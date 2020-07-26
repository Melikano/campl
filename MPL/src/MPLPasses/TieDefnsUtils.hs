{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
module MPLPasses.TieDefnsUtils where

import Optics 
import Optics.State
import Optics.State.Operators

import Control.Applicative

import MPLAST.MPLASTCore
import MPLAST.MPLTypeAST
import MPLUtil.UniqueSupply
import MPLPasses.SymbolTable
import MPLPasses.TieDefnsTypes
import MPLPasses.TieDefnsErrors
import MPLPasses.Unification
import MPLPasses.GraphGenCore

import MPLPasses.Unification

import Data.Functor.Foldable

import Data.Map ( Map (..) )
import qualified Data.Map as Map

import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Writer

import Data.Function
import Control.Applicative
import Data.List.NonEmpty ( NonEmpty (..) )
import qualified Data.List.NonEmpty as NE
import Data.Maybe
import Data.Foldable
import Data.List

import Control.Arrow
import Debug.Trace

lookupSeqPhrase :: 
    BnfcIdent -> 
    SymbolTable -> 
    Maybe (UniqueTag, TypePhraseG TaggedBnfcIdent)
lookupSeqPhrase ident ~symtable =  
    let candidates = filter ((ident ^. bnfcIdentName==) . fst) symtable
        res = helper candidates
    in res
  where
    helper ((_, SymEntry tag pos (SymPhrase n)):rst) 
        | objtype == CodataObj || objtype == DataObj = Just (tag, n)
      where
        objtype = n ^. 
            typePhraseContext 
            % phraseParent 
            % typeClauseNeighbors 
            % clauseGraph 
            % clauseGraphObjectType

    helper ((_, SymEntry _ _ _):rst) = helper rst
    helper [] = Nothing

    -- errormsg = liftToGraphErrors (_SeqPhraseNotInScope # ident)

clauseSubstitutions :: 
    ( MonadState s m 
    , HasUniqueSupply s ) =>
    TypeClauseG TaggedBnfcIdent ->
    m ( TypeGTypeTag
      , [TypeTag]
      , [(TaggedBnfcIdent, TypeGTypeTag)] )
    -- ( Clause type of the of the statevar
    -- , fresh vars used to substitte
    -- , substition list of unique tags to corresponsing types
        -- ( this includes the state variables )
clauseSubstitutions clauseg = do
    clauseargsubs <- traverse 
        (\n -> second TypeTag . (n,) <$> freshUniqueTag) 
        (clauseg ^. typeClauseArgs) 

    let clausestatevartype = _TypeWithArgs # 
            ( clauseg ^.  typeClauseName
            , TypeClauseCallDefKnot clauseg
            , map snd argsubstitions )
        clausegraphspine = NE.toList $ 
            clauseg ^. typeClauseNeighbors % clauseGraph % clauseGraphSpine
        argsubstitions = map 
            (second (flip TypeVar [])) 
            clauseargsubs
        statevarsubstitiions = map 
            (\n -> 
                ( n ^. typeClauseStateVar
                , _TypeWithArgs # 
                    ( n ^. typeClauseName
                    , TypeClauseCallDefKnot n 
                    , map snd argsubstitions )
                )
            )
            clausegraphspine

    return ( clausestatevartype
            , map snd clauseargsubs
            , statevarsubstitiions ++ argsubstitions)

annotateTypeIToTypeGAndGenSubs :: 
    SymbolTable -> 
    Type () BnfcIdent BnfcIdent -> 
    GraphGenCore 
        ( [TypeTag]
        , [(TaggedBnfcIdent, TypeGTypeTag)]
        , TypeG TaggedBnfcIdent)
annotateTypeIToTypeGAndGenSubs symtab = f <=< flip evalStateT symtab . annotateTypeIToTypeGAndScopeFreeVars 
  where
    f typeg = do    
        (tags, subs) <- genTypeGSubs typeg
        return (tags, subs, typeg)

genTypeGSubs :: 
    TypeG TaggedBnfcIdent -> 
    GraphGenCore ([TypeTag], [(TaggedBnfcIdent, TypeGTypeTag)])
genTypeGSubs typeg = do 
    let idents = collectTypeGFreeVarsIdents typeg
    ttypes <- traverse (const freshTypeTag) idents
    return (ttypes, zip idents $ map (flip TypeVar []) ttypes)

collectTypeGFreeVarsIdents :: 
    TypeG TaggedBnfcIdent ->
    [TaggedBnfcIdent]
collectTypeGFreeVarsIdents = nubBy ((==) `on` view uniqueTag) .  toList


-- takes an interface type and annotates it with the symbol table
-- moreover, for free variables, it will scope them all appropriately
annotateTypeIToTypeGAndScopeFreeVars :: 
    Type () BnfcIdent BnfcIdent -> 
    StateT SymbolTable GraphGenCore (TypeG TaggedBnfcIdent)
annotateTypeIToTypeGAndScopeFreeVars = cata f
  where
    f :: 
        TypeF () BnfcIdent BnfcIdent (StateT SymbolTable GraphGenCore (TypeG TaggedBnfcIdent)) -> 
        StateT SymbolTable GraphGenCore (TypeG TaggedBnfcIdent)
    f (TypeVarF ident args) = f $ TypeWithArgsF ident () args
    f (TypeWithArgsF ident () args) = do
        args' <- sequenceA args
        symtab <- guse equality

        lkup <- lift $ 
            ambiguousLookupCheck
            =<< censor (const []) (querySymbolTableBnfcIdentName ident symtab)
            -- note that this will check if it is out of scope already...

        case lkup of
            Just (_, SymEntry tag pos (SymClause n)) -> do
                return $ TypeWithArgs 
                    (TaggedBnfcIdent ident tag) 
                    (TypeClauseCallDefKnot n) 
                    args'
            Just (_, SymEntry tag pos SymTypeVar) -> do
                return $ TypeVar (TaggedBnfcIdent ident tag) 
                    args'

            Nothing -> do
                taggedident <- lift $ tagBnfcIdent ident
                ttype <- lift $ freshTypeTag

                equality %= (
                    ( taggedident ^. taggedBnfcIdentName
                    , SymEntry (taggedident ^. uniqueTag) (taggedident ^. taggedBnfcIdentPos)
                        $ SymTypeVar):)
                --annotateStateFreeVarsTypeTags %= (ttype:)
                -- annotateStateFreeVarsSubs %= ((taggedident, TypeVar ttype []):)

                return $ TypeVar taggedident args'

    f (TypeSeqF seq) = do
        seq' <- sequenceA seq 
        case seq' of
            TypeSeqArrF froms tos -> return $ TypeSeq $ TypeSeqArrF froms tos
            _ -> error "not impletmendyet "
        -- return $ TypeSeq <$> sequenceA seq'
        -- fmap TypeSeq <$> sequenceA seq
    -- f (TypeConcF conc) = fmap TypeConc <$> fmap sequenceA (sequenceA conc)
    

{-
tagTypeSeq :: 
    SeqTypeF BnfcIdent t ->
    GraphGenCore (SeqTypeF TaggedBnfcIdent t)
tagTypeSeq (TypeTupleF n) = return (TypeTupleF n)
tagTypeSeq (TypeIntF n) = return (TypeTupleF n)
-}

data ExprTypeTags = ExprTypeTags {
    _exprTtype :: TypeTag
    , _exprTtypeInternal :: TypeTag
}  deriving Show

data TieExprEnv = TieExprEnv {
    _tieExprEnvTypeTags :: ExprTypeTags
    , _tieExprEnvTagTypeMap :: TagTypeMap
}

$(makeLenses ''TieExprEnv)
$(makePrisms ''TieExprEnv)
$(makeClassy ''ExprTypeTags)
$(makePrisms ''ExprTypeTags)

freshExprTypeTags :: GraphGenCore ExprTypeTags
freshExprTypeTags = ExprTypeTags <$> freshTypeTag <*> freshTypeTag

instance HasExprTypeTags TieExprEnv where
    exprTypeTags = tieExprEnvTypeTags
