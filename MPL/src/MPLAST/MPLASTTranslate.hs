{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE CPP #-}
module MPLAST.MPLASTTranslate where

import Optics

import Data.Function
import qualified Data.Bifunctor as Bifunctor
import Control.Monad

import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty as NE 
import Data.Maybe
import Data.Coerce

import MPLAST.MPLTypeAST
import MPLAST.MPLPatternAST
import MPLAST.MPLExprAST
import MPLAST.MPLProcessCommandsAST
import MPLAST.MPLProg
import MPLAST.MPLProgI

import MPLAST.MPLASTTranslateType
import MPLAST.MPLASTTranslatePatterns
import MPLAST.MPLASTTranslateErrors
import MPLAST.MPLASTTranslateExpr

import MPLUtil.Data.Either
import MPLUtil.Data.Either.AccumEither

import qualified Language.AbsMPL as B

import Data.Data
import Data.Typeable
import Data.Either
import Data.Tuple
import Data.Semigroup
import Control.Arrow

import Text.PrettyPrint.GenericPretty

translateBnfcMplToProgI :: 
    forall e.
    AsTranslateBnfcErrors e => 
    B.MplProg -> 
    ([e], ProgI)
translateBnfcMplToProgI (B.MPL_PROG prog) = (concatMap NE.toList *** Prog ) 
    (partitionEithers (map translateBnfcStmt prog))

translateBnfcStmt ::    
     forall e .
     AsTranslateBnfcErrors e =>
     B.MplStmt ->
     Either (NonEmpty e) StmtI
translateBnfcStmt (B.MPL_DEFN_STMS_WHERE defs wheres) = undefined
translateBnfcStmt (B.MPL_DEFN_STMS defs) = undefined
translateBnfcStmt (B.MPL_STMT def) = undefined

translateBnfcMplDefnToDefn :: 
    forall e.
    AsTranslateBnfcErrors e => 
    B.MplDefn -> 
    Either (NonEmpty e) (Defn BnfcIdent BnfcIdent)
translateBnfcMplDefnToDefn (B.MPL_SEQUENTIAL_TYPE_DEFN (B.DATA_DEFN seqclauses)) = 
    DataDefn . NE.fromList
    <$> view collectsOnlyIfNoLeftsGetter 
        (map f seqclauses)
  where
    f (B.SEQ_TYPE_CLAUSE from to handles) = 
        translateSeqTypeClauseArgs _IllegalDataDeclaration to from handles

translateBnfcMplDefnToDefn (B.MPL_SEQUENTIAL_TYPE_DEFN (B.CODATA_DEFN seqclauses)) = 
    CodataDefn . NE.fromList
    <$> view collectsOnlyIfNoLeftsGetter 
        (map f seqclauses)
  where
    f (B.SEQ_TYPE_CLAUSE from to handles) = 
        translateSeqTypeClauseArgs _IllegalCodataDeclaration from to handles
            
translateBnfcMplDefnToDefn (B.MPL_CONCURRENT_TYPE_DEFN (B.PROTOCOL_DEFN concclauses)) = 
    ProtocolDefn . NE.fromList
    <$> view collectsOnlyIfNoLeftsGetter
    (map f concclauses)
  where
    f (B.CONCURRENT_TYPE_CLAUSE from to handles) = 
        translateConcTypeClauseArgs _IllegalProtocolDeclaration to from handles
translateBnfcMplDefnToDefn (B.MPL_CONCURRENT_TYPE_DEFN (B.COPROTOCOL_DEFN concclauses)) = 
    CoprotocolDefn . NE.fromList
    <$> view collectsOnlyIfNoLeftsGetter
    (map f concclauses)
  where
    f (B.CONCURRENT_TYPE_CLAUSE from to handles) = 
        translateConcTypeClauseArgs _IllegalProtocolDeclaration from to handles

translateBnfcMplDefnToDefn (B.MPL_FUNCTION_DEFN fundef) = review _FunctionDefn <$> translateBnfcFunDefToDefn fundef
translateBnfcMplDefnToDefn (B.MPL_PROCESS_DEFN procdef) = 
    review _ProcessDefn <$> translateBnfcProcessDefn procdef

translateBnfcMplDefnToDefn B.MPL_DEFNTEST = error "eheh a little easter egg :) No writing potato ;) "

translateBnfcFunDefToDefn :: 
    forall e.
    AsTranslateBnfcErrors e => 
    B.FunctionDefn -> 
    Either (NonEmpty e)
    ( BnfcIdent
    , Maybe ([Type BnfcIdent BnfcIdent], Type BnfcIdent BnfcIdent)
    , NonEmpty ( [Pattern BnfcIdent BnfcIdent] , ExprI )
        )
translateBnfcFunDefToDefn (B.TYPED_FUNCTION_DEFN name intype outtype pattexprs) = do
    (intype', outtype', pattexprs') <- runAccumEither ( (,,) 
            <$> foldMap (liftAEither . fmap pure . translateBnfcTypeToType) intype
            <*> liftAEither (translateBnfcTypeToType outtype)
            <*> translateBnfcPattExprPhrase pattexprs
        )
    return (name ^. pIdentBnfcIdentGetter, Just (intype', outtype'), pattexprs') 
translateBnfcFunDefToDefn (B.FUNCTION_DEFN name pattexprs) = do
    pattexprs' <- runAccumEither (translateBnfcPattExprPhrase pattexprs)
    return (name ^. pIdentBnfcIdentGetter, Nothing, pattexprs') 

translateBnfcPattExprPhrase :: 
    forall e.
    AsTranslateBnfcErrors e => 
    [B.PattExprPhrase] -> 
    AccumEither (NonEmpty e) (NonEmpty ([Pattern BnfcIdent BnfcIdent], ExprI))
translateBnfcPattExprPhrase pattexprs = NE.fromList 
    <$> sequenceA ( map (\(B.PATTERN_TO_EXPR patts expr) -> (,) 
            (map translateBnfcPattern patts)
            <$> liftAEither (translateBnfcExpr expr) ) 
        pattexprs 
    ) 

translateBnfcExpr ::
    forall e.
    AsTranslateBnfcErrors e => 
    B.Expr -> 
    Either (NonEmpty e) ExprI
translateBnfcExpr (B.EXPR expr) = translateBnfcExpr expr
translateBnfcExpr (B.IF_EXPR iif ithen ielse) = do
    (iif', ithen', ielse') <- runAccumEither ( (,,) 
            <$> liftAEither (translateBnfcExpr iif)
            <*> liftAEither (translateBnfcExpr ithen)
            <*> liftAEither (translateBnfcExpr ielse)
        )

    return $ review _EIf (iif', ithen', ielse')
translateBnfcExpr (B.LET_EXPR stmts expr) = do
    (stmts', expr') <- runAccumEither $ (,) 
        <$> foldMap (liftAEither . f) stmts
        <*> liftAEither (translateBnfcExpr expr)
    return $ review _ELet (NE.fromList stmts', expr')
  where
    f (B.LET_EXPR_PHRASE stmt) = fmap pure (translateBnfcStmt stmt)

translateBnfcExpr (B.INFIXR0_EXPR a colon b) = error "not implemented instr"
translateBnfcExpr (B.INFIXL1_EXPR a op b) = error "not implemented instr"
translateBnfcExpr (B.INFIXL2_EXPR a op b) = error "not implemented instr"
translateBnfcExpr (B.INFIXL3_EXPR a op b) = error "not implemented instr"
translateBnfcExpr (B.INFIXL4_EXPR a op b) = error "not implemented instr"
translateBnfcExpr (B.INFIXL5_EXPR a op b) = error "not implemented instr"
translateBnfcExpr (B.INFIXL6_EXPR a op b) = error "not implemented instr"
translateBnfcExpr (B.INFIXR7_EXPR a op b) = error "not implemented instr"
translateBnfcExpr (B.INFIXL8_EXPR a op b) = error "not implemented instr"

translateBnfcExpr (B.LIST_EXPR lbr exprs rbr) = error "not implemented instr"

translateBnfcExpr (B.VAR_EXPR v) = return $ review _EVar (v ^. pIdentBnfcIdentGetter)
translateBnfcExpr (B.INT_EXPR v) = return $ review _EInt (v ^. pIntegerGetter)

translateBnfcExpr (B.CHAR_EXPR v) = error "not implemented"
translateBnfcExpr (B.STRING_EXPR v) = error "not implemented"
translateBnfcExpr (B.DOUBLE_EXPR v) = error "not implemented"

translateBnfcExpr (B.UNIT_EXPR lbr rbr) = return $ review _EUnit (lbr ^. lBracketBnfcIdentGetter)

translateBnfcExpr (B.FOLD_EXPR expr phrases) = do
    n <- runAccumEither $ (,)
        <$> liftAEither (translateBnfcExpr expr)
        <*> traverse translateBnfcFoldPhrase phrases
    return $ review _EFold n
translateBnfcExpr (B.UNFOLD_EXPR expr phrases) = do
    n <- runAccumEither $ (,)
        <$> liftAEither (translateBnfcExpr expr)
        <*> traverse translateBnfcUnfoldPhrase phrases
    return $ review _EUnfold n

translateBnfcExpr (B.CASE_EXPR expr pattexprs) = do
    (expr, n) <- runAccumEither $ (,)
        <$> liftAEither (translateBnfcExpr expr)
        <*> translateBnfcPattExprPhrase pattexprs
    return $ review _ECase (expr, n)

translateBnfcExpr (B.SWITCH_EXP switches) = 
    ESwitch . NE.fromList 
        <$> runAccumEither (traverse (liftAEither . translateBnfcSwitchExprPhrase) switches)

translateBnfcExpr (B.DESTRUCTOR_CONSTRUCTOR_NO_ARGS_EXPR ident) =
    return $ review _EDestructorConstructor (ident ^. uIdentBnfcIdentGetter, [])

translateBnfcExpr (B.DESTRUCTOR_CONSTRUCTOR_ARGS_EXPR ident _ exprs _) = do
    exprs' <- runAccumEither $ traverse (liftAEither . translateBnfcExpr) exprs
    return $ review _EDestructorConstructor (ident ^. uIdentBnfcIdentGetter, exprs')

translateBnfcExpr (B.TUPLE_EXPR _ a as _) = do
    n <- runAccumEither $ (,) 
        <$> liftAEither (translateBnfcExpr a)
        <*> (NE.fromList <$> traverse (liftAEither . translateBnfcTupleExprList) as)
    return $ review _ETuple n

translateBnfcExpr (B.FUN_EXPR fun _ args _) = do
    review _EFun <$> ( (fun ^.pIdentBnfcIdentGetter,) 
            <$> runAccumEither (traverse (liftAEither . translateBnfcExpr) args)
        )
translateBnfcExpr (B.RECORD_EXPR lbr exprs _) = 
    ERecord (lbr ^. lBracketBnfcIdentGetter) . NE.fromList
        <$> runAccumEither (traverse (liftAEither . translateBnfcRecordExprPhrase) exprs)

translateBnfcExpr (B.BRACKETED_EXPR _ expr _) =  translateBnfcExpr expr

-- EXPRESSION TRANSLATIONS...
translateBnfcFoldPhrase (B.FOLD_EXPR_PHRASE ident _ patts expr) = 
    FoldPhraseF (ident ^. uIdentBnfcIdentGetter) 
        (map translateBnfcPattern patts)
        <$> liftAEither (translateBnfcExpr expr)

translateBnfcUnfoldPhrase (B.UNFOLD_EXPR_PHRASE exp foldphrases) = UnfoldPhraseF (translateBnfcPattern exp) 
    <$> traverse translateBnfcFoldPhrase foldphrases

translateBnfcSwitchExprPhrase (B.SWITCH_EXPR_PHRASE a b) = 
    (,) <$> translateBnfcExpr a <*> translateBnfcExpr b

translateBnfcTupleExprList (B.TUPLE_EXPR_LIST e) = translateBnfcExpr e

translateBnfcRecordExprPhrase (B.RECORD_EXPR_PHRASE ident expr) =
    (ident ^. uIdentBnfcIdentGetter,) <$> translateBnfcExpr expr
----------
    
-- Process trnaslation
translateBnfcProcessDefn ::
    forall e.
    AsTranslateBnfcErrors e => 
    B.ProcessDefn -> 
    Either (NonEmpty e)
    ( BnfcIdent
    , Maybe ([TypeI], [TypeI], [TypeI])
    , NonEmpty 
        ( ([PatternI], [BnfcIdent], [BnfcIdent]) 
        , ProcessCommands PatternI StmtI BnfcIdent BnfcIdent)
        )
translateBnfcProcessDefn (B.TYPED_PROCESS_DEFN ident seqs inchs outchs prcsphrase) = runAccumEither $
    (ident ^. pIdentBnfcIdentGetter,,)
        <$> ( Just <$> ( (,,) 
                <$> traverse (liftAEither . translateBnfcTypeToType) seqs
                <*> traverse (liftAEither . translateBnfcTypeToType) inchs
                <*> traverse (liftAEither . translateBnfcTypeToType) outchs )
            )
        <*> (NE.fromList <$> traverse translateBnfcProcessPhrase prcsphrase)
translateBnfcProcessDefn (B.PROCESS_DEFN ident prcsphrase) = runAccumEither $
    (ident ^. pIdentBnfcIdentGetter,,) Nothing
        <$> (NE.fromList <$> traverse translateBnfcProcessPhrase prcsphrase)
    
    
    -- | PROCESS_DEFN PIdent [ProcessPhrase]


translateBnfcProcessPhrase :: 
    forall e.
    AsTranslateBnfcErrors e => 
    B.ProcessPhrase -> 
    AccumEither (NonEmpty e) 
        ( ( ([PatternI], [BnfcIdent], [BnfcIdent])
            , ProcessCommands PatternI StmtI BnfcIdent BnfcIdent))
translateBnfcProcessPhrase (B.PROCESS_PHRASE seqs inchs outchs pblock) = 
    let args = ( map translateBnfcPattern seqs
                , map (^.pIdentBnfcIdentGetter) inchs
                , map (^.pIdentBnfcIdentGetter) outchs )
        cmds = translateBnfcProcessCommandsBlock pblock
    in (args,) <$> cmds

translateBnfcProcessCommandsBlock :: 
    forall e.
    AsTranslateBnfcErrors e => 
    B.ProcessCommandsBlock -> 
    AccumEither (NonEmpty e)
        (ProcessCommands PatternI StmtI BnfcIdent BnfcIdent)
translateBnfcProcessCommandsBlock (B.PROCESS_COMMANDS_DO_BLOCK cmds) = 
    NE.fromList <$> traverse translateBnfcProcessCommand cmds
    
translateBnfcProcessCommandsBlock (B.PROCESS_COMMANDS_SINGLE_COMMAND_BLOCK cmd) =
    (:| []) <$> translateBnfcProcessCommand cmd 

translateBnfcProcessCommand :: 
    forall e.
    AsTranslateBnfcErrors e => 
    B.ProcessCommand -> 
    AccumEither 
        (NonEmpty e) 
        (ProcessCommand PatternI StmtI BnfcIdent BnfcIdent)
translateBnfcProcessCommand (B.PROCESS_RUN ident _ seqs inchs outchs _) = 
    let ident'  = ident ^. pIdentBnfcIdentGetter
        seqs' = traverse (liftAEither . translateBnfcExpr) seqs
        inchs' = map (^. pIdentBnfcIdentGetter) inchs
        outchs' = map (^. pIdentBnfcIdentGetter) outchs
    in CRun <$> pure ident' <*> seqs' <*> pure inchs' <*> pure outchs'

translateBnfcProcessCommand (B.PROCESS_CLOSE ident) = 
    pure $ CClose (ident ^. pIdentBnfcIdentGetter)
translateBnfcProcessCommand (B.PROCESS_HALT ident) =
    pure $ CHalt (ident ^. pIdentBnfcIdentGetter)
translateBnfcProcessCommand (B.PROCESS_GET pat ident) =
    pure $ CGet (translateBnfcPattern pat) (ident ^. pIdentBnfcIdentGetter)
translateBnfcProcessCommand (B.PROCESS_PUT exp ident) =
    CPut <$> liftAEither (translateBnfcExpr exp) <*> pure (ident ^. pIdentBnfcIdentGetter)

translateBnfcProcessCommand (B.PROCESS_HCASE ident phrases) =
    CHCase (ident ^. pIdentBnfcIdentGetter) <$> (traverse translateBnfcHCase (NE.fromList phrases))
translateBnfcProcessCommand (B.PROCESS_HPUT ident0 ident1) =
    pure (CHPut (ident0 ^. uIdentBnfcIdentGetter) (ident1 ^. pIdentBnfcIdentGetter))
translateBnfcProcessCommand (B.PROCESS_SPLIT ch chs) = 
    CSplit (ch ^. pIdentBnfcIdentGetter) <$> translateBnfcSplitChannels chs
translateBnfcProcessCommand (B.PROCESS_FORK ch phrases) =
    CFork (ch ^. pIdentBnfcIdentGetter) <$> translateBnfcForkPhrase phrases

translateBnfcProcessCommand (B.PROCESS_ID a b) =
    pure (CId (a ^. pIdentBnfcIdentGetter) (b ^. pIdentBnfcIdentGetter))

translateBnfcProcessCommand (B.PROCESS_NEG a b) =
    pure (CIdNeg (a ^. pIdentBnfcIdentGetter) (b ^. pIdentBnfcIdentGetter))

translateBnfcProcessCommand (B.PROCESS_RACE races) =
    CRace <$> traverse translateBnfcRacePhrases (NE.fromList races)

translateBnfcProcessCommand (B.PROCESS_PLUG phrases) = 
    CPlug [] <$> traverse translateBnfcPlugPhrase phrases

translateBnfcProcessCommand (B.PROCESS_CASE expr pcases) = 
    CCase 
        <$> liftAEither (translateBnfcExpr expr)
        <*> traverse translateBnfcProcessCasePhrase pcases

translateBnfcProcessCommand (B.PROCESS_SWITCH pswitch) =
    CSwitch <$> traverse translateBnfcProcessSwitchPhrase (NE.fromList pswitch)



translateBnfcHCase :: 
    AsTranslateBnfcErrors e => 
    B.HCasePhrase -> 
    AccumEither (NonEmpty e)
          (BnfcIdent, ProcessCommands PatternI StmtI BnfcIdent BnfcIdent)
translateBnfcHCase (B.HCASE_PHRASE uident block) = 
    (uident ^. uIdentBnfcIdentGetter,) <$> translateBnfcProcessCommandsBlock block

translateBnfcSplitChannels ::
    AsTranslateBnfcErrors e => 
    [B.SplitChannel] ->
    AccumEither (NonEmpty e) (BnfcIdent, BnfcIdent)
translateBnfcSplitChannels chs = case map f chs of
    [a,b] -> liftAEither (Right (a,b))
    chs' -> liftAEither $ Left $ (review _IllegalSplit chs') :| []
  where
    f (B.SPLIT_CHANNEL ident) = ident ^. pIdentBnfcIdentGetter

translateBnfcForkPhrase ::
    AsTranslateBnfcErrors e => 
    [B.ForkPhrase] -> 
    AccumEither (NonEmpty e) ( (BnfcIdent, [BnfcIdent], ProcessCommandsI)
        , (BnfcIdent, [BnfcIdent], ProcessCommandsI ) )
translateBnfcForkPhrase ns = case ns of
    [a,b] -> (,) <$> f a <*> f b
    _ -> liftAEither $ Left $ (review _IllegalFork (map g ns) :| [])
  where
    f (B.FORK_PHRASE ch pblock) = f (B.FORK_WITH_PHRASE ch [] pblock)
    f (B.FORK_WITH_PHRASE ch chs pblock) = 
        ( ch ^. pIdentBnfcIdentGetter
        , map (\(B.FORK_CHANNEL n)-> view pIdentBnfcIdentGetter n) chs
        ,) <$>  translateBnfcProcessCommandsBlock pblock

    g (B.FORK_PHRASE ch pblock) = ch ^. pIdentBnfcIdentGetter
    g (B.FORK_WITH_PHRASE ch chs pblock) = ch ^. pIdentBnfcIdentGetter

translateBnfcRacePhrases :: 
    AsTranslateBnfcErrors e => 
    B.RacePhrase -> 
    AccumEither (NonEmpty e)
        (BnfcIdent, ProcessCommands PatternI StmtI BnfcIdent BnfcIdent)
translateBnfcRacePhrases (B.RACE_PHRASE ch pblock) = 
    (ch ^.pIdentBnfcIdentGetter,) 
        <$> translateBnfcProcessCommandsBlock pblock

translateBnfcPlugPhrase ::
    AsTranslateBnfcErrors e => 
    B.PlugPhrase ->
    AccumEither (NonEmpty e) ([BnfcIdent], ProcessCommandsI)
translateBnfcPlugPhrase (B.PLUG_PHRASE pblock) = 
    ([],) <$> translateBnfcProcessCommandsBlock pblock

translateBnfcProcessCasePhrase ::
    AsTranslateBnfcErrors e => 
    B.ProcessCasePhrase -> 
    AccumEither (NonEmpty e) (PatternI, ProcessCommandsI)
translateBnfcProcessCasePhrase (B.PROCESS_CASE_PHRASE pat pblock) = 
    (,) (translateBnfcPattern pat) <$> translateBnfcProcessCommandsBlock pblock

translateBnfcProcessSwitchPhrase ::
    AsTranslateBnfcErrors e => 
    B.ProcessSwitchPhrase ->
    AccumEither (NonEmpty e) (ExprI, ProcessCommandsI)
translateBnfcProcessSwitchPhrase (B.PROCESS_SWITCH_PHRASE expr pblock) = 
    (,) <$> liftAEither (translateBnfcExpr expr) 
        <*> translateBnfcProcessCommandsBlock pblock
