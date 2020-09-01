{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE NamedWildCards #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
module MplPasses.TypeChecker.TypeCheck where

import Optics 
import Optics.State.Operators

import MplAST.MplCore
import MplAST.MplParsed
import MplAST.MplRenamed
import MplAST.MplTypeChecked 

import MplPasses.TypeChecker.TypeCheckSemanticErrors 
import MplPasses.TypeChecker.TypeCheckUtils 
import MplPasses.TypeChecker.TypeCheckSym 
import MplPasses.TypeChecker.TypeCheckMplTypeSub 
import MplPasses.TypeChecker.TypeCheckMplTypeSubUtil
import MplPasses.TypeChecker.TypeEqns
import MplPasses.TypeChecker.TypeCheckObj 
import MplPasses.TypeChecker.KindCheck 
import MplPasses.TypeChecker.TypeCheckPatt 
import MplPasses.TypeChecker.TypeCheckPanic
import MplPasses.TypeChecker.TypeCheckErrorPkg
import MplPasses.TypeChecker.TypeCheckSymUtils 
import MplPasses.TypeChecker.TypeCheckErrors 
import MplPasses.TypeChecker.TypeCheckCallErrors 
import MplPasses.Env

import MplUtil.UniqueSupply

import Control.Monad.Writer
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except

import Control.Arrow
import Control.Applicative
import Data.Semigroup
import Data.Maybe
import Data.Bool
import Data.Traversable

import qualified Data.Map as Map
import Data.Map (Map)

import Data.List
import Debug.Trace

import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty as NE

import Data.Foldable

import Data.Functor.Foldable (Base, cata, para)

runTypeCheck' ::
    ( AsTypeCheckErrors err 
    , AsTypeUnificationError err MplTypeSub
    , AsTypeCheckSemanticErrors err
    , AsKindCheckErrors err 
    , AsTypeCheckCallErrors err ) =>
    (TopLevel, UniqueSupply) ->
    MplProg MplRenamed ->
    Either [err] (MplProg MplTypeChecked)
runTypeCheck' ~(top, sup) = 
    \case 
        (res, []) -> Right res
        (_, errs) -> Left errs
    . runWriter 
    . (`evalStateT` ( _Env # 
            ( top
            , lsup
            , mempty
            , TypeInfoEnv mempty tag mempty)
        )
      )
    . runTypeCheck
  where
    ~(lsup, rsup) = split sup
    tag = evalState freshTypeTag rsup

runTypeCheck ::
    forall e m0 n. 
    ( AsTypeCheckErrors e 
    , AsTypeUnificationError e MplTypeSub
    , AsTypeCheckSemanticErrors e
    , AsKindCheckErrors e
    , AsTypeCheckCallErrors e

    , MonadWriter [e] n 
    , MonadWriter [e] m0

    , MonadFix n 

    , Zoom m0 n SymTab TypeCheckEnv ) =>
    MplProg MplRenamed -> n (MplProg MplTypeChecked)
runTypeCheck (MplProg stmts) = 
    MplProg <$> traverse typeCheckStmts stmts

typeCheckStmts ::
    forall e m0 n. 
    ( AsTypeCheckErrors e 
    , AsTypeCheckCallErrors e
    , AsTypeUnificationError e MplTypeSub
    , AsTypeCheckSemanticErrors e
    , AsKindCheckErrors e 

    , MonadWriter [e] n 
    , MonadWriter [e] m0

    , MonadFix n 

    , Zoom m0 n SymTab TypeCheckEnv ) =>
    MplStmt MplRenamed -> n (MplStmt MplTypeChecked)
typeCheckStmts (MplStmt defns wheres) = do
    wheres' <- traverse typeCheckStmts wheres

    -- envLcl % typeInfoSymTab % symTabBadLookup .= False
    
    envLcl % typeInfoSymTab %= mempty
    rec envLcl % typeInfoEnvMap .= tagmap
        ~((defns', eqns), errpkg) <- fmap (first (NE.unzip . NE.fromList)) 
            $ runWriterT 
            $ typeCheckDefns 
            $ NE.toList defns
        let terrs = collectPkgErrors errpkg
            erroccured = hasn't _Empty terrs

            foralls = foldMap (view _1) eqns
            exists = foldMap (view _2) eqns
            subs = foldMap (view _3) eqns
            eqns' = TypeEqnsForall foralls $ [TypeEqnsExist exists subs]
            -- pkgtest = runExcept (solveTypeEqns eqns') :: Either (TypeUnificationError MplTypeSub) (Package MplTypeSub)
            -- pkg = runExcept $ bool (return ()) (throwError []) erroccured 
                -- >> withExceptT pure (solveTypeEqns eqns') 
            pkg = runExcept $ bool (return ()) (throwError mempty) erroccured 
                    >> withExceptT pure (solveTypeEqns eqns') 

        ~tagmap <- packageToTypeTagMap (either mempty id (pkg :: Either [e] (Package MplTypeSub)))

    -- tell $ pure $ head $ _Huhh # () : terrs
    tell terrs
    tell $ either id mempty pkg
    traceM $ bool [] (show eqns') $ null terrs

    -- need to replace definitions in the symbol table here for
    -- functions. Moreover, illegally called functoins need listening..
    zoom envGbl $ 
        bool (traverse eliminateSymTabDefn defns') (traverse recollectSymTabDefn defns') (has _Right pkg)

    -- swap the buffers..
    symtab' <- guse envGbl
    envLcl % typeInfoSymTab .= symtab'

    return $ MplStmt defns' wheres'

typeCheckDefns ::
    TypeCheck
        [MplDefn MplRenamed] 
        [ ( MplDefn MplTypeChecked
          , ([TypeP MplTypeSub], [TypeP MplTypeSub], [TypeEqns MplTypeSub])) ]
-- same as the rename step.. need to do the magic recursive do in order
-- to get the recursive declarations together properly.
typeCheckDefns (defn : defns) = do
    rec ~(defn', eqns) <- envLcl % typeInfoSymTab .= symtab 
                    >> fmap snd (withFreshTypeTag (typeCheckDefn defn))
        collectSymTabDefn defn'
        -- envGbl %= (collectSymTab (fmap fst defn')<>)
        ~defns' <- typeCheckDefns defns
        ~symtab <- guse envGbl
    return $ (defn', eqns) : defns'
typeCheckDefns [] = return []


typeCheckDefn ::
    TypeCheck (MplDefn MplRenamed) 
            ( (MplDefn MplTypeChecked), ([TypeP MplTypeSub], [TypeP MplTypeSub], [TypeEqns MplTypeSub]))
typeCheckDefn (ObjectDefn obj) = (((,mempty) . ObjectDefn)) <$> case obj of
        SeqObjDefn obj -> SeqObjDefn <$> case obj of
            DataDefn n -> DataDefn <$> typeCheckTypeClauseSpine n
            CodataDefn n -> CodataDefn <$> typeCheckTypeClauseSpine n
        ConcObjDefn obj -> ConcObjDefn <$> case obj of
            ProtocolDefn n -> ProtocolDefn <$> typeCheckTypeClauseSpine n
            CoprotocolDefn n -> CoprotocolDefn <$> typeCheckTypeClauseSpine n
typeCheckDefn (FunctionDefn fun@(MplFunction name funtype defn)) = do
    st <- guse equality
    ((foralls, funtype'), symtp) <- case funtype of    
        Just tp -> do
            tp <- kindCheckFunType tp
            arrenv <- freshInstantiateArrEnv
            let (inst, insttp) = runInstantiateArrType
                    (instantiateArrType (_Just % _TypeAnnFun # fun) tp)
                    arrenv
            return ((inst, insttp), SymFun tp)
        Nothing -> do
            tag <- freshTypeTag
            let tp = typePtoTypeVar $ annotateTypeTag tag fun
            return $ (([], tp), SymSub tp)
    ttype <- guse (envLcl % typeInfoEnvTypeTag)
    ttypemap <- guse (envLcl % typeInfoEnvMap)
    
    rec let funsymentry = _SymEntry # (symtp, _SymSeqCall % _ExprCallFun # fun')
        envLcl % typeInfoSymTab % symTabTerm % at (name ^. uniqueTag) ?= funsymentry

        ~(ttypephrases, (defn', acceqns)) <- second NE.unzip . NE.unzip <$> 
            traverse (withFreshTypeTag . typeCheckFunBody ) defn

        let fun' = MplFunction name (fromJust $ ttypemap ^? at ttype % _Just % _SymTypeFun) defn'
            ttype' = typePtoTypeVar $ annotateTypeTag ttype fun
            ttypephrases' = annotateTypeTags (NE.toList ttypephrases) $ NE.toList defn
            eqns = TypeEqnsExist ttypephrases' $
                [ TypeEqnsEq (ttype', funtype') ]
                <> map (TypeEqnsEq . (ttype',) . typePtoTypeVar ) ttypephrases'
                <> (sconcat acceqns)

    return (FunctionDefn fun', (foralls, ttypephrases', [eqns]))

-- some duplciated code...
typeCheckDefn (ProcessDefn procc@(MplProcess name proctype defn)) = do
    st <- guse equality
    ((foralls, proctype'), symtp) <- case proctype of    
        Just tp -> do
            ~tp <- fmap fromJust $ kindCheckProcessType tp
            arrenv <- freshInstantiateArrEnv
            let (inst, insttp) = runInstantiateArrType     
                    (instantiateArrType (_Just % _TypeAnnProc # procc) tp)
                    arrenv 
            return ((inst, insttp), SymProc tp)
        Nothing -> do
            tag <- freshTypeTag
            let tp = typePtoTypeVar $ annotateTypeTag tag procc
            return $ (([], tp), SymSub tp)

    ttype <- guse (envLcl % typeInfoEnvTypeTag)
    ttypemap <- guse (envLcl % typeInfoEnvMap)
    
    -- rec let procsymentry = _SymEntry # (SymSub proctype', _SymRunInfo # procc')
    rec let procsymentry = _SymEntry # (symtp, _SymRunInfo # procc')
        envLcl % typeInfoSymTab % symTabTerm % at (name ^. uniqueTag) ?= procsymentry

        (ttypephrases, (defn', acceqns)) <- second NE.unzip . NE.unzip <$> 
            traverse (withFreshTypeTag . typeCheckProcessBody) defn

        let procc' = MplProcess name (fromJust $ ttypemap ^? at ttype % _Just % _SymTypeProc) defn'
            ttype' = typePtoTypeVar $ annotateTypeTag ttype procc
            ttypephrases' = annotateTypeTags (NE.toList ttypephrases) $ NE.toList defn
            eqns = TypeEqnsExist ttypephrases' $
                [ TypeEqnsEq (ttype', proctype') ]
                -- <> map (TypeEqnsEq . (ttype',)) (annotateTypeTags (NE.toList ttypephrases) $ ttypephrases' )
                <> map (TypeEqnsEq . (ttype',) . typePtoTypeVar) ttypephrases'
                <> (sconcat acceqns)

    return $ (ProcessDefn procc', (foralls, ttypephrases', [eqns])) 

-------------------------
-- Type checking expressions
-------------------------
typeCheckFunBody ::
    TypeCheck
        ([MplPattern MplRenamed], MplExpr MplRenamed)
        (([MplPattern MplTypeChecked], MplExpr MplTypeChecked), 
            [TypeEqns MplTypeSub] )
typeCheckFunBody bdy@(patts, expr) = do
    ttype <- guse (envLcl % typeInfoEnvTypeTag)
    ttypestable <- freshTypeTag
    ttypemap <- guse (envLcl % typeInfoEnvMap)

    ~(ttypepatts, (patts', pattacceqns)) <- second NE.unzip . NE.unzip <$> 
        traverse (withFreshTypeTag . typeCheckPattern) patts 

    ~(ttypeexpr, (expr', expracceqn)) <- withFreshTypeTag . typeCheckExpr $ expr

    let ttypep = annotateTypeTag ttype bdy
        ttypepexpr = annotateTypeTag ttypeexpr expr
        ttypeppatts = annotateTypeTags ttypepatts patts

        eqn = TypeEqnsExist (ttypepexpr:ttypeppatts) $
                [ TypeEqnsEq 
                    ( typePtoTypeVar ttypep
                    , mkTypeSubSeqArr 
                        ( map typePtoTypeVar ttypeppatts
                        , typePtoTypeVar ttypepexpr )
                    )
                ]
                <> concat pattacceqns
                <> expracceqn

    return ((patts', expr'), [eqn])


typeCheckExpr ::
    TypeCheck
        (MplExpr MplRenamed)
        (MplExpr MplTypeChecked, [TypeEqns MplTypeSub])
typeCheckExpr = para f
  where
    f :: Base (MplExpr MplRenamed) (MplExpr MplRenamed, _ (MplExpr MplTypeChecked, [TypeEqns MplTypeSub])) ->
        _ (MplExpr MplTypeChecked, [TypeEqns MplTypeSub])
    f (EVarF cxt n) = do
        ttype <- guse (envLcl % typeInfoEnvTypeTag)
        ttypestable <- freshTypeTag
        ttypemap <- guse (envLcl % typeInfoEnvMap)

        ~(SymEntry lkuptp (SymSeqCall lkupdef)) <- zoom (envLcl % typeInfoSymTab) $ lookupSymTerm n

        let ttypep = annotateTypeTag ttype (_EVar # (cxt, n) :: MplExpr MplRenamed)
            
            lkuptp' = fromJust $ lkuptp ^? _SymSub
            eqns = [ TypeEqnsEq (typePtoTypeVar ttypep , lkuptp') ] 
                <> [ genStableEqn ttypestable ttypep ]

        return (EVar (lkupdef, fromJust $ ttypemap ^? at ttypestable % _Just % _SymType ) n, eqns)

    f (EPOpsF _ _ _ _ ) = panicNotImplemented
    f (EIntF _ _ ) = panicNotImplemented
    f (ECharF _ _ ) = panicNotImplemented
    f (EDoubleF _ _ ) = panicNotImplemented

    f (ECaseF cxt (caseon, mcaseon) cases) = do
        ttype <- guse (envLcl % typeInfoEnvTypeTag)
        ttypestable <- freshTypeTag
        ttypemap <- guse (envLcl % typeInfoEnvMap)

        (ttypecaseon, (caseon', caseoneqn)) <- withFreshTypeTag mcaseon

        ((ttypepatts, ttypeexprs), (pattsexprs', acceqns)) <- 
            fmap ((NE.unzip *** NE.unzip) <<< NE.unzip)
            $ for cases $ \(patt, (_, mexpreqn)) -> do
                (ttypepatt, (patt', patteqn)) <- withFreshTypeTag $ typeCheckPattern patt
                (ttypeexpr, (expr', expreqn)) <- withFreshTypeTag mexpreqn
                return ((ttypepatt, ttypeexpr), ((patt', expr'), patteqn <> expreqn))

        let ttypep = annotateTypeTag ttype (_ECase # (cxt, caseon, fmap (second fst) cases) :: MplExpr MplRenamed)
            ttypepcaseon = annotateTypeTag ttypecaseon caseon

            ttypeppatts = annotateTypeTags (NE.toList ttypepatts) (NE.toList $ fmap fst cases)
            ttypepexprs = annotateTypeTags (NE.toList ttypeexprs) (NE.toList $ fmap (fst . snd) cases)

            eqns = TypeEqnsExist (ttypepcaseon : ttypeppatts ++ ttypepexprs) $
                [ genStableEqn ttypestable ttypep ]
                -- the case on should be the same as all the patterns
                <> map (TypeEqnsEq . (typePtoTypeVar ttypepcaseon,) . typePtoTypeVar) ttypeppatts
                -- the resulting type should be the same as all expressions
                -- on the other side of the case
                <> map (TypeEqnsEq . (typePtoTypeVar ttypep,) . typePtoTypeVar) ttypepexprs
                -- accumulate the old equations of course.
                <> caseoneqn
                <> concat acceqns

        return 
            ( _ECase # 
             ( fromJust $ ttypemap ^? at ttypestable % _Just % _SymType
             , caseon'
             , pattsexprs' )
            , [eqns])
        
    f (EObjCallF cxt ident args) = do
        ttype <- guse (envLcl % typeInfoEnvTypeTag)
        ttypestable <- freshTypeTag
        ttypemap <- guse (envLcl % typeInfoEnvMap)

        ~(SymEntry lkuptp (SymSeqPhraseCall seqdef)) <- zoom (envLcl % typeInfoSymTab) $ lookupSymTerm ident

        (ttypeargs, (args', argseqns)) <- fmap (second unzip <<< unzip) $
            for args $ \(_, mexpreqns) -> withFreshTypeTag mexpreqns

        let expr = _EObjCall # (cxt, ident, map fst args) :: MplExpr MplRenamed

        -- Actually, we can type a destructor and just call it...
        -- tell $ review _ExternalError $ flip (maybe mempty) (seqdef ^? _CodataDefn) $ \defn ->
            -- [_IllegalExprDataCallGotCodataInstead # (expr, defn) ]

        arrenv <- freshInstantiateArrEnv
        let ttypep = annotateTypeTag ttype expr
            ttypepargs = annotateTypeTags ttypeargs $ map fst args

            ann = _Just % _TypeAnnExpr # expr
            ~(ttypesphrase, lkuptp') = (`runInstantiateArrType`arrenv)
                $ fromJust 
                $ instantiateArrType ann
                    <$> lkuptp ^? _SymDataPhrase % noStateVarsType
                <|> instantiateArrType ann
                    <$> lkuptp ^? _SymCodataPhrase % noStateVarsType

            eqns = TypeEqnsExist (ttypesphrase ++ ttypepargs) $
                [ TypeEqnsEq 
                    ( mkTypeSubSeqArr (map typePtoTypeVar ttypepargs, typePtoTypeVar ttypep)  
                    , lkuptp') 
                ] 
                <> [genStableEqn ttypestable ttypep]
                <> concat argseqns

        return 
            ( _EObjCall # 
              ( fromJust $ ttypemap ^? at ttypestable % _Just % _SymType
              , ident
              , args' ) 
            , [eqns] )

    -- lots of duplicated code..
    f (ECallF cxt ident args ) = do
        ttype <- guse (envLcl % typeInfoEnvTypeTag)
        ttypestable <- freshTypeTag
        ttypemap <- guse (envLcl % typeInfoEnvMap)

        ~(SymEntry lkuptp (SymSeqCall seqdef)) <- zoom (envLcl % typeInfoSymTab) $ lookupSymTerm ident

        (ttypeargs, (args', argseqns)) <- fmap (second unzip <<< unzip) $
            for args $ \(_, mexpreqns) -> withFreshTypeTag mexpreqns

        arrenv <- freshInstantiateArrEnv
        let expr = _ECall # (cxt, ident, map fst args) :: MplExpr MplRenamed

            ttypep = annotateTypeTag ttype expr
            ttypepargs = annotateTypeTags ttypeargs $ map fst args

            ann = _Just % _TypeAnnExpr # expr
            ~(ttypesphrase, lkuptp') = (`runInstantiateArrType`arrenv)
                $ fromJust 
                $ instantiateArrType ann
                    <$> lkuptp ^? _SymSub
                -- this call is the only thing that differs from the
                -- object call.
                <|> instantiateArrType ann <$> lkuptp ^? _SymFun 

            eqns = TypeEqnsExist (ttypesphrase ++ ttypepargs) $
                [ TypeEqnsEq 
                    ( mkTypeSubSeqArr (map typePtoTypeVar ttypepargs, typePtoTypeVar ttypep)  
                    , lkuptp') 
                ] 
                <> [genStableEqn ttypestable ttypep]
                <> concat argseqns

        return 
            ( _EObjCall # 
              ( fromJust $ ttypemap ^? at ttypestable % _Just % _SymType
              , ident
              , args' ) 
            , [eqns] )

    f (ERecordF cxt phrases) = do
        ttype <- guse (envLcl % typeInfoEnvTypeTag)
        ttypestable <- freshTypeTag
        ttypemap <- guse (envLcl % typeInfoEnvMap)
        
        let expr = _ERecord # (cxt, phrases & mapped % _3 % _2 %~ fst) :: MplExpr MplRenamed
            ttypep = annotateTypeTag ttype expr

        {-
         -- STILL NEED TO CHECK IF THE CLAUSE IS EXHAUSTIVE
         -- Not really a type checking thing to do?
        tell $ review _ExternalError $ bool 
            [] [_RecordConstructionErrorGotPhrasesButExpected # 
                ( recordphraseidents
                , clausephrases ) ]
            $ length recordphraseidents /= length clausephrases || 
                any id (zipWith (\a b -> a ^. uniqueTag /= b ^. typePhraseName % uniqueTag ) 
                    (NE.toList recordphraseidents) clausephrases)
        -}

        st <- guse equality
        sup <- freshUniqueSupply
        arrenv <- freshInstantiateArrEnv
        ~(~((ttypeppatts, ttypepexpr), (phrases', phraseseqns)), ttypepinst) <- fmap 
            (( unzip *** unzip <<< unzip <<< NE.toList) 
                *** (toListOf (_2 % instantiateArrEnvInstantiated % folded) ) )
            $ (`runStateT` (st & uniqueSupply .~ sup, arrenv))
            $ for phrases $ \(_, ident, (patts, (_, mexpr))) -> do
                ~(SymEntry lkuptp (SymSeqPhraseCall (CodataDefn seqdef))) <- 
                    zoom (_1 % envLcl % typeInfoSymTab) $ do
                        res <- guse $ symTabTerm % at (ident ^. uniqueTag)
                        let callterm = maybe (_Just % _CannotCallTerm # ident) (const Nothing) res
                        tell $ review _InternalError $ maybeToList $ callterm
                        -- NOTE: there is a bug here, when given a data call in place
                        -- of a codata call, it will just non exhaustive pattern match..
                        -- this requires a little more tinkering and fiddling than my appear
                        -- when trying to fix this! We leave this as todo...
                        tell $ review _InternalError $ maybeToList $ 
                            res ^? _Just 
                                % symEntryInfo 
                                % _SymSeqPhraseCall 
                                % _DataDefn 
                                % to (review _IllegalExprCodataCallGotDataInstead . (expr,))
                        return $ fromJust res

                ~(ttypepatts, ~(patts', pattseqns)) <- fmap (second NE.unzip <<< NE.unzip) 
                    $ zoom _1 
                    $ for patts $ withFreshTypeTag . typeCheckPattern

                ~(ttypeexpr, ~(expr', expreqns)) <- zoom _1 $ withFreshTypeTag $ lift mexpr 

                {-
                 - Note: we need the ``state $ runState" call here to get the correct laziness
                -}
                (ttypepphrase, ttypeclause) <- zoom _2 $ state $ runState $ do
                    ttypepphrase <- instantiateArrType 
                        {- TODO, probably should include some sort of annotation
                        - information here... e.g. (_Just % TypeAnnPatt seqdef) -}
                        Nothing 
                        $ fromJust $ lkuptp ^? _SymCodataPhrase 
                                % noStateVarsType 
                                % to (over _2 fst)
                    subs <- getInstantiatedSubs
                    return 
                        ( ttypepphrase
                        , seqdef ^. typePhraseExt % to 
                            (\clause -> fromJust 
                                $ instantiateTypeWithSubs subs
                                $ _TypeSeqWithArgs # 
                                    ( _CodataDefn # clause
                                    , clause ^. typeClauseName
                                    , clause ^. typeClauseArgs 
                                        -- duplicated code from TypeCheckMplTypeSub.hs
                                        % to (map (review _TypeVar . (Just $ SeqKind (),) . NamedType ))
                                    ) 
                            )
                        )

                let ttypeppatts = annotateTypeTags ttypepatts patts 
                    ttypepexpr = annotateTypeTag ttypeexpr expr
                    phraseeqns = 
                        -- the type of the patts and expression
                        -- must match the type phrase given in 
                        -- the clause
                        [ TypeEqnsEq 
                            ( mkTypeSubSeqArr (ttypeppatts, ttypepexpr) 
                            , ttypepphrase)
                        -- the type of this whole expression is the
                        -- same as the end result type
                        , TypeEqnsEq
                            ( ttypeclause
                            , typePtoTypeVar ttypep )
                        ]

                return 
                    ( (ttypeppatts, ttypepexpr)
                    , ((seqdef, ident, (patts', expr')), phraseeqns ++ concat pattseqns ++ expreqns)
                    )

        let eqns = TypeEqnsExist (concat ttypeppatts <> ttypepexpr <> ttypepinst ) $
                [ genStableEqn ttypestable ttypep ]
                <> concat phraseseqns

        return $ 
            ( _ERecord # 
              ( (cxt, fromJust $ ttypemap ^? at ttypestable % _Just % _SymType)
              , NE.fromList phrases') 
            , [eqns] )



-------------------------
-- Type checking process...
-------------------------
typeCheckProcessBody ::
    TypeCheck
    ( ([MplPattern MplRenamed], [ChIdentR], [ChIdentR])
        , NonEmpty (MplCmd MplRenamed) )
    ( (([MplPattern MplTypeChecked], [ChIdentT], [ChIdentT])
        , NonEmpty (MplCmd MplTypeChecked))
    , [TypeEqns MplTypeSub])
typeCheckProcessBody procbdy@((patts, ins, outs), cmds) = do
    ttype <- guse (envLcl % typeInfoEnvTypeTag)
    ttypestable <- freshTypeTag
    ttypemap <- guse (envLcl % typeInfoEnvMap)

    (ttypepatts, (patts', pattacceqns)) <- second NE.unzip . NE.unzip <$> 
        traverse (withFreshTypeTag . typeCheckPattern) patts 

    ttypeins <- traverse addChToSymTab ins
    ttypeouts <- traverse addChToSymTab outs

    -- ttypepattsstable <- traverse (const freshTypeTag) ttypepatts
    ttypeinsstable <- traverse (const freshTypeTag) ttypeins
    ttypeoutsstable <- traverse (const freshTypeTag) ttypeouts

    (cmds', acccmds) <- typeCheckCmds cmds
    let ttypep = annotateTypeTag ttype procbdy
        ttypeppatts = annotateTypeTags ttypepatts patts
        ttypepins = annotateTypeTags ttypeins ins
        ttypepouts = annotateTypeTags ttypeouts outs

        eqn = TypeEqnsExist (ttypeppatts ++ ttypepins ++ ttypepins) $
                -- phrase equation
                [ TypeEqnsEq    
                    ( typePtoTypeVar ttypep
                    , _TypeConcArrF # 
                        ( _Just % _TypeAnnProcPhrase # procbdy
                        , map typePtoTypeVar ttypeppatts
                        , map typePtoTypeVar ttypepins
                        , map typePtoTypeVar ttypepins ) 
                    ) 
                ]

                -- stable equations
                -- <> zipWith genStableEqn ttypepattsstable ttypeppatts
                <> zipWith genStableEqn ttypeinsstable ttypepins
                <> zipWith genStableEqn ttypeoutsstable ttypepouts

                -- accumulate the equations
                <> acccmds
                <> concat pattacceqns
        ins' = zipWith 
                (\stref -> review _ChIdentT . (,fromJust $ ttypemap ^? at stref % _Just % _SymType) )
                ttypeinsstable ins 
        outs' = zipWith 
                (\stref -> review _ChIdentT . (,fromJust $ ttypemap ^? at stref % _Just % _SymType) )
                ttypeoutsstable outs 

    return (((patts', ins', outs'), cmds'), [eqn])

typeCheckCmds ::
    TypeCheck
        (NonEmpty (MplCmd MplRenamed)) 
        (NonEmpty (MplCmd MplTypeChecked), [TypeEqns MplTypeSub])
typeCheckCmds (cmd :| []) = do
    tell $ review _ExternalError $ case cmd of
        (CClose cxt _) -> [_IllegalLastCommand # cxt]
        (CGet cxt _ _) -> [_IllegalLastCommand # cxt]
        (CPut cxt _ _) -> [_IllegalLastCommand # cxt]
        (CHPut cxt _ _) -> [_IllegalLastCommand # cxt]
        (CSplit cxt _ _) -> [_IllegalLastCommand # cxt]
        _ -> mempty
    first (:|[]) <$> typeCheckCmd cmd
typeCheckCmds (cmd :| rst) = do
    tell $ review _ExternalError $ case cmd of
        CFork cxt _ _ -> [_IllegalNonLastCommand # cxt]
        CId cxt _ -> [_IllegalNonLastCommand # cxt]
        CIdNeg cxt _ -> [_IllegalNonLastCommand # cxt]
        -- run commands are not techincally a keyword..
        CRun _ cxt _ _ _ -> [review _IllegalNonLastCommand $ cxt ^. identPNameOcc % to KeyWordNameOcc]
        CHCase cxt _ _ -> [_IllegalNonLastCommand # cxt]
        CHalt cxt _ -> [_IllegalNonLastCommand # cxt]
        CRace cxt _ -> [_IllegalNonLastCommand # cxt]
        _ -> []
    (cmd', eqn) <- typeCheckCmd cmd
    (rst', eqns) <- first NE.toList <$> typeCheckCmds (NE.fromList rst)
    return (cmd' :| rst', eqn <> eqns)

typeCheckCmd ::
    TypeCheck
        (MplCmd MplRenamed)
        (MplCmd MplTypeChecked, [TypeEqns MplTypeSub])
typeCheckCmd = \case
    cmd@(CRun cxt ident seqs ins outs) -> do
        ttype <- guse (envLcl % typeInfoEnvTypeTag)
        ttypestable <- freshTypeTag
        ttypemap <- guse (envLcl % typeInfoEnvMap)

        ~(SymEntry tp (SymRunInfo procc)) <- fmap fromJust $ 
            guse (envLcl % typeInfoSymTab % symTabTerm % at (ident ^. uniqueTag)) 

        arrenv <- freshInstantiateArrEnv
        let ttypelkup = (`evalState`arrenv) $ fromJust 
                -- actualyl this is useless
                $ tp ^? _SymSub % to (instantiateArrType (_Just % _TypeAnnCmd # cmd))
                -- but this phrase is helpful
                <|> tp ^? _SymProc % to (instantiateArrType (_Just % _TypeAnnCmd # cmd))

        -- inslkup <- traverse f ins 
        -- outslkup <- traverse f outs
        undefined
    
    {-
        symtab <- guse envLcl
        let identlkup = lookupSym ident (_Just % _SymProcInfo) symtab
            ident' = _IdentR # (ident, identlkup ^. to fromJust % uniqueTag )
            inslkup = traverse (flip lookupCh symtab) ins
            outslkup = traverse (flip lookupCh symtab) outs
            inslkup' = fromJust inslkup
            outslkup' = fromJust outslkup

            ins' = zipWith 
                (\ch -> review _IdentR 
                    . (ch,) 
                    . view uniqueTag) ins inslkup'
            outs' = zipWith 
                (\ch -> review _IdentR 
                    . (ch,) 
                    . view uniqueTag) outs outslkup'

        tell $ concat 
            [ maybe [_OutOfScope # ident] (const []) identlkup
            , outOfScopesWith lookupCh symtab ins 
            , outOfScopesWith lookupCh symtab outs ]
        -- tell $ maybe (concatMap expectedInputPolarity $ zip ins inslkup') (const []) $ inslkup
        -- tell $ maybe (concatMap expectedOutputPolarity $ zip ins outslkup') (const []) $ outslkup

        seqs' <- traverse (\expr -> do
                expr' <- splitUniqueSupply >=> renameExpr $ pure expr
                -- let bindings change the symbol table, so we make sure
                -- to reset this..
                envLcl .= symtab
                return expr' ) seqs
        return $ _CRun # 
            ( cxt
            , ident'
            , seqs'
            , map (review _ChIdentR . (,Input)  ) ins'
            , map (review _ChIdentR . (,Output) ) outs')
    -}
    CClose cxt ch -> do
        undefined

    {-
    f (CClose cxt ch) = do
        symtab <- guse envLcl
        tell $ outOfScopeWith lookupCh symtab ch 
        let chlkup = lookupCh ch symtab
            chlkup' = fromJust chlkup
            ch' = _ChIdentR # (_IdentR # (ch, chlkup' ^. uniqueTag ), chlkup' ^. symEntryInfo)
        return $ CClose cxt ch'
    f (CHalt cxt ch) = do
        symtab <- guse envLcl
        tell $ outOfScopeWith lookupCh symtab ch 
        let chlkup = lookupCh ch symtab
            chlkup' = fromJust chlkup
            ch' = _ChIdentR # (_IdentR # (ch, chlkup' ^. uniqueTag ), chlkup' ^. symEntryInfo)
        return $ CHalt cxt ch'
    f (CGet cxt patt ch) = do
        symtab <- guse envLcl
        patt' <- renamePattern patt
        tell $ outOfScopeWith lookupCh symtab ch 
        let chlkup = lookupCh ch symtab
            chlkup' = fromJust chlkup
            ch' = _ChIdentR # (_IdentR # (ch, chlkup' ^. uniqueTag ), chlkup' ^. symEntryInfo)
        return $ CGet cxt patt' ch'
    f (CPut cxt expr ch) = do
        symtab <- guse envLcl
        expr' <- renameExpr expr
        tell $ outOfScopeWith lookupCh symtab ch 
        let chlkup = lookupCh ch symtab
            chlkup' = fromJust chlkup
            ch' = _ChIdentR # (_IdentR # (ch, chlkup' ^. uniqueTag ), chlkup' ^. symEntryInfo)
        return $ CPut cxt expr' ch'

    f (CHCase cxt ch cases) = do
        symtab <- guse envLcl
        tell $ outOfScopeWith lookupCh symtab ch
        let chlkup = lookupCh ch symtab
            ch' = do
                chlkup' <- chlkup
                return $ _ChIdentR # (_IdentR # (ch, chlkup' ^. uniqueTag ), chlkup' ^. symEntryInfo)
            ch'' = fromJust ch' 

        cases' <- traverse (g ch') cases
        return $ CHCase cxt ch'' cases'
      where
        g ch' (cxt, ident, cmds) = do
            symtab <- guse envLcl
            tell $ outOfScopeWith lookupConcPhrase symtab ident
            let lkup = lookupConcPhrase ident symtab
                lkup' = fromJust lkup 
                ident' = tagIdentPWithSymEntry ident lkup'

                ch'' = fromJust ch'
            {-
            tell $ bool [] 
                (hCaseError 
                    (ch'' ^. chIdentRIdentR % identRIdentP, ch'' ^. polarity)
                    (ident' ^. identRIdentP, lkup' ^. symEntryInfo)
                    ) 
                (isJust ch' && isJust lkup)
                -}

            cmds' <- splitUniqueSupply $ renameCmds cmds
            envLcl .= symtab
            return (cxt, ident', cmds')
    f (CHPut cxt ident ch) = do
        symtab <- guse envLcl
        tell $ outOfScopeWith lookupCh symtab ch
        tell $ outOfScopeWith lookupConcPhrase symtab ident
        let chlkup = lookupCh ch symtab
            chlkup' = fromJust chlkup
            ch' = _ChIdentR # (_IdentR # (ch, chlkup' ^. uniqueTag ), chlkup' ^. symEntryInfo)

            lkup = lookupConcPhrase ident symtab
            lkup' = fromJust lkup 
            ident' = tagIdentPWithSymEntry ident lkup'

        {-
        tell $ bool [] 
            (hPutError 
                (ch' ^. chIdentRIdentR % identRIdentP, ch' ^. polarity)
                (ident' ^. identRIdentP, lkup' ^. symEntryInfo)
                ) 
            (isJust chlkup && isJust lkup)
        -}

        return $ CHPut cxt ident' ch'
        
    f (CSplit cxt ch (ch1,ch2)) = do
        symtab <- guse envLcl
        tell $ outOfScopeWith lookupCh symtab ch
        let chlkup = lookupCh ch symtab
            chlkup' = fromJust chlkup
            ch' = _ChIdentR # (_IdentR # (ch, chlkup' ^. uniqueTag ), chlkup' ^. symEntryInfo)
        ch1' <- fmap (review _ChIdentR . (,ch' ^. polarity)) $ splitUniqueSupply $ tagIdentP ch1
        ch2' <- fmap (review _ChIdentR . (,ch' ^. polarity)) $ splitUniqueSupply $ tagIdentP ch2
        envLcl %= deleteCh ch
        envLcl %= ((collectSymTab [ch1',ch2'])<>)
        return $ CSplit cxt ch' (ch1',ch2')

    f (CFork cxt ch ((ch1, (p1, cxt1), cmds1), (ch2, (p2, cxt2), cmds2))) = do
        symtab <- guse envLcl
        tell $ outOfScopeWith lookupCh symtab ch
        let chlkup = lookupCh ch symtab
            chlkup' = fromJust chlkup
            ch' = fromJust $ tagIdentPToChIdentRWithSymEntry ch <$> chlkup

            cxt1' = zipWith tagIdentPToChIdentRWithSymEntry cxt1 
                    $ fromJust
                    $ traverse (flip lookupCh symtab) cxt1
            cxt2' = zipWith tagIdentPToChIdentRWithSymEntry cxt2 
                    $ fromJust
                    $ traverse (flip lookupCh symtab) cxt2
            -- TODO: Currently, if there is a user provided context and a variable out of 
            -- scope, this will simply just ignore it... change this so that it really checks
            -- it, by providing the information of whether it was user supplied so we know whether
            -- to do out of scope checks.
        if p1 == UserProvidedContext
            then do 
                tell $ outOfScopesWith lookupCh symtab cxt1 
                tell $ overlappingDeclarations cxt1 
            else return ()
        if p2 == UserProvidedContext
            then do
                tell $ outOfScopesWith lookupCh symtab cxt2 
                tell $ overlappingDeclarations cxt1 
            else return ()

        envLcl %= deleteCh ch
        symtab <- guse envLcl

        -- tell $ forkExpectedDisjointChannelsButHasSharedChannels cxt1 cxt2

        ch1' <- fmap (review _ChIdentR . (,ch' ^. polarity)) $ splitUniqueSupply $ tagIdentP ch1
        ch2' <- fmap (review _ChIdentR . (,ch' ^. polarity)) $ splitUniqueSupply $ tagIdentP ch2

        envLcl .= symtab
        envLcl %= ((collectSymTab ch1')<>) . restrictChs cxt1
        
        cmds1' <- renameCmds cmds1

        envLcl .= symtab
        envLcl %= ((collectSymTab ch2')<>) . restrictChs cxt2
        cmds2' <- renameCmds cmds2

        envLcl .= symtab

        return $ CFork cxt ch' ((ch1', cxt1', cmds1'), (ch2', cxt2', cmds2'))

    f (CId cxt (ch1, ch2)) = do
        symtab <- guse envLcl
        tell $ outOfScopeWith lookupCh symtab ch1
        tell $ outOfScopeWith lookupCh symtab ch2
        let ch1lkup = lookupCh ch1 symtab
            ch1' = fromJust $ tagIdentPToChIdentRWithSymEntry ch1 <$> ch1lkup
            ch2lkup = lookupCh ch2 symtab
            ch2' = fromJust $ tagIdentPToChIdentRWithSymEntry ch2 <$> ch2lkup
        return $ CId cxt (ch1', ch2')

    f (CIdNeg cxt (ch1, ch2)) = do
        symtab <- guse envLcl
        tell $ outOfScopeWith lookupCh symtab ch1
        tell $ outOfScopeWith lookupCh symtab ch2
        let ch1lkup = lookupCh ch1 symtab
            ch1' = fromJust $ tagIdentPToChIdentRWithSymEntry ch1 <$> ch1lkup
            ch2lkup = lookupCh ch2 symtab
            ch2' = fromJust $ tagIdentPToChIdentRWithSymEntry ch2 <$> ch2lkup
        return $ CIdNeg cxt (ch1', ch2')

    f (CRace cxt races) = do
        races' <- traverse g races
        return $ CRace cxt races'
      where
        g (ch, cmds) = do
            symtab <- guse envLcl
            let chlkup = lookupCh ch symtab
                ch' = fromJust $ tagIdentPToChIdentRWithSymEntry ch <$> chlkup
            cmds' <- renameCmds cmds

            envLcl .= symtab

            return (ch', cmds')

    f (CPlugs (keyword, (p, cxt)) (phr1, phr2, phrs)) = do
        ~symtab <- guse envLcl

        sup <- freshUniqueSupply

        let ~scopes = map fst $ channelsInScope symtab
            ~plugged = if p == ComputedContext 
                then cxt \\ scopes
                else cxt
            ~plugged' = (`evalState` sup) $ traverse tagIdentP plugged

        tell $ bool [] (overlappingDeclarations plugged) (p == UserProvidedContext)

        ~(phr1':phr2':phrs') <- traverse (g plugged') (phr1:phr2:phrs)

        return $ CPlugs (keyword, plugged') (phr1', phr2', phrs')
      where
        g :: _ -> ((), ([IdentP], [IdentP]), NonEmpty (MplCmd MplCmdFreeVars)) ->
            _ ((), ([ChIdentR], [ChIdentR]), NonEmpty (MplCmd MplRenamed))
        g plugged ((), (ins, outs), cmds) = do
            initsymtab <- guse envLcl

            -- check overlapping declarations...
            tell $ overlappingDeclarations $ ins ++ outs

            -- restrict and check out of scope for the input channels
            envLcl %= (restrictChs ins (collectSymTab (map (review _ChIdentR . (,Input)) plugged))<>)
            symtab <- guse envLcl
            tell $ outOfScopesWith lookupCh symtab ins 
            let inslkup = fromJust $ traverse (flip lookupCh symtab) ins
                ins' = zipWith tagIdentPToChIdentRWithSymEntry ins inslkup
            -- envLcl %= restrictChs ins

            -- similarly, for the output channels
            envLcl %= (restrictChs outs (collectSymTab (map (review _ChIdentR . (,Output)) plugged))<>)
            symtab <- guse envLcl
            tell $ outOfScopesWith lookupCh symtab outs 
            let outslkup = fromJust $ traverse (flip lookupCh symtab) outs
                outs' = zipWith tagIdentPToChIdentRWithSymEntry outs outslkup
            envLcl %= restrictChs (ins ++ outs)

            ~cmds' <- renameCmds cmds

            envLcl .= initsymtab

            return ((), (ins', outs'), cmds')

    {-
    | CCase 
        !(XCCase x) 
        (XMplExpr x) 
        (NonEmpty (XMplPattern x, NonEmpty (MplCmd x)))
        {-
        { _cCase :: Expr pattern letdef typedef seqcalleddef ident
        , _cCases :: [(pattern, ProcessCommands pattern letdef typedef seqcalleddef conccalleddef ident chident)] }
        -}
    | CSwitch !(XCSwitch x) (NonEmpty (XMplExpr x, NonEmpty (MplCmd x)))
        -- { _cSwitches :: NonEmpty (Expr pattern letdef typedef seqcalleddef ident, ProcessCommands pattern letdef typedef seqcalleddef conccalleddef ident chident) }
        -}
        -}

-------------------------
-- Kind checking
-------------------------
kindCheckProcessType :: 
    TypeCheck 
        ([TypeP MplRenamed], [MplType MplRenamed], [MplType MplRenamed], [MplType MplRenamed]) 
        (Maybe ([TypeP MplTypeChecked], [MplType MplTypeChecked], [MplType MplTypeChecked], [MplType MplTypeChecked]))
kindCheckProcessType proctype@(varsyms, seqs, ins, outs) = do
    symtab <- guse (envLcl % typeInfoSymTab % symTabType)
    
    ~(res, st) <- 
        ( flip runStateT $ _KindCheckEnv #
            ( SeqKind ()
            , Map.fromList $ map (view uniqueTag &&& const Nothing ) varsyms
            ) )
        . ( flip runReaderT symtab) $ do
            seqs' <- traverse 
                (\mpltype -> do
                    kindCheckExpectedPrimitiveKind .= SeqKind ()
                    primitiveKindCheck mpltype) seqs
            ins' <- traverse 
                (\mpltype -> do
                    kindCheckExpectedPrimitiveKind .= ConcKind ()
                    primitiveKindCheck mpltype) ins
            outs' <- traverse 
                (\mpltype -> do
                    kindCheckExpectedPrimitiveKind .= ConcKind ()
                    primitiveKindCheck mpltype) outs
            return $ (,,) <$> sequenceA seqs' <*> sequenceA ins' <*> sequenceA outs'

    return $ do
        ~(seqs',ins',outs') <- res
        return (map NamedType varsyms , seqs', ins', outs')

kindCheckFunType ::
    TypeCheck 
        ([TypeP MplRenamed], [MplType MplRenamed], MplType MplRenamed) 
        ([TypeP MplTypeChecked], [MplType MplTypeChecked], MplType MplTypeChecked)
kindCheckFunType proctype@(varsyms, froms, to) = do
    ~symtab <- guse (envLcl % typeInfoSymTab % symTabType)
    
    ~(froms', to') <- 
        ( flip evalStateT $ _KindCheckEnv # 
            ( SeqKind ()
            , Map.fromList $ map (view uniqueTag &&& const Nothing ) varsyms
            ) ) 
        . (flip runReaderT symtab) $ do
            ~froms' <- traverse 
                (\mpltype -> do
                    kindCheckExpectedPrimitiveKind .= SeqKind ()
                    primitiveKindCheck mpltype)
                    froms

            kindCheckExpectedPrimitiveKind .= SeqKind ()
            to' <- primitiveKindCheck to
            return $ (map fromJust froms', fromJust to')

    return (map NamedType varsyms , froms', to')

-------------------------
-- Utilities
-------------------------
addChToSymTab :: TypeCheck ChIdentR TypeTag
addChToSymTab ch = do
    tag <- freshTypeTag
    let typep = annotateTypeTag tag ch
        ann = typePtoTypeVar typep
    envLcl % typeInfoSymTab % symTabTerm %%= 
        ( (tag,) 
        . ( Map.singleton 
            (ch ^. uniqueTag) 
            (_SymEntry # (SymSub ann , SymChInfo ch)) <>)
        )
        -- ((Map.fromList $ map (view uniqueTag &&&) ins )<>)

