-- Haskell module generated by the BNF converter

module MplLanguage.SkelMPL where

import qualified MplLanguage.AbsMPL

type Err = Either String
type Result = Err String

failure :: Show a => a -> Result
failure x = Left $ "Undefined case: " ++ show x

transPInteger :: MplLanguage.AbsMPL.PInteger -> Result
transPInteger x = case x of
  MplLanguage.AbsMPL.PInteger string -> failure x
transPDouble :: MplLanguage.AbsMPL.PDouble -> Result
transPDouble x = case x of
  MplLanguage.AbsMPL.PDouble string -> failure x
transPChar :: MplLanguage.AbsMPL.PChar -> Result
transPChar x = case x of
  MplLanguage.AbsMPL.PChar string -> failure x
transPString :: MplLanguage.AbsMPL.PString -> Result
transPString x = case x of
  MplLanguage.AbsMPL.PString string -> failure x
transPar :: MplLanguage.AbsMPL.Par -> Result
transPar x = case x of
  MplLanguage.AbsMPL.Par string -> failure x
transTensor :: MplLanguage.AbsMPL.Tensor -> Result
transTensor x = case x of
  MplLanguage.AbsMPL.Tensor string -> failure x
transLBracket :: MplLanguage.AbsMPL.LBracket -> Result
transLBracket x = case x of
  MplLanguage.AbsMPL.LBracket string -> failure x
transRBracket :: MplLanguage.AbsMPL.RBracket -> Result
transRBracket x = case x of
  MplLanguage.AbsMPL.RBracket string -> failure x
transLSquareBracket :: MplLanguage.AbsMPL.LSquareBracket -> Result
transLSquareBracket x = case x of
  MplLanguage.AbsMPL.LSquareBracket string -> failure x
transRSquareBracket :: MplLanguage.AbsMPL.RSquareBracket -> Result
transRSquareBracket x = case x of
  MplLanguage.AbsMPL.RSquareBracket string -> failure x
transNullPattern :: MplLanguage.AbsMPL.NullPattern -> Result
transNullPattern x = case x of
  MplLanguage.AbsMPL.NullPattern string -> failure x
transColon :: MplLanguage.AbsMPL.Colon -> Result
transColon x = case x of
  MplLanguage.AbsMPL.Colon string -> failure x
transInfixl1op :: MplLanguage.AbsMPL.Infixl1op -> Result
transInfixl1op x = case x of
  MplLanguage.AbsMPL.Infixl1op string -> failure x
transInfixl2op :: MplLanguage.AbsMPL.Infixl2op -> Result
transInfixl2op x = case x of
  MplLanguage.AbsMPL.Infixl2op string -> failure x
transInfixl3op :: MplLanguage.AbsMPL.Infixl3op -> Result
transInfixl3op x = case x of
  MplLanguage.AbsMPL.Infixl3op string -> failure x
transInfixl4op :: MplLanguage.AbsMPL.Infixl4op -> Result
transInfixl4op x = case x of
  MplLanguage.AbsMPL.Infixl4op string -> failure x
transInfixl5op :: MplLanguage.AbsMPL.Infixl5op -> Result
transInfixl5op x = case x of
  MplLanguage.AbsMPL.Infixl5op string -> failure x
transInfixl6op :: MplLanguage.AbsMPL.Infixl6op -> Result
transInfixl6op x = case x of
  MplLanguage.AbsMPL.Infixl6op string -> failure x
transInfixr7op :: MplLanguage.AbsMPL.Infixr7op -> Result
transInfixr7op x = case x of
  MplLanguage.AbsMPL.Infixr7op string -> failure x
transInfixl8op :: MplLanguage.AbsMPL.Infixl8op -> Result
transInfixl8op x = case x of
  MplLanguage.AbsMPL.Infixl8op string -> failure x
transClose :: MplLanguage.AbsMPL.Close -> Result
transClose x = case x of
  MplLanguage.AbsMPL.Close string -> failure x
transHalt :: MplLanguage.AbsMPL.Halt -> Result
transHalt x = case x of
  MplLanguage.AbsMPL.Halt string -> failure x
transGet :: MplLanguage.AbsMPL.Get -> Result
transGet x = case x of
  MplLanguage.AbsMPL.Get string -> failure x
transPut :: MplLanguage.AbsMPL.Put -> Result
transPut x = case x of
  MplLanguage.AbsMPL.Put string -> failure x
transHCase :: MplLanguage.AbsMPL.HCase -> Result
transHCase x = case x of
  MplLanguage.AbsMPL.HCase string -> failure x
transHPut :: MplLanguage.AbsMPL.HPut -> Result
transHPut x = case x of
  MplLanguage.AbsMPL.HPut string -> failure x
transSplit :: MplLanguage.AbsMPL.Split -> Result
transSplit x = case x of
  MplLanguage.AbsMPL.Split string -> failure x
transFork :: MplLanguage.AbsMPL.Fork -> Result
transFork x = case x of
  MplLanguage.AbsMPL.Fork string -> failure x
transChId :: MplLanguage.AbsMPL.ChId -> Result
transChId x = case x of
  MplLanguage.AbsMPL.ChId string -> failure x
transCase :: MplLanguage.AbsMPL.Case -> Result
transCase x = case x of
  MplLanguage.AbsMPL.Case string -> failure x
transUIdent :: MplLanguage.AbsMPL.UIdent -> Result
transUIdent x = case x of
  MplLanguage.AbsMPL.UIdent string -> failure x
transPIdent :: MplLanguage.AbsMPL.PIdent -> Result
transPIdent x = case x of
  MplLanguage.AbsMPL.PIdent string -> failure x
transUPIdent :: MplLanguage.AbsMPL.UPIdent -> Result
transUPIdent x = case x of
  MplLanguage.AbsMPL.UPIdent string -> failure x
transMplProg :: MplLanguage.AbsMPL.MplProg -> Result
transMplProg x = case x of
  MplLanguage.AbsMPL.MPL_PROG mplstmts -> failure x
transMplStmt :: MplLanguage.AbsMPL.MplStmt -> Result
transMplStmt x = case x of
  MplLanguage.AbsMPL.MPL_DEFN_STMS_WHERE mpldefns mplwheres -> failure x
  MplLanguage.AbsMPL.MPL_DEFN_STMS mpldefns -> failure x
  MplLanguage.AbsMPL.MPL_STMT mpldefn -> failure x
transMplWhere :: MplLanguage.AbsMPL.MplWhere -> Result
transMplWhere x = case x of
  MplLanguage.AbsMPL.MPL_WHERE mplstmt -> failure x
transMplDefn :: MplLanguage.AbsMPL.MplDefn -> Result
transMplDefn x = case x of
  MplLanguage.AbsMPL.MPL_SEQUENTIAL_TYPE_DEFN sequentialtypedefn -> failure x
  MplLanguage.AbsMPL.MPL_CONCURRENT_TYPE_DEFN concurrenttypedefn -> failure x
  MplLanguage.AbsMPL.MPL_FUNCTION_DEFN functiondefn -> failure x
  MplLanguage.AbsMPL.MPL_PROCESS_DEFN processdefn -> failure x
  MplLanguage.AbsMPL.MPL_DEFNTEST -> failure x
transMplType :: MplLanguage.AbsMPL.MplType -> Result
transMplType x = case x of
  MplLanguage.AbsMPL.MPL_TYPE mpltype -> failure x
  MplLanguage.AbsMPL.PAR_TYPE mpltype1 par mpltype2 -> failure x
  MplLanguage.AbsMPL.TENSOR_TYPE mpltype1 tensor mpltype2 -> failure x
  MplLanguage.AbsMPL.MPL_UIDENT_ARGS_TYPE uident lbracket mpltypes rbracket -> failure x
  MplLanguage.AbsMPL.MPL_UIDENT_SEQ_CONC_ARGS_TYPE uident lbracket mpltypes1 mpltypes2 rbracket -> failure x
  MplLanguage.AbsMPL.MPL_UIDENT_NO_ARGS_TYPE uident -> failure x
  MplLanguage.AbsMPL.MPL_UNIT_TYPE lbracket rbracket -> failure x
  MplLanguage.AbsMPL.MPL_BRACKETED_TYPE lbracket mpltype rbracket -> failure x
  MplLanguage.AbsMPL.MPL_LIST_TYPE lsquarebracket mpltype rsquarebracket -> failure x
  MplLanguage.AbsMPL.MPL_TUPLE_TYPE lbracket mpltype tuplelisttypes rbracket -> failure x
  MplLanguage.AbsMPL.MPL_SEQ_ARROW_TYPE forallvarlists mpltypes mpltype -> failure x
  MplLanguage.AbsMPL.MPL_CONC_ARROW_TYPE forallvarlists mpltypes1 mpltypes2 mpltypes3 -> failure x
transTupleListType :: MplLanguage.AbsMPL.TupleListType -> Result
transTupleListType x = case x of
  MplLanguage.AbsMPL.TUPLE_LIST_TYPE mpltype -> failure x
transForallVarList :: MplLanguage.AbsMPL.ForallVarList -> Result
transForallVarList x = case x of
  MplLanguage.AbsMPL.MPL_SEQ_FUN_TYPE_FORALL_LIST uident -> failure x
transSequentialTypeDefn :: MplLanguage.AbsMPL.SequentialTypeDefn -> Result
transSequentialTypeDefn x = case x of
  MplLanguage.AbsMPL.DATA_DEFN seqtypeclausedefns -> failure x
  MplLanguage.AbsMPL.CODATA_DEFN seqtypeclausedefns -> failure x
transSeqTypeClauseDefn :: MplLanguage.AbsMPL.SeqTypeClauseDefn -> Result
transSeqTypeClauseDefn x = case x of
  MplLanguage.AbsMPL.SEQ_TYPE_CLAUSE mpltype1 mpltype2 seqtypephrasedefns -> failure x
transSeqTypePhraseDefn :: MplLanguage.AbsMPL.SeqTypePhraseDefn -> Result
transSeqTypePhraseDefn x = case x of
  MplLanguage.AbsMPL.SEQ_TYPE_PHRASE typehandlenames mpltypes mpltype -> failure x
transConcurrentTypeDefn :: MplLanguage.AbsMPL.ConcurrentTypeDefn -> Result
transConcurrentTypeDefn x = case x of
  MplLanguage.AbsMPL.PROTOCOL_DEFN concurrenttypeclausedefns -> failure x
  MplLanguage.AbsMPL.COPROTOCOL_DEFN concurrenttypeclausedefns -> failure x
transConcurrentTypeClauseDefn :: MplLanguage.AbsMPL.ConcurrentTypeClauseDefn -> Result
transConcurrentTypeClauseDefn x = case x of
  MplLanguage.AbsMPL.CONCURRENT_TYPE_CLAUSE mpltype1 mpltype2 concurrenttypephrasedefns -> failure x
transConcurrentTypePhraseDefn :: MplLanguage.AbsMPL.ConcurrentTypePhraseDefn -> Result
transConcurrentTypePhraseDefn x = case x of
  MplLanguage.AbsMPL.CONCURRENT_TYPE_PHRASE typehandlenames mpltype1 mpltype2 -> failure x
transTypeHandleName :: MplLanguage.AbsMPL.TypeHandleName -> Result
transTypeHandleName x = case x of
  MplLanguage.AbsMPL.TYPE_HANDLE_NAME uident -> failure x
transExpr :: MplLanguage.AbsMPL.Expr -> Result
transExpr x = case x of
  MplLanguage.AbsMPL.EXPR expr -> failure x
  MplLanguage.AbsMPL.TYPED_EXPR expr mpltype -> failure x
  MplLanguage.AbsMPL.IF_EXPR expr1 expr2 expr3 -> failure x
  MplLanguage.AbsMPL.LET_EXPR letexprphrases expr -> failure x
  MplLanguage.AbsMPL.INFIXR0_EXPR expr1 colon expr2 -> failure x
  MplLanguage.AbsMPL.INFIXL1_EXPR expr1 infixlop expr2 -> failure x
  MplLanguage.AbsMPL.INFIXL2_EXPR expr1 infixlop expr2 -> failure x
  MplLanguage.AbsMPL.INFIXL3_EXPR expr1 infixlop expr2 -> failure x
  MplLanguage.AbsMPL.INFIXL4_EXPR expr1 infixlop expr2 -> failure x
  MplLanguage.AbsMPL.INFIXL5_EXPR expr1 infixlop expr2 -> failure x
  MplLanguage.AbsMPL.INFIXL6_EXPR expr1 infixlop expr2 -> failure x
  MplLanguage.AbsMPL.INFIXR7_EXPR expr1 infixrop expr2 -> failure x
  MplLanguage.AbsMPL.INFIXL8_EXPR expr1 infixlop expr2 -> failure x
  MplLanguage.AbsMPL.LIST_EXPR lsquarebracket exprs rsquarebracket -> failure x
  MplLanguage.AbsMPL.VAR_EXPR pident -> failure x
  MplLanguage.AbsMPL.INT_EXPR pinteger -> failure x
  MplLanguage.AbsMPL.STRING_EXPR pstring -> failure x
  MplLanguage.AbsMPL.CHAR_EXPR pchar -> failure x
  MplLanguage.AbsMPL.DOUBLE_EXPR pdouble -> failure x
  MplLanguage.AbsMPL.UNIT_EXPR lbracket rbracket -> failure x
  MplLanguage.AbsMPL.FOLD_EXPR expr foldexprphrases -> failure x
  MplLanguage.AbsMPL.UNFOLD_EXPR expr unfoldexprphrases -> failure x
  MplLanguage.AbsMPL.CASE_EXPR case_ expr pattexprphrases -> failure x
  MplLanguage.AbsMPL.SWITCH_EXP switchexprphrases -> failure x
  MplLanguage.AbsMPL.DESTRUCTOR_CONSTRUCTOR_ARGS_EXPR uident lbracket exprs rbracket -> failure x
  MplLanguage.AbsMPL.DESTRUCTOR_CONSTRUCTOR_NO_ARGS_EXPR uident -> failure x
  MplLanguage.AbsMPL.TUPLE_EXPR lbracket expr tupleexprlists rbracket -> failure x
  MplLanguage.AbsMPL.FUN_EXPR pident lbracket exprs rbracket -> failure x
  MplLanguage.AbsMPL.RECORD_EXPR lbracket recordexprphrases rbracket -> failure x
  MplLanguage.AbsMPL.BRACKETED_EXPR lbracket expr rbracket -> failure x
transUnfoldExprPhrase :: MplLanguage.AbsMPL.UnfoldExprPhrase -> Result
transUnfoldExprPhrase x = case x of
  MplLanguage.AbsMPL.UNFOLD_EXPR_PHRASE pattern_ foldexprphrases -> failure x
transFoldExprPhrase :: MplLanguage.AbsMPL.FoldExprPhrase -> Result
transFoldExprPhrase x = case x of
  MplLanguage.AbsMPL.FOLD_EXPR_PHRASE uident colon patterns expr -> failure x
transLetExprPhrase :: MplLanguage.AbsMPL.LetExprPhrase -> Result
transLetExprPhrase x = case x of
  MplLanguage.AbsMPL.LET_EXPR_PHRASE mplstmt -> failure x
transTupleExprList :: MplLanguage.AbsMPL.TupleExprList -> Result
transTupleExprList x = case x of
  MplLanguage.AbsMPL.TUPLE_EXPR_LIST expr -> failure x
transRecordExprPhrase :: MplLanguage.AbsMPL.RecordExprPhrase -> Result
transRecordExprPhrase x = case x of
  MplLanguage.AbsMPL.RECORD_EXPR_PHRASE uident expr -> failure x
  MplLanguage.AbsMPL.RECORD_EXPR_HIGHER_ORDER_PHRASE uident pattexprphrase -> failure x
transSwitchExprPhrase :: MplLanguage.AbsMPL.SwitchExprPhrase -> Result
transSwitchExprPhrase x = case x of
  MplLanguage.AbsMPL.SWITCH_EXPR_PHRASE expr1 expr2 -> failure x
transPattExprPhrase :: MplLanguage.AbsMPL.PattExprPhrase -> Result
transPattExprPhrase x = case x of
  MplLanguage.AbsMPL.PATTERN_TO_EXPR patterns expr -> failure x
transPattern :: MplLanguage.AbsMPL.Pattern -> Result
transPattern x = case x of
  MplLanguage.AbsMPL.PATTERN pattern_ -> failure x
  MplLanguage.AbsMPL.TYPED_PATTERN pattern_ mpltype -> failure x
  MplLanguage.AbsMPL.LIST_COLON_PATTERN pattern_1 colon pattern_2 -> failure x
  MplLanguage.AbsMPL.CONSTRUCTOR_PATTERN_ARGS uident lbracket patterns rbracket -> failure x
  MplLanguage.AbsMPL.CONSTRUCTOR_PATTERN_NO_ARGS uident -> failure x
  MplLanguage.AbsMPL.UNIT_PATTERN lbracket rbracket -> failure x
  MplLanguage.AbsMPL.RECORD_PATTERN lbracket destructorpatternphrases rbracket -> failure x
  MplLanguage.AbsMPL.LIST_PATTERN lsquarebracket patterns rsquarebracket -> failure x
  MplLanguage.AbsMPL.TUPLE_PATTERN lbracket pattern_ tuplelistpatterns rbracket -> failure x
  MplLanguage.AbsMPL.VAR_PATTERN pident -> failure x
  MplLanguage.AbsMPL.STR_PATTERN pstring -> failure x
  MplLanguage.AbsMPL.CHAR_PATTERN pchar -> failure x
  MplLanguage.AbsMPL.INT_PATTERN pinteger -> failure x
  MplLanguage.AbsMPL.NULL_PATTERN nullpattern -> failure x
  MplLanguage.AbsMPL.BRACKETED_PATTERN lbracket pattern_ rbracket -> failure x
transTupleListPattern :: MplLanguage.AbsMPL.TupleListPattern -> Result
transTupleListPattern x = case x of
  MplLanguage.AbsMPL.TUPLE_LIST_PATTERN pattern_ -> failure x
transDestructorPatternPhrase :: MplLanguage.AbsMPL.DestructorPatternPhrase -> Result
transDestructorPatternPhrase x = case x of
  MplLanguage.AbsMPL.DESTRUCTOR_PATTERN_PHRASE uident pattern_ -> failure x
transFunctionDefn :: MplLanguage.AbsMPL.FunctionDefn -> Result
transFunctionDefn x = case x of
  MplLanguage.AbsMPL.INTERNAL_TYPED_FUNCTION_DEFN pident mpltype pattexprphrases -> failure x
  MplLanguage.AbsMPL.TYPED_FUNCTION_DEFN pident mpltypes mpltype pattexprphrases -> failure x
  MplLanguage.AbsMPL.FUNCTION_DEFN pident pattexprphrases -> failure x
transProcessDefn :: MplLanguage.AbsMPL.ProcessDefn -> Result
transProcessDefn x = case x of
  MplLanguage.AbsMPL.TYPED_PROCESS_DEFN pident mpltypes1 mpltypes2 mpltypes3 processphrases -> failure x
  MplLanguage.AbsMPL.INTERNAL_TYPED_PROCESS_DEFN pident mpltype processphrases -> failure x
  MplLanguage.AbsMPL.PROCESS_DEFN pident processphrases -> failure x
transProcessPhrase :: MplLanguage.AbsMPL.ProcessPhrase -> Result
transProcessPhrase x = case x of
  MplLanguage.AbsMPL.PROCESS_PHRASE patterns pidents1 pidents2 processcommandsblock -> failure x
transProcessCommandsBlock :: MplLanguage.AbsMPL.ProcessCommandsBlock -> Result
transProcessCommandsBlock x = case x of
  MplLanguage.AbsMPL.PROCESS_COMMANDS_DO_BLOCK processcommands -> failure x
  MplLanguage.AbsMPL.PROCESS_COMMANDS_SINGLE_COMMAND_BLOCK processcommand -> failure x
transProcessCommand :: MplLanguage.AbsMPL.ProcessCommand -> Result
transProcessCommand x = case x of
  MplLanguage.AbsMPL.PROCESS_RUN pident lbracket exprs pidents1 pidents2 rbracket -> failure x
  MplLanguage.AbsMPL.PROCESS_CLOSE close pident -> failure x
  MplLanguage.AbsMPL.PROCESS_HALT halt pident -> failure x
  MplLanguage.AbsMPL.PROCESS_GET get pattern_ pident -> failure x
  MplLanguage.AbsMPL.PROCESS_PUT put expr pident -> failure x
  MplLanguage.AbsMPL.PROCESS_HCASE hcase pident hcasephrases -> failure x
  MplLanguage.AbsMPL.PROCESS_HPUT hput uident pident -> failure x
  MplLanguage.AbsMPL.PROCESS_SPLIT split pident splitchannels -> failure x
  MplLanguage.AbsMPL.PROCESS_FORK fork pident forkphrases -> failure x
  MplLanguage.AbsMPL.PROCESS_ID pident1 chid pident2 -> failure x
  MplLanguage.AbsMPL.PROCESS_NEG pident1 chid pident2 -> failure x
  MplLanguage.AbsMPL.PROCESS_RACE racephrases -> failure x
  MplLanguage.AbsMPL.PROCESS_PLUG plugphrases -> failure x
  MplLanguage.AbsMPL.PROCESS_CASE case_ expr processcasephrases -> failure x
  MplLanguage.AbsMPL.PROCESS_IF expr processcommandsblock1 processcommandsblock2 -> failure x
  MplLanguage.AbsMPL.PROCESS_SWITCH processswitchphrases -> failure x
transHCasePhrase :: MplLanguage.AbsMPL.HCasePhrase -> Result
transHCasePhrase x = case x of
  MplLanguage.AbsMPL.HCASE_PHRASE uident processcommandsblock -> failure x
transSplitChannel :: MplLanguage.AbsMPL.SplitChannel -> Result
transSplitChannel x = case x of
  MplLanguage.AbsMPL.SPLIT_CHANNEL pident -> failure x
transForkPhrase :: MplLanguage.AbsMPL.ForkPhrase -> Result
transForkPhrase x = case x of
  MplLanguage.AbsMPL.FORK_PHRASE pident processcommandsblock -> failure x
  MplLanguage.AbsMPL.FORK_WITH_PHRASE pident forkchannels processcommandsblock -> failure x
transForkChannel :: MplLanguage.AbsMPL.ForkChannel -> Result
transForkChannel x = case x of
  MplLanguage.AbsMPL.FORK_CHANNEL pident -> failure x
transRacePhrase :: MplLanguage.AbsMPL.RacePhrase -> Result
transRacePhrase x = case x of
  MplLanguage.AbsMPL.RACE_PHRASE pident processcommandsblock -> failure x
transPlugPhrase :: MplLanguage.AbsMPL.PlugPhrase -> Result
transPlugPhrase x = case x of
  MplLanguage.AbsMPL.PLUG_PHRASE processcommandsblock -> failure x
  MplLanguage.AbsMPL.PLUG_PHRASE_AS pidents1 pidents2 processcommandsblock -> failure x
transProcessCasePhrase :: MplLanguage.AbsMPL.ProcessCasePhrase -> Result
transProcessCasePhrase x = case x of
  MplLanguage.AbsMPL.PROCESS_CASE_PHRASE pattern_ processcommandsblock -> failure x
transProcessSwitchPhrase :: MplLanguage.AbsMPL.ProcessSwitchPhrase -> Result
transProcessSwitchPhrase x = case x of
  MplLanguage.AbsMPL.PROCESS_SWITCH_PHRASE expr processcommandsblock -> failure x

