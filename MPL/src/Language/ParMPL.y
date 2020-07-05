-- This Happy file was machine-generated by the BNF converter
{
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns #-}
module Language.ParMPL where
import Language.AbsMPL
import Language.LexMPL
import Language.ErrM

}

%name pMplProg MplProg
-- no lexer declaration
%monad { Err } { thenM } { returnM }
%tokentype {Token}
%token
  ',' { PT _ (TS _ 1) }
  '->' { PT _ (TS _ 2) }
  '::' { PT _ (TS _ 3) }
  ':=' { PT _ (TS _ 4) }
  ';' { PT _ (TS _ 5) }
  '=' { PT _ (TS _ 6) }
  '=>' { PT _ (TS _ 7) }
  'and' { PT _ (TS _ 8) }
  'as' { PT _ (TS _ 9) }
  'case' { PT _ (TS _ 10) }
  'close' { PT _ (TS _ 11) }
  'codata' { PT _ (TS _ 12) }
  'coprotocol' { PT _ (TS _ 13) }
  'data' { PT _ (TS _ 14) }
  'defn' { PT _ (TS _ 15) }
  'do' { PT _ (TS _ 16) }
  'else' { PT _ (TS _ 17) }
  'fold' { PT _ (TS _ 18) }
  'fork' { PT _ (TS _ 19) }
  'fun' { PT _ (TS _ 20) }
  'get' { PT _ (TS _ 21) }
  'halt' { PT _ (TS _ 22) }
  'hcase' { PT _ (TS _ 23) }
  'hput' { PT _ (TS _ 24) }
  'if' { PT _ (TS _ 25) }
  'in' { PT _ (TS _ 26) }
  'into' { PT _ (TS _ 27) }
  'let' { PT _ (TS _ 28) }
  'neg' { PT _ (TS _ 29) }
  'of' { PT _ (TS _ 30) }
  'on' { PT _ (TS _ 31) }
  'plug' { PT _ (TS _ 32) }
  'potato' { PT _ (TS _ 33) }
  'proc' { PT _ (TS _ 34) }
  'protocol' { PT _ (TS _ 35) }
  'put' { PT _ (TS _ 36) }
  'race' { PT _ (TS _ 37) }
  'split' { PT _ (TS _ 38) }
  'switch' { PT _ (TS _ 39) }
  'then' { PT _ (TS _ 40) }
  'unfold' { PT _ (TS _ 41) }
  'where' { PT _ (TS _ 42) }
  'with' { PT _ (TS _ 43) }
  '{' { PT _ (TS _ 44) }
  '|' { PT _ (TS _ 45) }
  '|=|' { PT _ (TS _ 46) }
  '}' { PT _ (TS _ 47) }
  L_quoted { PT _ (TL $$) }
  L_charac { PT _ (TC $$) }
  L_doubl  { PT _ (TD $$) }
  L_UIdent { PT _ (T_UIdent _) }
  L_PIdent { PT _ (T_PIdent _) }
  L_PInteger { PT _ (T_PInteger _) }
  L_Par { PT _ (T_Par _) }
  L_Tensor { PT _ (T_Tensor _) }
  L_LBracket { PT _ (T_LBracket _) }
  L_RBracket { PT _ (T_RBracket _) }
  L_LSquareBracket { PT _ (T_LSquareBracket _) }
  L_RSquareBracket { PT _ (T_RSquareBracket _) }
  L_NullPattern { PT _ (T_NullPattern _) }
  L_Colon { PT _ (T_Colon _) }
  L_Infixl1op { PT _ (T_Infixl1op $$) }
  L_Infixl2op { PT _ (T_Infixl2op $$) }
  L_Infixl3op { PT _ (T_Infixl3op $$) }
  L_Infixl4op { PT _ (T_Infixl4op $$) }
  L_Infixl5op { PT _ (T_Infixl5op $$) }
  L_Infixl6op { PT _ (T_Infixl6op $$) }
  L_Infixr7op { PT _ (T_Infixr7op $$) }
  L_Infixl8op { PT _ (T_Infixl8op $$) }

%%

String  :: { String }
String   : L_quoted {  $1 }

Char    :: { Char }
Char     : L_charac { (read ( $1)) :: Char }

Double  :: { Double }
Double   : L_doubl  { (read ( $1)) :: Double }

UIdent :: { UIdent}
UIdent  : L_UIdent { UIdent (mkPosToken $1)}

PIdent :: { PIdent}
PIdent  : L_PIdent { PIdent (mkPosToken $1)}

PInteger :: { PInteger}
PInteger  : L_PInteger { PInteger (mkPosToken $1)}

Par :: { Par}
Par  : L_Par { Par (mkPosToken $1)}

Tensor :: { Tensor}
Tensor  : L_Tensor { Tensor (mkPosToken $1)}

LBracket :: { LBracket}
LBracket  : L_LBracket { LBracket (mkPosToken $1)}

RBracket :: { RBracket}
RBracket  : L_RBracket { RBracket (mkPosToken $1)}

LSquareBracket :: { LSquareBracket}
LSquareBracket  : L_LSquareBracket { LSquareBracket (mkPosToken $1)}

RSquareBracket :: { RSquareBracket}
RSquareBracket  : L_RSquareBracket { RSquareBracket (mkPosToken $1)}

NullPattern :: { NullPattern}
NullPattern  : L_NullPattern { NullPattern (mkPosToken $1)}

Colon :: { Colon}
Colon  : L_Colon { Colon (mkPosToken $1)}

Infixl1op :: { Infixl1op}
Infixl1op  : L_Infixl1op { Infixl1op ($1)}

Infixl2op :: { Infixl2op}
Infixl2op  : L_Infixl2op { Infixl2op ($1)}

Infixl3op :: { Infixl3op}
Infixl3op  : L_Infixl3op { Infixl3op ($1)}

Infixl4op :: { Infixl4op}
Infixl4op  : L_Infixl4op { Infixl4op ($1)}

Infixl5op :: { Infixl5op}
Infixl5op  : L_Infixl5op { Infixl5op ($1)}

Infixl6op :: { Infixl6op}
Infixl6op  : L_Infixl6op { Infixl6op ($1)}

Infixr7op :: { Infixr7op}
Infixr7op  : L_Infixr7op { Infixr7op ($1)}

Infixl8op :: { Infixl8op}
Infixl8op  : L_Infixl8op { Infixl8op ($1)}

ListPIdent :: { [PIdent] }
ListPIdent : {- empty -} { [] }
           | PIdent { (:[]) $1 }
           | PIdent ',' ListPIdent { (:) $1 $3 }
MplProg :: { MplProg }
MplProg : ListMplStmt { Language.AbsMPL.MPL_PROG (reverse $1) }
MplStmt :: { MplStmt }
MplStmt : 'defn' '{' ListMplDefn '}' 'where' '{' ListMplStmt '}' { Language.AbsMPL.MPL_DEFN_STMS_WHERE $3 (reverse $7) }
        | 'defn' '{' ListMplDefn '}' { Language.AbsMPL.MPL_DEFN_STMS $3 }
        | MplDefn { Language.AbsMPL.MPL_STMT $1 }
ListMplDefn :: { [MplDefn] }
ListMplDefn : MplDefn { (:[]) $1 }
            | MplDefn ';' ListMplDefn { (:) $1 $3 }
ListMplStmt :: { [MplStmt] }
ListMplStmt : {- empty -} { [] }
            | ListMplStmt MplStmt { flip (:) $1 $2 }
MplDefn :: { MplDefn }
MplDefn : SequentialTypeDefn { Language.AbsMPL.MPL_SEQUENTIAL_TYPE_DEFN $1 }
        | ConcurrentTypeDefn { Language.AbsMPL.MPL_CONCURRENT_TYPE_DEFN $1 }
        | FunctionDefn { Language.AbsMPL.MPL_FUNCTION_DEFN $1 }
        | ProcessDefn { Language.AbsMPL.MPL_PROCESS_DEFN $1 }
        | 'potato' { Language.AbsMPL.MPL_DEFNTEST }
MplType :: { MplType }
MplType : MplType0 { Language.AbsMPL.MPL_TYPE $1 }
MplType0 :: { MplType }
MplType0 : MplType1 Par MplType1 { Language.AbsMPL.PAR_TYPE $1 $2 $3 }
         | MplType1 { $1 }
MplType1 :: { MplType }
MplType1 : MplType2 Tensor MplType2 { Language.AbsMPL.TENSOR_TYPE $1 $2 $3 }
         | MplType2 { $1 }
MplType2 :: { MplType }
MplType2 : UIdent LBracket MplType '|' MplType RBracket { Language.AbsMPL.GETPUT_TYPE $1 $2 $3 $5 $6 }
         | MplType3 { $1 }
MplType3 :: { MplType }
MplType3 : UIdent LBracket ListMplType RBracket { Language.AbsMPL.MPL_UIDENT_ARGS_TYPE $1 $2 $3 $4 }
         | UIdent { Language.AbsMPL.MPL_UIDENT_NO_ARGS_TYPE $1 }
         | LBracket RBracket { Language.AbsMPL.MPL_UNIT_TYPE $1 $2 }
         | LBracket MplType RBracket { Language.AbsMPL.MPL_BRACKETED_TYPE $1 $2 $3 }
         | LSquareBracket MplType RSquareBracket { Language.AbsMPL.MPL_LIST_TYPE $1 $2 $3 }
         | LBracket MplType ',' ListTupleListType RBracket { Language.AbsMPL.MPL_TUPLE_TYPE $1 $2 $4 $5 }
TupleListType :: { TupleListType }
TupleListType : MplType { Language.AbsMPL.TUPLE_LIST_TYPE $1 }
ListTupleListType :: { [TupleListType] }
ListTupleListType : TupleListType { (:[]) $1 }
                  | TupleListType ',' ListTupleListType { (:) $1 $3 }
ListMplType :: { [MplType] }
ListMplType : {- empty -} { [] }
            | MplType { (:[]) $1 }
            | MplType ',' ListMplType { (:) $1 $3 }
SequentialTypeDefn :: { SequentialTypeDefn }
SequentialTypeDefn : 'data' ListSeqTypeClauseDefn { Language.AbsMPL.DATA_DEFN $2 }
                   | 'codata' ListSeqTypeClauseDefn { Language.AbsMPL.CODATA_DEFN $2 }
SeqTypeClauseDefn :: { SeqTypeClauseDefn }
SeqTypeClauseDefn : MplType '->' MplType '=' '{' ListSeqTypePhraseDefn '}' { Language.AbsMPL.SEQ_TYPE_CLAUSE $1 $3 $6 }
SeqTypePhraseDefn :: { SeqTypePhraseDefn }
SeqTypePhraseDefn : ListTypeHandleName '::' ListMplType '->' MplType { Language.AbsMPL.SEQ_TYPE_PHRASE $1 $3 $5 }
ListSeqTypeClauseDefn :: { [SeqTypeClauseDefn] }
ListSeqTypeClauseDefn : SeqTypeClauseDefn { (:[]) $1 }
                      | SeqTypeClauseDefn 'and' ListSeqTypeClauseDefn { (:) $1 $3 }
ListSeqTypePhraseDefn :: { [SeqTypePhraseDefn] }
ListSeqTypePhraseDefn : {- empty -} { [] }
                      | SeqTypePhraseDefn { (:[]) $1 }
                      | SeqTypePhraseDefn ';' ListSeqTypePhraseDefn { (:) $1 $3 }
ConcurrentTypeDefn :: { ConcurrentTypeDefn }
ConcurrentTypeDefn : 'protocol' ListConcurrentTypeClauseDefn { Language.AbsMPL.PROTOCOL_DEFN $2 }
                   | 'coprotocol' ListConcurrentTypeClauseDefn { Language.AbsMPL.COPROTOCOL_DEFN $2 }
ConcurrentTypeClauseDefn :: { ConcurrentTypeClauseDefn }
ConcurrentTypeClauseDefn : MplType '=>' MplType '=' '{' ListConcurrentTypePhraseDefn '}' { Language.AbsMPL.CONCURRENT_TYPE_CLAUSE $1 $3 $6 }
ConcurrentTypePhraseDefn :: { ConcurrentTypePhraseDefn }
ConcurrentTypePhraseDefn : ListTypeHandleName '::' MplType '=>' MplType { Language.AbsMPL.CONCURRENT_TYPE_PHRASE $1 $3 $5 }
ListConcurrentTypeClauseDefn :: { [ConcurrentTypeClauseDefn] }
ListConcurrentTypeClauseDefn : ConcurrentTypeClauseDefn { (:[]) $1 }
                             | ConcurrentTypeClauseDefn 'and' ListConcurrentTypeClauseDefn { (:) $1 $3 }
ListConcurrentTypePhraseDefn :: { [ConcurrentTypePhraseDefn] }
ListConcurrentTypePhraseDefn : {- empty -} { [] }
                             | ConcurrentTypePhraseDefn { (:[]) $1 }
                             | ConcurrentTypePhraseDefn ';' ListConcurrentTypePhraseDefn { (:) $1 $3 }
TypeHandleName :: { TypeHandleName }
TypeHandleName : UIdent { Language.AbsMPL.TYPE_HANDLE_NAME $1 }
ListTypeHandleName :: { [TypeHandleName] }
ListTypeHandleName : TypeHandleName { (:[]) $1 }
                   | TypeHandleName ',' ListTypeHandleName { (:) $1 $3 }
Expr :: { Expr }
Expr : Expr0 { Language.AbsMPL.EXPR $1 }
     | 'if' Expr 'then' Expr 'else' Expr { Language.AbsMPL.IF_EXPR $2 $4 $6 }
     | 'let' '{' ListLetExprPhrase '}' 'in' Expr { Language.AbsMPL.LET_EXPR $3 $6 }
Expr0 :: { Expr }
Expr0 : Expr1 Colon Expr0 { Language.AbsMPL.INFIXR0_EXPR $1 $2 $3 }
      | Expr1 { $1 }
Expr1 :: { Expr }
Expr1 : Expr1 Infixl1op Expr2 { Language.AbsMPL.INFIXL1_EXPR $1 $2 $3 }
      | Expr2 { $1 }
Expr2 :: { Expr }
Expr2 : Expr2 Infixl2op Expr3 { Language.AbsMPL.INFIXL2_EXPR $1 $2 $3 }
      | Expr3 { $1 }
Expr3 :: { Expr }
Expr3 : Expr3 Infixl3op Expr4 { Language.AbsMPL.INFIXL3_EXPR $1 $2 $3 }
      | Expr4 { $1 }
Expr4 :: { Expr }
Expr4 : Expr4 Infixl4op Expr5 { Language.AbsMPL.INFIXL4_EXPR $1 $2 $3 }
      | Expr5 { $1 }
Expr5 :: { Expr }
Expr5 : Expr5 Infixl5op Expr6 { Language.AbsMPL.INFIXL5_EXPR $1 $2 $3 }
      | Expr6 { $1 }
Expr6 :: { Expr }
Expr6 : Expr6 Infixl6op Expr7 { Language.AbsMPL.INFIXL6_EXPR $1 $2 $3 }
      | Expr7 { $1 }
Expr7 :: { Expr }
Expr7 : Expr8 Infixr7op Expr7 { Language.AbsMPL.INFIXR7_EXPR $1 $2 $3 }
      | Expr8 { $1 }
Expr8 :: { Expr }
Expr8 : Expr8 Infixl8op Expr10 { Language.AbsMPL.INFIXL8_EXPR $1 $2 $3 }
      | Expr10 { $1 }
Expr10 :: { Expr }
Expr10 : LSquareBracket ListExpr RSquareBracket { Language.AbsMPL.LIST_EXPR $1 $2 $3 }
       | PIdent { Language.AbsMPL.VAR_EXPR $1 }
       | PInteger { Language.AbsMPL.INT_EXPR $1 }
       | String { Language.AbsMPL.STRING_EXPR $1 }
       | Char { Language.AbsMPL.CHAR_EXPR $1 }
       | Double { Language.AbsMPL.DOUBLE_EXPR $1 }
       | LBracket RBracket { Language.AbsMPL.UNIT_EXPR $1 $2 }
       | 'fold' Expr 'of' '{' ListFoldExprPhrase '}' { Language.AbsMPL.FOLD_EXPR $2 $5 }
       | 'unfold' Expr 'of' '{' ListUnfoldExprPhrase '}' { Language.AbsMPL.UNFOLD_EXPR $2 $5 }
       | 'case' Expr 'of' '{' ListPattExprPhrase '}' { Language.AbsMPL.CASE_EXPR $2 $5 }
       | 'switch' '{' ListSwitchExprPhrase '}' { Language.AbsMPL.SWITCH_EXP $3 }
       | UIdent LBracket ListExpr RBracket { Language.AbsMPL.DESTRUCTOR_CONSTRUCTOR_ARGS_EXPR $1 $2 $3 $4 }
       | UIdent { Language.AbsMPL.DESTRUCTOR_CONSTRUCTOR_NO_ARGS_EXPR $1 }
       | LBracket Expr ',' ListTupleExprList RBracket { Language.AbsMPL.TUPLE_EXPR $1 $2 $4 $5 }
       | PIdent LBracket ListExpr RBracket { Language.AbsMPL.FUN_EXPR $1 $2 $3 $4 }
       | LBracket ListRecordExprPhrase RBracket { Language.AbsMPL.RECORD_EXPR $1 $2 $3 }
       | LBracket Expr RBracket { Language.AbsMPL.BRACKETED_EXPR $1 $2 $3 }
UnfoldExprPhrase :: { UnfoldExprPhrase }
UnfoldExprPhrase : Pattern 'of' '{' ListFoldExprPhrase '}' { Language.AbsMPL.UNFOLD_EXPR_PHRASE $1 $4 }
ListUnfoldExprPhrase :: { [UnfoldExprPhrase] }
ListUnfoldExprPhrase : {- empty -} { [] }
                     | UnfoldExprPhrase { (:[]) $1 }
                     | UnfoldExprPhrase ';' ListUnfoldExprPhrase { (:) $1 $3 }
FoldExprPhrase :: { FoldExprPhrase }
FoldExprPhrase : UIdent Colon ListPattern '->' Expr { Language.AbsMPL.FOLD_EXPR_PHRASE $1 $2 $3 $5 }
ListFoldExprPhrase :: { [FoldExprPhrase] }
ListFoldExprPhrase : {- empty -} { [] }
                   | FoldExprPhrase { (:[]) $1 }
                   | FoldExprPhrase ';' ListFoldExprPhrase { (:) $1 $3 }
LetExprPhrase :: { LetExprPhrase }
LetExprPhrase : MplStmt { Language.AbsMPL.LET_EXPR_PHRASE $1 }
ListLetExprPhrase :: { [LetExprPhrase] }
ListLetExprPhrase : LetExprPhrase { (:[]) $1 }
                  | LetExprPhrase ';' ListLetExprPhrase { (:) $1 $3 }
TupleExprList :: { TupleExprList }
TupleExprList : Expr { Language.AbsMPL.TUPLE_EXPR_LIST $1 }
ListTupleExprList :: { [TupleExprList] }
ListTupleExprList : TupleExprList { (:[]) $1 }
                  | TupleExprList ',' ListTupleExprList { (:) $1 $3 }
RecordExprPhrase :: { RecordExprPhrase }
RecordExprPhrase : UIdent ':=' Expr { Language.AbsMPL.RECORD_EXPR_PHRASE $1 $3 }
ListRecordExprPhrase :: { [RecordExprPhrase] }
ListRecordExprPhrase : RecordExprPhrase { (:[]) $1 }
                     | RecordExprPhrase ',' ListRecordExprPhrase { (:) $1 $3 }
SwitchExprPhrase :: { SwitchExprPhrase }
SwitchExprPhrase : Expr '->' Expr { Language.AbsMPL.SWITCH_EXPR_PHRASE $1 $3 }
ListSwitchExprPhrase :: { [SwitchExprPhrase] }
ListSwitchExprPhrase : SwitchExprPhrase { (:[]) $1 }
                     | SwitchExprPhrase ';' ListSwitchExprPhrase { (:) $1 $3 }
ListExpr :: { [Expr] }
ListExpr : {- empty -} { [] }
         | Expr { (:[]) $1 }
         | Expr ',' ListExpr { (:) $1 $3 }
PattExprPhrase :: { PattExprPhrase }
PattExprPhrase : ListPattern '->' Expr { Language.AbsMPL.PATTERN_TO_EXPR $1 $3 }
Pattern :: { Pattern }
Pattern : Pattern0 { Language.AbsMPL.PATTERN $1 }
ListPattern :: { [Pattern] }
ListPattern : {- empty -} { [] }
            | Pattern { (:[]) $1 }
            | Pattern ',' ListPattern { (:) $1 $3 }
Pattern0 :: { Pattern }
Pattern0 : Pattern1 Colon Pattern0 { Language.AbsMPL.LIST_COLON_PATTERN $1 $2 $3 }
         | Pattern1 { $1 }
Pattern1 :: { Pattern }
Pattern1 : UIdent LBracket ListPattern RBracket { Language.AbsMPL.CONSTRUCTOR_PATTERN_ARGS $1 $2 $3 $4 }
         | UIdent { Language.AbsMPL.CONSTRUCTOR_PATTERN_NO_ARGS $1 }
         | LBracket RBracket { Language.AbsMPL.UNIT_PATTERN $1 $2 }
         | LBracket DestructorPatternPhrase ',' ListDestructorPatternPhrase RBracket { Language.AbsMPL.RECORD_PATTERN $1 $2 $4 $5 }
         | LSquareBracket ListPattern RSquareBracket { Language.AbsMPL.LIST_PATTERN $1 $2 $3 }
         | LBracket Pattern ',' ListTupleListPattern RBracket { Language.AbsMPL.TUPLE_PATTERN $1 $2 $4 $5 }
         | PIdent { Language.AbsMPL.VAR_PATTERN $1 }
         | String { Language.AbsMPL.STR_PATTERN $1 }
         | PInteger { Language.AbsMPL.INT_PATTERN $1 }
         | NullPattern { Language.AbsMPL.NULL_PATTERN $1 }
         | LBracket Pattern RBracket { Language.AbsMPL.BRACKETED_PATTERN $1 $2 $3 }
TupleListPattern :: { TupleListPattern }
TupleListPattern : Pattern { Language.AbsMPL.TUPLE_LIST_PATTERN $1 }
ListTupleListPattern :: { [TupleListPattern] }
ListTupleListPattern : TupleListPattern { (:[]) $1 }
                     | TupleListPattern ',' ListTupleListPattern { (:) $1 $3 }
DestructorPatternPhrase :: { DestructorPatternPhrase }
DestructorPatternPhrase : UIdent ':=' Pattern { Language.AbsMPL.DESTRUCTOR_PATTERN_PHRASE $1 $3 }
ListDestructorPatternPhrase :: { [DestructorPatternPhrase] }
ListDestructorPatternPhrase : DestructorPatternPhrase { (:[]) $1 }
                            | DestructorPatternPhrase ',' ListDestructorPatternPhrase { (:) $1 $3 }
FunctionDefn :: { FunctionDefn }
FunctionDefn : 'fun' PIdent '::' ListMplType '->' MplType '=' '{' ListPattExprPhrase '}' { Language.AbsMPL.TYPED_FUNCTION_DEFN $2 $4 $6 $9 }
             | 'fun' PIdent '=' '{' ListPattExprPhrase '}' { Language.AbsMPL.FUNCTION_DEFN $2 $5 }
ListPattExprPhrase :: { [PattExprPhrase] }
ListPattExprPhrase : PattExprPhrase { (:[]) $1 }
                   | PattExprPhrase ';' ListPattExprPhrase { (:) $1 $3 }
ProcessDefn :: { ProcessDefn }
ProcessDefn : 'proc' PIdent '::' ListMplType '|' ListMplType '=>' ListMplType '=' '{' ListProcessPhrase '}' { Language.AbsMPL.TYPED_PROCESS_DEFN $2 $4 $6 $8 $11 }
            | 'proc' PIdent '=' '{' ListProcessPhrase '}' { Language.AbsMPL.PROCESS_DEFN $2 $5 }
ProcessPhrase :: { ProcessPhrase }
ProcessPhrase : ListPattern '|' ListPIdent '=>' ListPIdent '->' ProcessCommandsBlock { Language.AbsMPL.PROCESS_PHRASE $1 $3 $5 $7 }
ListProcessPhrase :: { [ProcessPhrase] }
ListProcessPhrase : ProcessPhrase { (:[]) $1 }
                  | ProcessPhrase ';' ListProcessPhrase { (:) $1 $3 }
ProcessCommandsBlock :: { ProcessCommandsBlock }
ProcessCommandsBlock : 'do' '{' ListProcessCommand '}' { Language.AbsMPL.PROCESS_COMMANDS_DO_BLOCK $3 }
                     | ProcessCommand { Language.AbsMPL.PROCESS_COMMANDS_SINGLE_COMMAND_BLOCK $1 }
ListProcessCommand :: { [ProcessCommand] }
ListProcessCommand : {- empty -} { [] }
                   | ProcessCommand { (:[]) $1 }
                   | ProcessCommand ';' ListProcessCommand { (:) $1 $3 }
ProcessCommand :: { ProcessCommand }
ProcessCommand : PIdent LBracket ListExpr '|' ListPIdent '=>' ListPIdent RBracket { Language.AbsMPL.PROCESS_RUN $1 $2 $3 $5 $7 $8 }
               | 'close' PIdent { Language.AbsMPL.PROCESS_CLOSE $2 }
               | 'halt' PIdent { Language.AbsMPL.PROCESS_HALT $2 }
               | 'get' Pattern 'on' PIdent { Language.AbsMPL.PROCESS_GET $2 $4 }
               | 'put' Expr 'on' PIdent { Language.AbsMPL.PROCESS_PUT $2 $4 }
               | 'hcase' PIdent 'of' '{' ListHCasePhrase '}' { Language.AbsMPL.PROCESS_HCASE $2 $5 }
               | 'hput' UIdent 'on' PIdent { Language.AbsMPL.PROCESS_HPUT $2 $4 }
               | 'split' PIdent 'into' ListSplitChannel { Language.AbsMPL.PROCESS_SPLIT $2 $4 }
               | 'fork' PIdent 'as' '{' ListForkPhrase '}' { Language.AbsMPL.PROCESS_FORK $2 $5 }
               | PIdent '|=|' PIdent { Language.AbsMPL.PROCESS_ID $1 $3 }
               | PIdent '|=|' 'neg' PIdent { Language.AbsMPL.PROCESS_NEG $1 $4 }
               | 'race' '{' ListRacePhrase '}' { Language.AbsMPL.PROCESS_RACE $3 }
               | 'plug' '{' ListPlugPhrase '}' { Language.AbsMPL.PROCESS_PLUG $3 }
               | 'case' Expr 'of' '{' ListProcessCasePhrase '}' { Language.AbsMPL.PROCESS_CASE $2 $5 }
               | 'switch' '{' ListProcessSwitchPhrase '}' { Language.AbsMPL.PROCESS_SWITCH $3 }
HCasePhrase :: { HCasePhrase }
HCasePhrase : UIdent '->' ProcessCommandsBlock { Language.AbsMPL.HCASE_PHRASE $1 $3 }
ListHCasePhrase :: { [HCasePhrase] }
ListHCasePhrase : {- empty -} { [] }
                | HCasePhrase { (:[]) $1 }
                | HCasePhrase ';' ListHCasePhrase { (:) $1 $3 }
SplitChannel :: { SplitChannel }
SplitChannel : PIdent { Language.AbsMPL.SPLIT_CHANNEL $1 }
ListSplitChannel :: { [SplitChannel] }
ListSplitChannel : SplitChannel { (:[]) $1 }
                 | SplitChannel ',' ListSplitChannel { (:) $1 $3 }
ForkPhrase :: { ForkPhrase }
ForkPhrase : PIdent '->' ProcessCommandsBlock { Language.AbsMPL.FORK_PHRASE $1 $3 }
           | PIdent 'with' ListForkChannel '->' ProcessCommandsBlock { Language.AbsMPL.FORK_WITH_PHRASE $1 $3 $5 }
ListForkPhrase :: { [ForkPhrase] }
ListForkPhrase : ForkPhrase { (:[]) $1 }
               | ForkPhrase ';' ListForkPhrase { (:) $1 $3 }
ForkChannel :: { ForkChannel }
ForkChannel : PIdent { Language.AbsMPL.FORK_CHANNEL $1 }
ListForkChannel :: { [ForkChannel] }
ListForkChannel : ForkChannel { (:[]) $1 }
                | ForkChannel ';' ListForkChannel { (:) $1 $3 }
RacePhrase :: { RacePhrase }
RacePhrase : PIdent '->' ProcessCommandsBlock { Language.AbsMPL.RACE_PHRASE $1 $3 }
ListRacePhrase :: { [RacePhrase] }
ListRacePhrase : {- empty -} { [] }
               | RacePhrase { (:[]) $1 }
               | RacePhrase ';' ListRacePhrase { (:) $1 $3 }
PlugPhrase :: { PlugPhrase }
PlugPhrase : ProcessCommandsBlock { Language.AbsMPL.PLUG_PHRASE $1 }
ListPlugPhrase :: { [PlugPhrase] }
ListPlugPhrase : {- empty -} { [] }
               | PlugPhrase { (:[]) $1 }
               | PlugPhrase ';' ListPlugPhrase { (:) $1 $3 }
ProcessCasePhrase :: { ProcessCasePhrase }
ProcessCasePhrase : Pattern '->' ProcessCommandsBlock { Language.AbsMPL.PROCESS_CASE_PHRASE $1 $3 }
ListProcessCasePhrase :: { [ProcessCasePhrase] }
ListProcessCasePhrase : {- empty -} { [] }
                      | ProcessCasePhrase { (:[]) $1 }
                      | ProcessCasePhrase ';' ListProcessCasePhrase { (:) $1 $3 }
ProcessSwitchPhrase :: { ProcessSwitchPhrase }
ProcessSwitchPhrase : Expr '->' ProcessCommandsBlock { Language.AbsMPL.PROCESS_SWITCH_PHRASE $1 $3 }
ListProcessSwitchPhrase :: { [ProcessSwitchPhrase] }
ListProcessSwitchPhrase : ProcessSwitchPhrase { (:[]) $1 }
                        | ProcessSwitchPhrase ';' ListProcessSwitchPhrase { (:) $1 $3 }
{

returnM :: a -> Err a
returnM = return

thenM :: Err a -> (a -> Err b) -> Err b
thenM = (>>=)

happyError :: [Token] -> Err a
happyError ts =
  Bad $ "syntax error at " ++ tokenPos ts ++
  case ts of
    []      -> []
    [Err _] -> " due to lexer error"
    t:_     -> " before `" ++ id(prToken t) ++ "'"

myLexer = tokens
}

