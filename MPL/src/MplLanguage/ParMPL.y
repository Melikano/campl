-- This Happy file was machine-generated by the BNF converter
{
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns #-}
module MplLanguage.ParMPL
  ( happyError
  , myLexer
  , pMplProg
  ) where
import qualified MplLanguage.AbsMPL
import MplLanguage.LexMPL
}

%name pMplProg MplProg
-- no lexer declaration
%monad { Either String } { (>>=) } { return }
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
  'codata' { PT _ (TS _ 10) }
  'coprotocol' { PT _ (TS _ 11) }
  'data' { PT _ (TS _ 12) }
  'defn' { PT _ (TS _ 13) }
  'do' { PT _ (TS _ 14) }
  'else' { PT _ (TS _ 15) }
  'fold' { PT _ (TS _ 16) }
  'fun' { PT _ (TS _ 17) }
  'if' { PT _ (TS _ 18) }
  'in' { PT _ (TS _ 19) }
  'into' { PT _ (TS _ 20) }
  'let' { PT _ (TS _ 21) }
  'neg' { PT _ (TS _ 22) }
  'of' { PT _ (TS _ 23) }
  'on' { PT _ (TS _ 24) }
  'plug' { PT _ (TS _ 25) }
  'potato' { PT _ (TS _ 26) }
  'proc' { PT _ (TS _ 27) }
  'protocol' { PT _ (TS _ 28) }
  'race' { PT _ (TS _ 29) }
  'switch' { PT _ (TS _ 30) }
  'then' { PT _ (TS _ 31) }
  'unfold' { PT _ (TS _ 32) }
  'where' { PT _ (TS _ 33) }
  'with' { PT _ (TS _ 34) }
  '{' { PT _ (TS _ 35) }
  '|' { PT _ (TS _ 36) }
  '}' { PT _ (TS _ 37) }
  L_PInteger { PT _ (T_PInteger _) }
  L_PDouble { PT _ (T_PDouble _) }
  L_PChar { PT _ (T_PChar _) }
  L_PString { PT _ (T_PString _) }
  L_Par { PT _ (T_Par _) }
  L_Tensor { PT _ (T_Tensor _) }
  L_LBracket { PT _ (T_LBracket _) }
  L_RBracket { PT _ (T_RBracket _) }
  L_LSquareBracket { PT _ (T_LSquareBracket _) }
  L_RSquareBracket { PT _ (T_RSquareBracket _) }
  L_NullPattern { PT _ (T_NullPattern _) }
  L_Colon { PT _ (T_Colon _) }
  L_Infixl1op { PT _ (T_Infixl1op _) }
  L_Infixl2op { PT _ (T_Infixl2op _) }
  L_Infixl3op { PT _ (T_Infixl3op _) }
  L_Infixl4op { PT _ (T_Infixl4op _) }
  L_Infixl5op { PT _ (T_Infixl5op _) }
  L_Infixl6op { PT _ (T_Infixl6op _) }
  L_Infixr7op { PT _ (T_Infixr7op _) }
  L_Infixl8op { PT _ (T_Infixl8op _) }
  L_Close { PT _ (T_Close _) }
  L_Halt { PT _ (T_Halt _) }
  L_Get { PT _ (T_Get _) }
  L_Put { PT _ (T_Put _) }
  L_HCase { PT _ (T_HCase _) }
  L_HPut { PT _ (T_HPut _) }
  L_Split { PT _ (T_Split _) }
  L_Fork { PT _ (T_Fork _) }
  L_ChId { PT _ (T_ChId _) }
  L_Case { PT _ (T_Case _) }
  L_UIdent { PT _ (T_UIdent _) }
  L_PIdent { PT _ (T_PIdent _) }
  L_UPIdent { PT _ (T_UPIdent _) }

%%

PInteger :: { MplLanguage.AbsMPL.PInteger}
PInteger  : L_PInteger { MplLanguage.AbsMPL.PInteger (mkPosToken $1) }

PDouble :: { MplLanguage.AbsMPL.PDouble}
PDouble  : L_PDouble { MplLanguage.AbsMPL.PDouble (mkPosToken $1) }

PChar :: { MplLanguage.AbsMPL.PChar}
PChar  : L_PChar { MplLanguage.AbsMPL.PChar (mkPosToken $1) }

PString :: { MplLanguage.AbsMPL.PString}
PString  : L_PString { MplLanguage.AbsMPL.PString (mkPosToken $1) }

Par :: { MplLanguage.AbsMPL.Par}
Par  : L_Par { MplLanguage.AbsMPL.Par (mkPosToken $1) }

Tensor :: { MplLanguage.AbsMPL.Tensor}
Tensor  : L_Tensor { MplLanguage.AbsMPL.Tensor (mkPosToken $1) }

LBracket :: { MplLanguage.AbsMPL.LBracket}
LBracket  : L_LBracket { MplLanguage.AbsMPL.LBracket (mkPosToken $1) }

RBracket :: { MplLanguage.AbsMPL.RBracket}
RBracket  : L_RBracket { MplLanguage.AbsMPL.RBracket (mkPosToken $1) }

LSquareBracket :: { MplLanguage.AbsMPL.LSquareBracket}
LSquareBracket  : L_LSquareBracket { MplLanguage.AbsMPL.LSquareBracket (mkPosToken $1) }

RSquareBracket :: { MplLanguage.AbsMPL.RSquareBracket}
RSquareBracket  : L_RSquareBracket { MplLanguage.AbsMPL.RSquareBracket (mkPosToken $1) }

NullPattern :: { MplLanguage.AbsMPL.NullPattern}
NullPattern  : L_NullPattern { MplLanguage.AbsMPL.NullPattern (mkPosToken $1) }

Colon :: { MplLanguage.AbsMPL.Colon}
Colon  : L_Colon { MplLanguage.AbsMPL.Colon (mkPosToken $1) }

Infixl1op :: { MplLanguage.AbsMPL.Infixl1op}
Infixl1op  : L_Infixl1op { MplLanguage.AbsMPL.Infixl1op (mkPosToken $1) }

Infixl2op :: { MplLanguage.AbsMPL.Infixl2op}
Infixl2op  : L_Infixl2op { MplLanguage.AbsMPL.Infixl2op (mkPosToken $1) }

Infixl3op :: { MplLanguage.AbsMPL.Infixl3op}
Infixl3op  : L_Infixl3op { MplLanguage.AbsMPL.Infixl3op (mkPosToken $1) }

Infixl4op :: { MplLanguage.AbsMPL.Infixl4op}
Infixl4op  : L_Infixl4op { MplLanguage.AbsMPL.Infixl4op (mkPosToken $1) }

Infixl5op :: { MplLanguage.AbsMPL.Infixl5op}
Infixl5op  : L_Infixl5op { MplLanguage.AbsMPL.Infixl5op (mkPosToken $1) }

Infixl6op :: { MplLanguage.AbsMPL.Infixl6op}
Infixl6op  : L_Infixl6op { MplLanguage.AbsMPL.Infixl6op (mkPosToken $1) }

Infixr7op :: { MplLanguage.AbsMPL.Infixr7op}
Infixr7op  : L_Infixr7op { MplLanguage.AbsMPL.Infixr7op (mkPosToken $1) }

Infixl8op :: { MplLanguage.AbsMPL.Infixl8op}
Infixl8op  : L_Infixl8op { MplLanguage.AbsMPL.Infixl8op (mkPosToken $1) }

Close :: { MplLanguage.AbsMPL.Close}
Close  : L_Close { MplLanguage.AbsMPL.Close (mkPosToken $1) }

Halt :: { MplLanguage.AbsMPL.Halt}
Halt  : L_Halt { MplLanguage.AbsMPL.Halt (mkPosToken $1) }

Get :: { MplLanguage.AbsMPL.Get}
Get  : L_Get { MplLanguage.AbsMPL.Get (mkPosToken $1) }

Put :: { MplLanguage.AbsMPL.Put}
Put  : L_Put { MplLanguage.AbsMPL.Put (mkPosToken $1) }

HCase :: { MplLanguage.AbsMPL.HCase}
HCase  : L_HCase { MplLanguage.AbsMPL.HCase (mkPosToken $1) }

HPut :: { MplLanguage.AbsMPL.HPut}
HPut  : L_HPut { MplLanguage.AbsMPL.HPut (mkPosToken $1) }

Split :: { MplLanguage.AbsMPL.Split}
Split  : L_Split { MplLanguage.AbsMPL.Split (mkPosToken $1) }

Fork :: { MplLanguage.AbsMPL.Fork}
Fork  : L_Fork { MplLanguage.AbsMPL.Fork (mkPosToken $1) }

ChId :: { MplLanguage.AbsMPL.ChId}
ChId  : L_ChId { MplLanguage.AbsMPL.ChId (mkPosToken $1) }

Case :: { MplLanguage.AbsMPL.Case}
Case  : L_Case { MplLanguage.AbsMPL.Case (mkPosToken $1) }

UIdent :: { MplLanguage.AbsMPL.UIdent}
UIdent  : L_UIdent { MplLanguage.AbsMPL.UIdent (mkPosToken $1) }

PIdent :: { MplLanguage.AbsMPL.PIdent}
PIdent  : L_PIdent { MplLanguage.AbsMPL.PIdent (mkPosToken $1) }

UPIdent :: { MplLanguage.AbsMPL.UPIdent}
UPIdent  : L_UPIdent { MplLanguage.AbsMPL.UPIdent (mkPosToken $1) }

ListPIdent :: { [MplLanguage.AbsMPL.PIdent] }
ListPIdent : {- empty -} { [] }
           | PIdent { (:[]) $1 }
           | PIdent ',' ListPIdent { (:) $1 $3 }

MplProg :: { MplLanguage.AbsMPL.MplProg }
MplProg : ListMplStmt { MplLanguage.AbsMPL.MPL_PROG $1 }

MplStmt :: { MplLanguage.AbsMPL.MplStmt }
MplStmt : 'defn' '{' ListMplDefn '}' 'where' '{' ListMplWhere '}' { MplLanguage.AbsMPL.MPL_DEFN_STMS_WHERE $3 $7 }
        | 'defn' '{' ListMplDefn '}' { MplLanguage.AbsMPL.MPL_DEFN_STMS $3 }
        | MplDefn { MplLanguage.AbsMPL.MPL_STMT $1 }

ListMplDefn :: { [MplLanguage.AbsMPL.MplDefn] }
ListMplDefn : MplDefn { (:[]) $1 }
            | MplDefn ';' ListMplDefn { (:) $1 $3 }

ListMplStmt :: { [MplLanguage.AbsMPL.MplStmt] }
ListMplStmt : {- empty -} { [] }
            | MplStmt ListMplStmt { (:) $1 $2 }

MplWhere :: { MplLanguage.AbsMPL.MplWhere }
MplWhere : MplStmt { MplLanguage.AbsMPL.MPL_WHERE $1 }

ListMplWhere :: { [MplLanguage.AbsMPL.MplWhere] }
ListMplWhere : {- empty -} { [] }
             | MplWhere { (:[]) $1 }
             | MplWhere ';' ListMplWhere { (:) $1 $3 }

MplDefn :: { MplLanguage.AbsMPL.MplDefn }
MplDefn : SequentialTypeDefn { MplLanguage.AbsMPL.MPL_SEQUENTIAL_TYPE_DEFN $1 }
        | ConcurrentTypeDefn { MplLanguage.AbsMPL.MPL_CONCURRENT_TYPE_DEFN $1 }
        | FunctionDefn { MplLanguage.AbsMPL.MPL_FUNCTION_DEFN $1 }
        | ProcessDefn { MplLanguage.AbsMPL.MPL_PROCESS_DEFN $1 }
        | 'potato' { MplLanguage.AbsMPL.MPL_DEFNTEST }

MplType :: { MplLanguage.AbsMPL.MplType }
MplType : MplType0 { MplLanguage.AbsMPL.MPL_TYPE $1 }

MplType0 :: { MplLanguage.AbsMPL.MplType }
MplType0 : MplType1 Par MplType1 { MplLanguage.AbsMPL.PAR_TYPE $1 $2 $3 }
         | MplType1 { $1 }

MplType1 :: { MplLanguage.AbsMPL.MplType }
MplType1 : MplType2 Tensor MplType2 { MplLanguage.AbsMPL.TENSOR_TYPE $1 $2 $3 }
         | MplType2 { $1 }

MplType2 :: { MplLanguage.AbsMPL.MplType }
MplType2 : UIdent LBracket ListMplType RBracket { MplLanguage.AbsMPL.MPL_UIDENT_ARGS_TYPE $1 $2 $3 $4 }
         | UIdent LBracket ListMplType '|' ListMplType RBracket { MplLanguage.AbsMPL.MPL_UIDENT_SEQ_CONC_ARGS_TYPE $1 $2 $3 $5 $6 }
         | UIdent { MplLanguage.AbsMPL.MPL_UIDENT_NO_ARGS_TYPE $1 }
         | LBracket RBracket { MplLanguage.AbsMPL.MPL_UNIT_TYPE $1 $2 }
         | LBracket MplType RBracket { MplLanguage.AbsMPL.MPL_BRACKETED_TYPE $1 $2 $3 }
         | LSquareBracket MplType RSquareBracket { MplLanguage.AbsMPL.MPL_LIST_TYPE $1 $2 $3 }
         | LBracket MplType ',' ListTupleListType RBracket { MplLanguage.AbsMPL.MPL_TUPLE_TYPE $1 $2 $4 $5 }

TupleListType :: { MplLanguage.AbsMPL.TupleListType }
TupleListType : MplType { MplLanguage.AbsMPL.TUPLE_LIST_TYPE $1 }

ForallVarList :: { MplLanguage.AbsMPL.ForallVarList }
ForallVarList : UIdent { MplLanguage.AbsMPL.MPL_SEQ_FUN_TYPE_FORALL_LIST $1 }

ListForallVarList :: { [MplLanguage.AbsMPL.ForallVarList] }
ListForallVarList : {- empty -} { [] }
                  | ForallVarList ListForallVarList { (:) $1 $2 }

ListTupleListType :: { [MplLanguage.AbsMPL.TupleListType] }
ListTupleListType : TupleListType { (:[]) $1 }
                  | TupleListType ',' ListTupleListType { (:) $1 $3 }

ListMplType :: { [MplLanguage.AbsMPL.MplType] }
ListMplType : {- empty -} { [] }
            | MplType { (:[]) $1 }
            | MplType ',' ListMplType { (:) $1 $3 }

SequentialTypeDefn :: { MplLanguage.AbsMPL.SequentialTypeDefn }
SequentialTypeDefn : 'data' ListSeqTypeClauseDefn { MplLanguage.AbsMPL.DATA_DEFN $2 }
                   | 'codata' ListSeqTypeClauseDefn { MplLanguage.AbsMPL.CODATA_DEFN $2 }

SeqTypeClauseDefn :: { MplLanguage.AbsMPL.SeqTypeClauseDefn }
SeqTypeClauseDefn : MplType '->' MplType '=' '{' ListSeqTypePhraseDefn '}' { MplLanguage.AbsMPL.SEQ_TYPE_CLAUSE $1 $3 $6 }

SeqTypePhraseDefn :: { MplLanguage.AbsMPL.SeqTypePhraseDefn }
SeqTypePhraseDefn : ListTypeHandleName '::' ListMplType '->' MplType { MplLanguage.AbsMPL.SEQ_TYPE_PHRASE $1 $3 $5 }

ListSeqTypeClauseDefn :: { [MplLanguage.AbsMPL.SeqTypeClauseDefn] }
ListSeqTypeClauseDefn : SeqTypeClauseDefn { (:[]) $1 }
                      | SeqTypeClauseDefn 'and' ListSeqTypeClauseDefn { (:) $1 $3 }

ListSeqTypePhraseDefn :: { [MplLanguage.AbsMPL.SeqTypePhraseDefn] }
ListSeqTypePhraseDefn : {- empty -} { [] }
                      | SeqTypePhraseDefn { (:[]) $1 }
                      | SeqTypePhraseDefn ';' ListSeqTypePhraseDefn { (:) $1 $3 }

ConcurrentTypeDefn :: { MplLanguage.AbsMPL.ConcurrentTypeDefn }
ConcurrentTypeDefn : 'protocol' ListConcurrentTypeClauseDefn { MplLanguage.AbsMPL.PROTOCOL_DEFN $2 }
                   | 'coprotocol' ListConcurrentTypeClauseDefn { MplLanguage.AbsMPL.COPROTOCOL_DEFN $2 }

ConcurrentTypeClauseDefn :: { MplLanguage.AbsMPL.ConcurrentTypeClauseDefn }
ConcurrentTypeClauseDefn : MplType '=>' MplType '=' '{' ListConcurrentTypePhraseDefn '}' { MplLanguage.AbsMPL.CONCURRENT_TYPE_CLAUSE $1 $3 $6 }

ConcurrentTypePhraseDefn :: { MplLanguage.AbsMPL.ConcurrentTypePhraseDefn }
ConcurrentTypePhraseDefn : ListTypeHandleName '::' MplType '=>' MplType { MplLanguage.AbsMPL.CONCURRENT_TYPE_PHRASE $1 $3 $5 }

ListConcurrentTypeClauseDefn :: { [MplLanguage.AbsMPL.ConcurrentTypeClauseDefn] }
ListConcurrentTypeClauseDefn : ConcurrentTypeClauseDefn { (:[]) $1 }
                             | ConcurrentTypeClauseDefn 'and' ListConcurrentTypeClauseDefn { (:) $1 $3 }

ListConcurrentTypePhraseDefn :: { [MplLanguage.AbsMPL.ConcurrentTypePhraseDefn] }
ListConcurrentTypePhraseDefn : {- empty -} { [] }
                             | ConcurrentTypePhraseDefn { (:[]) $1 }
                             | ConcurrentTypePhraseDefn ';' ListConcurrentTypePhraseDefn { (:) $1 $3 }

TypeHandleName :: { MplLanguage.AbsMPL.TypeHandleName }
TypeHandleName : UIdent { MplLanguage.AbsMPL.TYPE_HANDLE_NAME $1 }

ListTypeHandleName :: { [MplLanguage.AbsMPL.TypeHandleName] }
ListTypeHandleName : TypeHandleName { (:[]) $1 }
                   | TypeHandleName ',' ListTypeHandleName { (:) $1 $3 }

Expr :: { MplLanguage.AbsMPL.Expr }
Expr : Expr0 { MplLanguage.AbsMPL.EXPR $1 }
     | 'if' Expr 'then' Expr 'else' Expr { MplLanguage.AbsMPL.IF_EXPR $2 $4 $6 }
     | 'let' '{' ListLetExprPhrase '}' 'in' Expr { MplLanguage.AbsMPL.LET_EXPR $3 $6 }

Expr0 :: { MplLanguage.AbsMPL.Expr }
Expr0 : Expr1 Colon Expr0 { MplLanguage.AbsMPL.INFIXR0_EXPR $1 $2 $3 }
      | Expr1 { $1 }

Expr1 :: { MplLanguage.AbsMPL.Expr }
Expr1 : Expr1 Infixl1op Expr2 { MplLanguage.AbsMPL.INFIXL1_EXPR $1 $2 $3 }
      | Expr2 { $1 }

Expr2 :: { MplLanguage.AbsMPL.Expr }
Expr2 : Expr2 Infixl2op Expr3 { MplLanguage.AbsMPL.INFIXL2_EXPR $1 $2 $3 }
      | Expr3 { $1 }

Expr3 :: { MplLanguage.AbsMPL.Expr }
Expr3 : Expr3 Infixl3op Expr4 { MplLanguage.AbsMPL.INFIXL3_EXPR $1 $2 $3 }
      | Expr4 { $1 }

Expr4 :: { MplLanguage.AbsMPL.Expr }
Expr4 : Expr4 Infixl4op Expr5 { MplLanguage.AbsMPL.INFIXL4_EXPR $1 $2 $3 }
      | Expr5 { $1 }

Expr5 :: { MplLanguage.AbsMPL.Expr }
Expr5 : Expr5 Infixl5op Expr6 { MplLanguage.AbsMPL.INFIXL5_EXPR $1 $2 $3 }
      | Expr6 { $1 }

Expr6 :: { MplLanguage.AbsMPL.Expr }
Expr6 : Expr6 Infixl6op Expr7 { MplLanguage.AbsMPL.INFIXL6_EXPR $1 $2 $3 }
      | Expr7 { $1 }

Expr7 :: { MplLanguage.AbsMPL.Expr }
Expr7 : Expr8 Infixr7op Expr7 { MplLanguage.AbsMPL.INFIXR7_EXPR $1 $2 $3 }
      | Expr8 { $1 }

Expr8 :: { MplLanguage.AbsMPL.Expr }
Expr8 : Expr8 Infixl8op Expr10 { MplLanguage.AbsMPL.INFIXL8_EXPR $1 $2 $3 }
      | Expr10 { $1 }

Expr10 :: { MplLanguage.AbsMPL.Expr }
Expr10 : LSquareBracket ListExpr RSquareBracket { MplLanguage.AbsMPL.LIST_EXPR $1 $2 $3 }
       | PIdent { MplLanguage.AbsMPL.VAR_EXPR $1 }
       | PInteger { MplLanguage.AbsMPL.INT_EXPR $1 }
       | PString { MplLanguage.AbsMPL.STRING_EXPR $1 }
       | PChar { MplLanguage.AbsMPL.CHAR_EXPR $1 }
       | PDouble { MplLanguage.AbsMPL.DOUBLE_EXPR $1 }
       | LBracket RBracket { MplLanguage.AbsMPL.UNIT_EXPR $1 $2 }
       | 'fold' Expr 'of' '{' ListFoldExprPhrase '}' { MplLanguage.AbsMPL.FOLD_EXPR $2 $5 }
       | 'unfold' Expr 'of' '{' ListUnfoldExprPhrase '}' { MplLanguage.AbsMPL.UNFOLD_EXPR $2 $5 }
       | Case Expr 'of' '{' ListPattExprPhrase '}' { MplLanguage.AbsMPL.CASE_EXPR $1 $2 $5 }
       | 'switch' '{' ListSwitchExprPhrase '}' { MplLanguage.AbsMPL.SWITCH_EXP $3 }
       | UIdent LBracket ListExpr RBracket { MplLanguage.AbsMPL.DESTRUCTOR_CONSTRUCTOR_ARGS_EXPR $1 $2 $3 $4 }
       | UIdent { MplLanguage.AbsMPL.DESTRUCTOR_CONSTRUCTOR_NO_ARGS_EXPR $1 }
       | LBracket Expr ',' ListTupleExprList RBracket { MplLanguage.AbsMPL.TUPLE_EXPR $1 $2 $4 $5 }
       | PIdent LBracket ListExpr RBracket { MplLanguage.AbsMPL.FUN_EXPR $1 $2 $3 $4 }
       | LBracket ListRecordExprPhrase RBracket { MplLanguage.AbsMPL.RECORD_EXPR $1 $2 $3 }
       | LBracket Expr RBracket { MplLanguage.AbsMPL.BRACKETED_EXPR $1 $2 $3 }

UnfoldExprPhrase :: { MplLanguage.AbsMPL.UnfoldExprPhrase }
UnfoldExprPhrase : Pattern 'of' '{' ListFoldExprPhrase '}' { MplLanguage.AbsMPL.UNFOLD_EXPR_PHRASE $1 $4 }

ListUnfoldExprPhrase :: { [MplLanguage.AbsMPL.UnfoldExprPhrase] }
ListUnfoldExprPhrase : UnfoldExprPhrase { (:[]) $1 }
                     | UnfoldExprPhrase ';' ListUnfoldExprPhrase { (:) $1 $3 }

FoldExprPhrase :: { MplLanguage.AbsMPL.FoldExprPhrase }
FoldExprPhrase : UIdent Colon ListPattern '->' Expr { MplLanguage.AbsMPL.FOLD_EXPR_PHRASE $1 $2 $3 $5 }

ListFoldExprPhrase :: { [MplLanguage.AbsMPL.FoldExprPhrase] }
ListFoldExprPhrase : FoldExprPhrase { (:[]) $1 }
                   | FoldExprPhrase ';' ListFoldExprPhrase { (:) $1 $3 }

LetExprPhrase :: { MplLanguage.AbsMPL.LetExprPhrase }
LetExprPhrase : MplStmt { MplLanguage.AbsMPL.LET_EXPR_PHRASE $1 }

ListLetExprPhrase :: { [MplLanguage.AbsMPL.LetExprPhrase] }
ListLetExprPhrase : LetExprPhrase { (:[]) $1 }
                  | LetExprPhrase ';' ListLetExprPhrase { (:) $1 $3 }

TupleExprList :: { MplLanguage.AbsMPL.TupleExprList }
TupleExprList : Expr { MplLanguage.AbsMPL.TUPLE_EXPR_LIST $1 }

ListTupleExprList :: { [MplLanguage.AbsMPL.TupleExprList] }
ListTupleExprList : TupleExprList { (:[]) $1 }
                  | TupleExprList ',' ListTupleExprList { (:) $1 $3 }

RecordExprPhrase :: { MplLanguage.AbsMPL.RecordExprPhrase }
RecordExprPhrase : UIdent ':=' PattExprPhrase { MplLanguage.AbsMPL.RECORD_EXPR_HIGHER_ORDER_PHRASE $1 $3 }

ListRecordExprPhrase :: { [MplLanguage.AbsMPL.RecordExprPhrase] }
ListRecordExprPhrase : RecordExprPhrase { (:[]) $1 }
                     | RecordExprPhrase ',' ListRecordExprPhrase { (:) $1 $3 }

SwitchExprPhrase :: { MplLanguage.AbsMPL.SwitchExprPhrase }
SwitchExprPhrase : Expr '->' Expr { MplLanguage.AbsMPL.SWITCH_EXPR_PHRASE $1 $3 }

ListSwitchExprPhrase :: { [MplLanguage.AbsMPL.SwitchExprPhrase] }
ListSwitchExprPhrase : SwitchExprPhrase { (:[]) $1 }
                     | SwitchExprPhrase ';' ListSwitchExprPhrase { (:) $1 $3 }

ListExpr :: { [MplLanguage.AbsMPL.Expr] }
ListExpr : {- empty -} { [] }
         | Expr { (:[]) $1 }
         | Expr ',' ListExpr { (:) $1 $3 }

PattExprPhrase :: { MplLanguage.AbsMPL.PattExprPhrase }
PattExprPhrase : ListPattern '->' Expr { MplLanguage.AbsMPL.PATTERN_TO_EXPR $1 $3 }

Pattern :: { MplLanguage.AbsMPL.Pattern }
Pattern : Pattern0 { MplLanguage.AbsMPL.PATTERN $1 }

ListPattern :: { [MplLanguage.AbsMPL.Pattern] }
ListPattern : {- empty -} { [] }
            | Pattern { (:[]) $1 }
            | Pattern ',' ListPattern { (:) $1 $3 }

Pattern0 :: { MplLanguage.AbsMPL.Pattern }
Pattern0 : Pattern1 Colon Pattern0 { MplLanguage.AbsMPL.LIST_COLON_PATTERN $1 $2 $3 }
         | Pattern1 { $1 }

Pattern1 :: { MplLanguage.AbsMPL.Pattern }
Pattern1 : UIdent LBracket ListPattern RBracket { MplLanguage.AbsMPL.CONSTRUCTOR_PATTERN_ARGS $1 $2 $3 $4 }
         | UIdent { MplLanguage.AbsMPL.CONSTRUCTOR_PATTERN_NO_ARGS $1 }
         | LBracket RBracket { MplLanguage.AbsMPL.UNIT_PATTERN $1 $2 }
         | LBracket ListDestructorPatternPhrase RBracket { MplLanguage.AbsMPL.RECORD_PATTERN $1 $2 $3 }
         | LSquareBracket ListPattern RSquareBracket { MplLanguage.AbsMPL.LIST_PATTERN $1 $2 $3 }
         | LBracket Pattern ',' ListTupleListPattern RBracket { MplLanguage.AbsMPL.TUPLE_PATTERN $1 $2 $4 $5 }
         | PIdent { MplLanguage.AbsMPL.VAR_PATTERN $1 }
         | PString { MplLanguage.AbsMPL.STR_PATTERN $1 }
         | PChar { MplLanguage.AbsMPL.CHAR_PATTERN $1 }
         | PInteger { MplLanguage.AbsMPL.INT_PATTERN $1 }
         | NullPattern { MplLanguage.AbsMPL.NULL_PATTERN $1 }
         | LBracket Pattern RBracket { MplLanguage.AbsMPL.BRACKETED_PATTERN $1 $2 $3 }

TupleListPattern :: { MplLanguage.AbsMPL.TupleListPattern }
TupleListPattern : Pattern { MplLanguage.AbsMPL.TUPLE_LIST_PATTERN $1 }

ListTupleListPattern :: { [MplLanguage.AbsMPL.TupleListPattern] }
ListTupleListPattern : TupleListPattern { (:[]) $1 }
                     | TupleListPattern ',' ListTupleListPattern { (:) $1 $3 }

DestructorPatternPhrase :: { MplLanguage.AbsMPL.DestructorPatternPhrase }
DestructorPatternPhrase : UIdent ':=' Pattern { MplLanguage.AbsMPL.DESTRUCTOR_PATTERN_PHRASE $1 $3 }

ListDestructorPatternPhrase :: { [MplLanguage.AbsMPL.DestructorPatternPhrase] }
ListDestructorPatternPhrase : DestructorPatternPhrase { (:[]) $1 }
                            | DestructorPatternPhrase ',' ListDestructorPatternPhrase { (:) $1 $3 }

FunctionDefn :: { MplLanguage.AbsMPL.FunctionDefn }
FunctionDefn : 'fun' PIdent '::' ListMplType '->' MplType '=' '{' ListPattExprPhrase '}' { MplLanguage.AbsMPL.TYPED_FUNCTION_DEFN $2 $4 $6 $9 }
             | 'fun' PIdent '=' '{' ListPattExprPhrase '}' { MplLanguage.AbsMPL.FUNCTION_DEFN $2 $5 }

ListPattExprPhrase :: { [MplLanguage.AbsMPL.PattExprPhrase] }
ListPattExprPhrase : PattExprPhrase { (:[]) $1 }
                   | PattExprPhrase ';' ListPattExprPhrase { (:) $1 $3 }

ProcessDefn :: { MplLanguage.AbsMPL.ProcessDefn }
ProcessDefn : 'proc' PIdent '::' ListMplType '|' ListMplType '=>' ListMplType '=' '{' ListProcessPhrase '}' { MplLanguage.AbsMPL.TYPED_PROCESS_DEFN $2 $4 $6 $8 $11 }
            | 'proc' PIdent '=' '{' ListProcessPhrase '}' { MplLanguage.AbsMPL.PROCESS_DEFN $2 $5 }

ProcessPhrase :: { MplLanguage.AbsMPL.ProcessPhrase }
ProcessPhrase : ListPattern '|' ListPIdent '=>' ListPIdent '->' ProcessCommandsBlock { MplLanguage.AbsMPL.PROCESS_PHRASE $1 $3 $5 $7 }

ListProcessPhrase :: { [MplLanguage.AbsMPL.ProcessPhrase] }
ListProcessPhrase : ProcessPhrase { (:[]) $1 }
                  | ProcessPhrase ';' ListProcessPhrase { (:) $1 $3 }

ProcessCommandsBlock :: { MplLanguage.AbsMPL.ProcessCommandsBlock }
ProcessCommandsBlock : 'do' '{' ListProcessCommand '}' { MplLanguage.AbsMPL.PROCESS_COMMANDS_DO_BLOCK $3 }
                     | ProcessCommand { MplLanguage.AbsMPL.PROCESS_COMMANDS_SINGLE_COMMAND_BLOCK $1 }

ListProcessCommand :: { [MplLanguage.AbsMPL.ProcessCommand] }
ListProcessCommand : ProcessCommand { (:[]) $1 }
                   | ProcessCommand ';' ListProcessCommand { (:) $1 $3 }

ProcessCommand :: { MplLanguage.AbsMPL.ProcessCommand }
ProcessCommand : PIdent LBracket ListExpr '|' ListPIdent '=>' ListPIdent RBracket { MplLanguage.AbsMPL.PROCESS_RUN $1 $2 $3 $5 $7 $8 }
               | Close PIdent { MplLanguage.AbsMPL.PROCESS_CLOSE $1 $2 }
               | Halt PIdent { MplLanguage.AbsMPL.PROCESS_HALT $1 $2 }
               | Get Pattern 'on' PIdent { MplLanguage.AbsMPL.PROCESS_GET $1 $2 $4 }
               | Put Expr 'on' PIdent { MplLanguage.AbsMPL.PROCESS_PUT $1 $2 $4 }
               | HCase PIdent 'of' '{' ListHCasePhrase '}' { MplLanguage.AbsMPL.PROCESS_HCASE $1 $2 $5 }
               | HPut UIdent 'on' PIdent { MplLanguage.AbsMPL.PROCESS_HPUT $1 $2 $4 }
               | Split PIdent 'into' ListSplitChannel { MplLanguage.AbsMPL.PROCESS_SPLIT $1 $2 $4 }
               | Fork PIdent 'as' '{' ListForkPhrase '}' { MplLanguage.AbsMPL.PROCESS_FORK $1 $2 $5 }
               | PIdent ChId PIdent { MplLanguage.AbsMPL.PROCESS_ID $1 $2 $3 }
               | PIdent ChId 'neg' PIdent { MplLanguage.AbsMPL.PROCESS_NEG $1 $2 $4 }
               | 'race' '{' ListRacePhrase '}' { MplLanguage.AbsMPL.PROCESS_RACE $3 }
               | 'plug' '{' ListPlugPhrase '}' { MplLanguage.AbsMPL.PROCESS_PLUG $3 }
               | Case Expr 'of' '{' ListProcessCasePhrase '}' { MplLanguage.AbsMPL.PROCESS_CASE $1 $2 $5 }
               | 'if' Expr 'then' ProcessCommandsBlock 'else' ProcessCommandsBlock { MplLanguage.AbsMPL.PROCESS_IF $2 $4 $6 }
               | 'switch' '{' ListProcessSwitchPhrase '}' { MplLanguage.AbsMPL.PROCESS_SWITCH $3 }

HCasePhrase :: { MplLanguage.AbsMPL.HCasePhrase }
HCasePhrase : UIdent '->' ProcessCommandsBlock { MplLanguage.AbsMPL.HCASE_PHRASE $1 $3 }

ListHCasePhrase :: { [MplLanguage.AbsMPL.HCasePhrase] }
ListHCasePhrase : {- empty -} { [] }
                | HCasePhrase { (:[]) $1 }
                | HCasePhrase ';' ListHCasePhrase { (:) $1 $3 }

SplitChannel :: { MplLanguage.AbsMPL.SplitChannel }
SplitChannel : PIdent { MplLanguage.AbsMPL.SPLIT_CHANNEL $1 }

ListSplitChannel :: { [MplLanguage.AbsMPL.SplitChannel] }
ListSplitChannel : SplitChannel { (:[]) $1 }
                 | SplitChannel ',' ListSplitChannel { (:) $1 $3 }

ForkPhrase :: { MplLanguage.AbsMPL.ForkPhrase }
ForkPhrase : PIdent '->' ProcessCommandsBlock { MplLanguage.AbsMPL.FORK_PHRASE $1 $3 }
           | PIdent 'with' ListForkChannel '->' ProcessCommandsBlock { MplLanguage.AbsMPL.FORK_WITH_PHRASE $1 $3 $5 }

ListForkPhrase :: { [MplLanguage.AbsMPL.ForkPhrase] }
ListForkPhrase : ForkPhrase { (:[]) $1 }
               | ForkPhrase ';' ListForkPhrase { (:) $1 $3 }

ForkChannel :: { MplLanguage.AbsMPL.ForkChannel }
ForkChannel : PIdent { MplLanguage.AbsMPL.FORK_CHANNEL $1 }

ListForkChannel :: { [MplLanguage.AbsMPL.ForkChannel] }
ListForkChannel : {- empty -} { [] }
                | ForkChannel { (:[]) $1 }
                | ForkChannel ';' ListForkChannel { (:) $1 $3 }

RacePhrase :: { MplLanguage.AbsMPL.RacePhrase }
RacePhrase : PIdent '->' ProcessCommandsBlock { MplLanguage.AbsMPL.RACE_PHRASE $1 $3 }

ListRacePhrase :: { [MplLanguage.AbsMPL.RacePhrase] }
ListRacePhrase : {- empty -} { [] }
               | RacePhrase { (:[]) $1 }
               | RacePhrase ';' ListRacePhrase { (:) $1 $3 }

PlugPhrase :: { MplLanguage.AbsMPL.PlugPhrase }
PlugPhrase : ProcessCommandsBlock { MplLanguage.AbsMPL.PLUG_PHRASE $1 }
           | ListPIdent '=>' ListPIdent '->' ProcessCommandsBlock { MplLanguage.AbsMPL.PLUG_PHRASE_AS $1 $3 $5 }

ListPlugPhrase :: { [MplLanguage.AbsMPL.PlugPhrase] }
ListPlugPhrase : PlugPhrase { (:[]) $1 }
               | PlugPhrase ';' ListPlugPhrase { (:) $1 $3 }

ProcessCasePhrase :: { MplLanguage.AbsMPL.ProcessCasePhrase }
ProcessCasePhrase : Pattern '->' ProcessCommandsBlock { MplLanguage.AbsMPL.PROCESS_CASE_PHRASE $1 $3 }

ListProcessCasePhrase :: { [MplLanguage.AbsMPL.ProcessCasePhrase] }
ListProcessCasePhrase : ProcessCasePhrase { (:[]) $1 }
                      | ProcessCasePhrase ';' ListProcessCasePhrase { (:) $1 $3 }

ProcessSwitchPhrase :: { MplLanguage.AbsMPL.ProcessSwitchPhrase }
ProcessSwitchPhrase : Expr '->' ProcessCommandsBlock { MplLanguage.AbsMPL.PROCESS_SWITCH_PHRASE $1 $3 }

ListProcessSwitchPhrase :: { [MplLanguage.AbsMPL.ProcessSwitchPhrase] }
ListProcessSwitchPhrase : ProcessSwitchPhrase { (:[]) $1 }
                        | ProcessSwitchPhrase ';' ListProcessSwitchPhrase { (:) $1 $3 }
{

happyError :: [Token] -> Either String a
happyError ts = Left $
  "syntax error at " ++ tokenPos ts ++
  case ts of
    []      -> []
    [Err _] -> " due to lexer error"
    t:_     -> " before `" ++ (prToken t) ++ "'"

myLexer = tokens
}

