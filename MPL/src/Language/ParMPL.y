-- This Happy file was machine-generated by the BNF converter
{
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns #-}
module Language.ParMPL where
import Language.AbsMPL
import Language.LexMPL
import Language.ErrM

}

%name pMPL MPL
%name pListMPLstmt ListMPLstmt
%name pMPLstmt MPLstmt
%name pMPLstmtAlt MPLstmtAlt
%name pListMPLstmtAlt ListMPLstmtAlt
%name pRUNstmt RUNstmt
%name pListDefn ListDefn
%name pDefn Defn
%name pTypeDefn TypeDefn
%name pListDataClause ListDataClause
%name pListCoDataClause ListCoDataClause
%name pListTypeSpec ListTypeSpec
%name pDataClause DataClause
%name pCoDataClause CoDataClause
%name pListDataPhrase ListDataPhrase
%name pListCoDataPhrase ListCoDataPhrase
%name pDataPhrase DataPhrase
%name pCoDataPhrase CoDataPhrase
%name pListStructor ListStructor
%name pListType ListType
%name pStructor Structor
%name pTypeSpec TypeSpec
%name pListTypeParam ListTypeParam
%name pTypeParam TypeParam
%name pType Type
%name pTypeN TypeN
%name pListTypeN ListTypeN
%name pListUIdent ListUIdent
%name pCTypeDefn CTypeDefn
%name pProtocolClause ProtocolClause
%name pCoProtocolClause CoProtocolClause
%name pListProtocolPhrase ListProtocolPhrase
%name pListCoProtocolPhrase ListCoProtocolPhrase
%name pProtocolPhrase ProtocolPhrase
%name pCoProtocolPhrase CoProtocolPhrase
%name pProtocol Protocol
%name pProtocol1 Protocol1
%name pListProtocol ListProtocol
%name pFunctionDefn FunctionDefn
%name pListFunctionDefn ListFunctionDefn
%name pListPattTermPhrase ListPattTermPhrase
%name pListPIdent ListPIdent
%name pFoldPattern FoldPattern
%name pListFoldPattern ListFoldPattern
%name pPattTermPhrase PattTermPhrase
%name pListGuardedTerm ListGuardedTerm
%name pGuardedTerm GuardedTerm
%name pListPattern ListPattern
%name pPattern Pattern
%name pPattern1 Pattern1
%name pTerm Term
%name pTerm1 Term1
%name pTerm2 Term2
%name pTerm3 Term3
%name pTerm4 Term4
%name pTerm5 Term5
%name pTerm6 Term6
%name pTerm7 Term7
%name pTerm8 Term8
%name pTerm9 Term9
%name pLetWhere LetWhere
%name pListLetWhere ListLetWhere
%name pPattTerm PattTerm
%name pListRecordEntry ListRecordEntry
%name pListRecordEntryAlt ListRecordEntryAlt
%name pListTerm ListTerm
%name pConstantType ConstantType
%name pRecordEntryAlt RecordEntryAlt
%name pListIdent ListIdent
%name pRecordEntry RecordEntry
%name pProcessDef ProcessDef
%name pPatProcessPhr PatProcessPhr
%name pListChannel ListChannel
%name pProcess Process
%name pListProcessCommand ListProcessCommand
%name pProcessCommand ProcessCommand
%name pPlugPart PlugPart
%name pRacePart RacePart
%name pListRacePart ListRacePart
%name pListPlugPart ListPlugPart
%name pListForkPart ListForkPart
%name pForkPart ForkPart
%name pListHandler ListHandler
%name pHandler Handler
%name pListProcessPhrase ListProcessPhrase
%name pProcessPhrase ProcessPhrase
%name pListGuardProcessPhrase ListGuardProcessPhrase
%name pGuardProcessPhrase GuardProcessPhrase
%name pPChannel PChannel
%name pChannel Channel
-- no lexer declaration
%monad { Err } { thenM } { returnM }
%tokentype {Token}
%token
  '(' { PT _ (TS _ 1) }
  '(*)' { PT _ (TS _ 2) }
  '(+)' { PT _ (TS _ 3) }
  ')' { PT _ (TS _ 4) }
  ',' { PT _ (TS _ 5) }
  '->' { PT _ (TS _ 6) }
  ':' { PT _ (TS _ 7) }
  '::' { PT _ (TS _ 8) }
  ':=' { PT _ (TS _ 9) }
  ';' { PT _ (TS _ 10) }
  '<' { PT _ (TS _ 11) }
  '=' { PT _ (TS _ 12) }
  '=>' { PT _ (TS _ 13) }
  '>' { PT _ (TS _ 14) }
  'Neg' { PT _ (TS _ 15) }
  'and' { PT _ (TS _ 16) }
  'as' { PT _ (TS _ 17) }
  'do' { PT _ (TS _ 18) }
  'else' { PT _ (TS _ 19) }
  'into' { PT _ (TS _ 20) }
  'neg' { PT _ (TS _ 21) }
  'of' { PT _ (TS _ 22) }
  'on' { PT _ (TS _ 23) }
  'plug' { PT _ (TS _ 24) }
  'race' { PT _ (TS _ 25) }
  'switch' { PT _ (TS _ 26) }
  'then' { PT _ (TS _ 27) }
  'where' { PT _ (TS _ 28) }
  'with' { PT _ (TS _ 29) }
  '{' { PT _ (TS _ 30) }
  '|' { PT _ (TS _ 31) }
  '|=|' { PT _ (TS _ 32) }
  '}' { PT _ (TS _ 33) }
  L_quoted { PT _ (TL $$) }
  L_charac { PT _ (TC $$) }
  L_doubl  { PT _ (TD $$) }
  L_ident  { PT _ (TV $$) }
  L_TokUnit { PT _ (T_TokUnit _) }
  L_TokSBrO { PT _ (T_TokSBrO _) }
  L_TokSBrC { PT _ (T_TokSBrC _) }
  L_TokDefn { PT _ (T_TokDefn _) }
  L_TokRun { PT _ (T_TokRun _) }
  L_TokTerm { PT _ (T_TokTerm _) }
  L_TokData { PT _ (T_TokData _) }
  L_TokCodata { PT _ (T_TokCodata _) }
  L_TokType { PT _ (T_TokType _) }
  L_TokProtocol { PT _ (T_TokProtocol _) }
  L_TokCoprotocol { PT _ (T_TokCoprotocol _) }
  L_TokGetProt { PT _ (T_TokGetProt _) }
  L_TokPutProt { PT _ (T_TokPutProt _) }
  L_TokNeg { PT _ (T_TokNeg _) }
  L_TokTopBot { PT _ (T_TokTopBot _) }
  L_TokFun { PT _ (T_TokFun _) }
  L_TokDefault { PT _ (T_TokDefault _) }
  L_TokRecord { PT _ (T_TokRecord _) }
  L_TokIf { PT _ (T_TokIf _) }
  L_TokFold { PT _ (T_TokFold _) }
  L_TokUnfold { PT _ (T_TokUnfold _) }
  L_TokCase { PT _ (T_TokCase _) }
  L_TokProc { PT _ (T_TokProc _) }
  L_TokClose { PT _ (T_TokClose _) }
  L_TokHalt { PT _ (T_TokHalt _) }
  L_TokGet { PT _ (T_TokGet _) }
  L_TokPut { PT _ (T_TokPut _) }
  L_TokHCase { PT _ (T_TokHCase _) }
  L_TokHPut { PT _ (T_TokHPut _) }
  L_TokSplit { PT _ (T_TokSplit _) }
  L_TokFork { PT _ (T_TokFork _) }
  L_TokDCare { PT _ (T_TokDCare _) }
  L_UIdent { PT _ (T_UIdent _) }
  L_PIdent { PT _ (T_PIdent _) }
  L_PInteger { PT _ (T_PInteger _) }
  L_Infix0op { PT _ (T_Infix0op $$) }
  L_Infix1op { PT _ (T_Infix1op $$) }
  L_Infix2op { PT _ (T_Infix2op $$) }
  L_Infix3op { PT _ (T_Infix3op $$) }
  L_Infix4op { PT _ (T_Infix4op $$) }
  L_Infix5op { PT _ (T_Infix5op $$) }
  L_Infix6op { PT _ (T_Infix6op $$) }
  L_Infix7op { PT _ (T_Infix7op $$) }

%%

String  :: { String }
String   : L_quoted {  $1 }

Char    :: { Char }
Char     : L_charac { (read ( $1)) :: Char }

Double  :: { Double }
Double   : L_doubl  { (read ( $1)) :: Double }

Ident   :: { Ident }
Ident    : L_ident  { Ident $1 }

TokUnit :: { TokUnit}
TokUnit  : L_TokUnit { TokUnit (mkPosToken $1)}

TokSBrO :: { TokSBrO}
TokSBrO  : L_TokSBrO { TokSBrO (mkPosToken $1)}

TokSBrC :: { TokSBrC}
TokSBrC  : L_TokSBrC { TokSBrC (mkPosToken $1)}

TokDefn :: { TokDefn}
TokDefn  : L_TokDefn { TokDefn (mkPosToken $1)}

TokRun :: { TokRun}
TokRun  : L_TokRun { TokRun (mkPosToken $1)}

TokTerm :: { TokTerm}
TokTerm  : L_TokTerm { TokTerm (mkPosToken $1)}

TokData :: { TokData}
TokData  : L_TokData { TokData (mkPosToken $1)}

TokCodata :: { TokCodata}
TokCodata  : L_TokCodata { TokCodata (mkPosToken $1)}

TokType :: { TokType}
TokType  : L_TokType { TokType (mkPosToken $1)}

TokProtocol :: { TokProtocol}
TokProtocol  : L_TokProtocol { TokProtocol (mkPosToken $1)}

TokCoprotocol :: { TokCoprotocol}
TokCoprotocol  : L_TokCoprotocol { TokCoprotocol (mkPosToken $1)}

TokGetProt :: { TokGetProt}
TokGetProt  : L_TokGetProt { TokGetProt (mkPosToken $1)}

TokPutProt :: { TokPutProt}
TokPutProt  : L_TokPutProt { TokPutProt (mkPosToken $1)}

TokNeg :: { TokNeg}
TokNeg  : L_TokNeg { TokNeg (mkPosToken $1)}

TokTopBot :: { TokTopBot}
TokTopBot  : L_TokTopBot { TokTopBot (mkPosToken $1)}

TokFun :: { TokFun}
TokFun  : L_TokFun { TokFun (mkPosToken $1)}

TokDefault :: { TokDefault}
TokDefault  : L_TokDefault { TokDefault (mkPosToken $1)}

TokRecord :: { TokRecord}
TokRecord  : L_TokRecord { TokRecord (mkPosToken $1)}

TokIf :: { TokIf}
TokIf  : L_TokIf { TokIf (mkPosToken $1)}

TokFold :: { TokFold}
TokFold  : L_TokFold { TokFold (mkPosToken $1)}

TokUnfold :: { TokUnfold}
TokUnfold  : L_TokUnfold { TokUnfold (mkPosToken $1)}

TokCase :: { TokCase}
TokCase  : L_TokCase { TokCase (mkPosToken $1)}

TokProc :: { TokProc}
TokProc  : L_TokProc { TokProc (mkPosToken $1)}

TokClose :: { TokClose}
TokClose  : L_TokClose { TokClose (mkPosToken $1)}

TokHalt :: { TokHalt}
TokHalt  : L_TokHalt { TokHalt (mkPosToken $1)}

TokGet :: { TokGet}
TokGet  : L_TokGet { TokGet (mkPosToken $1)}

TokPut :: { TokPut}
TokPut  : L_TokPut { TokPut (mkPosToken $1)}

TokHCase :: { TokHCase}
TokHCase  : L_TokHCase { TokHCase (mkPosToken $1)}

TokHPut :: { TokHPut}
TokHPut  : L_TokHPut { TokHPut (mkPosToken $1)}

TokSplit :: { TokSplit}
TokSplit  : L_TokSplit { TokSplit (mkPosToken $1)}

TokFork :: { TokFork}
TokFork  : L_TokFork { TokFork (mkPosToken $1)}

TokDCare :: { TokDCare}
TokDCare  : L_TokDCare { TokDCare (mkPosToken $1)}

UIdent :: { UIdent}
UIdent  : L_UIdent { UIdent (mkPosToken $1)}

PIdent :: { PIdent}
PIdent  : L_PIdent { PIdent (mkPosToken $1)}

PInteger :: { PInteger}
PInteger  : L_PInteger { PInteger (mkPosToken $1)}

Infix0op :: { Infix0op}
Infix0op  : L_Infix0op { Infix0op ($1)}

Infix1op :: { Infix1op}
Infix1op  : L_Infix1op { Infix1op ($1)}

Infix2op :: { Infix2op}
Infix2op  : L_Infix2op { Infix2op ($1)}

Infix3op :: { Infix3op}
Infix3op  : L_Infix3op { Infix3op ($1)}

Infix4op :: { Infix4op}
Infix4op  : L_Infix4op { Infix4op ($1)}

Infix5op :: { Infix5op}
Infix5op  : L_Infix5op { Infix5op ($1)}

Infix6op :: { Infix6op}
Infix6op  : L_Infix6op { Infix6op ($1)}

Infix7op :: { Infix7op}
Infix7op  : L_Infix7op { Infix7op ($1)}

MPL :: { MPL }
MPL : ListMPLstmt RUNstmt { Language.AbsMPL.MPLPROG (reverse $1) $2 }
ListMPLstmt :: { [MPLstmt] }
ListMPLstmt : {- empty -} { [] }
            | ListMPLstmt MPLstmt { flip (:) $1 $2 }
MPLstmt :: { MPLstmt }
MPLstmt : TokDefn 'of' '{' ListDefn '}' 'where' '{' ListMPLstmtAlt '}' { Language.AbsMPL.WHEREDEFN $1 $4 $8 }
        | TokDefn 'of' '{' ListDefn '}' { Language.AbsMPL.WOWHEREDEFN $1 $4 }
        | Defn { Language.AbsMPL.BAREDEFN $1 }
MPLstmtAlt :: { MPLstmtAlt }
MPLstmtAlt : MPLstmt { Language.AbsMPL.MPLSTMTALT $1 }
ListMPLstmtAlt :: { [MPLstmtAlt] }
ListMPLstmtAlt : {- empty -} { [] }
               | MPLstmtAlt { (:[]) $1 }
               | MPLstmtAlt ';' ListMPLstmtAlt { (:) $1 $3 }
RUNstmt :: { RUNstmt }
RUNstmt : TokRun '::' ListProtocol '=>' ListProtocol '=' '{' ListChannel '=>' ListChannel Process '}' { Language.AbsMPL.RUNSTMTWITHType $1 $3 $5 $8 $10 $11 }
        | TokRun ListChannel '=>' ListChannel Process { Language.AbsMPL.RUNSTMTWITHTOUType $1 $2 $4 $5 }
ListDefn :: { [Defn] }
ListDefn : Defn { (:[]) $1 } | Defn ';' ListDefn { (:) $1 $3 }
Defn :: { Defn }
Defn : TypeDefn { Language.AbsMPL.TYPEDEF $1 }
     | CTypeDefn { Language.AbsMPL.PROTOCOLDEF $1 }
     | FunctionDefn { Language.AbsMPL.FUNCTIONDEF $1 }
     | ProcessDef { Language.AbsMPL.PROCESSDEF $1 }
TypeDefn :: { TypeDefn }
TypeDefn : TokData ListDataClause { Language.AbsMPL.DATA $1 $2 }
         | TokCodata ListCoDataClause { Language.AbsMPL.CODATA $1 $2 }
         | TokType ListTypeSpec '=' '{' Type '}' { Language.AbsMPL.TYPE $1 $2 $5 }
ListDataClause :: { [DataClause] }
ListDataClause : DataClause { (:[]) $1 }
               | DataClause 'and' ListDataClause { (:) $1 $3 }
ListCoDataClause :: { [CoDataClause] }
ListCoDataClause : CoDataClause { (:[]) $1 }
                 | CoDataClause 'and' ListCoDataClause { (:) $1 $3 }
ListTypeSpec :: { [TypeSpec] }
ListTypeSpec : {- empty -} { [] }
             | TypeSpec { (:[]) $1 }
             | TypeSpec ',' ListTypeSpec { (:) $1 $3 }
DataClause :: { DataClause }
DataClause : TypeSpec '->' UIdent '=' '{' ListDataPhrase '}' { Language.AbsMPL.DATACLAUSE $1 $3 $6 }
CoDataClause :: { CoDataClause }
CoDataClause : UIdent '->' TypeSpec '=' '{' ListCoDataPhrase '}' { Language.AbsMPL.CODATACLAUSE $1 $3 $6 }
ListDataPhrase :: { [DataPhrase] }
ListDataPhrase : {- empty -} { [] }
               | DataPhrase { (:[]) $1 }
               | DataPhrase ';' ListDataPhrase { (:) $1 $3 }
ListCoDataPhrase :: { [CoDataPhrase] }
ListCoDataPhrase : {- empty -} { [] }
                 | CoDataPhrase { (:[]) $1 }
                 | CoDataPhrase ';' ListCoDataPhrase { (:) $1 $3 }
DataPhrase :: { DataPhrase }
DataPhrase : ListStructor '::' ListType '->' UIdent { Language.AbsMPL.DATAPHRASE $1 $3 $5 }
CoDataPhrase :: { CoDataPhrase }
CoDataPhrase : ListStructor '::' ListType '->' Type { Language.AbsMPL.CODATAPHRASE $1 $3 $5 }
ListStructor :: { [Structor] }
ListStructor : Structor { (:[]) $1 }
             | Structor ',' ListStructor { (:) $1 $3 }
ListType :: { [Type] }
ListType : {- empty -} { [] }
         | Type { (:[]) $1 }
         | Type ',' ListType { (:) $1 $3 }
Structor :: { Structor }
Structor : UIdent { Language.AbsMPL.STRUCTOR $1 }
TypeSpec :: { TypeSpec }
TypeSpec : UIdent '(' ListTypeParam ')' { Language.AbsMPL.TYPESPEC_param $1 $3 }
         | UIdent { Language.AbsMPL.TYPESPEC_basic $1 }
ListTypeParam :: { [TypeParam] }
ListTypeParam : {- empty -} { [] }
              | TypeParam { (:[]) $1 }
              | TypeParam ',' ListTypeParam { (:) $1 $3 }
TypeParam :: { TypeParam }
TypeParam : UIdent { Language.AbsMPL.TYPEPARAM $1 }
Type :: { Type }
Type : TypeN '=>' Type { Language.AbsMPL.TYPEARROW $1 $3 }
     | TypeN { Language.AbsMPL.TYPENext $1 }
TypeN :: { TypeN }
TypeN : TokUnit { Language.AbsMPL.TYPEUNIT $1 }
      | TokSBrO TypeN TokSBrC { Language.AbsMPL.TYPELIST $1 $2 $3 }
      | UIdent '(' ListType ')' { Language.AbsMPL.TYPEDATCODAT $1 $3 }
      | UIdent { Language.AbsMPL.TYPECONST_VAR $1 }
      | '<' ListType '>' { Language.AbsMPL.TYPEPROD $2 }
      | '(' Type ')' { Language.AbsMPL.TYPEBRACKET $2 }
ListTypeN :: { [TypeN] }
ListTypeN : {- empty -} { [] }
          | TypeN { (:[]) $1 }
          | TypeN ',' ListTypeN { (:) $1 $3 }
ListUIdent :: { [UIdent] }
ListUIdent : {- empty -} { [] }
           | UIdent { (:[]) $1 }
           | UIdent ',' ListUIdent { (:) $1 $3 }
CTypeDefn :: { CTypeDefn }
CTypeDefn : TokProtocol ProtocolClause { Language.AbsMPL.PROTOCOL $1 $2 }
          | TokCoprotocol CoProtocolClause { Language.AbsMPL.COPROTOCOL $1 $2 }
ProtocolClause :: { ProtocolClause }
ProtocolClause : TypeSpec '=>' UIdent '=' '{' ListProtocolPhrase '}' { Language.AbsMPL.PROTOCOLCLAUSE $1 $3 $6 }
CoProtocolClause :: { CoProtocolClause }
CoProtocolClause : UIdent '=>' TypeSpec '=' '{' ListCoProtocolPhrase '}' { Language.AbsMPL.COPROTOCOLCLAUSE $1 $3 $6 }
ListProtocolPhrase :: { [ProtocolPhrase] }
ListProtocolPhrase : {- empty -} { [] }
                   | ProtocolPhrase { (:[]) $1 }
                   | ProtocolPhrase ';' ListProtocolPhrase { (:) $1 $3 }
ListCoProtocolPhrase :: { [CoProtocolPhrase] }
ListCoProtocolPhrase : {- empty -} { [] }
                     | CoProtocolPhrase { (:[]) $1 }
                     | CoProtocolPhrase ';' ListCoProtocolPhrase { (:) $1 $3 }
ProtocolPhrase :: { ProtocolPhrase }
ProtocolPhrase : UIdent '::' Protocol '=>' UIdent { Language.AbsMPL.PROTOCOLPHRASE $1 $3 $5 }
CoProtocolPhrase :: { CoProtocolPhrase }
CoProtocolPhrase : UIdent '::' UIdent '=>' Protocol { Language.AbsMPL.COPROTOCOLPHRASE $1 $3 $5 }
Protocol :: { Protocol }
Protocol : Protocol1 { $1 }
         | Protocol1 '(*)' Protocol { Language.AbsMPL.PROTOCOLtensor $1 $3 }
         | Protocol1 '(+)' Protocol { Language.AbsMPL.PROTOCOLpar $1 $3 }
Protocol1 :: { Protocol }
Protocol1 : '(' Protocol ')' { $2 }
          | TokGetProt '(' Type '|' Protocol ')' { Language.AbsMPL.PROTOCOLget $1 $3 $5 }
          | TokPutProt '(' Type '|' Protocol ')' { Language.AbsMPL.PROTOCOLput $1 $3 $5 }
          | 'Neg' '(' Protocol ')' { Language.AbsMPL.PROTOCOLneg $3 }
          | TokTopBot { Language.AbsMPL.PROTOCOLtopbot $1 }
          | UIdent '(' ListType ')' { Language.AbsMPL.PROTNamedWArgs $1 $3 }
          | UIdent { Language.AbsMPL.PROTNamedWOArgs $1 }
ListProtocol :: { [Protocol] }
ListProtocol : {- empty -} { [] }
             | Protocol { (:[]) $1 }
             | Protocol ',' ListProtocol { (:) $1 $3 }
FunctionDefn :: { FunctionDefn }
FunctionDefn : TokFun PIdent '::' ListType '->' Type '=' '{' ListPattTermPhrase '}' { Language.AbsMPL.FUNCTIONDEFNfull $1 $2 $4 $6 $9 }
             | TokFun PIdent '=' '{' ListPattTermPhrase '}' { Language.AbsMPL.FUNCTIONDEFNshort $1 $2 $5 }
ListFunctionDefn :: { [FunctionDefn] }
ListFunctionDefn : FunctionDefn { (:[]) $1 }
                 | FunctionDefn ';' ListFunctionDefn { (:) $1 $3 }
ListPattTermPhrase :: { [PattTermPhrase] }
ListPattTermPhrase : PattTermPhrase { (:[]) $1 }
                   | PattTermPhrase ';' ListPattTermPhrase { (:) $1 $3 }
ListPIdent :: { [PIdent] }
ListPIdent : {- empty -} { [] }
           | PIdent { (:[]) $1 }
           | PIdent ',' ListPIdent { (:) $1 $3 }
FoldPattern :: { FoldPattern }
FoldPattern : UIdent ':' ListPIdent '=' '{' Term '}' { Language.AbsMPL.FOLDPATT_WOBRAC $1 $3 $6 }
ListFoldPattern :: { [FoldPattern] }
ListFoldPattern : {- empty -} { [] }
                | FoldPattern { (:[]) $1 }
                | FoldPattern ';' ListFoldPattern { (:) $1 $3 }
PattTermPhrase :: { PattTermPhrase }
PattTermPhrase : ListPattern '->' Term { Language.AbsMPL.PATTERNshort $1 $3 }
               | ListPattern '->' 'switch' '{' ListGuardedTerm '}' { Language.AbsMPL.PATTERNguard $1 $5 }
ListGuardedTerm :: { [GuardedTerm] }
ListGuardedTerm : GuardedTerm { (:[]) $1 }
                | GuardedTerm ';' ListGuardedTerm { (:) $1 $3 }
GuardedTerm :: { GuardedTerm }
GuardedTerm : Term '=' '{' Term '}' { Language.AbsMPL.GUARDterm $1 $4 }
            | TokDefault '=' '{' Term '}' { Language.AbsMPL.GUARDother $1 $4 }
ListPattern :: { [Pattern] }
ListPattern : {- empty -} { [] }
            | Pattern { (:[]) $1 }
            | Pattern ',' ListPattern { (:) $1 $3 }
Pattern :: { Pattern }
Pattern : Pattern1 ':' Pattern { Language.AbsMPL.LISTPATTERN2 $1 $3 }
        | Pattern1 { $1 }
Pattern1 :: { Pattern }
Pattern1 : UIdent '(' ListPattern ')' { Language.AbsMPL.CONSPATTERN $1 $3 }
         | UIdent { Language.AbsMPL.CONSPATTERN_WA $1 }
         | TokSBrO ListPattern TokSBrC { Language.AbsMPL.LISTPATTERN1 $1 $2 $3 }
         | '<' ListPattern '>' { Language.AbsMPL.PRODPATTERN $2 }
         | PIdent { Language.AbsMPL.VARPATTERN $1 }
         | String { Language.AbsMPL.STR_CONSTPATTERN $1 }
         | PInteger { Language.AbsMPL.INT_CONSTPATTERN $1 }
         | TokDCare { Language.AbsMPL.NULLPATTERN $1 }
         | '(' Pattern ')' { $2 }
Term :: { Term }
Term : Term1 ':' Term { Language.AbsMPL.LISTTERM2 $1 $3 }
     | Term1 { $1 }
     | Term1 'where' '{' ListLetWhere '}' { Language.AbsMPL.LETTERM $1 $4 }
Term1 :: { Term }
Term1 : Term1 Infix0op Term2 { Language.AbsMPL.Infix0TERM $1 $2 $3 }
      | Term2 { $1 }
Term2 :: { Term }
Term2 : Term2 Infix1op Term3 { Language.AbsMPL.Infix1TERM $1 $2 $3 }
      | Term3 { $1 }
Term3 :: { Term }
Term3 : Term3 Infix2op Term4 { Language.AbsMPL.Infix2TERM $1 $2 $3 }
      | Term4 { $1 }
Term4 :: { Term }
Term4 : Term4 Infix3op Term5 { Language.AbsMPL.Infix3TERM $1 $2 $3 }
      | Term5 { $1 }
Term5 :: { Term }
Term5 : Term5 Infix4op Term6 { Language.AbsMPL.Infix4TERM $1 $2 $3 }
      | Term6 { $1 }
Term6 :: { Term }
Term6 : Term6 Infix5op Term7 { Language.AbsMPL.Infix5TERM $1 $2 $3 }
      | Term7 { $1 }
Term7 :: { Term }
Term7 : Term8 Infix6op Term7 { Language.AbsMPL.Infix6TERM $1 $2 $3 }
      | Term8 { $1 }
Term8 :: { Term }
Term8 : Term8 Infix7op Term9 { Language.AbsMPL.Infix7TERM $1 $2 $3 }
      | Term9 { $1 }
Term9 :: { Term }
Term9 : TokSBrO ListTerm TokSBrC { Language.AbsMPL.LISTTERM $1 $2 $3 }
      | PIdent { Language.AbsMPL.VARTERM $1 }
      | ConstantType { Language.AbsMPL.CONSTTERM $1 }
      | TokIf Term 'then' Term 'else' '{' Term '}' { Language.AbsMPL.IFTERM $1 $2 $4 $7 }
      | TokUnfold PIdent 'with' '{' ListFoldPattern '}' { Language.AbsMPL.UNFOLDTERM $1 $2 $5 }
      | TokFold PIdent 'of' '{' ListFoldPattern '}' { Language.AbsMPL.FOLDTERM $1 $2 $5 }
      | TokCase Term 'of' '{' ListPattTermPhrase '}' { Language.AbsMPL.CASETERM $1 $2 $5 }
      | UIdent '(' ListTerm ')' { Language.AbsMPL.GENCONSTERM_WARGS $1 $3 }
      | UIdent { Language.AbsMPL.GENCONSTERM_WOARGS $1 }
      | '<' ListTerm '>' { Language.AbsMPL.PRODTERM $2 }
      | PIdent '(' ListTerm ')' { Language.AbsMPL.FUNAPPTERM $1 $3 }
      | TokRecord 'of' '{' ListRecordEntry '}' { Language.AbsMPL.RECORDTERM $1 $4 }
      | '(' ListRecordEntryAlt ')' { Language.AbsMPL.RECORDTERMALT $2 }
      | '(' Term ')' { $2 }
LetWhere :: { LetWhere }
LetWhere : Defn { Language.AbsMPL.DEFN_LetWhere $1 }
         | PattTerm { Language.AbsMPL.PATTTERM_LetWhere $1 }
ListLetWhere :: { [LetWhere] }
ListLetWhere : LetWhere { (:[]) $1 }
             | LetWhere ';' ListLetWhere { (:) $1 $3 }
PattTerm :: { PattTerm }
PattTerm : PIdent '=' '{' Term '}' { Language.AbsMPL.JUSTPATTTERM $1 $4 }
ListRecordEntry :: { [RecordEntry] }
ListRecordEntry : {- empty -} { [] }
                | RecordEntry { (:[]) $1 }
                | RecordEntry ';' ListRecordEntry { (:) $1 $3 }
ListRecordEntryAlt :: { [RecordEntryAlt] }
ListRecordEntryAlt : {- empty -} { [] }
                   | RecordEntryAlt { (:[]) $1 }
                   | RecordEntryAlt ',' ListRecordEntryAlt { (:) $1 $3 }
ListTerm :: { [Term] }
ListTerm : {- empty -} { [] }
         | Term { (:[]) $1 }
         | Term ',' ListTerm { (:) $1 $3 }
ConstantType :: { ConstantType }
ConstantType : PInteger { Language.AbsMPL.INTEGER $1 }
             | String { Language.AbsMPL.STRING $1 }
             | Char { Language.AbsMPL.CHAR $1 }
             | Double { Language.AbsMPL.DOUBLE $1 }
RecordEntryAlt :: { RecordEntryAlt }
RecordEntryAlt : RecordEntry { Language.AbsMPL.RECORDENTRY_ALT $1 }
ListIdent :: { [Ident] }
ListIdent : Ident { (:[]) $1 } | Ident ',' ListIdent { (:) $1 $3 }
RecordEntry :: { RecordEntry }
RecordEntry : Pattern ':=' Term { Language.AbsMPL.RECORDENTRY $1 $3 }
ProcessDef :: { ProcessDef }
ProcessDef : TokProc PIdent '::' ListType '|' ListProtocol '=>' ListProtocol '=' '{' PatProcessPhr '}' { Language.AbsMPL.PROCESSDEFfull $1 $2 $4 $6 $8 $11 }
           | TokProc PIdent '=' '{' PatProcessPhr '}' { Language.AbsMPL.PROCESSDEFshort $1 $2 $5 }
PatProcessPhr :: { PatProcessPhr }
PatProcessPhr : ListPattern '|' ListChannel '=>' ListChannel Process { Language.AbsMPL.PROCESSPHRASEnoguard $1 $3 $5 $6 }
ListChannel :: { [Channel] }
ListChannel : {- empty -} { [] }
            | Channel { (:[]) $1 }
            | Channel ',' ListChannel { (:) $1 $3 }
Process :: { Process }
Process : '->' 'do' '{' ListProcessCommand '}' { Language.AbsMPL.MANY_PROCESS $4 }
        | '->' ProcessCommand { Language.AbsMPL.ONE_PROCESS $2 }
ListProcessCommand :: { [ProcessCommand] }
ListProcessCommand : {- empty -} { [] }
                   | ProcessCommand { (:[]) $1 }
                   | ProcessCommand ';' ListProcessCommand { (:) $1 $3 }
ProcessCommand :: { ProcessCommand }
ProcessCommand : PIdent '(' ListTerm '|' ListChannel '=>' ListChannel ')' { Language.AbsMPL.PROCESS_RUN $1 $3 $5 $7 }
               | TokClose Channel { Language.AbsMPL.PROCESS_CLOSE $1 $2 }
               | TokHalt Channel { Language.AbsMPL.PROCESS_HALT $1 $2 }
               | TokGet PIdent 'on' Channel { Language.AbsMPL.PROCESS_GET $1 $2 $4 }
               | TokHCase Channel 'of' '{' ListHandler '}' { Language.AbsMPL.PROCESS_HCASE $1 $2 $5 }
               | TokPut Term 'on' Channel { Language.AbsMPL.PROCESS_PUT $1 $2 $4 }
               | TokHPut UIdent 'on' Channel { Language.AbsMPL.PROCESS_HPUT $1 $2 $4 }
               | TokSplit Channel 'into' ListChannel { Language.AbsMPL.PROCESS_SPLIT $1 $2 $4 }
               | TokFork PIdent 'as' '{' ListForkPart '}' { Language.AbsMPL.PROCESS_FORK $1 $2 $5 }
               | 'plug' '{' ListPlugPart '}' { Language.AbsMPL.Process_PLUG $3 }
               | 'race' '{' ListRacePart '}' { Language.AbsMPL.Process_RACE $3 }
               | Channel '|=|' PChannel { Language.AbsMPL.Procss_ID $1 $3 }
               | Channel '=' '{' 'neg' Channel '}' { Language.AbsMPL.PROCESS_NEG $1 $5 }
               | TokCase Term 'of' '{' ListProcessPhrase '}' { Language.AbsMPL.PROCESScase $1 $2 $5 }
PlugPart :: { PlugPart }
PlugPart : 'do' '{' ListProcessCommand '}' { Language.AbsMPL.PLUGPART_MANY $3 }
         | ProcessCommand { Language.AbsMPL.PLUGPART_ONE $1 }
RacePart :: { RacePart }
RacePart : Channel Process { Language.AbsMPL.RACEPART $1 $2 }
ListRacePart :: { [RacePart] }
ListRacePart : RacePart { (:[]) $1 }
             | RacePart ';' ListRacePart { (:) $1 $3 }
ListPlugPart :: { [PlugPart] }
ListPlugPart : PlugPart { (:[]) $1 }
             | PlugPart ';' ListPlugPart { (:) $1 $3 }
ListForkPart :: { [ForkPart] }
ListForkPart : ForkPart { (:[]) $1 }
             | ForkPart ';' ListForkPart { (:) $1 $3 }
ForkPart :: { ForkPart }
ForkPart : PIdent Process { Language.AbsMPL.FORKPARTshort $1 $2 }
ListHandler :: { [Handler] }
ListHandler : {- empty -} { [] }
            | Handler { (:[]) $1 }
            | Handler ';' ListHandler { (:) $1 $3 }
Handler :: { Handler }
Handler : UIdent Process { Language.AbsMPL.HANDLER $1 $2 }
ListProcessPhrase :: { [ProcessPhrase] }
ListProcessPhrase : {- empty -} { [] }
                  | ProcessPhrase { (:[]) $1 }
                  | ProcessPhrase ';' ListProcessPhrase { (:) $1 $3 }
ProcessPhrase :: { ProcessPhrase }
ProcessPhrase : Pattern Process { Language.AbsMPL.CASEPROCESSnoguard $1 $2 }
ListGuardProcessPhrase :: { [GuardProcessPhrase] }
ListGuardProcessPhrase : GuardProcessPhrase { (:[]) $1 }
                       | GuardProcessPhrase ';' ListGuardProcessPhrase { (:) $1 $3 }
GuardProcessPhrase :: { GuardProcessPhrase }
GuardProcessPhrase : Term '=' '{' ListProcessCommand '}' { Language.AbsMPL.GUARDEDPROCESSterm $1 $4 }
                   | TokDefault '=' '{' ListProcessCommand '}' { Language.AbsMPL.GUARDEDPROCESSother $1 $4 }
PChannel :: { PChannel }
PChannel : PIdent { Language.AbsMPL.BARECHANNEL $1 }
         | 'neg' PIdent { Language.AbsMPL.NEGCHANNEL $2 }
Channel :: { Channel }
Channel : PIdent { Language.AbsMPL.CHANNEL $1 }
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
