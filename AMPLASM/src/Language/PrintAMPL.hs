{-# LANGUAGE CPP #-}
#if __GLASGOW_HASKELL__ <= 708
{-# LANGUAGE OverlappingInstances #-}
#endif
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}

-- | Pretty-printer for Language.
--   Generated by the BNF converter.

module Language.PrintAMPL where

import qualified Language.AbsAMPL
import Data.Char

-- | The top-level printing method.

printTree :: Print a => a -> String
printTree = render . prt 0

type Doc = [ShowS] -> [ShowS]

doc :: ShowS -> Doc
doc = (:)

render :: Doc -> String
render d = rend 0 (map ($ "") $ d []) "" where
  rend i ss = case ss of
    "["      :ts -> showChar '[' . rend i ts
    "("      :ts -> showChar '(' . rend i ts
    "{"      :ts -> showChar '{' . new (i+1) . rend (i+1) ts
    "}" : ";":ts -> new (i-1) . space "}" . showChar ';' . new (i-1) . rend (i-1) ts
    "}"      :ts -> new (i-1) . showChar '}' . new (i-1) . rend (i-1) ts
    ";"      :ts -> showChar ';' . new i . rend i ts
    t  : ts@(p:_) | closingOrPunctuation p -> showString t . rend i ts
    t        :ts -> space t . rend i ts
    _            -> id
  new i   = showChar '\n' . replicateS (2*i) (showChar ' ') . dropWhile isSpace
  space t = showString t . (\s -> if null s then "" else ' ':s)

  closingOrPunctuation :: String -> Bool
  closingOrPunctuation [c] = c `elem` closerOrPunct
  closingOrPunctuation _   = False

  closerOrPunct :: String
  closerOrPunct = ")],;"

parenth :: Doc -> Doc
parenth ss = doc (showChar '(') . ss . doc (showChar ')')

concatS :: [ShowS] -> ShowS
concatS = foldr (.) id

concatD :: [Doc] -> Doc
concatD = foldr (.) id

replicateS :: Int -> ShowS -> ShowS
replicateS n f = concatS (replicate n f)

-- | The printer class does the job.

class Print a where
  prt :: Int -> a -> Doc
  prtList :: Int -> [a] -> Doc
  prtList i = concatD . map (prt i)

instance {-# OVERLAPPABLE #-} Print a => Print [a] where
  prt = prtList

instance Print Char where
  prt _ s = doc (showChar '\'' . mkEsc '\'' s . showChar '\'')
  prtList _ s = doc (showChar '"' . concatS (map (mkEsc '"') s) . showChar '"')

mkEsc :: Char -> Char -> ShowS
mkEsc q s = case s of
  _ | s == q -> showChar '\\' . showChar s
  '\\'-> showString "\\\\"
  '\n' -> showString "\\n"
  '\t' -> showString "\\t"
  _ -> showChar s

prPrec :: Int -> Int -> Doc -> Doc
prPrec i j = if j < i then parenth else id

instance Print Integer where
  prt _ x = doc (shows x)

instance Print Double where
  prt _ x = doc (shows x)

instance Print Language.AbsAMPL.Store where
  prt _ (Language.AbsAMPL.Store (_,i)) = doc (showString i)

instance Print Language.AbsAMPL.Load where
  prt _ (Language.AbsAMPL.Load (_,i)) = doc (showString i)

instance Print Language.AbsAMPL.Ret where
  prt _ (Language.AbsAMPL.Ret (_,i)) = doc (showString i)

instance Print Language.AbsAMPL.Call where
  prt _ (Language.AbsAMPL.Call (_,i)) = doc (showString i)

instance Print Language.AbsAMPL.ConstInt where
  prt _ (Language.AbsAMPL.ConstInt (_,i)) = doc (showString i)

instance Print Language.AbsAMPL.ConstChar where
  prt _ (Language.AbsAMPL.ConstChar (_,i)) = doc (showString i)

instance Print Language.AbsAMPL.ConstString where
  prt _ (Language.AbsAMPL.ConstString (_,i)) = doc (showString i)

instance Print Language.AbsAMPL.ToStr where
  prt _ (Language.AbsAMPL.ToStr (_,i)) = doc (showString i)

instance Print Language.AbsAMPL.ToInt where
  prt _ (Language.AbsAMPL.ToInt (_,i)) = doc (showString i)

instance Print Language.AbsAMPL.And where
  prt _ (Language.AbsAMPL.And (_,i)) = doc (showString i)

instance Print Language.AbsAMPL.Or where
  prt _ (Language.AbsAMPL.Or (_,i)) = doc (showString i)

instance Print Language.AbsAMPL.Append where
  prt _ (Language.AbsAMPL.Append (_,i)) = doc (showString i)

instance Print Language.AbsAMPL.Unstring where
  prt _ (Language.AbsAMPL.Unstring (_,i)) = doc (showString i)

instance Print Language.AbsAMPL.LeqI where
  prt _ (Language.AbsAMPL.LeqI (_,i)) = doc (showString i)

instance Print Language.AbsAMPL.EqI where
  prt _ (Language.AbsAMPL.EqI (_,i)) = doc (showString i)

instance Print Language.AbsAMPL.Leqc where
  prt _ (Language.AbsAMPL.Leqc (_,i)) = doc (showString i)

instance Print Language.AbsAMPL.Eqc where
  prt _ (Language.AbsAMPL.Eqc (_,i)) = doc (showString i)

instance Print Language.AbsAMPL.Leqs where
  prt _ (Language.AbsAMPL.Leqs (_,i)) = doc (showString i)

instance Print Language.AbsAMPL.Eqs where
  prt _ (Language.AbsAMPL.Eqs (_,i)) = doc (showString i)

instance Print Language.AbsAMPL.ConcatS where
  prt _ (Language.AbsAMPL.ConcatS (_,i)) = doc (showString i)

instance Print Language.AbsAMPL.Add where
  prt _ (Language.AbsAMPL.Add (_,i)) = doc (showString i)

instance Print Language.AbsAMPL.Subtract where
  prt _ (Language.AbsAMPL.Subtract (_,i)) = doc (showString i)

instance Print Language.AbsAMPL.Mul where
  prt _ (Language.AbsAMPL.Mul (_,i)) = doc (showString i)

instance Print Language.AbsAMPL.Quot where
  prt _ (Language.AbsAMPL.Quot (_,i)) = doc (showString i)

instance Print Language.AbsAMPL.Rem where
  prt _ (Language.AbsAMPL.Rem (_,i)) = doc (showString i)

instance Print Language.AbsAMPL.Cons where
  prt _ (Language.AbsAMPL.Cons (_,i)) = doc (showString i)

instance Print Language.AbsAMPL.Case where
  prt _ (Language.AbsAMPL.Case (_,i)) = doc (showString i)

instance Print Language.AbsAMPL.If where
  prt _ (Language.AbsAMPL.If (_,i)) = doc (showString i)

instance Print Language.AbsAMPL.Rec where
  prt _ (Language.AbsAMPL.Rec (_,i)) = doc (showString i)

instance Print Language.AbsAMPL.Get where
  prt _ (Language.AbsAMPL.Get (_,i)) = doc (showString i)

instance Print Language.AbsAMPL.Put where
  prt _ (Language.AbsAMPL.Put (_,i)) = doc (showString i)

instance Print Language.AbsAMPL.Hput where
  prt _ (Language.AbsAMPL.Hput (_,i)) = doc (showString i)

instance Print Language.AbsAMPL.Hcase where
  prt _ (Language.AbsAMPL.Hcase (_,i)) = doc (showString i)

instance Print Language.AbsAMPL.Split where
  prt _ (Language.AbsAMPL.Split (_,i)) = doc (showString i)

instance Print Language.AbsAMPL.Fork where
  prt _ (Language.AbsAMPL.Fork (_,i)) = doc (showString i)

instance Print Language.AbsAMPL.Plug where
  prt _ (Language.AbsAMPL.Plug (_,i)) = doc (showString i)

instance Print Language.AbsAMPL.Run where
  prt _ (Language.AbsAMPL.Run (_,i)) = doc (showString i)

instance Print Language.AbsAMPL.Race where
  prt _ (Language.AbsAMPL.Race (_,i)) = doc (showString i)

instance Print Language.AbsAMPL.Close where
  prt _ (Language.AbsAMPL.Close (_,i)) = doc (showString i)

instance Print Language.AbsAMPL.Halt where
  prt _ (Language.AbsAMPL.Halt (_,i)) = doc (showString i)

instance Print Language.AbsAMPL.Ch_Id where
  prt _ (Language.AbsAMPL.Ch_Id (_,i)) = doc (showString i)

instance Print Language.AbsAMPL.Main_run where
  prt _ (Language.AbsAMPL.Main_run (_,i)) = doc (showString i)

instance Print Language.AbsAMPL.BTrue where
  prt _ (Language.AbsAMPL.BTrue (_,i)) = doc (showString i)

instance Print Language.AbsAMPL.BFalse where
  prt _ (Language.AbsAMPL.BFalse (_,i)) = doc (showString i)

instance Print Language.AbsAMPL.Character where
  prt _ (Language.AbsAMPL.Character (_,i)) = doc (showString i)

instance Print Language.AbsAMPL.UIdent where
  prt _ (Language.AbsAMPL.UIdent (_,i)) = doc (showString i)

instance Print Language.AbsAMPL.PIdent where
  prt _ (Language.AbsAMPL.PIdent (_,i)) = doc (showString i)
  prtList _ [] = concatD []
  prtList _ [x] = concatD [prt 0 x]
  prtList _ (x:xs) = concatD [prt 0 x, doc (showString ","), prt 0 xs]

instance Print Language.AbsAMPL.PInteger where
  prt _ (Language.AbsAMPL.PInteger (_,i)) = doc (showString i)

instance Print Language.AbsAMPL.IIdent where
  prt _ (Language.AbsAMPL.IIdent (_,i)) = doc (showString i)

instance Print Language.AbsAMPL.AMPLCODE where
  prt i e = case e of
    Language.AbsAMPL.Main amplconstructss start -> prPrec i 0 (concatD [prt 0 amplconstructss, prt 0 start])

instance Print Language.AbsAMPL.AMPL_CONSTRUCTS where
  prt i e = case e of
    Language.AbsAMPL.IMPORT_CONSTRUCT import_ -> prPrec i 0 (concatD [prt 0 import_])
    Language.AbsAMPL.HANDLE_CONSTRUCT handles -> prPrec i 0 (concatD [prt 0 handles])
    Language.AbsAMPL.COHANDLE_CONSTRUCT cohandles -> prPrec i 0 (concatD [prt 0 cohandles])
    Language.AbsAMPL.CONSTRUCTOR_CONSTRUCT constructors -> prPrec i 0 (concatD [prt 0 constructors])
    Language.AbsAMPL.DESTRUCTOR_CONSTRUCT destructors -> prPrec i 0 (concatD [prt 0 destructors])
    Language.AbsAMPL.PROCESSES_CONSTRUCT processes -> prPrec i 0 (concatD [prt 0 processes])
    Language.AbsAMPL.FUNCTIONS_CONSTRUCT functions -> prPrec i 0 (concatD [prt 0 functions])
  prtList _ [] = concatD []
  prtList _ (x:xs) = concatD [prt 0 x, prt 0 xs]

instance Print [Language.AbsAMPL.AMPL_CONSTRUCTS] where
  prt = prtList

instance Print Language.AbsAMPL.HANDLE_SPEC where
  prt i e = case e of
    Language.AbsAMPL.Hand_spec uident handles -> prPrec i 0 (concatD [prt 0 uident, doc (showString "="), doc (showString "{"), prt 0 handles, doc (showString "}")])
  prtList _ [] = concatD []
  prtList _ [x] = concatD [prt 0 x]
  prtList _ (x:xs) = concatD [prt 0 x, doc (showString ";"), prt 0 xs]

instance Print Language.AbsAMPL.Handle where
  prt i e = case e of
    Language.AbsAMPL.HandName uident -> prPrec i 0 (concatD [prt 0 uident])
  prtList _ [x] = concatD [prt 0 x]
  prtList _ (x:xs) = concatD [prt 0 x, doc (showString ";"), prt 0 xs]

instance Print [Language.AbsAMPL.HANDLE_SPEC] where
  prt = prtList

instance Print [Language.AbsAMPL.Handle] where
  prt = prtList

instance Print Language.AbsAMPL.IMPORT where
  prt i e = case e of
    Language.AbsAMPL.Import iident -> prPrec i 0 (concatD [doc (showString "%include"), prt 0 iident])

instance Print Language.AbsAMPL.CONSTRUCTORS where
  prt i e = case e of
    Language.AbsAMPL.Constructors structorspecs -> prPrec i 0 (concatD [doc (showString "%constructors"), doc (showString ":"), doc (showString "{"), prt 0 structorspecs, doc (showString "}")])

instance Print Language.AbsAMPL.DESTRUCTORS where
  prt i e = case e of
    Language.AbsAMPL.Destructors structorspecs -> prPrec i 0 (concatD [doc (showString "%destructors"), doc (showString ":"), doc (showString "{"), prt 0 structorspecs, doc (showString "}")])

instance Print Language.AbsAMPL.STRUCTOR_SPEC where
  prt i e = case e of
    Language.AbsAMPL.Struct_spec uident structs -> prPrec i 0 (concatD [prt 0 uident, doc (showString "="), doc (showString "{"), prt 0 structs, doc (showString "}")])
  prtList _ [] = concatD []
  prtList _ [x] = concatD [prt 0 x]
  prtList _ (x:xs) = concatD [prt 0 x, doc (showString ";"), prt 0 xs]

instance Print Language.AbsAMPL.STRUCT where
  prt i e = case e of
    Language.AbsAMPL.Struct uident pinteger -> prPrec i 0 (concatD [prt 0 uident, prt 0 pinteger])
  prtList _ [x] = concatD [prt 0 x]
  prtList _ (x:xs) = concatD [prt 0 x, doc (showString ";"), prt 0 xs]

instance Print [Language.AbsAMPL.STRUCTOR_SPEC] where
  prt = prtList

instance Print [Language.AbsAMPL.STRUCT] where
  prt = prtList

instance Print Language.AbsAMPL.HANDLES where
  prt i e = case e of
    Language.AbsAMPL.Handles handlespecs -> prPrec i 0 (concatD [doc (showString "%handles"), doc (showString ":"), doc (showString "{"), prt 0 handlespecs, doc (showString "}")])

instance Print Language.AbsAMPL.COHANDLES where
  prt i e = case e of
    Language.AbsAMPL.Cohandles handlespecs -> prPrec i 0 (concatD [doc (showString "%cohandles"), doc (showString ":"), doc (showString "{"), prt 0 handlespecs, doc (showString "}")])

instance Print Language.AbsAMPL.PROCESSES where
  prt i e = case e of
    Language.AbsAMPL.Processes processspecs -> prPrec i 0 (concatD [doc (showString "%processes"), doc (showString ":"), doc (showString "{"), prt 0 processspecs, doc (showString "}")])

instance Print [Language.AbsAMPL.PROCESS_SPEC] where
  prt = prtList

instance Print Language.AbsAMPL.PROCESS_SPEC where
  prt i e = case e of
    Language.AbsAMPL.Process_spec pident varss pidents1 pidents2 coms -> prPrec i 0 (concatD [prt 0 pident, doc (showString "("), prt 0 varss, doc (showString "|"), prt 0 pidents1, doc (showString "=>"), prt 0 pidents2, doc (showString ")"), doc (showString "="), prt 0 coms])
  prtList _ [] = concatD []
  prtList _ [x] = concatD [prt 0 x]
  prtList _ (x:xs) = concatD [prt 0 x, doc (showString ";"), prt 0 xs]

instance Print Language.AbsAMPL.Vars where
  prt i e = case e of
    Language.AbsAMPL.VName pident -> prPrec i 0 (concatD [prt 0 pident])
  prtList _ [] = concatD []
  prtList _ [x] = concatD [prt 0 x]
  prtList _ (x:xs) = concatD [prt 0 x, doc (showString ","), prt 0 xs]

instance Print [Language.AbsAMPL.Vars] where
  prt = prtList

instance Print Language.AbsAMPL.FUNCTIONS where
  prt i e = case e of
    Language.AbsAMPL.Functions functionspecs -> prPrec i 0 (concatD [doc (showString "%functions"), doc (showString ":"), doc (showString "{"), prt 0 functionspecs, doc (showString "}")])

instance Print [Language.AbsAMPL.FUNCTION_SPEC] where
  prt = prtList

instance Print Language.AbsAMPL.FUNCTION_SPEC where
  prt i e = case e of
    Language.AbsAMPL.Function_spec pident varss coms -> prPrec i 0 (concatD [prt 0 pident, doc (showString "("), prt 0 varss, doc (showString ")"), doc (showString "="), prt 0 coms])
  prtList _ [] = concatD []
  prtList _ [x] = concatD [prt 0 x]
  prtList _ (x:xs) = concatD [prt 0 x, doc (showString ";"), prt 0 xs]

instance Print Language.AbsAMPL.START where
  prt i e = case e of
    Language.AbsAMPL.Start mainrun channelspec coms -> prPrec i 0 (concatD [prt 0 mainrun, prt 0 channelspec, doc (showString ":"), prt 0 coms])
    Language.AbsAMPL.Start_none -> prPrec i 0 (concatD [])

instance Print Language.AbsAMPL.CHANNEL_SPEC where
  prt i e = case e of
    Language.AbsAMPL.Channel_spec pidents1 pidents2 -> prPrec i 0 (concatD [doc (showString "("), doc (showString "|"), prt 0 pidents1, doc (showString "=>"), prt 0 pidents2, doc (showString ")")])

instance Print Language.AbsAMPL.COMS where
  prt i e = case e of
    Language.AbsAMPL.Prog coms -> prPrec i 0 (concatD [doc (showString "{"), prt 0 coms, doc (showString "}")])
  prtList _ [] = concatD []
  prtList _ [x] = concatD [prt 0 x]
  prtList _ (x:xs) = concatD [prt 0 x, doc (showString ","), prt 0 xs]

instance Print [Language.AbsAMPL.COM] where
  prt = prtList

instance Print Language.AbsAMPL.COM where
  prt i e = case e of
    Language.AbsAMPL.AC_ASSIGN pident com -> prPrec i 0 (concatD [prt 0 pident, doc (showString ":="), prt 0 com])
    Language.AbsAMPL.AC_STOREf store pident -> prPrec i 0 (concatD [prt 0 store, prt 0 pident])
    Language.AbsAMPL.AC_LOADf load pident -> prPrec i 0 (concatD [prt 0 load, prt 0 pident])
    Language.AbsAMPL.AC_RET ret -> prPrec i 0 (concatD [prt 0 ret])
    Language.AbsAMPL.AC_CALLf call pident pidents -> prPrec i 0 (concatD [prt 0 call, prt 0 pident, doc (showString "("), prt 0 pidents, doc (showString ")")])
    Language.AbsAMPL.AC_INT constint cinteger -> prPrec i 0 (concatD [prt 0 constint, prt 0 cinteger])
    Language.AbsAMPL.AC_CHAR constchar character -> prPrec i 0 (concatD [prt 0 constchar, prt 0 character])
    Language.AbsAMPL.AC_STRING conststring str -> prPrec i 0 (concatD [prt 0 conststring, prt 0 str])
    Language.AbsAMPL.AC_TOSTR tostr -> prPrec i 0 (concatD [prt 0 tostr])
    Language.AbsAMPL.AC_TOINT toint -> prPrec i 0 (concatD [prt 0 toint])
    Language.AbsAMPL.AC_AND and -> prPrec i 0 (concatD [prt 0 and])
    Language.AbsAMPL.AC_OR or -> prPrec i 0 (concatD [prt 0 or])
    Language.AbsAMPL.AC_APPEND append -> prPrec i 0 (concatD [prt 0 append])
    Language.AbsAMPL.AC_TRUE btrue -> prPrec i 0 (concatD [prt 0 btrue])
    Language.AbsAMPL.AC_FALSE bfalse -> prPrec i 0 (concatD [prt 0 bfalse])
    Language.AbsAMPL.AC_UNSTRING unstring -> prPrec i 0 (concatD [prt 0 unstring])
    Language.AbsAMPL.AC_LEQ leqi -> prPrec i 0 (concatD [prt 0 leqi])
    Language.AbsAMPL.AC_EQ eqi -> prPrec i 0 (concatD [prt 0 eqi])
    Language.AbsAMPL.AC_LEQC leqc -> prPrec i 0 (concatD [prt 0 leqc])
    Language.AbsAMPL.AC_EQC eqc -> prPrec i 0 (concatD [prt 0 eqc])
    Language.AbsAMPL.AC_LEQS leqs -> prPrec i 0 (concatD [prt 0 leqs])
    Language.AbsAMPL.AC_EQS eqs -> prPrec i 0 (concatD [prt 0 eqs])
    Language.AbsAMPL.AC_CONCAT concats n -> prPrec i 0 (concatD [prt 0 concats, prt 0 n])
    Language.AbsAMPL.AC_ADD add -> prPrec i 0 (concatD [prt 0 add])
    Language.AbsAMPL.AC_SUB subtract -> prPrec i 0 (concatD [prt 0 subtract])
    Language.AbsAMPL.AC_MUL mul -> prPrec i 0 (concatD [prt 0 mul])
    Language.AbsAMPL.AC_DIVQ quot -> prPrec i 0 (concatD [prt 0 quot])
    Language.AbsAMPL.AC_DIVR rem -> prPrec i 0 (concatD [prt 0 rem])
    Language.AbsAMPL.AC_CONS cons pinteger1 pinteger2 -> prPrec i 0 (concatD [prt 0 cons, doc (showString "("), prt 0 pinteger1, doc (showString ","), prt 0 pinteger2, doc (showString ")")])
    Language.AbsAMPL.AC_STRUCT uident1 uident2 -> prPrec i 0 (concatD [prt 0 uident1, doc (showString "."), prt 0 uident2])
    Language.AbsAMPL.AC_STRUCTAS uident1 uident2 pidents -> prPrec i 0 (concatD [prt 0 uident1, doc (showString "."), prt 0 uident2, doc (showString "("), prt 0 pidents, doc (showString ")")])
    Language.AbsAMPL.AC_CASEf case_ pident labelcomss -> prPrec i 0 (concatD [prt 0 case_, prt 0 pident, doc (showString "of"), doc (showString "{"), prt 0 labelcomss, doc (showString "}")])
    Language.AbsAMPL.AC_IF if_ pident coms1 coms2 -> prPrec i 0 (concatD [prt 0 if_, prt 0 pident, doc (showString "then"), prt 0 coms1, doc (showString "else"), prt 0 coms2])
    Language.AbsAMPL.AC_RECORDf rec labelcomss -> prPrec i 0 (concatD [prt 0 rec, doc (showString "of"), doc (showString "{"), prt 0 labelcomss, doc (showString "}")])
    Language.AbsAMPL.AC_DEST uident1 uident2 pident -> prPrec i 0 (concatD [prt 0 uident1, doc (showString "."), prt 0 uident2, prt 0 pident])
    Language.AbsAMPL.AC_DESTAS uident1 uident2 pidents pident -> prPrec i 0 (concatD [prt 0 uident1, doc (showString "."), prt 0 uident2, doc (showString "("), prt 0 pidents, doc (showString ")"), prt 0 pident])
    Language.AbsAMPL.AC_GETf get pident1 pident2 -> prPrec i 0 (concatD [prt 0 get, prt 0 pident1, doc (showString "on"), prt 0 pident2])
    Language.AbsAMPL.AC_HPUTf hput uident1 uident2 pident -> prPrec i 0 (concatD [prt 0 hput, prt 0 uident1, doc (showString "."), prt 0 uident2, doc (showString "on"), prt 0 pident])
    Language.AbsAMPL.AC_HCASEf hcase pident labelcomss -> prPrec i 0 (concatD [prt 0 hcase, prt 0 pident, doc (showString "of"), doc (showString "{"), prt 0 labelcomss, doc (showString "}")])
    Language.AbsAMPL.AC_PUTf put pident1 pident2 -> prPrec i 0 (concatD [prt 0 put, prt 0 pident1, doc (showString "on"), prt 0 pident2])
    Language.AbsAMPL.AC_SPLITf split pident1 pident2 pident3 -> prPrec i 0 (concatD [prt 0 split, prt 0 pident1, doc (showString "into"), prt 0 pident2, prt 0 pident3])
    Language.AbsAMPL.AC_FORKf fork pident1 pident2 pidents1 coms1 pident3 pidents2 coms2 -> prPrec i 0 (concatD [prt 0 fork, prt 0 pident1, doc (showString "as"), doc (showString "{"), prt 0 pident2, doc (showString "with"), prt 0 pidents1, doc (showString ":"), prt 0 coms1, doc (showString ";"), prt 0 pident3, doc (showString "with"), prt 0 pidents2, doc (showString ":"), prt 0 coms2, doc (showString "}")])
    Language.AbsAMPL.AC_PLUGf plug pidents1 pidents2 coms1 pidents3 coms2 -> prPrec i 0 (concatD [prt 0 plug, prt 0 pidents1, doc (showString "as"), doc (showString "{"), doc (showString "with"), doc (showString "["), prt 0 pidents2, doc (showString "]"), doc (showString ":"), prt 0 coms1, doc (showString ";"), doc (showString "with"), doc (showString "["), prt 0 pidents3, doc (showString "]"), doc (showString ":"), prt 0 coms2, doc (showString "}")])
    Language.AbsAMPL.AC_RUNf run pident pidents1 pidents2 pidents3 -> prPrec i 0 (concatD [prt 0 run, prt 0 pident, doc (showString "("), prt 0 pidents1, doc (showString "|"), prt 0 pidents2, doc (showString "=>"), prt 0 pidents3, doc (showString ")")])
    Language.AbsAMPL.AC_IDF pident1 chid pident2 -> prPrec i 0 (concatD [prt 0 pident1, prt 0 chid, prt 0 pident2])
    Language.AbsAMPL.AC_RACE race racess -> prPrec i 0 (concatD [prt 0 race, doc (showString "{"), prt 0 racess, doc (showString "}")])
    Language.AbsAMPL.AC_PROD pidents -> prPrec i 0 (concatD [doc (showString "("), prt 0 pidents, doc (showString ")")])
    Language.AbsAMPL.AC_PRODELEM pinteger pident -> prPrec i 0 (concatD [doc (showString "#"), prt 0 pinteger, doc (showString "("), prt 0 pident, doc (showString ")")])
    Language.AbsAMPL.AC_EMSG str -> prPrec i 0 (concatD [prt 0 str])
    Language.AbsAMPL.AC_CLOSEf close pident -> prPrec i 0 (concatD [prt 0 close, prt 0 pident])
    Language.AbsAMPL.AC_HALTf halt pident -> prPrec i 0 (concatD [prt 0 halt, prt 0 pident])
  prtList _ [] = concatD []
  prtList _ [x] = concatD [prt 0 x]
  prtList _ (x:xs) = concatD [prt 0 x, doc (showString ";"), prt 0 xs]

instance Print Language.AbsAMPL.LABELCOMS where
  prt i e = case e of
    Language.AbsAMPL.Labelcoms1 uident1 uident2 coms -> prPrec i 0 (concatD [prt 0 uident1, doc (showString "."), prt 0 uident2, doc (showString ":"), prt 0 coms])
    Language.AbsAMPL.Labelcoms2 uident1 uident2 pidents coms -> prPrec i 0 (concatD [prt 0 uident1, doc (showString "."), prt 0 uident2, doc (showString "("), prt 0 pidents, doc (showString ")"), doc (showString ":"), prt 0 coms])
  prtList _ [] = concatD []
  prtList _ [x] = concatD [prt 0 x]
  prtList _ (x:xs) = concatD [prt 0 x, doc (showString ";"), prt 0 xs]

instance Print [Language.AbsAMPL.COMS] where
  prt = prtList

instance Print [Language.AbsAMPL.LABELCOMS] where
  prt = prtList

instance Print Language.AbsAMPL.RACES where
  prt i e = case e of
    Language.AbsAMPL.Races pident coms -> prPrec i 0 (concatD [prt 0 pident, doc (showString "->"), prt 0 coms])
  prtList _ [] = concatD []
  prtList _ [x] = concatD [prt 0 x]
  prtList _ (x:xs) = concatD [prt 0 x, doc (showString ";"), prt 0 xs]

instance Print [Language.AbsAMPL.RACES] where
  prt = prtList

instance Print [Language.AbsAMPL.PIdent] where
  prt = prtList

instance Print Language.AbsAMPL.CInteger where
  prt i e = case e of
    Language.AbsAMPL.Positive pinteger -> prPrec i 0 (concatD [prt 0 pinteger])
    Language.AbsAMPL.Negative pinteger -> prPrec i 0 (concatD [doc (showString "-"), prt 0 pinteger])
  prtList _ [] = concatD []
  prtList _ [x] = concatD [prt 0 x]
  prtList _ (x:xs) = concatD [prt 0 x, doc (showString ","), prt 0 xs]

instance Print [Language.AbsAMPL.CInteger] where
  prt = prtList
