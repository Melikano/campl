{-# LANGUAGE QuasiQuotes #-}
module MplCompile where

import Text.RawString.QQ

import MplPasses.Parser.Parse
import MplPasses.Parser.BnfcParse

parsebnfc n = runParse' <$> runBnfc n

test = [r|
data Nat(A) -> S =
    Succ :: A, S -> S
    Zero ::   -> S
data NegNat -> S =
    Pred :: S -> S
    NZero ::   -> S

codata S -> Fun(A,B) =
    App :: A, S -> B

fun myConst =
    a -> (Succ := b -> b)
|]



{-
test = [r|
defn
    -- fun myfun :: Nat(),Nat() -> Nat() =
    fun myfun :: Nat() -> Nat() =
        Succ(a) -> a

    data Nat -> S =
        Succ :: S -> S
        Zero ::   -> S

|]
-}

{-
-- add this test in later
codata S -> Potato(A) =
    Huh :: A,S -> S

fun myfun :: A,A -> A =
    Huh(a),b -> b
    -}


-- runPassesTester
--
