{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE QuasiQuotes #-}

module MplPasses.Renamer.RenameSpec (spec) where

import Data.Either
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NE
import Data.Maybe
import Data.Traversable
import MplAST.MplCore
import MplPasses.Assertions
import MplPasses.Env
import MplPasses.Parser.BnfcParse qualified as B
import MplPasses.Parser.Parse
import MplPasses.Parser.ParseErrors
import MplPasses.Passes
import MplPasses.PassesErrors
import MplPasses.Renamer.Rename
import MplPasses.Renamer.RenameErrors
import MplPasses.Renamer.RenameSym qualified as R
import Optics
import Test.HUnit
import Test.Hspec
import Test.QuickCheck
import Text.RawString.QQ

-- Tests for overlapping declarations and out of scope errors

spec = do
  mapM_
    (`describeValidRename` const (return ()))
    [ v1,
      v2,
      v3,
      v4,
      v5,
      v6,
      v7,
      v8,
      v9,
      v10,
      v11,
      v12,
      v13,
      v14
    ]

  mapM_
    (`describeAllErrors` ("out of scope", _MplRenameErrors % _OutOfScope))
    [ n1,
      n2,
      n3,
      n4,
      n5,
      n6,
      n7,
      n8,
      n8
    ]

-- Valid tests
----------------------------
v1 =
  [r|
proc v1 =
    | c => a -> do
        fork a as
            a -> do
                fork a as
                    a -> do
                        close a
                        halt c
                    b -> halt b
            b -> do
                halt b 
|]

v2 =
  [r|
proc v2 =
    | => a -> do
       fork a as
            a -> do
                halt a
            b -> do
                halt b 
|]

v3 =
  [r|
proc v3 =
    | => a -> do
        plug 
            => a,b -> do
                close b
                halt a
            b => a -> do
                close b
                halt a
|]

v4 =
  [r|
defn
    fun test =
        a -> hehemut(a)
    fun hehemut =
        a -> a
|]

v5 =
  [r|
codata 
    C -> App(A,B) =
        App :: A,C -> B
fun appwrapper =
    (App := f), a -> f(a)
|]

v6 =
  [r|
data
    MyData(A,B) -> C =
        MyData :: A,B -> C
fun appwrapper =
    a -> case a of
        MyData(a,b) -> a
        MyData(_,_) -> a
|]

v7 =
  [r|
data
    MyData(A,B) -> C =
        MyData :: A,B -> C

fun v7 :: B,MyData(A,A) -> A =
    b, a -> case a of
        MyData(a,b) -> a
        MyData(_,_) -> a
|]

v8 =
  [r|
data
    MyData(A,B,D) -> C =
        MyData1 :: A,B,D -> C
        MyData2 :: A,B,E -> C

    and 
    Other(A,B,D) -> E =
        Other :: A,B,C -> E
|]

v9 =
  [r|
fun testing =
    a -> testing(a)
|]

v10 =
  [r|
fun testing =
    a -> 
        let fun wow =
                b -> a
        in wow(a)
|]

v11 =
  [r|
defn 
    fun v11 =
        a -> pow(a)
where
    fun wow =
        a -> a

    fun pow =
        a -> wow(a)
|]

-- testing sequential first order type classes
v12 =
  [r|
class Eq A where
  fun eq :: A, A -> Bool

class Eq A => Ord A where
    fun gt :: A, A -> Bool
    fun lt :: A, A -> Bool

instance Ord A => Ord [A] where
    fun gt =
        x, y -> True
|]

-- testing sequential higher order type classes
v13 =
  [r|
class Functor \X -> M(X) => Monad \X -> M(X) where
  fun return :: A -> M(A)
  fun bind :: M(A), Fun(A,M(B)) -> M(B) 

instance Functor \A -> Tree(A, B) => Monad \A -> Tree(A, B) where
  fun return =
    x -> Leaf(x)
  fun bind =
    Node(x), f -> f(x)
    leaf, _ -> leaf

class Map2 \A, B -> M(A, B) where
  fun map1 :: Fun(A,C), M(A,B) -> M(C,B) 
  fun map2 :: Fun(B,C), M(A,B) -> M(A,C)

instance Map2 \A, B -> Tree(A, B) where
  fun map1 = 
    f, Node(x) -> Node(f(x))
    _, leaf -> leaf
  fun map2 =
    f, Leaf(x) -> Leaf(f(x))
    _, node -> node
|]

-- testing concurrent first order type classes
v14 =
  [r|
class Kill T where
  proc kill :: | T =>

instance Kill TopBot where
  proc kill :: | TopBot => =
    | ch => -> halt ch

instance Kill T => Kill Get(A | T) where
  proc kill :: | Get(A | T) => =
    | ch => -> do
      put a on ch
      kill( | ch => )
|]

-- Invalid tests
----------------------------
n1 =
  [r|
proc n1 =
    | => a -> do
       fork a as
            c -> do
                halt a
            b -> do
                halt b 
|]

n2 =
  [r|
proc n2 =
    | => a -> do
       fork a as
            c -> do
                halt c
            b -> do
                halt c 
|]

n3 =
  [r|
proc n3 =
    | => a -> do
        plug 
            => a,b -> do
                close b
                halt a
            b => a,c -> do
                close b
                close c
                halt a
            c => b -> do
                close b
                close a
                halt c
|]

n4 =
  [r|
fun test =
    a -> hehemut(a)

fun hehemut =
    a -> a
|]

n5 =
  [r|
fun n5 =
    a -> a
    b -> a
|]

n6 =
  [r|
data
    MyData(A,B) -> C =
        MyData1 :: A,B,D -> C
        MyData2 :: A,B,D -> C
|]

n7 =
  [r|
defn 
    fun n7 =
        a -> pow(a)
where
    fun pow =
        a -> wow(a)
    fun wow =
        a -> a
|]

n8 =
  [r|
defn 
    fun n8 =
        a -> pow(a)
where
    fun pow =
        a -> pow(a)

fun whereoutofscope =
    a -> pow(a)
|]

n9 =
  [r|
defn 
    fun n9 =
        a -> 
            let
                fun pow =
                    a,b -> a
            in pow(a)

fun testing =
    a -> pow(a)
|]
