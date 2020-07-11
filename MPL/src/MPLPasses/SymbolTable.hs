{-# LANGUAGE TemplateHaskell #-}
module MPLPasses.SymbolTable where

import MPLAST.MPLProgI
import MPLAST.MPLASTCore

import Optics
import Optics.State.Operators

import Control.Monad.State
import Control.Monad.Except

import Data.Map ( Map (..) )
import qualified Data.Map as Map

type SymbolTable = [(String, SymEntry SymInfo)]


data SymEntry info = SymEntry {
    _symEntryUniqueTag :: UniqueTag
    , _symEntryInfo :: info
}  deriving Show


data SymInfo = 
    SymSeqClause (TypeClauseNode TaggedBnfcIdent)
    | SymConcClause (TypeClauseNode TaggedBnfcIdent)

$(makePrisms ''SymEntry)
$(makeLenses ''SymEntry)


{-
data SymEntry =
    SymTypeArgVar
    | SymTypeStateVar (SeqClauseG TaggedBnfcIdent)
    | SymSeqClause (SeqClauseG TaggedBnfcIdent)

{-
withScope  :: 
    ( MonadState c m
    , HasSymbolTableState c ) => 
    SymEntry ->
    m ()

insertSymbolTable :: 
    ( MonadState c m
    , HasSymbolTableState c ) => 
    SymEntry ->
    m ()
insertSymbolTable entry = do
    tag <- freshUniqueTag
    symbolTable %= Map.insert tag entry
    -}
    -}
