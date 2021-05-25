{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
module MplPasses.PatternCompiler.PatternCompileErrors where

import Optics

import MplAST.MplCore
import MplAST.MplParsed
import MplAST.MplRenamed
import MplAST.MplTypeChecked
import MplAST.MplPatternCompiled


data PatternCompileErrors 
    = NonExhaustiveFunPatt IdentT 
    | NonExhaustiveCasePatt  
    | NonExhaustiveSwitch  

    | NonExhaustiveRecordPatt IdentT
    | ExpectedVariablePatternButGot (MplPattern MplTypeChecked)
  deriving Show

data IdentPattern 
    = MorphismIdent IdentT
    | KeywordIdent NameOcc
  deriving Show 


$(makeClassyPrisms ''PatternCompileErrors)
