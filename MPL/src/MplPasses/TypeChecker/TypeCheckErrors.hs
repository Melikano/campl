{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
module MplPasses.TypeChecker.TypeCheckErrors where

import Optics

import MplAST.MplCore
import MplAST.MplParsed
import MplAST.MplRenamed
import MplAST.MplTypeChecked

import Data.Foldable
import Data.Function
import Data.List

import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty as NE
import Data.Bool
import Control.Arrow

data TypeCheckErrors = 
    SeqTypeClauseArgsMustContainTheSameTypeVariables 
        [NonEmpty [IdentR]]
        -- list of equivalence classes of the arguments on (==)
    | ConcTypeClauseArgsMustContainTheSameTypeVariables 
        [NonEmpty ([IdentR], [IdentR])]
        -- list of equivalence classes of the arguments on (==)
        --
    | ExpectedStateVarButGot IdentR IdentR 
        -- expected, actual
    | ExpectedOppositePolarity (IdentR, Polarity)
        -- channel, polarity of channel. 

    | HCaseExpectedInputPolarityChToHaveProtocolButGotCoprotocol 
        -- channel, phrase ident
        IdentR IdentR
    | HCaseExpectedOutputPolarityChToHaveCoprotocolButGotProtocol 
        -- channel, phrase ident
        IdentR IdentR

    | HPutExpectedInputPolarityChToHaveCoprotocolButGotProtocol
        IdentR IdentR
    | HPutExpectedOutputPolarityChToHaveProtocolButGotCoprotocol
        IdentR IdentR

    | ForkExpectedDisjointChannelsButHasSharedChannels [IdentR]

    | IllegalLastCommand KeyWordNameOcc 
    | IllegalNonLastCommand KeyWordNameOcc 

  deriving Show

$(makeClassyPrisms ''TypeCheckErrors)

class TypeClauseSpineSameVarError (t :: ObjectDefnTag) where
    typeClauseSpineSameVarError :: 
        AsTypeCheckErrors e => 
        MplTypeClauseSpine MplRenamed t -> 
        [e]
{-

instance TypeClauseSpineSameVarError (SeqObjTag t) where
    typeClauseSpineSameVarError spine = bool [] 
        [_SeqTypeClauseArgsMustContainTheSameTypeVariables # eqclasses]
        shoulderror
      where
        eqclasses :: [NonEmpty [IdentR]]
        eqclasses = NE.group 
            $ fmap (fmap (view identRIdentP) <<< view typeClauseArgs) 
            $ spine ^. typeClauseSpineClauses 

        shoulderror = length eqclasses >= 2

instance TypeClauseSpineSameVarError (ConcObjTag t) where
    typeClauseSpineSameVarError spine = bool [] 
        [_ConcTypeClauseArgsMustContainTheSameTypeVariables # eqclasses]
        shoulderror
      where
        eqclasses :: [NonEmpty ([IdentR], [IdentR])]
        eqclasses = NE.group 
            $ fmap (fmap (view identRIdentP) *** fmap (view identRIdentP)
                <<< view typeClauseArgs) 
            $ spine ^. typeClauseSpineClauses 

        shoulderror = length eqclasses >= 2

hCaseError :: 
    AsTypeCheckErrors e =>
    (IdentR, Polarity) ->
    (IdentR, ConcObjDefnTag) ->
    [e]
hCaseError (ch, Input) (ident, CoprotocolDefnTag) = 
    [_HCaseExpectedInputPolarityChToHaveProtocolButGotCoprotocol # (ch,ident) ]
hCaseError (ch, Output) (ident, ProtocolDefnTag) = 
    [_HCaseExpectedOutputPolarityChToHaveCoprotocolButGotProtocol # (ch,ident) ]
hCaseError _ _ = []

hPutError :: 
    AsTypeCheckErrors e =>
    (IdentR, Polarity) ->
    (IdentR, ConcObjDefnTag) ->
    [e]
hPutError (ch, Input) (ident, ProtocolDefnTag) = 
    [ _HPutExpectedInputPolarityChToHaveCoprotocolButGotProtocol # (ch,ident) ]
hPutError (ch, Output) (ident, CoprotocolDefnTag) = 
    [_HPutExpectedOutputPolarityChToHaveProtocolButGotCoprotocol # (ch,ident) ]
hPutError _ _ = []


forkExpectedDisjointChannelsButHasSharedChannels ::
    AsTypeCheckErrors e =>
    [IdentR] ->
    [IdentR] ->
    [e]
forkExpectedDisjointChannelsButHasSharedChannels a b =
    bool [_ForkExpectedDisjointChannelsButHasSharedChannels # common ] [] (null common)
  where
    common = a `intersect` b


expectedInputPolarity ::
    AsTypeCheckErrors e =>
    (IdentR, SymEntry Polarity) -> 
    [e]
expectedInputPolarity ch@(ident, SymEntry _ Output) = [_ExpectedOppositePolarity # (ident, Output)]
expectedInputPolarity _ = []

expectedOutputPolarity ::
    AsTypeCheckErrors e =>
    (IdentR, SymEntry Polarity) -> 
    [e]
expectedOutputPolarity ch@(ident, SymEntry _ Input) = [_ExpectedOppositePolarity # (ident, Input)]
expectedOutputPolarity _ = []

-}
