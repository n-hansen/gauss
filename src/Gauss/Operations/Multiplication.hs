module Gauss.Operations.Multiplication where

import           Gauss.Operations.Class
import qualified Gauss.Types.Int        as Int
import qualified Gauss.Types.Integer    as Integer

import           ClassyPrelude


data Multiplication = Multiplication
                    deriving (Show, Eq)

instance Operation Multiplication (Int,Int) where
  type Codomain Multiplication (Int,Int) = Int
  evaluate _ = uncurry Int.multiply

instance Operation Multiplication (Integer,Integer) where
  type Codomain Multiplication (Integer,Integer)= Integer
  evaluate _ = uncurry Integer.multiply