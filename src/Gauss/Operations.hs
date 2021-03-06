{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Gauss.Operations
       ( Operation(..)

       , Addition(..)
       , Multiplication(..)
       , Subtraction(..)
       , Division(..)

       , Monoid, Ring
       ) where


import           Prelude                         hiding (Monoid)

import           Gauss.Operations.Addition
import           Gauss.Operations.Class
import           Gauss.Operations.Division
import           Gauss.Operations.Multiplication
import           Gauss.Operations.Subtraction


type Monoid (op :: *) (t :: *) = (Eq t, Operation op (t,t), Codomain op (t,t) ~ t)

type Ring (t :: *) = (Monoid Addition t, Monoid Multiplication t)
