{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedLabels  #-}

module Dev where

import           Universum    hiding (Either (..), Identity, reduce, show)

import qualified Data.HashSet as HS
import           Data.Vector  (Vector)
import           GHC.TypeLits
import           Text.Printf
import           Text.Show


type Scalar = Double

newtype Tensor (dims :: [Int]) = Tensor (Vector Scalar)

data Expression = Variable String
                | Constant Scalar
                | Application Operation [Expression]
                deriving (Eq, Generic)

instance Hashable Expression

instance Show Expression where
  show (Variable v) = v
  show (Constant c) =
    if fromIntegral (truncate c) == c
      then show $ truncate c
      else show c
  show (Application op args) =
    let opSym = show op
        inner = case operatorFixity op of
          Prefix  -> opSym <> " " <> intercalate " " (map show args)
          Infix   -> intercalate opSym $ map show args
          Postfix -> (intercalate " " $ map show args) <> opSym
     in printf "(%s)" inner

instance (KnownSymbol symbol) => IsLabel symbol Expression where
  fromLabel = Variable (symbolVal p)
    where p :: Proxy symbol
          p = Proxy

instance Num Expression where
  x + y = Application Addition [x,y]
  x * y = Application Multiplication [x,y]
  x - y = Application Addition [x, negate y]
  negate x = Application (InverseUnder Addition) [x]
  fromInteger = Constant . fromInteger

instance Fractional Expression where
  x / y = Application Multiplication [x, recip y]
  recip x = Application (InverseUnder Multiplication) [x]
  fromRational = Constant . fromRational

isConstant :: Expression -> Bool
isConstant (Constant _) = True
isConstant _            = False

value :: Expression -> Maybe Scalar
value (Constant c) = Just c
value _            = Nothing

data Operation = Addition
               | Multiplication
               | InverseUnder Operation
               | Exponentiation
               | Ln
               deriving (Eq, Generic)

instance Hashable Operation

instance Show Operation where
  show = \case
           Addition                    -> "+"
           Multiplication              -> " "
           InverseUnder Addition       -> "-"
           InverseUnder Multiplication -> "^(-1)"
           Exponentiation              -> "^"
           Ln                          -> "ln"
           InverseUnder op             -> error . toText $ "Undefined operation: inverse under " <> show op

data Fixity = Prefix
            | Infix
            | Postfix
            deriving (Show, Eq, Generic)

operatorFixity :: Operation -> Fixity
operatorFixity op
  | op `elem` [Addition, Multiplication, Exponentiation] = Infix
  | op `elem` [InverseUnder Addition, Ln] = Prefix
  | op `elem` [InverseUnder Multiplication] = Postfix
  | otherwise = error . toText $ "Undefined fixity for operation: " <> show op

data Property = Associative { getSide :: Side }
              | Commutative
              | Distributive { getOperation :: Operation }
              | Closure
              | Identity { getSide :: Side, getUnit :: Expression }
              | Inverses
              | Computable { getFunction :: [Scalar] -> Scalar }
              deriving (Eq)

instance Eq (a -> b) where
  _ == _ = True

data Side = Left
          | Right
          deriving (Show, Eq)

data Structure = Structure { operation :: Operation, properties :: [Property] }

instance Eq Structure where
  (Structure a _) == (Structure b _) = a == b

structures :: [Structure]
structures =
  [ Structure Addition [ Associative Left, Associative Right
                       , Commutative
                       , Closure
                       , Identity Left 0, Identity Right 0
                       , Inverses
                       , Computable sum
                       ]
  , Structure Multiplication [ Associative Left, Associative Right
                             , Commutative
                             , Distributive Addition
                             , Closure
                             , Identity Left 1, Identity Right 1
                             , Inverses
                             , Computable product
                             ]
  ]

structureByOp :: Operation -> Maybe Structure
structureByOp op = find (\(Structure op' _) -> op == op') structures

unit, leftUnit, rightUnit :: Structure -> Maybe Expression
unit = liftA2 (<|>) leftUnit rightUnit -- NB: if both left and right units exist, they must be identical
leftUnit =
  map getUnit
  . find (\case
            Identity Left _ -> True
            _ -> False)
  . properties
rightUnit =
  map getUnit
  . find (\case
            Identity Right _ -> True
            _ -> False)
  . properties

inverse :: Structure -> Maybe Operation
inverse Structure{operation,properties} =
  guard (Inverses `elem` properties) *> Just (InverseUnder operation)

computable :: Structure -> Maybe ([Scalar] -> Scalar)
computable =
  map getFunction
  . find (\case
            Computable _ -> True
            _ -> False)
  . properties

type RewriteRule = Expression -> [Expression]

doNothing, removeLeftUnitApplication, removeRightUnitApplication, removeUnitApplication, removeDoubleInverse, removeInverseApplication, commuteArguments, applyOperation, reassociateLeft, reassociateRight :: RewriteRule

doNothing = pure

removeLeftUnitApplication (Application op [unit', val]) = maybeToList $ do
  unit <- leftUnit =<< structureByOp op
  guard $ unit == unit'
  pure val
removeLeftUnitApplication _ = fail "rule not applicable"

removeRightUnitApplication (Application op [val, unit']) = maybeToList $ do
  unit <- rightUnit =<< structureByOp op
  guard $ unit == unit'
  pure val
removeRightUnitApplication _ = fail "rule not applicable"

removeUnitApplication = liftA2 (<|>) removeLeftUnitApplication removeRightUnitApplication

removeDoubleInverse (Application (InverseUnder opO) [Application (InverseUnder opI) [val]]) = maybeToList $ do
  guard $ opO == opI
  pure val
removeDoubleInverse _ = fail "rule not applicable"

removeInverseApplication (Application opO [Application (InverseUnder opI) [x], y]) = maybeToList $ do
  unit <- unit =<< structureByOp opO
  guard $ opO == opI
  guard $ x == y
  pure unit
removeInverseApplication (Application opO [x, Application (InverseUnder opI) [y]]) = maybeToList $ do
  unit <- unit =<< structureByOp opO
  guard $ opO == opI
  guard $ x == y
  pure unit
removeInverseApplication _ = fail "rule not applicable"

commuteArguments (Application op args) = do
  -- Structure _ properties <-
  guard $ elem Commutative . maybeToMonoid . map properties $ structureByOp op
  args' <- permutations args
  pure $ Application op args'
commuteArguments _ = fail "rule not applicable"

applyOperation (Application op args) = maybeToList $ do
  guard $ all isConstant args
  f <- computable =<< structureByOp op
  pure . Constant . f . mapMaybe value $ args
applyOperation _                     = fail "rule not applicable"

reassociateLeft (Application op [Application op' [x,y], z]) = maybeToList $ do
  guard $ op == op'
  guard $ elem (Associative Left) . maybeToMonoid . map properties $ structureByOp op
  pure $ Application op [x, Application op' [y,z]]
reassociateLeft _ = fail "rule not applicable"

reassociateRight (Application op [x, Application op' [y,z]]) = maybeToList $ do
  guard $ op == op'
  guard $ elem (Associative Right) . maybeToMonoid . map properties $ structureByOp op
  pure $ Application op [Application op' [x,y], z]
reassociateRight _ = fail "rule not applicable"

rules :: [RewriteRule]
rules = [ doNothing
        , removeLeftUnitApplication
        , removeRightUnitApplication
        , removeDoubleInverse
        , removeInverseApplication
        , commuteArguments
        , applyOperation
        , reassociateLeft
        , reassociateRight
        ]

reductions :: Expression -> HashSet Expression
reductions expr = executingState mempty $ go expr
  where go :: Expression -> State (HashSet Expression) ()
        go (Application op args) = do
          seenRewrites <- get
          let newRewrites = HS.fromList $ do
                args' <- traverse (HS.toList . reductions) args
                rule <- rules
                result <- rule $ Application op args'
                pure result
              frontier = newRewrites `HS.difference` seenRewrites
          modify $ HS.union newRewrites
          traverse_ go frontier
        go expr = put $ one expr

nodes :: Expression -> [Expression]
nodes c@(Constant _)         = [c]
nodes v@(Variable _)         = [v]
nodes a@(Application _ args) = a : concatMap nodes args

score :: Expression -> Int
score (Constant _)         = 1
score (Variable _)         = 2
score (Application _ args) = 5 + (sum . map score $ args)

reduce :: Expression -> Expression
reduce = minimumBy (compare `on` score) . reductions
