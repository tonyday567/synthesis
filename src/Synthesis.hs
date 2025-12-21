module Synthesis where

import Data.Map.Strict qualified as Map
import Data.Bool hiding (not)
import Prelude as P
import NumHask.Prelude qualified as N
import NumHask.Space qualified as N
import Control.Category ((>>>))
import Data.Function
import Data.Maybe
import Data.Bool
import Data.List qualified as List
import Control.Monad
import Data.Bifunctor
import Data.Text qualified as T

-- prettyprinter (dev help)
import Prettyprinter

-- common chart-svg imports
import Chart hiding (abs)
import Prettychart
import Chart.Examples
import Optics.Core hiding ((|>),(<|))
import Control.Lens qualified as Lens
import Data.Data.Lens qualified as Lens

-- random variates
import System.Random.Stateful
import System.Random.MWC
import System.Random.MWC.Distributions

-- dev helpers
import Perf
import Flow hiding (apply)
import Data.FormatN
import Data.Mealy
import Data.Mealy.Simulate


-- | Tokens are operators but using this as a name tends to be cliche and can get confusing. We name the sumtype then as the glyph aspect of an operator.
data Token
  = -- Value token
    Val Double
  | -- Variables
    Var String
  | -- Constants
    Pi
  | Infinity
  | E
  | Zero
  | One
  | -- Monadic _ Pervasive
    Not
  | Sign
  | Negate
  | Abs
  | Sqrt
  | Sine
  | Floor
  | Ceiling
  | Round
  | -- Dyadic _ Pervasive
    Equals
  | NotEquals
  | LessThan
  | LessOrEqual
  | GreaterThan
  | GreaterOrEqual
  | Add
  | Subtract
  | Multiply
  | Divide
  | Modulus
  | Power
  | Logarithm
  | Minimum
  | Maximum
  | Atangent
  | -- Stack
    Identity
  | Pop
  | Duplicate
  | Flip
  | Over
  deriving (Eq, Ord, Show)

data TokenDeets = TokenDeets {glyph :: Token, symbol :: String, glyphCategory :: TokenCategory}

data TokenCategory = StackGC | ConstantGC | OperatorGC InputArity OutputArity Action | ModifierGC Modifier deriving (Eq, Show)

data InputArity = Monadic | Dyadic deriving (Eq, Show)

data OutputArity = NoOutput | SingleOutput | DoubleOutput deriving (Eq, Show)

data Action = Pervasive | ArrayAction deriving (Eq, Show)

data Reducing = Reducing | NotReducing deriving (Eq, Show)

data Modifier = Iterating | Aggregating | Inversion | OtherModifier deriving (Eq, Show)

glyphM :: Map.Map Token TokenDeets
glyphM = Map.fromList $ zip (fmap glyph glyphs) glyphs

glyphs :: [TokenDeets]
glyphs =
  [ -- ConstantGC
    TokenDeets Pi "π" ConstantGC,
    TokenDeets Infinity "∞" ConstantGC,
    TokenDeets E "e" ConstantGC,
    TokenDeets Zero "0" ConstantGC,
    TokenDeets One "1" ConstantGC,
    -- OpertorGC Monadic _ Pervasive
    TokenDeets Not "¬" (OperatorGC Monadic SingleOutput Pervasive),
    TokenDeets Sign "±" (OperatorGC Monadic SingleOutput Pervasive),
    TokenDeets Negate "¯" (OperatorGC Monadic SingleOutput Pervasive),
    TokenDeets Abs "⌵" (OperatorGC Monadic SingleOutput Pervasive),
    TokenDeets Sqrt "√" (OperatorGC Monadic SingleOutput Pervasive),
    TokenDeets Sine "○" (OperatorGC Monadic SingleOutput Pervasive),
    TokenDeets Floor "⌊" (OperatorGC Monadic SingleOutput Pervasive),
    TokenDeets Ceiling "⌈" (OperatorGC Monadic SingleOutput Pervasive),
    TokenDeets Round "⁅" (OperatorGC Monadic SingleOutput Pervasive),
    -- OperatorGCC Dyadic _ Pervasive
    TokenDeets Equals "=" (OperatorGC Dyadic SingleOutput Pervasive),
    TokenDeets NotEquals "≠" (OperatorGC Dyadic SingleOutput Pervasive),
    TokenDeets LessThan "&lt;" (OperatorGC Dyadic SingleOutput Pervasive),
    TokenDeets LessOrEqual "≤" (OperatorGC Dyadic SingleOutput Pervasive),
    TokenDeets GreaterThan "&gt;" (OperatorGC Dyadic SingleOutput Pervasive),
    TokenDeets GreaterOrEqual "≥" (OperatorGC Dyadic SingleOutput Pervasive),
    TokenDeets Add "+" (OperatorGC Dyadic SingleOutput Pervasive),
    TokenDeets Subtract "-" (OperatorGC Dyadic SingleOutput Pervasive),
    TokenDeets Multiply "×" (OperatorGC Dyadic SingleOutput Pervasive),
    TokenDeets Divide "÷" (OperatorGC Dyadic SingleOutput Pervasive),
    TokenDeets Modulus "◿" (OperatorGC Dyadic SingleOutput Pervasive),
    TokenDeets Power "ⁿ" (OperatorGC Dyadic SingleOutput Pervasive),
    TokenDeets Logarithm "ₙ" (OperatorGC Dyadic SingleOutput Pervasive),
    TokenDeets Minimum "↧" (OperatorGC Dyadic SingleOutput Pervasive),
    TokenDeets Maximum "↥" (OperatorGC Dyadic SingleOutput Pervasive),
    TokenDeets Atangent "∠" (OperatorGC Dyadic SingleOutput Pervasive),
    TokenDeets Identity "∘" StackGC,
    TokenDeets Duplicate "." StackGC,
    TokenDeets Over "," StackGC,
    TokenDeets Flip "∶" StackGC,
    TokenDeets Pop "◌" StackGC
  ]

isOperator :: Token -> Bool
isOperator g = case fmap glyphCategory (Map.lookup g glyphM) of
  (Just (OperatorGC {})) -> True
  (Just ConstantGC) -> True
  _ -> False

isNonadicOp :: Token -> Bool
isNonadicOp g = Just ConstantGC == fmap glyphCategory (Map.lookup g glyphM)

isMonadicOp :: Token -> Bool
isMonadicOp g = case fmap glyphCategory (Map.lookup g glyphM) of
  (Just (OperatorGC Monadic _ _)) -> True
  _ -> False

isDyadicOp :: Token -> Bool
isDyadicOp g = case fmap glyphCategory (Map.lookup g glyphM) of
  (Just (OperatorGC Dyadic _ _)) -> True
  _ -> False

isStackOp :: Token -> Bool
isStackOp g = case fmap glyphCategory (Map.lookup g glyphM) of
  (Just StackGC) -> True
  _ -> False

isVal :: Token -> Bool
isVal (Val _) = True
isVal _ = False

isVar :: Token -> Bool
isVar (Var _) = True
isVar _ = False

-- * Application
sig :: Bool -> Double
sig = bool 0 1


apply1 :: Token -> (Double -> Double) -> Stack -> Stack
apply1 _ f (Stack ((Val v):xs)) = Stack (Val (f v):xs)
apply1 t _ s@(Stack ((Var _):_)) = push t s
apply1 _ _ _ = error "NotAValVar"

apply2 :: Token -> (Double -> Double -> Double) -> Stack -> Stack
apply2 _ f (Stack ((Val v):(Val v'):xs)) = Stack (Val (f v v'):xs)
apply2 t _ s@(Stack ((Var _):_)) = push t s
apply2 _ _ _ = error "NotAValVar"

-- | Applies operators to the stack, resolving values
applyOps :: Token -> Stack -> Stack
applyOps (Val v) s = push (Val v) s
applyOps (Var v) s = push (Var v) s
applyOps Identity (Stack (x : xs)) = Stack (x : xs)
applyOps Duplicate (Stack (x : xs)) = Stack (x : x : xs)
applyOps Over (Stack (x : y : xs)) = Stack (y : x : y : xs)
applyOps Flip (Stack (x : y : xs)) = Stack (y : x : xs)
applyOps Pop (Stack (_ : xs)) = Stack xs
applyOps Pi s = push (Val pi) s
applyOps Infinity s = push (Val (1 / 0)) s
applyOps Zero s = push (Val 0) s
applyOps One s = push (Val 1) s
applyOps Not s = apply1 Not (1 -) s
applyOps Sign s = apply1 Sign signum s
applyOps Negate s = apply1 Negate negate s
applyOps Abs s = apply1 Abs abs s
applyOps Sqrt s = apply1 Sqrt sqrt s
applyOps Equals s = apply2 Equals (\x y -> sig (x == y)) s
applyOps NotEquals s = apply2 NotEquals (\x y -> sig (x /= y)) s
applyOps LessThan s = apply2 LessThan (\x y -> sig (x < y)) s
applyOps LessOrEqual s = apply2 LessOrEqual (\x y -> sig (x <= y)) s
applyOps GreaterThan s = apply2 GreaterThan (\x y -> sig (x > y)) s
applyOps GreaterOrEqual s = apply2 GreaterOrEqual (\x y -> sig (x >= y)) s
applyOps Add s = apply2 Add (+) s
applyOps Subtract s = apply2 Subtract (-) s
applyOps Multiply s = apply2 Multiply (*) s
applyOps Divide s = apply2 Divide (/) s
applyOps Modulus s = apply2 Modulus modF s
applyOps Power s = apply2 Power (**) s
-- note flip
applyOps Logarithm s = apply2 Logarithm (flip logBase) s
applyOps Minimum s = apply2 Minimum min s
applyOps Maximum s = apply2 Maximum max s
applyOps Atangent s = apply2 Atangent atan2 s
applyOps _ _ = error "nyi"

modF :: Double -> Double -> Double
modF n d
  | d == 1/0 = n
  | d == 0 = 0/0
  | P.True = n - d * fromIntegral @Int (floor (n / d))

newtype Stack
  = Stack { startingTokens :: [Token]}
  deriving (Show, Eq)

pushTo :: Stack -> Token -> Stack
pushTo (Stack rs) x = Stack (x:rs)

push :: Token -> Stack -> Stack
push x (Stack rs) = Stack (x:rs)

apply :: Token -> Stack -> Stack
apply g s
  | isVal g || isVar g = push g s
  | isStackOp g = applyOps g s
  | isNonadicOp g = applyOps g s
  | isMonadicOp g = case s of
      (Stack []) -> error "EmptyStack1"
      _ -> applyOps g s
  | isDyadicOp g = case s of
      (Stack []) -> error "EmptyStack1"
      (Stack [_]) -> error "EmptyStack2"
      _ -> applyOps g s
  | otherwise = error "ApplyNonOperator"

eval :: Foldable t => t Token -> Stack -> Stack
eval gs s = foldr apply s gs

eval0 :: Foldable t => t Token -> Stack
eval0 gs = eval gs (Stack [])

