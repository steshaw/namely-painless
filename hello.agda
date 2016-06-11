module Hello where

open import Agda.Builtin.Unit
open import IO
open import Data.Nat
open import Data.Nat.Show

double : ℕ → ℕ
double n = n + n

prog₁ : IO ⊤
prog₁ = putStrLn (show (double 21))
