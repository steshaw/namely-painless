module chapter1-intro where

open import Agda.Builtin.Unit
open import IO
open import Data.Nat
open import Data.Nat.Show renaming (show to showℕ)
open import Data.String renaming (show to showString)
open import Relation.Nullary

record Show {a} (A : Set a) : Set a where
  field
    show : A → String

open Show ⦃...⦄

instance
  ShowNat : Show ℕ
  ShowNat = record { show = showℕ }

instance
  ShowString : Show String
  ShowString = record { show = showString }

double : ℕ → ℕ
double n = n + n

Interactive : Set₁
Interactive = IO ⊤

print : String → Interactive
print = putStrLn

prog₁ : Interactive
prog₁ = print (show (double 21))

_=+=_ : ℕ → ℕ → ℕ
zero =+= n = n
suc m =+= n = suc (m + n)

_×_ : ℕ → ℕ → ℕ
zero × n = zero
suc m × n = n + m * n

id : ∀{A} → A → A
id x = x

-- The function id can be used at different types
prog₃ : Interactive
prog₃ = print (id "Hello " ++ show (id 42))

data Bool : Set where
  false : Bool
  true  : Bool

not : Bool → Bool
not false = true
not true  = false

data List (A : Set) : Set where
  [] : List A
  _::_ : A → List A → List A

length : ∀{A} → List A → ℕ
length []        = zero
length (_ :: xs) = suc (length xs)

map : {A B : Set} → (A → B) → List A → List B
map f []        = []
map f (x :: xs) = f x :: map f xs

filter : {A : Set} → (A → Bool) → List A → List A
filter p [] = []
filter p (x :: xs) with p x
...                | true  = x :: filter p xs
...                | false = filter p xs


data Tree (A : Set) : Set where
  node : A → List (Tree A) → Tree A

Forest : Set → Set
Forest A = List (Tree A)

sumTree : Tree ℕ → ℕ
sumForest : Forest ℕ → ℕ

sumTree (node n forest) = n + sumForest forest

sumForest []               = 0
sumForest (tree :: forest) = sumTree tree + sumForest forest

data _≡₀_ {A : Set₀} (x : A) : A → Set₀ where
  refl₀ : x ≡₀ x

_≢₀_ : {A : Set₀} → A → A → Set₀
x ≢₀ y = ¬(x ≡₀ y)

zero≡₀zero : zero ≡₀ zero
zero≡₀zero = refl₀

{-
suc_injective : ∀ n m → suc n ≡₀ suc m → n ≡₀ m
suc_injective = 
-}

-- This is definitionally true, hence immediately provable by ref.
lemma₁ : ∀ n → (zero + n) ≡₀ n
lemma₁ n = refl₀

-- This is provable by a simple induction on n.
lemma_plus_n_zero : (n : ℕ) → (n + zero) ≡₀ n
lemma_plus_n_zero zero    = refl₀
lemma_plus_n_zero (suc n) = lemma_plus_n_zero n

_λ=₀_ : {A B : Set₀} (f g : A → B) → Set₀
f λ=₀ g = ∀ x → f x ≡₀ g x

not² : Bool → Bool
not² x = not (not x)

not²=id : not² λ=₀ id
not²=id true  = refl₀
not²=id false = refl₀
