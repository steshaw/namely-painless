module Section8-de-Bruijn-indices where

module Bare where
  open import Data.Nat

  data Tmᵇ : Set where
    V   : (x : ℕ)     → Tmᵇ
    _·_ : (t u : Tmᵇ) → Tmᵇ
    Lam : (t : Tmᵇ)   → Tmᵇ
    Let : (t u : Tmᵇ) → Tmᵇ

  appTmᵇ : Tmᵇ
  appTmᵇ = Lam (Lam (V 1 · V 0))

module NestedDataType_or_Maybe where

  open import Data.Maybe
  open import Data.Empty using (⊥)

  data Tmᵐ (A : Set) : Set where
    V : (x : A) → Tmᵐ A
    _·_ : (t u : Tmᵐ A) → Tmᵐ A
    Lam : (t : Tmᵐ (Maybe A)) → Tmᵐ A
    Let : (t : Tmᵐ A) (u : Tmᵐ (Maybe A)) -> Tmᵐ A

  appTmᵐ : Tmᵐ ⊥
  appTmᵐ = Lam (Lam (V (just nothing) · V nothing))

module Fin where

  open import Data.Fin
  open import Data.Nat using (zero; suc)

  data Tmᶠ n : Set where
    V : (x : Fin n) → Tmᶠ n
    _·_ : (t u : Tmᶠ n) → Tmᶠ n
    Lam : (t : Tmᶠ (suc n)) → Tmᶠ n
    Let : (t : Tmᶠ n) (u : Tmᶠ (suc n)) → Tmᶠ n

  appTmᶠ : Tmᶠ 0
  appTmᶠ = Lam (Lam (V (suc zero) · V zero))
