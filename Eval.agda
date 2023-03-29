module Eval where

open import Data.Nat
open import Data.Sum
open import Data.Product

open import Base
open import Semantics
open import Progress
open import Preservation

data Finished : Set where
  done : ∀ {t} → value {∅} t → Finished
  out-of-gas : Finished

eval : ∀ {T} → ℕ → (t : CTerm) → ∅ ⊢ t ∈ T → Finished
eval zero t Ht = out-of-gas
eval {T} (suc gas) t Ht with progress T t Ht
... | inj₁ val-t = done val-t
... | inj₂ (t' , t~>t') = eval gas t' (preservation Ht t~>t')
