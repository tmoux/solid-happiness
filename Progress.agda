module Progress where

open import Data.Sum
open import Data.Product

open import Base
open import Subst
open import Semantics

progress : ∀ T t →
  ⊢ t ∈ T →
  value t ⊎ (∃[ t' ] (t ~> t'))
progress T (f $ x) (t-app f∈S⇒T x∈S) with (progress (_ ⇒ T) f f∈S⇒T)
... | inj₂ (f' , f~>f') = inj₂ (f' $ x , step-app1 f~>f')
... | inj₁ (val-lambda t) with (progress _ x x∈S)
... | inj₁ val-x = inj₂ (t [ x ] , step-lambda val-x)
... | inj₂ (x' , x~>x') = inj₂ ((f $ x') , step-app2 (val-lambda t) x~>x')
progress .(_ ⇒ _) (ƛ t) (t-lambda p) = inj₁ (val-lambda t)
