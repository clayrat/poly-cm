{-# OPTIONS --safe #-}
module Chart where

open import Prelude
open import Polynomial

record Chart {ℓ¹ ℓ² ℓ³ ℓ⁴ : Level} (from : Polynomial ℓ¹ ℓ²) (to : Polynomial ℓ³ ℓ⁴) : 𝒰 (ℓ¹ ⊔ ℓ² ⊔ ℓ³ ⊔ ℓ⁴) where
  constructor _⇉_
  field
    mpos : pos from → pos to
    mdir : (fp : pos from) → dir from fp → dir to (mpos fp)

open Chart public

id-chart : {ℓ¹ ℓ² : Level} {A : Polynomial ℓ¹ ℓ²} → Chart A A
id-chart = id ⇉ λ _ → id

_∘c_ : {ℓ¹ ℓ² ℓ³ ℓ⁴ ℓ⁵ ℓ⁶ : Level} {A : Polynomial ℓ¹ ℓ²} {B : Polynomial ℓ³ ℓ⁴} {C : Polynomial ℓ⁵ ℓ⁶}
     → Chart B C → Chart A B → Chart A C
(f ⇉ f♭) ∘c (g ⇉ g♭) = (f ∘ g) ⇉ (λ i → f♭ (g i) ∘ g♭ i)
infixl 25 _∘c_
