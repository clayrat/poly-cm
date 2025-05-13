{-# OPTIONS --safe #-}
module Lens where

open import Prelude
open import Polynomial

record Lens {ℓ¹ ℓ² ℓ³ ℓ⁴ : Level} (from : Polynomial ℓ¹ ℓ²) (to : Polynomial ℓ³ ℓ⁴) : 𝒰 (ℓ¹ ⊔ ℓ² ⊔ ℓ³ ⊔ ℓ⁴) where
  constructor _⇆_
  field
    mpos : pos from → pos to
    mdir : (fp : pos from) → dir to (mpos fp) → dir from fp

open Lens public

id-lens : {ℓ¹ ℓ² : Level} {A : Polynomial ℓ¹ ℓ²} → Lens A A
id-lens = id ⇆ λ _ → id

_∘ₚ_ : {ℓ¹ ℓ² ℓ³ ℓ⁴ ℓ⁵ ℓ⁶ : Level} {A : Polynomial ℓ¹ ℓ²} {B : Polynomial ℓ³ ℓ⁴} {C : Polynomial ℓ⁵ ℓ⁶}
     → Lens B C → Lens A B → Lens A C
(f ⇆ f♯) ∘ₚ (g ⇆ g♯) = (f ∘ g) ⇆ (λ i → g♯ i ∘ f♯ (g i))
infixl 25 _∘ₚ_

