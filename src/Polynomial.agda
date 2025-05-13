{-# OPTIONS --safe #-}
module Polynomial where

open import Prelude

record Polynomial (ℓᵖ ℓᵈ : Level) : 𝒰 (ℓsuc (ℓᵖ ⊔ ℓᵈ)) where
    constructor mkpoly
    field
      pos : 𝒰 ℓᵖ
      dir : pos → 𝒰 ℓᵈ

open Polynomial public

private variable
  ℓᵃ ℓᵇ ℓᵖ ℓᵈ : Level

𝟘 : Polynomial ℓᵖ ℓᵈ
𝟘 = mkpoly ⊥ λ ()

𝟙 : Polynomial ℓᵖ ℓᵈ
𝟙 = mkpoly ⊤ (λ _ → ⊥)

Y : Polynomial ℓᵖ ℓᵈ
Y = mkpoly ⊤ (λ _ → ⊤)

-- | p(y) = A*y^B
monomial : (A : 𝒰 ℓᵃ) (B : 𝒰 ℓᵇ) → Polynomial ℓᵃ ℓᵇ
monomial A B = mkpoly A (λ _ → B)

_y^_ = monomial
infix 50 _y^_

-- | p(y) = A
constant : (A : 𝒰 ℓᵃ) → Polynomial ℓᵃ ℓᵈ
constant A = monomial A ⊥

-- | p(y) = S*y^S
self-monomial : 𝒰 ℓᵃ → Polynomial ℓᵃ ℓᵃ
self-monomial S = monomial S S

-- | p(y) = y^S
pure-power : 𝒰 ℓᵃ → Polynomial ℓᵖ ℓᵃ
pure-power power = monomial ⊤ power

representable = pure-power

-- | p(y) = A*y
linear : 𝒰 ℓᵃ → Polynomial ℓᵃ ℓᵈ
linear A = monomial A ⊤

-- application

_⦅_⦆ : {ℓ : Level} → Polynomial ℓᵖ ℓᵈ → 𝒰 ℓ → 𝒰 (ℓᵖ ⊔ ℓᵈ ⊔ ℓ)
mkpoly p d ⦅ Y ⦆ = Σ[ x ꞉ p ] (d x → Y)
infixl 30 _⦅_⦆

ap-poly : {ℓᵃ ℓᵇ : Level} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ}
        → (p : Polynomial ℓᵖ ℓᵈ) → (A → B) → p ⦅ A ⦆ → p ⦅ B ⦆
ap-poly (mkpoly p d) f (x , g) = x , f ∘ g
