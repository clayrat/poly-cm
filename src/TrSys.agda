{-# OPTIONS --safe #-}
module TrSys where

open import Prelude

private variable
  ℓ ℓ′ ℓᵃ ℓᵇ ℓᶜ ℓˢ ℓ◃ ℓ▹ ℓ◃′ ℓ▹′ : Level
  A : 𝒰 ℓᵃ
  B : 𝒰 ℓᵇ
  C : 𝒰 ℓᶜ
  S : 𝒰 ℓˢ

-- binary relation
-- TODO what's this in prelude?
Rel2 : 𝒰 ℓᵃ → 𝒰 ℓᵇ → (ℓ : Level) → 𝒰 (ℓᵃ ⊔ ℓᵇ ⊔ ℓsuc ℓ)
Rel2 A B ℓ = A → B → 𝒰 ℓ

-- transition system

record TS {ℓᵃ ℓᵇ}
          (A : 𝒰 ℓᵃ) (B : 𝒰 ℓᵇ) (ℓ : Level) : 𝒰 (ℓᵃ ⊔ ℓᵇ ⊔ ℓsuc ℓ) where
  field
    tr : A → 𝒰 ℓ
    nx : {a : A} → tr a → B

open TS public

trseq : TS A B ℓ → TS B C ℓ′ → TS A C (ℓ ⊔ ℓ′)
trseq ab bc .tr a         = Σ[ ta ꞉ ab .tr a ] bc .tr (ab .nx ta)
trseq ab bc .nx (ta , bt) = bc .nx {a = ab .nx ta} bt

-- TODO ∙
