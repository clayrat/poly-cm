{-# OPTIONS --safe #-}
module Cover where

open import Prelude
open import TrSys
open import IntSys

private variable
  ℓ ℓ′ ℓᵃ ℓᵇ ℓᶜ ℓᵈ ℓ◃ ℓ▹ ℓ◃′ ℓ▹′ : Level
  A : 𝒰 ℓᵃ
  B : 𝒰 ℓᵇ
  C : 𝒰 ℓᶜ
  D : 𝒰 ℓᵈ

module ISCover (w : IFace A ℓ◃ ℓ▹) where

  -- least infinitary preorder satisfying U
  data _◁is_ {ℓ} (a : A) (U : A → 𝒰 ℓ) : 𝒰 (ℓ ⊔ ℓ◃ ⊔ ℓ▹) where
    -- aka reflexivity
    dir    : U a → a ◁is U
    -- aka infinity
    branch : (b : w .com a) → ((c : w. res b) → w .out b c ◁is U) → a ◁is U
    squash : (p q : a ◁is U) → p ＝ q

  trans◁ : {a : A} {U : A → 𝒰 ℓ} {V : A → 𝒰 ℓ′}
        → a ◁is U
        → (∀ {b} → U b → b ◁is V)
        → a ◁is V
  trans◁ (dir a∈u)      bv = bv a∈u
  trans◁ (branch wa k)  bv = branch wa λ c → trans◁ {a = w .out wa c} (k c) bv
  trans◁ (squash x y i) bv = squash (trans◁ x bv) (trans◁ y bv) i

  -- closure (infinitary preorder) properties
  
  refl◁ : {U : A → 𝒰 ℓ}
       → U ⊆ (_◁is U)
  refl◁ = dir

  mono◁ : {U : A → 𝒰 ℓ} {V : A → 𝒰 ℓ′}
        → U ⊆ V → (_◁is U) ⊆ (_◁is V)
  mono◁ uv au = trans◁ au (refl◁ ∘ uv)

  idem◁ : {U : A → 𝒰 ℓ}
        → (_◁is (_◁is U)) ⊆ (_◁is U)
  idem◁ uux = trans◁ uux id

  idem◁≈ : {U : A → 𝒰 ℓ}
         → (_◁is (_◁is U)) ≈ (_◁is U)
  idem◁≈ = idem◁ , refl◁

  -- TODO syntax
  inter◁ : {U : A → 𝒰 ℓ} {V : A → 𝒰 ℓ′}
         → (_◁is (λ a → U a × V a)) ⊆ (λ a → (a ◁is U) × (a ◁is V))
  inter◁ (dir (ux , vx)) = (dir ux) , (dir vx)
  inter◁ (branch wx k) = branch wx (λ c → inter◁ (k c) .fst) , branch wx λ c → inter◁ (k c) .snd
  inter◁ (squash x y i) = squash (inter◁ x .fst) (inter◁ y .fst) i , squash (inter◁ x .snd) (inter◁ y .snd) i
  
  -- saturated subsets

  Sat◁ : (A → 𝒰 ℓ) → ((A → 𝒰 ℓ) → 𝒰 (level-of-type A ⊔ ℓ◃ ⊔ ℓ▹ ⊔ ℓ))
  Sat◁ X U = U ⊆ X × ((_◁is U) ⊆ U)  -- TODO is this good?

