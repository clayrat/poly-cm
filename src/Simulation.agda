{-# OPTIONS --safe #-}
module Simulation where

open import Prelude

open import TrSys
open import IntSys

private variable
  ℓ ℓ′ ℓᵃ ℓᵇ ℓᶜ ℓᵈ ℓ◃ ℓ▹ ℓ◃′ ℓ▹′ : Level
  A : 𝒰 ℓᵃ
  B : 𝒰 ℓᵇ
  C : 𝒰 ℓᶜ
  D : 𝒰 ℓᵈ

-- relation transformer

RT : IS A B ℓ◃ ℓ▹ → IS C D ℓ◃′ ℓ▹′ → Rel2 B D ℓ → Rel2 A C (ℓ◃ ⊔ ℓ▹ ⊔ ℓ◃′ ⊔ ℓ▹′ ⊔ ℓ)
RT ab cd q b d = (c1 : ab .com b) → Σ[ c2 ꞉ cd .com d ] ((x2 : cd .res c2) → Σ[ x1 ꞉ ab .res c1 ] q (ab .out c1 x1) (cd .out c2 x2))

-- correspondence

Crsp : IS A B ℓ◃ ℓ▹ → IS C D ℓ◃′ ℓ▹′ → Rel2 A C ℓ → Rel2 B D ℓ′ → 𝒰 (level-of-type A ⊔ level-of-type C ⊔ ℓ◃ ⊔ ℓ▹ ⊔ ℓ◃′ ⊔ ℓ▹′ ⊔ ℓ ⊔ ℓ′)
Crsp {A} {C} ab cd r q = (a : A) → (c : C) → r a c → RT ab cd q a c

-- simulation

Simu : IFace A ℓ◃ ℓ▹ → IFace B ℓ◃′ ℓ▹′ → Rel2 A B ℓ → 𝒰 (level-of-type A ⊔ level-of-type B ⊔ ℓ◃ ⊔ ℓ▹ ⊔ ℓ◃′ ⊔ ℓ▹′ ⊔ ℓ)
Simu ab cd r = Crsp ab cd r r
