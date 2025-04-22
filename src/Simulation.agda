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

RT : IS A B ℓ◃ ℓ▹ → IS C D ℓ◃′ ℓ▹′
   → Rel2 B D ℓ → Rel2 A C (ℓ◃ ⊔ ℓ▹ ⊔ ℓ◃′ ⊔ ℓ▹′ ⊔ ℓ)
RT ab cd q b d = (c1 : ab .com b) → Σ[ c2 ꞉ cd .com d ] ((x2 : cd .res c2) → Σ[ x1 ꞉ ab .res c1 ] q (ab .out c1 x1) (cd .out c2 x2))

-- correspondence

Crsp : IS A B ℓ◃ ℓ▹ → IS C D ℓ◃′ ℓ▹′
     → Rel2 A C ℓ → Rel2 B D ℓ′
     → 𝒰 (level-of-type A ⊔ level-of-type C ⊔ ℓ◃ ⊔ ℓ▹ ⊔ ℓ◃′ ⊔ ℓ▹′ ⊔ ℓ ⊔ ℓ′)
Crsp {A} {C} ab cd r q = (a : A) → (c : C) → r a c → RT ab cd q a c

Crsp-id : (ab : IS A B ℓ◃ ℓ▹)
        → Crsp ab ab _＝_ _＝_
Crsp-id ab x y xy abx =
  Jₚ (λ z ez → Σ[ c2 ꞉ ab .com z ] ((x2 : ab .res c2) → Σ[ x1 ꞉ ab .res abx ] (ab .out abx x1 ＝ ab .out c2 x2)))
     (abx , (λ x2 → x2 , refl))
     xy

record Correspondence (ab : IS A B ℓ◃ ℓ▹) (cd : IS C D ℓ◃′ ℓ▹′) (ℓ ℓ′ : Level) : 𝒰 (  level-of-type A ⊔ level-of-type B ⊔ level-of-type C ⊔ level-of-type D
                                                                                     ⊔ ℓ◃ ⊔ ℓ▹ ⊔ ℓ◃′ ⊔ ℓ▹′
                                                                                     ⊔ ℓsuc ℓ ⊔ ℓsuc ℓ′) where
  field
    rc   : Rel2 A C ℓ
    qc   : Rel2 B D ℓ′
    crsp : Crsp {ℓ = ℓ} {ℓ′ = ℓ′} ab cd rc qc

open Correspondence public

idc : (ab : IS A B ℓ◃ ℓ▹) → Correspondence ab ab (level-of-type A) (level-of-type B)
idc ab .rc = _＝_
idc ab .qc = _＝_
idc ab .crsp = Crsp-id ab

-- simulation

Simu : IFace A ℓ◃ ℓ▹ → IFace B ℓ◃′ ℓ▹′
     → Rel2 A B ℓ → 𝒰 (level-of-type A ⊔ level-of-type B ⊔ ℓ◃ ⊔ ℓ▹ ⊔ ℓ◃′ ⊔ ℓ▹′ ⊔ ℓ)
Simu ab cd r = Crsp ab cd r r

record Simulation (ab : IFace A ℓ◃ ℓ▹) (cd : IFace B ℓ◃′ ℓ▹′) (ℓ : Level) : 𝒰 (level-of-type A ⊔ level-of-type B ⊔ ℓ◃ ⊔ ℓ▹ ⊔ ℓ◃′ ⊔ ℓ▹′ ⊔ ℓsuc ℓ) where
  field
    rs  : Rel2 A B ℓ
    sim : Simu {ℓ = ℓ} ab cd rs

open Simulation public

ids : (ab : IFace A ℓ◃ ℓ▹) → Simulation ab ab (level-of-type A)
ids ab .rs  = _＝_
ids ab .sim = Crsp-id ab
