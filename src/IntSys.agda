{-# OPTIONS --safe #-}
module IntSys where

open import Prelude

open import TrSys

private variable
  ℓ ℓ′ ℓᵃ ℓᵇ ℓᶜ ℓˢ ℓ◃ ℓ▹ ℓ◃′ ℓ▹′ : Level
  A : 𝒰 ℓᵃ
  B : 𝒰 ℓᵇ
  C : 𝒰 ℓᶜ
  S : 𝒰 ℓˢ

-- interaction system

record IS {ℓᵃ ℓᵇ}
          (A : 𝒰 ℓᵃ) (B : 𝒰 ℓᵇ) (ℓ◃ ℓ▹ : Level) : 𝒰 (ℓᵃ ⊔ ℓᵇ ⊔ ℓsuc ℓ◃ ⊔ ℓsuc ℓ▹) where
--  no-eta-equality
  field
    com : A → 𝒰 ℓ◃
    res : {a : A} → com a → 𝒰 ℓ▹
    out : {a : A} → (c : com a) → res c → B

open IS public

-- extension of a function
[_]⇒ : (A → B) → IS A B ℓ◃ ℓ▹
[ f ]⇒ .com _       = ⊤
[ f ]⇒ .res _       = ⊤
[ f ]⇒ .out {a} _ _ = f a

-- identity
skip : IS A A ℓ◃ ℓ▹
skip = [ id ]⇒

-- constant
cnst : Pred A ℓ → IS A B ℓ ℓ▹
cnst p .com     = p
cnst p .res _   = ⊥
cnst p .out _ b = ⊥.elim (lower b)

-- duality
_^⊥ : IS A B ℓ◃ ℓ▹ → IS A B (ℓ◃ ⊔ ℓ▹) ℓ◃
(w ^⊥) .com a     = (c : w .com a) → w .res c
(w ^⊥) .res {a} _ = w .com a
(w ^⊥) .out d c   = w .out c (d c)

-- composition
-- TODO ∙
inseq : IS A B ℓ◃ ℓ▹ → IS B C ℓ◃′ ℓ▹′ → IS A C (ℓ◃ ⊔ ℓ▹ ⊔ ℓ◃′) (ℓ▹ ⊔ ℓ▹′)
inseq ab bc .com a                      = Σ[ ca ꞉ ab .com a ] ((x : ab .res ca) → bc .com (ab .out ca x))
inseq ab bc .res {a} (ca , cf)          = Σ[ x ꞉ ab .res ca ] bc .res (cf x)
inseq ab bc .out {a} (ca , cf) (x , cx) = bc .out (cf x) cx

-- angelic extension for a transition system
[_]↑ : TS A B ℓ → IS A B ℓ ℓ▹
[ t ]↑ .com a   = t .tr a
[ t ]↑ .res _   = ⊤
[ t ]↑ .out c _ = t .nx c

-- demonic extension for a transition system
[_]↓ : TS A B ℓ → IS A B ℓ◃ ℓ
[ t ]↓ .com _     = ⊤
[ t ]↓ .res {a} _ = t .tr a
[ t ]↓ .out _ n   = t .nx n

munit : A → IS S (A × S) ℓ◃ ℓ▹
munit a = [ (a ,_) ]⇒

curry : (A → IS B C ℓ◃ ℓ▹) → IS (A × B) C ℓ◃ ℓ▹
curry f .com (a , b) = f a .com b
curry f .res {a = a , b} = f a .res
curry f .out {a = a , b} = f a .out

bind : IS S (A × B) ℓ◃ ℓ▹ → (A → IS B C ℓ◃′ ℓ▹′) → IS S C (ℓ◃ ⊔ ℓ▹ ⊔ ℓ◃′) (ℓ▹ ⊔ ℓ▹′)
bind sab = inseq sab ∘ curry

-- Cartesian product

pi : (A → IS B C ℓ◃ ℓ▹) → IS B C (level-of-type A ⊔ ℓ◃) (level-of-type A ⊔ ℓ▹)
pi {A} f .com b          = (a : A) → f a .com b
pi {A} f .res c          = Σ[ a ꞉ A ] f a .res (c a)
pi     f .out c (a , fa) = f a .out (c a) fa

-- Sum

sigma : (A → IS B C ℓ◃ ℓ▹) → IS B C (level-of-type A ⊔ ℓ◃) ℓ▹
sigma {A} f .com b        = Σ[ a ꞉ A ] f a .com b
sigma     f .res (a , fa) = f a .res fa
sigma     f .out (a , fa) = f a .out fa

-- Tensor product

tensor : IS A B ℓ◃ ℓ▹ → IS C S ℓ◃′ ℓ▹′ → IS (A × C) (B × S) (ℓ◃ ⊔ ℓ◃′) (ℓ▹ ⊔ ℓ▹′)
tensor ab cs .com (a , c) = ab .com a × cs .com c
tensor ab cs .res (abc , csc) = ab .res abc × cs .res csc
tensor ab cs .out (abc , csc) (abr , csr) = ab .out abc abr , cs .out csc csr

-- homogeneous interaction system aka interface
IFace : 𝒰 ℓᵃ → (ℓ◃ ℓ▹ : Level) → 𝒰 (ℓᵃ ⊔ ℓsuc ℓ◃ ⊔ ℓsuc ℓ▹)
IFace A ℓ◃ ℓ▹  = IS A A ℓ◃ ℓ▹

-- Angelic iteration

data Prog (i : IFace S ℓ◃ ℓ▹) : S → 𝒰 (level-of-type S ⊔ ℓ◃ ⊔ ℓ▹) where
  ret : ∀ {s} → Prog i s
  issue : ∀ {s} → (c : i .com s) → ((x : i .res c) → Prog i (i .out c x)) → Prog i s

tprog : {i : IFace S ℓ◃ ℓ▹} {s : S} → Prog i s → 𝒰 (ℓsuc ℓ▹)
tprog      ret        = ⊤
tprog {i} (issue c k) = Σ[ x ꞉ i .res c ] tprog (k x)

rprog : {i : IFace S ℓ◃ ℓ▹} {s : S} (p : Prog i s) (t : tprog p) → S
rprog {s}  ret         _      = s
rprog     (issue c k) (x , t) = rprog (k x) t

angelic-iter : IFace S ℓ◃ ℓ▹ → IFace S (level-of-type S ⊔ ℓ◃ ⊔ ℓ▹) (ℓsuc ℓ▹)
angelic-iter i .com = Prog i
angelic-iter i .res = tprog
angelic-iter i .out = rprog

-- Demonic iteration ?

-- extension of an interaction system
-- a predicate transformer
isys-pow : IS A B ℓ◃ ℓ▹ → Pred B ℓ → Pred A (ℓ◃ ⊔ ℓ▹ ⊔ ℓ)
isys-pow is pb a = Σ[ ac ꞉ is .com a ] ((ar : is .res ac) → pb (is .out ac ar))

instance
  ⟦⟧-IS : {ℓ : Level} → ⟦⟧-notation (IS A B ℓ◃ ℓ▹)
  ⟦⟧-IS {A} {B} {ℓ◃} {ℓ▹} {ℓ} = brackets (Pred B ℓ → Pred A (ℓ◃ ⊔ ℓ▹ ⊔ ℓ)) isys-pow

-- functoriality / monotonicity

functoriality : (w : IS A B ℓ◃ ℓ▹) (X Y : Pred B (ℓ◃ ⊔ ℓ▹))
              → X ⊆ Y → ⟦ w ⟧ X ⊆ ⟦ w ⟧ Y
functoriality w X Y xsy (wx , wf) = wx , (xsy ∘ wf)

-- All

all : {B : 𝒰 ℓᵇ} (w : IS A B ℓ◃ ℓ▹) (X : Pred B ℓ)
    → Pred (Σ[ b ꞉ B ] X b) ℓ′ → Pred (Σ[ a ꞉ A ] (⟦ w ⟧ X a)) (ℓ▹ ⊔ ℓ′)
all w X P (a , wa , k) = (r : w .res wa) → P (w .out wa r , k r)

-- Any

any : {B : 𝒰 ℓᵇ} (w : IS A B ℓ◃ ℓ▹) → (X : Pred B ℓ)
    → Pred (Σ[ b ꞉ B ] X b) ℓ′ → Pred (Σ[ a ꞉ A ] (⟦ w ⟧ X a)) (ℓ▹ ⊔ ℓ′)
any w X P (a , wa , k) = Σ[ r ꞉ w .res wa ] P (w .out wa r , k r)

-- correctness

skip-correct-l : {X : Pred A ℓ}
               → ⟦ skip {ℓ◃ = ℓ◃} {ℓ▹ = ℓ▹} ⟧ X ⊆ X
skip-correct-l (_ , k) = k (lift tt)

skip-correct-r : {X : Pred A ℓ}
               → X ⊆ ⟦ skip {ℓ◃ = ℓ◃} {ℓ▹ = ℓ▹} ⟧ X
skip-correct-r xa = lift tt , (λ _ → xa)

skip-correct : {X : Pred A ℓ}
             → ⟦ skip {ℓ◃ = ℓ◃} {ℓ▹ = ℓ▹} ⟧ X ≈ X
skip-correct {X} = skip-correct-l {X = X} , skip-correct-r {X = X}

cnst-correct-l : {X : Pred A ℓ} {Y : Pred A ℓ′}
               → ⟦ cnst {ℓ▹ = ℓ▹} X ⟧ Y ⊆ X
cnst-correct-l (xa , _) = xa

cnst-correct-r : {X : Pred A ℓ} {Y : Pred A ℓ′} {a : A}
               → X ⊆ ⟦ cnst {ℓ▹ = ℓ▹} X ⟧ Y
cnst-correct-r {Y} xa = xa , λ b → ⊥.elim {A = λ q → Y (⊥.elim q)} (lower b)

dual-correct-l : {w : IS A B ℓ◃ ℓ▹} {X : Pred B ℓ}
               → ⟦ w ^⊥ ⟧ X ⊆ (λ a → (c : w .com a) → Σ[ r ꞉ w .res c ] X (w .out c r))
dual-correct-l (f , g) c = (f c) , (g c)

dual-correct-r : {w : IS A B ℓ◃ ℓ▹} {X : Pred B ℓ} {a : A}
               → (λ a → (c : w .com a) → Σ[ r ꞉ w .res c ] X (w .out c r)) ⊆ ⟦ w ^⊥ ⟧ X
dual-correct-r f = (λ q → f q .fst) , (λ q → f q .snd)
