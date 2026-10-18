{-# OPTIONS --cubical -W noUnsupportedIndexedMatch #-}
{-
The standard interpretation of the inductive-recursive syntax (TT.agda)
into families of GROUPOIDS, in Cubical Agda, without UIP.

Two design decisions:

* Forded semantics of extension:
      ⟦ ext A x δ ⟧T γ = Σ a. Σ d. (⟦ δ ⟧ a ≡ d) × ⟦ x ⟧ d
  (equivalent to Σ a. ⟦ x ⟧ (⟦ δ ⟧ a) by contracting singletons). A kept
  entry then never transports the value v; it only changes the stored
  path. Equations between semantic thinnings have no fibre component.

* Codes act semantically:  ≈ : Code σ τ → ⟦ σ ⟧ a ≡ ⟦ τ ⟧ a  is defined by
  recursion, instead of applying ⟦_⟧ to Code-sound (which does not compute).

What remains are 2-cells in the semantic telescopes (coherences of ⟦∘⟧,
≈ and unwk-nat), proved by induction. 3-cells are trivial because the
semantic telescopes are groupoids.

Equality reasoning uses Agda's inductive identity type (J computes); it is
equivalent to the cubical path type (Cubical.Data.Equality).
-}
module Sem1 where

open import TT
open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit

import Cubical.Foundations.Prelude as P
import Cubical.Foundations.HLevels as H
import Cubical.Data.Equality as E
import Cubical.Data.Unit as CU

-- the universe: groupoids (in the sense of cubical paths) ------------------------

record Grpd : Set₁ where
  constructor grpd
  field
    ⌞_⌟    : Set
    isGrpd : P.isGroupoid ⌞_⌟
open Grpd

record ⊤₁ : Set₁ where
  constructor tt₁

-- equality toolkit ----------------------------------------------------------------

∙refl : {X : Set}{a b : X}(p : a ≡ b) → p ∙ refl ≡ p
∙refl refl = refl

-- the three algebraic reductions of the coherences (pure J)
lemN : {X : Set}{x y z w v : X}(m : x ≡ y)(n : y ≡ z)(k : x ≡ w)(l : w ≡ z)(e₁ : x ≡ v)(e₂ : w ≡ v)
     → m ∙ n ≡ k ∙ l → k ∙ e₂ ≡ e₁ → sym n ∙ (sym m ∙ e₁) ≡ sym l ∙ e₂
lemN' : {X : Set}{x w z v : X}(k : x ≡ w)(l : w ≡ z)(e₂ : w ≡ v) → sym (k ∙ l) ∙ (k ∙ e₂) ≡ sym l ∙ e₂
lemN' refl l e₂ = refl
lemN refl .(k ∙ l) k l .(k ∙ e₂) e₂ refl refl = lemN' k l e₂

lemA : {X : Set}{x y z w₁ w₂ t u v : X}
       (m : x ≡ y)(n : y ≡ z)(k₁ : x ≡ w₁)(l₁ : w₁ ≡ w₂)(l₂ : w₂ ≡ z)(g : w₂ ≡ u)
       (k₂ : w₁ ≡ t)(h : t ≡ u)(e₁ : x ≡ v)(e₂ : t ≡ v)(f : w₁ ≡ v)
     → m ∙ n ≡ k₁ ∙ (l₁ ∙ l₂) → l₁ ∙ g ≡ k₂ ∙ h → k₂ ∙ e₂ ≡ f → k₁ ∙ f ≡ e₁
     → sym n ∙ (sym m ∙ e₁) ≡ (sym l₂ ∙ g) ∙ (sym h ∙ e₂)
lemA' : {X : Set}{x w z t u v : X}(k₁ : x ≡ w)(l₂ : w ≡ z)(k₂ : w ≡ t)(h : t ≡ u)(e₂ : t ≡ v)
      → sym (k₁ ∙ l₂) ∙ (k₁ ∙ (k₂ ∙ e₂)) ≡ (sym l₂ ∙ (k₂ ∙ h)) ∙ (sym h ∙ e₂)
lemA' refl refl refl refl e₂ = refl
lemA refl .(k₁ ∙ l₂) k₁ refl l₂ .(k₂ ∙ h) k₂ h .(k₁ ∙ (k₂ ∙ e₂)) e₂ .(k₂ ∙ e₂) refl refl refl refl =
  lemA' k₁ l₂ k₂ h e₂

lemW : {X Y : Set}(F : X → Y){x₀ x₁ x₂ x₃ : X}{y₁ y₂ y₃ y₄ : Y}
       (m : x₀ ≡ x₁)(k : x₀ ≡ x₂)(j : x₂ ≡ x₃)(e₁ : x₀ ≡ x₃)
       (u₁ : F x₂ ≡ y₁)(o : y₁ ≡ y₂)(nδ : F x₁ ≡ y₃)(cu : y₃ ≡ y₂)(nδ' : F x₃ ≡ y₄)(g : y₁ ≡ y₄)
     → cong F k ∙ (u₁ ∙ o) ≡ cong F m ∙ (nδ ∙ cu) → cong F j ∙ nδ' ≡ u₁ ∙ g → k ∙ j ≡ e₁
     → sym cu ∙ (sym nδ ∙ cong F (sym m ∙ e₁)) ≡ (sym o ∙ g) ∙ sym nδ'
lemW' : {Y : Set}{y₀ y₂ y₃ y₄ : Y}(nδ : y₀ ≡ y₃)(cu : y₃ ≡ y₂)(g : y₀ ≡ y₄)
      → sym cu ∙ (sym nδ ∙ refl) ≡ (sym (nδ ∙ cu) ∙ g) ∙ sym g
lemW' refl refl refl = refl
lemW F refl refl refl .refl refl .(nδ ∙ cu) nδ cu .g g refl refl refl = lemW' nδ cu g

-- a point, a path to a fixed d, and a value over d
pathK : {B D : Set}{f : B → D}{V : D → Set}{b b' : B}{d : D}{q : f b ≡ d}{q' : f b' ≡ d}{v : V d}
      → (r : b ≡ b') → sym (cong f r) ∙ q ≡ q'
      → _≡_ {A = Σ B (λ b → Σ D (λ d → Σ (f b ≡ d) (λ _ → V d)))} (b , d , q , v) (b' , d , q' , v)
pathK {b = b} {d = d} {v = v} refl s = cong (λ q → b , d , q , v) s

-- groupoids, for the inductive identity type
isGrpdEq : Set → Set
isGrpdEq D = {u v : D}{q q' : u ≡ v}(s s' : q ≡ q') → s ≡ s'

eqIsSet : {D : Set} → P.isGroupoid D → (u v : D) → P.isSet (u ≡ v)
eqIsSet g u v = P.subst P.isSet (E.PathPathEq {x = u} {y = v}) (g u v)

grpdEq : {D : Set} → P.isGroupoid D → isGrpdEq D
grpdEq g {u} {v} {q} {q'} s s' = E.pathToEq (P.subst P.isProp (E.PathPathEq {x = q} {y = q'}) (eqIsSet g u v q q') s s')

-- in a set, 2-paths are unique
set→2prop : {X : Set}{a b : X}(h : (q q' : a ≡ b) → q ≡ q'){q q' : a ≡ b}(w w' : q ≡ q') → w ≡ w'
set→2prop {a = a} {b} h {q} {q'} w w' = canon w ∙ sym (canon w')
  where
    sym∙ : {y : a ≡ b}(t : q ≡ y) → sym t ∙ t ≡ refl
    sym∙ refl = refl
    canon : {y : a ≡ b}(w : q ≡ y) → w ≡ sym (h q q) ∙ h q y
    canon refl = sym (sym∙ (h q q))

cong-∙ : {X Y : Set}(F : X → Y){x y z : X}(r : x ≡ y)(t : y ≡ z) → cong F (r ∙ t) ≡ cong F r ∙ cong F t
cong-∙ F refl t = refl

-- composing paths of the form pathK
pathK-∙≡ : {B D : Set}{f : B → D}{V : D → Set}(gD : isGrpdEq D){b b' b'' : B}{d : D}
           {q : f b ≡ d}{q' : f b' ≡ d}{q'' : f b'' ≡ d}{v : V d}
           (r : b ≡ b')(r' : b' ≡ b'')(r'' : b ≡ b'')
           (s : sym (cong f r) ∙ q ≡ q')(s' : sym (cong f r') ∙ q' ≡ q'')(s'' : sym (cong f r'') ∙ q ≡ q'')
         → r ∙ r' ≡ r'' → pathK {V = V} {v = v} r s ∙ pathK r' s' ≡ pathK r'' s''
pathK-∙≡ gD {b = b} {d = d} {v = v} refl refl .refl s s' s'' refl =
  sym (cong-∙ (λ q → b , d , q , v) s s') ∙ cong (cong (λ q → b , d , q , v)) (gD (s ∙ s') s'')

-- the interpretation ----------------------------------------------------------------

⟦_⟧C : Con → Set₁
{-# TERMINATING #-}
⟦_⟧T : {Γ : Con} → Ty Γ → ⟦ Γ ⟧C → Set
⟦ • ⟧C = ⊤₁
⟦ Γ ▷ A ⟧C = Σ ⟦ Γ ⟧C (λ γ → ⟦ A ⟧T γ → Grpd)

{-# TERMINATING #-}
⟦_⟧V : {Γ : Con}{A : Ty Γ} → Var Γ A → (γ : ⟦ Γ ⟧C) → ⟦ A ⟧T γ → Set
{-# TERMINATING #-}
⟦_⟧Th : {Γ : Con}{A B : Ty Γ} → Thin A B → {γ : ⟦ Γ ⟧C} → ⟦ A ⟧T γ → ⟦ B ⟧T γ

-- codes act as paths
{-# TERMINATING #-}
≈ : {Γ : Con}{A C : Ty Γ}{σ τ : Thin A C} → Code σ τ → {γ : ⟦ Γ ⟧C}(a : ⟦ A ⟧T γ) → ⟦ σ ⟧Th a ≡ ⟦ τ ⟧Th a

-- composition
{-# TERMINATING #-}
⟦∘⟧ : {Γ : Con}{A B C : Ty Γ}(δ : Thin B C)(σ : Thin A B){γ : ⟦ Γ ⟧C}(a : ⟦ A ⟧T γ)
    → ⟦ δ ∘ σ ⟧Th a ≡ ⟦ δ ⟧Th (⟦ σ ⟧Th a)

-- the path stored by a kept entry
kp : {Γ : Con}{A B C : Ty Γ}(δ : Thin B C)(σ : Thin A B)(δ' : Thin A C) → Code (δ ∘ σ) δ'
   → {γ : ⟦ Γ ⟧C}(a : ⟦ A ⟧T γ) → ⟦ δ ⟧Th (⟦ σ ⟧Th a) ≡ ⟦ δ' ⟧Th a
kp δ σ δ' e a = sym (⟦∘⟧ δ σ a) ∙ ≈ {σ = δ ∘ σ} {δ'} e a

-- the rest of a kept entry, after identifying the source and target variables
tkR : {Γ : Con}{A B C C' : Ty Γ}{x : Var Γ C}{y : Var Γ C'}{γ : ⟦ Γ ⟧C}
      (σ : Thin A B)(δ : Thin B C')(δ' : Thin A C)
    → _≡_ {A = VarΣ Γ} (C , x) (C' , y) → Code (δ ∘ σ) δ'
    → (a : ⟦ A ⟧T γ) → Σ (⟦ C ⟧T γ) (λ d → Σ (⟦ δ' ⟧Th a ≡ d) (λ _ → ⟦ x ⟧V γ d))
    → Σ (⟦ C' ⟧T γ) (λ d → Σ (⟦ δ ⟧Th (⟦ σ ⟧Th a) ≡ d) (λ _ → ⟦ y ⟧V γ d))
tkR σ δ δ' refl e a (d , q , v) = d , kp δ σ δ' e a ∙ q , v

-- semantics of weakening by p
{-# TERMINATING #-}
unwk : {Γ : Con}(A : Ty Γ){B : Ty Γ}{γ : ⟦ Γ ⟧C}{X : ⟦ B ⟧T γ → Grpd}
     → ⟦ wkTy A (p {A = B}) ⟧T (γ , X) → ⟦ A ⟧T γ
{-# TERMINATING #-}
unwk-nat : {Γ : Con}{A C : Ty Γ}(δ : Thin A C){B : Ty Γ}{γ : ⟦ Γ ⟧C}{X : ⟦ B ⟧T γ → Grpd}
           (a : ⟦ wkTy A (p {A = B}) ⟧T (γ , X))
         → unwk C (⟦ wkThin δ p ⟧Th a) ≡ ⟦ δ ⟧Th (unwk A a)

⟦ ε ⟧T γ = ⊤
⟦ ext {B = C} A x δ ⟧T γ = Σ (⟦ A ⟧T γ) (λ a → Σ (⟦ C ⟧T γ) (λ d → Σ (⟦ δ ⟧Th a ≡ d) (λ _ → ⟦ x ⟧V γ d)))

⟦_⟧V {Γ ▷ B} zero (γ , X) b = ⌞ X (unwk B b) ⌟
⟦_⟧V {Γ ▷ B} (suc {A = A} x) (γ , X) b = ⟦ x ⟧V γ (unwk A b)

⟦ tε ⟧Th a = tt
⟦ t-d σ ⟧Th (a , r) = ⟦ σ ⟧Th a
⟦ t-k {x = x} {y = y} {δ = δ} {δ' = δ'} σ ex e ⟧Th (a , r) =
  ⟦ σ ⟧Th a , tkR σ δ δ' (CodeV-sound x y ex) e a r

unwk ε b = tt
unwk (ext {B = C} A x δ) (a , d , q , v) = unwk A a , unwk C d , sym (unwk-nat δ a) ∙ cong (unwk C) q , v

-- the generic coherences (2-cells), by induction ------------------------------------

-- T: code paths compose
{-# TERMINATING #-}
cohT : {Γ : Con}{A C : Ty Γ}(σ τ ρ : Thin A C)(c : Code σ τ)(d : Code τ ρ)(cd : Code σ ρ)
       {γ : ⟦ Γ ⟧C}(a : ⟦ A ⟧T γ)
     → ≈ {σ = σ} {τ} c a ∙ ≈ {σ = τ} {ρ} d a ≡ ≈ {σ = σ} {ρ} cd a

-- composition is natural in codes, on the right and on the left
{-# TERMINATING #-}
cohR : {Γ : Con}{A B C : Ty Γ}(δ : Thin B C)(σ τ : Thin A B)(c : Code σ τ)(c' : Code (δ ∘ σ) (δ ∘ τ))
       {γ : ⟦ Γ ⟧C}(a : ⟦ A ⟧T γ)
     → ⟦∘⟧ δ σ a ∙ cong ⟦ δ ⟧Th (≈ {σ = σ} {τ} c a) ≡ ≈ {σ = δ ∘ σ} {δ ∘ τ} c' a ∙ ⟦∘⟧ δ τ a
{-# TERMINATING #-}
cohL : {Γ : Con}{A B C : Ty Γ}(δ δ₂ : Thin B C)(σ : Thin A B)(c : Code δ δ₂)(c' : Code (δ ∘ σ) (δ₂ ∘ σ))
       {γ : ⟦ Γ ⟧C}(a : ⟦ A ⟧T γ)
     → ⟦∘⟧ δ σ a ∙ ≈ {σ = δ} {δ₂} c (⟦ σ ⟧Th a) ≡ ≈ {σ = δ ∘ σ} {δ₂ ∘ σ} c' a ∙ ⟦∘⟧ δ₂ σ a

-- composition is associative, coherently
{-# TERMINATING #-}
cohAs : {Γ : Con}{A B C D : Ty Γ}(ρ : Thin C D)(δ : Thin B C)(σ : Thin A B)
        (c : Code (ρ ∘ (δ ∘ σ)) ((ρ ∘ δ) ∘ σ)){γ : ⟦ Γ ⟧C}(a : ⟦ A ⟧T γ)
      → ⟦∘⟧ ρ (δ ∘ σ) a ∙ cong ⟦ ρ ⟧Th (⟦∘⟧ δ σ a)
        ≡ ≈ {σ = ρ ∘ (δ ∘ σ)} {(ρ ∘ δ) ∘ σ} c a ∙ (⟦∘⟧ (ρ ∘ δ) σ a ∙ ⟦∘⟧ ρ δ (⟦ σ ⟧Th a))

-- unwk-nat is natural in codes, and compatible with composition
{-# TERMINATING #-}
cohWN : {Γ : Con}{A C : Ty Γ}(ρ ρ' : Thin A C){B₀ : Ty Γ}
        (c : Code ρ ρ')(c' : Code (wkThin ρ (p {A = B₀})) (wkThin ρ' p))
        {γ : ⟦ Γ ⟧C}{X : ⟦ B₀ ⟧T γ → Grpd}(a : ⟦ wkTy A (p {A = B₀}) ⟧T (γ , X))
      → cong (unwk C) (≈ {σ = wkThin ρ p} {wkThin ρ' p} c' a) ∙ unwk-nat ρ' a
        ≡ unwk-nat ρ a ∙ ≈ {σ = ρ} {ρ'} c (unwk A a)
{-# TERMINATING #-}
cohW∘ : {Γ : Con}{A B C : Ty Γ}(δ : Thin B C)(σ : Thin A B){B₀ : Ty Γ}
        (c : Code (wkThin δ (p {A = B₀}) ∘ wkThin σ p) (wkThin (δ ∘ σ) p))
        {γ : ⟦ Γ ⟧C}{X : ⟦ B₀ ⟧T γ → Grpd}(a : ⟦ wkTy A (p {A = B₀}) ⟧T (γ , X))
      → cong (unwk C) (≈ {σ = wkThin δ p ∘ wkThin σ p} {wkThin (δ ∘ σ) p} c a)
        ∙ (unwk-nat (δ ∘ σ) a ∙ ⟦∘⟧ δ σ (unwk A a))
        ≡ cong (unwk C) (⟦∘⟧ (wkThin δ p) (wkThin σ p) a)
          ∙ (unwk-nat δ (⟦ wkThin σ p ⟧Th a) ∙ cong ⟦ δ ⟧Th (unwk-nat σ a))

-- the coherences used by the interpretation (2-cells) -------------------------------

-- N: the stored path is natural in codes
cohN : {Γ : Con}{A B C : Ty Γ}(δ : Thin B C)(σ τ : Thin A B)(δ' : Thin A C)
       (c : Code σ τ)(e : Code (δ ∘ σ) δ')(e' : Code (δ ∘ τ) δ'){γ : ⟦ Γ ⟧C}(a : ⟦ A ⟧T γ)
     → sym (cong ⟦ δ ⟧Th (≈ {σ = σ} {τ} c a)) ∙ kp δ σ δ' e a ≡ kp δ τ δ' e' a
cohN δ σ τ δ' c e e' a =
  lemN (⟦∘⟧ δ σ a) (cong ⟦ δ ⟧Th (≈ {σ = σ} {τ} c a)) (≈ {σ = δ ∘ σ} {δ ∘ τ} c' a) (⟦∘⟧ δ τ a)
       (≈ {σ = δ ∘ σ} {δ'} e a) (≈ {σ = δ ∘ τ} {δ'} e' a)
       (cohR δ σ τ c c' a) (cohT (δ ∘ σ) (δ ∘ τ) δ' c' e' e a)
  where c' = ≡→Code (cong (δ ∘_) (Code-sound σ τ c))

-- A: the stored paths of two keeps compose to the stored path of the composite
cohA : {Γ : Con}{A B C D : Ty Γ}(δC : Thin C D)(δB : Thin B D)(δA : Thin A D)(δ : Thin B C)(σ : Thin A B)
       (q : Code (δC ∘ δ) δB)(e : Code (δB ∘ σ) δA)(e' : Code (δC ∘ (δ ∘ σ)) δA){γ : ⟦ Γ ⟧C}(a : ⟦ A ⟧T γ)
     → sym (cong ⟦ δC ⟧Th (⟦∘⟧ δ σ a)) ∙ kp δC (δ ∘ σ) δA e' a ≡ kp δC δ δB q (⟦ σ ⟧Th a) ∙ kp δB σ δA e a
cohA δC δB δA δ σ q e e' a =
  lemA (⟦∘⟧ δC (δ ∘ σ) a) (cong ⟦ δC ⟧Th (⟦∘⟧ δ σ a))
       (≈ {σ = δC ∘ (δ ∘ σ)} {(δC ∘ δ) ∘ σ} c₁ a) (⟦∘⟧ (δC ∘ δ) σ a) (⟦∘⟧ δC δ (⟦ σ ⟧Th a))
       (≈ {σ = δC ∘ δ} {δB} q (⟦ σ ⟧Th a)) (≈ {σ = (δC ∘ δ) ∘ σ} {δB ∘ σ} c₂ a) (⟦∘⟧ δB σ a)
       (≈ {σ = δC ∘ (δ ∘ σ)} {δA} e' a) (≈ {σ = δB ∘ σ} {δA} e a) (≈ {σ = (δC ∘ δ) ∘ σ} {δA} c₂e a)
       (cohAs δC δ σ c₁ a) (cohL (δC ∘ δ) δB σ q c₂ a)
       (cohT ((δC ∘ δ) ∘ σ) (δB ∘ σ) δA c₂ e c₂e a) (cohT (δC ∘ (δ ∘ σ)) ((δC ∘ δ) ∘ σ) δA c₁ c₂e e' a)
  where c₁ = Code-assoc δC δ σ
        c₂ = Code-∘ (δC ∘ δ) δB σ q
        c₂e = Code-trans ((δC ∘ δ) ∘ σ) (δB ∘ σ) δA c₂ e

-- W: weakening commutes with stored paths
cohW : {Γ : Con}{A B C : Ty Γ}(σ : Thin A B)(δ : Thin B C)(δ' : Thin A C){B₀ : Ty Γ}
       (e : Code (δ ∘ σ) δ')(e₁ : Code (wkThin δ (p {A = B₀}) ∘ wkThin σ p) (wkThin δ' p))
       {γ : ⟦ Γ ⟧C}{X : ⟦ B₀ ⟧T γ → Grpd}(a : ⟦ wkTy A (p {A = B₀}) ⟧T (γ , X))
     → sym (cong ⟦ δ ⟧Th (unwk-nat σ a)) ∙ sym (unwk-nat δ (⟦ wkThin σ p ⟧Th a))
       ∙ cong (unwk C) (kp (wkThin δ p) (wkThin σ p) (wkThin δ' p) e₁ a)
       ≡ kp δ σ δ' e (unwk A a) ∙ sym (unwk-nat δ' a)
cohW {C = C} σ δ δ' e e₁ a =
  lemW (unwk C) (⟦∘⟧ (wkThin δ p) (wkThin σ p) a)
       (≈ {σ = wkThin δ p ∘ wkThin σ p} {wkThin (δ ∘ σ) p} c₃ a) (≈ {σ = wkThin (δ ∘ σ) p} {wkThin δ' p} cwe a)
       (≈ {σ = wkThin δ p ∘ wkThin σ p} {wkThin δ' p} e₁ a)
       (unwk-nat (δ ∘ σ) a) (⟦∘⟧ δ σ (unwk _ a)) (unwk-nat δ (⟦ wkThin σ p ⟧Th a))
       (cong ⟦ δ ⟧Th (unwk-nat σ a)) (unwk-nat δ' a) (≈ {σ = δ ∘ σ} {δ'} e (unwk _ a))
       (cohW∘ δ σ c₃ a) (cohWN (δ ∘ σ) δ' e cwe a)
       (cohT (wkThin δ p ∘ wkThin σ p) (wkThin (δ ∘ σ) p) (wkThin δ' p) c₃ cwe e₁ a)
  where c₃ = Code-wk∘ δ σ p
        cwe = Code-wk (δ ∘ σ) δ' p e

-- the clauses using them ----------------------------------------------------------

-- ≈ on keeps: the stored paths agree by cohN
≈K : {Γ : Con}{A B C C' : Ty Γ}{x : Var Γ C}{y : Var Γ C'}{γ : ⟦ Γ ⟧C}
     (σ τ : Thin A B)(δ : Thin B C')(δ' : Thin A C)(pxy pxy' : _≡_ {A = VarΣ Γ} (C , x) (C' , y))(w : pxy ≡ pxy')
     (c : Code σ τ)(e : Code (δ ∘ σ) δ')(e' : Code (δ ∘ τ) δ')(a : ⟦ A ⟧T γ)
     (r : Σ (⟦ C ⟧T γ) (λ d → Σ (⟦ δ' ⟧Th a ≡ d) (λ _ → ⟦ x ⟧V γ d)))
   → _≡_ {A = ⟦ ext B y δ ⟧T γ} (⟦ σ ⟧Th a , tkR σ δ δ' pxy e a r) (⟦ τ ⟧Th a , tkR τ δ δ' pxy' e' a r)
≈k : {Γ : Con}{A B C C' : Ty Γ}{x : Var Γ C}{y : Var Γ C'}{γ : ⟦ Γ ⟧C}
     {σ τ : Thin A B}(δ : Thin B C')(δ' : Thin A C)(pxy : _≡_ {A = VarΣ Γ} (C , x) (C' , y))
     (c : Code σ τ)(e : Code (δ ∘ σ) δ')(e' : Code (δ ∘ τ) δ')(a : ⟦ A ⟧T γ)
     (r : Σ (⟦ C ⟧T γ) (λ d → Σ (⟦ δ' ⟧Th a ≡ d) (λ _ → ⟦ x ⟧V γ d)))
   → _≡_ {A = ⟦ ext B y δ ⟧T γ} (⟦ σ ⟧Th a , tkR σ δ δ' pxy e a r) (⟦ τ ⟧Th a , tkR τ δ δ' pxy e' a r)
≈k {σ = σ} {τ} δ δ' refl c e e' a (d , refl , v) =
  pathK (≈ {σ = σ} {τ} c a) (cong (sym (cong ⟦ δ ⟧Th (≈ {σ = σ} {τ} c a)) ∙_) (∙refl (kp δ σ δ' e a))
                 ∙ cohN δ σ τ δ' c e e' a ∙ sym (∙refl (kp δ τ δ' e' a)))

≈K σ τ δ δ' pxy pxy' w c e e' a r =
  subst (λ q → _≡_ {A = ⟦ ext _ _ δ ⟧T _} (⟦ σ ⟧Th a , tkR σ δ δ' pxy e a r)
                                          (⟦ τ ⟧Th a , tkR τ δ δ' q e' a r))
        w (≈k δ δ' pxy c e e' a r)

≈ {σ = tε} {tε} c a = refl
≈ {σ = t-d σ} {t-d τ} c (a , r) = ≈ {σ = σ} {τ} c a
≈ {σ = t-k {x = x} {y} {δ} {δ'} σ ex e} {t-k τ ex' e'} c (a , r) =
  ≈K σ τ δ δ' (CodeV-sound x y ex) (CodeV-sound x y ex') (VarΣ-set _ _) c e e' a r
≈ {σ = t-d σ} {t-k τ _ _} () a
≈ {σ = t-k σ _ _} {t-d τ} () a

-- composition of two keeps: the stored paths agree by cohA
comp-k : {Γ : Con}{A B C D₁ D₂ D₃ : Ty Γ}{x : Var Γ D₁}{y : Var Γ D₂}{z : Var Γ D₃}{γ : ⟦ Γ ⟧C}
         (δ : Thin B C)(σ : Thin A B)(δC : Thin C D₃)(δB : Thin B D₂)(δA : Thin A D₁)
         (pxy : _≡_ {A = VarΣ Γ} (D₁ , x) (D₂ , y))(pyz : _≡_ {A = VarΣ Γ} (D₂ , y) (D₃ , z))
         (pxz : _≡_ {A = VarΣ Γ} (D₁ , x) (D₃ , z))
         (q : Code (δC ∘ δ) δB)(e : Code (δB ∘ σ) δA)(e' : Code (δC ∘ (δ ∘ σ)) δA)
         (a : ⟦ A ⟧T γ)(r : Σ (⟦ D₁ ⟧T γ) (λ d → Σ (⟦ δA ⟧Th a ≡ d) (λ _ → ⟦ x ⟧V γ d)))
       → _≡_ {A = ⟦ ext C z δC ⟧T γ}
           (⟦ δ ∘ σ ⟧Th a , tkR (δ ∘ σ) δC δA pxz e' a r)
           (⟦ δ ⟧Th (⟦ σ ⟧Th a) , tkR δ δC δB pyz q (⟦ σ ⟧Th a) (tkR σ δB δA pxy e a r))
comp-k₀ : {Γ : Con}{A B C D : Ty Γ}{x : Var Γ D}{γ : ⟦ Γ ⟧C}
          (δ : Thin B C)(σ : Thin A B)(δC : Thin C D)(δB : Thin B D)(δA : Thin A D)
          (q : Code (δC ∘ δ) δB)(e : Code (δB ∘ σ) δA)(e' : Code (δC ∘ (δ ∘ σ)) δA)
          (a : ⟦ A ⟧T γ)(r : Σ (⟦ D ⟧T γ) (λ d → Σ (⟦ δA ⟧Th a ≡ d) (λ _ → ⟦ x ⟧V γ d)))
        → _≡_ {A = ⟦ ext C x δC ⟧T γ}
            (⟦ δ ∘ σ ⟧Th a , tkR (δ ∘ σ) δC δA refl e' a r)
            (⟦ δ ⟧Th (⟦ σ ⟧Th a) , tkR δ δC δB refl q (⟦ σ ⟧Th a) (tkR σ δB δA refl e a r))
comp-k₀ δ σ δC δB δA q e e' a (d , refl , v) =
  pathK (⟦∘⟧ δ σ a)
        (cong (sym (cong ⟦ δC ⟧Th (⟦∘⟧ δ σ a)) ∙_) (∙refl (kp δC (δ ∘ σ) δA e' a))
         ∙ cohA δC δB δA δ σ q e e' a
         ∙ cong (kp δC δ δB q (⟦ σ ⟧Th a) ∙_) (sym (∙refl (kp δB σ δA e a))))

comp-k {x = x} {γ = γ} δ σ δC δB δA refl refl pxz q e e' a r =
  subst (λ w → _≡_ {A = ⟦ ext _ x δC ⟧T γ}
                   (⟦ δ ∘ σ ⟧Th a , tkR (δ ∘ σ) δC δA w e' a r)
                   (⟦ δ ⟧Th (⟦ σ ⟧Th a) , tkR δ δC δB refl q (⟦ σ ⟧Th a) (tkR σ δB δA refl e a r)))
        (VarΣ-set refl pxz)
        (comp-k₀ δ σ δC δB δA q e e' a r)

⟦∘⟧ δ tε a = refl
⟦∘⟧ δ (t-d σ) (a , r) = ⟦∘⟧ δ σ a
⟦∘⟧ (t-d δ) (t-k σ ex e) (a , r) = ⟦∘⟧ δ σ a
⟦∘⟧ (t-k {x = y} {y = z} {δ = δC} {δ' = δB} δ ey q) (t-k {x = x} {δ' = δA} σ ex e) (a , r) =
  comp-k δ σ δC δB δA (CodeV-sound x y ex) (CodeV-sound y z ey)
         (CodeV-sound x z (CodeV-trans x y z ex ey)) q e _ a r

-- weakening a keep: the stored paths agree by cohW
uk : {Γ : Con}{A B C C' B₀ : Ty Γ}{x : Var Γ C}{y : Var Γ C'}
     (σ : Thin A B)(δ : Thin B C')(δ' : Thin A C)(p₀ : _≡_ {A = VarΣ Γ} (C , x) (C' , y))
     (e : Code (δ ∘ σ) δ')(e₁ : Code (wkThin δ (p {A = B₀}) ∘ wkThin σ p) (wkThin δ' p))
     {γ : ⟦ Γ ⟧C}{X : ⟦ B₀ ⟧T γ → Grpd}(a : ⟦ wkTy A (p {A = B₀}) ⟧T (γ , X))
     (r : Σ (⟦ wkTy C (p {A = B₀}) ⟧T (γ , X)) (λ d → Σ (⟦ wkThin δ' p ⟧Th a ≡ d) (λ _ → ⟦ x ⟧V γ (unwk C d))))
   → _≡_ {A = ⟦ ext B y δ ⟧T γ}
       (unwk (ext B y δ) (⟦ wkThin σ p ⟧Th a , tkR (wkThin σ p) (wkThin δ p) (wkThin δ' p) (cong (sucΣ {B = B₀}) p₀) e₁ a r))
       (⟦ σ ⟧Th (unwk A a) ,
        tkR σ δ δ' p₀ e (unwk A a) (unwk C (fst r) , sym (unwk-nat δ' a) ∙ cong (unwk C) (fst (snd r)) , snd (snd r)))
uk {C = C} σ δ δ' refl e e₁ a (d , refl , v) =
  pathK (unwk-nat σ a)
        (cong (λ z → sym (cong ⟦ δ ⟧Th (unwk-nat σ a)) ∙ sym (unwk-nat δ (⟦ wkThin σ p ⟧Th a)) ∙ cong (unwk C) z)
              (∙refl (kp (wkThin δ p) (wkThin σ p) (wkThin δ' p) e₁ a))
         ∙ cohW σ δ δ' e e₁ a
         ∙ cong (kp δ σ δ' e (unwk _ a) ∙_) (sym (∙refl (sym (unwk-nat δ' a)))))

unwk-nat tε a = refl
unwk-nat (t-d σ) (a , r) = unwk-nat σ a
unwk-nat (t-k {x = x} {y = y} {δ = δ} {δ' = δ'} σ ex e) (a , r) = uk σ δ δ' (CodeV-sound x y ex) e _ a r

-- the semantic types are groupoids
{-# TERMINATING #-}
isGrpdT : {Γ : Con}(A : Ty Γ)(γ : ⟦ Γ ⟧C) → P.isGroupoid (⟦ A ⟧T γ)
{-# TERMINATING #-}
isGrpdV : {Γ : Con}{A : Ty Γ}(x : Var Γ A)(γ : ⟦ Γ ⟧C)(a : ⟦ A ⟧T γ) → P.isGroupoid (⟦ x ⟧V γ a)
isGrpdT ε γ = H.isSet→isGroupoid CU.isSetUnit
isGrpdT (ext {B = C} A x δ) γ =
  H.isGroupoidΣ (isGrpdT A γ) λ a → H.isGroupoidΣ (isGrpdT C γ) λ d →
    H.isGroupoidΣ (H.isSet→isGroupoid (eqIsSet (isGrpdT C γ) (⟦ δ ⟧Th a) d)) λ _ → isGrpdV x γ d
isGrpdV {Γ ▷ B} zero (γ , X) b = isGrpd (X (unwk B b))
isGrpdV {Γ ▷ B} (suc {A = A} x) (γ , X) b = isGrpdV x γ (unwk A b)

-- T on keeps
TK : {Γ : Con}{A B C C' : Ty Γ}{x : Var Γ C}{y : Var Γ C'}{γ : ⟦ Γ ⟧C}
     (σ τ ρ : Thin A B)(δ : Thin B C')(δ' : Thin A C)
     (p₁ p₂ p₃ : _≡_ {A = VarΣ Γ} (C , x) (C' , y))(w₁₂ : p₁ ≡ p₂)(w₂₃ : p₂ ≡ p₃)(w₁₃ : p₁ ≡ p₃)
     (c : Code σ τ)(d : Code τ ρ)(cd : Code σ ρ)
     (e : Code (δ ∘ σ) δ')(e' : Code (δ ∘ τ) δ')(e'' : Code (δ ∘ ρ) δ')(a : ⟦ A ⟧T γ)
     (r : Σ (⟦ C ⟧T γ) (λ d → Σ (⟦ δ' ⟧Th a ≡ d) (λ _ → ⟦ x ⟧V γ d)))
   → ≈K σ τ δ δ' p₁ p₂ w₁₂ c e e' a r ∙ ≈K τ ρ δ δ' p₂ p₃ w₂₃ d e' e'' a r ≡ ≈K σ ρ δ δ' p₁ p₃ w₁₃ cd e e'' a r
TK₀ : {Γ : Con}{A B C : Ty Γ}{x : Var Γ C}{γ : ⟦ Γ ⟧C}
      (σ τ ρ : Thin A B)(δ : Thin B C)(δ' : Thin A C)
      (c : Code σ τ)(d : Code τ ρ)(cd : Code σ ρ)
      (e : Code (δ ∘ σ) δ')(e' : Code (δ ∘ τ) δ')(e'' : Code (δ ∘ ρ) δ')(a : ⟦ A ⟧T γ)
      (r : Σ (⟦ C ⟧T γ) (λ d → Σ (⟦ δ' ⟧Th a ≡ d) (λ _ → ⟦ x ⟧V γ d)))
    → ≈K σ τ δ δ' refl refl refl c e e' a r ∙ ≈K τ ρ δ δ' refl refl refl d e' e'' a r ≡ ≈K σ ρ δ δ' refl refl refl cd e e'' a r
TK₀ {C = C} {γ = γ} σ τ ρ δ δ' c d cd e e' e'' a (d₀ , refl , v) =
  pathK-∙≡ (grpdEq (isGrpdT C γ)) (≈ {σ = σ} {τ} c a) (≈ {σ = τ} {ρ} d a) (≈ {σ = σ} {ρ} cd a) _ _ _
           (cohT σ τ ρ c d cd a)
TK σ τ ρ δ δ' refl .refl .refl refl refl w₁₃ c d cd e e' e'' a r =
  subst (λ w → ≈K σ τ δ δ' refl refl refl c e e' a r ∙ ≈K τ ρ δ δ' refl refl refl d e' e'' a r
               ≡ ≈K σ ρ δ δ' refl refl w cd e e'' a r)
        (set→2prop VarΣ-set refl w₁₃)
        (TK₀ σ τ ρ δ δ' c d cd e e' e'' a r)

cohT tε tε tε c d cd a = refl
cohT (t-d σ) (t-d τ) (t-d ρ) c d cd (a , r) = cohT σ τ ρ c d cd a
cohT (t-k {x = x} {y} {δ} {δ'} σ ex e) (t-k τ ex' e') (t-k ρ ex'' e'') c d cd (a , r) =
  TK σ τ ρ δ δ' (CodeV-sound x y ex) (CodeV-sound x y ex') (CodeV-sound x y ex'')
     (VarΣ-set _ _) (VarΣ-set _ _) (VarΣ-set _ _) c d cd e e' e'' a r
cohR = {!!}
cohL = {!!}
cohAs = {!!}
cohWN = {!!}
cohW∘ = {!!}
