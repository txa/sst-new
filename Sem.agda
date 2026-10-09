{-# OPTIONS --without-K #-}
{-
The standard interpretation of the syntax in Agda's Set:

  ⟦ Γ ⟧C : Set₁                       -- a sequence of type families
  ⟦ A ⟧T : ⟦ Γ ⟧C → Set               -- the domain of a family
  ⟦ x ⟧V : (γ : ⟦ Γ ⟧C) → ⟦ A ⟧T γ → Set
  ⟦ σ ⟧Th : ⟦ A ⟧T γ → ⟦ B ⟧T γ        -- projections

This file does NOT use K. The only principle beyond MLTT is pair-irr,
taken as a module parameter. It is UIP for the *semantic* types ⟦ C ⟧T γ
(pair-irr implies UIP, see experiments/hit), and it is needed exactly
twice: in unwk-nat-k and in comp-k (marked "uses K" below). SemK.agda
proves pair-irr with K and instantiates this module.

Everything about the syntax is K-free: codes are turned into equations
by CodeV-sound / Code-sound, and the total space of variables is a set
by VarΣ-set (both in TT.agda).

Weakening is interpreted by a map unwk : ⟦ wkTy A p ⟧T (γ , X) → ⟦ A ⟧T γ
(rather than an equation between types, which would need funext), and
t-k transports along the stored code.
-}

open import TT
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit

module Sem
  -- equality of pairs whose second components are transports of the same y.
  -- Equivalent to UIP; this is the only place where K enters.
  (pair-irr : {U D : Set}{f : U → D}{P : D → Set}{u₁ u₂ : U}
              {v₁ : P (f u₁)}{v₂ : P (f u₂)}{c : D}{y : P c}
            → u₁ ≡ u₂ → (α : c ≡ f u₁)(β : c ≡ f u₂)
            → v₁ ≡ subst P α y → v₂ ≡ subst P β y
            → _≡_ {A = Σ U (λ u → P (f u))} (u₁ , v₁) (u₂ , v₂))
  where

record ⊤₁ : Set₁ where
  constructor tt₁

-- transport (all without K) ---------------------------------------------

subst-subst : {X : Set}(P : X → Set){a b c : X}(r : a ≡ b)(q : b ≡ c)(y : P a)
            → subst P q (subst P r y) ≡ subst P (r ∙ q) y
subst-subst P refl refl y = refl

subst-∘ : {X Y : Set}(P : Y → Set)(g : X → Y){a b : X}(r : a ≡ b)(y : P (g a))
        → subst (λ x → P (g x)) r y ≡ subst P (cong g r) y
subst-∘ P g refl y = refl

-- the interpretation -------------------------------------------------

-- Termination (not related to K): the recursion is on the context first
-- and then on the syntax, but the type of unwk mentions ⟦ wkTy A p ⟧T at
-- the longer context Γ ▷ B, and wkTy A p is not a structural subterm, so
-- Agda's checker cannot see it. Hence TERMINATING for this block only.

⟦_⟧C : Con → Set₁
{-# TERMINATING #-}
⟦_⟧T : {Γ : Con} → Ty Γ → ⟦ Γ ⟧C → Set
⟦ • ⟧C = ⊤₁
⟦ Γ ▷ A ⟧C = Σ ⟦ Γ ⟧C (λ γ → ⟦ A ⟧T γ → Set)

{-# TERMINATING #-}
⟦_⟧V : {Γ : Con}{A : Ty Γ} → Var Γ A → (γ : ⟦ Γ ⟧C) → ⟦ A ⟧T γ → Set
⟦_⟧Th : {Γ : Con}{A B : Ty Γ} → Thin A B → {γ : ⟦ Γ ⟧C} → ⟦ A ⟧T γ → ⟦ B ⟧T γ

-- semantics of weakening by p
{-# TERMINATING #-}
unwk : {Γ : Con}(A : Ty Γ){B : Ty Γ}{γ : ⟦ Γ ⟧C}{X : ⟦ B ⟧T γ → Set}
     → ⟦ wkTy A (p {A = B}) ⟧T (γ , X) → ⟦ A ⟧T γ
{-# TERMINATING #-}
unwk-nat : {Γ : Con}{A C : Ty Γ}(δ : Thin A C){B : Ty Γ}{γ : ⟦ Γ ⟧C}{X : ⟦ B ⟧T γ → Set}
           (a : ⟦ wkTy A (p {A = B}) ⟧T (γ , X))
         → unwk C (⟦ wkThin δ p ⟧Th a) ≡ ⟦ δ ⟧Th (unwk A a)

-- semantics of composition
⟦∘⟧ : {Γ : Con}{A B C : Ty Γ}(δ : Thin B C)(σ : Thin A B){γ : ⟦ Γ ⟧C}(a : ⟦ A ⟧T γ)
    → ⟦ δ ∘ σ ⟧Th a ≡ ⟦ δ ⟧Th (⟦ σ ⟧Th a)
-- an equation between thinnings, semantically
keq : {Γ : Con}{A B C : Ty Γ}{δ : Thin B C}{σ : Thin A B}{δ' : Thin A C} → δ ∘ σ ≡ δ'
    → {γ : ⟦ Γ ⟧C}(a : ⟦ A ⟧T γ) → ⟦ δ' ⟧Th a ≡ ⟦ δ ⟧Th (⟦ σ ⟧Th a)
keq {δ = δ}{σ} refl a = ⟦∘⟧ δ σ a

-- the second component of a kept entry: first identify the source and
-- target variables (path induction on the decoded code, no K), then
-- transport along the decoded code of the commuting square
kt : {Γ : Con}{A B C C' : Ty Γ}{x : Var Γ C}{y : Var Γ C'}{γ : ⟦ Γ ⟧C}
     (σ : Thin A B)(δ : Thin B C')(δ' : Thin A C)
   → _≡_ {A = VarΣ Γ} (C , x) (C' , y) → Code (δ ∘ σ) δ'
   → (a : ⟦ A ⟧T γ) → ⟦ x ⟧V γ (⟦ δ' ⟧Th a) → ⟦ y ⟧V γ (⟦ δ ⟧Th (⟦ σ ⟧Th a))
kt {x = x}{γ = γ} σ δ δ' refl e a v =
  subst (⟦ x ⟧V γ) (keq {δ = δ}{σ = σ} (Code-sound (δ ∘ σ) δ' e) a) v

⟦ ε ⟧T γ = ⊤
⟦ ext A x δ ⟧T γ = Σ (⟦ A ⟧T γ) (λ a → ⟦ x ⟧V γ (⟦ δ ⟧Th a))

-- recursion on the context: unwk B works in the shorter context Γ
⟦_⟧V {Γ ▷ B} zero (γ , X) b = X (unwk B b)
⟦_⟧V {Γ ▷ B} (suc {A = A} x) (γ , X) b = ⟦ x ⟧V γ (unwk A b)

⟦ tε ⟧Th a = tt
⟦ t-d σ ⟧Th (a , v) = ⟦ σ ⟧Th a
⟦ t-k {x = x}{y = y}{δ = δ}{δ' = δ'} σ ex e ⟧Th {γ} (a , v) =
  ⟦ σ ⟧Th a , kt σ δ δ' (CodeV-sound x y ex) e a v

unwk ε b = tt
unwk (ext A x δ) {γ = γ} (a , v) = unwk A a , subst (⟦ x ⟧V γ) (unwk-nat δ a) v

-- naturality of unwk for a kept entry, with the decoded variable code
-- abstracted so that we can do path induction on it
unwk-nat-k : {Γ : Con}{A B C C' B₀ : Ty Γ}{x : Var Γ C}{y : Var Γ C'}
             (σ : Thin A B)(δ : Thin B C')(δ' : Thin A C)
             (p₀ : _≡_ {A = VarΣ Γ} (C , x) (C' , y))
             (e : Code (δ ∘ σ) δ')
             (e₁ : Code (wkThin δ (p {A = B₀}) ∘ wkThin σ p) (wkThin δ' p))
             {γ : ⟦ Γ ⟧C}{X : ⟦ B₀ ⟧T γ → Set}
             (a : ⟦ wkTy A (p {A = B₀}) ⟧T (γ , X))(v : ⟦ x ⟧V γ (unwk C (⟦ wkThin δ' p ⟧Th a)))
           → _≡_ {A = ⟦ ext B y δ ⟧T γ}
               (unwk B (⟦ wkThin σ p ⟧Th a) ,
                subst (⟦ y ⟧V γ) (unwk-nat δ (⟦ wkThin σ p ⟧Th a))
                      (kt (wkThin σ p) (wkThin δ p) (wkThin δ' p) (cong (sucΣ {B = B₀}) p₀) e₁ a v))
               (⟦ σ ⟧Th (unwk A a) ,
                kt σ δ δ' p₀ e (unwk A a) (subst (⟦ x ⟧V γ) (unwk-nat δ' a) v))
-- uses K (via pair-irr): two different transports of v must agree
unwk-nat-k {C = C}{x = x} σ δ δ' refl e e₁ {γ = γ} a v =
  pair-irr {f = ⟦ δ ⟧Th}{P = ⟦ x ⟧V γ} (unwk-nat σ a)
    (cong (unwk C) (keq {δ = wkThin δ p}{σ = wkThin σ p} (Code-sound _ _ e₁) a)
     ∙ unwk-nat δ (⟦ wkThin σ p ⟧Th a))
    (unwk-nat δ' a ∙ keq {δ = δ}{σ = σ} (Code-sound _ _ e) (unwk _ a))
    (cong (subst (⟦ x ⟧V γ) (unwk-nat δ (⟦ wkThin σ p ⟧Th a)))
          (subst-∘ (⟦ x ⟧V γ) (unwk C)
                   (keq {δ = wkThin δ p}{σ = wkThin σ p} (Code-sound _ _ e₁) a) v)
     ∙ subst-subst (⟦ x ⟧V γ)
         (cong (unwk C) (keq {δ = wkThin δ p}{σ = wkThin σ p} (Code-sound _ _ e₁) a))
         (unwk-nat δ (⟦ wkThin σ p ⟧Th a)) v)
    (subst-subst (⟦ x ⟧V γ) (unwk-nat δ' a) (keq {δ = δ}{σ = σ} (Code-sound _ _ e) (unwk _ a)) v)

unwk-nat tε a = refl
unwk-nat (t-d σ) (a , v) = unwk-nat σ a
unwk-nat {C = ext B y δ} (t-k {x = x}{δ' = δ'} σ ex e) (a , v) =
  unwk-nat-k σ δ δ' (CodeV-sound x y ex) e _ a v

-- composition of two kept entries, with all decoded variable codes abstracted
comp-k : {Γ : Con}{A B C D₁ D₂ D₃ : Ty Γ}{x : Var Γ D₁}{y : Var Γ D₂}{z : Var Γ D₃}
         (δ : Thin B C)(σ : Thin A B)(δC : Thin C D₃)(δB : Thin B D₂)(δA : Thin A D₁)
         (pxy : _≡_ {A = VarΣ Γ} (D₁ , x) (D₂ , y))(pyz : _≡_ {A = VarΣ Γ} (D₂ , y) (D₃ , z))
         (pxz : _≡_ {A = VarΣ Γ} (D₁ , x) (D₃ , z))
         (q : Code (δC ∘ δ) δB)(e : Code (δB ∘ σ) δA)(e' : Code (δC ∘ (δ ∘ σ)) δA)
         {γ : ⟦ Γ ⟧C}(a : ⟦ A ⟧T γ)(v : ⟦ x ⟧V γ (⟦ δA ⟧Th a))
       → _≡_ {A = ⟦ ext C z δC ⟧T γ}
           (⟦ δ ∘ σ ⟧Th a , kt (δ ∘ σ) δC δA pxz e' a v)
           (⟦ δ ⟧Th (⟦ σ ⟧Th a) , kt δ δC δB pyz q (⟦ σ ⟧Th a) (kt σ δB δA pxy e a v))
comp-k {x = x} δ σ δC δB δA refl refl pxz q e e' {γ} a v =
  -- the loop pxz is refl because variables form a set (no K)
  subst (λ r → _≡_ {A = ⟦ ext _ x δC ⟧T γ}
                   (⟦ δ ∘ σ ⟧Th a , kt (δ ∘ σ) δC δA r e' a v)
                   (⟦ δ ⟧Th (⟦ σ ⟧Th a) , kt δ δC δB refl q (⟦ σ ⟧Th a) (kt σ δB δA refl e a v)))
        (VarΣ-set refl pxz)
    -- uses K (via pair-irr): two different transports of v must agree
    (pair-irr {f = ⟦ δC ⟧Th}{P = ⟦ x ⟧V γ} (⟦∘⟧ δ σ a)
       (keq {δ = δC}{σ = δ ∘ σ} (Code-sound _ _ e') a)
       (keq {δ = δB}{σ = σ} (Code-sound _ _ e) a ∙ keq {δ = δC}{σ = δ} (Code-sound _ _ q) (⟦ σ ⟧Th a))
       refl
       (subst-subst (⟦ x ⟧V γ) (keq {δ = δB}{σ = σ} (Code-sound _ _ e) a)
                    (keq {δ = δC}{σ = δ} (Code-sound _ _ q) (⟦ σ ⟧Th a)) v))

⟦∘⟧ δ tε a = refl
⟦∘⟧ δ (t-d σ) (a , v) = ⟦∘⟧ δ σ a
⟦∘⟧ (t-d δ) (t-k σ ex e) (a , v) = ⟦∘⟧ δ σ a
⟦∘⟧ (t-k {x = y}{y = z}{δ = δC}{δ' = δB} δ ey q) (t-k {x = x}{δ' = δA} σ ex e) (a , v) =
  comp-k δ σ δC δB δA (CodeV-sound x y ex) (CodeV-sound y z ey)
         (CodeV-sound x z (CodeV-trans x y z ex ey)) q e _ a v
