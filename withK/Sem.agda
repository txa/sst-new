{-
The standard interpretation of the syntax in Agda's Set:

  ⟦ Γ ⟧C : Set₁                       -- a sequence of type families
  ⟦ A ⟧T : ⟦ Γ ⟧C → Set               -- the domain of a family
  ⟦ x ⟧V : (γ : ⟦ Γ ⟧C) → ⟦ A ⟧T γ → Set
  ⟦ σ ⟧Th : ⟦ A ⟧T γ → ⟦ B ⟧T γ        -- projections

Weakening is interpreted by a map unwk : ⟦ wkTy A p ⟧T (γ , X) → ⟦ A ⟧T γ
(rather than an equation between types, which would need funext), and
t-k transports along the stored equation. Uses K (pair-irr), like TT.agda.
For closed syntax all the proofs compute to refl, so e.g. ⟦ SST n ⟧C
for a numeral n is the expected nested Σ-type (see the test at the end).
-}
module Sem where

open import TT
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit

record ⊤₁ : Set₁ where
  constructor tt₁

-- transport ----------------------------------------------------------

subst : {X : Set}(P : X → Set){a b : X} → a ≡ b → P a → P b
subst P refl y = y

infixr 5 _∙_
_∙_ : {X : Set}{a b c : X} → a ≡ b → b ≡ c → a ≡ c
refl ∙ q = q

subst-subst : {X : Set}(P : X → Set){a b c : X}(r : a ≡ b)(q : b ≡ c)(y : P a)
            → subst P q (subst P r y) ≡ subst P (r ∙ q) y
subst-subst P refl refl y = refl

subst-∘ : {X Y : Set}(P : Y → Set)(g : X → Y){a b : X}(r : a ≡ b)(y : P (g a))
        → subst (λ x → P (g x)) r y ≡ subst P (cong g r) y
subst-∘ P g refl y = refl

-- equality of pairs whose second components are transports of the same y
pair-irr : {U D : Set}{f : U → D}{P : D → Set}{u₁ u₂ : U}
           {v₁ : P (f u₁)}{v₂ : P (f u₂)}{c : D}{y : P c}
         → u₁ ≡ u₂ → (α : c ≡ f u₁)(β : c ≡ f u₂)
         → v₁ ≡ subst P α y → v₂ ≡ subst P β y
         → _≡_ {A = Σ U (λ u → P (f u))} (u₁ , v₁) (u₂ , v₂)
pair-irr refl refl refl refl refl = refl

-- the interpretation -------------------------------------------------

-- Termination: the recursion is on the context first and then on the
-- syntax, but the type of unwk mentions ⟦ wkTy A p ⟧T at the longer
-- context Γ ▷ B, and wkTy A p is not a structural subterm, so Agda's
-- checker cannot see it. Hence TERMINATING for this block only.

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
-- the equation stored in t-k, semantically
keq : {Γ : Con}{A B C : Ty Γ}{δ : Thin B C}{σ : Thin A B}{δ' : Thin A C} → δ ∘ σ ≡ δ'
    → {γ : ⟦ Γ ⟧C}(a : ⟦ A ⟧T γ) → ⟦ δ' ⟧Th a ≡ ⟦ δ ⟧Th (⟦ σ ⟧Th a)
keq {δ = δ}{σ} refl a = ⟦∘⟧ δ σ a

⟦ ε ⟧T γ = ⊤
⟦ ext A x δ ⟧T γ = Σ (⟦ A ⟧T γ) (λ a → ⟦ x ⟧V γ (⟦ δ ⟧Th a))

-- recursion on the context: unwk B works in the shorter context Γ
⟦_⟧V {Γ ▷ B} zero (γ , X) b = X (unwk B b)
⟦_⟧V {Γ ▷ B} (suc {A = A} x) (γ , X) b = ⟦ x ⟧V γ (unwk A b)

⟦ tε ⟧Th a = tt
⟦ t-d σ ⟧Th (a , y) = ⟦ σ ⟧Th a
⟦ t-k {x = x}{δ = δ} σ e ⟧Th {γ} (a , y) =
  ⟦ σ ⟧Th a , subst (⟦ x ⟧V γ) (keq {δ = δ}{σ = σ} e a) y

unwk ε b = tt
unwk (ext A x δ) {γ = γ} (a , y) = unwk A a , subst (⟦ x ⟧V γ) (unwk-nat δ a) y

unwk-nat tε a = refl
unwk-nat (t-d σ) (a , y) = unwk-nat σ a
unwk-nat {C = ext B _ δ} (t-k {x = x}{δ' = δ'} σ e) {γ = γ} (a , y) =
  pair-irr {f = ⟦ δ ⟧Th}{P = ⟦ x ⟧V γ} (unwk-nat σ a)
    (cong (unwk _) (keq {δ = wkThin δ p}{σ = wkThin σ p} (wk-k {δ = δ}{σ = σ} p e) a)
     ∙ unwk-nat δ (⟦ wkThin σ p ⟧Th a))
    (unwk-nat δ' a ∙ keq {δ = δ}{σ = σ} e (unwk _ a))
    (cong (subst (⟦ x ⟧V γ) (unwk-nat δ (⟦ wkThin σ p ⟧Th a)))
          (subst-∘ (⟦ x ⟧V γ) (unwk _)
                   (keq {δ = wkThin δ p}{σ = wkThin σ p} (wk-k {δ = δ}{σ = σ} p e) a) y)
     ∙ subst-subst (⟦ x ⟧V γ)
         (cong (unwk _) (keq {δ = wkThin δ p}{σ = wkThin σ p} (wk-k {δ = δ}{σ = σ} p e) a))
         (unwk-nat δ (⟦ wkThin σ p ⟧Th a)) y)
    (subst-subst (⟦ x ⟧V γ) (unwk-nat δ' a) (keq {δ = δ}{σ = σ} e (unwk _ a)) y)

⟦∘⟧ δ tε a = refl
⟦∘⟧ δ (t-d σ) (a , y) = ⟦∘⟧ δ σ a
⟦∘⟧ (t-d δ) (t-k σ e) (a , y) = ⟦∘⟧ δ σ a
⟦∘⟧ (t-k {x = x}{δ = δC} δ q) (t-k {δ = δB} σ e) {γ} (a , y) =
  pair-irr {f = ⟦ δC ⟧Th}{P = ⟦ x ⟧V γ} (⟦∘⟧ δ σ a)
    (keq {δ = δC}{σ = δ ∘ σ} (∘-k q e) a)
    (keq {δ = δB}{σ = σ} e a ∙ keq {δ = δC}{σ = δ} q (⟦ σ ⟧Th a))
    refl
    (subst-subst (⟦ x ⟧V γ) (keq {δ = δB}{σ = σ} e a) (keq {δ = δC}{σ = δ} q (⟦ σ ⟧Th a)) y)

-- tests ---------------------------------------------------------------

open import SST using (Γ₁; A₂)

-- with X₀ and X₁ given, the domain of X₂ is: 3 points and 3 edges
module _ (X₀ : Set)(X₁ : X₀ → X₀ → Set) where

  γ₁ : ⟦ Γ₁ ⟧C
  γ₁ = (tt₁ , λ _ → X₀) , λ v → X₁ (snd (fst v)) (snd v)

  -- points x₀ x₁ x₂, then the edges x₀₁, x₀₂, x₁₂
  P₃ = Σ (Σ (Σ ⊤ (λ _ → X₀)) (λ _ → X₀)) (λ _ → X₀)
  E₀₁ = Σ P₃ (λ v → X₁ (snd (fst (fst v))) (snd (fst v)))
  E₀₂ = Σ E₀₁ (λ w → X₁ (snd (fst (fst (fst w)))) (snd (fst w)))
  E₁₂ = Σ E₀₂ (λ u → X₁ (snd (fst (fst (fst u)))) (snd (fst (fst u))))

  _ : ⟦ A₂ ⟧T γ₁ ≡ E₁₂
  _ = refl

-- the type of semi-simplicial types up to level n
open import SSTk using (SST)
open import Agda.Builtin.Nat using (Nat)

SSTSet : Nat → Set₁
SSTSet n = ⟦ SST n ⟧C

-- level 1: X₀ : Set and X₁ : X₀ → X₀ → Set (uncurried, with ⊤'s)
_ : SSTSet 1 ≡ Σ (Σ ⊤₁ (λ _ → ⊤ → Set))
                 (λ γ → Σ (Σ ⊤ (λ _ → snd γ tt)) (λ _ → snd γ tt) → Set)
_ = refl
