{-# OPTIONS --without-K #-}
{-
Experiment: make semantic composition definitional by making composition
of thinnings a *constructor*, and store in t-k a proof-relevant syntactic
derivation  e : δ' ≈ δ ∘ σ  instead of a (propositional) equation.

To isolate the issue, contexts and weakening are left out: the entries of
a telescope are semantic families X : ⟦ B ⟧ → Set (induction-recursion).

RESULT: everything is interpreted without K (⟦∘⟧ is gone, β-kk is plain
path algebra) except t-k-cong, which identifies t-k σ e and t-k σ' e' for
*unrelated* derivations e, e'. Its semantics needs the 2-cell
  ⟦ e ⟧≈ a ∙ cong ⟦ δ ⟧Th (⟦ d ⟧≈ a) ≡ ⟦ e' ⟧≈ a,
i.e. pair-irr. Giving t-k-cong a 2-dimensional premise relating e' to
e and d would make it interpretable, but then the syntax needs a
2-dimensional ≈₂ with its own congruences, and so on: the tower moves
into the syntax.
-}
module FreeComp where

open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit

-- path algebra (all without K)
subst : {X : Set}(P : X → Set){a b : X} → a ≡ b → P a → P b
subst P refl y = y

cong : {X Y : Set}(f : X → Y){a b : X} → a ≡ b → f a ≡ f b
cong f refl = refl

sym : {X : Set}{a b : X} → a ≡ b → b ≡ a
sym refl = refl

infixr 5 _∙_
_∙_ : {X : Set}{a b c : X} → a ≡ b → b ≡ c → a ≡ c
refl ∙ q = q

subst-subst : {X : Set}(P : X → Set){a b c : X}(r : a ≡ b)(q : b ≡ c)(y : P a)
            → subst P q (subst P r y) ≡ subst P (r ∙ q) y
subst-subst P refl refl y = refl

∙-refl : {X : Set}{a b : X}(p : a ≡ b) → p ∙ refl ≡ p
∙-refl refl = refl

-- syntax and semantics, simultaneously -------------------------------

data Tel : Set₁
⟦_⟧ : Tel → Set
data Thin : Tel → Tel → Set₁
⟦_⟧Th : {A B : Tel} → Thin A B → ⟦ A ⟧ → ⟦ B ⟧
data _≈_ : {A B : Tel} → Thin A B → Thin A B → Set₁
⟦_⟧≈ : {A B : Tel}{σ σ' : Thin A B} → σ ≈ σ' → (a : ⟦ A ⟧) → ⟦ σ ⟧Th a ≡ ⟦ σ' ⟧Th a

data Tel where
  ε : Tel
  ext : (A B : Tel)(X : ⟦ B ⟧ → Set) → Thin A B → Tel

infixr 9 _∘_
data Thin where
  _∘_ : {A B C : Tel} → Thin B C → Thin A B → Thin A C
  tε : Thin ε ε
  t-d : {A B C : Tel}{X : ⟦ C ⟧ → Set}{δ : Thin A C}
      → Thin A B → Thin (ext A C X δ) B
  t-k : {A B C : Tel}{X : ⟦ C ⟧ → Set}{δ : Thin B C}{δ' : Thin A C}
      → (σ : Thin A B) → δ' ≈ (δ ∘ σ) → Thin (ext A C X δ') (ext B C X δ)

data _≈_ where
  rfl : {A B : Tel}{σ : Thin A B} → σ ≈ σ
  sym≈ : {A B : Tel}{σ σ' : Thin A B} → σ ≈ σ' → σ' ≈ σ
  trans≈ : {A B : Tel}{σ σ' σ'' : Thin A B} → σ ≈ σ' → σ' ≈ σ'' → σ ≈ σ''
  ∘-cong : {A B C : Tel}{δ δ' : Thin B C}{σ σ' : Thin A B}
         → δ ≈ δ' → σ ≈ σ' → (δ ∘ σ) ≈ (δ' ∘ σ')
  assoc : {A B C D : Tel}{ρ : Thin C D}{δ : Thin B C}{σ : Thin A B}
        → ((ρ ∘ δ) ∘ σ) ≈ (ρ ∘ (δ ∘ σ))
  t-d-cong : {A B C : Tel}{X : ⟦ C ⟧ → Set}{δ : Thin A C}{σ σ' : Thin A B}
           → σ ≈ σ' → t-d {X = X}{δ = δ} σ ≈ t-d σ'
  -- computation rules for ∘
  β-ε : {C : Tel}{δ : Thin ε C} → (δ ∘ tε) ≈ δ
  β-d : {A B C D : Tel}{X : ⟦ D ⟧ → Set}{δA : Thin A D}{δ : Thin B C}{σ : Thin A B}
      → (δ ∘ t-d {X = X}{δ = δA} σ) ≈ t-d (δ ∘ σ)
  β-dk : {A B C D : Tel}{X : ⟦ D ⟧ → Set}{δB : Thin B D}{δA : Thin A D}
         {δ : Thin B C}{σ : Thin A B}{e : δA ≈ (δB ∘ σ)}
       → (t-d δ ∘ t-k {X = X} σ e) ≈ t-d (δ ∘ σ)
  β-kk : {A B C D : Tel}{X : ⟦ D ⟧ → Set}{δC : Thin C D}{δB : Thin B D}{δA : Thin A D}
         {δ : Thin B C}{σ : Thin A B}{q : δB ≈ (δC ∘ δ)}{e : δA ≈ (δB ∘ σ)}
       → (t-k {X = X} δ q ∘ t-k σ e) ≈ t-k (δ ∘ σ) (trans≈ e (trans≈ (∘-cong q rfl) assoc))
  -- congruence for t-k with *unrelated* derivations e, e'
  t-k-cong : {A B C : Tel}{X : ⟦ C ⟧ → Set}{δ : Thin B C}{δ' : Thin A C}
             {σ σ' : Thin A B}{e : δ' ≈ (δ ∘ σ)}{e' : δ' ≈ (δ ∘ σ')}
           → σ ≈ σ' → t-k {X = X} σ e ≈ t-k σ' e'

⟦ ε ⟧ = ⊤
⟦ ext A B X δ ⟧ = Σ ⟦ A ⟧ (λ a → X (⟦ δ ⟧Th a))

⟦ δ ∘ σ ⟧Th a = ⟦ δ ⟧Th (⟦ σ ⟧Th a)          -- definitional: no ⟦∘⟧ lemma
⟦ tε ⟧Th a = tt
⟦ t-d σ ⟧Th (a , y) = ⟦ σ ⟧Th a
⟦ t-k {X = X} σ e ⟧Th (a , y) = ⟦ σ ⟧Th a , subst X (⟦ e ⟧≈ a) y

⟦ rfl ⟧≈ a = refl
⟦ sym≈ d ⟧≈ a = sym (⟦ d ⟧≈ a)
⟦ trans≈ d d' ⟧≈ a = ⟦ d ⟧≈ a ∙ ⟦ d' ⟧≈ a
⟦ ∘-cong {δ' = δ'}{σ = σ} d d' ⟧≈ a = ⟦ d ⟧≈ (⟦ σ ⟧Th a) ∙ cong ⟦ δ' ⟧Th (⟦ d' ⟧≈ a)
⟦ assoc ⟧≈ a = refl
⟦ t-d-cong d ⟧≈ (a , y) = ⟦ d ⟧≈ a
⟦ β-ε ⟧≈ a = refl
⟦ β-d ⟧≈ (a , y) = refl
⟦ β-dk ⟧≈ (a , y) = refl
⟦ β-kk {X = X}{δ = δ}{σ = σ}{q = q}{e = e} ⟧≈ (a , y) =
  cong (⟦ δ ⟧Th (⟦ σ ⟧Th a) ,_)
       (subst-subst X (⟦ e ⟧≈ a) (⟦ q ⟧≈ (⟦ σ ⟧Th a)) y
        ∙ cong (λ r → subst X (⟦ e ⟧≈ a ∙ r) y)
               (sym (cong (_∙ refl) (∙-refl (⟦ q ⟧≈ (⟦ σ ⟧Th a))) ∙ ∙-refl _)))
-- this would need  ⟦ e ⟧≈ a ∙ cong ⟦ δ ⟧Th (⟦ d ⟧≈ a) ≡ ⟦ e' ⟧≈ a,
-- a 2-cell between unrelated derivations: exactly pair-irr / UIP
⟦ t-k-cong d ⟧≈ (a , y) = {!!}
