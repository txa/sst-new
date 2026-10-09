{-# OPTIONS --without-K #-}
{-
A HIIT version of the type theory (a variation of Kovács' optimised
syntax): weakening and composition are *constructors*, and their laws
are path constructors. We give the signature as a record of algebras
(Model); the syntax is the initial Model (see HIITConj.agda).

Compared with TT.agda (induction-recursion, where wkTy and _∘_ are
defined functions):
* here the standard model interprets wk and ∘ directly, so every path
  constructor is refl and no K is needed (std below);
* but the syntax is not obviously a set: ass is needed to state t-k∘t-k
  and creates critical pairs with the computation rules.
TT.agda is a model too (HIITtoIR.agda), which gives a map HIIT → IR. The
coherence problem is whether this map is an equivalence.
-}
module HIIT where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit

substℓ : ∀ {i j}{X : Set i}(P : X → Set j){a b : X} → a ≡ b → P a → P b
substℓ P refl y = y

symℓ : ∀ {i}{X : Set i}{a b : X} → a ≡ b → b ≡ a
symℓ refl = refl

record Model (i j : Level) : Set (lsuc (i ⊔ j)) where
  infixl 5 _▷_
  infixr 9 _∘_
  field
    -- sorts
    Con  : Set i
    Ty   : Con → Set j
    Var  : (Γ : Con) → Ty Γ → Set j
    Thin : {Γ : Con} → Ty Γ → Ty Γ → Set j
    -- point constructors
    •    : Con
    _▷_  : (Γ : Con) → Ty Γ → Con
    ε    : {Γ : Con} → Ty Γ
    ext  : {Γ : Con}(A : Ty Γ){B : Ty Γ} → Var Γ B → Thin A B → Ty Γ
    wk   : {Γ : Con}{B : Ty Γ} → Ty Γ → Ty (Γ ▷ B)
    tε   : {Γ : Con} → Thin {Γ} ε ε
    t-d  : {Γ : Con}{A B C : Ty Γ}{x : Var Γ C}{δ : Thin A C}
         → Thin A B → Thin (ext A x δ) B
    _∘_  : {Γ : Con}{A B C : Ty Γ} → Thin B C → Thin A B → Thin A C
    t-k  : {Γ : Con}{A B C : Ty Γ}{x : Var Γ C}{δ : Thin B C}
         → (σ : Thin A B) → Thin (ext A x (δ ∘ σ)) (ext B x δ)
    wkThin : {Γ : Con}{B : Ty Γ}{A A' : Ty Γ}
           → Thin A A' → Thin {Γ ▷ B} (wk A) (wk A')
    zero : {Γ : Con}{A : Ty Γ} → Var (Γ ▷ A) (wk A)
    suc  : {Γ : Con}{A B : Ty Γ} → Var Γ A → Var (Γ ▷ B) (wk A)
    -- path constructors: weakening
    wkε   : {Γ : Con}{B : Ty Γ} → wk {Γ}{B} ε ≡ ε
    wkext : {Γ : Con}{B A C : Ty Γ}{x : Var Γ C}{δ : Thin A C}
          → wk {Γ}{B} (ext A x δ) ≡ ext (wk A) (suc x) (wkThin δ)
    -- path constructors: composition
    ass   : {Γ : Con}{A B C D : Ty Γ}{ρ : Thin C D}{δ : Thin B C}{σ : Thin A B}
          → (ρ ∘ δ) ∘ σ ≡ ρ ∘ (δ ∘ σ)
    ∘tε   : {Γ : Con}{C : Ty Γ}{δ : Thin ε C} → δ ∘ tε ≡ δ
    ∘t-d  : {Γ : Con}{A B C D : Ty Γ}{x : Var Γ D}{δA : Thin A D}
            {δ : Thin B C}{σ : Thin A B}
          → δ ∘ t-d {x = x}{δ = δA} σ ≡ t-d (δ ∘ σ)
    t-d∘t-k : {Γ : Con}{A B C D : Ty Γ}{x : Var Γ D}{δB : Thin B D}
              {δ : Thin B C}{σ : Thin A B}
            → t-d δ ∘ t-k {x = x}{δ = δB} σ ≡ t-d (δ ∘ σ)
    -- composing two keeps re-associates the index: a path over ass
    t-k∘t-k : {Γ : Con}{A B C D : Ty Γ}{x : Var Γ D}{ρ : Thin C D}
              {δ : Thin B C}{σ : Thin A B}
            → substℓ (λ d → Thin (ext A x d) (ext C x ρ)) ass (t-k δ ∘ t-k σ)
              ≡ t-k (δ ∘ σ)
    -- path constructors: weakening of thinnings
    wktε  : {Γ : Con}{B : Ty Γ}
          → substℓ (λ T → Thin {Γ ▷ B} T T) wkε (wkThin tε) ≡ tε
    wk∘   : {Γ : Con}{B : Ty Γ}{A A' A'' : Ty Γ}{δ : Thin A' A''}{σ : Thin A A'}
          → wkThin {B = B} (δ ∘ σ) ≡ wkThin δ ∘ wkThin σ
    wkt-d : {Γ : Con}{B : Ty Γ}{A A' C : Ty Γ}{x : Var Γ C}{δ : Thin A C}{σ : Thin A A'}
          → substℓ (λ T → Thin {Γ ▷ B} T (wk A')) wkext (wkThin (t-d {x = x}{δ = δ} σ))
            ≡ t-d (wkThin σ)
    wkt-k : {Γ : Con}{B : Ty Γ}{A A' C : Ty Γ}{x : Var Γ C}{δ : Thin A' C}{σ : Thin A A'}
          → substℓ (λ T → Thin {Γ ▷ B} T (ext (wk A') (suc x) (wkThin δ))) (wkext {δ = δ ∘ σ})
              (substℓ (λ T → Thin {Γ ▷ B} (wk (ext A x (δ ∘ σ))) T) wkext
                      (wkThin (t-k {x = x}{δ = δ} σ)))
            ≡ substℓ (λ d → Thin (ext (wk A) (suc x) d) (ext (wk A') (suc x) (wkThin δ)))
                     (symℓ wk∘) (t-k (wkThin σ))

-- the standard model: everything is refl, no K -----------------------

record ⊤₁ : Set₁ where
  constructor tt₁

std : Model (lsuc (lsuc lzero)) (lsuc lzero)
std = record
  { Con = Set₁
  ; Ty = λ Γ → Γ → Set
  ; Var = λ Γ A → (γ : Γ) → A γ → Set
  ; Thin = λ {Γ} A B → {γ : Γ} → A γ → B γ
  ; • = ⊤₁
  ; _▷_ = λ Γ A → Σ Γ (λ γ → A γ → Set)
  ; ε = λ _ → ⊤
  ; ext = λ A x δ γ → Σ (A γ) (λ a → x γ (δ a))
  ; wk = λ A γ → A (fst γ)
  ; tε = λ _ → tt
  ; t-d = λ σ a → σ (fst a)
  ; _∘_ = λ δ σ a → δ (σ a)
  ; t-k = λ σ a → σ (fst a) , snd a          -- no transport needed
  ; wkThin = λ σ a → σ a
  ; zero = λ γ b → snd γ b                   -- no unwk needed
  ; suc = λ x γ b → x (fst γ) b
  ; wkε = refl ; wkext = refl ; ass = refl ; ∘tε = refl ; ∘t-d = refl
  ; t-d∘t-k = refl ; t-k∘t-k = refl
  ; wktε = refl ; wk∘ = refl ; wkt-d = refl ; wkt-k = refl
  }
