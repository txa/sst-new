{-# OPTIONS --with-K #-}
{-
The only file using K. It proves pair-irr (= UIP for the semantic types)
by K and instantiates the K-free interpretation Sem.agda with it.

K is used only in the definition of pair-irr below (the last pattern,
β = refl, deletes a reflexive equation c ≡ f u₁).
-}
module SemK where

open import TT
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit

-- uses K: after matching α = refl, matching β : f u₁ ≡ f u₁ with refl
-- needs to delete a reflexive equation
pair-irr : {U D : Set}{f : U → D}{P : D → Set}{u₁ u₂ : U}
           {v₁ : P (f u₁)}{v₂ : P (f u₂)}{c : D}{y : P c}
         → u₁ ≡ u₂ → (α : c ≡ f u₁)(β : c ≡ f u₂)
         → v₁ ≡ subst P α y → v₂ ≡ subst P β y
         → _≡_ {A = Σ U (λ u → P (f u))} (u₁ , v₁) (u₂ , v₂)
pair-irr refl refl refl refl refl = refl

open import Sem pair-irr public

-- tests ---------------------------------------------------------------

open import SST using (Γ₁; A₂)
open import SSTk using (SST)
open import Agda.Builtin.Nat using (Nat)

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
SSTSet : Nat → Set₁
SSTSet n = ⟦ SST n ⟧C

-- level 1: X₀ : Set and X₁ : X₀ → X₀ → Set (uncurried, with ⊤'s)
_ : SSTSet 1 ≡ Σ (Σ ⊤₁ (λ _ → ⊤ → Set))
                 (λ γ → Σ (Σ ⊤ (λ _ → snd γ tt)) (λ _ → snd γ tt) → Set)
_ = refl
