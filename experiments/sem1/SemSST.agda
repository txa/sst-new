{-# OPTIONS --cubical -W noUnsupportedIndexedMatch #-}
{-
Sanity check of the semantics of SST n: the standard (unforded)
semi-simplicial groupoids up to level n map into ⟦ SST n ⟧C. The map
transports each entry's value along its stored path into the family
applied to the faces it should select; this typechecks only if every
face map of the construction selects the right lower simplices.
-}
module SemSST where

import TT
open TT using (subst ; sym)
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit
open import Sem1
open Grpd
import SSTk
open SSTk using (SST)

-- level 1: points and edges
record Std₁ : Set₁ where
  field
    X₀ : Grpd
    X₁ : ⌞ X₀ ⌟ → ⌞ X₀ ⌟ → Grpd

-- level 2: and triangles
record Std₂ : Set₁ where
  field
    std₁ : Std₁
  open Std₁ std₁
  field
    X₂ : (x y z : ⌞ X₀ ⌟) → ⌞ X₁ x y ⌟ → ⌞ X₁ x z ⌟ → ⌞ X₁ y z ⌟ → Grpd

-- the components of an entry (a , d , q , v) of a forded telescope
pre : {P : Set}{D : Set}{f : P → D}{V : D → Set} → Σ P (λ a → Σ D (λ d → Σ (f a ≡ d) (λ _ → V d))) → P
pre = fst
val : {P : Set}{D : Set}{f : P → D}{V : D → Set}(t : Σ P (λ a → Σ D (λ d → Σ (f a ≡ d) (λ _ → V d)))) → V (fst (snd t))
val t = snd (snd (snd t))
pth : {P : Set}{D : Set}{f : P → D}{V : D → Set}(t : Σ P (λ a → Σ D (λ d → Σ (f a ≡ d) (λ _ → V d)))) → f (fst t) ≡ fst (snd t)
pth t = fst (snd (snd t))
-- the value transported back to the selected arguments
val' : {P : Set}{D : Set}{f : P → D}{V : D → Set}(t : Σ P (λ a → Σ D (λ d → Σ (f a ≡ d) (λ _ → V d)))) → V (f (fst t))
val' {V = V} t = subst V (sym (pth t)) (val t)

toSem₁ : Std₁ → ⟦ SST 1 ⟧C
toSem₁ S = (tt₁ , λ _ → X₀) , λ e → X₁ (val (fst e)) (val e)
  where open Std₁ S

toSem₂ : Std₂ → ⟦ SST 2 ⟧C
toSem₂ S = γ₂ , λ t → X₂ (x₀ t) (x₁ t) (x₂ t) (tr (fst (fst t))) (tr (fst t)) (tr t)
  where
    open Std₂ S
    open Std₁ std₁
    γ₂ = toSem₁ std₁
    -- the family of the edges, and the value of an edge entry transported to its selected points
    V : _ → Set
    V = ⟦ TT.zero {Γ = SSTk.ctx 1} {A = SSTk.SK 1 2} ⟧V γ₂
    tr : ∀ {P}{f : P → _} → (t : Σ P (λ a → Σ _ (λ d → Σ (f a ≡ d) (λ _ → V d)))) → V (f (fst t))
    tr t = subst V (sym (fst (snd (snd t)))) (snd (snd (snd t)))
    x₀ x₁ x₂ : _ → ⌞ X₀ ⌟
    x₀ t = snd (snd (snd (fst (fst (fst (fst (fst t)))))))
    x₁ t = snd (snd (snd (fst (fst (fst (fst t))))))
    x₂ t = snd (snd (snd (fst (fst (fst t)))))

-- level 3: the faces of a tetrahedron. Checking definitionally that the
-- transported triangle values match is too expensive (Agda would have to
-- normalise the stored paths, which contain the coherence proofs). But in
-- the forded semantics a thinning never changes the point d or the value v
-- of an entry, only its stored path. So it suffices to check that each
-- triangle face selects sub-entries with the right (d , v): points i j k and
-- edges ij ik jk.

dv : {P D : Set}{f : P → D}{V : D → Set} → Σ P (λ a → Σ D (λ d → Σ (f a ≡ d) (λ _ → V d))) → Σ D V
dv E = fst (snd E) , snd (snd (snd E))

sel : {P D : Set}{f : P → D}{V : D → Set} → Σ P (λ a → Σ D (λ d → Σ (f a ≡ d) (λ _ → V d))) → D
sel {f = f} E = f (fst E)

module Check₃ (γ : ⟦ SSTk.ctx 3 ⟧C)(t : ⟦ SSTk.SK 3 4 ⟧T γ) where
  -- the entries of the boundary of a tetrahedron, from the last one
  T₁₂₃ = t ; T₀₂₃ = fst T₁₂₃ ; T₀₁₃ = fst T₀₂₃ ; T₀₁₂ = fst T₀₁₃
  e₂₃ = fst T₀₁₂ ; e₁₃ = fst e₂₃ ; e₀₃ = fst e₁₃ ; e₁₂ = fst e₀₃ ; e₀₂ = fst e₁₂ ; e₀₁ = fst e₀₂
  p₃ = fst e₀₁ ; p₂ = fst p₃ ; p₁ = fst p₂ ; p₀ = fst p₁

  -- each triangle face selects the right points i j k and edges ij ik jk
  _ : (dv (fst (fst (fst (fst (fst (sel T₀₁₂)))))) , dv (fst (fst (fst (fst (sel T₀₁₂))))) , dv (fst (fst (fst (sel T₀₁₂))))
       , dv (fst (fst (sel T₀₁₂))) , dv (fst (sel T₀₁₂)) , dv (sel T₀₁₂))
      ≡ (dv p₀ , dv p₁ , dv p₂ , dv e₀₁ , dv e₀₂ , dv e₁₂)
  _ = refl
  _ : (dv (fst (fst (fst (fst (fst (sel T₀₁₃)))))) , dv (fst (fst (fst (fst (sel T₀₁₃))))) , dv (fst (fst (fst (sel T₀₁₃))))
       , dv (fst (fst (sel T₀₁₃))) , dv (fst (sel T₀₁₃)) , dv (sel T₀₁₃))
      ≡ (dv p₀ , dv p₁ , dv p₃ , dv e₀₁ , dv e₀₃ , dv e₁₃)
  _ = refl
  _ : (dv (fst (fst (fst (fst (fst (sel T₀₂₃)))))) , dv (fst (fst (fst (fst (sel T₀₂₃))))) , dv (fst (fst (fst (sel T₀₂₃))))
       , dv (fst (fst (sel T₀₂₃))) , dv (fst (sel T₀₂₃)) , dv (sel T₀₂₃))
      ≡ (dv p₀ , dv p₂ , dv p₃ , dv e₀₂ , dv e₀₃ , dv e₂₃)
  _ = refl
  _ : (dv (fst (fst (fst (fst (fst (sel T₁₂₃)))))) , dv (fst (fst (fst (fst (sel T₁₂₃))))) , dv (fst (fst (fst (sel T₁₂₃))))
       , dv (fst (fst (sel T₁₂₃))) , dv (fst (sel T₁₂₃)) , dv (sel T₁₂₃))
      ≡ (dv p₁ , dv p₂ , dv p₃ , dv e₁₂ , dv e₁₃ , dv e₂₃)
  _ = refl
