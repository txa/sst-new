{-
Define a TT to represent semi-simplicial types upto a fixed level
(but also semi-cubical, ...)

we define TT as an inductive-inductive recursive type (no truncation)
using Szumi's trick 

We use a 2-level theory
Con are sequences of type families
Ty : Con → Set : is the domain of a family
Thin : {Γ : Con} → Ty Γ → Ty Γ → Set , is the set of thinnings, ie injective variable substitutions
Var : (Γ : Con)(A : Ty Γ) → Set

Con is a sequence of Ty depending on the previous context

A : Ty Γ  is a sequence of assumptions of the form x : Var Γ A'
with a thinning δ : A → A'

Question how to present 
Var = typed debruijn indices? We need to define a weak op on Con₁ which we define by recursion.

As an example we define the Con₀ representing semi-simplicial types upto level 5
-}

module plan where

-- A semi-simplicial type up to level 4 bundles:
--   X₀ : vertices
--   X₁ : edges         (1 edge  per 2-element subset of vertices)
--   X₂ : triangles      (3 edges per 3-element subset)
--   X₃ : tetrahedra     (6 edges, 4 triangles per 4-element subset)
--   X₄ : 4-simplices   (10 edges, 10 triangles, 5 tetrahedra per 5-element subset)

record SST4 : Set₁ where
  field
    X₀ : Set

    X₁ : (x₀ x₁ : X₀)
       → Set

    -- 3 vertices, 3 edges
    X₂ : (x₀ x₁ x₂ : X₀)
       → (x₀₁ : X₁ x₀ x₁)(x₀₂ : X₁ x₀ x₂)(x₁₂ : X₁ x₁ x₂)
       → Set

    -- 4 vertices, 6 edges, 4 triangles
    X₃ : (x₀ x₁ x₂ x₃ : X₀)
       → (x₀₁ : X₁ x₀ x₁)(x₀₂ : X₁ x₀ x₂)(x₀₃ : X₁ x₀ x₃)
       → (x₁₂ : X₁ x₁ x₂)(x₁₃ : X₁ x₁ x₃)
       → (x₂₃ : X₁ x₂ x₃)
       → (x₀₁₂ : X₂ x₀ x₁ x₂ x₀₁ x₀₂ x₁₂)
       → (x₀₁₃ : X₂ x₀ x₁ x₃ x₀₁ x₀₃ x₁₃)
       → (x₀₂₃ : X₂ x₀ x₂ x₃ x₀₂ x₀₃ x₂₃)
       → (x₁₂₃ : X₂ x₁ x₂ x₃ x₁₂ x₁₃ x₂₃)
       → Set

    -- 5 vertices, 10 edges, 10 triangles, 5 tetrahedra
    X₄ : (x₀ x₁ x₂ x₃ x₄ : X₀)
       → (x₀₁ : X₁ x₀ x₁)(x₀₂ : X₁ x₀ x₂)(x₀₃ : X₁ x₀ x₃)(x₀₄ : X₁ x₀ x₄)
       → (x₁₂ : X₁ x₁ x₂)(x₁₃ : X₁ x₁ x₃)(x₁₄ : X₁ x₁ x₄)
       → (x₂₃ : X₁ x₂ x₃)(x₂₄ : X₁ x₂ x₄)
       → (x₃₄ : X₁ x₃ x₄)
       → (x₀₁₂ : X₂ x₀ x₁ x₂ x₀₁ x₀₂ x₁₂)
       → (x₀₁₃ : X₂ x₀ x₁ x₃ x₀₁ x₀₃ x₁₃)
       → (x₀₁₄ : X₂ x₀ x₁ x₄ x₀₁ x₀₄ x₁₄)
       → (x₀₂₃ : X₂ x₀ x₂ x₃ x₀₂ x₀₃ x₂₃)
       → (x₀₂₄ : X₂ x₀ x₂ x₄ x₀₂ x₀₄ x₂₄)
       → (x₀₃₄ : X₂ x₀ x₃ x₄ x₀₃ x₀₄ x₃₄)
       → (x₁₂₃ : X₂ x₁ x₂ x₃ x₁₂ x₁₃ x₂₃)
       → (x₁₂₄ : X₂ x₁ x₂ x₄ x₁₂ x₁₄ x₂₄)
       → (x₁₃₄ : X₂ x₁ x₃ x₄ x₁₃ x₁₄ x₃₄)
       → (x₂₃₄ : X₂ x₂ x₃ x₄ x₂₃ x₂₄ x₃₄)
       → (x₀₁₂₃ : X₃ x₀ x₁ x₂ x₃ x₀₁ x₀₂ x₀₃ x₁₂ x₁₃ x₂₃ x₀₁₂ x₀₁₃ x₀₂₃ x₁₂₃)
       → (x₀₁₂₄ : X₃ x₀ x₁ x₂ x₄ x₀₁ x₀₂ x₀₄ x₁₂ x₁₄ x₂₄ x₀₁₂ x₀₁₄ x₀₂₄ x₁₂₄)
       → (x₀₁₃₄ : X₃ x₀ x₁ x₃ x₄ x₀₁ x₀₃ x₀₄ x₁₃ x₁₄ x₃₄ x₀₁₃ x₀₁₄ x₀₃₄ x₁₃₄)
       → (x₀₂₃₄ : X₃ x₀ x₂ x₃ x₄ x₀₂ x₀₃ x₀₄ x₂₃ x₂₄ x₃₄ x₀₂₃ x₀₂₄ x₀₃₄ x₂₃₄)
       → (x₁₂₃₄ : X₃ x₁ x₂ x₃ x₄ x₁₂ x₁₃ x₁₄ x₂₃ x₂₄ x₃₄ x₁₂₃ x₁₂₄ x₁₃₄ x₂₃₄)
       → Set
