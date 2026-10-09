{-# OPTIONS --without-K --prop #-}
module SST where
open import TT
open import Agda.Builtin.Equality

-- semi-simplicial types up to level 2

-- X₀ : Set
Γ₀ : Con
Γ₀ = • ▷ ε

-- X₁ : (x₀ x₁ : X₀) → Set
A₁ : Ty Γ₀
A₁ = ext (ext ε zero tε) zero (t-d tε)

Γ₁ : Con
Γ₁ = Γ₀ ▷ A₁

-- X₂ : (x₀ x₁ x₂ : X₀)(x₀₁ : X₁ x₀ x₁)(x₀₂ : X₁ x₀ x₂)(x₁₂ : X₁ x₁ x₂) → Set
V₃ : Ty Γ₁
V₃ = ext (ext (ext ε (suc zero) tε) (suc zero) (t-d tε)) (suc zero) (t-d (t-d tε))

E₀₁ E₀₂ E₁₂ : Thin V₃ (wkTy A₁ p)
E₀₁ = t-d (t-k (t-k tε reflₚ) reflₚ)
E₀₂ = t-k (t-d (t-k tε reflₚ)) reflₚ
E₁₂ = t-k (t-k (t-d tε) reflₚ) reflₚ

A₂ : Ty Γ₁
A₂ = ext (ext (ext V₃ zero E₀₁) zero (t-d E₀₂)) zero (t-d (t-d E₁₂))

Γ₂ : Con
Γ₂ = Γ₁ ▷ A₂

-- the boundary of a triangle restricted to the edge x₀₂:
-- a thinning from the triangle's arguments to the edge's arguments
∂₀₂ : Thin A₂ (wkTy A₁ p)
∂₀₂ = t-d (t-d (t-d E₀₂))

-- in Γ₂ (one more family in scope) the same thinning, weakened
∂₀₂' : Thin (wkTy A₂ (p {A = A₂})) (wkTy (wkTy A₁ p) p)
∂₀₂' = wkThin ∂₀₂ p

-- identity and composition compute
_ : id {A = A₂} ∘ id ≡ id
_ = refl
