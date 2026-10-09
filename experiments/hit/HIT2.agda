{-# OPTIONS --without-K #-}
{-
Adding a specific 2-cell (the ass/∘drop critical pair from HIT.agda) to
the signature. The standard model interprets it by refl: no UIP needed.
-}
module HIT2 where

open import Agda.Builtin.Equality
open import HIT

cong₁ : {X Y : Set₁}(f : X → Y){a b : X} → a ≡ b → f a ≡ f b
cong₁ f refl = refl

_∙_ : {X : Set₁}{a b c : X} → a ≡ b → b ≡ c → a ≡ c
refl ∙ q = q

-- a model of HIT together with the 2-cell filling the critical pair
record Model₂ : Set₃ where
  field M : Model
  open Model M
  field
    ass-drop : {Γ : Con}{Δ Ξ Ψ Φ Θ : Loc Γ}{x : Var Γ Θ}{δ' : Emb Δ Θ}
               {σ : Emb Ψ Φ}{δ : Emb Ξ Ψ}{ν : Emb Δ Ξ}
             → _≡_ {A = (σ ∘ δ) ∘ drop {x = x}{δ = δ'} ν ≡ drop (σ ∘ (δ ∘ ν))}
                   (∘drop ∙ cong₁ drop ass)
                   (ass ∙ (cong₁ (σ ∘_) ∘drop ∙ ∘drop))

std₂ : Model₂
std₂ = record { M = std ; ass-drop = refl }
