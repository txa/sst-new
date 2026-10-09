{-# OPTIONS --without-K #-}
{-
The optimized syntax of Kovács (Rosain's report, Appendix A) as an
*untruncated* HIT: composition and weakening are constructors, their laws
are path constructors. We give its signature as a record of algebras
(Model); the syntax is the initial Model.

Main point: the standard model in Type is definable without K, and every
path constructor is interpreted by refl. The coherence problem we had in
paper/Sem.agda (⟦∘⟧) disappears, because ∘ and wkLoc are interpreted
directly as composition and precomposition.

Remark: ass can't be dropped, since keep∘keep is a path *over* ass
(its two sides have indices (ρ ∘ σ) ∘ δ and ρ ∘ (σ ∘ δ)).
-}
module HIT where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit

subst : ∀ {i j}{X : Set i}(P : X → Set j){a b : X} → a ≡ b → P a → P b
subst P refl y = y

sym' : ∀ {i}{X : Set i}{a b : X} → a ≡ b → b ≡ a
sym' refl = refl

record Model : Set₃ where
  infixl 5 _▷_
  infixr 9 _∘_
  field
    -- sorts
    Con : Set₂
    Loc : Con → Set₁                              -- = Ty
    Var : (Γ : Con) → Loc Γ → Set₁
    Emb : {Γ : Con} → Loc Γ → Loc Γ → Set₁        -- = Thin
    -- point constructors
    •     : Con
    _▷_   : (Γ : Con) → Loc Γ → Con
    []    : {Γ : Con} → Loc Γ
    ext   : {Γ : Con}(Δ : Loc Γ){Ξ : Loc Γ} → Var Γ Ξ → Emb Δ Ξ → Loc Γ
    wkLoc : {Γ : Con}{Δ' : Loc Γ} → Loc Γ → Loc (Γ ▷ Δ')
    ε     : {Γ : Con} → Emb {Γ} [] []
    drop  : {Γ : Con}{Δ Ξ Ψ : Loc Γ}{x : Var Γ Ψ}{δ : Emb Δ Ψ}
          → Emb Δ Ξ → Emb (ext Δ x δ) Ξ
    _∘_   : {Γ : Con}{Δ Ξ Ψ : Loc Γ} → Emb Ξ Ψ → Emb Δ Ξ → Emb Δ Ψ
    keep  : {Γ : Con}{Δ Ξ Ψ : Loc Γ}{x : Var Γ Ψ}{δ : Emb Ξ Ψ}
          → (σ : Emb Δ Ξ) → Emb (ext Δ x (δ ∘ σ)) (ext Ξ x δ)
    wkEmb : {Γ : Con}{Δ' : Loc Γ}{Ξ Ψ : Loc Γ}
          → Emb Ξ Ψ → Emb {Γ ▷ Δ'} (wkLoc Ξ) (wkLoc Ψ)
    vz    : {Γ : Con}{Δ : Loc Γ} → Var (Γ ▷ Δ) (wkLoc Δ)
    vs    : {Γ : Con}{Δ Ξ : Loc Γ} → Var Γ Δ → Var (Γ ▷ Ξ) (wkLoc Δ)
    -- path constructors
    wk[]  : {Γ : Con}{Δ' : Loc Γ} → wkLoc {Γ}{Δ'} [] ≡ []
    wk∷   : {Γ : Con}{Δ' : Loc Γ}{Ξ Ψ : Loc Γ}{x : Var Γ Ψ}{σ : Emb Ξ Ψ}
          → wkLoc {Γ}{Δ'} (ext Ξ x σ) ≡ ext (wkLoc Ξ) (vs x) (wkEmb σ)
    ass   : {Γ : Con}{Δ Ξ Ψ Φ : Loc Γ}{σ : Emb Ψ Φ}{δ : Emb Ξ Ψ}{ν : Emb Δ Ξ}
          → (σ ∘ δ) ∘ ν ≡ σ ∘ (δ ∘ ν)
    ∘ε    : {Γ : Con}{Ψ : Loc Γ}{σ : Emb [] Ψ} → σ ∘ ε ≡ σ
    ∘drop : {Γ : Con}{Δ Ξ Ψ Φ : Loc Γ}{x : Var Γ Φ}{δ' : Emb Δ Φ}
            {σ : Emb Ξ Ψ}{δ : Emb Δ Ξ}
          → σ ∘ drop {x = x}{δ = δ'} δ ≡ drop (σ ∘ δ)
    drop∘keep : {Γ : Con}{Δ Ξ Ψ Φ : Loc Γ}{x : Var Γ Φ}{ρ : Emb Ξ Φ}
                {σ : Emb Ξ Ψ}{δ : Emb Δ Ξ}
              → drop σ ∘ keep {x = x}{δ = ρ} δ ≡ drop (σ ∘ δ)
    keep∘keep : {Γ : Con}{Δ Ξ Ψ Φ : Loc Γ}{x : Var Γ Φ}{ρ : Emb Ψ Φ}
                {σ : Emb Ξ Ψ}{δ : Emb Δ Ξ}
              → subst (λ d → Emb (ext Δ x d) (ext Ψ x ρ)) ass (keep σ ∘ keep δ)
                ≡ keep (σ ∘ δ)
    wkε    : {Γ : Con}{Δ' : Loc Γ}
           → subst (λ L → Emb {Γ ▷ Δ'} L L) wk[] (wkEmb ε) ≡ ε
    wk∘    : {Γ : Con}{Δ' : Loc Γ}{Δ Ξ Ψ : Loc Γ}{σ : Emb Ξ Ψ}{δ : Emb Δ Ξ}
           → wkEmb {Δ' = Δ'} (σ ∘ δ) ≡ wkEmb σ ∘ wkEmb δ
    wkdrop : {Γ : Con}{Δ' : Loc Γ}{Δ Ξ Ψ : Loc Γ}{x : Var Γ Ψ}{δ : Emb Δ Ψ}{σ : Emb Δ Ξ}
           → subst (λ L → Emb {Γ ▷ Δ'} L (wkLoc Ξ)) wk∷ (wkEmb (drop {x = x}{δ = δ} σ))
             ≡ drop (wkEmb σ)
    wkkeep : {Γ : Con}{Δ' : Loc Γ}{Δ Ξ Ψ : Loc Γ}{x : Var Γ Ψ}{δ : Emb Ξ Ψ}{σ : Emb Δ Ξ}
           → subst (λ L → Emb {Γ ▷ Δ'} L (ext (wkLoc Ξ) (vs x) (wkEmb δ)))
                   (wk∷ {σ = δ ∘ σ})
                   (subst (λ L → Emb {Γ ▷ Δ'} (wkLoc (ext Δ x (δ ∘ σ))) L) wk∷
                          (wkEmb (keep {x = x}{δ = δ} σ)))
             ≡ subst (λ d → Emb (ext (wkLoc Δ) (vs x) d) (ext (wkLoc Ξ) (vs x) (wkEmb δ)))
                     (sym' wk∘) (keep (wkEmb σ))

-- the standard model ---------------------------------------------------

record ⊤₁ : Set₁ where
  constructor tt₁

module Std where
  Con : Set₂
  Con = Set₁
  Loc : Con → Set₁
  Loc Γ = Γ → Set
  Var : (Γ : Con) → Loc Γ → Set₁
  Var Γ Δ = (γ : Γ) → Δ γ → Set
  Emb : {Γ : Con} → Loc Γ → Loc Γ → Set₁
  Emb {Γ} Δ Ξ = {γ : Γ} → Δ γ → Ξ γ

  _▷_ : (Γ : Con) → Loc Γ → Con
  Γ ▷ Δ = Σ Γ (λ γ → Δ γ → Set)
  ext : {Γ : Con}(Δ : Loc Γ){Ξ : Loc Γ} → Var Γ Ξ → Emb Δ Ξ → Loc Γ
  ext Δ x δ γ = Σ (Δ γ) (λ a → x γ (δ a))
  wkLoc : {Γ : Con}{Δ' : Loc Γ} → Loc Γ → Loc (Γ ▷ Δ')
  wkLoc Δ γ = Δ (fst γ)
  _∘_ : {Γ : Con}{Δ Ξ Ψ : Loc Γ} → Emb Ξ Ψ → Emb Δ Ξ → Emb Δ Ψ
  (σ ∘ δ) a = σ (δ a)

std : Model
std = record
  { Con = Std.Con ; Loc = Std.Loc ; Var = Std.Var ; Emb = Std.Emb
  ; • = ⊤₁
  ; _▷_ = Std._▷_
  ; [] = λ _ → ⊤
  ; ext = Std.ext
  ; wkLoc = Std.wkLoc
  ; ε = λ _ → tt
  ; drop = λ σ a → σ (fst a)
  ; _∘_ = Std._∘_
  ; keep = λ σ a → σ (fst a) , snd a        -- no transport needed
  ; wkEmb = λ σ a → σ a
  ; vz = λ γ b → snd γ b                    -- no unwk needed
  ; vs = λ x γ b → x (fst γ) b
  ; wk[] = refl ; wk∷ = refl ; ass = refl ; ∘ε = refl ; ∘drop = refl
  ; drop∘keep = refl ; keep∘keep = refl
  ; wkε = refl ; wk∘ = refl ; wkdrop = refl ; wkkeep = refl
  }

-- a critical pair -------------------------------------------------------
-- In any model there are two paths
--   (σ ∘ δ) ∘ drop ν  ≡  drop (σ ∘ (δ ∘ ν)),
-- one using ∘drop first and then ass, the other using ass first and then
-- ∘drop twice. In the standard model both are refl. For the syntax to be
-- a set (which normalisation into TT.agda would show) they must be
-- equal, but the HIT has no 2-cell constructor saying so: this is the
-- coherence that is still to be shown (or added, and then its coherences...).

module CriticalPair (M : Model) where
  open Model M

  cong₁ : {X Y : Set₁}(f : X → Y){a b : X} → a ≡ b → f a ≡ f b
  cong₁ f refl = refl

  _∙_ : {X : Set₁}{a b c : X} → a ≡ b → b ≡ c → a ≡ c
  refl ∙ q = q

  module _ {Γ : Con}{Δ Ξ Ψ Φ Θ : Loc Γ}{x : Var Γ Θ}{δ' : Emb Δ Θ}
           {σ : Emb Ψ Φ}{δ : Emb Ξ Ψ}{ν : Emb Δ Ξ} where

    path₁ path₂ : (σ ∘ δ) ∘ drop {x = x}{δ = δ'} ν ≡ drop (σ ∘ (δ ∘ ν))
    path₁ = ∘drop ∙ cong₁ drop ass
    path₂ = ass ∙ (cong₁ (σ ∘_) ∘drop ∙ ∘drop)
