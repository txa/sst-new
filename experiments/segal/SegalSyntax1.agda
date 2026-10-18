{-# OPTIONS --cubical #-}
{-
The telescope layer of the syntax with composition given Segal-style:
the 1-categorical (semicategory) version.

* Thinnings do not compose by a recursive function; instead there is a
  sort of triangles  Tri δ σ τ  ("τ is a composite of δ and σ").
* A keep stores a triangle instead of an equation (Fording):
      t-k : (σ : Thin A B) → Tri δ σ δ' → Thin (ext A δ') (ext B δ)
* Composition is the filler of the horn Λ²₁ (_∘_ and tri, unique by
  uniq). The computation rules of composition are triangles. The keep–keep
  rule uses the filler of the 3-dimensional horn Λ³₁ (fill₁), which is
  where associativity lives.
* Thin is truncated to a set, and triangles to propositions (otherwise the
  computation triangles would give several triangles with the same
  boundary). Ty is not truncated. Tetrahedra carry no information.

Result: (Ty, Thin, Tri, ⊤) is a Segal SST₃ (Segal3.isSemicat), hence a
semicategory, with associativity derived from the tetrahedra.
-}
module SegalSyntax1 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Segal3

infixr 9 _∘_

-- one family for all sorts, so that constructors may mention the
-- constructors of other sorts (as in FHIIT2)
data U : Type
data El : U → Type

data U where
  ty   : U
  thin : El ty → El ty → U
  tri  : {A B C : El ty} → El (thin B C) → El (thin A B) → El (thin A C) → U

Ty : Type
Ty = El ty

Thin : Ty → Ty → Type
Thin A B = El (thin A B)

Tri : {A B C : Ty} → Thin B C → Thin A B → Thin A C → Type
Tri δ σ τ = El (tri δ σ τ)

data El where
  -- telescopes
  ε    : Ty
  ext  : (A : Ty){B : Ty} → Thin A B → Ty
  -- thinnings
  tε   : Thin ε ε
  t-d  : {A B C : Ty}{γ : Thin A C} → Thin A B → Thin (ext A γ) B
  t-k  : {A B C : Ty}{δ : Thin B C}{δ' : Thin A C}
       → (σ : Thin A B) → Tri δ σ δ' → Thin (ext A δ') (ext B δ)
  isSetThin : {A B : Ty}{σ τ : Thin A B}(p q : σ ≡ τ) → p ≡ q
  -- Λ²₁: composites exist and are unique
  _∘_  : {A B C : Ty} → Thin B C → Thin A B → Thin A C
  tri  : {A B C : Ty}(δ : Thin B C)(σ : Thin A B) → Tri δ σ (δ ∘ σ)
  uniq : {A B C : Ty}{δ : Thin B C}{σ : Thin A B}{τ : Thin A C} → Tri δ σ τ → δ ∘ σ ≡ τ
  isPropTri : {A B C : Ty}{δ : Thin B C}{σ : Thin A B}{τ : Thin A C}(s s' : Tri δ σ τ) → s ≡ s'
  -- Λ³₁: in a tetrahedron A → B → C → D with edges σ, δ, δC and
  -- long edges τ = δσ, δB = δC δ, δA, the face d₁ follows from the others
  fill₁ : {A B C D : Ty}{σ : Thin A B}{δ : Thin B C}{δC : Thin C D}
         {τ : Thin A C}{δB : Thin B D}{δA : Thin A D}
       → Tri δC δ δB → Tri δB σ δA → Tri δ σ τ → Tri δC τ δA
  -- the computation rules of composition, as triangles
  tri-ε  : {C : Ty}{δ : Thin ε C} → Tri δ tε δ
  tri-d  : {A B C D : Ty}{γ : Thin A D}{δ : Thin B C}{σ : Thin A B}{τ : Thin A C}
         → Tri δ σ τ → Tri δ (t-d {γ = γ} σ) (t-d {γ = γ} τ)
  tri-dk : {A B C D : Ty}{δB : Thin B D}{δA : Thin A D}{δ : Thin B C}{σ : Thin A B}{τ : Thin A C}
           {e : Tri δB σ δA}
         → Tri δ σ τ → Tri (t-d {γ = δB} δ) (t-k σ e) (t-d {γ = δA} τ)
  tri-kk : {A B C D : Ty}{δC : Thin C D}{δB : Thin B D}{δA : Thin A D}
           {δ : Thin B C}{σ : Thin A B}{τ : Thin A C}
           {q : Tri δC δ δB}{e : Tri δB σ δA}
         → (s : Tri δ σ τ) → Tri (t-k δ q) (t-k σ e) (t-k τ (fill₁ q e s))

-- the other inner 3-horn Λ³₂ is derivable from Λ³₁ and Λ²₁ --------------------

-- associativity, from the tetrahedron on the canonical triangles
ass : {A B C D : Ty}(ρ : Thin C D)(δ : Thin B C)(σ : Thin A B) → ρ ∘ (δ ∘ σ) ≡ (ρ ∘ δ) ∘ σ
ass ρ δ σ = uniq (fill₁ (tri ρ δ) (tri (ρ ∘ δ) σ) (tri δ σ))

fill₂ : {A B C D : Ty}{σ : Thin A B}{δ : Thin B C}{δC : Thin C D}
        {τ : Thin A C}{δB : Thin B D}{δA : Thin A D}
      → Tri δC δ δB → Tri δC τ δA → Tri δ σ τ → Tri δB σ δA
fill₂ {σ = σ} {δ} {δC} {τ} {δB} {δA} q r s =
  subst2 (λ b a → Tri b σ a) (uniq q)
         (sym (ass δC δ σ) ∙ cong (δC ∘_) (uniq s) ∙ uniq r)
         (tri (δC ∘ δ) σ)

-- the thinnings form a Segal SST₃ ------------------------------------------------
-- Segal3 composes diagrammatically: an edge f : x → y is a thinning
-- Thin x y, and X₂ f g h is a triangle exhibiting h as g ∘ f.

sst : SST3
sst = record
  { X₀ = Ty
  ; X₁ = Thin
  ; X₂ = λ f g h → Tri g f h
  ; X₃ = λ _ _ _ _ → Unit
  }

segal : isSemicat sst
segal = record
  { isSet₁ = λ σ τ → isSetThin
  ; Λ²₁ = λ f g → inhProp→isContr (g ∘ f , tri g f)
                    (λ (h , t) (h' , t') → ΣPathP (sym (uniq t) ∙ uniq t' ,
                                                    isProp→PathP (λ _ → isPropTri) t t'))
  ; Λ³₁ = λ t₀ t₂ t₃ → inhProp→isContr (fill₁ t₀ t₂ t₃ , tt) (isProp× isPropTri isPropUnit)
  ; Λ³₂ = λ t₀ t₁ t₃ → inhProp→isContr (fill₂ t₀ t₁ t₃ , tt) (isProp× isPropTri isPropUnit)
  }

-- hence a semicategory, whose composition is _∘_ and whose associativity
-- comes from Segal3 (i.e. from the tetrahedra)
semicat : Semicat
semicat = FromSegal.semicat sst segal

_ : {A B C : Ty}(σ : Thin A B)(δ : Thin B C) → Semicat._·_ semicat σ δ ≡ δ ∘ σ
_ = λ σ δ → refl
