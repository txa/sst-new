{-# OPTIONS --cubical #-}
{-
Semicategories as truncated Segal semi-simplicial types of height 3.

Instead of a composition operation and an associativity law we only have
simplices: a triangle  X₂ f g h  says that h is a composite of f and g,
and a tetrahedron relates four triangles. Composition is the (unique)
filler of the inner horn Λ²₁, and associativity comes from filling the
inner horn Λ³₁ of a tetrahedron.

Faces of a tetrahedron 0123 with edges
  f : 0→1, g : 1→2, h : 2→3, gf : 0→2, hg : 1→3, hgf : 0→3
are
  d₀ = 123 : X₂ g h hg       d₁ = 023 : X₂ gf h hgf
  d₂ = 013 : X₂ f hg hgf     d₃ = 012 : X₂ f g gf

Composition is written in diagrammatic order: f · g : x → z for
f : x → y, g : y → z.
-}
module Segal3 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

-- semi-simplicial types up to tetrahedra ------------------------------------

record SST3 : Type₁ where
  field
    X₀ : Type
    X₁ : X₀ → X₀ → Type
    X₂ : {x y z : X₀} → X₁ x y → X₁ y z → X₁ x z → Type
    X₃ : {w x y z : X₀}{f : X₁ w x}{g : X₁ x y}{h : X₁ y z}
         {gf : X₁ w y}{hg : X₁ x z}{hgf : X₁ w z}
       → X₂ g h hg → X₂ gf h hgf → X₂ f hg hgf → X₂ f g gf → Type

-- the Segal conditions for a semicategory -----------------------------------
-- (homs are sets; the inner horns have unique fillers)

record isSemicat (X : SST3) : Type where
  open SST3 X
  field
    isSet₁ : {x y : X₀} → isSet (X₁ x y)
    Λ²₁ : {x y z : X₀}(f : X₁ x y)(g : X₁ y z) → isContr (Σ[ h ∈ X₁ x z ] X₂ f g h)
    Λ³₁ : {w x y z : X₀}{f : X₁ w x}{g : X₁ x y}{h : X₁ y z}
          {gf : X₁ w y}{hg : X₁ x z}{hgf : X₁ w z}
          (t₀ : X₂ g h hg)(t₂ : X₂ f hg hgf)(t₃ : X₂ f g gf)
        → isContr (Σ[ t₁ ∈ X₂ gf h hgf ] X₃ t₀ t₁ t₂ t₃)
    Λ³₂ : {w x y z : X₀}{f : X₁ w x}{g : X₁ x y}{h : X₁ y z}
          {gf : X₁ w y}{hg : X₁ x z}{hgf : X₁ w z}
          (t₀ : X₂ g h hg)(t₁ : X₂ gf h hgf)(t₃ : X₂ f g gf)
        → isContr (Σ[ t₂ ∈ X₂ f hg hgf ] X₃ t₀ t₁ t₂ t₃)

-- semicategories in the usual sense ------------------------------------------

record Semicat : Type₁ where
  infixl 7 _·_
  field
    Ob    : Type
    Hom   : Ob → Ob → Type
    isSetHom : {x y : Ob} → isSet (Hom x y)
    _·_   : {x y z : Ob} → Hom x y → Hom y z → Hom x z
    assoc : {w x y z : Ob}(f : Hom w x)(g : Hom x y)(h : Hom y z)
          → (f · g) · h ≡ f · (g · h)

-- from simplices to composition and associativity ----------------------------

module FromSegal (X : SST3)(S : isSemicat X) where
  open SST3 X
  open isSemicat S

  infixl 7 _·_
  _·_ : {x y z : X₀} → X₁ x y → X₁ y z → X₁ x z
  f · g = fst (fst (Λ²₁ f g))

  tri : {x y z : X₀}(f : X₁ x y)(g : X₁ y z) → X₂ f g (f · g)
  tri f g = snd (fst (Λ²₁ f g))

  -- any triangle exhibits the composite
  uniq : {x y z : X₀}{f : X₁ x y}{g : X₁ y z}{h : X₁ x z} → X₂ f g h → f · g ≡ h
  uniq {f = f} {g} {h} t = cong fst (isContr→isProp (Λ²₁ f g) (f · g , tri f g) (h , t))

  -- associativity: fill the horn Λ³₁ spanned by the three composites
  -- f·g, g·h and f·(g·h); its missing face d₁ is a triangle for
  -- (f·g)·h with long edge f·(g·h)
  assoc : {w x y z : X₀}(f : X₁ w x)(g : X₁ x y)(h : X₁ y z)
        → (f · g) · h ≡ f · (g · h)
  assoc f g h = uniq (fst (fst (Λ³₁ (tri g h) (tri f (g · h)) (tri f g))))

  semicat : Semicat
  semicat = record { Ob = X₀ ; Hom = X₁ ; isSetHom = isSet₁ ; _·_ = _·_ ; assoc = assoc }

-- and back: a semicategory is a Segal SST3 ------------------------------------
-- triangles are equations, tetrahedra carry no information

module ToSegal (C : Semicat) where
  open Semicat C

  sst : SST3
  sst = record
    { X₀ = Ob
    ; X₁ = Hom
    ; X₂ = λ f g h → f · g ≡ h
    ; X₃ = λ _ _ _ _ → Unit
    }

  segal : isSemicat sst
  segal = record
    { isSet₁ = isSetHom
    ; Λ²₁ = λ f g → isContrSingl (f · g)
    ; Λ³₁ = λ {_} {_} {_} {_} {f} {g} {h} t₀ t₂ t₃ →
        inhProp→isContr (cong (_· h) (sym t₃) ∙ assoc f g h ∙ cong (f ·_) t₀ ∙ t₂ , tt)
                        (isProp× (isSetHom _ _) isPropUnit)
    ; Λ³₂ = λ {_} {_} {_} {_} {f} {g} {h} t₀ t₁ t₃ →
        inhProp→isContr (cong (f ·_) (sym t₀) ∙ sym (assoc f g h) ∙ cong (_· h) t₃ ∙ t₁ , tt)
                        (isProp× (isSetHom _ _) isPropUnit)
    }

-- degeneracies: identities and units ------------------------------------------
-- An identity edge and the two degenerate triangles of an edge f : x → y:
--   s₀ f  on the vertices x x y  (edges id, f, f)
--   s₁ f  on the vertices x y y  (edges f, id, f)

record Degen3 (X : SST3) : Type where
  open SST3 X
  field
    id₁ : {x : X₀} → X₁ x x
    s₀  : {x y : X₀}(f : X₁ x y) → X₂ id₁ f f
    s₁  : {x y : X₀}(f : X₁ x y) → X₂ f id₁ f

record Cat : Type₁ where
  field
    semicat : Semicat
  open Semicat semicat
  field
    id  : {x : Ob} → Hom x x
    idl : {x y : Ob}(f : Hom x y) → id · f ≡ f
    idr : {x y : Ob}(f : Hom x y) → f · id ≡ f

module FromSegalCat (X : SST3)(S : isSemicat X)(D : Degen3 X) where
  open SST3 X
  open Degen3 D
  open FromSegal X S

  cat : Cat
  cat = record { semicat = semicat ; id = id₁ ; idl = λ f → uniq (s₀ f) ; idr = λ f → uniq (s₁ f) }

module ToSegalCat (C : Cat) where
  open Cat C
  open ToSegal semicat

  degen : Degen3 sst
  degen = record { id₁ = id ; s₀ = idl ; s₁ = idr }
