{-# OPTIONS --cubical #-}
{-
(2,1)-semicategories as truncated Segal semi-simplicial types of height 4.

Homs are groupoids. Composition is the filler of Λ²₁, the associator is
the filler of Λ³₁ (as in Segal3), and the pentagon comes from filling the
inner horn Λ⁴₁ of a 4-simplex: its five tetrahedral faces are the five
associators of the pentagon.

Faces of an n-simplex: dᵢ omits vertex i. For a tetrahedron abcd:
  d₀ = bcd, d₁ = acd, d₂ = abd, d₃ = abc,
and for the 4-simplex 01234:
  d₀ = 1234, d₁ = 0234, d₂ = 0134, d₃ = 0124, d₄ = 0123.
Composition is in diagrammatic order.
-}
module Segal4 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

record SST4 : Type₁ where
  field
    X₀ : Type
    X₁ : X₀ → X₀ → Type
    X₂ : {x y z : X₀} → X₁ x y → X₁ y z → X₁ x z → Type
    X₃ : {w x y z : X₀}{f : X₁ w x}{g : X₁ x y}{h : X₁ y z}
         {gf : X₁ w y}{hg : X₁ x z}{hgf : X₁ w z}
       → X₂ g h hg → X₂ gf h hgf → X₂ f hg hgf → X₂ f g gf → Type
    X₄ : {v₀ v₁ v₂ v₃ v₄ : X₀}
         {e₀₁ : X₁ v₀ v₁}{e₁₂ : X₁ v₁ v₂}{e₂₃ : X₁ v₂ v₃}{e₃₄ : X₁ v₃ v₄}
         {e₀₂ : X₁ v₀ v₂}{e₁₃ : X₁ v₁ v₃}{e₂₄ : X₁ v₂ v₄}
         {e₀₃ : X₁ v₀ v₃}{e₁₄ : X₁ v₁ v₄}{e₀₄ : X₁ v₀ v₄}
         {t₀₁₂ : X₂ e₀₁ e₁₂ e₀₂}{t₀₁₃ : X₂ e₀₁ e₁₃ e₀₃}{t₀₁₄ : X₂ e₀₁ e₁₄ e₀₄}
         {t₀₂₃ : X₂ e₀₂ e₂₃ e₀₃}{t₀₂₄ : X₂ e₀₂ e₂₄ e₀₄}{t₀₃₄ : X₂ e₀₃ e₃₄ e₀₄}
         {t₁₂₃ : X₂ e₁₂ e₂₃ e₁₃}{t₁₂₄ : X₂ e₁₂ e₂₄ e₁₄}{t₁₃₄ : X₂ e₁₃ e₃₄ e₁₄}
         {t₂₃₄ : X₂ e₂₃ e₃₄ e₂₄}
       → X₃ t₂₃₄ t₁₃₄ t₁₂₄ t₁₂₃ → X₃ t₂₃₄ t₀₃₄ t₀₂₄ t₀₂₃ → X₃ t₁₃₄ t₀₃₄ t₀₁₄ t₀₁₃
       → X₃ t₁₂₄ t₀₂₄ t₀₁₄ t₀₁₂ → X₃ t₁₂₃ t₀₂₃ t₀₁₃ t₀₁₂ → Type

-- the Segal conditions for a (2,1)-semicategory: homs are groupoids, inner
-- horns have unique fillers (only Λ⁴₁ is stated; Λ⁴₂ and Λ⁴₃ are analogous)

record is21Semicat (X : SST4) : Type where
  open SST4 X
  field
    isGrpd₁ : {x y : X₀} → isGroupoid (X₁ x y)
    Λ²₁ : {x y z : X₀}(f : X₁ x y)(g : X₁ y z) → isContr (Σ[ h ∈ X₁ x z ] X₂ f g h)
    Λ³₁ : {w x y z : X₀}{f : X₁ w x}{g : X₁ x y}{h : X₁ y z}
          {gf : X₁ w y}{hg : X₁ x z}{hgf : X₁ w z}
          (t₀ : X₂ g h hg)(t₂ : X₂ f hg hgf)(t₃ : X₂ f g gf)
        → isContr (Σ[ t₁ ∈ X₂ gf h hgf ] X₃ t₀ t₁ t₂ t₃)
    Λ³₂ : {w x y z : X₀}{f : X₁ w x}{g : X₁ x y}{h : X₁ y z}
          {gf : X₁ w y}{hg : X₁ x z}{hgf : X₁ w z}
          (t₀ : X₂ g h hg)(t₁ : X₂ gf h hgf)(t₃ : X₂ f g gf)
        → isContr (Σ[ t₂ ∈ X₂ f hg hgf ] X₃ t₀ t₁ t₂ t₃)
    Λ⁴₁ : {v₀ v₁ v₂ v₃ v₄ : X₀}
          {e₀₁ : X₁ v₀ v₁}{e₁₂ : X₁ v₁ v₂}{e₂₃ : X₁ v₂ v₃}{e₃₄ : X₁ v₃ v₄}
          {e₀₂ : X₁ v₀ v₂}{e₁₃ : X₁ v₁ v₃}{e₂₄ : X₁ v₂ v₄}
          {e₀₃ : X₁ v₀ v₃}{e₁₄ : X₁ v₁ v₄}{e₀₄ : X₁ v₀ v₄}
          {t₀₁₂ : X₂ e₀₁ e₁₂ e₀₂}{t₀₁₃ : X₂ e₀₁ e₁₃ e₀₃}{t₀₁₄ : X₂ e₀₁ e₁₄ e₀₄}
          {t₀₂₃ : X₂ e₀₂ e₂₃ e₀₃}{t₀₂₄ : X₂ e₀₂ e₂₄ e₀₄}{t₀₃₄ : X₂ e₀₃ e₃₄ e₀₄}
          {t₁₂₃ : X₂ e₁₂ e₂₃ e₁₃}{t₁₂₄ : X₂ e₁₂ e₂₄ e₁₄}{t₁₃₄ : X₂ e₁₃ e₃₄ e₁₄}
          {t₂₃₄ : X₂ e₂₃ e₃₄ e₂₄}
          (T₀ : X₃ t₂₃₄ t₁₃₄ t₁₂₄ t₁₂₃)(T₂ : X₃ t₁₃₄ t₀₃₄ t₀₁₄ t₀₁₃)
          (T₃ : X₃ t₁₂₄ t₀₂₄ t₀₁₄ t₀₁₂)(T₄ : X₃ t₁₂₃ t₀₂₃ t₀₁₃ t₀₁₂)
        → isContr (Σ[ T₁ ∈ X₃ t₂₃₄ t₀₃₄ t₀₂₄ t₀₂₃ ] X₄ T₀ T₁ T₂ T₃ T₄)

-- small groupoid lemmas -------------------------------------------------------

private
  variable
    ℓ : Level
    A : Type ℓ
    u v w y z : A

  cancelL : (p : u ≡ v)(X : u ≡ w) → p ∙ (sym p ∙ X) ≡ X
  cancelL p X = assoc p (sym p) X ∙ cong (_∙ X) (rCancel p) ∙ sym (lUnit X)

  cancelL' : (p : u ≡ v)(X : v ≡ w) → sym p ∙ (p ∙ X) ≡ X
  cancelL' p X = assoc (sym p) p X ∙ cong (_∙ X) (lCancel p) ∙ sym (lUnit X)

  cancelR : (s : u ≡ v)(q : w ≡ v) → (s ∙ sym q) ∙ q ≡ s
  cancelR s q = sym (assoc s (sym q) q) ∙ cong (s ∙_) (lCancel q) ∙ sym (rUnit s)

  -- solving the pentagon for its middle edge
  penta-alg : (p : u ≡ v)(m : v ≡ w)(q : w ≡ z)(r : u ≡ y)(s : y ≡ z)
            → m ≡ sym p ∙ r ∙ s ∙ sym q → p ∙ m ∙ q ≡ r ∙ s
  penta-alg p m q r s e =
      cong (λ m' → p ∙ m' ∙ q) e
    ∙ assoc p (sym p ∙ r ∙ s ∙ sym q) q
    ∙ cong (_∙ q) (cancelL p (r ∙ s ∙ sym q))
    ∙ sym (assoc r (s ∙ sym q) q)
    ∙ cong (r ∙_) (cancelR s q)

-- from simplices to composition, associator and pentagon ----------------------

module FromSegal (X : SST4)(S : is21Semicat X) where
  open SST4 X
  open is21Semicat S

  infixl 7 _·_
  _·_ : {x y z : X₀} → X₁ x y → X₁ y z → X₁ x z
  f · g = fst (fst (Λ²₁ f g))

  tri : {x y z : X₀}(f : X₁ x y)(g : X₁ y z) → X₂ f g (f · g)
  tri f g = snd (fst (Λ²₁ f g))

  uniq : {x y z : X₀}{f : X₁ x y}{g : X₁ y z}{h : X₁ x z} → X₂ f g h → f · g ≡ h
  uniq {f = f} {g} {h} t = cong fst (isContr→isProp (Λ²₁ f g) (f · g , tri f g) (h , t))

  uniqRefl : {x y z : X₀}{f : X₁ x y}{g : X₁ y z} → uniq (tri f g) ≡ refl
  uniqRefl {f = f} {g} = cong (cong fst) (lCancel (snd (Λ²₁ f g) (f · g , tri f g)))

  -- induction over triangles with fixed spine (their total space is contractible)
  ind₂ : {x y z : X₀}{f : X₁ x y}{g : X₁ y z}(P : (h : X₁ x z) → X₂ f g h → Type)
       → P (f · g) (tri f g) → (h : X₁ x z)(t : X₂ f g h) → P h t
  ind₂ {f = f} {g} P p h t =
    subst (λ ht → P (fst ht) (snd ht)) (isContr→isProp (Λ²₁ f g) (f · g , tri f g) (h , t)) p

  -- the associator: the long edge of the filler of Λ³₁ on the canonical triangles
  α : {w x y z : X₀}(f : X₁ w x)(g : X₁ x y)(h : X₁ y z) → (f · g) · h ≡ f · (g · h)
  α f g h = uniq (fst (fst (Λ³₁ (tri g h) (tri f (g · h)) (tri f g))))

  -- what a tetrahedron says, in terms of paths
  rhs : {w x y z : X₀}{f : X₁ w x}{g : X₁ x y}{h : X₁ y z}
        {gf : X₁ w y}{hg : X₁ x z}{hgf : X₁ w z}
      → X₂ f g gf → X₂ g h hg → X₂ f hg hgf → gf · h ≡ hgf
  rhs {f = f} {g} {h} t₃ t₀ t₂ =
    cong (_· h) (sym (uniq t₃)) ∙ α f g h ∙ cong (f ·_) (uniq t₀) ∙ uniq t₂

  Qc : {w x y z : X₀}{f : X₁ w x}{g : X₁ x y}{h : X₁ y z}
       (t₁ : X₂ (f · g) h (f · (g · h)))(T : X₃ (tri g h) t₁ (tri f (g · h)) (tri f g))
     → uniq t₁ ≡ rhs (tri f g) (tri g h) (tri f (g · h))
  Qc {f = f} {g} {h} t₁ T =
      cong (λ c → uniq (fst c)) (isContr→isProp (Λ³₁ (tri g h) (tri f (g · h)) (tri f g)) (t₁ , T)
                                                 (fst (Λ³₁ (tri g h) (tri f (g · h)) (tri f g))))
    ∙ sym simp
    where
      simp : rhs (tri f g) (tri g h) (tri f (g · h)) ≡ α f g h
      simp = (λ i → cong (_· h) (sym (uniqRefl {f = f} {g} i)) ∙ α f g h
                    ∙ cong (f ·_) (uniqRefl {f = g} {h} i) ∙ uniqRefl {f = f} {g · h} i)
           ∙ sym (lUnit (α f g h ∙ refl ∙ refl))
           ∙ cong (α f g h ∙_) (sym (lUnit refl))
           ∙ sym (rUnit (α f g h))

  Q : {w x y z : X₀}{f : X₁ w x}{g : X₁ x y}{h : X₁ y z}
      {gf : X₁ w y}{hg : X₁ x z}{hgf : X₁ w z}
      (t₀ : X₂ g h hg)(t₁ : X₂ gf h hgf)(t₂ : X₂ f hg hgf)(t₃ : X₂ f g gf)
    → X₃ t₀ t₁ t₂ t₃ → uniq t₁ ≡ rhs t₃ t₀ t₂
  Q {f = f} {g} {h} {gf} {hg} {hgf} t₀ t₁ t₂ t₃ T =
    ind₂ (λ gf t₃ → (hg : _)(t₀ : X₂ g h hg)(hgf : _)(t₂ : X₂ f hg hgf)(t₁ : X₂ gf h hgf)
                  → X₃ t₀ t₁ t₂ t₃ → uniq t₁ ≡ rhs t₃ t₀ t₂)
      (ind₂ (λ hg t₀ → (hgf : _)(t₂ : X₂ f hg hgf)(t₁ : X₂ (f · g) h hgf)
                     → X₃ t₀ t₁ t₂ (tri f g) → uniq t₁ ≡ rhs (tri f g) t₀ t₂)
        (ind₂ (λ hgf t₂ → (t₁ : X₂ (f · g) h hgf)
                        → X₃ (tri g h) t₁ t₂ (tri f g) → uniq t₁ ≡ rhs (tri f g) (tri g h) t₂)
          Qc))
      gf t₃ hg t₀ hgf t₂ t₁ T

  -- dropping canonical triangles from rhs
  dropL : {a b c : X₀}{d e : X₀}{f : X₁ a b}{g : X₁ b c}(F : X₁ a c → X₁ d e){o : X₁ d e}(Z : F (f · g) ≡ o)
        → cong F (sym (uniq (tri f g))) ∙ Z ≡ Z
  dropL F Z = cong (λ p → cong F (sym p) ∙ Z) uniqRefl ∙ sym (lUnit Z)

  dropM : {a b c : X₀}{d e : X₀}{f : X₁ a b}{g : X₁ b c}(F : X₁ a c → X₁ d e){o : X₁ d e}(Z : F (f · g) ≡ o)
        → cong F (uniq (tri f g)) ∙ Z ≡ Z
  dropM F Z = cong (λ p → cong F p ∙ Z) uniqRefl ∙ sym (lUnit Z)

  dropR : {a b c : X₀}{f : X₁ a b}{g : X₁ b c}{o : X₁ a c}(Y : o ≡ f · g)
        → Y ∙ uniq (tri f g) ≡ Y
  dropR Y = cong (Y ∙_) uniqRefl ∙ sym (rUnit Y)

  -- the pentagon ---------------------------------------------------------------
  pentagon : {v₀ v₁ v₂ v₃ v₄ : X₀}(f : X₁ v₀ v₁)(g : X₁ v₁ v₂)(h : X₁ v₂ v₃)(k : X₁ v₃ v₄)
           → cong (_· k) (α f g h) ∙ α f (g · h) k ∙ cong (f ·_) (α g h k)
           ≡ α (f · g) h k ∙ α f g (h · k)
  pentagon f g h k =
    penta-alg (cong (_· k) (α f g h)) (α f (g · h) k) (cong (f ·_) (α g h k))
              (α (f · g) h k) (α f g (h · k)) middle
    where
      -- the 4-simplex: canonical triangles on the spine and on 013, 134, 014;
      -- the remaining triangles and four tetrahedra come from 3-dimensional horns
      t₀₁₂ = tri f g ; t₁₂₃ = tri g h ; t₂₃₄ = tri h k
      t₀₁₃ = tri f (g · h) ; t₁₃₄ = tri (g · h) k ; t₀₁₄ = tri f ((g · h) · k)
      c0123 = fst (Λ³₁ t₁₂₃ t₀₁₃ t₀₁₂)
      t₀₂₃ = fst c0123 ; T₄ = snd c0123
      c1234 = fst (Λ³₂ t₂₃₄ t₁₃₄ t₁₂₃)
      t₁₂₄ = fst c1234 ; T₀ = snd c1234
      c0134 = fst (Λ³₁ t₁₃₄ t₀₁₄ t₀₁₃)
      t₀₃₄ = fst c0134 ; T₂ = snd c0134
      c0124 = fst (Λ³₁ t₁₂₄ t₀₁₄ t₀₁₂)
      t₀₂₄ = fst c0124 ; T₃ = snd c0124
      -- the inner horn Λ⁴₁ supplies the fifth tetrahedron 0234
      T₁ = fst (fst (Λ⁴₁ T₀ T₂ T₃ T₄))

      -- what the five tetrahedra say
      E₄ : uniq t₀₂₃ ≡ α f g h
      E₄ = Q t₁₂₃ t₀₂₃ t₀₁₃ t₀₁₂ T₄ ∙ dropL (_· h) _ ∙ cong (α f g h ∙_) (dropM (f ·_) _) ∙ dropR _

      E₀ : uniq t₁₂₄ ≡ sym (α g h k)
      E₀ = sym (cancelL' (α g h k) (uniq t₁₂₄))
         ∙ cong (sym (α g h k) ∙_) (sym (sym uniqRefl ∙ Q t₂₃₄ t₁₃₄ t₁₂₄ t₁₂₃ T₀ ∙ dropL (_· k) _
                                        ∙ cong (α g h k ∙_) (dropM (g ·_) _)))
         ∙ sym (rUnit _)

      E₂ : uniq t₀₃₄ ≡ α f (g · h) k
      E₂ = Q t₁₃₄ t₀₃₄ t₀₁₄ t₀₁₃ T₂ ∙ dropL (_· k) _ ∙ cong (α f (g · h) k ∙_) (dropM (f ·_) _) ∙ dropR _

      E₃ : uniq t₀₂₄ ≡ α f g (h · k) ∙ cong (f ·_) (sym (α g h k))
      E₃ = Q t₁₂₄ t₀₂₄ t₀₁₄ t₀₁₂ T₃ ∙ dropL (_· (h · k)) _
         ∙ cong (α f g (h · k) ∙_) (cong (cong (f ·_) (uniq t₁₂₄) ∙_) refl ∙ dropR _)
         ∙ cong (λ b → α f g (h · k) ∙ cong (f ·_) b) E₀

      E₁ : uniq t₀₃₄ ≡ cong (_· k) (sym (uniq t₀₂₃)) ∙ α (f · g) h k
                       ∙ cong ((f · g) ·_) (uniq t₂₃₄) ∙ uniq t₀₂₄
      E₁ = Q t₂₃₄ t₀₃₄ t₀₂₄ t₀₂₃ T₁

      middle : α f (g · h) k ≡ sym (cong (_· k) (α f g h)) ∙ α (f · g) h k ∙ α f g (h · k)
                               ∙ sym (cong (f ·_) (α g h k))
      middle = sym E₂ ∙ E₁
             ∙ (λ i → cong (_· k) (sym (E₄ i)) ∙ α (f · g) h k ∙ dropM ((f · g) ·_) (uniq t₀₂₄) i)
             ∙ (λ i → cong (_· k) (sym (α f g h)) ∙ α (f · g) h k ∙ E₃ i)
