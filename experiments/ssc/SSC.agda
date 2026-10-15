{-# OPTIONS --without-K #-}
{-
Experiment: a single-substitution-calculus (Kaposi–Xie) style HIIT for
the telescope layer, to see whether it avoids the critical pairs of
HIIT.agda (which come from ass).

Only the telescope layer, in a fixed context: Var B is given (families
over the telescope B); context weakening is orthogonal and left out.

Idea: no general composition. A thinning is a word of single steps
    id · s₁ · s₂ · … · sₙ
and a step is a face  p  (drop the last entry) lifted under k entries.
The index of a lifted step is a constructor application:

    _⁺ : (s : Step A B) → Step (ext A x (δ · s)) (ext B x δ)

so t-k needs no composition, hence no ass.

Result (see the end of the file):
* the standard model is all refl, K-free (std below);
* but the exchange law (cosimplicial identity) is needed, already at
  level 2 of SST (E₁₂ below), and its lifted versions at level 3;
* exchanges have critical triples (three faces): a hexagon, which would
  need a 2-cell, then 3-cells for four faces, … (higher Bruhat orders).
So ass is traded for exch: still a coherence tower.
-}
module SSC where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit

subst : ∀ {i j}{X : Set i}(P : X → Set j){a b : X} → a ≡ b → P a → P b
subst P refl y = y

record Model (i j : Level) : Set (lsuc (i ⊔ j)) where
  infixl 5 _·_
  field
    Ty   : Set i
    Var  : Ty → Set i
    Thin : Ty → Ty → Set j
    Step : Ty → Ty → Set j

    ε    : Ty
    ext  : (A : Ty){B : Ty} → Var B → Thin A B → Ty

    id   : {A : Ty} → Thin A A
    _·_  : {A B C : Ty} → Thin B C → Step A B → Thin A C

    p    : {A B : Ty}{x : Var B}{δ : Thin A B} → Step (ext A x δ) A
    _⁺   : {A B C : Ty}{x : Var C}{δ : Thin B C}
         → (s : Step A B) → Step (ext A x (δ · s)) (ext B x δ)

    -- the exchange law  d_{j+1} d_i = d_i d_j  (i ≤ j) with the outer
    -- face p:   δ · p · s⁺ = δ · s · p
    exch : {A B C D : Ty}{y : Var D}{γ : Thin B D}{δ : Thin B C}{s : Step A B}
         → δ · p {x = y}{δ = γ} · (s ⁺) ≡ δ · s · p

    -- the same law under one more lift: a path over exch, since the two
    -- sides have different (but exch-equal) source types
    exch⁺ : {A B C D E : Ty}{y : Var D}{z : Var E}{γ : Thin B D}{ζ : Thin B E}
            {δ : Thin (ext B z ζ) C}{s : Step A B}
          → subst (λ θ → Thin (ext (ext A y (γ · s)) z θ) C)
                  (exch {y = y}{γ = γ}{δ = ζ}{s = s})
                  (δ · (p {x = y}{δ = γ} ⁺) · ((s ⁺) ⁺))
            ≡ δ · (s ⁺) · (p ⁺)

-- the standard model: everything is refl, no K -------------------------

std : Model (lsuc lzero) lzero
std = record
  { Ty = Set
  ; Var = λ B → B → Set
  ; Thin = λ A B → A → B
  ; Step = λ A B → A → B
  ; ε = ⊤
  ; ext = λ A x δ → Σ A (λ a → x (δ a))
  ; id = λ a → a
  ; _·_ = λ δ s a → δ (s a)
  ; p = fst
  ; _⁺ = λ s av → s (fst av) , snd av        -- no transport needed
  ; exch = refl
  ; exch⁺ = refl
  }

-- SST up to level 2, in any model ---------------------------------------

module Level2 {i j}(M : Model i j) where
  open Model M

  module _ (X₀ : Var ε) where

    P₁ : Ty                                  -- one point
    P₁ = ext ε X₀ id

    A₁ : Ty                                  -- two points: domain of X₁
    A₁ = ext P₁ X₀ (id · p)

    module _ (X₁ : Var A₁) where

      V₃ : Ty                                -- three points
      V₃ = ext A₁ X₀ (id · p · p)

      -- the three edges as single steps V₃ → A₁
      E₀₁ : Step V₃ A₁                       -- drop x₂
      E₀₁ = p

      E₀₂ : Step V₃ A₁                       -- drop x₁
      E₀₂ = p ⁺

      -- drop x₀: the lifted step has source  ext A₁ X₀ (id · p · p⁺),
      -- not V₃. They agree only by the exchange law.
      E₁₂⁻ : Step (ext A₁ X₀ (id · p · (p ⁺))) A₁
      E₁₂⁻ = (p ⁺) ⁺

      E₁₂ : Step V₃ A₁
      E₁₂ = subst (λ θ → Step (ext A₁ X₀ θ) A₁) exch E₁₂⁻

      -- domain of X₂: three points and three edges
      A₂ : Ty
      A₂ = ext (ext (ext V₃ X₁ (id · E₀₁)) X₁ (id · E₀₂ · p)) X₁ (id · E₁₂ · p · p)

-- in the standard model the transport is along refl, and A₂ is the
-- expected iterated Σ-type
module _ (X₀ : Set)(X₁ : Σ (Σ ⊤ (λ _ → X₀)) (λ _ → X₀) → Set) where
  open Level2 std

  P₃ = Σ (Σ (Σ ⊤ (λ _ → X₀)) (λ _ → X₀)) (λ _ → X₀)
  x₀ x₁ x₂ : P₃ → X₀
  x₀ v = snd (fst (fst v))
  x₁ v = snd (fst v)
  x₂ v = snd v

  e₀₁ = Σ P₃ (λ v → X₁ ((tt , x₀ v) , x₁ v))
  e₀₂ = Σ e₀₁ (λ w → X₁ ((tt , x₀ (fst w)) , x₂ (fst w)))
  e₁₂ = Σ e₀₂ (λ u → X₁ ((tt , x₁ (fst (fst u))) , x₂ (fst (fst u))))

  _ : A₂ (λ _ → X₀) (λ a → X₁ a) ≡ e₁₂
  _ = refl

{-
Critical triples (informal) ------------------------------------------

Orient exch as  δ · p · s⁺  ↦  δ · s · p  (move the outer face p to the
right). A word with three faces, e.g.

    δ · p · p⁺ · p⁺⁺            (drop x₀, x₁, x₂ of a 3-point telescope)

contains two overlapping redexes: the prefix  δ · p · p⁺  (exch) and the
suffix  p⁺ · p⁺⁺  (exch⁺). Both rewrite sequences end in the same normal
form after three exchanges each, in the pattern of the Yang–Baxter
hexagon  (12)(23)(12) = (23)(12)(23). In the untruncated HIIT these are
two different paths, i.e. a loop that is not obviously refl; making the
syntax a set needs a 2-cell for each such hexagon, then 3-cells for four
faces (Zamolodchikov tetrahedra), and so on.

By contrast with ass, the exchange laws are needed only to *type* the
syntax (E₁₂ above): no constructor's type mentions composition.
-}
