{-# OPTIONS --without-K #-}
{-
The coherence conjecture, stated formally.

Plain Agda has no higher inductive-inductive types, so the initial model
of the signature in HIIT.agda is POSTULATED here (only in this file),
together with its recursor. We only state what the recursor gives on
sorts; it also commutes with the constructors (β-laws), which we do not
spell out.

    Syn  --rec IR-->  TT.agda          (IR model: HIITtoIR.agda)
    Syn  --rec std--> Set              (standard model: HIIT.agda, all refl)

Conjecture: rec IR is an equivalence (on every sort).

Consequences if it holds:
* the HIIT Syn is a set, since the IR syntax is one (uniqueness of the
  stored codes is TT.agda; decidable equality of all sorts is still to be
  written down), so the HIIT is coherent;
* the IR syntax gets a K-free interpretation  rec std ∘ (rec IR)⁻¹,
  and with it SST n (SSTk.agda) becomes a type in book HoTT for all n.

Expected shape of a proof: define the inverse IR → Syn by recursion on
the IR syntax (sending codes to paths in Syn); the round trip
IR → Syn → IR is the identity by induction on IR (codes are
propositions). The other round trip Syn → IR → Syn needs induction on
Syn, whose path-constructor cases (in particular ass against the
computation rules, i.e. the pentagon) are exactly the coherence problem.
-}
module HIITConj where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import HIIT
open import HIITtoIR

-- equivalences (bi-invertible maps; a proposition, as in the HoTT book)
record isEquiv {i j}{X : Set i}{Y : Set j}(f : X → Y) : Set (i ⊔ j) where
  field
    g : Y → X
    gf : (x : X) → g (f x) ≡ x
    h : Y → X
    fh : (y : Y) → f (h y) ≡ y

-- the action of a morphism of models on sorts
record SortMap {i j i' j'}(M : Model i j)(N : Model i' j') : Set (i ⊔ j ⊔ i' ⊔ j') where
  private module M = Model M
  private module N = Model N
  field
    fCon  : M.Con → N.Con
    fTy   : {Γ : M.Con} → M.Ty Γ → N.Ty (fCon Γ)
    fVar  : {Γ : M.Con}{A : M.Ty Γ} → M.Var Γ A → N.Var (fCon Γ) (fTy A)
    fThin : {Γ : M.Con}{A B : M.Ty Γ} → M.Thin A B → N.Thin (fTy A) (fTy B)
    -- … together with the preservation of all constructors (omitted)

postulate
  -- the HIIT itself: the initial model of the signature
  Syn : Model lzero lzero
  rec : ∀ {i j}(M : Model i j) → SortMap Syn M

-- the map from the HIIT to the inductive-recursive syntax
toIR : SortMap Syn IR
toIR = rec IR

-- the conjecture: toIR is an equivalence on every sort
record Coherent : Set where
  open SortMap toIR
  private module S = Model Syn
  field
    con  : isEquiv fCon
    ty   : (Γ : S.Con) → isEquiv (fTy {Γ})
    var  : (Γ : S.Con)(A : S.Ty Γ) → isEquiv (fVar {Γ}{A})
    thin : (Γ : S.Con)(A B : S.Ty Γ) → isEquiv (fThin {Γ}{A}{B})
