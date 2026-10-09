{-
Plan: TT without K and without Prop, by proving that every sort of the
syntax (Con, Ty, Var, Thin) has decidable equality, hence (Hedberg) is a
set. Status: SKELETON, holes remain. See failed/ for the first attempt
(decidability of Thin alone) and why it fails.

Why all sorts: matching two t-k's needs to unify
  Thin (ext A x δ') (ext B x δ)
whose indices mention x : Var Γ C twice; --without-K cannot delete the
resulting C = C in Ty Γ. So we need UIP for Ty, and through ext also for
Var and Thin; Con for good measure.

Design (avoid ever unifying non-variable / repeated indices):
* decCon, decTy : homogeneous; their only index (Γ) is a variable.
* decVar  : over the total space Σ C. Var Γ C (zero/suc have the
            computed index wkTy A p, which cannot be unified).
* decThin : over the total space Σ (A , B). Thin A B (repeated x).
* "no" cases: never match an equation between constructors; instead
  apply cong to a projection / discriminator defined on fully general
  indices (with a default value), as in t-k-σ below.
* Hedberg gives uipCon, uipTy, uipVar, uipThin; the homogeneous
  decThin follows from decThinΣ using uipTy.
* t-k-cong then uses uipThin as in failed/.

Open problems:
1. Termination: decThinΣ (t-k ..) (t-k ..) compares the proofs e, e'
   via uipThin on Thin A C, which calls decThin on δ ∘ σ: not structural.
   Needs recursion on the length of the source telescope A (explicit
   measure or fuel), since it decreases from ext A x δ' to A.
2. Everything is mutual with _∘_ and its laws (t-k mentions ∘).
3. Still inductive-inductive-recursive (∘, wkTy in constructor types);
   eliminating that (Szumi's proposal) is a separate step.
-}
{-# OPTIONS --without-K #-}
open import Agda.Builtin.Equality

sym : {X : Set}{a b : X} → a ≡ b → b ≡ a
sym refl = refl

cong : {X Y : Set}(f : X → Y){a b : X} → a ≡ b → f a ≡ f b
cong f refl = refl

-- Σ, Dec, Hedberg ---------------------------------------------------

record Σ (X : Set)(Y : X → Set) : Set where
  constructor _,_
  field fst : X
        snd : Y fst
open Σ

data ⊥ : Set where

⊥-elim : {X : Set} → ⊥ → X
⊥-elim ()

data Bool : Set where
  true false : Bool

true≢false : true ≡ false → ⊥
true≢false ()

data Dec (X : Set) : Set where
  yes : X → Dec X
  no : (X → ⊥) → Dec X

trans : {X : Set}{a b c : X} → a ≡ b → b ≡ c → a ≡ c
trans refl q = q

inv-l : {X : Set}{a b : X}(q : a ≡ b) → trans (sym q) q ≡ refl
inv-l refl = refl

module Hedberg {X : Set}{a : X}(dec : (b : X) → Dec (a ≡ b)) where

  f : {b : X} → a ≡ b → a ≡ b
  f {b} e with dec b
  ... | yes q = q
  ... | no n = ⊥-elim (n e)

  f-const : {b : X}(e e' : a ≡ b) → f e ≡ f e'
  f-const {b} e e' with dec b
  ... | yes q = refl
  ... | no n = ⊥-elim (n e)

  canon : {b : X}(e : a ≡ b) → e ≡ trans (sym (f refl)) (f e)
  canon refl = sym (inv-l (f refl))

  uip : {b : X}(e e' : a ≡ b) → e ≡ e'
  uip e e' = trans (canon e)
               (trans (cong (trans (sym (f refl))) (f-const e e'))
                      (sym (canon e')))


data U : Set
data El : U → Set

data U where
    con : U
    ty : El con → U
    var : (Γ : El con) → El (ty Γ) → U
    wk : El con → El con → U
    thin : {Γ : El con} → El (ty Γ) → El (ty Γ) → U

Con : Set
Con = El con

variable Γ Δ : Con

Ty : Con → Set
Ty Γ = El (ty Γ)

variable A B C D : Ty Γ

Var : (Γ : Con) → Ty Γ → Set
Var Γ A = El (var Γ A)

Wk : Con → Con → Set
Wk Γ Δ = El (wk Γ Δ)

Thin : {Γ : Con} → Ty Γ → Ty Γ → Set
Thin A B = El (thin A B)

wkTy : Ty Γ → Wk Δ Γ → Ty Δ
wkThin : Thin A B → (w : Wk Δ Γ) → Thin (wkTy A w) (wkTy B w)

_∘_ : Thin B C → Thin A B → Thin A C

variable x y z : Var Γ A

data El where
    • : Con
    _▷_ : (Γ : Con) → Ty Γ → Con

    p : Wk (Γ ▷ A) Γ

    ε : Ty Γ
    ext : (A : Ty Γ) → Var Γ B → Thin A B → Ty Γ

    zero : Var (Γ ▷ A) (wkTy A p)
    suc : Var Γ A → Var (Γ ▷ B) (wkTy A p)

    tε : Thin (ε {Γ = Γ}) ε
    t-k : {δ : Thin B C}{δ' : Thin A C}
          (σ : Thin A B) → δ ∘ σ ≡ δ' → Thin (ext A x δ') (ext B x δ)
    t-d : {δ : Thin A C} (σ : Thin A B) → Thin (ext A x δ) B

-- weakening of variables (only by p)
wkVar : Var Γ A → (w : Wk Δ Γ) → Var Δ (wkTy A w)
wkVar x p = suc x

variable δ σ ρ : Thin A B

-- equality helpers

t-d-cong : {δ : Thin A C}{σ σ' : Thin A B} → σ ≡ σ' → t-d {x = x}{δ = δ} σ ≡ t-d σ'
t-d-cong refl = refl

-- total spaces --------------------------------------------------------

VarΣ : Con → Set
VarΣ Γ = Σ (Ty Γ) (Var Γ)

ThinΣ : Con → Set
ThinΣ Γ = Σ (Σ (Ty Γ) (λ _ → Ty Γ)) (λ AB → Thin (fst AB) (snd AB))

-- deciders ------------------------------------------------------------

decCon : (Γ Δ : Con) → Dec (Γ ≡ Δ)
decTy : (A B : Ty Γ) → Dec (A ≡ B)
decVar : (x y : VarΣ Γ) → Dec (x ≡ y)
decThinΣ : (σ τ : ThinΣ Γ) → Dec (σ ≡ τ)

uipTy : {A B : Ty Γ}(e e' : A ≡ B) → e ≡ e'
uipTy {A = A} = Hedberg.uip (decTy A)

-- homogeneous Thin from the total space, using uipTy (hole)
decThin : (σ τ : Thin A B) → Dec (σ ≡ τ)
decThin σ τ = {!!}

uipThin : {σ σ' : Thin A B}(e e' : σ ≡ σ') → e ≡ e'
uipThin {σ = σ} = Hedberg.uip (decThin σ)

-- Con
▷-inj : {Γ Δ : Con}{A : Ty Γ}{B : Ty Δ} → (Γ ▷ A) ≡ (Δ ▷ B) → Γ ≡ Δ
▷-inj refl = refl

decCon • • = yes refl
decCon • (Δ ▷ B) = no (λ ())
decCon (Γ ▷ A) • = no (λ ())
decCon (Γ ▷ A) (Δ ▷ B) with decCon Γ Δ
... | no n = no (λ q → n (▷-inj q))
... | yes refl with decTy A B
...   | yes refl = yes refl
...   | no n = no {!!} -- injectivity in A, after Γ ≡ Γ (needs uipCon)

-- Var: discriminate and project instead of matching on equations
isZero : VarΣ Γ → Bool
isZero (_ , zero) = true
isZero (_ , suc _) = false

pred : {B : Ty Γ} → VarΣ Γ → VarΣ (Γ ▷ B) → VarΣ Γ
pred d (_ , zero) = d
pred d (_ , suc x) = (_ , x)

decVar {Γ = • } (_ , ()) _
decVar {Γ = Γ ▷ B} (_ , zero) (_ , zero) = yes refl
decVar {Γ = Γ ▷ B} (_ , zero) (_ , suc y) = no (λ q → true≢false (cong isZero q))
decVar {Γ = Γ ▷ B} (_ , suc x) (_ , zero) = no (λ q → true≢false (cong isZero (sym q)))
decVar {Γ = Γ ▷ B} (_ , suc x) (_ , suc y) with decVar (_ , x) (_ , y)
... | yes refl = yes refl
... | no n = no (λ q → n (cong (pred (_ , x)) q))

-- Ty
decTy ε ε = yes refl
decTy ε (ext _ _ _) = no (λ ())
decTy (ext _ _ _) ε = no (λ ())
decTy (ext A x δ) (ext A' x' δ') = {!!}
  -- decTy A A', then decVar (_ , x) (_ , x'), then decThinΣ on δ, δ';
  -- "no" cases via projections out of Ty with a default

-- Thin over the total space
decThinΣ σ τ = {!!}
  -- t-k / t-k: compare σ's, then the proofs e, e' via uipThin on the
  -- shorter source telescope (termination: see open problem 1)

t-k-cong : {δ : Thin B C}{δ' : Thin A C}{σ σ' : Thin A B}
           {e : δ ∘ σ ≡ δ'}{e' : δ ∘ σ' ≡ δ'} →
           σ ≡ σ' → t-k {x = x} σ e ≡ t-k σ' e'
t-k-cong {e = e} {e'} refl = cong (t-k _) (uipThin e e')

∘-assoc : (ρ : Thin C D)(δ : Thin B C)(σ : Thin A B) → ρ ∘ (δ ∘ σ) ≡ (ρ ∘ δ) ∘ σ

∘-k : {ρ : Thin C D}{δ : Thin B C}{σ : Thin A B}{δB : Thin B D}{δA : Thin A D}
      → ρ ∘ δ ≡ δB → δB ∘ σ ≡ δA → ρ ∘ (δ ∘ σ) ≡ δA
∘-k {ρ = ρ}{δ}{σ} refl refl = ∘-assoc ρ δ σ

δ ∘ tε = δ
δ ∘ t-d σ = t-d (δ ∘ σ)
t-d δ ∘ t-k σ e = t-d (δ ∘ σ)
t-k δ e ∘ t-k σ e' = t-k (δ ∘ σ) (∘-k e e')

∘-assoc ρ δ tε = refl
∘-assoc ρ δ (t-d σ) = t-d-cong (∘-assoc ρ δ σ)
∘-assoc ρ (t-d δ) (t-k σ e) = t-d-cong (∘-assoc ρ δ σ)
∘-assoc (t-d ρ) (t-k δ e) (t-k σ e') = t-d-cong (∘-assoc ρ δ σ)
∘-assoc (t-k ρ e) (t-k δ e') (t-k σ e'') = t-k-cong (∘-assoc ρ δ σ)

-- identity thinning
id : Thin A A
∘-id : (δ : Thin A B) → δ ∘ id ≡ δ

id {A = ε} = tε
id {A = ext A x δ} = t-k id (∘-id δ)

∘-id tε = refl
∘-id (t-k δ e) = t-k-cong (∘-id δ)
∘-id (t-d δ) = t-d-cong (∘-id δ)

-- weakening
wkThin-∘ : (δ : Thin B C)(σ : Thin A B)(w : Wk Δ Γ) → wkThin (δ ∘ σ) w ≡ wkThin δ w ∘ wkThin σ w

wk-k : {δ : Thin B C}{σ : Thin A B}{δ' : Thin A C}(w : Wk Δ Γ)
       → δ ∘ σ ≡ δ' → wkThin δ w ∘ wkThin σ w ≡ wkThin δ' w
wk-k {δ = δ}{σ} w refl = sym (wkThin-∘ δ σ w)

wkTy ε w = ε
wkTy (ext A x δ) w = ext (wkTy A w) (wkVar x w) (wkThin δ w)

wkThin tε w = tε
wkThin (t-k {δ = δ} σ e) w = t-k (wkThin σ w) (wk-k {δ = δ} {σ = σ} w e)
wkThin (t-d σ) w = t-d (wkThin σ w)

wkThin-∘ δ tε w = refl
wkThin-∘ δ (t-d σ) w = t-d-cong (wkThin-∘ δ σ w)
wkThin-∘ (t-d δ) (t-k σ e) w = t-d-cong (wkThin-∘ δ σ w)
wkThin-∘ (t-k δ e) (t-k σ e') w = t-k-cong (wkThin-∘ δ σ w)
