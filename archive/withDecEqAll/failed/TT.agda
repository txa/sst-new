{-
*** FAILED ATTEMPT — does not check. ***
Hedberg itself is fine, but decThin cannot match two t-k's against each
other under --without-K: the index Thin (ext A x δ') (ext B x δ)
mentions x (and its type C) twice, so unification needs to delete the
reflexive equation C = C in El (ty Γ), i.e. UIP for Ty, not just Thin.
The same blocks t-k-inj (left as a hole).
-}
{-
A type theory for semi-simplicial (semi-cubical, ...) types using only
weakenings. No --rewriting:

* Wk has a single constructor p : Wk (Γ ▷ A) Γ (one-step weakening), so
  wkTy A idw ≡ A is never needed; wkVar x p = suc x.
* The commuting square of a kept assumption is stored as a field:
    t-k : (σ : Thin A B) → δ ∘ σ ≡ δ' → Thin (ext A x δ') (ext B x δ)
  instead of indexing by δ ∘ σ. The laws needed to build these proofs
  (∘-assoc, ∘-id, wkThin-∘) are proven mutually with the operations.
  Uniqueness of the proofs (t-k-cong) is UIP for Thin, which we derive
  without K: equality of thinnings is decidable, hence (Hedberg) Thin
  is a set. This file checks with --without-K.
-}
{-# OPTIONS --without-K #-}
open import Agda.Builtin.Equality

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
sym : {X : Set}{a b : X} → a ≡ b → b ≡ a
sym refl = refl

cong : {X Y : Set}(f : X → Y){a b : X} → a ≡ b → f a ≡ f b
cong f refl = refl

t-d-cong : {δ : Thin A C}{σ σ' : Thin A B} → σ ≡ σ' → t-d {x = x}{δ = δ} σ ≡ t-d σ'
t-d-cong refl = refl

-- UIP for Thin via Hedberg's theorem: equality of thinnings is decidable.
-- decThin and uipThin are mutually recursive with decreasing domain
-- (the t-k case needs UIP for thinnings out of the shorter telescope).

data ⊥ : Set where

⊥-elim : {X : Set} → ⊥ → X
⊥-elim ()

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

decThin : (σ σ' : Thin A B) → Dec (σ ≡ σ')
uipThin : {σ σ' : Thin A B}(e e' : σ ≡ σ') → e ≡ e'
uipThin {σ = σ} = Hedberg.uip (decThin σ)

t-d-inj : {δ : Thin A C}{σ σ' : Thin A B} → t-d {x = x}{δ = δ} σ ≡ t-d σ' → σ ≡ σ'
t-d-inj refl = refl

t-k-inj : {δ : Thin B C}{δ' : Thin A C}{σ σ' : Thin A B}
          {e : δ ∘ σ ≡ δ'}{e' : δ ∘ σ' ≡ δ'} →
          t-k {x = x} σ e ≡ t-k σ' e' → σ ≡ σ'
t-k-inj = {!!}

t-k-cong : {δ : Thin B C}{δ' : Thin A C}{σ σ' : Thin A B}
           {e : δ ∘ σ ≡ δ'}{e' : δ ∘ σ' ≡ δ'} →
           σ ≡ σ' → t-k {x = x} σ e ≡ t-k σ' e'
t-k-cong {e = e} {e'} refl = cong (t-k _) (uipThin e e')

decThin tε tε = yes refl
decThin (t-d σ) (t-d σ') with decThin σ σ'
... | yes q = yes (t-d-cong q)
... | no n = no (λ q → n (t-d-inj q))
decThin (t-d σ) (t-k σ' e') = no (λ ())
decThin (t-k σ e) (t-d σ') = no (λ ())
decThin (t-k σ e) (t-k σ' e') with decThin σ σ'
... | yes q = yes (t-k-cong q)
... | no n = no (λ q → n (t-k-inj q))

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
