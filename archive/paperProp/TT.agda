{-
A type theory for semi-simplicial (semi-cubical, ...) types using only
weakenings. No --rewriting:

* Wk has a single constructor p : Wk (Γ ▷ A) Γ (one-step weakening), so
  wkTy A idw ≡ A is never needed; wkVar x p = suc x.
* The commuting square of a kept assumption is stored as a field:
    t-k : (σ : Thin A B) → δ ∘ σ ≡ₚ δ' → Thin (ext A x δ') (ext B x δ)
  instead of indexing by δ ∘ σ. The laws needed to build these proofs
  (∘-assoc, ∘-id, wkThin-∘) are proven mutually with the operations.
  The equation lives in Prop (_≡ₚ_), so proofs are definitionally
  irrelevant and t-k-cong needs no K: this file checks with --without-K.
-}
{-# OPTIONS --without-K --prop #-}
open import Agda.Builtin.Equality

data _≡ₚ_ {X : Set}(a : X) : X → Prop where
  reflₚ : a ≡ₚ a

infix 4 _≡ₚ_
toₚ : {X : Set}{a b : X} → a ≡ b → a ≡ₚ b
toₚ refl = reflₚ

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
          (σ : Thin A B) → δ ∘ σ ≡ₚ δ' → Thin (ext A x δ') (ext B x δ)
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

t-k-cong : {δ : Thin B C}{δ' : Thin A C}{σ σ' : Thin A B}
           {e : δ ∘ σ ≡ₚ δ'}{e' : δ ∘ σ' ≡ₚ δ'} →
           σ ≡ σ' → t-k {x = x} σ e ≡ t-k σ' e'
t-k-cong refl = refl

∘-assoc : (ρ : Thin C D)(δ : Thin B C)(σ : Thin A B) → ρ ∘ (δ ∘ σ) ≡ (ρ ∘ δ) ∘ σ

∘-k : {ρ : Thin C D}{δ : Thin B C}{σ : Thin A B}{δB : Thin B D}{δA : Thin A D}
      → ρ ∘ δ ≡ₚ δB → δB ∘ σ ≡ₚ δA → ρ ∘ (δ ∘ σ) ≡ₚ δA
∘-k {ρ = ρ}{δ}{σ} reflₚ reflₚ = toₚ (∘-assoc ρ δ σ)

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
id {A = ext A x δ} = t-k id (toₚ (∘-id δ))

∘-id tε = refl
∘-id (t-k δ e) = t-k-cong (∘-id δ)
∘-id (t-d δ) = t-d-cong (∘-id δ)

-- weakening
wkThin-∘ : (δ : Thin B C)(σ : Thin A B)(w : Wk Δ Γ) → wkThin (δ ∘ σ) w ≡ wkThin δ w ∘ wkThin σ w

wk-k : {δ : Thin B C}{σ : Thin A B}{δ' : Thin A C}(w : Wk Δ Γ)
       → δ ∘ σ ≡ₚ δ' → wkThin δ w ∘ wkThin σ w ≡ₚ wkThin δ' w
wk-k {δ = δ}{σ} w reflₚ = toₚ (sym (wkThin-∘ δ σ w))

wkTy ε w = ε
wkTy (ext A x δ) w = ext (wkTy A w) (wkVar x w) (wkThin δ w)

wkThin tε w = tε
wkThin (t-k {δ = δ} σ e) w = t-k (wkThin σ w) (wk-k {δ = δ} {σ = σ} w e)
wkThin (t-d σ) w = t-d (wkThin σ w)

wkThin-∘ δ tε w = refl
wkThin-∘ δ (t-d σ) w = t-d-cong (wkThin-∘ δ σ w)
wkThin-∘ (t-d δ) (t-k σ e) w = t-d-cong (wkThin-∘ δ σ w)
wkThin-∘ (t-k δ e) (t-k σ e') w = t-k-cong (wkThin-∘ δ σ w)
