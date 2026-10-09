{-
SST : ℕ → Con, the context of semi-simplicial types up to level n.

  SST n = X₀ , X₁ , ... , Xₙ   where   Xₖ : ∂Δ[k] → Set

The boundary ∂Δ[n] lists the proper nonempty faces of {0..n}, ordered by
dimension and then lexicographically (as in plan.agda). It is produced by
an elaborator: faces are described combinatorially (sorted lists of
vertices) and turned into syntax; each thinning is built from a keep/drop
list, checking variables with decVar and the commuting square of t-k
with decThin (decidable equality uses K, like TT.agda).

So SST is total, but correctness (the elaborator never fails) is only
checked for concrete n by computation, see the tests at the end; a
failure would show up as ε in place of a boundary.
-}
module SSTn where

open import TT
open import Agda.Builtin.Equality
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Sigma

data ⊥ : Set where

data Dec (X : Set) : Set where
  yes : X → Dec X
  no : (X → ⊥) → Dec X

data Maybe (X : Set) : Set where
  nothing : Maybe X
  just : X → Maybe X

-- decidable equality of the syntax (uses K) -------------------------

VarΣ : Con → Set
VarΣ Γ = Σ (Ty Γ) (Var Γ)

decTy : (A B : Ty Γ) → Dec (A ≡ B)
decVar : (x y : VarΣ Γ) → Dec (x ≡ y)
decThin : (σ τ : Thin A B) → Dec (σ ≡ τ)

-- zero and suc have computed indices (wkTy A p), so we discriminate and
-- project instead of matching on equations between them
isZero : VarΣ Γ → Bool
isZero (_ , zero) = true
isZero (_ , suc _) = false

predV : {B : Ty Γ} → VarΣ Γ → VarΣ (Γ ▷ B) → VarΣ Γ
predV d (_ , zero) = d
predV d (_ , suc x) = (_ , x)

true≢false : true ≡ false → ⊥
true≢false ()

decVar {Γ = •} (_ , ()) _
decVar {Γ = Γ ▷ B} (_ , zero) (_ , zero) = yes refl
decVar {Γ = Γ ▷ B} (_ , zero) (_ , suc y) = no (λ q → true≢false (cong isZero q))
decVar {Γ = Γ ▷ B} (_ , suc x) (_ , zero) = no (λ q → true≢false (cong isZero (sym q)))
decVar {Γ = Γ ▷ B} (_ , suc x) (_ , suc y) with decVar (_ , x) (_ , y)
... | yes refl = yes refl
... | no n = no (λ q → n (cong (predV (_ , x)) q))

ext-inj₁ : {x : Var Γ C}{x' : Var Γ D}{δ : Thin A C}{δ' : Thin B D}
         → ext A x δ ≡ ext B x' δ' → A ≡ B
ext-inj₁ refl = refl

ext-inj₂ : {x : Var Γ C}{x' : Var Γ D}{δ : Thin A C}{δ' : Thin A D}
         → ext A x δ ≡ ext A x' δ' → (C , x) ≡ (D , x')
ext-inj₂ refl = refl

ext-inj₃ : {x : Var Γ C}{δ δ' : Thin A C} → ext A x δ ≡ ext A x δ' → δ ≡ δ'
ext-inj₃ refl = refl

decTy ε ε = yes refl
decTy ε (ext _ _ _) = no (λ ())
decTy (ext _ _ _) ε = no (λ ())
decTy (ext A x δ) (ext A' x' δ') with decTy A A'
... | no n = no (λ q → n (ext-inj₁ q))
... | yes refl with decVar (_ , x) (_ , x')
...   | no n = no (λ q → n (ext-inj₂ q))
...   | yes refl with decThin δ δ'
...     | no n = no (λ q → n (ext-inj₃ q))
...     | yes refl = yes refl

t-d-inj : {δ : Thin A C}{σ σ' : Thin A B} → t-d {x = x}{δ = δ} σ ≡ t-d σ' → σ ≡ σ'
t-d-inj refl = refl

t-k-inj : {δ : Thin B C}{δ' : Thin A C}{σ σ' : Thin A B}
          {e : δ ∘ σ ≡ δ'}{e' : δ ∘ σ' ≡ δ'} →
          t-k {x = x} σ e ≡ t-k σ' e' → σ ≡ σ'
t-k-inj refl = refl

decThin tε tε = yes refl
decThin (t-d σ) (t-d σ') with decThin σ σ'
... | yes refl = yes refl
... | no n = no (λ q → n (t-d-inj q))
decThin (t-d σ) (t-k σ' e') = no (λ ())
decThin (t-k σ e) (t-d σ') = no (λ ())
decThin (t-k σ e) (t-k σ' e') with decThin σ σ'
... | yes refl = yes (t-k-cong refl)
... | no n = no (λ q → n (t-k-inj q))

-- thinnings from keep/drop lists ---------------------------------------
-- the list is read from the last entry of the telescope backwards

build : (T U : Ty Γ) → List Bool → Maybe (Thin T U)
build ε ε [] = just tε
build (ext T y δ) U (false ∷ bs) with build T U bs
... | nothing = nothing
... | just σ = just (t-d σ)
build (ext T y δ) (ext U y' δ') (true ∷ bs) with decVar (_ , y) (_ , y')
... | no _ = nothing
... | yes refl with build T U bs
...   | nothing = nothing
...   | just σ with decThin (δ' ∘ σ) δ
...     | yes e = just (t-k σ e)
...     | no _ = nothing
build _ _ _ = nothing

-- combinatorics of faces ---------------------------------------------

Face = List Nat   -- a sorted list of vertices

_++_ : {X : Set} → List X → List X → List X
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

map : {X Y : Set} → (X → Y) → List X → List Y
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

reverse : {X : Set} → List X → List X
reverse [] = []
reverse (x ∷ xs) = reverse xs ++ (x ∷ [])

length : {X : Set} → List X → Nat
length [] = 0
length (_ ∷ xs) = suc (length xs)

-- k-element subsets in lexicographic order
choose : Nat → List Nat → List Face
choose zero _ = [] ∷ []
choose (suc k) [] = []
choose (suc k) (x ∷ xs) = map (x ∷_) (choose k xs) ++ choose (suc k) xs

upto : Nat → List Nat   -- [0 .. n]
upto zero = 0 ∷ []
upto (suc n) = upto n ++ (suc n ∷ [])

-- proper nonempty faces of Δ[n]: dimensions 0 .. n-1
faces : Nat → List Face
faces n = go n
  where go : Nat → List Face   -- faces of dimension < k, k ≤ n
        go zero = []
        go (suc k) = go k ++ choose (suc k) (upto n)

if_then_else_ : {X : Set} → Bool → X → X → X
if true then x else y = x
if false then x else y = y

elem : Nat → Face → Bool
elem x [] = false
elem x (y ∷ ys) = if x == y then true else elem x ys

_⊆_ : Face → Face → Bool
[] ⊆ S = true
(t ∷ T) ⊆ S = if elem t S then T ⊆ S else false

-- the contexts ----------------------------------------------------------

data _<'_ : Nat → Nat → Set where
  base : {d : Nat} → d <' suc d
  step : {d m : Nat} → d <' m → d <' suc m

eqNat : (a b : Nat) → Maybe (a ≡ b)
eqNat zero zero = just refl
eqNat (suc a) (suc b) with eqNat a b
... | just refl = just refl
... | nothing = nothing
eqNat _ _ = nothing

<'? : (d n : Nat) → Maybe (d <' n)
<'? d zero = nothing
<'? d (suc m) with eqNat d m
... | just refl = just base
... | nothing with <'? d m
...   | just l = just (step l)
...   | nothing = nothing

ctx : Nat → Con
∂Δ : (n : Nat) → Ty (ctx n)

-- the domain of X_d, weakened into ctx n
W : {d n : Nat} → d <' n → Ty (ctx n)
-- the variable X_d in ctx n
X : {d n : Nat}(l : d <' n) → Var (ctx n) (W l)

ctx zero = •
ctx (suc n) = ctx n ▷ ∂Δ n

W {d} base = wkTy (∂Δ d) p
W (step l) = wkTy (W l) p

X base = zero
X (step l) = suc (X l)

elab : (n : Nat) → Maybe (Ty (ctx n))
elab n = go (faces n) ε []
  where
  -- T is the telescope so far, prev the faces already in T (in order)
  go : List Face → Ty (ctx n) → List Face → Maybe (Ty (ctx n))
  go [] T prev = just T
  go (S ∷ Ss) T prev with <'? (length S - 1) n
  ... | nothing = nothing
  ... | just l with build T (W l) (reverse (map (_⊆ S) prev))
  ...   | nothing = nothing
  ...   | just δ = go Ss (ext T (X l) δ) (prev ++ (S ∷ []))

∂Δ n with elab n
... | just A = A
... | nothing = ε

-- semi-simplicial types up to level n: X₀ ... Xₙ
SST : Nat → Con
SST n = ctx (suc n)

-- tests ---------------------------------------------------------------

open import SST using (Γ₀; Γ₁; Γ₂)

_ : SST 0 ≡ Γ₀
_ = refl

_ : SST 1 ≡ Γ₁
_ = refl

_ : SST 2 ≡ Γ₂
_ = refl

-- the elaborator succeeds for levels 3 and 4
isJust : {X : Set} → Maybe X → Bool
isJust nothing = false
isJust (just _) = true

_ : isJust (elab 3) ≡ true
_ = refl

_ : isJust (elab 4) ≡ true
_ = refl

-- ∂Δ[n] has 2ⁿ⁺¹ - 2 entries
size : Ty Γ → Nat
size ε = 0
size (ext A _ _) = suc (size A)

_ : size (∂Δ 3) ≡ 14
_ = refl

_ : size (∂Δ 4) ≡ 30
_ = refl
