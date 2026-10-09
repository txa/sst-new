{-# OPTIONS --without-K #-}
{-
TT without K, without Prop and without rewriting: the commuting square of
a kept assumption is stored as a *decidable* boolean proposition, whose
proofs are unique by definition (T true = ⊤ has η, T false = ⊥ is empty).
No Hedberg is needed.

Changes w.r.t. ../TT.agda:
* t-k has separate source and target variables x, y with T (x ≈ᵥ y), so no
  index is repeated and pattern matching works without K;
* the equation compares raw bit vectors:  T (⌊ δ ⌋ ∘ᵦ ⌊ σ ⌋ == ⌊ δ' ⌋),
  so composition of thinnings no longer occurs in constructor types.
-}
module TT where

open import Agda.Builtin.Equality
open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Unit

data ⊥ : Set where

T : Bool → Set
T true = ⊤
T false = ⊥

T-prop : (b : Bool)(u v : T b) → u ≡ v
T-prop true u v = refl
T-prop false () v

sym : {X : Set}{a b : X} → a ≡ b → b ≡ a
sym refl = refl

cong : {X Y : Set}(f : X → Y){a b : X} → a ≡ b → f a ≡ f b
cong f refl = refl

infixr 5 _∙_
_∙_ : {X : Set}{a b c : X} → a ≡ b → b ≡ c → a ≡ c
refl ∙ q = q

subst : {X : Set}(P : X → Set){a b : X} → a ≡ b → P a → P b
subst P refl y = y

-- raw thinnings: bit vectors, last entry first --------------------------

Bits : Set
Bits = List Bool

infixl 9 _∘ᵦ_
_∘ᵦ_ : Bits → Bits → Bits
d ∘ᵦ [] = d
d ∘ᵦ (false ∷ s) = false ∷ (d ∘ᵦ s)
[] ∘ᵦ (true ∷ s) = true ∷ ([] ∘ᵦ s)
(b ∷ d) ∘ᵦ (true ∷ s) = b ∷ (d ∘ᵦ s)

[]∘ᵦ : (s : Bits) → [] ∘ᵦ s ≡ s
[]∘ᵦ [] = refl
[]∘ᵦ (false ∷ s) = cong (false ∷_) ([]∘ᵦ s)
[]∘ᵦ (true ∷ s) = cong (true ∷_) ([]∘ᵦ s)

∘ᵦ-assoc : (a b c : Bits) → a ∘ᵦ (b ∘ᵦ c) ≡ (a ∘ᵦ b) ∘ᵦ c
∘ᵦ-assoc a b [] = refl
∘ᵦ-assoc a b (false ∷ c) = cong (false ∷_) (∘ᵦ-assoc a b c)
∘ᵦ-assoc a [] (true ∷ c) = cong (a ∘ᵦ_) (cong (true ∷_) ([]∘ᵦ c))
∘ᵦ-assoc [] (b ∷ bs) (true ∷ c) =
  []∘ᵦ ((b ∷ bs) ∘ᵦ (true ∷ c)) ∙ sym (cong (_∘ᵦ (true ∷ c)) ([]∘ᵦ (b ∷ bs)))
∘ᵦ-assoc (a ∷ as) (false ∷ bs) (true ∷ c) = cong (false ∷_) (∘ᵦ-assoc (a ∷ as) bs c)
∘ᵦ-assoc (a ∷ as) (true ∷ bs) (true ∷ c) = cong (a ∷_) (∘ᵦ-assoc as bs c)

_==ᵇ_ : Bool → Bool → Bool
true ==ᵇ true = true
false ==ᵇ false = true
_ ==ᵇ _ = false

_&&_ : Bool → Bool → Bool
true && b = b
false && b = false

infix 4 _==_
_==_ : Bits → Bits → Bool
[] == [] = true
(a ∷ as) == (b ∷ bs) = (a ==ᵇ b) && (as == bs)
_ == _ = false

==-sound : (l l' : Bits) → T (l == l') → l ≡ l'
==-sound [] [] t = refl
==-sound (true ∷ as) (true ∷ bs) t = cong (true ∷_) (==-sound as bs t)
==-sound (false ∷ as) (false ∷ bs) t = cong (false ∷_) (==-sound as bs t)
==-sound [] (b ∷ bs) ()
==-sound (a ∷ as) [] ()
==-sound (true ∷ as) (false ∷ bs) ()
==-sound (false ∷ as) (true ∷ bs) ()

==-refl : (l : Bits) → T (l == l)
==-refl [] = tt
==-refl (true ∷ l) = ==-refl l
==-refl (false ∷ l) = ==-refl l

≡→T : {l l' : Bits} → l ≡ l' → T (l == l')
≡→T {l} refl = ==-refl l

-- syntax ----------------------------------------------------------------

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

variable A B C C' D : Ty Γ

Var : (Γ : Con) → Ty Γ → Set
Var Γ A = El (var Γ A)

Wk : Con → Con → Set
Wk Γ Δ = El (wk Γ Δ)

Thin : {Γ : Con} → Ty Γ → Ty Γ → Set
Thin A B = El (thin A B)

wkTy : Ty Γ → Wk Δ Γ → Ty Δ
⌊_⌋ : Thin A B → Bits
_≈ᵥ_ : Var Γ C → Var Γ C' → Bool

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
    t-k : {x : Var Γ C}{y : Var Γ C'}{δ : Thin B C'}{δ' : Thin A C}
          (σ : Thin A B) → T (x ≈ᵥ y) → T (⌊ δ ⌋ ∘ᵦ ⌊ σ ⌋ == ⌊ δ' ⌋)
        → Thin (ext A x δ') (ext B y δ)
    t-d : {x : Var Γ C}{δ : Thin A C}(σ : Thin A B) → Thin (ext A x δ) B

⌊ tε ⌋ = []
⌊ t-k σ _ _ ⌋ = true ∷ ⌊ σ ⌋
⌊ t-d σ ⌋ = false ∷ ⌊ σ ⌋

zero ≈ᵥ zero = true
suc x ≈ᵥ suc y = x ≈ᵥ y
_ ≈ᵥ _ = false

≈-refl : (x : Var Γ C) → T (x ≈ᵥ x)
≈-refl zero = tt
≈-refl (suc x) = ≈-refl x

≈-trans : (x : Var Γ C)(y : Var Γ C')(z : Var Γ D) → T (x ≈ᵥ y) → T (y ≈ᵥ z) → T (x ≈ᵥ z)
≈-trans zero zero zero t u = tt
≈-trans (suc x) (suc y) (suc z) t u = ≈-trans x y z t u
≈-trans zero (suc y) z () u
≈-trans (suc x) zero z () u
≈-trans zero zero (suc z) t ()
≈-trans (suc x) (suc y) zero t ()

-- weakening of variables (only by p)
wkVar : Var Γ A → (w : Wk Δ Γ) → Var Δ (wkTy A w)
wkVar x p = suc x

variable δ σ ρ : Thin A B

t-d-cong : {δ : Thin A C}{σ σ' : Thin A B} → σ ≡ σ' → t-d {x = x}{δ = δ} σ ≡ t-d σ'
t-d-cong refl = refl

-- no K: the stored proofs are unique because T b is a proposition
t-k-cong : {x : Var Γ C}{y : Var Γ C'}{δ : Thin B C'}{δ' : Thin A C}{σ σ' : Thin A B}
           {ex ex' : T (x ≈ᵥ y)}{e : T (⌊ δ ⌋ ∘ᵦ ⌊ σ ⌋ == ⌊ δ' ⌋)}{e' : T (⌊ δ ⌋ ∘ᵦ ⌊ σ' ⌋ == ⌊ δ' ⌋)}
         → σ ≡ σ' → t-k {x = x}{y = y}{δ = δ}{δ' = δ'} σ ex e ≡ t-k σ' ex' e'
t-k-cong {x = x}{y}{δ}{δ'}{σ}{ex = ex}{ex'}{e}{e'} refl =
  helper (T-prop (x ≈ᵥ y) ex ex') (T-prop (⌊ δ ⌋ ∘ᵦ ⌊ σ ⌋ == ⌊ δ' ⌋) e e')
  where helper : ex ≡ ex' → e ≡ e' → t-k σ ex e ≡ t-k σ ex' e'
        helper refl refl = refl

-- composition ----------------------------------------------------------

_∘_ : Thin B C → Thin A B → Thin A C
⌊∘⌋ : (δ : Thin B C)(σ : Thin A B) → ⌊ δ ∘ σ ⌋ ≡ ⌊ δ ⌋ ∘ᵦ ⌊ σ ⌋

-- the stored equation of a composite of two keeps
k-bits : {D₁ D₂ D₃ : Ty Γ}(δC : Thin C D₁)(δB : Thin B D₂)(δA : Thin A D₃)(δ : Thin B C)(σ : Thin A B)
       → T (⌊ δC ⌋ ∘ᵦ ⌊ δ ⌋ == ⌊ δB ⌋) → T (⌊ δB ⌋ ∘ᵦ ⌊ σ ⌋ == ⌊ δA ⌋)
       → T (⌊ δC ⌋ ∘ᵦ ⌊ δ ∘ σ ⌋ == ⌊ δA ⌋)
k-bits δC δB δA δ σ q e = ≡→T
  (cong (⌊ δC ⌋ ∘ᵦ_) (⌊∘⌋ δ σ)
   ∙ ∘ᵦ-assoc ⌊ δC ⌋ ⌊ δ ⌋ ⌊ σ ⌋
   ∙ cong (_∘ᵦ ⌊ σ ⌋) (==-sound _ _ q)
   ∙ ==-sound _ _ e)

δ ∘ tε = δ
δ ∘ t-d σ = t-d (δ ∘ σ)
t-d δ ∘ t-k σ ex e = t-d (δ ∘ σ)
t-k {x = y}{y = z}{δ = δC}{δ' = δB} δ ey q ∘ t-k {x = x}{δ' = δA} σ ex e =
  t-k (δ ∘ σ) (≈-trans x y z ex ey) (k-bits δC δB δA δ σ q e)

⌊∘⌋ δ tε = refl
⌊∘⌋ δ (t-d σ) = cong (false ∷_) (⌊∘⌋ δ σ)
⌊∘⌋ (t-d δ) (t-k σ ex e) = cong (false ∷_) (⌊∘⌋ δ σ)
⌊∘⌋ (t-k δ ey q) (t-k σ ex e) = cong (true ∷_) (⌊∘⌋ δ σ)

∘-assoc : (ρ : Thin C D)(δ : Thin B C)(σ : Thin A B) → ρ ∘ (δ ∘ σ) ≡ (ρ ∘ δ) ∘ σ
∘-assoc ρ δ tε = refl
∘-assoc ρ δ (t-d σ) = t-d-cong (∘-assoc ρ δ σ)
∘-assoc ρ (t-d δ) (t-k σ ex e) = t-d-cong (∘-assoc ρ δ σ)
∘-assoc (t-d ρ) (t-k δ ey q) (t-k σ ex e) = t-d-cong (∘-assoc ρ δ σ)
∘-assoc (t-k ρ ez r) (t-k δ ey q) (t-k σ ex e) = t-k-cong (∘-assoc ρ δ σ)

-- identity -------------------------------------------------------------

id : Thin A A
idr-bits : (δ : Thin A C) → ⌊ δ ⌋ ∘ᵦ ⌊ id {A = A} ⌋ ≡ ⌊ δ ⌋

id {A = ε} = tε
id {A = ext A x δ} = t-k id (≈-refl x) (≡→T (idr-bits δ))

idr-bits tε = refl
idr-bits (t-d δ) = cong (false ∷_) (idr-bits δ)
idr-bits (t-k δ ex e) = cong (true ∷_) (idr-bits δ)

∘-id : (δ : Thin A B) → δ ∘ id ≡ δ
∘-id tε = refl
∘-id (t-k δ ex e) = t-k-cong (∘-id δ)
∘-id (t-d δ) = t-d-cong (∘-id δ)

id-∘ : (δ : Thin A B) → id ∘ δ ≡ δ
id-∘ tε = refl
id-∘ (t-d δ) = t-d-cong (id-∘ δ)
id-∘ (t-k δ ex e) = t-k-cong (id-∘ δ)

-- weakening ------------------------------------------------------------

wkThin : Thin A B → (w : Wk Δ Γ) → Thin (wkTy A w) (wkTy B w)
⌊wk⌋ : (δ : Thin A B)(w : Wk Δ Γ) → ⌊ wkThin δ w ⌋ ≡ ⌊ δ ⌋

wkTy ε w = ε
wkTy (ext A x δ) w = ext (wkTy A w) (wkVar x w) (wkThin δ w)

wkThin tε w = tε
wkThin (t-k {δ = δ}{δ' = δ'} σ ex e) p =
  t-k (wkThin σ p) ex
      (≡→T (cong₂ _∘ᵦ_ (⌊wk⌋ δ p) (⌊wk⌋ σ p) ∙ ==-sound _ _ e ∙ sym (⌊wk⌋ δ' p)))
  where cong₂ : {X Y Z : Set}(f : X → Y → Z){a a' : X}{b b' : Y}
              → a ≡ a' → b ≡ b' → f a b ≡ f a' b'
        cong₂ f refl refl = refl
wkThin (t-d σ) w = t-d (wkThin σ w)

⌊wk⌋ tε w = refl
⌊wk⌋ (t-k σ ex e) p = cong (true ∷_) (⌊wk⌋ σ p)
⌊wk⌋ (t-d σ) w = cong (false ∷_) (⌊wk⌋ σ w)

wkThin-∘ : (δ : Thin B C)(σ : Thin A B)(w : Wk Δ Γ) → wkThin (δ ∘ σ) w ≡ wkThin δ w ∘ wkThin σ w
wkThin-∘ δ tε w = refl
wkThin-∘ δ (t-d σ) w = t-d-cong (wkThin-∘ δ σ w)
wkThin-∘ (t-d δ) (t-k σ ex e) p = t-d-cong (wkThin-∘ δ σ p)
wkThin-∘ (t-k δ ey q) (t-k σ ex e) p = t-k-cong (wkThin-∘ δ σ p)
