{-# OPTIONS --without-K #-}
{-
TT without K, without Prop, without Bool or untyped representations.

The commuting square of a kept assumption is stored as a typed *code*
  Code (δ ∘ σ) δ'
(the encode-decode characterisation of equality of thinnings), defined by
recursion into ⊤ / ⊥. Codes are propositions by induction (Code-prop), so
the stored proofs are unique without K and without Hedberg.

t-k has separate source and target variables x, y related by CodeV x y,
so no index is repeated and pattern matching works without K.
-}
module TT where

open import Agda.Builtin.Equality
open import Agda.Builtin.Unit
open import Agda.Builtin.Sigma

data ⊥ : Set where

sym : {X : Set}{a b : X} → a ≡ b → b ≡ a
sym refl = refl

cong : {X Y : Set}(f : X → Y){a b : X} → a ≡ b → f a ≡ f b
cong f refl = refl

infixr 5 _∙_
_∙_ : {X : Set}{a b c : X} → a ≡ b → b ≡ c → a ≡ c
refl ∙ q = q

subst : {X : Set}(P : X → Set){a b : X} → a ≡ b → P a → P b
subst P refl y = y

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

variable A A' A'' B B' C C' C'' D D' D'' : Ty Γ

Var : (Γ : Con) → Ty Γ → Set
Var Γ A = El (var Γ A)

Wk : Con → Con → Set
Wk Γ Δ = El (wk Γ Δ)

Thin : {Γ : Con} → Ty Γ → Ty Γ → Set
Thin A B = El (thin A B)

wkTy : Ty Γ → Wk Δ Γ → Ty Δ
_∘_ : Thin B C → Thin A B → Thin A C

-- codes for equality (heterogeneous in the indices)
CodeV : Var Γ C → Var Γ C' → Set
Code : Thin A C → Thin A' C' → Set

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
          (σ : Thin A B) → CodeV x y → Code (δ ∘ σ) δ'
        → Thin (ext A x δ') (ext B y δ)
    t-d : {x : Var Γ C}{δ : Thin A C}(σ : Thin A B) → Thin (ext A x δ) B

CodeV zero zero = ⊤
CodeV (suc x) (suc y) = CodeV x y
CodeV _ _ = ⊥

Code tε tε = ⊤
Code (t-d σ) (t-d τ) = Code σ τ
Code (t-k σ _ _) (t-k τ _ _) = Code σ τ
Code _ _ = ⊥

-- codes are propositions -------------------------------------------------

CodeV-prop : (x : Var Γ C)(y : Var Γ C')(u v : CodeV x y) → u ≡ v
CodeV-prop zero zero u v = refl
CodeV-prop (suc x) (suc y) u v = CodeV-prop x y u v
CodeV-prop zero (suc y) () v
CodeV-prop (suc x) zero () v

Code-prop : (σ : Thin A C)(τ : Thin A' C')(u v : Code σ τ) → u ≡ v
Code-prop tε tε u v = refl
Code-prop (t-d σ) (t-d τ) u v = Code-prop σ τ u v
Code-prop (t-k σ _ _) (t-k τ _ _) u v = Code-prop σ τ u v
Code-prop tε (t-k τ _ _) () v
Code-prop tε (t-d τ) () v
Code-prop (t-k σ _ _) tε () v
Code-prop (t-k σ _ _) (t-d τ) () v
Code-prop (t-d σ) tε () v
Code-prop (t-d σ) (t-k τ _ _) () v

-- codes are reflexive and transitive ------------------------------------

CodeV-refl : (x : Var Γ C) → CodeV x x
CodeV-refl zero = tt
CodeV-refl (suc x) = CodeV-refl x

CodeV-trans : (x : Var Γ C)(y : Var Γ C')(z : Var Γ D) → CodeV x y → CodeV y z → CodeV x z
CodeV-trans zero zero zero u v = tt
CodeV-trans (suc x) (suc y) (suc z) u v = CodeV-trans x y z u v
CodeV-trans zero (suc y) z () v
CodeV-trans (suc x) zero z () v
CodeV-trans zero zero (suc z) u ()
CodeV-trans (suc x) (suc y) zero u ()

Code-refl : (σ : Thin A C) → Code σ σ
Code-refl tε = tt
Code-refl (t-d σ) = Code-refl σ
Code-refl (t-k σ _ _) = Code-refl σ

Code-trans : (σ : Thin A C)(τ : Thin A' C')(ρ : Thin A'' C'') → Code σ τ → Code τ ρ → Code σ ρ
Code-trans tε tε tε u v = tt
Code-trans (t-d σ) (t-d τ) (t-d ρ) u v = Code-trans σ τ ρ u v
Code-trans (t-k σ _ _) (t-k τ _ _) (t-k ρ _ _) u v = Code-trans σ τ ρ u v
Code-trans tε (t-k τ _ _) ρ () v
Code-trans tε (t-d τ) ρ () v
Code-trans (t-k σ _ _) tε ρ () v
Code-trans (t-k σ _ _) (t-d τ) ρ () v
Code-trans (t-d σ) tε ρ () v
Code-trans (t-d σ) (t-k τ _ _) ρ () v
Code-trans tε tε (t-k ρ _ _) u ()
Code-trans tε tε (t-d ρ) u ()
Code-trans (t-k σ _ _) (t-k τ _ _) tε u ()
Code-trans (t-k σ _ _) (t-k τ _ _) (t-d ρ) u ()
Code-trans (t-d σ) (t-d τ) tε u ()
Code-trans (t-d σ) (t-d τ) (t-k ρ _ _) u ()

≡→Code : {σ τ : Thin A C} → σ ≡ τ → Code σ τ
≡→Code {σ = σ} refl = Code-refl σ

-- composition ----------------------------------------------------------

-- composition respects codes on the left
Code-∘ : (δ : Thin B C)(δ₂ : Thin B C')(σ : Thin A B) → Code δ δ₂ → Code (δ ∘ σ) (δ₂ ∘ σ)
-- associativity, as a code
Code-assoc : (ρ : Thin C D)(δ : Thin B C)(σ : Thin A B) → Code (ρ ∘ (δ ∘ σ)) ((ρ ∘ δ) ∘ σ)

-- the stored code of a composite of two keeps
k-code : (δC : Thin C D)(δB : Thin B D')(δA : Thin A D'')(δ : Thin B C)(σ : Thin A B)
       → Code (δC ∘ δ) δB → Code (δB ∘ σ) δA → Code (δC ∘ (δ ∘ σ)) δA
k-code δC δB δA δ σ q e =
  Code-trans (δC ∘ (δ ∘ σ)) ((δC ∘ δ) ∘ σ) δA (Code-assoc δC δ σ)
    (Code-trans ((δC ∘ δ) ∘ σ) (δB ∘ σ) δA (Code-∘ (δC ∘ δ) δB σ q) e)

δ ∘ tε = δ
δ ∘ t-d σ = t-d (δ ∘ σ)
t-d δ ∘ t-k σ ex e = t-d (δ ∘ σ)
t-k {x = y}{y = z}{δ = δC}{δ' = δB} δ ey q ∘ t-k {x = x}{δ' = δA} σ ex e =
  t-k (δ ∘ σ) (CodeV-trans x y z ex ey) (k-code δC δB δA δ σ q e)

Code-∘ δ δ₂ tε c = c
Code-∘ δ δ₂ (t-d σ) c = Code-∘ δ δ₂ σ c
Code-∘ (t-d δ) (t-d δ₂) (t-k σ _ _) c = Code-∘ δ δ₂ σ c
Code-∘ (t-k δ _ _) (t-k δ₂ _ _) (t-k σ _ _) c = Code-∘ δ δ₂ σ c
Code-∘ (t-d δ) (t-k δ₂ _ _) (t-k σ _ _) ()
Code-∘ (t-k δ _ _) (t-d δ₂) (t-k σ _ _) ()

Code-assoc ρ δ tε = Code-refl (ρ ∘ δ)
Code-assoc ρ δ (t-d σ) = Code-assoc ρ δ σ
Code-assoc ρ (t-d δ) (t-k σ _ _) = Code-assoc ρ δ σ
Code-assoc (t-d ρ) (t-k δ _ _) (t-k σ _ _) = Code-assoc ρ δ σ
Code-assoc (t-k ρ _ _) (t-k δ _ _) (t-k σ _ _) = Code-assoc ρ δ σ

-- laws as equations ----------------------------------------------------

variable δ σ ρ : Thin A B

t-d-cong : {x : Var Γ C}{δ : Thin A C}{σ σ' : Thin A B} → σ ≡ σ' → t-d {x = x}{δ = δ} σ ≡ t-d σ'
t-d-cong refl = refl

-- no K: the stored proofs are unique because codes are propositions
t-k-cong : {x : Var Γ C}{y : Var Γ C'}{δ : Thin B C'}{δ' : Thin A C}{σ σ' : Thin A B}
           {ex ex' : CodeV x y}{e : Code (δ ∘ σ) δ'}{e' : Code (δ ∘ σ') δ'}
         → σ ≡ σ' → t-k {x = x}{y = y}{δ = δ}{δ' = δ'} σ ex e ≡ t-k σ' ex' e'
t-k-cong {x = x}{y}{δ}{δ'}{σ}{ex = ex}{ex'}{e}{e'} refl =
  helper (CodeV-prop x y ex ex') (Code-prop (δ ∘ σ) δ' e e')
  where helper : ex ≡ ex' → e ≡ e' → t-k σ ex e ≡ t-k σ ex' e'
        helper refl refl = refl

∘-assoc : (ρ : Thin C D)(δ : Thin B C)(σ : Thin A B) → ρ ∘ (δ ∘ σ) ≡ (ρ ∘ δ) ∘ σ
∘-assoc ρ δ tε = refl
∘-assoc ρ δ (t-d σ) = t-d-cong (∘-assoc ρ δ σ)
∘-assoc ρ (t-d δ) (t-k σ ex e) = t-d-cong (∘-assoc ρ δ σ)
∘-assoc (t-d ρ) (t-k δ ey q) (t-k σ ex e) = t-d-cong (∘-assoc ρ δ σ)
∘-assoc (t-k ρ ez r) (t-k δ ey q) (t-k σ ex e) = t-k-cong (∘-assoc ρ δ σ)

-- identity -------------------------------------------------------------

id : Thin A A
id-code : (δ : Thin A C) → Code (δ ∘ id {A = A}) δ

id {A = ε} = tε
id {A = ext A x δ} = t-k id (CodeV-refl x) (id-code δ)

id-code tε = tt
id-code (t-d δ) = id-code δ
id-code (t-k δ _ _) = id-code δ

∘-id : (δ : Thin A B) → δ ∘ id ≡ δ
∘-id tε = refl
∘-id (t-k δ ex e) = t-k-cong (∘-id δ)
∘-id (t-d δ) = t-d-cong (∘-id δ)

id-∘ : (δ : Thin A B) → id ∘ δ ≡ δ
id-∘ tε = refl
id-∘ (t-d δ) = t-d-cong (id-∘ δ)
id-∘ (t-k δ ex e) = t-k-cong (id-∘ δ)

-- weakening ------------------------------------------------------------

wkVar : Var Γ A → (w : Wk Δ Γ) → Var Δ (wkTy A w)
wkVar x p = suc x

wkThin : Thin A B → (w : Wk Δ Γ) → Thin (wkTy A w) (wkTy B w)
-- weakening preserves codes, and commutes with composition up to codes
Code-wk : (σ : Thin A C)(τ : Thin A' C')(w : Wk Δ Γ) → Code σ τ → Code (wkThin σ w) (wkThin τ w)
Code-wk∘ : (δ : Thin B C)(σ : Thin A B)(w : Wk Δ Γ) → Code (wkThin δ w ∘ wkThin σ w) (wkThin (δ ∘ σ) w)

wkTy ε w = ε
wkTy (ext A x δ) w = ext (wkTy A w) (wkVar x w) (wkThin δ w)

wkThin tε w = tε
wkThin (t-k {δ = δ}{δ' = δ'} σ ex e) p =
  t-k (wkThin σ p) ex
      (Code-trans (wkThin δ p ∘ wkThin σ p) (wkThin (δ ∘ σ) p) (wkThin δ' p)
                  (Code-wk∘ δ σ p) (Code-wk (δ ∘ σ) δ' p e))
wkThin (t-d σ) w = t-d (wkThin σ w)

Code-wk tε tε w c = tt
Code-wk (t-d σ) (t-d τ) w c = Code-wk σ τ w c
Code-wk (t-k σ _ _) (t-k τ _ _) p c = Code-wk σ τ p c

Code-wk∘ δ tε w = Code-refl (wkThin δ w)
Code-wk∘ δ (t-d σ) w = Code-wk∘ δ σ w
Code-wk∘ (t-d δ) (t-k σ _ _) p = Code-wk∘ δ σ p
Code-wk∘ (t-k δ _ _) (t-k σ _ _) p = Code-wk∘ δ σ p

wkThin-∘ : (δ : Thin B C)(σ : Thin A B)(w : Wk Δ Γ) → wkThin (δ ∘ σ) w ≡ wkThin δ w ∘ wkThin σ w
wkThin-∘ δ tε w = refl
wkThin-∘ δ (t-d σ) w = t-d-cong (wkThin-∘ δ σ w)
wkThin-∘ (t-d δ) (t-k σ ex e) p = t-d-cong (wkThin-∘ δ σ p)
wkThin-∘ (t-k δ ey q) (t-k σ ex e) p = t-k-cong (wkThin-∘ δ σ p)

-- soundness of codes (needed for the interpretation, still without K) ----

VarΣ : Con → Set
VarΣ Γ = Σ (Ty Γ) (Var Γ)

sucΣ : {B : Ty Γ} → VarΣ Γ → VarΣ (Γ ▷ B)
sucΣ (C , x) = wkTy C p , suc x

-- decode: a code for variables gives a path in the total space
CodeV-sound : (x : Var Γ C)(y : Var Γ C') → CodeV x y → _≡_ {A = VarΣ Γ} (C , x) (C' , y)
CodeV-sound zero zero c = refl
CodeV-sound (suc x) (suc y) c = cong sucΣ (CodeV-sound x y c)
CodeV-sound zero (suc y) ()
CodeV-sound (suc x) zero ()

-- encode
CodeV-complete : {x : Var Γ C}{y : Var Γ C'} → _≡_ {A = VarΣ Γ} (C , x) (C' , y) → CodeV x y
CodeV-complete {x = x} refl = CodeV-refl x

decode-refl : (x : Var Γ C) → CodeV-sound x x (CodeV-refl x) ≡ refl
decode-refl zero = refl
decode-refl (suc x) = cong (cong sucΣ) (decode-refl x)

decode-encode : {x : Var Γ C}{y : Var Γ C'}(q : _≡_ {A = VarΣ Γ} (C , x) (C' , y))
              → CodeV-sound x y (CodeV-complete q) ≡ q
decode-encode {x = x} refl = decode-refl x

-- the total space of variables is a set (encode-decode, no K)
VarΣ-set : {x : Var Γ C}{y : Var Γ C'}(q q' : _≡_ {A = VarΣ Γ} (C , x) (C' , y)) → q ≡ q'
VarΣ-set {x = x}{y} q q' =
  sym (decode-encode q)
  ∙ cong (CodeV-sound x y) (CodeV-prop x y (CodeV-complete q) (CodeV-complete q'))
  ∙ decode-encode q'

-- a code between thinnings of the same type gives an equation
Code-sound : (σ τ : Thin A C) → Code σ τ → σ ≡ τ
Code-sound tε tε c = refl
Code-sound (t-d σ) (t-d τ) c = t-d-cong (Code-sound σ τ c)
Code-sound (t-k σ _ _) (t-k τ _ _) c = t-k-cong (Code-sound σ τ c)
Code-sound (t-d σ) (t-k τ _ _) ()
Code-sound (t-k σ _ _) (t-d τ) ()
