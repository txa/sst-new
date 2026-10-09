{-# OPTIONS --rewriting #-}
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

variable A B C : Ty Γ

Var : (Γ : Con) → Ty Γ → Set
Var Γ A = El (var Γ A)

Wk : Con → Con → Set
Wk Γ Δ = El (wk Γ Δ) 

Thin : {Γ : Con} → Ty Γ → Ty Γ → Set
Thin A B = El (thin A B)

wkTy : Ty Γ → Wk Δ Γ → Ty Δ
wkVar : Var Γ A → (w : Wk Δ Γ) → Var Δ (wkTy A w)

variable x y z : Var Γ A

wkThin : Thin A B → (w : Wk Δ Γ) → Thin (wkTy A w) (wkTy B w)

_∘_ : Thin A C → Thin B A → Thin B C


id : Thin A A -- do I need this?
id = {!   !}

variable δ σ : Thin A B

data El where
    • : Con
    _▷_ : (Γ : Con) → Ty Γ → Con

    ε : Ty Γ 
    ext : (A : Ty Γ) → Var Γ B → Thin A B → Ty Γ

    idw : Wk Γ Γ
    extw : Wk Γ Δ → Wk (Γ ▷ A) Δ
    -- a type is a sequence of declaration of the form Xi x₀ .. xₙ
    -- here we represent x₀ .. xn as a thinning
    zero : Var (Γ ▷ A) (wkTy A (extw idw))
    suc : Var Γ A → Var (Γ ▷ B) (wkTy A (extw idw))

    tε : Thin (ε {Γ = Γ}) ε
    t-k : (σ : Thin A B) → Thin (ext A x (δ ∘ σ)) (ext B x δ)
    t-d : (σ : Thin A B) → Thin (ext A x δ) B


wkTy ε w = ε
wkTy (ext A x δ) w = ext (wkTy A w) (wkVar x w) (wkThin δ w)

wkTy-id : (A : Ty Γ) → wkTy A idw ≡ A
wkTy-id = {!   !}




wkVar {A = A} x idw rewrite wkTy-id A = x 
wkVar x (extw w) = {! suc (wkVar x w) !} -- suc (wkVar x w)
-- Goal 
-- Var (Γ ▷ A) (wkTy A₁ (extw w))
-- Have
-- El (var (Γ ▷ _B_246) (wkTy (wkTy A₁ w) (extw idw)))


wkThin = {!   !}
-- -- wkThin tε w = tε
-- -- wkThin (t-k σ) w = t-k (wkThin σ w)
-- wkThin-id : (δ : Thin A B) → wkThin δ idw ≡ δ


-- wkTy-id : (A : Ty Γ) → wkTy A idw ≡ A
-- wkTy-id = ?
-- -- wkTy-id ε = refl
-- --- wkThin (t-d σ) w = t-d (wkThin σ w)

-- - wkTy-id (ext {B = B} A x δ) rewrite wkTy-id A | wkTy-id B | wkThin-id δ = refl

-- wkVar-id : (x : Var Γ A) → wkVar x idw ≡ x
-- wkVar-id = ?
-- -- wkVar-id x = refl

-- wkThin-id = ?
-- -- wkThin-id tε = refl
-- -- wkThin-id (t-k σ) rewrite wkThin-id σ = refl
-- -- wkThin-id (t-d σ) rewrite wkThin-id σ = refl

w ∘ v = {! w  !}

-- {-# REWRITE wkTy-id #-}
-- {-# REWRITE wkVar-id #-}
-- {-# REWRITE wkThin-id #-}

