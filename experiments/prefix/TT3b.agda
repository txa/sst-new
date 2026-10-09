{-
Option 3, second attempt: plain mutual data types defined in order
(Con, Pre, then the clauses of _⊕_, then Ty and Thin), so ⊕ computes in the
constructor types. The data definitions are accepted (π (q ⊕ y) = q ⊕ π y
holds definitionally).

BLOCKED at composition: t-k δ e ∘ t-k σ e' needs
  (q ⊕ r) ⊕ y  =  q ⊕ (r ⊕ y)
definitionally, where y is a variable. Ways out: store the variable
equation in t-k (equations as data, as for δ ∘ σ ≡ δ'), or use a
representation of prefixes that composes strictly.
-}
module TT3b where
open import Agda.Builtin.Equality

data Con : Set
data Ty : Con → Set
data Pre : Con → Con → Set
data Thin : {Γ Δ : Con} → Pre Γ Δ → Ty Γ → Ty Δ → Set

variable Γ Δ Θ Ξ : Con

data Con where
    • : Con
    _▷_ : (Γ : Con) → Ty Γ → Con

data Pre where
    ι : Pre Γ Γ
    π : {A : Ty Δ} → Pre Γ (Δ ▷ A) → Pre Γ Δ

_⊕_ : Pre Γ Δ → Pre Δ Θ → Pre Γ Θ
q ⊕ ι = q
q ⊕ π r = π (q ⊕ r)

_∘_ : {q : Pre Γ Δ}{r : Pre Δ Θ}{A : Ty Γ}{B : Ty Δ}{C : Ty Θ}
    → Thin r B C → Thin q A B → Thin (q ⊕ r) A C

data Ty where
    ε : Ty Γ
    ext : {B : Ty Δ}(A : Ty Γ)(x : Pre Γ (Δ ▷ B)) → Thin (π x) A B → Ty Γ

data Thin where
    tε : {q : Pre Γ Δ} → Thin q ε ε
    t-d : {q : Pre Γ Δ}{A : Ty Γ}{B : Ty Δ}{C : Ty Θ}{x : Pre Γ (Θ ▷ C)}{δ : Thin (π x) A C}
        → Thin q A B → Thin q (ext A x δ) B
    t-k : {q : Pre Γ Δ}{A : Ty Γ}{B : Ty Δ}{C : Ty Θ}{y : Pre Δ (Θ ▷ C)}
          {δ : Thin (π y) B C}{δ' : Thin (π (q ⊕ y)) A C}
        → (σ : Thin q A B) → δ ∘ σ ≡ δ' → Thin q (ext A (q ⊕ y) δ') (ext B y δ)

tε ∘ tε = tε
δ ∘ t-d σ = t-d (δ ∘ σ)
t-d δ ∘ t-k σ e = t-d (δ ∘ σ)
t-k δ e ∘ t-k σ e' = t-k (δ ∘ σ) {!!}
