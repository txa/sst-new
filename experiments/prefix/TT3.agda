{-
Option 3 experiment: variables point to a prefix of the context, so the
type of a variable is never weakened; thinnings go along a prefix.

STATUS: paused, does not check. The current error (π (q ⊕ y) vs q ⊕ π y)
only appears because the clauses of _⊕_ come after the data definition.
The open question is the next step: composition of thinnings has index
q ⊕ (r ⊕ s) vs (q ⊕ r) ⊕ s, so it needs ⊕ to be associative by
definition, which fails for an inductive Pre when the last argument is a
variable. Making Pre strictly associative with functions (Yoneda style)
would put El in a negative position inside the syntax.
-}
module TT3 where
open import Agda.Builtin.Equality

data U : Set
data El : U → Set

data U where
    con : U
    ty : El con → U
    pre : El con → El con → U
    thin : {Γ Δ : El con} → El (pre Γ Δ) → El (ty Γ) → El (ty Δ) → U

Con = El con
Ty : Con → Set
Ty Γ = El (ty Γ)
Pre : Con → Con → Set           -- Pre Γ Δ : Δ is a prefix of Γ
Pre Γ Δ = El (pre Γ Δ)
Thin : {Γ Δ : Con} → Pre Γ Δ → Ty Γ → Ty Δ → Set
Thin q A B = El (thin q A B)

variable Γ Δ Θ Ξ : Con

-- composition of prefixes, by recursion on the second argument
_⊕_ : Pre Γ Δ → Pre Δ Θ → Pre Γ Θ
_∘_ : {q : Pre Γ Δ}{r : Pre Δ Θ}{A : Ty Γ}{B : Ty Δ}{C : Ty Θ}
    → Thin r B C → Thin q A B → Thin (q ⊕ r) A C

data El where
    • : Con
    _▷_ : (Γ : Con) → Ty Γ → Con

    ι : Pre Γ Γ
    π : {A : Ty Δ} → Pre Γ (Δ ▷ A) → Pre Γ Δ

    ε : Ty Γ
    -- a variable is a prefix ending in its declaration: x : Pre Γ (Δ ▷ B)
    ext : {B : Ty Δ}(A : Ty Γ)(x : Pre Γ (Δ ▷ B)) → Thin (π x) A B → Ty Γ

    tε : {q : Pre Γ Δ} → Thin q ε ε
    t-d : {q : Pre Γ Δ}{A : Ty Γ}{B : Ty Δ}{C : Ty Θ}{x : Pre Γ (Θ ▷ C)}{δ : Thin (π x) A C}
        → Thin q A B → Thin q (ext A x δ) B
    t-k : {q : Pre Γ Δ}{A : Ty Γ}{B : Ty Δ}{C : Ty Θ}{y : Pre Δ (Θ ▷ C)}
          {δ : Thin (π y) B C}{δ' : Thin (π (q ⊕ y)) A C}
        → (σ : Thin q A B) → δ ∘ σ ≡ δ' → Thin q (ext A (q ⊕ y) δ') (ext B y δ)

q ⊕ ι = q
q ⊕ π r = π (q ⊕ r)

δ ∘ tε = {!!}
δ ∘ t-d σ = t-d (δ ∘ σ)
t-d δ ∘ t-k σ e = t-d (δ ∘ σ)
t-k δ e ∘ t-k σ e' = t-k (δ ∘ σ) {!!}
