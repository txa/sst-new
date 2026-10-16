{-# OPTIONS --cubical -W noUnsupportedIndexedMatch #-}
{-
The forded HIIT with contexts, variables and one-step weakening.

* composition and weakening are constructors; their computation rules are
  path constructors;
* indices never contain composition: t-k stores a path, and zero and suc
  store a path  wk B A ≡ C  instead of being indexed by  wk B A;
* the keep-keep rule and the weakening rule for a keep are conditional:
  they hold for every stored path on the right. There is no ass and no
  rule for weakening a composite.
* the weakening of an extension (wkext, and with it wkt-d and wkt-k) is
  conditional on a loop  p : wk E B ≡ wk E B  stored in the weakened
  variable  suc x p. With refl there, the cube for wkext needs a 2-cell
  in the HIIT; with an arbitrary loop the boxes can always be filled.

Result: Con, Ty, Var and Thin are sets (end of file), via
  nf : HIIT → normal forms (NF2.agda),  q : normal forms → HIIT,
  h : q ∘ nf ~ id  (by HIIT induction),
so the total spaces are retracts of sets.

Engineering notes: the cubes for wkext/wkt-d/wkt-k are separate functions
whose boundaries are fixed by SquareP types (they need the clauses of hV
and h, which hT precedes); local abbreviations are let- not where-bound;
and the NF2 soundness lemmas and the code paths are opaque — otherwise
conversion checking unfolds them and runs out of memory.
-}
module FHIIT2 where

open import Cubical.Foundations.Prelude hiding (_▷_)
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
import NF2 as N

infixl 5 _▷_
infixr 9 _∘_

-- All sorts are one family El : U → Type, so that every constructor can
-- refer to the constructors declared before it (wkext mentions suc and
-- wkThin), which separate data types in a mutual block do not allow.

data U : Type
data El : U → Type

data U where
  con  : U
  ty   : El con → U
  var  : (Γ : El con) → El (ty Γ) → U
  thin : {Γ : El con} → El (ty Γ) → El (ty Γ) → U

Con : Type
Con = El con

Ty : Con → Type
Ty Γ = El (ty Γ)

Var : (Γ : Con) → Ty Γ → Type
Var Γ A = El (var Γ A)

Thin : {Γ : Con} → Ty Γ → Ty Γ → Type
Thin A B = El (thin A B)

data El where
  •   : Con
  _▷_ : (Γ : Con) → Ty Γ → Con

  ε   : {Γ : Con} → Ty Γ
  ext : {Γ : Con}(A : Ty Γ){B : Ty Γ} → Var Γ B → Thin A B → Ty Γ
  wk  : {Γ : Con}(E : Ty Γ) → Ty Γ → Ty (Γ ▷ E)

  zero : {Γ : Con}{A : Ty Γ}{C : Ty (Γ ▷ A)} → wk A A ≡ C → Var (Γ ▷ A) C
  suc  : {Γ : Con}{A B : Ty Γ}{C : Ty (Γ ▷ B)} → Var Γ A → wk B A ≡ C → Var (Γ ▷ B) C

  _∘_ : {Γ : Con}{A B C : Ty Γ} → Thin B C → Thin A B → Thin A C
  tε  : {Γ : Con} → Thin {Γ} ε ε
  t-d : {Γ : Con}{A B C : Ty Γ}{x : Var Γ C}{δ : Thin A C} → Thin A B → Thin (ext A x δ) B
  t-k : {Γ : Con}{A B C : Ty Γ}{x : Var Γ C}{δ : Thin B C}{δ' : Thin A C}
      → (σ : Thin A B) → δ ∘ σ ≡ δ' → Thin (ext A x δ') (ext B x δ)
  wkThin : {Γ : Con}(E : Ty Γ){A A' : Ty Γ} → Thin A A' → Thin (wk E A) (wk E A')

  -- weakening of types
  wkε   : {Γ : Con}{E : Ty Γ} → wk E ε ≡ ε
  -- conditional: for every loop p stored in the weakened variable
  wkext : {Γ : Con}{E A B : Ty Γ}{x : Var Γ B}{δ : Thin A B}
        → (p : wk E B ≡ wk E B) → wk E (ext A x δ) ≡ ext (wk E A) (suc x p) (wkThin E δ)

  -- composition
  ∘tε : {Γ : Con}{C : Ty Γ}{δ : Thin ε C} → δ ∘ tε ≡ δ
  ∘t-d : {Γ : Con}{A B C D : Ty Γ}{x : Var Γ D}{γ : Thin A D}{δ : Thin B C}{σ : Thin A B}
       → δ ∘ t-d {x = x} {δ = γ} σ ≡ t-d (δ ∘ σ)
  t-d∘t-k : {Γ : Con}{A B C D : Ty Γ}{x : Var Γ D}{δB : Thin B D}{δA : Thin A D}
            {δ : Thin B C}{σ : Thin A B}{e : δB ∘ σ ≡ δA}
          → t-d {x = x} {δ = δB} δ ∘ t-k σ e ≡ t-d (δ ∘ σ)
  t-k∘t-k : {Γ : Con}{A B C D : Ty Γ}{x : Var Γ D}{δC : Thin C D}{δB : Thin B D}{δA : Thin A D}
            {δ : Thin B C}{σ : Thin A B}{q : δC ∘ δ ≡ δB}{e : δB ∘ σ ≡ δA}
          → (r : δC ∘ (δ ∘ σ) ≡ δA)
          → t-k {x = x} δ q ∘ t-k σ e ≡ t-k (δ ∘ σ) r

  -- weakening of thinnings
  wktε : {Γ : Con}{E : Ty Γ} → PathP (λ i → Thin (wkε {E = E} i) (wkε i)) (wkThin E tε) tε
  wkt-d : {Γ : Con}{E A B C : Ty Γ}{x : Var Γ C}{δ : Thin A C}{σ : Thin A B}
        → (p : wk E C ≡ wk E C)
        → PathP (λ i → Thin (wkext {E = E} {x = x} {δ = δ} p i) (wk E B))
                (wkThin E (t-d σ)) (t-d (wkThin E σ))
  wkt-k : {Γ : Con}{E A B C : Ty Γ}{x : Var Γ C}{δ : Thin B C}{δ' : Thin A C}
          {σ : Thin A B}{e : δ ∘ σ ≡ δ'}
        → (p : wk E C ≡ wk E C)(e' : wkThin E δ ∘ wkThin E σ ≡ wkThin E δ')
        → PathP (λ i → Thin (wkext {E = E} {x = x} {δ = δ'} p i) (wkext {E = E} {x = x} {δ = δ} p i))
                (wkThin E (t-k σ e)) (t-k (wkThin E σ) e')

-- normalisation ---------------------------------------------------------------------

-- the code of a weakened variable: the reflexivity code computed by N.wkTy,
-- and the one obtained from the loop P stored by wkext
-- (opaque: only the endpoints matter, and they hold by the type)
opaque
  wkcode : {Γ : N.Con}(E B : N.Ty Γ)(P : N.wkTy E B ≡ N.wkTy E B)
         → PathP (λ _ → N.CodeTy (N.wkTy E B) (N.wkTy E B)) (N.CodeTy-refl (N.wkTy E B)) (N.≡→CodeTy P)
  wkcode E B P = isProp→PathP (λ _ → N.CodeTy-prop (N.wkTy E B) (N.wkTy E B))
                              (N.CodeTy-refl (N.wkTy E B)) (N.≡→CodeTy P)

-- the code of a weakened keep: the one computed by N.wkThin, and the one
-- obtained from the stored path e' of wkt-k
opaque
  wkkcode : {Γ : N.Con}(E : N.Ty Γ){A B C : N.Ty Γ}(δ : N.Thin B C)(δ' : N.Thin A C)(σ : N.Thin A B)
          → (c : N.Code (δ N.∘ σ) δ')(c' : N.Code (N.wkThin E δ N.∘ N.wkThin E σ) (N.wkThin E δ'))
          → PathP (λ _ → N.Code (N.wkThin E δ N.∘ N.wkThin E σ) (N.wkThin E δ'))
                  (N.Code-trans (N.wkThin E δ N.∘ N.wkThin E σ) (N.wkThin E (δ N.∘ σ)) (N.wkThin E δ')
                                (N.Code-wk∘ E δ σ) (N.Code-wk E E (δ N.∘ σ) δ' c))
                  c'
  wkkcode E δ δ' σ c c' =
    isProp→PathP (λ _ → N.Code-prop (N.wkThin E δ N.∘ N.wkThin E σ) (N.wkThin E δ'))
                 (N.Code-trans (N.wkThin E δ N.∘ N.wkThin E σ) (N.wkThin E (δ N.∘ σ)) (N.wkThin E δ')
                               (N.Code-wk∘ E δ σ) (N.Code-wk E E (δ N.∘ σ) δ' c))
                 c'

-- TERMINATING: structural, but the stored paths are constructor arguments
-- of path type, and Agda does not see nf (e i) as a structural call.
{-# TERMINATING #-}
nfC : Con → N.Con
{-# TERMINATING #-}
nfT : {Γ : Con} → Ty Γ → N.Ty (nfC Γ)
{-# TERMINATING #-}
nfV : {Γ : Con}{A : Ty Γ} → Var Γ A → N.Var (nfC Γ) (nfT A)
{-# TERMINATING #-}
nf  : {Γ : Con}{A B : Ty Γ} → Thin A B → N.Thin (nfT A) (nfT B)

nfC • = N.•
nfC (Γ ▷ A) = nfC Γ N.▷ nfT A

nfT ε = N.ε
nfT (ext A x δ) = N.ext (nfT A) (nfV x) (nf δ)
nfT (wk E A) = N.wkTy (nfT E) (nfT A)
nfT (wkε i) = N.ε
nfT (wkext {E = E} {A} {B} {x} {δ} p i) =
  N.ext (N.wkTy (nfT E) (nfT A)) (N.suc (nfV x) (wkcode (nfT E) (nfT B) (cong nfT p) i)) (N.wkThin (nfT E) (nf δ))

nfV (zero p) = N.zero (N.≡→CodeTy (cong nfT p))
nfV (suc x p) = N.suc (nfV x) (N.≡→CodeTy (cong nfT p))

nf (δ ∘ σ) = nf δ N.∘ nf σ
nf tε = N.tε
nf (t-d σ) = N.t-d (nf σ)
nf (t-k σ e) = N.t-k (nf σ) (N.≡→Code (cong nf e))
nf (wkThin E σ) = N.wkThin (nfT E) (nf σ)
nf (∘tε {δ = δ} i) = nf δ
nf (∘t-d {δ = δ} {σ = σ} i) = N.t-d (nf δ N.∘ nf σ)
nf (t-d∘t-k {δ = δ} {σ = σ} i) = N.t-d (nf δ N.∘ nf σ)
nf (t-k∘t-k {δC = δC} {δB} {δA} {δ} {σ} {q} {e} r i) =
  N.t-k-cong {σ = nf δ N.∘ nf σ}
    {e = N.k-code (nf δC) (nf δB) (nf δA) (nf δ) (nf σ) (N.≡→Code (cong nf q)) (N.≡→Code (cong nf e))}
    {e' = N.≡→Code (cong nf r)} refl i
nf (wktε i) = N.tε
nf (wkt-d {E = E} {A} {B} {C} {x} {δ} {σ} p i) =
  N.t-d {x = N.suc (nfV x) (wkcode (nfT E) (nfT C) (cong nfT p) i)} {δ = N.wkThin (nfT E) (nf δ)} (N.wkThin (nfT E) (nf σ))
nf (wkt-k {E = E} {A} {B} {C} {x} {δ} {δ'} {σ} {e} p e' i) =
  N.t-k {x = N.suc (nfV x) (wkcode (nfT E) (nfT C) (cong nfT p) i)} {δ = N.wkThin (nfT E) (nf δ)}
        {δ' = N.wkThin (nfT E) (nf δ')} (N.wkThin (nfT E) (nf σ))
        (wkkcode (nfT E) (nf δ) (nf δ') (nf σ) (N.≡→Code (cong nf e)) (N.≡→Code (cong nf e')) i)

-- quoting -----------------------------------------------------------------------------
-- TERMINATING: structural recursion on normal forms; Lw mentions q of
-- weakened normal forms in the faces of its compositions, which the
-- termination checker cannot relate to the arguments.

{-# TERMINATING #-}
qC : N.Con → Con
{-# TERMINATING #-}
qT : {Γ : N.Con} → N.Ty Γ → Ty (qC Γ)

qC N.• = •
qC (Γ N.▷ A) = qC Γ ▷ qT A

{-# TERMINATING #-}
qV : {Γ : N.Con}{A : N.Ty Γ} → N.Var Γ A → Var (qC Γ) (qT A)
{-# TERMINATING #-}
q  : {Γ : N.Con}{A B : N.Ty Γ} → N.Thin A B → Thin (qT A) (qT B)
-- quote commutes with composition
{-# TERMINATING #-}
L  : {Γ : N.Con}{A B C : N.Ty Γ}(δ : N.Thin B C)(σ : N.Thin A B) → q (δ N.∘ σ) ≡ q δ ∘ q σ
-- quote commutes with weakening
{-# TERMINATING #-}
LwT : {Γ : N.Con}(E A : N.Ty Γ) → qT (N.wkTy E A) ≡ wk (qT E) (qT A)
-- the stored path of a quoted weakened variable, and the loop it gives
Pc : {Γ : N.Con}(E B : N.Ty Γ) → N.CodeTy (N.wkTy E B) (N.wkTy E B) → wk (qT E) (qT B) ≡ qT (N.wkTy E B)
Pc E B c = sym (LwT E B) ∙ cong qT (N.CodeTy-sound (N.wkTy E B) (N.wkTy E B) c)
L₀ : {Γ : N.Con}(E B : N.Ty Γ) → wk (qT E) (qT B) ≡ wk (qT E) (qT B)
L₀ E B = Pc E B (N.CodeTy-refl (N.wkTy E B)) ∙ LwT E B
{-# TERMINATING #-}
Vpath : {Γ : N.Con}(E B : N.Ty Γ)(x : N.Var Γ B)(c : N.CodeTy (N.wkTy E B) (N.wkTy E B))
      → PathP (λ i → Var (qC Γ ▷ qT E) (LwT E B i))
              (qV (N.suc x c)) (suc (qV x) (Pc E B c ∙ LwT E B))
{-# TERMINATING #-}
Lw : {Γ : N.Con}(E : N.Ty Γ){A A' : N.Ty Γ}(σ : N.Thin A A')
   → PathP (λ i → Thin (LwT E A i) (LwT E A' i)) (q (N.wkThin E σ)) (wkThin (qT E) (q σ))

{-# TERMINATING #-}
LwdFill : {Γ : N.Con}(E : N.Ty Γ){A B C : N.Ty Γ}{x : N.Var Γ C}{γ : N.Thin A C}(σ : N.Thin A B)(i j : I)
        → Thin (compPath-filler (λ i → ext (LwT E A i) {LwT E C i} (Vpath E C x (N.CodeTy-refl (N.wkTy E C)) i) (Lw E γ i)) (sym (wkext {E = qT E} {x = qV x} {δ = q γ} (L₀ E C))) j i) (LwT E B i)
{-# TERMINATING #-}
LwkFill : {Γ : N.Con}(E : N.Ty Γ){A B C : N.Ty Γ}{x : N.Var Γ C}{δ : N.Thin B C}{δ' : N.Thin A C}(σ : N.Thin A B)
          (c : N.Code (δ N.∘ σ) δ')(i j : I)
        → Thin (compPath-filler (λ i → ext (LwT E A i) {LwT E C i} (Vpath E C x (N.CodeTy-refl (N.wkTy E C)) i) (Lw E δ' i)) (sym (wkext {E = qT E} {x = qV x} {δ = q δ'} (L₀ E C))) j i) (compPath-filler (λ i → ext (LwT E B i) {LwT E C i} (Vpath E C x (N.CodeTy-refl (N.wkTy E C)) i) (Lw E δ i)) (sym (wkext {E = qT E} {x = qV x} {δ = q δ} (L₀ E C))) j i)

-- move the thinning of a keep along a path, transporting its stored path
tk-move : {Γ : Con}{A B C : Ty Γ}{x : Var Γ C}{δ : Thin B C}{δ' : Thin A C}{s s' : Thin A B}
          (u : s ≡ s'){P : δ ∘ s ≡ δ'} → t-k {x = x} s P ≡ t-k s' (subst (λ y → δ ∘ y ≡ δ') u P)
tk-move {δ = δ} {δ'} u {P} i = t-k (u i) (subst-filler (λ y → δ ∘ y ≡ δ') u P i)

qT N.ε = ε
qT (N.ext A x δ) = ext (qT A) (qV x) (q δ)

qV (N.zero {A = A} {C} c) = zero (sym (LwT A A) ∙ cong qT (N.CodeTy-sound (N.wkTy A A) C c))
qV (N.suc {A = A} {B} {C} x c) = suc (qV x) (sym (LwT B A) ∙ cong qT (N.CodeTy-sound (N.wkTy B A) C c))

q N.tε = tε
q (N.t-d σ) = t-d (q σ)
q (N.t-k {δ = δ} {δ'} σ c) = t-k (q σ) (sym (L δ σ) ∙ cong q (N.Code-sound (δ N.∘ σ) δ' c))

L δ N.tε = sym ∘tε
L δ (N.t-d σ) = cong t-d (L δ σ) ∙ sym ∘t-d
L (N.t-d δ) (N.t-k σ c) = cong t-d (L δ σ) ∙ sym t-d∘t-k
L (N.t-k δ c₁) (N.t-k σ c₂) = tk-move (L δ σ) ∙ sym (t-k∘t-k _)

LwT E N.ε = sym wkε
LwT E (N.ext A {B} x δ) =
  (λ i → ext (LwT E A i) {LwT E B i} (Vpath E B x (N.CodeTy-refl (N.wkTy E B)) i) (Lw E δ i)) ∙ sym (wkext (L₀ E B))

Vpath E B x c i = suc (qV x) (compPath-filler (Pc E B c) (LwT E B) i)


-- the fillers of the weakening of a drop and of a keep; Lw is their lid
LwdFill E {A} {B} {C} {x} {γ} σ i j =
  fill (λ j → Thin (compPath-filler (λ i → ext (LwT E A i) {LwT E C i} (Vpath E C x (N.CodeTy-refl (N.wkTy E C)) i) (Lw E γ i)) (sym (wkext {E = qT E} {x = qV x} {δ = q γ} (L₀ E C))) j i) (LwT E B i))
       (λ j → λ { (i = i0) → q (N.wkThin E (N.t-d {x = x} {δ = γ} σ))
                ; (i = i1) → wkt-d {E = qT E} {x = qV x} {δ = q γ} {σ = q σ} (L₀ E C) (~ j) })
       (inS (t-d {x = Vpath E C x (N.CodeTy-refl (N.wkTy E C)) i} {δ = Lw E γ i} (Lw E σ i))) j
LwkFill E {A} {B} {C} {x} {δ} {δ'} σ c i j =
  fill (λ j → Thin (compPath-filler (λ i → ext (LwT E A i) {LwT E C i} (Vpath E C x (N.CodeTy-refl (N.wkTy E C)) i) (Lw E δ' i)) (sym (wkext {E = qT E} {x = qV x} {δ = q δ'} (L₀ E C))) j i)
                   (compPath-filler (λ i → ext (LwT E B i) {LwT E C i} (Vpath E C x (N.CodeTy-refl (N.wkTy E C)) i) (Lw E δ i)) (sym (wkext {E = qT E} {x = qV x} {δ = q δ} (L₀ E C))) j i))
       (λ j → λ { (i = i0) → q (N.wkThin E (N.t-k {x = x} {δ = δ} {δ' = δ'} σ c))
                ; (i = i1) → wkt-k {E = qT E} {x = qV x} {δ = q δ} {δ' = q δ'} {σ = q σ}
                                   {e = sym (L δ σ) ∙ cong q (N.Code-sound (δ N.∘ σ) δ' c)} (L₀ E C)
                                   (transport (λ t → Lw E δ t ∘ Lw E σ t ≡ Lw E δ' t) (sym (L (N.wkThin E δ) (N.wkThin E σ))
         ∙ cong q (N.Code-sound (N.wkThin E δ N.∘ N.wkThin E σ) (N.wkThin E δ')
                                (N.Code-trans (N.wkThin E δ N.∘ N.wkThin E σ) (N.wkThin E (δ N.∘ σ)) (N.wkThin E δ') (N.Code-wk∘ E δ σ) (N.Code-wk E E (δ N.∘ σ) δ' c))))) (~ j) })
       (inS (t-k {x = Vpath E C x (N.CodeTy-refl (N.wkTy E C)) i} {δ = Lw E δ i} {δ' = Lw E δ' i} (Lw E σ i)
                 (transport-filler (λ t → Lw E δ t ∘ Lw E σ t ≡ Lw E δ' t) (sym (L (N.wkThin E δ) (N.wkThin E σ))
         ∙ cong q (N.Code-sound (N.wkThin E δ N.∘ N.wkThin E σ) (N.wkThin E δ')
                                (N.Code-trans (N.wkThin E δ N.∘ N.wkThin E σ) (N.wkThin E (δ N.∘ σ)) (N.wkThin E δ') (N.Code-wk∘ E δ σ) (N.Code-wk E E (δ N.∘ σ) δ' c)))) i))) j

Lw E N.tε = symP wktε
Lw E (N.t-d {x = x} {γ} σ) i = LwdFill E {x = x} {γ = γ} σ i i1
Lw E (N.t-k {x = x} {δ} {δ'} σ c) i = LwkFill E {x = x} {δ = δ} {δ' = δ'} σ c i i1

-- quote ∘ nf is the identity -----------------------------------------------------------
-- TERMINATING: HIIT induction; the clauses for path constructors mention h
-- on the endpoints, which the eliminator provides.

{-# TERMINATING #-}
hC : (Γ : Con) → qC (nfC Γ) ≡ Γ
{-# TERMINATING #-}
hT : {Γ : Con}(A : Ty Γ) → PathP (λ i → Ty (hC Γ i)) (qT (nfT A)) A
{-# TERMINATING #-}
hV : {Γ : Con}{A : Ty Γ}(x : Var Γ A) → PathP (λ i → Var (hC Γ i) (hT A i)) (qV (nfV x)) x
{-# TERMINATING #-}
h  : {Γ : Con}{A B : Ty Γ}(σ : Thin A B) → PathP (λ i → Thin (hT A i) (hT B i)) (q (nf σ)) σ
{-# TERMINATING #-}
hk : {Γ : Con}{A B C : Ty Γ}{δ : Thin B C}{δ' : Thin A C}(σ : Thin A B)(e : δ ∘ σ ≡ δ')
   → PathP (λ i → h δ i ∘ h σ i ≡ h δ' i)
           (sym (L (nf δ) (nf σ)) ∙ cong q (N.Code-sound (nf δ N.∘ nf σ) (nf δ') (N.≡→Code (cong nf e)))) e

hC • = refl
hC (Γ ▷ A) i = hC Γ i ▷ hT A i


-- the stored path of a weakened variable
{-# TERMINATING #-}
hsucZ : {Γ : Con}{A B : Ty Γ}{C : Ty (Γ ▷ B)}(p : wk B A ≡ C)
      → PathP (λ i → wk (hT B i) (hT A i) ≡ hT C i)
              (sym (LwT (nfT B) (nfT A)) ∙ cong qT (N.CodeTy-sound (N.wkTy (nfT B) (nfT A)) (nfT C) (N.≡→CodeTy (cong nfT p)))) p
-- the square filling h (wkThin E σ)
{-# TERMINATING #-}
hwk : {Γ : Con}(E : Ty Γ){A A' : Ty Γ}(σ : Thin A A')(i j : I)
    → Thin (doubleWhiskFiller (LwT (nfT E) (nfT A)) (λ i → wk (hT E i) (hT A i)) refl j i)
           (doubleWhiskFiller (LwT (nfT E) (nfT A')) (λ i → wk (hT E i) (hT A' i)) refl j i)
-- the cube filling hT (wkε k)
{-# TERMINATING #-}
hTwkε : {Γ : Con}(E : Ty Γ)(k i j : I) → Ty (hC Γ i ▷ hT E i)
-- the pieces of the cube filling hT (wkext p k):
-- the stored path of the variable on the face k = 1,
{-# TERMINATING #-}
wkW : {Γ : Con}{E B : Ty Γ}(p : wk E B ≡ wk E B)(j i : I)
    → wk (hT E i) (hT B i) ≡ doubleWhiskFiller (LwT (nfT E) (nfT B)) (λ i → wk (hT E i) (hT B i)) refl j i
-- the loop given to wkext in the base,
{-# TERMINATING #-}
wkP : {Γ : Con}{E B : Ty Γ}(p : wk E B ≡ wk E B)(k i : I) → wk (hT E i) (hT B i) ≡ wk (hT E i) (hT B i)
-- the face i = 0 (a filler in m),
{-# TERMINATING #-}
wkF0 : {Γ : Con}{E A B : Ty Γ}{x : Var Γ B}{δ : Thin A B}(p : wk E B ≡ wk E B)(k j m : I)
     → Ty (qC (nfC Γ) ▷ qT (nfT E))
-- and the whole cube
{-# TERMINATING #-}
hTwkextFill : {Γ : Con}{E A B : Ty Γ}{x : Var Γ B}{δ : Thin A B}(p : wk E B ≡ wk E B)(k i j : I)
        → Ty (hC Γ i ▷ hT E i)


-- the squares for wkext, wkt-d and wkt-k, with their boundaries fixed by
-- the type, so that hT and h can use them before they are defined (their
-- definitions need the clauses of hV and h)
{-# TERMINATING #-}
hTwkext : {Γ : Con}{E A B : Ty Γ}{x : Var Γ B}{δ : Thin A B}(p : wk E B ≡ wk E B)
        → SquareP (λ k i → Ty (hC Γ i ▷ hT E i))
                  (hT (wk E (ext A x δ))) (hT (ext (wk E A) (suc x p) (wkThin E δ)))
                  (λ k → qT (nfT (wkext {E = E} {x = x} {δ = δ} p k))) (λ k → wkext {E = E} {x = x} {δ = δ} p k)
{-# TERMINATING #-}
hwktd : {Γ : Con}{E A B C : Ty Γ}{x : Var Γ C}{δ : Thin A C}{σ : Thin A B}(p : wk E C ≡ wk E C)
      → SquareP (λ k i → Thin (hT (wkext {E = E} {x = x} {δ = δ} p k) i) (hT (wk E B) i))
                (h (wkThin E (t-d {x = x} {δ = δ} σ))) (h (t-d {x = suc x p} {δ = wkThin E δ} (wkThin E σ)))
                (λ k → q (nf (wkt-d {E = E} {x = x} {δ = δ} {σ = σ} p k))) (λ k → wkt-d {E = E} {x = x} {δ = δ} {σ = σ} p k)
{-# TERMINATING #-}
hwktk : {Γ : Con}{E A B C : Ty Γ}{x : Var Γ C}{δ : Thin B C}{δ' : Thin A C}{σ : Thin A B}{e : δ ∘ σ ≡ δ'}
        (p : wk E C ≡ wk E C)(e' : wkThin E δ ∘ wkThin E σ ≡ wkThin E δ')
      → SquareP (λ k i → Thin (hT (wkext {E = E} {x = x} {δ = δ'} p k) i) (hT (wkext {E = E} {x = x} {δ = δ} p k) i))
                (h (wkThin E (t-k {x = x} {δ = δ} {δ' = δ'} σ e)))
                (h (t-k {x = suc x p} {δ = wkThin E δ} {δ' = wkThin E δ'} (wkThin E σ) e'))
                (λ k → q (nf (wkt-k {E = E} {x = x} {δ = δ} {δ' = δ'} {σ = σ} {e = e} p e' k)))
                (λ k → wkt-k {E = E} {x = x} {δ = δ} {δ' = δ'} {σ = σ} {e = e} p e' k)

hTwkε E k i j =
  hfill (λ j → λ { (k = i0) → doubleWhiskFiller (sym (wkε {E = qT (nfT E)})) (λ i → wk (hT E i) ε) refl j i
                 ; (k = i1) → ε
                 ; (i = i0) → wkε {E = qT (nfT E)} (k ∨ j)
                 ; (i = i1) → wkε {E = E} k })
        (inS (wkε {E = hT E i} k)) j


hwk E {A} {A'} σ i j =
  fill (λ j → Thin (doubleWhiskFiller (LwT (nfT E) (nfT A)) (λ i → wk (hT E i) (hT A i)) refl j i)
                   (doubleWhiskFiller (LwT (nfT E) (nfT A')) (λ i → wk (hT E i) (hT A' i)) refl j i))
       (λ j → λ { (i = i0) → Lw (nfT E) (nf σ) (~ j) ; (i = i1) → wkThin E σ })
       (inS (wkThin (hT E i) (h σ i))) j


hT ε i = ε
hT (ext A x δ) i = ext (hT A i) (hV x i) (h δ i)
hT (wk E A) = LwT (nfT E) (nfT A) ◁ (λ i → wk (hT E i) (hT A i))
hT (wkε {E = E} k) i = hTwkε E k i i1
hT (wkext {x = x} {δ = δ} p k) i = hTwkext {x = x} {δ = δ} p k i


hsucZ {A = A} {B = B} {C = C} p =
  subst (λ P → PathP (λ i → wk (hT B i) (hT A i) ≡ hT C i) (sym (LwT (nfT B) (nfT A)) ∙ cong qT P) p)
        (N.isSetTy (N.wkTy (nfT B) (nfT A)) (nfT C) (cong nfT p)
                   (N.CodeTy-sound (N.wkTy (nfT B) (nfT A)) (nfT C) (N.≡→CodeTy (cong nfT p)))) E
  where
    E : PathP (λ i → wk (hT B i) (hT A i) ≡ hT C i)
              (sym (LwT (nfT B) (nfT A)) ∙ cong (λ y → qT (nfT y)) p) p
    E i j = hcomp (λ k → λ { (j = i0) → doubleWhiskFiller (LwT (nfT B) (nfT A)) (λ i → wk (hT B i) (hT A i)) refl (~ k) i
                           ; (j = i1) → hT C i
                           ; (i = i0) → compPath-filler' (sym (LwT (nfT B) (nfT A))) (cong (λ y → qT (nfT y)) p) k j
                           ; (i = i1) → p j })
                  (hT (p j) i)


hV (zero {A = A} {C = C} p) i = zero {A = hT A i} {C = hT C i} (Z i)
  where
    Pq = sym (LwT (nfT A) (nfT A)) ∙ cong qT (N.CodeTy-sound (N.wkTy (nfT A) (nfT A)) (nfT C) (N.≡→CodeTy (cong nfT p)))
    E : PathP (λ i → wk (hT A i) (hT A i) ≡ hT C i)
              (sym (LwT (nfT A) (nfT A)) ∙ cong (λ y → qT (nfT y)) p) p
    E i j = hcomp (λ k → λ { (j = i0) → doubleWhiskFiller (LwT (nfT A) (nfT A)) (λ i → wk (hT A i) (hT A i)) refl (~ k) i
                           ; (j = i1) → hT C i
                           ; (i = i0) → compPath-filler' (sym (LwT (nfT A) (nfT A))) (cong (λ y → qT (nfT y)) p) k j
                           ; (i = i1) → p j })
                  (hT (p j) i)
    Z : PathP (λ i → wk (hT A i) (hT A i) ≡ hT C i) Pq p
    Z = subst (λ P → PathP (λ i → wk (hT A i) (hT A i) ≡ hT C i) (sym (LwT (nfT A) (nfT A)) ∙ cong qT P) p)
              (N.isSetTy (N.wkTy (nfT A) (nfT A)) (nfT C) (cong nfT p)
                         (N.CodeTy-sound (N.wkTy (nfT A) (nfT A)) (nfT C) (N.≡→CodeTy (cong nfT p)))) E
hV (suc {A = A} {B = B} {C = C} x p) i = suc {A = hT A i} {B = hT B i} {C = hT C i} (hV x i) (hsucZ {A = A} {B = B} {C = C} p i)


h (δ ∘ σ) = L (nf δ) (nf σ) ◁ (λ i → h δ i ∘ h σ i)
h tε i = tε
h (t-d {x = x} {δ = γ} σ) i = t-d {x = hV x i} {δ = h γ i} (h σ i)
h (t-k {x = x} σ e) i = t-k {x = hV x i} (h σ i) (hk σ e i)
h (wkThin E σ) i = hwk E σ i i1
h (∘tε {δ = δ} k) i =
  hcomp (λ j → λ { (k = i0) → doubleWhiskFiller (sym ∘tε) (λ i → h δ i ∘ tε) refl j i
                 ; (k = i1) → h δ i
                 ; (i = i0) → ∘tε {δ = q (nf δ)} (k ∨ j)
                 ; (i = i1) → ∘tε {δ = δ} k })
        (∘tε {δ = h δ i} k)
h (∘t-d {x = x} {γ = γ} {δ = δ} {σ = σ} k) i =
  hcomp (λ j → λ { (k = i0) → doubleWhiskFiller L₁ (λ i → h δ i ∘ t-d {x = hV x i} {δ = h γ i} (h σ i)) refl j i
                 ; (k = i1) → t-d {x = hV x i} {δ = h γ i} (doubleWhiskFiller L' (λ i → h δ i ∘ h σ i) refl j i)
                 ; (i = i0) → compPath-filler (cong (t-d {x = qV (nfV x)} {δ = q (nf γ)}) L') (sym ∘t-dq) (~ k) (~ j)
                 ; (i = i1) → ∘t-d {x = x} {γ = γ} {δ = δ} {σ = σ} k })
        (∘t-d {x = hV x i} {γ = h γ i} {δ = h δ i} {σ = h σ i} k)
  where L' = L (nf δ) (nf σ)
        ∘t-dq = ∘t-d {x = qV (nfV x)} {γ = q (nf γ)} {δ = q (nf δ)} {σ = q (nf σ)}
        L₁ = cong (t-d {x = qV (nfV x)} {δ = q (nf γ)}) L' ∙ sym ∘t-dq
h (t-d∘t-k {x = x} {δB = δB} {δA = δA} {δ = δ} {σ = σ} {e = e} k) i =
  hcomp (λ j → λ { (k = i0) → doubleWhiskFiller L₁ (λ i → t-d {x = hV x i} {δ = h δB i} (h δ i) ∘ t-k {x = hV x i} (h σ i) (hk σ e i)) refl j i
                 ; (k = i1) → t-d {x = hV x i} {δ = h δA i} (doubleWhiskFiller L' (λ i → h δ i ∘ h σ i) refl j i)
                 ; (i = i0) → compPath-filler (cong (t-d {x = qV (nfV x)} {δ = q (nf δA)}) L') (sym t-d∘t-kq) (~ k) (~ j)
                 ; (i = i1) → t-d∘t-k {x = x} {δ = δ} {σ = σ} {e = e} k })
        (t-d∘t-k {x = hV x i} {δB = h δB i} {δA = h δA i} {δ = h δ i} {σ = h σ i} {e = hk σ e i} k)
  where L' = L (nf δ) (nf σ)
        t-d∘t-kq = t-d∘t-k {x = qV (nfV x)} {δB = q (nf δB)} {δA = q (nf δA)} {δ = q (nf δ)} {σ = q (nf σ)}
                           {e = sym (L (nf δB) (nf σ)) ∙ cong q (N.Code-sound (nf δB N.∘ nf σ) (nf δA) (N.≡→Code (cong nf e)))}
        L₁ = cong (t-d {x = qV (nfV x)} {δ = q (nf δA)}) L' ∙ sym t-d∘t-kq
h (t-k∘t-k {Γ} {A} {B} {C} {D} {x} {δC} {δB} {δA} {δ} {σ} {q₁} {e} r k) i =
  hcomp (λ j → λ { (k = i0) → doubleWhiskFiller L₁ M refl j i
                 ; (k = i1) → t-k {x = hV x i} (W' j i) (Z j i)
                 ; (i = i0) → B₀ k j
                 ; (i = i1) → t-k∘t-k {x = x} {q = q₁} {e = e} r k })
        (t-k∘t-k {x = hV x i} {δC = h δC i} {δB = h δB i} {δA = h δA i} {δ = h δ i} {σ = h σ i}
                 {q = hk δ q₁ i} {e = hk σ e i} (Z i0 i) k)
  where
    s₀ = nf δ N.∘ nf σ
    L' = L (nf δ) (nf σ)
    L₁ = L (nf (t-k {x = x} δ q₁)) (nf (t-k {x = x} σ e))
    M : PathP (λ i → Thin (hT (ext A x δA) i) (hT (ext C x δC) i))
              (q (nf (t-k {x = x} δ q₁)) ∘ q (nf (t-k {x = x} σ e))) (t-k δ q₁ ∘ t-k σ e)
    M i = h (t-k {x = x} δ q₁) i ∘ h (t-k {x = x} σ e) i
    M' : PathP (λ i → Thin (hT A i) (hT C i)) (q (nf δ) ∘ q (nf σ)) (δ ∘ σ)
    M' i = h δ i ∘ h σ i
    W' = doubleWhiskFiller L' M' refl
    F  = λ y → q (nf δC) ∘ y ≡ q (nf δA)
    kc = N.k-code (nf δC) (nf δB) (nf δA) (nf δ) (nf σ) (N.≡→Code (cong nf q₁)) (N.≡→Code (cong nf e))
    cr = N.≡→Code (cong nf r)
    Pk : (k : I) → q (nf δC) ∘ q s₀ ≡ q (nf δA)
    Pk k = sym (L (nf δC) s₀)
           ∙ cong q (N.Code-sound (nf δC N.∘ s₀) (nf δA) (isProp→PathP (λ _ → N.Code-prop (nf δC N.∘ s₀) (nf δA)) kc cr k))
    ρ : (k : I) → F (q (nf δ) ∘ q (nf σ))
    ρ k = subst F L' (Pk k)
    tkq : (r' : F (q (nf δ) ∘ q (nf σ))) → _
    tkq r' = t-k∘t-k {x = qV (nfV x)} {δC = q (nf δC)} {δB = q (nf δB)} {δA = q (nf δA)} {δ = q (nf δ)} {σ = q (nf σ)}
                     {q = hk δ q₁ i0} {e = hk σ e i0} r'
    ζ : (j : I) → F (L' (~ j))
    ζ j = subst-filler F L' (Pk i1) (~ j)
    Z : (j i : I) → h δC i ∘ W' j i ≡ h δA i
    Z j i = fill (λ m → h δC i ∘ W' (~ m) i ≡ h δA i)
                 (λ m → λ { (i = i0) → ζ (~ m) ; (i = i1) → r })
                 (inS (hk (δ ∘ σ) r i)) (~ j)
    tkm : (k : I) → _
    tkm k = tk-move {x = qV (nfV x)} L' {Pk k}
    T : (k : I) → _
    T k = (λ m → tkq (ρ k) m) ∙ (λ m → tkm k (~ m))
    B₀ : (k j : I) → _
    B₀ k j = hcomp (λ m → λ { (k = i0) → symDistr (tkm i0) (sym (tkq (ρ i0))) (~ m) j
                            ; (k = i1) → compPath-filler' (tkq (ρ i1)) (sym (tkm i1)) (~ m) j
                            ; (j = i0) → tkq (ρ i1) (k ∧ m)
                            ; (j = i1) → t-k {x = qV (nfV x)} (q s₀) (Pk k) })
                   (T k j)
h (wktε {E = E} k) i =
  comp (λ j → Thin (hTwkε E k i j) (hTwkε E k i j))
       (λ j → λ { (k = i0) → hwk E tε i j
                ; (k = i1) → tε
                ; (i = i0) → wktε {E = qT (nfT E)} (k ∨ j)
                ; (i = i1) → wktε {E = E} k })
       (wktε {E = hT E i} k)
h (wkt-d {x = x} {δ = δ} {σ = σ} p k) i = hwktd {x = x} {δ = δ} {σ = σ} p k i
h (wkt-k {x = x} {δ = δ} {δ' = δ'} {σ = σ} {e = e} p e' k) i = hwktk {x = x} {δ = δ} {δ' = δ'} {σ = σ} {e = e} p e' k i

-- the outer hcomp only makes the endpoint i0 reduce without unfolding subst
hk {δ = δ} {δ'} σ e i =
  hcomp (λ j → λ { (i = i0) → sym (L (nf δ) (nf σ)) ∙ cong q (N.Code-sound (nf δ N.∘ nf σ) (nf δ') (N.≡→Code (cong nf e)))
                 ; (i = i1) → e })
  (subst (λ P → PathP (λ i → h δ i ∘ h σ i ≡ h δ' i) (sym (L (nf δ) (nf σ)) ∙ cong q P) e)
        (N.isSetThin (nf δ N.∘ nf σ) (nf δ') (cong nf e) (N.Code-sound (nf δ N.∘ nf σ) (nf δ') (N.≡→Code (cong nf e))))
        E i)
  where
    E : PathP (λ i → h δ i ∘ h σ i ≡ h δ' i) (sym (L (nf δ) (nf σ)) ∙ cong (λ y → q (nf y)) e) e
    E i j = hcomp (λ k → λ { (j = i0) → doubleWhiskFiller (L (nf δ) (nf σ)) (λ i → h δ i ∘ h σ i) refl (~ k) i
                           ; (j = i1) → h δ' i
                           ; (i = i0) → compPath-filler' (sym (L (nf δ) (nf σ))) (cong (λ y → q (nf y)) e) k j
                           ; (i = i1) → e j })
                  (h (e j) i)


wkW {E = E} {B = B} p j i =
  fill (λ t → wk (hT E i) (hT B i) ≡ doubleWhiskFiller (LwT (nfT E) (nfT B)) (λ i → wk (hT E i) (hT B i)) refl (~ t) i)
       (λ t → λ { (i = i0) → compPath-filler (Pc (nfT E) (nfT B) (N.≡→CodeTy (cong nfT p))) (LwT (nfT E) (nfT B)) t
                ; (i = i1) → p })
       (inS (hsucZ {A = B} {B = E} {C = wk E B} p i)) (~ j)

wkP {E = E} {B = B} p k i =
  hfill (λ t → λ { (i = i0) → Pc (nfT E) (nfT B) (wkcode (nfT E) (nfT B) (cong nfT p) (~ t)) ∙ LwT (nfT E) (nfT B)
                 ; (i = i1) → p })
        (inS (wkW {E = E} {B = B} p i0 i)) (~ k)

wkF0 {E = E} {A} {B} {x} {δ} p k j m =
  hfill (λ m → λ { (j = i0) → wkext {E = qT (nfT E)} {A = qT (nfT A)} {B = qT (nfT B)} {x = qV (nfV x)} {δ = q (nf δ)}
                                    (wkP {E = E} {B = B} p k i0) (k ∨ ~ m)
                 ; (j = i1) → qT (nfT (wkext {E = E} {A} {B} {x} {δ} p k))
                 ; (k = i1) → ext (LwT (nfT E) (nfT A) (~ j)) {LwT (nfT E) (nfT B) (~ j)}
                                  (suc (qV (nfV x)) (compPath-filler (Pc (nfT E) (nfT B) (N.≡→CodeTy (cong nfT p))) (LwT (nfT E) (nfT B)) (~ j)))
                                  (Lw (nfT E) (nf δ) (~ j))
                 ; (k = i0) → compPath-filler (λ i → ext (LwT (nfT E) (nfT A) i) {LwT (nfT E) (nfT B) i}
                                                         (Vpath (nfT E) (nfT B) (nfV x) (N.CodeTy-refl (N.wkTy (nfT E) (nfT B))) i)
                                                         (Lw (nfT E) (nf δ) i))
                                              (sym (wkext {E = qT (nfT E)} {x = qV (nfV x)} {δ = q (nf δ)} (L₀ (nfT E) (nfT B)))) m (~ j) })
        (inS (ext (LwT (nfT E) (nfT A) (~ j)) {LwT (nfT E) (nfT B) (~ j)} (Vpath (nfT E) (nfT B) (nfV x) (wkcode (nfT E) (nfT B) (cong nfT p) k) (~ j))
                  (Lw (nfT E) (nf δ) (~ j)))) m


hTwkextFill {Γ} {E} {A} {B} {x} {δ} p k i j =
  hfill (λ j → λ { (k = i0) → doubleWhiskFiller (LwT (nfT E) (nfT (ext A x δ))) (λ i → wk (hT E i) (hT (ext A x δ) i)) refl j i
                 ; (k = i1) → ext (doubleWhiskFiller (LwT (nfT E) (nfT A)) (λ i → wk (hT E i) (hT A i)) refl j i)
                                  {doubleWhiskFiller (LwT (nfT E) (nfT B)) (λ i → wk (hT E i) (hT B i)) refl j i}
                                  (suc (hV x i) (wkW {E = E} {B = B} p j i)) (hwk E δ i j)
                 ; (i = i0) → wkF0 {x = x} {δ = δ} p k j i1
                 ; (i = i1) → wkext {x = x} {δ = δ} p k })
        (inS (wkext {E = hT E i} {A = hT A i} {B = hT B i} {x = hV x i} {δ = h δ i} (wkP {E = E} {B = B} p k i) k)) j

hTwkext {x = x} {δ = δ} p k i = hTwkextFill {x = x} {δ = δ} p k i i1

hwktd {Γ} {E} {A} {B} {C} {x} {δ} {σ} p k i =
  let
    G0 : (j : I) → Thin (wkF0 {x = x} {δ = δ} p k j i1) (LwT (nfT E) (nfT B) (~ j))
    G0 j = comp (λ m → Thin (wkF0 {x = x} {δ = δ} p k j m) (LwT (nfT E) (nfT B) (~ j)))
                (λ m → λ { (j = i0) → wkt-d {E = qT (nfT E)} {x = qV (nfV x)} {δ = q (nf δ)} {σ = q (nf σ)}
                                            (wkP {E = E} {B = C} p k i0) (k ∨ ~ m)
                         ; (j = i1) → q (nf (wkt-d {E = E} {x = x} {δ = δ} {σ = σ} p k))
                         ; (k = i1) → t-d {x = suc (qV (nfV x)) (compPath-filler (Pc (nfT E) (nfT C) (N.≡→CodeTy (cong nfT p))) (LwT (nfT E) (nfT C)) (~ j))}
                                          {δ = Lw (nfT E) (nf δ) (~ j)} (Lw (nfT E) (nf σ) (~ j))
                         ; (k = i0) → LwdFill (nfT E) {x = nfV x} {γ = nf δ} (nf σ) (~ j) m })
                (t-d {x = Vpath (nfT E) (nfT C) (nfV x) (wkcode (nfT E) (nfT C) (cong nfT p) k) (~ j)} {δ = Lw (nfT E) (nf δ) (~ j)} (Lw (nfT E) (nf σ) (~ j)))
  in
  comp (λ j → Thin (hTwkextFill {x = x} {δ = δ} p k i j) (doubleWhiskFiller (LwT (nfT E) (nfT B)) (λ i → wk (hT E i) (hT B i)) refl j i))
       (λ j → λ { (k = i0) → hwk E (t-d {x = x} {δ = δ} σ) i j
                ; (k = i1) → t-d {x = suc (hV x i) (wkW {E = E} {B = C} p j i)} {δ = hwk E δ i j} (hwk E σ i j)
                ; (i = i0) → G0 j
                ; (i = i1) → wkt-d {x = x} {δ = δ} {σ = σ} p k })
       (wkt-d {E = hT E i} {A = hT A i} {B = hT B i} {C = hT C i} {x = hV x i} {δ = h δ i} {σ = h σ i}
              (wkP {E = E} {B = C} p k i) k)

hwktk {Γ} {E} {A} {B} {C} {x} {δ} {δ'} {σ} {e} p e' k i =
  let
    F : I → Type
    F t = Lw (nfT E) (nf δ) t ∘ Lw (nfT E) (nf σ) t ≡ Lw (nfT E) (nf δ') t
    Pw : I → F i0
    Pw k = sym (L (N.wkThin (nfT E) (nf δ)) (N.wkThin (nfT E) (nf σ)))
           ∙ cong q (N.Code-sound (N.wkThin (nfT E) (nf δ) N.∘ N.wkThin (nfT E) (nf σ)) (N.wkThin (nfT E) (nf δ'))
                                  (wkkcode (nfT E) (nf δ) (nf δ') (nf σ) (N.≡→Code (cong nf e)) (N.≡→Code (cong nf e')) k))
    e'₀ : I → F i1
    e'₀ k = transport (λ t → F t) (Pw k)
    Tk : (k : I) → PathP F (Pw k) (e'₀ k)
    Tk k = transport-filler (λ t → F t) (Pw k)
    Y : (j i : I) → hwk E δ i j ∘ hwk E σ i j ≡ hwk E δ' i j
    Y j i = fill (λ t → hwk E δ i (~ t) ∘ hwk E σ i (~ t) ≡ hwk E δ' i (~ t))
                 (λ t → λ { (i = i0) → Tk i1 t ; (i = i1) → e' })
                 (inS (hk (wkThin E σ) e' i)) (~ j)
    E' : (k i : I) → wkThin (hT E i) (h δ i) ∘ wkThin (hT E i) (h σ i) ≡ wkThin (hT E i) (h δ' i)
    E' k i = hfill (λ t → λ { (i = i0) → e'₀ (~ t) ; (i = i1) → e' }) (inS (Y i0 i)) (~ k)
    H0 : (j : I) → Thin (wkF0 {x = x} {δ = δ'} p k j i1) (wkF0 {x = x} {δ = δ} p k j i1)
    H0 j = comp (λ m → Thin (wkF0 {x = x} {δ = δ'} p k j m) (wkF0 {x = x} {δ = δ} p k j m))
                (λ m → λ { (j = i0) → wkt-k {E = qT (nfT E)} {x = qV (nfV x)} {δ = q (nf δ)} {δ' = q (nf δ')} {σ = q (nf σ)}
                                            {e = hk σ e i0} (wkP {E = E} {B = C} p k i0) (e'₀ k) (k ∨ ~ m)
                         ; (j = i1) → q (nf (wkt-k {E = E} {x = x} {δ = δ} {δ' = δ'} {σ = σ} {e = e} p e' k))
                         ; (k = i1) → t-k {x = suc (qV (nfV x)) (compPath-filler (Pc (nfT E) (nfT C) (N.≡→CodeTy (cong nfT p))) (LwT (nfT E) (nfT C)) (~ j))}
                                          {δ = Lw (nfT E) (nf δ) (~ j)} {δ' = Lw (nfT E) (nf δ') (~ j)} (Lw (nfT E) (nf σ) (~ j)) (Tk i1 (~ j))
                         ; (k = i0) → LwkFill (nfT E) {x = nfV x} {δ = nf δ} {δ' = nf δ'} (nf σ) (N.≡→Code (cong nf e)) (~ j) m })
                (t-k {x = Vpath (nfT E) (nfT C) (nfV x) (wkcode (nfT E) (nfT C) (cong nfT p) k) (~ j)} {δ = Lw (nfT E) (nf δ) (~ j)} {δ' = Lw (nfT E) (nf δ') (~ j)}
                     (Lw (nfT E) (nf σ) (~ j)) (Tk k (~ j)))
  in
  comp (λ j → Thin (hTwkextFill {x = x} {δ = δ'} p k i j) (hTwkextFill {x = x} {δ = δ} p k i j))
       (λ j → λ { (k = i0) → hwk E (t-k {x = x} {δ = δ} {δ' = δ'} σ e) i j
                ; (k = i1) → t-k {x = suc (hV x i) (wkW {E = E} {B = C} p j i)} {δ = hwk E δ i j} {δ' = hwk E δ' i j}
                                 (hwk E σ i j) (Y j i)
                ; (i = i0) → H0 j
                ; (i = i1) → wkt-k {x = x} {δ = δ} {δ' = δ'} {σ = σ} {e = e} p e' k })
       (wkt-k {E = hT E i} {A = hT A i} {B = hT B i} {C = hT C i} {x = hV x i} {δ = h δ i} {δ' = h δ' i} {σ = h σ i}
              {e = hk σ e i} (wkP {E = E} {B = C} p k i) (E' k i) k)

-- the HIIT is a set --------------------------------------------------------------------
-- The total spaces are retracts of the total spaces of the normal forms,
-- which are sets; a fibre of a family over a set with a set as total space
-- is a set.

fibreSet : {A : Type}{B : A → Type} → isSet A → isSet (Σ A B) → (a : A) → isSet (B a)
fibreSet {A} {B} sA sT a x y p q =
  subst (λ s → PathP (λ i → PathP (λ j → B (s i j)) x y) p q)
        (isOfHLevelSuc 2 sA a a refl refl (λ i j → fst (sq i j)) refl)
        (λ i j → snd (sq i j))
  where sq = sT (a , x) (a , y) (λ j → a , p j) (λ j → a , q j)

isSetCon : isSet Con
isSetCon = isSetRetract nfC qC hC N.isSetCon

isSetΣConTy : isSet (Σ Con Ty)
isSetΣConTy = isSetRetract (λ { (Γ , A) → nfC Γ , nfT A }) (λ { (Γ , A) → qC Γ , qT A })
                           (λ { (Γ , A) i → hC Γ i , hT A i }) N.isSetConTy

isSetTy : {Γ : Con} → isSet (Ty Γ)
isSetTy {Γ} = fibreSet isSetCon isSetΣConTy Γ

isSetΣVar : isSet (Σ (Σ Con Ty) (λ p → Var (fst p) (snd p)))
isSetΣVar = isSetRetract (λ { ((Γ , A) , x) → (nfC Γ , nfT A) , nfV x }) (λ { ((Γ , A) , x) → (qC Γ , qT A) , qV x })
                         (λ { ((Γ , A) , x) i → (hC Γ i , hT A i) , hV x i })
                         (isSetΣ N.isSetConTy (λ _ → N.isSetVar))

isSetVar : {Γ : Con}{A : Ty Γ} → isSet (Var Γ A)
isSetVar {Γ} {A} = fibreSet isSetΣConTy isSetΣVar (Γ , A)

isSetΣConTyTy : isSet (Σ Con (λ Γ → Ty Γ × Ty Γ))
isSetΣConTyTy = isSetRetract (λ { (Γ , A , B) → nfC Γ , nfT A , nfT B }) (λ { (Γ , A , B) → qC Γ , qT A , qT B })
                             (λ { (Γ , A , B) i → hC Γ i , hT A i , hT B i }) N.isSetConTyTy

isSetΣThin : isSet (Σ (Σ Con (λ Γ → Ty Γ × Ty Γ)) (λ p → Thin (fst (snd p)) (snd (snd p))))
isSetΣThin = isSetRetract (λ { ((Γ , A , B) , σ) → (nfC Γ , nfT A , nfT B) , nf σ })
                          (λ { ((Γ , A , B) , σ) → (qC Γ , qT A , qT B) , q σ })
                          (λ { ((Γ , A , B) , σ) i → (hC Γ i , hT A i , hT B i) , h σ i })
                          (isSetΣ N.isSetConTyTy (λ _ → N.isSetThin))

isSetThin : {Γ : Con}{A B : Ty Γ} → isSet (Thin A B)
isSetThin {Γ} {A} {B} = fibreSet isSetΣConTyTy isSetΣThin (Γ , A , B)

