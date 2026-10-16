{-# OPTIONS --cubical -W noUnsupportedIndexedMatch #-}
{-
The forded HIIT for the telescope layer (no variables, no weakening):
composition is a constructor, t-k stores a path, and the keep-keep rule is
conditional (it holds for every path r). There is no ass constructor.

nf  : HIIT → normal forms   (recursion; the path constructors go to refl
                             or to t-k-cong, since codes are propositions)
quote : normal forms → HIIT (recursion on normal forms, with the lemma L
                             that quote commutes with composition)
-}
module FHIIT where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
import NF as N

infixr 9 _∘_
data Ty : Type
data Thin : Ty → Ty → Type

data Ty where
  ε   : Ty
  ext : (A : Ty){B : Ty} → Thin A B → Ty

data Thin where
  _∘_ : {A B C : Ty} → Thin B C → Thin A B → Thin A C
  tε  : Thin ε ε
  t-d : {A B C : Ty}{δ : Thin A C} → Thin A B → Thin (ext A δ) B
  t-k : {A B C : Ty}{δ : Thin B C}{δ' : Thin A C}
      → (σ : Thin A B) → δ ∘ σ ≡ δ' → Thin (ext A δ') (ext B δ)
  ∘tε : {C : Ty}{δ : Thin ε C} → δ ∘ tε ≡ δ
  ∘t-d : {A B C D : Ty}{γ : Thin A D}{δ : Thin B C}{σ : Thin A B}
       → δ ∘ t-d {δ = γ} σ ≡ t-d (δ ∘ σ)
  t-d∘t-k : {A B C D : Ty}{δB : Thin B D}{δA : Thin A D}{δ : Thin B C}{σ : Thin A B}
            {e : δB ∘ σ ≡ δA}
          → t-d {δ = δB} δ ∘ t-k σ e ≡ t-d (δ ∘ σ)
  t-k∘t-k : {A B C D : Ty}{δC : Thin C D}{δB : Thin B D}{δA : Thin A D}
            {δ : Thin B C}{σ : Thin A B}{q : δC ∘ δ ≡ δB}{e : δB ∘ σ ≡ δA}
          → (r : δC ∘ (δ ∘ σ) ≡ δA)
          → t-k δ q ∘ t-k σ e ≡ t-k (δ ∘ σ) r

-- normalisation ---------------------------------------------------------------

-- TERMINATING: the recursion is structural, but the stored path e of t-k
-- (and r of t-k∘t-k) is a constructor argument of path type, and Agda's
-- termination checker does not see nf (e i) as a structural call.
{-# TERMINATING #-}
nfT : Ty → N.NTy
{-# TERMINATING #-}
nf  : {A B : Ty} → Thin A B → N.NThin (nfT A) (nfT B)

nfT ε = N.ε
nfT (ext A δ) = N.ext (nfT A) (nf δ)

nf (δ ∘ σ) = nf δ N.∘ nf σ
nf tε = N.tε
nf (t-d σ) = N.t-d (nf σ)
nf (t-k σ e) = N.t-k (nf σ) (N.≡→Code (cong nf e))
nf (∘tε {δ = δ} i) = nf δ
nf (∘t-d {δ = δ} {σ = σ} i) = N.t-d (nf δ N.∘ nf σ)
nf (t-d∘t-k {δ = δ} {σ = σ} i) = N.t-d (nf δ N.∘ nf σ)
nf (t-k∘t-k {δC = δC} {δB} {δA} {δ} {σ} {q} {e} r i) =
  N.t-k-cong {σ = nf δ N.∘ nf σ}
    {e = N.k-code (nf δC) (nf δB) (nf δA) (nf δ) (nf σ) (N.≡→Code (cong nf q)) (N.≡→Code (cong nf e))}
    {e' = N.≡→Code (cong nf r)} refl i

-- quoting -----------------------------------------------------------------------

qT : N.NTy → Ty
q  : {A B : N.NTy} → N.NThin A B → Thin (qT A) (qT B)
L  : {A B C : N.NTy}(δ : N.NThin B C)(σ : N.NThin A B) → q (δ N.∘ σ) ≡ q δ ∘ q σ

-- move the thinning of a keep along a path, transporting its stored path
tk-move : {A B C : Ty}{δ : Thin B C}{δ' : Thin A C}{s s' : Thin A B}
          (u : s ≡ s'){P : δ ∘ s ≡ δ'} → t-k s P ≡ t-k s' (subst (λ x → δ ∘ x ≡ δ') u P)
tk-move {δ = δ} {δ'} u {P} i = t-k (u i) (subst-filler (λ x → δ ∘ x ≡ δ') u P i)

qT N.ε = ε
qT (N.ext A δ) = ext (qT A) (q δ)

q N.tε = tε
q (N.t-d σ) = t-d (q σ)
q (N.t-k {δ = δ} σ c) = t-k (q σ) (sym (L δ σ) ∙ cong q (N.Code-sound _ _ c))

L δ N.tε = sym ∘tε
L δ (N.t-d σ) = cong t-d (L δ σ) ∙ sym ∘t-d
L (N.t-d δ) (N.t-k σ c) = cong t-d (L δ σ) ∙ sym t-d∘t-k
L (N.t-k δ c₁) (N.t-k σ c₂) = tk-move (L δ σ) ∙ sym (t-k∘t-k _)

-- quote ∘ nf is the identity ----------------------------------------------------

-- TERMINATING: this is HIIT induction. In the case of a path constructor
-- the clause has to agree with h on the two endpoints, and the case for
-- t-k∘t-k mentions h on its right endpoint t-k (δ ∘ σ) r explicitly; the
-- eliminator provides this, but Agda's termination checker does not know it.
{-# TERMINATING #-}
hT : (A : Ty) → qT (nfT A) ≡ A
{-# TERMINATING #-}
h  : {A B : Ty}(σ : Thin A B) → PathP (λ i → Thin (hT A i) (hT B i)) (q (nf σ)) σ

-- the stored path of a keep: built from naturality of h along e
{-# TERMINATING #-}
hk : {A B C : Ty}{δ : Thin B C}{δ' : Thin A C}(σ : Thin A B)(e : δ ∘ σ ≡ δ')
   → PathP (λ i → h δ i ∘ h σ i ≡ h δ' i)
           (sym (L (nf δ) (nf σ)) ∙ cong q (N.Code-sound _ _ (N.≡→Code (cong nf e)))) e

hT ε = refl
hT (ext A δ) i = ext (hT A i) (h δ i)

h (δ ∘ σ) = L (nf δ) (nf σ) ◁ (λ i → h δ i ∘ h σ i)
h tε = refl
h (t-d {δ = γ} σ) i = t-d {δ = h γ i} (h σ i)
h (t-k σ e) i = t-k (h σ i) (hk σ e i)
h (∘tε {δ = δ} k) i =
  hcomp (λ j → λ { (k = i0) → doubleWhiskFiller (sym ∘tε) (λ i → h δ i ∘ tε) refl j i
                 ; (k = i1) → h δ i
                 ; (i = i0) → ∘tε {δ = q (nf δ)} (k ∨ j)
                 ; (i = i1) → ∘tε {δ = δ} k })
        (∘tε {δ = h δ i} k)
h (∘t-d {γ = γ} {δ = δ} {σ = σ} k) i =
  hcomp (λ j → λ { (k = i0) → doubleWhiskFiller L₁ (λ i → h δ i ∘ t-d {δ = h γ i} (h σ i)) refl j i
                 ; (k = i1) → t-d {δ = h γ i} (doubleWhiskFiller L' (λ i → h δ i ∘ h σ i) refl j i)
                 ; (i = i0) → compPath-filler (cong (t-d {δ = q (nf γ)}) L') (sym ∘t-dq) (~ k) (~ j)
                 ; (i = i1) → ∘t-d {γ = γ} {δ = δ} {σ = σ} k })
        (∘t-d {γ = h γ i} {δ = h δ i} {σ = h σ i} k)
  where L' = L (nf δ) (nf σ)
        ∘t-dq = ∘t-d {γ = q (nf γ)} {δ = q (nf δ)} {σ = q (nf σ)}
        L₁ = cong (t-d {δ = q (nf γ)}) L' ∙ sym ∘t-dq
h (t-d∘t-k {δB = δB} {δA = δA} {δ = δ} {σ = σ} {e = e} k) i =
  hcomp (λ j → λ { (k = i0) → doubleWhiskFiller L₁ (λ i → t-d {δ = h δB i} (h δ i) ∘ t-k (h σ i) (hk σ e i)) refl j i
                 ; (k = i1) → t-d {δ = h δA i} (doubleWhiskFiller L' (λ i → h δ i ∘ h σ i) refl j i)
                 ; (i = i0) → compPath-filler (cong (t-d {δ = q (nf δA)}) L') (sym t-d∘t-kq) (~ k) (~ j)
                 ; (i = i1) → t-d∘t-k {δ = δ} {σ = σ} {e = e} k })
        (t-d∘t-k {δB = h δB i} {δA = h δA i} {δ = h δ i} {σ = h σ i} {e = hk σ e i} k)
  where L' = L (nf δ) (nf σ)
        t-d∘t-kq = t-d∘t-k {δB = q (nf δB)} {δA = q (nf δA)} {δ = q (nf δ)} {σ = q (nf σ)}
                           {e = sym (L (nf δB) (nf σ)) ∙ cong q (N.Code-sound _ _ (N.≡→Code (cong nf e)))}
        L₁ = cong (t-d {δ = q (nf δA)}) L' ∙ sym t-d∘t-kq
h (t-k∘t-k {A} {B} {C} {D} {δC} {δB} {δA} {δ} {σ} {q₁} {e} r k) i =
  hcomp (λ j → λ { (k = i0) → doubleWhiskFiller L₁ M refl j i
                 ; (k = i1) → t-k (W' j i) (Z j i)
                 ; (i = i0) → B₀ k j
                 ; (i = i1) → t-k∘t-k {q = q₁} {e = e} r k })
        (t-k∘t-k {δC = h δC i} {δB = h δB i} {δA = h δA i} {δ = h δ i} {σ = h σ i}
                 {q = hk δ q₁ i} {e = hk σ e i} (Z i0 i) k)
  where
    s₀ = nf δ N.∘ nf σ
    L' = L (nf δ) (nf σ)
    L₁ = L (nf (t-k δ q₁)) (nf (t-k σ e))
    M : PathP (λ i → Thin (hT (ext A δA) i) (hT (ext C δC) i))
              (q (nf (t-k δ q₁)) ∘ q (nf (t-k σ e))) (t-k δ q₁ ∘ t-k σ e)
    M i = h (t-k δ q₁) i ∘ h (t-k σ e) i
    M' : PathP (λ i → Thin (hT A i) (hT C i)) (q (nf δ) ∘ q (nf σ)) (δ ∘ σ)
    M' i = h δ i ∘ h σ i
    W' = doubleWhiskFiller L' M' refl
    F  = λ x → q (nf δC) ∘ x ≡ q (nf δA)
    -- the stored codes on the two sides, and the path between them
    kc = N.k-code (nf δC) (nf δB) (nf δA) (nf δ) (nf σ) (N.≡→Code (cong nf q₁)) (N.≡→Code (cong nf e))
    cr = N.≡→Code (cong nf r)
    Pk : (k : I) → q (nf δC) ∘ q s₀ ≡ q (nf δA)
    Pk k = sym (L (nf δC) s₀)
           ∙ cong q (N.Code-sound _ _ (isProp→PathP (λ _ → N.Code-prop (nf δC N.∘ s₀) (nf δA)) kc cr k))
    ρ : (k : I) → F (q (nf δ) ∘ q (nf σ))
    ρ k = subst F L' (Pk k)
    -- the keep-keep rule at the quote level, for any stored path
    tkq : (r' : F (q (nf δ) ∘ q (nf σ))) → _
    tkq r' = t-k∘t-k {δC = q (nf δC)} {δB = q (nf δB)} {δA = q (nf δA)} {δ = q (nf δ)} {σ = q (nf σ)}
                     {q = hk δ q₁ i0} {e = hk σ e i0} r'
    -- the stored path of the right-hand side, moved back along the whisker
    ζ : (j : I) → F (L' (~ j))
    ζ j = subst-filler F L' (Pk i1) (~ j)
    Z : (j i : I) → h δC i ∘ W' j i ≡ h δA i
    Z j i = fill (λ m → h δC i ∘ W' (~ m) i ≡ h δA i)
                 (λ m → λ { (i = i0) → ζ (~ m) ; (i = i1) → r })
                 (inS (hk (δ ∘ σ) r i)) (~ j)
    -- the face at the quote level
    T : (k : I) → _
    T k = (λ m → tkq (ρ k) m) ∙ (λ m → tk-move L' {Pk k} (~ m))
    B₀ : (k j : I) → _
    B₀ k j = hcomp (λ m → λ { (k = i0) → symDistr (tk-move L' {Pk i0}) (sym (tkq (ρ i0))) (~ m) j
                            ; (k = i1) → compPath-filler' (tkq (ρ i1)) (sym (tk-move L' {Pk i1})) (~ m) j
                            ; (j = i0) → tkq (ρ i1) (k ∧ m)
                            ; (j = i1) → t-k (q s₀) (Pk k) })
                   (T k j)

hk {A} {B} {C} {δ} {δ'} σ e =
  subst (λ P → PathP (λ i → h δ i ∘ h σ i ≡ h δ' i) (sym (L (nf δ) (nf σ)) ∙ cong q P) e)
        (N.isSetNThin _ _ (cong nf e) (N.Code-sound _ _ (N.≡→Code (cong nf e))))
        E
  where
    E : PathP (λ i → h δ i ∘ h σ i ≡ h δ' i) (sym (L (nf δ) (nf σ)) ∙ cong (λ x → q (nf x)) e) e
    E i j = hcomp (λ k → λ { (j = i0) → doubleWhiskFiller (L (nf δ) (nf σ)) (λ i → h δ i ∘ h σ i) refl (~ k) i
                           ; (j = i1) → h δ' i
                           ; (i = i0) → compPath-filler' (sym (L (nf δ) (nf σ))) (cong (λ x → q (nf x)) e) k j
                           ; (i = i1) → e j })
                  (h (e j) i)

-- the HIIT is a set ---------------------------------------------------------------
-- Ty and Thin A B are retracts of the normal forms, which form a set.

isSetTy : isSet Ty
isSetTy = isSetRetract nfT qT hT N.isSetNTy

isSetThin : {A B : Ty} → isSet (Thin A B)
isSetThin {A} {B} =
  isSetRetract nf (λ n → transport (λ i → Thin (hT A i) (hT B i)) (q n))
               (λ σ → fromPathP (h σ)) N.isSetNThin
