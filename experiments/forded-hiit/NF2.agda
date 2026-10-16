{-# OPTIONS --cubical -W noUnsupportedIndexedMatch #-}
{-
Normal forms with contexts, variables and one-step weakening: the
inductive-recursive syntax of TT.agda in cubical Agda, with codes.

All indices of constructors are free of defined functions: a kept entry
stores a code for its commuting square (as in NF.agda), and the variables
are forded too: zero and suc store a code CodeTy (wkTy A) C instead of
being indexed by wkTy A. Codes are propositions, so all sorts are sets.
-}
module NF2 where

open import Cubical.Foundations.Prelude hiding (_▷_)
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Empty renaming (rec to ⊥-rec)

infixl 5 _▷_
infixr 9 _∘_

data Con : Type
data Ty : Con → Type
data Var : (Γ : Con) → Ty Γ → Type
data Thin : {Γ : Con} → Ty Γ → Ty Γ → Type

data Con where
  •   : Con
  _▷_ : (Γ : Con) → Ty Γ → Con

wkTy   : {Γ : Con}(B : Ty Γ) → Ty Γ → Ty (Γ ▷ B)
_∘_    : {Γ : Con}{A B C : Ty Γ} → Thin B C → Thin A B → Thin A C
CodeTy : {Γ Γ' : Con} → Ty Γ → Ty Γ' → Type
CodeV  : {Γ Γ' : Con}{C : Ty Γ}{C' : Ty Γ'} → Var Γ C → Var Γ' C' → Type
Code   : {Γ Γ' : Con}{A C : Ty Γ}{A' C' : Ty Γ'} → Thin A C → Thin A' C' → Type

data Ty where
  ε   : {Γ : Con} → Ty Γ
  ext : {Γ : Con}(A : Ty Γ){B : Ty Γ} → Var Γ B → Thin A B → Ty Γ

data Var where
  zero : {Γ : Con}{A : Ty Γ}{C : Ty (Γ ▷ A)} → CodeTy (wkTy A A) C → Var (Γ ▷ A) C
  suc  : {Γ : Con}{A B : Ty Γ}{C : Ty (Γ ▷ B)} → Var Γ A → CodeTy (wkTy B A) C → Var (Γ ▷ B) C

data Thin where
  tε  : {Γ : Con} → Thin {Γ} ε ε
  t-d : {Γ : Con}{A B C : Ty Γ}{x : Var Γ C}{δ : Thin A C} → Thin A B → Thin (ext A x δ) B
  t-k : {Γ : Con}{A B C : Ty Γ}{x : Var Γ C}{δ : Thin B C}{δ' : Thin A C}
      → (σ : Thin A B) → Code (δ ∘ σ) δ' → Thin (ext A x δ') (ext B x δ)

variable
  Γ Γ' Γ'' : Con
  A A' A'' B B' C C' C'' D : Ty Γ

-- codes --------------------------------------------------------------------------
-- Codes compare the shape of a term; indices are compared separately.

CodeTy ε ε = ⊤
CodeTy (ext A {B} x δ) (ext A' {B'} x' δ') = CodeTy A A' × (CodeTy B B' × (CodeV x x' × Code δ δ'))
CodeTy ε (ext _ _ _) = ⊥
CodeTy (ext _ _ _) ε = ⊥

CodeV (zero _) (zero _) = ⊤
CodeV (suc {A = A} x _) (suc {A = A'} x' _) = CodeTy A A' × CodeV x x'
CodeV (zero _) (suc _ _) = ⊥
CodeV (suc _ _) (zero _) = ⊥

Code tε tε = ⊤
Code (t-d σ) (t-d τ) = Code σ τ
Code (t-k σ _) (t-k τ _) = Code σ τ
Code tε (t-d _) = ⊥
Code tε (t-k _ _) = ⊥
Code (t-d _) tε = ⊥
Code (t-d _) (t-k _ _) = ⊥
Code (t-k _ _) tε = ⊥
Code (t-k _ _) (t-d _) = ⊥

CodeTy-refl : (A : Ty Γ) → CodeTy A A
CodeV-refl  : {C : Ty Γ}(x : Var Γ C) → CodeV x x
Code-refl   : (σ : Thin A C) → Code σ σ

CodeTy-refl ε = tt
CodeTy-refl (ext A {B} x δ) = CodeTy-refl A , CodeTy-refl B , CodeV-refl x , Code-refl δ
CodeV-refl (zero _) = tt
CodeV-refl (suc {A = A} x _) = CodeTy-refl A , CodeV-refl x
Code-refl tε = tt
Code-refl (t-d σ) = Code-refl σ
Code-refl (t-k σ _) = Code-refl σ

Code-trans : {Γ₁ Γ₂ Γ₃ : Con}{A₁ C₁ : Ty Γ₁}{A₂ C₂ : Ty Γ₂}{A₃ C₃ : Ty Γ₃}
             (σ : Thin A₁ C₁)(τ : Thin A₂ C₂)(ρ : Thin A₃ C₃) → Code σ τ → Code τ ρ → Code σ ρ
Code-trans tε tε tε u v = tt
Code-trans (t-d σ) (t-d τ) (t-d ρ) u v = Code-trans σ τ ρ u v
Code-trans (t-k σ _) (t-k τ _) (t-k ρ _) u v = Code-trans σ τ ρ u v
Code-trans tε (t-k τ _) ρ () v
Code-trans tε (t-d τ) ρ () v
Code-trans (t-k σ _) tε ρ () v
Code-trans (t-k σ _) (t-d τ) ρ () v
Code-trans (t-d σ) tε ρ () v
Code-trans (t-d σ) (t-k τ _) ρ () v
Code-trans tε tε (t-k ρ _) u ()
Code-trans tε tε (t-d ρ) u ()
Code-trans (t-k σ _) (t-k τ _) tε u ()
Code-trans (t-k σ _) (t-k τ _) (t-d ρ) u ()
Code-trans (t-d σ) (t-d τ) tε u ()
Code-trans (t-d σ) (t-d τ) (t-k ρ _) u ()

-- composition --------------------------------------------------------------------

Code-∘ : {A B C C' : Ty Γ}
         (δ : Thin B C)(δ₂ : Thin B C')(σ : Thin A B) → Code δ δ₂ → Code (δ ∘ σ) (δ₂ ∘ σ)
Code-assoc : (ρ : Thin C D)(δ : Thin B C)(σ : Thin A B) → Code (ρ ∘ (δ ∘ σ)) ((ρ ∘ δ) ∘ σ)

k-code : {D' D'' : Ty Γ}(δC : Thin C D)(δB : Thin B D')(δA : Thin A D'')(δ : Thin B C)(σ : Thin A B)
       → Code (δC ∘ δ) δB → Code (δB ∘ σ) δA → Code (δC ∘ (δ ∘ σ)) δA
k-code δC δB δA δ σ q e =
  Code-trans (δC ∘ (δ ∘ σ)) ((δC ∘ δ) ∘ σ) δA (Code-assoc δC δ σ)
    (Code-trans ((δC ∘ δ) ∘ σ) (δB ∘ σ) δA (Code-∘ (δC ∘ δ) δB σ q) e)

δ ∘ tε = δ
δ ∘ t-d σ = t-d (δ ∘ σ)
t-d δ ∘ t-k σ e = t-d (δ ∘ σ)
t-k {δ = δC} {δ' = δB} δ q ∘ t-k {δ' = δA} σ e = t-k (δ ∘ σ) (k-code δC δB δA δ σ q e)

Code-∘ δ δ₂ tε c = c
Code-∘ δ δ₂ (t-d σ) c = Code-∘ δ δ₂ σ c
Code-∘ (t-d δ) (t-d δ₂) (t-k σ _) c = Code-∘ δ δ₂ σ c
Code-∘ (t-k δ _) (t-k δ₂ _) (t-k σ _) c = Code-∘ δ δ₂ σ c
Code-∘ (t-d δ) (t-k δ₂ _) (t-k σ _) ()
Code-∘ (t-k δ _) (t-d δ₂) (t-k σ _) ()

Code-assoc ρ δ tε = Code-refl (ρ ∘ δ)
Code-assoc ρ δ (t-d σ) = Code-assoc ρ δ σ
Code-assoc ρ (t-d δ) (t-k σ _) = Code-assoc ρ δ σ
Code-assoc (t-d ρ) (t-k δ _) (t-k σ _) = Code-assoc ρ δ σ
Code-assoc (t-k ρ _) (t-k δ _) (t-k σ _) = Code-assoc ρ δ σ

-- weakening ----------------------------------------------------------------------

wkThin : (E : Ty Γ){A A' : Ty Γ} → Thin A A' → Thin (wkTy E A) (wkTy E A')
Code-wk : {Γ' : Con}(E : Ty Γ)(E' : Ty Γ'){A C : Ty Γ}{A' C' : Ty Γ'}
          (σ : Thin A C)(τ : Thin A' C') → Code σ τ → Code (wkThin E σ) (wkThin E' τ)
Code-wk∘ : (E : Ty Γ)(δ : Thin B C)(σ : Thin A B) → Code (wkThin E δ ∘ wkThin E σ) (wkThin E (δ ∘ σ))

wkTy E ε = ε
wkTy E (ext A {B} x δ) = ext (wkTy E A) (suc x (CodeTy-refl (wkTy E B))) (wkThin E δ)

wkThin E tε = tε
wkThin E (t-d σ) = t-d (wkThin E σ)
wkThin E (t-k {δ = δ} {δ' = δ'} σ c) =
  t-k (wkThin E σ) (Code-trans (wkThin E δ ∘ wkThin E σ) (wkThin E (δ ∘ σ)) (wkThin E δ')
                               (Code-wk∘ E δ σ) (Code-wk E E (δ ∘ σ) δ' c))

Code-wk E E' tε tε c = tt
Code-wk E E' (t-d σ) (t-d τ) c = Code-wk E E' σ τ c
Code-wk E E' (t-k σ _) (t-k τ _) c = Code-wk E E' σ τ c

Code-wk∘ E δ tε = Code-refl (wkThin E δ)
Code-wk∘ E δ (t-d σ) = Code-wk∘ E δ σ
Code-wk∘ E (t-d δ) (t-k σ _) = Code-wk∘ E δ σ
Code-wk∘ E (t-k δ _) (t-k σ _) = Code-wk∘ E δ σ

-- codes are propositions -----------------------------------------------------------

CodeTy-prop : (A : Ty Γ)(A' : Ty Γ') → isProp (CodeTy A A')
CodeV-prop  : {C : Ty Γ}{C' : Ty Γ'}(x : Var Γ C)(x' : Var Γ' C') → isProp (CodeV x x')
Code-prop   : {A C : Ty Γ}{A' C' : Ty Γ'}(σ : Thin A C)(τ : Thin A' C') → isProp (Code σ τ)

CodeTy-prop ε ε = isPropUnit
CodeTy-prop (ext A {B} x δ) (ext A' {B'} x' δ') =
  isProp× (CodeTy-prop A A') (isProp× (CodeTy-prop B B') (isProp× (CodeV-prop x x') (Code-prop δ δ')))
CodeTy-prop ε (ext _ _ _) = isProp⊥
CodeTy-prop (ext _ _ _) ε = isProp⊥

CodeV-prop (zero _) (zero _) = isPropUnit
CodeV-prop (suc {A = A} x _) (suc {A = A'} x' _) = isProp× (CodeTy-prop A A') (CodeV-prop x x')
CodeV-prop (zero _) (suc _ _) = isProp⊥
CodeV-prop (suc _ _) (zero _) = isProp⊥

Code-prop tε tε = isPropUnit
Code-prop (t-d σ) (t-d τ) = Code-prop σ τ
Code-prop (t-k σ _) (t-k τ _) = Code-prop σ τ
Code-prop tε (t-d _) = isProp⊥
Code-prop tε (t-k _ _) = isProp⊥
Code-prop (t-d _) tε = isProp⊥
Code-prop (t-d _) (t-k _ _) = isProp⊥
Code-prop (t-k _ _) tε = isProp⊥
Code-prop (t-k _ _) (t-d _) = isProp⊥

t-k-cong : {x : Var Γ C}{δ : Thin B C}{δ' : Thin A C}{σ σ' : Thin A B}
           {e : Code (δ ∘ σ) δ'}{e' : Code (δ ∘ σ') δ'}
         → σ ≡ σ' → t-k {x = x} {δ = δ} {δ' = δ'} σ e ≡ t-k σ' e'
t-k-cong {δ = δ} {δ'} {e = e} {e'} p i =
  t-k (p i) (isProp→PathP (λ j → Code-prop (δ ∘ p j) δ') e e' i)

-- contexts --------------------------------------------------------------------------

CodeCon : Con → Con → Type
CodeCon • • = ⊤
CodeCon (Γ ▷ A) (Γ' ▷ A') = CodeCon Γ Γ' × CodeTy A A'
CodeCon • (_ ▷ _) = ⊥
CodeCon (_ ▷ _) • = ⊥

CodeCon-prop : (Γ Γ' : Con) → isProp (CodeCon Γ Γ')
CodeCon-prop • • = isPropUnit
CodeCon-prop (Γ ▷ A) (Γ' ▷ A') = isProp× (CodeCon-prop Γ Γ') (CodeTy-prop A A')
CodeCon-prop • (_ ▷ _) = isProp⊥
CodeCon-prop (_ ▷ _) • = isProp⊥

CodeCon-refl : (Γ : Con) → CodeCon Γ Γ
CodeCon-refl • = tt
CodeCon-refl (Γ ▷ A) = CodeCon-refl Γ , CodeTy-refl A

-- soundness, as paths over the index paths -------------------------------------------

soundCon : (Γ Γ' : Con) → CodeCon Γ Γ' → Γ ≡ Γ'
soundTy  : (cΓ : CodeCon Γ Γ')(A : Ty Γ)(A' : Ty Γ') → CodeTy A A'
         → PathP (λ i → Ty (soundCon Γ Γ' cΓ i)) A A'
soundV   : {C : Ty Γ}{C' : Ty Γ'}(cΓ : CodeCon Γ Γ')(cC : CodeTy C C')(x : Var Γ C)(x' : Var Γ' C')
         → CodeV x x' → PathP (λ i → Var (soundCon Γ Γ' cΓ i) (soundTy cΓ C C' cC i)) x x'
sound    : {A C : Ty Γ}{A' C' : Ty Γ'}(cΓ : CodeCon Γ Γ')(cA : CodeTy A A')(cC : CodeTy C C')
           (σ : Thin A C)(τ : Thin A' C') → Code σ τ
         → PathP (λ i → Thin (soundTy cΓ A A' cA i) (soundTy cΓ C C' cC i)) σ τ

soundCon • • _ = refl
soundCon (Γ ▷ A) (Γ' ▷ A') (cΓ , cA) i = soundCon Γ Γ' cΓ i ▷ soundTy cΓ A A' cA i

soundTy cΓ ε ε _ i = ε
soundTy cΓ (ext A {B} x δ) (ext A' {B'} x' δ') (a , b , cx , cδ) i =
  ext (soundTy cΓ A A' a i) {soundTy cΓ B B' b i} (soundV cΓ b x x' cx i) (sound cΓ a b δ δ' cδ i)

soundV {Γ = Γ ▷ A} {Γ' = Γ' ▷ A'} {C} {C'} (cΓ , cA) cC (zero c) (zero c') _ i =
  zero {Γ = soundCon Γ Γ' cΓ i} {A = soundTy cΓ A A' cA i} {C = soundTy (cΓ , cA) C C' cC i}
       (isProp→PathP (λ j → CodeTy-prop (wkTy (soundTy cΓ A A' cA j) (soundTy cΓ A A' cA j)) (soundTy (cΓ , cA) C C' cC j)) c c' i)
soundV {Γ = Γ ▷ B} {Γ' = Γ' ▷ B'} {C} {C'} (cΓ , cB) cC (suc {A = A} x c) (suc {A = A'} x' c') (cA , cx) i =
  suc {Γ = soundCon Γ Γ' cΓ i} {A = soundTy cΓ A A' cA i} {B = soundTy cΓ B B' cB i}
      {C = soundTy (cΓ , cB) C C' cC i}
      (soundV cΓ cA x x' cx i)
      (isProp→PathP (λ j → CodeTy-prop (wkTy (soundTy cΓ B B' cB j) (soundTy cΓ A A' cA j)) (soundTy (cΓ , cB) C C' cC j)) c c' i)
soundV _ _ (zero _) (suc _ _) ()
soundV _ _ (suc _ _) (zero _) ()

sound cΓ _ _ tε tε _ i = tε
sound cΓ (a , e , cy , cγ) cB (t-d {A = A} {B} {E} {y} {γ} σ) (t-d {A = A'} {B'} {E'} {y'} {γ'} τ) c i =
  t-d {x = soundV cΓ e y y' cy i} {δ = sound cΓ a e γ γ' cγ i} (sound cΓ a cB σ τ c i)
sound {Γ = Γ} {Γ' = Γ'} cΓ (a , cC , cx , cδ') (b , cC₂ , cx₂ , cδ)
      (t-k {A = A} {B} {C} {x} {δ} {δ'} σ c₁) (t-k {A = A'} {B'} {C'} {x'} {δ₂} {δ'₂} τ c₂) c =
  subst2 (λ u v → PathP (λ i → Thin (ext (soundTy cΓ A A' a i) {soundTy cΓ C C' cC i} (soundV cΓ cC x x' cx i)
                                         (sound cΓ a cC δ' δ'₂ cδ' i))
                                    (ext (soundTy cΓ B B' b i) {soundTy cΓ C C' u i} (soundV cΓ u x x' v i)
                                         (sound cΓ b u δ δ₂ cδ i)))
                        (t-k σ c₁) (t-k τ c₂))
         (CodeTy-prop C C' cC cC₂) (CodeV-prop x x' cx cx₂)
         (λ i → t-k {x = soundV cΓ cC x x' cx i} {δ = sound cΓ b cC δ δ₂ cδ i}
                    {δ' = sound cΓ a cC δ' δ'₂ cδ' i}
                    (sound cΓ a b σ τ c i)
                    (isProp→PathP (λ j → Code-prop (sound cΓ b cC δ δ₂ cδ j ∘ sound cΓ a b σ τ c j)
                                                    (sound cΓ a cC δ' δ'₂ cδ' j)) c₁ c₂ i))
sound _ _ _ tε (t-d _) ()
sound _ _ _ tε (t-k _ _) ()
sound _ _ _ (t-d _) tε ()
sound _ _ _ (t-d _) (t-k _ _) ()
sound _ _ _ (t-k _ _) tε ()
sound _ _ _ (t-k _ _) (t-d _) ()

-- sets --------------------------------------------------------------------------------

-- a reflexive, proposition-valued relation implying equality makes a set
-- (HoTT book, Theorem 7.2.2)
module _ {X : Type}(R : X → X → Type)(Rprop : ∀ x y → isProp (R x y))
         (Rrefl : ∀ x → R x x)(Rid : ∀ x y → R x y → x ≡ y) where
  private
    canon : {x y : X} → R x y → x ≡ y
    canon {x} {y} r = sym (Rid x x (Rrefl x)) ∙ Rid x y r

    canon-path : {x y : X}(p : x ≡ y) → p ≡ canon (subst (R x) p (Rrefl x))
    canon-path {x} = J (λ y p → p ≡ canon (subst (R x) p (Rrefl x)))
      (sym (cong (λ r → sym (Rid x x (Rrefl x)) ∙ Rid x x r) (substRefl {B = R x} (Rrefl x))
            ∙ lCancel (Rid x x (Rrefl x))))

  reflPropRel→isSet : isSet X
  reflPropRel→isSet x y p q =
    canon-path p ∙ cong canon (Rprop x y _ _) ∙ sym (canon-path q)

isSetCon : isSet Con
isSetCon = reflPropRel→isSet CodeCon CodeCon-prop CodeCon-refl soundCon

-- the loop on Γ given by its reflexivity code is refl
loopCon : (Γ : Con) → soundCon Γ Γ (CodeCon-refl Γ) ≡ refl
loopCon Γ = isSetCon _ _ _ _

-- opaque: these are only ever used as paths, and unfolding them during
-- conversion checking in FHIIT2 is very expensive
opaque
  CodeTy-sound : (A A' : Ty Γ) → CodeTy A A' → A ≡ A'
  CodeTy-sound {Γ} A A' c =
    subst (λ p → PathP (λ i → Ty (p i)) A A') (loopCon Γ) (soundTy (CodeCon-refl Γ) A A' c)

  isSetTy : isSet (Ty Γ)
  isSetTy = reflPropRel→isSet CodeTy CodeTy-prop CodeTy-refl CodeTy-sound

  -- at fixed indices: the index paths form a loop in a total space which is a
  -- set, so the loop can be contracted

  isSetConTy : isSet (Σ Con Ty)
  isSetConTy = isSetΣ isSetCon (λ _ → isSetTy)

  isSetConTyTy : isSet (Σ Con (λ Γ → Ty Γ × Ty Γ))
  isSetConTyTy = isSetΣ isSetCon (λ _ → isSet× isSetTy isSetTy)

  CodeV-sound : {C : Ty Γ}(x x' : Var Γ C) → CodeV x x' → x ≡ x'
  CodeV-sound {Γ} {C} x x' c =
    subst (λ ℓ → PathP (λ i → Var (fst (ℓ i)) (snd (ℓ i))) x x')
          (isSetConTy _ _ (λ i → soundCon Γ Γ (CodeCon-refl Γ) i , soundTy (CodeCon-refl Γ) C C (CodeTy-refl C) i) refl)
          (soundV (CodeCon-refl Γ) (CodeTy-refl C) x x' c)

  Code-sound : {A C : Ty Γ}(σ τ : Thin A C) → Code σ τ → σ ≡ τ
  Code-sound {Γ} {A} {C} σ τ c =
    subst (λ ℓ → PathP (λ i → Thin (fst (snd (ℓ i))) (snd (snd (ℓ i)))) σ τ)
          (isSetConTyTy _ _ (λ i → soundCon Γ Γ (CodeCon-refl Γ) i ,
                                    soundTy (CodeCon-refl Γ) A A (CodeTy-refl A) i ,
                                    soundTy (CodeCon-refl Γ) C C (CodeTy-refl C) i) refl)
          (sound (CodeCon-refl Γ) (CodeTy-refl A) (CodeTy-refl C) σ τ c)

  isSetVar : {C : Ty Γ} → isSet (Var Γ C)
  isSetVar = reflPropRel→isSet CodeV CodeV-prop CodeV-refl CodeV-sound

  isSetThin : {A C : Ty Γ} → isSet (Thin A C)
  isSetThin = reflPropRel→isSet Code Code-prop Code-refl Code-sound

≡→CodeTy : {A A' : Ty Γ} → A ≡ A' → CodeTy A A'
≡→CodeTy {A = A} p = subst (CodeTy A) p (CodeTy-refl A)

≡→Code : {σ τ : Thin A C} → σ ≡ τ → Code σ τ
≡→Code {σ = σ} p = subst (Code σ) p (Code-refl σ)
