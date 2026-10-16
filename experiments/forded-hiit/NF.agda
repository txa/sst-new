{-# OPTIONS --cubical -W noUnsupportedIndexedMatch #-}
{-
Normal forms for the telescope layer (no variables, no weakening):
the inductive-recursive syntax, with composition defined by recursion and
the commuting square of a kept entry stored as a code. Codes are
propositions, so NThin A B is a set.
-}
module NF where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Empty renaming (rec to ⊥-rec)

infixr 9 _∘_

data NTy : Type
data NThin : NTy → NTy → Type
_∘_ : {A B C : NTy} → NThin B C → NThin A B → NThin A C
Code : {A A' C C' : NTy} → NThin A C → NThin A' C' → Type

data NTy where
  ε   : NTy
  ext : (A : NTy){B : NTy} → NThin A B → NTy

data NThin where
  tε  : NThin ε ε
  t-d : {A B C : NTy}{δ : NThin A C} → NThin A B → NThin (ext A δ) B
  t-k : {A B C : NTy}{δ : NThin B C}{δ' : NThin A C}
      → (σ : NThin A B) → Code (δ ∘ σ) δ' → NThin (ext A δ') (ext B δ)

Code tε tε = ⊤
Code (t-d σ) (t-d τ) = Code σ τ
Code (t-k σ _) (t-k τ _) = Code σ τ
Code _ _ = ⊥

variable
  A A' A'' B B' C C' C'' D : NTy

-- codes are propositions, reflexive and transitive -------------------------

Code-prop : (σ : NThin A C)(τ : NThin A' C') → isProp (Code σ τ)
Code-prop tε tε = isPropUnit
Code-prop (t-d σ) (t-d τ) = Code-prop σ τ
Code-prop (t-k σ _) (t-k τ _) = Code-prop σ τ
Code-prop tε (t-k τ _) = isProp⊥
Code-prop tε (t-d τ) = isProp⊥
Code-prop (t-k σ _) tε = isProp⊥
Code-prop (t-k σ _) (t-d τ) = isProp⊥
Code-prop (t-d σ) tε = isProp⊥
Code-prop (t-d σ) (t-k τ _) = isProp⊥

Code-refl : (σ : NThin A C) → Code σ σ
Code-refl tε = tt
Code-refl (t-d σ) = Code-refl σ
Code-refl (t-k σ _) = Code-refl σ

Code-trans : (σ : NThin A C)(τ : NThin A' C')(ρ : NThin A'' C'') → Code σ τ → Code τ ρ → Code σ ρ
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

-- composition ---------------------------------------------------------------

Code-∘ : (δ : NThin B C)(δ₂ : NThin B C')(σ : NThin A B) → Code δ δ₂ → Code (δ ∘ σ) (δ₂ ∘ σ)
Code-assoc : (ρ : NThin C D)(δ : NThin B C)(σ : NThin A B) → Code (ρ ∘ (δ ∘ σ)) ((ρ ∘ δ) ∘ σ)

k-code : {D' D'' : NTy}(δC : NThin C D)(δB : NThin B D')(δA : NThin A D'')(δ : NThin B C)(σ : NThin A B)
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

-- codes give equations, and NThin is a set ----------------------------------

t-k-cong : {δ : NThin B C}{δ' : NThin A C}{σ σ' : NThin A B}
           {e : Code (δ ∘ σ) δ'}{e' : Code (δ ∘ σ') δ'}
         → σ ≡ σ' → t-k {δ = δ} {δ' = δ'} σ e ≡ t-k σ' e'
t-k-cong {δ = δ} {δ'} {e = e} {e'} p i =
  t-k (p i) (isProp→PathP (λ j → Code-prop (δ ∘ p j) δ') e e' i)


-- codes for types, and soundness in the total space ------------------------
-- Code ignores the entries of the indices, so soundness has to compare the
-- indices as well (CodeTy). Stating it as a PathP over the index paths
-- means no pattern is ever matched at a fixed index (no K needed).

CodeTy : NTy → NTy → Type
CodeTy ε ε = ⊤
CodeTy (ext A {B} δ) (ext A' {B'} δ') = CodeTy A A' × (CodeTy B B' × Code δ δ')
CodeTy ε (ext _ _) = ⊥
CodeTy (ext _ _) ε = ⊥

CodeTy-prop : (A A' : NTy) → isProp (CodeTy A A')
CodeTy-prop ε ε = isPropUnit
CodeTy-prop (ext A {B} δ) (ext A' {B'} δ') =
  isProp× (CodeTy-prop A A') (isProp× (CodeTy-prop B B') (Code-prop δ δ'))
CodeTy-prop ε (ext _ _) = isProp⊥
CodeTy-prop (ext _ _) ε = isProp⊥

CodeTy-refl : (A : NTy) → CodeTy A A
CodeTy-refl ε = tt
CodeTy-refl (ext A {B} δ) = CodeTy-refl A , CodeTy-refl B , Code-refl δ

soundTy : (A A' : NTy) → CodeTy A A' → A ≡ A'
sound : (σ : NThin A C)(τ : NThin A' C')(cA : CodeTy A A')(cC : CodeTy C C') → Code σ τ
      → PathP (λ i → NThin (soundTy A A' cA i) (soundTy C C' cC i)) σ τ

soundTy ε ε _ = refl
soundTy (ext A {B} δ) (ext A' {B'} δ') (a , b , c) i =
  ext (soundTy A A' a i) {soundTy B B' b i} (sound δ δ' a b c i)

sound tε tε _ _ _ = refl
sound (t-d {A} {B} {E} {γ} σ) (t-d {A'} {B'} {E'} {γ'} τ) (a , e , cγ) cB c i =
  t-d {δ = sound γ γ' a e cγ i} (sound σ τ a cB c i)
sound (t-k {A} {B} {C} {δ} {δ'} σ c₁) (t-k {A'} {B'} {C'} {δ₂} {δ'₂} τ c₂)
      (a , cC , cδ') (b , cC₂ , cδ) c =
  subst (λ x → PathP (λ i → NThin (ext (soundTy A A' a i) {soundTy C C' cC i} (sound δ' δ'₂ a cC cδ' i))
                                   (ext (soundTy B B' b i) {soundTy C C' x i} (sound δ δ₂ b x cδ i)))
                     (t-k σ c₁) (t-k τ c₂))
        (CodeTy-prop C C' cC cC₂)
        (λ i → t-k {C = soundTy C C' cC i} {δ = sound δ δ₂ b cC cδ i} {δ' = sound δ' δ'₂ a cC cδ' i}
                   (sound σ τ a b c i)
                   (isProp→PathP (λ j → Code-prop (sound δ δ₂ b cC cδ j ∘ sound σ τ a b c j)
                                                   (sound δ' δ'₂ a cC cδ' j)) c₁ c₂ i))
sound tε (t-d τ) _ _ ()
sound tε (t-k τ _) _ _ ()
sound (t-d σ) tε _ _ ()
sound (t-d σ) (t-k τ _) _ _ ()
sound (t-k σ _) tε _ _ ()
sound (t-k σ _) (t-d τ) _ _ ()

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

isSetNTy : isSet NTy
isSetNTy = reflPropRel→isSet CodeTy CodeTy-prop CodeTy-refl soundTy

-- codes give equations at a fixed index
Code-sound : (σ τ : NThin A C) → Code σ τ → σ ≡ τ
Code-sound {A} {C} σ τ c =
  subst2 (λ pA pC → PathP (λ i → NThin (pA i) (pC i)) σ τ)
         (isSetNTy _ _ _ refl) (isSetNTy _ _ _ refl)
         (sound σ τ (CodeTy-refl A) (CodeTy-refl C) c)

isSetNThin : isSet (NThin A B)
isSetNThin = reflPropRel→isSet Code Code-prop Code-refl Code-sound

≡→Code : {σ τ : NThin A C} → σ ≡ τ → Code σ τ
≡→Code {σ = σ} p = subst (Code σ) p (Code-refl σ)
