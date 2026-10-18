{-# OPTIONS --cubical -W noUnsupportedIndexedMatch #-}
{-
The standard interpretation of the inductive-recursive syntax (TT.agda)
into families of GROUPOIDS, in Cubical Agda, without UIP.

Two design decisions:

* Forded semantics of extension:
      ⟦ ext A x δ ⟧T γ = Σ a. Σ d. (⟦ δ ⟧ a ≡ d) × ⟦ x ⟧ d
  (equivalent to Σ a. ⟦ x ⟧ (⟦ δ ⟧ a) by contracting singletons). A kept
  entry then never transports the value v; it only changes the stored
  path. Equations between semantic thinnings have no fibre component.

* Codes act semantically:  ≈ : Code σ τ → ⟦ σ ⟧ a ≡ ⟦ τ ⟧ a  is defined by
  recursion, instead of applying ⟦_⟧ to Code-sound (which does not compute).

What remains are 2-cells in the semantic telescopes (coherences of ⟦∘⟧,
≈ and unwk-nat), proved by induction. 3-cells are trivial because the
semantic telescopes are groupoids.

Equality reasoning uses Agda's inductive identity type (J computes); it is
equivalent to the cubical path type (Cubical.Data.Equality).
-}
module Sem1 where

open import TT
open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit

import Cubical.Foundations.Prelude as P
import Cubical.Foundations.HLevels as H
import Cubical.Data.Equality as E
import Cubical.Data.Unit as CU

-- the universe: groupoids (in the sense of cubical paths) ------------------------

record Grpd : Set₁ where
  constructor grpd
  field
    ⌞_⌟    : Set
    isGrpd : P.isGroupoid ⌞_⌟
open Grpd

record ⊤₁ : Set₁ where
  constructor tt₁

-- equality toolkit ----------------------------------------------------------------

∙refl : {X : Set}{a b : X}(p : a ≡ b) → p ∙ refl ≡ p
∙refl refl = refl

-- the three algebraic reductions of the coherences (pure J)
lemN : {X : Set}{x y z w v : X}(m : x ≡ y)(n : y ≡ z)(k : x ≡ w)(l : w ≡ z)(e₁ : x ≡ v)(e₂ : w ≡ v)
     → m ∙ n ≡ k ∙ l → k ∙ e₂ ≡ e₁ → sym n ∙ (sym m ∙ e₁) ≡ sym l ∙ e₂
lemN' : {X : Set}{x w z v : X}(k : x ≡ w)(l : w ≡ z)(e₂ : w ≡ v) → sym (k ∙ l) ∙ (k ∙ e₂) ≡ sym l ∙ e₂
lemN' refl l e₂ = refl
lemN refl .(k ∙ l) k l .(k ∙ e₂) e₂ refl refl = lemN' k l e₂

lemA : {X : Set}{x y z w₁ w₂ t u v : X}
       (m : x ≡ y)(n : y ≡ z)(k₁ : x ≡ w₁)(l₁ : w₁ ≡ w₂)(l₂ : w₂ ≡ z)(g : w₂ ≡ u)
       (k₂ : w₁ ≡ t)(h : t ≡ u)(e₁ : x ≡ v)(e₂ : t ≡ v)(f : w₁ ≡ v)
     → m ∙ n ≡ k₁ ∙ (l₁ ∙ l₂) → l₁ ∙ g ≡ k₂ ∙ h → k₂ ∙ e₂ ≡ f → k₁ ∙ f ≡ e₁
     → sym n ∙ (sym m ∙ e₁) ≡ (sym l₂ ∙ g) ∙ (sym h ∙ e₂)
lemA' : {X : Set}{x w z t u v : X}(k₁ : x ≡ w)(l₂ : w ≡ z)(k₂ : w ≡ t)(h : t ≡ u)(e₂ : t ≡ v)
      → sym (k₁ ∙ l₂) ∙ (k₁ ∙ (k₂ ∙ e₂)) ≡ (sym l₂ ∙ (k₂ ∙ h)) ∙ (sym h ∙ e₂)
lemA' refl refl refl refl e₂ = refl
lemA refl .(k₁ ∙ l₂) k₁ refl l₂ .(k₂ ∙ h) k₂ h .(k₁ ∙ (k₂ ∙ e₂)) e₂ .(k₂ ∙ e₂) refl refl refl refl =
  lemA' k₁ l₂ k₂ h e₂

lemW : {X Y : Set}(F : X → Y){x₀ x₁ x₂ x₃ : X}{y₁ y₂ y₃ y₄ : Y}
       (m : x₀ ≡ x₁)(k : x₀ ≡ x₂)(j : x₂ ≡ x₃)(e₁ : x₀ ≡ x₃)
       (u₁ : F x₂ ≡ y₁)(o : y₁ ≡ y₂)(nδ : F x₁ ≡ y₃)(cu : y₃ ≡ y₂)(nδ' : F x₃ ≡ y₄)(g : y₁ ≡ y₄)
     → cong F k ∙ (u₁ ∙ o) ≡ cong F m ∙ (nδ ∙ cu) → cong F j ∙ nδ' ≡ u₁ ∙ g → k ∙ j ≡ e₁
     → sym cu ∙ (sym nδ ∙ cong F (sym m ∙ e₁)) ≡ (sym o ∙ g) ∙ sym nδ'
lemW' : {Y : Set}{y₀ y₂ y₃ y₄ : Y}(nδ : y₀ ≡ y₃)(cu : y₃ ≡ y₂)(g : y₀ ≡ y₄)
      → sym cu ∙ (sym nδ ∙ refl) ≡ (sym (nδ ∙ cu) ∙ g) ∙ sym g
lemW' refl refl refl = refl
lemW F refl refl refl .refl refl .(nδ ∙ cu) nδ cu .g g refl refl refl = lemW' nδ cu g

-- a point, a path to a fixed d, and a value over d
pathK : {B D : Set}{f : B → D}{V : D → Set}{b b' : B}{d : D}{q : f b ≡ d}{q' : f b' ≡ d}{v : V d}
      → (r : b ≡ b') → sym (cong f r) ∙ q ≡ q'
      → _≡_ {A = Σ B (λ b → Σ D (λ d → Σ (f b ≡ d) (λ _ → V d)))} (b , d , q , v) (b' , d , q' , v)
pathK {b = b} {d = d} {v = v} refl s = cong (λ q → b , d , q , v) s

-- groupoids, for the inductive identity type
isGrpdEq : Set → Set
isGrpdEq D = {u v : D}{q q' : u ≡ v}(s s' : q ≡ q') → s ≡ s'

eqIsSet : {D : Set} → P.isGroupoid D → (u v : D) → P.isSet (u ≡ v)
eqIsSet g u v = P.subst P.isSet (E.PathPathEq {x = u} {y = v}) (g u v)

grpdEq : {D : Set} → P.isGroupoid D → isGrpdEq D
grpdEq g {u} {v} {q} {q'} s s' = E.pathToEq (P.subst P.isProp (E.PathPathEq {x = q} {y = q'}) (eqIsSet g u v q q') s s')

-- in a set, 2-paths are unique
set→2prop : {X : Set}{a b : X}(h : (q q' : a ≡ b) → q ≡ q'){q q' : a ≡ b}(w w' : q ≡ q') → w ≡ w'
set→2prop {a = a} {b} h {q} {q'} w w' = canon w ∙ sym (canon w')
  where
    sym∙ : {y : a ≡ b}(t : q ≡ y) → sym t ∙ t ≡ refl
    sym∙ refl = refl
    canon : {y : a ≡ b}(w : q ≡ y) → w ≡ sym (h q q) ∙ h q y
    canon refl = sym (sym∙ (h q q))

cong-∙ : {X Y : Set}(F : X → Y){x y z : X}(r : x ≡ y)(t : y ≡ z) → cong F (r ∙ t) ≡ cong F r ∙ cong F t
cong-∙ F refl t = refl

cong-∘ : {X Y Z : Set}(G : Y → Z)(F : X → Y){x y : X}(r : x ≡ y) → cong G (cong F r) ≡ cong (λ z → G (F z)) r
cong-∘ G F refl = refl

cong-const : {X Y : Set}(y₀ : Y){x x' : X}(r : x ≡ x') → cong (λ _ → y₀) r ≡ refl
cong-const y₀ refl = refl

∙-assoc : {X : Set}{x y z w : X}(p : x ≡ y)(q : y ≡ z)(r : z ≡ w) → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
∙-assoc refl q r = refl

reassoc3 : {X : Set}{x y z w u : X}(a : x ≡ y)(b : y ≡ z)(c : z ≡ w)(d : w ≡ u)
         → a ∙ (b ∙ (c ∙ d)) ≡ (a ∙ (b ∙ c)) ∙ d
reassoc3 refl refl c d = refl

∙sym : {X : Set}{x y : X}(p : x ≡ y) → p ∙ sym p ≡ refl
∙sym refl = refl

-- an idempotent loop is trivial
idem : {X : Set}{x : X}(t : x ≡ x) → t ∙ t ≡ t → t ≡ refl
idem t h = sym (∙refl t) ∙ cong (t ∙_) (sym (∙sym t)) ∙ sym (∙-assoc t t (sym t)) ∙ cong (_∙ sym t) h ∙ ∙sym t

-- projections and images of pathK
pathK-fst : {B D : Set}{f : B → D}{V : D → Set}{b b' : B}{d : D}{q : f b ≡ d}{q' : f b' ≡ d}{v : V d}
            (r : b ≡ b')(s : sym (cong f r) ∙ q ≡ q') → cong fst (pathK {V = V} {v = v} r s) ≡ r
pathK-fst {b = b} {d = d} {v = v} refl s = cong-∘ fst (λ q → b , d , q , v) s ∙ cong-const b s

imgS : {B B' D : Set}{f : B → D}{f' : B' → D}(G : B → B')(H : (b : B) → f' (G b) ≡ f b)
       {b b' : B}{d : D}{q : f b ≡ d}{q' : f b' ≡ d}
       (r : b ≡ b')(s : sym (cong f r) ∙ q ≡ q') → sym (cong f' (cong G r)) ∙ (H b ∙ q) ≡ H b' ∙ q'
imgS G H {b = b} refl s = cong (H b ∙_) s

pathK-img : {B B' D : Set}{f : B → D}{f' : B' → D}{V : D → Set}
            (G : B → B')(H : (b : B) → f' (G b) ≡ f b)
            {b b' : B}{d : D}{q : f b ≡ d}{q' : f b' ≡ d}{v : V d}
            (r : b ≡ b')(s : sym (cong f r) ∙ q ≡ q')
          → cong (λ t → G (fst t) , fst (snd t) , H (fst t) ∙ fst (snd (snd t)) , snd (snd (snd t))) (pathK {V = V} {v = v} r s)
            ≡ pathK {V = V} {v = v} (cong G r) (imgS {f = f} {f'} G H r s)
pathK-img G H {b = b} {d = d} {v = v} refl s =
  cong-∘ (λ t → G (fst t) , fst (snd t) , H (fst t) ∙ fst (snd (snd t)) , snd (snd (snd t))) (λ q → b , d , q , v) s
  ∙ sym (cong-∘ (λ q → G b , d , q , v) (H b ∙_) s)

imgSU : {B B' D D' : Set}{f : B → D}{f' : B' → D'}(G : B → B')(U : D → D')(H : (b : B) → f' (G b) ≡ U (f b))
        {b b' : B}{d : D}{q : f b ≡ d}{q' : f b' ≡ d}
        (r : b ≡ b')(s : sym (cong f r) ∙ q ≡ q') → sym (cong f' (cong G r)) ∙ (H b ∙ cong U q) ≡ H b' ∙ cong U q'
imgSU G U H {b = b} refl s = cong (λ t → H b ∙ cong U t) s

pathK-imgU : {B B' D D' : Set}{f : B → D}{f' : B' → D'}{V' : D' → Set}
             (G : B → B')(U : D → D')(H : (b : B) → f' (G b) ≡ U (f b))
             {b b' : B}{d : D}{q : f b ≡ d}{q' : f b' ≡ d}{v : V' (U d)}
             (r : b ≡ b')(s : sym (cong f r) ∙ q ≡ q')
           → cong (λ t → G (fst t) , U (fst (snd t)) , H (fst t) ∙ cong U (fst (snd (snd t))) , snd (snd (snd t)))
                  (pathK {f = f} {V = λ d → V' (U d)} {v = v} r s)
             ≡ pathK {f = f'} {V = V'} {v = v} (cong G r) (imgSU {f = f} {f'} G U H r s)
pathK-imgU G U H {b = b} {d = d} {v = v} refl s =
  cong-∘ (λ t → G (fst t) , U (fst (snd t)) , H (fst t) ∙ cong U (fst (snd (snd t))) , snd (snd (snd t)))
         (λ q → b , d , q , v) s
  ∙ sym (cong-∘ (λ q → G b , U d , q , v) (λ t → H b ∙ cong U t) s)

compS : {B D : Set}{f : B → D}{b b' b'' : B}{d : D}{q : f b ≡ d}{q' : f b' ≡ d}{q'' : f b'' ≡ d}
        (r : b ≡ b')(r' : b' ≡ b'')(s : sym (cong f r) ∙ q ≡ q')(s' : sym (cong f r') ∙ q' ≡ q'')
      → sym (cong f (r ∙ r')) ∙ q ≡ q''
compS refl refl s s' = s ∙ s'

pathK-comp : {B D : Set}{f : B → D}{V : D → Set}{b b' b'' : B}{d : D}
             {q : f b ≡ d}{q' : f b' ≡ d}{q'' : f b'' ≡ d}{v : V d}
             (r : b ≡ b')(r' : b' ≡ b'')(s : sym (cong f r) ∙ q ≡ q')(s' : sym (cong f r') ∙ q' ≡ q'')
           → pathK {V = V} {v = v} r s ∙ pathK r' s' ≡ pathK (r ∙ r') (compS r r' s s')
pathK-comp {b = b} {d = d} {v = v} refl refl s s' = sym (cong-∙ (λ q → b , d , q , v) s s')

-- two composites of pathKs agree if their base paths do
pathK-∙∙ : {B D : Set}{f : B → D}{V : D → Set}(gD : isGrpdEq D){b b₁ b₃ b' : B}{d : D}
           {q : f b ≡ d}{q₁ : f b₁ ≡ d}{q₃ : f b₃ ≡ d}{q' : f b' ≡ d}{v : V d}
           (r₁ : b ≡ b₁)(r₂ : b₁ ≡ b')(r₃ : b ≡ b₃)(r₄ : b₃ ≡ b')
           (s₁ : sym (cong f r₁) ∙ q ≡ q₁)(s₂ : sym (cong f r₂) ∙ q₁ ≡ q')
           (s₃ : sym (cong f r₃) ∙ q ≡ q₃)(s₄ : sym (cong f r₄) ∙ q₃ ≡ q')
         → r₁ ∙ r₂ ≡ r₃ ∙ r₄
         → pathK {V = V} {v = v} r₁ s₁ ∙ pathK r₂ s₂ ≡ pathK r₃ s₃ ∙ pathK r₄ s₄
pathK-∙∙ gD {b = b} {d = d} {v = v} refl refl refl .refl s₁ s₂ s₃ s₄ refl =
  sym (cong-∙ (λ q → b , d , q , v) s₁ s₂) ∙ cong (cong (λ q → b , d , q , v)) (gD (s₁ ∙ s₂) (s₃ ∙ s₄))
  ∙ cong-∙ (λ q → b , d , q , v) s₃ s₄

-- composing paths of the form pathK
pathK-∙≡ : {B D : Set}{f : B → D}{V : D → Set}(gD : isGrpdEq D){b b' b'' : B}{d : D}
           {q : f b ≡ d}{q' : f b' ≡ d}{q'' : f b'' ≡ d}{v : V d}
           (r : b ≡ b')(r' : b' ≡ b'')(r'' : b ≡ b'')
           (s : sym (cong f r) ∙ q ≡ q')(s' : sym (cong f r') ∙ q' ≡ q'')(s'' : sym (cong f r'') ∙ q ≡ q'')
         → r ∙ r' ≡ r'' → pathK {V = V} {v = v} r s ∙ pathK r' s' ≡ pathK r'' s''
pathK-∙≡ gD {b = b} {d = d} {v = v} refl refl .refl s s' s'' refl =
  sym (cong-∙ (λ q → b , d , q , v) s s') ∙ cong (cong (λ q → b , d , q , v)) (gD (s ∙ s') s'')

-- the interpretation ----------------------------------------------------------------

⟦_⟧C : Con → Set₁
{-# TERMINATING #-}
⟦_⟧T : {Γ : Con} → Ty Γ → ⟦ Γ ⟧C → Set
⟦ • ⟧C = ⊤₁
⟦ Γ ▷ A ⟧C = Σ ⟦ Γ ⟧C (λ γ → ⟦ A ⟧T γ → Grpd)

{-# TERMINATING #-}
⟦_⟧V : {Γ : Con}{A : Ty Γ} → Var Γ A → (γ : ⟦ Γ ⟧C) → ⟦ A ⟧T γ → Set
{-# TERMINATING #-}
⟦_⟧Th : {Γ : Con}{A B : Ty Γ} → Thin A B → {γ : ⟦ Γ ⟧C} → ⟦ A ⟧T γ → ⟦ B ⟧T γ

-- codes act as paths
{-# TERMINATING #-}
≈ : {Γ : Con}{A C : Ty Γ}{σ τ : Thin A C} → Code σ τ → {γ : ⟦ Γ ⟧C}(a : ⟦ A ⟧T γ) → ⟦ σ ⟧Th a ≡ ⟦ τ ⟧Th a

-- composition
{-# TERMINATING #-}
⟦∘⟧ : {Γ : Con}{A B C : Ty Γ}(δ : Thin B C)(σ : Thin A B){γ : ⟦ Γ ⟧C}(a : ⟦ A ⟧T γ)
    → ⟦ δ ∘ σ ⟧Th a ≡ ⟦ δ ⟧Th (⟦ σ ⟧Th a)

-- the path stored by a kept entry
kp : {Γ : Con}{A B C : Ty Γ}(δ : Thin B C)(σ : Thin A B)(δ' : Thin A C) → Code (δ ∘ σ) δ'
   → {γ : ⟦ Γ ⟧C}(a : ⟦ A ⟧T γ) → ⟦ δ ⟧Th (⟦ σ ⟧Th a) ≡ ⟦ δ' ⟧Th a
kp δ σ δ' e a = sym (⟦∘⟧ δ σ a) ∙ ≈ {σ = δ ∘ σ} {δ'} e a

-- the rest of a kept entry, after identifying the source and target variables
tkR : {Γ : Con}{A B C C' : Ty Γ}{x : Var Γ C}{y : Var Γ C'}{γ : ⟦ Γ ⟧C}
      (σ : Thin A B)(δ : Thin B C')(δ' : Thin A C)
    → _≡_ {A = VarΣ Γ} (C , x) (C' , y) → Code (δ ∘ σ) δ'
    → (a : ⟦ A ⟧T γ) → Σ (⟦ C ⟧T γ) (λ d → Σ (⟦ δ' ⟧Th a ≡ d) (λ _ → ⟦ x ⟧V γ d))
    → Σ (⟦ C' ⟧T γ) (λ d → Σ (⟦ δ ⟧Th (⟦ σ ⟧Th a) ≡ d) (λ _ → ⟦ y ⟧V γ d))
tkR σ δ δ' refl e a (d , q , v) = d , kp δ σ δ' e a ∙ q , v

-- semantics of weakening by p
{-# TERMINATING #-}
unwk : {Γ : Con}(A : Ty Γ){B : Ty Γ}{γ : ⟦ Γ ⟧C}{X : ⟦ B ⟧T γ → Grpd}
     → ⟦ wkTy A (p {A = B}) ⟧T (γ , X) → ⟦ A ⟧T γ
{-# TERMINATING #-}
unwk-nat : {Γ : Con}{A C : Ty Γ}(δ : Thin A C){B : Ty Γ}{γ : ⟦ Γ ⟧C}{X : ⟦ B ⟧T γ → Grpd}
           (a : ⟦ wkTy A (p {A = B}) ⟧T (γ , X))
         → unwk C (⟦ wkThin δ p ⟧Th a) ≡ ⟦ δ ⟧Th (unwk A a)

⟦ ε ⟧T γ = ⊤
⟦ ext {B = C} A x δ ⟧T γ = Σ (⟦ A ⟧T γ) (λ a → Σ (⟦ C ⟧T γ) (λ d → Σ (⟦ δ ⟧Th a ≡ d) (λ _ → ⟦ x ⟧V γ d)))

⟦_⟧V {Γ ▷ B} zero (γ , X) b = ⌞ X (unwk B b) ⌟
⟦_⟧V {Γ ▷ B} (suc {A = A} x) (γ , X) b = ⟦ x ⟧V γ (unwk A b)

⟦ tε ⟧Th a = tt
⟦ t-d σ ⟧Th (a , r) = ⟦ σ ⟧Th a
⟦ t-k {x = x} {y = y} {δ = δ} {δ' = δ'} σ ex e ⟧Th (a , r) =
  ⟦ σ ⟧Th a , tkR σ δ δ' (CodeV-sound x y ex) e a r

unwk ε b = tt
unwk (ext {B = C} A x δ) (a , d , q , v) = unwk A a , unwk C d , sym (unwk-nat δ a) ∙ cong (unwk C) q , v

-- the generic coherences (2-cells), by induction ------------------------------------

-- T: code paths compose
{-# TERMINATING #-}
cohT : {Γ : Con}{A C : Ty Γ}(σ τ ρ : Thin A C)(c : Code σ τ)(d : Code τ ρ)(cd : Code σ ρ)
       {γ : ⟦ Γ ⟧C}(a : ⟦ A ⟧T γ)
     → ≈ {σ = σ} {τ} c a ∙ ≈ {σ = τ} {ρ} d a ≡ ≈ {σ = σ} {ρ} cd a

-- composition is natural in codes, on the right and on the left
{-# TERMINATING #-}
cohR : {Γ : Con}{A B C : Ty Γ}(δ : Thin B C)(σ τ : Thin A B)(c : Code σ τ)(c' : Code (δ ∘ σ) (δ ∘ τ))
       {γ : ⟦ Γ ⟧C}(a : ⟦ A ⟧T γ)
     → ⟦∘⟧ δ σ a ∙ cong ⟦ δ ⟧Th (≈ {σ = σ} {τ} c a) ≡ ≈ {σ = δ ∘ σ} {δ ∘ τ} c' a ∙ ⟦∘⟧ δ τ a
{-# TERMINATING #-}
cohL : {Γ : Con}{A B C : Ty Γ}(δ δ₂ : Thin B C)(σ : Thin A B)(c : Code δ δ₂)(c' : Code (δ ∘ σ) (δ₂ ∘ σ))
       {γ : ⟦ Γ ⟧C}(a : ⟦ A ⟧T γ)
     → ⟦∘⟧ δ σ a ∙ ≈ {σ = δ} {δ₂} c (⟦ σ ⟧Th a) ≡ ≈ {σ = δ ∘ σ} {δ₂ ∘ σ} c' a ∙ ⟦∘⟧ δ₂ σ a

-- composition is associative, coherently
{-# TERMINATING #-}
cohAs : {Γ : Con}{A B C D : Ty Γ}(ρ : Thin C D)(δ : Thin B C)(σ : Thin A B)
        (c : Code (ρ ∘ (δ ∘ σ)) ((ρ ∘ δ) ∘ σ)){γ : ⟦ Γ ⟧C}(a : ⟦ A ⟧T γ)
      → ⟦∘⟧ ρ (δ ∘ σ) a ∙ cong ⟦ ρ ⟧Th (⟦∘⟧ δ σ a)
        ≡ ≈ {σ = ρ ∘ (δ ∘ σ)} {(ρ ∘ δ) ∘ σ} c a ∙ (⟦∘⟧ (ρ ∘ δ) σ a ∙ ⟦∘⟧ ρ δ (⟦ σ ⟧Th a))

-- unwk-nat is natural in codes, and compatible with composition
{-# TERMINATING #-}
cohWN : {Γ : Con}{A C : Ty Γ}(ρ ρ' : Thin A C){B₀ : Ty Γ}
        (c : Code ρ ρ')(c' : Code (wkThin ρ (p {A = B₀})) (wkThin ρ' p))
        {γ : ⟦ Γ ⟧C}{X : ⟦ B₀ ⟧T γ → Grpd}(a : ⟦ wkTy A (p {A = B₀}) ⟧T (γ , X))
      → cong (unwk C) (≈ {σ = wkThin ρ p} {wkThin ρ' p} c' a) ∙ unwk-nat ρ' a
        ≡ unwk-nat ρ a ∙ ≈ {σ = ρ} {ρ'} c (unwk A a)
{-# TERMINATING #-}
cohW∘ : {Γ : Con}{A B C : Ty Γ}(δ : Thin B C)(σ : Thin A B){B₀ : Ty Γ}
        (c : Code (wkThin δ (p {A = B₀}) ∘ wkThin σ p) (wkThin (δ ∘ σ) p))
        {γ : ⟦ Γ ⟧C}{X : ⟦ B₀ ⟧T γ → Grpd}(a : ⟦ wkTy A (p {A = B₀}) ⟧T (γ , X))
      → cong (unwk C) (≈ {σ = wkThin δ p ∘ wkThin σ p} {wkThin (δ ∘ σ) p} c a)
        ∙ (unwk-nat (δ ∘ σ) a ∙ ⟦∘⟧ δ σ (unwk A a))
        ≡ cong (unwk C) (⟦∘⟧ (wkThin δ p) (wkThin σ p) a)
          ∙ (unwk-nat δ (⟦ wkThin σ p ⟧Th a) ∙ cong ⟦ δ ⟧Th (unwk-nat σ a))

-- the coherences used by the interpretation (2-cells) -------------------------------

-- N: the stored path is natural in codes
cohN : {Γ : Con}{A B C : Ty Γ}(δ : Thin B C)(σ τ : Thin A B)(δ' : Thin A C)
       (c : Code σ τ)(e : Code (δ ∘ σ) δ')(e' : Code (δ ∘ τ) δ'){γ : ⟦ Γ ⟧C}(a : ⟦ A ⟧T γ)
     → sym (cong ⟦ δ ⟧Th (≈ {σ = σ} {τ} c a)) ∙ kp δ σ δ' e a ≡ kp δ τ δ' e' a
cohN δ σ τ δ' c e e' a =
  lemN (⟦∘⟧ δ σ a) (cong ⟦ δ ⟧Th (≈ {σ = σ} {τ} c a)) (≈ {σ = δ ∘ σ} {δ ∘ τ} c' a) (⟦∘⟧ δ τ a)
       (≈ {σ = δ ∘ σ} {δ'} e a) (≈ {σ = δ ∘ τ} {δ'} e' a)
       (cohR δ σ τ c c' a) (cohT (δ ∘ σ) (δ ∘ τ) δ' c' e' e a)
  where c' = ≡→Code (cong (δ ∘_) (Code-sound σ τ c))

-- A: the stored paths of two keeps compose to the stored path of the composite
cohA : {Γ : Con}{A B C D : Ty Γ}(δC : Thin C D)(δB : Thin B D)(δA : Thin A D)(δ : Thin B C)(σ : Thin A B)
       (q : Code (δC ∘ δ) δB)(e : Code (δB ∘ σ) δA)(e' : Code (δC ∘ (δ ∘ σ)) δA){γ : ⟦ Γ ⟧C}(a : ⟦ A ⟧T γ)
     → sym (cong ⟦ δC ⟧Th (⟦∘⟧ δ σ a)) ∙ kp δC (δ ∘ σ) δA e' a ≡ kp δC δ δB q (⟦ σ ⟧Th a) ∙ kp δB σ δA e a
cohA δC δB δA δ σ q e e' a =
  lemA (⟦∘⟧ δC (δ ∘ σ) a) (cong ⟦ δC ⟧Th (⟦∘⟧ δ σ a))
       (≈ {σ = δC ∘ (δ ∘ σ)} {(δC ∘ δ) ∘ σ} c₁ a) (⟦∘⟧ (δC ∘ δ) σ a) (⟦∘⟧ δC δ (⟦ σ ⟧Th a))
       (≈ {σ = δC ∘ δ} {δB} q (⟦ σ ⟧Th a)) (≈ {σ = (δC ∘ δ) ∘ σ} {δB ∘ σ} c₂ a) (⟦∘⟧ δB σ a)
       (≈ {σ = δC ∘ (δ ∘ σ)} {δA} e' a) (≈ {σ = δB ∘ σ} {δA} e a) (≈ {σ = (δC ∘ δ) ∘ σ} {δA} c₂e a)
       (cohAs δC δ σ c₁ a) (cohL (δC ∘ δ) δB σ q c₂ a)
       (cohT ((δC ∘ δ) ∘ σ) (δB ∘ σ) δA c₂ e c₂e a) (cohT (δC ∘ (δ ∘ σ)) ((δC ∘ δ) ∘ σ) δA c₁ c₂e e' a)
  where c₁ = Code-assoc δC δ σ
        c₂ = Code-∘ (δC ∘ δ) δB σ q
        c₂e = Code-trans ((δC ∘ δ) ∘ σ) (δB ∘ σ) δA c₂ e

-- W: weakening commutes with stored paths
cohW : {Γ : Con}{A B C : Ty Γ}(σ : Thin A B)(δ : Thin B C)(δ' : Thin A C){B₀ : Ty Γ}
       (e : Code (δ ∘ σ) δ')(e₁ : Code (wkThin δ (p {A = B₀}) ∘ wkThin σ p) (wkThin δ' p))
       {γ : ⟦ Γ ⟧C}{X : ⟦ B₀ ⟧T γ → Grpd}(a : ⟦ wkTy A (p {A = B₀}) ⟧T (γ , X))
     → sym (cong ⟦ δ ⟧Th (unwk-nat σ a)) ∙ sym (unwk-nat δ (⟦ wkThin σ p ⟧Th a))
       ∙ cong (unwk C) (kp (wkThin δ p) (wkThin σ p) (wkThin δ' p) e₁ a)
       ≡ kp δ σ δ' e (unwk A a) ∙ sym (unwk-nat δ' a)
cohW {C = C} σ δ δ' e e₁ a =
  lemW (unwk C) (⟦∘⟧ (wkThin δ p) (wkThin σ p) a)
       (≈ {σ = wkThin δ p ∘ wkThin σ p} {wkThin (δ ∘ σ) p} c₃ a) (≈ {σ = wkThin (δ ∘ σ) p} {wkThin δ' p} cwe a)
       (≈ {σ = wkThin δ p ∘ wkThin σ p} {wkThin δ' p} e₁ a)
       (unwk-nat (δ ∘ σ) a) (⟦∘⟧ δ σ (unwk _ a)) (unwk-nat δ (⟦ wkThin σ p ⟧Th a))
       (cong ⟦ δ ⟧Th (unwk-nat σ a)) (unwk-nat δ' a) (≈ {σ = δ ∘ σ} {δ'} e (unwk _ a))
       (cohW∘ δ σ c₃ a) (cohWN (δ ∘ σ) δ' e cwe a)
       (cohT (wkThin δ p ∘ wkThin σ p) (wkThin (δ ∘ σ) p) (wkThin δ' p) c₃ cwe e₁ a)
  where c₃ = Code-wk∘ δ σ p
        cwe = Code-wk (δ ∘ σ) δ' p e

-- the clauses using them ----------------------------------------------------------

-- ≈ on keeps: the stored paths agree by cohN
≈K : {Γ : Con}{A B C C' : Ty Γ}{x : Var Γ C}{y : Var Γ C'}{γ : ⟦ Γ ⟧C}
     (σ τ : Thin A B)(δ : Thin B C')(δ' : Thin A C)(pxy pxy' : _≡_ {A = VarΣ Γ} (C , x) (C' , y))(w : pxy ≡ pxy')
     (c : Code σ τ)(e : Code (δ ∘ σ) δ')(e' : Code (δ ∘ τ) δ')(a : ⟦ A ⟧T γ)
     (r : Σ (⟦ C ⟧T γ) (λ d → Σ (⟦ δ' ⟧Th a ≡ d) (λ _ → ⟦ x ⟧V γ d)))
   → _≡_ {A = ⟦ ext B y δ ⟧T γ} (⟦ σ ⟧Th a , tkR σ δ δ' pxy e a r) (⟦ τ ⟧Th a , tkR τ δ δ' pxy' e' a r)
≈k : {Γ : Con}{A B C C' : Ty Γ}{x : Var Γ C}{y : Var Γ C'}{γ : ⟦ Γ ⟧C}
     {σ τ : Thin A B}(δ : Thin B C')(δ' : Thin A C)(pxy : _≡_ {A = VarΣ Γ} (C , x) (C' , y))
     (c : Code σ τ)(e : Code (δ ∘ σ) δ')(e' : Code (δ ∘ τ) δ')(a : ⟦ A ⟧T γ)
     (r : Σ (⟦ C ⟧T γ) (λ d → Σ (⟦ δ' ⟧Th a ≡ d) (λ _ → ⟦ x ⟧V γ d)))
   → _≡_ {A = ⟦ ext B y δ ⟧T γ} (⟦ σ ⟧Th a , tkR σ δ δ' pxy e a r) (⟦ τ ⟧Th a , tkR τ δ δ' pxy e' a r)
≈k {σ = σ} {τ} δ δ' refl c e e' a (d , q , v) =
  pathK (≈ {σ = σ} {τ} c a) (sym (∙-assoc (sym (cong ⟦ δ ⟧Th (≈ {σ = σ} {τ} c a))) (kp δ σ δ' e a) q)
                             ∙ cong (_∙ q) (cohN δ σ τ δ' c e e' a))

≈K σ τ δ δ' pxy pxy' w c e e' a r =
  subst (λ q → _≡_ {A = ⟦ ext _ _ δ ⟧T _} (⟦ σ ⟧Th a , tkR σ δ δ' pxy e a r)
                                          (⟦ τ ⟧Th a , tkR τ δ δ' q e' a r))
        w (≈k δ δ' pxy c e e' a r)

≈ {σ = tε} {tε} c a = refl
≈ {σ = t-d σ} {t-d τ} c (a , r) = ≈ {σ = σ} {τ} c a
≈ {σ = t-k {x = x} {y} {δ} {δ'} σ ex e} {t-k τ ex' e'} c (a , r) =
  ≈K σ τ δ δ' (CodeV-sound x y ex) (CodeV-sound x y ex') (VarΣ-set _ _) c e e' a r
≈ {σ = t-d σ} {t-k τ _ _} () a
≈ {σ = t-k σ _ _} {t-d τ} () a

-- composition of two keeps: the stored paths agree by cohA
comp-k : {Γ : Con}{A B C D₁ D₂ D₃ : Ty Γ}{x : Var Γ D₁}{y : Var Γ D₂}{z : Var Γ D₃}{γ : ⟦ Γ ⟧C}
         (δ : Thin B C)(σ : Thin A B)(δC : Thin C D₃)(δB : Thin B D₂)(δA : Thin A D₁)
         (pxy : _≡_ {A = VarΣ Γ} (D₁ , x) (D₂ , y))(pyz : _≡_ {A = VarΣ Γ} (D₂ , y) (D₃ , z))
         (pxz : _≡_ {A = VarΣ Γ} (D₁ , x) (D₃ , z))
         (q : Code (δC ∘ δ) δB)(e : Code (δB ∘ σ) δA)(e' : Code (δC ∘ (δ ∘ σ)) δA)
         (a : ⟦ A ⟧T γ)(r : Σ (⟦ D₁ ⟧T γ) (λ d → Σ (⟦ δA ⟧Th a ≡ d) (λ _ → ⟦ x ⟧V γ d)))
       → _≡_ {A = ⟦ ext C z δC ⟧T γ}
           (⟦ δ ∘ σ ⟧Th a , tkR (δ ∘ σ) δC δA pxz e' a r)
           (⟦ δ ⟧Th (⟦ σ ⟧Th a) , tkR δ δC δB pyz q (⟦ σ ⟧Th a) (tkR σ δB δA pxy e a r))
comp-k₀ : {Γ : Con}{A B C D : Ty Γ}{x : Var Γ D}{γ : ⟦ Γ ⟧C}
          (δ : Thin B C)(σ : Thin A B)(δC : Thin C D)(δB : Thin B D)(δA : Thin A D)
          (q : Code (δC ∘ δ) δB)(e : Code (δB ∘ σ) δA)(e' : Code (δC ∘ (δ ∘ σ)) δA)
          (a : ⟦ A ⟧T γ)(r : Σ (⟦ D ⟧T γ) (λ d → Σ (⟦ δA ⟧Th a ≡ d) (λ _ → ⟦ x ⟧V γ d)))
        → _≡_ {A = ⟦ ext C x δC ⟧T γ}
            (⟦ δ ∘ σ ⟧Th a , tkR (δ ∘ σ) δC δA refl e' a r)
            (⟦ δ ⟧Th (⟦ σ ⟧Th a) , tkR δ δC δB refl q (⟦ σ ⟧Th a) (tkR σ δB δA refl e a r))
comp-k₀ δ σ δC δB δA q e e' a (d , q₀ , v) =
  pathK (⟦∘⟧ δ σ a)
        (sym (∙-assoc (sym (cong ⟦ δC ⟧Th (⟦∘⟧ δ σ a))) (kp δC (δ ∘ σ) δA e' a) q₀)
         ∙ cong (_∙ q₀) (cohA δC δB δA δ σ q e e' a)
         ∙ ∙-assoc (kp δC δ δB q (⟦ σ ⟧Th a)) (kp δB σ δA e a) q₀)

comp-k {x = x} {γ = γ} δ σ δC δB δA refl refl pxz q e e' a r =
  subst (λ w → _≡_ {A = ⟦ ext _ x δC ⟧T γ}
                   (⟦ δ ∘ σ ⟧Th a , tkR (δ ∘ σ) δC δA w e' a r)
                   (⟦ δ ⟧Th (⟦ σ ⟧Th a) , tkR δ δC δB refl q (⟦ σ ⟧Th a) (tkR σ δB δA refl e a r)))
        (VarΣ-set refl pxz)
        (comp-k₀ δ σ δC δB δA q e e' a r)

⟦∘⟧ δ tε a = refl
⟦∘⟧ δ (t-d σ) (a , r) = ⟦∘⟧ δ σ a
⟦∘⟧ (t-d δ) (t-k σ ex e) (a , r) = ⟦∘⟧ δ σ a
⟦∘⟧ (t-k {x = y} {y = z} {δ = δC} {δ' = δB} δ ey q) (t-k {x = x} {δ' = δA} σ ex e) (a , r) =
  comp-k δ σ δC δB δA (CodeV-sound x y ex) (CodeV-sound y z ey)
         (CodeV-sound x z (CodeV-trans x y z ex ey)) q e _ a r

-- weakening a keep: the stored paths agree by cohW
uk : {Γ : Con}{A B C C' B₀ : Ty Γ}{x : Var Γ C}{y : Var Γ C'}
     (σ : Thin A B)(δ : Thin B C')(δ' : Thin A C)(p₀ : _≡_ {A = VarΣ Γ} (C , x) (C' , y))
     (e : Code (δ ∘ σ) δ')(e₁ : Code (wkThin δ (p {A = B₀}) ∘ wkThin σ p) (wkThin δ' p))
     {γ : ⟦ Γ ⟧C}{X : ⟦ B₀ ⟧T γ → Grpd}(a : ⟦ wkTy A (p {A = B₀}) ⟧T (γ , X))
     (r : Σ (⟦ wkTy C (p {A = B₀}) ⟧T (γ , X)) (λ d → Σ (⟦ wkThin δ' p ⟧Th a ≡ d) (λ _ → ⟦ x ⟧V γ (unwk C d))))
   → _≡_ {A = ⟦ ext B y δ ⟧T γ}
       (unwk (ext B y δ) (⟦ wkThin σ p ⟧Th a , tkR (wkThin σ p) (wkThin δ p) (wkThin δ' p) (cong (sucΣ {B = B₀}) p₀) e₁ a r))
       (⟦ σ ⟧Th (unwk A a) ,
        tkR σ δ δ' p₀ e (unwk A a) (unwk C (fst r) , sym (unwk-nat δ' a) ∙ cong (unwk C) (fst (snd r)) , snd (snd r)))
uk {C = C} σ δ δ' refl e e₁ a (d , q , v) =
  pathK (unwk-nat σ a)
        (cong (λ t → sym (cong ⟦ δ ⟧Th (unwk-nat σ a)) ∙ sym (unwk-nat δ (⟦ wkThin σ p ⟧Th a)) ∙ t)
              (cong-∙ (unwk C) (kp (wkThin δ p) (wkThin σ p) (wkThin δ' p) e₁ a) q)
         ∙ reassoc3 (sym (cong ⟦ δ ⟧Th (unwk-nat σ a))) (sym (unwk-nat δ (⟦ wkThin σ p ⟧Th a)))
                    (cong (unwk C) (kp (wkThin δ p) (wkThin σ p) (wkThin δ' p) e₁ a)) (cong (unwk C) q)
         ∙ cong (_∙ cong (unwk C) q) (cohW σ δ δ' e e₁ a)
         ∙ ∙-assoc (kp δ σ δ' e (unwk _ a)) (sym (unwk-nat δ' a)) (cong (unwk C) q))

unwk-nat tε a = refl
unwk-nat (t-d σ) (a , r) = unwk-nat σ a
unwk-nat (t-k {x = x} {y = y} {δ = δ} {δ' = δ'} σ ex e) (a , r) = uk σ δ δ' (CodeV-sound x y ex) e _ a r

-- the semantic types are groupoids
{-# TERMINATING #-}
isGrpdT : {Γ : Con}(A : Ty Γ)(γ : ⟦ Γ ⟧C) → P.isGroupoid (⟦ A ⟧T γ)
{-# TERMINATING #-}
isGrpdV : {Γ : Con}{A : Ty Γ}(x : Var Γ A)(γ : ⟦ Γ ⟧C)(a : ⟦ A ⟧T γ) → P.isGroupoid (⟦ x ⟧V γ a)
isGrpdT ε γ = H.isSet→isGroupoid CU.isSetUnit
isGrpdT (ext {B = C} A x δ) γ =
  H.isGroupoidΣ (isGrpdT A γ) λ a → H.isGroupoidΣ (isGrpdT C γ) λ d →
    H.isGroupoidΣ (H.isSet→isGroupoid (eqIsSet (isGrpdT C γ) (⟦ δ ⟧Th a) d)) λ _ → isGrpdV x γ d
isGrpdV {Γ ▷ B} zero (γ , X) b = isGrpd (X (unwk B b))
isGrpdV {Γ ▷ B} (suc {A = A} x) (γ , X) b = isGrpdV x γ (unwk A b)

-- T on keeps
TK : {Γ : Con}{A B C C' : Ty Γ}{x : Var Γ C}{y : Var Γ C'}{γ : ⟦ Γ ⟧C}
     (σ τ ρ : Thin A B)(δ : Thin B C')(δ' : Thin A C)
     (p₁ p₂ p₃ : _≡_ {A = VarΣ Γ} (C , x) (C' , y))(w₁₂ : p₁ ≡ p₂)(w₂₃ : p₂ ≡ p₃)(w₁₃ : p₁ ≡ p₃)
     (c : Code σ τ)(d : Code τ ρ)(cd : Code σ ρ)
     (e : Code (δ ∘ σ) δ')(e' : Code (δ ∘ τ) δ')(e'' : Code (δ ∘ ρ) δ')(a : ⟦ A ⟧T γ)
     (r : Σ (⟦ C ⟧T γ) (λ d → Σ (⟦ δ' ⟧Th a ≡ d) (λ _ → ⟦ x ⟧V γ d)))
   → ≈K σ τ δ δ' p₁ p₂ w₁₂ c e e' a r ∙ ≈K τ ρ δ δ' p₂ p₃ w₂₃ d e' e'' a r ≡ ≈K σ ρ δ δ' p₁ p₃ w₁₃ cd e e'' a r
TK₀ : {Γ : Con}{A B C : Ty Γ}{x : Var Γ C}{γ : ⟦ Γ ⟧C}
      (σ τ ρ : Thin A B)(δ : Thin B C)(δ' : Thin A C)
      (c : Code σ τ)(d : Code τ ρ)(cd : Code σ ρ)
      (e : Code (δ ∘ σ) δ')(e' : Code (δ ∘ τ) δ')(e'' : Code (δ ∘ ρ) δ')(a : ⟦ A ⟧T γ)
      (r : Σ (⟦ C ⟧T γ) (λ d → Σ (⟦ δ' ⟧Th a ≡ d) (λ _ → ⟦ x ⟧V γ d)))
    → ≈K σ τ δ δ' refl refl refl c e e' a r ∙ ≈K τ ρ δ δ' refl refl refl d e' e'' a r ≡ ≈K σ ρ δ δ' refl refl refl cd e e'' a r
TK₀ {C = C} {γ = γ} σ τ ρ δ δ' c d cd e e' e'' a (d₀ , refl , v) =
  pathK-∙≡ (grpdEq (isGrpdT C γ)) (≈ {σ = σ} {τ} c a) (≈ {σ = τ} {ρ} d a) (≈ {σ = σ} {ρ} cd a) _ _ _
           (cohT σ τ ρ c d cd a)
TK σ τ ρ δ δ' refl .refl .refl refl refl w₁₃ c d cd e e' e'' a r =
  subst (λ w → ≈K σ τ δ δ' refl refl refl c e e' a r ∙ ≈K τ ρ δ δ' refl refl refl d e' e'' a r
               ≡ ≈K σ ρ δ δ' refl refl w cd e e'' a r)
        (set→2prop VarΣ-set refl w₁₃)
        (TK₀ σ τ ρ δ δ' c d cd e e' e'' a r)

cohT tε tε tε c d cd a = refl
cohT (t-d σ) (t-d τ) (t-d ρ) c d cd (a , r) = cohT σ τ ρ c d cd a
cohT (t-k {x = x} {y} {δ} {δ'} σ ex e) (t-k τ ex' e') (t-k ρ ex'' e'') c d cd (a , r) =
  TK σ τ ρ δ δ' (CodeV-sound x y ex) (CodeV-sound x y ex') (CodeV-sound x y ex'')
     (VarΣ-set _ _) (VarΣ-set _ _) (VarΣ-set _ _) c d cd e e' e'' a r
-- the code path of a loop is trivial
refl≈ : {Γ : Con}{A C : Ty Γ}(σ : Thin A C)(c : Code σ σ){γ : ⟦ Γ ⟧C}(a : ⟦ A ⟧T γ) → ≈ {σ = σ} {σ} c a ≡ refl
refl≈ σ c a = idem (≈ {σ = σ} {σ} c a) (cohT σ σ σ c c c a)

-- the base of ≈ on a keep is ≈ on the kept thinning
fstK : {Γ : Con}{A B C C' : Ty Γ}{x : Var Γ C}{y : Var Γ C'}{γ : ⟦ Γ ⟧C}
       (σ τ : Thin A B)(δ : Thin B C')(δ' : Thin A C)(pxy pxy' : _≡_ {A = VarΣ Γ} (C , x) (C' , y))(w : pxy ≡ pxy')
       (c : Code σ τ)(e : Code (δ ∘ σ) δ')(e' : Code (δ ∘ τ) δ')(a : ⟦ A ⟧T γ)
       (r : Σ (⟦ C ⟧T γ) (λ d → Σ (⟦ δ' ⟧Th a ≡ d) (λ _ → ⟦ x ⟧V γ d)))
     → cong fst (≈K σ τ δ δ' pxy pxy' w c e e' a r) ≡ ≈ {σ = σ} {τ} c a
fstK σ τ δ δ' refl .refl refl c e e' a (d , refl , v) = pathK-fst (≈ {σ = σ} {τ} c a) _

-- cohR for a keep after a keep
RK : {Γ : Con}{A B C D₁ D₂ D₃ : Ty Γ}{x : Var Γ D₁}{y : Var Γ D₂}{z : Var Γ D₃}{γ : ⟦ Γ ⟧C}
     (δ : Thin B C)(σ τ : Thin A B)(δC : Thin C D₃)(δB : Thin B D₂)(δA : Thin A D₁)
     (pxy pxy' : _≡_ {A = VarΣ Γ} (D₁ , x) (D₂ , y))(w : pxy ≡ pxy')(pyz : _≡_ {A = VarΣ Γ} (D₂ , y) (D₃ , z))
     (pxz pxz' : _≡_ {A = VarΣ Γ} (D₁ , x) (D₃ , z))(w' : pxz ≡ pxz')
     (c : Code σ τ)(c' : Code (δ ∘ σ) (δ ∘ τ))(q : Code (δC ∘ δ) δB)(e : Code (δB ∘ σ) δA)(e' : Code (δB ∘ τ) δA)
     (kc : Code (δC ∘ (δ ∘ σ)) δA)(kc' : Code (δC ∘ (δ ∘ τ)) δA)
     (a : ⟦ A ⟧T γ)(r : Σ (⟦ D₁ ⟧T γ) (λ d → Σ (⟦ δA ⟧Th a ≡ d) (λ _ → ⟦ x ⟧V γ d)))
   → comp-k δ σ δC δB δA pxy pyz pxz q e kc a r
     ∙ cong (λ t → ⟦ δ ⟧Th (fst t) , tkR δ δC δB pyz q (fst t) (snd t)) (≈K σ τ δB δA pxy pxy' w c e e' a r)
     ≡ ≈K (δ ∘ σ) (δ ∘ τ) δC δA pxz pxz' w' c' kc kc' a r ∙ comp-k δ τ δC δB δA pxy' pyz pxz' q e' kc' a r
RK₀ : {Γ : Con}{A B C D : Ty Γ}{x : Var Γ D}{γ : ⟦ Γ ⟧C}
      (δ : Thin B C)(σ τ : Thin A B)(δC : Thin C D)(δB : Thin B D)(δA : Thin A D)
      (c : Code σ τ)(c' : Code (δ ∘ σ) (δ ∘ τ))(q : Code (δC ∘ δ) δB)(e : Code (δB ∘ σ) δA)(e' : Code (δB ∘ τ) δA)
      (kc : Code (δC ∘ (δ ∘ σ)) δA)(kc' : Code (δC ∘ (δ ∘ τ)) δA)
      (a : ⟦ A ⟧T γ)(r : Σ (⟦ D ⟧T γ) (λ d → Σ (⟦ δA ⟧Th a ≡ d) (λ _ → ⟦ x ⟧V γ d)))
    → comp-k₀ δ σ δC δB δA q e kc a r
      ∙ cong (λ t → ⟦ δ ⟧Th (fst t) , tkR δ δC δB refl q (fst t) (snd t)) (≈k {σ = σ} {τ} δB δA refl c e e' a r)
      ≡ ≈k {σ = δ ∘ σ} {δ ∘ τ} δC δA refl c' kc kc' a r ∙ comp-k₀ δ τ δC δB δA q e' kc' a r
RK₀ {D = D} {γ = γ} δ σ τ δC δB δA c c' q e e' kc kc' a (d , refl , v) =
  cong (comp-k₀ δ σ δC δB δA q e kc a (d , refl , v) ∙_)
       (pathK-img ⟦ δ ⟧Th (kp δC δ δB q) (≈ {σ = σ} {τ} c a) _)
  ∙ pathK-∙∙ (grpdEq (isGrpdT D γ)) (⟦∘⟧ δ σ a) (cong ⟦ δ ⟧Th (≈ {σ = σ} {τ} c a))
             (≈ {σ = δ ∘ σ} {δ ∘ τ} c' a) (⟦∘⟧ δ τ a) _ _ _ _ (cohR δ σ τ c c' a)
RK δ σ τ δC δB δA refl .refl refl refl pxz .pxz refl c c' q e e' kc kc' a r =
  J-pxz pxz (VarΣ-set refl pxz)
  where
    J-pxz : (pxz : _) (w₀ : refl ≡ pxz)
          → subst (λ w → _≡_ {A = ⟦ ext _ _ δC ⟧T _} (⟦ δ ∘ σ ⟧Th a , tkR (δ ∘ σ) δC δA w kc a r)
                                (⟦ δ ⟧Th (⟦ σ ⟧Th a) , tkR δ δC δB refl q (⟦ σ ⟧Th a) (tkR σ δB δA refl e a r)))
                  w₀ (comp-k₀ δ σ δC δB δA q e kc a r)
            ∙ cong (λ t → ⟦ δ ⟧Th (fst t) , tkR δ δC δB refl q (fst t) (snd t)) (≈K σ τ δB δA refl refl refl c e e' a r)
            ≡ ≈K (δ ∘ σ) (δ ∘ τ) δC δA pxz pxz refl c' kc kc' a r
              ∙ subst (λ w → _≡_ {A = ⟦ ext _ _ δC ⟧T _} (⟦ δ ∘ τ ⟧Th a , tkR (δ ∘ τ) δC δA w kc' a r)
                                  (⟦ δ ⟧Th (⟦ τ ⟧Th a) , tkR δ δC δB refl q (⟦ τ ⟧Th a) (tkR τ δB δA refl e' a r)))
                      w₀ (comp-k₀ δ τ δC δB δA q e' kc' a r)
    J-pxz .refl refl = RK₀ δ σ τ δC δB δA c c' q e e' kc kc' a r

cohR δ tε tε c c' a = sym (∙refl (≈ {σ = δ} {δ} c' a) ∙ refl≈ δ c' a)
cohR δ (t-d σ) (t-d τ) c c' (a , r) = cohR δ σ τ c c' a
cohR (t-d δ) (t-k {δ = δB} {δ' = δA} σ ex e) (t-k τ ex' e') c c' (a , r) =
  cong (⟦∘⟧ δ σ a ∙_)
       (sym (cong-∘ ⟦ δ ⟧Th fst (≈K σ τ δB δA _ _ (VarΣ-set _ _) c e e' a r))
        ∙ cong (cong ⟦ δ ⟧Th) (fstK σ τ δB δA _ _ (VarΣ-set _ _) c e e' a r))
  ∙ cohR δ σ τ c c' a
cohR (t-k {x = y} {y = z} {δ = δC} {δ' = δB} δ ey q) (t-k {x = x} {δ' = δA} σ ex e) (t-k τ ex' e') c c' (a , r) =
  RK δ σ τ δC δB δA (CodeV-sound x y ex) (CodeV-sound x y ex') (VarΣ-set _ _) (CodeV-sound y z ey)
     (CodeV-sound x z (CodeV-trans x y z ex ey)) (CodeV-sound x z (CodeV-trans x y z ex' ey)) (VarΣ-set _ _)
     c c' q e e' _ _ a r
≈-irr : {Γ : Con}{A C : Ty Γ}(σ τ : Thin A C)(c c' : Code σ τ){γ : ⟦ Γ ⟧C}(a : ⟦ A ⟧T γ)
      → ≈ {σ = σ} {τ} c a ≡ ≈ {σ = σ} {τ} c' a
≈-irr σ τ c c' a = cong (λ k → ≈ {σ = σ} {τ} k a) (Code-prop σ τ c c')

-- cohL for a keep after a keep
LK : {Γ : Con}{A B C D₁ D₂ D₃ : Ty Γ}{x : Var Γ D₁}{y : Var Γ D₂}{z : Var Γ D₃}{γ : ⟦ Γ ⟧C}
     (δ δ₂ : Thin B C)(σ : Thin A B)(δC : Thin C D₃)(δB : Thin B D₂)(δA : Thin A D₁)
     (pxy : _≡_ {A = VarΣ Γ} (D₁ , x) (D₂ , y))(pyz pyz' : _≡_ {A = VarΣ Γ} (D₂ , y) (D₃ , z))(w : pyz ≡ pyz')
     (pxz pxz' : _≡_ {A = VarΣ Γ} (D₁ , x) (D₃ , z))(w' : pxz ≡ pxz')
     (c : Code δ δ₂)(c' : Code (δ ∘ σ) (δ₂ ∘ σ))(q : Code (δC ∘ δ) δB)(q' : Code (δC ∘ δ₂) δB)(e : Code (δB ∘ σ) δA)
     (kc : Code (δC ∘ (δ ∘ σ)) δA)(kc' : Code (δC ∘ (δ₂ ∘ σ)) δA)
     (a : ⟦ A ⟧T γ)(r : Σ (⟦ D₁ ⟧T γ) (λ d → Σ (⟦ δA ⟧Th a ≡ d) (λ _ → ⟦ x ⟧V γ d)))
   → comp-k δ σ δC δB δA pxy pyz pxz q e kc a r
     ∙ ≈K δ δ₂ δC δB pyz pyz' w c q q' (⟦ σ ⟧Th a) (tkR σ δB δA pxy e a r)
     ≡ ≈K (δ ∘ σ) (δ₂ ∘ σ) δC δA pxz pxz' w' c' kc kc' a r ∙ comp-k δ₂ σ δC δB δA pxy pyz' pxz' q' e kc' a r
LK₀ : {Γ : Con}{A B C D : Ty Γ}{x : Var Γ D}{γ : ⟦ Γ ⟧C}
      (δ δ₂ : Thin B C)(σ : Thin A B)(δC : Thin C D)(δB : Thin B D)(δA : Thin A D)
      (c : Code δ δ₂)(c' : Code (δ ∘ σ) (δ₂ ∘ σ))(q : Code (δC ∘ δ) δB)(q' : Code (δC ∘ δ₂) δB)(e : Code (δB ∘ σ) δA)
      (kc : Code (δC ∘ (δ ∘ σ)) δA)(kc' : Code (δC ∘ (δ₂ ∘ σ)) δA)
      (a : ⟦ A ⟧T γ)(r : Σ (⟦ D ⟧T γ) (λ d → Σ (⟦ δA ⟧Th a ≡ d) (λ _ → ⟦ x ⟧V γ d)))
    → comp-k₀ δ σ δC δB δA q e kc a r
      ∙ ≈k {σ = δ} {δ₂} δC δB refl c q q' (⟦ σ ⟧Th a) (tkR σ δB δA refl e a r)
      ≡ ≈k {σ = δ ∘ σ} {δ₂ ∘ σ} δC δA refl c' kc kc' a r ∙ comp-k₀ δ₂ σ δC δB δA q' e kc' a r
LK₀ {D = D} {γ = γ} δ δ₂ σ δC δB δA c c' q q' e kc kc' a (d , q₀ , v) =
  pathK-∙∙ (grpdEq (isGrpdT D γ)) (⟦∘⟧ δ σ a) (≈ {σ = δ} {δ₂} c (⟦ σ ⟧Th a))
           (≈ {σ = δ ∘ σ} {δ₂ ∘ σ} c' a) (⟦∘⟧ δ₂ σ a) _ _ _ _ (cohL δ δ₂ σ c c' a)
LK δ δ₂ σ δC δB δA refl refl .refl refl pxz .pxz refl c c' q q' e kc kc' a r = J-pxz pxz (VarΣ-set refl pxz)
  where
    J-pxz : (pxz : _) (w₀ : refl ≡ pxz)
          → subst (λ w → _≡_ {A = ⟦ ext _ _ δC ⟧T _} (⟦ δ ∘ σ ⟧Th a , tkR (δ ∘ σ) δC δA w kc a r)
                                (⟦ δ ⟧Th (⟦ σ ⟧Th a) , tkR δ δC δB refl q (⟦ σ ⟧Th a) (tkR σ δB δA refl e a r)))
                  w₀ (comp-k₀ δ σ δC δB δA q e kc a r)
            ∙ ≈K δ δ₂ δC δB refl refl refl c q q' (⟦ σ ⟧Th a) (tkR σ δB δA refl e a r)
            ≡ ≈K (δ ∘ σ) (δ₂ ∘ σ) δC δA pxz pxz refl c' kc kc' a r
              ∙ subst (λ w → _≡_ {A = ⟦ ext _ _ δC ⟧T _} (⟦ δ₂ ∘ σ ⟧Th a , tkR (δ₂ ∘ σ) δC δA w kc' a r)
                                  (⟦ δ₂ ⟧Th (⟦ σ ⟧Th a) , tkR δ₂ δC δB refl q' (⟦ σ ⟧Th a) (tkR σ δB δA refl e a r)))
                      w₀ (comp-k₀ δ₂ σ δC δB δA q' e kc' a r)
    J-pxz .refl refl = LK₀ δ δ₂ σ δC δB δA c c' q q' e kc kc' a r

cohL δ δ₂ tε c c' a = ≈-irr δ δ₂ c c' a ∙ sym (∙refl (≈ {σ = δ} {δ₂} c' a))
cohL δ δ₂ (t-d σ) c c' (a , r) = cohL δ δ₂ σ c c' a
cohL (t-d δ) (t-d δ₂) (t-k σ ex e) c c' (a , r) = cohL δ δ₂ σ c c' a
cohL (t-k {x = y} {y = z} {δ = δC} {δ' = δB} δ ey q) (t-k δ₂ ey' q') (t-k {x = x} {δ' = δA} σ ex e) c c' (a , r) =
  LK δ δ₂ σ δC δB δA (CodeV-sound x y ex) (CodeV-sound y z ey) (CodeV-sound y z ey') (VarΣ-set _ _)
     (CodeV-sound x z (CodeV-trans x y z ex ey)) (CodeV-sound x z (CodeV-trans x y z ex ey')) (VarΣ-set _ _)
     c c' q q' e _ _ a r
-- the base of a composite of keeps
fstC : {Γ : Con}{A B C D₁ D₂ D₃ : Ty Γ}{x : Var Γ D₁}{y : Var Γ D₂}{z : Var Γ D₃}{γ : ⟦ Γ ⟧C}
       (δ : Thin B C)(σ : Thin A B)(δC : Thin C D₃)(δB : Thin B D₂)(δA : Thin A D₁)
       (pxy : _≡_ {A = VarΣ Γ} (D₁ , x) (D₂ , y))(pyz : _≡_ {A = VarΣ Γ} (D₂ , y) (D₃ , z))
       (pxz : _≡_ {A = VarΣ Γ} (D₁ , x) (D₃ , z))
       (q : Code (δC ∘ δ) δB)(e : Code (δB ∘ σ) δA)(e' : Code (δC ∘ (δ ∘ σ)) δA)
       (a : ⟦ A ⟧T γ)(r : Σ (⟦ D₁ ⟧T γ) (λ d → Σ (⟦ δA ⟧Th a ≡ d) (λ _ → ⟦ x ⟧V γ d)))
     → cong fst (comp-k δ σ δC δB δA pxy pyz pxz q e e' a r) ≡ ⟦∘⟧ δ σ a
fstC δ σ δC δB δA refl refl pxz q e e' a r = J-pxz pxz (VarΣ-set refl pxz)
  where
    J-pxz : (pxz : _) (w₀ : refl ≡ pxz)
          → cong fst (subst (λ w → _≡_ {A = ⟦ ext _ _ δC ⟧T _} (⟦ δ ∘ σ ⟧Th a , tkR (δ ∘ σ) δC δA w e' a r)
                                (⟦ δ ⟧Th (⟦ σ ⟧Th a) , tkR δ δC δB refl q (⟦ σ ⟧Th a) (tkR σ δB δA refl e a r)))
                             w₀ (comp-k₀ δ σ δC δB δA q e e' a r))
            ≡ ⟦∘⟧ δ σ a
    J-pxz .refl refl = pathK-fst (⟦∘⟧ δ σ a) _

-- cohAs for three keeps, in stages: identify the generating variable
-- paths, then the composite ones (loops), then compute
module AKs {Γ : Con}{A B C Dt D : Ty Γ}{x : Var Γ D}{γ : ⟦ Γ ⟧C}
           (ρ : Thin C Dt)(δ : Thin B C)(σ : Thin A B)(δD : Thin Dt D)(δC : Thin C D)(δB : Thin B D)(δA : Thin A D)
           (qq : Code (δD ∘ ρ) δC)(q : Code (δC ∘ δ) δB)(e : Code (δB ∘ σ) δA)
           (c : Code (ρ ∘ (δ ∘ σ)) ((ρ ∘ δ) ∘ σ))
           (kc₁ : Code (δC ∘ (δ ∘ σ)) δA)(kc₂ : Code (δD ∘ (ρ ∘ (δ ∘ σ))) δA)
           (kc₃ : Code (δD ∘ ((ρ ∘ δ) ∘ σ)) δA)(kc₄ : Code (δD ∘ (ρ ∘ δ)) δB)
           (a : ⟦ A ⟧T γ)(r : Σ (⟦ D ⟧T γ) (λ d → Σ (⟦ δA ⟧Th a ≡ d) (λ _ → ⟦ x ⟧V γ d))) where

  ρ' : (b : ⟦ C ⟧T γ) → _ → _
  ρ' = λ b r' → ⟦ ρ ⟧Th b , tkR ρ δD δC refl qq b r'

  AK₀ : comp-k₀ ρ (δ ∘ σ) δD δC δA qq kc₁ kc₂ a r
        ∙ cong (λ t → ρ' (fst t) (snd t)) (comp-k₀ δ σ δC δB δA q e kc₁ a r)
        ≡ ≈k {σ = ρ ∘ (δ ∘ σ)} {(ρ ∘ δ) ∘ σ} δD δA refl c kc₂ kc₃ a r
          ∙ (comp-k₀ (ρ ∘ δ) σ δD δB δA kc₄ e kc₃ a r
             ∙ comp-k₀ ρ δ δD δC δB qq q kc₄ (⟦ σ ⟧Th a) (tkR σ δB δA refl e a r))
  AK₀ =
    cong (comp-k₀ ρ (δ ∘ σ) δD δC δA qq kc₁ kc₂ a r ∙_) (pathK-img ⟦ ρ ⟧Th (kp δD ρ δC qq) (⟦∘⟧ δ σ a) _)
    ∙ pathK-∙∙ (grpdEq (isGrpdT D γ)) (⟦∘⟧ ρ (δ ∘ σ) a) (cong ⟦ ρ ⟧Th (⟦∘⟧ δ σ a))
               (≈ {σ = ρ ∘ (δ ∘ σ)} {(ρ ∘ δ) ∘ σ} c a) (⟦∘⟧ (ρ ∘ δ) σ a ∙ ⟦∘⟧ ρ δ (⟦ σ ⟧Th a)) _ _ _ _
               (cohAs ρ δ σ c a)
    ∙ cong (≈k {σ = ρ ∘ (δ ∘ σ)} {(ρ ∘ δ) ∘ σ} δD δA refl c kc₂ kc₃ a r ∙_)
           (sym (pathK-comp (⟦∘⟧ (ρ ∘ δ) σ a) (⟦∘⟧ ρ δ (⟦ σ ⟧Th a)) _ _))

  -- the loops pxw, pxw' (and the witness w between them)
  AK₂ : (pxw pxw' : _≡_ {A = VarΣ Γ} (D , x) (D , x))(w₃ : refl ≡ pxw)(w₄ : refl ≡ pxw')(w : pxw ≡ pxw')
      → subst (λ w → _≡_ {A = ⟦ ext _ _ δD ⟧T _} (⟦ ρ ∘ (δ ∘ σ) ⟧Th a , tkR (ρ ∘ (δ ∘ σ)) δD δA w kc₂ a r)
                       (⟦ ρ ⟧Th (⟦ δ ∘ σ ⟧Th a) , tkR ρ δD δC refl qq (⟦ δ ∘ σ ⟧Th a) (tkR (δ ∘ σ) δC δA refl kc₁ a r)))
              w₃ (comp-k₀ ρ (δ ∘ σ) δD δC δA qq kc₁ kc₂ a r)
        ∙ cong (λ t → ρ' (fst t) (snd t)) (comp-k₀ δ σ δC δB δA q e kc₁ a r)
        ≡ ≈K (ρ ∘ (δ ∘ σ)) ((ρ ∘ δ) ∘ σ) δD δA pxw pxw' w c kc₂ kc₃ a r
          ∙ (subst (λ w → _≡_ {A = ⟦ ext _ _ δD ⟧T _} (⟦ (ρ ∘ δ) ∘ σ ⟧Th a , tkR ((ρ ∘ δ) ∘ σ) δD δA w kc₃ a r)
                             (⟦ ρ ∘ δ ⟧Th (⟦ σ ⟧Th a) , tkR (ρ ∘ δ) δD δB refl kc₄ (⟦ σ ⟧Th a) (tkR σ δB δA refl e a r)))
                   w₄ (comp-k₀ (ρ ∘ δ) σ δD δB δA kc₄ e kc₃ a r)
             ∙ comp-k₀ ρ δ δD δC δB qq q kc₄ (⟦ σ ⟧Th a) (tkR σ δB δA refl e a r))
  AK₂ .refl .refl refl refl w =
    subst (λ w → comp-k₀ ρ (δ ∘ σ) δD δC δA qq kc₁ kc₂ a r
                 ∙ cong (λ t → ρ' (fst t) (snd t)) (comp-k₀ δ σ δC δB δA q e kc₁ a r)
                 ≡ ≈K (ρ ∘ (δ ∘ σ)) ((ρ ∘ δ) ∘ σ) δD δA refl refl w c kc₂ kc₃ a r
                   ∙ (comp-k₀ (ρ ∘ δ) σ δD δB δA kc₄ e kc₃ a r
                      ∙ comp-k₀ ρ δ δD δC δB qq q kc₄ (⟦ σ ⟧Th a) (tkR σ δB δA refl e a r)))
          (set→2prop VarΣ-set refl w) AK₀
open AKs using (AK₂)

AK : {Γ : Con}{A B C Dt D₁ D₂ D₃ D₄ : Ty Γ}{x : Var Γ D₁}{y : Var Γ D₂}{z : Var Γ D₃}{w : Var Γ D₄}{γ : ⟦ Γ ⟧C}
     (ρ : Thin C Dt)(δ : Thin B C)(σ : Thin A B)(δD : Thin Dt D₄)(δC : Thin C D₃)(δB : Thin B D₂)(δA : Thin A D₁)
     (pxy : _≡_ {A = VarΣ Γ} (D₁ , x) (D₂ , y))(pyz : _≡_ {A = VarΣ Γ} (D₂ , y) (D₃ , z))
     (pzw : _≡_ {A = VarΣ Γ} (D₃ , z) (D₄ , w))
     (pxz : _≡_ {A = VarΣ Γ} (D₁ , x) (D₃ , z))(pyw : _≡_ {A = VarΣ Γ} (D₂ , y) (D₄ , w))
     (pxw pxw' : _≡_ {A = VarΣ Γ} (D₁ , x) (D₄ , w))(wxw : pxw ≡ pxw')
     (qq : Code (δD ∘ ρ) δC)(q : Code (δC ∘ δ) δB)(e : Code (δB ∘ σ) δA)
     (c : Code (ρ ∘ (δ ∘ σ)) ((ρ ∘ δ) ∘ σ))
     (kc₁ : Code (δC ∘ (δ ∘ σ)) δA)(kc₂ : Code (δD ∘ (ρ ∘ (δ ∘ σ))) δA)
     (kc₃ : Code (δD ∘ ((ρ ∘ δ) ∘ σ)) δA)(kc₄ : Code (δD ∘ (ρ ∘ δ)) δB)
     (a : ⟦ A ⟧T γ)(r : Σ (⟦ D₁ ⟧T γ) (λ d → Σ (⟦ δA ⟧Th a ≡ d) (λ _ → ⟦ x ⟧V γ d)))
   → comp-k ρ (δ ∘ σ) δD δC δA pxz pzw pxw qq kc₁ kc₂ a r
     ∙ cong (λ t → ⟦ ρ ⟧Th (fst t) , tkR ρ δD δC pzw qq (fst t) (snd t)) (comp-k δ σ δC δB δA pxy pyz pxz q e kc₁ a r)
     ≡ ≈K (ρ ∘ (δ ∘ σ)) ((ρ ∘ δ) ∘ σ) δD δA pxw pxw' wxw c kc₂ kc₃ a r
       ∙ (comp-k (ρ ∘ δ) σ δD δB δA pxy pyw pxw' kc₄ e kc₃ a r
          ∙ comp-k ρ δ δD δC δB pyz pzw pyw qq q kc₄ (⟦ σ ⟧Th a) (tkR σ δB δA pxy e a r))
AK ρ δ σ δD δC δB δA refl refl refl pxz pyw pxw pxw' wxw qq q e c kc₁ kc₂ kc₃ kc₄ a r =
  J₁ pxz (VarΣ-set refl pxz) pyw (VarΣ-set refl pyw)
  where
    J₁ : (pxz : _)(w₁ : refl ≡ pxz)(pyw : _)(w₂ : refl ≡ pyw)
       → comp-k ρ (δ ∘ σ) δD δC δA pxz refl pxw qq kc₁ kc₂ a r
         ∙ cong (λ t → ⟦ ρ ⟧Th (fst t) , tkR ρ δD δC refl qq (fst t) (snd t))
                (subst (λ w → _≡_ {A = ⟦ ext _ _ δC ⟧T _} (⟦ δ ∘ σ ⟧Th a , tkR (δ ∘ σ) δC δA w kc₁ a r)
                                  (⟦ δ ⟧Th (⟦ σ ⟧Th a) , tkR δ δC δB refl q (⟦ σ ⟧Th a) (tkR σ δB δA refl e a r)))
                       w₁ (comp-k₀ δ σ δC δB δA q e kc₁ a r))
         ≡ ≈K (ρ ∘ (δ ∘ σ)) ((ρ ∘ δ) ∘ σ) δD δA pxw pxw' wxw c kc₂ kc₃ a r
           ∙ (comp-k (ρ ∘ δ) σ δD δB δA refl pyw pxw' kc₄ e kc₃ a r
              ∙ subst (λ w → _≡_ {A = ⟦ ext _ _ δD ⟧T _} (⟦ ρ ∘ δ ⟧Th (⟦ σ ⟧Th a) , tkR (ρ ∘ δ) δD δB w kc₄ (⟦ σ ⟧Th a) (tkR σ δB δA refl e a r))
                                (⟦ ρ ⟧Th (⟦ δ ⟧Th (⟦ σ ⟧Th a)) , tkR ρ δD δC refl qq (⟦ δ ⟧Th (⟦ σ ⟧Th a))
                                                                  (tkR δ δC δB refl q (⟦ σ ⟧Th a) (tkR σ δB δA refl e a r))))
                      w₂ (comp-k₀ ρ δ δD δC δB qq q kc₄ (⟦ σ ⟧Th a) (tkR σ δB δA refl e a r)))
    J₁ .refl refl .refl refl =
      AK₂ ρ δ σ δD δC δB δA qq q e c kc₁ kc₂ kc₃ kc₄ a r pxw pxw' (VarΣ-set refl pxw) (VarΣ-set refl pxw') wxw

cohAs ρ δ tε c a = ∙refl (⟦∘⟧ ρ δ a) ∙ cong (_∙ ⟦∘⟧ ρ δ a) (sym (refl≈ (ρ ∘ δ) c a))
cohAs ρ δ (t-d σ) c (a , r) = cohAs ρ δ σ c a
cohAs ρ (t-d δ) (t-k σ ex e) c (a , r) = cohAs ρ δ σ c a
cohAs (t-d ρ) (t-k {x = y} {y = z} {δ = δC} {δ' = δB} δ ey q) (t-k {x = x} {δ' = δA} σ ex e) c (a , r) =
  cong (⟦∘⟧ ρ (δ ∘ σ) a ∙_)
       (sym (cong-∘ ⟦ ρ ⟧Th fst (comp-k δ σ δC δB δA (CodeV-sound x y ex) (CodeV-sound y z ey)
                                          (CodeV-sound x z (CodeV-trans x y z ex ey)) q e _ a r))
        ∙ cong (cong ⟦ ρ ⟧Th) (fstC δ σ δC δB δA _ _ _ q e _ a r))
  ∙ cohAs ρ δ σ c a
cohAs (t-k {x = z} {y = w} {δ = δD} {δ' = δC} ρ ez qq) (t-k {x = y} {δ' = δB} δ ey q) (t-k {x = x} {δ' = δA} σ ex e) c (a , r) =
  AK ρ δ σ δD δC δB δA (CodeV-sound x y ex) (CodeV-sound y z ey) (CodeV-sound z w ez)
     (CodeV-sound x z (CodeV-trans x y z ex ey)) (CodeV-sound y w (CodeV-trans y z w ey ez))
     (CodeV-sound x w (CodeV-trans x z w (CodeV-trans x y z ex ey) ez))
     (CodeV-sound x w (CodeV-trans x y w ex (CodeV-trans y z w ey ez))) (VarΣ-set _ _)
     qq q e c _ _ _ _ a r
-- the base of the weakening of a keep
fstU : {Γ : Con}{A B C C' B₀ : Ty Γ}{x : Var Γ C}{y : Var Γ C'}
       (σ : Thin A B)(δ : Thin B C')(δ' : Thin A C)(p₀ : _≡_ {A = VarΣ Γ} (C , x) (C' , y))
       (e : Code (δ ∘ σ) δ')(e₁ : Code (wkThin δ (p {A = B₀}) ∘ wkThin σ p) (wkThin δ' p))
       {γ : ⟦ Γ ⟧C}{X : ⟦ B₀ ⟧T γ → Grpd}(a : ⟦ wkTy A (p {A = B₀}) ⟧T (γ , X))
       (r : Σ (⟦ wkTy C (p {A = B₀}) ⟧T (γ , X)) (λ d → Σ (⟦ wkThin δ' p ⟧Th a ≡ d) (λ _ → ⟦ x ⟧V γ (unwk C d))))
     → cong fst (uk σ δ δ' p₀ e e₁ a r) ≡ unwk-nat σ a
fstU σ δ δ' refl e e₁ a r = pathK-fst (unwk-nat σ a) _

-- cohWN for keeps
WK : {Γ : Con}{A B C C' B₀ : Ty Γ}{x : Var Γ C}{y : Var Γ C'}
     (ρ ρ' : Thin A B)(δ : Thin B C')(δ' : Thin A C)(p₀ p₀' : _≡_ {A = VarΣ Γ} (C , x) (C' , y))(w : p₀ ≡ p₀')
     (w₁ : cong (sucΣ {B = B₀}) p₀ ≡ cong sucΣ p₀')
     (c : Code ρ ρ')(c' : Code (wkThin ρ (p {A = B₀})) (wkThin ρ' p))
     (e : Code (δ ∘ ρ) δ')(e' : Code (δ ∘ ρ') δ')
     (e₁ : Code (wkThin δ p ∘ wkThin ρ p) (wkThin δ' p))(e₁' : Code (wkThin δ p ∘ wkThin ρ' p) (wkThin δ' p))
     {γ : ⟦ Γ ⟧C}{X : ⟦ B₀ ⟧T γ → Grpd}(a : ⟦ wkTy A (p {A = B₀}) ⟧T (γ , X))
     (r : Σ (⟦ wkTy C (p {A = B₀}) ⟧T (γ , X)) (λ d → Σ (⟦ wkThin δ' p ⟧Th a ≡ d) (λ _ → ⟦ x ⟧V γ (unwk C d))))
   → cong (unwk (ext B y δ)) (≈K (wkThin ρ p) (wkThin ρ' p) (wkThin δ p) (wkThin δ' p) (cong sucΣ p₀) (cong sucΣ p₀') w₁ c' e₁ e₁' a r)
     ∙ uk ρ' δ δ' p₀' e' e₁' a r
     ≡ uk ρ δ δ' p₀ e e₁ a r
       ∙ ≈K ρ ρ' δ δ' p₀ p₀' w c e e' (unwk A a) (unwk C (fst r) , sym (unwk-nat δ' a) ∙ cong (unwk C) (fst (snd r)) , snd (snd r))
WK {B = B} {C' = C'} ρ ρ' δ δ' refl .refl refl w₁ c c' e e' e₁ e₁' {γ = γ} a r =
  subst (λ w₁ → cong (unwk (ext B _ δ)) (≈K (wkThin ρ p) (wkThin ρ' p) (wkThin δ p) (wkThin δ' p) refl refl w₁ c' e₁ e₁' a r)
                ∙ uk ρ' δ δ' refl e' e₁' a r
                ≡ uk ρ δ δ' refl e e₁ a r
                  ∙ ≈K ρ ρ' δ δ' refl refl refl c e e' (unwk _ a) (unwk _ (fst r) , sym (unwk-nat δ' a) ∙ cong (unwk _) (fst (snd r)) , snd (snd r)))
        (set→2prop VarΣ-set refl w₁)
        (cong (_∙ uk ρ' δ δ' refl e' e₁' a r)
              (pathK-imgU (unwk B) (unwk C') (λ b → sym (unwk-nat δ b)) (≈ {σ = wkThin ρ p} {wkThin ρ' p} c' a) _)
         ∙ pathK-∙∙ (grpdEq (isGrpdT C' γ)) (cong (unwk B) (≈ {σ = wkThin ρ p} {wkThin ρ' p} c' a)) (unwk-nat ρ' a)
                    (unwk-nat ρ a) (≈ {σ = ρ} {ρ'} c (unwk _ a)) _ _ _ _ (cohWN ρ ρ' c c' a))

cohWN tε tε c c' a = refl
cohWN (t-d ρ) (t-d ρ') c c' (a , r) = cohWN ρ ρ' c c' a
cohWN (t-k {x = x} {y = y} {δ = δ} {δ' = δ'} ρ ex e) (t-k ρ' ex' e') c c' (a , r) =
  WK ρ ρ' δ δ' (CodeV-sound x y ex) (CodeV-sound x y ex') (VarΣ-set _ _) (VarΣ-set _ _) c c' e e' _ _ a r

-- cohW∘ for a keep after a keep
module WDs {Γ : Con}{A B C D B₀ : Ty Γ}{x : Var Γ D}
           (δ : Thin B C)(σ : Thin A B)(δC : Thin C D)(δB : Thin B D)(δA : Thin A D)
           (q : Code (δC ∘ δ) δB)(e : Code (δB ∘ σ) δA)(kc : Code (δC ∘ (δ ∘ σ)) δA)
           (qw : Code (wkThin δC (p {A = B₀}) ∘ wkThin δ p) (wkThin δB p))
           (ew : Code (wkThin δB (p {A = B₀}) ∘ wkThin σ p) (wkThin δA p))
           (kcw : Code (wkThin δC (p {A = B₀}) ∘ (wkThin δ p ∘ wkThin σ p)) (wkThin δA p))
           (kcd : Code (wkThin δC (p {A = B₀}) ∘ wkThin (δ ∘ σ) p) (wkThin δA p))
           (c : Code (wkThin δ (p {A = B₀}) ∘ wkThin σ p) (wkThin (δ ∘ σ) p))
           {γ : ⟦ Γ ⟧C}{X : ⟦ B₀ ⟧T γ → Grpd}(a : ⟦ wkTy A (p {A = B₀}) ⟧T (γ , X))
           (r : Σ (⟦ wkTy D (p {A = B₀}) ⟧T (γ , X)) (λ d → Σ (⟦ wkThin δA p ⟧Th a ≡ d) (λ _ → ⟦ x ⟧V γ (unwk D d)))) where

  r' : Σ (⟦ D ⟧T γ) (λ d → Σ (⟦ δA ⟧Th (unwk A a) ≡ d) (λ _ → ⟦ x ⟧V γ d))
  r' = unwk D (fst r) , sym (unwk-nat δA a) ∙ cong (unwk D) (fst (snd r)) , snd (snd r)

  Loop : Set
  Loop = _≡_ {A = _≡_ {A = VarΣ (Γ ▷ B₀)} (wkTy D (p {A = B₀}) , suc {B = B₀} x) (wkTy D p , suc {B = B₀} x)} refl refl

  endL endR : ⟦ ext C x δC ⟧T γ
  endL = unwk (ext C x δC) (⟦ wkThin δ p ∘ wkThin σ p ⟧Th a ,
                            tkR {x = suc {B = B₀} x} {y = suc {B = B₀} x} (wkThin δ p ∘ wkThin σ p) (wkThin δC p) (wkThin δA p) refl kcw a r)
  endR = ⟦ δ ⟧Th (⟦ σ ⟧Th (unwk A a)) ,
         tkR {x = x} {y = x} δ δC δB refl q (⟦ σ ⟧Th (unwk A a)) (tkR {x = x} {y = x} σ δB δA refl e (unwk A a) r')

  endM : ⟦ ext C x δC ⟧T γ
  endM = unwk (ext C x δC) (⟦ wkThin δ p ⟧Th (⟦ wkThin σ p ⟧Th a) ,
                            tkR {x = suc {B = B₀} x} {y = suc {B = B₀} x} (wkThin δ p) (wkThin δC p) (wkThin δB p) refl qw (⟦ wkThin σ p ⟧Th a)
                                (tkR {x = suc {B = B₀} x} {y = suc {B = B₀} x} (wkThin σ p) (wkThin δB p) (wkThin δA p) refl ew a r))

  LHS₀ : Loop → endL ≡ endR
  LHS₀ w₂ = cong (unwk (ext C x δC)) (≈K {x = suc {B = B₀} x} {y = suc {B = B₀} x} (wkThin δ p ∘ wkThin σ p) (wkThin (δ ∘ σ) p) (wkThin δC p) (wkThin δA p)
                                         refl refl w₂ c kcw kcd a r)
            ∙ (uk {x = x} {y = x} (δ ∘ σ) δC δA refl kc kcd a r ∙ comp-k₀ {x = x} δ σ δC δB δA q e kc (unwk A a) r')

  tail₀ : endM ≡ endR
  tail₀ = uk {x = x} {y = x} δ δC δB refl q qw (⟦ wkThin σ p ⟧Th a) (tkR {x = suc {B = B₀} x} {y = suc {B = B₀} x} (wkThin σ p) (wkThin δB p) (wkThin δA p) refl ew a r)
          ∙ cong (λ t → ⟦ δ ⟧Th (fst t) , tkR {x = x} {y = x} δ δC δB refl q (fst t) (snd t)) (uk {x = x} {y = x} σ δB δA refl e ew a r)

  WD₀ : LHS₀ refl
        ≡ cong (unwk (ext C x δC)) (comp-k₀ {x = suc {B = B₀} x} (wkThin δ p) (wkThin σ p) (wkThin δC p) (wkThin δB p) (wkThin δA p) qw ew kcw a r)
          ∙ tail₀
  WD₀ =
    cong (_∙ (uk {x = x} {y = x} (δ ∘ σ) δC δA refl kc kcd a r ∙ comp-k₀ {x = x} δ σ δC δB δA q e kc (unwk A a) r'))
         (pathK-imgU (unwk C) (unwk D) (λ b → sym (unwk-nat δC b)) (≈ {σ = wkThin δ p ∘ wkThin σ p} {wkThin (δ ∘ σ) p} c a) _)
    ∙ cong (pathK (cong (unwk C) (≈ {σ = wkThin δ p ∘ wkThin σ p} {wkThin (δ ∘ σ) p} c a))
                  (imgSU (unwk C) (unwk D) (λ b → sym (unwk-nat δC b)) (≈ {σ = wkThin δ p ∘ wkThin σ p} {wkThin (δ ∘ σ) p} c a)
                         (sym (∙-assoc (sym (cong ⟦ wkThin δC p ⟧Th (≈ {σ = wkThin δ p ∘ wkThin σ p} {wkThin (δ ∘ σ) p} c a)))
                                       (kp (wkThin δC p) (wkThin δ p ∘ wkThin σ p) (wkThin δA p) kcw a) (fst (snd r)))
                          ∙ cong (_∙ fst (snd r)) (cohN (wkThin δC p) (wkThin δ p ∘ wkThin σ p) (wkThin (δ ∘ σ) p) (wkThin δA p) c kcw kcd a))) ∙_)
           (pathK-comp (unwk-nat (δ ∘ σ) a) (⟦∘⟧ δ σ (unwk A a)) _ _)
    ∙ pathK-∙∙ (grpdEq (isGrpdT D γ))
               (cong (unwk C) (≈ {σ = wkThin δ p ∘ wkThin σ p} {wkThin (δ ∘ σ) p} c a))
               (unwk-nat (δ ∘ σ) a ∙ ⟦∘⟧ δ σ (unwk A a))
               (cong (unwk C) (⟦∘⟧ (wkThin δ p) (wkThin σ p) a))
               (unwk-nat δ (⟦ wkThin σ p ⟧Th a) ∙ cong ⟦ δ ⟧Th (unwk-nat σ a)) _ _ _ _
               (cohW∘ δ σ c a)
    ∙ sym (cong (_∙ tail₀)
                (pathK-imgU (unwk C) (unwk D) (λ b → sym (unwk-nat δC b)) (⟦∘⟧ (wkThin δ p) (wkThin σ p) a) _)
           ∙ cong (pathK (cong (unwk C) (⟦∘⟧ (wkThin δ p) (wkThin σ p) a))
                         (imgSU (unwk C) (unwk D) (λ b → sym (unwk-nat δC b)) (⟦∘⟧ (wkThin δ p) (wkThin σ p) a)
                                (sym (∙-assoc (sym (cong ⟦ wkThin δC p ⟧Th (⟦∘⟧ (wkThin δ p) (wkThin σ p) a)))
                                              (kp (wkThin δC p) (wkThin δ p ∘ wkThin σ p) (wkThin δA p) kcw a) (fst (snd r)))
                                 ∙ cong (_∙ fst (snd r)) (cohA (wkThin δC p) (wkThin δB p) (wkThin δA p) (wkThin δ p) (wkThin σ p) qw ew kcw a)
                                 ∙ ∙-assoc (kp (wkThin δC p) (wkThin δ p) (wkThin δB p) qw (⟦ wkThin σ p ⟧Th a))
                                           (kp (wkThin δB p) (wkThin σ p) (wkThin δA p) ew a) (fst (snd r)))) ∙_)
                  (cong (uk {x = x} {y = x} δ δC δB refl q qw (⟦ wkThin σ p ⟧Th a) (tkR {x = suc {B = B₀} x} {y = suc {B = B₀} x} (wkThin σ p) (wkThin δB p) (wkThin δA p) refl ew a r) ∙_)
                        (pathK-img ⟦ δ ⟧Th (kp δC δ δB q) (unwk-nat σ a) _)
                   ∙ pathK-comp (unwk-nat δ (⟦ wkThin σ p ⟧Th a)) (cong ⟦ δ ⟧Th (unwk-nat σ a)) _ _))

  compw : Loop → _≡_ {A = ⟦ ext (wkTy C (p {A = B₀})) (suc {B = B₀} x) (wkThin δC p) ⟧T (γ , X)}
                     (⟦ wkThin δ p ∘ wkThin σ p ⟧Th a ,
                      tkR {x = suc {B = B₀} x} {y = suc {B = B₀} x} (wkThin δ p ∘ wkThin σ p) (wkThin δC p) (wkThin δA p) refl kcw a r)
                     (⟦ wkThin δ p ⟧Th (⟦ wkThin σ p ⟧Th a) ,
                      tkR {x = suc {B = B₀} x} {y = suc {B = B₀} x} (wkThin δ p) (wkThin δC p) (wkThin δB p) refl qw (⟦ wkThin σ p ⟧Th a)
                          (tkR {x = suc {B = B₀} x} {y = suc {B = B₀} x} (wkThin σ p) (wkThin δB p) (wkThin δA p) refl ew a r))
  compw w₁ = subst (λ w → _≡_ {A = ⟦ ext (wkTy C (p {A = B₀})) (suc {B = B₀} x) (wkThin δC p) ⟧T (γ , X)}
                       (⟦ wkThin δ p ∘ wkThin σ p ⟧Th a , tkR {x = suc {B = B₀} x} {y = suc {B = B₀} x} (wkThin δ p ∘ wkThin σ p) (wkThin δC p) (wkThin δA p) w kcw a r)
                       (⟦ wkThin δ p ⟧Th (⟦ wkThin σ p ⟧Th a) ,
                        tkR {x = suc {B = B₀} x} {y = suc {B = B₀} x} (wkThin δ p) (wkThin δC p) (wkThin δB p) refl qw (⟦ wkThin σ p ⟧Th a)
                            (tkR {x = suc {B = B₀} x} {y = suc {B = B₀} x} (wkThin σ p) (wkThin δB p) (wkThin δA p) refl ew a r)))
                   w₁ (comp-k₀ {x = suc {B = B₀} x} (wkThin δ p) (wkThin σ p) (wkThin δC p) (wkThin δB p) (wkThin δA p) qw ew kcw a r)

  WD₁ : (w₁ w₂ : Loop)
      → LHS₀ w₂ ≡ cong (unwk (ext C x δC)) (compw w₁) ∙ tail₀
  WD₁ w₁ w₂ =
    subst (λ w₁ → LHS₀ w₂ ≡ cong (unwk (ext C x δC)) (compw w₁) ∙ tail₀)
          (set→2prop VarΣ-set refl w₁)
          (subst (λ w₂ → LHS₀ w₂ ≡ cong (unwk (ext C x δC)) (compw refl) ∙ tail₀)
                 (set→2prop VarΣ-set refl w₂) WD₀)
open WDs using (WD₁)

WD : {Γ : Con}{A B C D₁ D₂ D₃ B₀ : Ty Γ}{x : Var Γ D₁}{y : Var Γ D₂}{z : Var Γ D₃}
     (δ : Thin B C)(σ : Thin A B)(δC : Thin C D₃)(δB : Thin B D₂)(δA : Thin A D₁)
     (pxy : _≡_ {A = VarΣ Γ} (D₁ , x) (D₂ , y))(pyz : _≡_ {A = VarΣ Γ} (D₂ , y) (D₃ , z))
     (pxz : _≡_ {A = VarΣ Γ} (D₁ , x) (D₃ , z))(w₂ : cong (sucΣ {B = B₀}) pxz ≡ cong sucΣ pxz)
     (q : Code (δC ∘ δ) δB)(e : Code (δB ∘ σ) δA)(kc : Code (δC ∘ (δ ∘ σ)) δA)
     (qw : Code (wkThin δC (p {A = B₀}) ∘ wkThin δ p) (wkThin δB p))
     (ew : Code (wkThin δB (p {A = B₀}) ∘ wkThin σ p) (wkThin δA p))
     (kcw : Code (wkThin δC (p {A = B₀}) ∘ (wkThin δ p ∘ wkThin σ p)) (wkThin δA p))
     (kcd : Code (wkThin δC (p {A = B₀}) ∘ wkThin (δ ∘ σ) p) (wkThin δA p))
     (c : Code (wkThin δ (p {A = B₀}) ∘ wkThin σ p) (wkThin (δ ∘ σ) p))
     {γ : ⟦ Γ ⟧C}{X : ⟦ B₀ ⟧T γ → Grpd}(a : ⟦ wkTy A (p {A = B₀}) ⟧T (γ , X))
     (r : Σ (⟦ wkTy D₁ (p {A = B₀}) ⟧T (γ , X)) (λ d → Σ (⟦ wkThin δA p ⟧Th a ≡ d) (λ _ → ⟦ x ⟧V γ (unwk D₁ d))))
   → cong (unwk (ext C z δC)) (≈K (wkThin δ p ∘ wkThin σ p) (wkThin (δ ∘ σ) p) (wkThin δC p) (wkThin δA p)
                                  (cong sucΣ pxz) (cong sucΣ pxz) w₂ c kcw kcd a r)
     ∙ (uk (δ ∘ σ) δC δA pxz kc kcd a r
        ∙ comp-k δ σ δC δB δA pxy pyz pxz q e kc (unwk A a)
                 (unwk D₁ (fst r) , sym (unwk-nat δA a) ∙ cong (unwk D₁) (fst (snd r)) , snd (snd r)))
     ≡ cong (unwk (ext C z δC))
            (comp-k (wkThin δ p) (wkThin σ p) (wkThin δC p) (wkThin δB p) (wkThin δA p)
                    (cong sucΣ pxy) (cong sucΣ pyz) (cong sucΣ pxz) qw ew kcw a r)
       ∙ (uk δ δC δB pyz q qw (⟦ wkThin σ p ⟧Th a) (tkR (wkThin σ p) (wkThin δB p) (wkThin δA p) (cong sucΣ pxy) ew a r)
          ∙ cong (λ t → ⟦ δ ⟧Th (fst t) , tkR δ δC δB pyz q (fst t) (snd t)) (uk σ δB δA pxy e ew a r))
WD {A = A} {C = C} {D₁ = D₁} {B₀ = B₀} {x = x} δ σ δC δB δA refl refl pxz w₂ q e kc qw ew kcw kcd c {γ} {X} a r =
  J₀ pxz (VarΣ-set refl pxz) (VarΣ-set refl (cong sucΣ pxz)) w₂
  where
    r' = unwk D₁ (fst r) , sym (unwk-nat δA a) ∙ cong (unwk D₁) (fst (snd r)) , snd (snd r)
    J₀ : (pxz : _)(w₀ : refl ≡ pxz)(w₁ : refl ≡ cong (sucΣ {B = B₀}) pxz)(w₂ : cong (sucΣ {B = B₀}) pxz ≡ cong sucΣ pxz)
       → cong (unwk (ext _ _ δC)) (≈K {x = suc {B = B₀} x} {y = suc {B = B₀} x} (wkThin δ p ∘ wkThin σ p) (wkThin (δ ∘ σ) p) (wkThin δC p) (wkThin δA p)
                                      (cong sucΣ pxz) (cong sucΣ pxz) w₂ c kcw kcd a r)
         ∙ (uk {x = x} {y = x} (δ ∘ σ) δC δA pxz kc kcd a r
            ∙ subst (λ w → _≡_ {A = ⟦ ext C x δC ⟧T γ} (⟦ δ ∘ σ ⟧Th (unwk A a) , tkR {x = x} {y = x} (δ ∘ σ) δC δA w kc (unwk A a) r')
                         (⟦ δ ⟧Th (⟦ σ ⟧Th (unwk A a)) , tkR {x = x} {y = x} δ δC δB refl q (⟦ σ ⟧Th (unwk A a)) (tkR {x = x} {y = x} σ δB δA refl e (unwk A a) r')))
                    w₀ (comp-k₀ {x = x} δ σ δC δB δA q e kc (unwk A a) r'))
         ≡ cong (unwk (ext _ _ δC))
                (subst (λ w → _≡_ {A = ⟦ ext (wkTy C (p {A = B₀})) (suc {B = B₀} x) (wkThin δC p) ⟧T (γ , X)}
                           (⟦ wkThin δ p ∘ wkThin σ p ⟧Th a , tkR {x = suc {B = B₀} x} {y = suc {B = B₀} x} (wkThin δ p ∘ wkThin σ p) (wkThin δC p) (wkThin δA p) w kcw a r)
                           (⟦ wkThin δ p ⟧Th (⟦ wkThin σ p ⟧Th a) ,
                            tkR {x = suc {B = B₀} x} {y = suc {B = B₀} x} (wkThin δ p) (wkThin δC p) (wkThin δB p) refl qw (⟦ wkThin σ p ⟧Th a)
                                (tkR {x = suc {B = B₀} x} {y = suc {B = B₀} x} (wkThin σ p) (wkThin δB p) (wkThin δA p) refl ew a r)))
                       w₁ (comp-k₀ {x = suc {B = B₀} x} (wkThin δ p) (wkThin σ p) (wkThin δC p) (wkThin δB p) (wkThin δA p) qw ew kcw a r))
           ∙ (uk {x = x} {y = x} δ δC δB refl q qw (⟦ wkThin σ p ⟧Th a) (tkR {x = suc {B = B₀} x} {y = suc {B = B₀} x} (wkThin σ p) (wkThin δB p) (wkThin δA p) refl ew a r)
              ∙ cong (λ t → ⟦ δ ⟧Th (fst t) , tkR {x = x} {y = x} δ δC δB refl q (fst t) (snd t)) (uk {x = x} {y = x} σ δB δA refl e ew a r))
    J₀ .refl refl w₁ w₂ = WD₁ δ σ δC δB δA q e kc qw ew kcw kcd c a r w₁ w₂

cohW∘ δ tε c a = cong (λ t → cong (unwk _) t ∙ (unwk-nat δ a ∙ refl)) (refl≈ (wkThin δ p) c a)
cohW∘ δ (t-d σ) c (a , r) = cohW∘ δ σ c a
cohW∘ (t-d δ) (t-k {x = x} {y = y} {δ = δB} {δ' = δA} σ ex e) c (a , r) =
  cohW∘ δ σ c a
  ∙ cong (λ t → cong (unwk _) (⟦∘⟧ (wkThin δ p) (wkThin σ p) a) ∙ (unwk-nat δ (⟦ wkThin σ p ⟧Th a) ∙ t))
         (sym (sym (cong-∘ ⟦ δ ⟧Th fst (uk σ δB δA (CodeV-sound x y ex) e _ a r))
               ∙ cong (cong ⟦ δ ⟧Th) (fstU σ δB δA (CodeV-sound x y ex) e _ a r)))
cohW∘ (t-k {x = y} {y = z} {δ = δC} {δ' = δB} δ ey q) (t-k {x = x} {δ' = δA} σ ex e) c (a , r) =
  WD δ σ δC δB δA (CodeV-sound x y ex) (CodeV-sound y z ey) (CodeV-sound x z (CodeV-trans x y z ex ey))
     (VarΣ-set _ _) q e _ _ _ _ _ c a r
