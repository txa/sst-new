{-# OPTIONS --without-K #-}
{-
The inductive-recursive syntax TT.agda is a model of the HIIT signature
(HIIT.agda). By initiality of the HIIT this gives the map  HIIT → IR,
which sends wk and ∘ to the functions wkTy and _∘_, and the path
constructors to the corresponding laws. No K is used.
-}
module HIITtoIR where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import HIIT using (Model; substℓ; symℓ)
import TT as I

-- transporting a keep along an equation of its source index gives a keep
-- (the stored codes are propositions, so they can be anything)
t-k-transp : {Γ : I.Con}{A B C C' : I.Ty Γ}{x : I.Var Γ C}{y : I.Var Γ C'}
             {δ : I.Thin B C'}{δ₁ δ₂ : I.Thin A C}{σ : I.Thin A B}
             {c c' : I.CodeV x y}{e : I.Code (δ I.∘ σ) δ₁}{e' : I.Code (δ I.∘ σ) δ₂}
           → (q : δ₁ ≡ δ₂)
           → substℓ (λ d → I.Thin (I.ext A x d) (I.ext B y δ)) q (I.t-k σ c e) ≡ I.t-k σ c' e'
t-k-transp refl = I.t-k-cong refl

IR : Model lzero lzero
IR = record
  { Con = I.Con ; Ty = I.Ty ; Var = I.Var ; Thin = I.Thin
  ; • = I.•
  ; _▷_ = I._▷_
  ; ε = I.ε
  ; ext = λ A x δ → I.ext A x δ
  ; wk = λ A → I.wkTy A I.p
  ; tε = I.tε
  ; t-d = I.t-d
  ; _∘_ = I._∘_
  ; t-k = λ {Γ}{A}{B}{C}{x}{δ} σ → I.t-k σ (I.CodeV-refl x) (I.Code-refl (δ I.∘ σ))
  ; wkThin = λ σ → I.wkThin σ I.p
  ; zero = I.zero
  ; suc = I.suc
  ; wkε = refl
  ; wkext = refl
  ; ass = λ {Γ}{A}{B}{C}{D}{ρ}{δ}{σ} → I.sym (I.∘-assoc ρ δ σ)
  ; ∘tε = refl
  ; ∘t-d = refl
  ; t-d∘t-k = refl
  ; t-k∘t-k = λ {Γ}{A}{B}{C}{D}{x}{ρ}{δ}{σ} → t-k-transp (I.sym (I.∘-assoc ρ δ σ))
  ; wktε = refl
  ; wk∘ = λ {Γ}{B}{A}{A'}{A''}{δ}{σ} → I.wkThin-∘ δ σ I.p
  ; wkt-d = refl
  ; wkt-k = λ {Γ}{B}{A}{A'}{C}{x}{δ}{σ} → symℓ (t-k-transp (symℓ (I.wkThin-∘ δ σ I.p)))
  }
