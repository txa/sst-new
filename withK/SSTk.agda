{-
SST : ℕ → Con, structurally and totally, following Section 3 of
Altenkirch, Capriotti, Kraus: "Extending homotopy type theory with
strict equality" (2016).

By induction on the level k we define, simultaneously,

  ctx k                      -- SST_k, levels X₀ .. X_{k-1}
  SK k n    : Ty (ctx k)     -- the k-skeleton of an (n-1)-simplex:
                             --   all faces with ≤ k vertices
  SK→ k f   : Thin (SK k n) (SK k m)       for f : OPE m n
  α k f g   : SK→ k g ∘ SK→ k f ≡ SK→ k (f ⊙ g)

with
  ctx (k+1)  = ctx k ▷ SK k (k+1)             -- X_k : ∂Δ[k] → Set
  SK (k+1) n = wk (SK k n) , one entry  X_k (wk (SK→ k h))
                                 for each face h : OPE (k+1) n
  SK→ (k+1) f keeps the entries f ⊙ g.

Level k+1 only ever uses level k *weakened once*, so all types agree
definitionally. The paper's transport along α_k is the commuting
equation of t-k, and the coherence of α (paper: by K) is t-k-cong.
-}
module SSTk where

open import TT
open import Agda.Builtin.Equality
open import Agda.Builtin.Nat using (Nat; suc) renaming (zero to 0ℕ)
open import Agda.Builtin.Sigma

infixr 5 _∙_
_∙_ : {X : Set}{a b c : X} → a ≡ b → b ≡ c → a ≡ c
refl ∙ q = q

id-∘ : (δ : Thin A B) → id ∘ δ ≡ δ
id-∘ tε = refl
id-∘ (t-d δ) = t-d-cong (id-∘ δ)
id-∘ (t-k δ e) = t-k-cong (id-∘ δ)

-- order preserving embeddings = morphisms of Δ₊ (including the empty
-- ordinal, as in the paper); the outer constructor is the last vertex

data OPE : Nat → Nat → Set where
  done : OPE 0ℕ 0ℕ
  drop : {m n : Nat} → OPE m n → OPE m (suc n)
  keep : {m n : Nat} → OPE m n → OPE (suc m) (suc n)

_⊙_ : {l m n : Nat} → OPE m n → OPE l m → OPE l n
done ⊙ done = done
drop f ⊙ g = drop (f ⊙ g)
keep f ⊙ drop g = drop (f ⊙ g)
keep f ⊙ keep g = keep (f ⊙ g)

-- Π f : Δ₊(j, n). Y (c f)  as an extension of a telescope -------------

module Tele {Γ : Con}{C : Ty Γ}(Y : Var Γ C) where

  -- extend S (with projection π to the base B) by one entry Y (c h ∘ π)
  -- for every h : OPE j n; returns the telescope and its projection to B
  Tel : {B : Ty Γ}(S : Ty Γ)(π : Thin S B)(j n : Nat)
      → (OPE j n → Thin B C) → Σ (Ty Γ) (λ T → Thin T B)
  Tel S π 0ℕ 0ℕ c = ext S Y (c done ∘ π) , t-d π
  Tel S π (suc j) 0ℕ c = S , π
  Tel S π 0ℕ (suc n) c = Tel S π 0ℕ n (λ h → c (drop h))
  Tel S π (suc j) (suc n) c =
    let r = Tel S π (suc j) n (λ h → c (drop h))
    in Tel (fst r) (snd r) j n (λ h → c (keep h))

  -- projection back to the start of the extension
  prj : {B : Ty Γ}(S : Ty Γ)(π : Thin S B)(j n : Nat)
      → (c : OPE j n → Thin B C) → Thin (fst (Tel S π j n c)) S
  prj S π 0ℕ 0ℕ c = t-d id
  prj S π (suc j) 0ℕ c = id
  prj S π 0ℕ (suc n) c = prj S π 0ℕ n (λ h → c (drop h))
  prj S π (suc j) (suc n) c =
    let r = Tel S π (suc j) n (λ h → c (drop h))
    in prj S π (suc j) n (λ h → c (drop h)) ∘ prj (fst r) (snd r) j n (λ h → c (keep h))

  tel-prj : {B : Ty Γ}(S : Ty Γ)(π : Thin S B)(j n : Nat)
          → (c : OPE j n → Thin B C) → π ∘ prj S π j n c ≡ snd (Tel S π j n c)
  tel-prj S π 0ℕ 0ℕ c = t-d-cong (∘-id π)
  tel-prj S π (suc j) 0ℕ c = ∘-id π
  tel-prj S π 0ℕ (suc n) c = tel-prj S π 0ℕ n (λ h → c (drop h))
  tel-prj S π (suc j) (suc n) c =
    let c₁ = λ h → c (drop h)
        r = Tel S π (suc j) n c₁
    in ∘-assoc π (prj S π (suc j) n c₁) (prj (fst r) (snd r) j n (λ h → c (keep h)))
       ∙ cong (_∘ prj (fst r) (snd r) j n (λ h → c (keep h))) (tel-prj S π (suc j) n c₁)
       ∙ tel-prj (fst r) (snd r) j n (λ h → c (keep h))

  -- the action of f : OPE m n, keeping the entries f ⊙ g (paper: SK→)
  sel : {m n : Nat}(f : OPE m n)(j : Nat){B B' S T : Ty Γ}
        {πS : Thin S B}{πT : Thin T B'}
        (φ : Thin B B')(cS : OPE j n → Thin B C)(cT : OPE j m → Thin B' C)
      → ((g : OPE j m) → cT g ∘ φ ≡ cS (f ⊙ g))
      → (σ : Thin S T) → πT ∘ σ ≡ φ ∘ πS
      → Thin (fst (Tel S πS j n cS)) (fst (Tel T πT j m cT))

  sel-inv : {m n : Nat}(f : OPE m n)(j : Nat){B B' S T : Ty Γ}
        {πS : Thin S B}{πT : Thin T B'}
        (φ : Thin B B')(cS : OPE j n → Thin B C)(cT : OPE j m → Thin B' C)
      → (hc : (g : OPE j m) → cT g ∘ φ ≡ cS (f ⊙ g))
      → (σ : Thin S T)(h : πT ∘ σ ≡ φ ∘ πS)
      → snd (Tel T πT j m cT) ∘ sel f j φ cS cT hc σ h ≡ φ ∘ snd (Tel S πS j n cS)

  sel done 0ℕ {πS = πS}{πT} φ cS cT hc σ h =
    t-k σ (sym (∘-assoc (cT done) πT σ) ∙ cong (cT done ∘_) h
           ∙ ∘-assoc (cT done) φ πS ∙ cong (_∘ πS) (hc done))
  sel done (suc j) φ cS cT hc σ h = σ
  sel (drop f) 0ℕ φ cS cT hc σ h = sel f 0ℕ φ (λ h → cS (drop h)) cT hc σ h
  sel (drop {n = n} f) (suc j) {S = S}{πS = πS} φ cS cT hc σ h =
    let r = Tel S πS (suc j) n (λ h → cS (drop h))
    in sel f (suc j) φ (λ h → cS (drop h)) cT hc σ h
       ∘ prj (fst r) (snd r) j n (λ h → cS (keep h))
  sel (keep f) 0ℕ φ cS cT hc σ h =
    sel f 0ℕ φ (λ h → cS (drop h)) (λ h → cT (drop h)) (λ g → hc (drop g)) σ h
  sel (keep f) (suc j) φ cS cT hc σ h =
    sel f j φ (λ h → cS (keep h)) (λ h → cT (keep h)) (λ g → hc (keep g))
      (sel f (suc j) φ (λ h → cS (drop h)) (λ h → cT (drop h)) (λ g → hc (drop g)) σ h)
      (sel-inv f (suc j) φ (λ h → cS (drop h)) (λ h → cT (drop h)) (λ g → hc (drop g)) σ h)

  sel-inv done 0ℕ φ cS cT hc σ h = t-d-cong h
  sel-inv done (suc j) φ cS cT hc σ h = h
  sel-inv (drop f) 0ℕ φ cS cT hc σ h = sel-inv f 0ℕ φ (λ h → cS (drop h)) cT hc σ h
  sel-inv {m = m} (drop {n = n} f) (suc j) {S = S}{T = T}{πS = πS}{πT} φ cS cT hc σ h =
    let r = Tel S πS (suc j) n (λ h → cS (drop h))
        p = prj (fst r) (snd r) j n (λ h → cS (keep h))
        σ' = sel f (suc j) φ (λ h → cS (drop h)) cT hc σ h
    in ∘-assoc (snd (Tel T πT (suc j) m cT)) σ' p
       ∙ cong (_∘ p) (sel-inv f (suc j) φ (λ h → cS (drop h)) cT hc σ h)
       ∙ sym (∘-assoc φ (snd r) p)
       ∙ cong (φ ∘_) (tel-prj (fst r) (snd r) j n (λ h → cS (keep h)))
  sel-inv (keep f) 0ℕ φ cS cT hc σ h =
    sel-inv f 0ℕ φ (λ h → cS (drop h)) (λ h → cT (drop h)) (λ g → hc (drop g)) σ h
  sel-inv (keep f) (suc j) φ cS cT hc σ h =
    sel-inv f j φ (λ h → cS (keep h)) (λ h → cT (keep h)) (λ g → hc (keep g))
      (sel f (suc j) φ (λ h → cS (drop h)) (λ h → cT (drop h)) (λ g → hc (drop g)) σ h)
      (sel-inv f (suc j) φ (λ h → cS (drop h)) (λ h → cT (drop h)) (λ g → hc (drop g)) σ h)

  -- naturality of prj
  prj-nat : {m n : Nat}(f : OPE m n)(j : Nat){B B' S T : Ty Γ}
        {πS : Thin S B}{πT : Thin T B'}
        (φ : Thin B B')(cS : OPE j n → Thin B C)(cT : OPE j m → Thin B' C)
      → (hc : (g : OPE j m) → cT g ∘ φ ≡ cS (f ⊙ g))
      → (σ : Thin S T)(h : πT ∘ σ ≡ φ ∘ πS)
      → prj T πT j m cT ∘ sel f j φ cS cT hc σ h ≡ σ ∘ prj S πS j n cS
  prj-nat done 0ℕ φ cS cT hc σ h = t-d-cong (id-∘ σ ∙ sym (∘-id σ))
  prj-nat done (suc j) φ cS cT hc σ h = id-∘ σ ∙ sym (∘-id σ)
  prj-nat (drop f) 0ℕ φ cS cT hc σ h = prj-nat f 0ℕ φ (λ h → cS (drop h)) cT hc σ h
  prj-nat {m = m} (drop {n = n} f) (suc j) {S = S}{T = T}{πS = πS}{πT} φ cS cT hc σ h =
    let r = Tel S πS (suc j) n (λ h → cS (drop h))
        p₁ = prj S πS (suc j) n (λ h → cS (drop h))
        p₂ = prj (fst r) (snd r) j n (λ h → cS (keep h))
        σ' = sel f (suc j) φ (λ h → cS (drop h)) cT hc σ h
    in ∘-assoc (prj T πT (suc j) m cT) σ' p₂
       ∙ cong (_∘ p₂) (prj-nat f (suc j) φ (λ h → cS (drop h)) cT hc σ h)
       ∙ sym (∘-assoc σ p₁ p₂)
  prj-nat (keep f) 0ℕ φ cS cT hc σ h =
    prj-nat f 0ℕ φ (λ h → cS (drop h)) (λ h → cT (drop h)) (λ g → hc (drop g)) σ h
  prj-nat (keep {m = m}{n = n} f) (suc j) {S = S}{T = T}{πS = πS}{πT} φ cS cT hc σ h =
    let rS = Tel S πS (suc j) n (λ h → cS (drop h))
        rT = Tel T πT (suc j) m (λ h → cT (drop h))
        pS₁ = prj S πS (suc j) n (λ h → cS (drop h))
        pS₂ = prj (fst rS) (snd rS) j n (λ h → cS (keep h))
        pT₁ = prj T πT (suc j) m (λ h → cT (drop h))
        pT₂ = prj (fst rT) (snd rT) j m (λ h → cT (keep h))
        σ₁ = sel f (suc j) φ (λ h → cS (drop h)) (λ h → cT (drop h)) (λ g → hc (drop g)) σ h
        h₁ = sel-inv f (suc j) φ (λ h → cS (drop h)) (λ h → cT (drop h)) (λ g → hc (drop g)) σ h
        σ₂ = sel f j φ (λ h → cS (keep h)) (λ h → cT (keep h)) (λ g → hc (keep g)) σ₁ h₁
    in sym (∘-assoc pT₁ pT₂ σ₂)
       ∙ cong (pT₁ ∘_) (prj-nat f j φ (λ h → cS (keep h)) (λ h → cT (keep h)) (λ g → hc (keep g)) σ₁ h₁)
       ∙ ∘-assoc pT₁ σ₁ pS₂
       ∙ cong (_∘ pS₂) (prj-nat f (suc j) φ (λ h → cS (drop h)) (λ h → cT (drop h)) (λ g → hc (drop g)) σ h)
       ∙ sym (∘-assoc σ pS₁ pS₂)

  -- functoriality of sel (paper: α_{k+1})
  sel-comp : {l m n : Nat}(f : OPE m n)(g : OPE l m)(j : Nat){B B' B'' S T R : Ty Γ}
        {πS : Thin S B}{πT : Thin T B'}{πR : Thin R B''}
        {φ : Thin B B'}{ψ : Thin B' B''}{χ : Thin B B''}
        {cS : OPE j n → Thin B C}{cT : OPE j m → Thin B' C}{cR : OPE j l → Thin B'' C}
        {hf : (g' : OPE j m) → cT g' ∘ φ ≡ cS (f ⊙ g')}
        {hg : (g' : OPE j l) → cR g' ∘ ψ ≡ cT (g ⊙ g')}
        {hfg : (g' : OPE j l) → cR g' ∘ χ ≡ cS ((f ⊙ g) ⊙ g')}
        {σf : Thin S T}{σg : Thin T R}{σfg : Thin S R}
        {h-f : πT ∘ σf ≡ φ ∘ πS}{h-g : πR ∘ σg ≡ ψ ∘ πT}{h-fg : πR ∘ σfg ≡ χ ∘ πS}
      → σg ∘ σf ≡ σfg
      → sel g j ψ cT cR hg σg h-g ∘ sel f j φ cS cT hf σf h-f
        ≡ sel (f ⊙ g) j χ cS cR hfg σfg h-fg
  sel-comp done done 0ℕ eq = t-k-cong eq
  sel-comp done done (suc j) eq = eq
  sel-comp (drop f) g 0ℕ eq = sel-comp f g 0ℕ eq
  sel-comp (drop {n = n} f) g (suc j) {S = S}{πS = πS}{φ = φ}{ψ}{cS = cS}{cT}{cR}{hf}{hg}
           {σf = σf}{σg}{h-f = h-f}{h-g} eq =
    let r = Tel S πS (suc j) n (λ h → cS (drop h))
        p = prj (fst r) (snd r) j n (λ h → cS (keep h))
    in ∘-assoc (sel g (suc j) ψ cT cR hg σg h-g)
               (sel f (suc j) φ (λ h → cS (drop h)) cT hf σf h-f) p
       ∙ cong (_∘ p) (sel-comp f g (suc j) eq)
  sel-comp (keep f) (drop g) 0ℕ eq = sel-comp f g 0ℕ eq
  sel-comp (keep {m = m}{n = n} f) (drop g) (suc j) {S = S}{T = T}{πS = πS}{πT = πT}
           {φ = φ}{ψ}{cS = cS}{cT}{cR}{hf}{hg}{σf = σf}{σg}{h-f = h-f}{h-g} eq =
    let rS = Tel S πS (suc j) n (λ h → cS (drop h))
        rT = Tel T πT (suc j) m (λ h → cT (drop h))
        pS₂ = prj (fst rS) (snd rS) j n (λ h → cS (keep h))
        pT₂ = prj (fst rT) (snd rT) j m (λ h → cT (keep h))
        τ = sel g (suc j) ψ (λ h → cT (drop h)) cR hg σg h-g
        σ₁ = sel f (suc j) φ (λ h → cS (drop h)) (λ h → cT (drop h)) (λ g → hf (drop g)) σf h-f
        h₁ = sel-inv f (suc j) φ (λ h → cS (drop h)) (λ h → cT (drop h)) (λ g → hf (drop g)) σf h-f
        σ₂ = sel f j φ (λ h → cS (keep h)) (λ h → cT (keep h)) (λ g → hf (keep g)) σ₁ h₁
    in sym (∘-assoc τ pT₂ σ₂)
       ∙ cong (τ ∘_) (prj-nat f j φ (λ h → cS (keep h)) (λ h → cT (keep h)) (λ g → hf (keep g)) σ₁ h₁)
       ∙ ∘-assoc τ σ₁ pS₂
       ∙ cong (_∘ pS₂) (sel-comp f g (suc j) eq)
  sel-comp (keep f) (keep g) 0ℕ eq = sel-comp f g 0ℕ eq
  sel-comp (keep f) (keep g) (suc j) eq =
    sel-comp f g j (sel-comp f g (suc j) eq)

-- semi-simplicial types ----------------------------------------------

ctx : Nat → Con
SK : (k n : Nat) → Ty (ctx k)
SK→ : (k : Nat){m n : Nat} → OPE m n → Thin (SK k n) (SK k m)
α : (k : Nat){l m n : Nat}(f : OPE m n)(g : OPE l m)
  → SK→ k g ∘ SK→ k f ≡ SK→ k (f ⊙ g)

ctx 0ℕ = •
ctx (suc k) = ctx k ▷ SK k (suc k)

-- the faces of SK (k+1) n at level k: X_k applied to the face's boundary
face : (k : Nat){n : Nat} → OPE (suc k) n
     → Thin (wkTy (SK k n) (p {A = SK k (suc k)})) (wkTy (SK k (suc k)) p)
face k h = wkThin (SK→ k h) p

wk-α : (k : Nat){l m n : Nat}(f : OPE m n)(g : OPE l m)
     → wkThin (SK→ k g) (p {A = SK k (suc k)}) ∘ wkThin (SK→ k f) p
       ≡ wkThin (SK→ k (f ⊙ g)) p
wk-α k f g = sym (wkThin-∘ (SK→ k g) (SK→ k f) p) ∙ cong (λ δ → wkThin δ p) (α k f g)

SK 0ℕ n = ε
SK (suc k) n = fst (Tele.Tel zero (wkTy (SK k n) p) id (suc k) n (face k))

SK→ 0ℕ f = tε
SK→ (suc k) f =
  Tele.sel zero f (suc k) φ (face k) (face k) (λ g → wk-α k f g) φ (id-∘ φ ∙ sym (∘-id φ))
  where φ = wkThin (SK→ k f) p

α 0ℕ f g = refl
α (suc k) f g = Tele.sel-comp zero f g (suc k) (wk-α k f g)

-- semi-simplicial types up to level n: X₀ .. Xₙ
SST : Nat → Con
SST n = ctx (suc n)

-- tests: agrees with the hand-written contexts
open import SST using (Γ₀; Γ₁; Γ₂)

_ : SST 0 ≡ Γ₀
_ = refl

_ : SST 1 ≡ Γ₁
_ = refl

_ : SST 2 ≡ Γ₂
_ = refl

size : Ty Γ → Nat
size ε = 0
size (ext A _ _) = suc (size A)

-- ∂Δ[n] has 2ⁿ⁺¹ - 2 entries
_ : size (SK 3 4) ≡ 14
_ = refl

_ : size (SK 4 5) ≡ 30
_ = refl
