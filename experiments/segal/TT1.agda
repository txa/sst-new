{-# OPTIONS --cubical #-}
{-
TT₁: the Segal-style syntax one truncation level up, with contexts,
variables and one-step weakening as constructors.

  Thin  groupoids (truncated)      Tri  sets (derived)
  Tet   propositions (derived)     4-simplices trivial

Only Thin is truncated explicitly. Each horn filler comes with a
contraction (uniq/uniqP), which makes the space of fillers contractible;
the h-levels of Tri and Tet follow.

  Λ²₁ : _∘_, tri, uniq, uniqP                  composition
  Λ³₁ : fill₁, tet₁, uniq₁, uniqP₁              associator
  Λ³₂ : fill₂, tet₂, uniq₂, uniqP₂
  Λ⁴₁ : fill₄                                   pentagon (Tet is a prop)

Weakening is a constructor on types (wk), and acts on thinnings,
triangles and tetrahedra (wkThin, wkTri, wkTet): it is a map of Segal
objects. Its computation rules (wk on ε and ext) are not included: the
construction of SST n does not need them, since zero : Var (Γ ▷ A) (wk A A)
already has the right type.

Result: in each context, the thinnings form a Segal SST₄ in the sense of Segal4
(is21Semicat), hence a (2,1)-semicategory with associator and pentagon.
Identities are added as degeneracies (id, degenerate triangles and
degenerate tetrahedra), giving unitors and the triangle identity.

Tet t₀ t₁ t₂ t₃ for a tetrahedron A → B → C → D with edges σ, δ, δC and
long edges τ (AC), δB (BD), δA (AD) has the faces
  t₀ : Tri δC δ δB  (BCD)     t₁ : Tri δC τ δA  (ACD)
  t₂ : Tri δB σ δA  (ABD)     t₃ : Tri δ σ τ    (ABC)
which is Segal4's X₃ with X₂ f g h = Tri g f h.
-}
module TT1 where

open import Cubical.Foundations.Prelude hiding (_▷_)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Segal4

infixr 9 _∘_
infixl 5 _▷_

data U : Type
data El : U → Type

data U where
  con  : U
  ty   : El con → U
  var  : (Γ : El con) → El (ty Γ) → U
  thin : {Γ : El con} → El (ty Γ) → El (ty Γ) → U
  tri  : {Γ : El con}{A B C : El (ty Γ)} → El (thin B C) → El (thin A B) → El (thin A C) → U
  tet  : {Γ : El con}{A B C D : El (ty Γ)}{σ : El (thin A B)}{δ : El (thin B C)}{δC : El (thin C D)}
         {τ : El (thin A C)}{δB : El (thin B D)}{δA : El (thin A D)}
       → El (tri δC δ δB) → El (tri δC τ δA) → El (tri δB σ δA) → El (tri δ σ τ) → U

Con : Type
Con = El con

variable Γ : Con

Ty : Con → Type
Ty Γ = El (ty Γ)

Var : (Γ : Con) → Ty Γ → Type
Var Γ A = El (var Γ A)

Thin : {Γ : Con} → Ty Γ → Ty Γ → Type
Thin A B = El (thin A B)

Tri : {Γ : Con}{A B C : Ty Γ} → Thin B C → Thin A B → Thin A C → Type
Tri δ σ τ = El (tri δ σ τ)

Tet : {Γ : Con}{A B C D : Ty Γ}{σ : Thin A B}{δ : Thin B C}{δC : Thin C D}
      {τ : Thin A C}{δB : Thin B D}{δA : Thin A D}
    → Tri δC δ δB → Tri δC τ δA → Tri δB σ δA → Tri δ σ τ → Type
Tet t₀ t₁ t₂ t₃ = El (tet t₀ t₁ t₂ t₃)

data El where
  -- contexts, telescopes and variables
  •    : Con
  _▷_  : (Γ : Con) → Ty Γ → Con
  ε    : Ty Γ
  ext  : (A : Ty Γ){B : Ty Γ} → Var Γ B → Thin A B → Ty Γ
  wk   : (E : Ty Γ) → Ty Γ → Ty (Γ ▷ E)
  zero : {A : Ty Γ} → Var (Γ ▷ A) (wk A A)
  suc  : {A B : Ty Γ} → Var Γ A → Var (Γ ▷ B) (wk B A)
  -- thinnings
  tε   : Thin {Γ} ε ε
  t-d  : {A B C : Ty Γ}{x : Var Γ C}{γ : Thin A C} → Thin A B → Thin (ext A x γ) B
  t-k  : {A B C : Ty Γ}{x : Var Γ C}{δ : Thin B C}{δ' : Thin A C}
       → (σ : Thin A B) → Tri δ σ δ' → Thin (ext A x δ') (ext B x δ)
  isGrpdThin : {A B : Ty Γ}{σ τ : Thin A B}{p q : σ ≡ τ}(r s : p ≡ q) → r ≡ s

  -- Λ²₁
  _∘_   : {A B C : Ty Γ} → Thin B C → Thin A B → Thin A C
  tri   : {A B C : Ty Γ}(δ : Thin B C)(σ : Thin A B) → Tri δ σ (δ ∘ σ)
  uniq  : {A B C : Ty Γ}{δ : Thin B C}{σ : Thin A B}{τ : Thin A C} → Tri δ σ τ → δ ∘ σ ≡ τ
  uniqP : {A B C : Ty Γ}{δ : Thin B C}{σ : Thin A B}{τ : Thin A C}
          (t : Tri δ σ τ) → PathP (λ i → Tri δ σ (uniq t i)) (tri δ σ) t

  -- Λ³₁: the face ACD from the others
  fill₁  : {A B C D : Ty Γ}{σ : Thin A B}{δ : Thin B C}{δC : Thin C D}
           {τ : Thin A C}{δB : Thin B D}{δA : Thin A D}
         → Tri δC δ δB → Tri δB σ δA → Tri δ σ τ → Tri δC τ δA
  tet₁   : {A B C D : Ty Γ}{σ : Thin A B}{δ : Thin B C}{δC : Thin C D}
           {τ : Thin A C}{δB : Thin B D}{δA : Thin A D}
           (t₀ : Tri δC δ δB)(t₂ : Tri δB σ δA)(t₃ : Tri δ σ τ) → Tet t₀ (fill₁ t₀ t₂ t₃) t₂ t₃
  uniq₁  : {A B C D : Ty Γ}{σ : Thin A B}{δ : Thin B C}{δC : Thin C D}
           {τ : Thin A C}{δB : Thin B D}{δA : Thin A D}
           {t₀ : Tri δC δ δB}{t₁ : Tri δC τ δA}{t₂ : Tri δB σ δA}{t₃ : Tri δ σ τ}
         → Tet t₀ t₁ t₂ t₃ → fill₁ t₀ t₂ t₃ ≡ t₁
  uniqP₁ : {A B C D : Ty Γ}{σ : Thin A B}{δ : Thin B C}{δC : Thin C D}
           {τ : Thin A C}{δB : Thin B D}{δA : Thin A D}
           {t₀ : Tri δC δ δB}{t₁ : Tri δC τ δA}{t₂ : Tri δB σ δA}{t₃ : Tri δ σ τ}
           (T : Tet t₀ t₁ t₂ t₃) → PathP (λ i → Tet t₀ (uniq₁ T i) t₂ t₃) (tet₁ t₀ t₂ t₃) T

  -- Λ³₂: the face ABD from the others
  fill₂  : {A B C D : Ty Γ}{σ : Thin A B}{δ : Thin B C}{δC : Thin C D}
           {τ : Thin A C}{δB : Thin B D}{δA : Thin A D}
         → Tri δC δ δB → Tri δC τ δA → Tri δ σ τ → Tri δB σ δA
  tet₂   : {A B C D : Ty Γ}{σ : Thin A B}{δ : Thin B C}{δC : Thin C D}
           {τ : Thin A C}{δB : Thin B D}{δA : Thin A D}
           (t₀ : Tri δC δ δB)(t₁ : Tri δC τ δA)(t₃ : Tri δ σ τ) → Tet t₀ t₁ (fill₂ t₀ t₁ t₃) t₃
  uniq₂  : {A B C D : Ty Γ}{σ : Thin A B}{δ : Thin B C}{δC : Thin C D}
           {τ : Thin A C}{δB : Thin B D}{δA : Thin A D}
           {t₀ : Tri δC δ δB}{t₁ : Tri δC τ δA}{t₂ : Tri δB σ δA}{t₃ : Tri δ σ τ}
         → Tet t₀ t₁ t₂ t₃ → fill₂ t₀ t₁ t₃ ≡ t₂
  uniqP₂ : {A B C D : Ty Γ}{σ : Thin A B}{δ : Thin B C}{δC : Thin C D}
           {τ : Thin A C}{δB : Thin B D}{δA : Thin A D}
           {t₀ : Tri δC δ δB}{t₁ : Tri δC τ δA}{t₂ : Tri δB σ δA}{t₃ : Tri δ σ τ}
           (T : Tet t₀ t₁ t₂ t₃) → PathP (λ i → Tet t₀ t₁ (uniq₂ T i) t₃) (tet₂ t₀ t₁ t₃) T

  -- Λ⁴₁: the tetrahedron 0234 from the others (edges eᵢⱼ : Thin vᵢ vⱼ,
  -- triangles tᵢⱼₖ : Tri eⱼₖ eᵢⱼ eᵢₖ)
  fill₄ : {v₀ v₁ v₂ v₃ v₄ : Ty Γ}
          {e₀₁ : Thin v₀ v₁}{e₁₂ : Thin v₁ v₂}{e₂₃ : Thin v₂ v₃}{e₃₄ : Thin v₃ v₄}
          {e₀₂ : Thin v₀ v₂}{e₁₃ : Thin v₁ v₃}{e₂₄ : Thin v₂ v₄}
          {e₀₃ : Thin v₀ v₃}{e₁₄ : Thin v₁ v₄}{e₀₄ : Thin v₀ v₄}
          {t₀₁₂ : Tri e₁₂ e₀₁ e₀₂}{t₀₁₃ : Tri e₁₃ e₀₁ e₀₃}{t₀₁₄ : Tri e₁₄ e₀₁ e₀₄}
          {t₀₂₃ : Tri e₂₃ e₀₂ e₀₃}{t₀₂₄ : Tri e₂₄ e₀₂ e₀₄}{t₀₃₄ : Tri e₃₄ e₀₃ e₀₄}
          {t₁₂₃ : Tri e₂₃ e₁₂ e₁₃}{t₁₂₄ : Tri e₂₄ e₁₂ e₁₄}{t₁₃₄ : Tri e₃₄ e₁₃ e₁₄}
          {t₂₃₄ : Tri e₃₄ e₂₃ e₂₄}
        → Tet t₂₃₄ t₁₃₄ t₁₂₄ t₁₂₃ → Tet t₁₃₄ t₀₃₄ t₀₁₄ t₀₁₃
        → Tet t₁₂₄ t₀₂₄ t₀₁₄ t₀₁₂ → Tet t₁₂₃ t₀₂₃ t₀₁₃ t₀₁₂
        → Tet t₂₃₄ t₀₃₄ t₀₂₄ t₀₂₃

  -- degeneracies: identities, degenerate triangles and degenerate tetrahedra
  -- (Tet is a proposition, so the tetrahedra need no contractions)
  id      : {A : Ty Γ} → Thin A A
  tri-idr : {A C : Ty Γ}(δ : Thin A C) → Tri δ id δ
  tri-idl : {A C : Ty Γ}(δ : Thin A C) → Tri id δ δ
  tet-s₀  : {A B C : Ty Γ}{δ : Thin B C}{σ : Thin A B}{τ : Thin A C}
            (t : Tri δ σ τ) → Tet t t (tri-idr τ) (tri-idr σ)
  tet-s₁  : {A B C : Ty Γ}{δ : Thin B C}{σ : Thin A B}{τ : Thin A C}
            (t : Tri δ σ τ) → Tet (tri-idr δ) t t (tri-idl σ)
  tet-s₂  : {A B C : Ty Γ}{δ : Thin B C}{σ : Thin A B}{τ : Thin A C}
            (t : Tri δ σ τ) → Tet (tri-idl δ) (tri-idl τ) t t
  -- the computation rules of composition, as triangles
  tri-ε  : {C : Ty Γ}{δ : Thin ε C} → Tri δ tε δ
  tri-d  : {A B C D : Ty Γ}{x : Var Γ D}{γ : Thin A D}{δ : Thin B C}{σ : Thin A B}{τ : Thin A C}
         → Tri δ σ τ → Tri δ (t-d {x = x} {γ = γ} σ) (t-d {x = x} {γ = γ} τ)
  tri-dk : {A B C D : Ty Γ}{x : Var Γ D}{δB : Thin B D}{δA : Thin A D}{δ : Thin B C}{σ : Thin A B}{τ : Thin A C}
           {e : Tri δB σ δA}
         → Tri δ σ τ → Tri (t-d {x = x} {γ = δB} δ) (t-k σ e) (t-d {x = x} {γ = δA} τ)
  tri-kk : {A B C D : Ty Γ}{x : Var Γ D}{δC : Thin C D}{δB : Thin B D}{δA : Thin A D}
           {δ : Thin B C}{σ : Thin A B}{τ : Thin A C}
           {q : Tri δC δ δB}{e : Tri δB σ δA}
         → (s : Tri δ σ τ) → Tri (t-k {x = x} δ q) (t-k {x = x} σ e) (t-k τ (fill₁ q e s))

  -- weakening is a map of Segal objects
  wkThin : (E : Ty Γ){A B : Ty Γ} → Thin A B → Thin (wk E A) (wk E B)
  wkTri  : (E : Ty Γ){A B C : Ty Γ}{δ : Thin B C}{σ : Thin A B}{τ : Thin A C}
         → Tri δ σ τ → Tri (wkThin E δ) (wkThin E σ) (wkThin E τ)
  wkTet  : (E : Ty Γ){A B C D : Ty Γ}{σ : Thin A B}{δ : Thin B C}{δC : Thin C D}
           {τ : Thin A C}{δB : Thin B D}{δA : Thin A D}
           {t₀ : Tri δC δ δB}{t₁ : Tri δC τ δA}{t₂ : Tri δB σ δA}{t₃ : Tri δ σ τ}
         → Tet t₀ t₁ t₂ t₃ → Tet (wkTri E t₀) (wkTri E t₁) (wkTri E t₂) (wkTri E t₃)

-- h-levels of triangles and tetrahedra -------------------------------------------
-- each is a retract of a path type, via its contraction constructors

isSetTri : {A B C : Ty Γ}{δ : Thin B C}{σ : Thin A B}{τ : Thin A C} → isSet (Tri δ σ τ)
isSetTri {δ = δ} {σ} {τ} =
  isSetRetract uniq (λ p → subst (Tri δ σ) p (tri δ σ)) (λ t → fromPathP (uniqP t))
               (isGrpdThin' (δ ∘ σ) τ)
  where
    isGrpdThin' : {A B : Ty Γ}(x y : Thin A B) → isSet (x ≡ y)
    isGrpdThin' x y p q r s = isGrpdThin r s

isPropTet : {A B C D : Ty Γ}{σ : Thin A B}{δ : Thin B C}{δC : Thin C D}
            {τ : Thin A C}{δB : Thin B D}{δA : Thin A D}
            {t₀ : Tri δC δ δB}{t₁ : Tri δC τ δA}{t₂ : Tri δB σ δA}{t₃ : Tri δ σ τ}
          → isProp (Tet t₀ t₁ t₂ t₃)
isPropTet {t₀ = t₀} {t₁} {t₂} {t₃} =
  isPropRetract uniq₁ (λ p → subst (λ t → Tet t₀ t t₂ t₃) p (tet₁ t₀ t₂ t₃)) (λ T → fromPathP (uniqP₁ T))
                (isSetTri (fill₁ t₀ t₂ t₃) t₁)

-- the thinnings form a Segal SST₄ ---------------------------------------------------

sst : Con → SST4
sst Γ = record
  { X₀ = Ty Γ
  ; X₁ = Thin
  ; X₂ = λ f g h → Tri g f h
  ; X₃ = Tet
  ; X₄ = λ _ _ _ _ _ → Unit
  }

segal : (Γ : Con) → is21Semicat (sst Γ)
segal Γ = record
  { isGrpd₁ = λ x y p q r s → isGrpdThin r s
  ; Λ²₁ = λ f g → (g ∘ f , tri g f) , λ (h , t) → ΣPathP (uniq t , uniqP t)
  ; Λ³₁ = λ t₀ t₂ t₃ → (fill₁ t₀ t₂ t₃ , tet₁ t₀ t₂ t₃) , λ (t₁ , T) → ΣPathP (uniq₁ T , uniqP₁ T)
  ; Λ³₂ = λ t₀ t₁ t₃ → (fill₂ t₀ t₁ t₃ , tet₂ t₀ t₁ t₃) , λ (t₂ , T) → ΣPathP (uniq₂ T , uniqP₂ T)
  ; Λ⁴₁ = λ T₀ T₂ T₃ T₄ → inhProp→isContr (fill₄ T₀ T₂ T₃ T₄ , tt) (isProp× isPropTet isPropUnit)
  }

-- hence a (2,1)-semicategory: composition, associator and pentagon
module _ {Γ : Con} where
  open FromSegal (sst Γ) (segal Γ) public using (α ; pentagon)

-- with the degeneracies: unitors and the triangle identity ----------------------------

degen : (Γ : Con) → Degen4 (sst Γ)
degen Γ = record { id₁ = id ; s₀ = tri-idr ; s₁ = tri-idl ; s₀₃ = tet-s₀ ; s₁₃ = tet-s₁ ; s₂₃ = tet-s₂ }

module _ {Γ : Con} where
  open FromSegalDeg (sst Γ) (segal Γ) (degen Γ) public using (λu ; ρu ; triangle)
