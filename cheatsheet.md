# Cheat sheet: a type theory for semi-simplicial types (whiteboard talk)

Files: `withK/TT.agda`, `withK/SST.agda` (simplest), `TT.agda` (K-free),
`Sem.agda`, `HIIT.agda`, `HIITConj.agda`.

---

## 1. The basic type theory

Idea: contexts are **sequences of type families**, types are **telescopes**,
and every entry of a telescope is a family applied to a *selection* of
earlier entries.

Sorts

    Con            contexts            ⟦Γ⟧ : Set₁
    Ty Γ           telescopes          ⟦A⟧ : ⟦Γ⟧ → Set
    Var Γ A        families over A     ⟦x⟧ : (γ : ⟦Γ⟧) → ⟦A⟧γ → Set
    Thin A B       thinnings A → B     ⟦σ⟧ : ⟦A⟧γ → ⟦B⟧γ   (projections)
    Wk Δ Γ         weakenings Δ → Γ    ⟦w⟧ : ⟦Δ⟧ → ⟦Γ⟧     (forget families)

Constructors

    •      : Con
    _▷_    : (Γ : Con) → Ty Γ → Con                 ⟦Γ ▷ A⟧ = Σ γ. ⟦A⟧γ → Set
    p      : Wk (Γ ▷ A) Γ                           fst
    ε      : Ty Γ                                   ⊤
    ext    : (A : Ty Γ) → Var Γ B → Thin A B → Ty Γ ⟦ext A x δ⟧ = Σ a. ⟦x⟧(⟦δ⟧ a)
    zero   : Var (Γ ▷ A) (A[p])
    suc    : Var Γ A → Var (Γ ▷ B) (A[p])
    tε     : Thin ε ε
    t-d    : Thin A B → Thin (ext A x δ) B          drop:  (a , v) ↦ ⟦σ⟧a
    t-k    : Thin A B → Thin (ext A x ?) (ext B x δ)  keep: (a , v) ↦ (⟦σ⟧a , v)

Weakening is the only substitution, and only one step (`p`). It acts by
recursion (defined functions, not constructors):

    wkTy   : Ty Γ → Wk Δ Γ → Ty Δ                   A[w]
    wkVar  : Var Γ A → (w : Wk Δ Γ) → Var Δ (A[w])  wkVar x p = suc x
    wkThin : Thin A B → (w : Wk Δ Γ) → Thin (A[w]) (B[w])

    ε[w] = ε        (ext A x δ)[w] = ext (A[w]) (wkVar x w) (wkThin δ w)

Needed because `zero`, `suc` live in `Γ ▷ A` but their type `A` lives in
`Γ`. Semantically `A[p]` is interpreted by a map
`unwk : ⟦A[p]⟧(γ , X) → ⟦A⟧γ` (not an equation of types: avoids funext).
`ext A x δ` reads: "extend A by an argument of type `x (δ a)`" — δ picks
the arguments of x out of the entries of A.

Example (level 1):

    X₀ : Set                     Γ₀ = • ▷ ε
    X₁ : X₀ → X₀ → Set           A₁ = ext (ext ε zero tε) zero (t-d tε)

---

## 2. Equations in the syntax → induction-recursion; SST

The `?` in t-k: if σ : Thin A B and δ : Thin B C, the kept entry has
arguments `δ ∘ σ`:

    t-k : (σ : Thin A B) → Thin (ext A x (δ ∘ σ)) (ext B x δ)

* `∘` (and `wkTy`, `wkThin`, since `zero : Var (Γ▷A) (A[p])`) are
  **functions** appearing in constructor types
  ⇒ syntax is **inductive-inductive-recursive** (IR); in Agda via a
  universe `U / El`.
* Indexing by `δ ∘ σ` = green slime, matching breaks. Instead store the
  square:

      t-k : (σ : Thin A B) → δ ∘ σ ≡ δ' → Thin (ext A x δ') (ext B x δ)

* Composition (by recursion on the right):

      δ      ∘ tε        = δ
      δ      ∘ t-d σ     = t-d (δ ∘ σ)
      t-d δ  ∘ t-k σ e   = t-d (δ ∘ σ)
      t-k δ q ∘ t-k σ e  = t-k (δ ∘ σ) (?? : δC ∘ (δ ∘ σ) ≡ δA)

  `??` from q : δC ∘ δ ≡ δB, e : δB ∘ σ ≡ δA **and ∘-assoc**
  ⇒ the laws (∘-assoc, ∘-id, wkThin-∘) are defined mutually with ∘.

**Q: why not drop the equation and index by `δ ∘ σ` directly?**
Then ∘, id, wkThin need transports in the *terms*:

    t-k δ ∘ t-k σ  : Thin (ext A x ((δC ∘ δ) ∘ σ)) _
    t-k (δ ∘ σ)    : Thin (ext A x (δC ∘ (δ ∘ σ))) _    -- subst along ∘-assoc
    id = t-k id    : Thin (ext A x (δ ∘ id)) _          -- subst along ∘-id
    wkThin (t-k σ)                                       -- subst along wkThin-∘

plus green slime when matching (unify δ' with δ ∘ σ). With the
equation as a field, the transports go into the proof argument
(`t-k (δ ∘ σ) (∘-k q e)`, `t-k id (∘-id δ)`): no subst in terms, closed
terms compute. Price: proofs inside terms ⇒ need their uniqueness (§3).
Dropping it = the HIIT version (§5): t-k∘t-k is a path over `ass`.

SST level 2 (`SST.agda`):

    X₂ : (x₀ x₁ x₂ : X₀)(x₀₁ : X₁ x₀ x₁)(x₀₂ : X₁ x₀ x₂)(x₁₂ : X₁ x₁ x₂) → Set

    V₃  = three points (ext ... (suc zero) ...)
    E₀₁ = t-d (t-k (t-k tε)),  E₀₂ = t-k (t-d (t-k tε)),  E₁₂ = t-k (t-k (t-d tε))
    A₂  = ext (ext (ext V₃ zero E₀₁) zero (t-d E₀₂)) zero (t-d (t-d E₁₂))

Faces are thinnings; all equations are `refl` for closed terms.
`SSTk.agda`: `SST : ℕ → Con` for all n (ACK 2016, §3): skeleta
`SK k n : Ty`, face maps `SK→ f : Thin`, functoriality `α` — the paper's
transport along α is exactly the equation stored in t-k.

---

## 3. Why we need UIP

∘-assoc, t-k case:

    t-k ρ _ ∘ (t-k δ _ ∘ t-k σ _)  ≡  (t-k ρ _ ∘ t-k δ _) ∘ t-k σ _

first components: IH. Second components: two proofs e, e' of the same
equation `δ ∘ σ ≡ δ'`.

    t-k-cong : σ ≡ σ' → t-k σ e ≡ t-k σ' e'
    t-k-cong {e = refl}{e' = refl} refl = refl      -- K !

Needs: **Thin A B is a set** (UIP for the syntax). And ∘-assoc is used
inside the definition of ∘, so we need it to even define the syntax.

---

## 4. UIP can be avoided (syntax is K-free)

Thin is a set anyway (decidable equality ⇒ Hedberg), but cleaner:

* store a **code** instead of an identity (encode–decode):

      Code : Thin A C → Thin A' C' → Set      -- by recursion into ⊤ / ⊥
      Code tε tε             = ⊤
      Code (t-d σ) (t-d τ)   = Code σ τ
      Code (t-k σ _) (t-k τ _) = Code σ τ
      Code _ _               = ⊥

      t-k : (σ : Thin A B) → CodeV x y → Code (δ ∘ σ) δ' → Thin (ext A x δ') (ext B y δ)

* `Code-prop : (u v : Code σ τ) → u ≡ v` by plain induction — no K,
  no Hedberg, no Prop.
* separate x, y (related by `CodeV x y`) so no index repeats ⇒ pattern
  matching works `--without-K`.
* `Code-sound : Code σ τ → σ ≡ τ`, `VarΣ-set` (encode–decode).

⇒ `TT.agda`, `SSTk.agda`: syntax and `SST n` are **K-free**.

---

## 5. The problem: the semantics

Interpret into Set (`Sem.agda`). Keep must transport along the stored
equation:

    ⟦t-k σ e⟧ (a , v) = (⟦σ⟧ a , subst ⟦x⟧ (keq e a) v)
    keq e a : ⟦δ'⟧ a ≡ ⟦δ⟧ (⟦σ⟧ a)

Need, mutually:

    ⟦∘⟧ : ⟦δ ∘ σ⟧ a ≡ ⟦δ⟧ (⟦σ⟧ a)

t-k ∘ t-k case: v is transported along two **different paths**

    keq (∘-k q e) a       vs.      keq e a ∙ keq q (⟦σ⟧ a)

These are paths in `⟦C⟧ γ` — an **arbitrary semantic type**, not the
syntax. Need them equal ⇒ `pair-irr` ⇔ UIP for semantic types.
(Same in `unwk-nat` for weakening.)

* syntax being a set does **not** help: the paths live in the model.
* really it says ⟦∘⟧ must be coherent with ∘-assoc, then with the
  pentagon, … = **the SST coherence tower** again.
* HIIT view (`HIIT.agda`): make ∘, wk constructors, laws path
  constructors. Standard model: everything `refl`, K-free! But now the
  syntax is not obviously a set (`ass` needed to state t-k∘t-k ⇒ critical
  pairs, pentagon, …).
* `HIITConj.agda` — **Conjecture**: the map HIIT → IR is an equivalence.
  Then: IR syntax gets a K-free semantics `std ∘ (toIR)⁻¹`, and `SST n`
  is a type in book HoTT for every n.

Dead ends: free composition with proof-relevant derivations (tower moves
into t-k-cong); Kovács' HIT alone (pentagon). Open lead: strictly
associative composition (position maps).
