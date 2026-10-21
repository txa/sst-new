# Sem2: the 3-cell layer

Sem2 interprets the inductive-recursive syntax (`TT.agda`) into families of
2-types. It is `Sem1` with the groupoid truncation replaced by explicit
3-cells. This file lists the 3-cell lemmas needed, read off from the six holes
of `Sem2.agda`.

## The data so far

Fix a semantic point `a`. The semantics provides 1-cells (paths in semantic
telescopes):

| 1-cell | type | meaning |
|---|---|---|
| `≈c` | `⟦σ⟧ a ≡ ⟦τ⟧ a` for `c : Code σ τ` | codes act as paths |
| `∘(δ,σ)` = `⟦∘⟧ δ σ a` | `⟦δ ∘ σ⟧ a ≡ ⟦δ⟧ (⟦σ⟧ a)` | compositor |
| `u(δ)` = `unwk-nat δ a` | `unwk (⟦wkThin δ p⟧ a) ≡ ⟦δ⟧ (unwk a)` | weakening comparison |

and 2-cells, the six generic lemmas of `Sem1`:

| 2-cell | statement |
|---|---|
| `T(c,d,cd)` | `≈c ∙ ≈d ≡ ≈cd` |
| `R(δ;c,c')` | `∘(δ,σ) ∙ cong ⟦δ⟧ ≈c ≡ ≈c' ∙ ∘(δ,τ)` (code on the right argument) |
| `L(c;σ;c')` | `∘(δ,σ) ∙ ≈c (⟦σ⟧ a) ≡ ≈c' ∙ ∘(δ₂,σ)` (code on the left argument) |
| `As(ρ,δ,σ;c)` | `∘(ρ,δσ) ∙ cong ⟦ρ⟧ ∘(δ,σ) ≡ ≈c ∙ (∘(ρδ,σ) ∙ ∘(ρ,δ))` |
| `WN(ρ,ρ';c,c')` | `cong unwk ≈c' ∙ u(ρ') ≡ u(ρ) ∙ ≈c` |
| `W∘(δ,σ;c)` | `cong unwk ≈c ∙ (u(δσ) ∙ ∘(δ,σ)) ≡ cong unwk ∘(wkδ,wkσ) ∙ (u(δ) ∙ cong ⟦δ⟧ u(σ))` |

So the semantics is a pseudofunctor-like structure on the category of
thinnings: `≈` is its action on codes (equalities of thinnings), `∘` its
compositor, `u` a pseudonatural comparison for weakening, and the 2-cells are
the corresponding naturality and associativity data. The stored-path cells
`cohN`, `cohA`, `cohW` are built from these by the J-lemmas `lemN`, `lemA`,
`lemW`.

## What the holes need

Each hole says: transported along a 2-cell at smaller thinnings, two pastings
of stored-path cells agree. Unfolding `cohN`, `cohA` and `cohW`, each becomes
an equation between two pastings of the generic 2-cells, i.e. a 3-cell.

| hole | `t-k` case of | cells involved |
|---|---|---|
| 0 | `cohT` | `T(c,d,cd)`; `cohN` for `c`, `d`, `cd` (so `R`, `T`) |
| 1 | `cohR` | `R`; `cohA` at `σ` and `τ` (`As`, `L`, `T`); `cohN` (`R`, `T`) |
| 2 | `cohL` | `L`; `cohA` at `δ` and `δ₂`; `cohN` for the code on `δ` |
| 3 | `cohAs` | `As`; four `cohA` (four thinnings `δD, ρ, δ, σ`); `cohN` |
| 4 | `cohWN` | `WN`; `cohW` at `ρ` and `ρ'`; weakened and plain `cohN` |
| 5 | `cohW∘` | `W∘`; three `cohW`; plain and weakened `cohA`; `cohN` |

## The 3-cell lemmas

These are the expected decompositions. Each is an equation between two
2-cells with the same source and target, i.e. a 3-cell; they are
propositions, since the targets are 2-types.

**Codes**

1. `T3` (associativity of `T`): for codes `σ → τ → ρ → μ`, the two ways from
   `(≈c₁ ∙ ≈c₂) ∙ ≈c₃` to `≈c₁₂₃` agree:
   `cong (_∙ ≈c₃) T(c₁,c₂,c₁₂) ∙ T(c₁₂,c₃,c₁₂₃) ≡ assoc ∙ cong (≈c₁ ∙_) T(c₂,c₃,c₂₃) ∙ T(c₁,c₂₃,c₁₂₃)`.
   Needed by every hole.

**Compositor**

2. `RT` (`R` is functorial in codes): pasting `R(c)` and `R(d)` and then
   `T` on the right equals `R(cd)` after `cong ⟦δ⟧ T(c,d,cd)`. Hole 0.
3. `LT` (`L` is functorial in codes): the same for `L`. Holes 2, 3, 5.
4. `RL` (interchange): for a code on `δ` and a code on `σ`, the two ways
   around the square from `∘(δ,σ)` to `∘(δ₂,τ)` (first `R` then `L`, or first
   `L` then `R`) agree. Hole 1.

**Associator**

5. `AsR` (naturality in the third argument): relates `As(ρ,δ,σ)` and
   `As(ρ,δ,τ)` through `R` at `ρ∘δ`, at `ρ` (on `δσ → δτ`) and, under
   `cong ⟦ρ⟧`, at `δ`. Hole 1.
6. `AsM` (naturality in the second argument): relates `As(ρ,δ,σ)` and
   `As(ρ,δ₂,σ)` through `L` at `σ`, `R` at `ρ`, and `L` under `cong ⟦ρ⟧`.
   Hole 2.
7. `AsL` (naturality in the first argument): relates `As(ρ,…)` and
   `As(ρ₂,…)` through `L`. Holes 3, 5.
8. `Pent` (pentagon): for four thinnings, the two ways of re-associating
   `∘` over `δD, ρ, δ, σ` agree. Hole 3.

**Weakening**

9. `WNT` (`WN` is functorial in codes). Hole 4.
10. `W∘R` (naturality of `W∘` in the right argument): relates `W∘(δ,σ)`,
    `W∘(δ,τ)`, `WN`, `R` and weakened `R`. Hole 4.
11. `W∘L` (naturality of `W∘` in the left argument). Hole 5.
12. `W∘As` (compatibility of `W∘` with the associator): for three thinnings,
    the weakened `As`, the plain `As` at the unweakened point, and the `W∘`
    and `u` cells paste consistently. Hole 5.

Besides these, generic path algebra (pure J): naturality of `lemN`, `lemA`,
`lemW`, `compS`, `imgS`, `imgSU` and the transports in their hypotheses.

## How they would be proved

Mutually with the 2-cell lemmas, by induction on the thinnings, as in `Sem1`:

- the `tε` and `t-d` cases reduce, because the 2-cell lemmas compute there;
- in the `t-k` cases, a 3-cell between two `pathK` pastings splits into a base
  3-cell (the induction hypothesis) and a stored-path component. That
  component is an equality between equalities in a set, hence automatic in
  2-types. So the tower stops here.

## The pattern

This layer relates to the 2-cell layer as the 2-cell layer relates to the
1-cells: every statement is an equation between two given parallel cells, so
no boundary data is ever needed. The 3-cells are the pseudofunctor axioms one
level up (functoriality and interchange of the naturality cells, naturality
of the associator, the pentagon, and the corresponding weakening laws). For a
uniform version with `k : ℕ`, the next step would be to describe these
layers as instances of one statement ("parallel pastings of the generators
agree") generated by induction on the dimension.
