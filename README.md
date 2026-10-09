# A type theory for semi-simplicial types using only weakenings

An Agda development of a small type theory whose contexts are sequences of
type families and whose types are telescopes of the form `X (δ args)`, where
the arguments are selected from earlier entries by a *thinning*. It is
designed to represent semi-simplicial (and semi-cubical) types.

The syntax is an ordinary (inductive-inductive-recursive) Agda definition, not
a quotient. The only equation is the commuting square of a kept entry of a
thinning, and it is stored as data.

## Main version (top level, `--without-K`)

| File | Contents |
|---|---|
| `TT.agda` | The syntax. `t-k` stores a typed *code* `Code (δ ∘ σ) δ'` (encode–decode), which is a proposition by induction, so uniqueness of the stored proofs needs neither K nor Hedberg. Composition, identity, weakening and their laws. Soundness of codes. |
| `SST.agda` | Semi-simplicial types up to level 2, written by hand. |
| `SSTk.agda` | `SST : ℕ → Con`, defined by structural recursion following Section 3 of Altenkirch, Capriotti, Kraus, *Extending homotopy type theory with strict equality* (2016). |
| `Sem.agda` | The interpretation into Agda's `Set`. K-free, parameterised by `pair-irr` (UIP for the semantic types), which is used in two lemmas. |
| `SemK.agda` | The only file using K: proves `pair-irr` and instantiates `Sem`, with tests. |
| `plan.agda` | The original plan: semi-simplicial types up to level 4, written out. |

## Other directories

- `withK/`: the first version, with a plain `δ ∘ σ ≡ δ'` in `t-k` and K. Simplest to present.
- `experiments/`:
  - `hit/`: Kovács' optimised syntax as an untruncated HIT, and its standard model (all `refl`, K-free).
  - `freecomp/`: composition as a constructor, with proof-relevant derivations.
  - `prefix/`: variables pointing to a prefix of the context (blocked on associativity of prefix composition).
- `archive/`: superseded variants: a Boolean encoding of the equations, `Prop`-based versions, a decidable-equality skeleton, and the original rewriting version.

## Status

The syntax and the construction of `SST n` are free of K. The interpretation
still needs UIP for the semantic types (`pair-irr`), i.e. coherence of the
interpretation of composition; this is where the open problem remains.

Checked with Agda 2.6.5, no libraries needed.
