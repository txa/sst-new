# A stabilised universe for relativity (sketch)

Context: defining SST by the décalage recursion (as in displayed type theory)
needs the display of the universe to be families, `Uᵈ A ≅ A → U`
(relativity). Reboullet (thesis, Paris Cité 2025) shows that in the nominal
(BCM) model of internal parametricity relativity fails for U, but that

    Path(U, A) ≅ Π(A, Path(U, 1))        (her Prop. 3.4.6, refined model)

So a universe V with `Path(V, 1) ≅ V` would satisfy relativity. This note
computes such a V as a fixed point of `X ↦ Path(X, 1)`. Status: sketch, not
formalised; open points are listed at the end.

## Setup (unary nominal model, empty context)

- `N(n, m)` = partial injections `[n] ⇀ [m]`; nominal sets are functors
  `N → Set`.
- A type over the n-cube is a functor `A : n/N → Set`; `A(f)` for
  `f : n ⇀ y` is the fibre at that cube (f undefined at k: direction k at its
  endpoint; `f(k) = j`: direction k has become name j).
- `U(n)` = small such functors, action `(h·A)(f) = A(f ∘ h)`.
- `Path(W, w)(n) = { t ∈ W(n+1) | e·t = wₙ }`, where `e : n+1 ⇀ n` forgets
  the last direction. Since this is `W(x+1)` cut down by an equation, Path
  commutes with all limits and with filtered colimits.

Glue `g : U → Path(U, 1)`, for `f : n+1 ⇀ y`:

    g(A)(f) = 1                  if f(n+1) is undefined
    g(A)(f) = A(δᵢ ∘ f|ₙ)        if f(n+1) = i

where `δᵢ : y ⇀ y−1` deletes name i.

Generic fibre `r : Path(U, 1) → U`: `r(P)(f) = P(f⁺)`, where `f⁺` sends the
bridge direction to a fresh last name. Then `r ∘ g = id` strictly (the
section–retraction of Altenkirch et al. 2024).

## Reboullet's counterexample

Let `T(f) = {f(1)}`: a bridge over 1 whose fibre in direction i is `{i}`.

- For a glued type, the swap τ of names 1 and 2 acts between the fibres in
  directions 1 and 2 through `δ₂ ∘ τ ∘ δ₁⁻¹ = id`.
- For T it sends `{1}` to `{2}`. Hence T is not of the form `g(A)`.
- `r(T)(f : 0 ⇀ y) = {y+1}`: a singleton, but not 1.
- `g(r T)` has fibre `{2}` in both directions at y = 2, so `g(r T) ≠ T`.

## The tower

    X₀ = U,   X_{n+1} = Path(Xₙ, ptₙ),   pt₀ = 1,   pt_{n+1} = cₙ(ptₙ)
    c₀ = g,   c_{n+1} = Path(cₙ)          (similarly r₀ = r, r_{n+1} = Path(rₙ))

`Xₙ(x)` = types over x + n dimensions that are 1 whenever one of the last n
(hidden) directions is at its endpoint. `cₙ` glues on a new hidden direction
in the innermost position. Path adds its new direction in the outermost
position (x+1).

### Colimit, `V = colim_g Xₙ`

- `Path(V, *) = colim X_{n+1}` with maps `Path(cₙ) = c_{n+1}`: the tail of
  the sequence, hence `Path(V, *) ≅ V`. The iso keeps the underlying type and
  reinterprets the bridge direction as a hidden direction.
- Decoding: `El[t ∈ Xₙ] = rⁿ(t)`, well defined since `r ∘ g = id`.
- T has a code `[T] ≠ [1]` with `El[T]` a named singleton.
- **Problem (compactness):** every element has finite depth, but families
  `ℕ → V` can have unbounded depth. So `Π(A, colim) ≠ colim Π(A, −)` for
  infinite A: V is not closed under Π over infinite types, and relativity
  holds only for compact `El a`. Transfinite iteration does not help:
  `X_{ω+1} ≅ X_ω` already.

### Limit, `V = lim_r Xₙ`

- Path commutes with limits, so again `Path(V, *) ≅ V` by the tail argument
  (`Path(rₙ) = r_{n+1}`; r always specialises the innermost hidden direction).
- Π commutes with limits: `Π(A, V) = lim Π(A, Xₙ)`, no compactness condition.
- Relativity `Path(V, a) ≅ Π(El a, V)` follows from the stagewise iso
  `Path(Xₙ, a) ≅ Π(rⁿ a, X_{n+1})`, natural in n (n = 0 is Reboullet's
  Prop. 3.4.6).
- `El` = projection to `X₀ = U`.
- The colimit embeds: depth-n code a ↦ `(…, a, g a, g² a, …)`. In particular
  `(r T, T, g T, g² T, …) ∈ V`.
- Display of El (sketch): for a bridge t corresponding to a family F, the
  fibre of `El t` over u and `El(F u)` are both the fibre at the generic point
  above u.

## What is not fixed

In both versions the iso `Path(V, 1) ≅ V` is "hide the bridge direction",
not glueing. Glueing for V adds the new direction in the outermost position;
compatibility of the tower needs the innermost one. The two differ by exactly
the swap that glueing is insensitive to. T, viewed as a bridge in V, is still
not glued: its fibres are labelled by the name of the bridge direction.

- Type Surjectivity (glue onto bridges) fails for every V of this kind.
- Relativity holds as a natural isomorphism, whose components are
  Reboullet's F (isolate a fibre) and T (total space) operators
  (Remark 3.4.7), now landing in V itself.

| | colimit along g | limit along r |
|---|---|---|
| `Path(V, 1) ≅ V` | yes (shift) | yes (shift) |
| relativity | only compact El a | yes, given the stagewise iso |
| closed under Π | no | expected |
| contains T | yes | yes |
| glueing surjective | no | no |

## Open points

1. The stagewise relativity `Path(Xₙ, a) ≅ Π(rⁿ a, X_{n+1})` in the refined
   model.
2. `r(Π(a, b)) = Π(r a, r b)` (strictly, or at least naturally), so that Π
   commutes with the tower.
3. Whether a natural isomorphism suffices for dTT's display rules, or whether
   V must be strictified so that the display of the universe holds on the
   nose.

If these go through, the limit universe gives a décalage-style display
`Vᵈ A ≅ A → V` in a symmetric model, and hence a model in which SST is
definable by the dTT recursion.
