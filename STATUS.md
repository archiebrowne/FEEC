# Status

`lake build` succeeds. There is no `sorry`, no `axiom` and no `native_decide` in the
library; the headline theorems depend only on `propext`, `Classical.choice`, `Quot.sound`.
About 3400 lines of Lean on Mathlib v4.35.0. Headline statements are collected in
`FEEC/Main.lean`.

## What is proved

| File | Content | Arnold |
|------|---------|--------|
| `Hilbert/InfSup.lean` | Babuška–Nečas for symmetric forms | — |
| `Hilbert/ShortComplex.lean` | three-term Hilbert complexes; `𝔷`, `𝔅`, `𝔥`; Hodge decomposition and its uniqueness; `𝔥 ≃ 𝔷 ⧸ 𝔅` | §4.1–4.2, Thm 4.5 |
| `Hilbert/Poincare.lean` | Poincaré inequality from closed range; closedness of `𝔅`; bounded potentials; finite-dimensional case | Thm 4.6 |
| `Hilbert/HodgeLaplace.lean` | mixed weak formulation; a priori estimate with explicit constant `stabilityConst c = 18 max(c,1)²`; existence and uniqueness | §4.4, Thm 4.8–4.9 |
| `Hilbert/Complex.lean` | `ℕ`-indexed `HilbertComplex`, its segments, closed complexes | §4.1 |
| `Discrete/Subcomplex.lean` | subcomplexes, bounded cochain projections, discrete Poincaré inequality (`c · K`) | §5.2, Thm 5.3 |
| `Discrete/Harmonic.lean` | gap between harmonic and discrete harmonic forms | Thm 5.2 |
| `Discrete/ErrorEstimate.lean` | stability of the Galerkin method; quasi-optimal error estimate with explicit `errorConst c K` | Thm 5.4, 5.5 |
| `Discrete/Complex.lean` | subcomplexes and cochain projections of `ℕ`-indexed complexes | §5.2 |
| `DeRham/Koszul.lean` | Koszul operator, `κ² = 0`, homotopy formula `(dκ + κd)ω = (k+1)ω + Dω(x)x` | §7.2 |
| `DeRham/Homogeneous.lean` | `𝓗ᵣΛᵏ`, Euler identity, `(dκ + κd)ω = (r+k)ω`, exactness, independence of degrees | §7.1–7.2, Thm 7.1 |
| `DeRham/Polynomial.lean` | `𝓟ᵣΛᵏ`, `𝓟ᵣ⁻Λᵏ`, inclusions, exactness of both polynomial de Rham complexes | §7.2–7.3 |
| `DeRham/Covector.lean` | Euclidean inner product on `k`-covectors | §6.1 |
| `DeRham/Codifferential.lean` | codifferential `δ`, `δ² = 0`, test forms | §6.2 |
| `DeRham/L2Complex.lean` | weak exterior derivative, its uniqueness, `HΛᵏ(Ω)`; **the `L²` de Rham complex is a `HilbertComplex`** | §6.2 |
| `DeRham/Classical.lean` | `δ` is the formal adjoint of `d`; `C¹` forms have weak `d` = `extDeriv`; polynomial forms lie in `HΛᵏ(Ω)` for bounded `Ω` | §6.2 |

## Deviations from the plan / things to know

* **Error estimate needs `0 ≤ μ`.** The statement first drafted without it is false
  (if `𝔥 = 0` the hypothesis on `μ` is vacuous). The hypothesis is now explicit.
* **Homogeneous forms are defined by smoothness + homogeneity**
  (`ω (t • x) = t ^ r • ω x` for all real `t`), not as polynomials in coordinates. Such maps
  are exactly the homogeneous polynomial forms, but that equivalence is not proved, and there
  are no dimension counts.
* `polyFormsMinus E r k` is Arnold's `𝓟⁻ᵣ₊₁Λᵏ` (index shift).
* `IsGenSolution.norm_le` in `HodgeLaplace.lean` uses `set_option maxHeartbeats 1600000`;
  it should be split into smaller lemmas.
* Linter warnings (unused simp arguments, deprecated names, long lines) have not been cleaned.

## Not done (see `docs/plan/00-overview.md`)

* Closedness of the `L²` de Rham complex (Poincaré inequality on Lipschitz domains): the
  de Rham well-posedness theorem `deRham_hodgeLaplace_wellPosed` takes it as a hypothesis.
* Meshes, Whitney forms on a triangulation, degrees of freedom, unisolvence, and the
  construction of bounded cochain projections: existence of a cochain projection is a
  hypothesis of the discretisation theorems. In particular no concrete finite element
  subcomplex of `deRhamComplex` is constructed (the polynomial spaces are shown to lie in
  `HΛ` on a single bounded open set, but are not packaged as a `Subcomplex`).
* Improved error estimates (Arnold Thm 5.6), eigenvalue problems, the adjoint `d*` and the
  strong form of the Hodge Laplacian.
