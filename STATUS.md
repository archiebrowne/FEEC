# Status

`lake build` succeeds. There is no `sorry`, no `axiom` and no `native_decide` in the
library; the headline theorems depend only on `propext`, `Classical.choice`, `Quot.sound`.
About 5500 lines of Lean on Mathlib v4.35.0. Headline statements are collected in
`FEEC/Main.lean`; the fully unconditional end-to-end result is
`FEEC.Interval.interval_mixed_convergence` in `FEEC/Interval/Convergence.lean`.

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
| `DeRham/Whitney.lean` | smooth forms in `HΛᵏ(Ω)` on bounded open `Ω`; `𝓟ᵣΛ` and `𝓟ᵣ⁻Λ` as `Subcomplex`es of the `L²` de Rham complex; Whitney forms `𝓟₁⁻Λᵏ` are finite-dimensional, their Galerkin problem is well posed, and the Whitney complex has no discrete harmonic forms in positive degree | §7.2–7.4 |
| `Discrete/Lift.lean` | lifting a bounded projection through a surjective `d`: a cochain projection one degree down with norm `≤ 1 + c_P` | — |
| `Interval/Scalar.lean` | weak derivatives on `(a,b)`, primitives, du Bois-Reymond, `u = c + ∫ₐˣ u′`, meshes, piecewise constants, `‖u − s‖ ≤ h‖u′‖` | — |
| `Interval/Bridge.lean` | `L²Λ⁰, L²Λ¹` of an interval are isometric to `L²(a,b)`; weak `d` = weak derivative; no forms of degree `≥ 2` | §6.2 |
| `Interval/Convergence.lean` | **end-to-end in 1D with no hypotheses**: the interval's de Rham complex is closed; mesh subcomplex (continuous `P₁` / `P₀`); cochain projection bounded uniformly in the mesh; quasi-optimality; `O(h)` convergence of the mixed method for `−u″ = f` | Thm 5.5 instantiated |

## Deviations from the plan / things to know

* **Error estimate needs `0 ≤ μ`.** The statement first drafted without it is false
  (if `𝔥 = 0` the hypothesis on `μ` is vacuous). The hypothesis is now explicit.
* **Homogeneous forms are defined by smoothness + homogeneity**
  (`ω (t • x) = t ^ r • ω x` for all real `t`), not as polynomials in coordinates. Such maps
  are exactly the homogeneous polynomial forms, but that equivalence is not proved, and there
  are no dimension counts.
* `polyFormsMinus E r k` is Arnold's `𝓟⁻ᵣ₊₁Λᵏ` (index shift).
* `IsGenSolution.norm_le` in `HodgeLaplace.lean` uses `set_option maxHeartbeats 1600000`;
  it should be split into smaller lemmas. `whitney_harmonic_eq_bot` uses 400000.
* Linter warnings (unused simp arguments, deprecated names, long lines) have not been cleaned.

## What "unconditional" covers

`interval_mixed_convergence`: for every mesh `M` of `(a,b)` and data `f = ⋆φ`, `φ ∈ H¹`,
`‖σ − σh‖_{H¹} + ‖u − uh‖_{L²} + ‖p − ph‖ ≤ C · M.size · ‖φ‖_{H¹}` with `C` depending only on
`(a,b)`. Existence of both solutions is `exists_isSolution` / `exists_discrete_isSolution`.
This is one space dimension, lowest order, the 1-form (Dirichlet mixed) problem only. In
dimension `n ≥ 2` bounded cochain projections remain hypotheses; closedness is proved on
boxes (next section).

## The `L²` Poincaré lemma on a box (plan: `docs/plan/05-poincare-lemma.md`)

For `Ω = box e a b = {x | ∀ i, aᵢ < ⟪eᵢ, x⟫ < bᵢ}` (`e` an orthonormal basis of `E`,
`aᵢ < bᵢ`), in any dimension and every degree, all in `DeRham/PoincareLemma.lean`:

* `exists_hasWeakExtDeriv_of_closed`: every weakly closed `ω ∈ L²Λᵏ⁺¹(Ω)` is `dη` with
  `‖η‖ ≤ C‖ω‖`.
* `boxComplex_isClosed`: the `L²` de Rham complex of `Ω` is closed.
* `box_harmonic_eq_bot`: no harmonic forms of degree `≥ 1`.
* `box_hodgeLaplace_wellPosed`: the Hodge Laplace problem at level `k + 1` is well posed
  with no hypothesis (and `p = 0`).

Supporting files: `Wedge.lean` (exterior multiplication by a covector, anticommutation with
contraction), `LineIntegral.lean`, `LineG.lean`, `LineL2.lean` (integrals along lines,
compactly supported antiderivatives, an `L²` bound), `TestForm.lean`, `BoxHomotopy.lean`
(the identity `δS + Sδ = 1 − Q` in one direction), `BoxBounds.lean`, `BoxDecomp.lean`
(every test form of positive degree is `δψ + χ` with `‖χ‖ ≤ C‖δφ‖`).

Limits: boxes only, not general star-shaped or Lipschitz domains. The level-0 problem
(`segmentZero`) is covered by closedness through the general theorem
`hodgeLaplace_wellPosed_zero`, but is not restated for boxes, and `ker d` on `HΛ⁰` is not
identified with the constants. The Poincaré constant is not explicit.

## Not done (see `docs/plan/00-overview.md`)

* Closedness of the `L²` de Rham complex on domains other than boxes (star-shaped,
  Lipschitz): there `deRham_hodgeLaplace_wellPosed` still takes it as a hypothesis.
* Meshes and inter-element continuity, degrees of freedom, unisolvence, and the construction
  of bounded cochain projections: existence of a cochain projection is a hypothesis of the
  uniform stability and error estimate theorems, so these are not yet instantiated for a
  concrete finite element space. `DeRham/Whitney.lean` treats a single element (a bounded
  open set); Whitney forms are the space `𝓟₁⁻Λᵏ`, not the barycentric formula (Mathlib has
  no wedge product of continuous alternating maps).
* Improved error estimates (Arnold Thm 5.6), eigenvalue problems, the adjoint `d*` and the
  strong form of the Hodge Laplacian.
