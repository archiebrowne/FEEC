# Part E — an unconditional convergence theorem on a mesh (one dimension)

Goal: instantiate the abstract theory completely, with no hypothesis left over, for the
`L²` de Rham complex of an interval `Ω = (a, b) ⊂ ℝ` and an arbitrary mesh
`a = x₀ < x₁ < ⋯ < x_N = b` with mesh size `h = max (xᵢ₊₁ − xᵢ)`.

The complex is `0 → HΛ⁰ = H¹(a,b) --d--> HΛ¹ ≅ L²(a,b) → 0 → ⋯` (`deRhamComplex` with
`E = ℝ`). The Hodge Laplacian on 1-forms (`segment 0`) is the mixed formulation of
`−u″ = f`, `u(a) = u(b) = 0`: find `σ ∈ H¹`, `u ∈ L²` with `⟪σ,τ⟫ = ⟪τ′,u⟫`, `⟪σ′,v⟫ = ⟪f,v⟫`.

**Theorem (`interval_mixed_convergence`).** There is `C` depending only on `(a, b)` such
that for every mesh, every `f = ⋆φ` with `φ ∈ H¹(a,b)`, the continuous solution `(σ,u,p)`
and the Galerkin solution `(σh,uh,ph)` in continuous piecewise linears × piecewise
constants satisfy `‖σ − σh‖_{H¹} + ‖u − uh‖_{L²} + ‖p − ph‖ ≤ C h ‖φ‖_{H¹}`.

## Ingredients

1. **`Discrete/Lift.lean` (abstract).** For a surjective bounded `T : X → Y` between Hilbert
   spaces and a bounded `Q : Y → Y`, the operator `P = P_{ker T} + R Q T`, with `R` the inverse
   of `T` on `(ker T)ᗮ`, satisfies `T P = Q T`, `P x = x` when `Q T x = T x`,
   `x − P x ∈ (ker T)ᗮ`, and `‖P‖ ≤ 1 + c ‖Q‖ ‖T‖` if `‖x‖ ≤ c ‖T x‖` on `(ker T)ᗮ`.
   In 1D with `T = d`, `Q` = `L²` projection onto piecewise constants this is a bounded
   cochain projection onto `{u | u′ piecewise constant}` = continuous piecewise linears,
   with bound `1 + c_P` independent of the mesh.

2. **`Interval/Scalar.lean` (scalar Sobolev toolkit).** `L2I a b = L²(a,b)`; weak derivative
   `HasWeakDeriv u g`; the primitive `x ↦ ∫ₐˣ g` of `g ∈ L²` has weak derivative `g` (Fubini);
   du Bois-Reymond: a function with zero weak derivative is a.e. constant, hence
   `u = c + ∫ₐˣ g` a.e.; meshes; piecewise constants `M.pcConst`; approximation
   `∃ s ∈ M.pcConst, ‖u − s‖ ≤ h ‖u′‖` (cellwise: `|u(x) − ū| ≤ √hᵢ ‖u′‖_{L²(cell)}`).

3. **`Interval/Bridge.lean`.** Isometries `s0 : L²Λ⁰ ≃ L²`, `s1 : L²Λ¹ ≃ L²` (so
   `⋆ = s1⁻¹ ∘ s0`), `HasWeakExtDeriv u η ↔ HasWeakDeriv (s0 u) (s1 η)` (in 1D
   `δ(g dx) = −g′`), and `L²Λᵏ = 0` for `k ≥ 2`. Also identifies the Euclidean volume on
   `ℝ` with Lebesgue measure.

4. **`Interval/Convergence.lean`.**
   * `d : HΛ⁰ → HΛ¹` is surjective (primitives), `HΛᵏ = 0` for `k ≥ 2`: the complex is closed.
   * Mesh subcomplex: `carrier 1` = piecewise constants, `carrier 0 = d⁻¹(carrier 1)`,
     `carrier (k+2) = ⊤`.
   * Cochain projection: `π¹` = orthogonal projection, `π⁰` = lift of `π¹`, `πᵏ⁺² = id`;
     `‖π‖ ≤ 1 + c_P`.
   * `𝔥¹ = 0` (as `𝔅¹` is everything), so `μ = 0`, `p = 0`, and `P_𝔅 u = u`.
   * Regularity is automatic: eq. 1 gives `σ′ = f`; eq. 0 tested with test functions gives
     `u′ = −σ` weakly. Hence `inf ‖u − v‖ ≤ h ‖σ‖ ≤ h · stab · ‖f‖` and
     `‖σ − π⁰σ‖_V ≤ c_P ‖(1 − π¹) f‖ ≤ c_P h ‖φ′‖` (using `σ − π⁰σ ∈ (ker d)ᗮ`).
   * Plug into `galerkin_error_estimate`.

## Not covered

Dimension `n ≥ 2`: simplicial meshes, trace continuity, smoothed projections, closedness on
Lipschitz domains. Higher polynomial degree in 1D. Rates for the 0-form (Neumann) problem.
