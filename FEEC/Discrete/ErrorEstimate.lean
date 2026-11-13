/-
Stability and quasi-optimal error estimate for the discrete mixed Hodge Laplacian.
-/
import FEEC.Discrete.Harmonic

/-!
# Stability and convergence of the Galerkin method for the Hodge Laplacian

Let `Vh` be a subcomplex of a short Hilbert complex `S` with Poincaré constant `c`, admitting
a cochain projection `π` with `‖π‖ ≤ K`. The Galerkin method for the mixed Hodge Laplace
problem is `Vh.toShort.IsSolution f σh uh ph`.

## Main results

* `CochainProjection.exists_discrete_isSolution`, `CochainProjection.discrete_norm_le`:
  **stability** (Arnold, Theorem 5.4): the discrete problem is well posed, with stability
  constant `stabilityConst (c * K)` independent of the subcomplex.
* `CochainProjection.error_estimate`: the **quasi-optimal error estimate**
  (Arnold, Theorem 5.5):
  `‖σ - σh‖ + ‖u - uh‖ + ‖p - ph‖ ≤ C (inf ‖σ - τ‖ + inf ‖u - v‖ + inf ‖p - q‖ + μ inf ‖P_𝔅 u - w‖)`
  where the infima are over the discrete spaces, all norms are `V`-norms, and
  `C = errorConst c K`.
-/

namespace FEEC

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- The constant in the quasi-optimal error estimate, as a function of the Poincaré constant
`c` and the bound `K` on the cochain projection. -/
noncomputable def errorConst (c K : ℝ) : ℝ := (1 + stabilityConst (c * K)) * (3 + K)

namespace ShortHilbertComplex

variable {W₀ W₁ W₂ V₀ V₁ : Type*}
  [NormedAddCommGroup W₀] [InnerProductSpace ℝ W₀]
  [NormedAddCommGroup W₁] [InnerProductSpace ℝ W₁]
  [NormedAddCommGroup W₂] [InnerProductSpace ℝ W₂]
  [NormedAddCommGroup V₀] [InnerProductSpace ℝ V₀]
  [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁]
  {S : ShortHilbertComplex W₀ W₁ W₂ V₀ V₁}

namespace CochainProjection

variable {Vh : S.Subcomplex} (π : S.CochainProjection Vh)
  [CompleteSpace V₀] [CompleteSpace V₁] [CompleteSpace Vh.carrier₀] [CompleteSpace Vh.carrier₁]

/-- **Stability of the Galerkin method** (Arnold, Theorem 5.4): existence of the discrete
solution. -/
theorem exists_discrete_isSolution {c K : ℝ} (hc : S.HasPoincareConst c)
    (hK₀ : ‖π.π₀‖ ≤ K) (hK₁ : ‖π.π₁‖ ≤ K) (f : W₁) :
    ∃ σh uh ph, Vh.toShort.IsSolution f σh uh ph := by
  sorry

/-- **Stability of the Galerkin method** (Arnold, Theorem 5.4): the discrete solution is
bounded by the data with a constant depending only on `c` and `K`. -/
theorem discrete_norm_le {c K : ℝ} (hc : S.HasPoincareConst c)
    (hK₀ : ‖π.π₀‖ ≤ K) (hK₁ : ‖π.π₁‖ ≤ K) {f : W₁}
    {σh : Vh.carrier₀} {uh ph : Vh.carrier₁} (h : Vh.toShort.IsSolution f σh uh ph) :
    ‖σh‖ + ‖uh‖ + ‖ph‖ ≤ stabilityConst (c * K) * ‖f‖ := by
  sorry

/-- **Quasi-optimal error estimate for the mixed Hodge Laplacian** (Arnold, Theorem 5.5).
Let `(σ, u, p)` be the solution of the continuous problem and `(σh, uh, ph)` the Galerkin
solution in a subcomplex admitting a cochain projection bounded by `K`. Let `μ` bound
`‖(1 - π) r‖ / ‖r‖` on harmonic forms, and let `b = P_𝔅 u` be the coboundary part of `u`
(characterised by `b ∈ 𝔅`, `u - b ∈ 𝔷ᗮ`, since `u ⟂ 𝔥`). Then for all discrete
`τ, v, q, w`,
`‖σ - σh‖ + ‖u - uh‖ + ‖p - ph‖ ≤ C (‖σ - τ‖ + ‖u - v‖ + ‖p - q‖ + μ ‖b - w‖)`,
with `C = errorConst c K` depending only on the Poincaré constant and `K`. -/
theorem error_estimate {c K μ : ℝ} (hc : S.HasPoincareConst c)
    (hK₀ : ‖π.π₀‖ ≤ K) (hK₁ : ‖π.π₁‖ ≤ K)
    (hμ : ∀ r ∈ S.harmonic, ‖r - π.π₁ r‖ ≤ μ * ‖r‖)
    {f : W₁} {σ : V₀} {u p : V₁} (h : S.IsSolution f σ u p)
    {σh : Vh.carrier₀} {uh ph : Vh.carrier₁} (hh : Vh.toShort.IsSolution f σh uh ph)
    {b : V₁} (hb : b ∈ S.coboundaries) (hub : u - b ∈ S.cocyclesᗮ)
    (τ : Vh.carrier₀) (v q w : Vh.carrier₁) :
    ‖σ - σh‖ + ‖u - uh‖ + ‖p - ph‖ ≤
      errorConst c K * (‖σ - τ‖ + ‖u - v‖ + ‖p - q‖ + μ * ‖b - w‖) := by
  sorry

end CochainProjection

end ShortHilbertComplex

end FEEC
