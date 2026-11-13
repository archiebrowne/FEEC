/-
Headline theorems of the FEEC formalisation, collected in one place.
-/
import FEEC.Discrete.ErrorEstimate
import FEEC.Discrete.Complex
import FEEC.DeRham.L2Complex
import FEEC.DeRham.Polynomial

/-!
# Finite element exterior calculus: main results

This file restates the main theorems for `ℕ`-indexed Hilbert complexes and for the `L²`
de Rham complex. The Hodge Laplacian at level `k + 1` lives on `C.segment k`
(`V k → V (k+1) → W (k+2)`) and at level `0` on `C.segmentZero`; all statements below are
given for `C.segment k` and hold verbatim for `C.segmentZero`.

* `HilbertComplex.hodgeLaplace_wellPosed` — Arnold, Theorem 4.8.
* `HilbertComplex.galerkin_wellPosed` — Arnold, Theorem 5.4.
* `HilbertComplex.galerkin_error_estimate` — Arnold, Theorem 5.5.
* `deRham_hodgeLaplace_wellPosed` — the Hodge Laplacian on differential forms.
-/

namespace FEEC

open ShortHilbertComplex

namespace HilbertComplex

variable {W V : ℕ → Type*}
  [∀ k, NormedAddCommGroup (W k)] [∀ k, InnerProductSpace ℝ (W k)]
  [∀ k, NormedAddCommGroup (V k)] [∀ k, InnerProductSpace ℝ (V k)]
  [∀ k, CompleteSpace (W k)] [∀ k, CompleteSpace (V k)]
  (C : HilbertComplex W V)

/-- **Well-posedness of the Hodge Laplacian** on a closed Hilbert complex (Arnold,
Theorem 4.8): at each level the mixed weak formulation has a unique solution, bounded by the
data. -/
theorem hodgeLaplace_wellPosed (hC : C.IsClosed) (k : ℕ) :
    ∃ c : ℝ, (C.segment k).HasPoincareConst c ∧ ∀ f : W (k + 1), ∃ σ u p,
      (C.segment k).IsSolution f σ u p ∧ ‖σ‖ + ‖u‖ + ‖p‖ ≤ stabilityConst c * ‖f‖ ∧
      ∀ σ' u' p', (C.segment k).IsSolution f σ' u' p' → σ' = σ ∧ u' = u ∧ p' = p := by
  obtain ⟨c, hc⟩ := C.exists_hasPoincareConst_segment hC k
  refine ⟨c, hc, fun f => ?_⟩
  obtain ⟨σ, u, p, h⟩ := exists_isSolution hc f
  exact ⟨σ, u, p, h, h.norm_le hc, fun σ' u' p' h' => h'.unique hc h⟩

/-- Well-posedness of the Hodge Laplacian at level `0`. -/
theorem hodgeLaplace_wellPosed_zero (hC : C.IsClosed) :
    ∃ c : ℝ, C.segmentZero.HasPoincareConst c ∧ ∀ f : W 0, ∃ σ u p,
      C.segmentZero.IsSolution f σ u p ∧ ‖σ‖ + ‖u‖ + ‖p‖ ≤ stabilityConst c * ‖f‖ ∧
      ∀ σ' u' p', C.segmentZero.IsSolution f σ' u' p' → σ' = σ ∧ u' = u ∧ p' = p := by
  obtain ⟨c, hc⟩ := C.exists_hasPoincareConst_segmentZero hC
  refine ⟨c, hc, fun f => ?_⟩
  obtain ⟨σ, u, p, h⟩ := exists_isSolution hc f
  exact ⟨σ, u, p, h, h.norm_le hc, fun σ' u' p' h' => h'.unique hc h⟩

variable {C}
variable {Vh : C.Subcomplex} [∀ k, CompleteSpace (Vh.carrier k)]

/-- **Stability of the Galerkin method** (Arnold, Theorem 5.4). For a subcomplex admitting a
cochain projection bounded by `K`, the discrete Hodge Laplace problem is well posed with a
stability constant depending only on the Poincaré constant `c` of the complex and on `K`. -/
theorem galerkin_wellPosed (π : C.CochainProjection Vh) {c K : ℝ} (k : ℕ)
    (hc : (C.segment k).HasPoincareConst c) (hK : ∀ j, ‖π.π j‖ ≤ K) (f : W (k + 1)) :
    ∃ σh uh ph, (Vh.segment k).toShort.IsSolution f σh uh ph ∧
      ‖σh‖ + ‖uh‖ + ‖ph‖ ≤ stabilityConst (c * K) * ‖f‖ ∧
      ∀ σ' u' p', (Vh.segment k).toShort.IsSolution f σ' u' p' → σ' = σh ∧ u' = uh ∧ p' = ph := by
  have hc' := (π.segment k).hasPoincareConst hc (hK k) (hK (k + 1))
  obtain ⟨σ, u, p, h⟩ := exists_isSolution hc' f
  exact ⟨σ, u, p, h, h.norm_le hc', fun σ' u' p' h' => h'.unique hc' h⟩

/-- **Convergence of the Galerkin method for the Hodge Laplacian** (Arnold, Theorem 5.5).
Let `(σ, u, p)` solve the Hodge Laplace problem at level `k + 1` and `(σh, uh, ph)` the
Galerkin problem in a subcomplex with a cochain projection bounded by `K`. Then the error is
quasi-optimal: it is bounded by the best approximation errors of `σ`, `u`, `p` in the discrete
spaces, plus `μ` times the best approximation error of the coboundary part `b = P_𝔅 u`, where
`μ` measures how well `π` preserves harmonic forms. The constant depends only on the Poincaré
constant and on `K`. -/
theorem galerkin_error_estimate (π : C.CochainProjection Vh) {c K μ : ℝ} (k : ℕ)
    (hc : (C.segment k).HasPoincareConst c) (hK : ∀ j, ‖π.π j‖ ≤ K) (hμ₀ : 0 ≤ μ)
    (hμ : ∀ r ∈ (C.segment k).harmonic, ‖r - π.π (k + 1) r‖ ≤ μ * ‖r‖)
    {f : W (k + 1)} {σ : V k} {u p : V (k + 1)} (h : (C.segment k).IsSolution f σ u p)
    {σh : Vh.carrier k} {uh ph : Vh.carrier (k + 1)}
    (hh : (Vh.segment k).toShort.IsSolution f σh uh ph)
    {b : V (k + 1)} (hb : b ∈ (C.segment k).coboundaries)
    (hub : u - b ∈ (C.segment k).cocyclesᗮ)
    (τ : Vh.carrier k) (v q w : Vh.carrier (k + 1)) :
    ‖σ - σh‖ + ‖u - uh‖ + ‖p - ph‖ ≤
      errorConst c K * (‖σ - τ‖ + ‖u - v‖ + ‖p - q‖ + μ * ‖b - w‖) :=
  (π.segment k).error_estimate hc (hK k) (hK (k + 1)) hμ₀ hμ h hh hb hub τ v q w

end HilbertComplex

/-! ### The de Rham complex -/

section DeRham

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Set E}

instance (k : ℕ) : CompleteSpace (Covector E k) := FiniteDimensional.complete ℝ _

/-- **The Hodge Laplacian on differential forms.** If the `L²` de Rham complex of the open set
`Ω` is closed (as it is for bounded Lipschitz domains), then for every `f ∈ L²Λᵏ⁺¹(Ω)` the
mixed problem: find `σ ∈ HΛᵏ`, `u ∈ HΛᵏ⁺¹`, `p ∈ 𝔥ᵏ⁺¹` with `σ = d* u`, `dσ + d* du + p = f`,
`u ⟂ 𝔥ᵏ⁺¹`, has a unique solution, depending continuously on `f`. -/
theorem deRham_hodgeLaplace_wellPosed (hΩ : IsOpen Ω) (hC : (deRhamComplex hΩ).IsClosed)
    (k : ℕ) :
    ∃ c : ℝ, ∀ f : L2Form Ω (k + 1), ∃ σ u p,
      ((deRhamComplex hΩ).segment k).IsSolution f σ u p ∧
      ‖σ‖ + ‖u‖ + ‖p‖ ≤ stabilityConst c * ‖f‖ ∧
      ∀ σ' u' p', ((deRhamComplex hΩ).segment k).IsSolution f σ' u' p' →
        σ' = σ ∧ u' = u ∧ p' = p := by
  obtain ⟨c, -, h⟩ := (deRhamComplex hΩ).hodgeLaplace_wellPosed hC k
  exact ⟨c, h⟩

end DeRham

end FEEC
