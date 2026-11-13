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
  exact Vh.toShort.exists_isSolution (π.hasPoincareConst hc hK₀ hK₁) f

/-- **Stability of the Galerkin method** (Arnold, Theorem 5.4): the discrete solution is
bounded by the data with a constant depending only on `c` and `K`. -/
theorem discrete_norm_le {c K : ℝ} (hc : S.HasPoincareConst c)
    (hK₀ : ‖π.π₀‖ ≤ K) (hK₁ : ‖π.π₁‖ ≤ K) {f : W₁}
    {σh : Vh.carrier₀} {uh ph : Vh.carrier₁} (h : Vh.toShort.IsSolution f σh uh ph) :
    ‖σh‖ + ‖uh‖ + ‖ph‖ ≤ stabilityConst (c * K) * ‖f‖ := by
  exact IsSolution.norm_le (π.hasPoincareConst hc hK₀ hK₁) h

/-- **Quasi-optimal error estimate for the mixed Hodge Laplacian** (Arnold, Theorem 5.5).
Let `(σ, u, p)` be the solution of the continuous problem and `(σh, uh, ph)` the Galerkin
solution in a subcomplex admitting a cochain projection bounded by `K`. Let `μ ≥ 0` bound
`‖(1 - π) r‖ / ‖r‖` on harmonic forms, and let `b = P_𝔅 u` be the coboundary part of `u`
(characterised by `b ∈ 𝔅`, `u - b ∈ 𝔷ᗮ`, since `u ⟂ 𝔥`). Then for all discrete
`τ, v, q, w`,
`‖σ - σh‖ + ‖u - uh‖ + ‖p - ph‖ ≤ C (‖σ - τ‖ + ‖u - v‖ + ‖p - q‖ + μ ‖b - w‖)`,
with `C = errorConst c K` depending only on the Poincaré constant and `K`. -/
theorem error_estimate {c K μ : ℝ} (hc : S.HasPoincareConst c)
    (hK₀ : ‖π.π₀‖ ≤ K) (hK₁ : ‖π.π₁‖ ≤ K) (hμ0 : 0 ≤ μ)
    (hμ : ∀ r ∈ S.harmonic, ‖r - π.π₁ r‖ ≤ μ * ‖r‖)
    {f : W₁} {σ : V₀} {u p : V₁} (h : S.IsSolution f σ u p)
    {σh : Vh.carrier₀} {uh ph : Vh.carrier₁} (hh : Vh.toShort.IsSolution f σh uh ph)
    {b : V₁} (hb : b ∈ S.coboundaries) (hub : u - b ∈ S.cocyclesᗮ)
    (τ : Vh.carrier₀) (v q w : Vh.carrier₁) :
    ‖σ - σh‖ + ‖u - uh‖ + ‖p - ph‖ ≤
      errorConst c K * (‖σ - τ‖ + ‖u - v‖ + ‖p - q‖ + μ * ‖b - w‖) := by
  have hK : 0 ≤ K := (norm_nonneg _).trans hK₁
  have hc' := π.hasPoincareConst hc hK₀ hK₁
  have hB := hc.isClosed_coboundaries
  obtain ⟨q', hq'h, hq'⟩ := π.exists_discrete_harmonic_near h.harmonic
  have hq'2 : ‖p - (q' : V₁)‖ ≤ (1 + K) * ‖p - (q : V₁)‖ :=
    hq'.trans (π.norm_sub_π₁_le hK₁ p q.2)
  have hA := norm_nonneg (σ - (τ : V₀))
  have hB' := norm_nonneg (u - (v : V₁))
  have hD := norm_nonneg (p - (q : V₁))
  have hm : 0 ≤ μ * ‖b - (w : V₁)‖ := mul_nonneg hμ0 (norm_nonneg _)
  have hCp := norm_nonneg (p - (q' : V₁))
  obtain ⟨F₀, hF₀, hF₀n⟩ : ∃ F₀ : Vh.carrier₀ →L[ℝ] ℝ,
      (∀ τ', F₀ τ' = ⟪S.ι₀ (σ - τ), S.ι₀ τ'⟫ - ⟪S.ι₁ (u - v), S.ι₁ (S.d₀ τ')⟫) ∧
      ‖F₀‖ ≤ ‖σ - (τ : V₀)‖ + ‖u - (v : V₁)‖ := by
    refine ⟨(innerSL ℝ (S.ι₀ (σ - τ))).comp Vh.toShort.ι₀ -
      ((innerSL ℝ (S.ι₁ (u - v))).comp Vh.toShort.ι₁).comp Vh.toShort.d₀, fun τ' => rfl, ?_⟩
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun τ' => ?_
    have e : (((innerSL ℝ (S.ι₀ (σ - τ))).comp Vh.toShort.ι₀ -
      ((innerSL ℝ (S.ι₁ (u - v))).comp Vh.toShort.ι₁).comp Vh.toShort.d₀) τ') =
        ⟪S.ι₀ (σ - τ), S.ι₀ τ'⟫ - ⟪S.ι₁ (u - v), S.ι₁ (S.d₀ τ')⟫ := rfl
    rw [e]
    have h1 : |⟪S.ι₀ (σ - τ), S.ι₀ τ'⟫| ≤ ‖σ - (τ : V₀)‖ * ‖τ'‖ :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul (S.norm_ι₀_le _) (S.norm_ι₀_le _)
        (norm_nonneg _) (norm_nonneg _))
    have h2 : |⟪S.ι₁ (u - v), S.ι₁ (S.d₀ τ')⟫| ≤ ‖u - (v : V₁)‖ * ‖τ'‖ := by
      refine (abs_real_inner_le_norm _ _).trans (mul_le_mul (S.norm_ι₁_le _) ?_
        (norm_nonneg _) (norm_nonneg _))
      rw [S.norm_ι₁_d₀]
      exact (S.norm_d₀_le _)
    rw [Real.norm_eq_abs]
    calc _ ≤ |⟪S.ι₀ (σ - τ), S.ι₀ τ'⟫| + |⟪S.ι₁ (u - v), S.ι₁ (S.d₀ τ')⟫| := abs_sub _ _
      _ ≤ _ := by nlinarith
  obtain ⟨F₁, hF₁, hF₁n⟩ : ∃ F₁ : Vh.carrier₁ →L[ℝ] ℝ,
      (∀ v', F₁ v' = ⟪S.ι₁ (S.d₀ (σ - τ)), S.ι₁ v'⟫ + ⟪S.d₁ (u - v), S.d₁ v'⟫ +
        ⟪S.ι₁ (p - q'), S.ι₁ v'⟫) ∧
      ‖F₁‖ ≤ ‖σ - (τ : V₀)‖ + ‖u - (v : V₁)‖ + ‖p - (q' : V₁)‖ := by
    refine ⟨((innerSL ℝ (S.ι₁ (S.d₀ (σ - τ)))).comp Vh.toShort.ι₁ +
      (innerSL ℝ (S.d₁ (u - v))).comp Vh.toShort.d₁ +
      (innerSL ℝ (S.ι₁ (p - q'))).comp Vh.toShort.ι₁), fun v' => rfl, ?_⟩
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v' => ?_
    have e : (((innerSL ℝ (S.ι₁ (S.d₀ (σ - τ)))).comp Vh.toShort.ι₁ +
      (innerSL ℝ (S.d₁ (u - v))).comp Vh.toShort.d₁ +
      (innerSL ℝ (S.ι₁ (p - q'))).comp Vh.toShort.ι₁) v') =
        ⟪S.ι₁ (S.d₀ (σ - τ)), S.ι₁ v'⟫ + ⟪S.d₁ (u - v), S.d₁ v'⟫ +
        ⟪S.ι₁ (p - q'), S.ι₁ v'⟫ := rfl
    rw [e]
    have h1 : |⟪S.ι₁ (S.d₀ (σ - τ)), S.ι₁ v'⟫| ≤ ‖σ - (τ : V₀)‖ * ‖v'‖ := by
      refine (abs_real_inner_le_norm _ _).trans (mul_le_mul ?_ (S.norm_ι₁_le _)
        (norm_nonneg _) (norm_nonneg _))
      rw [S.norm_ι₁_d₀]
      exact (S.norm_d₀_le _)
    have h2 : |⟪S.d₁ (u - v), S.d₁ v'⟫| ≤ ‖u - (v : V₁)‖ * ‖v'‖ :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul (S.norm_d₁_le _) (S.norm_d₁_le _)
        (norm_nonneg _) (norm_nonneg _))
    have h3 : |⟪S.ι₁ (p - q'), S.ι₁ v'⟫| ≤ ‖p - (q' : V₁)‖ * ‖v'‖ :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul (S.norm_ι₁_le _) (S.norm_ι₁_le _)
        (norm_nonneg _) (norm_nonneg _))
    rw [Real.norm_eq_abs]
    calc _ ≤ |⟪S.ι₁ (S.d₀ (σ - τ)), S.ι₁ v'⟫| + |⟪S.d₁ (u - v), S.d₁ v'⟫| +
          |⟪S.ι₁ (p - q'), S.ι₁ v'⟫| := by
          refine (abs_add_le _ _).trans ?_
          gcongr
          exact abs_add_le _ _
      _ ≤ _ := by nlinarith
  obtain ⟨F₂, hF₂, hF₂n⟩ : ∃ F₂ : Vh.toShort.harmonic →L[ℝ] ℝ,
      (∀ q'', F₂ q'' = ⟪S.ι₁ (u - v), S.ι₁ (q'' : Vh.carrier₁)⟫ -
        ⟪S.ι₁ u, S.ι₁ (q'' : Vh.carrier₁)⟫) ∧
      ‖F₂‖ ≤ ‖u - (v : V₁)‖ + (1 + K) * (μ * ‖b - (w : V₁)‖) := by
    refine ⟨((innerSL ℝ (S.ι₁ (u - v))).comp Vh.toShort.ι₁ -
      (innerSL ℝ (S.ι₁ u)).comp Vh.toShort.ι₁).comp Vh.toShort.harmonic.subtypeL,
      fun q'' => rfl, ?_⟩
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun q'' => ?_
    have e : ((((innerSL ℝ (S.ι₁ (u - v))).comp Vh.toShort.ι₁ -
      (innerSL ℝ (S.ι₁ u)).comp Vh.toShort.ι₁).comp Vh.toShort.harmonic.subtypeL) q'') =
        ⟪S.ι₁ (u - v), S.ι₁ (q'' : Vh.carrier₁)⟫ - ⟪S.ι₁ u, S.ι₁ (q'' : Vh.carrier₁)⟫ := rfl
    rw [e]
    have hqn : ‖q''‖ = ‖(q'' : Vh.carrier₁)‖ := rfl
    have h1 : |⟪S.ι₁ (u - v), S.ι₁ (q'' : Vh.carrier₁)⟫| ≤ ‖u - (v : V₁)‖ * ‖q''‖ := by
      rw [hqn]
      exact (abs_real_inner_le_norm _ _).trans (mul_le_mul (S.norm_ι₁_le _) (S.norm_ι₁_le _)
        (norm_nonneg _) (norm_nonneg _))
    have h2 := π.abs_inner_discrete_harmonic_le hB hμ hK₁ hb hub q''.2 w.2
    rw [Real.norm_eq_abs, hqn]
    rw [hqn] at h1
    calc _ ≤ |⟪S.ι₁ (u - v), S.ι₁ (q'' : Vh.carrier₁)⟫| + |⟪S.ι₁ u, S.ι₁ (q'' : Vh.carrier₁)⟫| :=
          abs_sub _ _
      _ ≤ _ := by nlinarith
  have hgs : Vh.toShort.IsGenSolution F₀ F₁ F₂ (σh - τ) (uh - v)
      (⟨ph, hh.harmonic⟩ - ⟨q', hq'h⟩) := by
    refine ⟨fun τ' => ?_, fun v' => ?_, fun q'' => ?_⟩
    · have e1 := hh.eq₀ τ'
      have e2 := h.eq₀ (τ' : V₀)
      rw [hF₀]
      simp only [ShortHilbertComplex.Subcomplex.toShort_ι₀, ShortHilbertComplex.Subcomplex.toShort_ι₁,
        ShortHilbertComplex.Subcomplex.coe_toShort_d₀] at e1 ⊢
      simp only [Submodule.coe_sub, map_sub, inner_sub_left, inner_sub_right] at e1 e2 ⊢
      have c1 := real_inner_comm (S.ι₁ (S.d₀ (τ' : V₀))) (S.ι₁ u)
      have c2 := real_inner_comm (S.ι₁ (S.d₀ (τ' : V₀))) (S.ι₁ (v : V₁))
      linarith
    · have e1 := hh.eq₁ v'
      have e2 := h.eq₁ (v' : V₁)
      rw [hF₁]
      simp only [ShortHilbertComplex.Subcomplex.toShort_ι₀, ShortHilbertComplex.Subcomplex.toShort_ι₁,
        ShortHilbertComplex.Subcomplex.coe_toShort_d₀, ShortHilbertComplex.Subcomplex.toShort_d₁] at e1 ⊢
      simp only [Submodule.coe_sub, map_sub, inner_sub_left, inner_sub_right] at e1 e2 ⊢
      linarith
    · have e1 := hh.eq₂ q'' q''.2
      rw [hF₂]
      simp only [ShortHilbertComplex.Subcomplex.toShort_ι₀, ShortHilbertComplex.Subcomplex.toShort_ι₁,
        ShortHilbertComplex.Subcomplex.coe_toShort_d₀, ShortHilbertComplex.Subcomplex.toShort_d₁] at e1 ⊢
      simp only [Submodule.coe_sub, map_sub, inner_sub_left, inner_sub_right] at e1 ⊢
      linarith
  have key := hgs.norm_le hc'
  have hn : ‖(⟨ph, hh.harmonic⟩ - ⟨q', hq'h⟩ : Vh.toShort.harmonic)‖ = ‖(ph : V₁) - (q' : V₁)‖ :=
    rfl
  have hCh := stabilityConst_pos (c * K)
  set Ch := stabilityConst (c * K) with hChdef
  have t1 : ‖σ - (σh : V₀)‖ ≤ ‖σ - (τ : V₀)‖ + ‖σh - τ‖ := by
    calc _ = ‖(σ - (τ : V₀)) - ((σh : V₀) - τ)‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  have t2 : ‖u - (uh : V₁)‖ ≤ ‖u - (v : V₁)‖ + ‖uh - v‖ := by
    calc _ = ‖(u - (v : V₁)) - ((uh : V₁) - v)‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  have t3 : ‖p - (ph : V₁)‖ ≤ ‖p - (q' : V₁)‖ + ‖(ph : V₁) - q'‖ := by
    calc _ = ‖(p - (q' : V₁)) - ((ph : V₁) - q')‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  have t1' : ‖σh - τ‖ = ‖(σh : V₀) - τ‖ := rfl
  have t2' : ‖uh - v‖ = ‖(uh : V₁) - v‖ := rfl
  rw [hn] at key
  have hF : ‖F₀‖ + ‖F₁‖ + ‖F₂‖ ≤ 2 * ‖σ - (τ : V₀)‖ + 3 * ‖u - (v : V₁)‖ + ‖p - (q' : V₁)‖ +
      (1 + K) * (μ * ‖b - (w : V₁)‖) := by linarith
  have k2 := key.trans (mul_le_mul_of_nonneg_left hF hCh.le)
  unfold errorConst
  rw [← hChdef]
  set A := ‖σ - (τ : V₀)‖
  set B := ‖u - (v : V₁)‖
  set D := ‖p - (q : V₁)‖
  set m0 := μ * ‖b - (w : V₁)‖
  set Cp := ‖p - (q' : V₁)‖
  have s1 : ‖σ - (σh : V₀)‖ + ‖u - (uh : V₁)‖ + ‖p - (ph : V₁)‖ ≤
      A + B + Cp + Ch * (2 * A + 3 * B + Cp + (1 + K) * m0) := by linarith
  have s2 : A + B + Cp + Ch * (2 * A + 3 * B + Cp + (1 + K) * m0) ≤
      A + B + (1 + K) * D + Ch * (2 * A + 3 * B + (1 + K) * D + (1 + K) * m0) := by
    nlinarith [mul_le_mul_of_nonneg_left hq'2 hCh.le]
  have s3 : A + B + (1 + K) * D + Ch * (2 * A + 3 * B + (1 + K) * D + (1 + K) * m0) ≤
      (1 + Ch) * (3 + K) * (A + B + D + m0) := by
    nlinarith [mul_nonneg hK hA, mul_nonneg hK hB', mul_nonneg hK hD, mul_nonneg hK hm,
      mul_nonneg hCh.le hA, mul_nonneg hCh.le hB', mul_nonneg hCh.le hD, mul_nonneg hCh.le hm,
      mul_nonneg (mul_nonneg hK hCh.le) hA, mul_nonneg (mul_nonneg hK hCh.le) hB',
      mul_nonneg (mul_nonneg hK hCh.le) hD, mul_nonneg (mul_nonneg hK hCh.le) hm]
  linarith

end CochainProjection

end ShortHilbertComplex

end FEEC
