/-
Integrals of compactly supported functions along lines.
-/
import Mathlib

/-!
# Integrals along lines

For `f : E → F` and a vector `e`, we consider the integral of `f` over the line through `x`
in direction `e`, and over the half-line ending at `x`:

* `lineInt e f x = ∫ τ, f (x + τ • e)`;
* `halfLineInt e f x = ∫ τ in (-∞, 0], f (x + τ • e)`.

For smooth compactly supported `f` both are smooth, and differentiation commutes with the
integral. The derivative of `lineInt e f` in direction `e` vanishes, while that of
`halfLineInt e f` is `f`.
-/

namespace FEEC

open MeasureTheory

local notation "⟪" x ", " y "⟫" => inner ℝ x y

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {F' : Type u} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [CompleteSpace F']

/-- The integral of `f` over the line through `x` in direction `e`. -/
noncomputable def lineInt (e : E) (f : E → F) (x : E) : F := ∫ τ : ℝ, f (x + τ • e)

/-- The integral of `f` over the half-line `{x + τ • e | τ ≤ 0}`. -/
noncomputable def halfLineInt (e : E) (f : E → F) (x : E) : F :=
  ∫ τ in Set.Iic (0 : ℝ), f (x + τ • e)

variable {e : E} {f : E → F}

theorem exists_support_bound {G : Type*} [Zero G] {g : E → G} (hg : HasCompactSupport g) :
    ∃ R : ℝ, ∀ y, g y ≠ 0 → ‖y‖ ≤ R := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : E)).1 hg.isCompact.isBounded
  exact ⟨R, fun y hy => by simpa using hR (subset_tsupport g hy)⟩

theorem abs_le_of_line_ne_zero {G : Type*} [Zero G] (he : ‖e‖ = 1) {g : E → G} {R : ℝ}
    (hR : ∀ y, g y ≠ 0 → ‖y‖ ≤ R) {x : E} {τ : ℝ} (h : g (x + τ • e) ≠ 0) :
    |τ| ≤ R + ‖x‖ := by
  have h1 := hR _ h
  have h2 : ‖τ • e‖ = |τ| := by rw [norm_smul, he, mul_one, Real.norm_eq_abs]
  have h3 : ‖τ • e‖ ≤ ‖x + τ • e‖ + ‖x‖ := by
    have := norm_sub_le (x + τ • e) x
    simpa using this
  linarith

theorem integrable_comp_line (he : ‖e‖ = 1) (hf : Continuous f) (hfc : HasCompactSupport f)
    (x : E) : Integrable (fun τ : ℝ => f (x + τ • e)) := by
  obtain ⟨R, hR⟩ := exists_support_bound hfc
  have hc : Continuous (fun τ : ℝ => f (x + τ • e)) :=
    hf.comp (continuous_const.add (continuous_id.smul continuous_const))
  refine hc.integrable_of_hasCompactSupport (HasCompactSupport.intro
    (isCompact_Icc (a := -(R + ‖x‖)) (b := R + ‖x‖)) fun τ hτ => ?_)
  by_contra h
  have := abs_le_of_line_ne_zero he hR h
  exact hτ (abs_le.1 this)

theorem norm_lineInt_le (e : E) (f : E → F) (x : E) :
    ‖lineInt e f x‖ ≤ ∫ τ : ℝ, ‖f (x + τ • e)‖ :=
  norm_integral_le_integral_norm _

theorem norm_halfLineInt_le (he : ‖e‖ = 1) (hf : Continuous f) (hfc : HasCompactSupport f)
    (x : E) : ‖halfLineInt e f x‖ ≤ ∫ τ : ℝ, ‖f (x + τ • e)‖ := by
  refine (norm_integral_le_integral_norm _).trans ?_
  exact setIntegral_le_integral (integrable_comp_line he hf hfc x).norm
    (Filter.Eventually.of_forall fun τ => norm_nonneg _)

/-- `lineInt` commutes with continuous linear maps. -/
theorem lineInt_comp_clm (he : ‖e‖ = 1) (hf : Continuous f) (hfc : HasCompactSupport f)
    (L : F →L[ℝ] F') (x : E) : lineInt e (fun y => L (f y)) x = L (lineInt e f x) :=
  L.integral_comp_comm (integrable_comp_line he hf hfc x)

/-- `halfLineInt` commutes with continuous linear maps. -/
theorem halfLineInt_comp_clm (he : ‖e‖ = 1) (hf : Continuous f) (hfc : HasCompactSupport f)
    (L : F →L[ℝ] F') (x : E) : halfLineInt e (fun y => L (f y)) x = L (halfLineInt e f x) :=
  L.integral_comp_comm (μ := volume.restrict (Set.Iic (0:ℝ)))
    (integrable_comp_line he hf hfc x).integrableOn

theorem hasFDerivAt_integral_line_aux (he : ‖e‖ = 1) (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) (μ : Measure ℝ) (hμ : μ ≤ volume) (x : E) :
    HasFDerivAt (fun y => ∫ τ : ℝ, f (y + τ • e) ∂μ) (∫ τ : ℝ, fderiv ℝ f (x + τ • e) ∂μ) x := by
  have hfc' : HasCompactSupport (fderiv ℝ f) := hfc.fderiv (𝕜 := ℝ)
  obtain ⟨R, hR⟩ := exists_support_bound hfc'
  have hcont' : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  have hcont : Continuous f := hf.continuous
  obtain ⟨M, hM⟩ := hcont'.bounded_above_of_compact_support hfc'
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x)
  have hdiff : Differentiable ℝ f := hf.differentiable one_ne_zero
  set T := R + ‖x‖ + 1 with hT
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun y τ => fderiv ℝ f (y + τ • e))
    (bound := Set.indicator (Set.Icc (-T) T) (fun _ => M)) (s := Metric.ball x 1) (Metric.ball_mem_nhds x one_pos) ?_ ?_ ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun y =>
      (hcont.comp (continuous_const.add (continuous_id.smul continuous_const))).aestronglyMeasurable
  · exact (integrable_comp_line he hcont hfc x).mono_measure hμ
  · exact (hcont'.comp (continuous_const.add
      (continuous_id.smul continuous_const))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun τ y hy => ?_
    by_cases h : fderiv ℝ f (y + τ • e) = 0
    · simp only [h, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => hM0) _
    · have h1 := abs_le_of_line_ne_zero he hR h
      have h2 : ‖y‖ ≤ ‖x‖ + 1 := by
        have := mem_ball_iff_norm.1 hy
        have := norm_le_norm_add_norm_sub' y x
        linarith
      have h3 : τ ∈ Set.Icc (-T) T := abs_le.1 (by rw [hT]; linarith)
      rw [Set.indicator_of_mem h3]
      exact hM _
  · have : Integrable (Set.indicator (Set.Icc (-T) T) (fun _ => M)) volume :=
      (integrable_indicator_iff measurableSet_Icc).2
        (integrableOn_const (by simp) )
    exact this.mono_measure hμ
  · refine Filter.Eventually.of_forall fun τ y _ => ?_
    have h1 : HasFDerivAt (fun y : E => y + τ • e) (ContinuousLinearMap.id ℝ E) y :=
      (hasFDerivAt_id y).add_const _
    have h2 := (hdiff (y + τ • e)).hasFDerivAt.comp y h1
    simpa [Function.comp_def] using h2

/-- Differentiation under the integral sign for `lineInt`. -/
theorem hasFDerivAt_lineInt (he : ‖e‖ = 1) (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (x : E) : HasFDerivAt (lineInt e f) (lineInt e (fderiv ℝ f) x) x :=
  hasFDerivAt_integral_line_aux he hf hfc volume le_rfl x

/-- Differentiation under the integral sign for `halfLineInt`. -/
theorem hasFDerivAt_halfLineInt (he : ‖e‖ = 1) (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) (x : E) :
    HasFDerivAt (halfLineInt e f) (halfLineInt e (fderiv ℝ f) x) x :=
  hasFDerivAt_integral_line_aux he hf hfc _ Measure.restrict_le_self x

theorem contDiff_lineInt_nat (he : ‖e‖ = 1) (n : ℕ) :
    ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (f : E → F),
      ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → ContDiff ℝ n (lineInt e f) := by
  induction n with
  | zero =>
    intro F _ _ _ f hf hfc
    refine contDiff_zero.2 ?_
    exact continuous_iff_continuousAt.2 fun x =>
      (hasFDerivAt_lineInt he (hf.of_le (by exact_mod_cast le_top)) hfc x).continuousAt
  | succ n ih =>
    intro F _ _ _ f hf hfc
    rw [Nat.cast_succ, contDiff_succ_iff_hasFDerivAt]
    refine ⟨lineInt e (fderiv ℝ f), ?_, fun x =>
      hasFDerivAt_lineInt he (hf.of_le (by exact_mod_cast le_top)) hfc x⟩
    exact ih (fderiv ℝ f) (hf.fderiv_right (by exact_mod_cast le_top)) (hfc.fderiv (𝕜 := ℝ))

theorem contDiff_halfLineInt_nat (he : ‖e‖ = 1) (n : ℕ) :
    ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (f : E → F),
      ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → ContDiff ℝ n (halfLineInt e f) := by
  induction n with
  | zero =>
    intro F _ _ _ f hf hfc
    refine contDiff_zero.2 ?_
    exact continuous_iff_continuousAt.2 fun x =>
      (hasFDerivAt_halfLineInt he (hf.of_le (by exact_mod_cast le_top)) hfc x).continuousAt
  | succ n ih =>
    intro F _ _ _ f hf hfc
    rw [Nat.cast_succ, contDiff_succ_iff_hasFDerivAt]
    refine ⟨halfLineInt e (fderiv ℝ f), ?_, fun x =>
      hasFDerivAt_halfLineInt he (hf.of_le (by exact_mod_cast le_top)) hfc x⟩
    exact ih (fderiv ℝ f) (hf.fderiv_right (by exact_mod_cast le_top)) (hfc.fderiv (𝕜 := ℝ))

theorem contDiff_lineInt (he : ‖e‖ = 1) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfc : HasCompactSupport f) : ContDiff ℝ (⊤ : ℕ∞) (lineInt e f) :=
  contDiff_infty.2 fun n => contDiff_lineInt_nat he n f hf hfc

theorem contDiff_halfLineInt (he : ‖e‖ = 1) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfc : HasCompactSupport f) : ContDiff ℝ (⊤ : ℕ∞) (halfLineInt e f) :=
  contDiff_infty.2 fun n => contDiff_halfLineInt_nat he n f hf hfc

theorem hasDerivAt_comp_line (hf : ContDiff ℝ 1 f) (x : E) (τ : ℝ) :
    HasDerivAt (fun τ : ℝ => f (x + τ • e)) (fderiv ℝ f (x + τ • e) e) τ := by
  have h1 : HasDerivAt (fun τ : ℝ => x + τ • e) e τ := by
    simpa using ((hasDerivAt_id τ).smul_const e).const_add x
  exact ((hf.differentiable one_ne_zero (x + τ • e)).hasFDerivAt).comp_hasDerivAt τ h1

/-- The integral over a whole line of the derivative along that line vanishes. -/
theorem lineInt_fderiv_apply_self (he : ‖e‖ = 1) (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) (x : E) : lineInt e (fderiv ℝ f) x e = 0 := by
  have hint' := integrable_comp_line he (hf.continuous_fderiv one_ne_zero) (hfc.fderiv (𝕜 := ℝ)) x
  unfold lineInt
  rw [ContinuousLinearMap.integral_apply hint']
  have hint : Integrable (fun τ : ℝ => fderiv ℝ f (x + τ • e) e) :=
    ((ContinuousLinearMap.apply ℝ F e).integrable_comp hint')
  exact integral_eq_zero_of_hasDerivAt_of_integrable (hasDerivAt_comp_line hf x) hint
    (integrable_comp_line he hf.continuous hfc x)

/-- The fundamental theorem of calculus along a half-line. -/
theorem halfLineInt_fderiv_apply_self (he : ‖e‖ = 1) (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) (x : E) : halfLineInt e (fderiv ℝ f) x e = f x := by
  have hint' := integrable_comp_line he (hf.continuous_fderiv one_ne_zero) (hfc.fderiv (𝕜 := ℝ)) x
  unfold halfLineInt
  rw [ContinuousLinearMap.integral_apply hint'.integrableOn]
  have hint : Integrable (fun τ : ℝ => fderiv ℝ f (x + τ • e) e) :=
    ((ContinuousLinearMap.apply ℝ F e).integrable_comp hint')
  obtain ⟨R, hR⟩ := exists_support_bound hfc
  have hlim : Filter.Tendsto (fun τ : ℝ => f (x + τ • e)) Filter.atBot (nhds 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_le_atBot (-(R + ‖x‖) - 1)] with τ hτ
    by_contra h
    have := abs_le_of_line_ne_zero he hR (Ne.symm h)
    have := neg_abs_le τ
    linarith
  have := integral_Iic_of_hasDerivAt_of_tendsto (a := (0:ℝ))
    (f := fun τ : ℝ => f (x + τ • e)) (f' := fun τ : ℝ => fderiv ℝ f (x + τ • e) e)
    (hf.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))).continuousWithinAt
    (fun τ _ => hasDerivAt_comp_line hf x τ) hint.integrableOn hlim
  simpa using this

end FEEC
