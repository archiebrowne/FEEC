/-
Weak exterior derivatives of tensor-product forms on a box.
-/
import FEEC.DeRham.BasisCovector
import FEEC.DeRham.BoxDecomp
import FEEC.DeRham.TestForm

/-!
# Weak exterior derivatives of tensor-product forms

* `FEEC.integral_mul_fderiv_eq`: integration by parts along a direction `e` for a function
  `u(⟪e, x⟫) r(x)` with `u` Lipschitz and piecewise differentiable and `r` invariant along `e`.
* `FEEC.codiff_eq_sum_basis`: the codifferential can be computed in any orthonormal basis.
* `FEEC.hasWeakExtDeriv_prod_smul`: on a box, the form `(∏ᵢ uᵢ(⟪eᵢ, x⟫)) α` has weak exterior
  derivative `∑ᵢ uᵢ'(⟪eᵢ, x⟫) ∏_{j ≠ i} uⱼ(⟪eⱼ, x⟫) eᵢ♭ ∧ α`, provided for each `i` either
  `eᵢ♭ ∧ α = 0` or `uᵢ` is Lipschitz with derivative `uᵢ'` away from finitely many points.
-/

namespace FEEC

open MeasureTheory Filter Topology

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {n k : ℕ}

theorem integrable_mul_of_bdd {h f : E → ℝ} (hh : AEStronglyMeasurable h volume)
    (hf : Continuous f) (hfc : HasCompactSupport f) {C : ℝ}
    (hb : ∀ x ∈ tsupport f, |h x| ≤ C) : Integrable (fun x => h x * f x) := by
  refine Integrable.mono' ((hf.integrable_of_hasCompactSupport hfc).norm.const_mul C)
    (hh.mul hf.aestronglyMeasurable) (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ tsupport f
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (by simpa using hb x hx) (norm_nonneg _)
  · have : f x = 0 := image_eq_zero_of_notMem_tsupport hx
    simp [this]

/-- Integration by parts along the direction `e`. -/
theorem integral_mul_fderiv_eq {e : E} (he : ‖e‖ = 1) {a b : ℝ} {u u' : ℝ → ℝ} {K : NNReal}
    (hu : LipschitzWith K u) (hu'm : Measurable u') (Z : Finset ℝ)
    (hd : ∀ t ∈ Set.Ioo a b, t ∉ Z → HasDerivAt u (u' t) t)
    {r : E → ℝ} (hr : Measurable r) {Cr : ℝ} (hrb : ∀ x, |r x| ≤ Cr)
    (hre : ∀ x (t : ℝ), r (x + t • e) = r x)
    {f : E → ℝ} (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (hfs : ∀ x ∈ tsupport f, ⟪e, x⟫ ∈ Set.Ioo a b) :
    ∫ x, u ⟪e, x⟫ * r x * fderiv ℝ f x e = - ∫ x, u' ⟪e, x⟫ * r x * f x := by
  classical
  obtain ⟨G, hG⟩ : ∃ G : E → ℝ, ∀ x, G x = u ⟪e, x⟫ * r x := ⟨_, fun _ => rfl⟩
  simp only [← hG]
  have hucont : Continuous u := hu.continuous
  have hum : Measurable u := hucont.measurable
  have hinner : Continuous fun x : E => ⟪e, x⟫ := continuous_const.inner continuous_id
  have hGm : Measurable G := by
    have : G = fun x => u ⟪e, x⟫ * r x := funext hG
    rw [this]; exact (hum.comp hinner.measurable).mul hr
  have hCr : 0 ≤ Cr := (abs_nonneg _).trans (hrb 0)
  have hGb : ∀ S : Set E, IsCompact S → ∃ C, ∀ x ∈ S, |G x| ≤ C := by
    intro S hS
    obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn
      (f := fun x : E => u ⟪e, x⟫) (hucont.comp hinner).continuousOn
    refine ⟨B * Cr, fun x hx => ?_⟩
    rw [hG, abs_mul]
    exact mul_le_mul (by simpa using hB x hx) (hrb x) (abs_nonneg _)
      ((norm_nonneg _).trans (hB x hx))
  have hfd : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hfcont : Continuous f := hf.continuous
  have hfm : Measurable f := hfcont.measurable
  obtain ⟨L, hL⟩ : ∃ L, ∀ x, ‖fderiv ℝ f x‖ ≤ L :=
    (hf.continuous_fderiv one_ne_zero).bounded_above_of_compact_support (hfc.fderiv ℝ)
  have hlip : ∀ x y, |f y - f x| ≤ L * ‖y - x‖ := fun x y => by
    simpa using Convex.norm_image_sub_le_of_norm_fderiv_le (f := f) (𝕜 := ℝ) (s := Set.univ)
      (fun x _ => hfd x) (fun x _ => hL x) convex_univ (Set.mem_univ x) (Set.mem_univ y)
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  -- null set
  have hplane : ∀ z : ℝ, volume {x : E | ⟪e, x⟫ = z} = 0 := by
    intro z
    have hne : (ℝ ∙ e)ᗮ ≠ ⊤ := by
      intro h
      have : e ∈ (ℝ ∙ e)ᗮ := h ▸ Submodule.mem_top
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at this
      simp [real_inner_self_eq_norm_sq, he] at this
    have h0 := Measure.addHaar_submodule volume _ hne
    have : {x : E | ⟪e, x⟫ = z} = (fun x => x + (-z) • e) ⁻¹' ((ℝ ∙ e)ᗮ : Set E) := by
      ext x
      simp [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_add_right,
        inner_smul_right, real_inner_self_eq_norm_sq, he]
      constructor <;> intro h <;> linarith
    rw [this, measure_preimage_add_right]; exact h0
  have hexc : ∀ᵐ x : E, ⟪e, x⟫ ∉ (Z : Set ℝ) := by
    have : ∀ᵐ x : E, ∀ z ∈ (Z : Set ℝ), ⟪e, x⟫ ≠ z := by
      rw [ae_ball_iff Z.countable_toSet]
      intro z _
      rw [ae_iff]; simpa using hplane z
    filter_upwards [this] with x hx h using hx _ h rfl
  -- translated integrals
  have hI : ∀ t : ℝ, Integrable (fun x => G (x - t • e) * f x) := by
    intro t
    obtain ⟨C, hC⟩ := hGb ((fun x : E => x - t • e) '' tsupport f)
      (hfc.image (continuous_id.sub continuous_const))
    exact integrable_mul_of_bdd (hGm.comp (measurable_id.sub_const _)).aestronglyMeasurable
      hfcont hfc (fun x hx => hC _ ⟨x, hx, rfl⟩)
  have hI0 : Integrable (fun x => G x * f x) := by
    simpa using hI 0
  have heq : ∀ t : ℝ, t ≠ 0 → ∫ x, G x * ((f (x + t • e) - f x) / t) =
      ∫ x, ((u (⟪e, x⟫ - t) - u ⟪e, x⟫) / t * r x) * f x := by
    intro t ht
    have hI3 : Integrable (fun x => G x * f (x + t • e)) := by
      have := (hI t).comp_add_right (t • e)
      simpa using this
    have hshift : ∫ x, G x * f (x + t • e) = ∫ x, G (x - t • e) * f x := by
      rw [← integral_add_right_eq_self (fun x => G (x - t • e) * f x) (t • e)]
      simp
    have e1 : (fun x => G x * ((f (x + t • e) - f x) / t)) =
        fun x => (G x * f (x + t • e) - G x * f x) / t := by
      funext x; ring
    have e2 : (fun x => ((u (⟪e, x⟫ - t) - u ⟪e, x⟫) / t * r x) * f x) =
        fun x => (G (x - t • e) * f x - G x * f x) / t := by
      funext x
      have : G (x - t • e) = u (⟪e, x⟫ - t) * r x := by
        have h1 : ⟪e, x - t • e⟫ = ⟪e, x⟫ - t := by
          rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, he]; simp
        have h2 : r (x - t • e) = r x := by
          rw [sub_eq_add_neg, ← neg_smul, hre]
        rw [hG, h1, h2]
      rw [this, hG]; ring
    rw [e1, e2, integral_div, integral_div, integral_sub hI3 hI0, integral_sub (hI t) hI0, hshift]
  have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) {0}ᶜ, t ≠ 0 ∧ |t| ≤ 1 := by
    refine Filter.Eventually.and self_mem_nhdsWithin ?_
    refine eventually_nhdsWithin_of_eventually_nhds ?_
    have : Metric.closedBall (0 : ℝ) 1 ∈ nhds (0 : ℝ) := Metric.closedBall_mem_nhds 0 one_pos
    filter_upwards [this] with t ht
    simpa using ht
  -- left limit
  have hK' : IsCompact (Metric.cthickening 1 (tsupport f)) := hfc.cthickening
  obtain ⟨M, hM⟩ := hGb _ hK'
  have hL1 : Tendsto (fun t : ℝ => ∫ x, G x * ((f (x + t • e) - f x) / t)) (𝓝[≠] 0)
      (𝓝 (∫ x, G x * fderiv ℝ f x e)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      ((Metric.cthickening 1 (tsupport f)).indicator fun _ => M * L) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall fun t => ?_
      exact (hGm.mul (((hfm.comp (measurable_id.add_const (t • e))).sub hfm).div_const t)).aestronglyMeasurable
    · filter_upwards [hev] with t ⟨ht0, ht1⟩
      refine Eventually.of_forall fun x => ?_
      by_cases hx : x ∈ Metric.cthickening 1 (tsupport f)
      · rw [Set.indicator_of_mem hx, Real.norm_eq_abs, abs_mul, abs_div]
        have h1 := hlip x (x + t • e)
        rw [add_sub_cancel_left, norm_smul, he, mul_one, Real.norm_eq_abs] at h1
        have h2 : |f (x + t • e) - f x| / |t| ≤ L := by
          rw [div_le_iff₀ (abs_pos.mpr ht0)]; linarith
        have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x hx)
        exact mul_le_mul (hM x hx) h2 (by positivity) hM0
      · rw [Set.indicator_of_notMem hx]
        have h1 : f x = 0 := image_eq_zero_of_notMem_tsupport
          (fun h => hx (Metric.self_subset_cthickening _ h))
        have h2 : f (x + t • e) = 0 := by
          refine image_eq_zero_of_notMem_tsupport fun h => hx ?_
          refine Metric.mem_cthickening_of_dist_le x _ 1 _ h ?_
          rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul, he]
          simpa using ht1
        simp [h1, h2]
    · exact (integrableOn_const hK'.measure_lt_top.ne).integrable_indicator
        hK'.isClosed.measurableSet
    · refine Eventually.of_forall fun x => ?_
      have h1 : HasDerivAt (fun t : ℝ => f (x + t • e)) (fderiv ℝ f x e) 0 := by
        have h2 : HasDerivAt (fun t : ℝ => x + t • e) e 0 := by
          simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add x
        have h3 := (hfd (x + (0 : ℝ) • e)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
        simp only [zero_smul, add_zero] at h3
        exact h3
      refine (h1.tendsto_slope_zero.const_mul (G x)).congr fun t => ?_
      simp [div_eq_inv_mul]
  -- right limit
  have hR1 : Tendsto (fun t : ℝ => ∫ x, ((u (⟪e, x⟫ - t) - u ⟪e, x⟫) / t * r x) * f x)
      (𝓝[≠] 0) (𝓝 (∫ x, -(u' ⟪e, x⟫ * r x * f x))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x => K * Cr * ‖f x‖) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall fun t => ?_
      exact ((((hum.comp (hinner.measurable.sub_const t)).sub (hum.comp hinner.measurable)).div_const
        t).mul hr |>.mul hfm).aestronglyMeasurable
    · filter_upwards [hev] with t ⟨ht0, ht1⟩
      refine Eventually.of_forall fun x => ?_
      have h1 := hu.dist_le_mul (⟪e, x⟫ - t) ⟪e, x⟫
      simp only [Real.dist_eq] at h1
      rw [show ⟪e, x⟫ - t - ⟪e, x⟫ = -t by ring, abs_neg] at h1
      have h2 : |u (⟪e, x⟫ - t) - u ⟪e, x⟫| / |t| ≤ K := by
        rw [div_le_iff₀ (abs_pos.mpr ht0)]; linarith
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_div, Real.norm_eq_abs]
      have : 0 ≤ |f x| := abs_nonneg _
      calc |u (⟪e, x⟫ - t) - u ⟪e, x⟫| / |t| * |r x| * |f x|
          ≤ K * Cr * |f x| :=
        mul_le_mul_of_nonneg_right (mul_le_mul h2 (hrb x) (abs_nonneg _) (NNReal.coe_nonneg _)) this
        _ = _ := rfl
    · exact (hfcont.integrable_of_hasCompactSupport hfc).norm.const_mul _
    · filter_upwards [hexc] with x hxZ
      by_cases hx : x ∈ tsupport f
      · have hs := hfs x hx
        have hder := hd _ hs (by simpa using hxZ)
        have h1 : HasDerivAt (fun t : ℝ => u (⟪e, x⟫ - t)) (-u' ⟪e, x⟫) 0 :=
          HasDerivAt.comp_const_sub (⟪e, x⟫) 0 (by simpa using hder)
        have h2 := (h1.tendsto_slope_zero.mul_const (r x)).mul_const (f x)
        rw [neg_mul, neg_mul] at h2
        refine h2.congr fun t => ?_
        simp [div_eq_inv_mul]
      · have h1 : f x = 0 := image_eq_zero_of_notMem_tsupport hx
        simp [h1]
  have hlim := tendsto_nhds_unique
    (hL1.congr' (hev.mono fun t ht => heq t ht.1)) hR1
  rw [hlim, integral_neg]

/-- The codifferential in an arbitrary orthonormal basis. -/
theorem codiff_eq_sum_basis {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ E)
    (φ : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ) (x : E) :
    codiff φ x = -∑ i, (fderiv ℝ φ x (e i)).curryLeft (e i) := by
  classical
  rw [codiff_apply]
  congr 1
  set M : E →L[ℝ] E →L[ℝ] (E [⋀^Fin k]→L[ℝ] ℝ) :=
    (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := E) (F := ℝ) (n := k)).toContinuousLinearMap.comp
      (fderiv ℝ φ x) with hM
  have hMv : ∀ v w, (fderiv ℝ φ x v).curryLeft w = M v w := fun v w => rfl
  simp only [hMv]
  have expand : ∀ v w : E, M v w = ∑ i, ∑ l, (⟪e i, v⟫ * ⟪e l, w⟫) • M (e i) (e l) := by
    intro v w
    conv_lhs => rw [← e.sum_repr' v, ← e.sum_repr' w]
    simp [map_sum, smul_smul, Finset.smul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]
  have hstd : ∀ j, M (stdBasis E j) (stdBasis E j) = ∑ i, ∑ l,
      (⟪e i, stdBasis E j⟫ * ⟪e l, stdBasis E j⟫) • M (e i) (e l) := fun j => expand _ _
  simp only [hstd]
  have key : ∀ i l, ∑ j, ⟪e i, stdBasis E j⟫ * ⟪e l, stdBasis E j⟫ = if i = l then 1 else 0 := by
    intro i l
    have := (stdBasis E).sum_inner_mul_inner (e i) (e l)
    simp_rw [real_inner_comm (e l) (stdBasis E _)] at this
    rw [this, e.inner_eq_ite]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, key]
  simp

/-- **Weak exterior derivative of a tensor-product form on a box.** -/
theorem hasWeakExtDeriv_prod_smul (e : OrthonormalBasis (Fin n) ℝ E) (a b : Fin n → ℝ)
    (u u' : Fin n → ℝ → ℝ) (α : E [⋀^Fin k]→L[ℝ] ℝ)
    (hu : ∀ i, Measurable (u i)) (hub : ∀ i, ∃ C, ∀ t, |u i t| ≤ C)
    (hu' : ∀ i, Measurable (u' i)) (hu'b : ∀ i, ∃ C, ∀ t, |u' i t| ≤ C)
    (hd : ∀ i, wedgeLeft (e i) α = 0 ∨ ((∃ K, LipschitzWith K (u i)) ∧
      ∃ Z : Finset ℝ, ∀ t ∈ Set.Ioo (a i) (b i), t ∉ Z → HasDerivAt (u i) (u' i t) t))
    (ω : L2Form (box e a b) k)
    (hω : ω =ᵐ[volume.restrict (box e a b)]
      fun x => Covector.ofAlt ((∏ i, u i ⟪e i, x⟫) • α))
    (η : L2Form (box e a b) (k + 1))
    (hη : η =ᵐ[volume.restrict (box e a b)] fun x => Covector.ofAlt
      (∑ i, (u' i ⟪e i, x⟫ * ∏ j ∈ Finset.univ.erase i, u j ⟪e j, x⟫) • wedgeLeft (e i) α)) :
    HasWeakExtDeriv ω η := by
  classical
  intro φ hφ
  have hΩ : MeasurableSet (box e a b) := (isOpen_box e a b).measurableSet
  choose C hC using hub
  choose C' hC' using hu'b
  have hC0 : ∀ j, 0 ≤ C j := fun j => (abs_nonneg _).trans (hC j 0)
  have hC'0 : ∀ j, 0 ≤ C' j := fun j => (abs_nonneg _).trans (hC' j 0)
  have hinner : ∀ i, Continuous fun x : E => ⟪e i, x⟫ := fun i => continuous_const.inner continuous_id
  have hprodm : ∀ s : Finset (Fin n), Measurable fun x : E => ∏ j ∈ s, u j ⟪e j, x⟫ := fun s =>
    Finset.measurable_prod s fun j _ => (hu j).comp (hinner j).measurable
  have hprodb : ∀ (s : Finset (Fin n)) (x : E), |∏ j ∈ s, u j ⟪e j, x⟫| ≤ ∏ j ∈ s, C j := by
    intro s x
    rw [Finset.abs_prod]
    gcongr with j _
    exact hC j _
  obtain ⟨gg, hgg⟩ : ∃ gg : E → ℝ, ∀ x, gg x = ∏ i, u i ⟪e i, x⟫ := ⟨_, fun _ => rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : Fin n → E → ℝ, ∀ i x,
      g i x = u' i ⟪e i, x⟫ * ∏ j ∈ Finset.univ.erase i, u j ⟪e j, x⟫ := ⟨_, fun _ _ => rfl⟩
  have hggm : Measurable gg := by
    have : gg = fun x => ∏ i, u i ⟪e i, x⟫ := funext hgg
    rw [this]; exact hprodm _
  have hggb : ∀ x, |gg x| ≤ ∏ j, C j := fun x => by rw [hgg]; exact hprodb _ x
  have hgm : ∀ i, Measurable (g i) := by
    intro i
    have : g i = fun x => u' i ⟪e i, x⟫ * ∏ j ∈ Finset.univ.erase i, u j ⟪e j, x⟫ :=
      funext (hg i)
    rw [this]; exact ((hu' i).comp (hinner i).measurable).mul (hprodm _)
  have hgb : ∀ i x, |g i x| ≤ C' i * ∏ j ∈ Finset.univ.erase i, C j := by
    intro i x
    rw [hg, abs_mul]
    exact mul_le_mul (hC' i _) (hprodb _ x) (abs_nonneg _) (hC'0 i)
  obtain ⟨Lf, hLf⟩ : ∃ Lf : Fin n → (E [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] ℝ, ∀ i y,
      Lf i y = ⟪Covector.ofAlt (wedgeLeft (e i) α), Covector.ofAlt y⟫ :=
    ⟨fun i => (innerSL ℝ (Covector.ofAlt (wedgeLeft (e i) α))).comp
      (Covector.ofAlt : (E [⋀^Fin (k + 1)]→L[ℝ] ℝ) ≃L[ℝ] _).toContinuousLinearMap,
      fun i y => rfl⟩
  have hφ1 : ContDiff ℝ 1 φ := hφ.contDiff.of_le (by exact_mod_cast le_top)
  have hφd : Differentiable ℝ φ := hφ1.differentiable one_ne_zero
  have hDc : Continuous (fderiv ℝ φ) := hφ1.continuous_fderiv one_ne_zero
  have hφ0 : ∀ x ∉ box e a b, φ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hφ.tsupport_subset h)
  have hD0 : ∀ x ∉ box e a b, fderiv ℝ φ x = 0 := by
    intro x hx
    by_contra hne
    exact hx (hφ.tsupport_subset (tsupport_fderiv_subset ℝ (subset_tsupport _ hne)))
  have hderiv : ∀ i x, fderiv ℝ (fun x => Lf i (φ x)) x (e i) = Lf i (fderiv ℝ φ x (e i)) := by
    intro i x
    have h := (Lf i).hasFDerivAt.comp x (hφd x).hasFDerivAt
    rw [show (fun x => Lf i (φ x)) = Lf i ∘ φ from rfl, h.fderiv]; rfl
  have hfi_c : ∀ i, Continuous fun x => Lf i (φ x) := fun i => (Lf i).continuous.comp hφ.contDiff.continuous
  have hfi_cs : ∀ i, HasCompactSupport fun x => Lf i (φ x) := fun i =>
    hφ.hasCompactSupport.comp_left (g := Lf i) (map_zero _)
  have hint1 : ∀ i, Integrable fun x => g i x * Lf i (φ x) := fun i =>
    integrable_mul_of_bdd (hgm i).aestronglyMeasurable (hfi_c i) (hfi_cs i) (fun x _ => hgb i x)
  have hint2 : ∀ i, Integrable fun x => gg x * Lf i (fderiv ℝ φ x (e i)) := fun i =>
    integrable_mul_of_bdd (C := ∏ j, C j) hggm.aestronglyMeasurable
      ((Lf i).continuous.comp (hDc.clm_apply continuous_const))
      (hφ.hasCompactSupport.fderiv_apply ℝ (e i) |>.comp_left (g := Lf i) (map_zero _))
      (fun x _ => hggb x)
  have key : ∀ i, ∫ x, g i x * Lf i (φ x) = -∫ x, gg x * Lf i (fderiv ℝ φ x (e i)) := by
    intro i
    by_cases hA : wedgeLeft (e i) α = 0
    · have h0 : ∀ y, Lf i y = 0 := fun y => by rw [hLf, hA]; simp
      simp [h0]
    · obtain ⟨⟨K, hK⟩, Z, hZ⟩ := (hd i).resolve_left hA
      have hre : ∀ (x : E) (t : ℝ), (∏ j ∈ Finset.univ.erase i, u j ⟪e j, x + t • e i⟫) =
          ∏ j ∈ Finset.univ.erase i, u j ⟪e j, x⟫ := by
        intro x t
        refine Finset.prod_congr rfl fun j hj => ?_
        have hne : j ≠ i := Finset.ne_of_mem_erase hj
        rw [inner_add_right, inner_smul_right, e.inner_eq_ite, if_neg hne]; simp
      have hfs : ∀ x ∈ tsupport fun x => Lf i (φ x), ⟪e i, x⟫ ∈ Set.Ioo (a i) (b i) := by
        intro x hx
        exact (hφ.tsupport_subset ((tsupport_comp_subset (map_zero (Lf i)) φ) hx) i)
      have := integral_mul_fderiv_eq (e := e i) (e.norm_eq_one i) hK (hu' i) Z hZ
        (r := fun x => ∏ j ∈ Finset.univ.erase i, u j ⟪e j, x⟫) (hprodm _)
        (Cr := ∏ j ∈ Finset.univ.erase i, C j) (hprodb _) hre
        (f := fun x => Lf i (φ x)) ((Lf i).contDiff.comp hφ1) (hfi_cs i) hfs
      simp only [hderiv] at this
      have e1 : ∀ x, gg x = u i ⟪e i, x⟫ * ∏ j ∈ Finset.univ.erase i, u j ⟪e j, x⟫ := fun x => by
        rw [hgg]; exact (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
      simp only [e1, hg]
      linarith
  rw [L2.inner_def, L2.inner_def]
  have hlhs : ∫ x, ⟪η x, hφ.toLp x⟫ ∂(volume.restrict (box e a b)) =
      ∑ i, ∫ x, g i x * Lf i (φ x) := by
    have h1 : ∀ᵐ x ∂(volume.restrict (box e a b)),
        ⟪η x, hφ.toLp x⟫ = ∑ i, g i x * Lf i (φ x) := by
      filter_upwards [hη, hφ.coeFn_toLp] with x h1 h2
      rw [h1, h2]
      simp only [map_sum, map_smul, sum_inner, real_inner_smul_left, hLf, hg]
    rw [integral_congr_ae h1, integral_finset_sum _ (fun i _ => (hint1 i).integrableOn)]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by simp [hφ0 x hx]
  have hrhs : ∫ x, ⟪ω x, hφ.codiff.toLp x⟫ ∂(volume.restrict (box e a b)) =
      -∑ i, ∫ x, gg x * Lf i (fderiv ℝ φ x (e i)) := by
    have h1 : ∀ᵐ x ∂(volume.restrict (box e a b)),
        ⟪ω x, hφ.codiff.toLp x⟫ = -∑ i, gg x * Lf i (fderiv ℝ φ x (e i)) := by
      filter_upwards [hω, hφ.codiff.coeFn_toLp] with x h1 h2
      rw [h1, h2, codiff_eq_sum_basis e φ x]
      simp only [map_neg, map_sum, map_smul, inner_neg_right, inner_sum, real_inner_smul_left]
      rw [← hgg x]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hLf, inner_wedgeLeft]
    rw [integral_congr_ae h1, integral_neg,
      integral_finset_sum _ (fun i _ => (hint2 i).integrableOn)]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    exact setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by simp [hD0 x hx]
  rw [hlhs, hrhs, Finset.sum_congr rfl (fun i _ => key i), Finset.sum_neg_distrib]

end FEEC
