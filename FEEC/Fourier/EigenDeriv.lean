/-
Weak exterior derivatives of eigenforms, and integration by parts against them.
-/
import FEEC.Fourier.Eigenforms
import FEEC.Tensor.FormsDeriv

/-!
# `d` and `δ` on eigenforms

* `Fourier.hasWeakExtDeriv_synth`: `d (synth m α) = synth m (ξ_m ∧ α)`.
* `Fourier.inner_d_synth`: **integration by parts against eigenforms**: for every `w ∈ HΛᵏ` of
  the box, `⟪dw, synth m γ⟫ = ⟪w, synth m (ξ_m ⌟ γ)⟫`, although `synth m γ` is not compactly
  supported (its normal components vanish on the boundary).
* `Fourier.coef_d`: hence `(dw)^(m) = ξ_m ∧ ŵ(m)`.
-/

namespace FEEC

namespace Fourier

open MeasureTheory Tensor

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {n : ℕ}
  {e : OrthonormalBasis (Fin n) ℝ E} {a b : Fin n → ℝ} {k : ℕ}

/-! ### Elementary helpers -/

section helpers

variable (e a b) in
theorem inner_xi (m : Fin n → ℕ) (i : Fin n) :
    ⟪e i, xi e a b m⟫ = -freq (a i) (b i) (m i) := by
  simp [xi, inner_neg_right, inner_sum, inner_smul_right, e.inner_eq_ite]

theorem contDiff_trig1 (s : Bool) (a b : ℝ) (m : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (trig1 s a b m) := by
  unfold trig1; split_ifs
  exacts [contDiff_trigS m, contDiff_trigC m]

theorem abs_trig1_le (s : Bool) (a b : ℝ) (m : ℕ) (t : ℝ) : |trig1 s a b m t| ≤ 1 := by
  unfold trig1; split_ifs
  exacts [abs_trigS_le _ _, abs_trigC_le _ _]

theorem pat_eq_of_range_eq {l : ℕ} {S T : Fin l → Fin n} (h : Set.range S = Set.range T) :
    pat S = pat T := by
  funext i
  rw [Bool.eq_iff_iff, pat_eq_true_iff, pat_eq_true_iff, h]

theorem trigProd_cons (i : Fin n) (T : Fin k → Fin n) (m : Fin n → ℕ) (x : E) :
    trigProd e a b (pat (Fin.cons i T : Fin (k + 1) → Fin n)) m x =
      trig1 true (a i) (b i) (m i) ⟪e i, x⟫ *
        ∏ j ∈ Finset.univ.erase i, trig1 (pat T j) (a j) (b j) (m j) ⟪e j, x⟫ := by
  unfold trigProd
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  have hp : pat (Fin.cons i T : Fin (k + 1) → Fin n) i = true := by
    rw [pat_cons]; simp
  rw [hp]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [pat_cons, decide_eq_false (Finset.ne_of_mem_erase hj)]; simp

theorem fderiv_prod_apply (h : Fin n → ℝ → ℝ) (hh : ∀ i, Differentiable ℝ (h i)) (x : E)
    (i : Fin n) :
    fderiv ℝ (fun y : E => ∏ j, h j ⟪e j, y⟫) x (e i) =
      deriv (h i) ⟪e i, x⟫ * ∏ j ∈ Finset.univ.erase i, h j ⟪e j, x⟫ := by
  classical
  have hdiff : Differentiable ℝ (fun y : E => ∏ j, h j ⟪e j, y⟫) := by
    have hj : ∀ j, Differentiable ℝ (fun y : E => h j ⟪e j, y⟫) := fun j =>
      (hh j).comp ((innerSL ℝ (e j)).differentiable : Differentiable ℝ fun y : E => ⟪e j, y⟫)
    intro y
    exact (HasFDerivAt.finsetProd (u := Finset.univ) fun j _ => (hj j y).hasFDerivAt).differentiableAt
  have h1 : HasDerivAt (fun t : ℝ => (fun y : E => ∏ j, h j ⟪e j, y⟫) (x + t • e i))
      (fderiv ℝ (fun y : E => ∏ j, h j ⟪e j, y⟫) x (e i)) 0 := by
    have h2 : HasDerivAt (fun t : ℝ => x + t • e i) (e i) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (e i)).const_add x
    have h3 := (hdiff (x + (0 : ℝ) • e i)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
    simp only [zero_smul, add_zero] at h3
    exact h3
  have h2 : HasDerivAt (fun t : ℝ => (fun y : E => ∏ j, h j ⟪e j, y⟫) (x + t • e i))
      (deriv (h i) ⟪e i, x⟫ * ∏ j ∈ Finset.univ.erase i, h j ⟪e j, x⟫) 0 := by
    have hfun : (fun t : ℝ => (fun y : E => ∏ j, h j ⟪e j, y⟫) (x + t • e i)) = fun t =>
        h i (⟪e i, x⟫ + t) * ∏ j ∈ Finset.univ.erase i, h j ⟪e j, x⟫ := by
      funext t
      simp only
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
      congr 1
      · rw [inner_add_right, inner_smul_right, e.inner_eq_ite, if_pos rfl, mul_one]
      · refine Finset.prod_congr rfl fun j hj => ?_
        rw [inner_add_right, inner_smul_right, e.inner_eq_ite, if_neg (Finset.ne_of_mem_erase hj)]
        simp
    rw [hfun]
    have hd : HasDerivAt (h i) (deriv (h i) ⟪e i, x⟫) ⟪e i, x⟫ := (hh i _).hasDerivAt
    exact (HasDerivAt.comp_const_add (⟪e i, x⟫) 0 (by simpa using hd)).mul_const _
  exact h1.unique h2

end helpers

/-! ### `L²` bookkeeping and the covector identities -/

section l2

theorem coeFn_sum_smul' {Ω : Set E} {j : ℕ} {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (f : ι → L2Form Ω j) :
    (⇑(∑ i ∈ s, c i • f i : L2Form Ω j)) =ᵐ[volume.restrict Ω]
      fun x => ∑ i ∈ s, c i • (f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero (Covector E j) 2 (volume.restrict Ω)] with x hx
    simpa using hx
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (c i • f i) (∑ i ∈ s, c i • f i), Lp.coeFn_smul (c i) (f i), ih]
      with x h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3, Finset.sum_insert hi]
    rfl

theorem hasWeakExtDeriv_sum {Ω : Set E} {j : ℕ} {ι : Type*} (s : Finset ι)
    (ω : ι → L2Form Ω j) (η : ι → L2Form Ω (j + 1))
    (h : ∀ i ∈ s, HasWeakExtDeriv (ω i) (η i)) :
    HasWeakExtDeriv (∑ i ∈ s, ω i) (∑ i ∈ s, η i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasWeakExtDeriv.zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add (ih fun i hi' => h i (Finset.mem_insert_of_mem hi'))

theorem synth_ae (m : Fin n → ℕ) {j : ℕ} (β : Covector E j) :
    synth e a b m β =ᵐ[volume.restrict (box e a b)] fun x =>
      ((j.factorial : ℝ))⁻¹ • ∑ T : Fin j → Fin n,
        ⟪β, Covector.ofAlt (dxT e j T)⟫ • Covector.ofAlt (eigForm e a b T m x) := by
  unfold synth
  filter_upwards [Lp.coeFn_smul ((j.factorial : ℝ))⁻¹
      (∑ T : Fin j → Fin n, ⟪β, Covector.ofAlt (dxT e j T)⟫ • eigLp e a b T m),
    coeFn_sum_smul' (Finset.univ : Finset (Fin j → Fin n))
      (fun T => ⟪β, Covector.ofAlt (dxT e j T)⟫) (fun T => eigLp e a b T m),
    ae_all_iff.2 fun T : Fin j → Fin n => coeFn_eigLp (e := e) (a := a) (b := b) T m]
    with x h1 h2 h3
  rw [h1, Pi.smul_apply, h2]
  simp only [h3]

theorem sum_inner_dxC {j : ℕ} (β : Covector E j) :
    ((j.factorial : ℝ))⁻¹ • ∑ T : Fin j → Fin n,
      ⟪β, Covector.ofAlt (dxT e j T)⟫ • Covector.ofAlt (dxT e j T) = β := by
  have := congrArg Covector.ofAlt (sum_inner_dxT_smul e β.toAlt)
  simpa [map_smul, map_sum] using this

theorem sum_inner_dxC_tau {j : ℕ} (S : Fin j → Fin n) (f : (Fin j → Fin n) → ℝ)
    (hf : ∀ T T', Set.range T = Set.range T' → f T = f T') :
    ∑ T : Fin j → Fin n, ⟪Covector.ofAlt (dxT e j S), Covector.ofAlt (dxT e j T)⟫ •
        (f T • Covector.ofAlt (dxT e j T)) =
      ((j.factorial : ℝ) * f S) • Covector.ofAlt (dxT e j S) := by
  have h1 : ∀ T : Fin j → Fin n,
      ⟪Covector.ofAlt (dxT e j S), Covector.ofAlt (dxT e j T)⟫ •
        (f T • Covector.ofAlt (dxT e j T)) =
      f S • (⟪Covector.ofAlt (dxT e j S), Covector.ofAlt (dxT e j T)⟫ •
        Covector.ofAlt (dxT e j T)) := by
    intro T
    by_cases h : Set.range S = Set.range T
    · rw [hf T S h.symm, smul_comm]
    · rw [inner_dxT_eq_zero_of_range_ne e h]; simp
  simp only [h1]
  rw [← Finset.smul_sum]
  have hne : (j.factorial : ℝ) ≠ 0 := by positivity
  have h2 := (inv_smul_eq_iff₀ hne).1 (sum_inner_dxC (e := e) (Covector.ofAlt (dxT e j S)))
  rw [h2, smul_smul, mul_comm]

theorem ccontr_eq_sum (v : E) (β : Covector E (k + 1)) :
    ccontr v β = ∑ i, ⟪e i, v⟫ • ccontr (e i) β := by
  unfold ccontr
  conv_lhs => rw [← e.sum_repr' v]
  simp [map_sum, map_smul]

theorem inner_cwedge_dxC (v : E) (α : Covector E k) (T' : Fin (k + 1) → Fin n) :
    ⟪cwedge v α, Covector.ofAlt (dxT e (k + 1) T')⟫ =
      ((k.factorial : ℝ))⁻¹ * ∑ S : Fin k → Fin n, ⟪α, Covector.ofAlt (dxT e k S)⟫ *
        ∑ i, ⟪e i, v⟫ * ⟪Covector.ofAlt (dxT e (k + 1) (Fin.cons i S : Fin (k + 1) → Fin n)),
          Covector.ofAlt (dxT e (k + 1) T')⟫ := by
  rw [inner_cwedge]
  have hα := sum_inner_dxC (e := e) α
  have h1 : ∀ S : Fin k → Fin n, ⟪Covector.ofAlt (dxT e k S), ccontr v (Covector.ofAlt (dxT e (k + 1) T'))⟫ =
      ∑ i, ⟪e i, v⟫ * ⟪Covector.ofAlt (dxT e (k + 1) (Fin.cons i S : Fin (k + 1) → Fin n)),
          Covector.ofAlt (dxT e (k + 1) T')⟫ := by
    intro S
    rw [ccontr_eq_sum (e := e), inner_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_smul_right]
    congr 1
    unfold ccontr
    rw [Covector.toAlt_ofAlt, real_inner_comm, inner_curryLeft_dxT, real_inner_comm]
  calc _ = ⟪((k.factorial : ℝ))⁻¹ • ∑ T : Fin k → Fin n,
        ⟪α, Covector.ofAlt (dxT e k T)⟫ • Covector.ofAlt (dxT e k T),
        ccontr v (Covector.ofAlt (dxT e (k + 1) T'))⟫ := by rw [hα]
    _ = _ := by
      rw [real_inner_smul_left, sum_inner]
      simp only [real_inner_smul_left, h1]

end l2

/-! ### One-dimensional cutoffs -/

section cutoff

open Real.smoothTransition in
theorem deriv_smoothTransition_eq_zero {y : ℝ} (h : y < 0 ∨ 1 < y) :
    deriv Real.smoothTransition y = 0 := by
  rcases h with h | h
  · have : Real.smoothTransition =ᶠ[nhds y] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds h] with z hz
      exact Real.smoothTransition.zero_of_nonpos (le_of_lt hz)
    rw [this.deriv_eq]; simp
  · have : Real.smoothTransition =ᶠ[nhds y] fun _ => (1 : ℝ) := by
      filter_upwards [Ioi_mem_nhds h] with z hz
      exact Real.smoothTransition.one_of_one_le (le_of_lt hz)
    rw [this.deriv_eq]; simp

theorem exists_bound_deriv_smoothTransition :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ y, |deriv Real.smoothTransition y| ≤ L := by
  have hc : Continuous (deriv Real.smoothTransition) := by
    have := (Real.smoothTransition.contDiff (n := (⊤ : ℕ∞)))
    exact this.continuous_deriv (by simp)
  obtain ⟨L, hL⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hc.continuousOn
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0 ⟨le_rfl, zero_le_one⟩)
  refine ⟨L, hL0, fun y => ?_⟩
  by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
  · simpa using hL y hy
  · rw [deriv_smoothTransition_eq_zero (by
      by_contra hh; push Not at hh; exact hy ⟨hh.1, hh.2⟩)]
    simpa using hL0

/-- The smooth cutoff of the interval `(a, b)`, supported in `(a + ε, b - ε)`. -/
noncomputable def theta (ε a b t : ℝ) : ℝ :=
  Real.smoothTransition ((t - a - ε) / ε) * Real.smoothTransition ((b - ε - t) / ε)

/-- Its derivative. -/
noncomputable def thetaD (ε a b t : ℝ) : ℝ :=
  deriv Real.smoothTransition ((t - a - ε) / ε) / ε * Real.smoothTransition ((b - ε - t) / ε) -
    Real.smoothTransition ((t - a - ε) / ε) *
      (deriv Real.smoothTransition ((b - ε - t) / ε) / ε)

theorem contDiff_theta (ε a b : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (theta ε a b) := by
  unfold theta
  exact (Real.smoothTransition.contDiff.comp (by fun_prop)).mul
    (Real.smoothTransition.contDiff.comp (by fun_prop))

theorem hasDerivAt_theta (ε a b t : ℝ) (hε : 0 < ε) : HasDerivAt (theta ε a b) (thetaD ε a b t) t := by
  have hd := Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))
  have h1 : HasDerivAt (fun t : ℝ => (t - a - ε) / ε) (1 / ε) t := by
    simpa using (((hasDerivAt_id t).sub_const a).sub_const ε).div_const ε
  have h2 : HasDerivAt (fun t : ℝ => (b - ε - t) / ε) (-1 / ε) t := by
    simpa using ((hasDerivAt_id t).const_sub (b - ε)).div_const ε
  have e1 := ((hd.differentiable (by simp)) ((t - a - ε) / ε)).hasDerivAt.comp t h1
  have e2 := ((hd.differentiable (by simp)) ((b - ε - t) / ε)).hasDerivAt.comp t h2
  have := e1.mul e2
  unfold theta thetaD
  refine HasDerivAt.congr_deriv this ?_
  simp only [Function.comp]
  field_simp
  ring

theorem theta_nonneg (ε a b t : ℝ) : 0 ≤ theta ε a b t :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem theta_le_one (ε a b t : ℝ) : theta ε a b t ≤ 1 :=
  mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.le_one _)

theorem abs_theta_le_one (ε a b t : ℝ) : |theta ε a b t| ≤ 1 := by
  rw [abs_of_nonneg (theta_nonneg _ _ _ _)]; exact theta_le_one _ _ _ _

theorem theta_pos {ε a b t : ℝ} (hε : 0 < ε) (h : theta ε a b t ≠ 0) :
    a + ε < t ∧ t < b - ε := by
  by_contra hh
  apply h
  unfold theta
  rcases not_and_or.1 hh with h1 | h1
  · push Not at h1
    have h2 : (t - a - ε) / ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
    rw [Real.smoothTransition.zero_of_nonpos h2, zero_mul]
  · push Not at h1
    have h2 : (b - ε - t) / ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
    rw [Real.smoothTransition.zero_of_nonpos h2, mul_zero]

theorem theta_eq_one {ε a b t : ℝ} (hε : 0 < ε) (h1 : a + 2 * ε ≤ t) (h2 : t ≤ b - 2 * ε) :
    theta ε a b t = 1 := by
  unfold theta
  rw [Real.smoothTransition.one_of_one_le, Real.smoothTransition.one_of_one_le, one_mul]
  · rw [le_div_iff₀ hε]; linarith
  · rw [le_div_iff₀ hε]; linarith

theorem thetaD_eq_zero {ε a b t : ℝ} (hε : 0 < ε) (h1 : a + 2 * ε < t) (h2 : t < b - 2 * ε) :
    thetaD ε a b t = 0 := by
  unfold thetaD
  rw [deriv_smoothTransition_eq_zero, deriv_smoothTransition_eq_zero]
  · simp
  · right; rw [lt_div_iff₀ hε]; linarith
  · right; rw [lt_div_iff₀ hε]; linarith

theorem abs_thetaD_mul_trigS_le {a b : ℝ} (hab : a < b) {ε : ℝ} (hε : 0 < ε) (m : ℕ) (t : ℝ)
    {L : ℝ} (hL : ∀ y, |deriv Real.smoothTransition y| ≤ L) :
    |thetaD ε a b t * trigS a b m t| ≤ 4 * L * freq a b m := by
  have hf : 0 ≤ freq a b m := by
    unfold freq; have := sub_pos.2 hab; positivity
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL 0)
  have hA : |deriv Real.smoothTransition ((t - a - ε) / ε) / ε *
      Real.smoothTransition ((b - ε - t) / ε) * trigS a b m t| ≤ 2 * L * freq a b m := by
    by_cases hD : deriv Real.smoothTransition ((t - a - ε) / ε) = 0
    · simp only [hD, zero_div, zero_mul, abs_zero]; positivity
    by_cases hs : Real.smoothTransition ((b - ε - t) / ε) = 0
    · simp only [hs, mul_zero, zero_mul, abs_zero]; positivity
    have hy1 : 0 ≤ (t - a - ε) / ε ∧ (t - a - ε) / ε ≤ 1 := by
      by_contra hh
      apply hD
      apply deriv_smoothTransition_eq_zero
      by_contra h3; push Not at h3
      exact hh ⟨by linarith [h3.1], by linarith [h3.2]⟩
    have hy2 : 0 < (b - ε - t) / ε := by
      by_contra h3; push Not at h3
      exact hs (Real.smoothTransition.zero_of_nonpos h3)
    have h4 := (le_div_iff₀ hε).1 hy1.1
    have h5 := (div_le_iff₀ hε).1 hy1.2
    have h6 := (lt_div_iff₀ hε).1 hy2
    have ht : t ∈ Set.Icc a b := ⟨by linarith, by linarith⟩
    have hS : |trigS a b m t| ≤ freq a b m * (2 * ε) :=
      (abs_trigS_le_dist hab m ht).trans (mul_le_mul_of_nonneg_left
        ((min_le_left _ _).trans (by linarith)) hf)
    have hs1 : |Real.smoothTransition ((b - ε - t) / ε)| ≤ 1 := by
      rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]; exact Real.smoothTransition.le_one _
    rw [abs_mul, abs_mul, abs_div, abs_of_pos hε]
    calc _ ≤ (L / ε) * 1 * (freq a b m * (2 * ε)) := by
          gcongr
          exact hL _
      _ = 2 * L * freq a b m := by field_simp
  have hB : |Real.smoothTransition ((t - a - ε) / ε) *
      (deriv Real.smoothTransition ((b - ε - t) / ε) / ε) * trigS a b m t| ≤
        2 * L * freq a b m := by
    by_cases hD : deriv Real.smoothTransition ((b - ε - t) / ε) = 0
    · simp only [hD, zero_div, mul_zero, zero_mul, abs_zero]; positivity
    by_cases hs : Real.smoothTransition ((t - a - ε) / ε) = 0
    · simp only [hs, zero_mul, abs_zero]; positivity
    have hy1 : 0 ≤ (b - ε - t) / ε ∧ (b - ε - t) / ε ≤ 1 := by
      by_contra hh
      apply hD
      apply deriv_smoothTransition_eq_zero
      by_contra h3; push Not at h3
      exact hh ⟨by linarith [h3.1], by linarith [h3.2]⟩
    have hy2 : 0 < (t - a - ε) / ε := by
      by_contra h3; push Not at h3
      exact hs (Real.smoothTransition.zero_of_nonpos h3)
    have h4 := (le_div_iff₀ hε).1 hy1.1
    have h5 := (div_le_iff₀ hε).1 hy1.2
    have h6 := (lt_div_iff₀ hε).1 hy2
    have ht : t ∈ Set.Icc a b := ⟨by linarith, by linarith⟩
    have hS : |trigS a b m t| ≤ freq a b m * (2 * ε) :=
      (abs_trigS_le_dist hab m ht).trans (mul_le_mul_of_nonneg_left
        ((min_le_right _ _).trans (by linarith)) hf)
    have hs1 : |Real.smoothTransition ((t - a - ε) / ε)| ≤ 1 := by
      rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]; exact Real.smoothTransition.le_one _
    rw [abs_mul, abs_mul, abs_div, abs_of_pos hε]
    calc _ ≤ 1 * (L / ε) * (freq a b m * (2 * ε)) := by
          gcongr
          exact hL _
      _ = 2 * L * freq a b m := by field_simp
  have : thetaD ε a b t * trigS a b m t =
      deriv Real.smoothTransition ((t - a - ε) / ε) / ε *
        Real.smoothTransition ((b - ε - t) / ε) * trigS a b m t -
      Real.smoothTransition ((t - a - ε) / ε) *
        (deriv Real.smoothTransition ((b - ε - t) / ε) / ε) * trigS a b m t := by
    unfold thetaD; ring
  rw [this]
  calc _ ≤ _ := abs_sub _ _
    _ ≤ 2 * L * freq a b m + 2 * L * freq a b m := add_le_add hA hB
    _ = _ := by ring

end cutoff

/-! ### Cutoffs on the box and the codifferential of a cut-off eigenform -/

section ibp

variable (e a b) in
/-- The product cutoff. -/
noncomputable def chi (ε : ℝ) (x : E) : ℝ := ∏ j, theta ε (a j) (b j) ⟪e j, x⟫

theorem contDiff_chi (ε : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (chi e a b ε) := by
  unfold chi
  refine contDiff_prod fun j _ => ?_
  exact (contDiff_theta _ _ _).comp ((innerSL ℝ (e j)).contDiff)

theorem contDiff_trigProd' (s : Fin n → Bool) (m : Fin n → ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (trigProd e a b s m) := by
  unfold trigProd
  refine contDiff_prod fun j _ => ?_
  exact (contDiff_trig1 _ _ _ _).comp ((innerSL ℝ (e j)).contDiff)

theorem abs_prod_le_one' {ι : Type*} (s : Finset ι) (f : ι → ℝ) (h : ∀ i, |f i| ≤ 1) :
    |∏ i ∈ s, f i| ≤ 1 := by
  rw [Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun i _ => h i

theorem abs_chi_le (ε : ℝ) (x : E) : |chi e a b ε x| ≤ 1 :=
  abs_prod_le_one' _ _ fun _ => abs_theta_le_one _ _ _ _

theorem tsupport_chi_subset (hε : 0 < ε) :
    tsupport (chi e a b ε) ⊆ {x | ∀ j, ⟪e j, x⟫ ∈ Set.Icc (a j + ε) (b j - ε)} := by
  have hcl : IsClosed {x : E | ∀ j, ⟪e j, x⟫ ∈ Set.Icc (a j + ε) (b j - ε)} := by
    have : {x : E | ∀ j, ⟪e j, x⟫ ∈ Set.Icc (a j + ε) (b j - ε)} =
        ⋂ j, (fun x => ⟪e j, x⟫) ⁻¹' Set.Icc (a j + ε) (b j - ε) := by
      ext x; simp
    rw [this]
    exact isClosed_iInter fun j => isClosed_Icc.preimage (continuous_const.inner continuous_id)
  refine closure_minimal ?_ hcl
  intro x hx j
  have hne : chi e a b ε x ≠ 0 := hx
  have := (Finset.prod_ne_zero_iff.1 hne) j (Finset.mem_univ j)
  have h2 := theta_pos hε this
  exact ⟨h2.1.le, h2.2.le⟩

theorem tsupport_chi_subset_box (hε : 0 < ε) : tsupport (chi e a b ε) ⊆ box e a b := by
  intro x hx j
  have := tsupport_chi_subset hε hx j
  exact ⟨by linarith [this.1], by linarith [this.2]⟩

theorem hasCompactSupport_chi (hε : 0 < ε) : HasCompactSupport (chi e a b ε) := by
  have hcl : IsClosed {x : E | ∀ j, ⟪e j, x⟫ ∈ Set.Icc (a j + ε) (b j - ε)} := by
    have : {x : E | ∀ j, ⟪e j, x⟫ ∈ Set.Icc (a j + ε) (b j - ε)} =
        ⋂ j, (fun x => ⟪e j, x⟫) ⁻¹' Set.Icc (a j + ε) (b j - ε) := by
      ext x; simp
    rw [this]
    exact isClosed_iInter fun j => isClosed_Icc.preimage (continuous_const.inner continuous_id)
  have hK : IsCompact {x : E | ∀ j, ⟪e j, x⟫ ∈ Set.Icc (a j + ε) (b j - ε)} :=
    (isCompact_boxK e a b).of_isClosed_subset hcl fun x hx j =>
      ⟨by linarith [(hx j).1], by linarith [(hx j).2]⟩
  exact hK.of_isClosed_subset (isClosed_tsupport _) (tsupport_chi_subset hε)

theorem chi_eq_one {ε : ℝ} (hε : 0 < ε) {x : E}
    (h : ∀ j, a j + 2 * ε ≤ ⟪e j, x⟫ ∧ ⟪e j, x⟫ ≤ b j - 2 * ε) : chi e a b ε x = 1 :=
  Finset.prod_eq_one fun j _ => theta_eq_one hε (h j).1 (h j).2

theorem fderiv_chi_apply {ε : ℝ} (hε : 0 < ε) (x : E) (i : Fin n) :
    fderiv ℝ (chi e a b ε) x (e i) =
      thetaD ε (a i) (b i) ⟪e i, x⟫ *
        ∏ j ∈ Finset.univ.erase i, theta ε (a j) (b j) ⟪e j, x⟫ := by
  have := fderiv_prod_apply (e := e) (fun j => theta ε (a j) (b j))
    (fun j => (contDiff_theta _ _ _).differentiable (by simp)) x i
  rw [(hasDerivAt_theta ε (a i) (b i) _ hε).deriv] at this
  exact this

theorem fderiv_trigProd_apply (s : Fin n → Bool) (m : Fin n → ℕ) (x : E) (i : Fin n) :
    fderiv ℝ (trigProd e a b s m) x (e i) =
      deriv (trig1 (s i) (a i) (b i) (m i)) ⟪e i, x⟫ *
        ∏ j ∈ Finset.univ.erase i, trig1 (s j) (a j) (b j) (m j) ⟪e j, x⟫ :=
  fderiv_prod_apply (e := e) (fun j => trig1 (s j) (a j) (b j) (m j))
    (fun j => (contDiff_trig1 _ _ _ _).differentiable (by simp)) x i

theorem trigProd_split (s : Fin n → Bool) (m : Fin n → ℕ) (x : E) (i : Fin n) :
    trigProd e a b s m x = trig1 (s i) (a i) (b i) (m i) ⟪e i, x⟫ *
      ∏ j ∈ Finset.univ.erase i, trig1 (s j) (a j) (b j) (m j) ⟪e j, x⟫ := by
  unfold trigProd
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]

theorem codiff_smul_const_apply (g : E → ℝ) (hg : Differentiable ℝ g)
    (α : E [⋀^Fin (k + 1)]→L[ℝ] ℝ) (x : E) :
    codiff (fun y => g y • α) x = -∑ i, fderiv ℝ g x (e i) • α.curryLeft (e i) := by
  rw [codiff_eq_sum_basis e]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_smul_const (hg x)]
  exact curryLeft_smul' _ _ _

end ibp

section ibp2

theorem freq_nonneg' {a' b' : ℝ} (hab : a' < b') (m : ℕ) : 0 ≤ freq a' b' m := by
  unfold freq; have := sub_pos.2 hab; positivity

theorem abs_fderiv_g_le (hab : ∀ i, a i < b i) {L : ℝ} (hL : ∀ y, |deriv Real.smoothTransition y| ≤ L)
    {ε : ℝ} (hε : 0 < ε) (T' : Fin (k + 1) → Fin n) (m : Fin n → ℕ) (x : E) (i : Fin n)
    (hi : i ∈ Set.range T') :
    |fderiv ℝ (fun y => chi e a b ε y * trigProd e a b (pat T') m y) x (e i)| ≤
      freq (a i) (b i) (m i) * (1 + 4 * L) := by
  have hf := freq_nonneg' (hab i) (m i)
  have hp : pat T' i = true := (pat_eq_true_iff _ _).2 hi
  have hχd : Differentiable ℝ (chi e a b ε) := (contDiff_chi ε).differentiable (by simp)
  have hτd : Differentiable ℝ (trigProd e a b (pat T') m) :=
    (contDiff_trigProd' _ _).differentiable (by simp)
  rw [fderiv_fun_mul (hχd x) (hτd x)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    fderiv_chi_apply hε, fderiv_trigProd_apply]
  have htr : trig1 (pat T' i) (a i) (b i) (m i) = trigS (a i) (b i) (m i) := by
    funext t; simp [trig1, hp]
  have e1 : deriv (trig1 (pat T' i) (a i) (b i) (m i)) ⟪e i, x⟫ =
      freq (a i) (b i) (m i) * trigC (a i) (b i) (m i) ⟪e i, x⟫ := by
    rw [htr]; exact (hasDerivAt_trigS _ _).deriv
  have e2 := trigProd_split (e := e) (a := a) (b := b) (pat T') m x i
  rw [htr] at e2
  rw [e1, e2]
  set P := ∏ j ∈ Finset.univ.erase i, trig1 (pat T' j) (a j) (b j) (m j) ⟪e j, x⟫ with hPdef
  set Q := ∏ j ∈ Finset.univ.erase i, theta ε (a j) (b j) ⟪e j, x⟫ with hQdef
  have hP : |P| ≤ 1 := abs_prod_le_one' _ _ fun _ => abs_trig1_le _ _ _ _ _
  have hQ : |Q| ≤ 1 := abs_prod_le_one' _ _ fun _ => abs_theta_le_one _ _ _ _
  have hc := abs_trigC_le (a := a i) (b := b i) (m i) ⟪e i, x⟫
  have hχ := abs_chi_le (e := e) (a := a) (b := b) ε x
  have hT := abs_thetaD_mul_trigS_le (hab i) hε (m i) ⟪e i, x⟫ hL
  have h1 : |chi e a b ε x * (freq (a i) (b i) (m i) * trigC (a i) (b i) (m i) ⟪e i, x⟫ * P)| ≤
      freq (a i) (b i) (m i) := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hf]
    calc _ ≤ 1 * (freq (a i) (b i) (m i) * 1 * 1) := by
          gcongr
      _ = _ := by ring
  have h2 : |trigS (a i) (b i) (m i) ⟪e i, x⟫ * P * (thetaD ε (a i) (b i) ⟪e i, x⟫ * Q)| ≤
      4 * L * freq (a i) (b i) (m i) := by
    have : trigS (a i) (b i) (m i) ⟪e i, x⟫ * P * (thetaD ε (a i) (b i) ⟪e i, x⟫ * Q) =
        (thetaD ε (a i) (b i) ⟪e i, x⟫ * trigS (a i) (b i) (m i) ⟪e i, x⟫) * (P * Q) := by ring
    have hPQ : |P * Q| ≤ 1 := by
      rw [abs_mul]; nlinarith [abs_nonneg P, abs_nonneg Q]
    have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL 0)
    rw [this, abs_mul]
    calc _ ≤ 4 * L * freq (a i) (b i) (m i) * 1 :=
          mul_le_mul hT hPQ (abs_nonneg _) (mul_nonneg (by linarith) hf)
      _ = _ := by ring
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ freq (a i) (b i) (m i) + 4 * L * freq (a i) (b i) (m i) := add_le_add h1 h2
    _ = _ := by ring

theorem fderiv_g_eq {ε : ℝ} (hε : 0 < ε) (T' : Fin (k + 1) → Fin n) (m : Fin n → ℕ) (x : E)
    (h : ∀ j, a j + 2 * ε < ⟪e j, x⟫ ∧ ⟪e j, x⟫ < b j - 2 * ε) (i : Fin n) :
    fderiv ℝ (fun y => chi e a b ε y * trigProd e a b (pat T') m y) x (e i) =
      fderiv ℝ (trigProd e a b (pat T') m) x (e i) := by
  have hχd : Differentiable ℝ (chi e a b ε) := (contDiff_chi ε).differentiable (by simp)
  have hτd : Differentiable ℝ (trigProd e a b (pat T') m) :=
    (contDiff_trigProd' _ _).differentiable (by simp)
  rw [fderiv_fun_mul (hχd x) (hτd x)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    fderiv_chi_apply hε, thetaD_eq_zero hε (h i).1 (h i).2, zero_mul, mul_zero, add_zero,
    chi_eq_one hε (fun j => ⟨(h j).1.le, (h j).2.le⟩), one_mul]

theorem ofAlt_codiff_smul_const (g : E → ℝ) (hg : Differentiable ℝ g)
    (α : E [⋀^Fin (k + 1)]→L[ℝ] ℝ) (x : E) :
    Covector.ofAlt (codiff (fun y => g y • α) x) =
      -∑ i, fderiv ℝ g x (e i) • Covector.ofAlt (α.curryLeft (e i)) := by
  rw [codiff_smul_const_apply (e := e) g hg, map_neg, map_sum]
  simp [map_smul]

end ibp2

open Filter Topology in
/-- Integration by parts of a weakly differentiable form against a single eigenform. -/
theorem ibp_eigForm (hab : ∀ i, a i < b i) (u : L2Form (box e a b) k)
    (v : L2Form (box e a b) (k + 1)) (huv : HasWeakExtDeriv u v) (T' : Fin (k + 1) → Fin n)
    (m : Fin n → ℕ) :
    ∫ x in box e a b, ⟪v x, Covector.ofAlt (eigForm e a b T' m x)⟫ =
      ∫ x in box e a b, ⟪u x, Covector.ofAlt (codiff (eigForm e a b T' m) x)⟫ := by
  classical
  haveI : IsFiniteMeasure (volume.restrict (box e a b)) :=
    ⟨by simpa using volume_box_lt_top e a b⟩
  obtain ⟨L, hL0, hL⟩ := exists_bound_deriv_smoothTransition
  let τ : E → ℝ := trigProd e a b (pat T') m
  let ε : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hεpos : ∀ j, 0 < ε j := fun j => by positivity
  have hεt : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hτc : ContDiff ℝ (⊤ : ℕ∞) τ := contDiff_trigProd' _ _
  have hτd : Differentiable ℝ τ := hτc.differentiable (by simp)
  let g : ℕ → E → ℝ := fun j x => chi e a b (ε j) x * τ x
  have hgc : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (g j) := fun j => (contDiff_chi _).mul hτc
  have hgd : ∀ j, Differentiable ℝ (g j) := fun j => (hgc j).differentiable (by simp)
  have htest : ∀ j, IsTestForm (box e a b) (fun x => g j x • dxT e (k + 1) T') := by
    intro j
    refine IsTestForm.smul_const (hgc j) ?_ ?_ _
    · exact (hasCompactSupport_chi (hεpos j)).mul_right
    · exact (tsupport_mul_subset_left).trans (tsupport_chi_subset_box (hεpos j))
  have hw : ∀ j, ∫ x in box e a b, ⟪v x, Covector.ofAlt (g j x • dxT e (k + 1) T')⟫ =
      ∫ x in box e a b, ⟪u x, Covector.ofAlt
        (codiff (fun y => g j y • dxT e (k + 1) T') x)⟫ := by
    intro j
    have := huv _ (htest j)
    rw [L2.inner_def, L2.inner_def] at this
    have h1 : ∫ x in box e a b, ⟪v x, Covector.ofAlt (g j x • dxT e (k + 1) T')⟫ =
        ∫ x in box e a b, ⟪v x, (htest j).toLp x⟫ := by
      refine integral_congr_ae ?_
      filter_upwards [(htest j).coeFn_toLp] with x hx
      rw [hx]
    have h2 : ∫ x in box e a b, ⟪u x, Covector.ofAlt
        (codiff (fun y => g j y • dxT e (k + 1) T') x)⟫ =
        ∫ x in box e a b, ⟪u x, (htest j).codiff.toLp x⟫ := by
      refine integral_congr_ae ?_
      filter_upwards [(htest j).codiff.coeFn_toLp] with x hx
      rw [hx]
    rw [h1, h2]
    exact this
  -- eventually, the cutoff is invisible
  have hev : ∀ x ∈ box e a b, ∀ᶠ j in atTop, ∀ i, a i + 2 * ε j < ⟪e i, x⟫ ∧
      ⟪e i, x⟫ < b i - 2 * ε j := by
    intro x hx
    refine Filter.eventually_all.2 fun i => ?_
    have h1 : 0 < (⟪e i, x⟫ - a i) / 2 := by linarith [(hx i).1]
    have h2 : 0 < (b i - ⟪e i, x⟫) / 2 := by linarith [(hx i).2]
    filter_upwards [hεt.eventually (gt_mem_nhds h1), hεt.eventually (gt_mem_nhds h2)] with j hj1 hj2
    exact ⟨by linarith, by linarith⟩
  have hcm : ∀ (j : ℕ) {l : ℕ}, ∀ (f : E → E [⋀^Fin l]→L[ℝ] ℝ), Continuous f →
      Continuous fun x => Covector.ofAlt (f x) := fun j l f hf => Covector.ofAlt.continuous.comp hf
  -- the left-hand side
  have hlim1 : Tendsto (fun j => ∫ x in box e a b,
      ⟪v x, Covector.ofAlt (g j x • dxT e (k + 1) T')⟫) atTop
      (𝓝 (∫ x in box e a b, ⟪v x, Covector.ofAlt (eigForm e a b T' m x)⟫)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => ‖v x‖ * ‖Covector.ofAlt (dxT e (k + 1) T')‖) ?_ ?_ ?_ ?_
    · intro j
      refine (Lp.aestronglyMeasurable v).inner (Continuous.aestronglyMeasurable ?_)
      exact hcm j _ ((hgc j).continuous.smul continuous_const)
    · exact ((Lp.memLp v).integrable (by norm_num)).norm.mul_const _
    · intro j
      refine Filter.Eventually.of_forall fun x => ?_
      refine (norm_inner_le_norm _ _).trans ?_
      rw [map_smul, norm_smul]
      have : ‖g j x‖ ≤ 1 := by
        rw [Real.norm_eq_abs]
        simp only [g, abs_mul]
        exact mul_le_one₀ (abs_chi_le _ _) (abs_nonneg _) (abs_prod_le_one' _ _
          fun _ => abs_trig1_le _ _ _ _ _)
      calc _ ≤ ‖v x‖ * (1 * ‖Covector.ofAlt (dxT e (k + 1) T')‖) := by gcongr
        _ = _ := by ring
    · filter_upwards [ae_restrict_mem (isOpen_box e a b).measurableSet] with x hx
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev x hx] with j hj
      have : g j x = τ x := by
        simp only [g]
        rw [chi_eq_one (hεpos j) (fun i => ⟨(hj i).1.le, (hj i).2.le⟩), one_mul]
      show ⟪v x, Covector.ofAlt (eigForm e a b T' m x)⟫ =
        ⟪v x, Covector.ofAlt (g j x • dxT e (k + 1) T')⟫
      rw [this]
      rfl
  -- the right-hand side
  let c : Fin n → Covector E k := fun i => Covector.ofAlt ((dxT e (k + 1) T').curryLeft (e i))
  have hterm : ∀ j x i, ‖fderiv ℝ (g j) x (e i) • c i‖ ≤
      freq (a i) (b i) (m i) * (1 + 4 * L) * ‖c i‖ := by
    intro j x i
    by_cases hi : i ∈ Set.range T'
    · rw [norm_smul]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      rw [Real.norm_eq_abs]
      exact abs_fderiv_g_le hab hL (hεpos j) T' m x i hi
    · have h0 : c i = 0 := by
        simp [c, curryLeft_dxT_of_not_mem e hi]
      rw [h0]
      simp
  let B : ℝ := ∑ i, freq (a i) (b i) (m i) * (1 + 4 * L) * ‖c i‖
  have hlim2 : Tendsto (fun j => ∫ x in box e a b, ⟪u x, Covector.ofAlt
        (codiff (fun y => g j y • dxT e (k + 1) T') x)⟫) atTop
      (𝓝 (∫ x in box e a b, ⟪u x, Covector.ofAlt (codiff (eigForm e a b T' m) x)⟫)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖u x‖ * B) ?_ ?_ ?_ ?_
    · intro j
      refine (Lp.aestronglyMeasurable u).inner (Continuous.aestronglyMeasurable ?_)
      exact hcm j _ (htest j).codiff.contDiff.continuous
    · exact ((Lp.memLp u).integrable (by norm_num)).norm.mul_const _
    · intro j
      refine Filter.Eventually.of_forall fun x => ?_
      refine (norm_inner_le_norm _ _).trans ?_
      rw [ofAlt_codiff_smul_const (e := e) (g j) (hgd j), norm_neg]
      refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) (norm_nonneg _)
      exact Finset.sum_le_sum fun i _ => hterm j x i
    · filter_upwards [ae_restrict_mem (isOpen_box e a b).measurableSet] with x hx
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev x hx] with j hj
      show ⟪u x, Covector.ofAlt (codiff (fun y => τ y • dxT e (k + 1) T') x)⟫ =
        ⟪u x, Covector.ofAlt (codiff (fun y => g j y • dxT e (k + 1) T') x)⟫
      rw [ofAlt_codiff_smul_const (e := e) τ hτd, ofAlt_codiff_smul_const (e := e) (g j) (hgd j)]
      have hh : ∀ i, fderiv ℝ (g j) x (e i) = fderiv ℝ τ x (e i) := fun i =>
        fderiv_g_eq (hεpos j) T' m x hj i
      simp only [hh]
  exact tendsto_nhds_unique (hlim1.congr hw) hlim2

theorem ofAlt_codiff_eigForm (T' : Fin (k + 1) → Fin n) (m : Fin n → ℕ) (x : E) :
    Covector.ofAlt (codiff (eigForm e a b T' m) x) =
      ((k.factorial : ℝ))⁻¹ • ∑ i, ∑ S : Fin k → Fin n,
        (⟪e i, xi e a b m⟫ * ⟪Covector.ofAlt (dxT e (k + 1) T'),
          Covector.ofAlt (dxT e (k + 1) (Fin.cons i S : Fin (k + 1) → Fin n))⟫) •
          Covector.ofAlt (eigForm e a b S m x) := by
  have hτd : Differentiable ℝ (trigProd e a b (pat T') m) :=
    (contDiff_trigProd' _ _).differentiable (by simp)
  change Covector.ofAlt (codiff (fun y => trigProd e a b (pat T') m y • dxT e (k + 1) T') x) = _
  rw [ofAlt_codiff_smul_const (e := e) _ hτd]
  simp only [curryLeft_dxT_expand (e := e), map_smul, map_sum, Finset.smul_sum, smul_smul]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases hc : ⟪Covector.ofAlt (dxT e (k + 1) T'),
      Covector.ofAlt (dxT e (k + 1) (Fin.cons i S : Fin (k + 1) → Fin n))⟫ = 0
  · simp [hc]
  obtain ⟨hiT, hiS, hST⟩ := pat_of_inner_ne_zero (e := e) i S T' hc
  have htT : trig1 (pat T' i) (a i) (b i) (m i) = trigS (a i) (b i) (m i) := by
    funext t; simp [trig1, hiT]
  have htS : trig1 (pat S i) (a i) (b i) (m i) = trigC (a i) (b i) (m i) := by
    funext t; simp [trig1, hiS]
  have e1 : fderiv ℝ (trigProd e a b (pat T') m) x (e i) =
      freq (a i) (b i) (m i) * trigC (a i) (b i) (m i) ⟪e i, x⟫ *
        ∏ j ∈ Finset.univ.erase i, trig1 (pat T' j) (a j) (b j) (m j) ⟪e j, x⟫ := by
    rw [fderiv_trigProd_apply, htT, (hasDerivAt_trigS _ _).deriv]
  have e2 : trigProd e a b (pat S) m x = trigC (a i) (b i) (m i) ⟪e i, x⟫ *
        ∏ j ∈ Finset.univ.erase i, trig1 (pat T' j) (a j) (b j) (m j) ⟪e j, x⟫ := by
    rw [trigProd_split (i := i), htS]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [hST j (Finset.ne_of_mem_erase hj)]
  simp only [eigForm, map_smul, smul_smul]
  rw [e1, e2, inner_xi, ← neg_smul]
  congr 1
  ring

theorem coeFn_combo (c : Fin n → (Fin k → Fin n) → ℝ) (m : Fin n → ℕ) :
    (⇑(((k.factorial : ℝ))⁻¹ • ∑ i, ∑ S : Fin k → Fin n, c i S • eigLp e a b S m :
        L2Form (box e a b) k)) =ᵐ[volume.restrict (box e a b)]
      fun x => ((k.factorial : ℝ))⁻¹ • ∑ i, ∑ S : Fin k → Fin n,
        c i S • Covector.ofAlt (eigForm e a b S m x) := by
  have hi : ∀ i : Fin n, ∀ᵐ x ∂(volume.restrict (box e a b)),
      (⇑(∑ S : Fin k → Fin n, c i S • eigLp e a b S m : L2Form (box e a b) k)) x =
        ∑ S : Fin k → Fin n, c i S • Covector.ofAlt (eigForm e a b S m x) := by
    intro i
    filter_upwards [coeFn_sum_smul' (Finset.univ : Finset (Fin k → Fin n)) (c i)
      (fun S => eigLp e a b S m),
      ae_all_iff.2 fun S : Fin k → Fin n => coeFn_eigLp (e := e) (a := a) (b := b) S m]
      with x h1 h2
    rw [h1]
    simp only [h2]
  filter_upwards [Lp.coeFn_smul ((k.factorial : ℝ))⁻¹
      (∑ i, ∑ S : Fin k → Fin n, c i S • eigLp e a b S m),
    Lp.coeFn_finsetSum (μ := volume.restrict (box e a b)) (Finset.univ : Finset (Fin n))
      (fun i => ∑ S : Fin k → Fin n, c i S • eigLp e a b S m), ae_all_iff.2 hi] with x h1 h2 h3
  rw [h1, Pi.smul_apply, h2, Finset.sum_apply]
  simp only [h3]

/-- Integration by parts of a weakly differentiable form against an eigenform. -/
theorem inner_eigLp_ibp (hab : ∀ i, a i < b i) (u : L2Form (box e a b) k)
    (v : L2Form (box e a b) (k + 1)) (huv : HasWeakExtDeriv u v) (T' : Fin (k + 1) → Fin n)
    (m : Fin n → ℕ) :
    ⟪v, eigLp e a b T' m⟫ = ⟪u, ((k.factorial : ℝ))⁻¹ • ∑ i, ∑ S : Fin k → Fin n,
      (⟪e i, xi e a b m⟫ * ⟪Covector.ofAlt (dxT e (k + 1) T'),
        Covector.ofAlt (dxT e (k + 1) (Fin.cons i S : Fin (k + 1) → Fin n))⟫) •
          eigLp e a b S m⟫ := by
  rw [L2.inner_def, L2.inner_def]
  have h1 : ∫ x, ⟪v x, (eigLp e a b T' m) x⟫ ∂(volume.restrict (box e a b)) =
      ∫ x in box e a b, ⟪v x, Covector.ofAlt (eigForm e a b T' m x)⟫ := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_eigLp (e := e) (a := a) (b := b) T' m] with x hx
    rw [hx]
  rw [h1, ibp_eigForm hab u v huv T' m]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_combo (e := e) (a := a) (b := b) (fun i S =>
    ⟪e i, xi e a b m⟫ * ⟪Covector.ofAlt (dxT e (k + 1) T'),
      Covector.ofAlt (dxT e (k + 1) (Fin.cons i S : Fin (k + 1) → Fin n))⟫) m] with x hx
  rw [hx, ofAlt_codiff_eigForm]

theorem hasWeakExtDeriv_eigLp (hab : ∀ i, a i < b i) (T : Fin k → Fin n) (m : Fin n → ℕ) :
    HasWeakExtDeriv (eigLp e a b T m)
      (∑ i, (-freq (a i) (b i) (m i)) •
        eigLp e a b (Fin.cons i T : Fin (k + 1) → Fin n) m) := by
  classical
  refine hasWeakExtDeriv_prod_smul e a b
    (fun i => trig1 (pat T i) (a i) (b i) (m i))
    (fun i t => if pat T i = true then freq (a i) (b i) (m i) * trigC (a i) (b i) (m i) t
      else -(freq (a i) (b i) (m i) * trigS (a i) (b i) (m i) t))
    (dxT e k T) (fun i => (contDiff_trig1 _ _ _ _).continuous.measurable)
    (fun i => ⟨1, abs_trig1_le _ _ _ _⟩) ?_ ?_ ?_ _ (coeFn_eigLp T m) _ ?_
  · intro i
    by_cases h : pat T i = true
    · simp only [h, if_true]
      exact ((contDiff_trigC (a := a i) (b := b i) (m i)).continuous.const_mul _).measurable
    · simp only [h, if_false]
      exact (((contDiff_trigS (a := a i) (b := b i) (m i)).continuous.const_mul _).neg).measurable
  · intro i
    refine ⟨|freq (a i) (b i) (m i)|, fun t => ?_⟩
    by_cases h : pat T i = true
    · rw [if_pos h, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (abs_trigC_le _ _)
    · rw [if_neg h, abs_neg, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (abs_trigS_le _ _)
  · intro i
    by_cases hp : pat T i = true
    · left
      exact wedgeLeft_dxT_of_mem e ((pat_eq_true_iff T i).1 hp)
    · right
      have hp' : pat T i = false := by simpa using hp
      have hfun : trig1 (pat T i) (a i) (b i) (m i) = trigC (a i) (b i) (m i) := by
        funext t; simp [trig1, hp']
      refine ⟨⟨‖freq (a i) (b i) (m i)‖₊, ?_⟩, ∅, fun t _ _ => ?_⟩
      · rw [hfun]
        refine lipschitzWith_of_nnnorm_deriv_le
          ((contDiff_trigC (a := a i) (b := b i) (m i)).differentiable (by simp)) fun t => ?_
        rw [(hasDerivAt_trigC (a := a i) (b := b i) (m i) t).deriv]
        rw [nnnorm_neg, nnnorm_mul]
        refine mul_le_of_le_one_right (by positivity) ?_
        rw [← NNReal.coe_le_coe]
        simpa using abs_trigS_le (a := a i) (b := b i) (m i) t
      · simp only [hp, if_false, hfun]
        exact hasDerivAt_trigC _ _
  · have h1 := coeFn_sum_smul' (Finset.univ : Finset (Fin n))
      (fun i => -freq (a i) (b i) (m i))
      (fun i => eigLp e a b (Fin.cons i T : Fin (k + 1) → Fin n) m)
    filter_upwards [h1, ae_all_iff.2 fun i : Fin n =>
      coeFn_eigLp (e := e) (a := a) (b := b) (Fin.cons i T : Fin (k + 1) → Fin n) m] with x hx hx2
    rw [hx]
    simp only [hx2, map_sum, map_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hp : pat T i = true
    · have h0 : wedgeLeft (e i) (dxT e k T) = 0 := wedgeLeft_dxT_of_mem e ((pat_eq_true_iff T i).1 hp)
      simp [eigForm, ← wedgeLeft_dxT, h0]
    · have hp' : pat T i = false := by simpa using hp
      have ht : trig1 true (a i) (b i) (m i) = trigS (a i) (b i) (m i) := by
        funext t; simp [trig1]
      simp only [eigForm, ← wedgeLeft_dxT, map_smul, smul_smul, trigProd_cons, if_neg hp, ht]
      congr 1
      ring

theorem synth_pointwise (v : E) (α : Covector E k) (τ : (Fin (k + 1) → Fin n) → ℝ)
    (hτ : ∀ T T', Set.range T = Set.range T' → τ T = τ T') :
    (((k + 1).factorial : ℝ))⁻¹ • ∑ T' : Fin (k + 1) → Fin n,
        ⟪cwedge v α, Covector.ofAlt (dxT e (k + 1) T')⟫ •
          (τ T' • Covector.ofAlt (dxT e (k + 1) T')) =
      ((k.factorial : ℝ))⁻¹ • ∑ T : Fin k → Fin n, ⟪α, Covector.ofAlt (dxT e k T)⟫ •
        ∑ i, ⟪e i, v⟫ • (τ (Fin.cons i T : Fin (k + 1) → Fin n) •
          Covector.ofAlt (dxT e (k + 1) (Fin.cons i T : Fin (k + 1) → Fin n))) := by
  have hK : (((k + 1).factorial : ℝ)) ≠ 0 := by positivity
  have hk : ((k.factorial : ℝ)) ≠ 0 := by positivity
  have key : ∀ T' : Fin (k + 1) → Fin n,
      ⟪cwedge v α, Covector.ofAlt (dxT e (k + 1) T')⟫ •
          (τ T' • Covector.ofAlt (dxT e (k + 1) T')) =
        ((k.factorial : ℝ))⁻¹ • ∑ S : Fin k → Fin n, ⟪α, Covector.ofAlt (dxT e k S)⟫ •
          ∑ i, ⟪e i, v⟫ • (⟪Covector.ofAlt (dxT e (k + 1) (Fin.cons i S : Fin (k + 1) → Fin n)),
            Covector.ofAlt (dxT e (k + 1) T')⟫ • (τ T' • Covector.ofAlt (dxT e (k + 1) T'))) := by
    intro T'
    rw [inner_cwedge_dxC (e := e), mul_smul, Finset.sum_smul]
    refine congrArg _ (Finset.sum_congr rfl fun S _ => ?_)
    rw [mul_smul, Finset.sum_smul]
    refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
    rw [mul_smul]
  simp only [key]
  rw [← Finset.smul_sum (r := ((k.factorial : ℝ))⁻¹), Finset.sum_comm]
  have h2 : ∀ S : Fin k → Fin n,
      ∑ T' : Fin (k + 1) → Fin n, ⟪α, Covector.ofAlt (dxT e k S)⟫ •
          ∑ i, ⟪e i, v⟫ • (⟪Covector.ofAlt (dxT e (k + 1) (Fin.cons i S : Fin (k + 1) → Fin n)),
            Covector.ofAlt (dxT e (k + 1) T')⟫ • (τ T' • Covector.ofAlt (dxT e (k + 1) T'))) =
        ⟪α, Covector.ofAlt (dxT e k S)⟫ • ∑ i, ((k + 1).factorial : ℝ) •
          (⟪e i, v⟫ • (τ (Fin.cons i S : Fin (k + 1) → Fin n) •
            Covector.ofAlt (dxT e (k + 1) (Fin.cons i S : Fin (k + 1) → Fin n)))) := by
    intro S
    rw [← Finset.smul_sum, Finset.sum_comm]
    refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
    rw [← Finset.smul_sum, sum_inner_dxC_tau (e := e) _ τ hτ]
    simp only [smul_smul]
    congr 1
    ring
  simp only [h2]
  have h3 : ∀ S : Fin k → Fin n, ⟪α, Covector.ofAlt (dxT e k S)⟫ •
      ∑ i, ((k + 1).factorial : ℝ) • (⟪e i, v⟫ • (τ (Fin.cons i S : Fin (k + 1) → Fin n) •
        Covector.ofAlt (dxT e (k + 1) (Fin.cons i S : Fin (k + 1) → Fin n)))) =
      ((k + 1).factorial : ℝ) • (⟪α, Covector.ofAlt (dxT e k S)⟫ •
      ∑ i, (⟪e i, v⟫ • (τ (Fin.cons i S : Fin (k + 1) → Fin n) •
        Covector.ofAlt (dxT e (k + 1) (Fin.cons i S : Fin (k + 1) → Fin n))))) := by
    intro S
    rw [← Finset.smul_sum, smul_comm]
  rw [Finset.sum_congr rfl fun S _ => h3 S, ← Finset.smul_sum, smul_smul, smul_smul]
  congr 1
  field_simp

theorem synth_cwedge_eq (m : Fin n → ℕ) (α : Covector E k) :
    synth e a b m (cwedge (xi e a b m) α) =
      ((k.factorial : ℝ))⁻¹ • ∑ T : Fin k → Fin n, ⟪α, Covector.ofAlt (dxT e k T)⟫ •
        ∑ i, (-freq (a i) (b i) (m i)) •
          eigLp e a b (Fin.cons i T : Fin (k + 1) → Fin n) m := by
  refine Lp.ext ?_
  have hT : ∀ T : Fin k → Fin n, ∀ᵐ x ∂(volume.restrict (box e a b)),
      (⇑(∑ i, (-freq (a i) (b i) (m i)) •
        eigLp e a b (Fin.cons i T : Fin (k + 1) → Fin n) m : L2Form (box e a b) (k + 1))) x =
      ∑ i, (-freq (a i) (b i) (m i)) •
        Covector.ofAlt (eigForm e a b (Fin.cons i T : Fin (k + 1) → Fin n) m x) := by
    intro T
    filter_upwards [coeFn_sum_smul' (Finset.univ : Finset (Fin n))
      (fun i => -freq (a i) (b i) (m i))
      (fun i => eigLp e a b (Fin.cons i T : Fin (k + 1) → Fin n) m),
      ae_all_iff.2 fun i : Fin n =>
      coeFn_eigLp (e := e) (a := a) (b := b) (Fin.cons i T : Fin (k + 1) → Fin n) m]
      with x h1 h2
    rw [h1]
    simp only [h2]
  filter_upwards [synth_ae (e := e) (a := a) (b := b) m (cwedge (xi e a b m) α),
    Lp.coeFn_smul ((k.factorial : ℝ))⁻¹ (∑ T : Fin k → Fin n,
      ⟪α, Covector.ofAlt (dxT e k T)⟫ • ∑ i, (-freq (a i) (b i) (m i)) •
        eigLp e a b (Fin.cons i T : Fin (k + 1) → Fin n) m),
    coeFn_sum_smul' (Finset.univ : Finset (Fin k → Fin n))
      (fun T => ⟪α, Covector.ofAlt (dxT e k T)⟫)
      (fun T => ∑ i, (-freq (a i) (b i) (m i)) •
        eigLp e a b (Fin.cons i T : Fin (k + 1) → Fin n) m),
    ae_all_iff.2 hT] with x h1 h2 h3 h4
  rw [h1, h2, Pi.smul_apply, h3]
  simp only [h4]
  have := synth_pointwise (e := e) (xi e a b m) α
    (fun S => trigProd e a b (pat S) m x)
    (fun S T h => by rw [pat_eq_of_range_eq h])
  simp only [inner_xi] at this
  simp only [eigForm, map_smul, smul_smul]
  convert this using 1
  · refine congrArg _ (Finset.sum_congr rfl fun T' _ => ?_)
    simp only [smul_smul]
  · refine congrArg _ (Finset.sum_congr rfl fun T _ => ?_)
    refine congrArg _ ?_
    simp only [Finset.smul_sum, smul_smul]

theorem hasWeakExtDeriv_synth (hab : ∀ i, a i < b i) (m : Fin n → ℕ) (α : Covector E k) :
    HasWeakExtDeriv (synth e a b m α) (synth e a b m (cwedge (xi e a b m) α)) := by
  rw [synth_cwedge_eq]
  exact (hasWeakExtDeriv_sum _ _ _ fun T _ =>
    (hasWeakExtDeriv_eigLp hab T m).smul _).smul _

variable (e a b) in
/-- `synth m α` as an element of `HΛᵏ`. -/
noncomputable def synthH (hab : ∀ i, a i < b i) (m : Fin n → ℕ) (α : Covector E k) :
    HΛ (box e a b) k :=
  ⟨WithLp.toLp 2 (synth e a b m α, synth e a b m (cwedge (xi e a b m) α)),
    hasWeakExtDeriv_synth hab m α⟩

theorem sum_inner_inner {j : ℕ} (γ X : Covector E j) :
    ∑ T : Fin j → Fin n, ⟪γ, Covector.ofAlt (dxT e j T)⟫ * ⟪Covector.ofAlt (dxT e j T), X⟫ =
      (j.factorial : ℝ) * ⟪γ, X⟫ := by
  have h := congrArg (fun y => ⟪y, X⟫) (sum_inner_dxC (e := e) γ)
  simp only [real_inner_smul_left, sum_inner] at h
  have hne : (j.factorial : ℝ) ≠ 0 := by positivity
  rw [← h]
  field_simp

theorem inner_ccontr_dxC (v : E) (γ : Covector E (k + 1)) (S : Fin k → Fin n) :
    ⟪ccontr v γ, Covector.ofAlt (dxT e k S)⟫ =
      ∑ i, ⟪e i, v⟫ * ⟪γ, Covector.ofAlt (dxT e (k + 1) (Fin.cons i S : Fin (k + 1) → Fin n))⟫ := by
  rw [ccontr_eq_sum (e := e), sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_left]
  congr 1
  unfold ccontr
  have := inner_curryLeft_dxT (e := e) γ.toAlt i S
  simpa using this

/-- **Integration by parts against eigenforms.** -/
theorem inner_d_synth (hab : ∀ i, a i < b i) (w : HΛ (box e a b) k) (m : Fin n → ℕ)
    (γ : Covector E (k + 1)) :
    ⟪HΛ.toL2 (HΛ.d w), synth e a b m γ⟫ =
      ⟪HΛ.toL2 w, synth e a b m (ccontr (xi e a b m) γ)⟫ := by
  have huv := HΛ.hasWeakExtDeriv w
  set u := HΛ.toL2 w with hu
  set v := HΛ.toL2 (HΛ.d w) with hv
  simp only [synth, inner_smul_right, inner_sum]
  simp only [inner_eigLp_ibp hab u v huv, inner_smul_right, inner_sum]
  simp only [inner_ccontr_dxC (e := e)]
  have key : ∀ (i : Fin n) (S : Fin k → Fin n),
      ∑ T' : Fin (k + 1) → Fin n, ⟪γ, Covector.ofAlt (dxT e (k + 1) T')⟫ *
        ⟪Covector.ofAlt (dxT e (k + 1) T'),
          Covector.ofAlt (dxT e (k + 1) (Fin.cons i S : Fin (k + 1) → Fin n))⟫ =
      ((k + 1).factorial : ℝ) *
        ⟪γ, Covector.ofAlt (dxT e (k + 1) (Fin.cons i S : Fin (k + 1) → Fin n))⟫ :=
    fun i S => sum_inner_inner (e := e) _ _
  have hK : (((k + 1).factorial : ℝ)) ≠ 0 := by positivity
  have hk : ((k.factorial : ℝ)) ≠ 0 := by positivity
  -- reorganise the left-hand side
  have hL : ∀ T' : Fin (k + 1) → Fin n,
      ⟪γ, Covector.ofAlt (dxT e (k + 1) T')⟫ * (((k.factorial : ℝ))⁻¹ * ∑ i, ∑ S : Fin k → Fin n,
        (⟪e i, xi e a b m⟫ * ⟪Covector.ofAlt (dxT e (k + 1) T'),
          Covector.ofAlt (dxT e (k + 1) (Fin.cons i S : Fin (k + 1) → Fin n))⟫) * ⟪u, eigLp e a b S m⟫) =
      ((k.factorial : ℝ))⁻¹ * ∑ i, ∑ S : Fin k → Fin n, ⟪e i, xi e a b m⟫ * ⟪u, eigLp e a b S m⟫ *
        (⟪γ, Covector.ofAlt (dxT e (k + 1) T')⟫ * ⟪Covector.ofAlt (dxT e (k + 1) T'),
          Covector.ofAlt (dxT e (k + 1) (Fin.cons i S : Fin (k + 1) → Fin n))⟫) := by
    intro T'
    rw [mul_left_comm, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    ring
  simp only [hL]
  rw [← Finset.mul_sum, Finset.sum_comm]
  rw [Finset.sum_congr rfl fun y _ => Finset.sum_comm]
  simp only [← Finset.mul_sum, key, Finset.sum_mul]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ) (f := fun (S : Fin k → Fin n) (i : Fin n) =>
    ⟪e i, xi e a b m⟫ * ⟪γ, Covector.ofAlt (dxT e (k + 1) (Fin.cons i S : Fin (k + 1) → Fin n))⟫ *
      ⟪u, eigLp e a b S m⟫)]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun S _ => ?_
  field_simp


theorem coef_d (hab : ∀ i, a i < b i) (w : HΛ (box e a b) k) (m : Fin n → ℕ) :
    coef e a b (HΛ.toL2 (HΛ.d w)) m = cwedge (xi e a b m) (coef e a b (HΛ.toL2 w) m) := by
  have hN := normProd_pos hab m
  refine ext_inner_right ℝ fun γ => ?_
  have h1 := inner_d_synth hab w m γ
  rw [inner_synth hab, inner_synth hab] at h1
  rw [inner_cwedge]
  exact mul_left_cancel₀ hN.ne' h1

end Fourier

end FEEC
