/-
One-dimensional approximation by the shape/dual quasi-interpolant.
-/
import FEEC.Tensor.Ref1DSchur
import FEEC.Tensor.Ref1DBiorth

/-!
# One-dimensional approximation

The one-dimensional operator `P g (t) = ∑ⱼ shapeⱼ(t) ∫ dualⱼ g` reproduces constants, and for
`C¹` functions `g - P g` is an integral operator applied to `g'` whose kernel has Schur
constants of order `h`.
-/

namespace FEEC

open MeasureTheory

namespace Ref

variable {a b : ℝ} {N : ℕ}


theorem integrable_dual (hab : a < b) (hN : 0 < N) (s : Bool) (j : ℕ) :
    Integrable (dual a b N s j) :=
  (contDiff_dual hab hN s j).continuous.integrable_of_hasCompactSupport
    (IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _)
      ((tsupport_dual_subset hab hN s j).trans Set.Ioo_subset_Icc_self))

theorem sum_hat_eq_one (N : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (huN : u < N) :
    ∑ i ∈ Finset.range (N + 2), (if i ≤ N then hat (u - i) else 0) = 1 := by
  have hf := Nat.floor_le hu0
  have hf2 := Nat.lt_floor_add_one u
  have hfN : ⌊u⌋₊ < N := (Nat.floor_lt hu0).2 huN
  rw [← Finset.sum_subset (s₁ := {⌊u⌋₊, ⌊u⌋₊ + 1}) ?_ ?_]
  · rw [Finset.sum_pair (by omega), if_pos (by omega), if_pos (by omega)]
    have e1 : hat (u - ⌊u⌋₊) = 1 - (u - ⌊u⌋₊) := hat_of_pos (by linarith) (by linarith)
    have e2 : hat (u - ((⌊u⌋₊ + 1 : ℕ) : ℝ)) = 1 + (u - ((⌊u⌋₊ + 1 : ℕ) : ℝ)) :=
      by
        unfold hat
        rw [abs_of_nonpos (by push_cast; linarith), max_eq_right (by push_cast; linarith)]
        ring
    rw [e1, e2]; push_cast; ring
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rw [Finset.mem_range]; omega
  · intro i _ hi
    by_cases h0 : i ≤ N
    · rw [if_pos h0]
      by_contra hne
      have := hat_ne_zero hne
      rw [abs_lt] at this
      exact hi (idx_two (by linarith [this.1]) (by linarith [this.2]))
    · rw [if_neg h0]

theorem sum_ind_eq_one (N : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (huN : u < N) :
    ∑ i ∈ Finset.range (N + 2),
      (if (1 ≤ i ∧ i ≤ N ∧ (i : ℝ) - 1 ≤ u ∧ u < i) then (1 : ℝ) else 0) = 1 := by
  have hf := Nat.floor_le hu0
  have hf2 := Nat.lt_floor_add_one u
  have hfN : ⌊u⌋₊ < N := (Nat.floor_lt hu0).2 huN
  rw [Finset.sum_eq_single (⌊u⌋₊ + 1)]
  · rw [if_pos]
    refine ⟨by omega, by omega, ?_, ?_⟩ <;> push_cast <;> linarith
  · intro i _ hi
    rw [if_neg]
    rintro ⟨h1, _, h3, h4⟩
    exact hi (by simpa using idx_one h1 h3 h4)
  · intro h; exfalso; apply h; rw [Finset.mem_range]; omega

theorem sum_shape_eq_one (hab : a < b) (hN : 0 < N) (s : Bool) {t : ℝ} (ht : t ∈ Set.Ioo a b) :
    ∑ i ∈ Finset.range (N + 2), shape a b N s i t = 1 := by
  have hu := coord_mem_Ioo hab hN ht
  cases s
  · simp_rw [shape_false_eq]; exact sum_hat_eq_one N hu.1.le hu.2
  · simp_rw [shape_true_eq]; exact sum_ind_eq_one N hu.1.le hu.2

theorem integral_dual_eq_one (hab : a < b) (hN : 0 < N) (s : Bool) {j : ℕ} (hj : Valid N s j) :
    ∫ y in Set.Ioo a b, dual a b N s j y = 1 := by
  have hjN : j ≤ N := by
    cases s
    · exact valid_false_iff.1 hj
    · exact (valid_true_iff.1 hj).2
  have h1 : ∫ y in Set.Ioo a b, dual a b N s j y =
      ∫ y in Set.Ioo a b, ∑ i ∈ Finset.range (N + 2), shape a b N s i y * dual a b N s j y := by
    refine setIntegral_congr_fun measurableSet_Ioo fun y hy => ?_
    rw [← Finset.sum_mul, sum_shape_eq_one hab hN s hy, one_mul]
  rw [h1, integral_finset_sum _ (fun i _ =>
    ((integrable_dual hab hN s j).bdd_mul (c := 1) (measurable_shape s i).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simpa using abs_shape_le_one s i x)).integrableOn)]
  simp_rw [integral_shape_mul_dual hab hN s]
  rw [Finset.sum_eq_single j]
  · simp [hj]
  · intro i _ hi; simp [hi]
  · intro hjn; exfalso; apply hjn; rw [Finset.mem_range]; omega

/-- Partition of unity: `P` reproduces constants. -/
theorem sum_shape_mul_integral_dual (hab : a < b) (hN : 0 < N) (s : Bool) {t : ℝ}
    (ht : t ∈ Set.Ioo a b) :
    ∑ j ∈ Finset.range (N + 2),
      shape a b N s j t * ∫ y in Set.Ioo a b, dual a b N s j y = 1 := by
  rw [← sum_shape_eq_one hab hN s ht]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hv : Valid N s j
  · rw [integral_dual_eq_one hab hN s hv, mul_one]
  · have : shape a b N s j t = 0 := by simp [shape, hv]
    rw [this, zero_mul]

/-- The kernel of `g' ↦ g - P g`. -/
noncomputable def rKer (a b : ℝ) (N : ℕ) (s : Bool) (t τ : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (N + 2), shape a b N s j t *
    ∫ y in Set.Ioo a b, dual a b N s j y *
      ((if y < τ ∧ τ < t then 1 else 0) - (if t < τ ∧ τ < y then 1 else 0))


theorem measurable_nodeDual (j : ℕ) : Measurable (nodeDual a b N j) := by
  have hc : Measurable (coord a b N) := continuous_coord.measurable
  unfold nodeDual
  split_ifs
  · exact (rho_contDiff.continuous.measurable.comp (hc.sub measurable_const)).div_const _
  · exact (rho_contDiff.continuous.measurable.comp (measurable_const.sub hc)).div_const _
  · exact measurable_const

theorem measurable_cumul {g : ℝ → ℝ} (hg : Measurable g) : Measurable (cumul g) := by
  have : cumul g = fun x => ∫ y, (if y ≤ x then g y else 0) := by
    funext x; unfold cumul
    rw [← integral_indicator measurableSet_Iic]
    simp [Set.indicator_apply]
  rw [this]
  have hm : StronglyMeasurable (fun q : ℝ × ℝ => if q.2 ≤ q.1 then g q.2 else 0) :=
    Measurable.stronglyMeasurable (Measurable.ite (measurableSet_le measurable_snd measurable_fst)
      (hg.comp measurable_snd) measurable_const)
  exact (hm.integral_prod_right' (ν := volume)).measurable

theorem measurable_dual (s : Bool) (j : ℕ) : Measurable (dual a b N s j) := by
  unfold dual
  split_ifs
  · exact measurable_cumul (((measurable_nodeDual _).sub (measurable_nodeDual _)).div_const _)
  · exact measurable_nodeDual j
  · exact measurable_const

/-- The indicator combination appearing in the kernel. -/
noncomputable def kI (y τ t : ℝ) : ℝ :=
  (if y < τ ∧ τ < t then 1 else 0) - (if t < τ ∧ τ < y then 1 else 0)

theorem measurable_kI : Measurable (fun p : ℝ × ℝ × ℝ => kI p.1 p.2.1 p.2.2) := by
  unfold kI
  refine Measurable.sub (Measurable.ite ?_ measurable_const measurable_const)
    (Measurable.ite ?_ measurable_const measurable_const)
  · exact (measurableSet_lt measurable_fst (measurable_fst.comp measurable_snd)).inter
      (measurableSet_lt (measurable_fst.comp measurable_snd) (measurable_snd.comp measurable_snd))
  · exact (measurableSet_lt measurable_snd.snd (measurable_fst.comp measurable_snd)).inter
      (measurableSet_lt (measurable_fst.comp measurable_snd) measurable_fst)

theorem abs_kI_le (y τ t : ℝ) : |kI y τ t| ≤ 1 := by
  unfold kI
  split_ifs <;> norm_num

theorem rKer_eq (s : Bool) (t τ : ℝ) : rKer a b N s t τ =
    ∑ j ∈ Finset.range (N + 2), shape a b N s j t *
      ∫ y in Set.Ioo a b, dual a b N s j y * kI y τ t := rfl

theorem measurable_rKer (s : Bool) : Measurable (Function.uncurry (rKer a b N s)) := by
  have : Function.uncurry (rKer a b N s) = fun p : ℝ × ℝ =>
      ∑ j ∈ Finset.range (N + 2), shape a b N s j p.1 *
        ∫ y in Set.Ioo a b, dual a b N s j y * kI y p.2 p.1 := by
    funext p; rfl
  rw [this]
  refine Finset.measurable_sum _ fun j _ => ?_
  refine ((measurable_shape s j).comp measurable_fst).mul ?_
  have hm : StronglyMeasurable (fun q : (ℝ × ℝ) × ℝ => dual a b N s j q.2 * kI q.2 q.1.2 q.1.1) := by
    refine Measurable.stronglyMeasurable (Measurable.mul ?_ ?_)
    · exact (measurable_dual s j).comp measurable_snd
    · exact measurable_kI.comp (measurable_snd.prodMk
        ((measurable_snd.comp measurable_fst).prodMk (measurable_fst.comp measurable_fst)))
  exact (hm.integral_prod_right' (ν := volume.restrict (Set.Ioo a b))).measurable


theorem hasCompactSupport_dual (hab : a < b) (hN : 0 < N) (s : Bool) (j : ℕ) :
    HasCompactSupport (dual a b N s j) :=
  IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _)
    ((tsupport_dual_subset hab hN s j).trans Set.Ioo_subset_Icc_self)

theorem integral_dual_mul_sub (hab : a < b) (hN : 0 < N) (s : Bool) (j : ℕ) {g : ℝ → ℝ}
    (hg : Continuous g) (t : ℝ) :
    ∫ y in Set.Ioo a b, dual a b N s j y * (g t - g y) =
      g t * (∫ y in Set.Ioo a b, dual a b N s j y) - ∫ y in Set.Ioo a b, dual a b N s j y * g y := by
  have h1 : IntegrableOn (fun y => dual a b N s j y * g t) (Set.Ioo a b) :=
    ((integrable_dual hab hN s j).mul_const _).integrableOn
  have h2 : IntegrableOn (fun y => dual a b N s j y * g y) (Set.Ioo a b) :=
    (((contDiff_dual hab hN s j).continuous.mul hg).integrable_of_hasCompactSupport
      ((hasCompactSupport_dual hab hN s j).mul_right)).integrableOn
  simp_rw [mul_sub]
  rw [integral_sub h1 h2, integral_mul_const, mul_comm]

theorem ftc_helper (hab : a < b) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) {y t : ℝ}
    (hy : y ∈ Set.Ioo a b) (ht : t ∈ Set.Ioo a b) :
    ∫ τ in Set.Ioo a b, kI y τ t * deriv g τ = g t - g y := by
  have hd : ∀ x, HasDerivAt g (deriv g x) x := fun x =>
    ((hg.differentiable one_ne_zero).differentiableAt (x := x)).hasDerivAt
  have hc : Continuous (deriv g) := hg.continuous_deriv le_rfl
  have key : ∀ {l r : ℝ}, l ∈ Set.Ioo a b → r ∈ Set.Ioo a b → l ≤ r →
      ∫ τ in Set.Ioo a b, (Set.Ioo l r).indicator (deriv g) τ = g r - g l := by
    intro l r hl hr hlr
    rw [setIntegral_indicator measurableSet_Ioo,
      Set.inter_eq_right.2 (Set.Ioo_subset_Ioo hl.1.le hr.2.le),
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hlr]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
      (hc.intervalIntegrable _ _)
  rcases le_or_gt y t with h | h
  · have : ∀ τ, kI y τ t * deriv g τ = (Set.Ioo y t).indicator (deriv g) τ := by
      intro τ
      unfold kI
      rw [Set.indicator_apply]
      by_cases h1 : y < τ ∧ τ < t
      · have h2 : ¬ (t < τ ∧ τ < y) := fun h2 => by linarith [h1.1, h2.2]
        simp [Set.mem_Ioo, h1, h2]
      · have h2 : ¬ (t < τ ∧ τ < y) := fun h2 => by linarith [h2.1, h2.2]
        simp [Set.mem_Ioo, h1, h2]
    simp_rw [this]
    exact key hy ht h
  · have : ∀ τ, kI y τ t * deriv g τ = -(Set.Ioo t y).indicator (deriv g) τ := by
      intro τ
      unfold kI
      rw [Set.indicator_apply]
      by_cases h1 : t < τ ∧ τ < y
      · have h2 : ¬ (y < τ ∧ τ < t) := fun h2 => by linarith [h1.1, h2.2]
        simp [Set.mem_Ioo, h1, h2]
      · have h2 : ¬ (y < τ ∧ τ < t) := fun h2 => by linarith [h2.1, h2.2]
        simp [Set.mem_Ioo, h1, h2]
    simp_rw [this]
    rw [integral_neg, key ht hy h.le]
    ring

theorem integrable_prod_term (hab : a < b) (hN : 0 < N) (s : Bool) (j : ℕ) {g : ℝ → ℝ}
    (hg : ContDiff ℝ 1 g) (t : ℝ) :
    Integrable (Function.uncurry fun τ y => dual a b N s j y * kI y τ t * deriv g τ)
      ((volume.restrict (Set.Ioo a b)).prod (volume.restrict (Set.Ioo a b))) := by
  have hc : Continuous (deriv g) := hg.continuous_deriv le_rfl
  obtain ⟨Bd, hBd⟩ := (contDiff_dual hab hN s j).continuous.bounded_above_of_compact_support
    (hasCompactSupport_dual hab hN s j)
  obtain ⟨Bg, hBg⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := deriv g) (s := Set.Icc a b)
    hc.continuousOn
  have hBd0 : 0 ≤ Bd := (norm_nonneg _).trans (hBd 0)
  have hBg0 : 0 ≤ Bg := (norm_nonneg _).trans (hBg a ⟨le_rfl, hab.le⟩)
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioo a b)) := ⟨by simp⟩
  refine Integrable.of_bound (C := Bd * 1 * Bg) ?_ ?_
  · refine Measurable.aestronglyMeasurable ?_
    have : Measurable (fun p : ℝ × ℝ => dual a b N s j p.2 * kI p.2 p.1 t * deriv g p.1) := by
      refine Measurable.mul (Measurable.mul ?_ ?_) (hc.measurable.comp measurable_fst)
      · exact (measurable_dual s j).comp measurable_snd
      · exact measurable_kI.comp (measurable_snd.prodMk
          (measurable_fst.prodMk measurable_const))
    exact this
  · rw [Measure.prod_restrict, ae_restrict_iff' (measurableSet_Ioo.prod measurableSet_Ioo)]
    refine Filter.Eventually.of_forall fun p hp => ?_
    have hτ : p.1 ∈ Set.Icc a b := Set.Ioo_subset_Icc_self hp.1
    show ‖dual a b N s j p.2 * kI p.2 p.1 t * deriv g p.1‖ ≤ Bd * 1 * Bg
    rw [norm_mul, norm_mul]
    refine mul_le_mul (mul_le_mul (hBd _) ?_ (norm_nonneg _) hBd0) (hBg _ hτ) (norm_nonneg _)
      (by positivity)
    simpa using abs_kI_le p.2 p.1 t

theorem term_eq (hab : a < b) (hN : 0 < N) (s : Bool) (j : ℕ) {g : ℝ → ℝ}
    (hg : ContDiff ℝ 1 g) {t : ℝ} (ht : t ∈ Set.Ioo a b) :
    IntegrableOn (fun τ => (∫ y in Set.Ioo a b, dual a b N s j y * kI y τ t) * deriv g τ)
        (Set.Ioo a b) ∧
      ∫ τ in Set.Ioo a b, (∫ y in Set.Ioo a b, dual a b N s j y * kI y τ t) * deriv g τ =
        ∫ y in Set.Ioo a b, dual a b N s j y * (g t - g y) := by
  have hI := integrable_prod_term hab hN s j hg t
  have e1 : ∀ τ, (∫ y in Set.Ioo a b, dual a b N s j y * kI y τ t) * deriv g τ =
      ∫ y in Set.Ioo a b, dual a b N s j y * kI y τ t * deriv g τ :=
    fun τ => (integral_mul_const _ _).symm
  simp_rw [e1]
  refine ⟨hI.integral_prod_left, ?_⟩
  rw [integral_integral_swap hI]
  refine setIntegral_congr_fun measurableSet_Ioo fun y hy => ?_
  have : ∀ τ, dual a b N s j y * kI y τ t * deriv g τ =
      dual a b N s j y * (kI y τ t * deriv g τ) := fun τ => mul_assoc _ _ _
  simp only [this]
  rw [integral_const_mul, ftc_helper hab hg hy ht]

/-- The error of `P` is an integral operator applied to the derivative. -/
theorem sub_sum_shape_eq_integral_rKer (hab : a < b) (hN : 0 < N) (s : Bool)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) {t : ℝ} (ht : t ∈ Set.Ioo a b) :
    g t - ∑ j ∈ Finset.range (N + 2),
        shape a b N s j t * ∫ y in Set.Ioo a b, dual a b N s j y * g y =
      ∫ τ in Set.Ioo a b, rKer a b N s t τ * deriv g τ := by
  have hone := sum_shape_mul_integral_dual hab hN s ht
  have hA : g t - ∑ j ∈ Finset.range (N + 2),
        shape a b N s j t * ∫ y in Set.Ioo a b, dual a b N s j y * g y =
      ∑ j ∈ Finset.range (N + 2),
        shape a b N s j t * ∫ y in Set.Ioo a b, dual a b N s j y * (g t - g y) := by
    simp_rw [integral_dual_mul_sub hab hN s _ hg.continuous, mul_sub, Finset.sum_sub_distrib]
    have : ∑ j ∈ Finset.range (N + 2), shape a b N s j t *
        (g t * ∫ y in Set.Ioo a b, dual a b N s j y) = g t := by
      simp_rw [mul_left_comm _ (g t)]
      rw [← Finset.mul_sum, hone, mul_one]
    rw [this]
  rw [hA]
  have h2 : ∀ τ, rKer a b N s t τ * deriv g τ = ∑ j ∈ Finset.range (N + 2),
      shape a b N s j t * ((∫ y in Set.Ioo a b, dual a b N s j y * kI y τ t) * deriv g τ) := by
    intro τ
    rw [rKer_eq, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp_rw [h2]
  rw [integral_finsetSum _ (fun j _ => Integrable.const_mul (term_eq hab hN s j hg ht).1 _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, (term_eq hab hN s j hg ht).2]


theorem supp_close (hab : a < b) (hN : 0 < N) (s : Bool) {j : ℕ} {t y : ℝ}
    (hs : shape a b N s j t ≠ 0) (hd : dual a b N s j y ≠ 0) :
    |t - y| < 2 * meshH a b N := by
  have hh := meshH_pos hab hN
  have hty : t - y = meshH a b N * (coord a b N t - coord a b N y) := by
    unfold coord; field_simp; ring
  suffices h : |coord a b N t - coord a b N y| < 2 by
    rw [hty, abs_mul, abs_of_pos hh]
    exact (mul_lt_mul_of_pos_left h hh).trans_eq (mul_comm _ _)
  cases s
  · obtain ⟨h1, h2⟩ := shape_false_supp hs
    obtain ⟨_, hne⟩ := dual_false_ne_zero hd
    rw [abs_lt]
    rcases nodeDual_ne_zero hne with ⟨_, h3, h4⟩ | ⟨hk, h3, h4⟩
    · constructor <;> linarith
    · have : (j : ℝ) = N := by exact_mod_cast hk
      constructor <;> linarith
  · obtain ⟨_, h1, h2⟩ := shape_true_supp hs
    obtain ⟨_, _, h3, h4⟩ := dual_true_supp hab hN hd
    rw [abs_lt]; constructor <;> linarith

theorem kI_eq_zero_of_far {y τ t h : ℝ} (hτ : ¬ |t - τ| < h) (hy : |t - y| < h) : kI y τ t = 0 := by
  have hy' := abs_lt.1 hy
  unfold kI
  rw [if_neg, if_neg, sub_zero]
  · rintro ⟨h1, h2⟩
    exact hτ (abs_lt.2 ⟨by linarith, by linarith⟩)
  · rintro ⟨h1, h2⟩
    exact hτ (abs_lt.2 ⟨by linarith, by linarith⟩)

theorem rKer_bound (hab : a < b) (hN : 0 < N) (s : Bool) {K₁ : ℝ}
    (hK : ∀ x, ∑ j ∈ Finset.range (N + 2),
      |shape a b N s j x| * ∫ y in Set.Ioo a b, |dual a b N s j y| ≤ K₁) (t τ : ℝ) :
    |rKer a b N s t τ| ≤ if |t - τ| < 2 * meshH a b N then K₁ else 0 := by
  split_ifs with hτ
  · rw [rKer_eq]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun j _ => ?_).trans (hK t))
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    calc |∫ y in Set.Ioo a b, dual a b N s j y * kI y τ t|
        ≤ ∫ y in Set.Ioo a b, |dual a b N s j y * kI y τ t| := abs_integral_le_integral_abs
      _ ≤ ∫ y in Set.Ioo a b, |dual a b N s j y| :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => abs_nonneg _)
            (integrable_dual hab hN s j).abs.integrableOn
            (Filter.Eventually.of_forall fun y => by
              show |dual a b N s j y * kI y τ t| ≤ |dual a b N s j y|
              rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (abs_kI_le _ _ _))
  · have : rKer a b N s t τ = 0 := by
      rw [rKer_eq]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hs : shape a b N s j t = 0
      · rw [hs, zero_mul]
      · have : ∀ y, dual a b N s j y * kI y τ t = 0 := fun y => by
          by_cases hd : dual a b N s j y = 0
          · rw [hd, zero_mul]
          · rw [kI_eq_zero_of_far hτ (supp_close hab hN s hs hd), mul_zero]
        simp_rw [this]; simp
    rw [this]; simp

theorem int_bound (hab : a < b) (hN : 0 < N) {K₁ : ℝ} (hK₁ : 0 ≤ K₁) (f : ℝ → ℝ) (c : ℝ)
    (hf : ∀ x, |f x| ≤ if |x - c| < 2 * meshH a b N then K₁ else 0) :
    ∫ x in Set.Ioo a b, |f x| ≤ 4 * K₁ * meshH a b N := by
  have hh := meshH_pos hab hN
  set G : ℝ → ℝ := (Set.Icc (c - 2 * meshH a b N) (c + 2 * meshH a b N)).indicator (fun _ => K₁)
    with hG
  have hGi : Integrable G :=
    (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
  have hG0 : ∀ x, 0 ≤ G x := fun x => Set.indicator_nonneg (fun _ _ => hK₁) x
  calc ∫ x in Set.Ioo a b, |f x| ≤ ∫ x in Set.Ioo a b, G x := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => abs_nonneg _)
          hGi.integrableOn (Filter.Eventually.of_forall fun x => ?_)
        have := hf x
        by_cases hx : |x - c| < 2 * meshH a b N
        · rw [if_pos hx] at this
          have hx' := abs_lt.1 hx
          rw [hG, Set.indicator_of_mem (by rw [Set.mem_Icc]; constructor <;> linarith)]
          exact this
        · rw [if_neg hx] at this
          exact this.trans (hG0 x)
    _ ≤ ∫ x, G x := setIntegral_le_integral hGi (Filter.Eventually.of_forall hG0)
    _ = 4 * K₁ * meshH a b N := by
        rw [hG, integral_indicator_const _ measurableSet_Icc, measureReal_def, Real.volume_Icc,
          ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
        ring

/-- Schur constants of `rKer` are `O(h)`, with an absolute constant. -/
theorem exists_rKer_schur : ∃ K : ℝ, 0 ≤ K ∧ ∀ (a b : ℝ) (N : ℕ), a < b → 0 < N →
    ∀ s : Bool,
      (∀ t, ∫ τ in Set.Ioo a b, |rKer a b N s t τ| ≤ K * meshH a b N) ∧
      (∀ τ, ∫ t in Set.Ioo a b, |rKer a b N s t τ| ≤ K * meshH a b N) ∧
      (∀ t, IntegrableOn (fun τ => rKer a b N s t τ) (Set.Ioo a b)) := by
  obtain ⟨K₁, hK₁0, hK₁⟩ := exists_schur_const
  refine ⟨4 * K₁, by positivity, ?_⟩
  intro a b N hab hN s
  have hbd := rKer_bound hab hN s (hK₁ a b N hab hN s).1
  refine ⟨fun t => ?_, fun τ => ?_, fun t => ?_⟩
  · exact int_bound hab hN hK₁0 (fun τ => rKer a b N s t τ) t (fun τ => by
      rw [abs_sub_comm]; exact hbd t τ)
  · exact int_bound hab hN hK₁0 (fun t => rKer a b N s t τ) τ (fun t => hbd t τ)
  · refine Measure.integrableOn_of_bounded (M := K₁) (by simp) ?_ ?_
    · exact ((measurable_rKer s).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun τ => ?_
      have := hbd t τ
      rw [Real.norm_eq_abs]
      split_ifs at this
      · exact this
      · exact this.trans hK₁0

end Ref

end FEEC
