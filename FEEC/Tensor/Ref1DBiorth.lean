/-
Biorthogonality of the one-dimensional shape and dual functions.
-/
import FEEC.Tensor.Ref1D

namespace FEEC

open MeasureTheory

namespace Ref

variable {a b : ℝ} {N : ℕ}

/-- Change of variables to the reference coordinate. -/
theorem integral_comp_coord (hab : a < b) (hN : 0 < N) (f : ℝ → ℝ) :
    ∫ x, f (coord a b N x) = meshH a b N * ∫ t, f t := by
  have hh := meshH_pos hab hN
  unfold coord
  have h1 : ∫ x : ℝ, f ((x - a) / meshH a b N) = ∫ x : ℝ, f (x / meshH a b N) :=
    integral_sub_right_eq_self (fun x => f (x / meshH a b N)) a
  rw [h1, Measure.integral_comp_div, abs_of_pos hh, smul_eq_mul]

theorem coord_mono (hab : a < b) (hN : 0 < N) : Monotone (coord a b N) := by
  have hh := meshH_pos hab hN
  intro x y hxy
  unfold coord
  exact div_le_div_of_nonneg_right (by linarith) hh.le

theorem integral_Iic_comp_coord (hab : a < b) (hN : 0 < N) (f : ℝ → ℝ) (x : ℝ) :
    ∫ y in Set.Iic x, f (coord a b N y) = meshH a b N * ∫ t in Set.Iic (coord a b N x), f t := by
  have hh := meshH_pos hab hN
  have key : ∀ y, Set.indicator (Set.Iic x) (fun y => f (coord a b N y)) y =
      (Set.indicator (Set.Iic (coord a b N x)) f) (coord a b N y) := by
    intro y
    have : y ∈ Set.Iic x ↔ coord a b N y ∈ Set.Iic (coord a b N x) := by
      simp only [Set.mem_Iic]
      constructor
      · exact fun h => coord_mono hab hN h
      · intro h
        unfold coord at h
        have := (div_le_div_iff_of_pos_right hh).1 h
        linarith
    by_cases hy : y ∈ Set.Iic x
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (this.1 hy)]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem (fun h => hy (this.2 h))]
  rw [← integral_indicator measurableSet_Iic, ← integral_indicator measurableSet_Iic]
  simp_rw [key]
  exact integral_comp_coord hab hN _

/-- The primitive of `rho`. -/
noncomputable def F (u : ℝ) : ℝ := cumul rho u

theorem rho_isBump : IsBump rho 0 1 :=
  ⟨rho_contDiff, rho_tsupport, integral_rho⟩

theorem rho_eq_zero {t : ℝ} (ht : ¬ (0 < t ∧ t < 1)) : rho t = 0 := by
  by_contra h
  exact ht (rho_tsupport (subset_tsupport _ h))

theorem rho_integrable : Integrable rho :=
  rho_contDiff.continuous.integrable_of_hasCompactSupport rho_isBump.hasCompactSupport

theorem hasDerivAt_F (u : ℝ) : HasDerivAt F (rho u) u := rho_isBump.hasDerivAt_cumul u

theorem continuous_F : Continuous F := continuous_iff_continuousAt.2 fun u => (hasDerivAt_F u).continuousAt

theorem F_eq_zero {u : ℝ} (hu : u ≤ 0) : F u = 0 := by
  unfold F cumul
  refine setIntegral_eq_zero_of_forall_eq_zero fun t ht => rho_eq_zero ?_
  have : t ≤ u := ht
  intro h; linarith [h.1]

theorem F_eq_one {u : ℝ} (hu : 1 ≤ u) : F u = 1 := by
  unfold F cumul
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero, integral_rho]
  intro t ht
  refine rho_eq_zero ?_
  have : ¬ t ≤ u := ht
  intro h; linarith [h.2]

theorem integral_F_zero_one : ∫ u in (0:ℝ)..1, F u = 1 := by
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := 1)
    (u := fun u : ℝ => u) (v := F) (u' := fun _ => 1) (v' := rho)
    (fun x _ => hasDerivAt_id x) (fun x _ => hasDerivAt_F x)
    (by simp) (rho_contDiff.continuous.intervalIntegrable _ _)
  have h2 : ∫ x in (0:ℝ)..1, x * rho x = 0 := by
    have : ∫ x in (0:ℝ)..1, x * rho x = ∫ x, x * rho x := by
      rw [intervalIntegral.integral_of_le zero_le_one,
        ← integral_Icc_eq_integral_Ioc, setIntegral_eq_integral_of_forall_compl_eq_zero]
      intro t ht
      have : rho t = 0 := rho_eq_zero (fun h => ht ⟨h.1.le, h.2.le⟩)
      simp [this]
    rw [this, integral_mul_rho]
  rw [h2, F_eq_one le_rfl, F_eq_zero le_rfl] at h
  simp at h; linarith

theorem integral_F_nat (n : ℕ) : ∫ u in (n:ℝ)..(n + 1), F u = 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using integral_F_zero_one
  · have : ∫ u in (n:ℝ)..(n + 1), F u = ∫ u in (n:ℝ)..(n + 1), (1:ℝ) := by
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [Set.uIcc_of_le (by linarith)] at hu
      have : (1:ℝ) ≤ n := by exact_mod_cast hn
      exact F_eq_one (by linarith [hu.1])
    rw [this]; simp

theorem integral_Iic_sub (g : ℝ → ℝ) (c d : ℝ) :
    ∫ t in Set.Iic c, g (t - d) = ∫ t in Set.Iic (c - d), g t := by
  rw [← integral_indicator measurableSet_Iic, ← integral_indicator measurableSet_Iic]
  rw [← integral_sub_right_eq_self (Set.indicator (Set.Iic (c - d)) g) d]
  congr 1
  funext t
  by_cases h : t ≤ c
  · rw [Set.indicator_of_mem (show t ∈ Set.Iic c from h),
      Set.indicator_of_mem (show t - d ∈ Set.Iic (c - d) by simp only [Set.mem_Iic]; linarith)]
  · rw [Set.indicator_of_notMem (show t ∉ Set.Iic c from h),
      Set.indicator_of_notMem (show t - d ∉ Set.Iic (c - d) by simp only [Set.mem_Iic]; intro h'; apply h; linarith)]

theorem integral_Iic_reflect (g : ℝ → ℝ) (c d : ℝ) :
    ∫ t in Set.Iic c, g (d - t) = ∫ u in Set.Ici (d - c), g u := by
  rw [← integral_indicator measurableSet_Iic, ← integral_indicator measurableSet_Ici]
  rw [← integral_sub_left_eq_self (Set.indicator (Set.Ici (d - c)) g) volume d]
  congr 1
  funext t
  by_cases h : t ≤ c
  · rw [Set.indicator_of_mem (show t ∈ Set.Iic c from h),
      Set.indicator_of_mem (show d - t ∈ Set.Ici (d - c) by simp only [Set.mem_Ici]; linarith)]
  · rw [Set.indicator_of_notMem (show t ∉ Set.Iic c from h),
      Set.indicator_of_notMem (show d - t ∉ Set.Ici (d - c) by simp only [Set.mem_Ici]; intro h'; apply h; linarith)]

theorem integral_Ici_rho (e : ℝ) : ∫ u in Set.Ici e, rho u = 1 - F e := by
  have h := integral_add_compl (μ := volume) (measurableSet_Ici (a := e)) rho_integrable
  rw [Set.compl_Ici, integral_rho] at h
  unfold F cumul
  rw [integral_Iic_eq_integral_Iio]
  linarith

/-- The primitive of a node dual in reference coordinates. -/
noncomputable def P (N : ℕ) (m : ℕ) (t : ℝ) : ℝ :=
  if m < N then F (t - m) else 1 - F (m - t)

theorem cumul_nodeDual (hab : a < b) (hN : 0 < N) {m : ℕ} (hm : m ≤ N) (x : ℝ) :
    cumul (nodeDual a b N m) x = P N m (coord a b N x) := by
  have hh := meshH_pos hab hN
  unfold cumul P
  by_cases hmN : m < N
  · rw [if_pos hmN]
    have : nodeDual a b N m = fun y => (fun t => rho (t - m) / meshH a b N) (coord a b N y) := by
      funext y; simp [nodeDual, hmN]
    rw [this, integral_Iic_comp_coord hab hN, integral_div, integral_Iic_sub]
    unfold F cumul
    field_simp
  · rw [if_neg hmN]
    have hmN' : m = N := le_antisymm hm (not_lt.1 hmN)
    have : nodeDual a b N m = fun y => (fun t => rho (m - t) / meshH a b N) (coord a b N y) := by
      funext y; simp [nodeDual, hmN, hmN']
    rw [this, integral_Iic_comp_coord hab hN, integral_div, integral_Iic_reflect, integral_Ici_rho]
    field_simp

theorem integrable_nodeDual (hab : a < b) (hN : 0 < N) (m : ℕ) : Integrable (nodeDual a b N m) := by
  refine (contDiff_nodeDual hab hN m).continuous.integrable_of_hasCompactSupport ?_
  exact IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _)
    ((tsupport_nodeDual_subset hab hN m).trans Set.Ioo_subset_Icc_self)

theorem dual_true_eq (hab : a < b) (hN : 0 < N) {j : ℕ} (hj1 : 1 ≤ j) (hjN : j ≤ N) (x : ℝ) :
    dual a b N true j x = (P N (j - 1) (coord a b N x) - P N j (coord a b N x)) / meshH a b N := by
  have hV : Valid N true j := by simp [Valid, hj1, hjN]
  have hh := meshH_pos hab hN
  unfold dual
  rw [if_pos hV, if_pos rfl]
  unfold cumul
  rw [integral_div, integral_sub (integrable_nodeDual hab hN _).integrableOn
    (integrable_nodeDual hab hN _).integrableOn]
  have h1 := cumul_nodeDual hab hN (m := j - 1) (by omega) x
  have h2 := cumul_nodeDual hab hN (m := j) hjN x
  unfold cumul at h1 h2
  rw [h1, h2]

theorem continuous_P (m : ℕ) : Continuous (P N m) := by
  unfold P
  split_ifs
  · exact continuous_F.comp (continuous_id.sub continuous_const)
  · exact continuous_const.sub (continuous_F.comp (continuous_const.sub continuous_id))

theorem integral_Ico_P {m i : ℕ} (hm : m ≤ N) (hi1 : 1 ≤ i) (hiN : i ≤ N) :
    ∫ t in Set.Ico ((i:ℝ) - 1) i, P N m t = if m < N ∧ m + 1 ≤ i then 1 else 0 := by
  have hle : (i:ℝ) - 1 ≤ i := by linarith
  rw [integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hle]
  unfold P
  by_cases hmN : m < N
  · simp only [if_pos hmN]
    rw [intervalIntegral.integral_comp_sub_right (fun u => F u) (m:ℝ)]
    by_cases him : m + 1 ≤ i
    · rw [if_pos ⟨hmN, him⟩]
      obtain ⟨n, hn⟩ : ∃ n : ℕ, i = m + 1 + n := ⟨i - (m + 1), by omega⟩
      have e1 : (i:ℝ) - 1 - m = n := by rw [hn]; push_cast; ring
      have e2 : (i:ℝ) - m = n + 1 := by rw [hn]; push_cast; ring
      rw [e1, e2, integral_F_nat]
    · rw [if_neg (fun h => him h.2)]
      have : i ≤ m := by omega
      have hc : (i:ℝ) ≤ m := by exact_mod_cast this
      have : ∫ u in (i:ℝ) - 1 - m..i - m, F u = ∫ u in (i:ℝ) - 1 - m..i - m, (0:ℝ) := by
        refine intervalIntegral.integral_congr fun u hu => ?_
        rw [Set.uIcc_of_le (by linarith)] at hu
        exact F_eq_zero (by linarith [hu.2])
      rw [this]; simp
  · simp only [if_neg hmN]
    rw [if_neg (fun h => hmN h.1)]
    have hmN' : m = N := le_antisymm hm (not_lt.1 hmN)
    have hF : IntervalIntegrable (fun t : ℝ => F ((m:ℝ) - t)) volume ((i:ℝ) - 1) i :=
      (continuous_F.comp (continuous_const.sub continuous_id)).intervalIntegrable _ _
    rw [intervalIntegral.integral_sub intervalIntegrable_const hF,
      intervalIntegral.integral_comp_sub_left (fun u => F u) (m:ℝ)]
    obtain ⟨n, hn⟩ : ∃ n : ℕ, N = i + n := ⟨N - i, by omega⟩
    have e1 : (m:ℝ) - i = n := by rw [hmN', hn]; push_cast; ring
    have e2 : (m:ℝ) - (i - 1) = n + 1 := by rw [hmN', hn]; push_cast; ring
    rw [e1, e2, integral_F_nat]
    simp

theorem hat_eq_zero_of {t : ℝ} (h : 1 ≤ t ∨ t ≤ -1) : hat t = 0 := by
  unfold hat
  have : 1 ≤ |t| := by
    rcases h with h | h
    · exact le_trans h (le_abs_self t)
    · exact le_trans (by linarith) (neg_le_abs t)
  exact max_eq_left (by linarith)

theorem hat_node_lt (i j : ℕ) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    hat (u + j - i) = if i = j then 1 - u else if i = j + 1 then u else 0 := by
  by_cases h1 : i = j
  · subst h1
    simp only [if_true, add_sub_cancel_right]
    unfold hat
    rw [abs_of_pos hu0]
    exact max_eq_right (by linarith)
  · rw [if_neg h1]
    by_cases h2 : i = j + 1
    · subst h2
      simp only [if_true]
      unfold hat
      have : u + (j:ℝ) - ((j + 1 : ℕ):ℝ) = u - 1 := by push_cast; ring
      rw [this, abs_of_neg (by linarith)]
      exact (max_eq_right (by linarith)).trans (by ring)
    · rw [if_neg h2]
      apply hat_eq_zero_of
      rcases Nat.lt_or_ge i j with h | h
      · left
        have : (i:ℝ) + 1 ≤ j := by exact_mod_cast h
        linarith
      · right
        have : (j:ℝ) + 2 ≤ i := by exact_mod_cast (by omega : j + 2 ≤ i)
        linarith

theorem hat_node_N (i : ℕ) (hiN : i ≤ N) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    hat ((N:ℝ) - u - i) = if i = N then 1 - u else if i + 1 = N then u else 0 := by
  by_cases h1 : i = N
  · subst h1
    simp only [if_true, sub_self]
    unfold hat
    have : (i:ℝ) - u - i = -u := by ring
    rw [this, abs_neg, abs_of_pos hu0]
    exact max_eq_right (by linarith)
  · rw [if_neg h1]
    by_cases h2 : i + 1 = N
    · subst h2
      simp only [if_true]
      unfold hat
      have : ((i + 1 : ℕ):ℝ) - u - i = 1 - u := by push_cast; ring
      rw [this, abs_of_pos (by linarith)]
      exact (max_eq_right (by linarith)).trans (by ring)
    · rw [if_neg h2]
      apply hat_eq_zero_of
      left
      have : (i:ℝ) + 2 ≤ N := by exact_mod_cast (by omega : i + 2 ≤ N)
      linarith

theorem integrable_mul_rho : Integrable (fun u => u * rho u) :=
  (continuous_id.mul rho_contDiff.continuous).integrable_of_hasCompactSupport
    (rho_isBump.hasCompactSupport.mul_left)

theorem integral_rho_mul_case (P1 P2 : Prop) [Decidable P1] [Decidable P2] :
    ∫ u, rho u * (if P1 then 1 - u else if P2 then u else 0) =
      if P1 then 1 else 0 := by
  by_cases h1 : P1
  · simp only [if_pos h1]
    have : ∀ u, rho u * (1 - u) = rho u - u * rho u := fun u => by ring
    simp_rw [this]
    rw [integral_sub rho_integrable integrable_mul_rho, integral_rho, integral_mul_rho]; simp
  · simp only [if_neg h1]
    by_cases h2 : P2
    · simp only [if_pos h2]
      have : ∀ u, rho u * u = u * rho u := fun u => by ring
      simp_rw [this]
      exact integral_mul_rho
    · simp [if_neg h2]

/-- **Biorthogonality** of shape and dual functions of the same type. -/
theorem integral_shape_mul_dual (hab : a < b) (hN : 0 < N) (s : Bool) (i j : ℕ) :
    ∫ x in Set.Ioo a b, shape a b N s i x * dual a b N s j x =
      if Valid N s i ∧ i = j then 1 else 0 := by
  have hh := meshH_pos hab hN
  by_cases hi : Valid N s i
  swap
  · have : ∀ x, shape a b N s i x = 0 := fun x => by simp [shape, hi]
    simp [this, hi]
  by_cases hj : Valid N s j
  swap
  · have : ∀ x, dual a b N s j x = 0 := fun x => by simp [dual, hj]
    have hij : ¬ i = j := by rintro rfl; exact hj hi
    simp [this, hij]
  have hsupp : ∫ x in Set.Ioo a b, shape a b N s i x * dual a b N s j x =
      ∫ x, shape a b N s i x * dual a b N s j x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have : dual a b N s j x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hx (tsupport_dual_subset hab hN s j h))
    simp [this]
  rw [hsupp]
  cases s
  · -- nodes
    have hiN : i ≤ N := by simpa [Valid] using hi
    have hjN : j ≤ N := by simpa [Valid] using hj
    have hsh : ∀ x, shape a b N false i x = hat (coord a b N x - i) := fun x => by
      simp [shape, hi]
    have hdu : ∀ x, dual a b N false j x = nodeDual a b N j x := fun x => by simp [dual, hj]
    simp_rw [hsh, hdu]
    have hV : (Valid N false i ∧ i = j) ↔ (if j < N then i = j else i = N) := by
      by_cases hjlt : j < N
      · simp only [if_pos hjlt]
        constructor
        · exact fun h => h.2
        · intro h; exact ⟨hi, h⟩
      · have : j = N := le_antisymm hjN (not_lt.1 hjlt)
        subst this
        simp only [if_neg hjlt]
        constructor
        · exact fun h => h.2
        · intro h; exact ⟨hi, h⟩
    by_cases hjlt : j < N
    · have e : (fun x => hat (coord a b N x - i) * nodeDual a b N j x) =
          fun x => (fun t => hat (t - i) * (rho (t - j) / meshH a b N)) (coord a b N x) := by
        funext x; simp [nodeDual, hjlt]
      rw [e]
      refine Eq.trans (integral_comp_coord hab hN (fun t => hat (t - i) * (rho (t - j) / meshH a b N))) ?_
      have e2 : ∀ t : ℝ, hat (t - i) * (rho (t - j) / meshH a b N) =
          (1 / meshH a b N) * (hat (t - i) * rho (t - j)) := fun t => by ring
      simp_rw [e2]
      rw [integral_const_mul]
      have := integral_add_right_eq_self (μ := volume)
        (fun t : ℝ => hat (t - i) * rho (t - j)) (j:ℝ)
      simp only [add_sub_cancel_right] at this
      rw [← this]
      have e3 : ∀ u : ℝ, hat (u + j - i) * rho u =
          rho u * (if i = j then 1 - u else if i = j + 1 then u else 0) := by
        intro u
        by_cases hu : 0 < u ∧ u < 1
        · rw [hat_node_lt i j hu.1 hu.2]; ring
        · rw [rho_eq_zero hu]; simp
      simp_rw [e3]
      rw [integral_rho_mul_case]
      have : (if Valid N false i ∧ i = j then (1:ℝ) else 0) = if i = j then 1 else 0 := by
        simp [hi]
      rw [this]
      field_simp
    · have hjN' : N = j := (le_antisymm hjN (not_lt.1 hjlt)).symm
      subst hjN'
      have e : (fun x => hat (coord a b N x - i) * nodeDual a b N N x) =
          fun x => (fun t => hat (t - i) * (rho (N - t) / meshH a b N)) (coord a b N x) := by
        funext x; simp [nodeDual, hjlt]
      rw [e]
      refine Eq.trans (integral_comp_coord hab hN (fun t => hat (t - i) * (rho (N - t) / meshH a b N))) ?_
      have e2 : ∀ t : ℝ, hat (t - i) * (rho (N - t) / meshH a b N) =
          (1 / meshH a b N) * (hat (t - i) * rho (N - t)) := fun t => by ring
      simp_rw [e2]
      rw [integral_const_mul]
      have := integral_sub_left_eq_self (μ := volume)
        (fun u : ℝ => hat ((N:ℝ) - u - i) * rho u) (N:ℝ)
      simp only [sub_sub_cancel] at this
      rw [this]
      have e3 : ∀ u : ℝ, hat ((N:ℝ) - u - i) * rho u =
          rho u * (if i = N then 1 - u else if i + 1 = N then u else 0) := by
        intro u
        by_cases hu : 0 < u ∧ u < 1
        · rw [hat_node_N i hiN hu.1 hu.2]; ring
        · rw [rho_eq_zero hu]; simp
      simp_rw [e3]
      rw [integral_rho_mul_case]
      have : (if Valid N false i ∧ i = N then (1:ℝ) else 0) = if i = N then 1 else 0 := by
        simp [hi]
      rw [this]
      field_simp
  · -- cells
    have hi' : 1 ≤ i ∧ i ≤ N := by simpa [Valid] using hi
    have hj' : 1 ≤ j ∧ j ≤ N := by simpa [Valid] using hj
    have hsh : ∀ x, shape a b N true i x =
        Set.indicator (Set.Ico ((i:ℝ) - 1) i) (fun _ => (1:ℝ)) (coord a b N x) := fun x => by
      simp [shape, hi]
    have hdu : ∀ x, dual a b N true j x =
        (P N (j - 1) (coord a b N x) - P N j (coord a b N x)) / meshH a b N :=
      fun x => dual_true_eq hab hN hj'.1 hj'.2 x
    simp_rw [hsh, hdu]
    have e : ∀ t : ℝ, Set.indicator (Set.Ico ((i:ℝ) - 1) i) (fun _ => (1:ℝ)) t *
        ((P N (j - 1) t - P N j t) / meshH a b N) =
        Set.indicator (Set.Ico ((i:ℝ) - 1) i) (fun t => (P N (j - 1) t - P N j t) / meshH a b N) t := by
      intro t
      by_cases ht : t ∈ Set.Ico ((i:ℝ) - 1) i
      · simp [Set.indicator_of_mem ht]
      · simp [Set.indicator_of_notMem ht]
    rw [integral_comp_coord hab hN
      (fun t => Set.indicator (Set.Ico ((i:ℝ) - 1) i) (fun _ => (1:ℝ)) t *
        ((P N (j - 1) t - P N j t) / meshH a b N))]
    simp_rw [e]
    rw [integral_indicator measurableSet_Ico, integral_div]
    have hI : ∀ m, IntegrableOn (P N m) (Set.Ico ((i:ℝ) - 1) i) := fun m =>
      ((continuous_P m).integrableOn_Icc).mono_set Set.Ico_subset_Icc_self
    rw [integral_sub (hI _) (hI _), integral_Ico_P (by omega) hi'.1 hi'.2,
      integral_Ico_P hj'.2 hi'.1 hi'.2]
    have hV : Valid N true i := hi
    rw [mul_div_cancel₀ _ hh.ne']
    have : (if Valid N true i ∧ i = j then (1:ℝ) else 0) = if i = j then 1 else 0 := by
      simp [hV]
    rw [this]
    split_ifs <;> first | (exfalso; omega) | norm_num

end Ref

end FEEC
