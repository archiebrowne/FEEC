/-
Schur sums for the one-dimensional shape and dual functions.
-/
import FEEC.Tensor.Ref1D

namespace FEEC

open MeasureTheory

namespace Ref

variable {a b : ℝ} {N : ℕ}

lemma coord_def (x : ℝ) : coord a b N x = (x - a) / meshH a b N := rfl

lemma coord_lt_coord (hh : 0 < meshH a b N) {x y : ℝ} :
    coord a b N x < coord a b N y ↔ x < y := by
  unfold coord
  rw [div_lt_div_iff_of_pos_right hh, sub_lt_sub_iff_right]

lemma rho_hcs : HasCompactSupport rho := by
  refine IsCompact.of_isClosed_subset (isCompact_Icc (a := (0:ℝ)) (b := 1)) (isClosed_tsupport _) ?_
  exact rho_tsupport.trans Set.Ioo_subset_Icc_self

lemma rho_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ y, |rho y| ≤ C := by
  obtain ⟨C, hC⟩ := rho_contDiff.continuous.bounded_above_of_compact_support rho_hcs
  exact ⟨C, (abs_nonneg _).trans (by simpa using hC 0), fun y => by simpa using hC y⟩

lemma integrable_abs_rho : Integrable (fun t => |rho t|) :=
  (rho_contDiff.continuous.integrable_of_hasCompactSupport rho_hcs).abs

lemma schur_integrable_nodeDual (hab : a < b) (hN : 0 < N) (k : ℕ) : Integrable (nodeDual a b N k) :=
  (contDiff_nodeDual hab hN k).continuous.integrable_of_hasCompactSupport
    (IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _)
      ((tsupport_nodeDual_subset hab hN k).trans Set.Ioo_subset_Icc_self))

lemma abs_nodeDual_le (hab : a < b) (hN : 0 < N) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ y, |rho y| ≤ C) (k : ℕ) (y : ℝ) : |nodeDual a b N k y| ≤ C / meshH a b N := by
  have hh := meshH_pos hab hN
  unfold nodeDual
  split_ifs
  · rw [abs_div, abs_of_pos hh]; exact div_le_div_of_nonneg_right (hC _) hh.le
  · rw [abs_div, abs_of_pos hh]; exact div_le_div_of_nonneg_right (hC _) hh.le
  · simpa using div_nonneg hC0 hh.le

lemma nodeDual_ne_zero {k : ℕ} {y : ℝ} (hy : nodeDual a b N k y ≠ 0) :
    (k < N ∧ (k : ℝ) < coord a b N y ∧ coord a b N y < k + 1) ∨
    (k = N ∧ (N : ℝ) - 1 < coord a b N y ∧ coord a b N y < N) := by
  unfold nodeDual at hy
  split_ifs at hy with h1 h2
  · left
    have hr : rho (coord a b N y - k) ≠ 0 := fun h => hy (by simp [h])
    obtain ⟨l, u⟩ := rho_tsupport (subset_tsupport _ hr)
    exact ⟨h1, by linarith, by linarith⟩
  · right
    have hr : rho ((k : ℝ) - coord a b N y) ≠ 0 := fun h => hy (by simp [h])
    obtain ⟨l, u⟩ := rho_tsupport (subset_tsupport _ hr)
    have : (k : ℝ) = N := by exact_mod_cast h2
    exact ⟨h2, by linarith, by linarith⟩
  · exact absurd (by simp) hy

lemma integral_abs_nodeDual (hab : a < b) (hN : 0 < N) {k : ℕ} (hk : k ≤ N) :
    ∫ x, |nodeDual a b N k x| = ∫ t, |rho t| := by
  have hh := meshH_pos hab hN
  have key : ∀ (g : ℝ → ℝ) (c : ℝ),
      ∫ x, g ((x - c) / meshH a b N) = meshH a b N * ∫ t, g t := by
    intro g c
    have := integral_sub_right_eq_self (μ := (volume : Measure ℝ)) (fun u => g (u / meshH a b N)) c
    rw [this, MeasureTheory.Measure.integral_comp_div, abs_of_pos hh, smul_eq_mul]
  rcases hk.lt_or_eq with hk | hk
  · have e : ∀ x, |nodeDual a b N k x| =
        (fun u => |rho u|) ((x - (a + k * meshH a b N)) / meshH a b N) / meshH a b N := by
      intro x
      have : coord a b N x - k = (x - (a + k * meshH a b N)) / meshH a b N := by
        unfold coord; field_simp; ring
      simp only [nodeDual, if_pos hk, abs_div, abs_of_pos hh, this]
    simp_rw [e]
    have k1 := key (fun u => |rho u|) (a + k * meshH a b N)
    rw [integral_div, k1]
    field_simp
  · subst hk
    have e : ∀ x, |nodeDual a b k k x| =
        (fun u => |rho (-u)|) ((x - (a + k * meshH a b k)) / meshH a b k) / meshH a b k := by
      intro x
      have : (k : ℝ) - coord a b k x = -((x - (a + k * meshH a b k)) / meshH a b k) := by
        unfold coord; field_simp; ring
      simp only [nodeDual, lt_irrefl, if_false, if_true, abs_div, abs_of_pos hh, this]
    simp_rw [e]
    have k1 := key (fun u => |rho (-u)|) (a + k * meshH a b k)
    rw [integral_div, k1, integral_neg_eq_self (fun t => |rho t|)]
    field_simp

lemma integral_abs_nodeDual_le (hab : a < b) (hN : 0 < N) (k : ℕ) :
    ∫ x, |nodeDual a b N k x| ≤ ∫ t, |rho t| := by
  by_cases hk : k ≤ N
  · exact (integral_abs_nodeDual hab hN hk).le
  · have : ∀ x, nodeDual a b N k x = 0 := by
      intro x; unfold nodeDual
      rw [if_neg (by omega), if_neg (by omega)]
    simp [this]; exact integral_nonneg (fun t => abs_nonneg _)

/-- Cumulative integral of a node dual. -/
noncomputable def Phi (a b : ℝ) (N : ℕ) (k : ℕ) (y : ℝ) : ℝ := ∫ z in Set.Iic y, nodeDual a b N k z

lemma Phi_zero {k : ℕ} {y : ℝ} (h : ∀ z, nodeDual a b N k z ≠ 0 → y < z) : Phi a b N k y = 0 := by
  unfold Phi
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro z hz
  by_contra hne
  exact absurd (h z hne) (not_lt.2 hz)

lemma Phi_one (hab : a < b) (hN : 0 < N) {k : ℕ} (hk : k ≤ N) {y : ℝ}
    (h : ∀ z, nodeDual a b N k z ≠ 0 → z ≤ y) : Phi a b N k y = 1 := by
  unfold Phi
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero, integral_nodeDual hab hN hk]
  intro z hz
  by_contra hne
  exact hz (h z hne)

lemma schur_dual_true_eq (hab : a < b) (hN : 0 < N) {i : ℕ} (hi : i < N) (y : ℝ) :
    dual a b N true (i + 1) y = (Phi a b N i y - Phi a b N (i + 1) y) / meshH a b N := by
  have hv : Valid N true (i + 1) := by simp [Valid]; omega
  have h1 := (schur_integrable_nodeDual hab hN i).integrableOn (s := Set.Iic y)
  have h2 := (schur_integrable_nodeDual hab hN (i + 1)).integrableOn (s := Set.Iic y)
  simp only [dual, hv, if_true, cumul, Nat.add_sub_cancel, Phi]
  rw [integral_div, integral_sub h1 h2]


lemma lt_of_coord_lt (hh : 0 < meshH a b N) {x y : ℝ} (h : coord a b N x < coord a b N y) :
    x < y := (coord_lt_coord hh).1 h

lemma abs_Phi_le (hab : a < b) (hN : 0 < N) (k : ℕ) (y : ℝ) :
    |Phi a b N k y| ≤ ∫ t, |rho t| := by
  have hi := (schur_integrable_nodeDual hab hN k).norm
  calc |Phi a b N k y| = ‖∫ z in Set.Iic y, nodeDual a b N k z‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ z in Set.Iic y, ‖nodeDual a b N k z‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z, ‖nodeDual a b N k z‖ :=
        setIntegral_le_integral hi (Filter.Eventually.of_forall (fun z => norm_nonneg _))
    _ ≤ ∫ t, |rho t| := by
        simpa only [Real.norm_eq_abs] using integral_abs_nodeDual_le hab hN k

lemma dual_true_supp (hab : a < b) (hN : 0 < N) {j : ℕ} {y : ℝ}
    (hy : dual a b N true j y ≠ 0) :
    1 ≤ j ∧ j ≤ N ∧ (j : ℝ) - 1 < coord a b N y ∧ coord a b N y < j + 1 := by
  have hv : Valid N true j := by
    by_contra hv; apply hy; simp [dual, hv]
  have hv' : 1 ≤ j ∧ j ≤ N := by simpa [Valid] using hv
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hi : i < N := by omega
  rw [schur_dual_true_eq hab hN hi] at hy
  have hh := meshH_pos hab hN
  have hiN : ((i : ℝ) + 1) ≤ N := by exact_mod_cast hi
  refine ⟨hv'.1, hv'.2, ?_, ?_⟩
  · by_contra hc
    push_neg at hc
    apply hy
    have hc' : coord a b N y ≤ i := by push_cast at hc; linarith
    have z0 : Phi a b N i y = 0 := by
      apply Phi_zero
      intro z hz
      apply lt_of_coord_lt hh
      rcases nodeDual_ne_zero hz with ⟨_, h2, _⟩ | ⟨h1, _⟩
      · linarith
      · omega
    have z1 : Phi a b N (i + 1) y = 0 := by
      apply Phi_zero
      intro z hz
      apply lt_of_coord_lt hh
      rcases nodeDual_ne_zero hz with ⟨_, h2, _⟩ | ⟨h1, h2, _⟩
      · push_cast at h2; linarith
      · have : ((i + 1 : ℕ) : ℝ) = N := by exact_mod_cast h1
        push_cast at this; linarith
    rw [z0, z1]; simp
  · by_contra hc
    push_neg at hc
    apply hy
    push_cast at hc
    have z0 : Phi a b N i y = 1 := by
      apply Phi_one hab hN (by omega)
      intro z hz
      apply le_of_lt; apply lt_of_coord_lt hh
      rcases nodeDual_ne_zero hz with ⟨_, _, h3⟩ | ⟨h1, _⟩
      · linarith
      · omega
    have z1 : Phi a b N (i + 1) y = 1 := by
      apply Phi_one hab hN (by omega)
      intro z hz
      apply le_of_lt; apply lt_of_coord_lt hh
      rcases nodeDual_ne_zero hz with ⟨_, _, h3⟩ | ⟨h1, _, h3⟩
      · push_cast at h3; linarith
      · have : ((i + 1 : ℕ) : ℝ) = N := by exact_mod_cast h1
        push_cast at this; linarith
    rw [z0, z1]; simp

lemma abs_dual_true_le (hab : a < b) (hN : 0 < N) (j : ℕ) (y : ℝ) :
    |dual a b N true j y| ≤ 2 * (∫ t, |rho t|) / meshH a b N := by
  have hh := meshH_pos hab hN
  have hc0 : 0 ≤ ∫ t, |rho t| := integral_nonneg (fun t => abs_nonneg _)
  by_cases hv : Valid N true j
  · have hv' : 1 ≤ j ∧ j ≤ N := by simpa [Valid] using hv
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [schur_dual_true_eq hab hN (by omega), abs_div, abs_of_pos hh]
    apply div_le_div_of_nonneg_right _ hh.le
    have := abs_Phi_le hab hN i y
    have := abs_Phi_le hab hN (i + 1) y
    have := abs_sub (Phi a b N i y) (Phi a b N (i + 1) y)
    linarith
  · simp [dual, hv]; positivity

lemma dual_false_eq {j : ℕ} (hj : j ≤ N) (y : ℝ) :
    dual a b N false j y = nodeDual a b N j y := by
  simp [dual, Valid, hj]

lemma dual_false_ne_zero {j : ℕ} {y : ℝ} (h : dual a b N false j y ≠ 0) :
    j ≤ N ∧ nodeDual a b N j y ≠ 0 := by
  by_cases hj : j ≤ N
  · exact ⟨hj, by rwa [dual_false_eq hj] at h⟩
  · exact absurd (by simp [dual, Valid, hj]) h

lemma abs_dual_false_le (hab : a < b) (hN : 0 < N) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ y, |rho y| ≤ C) (j : ℕ) (y : ℝ) : |dual a b N false j y| ≤ C / meshH a b N := by
  have hh := meshH_pos hab hN
  by_cases hj : j ≤ N
  · rw [dual_false_eq hj]; exact abs_nodeDual_le hab hN hC0 hC j y
  · simp [dual, Valid, hj]; positivity

lemma setIntegral_abs_le (hab : a < b) (hN : 0 < N) (f : ℝ → ℝ) (B lo hi : ℝ) (hB : 0 ≤ B)
    (hlh : lo ≤ hi) (hbd : ∀ y, |f y| ≤ B)
    (hs : ∀ y, f y ≠ 0 → lo ≤ coord a b N y ∧ coord a b N y ≤ hi) :
    ∫ y in Set.Ioo a b, |f y| ≤ B * (meshH a b N * (hi - lo)) := by
  have hh := meshH_pos hab hN
  have hpt : ∀ y, |f y| ≤
      (Set.Icc (a + meshH a b N * lo) (a + meshH a b N * hi)).indicator (fun _ => B) y := by
    intro y
    by_cases hy : f y = 0
    · rw [hy]; simpa using Set.indicator_nonneg (fun _ _ => hB) y
    · obtain ⟨h1, h2⟩ := hs y hy
      rw [coord_def, le_div_iff₀ hh] at h1
      rw [coord_def, div_le_iff₀ hh] at h2
      have hmem : y ∈ Set.Icc (a + meshH a b N * lo) (a + meshH a b N * hi) :=
        ⟨by linarith, by linarith⟩
      rw [Set.indicator_of_mem hmem]; exact hbd y
  have hint : Integrable ((Set.Icc (a + meshH a b N * lo) (a + meshH a b N * hi)).indicator
      (fun _ => B)) :=
    (integrableOn_const (isCompact_Icc.measure_lt_top.ne)).integrable_indicator measurableSet_Icc
  calc ∫ y in Set.Ioo a b, |f y|
      ≤ ∫ y in Set.Ioo a b, (Set.Icc (a + meshH a b N * lo)
          (a + meshH a b N * hi)).indicator (fun _ => B) y := by
        apply integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall (fun y => abs_nonneg _)
        · exact hint.integrableOn
        · exact Filter.Eventually.of_forall hpt
    _ ≤ ∫ y, (Set.Icc (a + meshH a b N * lo)
          (a + meshH a b N * hi)).indicator (fun _ => B) y :=
        setIntegral_le_integral hint
          (Filter.Eventually.of_forall (fun y => Set.indicator_nonneg (fun _ _ => hB) y))
    _ = B * (meshH a b N * (hi - lo)) := by
        rw [integral_indicator_const _ measurableSet_Icc, measureReal_def, Real.volume_Icc,
          ENNReal.toReal_ofReal (by nlinarith), smul_eq_mul, mul_comm]
        congr 1; ring

lemma hat_ne_zero {u : ℝ} (h : hat u ≠ 0) : |u| < 1 := by
  by_contra hc
  push_neg at hc
  exact h (by unfold hat; exact max_eq_left (by linarith))

lemma shape_false_supp {j : ℕ} {x : ℝ} (h : shape a b N false j x ≠ 0) :
    (j : ℝ) - 1 < coord a b N x ∧ coord a b N x < j + 1 := by
  have hv : Valid N false j := by
    by_contra hv; exact h (by simp [shape, hv])
  have h' : hat (coord a b N x - j) ≠ 0 := by
    simpa [shape, hv] using h
  have := abs_lt.1 (hat_ne_zero h')
  constructor <;> linarith [this.1, this.2]

lemma shape_true_supp {j : ℕ} {x : ℝ} (h : shape a b N true j x ≠ 0) :
    1 ≤ j ∧ (j : ℝ) - 1 ≤ coord a b N x ∧ coord a b N x < j := by
  have hv : Valid N true j := by
    by_contra hv; exact h (by simp [shape, hv])
  have hv' : 1 ≤ j ∧ j ≤ N := by simpa [Valid] using hv
  have h' : Set.indicator (Set.Ico ((j : ℝ) - 1) j) (fun _ => (1 : ℝ)) (coord a b N x) ≠ 0 := by
    simpa [shape, hv] using h
  rw [Ne, Set.indicator_apply_eq_zero] at h'
  push_neg at h'
  obtain ⟨⟨l, u⟩, _⟩ := h'
  exact ⟨hv'.1, l, u⟩

lemma int_dual_false_le (hab : a < b) (hN : 0 < N) (j : ℕ) :
    ∫ y in Set.Ioo a b, |dual a b N false j y| ≤ ∫ t, |rho t| := by
  by_cases hj : j ≤ N
  · simp_rw [dual_false_eq hj]
    calc _ ≤ ∫ y, |nodeDual a b N j y| :=
          setIntegral_le_integral (schur_integrable_nodeDual hab hN j).abs
            (Filter.Eventually.of_forall (fun y => abs_nonneg _))
      _ = _ := integral_abs_nodeDual hab hN hj
  · simp [dual, Valid, hj]; exact integral_nonneg (fun t => abs_nonneg _)

lemma int_dual_true_le (hab : a < b) (hN : 0 < N) (j : ℕ) :
    ∫ y in Set.Ioo a b, |dual a b N true j y| ≤ 4 * ∫ t, |rho t| := by
  have hh := meshH_pos hab hN
  have hc0 : 0 ≤ ∫ t, |rho t| := integral_nonneg (fun t => abs_nonneg _)
  have := setIntegral_abs_le hab hN (dual a b N true j) (2 * (∫ t, |rho t|) / meshH a b N)
    ((j : ℝ) - 1) (j + 1) (by positivity) (by linarith) (abs_dual_true_le hab hN j)
    (fun y hy => by
      obtain ⟨_, _, h1, h2⟩ := dual_true_supp hab hN hy
      exact ⟨h1.le, h2.le⟩)
  refine this.trans (le_of_eq ?_)
  field_simp
  ring

lemma int_shape_false_le (hab : a < b) (hN : 0 < N) (j : ℕ) :
    ∫ y in Set.Ioo a b, |shape a b N false j y| ≤ 2 * meshH a b N := by
  have := setIntegral_abs_le hab hN (shape a b N false j) 1 ((j : ℝ) - 1) (j + 1) zero_le_one
    (by linarith) (abs_shape_le_one false j)
    (fun y hy => by
      obtain ⟨h1, h2⟩ := shape_false_supp hy
      exact ⟨h1.le, h2.le⟩)
  refine this.trans (le_of_eq ?_)
  ring

lemma int_shape_true_le (hab : a < b) (hN : 0 < N) (j : ℕ) :
    ∫ y in Set.Ioo a b, |shape a b N true j y| ≤ meshH a b N := by
  have := setIntegral_abs_le hab hN (shape a b N true j) 1 ((j : ℝ) - 1) j zero_le_one
    (by linarith) (abs_shape_le_one true j)
    (fun y hy => by
      obtain ⟨_, h1, h2⟩ := shape_true_supp hy
      exact ⟨h1, h2.le⟩)
  refine this.trans (le_of_eq ?_)
  ring

lemma sum_le_card (n : ℕ) (g : ℕ → ℝ) (S : Finset ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hg : ∀ j, g j ≤ B) (hg0 : ∀ j, j ∉ S → g j ≤ 0) :
    ∑ j ∈ Finset.range n, g j ≤ S.card * B := by
  calc ∑ j ∈ Finset.range n, g j ≤ ∑ j ∈ Finset.range n, (if j ∈ S then B else 0) := by
        apply Finset.sum_le_sum
        intro j _
        by_cases h : j ∈ S
        · simp [h, hg j]
        · simp only [h, if_false]; exact hg0 j h
    _ = ∑ j ∈ Finset.range n ∩ S, B := by rw [Finset.sum_ite_mem]
    _ ≤ S.card * B := by
        rw [Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast Finset.card_le_card Finset.inter_subset_right) hB

lemma idx_two {j : ℕ} {t : ℝ} (h1 : (j : ℝ) - 1 < t) (h2 : t < j + 1) :
    j ∈ ({⌊t⌋₊, ⌊t⌋₊ + 1} : Finset ℕ) := by
  have h3 : t < ⌊t⌋₊ + 1 := Nat.lt_floor_add_one t
  have hj1 : j < ⌊t⌋₊ + 2 := by
    have : (j : ℝ) < ⌊t⌋₊ + 2 := by linarith
    exact_mod_cast this
  have hj2 : ⌊t⌋₊ ≤ j := by
    by_cases ht : t < 0
    · rw [Nat.floor_of_nonpos ht.le]; exact Nat.zero_le _
    · have := Nat.floor_le (not_lt.1 ht)
      have : (⌊t⌋₊ : ℝ) < j + 1 := by linarith
      have : ⌊t⌋₊ < j + 1 := by exact_mod_cast this
      omega
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

lemma idx_one {j : ℕ} {t : ℝ} (hj : 1 ≤ j) (h1 : (j : ℝ) - 1 ≤ t) (h2 : t < j) :
    j ∈ ({⌊t⌋₊ + 1} : Finset ℕ) := by
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have h3 : t < ⌊t⌋₊ + 1 := Nat.lt_floor_add_one t
  have h4 := Nat.floor_le (show 0 ≤ t by linarith)
  have a1 : j < ⌊t⌋₊ + 2 := by
    have : (j : ℝ) < ⌊t⌋₊ + 2 := by linarith
    exact_mod_cast this
  have a2 : ⌊t⌋₊ < j := by
    have : (⌊t⌋₊ : ℝ) < j := by linarith
    exact_mod_cast this
  simp only [Finset.mem_singleton]
  omega


/-- The Schur sums of the kernel `∑ⱼ shapeⱼ(x) dualⱼ(y)` are bounded by an absolute constant,
independent of the interval and of the number of cells. -/
theorem exists_schur_const : ∃ K : ℝ, 0 ≤ K ∧ ∀ (a b : ℝ) (N : ℕ), a < b → 0 < N →
    ∀ s : Bool,
      (∀ x, ∑ j ∈ Finset.range (N + 2),
        |shape a b N s j x| * ∫ y in Set.Ioo a b, |dual a b N s j y| ≤ K) ∧
      (∀ y, ∑ j ∈ Finset.range (N + 2),
        (∫ x in Set.Ioo a b, |shape a b N s j x|) * |dual a b N s j y| ≤ K) := by
  obtain ⟨C, hC0, hC⟩ := rho_bound
  have hc0 : 0 ≤ ∫ t, |rho t| := integral_nonneg (fun t => abs_nonneg _)
  set c₁ : ℝ := ∫ t, |rho t| with hc
  refine ⟨4 * c₁ + 4 * C, by positivity, ?_⟩
  intro a b N hab hN s
  have hh := meshH_pos hab hN
  cases s
  · refine ⟨fun x => ?_, fun y => ?_⟩
    · have key := sum_le_card (N + 2)
        (fun j => |shape a b N false j x| * ∫ y in Set.Ioo a b, |dual a b N false j y|)
        {⌊coord a b N x⌋₊, ⌊coord a b N x⌋₊ + 1} c₁ hc0 (fun j => ?_) (fun j hj => ?_)
      · calc _ ≤ _ := key
          _ ≤ 2 * c₁ := mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_two) hc0
          _ ≤ _ := by linarith
      · show |shape a b N false j x| * ∫ y in Set.Ioo a b, |dual a b N false j y| ≤ c₁
        calc _ ≤ 1 * c₁ := mul_le_mul (abs_shape_le_one false j x) (int_dual_false_le hab hN j)
              (integral_nonneg (fun _ => abs_nonneg _)) zero_le_one
          _ = c₁ := one_mul _
      · show |shape a b N false j x| * ∫ y in Set.Ioo a b, |dual a b N false j y| ≤ 0
        by_cases h0 : shape a b N false j x = 0
        · simp [h0]
        · exact absurd (idx_two (shape_false_supp h0).1 (shape_false_supp h0).2) hj
    · have key := sum_le_card (N + 2)
        (fun j => (∫ x in Set.Ioo a b, |shape a b N false j x|) * |dual a b N false j y|)
        {⌊coord a b N y⌋₊, N} (2 * C) (by positivity) (fun j => ?_) (fun j hj => ?_)
      · calc _ ≤ _ := key
          _ ≤ 2 * (2 * C) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_two) (by positivity)
          _ ≤ _ := by linarith
      · show (∫ x in Set.Ioo a b, |shape a b N false j x|) * |dual a b N false j y| ≤ 2 * C
        calc _ ≤ (2 * meshH a b N) * (C / meshH a b N) :=
              mul_le_mul (int_shape_false_le hab hN j) (abs_dual_false_le hab hN hC0 hC j y)
                (abs_nonneg _) (by positivity)
          _ = 2 * C := by field_simp
      · show (∫ x in Set.Ioo a b, |shape a b N false j x|) * |dual a b N false j y| ≤ 0
        by_cases h0 : dual a b N false j y = 0
        · simp [h0]
        · exfalso
          apply hj
          obtain ⟨hjN, hne⟩ := dual_false_ne_zero h0
          rcases nodeDual_ne_zero hne with ⟨_, h2, h3⟩ | ⟨h1, _⟩
          · have := (Nat.floor_eq_iff (by linarith : 0 ≤ coord a b N y)).2 ⟨h2.le, h3⟩
            simp [this]
          · simp [h1]
  · refine ⟨fun x => ?_, fun y => ?_⟩
    · have key := sum_le_card (N + 2)
        (fun j => |shape a b N true j x| * ∫ y in Set.Ioo a b, |dual a b N true j y|)
        {⌊coord a b N x⌋₊ + 1} (4 * c₁) (by positivity) (fun j => ?_) (fun j hj => ?_)
      · calc _ ≤ _ := key
          _ ≤ 1 * (4 * c₁) := by simp
          _ ≤ _ := by linarith
      · show |shape a b N true j x| * ∫ y in Set.Ioo a b, |dual a b N true j y| ≤ 4 * c₁
        calc _ ≤ 1 * (4 * c₁) := mul_le_mul (abs_shape_le_one true j x) (int_dual_true_le hab hN j)
              (integral_nonneg (fun _ => abs_nonneg _)) zero_le_one
          _ = 4 * c₁ := one_mul _
      · show |shape a b N true j x| * ∫ y in Set.Ioo a b, |dual a b N true j y| ≤ 0
        by_cases h0 : shape a b N true j x = 0
        · simp [h0]
        · obtain ⟨h1, h2, h3⟩ := shape_true_supp h0
          exact absurd (idx_one h1 h2 h3) hj
    · have key := sum_le_card (N + 2)
        (fun j => (∫ x in Set.Ioo a b, |shape a b N true j x|) * |dual a b N true j y|)
        {⌊coord a b N y⌋₊, ⌊coord a b N y⌋₊ + 1} (2 * c₁) (by positivity) (fun j => ?_)
        (fun j hj => ?_)
      · calc _ ≤ _ := key
          _ ≤ 2 * (2 * c₁) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_two) (by positivity)
          _ ≤ _ := by linarith
      · show (∫ x in Set.Ioo a b, |shape a b N true j x|) * |dual a b N true j y| ≤ 2 * c₁
        calc _ ≤ meshH a b N * (2 * c₁ / meshH a b N) :=
              mul_le_mul (int_shape_true_le hab hN j) (abs_dual_true_le hab hN j y)
                (abs_nonneg _) hh.le
          _ = 2 * c₁ := by field_simp
      · show (∫ x in Set.Ioo a b, |shape a b N true j x|) * |dual a b N true j y| ≤ 0
        by_cases h0 : dual a b N true j y = 0
        · simp [h0]
        · obtain ⟨_, _, h1, h2⟩ := dual_true_supp hab hN h0
          exact absurd (idx_two h1 h2) hj

end Ref

end FEEC
