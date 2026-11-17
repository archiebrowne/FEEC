/-
Cosine and sine systems on an interval.
-/
import Mathlib

/-!
# Cosine and sine systems on an interval

On `(a, b)` with `ℓ = b - a`, `trigC a b m t = cos (π m (t - a) / ℓ)` and
`trigS a b m t = sin (π m (t - a) / ℓ)`: orthogonality, derivatives, product-to-sum formulas.
-/

namespace FEEC

open MeasureTheory Real

/-- `cos (π m (t - a) / (b - a))`. -/
noncomputable def trigC (a b : ℝ) (m : ℕ) (t : ℝ) : ℝ := cos (π * m * (t - a) / (b - a))

/-- `sin (π m (t - a) / (b - a))`. -/
noncomputable def trigS (a b : ℝ) (m : ℕ) (t : ℝ) : ℝ := sin (π * m * (t - a) / (b - a))

/-- The frequency `π m / (b - a)`. -/
noncomputable def freq (a b : ℝ) (m : ℕ) : ℝ := π * m / (b - a)

/-- The squared `L²` norm of `trigC a b m` on `(a, b)`. -/
noncomputable def trigNormSq (a b : ℝ) (m : ℕ) : ℝ := if m = 0 then b - a else (b - a) / 2

variable {a b : ℝ}

theorem hasDerivAt_arg (m : ℕ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => π * m * (t - a) / (b - a)) (freq a b m) t := by
  have := (((hasDerivAt_id t).sub_const a).const_mul (π * m)).div_const (b - a)
  refine HasDerivAt.congr_deriv this ?_
  unfold freq; ring

theorem contDiff_trigC (m : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (trigC a b m) := by
  unfold trigC; fun_prop

theorem contDiff_trigS (m : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (trigS a b m) := by
  unfold trigS; fun_prop

theorem hasDerivAt_trigC (m : ℕ) (t : ℝ) :
    HasDerivAt (trigC a b m) (-(freq a b m * trigS a b m t)) t := by
  have := (Real.hasDerivAt_cos (π * m * (t - a) / (b - a))).comp t (hasDerivAt_arg (a := a) (b := b) m t)
  unfold trigC trigS
  exact HasDerivAt.congr_deriv this (by ring)

theorem hasDerivAt_trigS (m : ℕ) (t : ℝ) :
    HasDerivAt (trigS a b m) (freq a b m * trigC a b m t) t := by
  have := (Real.hasDerivAt_sin (π * m * (t - a) / (b - a))).comp t (hasDerivAt_arg (a := a) (b := b) m t)
  unfold trigC trigS
  exact HasDerivAt.congr_deriv this (by ring)

theorem abs_trigC_le (m : ℕ) (t : ℝ) : |trigC a b m t| ≤ 1 := abs_cos_le_one _

theorem abs_trigS_le (m : ℕ) (t : ℝ) : |trigS a b m t| ≤ 1 := abs_sin_le_one _

theorem trigS_zero : trigS a b 0 = 0 := by
  funext t; simp [trigS]

theorem trigC_zero : trigC a b 0 = 1 := by
  funext t; simp [trigC]

theorem trigC_mul_trigC (m m' : ℕ) (t : ℝ) :
    trigC a b m t * trigC a b m' t =
      (trigC a b (m + m') t + trigC a b (Nat.dist m m') t) / 2 := by
  unfold trigC
  have h1 : π * ((m + m' : ℕ) : ℝ) * (t - a) / (b - a)
      = π * m * (t - a) / (b - a) + π * m' * (t - a) / (b - a) := by push_cast; ring
  rw [h1]
  rcases le_total m m' with h | h
  · rw [Nat.dist_eq_sub_of_le h]
    have h2 : π * ((m' - m : ℕ) : ℝ) * (t - a) / (b - a)
      = π * m' * (t - a) / (b - a) - π * m * (t - a) / (b - a) := by
      rw [Nat.cast_sub h]; ring
    rw [h2, cos_add, cos_sub]; ring
  · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le h]
    have h2 : π * ((m - m' : ℕ) : ℝ) * (t - a) / (b - a)
      = π * m * (t - a) / (b - a) - π * m' * (t - a) / (b - a) := by
      rw [Nat.cast_sub h]; ring
    rw [h2, cos_add, cos_sub]; ring

theorem trigS_mul_trigS (m m' : ℕ) (t : ℝ) :
    trigS a b m t * trigS a b m' t =
      (trigC a b (Nat.dist m m') t - trigC a b (m + m') t) / 2 := by
  unfold trigC trigS
  have h1 : π * ((m + m' : ℕ) : ℝ) * (t - a) / (b - a)
      = π * m * (t - a) / (b - a) + π * m' * (t - a) / (b - a) := by push_cast; ring
  rw [h1]
  rcases le_total m m' with h | h
  · rw [Nat.dist_eq_sub_of_le h]
    have h2 : π * ((m' - m : ℕ) : ℝ) * (t - a) / (b - a)
      = π * m' * (t - a) / (b - a) - π * m * (t - a) / (b - a) := by
      rw [Nat.cast_sub h]; ring
    rw [h2, cos_add, cos_sub]; ring
  · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le h]
    have h2 : π * ((m - m' : ℕ) : ℝ) * (t - a) / (b - a)
      = π * m * (t - a) / (b - a) - π * m' * (t - a) / (b - a) := by
      rw [Nat.cast_sub h]; ring
    rw [h2, cos_add, cos_sub]; ring

theorem integral_trigC (hab : a < b) (k : ℕ) :
    ∫ t in Set.Ioo a b, trigC a b k t = if k = 0 then b - a else 0 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab.le]
  by_cases hk : k = 0
  · subst hk
    simp [trigC_zero]
  · simp only [hk, if_false]
    have hf : freq a b k ≠ 0 := by
      unfold freq
      have : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
      have := sub_pos.2 hab
      positivity
    have hd : ∀ x ∈ Set.uIcc a b,
        HasDerivAt (fun t => trigS a b k t / freq a b k) (trigC a b k x) x := by
      intro x _
      convert (hasDerivAt_trigS (a := a) (b := b) k x).div_const (freq a b k) using 1
      field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((continuous_def.2 fun _ h => by
        have := (contDiff_trigC (a := a) (b := b) k).continuous
        exact this.isOpen_preimage _ h).intervalIntegrable _ _)]
    have hba : b - a ≠ 0 := (sub_pos.2 hab).ne'
    have e1 : trigS a b k b = 0 := by
      unfold trigS
      have : π * k * (b - a) / (b - a) = k * π := by field_simp
      rw [this, sin_nat_mul_pi]
    have e2 : trigS a b k a = 0 := by simp [trigS]
    simp [e1, e2]

theorem integrableOn_trigC (m : ℕ) : IntegrableOn (trigC a b m) (Set.Ioo a b) :=
  (contDiff_trigC (a := a) (b := b) m).continuous.integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self

theorem integral_trigC_mul_trigC (hab : a < b) (m m' : ℕ) :
    ∫ t in Set.Ioo a b, trigC a b m t * trigC a b m' t =
      if m = m' then trigNormSq a b m else 0 := by
  simp_rw [trigC_mul_trigC]
  rw [integral_div, integral_add (integrableOn_trigC _) (integrableOn_trigC _),
    integral_trigC hab, integral_trigC hab]
  have hba := sub_pos.2 hab
  unfold trigNormSq
  by_cases h : m = m'
  · subst h
    by_cases h0 : m = 0 <;> simp [h0]
  · have h1 : m + m' ≠ 0 := by omega
    have h2 : Nat.dist m m' ≠ 0 := by
      intro h0; exact h (Nat.eq_of_dist_eq_zero h0)
    simp [h, h2]
    intro h0 h0'
    omega

theorem integral_trigS_mul_trigS (hab : a < b) (m m' : ℕ) :
    ∫ t in Set.Ioo a b, trigS a b m t * trigS a b m' t =
      if m = m' ∧ m ≠ 0 then trigNormSq a b m else 0 := by
  simp_rw [trigS_mul_trigS]
  rw [integral_div, integral_sub (integrableOn_trigC _) (integrableOn_trigC _),
    integral_trigC hab, integral_trigC hab]
  have hba := sub_pos.2 hab
  unfold trigNormSq
  by_cases h : m = m'
  · subst h
    by_cases h0 : m = 0 <;> simp [h0]
  · have h1 : m + m' ≠ 0 := by omega
    have h2 : Nat.dist m m' ≠ 0 := by
      intro h0; exact h (Nat.eq_of_dist_eq_zero h0)
    simp [h, h2]
    intro h0 h0'
    omega

theorem trigS_one_mul_trigC (j : ℕ) (t : ℝ) :
    trigS a b 1 t * trigC a b (j + 1) t = (trigS a b (j + 2) t - trigS a b j t) / 2 := by
  unfold trigS trigC
  have e1 : π * ((j + 2 : ℕ) : ℝ) * (t - a) / (b - a)
      = π * ((j + 1 : ℕ) : ℝ) * (t - a) / (b - a) + π * ((1 : ℕ) : ℝ) * (t - a) / (b - a) := by
    push_cast; ring
  have e2 : π * (j : ℝ) * (t - a) / (b - a)
      = π * ((j + 1 : ℕ) : ℝ) * (t - a) / (b - a) - π * ((1 : ℕ) : ℝ) * (t - a) / (b - a) := by
    push_cast; ring
  rw [e1, e2, sin_add, sin_sub]; ring

theorem trigS_one_pos (hab : a < b) {t : ℝ} (ht : t ∈ Set.Ioo a b) : 0 < trigS a b 1 t := by
  unfold trigS
  apply sin_pos_of_pos_of_lt_pi
  · have := sub_pos.2 hab
    have := sub_pos.2 ht.1
    simp only [Nat.cast_one]; positivity
  · have := sub_pos.2 hab
    simp only [Nat.cast_one]
    rw [mul_one, div_lt_iff₀ this]
    nlinarith [pi_pos, ht.2]

theorem trigC_one_injOn (hab : a < b) : Set.InjOn (trigC a b 1) (Set.Icc a b) := by
  intro s hs t ht h
  have hba := sub_pos.2 hab
  have hm : ∀ u ∈ Set.Icc a b, π * ((1 : ℕ) : ℝ) * (u - a) / (b - a) ∈ Set.Icc 0 π := by
    intro u hu
    have h1 := sub_nonneg.2 hu.1
    refine ⟨by simp only [Nat.cast_one]; positivity, ?_⟩
    simp only [Nat.cast_one]
    rw [mul_one, div_le_iff₀ hba]
    nlinarith [pi_pos, hu.2]
  have := injOn_cos (hm s hs) (hm t ht) h
  simp only [Nat.cast_one, mul_one] at this
  field_simp at this
  linarith

theorem abs_trigS_le_dist (hab : a < b) (m : ℕ) {t : ℝ} (ht : t ∈ Set.Icc a b) :
    |trigS a b m t| ≤ freq a b m * min (t - a) (b - t) := by
  have hba : b - a ≠ 0 := (sub_pos.2 hab).ne'
  have hf : 0 ≤ freq a b m := by
    unfold freq; have := sub_pos.2 hab; positivity
  rw [mul_min_of_nonneg _ _ hf]
  apply le_min
  · have h1 : π * m * (t - a) / (b - a) = freq a b m * (t - a) := by unfold freq; ring
    have h2 : 0 ≤ freq a b m * (t - a) := mul_nonneg hf (sub_nonneg.2 ht.1)
    unfold trigS
    rw [h1]
    calc _ ≤ |freq a b m * (t - a)| := abs_sin_le_abs
      _ = _ := abs_of_nonneg h2
  · have h2 : 0 ≤ freq a b m * (b - t) := mul_nonneg hf (sub_nonneg.2 ht.2)
    have h1 : π * m * (t - a) / (b - a) = m * π - freq a b m * (b - t) := by
      unfold freq; field_simp; ring
    unfold trigS
    rw [h1, sin_sub, sin_nat_mul_pi, cos_nat_mul_pi]
    calc _ = |sin (freq a b m * (b - t))| := by
          simp [abs_mul, abs_pow]
      _ ≤ |freq a b m * (b - t)| := abs_sin_le_abs
      _ = _ := abs_of_nonneg h2

theorem trigNormSq_pos (hab : a < b) (m : ℕ) : 0 < trigNormSq a b m := by
  unfold trigNormSq
  have := sub_pos.2 hab
  split_ifs <;> linarith

end FEEC
