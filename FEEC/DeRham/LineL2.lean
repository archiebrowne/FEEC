/-
An `L²` bound for integrals along lines in a slab.
-/
import Mathlib

/-!
# An `L²` bound for integrals along lines

If `Ω` lies in the slab `{x | a < ⟪e, x⟫ < b}` and `h ≥ 0` is continuous, compactly supported
and vanishes outside `Ω`, then

`∫_Ω (∫_ℝ h (x + τ • e) dτ)² dx ≤ (b - a)² ∫_Ω h²`.

(Cauchy–Schwarz on a segment of length at most `b - a`, then Tonelli and translation
invariance of Lebesgue measure.)
-/

namespace FEEC

open MeasureTheory

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- One-variable Cauchy–Schwarz on an interval. -/
lemma sq_integral_le_of_zero_off {k : ℝ → ℝ} (hk : Continuous k) {p q : ℝ} (hpq : p < q)
    (hz : ∀ τ, τ ∉ Set.Ioo p q → k τ = 0) :
    (∫ τ, k τ) ^ 2 ≤ (q - p) * ∫ τ, k τ ^ 2 := by
  have hL : 0 < q - p := sub_pos.mpr hpq
  have hi1 : IntegrableOn k (Set.Ioo p q) :=
    (hk.integrableOn_Icc (a := p) (b := q)).mono_set Set.Ioo_subset_Icc_self
  have hi2 : IntegrableOn (fun τ => k τ ^ 2) (Set.Ioo p q) :=
    ((hk.pow 2).integrableOn_Icc (a := p) (b := q)).mono_set Set.Ioo_subset_Icc_self
  have e1 : ∫ τ in Set.Ioo p q, k τ = ∫ τ, k τ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hz
  have e2 : ∫ τ in Set.Ioo p q, k τ ^ 2 = ∫ τ, k τ ^ 2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun τ hτ => by simp [hz τ hτ])
  set S := ∫ τ, k τ
  set Q := ∫ τ, k τ ^ 2
  set m := S / (q - p) with hm
  have h0 : 0 ≤ ∫ τ in Set.Ioo p q, (k τ - m) ^ 2 :=
    setIntegral_nonneg measurableSet_Ioo (fun τ _ => sq_nonneg _)
  have : ∫ τ in Set.Ioo p q, (k τ - m) ^ 2
      = (∫ τ in Set.Ioo p q, k τ ^ 2) - 2 * m * (∫ τ in Set.Ioo p q, k τ) + m ^ 2 * (q - p) := by
    have : ∀ τ, (k τ - m) ^ 2 = (k τ ^ 2 - 2 * m * k τ) + m ^ 2 := fun τ => by ring
    simp_rw [this]
    have hi3 : IntegrableOn (fun τ => 2 * m * k τ) (Set.Ioo p q) := hi1.const_mul _
    have hi4 : IntegrableOn (fun τ => k τ ^ 2 - 2 * m * k τ) (Set.Ioo p q) := hi2.sub hi3
    have hi5 : IntegrableOn (fun _ : ℝ => m ^ 2) (Set.Ioo p q) := integrableOn_const (by simp)
    rw [integral_add hi4 hi5, integral_sub hi2 hi3, integral_const_mul]
    simp [Real.volume_real_Ioo_of_le hpq.le, mul_comm]
  rw [this, e1, e2, hm] at h0
  have : S ^ 2 / (q - p) ≤ Q := by
    field_simp at h0 ⊢
    nlinarith [h0]
  rw [div_le_iff₀ hL] at this
  linarith

/-- Per-slice bound. -/
lemma slice_bound {Ω : Set E} {e : E} (he : ‖e‖ = 1)
    {a b : ℝ} (hΩ : ∀ x ∈ Ω, ⟪e, x⟫ ∈ Set.Ioo a b) {h : E → ℝ} (hc : Continuous h)
    (hsupp : ∀ x, x ∉ Ω → h x = 0) {x : E} (hx : x ∈ Ω) :
    ENNReal.ofReal ((∫ τ : ℝ, h (x + τ • e)) ^ 2) ≤
      ENNReal.ofReal (b - a) * ∫⁻ τ : ℝ, ENNReal.ofReal (h (x + τ • e) ^ 2) := by
  have hee : ⟪e, e⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  have hxab := hΩ x hx
  have hab : a < b := hxab.1.trans hxab.2
  have hk : Continuous (fun τ : ℝ => h (x + τ • e)) := by fun_prop
  have hz : ∀ τ : ℝ, τ ∉ Set.Ioo (a - ⟪e, x⟫) (b - ⟪e, x⟫) → h (x + τ • e) = 0 := by
    intro τ hτ
    apply hsupp
    intro hmem
    have := hΩ _ hmem
    rw [inner_add_right, inner_smul_right, hee] at this
    exact hτ ⟨by linarith [this.1], by linarith [this.2]⟩
  have hlt : a - ⟪e, x⟫ < b - ⟪e, x⟫ := by linarith
  have hcs := sq_integral_le_of_zero_off hk hlt hz
  have hint : Integrable (fun τ : ℝ => h (x + τ • e) ^ 2) := by
    refine IntegrableOn.integrable_of_forall_notMem_eq_zero (s := Set.Ioo (a - ⟪e, x⟫) (b - ⟪e, x⟫))
      ?_ (fun τ hτ => by simp [hz τ hτ])
    exact ((hk.pow 2).integrableOn_Icc (a := a - ⟪e, x⟫) (b := b - ⟪e, x⟫)).mono_set
      Set.Ioo_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun τ => sq_nonneg _),
    ← ENNReal.ofReal_mul (by linarith)]
  apply ENNReal.ofReal_le_ofReal
  have : b - ⟪e, x⟫ - (a - ⟪e, x⟫) = b - a := by ring
  rwa [this] at hcs

lemma lintegral_swap_bound {Ω : Set E} (hΩm : MeasurableSet Ω) {e : E} (he : ‖e‖ = 1)
    {a b : ℝ} (hΩ : ∀ x ∈ Ω, ⟪e, x⟫ ∈ Set.Ioo a b) {h : E → ℝ} (hc : Continuous h) :
    ∫⁻ x in Ω, ∫⁻ τ : ℝ, ENNReal.ofReal (h (x + τ • e) ^ 2) ≤
      ENNReal.ofReal (b - a) * ∫⁻ y, ENNReal.ofReal (h y ^ 2) := by
  have hee : ⟪e, e⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  set f : E → ENNReal := fun y => ENNReal.ofReal (h y ^ 2) with hf
  have hfm : Measurable f := (ENNReal.measurable_ofReal.comp (hc.pow 2).measurable)
  have hind : Measurable (Ω.indicator (1 : E → ENNReal)) := measurable_one.indicator hΩm
  -- step 1: write with indicator
  have h1 : ∫⁻ x in Ω, ∫⁻ τ : ℝ, f (x + τ • e) =
      ∫⁻ x, ∫⁻ τ : ℝ, Ω.indicator (1 : E → ENNReal) x * f (x + τ • e) := by
    rw [← lintegral_indicator hΩm]
    congr 1; ext x
    by_cases hx : x ∈ Ω <;> simp [hx]
  have hmeas1 : Measurable (fun p : E × ℝ => Ω.indicator (1 : E → ENNReal) p.1 *
      f (p.1 + p.2 • e)) := by
    refine (hind.comp measurable_fst).mul (hfm.comp ?_)
    fun_prop
  rw [h1, lintegral_lintegral_swap hmeas1.aemeasurable]
  have h2 : ∀ τ : ℝ, ∫⁻ x, Ω.indicator (1 : E → ENNReal) x * f (x + τ • e) =
      ∫⁻ y, Ω.indicator (1 : E → ENNReal) (y - τ • e) * f y := by
    intro τ
    rw [← lintegral_add_right_eq_self (fun y => Ω.indicator (1 : E → ENNReal) (y - τ • e) * f y)
      (τ • e)]
    simp
  simp_rw [h2]
  have hmeas2 : Measurable (fun p : ℝ × E => Ω.indicator (1 : E → ENNReal) (p.2 - p.1 • e) *
      f p.2) := by
    refine (hind.comp ?_).mul (hfm.comp measurable_snd)
    fun_prop
  rw [lintegral_lintegral_swap hmeas2.aemeasurable]
  calc ∫⁻ y, ∫⁻ τ : ℝ, Ω.indicator (1 : E → ENNReal) (y - τ • e) * f y
      ≤ ∫⁻ y, ENNReal.ofReal (b - a) * f y := by
        refine lintegral_mono (fun y => ?_)
        have hsub : ∫⁻ τ : ℝ, Ω.indicator (1 : E → ENNReal) (y - τ • e) ≤
            ∫⁻ τ : ℝ, (Set.Ioo (⟪e, y⟫ - b) (⟪e, y⟫ - a)).indicator 1 τ := by
          refine lintegral_mono (fun τ => ?_)
          by_cases hτ : y - τ • e ∈ Ω
          · have := hΩ _ hτ
            rw [inner_sub_right, inner_smul_right, hee] at this
            have hmem : τ ∈ Set.Ioo (⟪e, y⟫ - b) (⟪e, y⟫ - a) :=
              ⟨by linarith [this.2], by linarith [this.1]⟩
            simp [hτ, hmem]
          · simp [hτ]
        have hbd : ∫⁻ τ : ℝ, Ω.indicator (1 : E → ENNReal) (y - τ • e) ≤ ENNReal.ofReal (b - a) := by
          refine hsub.trans ?_
          rw [lintegral_indicator_one measurableSet_Ioo, Real.volume_Ioo]
          apply le_of_eq; congr 1; ring
        rw [lintegral_mul_const' _ _ (by simp [hf])]
        gcongr
    _ = ENNReal.ofReal (b - a) * ∫⁻ y, f y := lintegral_const_mul _ hfm

theorem integral_sq_lineInt_le {Ω : Set E} (hΩm : MeasurableSet Ω) {e : E} (he : ‖e‖ = 1)
    {a b : ℝ} (hΩ : ∀ x ∈ Ω, ⟪e, x⟫ ∈ Set.Ioo a b) {h : E → ℝ} (hc : Continuous h)
    (hcs : HasCompactSupport h) (h0 : ∀ x, 0 ≤ h x) (hsupp : ∀ x, x ∉ Ω → h x = 0) :
    ∫ x in Ω, (∫ τ : ℝ, h (x + τ • e)) ^ 2 ≤ (b - a) ^ 2 * ∫ x in Ω, (h x) ^ 2 := by
  rcases Ω.eq_empty_or_nonempty with rfl | ⟨x0, hx0⟩
  · simp
  have hab : a < b := (hΩ x0 hx0).1.trans (hΩ x0 hx0).2
  have hint : Integrable (fun y => h y ^ 2) := (hc.pow 2).integrable_of_hasCompactSupport
    (hcs.mono (fun y hy => by
      rw [Function.mem_support] at hy ⊢
      intro h0'
      apply hy
      simp [h0']))
  have hEΩ : ∫ x in Ω, h x ^ 2 = ∫ x, h x ^ 2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by simp [hsupp x hx])
  have hS : Measurable (fun x : E => ∫ τ : ℝ, h (x + τ • e)) := by
    have : Continuous (fun p : E × ℝ => h (p.1 + p.2 • e)) := by fun_prop
    exact (this.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
  have hL : ∫ x in Ω, (∫ τ : ℝ, h (x + τ • e)) ^ 2 =
      (∫⁻ x in Ω, ENNReal.ofReal ((∫ τ : ℝ, h (x + τ • e)) ^ 2)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => sq_nonneg _)
      ((hS.pow_const 2).aestronglyMeasurable)
  have hle : ∫⁻ x in Ω, ENNReal.ofReal ((∫ τ : ℝ, h (x + τ • e)) ^ 2) ≤
      ENNReal.ofReal ((b - a) ^ 2 * ∫ x in Ω, h x ^ 2) := by
    calc ∫⁻ x in Ω, ENNReal.ofReal ((∫ τ : ℝ, h (x + τ • e)) ^ 2)
        ≤ ∫⁻ x in Ω, ENNReal.ofReal (b - a) *
            ∫⁻ τ : ℝ, ENNReal.ofReal (h (x + τ • e) ^ 2) :=
          setLIntegral_mono' hΩm (fun x hx => slice_bound he hΩ hc hsupp hx)
      _ = ENNReal.ofReal (b - a) * ∫⁻ x in Ω, ∫⁻ τ : ℝ, ENNReal.ofReal (h (x + τ • e) ^ 2) :=
          lintegral_const_mul' _ _ (by simp)
      _ ≤ ENNReal.ofReal (b - a) * (ENNReal.ofReal (b - a) *
            ∫⁻ y, ENNReal.ofReal (h y ^ 2)) :=
          by gcongr; exact lintegral_swap_bound hΩm he hΩ hc
      _ = ENNReal.ofReal ((b - a) ^ 2 * ∫ x in Ω, h x ^ 2) := by
          rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun τ => sq_nonneg _),
            hEΩ.symm.symm, ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul (by linarith)]
          congr 1; ring
  rw [hL]
  exact ENNReal.toReal_le_of_le_ofReal
    (mul_nonneg (sq_nonneg _) (setIntegral_nonneg hΩm fun x _ => sq_nonneg _)) hle

end FEEC
