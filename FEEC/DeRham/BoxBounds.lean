/-
`L²` bounds for the one-directional homotopy operators.
-/
import FEEC.DeRham.BoxHomotopy
import FEEC.DeRham.LineL2
import FEEC.DeRham.TestForm

/-!
# `L²` bounds for the homotopy operators

On a slab `Ω` in direction `e`, the operators `homotopyS e θ` and `homotopyQ e θ` are bounded
in the `L²(Ω)` norm on test forms.
-/

namespace FEEC

open MeasureTheory

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Set E} {e : E} {θ : ℝ → ℝ} {a b : ℝ}


section Aux

set_option linter.unusedSectionVars false

/-- Bound on the line integral of a bounded function supported in a slab. -/
lemma line_bound {Ω : Set E} {e : E} (he : ‖e‖ = 1)
    (hΩ : ∀ x ∈ Ω, ⟪e, x⟫ ∈ Set.Ioo a b) {h : E → ℝ} (hsupp : ∀ x, x ∉ Ω → h x = 0)
    {M : ℝ} (hM : ∀ y, |h y| ≤ M) {x : E} (hx : x ∈ Ω) :
    |∫ τ : ℝ, h (x + τ • e)| ≤ M * (b - a) := by
  have hee : ⟪e, e⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  have hxab := hΩ x hx
  have hz : ∀ τ : ℝ, τ ∉ Set.Ioo (a - ⟪e, x⟫) (b - ⟪e, x⟫) → h (x + τ • e) = 0 := by
    intro τ hτ
    apply hsupp
    intro hmem
    have := hΩ _ hmem
    rw [inner_add_right, inner_smul_right, hee] at this
    exact hτ ⟨by linarith [this.1], by linarith [this.2]⟩
  have e1 : ∫ τ in Set.Ioo (a - ⟪e, x⟫) (b - ⟪e, x⟫), h (x + τ • e) = ∫ τ : ℝ, h (x + τ • e) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hz
  rw [← e1]
  have := norm_setIntegral_le_of_norm_le_const (μ := volume)
    (s := Set.Ioo (a - ⟪e, x⟫) (b - ⟪e, x⟫)) (f := fun τ : ℝ => h (x + τ • e)) (C := M)
    (by simp) (fun τ _ => by simpa using hM _)
  have hv : volume.real (Set.Ioo (a - ⟪e, x⟫) (b - ⟪e, x⟫)) = b - a := by
    rw [Real.volume_real_Ioo_of_le]
    · ring
    · linarith [hxab.1, hxab.2]
  rw [hv] at this
  simpa using this

lemma integrableOn_sq_line {Ω : Set E} (hΩm : MeasurableSet Ω) {e : E} (he : ‖e‖ = 1)
    (hΩ : ∀ x ∈ Ω, ⟪e, x⟫ ∈ Set.Ioo a b) {h : E → ℝ} (hc : Continuous h)
    (hcs : HasCompactSupport h) (hsupp : ∀ x, x ∉ Ω → h x = 0) :
    IntegrableOn (fun x => (∫ τ : ℝ, h (x + τ • e)) ^ 2) Ω := by
  have hee : ⟪e, e⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  obtain ⟨M, hM⟩ := hc.bounded_above_of_compact_support hcs
  obtain ⟨R, hR⟩ := exists_support_bound hcs
  have hM' : ∀ y, |h y| ≤ M := fun y => by simpa using hM y
  have hS : Measurable (fun x : E => ∫ τ : ℝ, h (x + τ • e)) := by
    have : Continuous (fun p : E × ℝ => h (p.1 + p.2 • e)) := by fun_prop
    exact (this.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
  rw [← integrable_indicator_iff hΩm]
  have hB : Integrable ((Metric.closedBall (0 : E) (R + (b - a))).indicator
      (fun _ => (M * (b - a)) ^ 2)) :=
    (integrable_indicator_iff Metric.isClosed_closedBall.measurableSet).2
      (integrableOn_const (measure_closedBall_lt_top.ne) )
  refine hB.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact ((hS.pow_const 2).indicator hΩm).aestronglyMeasurable
  · by_cases hx : x ∈ Ω
    · have hb := line_bound he hΩ hsupp hM' hx
      by_cases hxB : x ∈ Metric.closedBall (0 : E) (R + (b - a))
      · simp only [Set.indicator_of_mem hx, Set.indicator_of_mem hxB, norm_pow, Real.norm_eq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hb 2 |>.trans_eq' (by simp [sq_abs])
      · have h0 : ∫ τ : ℝ, h (x + τ • e) = 0 := by
          have : ∀ τ : ℝ, h (x + τ • e) = 0 := by
            intro τ
            by_contra hne
            apply hxB
            have h1 := hR _ hne
            have hmem := hΩ _ (by_contra fun hn => hne (hsupp _ hn))
            rw [inner_add_right, inner_smul_right, hee] at hmem
            have hxab := hΩ x hx
            have h2 : ‖τ • e‖ = |τ| := by rw [norm_smul, he, mul_one, Real.norm_eq_abs]
            have h3 : ‖x‖ ≤ ‖x + τ • e‖ + ‖τ • e‖ := by
              have := norm_sub_le (x + τ • e) (τ • e)
              simpa using this
            have h4 : |τ| ≤ b - a := by
              rw [abs_le]; constructor <;> linarith [hmem.1, hmem.2, hxab.1, hxab.2]
            rw [mem_closedBall_zero_iff]
            linarith
          simp [this]
        simp only [Set.indicator_of_mem hx, h0]
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, norm_zero]
        exact Set.indicator_nonneg (fun _ _ => sq_nonneg _) _
    · simp only [Set.indicator_of_notMem hx, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => sq_nonneg _) _

lemma sq_bound_of_pointwise {Ω : Set E} (hΩm : MeasurableSet Ω) {e : E} (he : ‖e‖ = 1)
    (hΩ : ∀ x ∈ Ω, ⟪e, x⟫ ∈ Set.Ioo a b) {h : E → ℝ} (hc : Continuous h)
    (hcs : HasCompactSupport h) (h0 : ∀ x, 0 ≤ h x) (hsupp : ∀ x, x ∉ Ω → h x = 0)
    {g : E → ℝ} (hg : IntegrableOn (fun x => g x ^ 2) Ω) {C : ℝ}
    (hpt : ∀ x ∈ Ω, |g x| ≤ C * ∫ τ : ℝ, h (x + τ • e)) :
    ∫ x in Ω, g x ^ 2 ≤ (C * (b - a)) ^ 2 * ∫ x in Ω, h x ^ 2 := by
  have hN0 : ∀ x, 0 ≤ ∫ τ : ℝ, h (x + τ • e) := fun x => integral_nonneg fun τ => h0 _
  have hint := integrableOn_sq_line hΩm he hΩ hc hcs hsupp
  calc ∫ x in Ω, g x ^ 2 ≤ ∫ x in Ω, C ^ 2 * (∫ τ : ℝ, h (x + τ • e)) ^ 2 := by
        refine setIntegral_mono_on hg (hint.const_mul _) hΩm fun x hx => ?_
        have h1 := hpt x hx
        have hC : 0 ≤ C * ∫ τ : ℝ, h (x + τ • e) := (abs_nonneg _).trans h1
        calc g x ^ 2 = |g x| ^ 2 := (sq_abs _).symm
          _ ≤ (C * ∫ τ : ℝ, h (x + τ • e)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
          _ = _ := by ring
    _ = C ^ 2 * ∫ x in Ω, (∫ τ : ℝ, h (x + τ • e)) ^ 2 := integral_const_mul _ _
    _ ≤ C ^ 2 * ((b - a) ^ 2 * ∫ x in Ω, h x ^ 2) := by
        gcongr
        exact integral_sq_lineInt_le hΩm he hΩ hc hcs h0 hsupp
    _ = _ := by ring

/-- Comparing a form-valued line integral with its covector norm. -/
lemma line_form_bound {e : E} (he : ‖e‖ = 1) {k : ℕ} {φ : E → E [⋀^Fin k]→L[ℝ] ℝ}
    (hc : Continuous φ) (hcs : HasCompactSupport φ) (x : E) :
    ∫ τ : ℝ, ‖φ (x + τ • e)‖ ≤
      ‖(Covector.ofAlt (E := E) (k := k)).symm.toContinuousLinearMap‖ *
        ∫ τ : ℝ, ‖Covector.ofAlt (φ (x + τ • e))‖ := by
  set L := (Covector.ofAlt (E := E) (k := k))
  have hi := (integrable_comp_line he hc hcs x).norm
  have hi2 : Integrable (fun τ : ℝ => ‖L (φ (x + τ • e))‖) := by
    refine (hi.const_mul ‖L.toContinuousLinearMap‖).mono' ?_ (Filter.Eventually.of_forall fun τ => ?_)
    · have : Continuous (fun τ : ℝ => ‖L (φ (x + τ • e))‖) := by fun_prop
      exact this.aestronglyMeasurable
    · simpa using L.toContinuousLinearMap.le_opNorm (φ (x + τ • e))
  rw [← integral_const_mul]
  refine integral_mono hi (hi2.const_mul _) fun τ => ?_
  simpa using L.symm.toContinuousLinearMap.le_opNorm (L (φ (x + τ • e)))

lemma bound_of_pointwise {Ω : Set E} (hΩm : MeasurableSet Ω) {e : E} (he : ‖e‖ = 1)
    (hΩ : IsSlab Ω e a b) {k j : ℕ} {φ : E → E [⋀^Fin k]→L[ℝ] ℝ} (hφ : IsTestForm Ω φ)
    {ψ : E → E [⋀^Fin j]→L[ℝ] ℝ} (hψ : IsTestForm Ω ψ) {K : ℝ} (hK : 0 ≤ K)
    (hpt : ∀ x, ‖ψ x‖ ≤ K * ∫ τ : ℝ, ‖φ (x + τ • e)‖) :
    ‖hψ.toLp‖ ≤ (‖(Covector.ofAlt (E := E) (k := j)).toContinuousLinearMap‖ * K *
      ‖(Covector.ofAlt (E := E) (k := k)).symm.toContinuousLinearMap‖ * |b - a|) * ‖hφ.toLp‖ := by
  set c₀ := ‖(Covector.ofAlt (E := E) (k := j)).toContinuousLinearMap‖
  set c₁ := ‖(Covector.ofAlt (E := E) (k := k)).symm.toContinuousLinearMap‖
  have hφc := hφ.contDiff.continuous
  have hH : Continuous (fun y => ‖Covector.ofAlt (φ y)‖) := by fun_prop
  have hHc : HasCompactSupport (fun y => ‖Covector.ofAlt (φ y)‖) := by
    have := hφ.hasCompactSupport.comp_left (g := fun v => ‖Covector.ofAlt (E := E) (k := k) v‖)
      (by simp)
    exact this
  have hsupp : ∀ x, x ∉ Ω → ‖Covector.ofAlt (φ x)‖ = 0 := fun x hx => by
    have : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hφ.tsupport_subset h))
    simp [this]
  have hψsq : IntegrableOn (fun x => ‖Covector.ofAlt (ψ x)‖ ^ 2) Ω := by
    have hc : Continuous (fun x => ‖Covector.ofAlt (ψ x)‖ ^ 2) := by
      have := hψ.contDiff.continuous
      fun_prop
    have hcs : HasCompactSupport (fun x => ‖Covector.ofAlt (ψ x)‖ ^ 2) := by
      have := hψ.hasCompactSupport.comp_left
        (g := fun v => ‖Covector.ofAlt (E := E) (k := j) v‖ ^ 2) (by simp)
      exact this
    exact (hc.integrable_of_hasCompactSupport hcs).integrableOn
  have hmain := sq_bound_of_pointwise hΩm he hΩ.mem_Ioo hH hHc (fun _ => norm_nonneg _) hsupp
    hψsq (C := c₀ * K * c₁) (fun x _ => by
      rw [abs_of_nonneg (norm_nonneg _)]
      calc ‖Covector.ofAlt (ψ x)‖ ≤ c₀ * ‖ψ x‖ := by
            simpa using (Covector.ofAlt (E := E) (k := j)).toContinuousLinearMap.le_opNorm (ψ x)
        _ ≤ c₀ * (K * ∫ τ : ℝ, ‖φ (x + τ • e)‖) := by gcongr; exact hpt x
        _ ≤ c₀ * (K * (c₁ * ∫ τ : ℝ, ‖Covector.ofAlt (φ (x + τ • e))‖)) := by
            gcongr; exact line_form_bound he hφc hφ.hasCompactSupport x
        _ = _ := by ring)
  rw [← hψ.norm_toLp_sq, ← hφ.norm_toLp_sq] at hmain
  have : ‖hψ.toLp‖ ^ 2 ≤ ((c₀ * K * c₁ * |b - a|) * ‖hφ.toLp‖) ^ 2 := by
    calc _ ≤ _ := hmain
      _ = _ := by simp only [mul_pow, sq_abs]
  have hc0 : 0 ≤ c₀ * K * c₁ * |b - a| * ‖hφ.toLp‖ := by positivity
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hc0 two_ne_zero).1 this

end Aux

theorem exists_norm_homotopyS_le (hΩm : MeasurableSet Ω) (hΩ : IsSlab Ω e a b)
    (hθ : IsBump θ a b) (he : ‖e‖ = 1) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : E → E [⋀^Fin k]→L[ℝ] ℝ) (hφ : IsTestForm Ω φ)
      (hS : IsTestForm Ω (homotopyS e θ φ)), ‖hS.toLp‖ ≤ C * ‖hφ.toLp‖ := by
  set K := ‖wedgeLeft (E := E) (k := k) e‖ * ((∫ t, |θ t|) + 1)
  have hK : 0 ≤ K := by positivity
  refine ⟨_, by positivity, fun φ hφ hS => bound_of_pointwise hΩm he hΩ hφ hS hK (fun x => ?_)⟩
  calc ‖homotopyS e θ φ x‖ ≤ ‖wedgeLeft (E := E) (k := k) e‖ * ‖lineG e θ φ x‖ :=
        (wedgeLeft e).le_opNorm _
    _ ≤ ‖wedgeLeft (E := E) (k := k) e‖ * (((∫ t, |θ t|) + 1) *
          ∫ τ : ℝ, ‖φ (x + τ • e)‖) := by
        gcongr; exact norm_lineG_le hθ he hφ.contDiff.continuous hφ.hasCompactSupport x
    _ = _ := by ring

theorem exists_norm_homotopyQ_le (hΩm : MeasurableSet Ω) (hΩ : IsSlab Ω e a b)
    (hθ : IsBump θ a b) (he : ‖e‖ = 1) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : E → E [⋀^Fin k]→L[ℝ] ℝ) (hφ : IsTestForm Ω φ)
      (hQ : IsTestForm Ω (homotopyQ e θ φ)), ‖hQ.toLp‖ ≤ C * ‖hφ.toLp‖ := by
  obtain ⟨Mθ, hMθ⟩ := hθ.contDiff.continuous.bounded_above_of_compact_support hθ.hasCompactSupport
  set K := (|Mθ|) * ‖tangPartAll (E := E) e k‖
  have hK : 0 ≤ K := by positivity
  refine ⟨_, by positivity, fun φ hφ hQ => bound_of_pointwise hΩm he hΩ hφ hQ hK (fun x => ?_)⟩
  have h1 : |θ ⟪e, x⟫| ≤ |Mθ| := by
    have := hMθ ⟪e, x⟫
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_abs_self _)
  calc ‖homotopyQ e θ φ x‖ = |θ ⟪e, x⟫| * ‖tangPartAll e k (lineInt e φ x)‖ := by
        rw [homotopyQ, norm_smul, Real.norm_eq_abs]
    _ ≤ |Mθ| * (‖tangPartAll (E := E) e k‖ * ‖lineInt e φ x‖) := by
        gcongr
        exact (tangPartAll e k).le_opNorm _
    _ ≤ |Mθ| * (‖tangPartAll (E := E) e k‖ * ∫ τ : ℝ, ‖φ (x + τ • e)‖) := by
        gcongr; exact norm_lineInt_le e φ x
    _ = _ := by ring

end FEEC
