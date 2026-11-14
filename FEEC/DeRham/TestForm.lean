/-
Linear structure of test forms.
-/
import FEEC.DeRham.L2Complex

/-!
# The vector space of test forms

Test forms on `Ω` are closed under linear combinations, and taking the `L²` class and the
codifferential are linear.
-/

namespace FEEC

open MeasureTheory

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Ω : Set E} {k : ℕ}

namespace IsTestForm

theorem add {φ ψ : E → E [⋀^Fin k]→L[ℝ] ℝ} (hφ : IsTestForm Ω φ) (hψ : IsTestForm Ω ψ) :
    IsTestForm Ω (φ + ψ) where
  contDiff := hφ.contDiff.add hψ.contDiff
  hasCompactSupport := hφ.hasCompactSupport.add hψ.hasCompactSupport
  tsupport_subset := (closure_mono (Function.support_add φ ψ)).trans
    (by rw [closure_union]; exact Set.union_subset hφ.tsupport_subset hψ.tsupport_subset)

theorem const_smul (c : ℝ) {φ : E → E [⋀^Fin k]→L[ℝ] ℝ} (hφ : IsTestForm Ω φ) :
    IsTestForm Ω (c • φ) where
  contDiff := contDiff_const.smul hφ.contDiff
  hasCompactSupport := hφ.hasCompactSupport.smul_left
  tsupport_subset := (tsupport_smul_subset_right (fun _ => c) φ).trans hφ.tsupport_subset

theorem neg {φ : E → E [⋀^Fin k]→L[ℝ] ℝ} (hφ : IsTestForm Ω φ) : IsTestForm Ω (-φ) := by
  rw [← neg_one_smul ℝ φ]; exact hφ.const_smul _

theorem sub {φ ψ : E → E [⋀^Fin k]→L[ℝ] ℝ} (hφ : IsTestForm Ω φ) (hψ : IsTestForm Ω ψ) :
    IsTestForm Ω (φ - ψ) := by
  rw [sub_eq_add_neg]; exact hφ.add hψ.neg

variable [MeasurableSpace E] [BorelSpace E]

/-- The `L²` class of a test form depends only on the form. -/
theorem toLp_congr {φ ψ : E → E [⋀^Fin k]→L[ℝ] ℝ} (hφ : IsTestForm Ω φ) (hψ : IsTestForm Ω ψ)
    (h : φ = ψ) : hφ.toLp = hψ.toLp := by
  subst h; rfl

theorem toLp_add {φ ψ : E → E [⋀^Fin k]→L[ℝ] ℝ} (hφ : IsTestForm Ω φ) (hψ : IsTestForm Ω ψ) :
    (hφ.add hψ).toLp = hφ.toLp + hψ.toLp := by
  refine Lp.ext ?_
  filter_upwards [(hφ.add hψ).coeFn_toLp, hφ.coeFn_toLp, hψ.coeFn_toLp,
    Lp.coeFn_add hφ.toLp hψ.toLp] with x h1 h2 h3 h4
  rw [h1, h4]; simp [h2, h3]

theorem toLp_const_smul (c : ℝ) {φ : E → E [⋀^Fin k]→L[ℝ] ℝ} (hφ : IsTestForm Ω φ) :
    (hφ.const_smul c).toLp = c • hφ.toLp := by
  refine Lp.ext ?_
  filter_upwards [(hφ.const_smul c).coeFn_toLp, hφ.coeFn_toLp,
    Lp.coeFn_smul c hφ.toLp] with x h1 h2 h4
  rw [h1, h4]; simp [h2]

theorem toLp_sub {φ ψ : E → E [⋀^Fin k]→L[ℝ] ℝ} (hφ : IsTestForm Ω φ) (hψ : IsTestForm Ω ψ) :
    (hφ.sub hψ).toLp = hφ.toLp - hψ.toLp := by
  refine Lp.ext ?_
  filter_upwards [(hφ.sub hψ).coeFn_toLp, hφ.coeFn_toLp, hψ.coeFn_toLp,
    Lp.coeFn_sub hφ.toLp hψ.toLp] with x h1 h2 h3 h4
  rw [h1, h4]; simp [h2, h3]

/-- The `L²(Ω)` norm of the class of a test form. -/
theorem norm_toLp_sq {φ : E → E [⋀^Fin k]→L[ℝ] ℝ} (hφ : IsTestForm Ω φ) :
    ‖hφ.toLp‖ ^ 2 = ∫ x in Ω, ‖Covector.ofAlt (φ x)‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hφ.coeFn_toLp] with x hx
  rw [hx, real_inner_self_eq_norm_sq]

end IsTestForm

variable (Ω k) in
/-- The vector space of test `k`-forms on `Ω`. -/
def testForms : Submodule ℝ (E → E [⋀^Fin k]→L[ℝ] ℝ) where
  carrier := {φ | IsTestForm Ω φ}
  add_mem' h h' := h.add h'
  zero_mem' := IsTestForm.zero
  smul_mem' c _ h := h.const_smul c

variable [MeasurableSpace E] [BorelSpace E]

variable (Ω k) in
/-- The `L²` class, as a linear map on test forms. -/
noncomputable def testFormsToLp : testForms Ω k →ₗ[ℝ] L2Form Ω k where
  toFun φ := IsTestForm.toLp (φ := φ.1) φ.2
  map_add' φ ψ := IsTestForm.toLp_add φ.2 ψ.2
  map_smul' c φ := IsTestForm.toLp_const_smul c φ.2

variable (Ω k) in
/-- The `L²` class of the codifferential, as a linear map on test forms. -/
noncomputable def testFormsCodiffToLp : testForms Ω (k + 1) →ₗ[ℝ] L2Form Ω k where
  toFun φ := (IsTestForm.codiff (φ := φ.1) φ.2).toLp
  map_add' φ ψ :=
    (IsTestForm.toLp_congr _ (φ.2.codiff.add ψ.2.codiff)
      (codiff_add (φ.2.contDiff.differentiable (by simp))
        (ψ.2.contDiff.differentiable (by simp)))).trans
      (IsTestForm.toLp_add φ.2.codiff ψ.2.codiff)
  map_smul' c φ :=
    (IsTestForm.toLp_congr _ (φ.2.codiff.const_smul c)
      (codiff_const_smul c (φ.2.contDiff.differentiable (by simp)))).trans
      (IsTestForm.toLp_const_smul c φ.2.codiff)

end FEEC
