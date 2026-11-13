/-
Differential forms on the real line in scalar terms.
-/
import FEEC.DeRham.L2Complex
import FEEC.Interval.Scalar

/-!
# The `L²` de Rham complex of an interval in scalar terms

On `E = ℝ` a `0`-form is a function and a `1`-form is `g dx`. This file identifies
`L²Λ⁰(a,b)` and `L²Λ¹(a,b)` with `L²(a,b)` isometrically (`s0`, `s1`), shows that under these
identifications the weak exterior derivative is the weak derivative
(`hasWeakExtDeriv_iff`), and that there are no forms of degree `≥ 2`.
-/

namespace FEEC.Interval

open MeasureTheory Set

variable {a b : ℝ}

/-! ### Covectors on `ℝ` -/

instance : Unique (Fin (Module.finrank ℝ ℝ)) := by
  rw [Module.finrank_self]; infer_instance

/-- Every vector of the standard basis of `ℝ` is `1` or `-1`. -/
theorem stdBasis_real (i : Fin (Module.finrank ℝ ℝ)) : stdBasis ℝ i = 1 ∨ stdBasis ℝ i = -1 := by
  have h := (stdBasis ℝ).norm_eq_one i
  rw [Real.norm_eq_abs] at h
  exact abs_eq (zero_le_one) |>.1 h

/-- A `1`-form on `ℝ` is determined by its value on `1`. -/
theorem alt1_apply (α : ℝ [⋀^Fin 1]→L[ℝ] ℝ) (v : Fin 1 → ℝ) : α v = v 0 * α ![1] := by
  have : v = fun i => v i • (![1] : Fin 1 → ℝ) i := by
    funext i; fin_cases i; simp
  conv_lhs => rw [this]
  rw [α.map_smul_univ]
  simp

theorem coeff_zero (α : Covector ℝ 0) (I : Fin 0 → Fin (Module.finrank ℝ ℝ)) :
    α.coeff I = α.toAlt ![] := by
  simp only [Covector.coeff]
  congr 1
  exact Subsingleton.elim _ _

theorem coeff_one (α : Covector ℝ 1) (I : Fin 1 → Fin (Module.finrank ℝ ℝ)) :
    α.coeff I = stdBasis ℝ (I 0) * α.toAlt ![1] := by
  simp only [Covector.coeff]
  rw [alt1_apply]

theorem inner_cov0 (α β : Covector ℝ 0) : inner ℝ α β = α.toAlt ![] * β.toAlt ![] := by
  rw [Covector.inner_def]
  simp [coeff_zero]

theorem inner_cov1 (α β : Covector ℝ 1) : inner ℝ α β = α.toAlt ![1] * β.toAlt ![1] := by
  rw [Covector.inner_def]
  simp only [coeff_one, Nat.factorial_one, Nat.cast_one, inv_one, one_mul]
  rw [Finset.sum_eq_single (fun _ => default)]
  · have : ∀ x : Fin (Module.finrank ℝ ℝ), x = default := fun x => Subsingleton.elim _ _
    rcases stdBasis_real (default : Fin (Module.finrank ℝ ℝ)) with h | h <;> simp [h]
  · intro I _ hI; exact absurd (funext fun i => Subsingleton.elim _ _) hI
  · simp

/-- A `0`-covector on `ℝ` is a scalar. -/
noncomputable def cov0 : Covector ℝ 0 ≃ₗᵢ[ℝ] ℝ :=
  LinearEquiv.isometryOfInner
    { toFun := fun α => α.toAlt ![]
      map_add' := fun α β => by simp [Covector.toAlt]
      map_smul' := fun c α => by simp [Covector.toAlt]
      invFun := fun c => Covector.ofAlt (ContinuousAlternatingMap.constOfIsEmpty ℝ ℝ (Fin 0) c)
      left_inv := fun α => by
        refine (congrArg Covector.ofAlt ?_).trans (Covector.ofAlt_toAlt α)
        refine ContinuousAlternatingMap.ext fun v => ?_
        have : v = ![] := Subsingleton.elim _ _
        simp [this]
      right_inv := fun c => by simp }
    (fun α β => by
      change inner ℝ (α.toAlt ![]) (β.toAlt ![]) = inner ℝ α β
      rw [inner_cov0]; simp [mul_comm])

/-- A `1`-covector on `ℝ` is a scalar: its value on the unit vector `1`. -/
noncomputable def cov1 : Covector ℝ 1 ≃ₗᵢ[ℝ] ℝ :=
  LinearEquiv.isometryOfInner
    { toFun := fun α => α.toAlt ![1]
      map_add' := fun α β => by simp [Covector.toAlt]
      map_smul' := fun c α => by simp [Covector.toAlt]
      invFun := fun c => Covector.ofAlt
        (ContinuousAlternatingMap.ofSubsingleton ℝ ℝ ℝ (0 : Fin 1) (c • ContinuousLinearMap.id ℝ ℝ))
      left_inv := fun α => by
        refine (congrArg Covector.ofAlt ?_).trans (Covector.ofAlt_toAlt α)
        refine ContinuousAlternatingMap.ext fun v => ?_
        rw [alt1_apply α.toAlt v]
        simp [mul_comm]
      right_inv := fun c => by simp }
    (fun α β => by
      change inner ℝ (α.toAlt ![1]) (β.toAlt ![1]) = inner ℝ α β
      rw [inner_cov1]; simp [mul_comm])

theorem cov0_apply (α : Covector ℝ 0) : cov0 α = α.toAlt ![] := rfl

theorem cov1_apply (α : Covector ℝ 1) : cov1 α = α.toAlt ![1] := rfl

/-- There are no nonzero alternating forms of degree `≥ 2` on `ℝ`. -/
instance (k : ℕ) : Subsingleton (Covector ℝ (k + 2)) := by
  refine subsingleton_of_forall_eq 0 fun α => Covector.eq_zero_of_coeff α fun I => ?_
  have h : (fun j => stdBasis ℝ (I j)) 0 = (fun j => stdBasis ℝ (I j)) 1 := by
    simp only [Subsingleton.elim (I 0) (I 1)]
  exact α.toAlt.map_eq_zero_of_eq _ h (by simp)

/-! ### `L²` forms as scalar `L²` functions -/

section LpCongr

variable {α F G : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Composition with a linear isometry equivalence is a linear isometry equivalence of `L²`. -/
noncomputable def lpCongr (L : F ≃ₗᵢ[ℝ] G) : Lp F 2 μ ≃ₗᵢ[ℝ] Lp G 2 μ where
  toFun f := (L.toContinuousLinearEquiv : F →L[ℝ] G).compLp f
  invFun f := (L.symm.toContinuousLinearEquiv : G →L[ℝ] F).compLp f
  map_add' f g := (ContinuousLinearMap.compLpₗ 2 μ (L.toContinuousLinearEquiv : F →L[ℝ] G)).map_add f g
  map_smul' c f :=
    (ContinuousLinearMap.compLpₗ 2 μ (L.toContinuousLinearEquiv : F →L[ℝ] G)).map_smul c f
  left_inv f := by
    refine Lp.ext ?_
    filter_upwards [ContinuousLinearMap.coeFn_compLp (L.symm.toContinuousLinearEquiv : G →L[ℝ] F)
      ((L.toContinuousLinearEquiv : F →L[ℝ] G).compLp f),
      ContinuousLinearMap.coeFn_compLp (L.toContinuousLinearEquiv : F →L[ℝ] G) f] with x h1 h2
    rw [h1, h2]; simp
  right_inv f := by
    refine Lp.ext ?_
    filter_upwards [ContinuousLinearMap.coeFn_compLp (L.toContinuousLinearEquiv : F →L[ℝ] G)
      ((L.symm.toContinuousLinearEquiv : G →L[ℝ] F).compLp f),
      ContinuousLinearMap.coeFn_compLp (L.symm.toContinuousLinearEquiv : G →L[ℝ] F) f] with x h1 h2
    rw [h1, h2]; simp
  norm_map' f := by
    have h1 : ‖(L.toContinuousLinearEquiv : F →L[ℝ] G).compLp f‖ ≤ ‖f‖ := by
      refine (ContinuousLinearMap.norm_compLp_le _ f).trans ?_
      have : ‖(L.toContinuousLinearEquiv : F →L[ℝ] G)‖ ≤ 1 := L.toLinearIsometry.norm_toContinuousLinearMap_le
      calc _ ≤ 1 * ‖f‖ := by gcongr
        _ = ‖f‖ := one_mul _
    have h2 : ‖f‖ ≤ ‖(L.toContinuousLinearEquiv : F →L[ℝ] G).compLp f‖ := by
      have := ContinuousLinearMap.norm_compLp_le (L.symm.toContinuousLinearEquiv : G →L[ℝ] F)
        ((L.toContinuousLinearEquiv : F →L[ℝ] G).compLp f)
      have h3 : ‖(L.symm.toContinuousLinearEquiv : G →L[ℝ] F)‖ ≤ 1 :=
        L.symm.toLinearIsometry.norm_toContinuousLinearMap_le
      have h4 : (L.symm.toContinuousLinearEquiv : G →L[ℝ] F).compLp
          ((L.toContinuousLinearEquiv : F →L[ℝ] G).compLp f) = f := by
        refine Lp.ext ?_
        filter_upwards [ContinuousLinearMap.coeFn_compLp (L.symm.toContinuousLinearEquiv : G →L[ℝ] F)
          ((L.toContinuousLinearEquiv : F →L[ℝ] G).compLp f),
          ContinuousLinearMap.coeFn_compLp (L.toContinuousLinearEquiv : F →L[ℝ] G) f] with x h1 h2
        rw [h1, h2]; simp
      rw [h4] at this
      calc _ ≤ _ := this
        _ ≤ 1 * ‖(L.toContinuousLinearEquiv : F →L[ℝ] G).compLp f‖ := by gcongr
        _ = _ := one_mul _
    exact le_antisymm h1 h2

theorem coeFn_lpCongr (L : F ≃ₗᵢ[ℝ] G) (f : Lp F 2 μ) :
    (lpCongr L f : α → G) =ᵐ[μ] fun x => L (f x) := by
  filter_upwards [ContinuousLinearMap.coeFn_compLp (L.toContinuousLinearEquiv : F →L[ℝ] G) f]
    with x hx
  exact hx

end LpCongr

/-- `L²Λ⁰(a,b) ≃ L²(a,b)`. -/
noncomputable def s0 : L2Form (Ioo a b) 0 ≃ₗᵢ[ℝ] L2I a b :=
  lpCongr cov0

/-- `L²Λ¹(a,b) ≃ L²(a,b)`, `g dx ↦ g`. -/
noncomputable def s1 : L2Form (Ioo a b) 1 ≃ₗᵢ[ℝ] L2I a b :=
  lpCongr cov1

theorem coeFn_s0 (u : L2Form (Ioo a b) 0) :
    (s0 u : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)] fun x => cov0 (u x) :=
  coeFn_lpCongr cov0 u

theorem coeFn_s1 (η : L2Form (Ioo a b) 1) :
    (s1 η : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)] fun x => cov1 (η x) :=
  coeFn_lpCongr cov1 η

/-! ### Test forms versus test functions -/

/-- Evaluation of a `1`-form on `ℝ` at the unit vector `1`. -/
noncomputable def ev1 : (ℝ [⋀^Fin 1]→L[ℝ] ℝ) →L[ℝ] ℝ :=
  ContinuousAlternatingMap.apply ℝ ℝ ℝ ![1]

@[simp] theorem ev1_apply (α : ℝ [⋀^Fin 1]→L[ℝ] ℝ) : ev1 α = α ![1] := rfl

/-- The `1`-form `dx` on `ℝ`. -/
noncomputable def dx : ℝ [⋀^Fin 1]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.ofSubsingleton ℝ ℝ ℝ (0 : Fin 1) (ContinuousLinearMap.id ℝ ℝ)

@[simp] theorem dx_apply : dx ![1] = 1 := by simp [dx]

/-- The scalar function attached to a `1`-form on `ℝ`. -/
theorem _root_.FEEC.IsTestForm.toTestFn {φ : ℝ → ℝ [⋀^Fin 1]→L[ℝ] ℝ} (hφ : IsTestForm (Ioo a b) φ) :
    IsTestFn a b (fun x => φ x ![1]) where
  contDiff := ev1.contDiff.comp hφ.contDiff
  hasCompactSupport := hφ.hasCompactSupport.comp_left (g := ev1) (map_zero _)
  tsupport_subset :=
    (tsupport_comp_subset (g := ev1) (map_zero _) φ).trans hφ.tsupport_subset

/-- A scalar test function times `dx` is a test `1`-form. -/
theorem IsTestFn.toTestForm {g : ℝ → ℝ} (hg : IsTestFn a b g) :
    IsTestForm (Ioo a b) (fun x => g x • dx) :=
  IsTestForm.smul_const hg.contDiff hg.hasCompactSupport hg.tsupport_subset dx

theorem cov0_codiff {φ : ℝ → ℝ [⋀^Fin 1]→L[ℝ] ℝ} (hφ : Differentiable ℝ φ) (x : ℝ) :
    cov0 (Covector.ofAlt (codiff φ x)) = -deriv (fun y => φ y ![1]) x := by
  have hd : deriv (fun y => φ y ![1]) x = fderiv ℝ φ x 1 ![1] := by
    have : HasDerivAt (fun y => φ y ![1]) (fderiv ℝ φ x 1 ![1]) x :=
      (ev1.hasFDerivAt.comp x (hφ x).hasFDerivAt).hasDerivAt
    exact this.deriv
  rw [hd, cov0_apply, Covector.toAlt_ofAlt, codiff_apply]
  simp only [ContinuousAlternatingMap.neg_apply, ContinuousAlternatingMap.sum_apply,
    ContinuousAlternatingMap.curryLeft_apply_apply]
  congr 1
  rw [Finset.sum_eq_single default]
  · have key : ∀ c : ℝ, (fderiv ℝ φ x c) (Matrix.vecCons c ![]) = c * c * fderiv ℝ φ x 1 ![1] := by
      intro c
      have : fderiv ℝ φ x c = c • fderiv ℝ φ x 1 := by
        conv_lhs => rw [show c = c • (1 : ℝ) by simp, map_smul]
      rw [this, ContinuousAlternatingMap.smul_apply, alt1_apply (fderiv ℝ φ x 1) (Matrix.vecCons c ![])]
      simp [mul_assoc]
    rw [key]
    rcases stdBasis_real (default : Fin (Module.finrank ℝ ℝ)) with h | h <;> simp [h]
  · intro i _ hi; exact absurd (Subsingleton.elim _ _) hi
  · simp

theorem inner_toLp_one (η : L2Form (Ioo a b) 1) {φ : ℝ → ℝ [⋀^Fin 1]→L[ℝ] ℝ}
    (hφ : IsTestForm (Ioo a b) φ) :
    inner ℝ η hφ.toLp = ∫ x in Ioo a b, (s1 η : ℝ → ℝ) x * φ x ![1] := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hφ.coeFn_toLp, coeFn_s1 η] with x h1 h2
  rw [h1, h2, ← cov1.inner_map_map, cov1_apply (Covector.ofAlt (φ x)), Covector.toAlt_ofAlt]
  simp [mul_comm]

theorem inner_codiff_toLp (u : L2Form (Ioo a b) 0) {φ : ℝ → ℝ [⋀^Fin 1]→L[ℝ] ℝ}
    (hφ : IsTestForm (Ioo a b) φ) :
    inner ℝ u hφ.codiff.toLp =
      -∫ x in Ioo a b, (s0 u : ℝ → ℝ) x * deriv (fun y => φ y ![1]) x := by
  have hd : Differentiable ℝ φ :=
    (hφ.contDiff.differentiable (by simp))
  rw [MeasureTheory.L2.inner_def, ← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards [hφ.codiff.coeFn_toLp, coeFn_s0 u] with x h1 h2
  rw [h1, h2, ← cov0.inner_map_map, cov0_codiff hd]
  simp [mul_comm]

/-- **In one dimension the weak exterior derivative of a `0`-form is the weak derivative.** -/
theorem hasWeakExtDeriv_iff (u : L2Form (Ioo a b) 0) (η : L2Form (Ioo a b) 1) :
    HasWeakExtDeriv u η ↔ HasWeakDeriv (s0 u) (s1 η) := by
  constructor
  · intro h ψ hψ
    have := h _ hψ.toTestForm
    rw [inner_toLp_one η hψ.toTestForm, inner_codiff_toLp u hψ.toTestForm] at this
    simpa using this
  · intro h φ hφ
    have := h _ hφ.toTestFn
    rw [inner_toLp_one η hφ, inner_codiff_toLp u hφ]
    exact this

/-- There are no nonzero `L²` forms of degree `≥ 2` on an interval. -/
instance (k : ℕ) : Subsingleton (L2Form (Ioo a b) (k + 2)) :=
  ⟨fun _ _ => Lp.ext (Filter.Eventually.of_forall fun _ => Subsingleton.elim _ _)⟩

/-- Every `L²` `1`-form on an interval has weak exterior derivative `0`. -/
theorem hasWeakExtDeriv_zero (η : L2Form (Ioo a b) 1) : HasWeakExtDeriv η 0 := by
  intro φ hφ
  haveI : Subsingleton (ℝ [⋀^Fin 2]→L[ℝ] ℝ) := Covector.ofAlt.toEquiv.subsingleton
  have h0 : φ = 0 := funext fun x => Subsingleton.elim _ _
  have h1 : codiff φ = 0 := by
    rw [h0]; ext1 x; simp [codiff_eq]
  rw [hφ.codiff.toLp_eq_zero h1, inner_zero_left, inner_zero_right]

end FEEC.Interval
