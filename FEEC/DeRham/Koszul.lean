/-
The Koszul operator on differential forms and the homotopy formula.
-/
import Mathlib

/-!
# The Koszul operator

A differential `k`-form on a normed space `E` is a map `ω : E → E [⋀^Fin k]→L[ℝ] ℝ`, and
Mathlib provides the exterior derivative `extDeriv`. The *Koszul operator* `κ` contracts a
form with the identity (radial) vector field:
`(κ ω)ₓ(v₁, …, v_k) = ωₓ(x, v₁, …, v_k)` (Arnold, §7.2).

## Main results

* `FEEC.koszul_koszul`: `κ ∘ κ = 0`.
* `FEEC.extDeriv_koszul_add_koszul_extDeriv`: the homotopy formula
  `(dκ + κd) ω = (k+1) • ω + Dω(x) x` for a `(k+1)`-form (this is the Lie derivative of `ω`
  along the radial vector field).
-/

namespace FEEC

open ContinuousAlternatingMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ}

/-- The Koszul operator: contraction of a `(k+1)`-form with the radial vector field `x ↦ x`. -/
noncomputable def koszul (ω : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ) : E → E [⋀^Fin k]→L[ℝ] ℝ :=
  fun x => (ω x).curryLeft x

theorem koszul_apply (ω : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ) (x : E) :
    koszul ω x = (ω x).curryLeft x := rfl

theorem koszul_apply_apply (ω : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ) (x : E) (v : Fin k → E) :
    koszul ω x v = ω x (Matrix.vecCons x v) := rfl

@[simp] theorem koszul_zero : koszul (0 : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ) = 0 := by
  funext x; ext v; simp [koszul_apply_apply]

theorem koszul_add (ω η : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ) :
    koszul (ω + η) = koszul ω + koszul η := by
  funext x; ext v; simp [koszul_apply_apply]

theorem koszul_smul (c : ℝ) (ω : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ) :
    koszul (c • ω) = c • koszul ω := by
  funext x; ext v; simp [koszul_apply_apply]

theorem koszul_sum {ι : Type*} (s : Finset ι) (ω : ι → E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ) :
    koszul (∑ i ∈ s, ω i) = ∑ i ∈ s, koszul (ω i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, koszul_add, ih]

/-- The Koszul operator as a linear map. -/
noncomputable def koszulₗ :
    (E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ) →ₗ[ℝ] (E → E [⋀^Fin k]→L[ℝ] ℝ) where
  toFun := koszul
  map_add' := koszul_add
  map_smul' := koszul_smul

@[simp] theorem koszulₗ_apply (ω : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ) : koszulₗ ω = koszul ω := rfl

/-- `κ ∘ κ = 0`. -/
theorem koszul_koszul (ω : E → E [⋀^Fin (k + 2)]→L[ℝ] ℝ) : koszul (koszul ω) = 0 := by
  funext x; exact curryLeft_same (ω x) x

/-- `curryLeft` as a continuous linear map. -/
private noncomputable abbrev curryL (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℕ) :
    (E [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E [⋀^Fin k]→L[ℝ] ℝ) :=
  (curryLeftLI (𝕜 := ℝ) (E := E) (F := ℝ) (n := k)).toContinuousLinearMap

private theorem koszul_eq_clm (ω : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ) :
    koszul ω = fun x => (curryL E k (ω x)) x := rfl

theorem _root_.ContDiff.koszul {n : WithTop ℕ∞} {ω : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ}
    (h : ContDiff ℝ n ω) : ContDiff ℝ n (FEEC.koszul ω) := by
  rw [FEEC.koszul_eq_clm]
  exact ((curryL E k).contDiff.comp h).clm_apply contDiff_id

theorem _root_.DifferentiableAt.koszul {ω : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ} {x : E}
    (h : DifferentiableAt ℝ ω x) : DifferentiableAt ℝ (FEEC.koszul ω) x := by
  rw [FEEC.koszul_eq_clm]
  exact ((curryL E k).differentiableAt.comp x h).clm_apply differentiableAt_id

/-- The derivative of `κ ω`: the product rule for the bilinear map `curryLeft`. -/
theorem fderiv_koszul_apply {ω : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ} {x : E}
    (h : DifferentiableAt ℝ ω x) (w : E) :
    fderiv ℝ (koszul ω) x w = (fderiv ℝ ω x w).curryLeft x + (ω x).curryLeft w := by
  rw [koszul_eq_clm]
  have hc : HasFDerivAt (fun y => curryL E k (ω y)) ((curryL E k).comp (fderiv ℝ ω x)) x :=
    (curryL E k).hasFDerivAt.comp x h.hasFDerivAt
  have h2 : fderiv ℝ (fun y => (curryL E k (ω y)) y) x = _ :=
    (hc.clm_apply (hasFDerivAt_id x)).fderiv
  rw [h2]
  simp [add_comm]

theorem sum_neg_one_pow_smul_map_cons_removeNth (f : E [⋀^Fin (k + 1)]→L[ℝ] ℝ)
    (v : Fin (k + 1) → E) :
    ∑ i : Fin (k + 1), (-1 : ℝ) ^ (i : ℕ) • f (Matrix.vecCons (v i) (i.removeNth v)) =
      ((k : ℝ) + 1) • f v := by
  have h : ∀ i : Fin (k + 1), (-1 : ℝ) ^ (i : ℕ) • f (Matrix.vecCons (v i) (i.removeNth v)) =
      f v := by
    intro i
    have := f.neg_one_pow_smul_map_insertNth i (v i) (i.removeNth v)
    rw [Fin.insertNth_self_removeNth] at this
    rw [← this]
    simp [← mul_assoc, ← mul_pow]
  rw [Finset.sum_congr rfl (fun i _ => h i)]
  simp [Finset.sum_const]

theorem removeNth_succ_cons (x : E) (v : Fin (k + 1) → E) (i : Fin (k + 1)) :
    i.succ.removeNth (Matrix.vecCons x v) = Matrix.vecCons x (i.removeNth v) := by
  ext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [Fin.removeNth]
  · simp [Fin.removeNth]

theorem extDeriv_koszul_add_koszul_extDeriv {ω : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ} {x : E}
    (h : DifferentiableAt ℝ ω x) :
    extDeriv (koszul ω) x + koszul (extDeriv ω) x = ((k : ℝ) + 1) • ω x + fderiv ℝ ω x x := by
  ext v
  have hk := h.koszul
  have e1 : extDeriv (koszul ω) x v = ∑ i : Fin (k + 1), (-1 : ℝ) ^ (i : ℕ) •
      ((fderiv ℝ ω x (v i)) (Matrix.vecCons x (i.removeNth v)) +
        ω x (Matrix.vecCons (v i) (i.removeNth v))) := by
    rw [extDeriv_apply hk]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [fderiv_continuousAlternatingMap_apply_const_apply hk, fderiv_koszul_apply h]
    rfl
  have e2 : koszul (extDeriv ω) x v = fderiv ℝ ω x x v - ∑ i : Fin (k + 1), (-1 : ℝ) ^ (i : ℕ) •
      (fderiv ℝ ω x (v i)) (Matrix.vecCons x (i.removeNth v)) := by
    rw [koszul_apply_apply, extDeriv_apply h, Fin.sum_univ_succ]
    simp only [fderiv_continuousAlternatingMap_apply_const_apply h, Fin.val_zero, pow_zero,
      one_smul, Fin.val_succ, Fin.removeNth_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.tail_cons, removeNth_succ_cons, pow_succ, mul_neg, mul_one, neg_smul,
      Finset.sum_neg_distrib, sub_eq_add_neg]
    rfl
  rw [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.smul_apply, e1, e2]
  simp only [smul_add, Finset.sum_add_distrib, sum_neg_one_pow_smul_map_cons_removeNth]
  simp only [smul_eq_mul]
  ring

/-- The homotopy formula in degree `0`: `(κ d f)ₓ = Df(x) x`. -/
theorem koszul_extDeriv_zero {f : E → E [⋀^Fin 0]→L[ℝ] ℝ} {x : E}
    (h : DifferentiableAt ℝ f x) : koszul (extDeriv f) x = fderiv ℝ f x x := by
  ext v
  rw [koszul_apply_apply, extDeriv_apply h]
  simp [Fin.sum_univ_succ, fderiv_continuousAlternatingMap_apply_const_apply h]

end FEEC
