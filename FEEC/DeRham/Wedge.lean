/-
Exterior multiplication by a covector.
-/
import FEEC.DeRham.Codifferential

/-!
# Exterior multiplication by a covector

For `e : E`, `wedgeLeft e α` is the exterior product `e♭ ∧ α` of the covector `⟪e, ·⟫` with the
alternating form `α`:
`(e♭ ∧ α)(v₀, …, v_k) = ∑ᵢ (-1)ⁱ ⟪e, vᵢ⟫ α(v₀, …, v̂ᵢ, …, v_k)`.

## Main results

* `FEEC.curryLeft_wedgeLeft`: the anticommutation relation
  `u ⌟ (e♭ ∧ α) = ⟪e, u⟫ α - e♭ ∧ (u ⌟ α)`.
* `FEEC.tangPart`: `α - e♭ ∧ (e ⌟ α)`, the part of `α` not involving `e`.
* `FEEC.eq_zero_of_curryLeft_basis`: a form of positive degree annihilated by contraction with
  every vector of a basis is zero.
-/

namespace FEEC

open Module

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {k : ℕ}

/-- Exterior multiplication `α ↦ e♭ ∧ α` by the covector `⟪e, ·⟫`. -/
noncomputable def wedgeLeft (e : E) :
    (E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] (E [⋀^Fin (k + 1)]→L[ℝ] ℝ) :=
  (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℝ).comp
    (ContinuousLinearMap.smulRightL ℝ E (E [⋀^Fin k]→L[ℝ] ℝ) (innerSL ℝ e))

theorem wedgeLeft_apply (e : E) (α : E [⋀^Fin k]→L[ℝ] ℝ) (v : Fin (k + 1) → E) :
    wedgeLeft e α v = ∑ i : Fin (k + 1), (-1 : ℝ) ^ (i : ℕ) * (⟪e, v i⟫ * α (i.removeNth v)) := by
  simp [wedgeLeft, ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply,
    ContinuousAlternatingMap.alternatizeUncurryFin_apply]

theorem removeNth_succ_vecCons (u : E) (v : Fin (k + 1) → E) (j : Fin (k + 1)) :
    j.succ.removeNth (Matrix.vecCons u v) = Matrix.vecCons u (j.removeNth v) :=
  Fin.cons_comp_succ_succAbove u v j

/-- Anticommutation of contraction and exterior multiplication, in degree `0`. -/
theorem curryLeft_wedgeLeft_zero (u e : E) (α : E [⋀^Fin 0]→L[ℝ] ℝ) :
    (wedgeLeft e α).curryLeft u = ⟪e, u⟫ • α := by
  ext v
  simp [wedgeLeft_apply, Fin.sum_univ_succ, ContinuousAlternatingMap.curryLeft_apply_apply]

/-- Anticommutation of contraction and exterior multiplication:
`u ⌟ (e♭ ∧ α) = ⟪e, u⟫ α - e♭ ∧ (u ⌟ α)`. -/
theorem curryLeft_wedgeLeft (u e : E) (α : E [⋀^Fin (k + 1)]→L[ℝ] ℝ) :
    (wedgeLeft e α).curryLeft u = ⟪e, u⟫ • α - wedgeLeft e (α.curryLeft u) := by
  ext v
  rw [ContinuousAlternatingMap.curryLeft_apply_apply, wedgeLeft_apply, Fin.sum_univ_succ]
  simp only [ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.smul_apply,
    wedgeLeft_apply, ContinuousAlternatingMap.curryLeft_apply_apply, smul_eq_mul]
  simp only [Fin.val_zero, pow_zero, one_mul, Fin.removeNth_zero, Matrix.cons_val_zero,
    Fin.val_succ, removeNth_succ_vecCons, Fin.tail, Matrix.tail_cons]
  simp [pow_succ, Finset.sum_neg_distrib, sub_eq_add_neg]

/-- Contracting twice with the same vector gives zero. -/
theorem curryLeft_curryLeft_self (α : E [⋀^Fin (k + 2)]→L[ℝ] ℝ) (u : E) :
    (α.curryLeft u).curryLeft u = 0 := by
  have h := curryLeft_curryLeft_swap α u u
  have h2 : (α.curryLeft u).curryLeft u + (α.curryLeft u).curryLeft u = 0 := by
    nth_rewrite 2 [h]; simp
  have : (2 : ℝ) • (α.curryLeft u).curryLeft u = 0 := by rw [two_smul]; exact h2
  exact (smul_eq_zero.mp this).resolve_left two_ne_zero

/-- The part of `α` not involving `e`: `α - e♭ ∧ (e ⌟ α)`. -/
noncomputable def tangPart (e : E) :
    (E [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] (E [⋀^Fin (k + 1)]→L[ℝ] ℝ) :=
  ContinuousLinearMap.id ℝ _ - (wedgeLeft e).comp
    ((ContinuousLinearMap.apply ℝ (E [⋀^Fin k]→L[ℝ] ℝ) e).comp
      (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := E) (F := ℝ)
        (n := k)).toContinuousLinearMap)

theorem tangPart_apply (e : E) (α : E [⋀^Fin (k + 1)]→L[ℝ] ℝ) :
    tangPart e α = α - wedgeLeft e (α.curryLeft e) := by
  simp [tangPart]

theorem curryLeft_sub' (a b : E [⋀^Fin (k + 1)]→L[ℝ] ℝ) (u : E) :
    (a - b).curryLeft u = a.curryLeft u - b.curryLeft u := by
  ext v; simp [ContinuousAlternatingMap.curryLeft_apply_apply]

theorem curryLeft_tangPart_self {e : E} (he : ‖e‖ = 1) (α : E [⋀^Fin (k + 1)]→L[ℝ] ℝ) :
    (tangPart e α).curryLeft e = 0 := by
  have hee : ⟪e, e⟫ = 1 := by simp [real_inner_self_eq_norm_sq, he]
  rw [tangPart_apply, curryLeft_sub']
  cases k with
  | zero =>
    rw [curryLeft_wedgeLeft_zero, hee, one_smul, sub_self]
  | succ k =>
    rw [curryLeft_wedgeLeft, hee, one_smul, curryLeft_curryLeft_self, map_zero, sub_zero, sub_self]

theorem curryLeft_tangPart_of_orthogonal {e u : E} (h : ⟪e, u⟫ = 0)
    {α : E [⋀^Fin (k + 1)]→L[ℝ] ℝ} (hα : α.curryLeft u = 0) :
    (tangPart e α).curryLeft u = 0 := by
  rw [tangPart_apply, curryLeft_sub', hα]
  cases k with
  | zero =>
    rw [curryLeft_wedgeLeft_zero, h]; simp
  | succ k =>
    have h2 : (α.curryLeft e).curryLeft u = 0 := by
      rw [curryLeft_curryLeft_swap, hα]; simp
    rw [curryLeft_wedgeLeft, h2, h]; simp

/-- A form of positive degree annihilated by contraction with every vector of a basis is
zero. -/
theorem eq_zero_of_curryLeft_basis {ι : Type*} (b : Basis ι ℝ E)
    (α : E [⋀^Fin (k + 1)]→L[ℝ] ℝ) (h : ∀ i, α.curryLeft (b i) = 0) : α = 0 := by
  have hc : (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := E) (F := ℝ) (n := k) α :
      E →L[ℝ] (E [⋀^Fin k]→L[ℝ] ℝ)) = 0 := by
    apply ContinuousLinearMap.coe_injective
    apply b.ext
    intro i
    exact h i
  ext v
  have := congrArg (fun f => f (v 0)) hc
  have h3 := congrArg (fun a => a (Fin.tail v)) this
  have h5 := ContinuousAlternatingMap.curryLeft_apply_apply (α) (v 0) (Fin.tail v)
  simp only [ContinuousLinearMap.zero_apply] at h3
  have h4 : (Matrix.vecCons (v 0) (Fin.tail v) : Fin (k + 1) → E) = v := Fin.cons_self_tail v
  rw [h4] at h5
  rw [ContinuousAlternatingMap.coe_zero, Pi.zero_apply]
  rw [← h5]; exact h3

end FEEC
