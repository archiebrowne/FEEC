/-
Babuška–Nečas theorem for symmetric bounded bilinear forms on a Hilbert space.
-/
import Mathlib

/-!
# Well-posedness from a lower bound (Babuška–Nečas, symmetric case)

Let `X` be a real Hilbert space and `B : X →L[ℝ] X →L[ℝ] ℝ` a bounded symmetric bilinear
form. If `B` is bounded below, `‖x‖ ≤ K * ‖B x‖` (which is the inf-sup condition with
constant `K⁻¹`), then for every functional `F` there is a unique `x` with `B x = F`.
-/

namespace FEEC

local notation "⟪" x ", " y "⟫_ℝ" => inner ℝ x y

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

/-- **Babuška–Nečas theorem**, symmetric case: a bounded symmetric bilinear form on a Hilbert
space which is bounded below induces a bijection `X → X*`. -/
theorem existsUnique_of_symm_of_bounded_below (B : X →L[ℝ] X →L[ℝ] ℝ)
    (hsymm : ∀ x y, B x y = B y x) {K : ℝ} (hB : ∀ x, ‖x‖ ≤ K * ‖B x‖) (F : X →L[ℝ] ℝ) :
    ∃! x, B x = F := by
  classical
  set T : X →L[ℝ] X := InnerProductSpace.continuousLinearMapOfBilin B with hT
  have hTB : ∀ x y, ⟪T x, y⟫_ℝ = B x y := fun x y =>
    InnerProductSpace.continuousLinearMapOfBilin_apply B x y
  have hnorm : ∀ x, ‖T x‖ = ‖B x‖ := by
    intro x
    have : B x = (InnerProductSpace.toDual ℝ X) (T x) := by
      ext y; simp [hTB]
    rw [this, LinearIsometryEquiv.norm_map]
  have hanti : AntilipschitzWith (max K 0).toNNReal T := by
    refine ContinuousLinearMap.antilipschitz_of_bound T fun x => ?_
    rw [hnorm, Real.coe_toNNReal _ (le_max_right _ _)]
    exact (hB x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hker : ∀ x, T x = 0 → x = 0 := fun x hx => hanti.injective (by simpa using hx)
  have hrange : LinearMap.range (T : X →ₗ[ℝ] X) = ⊤ := by
    have hcl : IsClosed (LinearMap.range (T : X →ₗ[ℝ] X) : Set X) :=
      hanti.isClosed_range T.uniformContinuous
    have := hcl.completeSpace_coe
    rw [← (LinearMap.range (T : X →ₗ[ℝ] X)).orthogonal_orthogonal]
    rw [Submodule.eq_top_iff']
    intro v w hw
    have hw0 : w = 0 := by
      apply hker
      have h1 : ∀ x, ⟪T w, x⟫_ℝ = 0 := fun x => by
        rw [hTB, hsymm, ← hTB]; exact hw _ ⟨x, rfl⟩
      exact inner_self_eq_zero.1 (h1 _)
    simp [hw0]
  obtain ⟨x, hx⟩ : ∃ x, T x = (InnerProductSpace.toDual ℝ X).symm F := by
    have : (InnerProductSpace.toDual ℝ X).symm F ∈ LinearMap.range (T : X →ₗ[ℝ] X) := by
      rw [hrange]; trivial
    exact this
  have hxF : B x = F := by
    ext y
    rw [← hTB, hx]; simp
  refine ⟨x, hxF, fun y hy => ?_⟩
  have h0 : ‖y - x‖ ≤ 0 := by
    have : B (y - x) = 0 := by rw [map_sub, hy, hxF, sub_self]
    have := hB (y - x)
    rw [‹B (y - x) = 0›, norm_zero, mul_zero] at this
    exact this
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h0)

end FEEC
