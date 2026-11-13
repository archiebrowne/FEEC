/-
Lifting a projection through a surjective operator.
-/
import Mathlib

/-!
# Lifting a projection through a surjective operator

Let `T : X → Y` be a bounded surjective operator between Hilbert spaces and `Q : Y → Y` a
bounded operator (in applications a projection onto a discrete subspace `Yh`). Then
`P = P_{ker T} + R ∘ Q ∘ T`, where `R : Y → (ker T)ᗮ` is the bounded inverse of `T` on
`(ker T)ᗮ`, is a bounded operator on `X` with `T ∘ P = Q ∘ T` which fixes every `x` with
`Q (T x) = T x`.

With `T = d` this constructs a bounded cochain projection one degree down from a given one,
onto `d⁻¹(Yh)`, whenever `d` is surjective. Its norm is controlled by the Poincaré constant.
-/

namespace FEEC

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

section aux

variable (T : X →L[ℝ] Y)

lemma T_starProjection_ker (x : X) :
    T ((LinearMap.ker (T : X →ₗ[ℝ] Y)).starProjection x) = 0 :=
  (LinearMap.mem_ker (f := (T : X →ₗ[ℝ] Y))).1
    (Submodule.starProjection_apply_mem (LinearMap.ker (T : X →ₗ[ℝ] Y)) x)

/-- `T` restricted to `(ker T)ᗮ` is an isomorphism onto `Y` when `T` is surjective. -/
noncomputable def liftEquiv (hT : Function.Surjective T) :
    (LinearMap.ker (T : X →ₗ[ℝ] Y))ᗮ ≃L[ℝ] Y :=
  ContinuousLinearEquiv.ofBijective
    (T ∘L (LinearMap.ker (T : X →ₗ[ℝ] Y))ᗮ.subtypeL)
    (by
      rw [LinearMap.ker_eq_bot', ]
      intro x hx
      have h1 : (x : X) ∈ LinearMap.ker (T : X →ₗ[ℝ] Y) := by
        simpa using hx
      have h2 : (x : X) ∈ (LinearMap.ker (T : X →ₗ[ℝ] Y))ᗮ := x.2
      have : (x : X) = 0 := by
        have := Submodule.inner_right_of_mem_orthogonal h1 h2
        exact inner_self_eq_zero.1 this
      exact Subtype.ext this)
    (by
      rw [LinearMap.range_eq_top]
      intro y
      obtain ⟨x, rfl⟩ := hT y
      refine ⟨⟨x - (LinearMap.ker (T : X →ₗ[ℝ] Y)).starProjection x,
        Submodule.sub_starProjection_mem_orthogonal x⟩, ?_⟩
      simp [T_starProjection_ker])

lemma T_liftEquiv_symm (hT : Function.Surjective T) (y : Y) :
    T ((liftEquiv T hT).symm y : X) = y := by
  have := (liftEquiv T hT).apply_symm_apply y
  exact this

lemma liftEquiv_symm_T (hT : Function.Surjective T) (x : X) :
    ((liftEquiv T hT).symm (T x) : X) =
      x - (LinearMap.ker (T : X →ₗ[ℝ] Y)).starProjection x := by
  have hm := Submodule.sub_starProjection_mem_orthogonal (K := LinearMap.ker (T : X →ₗ[ℝ] Y)) x
  have : (liftEquiv T hT).symm (T x) = ⟨_, hm⟩ := by
    rw [ContinuousLinearEquiv.symm_apply_eq]
    simp [liftEquiv, T_starProjection_ker]
  rw [this]

end aux

/-- The lift `P_{ker T} + R ∘ Q ∘ T` of `Q : Y → Y` through the surjective operator
`T : X → Y`. -/
noncomputable def liftProjection (T : X →L[ℝ] Y) (hT : Function.Surjective T)
    (Q : Y →L[ℝ] Y) : X →L[ℝ] X :=
  (LinearMap.ker (T : X →ₗ[ℝ] Y)).starProjection +
    (LinearMap.ker (T : X →ₗ[ℝ] Y))ᗮ.subtypeL ∘L
      ((liftEquiv T hT).symm : Y →L[ℝ] _) ∘L Q ∘L T

variable (T : X →L[ℝ] Y) (hT : Function.Surjective T) (Q : Y →L[ℝ] Y)

lemma liftProjection_apply (x : X) : liftProjection T hT Q x =
    (LinearMap.ker (T : X →ₗ[ℝ] Y)).starProjection x +
      ((liftEquiv T hT).symm (Q (T x)) : X) := rfl

theorem map_liftProjection (x : X) : T (liftProjection T hT Q x) = Q (T x) := by
  rw [liftProjection_apply, map_add, T_starProjection_ker, T_liftEquiv_symm, zero_add]

theorem liftProjection_eq_self {x : X} (hx : Q (T x) = T x) : liftProjection T hT Q x = x := by
  rw [liftProjection_apply, hx, liftEquiv_symm_T]
  abel

theorem sub_liftProjection_mem (x : X) :
    x - liftProjection T hT Q x ∈ (LinearMap.ker (T : X →ₗ[ℝ] Y))ᗮ := by
  rw [liftProjection_apply, ← sub_sub]
  exact Submodule.sub_mem _ (Submodule.sub_starProjection_mem_orthogonal x)
    ((liftEquiv T hT).symm (Q (T x))).2

theorem norm_liftProjection_le {c : ℝ}
    (hc : ∀ x ∈ (LinearMap.ker (T : X →ₗ[ℝ] Y))ᗮ, ‖x‖ ≤ c * ‖T x‖) :
    ‖liftProjection T hT Q‖ ≤ 1 + c * ‖Q‖ * ‖T‖ := by
  have hPK : ∀ x : X, ‖(LinearMap.ker (T : X →ₗ[ℝ] Y)).starProjection x‖ ≤ ‖x‖ :=
    Submodule.norm_starProjection_apply_le _
  by_cases hc0 : 0 ≤ c
  · have key : ∀ x : X, ‖liftProjection T hT Q x‖ ≤ (1 + c * ‖Q‖ * ‖T‖) * ‖x‖ := by
      intro x
      set e := (liftEquiv T hT).symm (Q (T x))
      have h1 : ‖(e : X)‖ ≤ c * ‖Q (T x)‖ := by
        have := hc (e : X) e.2
        rwa [T_liftEquiv_symm] at this
      have h2 : ‖Q (T x)‖ ≤ ‖Q‖ * ‖T‖ * ‖x‖ := by
        calc ‖Q (T x)‖ ≤ ‖Q‖ * ‖T x‖ := Q.le_opNorm _
          _ ≤ ‖Q‖ * (‖T‖ * ‖x‖) := by gcongr; exact T.le_opNorm _
          _ = _ := by ring
      rw [liftProjection_apply]
      calc _ ≤ ‖(LinearMap.ker (T : X →ₗ[ℝ] Y)).starProjection x‖ + ‖(e : X)‖ :=
            norm_add_le _ _
        _ ≤ ‖x‖ + c * (‖Q‖ * ‖T‖ * ‖x‖) := by
          have := mul_le_mul_of_nonneg_left h2 hc0
          linarith [hPK x]
        _ = _ := by ring
    exact ContinuousLinearMap.opNorm_le_bound _
      (by positivity) key
  · push_neg at hc0
    have hY : ∀ y : Y, y = 0 := by
      intro y
      have h := hc ((liftEquiv T hT).symm y : X) ((liftEquiv T hT).symm y).2
      rw [T_liftEquiv_symm] at h
      have h3 : c * ‖y‖ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc0.le (norm_nonneg _)
      have h4 : ‖y‖ ≤ 0 := by
        by_contra hy
        push_neg at hy
        have : c * ‖y‖ < 0 := mul_neg_of_neg_of_pos hc0 hy
        linarith [norm_nonneg ((liftEquiv T hT).symm y : X)]
      exact norm_le_zero_iff.1 h4
    have hQ : Q = 0 := by
      ext y; simp [hY y]
    have key : ∀ x : X, ‖liftProjection T hT Q x‖ ≤ 1 * ‖x‖ := by
      intro x
      rw [liftProjection_apply, hY (Q (T x))]
      simp only [map_zero, ZeroMemClass.coe_zero, add_zero, one_mul]
      exact hPK x
    have := ContinuousLinearMap.opNorm_le_bound _ (by norm_num) key
    simpa [hQ] using this

end FEEC
