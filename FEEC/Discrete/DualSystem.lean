/-
Cochain projections from dual systems.
-/
import FEEC.Discrete.Complex

/-!
# Cochain projections from dual systems

Let `C` be a Hilbert complex with spaces `V k ⊆ W k`. Given finite families `Λ k j ∈ V k`
("shape functions") and `Ψ k j ∈ W k` ("dual functions") and scalars `c k`, consider

`P k u = c k • ∑ j, ⟪Ψ k j, ι u⟫ • Λ k j`.

Under four algebraic conditions (`FEEC.HilbertComplex.IsDualSystem`) the spans of the `Λ k j`
form a subcomplex and `P` is a cochain projection onto it, bounded in the `V`-norm by the
`W`-operator norms of `w ↦ c k • ∑ j, ⟪Ψ k j, w⟫ • ι (Λ k j)`.
-/

namespace FEEC

namespace HilbertComplex

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {W V : ℕ → Type*}
  [∀ k, NormedAddCommGroup (W k)] [∀ k, InnerProductSpace ℝ (W k)]
  [∀ k, NormedAddCommGroup (V k)] [∀ k, InnerProductSpace ℝ (V k)]
  (C : HilbertComplex W V)
  {J : ℕ → Type*} [∀ k, Fintype (J k)]
  (Λ : ∀ k, J k → V k) (Ψ : ∀ k, J k → W k) (c : ℕ → ℝ)

/-- The operator `P k u = c k • ∑ j, ⟪Ψ k j, ι u⟫ • Λ k j` on `V k`. -/
noncomputable def dualProj (k : ℕ) : V k →L[ℝ] V k :=
  c k • ∑ j, ((innerSL ℝ (Ψ k j)).comp (C.ι k)).smulRight (Λ k j)

/-- The operator `w ↦ c k • ∑ j, ⟪Ψ k j, w⟫ • ι (Λ k j)` on `W k`. -/
noncomputable def dualOp (k : ℕ) : W k →L[ℝ] W k :=
  c k • ∑ j, (innerSL ℝ (Ψ k j)).smulRight (C.ι k (Λ k j))

theorem dualProj_apply (k : ℕ) (u : V k) :
    C.dualProj Λ Ψ c k u = c k • ∑ j, ⟪Ψ k j, C.ι k u⟫ • Λ k j := by
  simp [dualProj]

theorem dualOp_apply (k : ℕ) (w : W k) :
    C.dualOp Λ Ψ c k w = c k • ∑ j, ⟪Ψ k j, w⟫ • C.ι k (Λ k j) := by
  simp [dualOp]

theorem ι_dualProj (k : ℕ) (u : V k) :
    C.ι k (C.dualProj Λ Ψ c k u) = C.dualOp Λ Ψ c k (C.ι k u) := by
  rw [dualProj_apply, dualOp_apply, map_smul, map_sum]
  simp only [map_smul]

/-- The conditions making `dualProj` a cochain projection onto the span of the `Λ k j`. -/
structure IsDualSystem : Prop where
  proj_shape : ∀ k j, C.dualProj Λ Ψ c k (Λ k j) = Λ k j
  proj_dual : ∀ k j u, ⟪Ψ k j, C.ι k (C.dualProj Λ Ψ c k u)⟫ = ⟪Ψ k j, C.ι k u⟫
  d_shape : ∀ k j, C.d k (Λ k j) ∈ Submodule.span ℝ (Set.range (Λ (k + 1)))
  d_dual : ∀ k (j : J (k + 1)), ∃ γ : J k → ℝ, ∀ u : V k,
    ⟪Ψ (k + 1) j, C.ι (k + 1) (C.d k u)⟫ = ∑ l, γ l * ⟪Ψ k l, C.ι k u⟫

/-- The subcomplex spanned by the shape functions. -/
def dualSubcomplex
    (h : ∀ k j, C.d k (Λ k j) ∈ Submodule.span ℝ (Set.range (Λ (k + 1)))) : C.Subcomplex where
  carrier k := Submodule.span ℝ (Set.range (Λ k))
  map_d k u hu := by
    have : Submodule.span ℝ (Set.range (Λ k)) ≤
        (Submodule.span ℝ (Set.range (Λ (k + 1)))).comap (C.d k : V k →ₗ[ℝ] V (k + 1)) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact h k j
    exact this hu

instance (h : ∀ k j, C.d k (Λ k j) ∈ Submodule.span ℝ (Set.range (Λ (k + 1)))) (k : ℕ) :
    FiniteDimensional ℝ ((C.dualSubcomplex Λ h).carrier k) := by
  show FiniteDimensional ℝ (Submodule.span ℝ (Set.range (Λ k)))
  exact FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

instance (h : ∀ k j, C.d k (Λ k j) ∈ Submodule.span ℝ (Set.range (Λ (k + 1)))) (k : ℕ) :
    CompleteSpace ((C.dualSubcomplex Λ h).carrier k) :=
  FiniteDimensional.complete ℝ _

variable {C Λ Ψ c}

theorem IsDualSystem.proj_span (h : C.IsDualSystem Λ Ψ c) (k : ℕ) {u : V k}
    (hu : u ∈ Submodule.span ℝ (Set.range (Λ k))) : C.dualProj Λ Ψ c k u = u := by
  induction hu using Submodule.span_induction with
  | mem x hx => obtain ⟨j, rfl⟩ := hx; exact h.proj_shape k j
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul a x _ hx => rw [map_smul, hx]

theorem dualProj_mem_span (k : ℕ) (u : V k) :
    C.dualProj Λ Ψ c k u ∈ Submodule.span ℝ (Set.range (Λ k)) := by
  rw [dualProj_apply]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_)
  exact Submodule.subset_span ⟨j, rfl⟩

theorem IsDualSystem.d_span (h : C.IsDualSystem Λ Ψ c) (k : ℕ) {u : V k}
    (hu : u ∈ Submodule.span ℝ (Set.range (Λ k))) :
    C.d k u ∈ Submodule.span ℝ (Set.range (Λ (k + 1))) :=
  (C.dualSubcomplex Λ h.d_shape).map_d k u hu

theorem IsDualSystem.comm (h : C.IsDualSystem Λ Ψ c) (k : ℕ) (u : V k) :
    C.dualProj Λ Ψ c (k + 1) (C.d k u) = C.d k (C.dualProj Λ Ψ c k u) := by
  have hc : C.dualProj Λ Ψ c (k + 1) (C.d k (C.dualProj Λ Ψ c k u)) =
      C.d k (C.dualProj Λ Ψ c k u) :=
    h.proj_span (k + 1) (h.d_span k (dualProj_mem_span k u))
  refine Eq.trans ?_ hc
  rw [C.dualProj_apply Λ Ψ c (k + 1) (C.d k u),
    C.dualProj_apply Λ Ψ c (k + 1) (C.d k (C.dualProj Λ Ψ c k u))]
  refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
  obtain ⟨γ, hγ⟩ := h.d_dual k j
  rw [hγ, hγ]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [h.proj_dual]

/-- The cochain projection of a dual system. -/
noncomputable def IsDualSystem.cochainProjection (h : C.IsDualSystem Λ Ψ c) :
    C.CochainProjection (C.dualSubcomplex Λ h.d_shape) where
  π := C.dualProj Λ Ψ c
  π_mem k u := dualProj_mem_span k u
  π_id k u hu := h.proj_span k hu
  comm := h.comm

/-- The `V`-norm of the cochain projection is bounded by the `W`-norms of `dualOp`. -/
theorem IsDualSystem.norm_dualProj_le (h : C.IsDualSystem Λ Ψ c) {K : ℕ → ℝ}
    (hK0 : ∀ k, 0 ≤ K k) (hK : ∀ k w, ‖C.dualOp Λ Ψ c k w‖ ≤ K k * ‖w‖) (k : ℕ) :
    ‖C.dualProj Λ Ψ c k‖ ≤ max (K k) (K (k + 1)) := by
  have hM : 0 ≤ max (K k) (K (k + 1)) := le_max_of_le_left (hK0 k)
  refine ContinuousLinearMap.opNorm_le_bound _ hM fun u => ?_
  have h1 := C.inner_eq k (C.dualProj Λ Ψ c k u) (C.dualProj Λ Ψ c k u)
  have h2 := C.inner_eq k u u
  simp only [real_inner_self_eq_norm_sq] at h1 h2
  have e1 : ‖C.ι k (C.dualProj Λ Ψ c k u)‖ ≤ K k * ‖C.ι k u‖ := by
    rw [ι_dualProj]; exact hK k _
  have e2 : ‖C.ι (k + 1) (C.d k (C.dualProj Λ Ψ c k u))‖ ≤
      K (k + 1) * ‖C.ι (k + 1) (C.d k u)‖ := by
    rw [← h.comm, ι_dualProj]; exact hK _ _
  have m1 : K k ≤ max (K k) (K (k + 1)) := le_max_left _ _
  have m2 : K (k + 1) ≤ max (K k) (K (k + 1)) := le_max_right _ _
  have f1 := e1.trans (mul_le_mul_of_nonneg_right m1 (norm_nonneg _))
  have f2 := e2.trans (mul_le_mul_of_nonneg_right m2 (norm_nonneg _))
  have g1 := pow_le_pow_left₀ (norm_nonneg _) f1 2
  have g2 := pow_le_pow_left₀ (norm_nonneg _) f2 2
  rw [mul_pow] at g1 g2
  have : ‖C.dualProj Λ Ψ c k u‖ ^ 2 ≤ (max (K k) (K (k + 1)) * ‖u‖) ^ 2 := by
    rw [mul_pow]
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg _)) two_ne_zero).1 this

end HilbertComplex

end FEEC
