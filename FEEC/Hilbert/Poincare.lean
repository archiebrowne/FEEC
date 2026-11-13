/-
The Poincaré inequality for short Hilbert complexes.
-/
import FEEC.Hilbert.ShortComplex

/-!
# The Poincaré inequality

For a short Hilbert complex `V₀ --d₀--> V₁ --d₁--> W₂` we say that `c` is a *Poincaré
constant* if `‖τ‖_V ≤ c ‖d₀ τ‖` for `τ ⟂ ker d₀` and `‖v‖_V ≤ c ‖d₁ v‖` for `v ⟂ ker d₁`.

## Main results

* `ShortHilbertComplex.exists_hasPoincareConst`: closed complexes have a Poincaré constant
  (Arnold, Theorem 4.6).
* `ShortHilbertComplex.HasPoincareConst.isClosed_coboundaries`
* `ShortHilbertComplex.HasPoincareConst.exists_potential`: bounded potentials for coboundaries.
-/

namespace FEEC

local notation "⟪" x ", " y "⟫" => inner ℝ x y

namespace ShortHilbertComplex

variable {W₀ W₁ W₂ V₀ V₁ : Type*}
  [NormedAddCommGroup W₀] [InnerProductSpace ℝ W₀]
  [NormedAddCommGroup W₁] [InnerProductSpace ℝ W₁]
  [NormedAddCommGroup W₂] [InnerProductSpace ℝ W₂]
  [NormedAddCommGroup V₀] [InnerProductSpace ℝ V₀]
  [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁]
  (S : ShortHilbertComplex W₀ W₁ W₂ V₀ V₁)

/-- `c` is a Poincaré constant for both differentials of the short complex `S`
(Arnold, eq. (4.5)): the `V`-norm is controlled by the norm of the differential on the
orthogonal complement of its kernel. -/
structure HasPoincareConst (c : ℝ) : Prop where
  nonneg : 0 ≤ c
  le₀ : ∀ τ ∈ S.cocycles₀ᗮ, ‖τ‖ ≤ c * ‖S.d₀ τ‖
  le₁ : ∀ v ∈ S.cocyclesᗮ, ‖v‖ ≤ c * ‖S.d₁ v‖

variable {S}

/-- If `g` is injective on a closed subspace `K` of a Banach space and `g '' K` is closed, then
`g` is bounded below on `K`. -/
theorem exists_bound_on_submodule {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (K : Submodule ℝ E) (hK : IsClosed (K : Set E)) (g : E →L[ℝ] F)
    (hinj : ∀ x ∈ K, g x = 0 → x = 0) (hrange : IsClosed (g '' (K : Set E))) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x ∈ K, ‖x‖ ≤ c * ‖g x‖ := by
  haveI := hK.completeSpace_coe
  let f : K →L[ℝ] F := g.comp K.subtypeL
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    exact Subtype.ext (hinj x x.2 hx)
  have hr : IsClosed (Set.range f) := by
    have : Set.range f = g '' (K : Set E) := by
      ext y; constructor
      · rintro ⟨x, rfl⟩; exact ⟨x, x.2, rfl⟩
      · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩
    rw [this]; exact hrange
  obtain ⟨c, hc⟩ := f.antilipschitz_of_injective_of_isClosed_range hf hr
  exact ⟨c, c.2, fun x hx => f.bound_of_antilipschitz hc ⟨x, hx⟩⟩

/-- Finite-dimensional version of `exists_bound_on_submodule`. -/
theorem exists_bound_on_submodule_of_finiteDimensional {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : Submodule ℝ E) (g : E →L[ℝ] F) (hinj : ∀ x ∈ K, g x = 0 → x = 0) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x ∈ K, ‖x‖ ≤ c * ‖g x‖ := by
  let f : K →ₗ[ℝ] F := (g : E →ₗ[ℝ] F).comp K.subtype
  have hker : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    exact Subtype.ext (hinj x x.2 hx)
  obtain ⟨c, -, hc⟩ := f.exists_antilipschitzWith hker
  refine ⟨c, c.2, fun x hx => ?_⟩
  have := hc.le_mul_dist (⟨x, hx⟩ : K) 0
  simpa [f, dist_eq_norm] using this

/-- To produce a Poincaré constant it suffices to bound both differentials on the orthogonal
complements of their kernels. -/
theorem exists_hasPoincareConst_of_bounds
    (h₀ : ∃ c : ℝ, 0 ≤ c ∧ ∀ τ ∈ S.cocycles₀ᗮ, ‖τ‖ ≤ c * ‖S.d₀ τ‖)
    (h₁ : ∃ c : ℝ, 0 ≤ c ∧ ∀ v ∈ S.cocyclesᗮ, ‖v‖ ≤ c * ‖S.d₁ v‖) :
    ∃ c, S.HasPoincareConst c := by
  obtain ⟨c₀, hc₀, H₀⟩ := h₀
  obtain ⟨c₁, hc₁, H₁⟩ := h₁
  refine ⟨max c₀ c₁, hc₀.trans (le_max_left _ _), fun τ hτ => (H₀ τ hτ).trans ?_,
    fun v hv => (H₁ v hv).trans ?_⟩
  · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)


theorem HasPoincareConst.mono {c c' : ℝ} (h : S.HasPoincareConst c) (hc : c ≤ c') :
    S.HasPoincareConst c' := by
  refine ⟨h.nonneg.trans hc, fun τ hτ => (h.le₀ τ hτ).trans ?_, fun v hv => (h.le₁ v hv).trans ?_⟩
  · exact mul_le_mul_of_nonneg_right hc (norm_nonneg _)
  · exact mul_le_mul_of_nonneg_right hc (norm_nonneg _)

section Complete

variable [CompleteSpace V₀] [CompleteSpace V₁]

variable (S) in
/-- Every `d₀ τ` has a preimage in `(ker d₀)ᗮ`. -/
theorem exists_mem_cocycles₀_orthogonal (τ : V₀) :
    ∃ ρ ∈ S.cocycles₀ᗮ, S.d₀ ρ = S.d₀ τ := by
  refine ⟨τ - S.cocycles₀.starProjection τ, Submodule.sub_starProjection_mem_orthogonal _, ?_⟩
  have : S.d₀ (S.cocycles₀.starProjection τ) = 0 :=
    S.mem_cocycles₀.1 (Submodule.starProjection_apply_mem _ _)
  rw [map_sub, this, sub_zero]

/-- Every coboundary has a potential bounded by the Poincaré constant. -/
theorem HasPoincareConst.exists_potential {c : ℝ} (h : S.HasPoincareConst c) {b : V₁}
    (hb : b ∈ S.coboundaries) : ∃ ρ : V₀, S.d₀ ρ = b ∧ ‖ρ‖ ≤ c * ‖b‖ := by
  obtain ⟨τ, rfl⟩ := hb
  obtain ⟨ρ, hρ, hd⟩ := S.exists_mem_cocycles₀_orthogonal τ
  exact ⟨ρ, hd, by have := h.le₀ ρ hρ; rw [hd] at this; exact this⟩

/-- If the Poincaré inequality holds, the coboundaries are closed. -/
theorem HasPoincareConst.isClosed_coboundaries {c : ℝ} (h : S.HasPoincareConst c) :
    IsClosed (S.coboundaries : Set V₁) := by
  have hK : IsClosed (S.cocycles₀ᗮ : Set V₀) := Submodule.isClosed_orthogonal _
  have hinj : ∀ x ∈ S.cocycles₀ᗮ, S.d₀ x = 0 → x = 0 := fun x hx hx0 => by
    have := h.le₀ x hx
    rw [hx0, norm_zero, mul_zero] at this
    exact norm_le_zero_iff.1 this
  have hr : IsClosed (S.d₀ '' (S.cocycles₀ᗮ : Set V₀)) := by
    have hK' := hK.completeSpace_coe
    let f : S.cocycles₀ᗮ →L[ℝ] V₁ := S.d₀.comp S.cocycles₀ᗮ.subtypeL
    have hanti : AntilipschitzWith c.toNNReal f :=
      ContinuousLinearMap.antilipschitz_of_bound f fun x => by
        rw [Real.coe_toNNReal _ h.nonneg]; exact h.le₀ x x.2
    have := hanti.isClosed_range f.uniformContinuous
    have e : Set.range f = S.d₀ '' (S.cocycles₀ᗮ : Set V₀) := by
      ext y; constructor
      · rintro ⟨x, rfl⟩; exact ⟨x, x.2, rfl⟩
      · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩
    rwa [e] at this
  have e : (S.coboundaries : Set V₁) = S.d₀ '' (S.cocycles₀ᗮ : Set V₀) := by
    ext y; constructor
    · rintro ⟨τ, rfl⟩
      obtain ⟨ρ, hρ, hd⟩ := S.exists_mem_cocycles₀_orthogonal τ
      exact ⟨ρ, hρ, hd⟩
    · rintro ⟨x, -, rfl⟩; exact ⟨x, rfl⟩
  rw [e]; exact hr

variable (S)

/-- **Poincaré inequality** (Arnold, Theorem 4.6). If the ranges of both differentials are
closed (as subsets of the ambient spaces `W₁`, `W₂`), the short complex has a Poincaré
constant. -/
theorem exists_hasPoincareConst [CompleteSpace W₁] [CompleteSpace W₂]
    (h₀ : IsClosed (Set.range (S.ι₁ ∘ S.d₀))) (h₁ : IsClosed (Set.range S.d₁)) :
    ∃ c, S.HasPoincareConst c := by
  have hinj₀ : ∀ x ∈ S.cocycles₀ᗮ, S.ι₁ (S.d₀ x) = 0 → x = 0 := fun x hx hx0 => by
    have h := S.norm_ι₁_d₀ x
    rw [hx0, norm_zero] at h
    have hx' : x ∈ S.cocycles₀ := S.mem_cocycles₀.2 (norm_eq_zero.1 h.symm)
    exact inner_self_eq_zero.1 (Submodule.inner_right_of_mem_orthogonal hx' hx)
  have hinj₁ : ∀ x ∈ S.cocyclesᗮ, S.d₁ x = 0 → x = 0 := fun x hx hx0 =>
    inner_self_eq_zero.1 (Submodule.inner_right_of_mem_orthogonal (S.mem_cocycles.2 hx0) hx)
  refine exists_hasPoincareConst_of_bounds (S := S) ?_ ?_
  · obtain ⟨c, hc, H⟩ := exists_bound_on_submodule S.cocycles₀ᗮ (Submodule.isClosed_orthogonal _)
      (S.ι₁.comp S.d₀) hinj₀ (by
        convert h₀ using 1
        ext y; constructor
        · rintro ⟨x, -, rfl⟩; exact ⟨x, rfl⟩
        · rintro ⟨x, rfl⟩
          obtain ⟨ρ, hρ, hd⟩ := S.exists_mem_cocycles₀_orthogonal x
          exact ⟨ρ, hρ, by simp [hd]⟩)
    refine ⟨c, hc, fun τ hτ => ?_⟩
    have := H τ hτ
    rwa [ContinuousLinearMap.comp_apply, S.norm_ι₁_d₀] at this
  · exact exists_bound_on_submodule S.cocyclesᗮ (Submodule.isClosed_orthogonal _)
      S.d₁ hinj₁ (by
        convert h₁ using 1
        ext y; constructor
        · rintro ⟨x, -, rfl⟩; exact ⟨x, rfl⟩
        · rintro ⟨x, rfl⟩
          refine ⟨x - S.cocycles.starProjection x,
            Submodule.sub_starProjection_mem_orthogonal _, ?_⟩
          have : S.d₁ (S.cocycles.starProjection x) = 0 :=
            S.mem_cocycles.1 (Submodule.starProjection_apply_mem _ _)
          rw [map_sub, this, sub_zero])

/-- A finite-dimensional short complex has a Poincaré constant. -/
theorem exists_hasPoincareConst_of_finiteDimensional [FiniteDimensional ℝ V₀]
    [FiniteDimensional ℝ V₁] : ∃ c, S.HasPoincareConst c := by
  have := FiniteDimensional.complete ℝ V₀
  have := FiniteDimensional.complete ℝ V₁
  refine exists_hasPoincareConst_of_bounds (S := S) ?_ ?_
  · exact exists_bound_on_submodule_of_finiteDimensional S.cocycles₀ᗮ S.d₀ fun x hx hx0 =>
      inner_self_eq_zero.1 (Submodule.inner_right_of_mem_orthogonal (S.mem_cocycles₀.2 hx0) hx)
  · exact exists_bound_on_submodule_of_finiteDimensional S.cocyclesᗮ S.d₁ fun x hx hx0 =>
      inner_self_eq_zero.1 (Submodule.inner_right_of_mem_orthogonal (S.mem_cocycles.2 hx0) hx)

end Complete

end ShortHilbertComplex

end FEEC
