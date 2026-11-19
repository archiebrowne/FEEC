/-
Bessel's inequality and completeness of the eigenform expansion.
-/
import FEEC.Fourier.Eigenforms

namespace FEEC

namespace Fourier

open MeasureTheory Tensor

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {n : ℕ}
  {e : OrthonormalBasis (Fin n) ℝ E} {a b : Fin n → ℝ} {k : ℕ}

section helpers

local notation "𝒫" => fun (w : L2Form (box e a b) k) (m : Fin n → ℕ) => synth e a b m (coef e a b w m)

theorem inner_proj_proj (hab : ∀ i, a i < b i) (w : L2Form (box e a b) k) (m m' : Fin n → ℕ) :
    ⟪synth e a b m (coef e a b w m), synth e a b m' (coef e a b w m')⟫ =
      if m = m' then normProd a b m * ‖coef e a b w m‖ ^ 2 else 0 := by
  rw [inner_synth_synth hab]
  split_ifs with h
  · subst h
    rw [allow_coef hab, real_inner_self_eq_norm_sq]
  · rfl

theorem inner_self_proj (hab : ∀ i, a i < b i) (w : L2Form (box e a b) k) (m : Fin n → ℕ) :
    ⟪w, synth e a b m (coef e a b w m)⟫ = normProd a b m * ‖coef e a b w m‖ ^ 2 := by
  rw [inner_synth hab, real_inner_self_eq_norm_sq]

theorem norm_sq_sum_proj (hab : ∀ i, a i < b i) (w : L2Form (box e a b) k)
    (M : Finset (Fin n → ℕ)) :
    ‖∑ m ∈ M, synth e a b m (coef e a b w m)‖ ^ 2 =
      ∑ m ∈ M, normProd a b m * ‖coef e a b w m‖ ^ 2 := by
  classical
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [inner_sum]
  simp only [inner_proj_proj hab]
  simp [hm]

theorem bessel (hab : ∀ i, a i < b i) (w : L2Form (box e a b) k) (M : Finset (Fin n → ℕ)) :
    ∑ m ∈ M, normProd a b m * ‖coef e a b w m‖ ^ 2 ≤ ‖w‖ ^ 2 := by
  have h1 : ⟪w, ∑ m ∈ M, synth e a b m (coef e a b w m)⟫ =
      ∑ m ∈ M, normProd a b m * ‖coef e a b w m‖ ^ 2 := by
    rw [inner_sum]
    exact Finset.sum_congr rfl fun m _ => inner_self_proj hab w m
  have h2 := norm_sub_sq_real w (∑ m ∈ M, synth e a b m (coef e a b w m))
  rw [h1, norm_sq_sum_proj hab] at h2
  nlinarith [sq_nonneg ‖w - ∑ m ∈ M, synth e a b m (coef e a b w m)‖]

theorem summable_norm_sq_coef (hab : ∀ i, a i < b i) (w : L2Form (box e a b) k) :
    Summable (fun m => normProd a b m * ‖coef e a b w m‖ ^ 2) :=
  summable_of_sum_le (fun m => mul_nonneg (normProd_pos hab m).le (sq_nonneg _))
    (bessel hab w)

theorem exists_hasSum_proj (hab : ∀ i, a i < b i) (w : L2Form (box e a b) k) :
    ∃ w', HasSum (fun m => synth e a b m (coef e a b w m)) w' := by
  classical
  let V : (Fin n → ℕ) → Submodule ℝ (L2Form (box e a b) k) := fun m =>
    ℝ ∙ synth e a b m (coef e a b w m)
  have hV : OrthogonalFamily ℝ (fun m => V m) (fun m => (V m).subtypeₗᵢ) := by
    rw [orthogonalFamily_iff_pairwise]
    intro m m' hne
    simp only [Function.onFun, V]
    rw [Submodule.isOrtho_span]
    simp only [Set.mem_singleton_iff, forall_eq]
    rw [inner_proj_proj hab, if_neg hne]
  have hs := (hV.summable_iff_norm_sq_summable
    (fun m => (⟨synth e a b m (coef e a b w m), Submodule.mem_span_singleton_self _⟩ : V m))).2 (by
      refine (summable_norm_sq_coef hab w).congr fun m => ?_
      show _ = ‖synth e a b m (coef e a b w m)‖ ^ 2
      have := inner_proj_proj hab w m m
      rw [if_pos rfl, real_inner_self_eq_norm_sq] at this
      exact this.symm)
  exact ⟨_, hs.hasSum⟩

theorem sum_inner_dxT_cov (S : Fin k → Fin n) :
    ∑ T : Fin k → Fin n, ⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k T)⟫ •
      Covector.ofAlt (dxT e k T) = (k.factorial : ℝ) • Covector.ofAlt (dxT e k S) := by
  have h := sum_inner_dxT_smul (e := e) (dxT e k S)
  have h2 := congrArg Covector.ofAlt h
  simp only [map_smul, map_sum] at h2
  exact (inv_smul_eq_iff₀ (by positivity)).1 h2

theorem integral_eigLp_term (hab : ∀ i, a i < b i) (r : L2Form (box e a b) k)
    (m : Fin n → ℕ) (S T : Fin k → Fin n) :
    Integrable (fun x => trigProd e a b (pat S) m x *
        (⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k T)⟫ *
          ⟪Covector.ofAlt (dxT e k T), r x⟫)) (volume.restrict (box e a b)) ∧
      ⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k T)⟫ * ⟪r, eigLp e a b T m⟫ =
      ∫ x in box e a b, trigProd e a b (pat S) m x *
        (⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k T)⟫ *
          ⟪Covector.ofAlt (dxT e k T), r x⟫) := by
  by_cases hc : ⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k T)⟫ = 0
  · simp [hc]
  · have hp : pat T = pat S := by
      have hr : Set.range S = Set.range T := by
        by_contra hr
        exact hc (inner_dxT_eq_zero_of_range_ne e hr)
      funext i
      have := Set.ext_iff.1 hr i
      simp only [Set.mem_range] at this
      simp only [pat, this.symm]
    have hae : (fun x => trigProd e a b (pat S) m x *
        (⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k T)⟫ *
          ⟪Covector.ofAlt (dxT e k T), r x⟫)) =ᵐ[volume.restrict (box e a b)]
        fun x => ⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k T)⟫ *
          ⟪r x, eigLp e a b T m x⟫ := by
      filter_upwards [coeFn_eigLp (e := e) (a := a) (b := b) T m] with x hx
      rw [hx, eigForm, ← hp, map_smul, inner_smul_right, real_inner_comm (r x)]
      ring
    refine ⟨((L2.integrable_inner r (eigLp e a b T m)).const_mul _).congr hae.symm, ?_⟩
    rw [integral_congr_ae hae, L2.inner_def, integral_const_mul]

theorem eq_zero_of_inner_synth (hab : ∀ i, a i < b i) (r : L2Form (box e a b) k)
    (h : ∀ m β, ⟪r, synth e a b m β⟫ = 0) : r = 0 := by
  classical
  have hF : ∀ S : Fin k → Fin n, MemLp (fun x => ⟪Covector.ofAlt (dxT e k S), r x⟫) 2
      (volume.restrict (box e a b)) := fun S =>
    (innerSL ℝ (Covector.ofAlt (dxT e k S))).comp_memLp' (Lp.memLp r)
  have hS : ∀ S : Fin k → Fin n, (fun x => ⟪Covector.ofAlt (dxT e k S), r x⟫)
      =ᵐ[volume.restrict (box e a b)] 0 := by
    intro S
    refine eq_zero_of_forall_integral_trigProd e hab (pat S) (hF S) fun m => ?_
    have h1 := h m (Covector.ofAlt (dxT e k S))
    rw [synth, inner_smul_right, inner_sum] at h1
    simp only [inner_smul_right] at h1
    have h2 : ∑ T : Fin k → Fin n,
        ⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k T)⟫ * ⟪r, eigLp e a b T m⟫ =
        ∫ x in box e a b, ∑ T : Fin k → Fin n, trigProd e a b (pat S) m x *
          (⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k T)⟫ *
            ⟪Covector.ofAlt (dxT e k T), r x⟫) := by
      rw [integral_finsetSum _ fun T _ => (integral_eigLp_term hab r m S T).1]
      exact Finset.sum_congr rfl fun T _ => (integral_eigLp_term hab r m S T).2
    have h3 : ∀ x, ∑ T : Fin k → Fin n, trigProd e a b (pat S) m x *
          (⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k T)⟫ *
            ⟪Covector.ofAlt (dxT e k T), r x⟫) =
        (k.factorial : ℝ) * (⟪Covector.ofAlt (dxT e k S), r x⟫ * trigProd e a b (pat S) m x) := by
      intro x
      have h4 : ∑ T : Fin k → Fin n,
          ⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k T)⟫ *
            ⟪Covector.ofAlt (dxT e k T), r x⟫ = (k.factorial : ℝ) * ⟪Covector.ofAlt (dxT e k S), r x⟫ := by
        have := congrArg (fun v => ⟪v, r x⟫) (sum_inner_dxT_cov (e := e) S)
        simpa [sum_inner, inner_smul_left] using this
      rw [← Finset.mul_sum, h4]
      ring
    simp only [h3] at h2
    rw [integral_const_mul] at h2
    have hk : (k.factorial : ℝ) ≠ 0 := by positivity
    rw [h2] at h1
    rcases mul_eq_zero.1 h1 with h5 | h5
    · exact absurd (inv_eq_zero.1 h5) hk
    · rcases mul_eq_zero.1 h5 with h6 | h6
      · exact absurd h6 hk
      · exact h6
  have hall : ∀ᵐ x ∂(volume.restrict (box e a b)), ∀ S : Fin k → Fin n,
      ⟪Covector.ofAlt (dxT e k S), r x⟫ = 0 := ae_all_iff.2 fun S => hS S
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [hall] with x hx
  have h0 : ∀ T : Fin k → Fin n, ⟪r x, Covector.ofAlt (dxT e k T)⟫ = 0 := fun T => by
    rw [real_inner_comm]; exact hx T
  have := sum_inner_dxT_smul (e := e) (r x).toAlt
  simp only [Covector.ofAlt_toAlt, h0, zero_smul, Finset.sum_const_zero, smul_zero] at this
  have h7 : r x = Covector.ofAlt (r x).toAlt := (Covector.ofAlt_toAlt _).symm
  rw [h7, ← this]
  simp

/-- **Completeness**: every `L²` form is the sum of its eigenform expansion. -/
theorem hasSum_synth_coef (hab : ∀ i, a i < b i) (w : L2Form (box e a b) k) :
    HasSum (fun m => synth e a b m (coef e a b w m)) w := by
  classical
  obtain ⟨w', hw'⟩ := exists_hasSum_proj hab w
  have key : ∀ m β, ⟪w', synth e a b m β⟫ = ⟪w, synth e a b m β⟫ := by
    intro m β
    have h1 : HasSum (fun m' => ⟪synth e a b m' (coef e a b w m'), synth e a b m β⟫)
        ⟪w', synth e a b m β⟫ := by
      have := (innerSL ℝ (synth e a b m β)).hasSum hw'
      simpa [real_inner_comm (synth e a b m β)] using this
    have h2 : (fun m' => ⟪synth e a b m' (coef e a b w m'), synth e a b m β⟫) =
        fun m' => if m' = m then ⟪w, synth e a b m β⟫ else 0 := by
      funext m'
      rw [inner_synth_synth hab, inner_synth hab]
      by_cases hm : m' = m
      · subst hm; simp [allow_coef hab]
      · simp [hm]
    rw [h2] at h1
    exact h1.unique (hasSum_ite_eq m _)
  have hr : w - w' = 0 := by
    refine eq_zero_of_inner_synth hab _ fun m β => ?_
    rw [inner_sub_left, key, sub_self]
  have hw : w' = w := (sub_eq_zero.1 hr).symm
  rw [hw] at hw'
  exact hw'

/-- **Parseval's identity** for the eigenform expansion. -/
theorem hasSum_norm_sq_coef (hab : ∀ i, a i < b i) (w : L2Form (box e a b) k) :
    HasSum (fun m => normProd a b m * ‖coef e a b w m‖ ^ 2) (‖w‖ ^ 2) := by
  have h := hasSum_synth_coef hab w
  have h2 : Filter.Tendsto (fun M : Finset (Fin n → ℕ) =>
      ‖∑ m ∈ M, synth e a b m (coef e a b w m)‖ ^ 2) Filter.atTop (nhds (‖w‖ ^ 2)) :=
    ((continuous_norm.pow 2).tendsto w).comp h
  simp only [norm_sq_sum_proj hab] at h2
  exact h2

end helpers

end Fourier

end FEEC
