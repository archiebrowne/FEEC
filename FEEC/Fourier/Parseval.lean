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
      rw [← real_inner_self_eq_norm_sq, inner_proj_proj hab, if_pos rfl])
  exact ⟨_, hs.hasSum⟩

theorem sum_inner_dxT_cov (S : Fin k → Fin n) :
    ∑ T : Fin k → Fin n, ⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k T)⟫ •
      Covector.ofAlt (dxT e k T) = (k.factorial : ℝ) • Covector.ofAlt (dxT e k S) := by
  have h := sum_inner_dxT_smul (e := e) (dxT e k S)
  have h2 := congrArg Covector.ofAlt h
  simp only [map_smul, map_sum] at h2
  rw [← h2, smul_inv_smul₀ (by positivity)]
  sorry

end helpers

end Fourier

end FEEC
