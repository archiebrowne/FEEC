/-
Approximation estimate for L² forms with finite Fourier H¹-seminorm.
-/
import FEEC.Fourier.Regularity
import FEEC.Tensor.Approx

/-!
# Approximation of forms with finite Fourier `H¹`-seminorm

`‖w − πₕ w‖² ≤ C h² Nsq w` for every `L²` form `w` on the box with summable `nTerm`, where
`πₕ` is the `L²` operator of the tensor-product dual system. Proof: apply
`Tensor.exists_approx_smooth` to the partial sums of the eigenform expansion
(`hasSum_synth_coef`), whose derivatives are controlled by `nTerm`, and pass to the limit.
-/

namespace FEEC

namespace Fourier

open MeasureTheory Tensor

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {n : ℕ}
  {e : OrthonormalBasis (Fin n) ℝ E} {a b : Fin n → ℝ} {k : ℕ}

/-- The smooth function representing a finite eigenform sum. -/
noncomputable def synthFun (e : OrthonormalBasis (Fin n) ℝ E) (a b : Fin n → ℝ)
    (M : Finset (Fin n → ℕ)) (c : (Fin n → ℕ) → Covector E k) : E → E [⋀^Fin k]→L[ℝ] ℝ :=
  fun x => ∑ m ∈ M, ((k.factorial : ℝ))⁻¹ •
    ∑ T : Fin k → Fin n, ⟪c m, Covector.ofAlt (dxT e k T)⟫ • eigForm e a b T m x

theorem synthFun_mem_span (M : Finset (Fin n → ℕ)) (c : (Fin n → ℕ) → Covector E k) :
    synthFun e a b M c ∈ Submodule.span ℝ (Set.range fun p : (Fin k → Fin n) × (Fin n → ℕ) =>
      eigForm e a b p.1 p.2) := by
  sorry

theorem contDiff_synthFun (M : Finset (Fin n → ℕ)) (c : (Fin n → ℕ) → Covector E k) :
    ContDiff ℝ 1 (synthFun e a b M c) := by
  sorry

theorem toLp_synthFun (hab : ∀ i, a i < b i) (M : Finset (Fin n → ℕ))
    (c : (Fin n → ℕ) → Covector E k) :
    (memLp_of_continuous_box e a b
      (Covector.ofAlt.continuous.comp (contDiff_synthFun M c).continuous)).toLp _ =
      ∑ m ∈ M, synth e a b m (c m) := by
  sorry

/-- Derivatives of finite eigenform sums. -/
theorem sum_integral_fderiv_synthFun_le (hab : ∀ i, a i < b i) (M : Finset (Fin n → ℕ))
    (c : (Fin n → ℕ) → Covector E k) (hc : ∀ m, allow e m (c m) = c m) :
    ∑ i, ∫ x in box e a b, ‖Covector.ofAlt (fderiv ℝ (synthFun e a b M c) x (e i))‖ ^ 2 ≤
      ∑ m ∈ M, normProd a b m * ‖xi e a b m‖ ^ 2 * ‖c m‖ ^ 2 := by
  sorry

/-- **Approximation estimate** in terms of the Fourier `H¹`-seminorm. -/
theorem exists_approx_series (n k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E] (e : OrthonormalBasis (Fin n) ℝ E)
      (a b : Fin n → ℝ) (N : Fin n → ℕ) (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i) (h : ℝ)
      (_ : ∀ i, Ref.meshH (a i) (b i) (N i) ≤ h) (w : L2Form (box e a b) k)
      (_ : Summable (nTerm e a b w)),
      ‖w - (deRhamComplex (isOpen_box e a b)).dualOp (shapeH (e := e) hab hN)
            (dualL (e := e) hab hN) (fun k => ((k.factorial : ℝ))⁻¹) k w‖ ^ 2 ≤
        C * h ^ 2 * Nsq e a b w := by
  sorry

end Fourier

end FEEC
