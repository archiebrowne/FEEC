/-
Uniform L² bound for the tensor-product projection.
-/
import FEEC.Tensor.Projection

namespace FEEC

namespace Tensor

open MeasureTheory

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- **Uniform `L²` bound**: the operators of the dual system are bounded by constants
depending only on the dimension `n` and the degree `k`. -/
theorem exists_norm_dualOp_le (n : ℕ) : ∃ K : ℕ → ℝ, (∀ k, 0 ≤ K k) ∧
    ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E] (e : OrthonormalBasis (Fin n) ℝ E)
      (a b : Fin n → ℝ) (N : Fin n → ℕ) (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i) (k : ℕ)
      (w : L2Form (box e a b) k),
      ‖(deRhamComplex (isOpen_box e a b)).dualOp (shapeH (e := e) hab hN)
        (dualL (e := e) hab hN) (fun k => ((k.factorial : ℝ))⁻¹) k w‖ ≤ K k * ‖w‖ := by
  sorry

end Tensor

end FEEC
