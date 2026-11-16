/-
Biorthogonality of the one-dimensional shape and dual functions.
-/
import FEEC.Tensor.Ref1D

namespace FEEC

open MeasureTheory

namespace Ref

variable {a b : ℝ} {N : ℕ}

/-- **Biorthogonality** of shape and dual functions of the same type. -/
theorem integral_shape_mul_dual (hab : a < b) (hN : 0 < N) (s : Bool) (i j : ℕ) :
    ∫ x in Set.Ioo a b, shape a b N s i x * dual a b N s j x =
      if Valid N s i ∧ i = j then 1 else 0 := by
  sorry

end Ref

end FEEC
