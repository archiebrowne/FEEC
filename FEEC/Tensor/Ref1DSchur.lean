/-
Schur sums for the one-dimensional shape and dual functions.
-/
import FEEC.Tensor.Ref1D

namespace FEEC

open MeasureTheory

namespace Ref

/-- The Schur sums of the kernel `∑ⱼ shapeⱼ(x) dualⱼ(y)` are bounded by an absolute constant,
independent of the interval and of the number of cells. -/
theorem exists_schur_const : ∃ K : ℝ, 0 ≤ K ∧ ∀ (a b : ℝ) (N : ℕ), a < b → 0 < N →
    ∀ s : Bool,
      (∀ x, ∑ j ∈ Finset.range (N + 2),
        |shape a b N s j x| * ∫ y in Set.Ioo a b, |dual a b N s j y| ≤ K) ∧
      (∀ y, ∑ j ∈ Finset.range (N + 2),
        (∫ x in Set.Ioo a b, |shape a b N s j x|) * |dual a b N s j y| ≤ K) := by
  sorry

end Ref

end FEEC
