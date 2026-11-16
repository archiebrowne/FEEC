/-
Integrals of product functions over a box.
-/
import FEEC.DeRham.BoxDecomp

namespace FEEC

open MeasureTheory

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {n : ℕ}

/-- The integral over a box of a product of functions of the coordinates is the product of
the one-dimensional integrals. -/
theorem integral_box_prod (e : OrthonormalBasis (Fin n) ℝ E) (a b : Fin n → ℝ)
    (f : Fin n → ℝ → ℝ) :
    ∫ x in box e a b, ∏ i, f i ⟪e i, x⟫ = ∏ i, ∫ t in Set.Ioo (a i) (b i), f i t := by
  sorry

theorem measurableSet_box (e : OrthonormalBasis (Fin n) ℝ E) (a b : Fin n → ℝ) :
    MeasurableSet (box e a b) := (isOpen_box e a b).measurableSet

/-- A box has finite volume. -/
theorem volume_box_lt_top (e : OrthonormalBasis (Fin n) ℝ E) (a b : Fin n → ℝ) :
    volume (box e a b) < ⊤ := by
  sorry

end FEEC
