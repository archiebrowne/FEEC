/-
`L²` bounds for the one-directional homotopy operators.
-/
import FEEC.DeRham.BoxHomotopy
import FEEC.DeRham.LineL2
import FEEC.DeRham.TestForm

/-!
# `L²` bounds for the homotopy operators

On a slab `Ω` in direction `e`, the operators `homotopyS e θ` and `homotopyQ e θ` are bounded
in the `L²(Ω)` norm on test forms.
-/

namespace FEEC

open MeasureTheory

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Set E} {e : E} {θ : ℝ → ℝ} {a b : ℝ}

theorem exists_norm_homotopyS_le (hΩm : MeasurableSet Ω) (hΩ : IsSlab Ω e a b)
    (hθ : IsBump θ a b) (he : ‖e‖ = 1) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : E → E [⋀^Fin k]→L[ℝ] ℝ) (hφ : IsTestForm Ω φ)
      (hS : IsTestForm Ω (homotopyS e θ φ)), ‖hS.toLp‖ ≤ C * ‖hφ.toLp‖ := by
  sorry

theorem exists_norm_homotopyQ_le (hΩm : MeasurableSet Ω) (hΩ : IsSlab Ω e a b)
    (hθ : IsBump θ a b) (he : ‖e‖ = 1) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : E → E [⋀^Fin k]→L[ℝ] ℝ) (hφ : IsTestForm Ω φ)
      (hQ : IsTestForm Ω (homotopyQ e θ φ)), ‖hQ.toLp‖ ≤ C * ‖hφ.toLp‖ := by
  sorry

end FEEC
