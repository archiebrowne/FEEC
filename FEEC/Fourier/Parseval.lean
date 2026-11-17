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

/-- **Parseval's identity** for the eigenform expansion. -/
theorem hasSum_norm_sq_coef (hab : ∀ i, a i < b i) (w : L2Form (box e a b) k) :
    HasSum (fun m => normProd a b m * ‖coef e a b w m‖ ^ 2) (‖w‖ ^ 2) := by
  sorry

/-- **Completeness**: every `L²` form is the sum of its eigenform expansion. -/
theorem hasSum_synth_coef (hab : ∀ i, a i < b i) (w : L2Form (box e a b) k) :
    HasSum (fun m => synth e a b m (coef e a b w m)) w := by
  sorry

end Fourier

end FEEC
