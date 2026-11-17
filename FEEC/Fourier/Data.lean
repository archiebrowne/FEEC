/-
The Fourier H¹-seminorm of a test form.
-/
import FEEC.Fourier.Regularity

namespace FEEC

namespace Fourier

open MeasureTheory Tensor

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {n : ℕ}
  {e : OrthonormalBasis (Fin n) ℝ E} {a b : Fin n → ℝ} {k : ℕ}

/-- For a test form, the Fourier `H¹`-seminorm is bounded by the `L²` norms of its partial
derivatives (Bessel's inequality for the derivatives, integration by parts). -/
theorem summable_nTerm_and_Nsq_le (hab : ∀ i, a i < b i) {φ : E → E [⋀^Fin k]→L[ℝ] ℝ}
    (hφ : IsTestForm (box e a b) φ) :
    Summable (nTerm e a b hφ.toLp) ∧
      Nsq e a b hφ.toLp ≤ ∑ i, ∫ x in box e a b, ‖Covector.ofAlt (fderiv ℝ φ x (e i))‖ ^ 2 := by
  sorry

end Fourier

end FEEC
