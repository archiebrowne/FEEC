/-
Approximation estimate for the tensor-product quasi-interpolant on smooth functions.
-/
import FEEC.Tensor.ApproxScalar
import FEEC.Tensor.ProjectionBound
import FEEC.Fourier.Eigenforms

/-!
# Approximation by the tensor-product projection

For a trigonometric polynomial form `g` (a combination of eigenforms), `‖[g] - πₕ[g]‖_{L²(box)}² ≤ C h² ∑ᵢ ‖∂ᵢ g‖²_{L²(box)}`, where
`πₕ` is the `L²` operator of the dual system (`dualOp`) and `h` bounds all mesh sizes. The
constant depends only on `n` and `k`.
-/

namespace FEEC

namespace Tensor

open MeasureTheory

local notation "⟪" x ", " y "⟫" => inner ℝ x y

theorem memLp_of_continuous_box {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {n : ℕ}
    (e : OrthonormalBasis (Fin n) ℝ E) (a b : Fin n → ℝ) {F : Type*} [NormedAddCommGroup F]
    {g : E → F} (hg : Continuous g) : MemLp g 2 (volume.restrict (box e a b)) := by
  sorry

/-- **Approximation estimate** for smooth forms. -/
theorem exists_approx_smooth (n k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E] (e : OrthonormalBasis (Fin n) ℝ E)
      (a b : Fin n → ℝ) (N : Fin n → ℕ) (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i) (h : ℝ)
      (hh : ∀ i, Ref.meshH (a i) (b i) (N i) ≤ h)
      (g : E → E [⋀^Fin k]→L[ℝ] ℝ) (hg : ContDiff ℝ 1 g)
      (hgs : g ∈ Submodule.span ℝ (Set.range fun p : (Fin k → Fin n) × (Fin n → ℕ) =>
        Fourier.eigForm e a b p.1 p.2)),
      ‖(memLp_of_continuous_box e a b (Covector.ofAlt.continuous.comp hg.continuous)).toLp _ -
          (deRhamComplex (isOpen_box e a b)).dualOp (shapeH (e := e) hab hN)
            (dualL (e := e) hab hN) (fun k => ((k.factorial : ℝ))⁻¹) k
            ((memLp_of_continuous_box e a b
              (Covector.ofAlt.continuous.comp hg.continuous)).toLp _)‖ ^ 2 ≤
        C * h ^ 2 * ∑ i, ∫ x in box e a b, ‖Covector.ofAlt (fderiv ℝ g x (e i))‖ ^ 2 := by
  sorry

end Tensor

end FEEC
