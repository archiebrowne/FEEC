/-
An unconditional O(h) convergence rate for tensor-product FEEC on a box.
-/
import FEEC.Fourier.SeriesApprox
import FEEC.Fourier.Data
import FEEC.Tensor.Main

/-!
# Convergence rate on a box in any dimension

**Theorem** (`Fourier.box_tensor_rate`). Let `Ω` be a box in a Euclidean space of any
dimension, `k + 1` a degree. There is `C`, depending only on the box and `k`, such that for
every tensor-product grid with all cell sizes at most `h` and every test form `φ` of degree
`k + 1`, the solutions of the Hodge Laplace problem and of its Galerkin approximation in the
tensor-product Whitney spaces, with data `f = φ`, satisfy

  `‖σ − σh‖ + ‖u − uh‖ + ‖p − ph‖ ≤ C h (‖φ‖ + ∑ᵢ ‖∂ᵢ φ‖)`.

No hypothesis is assumed.
-/

namespace FEEC

namespace Fourier

open MeasureTheory Tensor

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {n : ℕ}
  (e : OrthonormalBasis (Fin n) ℝ E) {a b : Fin n → ℝ}

/-- **Unconditional `O(h)` convergence of tensor-product FEEC for the Hodge Laplacian on a
box, in any dimension and degree.** -/
theorem box_tensor_rate (hab : ∀ i, a i < b i) (k : ℕ) :
    ∃ C : ℝ, ∀ (N : Fin n → ℕ) (hN : ∀ i, 0 < N i) (h : ℝ)
      (_ : ∀ i, Ref.meshH (a i) (b i) (N i) ≤ h)
      (φ : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ) (hφ : IsTestForm (box e a b) φ)
      (σ : HΛ (box e a b) k) (u p : HΛ (box e a b) (k + 1))
      (_ : ((deRhamComplex (isOpen_box e a b)).segment k).IsSolution hφ.toLp σ u p)
      (σh : (subcomplex e hab hN).carrier k) (uh ph : (subcomplex e hab hN).carrier (k + 1))
      (_ : ((subcomplex e hab hN).segment k).toShort.IsSolution hφ.toLp σh uh ph),
      ‖σ - σh‖ + ‖u - uh‖ + ‖p - ph‖ ≤
        C * h * (‖hφ.toLp‖ + ∑ i, Real.sqrt
          (∫ x in box e a b, ‖Covector.ofAlt (fderiv ℝ φ x (e i))‖ ^ 2)) := by
  sorry

end Fourier

end FEEC
