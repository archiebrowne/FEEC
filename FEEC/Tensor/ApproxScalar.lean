/-
Approximation by the scalar tensor-product quasi-interpolant on trigonometric polynomials.
-/
import FEEC.Tensor.Ref1DApprox
import FEEC.Fourier.CoordSchur
import FEEC.Fourier.TrigDensity

/-!
# The scalar tensor-product quasi-interpolant

For a pattern `s` (`true` = cell, `false` = node in each direction),
`quasiP s G x = ∑_q (∏ᵢ shapeᵢ(xᵢ)) ∫_box (∏ᵢ dualᵢ) G`. For `G` a trigonometric polynomial,
`‖G − quasiP s G‖² ≤ C h² ∑ᵢ ‖∂ᵢ G‖²` on the box, `C` depending only on `n`.

*Proof idea.* On products `G = ∏ gᵢ(xᵢ)`, `quasiP` is the product of the one-dimensional
operators (`integral_box_prod`), and `G − quasiP G = ∑ᵢ P₁ ⋯ P_{i−1} Rᵢ (∂ᵢ G)` where `Pⱼ`, `Rᵢ`
are integral operators in one coordinate (`coordOp`) with kernels
`∑_j shape_j(t) dual_j(τ)` and `Ref.rKer`; by linearity this holds for trigonometric
polynomials, and `coordOp_sq_le` bounds each term.
-/

namespace FEEC

namespace Tensor

open MeasureTheory

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {n : ℕ}

/-- Product of shape functions with pattern `s`. -/
noncomputable def shapeP (e : OrthonormalBasis (Fin n) ℝ E) (a b : Fin n → ℝ) (N : Fin n → ℕ)
    (s : Fin n → Bool) (q : Fin n → ℕ) (x : E) : ℝ :=
  ∏ i, Ref.shape (a i) (b i) (N i) (s i) (q i) ⟪e i, x⟫

/-- Product of dual functions with pattern `s`. -/
noncomputable def dualP (e : OrthonormalBasis (Fin n) ℝ E) (a b : Fin n → ℝ) (N : Fin n → ℕ)
    (s : Fin n → Bool) (q : Fin n → ℕ) (x : E) : ℝ :=
  ∏ i, Ref.dual (a i) (b i) (N i) (s i) (q i) ⟪e i, x⟫

/-- The scalar tensor-product quasi-interpolant. -/
noncomputable def quasiP (e : OrthonormalBasis (Fin n) ℝ E) (a b : Fin n → ℝ) (N : Fin n → ℕ)
    (s : Fin n → Bool) (G : E → ℝ) (x : E) : ℝ :=
  ∑ q : (i : Fin n) → Fin (N i + 2), shapeP e a b N s (fun i => q i) x *
    ∫ y in box e a b, dualP e a b N s (fun i => q i) y * G y

/-- **Approximation estimate** for trigonometric polynomials. -/
theorem exists_approx_trig (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E] (e : OrthonormalBasis (Fin n) ℝ E)
      (a b : Fin n → ℝ) (N : Fin n → ℕ) (_ : ∀ i, a i < b i) (_ : ∀ i, 0 < N i) (h : ℝ)
      (_ : ∀ i, Ref.meshH (a i) (b i) (N i) ≤ h) (s : Fin n → Bool) (G : E → ℝ)
      (_ : G ∈ Submodule.span ℝ
        (Set.range fun p : (Fin n → Bool) × (Fin n → ℕ) => trigProd e a b p.1 p.2)),
      ∫ x in box e a b, (G x - quasiP e a b N s G x) ^ 2 ≤
        C * h ^ 2 * ∑ i, ∫ x in box e a b, (fderiv ℝ G x (e i)) ^ 2 := by
  sorry

end Tensor

end FEEC
