/-
Schur's test for finite-rank operators on `L²`.
-/
import Mathlib

namespace FEEC

open MeasureTheory

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- **Schur's test** for the finite-rank operator `ω ↦ ∑ₘ ⟪ω, bₘ β⟫ aₘ α` on `L²(μ; F)`. -/
theorem norm_sum_inner_smul_le {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {ι : Type*} [Fintype ι] (A B : ι → Lp F 2 μ) (a b : ι → X → ℝ) (α β : F)
    (hA : ∀ m, A m =ᵐ[μ] fun x => a m x • α) (hB : ∀ m, B m =ᵐ[μ] fun x => b m x • β)
    (ha : ∀ m, Integrable (a m) μ) (hb : ∀ m, Integrable (b m) μ)
    (hbb : ∀ m, ∃ C, ∀ y, |b m y| ≤ C)
    {M₁ M₂ : ℝ} (h1 : ∀ᵐ x ∂μ, ∑ m, |a m x| * ∫ y, |b m y| ∂μ ≤ M₁)
    (h2 : ∀ᵐ y ∂μ, ∑ m, (∫ x, |a m x| ∂μ) * |b m y| ≤ M₂) (ω : Lp F 2 μ) :
    ‖∑ m, ⟪ω, B m⟫ • A m‖ ^ 2 ≤ ‖α‖ ^ 2 * ‖β‖ ^ 2 * M₁ * M₂ * ‖ω‖ ^ 2 := by
  sorry

end FEEC
