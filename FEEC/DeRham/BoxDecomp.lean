/-
Decomposition of test forms on a box.
-/
import FEEC.DeRham.BoxBounds

/-!
# Decomposition of test forms on a box

Let `Ω = box e a b = {x | ∀ i, aᵢ < ⟪eᵢ, x⟫ < bᵢ}` for an orthonormal basis `e`. Applying the
one-directional homotopy successively in the directions `e₀, …, e_{n-1}` shows that every
test form `φ` of positive degree on `Ω` can be written `φ = δψ + χ` with test forms `ψ`, `χ`
and `‖χ‖_{L²} ≤ C ‖δφ‖_{L²}` (`FEEC.exists_codiff_decomp`).
-/

namespace FEEC

open MeasureTheory

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ} {k : ℕ}

/-- The open box `{x | ∀ i, aᵢ < ⟪eᵢ, x⟫ < bᵢ}` with respect to an orthonormal basis `e`. -/
def box (e : OrthonormalBasis (Fin n) ℝ E) (a b : Fin n → ℝ) : Set E :=
  {x | ∀ i, ⟪e i, x⟫ ∈ Set.Ioo (a i) (b i)}

variable (e : OrthonormalBasis (Fin n) ℝ E) (a b : Fin n → ℝ)

theorem isOpen_box : IsOpen (box e a b) := by
  sorry

theorem isSlab_box (i : Fin n) : IsSlab (box e a b) (e i) (a i) (b i) := by
  sorry

/-- The composition `Q_{j-1} ∘ ⋯ ∘ Q_0` of the operators `homotopyQ (e i) (θ i)`. -/
noncomputable def iterQ (θ : Fin n → ℝ → ℝ) :
    ℕ → (E → E [⋀^Fin k]→L[ℝ] ℝ) → (E → E [⋀^Fin k]→L[ℝ] ℝ)
  | 0, φ => φ
  | j + 1, φ => if h : j < n then homotopyQ (e ⟨j, h⟩) (θ ⟨j, h⟩) (iterQ θ j φ)
      else iterQ θ j φ

variable {e a b} {θ : Fin n → ℝ → ℝ}

theorem IsTestForm.iterQ (hθ : ∀ i, IsBump (θ i) (a i) (b i)) (j : ℕ)
    {φ : E → E [⋀^Fin k]→L[ℝ] ℝ} (hφ : IsTestForm (box e a b) φ) :
    IsTestForm (box e a b) (iterQ e θ j φ) := by
  sorry

theorem codiff_iterQ (hθ : ∀ i, IsBump (θ i) (a i) (b i)) (j : ℕ)
    {φ : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ} (hφ : IsTestForm (box e a b) φ) :
    codiff (iterQ e θ j φ) = iterQ e θ j (codiff φ) := by
  sorry

/-- After all `n` directions nothing is left of a form of positive degree. -/
theorem iterQ_eq_zero (hθ : ∀ i, IsBump (θ i) (a i) (b i))
    {φ : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ} (hφ : IsTestForm (box e a b) φ) :
    iterQ e θ n φ = 0 := by
  sorry

variable [MeasurableSpace E] [BorelSpace E]

theorem exists_norm_iterQ_le (hθ : ∀ i, IsBump (θ i) (a i) (b i)) (k j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : E → E [⋀^Fin k]→L[ℝ] ℝ) (hφ : IsTestForm (box e a b) φ)
      (hR : IsTestForm (box e a b) (iterQ e θ j φ)), ‖hR.toLp‖ ≤ C * ‖hφ.toLp‖ := by
  sorry

/-- **Decomposition of test forms on a box.** Every test form `φ` of positive degree is
`δψ + χ` with `χ` controlled in `L²` by `δφ`. -/
theorem exists_codiff_decomp (e : OrthonormalBasis (Fin n) ℝ E) {a b : Fin n → ℝ}
    (hab : ∀ i, a i < b i) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ) (hφ : IsTestForm (box e a b) φ),
      ∃ (ψ : E → E [⋀^Fin (k + 2)]→L[ℝ] ℝ) (_ : IsTestForm (box e a b) ψ)
        (χ : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ) (hχ : IsTestForm (box e a b) χ),
        φ = codiff ψ + χ ∧ ‖hχ.toLp‖ ≤ C * ‖hφ.codiff.toLp‖ := by
  sorry

end FEEC
