/-
The L² Poincaré lemma on a box, and closedness of the de Rham complex.
-/
import FEEC.DeRham.BoxDecomp
import FEEC.Main

/-!
# The `L²` Poincaré lemma on a box

Let `Ω = box e a b` be a nonempty open box in a Euclidean space of any dimension.

* `FEEC.exists_hasWeakExtDeriv_of_closed`: **the `L²` Poincaré lemma**: every weakly closed
  `ω ∈ L²Λᵏ⁺¹(Ω)` is `dη` for some `η ∈ L²Λᵏ(Ω)` with `‖η‖ ≤ C ‖ω‖`.
* `FEEC.boxComplex_isClosed`: the `L²` de Rham complex of `Ω` is closed.
* `FEEC.box_harmonic_eq_bot`: there are no nonzero harmonic forms of positive degree.
* `FEEC.box_hodgeLaplace_wellPosed`: **the Hodge Laplace problem on `Ω` is well posed in every
  degree, with no further hypothesis.**
-/

namespace FEEC

open MeasureTheory

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- A linear functional dominated by the norm of a linear map into a Hilbert space is
represented by a vector (Riesz representation on the closure of the range). -/
theorem exists_inner_eq_of_abs_le {X H : Type*} [AddCommGroup X] [Module ℝ X]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (j : X →ₗ[ℝ] H) (g : X →ₗ[ℝ] ℝ) {C : ℝ} (hC : 0 ≤ C) (h : ∀ x, |g x| ≤ C * ‖j x‖) :
    ∃ η : H, ‖η‖ ≤ C ∧ ∀ x, g x = ⟪η, j x⟫ := by
  sorry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {n : ℕ}
  (e : OrthonormalBasis (Fin n) ℝ E) {a b : Fin n → ℝ}

/-- **The `L²` Poincaré lemma on a box.** -/
theorem exists_hasWeakExtDeriv_of_closed (hab : ∀ i, a i < b i) (k : ℕ) :
    ∃ C : ℝ, ∀ ω : L2Form (box e a b) (k + 1),
      HasWeakExtDeriv ω (0 : L2Form (box e a b) (k + 2)) →
      ∃ η : L2Form (box e a b) k, HasWeakExtDeriv η ω ∧ ‖η‖ ≤ C * ‖ω‖ := by
  sorry

/-- **The `L²` de Rham complex of a box is closed.** -/
theorem boxComplex_isClosed (hab : ∀ i, a i < b i) :
    (deRhamComplex (isOpen_box e a b)).IsClosed := by
  sorry

/-- On a box there are no nonzero harmonic forms of positive degree. -/
theorem box_harmonic_eq_bot (hab : ∀ i, a i < b i) (k : ℕ) :
    ((deRhamComplex (isOpen_box e a b)).segment k).harmonic = ⊥ := by
  sorry

/-- **Unconditional well-posedness of the Hodge Laplacian on a box**, in every dimension and
every degree `k + 1`: for every `f ∈ L²Λᵏ⁺¹(Ω)` the mixed problem: find `σ ∈ HΛᵏ`,
`u ∈ HΛᵏ⁺¹`, `p ∈ 𝔥ᵏ⁺¹` with `σ = d* u`, `dσ + d* du + p = f`, `u ⟂ 𝔥ᵏ⁺¹`, has a unique
solution, depending continuously on `f`; moreover `p = 0`. -/
theorem box_hodgeLaplace_wellPosed (hab : ∀ i, a i < b i) (k : ℕ) :
    ∃ c : ℝ, ∀ f : L2Form (box e a b) (k + 1), ∃ σ u p,
      ((deRhamComplex (isOpen_box e a b)).segment k).IsSolution f σ u p ∧ p = 0 ∧
      ‖σ‖ + ‖u‖ + ‖p‖ ≤ stabilityConst c * ‖f‖ ∧
      ∀ σ' u' p', ((deRhamComplex (isOpen_box e a b)).segment k).IsSolution f σ' u' p' →
        σ' = σ ∧ u' = u ∧ p' = p := by
  sorry

end FEEC
