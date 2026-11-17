/-
Regularity of the Hodge Laplacian on a box, in Fourier coefficients.
-/
import FEEC.Fourier.EigenDeriv
import FEEC.Fourier.Parseval
import FEEC.DeRham.PoincareLemma

/-!
# Regularity on a box

For the solution `(σ, u, p)` of the Hodge Laplace problem on a box at level `k + 1`:
`p = 0`, `σ̂(m) = ξ_m ⌟ û(m)` and `|ξ_m|² û(m) = f̂(m)`. Consequently the Fourier
`H¹`-seminorms `Nsq` of `σ`, `dσ`, `u`, `du` are bounded by `‖f‖² + Nsq f`.
-/

namespace FEEC

namespace Fourier

open MeasureTheory Tensor

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {n : ℕ}
  {e : OrthonormalBasis (Fin n) ℝ E} {a b : Fin n → ℝ} {k : ℕ}

variable (e a b) in
/-- The terms of the Fourier `H¹`-seminorm. -/
noncomputable def nTerm (w : L2Form (box e a b) k) (m : Fin n → ℕ) : ℝ :=
  normProd a b m * ‖xi e a b m‖ ^ 2 * ‖coef e a b w m‖ ^ 2

variable (e a b) in
/-- The squared Fourier `H¹`-seminorm. -/
noncomputable def Nsq (w : L2Form (box e a b) k) : ℝ := ∑' m, nTerm e a b w m

theorem coef_sigma (hab : ∀ i, a i < b i) {f : L2Form (box e a b) (k + 1)}
    {σ : HΛ (box e a b) k} {u p : HΛ (box e a b) (k + 1)}
    (h : ((deRhamComplex (isOpen_box e a b)).segment k).IsSolution f σ u p) (m : Fin n → ℕ) :
    coef e a b (HΛ.toL2 σ) m = ccontr (xi e a b m) (coef e a b (HΛ.toL2 u) m) := by
  sorry

theorem coef_u (hab : ∀ i, a i < b i) {f : L2Form (box e a b) (k + 1)}
    {σ : HΛ (box e a b) k} {u p : HΛ (box e a b) (k + 1)}
    (h : ((deRhamComplex (isOpen_box e a b)).segment k).IsSolution f σ u p) (m : Fin n → ℕ) :
    (‖xi e a b m‖ ^ 2) • coef e a b (HΛ.toL2 u) m = coef e a b f m := by
  sorry

/-- **Regularity estimate.** -/
theorem exists_regularity (hab : ∀ i, a i < b i) (k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (f : L2Form (box e a b) (k + 1)) (σ : HΛ (box e a b) k) (u p : HΛ (box e a b) (k + 1)),
      ((deRhamComplex (isOpen_box e a b)).segment k).IsSolution f σ u p →
      Summable (nTerm e a b f) →
      Summable (nTerm e a b (HΛ.toL2 σ)) ∧ Summable (nTerm e a b (HΛ.toL2 (HΛ.d σ))) ∧
      Summable (nTerm e a b (HΛ.toL2 u)) ∧ Summable (nTerm e a b (HΛ.toL2 (HΛ.d u))) ∧
      Nsq e a b (HΛ.toL2 σ) + Nsq e a b (HΛ.toL2 (HΛ.d σ)) + Nsq e a b (HΛ.toL2 u) +
        Nsq e a b (HΛ.toL2 (HΛ.d u)) ≤ C * (‖f‖ ^ 2 + Nsq e a b f) := by
  sorry

end Fourier

end FEEC
