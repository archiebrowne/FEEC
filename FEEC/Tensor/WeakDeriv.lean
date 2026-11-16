/-
Weak exterior derivatives of tensor-product forms on a box.
-/
import FEEC.DeRham.BasisCovector
import FEEC.DeRham.BoxDecomp
import FEEC.DeRham.TestForm

/-!
# Weak exterior derivatives of tensor-product forms

* `FEEC.integral_mul_fderiv_eq`: integration by parts along a direction `e` for a function
  `u(⟪e, x⟫) r(x)` with `u` Lipschitz and piecewise differentiable and `r` invariant along `e`.
* `FEEC.codiff_eq_sum_basis`: the codifferential can be computed in any orthonormal basis.
* `FEEC.hasWeakExtDeriv_prod_smul`: on a box, the form `(∏ᵢ uᵢ(⟪eᵢ, x⟫)) α` has weak exterior
  derivative `∑ᵢ uᵢ'(⟪eᵢ, x⟫) ∏_{j ≠ i} uⱼ(⟪eⱼ, x⟫) eᵢ♭ ∧ α`, provided for each `i` either
  `eᵢ♭ ∧ α = 0` or `uᵢ` is Lipschitz with derivative `uᵢ'` away from finitely many points.
-/

namespace FEEC

open MeasureTheory

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {n k : ℕ}

/-- Integration by parts along the direction `e`. -/
theorem integral_mul_fderiv_eq {e : E} (he : ‖e‖ = 1) {a b : ℝ} {u u' : ℝ → ℝ} {K : NNReal}
    (hu : LipschitzWith K u) (hu'm : Measurable u') (Z : Finset ℝ)
    (hd : ∀ t ∈ Set.Ioo a b, t ∉ Z → HasDerivAt u (u' t) t)
    {r : E → ℝ} (hr : Measurable r) {Cr : ℝ} (hrb : ∀ x, |r x| ≤ Cr)
    (hre : ∀ x (t : ℝ), r (x + t • e) = r x)
    {f : E → ℝ} (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (hfs : ∀ x ∈ tsupport f, ⟪e, x⟫ ∈ Set.Ioo a b) :
    ∫ x, u ⟪e, x⟫ * r x * fderiv ℝ f x e = - ∫ x, u' ⟪e, x⟫ * r x * f x := by
  sorry

/-- The codifferential in an arbitrary orthonormal basis. -/
theorem codiff_eq_sum_basis {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ E)
    (φ : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ) (x : E) :
    codiff φ x = -∑ i, (fderiv ℝ φ x (e i)).curryLeft (e i) := by
  sorry

/-- **Weak exterior derivative of a tensor-product form on a box.** -/
theorem hasWeakExtDeriv_prod_smul (e : OrthonormalBasis (Fin n) ℝ E) (a b : Fin n → ℝ)
    (u u' : Fin n → ℝ → ℝ) (α : E [⋀^Fin k]→L[ℝ] ℝ)
    (hu : ∀ i, Measurable (u i)) (hub : ∀ i, ∃ C, ∀ t, |u i t| ≤ C)
    (hu' : ∀ i, Measurable (u' i)) (hu'b : ∀ i, ∃ C, ∀ t, |u' i t| ≤ C)
    (hd : ∀ i, wedgeLeft (e i) α = 0 ∨ ((∃ K, LipschitzWith K (u i)) ∧
      ∃ Z : Finset ℝ, ∀ t ∈ Set.Ioo (a i) (b i), t ∉ Z → HasDerivAt (u i) (u' i t) t))
    (ω : L2Form (box e a b) k)
    (hω : ω =ᵐ[volume.restrict (box e a b)]
      fun x => Covector.ofAlt ((∏ i, u i ⟪e i, x⟫) • α))
    (η : L2Form (box e a b) (k + 1))
    (hη : η =ᵐ[volume.restrict (box e a b)] fun x => Covector.ofAlt
      (∑ i, (u' i ⟪e i, x⟫ * ∏ j ∈ Finset.univ.erase i, u j ⟪e j, x⟫) • wedgeLeft (e i) α)) :
    HasWeakExtDeriv ω η := by
  sorry

end FEEC
