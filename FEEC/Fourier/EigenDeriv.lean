/-
Weak exterior derivatives of eigenforms, and integration by parts against them.
-/
import FEEC.Fourier.Eigenforms

/-!
# `d` and `δ` on eigenforms

* `Fourier.hasWeakExtDeriv_synth`: `d (synth m α) = synth m (ξ_m ∧ α)`.
* `Fourier.inner_d_synth`: **integration by parts against eigenforms**: for every `w ∈ HΛᵏ` of
  the box, `⟪dw, synth m γ⟫ = ⟪w, synth m (ξ_m ⌟ γ)⟫`, although `synth m γ` is not compactly
  supported (its normal components vanish on the boundary).
* `Fourier.coef_d`: hence `(dw)^(m) = ξ_m ∧ ŵ(m)`.
-/

namespace FEEC

namespace Fourier

open MeasureTheory Tensor

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {n : ℕ}
  {e : OrthonormalBasis (Fin n) ℝ E} {a b : Fin n → ℝ} {k : ℕ}

theorem hasWeakExtDeriv_synth (hab : ∀ i, a i < b i) (m : Fin n → ℕ) (α : Covector E k) :
    HasWeakExtDeriv (synth e a b m α) (synth e a b m (cwedge (xi e a b m) α)) := by
  sorry

variable (e a b) in
/-- `synth m α` as an element of `HΛᵏ`. -/
noncomputable def synthH (hab : ∀ i, a i < b i) (m : Fin n → ℕ) (α : Covector E k) :
    HΛ (box e a b) k :=
  ⟨WithLp.toLp 2 (synth e a b m α, synth e a b m (cwedge (xi e a b m) α)),
    hasWeakExtDeriv_synth hab m α⟩

/-- **Integration by parts against eigenforms.** -/
theorem inner_d_synth (hab : ∀ i, a i < b i) (w : HΛ (box e a b) k) (m : Fin n → ℕ)
    (γ : Covector E (k + 1)) :
    ⟪HΛ.toL2 (HΛ.d w), synth e a b m γ⟫ =
      ⟪HΛ.toL2 w, synth e a b m (ccontr (xi e a b m) γ)⟫ := by
  sorry

theorem coef_d (hab : ∀ i, a i < b i) (w : HΛ (box e a b) k) (m : Fin n → ℕ) :
    coef e a b (HΛ.toL2 (HΛ.d w)) m = cwedge (xi e a b m) (coef e a b (HΛ.toL2 w) m) := by
  sorry

end Fourier

end FEEC
