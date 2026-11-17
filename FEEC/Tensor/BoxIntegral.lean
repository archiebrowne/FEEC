/-
Integrals of product functions over a box.
-/
import FEEC.DeRham.BoxDecomp

namespace FEEC

open MeasureTheory

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {n : ℕ}

/-- The measurable equivalence `E ≃ᵐ (Fin n → ℝ)` given by the coordinates `x ↦ (⟪e i, x⟫)ᵢ`. -/
noncomputable def coordEquiv (e : OrthonormalBasis (Fin n) ℝ E) : E ≃ᵐ (Fin n → ℝ) :=
  e.repr.toHomeomorph.toMeasurableEquiv.trans (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm

theorem coordEquiv_apply (e : OrthonormalBasis (Fin n) ℝ E) (x : E) (i : Fin n) :
    coordEquiv e x i = ⟪e i, x⟫ := by
  simp [coordEquiv, OrthonormalBasis.repr_apply_apply]

theorem measurePreserving_coordEquiv (e : OrthonormalBasis (Fin n) ℝ E) :
    MeasurePreserving (coordEquiv e) :=
  (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n)).comp
    e.measurePreserving_repr

theorem preimage_pi_coordEquiv (e : OrthonormalBasis (Fin n) ℝ E) (a b : Fin n → ℝ) :
    box e a b = coordEquiv e ⁻¹' (Set.univ.pi fun i => Set.Ioo (a i) (b i)) := by
  ext x
  simp [box, coordEquiv_apply]

/-- The integral over a box of a product of functions of the coordinates is the product of
the one-dimensional integrals. -/
theorem integral_box_prod (e : OrthonormalBasis (Fin n) ℝ E) (a b : Fin n → ℝ)
    (f : Fin n → ℝ → ℝ) :
    ∫ x in box e a b, ∏ i, f i ⟪e i, x⟫ = ∏ i, ∫ t in Set.Ioo (a i) (b i), f i t := by
  have h := measurePreserving_coordEquiv e
  rw [preimage_pi_coordEquiv]
  have := h.setIntegral_preimage_emb (coordEquiv e).measurableEmbedding
    (fun y => ∏ i, f i (y i)) (Set.univ.pi fun i => Set.Ioo (a i) (b i))
  simp_rw [coordEquiv_apply] at this
  rw [this, volume_pi, Measure.restrict_pi_pi]
  rw [integral_fintype_prod_eq_prod (fun i t => f i t)
    (μ := fun i => volume.restrict (Set.Ioo (a i) (b i)))]

theorem measurableSet_box (e : OrthonormalBasis (Fin n) ℝ E) (a b : Fin n → ℝ) :
    MeasurableSet (box e a b) := (isOpen_box e a b).measurableSet

/-- A box has finite volume. -/
theorem volume_box_lt_top (e : OrthonormalBasis (Fin n) ℝ E) (a b : Fin n → ℝ) :
    volume (box e a b) < ⊤ := by
  rw [preimage_pi_coordEquiv, (measurePreserving_coordEquiv e).measure_preimage_equiv,
    volume_pi_pi]
  exact ENNReal.prod_lt_top (fun i _ => by simp)

end FEEC
