/-
The tensor-product cochain projection on a box.
-/
import FEEC.Tensor.FormsDeriv
import FEEC.Tensor.Ref1DSchur
import FEEC.Tensor.Schur
import FEEC.Discrete.DualSystem
import FEEC.DeRham.PoincareLemma

/-!
# The tensor-product cochain projection

The shape forms `Tensor.shapeH` (elements of `HΛᵏ` of the box) and the dual forms
`Tensor.dualL`, indexed by `Tensor.Idx N k` (a tuple `T` and a multi-index), form a dual
system for the `L²` de Rham complex of the box with weights `(k!)⁻¹`
(`Tensor.isDualSystem`). The associated operators are bounded on `L²` by a constant depending
only on the dimension and the degree — not on the box or the mesh
(`Tensor.exists_norm_dualOp_le`).
-/

namespace FEEC

namespace Tensor

open MeasureTheory

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {n : ℕ}
  {e : OrthonormalBasis (Fin n) ℝ E} {a b : Fin n → ℝ} {N : Fin n → ℕ}

/-- Indices of shape forms of degree `k`: a tuple of directions and a multi-index. -/
abbrev Idx (N : Fin n → ℕ) (k : ℕ) : Type := (Fin k → Fin n) × ((i : Fin n) → Fin (N i + 2))

/-- The shape forms as elements of `HΛᵏ`. -/
noncomputable def shapeH (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i) (k : ℕ) (p : Idx N k) :
    HΛ (box e a b) k :=
  ⟨WithLp.toLp 2 (shapeLp e a b N p.1 (fun i => (p.2 i : ℕ)), _),
    hasWeakExtDeriv_shapeLp hab hN p.1 (fun i => (p.2 i : ℕ))⟩

/-- The dual forms. -/
noncomputable def dualL (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i) (k : ℕ) (p : Idx N k) :
    L2Form (box e a b) k :=
  dualLp (e := e) hab hN p.1 (fun i => (p.2 i : ℕ))

theorem toL2_shapeH (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i) (k : ℕ) (p : Idx N k) :
    HΛ.toL2 (shapeH (e := e) hab hN k p) = shapeLp e a b N p.1 (fun i => (p.2 i : ℕ)) := rfl

/-- **The shape and dual forms are a dual system** for the de Rham complex of the box. -/
theorem isDualSystem (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i) :
    (deRhamComplex (isOpen_box e a b)).IsDualSystem (shapeH (e := e) hab hN)
      (dualL (e := e) hab hN) (fun k => ((k.factorial : ℝ))⁻¹) := by
  sorry

end Tensor

end FEEC
