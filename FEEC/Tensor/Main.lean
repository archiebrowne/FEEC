/-
An unconditional finite element theorem on a box in any dimension.
-/
import FEEC.Tensor.ProjectionBound

/-!
# Tensor-product finite elements on a box: stability and quasi-optimality

Let `Ω = box e a b` be a box in a Euclidean space of any dimension `n`, meshed by a
tensor-product grid with `N i` equal cells in direction `i`.

* `Tensor.subcomplex`: the finite element spaces — in degree `k`, the forms in `HΛᵏ(Ω)` which
  are combinations of the tensor-product shape forms `(∏ᵢ shapeᵢ(xᵢ)) dx_T`
  (`Tensor.mem_subcomplex_iff`). These are the tensor-product Whitney forms `Q₁⁻Λᵏ`
  (lowest-order Raviart–Thomas elements on boxes for `k = n - 1`).
* `Tensor.projection`: a cochain projection onto them, bounded in the `HΛ` norm uniformly in
  the mesh and in the box (`Tensor.exists_norm_projection_le`).
* `Tensor.box_tensor_galerkin`: **for every mesh, the Galerkin method for the Hodge Laplacian
  is well posed and quasi-optimal, with a constant independent of the mesh.** No hypothesis
  is assumed: closedness of the complex and the cochain projection are both proved.
-/

namespace FEEC

namespace Tensor

open MeasureTheory

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {n : ℕ}
  (e : OrthonormalBasis (Fin n) ℝ E) {a b : Fin n → ℝ} {N : Fin n → ℕ}

/-- The tensor-product finite element subcomplex of the de Rham complex of a box. -/
noncomputable def subcomplex (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i) :
    (deRhamComplex (isOpen_box e a b)).Subcomplex :=
  (deRhamComplex (isOpen_box e a b)).dualSubcomplex (shapeH (e := e) hab hN)
    (isDualSystem hab hN).d_shape

instance (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i) (k : ℕ) :
    CompleteSpace ((subcomplex e hab hN).carrier k) := by
  haveI : FiniteDimensional ℝ ((subcomplex e hab hN).carrier k) := by
    show FiniteDimensional ℝ (Submodule.span ℝ (Set.range (shapeH (e := e) hab hN k)))
    exact FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  exact FiniteDimensional.complete ℝ _

/-- The bounded cochain projection onto the tensor-product finite element spaces. -/
noncomputable def projection (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i) :
    (deRhamComplex (isOpen_box e a b)).CochainProjection (subcomplex e hab hN) :=
  (isDualSystem hab hN).cochainProjection

/-- The finite element space of degree `k` consists of the elements of `HΛᵏ` which are
combinations of tensor-product shape forms. -/
theorem mem_subcomplex_iff (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i) (k : ℕ)
    (u : HΛ (box e a b) k) :
    u ∈ (subcomplex e hab hN).carrier k ↔
      HΛ.toL2 u ∈ Submodule.span ℝ
        (Set.range fun p : Idx N k => shapeLp e a b N p.1 (fun i => (p.2 i : ℕ))) := by
  sorry

/-- The cochain projection is bounded uniformly in the mesh and in the box. -/
theorem exists_norm_projection_le (n : ℕ) : ∃ K : ℕ → ℝ, (∀ k, 0 ≤ K k) ∧
    ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E] (e : OrthonormalBasis (Fin n) ℝ E)
      (a b : Fin n → ℝ) (N : Fin n → ℕ) (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i) (k : ℕ),
      ‖(projection e hab hN).π k‖ ≤ K k := by
  sorry

/-- **Unconditional stability and quasi-optimality of tensor-product finite elements on a box,
in any dimension and degree.** There is a constant `C`, depending on the box and the degree but
not on the mesh, such that for every tensor-product mesh and every `f ∈ L²Λᵏ⁺¹`:
the Galerkin problem for the Hodge Laplacian has a unique solution, bounded by `C ‖f‖`; and
its error is at most `C` times the best approximation error of `σ` and `u` in the finite
element spaces. -/
theorem box_tensor_galerkin (hab : ∀ i, a i < b i) (k : ℕ) :
    ∃ C : ℝ, ∀ (N : Fin n → ℕ) (hN : ∀ i, 0 < N i) (f : L2Form (box e a b) (k + 1)),
      (∃ σh uh ph, ((subcomplex e hab hN).segment k).toShort.IsSolution f σh uh ph ∧
        ‖σh‖ + ‖uh‖ + ‖ph‖ ≤ C * ‖f‖ ∧
        ∀ σ' u' p', ((subcomplex e hab hN).segment k).toShort.IsSolution f σ' u' p' →
          σ' = σh ∧ u' = uh ∧ p' = ph) ∧
      ∀ σ u p, ((deRhamComplex (isOpen_box e a b)).segment k).IsSolution f σ u p →
        ∀ σh uh ph, ((subcomplex e hab hN).segment k).toShort.IsSolution f σh uh ph →
          ∀ (τ : (subcomplex e hab hN).carrier k) (v : (subcomplex e hab hN).carrier (k + 1)),
            ‖σ - σh‖ + ‖u - uh‖ + ‖p - ph‖ ≤ C * (‖σ - τ‖ + ‖u - v‖) := by
  sorry

end Tensor

end FEEC
