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
  show u ∈ Submodule.span ℝ (Set.range (shapeH (e := e) hab hN k)) ↔ _
  constructor
  · intro hu
    have := Submodule.mem_map_of_mem
      (f := (HΛ.toL2 : HΛ (box e a b) k →L[ℝ] L2Form (box e a b) k).toLinearMap) hu
    rw [Submodule.map_span, ← Set.range_comp] at this
    exact this
  · intro hu
    obtain ⟨γ, hγ⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hu
    have : u = ∑ p, γ p • shapeH (e := e) hab hN k p := by
      refine HΛ.toL2_injective (isOpen_box e a b) ?_
      rw [map_sum]
      simp only [map_smul]
      exact hγ.symm
    rw [this]
    exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)

/-- The cochain projection is bounded uniformly in the mesh and in the box. -/
theorem exists_norm_projection_le (n : ℕ) : ∃ K : ℕ → ℝ, (∀ k, 0 ≤ K k) ∧
    ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E] (e : OrthonormalBasis (Fin n) ℝ E)
      (a b : Fin n → ℝ) (N : Fin n → ℕ) (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i) (k : ℕ),
      ‖(projection e hab hN).π k‖ ≤ K k := by
  obtain ⟨K, hK0, hK⟩ := exists_norm_dualOp_le n
  refine ⟨fun k => max (K k) (K (k + 1)), fun k => le_max_of_le_left (hK0 k),
    fun e a b N hab hN k => ?_⟩
  exact (isDualSystem hab hN).norm_dualProj_le hK0 (fun k w => hK e a b N hab hN k w) k

theorem exists_poincareConst (hab : ∀ i, a i < b i) (k : ℕ) :
    ∃ c, (((deRhamComplex (isOpen_box e a b)).segment k)).HasPoincareConst c :=
  (deRhamComplex (isOpen_box e a b)).exists_hasPoincareConst_segment
    (boxComplex_isClosed e hab) k

theorem norm_projection_le (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i) (j : ℕ) :
    ‖(projection e hab hN).π j‖ ≤ uniformConst n := by
  have := (isDualSystem (e := e) hab hN).norm_dualProj_le (K := fun _ => uniformConst n)
    (fun _ => uniformConst_nonneg n)
    (fun k w => norm_dualOp_le_uniformConst (e := e) hab hN k w) j
  exact this.trans_eq (max_self _)

theorem harmonic_eq_zero (hab : ∀ i, a i < b i) (k : ℕ) (x : HΛ (box e a b) (k + 1))
    (hx : x ∈ ((deRhamComplex (isOpen_box e a b)).segment k).harmonic) : x = 0 := by
  have hbot := box_harmonic_eq_bot e hab k
  rw [hbot] at hx
  exact (Submodule.mem_bot ℝ).1 hx

theorem exists_coboundary_decomp (hab : ∀ i, a i < b i) (k : ℕ) {c : ℝ}
    (hc : (((deRhamComplex (isOpen_box e a b)).segment k)).HasPoincareConst c)
    (u : HΛ (box e a b) (k + 1)) :
    ∃ b' ∈ ((deRhamComplex (isOpen_box e a b)).segment k).coboundaries,
      u - b' ∈ ((deRhamComplex (isOpen_box e a b)).segment k).cocyclesᗮ := by
  obtain ⟨b', hb', w, hw, huw, -⟩ :=
    ((deRhamComplex (isOpen_box e a b)).segment k).hodge_decomposition hc.isClosed_coboundaries u
  have hhp : (((deRhamComplex (isOpen_box e a b)).segment k).harmonicPart u :
      HΛ (box e a b) (k + 1)) = 0 := by
    exact harmonic_eq_zero e hab k _
      (((deRhamComplex (isOpen_box e a b)).segment k).harmonicPart u).2
  refine ⟨b', hb', ?_⟩
  have : u - b' = w := by rw [huw, hhp]; abel
  rw [this]; exact hw

set_option maxHeartbeats 400000 in
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
  obtain ⟨c, hc⟩ := exists_poincareConst e hab k
  refine ⟨max (stabilityConst (c * uniformConst n)) (errorConst c (uniformConst n)), fun N hN f => ?_⟩
  have hπ := norm_projection_le e hab hN
  refine ⟨?_, ?_⟩
  · obtain ⟨σh, uh, ph, hs, hn, hu⟩ :=
      HilbertComplex.galerkin_wellPosed (projection e hab hN) k hc hπ f
    exact ⟨σh, uh, ph, hs, hn.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (norm_nonneg _)), hu⟩
  · intro σ u p h σh uh ph hh τ v
    have hp : p = 0 := harmonic_eq_zero e hab k p h.harmonic
    obtain ⟨b', hb', hub⟩ := exists_coboundary_decomp e hab k hc u
    have hμ : ∀ r ∈ ((deRhamComplex (isOpen_box e a b)).segment k).harmonic,
        ‖r - (projection e hab hN).π (k + 1) r‖ ≤ 0 * ‖r‖ := by
      intro r hr
      have : r = 0 := harmonic_eq_zero e hab k r hr
      subst this
      simp
    have := HilbertComplex.galerkin_error_estimate (projection e hab hN) k hc hπ le_rfl hμ h hh
      hb' hub τ v 0 0
    subst hp
    simp only [zero_mul, add_zero, ZeroMemClass.coe_zero, sub_self, norm_zero] at this
    calc _ ≤ errorConst c (uniformConst n) * (‖σ - τ‖ + ‖u - v‖) := this
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _)
          (add_nonneg (norm_nonneg _) (norm_nonneg _))

end Tensor

end FEEC
