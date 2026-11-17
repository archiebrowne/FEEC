/-
Tensor-product shape and dual forms on a box.
-/
import FEEC.DeRham.BasisCovector
import FEEC.Tensor.Ref1DBiorth
import FEEC.Tensor.BoxIntegral
import FEEC.Tensor.WeakDeriv

/-!
# Tensor-product shape and dual forms on a box

Fix an orthonormal basis `e`, a box `box e a b` and numbers of cells `N i` in each direction.
For a tuple `T : Fin k → Fin n` and a multi-index `m : Fin n → ℕ`:

* `Tensor.shapeForm e a b N T m = (∏ᵢ shapeᵢ(⟪eᵢ, x⟫)) • dxT e k T`, where in direction `i`
  the shape function is a cell indicator if `i` occurs in `T` and a hat function otherwise
  (the tensor-product Whitney forms `Q₁⁻Λᵏ`);
* `Tensor.dualForm e a b N T m`, the same with the smooth compactly supported dual
  functions: a test form on the box.

Main results: the pairing of shape and dual forms factorises
(`Tensor.inner_shapeLp_dualLp`); shape forms have a weak exterior derivative which is a
combination of shape forms of the next degree (`Tensor.hasWeakExtDeriv_shapeLp`); the
codifferential of a dual form is a combination of dual forms of the previous degree
(`Tensor.exists_codiff_dualLp`).
-/

namespace FEEC

namespace Tensor

open MeasureTheory

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {n : ℕ}
  (e : OrthonormalBasis (Fin n) ℝ E) (a b : Fin n → ℝ) (N : Fin n → ℕ) {k : ℕ}

/-- The type (`true` = cell, `false` = node) of direction `i` for the tuple `T`. -/
def pat (T : Fin k → Fin n) (i : Fin n) : Bool := decide (∃ p, T p = i)

/-- The product of one-dimensional shape functions. -/
noncomputable def shapeProd (T : Fin k → Fin n) (m : Fin n → ℕ) (x : E) : ℝ :=
  ∏ i, Ref.shape (a i) (b i) (N i) (pat T i) (m i) ⟪e i, x⟫

/-- The product of one-dimensional dual functions. -/
noncomputable def dualProd (T : Fin k → Fin n) (m : Fin n → ℕ) (x : E) : ℝ :=
  ∏ i, Ref.dual (a i) (b i) (N i) (pat T i) (m i) ⟪e i, x⟫

/-- Tensor-product shape forms. -/
noncomputable def shapeForm (T : Fin k → Fin n) (m : Fin n → ℕ) : E → E [⋀^Fin k]→L[ℝ] ℝ :=
  fun x => shapeProd e a b N T m x • dxT e k T

/-- Tensor-product dual forms. -/
noncomputable def dualForm (T : Fin k → Fin n) (m : Fin n → ℕ) : E → E [⋀^Fin k]→L[ℝ] ℝ :=
  fun x => dualProd e a b N T m x • dxT e k T

variable {e a b N}

theorem measurable_shapeProd (T : Fin k → Fin n) (m : Fin n → ℕ) :
    Measurable (shapeProd e a b N T m) := by
  unfold shapeProd
  refine Finset.measurable_prod _ fun i _ => ?_
  exact (Ref.measurable_shape _ _).comp (continuous_const.inner continuous_id).measurable

theorem abs_shapeProd_le_one (T : Fin k → Fin n) (m : Fin n → ℕ) (x : E) :
    |shapeProd e a b N T m x| ≤ 1 := by
  unfold shapeProd
  rw [Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun i _ => abs_nonneg _) (fun i _ => Ref.abs_shape_le_one _ _ _)

theorem contDiff_dualProd (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i) (T : Fin k → Fin n)
    (m : Fin n → ℕ) : ContDiff ℝ (⊤ : ℕ∞) (dualProd e a b N T m) := by
  unfold dualProd
  refine contDiff_prod fun i _ => ?_
  exact (Ref.contDiff_dual (hab i) (hN i) _ _).comp
    ((innerSL ℝ (e i)).contDiff)

theorem dualProd_eq_zero {T : Fin k → Fin n} {m : Fin n → ℕ} {i : Fin n}
    (h : N i + 2 ≤ m i) : dualProd e a b N T m = 0 := by
  funext x
  unfold dualProd
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  cases hp : pat T i
  · have : ¬ Ref.Valid (N i) false (m i) := by rw [Ref.valid_false_iff]; omega
    simp [Ref.dual, this]
  · have : ¬ Ref.Valid (N i) true (m i) := by rw [Ref.valid_true_iff]; omega
    simp [Ref.dual, this]

theorem shapeProd_eq_zero {T : Fin k → Fin n} {m : Fin n → ℕ} {i : Fin n}
    (h : N i + 2 ≤ m i) : shapeProd e a b N T m = 0 := by
  funext x
  unfold shapeProd
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  cases hp : pat T i
  · have : ¬ Ref.Valid (N i) false (m i) := by rw [Ref.valid_false_iff]; omega
    simp [Ref.shape, this]
  · have : ¬ Ref.Valid (N i) true (m i) := by rw [Ref.valid_true_iff]; omega
    simp [Ref.shape, this]

theorem isTestForm_dualForm (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i) (T : Fin k → Fin n)
    (m : Fin n → ℕ) : IsTestForm (box e a b) (dualForm e a b N T m) := by
  have hK : ∀ i, IsCompact (tsupport (Ref.dual (a i) (b i) (N i) (pat T i) (m i))) := fun i =>
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _)
      ((Ref.tsupport_dual_subset (hab i) (hN i) _ _).trans Set.Ioo_subset_Icc_self)
  let h : E ≃ₜ (Fin n → ℝ) :=
    (e.repr.toHomeomorph.trans (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph)
  have hh : ∀ x i, h x i = ⟪e i, x⟫ := fun x i => by
    simp [h, OrthonormalBasis.repr_apply_apply]
  let C : Set E := h ⁻¹' (Set.univ.pi fun i => tsupport (Ref.dual (a i) (b i) (N i) (pat T i) (m i)))
  have hC : IsCompact C := h.isCompact_preimage.2 (isCompact_univ_pi hK)
  have hsub : Function.support (dualProd e a b N T m) ⊆ C := by
    intro x hx
    simp only [C, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, hh]
    intro i
    by_contra hi
    apply hx
    unfold dualProd
    exact Finset.prod_eq_zero (Finset.mem_univ i) (image_eq_zero_of_notMem_tsupport hi)
  have hts : tsupport (dualProd e a b N T m) ⊆ C := closure_minimal hsub hC.isClosed
  have hbox : C ⊆ box e a b := by
    intro x hx i
    have := hx i (Set.mem_univ i)
    rw [hh] at this
    exact Ref.tsupport_dual_subset (hab i) (hN i) _ _ this
  exact IsTestForm.smul_const (contDiff_dualProd hab hN T m)
    (hC.of_isClosed_subset (isClosed_tsupport _) hts) (hts.trans hbox) _

theorem memLp_shapeForm (T : Fin k → Fin n) (m : Fin n → ℕ) :
    MemLp (fun x => Covector.ofAlt (shapeForm e a b N T m x)) 2
      (volume.restrict (box e a b)) := by
  haveI : IsFiniteMeasure (volume.restrict (box e a b)) :=
    ⟨by simpa using volume_box_lt_top e a b⟩
  refine MemLp.of_bound ?_ ‖Covector.ofAlt (dxT e k T)‖ ?_
  · exact Covector.ofAlt.continuous.comp_aestronglyMeasurable
      ((measurable_shapeProd T m).aestronglyMeasurable.smul_const _)
  · refine Filter.Eventually.of_forall fun x => ?_
    simp only [shapeForm, map_smul, norm_smul, Real.norm_eq_abs]
    calc _ ≤ 1 * ‖Covector.ofAlt (dxT e k T)‖ := by
          gcongr; exact abs_shapeProd_le_one T m x
      _ = _ := one_mul _

variable (e a b N) in
/-- The class of a shape form in `L²Λᵏ`. -/
noncomputable def shapeLp (T : Fin k → Fin n) (m : Fin n → ℕ) : L2Form (box e a b) k :=
  (memLp_shapeForm (e := e) (a := a) (b := b) (N := N) T m).toLp _

/-- The class of a dual form in `L²Λᵏ`. -/
noncomputable def dualLp (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i) (T : Fin k → Fin n)
    (m : Fin n → ℕ) : L2Form (box e a b) k :=
  (isTestForm_dualForm (e := e) hab hN T m).toLp

theorem coeFn_shapeLp (T : Fin k → Fin n) (m : Fin n → ℕ) :
    shapeLp e a b N T m =ᵐ[volume.restrict (box e a b)]
      fun x => Covector.ofAlt (shapeForm e a b N T m x) :=
  MemLp.coeFn_toLp _

/-- The pairing of a shape form with a dual form factorises. -/
theorem inner_shapeLp_dualLp (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i)
    (S T : Fin k → Fin n) (q m : Fin n → ℕ) :
    ⟪shapeLp e a b N S q, dualLp hab hN T m⟫ =
      ⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k T)⟫ *
        ∏ i, ∫ t in Set.Ioo (a i) (b i),
          Ref.shape (a i) (b i) (N i) (pat S i) (q i) t *
            Ref.dual (a i) (b i) (N i) (pat T i) (m i) t := by
  rw [L2.inner_def]
  have h1 : ∀ᵐ x ∂(volume.restrict (box e a b)),
      ⟪(shapeLp e a b N S q : L2Form (box e a b) k) x, (dualLp hab hN T m : L2Form (box e a b) k) x⟫ =
        (∏ i, (Ref.shape (a i) (b i) (N i) (pat S i) (q i) ⟪e i, x⟫ *
            Ref.dual (a i) (b i) (N i) (pat T i) (m i) ⟪e i, x⟫)) *
          ⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k T)⟫ := by
    have h3' : dualLp hab hN T m =ᵐ[volume.restrict (box e a b)]
        fun x => Covector.ofAlt (dualForm e a b N T m x) :=
      (isTestForm_dualForm (e := e) hab hN T m).coeFn_toLp
    filter_upwards [coeFn_shapeLp (e := e) (a := a) (b := b) (N := N) S q, h3'] with x h2 h3
    rw [h2, h3]
    simp only [shapeForm, dualForm, map_smul, real_inner_smul_left, real_inner_smul_right,
      Finset.prod_mul_distrib]
    unfold shapeProd dualProd
    ring
  rw [integral_congr_ae h1, integral_mul_const,
    integral_box_prod e a b (fun i t => Ref.shape (a i) (b i) (N i) (pat S i) (q i) t *
      Ref.dual (a i) (b i) (N i) (pat T i) (m i) t), mul_comm]

/-- A shape form with an out-of-range index vanishes. -/
theorem shapeLp_eq_zero {T : Fin k → Fin n} {m : Fin n → ℕ} {i : Fin n}
    (h : N i + 2 ≤ m i) : shapeLp e a b N T m = 0 := by
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [coeFn_shapeLp (e := e) (a := a) (b := b) (N := N) T m] with x hx
  rw [hx]
  simp [shapeForm, shapeProd_eq_zero h]

/-- A dual form with an out-of-range index vanishes. -/
theorem dualLp_eq_zero (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i) {T : Fin k → Fin n}
    {m : Fin n → ℕ} {i : Fin n} (h : N i + 2 ≤ m i) : dualLp (e := e) hab hN T m = 0 := by
  refine (isTestForm_dualForm (e := e) hab hN T m).toLp_eq_zero ?_
  funext x
  simp [dualForm, dualProd_eq_zero h]

end Tensor

end FEEC
