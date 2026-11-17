/-
Uniform L² bound for the tensor-product projection.
-/
import FEEC.Tensor.Projection

namespace FEEC

namespace Tensor

open MeasureTheory

local notation "⟪" x ", " y "⟫" => inner ℝ x y

lemma sum_pi_prod_le {n : ℕ} (N : Fin n → ℕ) (g : Fin n → ℕ → ℝ) (K : ℝ)
    (hg : ∀ i j, 0 ≤ g i j) (hK : ∀ i, ∑ j ∈ Finset.range (N i + 2), g i j ≤ K) :
    ∑ q : (i : Fin n) → Fin (N i + 2), ∏ i, g i (q i) ≤ K ^ n := by
  rw [← Fintype.prod_sum (fun i (j : Fin (N i + 2)) => g i j)]
  calc ∏ i, ∑ j : Fin (N i + 2), g i j ≤ ∏ _i : Fin n, K := by
        refine Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun j _ => hg _ _) fun i _ => ?_
        rw [Fin.sum_univ_eq_sum_range (fun j => g i j) (N i + 2)]
        exact hK i
    _ = K ^ n := by simp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {n : ℕ}
  {e : OrthonormalBasis (Fin n) ℝ E} {a b : Fin n → ℝ} {N : Fin n → ℕ}

lemma dualProd_bound (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i) {k : ℕ} (T : Fin k → Fin n)
    (m : Fin n → ℕ) : ∃ C, ∀ y, |dualProd e a b N T m y| ≤ C := by
  have : ∀ i, ∃ C, ∀ t, |Ref.dual (a i) (b i) (N i) (pat T i) (m i) t| ≤ C := fun i => by
    have hK : HasCompactSupport (Ref.dual (a i) (b i) (N i) (pat T i) (m i)) :=
      IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _)
        ((Ref.tsupport_dual_subset (hab i) (hN i) _ _).trans Set.Ioo_subset_Icc_self)
    obtain ⟨C, hC⟩ := (Ref.contDiff_dual (hab i) (hN i) _ _).continuous.bounded_above_of_compact_support hK
    exact ⟨C, fun t => by simpa using hC t⟩
  choose C hC using this
  refine ⟨∏ i, C i, fun y => ?_⟩
  unfold dualProd
  rw [Finset.abs_prod]
  exact Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) fun i _ => hC i _

/-- The Schur estimate for the operator of a fixed tuple `T`. -/
lemma norm_sum_shape_le {K₁ : ℝ} (hK₁ : 0 ≤ K₁)
    (hS : ∀ (a b : ℝ) (N : ℕ), a < b → 0 < N → ∀ s : Bool,
      (∀ x, ∑ j ∈ Finset.range (N + 2),
        |Ref.shape a b N s j x| * ∫ y in Set.Ioo a b, |Ref.dual a b N s j y| ≤ K₁) ∧
      (∀ y, ∑ j ∈ Finset.range (N + 2),
        (∫ x in Set.Ioo a b, |Ref.shape a b N s j x|) * |Ref.dual a b N s j y| ≤ K₁))
    (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i) {k : ℕ} (T : Fin k → Fin n)
    (w : L2Form (box e a b) k) :
    ‖∑ q : (i : Fin n) → Fin (N i + 2),
        ⟪w, dualLp (e := e) hab hN T (fun i => (q i : ℕ))⟫ •
          shapeLp e a b N T (fun i => (q i : ℕ))‖ ≤ K₁ ^ n * ‖w‖ := by
  haveI : IsFiniteMeasure (volume.restrict (box e a b)) :=
    ⟨by simpa using volume_box_lt_top e a b⟩
  have hα := norm_ofAlt_dxT_le e T
  have hA : ∀ q : (i : Fin n) → Fin (N i + 2),
      shapeLp e a b N T (fun i => (q i : ℕ)) =ᵐ[volume.restrict (box e a b)]
        fun x => shapeProd e a b N T (fun i => (q i : ℕ)) x • Covector.ofAlt (dxT e k T) := by
    intro q
    filter_upwards [coeFn_shapeLp (e := e) (a := a) (b := b) (N := N) T (fun i => (q i : ℕ))]
      with x hx
    rw [hx]
    simp [shapeForm]
  have hB : ∀ q : (i : Fin n) → Fin (N i + 2),
      dualLp (e := e) hab hN T (fun i => (q i : ℕ)) =ᵐ[volume.restrict (box e a b)]
        fun x => dualProd e a b N T (fun i => (q i : ℕ)) x • Covector.ofAlt (dxT e k T) := by
    intro q
    filter_upwards [(isTestForm_dualForm (e := e) hab hN T (fun i => (q i : ℕ))).coeFn_toLp]
      with x hx
    rw [dualLp, hx]
    simp [dualForm]
  have ha : ∀ q : (i : Fin n) → Fin (N i + 2),
      Integrable (shapeProd e a b N T (fun i => (q i : ℕ))) (volume.restrict (box e a b)) :=
    fun q => Integrable.of_bound (measurable_shapeProd _ _).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun x => by simpa using abs_shapeProd_le_one _ _ x)
  have hbb : ∀ q : (i : Fin n) → Fin (N i + 2),
      ∃ C, ∀ y, |dualProd e a b N T (fun i => (q i : ℕ)) y| ≤ C :=
    fun q => dualProd_bound hab hN T _
  have hb : ∀ q : (i : Fin n) → Fin (N i + 2),
      Integrable (dualProd e a b N T (fun i => (q i : ℕ))) (volume.restrict (box e a b)) := by
    intro q
    obtain ⟨C, hC⟩ := hbb q
    exact Integrable.of_bound (contDiff_dualProd hab hN T _).continuous.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun x => by simpa using hC x)
  have h1 : ∀ᵐ x ∂(volume.restrict (box e a b)),
      ∑ q : (i : Fin n) → Fin (N i + 2), |shapeProd e a b N T (fun i => (q i : ℕ)) x| *
        ∫ y, |dualProd e a b N T (fun i => (q i : ℕ)) y| ∂(volume.restrict (box e a b)) ≤ K₁ ^ n := by
    refine Filter.Eventually.of_forall fun x => ?_
    have : ∀ q : (i : Fin n) → Fin (N i + 2),
        |shapeProd e a b N T (fun i => (q i : ℕ)) x| *
          ∫ y, |dualProd e a b N T (fun i => (q i : ℕ)) y| ∂(volume.restrict (box e a b)) =
        ∏ i, (fun i (j : ℕ) => |Ref.shape (a i) (b i) (N i) (pat T i) j ⟪e i, x⟫| *
          ∫ t in Set.Ioo (a i) (b i), |Ref.dual (a i) (b i) (N i) (pat T i) j t|) i (q i : ℕ) := by
      intro q
      have e1 : ∫ y, |dualProd e a b N T (fun i => (q i : ℕ)) y| ∂(volume.restrict (box e a b)) =
          ∏ i, ∫ t in Set.Ioo (a i) (b i),
            |Ref.dual (a i) (b i) (N i) (pat T i) (q i : ℕ) t| := by
        rw [← integral_box_prod e a b
          (fun i t => |Ref.dual (a i) (b i) (N i) (pat T i) (q i : ℕ) t|)]
        simp only [dualProd, Finset.abs_prod]
      rw [e1]
      simp only [shapeProd, Finset.abs_prod, Finset.prod_mul_distrib]
    rw [Finset.sum_congr rfl fun q _ => this q]
    exact sum_pi_prod_le N (fun i (j : ℕ) => |Ref.shape (a i) (b i) (N i) (pat T i) j ⟪e i, x⟫| *
          ∫ t in Set.Ioo (a i) (b i), |Ref.dual (a i) (b i) (N i) (pat T i) j t|) K₁
      (fun i j => mul_nonneg (abs_nonneg _) (integral_nonneg fun _ => abs_nonneg _))
      fun i => (hS (a i) (b i) (N i) (hab i) (hN i) (pat T i)).1 _
  have h2 : ∀ᵐ y ∂(volume.restrict (box e a b)),
      ∑ q : (i : Fin n) → Fin (N i + 2),
        (∫ x, |shapeProd e a b N T (fun i => (q i : ℕ)) x| ∂(volume.restrict (box e a b))) *
          |dualProd e a b N T (fun i => (q i : ℕ)) y| ≤ K₁ ^ n := by
    refine Filter.Eventually.of_forall fun y => ?_
    have : ∀ q : (i : Fin n) → Fin (N i + 2),
        (∫ x, |shapeProd e a b N T (fun i => (q i : ℕ)) x| ∂(volume.restrict (box e a b))) *
          |dualProd e a b N T (fun i => (q i : ℕ)) y| =
        ∏ i, (fun i (j : ℕ) => (∫ t in Set.Ioo (a i) (b i),
            |Ref.shape (a i) (b i) (N i) (pat T i) j t|) *
          |Ref.dual (a i) (b i) (N i) (pat T i) j ⟪e i, y⟫|) i (q i : ℕ) := by
      intro q
      have e1 : ∫ x, |shapeProd e a b N T (fun i => (q i : ℕ)) x| ∂(volume.restrict (box e a b)) =
          ∏ i, ∫ t in Set.Ioo (a i) (b i),
            |Ref.shape (a i) (b i) (N i) (pat T i) (q i : ℕ) t| := by
        rw [← integral_box_prod e a b
          (fun i t => |Ref.shape (a i) (b i) (N i) (pat T i) (q i : ℕ) t|)]
        simp only [shapeProd, Finset.abs_prod]
      rw [e1]
      simp only [dualProd, Finset.abs_prod, Finset.prod_mul_distrib]
    rw [Finset.sum_congr rfl fun q _ => this q]
    exact sum_pi_prod_le N (fun i (j : ℕ) => (∫ t in Set.Ioo (a i) (b i),
            |Ref.shape (a i) (b i) (N i) (pat T i) j t|) *
          |Ref.dual (a i) (b i) (N i) (pat T i) j ⟪e i, y⟫|) K₁
      (fun i j => mul_nonneg (integral_nonneg fun _ => abs_nonneg _) (abs_nonneg _))
      fun i => (hS (a i) (b i) (N i) (hab i) (hN i) (pat T i)).2 _
  have key := norm_sum_inner_smul_le (μ := volume.restrict (box e a b))
    (fun q : (i : Fin n) → Fin (N i + 2) => shapeLp e a b N T (fun i => (q i : ℕ)))
    (fun q => dualLp (e := e) hab hN T (fun i => (q i : ℕ)))
    (fun q x => shapeProd e a b N T (fun i => (q i : ℕ)) x)
    (fun q x => dualProd e a b N T (fun i => (q i : ℕ)) x)
    (Covector.ofAlt (dxT e k T)) (Covector.ofAlt (dxT e k T)) hA hB ha hb hbb h1 h2 w
  have hα2 : ‖Covector.ofAlt (dxT e k T)‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hα
  have hM : 0 ≤ K₁ ^ n := pow_nonneg hK₁ n
  have hα4 : ‖Covector.ofAlt (dxT e k T)‖ ^ 2 * ‖Covector.ofAlt (dxT e k T)‖ ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg ‖Covector.ofAlt (dxT e k T)‖]
  have : ‖∑ q : (i : Fin n) → Fin (N i + 2),
        ⟪w, dualLp (e := e) hab hN T (fun i => (q i : ℕ))⟫ •
          shapeLp e a b N T (fun i => (q i : ℕ))‖ ^ 2 ≤ (K₁ ^ n * ‖w‖) ^ 2 := by
    refine key.trans ?_
    have e1 : ‖Covector.ofAlt (dxT e k T)‖ ^ 2 * ‖Covector.ofAlt (dxT e k T)‖ ^ 2 * K₁ ^ n *
        K₁ ^ n * ‖w‖ ^ 2 = (‖Covector.ofAlt (dxT e k T)‖ ^ 2 * ‖Covector.ofAlt (dxT e k T)‖ ^ 2) *
          ((K₁ ^ n * ‖w‖) ^ 2) := by ring
    rw [e1]
    calc _ ≤ 1 * ((K₁ ^ n * ‖w‖) ^ 2) :=
          mul_le_mul_of_nonneg_right hα4 (sq_nonneg _)
      _ = _ := one_mul _
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))
    two_ne_zero).1 this

/-- Explicit form of the `L²` bound, in terms of the constant of the one-dimensional Schur test. -/
lemma norm_dualOp_le_explicit {K₁ : ℝ} (hK₁ : 0 ≤ K₁)
    (hS : ∀ (a b : ℝ) (N : ℕ), a < b → 0 < N → ∀ s : Bool,
      (∀ x, ∑ j ∈ Finset.range (N + 2),
        |Ref.shape a b N s j x| * ∫ y in Set.Ioo a b, |Ref.dual a b N s j y| ≤ K₁) ∧
      (∀ y, ∑ j ∈ Finset.range (N + 2),
        (∫ x in Set.Ioo a b, |Ref.shape a b N s j x|) * |Ref.dual a b N s j y| ≤ K₁))
    (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i) (k : ℕ) (w : L2Form (box e a b) k) :
    ‖(deRhamComplex (isOpen_box e a b)).dualOp (shapeH (e := e) hab hN)
        (dualL (e := e) hab hN) (fun k => ((k.factorial : ℝ))⁻¹) k w‖ ≤
      ((k.factorial : ℝ)⁻¹ * ((n : ℝ) ^ k * K₁ ^ n)) * ‖w‖ := by
  rw [HilbertComplex.dualOp_apply]
  have hsum : ∑ p : Idx N k, ⟪dualL (e := e) hab hN k p, w⟫ •
        (deRhamComplex (isOpen_box e a b)).ι k (shapeH (e := e) hab hN k p) =
      ∑ T : Fin k → Fin n, ∑ q : (i : Fin n) → Fin (N i + 2),
        ⟪w, dualLp (e := e) hab hN T (fun i => (q i : ℕ))⟫ •
          shapeLp e a b N T (fun i => (q i : ℕ)) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun T _ => Finset.sum_congr rfl fun q _ => ?_
    rw [real_inner_comm]
    rfl
  rw [hsum, norm_smul]
  have hk : ‖((k.factorial : ℝ))⁻¹‖ = (k.factorial : ℝ)⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [hk, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc _ ≤ ∑ T : Fin k → Fin n, ‖∑ q : (i : Fin n) → Fin (N i + 2),
        ⟪w, dualLp (e := e) hab hN T (fun i => (q i : ℕ))⟫ •
          shapeLp e a b N T (fun i => (q i : ℕ))‖ := norm_sum_le _ _
    _ ≤ ∑ _T : Fin k → Fin n, K₁ ^ n * ‖w‖ :=
        Finset.sum_le_sum fun T _ => norm_sum_shape_le hK₁ hS hab hN T w
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-- **Uniform `L²` bound**: the operators of the dual system are bounded by constants
depending only on the dimension `n` and the degree `k`. -/
theorem exists_norm_dualOp_le (n : ℕ) : ∃ K : ℕ → ℝ, (∀ k, 0 ≤ K k) ∧
    ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E] (e : OrthonormalBasis (Fin n) ℝ E)
      (a b : Fin n → ℝ) (N : Fin n → ℕ) (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i) (k : ℕ)
      (w : L2Form (box e a b) k),
      ‖(deRhamComplex (isOpen_box e a b)).dualOp (shapeH (e := e) hab hN)
        (dualL (e := e) hab hN) (fun k => ((k.factorial : ℝ))⁻¹) k w‖ ≤ K k * ‖w‖ := by
  obtain ⟨K₁, hK₁, hS⟩ := Ref.exists_schur_const
  exact ⟨fun k => (k.factorial : ℝ)⁻¹ * ((n : ℝ) ^ k * K₁ ^ n), fun k => by positivity,
    fun e a b N hab hN k w => norm_dualOp_le_explicit hK₁ hS hab hN k w⟩

/-- The constant of the degree-uniform `L²` bound. -/
noncomputable def uniformConst (n : ℕ) : ℝ :=
  Real.exp n * (Ref.exists_schur_const.choose) ^ n

lemma uniformConst_nonneg (n : ℕ) : 0 ≤ uniformConst n :=
  mul_nonneg (Real.exp_pos _).le (pow_nonneg Ref.exists_schur_const.choose_spec.1 n)

/-- The operators of the dual system are bounded uniformly in the degree. -/
lemma norm_dualOp_le_uniformConst (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i) (k : ℕ)
    (w : L2Form (box e a b) k) :
    ‖(deRhamComplex (isOpen_box e a b)).dualOp (shapeH (e := e) hab hN)
        (dualL (e := e) hab hN) (fun k => ((k.factorial : ℝ))⁻¹) k w‖ ≤
      uniformConst n * ‖w‖ := by
  obtain ⟨hK₁, hS⟩ := Ref.exists_schur_const.choose_spec
  refine (norm_dualOp_le_explicit hK₁ hS hab hN k w).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  have h := Real.pow_div_factorial_le_exp (n : ℝ) (Nat.cast_nonneg n) k
  have : (k.factorial : ℝ)⁻¹ * ((n : ℝ) ^ k * Ref.exists_schur_const.choose ^ n) =
      ((n : ℝ) ^ k / k.factorial) * Ref.exists_schur_const.choose ^ n := by ring
  rw [this]
  exact mul_le_mul_of_nonneg_right h (pow_nonneg hK₁ n)

/-- A bound on the operators of the dual system which is uniform in the degree. -/
theorem exists_uniform_norm_dualOp_le (n : ℕ) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E] (e : OrthonormalBasis (Fin n) ℝ E)
      (a b : Fin n → ℝ) (N : Fin n → ℕ) (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i) (k : ℕ)
      (w : L2Form (box e a b) k),
      ‖(deRhamComplex (isOpen_box e a b)).dualOp (shapeH (e := e) hab hN)
        (dualL (e := e) hab hN) (fun k => ((k.factorial : ℝ))⁻¹) k w‖ ≤ K * ‖w‖ :=
  ⟨uniformConst n, uniformConst_nonneg n, fun e a b N hab hN k w =>
    norm_dualOp_le_uniformConst hab hN k w⟩

end Tensor

end FEEC
