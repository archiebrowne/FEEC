/-
Approximation by the scalar tensor-product quasi-interpolant on trigonometric polynomials.
-/
import FEEC.Tensor.Ref1DApprox
import FEEC.Fourier.CoordSchur
import FEEC.Fourier.TrigDensity

/-!
# The scalar tensor-product quasi-interpolant

For a pattern `s` (`true` = cell, `false` = node in each direction),
`quasiP s G x = ∑_q (∏ᵢ shapeᵢ(xᵢ)) ∫_box (∏ᵢ dualᵢ) G`. For `G` a trigonometric polynomial,
`‖G − quasiP s G‖² ≤ C h² ∑ᵢ ‖∂ᵢ G‖²` on the box, `C` depending only on `n`.

*Proof idea.* On products `G = ∏ gᵢ(xᵢ)`, `quasiP` is the product of the one-dimensional
operators (`integral_box_prod`), and `G − quasiP G = ∑ᵢ P₁ ⋯ P_{i−1} Rᵢ (∂ᵢ G)` where `Pⱼ`, `Rᵢ`
are integral operators in one coordinate (`coordOp`) with kernels
`∑_j shape_j(t) dual_j(τ)` and `Ref.rKer`; by linearity this holds for trigonometric
polynomials, and `coordOp_sq_le` bounds each term.
-/

namespace FEEC

namespace Tensor

set_option linter.unusedSectionVars false

open MeasureTheory

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {n : ℕ}

/-- Product of shape functions with pattern `s`. -/
noncomputable def shapeP (e : OrthonormalBasis (Fin n) ℝ E) (a b : Fin n → ℝ) (N : Fin n → ℕ)
    (s : Fin n → Bool) (q : Fin n → ℕ) (x : E) : ℝ :=
  ∏ i, Ref.shape (a i) (b i) (N i) (s i) (q i) ⟪e i, x⟫

/-- Product of dual functions with pattern `s`. -/
noncomputable def dualP (e : OrthonormalBasis (Fin n) ℝ E) (a b : Fin n → ℝ) (N : Fin n → ℕ)
    (s : Fin n → Bool) (q : Fin n → ℕ) (x : E) : ℝ :=
  ∏ i, Ref.dual (a i) (b i) (N i) (s i) (q i) ⟪e i, x⟫

/-- The scalar tensor-product quasi-interpolant. -/
noncomputable def quasiP (e : OrthonormalBasis (Fin n) ℝ E) (a b : Fin n → ℝ) (N : Fin n → ℕ)
    (s : Fin n → Bool) (G : E → ℝ) (x : E) : ℝ :=
  ∑ q : (i : Fin n) → Fin (N i + 2), shapeP e a b N s (fun i => q i) x *
    ∫ y in box e a b, dualP e a b N s (fun i => q i) y * G y

section prodpart

variable (e : OrthonormalBasis (Fin n) ℝ E) (a b : Fin n → ℝ) (N : Fin n → ℕ) (s : Fin n → Bool)

/-- Product function `x ↦ ∏ᵢ gᵢ ⟪eᵢ, x⟫`. -/
noncomputable def prodF (g : Fin n → ℝ → ℝ) (x : E) : ℝ := ∏ i, g i ⟪e i, x⟫

/-- The one-dimensional quasi-interpolant in direction `i`. -/
noncomputable def P1 (i : Fin n) (u : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (N i + 2), Ref.shape (a i) (b i) (N i) (s i) j t *
    ∫ y in Set.Ioo (a i) (b i), Ref.dual (a i) (b i) (N i) (s i) j y * u y

/-- The kernel of `P1`. -/
noncomputable def pK (i : Fin n) (t τ : ℝ) : ℝ :=
  ∑ l ∈ Finset.range (N i + 2), Ref.shape (a i) (b i) (N i) (s i) l t *
    Ref.dual (a i) (b i) (N i) (s i) l τ

theorem inner_orth (x : E) (c : ℝ) (i j : Fin n) :
    ⟪e i, x + c • e j⟫ = ⟪e i, x⟫ + if i = j then c else 0 := by
  have ho := orthonormal_iff_ite.1 e.orthonormal
  rw [inner_add_right, inner_smul_right, ho]
  by_cases h : i = j <;> simp [h]

theorem prodF_split (g : Fin n → ℝ → ℝ) (j : Fin n) (x : E) :
    prodF e g x = g j ⟪e j, x⟫ * ∏ i ∈ Finset.univ.erase j, g i ⟪e i, x⟫ := by
  unfold prodF
  rw [Finset.mul_prod_erase Finset.univ (fun i => g i ⟪e i, x⟫) (Finset.mem_univ j)]

theorem coordOp_prodF (j : Fin n) (k : ℝ → ℝ → ℝ) (g : Fin n → ℝ → ℝ) :
    coordOp e a b j k (prodF e g) = prodF e
      (Function.update g j (fun t => ∫ τ in Set.Ioo (a j) (b j), k t τ * g j τ)) := by
  funext x
  unfold coordOp
  rw [prodF_split e (Function.update g j _) j x]
  simp only [Function.update_self]
  have hrest : ∏ i ∈ Finset.univ.erase j, Function.update g j
      (fun t => ∫ τ in Set.Ioo (a j) (b j), k t τ * g j τ) i ⟪e i, x⟫ =
      ∏ i ∈ Finset.univ.erase j, g i ⟪e i, x⟫ := by
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [hrest, ← integral_mul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  show k ⟪e j, x⟫ τ * prodF e g (x + (τ - ⟪e j, x⟫) • e j) = _
  rw [prodF_split e g j]
  show _ = k ⟪e j, x⟫ τ * g j τ * _
  rw [mul_assoc]
  congr 2
  · simp [inner_orth]
  · refine Finset.prod_congr rfl fun i hi => ?_
    rw [inner_orth, if_neg (Finset.ne_of_mem_erase hi), add_zero]

theorem quasiP_prodF (g : Fin n → ℝ → ℝ) (x : E) :
    quasiP e a b N s (prodF e g) x = ∏ i, P1 a b N s i (g i) ⟪e i, x⟫ := by
  unfold quasiP P1
  have h1 : ∀ q : (i : Fin n) → Fin (N i + 2),
      shapeP e a b N s (fun i => q i) x *
        ∫ y in box e a b, dualP e a b N s (fun i => q i) y * prodF e g y =
      ∏ i, (Ref.shape (a i) (b i) (N i) (s i) (q i) ⟪e i, x⟫ *
        ∫ y in Set.Ioo (a i) (b i), Ref.dual (a i) (b i) (N i) (s i) (q i) y * g i y) := by
    intro q
    have : ∀ y, dualP e a b N s (fun i => q i) y * prodF e g y =
        ∏ i, (Ref.dual (a i) (b i) (N i) (s i) (q i) ⟪e i, y⟫ * g i ⟪e i, y⟫) := by
      intro y; unfold dualP prodF; rw [Finset.prod_mul_distrib]
    simp_rw [this]
    rw [integral_box_prod e a b (fun i t => Ref.dual (a i) (b i) (N i) (s i) (q i) t * g i t),
      shapeP, ← Finset.prod_mul_distrib]
  simp_rw [h1]
  rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum (fun i => (Finset.univ : Finset (Fin (N i + 2))))
    (fun i j => Ref.shape (a i) (b i) (N i) (s i) j ⟪e i, x⟫ *
        ∫ y in Set.Ioo (a i) (b i), Ref.dual (a i) (b i) (N i) (s i) j y * g i y)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.sum_range (fun j => Ref.shape (a i) (b i) (N i) (s i) j ⟪e i, x⟫ *
        ∫ y in Set.Ioo (a i) (b i), Ref.dual (a i) (b i) (N i) (s i) j y * g i y)]

theorem prodF_update (g : Fin n → ℝ → ℝ) (j : Fin n) (h : ℝ → ℝ) (x : E) :
    prodF e (Function.update g j h) x = h ⟪e j, x⟫ * ∏ i ∈ Finset.univ.erase j, g i ⟪e i, x⟫ := by
  rw [prodF_split e _ j x, Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

theorem P1_eq (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i) (i : Fin n) {u : ℝ → ℝ}
    (hu : Continuous u) (t : ℝ) :
    P1 a b N s i u t = ∫ τ in Set.Ioo (a i) (b i), pK a b N s i t τ * u τ := by
  unfold P1 pK
  simp_rw [Finset.sum_mul]
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl fun j _ => ?_
    simp_rw [mul_assoc]
    rw [integral_const_mul]
  · intro j _
    have : IntegrableOn (fun y => Ref.dual (a i) (b i) (N i) (s i) j y * u y) (Set.Ioo (a i) (b i)) :=
      (((Ref.contDiff_dual (hab i) (hN i) (s i) j).continuous.mul hu).integrable_of_hasCompactSupport
        ((Ref.hasCompactSupport_dual (hab i) (hN i) (s i) j).mul_right)).integrableOn
    simp_rw [mul_assoc]
    exact this.const_mul _

/-- One factor of the composition. -/
noncomputable def PK (m : ℕ) (F : E → ℝ) : E → ℝ :=
  if h : m < n then coordOp e a b ⟨m, h⟩ (pK a b N s ⟨m, h⟩) F else F

/-- Compositions of the first `m` projections. -/
noncomputable def Pcomp : ℕ → (E → ℝ) → E → ℝ
  | 0, F => F
  | m + 1, F => PK e a b N s m (Pcomp m F)

theorem Pcomp_prodF (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i) (v : Fin n → ℝ → ℝ) (m : ℕ)
    (hv : ∀ j : Fin n, j.val < m → Continuous (v j)) :
    Pcomp e a b N s m (prodF e v) =
      prodF e (fun j => if j.val < m then P1 a b N s j (v j) else v j) := by
  induction m with
  | zero => simp [Pcomp]
  | succ m ih =>
    have ih' := ih (fun j hj => hv j (by omega))
    simp only [Pcomp]
    rw [ih']
    unfold PK
    by_cases hm : m < n
    · rw [dif_pos hm, coordOp_prodF]
      congr 1
      funext j
      by_cases hj : j = ⟨m, hm⟩
      · subst hj
        simp only [Function.update_self, lt_irrefl, if_false, lt_add_iff_pos_right, zero_lt_one,
          if_true]
        funext t
        rw [P1_eq a b N s hab hN _ (hv _ (by simp)) t]
      · have : j.val ≠ m := fun h => hj (Fin.ext h)
        rw [Function.update_of_ne hj]
        by_cases hjm : j.val < m
        · simp [hjm, show j.val < m + 1 by omega]
        · simp [hjm, show ¬ j.val < m + 1 by omega]
    · rw [dif_neg hm]
      congr 1
      funext j
      have := j.isLt
      simp [show j.val < m by omega, show j.val < m + 1 by omega]

theorem fderiv_prodF {g : Fin n → ℝ → ℝ} (hg : ∀ i, ContDiff ℝ 1 (g i)) :
    ContDiff ℝ 1 (prodF e g) ∧ ∀ (i : Fin n) (x : E),
      fderiv ℝ (prodF e g) x (e i) = prodF e (Function.update g i (deriv (g i))) x := by
  have hcd : ContDiff ℝ 1 (prodF e g) := by
    unfold prodF
    exact contDiff_prod fun i _ => (hg i).comp (contDiff_const.inner ℝ contDiff_id)
  refine ⟨hcd, fun i x => ?_⟩
  have h1 : HasDerivAt (fun t : ℝ => prodF e g (x + t • e i)) (fderiv ℝ (prodF e g) x (e i)) 0 := by
    have hf : HasFDerivAt (prodF e g) (fderiv ℝ (prodF e g) x) (x + (0 : ℝ) • e i) := by
      simpa using (hcd.differentiable one_ne_zero x).hasFDerivAt
    have hl : HasDerivAt (fun t : ℝ => x + t • e i) (e i) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (e i)).const_add x
    exact hf.comp_hasDerivAt (0 : ℝ) hl
  set C := ∏ j ∈ Finset.univ.erase i, g j ⟪e j, x⟫ with hC
  have hfun : (fun t : ℝ => prodF e g (x + t • e i)) = fun t => g i (⟪e i, x⟫ + t) * C := by
    funext t
    rw [prodF_split e g i, hC]
    congr 1
    · simp [inner_orth]
    · refine Finset.prod_congr rfl fun j hj => ?_
      rw [inner_orth, if_neg (Finset.ne_of_mem_erase hj), add_zero]
  have hd : HasDerivAt (g i) (deriv (g i) ⟪e i, x⟫) ⟪e i, x⟫ :=
    ((hg i).differentiable one_ne_zero ⟪e i, x⟫).hasDerivAt
  have h2 : HasDerivAt (fun t : ℝ => g i (⟪e i, x⟫ + t) * C) (deriv (g i) ⟪e i, x⟫ * C) 0 := by
    have hd0 : HasDerivAt (g i) (deriv (g i) ⟪e i, x⟫) (⟪e i, x⟫ + 0) := by simpa using hd
    exact (hd0.comp_const_add ⟪e i, x⟫ 0).mul_const C
  rw [hfun] at h1
  rw [h1.unique h2, prodF_update]

theorem prod_sub_prod_tele (u v : Fin n → ℝ) :
    ∏ i, u i - ∏ i, v i = ∑ i : Fin n, ∏ j : Fin n,
      (if j.val < i.val then v j else if j = i then u i - v i else u j) := by
  set S : ℕ → ℝ := fun k => ∏ j : Fin n, if j.val < k then v j else u j with hS
  have hterm : ∀ i : Fin n, ∏ j : Fin n,
      (if j.val < i.val then v j else if j = i then u i - v i else u j) =
      S i.val - S (i.val + 1) := by
    intro i
    set R := ∏ j ∈ Finset.univ.erase i, (if j.val < i.val then v j else u j) with hR
    have e1 : S i.val = u i * R := by
      rw [hS]; dsimp only
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
      rw [if_neg (lt_irrefl _)]
    have e2 : S (i.val + 1) = v i * R := by
      rw [hS]; dsimp only
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
      simp only [lt_add_iff_pos_right, zero_lt_one, if_true]
      congr 1
      refine Finset.prod_congr rfl fun j hj => ?_
      have : j.val ≠ i.val := fun h => Finset.ne_of_mem_erase hj (Fin.ext h)
      by_cases h : j.val < i.val
      · simp [h, show j.val < i.val + 1 by omega]
      · simp [h, show ¬ j.val < i.val + 1 by omega]
    have e3 : ∏ j : Fin n,
        (if j.val < i.val then v j else if j = i then u i - v i else u j) = (u i - v i) * R := by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
      simp only [lt_irrefl, if_false, if_true]
      congr 1
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [if_neg (Finset.ne_of_mem_erase hj)]
    rw [e3, e1, e2]; ring
  simp_rw [hterm]
  rw [Fin.sum_univ_eq_sum_range (fun k => S k - S (k + 1)) n, Finset.sum_range_sub']
  have h0 : S 0 = ∏ i, u i := by simp [hS]
  have hn : S n = ∏ i, v i := by
    simp only [hS]
    exact Finset.prod_congr rfl fun j _ => if_pos j.isLt
  rw [h0, hn]

/-- The kernel of the error operator in direction `i`. -/
noncomputable def rK (i : Fin n) : ℝ → ℝ → ℝ := Ref.rKer (a i) (b i) (N i) (s i)

theorem tele_prod (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i) {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 1 (g i)) {x : E} (hx : x ∈ box e a b) :
    prodF e g x - quasiP e a b N s (prodF e g) x = ∑ i : Fin n,
      Pcomp e a b N s i.val (coordOp e a b i (rK a b N s i)
        (fun y => fderiv ℝ (prodF e g) y (e i))) x := by
  rw [quasiP_prodF]
  refine (prod_sub_prod_tele (fun j => g j ⟪e j, x⟫)
    (fun j => P1 a b N s j (g j) ⟪e j, x⟫)).trans ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  have hD : (fun y => fderiv ℝ (prodF e g) y (e i)) =
      prodF e (Function.update g i (deriv (g i))) :=
    funext fun y => (fderiv_prodF e hg).2 i y
  rw [hD, coordOp_prodF, Function.update_idem]
  rw [Pcomp_prodF e a b N s hab hN _ i.val (fun j hj => by
    rw [Function.update_of_ne (fun h => by subst h; omega)]
    exact (hg j).continuous)]
  unfold prodF
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hj : j.val < i.val
  · have hne : j ≠ i := fun h => by subst h; omega
    simp only [hj, hne, ↓reduceIte, Function.update_of_ne hne]
  · by_cases hji : j = i
    · subst hji
      simp only [hj, ↓reduceIte, Function.update_self]
      unfold P1 rK
      rw [Ref.sub_sum_shape_eq_integral_rKer (hab j) (hN j) (s j) (hg j) (hx j)]
    · simp only [hj, hji, ↓reduceIte, Function.update_of_ne hji]

end prodpart

section kernels

/-- The one-dimensional kernel of `P1`. -/
noncomputable def pk1 (a b : ℝ) (N : ℕ) (s : Bool) (t τ : ℝ) : ℝ :=
  ∑ l ∈ Finset.range (N + 2), Ref.shape a b N s l t * Ref.dual a b N s l τ

theorem measurable_pk1 (a b : ℝ) (N : ℕ) (s : Bool) :
    Measurable (Function.uncurry (pk1 a b N s)) := by
  have : Function.uncurry (pk1 a b N s) = fun p : ℝ × ℝ =>
      ∑ l ∈ Finset.range (N + 2), Ref.shape a b N s l p.1 * Ref.dual a b N s l p.2 := by
    funext p; rfl
  rw [this]
  exact Finset.measurable_sum _ fun l _ =>
    ((Ref.measurable_shape s l).comp measurable_fst).mul ((Ref.measurable_dual s l).comp measurable_snd)

theorem integrableOn_pk1 {a b : ℝ} {N : ℕ} (hab : a < b) (hN : 0 < N) (s : Bool) (t : ℝ) :
    IntegrableOn (pk1 a b N s t) (Set.Ioo a b) := by
  unfold pk1
  exact integrable_finset_sum _ fun l _ =>
    ((Ref.integrable_dual hab hN s l).const_mul _).integrableOn

theorem pk1_A {a b : ℝ} {N : ℕ} (hab : a < b) (hN : 0 < N) (s : Bool) {K : ℝ}
    (hK : ∀ x, ∑ j ∈ Finset.range (N + 2),
      |Ref.shape a b N s j x| * ∫ y in Set.Ioo a b, |Ref.dual a b N s j y| ≤ K) (t : ℝ) :
    ∫ τ in Set.Ioo a b, |pk1 a b N s t τ| ≤ K := by
  have hi : ∀ l ∈ Finset.range (N + 2), IntegrableOn
      (fun τ => |Ref.shape a b N s l t| * |Ref.dual a b N s l τ|) (Set.Ioo a b) :=
    fun l _ => ((Ref.integrable_dual hab hN s l).abs.const_mul _).integrableOn
  calc ∫ τ in Set.Ioo a b, |pk1 a b N s t τ|
      ≤ ∫ τ in Set.Ioo a b, ∑ l ∈ Finset.range (N + 2),
          |Ref.shape a b N s l t| * |Ref.dual a b N s l τ| := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun τ => abs_nonneg _)
          (integrable_finset_sum _ hi) (Filter.Eventually.of_forall fun τ => ?_)
        unfold pk1
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        exact Finset.sum_congr rfl fun l _ => abs_mul _ _
    _ = ∑ l ∈ Finset.range (N + 2),
          |Ref.shape a b N s l t| * ∫ τ in Set.Ioo a b, |Ref.dual a b N s l τ| := by
        rw [integral_finset_sum _ hi]
        exact Finset.sum_congr rfl fun l _ => integral_const_mul _ _
    _ ≤ K := hK t

theorem pk1_B {a b : ℝ} {N : ℕ} (hab : a < b) (hN : 0 < N) (s : Bool) {K : ℝ}
    (hK : ∀ y, ∑ j ∈ Finset.range (N + 2),
      (∫ x in Set.Ioo a b, |Ref.shape a b N s j x|) * |Ref.dual a b N s j y| ≤ K) (τ : ℝ) :
    ∫ t in Set.Ioo a b, |pk1 a b N s t τ| ≤ K := by
  have hi : ∀ l ∈ Finset.range (N + 2), IntegrableOn
      (fun t => |Ref.shape a b N s l t| * |Ref.dual a b N s l τ|) (Set.Ioo a b) := by
    intro l _
    refine Integrable.mul_const ?_ _
    refine Measure.integrableOn_of_bounded (M := 1) (by simp) ?_ ?_
    · exact (Ref.measurable_shape s l).abs.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun t => by
        simpa using Ref.abs_shape_le_one (a := a) (b := b) (N := N) s l t
  calc ∫ t in Set.Ioo a b, |pk1 a b N s t τ|
      ≤ ∫ t in Set.Ioo a b, ∑ l ∈ Finset.range (N + 2),
          |Ref.shape a b N s l t| * |Ref.dual a b N s l τ| := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun τ => abs_nonneg _)
          (integrable_finset_sum _ hi) (Filter.Eventually.of_forall fun t => ?_)
        unfold pk1
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        exact Finset.sum_congr rfl fun l _ => abs_mul _ _
    _ = ∑ l ∈ Finset.range (N + 2),
          (∫ t in Set.Ioo a b, |Ref.shape a b N s l t|) * |Ref.dual a b N s l τ| := by
        rw [integral_finset_sum _ hi]
        exact Finset.sum_congr rfl fun l _ => integral_mul_const _ _
    _ ≤ K := hK τ

end kernels

section linear

variable (e : OrthonormalBasis (Fin n) ℝ E) (a b : Fin n → ℝ) (N : Fin n → ℕ) (s : Fin n → Bool)

/-- Measurable and bounded. -/
def Nice (F : E → ℝ) : Prop := Measurable F ∧ ∃ M, ∀ x, |F x| ≤ M

theorem Nice.add {F H : E → ℝ} (hF : Nice F) (hH : Nice H) : Nice (F + H) := by
  obtain ⟨m1, M1, h1⟩ := hF
  obtain ⟨m2, M2, h2⟩ := hH
  exact ⟨m1.add m2, M1 + M2, fun x => (abs_add_le _ _).trans (add_le_add (h1 x) (h2 x))⟩

theorem Nice.smul {F : E → ℝ} (c : ℝ) (hF : Nice F) : Nice (c • F) := by
  obtain ⟨m1, M1, h1⟩ := hF
  refine ⟨m1.const_smul c, |c| * M1, fun x => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (h1 x) (abs_nonneg _)

theorem Nice.zero : Nice (0 : E → ℝ) := ⟨measurable_const, 0, fun x => by simp⟩

/-- Kernel conditions. -/
def GoodK (j : Fin n) (k : ℝ → ℝ → ℝ) : Prop :=
  Measurable (Function.uncurry k) ∧ (∀ t, IntegrableOn (k t) (Set.Ioo (a j) (b j))) ∧
    ∃ A, ∀ t, ∫ τ in Set.Ioo (a j) (b j), |k t τ| ≤ A

theorem integrable_integrand {j : Fin n} {k : ℝ → ℝ → ℝ} (hk : GoodK a b j k) {F : E → ℝ}
    (hF : Nice F) (x : E) :
    IntegrableOn (fun τ => k ⟪e j, x⟫ τ * F (x + (τ - ⟪e j, x⟫) • e j)) (Set.Ioo (a j) (b j)) := by
  obtain ⟨hm, M, hM⟩ := hF
  refine (hk.2.1 _).mul_bdd (c := M) ?_ (Filter.Eventually.of_forall fun τ => ?_)
  · exact (hm.comp (measurable_const.add ((measurable_id.sub measurable_const).smul
      measurable_const))).aestronglyMeasurable
  · simpa using hM _

theorem coordOp_add {j : Fin n} {k : ℝ → ℝ → ℝ} (hk : GoodK a b j k) {F H : E → ℝ}
    (hF : Nice F) (hH : Nice H) :
    coordOp e a b j k (F + H) = coordOp e a b j k F + coordOp e a b j k H := by
  funext x
  simp only [coordOp, Pi.add_apply, mul_add]
  exact integral_add (integrable_integrand e a b hk hF x) (integrable_integrand e a b hk hH x)

theorem coordOp_smul (j : Fin n) (k : ℝ → ℝ → ℝ) (c : ℝ) (F : E → ℝ) :
    coordOp e a b j k (c • F) = c • coordOp e a b j k F := by
  funext x
  simp only [coordOp, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
  exact integral_const_mul _ _

theorem coordOp_zero (j : Fin n) (k : ℝ → ℝ → ℝ) : coordOp e a b j k (0 : E → ℝ) = 0 := by
  funext x; simp [coordOp]

theorem Nice.coordOp {j : Fin n} {k : ℝ → ℝ → ℝ} (hk : GoodK a b j k) {F : E → ℝ}
    (hF : Nice F) : Nice (coordOp e a b j k F) := by
  refine ⟨measurable_coordOp e a b j hk.1 hF.1, ?_⟩
  obtain ⟨A, hA⟩ := hk.2.2
  obtain ⟨M, hM⟩ := hF.2
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  refine ⟨A * M, fun x => ?_⟩
  unfold FEEC.coordOp
  calc |∫ τ in Set.Ioo (a j) (b j), k ⟪e j, x⟫ τ * F (x + (τ - ⟪e j, x⟫) • e j)|
      ≤ ∫ τ in Set.Ioo (a j) (b j), |k ⟪e j, x⟫ τ * F (x + (τ - ⟪e j, x⟫) • e j)| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ τ in Set.Ioo (a j) (b j), |k ⟪e j, x⟫ τ| * M := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun τ => abs_nonneg _)
          ((hk.2.1 _).abs.mul_const _) (Filter.Eventually.of_forall fun τ => ?_)
        show |k ⟪e j, x⟫ τ * F (x + (τ - ⟪e j, x⟫) • e j)| ≤ |k ⟪e j, x⟫ τ| * M
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hM _) (abs_nonneg _)
    _ = (∫ τ in Set.Ioo (a j) (b j), |k ⟪e j, x⟫ τ|) * M := integral_mul_const _ _
    _ ≤ A * M := mul_le_mul_of_nonneg_right (hA _) hM0

theorem goodK_pK (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i) (j : Fin n) :
    GoodK a b j (pK a b N s j) := by
  obtain ⟨K, hK0, hK⟩ := Ref.exists_schur_const
  exact ⟨measurable_pk1 _ _ _ _, fun t => integrableOn_pk1 (hab j) (hN j) _ t,
    K, fun t => pk1_A (hab j) (hN j) _ (hK _ _ _ (hab j) (hN j) _).1 t⟩

theorem goodK_rK (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i) (j : Fin n) :
    GoodK a b j (rK a b N s j) := by
  obtain ⟨K, hK0, hK⟩ := Ref.exists_rKer_schur
  exact ⟨Ref.measurable_rKer _, fun t => (hK _ _ _ (hab j) (hN j) _).2.2 t,
    _, fun t => (hK _ _ _ (hab j) (hN j) _).1 t⟩

theorem PK_add (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i) (m : ℕ) {F H : E → ℝ}
    (hF : Nice F) (hH : Nice H) :
    PK e a b N s m (F + H) = PK e a b N s m F + PK e a b N s m H := by
  unfold PK
  split_ifs with h
  · exact coordOp_add e a b (goodK_pK a b N s hab hN _) hF hH
  · rfl

theorem PK_smul (m : ℕ) (c : ℝ) (F : E → ℝ) :
    PK e a b N s m (c • F) = c • PK e a b N s m F := by
  unfold PK
  split_ifs with h
  · exact coordOp_smul e a b _ _ c F
  · rfl

theorem PK_zero (m : ℕ) : PK e a b N s m (0 : E → ℝ) = 0 := by
  unfold PK
  split_ifs with h
  · exact coordOp_zero e a b _ _
  · rfl

theorem Nice.PK (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i) (m : ℕ) {F : E → ℝ}
    (hF : Nice F) : Nice (PK e a b N s m F) := by
  unfold FEEC.Tensor.PK
  split_ifs with h
  · exact Nice.coordOp e a b (goodK_pK a b N s hab hN _) hF
  · exact hF

theorem Nice.Pcomp (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i) (m : ℕ) {F : E → ℝ}
    (hF : Nice F) : Nice (Pcomp e a b N s m F) := by
  induction m with
  | zero => exact hF
  | succ m ih => exact Nice.PK e a b N s hab hN m ih

theorem Pcomp_add (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i) (m : ℕ) {F H : E → ℝ}
    (hF : Nice F) (hH : Nice H) :
    Pcomp e a b N s m (F + H) = Pcomp e a b N s m F + Pcomp e a b N s m H := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [Pcomp]
    rw [ih, PK_add e a b N s hab hN m (Nice.Pcomp e a b N s hab hN m hF)
      (Nice.Pcomp e a b N s hab hN m hH)]

theorem Pcomp_smul (m : ℕ) (c : ℝ) (F : E → ℝ) :
    Pcomp e a b N s m (c • F) = c • Pcomp e a b N s m F := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [Pcomp]; rw [ih, PK_smul]

theorem Pcomp_zero (m : ℕ) : Pcomp e a b N s m (0 : E → ℝ) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [Pcomp]; rw [ih, PK_zero]

end linear

section linear2

variable (e : OrthonormalBasis (Fin n) ℝ E) (a b : Fin n → ℝ) (N : Fin n → ℕ) (s : Fin n → Bool)

theorem measurable_inner_e (i : Fin n) : Measurable (fun x : E => ⟪e i, x⟫) :=
  (continuous_const.inner continuous_id).measurable

theorem measurable_dualP (q : Fin n → ℕ) : Measurable (dualP e a b N s q) := by
  unfold dualP
  exact Finset.measurable_prod _ fun i _ => (Ref.measurable_dual _ _).comp (measurable_inner_e e i)

theorem bdd_dualP (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i) (q : Fin n → ℕ) :
    ∃ B, ∀ y, |dualP e a b N s q y| ≤ B := by
  have : ∀ i, ∃ B, 0 ≤ B ∧ ∀ t, |Ref.dual (a i) (b i) (N i) (s i) (q i) t| ≤ B := by
    intro i
    obtain ⟨B, hB⟩ := (Ref.contDiff_dual (hab i) (hN i) (s i) (q i)).continuous.bounded_above_of_compact_support
      (Ref.hasCompactSupport_dual (hab i) (hN i) (s i) (q i))
    exact ⟨B, (norm_nonneg _).trans (hB 0), fun t => by simpa using hB t⟩
  choose B hB0 hB using this
  refine ⟨∏ i, B i, fun y => ?_⟩
  unfold dualP
  rw [Finset.abs_prod]
  gcongr with i _
  exact hB i _

theorem integrableOn_dualP_mul (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i) (q : Fin n → ℕ)
    {F : E → ℝ} (hF : Nice F) :
    IntegrableOn (fun y => dualP e a b N s q y * F y) (box e a b) := by
  obtain ⟨B, hB⟩ := bdd_dualP e a b N s hab hN q
  obtain ⟨M, hM⟩ := hF.2
  refine Measure.integrableOn_of_bounded (M := B * M) (volume_box_lt_top e a b).ne
    ((measurable_dualP e a b N s q).mul hF.1).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hB y) (hM y) (abs_nonneg _) ((abs_nonneg _).trans (hB y))

theorem quasiP_add (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i) {F H : E → ℝ}
    (hF : Nice F) (hH : Nice H) :
    quasiP e a b N s (F + H) = quasiP e a b N s F + quasiP e a b N s H := by
  funext x
  simp only [quasiP, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← mul_add, ← integral_add (integrableOn_dualP_mul e a b N s hab hN _ hF)
    (integrableOn_dualP_mul e a b N s hab hN _ hH)]
  simp only [mul_add]

theorem quasiP_smul (c : ℝ) (F : E → ℝ) :
    quasiP e a b N s (c • F) = c • quasiP e a b N s F := by
  funext x
  simp only [quasiP, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  have : ∀ y, dualP e a b N s (fun i => q i) y * (c * F y) =
      c * (dualP e a b N s (fun i => q i) y * F y) := fun y => by ring
  simp_rw [this]
  rw [integral_const_mul]; ring

theorem quasiP_zero : quasiP e a b N s (0 : E → ℝ) = 0 := by
  funext x; simp [quasiP]

/-- Derivative in direction `i`. -/
noncomputable def DD (G : E → ℝ) (i : Fin n) : E → ℝ := fun y => fderiv ℝ G y (e i)

/-- Properties needed for linear extension. -/
def Good (G : E → ℝ) : Prop := ContDiff ℝ 1 G ∧ Nice G ∧ ∀ i, Nice (DD e G i)

/-- The `i`-th term in the telescoping sum. -/
noncomputable def T (G : E → ℝ) (i : Fin n) : E → ℝ :=
  Pcomp e a b N s i.val (coordOp e a b i (rK a b N s i) (DD e G i))

theorem DD_add {G H : E → ℝ} (hG : ContDiff ℝ 1 G) (hH : ContDiff ℝ 1 H) (i : Fin n) :
    DD e (G + H) i = DD e G i + DD e H i := by
  funext y
  simp only [DD, Pi.add_apply]
  rw [fderiv_add (hG.differentiable one_ne_zero y) (hH.differentiable one_ne_zero y)]
  rfl

theorem DD_smul {G : E → ℝ} (hG : ContDiff ℝ 1 G) (c : ℝ) (i : Fin n) :
    DD e (c • G) i = c • DD e G i := by
  funext y
  simp only [DD, Pi.smul_apply]
  rw [fderiv_const_smul (hG.differentiable one_ne_zero y)]
  rfl

theorem Good.add {G H : E → ℝ} (hG : Good e G) (hH : Good e H) : Good e (G + H) :=
  ⟨hG.1.add hH.1, hG.2.1.add hH.2.1, fun i => by
    rw [DD_add e hG.1 hH.1]; exact (hG.2.2 i).add (hH.2.2 i)⟩

theorem Good.smul {G : E → ℝ} (hG : Good e G) (c : ℝ) : Good e (c • G) :=
  ⟨hG.1.const_smul c, hG.2.1.smul c, fun i => by
    rw [DD_smul e hG.1]; exact (hG.2.2 i).smul c⟩

theorem T_add (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i) {G H : E → ℝ} (hG : Good e G)
    (hH : Good e H) (i : Fin n) :
    T e a b N s (G + H) i = T e a b N s G i + T e a b N s H i := by
  unfold T
  rw [DD_add e hG.1 hH.1, coordOp_add e a b (goodK_rK a b N s hab hN i) (hG.2.2 i) (hH.2.2 i),
    Pcomp_add e a b N s hab hN _ (Nice.coordOp e a b (goodK_rK a b N s hab hN i) (hG.2.2 i))
      (Nice.coordOp e a b (goodK_rK a b N s hab hN i) (hH.2.2 i))]

theorem T_smul {G : E → ℝ} (hG : Good e G) (c : ℝ) (i : Fin n) :
    T e a b N s (c • G) i = c • T e a b N s G i := by
  unfold T
  rw [DD_smul e hG.1, coordOp_smul, Pcomp_smul]

theorem T_zero (i : Fin n) : T e a b N s (0 : E → ℝ) i = 0 := by
  unfold T
  have : DD e (0 : E → ℝ) i = 0 := by funext y; simp [DD]
  rw [this, coordOp_zero, Pcomp_zero]

end linear2

section span

variable (e : OrthonormalBasis (Fin n) ℝ E) (a b : Fin n → ℝ) (N : Fin n → ℕ) (s : Fin n → Bool)

theorem abs_prodF_le {M : ℝ} (g : Fin n → ℝ → ℝ) (hg : ∀ i t, |g i t| ≤ M) (x : E) :
    |prodF e g x| ≤ M ^ n := by
  unfold prodF
  rw [Finset.abs_prod]
  calc ∏ i, |g i ⟪e i, x⟫| ≤ ∏ _i : Fin n, M := by
        gcongr with i _
        exact hg i _
    _ = M ^ n := by simp

theorem contDiff_trig1 (σ : Bool) (a b : ℝ) (m : ℕ) : ContDiff ℝ 1 (trig1 σ a b m) := by
  unfold trig1
  split_ifs
  exacts [(contDiff_trigS m).of_le (by norm_cast),
    (contDiff_trigC m).of_le (by norm_cast)]

theorem abs_trig1_le (σ : Bool) (a b : ℝ) (m : ℕ) (t : ℝ) : |trig1 σ a b m t| ≤ 1 := by
  unfold trig1; split_ifs
  exacts [abs_trigS_le _ _, abs_trigC_le _ _]

theorem abs_deriv_trig1 (σ : Bool) (a b : ℝ) (m : ℕ) (t : ℝ) :
    |deriv (trig1 σ a b m) t| ≤ |freq a b m| := by
  cases σ
  · have := (hasDerivAt_trigC (a := a) (b := b) m t).deriv
    have h : trig1 false a b m = trigC a b m := by funext t; simp [trig1]
    rw [h, this, abs_neg, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (abs_trigS_le _ _)
  · have := (hasDerivAt_trigS (a := a) (b := b) m t).deriv
    have h : trig1 true a b m = trigS a b m := by funext t; simp [trig1]
    rw [h, this, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (abs_trigC_le _ _)

theorem trigProd_good (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i) (σ : Fin n → Bool)
    (m : Fin n → ℕ) :
    Good e (trigProd e a b σ m) ∧ ∀ x ∈ box e a b,
      trigProd e a b σ m x - quasiP e a b N s (trigProd e a b σ m) x =
        ∑ i : Fin n, T e a b N s (trigProd e a b σ m) i x := by
  set g : Fin n → ℝ → ℝ := fun i => trig1 (σ i) (a i) (b i) (m i) with hgdef
  have hgd : ∀ i, ContDiff ℝ 1 (g i) := fun i => contDiff_trig1 _ _ _ _
  have hP : trigProd e a b σ m = prodF e g := rfl
  rw [hP]
  obtain ⟨hcd, hder⟩ := fderiv_prodF e hgd
  have hDD : ∀ i, DD e (prodF e g) i = prodF e (Function.update g i (deriv (g i))) :=
    fun i => funext fun y => hder i y
  refine ⟨⟨hcd, ⟨hcd.continuous.measurable, 1, fun x => ?_⟩, fun i => ?_⟩, fun x hx => ?_⟩
  · have := abs_trigProd_le e a b σ m x
    simpa [← hP] using this
  · refine ⟨?_, max 1 (∑ j, |freq (a j) (b j) (m j)|) ^ n, fun y => ?_⟩
    · have : Continuous (fun y => fderiv ℝ (prodF e g) y (e i)) :=
        (hcd.continuous_fderiv one_ne_zero).clm_apply continuous_const
      exact this.measurable
    · rw [hDD]
      refine abs_prodF_le e _ (fun j t => ?_) y
      by_cases hj : j = i
      · subst hj
        rw [Function.update_self]
        refine (abs_deriv_trig1 _ _ _ _ _).trans ?_
        refine le_trans ?_ (le_max_right _ _)
        exact Finset.single_le_sum (f := fun j => |freq (a j) (b j) (m j)|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
      · rw [Function.update_of_ne hj]
        exact (abs_trig1_le _ _ _ _ _).trans (le_max_left _ _)
  · have := tele_prod e a b N s hab hN hgd hx
    rw [this]
    rfl

end span

section final

variable (e : OrthonormalBasis (Fin n) ℝ E) (a b : Fin n → ℝ) (N : Fin n → ℕ) (s : Fin n → Bool)

theorem span_good (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i) {G : E → ℝ}
    (hG : G ∈ Submodule.span ℝ
        (Set.range fun p : (Fin n → Bool) × (Fin n → ℕ) => trigProd e a b p.1 p.2)) :
    Good e G ∧ ∀ x ∈ box e a b,
      G x - quasiP e a b N s G x = ∑ i : Fin n, T e a b N s G i x := by
  induction hG using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    exact trigProd_good e a b N s hab hN p.1 p.2
  | zero =>
    refine ⟨⟨contDiff_const, Nice.zero, fun i => ?_⟩, fun x hx => ?_⟩
    · have : DD e (0 : E → ℝ) i = 0 := by funext y; simp [DD]
      rw [this]; exact Nice.zero
    · simp [quasiP_zero, T_zero]
  | add G H _ _ ihG ihH =>
    refine ⟨ihG.1.add e ihH.1, fun x hx => ?_⟩
    have h1 := ihG.2 x hx
    have h2 := ihH.2 x hx
    simp_rw [T_add e a b N s hab hN ihG.1 ihH.1,
      quasiP_add e a b N s hab hN ihG.1.2.1 ihH.1.2.1]
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    linarith
  | smul c G _ ihG =>
    refine ⟨ihG.1.smul e c, fun x hx => ?_⟩
    have h1 := ihG.2 x hx
    simp_rw [T_smul e a b N s ihG.1 c, quasiP_smul e a b N s c]
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    rw [← h1]; ring

theorem Pcomp_bound (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i) {Kp : ℝ}
    (hA : ∀ i t, ∫ τ in Set.Ioo (a i) (b i), |pK a b N s i t τ| ≤ Kp)
    (hB : ∀ i τ, ∫ t in Set.Ioo (a i) (b i), |pK a b N s i t τ| ≤ Kp) :
    ∀ m, m ≤ n → ∀ F : E → ℝ, Measurable F → IntegrableOn (fun x => F x ^ 2) (box e a b) →
      Measurable (Pcomp e a b N s m F) ∧
      IntegrableOn (fun x => Pcomp e a b N s m F x ^ 2) (box e a b) ∧
      ∫ x in box e a b, Pcomp e a b N s m F x ^ 2 ≤
        (Kp * Kp) ^ m * ∫ x in box e a b, F x ^ 2 := by
  intro m
  induction m with
  | zero => intro _ F hF hF2; exact ⟨hF, hF2, by simp [Pcomp]⟩
  | succ m ih =>
    intro hm F hF hF2
    obtain ⟨h1, h2, h3⟩ := ih (by omega) F hF hF2
    have hmn : m < n := by omega
    simp only [Pcomp]
    unfold PK
    rw [dif_pos hmn]
    have hk := goodK_pK a b N s hab hN ⟨m, hmn⟩
    obtain ⟨h4, h5⟩ := coordOp_sq_le e hab ⟨m, hmn⟩ hk.1 (hA _) (hB _) hk.2.1 h1 h2
    refine ⟨measurable_coordOp e a b _ hk.1 h1, h4, h5.trans ?_⟩
    have hKK : 0 ≤ Kp * Kp := by
      have := hA ⟨m, hmn⟩ 0
      have h0 : 0 ≤ Kp := (integral_nonneg fun _ => abs_nonneg _).trans this
      positivity
    calc Kp * Kp * ∫ x in box e a b, Pcomp e a b N s m F x ^ 2
        ≤ Kp * Kp * ((Kp * Kp) ^ m * ∫ x in box e a b, F x ^ 2) :=
          mul_le_mul_of_nonneg_left h3 hKK
      _ = _ := by ring

end final

/-- **Approximation estimate** for trigonometric polynomials. -/
theorem exists_approx_trig (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E] (e : OrthonormalBasis (Fin n) ℝ E)
      (a b : Fin n → ℝ) (N : Fin n → ℕ) (_ : ∀ i, a i < b i) (_ : ∀ i, 0 < N i) (h : ℝ)
      (_ : ∀ i, Ref.meshH (a i) (b i) (N i) ≤ h) (s : Fin n → Bool) (G : E → ℝ)
      (_ : G ∈ Submodule.span ℝ
        (Set.range fun p : (Fin n → Bool) × (Fin n → ℕ) => trigProd e a b p.1 p.2)),
      ∫ x in box e a b, (G x - quasiP e a b N s G x) ^ 2 ≤
        C * h ^ 2 * ∑ i, ∫ x in box e a b, (fderiv ℝ G x (e i)) ^ 2 := by
  obtain ⟨K₁, hK₁0, hK₁⟩ := Ref.exists_schur_const
  obtain ⟨K₂, hK₂0, hK₂⟩ := Ref.exists_rKer_schur
  set Kp : ℝ := max 1 K₁ with hKp
  have hKp1 : 1 ≤ Kp := le_max_left _ _
  have hKK1 : 1 ≤ Kp * Kp := by nlinarith
  refine ⟨n * (Kp * Kp) ^ n * (K₂ * K₂), by positivity, ?_⟩
  intro E _ _ _ _ _ e a b N hab hN h hh s G hG
  obtain ⟨hGood, hIden⟩ := span_good e a b N s hab hN hG
  have hA : ∀ i t, ∫ τ in Set.Ioo (a i) (b i), |pK a b N s i t τ| ≤ Kp := fun i t =>
    (pk1_A (hab i) (hN i) _ (hK₁ _ _ _ (hab i) (hN i) _).1 t).trans (le_max_right _ _)
  have hB : ∀ i τ, ∫ t in Set.Ioo (a i) (b i), |pK a b N s i t τ| ≤ Kp := fun i τ =>
    (pk1_B (hab i) (hN i) _ (hK₁ _ _ _ (hab i) (hN i) _).2 τ).trans (le_max_right _ _)
  have hbox : ∀ F : E → ℝ, Nice F → IntegrableOn (fun x => F x ^ 2) (box e a b) := by
    intro F hF
    obtain ⟨M, hM⟩ := hF.2
    refine Measure.integrableOn_of_bounded (M := M ^ 2) (volume_box_lt_top e a b).ne
      (hF.1.pow_const 2).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hM x) 2
  have hterm : ∀ i : Fin n, Measurable (T e a b N s G i) ∧
      IntegrableOn (fun x => T e a b N s G i x ^ 2) (box e a b) ∧
      ∫ x in box e a b, T e a b N s G i x ^ 2 ≤
        (Kp * Kp) ^ n * ((K₂ * h) * (K₂ * h)) * ∫ x in box e a b, DD e G i x ^ 2 := by
    intro i
    obtain ⟨hKm, hKm2, hKi⟩ := hK₂ (a i) (b i) (N i) (hab i) (hN i) (s i)
    have hrk := goodK_rK a b N s hab hN i
    have hmesh := hh i
    have hAA : ∀ t, ∫ τ in Set.Ioo (a i) (b i), |rK a b N s i t τ| ≤ K₂ * h := fun t =>
      (hKm t).trans (mul_le_mul_of_nonneg_left hmesh hK₂0)
    have hBB : ∀ τ, ∫ t in Set.Ioo (a i) (b i), |rK a b N s i t τ| ≤ K₂ * h := fun τ =>
      (hKm2 τ).trans (mul_le_mul_of_nonneg_left hmesh hK₂0)
    have hD := hGood.2.2 i
    obtain ⟨h4, h5⟩ := coordOp_sq_le e hab i hrk.1 hAA hBB hrk.2.1 hD.1 (hbox _ hD)
    obtain ⟨h6, h7, h8⟩ := Pcomp_bound e a b N s hab hN hA hB i.val i.isLt.le _
      (measurable_coordOp e a b i hrk.1 hD.1) h4
    refine ⟨h6, h7, ?_⟩
    show ∫ x in box e a b, Pcomp e a b N s i.val (coordOp e a b i (rK a b N s i) (DD e G i)) x ^ 2 ≤ _
    have hpow : (Kp * Kp) ^ i.val ≤ (Kp * Kp) ^ n := pow_le_pow_right₀ hKK1 i.isLt.le
    have hint0 : 0 ≤ ∫ x in box e a b, coordOp e a b i (rK a b N s i) (DD e G i) x ^ 2 :=
      integral_nonneg fun _ => sq_nonneg _
    calc _ ≤ (Kp * Kp) ^ i.val * ∫ x in box e a b,
            coordOp e a b i (rK a b N s i) (DD e G i) x ^ 2 := h8
      _ ≤ (Kp * Kp) ^ n * ((K₂ * h) * (K₂ * h) * ∫ x in box e a b, DD e G i x ^ 2) :=
          mul_le_mul hpow h5 hint0 (by positivity)
      _ = _ := by ring
  have hid : ∫ x in box e a b, (G x - quasiP e a b N s G x) ^ 2 =
      ∫ x in box e a b, (∑ i : Fin n, T e a b N s G i x) ^ 2 :=
    setIntegral_congr_fun (measurableSet_box e a b) fun x hx => by
      rw [hIden x hx]
  rw [hid]
  have hsum_int : IntegrableOn (fun x => (n : ℝ) * ∑ i : Fin n, T e a b N s G i x ^ 2) (box e a b) :=
    (integrable_finset_sum _ fun i _ => (hterm i).2.1).const_mul _
  calc ∫ x in box e a b, (∑ i : Fin n, T e a b N s G i x) ^ 2
      ≤ ∫ x in box e a b, (n : ℝ) * ∑ i : Fin n, T e a b N s G i x ^ 2 := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => sq_nonneg _)
          hsum_int (Filter.Eventually.of_forall fun x => ?_)
        have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n)))
          (f := fun i => T e a b N s G i x)
        simpa [Finset.card_univ, Fintype.card_fin] using this
    _ = n * ∑ i : Fin n, ∫ x in box e a b, T e a b N s G i x ^ 2 := by
        rw [integral_const_mul, integral_finset_sum _ fun i _ => (hterm i).2.1]
    _ ≤ n * ∑ i : Fin n, ((Kp * Kp) ^ n * ((K₂ * h) * (K₂ * h)) *
          ∫ x in box e a b, DD e G i x ^ 2) := by
        gcongr with i _
        exact (hterm i).2.2
    _ = _ := by
        rw [← Finset.mul_sum]
        simp only [DD]
        ring

end Tensor

end FEEC
