/-
An unconditional O(h) convergence rate for tensor-product FEEC on a box.
-/
import FEEC.Fourier.SeriesApprox
import FEEC.Fourier.Data
import FEEC.Tensor.Main

/-!
# Convergence rate on a box in any dimension

**Theorem** (`Fourier.box_tensor_rate`). Let `Ω` be a box in a Euclidean space of any
dimension, `k + 1` a degree. There is `C`, depending only on the box and `k`, such that for
every tensor-product grid with all cell sizes at most `h` and every test form `φ` of degree
`k + 1`, the solutions of the Hodge Laplace problem and of its Galerkin approximation in the
tensor-product Whitney spaces, with data `f = φ`, satisfy

  `‖σ − σh‖ + ‖u − uh‖ + ‖p − ph‖ ≤ C h (‖φ‖ + ∑ᵢ ‖∂ᵢ φ‖)`.

No hypothesis is assumed.
-/

namespace FEEC

namespace Fourier

open MeasureTheory Tensor

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {n : ℕ}
  (e : OrthonormalBasis (Fin n) ℝ E) {a b : Fin n → ℝ}

/-- The error of the cochain projection of the tensor-product dual system, in the graph norm. -/
theorem norm_sub_proj_sq (hab : ∀ i, a i < b i) {N : Fin n → ℕ} (hN : ∀ i, 0 < N i) {k : ℕ}
    (σ : HΛ (box e a b) k) :
    ‖σ - (projection e hab hN).π k σ‖ ^ 2 =
      ‖HΛ.toL2 σ - (deRhamComplex (isOpen_box e a b)).dualOp (shapeH (e := e) hab hN)
          (dualL (e := e) hab hN) (fun k => ((k.factorial : ℝ))⁻¹) k (HΛ.toL2 σ)‖ ^ 2 +
      ‖HΛ.toL2 (HΛ.d σ) - (deRhamComplex (isOpen_box e a b)).dualOp (shapeH (e := e) hab hN)
          (dualL (e := e) hab hN) (fun k => ((k.factorial : ℝ))⁻¹) (k + 1)
          (HΛ.toL2 (HΛ.d σ))‖ ^ 2 := by
  have hI := (deRhamComplex (isOpen_box e a b)).inner_eq k (σ - (projection e hab hN).π k σ)
    (σ - (projection e hab hN).π k σ)
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hI
  have h1 : (deRhamComplex (isOpen_box e a b)).ι k (σ - (projection e hab hN).π k σ) =
      HΛ.toL2 σ - (deRhamComplex (isOpen_box e a b)).dualOp (shapeH (e := e) hab hN)
          (dualL (e := e) hab hN) (fun k => ((k.factorial : ℝ))⁻¹) k (HΛ.toL2 σ) := by
    refine ((deRhamComplex (isOpen_box e a b)).ι k).map_sub _ _ |>.trans ?_
    exact congrArg _ ((deRhamComplex (isOpen_box e a b)).ι_dualProj _ _ _ k σ)
  have h2 : (deRhamComplex (isOpen_box e a b)).ι (k + 1)
      ((deRhamComplex (isOpen_box e a b)).d k (σ - (projection e hab hN).π k σ)) =
      HΛ.toL2 (HΛ.d σ) - (deRhamComplex (isOpen_box e a b)).dualOp (shapeH (e := e) hab hN)
          (dualL (e := e) hab hN) (fun k => ((k.factorial : ℝ))⁻¹) (k + 1)
          (HΛ.toL2 (HΛ.d σ)) := by
    have hc : (deRhamComplex (isOpen_box e a b)).d k ((projection e hab hN).π k σ) =
        (projection e hab hN).π (k + 1) (HΛ.d σ) := ((projection e hab hN).comm k σ).symm
    have hd : (deRhamComplex (isOpen_box e a b)).d k (σ - (projection e hab hN).π k σ) =
        HΛ.d σ - (projection e hab hN).π (k + 1) (HΛ.d σ) := by
      have hdσ : (deRhamComplex (isOpen_box e a b)).d k σ = HΛ.d σ := rfl
      exact ((deRhamComplex (isOpen_box e a b)).d k).map_sub _ _ |>.trans
        (congrArg₂ (· - ·) hdσ hc)
    rw [hd]
    refine ((deRhamComplex (isOpen_box e a b)).ι (k + 1)).map_sub _ _ |>.trans ?_
    exact congrArg _ ((deRhamComplex (isOpen_box e a b)).ι_dualProj _ _ _ (k + 1) (HΛ.d σ))
  exact hI.trans (congrArg₂ (fun p q => ‖p‖ ^ 2 + ‖q‖ ^ 2) h1 h2)

theorem Nsq_eq_zero_of_eq_zero (hn : n = 0) {k : ℕ} (w : L2Form (box e a b) k) :
    Nsq e a b w = 0 := by
  subst hn
  simp [Nsq, nTerm, xi]

theorem sq_le_sq_add_sum (x : ℝ) (hx : 0 ≤ x) (I : Fin n → ℝ) (hI : ∀ i, 0 ≤ I i) :
    x ^ 2 + ∑ i, I i ≤ (x + ∑ i, Real.sqrt (I i)) ^ 2 := by
  have h1 : ∑ i, I i ≤ (∑ i, Real.sqrt (I i)) ^ 2 := by
    calc ∑ i, I i = ∑ i, Real.sqrt (I i) ^ 2 :=
          Finset.sum_congr rfl fun i _ => (Real.sq_sqrt (hI i)).symm
      _ ≤ _ := Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => Real.sqrt_nonneg _)
  have h2 : 0 ≤ ∑ i, Real.sqrt (I i) := Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _
  nlinarith [mul_nonneg hx h2]

set_option maxHeartbeats 400000 in
theorem key_estimate (hab : ∀ i, a i < b i) (k : ℕ) : ∃ CE M CR : ℝ, 0 ≤ M ∧ 0 ≤ CR ∧
    ∀ (N : Fin n → ℕ) (hN : ∀ i, 0 < N i) (h : ℝ)
    (hh : ∀ i, Ref.meshH (a i) (b i) (N i) ≤ h)
    (φ : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ) (hφ : IsTestForm (box e a b) φ)
    (σ : HΛ (box e a b) k) (u p : HΛ (box e a b) (k + 1))
    (_ : ((deRhamComplex (isOpen_box e a b)).segment k).IsSolution hφ.toLp σ u p)
    (σh : (subcomplex e hab hN).carrier k) (uh ph : (subcomplex e hab hN).carrier (k + 1))
    (_ : ((subcomplex e hab hN).segment k).toShort.IsSolution hφ.toLp σh uh ph),
    ∃ x y S : ℝ, 0 ≤ x ∧ 0 ≤ y ∧
      ‖σ - σh‖ + ‖u - uh‖ + ‖p - ph‖ ≤ CE * (x + y) ∧
      x ^ 2 + y ^ 2 ≤ M * h ^ 2 * S ∧
      S ≤ CR * (‖hφ.toLp‖ ^ 2 + ∑ i, ∫ x in box e a b,
        ‖Covector.ofAlt (fderiv ℝ φ x (e i))‖ ^ 2) ∧ 0 ≤ S ∧ (n = 0 → S = 0) := by
  obtain ⟨CE, hCE⟩ := Tensor.box_tensor_galerkin e hab k
  obtain ⟨A0, hA00, hA0⟩ := exists_approx_series n k
  obtain ⟨A1, hA10, hA1⟩ := exists_approx_series n (k + 1)
  obtain ⟨A2, hA20, hA2⟩ := exists_approx_series n (k + 1 + 1)
  obtain ⟨CR, hCR0, hCR⟩ := exists_regularity (e := e) hab k
  have hNsq : ∀ {j : ℕ} (w : L2Form (box e a b) j), 0 ≤ Nsq e a b w := fun w =>
    tsum_nonneg fun m => mul_nonneg (mul_nonneg (normProd_pos hab m).le (sq_nonneg _))
      (sq_nonneg _)
  refine ⟨CE, max A0 (max A1 A2), CR, le_max_of_le_left hA00, hCR0, ?_⟩
  intro N hN h hh φ hφ σ u p hs σh uh ph hsh
  obtain ⟨hfs, hfN⟩ := summable_nTerm_and_Nsq_le hab hφ
  obtain ⟨hs1, hs2, hs3, hs4, hS⟩ := hCR hφ.toLp σ u p hs hfs
  have hG := (hCE N hN hφ.toLp).2 σ u p hs σh uh ph hsh
    ⟨(projection e hab hN).π k σ, (projection e hab hN).π_mem k σ⟩
    ⟨(projection e hab hN).π (k + 1) u, (projection e hab hN).π_mem (k + 1) u⟩
  have a1 := hA0 e a b N hab hN h hh (HΛ.toL2 σ) hs1
  have a2 := hA1 e a b N hab hN h hh (HΛ.toL2 (HΛ.d σ)) hs2
  have a3 := hA1 e a b N hab hN h hh (HΛ.toL2 u) hs3
  have a4 := hA2 e a b N hab hN h hh (HΛ.toL2 (HΛ.d u)) hs4
  have e1 := norm_sub_proj_sq e hab hN σ
  have e2 := norm_sub_proj_sq e hab hN u
  have n1 := hNsq (HΛ.toL2 σ)
  have n2 := hNsq (HΛ.toL2 (HΛ.d σ))
  have n3 := hNsq (HΛ.toL2 u)
  have n4 := hNsq (HΛ.toL2 (HΛ.d u))
  have hh2 : 0 ≤ h ^ 2 := sq_nonneg h
  refine ⟨‖σ - (projection e hab hN).π k σ‖, ‖u - (projection e hab hN).π (k + 1) u‖,
    Nsq e a b (HΛ.toL2 σ) + Nsq e a b (HΛ.toL2 (HΛ.d σ)) + Nsq e a b (HΛ.toL2 u) +
      Nsq e a b (HΛ.toL2 (HΛ.d u)),
    norm_nonneg _, norm_nonneg _, hG, ?_, ?_, by positivity, ?_⟩
  · rw [e1, e2]
    have m0 : A0 ≤ max A0 (max A1 A2) := le_max_left _ _
    have m1 : A1 ≤ max A0 (max A1 A2) := (le_max_left _ _).trans (le_max_right _ _)
    have m2 : A2 ≤ max A0 (max A1 A2) := (le_max_right _ _).trans (le_max_right _ _)
    linarith [mul_le_mul_of_nonneg_right m0 (mul_nonneg hh2 n1),
      mul_le_mul_of_nonneg_right m1 (mul_nonneg hh2 n2),
      mul_le_mul_of_nonneg_right m1 (mul_nonneg hh2 n3),
      mul_le_mul_of_nonneg_right m2 (mul_nonneg hh2 n4)]
  · calc _ ≤ CR * (‖hφ.toLp‖ ^ 2 + Nsq e a b hφ.toLp) := hS
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hCR0
  · intro hn
    simp only [Nsq_eq_zero_of_eq_zero e hn, add_zero]

/-- **Unconditional `O(h)` convergence of tensor-product FEEC for the Hodge Laplacian on a
box, in any dimension and degree.** -/
theorem box_tensor_rate (hab : ∀ i, a i < b i) (k : ℕ) :
    ∃ C : ℝ, ∀ (N : Fin n → ℕ) (hN : ∀ i, 0 < N i) (h : ℝ)
      (_ : ∀ i, Ref.meshH (a i) (b i) (N i) ≤ h)
      (φ : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ) (hφ : IsTestForm (box e a b) φ)
      (σ : HΛ (box e a b) k) (u p : HΛ (box e a b) (k + 1))
      (_ : ((deRhamComplex (isOpen_box e a b)).segment k).IsSolution hφ.toLp σ u p)
      (σh : (subcomplex e hab hN).carrier k) (uh ph : (subcomplex e hab hN).carrier (k + 1))
      (_ : ((subcomplex e hab hN).segment k).toShort.IsSolution hφ.toLp σh uh ph),
      ‖σ - σh‖ + ‖u - uh‖ + ‖p - ph‖ ≤
        C * h * (‖hφ.toLp‖ + ∑ i, Real.sqrt
          (∫ x in box e a b, ‖Covector.ofAlt (fderiv ℝ φ x (e i))‖ ^ 2)) := by
  obtain ⟨CE, M, CR, hM0, hCR0, key⟩ := key_estimate e hab k
  by_cases hn : n = 0
  · refine ⟨0, fun N hN h hh φ hφ σ u p hs σh uh ph hsh => ?_⟩
    obtain ⟨x, y, S, hx, hy, hG, hq, -, -, hS0⟩ := key N hN h hh φ hφ σ u p hs σh uh ph hsh
    rw [hS0 hn, mul_zero] at hq
    have hx0 : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    have hy0 : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    rw [hx0, hy0] at hG
    simpa using hG
  · have hn' : 0 < n := Nat.pos_of_ne_zero hn
    refine ⟨max CE 0 * Real.sqrt (2 * M * CR), fun N hN h hh φ hφ σ u p hs σh uh ph hsh => ?_⟩
    obtain ⟨x, y, S, hx, hy, hG, hq, hSR, hS0, -⟩ := key N hN h hh φ hφ σ u p hs σh uh ph hsh
    have hh0 : 0 < h := lt_of_lt_of_le
      (Ref.meshH_pos (hab ⟨0, hn'⟩) (hN ⟨0, hn'⟩)) (hh ⟨0, hn'⟩)
    have hB := sq_le_sq_add_sum ‖hφ.toLp‖ (norm_nonneg _)
      (fun i => ∫ x in box e a b, ‖Covector.ofAlt (fderiv ℝ φ x (e i))‖ ^ 2)
      (fun i => integral_nonneg fun x => sq_nonneg _)
    beta_reduce at hB
    have hB0 : 0 ≤ ‖hφ.toLp‖ + ∑ i, Real.sqrt
          (∫ x in box e a b, ‖Covector.ofAlt (fderiv ℝ φ x (e i))‖ ^ 2) := by positivity
    have hK2 : Real.sqrt (2 * M * CR) ^ 2 = 2 * M * CR := Real.sq_sqrt (by positivity)
    have hK0 : 0 ≤ Real.sqrt (2 * M * CR) := Real.sqrt_nonneg _
    have hxy : x + y ≤ Real.sqrt (2 * M * CR) * h * (‖hφ.toLp‖ + ∑ i, Real.sqrt
          (∫ x in box e a b, ‖Covector.ofAlt (fderiv ℝ φ x (e i))‖ ^ 2)) := by
      refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 ?_
      have h1 : (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by nlinarith [sq_nonneg (x - y)]
      have hh2 : 0 ≤ M * h ^ 2 := by positivity
      calc (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := h1
        _ ≤ 2 * (M * h ^ 2 * S) := by linarith
        _ ≤ 2 * (M * h ^ 2 * (CR * (‖hφ.toLp‖ ^ 2 + ∑ i, ∫ x in box e a b,
              ‖Covector.ofAlt (fderiv ℝ φ x (e i))‖ ^ 2))) := by
          gcongr
        _ ≤ 2 * (M * h ^ 2 * (CR * (‖hφ.toLp‖ + ∑ i, Real.sqrt
              (∫ x in box e a b, ‖Covector.ofAlt (fderiv ℝ φ x (e i))‖ ^ 2)) ^ 2)) := by
          gcongr
        _ = _ := by rw [mul_pow, mul_pow, hK2]; ring
    calc _ ≤ CE * (x + y) := hG
      _ ≤ max CE 0 * (x + y) := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max CE 0 * (Real.sqrt (2 * M * CR) * h * (‖hφ.toLp‖ + ∑ i, Real.sqrt
          (∫ x in box e a b, ‖Covector.ofAlt (fderiv ℝ φ x (e i))‖ ^ 2))) :=
        mul_le_mul_of_nonneg_left hxy (le_max_right _ _)
      _ = _ := by ring

end Fourier

end FEEC
