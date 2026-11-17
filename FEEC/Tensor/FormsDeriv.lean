/-
Derivatives of tensor-product shape and dual forms.
-/
import FEEC.Tensor.Forms

namespace FEEC

namespace Tensor

open MeasureTheory

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {n : ℕ}
  {e : OrthonormalBasis (Fin n) ℝ E} {a b : Fin n → ℝ} {N : Fin n → ℕ} {k : ℕ}

theorem pat_eq_true_iff (T : Fin k → Fin n) (i : Fin n) : pat T i = true ↔ i ∈ Set.range T := by
  simp [pat, Set.mem_range]

theorem pat_cons (i : Fin n) (T : Fin k → Fin n) (j : Fin n) :
    pat (Fin.cons i T : Fin (k + 1) → Fin n) j = (decide (j = i) || pat T j) := by
  by_cases h : j = i
  · subst h
    simp only [decide_true, Bool.true_or, pat_eq_true_iff]
    exact ⟨0, by simp⟩
  · rw [Bool.eq_iff_iff, Bool.or_eq_true, pat_eq_true_iff, pat_eq_true_iff]
    simp only [decide_eq_true_eq, h, false_or]
    constructor
    · rintro ⟨p, rfl⟩
      induction p using Fin.cases with
      | zero => simp at h
      | succ q => exact ⟨q, by simp⟩
    · rintro ⟨q, rfl⟩
      exact ⟨q.succ, by simp⟩

theorem shapeProd_cons_diff (i : Fin n) (T : Fin k → Fin n) (hi : i ∉ Set.range T)
    (m : Fin n → ℕ) (x : E) :
    shapeProd e a b N (Fin.cons i T : Fin (k + 1) → Fin n) m x -
        shapeProd e a b N (Fin.cons i T : Fin (k + 1) → Fin n) (Function.update m i (m i + 1)) x =
      (Ref.shape (a i) (b i) (N i) true (m i) ⟪e i, x⟫ -
          Ref.shape (a i) (b i) (N i) true (m i + 1) ⟪e i, x⟫) *
        ∏ j ∈ Finset.univ.erase i, Ref.shape (a j) (b j) (N j) (pat T j) (m j) ⟪e j, x⟫ := by
  classical
  unfold shapeProd
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  have hp : pat (Fin.cons i T : Fin (k + 1) → Fin n) i = true := by
    rw [pat_cons]; simp
  have h1 : ∀ j ∈ Finset.univ.erase i,
      Ref.shape (a j) (b j) (N j) (pat (Fin.cons i T : Fin (k + 1) → Fin n) j) (m j) ⟪e j, x⟫ =
      Ref.shape (a j) (b j) (N j) (pat T j) (m j) ⟪e j, x⟫ := by
    intro j hj
    rw [pat_cons, decide_eq_false (Finset.ne_of_mem_erase hj)]; simp
  have h2 : ∀ j ∈ Finset.univ.erase i,
      Ref.shape (a j) (b j) (N j) (pat (Fin.cons i T : Fin (k + 1) → Fin n) j)
        (Function.update m i (m i + 1) j) ⟪e j, x⟫ =
      Ref.shape (a j) (b j) (N j) (pat T j) (m j) ⟪e j, x⟫ := by
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj), ← h1 j hj]
  rw [Finset.prod_congr rfl h1, Finset.prod_congr rfl h2, hp, Function.update_self]
  ring

/-- **Shape forms have a weak exterior derivative**, a combination of shape forms of the next
degree. -/
theorem hasWeakExtDeriv_shapeLp (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i)
    (T : Fin k → Fin n) (m : Fin n → ℕ) :
    HasWeakExtDeriv (shapeLp e a b N T m)
      (∑ i, (Ref.meshH (a i) (b i) (N i))⁻¹ •
        (shapeLp e a b N (Fin.cons i T : Fin (k + 1) → Fin n) m -
          shapeLp e a b N (Fin.cons i T : Fin (k + 1) → Fin n)
            (Function.update m i (m i + 1)))) := by
  classical
  refine hasWeakExtDeriv_prod_smul e a b
    (fun i => Ref.shape (a i) (b i) (N i) (pat T i) (m i))
    (fun i t => (Ref.shape (a i) (b i) (N i) true (m i) t -
      Ref.shape (a i) (b i) (N i) true (m i + 1) t) / Ref.meshH (a i) (b i) (N i))
    (dxT e k T) (fun i => Ref.measurable_shape _ _) (fun i => ⟨1, fun t => Ref.abs_shape_le_one _ _ t⟩)
    (fun i => ((Ref.measurable_shape _ _).sub (Ref.measurable_shape _ _)).div_const _)
    ?_ ?_ _ ?_ _ ?_
  · intro i
    refine ⟨2 / |Ref.meshH (a i) (b i) (N i)|, fun t => ?_⟩
    rw [abs_div]
    gcongr
    have h1 := Ref.abs_shape_le_one (a := a i) (b := b i) (N := N i) true (m i) t
    have h2 := Ref.abs_shape_le_one (a := a i) (b := b i) (N := N i) true (m i + 1) t
    exact (abs_sub _ _).trans (by linarith)
  · intro i
    by_cases hp : pat T i = true
    · left
      exact wedgeLeft_dxT_of_mem e ((pat_eq_true_iff T i).1 hp)
    · right
      rw [Bool.not_eq_true] at hp
      obtain ⟨Z, hZ⟩ := Ref.hasDerivAt_shape_false (hab i) (hN i)
      refine ⟨?_, Z, fun t ht htZ => ?_⟩
      · simp only [hp]; exact Ref.lipschitz_shape_false (hab i) (hN i) (m i)
      · simp only [hp]; exact hZ (m i) t ht htZ
  · filter_upwards [coeFn_shapeLp (e := e) (a := a) (b := b) (N := N) T m] with x hx
    rw [hx]; rfl
  · have h1 := Lp.coeFn_finsetSum (μ := volume.restrict (box e a b)) Finset.univ
      (fun i => (Ref.meshH (a i) (b i) (N i))⁻¹ •
        (shapeLp e a b N (Fin.cons i T : Fin (k + 1) → Fin n) m -
          shapeLp e a b N (Fin.cons i T : Fin (k + 1) → Fin n) (Function.update m i (m i + 1))))
    have h2 : ∀ᵐ x ∂(volume.restrict (box e a b)), ∀ i,
        ((Ref.meshH (a i) (b i) (N i))⁻¹ •
        (shapeLp e a b N (Fin.cons i T : Fin (k + 1) → Fin n) m -
          shapeLp e a b N (Fin.cons i T : Fin (k + 1) → Fin n) (Function.update m i (m i + 1))) :
          L2Form (box e a b) (k + 1)) x =
        (Ref.meshH (a i) (b i) (N i))⁻¹ • (Covector.ofAlt (shapeForm e a b N
          (Fin.cons i T : Fin (k + 1) → Fin n) m x) -
          Covector.ofAlt (shapeForm e a b N (Fin.cons i T : Fin (k + 1) → Fin n)
            (Function.update m i (m i + 1)) x)) := by
      rw [ae_all_iff]; intro i
      filter_upwards [Lp.coeFn_smul (Ref.meshH (a i) (b i) (N i))⁻¹ (shapeLp e a b N
          (Fin.cons i T : Fin (k + 1) → Fin n) m - shapeLp e a b N
          (Fin.cons i T : Fin (k + 1) → Fin n) (Function.update m i (m i + 1))),
        Lp.coeFn_sub (shapeLp e a b N (Fin.cons i T : Fin (k + 1) → Fin n) m)
          (shapeLp e a b N (Fin.cons i T : Fin (k + 1) → Fin n) (Function.update m i (m i + 1))),
        coeFn_shapeLp (e := e) (a := a) (b := b) (N := N)
          (Fin.cons i T : Fin (k + 1) → Fin n) m,
        coeFn_shapeLp (e := e) (a := a) (b := b) (N := N)
          (Fin.cons i T : Fin (k + 1) → Fin n) (Function.update m i (m i + 1))]
        with x g1 g2 g3 g4
      rw [g1]
      simp only [Pi.smul_apply, g2, Pi.sub_apply, g3, g4]
    filter_upwards [h1, h2] with x hx hx2
    rw [hx, Finset.sum_apply, Finset.sum_congr rfl (fun i _ => hx2 i)]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [shapeForm, ← sub_smul, ← map_sub]
    rw [← map_smul, ← wedgeLeft_dxT]
    congr 1
    by_cases hi : i ∈ Set.range T
    · rw [wedgeLeft_dxT_of_mem e hi]; simp
    · rw [shapeProd_cons_diff i T hi, smul_smul]
      congr 1
      ring

theorem fderiv_dualProd_apply (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i) (T : Fin k → Fin n)
    (m : Fin n → ℕ) (x : E) (i : Fin n) :
    fderiv ℝ (dualProd e a b N T m) x (e i) =
      deriv (Ref.dual (a i) (b i) (N i) (pat T i) (m i)) ⟪e i, x⟫ *
        ∏ j ∈ Finset.univ.erase i, Ref.dual (a j) (b j) (N j) (pat T j) (m j) ⟪e j, x⟫ := by
  classical
  have hdiff : Differentiable ℝ (dualProd e a b N T m) :=
    (contDiff_dualProd hab hN T m).differentiable (by simp)
  have h1 : HasDerivAt (fun t : ℝ => dualProd e a b N T m (x + t • e i))
      (fderiv ℝ (dualProd e a b N T m) x (e i)) 0 := by
    have h2 : HasDerivAt (fun t : ℝ => x + t • e i) (e i) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (e i)).const_add x
    have h3 := (hdiff (x + (0 : ℝ) • e i)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
    simp only [zero_smul, add_zero] at h3
    exact h3
  have h2 : HasDerivAt (fun t : ℝ => dualProd e a b N T m (x + t • e i))
      (deriv (Ref.dual (a i) (b i) (N i) (pat T i) (m i)) ⟪e i, x⟫ *
        ∏ j ∈ Finset.univ.erase i, Ref.dual (a j) (b j) (N j) (pat T j) (m j) ⟪e j, x⟫) 0 := by
    have hfun : (fun t : ℝ => dualProd e a b N T m (x + t • e i)) = fun t =>
        Ref.dual (a i) (b i) (N i) (pat T i) (m i) (⟪e i, x⟫ + t) *
          ∏ j ∈ Finset.univ.erase i, Ref.dual (a j) (b j) (N j) (pat T j) (m j) ⟪e j, x⟫ := by
      funext t
      unfold dualProd
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
      congr 1
      · rw [inner_add_right, inner_smul_right, e.inner_eq_ite, if_pos rfl, mul_one]
      · refine Finset.prod_congr rfl fun j hj => ?_
        rw [inner_add_right, inner_smul_right, e.inner_eq_ite, if_neg (Finset.ne_of_mem_erase hj)]
        simp
    rw [hfun]
    have hd : HasDerivAt (Ref.dual (a i) (b i) (N i) (pat T i) (m i))
        (deriv (Ref.dual (a i) (b i) (N i) (pat T i) (m i)) ⟪e i, x⟫) ⟪e i, x⟫ :=
      ((Ref.contDiff_dual (hab i) (hN i) _ _).differentiable (by simp) _).hasDerivAt
    exact (HasDerivAt.comp_const_add (⟪e i, x⟫) 0 (by simpa using hd)).mul_const _
  exact h1.unique h2

theorem dualProd_update {l : ℕ} (i : Fin n) (S : Fin k → Fin n) (T : Fin l → Fin n) (hS : pat S i = false)
    (hST : ∀ j, j ≠ i → pat S j = pat T j) (m : Fin n → ℕ) (v : ℕ) (x : E) :
    dualProd e a b N S (Function.update m i v) x =
      Ref.dual (a i) (b i) (N i) false v ⟪e i, x⟫ *
        ∏ j ∈ Finset.univ.erase i, Ref.dual (a j) (b j) (N j) (pat T j) (m j) ⟪e j, x⟫ := by
  classical
  unfold dualProd
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), hS, Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj), hST j (Finset.ne_of_mem_erase hj)]

theorem inner_curryLeft_dxT (β : E [⋀^Fin (k + 1)]→L[ℝ] ℝ) (i : Fin n) (S : Fin k → Fin n) :
    ⟪Covector.ofAlt (β.curryLeft (e i)), Covector.ofAlt (dxT e k S)⟫ =
      ⟪Covector.ofAlt β, Covector.ofAlt (dxT e (k + 1) (Fin.cons i S : Fin (k + 1) → Fin n))⟫ := by
  rw [← wedgeLeft_dxT, ← real_inner_comm (Covector.ofAlt β), inner_wedgeLeft, real_inner_comm]

theorem curryLeft_dxT_expand (T : Fin (k + 1) → Fin n) (i : Fin n) :
    (dxT e (k + 1) T).curryLeft (e i) = ((k.factorial : ℝ))⁻¹ • ∑ S : Fin k → Fin n,
      ⟪Covector.ofAlt (dxT e (k + 1) T),
        Covector.ofAlt (dxT e (k + 1) (Fin.cons i S : Fin (k + 1) → Fin n))⟫ • dxT e k S := by
  conv_lhs => rw [← sum_inner_dxT_smul e ((dxT e (k + 1) T).curryLeft (e i))]
  simp only [inner_curryLeft_dxT]

theorem pat_of_inner_ne_zero (i : Fin n) (S : Fin k → Fin n) (T : Fin (k + 1) → Fin n)
    (hc : ⟪Covector.ofAlt (dxT e (k + 1) T),
      Covector.ofAlt (dxT e (k + 1) (Fin.cons i S : Fin (k + 1) → Fin n))⟫ ≠ 0) :
    pat T i = true ∧ pat S i = false ∧ ∀ j, j ≠ i → pat S j = pat T j := by
  have hr : Set.range (Fin.cons i S : Fin (k + 1) → Fin n) = Set.range T := by
    by_contra h
    exact hc (by rw [real_inner_comm]; exact inner_dxT_eq_zero_of_range_ne e h)
  have hiS : i ∉ Set.range S := by
    intro h
    apply hc
    rw [← wedgeLeft_dxT, wedgeLeft_dxT_of_mem e h]; simp
  have hp : ∀ j, pat (Fin.cons i S : Fin (k + 1) → Fin n) j = pat T j := fun j => by
    rw [Bool.eq_iff_iff, pat_eq_true_iff, pat_eq_true_iff, hr]
  refine ⟨?_, ?_, fun j hj => ?_⟩
  · rw [← hp, pat_cons]; simp
  · cases hpp : pat S i
    · rfl
    · exact absurd ((pat_eq_true_iff S i).1 hpp) hiS
  · rw [← hp, pat_cons, decide_eq_false hj]; simp

variable (e a b N) in
/-- The coefficient of the dual form `S` with node `m i - 1` in the codifferential of the dual
form `T`. -/
noncomputable def codiffCoeff (T : Fin (k + 1) → Fin n) (m : Fin n → ℕ) (i : Fin n)
    (S : Fin k → Fin n) : ℝ :=
  if pat T i = true ∧ Ref.Valid (N i) true (m i) then
    -(((k.factorial : ℝ))⁻¹ * ⟪Covector.ofAlt (dxT e (k + 1) T),
      Covector.ofAlt (dxT e (k + 1) (Fin.cons i S : Fin (k + 1) → Fin n))⟫ /
        Ref.meshH (a i) (b i) (N i))
  else 0

theorem codiff_dualForm_apply (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i)
    (T : Fin (k + 1) → Fin n) (m : Fin n → ℕ) (x : E) :
    codiff (dualForm e a b N T m) x = ∑ i, ∑ S : Fin k → Fin n,
      codiffCoeff e a b N T m i S •
        (dualForm e a b N S (Function.update m i (m i - 1)) x - dualForm e a b N S m x) := by
  classical
  have hdiff : Differentiable ℝ (dualProd e a b N T m) :=
    (contDiff_dualProd hab hN T m).differentiable (by simp)
  rw [codiff_eq_sum_basis e]
  have h1 : ∀ i, fderiv ℝ (dualForm e a b N T m) x (e i) =
      fderiv ℝ (dualProd e a b N T m) x (e i) • dxT e (k + 1) T := by
    intro i
    have : dualForm e a b N T m = fun y => dualProd e a b N T m y • dxT e (k + 1) T := rfl
    rw [this, fderiv_smul_const (hdiff x)]; rfl
  simp only [h1, curryLeft_smul', fderiv_dualProd_apply hab hN, curryLeft_dxT_expand (e := e),
    Finset.smul_sum]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases hc : ⟪Covector.ofAlt (dxT e (k + 1) T),
      Covector.ofAlt (dxT e (k + 1) (Fin.cons i S : Fin (k + 1) → Fin n))⟫ = 0
  · simp [codiffCoeff, hc]
  obtain ⟨hiT, hiS, hST⟩ := pat_of_inner_ne_zero (e := e) i S T hc
  by_cases hv : Ref.Valid (N i) true (m i)
  · have hder := (Ref.hasDerivAt_dual_true (hab i) (hN i) (m i) ⟪e i, x⟫).deriv
    rw [if_pos hv] at hder
    have hm : Function.update m i (m i) = m := Function.update_eq_self i m
    have hs : dualForm e a b N S m x = dualProd e a b N S m x • dxT e k S := rfl
    have hs1 : dualForm e a b N S (Function.update m i (m i - 1)) x =
        dualProd e a b N S (Function.update m i (m i - 1)) x • dxT e k S := rfl
    rw [hs, hs1, ← sub_smul, hiT, hder, codiffCoeff, if_pos ⟨hiT, hv⟩, smul_smul, smul_smul,
      smul_smul]
    have e1 := dualProd_update (e := e) (a := a) (b := b) (N := N) i S T hiS hST m (m i - 1) x
    have e2 := dualProd_update (e := e) (a := a) (b := b) (N := N) i S T hiS hST m (m i) x
    rw [hm] at e2
    rw [e1, e2, ← neg_smul]
    congr 1
    ring
  · have hder := (Ref.hasDerivAt_dual_true (hab i) (hN i) (m i) ⟪e i, x⟫).deriv
    rw [if_neg hv] at hder
    rw [hiT, hder]
    simp [codiffCoeff, hv]

/-- **The codifferential of a dual form** is a combination of dual forms of the previous
degree. -/
theorem exists_codiff_dualLp (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i)
    (T : Fin (k + 1) → Fin n) (m : Fin n → ℕ) :
    ∃ γ : (Fin k → Fin n) × ((i : Fin n) → Fin (N i + 2)) → ℝ,
      (isTestForm_dualForm (e := e) hab hN T m).codiff.toLp =
        ∑ p, γ p • dualLp (e := e) hab hN p.1 (fun i => (p.2 i : ℕ)) := by
  classical
  have hmem : ∀ (S : Fin k → Fin n) (m' : Fin n → ℕ), dualLp (e := e) hab hN S m' ∈
      Submodule.span ℝ (Set.range fun p : (Fin k → Fin n) × ((i : Fin n) → Fin (N i + 2)) =>
        dualLp (e := e) hab hN p.1 (fun i => (p.2 i : ℕ))) := by
    intro S m'
    by_cases h : ∀ j, m' j < N j + 2
    · exact Submodule.subset_span ⟨(S, fun j => ⟨m' j, h j⟩), rfl⟩
    · push Not at h
      obtain ⟨j, hj⟩ := h
      rw [dualLp_eq_zero hab hN hj]; exact Submodule.zero_mem _
  let w : testForms (box e a b) k := ∑ i, ∑ S : Fin k → Fin n, codiffCoeff e a b N T m i S •
    (⟨dualForm e a b N S (Function.update m i (m i - 1)),
        isTestForm_dualForm hab hN S _⟩ - ⟨dualForm e a b N S m, isTestForm_dualForm hab hN S m⟩)
  have hw : w.1 = codiff (dualForm e a b N T m) := by
    funext x
    rw [codiff_dualForm_apply hab hN T m x]
    simp [w, Finset.sum_apply]
  have h1 : (isTestForm_dualForm (e := e) hab hN T m).codiff.toLp = testFormsToLp _ k w :=
    IsTestForm.toLp_congr _ w.2 hw.symm
  have h2 : testFormsToLp (box e a b) k w ∈ Submodule.span ℝ
      (Set.range fun p : (Fin k → Fin n) × ((i : Fin n) → Fin (N i + 2)) =>
        dualLp (e := e) hab hN p.1 (fun i => (p.2 i : ℕ))) := by
    simp only [w, map_sum, map_smul, map_sub]
    refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun S _ =>
      Submodule.smul_mem _ _ (Submodule.sub_mem _ (hmem _ _) (hmem _ _))
  rw [h1]
  obtain ⟨γ, hγ⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 h2
  exact ⟨γ, hγ.symm⟩

end Tensor

end FEEC
