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


theorem coeFn_sum_smul' {Ω : Set E} {k : ℕ} {ι : Type*} [Countable ι] (s : Finset ι) (c : ι → ℝ)
    (X : ι → L2Form Ω k) :
    ∀ᵐ x ∂(volume.restrict Ω), (∑ i ∈ s, c i • X i : L2Form Ω k) x = ∑ i ∈ s, c i • (X i x) := by
  have h1 := Lp.coeFn_finsetSum (μ := volume.restrict Ω) s (fun i => c i • X i)
  have h2 : ∀ᵐ x ∂(volume.restrict Ω), ∀ i, (c i • X i : L2Form Ω k) x = c i • X i x := by
    rw [ae_all_iff]; intro i
    filter_upwards [Lp.coeFn_smul (c i) (X i)] with x hx using hx
  filter_upwards [h1, h2] with x hx hx2
  rw [hx, Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ => hx2 i

theorem sum_inner_smul_ae {Ω : Set E} {k : ℕ} (S : Fin k → Fin n) (g : E → ℝ)
    (X : (Fin k → Fin n) → L2Form Ω k) (Y : L2Form Ω k)
    (hX : ∀ T, ⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k T)⟫ ≠ 0 →
      X T =ᵐ[volume.restrict Ω] fun x => Covector.ofAlt (g x • dxT e k T))
    (hY : Y =ᵐ[volume.restrict Ω] fun x => Covector.ofAlt (g x • dxT e k S)) :
    ∑ T, ⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k T)⟫ • X T =
      (k.factorial : ℝ) • Y := by
  have hall : ∀ᵐ x ∂(volume.restrict Ω), ∀ T,
      ⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k T)⟫ ≠ 0 →
        X T x = Covector.ofAlt (g x • dxT e k T) := by
    rw [ae_all_iff]; intro T
    by_cases h : ⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k T)⟫ = 0
    · exact ae_of_all _ fun x hh => absurd h hh
    · exact (hX T h).mono fun x hx _ => hx
  refine Lp.ext ?_
  filter_upwards [coeFn_sum_smul' Finset.univ
    (fun T => ⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k T)⟫) X, hall,
    Lp.coeFn_smul (k.factorial : ℝ) Y, hY] with x h1 h2 h3 h4
  rw [h1, h3, Pi.smul_apply, h4]
  have hk : (k.factorial : ℝ) ≠ 0 := by positivity
  have key := sum_inner_dxT_smul e (dxT e k S)
  have h5 : ∑ T : Fin k → Fin n,
      ⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k T)⟫ • dxT e k T =
        (k.factorial : ℝ) • dxT e k S := by
    have := congrArg (fun y => (k.factorial : ℝ) • y) key
    simp only [smul_smul, mul_inv_cancel₀ hk, one_smul] at this
    exact this
  have h6 : ∑ T : Fin k → Fin n, ⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k T)⟫ •
      X T x = ∑ T : Fin k → Fin n,
        ⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k T)⟫ •
          Covector.ofAlt (g x • dxT e k T) := by
    refine Finset.sum_congr rfl fun T _ => ?_
    by_cases h : ⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k T)⟫ = 0
    · simp [h]
    · rw [h2 T h]
  rw [h6]
  have h7 : ∑ T : Fin k → Fin n, ⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k T)⟫ •
      Covector.ofAlt (g x • dxT e k T) = Covector.ofAlt (g x • ((k.factorial : ℝ) • dxT e k S)) := by
    rw [← h5]
    simp only [map_sum, map_smul, Finset.smul_sum, smul_comm (g x)]
  rw [h7]
  simp only [map_smul, smul_comm (g x)]

theorem pat_eq_of_inner_ne_zero' {S T : Fin k → Fin n}
    (h : ⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k T)⟫ ≠ 0) : pat S = pat T := by
  have hr : Set.range S = Set.range T := by
    by_contra hne
    exact h (inner_dxT_eq_zero_of_range_ne e hne)
  funext i
  rw [Bool.eq_iff_iff, pat_eq_true_iff, pat_eq_true_iff, hr]

theorem shapeLp_eq_zero_of_not_valid {T : Fin k → Fin n} {m : Fin n → ℕ}
    (h : ¬ ∀ i, Ref.Valid (N i) (pat T i) (m i)) : shapeLp e a b N T m = 0 := by
  push Not at h
  obtain ⟨i, hi⟩ := h
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [coeFn_shapeLp (e := e) (a := a) (b := b) (N := N) T m] with x hx
  rw [hx]
  have : shapeProd e a b N T m x = 0 := by
    unfold shapeProd
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Ref.shape, hi])
  simp [shapeForm, this]

theorem dualLp_eq_zero_of_not_valid (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i)
    {T : Fin k → Fin n} {m : Fin n → ℕ}
    (h : ¬ ∀ i, Ref.Valid (N i) (pat T i) (m i)) : dualLp (e := e) hab hN T m = 0 := by
  push Not at h
  obtain ⟨i, hi⟩ := h
  refine (isTestForm_dualForm (e := e) hab hN T m).toLp_eq_zero ?_
  funext x
  have : dualProd e a b N T m x = 0 := by
    unfold dualProd
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Ref.dual, hi])
  simp [dualForm, this]

theorem coeFn_dualLp (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i) (T : Fin k → Fin n)
    (m : Fin n → ℕ) :
    dualLp (e := e) hab hN T m =ᵐ[volume.restrict (box e a b)]
      fun x => Covector.ofAlt (dualForm e a b N T m x) :=
  (isTestForm_dualForm (e := e) hab hN T m).coeFn_toLp

theorem inner_shapeLp_dualLp_eq (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i)
    (S T : Fin k → Fin n) (q m : Fin n → ℕ) :
    ⟪shapeLp e a b N S q, dualLp (e := e) hab hN T m⟫ =
      ⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k T)⟫ *
        (if q = m ∧ ∀ i, Ref.Valid (N i) (pat T i) (q i) then 1 else 0) := by
  rw [inner_shapeLp_dualLp]
  by_cases h : ⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k T)⟫ = 0
  · simp [h]
  · rw [pat_eq_of_inner_ne_zero' h]
    rw [Finset.prod_congr rfl (fun i _ => Ref.integral_shape_mul_dual (hab i) (hN i) _ _ _),
      Finset.prod_boole]
    congr 1
    have hiff : (∀ i ∈ (Finset.univ : Finset (Fin n)),
        Ref.Valid (N i) (pat T i) (q i) ∧ q i = m i) ↔
        (q = m ∧ ∀ i, Ref.Valid (N i) (pat T i) (q i)) := by
      simp only [Finset.mem_univ, true_implies, forall_and]
      rw [and_comm, funext_iff]
    by_cases hc : q = m ∧ ∀ i, Ref.Valid (N i) (pat T i) (q i)
    · rw [if_pos hc, if_pos (hiff.2 hc)]
    · rw [if_neg hc, if_neg (fun h' => hc (hiff.1 h'))]

theorem proj_shape_aux (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i) (S : Fin k → Fin n)
    (q : (i : Fin n) → Fin (N i + 2)) :
    ((k.factorial : ℝ))⁻¹ • ∑ j : Idx N k,
      ⟪dualLp (e := e) hab hN j.1 (fun i => (j.2 i : ℕ)),
        shapeLp e a b N S (fun i => (q i : ℕ))⟫ •
        shapeLp e a b N j.1 (fun i => (j.2 i : ℕ)) = shapeLp e a b N S (fun i => (q i : ℕ)) := by
  have hterm : ∀ (T : Fin k → Fin n) (m : (i : Fin n) → Fin (N i + 2)),
      ⟪dualLp (e := e) hab hN T (fun i => (m i : ℕ)), shapeLp e a b N S (fun i => (q i : ℕ))⟫ •
        shapeLp e a b N T (fun i => (m i : ℕ)) =
      if m = q then ⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k T)⟫ •
        shapeLp e a b N T (fun i => (q i : ℕ)) else 0 := by
    intro T m
    rw [real_inner_comm, inner_shapeLp_dualLp_eq hab hN]
    by_cases hm : m = q
    · subst hm
      by_cases hv : ∀ i, Ref.Valid (N i) (pat T i) (m i)
      · simp [hv]
      · rw [shapeLp_eq_zero_of_not_valid hv]; simp
    · have : ¬ ((fun i => (q i : ℕ)) = fun i => (m i : ℕ)) := fun h =>
        hm (funext fun i => Fin.ext (congrFun h i).symm)
      simp [hm, this]
  rw [Fintype.sum_prod_type]
  simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [sum_inner_smul_ae S (shapeProd e a b N S (fun i => (q i : ℕ)))
    (fun T => shapeLp e a b N T (fun i => (q i : ℕ))) (shapeLp e a b N S (fun i => (q i : ℕ)))
    ?_ (coeFn_shapeLp S _), smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
  intro T h
  filter_upwards [coeFn_shapeLp (e := e) (a := a) (b := b) (N := N) T (fun i => (q i : ℕ))]
    with x hx
  have : shapeProd e a b N S (fun i => (q i : ℕ)) x = shapeProd e a b N T (fun i => (q i : ℕ)) x := by
    unfold shapeProd; rw [pat_eq_of_inner_ne_zero' h]
  rw [hx]
  simp only [shapeForm, this]

theorem proj_dual_aux (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i) (T : Fin k → Fin n)
    (m : (i : Fin n) → Fin (N i + 2)) (u : L2Form (box e a b) k) :
    ⟪dualLp (e := e) hab hN T (fun i => (m i : ℕ)),
      ((k.factorial : ℝ))⁻¹ • ∑ j : Idx N k,
        ⟪dualLp (e := e) hab hN j.1 (fun i => (j.2 i : ℕ)), u⟫ •
          shapeLp e a b N j.1 (fun i => (j.2 i : ℕ))⟫ =
      ⟪dualLp (e := e) hab hN T (fun i => (m i : ℕ)), u⟫ := by
  by_cases hv : ∀ i, Ref.Valid (N i) (pat T i) (m i)
  swap
  · rw [dualLp_eq_zero_of_not_valid hab hN hv]; simp
  have hk : (k.factorial : ℝ) ≠ 0 := by positivity
  have hterm : ∀ (S : Fin k → Fin n) (q : (i : Fin n) → Fin (N i + 2)),
      ⟪dualLp (e := e) hab hN S (fun i => (q i : ℕ)), u⟫ *
        ⟪dualLp (e := e) hab hN T (fun i => (m i : ℕ)),
          shapeLp e a b N S (fun i => (q i : ℕ))⟫ =
      if q = m then ⟪Covector.ofAlt (dxT e k T), Covector.ofAlt (dxT e k S)⟫ *
        ⟪dualLp (e := e) hab hN S (fun i => (m i : ℕ)), u⟫ else 0 := by
    intro S q
    rw [← real_inner_comm (dualLp (e := e) hab hN T _), inner_shapeLp_dualLp_eq hab hN]
    by_cases hq : q = m
    · subst hq
      simp [hv, real_inner_comm]
      ring
    · have : ¬ ((fun i => (q i : ℕ)) = fun i => (m i : ℕ)) := fun h =>
        hq (funext fun i => Fin.ext (congrFun h i))
      simp [hq, this]
  rw [inner_smul_right, inner_sum]
  simp only [inner_smul_right]
  rw [Fintype.sum_prod_type]
  simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hsum := sum_inner_smul_ae T (dualProd e a b N T (fun i => (m i : ℕ)))
    (fun S => dualLp (e := e) hab hN S (fun i => (m i : ℕ)))
    (dualLp (e := e) hab hN T (fun i => (m i : ℕ))) ?_ (coeFn_dualLp hab hN T _)
  · have := congrArg (fun y => ⟪y, u⟫) hsum
    simp only [sum_inner, real_inner_smul_left] at this
    rw [this]
    field_simp
  · intro S h
    filter_upwards [coeFn_dualLp (e := e) hab hN S (fun i => (m i : ℕ))] with x hx
    have : dualProd e a b N T (fun i => (m i : ℕ)) x = dualProd e a b N S (fun i => (m i : ℕ)) x := by
      unfold dualProd; rw [pat_eq_of_inner_ne_zero' h]
    rw [hx]
    simp only [dualForm, this]

/-- **The shape and dual forms are a dual system** for the de Rham complex of the box. -/
theorem isDualSystem (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i) :
    (deRhamComplex (isOpen_box e a b)).IsDualSystem (shapeH (e := e) hab hN)
      (dualL (e := e) hab hN) (fun k => ((k.factorial : ℝ))⁻¹) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k p
    refine HΛ.toL2_injective (isOpen_box e a b) ?_
    rw [HilbertComplex.dualProj_apply]
    simp only [map_smul, map_sum]
    exact proj_shape_aux hab hN p.1 p.2
  · intro k p u
    rw [HilbertComplex.dualProj_apply]
    simp only [map_smul, map_sum]
    exact proj_dual_aux hab hN p.1 p.2 _
  · intro k p
    have hmem : ∀ (T : Fin (k + 1) → Fin n) (m' : Fin n → ℕ),
        shapeLp e a b N T m' ∈ Submodule.span ℝ (Set.range fun j : Idx N (k + 1) =>
          HΛ.toL2 (shapeH (e := e) hab hN (k + 1) j)) := by
      intro T m'
      by_cases h : ∀ j, m' j < N j + 2
      · exact Submodule.subset_span ⟨(T, fun j => ⟨m' j, h j⟩), rfl⟩
      · push Not at h
        obtain ⟨j, hj⟩ := h
        rw [shapeLp_eq_zero hj]; exact Submodule.zero_mem _
    have h1 : HΛ.toL2 (HΛ.d (shapeH (e := e) hab hN k p)) ∈
        Submodule.span ℝ (Set.range fun j : Idx N (k + 1) =>
          HΛ.toL2 (shapeH (e := e) hab hN (k + 1) j)) := by
      change ∑ i, (Ref.meshH (a i) (b i) (N i))⁻¹ •
        (shapeLp e a b N (Fin.cons i p.1 : Fin (k + 1) → Fin n) (fun i => (p.2 i : ℕ)) -
          shapeLp e a b N (Fin.cons i p.1 : Fin (k + 1) → Fin n)
            (Function.update (fun i => (p.2 i : ℕ)) i ((p.2 i : ℕ) + 1))) ∈ _
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.sub_mem _ (hmem _ _) (hmem _ _))
    obtain ⟨γ, hγ⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 h1
    refine (Submodule.mem_span_range_iff_exists_fun ℝ).2 ⟨γ, ?_⟩
    refine HΛ.toL2_injective (isOpen_box e a b) ?_
    simp only [map_sum, map_smul]
    exact hγ
  · intro k j
    obtain ⟨γ, hγ⟩ := exists_codiff_dualLp (e := e) hab hN j.1 (fun i => (j.2 i : ℕ))
    refine ⟨γ, fun u => ?_⟩
    have h1 := HΛ.hasWeakExtDeriv u _ (isTestForm_dualForm (e := e) hab hN j.1
      (fun i => (j.2 i : ℕ)))
    rw [hγ, inner_sum] at h1
    simp only [inner_smul_right] at h1
    change ⟪dualLp (e := e) hab hN j.1 (fun i => (j.2 i : ℕ)), HΛ.toL2 (HΛ.d u)⟫ = _
    rw [real_inner_comm]
    refine h1.trans (Finset.sum_congr rfl fun l _ => ?_)
    rw [real_inner_comm]
    rfl

end Tensor

end FEEC
