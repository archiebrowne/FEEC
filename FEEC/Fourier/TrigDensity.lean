/-
Completeness of cosine/sine product systems on a box.
-/
import FEEC.Fourier.Trig1D
import FEEC.Tensor.BoxIntegral

/-!
# Completeness of trigonometric product systems on a box

For a pattern `s : Fin n → Bool`, `trigProd e a b s m x = ∏ᵢ T_{mᵢ}(⟪eᵢ, x⟫)` with `T = trigS`
in the directions where `s i` holds and `T = trigC` otherwise. A square integrable function
on the box orthogonal to all of them vanishes (`FEEC.eq_zero_of_forall_integral_trigProd`).
-/

namespace FEEC

open MeasureTheory

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {n : ℕ}

/-- One-dimensional factor: sine (`true`) or cosine (`false`). -/
noncomputable def trig1 (s : Bool) (a b : ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  if s then trigS a b m t else trigC a b m t

/-- Products of cosines and sines of the coordinates. -/
noncomputable def trigProd (e : OrthonormalBasis (Fin n) ℝ E) (a b : Fin n → ℝ)
    (s : Fin n → Bool) (m : Fin n → ℕ) (x : E) : ℝ :=
  ∏ i, trig1 (s i) (a i) (b i) (m i) ⟪e i, x⟫


section helpers

open Set Submodule

variable (e : OrthonormalBasis (Fin n) ℝ E) (a b : Fin n → ℝ) (s : Fin n → Bool)

/-- The closed box. -/
def boxK : Set E := {x | ∀ i, ⟪e i, x⟫ ∈ Set.Icc (a i) (b i)}

theorem box_subset_boxK : box e a b ⊆ boxK e a b := fun _ hx i => Set.Ioo_subset_Icc_self (hx i)

theorem isCompact_boxK : IsCompact (boxK e a b) := by
  have hc : IsClosed (boxK e a b) := by
    have : boxK e a b = ⋂ i, (fun x => ⟪e i, x⟫) ⁻¹' Set.Icc (a i) (b i) := by
      ext x; simp [boxK]
    rw [this]
    exact isClosed_iInter fun i => isClosed_Icc.preimage (continuous_const.inner continuous_id)
  have hcomp : IsCompact ((fun y : Fin n → ℝ => ∑ i, y i • e i) ''
      Set.univ.pi fun i => Set.Icc (a i) (b i)) :=
    (isCompact_univ_pi fun i => isCompact_Icc).image (by fun_prop)
  refine hcomp.of_isClosed_subset hc fun x hx => ⟨fun i => ⟪e i, x⟫, fun i _ => hx i, ?_⟩
  exact e.sum_repr' x

theorem continuous_trigProd (m : Fin n → ℕ) : Continuous (trigProd e a b s m) := by
  unfold trigProd
  refine continuous_finset_prod _ fun i _ => ?_
  have : Continuous (trig1 (s i) (a i) (b i) (m i)) := by
    unfold trig1; split_ifs
    exacts [(contDiff_trigS _).continuous, (contDiff_trigC _).continuous]
  exact this.comp (continuous_const.inner continuous_id)

theorem abs_trigProd_le (m : Fin n → ℕ) (x : E) : |trigProd e a b s m x| ≤ 1 := by
  unfold trigProd
  rw [Finset.abs_prod]
  refine Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun i _ => ?_
  unfold trig1; split_ifs
  exacts [abs_trigS_le _ _, abs_trigC_le _ _]

theorem prod_mem_span_trigProd (u : Fin n → ℝ → ℝ)
    (hu : ∀ i, u i ∈ span ℝ (Set.range (trig1 (s i) (a i) (b i)))) :
    (fun x : E => ∏ i, u i ⟪e i, x⟫) ∈ span ℝ (Set.range (trigProd e a b s)) := by
  classical
  choose c hc using fun i => (Finsupp.mem_span_range_iff_exists_finsupp).1 (hu i)
  have hu' : ∀ i t, u i t = ∑ j ∈ (c i).support, c i j * trig1 (s i) (a i) (b i) j t := by
    intro i t
    rw [← hc i]
    simp [Finsupp.sum, Finset.sum_apply]
  have : (fun x : E => ∏ i, u i ⟪e i, x⟫) = ∑ p ∈ Fintype.piFinset (fun i => (c i).support),
      (∏ i, c i (p i)) • trigProd e a b s p := by
    funext x
    simp_rw [hu']
    rw [Finset.prod_univ_sum]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.prod_mul_distrib]; rfl
  rw [this]
  exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (subset_span ⟨p, rfl⟩)

theorem mul_mem_span_cos {φ ψ : E → ℝ}
    (hφ : φ ∈ span ℝ (Set.range (trigProd e a b (fun _ => false))))
    (hψ : ψ ∈ span ℝ (Set.range (trigProd e a b (fun _ => false)))) :
    φ * ψ ∈ span ℝ (Set.range (trigProd e a b (fun _ => false))) := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, rfl⟩ := hx
    induction hψ using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨m', rfl⟩ := hy
      have := prod_mem_span_trigProd e a b (fun _ => false)
        (fun i t => trigC (a i) (b i) (m i) t * trigC (a i) (b i) (m' i) t) (by
          intro i
          have : (fun t => trigC (a i) (b i) (m i) t * trigC (a i) (b i) (m' i) t) =
              (1 / 2 : ℝ) • trig1 false (a i) (b i) (m i + m' i) +
              (1 / 2 : ℝ) • trig1 false (a i) (b i) (Nat.dist (m i) (m' i)) := by
            funext t
            simp only [trig1, Bool.false_eq_true, if_false, Pi.add_apply, Pi.smul_apply,
              smul_eq_mul, trigC_mul_trigC]
            ring
          rw [this]
          exact add_mem (smul_mem _ _ (subset_span ⟨_, rfl⟩)) (smul_mem _ _ (subset_span ⟨_, rfl⟩)))
      convert this using 1
      funext x
      simp only [Pi.mul_apply, trigProd, trig1, Bool.false_eq_true, if_false,
        Finset.prod_mul_distrib]
    | zero => simp
    | add y z _ _ hy hz => simpa [mul_add] using add_mem hy hz
    | smul c y _ hy => simpa [mul_smul_comm] using smul_mem _ c hy
  | zero => simp
  | add y z _ _ hy hz => simpa [add_mul] using add_mem hy hz
  | smul c y _ hy => simpa [smul_mul_assoc] using smul_mem _ c hy

theorem integrable_mul_trigProd {F : E → ℝ} (hF : Integrable F (volume.restrict (box e a b)))
    (m : Fin n → ℕ) : Integrable (fun x => F x * trigProd e a b s m x)
      (volume.restrict (box e a b)) :=
  hF.mul_bdd (c := 1) (continuous_trigProd e a b s m).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by simpa using abs_trigProd_le e a b s m x)

theorem integral_span_zero {F : E → ℝ} (hF : Integrable F (volume.restrict (box e a b)))
    (h : ∀ m, ∫ x in box e a b, F x * trigProd e a b s m x = 0) :
    ∀ ψ ∈ span ℝ (Set.range (trigProd e a b s)),
      Integrable (fun x => F x * ψ x) (volume.restrict (box e a b)) ∧
        ∫ x in box e a b, F x * ψ x = 0 := by
  intro ψ hψ
  induction hψ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, rfl⟩ := hx
    exact ⟨integrable_mul_trigProd e a b s hF m, h m⟩
  | zero => simp
  | add y z _ _ hy hz =>
    refine ⟨?_, ?_⟩
    · simp only [Pi.add_apply, mul_add]; exact hy.1.add hz.1
    · simp only [Pi.add_apply, mul_add]
      rw [integral_add hy.1 hz.1, hy.2, hz.2, add_zero]
  | smul c y _ hy =>
    refine ⟨?_, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]; exact hy.1.const_mul c
    · simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
      rw [integral_const_mul, hy.2, mul_zero]

theorem ae_eq_zero_of_integral_smul {F : E → ℝ}
    (hF : Integrable F (volume.restrict (box e a b)))
    (h : ∀ g : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ box e a b →
      ∫ x in box e a b, g x • F x = 0) : F =ᵐ[volume.restrict (box e a b)] 0 := by
  have := (isOpen_box e a b).ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hF.locallyIntegrable.locallyIntegrableOn _) h
  filter_upwards [this, ae_restrict_mem (measurableSet_box e a b)] with x hx hxΩ using hx hxΩ

theorem trigProd_single (i : Fin n) (x : E) :
    trigProd e a b (fun _ => false) (Pi.single i 1) x = trigC (a i) (b i) 1 ⟪e i, x⟫ := by
  unfold trigProd
  rw [Finset.prod_eq_single_of_mem i (Finset.mem_univ i)]
  · simp [trig1]
  · intro j _ hj
    simp [trig1, Pi.single_apply, hj, trigC_zero]

theorem eq_of_forall_inner_eq {x y : E} (h : ∀ i, ⟪e i, x⟫ = ⟪e i, y⟫) : x = y := by
  rw [← e.sum_repr' x, ← e.sum_repr' y]
  simp [h]

/-- Cosine case: integrals against all continuous bounded functions vanish. -/
theorem integral_mul_eq_zero_cos (hab : ∀ i, a i < b i) {F : E → ℝ}
    (hF : Integrable F (volume.restrict (box e a b)))
    (h : ∀ m, ∫ x in box e a b, F x * trigProd e a b (fun _ => false) m x = 0)
    {g : E → ℝ} (hg : Continuous g) (hgb : ∃ C, ∀ x, ‖g x‖ ≤ C) :
    ∫ x in box e a b, F x * g x = 0 := by
  classical
  have hKc := isCompact_boxK e a b
  haveI : CompactSpace (boxK e a b) := isCompact_iff_compactSpace.1 hKc
  set Sp : Submodule ℝ (E → ℝ) := span ℝ (Set.range (trigProd e a b (fun _ => false))) with hSp
  have hone : (1 : E → ℝ) ∈ Sp := by
    have : (1 : E → ℝ) = trigProd e a b (fun _ => false) 0 := by
      funext x; simp [trigProd, trig1, trigC_zero]
    rw [this]; exact subset_span ⟨_, rfl⟩
  let Sp' : Subalgebra ℝ (E → ℝ) :=
    Sp.toSubalgebra hone (fun φ ψ hφ hψ => mul_mem_span_cos e a b hφ hψ)
  let ρ : (E → ℝ) →ₐ[ℝ] (boxK e a b → ℝ) :=
    { toFun := fun φ z => φ z.1, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl, commutes' := fun _ => rfl }
  let A : Subalgebra ℝ C(boxK e a b, ℝ) :=
    (Sp'.map ρ).comap (ContinuousMap.coeFnAlgHom (R := ℝ))
  have hsep : A.SeparatesPoints := by
    intro x y hxy
    have : ∃ i, ⟪e i, (x : E)⟫ ≠ ⟪e i, (y : E)⟫ := by
      by_contra hcon
      push Not at hcon
      exact hxy (Subtype.ext (eq_of_forall_inner_eq e hcon))
    obtain ⟨i, hi⟩ := this
    refine ⟨_, ⟨⟨fun z => trigProd e a b (fun _ => false) (Pi.single i 1) z.1,
      (continuous_trigProd e a b _ _).comp continuous_subtype_val⟩, ?_, rfl⟩, ?_⟩
    · refine ⟨trigProd e a b (fun _ => false) (Pi.single i 1), subset_span ⟨_, rfl⟩, rfl⟩
    · simp only [trigProd_single]
      intro heq
      exact hi (trigC_one_injOn (hab i) (x.2 i) (y.2 i) heq)
  let gK : C(boxK e a b, ℝ) := ⟨fun z => g z.1, hg.comp continuous_subtype_val⟩
  have hM : 0 ≤ ∫ x in box e a b, ‖F x‖ := integral_nonneg fun _ => norm_nonneg _
  have hmain : ∀ ε > 0, ‖∫ x in box e a b, F x * g x‖ ≤ ε * ∫ x in box e a b, ‖F x‖ := by
    intro ε hε
    obtain ⟨⟨f, hfA⟩, hf⟩ :=
      ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints A hsep
        gK.1 gK.2 ε hε
    have hfA' : ContinuousMap.coeFnAlgHom (R := ℝ) f ∈ Sp'.map ρ := hfA
    obtain ⟨φ, hφ, hφf⟩ := Subalgebra.mem_map.1 hfA'
    have hφS : φ ∈ Sp := hφ
    have hφint := integral_span_zero e a b (fun _ => false) hF h φ hφS
    obtain ⟨C, hC⟩ := hgb
    have hgint : Integrable (fun x => F x * g x) (volume.restrict (box e a b)) :=
      hF.mul_bdd (c := C) hg.aestronglyMeasurable (Filter.Eventually.of_forall hC)
    have h1 : ∫ x in box e a b, F x * g x = ∫ x in box e a b, F x * (g x - φ x) := by
      have := integral_sub hgint hφint.1
      simp_rw [mul_sub]
      rw [this, hφint.2, sub_zero]
    have hdiff : Integrable (fun x => F x * (g x - φ x)) (volume.restrict (box e a b)) := by
      simp_rw [mul_sub]; exact hgint.sub hφint.1
    rw [h1]
    refine (norm_integral_le_of_norm_le (hF.norm.const_mul ε) ?_).trans_eq
      (integral_const_mul _ _)
    refine ae_restrict_of_forall_mem (measurableSet_box e a b) fun x hx => ?_
    have hx' : ‖φ x - g x‖ < ε := by
      have := hf ⟨x, box_subset_boxK e a b hx⟩
      have h2 : (f : C(boxK e a b, ℝ)) ⟨x, box_subset_boxK e a b hx⟩ = φ x :=
        (congrFun hφf ⟨x, box_subset_boxK e a b hx⟩).symm
      simpa [h2, gK] using this
    rw [norm_mul, mul_comm ε]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [← norm_neg, neg_sub]; exact hx'.le
  by_contra hI
  have hpos : 0 < ‖∫ x in box e a b, F x * g x‖ := norm_pos_iff.2 hI
  set I := ∫ x in box e a b, F x * g x
  set M := ∫ x in box e a b, ‖F x‖
  have hε : 0 < ‖I‖ / (M + 1) := by positivity
  have h3 := hmain _ hε
  have h4 : ‖I‖ / (M + 1) * M < ‖I‖ := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith
  linarith

/-- Cosine case of completeness. -/
theorem eq_zero_cos (hab : ∀ i, a i < b i) {F : E → ℝ}
    (hF : Integrable F (volume.restrict (box e a b)))
    (h : ∀ m, ∫ x in box e a b, F x * trigProd e a b (fun _ => false) m x = 0) :
    F =ᵐ[volume.restrict (box e a b)] 0 := by
  refine ae_eq_zero_of_integral_smul e a b hF fun g hg hgc _ => ?_
  have hgb : ∃ C, ∀ x, ‖g x‖ ≤ C :=
    hg.continuous.bounded_above_of_compact_support hgc
  have := integral_mul_eq_zero_cos e a b hab hF h hg.continuous hgb
  simpa [mul_comm] using this

end helpers

/-- **Completeness.** A square integrable function on a box orthogonal to all trigonometric
products of a given pattern vanishes almost everywhere. -/
theorem eq_zero_of_forall_integral_trigProd (e : OrthonormalBasis (Fin n) ℝ E)
    {a b : Fin n → ℝ} (hab : ∀ i, a i < b i) (s : Fin n → Bool)
    {F : E → ℝ} (hF : MemLp F 2 (volume.restrict (box e a b)))
    (h : ∀ m : Fin n → ℕ, ∫ x in box e a b, F x * trigProd e a b s m x = 0) :
    F =ᵐ[volume.restrict (box e a b)] 0 := by
  classical
  haveI : IsFiniteMeasure (volume.restrict (box e a b)) :=
    ⟨by simpa using volume_box_lt_top e a b⟩
  have hint : Integrable F (volume.restrict (box e a b)) := hF.integrable (by norm_num)
  let w : E → ℝ := fun x => ∏ i, (if s i then trigS (a i) (b i) 1 ⟪e i, x⟫ else 1)
  have hwc : Continuous w := by
    refine continuous_finset_prod _ fun i _ => ?_
    split_ifs
    · exact (contDiff_trigS _).continuous.comp (continuous_const.inner continuous_id)
    · exact continuous_const
  have hwb : ∀ x, ‖w x‖ ≤ 1 := by
    intro x
    simp only [w, Real.norm_eq_abs]
    rw [Finset.abs_prod]
    refine Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun i _ => ?_
    split_ifs
    · exact abs_trigS_le _ _
    · simp
  have hwpos : ∀ x ∈ box e a b, 0 < w x := by
    intro x hx
    refine Finset.prod_pos fun i _ => ?_
    split_ifs
    · exact trigS_one_pos (hab i) (hx i)
    · exact one_pos
  have hF' : Integrable (fun x => F x * w x) (volume.restrict (box e a b)) :=
    hint.mul_bdd (c := 1) hwc.aestronglyMeasurable (Filter.Eventually.of_forall hwb)
  have key := eq_zero_cos e a b hab hF' (fun m => by
    let u : Fin n → ℝ → ℝ := fun i t =>
      (if s i then trigS (a i) (b i) 1 t else 1) * trigC (a i) (b i) (m i) t
    have hu : ∀ i, u i ∈ Submodule.span ℝ (Set.range (trig1 (s i) (a i) (b i))) := by
      intro i
      by_cases hs : s i = true
      · rw [hs]
        cases hm : m i with
        | zero =>
          have : u i = trig1 true (a i) (b i) 1 := by
            funext t; simp [u, trig1, hs, hm, trigC_zero]
          rw [this]; exact Submodule.subset_span ⟨_, rfl⟩
        | succ j =>
          have : u i = (1 / 2 : ℝ) • trig1 true (a i) (b i) (j + 2) -
              (1 / 2 : ℝ) • trig1 true (a i) (b i) j := by
            funext t
            simp only [u, hs, hm, if_true, trig1, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
              trigS_one_mul_trigC]
            ring
          rw [this]
          exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
            (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
      · have hs' : s i = false := by simpa using hs
        rw [hs']
        have : u i = trig1 false (a i) (b i) (m i) := by
          funext t; simp [u, trig1, hs']
        rw [this]; exact Submodule.subset_span ⟨_, rfl⟩
    have hψ := prod_mem_span_trigProd e a b s u hu
    have := (integral_span_zero e a b s hint h _ hψ).2
    rw [← this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [w, u, trigProd, trig1, Bool.false_eq_true, if_false]
    rw [Finset.prod_mul_distrib]
    ring)
  filter_upwards [key, ae_restrict_mem (measurableSet_box e a b)] with x hx hxb
  have := hwpos x hxb
  simpa [this.ne'] using hx

end FEEC
