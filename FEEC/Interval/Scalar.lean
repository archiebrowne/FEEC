/-
Scalar Sobolev toolkit on an interval: weak derivatives, primitives, meshes.
-/
import Mathlib

/-!
# Weak derivatives on an interval, and piecewise constant approximation

Elementary one-dimensional Sobolev theory on `(a, b)`, in scalar terms.

* `L2I a b = L²(a, b)`; `HasWeakDeriv u g`: `∫ g φ = -∫ u φ'` for all test functions `φ`.
* `hasWeakDeriv_primitive`: `x ↦ ∫ₐˣ g` has weak derivative `g`.
* `HasWeakDeriv.ae_eq_const_add_primitive` (du Bois-Reymond / fundamental theorem of
  calculus in `H¹`): if `u' = g` weakly then `u = c + ∫ₐˣ g` a.e.
* `Mesh a b`: a mesh `a = x₀ < ⋯ < x_{n+1} = b`, with mesh size `M.size` and the space
  `M.pcConst` of piecewise constant functions.
* `Mesh.exists_pcConst_near`: `u ∈ H¹` is within `h ‖u'‖` of the piecewise constants.
-/

namespace FEEC.Interval

open MeasureTheory Set

/-- `L²(a, b)`. -/
abbrev L2I (a b : ℝ) : Type := Lp ℝ 2 (volume.restrict (Ioo a b))

variable {a b : ℝ}

/-- A test function on `(a, b)`: smooth with compact support inside `(a, b)`. -/
structure IsTestFn (a b : ℝ) (φ : ℝ → ℝ) : Prop where
  contDiff : ContDiff ℝ (⊤ : ℕ∞) φ
  hasCompactSupport : HasCompactSupport φ
  tsupport_subset : tsupport φ ⊆ Ioo a b

/-- `g` is the weak derivative of `u` on `(a, b)`. -/
def HasWeakDeriv (u g : L2I a b) : Prop :=
  ∀ φ : ℝ → ℝ, IsTestFn a b φ →
    ∫ x in Ioo a b, g x * φ x = -∫ x in Ioo a b, u x * deriv φ x

instance : IsFiniteMeasure (volume.restrict (Ioo a b)) := by
  rw [isFiniteMeasure_restrict]; simp

theorem integrable_mul_cont (u : L2I a b) {ψ : ℝ → ℝ} (hψ : Continuous ψ)
    (hs : HasCompactSupport ψ) :
    Integrable (fun x => u x * ψ x) (volume.restrict (Ioo a b)) := by
  obtain ⟨C, hC⟩ := hψ.bounded_above_of_compact_support hs
  have hu : Integrable (u : ℝ → ℝ) (volume.restrict (Ioo a b)) :=
    (Lp.memLp u).integrable (by norm_num)
  exact hu.mul_bdd hψ.aestronglyMeasurable (Filter.Eventually.of_forall hC)

theorem IsTestFn.integrable_mul {φ : ℝ → ℝ} (hφ : IsTestFn a b φ) (u : L2I a b) :
    Integrable (fun x => u x * φ x) (volume.restrict (Ioo a b)) :=
  integrable_mul_cont u (hφ.contDiff.continuous) hφ.hasCompactSupport

theorem IsTestFn.integrable_mul_deriv {φ : ℝ → ℝ} (hφ : IsTestFn a b φ) (u : L2I a b) :
    Integrable (fun x => u x * deriv φ x) (volume.restrict (Ioo a b)) :=
  integrable_mul_cont u (hφ.contDiff.continuous_deriv (by exact_mod_cast le_top))
    hφ.hasCompactSupport.deriv

theorem HasWeakDeriv.zero : HasWeakDeriv (0 : L2I a b) 0 := by
  intro φ _
  have e1 : ∫ x in Ioo a b, (0 : L2I a b) x * φ x = 0 := by
    rw [← integral_zero (α := ℝ) (μ := volume.restrict (Ioo a b)) (G := ℝ)]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_zero ℝ 2 (volume.restrict (Ioo a b))] with x hx
    rw [hx]; simp
  have e2 : ∫ x in Ioo a b, (0 : L2I a b) x * deriv φ x = 0 := by
    rw [← integral_zero (α := ℝ) (μ := volume.restrict (Ioo a b)) (G := ℝ)]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_zero ℝ 2 (volume.restrict (Ioo a b))] with x hx
    rw [hx]; simp
  rw [e1, e2]; simp

theorem HasWeakDeriv.add {u u' g g' : L2I a b} (h : HasWeakDeriv u g) (h' : HasWeakDeriv u' g') :
    HasWeakDeriv (u + u') (g + g') := by
  intro φ hφ
  have e1 : ∫ x in Ioo a b, (g + g' : L2I a b) x * φ x
      = ∫ x in Ioo a b, (g x * φ x + g' x * φ x) := by
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_add g g'] with x hx
    rw [hx]; simp [add_mul]
  have e2 : ∫ x in Ioo a b, (u + u' : L2I a b) x * deriv φ x
      = ∫ x in Ioo a b, (u x * deriv φ x + u' x * deriv φ x) := by
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_add u u'] with x hx
    rw [hx]; simp [add_mul]
  rw [e1, e2, integral_add (hφ.integrable_mul g) (hφ.integrable_mul g'),
    integral_add (hφ.integrable_mul_deriv u) (hφ.integrable_mul_deriv u'), h φ hφ, h' φ hφ]
  ring

theorem HasWeakDeriv.smul (c : ℝ) {u g : L2I a b} (h : HasWeakDeriv u g) :
    HasWeakDeriv (c • u) (c • g) := by
  intro φ hφ
  have e1 : ∫ x in Ioo a b, (c • g : L2I a b) x * φ x
      = ∫ x in Ioo a b, c * (g x * φ x) := by
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_smul c g] with x hx
    rw [hx]; simp [mul_assoc]
  have e2 : ∫ x in Ioo a b, (c • u : L2I a b) x * deriv φ x
      = ∫ x in Ioo a b, c * (u x * deriv φ x) := by
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_smul c u] with x hx
    rw [hx]; simp [mul_assoc]
  rw [e1, e2, integral_const_mul, integral_const_mul, h φ hφ]
  ring

theorem HasWeakDeriv.neg {u g : L2I a b} (h : HasWeakDeriv u g) : HasWeakDeriv (-u) (-g) := by
  have := h.smul (-1)
  simpa using this

theorem intervalIntegrable_coe (g : L2I a b) (hab : a ≤ b) :
    IntervalIntegrable (g : ℝ → ℝ) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab]
  exact (Lp.memLp g).integrable (by norm_num)

/-- The primitive of an `L²` function is in `L²(a, b)`. -/
theorem memLp_primitive (g : L2I a b) :
    MemLp (fun x => ∫ t in a..x, g t) 2 (volume.restrict (Ioo a b)) := by
  rcases lt_or_ge a b with hab | hab
  swap
  · simp [Ioo_eq_empty (not_lt.2 hab)]
  have hI := intervalIntegrable_coe g hab.le
  have hcont : ContinuousOn (fun x => ∫ t in a..x, g t) (uIcc a b) :=
    intervalIntegral.continuousOn_primitive_interval' hI left_mem_uIcc
  obtain ⟨C, hC⟩ := isCompact_uIcc.exists_bound_of_continuousOn hcont
  refine MemLp.of_bound ((hcont.mono ?_).aestronglyMeasurable measurableSet_Ioo) C ?_
  · intro x hx; rw [uIcc_of_le hab.le]; exact Ioo_subset_Icc_self hx
  · refine ae_restrict_of_forall_mem measurableSet_Ioo (fun x hx => hC x ?_)
    rw [uIcc_of_le hab.le]; exact Ioo_subset_Icc_self hx

/-- The primitive `x ↦ ∫ₐˣ g` of `g ∈ L²(a, b)`, as an element of `L²(a, b)`. -/
noncomputable def primitive (g : L2I a b) : L2I a b := (memLp_primitive g).toLp _

theorem coeFn_primitive (g : L2I a b) :
    primitive g =ᵐ[volume.restrict (Ioo a b)] fun x => ∫ t in a..x, g t :=
  MemLp.coeFn_toLp _

/-- The primitive of `g` has weak derivative `g`. -/
theorem hasWeakDeriv_primitive (g : L2I a b) : HasWeakDeriv (primitive g) g := by
  intro φ hφ
  rcases lt_or_ge a b with hab | hab
  swap
  · simp [Ioo_eq_empty (not_lt.2 hab)]
  have hI := intervalIntegrable_coe g hab.le
  have e : ∫ x in Ioo a b, (primitive g : L2I a b) x * deriv φ x
      = ∫ x in a..b, (∫ t in a..x, g t) * deriv φ x := by
    rw [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_primitive g] with x hx
    rw [hx]
  have e' : ∫ x in Ioo a b, g x * φ x = ∫ x in a..b, g x * φ x := by
    rw [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo]
  have hGac := hI.absolutelyContinuousOnInterval_intervalIntegral (c := a) left_mem_uIcc
  have hφac : AbsolutelyContinuousOnInterval φ a b :=
    (hφ.contDiff.of_le (by exact_mod_cast le_top)).contDiffOn.absolutelyContinuousOnInterval
  have ibp := hGac.integral_mul_deriv_eq_deriv_mul hφac
  have hφa : φ a = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => by simpa using hφ.tsupport_subset h)
  have hφb : φ b = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => by simpa using hφ.tsupport_subset h)
  have hd : ∫ x in a..b, deriv (fun x => ∫ t in a..x, g t) x * φ x = ∫ x in a..b, g x * φ x := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hI.ae_hasDerivAt_integral] with x hx hxI
    rw [(hx (uIoc_subset_uIcc hxI) a left_mem_uIcc).deriv]
  rw [e, e', ibp, hd, hφa, hφb]
  ring

theorem IsTestFn.sub_mul {ψ ψ₀ : ℝ → ℝ} (hψ : IsTestFn a b ψ) (hψ₀ : IsTestFn a b ψ₀)
    (m : ℝ) : IsTestFn a b (fun x => ψ x - m * ψ₀ x) := by
  have hK := hψ.hasCompactSupport.union hψ₀.hasCompactSupport
  have hsub : tsupport ψ ∪ tsupport ψ₀ ⊆ Ioo a b := union_subset hψ.tsupport_subset
    hψ₀.tsupport_subset
  refine ⟨hψ.contDiff.sub (contDiff_const.mul hψ₀.contDiff), ?_, ?_⟩
  · refine HasCompactSupport.intro hK (fun x hx => ?_)
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (Or.inl h)),
      image_eq_zero_of_notMem_tsupport (fun h => hx (Or.inr h))]
    simp
  · refine (closure_minimal ?_ ((isClosed_tsupport _).union (isClosed_tsupport _))).trans hsub
    intro x hx
    by_contra hx'
    apply hx
    show ψ x - m * ψ₀ x = 0
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx' (Or.inl h)),
      image_eq_zero_of_notMem_tsupport (fun h => hx' (Or.inr h))]
    simp

theorem exists_testFn_integral_one (hab : a < b) :
    ∃ ψ : ℝ → ℝ, IsTestFn a b ψ ∧ ∫ x, ψ x = 1 := by
  let f : ContDiffBump ((a + b) / 2) := ⟨(b - a) / 8, (b - a) / 4, by linarith, by linarith⟩
  refine ⟨f.normed volume, ⟨f.contDiff_normed, f.hasCompactSupport_normed, ?_⟩,
    f.integral_normed⟩
  rw [f.tsupport_normed_eq]
  intro x hx
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hx
  simp only [f] at hx
  constructor <;> linarith [hx.1, hx.2]

theorem exists_primitive_testFn (hab : a < b) {χ : ℝ → ℝ} (hχ : IsTestFn a b χ)
    (h0 : ∫ x, χ x = 0) : ∃ Φ : ℝ → ℝ, IsTestFn a b Φ ∧ ∀ x, deriv Φ x = χ x := by
  have hc : Continuous χ := hχ.contDiff.continuous
  have hd : ∀ x, deriv (fun u => ∫ t in a..u, χ t) x = χ x := fun x => hc.deriv_integral χ a x
  have hdiff : Differentiable ℝ (fun u => ∫ t in a..u, χ t) :=
    fun x => (hc.integral_hasStrictDerivAt a x).hasDerivAt.differentiableAt
  have hz : ∀ y, y ∉ Ioo a b → χ y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport (fun h => hy (hχ.tsupport_subset h))
  set K' : Set ℝ := insert ((a + b) / 2) (tsupport χ) with hK'
  have hKc : IsCompact K' := hχ.hasCompactSupport.insert _
  have hne : K'.Nonempty := ⟨_, Set.mem_insert _ _⟩
  have hsub : K' ⊆ Ioo a b := by
    refine insert_subset ?_ hχ.tsupport_subset
    constructor <;> linarith
  have hα := hsub (hKc.sInf_mem hne)
  have hβ := hsub (hKc.sSup_mem hne)
  have hz2 : ∀ y, (y < sInf K' ∨ sSup K' < y) → χ y = 0 := by
    intro y hy
    apply image_eq_zero_of_notMem_tsupport
    intro hyK
    have hyK' : y ∈ K' := Set.mem_insert_of_mem _ hyK
    rcases hy with hy | hy
    · exact absurd (csInf_le hKc.bddBelow hyK') (not_le.2 hy)
    · exact absurd (le_csSup hKc.bddAbove hyK') (not_le.2 hy)
  have hΦb : ∫ t in a..b, χ t = 0 := by
    rw [intervalIntegral.integral_of_le hab.le,
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x (hx : x ∉ Ioc a b) => hz x
        (fun h => hx ⟨h.1, h.2.le⟩)), h0]
  have hzero : ∀ x, (x < sInf K' ∨ sSup K' < x) → ∫ t in a..x, χ t = 0 := by
    intro x hx
    rcases hx with hx | hx
    · rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
      · simp
      · intro t ht
        refine hz2 t (Or.inl ?_)
        rw [uIcc_eq_union] at ht
        rcases ht with ht | ht
        · exact lt_of_le_of_lt ht.2 hx |>.trans_le' le_rfl |> fun h => by linarith [ht.2, hα.1]
        · exact lt_of_le_of_lt ht.2 hα.1 |> fun h => by linarith [ht.2, hα.1]
    · rw [← intervalIntegral.integral_add_adjacent_intervals (b := b)
        (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _), hΦb, zero_add,
        intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
      · simp
      · intro t ht
        refine hz2 t (Or.inr ?_)
        rw [uIcc_eq_union] at ht
        rcases ht with ht | ht
        · linarith [ht.1, hβ.2]
        · linarith [ht.1, hβ.2]
  refine ⟨fun u => ∫ t in a..u, χ t, ⟨?_, ?_, ?_⟩, hd⟩
  · exact contDiff_infty_iff_deriv.2 ⟨hdiff, by simpa only [funext hd] using hχ.contDiff⟩
  · refine HasCompactSupport.intro (isCompact_Icc (a := sInf K') (b := sSup K')) (fun x hx => ?_)
    refine hzero x ?_
    by_contra hh
    push Not at hh
    exact hx ⟨hh.1, hh.2⟩
  · refine (closure_minimal ?_ isClosed_Icc).trans (Icc_subset_Ioo hα.1 hβ.2)
    intro x hx
    by_contra hh
    apply hx
    refine hzero x ?_
    by_contra hh'
    push Not at hh'
    exact hh ⟨hh'.1, hh'.2⟩

/-- **du Bois-Reymond lemma**: a function on an interval whose weak derivative vanishes is
a.e. constant. -/
theorem HasWeakDeriv.ae_eq_const {u : L2I a b} (h : HasWeakDeriv u 0) :
    ∃ c : ℝ, u =ᵐ[volume.restrict (Ioo a b)] fun _ => c := by
  rcases lt_or_ge a b with hab | hab
  swap
  · exact ⟨0, by
      exact ae_iff.2 (measure_mono_null (subset_univ _) (by
        rw [Measure.restrict_apply_univ, Ioo_eq_empty (not_lt.2 hab)]; simp))⟩
  obtain ⟨ψ₀, hψ₀, hψ₀int⟩ := exists_testFn_integral_one hab
  set c := ∫ x in Ioo a b, u x * ψ₀ x with hc
  have key : ∀ ψ, IsTestFn a b ψ → ∫ x in Ioo a b, u x * ψ x = (∫ x, ψ x) * c := by
    intro ψ hψ
    set m := ∫ x, ψ x with hm
    have hχ : IsTestFn a b (fun x => ψ x - m * ψ₀ x) := hψ.sub_mul hψ₀ m
    have hint : ∫ x, (ψ x - m * ψ₀ x) = 0 := by
      rw [integral_sub (hψ.contDiff.continuous.integrable_of_hasCompactSupport
        hψ.hasCompactSupport)
        ((hψ₀.contDiff.continuous.integrable_of_hasCompactSupport
          hψ₀.hasCompactSupport).const_mul m), integral_const_mul, hψ₀int]
      simp [hm]
    obtain ⟨Φ, hΦ, hd⟩ := exists_primitive_testFn hab hχ hint
    have h1 := h Φ hΦ
    have e0 : ∫ x in Ioo a b, (0 : L2I a b) x * Φ x = 0 := by
      rw [← integral_zero (α := ℝ) (μ := volume.restrict (Ioo a b)) (G := ℝ)]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_zero ℝ 2 (volume.restrict (Ioo a b))] with x hx
      rw [hx]; simp
    have e1 : ∫ x in Ioo a b, u x * deriv Φ x
        = (∫ x in Ioo a b, u x * ψ x) - m * c := by
      simp only [hd]
      rw [hc, ← integral_const_mul,
        ← integral_sub (integrable_mul_cont u hψ.contDiff.continuous hψ.hasCompactSupport)
          ((integrable_mul_cont u hψ₀.contDiff.continuous hψ₀.hasCompactSupport).const_mul m)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only; ring
    have e2 : (0 : L2I a b) = 0 := rfl
    rw [e0, e1] at h1
    linarith
  refine ⟨c, ?_⟩
  have hu : Integrable (u : ℝ → ℝ) (volume.restrict (Ioo a b)) :=
    (Lp.memLp u).integrable (by norm_num)
  have hf : LocallyIntegrableOn (fun x => (u : ℝ → ℝ) x - c) (Ioo a b)
      (volume.restrict (Ioo a b)) :=
    (hu.sub (integrable_const c)).locallyIntegrable.locallyIntegrableOn _
  have H := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hf (by
    intro g hg hs hts
    have hz : ∀ x ∉ Ioo a b, g x = 0 := fun x hx =>
      image_eq_zero_of_notMem_tsupport (fun h => hx (hts h))
    have hgc : Continuous g := hg.continuous
    have hgi : Integrable g (volume.restrict (Ioo a b)) :=
      (hgc.integrable_of_hasCompactSupport hs).integrableOn
    have hint : ∫ x in Ioo a b, g x = ∫ x, g x :=
      setIntegral_eq_integral_of_forall_compl_eq_zero hz
    have := key g ⟨hg, hs, hts⟩
    simp only [smul_eq_mul]
    have e : ∀ x, g x * (u x - c) = u x * g x - c * g x := fun x => by ring
    simp only [e]
    rw [integral_sub (integrable_mul_cont u hgc hs) (hgi.const_mul c), integral_const_mul, hint,
      this]
    ring)
  filter_upwards [H, ae_restrict_mem measurableSet_Ioo] with x hx hxI
  have := hx hxI
  linarith

/-- **Fundamental theorem of calculus in `H¹(a, b)`**: if `u' = g` weakly then
`u = c + ∫ₐˣ g` almost everywhere. -/
theorem HasWeakDeriv.ae_eq_const_add_primitive {u g : L2I a b} (h : HasWeakDeriv u g) :
    ∃ c : ℝ, u =ᵐ[volume.restrict (Ioo a b)] fun x => c + ∫ t in a..x, g t := by
  have h1 : HasWeakDeriv (u + -primitive g) (g + -g) := h.add (hasWeakDeriv_primitive g).neg
  rw [add_neg_cancel] at h1
  obtain ⟨c, hc⟩ := h1.ae_eq_const
  refine ⟨c, ?_⟩
  filter_upwards [hc, Lp.coeFn_add u (-primitive g), Lp.coeFn_neg (primitive g),
    coeFn_primitive g] with x e1 e2 e3 e4
  simp only [Pi.add_apply, Pi.neg_apply] at e2 e3
  linarith

/-- A mesh of the interval `[a, b]` with `n + 1` cells: nodes
`a = x₀ < x₁ < ⋯ < x_{n+1} = b`. -/
structure Mesh (a b : ℝ) where
  /-- The number of cells is `n + 1`. -/
  n : ℕ
  /-- The nodes. -/
  node : Fin (n + 2) → ℝ
  strictMono : StrictMono node
  node_zero : node 0 = a
  node_last : node (Fin.last (n + 1)) = b

namespace Mesh

variable (M : Mesh a b)

/-- The `i`-th (open) cell of the mesh. -/
def cell (i : Fin (M.n + 1)) : Set ℝ := Ioo (M.node i.castSucc) (M.node i.succ)

/-- The mesh size `h = maxᵢ (xᵢ₊₁ - xᵢ)`. -/
noncomputable def size : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i : Fin (M.n + 1) =>
    M.node i.succ - M.node i.castSucc

theorem size_pos : 0 < M.size := by
  have h : 0 < M.node (0 : Fin (M.n + 1)).succ - M.node (0 : Fin (M.n + 1)).castSucc :=
    sub_pos.2 (M.strictMono (Fin.castSucc_lt_succ))
  exact lt_of_lt_of_le h (Finset.le_sup' (fun i : Fin (M.n + 1) =>
    M.node i.succ - M.node i.castSucc) (Finset.mem_univ _))

theorem lt (M : Mesh a b) : a < b := by
  have := M.strictMono (show (0 : Fin (M.n + 2)) < Fin.last (M.n + 1) by simp [Fin.lt_def])
  rwa [M.node_zero, M.node_last] at this

theorem cell_subset (i : Fin (M.n + 1)) : M.cell i ⊆ Ioo a b := by
  refine Ioo_subset_Ioo ?_ ?_
  · have := M.strictMono.monotone (Fin.zero_le i.castSucc)
    rwa [M.node_zero] at this
  · have := M.strictMono.monotone (Fin.le_last i.succ)
    rwa [M.node_last] at this

theorem measurableSet_cell (i : Fin (M.n + 1)) : MeasurableSet (M.cell i) := measurableSet_Ioo

theorem cell_pairwise_disjoint :
    Pairwise (Function.onFun Disjoint M.cell) := by
  intro i j hij
  show Disjoint (M.cell i) (M.cell j)
  rw [Set.disjoint_left]
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with h | h
  · have : M.node i.succ ≤ M.node j.castSucc :=
      M.strictMono.monotone (by rw [Fin.le_def]; simpa using Fin.lt_def.1 h)
    exact lt_asymm hxi.2 (lt_of_le_of_lt this hxj.1)
  · have : M.node j.succ ≤ M.node i.castSucc :=
      M.strictMono.monotone (by rw [Fin.le_def]; simpa using Fin.lt_def.1 h)
    exact lt_asymm hxj.2 (lt_of_le_of_lt this hxi.1)

/-- `‖f‖² = ∫ f²` in `L²(a, b)`. -/
theorem norm_sq_eq_integral (f : L2I a b) : ‖f‖ ^ 2 = ∫ x in Ioo a b, (f x) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [sq]

theorem exists_cell_of_mem (x : ℝ) (hx : x ∈ Ioo a b) (hn : x ∉ Set.range M.node) :
    ∃ i, x ∈ M.cell i := by
  classical
  let S : Finset (Fin (M.n + 2)) := Finset.univ.filter fun j => M.node j ≤ x
  have h0 : (0 : Fin (M.n + 2)) ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, M.node_zero]; exact hx.1.le
  have hS : S.Nonempty := ⟨0, h0⟩
  have hjS := Finset.max'_mem S hS
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hjS
  have hne : S.max' hS ≠ Fin.last (M.n + 1) := by
    intro h
    rw [h, M.node_last] at hjS
    exact absurd hx.2 (not_lt.2 hjS)
  obtain ⟨i, hi⟩ := Fin.exists_castSucc_eq.2 hne
  refine ⟨i, ?_, ?_⟩
  · rw [hi]
    exact lt_of_le_of_ne hjS (fun h => hn ⟨_, h⟩)
  · by_contra hcon
    have hmem : i.succ ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]; exact not_lt.1 hcon
    have := Finset.le_max' S _ hmem
    rw [← hi] at this
    exact absurd (Fin.castSucc_lt_succ (i := i)) (not_lt.2 this)

theorem Ioo_ae_eq_iUnion_cell :
    (Ioo a b : Set ℝ) =ᵐ[volume] ⋃ i, M.cell i := by
  rw [ae_eq_set]
  constructor
  · refine measure_mono_null ?_ ((Set.finite_range M.node).measure_zero volume)
    intro x ⟨hx, hx'⟩
    by_contra hn
    obtain ⟨i, hi⟩ := M.exists_cell_of_mem x hx hn
    exact hx' (Set.mem_iUnion.2 ⟨i, hi⟩)
  · rw [Set.diff_eq_empty.2 (Set.iUnion_subset M.cell_subset)]; simp

theorem integral_Ioo_eq_sum {f : ℝ → ℝ} (hf : IntegrableOn f (Ioo a b)) :
    ∫ x in Ioo a b, f x = ∑ i, ∫ x in M.cell i, f x := by
  rw [setIntegral_congr_set M.Ioo_ae_eq_iUnion_cell,
    integral_iUnion_fintype M.measurableSet_cell M.cell_pairwise_disjoint]
  exact fun i => hf.mono_set (M.cell_subset i)

/-- Cauchy–Schwarz on an interval: `(∫ₚˣ g)² ≤ (x - p) ∫ₚˣ g²`. -/
theorem sq_intervalIntegral_le {g : ℝ → ℝ} {p x : ℝ} (hpx : p ≤ x)
    (hg : IntervalIntegrable g volume p x) (hg2 : IntervalIntegrable (fun t => g t ^ 2) volume p x) :
    (∫ t in p..x, g t) ^ 2 ≤ (x - p) * ∫ t in p..x, g t ^ 2 := by
  rcases hpx.eq_or_lt with h | h
  · subst h; simp
  have hL : 0 < x - p := sub_pos.2 h
  set J := ∫ t in p..x, g t with hJ
  set Q := ∫ t in p..x, g t ^ 2 with hQ
  set l := J / (x - p) with hl
  have key : ∫ t in p..x, (2 * l * g t - l ^ 2) ≤ Q := by
    refine intervalIntegral.integral_mono_on hpx
      ((hg.const_mul _).sub intervalIntegrable_const) hg2 (fun t _ => ?_)
    nlinarith [sq_nonneg (g t - l)]
  rw [intervalIntegral.integral_sub (hg.const_mul _) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at key
  have e : 2 * l * J - (x - p) • l ^ 2 = J ^ 2 / (x - p) := by
    rw [smul_eq_mul, hl]; field_simp; ring
  rw [e, div_le_iff₀ hL] at key
  linarith

/-- The piecewise constant functions on the mesh, as a subspace of `L²(a, b)`. -/
def pcConst : Submodule ℝ (L2I a b) where
  carrier := {u | ∃ c : Fin (M.n + 1) → ℝ,
    u =ᵐ[volume.restrict (Ioo a b)] fun x => ∑ i, (M.cell i).indicator (fun _ => c i) x}
  add_mem' := by
    rintro u v ⟨c, hc⟩ ⟨c', hc'⟩
    refine ⟨c + c', ?_⟩
    filter_upwards [Lp.coeFn_add u v, hc, hc'] with x h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hx : x ∈ M.cell i <;> simp [hx]
  zero_mem' := by
    refine ⟨0, ?_⟩
    filter_upwards [Lp.coeFn_zero ℝ 2 (volume.restrict (Ioo a b))] with x h1
    rw [h1]; simp
  smul_mem' := by
    rintro r u ⟨c, hc⟩
    refine ⟨r • c, ?_⟩
    filter_upwards [Lp.coeFn_smul r u, hc] with x h1 h2
    rw [h1, Pi.smul_apply, h2, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hx : x ∈ M.cell i <;> simp [hx]

/-- The indicator function of the `i`-th cell, as an element of `L²(a, b)`. -/
noncomputable def cellIndicator (i : Fin (M.n + 1)) : L2I a b :=
  indicatorConstLp 2 (M.measurableSet_cell i) (measure_ne_top _ _) (1 : ℝ)

theorem coeFn_cellIndicator (i : Fin (M.n + 1)) :
    M.cellIndicator i =ᵐ[volume.restrict (Ioo a b)] (M.cell i).indicator fun _ => (1 : ℝ) :=
  indicatorConstLp_coeFn

theorem coeFn_sum_cellIndicator (c : Fin (M.n + 1) → ℝ) :
    (∑ i, c i • M.cellIndicator i : L2I a b) =ᵐ[volume.restrict (Ioo a b)]
      fun x => ∑ i, (M.cell i).indicator (fun _ => c i) x := by
  have hE : ∀ᵐ x ∂(volume.restrict (Ioo a b)), ∀ i, M.cellIndicator i x
      = (M.cell i).indicator (fun _ => (1 : ℝ)) x :=
    ae_all_iff.2 fun i => M.coeFn_cellIndicator i
  have hs : ∀ᵐ x ∂(volume.restrict (Ioo a b)), ∀ i, (c i • M.cellIndicator i) x
      = c i * M.cellIndicator i x :=
    ae_all_iff.2 fun i => Lp.coeFn_smul (c i) (M.cellIndicator i)
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i => c i • M.cellIndicator i),
    hE, hs] with x h2 h3 h4
  rw [h2]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h4, h3]
  by_cases hx : x ∈ M.cell i <;> simp [hx]

theorem sum_cellIndicator_mem (c : Fin (M.n + 1) → ℝ) :
    (∑ i, c i • M.cellIndicator i : L2I a b) ∈ M.pcConst :=
  ⟨c, M.coeFn_sum_cellIndicator c⟩

theorem pcConst_le_span : M.pcConst ≤ Submodule.span ℝ (Set.range M.cellIndicator) := by
  rintro u ⟨c, hc⟩
  have : u = ∑ i, c i • M.cellIndicator i :=
    Lp.ext (hc.trans (M.coeFn_sum_cellIndicator c).symm)
  rw [this]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

instance : FiniteDimensional ℝ M.pcConst :=
  haveI : FiniteDimensional ℝ (Submodule.span ℝ (Set.range M.cellIndicator)) :=
    Module.Finite.span_of_finite ℝ (Set.finite_range _)
  Submodule.finiteDimensional_of_le M.pcConst_le_span

theorem node_mem_Icc (k : Fin (M.n + 2)) : M.node k ∈ Icc a b := by
  constructor
  · have := M.strictMono.monotone (Fin.zero_le k)
    rwa [M.node_zero] at this
  · have := M.strictMono.monotone (Fin.le_last k)
    rwa [M.node_last] at this

theorem cell_length_le_size (i : Fin (M.n + 1)) : M.node i.succ - M.node i.castSucc ≤ M.size :=
  Finset.le_sup' (fun i : Fin (M.n + 1) => M.node i.succ - M.node i.castSucc)
    (Finset.mem_univ i)

theorem intervalIntegrable_of_integrableOn_Ioo {f : ℝ → ℝ} (hab : a ≤ b)
    (hf : IntegrableOn f (Ioo a b)) {y z : ℝ} (hy : y ∈ Icc a b) (hz : z ∈ Icc a b) :
    IntervalIntegrable f volume y z :=
  ((intervalIntegrable_iff_integrableOn_Ioo_of_le hab).2 hf).mono_set
    (uIcc_subset_uIcc (by rwa [uIcc_of_le hab]) (by rwa [uIcc_of_le hab]))

/-- **Approximation by piecewise constants**: a function with weak derivative `g ∈ L²` is
within `h ‖g‖` of the piecewise constants, in `L²`. -/
theorem exists_pcConst_near {u g : L2I a b} (h : HasWeakDeriv u g) :
    ∃ s ∈ M.pcConst, ‖u - s‖ ≤ M.size * ‖g‖ := by
  obtain ⟨c, hc⟩ := h.ae_eq_const_add_primitive
  set m : Fin (M.n + 1) → ℝ := fun i => c + ∫ t in a..M.node i.castSucc, g t with hm
  refine ⟨∑ i, m i • M.cellIndicator i, M.sum_cellIndicator_mem m, ?_⟩
  set s : L2I a b := ∑ i, m i • M.cellIndicator i with hs
  set F : ℝ → ℝ := fun x => c + (∫ t in a..x, g t) -
    ∑ i, (M.cell i).indicator (fun _ => m i) x with hF
  have hae : (u - s : L2I a b) =ᵐ[volume.restrict (Ioo a b)] F := by
    filter_upwards [Lp.coeFn_sub u s, hc, M.coeFn_sum_cellIndicator m] with x h1 h2 h3
    rw [h1, Pi.sub_apply, h2, hF]
    simp only
    rw [hs, h3]
  have hF2 : Integrable (fun x => F x ^ 2) (volume.restrict (Ioo a b)) :=
    ((Lp.memLp (u - s)).integrable_sq).congr (by
      filter_upwards [hae] with x hx; rw [hx])
  have hg2 : Integrable (fun x => (g x) ^ 2) (volume.restrict (Ioo a b)) :=
    (Lp.memLp g).integrable_sq
  have hgi : Integrable (g : ℝ → ℝ) (volume.restrict (Ioo a b)) :=
    (Lp.memLp g).integrable (by norm_num)
  have hnorm : ‖u - s‖ ^ 2 = ∫ x in Ioo a b, F x ^ 2 := by
    rw [norm_sq_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx; rw [hx]
  have hab : a ≤ b := M.lt.le
  have hcell : ∀ i, ∫ x in M.cell i, F x ^ 2
      ≤ M.size ^ 2 * ∫ x in M.cell i, (g x) ^ 2 := by
    intro i
    set p := M.node i.castSucc with hp
    set q := M.node i.succ with hq
    have hpq : p < q := M.strictMono (Fin.castSucc_lt_succ)
    have hqs : q - p ≤ M.size := M.cell_length_le_size i
    have hg2c : IntegrableOn (fun x => (g x) ^ 2) (M.cell i) := IntegrableOn.mono_set hg2 (M.cell_subset i)
    have hQ : 0 ≤ ∫ x in M.cell i, (g x) ^ 2 := setIntegral_nonneg (M.measurableSet_cell i)
      (fun x _ => sq_nonneg _)
    have hpI : p ∈ Icc a b := M.node_mem_Icc _
    have hpt : ∀ x ∈ M.cell i, F x ^ 2 ≤ M.size * ∫ x in M.cell i, (g x) ^ 2 := by
      intro x hx
      have hxs : ∑ j, (M.cell j).indicator (fun _ => m j) x = m i := by
        rw [Finset.sum_eq_single i]
        · simp [hx]
        · intro j _ hji
          refine Set.indicator_of_notMem (fun hxj => ?_) _
          exact Set.disjoint_left.1 (M.cell_pairwise_disjoint hji) hxj hx
        · simp
      have hxI : x ∈ Ioo a b := M.cell_subset i hx
      have hxI' : x ∈ Icc a b := Ioo_subset_Icc_self hxI
      have hga : IntervalIntegrable (g : ℝ → ℝ) volume a x :=
        intervalIntegrable_of_integrableOn_Ioo hab hgi (left_mem_Icc.2 hab) hxI'
      have hgp : IntervalIntegrable (g : ℝ → ℝ) volume a p :=
        intervalIntegrable_of_integrableOn_Ioo hab hgi (left_mem_Icc.2 hab) hpI
      have hgpx : IntervalIntegrable (g : ℝ → ℝ) volume p x :=
        intervalIntegrable_of_integrableOn_Ioo hab hgi hpI hxI'
      have hg2px : IntervalIntegrable (fun t => (g t) ^ 2) volume p x :=
        intervalIntegrable_of_integrableOn_Ioo hab hg2 hpI hxI'
      have hFx : F x = ∫ t in p..x, g t := by
        simp only [hF]
        rw [hxs, hm]
        simp only
        rw [← intervalIntegral.integral_interval_sub_left hga hgp]; ring
      have hpx : p ≤ x := hx.1.le
      have h1 := sq_intervalIntegral_le hpx hgpx hg2px
      have h2 : ∫ t in p..x, g t ^ 2 ≤ ∫ t in M.cell i, g t ^ 2 := by
        rw [intervalIntegral.integral_of_le hpx, integral_Ioc_eq_integral_Ioo]
        exact setIntegral_mono_set hg2c (Filter.Eventually.of_forall fun t => sq_nonneg _)
          (Filter.Eventually.of_forall fun t ht => ⟨ht.1, ht.2.trans hx.2⟩)
      have h3 : x - p ≤ M.size := by linarith [hx.2]
      rw [hFx]
      calc _ ≤ (x - p) * ∫ t in p..x, (g t) ^ 2 := h1
        _ ≤ M.size * ∫ t in M.cell i, (g t) ^ 2 :=
          mul_le_mul h3 h2 (intervalIntegral.integral_nonneg hpx (fun _ _ => sq_nonneg _))
            M.size_pos.le
    have hcI : IntegrableOn (fun x => F x ^ 2) (M.cell i) := IntegrableOn.mono_set hF2 (M.cell_subset i)
    have hcc : IntegrableOn (fun _ : ℝ => M.size * ∫ x in M.cell i, (g x) ^ 2) (M.cell i) :=
      integrableOn_const (by simp [Mesh.cell])
    calc ∫ x in M.cell i, F x ^ 2
        ≤ ∫ _ in M.cell i, M.size * ∫ x in M.cell i, (g x) ^ 2 :=
          setIntegral_mono_on hcI hcc (M.measurableSet_cell i) hpt
      _ = (q - p) * (M.size * ∫ x in M.cell i, (g x) ^ 2) := by
          rw [setIntegral_const, smul_eq_mul]
          congr 1
          exact Real.volume_real_Ioo_of_le hpq.le
      _ ≤ M.size * (M.size * ∫ x in M.cell i, (g x) ^ 2) :=
          mul_le_mul_of_nonneg_right hqs (mul_nonneg M.size_pos.le hQ)
      _ = M.size ^ 2 * ∫ x in M.cell i, (g x) ^ 2 := by ring
  have hsq : ‖u - s‖ ^ 2 ≤ (M.size * ‖g‖) ^ 2 := by
    rw [hnorm, M.integral_Ioo_eq_sum (f := fun x => F x ^ 2) hF2, mul_pow,
      norm_sq_eq_integral, M.integral_Ioo_eq_sum (f := fun x => (g x) ^ 2) hg2, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => hcell i
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg M.size_pos.le (norm_nonneg _))
    two_ne_zero).1 hsq

end Mesh

end FEEC.Interval
