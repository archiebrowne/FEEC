/-
Approximation estimate for the tensor-product quasi-interpolant on smooth functions.
-/
import FEEC.Tensor.ApproxScalar
import FEEC.Tensor.ProjectionBound
import FEEC.Fourier.Eigenforms

/-!
# Approximation by the tensor-product projection

For a trigonometric polynomial form `g` (a combination of eigenforms), `‖[g] - πₕ[g]‖_{L²(box)}² ≤ C h² ∑ᵢ ‖∂ᵢ g‖²_{L²(box)}`, where
`πₕ` is the `L²` operator of the dual system (`dualOp`) and `h` bounds all mesh sizes. The
constant depends only on `n` and `k`.
-/

namespace FEEC

namespace Tensor

open MeasureTheory

local notation "⟪" x ", " y "⟫" => inner ℝ x y

theorem memLp_of_continuous_box {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {n : ℕ}
    (e : OrthonormalBasis (Fin n) ℝ E) (a b : Fin n → ℝ) {F : Type*} [NormedAddCommGroup F]
    {g : E → F} (hg : Continuous g) : MemLp g 2 (volume.restrict (box e a b)) := by
  haveI : IsFiniteMeasure (volume.restrict (box e a b)) :=
    ⟨by simpa using volume_box_lt_top e a b⟩
  have hbd : Bornology.IsBounded (box e a b) := by
    rw [Metric.isBounded_iff_subset_closedBall (0 : E)]
    refine ⟨∑ i, (|a i| + |b i|), fun x hx => ?_⟩
    rw [mem_closedBall_zero_iff]
    calc ‖x‖ = ‖∑ i, ⟪e i, x⟫ • e i‖ := by rw [e.sum_repr' x]
      _ ≤ ∑ i, ‖⟪e i, x⟫ • e i‖ := norm_sum_le _ _
      _ ≤ ∑ i, (|a i| + |b i|) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_smul, e.norm_eq_one, mul_one, Real.norm_eq_abs]
        have h1 := hx i
        rw [abs_le]
        constructor <;> nlinarith [h1.1, h1.2, abs_nonneg (a i), abs_nonneg (b i),
          neg_abs_le (a i), le_abs_self (b i), neg_abs_le (b i), le_abs_self (a i)]
  have hc : IsCompact (closure (box e a b)) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure hbd.closure
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn hg.continuousOn
  refine MemLp.of_bound hg.aestronglyMeasurable C ?_
  exact (ae_restrict_iff' (measurableSet_box e a b)).2
    (Filter.Eventually.of_forall fun x hx => hC x (subset_closure hx))


section helpers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {n : ℕ}

/-- The component `x ↦ ⟪g x, dx_T⟫` of a form-valued function. -/
noncomputable def compC (e : OrthonormalBasis (Fin n) ℝ E) {k : ℕ} (T : Fin k → Fin n)
    (g : E → E [⋀^Fin k]→L[ℝ] ℝ) (x : E) : ℝ :=
  ⟪Covector.ofAlt (g x), Covector.ofAlt (dxT e k T)⟫

theorem compC_mem_span (e : OrthonormalBasis (Fin n) ℝ E) (a b : Fin n → ℝ) {k : ℕ}
    (T : Fin k → Fin n) (g : E → E [⋀^Fin k]→L[ℝ] ℝ)
    (hgs : g ∈ Submodule.span ℝ (Set.range fun p : (Fin k → Fin n) × (Fin n → ℕ) =>
        Fourier.eigForm e a b p.1 p.2)) :
    compC e T g ∈ Submodule.span ℝ
      (Set.range fun p : (Fin n → Bool) × (Fin n → ℕ) => trigProd e a b p.1 p.2) := by
  induction hgs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨S, m⟩, rfl⟩ := hx
    have : compC e T (Fourier.eigForm e a b S m) =
        ⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k T)⟫ • trigProd e a b (pat S) m := by
      funext x
      simp [compC, Fourier.eigForm, real_inner_smul_left, mul_comm]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(pat S, m), rfl⟩)
  | zero =>
    have : compC e T (0 : E → E [⋀^Fin k]→L[ℝ] ℝ) = 0 := by
      funext x; simp [compC]
    rw [this]; exact Submodule.zero_mem _
  | add f g _ _ hf hg =>
    have : compC e T (f + g) = compC e T f + compC e T g := by
      funext x; simp [compC, inner_add_left]
    rw [this]; exact Submodule.add_mem _ hf hg
  | smul c f _ hf =>
    have : compC e T (c • f) = c • compC e T f := by
      funext x; simp [compC, real_inner_smul_left]
    rw [this]; exact Submodule.smul_mem _ _ hf

theorem continuous_compC (e : OrthonormalBasis (Fin n) ℝ E) {k : ℕ} (T : Fin k → Fin n)
    {g : E → E [⋀^Fin k]→L[ℝ] ℝ} (hg : Continuous g) : Continuous (compC e T g) :=
  (Covector.ofAlt.continuous.comp hg).inner continuous_const

theorem fderiv_compC (e : OrthonormalBasis (Fin n) ℝ E) {k : ℕ} (T : Fin k → Fin n)
    {g : E → E [⋀^Fin k]→L[ℝ] ℝ} (hg : ContDiff ℝ 1 g) (x v : E) :
    fderiv ℝ (compC e T g) x v =
      ⟪Covector.ofAlt (fderiv ℝ g x v), Covector.ofAlt (dxT e k T)⟫ := by
  let L : (E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ :=
    (innerSL ℝ (Covector.ofAlt (dxT e k T))).comp
      (Covector.ofAlt : (E [⋀^Fin k]→L[ℝ] ℝ) ≃L[ℝ] Covector E k).toContinuousLinearMap
  have hc : compC e T g = fun x => L (g x) := by
    funext x; simp [L, compC, real_inner_comm]
  have hd : DifferentiableAt ℝ g x := (hg.differentiable one_ne_zero) x
  have hf : HasFDerivAt (fun x => L (g x)) (L.comp (fderiv ℝ g x)) x :=
    L.hasFDerivAt.comp x hd.hasFDerivAt
  rw [hc, hf.fderiv]
  simp [L, real_inner_comm]

theorem sq_fderiv_compC_le (e : OrthonormalBasis (Fin n) ℝ E) {k : ℕ} (T : Fin k → Fin n)
    {g : E → E [⋀^Fin k]→L[ℝ] ℝ} (hg : ContDiff ℝ 1 g) (x v : E) :
    (fderiv ℝ (compC e T g) x v) ^ 2 ≤ ‖Covector.ofAlt (fderiv ℝ g x v)‖ ^ 2 := by
  rw [fderiv_compC e T hg]
  have h1 := abs_real_inner_le_norm (Covector.ofAlt (fderiv ℝ g x v)) (Covector.ofAlt (dxT e k T))
  have h2 := norm_ofAlt_dxT_le e T
  have h3 : |⟪Covector.ofAlt (fderiv ℝ g x v), Covector.ofAlt (dxT e k T)⟫| ≤
      ‖Covector.ofAlt (fderiv ℝ g x v)‖ :=
    h1.trans (by nlinarith [norm_nonneg (Covector.ofAlt (fderiv ℝ g x v))])
  calc _ = |⟪Covector.ofAlt (fderiv ℝ g x v), Covector.ofAlt (dxT e k T)⟫| ^ 2 := (sq_abs _).symm
    _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) h3 2

theorem norm_sq_le_integral {Ω : Set E} {k : ℕ} (X : L2Form Ω k) (H : E → ℝ) (α : Covector E k)
    (hα : ‖α‖ ≤ 1) (hX : X =ᵐ[volume.restrict Ω] fun x => H x • α)
    (hH : Integrable (fun x => H x ^ 2) (volume.restrict Ω)) :
    ‖X‖ ^ 2 ≤ ∫ x in Ω, H x ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => ?_) hH ?_
  · exact real_inner_self_nonneg
  · filter_upwards [hX] with x hx
    rw [hx, real_inner_self_eq_norm_sq, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    calc H x ^ 2 * ‖α‖ ^ 2 ≤ H x ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hα) (sq_nonneg _)
      _ = _ := mul_one _

end helpers


section dualop

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {n : ℕ}
  {e : OrthonormalBasis (Fin n) ℝ E} {a b : Fin n → ℝ} {N : Fin n → ℕ}

/-- The class of a continuous form-valued function in `L²Λᵏ` of the box. -/
noncomputable def wOf (e : OrthonormalBasis (Fin n) ℝ E) (a b : Fin n → ℝ) {k : ℕ}
    (g : E → E [⋀^Fin k]→L[ℝ] ℝ) (hg : Continuous g) : L2Form (box e a b) k :=
  (memLp_of_continuous_box e a b (Covector.ofAlt.continuous.comp hg)).toLp _

/-- The class of the `T`-component of a continuous form-valued function. -/
noncomputable def Fc (e : OrthonormalBasis (Fin n) ℝ E) (a b : Fin n → ℝ) {k : ℕ}
    (T : Fin k → Fin n) (g : E → E [⋀^Fin k]→L[ℝ] ℝ) (hg : Continuous g) :
    L2Form (box e a b) k :=
  (memLp_of_continuous_box e a b
    ((continuous_compC e T hg).smul
      (continuous_const (y := Covector.ofAlt (dxT e k T))))).toLp _

theorem coeFn_Fc {k : ℕ} (T : Fin k → Fin n) (g : E → E [⋀^Fin k]→L[ℝ] ℝ) (hg : Continuous g) :
    Fc e a b T g hg =ᵐ[volume.restrict (box e a b)]
      fun x => compC e T g x • Covector.ofAlt (dxT e k T) :=
  MemLp.coeFn_toLp _

theorem wOf_eq_sum {k : ℕ} (g : E → E [⋀^Fin k]→L[ℝ] ℝ) (hg : Continuous g) :
    wOf e a b g hg = ((k.factorial : ℝ))⁻¹ • ∑ T : Fin k → Fin n, Fc e a b T g hg := by
  refine Lp.ext ?_
  have h1 : ∀ᵐ x ∂(volume.restrict (box e a b)), ∀ T : Fin k → Fin n,
      Fc e a b T g hg x = compC e T g x • Covector.ofAlt (dxT e k T) := by
    rw [ae_all_iff]; intro T; exact coeFn_Fc T g hg
  filter_upwards [MemLp.coeFn_toLp (Covector.ofAlt.continuous.comp hg |> memLp_of_continuous_box e a b),
    Lp.coeFn_smul ((k.factorial : ℝ))⁻¹ (∑ T : Fin k → Fin n, Fc e a b T g hg),
    Lp.coeFn_finsetSum (μ := volume.restrict (box e a b)) Finset.univ
      (fun T : Fin k → Fin n => Fc e a b T g hg), h1] with x hx h2 h3 h4
  rw [wOf, hx, h2, Pi.smul_apply, h3, Finset.sum_apply]
  simp only [h4]
  have := congrArg Covector.ofAlt (sum_inner_dxT_smul e (g x))
  simpa [map_smul, map_sum, compC] using this.symm

theorem dualOp_eq_sum (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i) (k : ℕ)
    (w : L2Form (box e a b) k) :
    (deRhamComplex (isOpen_box e a b)).dualOp (shapeH (e := e) hab hN)
        (dualL (e := e) hab hN) (fun k => ((k.factorial : ℝ))⁻¹) k w =
      ((k.factorial : ℝ))⁻¹ • ∑ T : Fin k → Fin n, ∑ q : (i : Fin n) → Fin (N i + 2),
        ⟪w, dualLp (e := e) hab hN T (fun i => (q i : ℕ))⟫ •
          shapeLp e a b N T (fun i => (q i : ℕ)) := by
  rw [HilbertComplex.dualOp_apply]
  congr 1
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun T _ => Finset.sum_congr rfl fun q _ => ?_
  rw [real_inner_comm]
  rfl

theorem inner_wOf_dualLp (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i) {k : ℕ}
    (g : E → E [⋀^Fin k]→L[ℝ] ℝ) (hg : Continuous g) (T : Fin k → Fin n)
    (q : (i : Fin n) → Fin (N i + 2)) :
    ⟪wOf e a b g hg, dualLp (e := e) hab hN T (fun i => (q i : ℕ))⟫ =
      ∫ y in box e a b, dualP e a b N (pat T) (fun i => (q i : ℕ)) y * compC e T g y := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (Covector.ofAlt.continuous.comp hg |> memLp_of_continuous_box e a b),
    coeFn_dualLp (e := e) hab hN T (fun i => (q i : ℕ))] with y h1 h2
  rw [wOf, h1, h2]
  simp [dualForm, dualP, dualProd, compC, real_inner_smul_right, mul_comm]

theorem sum_shapeLp_ae {k : ℕ} (T : Fin k → Fin n) (c : ((i : Fin n) → Fin (N i + 2)) → ℝ) :
    (∑ q : (i : Fin n) → Fin (N i + 2), c q • shapeLp e a b N T (fun i => (q i : ℕ)) :
        L2Form (box e a b) k) =ᵐ[volume.restrict (box e a b)]
      fun x => (∑ q : (i : Fin n) → Fin (N i + 2),
        shapeP e a b N (pat T) (fun i => (q i : ℕ)) x * c q) • Covector.ofAlt (dxT e k T) := by
  have h2 : ∀ᵐ x ∂(volume.restrict (box e a b)), ∀ q : (i : Fin n) → Fin (N i + 2),
      shapeLp e a b N T (fun i => (q i : ℕ)) x =
        shapeP e a b N (pat T) (fun i => (q i : ℕ)) x • Covector.ofAlt (dxT e k T) := by
    rw [ae_all_iff]; intro q
    filter_upwards [coeFn_shapeLp (e := e) (a := a) (b := b) (N := N) T (fun i => (q i : ℕ))]
      with x hx
    rw [hx]
    simp [shapeForm, shapeP, shapeProd]
  filter_upwards [coeFn_sum_smul' Finset.univ c
    (fun q : (i : Fin n) → Fin (N i + 2) => shapeLp e a b N T (fun i => (q i : ℕ))), h2]
    with x h1 h3
  rw [h1, Finset.sum_smul]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [h3 q, smul_smul, mul_comm]

end dualop


section final

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {n : ℕ}

theorem memLp_sub_quasiP (e : OrthonormalBasis (Fin n) ℝ E) (a b : Fin n → ℝ) (N : Fin n → ℕ)
    {k : ℕ} (T : Fin k → Fin n) {G : E → ℝ} (hG : Continuous G) :
    MemLp (fun x => G x - quasiP e a b N (pat T) G x) 2 (volume.restrict (box e a b)) := by
  haveI : IsFiniteMeasure (volume.restrict (box e a b)) :=
    ⟨by simpa using volume_box_lt_top e a b⟩
  refine (memLp_of_continuous_box e a b hG).sub ?_
  set c : ((i : Fin n) → Fin (N i + 2)) → ℝ := fun q =>
    ∫ y in box e a b, dualP e a b N (pat T) (fun i => (q i : ℕ)) y * G y with hc
  have hq : quasiP e a b N (pat T) G = fun x => ∑ q : (i : Fin n) → Fin (N i + 2),
      shapeProd e a b N T (fun i => (q i : ℕ)) x * c q := rfl
  rw [hq]
  refine MemLp.of_bound ?_ (∑ q, |c q|) (Filter.Eventually.of_forall fun x => ?_)
  · exact (Finset.measurable_sum _ fun q _ =>
      (measurable_shapeProd _ _).mul_const _).aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun q _ => ?_)
    rw [abs_mul]
    calc _ ≤ 1 * |c q| := by
          gcongr; exact abs_shapeProd_le_one _ _ x
      _ = _ := one_mul _

end final

/-- **Approximation estimate** for smooth forms. -/
theorem exists_approx_smooth (n k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E] (e : OrthonormalBasis (Fin n) ℝ E)
      (a b : Fin n → ℝ) (N : Fin n → ℕ) (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i) (h : ℝ)
      (hh : ∀ i, Ref.meshH (a i) (b i) (N i) ≤ h)
      (g : E → E [⋀^Fin k]→L[ℝ] ℝ) (hg : ContDiff ℝ 1 g)
      (hgs : g ∈ Submodule.span ℝ (Set.range fun p : (Fin k → Fin n) × (Fin n → ℕ) =>
        Fourier.eigForm e a b p.1 p.2)),
      ‖(memLp_of_continuous_box e a b (Covector.ofAlt.continuous.comp hg.continuous)).toLp _ -
          (deRhamComplex (isOpen_box e a b)).dualOp (shapeH (e := e) hab hN)
            (dualL (e := e) hab hN) (fun k => ((k.factorial : ℝ))⁻¹) k
            ((memLp_of_continuous_box e a b
              (Covector.ofAlt.continuous.comp hg.continuous)).toLp _)‖ ^ 2 ≤
        C * h ^ 2 * ∑ i, ∫ x in box e a b, ‖Covector.ofAlt (fderiv ℝ g x (e i))‖ ^ 2 := by
  obtain ⟨C₀, hC₀, hC⟩ := exists_approx_trig n
  refine ⟨(((k.factorial : ℝ))⁻¹ * ((n ^ k : ℕ) : ℝ)) ^ 2 * C₀, by positivity, ?_⟩
  intro E _ _ _ _ _ e a b N hab hN h hh g hg hgs
  haveI : IsFiniteMeasure (volume.restrict (box e a b)) :=
    ⟨by simpa using volume_box_lt_top e a b⟩
  have hgc : Continuous g := hg.continuous
  set S := ∑ i, ∫ x in box e a b, ‖Covector.ofAlt (fderiv ℝ g x (e i))‖ ^ 2 with hSdef
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => integral_nonneg fun _ => sq_nonneg _
  set B := C₀ * h ^ 2 * S with hBdef
  have hB : 0 ≤ B := by positivity
  set c : (Fin k → Fin n) → ((i : Fin n) → Fin (N i + 2)) → ℝ := fun T q =>
    ∫ y in box e a b, dualP e a b N (pat T) (fun i => (q i : ℕ)) y * compC e T g y with hc
  set X : (Fin k → Fin n) → L2Form (box e a b) k := fun T =>
    Fc e a b T g hgc - ∑ q : (i : Fin n) → Fin (N i + 2), c T q •
      shapeLp e a b N T (fun i => (q i : ℕ)) with hX
  have hD : wOf e a b g hgc - (deRhamComplex (isOpen_box e a b)).dualOp (shapeH (e := e) hab hN)
      (dualL (e := e) hab hN) (fun k => ((k.factorial : ℝ))⁻¹) k (wOf e a b g hgc) =
      ((k.factorial : ℝ))⁻¹ • ∑ T : Fin k → Fin n, X T := by
    rw [dualOp_eq_sum]
    nth_rw 1 [wOf_eq_sum]
    rw [← smul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun T _ => ?_
    simp only [hX, hc]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [inner_wOf_dualLp hab hN g hgc T q]
  have hT : ∀ T, ‖X T‖ ≤ Real.sqrt B := by
    intro T
    have hGc : Continuous (compC e T g) := continuous_compC e T hgc
    have hH := memLp_sub_quasiP e a b N T hGc
    have hae : X T =ᵐ[volume.restrict (box e a b)] fun x =>
        (compC e T g x - quasiP e a b N (pat T) (compC e T g) x) • Covector.ofAlt (dxT e k T) := by
      filter_upwards [coeFn_Fc (e := e) (a := a) (b := b) T g hgc,
        Lp.coeFn_sub (Fc e a b T g hgc) (∑ q : (i : Fin n) → Fin (N i + 2), c T q •
          shapeLp e a b N T (fun i => (q i : ℕ))),
        sum_shapeLp_ae (e := e) (a := a) (b := b) (N := N) T (c T)] with x h1 h2 h3
      simp only [hX]
      rw [h2, Pi.sub_apply, h1, h3, sub_smul]
      rfl
    have h1 := norm_sq_le_integral (X T) _ _ (norm_ofAlt_dxT_le e T) hae hH.integrable_sq
    have h2 := hC e a b N hab hN h hh (pat T) (compC e T g) (compC_mem_span e a b T g hgs)
    have h3 : ∑ i, ∫ x in box e a b, (fderiv ℝ (compC e T g) x (e i)) ^ 2 ≤ S := by
      refine Finset.sum_le_sum fun i _ => ?_
      have hfc : Continuous fun x => ‖Covector.ofAlt (fderiv ℝ g x (e i))‖ :=
        (Covector.ofAlt.continuous.comp
          ((hg.continuous_fderiv one_ne_zero).clm_apply continuous_const)).norm
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => sq_nonneg _)
        (memLp_of_continuous_box e a b hfc).integrable_sq
        (Filter.Eventually.of_forall fun x => sq_fderiv_compC_le e T hg x (e i))
    have h4 : ‖X T‖ ^ 2 ≤ B := by
      refine h1.trans (h2.trans ?_)
      exact mul_le_mul_of_nonneg_left h3 (by positivity)
    exact (le_abs_self _).trans (Real.abs_le_sqrt h4)
  have hnorm : ‖wOf e a b g hgc - (deRhamComplex (isOpen_box e a b)).dualOp
      (shapeH (e := e) hab hN) (dualL (e := e) hab hN) (fun k => ((k.factorial : ℝ))⁻¹) k
      (wOf e a b g hgc)‖ ≤ ((k.factorial : ℝ))⁻¹ * ((n ^ k : ℕ) * Real.sqrt B) := by
    rw [hD, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc _ ≤ ∑ T : Fin k → Fin n, ‖X T‖ := norm_sum_le _ _
      _ ≤ ∑ _T : Fin k → Fin n, Real.sqrt B := Finset.sum_le_sum fun T _ => hT T
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul]
  change ‖wOf e a b g hgc - (deRhamComplex (isOpen_box e a b)).dualOp (shapeH (e := e) hab hN)
      (dualL (e := e) hab hN) (fun k => ((k.factorial : ℝ))⁻¹) k (wOf e a b g hgc)‖ ^ 2 ≤ _
  calc _ ≤ (((k.factorial : ℝ))⁻¹ * ((n ^ k : ℕ) * Real.sqrt B)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ = (((k.factorial : ℝ))⁻¹ * ((n ^ k : ℕ) : ℝ)) ^ 2 * B := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hB]; ring
    _ = _ := by rw [hBdef]; ring

end Tensor

end FEEC
