/-
Compactly supported antiderivatives along a direction.
-/
import FEEC.DeRham.LineIntegral

/-!
# Compactly supported antiderivatives along a direction

Let `θ` be a smooth bump on `(a, b)` with integral one and `Θ = cumul θ` its cumulative
integral. For a compactly supported `f : E → F` and a unit vector `e`,

`lineG e θ f x = Θ(⟪e, x⟫) • lineInt e f x - halfLineInt e f x`

satisfies `∂_e (lineG e θ f) = θ(⟪e, x⟫) • lineInt e f x - f x`, and, unlike `halfLineInt e f`,
it has compact support: it vanishes when `⟪e, x⟫` lies below or above the supports of `θ` and
of `f`. If `Ω` is a *slab* in direction `e` over `(a, b)` (`FEEC.IsSlab`), `lineG e θ` maps
functions compactly supported in `Ω` to functions compactly supported in `Ω`.
-/

namespace FEEC

open MeasureTheory

local notation "⟪" x ", " y "⟫" => inner ℝ x y

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {F' : Type u} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [CompleteSpace F']

/-- The cumulative integral `Θ(s) = ∫_{-∞}^s θ`. -/
noncomputable def cumul (θ : ℝ → ℝ) (s : ℝ) : ℝ := ∫ t in Set.Iic s, θ t

/-- A smooth function supported in `(a, b)` with integral one. -/
structure IsBump (θ : ℝ → ℝ) (a b : ℝ) : Prop where
  contDiff : ContDiff ℝ (⊤ : ℕ∞) θ
  tsupport_subset : tsupport θ ⊆ Set.Ioo a b
  integral_eq_one : ∫ s, θ s = 1

theorem exists_isBump {a b : ℝ} (hab : a < b) : ∃ θ : ℝ → ℝ, IsBump θ a b := by
  let c : ContDiffBump ((a + b) / 2) := ⟨(b - a) / 8, (b - a) / 4, by linarith, by linarith⟩
  refine ⟨c.normed volume, c.contDiff_normed, ?_, c.integral_normed⟩
  rw [c.tsupport_normed_eq]
  intro x hx
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hx
  have : c.rOut = (b - a) / 4 := rfl
  rw [this] at hx
  constructor <;> linarith [hx.1, hx.2]

namespace IsBump

variable {θ : ℝ → ℝ} {a b : ℝ}

theorem hasCompactSupport (hθ : IsBump θ a b) : HasCompactSupport θ := by
  refine HasCompactSupport.intro (K := Set.Icc a b) isCompact_Icc ?_
  intro x hx
  by_contra h
  exact hx (Set.Ioo_subset_Icc_self (hθ.tsupport_subset (subset_tsupport _ h)))

theorem hasDerivAt_cumul (hθ : IsBump θ a b) (s : ℝ) : HasDerivAt (cumul θ) (θ s) s := by
  have hc : Continuous θ := hθ.contDiff.continuous
  have hi : Integrable θ := hc.integrable_of_hasCompactSupport hθ.hasCompactSupport
  have key : cumul θ = fun s => cumul θ 0 + ∫ t in (0:ℝ)..s, θ t := by
    funext s
    have := intervalIntegral.integral_Iic_sub_Iic (a := 0) (b := s) hi.integrableOn hi.integrableOn
    simp only [cumul]; linarith
  rw [key]
  exact ((hc.integral_hasStrictDerivAt 0 s).hasDerivAt).const_add _

theorem contDiff_cumul (hθ : IsBump θ a b) : ContDiff ℝ (⊤ : ℕ∞) (cumul θ) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun s => (hθ.hasDerivAt_cumul s).differentiableAt, ?_⟩
  have : deriv (cumul θ) = θ := funext fun s => (hθ.hasDerivAt_cumul s).deriv
  rw [this]; exact hθ.contDiff

theorem abs_cumul_le (hθ : IsBump θ a b) (s : ℝ) : |cumul θ s| ≤ ∫ t, |θ t| := by
  have hc : Continuous θ := hθ.contDiff.continuous
  have hi : Integrable θ := hc.integrable_of_hasCompactSupport hθ.hasCompactSupport
  calc |cumul θ s| = ‖∫ t in Set.Iic s, θ t‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ t in Set.Iic s, ‖θ t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t, ‖θ t‖ :=
        setIntegral_le_integral hi.norm (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    _ = ∫ t, |θ t| := by simp only [Real.norm_eq_abs]

end IsBump

/-- `Ω` is a slab in direction `e` over the interval `(a, b)`: on `Ω` the coordinate `⟪e, x⟫`
lies in `(a, b)`, and `Ω` is invariant under moving that coordinate within `(a, b)`. -/
structure IsSlab (Ω : Set E) (e : E) (a b : ℝ) : Prop where
  mem_Ioo : ∀ x ∈ Ω, ⟪e, x⟫ ∈ Set.Ioo a b
  shift_mem : ∀ x ∈ Ω, ∀ s ∈ Set.Ioo a b, x + (s - ⟪e, x⟫) • e ∈ Ω

/-- The compactly supported antiderivative of `-f` along `e` (up to the correction term
`θ • lineInt e f`). -/
noncomputable def lineG (e : E) (θ : ℝ → ℝ) (f : E → F) (x : E) : F :=
  cumul θ ⟪e, x⟫ • lineInt e f x - halfLineInt e f x

variable {e : E} {θ : ℝ → ℝ} {a b : ℝ} {f : E → F}

theorem lineG_comp_clm (he : ‖e‖ = 1) (hf : Continuous f) (hfc : HasCompactSupport f)
    (L : F →L[ℝ] F') (x : E) : lineG e θ (fun y => L (f y)) x = L (lineG e θ f x) := by
  rw [lineG, lineG, lineInt_comp_clm he hf hfc, halfLineInt_comp_clm he hf hfc, map_sub, map_smul]

theorem norm_lineG_le (hθ : IsBump θ a b) (he : ‖e‖ = 1) (hf : Continuous f)
    (hfc : HasCompactSupport f) (x : E) :
    ‖lineG e θ f x‖ ≤ ((∫ t, |θ t|) + 1) * ∫ τ : ℝ, ‖f (x + τ • e)‖ := by
  have h1 := norm_lineInt_le e f x
  have h2 := norm_halfLineInt_le he hf hfc x
  have h3 := hθ.abs_cumul_le ⟪e, x⟫
  have hA : 0 ≤ ∫ t, |θ t| := integral_nonneg fun _ => abs_nonneg _
  have h4 : |cumul θ ⟪e, x⟫| * ‖lineInt e f x‖ ≤ (∫ t, |θ t|) * ∫ τ : ℝ, ‖f (x + τ • e)‖ :=
    mul_le_mul h3 h1 (norm_nonneg _) hA
  calc ‖lineG e θ f x‖ ≤ ‖cumul θ ⟪e, x⟫ • lineInt e f x‖ + ‖halfLineInt e f x‖ :=
        norm_sub_le _ _
    _ ≤ _ := by
        rw [norm_smul, Real.norm_eq_abs, add_mul, one_mul]
        linarith

theorem hasFDerivAt_lineG (hθ : IsBump θ a b) (he : ‖e‖ = 1) (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) (x : E) :
    HasFDerivAt (lineG e θ f)
      ((θ ⟪e, x⟫ • innerSL ℝ e).smulRight (lineInt e f x) + lineG e θ (fderiv ℝ f) x) x := by
  have hΘ : HasFDerivAt (fun y => cumul θ ⟪e, y⟫) (θ ⟪e, x⟫ • innerSL ℝ e) x :=
    (hθ.hasDerivAt_cumul ⟪e, x⟫).comp_hasFDerivAt x (innerSL ℝ e).hasFDerivAt
  have hprod := hΘ.smul (hasFDerivAt_lineInt he hf hfc x)
  have := hprod.sub (hasFDerivAt_halfLineInt he hf hfc x)
  refine this.congr_fderiv ?_
  ext v
  simp only [lineG, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply]
  abel

theorem contDiff_lineG (hθ : IsBump θ a b) (he : ‖e‖ = 1) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfc : HasCompactSupport f) : ContDiff ℝ (⊤ : ℕ∞) (lineG e θ f) :=
  ((hθ.contDiff_cumul.comp (innerSL ℝ e).contDiff).smul (contDiff_lineInt he hf hfc)).sub
    (contDiff_halfLineInt he hf hfc)

theorem lineG_fderiv_apply_self (he : ‖e‖ = 1) (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) (x : E) : lineG e θ (fderiv ℝ f) x e = - f x := by
  have h1 := lineInt_fderiv_apply_self he hf hfc x
  have h2 := halfLineInt_fderiv_apply_self he hf hfc x
  rw [lineG, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, h1, h2]
  simp

lemma inner_add_smul_self (he : ‖e‖ = 1) (x : E) (τ : ℝ) : ⟪e, x + τ • e⟫ = ⟪e, x⟫ + τ := by
  rw [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, he]; simp

/-- The set of points of `Ω` obtained from `K` by moving the `e`-coordinate into `S`. -/
def shiftSet (e : E) (K : Set E) (S : Set ℝ) : Set E :=
  (fun p : E × ℝ => p.1 + (p.2 - ⟪e, p.1⟫) • e) '' (K ×ˢ S)

lemma isCompact_shiftSet (e : E) {K : Set E} (hK : IsCompact K) {S : Set ℝ} (hS : IsCompact S) :
    IsCompact (shiftSet e K S) :=
  (hK.prod hS).image (by fun_prop)

lemma shiftSet_subset {Ω : Set E} (hΩ : IsSlab Ω e a b) {K : Set E} (hKΩ : K ⊆ Ω) {S : Set ℝ}
    (hS : S ⊆ Set.Ioo a b) : shiftSet e K S ⊆ Ω := by
  rintro _ ⟨⟨y, s⟩, ⟨hy, hs⟩, rfl⟩
  exact hΩ.shift_mem y (hKΩ hy) s (hS hs)

lemma mem_shiftSet (he : ‖e‖ = 1) {K : Set E} {S : Set ℝ} {x : E} (τ : ℝ)
    (hy : x + τ • e ∈ K) (hx : ⟪e, x⟫ ∈ S) : x ∈ shiftSet e K S := by
  refine ⟨(x + τ • e, ⟪e, x⟫), ⟨hy, hx⟩, ?_⟩
  show (x + τ • e) + (⟪e, x⟫ - ⟪e, x + τ • e⟫) • e = x
  rw [inner_add_smul_self he]
  have : ⟪e, x⟫ - (⟪e, x⟫ + τ) = -τ := by ring
  rw [this, neg_smul]; abel

lemma compactSupport_of_support_subset {G : Type*} [Zero G] {g : E → G}
    {C : Set E} (hC : IsCompact C) (h : Function.support g ⊆ C) :
    HasCompactSupport g ∧ tsupport g ⊆ C := by
  have : tsupport g ⊆ C := closure_minimal h hC.isClosed
  exact ⟨hC.of_isClosed_subset (isClosed_tsupport _) this, this⟩

lemma exists_bounds {Ω : Set E} (hΩ : IsSlab Ω e a b) (hθ : IsBump θ a b) {K : Set E}
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ lo hi : ℝ, a < lo ∧ hi < b ∧ tsupport θ ⊆ Set.Icc lo hi ∧
      ∀ y ∈ K, ⟪e, y⟫ ∈ Set.Icc lo hi := by
  have hT : IsCompact (tsupport θ) := hθ.hasCompactSupport
  have hSc : IsCompact (tsupport θ ∪ (fun y => ⟪e, y⟫) '' K) :=
    hT.union (hK.image (by fun_prop))
  have hne : (tsupport θ ∪ (fun y => ⟪e, y⟫) '' K).Nonempty := by
    have : (tsupport θ).Nonempty := by
      by_contra hn
      rw [Set.not_nonempty_iff_eq_empty, tsupport_eq_empty_iff] at hn
      have := hθ.integral_eq_one
      simp [hn] at this
    exact this.mono Set.subset_union_left
  have hSsub : tsupport θ ∪ (fun y => ⟪e, y⟫) '' K ⊆ Set.Ioo a b := by
    rintro s (hs | ⟨y, hy, rfl⟩)
    · exact hθ.tsupport_subset hs
    · exact hΩ.mem_Ioo y (hKΩ hy)
  obtain ⟨lo, hlo, hlo'⟩ := hSc.exists_isLeast hne
  obtain ⟨hi, hhi, hhi'⟩ := hSc.exists_isGreatest hne
  exact ⟨lo, hi, (hSsub hlo).1, (hSsub hhi).2, fun s hs => ⟨hlo' (Or.inl hs), hhi' (Or.inl hs)⟩,
    fun y hy => ⟨hlo' (Or.inr ⟨y, hy, rfl⟩), hhi' (Or.inr ⟨y, hy, rfl⟩)⟩⟩

/-- `lineG e θ` preserves compact support inside a slab. -/
theorem hasCompactSupport_lineG {Ω : Set E} (hΩ : IsSlab Ω e a b) (hθ : IsBump θ a b)
    (he : ‖e‖ = 1) (hf : Continuous f) (hfc : HasCompactSupport f) (hfΩ : tsupport f ⊆ Ω) :
    HasCompactSupport (lineG e θ f) ∧ tsupport (lineG e θ f) ⊆ Ω := by
  have hK : IsCompact (tsupport f) := hfc
  obtain ⟨lo, hi, hlo, hhi, hT, hKb⟩ := exists_bounds hΩ hθ hK hfΩ
  have hIcc : Set.Icc lo hi ⊆ Set.Ioo a b := fun s hs => ⟨hlo.trans_le hs.1, hs.2.trans_lt hhi⟩
  have hfz : ∀ y, y ∉ tsupport f → f y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport hy
  have hsupp : Function.support (lineG e θ f) ⊆ shiftSet e (tsupport f) (Set.Icc lo hi) := by
    intro x hx
    have hx' : lineG e θ f x ≠ 0 := hx
    have hmem : ⟪e, x⟫ ∈ Set.Icc lo hi := by
      by_contra hn
      rcases not_and_or.mp hn with h | h
      · push_neg at h
        apply hx'
        have h1 : cumul θ ⟪e, x⟫ = 0 := by
          unfold cumul
          apply setIntegral_eq_zero_of_forall_eq_zero
          intro t ht
          apply image_eq_zero_of_notMem_tsupport
          intro htT
          have := (hT htT).1
          have : t ≤ ⟪e, x⟫ := ht
          linarith
        have h2 : halfLineInt e f x = 0 := by
          unfold halfLineInt
          apply setIntegral_eq_zero_of_forall_eq_zero
          intro τ hτ
          apply hfz
          intro hy
          have := (hKb _ hy).1
          rw [inner_add_smul_self he] at this
          have : τ ≤ 0 := hτ
          linarith
        simp [lineG, h1, h2]
      · push_neg at h
        apply hx'
        have h1 : cumul θ ⟪e, x⟫ = 1 := by
          unfold cumul
          rw [setIntegral_eq_integral_of_forall_compl_eq_zero, hθ.integral_eq_one]
          intro t ht
          apply image_eq_zero_of_notMem_tsupport
          intro htT
          have := (hT htT).2
          have : ¬ t ≤ ⟪e, x⟫ := ht
          linarith
        have h2 : halfLineInt e f x = lineInt e f x := by
          unfold halfLineInt lineInt
          apply setIntegral_eq_integral_of_forall_compl_eq_zero
          intro τ hτ
          apply hfz
          intro hy
          have := (hKb _ hy).2
          rw [inner_add_smul_self he] at this
          have : ¬ τ ≤ 0 := hτ
          linarith
        simp [lineG, h1, h2]
    have hex : ∃ τ : ℝ, x + τ • e ∈ tsupport f := by
      by_contra hn
      push_neg at hn
      apply hx'
      have hz : ∀ τ : ℝ, f (x + τ • e) = 0 := fun τ => hfz _ (hn τ)
      simp [lineG, lineInt, halfLineInt, hz]
    obtain ⟨τ, hτ⟩ := hex
    exact mem_shiftSet he τ hτ hmem
  obtain ⟨h1, h2⟩ := compactSupport_of_support_subset (isCompact_shiftSet e hK isCompact_Icc) hsupp
  exact ⟨h1, h2.trans (shiftSet_subset hΩ hfΩ hIcc)⟩

/-- `x ↦ θ(⟪e, x⟫) • lineInt e f x` is compactly supported inside a slab. -/
theorem hasCompactSupport_bump_smul_lineInt {Ω : Set E} (hΩ : IsSlab Ω e a b)
    (hθ : IsBump θ a b) (he : ‖e‖ = 1) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hfΩ : tsupport f ⊆ Ω) :
    HasCompactSupport (fun x => θ ⟪e, x⟫ • lineInt e f x) ∧
      tsupport (fun x => θ ⟪e, x⟫ • lineInt e f x) ⊆ Ω := by
  have hK : IsCompact (tsupport f) := hfc
  have hT : IsCompact (tsupport θ) := hθ.hasCompactSupport
  have hfz : ∀ y, y ∉ tsupport f → f y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport hy
  have hsupp : Function.support (fun x => θ ⟪e, x⟫ • lineInt e f x) ⊆
      shiftSet e (tsupport f) (tsupport θ) := by
    intro x hx
    have hx' : θ ⟪e, x⟫ • lineInt e f x ≠ 0 := hx
    have h1 : θ ⟪e, x⟫ ≠ 0 := left_ne_zero_of_smul hx'
    have h2 : lineInt e f x ≠ 0 := right_ne_zero_of_smul hx'
    have hmem : ⟪e, x⟫ ∈ tsupport θ := subset_tsupport _ h1
    have hex : ∃ τ : ℝ, x + τ • e ∈ tsupport f := by
      by_contra hn
      push_neg at hn
      apply h2
      have hz : ∀ τ : ℝ, f (x + τ • e) = 0 := fun τ => hfz _ (hn τ)
      simp [lineInt, hz]
    obtain ⟨τ, hτ⟩ := hex
    exact mem_shiftSet he τ hτ hmem
  obtain ⟨h1, h2⟩ := compactSupport_of_support_subset (isCompact_shiftSet e hK hT) hsupp
  exact ⟨h1, h2.trans (shiftSet_subset hΩ hfΩ hθ.tsupport_subset)⟩

end FEEC
