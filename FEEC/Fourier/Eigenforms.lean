/-
Eigenforms of the Hodge Laplacian on a box and Fourier coefficients.
-/
import FEEC.Fourier.TrigDensity
import FEEC.Tensor.Forms

/-!
# Eigenforms on a box and Fourier coefficients of `L²` forms

For a tuple `T : Fin k → Fin n` and frequencies `m : Fin n → ℕ`,
`eigForm e a b T m = trigProd e a b (pat T) m • dx_T`: sine in the directions of `T`,
cosine in the others (the natural boundary conditions).

For a covector `α`, `synth m α = (k!)⁻¹ ∑_T ⟪α, dx_T⟫ eigLp T m`, and for an `L²` form `w`,
`coef w m = (k!)⁻¹ ∑_T (⟪w, eigLp T m⟫ / normProd m) dx_T`, so that
`⟪w, synth m α⟫ = normProd m * ⟪coef w m, α⟫` (`inner_synth`).
Frequencies with `mᵢ = 0` kill the components involving `eᵢ` (`allow`).
`xi m = -∑ᵢ (π mᵢ / ℓᵢ) eᵢ` is the frequency vector: `d` acts as `xi m ∧ ·`.
-/

namespace FEEC

namespace Fourier

open MeasureTheory Tensor

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {n : ℕ}
  (e : OrthonormalBasis (Fin n) ℝ E) (a b : Fin n → ℝ) {k : ℕ}

/-- The eigenform with tuple `T` and frequencies `m`. -/
noncomputable def eigForm (T : Fin k → Fin n) (m : Fin n → ℕ) : E → E [⋀^Fin k]→L[ℝ] ℝ :=
  fun x => trigProd e a b (pat T) m x • dxT e k T

/-- `∏ᵢ ‖cos(π mᵢ ·)‖²`. -/
noncomputable def normProd (m : Fin n → ℕ) : ℝ := ∏ i, trigNormSq (a i) (b i) (m i)

/-- The frequency vector `-∑ᵢ (π mᵢ / ℓᵢ) eᵢ`. -/
noncomputable def xi (m : Fin n → ℕ) : E := -∑ i, freq (a i) (b i) (m i) • e i

/-- Exterior multiplication by a vector, on covectors. -/
noncomputable def cwedge (v : E) (α : Covector E k) : Covector E (k + 1) :=
  Covector.ofAlt (wedgeLeft v α.toAlt)

/-- Contraction with a vector, on covectors. -/
noncomputable def ccontr (v : E) (α : Covector E (k + 1)) : Covector E k :=
  Covector.ofAlt (α.toAlt.curryLeft v)

/-- The part of a covector allowed by the frequencies `m`. -/
noncomputable def allow (m : Fin n → ℕ) (α : Covector E k) : Covector E k :=
  ((k.factorial : ℝ))⁻¹ • ∑ T : Fin k → Fin n,
    (if ∀ p, m (T p) ≠ 0 then ⟪α, Covector.ofAlt (dxT e k T)⟫ else 0) •
      Covector.ofAlt (dxT e k T)

variable {e a b}

theorem contDiff_eigForm (T : Fin k → Fin n) (m : Fin n → ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (eigForm e a b T m) := by
  have h : ContDiff ℝ (⊤ : ℕ∞) (trigProd e a b (pat T) m) := by
    unfold trigProd
    refine contDiff_prod fun i _ => ?_
    have : ContDiff ℝ (⊤ : ℕ∞) (trig1 (pat T i) (a i) (b i) (m i)) := by
      unfold trig1; split_ifs
      exacts [contDiff_trigS _, contDiff_trigC _]
    exact this.comp ((innerSL ℝ (e i)).contDiff)
  exact h.smul contDiff_const

theorem memLp_eigForm (T : Fin k → Fin n) (m : Fin n → ℕ) :
    MemLp (fun x => Covector.ofAlt (eigForm e a b T m x)) 2 (volume.restrict (box e a b)) := by
  haveI : IsFiniteMeasure (volume.restrict (box e a b)) :=
    ⟨by simpa using volume_box_lt_top e a b⟩
  refine MemLp.of_bound ?_ ‖Covector.ofAlt (dxT e k T)‖ ?_
  · exact Covector.ofAlt.continuous.comp_aestronglyMeasurable
      ((continuous_trigProd e a b (pat T) m).aestronglyMeasurable.smul_const _)
  · refine Filter.Eventually.of_forall fun x => ?_
    simp only [eigForm, map_smul, norm_smul, Real.norm_eq_abs]
    calc _ ≤ 1 * ‖Covector.ofAlt (dxT e k T)‖ := by
          gcongr; exact abs_trigProd_le e a b _ m x
      _ = _ := one_mul _

variable (e a b) in
/-- The class of an eigenform in `L²Λᵏ`. -/
noncomputable def eigLp (T : Fin k → Fin n) (m : Fin n → ℕ) : L2Form (box e a b) k :=
  (memLp_eigForm (e := e) (a := a) (b := b) T m).toLp _

variable (e a b) in
/-- The `L²` form with frequency `m` and covector coefficient `α`. -/
noncomputable def synth (m : Fin n → ℕ) (α : Covector E k) : L2Form (box e a b) k :=
  ((k.factorial : ℝ))⁻¹ • ∑ T : Fin k → Fin n, ⟪α, Covector.ofAlt (dxT e k T)⟫ • eigLp e a b T m

variable (e a b) in
/-- The Fourier coefficient of frequency `m`. -/
noncomputable def coef (w : L2Form (box e a b) k) (m : Fin n → ℕ) : Covector E k :=
  ((k.factorial : ℝ))⁻¹ • ∑ T : Fin k → Fin n,
    (⟪w, eigLp e a b T m⟫ / normProd a b m) • Covector.ofAlt (dxT e k T)

theorem coeFn_eigLp (T : Fin k → Fin n) (m : Fin n → ℕ) :
    eigLp e a b T m =ᵐ[volume.restrict (box e a b)]
      fun x => Covector.ofAlt (eigForm e a b T m x) :=
  MemLp.coeFn_toLp _

theorem normProd_pos (hab : ∀ i, a i < b i) (m : Fin n → ℕ) : 0 < normProd a b m :=
  Finset.prod_pos fun i _ => trigNormSq_pos (hab i) _

theorem integral_trig1_mul {a' b' : ℝ} (hab : a' < b') (s : Bool) (m m' : ℕ) :
    ∫ t in Set.Ioo a' b', trig1 s a' b' m t * trig1 s a' b' m' t =
      if m = m' ∧ (s = true → m ≠ 0) then trigNormSq a' b' m else 0 := by
  cases s
  · simp only [trig1, Bool.false_eq_true, if_false, false_imp_iff, and_true]
    exact integral_trigC_mul_trigC hab m m'
  · simp only [trig1, if_true, true_imp_iff]
    exact integral_trigS_mul_trigS hab m m'

theorem pat_eq_true_iff' (T : Fin k → Fin n) (i : Fin n) : pat T i = true ↔ ∃ p, T p = i := by
  simp [pat]

theorem pat_eq_of_inner_ne_zero_aux {S T : Fin k → Fin n}
    (h : ⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k T)⟫ ≠ 0) : pat S = pat T := by
  have hr : Set.range S = Set.range T := by
    by_contra hne
    exact h (inner_dxT_eq_zero_of_range_ne e hne)
  funext i
  rw [Bool.eq_iff_iff, pat_eq_true_iff', pat_eq_true_iff', ← Set.mem_range, ← Set.mem_range, hr]

/-- Pairing of eigenforms. -/
theorem inner_eigLp (hab : ∀ i, a i < b i) (S T : Fin k → Fin n) (m m' : Fin n → ℕ) :
    ⟪eigLp e a b S m, eigLp e a b T m'⟫ =
      if m = m' ∧ (∀ p, m (S p) ≠ 0) then
        ⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k T)⟫ * normProd a b m
      else 0 := by
  rw [L2.inner_def]
  have h1 : ∀ᵐ x ∂(volume.restrict (box e a b)),
      ⟪(eigLp e a b S m : L2Form (box e a b) k) x, (eigLp e a b T m' : L2Form (box e a b) k) x⟫ =
        (∏ i, (trig1 (pat S i) (a i) (b i) (m i) ⟪e i, x⟫ *
            trig1 (pat T i) (a i) (b i) (m' i) ⟪e i, x⟫)) *
          ⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k T)⟫ := by
    filter_upwards [coeFn_eigLp (e := e) (a := a) (b := b) S m,
      coeFn_eigLp (e := e) (a := a) (b := b) T m'] with x h2 h3
    rw [h2, h3]
    simp only [eigForm, map_smul, real_inner_smul_left, real_inner_smul_right,
      Finset.prod_mul_distrib]
    unfold trigProd
    ring
  rw [integral_congr_ae h1, integral_mul_const,
    integral_box_prod e a b (fun i t => trig1 (pat S i) (a i) (b i) (m i) t *
      trig1 (pat T i) (a i) (b i) (m' i) t), mul_comm]
  by_cases h : ⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k T)⟫ = 0
  · simp [h]
  · have hp : pat S = pat T := pat_eq_of_inner_ne_zero_aux (e := e) h
    simp only [hp, integral_trig1_mul (hab _)]
    rw [Finset.prod_ite_zero]
    by_cases hc : m = m' ∧ (∀ p, m (S p) ≠ 0)
    · have : ∀ i ∈ Finset.univ, (m i = m' i ∧ (pat T i = true → m i ≠ 0)) := by
        intro i _
        refine ⟨congrFun hc.1 i, fun hi => ?_⟩
        rw [← hp, pat_eq_true_iff'] at hi
        obtain ⟨p, rfl⟩ := hi
        exact hc.2 p
      rw [if_pos this, if_pos hc]
      obtain ⟨rfl, _⟩ := hc
      rfl
    · rw [if_neg hc, if_neg]
      · simp
      · intro hall
        apply hc
        refine ⟨funext fun i => (hall i (Finset.mem_univ i)).1, fun p => ?_⟩
        have := (hall (S p) (Finset.mem_univ _)).2
        rw [← hp, pat_eq_true_iff'] at this
        exact this ⟨p, rfl⟩

theorem sum_inner_inner_dxT (β : Covector E k) (S : Fin k → Fin n) :
    ∑ T : Fin k → Fin n, ⟪β, Covector.ofAlt (dxT e k T)⟫ *
      ⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k T)⟫ =
        (k.factorial : ℝ) * ⟪β, Covector.ofAlt (dxT e k S)⟫ := by
  have h := sum_inner_dxT_smul e β.toAlt
  simp only [Covector.ofAlt_toAlt] at h
  have h2 := congrArg (fun x => ⟪Covector.ofAlt x, Covector.ofAlt (dxT e k S)⟫) h
  simp only [map_smul, map_sum, real_inner_smul_left, sum_inner, Covector.ofAlt_toAlt] at h2
  have hk : (k.factorial : ℝ) ≠ 0 := by positivity
  rw [← h2, ← mul_assoc, mul_inv_cancel₀ hk, one_mul]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [real_inner_comm (Covector.ofAlt (dxT e k S))]

theorem inner_synth (hab : ∀ i, a i < b i) (w : L2Form (box e a b) k) (m : Fin n → ℕ)
    (α : Covector E k) :
    ⟪w, synth e a b m α⟫ = normProd a b m * ⟪coef e a b w m, α⟫ := by
  have hN := (normProd_pos hab m).ne'
  unfold synth coef
  simp only [inner_smul_right, inner_sum, inner_smul_left, sum_inner, RCLike.conj_to_real]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [real_inner_comm α]
  field_simp

theorem inner_synth_synth (hab : ∀ i, a i < b i) (m m' : Fin n → ℕ) (α β : Covector E k) :
    ⟪synth e a b m α, synth e a b m' β⟫ =
      if m = m' then normProd a b m * ⟪allow e m α, β⟫ else 0 := by
  have hk : (k.factorial : ℝ) ≠ 0 := by positivity
  unfold synth allow
  simp only [inner_smul_right, inner_smul_left, inner_sum, sum_inner, RCLike.conj_to_real,
    inner_eigLp hab]
  by_cases h : m = m'
  · subst h
    simp only [if_true]
    have key : ∀ S : Fin k → Fin n, ∑ T : Fin k → Fin n, ⟪β, Covector.ofAlt (dxT e k T)⟫ *
        (if (∀ p, m (S p) ≠ 0) then ⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k T)⟫ *
          normProd a b m else 0) =
        if (∀ p, m (S p) ≠ 0) then normProd a b m * ((k.factorial : ℝ) *
          ⟪β, Covector.ofAlt (dxT e k S)⟫) else 0 := by
      intro S
      split_ifs
      · rw [← sum_inner_inner_dxT (e := e) β S, Finset.mul_sum]
        refine Finset.sum_congr rfl fun T _ => ?_
        ring
      · simp
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun S _ => ?_
    by_cases hS : ∀ p, m (S p) ≠ 0
    · have hk' := key S
      simp only [hS, if_true, ne_eq, not_false_eq_true, true_and, implies_true] at hk' ⊢
      have e1 : ∑ x : Fin k → Fin n, (k.factorial : ℝ)⁻¹ * (⟪β, Covector.ofAlt (dxT e k x)⟫ *
          ((k.factorial : ℝ)⁻¹ * (⟪α, Covector.ofAlt (dxT e k S)⟫ *
            (⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k x)⟫ * normProd a b m)))) =
          (k.factorial : ℝ)⁻¹ * (k.factorial : ℝ)⁻¹ * ⟪α, Covector.ofAlt (dxT e k S)⟫ *
            ∑ x : Fin k → Fin n, ⟪β, Covector.ofAlt (dxT e k x)⟫ *
              (⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k x)⟫ * normProd a b m) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        ring
      rw [e1, hk', real_inner_comm β]
      field_simp
    · simp [hS]
  · simp [h]

variable (e) in
/-- `allow` as a linear map. -/
noncomputable def allowL (m : Fin n → ℕ) : Covector E k →ₗ[ℝ] Covector E k where
  toFun := allow e m
  map_add' α β := by
    unfold allow
    rw [← smul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun T _ => ?_
    split_ifs
    · rw [inner_add_left, add_smul]
    · simp
  map_smul' c α := by
    show allow e m (c • α) = c • allow e m α
    unfold allow
    rw [smul_comm c]
    congr 1
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    split_ifs
    · rw [real_inner_smul_left, smul_smul]
    · simp

theorem allowL_apply (m : Fin n → ℕ) (α : Covector E k) : allowL e m α = allow e m α := rfl

theorem eigLp_eq_zero_of_zero {T : Fin k → Fin n} {m : Fin n → ℕ} {p : Fin k}
    (h : m (T p) = 0) : eigLp e a b T m = 0 := by
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [coeFn_eigLp (e := e) (a := a) (b := b) T m] with x hx
  rw [hx]
  have : trigProd e a b (pat T) m x = 0 := by
    unfold trigProd
    refine Finset.prod_eq_zero (Finset.mem_univ (T p)) ?_
    have : pat T (T p) = true := (pat_eq_true_iff' T _).2 ⟨p, rfl⟩
    simp [trig1, this, h, trigS_zero]
  simp [eigForm, this]

theorem allow_dxT {m : Fin n → ℕ} {T₀ : Fin k → Fin n} (h : ∀ p, m (T₀ p) ≠ 0) :
    allow e m (Covector.ofAlt (dxT e k T₀)) = Covector.ofAlt (dxT e k T₀) := by
  have key := congrArg Covector.ofAlt (sum_inner_dxT_smul e (dxT e k T₀))
  simp only [map_smul, map_sum] at key
  refine Eq.trans ?_ key
  unfold allow
  congr 1
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases hS : ⟪Covector.ofAlt (dxT e k T₀), Covector.ofAlt (dxT e k S)⟫ = 0
  · simp [hS]
  · have hr : Set.range T₀ = Set.range S := by
      by_contra hne
      exact hS (inner_dxT_eq_zero_of_range_ne e hne)
    have : ∀ p, m (S p) ≠ 0 := by
      intro p
      have : S p ∈ Set.range T₀ := hr ▸ ⟨p, rfl⟩
      obtain ⟨q, hq⟩ := this
      rw [← hq]; exact h q
    rw [if_pos this]

theorem allow_coef (hab : ∀ i, a i < b i) (w : L2Form (box e a b) k) (m : Fin n → ℕ) :
    allow e m (coef e a b w m) = coef e a b w m := by
  rw [← allowL_apply]
  unfold coef
  rw [map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [map_smul, allowL_apply]
  by_cases hT : ∀ p, m (T p) ≠ 0
  · rw [allow_dxT hT]
  · push Not at hT
    obtain ⟨p, hp⟩ := hT
    rw [eigLp_eq_zero_of_zero (e := e) (a := a) (b := b) hp]
    simp

theorem coef_synth (hab : ∀ i, a i < b i) (m m' : Fin n → ℕ) (α : Covector E k) :
    coef e a b (synth e a b m α) m' = if m = m' then allow e m α else 0 := by
  refine ext_inner_right ℝ fun β => ?_
  have h1 := inner_synth hab (synth e a b m α) m' β
  rw [inner_synth_synth hab] at h1
  have hN := (normProd_pos (a := a) (b := b) hab m').ne'
  by_cases h : m = m'
  · subst h
    simp only [if_true] at h1 ⊢
    exact (mul_left_cancel₀ hN h1).symm
  · simp only [h, if_false] at h1 ⊢
    rw [inner_zero_left]
    rcases mul_eq_zero.1 h1.symm with h2 | h2
    · exact absurd h2 hN
    · exact h2

/-- `ξ ∧ ·` and `ξ ⌟ ·` are adjoint. -/
theorem inner_cwedge (v : E) (α : Covector E k) (β : Covector E (k + 1)) :
    ⟪cwedge v α, β⟫ = ⟪α, ccontr v β⟫ := by
  have := inner_wedgeLeft v α.toAlt β.toAlt
  simpa [cwedge, ccontr] using this

/-- `v ⌟ (v ∧ α) + v ∧ (v ⌟ α) = |v|² α`. -/
theorem ccontr_cwedge_add (v : E) (α : Covector E (k + 1)) :
    ccontr v (cwedge v α) + cwedge v (ccontr v α) = (‖v‖ ^ 2) • α := by
  unfold ccontr cwedge
  rw [Covector.toAlt_ofAlt, curryLeft_wedgeLeft, Covector.toAlt_ofAlt, ← map_add]
  have : ‖v‖ ^ 2 = ⟪v, v⟫ := (real_inner_self_eq_norm_sq v).symm
  rw [this, sub_add_cancel]
  conv_rhs => rw [← Covector.ofAlt_toAlt α]
  rw [map_smul]

theorem norm_sq_cwedge_add (v : E) (α : Covector E (k + 1)) :
    ‖cwedge v α‖ ^ 2 + ‖ccontr v α‖ ^ 2 = ‖v‖ ^ 2 * ‖α‖ ^ 2 := by
  have h := congrArg (fun x => ⟪α, x⟫) (ccontr_cwedge_add v α)
  simp only [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq] at h
  have h2 : ⟪α, cwedge v (ccontr v α)⟫ = ⟪ccontr v α, ccontr v α⟫ := by
    rw [real_inner_comm (cwedge v (ccontr v α)) α, inner_cwedge]
  have h1 : ⟪α, ccontr v (cwedge v α)⟫ = ‖cwedge v α‖ ^ 2 := by
    rw [← inner_cwedge, real_inner_self_eq_norm_sq]
  rw [h1, h2, real_inner_self_eq_norm_sq] at h
  exact h

theorem norm_cwedge_le (v : E) (α : Covector E k) : ‖cwedge v α‖ ≤ ‖v‖ * ‖α‖ := by
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero, mul_pow]
  cases k with
  | zero =>
    have h1 : ‖cwedge v α‖ ^ 2 = ⟪α, ccontr v (cwedge v α)⟫ := by
      rw [← real_inner_self_eq_norm_sq, inner_cwedge]
    have h2 : ccontr v (cwedge v α) = (‖v‖ ^ 2) • α := by
      unfold ccontr cwedge
      rw [Covector.toAlt_ofAlt, curryLeft_wedgeLeft_zero, real_inner_self_eq_norm_sq]
      conv_rhs => rw [← Covector.ofAlt_toAlt α]
      rw [map_smul]
    rw [h1, h2, real_inner_smul_right, real_inner_self_eq_norm_sq]
  | succ k =>
    have := norm_sq_cwedge_add v α
    nlinarith [sq_nonneg ‖ccontr v α‖]

theorem norm_ccontr_le (v : E) (α : Covector E (k + 1)) : ‖ccontr v α‖ ≤ ‖v‖ * ‖α‖ := by
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero, mul_pow]
  have := norm_sq_cwedge_add v α
  nlinarith [sq_nonneg ‖cwedge v α‖]

/-- Nonzero frequency vectors are bounded below. -/
theorem exists_norm_xi_ge (hab : ∀ i, a i < b i) :
    ∃ c > 0, ∀ m : Fin n → ℕ, m ≠ 0 → c ≤ ‖xi e a b m‖ := by
  have hs : 0 ≤ ∑ i, (b i - a i) := Finset.sum_nonneg fun i _ => (sub_pos.2 (hab i)).le
  refine ⟨Real.pi / (1 + ∑ i, (b i - a i)), by positivity, ?_⟩
  intro m hm
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
    by_contra h
    push Not at h
    exact hm (funext h)
  have h1 : |⟪e i, xi e a b m⟫| ≤ ‖xi e a b m‖ := by
    calc _ ≤ ‖e i‖ * ‖xi e a b m‖ := abs_real_inner_le_norm _ _
      _ = _ := by rw [e.orthonormal.1 i, one_mul]
  have h2 : ⟪e i, xi e a b m⟫ = -freq (a i) (b i) (m i) := by
    unfold xi
    rw [inner_neg_right, inner_sum, Finset.sum_eq_single i]
    · rw [inner_smul_right, real_inner_self_eq_norm_sq, e.orthonormal.1 i]; simp
    · intro j _ hj
      rw [inner_smul_right, e.orthonormal.inner_eq_zero (Ne.symm hj), mul_zero]
    · simp
  have hba := sub_pos.2 (hab i)
  have hm1 : (1 : ℝ) ≤ m i := by exact_mod_cast Nat.pos_of_ne_zero hi
  have h3 : 0 ≤ freq (a i) (b i) (m i) := by unfold freq; positivity
  have h4 : Real.pi / (b i - a i) ≤ freq (a i) (b i) (m i) := by
    unfold freq
    exact div_le_div_of_nonneg_right (by nlinarith [Real.pi_pos]) hba.le
  have h5 : b i - a i ≤ 1 + ∑ i, (b i - a i) := by
    have := Finset.single_le_sum (f := fun i => b i - a i) (fun i _ => (sub_pos.2 (hab i)).le)
      (Finset.mem_univ i)
    linarith
  have h6 : Real.pi / (1 + ∑ i, (b i - a i)) ≤ Real.pi / (b i - a i) :=
    div_le_div_of_nonneg_left Real.pi_pos.le hba h5
  rw [h2, abs_neg, abs_of_nonneg h3] at h1
  linarith

/-- In positive degree, a coefficient can only be nonzero at a nonzero frequency. -/
theorem coef_zero_freq (hab : ∀ i, a i < b i) (w : L2Form (box e a b) (k + 1)) :
    coef e a b w 0 = 0 := by
  unfold coef
  have : ∀ T : Fin (k + 1) → Fin n, eigLp e a b T 0 = 0 := fun T =>
    eigLp_eq_zero_of_zero (e := e) (a := a) (b := b) (p := 0) rfl
  simp [this]

end Fourier

end FEEC
