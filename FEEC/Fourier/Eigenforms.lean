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
    simp only [integral_trig1_mul (hab _)]
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

theorem inner_synth (hab : ∀ i, a i < b i) (w : L2Form (box e a b) k) (m : Fin n → ℕ) (α : Covector E k) :
    ⟪w, synth e a b m α⟫ = normProd a b m * ⟪coef e a b w m, α⟫ := by
  sorry

theorem inner_synth_synth (hab : ∀ i, a i < b i) (m m' : Fin n → ℕ) (α β : Covector E k) :
    ⟪synth e a b m α, synth e a b m' β⟫ =
      if m = m' then normProd a b m * ⟪allow e m α, β⟫ else 0 := by
  sorry

theorem allow_coef (hab : ∀ i, a i < b i) (w : L2Form (box e a b) k) (m : Fin n → ℕ) :
    allow e m (coef e a b w m) = coef e a b w m := by
  sorry

theorem coef_synth (hab : ∀ i, a i < b i) (m m' : Fin n → ℕ) (α : Covector E k) :
    coef e a b (synth e a b m α) m' = if m = m' then allow e m α else 0 := by
  sorry

/-- `ξ ∧ ·` and `ξ ⌟ ·` are adjoint. -/
theorem inner_cwedge (v : E) (α : Covector E k) (β : Covector E (k + 1)) :
    ⟪cwedge v α, β⟫ = ⟪α, ccontr v β⟫ := by
  sorry

/-- `v ⌟ (v ∧ α) + v ∧ (v ⌟ α) = |v|² α`. -/
theorem ccontr_cwedge_add (v : E) (α : Covector E (k + 1)) :
    ccontr v (cwedge v α) + cwedge v (ccontr v α) = (‖v‖ ^ 2) • α := by
  sorry

theorem norm_cwedge_le (v : E) (α : Covector E k) : ‖cwedge v α‖ ≤ ‖v‖ * ‖α‖ := by
  sorry

theorem norm_ccontr_le (v : E) (α : Covector E (k + 1)) : ‖ccontr v α‖ ≤ ‖v‖ * ‖α‖ := by
  sorry

/-- Nonzero frequency vectors are bounded below. -/
theorem exists_norm_xi_ge (hab : ∀ i, a i < b i) :
    ∃ c > 0, ∀ m : Fin n → ℕ, m ≠ 0 → c ≤ ‖xi e a b m‖ := by
  sorry

/-- In positive degree, a coefficient can only be nonzero at a nonzero frequency. -/
theorem coef_zero_freq (hab : ∀ i, a i < b i) (w : L2Form (box e a b) (k + 1)) :
    coef e a b w 0 = 0 := by
  sorry

end Fourier

end FEEC
