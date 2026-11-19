/-
The Fourier H¹-seminorm of a test form.
-/
import FEEC.Fourier.Regularity

namespace FEEC

namespace Fourier

open MeasureTheory Tensor

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {n : ℕ}
  {e : OrthonormalBasis (Fin n) ℝ E} {a b : Fin n → ℝ} {k : ℕ}

/-! ### A general Bessel inequality for toggled trigonometric families -/

section toggled

variable (e a b) in
/-- The pattern `s` has no sine in a direction of frequency `0`. -/
def trigCond (s : Fin n → Bool) (m : Fin n → ℕ) : Prop := ∀ j, s j = true → m j ≠ 0

theorem memLp_tForm (s : Fin n → Bool) (T : Fin k → Fin n) (m : Fin n → ℕ) :
    MemLp (fun x => Covector.ofAlt (trigProd e a b s m x • dxT e k T)) 2
      (volume.restrict (box e a b)) := by
  haveI : IsFiniteMeasure (volume.restrict (box e a b)) :=
    ⟨by simpa using volume_box_lt_top e a b⟩
  refine MemLp.of_bound ?_ ‖Covector.ofAlt (dxT e k T)‖ ?_
  · exact Covector.ofAlt.continuous.comp_aestronglyMeasurable
      ((continuous_trigProd e a b s m).aestronglyMeasurable.smul_const _)
  · refine Filter.Eventually.of_forall fun x => ?_
    simp only [map_smul, norm_smul, Real.norm_eq_abs]
    calc _ ≤ 1 * ‖Covector.ofAlt (dxT e k T)‖ := by
          gcongr; exact abs_trigProd_le e a b _ m x
      _ = _ := one_mul _

variable (e a b) in
/-- The class of `trigProd s m • dx_T`. -/
noncomputable def tLp (s : Fin n → Bool) (T : Fin k → Fin n) (m : Fin n → ℕ) :
    L2Form (box e a b) k :=
  (memLp_tForm (e := e) (a := a) (b := b) s T m).toLp _

theorem coeFn_tLp (s : Fin n → Bool) (T : Fin k → Fin n) (m : Fin n → ℕ) :
    tLp e a b s T m =ᵐ[volume.restrict (box e a b)]
      fun x => Covector.ofAlt (trigProd e a b s m x • dxT e k T) :=
  MemLp.coeFn_toLp _

theorem tLp_eq_zero {s : Fin n → Bool} {m : Fin n → ℕ} (T : Fin k → Fin n)
    (h : ¬ trigCond s m) : tLp e a b s T m = 0 := by
  unfold trigCond at h
  push Not at h
  obtain ⟨j, hj, hm⟩ := h
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [coeFn_tLp (e := e) (a := a) (b := b) s T m] with x hx
  rw [hx]
  have : trigProd e a b s m x = 0 := by
    unfold trigProd
    refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
    simp [trig1, hj, hm, trigS_zero]
  simp [this]

theorem inner_tLp (s s' : Fin n → Bool) (S T : Fin k → Fin n) (m m' : Fin n → ℕ) :
    ⟪tLp e a b s S m, tLp e a b s' T m'⟫ =
      ⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k T)⟫ *
        ∫ x in box e a b, trigProd e a b s m x * trigProd e a b s' m' x := by
  rw [L2.inner_def]
  have h1 : ∀ᵐ x ∂(volume.restrict (box e a b)),
      ⟪(tLp e a b s S m : L2Form (box e a b) k) x, (tLp e a b s' T m' : L2Form (box e a b) k) x⟫ =
        (trigProd e a b s m x * trigProd e a b s' m' x) *
          ⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k T)⟫ := by
    filter_upwards [coeFn_tLp (e := e) (a := a) (b := b) s S m,
      coeFn_tLp (e := e) (a := a) (b := b) s' T m'] with x h2 h3
    rw [h2, h3]
    simp only [map_smul, real_inner_smul_left, real_inner_smul_right]
    ring
  rw [integral_congr_ae h1, integral_mul_const, mul_comm]

open Classical in
theorem integral_trigProd_mul (hab : ∀ i, a i < b i) (s : Fin n → Bool) (m m' : Fin n → ℕ) :
    ∫ x in box e a b, trigProd e a b s m x * trigProd e a b s m' x =
      if m = m' ∧ trigCond s m then normProd a b m else 0 := by
  have h := integral_box_prod e a b
    (fun i t => trig1 (s i) (a i) (b i) (m i) t * trig1 (s i) (a i) (b i) (m' i) t)
  simp only [trigProd, ← Finset.prod_mul_distrib]
  rw [h]
  simp only [integral_trig1_mul (hab _)]
  rw [Finset.prod_ite_zero]
  by_cases hc : m = m' ∧ trigCond s m
  · have : ∀ i ∈ Finset.univ, (m i = m' i ∧ (s i = true → m i ≠ 0)) := fun i _ =>
      ⟨congrFun hc.1 i, hc.2 i⟩
    rw [if_pos this, if_pos hc]
    obtain ⟨rfl, _⟩ := hc
    rfl
  · rw [if_neg hc, if_neg]
    intro hh
    exact hc ⟨funext fun i => (hh i (Finset.mem_univ i)).1,
      fun j hj => (hh j (Finset.mem_univ j)).2 hj⟩

variable (p : (Fin k → Fin n) → (Fin n → Bool))

open Classical in
theorem inner_tLp_p (hab : ∀ i, a i < b i)
    (hp : ∀ S T, ⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k T)⟫ ≠ 0 → p S = p T)
    (S T : Fin k → Fin n) (m m' : Fin n → ℕ) :
    ⟪tLp e a b (p S) S m, tLp e a b (p T) T m'⟫ =
      if m = m' ∧ trigCond (p S) m then
        ⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k T)⟫ * normProd a b m else 0 := by
  rw [inner_tLp]
  by_cases hc : ⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k T)⟫ = 0
  · simp [hc]
  · rw [← hp S T hc, integral_trigProd_mul hab]
    split_ifs <;> simp

variable (e a b) in
/-- The coefficient of `w` against the family `trigProd (p T) m • dx_T`. -/
noncomputable def dCoef (w : L2Form (box e a b) k) (m : Fin n → ℕ) : Covector E k :=
  ((k.factorial : ℝ))⁻¹ • ∑ T : Fin k → Fin n,
    (⟪w, tLp e a b (p T) T m⟫ / normProd a b m) • Covector.ofAlt (dxT e k T)

variable (e a b) in
noncomputable def tSynth (m : Fin n → ℕ) (α : Covector E k) : L2Form (box e a b) k :=
  ((k.factorial : ℝ))⁻¹ • ∑ T : Fin k → Fin n,
    ⟪α, Covector.ofAlt (dxT e k T)⟫ • tLp e a b (p T) T m

theorem inner_tSynth (hab : ∀ i, a i < b i) (w : L2Form (box e a b) k) (m : Fin n → ℕ)
    (α : Covector E k) :
    ⟪w, tSynth e a b p m α⟫ = normProd a b m * ⟪dCoef e a b p w m, α⟫ := by
  have hN := (normProd_pos hab m).ne'
  unfold tSynth dCoef
  simp only [inner_smul_right, inner_sum, inner_smul_left, sum_inner, RCLike.conj_to_real]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [real_inner_comm α]
  field_simp

theorem inner_dCoef_eq_zero (hp : ∀ S T, ⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k T)⟫ ≠ 0 → p S = p T)
    (w : L2Form (box e a b) k) (m : Fin n → ℕ) (S : Fin k → Fin n)
    (hS : ¬ trigCond (p S) m) :
    ⟪dCoef e a b p w m, Covector.ofAlt (dxT e k S)⟫ = 0 := by
  unfold dCoef
  simp only [inner_smul_left, sum_inner, RCLike.conj_to_real]
  rw [Finset.sum_eq_zero, mul_zero]
  intro T _
  by_cases hc : ⟪Covector.ofAlt (dxT e k T), Covector.ofAlt (dxT e k S)⟫ = 0
  · rw [hc, mul_zero]
  · have : p T = p S := hp T S hc
    rw [this, tLp_eq_zero (e := e) (a := a) (b := b) T hS]
    simp

theorem expand_cov (α : Covector E k) :
    α = ((k.factorial : ℝ))⁻¹ • ∑ T : Fin k → Fin n,
      ⟪α, Covector.ofAlt (dxT e k T)⟫ • Covector.ofAlt (dxT e k T) := by
  have h := congrArg Covector.ofAlt (sum_inner_dxT_smul e α.toAlt)
  simp only [map_smul, map_sum, Covector.ofAlt_toAlt] at h
  exact h.symm

theorem norm_sq_cov (α : Covector E k) :
    ‖α‖ ^ 2 = ((k.factorial : ℝ))⁻¹ * ∑ T : Fin k → Fin n,
      ⟪α, Covector.ofAlt (dxT e k T)⟫ * ⟪α, Covector.ofAlt (dxT e k T)⟫ := by
  calc ‖α‖ ^ 2 = ⟪α, α⟫ := (real_inner_self_eq_norm_sq α).symm
    _ = ⟪α, ((k.factorial : ℝ))⁻¹ • ∑ T : Fin k → Fin n,
        ⟪α, Covector.ofAlt (dxT e k T)⟫ • Covector.ofAlt (dxT e k T)⟫ := by
      rw [← expand_cov (e := e) α]
    _ = _ := by
      simp only [inner_smul_right, inner_sum, real_inner_smul_right]

open Classical in
theorem inner_tSynth_tSynth (hab : ∀ i, a i < b i)
    (hp : ∀ S T, ⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k T)⟫ ≠ 0 → p S = p T)
    (m m' : Fin n → ℕ) (α β : Covector E k)
    (hα : ∀ S, ¬ trigCond (p S) m → ⟪α, Covector.ofAlt (dxT e k S)⟫ = 0) :
    ⟪tSynth e a b p m α, tSynth e a b p m' β⟫ =
      if m = m' then normProd a b m * (((k.factorial : ℝ))⁻¹ * ∑ S : Fin k → Fin n,
        ⟪α, Covector.ofAlt (dxT e k S)⟫ * ⟪β, Covector.ofAlt (dxT e k S)⟫) else 0 := by
  have hk : (k.factorial : ℝ) ≠ 0 := by positivity
  unfold tSynth
  simp only [inner_smul_right, inner_smul_left, inner_sum, sum_inner, RCLike.conj_to_real,
    inner_tLp_p p hab hp]
  by_cases h : m = m'
  · subst h
    simp only [if_true]
    have key : ∀ S : Fin k → Fin n, ∑ T : Fin k → Fin n, ⟪β, Covector.ofAlt (dxT e k T)⟫ *
        (if trigCond (p S) m then ⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k T)⟫ *
          normProd a b m else 0) =
        if trigCond (p S) m then normProd a b m * ((k.factorial : ℝ) *
          ⟪β, Covector.ofAlt (dxT e k S)⟫) else 0 := by
      intro S
      split_ifs
      · rw [← sum_inner_inner_dxT (e := e) β S, Finset.mul_sum]
        refine Finset.sum_congr rfl fun T _ => ?_
        ring
      · simp
    simp only [true_and, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun S _ => ?_
    by_cases hS : trigCond (p S) m
    · have hk' := key S
      simp only [hS, if_true] at hk' ⊢
      have e1 : ∑ x : Fin k → Fin n, (k.factorial : ℝ)⁻¹ * (⟪β, Covector.ofAlt (dxT e k x)⟫ *
          ((k.factorial : ℝ)⁻¹ * (⟪α, Covector.ofAlt (dxT e k S)⟫ *
            (⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k x)⟫ * normProd a b m)))) =
          (k.factorial : ℝ)⁻¹ * (k.factorial : ℝ)⁻¹ * ⟪α, Covector.ofAlt (dxT e k S)⟫ *
            ∑ x : Fin k → Fin n, ⟪β, Covector.ofAlt (dxT e k x)⟫ *
              (⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k x)⟫ * normProd a b m) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        ring
      rw [e1, hk']
      field_simp
    · simp [hS, hα S hS]
  · simp [h]

theorem bessel_t (hab : ∀ i, a i < b i)
    (hp : ∀ S T, ⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k T)⟫ ≠ 0 → p S = p T)
    (w : L2Form (box e a b) k) (M : Finset (Fin n → ℕ)) :
    ∑ m ∈ M, normProd a b m * ‖dCoef e a b p w m‖ ^ 2 ≤ ‖w‖ ^ 2 := by
  classical
  have hα : ∀ m S, ¬ trigCond (p S) m →
      ⟪dCoef e a b p w m, Covector.ofAlt (dxT e k S)⟫ = 0 := fun m S hS =>
    inner_dCoef_eq_zero p hp w m S hS
  have h1 : ⟪w, ∑ m ∈ M, tSynth e a b p m (dCoef e a b p w m)⟫ =
      ∑ m ∈ M, normProd a b m * ‖dCoef e a b p w m‖ ^ 2 := by
    rw [inner_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [inner_tSynth p hab, real_inner_self_eq_norm_sq]
  have h2 : ‖∑ m ∈ M, tSynth e a b p m (dCoef e a b p w m)‖ ^ 2 =
      ∑ m ∈ M, normProd a b m * ‖dCoef e a b p w m‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [inner_sum]
    simp only [inner_tSynth_tSynth p hab hp m _ _ _ (hα m)]
    rw [Finset.sum_ite_eq, if_pos hm, norm_sq_cov (e := e)]
  have h3 := norm_sub_sq_real w (∑ m ∈ M, tSynth e a b p m (dCoef e a b p w m))
  rw [h1, h2] at h3
  nlinarith [sq_nonneg ‖w - ∑ m ∈ M, tSynth e a b p m (dCoef e a b p w m)‖]

end toggled

/-! ### Integration by parts in one direction -/

section application

/-- The pattern of `T`, toggled in the direction `i`. -/
def sp (i : Fin n) (T : Fin k → Fin n) : Fin n → Bool := Function.update (pat T) i (!pat T i)

/-- The sign `+1` if `pat T i = true` and `-1` otherwise. -/
def sgn (i : Fin n) (T : Fin k → Fin n) : ℝ := if pat T i = true then 1 else -1

theorem sp_compat (i : Fin n) (S T : Fin k → Fin n)
    (h : ⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k T)⟫ ≠ 0) :
    sp i S = sp i T := by
  have := pat_eq_of_inner_ne_zero_aux (e := e) h
  unfold sp
  rw [this]

theorem sgn_compat (i : Fin n) (S T : Fin k → Fin n)
    (h : ⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k T)⟫ ≠ 0) :
    sgn i S = sgn i T := by
  have := pat_eq_of_inner_ne_zero_aux (e := e) h
  unfold sgn
  rw [this]

theorem sgn_sq (i : Fin n) (T : Fin k → Fin n) : sgn i T ^ 2 = 1 := by
  unfold sgn; split_ifs <;> norm_num

theorem deriv_trig1_true (a b : ℝ) (m : ℕ) (t : ℝ) :
    deriv (trig1 true a b m) t = freq a b m * trig1 false a b m t := by
  have : trig1 true a b m = trigS a b m := by funext t; simp [trig1]
  rw [this, (hasDerivAt_trigS m t).deriv]
  simp [trig1]

theorem deriv_trig1_false (a b : ℝ) (m : ℕ) (t : ℝ) :
    deriv (trig1 false a b m) t = -(freq a b m * trig1 true a b m t) := by
  have : trig1 false a b m = trigC a b m := by funext t; simp [trig1]
  rw [this, (hasDerivAt_trigC m t).deriv]
  simp [trig1]

theorem fderiv_tau_apply (i : Fin n) (T : Fin k → Fin n) (m : Fin n → ℕ) (x : E) :
    fderiv ℝ (trigProd e a b (sp i T) m) x (e i) =
      -(sgn i T) * freq (a i) (b i) (m i) * trigProd e a b (pat T) m x := by
  rw [fderiv_trigProd_apply, trigProd_split (e := e) (a := a) (b := b) (pat T) m x i]
  have hj : ∀ j ∈ Finset.univ.erase i, sp i T j = pat T j := fun j hj =>
    Function.update_of_ne (Finset.ne_of_mem_erase hj) _ _
  have hprod : ∏ j ∈ Finset.univ.erase i, trig1 (sp i T j) (a j) (b j) (m j) ⟪e j, x⟫ =
      ∏ j ∈ Finset.univ.erase i, trig1 (pat T j) (a j) (b j) (m j) ⟪e j, x⟫ :=
    Finset.prod_congr rfl fun j hj' => by rw [hj j hj']
  rw [hprod]
  cases h : pat T i
  · have : sp i T i = true := by simp [sp, h]
    rw [this, deriv_trig1_true]
    simp [sgn, h]
    ring
  · have : sp i T i = false := by simp [sp, h]
    rw [this, deriv_trig1_false]
    simp [sgn, h]
    ring

theorem ibp_scalar {φ : E → E [⋀^Fin k]→L[ℝ] ℝ} (hφ : IsTestForm (box e a b) φ)
    (i : Fin n) (T : Fin k → Fin n) (m : Fin n → ℕ) :
    ∫ x in box e a b, trigProd e a b (sp i T) m x *
        ⟪Covector.ofAlt (dxT e k T), Covector.ofAlt (fderiv ℝ φ x (e i))⟫ =
      sgn i T * freq (a i) (b i) (m i) * ∫ x in box e a b, trigProd e a b (pat T) m x *
        ⟪Covector.ofAlt (dxT e k T), Covector.ofAlt (φ x)⟫ := by
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : (E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ, ∀ y,
      Λ y = ⟪Covector.ofAlt (dxT e k T), Covector.ofAlt y⟫ :=
    ⟨(innerSL ℝ (Covector.ofAlt (dxT e k T))).comp
      (Covector.ofAlt : (E [⋀^Fin k]→L[ℝ] ℝ) ≃L[ℝ] _).toContinuousLinearMap, fun y => rfl⟩
  have hφd : Differentiable ℝ φ := hφ.contDiff.differentiable (by simp)
  have hφ0 : ∀ x ∉ box e a b, φ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hφ.tsupport_subset h)
  have hD0 : ∀ x ∉ box e a b, fderiv ℝ φ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hφ.tsupport_subset (tsupport_fderiv_subset ℝ h))
  set f : E → ℝ := fun x => Λ (φ x) with hf
  have hfc : ContDiff ℝ (⊤ : ℕ∞) f := Λ.contDiff.comp hφ.contDiff
  have hfd : ∀ x, fderiv ℝ f x (e i) = Λ (fderiv ℝ φ x (e i)) := fun x => by
    have := (Λ.hasFDerivAt.comp x (hφd x).hasFDerivAt).fderiv
    exact congrArg (fun L => L (e i)) this
  have hfcs : HasCompactSupport f := hφ.hasCompactSupport.comp_left (g := Λ) (map_zero Λ)
  have hfcs' : HasCompactSupport (fun x => fderiv ℝ f x (e i)) := hfcs.fderiv_apply ℝ (e i)
  set τ := trigProd e a b (sp i T) m with hτ
  have hτc : ContDiff ℝ (⊤ : ℕ∞) τ := contDiff_trigProd' _ _
  have hτd : Differentiable ℝ τ := hτc.differentiable (by simp)
  have hτ' : Continuous (fun x => fderiv ℝ τ x (e i)) :=
    (hτc.continuous_fderiv (by simp)).clm_apply continuous_const
  have hfd' : Continuous (fun x => fderiv ℝ f x (e i)) :=
    (hfc.continuous_fderiv (by simp)).clm_apply continuous_const
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := τ) (g := f)
    (v := e i)
    (((hτ'.mul hfc.continuous).integrable_of_hasCompactSupport hfcs.mul_left))
    (((hτc.continuous.mul hfd').integrable_of_hasCompactSupport hfcs'.mul_left))
    (((hτc.continuous.mul hfc.continuous).integrable_of_hasCompactSupport hfcs.mul_left))
    (fun x _ => hτd x) (fun x _ => hfc.differentiable (by simp) x)
  have h1 : ∀ x, fderiv ℝ τ x (e i) * f x =
      -(sgn i T * freq (a i) (b i) (m i)) * (trigProd e a b (pat T) m x * f x) := fun x => by
    rw [hτ, fderiv_tau_apply]; ring
  have h2 : ∫ x in box e a b, τ x * Λ (fderiv ℝ φ x (e i)) = ∫ x, τ x * fderiv ℝ f x (e i) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · simp only [hfd]
    · intro x hx
      simp [hD0 x hx]
  have h3 : ∫ x in box e a b, trigProd e a b (pat T) m x * f x =
      ∫ x, trigProd e a b (pat T) m x * f x := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    simp [hf, hφ0 x hx]
  simp only [← hΛ]
  have h4 : ∫ x, fderiv ℝ τ x (e i) * f x =
      -(sgn i T * freq (a i) (b i) (m i)) * ∫ x, trigProd e a b (pat T) m x * f x := by
    simp only [h1]
    rw [integral_const_mul]
  have h5 : ∫ x in box e a b, trigProd e a b (pat T) m x * Λ (φ x) =
      ∫ x in box e a b, trigProd e a b (pat T) m x * f x := rfl
  rw [h2, key, h5, h3, h4]
  ring

theorem memLp_dForm {φ : E → E [⋀^Fin k]→L[ℝ] ℝ} (hφ : IsTestForm (box e a b) φ) (i : Fin n) :
    MemLp (fun x => Covector.ofAlt (fderiv ℝ φ x (e i))) 2 (volume.restrict (box e a b)) := by
  have hc : Continuous (fun x => Covector.ofAlt (fderiv ℝ φ x (e i))) :=
    Covector.ofAlt.continuous.comp ((hφ.contDiff.continuous_fderiv (by simp)).clm_apply
      continuous_const)
  have hs : HasCompactSupport (fun x => Covector.ofAlt (fderiv ℝ φ x (e i))) :=
    (hφ.hasCompactSupport.fderiv_apply ℝ (e i)).comp_left
      (g := fun y : E [⋀^Fin k]→L[ℝ] ℝ => Covector.ofAlt y) (map_zero _)
  exact hc.memLp_of_hasCompactSupport hs

variable (e a b) in
/-- The class of the partial derivative `∂ᵢ φ` of a test form. -/
noncomputable def dataDLp {φ : E → E [⋀^Fin k]→L[ℝ] ℝ} (hφ : IsTestForm (box e a b) φ) (i : Fin n) :
    L2Form (box e a b) k :=
  (memLp_dForm hφ i).toLp _

theorem inner_dLp_tLp {φ : E → E [⋀^Fin k]→L[ℝ] ℝ} (hφ : IsTestForm (box e a b) φ) (i : Fin n)
    (s : Fin n → Bool) (T : Fin k → Fin n) (m : Fin n → ℕ) :
    ⟪dataDLp e a b hφ i, tLp e a b s T m⟫ = ∫ x in box e a b, trigProd e a b s m x *
      ⟪Covector.ofAlt (dxT e k T), Covector.ofAlt (fderiv ℝ φ x (e i))⟫ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_dForm hφ i).coeFn_toLp, coeFn_tLp (e := e) (a := a) (b := b) s T m]
    with x h1 h2
  show ⟪(dataDLp e a b hφ i : L2Form (box e a b) k) x, _⟫ = _
  rw [show (dataDLp e a b hφ i : L2Form (box e a b) k) x = _ from h1, h2]
  simp only [map_smul, real_inner_smul_right]
  rw [real_inner_comm]

theorem inner_toLp_eigLp {φ : E → E [⋀^Fin k]→L[ℝ] ℝ} (hφ : IsTestForm (box e a b) φ)
    (T : Fin k → Fin n) (m : Fin n → ℕ) :
    ⟪hφ.toLp, eigLp e a b T m⟫ = ∫ x in box e a b, trigProd e a b (pat T) m x *
      ⟪Covector.ofAlt (dxT e k T), Covector.ofAlt (φ x)⟫ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hφ.coeFn_toLp, coeFn_eigLp (e := e) (a := a) (b := b) T m] with x h1 h2
  rw [h1, h2]
  simp only [eigForm, map_smul, real_inner_smul_right]
  rw [real_inner_comm]

theorem inner_dLp_tLp_eq {φ : E → E [⋀^Fin k]→L[ℝ] ℝ} (hφ : IsTestForm (box e a b) φ)
    (i : Fin n) (T : Fin k → Fin n) (m : Fin n → ℕ) :
    ⟪dataDLp e a b hφ i, tLp e a b (sp i T) T m⟫ =
      sgn i T * freq (a i) (b i) (m i) * ⟪hφ.toLp, eigLp e a b T m⟫ := by
  rw [inner_dLp_tLp, inner_toLp_eigLp, ibp_scalar hφ]

theorem norm_sq_comb (y : (Fin k → Fin n) → ℝ) :
    ‖((k.factorial : ℝ))⁻¹ • ∑ T : Fin k → Fin n, y T • Covector.ofAlt (dxT e k T)‖ ^ 2 =
      ((k.factorial : ℝ))⁻¹ * ((k.factorial : ℝ))⁻¹ * ∑ S : Fin k → Fin n, ∑ T : Fin k → Fin n,
        y S * (y T * ⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k T)⟫) := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_smul_left, inner_smul_right, sum_inner, inner_sum, RCLike.conj_to_real]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun T _ => ?_
  rw [real_inner_comm]
  ring

theorem norm_sq_comb_sign (σ : (Fin k → Fin n) → ℝ) (hσ : ∀ T, σ T ^ 2 = 1)
    (hσ' : ∀ S T, ⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k T)⟫ ≠ 0 → σ S = σ T)
    (y : (Fin k → Fin n) → ℝ) :
    ‖((k.factorial : ℝ))⁻¹ • ∑ T : Fin k → Fin n, (σ T * y T) • Covector.ofAlt (dxT e k T)‖ ^ 2 =
      ‖((k.factorial : ℝ))⁻¹ • ∑ T : Fin k → Fin n, y T • Covector.ofAlt (dxT e k T)‖ ^ 2 := by
  rw [norm_sq_comb, norm_sq_comb]
  congr 1
  refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun T _ => ?_
  by_cases h : ⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k T)⟫ = 0
  · rw [h]; ring
  · rw [hσ' S T h]
    calc _ = σ T ^ 2 * (y S * (y T * ⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k T)⟫)) := by
          ring
      _ = _ := by rw [hσ T, one_mul]

theorem norm_sq_dCoef (hab : ∀ i, a i < b i) {φ : E → E [⋀^Fin k]→L[ℝ] ℝ}
    (hφ : IsTestForm (box e a b) φ) (i : Fin n) (m : Fin n → ℕ) :
    ‖dCoef e a b (sp i) (dataDLp e a b hφ i) m‖ ^ 2 =
      freq (a i) (b i) (m i) ^ 2 * ‖coef e a b hφ.toLp m‖ ^ 2 := by
  have h1 : dCoef e a b (sp i) (dataDLp e a b hφ i) m = freq (a i) (b i) (m i) •
      (((k.factorial : ℝ))⁻¹ • ∑ T : Fin k → Fin n,
        (sgn i T * (⟪hφ.toLp, eigLp e a b T m⟫ / normProd a b m)) •
          Covector.ofAlt (dxT e k T)) := by
    unfold dCoef
    rw [smul_comm (freq (a i) (b i) (m i))]
    congr 1
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [inner_dLp_tLp_eq, ← mul_smul]
    congr 1
    ring
  rw [h1, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, norm_sq_comb_sign (sgn i) (sgn_sq i)
    (sgn_compat i)]
  rfl

theorem norm_sq_xi (m : Fin n → ℕ) :
    ‖xi e a b m‖ ^ 2 = ∑ i, freq (a i) (b i) (m i) ^ 2 := by
  rw [← e.sum_sq_norm_inner_right (xi e a b m)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_xi, norm_neg, Real.norm_eq_abs, sq_abs]

theorem norm_sq_dLp {φ : E → E [⋀^Fin k]→L[ℝ] ℝ} (hφ : IsTestForm (box e a b) φ) (i : Fin n) :
    ‖dataDLp e a b hφ i‖ ^ 2 = ∫ x in box e a b, ‖Covector.ofAlt (fderiv ℝ φ x (e i))‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_dForm hφ i).coeFn_toLp] with x h1
  rw [show (dataDLp e a b hφ i : L2Form (box e a b) k) x = _ from h1, real_inner_self_eq_norm_sq]

end application

/-- For a test form, the Fourier `H¹`-seminorm is bounded by the `L²` norms of its partial
derivatives (Bessel's inequality for the derivatives, integration by parts). -/
theorem summable_nTerm_and_Nsq_le (hab : ∀ i, a i < b i) {φ : E → E [⋀^Fin k]→L[ℝ] ℝ}
    (hφ : IsTestForm (box e a b) φ) :
    Summable (nTerm e a b hφ.toLp) ∧
      Nsq e a b hφ.toLp ≤ ∑ i, ∫ x in box e a b, ‖Covector.ofAlt (fderiv ℝ φ x (e i))‖ ^ 2 := by
  have hnT : ∀ m, nTerm e a b hφ.toLp m =
      ∑ i, normProd a b m * ‖dCoef e a b (sp i) (dataDLp e a b hφ i) m‖ ^ 2 := by
    intro m
    unfold nTerm
    rw [norm_sq_xi, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [norm_sq_dCoef hab hφ]
    ring
  have hbound : ∀ M : Finset (Fin n → ℕ), ∑ m ∈ M, nTerm e a b hφ.toLp m ≤
      ∑ i, ∫ x in box e a b, ‖Covector.ofAlt (fderiv ℝ φ x (e i))‖ ^ 2 := by
    intro M
    simp only [hnT]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← norm_sq_dLp hφ i]
    exact bessel_t (sp i) hab (sp_compat i) _ M
  have hnn : ∀ m, 0 ≤ nTerm e a b hφ.toLp m := fun m => by
    unfold nTerm
    have := normProd_pos hab m
    positivity
  exact ⟨summable_of_sum_le hnn hbound, Real.tsum_le_of_sum_le hnn hbound⟩

end Fourier

end FEEC
