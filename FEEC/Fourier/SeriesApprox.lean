/-
Approximation estimate for L² forms with finite Fourier H¹-seminorm.
-/
import FEEC.Fourier.Regularity
import FEEC.Tensor.Approx

/-!
# Approximation of forms with finite Fourier `H¹`-seminorm

`‖w − πₕ w‖² ≤ C h² Nsq w` for every `L²` form `w` on the box with summable `nTerm`, where
`πₕ` is the `L²` operator of the tensor-product dual system. Proof: apply
`Tensor.exists_approx_smooth` to the partial sums of the eigenform expansion
(`hasSum_synth_coef`), whose derivatives are controlled by `nTerm`, and pass to the limit.
-/

namespace FEEC

namespace Fourier

open MeasureTheory Tensor

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {n : ℕ}
  {e : OrthonormalBasis (Fin n) ℝ E} {a b : Fin n → ℝ} {k : ℕ}

/-- The smooth function representing a finite eigenform sum. -/
noncomputable def synthFun (e : OrthonormalBasis (Fin n) ℝ E) (a b : Fin n → ℝ)
    (M : Finset (Fin n → ℕ)) (c : (Fin n → ℕ) → Covector E k) : E → E [⋀^Fin k]→L[ℝ] ℝ :=
  fun x => ∑ m ∈ M, ((k.factorial : ℝ))⁻¹ •
    ∑ T : Fin k → Fin n, ⟪c m, Covector.ofAlt (dxT e k T)⟫ • eigForm e a b T m x

theorem synthFun_mem_span (M : Finset (Fin n → ℕ)) (c : (Fin n → ℕ) → Covector E k) :
    synthFun e a b M c ∈ Submodule.span ℝ (Set.range fun p : (Fin k → Fin n) × (Fin n → ℕ) =>
      eigForm e a b p.1 p.2) := by
  have : synthFun e a b M c = ∑ m ∈ M, ((k.factorial : ℝ))⁻¹ •
      ∑ T : Fin k → Fin n, ⟪c m, Covector.ofAlt (dxT e k T)⟫ • eigForm e a b T m := by
    funext x; simp [synthFun, Finset.sum_apply]
  rw [this]
  exact Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (Submodule.sum_mem _ fun T _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨(T, m), rfl⟩))

theorem contDiff_synthFun (M : Finset (Fin n → ℕ)) (c : (Fin n → ℕ) → Covector E k) :
    ContDiff ℝ 1 (synthFun e a b M c) := by
  unfold synthFun
  refine ContDiff.sum fun m _ => ContDiff.const_smul _ (ContDiff.sum fun T _ =>
    ContDiff.const_smul _ ?_)
  exact (contDiff_eigForm T m).of_le (by simp)

theorem coeFn_wOf' (g : E → E [⋀^Fin k]→L[ℝ] ℝ) (hg : Continuous g) :
    wOf e a b g hg =ᵐ[volume.restrict (box e a b)] fun x => Covector.ofAlt (g x) :=
  MemLp.coeFn_toLp _

theorem wOf_family {ι : Type*} (M : Finset ι) (s : ℝ) (r : ι → (Fin k → Fin n) → ℝ)
    (F : ι → (Fin k → Fin n) → E → (E [⋀^Fin k]→L[ℝ] ℝ)) (hF : ∀ m T, Continuous (F m T))
    (hg : Continuous fun x => ∑ m ∈ M, s • ∑ T, r m T • F m T x) :
    wOf e a b (fun x => ∑ m ∈ M, s • ∑ T, r m T • F m T x) hg =
      ∑ m ∈ M, s • ∑ T, r m T • wOf e a b (F m T) (hF m T) := by
  classical
  refine Lp.ext ?_
  have h1 : ∀ m ∈ M, ∀ᵐ x ∂(volume.restrict (box e a b)),
      (⇑(∑ T, r m T • wOf e a b (F m T) (hF m T) : L2Form (box e a b) k)) x =
        ∑ T, r m T • Covector.ofAlt (F m T x) := by
    intro m _
    filter_upwards [coeFn_sum_smul' (Finset.univ : Finset (Fin k → Fin n)) (r m)
      (fun T => wOf e a b (F m T) (hF m T)),
      ae_all_iff.2 fun T : Fin k → Fin n => coeFn_wOf' (e := e) (a := a) (b := b) (F m T) (hF m T)]
      with x h1 h2
    rw [h1]
    simp only [h2]
  filter_upwards [coeFn_wOf' (e := e) (a := a) (b := b) _ hg,
    coeFn_sum_smul' M (fun _ => s) (fun m => ∑ T, r m T • wOf e a b (F m T) (hF m T)),
    (Filter.eventually_all_finset M).2 h1] with x hx h2 h3
  rw [hx, h2]
  simp only [map_sum, map_smul]
  exact Finset.sum_congr rfl fun m hm => by rw [h3 m hm]

theorem eigLp_eq_wOf (T : Fin k → Fin n) (m : Fin n → ℕ) :
    eigLp e a b T m = wOf e a b (eigForm e a b T m) (contDiff_eigForm T m).continuous := rfl

theorem toLp_synthFun (hab : ∀ i, a i < b i) (M : Finset (Fin n → ℕ))
    (c : (Fin n → ℕ) → Covector E k) :
    (memLp_of_continuous_box e a b
      (Covector.ofAlt.continuous.comp (contDiff_synthFun (e := e) (a := a) (b := b) M c).continuous)).toLp _ =
      ∑ m ∈ M, synth e a b m (c m) := by
  have := wOf_family (e := e) (a := a) (b := b) M ((k.factorial : ℝ))⁻¹
    (fun m T => ⟪c m, Covector.ofAlt (dxT e k T)⟫) (fun m T => eigForm e a b T m)
    (fun m T => (contDiff_eigForm T m).continuous)
    (contDiff_synthFun (e := e) (a := a) (b := b) M c).continuous
  exact this


theorem continuous_fderiv_trigProd (s : Fin n → Bool) (m : Fin n → ℕ) (i : Fin n) :
    Continuous fun x => fderiv ℝ (trigProd e a b s m) x (e i) :=
  ((contDiff_trigProd' (e := e) (a := a) (b := b) s m).continuous_fderiv (by simp)).clm_apply
    continuous_const

variable (e a b) in
/-- The `i`-th partial derivative of an eigenform. -/
noncomputable def dxF (i : Fin n) (T : Fin k → Fin n) (m : Fin n → ℕ) (x : E) :
    E [⋀^Fin k]→L[ℝ] ℝ :=
  fderiv ℝ (trigProd e a b (pat T) m) x (e i) • dxT e k T

theorem continuous_dxF (i : Fin n) (T : Fin k → Fin n) (m : Fin n → ℕ) :
    Continuous (dxF e a b i T m) :=
  (continuous_fderiv_trigProd _ m i).smul continuous_const

variable (e a b) in
/-- The class of the `i`-th partial derivative of an eigenform. -/
noncomputable def dLp (i : Fin n) (T : Fin k → Fin n) (m : Fin n → ℕ) : L2Form (box e a b) k :=
  wOf e a b (dxF e a b i T m) (continuous_dxF i T m)

theorem wOf_congr {g g' : E → E [⋀^Fin k]→L[ℝ] ℝ} (h : g = g') (hg : Continuous g)
    (hg' : Continuous g') : wOf e a b g hg = wOf e a b g' hg' := by
  subst h; rfl

theorem fderiv_synthFun_apply (M : Finset (Fin n → ℕ)) (c : (Fin n → ℕ) → Covector E k) (x : E)
    (i : Fin n) :
    fderiv ℝ (synthFun e a b M c) x (e i) = ∑ m ∈ M, ((k.factorial : ℝ))⁻¹ •
      ∑ T : Fin k → Fin n, ⟪c m, Covector.ofAlt (dxT e k T)⟫ • dxF e a b i T m x := by
  have h : ∀ (m : Fin n → ℕ) (T : Fin k → Fin n), HasFDerivAt (fun y => eigForm e a b T m y)
      ((fderiv ℝ (trigProd e a b (pat T) m) x).smulRight (dxT e k T)) x := fun m T =>
    (((contDiff_trigProd' (e := e) (a := a) (b := b) (pat T) m).differentiable (by simp)) x
      ).hasFDerivAt.smul_const (dxT e k T)
  have h2 : HasFDerivAt (synthFun e a b M c) (∑ m ∈ M, ((k.factorial : ℝ))⁻¹ •
      ∑ T : Fin k → Fin n, ⟪c m, Covector.ofAlt (dxT e k T)⟫ •
        ((fderiv ℝ (trigProd e a b (pat T) m) x).smulRight (dxT e k T))) x := by
    unfold synthFun
    exact HasFDerivAt.fun_sum fun m _ => (HasFDerivAt.fun_sum fun T _ =>
      (h m T).const_smul (⟪c m, Covector.ofAlt (dxT e k T)⟫)).const_smul ((k.factorial : ℝ))⁻¹
  rw [h2.fderiv]
  simp [dxF, sum_apply]

theorem integral_dtrig1_mul {a' b' : ℝ} (hab : a' < b') (s : Bool) (m m' : ℕ) :
    ∫ t in Set.Ioo a' b', deriv (trig1 s a' b' m) t * deriv (trig1 s a' b' m') t =
      if m = m' ∧ (s = true → m ≠ 0) then freq a' b' m ^ 2 * trigNormSq a' b' m else 0 := by
  have hf0 : freq a' b' 0 = 0 := by simp [freq]
  cases s
  · have hd : ∀ (m : ℕ) (t : ℝ), deriv (trig1 false a' b' m) t = -(freq a' b' m * trigS a' b' m t) :=
      fun m t => by
        have : trig1 false a' b' m = trigC a' b' m := by funext t; simp [trig1]
        rw [this]; exact (hasDerivAt_trigC m t).deriv
    simp_rw [hd]
    have : ∀ t, -(freq a' b' m * trigS a' b' m t) * -(freq a' b' m' * trigS a' b' m' t) =
        (freq a' b' m * freq a' b' m') * (trigS a' b' m t * trigS a' b' m' t) := fun t => by ring
    simp_rw [this]
    rw [integral_const_mul, integral_trigS_mul_trigS hab]
    by_cases h : m = m'
    · subst h; by_cases h0 : m = 0 <;> simp [h0, hf0, sq]
    · simp [h]
  · have hd : ∀ (m : ℕ) (t : ℝ), deriv (trig1 true a' b' m) t = freq a' b' m * trigC a' b' m t :=
      fun m t => by
        have : trig1 true a' b' m = trigS a' b' m := by funext t; simp [trig1]
        rw [this]; exact (hasDerivAt_trigS m t).deriv
    simp_rw [hd]
    have : ∀ t, freq a' b' m * trigC a' b' m t * (freq a' b' m' * trigC a' b' m' t) =
        (freq a' b' m * freq a' b' m') * (trigC a' b' m t * trigC a' b' m' t) := fun t => by ring
    simp_rw [this]
    rw [integral_const_mul, integral_trigC_mul_trigC hab]
    by_cases h : m = m'
    · subst h; by_cases h0 : m = 0 <;> simp [h0, hf0, sq]
    · simp [h]

variable (a b) in
/-- The factors of the `i`-th partial derivative of a product. -/
noncomputable def dfac (i : Fin n) (s : Fin n → Bool) (m : Fin n → ℕ) (j : Fin n) (t : ℝ) : ℝ :=
  if j = i then deriv (trig1 (s j) (a j) (b j) (m j)) t else trig1 (s j) (a j) (b j) (m j) t

theorem fderiv_trigProd_eq_prod (s : Fin n → Bool) (m : Fin n → ℕ) (x : E) (i : Fin n) :
    fderiv ℝ (trigProd e a b s m) x (e i) = ∏ j, dfac a b i s m j ⟪e j, x⟫ := by
  rw [fderiv_trigProd_apply, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  congr 1
  · simp [dfac]
  · exact Finset.prod_congr rfl fun j hj => by simp [dfac, Finset.ne_of_mem_erase hj]

theorem integral_prod_dfac (hab : ∀ i, a i < b i) (i : Fin n) (s : Fin n → Bool) (m m' : Fin n → ℕ) :
    ∫ x in box e a b, (∏ j, dfac a b i s m j ⟪e j, x⟫) * (∏ j, dfac a b i s m' j ⟪e j, x⟫) =
      if m = m' ∧ (∀ j, s j = true → m j ≠ 0) then
        freq (a i) (b i) (m i) ^ 2 * normProd a b m else 0 := by
  simp_rw [← Finset.prod_mul_distrib]
  rw [integral_box_prod e a b (fun j t => dfac a b i s m j t * dfac a b i s m' j t)]
  have h1 : ∀ j, ∫ t in Set.Ioo (a j) (b j), dfac a b i s m j t * dfac a b i s m' j t =
      if (m j = m' j ∧ (s j = true → m j ≠ 0)) then
        (if j = i then freq (a j) (b j) (m j) ^ 2 else 1) * trigNormSq (a j) (b j) (m j) else 0 := by
    intro j
    by_cases hj : j = i
    · subst hj
      simp only [dfac, if_true]
      rw [integral_dtrig1_mul (hab j)]
    · simp only [dfac, hj, if_false]
      rw [integral_trig1_mul (hab j)]
      split_ifs <;> simp
  rw [Finset.prod_congr rfl fun j _ => h1 j, Finset.prod_ite_zero]
  by_cases hc : m = m' ∧ (∀ j, s j = true → m j ≠ 0)
  · have : ∀ j ∈ Finset.univ, (m j = m' j ∧ (s j = true → m j ≠ 0)) :=
      fun j _ => ⟨congrFun hc.1 j, hc.2 j⟩
    rw [if_pos this, if_pos hc, Finset.prod_mul_distrib]
    simp [normProd]
  · rw [if_neg hc, if_neg]
    intro hall
    exact hc ⟨funext fun j => (hall j (Finset.mem_univ j)).1,
      fun j => (hall j (Finset.mem_univ j)).2⟩

theorem inner_dLp (hab : ∀ i, a i < b i) (i : Fin n) (S T : Fin k → Fin n) (m m' : Fin n → ℕ) :
    ⟪dLp e a b i S m, dLp e a b i T m'⟫ =
      if m = m' then freq (a i) (b i) (m i) ^ 2 * ⟪eigLp e a b S m, eigLp e a b T m'⟫ else 0 := by
  unfold dLp
  rw [L2.inner_def]
  have h1 : ∀ᵐ x ∂(volume.restrict (box e a b)),
      ⟪(wOf e a b (dxF e a b i S m) (continuous_dxF i S m) : L2Form (box e a b) k) x,
        (wOf e a b (dxF e a b i T m') (continuous_dxF i T m') : L2Form (box e a b) k) x⟫ =
        ((∏ j, dfac a b i (pat S) m j ⟪e j, x⟫) * (∏ j, dfac a b i (pat T) m' j ⟪e j, x⟫)) *
          ⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k T)⟫ := by
    filter_upwards [coeFn_wOf' (e := e) (a := a) (b := b) _ (continuous_dxF i S m),
      coeFn_wOf' (e := e) (a := a) (b := b) _ (continuous_dxF i T m')] with x h2 h3
    rw [h2, h3]
    simp only [dxF, map_smul, real_inner_smul_left, real_inner_smul_right,
      fderiv_trigProd_eq_prod]
    ring
  rw [integral_congr_ae h1, integral_mul_const, inner_eigLp hab]
  by_cases h : ⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k T)⟫ = 0
  · simp [h]
  · have hp : pat S = pat T := pat_eq_of_inner_ne_zero_aux (e := e) h
    rw [← hp, integral_prod_dfac hab]
    have hcond : (∀ j, pat S j = true → m j ≠ 0) ↔ ∀ p, m (S p) ≠ 0 := by
      constructor
      · intro hh p
        exact hh _ ((pat_eq_true_iff' S _).2 ⟨p, rfl⟩)
      · intro hh j hj
        obtain ⟨p, rfl⟩ := (pat_eq_true_iff' S j).1 hj
        exact hh p
    by_cases hmm : m = m'
    · by_cases hq : ∀ p, m (S p) ≠ 0
      · rw [if_pos ⟨hmm, hcond.2 hq⟩, if_pos hmm, if_pos ⟨hmm, hq⟩]
        ring
      · rw [if_neg (fun hh => hq (hcond.1 hh.2)), if_pos hmm, if_neg (fun hh => hq hh.2)]
        simp
    · simp [hmm]


theorem inner_combo {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {ι : Type*}
    [Fintype ι] (s : ℝ) (r r' : ι → ℝ) (X Y : ι → V) :
    ⟪s • ∑ S, r S • X S, s • ∑ T, r' T • Y T⟫ = s * s * ∑ S, ∑ T, r S * r' T * ⟪X S, Y T⟫ := by
  simp only [real_inner_smul_left, real_inner_smul_right, sum_inner, inner_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun T _ => ?_
  ring

theorem inner_dLp_sum (hab : ∀ i, a i < b i) (i : Fin n) (c : (Fin n → ℕ) → Covector E k)
    (hc : ∀ m, allow e m (c m) = c m) (m m' : Fin n → ℕ) :
    ⟪((k.factorial : ℝ))⁻¹ • ∑ T : Fin k → Fin n, ⟪c m, Covector.ofAlt (dxT e k T)⟫ • dLp e a b i T m,
      ((k.factorial : ℝ))⁻¹ • ∑ T : Fin k → Fin n, ⟪c m', Covector.ofAlt (dxT e k T)⟫ •
        dLp e a b i T m'⟫ =
      if m = m' then freq (a i) (b i) (m i) ^ 2 * (normProd a b m * ‖c m‖ ^ 2) else 0 := by
  rw [inner_combo]
  simp only [inner_dLp hab]
  by_cases h : m = m'
  · subst h
    have h2 := inner_synth_synth (e := e) (a := a) (b := b) hab m m (c m) (c m)
    rw [if_pos rfl, hc] at h2
    unfold synth at h2
    rw [inner_combo] at h2
    simp only [if_true]
    rw [real_inner_self_eq_norm_sq] at h2
    rw [← h2, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun T _ => by ring
  · simp [h]


theorem sum_freq_sq (m : Fin n → ℕ) :
    ∑ i, freq (a i) (b i) (m i) ^ 2 = ‖xi e a b m‖ ^ 2 := by
  rw [← e.sum_sq_norm_inner_right (xi e a b m)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_xi, norm_neg, Real.norm_eq_abs, sq_abs]

theorem integral_fderiv_synthFun (hab : ∀ i, a i < b i) (M : Finset (Fin n → ℕ))
    (c : (Fin n → ℕ) → Covector E k) (hc : ∀ m, allow e m (c m) = c m) (i : Fin n) :
    ∫ x in box e a b, ‖Covector.ofAlt (fderiv ℝ (synthFun e a b M c) x (e i))‖ ^ 2 =
      ∑ m ∈ M, freq (a i) (b i) (m i) ^ 2 * (normProd a b m * ‖c m‖ ^ 2) := by
  have hG : Continuous fun x => fderiv ℝ (synthFun e a b M c) x (e i) :=
    ((contDiff_synthFun (e := e) (a := a) (b := b) M c).continuous_fderiv one_ne_zero).clm_apply
      continuous_const
  have h1 : ∫ x in box e a b, ‖Covector.ofAlt (fderiv ℝ (synthFun e a b M c) x (e i))‖ ^ 2 =
      ‖wOf e a b (fun x => fderiv ℝ (synthFun e a b M c) x (e i)) hG‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_wOf' (e := e) (a := a) (b := b) _ hG] with x hx
    rw [hx, real_inner_self_eq_norm_sq]
  have hfun : (fun x => fderiv ℝ (synthFun e a b M c) x (e i)) = fun x => ∑ m ∈ M,
      ((k.factorial : ℝ))⁻¹ • ∑ T : Fin k → Fin n,
        ⟪c m, Covector.ofAlt (dxT e k T)⟫ • dxF e a b i T m x :=
    funext fun x => fderiv_synthFun_apply M c x i
  have hG' : Continuous fun x => ∑ m ∈ M, ((k.factorial : ℝ))⁻¹ • ∑ T : Fin k → Fin n,
        ⟪c m, Covector.ofAlt (dxT e k T)⟫ • dxF e a b i T m x := hfun ▸ hG
  have h2 := wOf_family (e := e) (a := a) (b := b) M ((k.factorial : ℝ))⁻¹
    (fun m T => ⟪c m, Covector.ofAlt (dxT e k T)⟫) (fun m T => dxF e a b i T m)
    (fun m T => continuous_dxF i T m) hG'
  rw [h1, wOf_congr hfun hG hG', h2, ← real_inner_self_eq_norm_sq, sum_inner]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [inner_sum]
  have : ∀ m' ∈ M, ⟪((k.factorial : ℝ))⁻¹ • ∑ T : Fin k → Fin n,
      ⟪c m, Covector.ofAlt (dxT e k T)⟫ • wOf e a b (dxF e a b i T m) (continuous_dxF i T m),
      ((k.factorial : ℝ))⁻¹ • ∑ T : Fin k → Fin n, ⟪c m', Covector.ofAlt (dxT e k T)⟫ •
        wOf e a b (dxF e a b i T m') (continuous_dxF i T m')⟫ =
      if m = m' then freq (a i) (b i) (m i) ^ 2 * (normProd a b m * ‖c m‖ ^ 2) else 0 :=
    fun m' _ => inner_dLp_sum hab i c hc m m'
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq, if_pos hm]

/-- Derivatives of finite eigenform sums. -/
theorem sum_integral_fderiv_synthFun_le (hab : ∀ i, a i < b i) (M : Finset (Fin n → ℕ))
    (c : (Fin n → ℕ) → Covector E k) (hc : ∀ m, allow e m (c m) = c m) :
    ∑ i, ∫ x in box e a b, ‖Covector.ofAlt (fderiv ℝ (synthFun e a b M c) x (e i))‖ ^ 2 ≤
      ∑ m ∈ M, normProd a b m * ‖xi e a b m‖ ^ 2 * ‖c m‖ ^ 2 := by
  refine le_of_eq ?_
  simp_rw [integral_fderiv_synthFun hab M c hc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← Finset.sum_mul, sum_freq_sq (e := e) (a := a) (b := b) m]
  ring


open Filter Topology in
/-- **Approximation estimate** in terms of the Fourier `H¹`-seminorm. -/
theorem exists_approx_series (n k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E] (e : OrthonormalBasis (Fin n) ℝ E)
      (a b : Fin n → ℝ) (N : Fin n → ℕ) (hab : ∀ i, a i < b i) (hN : ∀ i, 0 < N i) (h : ℝ)
      (_ : ∀ i, Ref.meshH (a i) (b i) (N i) ≤ h) (w : L2Form (box e a b) k)
      (_ : Summable (nTerm e a b w)),
      ‖w - (deRhamComplex (isOpen_box e a b)).dualOp (shapeH (e := e) hab hN)
            (dualL (e := e) hab hN) (fun k => ((k.factorial : ℝ))⁻¹) k w‖ ^ 2 ≤
        C * h ^ 2 * Nsq e a b w := by
  obtain ⟨C, hC0, hC⟩ := Tensor.exists_approx_smooth n k
  refine ⟨C, hC0, ?_⟩
  intro E _ _ _ _ _ e a b N hab hN h hh w hw
  set P := (deRhamComplex (isOpen_box e a b)).dualOp (shapeH (e := e) hab hN)
    (dualL (e := e) hab hN) (fun k => ((k.factorial : ℝ))⁻¹) k with hP
  have hlim : Tendsto (fun M : Finset (Fin n → ℕ) => ∑ m ∈ M, synth e a b m (coef e a b w m))
      atTop (𝓝 w) := hasSum_synth_coef hab w
  have hcont : Tendsto (fun M : Finset (Fin n → ℕ) =>
      ‖(∑ m ∈ M, synth e a b m (coef e a b w m)) - P (∑ m ∈ M, synth e a b m (coef e a b w m))‖ ^ 2)
      atTop (𝓝 (‖w - P w‖ ^ 2)) := by
    have : Continuous fun v : L2Form (box e a b) k => ‖v - P v‖ ^ 2 :=
      (continuous_norm.comp (continuous_id.sub P.continuous)).pow 2
    exact (this.tendsto w).comp hlim
  refine le_of_tendsto' hcont fun M => ?_
  have hmem := synthFun_mem_span (e := e) (a := a) (b := b) M (fun m => coef e a b w m)
  have h1 := hC e a b N hab hN h hh (synthFun e a b M (fun m => coef e a b w m))
    (contDiff_synthFun M _) hmem
  rw [toLp_synthFun hab M (fun m => coef e a b w m)] at h1
  refine h1.trans ?_
  have h3 := sum_integral_fderiv_synthFun_le hab M (fun m => coef e a b w m)
    (fun m => allow_coef hab w m)
  have h4 : ∑ m ∈ M, normProd a b m * ‖xi e a b m‖ ^ 2 * ‖coef e a b w m‖ ^ 2 ≤ Nsq e a b w :=
    hw.sum_le_tsum M (fun m _ => by
      have := normProd_pos hab m
      positivity)
  have h5 : 0 ≤ C * h ^ 2 := by positivity
  exact mul_le_mul_of_nonneg_left (h3.trans h4) h5

end Fourier

end FEEC
