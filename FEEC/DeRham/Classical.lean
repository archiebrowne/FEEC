/-
Smooth forms have weak exterior derivatives: the classical and weak derivatives agree.
-/
import FEEC.DeRham.L2Complex
import FEEC.DeRham.Polynomial

/-!
# Classical forms in the `L²` de Rham complex

The weak exterior derivative of `FEEC.HasWeakExtDeriv` is defined by duality with the
codifferential. Here we check that this is the right notion: for a `C¹` form `ω`, the
classical exterior derivative `extDeriv ω` (Mathlib) is a weak exterior derivative.

## Main results

* `FEEC.inner_extDeriv_eq_sum`: the pointwise identity `⟪dω, β⟫ = ∑ᵢ ⟪∂ᵢω, β ⌟ eᵢ⟫`.
* `FEEC.integral_inner_extDeriv_eq`: integration by parts, `∫ ⟪dω, φ⟫ = ∫ ⟪ω, δφ⟫` for `φ`
  compactly supported: `δ` is the formal adjoint of `d`.
* `FEEC.hasWeakExtDeriv_of_contDiff`: a `C¹` form `ω` with `ω, dω ∈ L²(Ω)` lies in `HΛᵏ(Ω)`,
  with weak exterior derivative `dω`.
* `FEEC.exists_hasWeakExtDeriv_of_mem_polyForms`: on a bounded open set, polynomial
  differential forms lie in `HΛᵏ(Ω)` and their weak and classical exterior derivatives agree.
  Hence the spaces `𝓟ᵣΛᵏ` and `𝓟ᵣ⁻Λᵏ` are subcomplexes of the `L²` de Rham complex.
-/

namespace FEEC

open Module MeasureTheory

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {k : ℕ}

theorem sum_reindex_aux (a : E →L[ℝ] E [⋀^Fin k]→L[ℝ] ℝ) (β : E [⋀^Fin (k + 1)]→L[ℝ] ℝ)
    (j : Fin (k + 1)) :
    ∑ I : Fin (k + 1) → Fin (finrank ℝ E),
      (-1 : ℝ) ^ (j : ℕ) * (a (stdBasis E (I j)) (fun l => stdBasis E (j.removeNth I l)) *
        β (fun l => stdBasis E (I l))) =
    ∑ i : Fin (finrank ℝ E), ∑ J : Fin k → Fin (finrank ℝ E),
      a (stdBasis E i) (fun l => stdBasis E (J l)) *
        β (Matrix.vecCons (stdBasis E i) (fun l => stdBasis E (J l))) := by
  rw [← (Fin.insertNthEquiv (fun _ => Fin (finrank ℝ E)) j).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun J _ => ?_
  have h1 : (fun l => stdBasis E ((Fin.insertNthEquiv (fun _ => Fin (finrank ℝ E)) j (i, J)) l)) =
      j.insertNth (stdBasis E i) (fun l => stdBasis E (J l)) := by
    ext l
    refine Fin.succAboveCases j ?_ (fun m => ?_) l <;> simp
  have h2 := β.neg_one_pow_smul_map_insertNth j (stdBasis E i) (fun l => stdBasis E (J l))
  simp only [Fin.insertNthEquiv_apply, Fin.insertNth_apply_same, Fin.removeNth_insertNth] at *
  rw [h1, ← h2]
  have h3 : j.removeNth (Fin.insertNthEquiv (fun _ => Fin (finrank ℝ E)) j (i, J)) = J := by
    exact Fin.removeNth_insertNth (α := fun _ => Fin (finrank ℝ E)) j i J
  rw [h3]
  simp only [zsmul_eq_mul]
  push_cast
  ring

/-- The pointwise identity behind integration by parts for the exterior derivative:
`⟪dω, β⟫ = ∑ᵢ ⟪∂ᵢω, β ⌟ eᵢ⟫`. -/
theorem inner_extDeriv_eq_sum {ω : E → E [⋀^Fin k]→L[ℝ] ℝ} {x : E}
    (hω : DifferentiableAt ℝ ω x) (β : E [⋀^Fin (k + 1)]→L[ℝ] ℝ) :
    ⟪Covector.ofAlt (extDeriv ω x), Covector.ofAlt β⟫ =
      ∑ i, ⟪Covector.ofAlt (fderiv ℝ ω x (stdBasis E i)),
        Covector.ofAlt (β.curryLeft (stdBasis E i))⟫ := by
  set a := fderiv ℝ ω x with ha
  have key : ∀ I : Fin (k + 1) → Fin (finrank ℝ E),
      (Covector.ofAlt (extDeriv ω x)).coeff I * (Covector.ofAlt β).coeff I =
      ∑ j : Fin (k + 1), (-1 : ℝ) ^ (j : ℕ) * (a (stdBasis E (I j))
        (fun l => stdBasis E (j.removeNth I l)) * β (fun l => stdBasis E (I l))) := by
    intro I
    rw [Covector.coeff_ofAlt, Covector.coeff_ofAlt, extDeriv_apply hω, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [fderiv_continuousAlternatingMap_apply_const_apply hω]
    simp only [smul_eq_mul, zsmul_eq_mul]
    push_cast
    rw [mul_assoc]
    rfl
  simp only [Covector.inner_def, key]
  rw [Finset.sum_comm]
  simp only [← ha] at *
  have h2 : ∀ j : Fin (k + 1), ∑ I : Fin (k + 1) → Fin (finrank ℝ E),
      (-1 : ℝ) ^ (j : ℕ) * (a (stdBasis E (I j)) (fun l => stdBasis E (j.removeNth I l)) *
        β (fun l => stdBasis E (I l))) =
      ∑ i : Fin (finrank ℝ E), ∑ J : Fin k → Fin (finrank ℝ E),
        a (stdBasis E i) (fun l => stdBasis E (J l)) *
          β (Matrix.vecCons (stdBasis E i) (fun l => stdBasis E (J l))) :=
    fun j => sum_reindex_aux a β j
  simp only [h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [Covector.coeff_ofAlt, ContinuousAlternatingMap.curryLeft_apply_apply,
    ← Finset.mul_sum]
  rw [Nat.factorial_succ]
  push_cast
  have : (k.factorial : ℝ) ≠ 0 := by positivity
  field_simp

variable [MeasurableSpace E] [BorelSpace E]

/-- `b ↦ b.curryLeft v` as a continuous linear map. -/
noncomputable def curryCLM (k : ℕ) (v : E) :
    (E [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] (E [⋀^Fin k]→L[ℝ] ℝ) :=
  (ContinuousLinearMap.apply ℝ (E [⋀^Fin k]→L[ℝ] ℝ) v).comp
    (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := E) (F := ℝ) (n := k)).toContinuousLinearMap

theorem curryCLM_apply (v : E) (b : E [⋀^Fin (k + 1)]→L[ℝ] ℝ) :
    curryCLM k v b = b.curryLeft v := rfl

/-- The bilinear form `(a, b) ↦ ⟪a, b ⌟ v⟫`. -/
noncomputable def pairCLM (k : ℕ) (v : E) :
    (E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] (E [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] ℝ :=
  (innerSL ℝ (E := Covector E k)).bilinearComp Covector.ofAlt.toContinuousLinearMap
    (Covector.ofAlt.toContinuousLinearMap.comp (curryCLM k v))

theorem pairCLM_apply (v : E) (a : E [⋀^Fin k]→L[ℝ] ℝ) (b : E [⋀^Fin (k + 1)]→L[ℝ] ℝ) :
    pairCLM k v a b = inner ℝ (Covector.ofAlt a) (Covector.ofAlt (b.curryLeft v)) := rfl

/-- **The codifferential is the formal adjoint of the exterior derivative**:
`∫ ⟪dω, φ⟫ = ∫ ⟪ω, δφ⟫` for `C¹` forms with `φ` compactly supported. -/
theorem integral_inner_extDeriv_eq {ω : E → E [⋀^Fin k]→L[ℝ] ℝ}
    {φ : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ} (hω : ContDiff ℝ 1 ω) (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) :
    ∫ x, ⟪Covector.ofAlt (extDeriv ω x), Covector.ofAlt (φ x)⟫ =
      ∫ x, ⟪Covector.ofAlt (ω x), Covector.ofAlt (codiff φ x)⟫ := by
  have hωd : Differentiable ℝ ω := hω.differentiable (by norm_num)
  have hφd : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hDω : Continuous (fderiv ℝ ω) := hω.continuous_fderiv (by norm_num)
  have hDφ : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by norm_num)
  have hz : ∀ x, x ∉ tsupport φ → φ x = 0 ∧ fderiv ℝ φ x = 0 := by
    intro x hx
    refine ⟨image_eq_zero_of_notMem_tsupport hx, ?_⟩
    by_contra hne
    exact hx (tsupport_fderiv_subset ℝ (subset_tsupport _ hne))
  have hint : ∀ F : E → ℝ, Continuous F → (∀ x, x ∉ tsupport φ → F x = 0) → Integrable F :=
    fun F hF h0 => hF.integrable_of_hasCompactSupport (HasCompactSupport.intro hφc h0)
  set e := stdBasis E
  have h1 : ∀ x, inner ℝ (Covector.ofAlt (extDeriv ω x)) (Covector.ofAlt (φ x)) =
      ∑ i, pairCLM k (e i) (fderiv ℝ ω x (e i)) (φ x) := fun x => by
    rw [inner_extDeriv_eq_sum (hωd x)]; rfl
  have h2 : ∀ x, inner ℝ (Covector.ofAlt (ω x)) (Covector.ofAlt (codiff φ x)) =
      -∑ i, pairCLM k (e i) (ω x) (fderiv ℝ φ x (e i)) := fun x => by
    rw [codiff_apply, map_neg, map_sum, inner_neg_right, inner_sum]
    simp only [pairCLM_apply]
    rfl
  simp only [h1, h2]
  have hcp : ∀ (v : E) {A : E → E [⋀^Fin k]→L[ℝ] ℝ} {C : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ},
      Continuous A → Continuous C → Continuous fun x => pairCLM k v (A x) (C x) :=
    fun v A C hA hC => ((pairCLM k v).continuous.comp hA).clm_apply hC
  have hI1 : ∀ i, Integrable (fun x => pairCLM k (e i) (fderiv ℝ ω x (e i)) (φ x)) := fun i =>
    hint _ (hcp _ (hDω.clm_apply continuous_const) hφ.continuous) (fun x hx => by
      simp [(hz x hx).1])
  have hI2 : ∀ i, Integrable (fun x => pairCLM k (e i) (ω x) (fderiv ℝ φ x (e i))) := fun i =>
    hint _ (hcp _ hω.continuous (hDφ.clm_apply continuous_const)) (fun x hx => by
      simp [(hz x hx).2])
  have hI3 : ∀ i, Integrable (fun x => pairCLM k (e i) (ω x) (φ x)) := fun i =>
    hint _ (hcp _ hω.continuous hφ.continuous) (fun x hx => by simp [(hz x hx).1])
  rw [integral_neg, integral_finsetSum _ (fun i _ => hI1 i), integral_finsetSum _ (fun i _ => hI2 i),
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := integral_bilinear_fderiv_right_eq_neg_left_of_integrable (μ := volume)
    (B := pairCLM k (e i)) (v := e i) (f := ω) (g := φ) (hI1 i) (hI2 i) (hI3 i)
    (fun x _ => hωd x) (fun x _ => hφd x)
  linarith

variable {Ω : Set E}

/-- **Classical exterior derivatives are weak exterior derivatives**: a `C¹` form `ω` on `E`
with `ω, dω ∈ L²(Ω)` has weak exterior derivative `dω` on `Ω`. -/
theorem hasWeakExtDeriv_of_contDiff (hΩ : IsOpen Ω) {ω : E → E [⋀^Fin k]→L[ℝ] ℝ}
    (hω : ContDiff ℝ 1 ω)
    (h₁ : MemLp (fun x => Covector.ofAlt (ω x)) 2 (volume.restrict Ω))
    (h₂ : MemLp (fun x => Covector.ofAlt (extDeriv ω x)) 2 (volume.restrict Ω)) :
    HasWeakExtDeriv (h₁.toLp _ : L2Form Ω k) (h₂.toLp _) := by
  intro φ hφ
  rw [L2.inner_def, L2.inner_def]
  have hφ1 : ContDiff ℝ 1 φ := hφ.contDiff.of_le (by exact_mod_cast le_top)
  have hz : ∀ x, x ∉ Ω → φ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hφ.tsupport_subset h)
  have hz' : ∀ x, x ∉ Ω → codiff φ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hφ.codiff.tsupport_subset h)
  calc ∫ x, inner ℝ ((h₂.toLp _ : L2Form Ω (k + 1)) x) (hφ.toLp x) ∂(volume.restrict Ω)
      = ∫ x, inner ℝ (Covector.ofAlt (extDeriv ω x)) (Covector.ofAlt (φ x))
          ∂(volume.restrict Ω) := by
        refine integral_congr_ae ?_
        filter_upwards [h₂.coeFn_toLp, hφ.coeFn_toLp] with x h2 h3
        rw [h2, h3]
    _ = ∫ x, inner ℝ (Covector.ofAlt (extDeriv ω x)) (Covector.ofAlt (φ x)) :=
        setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by simp [hz x hx]
    _ = ∫ x, inner ℝ (Covector.ofAlt (ω x)) (Covector.ofAlt (codiff φ x)) :=
        integral_inner_extDeriv_eq hω hφ1 hφ.hasCompactSupport
    _ = ∫ x, inner ℝ (Covector.ofAlt (ω x)) (Covector.ofAlt (codiff φ x))
          ∂(volume.restrict Ω) :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by simp [hz' x hx]).symm
    _ = _ := by
        refine integral_congr_ae ?_
        filter_upwards [h₁.coeFn_toLp, hφ.codiff.coeFn_toLp] with x h2 h3
        rw [h2, h3]

/-- A continuous form is square integrable on a bounded open set. -/
theorem memLp_ofAlt_of_continuous (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {ω : E → E [⋀^Fin k]→L[ℝ] ℝ} (hω : Continuous ω) :
    MemLp (fun x => Covector.ofAlt (ω x)) 2 (volume.restrict Ω) := by
  have hc : Continuous (fun x => Covector.ofAlt (ω x)) :=
    Covector.ofAlt.continuous.comp hω
  have hK : IsCompact (closure Ω) := hb.isCompact_closure
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  haveI : IsFiniteMeasure (volume.restrict Ω) := ⟨by simpa using hb.measure_lt_top⟩
  refine MemLp.of_bound hc.aestronglyMeasurable C ?_
  exact (ae_restrict_iff' hΩ.measurableSet).2 (Filter.Eventually.of_forall fun x hx =>
    hC x (subset_closure hx))

/-- **Polynomial differential forms lie in `HΛᵏ(Ω)`** for bounded open `Ω`, and their weak
exterior derivative is the classical one. -/
theorem exists_hasWeakExtDeriv_of_mem_polyForms (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {r : ℕ} {ω : E → E [⋀^Fin k]→L[ℝ] ℝ} (hω : ω ∈ polyForms E r k) :
    ∃ (h₁ : MemLp (fun x => Covector.ofAlt (ω x)) 2 (volume.restrict Ω))
      (h₂ : MemLp (fun x => Covector.ofAlt (extDeriv ω x)) 2 (volume.restrict Ω)),
      HasWeakExtDeriv (h₁.toLp _ : L2Form Ω k) (h₂.toLp _) := by
  have hs : ContDiff ℝ (⊤ : ℕ∞) ω := by
    obtain ⟨c, hc, rfl⟩ := mem_polyForms_iff.1 hω
    have := ContDiff.sum (s := Finset.range (r + 1)) fun j _ => (hc j).contDiff
    convert this using 1
    ext x
    simp
  have hd : Continuous (extDeriv ω) := by
    exact (differentiable_of_mem_polyForms
      (extDeriv_mem_polyForms (polyForms_mono (Nat.le_succ r) hω))).continuous
  exact ⟨memLp_ofAlt_of_continuous hΩ hb hs.continuous, memLp_ofAlt_of_continuous hΩ hb hd,
    hasWeakExtDeriv_of_contDiff hΩ (hs.of_le (by exact_mod_cast le_top)) _ _⟩

end FEEC
