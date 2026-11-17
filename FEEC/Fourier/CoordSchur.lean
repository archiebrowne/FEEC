/-
Operators acting in one coordinate of a box.
-/
import FEEC.Tensor.BoxIntegral

/-!
# Integral operators acting in one coordinate of a box

For a kernel `k : ℝ → ℝ → ℝ` on `(a j, b j)` with Schur constants `A`, `B`, the operator
`F ↦ (x ↦ ∫ τ in (a j, b j), k ⟪e j, x⟫ τ * F (x + (τ - ⟪e j, x⟫) • e j))` is bounded on
`L²(box)` with norm at most `√(A B)`.
-/

namespace FEEC

open MeasureTheory

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {n : ℕ}


open scoped ENNReal

/-- Splitting off one coordinate of a product measure. -/
theorem lintegral_pi_split {m : ℕ} (μ : Fin (m + 1) → Measure ℝ) [∀ i, SigmaFinite (μ i)]
    (j : Fin (m + 1)) (H : (Fin (m + 1) → ℝ) → ℝ≥0∞) :
    ∫⁻ y, H y ∂Measure.pi μ =
      ∫⁻ p, H (Fin.insertNth j p.1 p.2) ∂((μ j).prod (Measure.pi fun i => μ (j.succAbove i))) := by
  have h := ((measurePreserving_piFinSuccAbove μ j).symm _).lintegral_comp_emb
    (MeasurableEquiv.measurableEmbedding _) H
  rw [← h]
  rfl

theorem core_coord {m : ℕ} (μ : Fin (m + 1) → Measure ℝ) [∀ i, SigmaFinite (μ i)]
    (j : Fin (m + 1)) {K : ℝ → ℝ → ℝ≥0∞} (hK : Measurable (Function.uncurry K))
    {g : (Fin (m + 1) → ℝ) → ℝ≥0∞} (hg : Measurable g) {B' : ℝ≥0∞}
    (hB : ∀ᵐ τ ∂μ j, ∫⁻ s, K s τ ∂μ j ≤ B') :
    ∫⁻ y, ∫⁻ τ, K (y j) τ * g (Function.update y j τ) ∂μ j ∂Measure.pi μ ≤
      B' * ∫⁻ y, g y ∂Measure.pi μ := by
  have hins : Measurable (fun q : ℝ × (Fin m → ℝ) => (Fin.insertNth j q.1 q.2 : Fin (m+1) → ℝ)) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) j).symm.measurable
  have hΦ : Measurable (fun y : Fin (m + 1) → ℝ =>
      ∫⁻ τ, K (y j) τ * g (Function.update y j τ) ∂μ j) := by
    refine Measurable.lintegral_prod_right' (f := fun q : (Fin (m+1) → ℝ) × ℝ =>
      K (q.1 j) q.2 * g (Function.update q.1 j q.2)) ?_
    refine Measurable.mul ?_ ?_
    · exact hK.comp (f := fun q : (Fin (m+1) → ℝ) × ℝ => (q.1 j, q.2)) (by fun_prop)
    · exact hg.comp (by
        refine measurable_pi_iff.2 fun i => ?_
        by_cases hi : i = j
        · subst hi; simpa using measurable_snd
        · simp only [Function.update_of_ne hi]; fun_prop)
  rw [lintegral_pi_split μ j _, lintegral_pi_split μ j g]
  simp only [Fin.insertNth_apply_same, Fin.update_insertNth]
  set ρ := Measure.pi fun i => μ (j.succAbove i)
  have hG : Measurable (fun q : ℝ × (Fin m → ℝ) => g (Fin.insertNth j q.1 q.2)) := hg.comp hins
  have hT : Measurable (fun w : (ℝ × (Fin m → ℝ)) × ℝ =>
      K w.1.1 w.2 * g (Fin.insertNth j w.2 w.1.2)) := by
    refine Measurable.mul ?_ ?_
    · exact hK.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    · exact hg.comp (hins.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))
  rw [lintegral_prod _ (hT.lintegral_prod_right').aemeasurable,
    lintegral_prod _ hG.aemeasurable]
  rw [lintegral_lintegral_swap (hT.lintegral_prod_right').aemeasurable]
  dsimp only
  have hR : ∫⁻ x, ∫⁻ y, g (Fin.insertNth j x y) ∂ρ ∂μ j =
      ∫⁻ y, ∫⁻ x, g (Fin.insertNth j x y) ∂μ j ∂ρ :=
    lintegral_lintegral_swap hG.aemeasurable
  rw [hR, ← lintegral_const_mul _ hG.lintegral_prod_left']
  refine lintegral_mono fun r => ?_
  have hT' : Measurable (fun w : ℝ × ℝ => K w.1 w.2 * g (Fin.insertNth j w.2 r)) :=
    hK.mul (hg.comp (hins.comp (measurable_snd.prodMk measurable_const)))
  have hgr : Measurable (fun x : ℝ => g (Fin.insertNth j x r)) :=
    hg.comp (hins.comp (measurable_id.prodMk measurable_const))
  dsimp only
  rw [lintegral_lintegral_swap hT'.aemeasurable, ← lintegral_const_mul _ hgr]
  refine lintegral_mono_ae ?_
  filter_upwards [hB] with τ hτ
  have hKτ : Measurable (fun x : ℝ => K x τ) :=
    hK.comp (measurable_id.prodMk measurable_const)
  rw [lintegral_mul_const _ hKτ]
  gcongr


theorem coordEquiv_update (e : OrthonormalBasis (Fin n) ℝ E) (x : E) (j : Fin n) (τ : ℝ) :
    coordEquiv e (x + (τ - ⟪e j, x⟫) • e j) = Function.update (coordEquiv e x) j τ := by
  have ho := orthonormal_iff_ite.1 e.orthonormal
  ext i
  rw [coordEquiv_apply, inner_add_right, inner_smul_right, ← coordEquiv_apply e x i]
  by_cases h : i = j
  · subst h
    simp [coordEquiv_apply]
  · simp [ho, h]

theorem lintegral_box_coord (e : OrthonormalBasis (Fin n) ℝ E) (a b : Fin n → ℝ)
    (H : (Fin n → ℝ) → ℝ≥0∞) :
    ∫⁻ x in box e a b, H (coordEquiv e x) =
      ∫⁻ y, H y ∂Measure.pi (fun i => volume.restrict (Set.Ioo (a i) (b i))) := by
  rw [preimage_pi_coordEquiv,
    (measurePreserving_coordEquiv e).setLIntegral_comp_preimage_emb
      (coordEquiv e).measurableEmbedding H, volume_pi, Measure.restrict_pi_pi]

theorem core_box (e : OrthonormalBasis (Fin n) ℝ E) (a b : Fin n → ℝ) (j : Fin n)
    {K : ℝ → ℝ → ℝ≥0∞} (hK : Measurable (Function.uncurry K))
    {G : E → ℝ≥0∞} (hG : Measurable G) {B' : ℝ≥0∞}
    (hB : ∀ᵐ τ ∂(volume.restrict (Set.Ioo (a j) (b j))),
      ∫⁻ s in Set.Ioo (a j) (b j), K s τ ≤ B') :
    ∫⁻ x in box e a b, ∫⁻ τ in Set.Ioo (a j) (b j), K ⟪e j, x⟫ τ * G (x + (τ - ⟪e j, x⟫) • e j) ≤
      B' * ∫⁻ x in box e a b, G x := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := j.pos; omega⟩
  set c := coordEquiv e with hc
  have h1 : ∀ x, ∫⁻ τ in Set.Ioo (a j) (b j), K ⟪e j, x⟫ τ * G (x + (τ - ⟪e j, x⟫) • e j) =
      (fun y => ∫⁻ τ in Set.Ioo (a j) (b j), K (y j) τ *
        (G ∘ c.symm) (Function.update y j τ)) (c x) := by
    intro x
    simp only [Function.comp, ← coordEquiv_update, MeasurableEquiv.symm_apply_apply, hc,
      coordEquiv_apply]
  have h2 : ∀ x, G x = (G ∘ c.symm) (c x) := fun x => by simp
  simp_rw [h1]
  rw [lintegral_box_coord e a b (fun y => ∫⁻ τ in Set.Ioo (a j) (b j), K (y j) τ *
        (G ∘ c.symm) (Function.update y j τ))]
  conv_rhs => rw [show (∫⁻ x in box e a b, G x) = ∫⁻ x in box e a b, (G ∘ c.symm) (c x) from
    lintegral_congr h2, lintegral_box_coord e a b (G ∘ c.symm)]
  exact core_coord (fun i => volume.restrict (Set.Ioo (a i) (b i))) j hK
    (hG.comp c.symm.measurable) hB

/-- The operator with kernel `k` acting in coordinate `j`. -/
noncomputable def coordOp (e : OrthonormalBasis (Fin n) ℝ E) (a b : Fin n → ℝ) (j : Fin n)
    (k : ℝ → ℝ → ℝ) (F : E → ℝ) (x : E) : ℝ :=
  ∫ τ in Set.Ioo (a j) (b j), k ⟪e j, x⟫ τ * F (x + (τ - ⟪e j, x⟫) • e j)

theorem measurable_coordOp (e : OrthonormalBasis (Fin n) ℝ E) (a b : Fin n → ℝ) (j : Fin n)
    {k : ℝ → ℝ → ℝ} (hk : Measurable (Function.uncurry k)) {F : E → ℝ} (hF : Measurable F) :
    Measurable (coordOp e a b j k F) := by
  unfold coordOp
  have hin : Measurable (fun x : E => ⟪e j, x⟫) :=
    (continuous_const.inner continuous_id).measurable
  have hf : Measurable (fun q : E × ℝ =>
      k ⟪e j, q.1⟫ q.2 * F (q.1 + (q.2 - ⟪e j, q.1⟫) • e j)) := by
    refine Measurable.mul ?_ ?_
    · exact hk.comp (f := fun q : E × ℝ => (⟪e j, q.1⟫, q.2))
        ((hin.comp measurable_fst).prodMk measurable_snd)
    · refine hF.comp ?_
      refine measurable_fst.add (Measurable.smul ?_ measurable_const)
      exact measurable_snd.sub (hin.comp measurable_fst)
  exact (hf.stronglyMeasurable.integral_prod_right' (ν := volume.restrict _)).measurable

theorem sq_lintegral_le {α : Type*} [MeasurableSpace α] (μ : Measure α) {K φ : α → ℝ≥0∞}
    (hK : Measurable K) (hφ : Measurable φ) :
    (∫⁻ x, K x * φ x ∂μ) ^ 2 ≤ (∫⁻ x, K x ∂μ) * ∫⁻ x, K x * φ x ^ 2 ∂μ := by
  have h1 : ∫⁻ x, K x * φ x ∂μ = ∫⁻ x, φ x ∂(μ.withDensity K) :=
    (lintegral_withDensity_eq_lintegral_mul _ hK hφ).symm
  have h2 : ∫⁻ x, K x * φ x ^ 2 ∂μ = ∫⁻ x, φ x ^ 2 ∂(μ.withDensity K) :=
    (lintegral_withDensity_eq_lintegral_mul _ hK (hφ.pow_const 2)).symm
  have h3 : ∫⁻ x, K x ∂μ = (μ.withDensity K) Set.univ := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [h1, h2, h3]
  set ν := μ.withDensity K
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two
    (f := fun _ => (1 : ℝ≥0∞)) (g := φ) aemeasurable_const hφ.aemeasurable
  have h' : ∫⁻ x, φ x ∂ν ≤ (ν Set.univ) ^ (1 / 2 : ℝ) * (∫⁻ x, φ x ^ 2 ∂ν) ^ (1 / 2 : ℝ) := by
    simpa [ENNReal.rpow_two] using h
  calc (∫⁻ x, φ x ∂ν) ^ 2 ≤ ((ν Set.univ) ^ (1 / 2 : ℝ) * (∫⁻ x, φ x ^ 2 ∂ν) ^ (1 / 2 : ℝ)) ^ 2 := by
        gcongr
    _ = _ := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast (_ ^ _), ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul]
        norm_num

/-- **Schur's test in one coordinate.** -/
theorem coordOp_sq_le (e : OrthonormalBasis (Fin n) ℝ E) {a b : Fin n → ℝ}
    (hab : ∀ i, a i < b i) (j : Fin n) {k : ℝ → ℝ → ℝ} (hk : Measurable (Function.uncurry k))
    {A B : ℝ} (hA : ∀ s, ∫ τ in Set.Ioo (a j) (b j), |k s τ| ≤ A)
    (hB : ∀ τ, ∫ s in Set.Ioo (a j) (b j), |k s τ| ≤ B)
    (hkA : ∀ s, IntegrableOn (fun τ => k s τ) (Set.Ioo (a j) (b j)))
    {F : E → ℝ} (hF : Measurable F) (hF2 : IntegrableOn (fun x => F x ^ 2) (box e a b)) :
    IntegrableOn (fun x => coordOp e a b j k F x ^ 2) (box e a b) ∧
      ∫ x in box e a b, coordOp e a b j k F x ^ 2 ≤ A * B * ∫ x in box e a b, F x ^ 2 := by
  set I := Set.Ioo (a j) (b j) with hI
  have hIlt : volume I < ⊤ := by simp [hI]
  set K : ℝ → ℝ → ℝ≥0∞ := fun s τ => ‖k s τ‖ₑ with hKdef
  have hKm : Measurable (Function.uncurry K) := hk.enorm
  have hA0 : 0 ≤ A := le_trans (integral_nonneg fun _ => abs_nonneg _) (hA 0)
  have hB0 : 0 ≤ B := le_trans (integral_nonneg fun _ => abs_nonneg _) (hB 0)
  have hKA : ∀ s, ∫⁻ τ in I, K s τ ≤ ENNReal.ofReal A := fun s => by
    have h := ofReal_integral_norm_eq_lintegral_enorm (hkA s)
    refine le_trans (le_of_eq h.symm) (ENNReal.ofReal_le_ofReal ?_)
    simpa [Real.norm_eq_abs] using hA s
  have hKB : ∀ᵐ τ ∂(volume.restrict I), ∫⁻ s in I, K s τ ≤ ENNReal.ofReal B := by
    have hfin : ∫⁻ τ in I, ∫⁻ s in I, K s τ < ⊤ := by
      have hm : AEMeasurable (Function.uncurry fun τ s => K s τ)
          ((volume.restrict I).prod (volume.restrict I)) :=
        (hKm.comp measurable_swap).aemeasurable
      rw [lintegral_lintegral_swap hm]
      calc _ ≤ ∫⁻ s in I, ENNReal.ofReal A := lintegral_mono hKA
        _ < ⊤ := by simpa using ENNReal.mul_lt_top ENNReal.ofReal_lt_top hIlt
    have hmeas : Measurable (fun τ => ∫⁻ s in I, K s τ) := hKm.lintegral_prod_left'
    filter_upwards [ae_lt_top hmeas hfin.ne] with τ hτ
    have hint : Integrable (fun s => k s τ) (volume.restrict I) :=
      ⟨(hk.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable,
        hasFiniteIntegral_iff_enorm.2 hτ⟩
    refine le_trans (le_of_eq (ofReal_integral_norm_eq_lintegral_enorm hint).symm)
      (ENNReal.ofReal_le_ofReal ?_)
    simpa [Real.norm_eq_abs] using hB τ
  have hFe : Measurable (fun x => ‖F x‖ₑ ^ 2) := hF.enorm.pow_const 2
  have hpt : ∀ x, ‖coordOp e a b j k F x‖ₑ ^ 2 ≤ ENNReal.ofReal A *
      ∫⁻ τ in I, K ⟪e j, x⟫ τ * (‖F (x + (τ - ⟪e j, x⟫) • e j)‖ₑ ^ 2) := by
    intro x
    have hin : Measurable (fun x : E => ⟪e j, x⟫) :=
      (continuous_const.inner continuous_id).measurable
    have hφ : Measurable (fun τ : ℝ => ‖F (x + (τ - ⟪e j, x⟫) • e j)‖ₑ) := by
      refine hF.enorm.comp ?_
      exact measurable_const.add (Measurable.smul (measurable_id.sub measurable_const)
        measurable_const)
    have hKs : Measurable (fun τ => K ⟪e j, x⟫ τ) :=
      hKm.comp (measurable_const.prodMk measurable_id)
    calc ‖coordOp e a b j k F x‖ₑ ^ 2
        ≤ (∫⁻ τ in I, K ⟪e j, x⟫ τ * ‖F (x + (τ - ⟪e j, x⟫) • e j)‖ₑ) ^ 2 := by
          gcongr
          refine (enorm_integral_le_lintegral_enorm (μ := volume.restrict I) _).trans (le_of_eq ?_)
          simp only [hKdef, enorm_mul]
      _ ≤ (∫⁻ τ in I, K ⟪e j, x⟫ τ) *
          ∫⁻ τ in I, K ⟪e j, x⟫ τ * ‖F (x + (τ - ⟪e j, x⟫) • e j)‖ₑ ^ 2 :=
          sq_lintegral_le _ hKs hφ
      _ ≤ _ := by gcongr; exact hKA _
  have hmain : ∫⁻ x in box e a b, ‖coordOp e a b j k F x‖ₑ ^ 2 ≤
      ENNReal.ofReal A * (ENNReal.ofReal B * ∫⁻ x in box e a b, ‖F x‖ₑ ^ 2) := by
    calc _ ≤ ∫⁻ x in box e a b, ENNReal.ofReal A *
          ∫⁻ τ in I, K ⟪e j, x⟫ τ * (‖F (x + (τ - ⟪e j, x⟫) • e j)‖ₑ ^ 2) := lintegral_mono hpt
      _ ≤ _ := by
          have hc := core_box e a b j hKm hFe (B' := ENNReal.ofReal B) hKB
          have hm : Measurable (fun x : E => ∫⁻ τ in I, K ⟪e j, x⟫ τ *
              (‖F (x + (τ - ⟪e j, x⟫) • e j)‖ₑ ^ 2)) := by
            have hin : Measurable (fun x : E => ⟪e j, x⟫) :=
              (continuous_const.inner continuous_id).measurable
            refine Measurable.lintegral_prod_right'
              (f := fun q : E × ℝ => K ⟪e j, q.1⟫ q.2 *
                (‖F (q.1 + (q.2 - ⟪e j, q.1⟫) • e j)‖ₑ ^ 2)) ?_
            exact (hKm.comp (f := fun q : E × ℝ => (⟪e j, q.1⟫, q.2))
                ((hin.comp measurable_fst).prodMk measurable_snd)).mul
              (hFe.comp (f := fun q : E × ℝ => q.1 + (q.2 - ⟪e j, q.1⟫) • e j)
                (measurable_fst.add (Measurable.smul
                (measurable_snd.sub (hin.comp measurable_fst)) measurable_const)))
          rw [lintegral_const_mul _ hm]
          gcongr
  have hFint : ∫⁻ x in box e a b, ‖F x‖ₑ ^ 2 = ENNReal.ofReal (∫ x in box e a b, F x ^ 2) := by
    have h := ofReal_integral_norm_eq_lintegral_enorm hF2
    simp only [Real.norm_of_nonneg (sq_nonneg _), enorm_pow] at h
    exact h.symm
  have hcm : Measurable (coordOp e a b j k F) := measurable_coordOp e a b j hk hF
  have hint : IntegrableOn (fun x => coordOp e a b j k F x ^ 2) (box e a b) := by
    refine ⟨(hcm.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    calc ∫⁻ x in box e a b, ‖coordOp e a b j k F x ^ 2‖ₑ
        = ∫⁻ x in box e a b, ‖coordOp e a b j k F x‖ₑ ^ 2 := by simp only [enorm_pow]
      _ ≤ ENNReal.ofReal A * (ENNReal.ofReal B * ENNReal.ofReal (∫ x in box e a b, F x ^ 2)) :=
          hFint ▸ hmain
      _ < ⊤ := by simp [ENNReal.mul_lt_top]
  refine ⟨hint, ?_⟩
  have h := ofReal_integral_norm_eq_lintegral_enorm hint
  simp only [Real.norm_of_nonneg (sq_nonneg _), enorm_pow] at h
  have h2 : ENNReal.ofReal (∫ x in box e a b, coordOp e a b j k F x ^ 2) ≤
      ENNReal.ofReal (A * B * ∫ x in box e a b, F x ^ 2) := by
    rw [h, ENNReal.ofReal_mul (mul_nonneg hA0 hB0), ENNReal.ofReal_mul hA0, mul_assoc]
    exact hFint ▸ hmain
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (mul_nonneg hA0 hB0)
    (integral_nonneg fun _ => sq_nonneg _))).1 h2

end FEEC
