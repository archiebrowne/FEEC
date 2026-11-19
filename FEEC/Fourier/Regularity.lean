/-
Regularity of the Hodge Laplacian on a box, in Fourier coefficients.
-/
import FEEC.Fourier.EigenDeriv
import FEEC.Fourier.Parseval
import FEEC.DeRham.PoincareLemma

/-!
# Regularity on a box

For the solution `(σ, u, p)` of the Hodge Laplace problem on a box at level `k + 1`:
`p = 0`, `σ̂(m) = ξ_m ⌟ û(m)` and `|ξ_m|² û(m) = f̂(m)`. Consequently the Fourier
`H¹`-seminorms `Nsq` of `σ`, `dσ`, `u`, `du` are bounded by `‖f‖² + Nsq f`.
-/

namespace FEEC

namespace Fourier

open MeasureTheory Tensor

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {n : ℕ}
  {e : OrthonormalBasis (Fin n) ℝ E} {a b : Fin n → ℝ} {k : ℕ}

variable (e a b) in
/-- The terms of the Fourier `H¹`-seminorm. -/
noncomputable def nTerm (w : L2Form (box e a b) k) (m : Fin n → ℕ) : ℝ :=
  normProd a b m * ‖xi e a b m‖ ^ 2 * ‖coef e a b w m‖ ^ 2

variable (e a b) in
/-- The squared Fourier `H¹`-seminorm. -/
noncomputable def Nsq (w : L2Form (box e a b) k) : ℝ := ∑' m, nTerm e a b w m

theorem coef_sigma (hab : ∀ i, a i < b i) {f : L2Form (box e a b) (k + 1)}
    {σ : HΛ (box e a b) k} {u p : HΛ (box e a b) (k + 1)}
    (h : ((deRhamComplex (isOpen_box e a b)).segment k).IsSolution f σ u p) (m : Fin n → ℕ) :
    coef e a b (HΛ.toL2 σ) m = ccontr (xi e a b m) (coef e a b (HΛ.toL2 u) m) := by
  have hN := normProd_pos hab m
  refine ext_inner_right ℝ fun α => ?_
  have h0 := h.eq₀ (synthH e a b hab m α)
  have e1 : ⟪HΛ.toL2 σ, synth e a b m α⟫ = normProd a b m * ⟪coef e a b (HΛ.toL2 σ) m, α⟫ :=
    inner_synth hab _ m α
  have e2 : ⟪synth e a b m (cwedge (xi e a b m) α), HΛ.toL2 u⟫ =
      normProd a b m * ⟪coef e a b (HΛ.toL2 u) m, cwedge (xi e a b m) α⟫ := by
    rw [real_inner_comm, inner_synth hab]
  have h0' : ⟪HΛ.toL2 σ, synth e a b m α⟫ -
      ⟪synth e a b m (cwedge (xi e a b m) α), HΛ.toL2 u⟫ = 0 := h0
  have e3 : ⟪coef e a b (HΛ.toL2 u) m, cwedge (xi e a b m) α⟫ =
      ⟪ccontr (xi e a b m) (coef e a b (HΛ.toL2 u) m), α⟫ := by
    rw [real_inner_comm, inner_cwedge, real_inner_comm]
  rw [e1, e2, e3] at h0'
  have : normProd a b m * (⟪coef e a b (HΛ.toL2 σ) m, α⟫ -
      ⟪ccontr (xi e a b m) (coef e a b (HΛ.toL2 u) m), α⟫) = 0 := by linarith
  rcases mul_eq_zero.1 this with h1 | h1
  · exact absurd h1 hN.ne'
  · linarith

theorem coef_u (hab : ∀ i, a i < b i) {f : L2Form (box e a b) (k + 1)}
    {σ : HΛ (box e a b) k} {u p : HΛ (box e a b) (k + 1)}
    (h : ((deRhamComplex (isOpen_box e a b)).segment k).IsSolution f σ u p) (m : Fin n → ℕ) :
    (‖xi e a b m‖ ^ 2) • coef e a b (HΛ.toL2 u) m = coef e a b f m := by
  have hN := normProd_pos hab m
  have hp : p = 0 := by
    have := h.harmonic
    rw [box_harmonic_eq_bot e hab k] at this
    exact (Submodule.mem_bot ℝ).1 this
  have hσ := coef_sigma hab h m
  have key : coef e a b f m = cwedge (xi e a b m) (coef e a b (HΛ.toL2 σ) m) +
      ccontr (xi e a b m) (cwedge (xi e a b m) (coef e a b (HΛ.toL2 u) m)) := by
    refine ext_inner_right ℝ fun β => ?_
    have h1 := h.eq₁ (synthH e a b hab m β)
    have e1 : ⟪HΛ.toL2 (HΛ.d σ), synth e a b m β⟫ =
        normProd a b m * ⟪cwedge (xi e a b m) (coef e a b (HΛ.toL2 σ) m), β⟫ := by
      rw [← coef_d hab]; exact inner_synth hab _ m β
    have e2 : ⟪HΛ.toL2 (HΛ.d u), synth e a b m (cwedge (xi e a b m) β)⟫ =
        normProd a b m * ⟪ccontr (xi e a b m) (cwedge (xi e a b m) (coef e a b (HΛ.toL2 u) m)), β⟫ := by
      rw [inner_synth hab, coef_d hab]
      congr 1
      rw [real_inner_comm, inner_cwedge, real_inner_comm]
    have e3 : ⟪f, synth e a b m β⟫ = normProd a b m * ⟪coef e a b f m, β⟫ := inner_synth hab _ m β
    have h1' : ⟪HΛ.toL2 (HΛ.d σ), synth e a b m β⟫ +
        ⟪HΛ.toL2 (HΛ.d u), synth e a b m (cwedge (xi e a b m) β)⟫ +
        ⟪HΛ.toL2 p, synth e a b m β⟫ = ⟪f, synth e a b m β⟫ := h1
    rw [hp] at h1'
    have z : HΛ.toL2 (0 : HΛ (box e a b) (k + 1)) = 0 := rfl
    rw [z, inner_zero_left, add_zero, e1, e2, e3, ← mul_add] at h1'
    rw [inner_add_left]
    exact (mul_left_cancel₀ hN.ne' h1').symm
  have := ccontr_cwedge_add (xi e a b m) (coef e a b (HΛ.toL2 u) m)
  rw [key]
  simp only [hσ]
  exact ((add_comm _ _).trans this).symm

theorem aux_bounds {x s t t' r φ c : ℝ} (hx : 0 ≤ x) (hs : 0 ≤ s) (ht : 0 ≤ t) (ht' : 0 ≤ t')
    (hr : 0 ≤ r) (hφ : φ = x ^ 2 * r) (hc : 0 < c) (hxc : c ≤ x ∨ r = 0)
    (h1 : s ≤ x * r) (h2 : t ≤ x * s) (h3 : t' ≤ x * r) :
    x ^ 2 * s ^ 2 ≤ φ ^ 2 ∧ x ^ 2 * t ^ 2 ≤ x ^ 2 * φ ^ 2 ∧ x ^ 2 * r ^ 2 ≤ (1 / c ^ 2) * φ ^ 2 ∧
      x ^ 2 * t' ^ 2 ≤ φ ^ 2 := by
  have e1 : s ^ 2 ≤ (x * r) ^ 2 := pow_le_pow_left₀ hs h1 2
  have e3 : t' ^ 2 ≤ (x * r) ^ 2 := pow_le_pow_left₀ ht' h3 2
  have e2 : t ^ 2 ≤ (x * s) ^ 2 := pow_le_pow_left₀ ht h2 2
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc x ^ 2 * s ^ 2 ≤ x ^ 2 * (x * r) ^ 2 := mul_le_mul_of_nonneg_left e1 hx2
      _ = φ ^ 2 := by rw [hφ]; ring
  · have : x ^ 2 * t ^ 2 ≤ x ^ 2 * (x * s) ^ 2 := mul_le_mul_of_nonneg_left e2 hx2
    have h4 : x ^ 2 * (x * s) ^ 2 ≤ x ^ 2 * (x ^ 2 * (x * r) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hx2
      calc (x * s) ^ 2 = x ^ 2 * s ^ 2 := by ring
        _ ≤ x ^ 2 * (x * r) ^ 2 := mul_le_mul_of_nonneg_left e1 hx2
    calc x ^ 2 * t ^ 2 ≤ _ := this.trans h4
      _ = x ^ 2 * φ ^ 2 := by rw [hφ]; ring
  · rcases hxc with hxc | hr0
    · have hxpos : 0 < x := hc.trans_le hxc
      have : c ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hc.le hxc 2
      have hc2 : 0 < c ^ 2 := by positivity
      rw [hφ, one_div, inv_mul_eq_div, le_div_iff₀ hc2]
      have : x ^ 2 * r ^ 2 * c ^ 2 ≤ x ^ 2 * r ^ 2 * x ^ 2 :=
        mul_le_mul_of_nonneg_left this (by positivity)
      calc x ^ 2 * r ^ 2 * c ^ 2 ≤ x ^ 2 * r ^ 2 * x ^ 2 := this
        _ = (x ^ 2 * r) ^ 2 := by ring
    · subst hr0; simp [hφ]
  · calc x ^ 2 * t' ^ 2 ≤ x ^ 2 * (x * r) ^ 2 := mul_le_mul_of_nonneg_left e3 hx2
      _ = φ ^ 2 := by rw [hφ]; ring

/-- **Regularity estimate.** -/
theorem exists_regularity (hab : ∀ i, a i < b i) (k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (f : L2Form (box e a b) (k + 1)) (σ : HΛ (box e a b) k) (u p : HΛ (box e a b) (k + 1)),
      ((deRhamComplex (isOpen_box e a b)).segment k).IsSolution f σ u p →
      Summable (nTerm e a b f) →
      Summable (nTerm e a b (HΛ.toL2 σ)) ∧ Summable (nTerm e a b (HΛ.toL2 (HΛ.d σ))) ∧
      Summable (nTerm e a b (HΛ.toL2 u)) ∧ Summable (nTerm e a b (HΛ.toL2 (HΛ.d u))) ∧
      Nsq e a b (HΛ.toL2 σ) + Nsq e a b (HΛ.toL2 (HΛ.d σ)) + Nsq e a b (HΛ.toL2 u) +
        Nsq e a b (HΛ.toL2 (HΛ.d u)) ≤ C * (‖f‖ ^ 2 + Nsq e a b f) := by
  obtain ⟨c, hc, hxi⟩ := exists_norm_xi_ge (e := e) (a := a) (b := b) hab
  refine ⟨3 + 1 / c ^ 2, by positivity, ?_⟩
  intro f σ u p h hf
  have hN := normProd_pos hab
  have hP := hasSum_norm_sq_coef (e := e) hab f
  set F : (Fin n → ℕ) → ℝ := fun m => normProd a b m * ‖coef e a b f m‖ ^ 2 with hF
  have hFs : Summable F := hP.summable
  have pt : ∀ m, nTerm e a b (HΛ.toL2 σ) m ≤ F m ∧
      nTerm e a b (HΛ.toL2 (HΛ.d σ)) m ≤ nTerm e a b f m ∧
      nTerm e a b (HΛ.toL2 u) m ≤ (1 / c ^ 2) * F m ∧
      nTerm e a b (HΛ.toL2 (HΛ.d u)) m ≤ F m := by
    intro m
    have hu := coef_u hab h m
    have hσ := coef_sigma hab h m
    have hxc : c ≤ ‖xi e a b m‖ ∨ ‖coef e a b (HΛ.toL2 u) m‖ = 0 := by
      by_cases hm : m = 0
      · right; subst hm; rw [coef_zero_freq hab]; simp
      · left; exact hxi m hm
    have hφ : ‖coef e a b f m‖ = ‖xi e a b m‖ ^ 2 * ‖coef e a b (HΛ.toL2 u) m‖ := by
      rw [← hu, norm_smul]; simp
    obtain ⟨b1, b2, b3, b4⟩ := aux_bounds (norm_nonneg _) (norm_nonneg (coef e a b (HΛ.toL2 σ) m))
      (norm_nonneg (coef e a b (HΛ.toL2 (HΛ.d σ)) m)) (norm_nonneg (coef e a b (HΛ.toL2 (HΛ.d u)) m))
      (norm_nonneg (coef e a b (HΛ.toL2 u) m)) hφ hc hxc
      (by rw [hσ]; exact norm_ccontr_le _ _)
      (by rw [coef_d hab]; exact norm_cwedge_le _ _)
      (by rw [coef_d hab]; exact norm_cwedge_le _ _)
    have hNm := hN m
    refine ⟨?_, ?_, ?_, ?_⟩
    · unfold nTerm; simp only [hF]
      calc _ = normProd a b m * (‖xi e a b m‖ ^ 2 * ‖coef e a b (HΛ.toL2 σ) m‖ ^ 2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left b1 hNm.le
    · unfold nTerm
      calc _ = normProd a b m * (‖xi e a b m‖ ^ 2 * ‖coef e a b (HΛ.toL2 (HΛ.d σ)) m‖ ^ 2) := by
            ring
        _ ≤ normProd a b m * (‖xi e a b m‖ ^ 2 * ‖coef e a b f m‖ ^ 2) :=
            mul_le_mul_of_nonneg_left b2 hNm.le
        _ = _ := by ring
    · unfold nTerm; simp only [hF]
      calc _ = normProd a b m * (‖xi e a b m‖ ^ 2 * ‖coef e a b (HΛ.toL2 u) m‖ ^ 2) := by ring
        _ ≤ normProd a b m * ((1 / c ^ 2) * ‖coef e a b f m‖ ^ 2) :=
            mul_le_mul_of_nonneg_left b3 hNm.le
        _ = _ := by ring
    · unfold nTerm; simp only [hF]
      calc _ = normProd a b m * (‖xi e a b m‖ ^ 2 * ‖coef e a b (HΛ.toL2 (HΛ.d u)) m‖ ^ 2) := by
            ring
        _ ≤ _ := mul_le_mul_of_nonneg_left b4 hNm.le
  have nn : ∀ (w : L2Form (box e a b) (k + 1)) m, 0 ≤ nTerm e a b w m := fun w m => by
    unfold nTerm; have := hN m; positivity
  have nn' : ∀ (w : L2Form (box e a b) k) m, 0 ≤ nTerm e a b w m := fun w m => by
    unfold nTerm; have := hN m; positivity
  have nn'' : ∀ (w : L2Form (box e a b) (k + 2)) m, 0 ≤ nTerm e a b w m := fun w m => by
    unfold nTerm; have := hN m; positivity
  have s1 : Summable (nTerm e a b (HΛ.toL2 σ)) :=
    Summable.of_nonneg_of_le (nn' _) (fun m => (pt m).1) hFs
  have s2 : Summable (nTerm e a b (HΛ.toL2 (HΛ.d σ))) :=
    Summable.of_nonneg_of_le (nn _) (fun m => (pt m).2.1) hf
  have s3 : Summable (nTerm e a b (HΛ.toL2 u)) :=
    Summable.of_nonneg_of_le (nn _) (fun m => (pt m).2.2.1) (hFs.mul_left _)
  have s4 : Summable (nTerm e a b (HΛ.toL2 (HΛ.d u))) :=
    Summable.of_nonneg_of_le (nn'' _) (fun m => (pt m).2.2.2) hFs
  refine ⟨s1, s2, s3, s4, ?_⟩
  have t1 : Nsq e a b (HΛ.toL2 σ) ≤ ‖f‖ ^ 2 := by
    rw [← hP.tsum_eq]; exact Summable.tsum_le_tsum (fun m => (pt m).1) s1 hFs
  have t2 : Nsq e a b (HΛ.toL2 (HΛ.d σ)) ≤ Nsq e a b f :=
    Summable.tsum_le_tsum (fun m => (pt m).2.1) s2 hf
  have t3 : Nsq e a b (HΛ.toL2 u) ≤ (1 / c ^ 2) * ‖f‖ ^ 2 := by
    rw [← hP.tsum_eq, ← tsum_mul_left]
    exact Summable.tsum_le_tsum (fun m => (pt m).2.2.1) s3 (hFs.mul_left _)
  have t4 : Nsq e a b (HΛ.toL2 (HΛ.d u)) ≤ ‖f‖ ^ 2 := by
    rw [← hP.tsum_eq]; exact Summable.tsum_le_tsum (fun m => (pt m).2.2.2) s4 hFs
  have t5 : 0 ≤ Nsq e a b f := tsum_nonneg (nn f)
  have hc2 : 0 ≤ 1 / c ^ 2 := by positivity
  nlinarith [sq_nonneg ‖f‖]

end Fourier

end FEEC
