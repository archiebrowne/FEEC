/-
Schur's test for finite-rank operators on `L²`.
-/
import Mathlib

namespace FEEC

open MeasureTheory

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- Finite Cauchy–Schwarz through a nonnegative quadratic. -/
lemma schur_cs {ι : Type*} [Fintype ι] (p u d v : ι → ℝ) (hp : ∀ m, 0 ≤ p m)
    (h : ∀ m s, 0 ≤ s ^ 2 * u m - 2 * s * d m + v m) :
    (∑ m, p m * d m) ^ 2 ≤ (∑ m, p m * u m) * (∑ m, p m * v m) := by
  have key : ∀ s : ℝ, 0 ≤ (∑ m, p m * u m) * (s * s) + (-2 * ∑ m, p m * d m) * s
      + ∑ m, p m * v m := by
    intro s
    have : (∑ m, p m * u m) * (s * s) + (-2 * ∑ m, p m * d m) * s + ∑ m, p m * v m
        = ∑ m, p m * (s ^ 2 * u m - 2 * s * d m + v m) := by
      have e : ∀ m, p m * (s ^ 2 * u m - 2 * s * d m + v m)
          = (s * s) * (p m * u m) - (2 * s) * (p m * d m) + p m * v m := fun m => by ring
      simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      ring
    rw [this]
    exact Finset.sum_nonneg fun m _ => mul_nonneg (hp m) (h m s)
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith

lemma schur_int {X : Type*} [MeasurableSpace X] {μ : Measure X} {f w : X → ℝ}
    (hf : Integrable f μ) (hfb : ∃ C, ∀ y, |f y| ≤ C) (hw : AEStronglyMeasurable w μ)
    (hw2 : Integrable (fun y => w y ^ 2) μ) :
    Integrable (fun y => |f y| * w y) μ ∧ Integrable (fun y => |f y| * w y ^ 2) μ := by
  obtain ⟨C, hC⟩ := hfb
  have h2 : Integrable (fun y => |f y| * w y ^ 2) μ := by
    have := hw2.bdd_mul (c := C) (f := fun y => |f y|) hf.abs.aestronglyMeasurable
      (by filter_upwards with y; simpa using hC y)
    exact this
  refine ⟨?_, h2⟩
  refine Integrable.mono' (hf.abs.add h2) (hf.abs.aestronglyMeasurable.mul hw) ?_
  filter_upwards with y
  have : |w y| ≤ 1 + w y ^ 2 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (|w y| - 1), sq_abs (w y), abs_nonneg (w y)]
  have h0 := abs_nonneg (f y)
  simp only [Real.norm_eq_abs, abs_mul, abs_abs, Pi.add_apply]
  nlinarith [mul_le_mul_of_nonneg_left this h0]

lemma schur_quad {X : Type*} [MeasurableSpace X] {μ : Measure X} {f w : X → ℝ}
    (hf : Integrable f μ) (hfb : ∃ C, ∀ y, |f y| ≤ C) (hw : AEStronglyMeasurable w μ)
    (hw2 : Integrable (fun y => w y ^ 2) μ) (s : ℝ) :
    0 ≤ s ^ 2 * (∫ y, |f y| ∂μ) - 2 * s * (∫ y, |f y| * w y ∂μ)
      + ∫ y, |f y| * w y ^ 2 ∂μ := by
  obtain ⟨i1, i2⟩ := schur_int hf hfb hw hw2
  have e : ∫ y, |f y| * (w y - s) ^ 2 ∂μ = s ^ 2 * (∫ y, |f y| ∂μ)
      - 2 * s * (∫ y, |f y| * w y ∂μ) + ∫ y, |f y| * w y ^ 2 ∂μ := by
    have : (fun y => |f y| * (w y - s) ^ 2) = fun y =>
        (s ^ 2 * |f y| - 2 * s * (|f y| * w y)) + |f y| * w y ^ 2 := by
      funext y; ring
    have j0 : Integrable (fun y => s ^ 2 * |f y|) μ := hf.abs.const_mul _
    have j1 : Integrable (fun y => 2 * s * (|f y| * w y)) μ := i1.const_mul _
    have j2 : Integrable (fun y => s ^ 2 * |f y| - 2 * s * (|f y| * w y)) μ := j0.sub j1
    rw [this, integral_add j2 i2, integral_sub j0 j1, integral_const_mul,
      integral_const_mul]
  rw [← e]
  exact integral_nonneg fun y => mul_nonneg (abs_nonneg _) (sq_nonneg _)

lemma schur_coeFn_sum {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {ι : Type*} (A : ι → Lp F 2 μ) (c : ι → ℝ) (s : Finset ι) :
    ((∑ m ∈ s, c m • A m : Lp F 2 μ) : X → F) =ᵐ[μ] fun x => ∑ m ∈ s, c m • (A m : X → F) x := by
  induction s using Finset.cons_induction with
  | empty =>
    filter_upwards [Lp.coeFn_zero F 2 μ] with x hx
    simpa using hx
  | cons i s hi ih =>
    simp only [Finset.sum_cons]
    filter_upwards [Lp.coeFn_add (c i • A i) (∑ m ∈ s, c m • A m),
      Lp.coeFn_smul (c i) (A i), ih] with x h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3]
    rfl

lemma schur_norm_sq {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (ω : Lp F 2 μ) : ‖ω‖ ^ 2 = ∫ y, ‖(ω : X → F) y‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

/-- **Schur's test** for the finite-rank operator `ω ↦ ∑ₘ ⟪ω, bₘ β⟫ aₘ α` on `L²(μ; F)`. -/
theorem norm_sum_inner_smul_le {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {ι : Type*} [Fintype ι] (A B : ι → Lp F 2 μ) (a b : ι → X → ℝ) (α β : F)
    (hA : ∀ m, A m =ᵐ[μ] fun x => a m x • α) (hB : ∀ m, B m =ᵐ[μ] fun x => b m x • β)
    (ha : ∀ m, Integrable (a m) μ) (hb : ∀ m, Integrable (b m) μ)
    (hbb : ∀ m, ∃ C, ∀ y, |b m y| ≤ C)
    {M₁ M₂ : ℝ} (h1 : ∀ᵐ x ∂μ, ∑ m, |a m x| * ∫ y, |b m y| ∂μ ≤ M₁)
    (h2 : ∀ᵐ y ∂μ, ∑ m, (∫ x, |a m x| ∂μ) * |b m y| ≤ M₂) (ω : Lp F 2 μ) :
    ‖∑ m, ⟪ω, B m⟫ • A m‖ ^ 2 ≤ ‖α‖ ^ 2 * ‖β‖ ^ 2 * M₁ * M₂ * ‖ω‖ ^ 2 := by
  by_cases hμ : μ = 0
  · have : ω = 0 := by
      subst hμ
      exact Lp.ext (by simp [Filter.EventuallyEq])
    subst this
    simp
  have hM1 : 0 ≤ M₁ := by
    have : (ae μ).NeBot := ae_neBot.2 hμ
    obtain ⟨x, hx⟩ := h1.exists
    exact le_trans (Finset.sum_nonneg fun m _ => mul_nonneg (abs_nonneg _)
      (integral_nonneg fun _ => abs_nonneg _)) hx
  set w : X → ℝ := fun y => ‖(ω : X → F) y‖ with hwdef
  have hwm : AEStronglyMeasurable w μ := (Lp.memLp ω).norm.aestronglyMeasurable
  have hw2 : Integrable (fun y => w y ^ 2) μ := (Lp.memLp ω).norm.integrable_sq
  have hwint : ∫ y, w y ^ 2 ∂μ = ‖ω‖ ^ 2 := (schur_norm_sq ω).symm
  -- notation
  set u : ι → ℝ := fun m => ∫ y, |b m y| ∂μ with hu
  set d : ι → ℝ := fun m => ∫ y, |b m y| * w y ∂μ with hd
  set v : ι → ℝ := fun m => ∫ y, |b m y| * w y ^ 2 ∂μ with hv
  set c : ι → ℝ := fun m => ⟪ω, B m⟫ with hc
  have hcb : ∀ m, |c m| ≤ ‖β‖ * d m := by
    intro m
    have hi := (schur_int (hb m) (hbb m) hwm hw2).1
    have e : c m = ∫ y, ⟪(ω : X → F) y, b m y • β⟫ ∂μ := by
      simp only [hc]
      rw [L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hB m] with y hy
      rw [hy]
    have := norm_integral_le_of_norm_le (hi.const_mul ‖β‖) (f := fun y => ⟪(ω : X → F) y, b m y • β⟫)
      (by
        filter_upwards with y
        calc ‖⟪(ω : X → F) y, b m y • β⟫‖ ≤ ‖(ω : X → F) y‖ * ‖b m y • β‖ := norm_inner_le_norm _ _
          _ = ‖β‖ * (|b m y| * w y) := by
            rw [norm_smul, Real.norm_eq_abs]; simp only [hwdef]; ring)
    rw [e, ← Real.norm_eq_abs]
    refine this.trans ?_
    rw [integral_const_mul]
  have hq : ∀ m s, 0 ≤ s ^ 2 * u m - 2 * s * d m + v m :=
    fun m s => schur_quad (hb m) (hbb m) hwm hw2 s
  -- the sum
  set S : X → ℝ := fun x => ∑ m, c m * a m x with hS
  have hG : ((∑ m, c m • A m : Lp F 2 μ) : X → F) =ᵐ[μ] fun x => S x • α := by
    have hall : ∀ᵐ x ∂μ, ∀ m, (A m : X → F) x = a m x • α := ae_all_iff.2 hA
    filter_upwards [schur_coeFn_sum A c Finset.univ, hall] with x h3 h4
    rw [h3]
    simp only [hS, Finset.sum_smul, smul_smul, h4]
  have hGn : ‖∑ m, c m • A m‖ ^ 2 = ‖α‖ ^ 2 * ∫ x, S x ^ 2 ∂μ := by
    rw [schur_norm_sq, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hG] with x hx
    rw [hx, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]; ring
  show ‖∑ m, c m • A m‖ ^ 2 ≤ _
  rw [hGn]
  by_cases hα : α = 0
  · subst hα; simp
  -- integrability of S²
  have hSi : Integrable (fun x => S x ^ 2) μ := by
    have hnorm : Integrable (fun x => ‖(∑ m, c m • A m : Lp F 2 μ) x‖ ^ 2) μ :=
      (Lp.memLp _).norm.integrable_sq
    have := hnorm.div_const (‖α‖ ^ 2)
    refine this.congr ?_
    filter_upwards [hG] with x hx
    have hn : ‖α‖ ≠ 0 := norm_ne_zero_iff.2 hα
    rw [hx, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    field_simp
  -- pointwise bound
  set T : X → ℝ := fun x => ∑ m, |a m x| * v m with hT
  have hTi : Integrable T μ := by
    refine integrable_finsetSum _ fun m _ => ?_
    exact (ha m).abs.mul_const _
  have hpt : ∀ᵐ x ∂μ, S x ^ 2 ≤ ‖β‖ ^ 2 * M₁ * T x := by
    filter_upwards [h1] with x hx
    have hS1 : |S x| ≤ ‖β‖ * ∑ m, |a m x| * d m := by
      calc |S x| ≤ ∑ m, |c m * a m x| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ m, ‖β‖ * (|a m x| * d m) := by
          refine Finset.sum_le_sum fun m _ => ?_
          rw [abs_mul]
          calc |c m| * |a m x| ≤ (‖β‖ * d m) * |a m x| :=
                mul_le_mul_of_nonneg_right (hcb m) (abs_nonneg _)
            _ = _ := by ring
        _ = _ := by rw [Finset.mul_sum]
    have hcs := schur_cs (fun m => |a m x|) u d v (fun m => abs_nonneg _) hq
    have hTn : 0 ≤ T x := Finset.sum_nonneg fun m _ => mul_nonneg (abs_nonneg _)
      (integral_nonneg fun y => mul_nonneg (abs_nonneg _) (sq_nonneg _))
    calc S x ^ 2 = |S x| ^ 2 := (sq_abs _).symm
      _ ≤ (‖β‖ * ∑ m, |a m x| * d m) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hS1 2
      _ = ‖β‖ ^ 2 * (∑ m, |a m x| * d m) ^ 2 := by ring
      _ ≤ ‖β‖ ^ 2 * ((∑ m, |a m x| * u m) * T x) :=
          mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
      _ ≤ ‖β‖ ^ 2 * (M₁ * T x) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hx hTn) (sq_nonneg _)
      _ = _ := by ring
  have hint1 : ∫ x, S x ^ 2 ∂μ ≤ ‖β‖ ^ 2 * M₁ * ∫ x, T x ∂μ := by
    rw [← integral_const_mul]
    exact integral_mono_ae hSi (hTi.const_mul _) hpt
  have hint2 : ∫ x, T x ∂μ ≤ M₂ * ‖ω‖ ^ 2 := by
    have e : ∫ x, T x ∂μ = ∫ y, (∑ m, (∫ x, |a m x| ∂μ) * |b m y|) * w y ^ 2 ∂μ := by
      simp only [hT]
      rw [integral_finsetSum _ (fun m _ => (ha m).abs.mul_const _)]
      have : ∀ m, ∫ x, |a m x| * v m ∂μ = ∫ y, (∫ x, |a m x| ∂μ) * (|b m y| * w y ^ 2) ∂μ := by
        intro m
        rw [integral_mul_const, integral_const_mul]
      rw [Finset.sum_congr rfl fun m _ => this m, ← integral_finsetSum]
      · refine integral_congr_ae ?_
        filter_upwards with y
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun m _ => by ring
      · intro m _
        exact ((schur_int (hb m) (hbb m) hwm hw2).2).const_mul _
    rw [e, ← hwint, ← integral_const_mul]
    refine integral_mono_ae ?_ (hw2.const_mul _) ?_
    · have : ∀ m, Integrable (fun y => (∫ x, |a m x| ∂μ) * (|b m y| * w y ^ 2)) μ :=
        fun m => ((schur_int (hb m) (hbb m) hwm hw2).2).const_mul _
      have := integrable_finsetSum _ (fun m (_ : m ∈ Finset.univ) => this m)
      refine this.congr ?_
      filter_upwards with y
      simp only [Finset.sum_mul]
      exact Finset.sum_congr rfl fun m _ => by ring
    · filter_upwards [h2] with y hy
      exact mul_le_mul_of_nonneg_right hy (sq_nonneg _)
  have hfin : ∫ x, S x ^ 2 ∂μ ≤ ‖β‖ ^ 2 * M₁ * (M₂ * ‖ω‖ ^ 2) :=
    hint1.trans (mul_le_mul_of_nonneg_left hint2 (mul_nonneg (sq_nonneg _) hM1))
  calc ‖α‖ ^ 2 * ∫ x, S x ^ 2 ∂μ ≤ ‖α‖ ^ 2 * (‖β‖ ^ 2 * M₁ * (M₂ * ‖ω‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hfin (sq_nonneg _)
    _ = _ := by ring

end FEEC
