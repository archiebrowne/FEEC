/-
The L² de Rham complex as a Hilbert complex.
-/
import FEEC.DeRham.Codifferential
import FEEC.Hilbert.Complex

/-!
# The `L²` de Rham complex

Let `Ω` be an open subset of a Euclidean space `E`. Following Arnold, §6.2:

* `L2Form Ω k = L²(Ω; Λᵏ)` is the Hilbert space of square integrable `k`-forms on `Ω`;
* `η ∈ L²Λᵏ⁺¹` is the *weak exterior derivative* of `ω ∈ L²Λᵏ` if
  `∫_Ω ⟪η, φ⟫ = ∫_Ω ⟪ω, δφ⟫` for all test forms `φ ∈ C_c^∞(Ω; Λᵏ⁺¹)` (`HasWeakExtDeriv`);
* `HΛ Ω k` is the space of `ω ∈ L²Λᵏ` having a weak exterior derivative in `L²Λᵏ⁺¹`, realised
  as the graph `{(ω, dω)}`, a closed subspace of `L²Λᵏ × L²Λᵏ⁺¹`. Its norm is therefore the
  graph norm, and it is a Hilbert space.

## Main results

* `FEEC.HasWeakExtDeriv.unique`: weak exterior derivatives are unique.
* `FEEC.deRhamComplex Ω : HilbertComplex (L2Form Ω) (HΛ Ω)`: **the `L²` de Rham complex
  `0 → HΛ⁰(Ω) → HΛ¹(Ω) → ⋯` is a Hilbert complex.**

Consequently the abstract theory (Hodge decomposition, well-posedness of the Hodge Laplacian,
stability and convergence of Galerkin methods with bounded cochain projections) applies to it
as soon as it is closed. Closedness holds for bounded Lipschitz domains; that is not proved
here.
-/

namespace FEEC

open Module MeasureTheory

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- `L²(Ω; Λᵏ)`: square integrable differential `k`-forms on `Ω`. -/
abbrev L2Form (Ω : Set E) (k : ℕ) : Type _ := Lp (Covector E k) 2 (volume.restrict Ω)

variable {Ω : Set E} {k : ℕ}

/-- `η` is the weak exterior derivative of `ω` on `Ω`: `⟪η, φ⟫ = ⟪ω, δφ⟫` in `L²(Ω)` for all
test forms `φ`. -/
def HasWeakExtDeriv (ω : L2Form Ω k) (η : L2Form Ω (k + 1)) : Prop :=
  ∀ (φ : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ) (hφ : IsTestForm Ω φ), ⟪η, hφ.toLp⟫ = ⟪ω, hφ.codiff.toLp⟫

namespace HasWeakExtDeriv

theorem zero : HasWeakExtDeriv (0 : L2Form Ω k) 0 := by
  intro φ hφ
  simp

theorem add {ω ω' : L2Form Ω k} {η η' : L2Form Ω (k + 1)} (h : HasWeakExtDeriv ω η)
    (h' : HasWeakExtDeriv ω' η') : HasWeakExtDeriv (ω + ω') (η + η') := by
  intro φ hφ
  rw [inner_add_left, inner_add_left, h φ hφ, h' φ hφ]

theorem smul (c : ℝ) {ω : L2Form Ω k} {η : L2Form Ω (k + 1)} (h : HasWeakExtDeriv ω η) :
    HasWeakExtDeriv (c • ω) (c • η) := by
  intro φ hφ
  rw [real_inner_smul_left, real_inner_smul_left, h φ hφ]

/-- The class of a test form whose function is zero is zero. -/
theorem _root_.FEEC.IsTestForm.toLp_eq_zero {φ : E → E [⋀^Fin k]→L[ℝ] ℝ} (hφ : IsTestForm Ω φ)
    (h0 : φ = 0) : hφ.toLp = 0 := by
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [hφ.coeFn_toLp] with x hx
  rw [hx, h0]
  simp

/-- The weak exterior derivative of a weak exterior derivative is zero: `d ∘ d = 0`. -/
theorem zero_right {ω : L2Form Ω k} {η : L2Form Ω (k + 1)} (h : HasWeakExtDeriv ω η) :
    HasWeakExtDeriv η 0 := by
  intro ψ hψ
  rw [inner_zero_left, h _ hψ.codiff]
  have h2 : codiff (codiff ψ) = 0 := codiff_codiff (hψ.contDiff.of_le (by norm_cast))
  rw [hψ.codiff.codiff.toLp_eq_zero h2, inner_zero_right]

/-- A form which is `L²`-orthogonal to all test forms vanishes (the fundamental lemma of the
calculus of variations). -/
theorem eq_zero_of_forall_inner_toLp_eq_zero (hΩ : IsOpen Ω) {η : L2Form Ω k}
    (h : ∀ (φ : E → E [⋀^Fin k]→L[ℝ] ℝ) (hφ : IsTestForm Ω φ), ⟪η, hφ.toLp⟫ = 0) : η = 0 := by
  have key : ∀ c : Covector E k, ∀ᵐ x ∂(volume.restrict Ω), ⟪η x, c⟫ = 0 := by
    intro c
    have hloc : LocallyIntegrable (fun x => ⟪η x, c⟫) (volume.restrict Ω) := by
      have h1 : LocallyIntegrable (fun x => η x) (volume.restrict Ω) :=
        (Lp.memLp η).locallyIntegrable (by norm_num)
      intro x
      obtain ⟨s, hs, hint⟩ := h1 x
      exact ⟨s, hs, hint.inner_const c⟩
    have hint : ∀ g : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ Ω →
        ∫ x, g x • ⟪η x, c⟫ ∂(volume.restrict Ω) = 0 := by
      intro g hg hgc hgΩ
      have := h _ (IsTestForm.smul_const hg hgc hgΩ c.toAlt)
      rw [L2.inner_def] at this
      rw [← this]
      refine integral_congr_ae ?_
      filter_upwards [(IsTestForm.smul_const hg hgc hgΩ c.toAlt).coeFn_toLp] with x hx
      rw [hx, map_smul, Covector.ofAlt_toAlt, real_inner_smul_right, smul_eq_mul]
    have := hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hloc.locallyIntegrableOn Ω) hint
    filter_upwards [this, ae_restrict_mem hΩ.measurableSet] with x hx hxΩ using hx hxΩ
  have hb := Module.finBasis ℝ (Covector E k)
  have hall : ∀ᵐ x ∂(volume.restrict Ω), ∀ i, ⟪η x, Module.finBasis ℝ (Covector E k) i⟫ = 0 :=
    ae_all_iff.2 fun i => key _
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [hall] with x hx
  have e := ((Module.finBasis ℝ (Covector E k)).sum_repr (η x)).symm
  have : ⟪η x, η x⟫ = 0 := by
    calc ⟪η x, η x⟫ = ⟪η x, ∑ i, (Module.finBasis ℝ (Covector E k)).repr (η x) i •
          Module.finBasis ℝ (Covector E k) i⟫ := by rw [← e]
      _ = 0 := by rw [inner_sum]; simp only [inner_smul_right, hx, mul_zero, Finset.sum_const_zero]
  exact inner_self_eq_zero.1 this

/-- **Uniqueness of the weak exterior derivative.** -/
theorem unique (hΩ : IsOpen Ω) {ω : L2Form Ω k} {η η' : L2Form Ω (k + 1)}
    (h : HasWeakExtDeriv ω η) (h' : HasWeakExtDeriv ω η') : η = η' := by
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_inner_toLp_eq_zero hΩ fun φ hφ => ?_
  rw [inner_sub_left, h φ hφ, h' φ hφ, sub_self]

end HasWeakExtDeriv

theorem withLp_prod_ext {A B : Type*} [NormedAddCommGroup A] [NormedAddCommGroup B]
    {p q : WithLp 2 (A × B)} (h1 : p.fst = q.fst) (h2 : p.snd = q.snd) : p = q :=
  WithLp.ofLp_injective 2 (Prod.ext h1 h2)

variable (Ω k) in
/-- `HΛᵏ(Ω)`: the `L²` forms with weak exterior derivative in `L²`, realised as the graph of
the weak exterior derivative inside `L²Λᵏ × L²Λᵏ⁺¹` (so its norm is the graph norm). -/
def HΛ : Submodule ℝ (WithLp 2 (L2Form Ω k × L2Form Ω (k + 1))) where
  carrier := {p | HasWeakExtDeriv p.fst p.snd}
  add_mem' h h' := h.add h'
  zero_mem' := HasWeakExtDeriv.zero
  smul_mem' c _ h := h.smul c

theorem mem_HΛ {p : WithLp 2 (L2Form Ω k × L2Form Ω (k + 1))} :
    p ∈ HΛ Ω k ↔ HasWeakExtDeriv p.fst p.snd := Iff.rfl

/-- `HΛᵏ(Ω)` is closed in `L²Λᵏ × L²Λᵏ⁺¹`: the weak exterior derivative is a closed operator. -/
theorem isClosed_HΛ : IsClosed (HΛ Ω k : Set (WithLp 2 (L2Form Ω k × L2Form Ω (k + 1)))) := by
  have : (HΛ Ω k : Set (WithLp 2 (L2Form Ω k × L2Form Ω (k + 1)))) =
      ⋂ (φ : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ) (hφ : IsTestForm Ω φ),
        {p | ⟪p.snd, hφ.toLp⟫ = ⟪p.fst, hφ.codiff.toLp⟫} := by
    ext p
    simp [mem_HΛ, HasWeakExtDeriv]
  rw [this]
  refine isClosed_iInter fun φ => isClosed_iInter fun hφ => isClosed_eq ?_ ?_
  · exact ((WithLp.sndL 2 ℝ _ _).continuous.inner continuous_const)
  · exact ((WithLp.fstL 2 ℝ _ _).continuous.inner continuous_const)

instance : CompleteSpace (HΛ Ω k) := isClosed_HΛ.completeSpace_coe

/-- The underlying `L²` form of an element of `HΛᵏ(Ω)`. -/
noncomputable def HΛ.toL2 : HΛ Ω k →L[ℝ] L2Form Ω k :=
  (WithLp.fstL 2 ℝ _ _).comp (HΛ Ω k).subtypeL

/-- The weak exterior derivative `d : HΛᵏ(Ω) → HΛᵏ⁺¹(Ω)`. -/
noncomputable def HΛ.d : HΛ Ω k →L[ℝ] HΛ Ω (k + 1) :=
  LinearMap.mkContinuous
    { toFun := fun p => ⟨WithLp.toLp 2 (p.1.snd, 0), p.2.zero_right⟩
      map_add' := by
        intro p q
        refine Subtype.ext ?_
        refine withLp_prod_ext ?_ ?_ <;> simp
      map_smul' := by
        intro c p
        refine Subtype.ext ?_
        refine withLp_prod_ext ?_ ?_ <;> simp }
    1 (by
      intro p
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      change ‖(WithLp.toLp 2 (p.1.snd, 0) : WithLp 2 (L2Form Ω (k + 1) × L2Form Ω (k + 1 + 1)))‖
        ≤ ‖p.1‖
      refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
      rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
      simp)

theorem HΛ.toL2_d (p : HΛ Ω k) : HΛ.toL2 (HΛ.d p) = p.1.snd := rfl

theorem HΛ.hasWeakExtDeriv (p : HΛ Ω k) : HasWeakExtDeriv (HΛ.toL2 p) (HΛ.toL2 (HΛ.d p)) :=
  p.2

theorem HΛ.toL2_injective (hΩ : IsOpen Ω) : Function.Injective (HΛ.toL2 : HΛ Ω k → L2Form Ω k) := by
  intro p q hpq
  have h1 : p.1.snd = q.1.snd := HasWeakExtDeriv.unique hΩ p.2 (by
    have : p.1.fst = q.1.fst := hpq
    rw [this]; exact q.2)
  refine Subtype.ext ?_
  exact withLp_prod_ext hpq h1

/-- **The `L²` de Rham complex** `HΛ⁰(Ω) → HΛ¹(Ω) → HΛ²(Ω) → ⋯` of an open subset `Ω` of a
Euclidean space is a Hilbert complex (Arnold, §6.2). -/
noncomputable def deRhamComplex (hΩ : IsOpen Ω) :
    HilbertComplex (fun k => L2Form Ω k) (fun k => HΛ Ω k) where
  ι _ := HΛ.toL2
  ι_injective _ := HΛ.toL2_injective hΩ
  d _ := HΛ.d
  d_d := by
    intro k p
    refine Subtype.ext ?_
    refine withLp_prod_ext ?_ ?_ <;> simp [HΛ.d]
  inner_eq := by
    intro k p q
    change ⟪p.1, q.1⟫ = _
    rw [WithLp.prod_inner_apply]
    rfl

end FEEC
