/-
The L² Poincaré lemma on a box, and closedness of the de Rham complex.
-/
import FEEC.DeRham.BoxDecomp
import FEEC.Main

/-!
# The `L²` Poincaré lemma on a box

Let `Ω = box e a b` be a nonempty open box in a Euclidean space of any dimension.

* `FEEC.exists_hasWeakExtDeriv_of_closed`: **the `L²` Poincaré lemma**: every weakly closed
  `ω ∈ L²Λᵏ⁺¹(Ω)` is `dη` for some `η ∈ L²Λᵏ(Ω)` with `‖η‖ ≤ C ‖ω‖`.
* `FEEC.boxComplex_isClosed`: the `L²` de Rham complex of `Ω` is closed.
* `FEEC.box_harmonic_eq_bot`: there are no nonzero harmonic forms of positive degree.
* `FEEC.box_hodgeLaplace_wellPosed`: **the Hodge Laplace problem on `Ω` is well posed in every
  degree, with no further hypothesis.**
-/

namespace FEEC

open MeasureTheory

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- A linear functional dominated by the norm of a linear map into a Hilbert space is
represented by a vector (Riesz representation on the closure of the range). -/
theorem exists_inner_eq_of_abs_le {X H : Type*} [AddCommGroup X] [Module ℝ X]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (j : X →ₗ[ℝ] H) (g : X →ₗ[ℝ] ℝ) {C : ℝ} (hC : 0 ≤ C) (h : ∀ x, |g x| ≤ C * ‖j x‖) :
    ∃ η : H, ‖η‖ ≤ C ∧ ∀ x, g x = ⟪η, j x⟫ := by
  have hker : LinearMap.ker j ≤ LinearMap.ker g := by
    intro x hx
    have := h x
    rw [LinearMap.mem_ker.1 hx] at this
    simp only [norm_zero, mul_zero] at this
    exact LinearMap.mem_ker.2 (abs_nonpos_iff.1 this)
  let g' : LinearMap.range j →ₗ[ℝ] ℝ :=
    ((LinearMap.ker j).liftQ g hker).comp (LinearMap.quotKerEquivRange j).symm.toLinearMap
  have hg' : ∀ x, g' ⟨j x, LinearMap.mem_range_self j x⟩ = g x := by
    intro x
    have : (LinearMap.quotKerEquivRange j).symm ⟨j x, LinearMap.mem_range_self j x⟩ =
        Submodule.Quotient.mk x := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp [g', this]
  have hbd : ∀ y : LinearMap.range j, ‖g' y‖ ≤ C * ‖y‖ := by
    rintro ⟨_, x, rfl⟩
    rw [hg', Real.norm_eq_abs]
    exact h x
  let f : LinearMap.range j →L[ℝ] ℝ := g'.mkContinuous C hbd
  obtain ⟨G, hG, hGn⟩ := exists_extension_norm_eq (LinearMap.range j) f
  have hfn : ‖f‖ ≤ C := LinearMap.mkContinuous_norm_le _ hC _
  refine ⟨(InnerProductSpace.toDual ℝ H).symm G, ?_, fun x => ?_⟩
  · rw [LinearIsometryEquiv.norm_map, hGn]; exact hfn
  · rw [InnerProductSpace.toDual_symm_apply, hG ⟨j x, LinearMap.mem_range_self j x⟩]
    exact (hg' x).symm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {n : ℕ}
  (e : OrthonormalBasis (Fin n) ℝ E) {a b : Fin n → ℝ}

/-- **The `L²` Poincaré lemma on a box.** -/
theorem exists_hasWeakExtDeriv_of_closed (hab : ∀ i, a i < b i) (k : ℕ) :
    ∃ C : ℝ, ∀ ω : L2Form (box e a b) (k + 1),
      HasWeakExtDeriv ω (0 : L2Form (box e a b) (k + 2)) →
      ∃ η : L2Form (box e a b) k, HasWeakExtDeriv η ω ∧ ‖η‖ ≤ C * ‖ω‖ := by
  obtain ⟨C, hC0, hdec⟩ := exists_codiff_decomp e hab k
  refine ⟨C, fun ω hω => ?_⟩
  let g : testForms (box e a b) (k + 1) →ₗ[ℝ] ℝ :=
    ((innerSL ℝ ω).toLinearMap).comp (testFormsToLp (box e a b) (k + 1))
  have hg : ∀ φ : testForms (box e a b) (k + 1), g φ = ⟪ω, φ.2.toLp⟫ := fun φ => rfl
  have hbd : ∀ φ : testForms (box e a b) (k + 1),
      |g φ| ≤ (C * ‖ω‖) * ‖testFormsCodiffToLp (box e a b) k φ‖ := by
    rintro ⟨φ, hφ⟩
    obtain ⟨ψ, hψ, χ, hχ, hφeq, hn⟩ := hdec φ hφ
    have h1 : hφ.toLp = hψ.codiff.toLp + hχ.toLp :=
      (IsTestForm.toLp_congr hφ (hψ.codiff.add hχ) hφeq).trans
        (IsTestForm.toLp_add hψ.codiff hχ)
    have h2 : ⟪ω, hψ.codiff.toLp⟫ = 0 := by
      have := hω ψ hψ
      rw [inner_zero_left] at this
      exact this.symm
    show |⟪ω, hφ.toLp⟫| ≤ _
    rw [h1, inner_add_right, h2, zero_add]
    calc |⟪ω, hχ.toLp⟫| ≤ ‖ω‖ * ‖hχ.toLp‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖ω‖ * (C * ‖hφ.codiff.toLp‖) := by gcongr
      _ = _ := by
        show _ = (C * ‖ω‖) * ‖hφ.codiff.toLp‖
        ring
  obtain ⟨η, hη, hηg⟩ := exists_inner_eq_of_abs_le (testFormsCodiffToLp (box e a b) k) g
    (mul_nonneg hC0 (norm_nonneg _)) hbd
  refine ⟨η, fun φ hφ => ?_, by linarith⟩
  have := hηg ⟨φ, hφ⟩
  rw [hg] at this
  exact this

/-- Weakly closed elements of `HΛᵏ⁺¹(box)` are `d` of elements of `HΛᵏ(box)`. -/
theorem exists_d_eq_of_hasWeakExtDeriv_zero (hab : ∀ i, a i < b i) {k : ℕ}
    (u : HΛ (box e a b) (k + 1)) (hu : HasWeakExtDeriv (HΛ.toL2 u) (0 : L2Form (box e a b) (k + 2))) :
    ∃ τ : HΛ (box e a b) k, HΛ.d τ = u := by
  obtain ⟨C, hC⟩ := exists_hasWeakExtDeriv_of_closed e hab k
  obtain ⟨η, hη, -⟩ := hC (HΛ.toL2 u) hu
  refine ⟨⟨WithLp.toLp 2 (η, HΛ.toL2 u), hη⟩, ?_⟩
  exact HΛ.toL2_injective (isOpen_box e a b) rfl

/-- **The `L²` de Rham complex of a box is closed.** -/
theorem boxComplex_isClosed (hab : ∀ i, a i < b i) :
    (deRhamComplex (isOpen_box e a b)).IsClosed := by
  intro k
  have hset : Set.range ((deRhamComplex (isOpen_box e a b)).ι (k + 1) ∘
      (deRhamComplex (isOpen_box e a b)).d k) =
      ⋂ (ψ : E → E [⋀^Fin (k + 1 + 1)]→L[ℝ] ℝ) (hψ : IsTestForm (box e a b) ψ),
        {ω : L2Form (box e a b) (k + 1) |
          ⟪(0 : L2Form (box e a b) (k + 2)), hψ.toLp⟫ = ⟪ω, hψ.codiff.toLp⟫} := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · rintro ⟨p, rfl⟩ ψ hψ
      exact (p.2.zero_right) ψ hψ
    · intro hω
      obtain ⟨τ, hτ⟩ := exists_d_eq_of_hasWeakExtDeriv_zero e hab
        (k := k) ⟨WithLp.toLp 2 (ω, 0), by
          intro ψ hψ; exact hω ψ hψ⟩ (fun ψ hψ => hω ψ hψ)
      exact ⟨τ, congrArg HΛ.toL2 hτ⟩
  rw [hset]
  exact isClosed_iInter fun ψ => isClosed_iInter fun hψ =>
    isClosed_eq continuous_const (continuous_id.inner continuous_const)

/-- On a box there are no nonzero harmonic forms of positive degree. -/
theorem box_harmonic_eq_bot (hab : ∀ i, a i < b i) (k : ℕ) :
    ((deRhamComplex (isOpen_box e a b)).segment k).harmonic = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hz, hperp⟩ := Submodule.mem_inf.1 hx
  have hz' : x.1.snd = 0 := hz
  have hw : HasWeakExtDeriv (HΛ.toL2 x) (0 : L2Form (box e a b) (k + 2)) := by
    have : HasWeakExtDeriv x.1.fst x.1.snd := x.2
    rw [hz'] at this
    exact this
  obtain ⟨τ, hτ⟩ := exists_d_eq_of_hasWeakExtDeriv_zero e hab x hw
  have hcob : x ∈ ((deRhamComplex (isOpen_box e a b)).segment k).coboundaries := ⟨τ, hτ⟩
  have := (Submodule.mem_orthogonal _ _).1 hperp x hcob
  exact (Submodule.mem_bot ℝ).2 (inner_self_eq_zero.1 this)

/-- **Unconditional well-posedness of the Hodge Laplacian on a box**, in every dimension and
every degree `k + 1`: for every `f ∈ L²Λᵏ⁺¹(Ω)` the mixed problem: find `σ ∈ HΛᵏ`,
`u ∈ HΛᵏ⁺¹`, `p ∈ 𝔥ᵏ⁺¹` with `σ = d* u`, `dσ + d* du + p = f`, `u ⟂ 𝔥ᵏ⁺¹`, has a unique
solution, depending continuously on `f`; moreover `p = 0`. -/
theorem box_hodgeLaplace_wellPosed (hab : ∀ i, a i < b i) (k : ℕ) :
    ∃ c : ℝ, ∀ f : L2Form (box e a b) (k + 1), ∃ σ u p,
      ((deRhamComplex (isOpen_box e a b)).segment k).IsSolution f σ u p ∧ p = 0 ∧
      ‖σ‖ + ‖u‖ + ‖p‖ ≤ stabilityConst c * ‖f‖ ∧
      ∀ σ' u' p', ((deRhamComplex (isOpen_box e a b)).segment k).IsSolution f σ' u' p' →
        σ' = σ ∧ u' = u ∧ p' = p := by
  obtain ⟨c, hc⟩ := deRham_hodgeLaplace_wellPosed (isOpen_box e a b) (boxComplex_isClosed e hab) k
  refine ⟨c, fun f => ?_⟩
  obtain ⟨σ, u, p, hs, hn, hu⟩ := hc f
  refine ⟨σ, u, p, hs, ?_, hn, hu⟩
  have := hs.harmonic
  rw [box_harmonic_eq_bot e hab k] at this
  exact (Submodule.mem_bot ℝ).1 this

end FEEC
