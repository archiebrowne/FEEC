/-
Homogeneous differential forms.
-/
import FEEC.DeRham.Koszul

/-!
# Homogeneous differential forms

`𝓗ᵣΛᵏ`: the smooth `k`-forms `ω` on `E` with `ω (t • x) = t ^ r • ω x` for all real `t`.
A smooth map which is homogeneous of degree `r : ℕ` in this sense is a homogeneous polynomial
of degree `r`, so these are the homogeneous polynomial differential forms of Arnold, §7.1.
All results here only use smoothness and homogeneity.

## Main results

* `IsHomogeneousForm.fderiv_apply_self`: Euler's identity `Dω(x) x = r • ω x`.
* `IsHomogeneousForm.extDeriv`, `IsHomogeneousForm.koszul`: `d : 𝓗ᵣ₊₁Λᵏ → 𝓗ᵣΛᵏ⁺¹`,
  `κ : 𝓗ᵣΛᵏ⁺¹ → 𝓗ᵣ₊₁Λᵏ`.
* `IsHomogeneousForm.homotopy`: `(dκ + κd) ω = (r + k) • ω` for `ω ∈ 𝓗ᵣΛᵏ`
  (Arnold, Theorem 7.1).
* `IsHomogeneousForm.eq_extDeriv_of_extDeriv_eq_zero`,
  `IsHomogeneousForm.eq_koszul_of_koszul_eq_zero`: exactness of the homogeneous polynomial
  de Rham and Koszul complexes.
* `IsHomogeneousForm.eq_zero_of_sum_eq_zero`: forms of different degrees of homogeneity are
  linearly independent.
-/

namespace FEEC


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k r : ℕ}

/-- A smooth `k`-form which is homogeneous of degree `r`: an element of `𝓗ᵣΛᵏ`. -/
structure IsHomogeneousForm (r : ℕ) (ω : E → E [⋀^Fin k]→L[ℝ] ℝ) : Prop where
  contDiff : ContDiff ℝ (⊤ : ℕ∞) ω
  map_smul : ∀ (t : ℝ) (x : E), ω (t • x) = t ^ r • ω x

namespace IsHomogeneousForm

theorem zero : IsHomogeneousForm r (0 : E → E [⋀^Fin k]→L[ℝ] ℝ) :=
  ⟨contDiff_const, fun t x => by simp⟩

theorem add {ω η : E → E [⋀^Fin k]→L[ℝ] ℝ} (hω : IsHomogeneousForm r ω)
    (hη : IsHomogeneousForm r η) : IsHomogeneousForm r (ω + η) :=
  ⟨hω.contDiff.add hη.contDiff, fun t x => by
    simp [hω.map_smul, hη.map_smul, smul_add]⟩

theorem smul {ω : E → E [⋀^Fin k]→L[ℝ] ℝ} (c : ℝ) (hω : IsHomogeneousForm r ω) :
    IsHomogeneousForm r (c • ω) :=
  ⟨hω.contDiff.const_smul c, fun t x => by
    simp [hω.map_smul, smul_comm c]⟩

/-- A constant form is homogeneous of degree `0`. -/
theorem const (a : E [⋀^Fin k]→L[ℝ] ℝ) : IsHomogeneousForm 0 (fun _ : E => a) :=
  ⟨contDiff_const, fun t x => by simp⟩

/-- A form which is homogeneous of degree `0` is constant. -/
theorem eq_const {ω : E → E [⋀^Fin k]→L[ℝ] ℝ} (hω : IsHomogeneousForm 0 ω) (x : E) :
    ω x = ω 0 := by
  have := hω.map_smul 0 x
  simpa using this.symm

theorem differentiable {ω : E → E [⋀^Fin k]→L[ℝ] ℝ} (hω : IsHomogeneousForm r ω) :
    Differentiable ℝ ω :=
  hω.contDiff.differentiable (by simp)

/-- **Euler's identity** for homogeneous forms. -/
theorem fderiv_apply_self {ω : E → E [⋀^Fin k]→L[ℝ] ℝ} (hω : IsHomogeneousForm r ω) (x : E) :
    fderiv ℝ ω x x = (r : ℝ) • ω x := by
  have h1 : HasDerivAt (fun t : ℝ => ω (t • x)) (fderiv ℝ ω ((1 : ℝ) • x) ((1 : ℝ) • x)) 1 := by
    have := ((hω.differentiable).differentiableAt (x := (1 : ℝ) • x)).hasFDerivAt.comp_hasDerivAt
      (1 : ℝ) ((hasDerivAt_id (1 : ℝ)).smul_const x)
    exact this
  have h2 : HasDerivAt (fun t : ℝ => ω (t • x)) ((r : ℝ) • ω x) 1 := by
    have : (fun t : ℝ => ω (t • x)) = fun t => t ^ r • ω x := funext fun t => hω.map_smul t x
    rw [this]
    simpa using ((hasDerivAt_pow r (1 : ℝ)).smul_const (ω x))
  simpa using h1.unique h2

/-- The derivative of a form homogeneous of degree `r + 1` is homogeneous of degree `r`. -/
theorem fderiv_smul {ω : E → E [⋀^Fin k]→L[ℝ] ℝ} (hω : IsHomogeneousForm (r + 1) ω)
    (t : ℝ) (x : E) : fderiv ℝ ω (t • x) = t ^ r • fderiv ℝ ω x := by
  have key : ∀ t : ℝ, t ≠ 0 → fderiv ℝ ω (t • x) = t ^ r • fderiv ℝ ω x := by
    intro t ht
    have hc : HasFDerivAt (ω ∘ fun y : E => t • y)
        ((fderiv ℝ ω (t • x)).comp (t • ContinuousLinearMap.id ℝ E)) x :=
      (hω.differentiable.differentiableAt (x := t • x)).hasFDerivAt.comp x
        ((hasFDerivAt_id x).const_smul t)
    have hfun : (ω ∘ fun y : E => t • y) = fun y => t ^ (r + 1) • ω y :=
      funext fun y => hω.map_smul t y
    rw [hfun] at hc
    have hd : HasFDerivAt (fun y => t ^ (r + 1) • ω y) (t ^ (r + 1) • fderiv ℝ ω x) x :=
      HasFDerivAt.const_smul (hω.differentiable.differentiableAt (x := x)).hasFDerivAt
        (t ^ (r + 1))
    have := hc.unique hd
    refine ContinuousLinearMap.ext fun m => ?_
    rw [smul_apply]
    have h3 := congrArg (fun L => L m) this
    simp only [ContinuousLinearMap.comp_apply, smul_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.map_smul, pow_succ] at h3
    have h4 : t • (fderiv ℝ ω (t • x) m) = t • (t ^ r • fderiv ℝ ω x m) := by
      rw [h3, mul_comm, mul_smul]
    exact smul_right_injective _ ht h4
  by_cases ht : t = 0
  · subst ht
    have hcont : Continuous (fun s : ℝ => fderiv ℝ ω (s • x)) :=
      (hω.contDiff.continuous_fderiv (by simp)).comp (continuous_id.smul continuous_const)
    have h1 : Filter.Tendsto (fun s : ℝ => fderiv ℝ ω (s • x)) (nhdsWithin 0 {0}ᶜ)
        (nhds (fderiv ℝ ω ((0 : ℝ) • x))) :=
      (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    have h2 : Filter.Tendsto (fun s : ℝ => fderiv ℝ ω (s • x)) (nhdsWithin 0 {0}ᶜ)
        (nhds ((0 : ℝ) ^ r • fderiv ℝ ω x)) := by
      have : Filter.Tendsto (fun s : ℝ => s ^ r • fderiv ℝ ω x) (nhdsWithin 0 {0}ᶜ)
          (nhds ((0 : ℝ) ^ r • fderiv ℝ ω x)) :=
        ((continuous_pow r).smul continuous_const).tendsto 0 |>.mono_left nhdsWithin_le_nhds
      refine this.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact (key s hs).symm
    exact tendsto_nhds_unique h1 h2
  · exact key t ht

/-- `d : 𝓗ᵣ₊₁Λᵏ → 𝓗ᵣΛᵏ⁺¹`. -/
protected theorem extDeriv {ω : E → E [⋀^Fin k]→L[ℝ] ℝ} (hω : IsHomogeneousForm (r + 1) ω) :
    IsHomogeneousForm r (extDeriv ω) := by
  refine ⟨?_, fun t x => ?_⟩
  · have h1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ ω) :=
      hω.contDiff.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
    exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℝ).contDiff.comp h1
  · simp only [_root_.extDeriv, hω.fderiv_smul]
    exact ContinuousAlternatingMap.alternatizeUncurryFin_smul _ _

/-- `d` vanishes on `𝓗₀Λᵏ` (constant forms). -/
theorem extDeriv_eq_zero {ω : E → E [⋀^Fin k]→L[ℝ] ℝ} (hω : IsHomogeneousForm 0 ω) :
    extDeriv ω = 0 := by
  have : fderiv ℝ ω = 0 := by
    funext x
    obtain ⟨c, hc⟩ : ∃ c, ω = fun _ => c := ⟨ω 0, funext fun y => hω.eq_const y⟩
    rw [hc]; simp
  funext x
  simp [_root_.extDeriv, this, ← ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply]

/-- `κ : 𝓗ᵣΛᵏ⁺¹ → 𝓗ᵣ₊₁Λᵏ`. -/
protected theorem koszul {ω : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ} (hω : IsHomogeneousForm r ω) :
    IsHomogeneousForm (r + 1) (koszul ω) := by
  refine ⟨hω.contDiff.koszul, fun t x => ?_⟩
  rw [koszul_apply, koszul_apply, hω.map_smul]
  ext v
  simp [pow_succ, mul_comm, mul_smul]

/-- **Homotopy formula** (Arnold, Theorem 7.1): `(dκ + κd) ω = (r + k) ω` for `ω ∈ 𝓗ᵣΛᵏ`,
here stated for forms of degree `k + 1`. -/
theorem homotopy {ω : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ} (hω : IsHomogeneousForm r ω) :
    extDeriv (koszul ω) + koszul (extDeriv ω) = ((r + k + 1 : ℕ) : ℝ) • ω := by
  funext x
  have := extDeriv_koszul_add_koszul_extDeriv (hω.differentiable x)
  rw [hω.fderiv_apply_self] at this
  simp only [Pi.add_apply, Pi.smul_apply, this]
  push_cast
  module

/-- The homotopy formula for `0`-forms: `κ d f = r f` for `f ∈ 𝓗ᵣΛ⁰`. -/
theorem homotopy_zero {f : E → E [⋀^Fin 0]→L[ℝ] ℝ} (hf : IsHomogeneousForm r f) :
    koszul (extDeriv f) = (r : ℝ) • f := by
  funext x
  rw [koszul_extDeriv_zero (hf.differentiable x), hf.fderiv_apply_self]
  rfl

/-- **Exactness of the homogeneous polynomial de Rham complex**: a closed form in `𝓗ᵣΛᵏ⁺¹`
is `d` of an explicit form in `κ 𝓗ᵣΛᵏ⁺¹ ⊆ 𝓗ᵣ₊₁Λᵏ`. -/
theorem eq_extDeriv_of_extDeriv_eq_zero {ω : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ}
    (hω : IsHomogeneousForm r ω) (hd : extDeriv ω = 0) :
    ω = extDeriv (koszul (((r + k + 1 : ℕ) : ℝ)⁻¹ • ω)) := by
  have h := hω.homotopy
  rw [hd, koszul_zero] at h
  have hne : ((r + k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  funext x
  have hx := congrFun h x
  simp only [Pi.add_apply, Pi.zero_apply, add_zero, Pi.smul_apply] at hx
  rw [koszul_smul, extDeriv_smul, hx, smul_smul, inv_mul_cancel₀ hne, one_smul]

/-- **Exactness of the homogeneous Koszul complex**: a form in `𝓗ᵣΛᵏ⁺¹` with `κ ω = 0` is
`κ` of an explicit form. -/
theorem eq_koszul_of_koszul_eq_zero {ω : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ}
    (hω : IsHomogeneousForm r ω) (hκ : koszul ω = 0) :
    ω = koszul (extDeriv (((r + k + 1 : ℕ) : ℝ)⁻¹ • ω)) := by
  have h := hω.homotopy
  rw [hκ] at h
  have hne : ((r + k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have h0 : extDeriv (0 : E → E [⋀^Fin k]→L[ℝ] ℝ) = 0 := by
    funext x
    simp [_root_.extDeriv, ← ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply]
  rw [h0] at h
  have e : extDeriv (((r + k + 1 : ℕ) : ℝ)⁻¹ • ω) = ((r + k + 1 : ℕ) : ℝ)⁻¹ • extDeriv ω := by
    funext x; exact extDeriv_smul _ _
  funext x
  have hx := congrFun h x
  simp only [Pi.add_apply, Pi.zero_apply, zero_add, Pi.smul_apply] at hx
  rw [e, koszul_smul, Pi.smul_apply, hx, smul_smul, inv_mul_cancel₀ hne, one_smul]

/-- A form in `𝓗ᵣΛᵏ⁺¹` whose image under `κ` is closed has `κ ω = 0`. This is the key fact
behind `𝓟ᵣ⁻Λᵏ ∩ ker d ⊆ 𝓟ᵣ₋₁Λᵏ`. -/
theorem koszul_eq_zero_of_extDeriv_koszul_eq_zero {ω : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ}
    (hω : IsHomogeneousForm r ω) (hd : extDeriv (koszul ω) = 0) : koszul ω = 0 := by
  have h := congrArg koszul hω.homotopy
  rw [hd, koszul_add, koszul_koszul, koszul_smul, koszul_zero, add_zero] at h
  have hne : ((r + k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  rcases smul_eq_zero.1 h.symm with h1 | h1
  · exact absurd h1 hne
  · exact h1

/-- Forms of distinct degrees of homogeneity are linearly independent: if
`ω₀ + ⋯ + ω_r = 0` with `ω_j ∈ 𝓗ⱼΛᵏ` then every `ω_j` vanishes. -/
theorem eq_zero_of_sum_eq_zero {ω : ℕ → E → E [⋀^Fin k]→L[ℝ] ℝ} {n : ℕ}
    (hω : ∀ j < n, IsHomogeneousForm j (ω j)) (hsum : ∑ j ∈ Finset.range n, ω j = 0) :
    ∀ j < n, ω j = 0 := by
  intro j hj
  funext x
  ext v
  let P : Polynomial ℝ := ∑ i ∈ Finset.range n, Polynomial.C (ω i x v) * Polynomial.X ^ i
  have hP : P = 0 := by
    apply Polynomial.funext
    intro t
    have h2 : (∑ i ∈ Finset.range n, ω i (t • x)) v = 0 := by
      have := congrArg (fun f => f (t • x) v) hsum
      simpa using this
    simp only [P, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_zero]
    have h3 : (∑ i ∈ Finset.range n, ω i (t • x)) v = ∑ i ∈ Finset.range n, (ω i x v) * t ^ i := by
      rw [ContinuousAlternatingMap.sum_apply]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [(hω i (Finset.mem_range.1 hi)).map_smul]
      simp [mul_comm]
    rw [← h3]
    exact h2
  have hc := congrArg (fun q => Polynomial.coeff q j) hP
  simpa [P, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hj] using hc

end IsHomogeneousForm

variable (E) in
/-- `𝓗ᵣΛᵏ(E)`: the space of homogeneous polynomial `k`-forms of degree `r`. -/
def homogeneousForms (r k : ℕ) : Submodule ℝ (E → E [⋀^Fin k]→L[ℝ] ℝ) where
  carrier := {ω | IsHomogeneousForm r ω}
  add_mem' := IsHomogeneousForm.add
  zero_mem' := IsHomogeneousForm.zero
  smul_mem' c _ h := IsHomogeneousForm.smul c h

@[simp] theorem mem_homogeneousForms {ω : E → E [⋀^Fin k]→L[ℝ] ℝ} :
    ω ∈ homogeneousForms E r k ↔ IsHomogeneousForm r ω := Iff.rfl

end FEEC
