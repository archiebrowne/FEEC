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

theorem zero : IsHomogeneousForm r (0 : E → E [⋀^Fin k]→L[ℝ] ℝ) := by
  sorry

theorem add {ω η : E → E [⋀^Fin k]→L[ℝ] ℝ} (hω : IsHomogeneousForm r ω)
    (hη : IsHomogeneousForm r η) : IsHomogeneousForm r (ω + η) := by
  sorry

theorem smul {ω : E → E [⋀^Fin k]→L[ℝ] ℝ} (c : ℝ) (hω : IsHomogeneousForm r ω) :
    IsHomogeneousForm r (c • ω) := by
  sorry

/-- A constant form is homogeneous of degree `0`. -/
theorem const (a : E [⋀^Fin k]→L[ℝ] ℝ) : IsHomogeneousForm 0 (fun _ : E => a) := by
  sorry

/-- A form which is homogeneous of degree `0` is constant. -/
theorem eq_const {ω : E → E [⋀^Fin k]→L[ℝ] ℝ} (hω : IsHomogeneousForm 0 ω) (x : E) :
    ω x = ω 0 := by
  sorry

/-- **Euler's identity** for homogeneous forms. -/
theorem fderiv_apply_self {ω : E → E [⋀^Fin k]→L[ℝ] ℝ} (hω : IsHomogeneousForm r ω) (x : E) :
    fderiv ℝ ω x x = (r : ℝ) • ω x := by
  sorry

/-- The derivative of a form homogeneous of degree `r + 1` is homogeneous of degree `r`. -/
theorem fderiv_smul {ω : E → E [⋀^Fin k]→L[ℝ] ℝ} (hω : IsHomogeneousForm (r + 1) ω)
    (t : ℝ) (x : E) : fderiv ℝ ω (t • x) = t ^ r • fderiv ℝ ω x := by
  sorry

/-- `d : 𝓗ᵣ₊₁Λᵏ → 𝓗ᵣΛᵏ⁺¹`. -/
protected theorem extDeriv {ω : E → E [⋀^Fin k]→L[ℝ] ℝ} (hω : IsHomogeneousForm (r + 1) ω) :
    IsHomogeneousForm r (extDeriv ω) := by
  sorry

/-- `d` vanishes on `𝓗₀Λᵏ` (constant forms). -/
theorem extDeriv_eq_zero {ω : E → E [⋀^Fin k]→L[ℝ] ℝ} (hω : IsHomogeneousForm 0 ω) :
    extDeriv ω = 0 := by
  sorry

/-- `κ : 𝓗ᵣΛᵏ⁺¹ → 𝓗ᵣ₊₁Λᵏ`. -/
protected theorem koszul {ω : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ} (hω : IsHomogeneousForm r ω) :
    IsHomogeneousForm (r + 1) (koszul ω) := by
  sorry

/-- **Homotopy formula** (Arnold, Theorem 7.1): `(dκ + κd) ω = (r + k) ω` for `ω ∈ 𝓗ᵣΛᵏ`,
here stated for forms of degree `k + 1`. -/
theorem homotopy {ω : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ} (hω : IsHomogeneousForm r ω) :
    extDeriv (koszul ω) + koszul (extDeriv ω) = ((r + k + 1 : ℕ) : ℝ) • ω := by
  sorry

/-- The homotopy formula for `0`-forms: `κ d f = r f` for `f ∈ 𝓗ᵣΛ⁰`. -/
theorem homotopy_zero {f : E → E [⋀^Fin 0]→L[ℝ] ℝ} (hf : IsHomogeneousForm r f) :
    koszul (extDeriv f) = (r : ℝ) • f := by
  sorry

/-- **Exactness of the homogeneous polynomial de Rham complex**: a closed form in `𝓗ᵣΛᵏ⁺¹`
is `d` of an explicit form in `κ 𝓗ᵣΛᵏ⁺¹ ⊆ 𝓗ᵣ₊₁Λᵏ`. -/
theorem eq_extDeriv_of_extDeriv_eq_zero {ω : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ}
    (hω : IsHomogeneousForm r ω) (hd : extDeriv ω = 0) :
    ω = extDeriv (koszul (((r + k + 1 : ℕ) : ℝ)⁻¹ • ω)) := by
  sorry

/-- **Exactness of the homogeneous Koszul complex**: a form in `𝓗ᵣΛᵏ⁺¹` with `κ ω = 0` is
`κ` of an explicit form. -/
theorem eq_koszul_of_koszul_eq_zero {ω : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ}
    (hω : IsHomogeneousForm r ω) (hκ : koszul ω = 0) :
    ω = koszul (extDeriv (((r + k + 1 : ℕ) : ℝ)⁻¹ • ω)) := by
  sorry

/-- A form in `𝓗ᵣΛᵏ⁺¹` whose image under `κ` is closed has `κ ω = 0`. This is the key fact
behind `𝓟ᵣ⁻Λᵏ ∩ ker d ⊆ 𝓟ᵣ₋₁Λᵏ`. -/
theorem koszul_eq_zero_of_extDeriv_koszul_eq_zero {ω : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ}
    (hω : IsHomogeneousForm r ω) (hd : extDeriv (koszul ω) = 0) : koszul ω = 0 := by
  sorry

/-- Forms of distinct degrees of homogeneity are linearly independent: if
`ω₀ + ⋯ + ω_r = 0` with `ω_j ∈ 𝓗ⱼΛᵏ` then every `ω_j` vanishes. -/
theorem eq_zero_of_sum_eq_zero {ω : ℕ → E → E [⋀^Fin k]→L[ℝ] ℝ} {n : ℕ}
    (hω : ∀ j < n, IsHomogeneousForm j (ω j)) (hsum : ∑ j ∈ Finset.range n, ω j = 0) :
    ∀ j < n, ω j = 0 := by
  sorry

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
