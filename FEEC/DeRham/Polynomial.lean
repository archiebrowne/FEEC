/-
Polynomial differential forms: the spaces `𝓟ᵣΛᵏ` and `𝓟ᵣ⁻Λᵏ`.
-/
import FEEC.DeRham.Homogeneous

/-!
# Polynomial differential forms

* `polyForms E r k` is `𝓟ᵣΛᵏ(E) = ⨁_{j ≤ r} 𝓗ⱼΛᵏ`, the polynomial `k`-forms of degree `≤ r`.
* `polyFormsMinus E r k` is `𝓟⁻ᵣ₊₁Λᵏ(E) = 𝓟ᵣΛᵏ + κ 𝓗ᵣΛᵏ⁺¹` (note the index shift: Arnold's
  `𝓟ᵣ⁻` is defined for `r ≥ 1`, and `polyFormsMinus E r k` is `𝓟⁻ᵣ₊₁Λᵏ`). In particular
  `polyFormsMinus E 0 k` is the space of Whitney forms `𝓟₁⁻Λᵏ`.

## Main results (Arnold, §7.1–7.3)

* `extDeriv_mem_polyForms`, `koszul_mem_polyForms`: `d 𝓟ᵣ₊₁Λᵏ ⊆ 𝓟ᵣΛᵏ⁺¹`, `κ 𝓟ᵣΛᵏ⁺¹ ⊆ 𝓟ᵣ₊₁Λᵏ`.
* `polyForms_le_polyFormsMinus`, `polyFormsMinus_le_polyForms`:
  `𝓟ᵣΛᵏ ⊆ 𝓟⁻ᵣ₊₁Λᵏ ⊆ 𝓟ᵣ₊₁Λᵏ`.
* `extDeriv_mem_polyForms_of_mem_polyFormsMinus`: `d 𝓟⁻ᵣ₊₁Λᵏ ⊆ 𝓟ᵣΛᵏ⁺¹`.
* `exists_extDeriv_eq_of_mem_polyForms`: exactness of the polynomial de Rham complex, with
  potentials in `𝓟⁻`.
* `mem_polyForms_of_mem_polyFormsMinus_of_extDeriv_eq_zero`: a closed form in `𝓟⁻ᵣ₊₁Λᵏ`
  lies in `𝓟ᵣΛᵏ`.

Together these say that both `𝓟ᵣΛ⁰ → 𝓟ᵣ₋₁Λ¹ → ⋯` and `𝓟ᵣ⁻Λ⁰ → 𝓟ᵣ⁻Λ¹ → ⋯` are exact
subcomplexes of the de Rham complex (in positive degree).
-/

namespace FEEC

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `𝓟ᵣΛᵏ(E)`: polynomial `k`-forms of degree at most `r`. -/
def polyForms (r k : ℕ) : Submodule ℝ (E → E [⋀^Fin k]→L[ℝ] ℝ) :=
  ⨆ j : Fin (r + 1), homogeneousForms E j k

/-- `𝓟⁻ᵣ₊₁Λᵏ(E) = 𝓟ᵣΛᵏ + κ 𝓗ᵣΛᵏ⁺¹` (note the index shift). -/
noncomputable def polyFormsMinus (r k : ℕ) : Submodule ℝ (E → E [⋀^Fin k]→L[ℝ] ℝ) :=
  polyForms E r k ⊔ (homogeneousForms E r (k + 1)).map koszulₗ

variable {E} {r k : ℕ}

/-- A form is in `𝓟ᵣΛᵏ` iff it is a sum of homogeneous forms of degrees `0, …, r`. -/
theorem mem_polyForms_iff {ω : E → E [⋀^Fin k]→L[ℝ] ℝ} :
    ω ∈ polyForms E r k ↔ ∃ c : ℕ → E → E [⋀^Fin k]→L[ℝ] ℝ,
      (∀ j, IsHomogeneousForm j (c j)) ∧ ω = ∑ j ∈ Finset.range (r + 1), c j := by
  sorry

theorem IsHomogeneousForm.mem_polyForms {ω : E → E [⋀^Fin k]→L[ℝ] ℝ} {j : ℕ}
    (hω : IsHomogeneousForm j ω) (hj : j ≤ r) : ω ∈ polyForms E r k := by
  sorry

theorem polyForms_mono {r r' : ℕ} (h : r ≤ r') : polyForms E r k ≤ polyForms E r' k := by
  sorry

/-- `d 𝓟ᵣ₊₁Λᵏ ⊆ 𝓟ᵣΛᵏ⁺¹`. -/
theorem extDeriv_mem_polyForms {ω : E → E [⋀^Fin k]→L[ℝ] ℝ} (hω : ω ∈ polyForms E (r + 1) k) :
    extDeriv ω ∈ polyForms E r (k + 1) := by
  sorry

/-- `d` vanishes on `𝓟₀Λᵏ`. -/
theorem extDeriv_eq_zero_of_mem_polyForms_zero {ω : E → E [⋀^Fin k]→L[ℝ] ℝ}
    (hω : ω ∈ polyForms E 0 k) : extDeriv ω = 0 := by
  sorry

/-- `κ 𝓟ᵣΛᵏ⁺¹ ⊆ 𝓟ᵣ₊₁Λᵏ`. -/
theorem koszul_mem_polyForms {ω : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ}
    (hω : ω ∈ polyForms E r (k + 1)) : koszul ω ∈ polyForms E (r + 1) k := by
  sorry

/-- `𝓟ᵣΛᵏ ⊆ 𝓟⁻ᵣ₊₁Λᵏ`. -/
theorem polyForms_le_polyFormsMinus : polyForms E r k ≤ polyFormsMinus E r k :=
  le_sup_left

/-- `𝓟⁻ᵣ₊₁Λᵏ ⊆ 𝓟ᵣ₊₁Λᵏ`. -/
theorem polyFormsMinus_le_polyForms : polyFormsMinus E r k ≤ polyForms E (r + 1) k := by
  sorry

/-- `d 𝓟⁻ᵣ₊₁Λᵏ ⊆ 𝓟ᵣΛᵏ⁺¹`. -/
theorem extDeriv_mem_polyForms_of_mem_polyFormsMinus {ω : E → E [⋀^Fin k]→L[ℝ] ℝ}
    (hω : ω ∈ polyFormsMinus E r k) : extDeriv ω ∈ polyForms E r (k + 1) := by
  sorry

/-- **Exactness of the polynomial de Rham complex** (Arnold, §7.2): every closed form in
`𝓟ᵣΛᵏ⁺¹` is the exterior derivative of a form in `𝓟⁻ᵣ₊₁Λᵏ`. -/
theorem exists_extDeriv_eq_of_mem_polyForms {ω : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ}
    (hω : ω ∈ polyForms E r (k + 1)) (hd : extDeriv ω = 0) :
    ∃ η ∈ polyFormsMinus E r k, extDeriv η = ω := by
  sorry

/-- A closed polynomial `0`-form is constant. -/
theorem mem_polyForms_zero_of_extDeriv_eq_zero {f : E → E [⋀^Fin 0]→L[ℝ] ℝ}
    (hf : f ∈ polyForms E r 0) (hd : extDeriv f = 0) : f ∈ polyForms E 0 0 := by
  sorry

/-- **Closed forms in `𝓟⁻`** (Arnold, §7.3): if `ω ∈ 𝓟⁻ᵣ₊₁Λᵏ` and `dω = 0` then `ω ∈ 𝓟ᵣΛᵏ`.
Consequently the complex `𝓟ᵣ⁻Λ⁰ → 𝓟ᵣ⁻Λ¹ → ⋯` is exact as well. -/
theorem mem_polyForms_of_mem_polyFormsMinus_of_extDeriv_eq_zero
    {ω : E → E [⋀^Fin k]→L[ℝ] ℝ} (hω : ω ∈ polyFormsMinus E r k) (hd : extDeriv ω = 0) :
    ω ∈ polyForms E r k := by
  sorry

/-- **Exactness of the `𝓟⁻` complex**: every closed form in `𝓟⁻ᵣ₊₁Λᵏ⁺¹` is the exterior
derivative of a form in `𝓟⁻ᵣ₊₁Λᵏ`. -/
theorem exists_extDeriv_eq_of_mem_polyFormsMinus {ω : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ}
    (hω : ω ∈ polyFormsMinus E r (k + 1)) (hd : extDeriv ω = 0) :
    ∃ η ∈ polyFormsMinus E r k, extDeriv η = ω := by
  sorry

end FEEC
