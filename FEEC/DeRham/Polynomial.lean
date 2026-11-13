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
  classical
  constructor
  · intro h
    refine Submodule.iSup_induction (fun j : Fin (r + 1) => homogeneousForms E j k)
      (motive := fun ω => ∃ c : ℕ → E → E [⋀^Fin k]→L[ℝ] ℝ,
        (∀ j, IsHomogeneousForm j (c j)) ∧ ω = ∑ j ∈ Finset.range (r + 1), c j) h ?_ ?_ ?_
    · intro j ω hω
      refine ⟨fun i => if i = (j : ℕ) then ω else 0, fun i => ?_, ?_⟩
      · by_cases hi : i = (j : ℕ)
        · simp only [hi, if_true]
          exact hω
        · simp only [hi, if_false]
          exact IsHomogeneousForm.zero
      · have hj : (j : ℕ) ∈ Finset.range (r + 1) := Finset.mem_range.2 j.2
        simp [Finset.sum_ite_eq', hj]
    · exact ⟨fun _ => 0, fun _ => IsHomogeneousForm.zero, by simp⟩
    · rintro _ _ ⟨c₁, h₁, rfl⟩ ⟨c₂, h₂, rfl⟩
      exact ⟨fun j => c₁ j + c₂ j, fun j => (h₁ j).add (h₂ j), by
        simp [Finset.sum_add_distrib]⟩
  · rintro ⟨c, hc, rfl⟩
    exact Submodule.sum_mem _ fun j hj =>
      Submodule.mem_iSup_of_mem (⟨j, by simpa [Nat.lt_succ_iff] using hj⟩ : Fin (r + 1)) (hc j)

theorem IsHomogeneousForm.mem_polyForms {ω : E → E [⋀^Fin k]→L[ℝ] ℝ} {j : ℕ}
    (hω : IsHomogeneousForm j ω) (hj : j ≤ r) : ω ∈ polyForms E r k :=
  Submodule.mem_iSup_of_mem (⟨j, by omega⟩ : Fin (r + 1)) hω

theorem polyForms_mono {r r' : ℕ} (h : r ≤ r') : polyForms E r k ≤ polyForms E r' k :=
  iSup_le fun j =>
    le_iSup (fun i : Fin (r' + 1) => homogeneousForms E i k) (⟨j, by omega⟩ : Fin (r' + 1))

theorem differentiable_of_mem_polyForms {ω : E → E [⋀^Fin k]→L[ℝ] ℝ}
    (hω : ω ∈ polyForms E r k) : Differentiable ℝ ω := by
  obtain ⟨c, hc, rfl⟩ := mem_polyForms_iff.1 hω
  exact Differentiable.sum fun j _ => (hc j).differentiable

private theorem extDeriv_zero' : extDeriv (0 : E → E [⋀^Fin k]→L[ℝ] ℝ) = 0 := by
  funext x
  simp [_root_.extDeriv, ← ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply]

private theorem extDeriv_sum {ι : Type*} (s : Finset ι) (f : ι → E → E [⋀^Fin k]→L[ℝ] ℝ)
    (hf : ∀ i ∈ s, Differentiable ℝ (f i)) :
    extDeriv (∑ i ∈ s, f i) = ∑ i ∈ s, extDeriv (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using extDeriv_zero'
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    funext x
    have h1 : DifferentiableAt ℝ (f a) x := hf a (Finset.mem_insert_self _ _) x
    have h2 : DifferentiableAt ℝ (∑ i ∈ s, f i) x :=
      (Differentiable.sum fun i hi => hf i (Finset.mem_insert_of_mem hi)) x
    rw [extDeriv_add h1 h2, ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]
    rfl

private theorem extDeriv_sum_range_succ (c : ℕ → E → E [⋀^Fin k]→L[ℝ] ℝ)
    (hc : ∀ j, IsHomogeneousForm j (c j)) (n : ℕ) :
    extDeriv (∑ j ∈ Finset.range (n + 1), c j) = ∑ j ∈ Finset.range n, extDeriv (c (j + 1)) := by
  rw [extDeriv_sum _ _ fun j _ => (hc j).differentiable, Finset.sum_range_succ',
    (hc 0).extDeriv_eq_zero, add_zero]

/-- `d 𝓟ᵣ₊₁Λᵏ ⊆ 𝓟ᵣΛᵏ⁺¹`. -/
theorem extDeriv_mem_polyForms {ω : E → E [⋀^Fin k]→L[ℝ] ℝ} (hω : ω ∈ polyForms E (r + 1) k) :
    extDeriv ω ∈ polyForms E r (k + 1) := by
  obtain ⟨c, hc, rfl⟩ := mem_polyForms_iff.1 hω
  rw [extDeriv_sum_range_succ c hc]
  exact mem_polyForms_iff.2 ⟨fun j => extDeriv (c (j + 1)), fun j => (hc (j + 1)).extDeriv, rfl⟩

/-- `d` vanishes on `𝓟₀Λᵏ`. -/
theorem extDeriv_eq_zero_of_mem_polyForms_zero {ω : E → E [⋀^Fin k]→L[ℝ] ℝ}
    (hω : ω ∈ polyForms E 0 k) : extDeriv ω = 0 := by
  obtain ⟨c, hc, rfl⟩ := mem_polyForms_iff.1 hω
  simpa using (hc 0).extDeriv_eq_zero

/-- `κ 𝓟ᵣΛᵏ⁺¹ ⊆ 𝓟ᵣ₊₁Λᵏ`. -/
theorem koszul_mem_polyForms {ω : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ}
    (hω : ω ∈ polyForms E r (k + 1)) : koszul ω ∈ polyForms E (r + 1) k := by
  obtain ⟨c, hc, rfl⟩ := mem_polyForms_iff.1 hω
  rw [koszul_sum]
  exact Submodule.sum_mem _ fun j hj =>
    (hc j).koszul.mem_polyForms (by have := Finset.mem_range.1 hj; omega)

/-- `𝓟ᵣΛᵏ ⊆ 𝓟⁻ᵣ₊₁Λᵏ`. -/
theorem polyForms_le_polyFormsMinus : polyForms E r k ≤ polyFormsMinus E r k :=
  le_sup_left

/-- `𝓟⁻ᵣ₊₁Λᵏ ⊆ 𝓟ᵣ₊₁Λᵏ`. -/
theorem polyFormsMinus_le_polyForms : polyFormsMinus E r k ≤ polyForms E (r + 1) k := by
  refine sup_le (polyForms_mono (Nat.le_succ r)) ?_
  rintro _ ⟨β, hβ, rfl⟩
  exact (IsHomogeneousForm.koszul (show IsHomogeneousForm r β from hβ)).mem_polyForms le_rfl

/-- `d 𝓟⁻ᵣ₊₁Λᵏ ⊆ 𝓟ᵣΛᵏ⁺¹`. -/
theorem extDeriv_mem_polyForms_of_mem_polyFormsMinus {ω : E → E [⋀^Fin k]→L[ℝ] ℝ}
    (hω : ω ∈ polyFormsMinus E r k) : extDeriv ω ∈ polyForms E r (k + 1) := by
  obtain ⟨α, hα, _, ⟨β, hβ, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hω
  have hβ' : IsHomogeneousForm r β := hβ
  have hk := hβ'.koszul
  have hsplit : extDeriv (α + koszulₗ β) = extDeriv α + extDeriv (koszul β) := by
    funext x
    exact extDeriv_add ((differentiable_of_mem_polyForms hα) x) (hk.differentiable x)
  rw [hsplit]
  refine add_mem ?_ (hk.extDeriv.mem_polyForms le_rfl)
  cases r with
  | zero => rw [extDeriv_eq_zero_of_mem_polyForms_zero hα]; exact zero_mem _
  | succ r => exact polyForms_mono (Nat.le_succ r) (extDeriv_mem_polyForms hα)

/-- **Exactness of the polynomial de Rham complex** (Arnold, §7.2): every closed form in
`𝓟ᵣΛᵏ⁺¹` is the exterior derivative of a form in `𝓟⁻ᵣ₊₁Λᵏ`. -/
theorem exists_extDeriv_eq_of_mem_polyForms {ω : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ}
    (hω : ω ∈ polyForms E r (k + 1)) (hd : extDeriv ω = 0) :
    ∃ η ∈ polyFormsMinus E r k, extDeriv η = ω := by
  obtain ⟨c, hc, rfl⟩ := mem_polyForms_iff.1 hω
  rw [extDeriv_sum_range_succ c hc] at hd
  have hz : ∀ j < r, extDeriv (c (j + 1)) = 0 :=
    IsHomogeneousForm.eq_zero_of_sum_eq_zero (ω := fun j => extDeriv (c (j + 1)))
      (fun j _ => (hc (j + 1)).extDeriv) hd
  have hz' : ∀ j, j ≤ r → extDeriv (c j) = 0 := by
    intro j hj
    cases j with
    | zero => exact (hc 0).extDeriv_eq_zero
    | succ j => exact hz j (by omega)
  refine ⟨∑ j ∈ Finset.range (r + 1), koszul (((j + k + 1 : ℕ) : ℝ)⁻¹ • c j), ?_, ?_⟩
  · rw [Finset.sum_range_succ]
    refine add_mem (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
    · exact Submodule.sum_mem _ fun j hj =>
        ((hc j).smul _).koszul.mem_polyForms (by have := Finset.mem_range.1 hj; omega)
    · exact ⟨((r + k + 1 : ℕ) : ℝ)⁻¹ • c r, (hc r).smul _, rfl⟩
  · rw [extDeriv_sum _ _ fun j _ => ((hc j).smul _).koszul.differentiable]
    exact Finset.sum_congr rfl fun j hj =>
      ((hc j).eq_extDeriv_of_extDeriv_eq_zero
        (hz' j (by have := Finset.mem_range.1 hj; omega))).symm

/-- A closed polynomial `0`-form is constant. -/
theorem mem_polyForms_zero_of_extDeriv_eq_zero {f : E → E [⋀^Fin 0]→L[ℝ] ℝ}
    (hf : f ∈ polyForms E r 0) (hd : extDeriv f = 0) : f ∈ polyForms E 0 0 := by
  obtain ⟨c, hc, rfl⟩ := mem_polyForms_iff.1 hf
  rw [extDeriv_sum_range_succ c hc] at hd
  have hz : ∀ j < r, extDeriv (c (j + 1)) = 0 :=
    IsHomogeneousForm.eq_zero_of_sum_eq_zero (ω := fun j => extDeriv (c (j + 1)))
      (fun j _ => (hc (j + 1)).extDeriv) hd
  have hc0 : ∀ j < r, c (j + 1) = 0 := by
    intro j hj
    have h1 := (hc (j + 1)).homotopy_zero
    rw [hz j hj, koszul_zero] at h1
    have hne : ((j + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    rcases smul_eq_zero.1 h1.symm with h | h
    · exact absurd h hne
    · exact h
  rw [Finset.sum_range_succ', Finset.sum_eq_zero fun j hj => hc0 j (Finset.mem_range.1 hj),
    zero_add]
  exact (hc 0).mem_polyForms le_rfl

/-- **Closed forms in `𝓟⁻`** (Arnold, §7.3): if `ω ∈ 𝓟⁻ᵣ₊₁Λᵏ` and `dω = 0` then `ω ∈ 𝓟ᵣΛᵏ`.
Consequently the complex `𝓟ᵣ⁻Λ⁰ → 𝓟ᵣ⁻Λ¹ → ⋯` is exact as well. -/
theorem mem_polyForms_of_mem_polyFormsMinus_of_extDeriv_eq_zero
    {ω : E → E [⋀^Fin k]→L[ℝ] ℝ} (hω : ω ∈ polyFormsMinus E r k) (hd : extDeriv ω = 0) :
    ω ∈ polyForms E r k := by
  obtain ⟨α, hα, _, ⟨β, hβ, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hω
  have hβ' : IsHomogeneousForm r β := hβ
  have hk := hβ'.koszul
  obtain ⟨c, hc, rfl⟩ := mem_polyForms_iff.1 hα
  have hsplit : extDeriv ((∑ j ∈ Finset.range (r + 1), c j) + koszulₗ β) =
      ∑ j ∈ Finset.range r, extDeriv (c (j + 1)) + extDeriv (koszul β) := by
    funext x
    change extDeriv ((∑ j ∈ Finset.range (r + 1), c j) + koszul β) x = _
    rw [extDeriv_add ((Differentiable.sum fun j _ => (hc j).differentiable) x)
      (hk.differentiable x), extDeriv_sum_range_succ c hc]
    rfl
  rw [hsplit] at hd
  classical
  let e : ℕ → E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ := fun j =>
    if j < r then extDeriv (c (j + 1)) else extDeriv (koszul β)
  have hsum : ∑ j ∈ Finset.range (r + 1), e j = 0 := by
    rw [Finset.sum_range_succ]
    have : ∑ j ∈ Finset.range r, e j = ∑ j ∈ Finset.range r, extDeriv (c (j + 1)) :=
      Finset.sum_congr rfl fun j hj => if_pos (Finset.mem_range.1 hj)
    rw [this]
    simpa [e] using hd
  have hhom : ∀ j < r + 1, IsHomogeneousForm j (e j) := by
    intro j hj
    by_cases h : j < r
    · simp only [e, if_pos h]
      exact (hc (j + 1)).extDeriv
    · have : j = r := by omega
      subst this
      simp only [e, if_neg h]
      exact hk.extDeriv
  have h1 := IsHomogeneousForm.eq_zero_of_sum_eq_zero hhom hsum r (Nat.lt_succ_self r)
  simp only [e, lt_irrefl, if_false] at h1
  have h2 := IsHomogeneousForm.koszul_eq_zero_of_extDeriv_koszul_eq_zero hβ' h1
  rw [koszulₗ_apply, h2, add_zero]
  exact hα

/-- **Exactness of the `𝓟⁻` complex**: every closed form in `𝓟⁻ᵣ₊₁Λᵏ⁺¹` is the exterior
derivative of a form in `𝓟⁻ᵣ₊₁Λᵏ`. -/
theorem exists_extDeriv_eq_of_mem_polyFormsMinus {ω : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ}
    (hω : ω ∈ polyFormsMinus E r (k + 1)) (hd : extDeriv ω = 0) :
    ∃ η ∈ polyFormsMinus E r k, extDeriv η = ω :=
  exists_extDeriv_eq_of_mem_polyForms
    (mem_polyForms_of_mem_polyFormsMinus_of_extDeriv_eq_zero hω hd) hd

end FEEC
