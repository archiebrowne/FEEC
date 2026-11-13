/-
The Euclidean inner product on k-covectors.
-/
import Mathlib

/-!
# Covectors with their Euclidean inner product

Mathlib equips the space `E [⋀^Fin k]→L[ℝ] ℝ` of alternating `k`-linear forms with the
operator norm, which does not come from an inner product. For the `L²` theory of differential
forms we need the Euclidean inner product

`⟪α, β⟫ = (1 / k!) ∑_{I : Fin k → Fin n} α(e_I) β(e_I) = ∑_{I increasing} α(e_I) β(e_I)`,

where `e` is an orthonormal basis of the Euclidean space `E` and `e_I = (e_{I 0}, …)`.
We put it on a type synonym `Covector E k`.

## Main definitions

* `FEEC.Covector E k`, with `InnerProductSpace ℝ (Covector E k)`.
* `FEEC.Covector.ofAlt`: the continuous linear equivalence from `E [⋀^Fin k]→L[ℝ] ℝ`.
-/

namespace FEEC

open Module

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The orthonormal basis of `E` used to define inner products of covectors and the
codifferential. (Neither depends on the choice.) -/
noncomputable abbrev stdBasis : OrthonormalBasis (Fin (finrank ℝ E)) ℝ E :=
  stdOrthonormalBasis ℝ E

/-- The space of alternating `k`-linear forms on `E`, with the Euclidean inner product. -/
def Covector (k : ℕ) : Type _ := E [⋀^Fin k]→L[ℝ] ℝ

namespace Covector

variable {E} {k : ℕ}

noncomputable instance : AddCommGroup (Covector E k) :=
  inferInstanceAs (AddCommGroup (E [⋀^Fin k]→L[ℝ] ℝ))

noncomputable instance : Module ℝ (Covector E k) :=
  inferInstanceAs (Module ℝ (E [⋀^Fin k]→L[ℝ] ℝ))

/-- The identity map from alternating forms to covectors, as a linear equivalence. -/
noncomputable def ofAltₗ : (E [⋀^Fin k]→L[ℝ] ℝ) ≃ₗ[ℝ] Covector E k := LinearEquiv.refl ℝ _

/-- The underlying alternating form of a covector. -/
noncomputable def toAlt (α : Covector E k) : E [⋀^Fin k]→L[ℝ] ℝ := ofAltₗ.symm α

/-- The value of a covector on the tuple of basis vectors `e_I`. -/
noncomputable def coeff (α : Covector E k) (I : Fin k → Fin (finrank ℝ E)) : ℝ :=
  α.toAlt fun j => stdBasis E (I j)

theorem eq_zero_of_forall_apply_basis (a : E [⋀^Fin k]→L[ℝ] ℝ)
    (h : ∀ I : Fin k → Fin (finrank ℝ E), a (fun j => stdBasis E (I j)) = 0) : a = 0 := by
  have key : a.toContinuousMultilinearMap.toMultilinearMap =
      (0 : E [⋀^Fin k]→L[ℝ] ℝ).toContinuousMultilinearMap.toMultilinearMap :=
    Module.Basis.ext_multilinear (fun _ => (stdBasis E).toBasis) (fun v => by
      simpa using h v)
  ext x
  exact congrArg (fun f => f x) key

theorem coeff_add (α β : Covector E k) (I : Fin k → Fin (finrank ℝ E)) :
    (α + β).coeff I = α.coeff I + β.coeff I := by
  simp [coeff, toAlt]

theorem coeff_smul (c : ℝ) (α : Covector E k) (I : Fin k → Fin (finrank ℝ E)) :
    (c • α).coeff I = c * α.coeff I := by
  simp [coeff, toAlt]

theorem eq_zero_of_coeff (α : Covector E k) (h : ∀ I, α.coeff I = 0) : α = 0 := by
  have : α.toAlt = 0 := eq_zero_of_forall_apply_basis _ h
  have h2 : ofAltₗ α.toAlt = ofAltₗ (0 : E [⋀^Fin k]→L[ℝ] ℝ) := by rw [this]
  simpa [toAlt] using h2

/-- The Euclidean inner product of covectors. -/
noncomputable def innerCore : InnerProductSpace.Core ℝ (Covector E k) where
  inner α β := ((k.factorial : ℝ))⁻¹ * ∑ I : Fin k → Fin (finrank ℝ E), α.coeff I * β.coeff I
  conj_inner_symm := by
    intro x y
    simp only [conj_trivial]
    congr 1
    exact Finset.sum_congr rfl fun I _ => mul_comm _ _
  re_inner_nonneg := by
    intro x
    simp only [RCLike.re_to_real]
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun I _ => mul_self_nonneg _)
  add_left := by
    intro x y z
    simp only [coeff_add, add_mul, Finset.sum_add_distrib]
    ring
  smul_left := by
    intro x y r
    simp only [coeff_smul, conj_trivial, mul_assoc, ← Finset.mul_sum]
    ring
  definite := by
    intro x hx
    apply eq_zero_of_coeff
    have hk : ((k.factorial : ℝ))⁻¹ ≠ 0 := by positivity
    have hs : ∑ I : Fin k → Fin (finrank ℝ E), x.coeff I * x.coeff I = 0 := by
      rcases mul_eq_zero.mp hx with h | h
      · exact absurd h hk
      · exact h
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun I _ => mul_self_nonneg (x.coeff I))).mp hs
    intro I
    exact mul_self_eq_zero.mp (this I (Finset.mem_univ _))

noncomputable instance : NormedAddCommGroup (Covector E k) :=
  innerCore.toNormedAddCommGroup

noncomputable instance : InnerProductSpace ℝ (Covector E k) :=
  InnerProductSpace.ofCore innerCore.toCore

theorem inner_def (α β : Covector E k) :
    ⟪α, β⟫ = ((k.factorial : ℝ))⁻¹ * ∑ I : Fin k → Fin (finrank ℝ E), α.coeff I * β.coeff I :=
  rfl

/-- The coefficient map as a linear map. -/
noncomputable def coeffₗ : Covector E k →ₗ[ℝ] ((Fin k → Fin (finrank ℝ E)) → ℝ) where
  toFun α I := α.coeff I
  map_add' α β := by ext I; exact coeff_add α β I
  map_smul' c α := by ext I; exact coeff_smul c α I

theorem coeffₗ_injective : Function.Injective (coeffₗ (E := E) (k := k)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro α h
  exact eq_zero_of_coeff α fun I => congrFun h I

instance : FiniteDimensional ℝ (Covector E k) :=
  Module.Finite.of_injective coeffₗ coeffₗ_injective

noncomputable instance : FiniteDimensional ℝ (E [⋀^Fin k]→L[ℝ] ℝ) :=
  Module.Finite.equiv (ofAltₗ (E := E) (k := k)).symm

/-- The identity map from alternating forms (with the operator norm) to covectors (with the
Euclidean norm), as a continuous linear equivalence. -/
noncomputable def ofAlt : (E [⋀^Fin k]→L[ℝ] ℝ) ≃L[ℝ] Covector E k :=
  ofAltₗ.toContinuousLinearEquiv

theorem ofAlt_apply (a : E [⋀^Fin k]→L[ℝ] ℝ) : ofAlt a = ofAltₗ a := rfl

@[simp] theorem toAlt_ofAlt (a : E [⋀^Fin k]→L[ℝ] ℝ) : (ofAlt a).toAlt = a := by
  simp [ofAlt_apply, toAlt]

@[simp] theorem ofAlt_toAlt (α : Covector E k) : ofAlt α.toAlt = α := by
  simp [ofAlt_apply, toAlt]

theorem coeff_ofAlt (a : E [⋀^Fin k]→L[ℝ] ℝ) (I : Fin k → Fin (finrank ℝ E)) :
    (ofAlt a).coeff I = a fun j => stdBasis E (I j) := by
  simp [coeff]

end Covector

end FEEC
