/-
Subcomplexes of short Hilbert complexes, bounded cochain projections, discrete Poincaré.
-/
import FEEC.Hilbert.HodgeLaplace

/-!
# Approximation of Hilbert complexes: subcomplexes and cochain projections

Following Arnold, §5.2, a discretisation of a short Hilbert complex
`V₀ --d₀--> V₁ --d₁--> W₂` is given by subspaces `Vh₀ ⊆ V₀`, `Vh₁ ⊆ V₁` with
`d₀ Vh₀ ⊆ Vh₁`. The restricted complex `Vh.toShort` is again a short Hilbert complex, so
the discrete cocycles, coboundaries, harmonic forms and the Galerkin method
`Vh.toShort.IsSolution f σh uh ph` come for free from the general definitions.

## Main results

* `ShortHilbertComplex.CochainProjection.hasPoincareConst`: the **discrete Poincaré
  inequality** (Arnold, Theorem 5.3): if `c` is a Poincaré constant for the complex and `π`
  is a cochain projection with `‖π‖ ≤ K`, then `c * K` is a Poincaré constant for the
  subcomplex.
-/

namespace FEEC

local notation "⟪" x ", " y "⟫" => inner ℝ x y

namespace ShortHilbertComplex

variable {W₀ W₁ W₂ V₀ V₁ : Type*}
  [NormedAddCommGroup W₀] [InnerProductSpace ℝ W₀]
  [NormedAddCommGroup W₁] [InnerProductSpace ℝ W₁]
  [NormedAddCommGroup W₂] [InnerProductSpace ℝ W₂]
  [NormedAddCommGroup V₀] [InnerProductSpace ℝ V₀]
  [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁]
  (S : ShortHilbertComplex W₀ W₁ W₂ V₀ V₁)

/-- A subcomplex of a short Hilbert complex: subspaces `Vh₀ ⊆ V₀`, `Vh₁ ⊆ V₁` with
`d₀ Vh₀ ⊆ Vh₁`. -/
structure Subcomplex where
  /-- The discrete space `Vh₀ ⊆ V₀`. -/
  carrier₀ : Submodule ℝ V₀
  /-- The discrete space `Vh₁ ⊆ V₁`. -/
  carrier₁ : Submodule ℝ V₁
  map_d₀ : ∀ τ ∈ carrier₀, S.d₀ τ ∈ carrier₁

variable {S}

namespace Subcomplex

variable (Vh : S.Subcomplex)

/-- The subcomplex as a short Hilbert complex in its own right (with the same ambient
spaces `W`). -/
def toShort : ShortHilbertComplex W₀ W₁ W₂ Vh.carrier₀ Vh.carrier₁ where
  ι₀ := S.ι₀ ∘L Vh.carrier₀.subtypeL
  ι₁ := S.ι₁ ∘L Vh.carrier₁.subtypeL
  d₀ := (S.d₀ ∘L Vh.carrier₀.subtypeL).codRestrict Vh.carrier₁ fun τ => Vh.map_d₀ τ τ.2
  d₁ := S.d₁ ∘L Vh.carrier₁.subtypeL
  d₁_d₀ τ := S.d₁_d₀ τ
  inner_V₀ σ τ := S.inner_V₀ σ τ
  inner_V₁ u v := S.inner_V₁ u v

@[simp] theorem toShort_ι₀ (τ : Vh.carrier₀) : Vh.toShort.ι₀ τ = S.ι₀ τ := rfl
@[simp] theorem toShort_ι₁ (v : Vh.carrier₁) : Vh.toShort.ι₁ v = S.ι₁ v := rfl
@[simp] theorem coe_toShort_d₀ (τ : Vh.carrier₀) : (Vh.toShort.d₀ τ : V₁) = S.d₀ τ := rfl
@[simp] theorem toShort_d₁ (v : Vh.carrier₁) : Vh.toShort.d₁ v = S.d₁ v := rfl

/-- Discrete cocycles are cocycles. -/
theorem coe_mem_cocycles {z : Vh.carrier₁} (hz : z ∈ Vh.toShort.cocycles) :
    (z : V₁) ∈ S.cocycles := hz

/-- Discrete coboundaries are coboundaries. -/
theorem coe_mem_coboundaries {b : Vh.carrier₁} (hb : b ∈ Vh.toShort.coboundaries) :
    (b : V₁) ∈ S.coboundaries := by
  sorry

/-- Discrete harmonic forms are cocycles (but in general not harmonic). -/
theorem coe_harmonic_mem_cocycles {q : Vh.carrier₁} (hq : q ∈ Vh.toShort.harmonic) :
    (q : V₁) ∈ S.cocycles :=
  Vh.toShort.harmonic_le_cocycles hq

/-- Discrete harmonic forms are orthogonal to discrete coboundaries. -/
theorem inner_harmonic_d₀ {q : Vh.carrier₁} (hq : q ∈ Vh.toShort.harmonic) (τ : Vh.carrier₀) :
    ⟪(q : V₁), S.d₀ τ⟫ = 0 := by
  sorry

end Subcomplex

variable (S) in
/-- A **cochain projection** onto a subcomplex (Arnold, §5.2): projections `π₀`, `π₁` onto
the discrete spaces which commute with the differentials. Boundedness in the `V`-norm is
built in (they are continuous linear maps `V → V`); bounds on their norms appear as
hypotheses of the theorems.

The last field `comm₁` is the shadow, on a three-term segment, of the next commutation
relation `π₂ ∘ d₁ = d₁ ∘ π₁` together with `π₂ = id` on the discrete space: if
`d₁ u = d₁ v` with `v` discrete then `d₁ (π₁ u) = π₂ (d₁ u) = π₂ (d₁ v) = d₁ v`. -/
structure CochainProjection (Vh : S.Subcomplex) where
  /-- The projection `V₀ → Vh₀`. -/
  π₀ : V₀ →L[ℝ] V₀
  /-- The projection `V₁ → Vh₁`. -/
  π₁ : V₁ →L[ℝ] V₁
  π₀_mem : ∀ τ, π₀ τ ∈ Vh.carrier₀
  π₁_mem : ∀ v, π₁ v ∈ Vh.carrier₁
  π₀_id : ∀ τ ∈ Vh.carrier₀, π₀ τ = τ
  π₁_id : ∀ v ∈ Vh.carrier₁, π₁ v = v
  comm₀ : ∀ τ, π₁ (S.d₀ τ) = S.d₀ (π₀ τ)
  comm₁ : ∀ u, ∀ v ∈ Vh.carrier₁, S.d₁ u = S.d₁ v → S.d₁ (π₁ u) = S.d₁ v

namespace CochainProjection

variable {Vh : S.Subcomplex} (π : S.CochainProjection Vh)

/-- A cochain projection maps cocycles to cocycles. -/
theorem d₁_π₁_eq_zero {z : V₁} (hz : S.d₁ z = 0) : S.d₁ (π.π₁ z) = 0 := by
  sorry

/-- A cochain projection maps coboundaries to discrete coboundaries. -/
theorem π₁_coboundary (ρ : V₀) :
    π.π₁ (S.d₀ ρ) = S.d₀ (⟨π.π₀ ρ, π.π₀_mem ρ⟩ : Vh.carrier₀) :=
  π.comm₀ ρ

theorem norm_sub_π₁_le {K : ℝ} (hK : ‖π.π₁‖ ≤ K) (u : V₁) {w : V₁} (hw : w ∈ Vh.carrier₁) :
    ‖u - π.π₁ u‖ ≤ (1 + K) * ‖u - w‖ := by
  sorry

variable [CompleteSpace V₀] [CompleteSpace V₁]

/-- **Discrete Poincaré inequality** (Arnold, Theorem 5.3). If `c` is a Poincaré constant
for the complex and the cochain projection is bounded by `K`, then `c * K` is a Poincaré
constant for the subcomplex. In particular it is uniform over a family of subcomplexes with
uniformly bounded cochain projections. -/
theorem hasPoincareConst {c K : ℝ} (hc : S.HasPoincareConst c)
    (hK₀ : ‖π.π₀‖ ≤ K) (hK₁ : ‖π.π₁‖ ≤ K) : Vh.toShort.HasPoincareConst (c * K) := by
  sorry

end CochainProjection

end ShortHilbertComplex

end FEEC
