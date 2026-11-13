/-
The gap between continuous and discrete harmonic forms.
-/
import FEEC.Discrete.Subcomplex

/-!
# Harmonic forms and discrete harmonic forms

The discrete harmonic forms `𝔥_h = 𝔷_h ∩ 𝔅_hᗮ` of a subcomplex are in general not harmonic.
In the presence of a cochain projection the two spaces are close (Arnold, Theorem 5.2):

* `CochainProjection.exists_discrete_harmonic_near`: every `q ∈ 𝔥` is within
  `‖q - π q‖` of `𝔥_h`.
* `CochainProjection.norm_sub_harmonicPart_le`: for `q ∈ 𝔥_h`,
  `‖q - P_𝔥 q‖ ≤ ‖(1 - π) P_𝔥 q‖`.
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
  {S : ShortHilbertComplex W₀ W₁ W₂ V₀ V₁}

namespace CochainProjection

variable {Vh : S.Subcomplex} (π : S.CochainProjection Vh)
  [CompleteSpace V₀] [CompleteSpace V₁] [CompleteSpace Vh.carrier₁]

/-- **Harmonic forms are close to discrete harmonic forms** (Arnold, Theorem 5.2):
for `q ∈ 𝔥` there is `qh ∈ 𝔥_h` (namely its orthogonal projection) with
`‖q - qh‖ ≤ ‖q - π q‖`. -/
theorem exists_discrete_harmonic_near {q : V₁} (hq : q ∈ S.harmonic) :
    ∃ qh : Vh.carrier₁, qh ∈ Vh.toShort.harmonic ∧ ‖q - qh‖ ≤ ‖q - π.π₁ q‖ := by
  sorry

/-- **Discrete harmonic forms are close to harmonic forms** (Arnold, Theorem 5.2):
for `q ∈ 𝔥_h`, `‖q - P_𝔥 q‖ ≤ ‖(1 - π) P_𝔥 q‖`. -/
theorem norm_sub_harmonicPart_le (hB : IsClosed (S.coboundaries : Set V₁))
    {q : Vh.carrier₁} (hq : q ∈ Vh.toShort.harmonic) :
    ‖(q : V₁) - S.harmonicPart q‖ ≤ ‖(S.harmonicPart q : V₁) - π.π₁ (S.harmonicPart q)‖ := by
  sorry

/-- If `‖(1 - π) r‖ ≤ μ ‖r‖` on harmonic forms, then discrete harmonic forms are within
relative distance `μ` of the harmonic forms. -/
theorem norm_sub_harmonicPart_le_mul (hB : IsClosed (S.coboundaries : Set V₁)) {μ : ℝ}
    (hμ : ∀ r ∈ S.harmonic, ‖r - π.π₁ r‖ ≤ μ * ‖r‖)
    {q : Vh.carrier₁} (hq : q ∈ Vh.toShort.harmonic) :
    ‖(q : V₁) - S.harmonicPart q‖ ≤ μ * ‖q‖ := by
  sorry

/-- The component of `u` in `𝔥_h` is small when `u ⟂ 𝔥`: if `u = b + w` with `b ∈ 𝔅`,
`w ∈ 𝔷ᗮ`, then for `q ∈ 𝔥_h` and any discrete `w'`,
`|⟪u, q⟫| ≤ (1 + K) μ ‖b - w'‖ ‖q‖`. This is the consistency term in the error estimate. -/
theorem abs_inner_discrete_harmonic_le (hB : IsClosed (S.coboundaries : Set V₁)) {μ K : ℝ}
    (hμ : ∀ r ∈ S.harmonic, ‖r - π.π₁ r‖ ≤ μ * ‖r‖) (hK : ‖π.π₁‖ ≤ K)
    {u b : V₁} (hb : b ∈ S.coboundaries) (hu : u - b ∈ S.cocyclesᗮ)
    {q : Vh.carrier₁} (hq : q ∈ Vh.toShort.harmonic) {w' : V₁} (hw' : w' ∈ Vh.carrier₁) :
    |⟪S.ι₁ u, S.ι₁ q⟫| ≤ (1 + K) * μ * ‖b - w'‖ * ‖q‖ := by
  sorry

end CochainProjection

end ShortHilbertComplex

end FEEC
