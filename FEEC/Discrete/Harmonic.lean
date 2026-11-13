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
  have hqz : S.d₁ q = 0 := S.d₁_harmonic hq
  have hcl : IsClosed (Vh.carrier₁ : Set V₁) :=
    (completeSpace_coe_iff_isComplete.1 inferInstance).isClosed
  set Z : Submodule ℝ V₁ := S.cocycles ⊓ Vh.carrier₁ with hZ
  have hZc : IsClosed (Z : Set V₁) := by
    rw [hZ, Submodule.coe_inf]; exact S.isClosed_cocycles.inter hcl
  have : CompleteSpace Z := hZc.completeSpace_coe
  set qh₀ : V₁ := Z.starProjection q with hqh₀
  have hmem : qh₀ ∈ Z := Submodule.starProjection_apply_mem _ _
  have horth : ∀ z ∈ Z, ⟪q - qh₀, z⟫ = 0 := fun z hz =>
    Submodule.starProjection_inner_eq_zero _ _ hz
  have hqq : ∀ τ : Vh.carrier₀, ⟪q, S.d₀ τ⟫ = 0 := fun τ => by
    rw [real_inner_comm]
    exact Submodule.inner_right_of_mem_orthogonal (S.d₀_mem_coboundaries τ)
      (Submodule.mem_inf.1 hq).2
  refine ⟨⟨qh₀, hmem.2⟩, Vh.toShort.mem_harmonic_iff.2 ⟨hmem.1, fun τ => ?_⟩, ?_⟩
  · show ⟪S.ι₁ qh₀, S.ι₁ (S.d₀ τ)⟫ = 0
    have hd : S.d₀ τ ∈ Z := ⟨S.coboundaries_le_cocycles (S.d₀_mem_coboundaries _),
      Vh.map_d₀ τ τ.2⟩
    have h1 := horth _ hd
    have h2 := hqq τ
    have h3 : ⟪qh₀, S.d₀ τ⟫ = 0 := by rw [inner_sub_left] at h1; linarith
    rw [← S.inner_eq_of_d₁_eq_zero hmem.1]
    exact h3
  · have hπ : π.π₁ q ∈ Z := ⟨π.d₁_π₁_eq_zero hqz, π.π₁_mem q⟩
    have h1 := horth _ hπ
    have h2 : ⟪q - qh₀, qh₀ - π.π₁ q⟫ = 0 := horth _ (Z.sub_mem hmem hπ)
    have e : q - π.π₁ q = (q - qh₀) + (qh₀ - π.π₁ q) := by abel
    have : ‖q - π.π₁ q‖ ^ 2 = ‖q - qh₀‖ ^ 2 + ‖qh₀ - π.π₁ q‖ ^ 2 := by
      rw [e, norm_add_sq_real, h2]; ring
    refine le_of_sq_le_sq ?_ (norm_nonneg _)
    nlinarith [sq_nonneg ‖qh₀ - π.π₁ q‖]

/-- **Discrete harmonic forms are close to harmonic forms** (Arnold, Theorem 5.2):
for `q ∈ 𝔥_h`, `‖q - P_𝔥 q‖ ≤ ‖(1 - π) P_𝔥 q‖`. -/
theorem norm_sub_harmonicPart_le (hB : IsClosed (S.coboundaries : Set V₁))
    {q : Vh.carrier₁} (hq : q ∈ Vh.toShort.harmonic) :
    ‖(q : V₁) - S.harmonicPart q‖ ≤ ‖(S.harmonicPart q : V₁) - π.π₁ (S.harmonicPart q)‖ := by
  have hQ : S.d₁ (q : V₁) = 0 := (Vh.toShort.harmonic_le_cocycles hq)
  set Q : V₁ := (q : V₁) with hQdef
  set P : V₁ := (S.harmonicPart Q : V₁) with hPdef
  have hPh : P ∈ S.harmonic := (S.harmonicPart Q).2
  have hPo : ∀ x ∈ S.coboundaries, ⟪x, P⟫ = 0 := fun x hx =>
    Submodule.inner_right_of_mem_orthogonal hx (Submodule.mem_inf.1 hPh).2
  obtain ⟨b, hb, w, hw, hu, -⟩ := S.hodge_decomposition hB Q
  have hwz : w ∈ S.cocycles := by
    have : w = Q - b - P := by rw [hu] ; abel
    rw [this]
    exact S.cocycles.sub_mem (S.cocycles.sub_mem hQ (S.coboundaries_le_cocycles hb))
      (S.harmonic_le_cocycles hPh)
  have hw0 : w = 0 := inner_self_eq_zero.1 (Submodule.inner_right_of_mem_orthogonal hwz hw)
  have he : Q - P = b := by rw [hw0, add_zero] at hu; rw [hu]; abel
  obtain ⟨ρ, hρ⟩ := hb
  have hρ' : S.d₀ ρ = b := hρ
  subst hρ'
  have hπe : π.π₁ (S.d₀ ρ) = S.d₀ (⟨π.π₀ ρ, π.π₀_mem ρ⟩ : Vh.carrier₀) := π.comm₀ ρ
  have h1' : ⟪π.π₁ (S.d₀ ρ), S.d₀ ρ⟫ = 0 := by
    have e1 : ⟪π.π₁ (S.d₀ ρ), Q - P⟫ = 0 := by
      rw [hπe, inner_sub_right, real_inner_comm, Vh.inner_harmonic_d₀ hq,
        hPo _ (S.d₀_mem_coboundaries _), sub_zero]
    rwa [he] at e1
  have hπQ : π.π₁ Q = Q := π.π₁_id _ q.2
  have h2 : (S.d₀ ρ) - π.π₁ (S.d₀ ρ) = -(P - π.π₁ P) := by
    rw [← he, map_sub, hπQ]; abel
  rw [he]
  refine norm_le_of_inner_aux (S.d₀ ρ) (-(P - π.π₁ P)) ?_ (by rw [norm_neg])
  rw [← h2, inner_sub_left, h1', sub_zero]

/-- If `‖(1 - π) r‖ ≤ μ ‖r‖` on harmonic forms, then discrete harmonic forms are within
relative distance `μ` of the harmonic forms. -/
theorem norm_sub_harmonicPart_le_mul (hB : IsClosed (S.coboundaries : Set V₁)) {μ : ℝ}
    (hμ : ∀ r ∈ S.harmonic, ‖r - π.π₁ r‖ ≤ μ * ‖r‖)
    {q : Vh.carrier₁} (hq : q ∈ Vh.toShort.harmonic) :
    ‖(q : V₁) - S.harmonicPart q‖ ≤ μ * ‖q‖ := by
  have hP := (S.harmonicPart (q : V₁)).2
  have h1 := π.norm_sub_harmonicPart_le hB hq
  have h2 : ‖(S.harmonicPart (q : V₁) : V₁) - π.π₁ (S.harmonicPart (q : V₁))‖ ≤
      μ * ‖(S.harmonicPart (q : V₁) : V₁)‖ := hμ _ hP
  have h3 : ‖(S.harmonicPart (q : V₁) : V₁)‖ ≤ ‖(q : V₁)‖ :=
    Submodule.norm_orthogonalProjectionOnto_apply_le _ _
  have h4 := h1.trans h2
  have hqn : ‖q‖ = ‖(q : V₁)‖ := rfl
  rw [hqn]
  by_cases h0 : ‖(S.harmonicPart (q : V₁) : V₁)‖ = 0
  · rw [h0, mul_zero] at h4
    have hPz : (S.harmonicPart (q : V₁) : V₁) = 0 := norm_eq_zero.1 h0
    have : (q : V₁) = 0 := by
      rw [hPz, sub_zero] at h4
      exact norm_le_zero_iff.1 h4
    rw [hPz, this]; simp
  · have hpos : 0 < ‖(S.harmonicPart (q : V₁) : V₁)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    have hμ0 : 0 ≤ μ := by
      by_contra hneg
      push_neg at hneg
      have := (norm_nonneg ((S.harmonicPart (q : V₁) : V₁) -
        π.π₁ (S.harmonicPart (q : V₁)))).trans h2
      nlinarith
    calc _ ≤ _ := h4
      _ ≤ μ * ‖(q : V₁)‖ := mul_le_mul_of_nonneg_left h3 hμ0

/-- The component of `u` in `𝔥_h` is small when `u ⟂ 𝔥`: if `u = b + w` with `b ∈ 𝔅`,
`w ∈ 𝔷ᗮ`, then for `q ∈ 𝔥_h` and any discrete `w'`,
`|⟪u, q⟫| ≤ (1 + K) μ ‖b - w'‖ ‖q‖`. This is the consistency term in the error estimate. -/
theorem abs_inner_discrete_harmonic_le (hB : IsClosed (S.coboundaries : Set V₁)) {μ K : ℝ}
    (hμ : ∀ r ∈ S.harmonic, ‖r - π.π₁ r‖ ≤ μ * ‖r‖) (hK : ‖π.π₁‖ ≤ K)
    {u b : V₁} (hb : b ∈ S.coboundaries) (hu : u - b ∈ S.cocyclesᗮ)
    {q : Vh.carrier₁} (hq : q ∈ Vh.toShort.harmonic) {w' : V₁} (hw' : w' ∈ Vh.carrier₁) :
    |⟪S.ι₁ u, S.ι₁ q⟫| ≤ (1 + K) * μ * ‖b - w'‖ * ‖q‖ := by
  have hQ : S.d₁ (q : V₁) = 0 := (Vh.toShort.harmonic_le_cocycles hq)
  set Q : V₁ := (q : V₁) with hQdef
  set P : V₁ := (S.harmonicPart Q : V₁) with hPdef
  have hPh : P ∈ S.harmonic := (S.harmonicPart Q).2
  have hPo : ∀ x ∈ S.coboundaries, ⟪x, P⟫ = 0 := fun x hx =>
    Submodule.inner_right_of_mem_orthogonal hx (Submodule.mem_inf.1 hPh).2
  have hμQ := π.norm_sub_harmonicPart_le_mul hB hμ hq
  have hqn : ‖q‖ = ‖(q : V₁)‖ := rfl
  have hK0 : 0 ≤ K := (norm_nonneg _).trans hK
  have h1 : ⟪S.ι₁ u, S.ι₁ Q⟫ = ⟪b, Q⟫ := by
    rw [← S.inner_eq_of_d₁_eq_zero' hQ u]
    have := Submodule.inner_right_of_mem_orthogonal hQ hu
    rw [inner_sub_right] at this
    have c1 := real_inner_comm Q u
    have c2 := real_inner_comm Q b
    linarith
  obtain ⟨ρ, hρ⟩ := hb
  have hρ' : S.d₀ ρ = b := hρ
  subst hρ'
  have hπe : π.π₁ (S.d₀ ρ) = S.d₀ (⟨π.π₀ ρ, π.π₀_mem ρ⟩ : Vh.carrier₀) := π.comm₀ ρ
  have h2 : ⟪S.d₀ ρ, Q⟫ = ⟪S.d₀ ρ - π.π₁ (S.d₀ ρ), Q - P⟫ := by
    have a1 : ⟪π.π₁ (S.d₀ ρ), Q⟫ = 0 := by
      rw [hπe, real_inner_comm]; exact Vh.inner_harmonic_d₀ hq _
    have a2 : ⟪π.π₁ (S.d₀ ρ), P⟫ = 0 := by
      rw [hπe]; exact hPo _ (S.d₀_mem_coboundaries _)
    have a3 : ⟪S.d₀ ρ, P⟫ = 0 := hPo _ (S.d₀_mem_coboundaries _)
    rw [inner_sub_left, inner_sub_right, inner_sub_right, a1, a2, a3]; ring
  have h3 : ‖S.d₀ ρ - π.π₁ (S.d₀ ρ)‖ ≤ (1 + K) * ‖S.d₀ ρ - w'‖ :=
    π.norm_sub_π₁_le hK _ hw'
  rw [h1, h2]
  have hnn : 0 ≤ μ * ‖Q‖ := (norm_nonneg _).trans hμQ
  calc |⟪S.d₀ ρ - π.π₁ (S.d₀ ρ), Q - P⟫|
      ≤ ‖S.d₀ ρ - π.π₁ (S.d₀ ρ)‖ * ‖Q - P‖ := abs_real_inner_le_norm _ _
    _ ≤ ((1 + K) * ‖S.d₀ ρ - w'‖) * (μ * ‖Q‖) := mul_le_mul h3 hμQ (norm_nonneg _)
        (mul_nonneg (by linarith) (norm_nonneg _))
    _ = (1 + K) * μ * ‖S.d₀ ρ - w'‖ * ‖q‖ := by rw [hqn]; ring

end CochainProjection

end ShortHilbertComplex

end FEEC
