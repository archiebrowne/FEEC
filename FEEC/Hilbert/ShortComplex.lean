/-
Three-term Hilbert complexes: cocycles, coboundaries, harmonic forms, Hodge decomposition.
-/
import Mathlib

/-!
# Short Hilbert complexes

A *short Hilbert complex* is a three-term piece `V₀ --d₀--> V₁ --d₁--> W₂` of the domain
complex of a Hilbert complex (Arnold, *Finite Element Exterior Calculus*, §4.1–4.2).

* `W₀`, `W₁`, `W₂` are the ambient Hilbert spaces ("`L²`");
* `V₀`, `V₁` are the domains of `d`, which are Hilbert spaces in the graph norm, with
  bounded maps `ι₀ : V₀ → W₀`, `ι₁ : V₁ → W₁` (the inclusions);
* `d₀ : V₀ → V₁` and `d₁ : V₁ → W₂` are bounded, with `d₁ ∘ d₀ = 0`;
* the inner products of `V₀`, `V₁` are the graph inner products.

This is all the structure seen by the Hodge Laplacian at the middle level. We do not assume
the inclusions are dense, so that a subcomplex is again a short Hilbert complex.

## Main definitions

* `FEEC.ShortHilbertComplex`
* `ShortHilbertComplex.cocycles` (`𝔷`), `coboundaries` (`𝔅`), `harmonic` (`𝔥`)
* `ShortHilbertComplex.harmonicEquivCohomology`: `𝔥 ≃ 𝔷 ⧸ 𝔅` when `𝔅` is closed.

## Main results

* `ShortHilbertComplex.hodge_decomposition`: if `𝔅` is closed, every `u : V₁` is the sum of
  its orthogonal projections onto `𝔅`, `𝔥` and `𝔷ᗮ` (Arnold, Theorem 4.5).
-/

namespace FEEC

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- A three-term piece `V₀ --d₀--> V₁ --d₁--> W₂` of the domain complex of a Hilbert complex.
The spaces `V₀`, `V₁` carry the graph inner products. -/
structure ShortHilbertComplex (W₀ W₁ W₂ V₀ V₁ : Type*)
    [NormedAddCommGroup W₀] [InnerProductSpace ℝ W₀]
    [NormedAddCommGroup W₁] [InnerProductSpace ℝ W₁]
    [NormedAddCommGroup W₂] [InnerProductSpace ℝ W₂]
    [NormedAddCommGroup V₀] [InnerProductSpace ℝ V₀]
    [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁] where
  /-- The inclusion of the domain `V₀` into the ambient space `W₀`. -/
  ι₀ : V₀ →L[ℝ] W₀
  /-- The inclusion of the domain `V₁` into the ambient space `W₁`. -/
  ι₁ : V₁ →L[ℝ] W₁
  /-- The incoming differential. -/
  d₀ : V₀ →L[ℝ] V₁
  /-- The outgoing differential, with values in the ambient space `W₂`. -/
  d₁ : V₁ →L[ℝ] W₂
  /-- The complex property. -/
  d₁_d₀ : ∀ τ, d₁ (d₀ τ) = 0
  /-- `V₀` carries the graph inner product. -/
  inner_V₀ : ∀ σ τ, ⟪σ, τ⟫ = ⟪ι₀ σ, ι₀ τ⟫ + ⟪ι₁ (d₀ σ), ι₁ (d₀ τ)⟫
  /-- `V₁` carries the graph inner product. -/
  inner_V₁ : ∀ u v, ⟪u, v⟫ = ⟪ι₁ u, ι₁ v⟫ + ⟪d₁ u, d₁ v⟫

namespace ShortHilbertComplex

variable {W₀ W₁ W₂ V₀ V₁ : Type*}
  [NormedAddCommGroup W₀] [InnerProductSpace ℝ W₀]
  [NormedAddCommGroup W₁] [InnerProductSpace ℝ W₁]
  [NormedAddCommGroup W₂] [InnerProductSpace ℝ W₂]
  [NormedAddCommGroup V₀] [InnerProductSpace ℝ V₀]
  [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁]
  (S : ShortHilbertComplex W₀ W₁ W₂ V₀ V₁)

/-! ### Norm identities -/

theorem norm_sq_V₀ (τ : V₀) : ‖τ‖ ^ 2 = ‖S.ι₀ τ‖ ^ 2 + ‖S.ι₁ (S.d₀ τ)‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, S.inner_V₀, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq]

theorem norm_sq_V₁ (u : V₁) : ‖u‖ ^ 2 = ‖S.ι₁ u‖ ^ 2 + ‖S.d₁ u‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, S.inner_V₁, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq]

theorem norm_ι₀_le (τ : V₀) : ‖S.ι₀ τ‖ ≤ ‖τ‖ := by
  refine le_of_sq_le_sq ?_ (norm_nonneg _)
  nlinarith [S.norm_sq_V₀ τ, sq_nonneg ‖S.ι₁ (S.d₀ τ)‖]

theorem norm_ι₁_le (u : V₁) : ‖S.ι₁ u‖ ≤ ‖u‖ := by
  refine le_of_sq_le_sq ?_ (norm_nonneg _)
  nlinarith [S.norm_sq_V₁ u, sq_nonneg ‖S.d₁ u‖]

theorem norm_d₁_le (u : V₁) : ‖S.d₁ u‖ ≤ ‖u‖ := by
  refine le_of_sq_le_sq ?_ (norm_nonneg _)
  nlinarith [S.norm_sq_V₁ u, sq_nonneg ‖S.ι₁ u‖]

/-- On cocycles the `V`- and `W`-inner products agree. -/
theorem inner_eq_of_d₁_eq_zero {z : V₁} (hz : S.d₁ z = 0) (v : V₁) :
    ⟪z, v⟫ = ⟪S.ι₁ z, S.ι₁ v⟫ := by
  rw [S.inner_V₁, hz]; simp

theorem inner_eq_of_d₁_eq_zero' {z : V₁} (hz : S.d₁ z = 0) (v : V₁) :
    ⟪v, z⟫ = ⟪S.ι₁ v, S.ι₁ z⟫ := by
  rw [S.inner_V₁, hz]; simp

theorem norm_eq_of_d₁_eq_zero {z : V₁} (hz : S.d₁ z = 0) : ‖S.ι₁ z‖ = ‖z‖ := by
  have := S.norm_sq_V₁ z
  rw [hz, norm_zero] at this
  have h2 : ‖S.ι₁ z‖ ^ 2 = ‖z‖ ^ 2 := by linarith
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2

/-- `‖d₀ τ‖_V = ‖d₀ τ‖_W`. -/
theorem norm_ι₁_d₀ (τ : V₀) : ‖S.ι₁ (S.d₀ τ)‖ = ‖S.d₀ τ‖ :=
  S.norm_eq_of_d₁_eq_zero (S.d₁_d₀ τ)

theorem norm_d₀_le (τ : V₀) : ‖S.d₀ τ‖ ≤ ‖τ‖ := by
  rw [← S.norm_ι₁_d₀]
  refine le_of_sq_le_sq ?_ (norm_nonneg _)
  nlinarith [S.norm_sq_V₀ τ, sq_nonneg ‖S.ι₀ τ‖]

/-! ### Cocycles, coboundaries, harmonic forms -/

/-- The cocycles `𝔷 = ker d₁ ⊆ V₁`. -/
def cocycles : Submodule ℝ V₁ := LinearMap.ker (S.d₁ : V₁ →ₗ[ℝ] W₂)

/-- The cocycles of the incoming differential, `ker d₀ ⊆ V₀`. -/
def cocycles₀ : Submodule ℝ V₀ := LinearMap.ker (S.d₀ : V₀ →ₗ[ℝ] V₁)

/-- The coboundaries `𝔅 = range d₀ ⊆ V₁`. -/
def coboundaries : Submodule ℝ V₁ := LinearMap.range (S.d₀ : V₀ →ₗ[ℝ] V₁)

/-- The harmonic forms `𝔥 = 𝔷 ∩ 𝔅ᗮ ⊆ V₁`. -/
noncomputable def harmonic : Submodule ℝ V₁ := S.cocycles ⊓ S.coboundariesᗮ

@[simp] theorem mem_cocycles {u : V₁} : u ∈ S.cocycles ↔ S.d₁ u = 0 := Iff.rfl

@[simp] theorem mem_cocycles₀ {τ : V₀} : τ ∈ S.cocycles₀ ↔ S.d₀ τ = 0 := Iff.rfl

theorem mem_coboundaries {u : V₁} : u ∈ S.coboundaries ↔ ∃ τ, S.d₀ τ = u := Iff.rfl

theorem d₀_mem_coboundaries (τ : V₀) : S.d₀ τ ∈ S.coboundaries := ⟨τ, rfl⟩

theorem coboundaries_le_cocycles : S.coboundaries ≤ S.cocycles := by
  rintro _ ⟨τ, rfl⟩
  exact S.d₁_d₀ τ

/-- Harmonic forms are the cocycles which are `W`-orthogonal to the coboundaries. -/
theorem mem_harmonic_iff {p : V₁} :
    p ∈ S.harmonic ↔ S.d₁ p = 0 ∧ ∀ τ, ⟪S.ι₁ p, S.ι₁ (S.d₀ τ)⟫ = 0 := by
  unfold harmonic
  rw [Submodule.mem_inf, mem_cocycles, Submodule.mem_orthogonal]
  refine and_congr_right fun hp => ⟨fun h τ => ?_, fun h u hu => ?_⟩
  · have := h _ (S.d₀_mem_coboundaries τ)
    rwa [S.inner_eq_of_d₁_eq_zero' hp, real_inner_comm] at this
  · obtain ⟨τ, rfl⟩ := hu
    rw [S.inner_eq_of_d₁_eq_zero' hp, real_inner_comm]
    exact h τ

theorem harmonic_le_cocycles : S.harmonic ≤ S.cocycles := inf_le_left

theorem d₁_harmonic {p : V₁} (hp : p ∈ S.harmonic) : S.d₁ p = 0 := S.harmonic_le_cocycles hp

theorem inner_ι₁_harmonic_d₀ {p : V₁} (hp : p ∈ S.harmonic) (τ : V₀) :
    ⟪S.ι₁ p, S.ι₁ (S.d₀ τ)⟫ = 0 :=
  (S.mem_harmonic_iff.1 hp).2 τ

theorem inner_ι₁_d₀_harmonic {p : V₁} (hp : p ∈ S.harmonic) (τ : V₀) :
    ⟪S.ι₁ (S.d₀ τ), S.ι₁ p⟫ = 0 := by
  rw [real_inner_comm]; exact S.inner_ι₁_harmonic_d₀ hp τ

theorem isClosed_cocycles : IsClosed (S.cocycles : Set V₁) := by
  exact ContinuousLinearMap.isClosed_ker S.d₁

theorem isClosed_cocycles₀ : IsClosed (S.cocycles₀ : Set V₀) := by
  exact ContinuousLinearMap.isClosed_ker S.d₀

theorem isClosed_harmonic : IsClosed (S.harmonic : Set V₁) := by
  unfold harmonic
  rw [Submodule.coe_inf]
  exact S.isClosed_cocycles.inter (Submodule.isClosed_orthogonal _)

/-- Elements of `𝔷ᗮ` are `W`-orthogonal to cocycles. -/
theorem inner_ι₁_eq_zero_of_mem_cocycles_orthogonal {z w : V₁} (hz : S.d₁ z = 0)
    (hw : w ∈ S.cocyclesᗮ) : ⟪S.ι₁ z, S.ι₁ w⟫ = 0 := by
  rw [← S.inner_eq_of_d₁_eq_zero hz]
  exact Submodule.inner_right_of_mem_orthogonal hz hw

section Complete

variable [CompleteSpace V₀] [CompleteSpace V₁]

instance : CompleteSpace S.cocycles := S.isClosed_cocycles.completeSpace_coe
instance : CompleteSpace S.cocycles₀ := S.isClosed_cocycles₀.completeSpace_coe
instance : CompleteSpace S.harmonic := S.isClosed_harmonic.completeSpace_coe

/-- The harmonic part `P_𝔥 u` of `u`, as an element of `𝔥`. -/
noncomputable def harmonicPart (u : V₁) : S.harmonic := S.harmonic.orthogonalProjectionOnto u

/-- **Hodge decomposition** (Arnold, Theorem 4.5). If the coboundaries `𝔅` are closed, then
`V₁ = 𝔅 ⊕ 𝔥 ⊕ 𝔷ᗮ`: there are `b ∈ 𝔅`, `p ∈ 𝔥`, `w ∈ 𝔷ᗮ` with `u = b + p + w`. The
decomposition is orthogonal for the `V`-inner product (and also for the `W`-inner product),
and is unique. Here `p = S.harmonicPart u`. -/
theorem hodge_decomposition (hB : IsClosed (S.coboundaries : Set V₁)) (u : V₁) :
    ∃ b ∈ S.coboundaries, ∃ w ∈ S.cocyclesᗮ,
      u = b + S.harmonicPart u + w ∧
      ‖u‖ ^ 2 = ‖b‖ ^ 2 + ‖(S.harmonicPart u : V₁)‖ ^ 2 + ‖w‖ ^ 2 := by
  have := hB.completeSpace_coe
  set z := S.cocycles.starProjection u with hz
  set b := S.coboundaries.starProjection u with hb
  have hzmem : z ∈ S.cocycles := Submodule.starProjection_apply_mem _ _
  have hbmem : b ∈ S.coboundaries := Submodule.starProjection_apply_mem _ _
  have hwmem : u - z ∈ S.cocyclesᗮ := Submodule.sub_starProjection_mem_orthogonal _
  have hbz : b ∈ S.cocycles := S.coboundaries_le_cocycles hbmem
  have hbo : ∀ c ∈ S.coboundaries, ⟪c, u - b⟫ = 0 := fun c hc => by
    rw [real_inner_comm]; exact Submodule.starProjection_inner_eq_zero _ _ hc
  have hzo : ∀ c ∈ S.cocycles, ⟪c, u - z⟫ = 0 := fun c hc => by
    rw [real_inner_comm]; exact Submodule.starProjection_inner_eq_zero _ _ hc
  have hzb : z - b ∈ S.harmonic := by
    refine ⟨S.cocycles.sub_mem hzmem hbz, ?_⟩
    show z - b ∈ S.coboundariesᗮ
    rw [Submodule.mem_orthogonal]
    intro c hc
    have h1 := hbo c hc
    have h2 := hzo c (S.coboundaries_le_cocycles hc)
    have : z - b = (u - b) - (u - z) := by abel
    rw [this, inner_sub_right, h1, h2, sub_zero]
  have hP : (S.harmonicPart u : V₁) = z - b := by
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero hzb fun q hq => ?_
    have hq' := (Submodule.mem_inf.1 hq)
    have : u - (z - b) = (u - z) + b := by abel
    rw [this, inner_add_left, real_inner_comm, hzo q hq'.1, zero_add,
      Submodule.inner_right_of_mem_orthogonal hbmem hq'.2]
  refine ⟨b, hbmem, u - z, hwmem, ?_, ?_⟩
  · rw [hP]; abel
  · rw [hP]
    have e1 : ‖u‖ ^ 2 = ‖z‖ ^ 2 + ‖u - z‖ ^ 2 := by
      have := norm_add_sq_real z (u - z)
      have h0 : ⟪z, u - z⟫ = 0 := hzo z hzmem
      rw [h0] at this
      simp only [add_sub_cancel] at this
      linarith
    have e2 : ‖z‖ ^ 2 = ‖b‖ ^ 2 + ‖z - b‖ ^ 2 := by
      have := norm_add_sq_real b (z - b)
      have h0 : ⟪b, z - b⟫ = 0 := by
        have h1 := hbo b hbmem
        have h2 := hzo b hbz
        have : z - b = (u - b) - (u - z) := by abel
        rw [this, inner_sub_right, h1, h2, sub_zero]
      rw [h0] at this
      simp only [add_sub_cancel] at this
      linarith
    linarith

/-- Uniqueness in the Hodge decomposition. -/
theorem hodge_decomposition_unique {b p w b' p' w' : V₁}
    (hb : b ∈ S.coboundaries) (hp : p ∈ S.harmonic) (hw : w ∈ S.cocyclesᗮ)
    (hb' : b' ∈ S.coboundaries) (hp' : p' ∈ S.harmonic) (hw' : w' ∈ S.cocyclesᗮ)
    (h : b + p + w = b' + p' + w') : b = b' ∧ p = p' ∧ w = w' := by
  have hBH : ∀ {x y : V₁}, x ∈ S.coboundaries → y ∈ S.harmonic → ⟪x, y⟫ = 0 :=
    fun hx hy => Submodule.inner_right_of_mem_orthogonal hx (Submodule.mem_inf.1 hy).2
  have hBW : ∀ {x y : V₁}, x ∈ S.coboundaries → y ∈ S.cocyclesᗮ → ⟪x, y⟫ = 0 :=
    fun hx hy => Submodule.inner_right_of_mem_orthogonal (S.coboundaries_le_cocycles hx) hy
  have hHW : ∀ {x y : V₁}, x ∈ S.harmonic → y ∈ S.cocyclesᗮ → ⟪x, y⟫ = 0 :=
    fun hx hy => Submodule.inner_right_of_mem_orthogonal (S.harmonic_le_cocycles hx) hy
  have hs : (b - b') + (p - p') + (w - w') = 0 := by
    rw [show (b - b') + (p - p') + (w - w') = (b + p + w) - (b' + p' + w') by abel, h, sub_self]
  have hx : b - b' ∈ S.coboundaries := S.coboundaries.sub_mem hb hb'
  have hy : p - p' ∈ S.harmonic := S.harmonic.sub_mem hp hp'
  have hv : w - w' ∈ S.cocyclesᗮ := S.cocyclesᗮ.sub_mem hw hw'
  have hxy := hBH hx hy
  have hxv := hBW hx hv
  have hyv := hHW hy hv
  have h1 : ‖b - b'‖ ^ 2 = 0 := by
    have := congrArg (fun t => ⟪b - b', t⟫) hs
    simp only [inner_add_right, inner_zero_right, hxy, hxv, add_zero] at this
    rwa [real_inner_self_eq_norm_sq] at this
  have h2 : ‖p - p'‖ ^ 2 = 0 := by
    have := congrArg (fun t => ⟪p - p', t⟫) hs
    simp only [inner_add_right, inner_zero_right, hyv, real_inner_comm (b - b') (p - p') ▸ hxy,
      zero_add, add_zero] at this
    rwa [real_inner_self_eq_norm_sq] at this
  have h3 : ‖w - w'‖ ^ 2 = 0 := by
    have := congrArg (fun t => ⟪w - w', t⟫) hs
    simp only [inner_add_right, inner_zero_right, real_inner_comm (b - b') (w - w') ▸ hxv,
      real_inner_comm (p - p') (w - w') ▸ hyv, zero_add] at this
    rwa [real_inner_self_eq_norm_sq] at this
  refine ⟨sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h1)),
    sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)),
    sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h3))⟩

/-- If `𝔅` is closed, the cocycles decompose as `𝔷 = 𝔅 ⊕ 𝔥`. -/
theorem cocycles_eq_coboundaries_sup_harmonic (hB : IsClosed (S.coboundaries : Set V₁)) :
    S.cocycles = S.coboundaries ⊔ S.harmonic := by
  refine le_antisymm (fun z hz => ?_)
    (sup_le S.coboundaries_le_cocycles S.harmonic_le_cocycles)
  obtain ⟨b, hb, w, hw, hu, -⟩ := S.hodge_decomposition hB z
  have hp := S.harmonic_le_cocycles (S.harmonicPart z).2
  have hwz : w ∈ S.cocycles := by
    have : w = z - b - S.harmonicPart z :=
      calc w = (w + S.harmonicPart z + b) - b - S.harmonicPart z := by abel
        _ = z - b - S.harmonicPart z := by rw [show w + S.harmonicPart z + b = z from
          (by abel : w + S.harmonicPart z + b = b + S.harmonicPart z + w).trans hu.symm]
    rw [this]
    exact S.cocycles.sub_mem (S.cocycles.sub_mem hz (S.coboundaries_le_cocycles hb)) hp
  have hw0 : w = 0 := by
    have := Submodule.inner_right_of_mem_orthogonal hwz hw
    exact inner_self_eq_zero.1 this
  rw [hw0, add_zero] at hu
  rw [hu]
  exact Submodule.add_mem_sup hb (S.harmonicPart z).2

theorem coboundaries_disjoint_harmonic : Disjoint S.coboundaries S.harmonic := by
  rw [Submodule.disjoint_def]
  intro x hx hx'
  exact inner_self_eq_zero.1
    (Submodule.inner_right_of_mem_orthogonal hx (Submodule.mem_inf.1 hx').2)

/-- **Harmonic forms represent cohomology**: if `𝔅` is closed then `𝔥 ≃ 𝔷 ⧸ 𝔅`
(Arnold, §4.2). The cohomology is written as the quotient of `𝔷` by `𝔅` viewed inside `𝔷`. -/
noncomputable def harmonicEquivCohomology (hB : IsClosed (S.coboundaries : Set V₁)) :
    S.harmonic ≃ₗ[ℝ] (S.cocycles ⧸ S.coboundaries.comap S.cocycles.subtype) := by
  refine LinearEquiv.ofBijective
    ((Submodule.mkQ _).comp (Submodule.inclusion S.harmonic_le_cocycles)) ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply,
      Submodule.coe_inclusion] at hp
    have : (p : V₁) = 0 :=
      Submodule.disjoint_def.1 S.coboundaries_disjoint_harmonic _ hp p.2
    exact Subtype.ext this
  · intro q
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have hz : (z : V₁) ∈ S.coboundaries ⊔ S.harmonic := by
      rw [← S.cocycles_eq_coboundaries_sup_harmonic hB]; exact z.2
    obtain ⟨b, hb, p, hp, hbp⟩ := Submodule.mem_sup.1 hz
    refine ⟨⟨p, hp⟩, ?_⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply]
    rw [Submodule.Quotient.eq]
    change (p : V₁) - (z : V₁) ∈ S.coboundaries
    have : (p : V₁) - z = -b := by rw [← hbp]; abel
    rw [this]
    exact S.coboundaries.neg_mem hb

theorem harmonicEquivCohomology_apply (hB : IsClosed (S.coboundaries : Set V₁))
    (p : S.harmonic) :
    S.harmonicEquivCohomology hB p =
      Submodule.Quotient.mk ⟨p, S.harmonic_le_cocycles p.2⟩ := by
  rfl

end Complete

end ShortHilbertComplex

end FEEC
