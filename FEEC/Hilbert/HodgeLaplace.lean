/-
The abstract Hodge Laplacian in mixed weak form and its well-posedness.
-/
import FEEC.Hilbert.Poincare
import FEEC.Hilbert.InfSup

/-!
# The abstract Hodge Laplacian (mixed weak formulation)

For a short Hilbert complex `V₀ --d₀--> V₁ --d₁--> W₂` and `f : W₁`, the mixed weak
formulation of the Hodge Laplace problem (Arnold, §4.4, eq. (4.18)) is: find
`σ : V₀`, `u : V₁`, `p ∈ 𝔥` with

* `⟪σ, τ⟫ - ⟪d₀ τ, u⟫ = 0` for all `τ : V₀`,
* `⟪d₀ σ, v⟫ + ⟪d₁ u, d₁ v⟫ + ⟪p, v⟫ = ⟪f, v⟫` for all `v : V₁`,
* `⟪u, q⟫ = 0` for all `q ∈ 𝔥`,

where all inner products are `W`-inner products.

## Main results

* `ShortHilbertComplex.IsGenSolution.norm_le`: the a priori estimate (equivalent to the
  inf-sup condition of Arnold, Theorem 4.9), with the explicit constant `stabilityConst c`
  depending only on the Poincaré constant `c`.
* `ShortHilbertComplex.existsUnique_isGenSolution`, `existsUnique_isSolution`:
  well-posedness (Arnold, Theorem 4.8).
-/

namespace FEEC

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- The stability constant of the mixed Hodge Laplace problem as a function of the Poincaré
constant. -/
noncomputable def stabilityConst (c : ℝ) : ℝ := 18 * (max c 1) ^ 2

theorem stabilityConst_pos (c : ℝ) : 0 < stabilityConst c := by
  unfold stabilityConst; positivity

theorem stabilityConst_mono {c c' : ℝ} (h : c ≤ c') : stabilityConst c ≤ stabilityConst c' := by
  unfold stabilityConst
  gcongr

namespace ShortHilbertComplex

variable {W₀ W₁ W₂ V₀ V₁ : Type*}
  [NormedAddCommGroup W₀] [InnerProductSpace ℝ W₀]
  [NormedAddCommGroup W₁] [InnerProductSpace ℝ W₁]
  [NormedAddCommGroup W₂] [InnerProductSpace ℝ W₂]
  [NormedAddCommGroup V₀] [InnerProductSpace ℝ V₀]
  [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁]
  (S : ShortHilbertComplex W₀ W₁ W₂ V₀ V₁)

/-- The mixed weak formulation of the Hodge Laplace problem with general right-hand sides
`F₀ ∈ V₀*`, `F₁ ∈ V₁*`, `F₂ ∈ 𝔥*`. -/
structure IsGenSolution (F₀ : V₀ →L[ℝ] ℝ) (F₁ : V₁ →L[ℝ] ℝ) (F₂ : S.harmonic →L[ℝ] ℝ)
    (σ : V₀) (u : V₁) (p : S.harmonic) : Prop where
  eq₀ : ∀ τ : V₀, ⟪S.ι₀ σ, S.ι₀ τ⟫ - ⟪S.ι₁ (S.d₀ τ), S.ι₁ u⟫ = F₀ τ
  eq₁ : ∀ v : V₁, ⟪S.ι₁ (S.d₀ σ), S.ι₁ v⟫ + ⟪S.d₁ u, S.d₁ v⟫ + ⟪S.ι₁ p, S.ι₁ v⟫ = F₁ v
  eq₂ : ∀ q : S.harmonic, ⟪S.ι₁ u, S.ι₁ q⟫ = F₂ q

/-- The mixed weak formulation of the Hodge Laplace problem with data `f : W₁`
(Arnold, eq. (4.18)): `σ = d* u`, `d σ + d* d u + p = f`, `u ⟂ 𝔥`. -/
structure IsSolution (f : W₁) (σ : V₀) (u : V₁) (p : V₁) : Prop where
  harmonic : p ∈ S.harmonic
  eq₀ : ∀ τ : V₀, ⟪S.ι₀ σ, S.ι₀ τ⟫ - ⟪S.ι₁ (S.d₀ τ), S.ι₁ u⟫ = 0
  eq₁ : ∀ v : V₁, ⟪S.ι₁ (S.d₀ σ), S.ι₁ v⟫ + ⟪S.d₁ u, S.d₁ v⟫ + ⟪S.ι₁ p, S.ι₁ v⟫ = ⟪f, S.ι₁ v⟫
  eq₂ : ∀ q ∈ S.harmonic, ⟪S.ι₁ u, S.ι₁ q⟫ = 0

/-- The load functional `v ↦ ⟪f, v⟫_W` on `V₁`. -/
noncomputable def load (f : W₁) : V₁ →L[ℝ] ℝ := (innerSL ℝ f).comp S.ι₁

@[simp] theorem load_apply (f : W₁) (v : V₁) : S.load f v = ⟪f, S.ι₁ v⟫ := rfl

theorem norm_load_le (f : W₁) : ‖S.load f‖ ≤ ‖f‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
  rw [load_apply]
  calc ‖⟪f, S.ι₁ v⟫‖ ≤ ‖f‖ * ‖S.ι₁ v‖ := norm_inner_le_norm _ _
    _ ≤ ‖f‖ * ‖v‖ := by gcongr; exact S.norm_ι₁_le v

theorem isSolution_iff_isGenSolution {f : W₁} {σ : V₀} {u : V₁} {p : S.harmonic} :
    S.IsSolution f σ u p ↔ S.IsGenSolution 0 (S.load f) 0 σ u p := by
  constructor
  · intro h
    exact ⟨fun τ => by simpa using h.eq₀ τ, fun v => by simpa using h.eq₁ v,
      fun q => by simpa using h.eq₂ q q.2⟩
  · intro h
    exact ⟨p.2, fun τ => by simpa using h.eq₀ τ, fun v => by simpa using h.eq₁ v,
      fun q hq => by simpa using h.eq₂ ⟨q, hq⟩⟩

variable {S}

/-! ### The ambient Hilbert space for the existence proof -/

/-- The Hilbert space `V₀ × V₁ × 𝔥` (with the `L²`-product norm) in which the mixed problem is
posed as a single symmetric bilinear equation. -/
abbrev GenSpace (S : ShortHilbertComplex W₀ W₁ W₂ V₀ V₁) :=
  WithLp 2 (V₀ × WithLp 2 (V₁ × S.harmonic))

namespace GenSpace

variable (S)

/-- The identification of `GenSpace S` with the plain product. -/
noncomputable def Φ : GenSpace S ≃L[ℝ] V₀ × (V₁ × S.harmonic) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ V₀ (WithLp 2 (V₁ × S.harmonic))).trans
    (ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ V₀)
      (WithLp.prodContinuousLinearEquiv 2 ℝ V₁ S.harmonic))

/-- First projection. -/
noncomputable def π₀ : GenSpace S →L[ℝ] V₀ :=
  (ContinuousLinearMap.fst ℝ V₀ (V₁ × S.harmonic)).comp (Φ S : GenSpace S →L[ℝ] _)

/-- Second projection. -/
noncomputable def π₁ : GenSpace S →L[ℝ] V₁ :=
  ((ContinuousLinearMap.fst ℝ V₁ S.harmonic).comp
    (ContinuousLinearMap.snd ℝ V₀ (V₁ × S.harmonic))).comp (Φ S : GenSpace S →L[ℝ] _)

/-- Third projection. -/
noncomputable def π₂ : GenSpace S →L[ℝ] S.harmonic :=
  ((ContinuousLinearMap.snd ℝ V₁ S.harmonic).comp
    (ContinuousLinearMap.snd ℝ V₀ (V₁ × S.harmonic))).comp (Φ S : GenSpace S →L[ℝ] _)

/-- First inclusion. -/
noncomputable def e₀ : V₀ →L[ℝ] GenSpace S :=
  ((Φ S).symm : V₀ × (V₁ × S.harmonic) →L[ℝ] GenSpace S).comp
    (ContinuousLinearMap.inl ℝ V₀ (V₁ × S.harmonic))

/-- Second inclusion. -/
noncomputable def e₁ : V₁ →L[ℝ] GenSpace S :=
  ((Φ S).symm : V₀ × (V₁ × S.harmonic) →L[ℝ] GenSpace S).comp
    ((ContinuousLinearMap.inr ℝ V₀ (V₁ × S.harmonic)).comp
      (ContinuousLinearMap.inl ℝ V₁ S.harmonic))

/-- Third inclusion. -/
noncomputable def e₂ : S.harmonic →L[ℝ] GenSpace S :=
  ((Φ S).symm : V₀ × (V₁ × S.harmonic) →L[ℝ] GenSpace S).comp
    ((ContinuousLinearMap.inr ℝ V₀ (V₁ × S.harmonic)).comp
      (ContinuousLinearMap.inr ℝ V₁ S.harmonic))

section
variable {S}
@[simp] theorem π₀_e₀ (τ : V₀) : π₀ S (e₀ S τ) = τ := rfl
@[simp] theorem π₁_e₀ (τ : V₀) : π₁ S (e₀ S τ) = 0 := rfl
@[simp] theorem π₂_e₀ (τ : V₀) : π₂ S (e₀ S τ) = 0 := rfl
@[simp] theorem π₀_e₁ (v : V₁) : π₀ S (e₁ S v) = 0 := rfl
@[simp] theorem π₁_e₁ (v : V₁) : π₁ S (e₁ S v) = v := rfl
@[simp] theorem π₂_e₁ (v : V₁) : π₂ S (e₁ S v) = 0 := rfl
@[simp] theorem π₀_e₂ (q : S.harmonic) : π₀ S (e₂ S q) = 0 := rfl
@[simp] theorem π₁_e₂ (q : S.harmonic) : π₁ S (e₂ S q) = 0 := rfl
@[simp] theorem π₂_e₂ (q : S.harmonic) : π₂ S (e₂ S q) = q := rfl

theorem norm_sq_eq (x : GenSpace S) :
    ‖x‖ ^ 2 = ‖π₀ S x‖ ^ 2 + ‖π₁ S x‖ ^ 2 + ‖π₂ S x‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
  have e0 : π₀ S x = WithLp.fst x := rfl
  have e1 : π₁ S x = (WithLp.snd x).fst := rfl
  have e2 : π₂ S x = (WithLp.snd x).snd := rfl
  rw [e0, e1, e2]; ring

theorem norm_e₀ (τ : V₀) : ‖e₀ S τ‖ = ‖τ‖ := by
  have h := norm_sq_eq (e₀ S τ)
  simp only [π₀_e₀, π₁_e₀, π₂_e₀, norm_zero] at h
  nlinarith [norm_nonneg (e₀ S τ), norm_nonneg τ]

theorem norm_e₁ (v : V₁) : ‖e₁ S v‖ = ‖v‖ := by
  have h := norm_sq_eq (e₁ S v)
  simp only [π₀_e₁, π₁_e₁, π₂_e₁, norm_zero] at h
  nlinarith [norm_nonneg (e₁ S v), norm_nonneg v]

theorem norm_e₂ (q : S.harmonic) : ‖e₂ S q‖ = ‖q‖ := by
  have h := norm_sq_eq (e₂ S q)
  simp only [π₀_e₂, π₁_e₂, π₂_e₂, norm_zero] at h
  nlinarith [norm_nonneg (e₂ S q), norm_nonneg q]

theorem norm_le_sum (x : GenSpace S) : ‖x‖ ≤ ‖π₀ S x‖ + ‖π₁ S x‖ + ‖π₂ S x‖ := by
  have h := norm_sq_eq x
  by_contra hlt
  push_neg at hlt
  nlinarith [norm_nonneg (π₀ S x), norm_nonneg (π₁ S x), norm_nonneg (π₂ S x), norm_nonneg x]
end

/-- The symmetric bilinear form of the mixed Hodge Laplace problem on `GenSpace S`. -/
noncomputable def form : GenSpace S →L[ℝ] GenSpace S →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp (S.ι₀ ∘L π₀ S) (S.ι₀ ∘L π₀ S)
  - (innerSL ℝ).bilinearComp (S.ι₁ ∘L π₁ S) (S.ι₁ ∘L S.d₀ ∘L π₀ S)
  - (innerSL ℝ).bilinearComp (S.ι₁ ∘L S.d₀ ∘L π₀ S) (S.ι₁ ∘L π₁ S)
  - (innerSL ℝ).bilinearComp (S.d₁ ∘L π₁ S) (S.d₁ ∘L π₁ S)
  - (innerSL ℝ).bilinearComp (S.ι₁ ∘L S.harmonic.subtypeL ∘L π₂ S) (S.ι₁ ∘L π₁ S)
  - (innerSL ℝ).bilinearComp (S.ι₁ ∘L π₁ S) (S.ι₁ ∘L S.harmonic.subtypeL ∘L π₂ S)

theorem form_apply (x y : GenSpace S) :
    form S x y = ⟪S.ι₀ (π₀ S x), S.ι₀ (π₀ S y)⟫ - ⟪S.ι₁ (π₁ S x), S.ι₁ (S.d₀ (π₀ S y))⟫
      - ⟪S.ι₁ (S.d₀ (π₀ S x)), S.ι₁ (π₁ S y)⟫ - ⟪S.d₁ (π₁ S x), S.d₁ (π₁ S y)⟫
      - ⟪S.ι₁ (π₂ S x : V₁), S.ι₁ (π₁ S y)⟫ - ⟪S.ι₁ (π₁ S x), S.ι₁ (π₂ S y : V₁)⟫ := by
  simp [form, ContinuousLinearMap.bilinearComp_apply, innerSL_apply_apply]

theorem form_symm (x y : GenSpace S) : form S x y = form S y x := by
  rw [form_apply, form_apply, real_inner_comm (S.ι₀ (π₀ S x)),
    real_inner_comm (S.d₁ (π₁ S x)), real_inner_comm (S.ι₁ (π₁ S x)) (S.ι₁ (S.d₀ (π₀ S y))),
    real_inner_comm (S.ι₁ (S.d₀ (π₀ S x))) (S.ι₁ (π₁ S y)),
    real_inner_comm (S.ι₁ (π₂ S x : V₁)) (S.ι₁ (π₁ S y)),
    real_inner_comm (S.ι₁ (π₁ S x)) (S.ι₁ (π₂ S y : V₁))]
  ring

end GenSpace

section Complete

variable [CompleteSpace V₀] [CompleteSpace V₁]

theorem hodge_real_aux {a s0 s1 nb nh nw np d A f nσ nu : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hA2 : a * A ≤ s0 ^ 2 / 2 + a * nb ^ 2 / 2) (hw2 : a * nw ^ 2 ≤ d ^ 2)
    (hsum : f = s0 ^ 2 - a * A + a * nb ^ 2 + s1 ^ 2 + d ^ 2 + np ^ 2 + nh ^ 2)
    (hσ : nσ ^ 2 = s0 ^ 2 + s1 ^ 2) (hu : nu ^ 2 = nb ^ 2 + nh ^ 2 + nw ^ 2) :
    a * (nσ + nu + np) ^ 2 ≤ 6 * f := by
  have h1 : 0 ≤ 1 - a := sub_nonneg.2 ha1
  have key : a * (nσ ^ 2 + nu ^ 2 + np ^ 2) ≤ 2 * f := by
    rw [hσ, hu]
    nlinarith [mul_nonneg h1 (sq_nonneg s0), mul_nonneg h1 (sq_nonneg s1),
      mul_nonneg h1 (sq_nonneg np), mul_nonneg h1 (sq_nonneg nh), mul_nonneg h1 (sq_nonneg nw),
      mul_nonneg h1 (sq_nonneg nb)]
  nlinarith [mul_nonneg ha0.le (sq_nonneg (nσ - nu)), mul_nonneg ha0.le (sq_nonneg (nσ - np)),
    mul_nonneg ha0.le (sq_nonneg (nu - np))]

set_option maxHeartbeats 1600000 in
/-- **A priori estimate for the mixed Hodge Laplacian** (the inf-sup condition of Arnold,
Theorem 4.9, in the form of a stability estimate). The constant depends only on the Poincaré
constant. -/
theorem IsGenSolution.norm_le {c : ℝ} (hc : S.HasPoincareConst c)
    {F₀ : V₀ →L[ℝ] ℝ} {F₁ : V₁ →L[ℝ] ℝ} {F₂ : S.harmonic →L[ℝ] ℝ}
    {σ : V₀} {u : V₁} {p : S.harmonic} (h : S.IsGenSolution F₀ F₁ F₂ σ u p) :
    ‖σ‖ + ‖u‖ + ‖p‖ ≤ stabilityConst c * (‖F₀‖ + ‖F₁‖ + ‖F₂‖) := by
  have hc1 : (1 : ℝ) ≤ max c 1 := le_max_right _ _
  have hcp : S.HasPoincareConst (max c 1) := hc.mono (le_max_left _ _)
  have hstab : stabilityConst c = 18 * (max c 1) ^ 2 := rfl
  generalize max c 1 = c' at hc1 hcp hstab
  have hcpos : 0 < c' := by linarith
  obtain ⟨b, hb, w, hw, hu, hnorm⟩ := S.hodge_decomposition hcp.isClosed_coboundaries u
  obtain ⟨ρ, hρ, hρn⟩ := hcp.exists_potential hb
  generalize hhh : S.harmonicPart u = hh at hu hnorm
  have hhm : (hh : V₁) ∈ S.harmonic := hh.2
  have hd1b : S.d₁ b = 0 := S.coboundaries_le_cocycles hb
  have hd1h : S.d₁ (hh : V₁) = 0 := S.d₁_harmonic hhm
  have hd1p : S.d₁ (p : V₁) = 0 := S.d₁_harmonic p.2
  have hd1w : S.d₁ u = S.d₁ w := by
    rw [hu, map_add, map_add, hd1b, hd1h]; simp
  have hι : S.ι₁ u = S.ι₁ b + S.ι₁ hh + S.ι₁ w := by
    rw [hu]; simp only [map_add]
  have hbh : ⟪S.ι₁ b, S.ι₁ (hh : V₁)⟫ = 0 := by
    obtain ⟨τ, hτ⟩ := S.mem_coboundaries.1 hb
    rw [← hτ]; exact S.inner_ι₁_d₀_harmonic hhm τ
  have hbw : ⟪S.ι₁ b, S.ι₁ w⟫ = 0 := S.inner_ι₁_eq_zero_of_mem_cocycles_orthogonal hd1b hw
  have hhw : ⟪S.ι₁ (hh : V₁), S.ι₁ w⟫ = 0 := S.inner_ι₁_eq_zero_of_mem_cocycles_orthogonal hd1h hw
  have hnb : ‖S.ι₁ b‖ = ‖b‖ := S.norm_eq_of_d₁_eq_zero hd1b
  have hnh : ‖S.ι₁ (hh : V₁)‖ = ‖(hh : V₁)‖ := S.norm_eq_of_d₁_eq_zero hd1h
  have hbu : ⟪S.ι₁ b, S.ι₁ u⟫ = ‖b‖ ^ 2 := by
    rw [hι, inner_add_right, inner_add_right, hbh, hbw, real_inner_self_eq_norm_sq, hnb]; ring
  have hhu : ⟪S.ι₁ u, S.ι₁ (hh : V₁)⟫ = ‖(hh : V₁)‖ ^ 2 := by
    rw [hι, inner_add_left, inner_add_left, hbh, real_inner_comm (S.ι₁ (hh : V₁)) (S.ι₁ w), hhw,
      real_inner_self_eq_norm_sq, hnh]; ring
  have hnp : ‖S.ι₁ (p : V₁)‖ = ‖(p : V₁)‖ := S.norm_eq_of_d₁_eq_zero hd1p
  have hpp : ⟪S.ι₁ (S.d₀ σ), S.ι₁ (p : V₁)⟫ = 0 := S.inner_ι₁_d₀_harmonic p.2 σ
  have hpp' : ⟪S.ι₁ (p : V₁), S.ι₁ (S.d₀ σ)⟫ = 0 := S.inner_ι₁_harmonic_d₀ p.2 σ
  have hYc := real_inner_comm (S.ι₁ (p : V₁)) (S.ι₁ u)
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 1 / c' ^ 2 := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; positivity
  have hac : a * c' ^ 2 = 1 := by rw [ha]; field_simp
  have hc2 : 1 ≤ c' ^ 2 := by nlinarith
  have ha1 : a ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_left hc2 ha0.le]
  have hac1 : a * c' ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_left (show c' ≤ c' ^ 2 by nlinarith) ha0.le]
  have E0 := h.eq₀ (σ - a • ρ)
  have E1 := h.eq₁ (u + S.d₀ σ + (p : V₁))
  have E2 := h.eq₂ (hh - p)
  obtain ⟨f0, hf0⟩ : ∃ f, f = F₀ (σ - a • ρ) := ⟨_, rfl⟩
  obtain ⟨f1, hf1⟩ : ∃ f, f = F₁ (u + S.d₀ σ + (p : V₁)) := ⟨_, rfl⟩
  obtain ⟨f2, hf2⟩ : ∃ f, f = F₂ (hh - p) := ⟨_, rfl⟩
  rw [← hf0] at E0
  rw [← hf1] at E1
  rw [← hf2] at E2
  simp only [map_sub, map_add, map_smul, inner_add_right, inner_sub_right, inner_add_left,
    inner_sub_left, real_inner_smul_right, real_inner_smul_left, hρ, S.d₁_d₀, hd1p,
    inner_zero_right, add_zero, Submodule.coe_sub, real_inner_self_eq_norm_sq] at E0 E1 E2
  -- real-number bookkeeping
  have sqle : ∀ x y : ℝ, 0 ≤ y → x ^ 2 ≤ y ^ 2 → x ≤ y :=
    fun x y hy h => (abs_le_of_sq_le_sq' h hy).2
  have hnu_nonneg := norm_nonneg u
  have hbu' : ‖b‖ ≤ ‖u‖ := sqle _ _ hnu_nonneg (by nlinarith [sq_nonneg ‖(hh : V₁)‖, sq_nonneg ‖w‖])
  have hhu' : ‖(hh : V₁)‖ ≤ ‖u‖ :=
    sqle _ _ hnu_nonneg (by nlinarith [sq_nonneg ‖b‖, sq_nonneg ‖w‖])
  have hρ' : ‖ρ‖ ≤ c' * ‖b‖ := hρn
  -- lower bound
  have hA1 : ⟪S.ι₀ σ, S.ι₀ ρ⟫ ≤ ‖S.ι₀ σ‖ * (c' * ‖b‖) :=
    calc ⟪S.ι₀ σ, S.ι₀ ρ⟫ ≤ ‖S.ι₀ σ‖ * ‖S.ι₀ ρ‖ := real_inner_le_norm _ _
      _ ≤ ‖S.ι₀ σ‖ * ‖ρ‖ := by gcongr; exact S.norm_ι₀_le ρ
      _ ≤ ‖S.ι₀ σ‖ * (c' * ‖b‖) := by gcongr
  have hac2 : a ^ 2 * c' ^ 2 * ‖b‖ ^ 2 = a * ‖b‖ ^ 2 := by
    rw [show a ^ 2 * c' ^ 2 * ‖b‖ ^ 2 = (a * c' ^ 2) * (a * ‖b‖ ^ 2) by ring, hac, one_mul]
  have hA2 : a * ⟪S.ι₀ σ, S.ι₀ ρ⟫ ≤ ‖S.ι₀ σ‖ ^ 2 / 2 + a * ‖b‖ ^ 2 / 2 := by
    nlinarith [sq_nonneg (‖S.ι₀ σ‖ - a * c' * ‖b‖), mul_le_mul_of_nonneg_left hA1 ha0.le]
  have hw1 : ‖w‖ ≤ c' * ‖S.d₁ u‖ := by rw [hd1w]; exact hcp.le₁ w hw
  have hw2 : a * ‖w‖ ^ 2 ≤ ‖S.d₁ u‖ ^ 2 := by
    have h1 : ‖w‖ ^ 2 ≤ (c' * ‖S.d₁ u‖) ^ 2 := by gcongr
    nlinarith [mul_le_mul_of_nonneg_left h1 ha0.le, sq_nonneg ‖S.d₁ u‖]
  have hσ := S.norm_sq_V₀ σ
  have hSum_lb : a * (‖σ‖ + ‖u‖ + ‖p‖) ^ 2 ≤ 6 * (f0 + f1 + f2) := by
    rw [hnp, hpp, hpp'] at E1
    rw [hhu] at E2
    rw [hbu] at E0
    have hnp' : ‖(p : V₁)‖ = ‖p‖ := rfl
    refine hodge_real_aux (A := ⟪S.ι₀ σ, S.ι₀ ρ⟫) (s0 := ‖S.ι₀ σ‖) (s1 := ‖S.ι₁ (S.d₀ σ)‖)
      (nb := ‖b‖) (nh := ‖(hh : V₁)‖) (nw := ‖w‖) (np := ‖p‖) (d := ‖S.d₁ u‖) ha0 ha1 hA2 hw2
      ?_ hσ hnorm
    rw [hnp'] at E1
    linarith
  -- upper bound
  have hτ : ‖σ - a • ρ‖ ≤ ‖σ‖ + ‖u‖ + ‖p‖ := by
    have : ‖σ - a • ρ‖ ≤ ‖σ‖ + a * ‖ρ‖ := by
      calc ‖σ - a • ρ‖ ≤ ‖σ‖ + ‖a • ρ‖ := norm_sub_le _ _
        _ = ‖σ‖ + a * ‖ρ‖ := by rw [norm_smul, Real.norm_of_nonneg ha0.le]
    have h2 : a * ‖ρ‖ ≤ ‖b‖ := by
      calc a * ‖ρ‖ ≤ a * (c' * ‖b‖) := by gcongr
        _ = (a * c') * ‖b‖ := by ring
        _ ≤ 1 * ‖b‖ := by gcongr
        _ = ‖b‖ := one_mul _
    linarith [norm_nonneg p]
  have hv : ‖u + S.d₀ σ + (p : V₁)‖ ≤ ‖σ‖ + ‖u‖ + ‖p‖ := by
    calc ‖u + S.d₀ σ + (p : V₁)‖ ≤ ‖u + S.d₀ σ‖ + ‖(p : V₁)‖ := norm_add_le _ _
      _ ≤ ‖u‖ + ‖σ‖ + ‖p‖ := by
        have h1 := S.norm_d₀_le σ
        have h2 := norm_add_le u (S.d₀ σ)
        have hpn : ‖(p : V₁)‖ = ‖p‖ := rfl
        linarith
      _ = _ := by ring
  have hq : ‖hh - p‖ ≤ ‖σ‖ + ‖u‖ + ‖p‖ := by
    calc ‖hh - p‖ ≤ ‖hh‖ + ‖p‖ := norm_sub_le _ _
      _ ≤ ‖u‖ + ‖p‖ := by gcongr; exact hhu'
      _ ≤ _ := by linarith [norm_nonneg σ]
  have hF : f0 + f1 + f2 ≤
      (‖F₀‖ + ‖F₁‖ + ‖F₂‖) * (‖σ‖ + ‖u‖ + ‖p‖) := by
    have g0 : f0 ≤ ‖F₀‖ * (‖σ‖ + ‖u‖ + ‖p‖) :=
      hf0 ▸ (Real.le_norm_self _).trans ((F₀.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left hτ (norm_nonneg _)))
    have g1 : f1 ≤ ‖F₁‖ * (‖σ‖ + ‖u‖ + ‖p‖) :=
      hf1 ▸ (Real.le_norm_self _).trans ((F₁.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left hv (norm_nonneg _)))
    have g2 : f2 ≤ ‖F₂‖ * (‖σ‖ + ‖u‖ + ‖p‖) :=
      hf2 ▸ (Real.le_norm_self _).trans ((F₂.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left hq (norm_nonneg _)))
    linarith
  -- conclusion
  have hΦ : 0 ≤ ‖F₀‖ + ‖F₁‖ + ‖F₂‖ := by positivity
  have hN : 0 ≤ ‖σ‖ + ‖u‖ + ‖p‖ := by positivity
  rw [hstab]
  rcases hN.eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  · have h6 : a * (‖σ‖ + ‖u‖ + ‖p‖) ≤ 6 * (‖F₀‖ + ‖F₁‖ + ‖F₂‖) := by
      refine le_of_mul_le_mul_right ?_ hpos
      calc a * (‖σ‖ + ‖u‖ + ‖p‖) * (‖σ‖ + ‖u‖ + ‖p‖)
          = a * (‖σ‖ + ‖u‖ + ‖p‖) ^ 2 := by ring
        _ ≤ 6 * (f0 + f1 + f2) := hSum_lb
        _ ≤ 6 * ((‖F₀‖ + ‖F₁‖ + ‖F₂‖) * (‖σ‖ + ‖u‖ + ‖p‖)) := by linarith
        _ = 6 * (‖F₀‖ + ‖F₁‖ + ‖F₂‖) * (‖σ‖ + ‖u‖ + ‖p‖) := by ring
    have h7 : ‖σ‖ + ‖u‖ + ‖p‖ ≤ c' ^ 2 * (6 * (‖F₀‖ + ‖F₁‖ + ‖F₂‖)) := by
      calc ‖σ‖ + ‖u‖ + ‖p‖ = c' ^ 2 * (a * (‖σ‖ + ‖u‖ + ‖p‖)) := by
            rw [← mul_assoc, mul_comm (c' ^ 2) a, hac, one_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_left h6 (sq_nonneg c')
    have h8 := mul_nonneg (sq_nonneg c') hΦ
    linarith

/-- Uniqueness for the general mixed problem. -/
theorem IsGenSolution.unique {c : ℝ} (hc : S.HasPoincareConst c)
    {F₀ : V₀ →L[ℝ] ℝ} {F₁ : V₁ →L[ℝ] ℝ} {F₂ : S.harmonic →L[ℝ] ℝ}
    {σ σ' : V₀} {u u' : V₁} {p p' : S.harmonic} (h : S.IsGenSolution F₀ F₁ F₂ σ u p)
    (h' : S.IsGenSolution F₀ F₁ F₂ σ' u' p') : σ = σ' ∧ u = u' ∧ p = p' := by
  have hd : S.IsGenSolution 0 0 0 (σ - σ') (u - u') (p - p') := by
    refine ⟨fun τ => ?_, fun v => ?_, fun q => ?_⟩
    · have := h.eq₀ τ; have := h'.eq₀ τ
      simp only [map_sub, inner_sub_left, inner_sub_right, zero_apply] at *
      linarith
    · have := h.eq₁ v; have := h'.eq₁ v
      simp only [map_sub, inner_sub_left, inner_sub_right, zero_apply,
        Submodule.coe_sub] at *
      linarith
    · have := h.eq₂ q; have := h'.eq₂ q
      simp only [map_sub, inner_sub_left, inner_sub_right, zero_apply,
        Submodule.coe_sub] at *
      linarith
  have hn := hd.norm_le hc
  simp only [norm_zero, add_zero, mul_zero] at hn
  have n1 := norm_nonneg (σ - σ')
  have n2 := norm_nonneg (u - u')
  have n3 := norm_nonneg (p - p')
  have h1 : ‖σ - σ'‖ = 0 := by linarith
  have h2 : ‖u - u'‖ = 0 := by linarith
  have h3 : ‖p - p'‖ = 0 := by linarith
  exact ⟨sub_eq_zero.1 (norm_eq_zero.1 h1), sub_eq_zero.1 (norm_eq_zero.1 h2),
    sub_eq_zero.1 (norm_eq_zero.1 h3)⟩

/-- Existence for the general mixed problem. -/
theorem exists_isGenSolution {c : ℝ} (hc : S.HasPoincareConst c)
    (F₀ : V₀ →L[ℝ] ℝ) (F₁ : V₁ →L[ℝ] ℝ) (F₂ : S.harmonic →L[ℝ] ℝ) :
    ∃ σ u p, S.IsGenSolution F₀ F₁ F₂ σ u p := by
  let F : GenSpace S →L[ℝ] ℝ :=
    F₀.comp (GenSpace.π₀ S) - F₁.comp (GenSpace.π₁ S) - F₂.comp (GenSpace.π₂ S)
  have key : ∀ x : GenSpace S, ‖x‖ ≤ (3 * stabilityConst c) * ‖GenSpace.form S x‖ := by
    intro x
    set B := GenSpace.form S x with hBdef
    have h0 : ‖B.comp (GenSpace.e₀ S)‖ ≤ ‖B‖ :=
      ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun τ => by
        calc ‖(B.comp (GenSpace.e₀ S)) τ‖ = ‖B (GenSpace.e₀ S τ)‖ := rfl
          _ ≤ ‖B‖ * ‖GenSpace.e₀ S τ‖ := B.le_opNorm _
          _ = ‖B‖ * ‖τ‖ := by rw [GenSpace.norm_e₀]
    have h1 : ‖-(B.comp (GenSpace.e₁ S))‖ ≤ ‖B‖ := by
      rw [norm_neg]
      exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => by
        calc ‖(B.comp (GenSpace.e₁ S)) v‖ = ‖B (GenSpace.e₁ S v)‖ := rfl
          _ ≤ ‖B‖ * ‖GenSpace.e₁ S v‖ := B.le_opNorm _
          _ = ‖B‖ * ‖v‖ := by rw [GenSpace.norm_e₁]
    have h2 : ‖-(B.comp (GenSpace.e₂ S))‖ ≤ ‖B‖ := by
      rw [norm_neg]
      exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun q => by
        calc ‖(B.comp (GenSpace.e₂ S)) q‖ = ‖B (GenSpace.e₂ S q)‖ := rfl
          _ ≤ ‖B‖ * ‖GenSpace.e₂ S q‖ := B.le_opNorm _
          _ = ‖B‖ * ‖q‖ := by rw [GenSpace.norm_e₂]
    have hsol : S.IsGenSolution (B.comp (GenSpace.e₀ S)) (-(B.comp (GenSpace.e₁ S)))
        (-(B.comp (GenSpace.e₂ S))) (GenSpace.π₀ S x) (GenSpace.π₁ S x) (GenSpace.π₂ S x) := by
      refine ⟨fun τ => ?_, fun v => ?_, fun q => ?_⟩
      · simp only [ContinuousLinearMap.comp_apply, hBdef, GenSpace.form_apply, GenSpace.π₀_e₀,
          GenSpace.π₁_e₀, GenSpace.π₂_e₀, map_zero, inner_zero_right, inner_zero_left,
          ZeroMemClass.coe_zero, sub_zero]
        rw [real_inner_comm (S.ι₁ (GenSpace.π₁ S x)) (S.ι₁ (S.d₀ τ))]
      · simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply, hBdef,
          GenSpace.form_apply, GenSpace.π₀_e₁, GenSpace.π₁_e₁, GenSpace.π₂_e₁, map_zero,
          inner_zero_right, inner_zero_left, ZeroMemClass.coe_zero, sub_zero, zero_sub]
        ring
      · simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply, hBdef,
          GenSpace.form_apply, GenSpace.π₀_e₂, GenSpace.π₁_e₂, GenSpace.π₂_e₂, map_zero,
          inner_zero_right, inner_zero_left, sub_zero, zero_sub]
        ring
    have hn := hsol.norm_le hc
    have h3 := GenSpace.norm_le_sum x
    have h4 : stabilityConst c * (‖B.comp (GenSpace.e₀ S)‖ + ‖-(B.comp (GenSpace.e₁ S))‖ +
        ‖-(B.comp (GenSpace.e₂ S))‖) ≤ stabilityConst c * (3 * ‖B‖) := by
      exact mul_le_mul_of_nonneg_left (by linarith) (stabilityConst_pos c).le
    have h5 : 3 * stabilityConst c * ‖B‖ = stabilityConst c * (3 * ‖B‖) := by ring
    linarith
  obtain ⟨x, hx, -⟩ := existsUnique_of_symm_of_bounded_below (GenSpace.form S)
    (GenSpace.form_symm S) key F
  refine ⟨GenSpace.π₀ S x, GenSpace.π₁ S x, GenSpace.π₂ S x, ?_, ?_, ?_⟩
  · intro τ
    have := DFunLike.congr_fun hx (GenSpace.e₀ S τ)
    simp only [GenSpace.form_apply, F, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.comp_apply, GenSpace.π₀_e₀, GenSpace.π₁_e₀, GenSpace.π₂_e₀, map_zero,
      inner_zero_right, inner_zero_left, ZeroMemClass.coe_zero, sub_zero] at this
    have hc' := real_inner_comm (S.ι₁ (GenSpace.π₁ S x)) (S.ι₁ (S.d₀ τ))
    linarith
  · intro v
    have := DFunLike.congr_fun hx (GenSpace.e₁ S v)
    simp only [GenSpace.form_apply, F, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.comp_apply, GenSpace.π₀_e₁, GenSpace.π₁_e₁, GenSpace.π₂_e₁, map_zero,
      inner_zero_right, inner_zero_left, ZeroMemClass.coe_zero, sub_zero, zero_sub] at this
    linarith
  · intro q
    have := DFunLike.congr_fun hx (GenSpace.e₂ S q)
    simp only [GenSpace.form_apply, F, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.comp_apply, GenSpace.π₀_e₂, GenSpace.π₁_e₂, GenSpace.π₂_e₂, map_zero,
      inner_zero_right, inner_zero_left, sub_zero, zero_sub] at this
    linarith

/-- **Well-posedness of the mixed Hodge Laplace problem** (Arnold, Theorem 4.8): existence. -/
theorem exists_isSolution {c : ℝ} (hc : S.HasPoincareConst c) (f : W₁) :
    ∃ σ u p, S.IsSolution f σ u p := by
  obtain ⟨σ, u, p, h⟩ := exists_isGenSolution hc 0 (S.load f) 0
  exact ⟨σ, u, p, (S.isSolution_iff_isGenSolution).2 h⟩

/-- **Well-posedness of the mixed Hodge Laplace problem** (Arnold, Theorem 4.8): uniqueness. -/
theorem IsSolution.unique {c : ℝ} (hc : S.HasPoincareConst c) {f : W₁}
    {σ σ' : V₀} {u u' p p' : V₁} (h : S.IsSolution f σ u p) (h' : S.IsSolution f σ' u' p') :
    σ = σ' ∧ u = u' ∧ p = p' := by
  have hh := (S.isSolution_iff_isGenSolution (p := ⟨p, h.harmonic⟩)).1 h
  have hh' := (S.isSolution_iff_isGenSolution (p := ⟨p', h'.harmonic⟩)).1 h'
  have := hh.unique hc hh'
  exact ⟨this.1, this.2.1, congrArg Subtype.val this.2.2⟩

/-- **Well-posedness of the mixed Hodge Laplace problem** (Arnold, Theorem 4.8): stability,
`‖σ‖_V + ‖u‖_V + ‖p‖ ≤ C ‖f‖` with `C` depending only on the Poincaré constant. -/
theorem IsSolution.norm_le {c : ℝ} (hc : S.HasPoincareConst c) {f : W₁}
    {σ : V₀} {u p : V₁} (h : S.IsSolution f σ u p) :
    ‖σ‖ + ‖u‖ + ‖p‖ ≤ stabilityConst c * ‖f‖ := by
  have hh := (S.isSolution_iff_isGenSolution (p := ⟨p, h.harmonic⟩)).1 h
  have := hh.norm_le hc
  simp only [norm_zero, zero_add, add_zero, Submodule.norm_coe] at this
  calc ‖σ‖ + ‖u‖ + ‖p‖ ≤ stabilityConst c * ‖S.load f‖ := this
    _ ≤ stabilityConst c * ‖f‖ := by
      exact mul_le_mul_of_nonneg_left (S.norm_load_le f) (stabilityConst_pos c).le

end Complete

end ShortHilbertComplex

end FEEC
