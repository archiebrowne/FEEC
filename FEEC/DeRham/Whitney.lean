/-
Polynomial and Whitney forms as subcomplexes of the L² de Rham complex.
-/
import FEEC.DeRham.Classical
import FEEC.Discrete.Complex
import FEEC.Discrete.ErrorEstimate

/-!
# Finite element subcomplexes of the `L²` de Rham complex on a single element

Let `Ω` be a bounded open subset of a Euclidean space `E` (think of the interior of a
simplex: a mesh with one element). Smooth forms on `E` restrict to elements of `HΛᵏ(Ω)`, and
this is compatible with the exterior derivative (`smoothToHΛ`, `d_smoothToHΛ`). Hence the
two families of polynomial complexes of Arnold, §7 give subcomplexes of the `L²` de Rham
complex:

* `polySubcomplex r`: `𝓟ᵣΛ⁰ → 𝓟ᵣ₋₁Λ¹ → ⋯ → 𝓟₀Λʳ → 0`;
* `polyMinusSubcomplex r`: `𝓟⁻ᵣ₊₁Λ⁰ → 𝓟⁻ᵣ₊₁Λ¹ → ⋯`;
* `whitneySubcomplex = polyMinusSubcomplex 0`: the **Whitney forms** `𝓟₁⁻Λᵏ`.

## Main results

* `finiteDimensional_whitney`: the spaces of Whitney forms are finite-dimensional.
* `whitney_galerkin_wellPosed`: the Galerkin method for the Hodge Laplacian in Whitney forms
  has a unique solution.
* `whitney_harmonic_eq_bot`: the Whitney complex is exact in positive degree: it has no
  nonzero discrete harmonic forms (the discrete analogue of the Poincaré lemma).

A bounded cochain projection onto these spaces, and the assembly of elements into a mesh,
are not constructed here.
-/

namespace FEEC

open Module MeasureTheory ShortHilbertComplex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {k : ℕ}

variable (E k) in
/-- The space of smooth `k`-forms on `E`. -/
def smoothForms : Submodule ℝ (E → E [⋀^Fin k]→L[ℝ] ℝ) where
  carrier := {ω | ContDiff ℝ (⊤ : ℕ∞) ω}
  add_mem' {a b} (h : ContDiff ℝ (⊤ : ℕ∞) a) (h' : ContDiff ℝ (⊤ : ℕ∞) b) := h.add h'
  zero_mem' := (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : E => (0 : E [⋀^Fin k]→L[ℝ] ℝ)))
  smul_mem' c {a} (h : ContDiff ℝ (⊤ : ℕ∞) a) := h.const_smul c

theorem mem_smoothForms {ω : E → E [⋀^Fin k]→L[ℝ] ℝ} :
    ω ∈ smoothForms E k ↔ ContDiff ℝ (⊤ : ℕ∞) ω := Iff.rfl

theorem polyForms_le_smoothForms (r : ℕ) : polyForms E r k ≤ smoothForms E k := by
  intro ω hω
  obtain ⟨c, hc, rfl⟩ := mem_polyForms_iff.1 hω
  have := ContDiff.sum (s := Finset.range (r + 1)) fun j _ => (hc j).contDiff
  refine mem_smoothForms.2 ?_
  convert this using 1
  ext x
  simp

theorem polyFormsMinus_le_smoothForms (r : ℕ) : polyFormsMinus E r k ≤ smoothForms E k :=
  polyFormsMinus_le_polyForms.trans (polyForms_le_smoothForms _)

theorem extDeriv_mem_smoothForms {ω : E → E [⋀^Fin k]→L[ℝ] ℝ} (hω : ω ∈ smoothForms E k) :
    extDeriv ω ∈ smoothForms E (k + 1) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ ω) :=
    (mem_smoothForms.1 hω).fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℝ).contDiff.comp h1

variable [MeasurableSpace E] [BorelSpace E] {Ω : Set E}

variable (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) in
/-- The `L²` class of a continuous form. -/
noncomputable def ofAltLp {k : ℕ} (f : E → E [⋀^Fin k]→L[ℝ] ℝ) (hf : Continuous f) :
    L2Form Ω k :=
  (memLp_ofAlt_of_continuous hΩ hb hf).toLp _

theorem ofAltLp_congr (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {f g : E → E [⋀^Fin k]→L[ℝ] ℝ}
    (hf : Continuous f) (hg : Continuous g) (h : f = g) : ofAltLp hΩ hb f hf = ofAltLp hΩ hb g hg := by
  subst h; rfl

theorem coeFn_ofAltLp (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {f : E → E [⋀^Fin k]→L[ℝ] ℝ}
    (hf : Continuous f) : ofAltLp hΩ hb f hf =ᵐ[volume.restrict Ω] fun x => Covector.ofAlt (f x) :=
  MemLp.coeFn_toLp _

theorem ofAltLp_add (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {f g : E → E [⋀^Fin k]→L[ℝ] ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    ofAltLp hΩ hb (f + g) (hf.add hg) = ofAltLp hΩ hb f hf + ofAltLp hΩ hb g hg := by
  refine Lp.ext ?_
  filter_upwards [coeFn_ofAltLp hΩ hb (hf.add hg), Lp.coeFn_add (ofAltLp hΩ hb f hf)
    (ofAltLp hΩ hb g hg), coeFn_ofAltLp hΩ hb hf, coeFn_ofAltLp hΩ hb hg] with x h1 h2 h3 h4
  simp only [Pi.add_apply] at h1 h2
  rw [h1, h2, h3, h4]
  simp

theorem ofAltLp_smul (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (c : ℝ)
    {f : E → E [⋀^Fin k]→L[ℝ] ℝ} (hf : Continuous f) :
    ofAltLp hΩ hb (c • f) (hf.const_smul c) = c • ofAltLp hΩ hb f hf := by
  refine Lp.ext ?_
  filter_upwards [coeFn_ofAltLp hΩ hb (hf.const_smul c), Lp.coeFn_smul c (ofAltLp hΩ hb f hf),
    coeFn_ofAltLp hΩ hb hf] with x h1 h2 h3
  simp only [Pi.smul_apply] at h1 h2
  rw [h1, h2, h3]
  simp

/-- A smooth form on `E`, restricted to a bounded open set `Ω`, as an element of `HΛᵏ(Ω)`:
the pair of the `L²` classes of `ω` and of its exterior derivative. -/
noncomputable def smoothToHΛ (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (k : ℕ) :
    smoothForms E k →ₗ[ℝ] HΛ Ω k where
  toFun ω :=
    have h₁ := memLp_ofAlt_of_continuous hΩ hb (mem_smoothForms.1 ω.2).continuous
    have h₂ := memLp_ofAlt_of_continuous hΩ hb
      (mem_smoothForms.1 (extDeriv_mem_smoothForms ω.2)).continuous
    ⟨WithLp.toLp 2 (h₁.toLp _, h₂.toLp _),
      hasWeakExtDeriv_of_contDiff hΩ ((mem_smoothForms.1 ω.2).of_le (by exact_mod_cast le_top))
        h₁ h₂⟩
  map_add' ω η := by
    refine Subtype.ext (withLp_prod_ext ?_ ?_)
    · exact (ofAltLp_add hΩ hb (mem_smoothForms.1 ω.2).continuous
        (mem_smoothForms.1 η.2).continuous)
    · refine (ofAltLp_congr hΩ hb (mem_smoothForms.1 (extDeriv_mem_smoothForms (ω + η).2)).continuous
        ((mem_smoothForms.1 (extDeriv_mem_smoothForms ω.2)).continuous.add
        (mem_smoothForms.1 (extDeriv_mem_smoothForms η.2)).continuous) ?_).trans
        (ofAltLp_add hΩ hb (mem_smoothForms.1 (extDeriv_mem_smoothForms ω.2)).continuous
          (mem_smoothForms.1 (extDeriv_mem_smoothForms η.2)).continuous)
      funext x
      exact extDeriv_add ((mem_smoothForms.1 ω.2).differentiable (by simp) x)
        ((mem_smoothForms.1 η.2).differentiable (by simp) x)
  map_smul' c ω := by
    refine Subtype.ext (withLp_prod_ext ?_ ?_)
    · exact ofAltLp_smul hΩ hb c (mem_smoothForms.1 ω.2).continuous
    · refine (ofAltLp_congr hΩ hb (mem_smoothForms.1 (extDeriv_mem_smoothForms (c • ω).2)).continuous
        ((mem_smoothForms.1 (extDeriv_mem_smoothForms ω.2)).continuous.const_smul c) ?_).trans
        (ofAltLp_smul hΩ hb c (mem_smoothForms.1 (extDeriv_mem_smoothForms ω.2)).continuous)
      funext x
      exact extDeriv_smul c _

/-- The underlying `L²` form of `smoothToHΛ ω` is the class of `ω`. -/
theorem toL2_smoothToHΛ (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (ω : smoothForms E k) :
    HΛ.toL2 (smoothToHΛ hΩ hb k ω) =ᵐ[volume.restrict Ω] fun x => Covector.ofAlt (ω.1 x) :=
  coeFn_ofAltLp hΩ hb (mem_smoothForms.1 ω.2).continuous

/-- The weak exterior derivative of a smooth form is the classical one. -/
theorem d_smoothToHΛ (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (ω : smoothForms E k) :
    HΛ.d (smoothToHΛ hΩ hb k ω) =
      smoothToHΛ hΩ hb (k + 1) ⟨extDeriv ω.1, extDeriv_mem_smoothForms ω.2⟩ := by
  refine HΛ.toL2_injective hΩ ?_
  rw [HΛ.toL2_d]
  rfl

/-- The image in `HΛᵏ(Ω)` of a space `P` of forms on `E` (only its smooth elements count). -/
noncomputable def formsInHΛ (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (P : Submodule ℝ (E → E [⋀^Fin k]→L[ℝ] ℝ)) : Submodule ℝ (HΛ Ω k) :=
  (P.comap (smoothForms E k).subtype).map (smoothToHΛ hΩ hb k)

theorem mem_formsInHΛ {hΩ : IsOpen Ω} {hb : Bornology.IsBounded Ω}
    {P : Submodule ℝ (E → E [⋀^Fin k]→L[ℝ] ℝ)} {p : HΛ Ω k} :
    p ∈ formsInHΛ hΩ hb P ↔ ∃ ω : smoothForms E k, ω.1 ∈ P ∧ smoothToHΛ hΩ hb k ω = p := by
  unfold formsInHΛ
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]

/-- If `d P ⊆ Q` for spaces of smooth forms then `d` maps the image of `P` in `HΛ` into that
of `Q`. -/
theorem d_mem_formsInHΛ {hΩ : IsOpen Ω} {hb : Bornology.IsBounded Ω}
    {P : Submodule ℝ (E → E [⋀^Fin k]→L[ℝ] ℝ)} {Q : Submodule ℝ (E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ)}
    (h : ∀ ω ∈ P, ω ∈ smoothForms E k → extDeriv ω ∈ Q) {p : HΛ Ω k}
    (hp : p ∈ formsInHΛ hΩ hb P) : HΛ.d p ∈ formsInHΛ hΩ hb Q := by
  obtain ⟨ω, hω, rfl⟩ := mem_formsInHΛ.1 hp
  rw [d_smoothToHΛ]
  exact mem_formsInHΛ.2 ⟨_, h _ hω ω.2, rfl⟩

/-- The subcomplex `𝓟⁻ᵣ₊₁Λ⁰ → 𝓟⁻ᵣ₊₁Λ¹ → ⋯` of the `L²` de Rham complex of a bounded open
set. -/
noncomputable def polyMinusSubcomplex (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (r : ℕ) :
    (deRhamComplex hΩ).Subcomplex where
  carrier k := formsInHΛ hΩ hb (polyFormsMinus E r k)
  map_d k p hp :=
    d_mem_formsInHΛ (fun _ hω _ =>
      polyForms_le_polyFormsMinus (extDeriv_mem_polyForms_of_mem_polyFormsMinus hω)) hp

/-- The subcomplex `𝓟ᵣΛ⁰ → 𝓟ᵣ₋₁Λ¹ → ⋯ → 𝓟₀Λʳ → 0` of the `L²` de Rham complex of a bounded
open set. -/
noncomputable def polySubcomplex (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (r : ℕ) :
    (deRhamComplex hΩ).Subcomplex where
  carrier k := if k ≤ r then formsInHΛ hΩ hb (polyForms E (r - k) k) else ⊥
  map_d k p hp := by
    by_cases hk : k ≤ r
    · simp only [if_pos hk] at hp
      by_cases hk1 : k + 1 ≤ r
      · simp only [if_pos hk1]
        refine d_mem_formsInHΛ (fun ω hω _ => ?_) hp
        have : r - k = (r - (k + 1)) + 1 := by omega
        rw [this] at hω
        exact extDeriv_mem_polyForms hω
      · simp only [hk1, if_false]
        obtain ⟨ω, hω, rfl⟩ := mem_formsInHΛ.1 hp
        have h0 : r - k = 0 := by omega
        rw [h0] at hω
        rw [show (deRhamComplex hΩ).d k _ = HΛ.d _ from rfl, d_smoothToHΛ]
        have : (⟨extDeriv ω.1, extDeriv_mem_smoothForms ω.2⟩ : smoothForms E (k + 1)) = 0 :=
          Subtype.ext (extDeriv_eq_zero_of_mem_polyForms_zero hω)
        rw [this, map_zero]
        exact Submodule.zero_mem _
    · simp only [hk, if_false] at hp
      have : p = 0 := (Submodule.mem_bot ℝ).1 hp
      subst this
      rw [map_zero]
      exact Submodule.zero_mem _

/-- The complex of **Whitney forms** `𝓟₁⁻Λ⁰ → 𝓟₁⁻Λ¹ → ⋯` on a bounded open set, as a
subcomplex of the `L²` de Rham complex. -/
noncomputable abbrev whitneySubcomplex (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    (deRhamComplex hΩ).Subcomplex :=
  polyMinusSubcomplex hΩ hb 0

/-- The space of Whitney `k`-forms is finite-dimensional. -/
theorem finiteDimensional_whitney (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (k : ℕ) :
    FiniteDimensional ℝ ((whitneySubcomplex hΩ hb).carrier k) := by
  let c : (E [⋀^Fin k]→L[ℝ] ℝ) →ₗ[ℝ] (E → E [⋀^Fin k]→L[ℝ] ℝ) :=
    { toFun := fun a _ => a
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let c' : (E [⋀^Fin (k + 1)]→L[ℝ] ℝ) →ₗ[ℝ] (E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ) :=
    { toFun := fun a _ => a
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let L : (E [⋀^Fin k]→L[ℝ] ℝ) × (E [⋀^Fin (k + 1)]→L[ℝ] ℝ) →ₗ[ℝ] (E → E [⋀^Fin k]→L[ℝ] ℝ) :=
    c.comp (LinearMap.fst ℝ _ _) + koszulₗ.comp (c'.comp (LinearMap.snd ℝ _ _))
  have hP : polyFormsMinus E 0 k ≤ LinearMap.range L := by
    refine sup_le ?_ ?_
    · intro ω hω
      obtain ⟨cc, hc, rfl⟩ := mem_polyForms_iff.1 hω
      refine ⟨(cc 0 0, 0), ?_⟩
      funext x
      simp [L, c, (hc 0).eq_const x]
    · rintro _ ⟨β, hβ, rfl⟩
      have hβ' : IsHomogeneousForm 0 β := hβ
      refine ⟨(0, β 0), ?_⟩
      have : β = fun _ => β 0 := funext fun x => hβ'.eq_const x
      simp [L, c', koszulₗ_apply, ← this]
  have : FiniteDimensional ℝ (polyFormsMinus E 0 k) :=
    Submodule.finiteDimensional_of_le hP
  let g : (polyFormsMinus E 0 k).comap (smoothForms E k).subtype →ₗ[ℝ] polyFormsMinus E 0 k :=
    (smoothForms E k).subtype.restrict fun x hx => hx
  have : FiniteDimensional ℝ ((polyFormsMinus E 0 k).comap (smoothForms E k).subtype) :=
    Module.Finite.of_injective g fun x y hxy => by
      have h := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext h)
  exact Module.Finite.map _ _

theorem wellPosed_of_finiteDimensional {W₀ W₁ W₂ V₀ V₁ : Type*}
    [NormedAddCommGroup W₀] [InnerProductSpace ℝ W₀]
    [NormedAddCommGroup W₁] [InnerProductSpace ℝ W₁]
    [NormedAddCommGroup W₂] [InnerProductSpace ℝ W₂]
    [NormedAddCommGroup V₀] [InnerProductSpace ℝ V₀]
    [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁]
    [FiniteDimensional ℝ V₀] [FiniteDimensional ℝ V₁]
    (S : ShortHilbertComplex W₀ W₁ W₂ V₀ V₁) (f : W₁) :
    ∃ σh uh ph, S.IsSolution f σh uh ph ∧
      ∀ σ' u' p', S.IsSolution f σ' u' p' → σ' = σh ∧ u' = uh ∧ p' = ph := by
  have := FiniteDimensional.complete ℝ V₀
  have := FiniteDimensional.complete ℝ V₁
  obtain ⟨c, hc⟩ := ShortHilbertComplex.exists_hasPoincareConst_of_finiteDimensional (S := S)
  obtain ⟨σ, u, p, h⟩ := exists_isSolution hc f
  refine ⟨σ, u, p, h, fun σ' u' p' h' => ?_⟩
  obtain ⟨e1, e2, e3⟩ := h.unique hc h'
  exact ⟨e1.symm, e2.symm, e3.symm⟩

/-- **The Galerkin method for the Hodge Laplacian in Whitney forms is well posed**: for every
`f ∈ L²Λᵏ⁺¹(Ω)` the discrete mixed problem has a unique solution. -/
theorem whitney_galerkin_wellPosed (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (k : ℕ)
    (f : L2Form Ω (k + 1)) :
    ∃ σh uh ph, ((whitneySubcomplex hΩ hb).segment k).toShort.IsSolution f σh uh ph ∧
      ∀ σ' u' p', ((whitneySubcomplex hΩ hb).segment k).toShort.IsSolution f σ' u' p' →
        σ' = σh ∧ u' = uh ∧ p' = ph := by
  have h0 : FiniteDimensional ℝ ((whitneySubcomplex hΩ hb).segment k).carrier₀ :=
    finiteDimensional_whitney hΩ hb k
  have h1 : FiniteDimensional ℝ ((whitneySubcomplex hΩ hb).segment k).carrier₁ :=
    finiteDimensional_whitney hΩ hb (k + 1)
  exact wellPosed_of_finiteDimensional _ f

set_option maxHeartbeats 400000 in
/-- **The Whitney complex is exact in positive degree**: there are no nonzero discrete
harmonic Whitney forms of degree `k + 1`. -/
theorem whitney_harmonic_eq_bot (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (k : ℕ) :
    ((whitneySubcomplex hΩ hb).segment k).toShort.harmonic = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro q hq
  have hdq : HΛ.d (q : HΛ Ω (k + 1)) = 0 := by
    apply HΛ.toL2_injective hΩ
    have h : HΛ.toL2 (HΛ.d (q : HΛ Ω (k + 1))) = 0 :=
      ShortHilbertComplex.Subcomplex.coe_harmonic_mem_cocycles _ hq
    rw [h, map_zero]
  obtain ⟨ω, hω, hωq⟩ := mem_formsInHΛ.1 (q.2 : (q : HΛ Ω (k + 1)) ∈
    formsInHΛ hΩ hb (polyFormsMinus E 0 (k + 1)))
  by_cases hne : Ω.Nonempty
  · have hmem := extDeriv_mem_polyForms_of_mem_polyFormsMinus hω
    obtain ⟨c, hc, hcη⟩ := mem_polyForms_iff.1 hmem
    have hconst : ∀ x, extDeriv ω.1 x = extDeriv ω.1 0 := by
      intro x
      rw [hcη]
      simp [(hc 0).eq_const x]
    have hae : (fun x => Covector.ofAlt (extDeriv ω.1 x)) =ᵐ[volume.restrict Ω] 0 := by
      have h1 := toL2_smoothToHΛ hΩ hb ⟨extDeriv ω.1, extDeriv_mem_smoothForms ω.2⟩
      rw [← d_smoothToHΛ, hωq, hdq, map_zero] at h1
      exact h1.symm.trans (Lp.coeFn_zero _ _ _)
    have hvol : (volume.restrict Ω : Measure E) ≠ 0 := by
      intro h
      rw [Measure.restrict_eq_zero] at h
      exact (hΩ.measure_pos volume hne).ne' h
    haveI : (ae (volume.restrict Ω)).NeBot := ae_neBot.2 hvol
    obtain ⟨x, hx⟩ := hae.exists
    have hx' : extDeriv ω.1 x = 0 := by simpa using hx
    have hη : extDeriv ω.1 = 0 := by
      funext y
      exact (hconst y).trans ((hconst x).symm.trans hx')
    have key := exists_extDeriv_eq_of_mem_polyFormsMinus (r := 0) (k := k) (ω := ω.1) hω
    obtain ⟨ζ, hζ, hζd⟩ := key hη
    let τ : ((whitneySubcomplex hΩ hb).segment k).carrier₀ :=
      ⟨smoothToHΛ hΩ hb k ⟨ζ, polyFormsMinus_le_smoothForms 0 hζ⟩,
        mem_formsInHΛ.2 ⟨_, hζ, rfl⟩⟩
    have hdτ : HΛ.d τ.1 = (q : HΛ Ω (k + 1)) := by
      have e : (⟨extDeriv ζ, extDeriv_mem_smoothForms (polyFormsMinus_le_smoothForms 0 hζ)⟩ :
          smoothForms E (k + 1)) = ω := Subtype.ext hζd
      show HΛ.d (smoothToHΛ hΩ hb k _) = _
      rw [d_smoothToHΛ, e, hωq]
    have h := ShortHilbertComplex.Subcomplex.inner_harmonic_d₀ _ hq τ
    have h2 : inner ℝ (q : HΛ Ω (k + 1)) (q : HΛ Ω (k + 1)) = 0 := by
      have e : ((deRhamComplex hΩ).segment k).d₀ τ.1 = (q : HΛ Ω (k + 1)) := hdτ
      rw [e] at h
      exact h
    exact Subtype.ext (inner_self_eq_zero.1 h2)
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    have hz : (ae (volume.restrict Ω) : Filter E) = ⊥ := by
      rw [hne, Measure.restrict_empty, ae_zero]
    have : HΛ.toL2 (q : HΛ Ω (k + 1)) = 0 := by
      rw [Lp.eq_zero_iff_ae_eq_zero]
      rw [Filter.EventuallyEq, hz]
      exact Filter.eventually_bot
    exact Subtype.ext (HΛ.toL2_injective hΩ (by rw [this]; simp))

end FEEC
