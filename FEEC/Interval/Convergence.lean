/-
An unconditional convergence theorem for a finite element method on a mesh of an interval.
-/
import FEEC.Main
import FEEC.Discrete.Lift
import FEEC.Interval.Bridge

/-!
# Convergence of the mixed finite element method on an interval

This file instantiates the abstract theory completely for the `L²` de Rham complex
`HΛ⁰(a,b) → HΛ¹(a,b) → 0` of an interval, with every hypothesis discharged:

* `intervalComplex_isClosed`: the complex is closed (in fact `d : HΛ⁰ → HΛ¹` is surjective);
* `meshSubcomplex M`: for a mesh `M`, continuous piecewise linear `0`-forms
  (`M.linForms`, characterised by `Mesh.mem_linForms_iff`) and piecewise constant `1`-forms
  (`M.pcForms`) form a subcomplex;
* `meshProjection M`: a cochain projection onto it, bounded by `1 + c_P` uniformly in the
  mesh (`norm_meshProjection_le`);
* `interval_mixed_quasi_optimal`: the Galerkin solution of the Hodge Laplacian on `1`-forms
  is quasi-optimal with a mesh independent constant;
* `interval_mixed_convergence`: **`O(h)` convergence**. For data `f = ⋆φ` with
  `φ ∈ H¹(a,b)`, `‖σ - σh‖_{H¹} + ‖u - uh‖_{L²} + ‖p - ph‖ ≤ C h ‖φ‖_{H¹}`, with `C`
  depending only on the interval.

The Hodge Laplace problem on `1`-forms is the mixed formulation of `-u″ = f` on `(a,b)` with
`u(a) = u(b) = 0`: `σ ∈ H¹`, `u ∈ L²`, `⟪σ,τ⟫ = ⟪τ′,u⟫` for all `τ ∈ H¹`, `⟪σ′,v⟫ = ⟪f,v⟫`
for all `v ∈ L²`. The method is the lowest order Raviart–Thomas (`P₁`–`P₀`) mixed method.
-/

namespace FEEC.Interval

open MeasureTheory Set ShortHilbertComplex

variable {a b : ℝ}

/-- The `L²` de Rham complex of the interval `(a, b)`. -/
noncomputable abbrev intervalComplex (a b : ℝ) :
    HilbertComplex (fun k => L2Form (Ioo a b) k) (fun k => HΛ (Ioo a b) k) :=
  deRhamComplex isOpen_Ioo

/-! ### Closedness -/

/-- On an interval every `L²` `1`-form is the weak exterior derivative of an `H¹` function
(its primitive). -/
theorem d_surjective : Function.Surjective (HΛ.d : HΛ (Ioo a b) 0 → HΛ (Ioo a b) 1) := by
  intro q
  have h : HasWeakExtDeriv (s0.symm (primitive (s1 (HΛ.toL2 q)))) (HΛ.toL2 q) := by
    rw [hasWeakExtDeriv_iff]
    simpa using hasWeakDeriv_primitive (s1 (HΛ.toL2 q))
  refine ⟨⟨WithLp.toLp 2 (s0.symm (primitive (s1 (HΛ.toL2 q))), HΛ.toL2 q), h⟩, ?_⟩
  apply HΛ.toL2_injective isOpen_Ioo
  rfl

/-- Every `L²` `1`-form on an interval lies in `HΛ¹`. -/
theorem toL2_surjective :
    Function.Surjective (HΛ.toL2 : HΛ (Ioo a b) 1 → L2Form (Ioo a b) 1) := by
  intro η
  exact ⟨⟨WithLp.toLp 2 (η, 0), hasWeakExtDeriv_zero η⟩, rfl⟩

instance (k : ℕ) : Subsingleton (HΛ (Ioo a b) (k + 2)) :=
  ⟨fun p q => Subtype.ext (withLp_prod_ext (Subsingleton.elim _ _) (Subsingleton.elim _ _))⟩

/-- **The `L²` de Rham complex of an interval is closed.** -/
theorem intervalComplex_isClosed : (intervalComplex a b).IsClosed := by
  intro k
  cases k with
  | zero =>
    have : Set.range ((intervalComplex a b).ι (0 + 1) ∘ (intervalComplex a b).d 0) = Set.univ := by
      refine Set.eq_univ_of_forall fun η => ?_
      obtain ⟨q, rfl⟩ := toL2_surjective η
      obtain ⟨τ, rfl⟩ := d_surjective q
      exact ⟨τ, rfl⟩
    rw [this]; exact isClosed_univ
  | succ k =>
    exact (Set.subsingleton_of_subsingleton).isClosed

/-- There are no nonzero harmonic `1`-forms on an interval. -/
theorem harmonic_eq_bot : ((intervalComplex a b).segment 0).harmonic = ⊥ := by
  have h : ((intervalComplex a b).segment 0).coboundaries = ⊤ := by
    rw [eq_top_iff]
    intro u _
    obtain ⟨τ, hτ⟩ := d_surjective u
    exact ⟨τ, hτ⟩
  unfold ShortHilbertComplex.harmonic
  rw [h, Submodule.top_orthogonal_eq_bot]
  simp

/-- The Hodge star `L²Λ⁰(a,b) ≃ L²Λ¹(a,b)`, `g ↦ g dx`. -/
noncomputable def hodgeStar : L2Form (Ioo a b) 0 ≃ₗᵢ[ℝ] L2Form (Ioo a b) 1 :=
  s0.trans s1.symm

/-! ### Scalar helper lemmas -/

theorem IsTestFn.apply_left {φ : ℝ → ℝ} (hφ : IsTestFn a b φ) : φ a = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h => by simpa using hφ.tsupport_subset h)

theorem IsTestFn.apply_right {φ : ℝ → ℝ} (hφ : IsTestFn a b φ) : φ b = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h => by simpa using hφ.tsupport_subset h)

theorem IsTestFn.differentiable {φ : ℝ → ℝ} (hφ : IsTestFn a b φ) : Differentiable ℝ φ :=
  hφ.contDiff.differentiable (by simp)

theorem IsTestFn.continuous_deriv {φ : ℝ → ℝ} (hφ : IsTestFn a b φ) : Continuous (deriv φ) :=
  hφ.contDiff.continuous_deriv (by exact_mod_cast le_top)

theorem IsTestFn.memLp {φ : ℝ → ℝ} (hφ : IsTestFn a b φ) :
    MemLp φ 2 (volume.restrict (Ioo a b)) := by
  obtain ⟨C, hC⟩ := hφ.contDiff.continuous.bounded_above_of_compact_support hφ.hasCompactSupport
  exact MemLp.of_bound hφ.contDiff.continuous.aestronglyMeasurable C
    (Filter.Eventually.of_forall hC)

theorem IsTestFn.memLp_deriv {φ : ℝ → ℝ} (hφ : IsTestFn a b φ) :
    MemLp (deriv φ) 2 (volume.restrict (Ioo a b)) := by
  obtain ⟨C, hC⟩ := hφ.continuous_deriv.bounded_above_of_compact_support hφ.hasCompactSupport.deriv
  exact MemLp.of_bound hφ.continuous_deriv.aestronglyMeasurable C
    (Filter.Eventually.of_forall hC)

theorem integral_deriv_testFn {φ : ℝ → ℝ} (hφ : IsTestFn a b φ) :
    ∫ x in Ioo a b, deriv φ x = 0 := by
  rcases lt_or_ge a b with hab | hab
  swap
  · simp [Ioo_eq_empty (not_lt.2 hab)]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab.le,
    intervalIntegral.integral_deriv_eq_sub' φ rfl (fun x _ => hφ.differentiable x)
      hφ.continuous_deriv.continuousOn, hφ.apply_left, hφ.apply_right]
  simp

/-- Integration by parts for two test functions. -/
theorem integral_deriv_mul_testFn {φ ψ : ℝ → ℝ} (hφ : IsTestFn a b φ) (hψ : IsTestFn a b ψ) :
    ∫ x in Ioo a b, deriv φ x * ψ x = -∫ x in Ioo a b, φ x * deriv ψ x := by
  rcases lt_or_ge a b with hab | hab
  swap
  · simp [Ioo_eq_empty (not_lt.2 hab)]
  rw [← integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hab.le, ← intervalIntegral.integral_of_le hab.le]
  have h1 : IntervalIntegrable (fun x => deriv φ x * ψ x) volume a b :=
    (hφ.continuous_deriv.mul hψ.contDiff.continuous).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun x => φ x * deriv ψ x) volume a b :=
    (hφ.contDiff.continuous.mul hψ.continuous_deriv).intervalIntegrable _ _
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x => φ x * ψ x) (f' := fun x => deriv φ x * ψ x + φ x * deriv ψ x) (a := a) (b := b)
    (fun x _ => (hφ.differentiable x).hasDerivAt.mul (hψ.differentiable x).hasDerivAt)
    (h1.add h2)
  rw [intervalIntegral.integral_add h1 h2, hφ.apply_left, hφ.apply_right] at key
  simp at key
  linarith

theorem hasWeakDeriv_of_ae_const {u : L2I a b} {c : ℝ}
    (h : u =ᵐ[volume.restrict (Ioo a b)] fun _ => c) : HasWeakDeriv u 0 := by
  intro φ hφ
  have e1 : ∫ x in Ioo a b, (0 : L2I a b) x * φ x = 0 := by
    rw [← integral_zero (α := ℝ) (μ := volume.restrict (Ioo a b)) (G := ℝ)]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_zero ℝ 2 (volume.restrict (Ioo a b))] with x hx
    rw [hx]; simp
  have e2 : ∫ x in Ioo a b, u x * deriv φ x = ∫ x in Ioo a b, c * deriv φ x := by
    refine integral_congr_ae ?_
    filter_upwards [h] with x hx
    rw [hx]
  rw [e1, e2, integral_const_mul, integral_deriv_testFn hφ]
  simp

theorem inner_L2I (u v : L2I a b) : inner ℝ u v = ∫ x in Ioo a b, u x * v x := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [mul_comm]

/-! ### The finite element spaces of a mesh -/

namespace Mesh

variable (M : Mesh a b)

/-- Piecewise constant `1`-forms on the mesh, as a subspace of `HΛ¹(a,b)`. -/
def pcForms : Submodule ℝ (HΛ (Ioo a b) 1) where
  carrier := {p | s1 (HΛ.toL2 p) ∈ M.pcConst}
  add_mem' := by
    intro p q hp hq
    show s1 (HΛ.toL2 (p + q)) ∈ M.pcConst
    rw [map_add, map_add]
    exact add_mem hp hq
  zero_mem' := by
    show s1 (HΛ.toL2 (0 : HΛ (Ioo a b) 1)) ∈ M.pcConst
    rw [map_zero, map_zero]
    exact zero_mem _
  smul_mem' := by
    intro c p hp
    show s1 (HΛ.toL2 (c • p)) ∈ M.pcConst
    rw [map_smul, map_smul]
    exact Submodule.smul_mem _ _ hp

theorem mem_pcForms {p : HΛ (Ioo a b) 1} : p ∈ M.pcForms ↔ s1 (HΛ.toL2 p) ∈ M.pcConst :=
  Iff.rfl

/-- Continuous piecewise linear functions on the mesh, as a subspace of `HΛ⁰(a,b) = H¹(a,b)`:
the functions whose weak derivative is piecewise constant (see `mem_linForms_iff`). -/
def linForms : Submodule ℝ (HΛ (Ioo a b) 0) where
  carrier := {p | HΛ.d p ∈ M.pcForms}
  add_mem' := by
    intro p q hp hq
    show HΛ.d (p + q) ∈ M.pcForms
    rw [map_add]
    exact add_mem hp hq
  zero_mem' := by
    show HΛ.d (0 : HΛ (Ioo a b) 0) ∈ M.pcForms
    rw [map_zero]
    exact zero_mem _
  smul_mem' := by
    intro c p hp
    show HΛ.d (c • p) ∈ M.pcForms
    rw [map_smul]
    exact Submodule.smul_mem _ _ hp

theorem mem_linForms {p : HΛ (Ioo a b) 0} : p ∈ M.linForms ↔ HΛ.d p ∈ M.pcForms := Iff.rfl

/-- `M.linForms` consists exactly of the continuous piecewise linear functions: primitives of
piecewise constants, up to an additive constant. -/
theorem mem_linForms_iff {p : HΛ (Ioo a b) 0} :
    p ∈ M.linForms ↔ ∃ c : ℝ, ∃ s ∈ M.pcConst,
      (s0 (HΛ.toL2 p) : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)] fun x => c + ∫ t in a..x, s t := by
  constructor
  · intro hp
    have hwd : HasWeakDeriv (s0 (HΛ.toL2 p)) (s1 (HΛ.toL2 (HΛ.d p))) :=
      (hasWeakExtDeriv_iff _ _).1 p.2
    obtain ⟨c, hc⟩ := hwd.ae_eq_const_add_primitive
    exact ⟨c, _, hp, hc⟩
  · rintro ⟨c, s, hs, h⟩
    have h1 : HasWeakDeriv (s0 (HΛ.toL2 p) - primitive s) 0 := by
      refine hasWeakDeriv_of_ae_const (c := c) ?_
      filter_upwards [h, Lp.coeFn_sub (s0 (HΛ.toL2 p)) (primitive s), coeFn_primitive s]
        with x hx1 hx2 hx3
      rw [hx2, Pi.sub_apply, hx1, hx3]; ring
    have h2 : HasWeakDeriv (s0 (HΛ.toL2 p)) s := by
      have := h1.add (hasWeakDeriv_primitive s)
      simpa using this
    have h3 : HasWeakExtDeriv (HΛ.toL2 p) (s1.symm s) :=
      (hasWeakExtDeriv_iff _ _).2 (by simpa using h2)
    have h4 : HΛ.toL2 (HΛ.d p) = s1.symm s := HasWeakExtDeriv.unique isOpen_Ioo p.2 h3
    change s1 (HΛ.toL2 (HΛ.d p)) ∈ M.pcConst
    rw [h4, LinearIsometryEquiv.apply_symm_apply]
    exact hs

theorem isClosed_pcForms : IsClosed (M.pcForms : Set (HΛ (Ioo a b) 1)) := by
  have : (M.pcForms : Set (HΛ (Ioo a b) 1)) =
      (fun p => s1 (HΛ.toL2 p)) ⁻¹' (M.pcConst : Set (L2I a b)) := rfl
  rw [this]
  exact (Submodule.closed_of_finiteDimensional M.pcConst).preimage
    (s1.continuous.comp HΛ.toL2.continuous)

theorem isClosed_linForms : IsClosed (M.linForms : Set (HΛ (Ioo a b) 0)) := by
  have : (M.linForms : Set (HΛ (Ioo a b) 0)) =
      (fun p => HΛ.d p) ⁻¹' (M.pcForms : Set (HΛ (Ioo a b) 1)) := rfl
  rw [this]
  exact M.isClosed_pcForms.preimage HΛ.d.continuous

instance : CompleteSpace M.pcForms := M.isClosed_pcForms.completeSpace_coe

instance : CompleteSpace M.linForms := M.isClosed_linForms.completeSpace_coe

end Mesh

/-- The finite element subcomplex of a mesh: continuous piecewise linears in degree `0`,
piecewise constants in degree `1` (and everything, i.e. `0`, in higher degrees). -/
noncomputable def meshSubcomplex (M : Mesh a b) : (intervalComplex a b).Subcomplex where
  carrier
    | 0 => M.linForms
    | 1 => M.pcForms
    | _ + 2 => ⊤
  map_d := by
    intro k
    match k with
    | 0 => exact fun u hu => hu
    | 1 => exact fun u _ => Submodule.mem_top
    | k + 2 => exact fun u _ => Submodule.mem_top

instance (M : Mesh a b) (k : ℕ) : CompleteSpace ((meshSubcomplex M).carrier k) := by
  match k with
  | 0 => exact inferInstanceAs (CompleteSpace M.linForms)
  | 1 => exact inferInstanceAs (CompleteSpace M.pcForms)
  | k + 2 => exact inferInstanceAs (CompleteSpace (⊤ : Submodule ℝ (HΛ (Ioo a b) (k + 2))))

/-- The `L²` projection onto piecewise constant `1`-forms (orthogonal projection in `HΛ¹`,
which for `1`-forms is the `L²` projection, as `HΛ¹ ≅ L²`). -/
noncomputable def meshπ₁ (M : Mesh a b) : HΛ (Ioo a b) 1 →L[ℝ] HΛ (Ioo a b) 1 :=
  M.pcForms.starProjection

/-- The projection in degree `0`: the lift of `meshπ₁` through `d`. -/
noncomputable def meshπ₀ (M : Mesh a b) : HΛ (Ioo a b) 0 →L[ℝ] HΛ (Ioo a b) 0 :=
  liftProjection (HΛ.d : HΛ (Ioo a b) 0 →L[ℝ] HΛ (Ioo a b) 1) d_surjective (meshπ₁ M)

/-- The projections in all degrees. -/
noncomputable def meshπ (M : Mesh a b) : ∀ k, HΛ (Ioo a b) k →L[ℝ] HΛ (Ioo a b) k
  | 0 => meshπ₀ M
  | 1 => meshπ₁ M
  | _ + 2 => ContinuousLinearMap.id ℝ _

theorem meshπ₁_mem (M : Mesh a b) (x : HΛ (Ioo a b) 1) : meshπ₁ M x ∈ M.pcForms :=
  Submodule.starProjection_apply_mem _ _

theorem meshπ₁_id (M : Mesh a b) {x : HΛ (Ioo a b) 1} (hx : x ∈ M.pcForms) : meshπ₁ M x = x :=
  Submodule.starProjection_eq_self_iff.2 hx

theorem d_meshπ₀ (M : Mesh a b) (x : HΛ (Ioo a b) 0) :
    HΛ.d (meshπ₀ M x) = meshπ₁ M (HΛ.d x) :=
  map_liftProjection (HΛ.d : HΛ (Ioo a b) 0 →L[ℝ] HΛ (Ioo a b) 1) d_surjective (meshπ₁ M) x

theorem meshπ₀_mem (M : Mesh a b) (x : HΛ (Ioo a b) 0) : meshπ₀ M x ∈ M.linForms := by
  rw [Mesh.mem_linForms, d_meshπ₀]
  exact meshπ₁_mem M _

theorem meshπ₀_id (M : Mesh a b) {x : HΛ (Ioo a b) 0} (hx : x ∈ M.linForms) :
    meshπ₀ M x = x :=
  liftProjection_eq_self (HΛ.d : HΛ (Ioo a b) 0 →L[ℝ] HΛ (Ioo a b) 1) d_surjective (meshπ₁ M)
    (meshπ₁_id M hx)

/-- A cochain projection onto the finite element subcomplex of a mesh: the `L²` projection
onto piecewise constants in degree `1`, and its lift through `d` (`liftProjection`) in
degree `0`. -/
noncomputable def meshProjection (M : Mesh a b) :
    (intervalComplex a b).CochainProjection (meshSubcomplex M) where
  π := meshπ M
  π_mem := by
    intro k
    match k with
    | 0 => exact fun u => meshπ₀_mem M u
    | 1 => exact fun u => meshπ₁_mem M u
    | k + 2 => exact fun u => Submodule.mem_top
  π_id := by
    intro k
    match k with
    | 0 => exact fun u hu => meshπ₀_id M hu
    | 1 => exact fun u hu => meshπ₁_id M hu
    | k + 2 => exact fun u _ => rfl
  comm := by
    intro k
    match k with
    | 0 => exact fun u => (d_meshπ₀ M u).symm
    | 1 => exact fun u => Subsingleton.elim _ _
    | k + 2 => exact fun u => rfl

theorem meshProjection_π_zero (M : Mesh a b) : (meshProjection M).π 0 = meshπ₀ M := rfl

theorem meshProjection_π_one (M : Mesh a b) : (meshProjection M).π 1 = meshπ₁ M := rfl

theorem norm_d_le (x : HΛ (Ioo a b) 0) : ‖(HΛ.d x : HΛ (Ioo a b) 1)‖ ≤ ‖x‖ :=
  ((intervalComplex a b).segment 0).norm_d₀_le x

theorem norm_d_op_le : ‖(HΛ.d : HΛ (Ioo a b) 0 →L[ℝ] HΛ (Ioo a b) 1)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [one_mul]; exact norm_d_le x

theorem norm_meshπ₁_le (M : Mesh a b) : ‖meshπ₁ M‖ ≤ 1 :=
  Submodule.starProjection_norm_le _

/-- **The cochain projections are bounded uniformly in the mesh**, by `1 + c` where `c` is a
Poincaré constant of the complex. -/
theorem norm_meshProjection_le (M : Mesh a b) {c : ℝ}
    (hc : ((intervalComplex a b).segment 0).HasPoincareConst c) (j : ℕ) :
    ‖(meshProjection M).π j‖ ≤ 1 + c := by
  have hc0 := hc.nonneg
  match j with
  | 0 =>
    have h : ‖meshπ₀ M‖ ≤ 1 + c * ‖meshπ₁ M‖ * ‖(HΛ.d : HΛ (Ioo a b) 0 →L[ℝ] HΛ (Ioo a b) 1)‖ :=
      norm_liftProjection_le (HΛ.d : HΛ (Ioo a b) 0 →L[ℝ] HΛ (Ioo a b) 1)
      d_surjective (meshπ₁ M) (c := c) (fun x hx => hc.le₀ x hx)
    have h1 : c * ‖meshπ₁ M‖ * ‖(HΛ.d : HΛ (Ioo a b) 0 →L[ℝ] HΛ (Ioo a b) 1)‖ ≤ c * 1 * 1 := by
      gcongr
      · exact norm_meshπ₁_le M
      · exact norm_d_op_le
    change ‖meshπ₀ M‖ ≤ 1 + c
    linarith
  | 1 =>
    change ‖meshπ₁ M‖ ≤ 1 + c
    linarith [norm_meshπ₁_le M]
  | k + 2 =>
    change ‖ContinuousLinearMap.id ℝ (HΛ (Ioo a b) (k + 2))‖ ≤ 1 + c
    linarith [ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := HΛ (Ioo a b) (k + 2))]

/-! ### Well-posedness -/

/-- The mixed problem on the interval has a solution for every `f ∈ L²Λ¹`. -/
theorem exists_isSolution (f : L2Form (Ioo a b) 1) :
    ∃ σ u p, ((intervalComplex a b).segment 0).IsSolution f σ u p := by
  obtain ⟨c, hc⟩ := (intervalComplex a b).exists_hasPoincareConst_segment
    intervalComplex_isClosed 0
  exact ShortHilbertComplex.exists_isSolution hc f

/-- The mixed finite element problem on a mesh has a solution for every `f ∈ L²Λ¹`. -/
theorem exists_discrete_isSolution (M : Mesh a b) (f : L2Form (Ioo a b) 1) :
    ∃ σh uh ph, ((meshSubcomplex M).segment 0).toShort.IsSolution f σh uh ph := by
  obtain ⟨c, hc⟩ := (intervalComplex a b).exists_hasPoincareConst_segment
    intervalComplex_isClosed 0
  obtain ⟨σh, uh, ph, h, -⟩ := HilbertComplex.galerkin_wellPosed (meshProjection M) 0 hc
    (norm_meshProjection_le M hc) f
  exact ⟨σh, uh, ph, h⟩

/-! ### Regularity of the solution -/

/-- The second equation of the mixed problem says `dσ = f`. -/
theorem IsSolution.toL2_d_eq {f : L2Form (Ioo a b) 1} {σ : HΛ (Ioo a b) 0}
    {u p : HΛ (Ioo a b) 1} (h : ((intervalComplex a b).segment 0).IsSolution f σ u p) :
    HΛ.toL2 (HΛ.d σ) = f := by
  have hp : p = 0 := by
    have := h.harmonic
    rw [harmonic_eq_bot] at this
    exact (Submodule.mem_bot ℝ).1 this
  subst hp
  have key : ∀ w : L2Form (Ioo a b) 1, inner ℝ (HΛ.toL2 (HΛ.d σ) - f) w = 0 := by
    intro w
    obtain ⟨v, rfl⟩ := toL2_surjective w
    have h1 := h.eq₁ v
    have h0 : ((intervalComplex a b).segment 0).d₁ u = 0 := Subsingleton.elim _ _
    have h0' : ((intervalComplex a b).segment 0).d₁ v = 0 := Subsingleton.elim _ _
    rw [h0, h0'] at h1
    simp only [map_zero, inner_zero_left, inner_zero_right, add_zero] at h1
    rw [inner_sub_left]
    exact sub_eq_zero.2 h1
  exact sub_eq_zero.1 (inner_self_eq_zero.1 (key _))

/-- The first equation of the mixed problem says that `u` has weak derivative `-σ`. -/
theorem IsSolution.hasWeakDeriv {f : L2Form (Ioo a b) 1} {σ : HΛ (Ioo a b) 0}
    {u p : HΛ (Ioo a b) 1} (h : ((intervalComplex a b).segment 0).IsSolution f σ u p) :
    HasWeakDeriv (s1 (HΛ.toL2 u)) (-(s0 (HΛ.toL2 σ))) := by
  intro φ hφ
  set Φ : L2I a b := hφ.memLp.toLp φ with hΦdef
  set Φ' : L2I a b := hφ.memLp_deriv.toLp (deriv φ) with hΦ'def
  have cΦ : Φ =ᵐ[volume.restrict (Ioo a b)] φ := hφ.memLp.coeFn_toLp
  have cΦ' : Φ' =ᵐ[volume.restrict (Ioo a b)] deriv φ := hφ.memLp_deriv.coeFn_toLp
  have hΦ : HasWeakDeriv Φ Φ' := by
    intro ψ hψ
    have e1 : ∫ x in Ioo a b, Φ' x * ψ x = ∫ x in Ioo a b, deriv φ x * ψ x := by
      refine integral_congr_ae ?_
      filter_upwards [cΦ'] with x hx
      rw [hx]
    have e2 : ∫ x in Ioo a b, Φ x * deriv ψ x = ∫ x in Ioo a b, φ x * deriv ψ x := by
      refine integral_congr_ae ?_
      filter_upwards [cΦ] with x hx
      rw [hx]
    rw [e1, e2]
    exact integral_deriv_mul_testFn hφ hψ
  have hτ : HasWeakExtDeriv (s0.symm Φ) (s1.symm Φ') :=
    (hasWeakExtDeriv_iff _ _).2 (by simpa using hΦ)
  let τ : HΛ (Ioo a b) 0 := ⟨WithLp.toLp 2 (s0.symm Φ, s1.symm Φ'), hτ⟩
  have e := h.eq₀ τ
  have e0 : inner ℝ (HΛ.toL2 σ) (s0.symm Φ) = inner ℝ (s1.symm Φ') (HΛ.toL2 u) := by
    have e1 : inner ℝ (HΛ.toL2 σ) (HΛ.toL2 τ) - inner ℝ (HΛ.toL2 (HΛ.d τ)) (HΛ.toL2 u) = 0 := e
    have e2 : HΛ.toL2 τ = s0.symm Φ := rfl
    have e3 : HΛ.toL2 (HΛ.d τ) = s1.symm Φ' := rfl
    rw [e2, e3] at e1
    linarith
  rw [← s0.inner_map_map, ← s1.inner_map_map] at e0
  simp only [LinearIsometryEquiv.apply_symm_apply] at e0
  rw [inner_L2I, inner_L2I] at e0
  have e4 : ∫ x in Ioo a b, (s0 (HΛ.toL2 σ)) x * Φ x
      = ∫ x in Ioo a b, (s0 (HΛ.toL2 σ)) x * φ x := by
    refine integral_congr_ae ?_
    filter_upwards [cΦ] with x hx
    rw [hx]
  have e5 : ∫ x in Ioo a b, Φ' x * (s1 (HΛ.toL2 u)) x
      = ∫ x in Ioo a b, (s1 (HΛ.toL2 u)) x * deriv φ x := by
    refine integral_congr_ae ?_
    filter_upwards [cΦ'] with x hx
    rw [hx, mul_comm]
  have e6 : ∫ x in Ioo a b, (-(s0 (HΛ.toL2 σ)) : L2I a b) x * φ x
      = -∫ x in Ioo a b, (s0 (HΛ.toL2 σ)) x * φ x := by
    rw [← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_neg (s0 (HΛ.toL2 σ))] with x hx
    rw [hx]; simp
  rw [e6, ← e4, e0, e5]

/-! ### Convergence -/

theorem sub_self_mem {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Submodule ℝ E) (u : E) : u - u ∈ K := by
  rw [sub_self]; exact K.zero_mem

theorem eq_zero_of_mem_harmonic {p : HΛ (Ioo a b) 1}
    (hp : p ∈ ((intervalComplex a b).segment 0).harmonic) : p = 0 := by
  rw [harmonic_eq_bot] at hp
  exact (Submodule.mem_bot ℝ).1 hp

theorem mem_coboundaries_all (u : HΛ (Ioo a b) 1) :
    u ∈ ((intervalComplex a b).segment 0).coboundaries := by
  obtain ⟨τ', hτ'⟩ := d_surjective u
  exact ⟨τ', hτ'⟩

theorem harmonic_approx (M : Mesh a b) :
    ∀ r ∈ ((intervalComplex a b).segment 0).harmonic,
      ‖r - (meshProjection M).π (0 + 1) r‖ ≤ (0 : ℝ) * ‖r‖ := by
  intro r hr
  have : r = 0 := eq_zero_of_mem_harmonic hr
  subst this
  simp only [map_zero, sub_zero, norm_zero, mul_zero, le_refl]

theorem galerkin_aux (M : Mesh a b) {c : ℝ}
    (hc : ((intervalComplex a b).segment 0).HasPoincareConst c)
    {f : L2Form (Ioo a b) 1} {σ : HΛ (Ioo a b) 0} {u p : HΛ (Ioo a b) 1}
    (h : ((intervalComplex a b).segment 0).IsSolution f σ u p)
    {σh : (meshSubcomplex M).carrier 0} {uh ph : (meshSubcomplex M).carrier 1}
    (hh : ((meshSubcomplex M).segment 0).toShort.IsSolution f σh uh ph)
    (τ : (meshSubcomplex M).carrier 0) (v : (meshSubcomplex M).carrier 1) :
    ‖σ - σh‖ + ‖u - uh‖ + ‖p - ph‖ ≤ errorConst c (1 + c) *
      (‖σ - τ‖ + ‖u - v‖ + ‖p - ((0 : (meshSubcomplex M).carrier 1) : HΛ (Ioo a b) 1)‖ +
        (0 : ℝ) * ‖u - ((0 : (meshSubcomplex M).carrier 1) : HΛ (Ioo a b) 1)‖) :=
  HilbertComplex.galerkin_error_estimate (meshProjection M) 0 hc
    (norm_meshProjection_le M hc) (μ := 0) le_rfl (harmonic_approx M) h hh
    (mem_coboundaries_all u) (sub_self_mem _ u) τ v 0 0

theorem real_aux (A C x y z t : ℝ) (hz : z = 0) (h : A ≤ C * (x + y + z + 0 * t)) :
    A ≤ C * (x + y) := by
  rw [hz] at h; simpa using h

/-- Quasi-optimality with an explicit Poincaré constant. -/
theorem quasi_optimal_aux (M : Mesh a b) {c : ℝ}
    (hc : ((intervalComplex a b).segment 0).HasPoincareConst c)
    {f : L2Form (Ioo a b) 1} {σ : HΛ (Ioo a b) 0} {u p : HΛ (Ioo a b) 1}
    (h : ((intervalComplex a b).segment 0).IsSolution f σ u p)
    {σh : (meshSubcomplex M).carrier 0} {uh ph : (meshSubcomplex M).carrier 1}
    (hh : ((meshSubcomplex M).segment 0).toShort.IsSolution f σh uh ph)
    (τ : (meshSubcomplex M).carrier 0) (v : (meshSubcomplex M).carrier 1) :
    ‖σ - σh‖ + ‖u - uh‖ + ‖p - ph‖ ≤ errorConst c (1 + c) * (‖σ - τ‖ + ‖u - v‖) := by
  have hp : p = 0 := eq_zero_of_mem_harmonic h.harmonic
  have := galerkin_aux M hc h hh τ v
  have h0 : ‖p - ((0 : (meshSubcomplex M).carrier 1) : HΛ (Ioo a b) 1)‖ = 0 := by
    rw [Submodule.coe_zero, sub_zero, hp, norm_zero]
  exact real_aux _ _ _ _ _ _ h0 this

/-- **Quasi-optimality of the mixed finite element method on an interval**, with a constant
independent of the mesh. -/
theorem interval_mixed_quasi_optimal :
    ∃ C : ℝ, ∀ (M : Mesh a b) (f : L2Form (Ioo a b) 1)
      (σ : HΛ (Ioo a b) 0) (u p : HΛ (Ioo a b) 1)
      (_ : ((intervalComplex a b).segment 0).IsSolution f σ u p)
      (σh : (meshSubcomplex M).carrier 0) (uh ph : (meshSubcomplex M).carrier 1)
      (_ : ((meshSubcomplex M).segment 0).toShort.IsSolution f σh uh ph)
      (τ : (meshSubcomplex M).carrier 0) (v : (meshSubcomplex M).carrier 1),
      ‖σ - σh‖ + ‖u - uh‖ + ‖p - ph‖ ≤ C * (‖σ - τ‖ + ‖u - v‖) := by
  obtain ⟨c, hc⟩ := (intervalComplex a b).exists_hasPoincareConst_segment
    intervalComplex_isClosed 0
  exact ⟨errorConst c (1 + c), fun M f σ u p h σh uh ph hh τ v =>
    quasi_optimal_aux M hc h hh τ v⟩

/-! ### Approximation helpers -/

/-- The `1`-form with `L²` representative `s1.symm s`. -/
noncomputable def pc1 (s : L2I a b) : HΛ (Ioo a b) 1 :=
  ⟨WithLp.toLp 2 (s1.symm s, 0), hasWeakExtDeriv_zero _⟩

theorem toL2_pc1 (s : L2I a b) : HΛ.toL2 (pc1 s) = s1.symm s := rfl

theorem pc1_mem (M : Mesh a b) {s : L2I a b} (hs : s ∈ M.pcConst) : pc1 s ∈ M.pcForms := by
  change s1 (HΛ.toL2 (pc1 s)) ∈ M.pcConst
  rw [toL2_pc1, LinearIsometryEquiv.apply_symm_apply]
  exact hs

theorem norm_eq_toL2 (w : HΛ (Ioo a b) 1) : ‖w‖ = ‖HΛ.toL2 w‖ := by
  have h0 : ((intervalComplex a b).segment 0).d₁ w = 0 := Subsingleton.elim _ _
  exact (((intervalComplex a b).segment 0).norm_eq_of_d₁_eq_zero h0).symm

theorem norm_sub_pc1 (w : HΛ (Ioo a b) 1) (s : L2I a b) :
    ‖w - pc1 s‖ = ‖s1 (HΛ.toL2 w) - s‖ := by
  rw [norm_eq_toL2, map_sub, toL2_pc1, ← s1.norm_map, map_sub,
    LinearIsometryEquiv.apply_symm_apply]

theorem norm_toL2_le {k : ℕ} (w : HΛ (Ioo a b) k) : ‖HΛ.toL2 w‖ ≤ ‖w‖ :=
  ((intervalComplex a b).segment k).norm_ι₀_le w

theorem norm_toL2_d_le (w : HΛ (Ioo a b) 0) : ‖HΛ.toL2 (HΛ.d w)‖ ≤ ‖w‖ := by
  have := ((intervalComplex a b).segment 0).norm_ι₁_d₀ w
  have h2 := ((intervalComplex a b).segment 0).norm_d₀_le w
  calc ‖HΛ.toL2 (HΛ.d w)‖ = ‖(HΛ.d w : HΛ (Ioo a b) 1)‖ := this
    _ ≤ ‖w‖ := h2

theorem norm_sub_meshπ₁_le (M : Mesh a b) (y : HΛ (Ioo a b) 1) {w : HΛ (Ioo a b) 1}
    (hw : w ∈ M.pcForms) : ‖y - meshπ₁ M y‖ ≤ ‖y - w‖ := by
  unfold meshπ₁
  rw [Submodule.starProjection_minimal]
  exact ciInf_le ⟨0, by rintro _ ⟨x, rfl⟩; exact norm_nonneg _⟩ (⟨w, hw⟩ : M.pcForms)

/-- The error of the lifted projection `π⁰` on a solution `σ` with `d σ = f`, where `s1 f` is
within `ε` of the piecewise constants. -/
theorem norm_sub_meshπ₀_le (M : Mesh a b) {c : ℝ}
    (hc : ((intervalComplex a b).segment 0).HasPoincareConst c) (σ : HΛ (Ioo a b) 0)
    {s : L2I a b} (hs : s ∈ M.pcConst) :
    ‖σ - meshπ₀ M σ‖ ≤ c * ‖s1 (HΛ.toL2 (HΛ.d σ)) - s‖ := by
  have hmem := sub_liftProjection_mem (HΛ.d : HΛ (Ioo a b) 0 →L[ℝ] HΛ (Ioo a b) 1)
    d_surjective (meshπ₁ M) σ
  have h1 : ‖σ - meshπ₀ M σ‖ ≤ c * ‖(HΛ.d (σ - meshπ₀ M σ) : HΛ (Ioo a b) 1)‖ :=
    hc.le₀ _ hmem
  have h2 : HΛ.d (σ - meshπ₀ M σ) = HΛ.d σ - meshπ₁ M (HΛ.d σ) := by
    rw [map_sub, d_meshπ₀]
  rw [h2] at h1
  have h3 : ‖HΛ.d σ - meshπ₁ M (HΛ.d σ)‖ ≤ ‖s1 (HΛ.toL2 (HΛ.d σ)) - s‖ := by
    rw [← norm_sub_pc1]
    exact norm_sub_meshπ₁_le M _ (pc1_mem M hs)
  exact h1.trans (by gcongr; exact hc.nonneg)

theorem errorConst_nonneg {c : ℝ} (hc : 0 ≤ c) : 0 ≤ errorConst c (1 + c) := by
  unfold errorConst
  have := stabilityConst_pos (c * (1 + c))
  positivity

theorem hodgeStar_norm_le (φ : HΛ (Ioo a b) 0) : ‖hodgeStar (HΛ.toL2 φ)‖ ≤ ‖φ‖ := by
  have : ‖hodgeStar (HΛ.toL2 φ)‖ = ‖HΛ.toL2 φ‖ := by
    simp [hodgeStar]
  rw [this]; exact norm_toL2_le φ

theorem s1_hodgeStar (φ : HΛ (Ioo a b) 0) :
    s1 (hodgeStar (HΛ.toL2 φ)) = s0 (HΛ.toL2 φ) := by
  simp [hodgeStar]

theorem norm_sigma_le {c : ℝ} (hc : ((intervalComplex a b).segment 0).HasPoincareConst c)
    {φ σ : HΛ (Ioo a b) 0} {u p : HΛ (Ioo a b) 1}
    (h : ((intervalComplex a b).segment 0).IsSolution (hodgeStar (HΛ.toL2 φ)) σ u p) :
    ‖σ‖ + ‖u‖ + ‖p‖ ≤ stabilityConst c * ‖φ‖ := by
  have hnorm : ‖σ‖ + ‖u‖ + ‖p‖ ≤ stabilityConst c * ‖hodgeStar (HΛ.toL2 φ)‖ :=
    h.norm_le hc
  exact hnorm.trans (mul_le_mul_of_nonneg_left (hodgeStar_norm_le φ) (stabilityConst_pos c).le)

theorem approx_u (M : Mesh a b) {c : ℝ}
    (hc : ((intervalComplex a b).segment 0).HasPoincareConst c)
    {φ σ : HΛ (Ioo a b) 0} {u p : HΛ (Ioo a b) 1}
    (h : ((intervalComplex a b).segment 0).IsSolution (hodgeStar (HΛ.toL2 φ)) σ u p) :
    ∃ s ∈ M.pcConst, ‖u - pc1 s‖ ≤ M.size * (stabilityConst c * ‖φ‖) := by
  have hwd := IsSolution.hasWeakDeriv h
  have hσ : ‖σ‖ ≤ stabilityConst c * ‖φ‖ := by
    have := norm_sigma_le hc h
    linarith [norm_nonneg u, norm_nonneg p]
  obtain ⟨s, hs, hsn⟩ := M.exists_pcConst_near hwd
  refine ⟨s, hs, ?_⟩
  rw [norm_sub_pc1]
  refine hsn.trans ?_
  rw [norm_neg, s0.norm_map]
  exact mul_le_mul_of_nonneg_left ((norm_toL2_le σ).trans hσ) M.size_pos.le

theorem approx_σ (M : Mesh a b) {c : ℝ}
    (hc : ((intervalComplex a b).segment 0).HasPoincareConst c)
    {φ σ : HΛ (Ioo a b) 0} {u p : HΛ (Ioo a b) 1}
    (h : ((intervalComplex a b).segment 0).IsSolution (hodgeStar (HΛ.toL2 φ)) σ u p) :
    ‖σ - meshπ₀ M σ‖ ≤ c * (M.size * ‖φ‖) := by
  have hdσ := IsSolution.toL2_d_eq h
  obtain ⟨s', hs', hs'n⟩ := M.exists_pcConst_near
    ((hasWeakExtDeriv_iff _ _).1 φ.2 : HasWeakDeriv (s0 (HΛ.toL2 φ)) (s1 (HΛ.toL2 (HΛ.d φ))))
  refine (norm_sub_meshπ₀_le M hc σ hs').trans ?_
  rw [hdσ, s1_hodgeStar]
  refine mul_le_mul_of_nonneg_left (hs'n.trans ?_) hc.nonneg
  exact mul_le_mul_of_nonneg_left (by rw [s1.norm_map]; exact norm_toL2_d_le φ) M.size_pos.le

/-- **Convergence of the mixed finite element method on an interval.** There is a constant
`C`, depending only on the interval, such that for every mesh `M` of `(a, b)` with mesh size
`h = M.size`, and every right-hand side `f = ⋆φ` with `φ ∈ H¹(a,b)`, the solution `(σ, u, p)`
of the Hodge Laplace problem on `1`-forms and its Galerkin approximation `(σh, uh, ph)` in
continuous piecewise linear × piecewise constant elements satisfy
`‖σ - σh‖_{H¹} + ‖u - uh‖_{L²} + ‖p - ph‖ ≤ C h ‖φ‖_{H¹}`.

No hypothesis is left over: closedness of the complex, the bounded cochain projection and the
approximation estimates are all proved. -/
theorem interval_mixed_convergence :
    ∃ C : ℝ, ∀ (M : Mesh a b) (φ : HΛ (Ioo a b) 0)
      (σ : HΛ (Ioo a b) 0) (u p : HΛ (Ioo a b) 1)
      (_ : ((intervalComplex a b).segment 0).IsSolution (hodgeStar (HΛ.toL2 φ)) σ u p)
      (σh : (meshSubcomplex M).carrier 0) (uh ph : (meshSubcomplex M).carrier 1)
      (_ : ((meshSubcomplex M).segment 0).toShort.IsSolution (hodgeStar (HΛ.toL2 φ)) σh uh ph),
      ‖σ - σh‖ + ‖u - uh‖ + ‖p - ph‖ ≤ C * M.size * ‖φ‖ := by
  obtain ⟨c, hc⟩ := (intervalComplex a b).exists_hasPoincareConst_segment
    intervalComplex_isClosed 0
  refine ⟨errorConst c (1 + c) * (c + stabilityConst c), fun M φ σ u p h σh uh ph hh => ?_⟩
  obtain ⟨s, hs, hu⟩ := approx_u M hc h
  have hσ' := approx_σ M hc h
  have hq := quasi_optimal_aux M hc h hh ⟨meshπ₀ M σ, meshπ₀_mem M σ⟩ ⟨pc1 s, pc1_mem M hs⟩
  refine hq.trans ?_
  have hsum : ‖σ - meshπ₀ M σ‖ + ‖u - pc1 s‖ ≤ (c + stabilityConst c) * M.size * ‖φ‖ := by
    calc _ ≤ c * (M.size * ‖φ‖) + M.size * (stabilityConst c * ‖φ‖) := add_le_add hσ' hu
      _ = _ := by ring
  calc _ ≤ errorConst c (1 + c) * ((c + stabilityConst c) * M.size * ‖φ‖) :=
        mul_le_mul_of_nonneg_left hsum (errorConst_nonneg hc.nonneg)
    _ = _ := by ring

end FEEC.Interval
