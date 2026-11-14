/-
The homotopy operators for the codifferential in one coordinate direction.
-/
import FEEC.DeRham.Wedge
import FEEC.DeRham.LineG

/-!
# A homotopy for the codifferential in one direction

Fix a unit vector `e` and a bump `θ`. For a compactly supported smooth form `φ` put

* `homotopyS e θ φ = e♭ ∧ lineG e θ φ` (raises the degree by one),
* `homotopyQ e θ φ = θ(⟪e, x⟫) • tangPart e (lineInt e φ x)`.

Then `δ (S φ) + S (δ φ) = φ - Q φ` (`FEEC.codiff_homotopyS`): modulo `δ`-exact forms and the
image of `δφ`, a form can be replaced by `Q φ`, which no longer involves `e`
(`e ⌟ Q φ = 0`). Both operators preserve test forms on a slab, and `Q` commutes with `δ`.
-/

namespace FEEC

set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

open MeasureTheory

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {k : ℕ}

/-- `tangPart e` extended to degree `0`, where it is the identity. -/
noncomputable def tangPartAll (e : E) :
    (k : ℕ) → (E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] (E [⋀^Fin k]→L[ℝ] ℝ)
  | 0 => ContinuousLinearMap.id ℝ _
  | (_ + 1) => tangPart e

theorem tangPartAll_succ (e : E) (α : E [⋀^Fin (k + 1)]→L[ℝ] ℝ) :
    tangPartAll e (k + 1) α = tangPart e α := rfl

theorem curryLeft_smul' (c : ℝ) (a : E [⋀^Fin (k + 1)]→L[ℝ] ℝ) (u : E) :
    (c • a).curryLeft u = c • a.curryLeft u := by
  ext v; simp [ContinuousAlternatingMap.curryLeft_apply_apply]

theorem curryLeft_neg' (a : E [⋀^Fin (k + 1)]→L[ℝ] ℝ) (u : E) :
    (-a).curryLeft u = -a.curryLeft u := by
  ext v; simp [ContinuousAlternatingMap.curryLeft_apply_apply]

theorem curryLeft_add' (a b : E [⋀^Fin (k + 1)]→L[ℝ] ℝ) (u : E) :
    (a + b).curryLeft u = a.curryLeft u + b.curryLeft u := by
  ext v; simp [ContinuousAlternatingMap.curryLeft_apply_apply]

/-- Contraction of the tangential part. -/
theorem curryLeft_tangPart (e u : E) (α : E [⋀^Fin (k + 1)]→L[ℝ] ℝ) :
    (tangPart e α).curryLeft u = tangPartAll e k (α.curryLeft u) - ⟪e, u⟫ • α.curryLeft e := by
  rw [tangPart_apply, curryLeft_sub']
  cases k with
  | zero =>
    rw [curryLeft_wedgeLeft_zero]
    simp only [tangPartAll, ContinuousLinearMap.id_apply]
  | succ k =>
    have h : (α.curryLeft e).curryLeft u = -((α.curryLeft u).curryLeft e) := by
      rw [curryLeft_curryLeft_swap α u e, neg_neg]
    rw [curryLeft_wedgeLeft, tangPartAll_succ, tangPart_apply, h, map_neg]
    abel

/-- Linearity of contraction in the vector, for sums. -/
theorem sum_smul_curryLeft {ι : Type*} (s : Finset ι) (c : ι → ℝ) (v : ι → E)
    (a : E [⋀^Fin (k + 1)]→L[ℝ] ℝ) :
    ∑ i ∈ s, c i • a.curryLeft (v i) = a.curryLeft (∑ i ∈ s, c i • v i) := by
  have := map_sum (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := E) (F := ℝ) (n := k) a)
    (fun i => c i • v i) s
  simpa using this.symm

/-- The homotopy operator `S φ = e♭ ∧ lineG e θ φ`. -/
noncomputable def homotopyS (e : E) (θ : ℝ → ℝ) (φ : E → E [⋀^Fin k]→L[ℝ] ℝ) :
    E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ :=
  fun x => wedgeLeft e (lineG e θ φ x)

/-- The operator `Q φ = θ(⟪e, x⟫) • tangPart e (lineInt e φ x)`. -/
noncomputable def homotopyQ (e : E) (θ : ℝ → ℝ) (φ : E → E [⋀^Fin k]→L[ℝ] ℝ) :
    E → E [⋀^Fin k]→L[ℝ] ℝ :=
  fun x => θ ⟪e, x⟫ • tangPartAll e k (lineInt e φ x)

variable {e : E} {θ : ℝ → ℝ} {a b : ℝ}

theorem sum_inner_smul_stdBasis (e : E) : ∑ i, ⟪e, stdBasis E i⟫ • stdBasis E i = e := by
  have := (stdBasis E).sum_repr' e
  simpa [real_inner_comm] using this

/-- The codifferential as a single continuous linear map on derivatives. -/
noncomputable def codiffL (k : ℕ) :
    (E →L[ℝ] E [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] (E [⋀^Fin k]→L[ℝ] ℝ) :=
  (-1 : ℝ) • ∑ i, codiffCLM k (stdBasis E i)

theorem codiffL_apply (T : E →L[ℝ] E [⋀^Fin (k + 1)]→L[ℝ] ℝ) :
    codiffL k T = -∑ i, (T (stdBasis E i)).curryLeft (stdBasis E i) := by
  unfold codiffL
  rw [ContinuousLinearMap.smul_apply, neg_one_smul, ContinuousLinearMap.sum_apply]
  simp [codiffCLM_apply]

theorem codiff_eq_codiffL (φ : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ) :
    codiff φ = fun y => codiffL k (fderiv ℝ φ y) := by
  ext1 y
  rw [codiffL_apply]
  rfl

theorem codiffL_smulRight (e : E) (c : ℝ) (a : E [⋀^Fin (k + 1)]→L[ℝ] ℝ) :
    codiffL k ((c • innerSL ℝ e).smulRight a) = -(c • a.curryLeft e) := by
  rw [codiffL_apply]
  congr 1
  simp only [ContinuousLinearMap.smulRight_apply, smul_apply,
    innerSL_apply_apply, curryLeft_smul']
  have := sum_smul_curryLeft (k := k) Finset.univ (fun i => ⟪e, stdBasis E i⟫)
    (fun i => stdBasis E i) a
  rw [sum_inner_smul_stdBasis] at this
  rw [← this, Finset.smul_sum]
  simp [smul_smul]

theorem codiffL_wedge (e : E) (D : E →L[ℝ] E [⋀^Fin (k + 1)]→L[ℝ] ℝ) :
    codiffL (k + 1) ((wedgeLeft e).comp D) = -(D e) - wedgeLeft e (codiffL k D) := by
  rw [codiffL_apply, codiffL_apply]
  simp only [ContinuousLinearMap.comp_apply, curryLeft_wedgeLeft, Finset.sum_sub_distrib,
    map_neg, map_sum]
  have h1 : ∑ i, ⟪e, stdBasis E i⟫ • D (stdBasis E i) = D e := by
    conv_rhs => rw [← sum_inner_smul_stdBasis e]
    simp [map_sum]
  rw [h1]
  abel

/-- Contraction with `u` as a continuous linear map on forms. -/
noncomputable def curryLeftCLM (k : ℕ) (u : E) :
    (E [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] (E [⋀^Fin k]→L[ℝ] ℝ) :=
  (ContinuousLinearMap.apply ℝ (E [⋀^Fin k]→L[ℝ] ℝ) u).comp
    (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := E) (F := ℝ) (n := k)).toContinuousLinearMap

theorem curryLeftCLM_apply (u : E) (a : E [⋀^Fin (k + 1)]→L[ℝ] ℝ) :
    curryLeftCLM k u a = a.curryLeft u := rfl

section Apply

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem lineInt_apply_clm {e : E} (he : ‖e‖ = 1) {T : E → E →L[ℝ] F} (hT : Continuous T)
    (hc : HasCompactSupport T) (x v : E) :
    lineInt e T x v = lineInt e (fun y => T y v) x := by
  unfold lineInt
  rw [ContinuousLinearMap.integral_apply (integrable_comp_line he hT hc x)]

theorem halfLineInt_apply_clm {e : E} (he : ‖e‖ = 1) {T : E → E →L[ℝ] F} (hT : Continuous T)
    (hc : HasCompactSupport T) (x v : E) :
    halfLineInt e T x v = halfLineInt e (fun y => T y v) x := by
  unfold halfLineInt
  rw [ContinuousLinearMap.integral_apply (integrable_comp_line he hT hc x).integrableOn]

end Apply

theorem lineInt_negsum {e : E} (he : ‖e‖ = 1) {ι : Type*} (s : Finset ι)
    {g : ι → E → E [⋀^Fin k]→L[ℝ] ℝ} (hg : ∀ i, Continuous (g i))
    (hc : ∀ i, HasCompactSupport (g i)) (x : E) :
    lineInt e (fun y => -∑ i ∈ s, g i y) x = -∑ i ∈ s, lineInt e (g i) x := by
  unfold lineInt
  rw [integral_neg, integral_finset_sum _ (fun i _ => integrable_comp_line he (hg i) (hc i) x)]

theorem halfLineInt_negsum {e : E} (he : ‖e‖ = 1) {ι : Type*} (s : Finset ι)
    {g : ι → E → E [⋀^Fin k]→L[ℝ] ℝ} (hg : ∀ i, Continuous (g i))
    (hc : ∀ i, HasCompactSupport (g i)) (x : E) :
    halfLineInt e (fun y => -∑ i ∈ s, g i y) x = -∑ i ∈ s, halfLineInt e (g i) x := by
  unfold halfLineInt
  rw [integral_neg, integral_finset_sum _
    (fun i _ => (integrable_comp_line he (hg i) (hc i) x).integrableOn)]

theorem continuous_fderiv_apply {φ : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ} (hφ : ContDiff ℝ 1 φ) (v : E) :
    Continuous (fun y => curryLeftCLM k v (fderiv ℝ φ y v)) :=
  (curryLeftCLM k v).continuous.comp
    ((ContinuousLinearMap.apply ℝ (E [⋀^Fin (k + 1)]→L[ℝ] ℝ) v).continuous.comp
      (hφ.continuous_fderiv one_ne_zero))

theorem hasCompactSupport_fderiv_apply {φ : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ}
    (hφc : HasCompactSupport φ) (v : E) :
    HasCompactSupport (fun y => curryLeftCLM k v (fderiv ℝ φ y v)) := by
  have := (hφc.fderiv (𝕜 := ℝ)).comp_left (g := fun T : E →L[ℝ] E [⋀^Fin (k + 1)]→L[ℝ] ℝ =>
    curryLeftCLM k v (T v)) (by simp)
  exact this

theorem lineInt_codiff {e : E} (he : ‖e‖ = 1) {φ : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ}
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (x : E) :
    lineInt e (codiff φ) x = codiffL k (lineInt e (fderiv ℝ φ) x) := by
  have hfd : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv one_ne_zero
  have hfc := hφc.fderiv (𝕜 := ℝ)
  rw [codiffL_apply]
  have h1 : codiff φ = fun y => -∑ i, curryLeftCLM k (stdBasis E i) (fderiv ℝ φ y (stdBasis E i)) :=
    rfl
  rw [h1, lineInt_negsum he _ (fun i => continuous_fderiv_apply hφ _)
    (fun i => hasCompactSupport_fderiv_apply hφc _)]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lineInt_comp_clm he (f := fun y => fderiv ℝ φ y (stdBasis E i))
    ((ContinuousLinearMap.apply ℝ _ _).continuous.comp hfd)
    ((hfc).comp_left (g := fun T : E →L[ℝ] E [⋀^Fin (k + 1)]→L[ℝ] ℝ => T (stdBasis E i))
      (by simp)), lineInt_apply_clm he hfd hfc]
  rfl

theorem halfLineInt_codiff {e : E} (he : ‖e‖ = 1) {φ : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ}
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (x : E) :
    halfLineInt e (codiff φ) x = codiffL k (halfLineInt e (fderiv ℝ φ) x) := by
  have hfd : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv one_ne_zero
  have hfc := hφc.fderiv (𝕜 := ℝ)
  rw [codiffL_apply]
  have h1 : codiff φ = fun y => -∑ i, curryLeftCLM k (stdBasis E i) (fderiv ℝ φ y (stdBasis E i)) :=
    rfl
  rw [h1, halfLineInt_negsum he _ (fun i => continuous_fderiv_apply hφ _)
    (fun i => hasCompactSupport_fderiv_apply hφc _)]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [halfLineInt_comp_clm he (f := fun y => fderiv ℝ φ y (stdBasis E i))
    ((ContinuousLinearMap.apply ℝ _ _).continuous.comp hfd)
    ((hfc).comp_left (g := fun T : E →L[ℝ] E [⋀^Fin (k + 1)]→L[ℝ] ℝ => T (stdBasis E i))
      (by simp)), halfLineInt_apply_clm he hfd hfc]
  rfl

theorem lineG_codiff {e : E} {θ : ℝ → ℝ} (he : ‖e‖ = 1) {φ : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ}
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (x : E) :
    lineG e θ (codiff φ) x = codiffL k (lineG e θ (fderiv ℝ φ) x) := by
  have hfd : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv one_ne_zero
  have hfc := hφc.fderiv (𝕜 := ℝ)
  unfold lineG
  rw [lineInt_codiff he hφ hφc, halfLineInt_codiff he hφ hφc]
  rw [map_sub, map_smul]

/-- The codifferential of `lineG e θ φ`. -/
theorem codiff_lineG (hθ : IsBump θ a b) (he : ‖e‖ = 1)
    {φ : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) :
    codiff (lineG e θ φ) =
      fun x => lineG e θ (codiff φ) x - θ ⟪e, x⟫ • (lineInt e φ x).curryLeft e := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast le_top)
  ext1 x
  rw [codiff_eq_codiffL (lineG e θ φ)]
  beta_reduce
  rw [(hasFDerivAt_lineG hθ he hφ1 hφc x).fderiv, map_add, codiffL_smulRight,
    lineG_codiff he hφ1 hφc x]
  abel

/-- **The homotopy identity** `δ (S φ) + S (δ φ) = φ - Q φ`. -/
theorem codiff_homotopyS (hθ : IsBump θ a b) (he : ‖e‖ = 1)
    {φ : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) :
    codiff (homotopyS e θ φ) + homotopyS e θ (codiff φ) = φ - homotopyQ e θ φ := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast le_top)
  have hee : ⟪e, e⟫ = 1 := by simp [real_inner_self_eq_norm_sq, he]
  funext x
  set D : E →L[ℝ] E [⋀^Fin (k + 1)]→L[ℝ] ℝ :=
    (θ ⟪e, x⟫ • innerSL ℝ e).smulRight (lineInt e φ x) + lineG e θ (fderiv ℝ φ) x with hD
  have hG : HasFDerivAt (lineG e θ φ) D x := hasFDerivAt_lineG hθ he hφ1 hφc x
  have hS : HasFDerivAt (homotopyS e θ φ) ((wedgeLeft e).comp D) x :=
    (wedgeLeft e).hasFDerivAt.comp x hG
  have h1 : codiffL k D = lineG e θ (codiff φ) x - θ ⟪e, x⟫ • (lineInt e φ x).curryLeft e := by
    have := congrFun (codiff_lineG hθ he hφ hφc) x
    rw [codiff_eq_codiffL (lineG e θ φ)] at this
    beta_reduce at this
    rwa [hG.fderiv] at this
  have h2 : D e = θ ⟪e, x⟫ • lineInt e φ x - φ x := by
    rw [hD, ContinuousLinearMap.add_apply, lineG_fderiv_apply_self he hφ1 hφc]
    simp [hee, he, sub_eq_add_neg]
  have h3 : codiff (homotopyS e θ φ) x = -(D e) - wedgeLeft e (codiffL k D) := by
    rw [codiff_eq_codiffL]
    beta_reduce
    rw [hS.fderiv, codiffL_wedge]
  have h4 : homotopyQ e θ φ x = θ ⟪e, x⟫ • (lineInt e φ x - wedgeLeft e ((lineInt e φ x).curryLeft e)) := by
    rw [homotopyQ]
    simp only [tangPartAll_succ, tangPart_apply]
  show codiff (homotopyS e θ φ) x + homotopyS e θ (codiff φ) x = φ x - homotopyQ e θ φ x
  rw [h3, h1, h2, h4]
  simp only [homotopyS, map_sub, map_smul]
  module

/-- `Q` commutes with the codifferential. -/
theorem codiff_homotopyQ (hθ : IsBump θ a b) (he : ‖e‖ = 1)
    {φ : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) :
    codiff (homotopyQ e θ φ) = homotopyQ e θ (codiff φ) := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast le_top)
  have hθ1 : ContDiff ℝ 1 θ := hθ.contDiff.of_le (by exact_mod_cast le_top)
  funext x
  set T : (E [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] (E [⋀^Fin (k + 1)]→L[ℝ] ℝ) :=
    tangPartAll e (k + 1) with hT
  set M : E →L[ℝ] E [⋀^Fin (k + 1)]→L[ℝ] ℝ := lineInt e (fderiv ℝ φ) x with hM
  have hΘ : HasFDerivAt (fun y => θ ⟪e, y⟫) (deriv θ ⟪e, x⟫ • innerSL ℝ e) x :=
    ((hθ1.differentiable one_ne_zero ⟪e, x⟫).hasDerivAt).comp_hasFDerivAt x
      (innerSL ℝ e).hasFDerivAt
  have hA : HasFDerivAt (fun y => T (lineInt e φ y)) (T.comp M) x :=
    T.hasFDerivAt.comp x (hasFDerivAt_lineInt he hφ1 hφc x)
  have hQ : HasFDerivAt (homotopyQ e θ φ)
      (θ ⟪e, x⟫ • T.comp M + (deriv θ ⟪e, x⟫ • innerSL ℝ e).smulRight (T (lineInt e φ x))) x :=
    hΘ.smul hA
  have h0 : (T (lineInt e φ x)).curryLeft e = 0 := curryLeft_tangPart_self he _
  have hMe : M e = 0 := lineInt_fderiv_apply_self he hφ1 hφc x
  have h1 : codiffL k (T.comp M) = tangPartAll e k (lineInt e (codiff φ) x) := by
    rw [lineInt_codiff he hφ1 hφc, codiffL_apply, codiffL_apply]
    have key : ∀ i, (T (M (stdBasis E i))).curryLeft (stdBasis E i) =
        tangPartAll e k ((M (stdBasis E i)).curryLeft (stdBasis E i)) -
          ⟪e, stdBasis E i⟫ • (M (stdBasis E i)).curryLeft e :=
      fun i => curryLeft_tangPart e _ _
    have hsum : ∑ i, ⟪e, stdBasis E i⟫ • M (stdBasis E i) = M e := by
      conv_rhs => rw [← sum_inner_smul_stdBasis e]
      simp [map_sum]
    have hz : ∑ i, ⟪e, stdBasis E i⟫ • (M (stdBasis E i)).curryLeft e = 0 := by
      calc _ = curryLeftCLM k e (∑ i, ⟪e, stdBasis E i⟫ • M (stdBasis E i)) := by
            simp [map_sum, curryLeftCLM_apply]
        _ = 0 := by rw [hsum, hMe]; simp [curryLeftCLM_apply]
    simp only [ContinuousLinearMap.comp_apply, key, Finset.sum_sub_distrib, map_neg, map_sum, hz]
    rw [sub_zero]
  rw [codiff_eq_codiffL (homotopyQ e θ φ)]
  beta_reduce
  rw [hQ.fderiv, map_add, map_smul, codiffL_smulRight, h0, h1]
  simp [homotopyQ]

theorem curryLeft_homotopyQ_self (he : ‖e‖ = 1) (φ : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ) (x : E) :
    (homotopyQ e θ φ x).curryLeft e = 0 := by
  rw [homotopyQ, curryLeft_smul', tangPartAll_succ, curryLeft_tangPart_self he, smul_zero]

theorem curryLeft_homotopyQ_of_orthogonal {u : E} (h : ⟪e, u⟫ = 0) (he : ‖e‖ = 1)
    {φ : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hu : ∀ x, (φ x).curryLeft u = 0) (x : E) :
    (homotopyQ e θ φ x).curryLeft u = 0 := by
  have h1 : (lineInt e φ x).curryLeft u = 0 := by
    have := lineInt_comp_clm he hφ hφc (curryLeftCLM k u) x
    rw [curryLeftCLM_apply] at this
    simp only [curryLeftCLM_apply, hu] at this
    rw [← this]
    simp [lineInt]
  rw [homotopyQ, curryLeft_smul', tangPartAll_succ, curryLeft_tangPart_of_orthogonal h h1,
    smul_zero]

variable {Ω : Set E}

/-- `S` preserves test forms on a slab. -/
theorem IsTestForm.homotopyS (hΩ : IsSlab Ω e a b) (hθ : IsBump θ a b) (he : ‖e‖ = 1)
    {φ : E → E [⋀^Fin k]→L[ℝ] ℝ} (hφ : IsTestForm Ω φ) :
    IsTestForm Ω (homotopyS e θ φ) := by
  obtain ⟨h1, h2⟩ := hasCompactSupport_lineG hΩ hθ he hφ.contDiff.continuous
    hφ.hasCompactSupport hφ.tsupport_subset
  refine ⟨(wedgeLeft e).contDiff.comp (contDiff_lineG hθ he hφ.contDiff hφ.hasCompactSupport),
    h1.comp_left (g := wedgeLeft e) (map_zero _), ?_⟩
  exact (tsupport_comp_subset (g := wedgeLeft e) (map_zero _) (lineG e θ φ)).trans h2

/-- `Q` preserves test forms on a slab. -/
theorem IsTestForm.homotopyQ (hΩ : IsSlab Ω e a b) (hθ : IsBump θ a b) (he : ‖e‖ = 1)
    {φ : E → E [⋀^Fin k]→L[ℝ] ℝ} (hφ : IsTestForm Ω φ) :
    IsTestForm Ω (homotopyQ e θ φ) := by
  obtain ⟨h1, h2⟩ := hasCompactSupport_bump_smul_lineInt hΩ hθ he hφ.contDiff.continuous
    hφ.hasCompactSupport hφ.tsupport_subset
  have hQ : FEEC.homotopyQ e θ φ = fun x => tangPartAll e k (θ ⟪e, x⟫ • lineInt e φ x) := by
    funext x; simp [FEEC.homotopyQ]
  rw [hQ]
  refine ⟨(tangPartAll e k).contDiff.comp
    (((hθ.contDiff.comp (innerSL ℝ e).contDiff).smul (contDiff_lineInt he hφ.contDiff
      hφ.hasCompactSupport))),
    h1.comp_left (g := tangPartAll e k) (map_zero _), ?_⟩
  exact (tsupport_comp_subset (g := tangPartAll e k) (map_zero _)
    (fun x => θ ⟪e, x⟫ • lineInt e φ x)).trans h2

end FEEC
