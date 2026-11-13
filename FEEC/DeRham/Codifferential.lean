/-
The codifferential on smooth forms and test forms.
-/
import FEEC.DeRham.Covector

/-!
# The codifferential and test forms

On a Euclidean space `E` with orthonormal basis `e`, the *codifferential* (formal adjoint of
the exterior derivative) of a `(k+1)`-form `φ` is the `k`-form

`(δ φ)ₓ = - ∑ᵢ (∂ᵢ φ)ₓ ⌟ eᵢ`,  i.e. `(δ φ)ₓ(v₁, …, v_k) = - ∑ᵢ (Dφ(x) eᵢ)(eᵢ, v₁, …, v_k)`.

## Main results

* `FEEC.codiff_codiff`: `δ ∘ δ = 0` on `C²` forms.
* `FEEC.IsTestForm`: smooth forms compactly supported in an open set `Ω`, their stability
  under `δ`, and their classes in `L²(Ω)`.
-/

namespace FEEC

open Module MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {k : ℕ}

/-- The codifferential `δ` of a `(k+1)`-form: the formal adjoint of the exterior derivative. -/
noncomputable def codiff (φ : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ) : E → E [⋀^Fin k]→L[ℝ] ℝ :=
  fun x => -∑ i, (fderiv ℝ φ x (stdBasis E i)).curryLeft (stdBasis E i)

theorem codiff_apply (φ : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ) (x : E) :
    codiff φ x = -∑ i, (fderiv ℝ φ x (stdBasis E i)).curryLeft (stdBasis E i) := rfl

/-- The continuous linear map `T ↦ (T v).curryLeft v` underlying a term of the codifferential. -/
noncomputable def codiffCLM (k : ℕ) (v : E) :
    (E →L[ℝ] E [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] (E [⋀^Fin k]→L[ℝ] ℝ) :=
  (ContinuousLinearMap.apply ℝ (E [⋀^Fin k]→L[ℝ] ℝ) v).comp
    ((ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := E) (F := ℝ) (n := k)).toContinuousLinearMap.comp
      (ContinuousLinearMap.apply ℝ (E [⋀^Fin (k + 1)]→L[ℝ] ℝ) v))

theorem codiffCLM_apply (v : E) (T : E →L[ℝ] E [⋀^Fin (k + 1)]→L[ℝ] ℝ) :
    codiffCLM k v T = (T v).curryLeft v := rfl

theorem codiff_eq (φ : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ) :
    codiff φ = fun x => -∑ i, codiffCLM k (stdBasis E i) (fderiv ℝ φ x) := rfl

theorem _root_.ContDiff.codiff {n : ℕ∞} {φ : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ}
    (h : ContDiff ℝ (n + 1) φ) : ContDiff ℝ n (codiff φ) := by
  have h1 : ContDiff ℝ n (fderiv ℝ φ) := by
    have := h.fderiv_right (m := n) (by norm_cast)
    exact this
  rw [codiff_eq]
  exact (ContDiff.sum fun i _ => (codiffCLM k (stdBasis E i)).contDiff.comp h1).neg

theorem tsupport_codiff_subset (φ : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ) :
    tsupport (codiff φ) ⊆ tsupport φ := by
  refine closure_minimal ?_ (isClosed_tsupport _)
  intro x hx
  by_contra hxφ
  apply hx
  have h0 : fderiv ℝ φ x = 0 := by
    by_contra hne
    exact hxφ (tsupport_fderiv_subset ℝ (subset_tsupport _ hne))
  simp [codiff_eq, h0]

theorem codiff_add {φ ψ : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ} (hφ : Differentiable ℝ φ)
    (hψ : Differentiable ℝ ψ) : codiff (φ + ψ) = codiff φ + codiff ψ := by
  ext1 x
  simp only [codiff_eq, Pi.add_apply]
  rw [fderiv_add (hφ x) (hψ x)]
  simp [Finset.sum_add_distrib]
  abel

theorem codiff_const_smul (c : ℝ) {φ : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ} (hφ : Differentiable ℝ φ) :
    codiff (c • φ) = c • codiff φ := by
  ext1 x
  simp only [codiff_eq, Pi.smul_apply]
  rw [fderiv_const_smul (hφ x)]
  simp [Finset.smul_sum]

theorem curryLeft_curryLeft_swap (a : E [⋀^Fin (k + 2)]→L[ℝ] ℝ) (u w : E) :
    (a.curryLeft u).curryLeft w = -(a.curryLeft w).curryLeft u := by
  ext v
  simp only [ContinuousAlternatingMap.curryLeft_apply_apply, ContinuousAlternatingMap.neg_apply]
  have := a.toAlternatingMap.map_swap (Matrix.vecCons u (Matrix.vecCons w v)) (i := 0) (j := 1)
    (by simp)
  have e : (Matrix.vecCons u (Matrix.vecCons w v) : Fin (k + 2) → E) ∘ Equiv.swap 0 1 =
      Matrix.vecCons w (Matrix.vecCons u v) := by
    funext j
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j
    · simp
    · simp
    · simp only [Function.comp_apply]
      rw [Equiv.swap_apply_of_ne_of_ne (by simp) (Fin.succ_succ_ne_one j)]
      simp
  rw [e] at this
  change a.toAlternatingMap _ = -a.toAlternatingMap _
  linarith

/-- `δ ∘ δ = 0`: the codifferential is a differential. -/
theorem codiff_codiff {φ : E → E [⋀^Fin (k + 2)]→L[ℝ] ℝ} (hφ : ContDiff ℝ 2 φ) :
    codiff (codiff φ) = 0 := by
  ext1 x
  have hD : Differentiable ℝ (fderiv ℝ φ) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hsymm : IsSymmSndFDerivAt ℝ φ x :=
    (hφ.contDiffAt).isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  have hderiv : ∀ u, fderiv ℝ (codiff φ) x u =
      -∑ i, codiffCLM (k + 1) (stdBasis E i) (fderiv ℝ (fderiv ℝ φ) x u) := by
    intro u
    have h1 : HasFDerivAt (codiff φ) (-∑ i, (codiffCLM (k + 1) (stdBasis E i)).comp
        (fderiv ℝ (fderiv ℝ φ) x)) x := by
      rw [codiff_eq]
      refine HasFDerivAt.neg ?_
      exact HasFDerivAt.fun_sum fun i _ =>
        (codiffCLM (k + 1) (stdBasis E i)).hasFDerivAt.comp x (hD x).hasFDerivAt
    rw [h1.fderiv]
    simp
  set D := fderiv ℝ (fderiv ℝ φ) x with hDdef
  set e := stdBasis E
  -- the double sum
  let f : Fin (finrank ℝ E) → Fin (finrank ℝ E) → (E [⋀^Fin k]→L[ℝ] ℝ) :=
    fun j i => ((D (e j) (e i)).curryLeft (e i)).curryLeft (e j)
  have hf : ∀ j i, f j i = - f i j := by
    intro j i
    simp only [f]
    rw [hsymm.eq (e j) (e i)]
    exact curryLeft_curryLeft_swap _ _ _
  have hsum : codiff (codiff φ) x = ∑ j, ∑ i, f j i := by
    rw [codiff_apply]
    simp only [hderiv]
    ext v
    simp [f, codiffCLM_apply, ContinuousAlternatingMap.sum_apply]
    rfl
  have h2 : ∑ j, ∑ i, f j i = - ∑ j, ∑ i, f j i := by
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => hf i j
  have h3 : ∑ j, ∑ i, f j i = 0 := by
    have h4 : (2 : ℝ) • ∑ j, ∑ i, f j i = 0 := by
      rw [two_smul]
      nth_rewrite 1 [h2]
      exact neg_add_cancel _
    exact (smul_eq_zero.mp h4).resolve_left two_ne_zero
  rw [Pi.zero_apply, hsum, h3]

/-- A *test form* on `Ω`: a smooth form with compact support contained in `Ω`. -/
structure IsTestForm (Ω : Set E) (φ : E → E [⋀^Fin k]→L[ℝ] ℝ) : Prop where
  contDiff : ContDiff ℝ (⊤ : ℕ∞) φ
  hasCompactSupport : HasCompactSupport φ
  tsupport_subset : tsupport φ ⊆ Ω

namespace IsTestForm

variable {Ω : Set E}

theorem zero : IsTestForm Ω (0 : E → E [⋀^Fin k]→L[ℝ] ℝ) where
  contDiff := contDiff_const
  hasCompactSupport := HasCompactSupport.zero
  tsupport_subset := by simp

/-- The codifferential of a test form is a test form. -/
protected theorem codiff {φ : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ} (hφ : IsTestForm Ω φ) :
    IsTestForm Ω (codiff φ) where
  contDiff := ContDiff.codiff (n := ⊤) (by simpa using hφ.contDiff)
  hasCompactSupport :=
    hφ.hasCompactSupport.of_isClosed_subset (isClosed_tsupport _) (tsupport_codiff_subset φ)
  tsupport_subset := (tsupport_codiff_subset φ).trans hφ.tsupport_subset

/-- A scalar test function times a constant covector is a test form. -/
theorem smul_const {g : E → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hg' : HasCompactSupport g)
    (hgΩ : tsupport g ⊆ Ω) (a : E [⋀^Fin k]→L[ℝ] ℝ) : IsTestForm Ω (fun x => g x • a) where
  contDiff := hg.smul contDiff_const
  hasCompactSupport := hg'.smul_right
  tsupport_subset := (tsupport_smul_subset_left g (fun _ => a)).trans hgΩ

variable [MeasurableSpace E] [BorelSpace E]

theorem memLp {φ : E → E [⋀^Fin k]→L[ℝ] ℝ} (hφ : IsTestForm Ω φ) :
    MemLp (fun x => Covector.ofAlt (φ x)) 2 (volume.restrict Ω) := by
  have hc : Continuous (fun x => Covector.ofAlt (φ x)) :=
    Covector.ofAlt.continuous.comp hφ.contDiff.continuous
  have hs : HasCompactSupport (fun x => Covector.ofAlt (φ x)) :=
    hφ.hasCompactSupport.comp_left (g := Covector.ofAlt) (map_zero _)
  exact hc.memLp_of_hasCompactSupport hs

/-- The class of a test form in `L²(Ω; Λᵏ)`. -/
noncomputable def toLp {φ : E → E [⋀^Fin k]→L[ℝ] ℝ} (hφ : IsTestForm Ω φ) :
    Lp (Covector E k) 2 (volume.restrict Ω) :=
  hφ.memLp.toLp _

theorem coeFn_toLp {φ : E → E [⋀^Fin k]→L[ℝ] ℝ} (hφ : IsTestForm Ω φ) :
    hφ.toLp =ᵐ[volume.restrict Ω] fun x => Covector.ofAlt (φ x) :=
  MemLp.coeFn_toLp _

end IsTestForm

end FEEC
