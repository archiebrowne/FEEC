/-
Eigenforms of the Hodge Laplacian on a box and Fourier coefficients.
-/
import FEEC.Fourier.TrigDensity
import FEEC.Tensor.Forms

/-!
# Eigenforms on a box and Fourier coefficients of `L²` forms

For a tuple `T : Fin k → Fin n` and frequencies `m : Fin n → ℕ`,
`eigForm e a b T m = trigProd e a b (pat T) m • dx_T`: sine in the directions of `T`,
cosine in the others (the natural boundary conditions).

For a covector `α`, `synth m α = (k!)⁻¹ ∑_T ⟪α, dx_T⟫ eigLp T m`, and for an `L²` form `w`,
`coef w m = (k!)⁻¹ ∑_T (⟪w, eigLp T m⟫ / normProd m) dx_T`, so that
`⟪w, synth m α⟫ = normProd m * ⟪coef w m, α⟫` (`inner_synth`).
Frequencies with `mᵢ = 0` kill the components involving `eᵢ` (`allow`).
`xi m = -∑ᵢ (π mᵢ / ℓᵢ) eᵢ` is the frequency vector: `d` acts as `xi m ∧ ·`.
-/

namespace FEEC

namespace Fourier

open MeasureTheory Tensor

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {n : ℕ}
  (e : OrthonormalBasis (Fin n) ℝ E) (a b : Fin n → ℝ) {k : ℕ}

/-- The eigenform with tuple `T` and frequencies `m`. -/
noncomputable def eigForm (T : Fin k → Fin n) (m : Fin n → ℕ) : E → E [⋀^Fin k]→L[ℝ] ℝ :=
  fun x => trigProd e a b (pat T) m x • dxT e k T

/-- `∏ᵢ ‖cos(π mᵢ ·)‖²`. -/
noncomputable def normProd (m : Fin n → ℕ) : ℝ := ∏ i, trigNormSq (a i) (b i) (m i)

/-- The frequency vector `-∑ᵢ (π mᵢ / ℓᵢ) eᵢ`. -/
noncomputable def xi (m : Fin n → ℕ) : E := -∑ i, freq (a i) (b i) (m i) • e i

/-- Exterior multiplication by a vector, on covectors. -/
noncomputable def cwedge (v : E) (α : Covector E k) : Covector E (k + 1) :=
  Covector.ofAlt (wedgeLeft v α.toAlt)

/-- Contraction with a vector, on covectors. -/
noncomputable def ccontr (v : E) (α : Covector E (k + 1)) : Covector E k :=
  Covector.ofAlt (α.toAlt.curryLeft v)

/-- The part of a covector allowed by the frequencies `m`. -/
noncomputable def allow (m : Fin n → ℕ) (α : Covector E k) : Covector E k :=
  ((k.factorial : ℝ))⁻¹ • ∑ T : Fin k → Fin n,
    (if ∀ p, m (T p) ≠ 0 then ⟪α, Covector.ofAlt (dxT e k T)⟫ else 0) •
      Covector.ofAlt (dxT e k T)

variable {e a b}

theorem contDiff_eigForm (T : Fin k → Fin n) (m : Fin n → ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (eigForm e a b T m) := by
  sorry

theorem memLp_eigForm (T : Fin k → Fin n) (m : Fin n → ℕ) :
    MemLp (fun x => Covector.ofAlt (eigForm e a b T m x)) 2 (volume.restrict (box e a b)) := by
  sorry

variable (e a b) in
/-- The class of an eigenform in `L²Λᵏ`. -/
noncomputable def eigLp (T : Fin k → Fin n) (m : Fin n → ℕ) : L2Form (box e a b) k :=
  (memLp_eigForm (e := e) (a := a) (b := b) T m).toLp _

variable (e a b) in
/-- The `L²` form with frequency `m` and covector coefficient `α`. -/
noncomputable def synth (m : Fin n → ℕ) (α : Covector E k) : L2Form (box e a b) k :=
  ((k.factorial : ℝ))⁻¹ • ∑ T : Fin k → Fin n, ⟪α, Covector.ofAlt (dxT e k T)⟫ • eigLp e a b T m

variable (e a b) in
/-- The Fourier coefficient of frequency `m`. -/
noncomputable def coef (w : L2Form (box e a b) k) (m : Fin n → ℕ) : Covector E k :=
  ((k.factorial : ℝ))⁻¹ • ∑ T : Fin k → Fin n,
    (⟪w, eigLp e a b T m⟫ / normProd a b m) • Covector.ofAlt (dxT e k T)

theorem coeFn_eigLp (T : Fin k → Fin n) (m : Fin n → ℕ) :
    eigLp e a b T m =ᵐ[volume.restrict (box e a b)]
      fun x => Covector.ofAlt (eigForm e a b T m x) := by
  sorry

theorem normProd_pos (hab : ∀ i, a i < b i) (m : Fin n → ℕ) : 0 < normProd a b m := by
  sorry

/-- Pairing of eigenforms. -/
theorem inner_eigLp (hab : ∀ i, a i < b i) (S T : Fin k → Fin n) (m m' : Fin n → ℕ) :
    ⟪eigLp e a b S m, eigLp e a b T m'⟫ =
      if m = m' ∧ (∀ p, m (S p) ≠ 0) then
        ⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k T)⟫ * normProd a b m
      else 0 := by
  sorry

theorem inner_synth (hab : ∀ i, a i < b i) (w : L2Form (box e a b) k) (m : Fin n → ℕ) (α : Covector E k) :
    ⟪w, synth e a b m α⟫ = normProd a b m * ⟪coef e a b w m, α⟫ := by
  sorry

theorem inner_synth_synth (hab : ∀ i, a i < b i) (m m' : Fin n → ℕ) (α β : Covector E k) :
    ⟪synth e a b m α, synth e a b m' β⟫ =
      if m = m' then normProd a b m * ⟪allow e m α, β⟫ else 0 := by
  sorry

theorem allow_coef (hab : ∀ i, a i < b i) (w : L2Form (box e a b) k) (m : Fin n → ℕ) :
    allow e m (coef e a b w m) = coef e a b w m := by
  sorry

theorem coef_synth (hab : ∀ i, a i < b i) (m m' : Fin n → ℕ) (α : Covector E k) :
    coef e a b (synth e a b m α) m' = if m = m' then allow e m α else 0 := by
  sorry

/-- `ξ ∧ ·` and `ξ ⌟ ·` are adjoint. -/
theorem inner_cwedge (v : E) (α : Covector E k) (β : Covector E (k + 1)) :
    ⟪cwedge v α, β⟫ = ⟪α, ccontr v β⟫ := by
  sorry

/-- `v ⌟ (v ∧ α) + v ∧ (v ⌟ α) = |v|² α`. -/
theorem ccontr_cwedge_add (v : E) (α : Covector E (k + 1)) :
    ccontr v (cwedge v α) + cwedge v (ccontr v α) = (‖v‖ ^ 2) • α := by
  sorry

theorem norm_cwedge_le (v : E) (α : Covector E k) : ‖cwedge v α‖ ≤ ‖v‖ * ‖α‖ := by
  sorry

theorem norm_ccontr_le (v : E) (α : Covector E (k + 1)) : ‖ccontr v α‖ ≤ ‖v‖ * ‖α‖ := by
  sorry

/-- Nonzero frequency vectors are bounded below. -/
theorem exists_norm_xi_ge (hab : ∀ i, a i < b i) :
    ∃ c > 0, ∀ m : Fin n → ℕ, m ≠ 0 → c ≤ ‖xi e a b m‖ := by
  sorry

/-- In positive degree, a coefficient can only be nonzero at a nonzero frequency. -/
theorem coef_zero_freq (hab : ∀ i, a i < b i) (w : L2Form (box e a b) (k + 1)) :
    coef e a b w 0 = 0 := by
  sorry

end Fourier

end FEEC
