/-
Decomposition of test forms on a box.
-/
import FEEC.DeRham.BoxBounds

/-!
# Decomposition of test forms on a box

Let `Ω = box e a b = {x | ∀ i, aᵢ < ⟪eᵢ, x⟫ < bᵢ}` for an orthonormal basis `e`. Applying the
one-directional homotopy successively in the directions `e₀, …, e_{n-1}` shows that every
test form `φ` of positive degree on `Ω` can be written `φ = δψ + χ` with test forms `ψ`, `χ`
and `‖χ‖_{L²} ≤ C ‖δφ‖_{L²}` (`FEEC.exists_codiff_decomp`).
-/

namespace FEEC

open MeasureTheory

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ} {k : ℕ}

/-- The open box `{x | ∀ i, aᵢ < ⟪eᵢ, x⟫ < bᵢ}` with respect to an orthonormal basis `e`. -/
def box (e : OrthonormalBasis (Fin n) ℝ E) (a b : Fin n → ℝ) : Set E :=
  {x | ∀ i, ⟪e i, x⟫ ∈ Set.Ioo (a i) (b i)}

variable (e : OrthonormalBasis (Fin n) ℝ E) (a b : Fin n → ℝ)

theorem isOpen_box : IsOpen (box e a b) := by
  have : box e a b = ⋂ i, (fun x => ⟪e i, x⟫) ⁻¹' Set.Ioo (a i) (b i) := by
    ext x; simp [box]
  rw [this]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_Ioo.preimage (by fun_prop)

theorem isSlab_box (i : Fin n) : IsSlab (box e a b) (e i) (a i) (b i) where
  mem_Ioo x hx := hx i
  shift_mem x hx s hs := by
    intro j
    have h1 : ⟪e j, e i⟫ = if j = i then 1 else 0 := e.inner_eq_ite j i
    have h2 : ⟪e j, x + (s - ⟪e i, x⟫) • e i⟫ = ⟪e j, x⟫ + (s - ⟪e i, x⟫) * ⟪e j, e i⟫ := by
      rw [inner_add_right, inner_smul_right]
    rw [h2, h1]
    by_cases hji : j = i
    · subst hji; simpa using hs
    · simpa [hji] using hx j

/-- The composition `Q_{j-1} ∘ ⋯ ∘ Q_0` of the operators `homotopyQ (e i) (θ i)`. -/
noncomputable def iterQ (θ : Fin n → ℝ → ℝ) :
    ℕ → (E → E [⋀^Fin k]→L[ℝ] ℝ) → (E → E [⋀^Fin k]→L[ℝ] ℝ)
  | 0, φ => φ
  | j + 1, φ => if h : j < n then homotopyQ (e ⟨j, h⟩) (θ ⟨j, h⟩) (iterQ θ j φ)
      else iterQ θ j φ

variable {e a b} {θ : Fin n → ℝ → ℝ}

theorem iterQ_succ_of_lt {j : ℕ} (h : j < n) (φ : E → E [⋀^Fin k]→L[ℝ] ℝ) :
    iterQ e θ (j + 1) φ = homotopyQ (e ⟨j, h⟩) (θ ⟨j, h⟩) (iterQ e θ j φ) := by
  simp [iterQ, h]

theorem iterQ_succ_of_not_lt {j : ℕ} (h : ¬ j < n) (φ : E → E [⋀^Fin k]→L[ℝ] ℝ) :
    iterQ e θ (j + 1) φ = iterQ e θ j φ := by
  simp [iterQ, h]

theorem IsTestForm.iterQ (hθ : ∀ i, IsBump (θ i) (a i) (b i)) (j : ℕ)
    {φ : E → E [⋀^Fin k]→L[ℝ] ℝ} (hφ : IsTestForm (box e a b) φ) :
    IsTestForm (box e a b) (iterQ e θ j φ) := by
  induction j with
  | zero => exact hφ
  | succ j ih =>
    by_cases h : j < n
    · rw [iterQ_succ_of_lt h]
      exact IsTestForm.homotopyQ (isSlab_box e a b _) (hθ _) (by simp) ih
    · rw [iterQ_succ_of_not_lt h]; exact ih

theorem codiff_iterQ (hθ : ∀ i, IsBump (θ i) (a i) (b i)) (j : ℕ)
    {φ : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ} (hφ : IsTestForm (box e a b) φ) :
    codiff (iterQ e θ j φ) = iterQ e θ j (codiff φ) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    by_cases h : j < n
    · have hR := IsTestForm.iterQ hθ j hφ
      rw [iterQ_succ_of_lt h, iterQ_succ_of_lt h,
        codiff_homotopyQ (hθ _) (by simp) hR.contDiff hR.hasCompactSupport, ih]
    · rw [iterQ_succ_of_not_lt h, iterQ_succ_of_not_lt h]; exact ih

/-- After all `n` directions nothing is left of a form of positive degree. -/
theorem iterQ_eq_zero (hθ : ∀ i, IsBump (θ i) (a i) (b i))
    {φ : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ} (hφ : IsTestForm (box e a b) φ) :
    iterQ e θ n φ = 0 := by
  have key : ∀ j, j ≤ n → ∀ i : Fin n, (i : ℕ) < j → ∀ x, (iterQ e θ j φ x).curryLeft (e i) = 0 := by
    intro j
    induction j with
    | zero => intro _ i hi; omega
    | succ j ih =>
      intro hj i hi x
      have h : j < n := hj
      rw [iterQ_succ_of_lt h]
      have hR := IsTestForm.iterQ hθ j hφ
      by_cases hij : (i : ℕ) = j
      · have : i = ⟨j, h⟩ := Fin.ext hij
        subst this
        exact curryLeft_homotopyQ_self (by simp) _ x
      · have hlt : (i : ℕ) < j := by omega
        refine curryLeft_homotopyQ_of_orthogonal ?_ (by simp) hR.contDiff.continuous
          hR.hasCompactSupport (ih h.le i hlt) x
        have hne : (⟨j, h⟩ : Fin n) ≠ i := fun hh => hij (by rw [← hh])
        exact e.orthonormal.2 hne
  funext x
  exact eq_zero_of_curryLeft_basis e.toBasis _ fun i => by
    simpa using key n le_rfl i i.2 x

variable [MeasurableSpace E] [BorelSpace E]

theorem exists_norm_iterQ_le (hθ : ∀ i, IsBump (θ i) (a i) (b i)) (k j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : E → E [⋀^Fin k]→L[ℝ] ℝ) (hφ : IsTestForm (box e a b) φ)
      (hR : IsTestForm (box e a b) (iterQ e θ j φ)), ‖hR.toLp‖ ≤ C * ‖hφ.toLp‖ := by
  induction j with
  | zero =>
    refine ⟨1, zero_le_one, fun φ hφ hR => ?_⟩
    rw [one_mul, hR.toLp_congr hφ rfl]
  | succ j ih =>
    obtain ⟨Cj, hCj, hj⟩ := ih
    by_cases h : j < n
    · obtain ⟨C', hC', hQ⟩ := exists_norm_homotopyQ_le (isOpen_box e a b).measurableSet
        (isSlab_box e a b ⟨j, h⟩) (hθ ⟨j, h⟩) (by simp) k
      refine ⟨C' * Cj, mul_nonneg hC' hCj, fun φ hφ hR => ?_⟩
      have hRj := IsTestForm.iterQ hθ j hφ
      have e1 := iterQ_succ_of_lt (e := e) (θ := θ) h φ
      have hR' : IsTestForm (box e a b) (homotopyQ (e ⟨j, h⟩) (θ ⟨j, h⟩) (iterQ e θ j φ)) :=
        e1 ▸ hR
      rw [hR.toLp_congr hR' e1, mul_assoc]
      exact (hQ _ hRj hR').trans (mul_le_mul_of_nonneg_left (hj φ hφ hRj) hC')
    · refine ⟨Cj, hCj, fun φ hφ hR => ?_⟩
      have e1 := iterQ_succ_of_not_lt (e := e) (θ := θ) h φ
      have hRj := IsTestForm.iterQ hθ j hφ
      rw [hR.toLp_congr hRj e1]
      exact hj φ hφ hRj

/-- **Decomposition of test forms on a box.** Every test form `φ` of positive degree is
`δψ + χ` with `χ` controlled in `L²` by `δφ`. -/
theorem exists_codiff_decomp (e : OrthonormalBasis (Fin n) ℝ E) {a b : Fin n → ℝ}
    (hab : ∀ i, a i < b i) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ) (hφ : IsTestForm (box e a b) φ),
      ∃ (ψ : E → E [⋀^Fin (k + 2)]→L[ℝ] ℝ) (_ : IsTestForm (box e a b) ψ)
        (χ : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ) (hχ : IsTestForm (box e a b) χ),
        φ = codiff ψ + χ ∧ ‖hχ.toLp‖ ≤ C * ‖hφ.codiff.toLp‖ := by
  have hθ' : ∀ i, ∃ t, IsBump t (a i) (b i) := fun i => exists_isBump (hab i)
  choose θ hθ using hθ'
  have main : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (φ : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ) (hφ : IsTestForm (box e a b) φ),
      ∃ (ψ : E → E [⋀^Fin (k + 2)]→L[ℝ] ℝ) (_ : IsTestForm (box e a b) ψ)
        (χ : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ) (hχ : IsTestForm (box e a b) χ),
        φ = codiff ψ + χ + iterQ e θ j φ ∧ ‖hχ.toLp‖ ≤ C * ‖hφ.codiff.toLp‖ := by
    intro j
    induction j with
    | zero =>
      refine ⟨0, le_rfl, fun φ hφ => ?_⟩
      refine ⟨0, IsTestForm.zero, 0, IsTestForm.zero, ?_, ?_⟩
      · have : codiff (0 : E → E [⋀^Fin (k + 2)]→L[ℝ] ℝ) = 0 := by
          funext x; simp [codiff_eq]
        simp [this, iterQ]
      · rw [IsTestForm.zero.toLp_eq_zero rfl]; simp
    | succ j ih =>
      obtain ⟨C, hC, hj⟩ := ih
      by_cases h : j < n
      · obtain ⟨CS, hCS, hS⟩ := exists_norm_homotopyS_le (isOpen_box e a b).measurableSet
          (isSlab_box e a b ⟨j, h⟩) (hθ ⟨j, h⟩) (by simp) k
        obtain ⟨CR, hCR, hR⟩ := exists_norm_iterQ_le (e := e) (a := a) (b := b) (θ := θ) hθ k j
        refine ⟨C + CS * CR, add_nonneg hC (mul_nonneg hCS hCR), fun φ hφ => ?_⟩
        obtain ⟨ψ, hψ, χ, hχ, heq, hb⟩ := hj φ hφ
        have hRj := IsTestForm.iterQ hθ j hφ
        have hSR := IsTestForm.homotopyS (isSlab_box e a b ⟨j, h⟩) (hθ ⟨j, h⟩)
          (by simp) hRj
        have hcφ := hφ.codiff
        have hRc := IsTestForm.iterQ hθ j hcφ
        have hSRc := IsTestForm.homotopyS (isSlab_box e a b ⟨j, h⟩) (hθ ⟨j, h⟩)
          (by simp) hRc
        refine ⟨ψ + homotopyS (e ⟨j, h⟩) (θ ⟨j, h⟩) (iterQ e θ j φ), hψ.add hSR,
          χ + homotopyS (e ⟨j, h⟩) (θ ⟨j, h⟩) (iterQ e θ j (codiff φ)), hχ.add hSRc, ?_, ?_⟩
        · have h1 := codiff_homotopyS (e := e ⟨j, h⟩) (θ := θ ⟨j, h⟩) (hθ ⟨j, h⟩) (by simp)
            hRj.contDiff hRj.hasCompactSupport
          rw [codiff_iterQ hθ j hφ, ← iterQ_succ_of_lt h] at h1
          rw [codiff_add (hψ.contDiff.differentiable (by simp))
            (hSR.contDiff.differentiable (by simp))]
          have h1' : iterQ e θ j φ = codiff (homotopyS (e ⟨j, h⟩) (θ ⟨j, h⟩) (iterQ e θ j φ)) +
              homotopyS (e ⟨j, h⟩) (θ ⟨j, h⟩) (iterQ e θ j (codiff φ)) +
              iterQ e θ (j + 1) φ := by
            rw [h1]; abel
          calc φ = codiff ψ + χ + iterQ e θ j φ := heq
            _ = _ := by
              conv_lhs => rw [h1']
              abel
        · rw [hχ.toLp_add hSRc]
          have h1 := hS _ hRc hSRc
          have h2 := hR _ hcφ hRc
          calc _ ≤ ‖hχ.toLp‖ + ‖hSRc.toLp‖ := norm_add_le _ _
            _ ≤ C * ‖hcφ.toLp‖ + CS * (CR * ‖hcφ.toLp‖) :=
              add_le_add hb (h1.trans (mul_le_mul_of_nonneg_left h2 hCS))
            _ = _ := by ring
      · refine ⟨C, hC, fun φ hφ => ?_⟩
        obtain ⟨ψ, hψ, χ, hχ, heq, hb⟩ := hj φ hφ
        exact ⟨ψ, hψ, χ, hχ, by rw [iterQ_succ_of_not_lt h]; exact heq, hb⟩
  obtain ⟨C, hC, hmain⟩ := main n
  refine ⟨C, hC, fun φ hφ => ?_⟩
  obtain ⟨ψ, hψ, χ, hχ, heq, hb⟩ := hmain φ hφ
  exact ⟨ψ, hψ, χ, hχ, by rw [heq, iterQ_eq_zero hθ hφ, add_zero], hb⟩

end FEEC
