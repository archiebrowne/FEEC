/-
One-dimensional shape and dual functions on a uniform grid.
-/
import FEEC.DeRham.LineG

/-!
# Shape and dual functions on a uniform grid of an interval

On `(a, b)` with `N` equal cells of size `h = (b - a) / N`, in the reference coordinate
`t = (x - a) / h` the nodes are `0, …, N` and cell `c ∈ {1, …, N}` is `[c - 1, c)`.

* Shape functions `Ref.shape a b N s j`: for `s = false` the hat function of node `j`; for
  `s = true` the indicator of cell `j`. (Zero for invalid indices.)
* Dual functions `Ref.dual a b N s j`: smooth, compactly supported in `(a, b)`. For
  `s = false`, a rescaled copy of a fixed `rho ∈ C_c^∞(0, 1)` with `∫ rho = 1`,
  `∫ t rho(t) = 0`, placed in a cell adjacent to node `j`. For `s = true`, the primitive of
  `(dual false (j - 1) - dual false j) / h`.

They are biorthogonal, and differentiation maps hats to differences of cell indicators and
cell duals to differences of node duals, with the same coefficients.
-/

namespace FEEC

open MeasureTheory

/-- The reference hat function. -/
noncomputable def hat (t : ℝ) : ℝ := max 0 (1 - |t|)

theorem exists_rho : ∃ ρ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ρ ∧ tsupport ρ ⊆ Set.Ioo 0 1 ∧
    ∫ t, ρ t = 1 ∧ ∫ t, t * ρ t = 0 := by
  sorry

/-- A fixed smooth function supported in `(0, 1)` with `∫ rho = 1` and `∫ t rho(t) = 0`. -/
noncomputable def rho : ℝ → ℝ := Classical.choose exists_rho

theorem rho_contDiff : ContDiff ℝ (⊤ : ℕ∞) rho := (Classical.choose_spec exists_rho).1

theorem rho_tsupport : tsupport rho ⊆ Set.Ioo 0 1 := (Classical.choose_spec exists_rho).2.1

theorem integral_rho : ∫ t, rho t = 1 := (Classical.choose_spec exists_rho).2.2.1

theorem integral_mul_rho : ∫ t, t * rho t = 0 := (Classical.choose_spec exists_rho).2.2.2

namespace Ref

variable (a b : ℝ) (N : ℕ)

/-- The mesh size. -/
noncomputable def meshH : ℝ := (b - a) / N

/-- The reference coordinate `(x - a) / h`. -/
noncomputable def coord (x : ℝ) : ℝ := (x - a) / meshH a b N

/-- Valid indices: nodes `0..N` (`s = false`), cells `1..N` (`s = true`). -/
def Valid (s : Bool) (j : ℕ) : Prop := if s then 1 ≤ j ∧ j ≤ N else j ≤ N

instance (s : Bool) (j : ℕ) : Decidable (Valid N s j) := by
  unfold Valid; infer_instance

/-- Shape functions: hats (`s = false`) and cell indicators (`s = true`). -/
noncomputable def shape (s : Bool) (j : ℕ) (x : ℝ) : ℝ :=
  if Valid N s j then
    (if s then Set.indicator (Set.Ico ((j : ℝ) - 1) j) (fun _ => (1 : ℝ)) (coord a b N x)
      else hat (coord a b N x - j))
  else 0

/-- The dual function of node `j`. -/
noncomputable def nodeDual (j : ℕ) (x : ℝ) : ℝ :=
  if j < N then rho (coord a b N x - j) / meshH a b N
  else if j = N then rho (j - coord a b N x) / meshH a b N
  else 0

/-- Dual functions. -/
noncomputable def dual (s : Bool) (j : ℕ) (x : ℝ) : ℝ :=
  if Valid N s j then
    (if s then cumul (fun y => (nodeDual a b N (j - 1) y - nodeDual a b N j y) / meshH a b N) x
      else nodeDual a b N j x)
  else 0

variable {a b N}

theorem measurable_shape (s : Bool) (j : ℕ) : Measurable (shape a b N s j) := by
  sorry

theorem abs_shape_le_one (s : Bool) (j : ℕ) (x : ℝ) : |shape a b N s j x| ≤ 1 := by
  sorry

theorem contDiff_nodeDual (hab : a < b) (hN : 0 < N) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (nodeDual a b N j) := by
  sorry

theorem tsupport_nodeDual_subset (hab : a < b) (hN : 0 < N) (j : ℕ) :
    tsupport (nodeDual a b N j) ⊆ Set.Ioo a b := by
  sorry

theorem integral_nodeDual (hab : a < b) (hN : 0 < N) {j : ℕ} (hj : j ≤ N) :
    ∫ x, nodeDual a b N j x = 1 := by
  sorry

theorem contDiff_dual (hab : a < b) (hN : 0 < N) (s : Bool) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (dual a b N s j) := by
  sorry

theorem tsupport_dual_subset (hab : a < b) (hN : 0 < N) (s : Bool) (j : ℕ) :
    tsupport (dual a b N s j) ⊆ Set.Ioo a b := by
  sorry

/-- The derivative of a cell dual is a difference of node duals. -/
theorem hasDerivAt_dual_true (hab : a < b) (hN : 0 < N) (j : ℕ) (x : ℝ) :
    HasDerivAt (dual a b N true j)
      (if Valid N true j then (dual a b N false (j - 1) x - dual a b N false j x) / meshH a b N
        else 0) x := by
  sorry

theorem lipschitz_shape_false (hab : a < b) (hN : 0 < N) (j : ℕ) :
    ∃ K, LipschitzWith K (shape a b N false j) := by
  sorry

/-- The derivative of a hat is a difference of cell indicators (away from the nodes). -/
theorem hasDerivAt_shape_false (hab : a < b) (hN : 0 < N) :
    ∃ Z : Finset ℝ, ∀ j : ℕ, ∀ x ∈ Set.Ioo a b, x ∉ Z →
      HasDerivAt (shape a b N false j)
        ((shape a b N true j x - shape a b N true (j + 1) x) / meshH a b N) x := by
  sorry

end Ref

end FEEC
