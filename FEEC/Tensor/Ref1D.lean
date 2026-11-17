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


theorem hasDerivAt_cumul_of {g : ℝ → ℝ} (hc : Continuous g) (hs : HasCompactSupport g) (s : ℝ) :
    HasDerivAt (cumul g) (g s) s := by
  have hi : Integrable g := hc.integrable_of_hasCompactSupport hs
  have key : cumul g = fun s => cumul g 0 + ∫ t in (0:ℝ)..s, g t := by
    funext s
    have := intervalIntegral.integral_Iic_sub_Iic (a := 0) (b := s) hi.integrableOn hi.integrableOn
    simp only [cumul]; linarith
  rw [key]
  exact ((hc.integral_hasStrictDerivAt 0 s).hasDerivAt).const_add _

theorem contDiff_cumul_of {g : ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hs : HasCompactSupport g) :
    ContDiff ℝ (⊤ : ℕ∞) (cumul g) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun s => (hasDerivAt_cumul_of hg.continuous hs s).differentiableAt, ?_⟩
  have : deriv (cumul g) = g := funext fun s => (hasDerivAt_cumul_of hg.continuous hs s).deriv
  rw [this]; exact hg

theorem exists_Icc_of_isCompact {K : Set ℝ} {a b : ℝ} (hab : a < b) (hK : IsCompact K) (h : K ⊆ Set.Ioo a b) :
    ∃ lo hi, a < lo ∧ hi < b ∧ K ⊆ Set.Icc lo hi := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨(a+b)/2, (a+b)/2, by linarith, by linarith, by simp⟩
  · obtain ⟨l, hl, hlmin⟩ := hK.exists_isMinOn hne continuousOn_id
    obtain ⟨r, hr, hrmax⟩ := hK.exists_isMaxOn hne continuousOn_id
    exact ⟨l, r, (h hl).1, (h hr).2, fun x hx => ⟨hlmin hx, hrmax hx⟩⟩

theorem cumul_eq_zero_of_lt {g : ℝ → ℝ} {lo hi : ℝ} (hsupp : tsupport g ⊆ Set.Icc lo hi)
    {x : ℝ} (hx : x < lo) : cumul g x = 0 := by
  unfold cumul
  refine setIntegral_eq_zero_of_forall_eq_zero fun t ht => ?_
  by_contra hne
  have h1 := hsupp (subset_tsupport _ hne)
  have h2 : t ≤ x := ht
  linarith [h1.1]

theorem cumul_eq_zero_of_gt {g : ℝ → ℝ} {lo hi : ℝ} (hsupp : tsupport g ⊆ Set.Icc lo hi)
    (hint : ∫ t, g t = 0) {x : ℝ} (hx : hi < x) : cumul g x = 0 := by
  unfold cumul
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero, hint]
  intro t ht
  by_contra hne
  have := (hsupp (subset_tsupport _ hne)).2
  have : x < t := by simpa using ht
  linarith

theorem tsupport_cumul_subset {g : ℝ → ℝ} {lo hi : ℝ} (hsupp : tsupport g ⊆ Set.Icc lo hi)
    (hint : ∫ t, g t = 0) : tsupport (cumul g) ⊆ Set.Icc lo hi := by
  refine closure_minimal ?_ isClosed_Icc
  intro x hx
  by_contra hxn
  simp only [Set.mem_Icc, not_and_or, not_le] at hxn
  apply hx
  rcases hxn with h | h
  · exact cumul_eq_zero_of_lt hsupp h
  · exact cumul_eq_zero_of_gt hsupp hint h


theorem exists_rho : ∃ ρ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ρ ∧ tsupport ρ ⊆ Set.Ioo 0 1 ∧
    ∫ t, ρ t = 1 ∧ ∫ t, t * ρ t = 0 := by
  obtain ⟨β, hβ⟩ := exists_isBump (a := (0:ℝ)) (b := 1) one_pos
  have hβc : HasCompactSupport β := hβ.hasCompactSupport
  have hβd : ContDiff ℝ (⊤ : ℕ∞) (deriv β) := (contDiff_infty_iff_deriv.1 hβ.contDiff).2
  have hβdiff : Differentiable ℝ β := (contDiff_infty_iff_deriv.1 hβ.contDiff).1
  have hβ' : HasCompactSupport (deriv β) := hβc.deriv
  have hβi : Integrable β := hβ.contDiff.continuous.integrable_of_hasCompactSupport hβc
  have hdi : Integrable (deriv β) := hβd.continuous.integrable_of_hasCompactSupport hβ'
  have hid : Continuous fun t : ℝ => t * β t := continuous_id.mul hβ.contDiff.continuous
  have hcs : HasCompactSupport fun t : ℝ => t * β t := hβc.mul_left
  have hti : Integrable fun t : ℝ => t * β t := hid.integrable_of_hasCompactSupport hcs
  have htd : Integrable fun t : ℝ => t * deriv β t :=
    (continuous_id.mul hβd.continuous).integrable_of_hasCompactSupport hβ'.mul_left
  have h0 : ∫ t, deriv β t = 0 := by
    have := integral_of_hasDerivAt_of_tendsto (f := β) (f' := deriv β) (m := 0) (n := 0)
      (fun x => (hβdiff x).hasDerivAt) hdi
      (hβc.is_zero_at_infty.mono_left atBot_le_cocompact)
      (hβc.is_zero_at_infty.mono_left atTop_le_cocompact)
    simpa using this
  have h1 : ∫ t, (β t + t * deriv β t) = 0 := by
    have := integral_of_hasDerivAt_of_tendsto (f := fun t : ℝ => t * β t)
      (f' := fun t => β t + t * deriv β t) (m := 0) (n := 0)
      (fun x => by
        exact ((hasDerivAt_id' x).mul (hβdiff x).hasDerivAt).congr_deriv (by ring)) (hβi.add htd)
      (hcs.is_zero_at_infty.mono_left atBot_le_cocompact)
      (hcs.is_zero_at_infty.mono_left atTop_le_cocompact)
    simpa using this
  rw [integral_add hβi htd, hβ.integral_eq_one] at h1
  have h2 : ∫ t, t * deriv β t = -1 := by linarith
  set c := ∫ t, t * β t with hc
  refine ⟨fun t => β t + c * deriv β t, hβ.contDiff.add (contDiff_const.mul hβd), ?_, ?_, ?_⟩
  · refine (tsupport_add _ _).trans (Set.union_subset hβ.tsupport_subset ?_)
    exact (tsupport_mul_subset_right (f := fun _ => c) (g := deriv β)).trans
      ((tsupport_deriv_subset).trans hβ.tsupport_subset)
  · rw [integral_add hβi (hdi.const_mul c), integral_const_mul, h0, hβ.integral_eq_one]; ring
  · have : ∀ t, t * (β t + c * deriv β t) = t * β t + c * (t * deriv β t) := fun t => by ring
    simp_rw [this]
    rw [integral_add hti (htd.const_mul c), integral_const_mul, h2]; ring

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

theorem meshH_pos (hab : a < b) (hN : 0 < N) : 0 < meshH a b N :=
  div_pos (sub_pos.2 hab) (by exact_mod_cast hN)

theorem meshH_mul_N (hN : 0 < N) : meshH a b N * N = b - a := by
  unfold meshH
  have : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

theorem continuous_coord : Continuous (coord a b N) := by
  unfold coord; fun_prop

theorem contDiff_coord : ContDiff ℝ (⊤ : ℕ∞) (coord a b N) := by
  unfold coord; fun_prop

theorem hasDerivAt_coord (x : ℝ) : HasDerivAt (coord a b N) (1 / meshH a b N) x := by
  unfold coord
  simpa using ((hasDerivAt_id x).sub_const a).div_const (meshH a b N)

theorem coord_mem_Ioo (hab : a < b) (hN : 0 < N) {x : ℝ} (hx : x ∈ Set.Ioo a b) :
    coord a b N x ∈ Set.Ioo (0 : ℝ) N := by
  have hh := meshH_pos hab hN
  have hm := meshH_mul_N (a := a) (b := b) hN
  unfold coord
  constructor
  · exact div_pos (by linarith [hx.1]) hh
  · rw [div_lt_iff₀ hh]; nlinarith [hx.2]

theorem eq_of_coord (hab : a < b) (hN : 0 < N) (x : ℝ) : x = a + meshH a b N * coord a b N x := by
  have hh := meshH_pos hab hN
  unfold coord; field_simp; ring

theorem continuous_hat : Continuous hat := by
  unfold hat; fun_prop

theorem hat_nonneg (t : ℝ) : 0 ≤ hat t := le_max_left _ _

theorem hat_le_one (t : ℝ) : hat t ≤ 1 :=
  max_le zero_le_one (by linarith [abs_nonneg t])

theorem abs_hat_sub_le (s t : ℝ) : |hat s - hat t| ≤ |s - t| := by
  unfold hat
  have h := abs_max_sub_max_le_max 0 (1 - |s|) 0 (1 - |t|)
  refine h.trans (max_le (by simp) ?_)
  have h2 := abs_abs_sub_abs_le_abs_sub s t
  calc |1 - |s| - (1 - |t|)| = |(|t| - |s|)| := by congr 1; ring
    _ = |(|s| - |t|)| := abs_sub_comm _ _
    _ ≤ _ := h2

theorem hat_of_neg {s : ℝ} (h1 : -1 < s) (h2 : s ≤ 0) : hat s = 1 + s := by
  unfold hat
  rw [abs_of_nonpos h2, max_eq_right (by linarith)]
  ring

theorem hat_of_pos {s : ℝ} (h1 : 0 ≤ s) (h2 : s < 1) : hat s = 1 - s := by
  unfold hat
  rw [abs_of_nonneg h1, max_eq_right (by linarith)]

theorem hat_of_one_le {s : ℝ} (h : 1 ≤ |s|) : hat s = 0 := by
  unfold hat
  exact max_eq_left (by linarith)

theorem valid_false_iff {j : ℕ} : Valid N false j ↔ j ≤ N := by simp [Valid]

theorem valid_true_iff {j : ℕ} : Valid N true j ↔ 1 ≤ j ∧ j ≤ N := by simp [Valid]

theorem shape_false_eq (j : ℕ) (x : ℝ) :
    shape a b N false j x = if j ≤ N then hat (coord a b N x - j) else 0 := by
  unfold shape
  simp [valid_false_iff]

theorem shape_true_eq (j : ℕ) (x : ℝ) : shape a b N true j x =
    if (1 ≤ j ∧ j ≤ N ∧ (j : ℝ) - 1 ≤ coord a b N x ∧ coord a b N x < j) then 1 else 0 := by
  unfold shape
  by_cases hv : 1 ≤ j ∧ j ≤ N
  · simp [valid_true_iff, hv, Set.indicator_apply]
  · have : ¬ Valid N true j := by rw [valid_true_iff]; exact hv
    have h2 : ¬ (1 ≤ j ∧ j ≤ N ∧ (j : ℝ) - 1 ≤ coord a b N x ∧ coord a b N x < j) :=
      fun h => hv ⟨h.1, h.2.1⟩
    rw [if_neg this, if_neg h2]

theorem measurable_shape (s : Bool) (j : ℕ) : Measurable (shape a b N s j) := by
  have hc : Measurable (coord a b N) := continuous_coord.measurable
  unfold shape
  split_ifs with hv hs
  · exact (measurable_const.indicator measurableSet_Ico).comp hc
  · exact continuous_hat.measurable.comp (hc.sub measurable_const)
  · exact measurable_const

theorem abs_shape_le_one (s : Bool) (j : ℕ) (x : ℝ) : |shape a b N s j x| ≤ 1 := by
  unfold shape
  split_ifs with hv hs
  · rw [Set.indicator_apply]; split_ifs <;> simp
  · rw [abs_of_nonneg (hat_nonneg _)]; exact hat_le_one _
  · simp

theorem exists_rho_Icc : ∃ lo hi : ℝ, 0 < lo ∧ hi < 1 ∧ tsupport rho ⊆ Set.Icc lo hi := by
  have hK : IsCompact (tsupport rho) :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _)
      (rho_tsupport.trans Set.Ioo_subset_Icc_self)
  exact exists_Icc_of_isCompact one_pos hK rho_tsupport

theorem nodeDual_support (hab : a < b) (hN : 0 < N) (j : ℕ) :
    ∃ l r : ℝ, a < l ∧ r < b ∧ ∀ x, nodeDual a b N j x ≠ 0 → x ∈ Set.Icc l r := by
  obtain ⟨lo, hi, hlo, hhi, hsub⟩ := exists_rho_Icc
  have hh := meshH_pos hab hN
  have hm := meshH_mul_N (a := a) (b := b) hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  by_cases h1 : j < N
  · have h1' : (j : ℝ) + 1 ≤ N := by exact_mod_cast h1
    refine ⟨a + meshH a b N * (j + lo), a + meshH a b N * (j + hi), ?_, ?_, ?_⟩
    · have := mul_pos hh (show 0 < (j : ℝ) + lo by linarith); linarith
    · have := mul_lt_mul_of_pos_left (show (j : ℝ) + hi < N by linarith) hh; linarith
    · intro x hx
      have hx' : rho (coord a b N x - j) ≠ 0 := by
        intro h0; apply hx; simp [nodeDual, h1, h0]
      have hmem := hsub (subset_tsupport _ hx')
      have hxe := eq_of_coord hab hN x
      constructor
      · have := mul_le_mul_of_nonneg_left (show (j : ℝ) + lo ≤ coord a b N x by linarith [hmem.1])
          hh.le
        linarith
      · have := mul_le_mul_of_nonneg_left (show coord a b N x ≤ (j : ℝ) + hi by linarith [hmem.2])
          hh.le
        linarith
  · by_cases h2 : j = N
    · subst j
      refine ⟨a + meshH a b N * (N - hi), a + meshH a b N * (N - lo), ?_, ?_, ?_⟩
      · have := mul_pos hh (show 0 < (N : ℝ) - hi by linarith); linarith
      · have := mul_lt_mul_of_pos_left (show (N : ℝ) - lo < N by linarith) hh; linarith
      · intro x hx
        have hx' : rho (N - coord a b N x) ≠ 0 := by
          intro h0; apply hx; simp [nodeDual, h0]
        have hmem := hsub (subset_tsupport _ hx')
        have hxe := eq_of_coord hab hN x
        constructor
        · have := mul_le_mul_of_nonneg_left (show (N : ℝ) - hi ≤ coord a b N x by linarith [hmem.2])
            hh.le
          linarith
        · have := mul_le_mul_of_nonneg_left (show coord a b N x ≤ (N : ℝ) - lo by linarith [hmem.1])
            hh.le
          linarith
    · refine ⟨(a + b) / 2, (a + b) / 2, by linarith, by linarith, ?_⟩
      intro x hx
      exfalso; apply hx; simp [nodeDual, h1, h2]

theorem contDiff_nodeDual (hab : a < b) (hN : 0 < N) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (nodeDual a b N j) := by
  by_cases h1 : j < N
  · have : nodeDual a b N j = fun x => rho (coord a b N x - j) / meshH a b N := by
      funext x; simp [nodeDual, h1]
    rw [this]
    exact (rho_contDiff.comp (contDiff_coord.sub contDiff_const)).div_const _
  · by_cases h2 : j = N
    · subst j
      have : nodeDual a b N N = fun x => rho (N - coord a b N x) / meshH a b N := by
        funext x; simp [nodeDual]
      rw [this]
      exact (rho_contDiff.comp (contDiff_const.sub contDiff_coord)).div_const _
    · have : nodeDual a b N j = fun _ => 0 := by
        funext x; simp [nodeDual, h1, h2]
      rw [this]; exact contDiff_const

theorem tsupport_nodeDual_Icc (hab : a < b) (hN : 0 < N) (j : ℕ) :
    ∃ l r : ℝ, a < l ∧ r < b ∧ tsupport (nodeDual a b N j) ⊆ Set.Icc l r := by
  obtain ⟨l, r, hl, hr, h⟩ := nodeDual_support hab hN j
  exact ⟨l, r, hl, hr, closure_minimal h isClosed_Icc⟩

theorem tsupport_nodeDual_subset (hab : a < b) (hN : 0 < N) (j : ℕ) :
    tsupport (nodeDual a b N j) ⊆ Set.Ioo a b := by
  obtain ⟨l, r, hl, hr, h⟩ := tsupport_nodeDual_Icc hab hN j
  exact h.trans fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩

theorem hasCompactSupport_nodeDual (hab : a < b) (hN : 0 < N) (j : ℕ) :
    HasCompactSupport (nodeDual a b N j) := by
  obtain ⟨l, r, hl, hr, h⟩ := tsupport_nodeDual_Icc hab hN j
  exact IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) h

theorem integral_rho_comp_left (hh : 0 < meshH a b N) (c : ℝ) :
    ∫ x, rho ((x - a) / meshH a b N - c) / meshH a b N = 1 := by
  rw [integral_div]
  have : ∫ x, rho ((x - a) / meshH a b N - c) = meshH a b N * ∫ t, rho t := by
    calc ∫ x, rho ((x - a) / meshH a b N - c)
        = ∫ x, (fun y => rho (y / meshH a b N - c)) (x - a) := rfl
      _ = ∫ y, rho (y / meshH a b N - c) :=
          integral_sub_right_eq_self (fun y => rho (y / meshH a b N - c)) a
      _ = ∫ y, (fun u => rho (u - c)) (y / meshH a b N) := rfl
      _ = |meshH a b N| • ∫ u, rho (u - c) := Measure.integral_comp_div (fun u => rho (u - c)) _
      _ = meshH a b N * ∫ t, rho t := by
          rw [integral_sub_right_eq_self rho c, abs_of_pos hh]; rfl
  rw [this, integral_rho]; field_simp

theorem integral_rho_comp_right (hh : 0 < meshH a b N) (c : ℝ) :
    ∫ x, rho (c - (x - a) / meshH a b N) / meshH a b N = 1 := by
  rw [integral_div]
  have : ∫ x, rho (c - (x - a) / meshH a b N) = meshH a b N * ∫ t, rho t := by
    calc ∫ x, rho (c - (x - a) / meshH a b N)
        = ∫ x, (fun y => rho (c - y / meshH a b N)) (x - a) := rfl
      _ = ∫ y, rho (c - y / meshH a b N) :=
          integral_sub_right_eq_self (fun y => rho (c - y / meshH a b N)) a
      _ = ∫ y, (fun u => rho (c - u)) (y / meshH a b N) := rfl
      _ = |meshH a b N| • ∫ u, rho (c - u) := Measure.integral_comp_div (fun u => rho (c - u)) _
      _ = meshH a b N * ∫ t, rho t := by
          rw [integral_sub_left_eq_self rho volume c, abs_of_pos hh]; rfl
  rw [this, integral_rho]; field_simp

theorem integral_nodeDual (hab : a < b) (hN : 0 < N) {j : ℕ} (hj : j ≤ N) :
    ∫ x, nodeDual a b N j x = 1 := by
  have hh := meshH_pos hab hN
  by_cases h1 : j < N
  · have : nodeDual a b N j = fun x => rho (coord a b N x - j) / meshH a b N := by
      funext x; simp [nodeDual, h1]
    rw [this]; exact integral_rho_comp_left hh j
  · have h2 : j = N := le_antisymm hj (not_lt.1 h1)
    subst j
    have : nodeDual a b N N = fun x => rho (N - coord a b N x) / meshH a b N := by
      funext x; simp [nodeDual]
    rw [this]; exact integral_rho_comp_right hh N

theorem dual_false (j : ℕ) : dual a b N false j = nodeDual a b N j := by
  funext x
  unfold dual
  by_cases hj : j ≤ N
  · simp [valid_false_iff, hj]
  · have : ¬ Valid N false j := by rw [valid_false_iff]; exact hj
    have h1 : ¬ j < N := by omega
    have h2 : ¬ j = N := by omega
    simp [this, nodeDual, h1, h2]

theorem dual_true_of_valid {j : ℕ} (hv : 1 ≤ j ∧ j ≤ N) :
    dual a b N true j =
      cumul (fun y => (nodeDual a b N (j - 1) y - nodeDual a b N j y) / meshH a b N) := by
  funext x
  simp [dual, valid_true_iff, hv]

theorem dual_true_of_not_valid {j : ℕ} (hv : ¬ (1 ≤ j ∧ j ≤ N)) :
    dual a b N true j = fun _ => 0 := by
  funext x
  have : ¬ Valid N true j := by rw [valid_true_iff]; exact hv
  simp [dual, this]

theorem diff_nodeDual_data (hab : a < b) (hN : 0 < N) (j₁ j₂ : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => (nodeDual a b N j₁ y - nodeDual a b N j₂ y) / meshH a b N) ∧
    HasCompactSupport (fun y => (nodeDual a b N j₁ y - nodeDual a b N j₂ y) / meshH a b N) ∧
    ∃ l r : ℝ, a < l ∧ r < b ∧
      tsupport (fun y => (nodeDual a b N j₁ y - nodeDual a b N j₂ y) / meshH a b N) ⊆
        Set.Icc l r := by
  obtain ⟨l₁, r₁, hl₁, hr₁, h₁⟩ := nodeDual_support hab hN j₁
  obtain ⟨l₂, r₂, hl₂, hr₂, h₂⟩ := nodeDual_support hab hN j₂
  have hsub : tsupport (fun y => (nodeDual a b N j₁ y - nodeDual a b N j₂ y) / meshH a b N) ⊆
      Set.Icc (min l₁ l₂) (max r₁ r₂) := by
    refine closure_minimal ?_ isClosed_Icc
    intro x hx
    have hx' : nodeDual a b N j₁ x ≠ 0 ∨ nodeDual a b N j₂ x ≠ 0 := by
      by_contra hc
      push Not at hc
      apply hx
      simp [hc.1, hc.2]
    rcases hx' with h | h
    · have := h₁ x h
      exact ⟨(min_le_left _ _).trans this.1, this.2.trans (le_max_left _ _)⟩
    · have := h₂ x h
      exact ⟨(min_le_right _ _).trans this.1, this.2.trans (le_max_right _ _)⟩
  refine ⟨((contDiff_nodeDual hab hN j₁).sub (contDiff_nodeDual hab hN j₂)).div_const _,
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) hsub,
    min l₁ l₂, max r₁ r₂, lt_min hl₁ hl₂, max_lt hr₁ hr₂, hsub⟩

theorem contDiff_dual (hab : a < b) (hN : 0 < N) (s : Bool) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (dual a b N s j) := by
  cases s
  · rw [dual_false]; exact contDiff_nodeDual hab hN j
  · by_cases hv : 1 ≤ j ∧ j ≤ N
    · rw [dual_true_of_valid hv]
      obtain ⟨h1, h2, _⟩ := diff_nodeDual_data hab hN (j - 1) j
      exact contDiff_cumul_of h1 h2
    · rw [dual_true_of_not_valid hv]; exact contDiff_const

theorem tsupport_dual_subset (hab : a < b) (hN : 0 < N) (s : Bool) (j : ℕ) :
    tsupport (dual a b N s j) ⊆ Set.Ioo a b := by
  cases s
  · rw [dual_false]; exact tsupport_nodeDual_subset hab hN j
  · by_cases hv : 1 ≤ j ∧ j ≤ N
    · rw [dual_true_of_valid hv]
      obtain ⟨_, _, l, r, hl, hr, hsub⟩ := diff_nodeDual_data hab hN (j - 1) j
      have hint : ∫ y, (nodeDual a b N (j - 1) y - nodeDual a b N j y) / meshH a b N = 0 := by
        have hi : ∀ i, Integrable (nodeDual a b N i) := fun i =>
          (contDiff_nodeDual hab hN i).continuous.integrable_of_hasCompactSupport
            (hasCompactSupport_nodeDual hab hN i)
        rw [integral_div, integral_sub (hi _) (hi _),
          integral_nodeDual hab hN (by omega), integral_nodeDual hab hN hv.2]
        simp
      have := tsupport_cumul_subset hsub hint
      exact this.trans fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
    · rw [dual_true_of_not_valid hv]; simp

/-- The derivative of a cell dual is a difference of node duals. -/
theorem hasDerivAt_dual_true (hab : a < b) (hN : 0 < N) (j : ℕ) (x : ℝ) :
    HasDerivAt (dual a b N true j)
      (if Valid N true j then (dual a b N false (j - 1) x - dual a b N false j x) / meshH a b N
        else 0) x := by
  by_cases hv : 1 ≤ j ∧ j ≤ N
  · have hv' : Valid N true j := by rw [valid_true_iff]; exact hv
    rw [if_pos hv', dual_true_of_valid hv, dual_false, dual_false]
    obtain ⟨h1, h2, _⟩ := diff_nodeDual_data hab hN (j - 1) j
    exact hasDerivAt_cumul_of h1.continuous h2 x
  · have hv' : ¬ Valid N true j := by rw [valid_true_iff]; exact hv
    rw [if_neg hv', dual_true_of_not_valid hv]
    exact hasDerivAt_const x 0

theorem lipschitz_shape_false (hab : a < b) (hN : 0 < N) (j : ℕ) :
    ∃ K, LipschitzWith K (shape a b N false j) := by
  have hh := meshH_pos hab hN
  refine ⟨(1 / meshH a b N).toNNReal, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  rw [Real.coe_toNNReal _ (by positivity), Real.dist_eq, Real.dist_eq, shape_false_eq,
    shape_false_eq]
  have hc : |coord a b N x - coord a b N y| = (1 / meshH a b N) * |x - y| := by
    unfold coord
    rw [← sub_div, abs_div, abs_of_pos hh]
    have : x - a - (y - a) = x - y := by ring
    rw [this]; field_simp
  split_ifs
  · calc |hat (coord a b N x - j) - hat (coord a b N y - j)|
        ≤ |(coord a b N x - j) - (coord a b N y - j)| := abs_hat_sub_le _ _
      _ = (1 / meshH a b N) * |x - y| := by rw [← hc]; congr 1; ring
  · simp; positivity

/-- The derivative of a hat is a difference of cell indicators (away from the nodes). -/
theorem hasDerivAt_shape_false (hab : a < b) (hN : 0 < N) :
    ∃ Z : Finset ℝ, ∀ j : ℕ, ∀ x ∈ Set.Ioo a b, x ∉ Z →
      HasDerivAt (shape a b N false j)
        ((shape a b N true j x - shape a b N true (j + 1) x) / meshH a b N) x := by
  have hh := meshH_pos hab hN
  refine ⟨(Finset.range (N + 2)).image (fun i : ℕ => a + i * meshH a b N), ?_⟩
  intro j x hx hxZ
  have ht := coord_mem_Ioo hab hN hx
  set t := coord a b N x with htdef
  have hxe := eq_of_coord hab hN x
  have hnat : ∀ i : ℕ, t ≠ i := by
    intro i hi
    apply hxZ
    rw [Finset.mem_image]
    refine ⟨i, Finset.mem_range.2 ?_, ?_⟩
    · have : (i : ℝ) < N := hi ▸ ht.2
      have : i < N := by exact_mod_cast this
      omega
    · rw [hxe, ← htdef, hi]; ring
  have hnat1 : ∀ i : ℕ, t ≠ (i : ℝ) - 1 := by
    intro i hi
    have hi1 : (1 : ℝ) < i := by linarith [ht.1]
    have hi2 : 1 < i := by exact_mod_cast hi1
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    apply hnat k
    rw [hi]; push_cast; ring
  have hcd := hasDerivAt_coord (a := a) (b := b) (N := N) x
  by_cases hj : j ≤ N
  swap
  · have h0 : shape a b N false j = fun _ => 0 := by
      funext y; rw [shape_false_eq, if_neg hj]
    have e1 : shape a b N true j x = 0 := by
      rw [shape_true_eq, if_neg]; intro h; exact hj h.2.1
    have e2 : shape a b N true (j + 1) x = 0 := by
      rw [shape_true_eq, if_neg]; intro h; exact hj (by omega)
    rw [h0, e1, e2]; simpa using hasDerivAt_const x (0 : ℝ)
  have hfun : shape a b N false j = fun y => hat (coord a b N y - j) := by
    funext y; rw [shape_false_eq, if_pos hj]
  have hd : HasDerivAt (fun y => coord a b N y - j) (1 / meshH a b N) x := hcd.sub_const _
  rw [hfun]
  rcases lt_trichotomy t ((j : ℝ) - 1) with h1 | h1 | h1
  · -- far left
    have e1 : shape a b N true j x = 0 := by
      rw [shape_true_eq, if_neg]; intro h; linarith [h.2.2.1]
    have e2 : shape a b N true (j + 1) x = 0 := by
      rw [shape_true_eq, if_neg]; intro h; push_cast at h; linarith [h.2.2.1]
    rw [e1, e2]
    have hev : ∀ᶠ y in nhds x, coord a b N y < (j : ℝ) - 1 :=
      continuous_coord.continuousAt.eventually (Iio_mem_nhds h1)
    have : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 x := hasDerivAt_const x 0
    have := this.congr_of_eventuallyEq (f₁ := fun y => hat (coord a b N y - j)) (by
      filter_upwards [hev] with y hy
      exact hat_of_one_le (by rw [abs_of_neg (by linarith)]; linarith))
    simpa using this
  · exact absurd h1 (hnat1 j)
  rcases lt_trichotomy t (j : ℝ) with h2 | h2 | h2
  · -- left slope
    have hj1 : 1 ≤ j := by
      have : (0 : ℝ) < j := by linarith [ht.1]
      exact_mod_cast this
    have e1 : shape a b N true j x = 1 := by
      rw [shape_true_eq, if_pos ⟨hj1, hj, h1.le, h2⟩]
    have e2 : shape a b N true (j + 1) x = 0 := by
      rw [shape_true_eq, if_neg]; intro h; push_cast at h; linarith [h.2.2.1]
    rw [e1, e2]
    have hev : ∀ᶠ y in nhds x, coord a b N y < (j : ℝ) :=
      continuous_coord.continuousAt.eventually (Iio_mem_nhds h2)
    have hev2 : ∀ᶠ y in nhds x, (j : ℝ) - 1 < coord a b N y :=
      continuous_coord.continuousAt.eventually (Ioi_mem_nhds h1)
    have := (hd.const_add 1).congr_of_eventuallyEq (f₁ := fun y => hat (coord a b N y - j)) (by
      filter_upwards [hev, hev2] with y hy hy2
      exact hat_of_neg (by linarith) (by linarith))
    have e : (1 - 0) / meshH a b N = 1 / meshH a b N := by ring
    rw [e]; exact this
  · exact absurd h2 (hnat j)
  rcases lt_trichotomy t ((j : ℝ) + 1) with h3 | h3 | h3
  · -- right slope
    have hjN : j < N := by
      have : (j : ℝ) < N := by linarith [ht.2]
      exact_mod_cast this
    have e1 : shape a b N true j x = 0 := by
      rw [shape_true_eq, if_neg]; intro h; linarith [h.2.2.2]
    have e2 : shape a b N true (j + 1) x = 1 := by
      rw [shape_true_eq, if_pos]
      refine ⟨by omega, by omega, ?_, ?_⟩ <;> push_cast <;> linarith
    rw [e1, e2]
    have hev : ∀ᶠ y in nhds x, (j : ℝ) < coord a b N y :=
      continuous_coord.continuousAt.eventually (Ioi_mem_nhds h2)
    have hev2 : ∀ᶠ y in nhds x, coord a b N y < (j : ℝ) + 1 :=
      continuous_coord.continuousAt.eventually (Iio_mem_nhds h3)
    have := (hd.const_sub 1).congr_of_eventuallyEq (f₁ := fun y => hat (coord a b N y - j)) (by
      filter_upwards [hev, hev2] with y hy hy2
      exact hat_of_pos (by linarith) (by linarith))
    have e : (0 - 1) / meshH a b N = -(1 / meshH a b N) := by ring
    rw [e]; exact this
  · exact absurd (by rw [h3]; push_cast; ring) (hnat (j + 1))
  · -- far right
    have e1 : shape a b N true j x = 0 := by
      rw [shape_true_eq, if_neg]; intro h; linarith [h.2.2.2]
    have e2 : shape a b N true (j + 1) x = 0 := by
      rw [shape_true_eq, if_neg]; intro h; push_cast at h; linarith [h.2.2.2]
    rw [e1, e2]
    have hev : ∀ᶠ y in nhds x, (j : ℝ) + 1 < coord a b N y :=
      continuous_coord.continuousAt.eventually (Ioi_mem_nhds h3)
    have : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 x := hasDerivAt_const x 0
    have := this.congr_of_eventuallyEq (f₁ := fun y => hat (coord a b N y - j)) (by
      filter_upwards [hev] with y hy
      exact hat_of_one_le (by rw [abs_of_pos (by linarith)]; linarith))
    simpa using this

end Ref

end FEEC
