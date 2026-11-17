/-
Adjointness of exterior and interior multiplication; basis covectors.
-/
import FEEC.DeRham.Wedge

/-!
# Basis covectors

* `FEEC.inner_wedgeLeft`: exterior multiplication `e♭ ∧ ·` and contraction `e ⌟ ·` are adjoint
  for the Euclidean inner product of covectors.
* `FEEC.dxT e k T`: for an orthonormal basis `e` and any tuple `T : Fin k → Fin n`, the
  covector `e_{T 0}♭ ∧ e_{T 1}♭ ∧ ⋯ ∧ e_{T (k-1)}♭`.
* `FEEC.sum_inner_dxT_smul`: the resolution of the identity
  `α = (k!)⁻¹ ∑_T ⟪α, dxT T⟫ dxT T` over all tuples.
-/

namespace FEEC

open Module

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {k : ℕ}

theorem sum_reindex_aux' (a : E →L[ℝ] E [⋀^Fin k]→L[ℝ] ℝ) (β : E [⋀^Fin (k + 1)]→L[ℝ] ℝ)
    (j : Fin (k + 1)) :
    ∑ I : Fin (k + 1) → Fin (finrank ℝ E),
      (-1 : ℝ) ^ (j : ℕ) * (a (stdBasis E (I j)) (fun l => stdBasis E (j.removeNth I l)) *
        β (fun l => stdBasis E (I l))) =
    ∑ i : Fin (finrank ℝ E), ∑ J : Fin k → Fin (finrank ℝ E),
      a (stdBasis E i) (fun l => stdBasis E (J l)) *
        β (Matrix.vecCons (stdBasis E i) (fun l => stdBasis E (J l))) := by
  rw [← (Fin.insertNthEquiv (fun _ => Fin (finrank ℝ E)) j).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun J _ => ?_
  have h1 : (fun l => stdBasis E ((Fin.insertNthEquiv (fun _ => Fin (finrank ℝ E)) j (i, J)) l)) =
      j.insertNth (stdBasis E i) (fun l => stdBasis E (J l)) := by
    ext l
    refine Fin.succAboveCases j ?_ (fun m => ?_) l <;> simp
  have h2 := β.neg_one_pow_smul_map_insertNth j (stdBasis E i) (fun l => stdBasis E (J l))
  simp only [Fin.insertNthEquiv_apply, Fin.insertNth_apply_same, Fin.removeNth_insertNth] at *
  rw [h1, ← h2]
  have h3 : j.removeNth (Fin.insertNthEquiv (fun _ => Fin (finrank ℝ E)) j (i, J)) = J := by
    exact Fin.removeNth_insertNth (α := fun _ => Fin (finrank ℝ E)) j i J
  rw [h3]
  simp only [zsmul_eq_mul]
  push_cast
  ring

/-- Exterior multiplication by `e♭` is adjoint to contraction with `e`. -/
theorem inner_wedgeLeft (e : E) (α : E [⋀^Fin k]→L[ℝ] ℝ) (β : E [⋀^Fin (k + 1)]→L[ℝ] ℝ) :
    ⟪Covector.ofAlt (wedgeLeft e α), Covector.ofAlt β⟫ =
      ⟪Covector.ofAlt α, Covector.ofAlt (β.curryLeft e)⟫ := by
  set a : E →L[ℝ] E [⋀^Fin k]→L[ℝ] ℝ := (innerSL ℝ e).smulRight α with ha
  have key : ∀ I : Fin (k + 1) → Fin (finrank ℝ E),
      (Covector.ofAlt (wedgeLeft e α)).coeff I * (Covector.ofAlt β).coeff I =
      ∑ j : Fin (k + 1), (-1 : ℝ) ^ (j : ℕ) * (a (stdBasis E (I j))
        (fun l => stdBasis E (j.removeNth I l)) * β (fun l => stdBasis E (I l))) := by
    intro I
    rw [Covector.coeff_ofAlt, Covector.coeff_ofAlt, wedgeLeft_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [ha]
    have e : (j.removeNth fun j => stdBasis E (I j)) =
        fun l => stdBasis E (I (j.succAbove l)) := rfl
    have e2 : (fun l => stdBasis E (I (j.succAbove l))) =
        fun l => stdBasis E (j.removeNth I l) := rfl
    rw [e, e2]
    ring
  rw [Covector.inner_def, Covector.inner_def]
  simp only [key]
  rw [Finset.sum_comm]
  have h2 : ∀ j : Fin (k + 1), _ := fun j => sum_reindex_aux' a β j
  simp only [h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [Covector.coeff_ofAlt, ContinuousAlternatingMap.curryLeft_apply_apply]
  rw [Nat.factorial_succ]
  push_cast
  have hk : (k.factorial : ℝ) ≠ 0 := by positivity
  have h4 : ∀ w : Fin k → E, ∑ i, ⟪e, stdBasis E i⟫ * β (Matrix.vecCons (stdBasis E i) w) =
      β (Matrix.vecCons e w) := by
    intro w
    have := congrArg (fun x => (β.curryLeft x) w) ((stdBasis E).sum_repr' e)
    simp only [map_sum, map_smul, ContinuousAlternatingMap.curryLeft_apply_apply] at this
    simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_comm]; simp
  have h5 : ∑ i, ∑ J : Fin k → Fin (finrank ℝ E),
      ((a (stdBasis E i)) fun l => stdBasis E (J l)) *
        β (Matrix.vecCons (stdBasis E i) fun l => stdBasis E (J l)) =
      ∑ J : Fin k → Fin (finrank ℝ E), (α fun j => stdBasis E (J j)) *
        β (Matrix.vecCons e fun j => stdBasis E (J j)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [← h4]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [ha]
    ring
  rw [h5]
  field_simp

theorem wedgeLeft_wedgeLeft_swap (u v : E) (α : E [⋀^Fin k]→L[ℝ] ℝ) :
    wedgeLeft u (wedgeLeft v α) = - wedgeLeft v (wedgeLeft u α) := by
  rw [← sub_eq_zero, sub_neg_eq_add]
  have h : ∀ γ : E [⋀^Fin (k + 2)]→L[ℝ] ℝ,
      ⟪Covector.ofAlt (wedgeLeft u (wedgeLeft v α) + wedgeLeft v (wedgeLeft u α)),
        Covector.ofAlt γ⟫ = 0 := by
    intro γ
    rw [map_add, inner_add_left, inner_wedgeLeft, inner_wedgeLeft, inner_wedgeLeft,
      inner_wedgeLeft, curryLeft_curryLeft_swap γ u v, map_neg, inner_neg_right]
    ring
  have := inner_self_eq_zero.mp (h _)
  exact (map_eq_zero_iff _ (Covector.ofAlt.injective)).mp this

theorem wedgeLeft_wedgeLeft_self (u : E) (α : E [⋀^Fin k]→L[ℝ] ℝ) :
    wedgeLeft u (wedgeLeft u α) = 0 := by
  have h := wedgeLeft_wedgeLeft_swap u u α
  have h2 : (2 : ℝ) • wedgeLeft u (wedgeLeft u α) = 0 := by
    rw [two_smul]; nth_rewrite 2 [h]; simp
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

theorem sum_inner_basis {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (β : E [⋀^Fin (k + 1)]→L[ℝ] ℝ) (x : E) (w : Fin k → E) :
    ∑ i, ⟪b i, x⟫ * β (Matrix.vecCons (b i) w) = β (Matrix.vecCons x w) := by
  have := congrArg (fun x => (β.curryLeft x) w) (b.sum_repr' x)
  simp only [map_sum, map_smul, ContinuousAlternatingMap.curryLeft_apply_apply] at this
  simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply] at this
  rw [← this]
  simp

theorem vecCons_removeNth (α : E [⋀^Fin (k + 1)]→L[ℝ] ℝ) (v : Fin (k + 1) → E)
    (j : Fin (k + 1)) :
    α (Matrix.vecCons (v j) (j.removeNth v)) = (-1 : ℝ) ^ (j : ℕ) * α v := by
  have h := α.neg_one_pow_smul_map_insertNth j (v j) (j.removeNth v)
  rw [Fin.insertNth_self_removeNth] at h
  rw [← h]
  simp only [zsmul_eq_mul]
  have : ((-1 : ℝ) ^ (j : ℕ)) * ((-1 : ℝ) ^ (j : ℕ)) = 1 := by
    rw [← mul_pow]; simp
  push_cast
  try rfl

/-- `∑ᵢ eᵢ♭ ∧ (eᵢ ⌟ α) = (deg α) α` for an orthonormal basis. -/
theorem sum_wedgeLeft_curryLeft {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (α : E [⋀^Fin (k + 1)]→L[ℝ] ℝ) :
    ∑ i, wedgeLeft (b i) (α.curryLeft (b i)) = ((k : ℝ) + 1) • α := by
  ext v
  simp only [ContinuousAlternatingMap.sum_apply, wedgeLeft_apply,
    ContinuousAlternatingMap.curryLeft_apply_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul]
  rw [Finset.sum_comm]
  have h1 : ∀ j : Fin (k + 1), ∑ i, (-1 : ℝ) ^ (j : ℕ) *
      (⟪b i, v j⟫ * α (Matrix.vecCons (b i) (j.removeNth v))) = α v := by
    intro j
    rw [← Finset.mul_sum, sum_inner_basis b α (v j) (j.removeNth v), vecCons_removeNth]
    have : ((-1 : ℝ) ^ (j : ℕ)) * ((-1 : ℝ) ^ (j : ℕ)) = 1 := by
      rw [← mul_pow]; simp
    rw [← mul_assoc, this, one_mul]
  simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast; ring

variable {n : ℕ} (e : OrthonormalBasis (Fin n) ℝ E)

/-- The basis covector `e_{T 0}♭ ∧ ⋯ ∧ e_{T (k-1)}♭` of a tuple `T`. -/
noncomputable def dxT : (k : ℕ) → (Fin k → Fin n) → E [⋀^Fin k]→L[ℝ] ℝ
  | 0, _ => ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) (1 : ℝ)
  | k + 1, T => wedgeLeft (e (T 0)) (dxT k (Fin.tail T))

theorem dxT_succ (T : Fin (k + 1) → Fin n) :
    dxT e (k + 1) T = wedgeLeft (e (T 0)) (dxT e k (Fin.tail T)) := rfl

theorem wedgeLeft_dxT (i : Fin n) (T : Fin k → Fin n) :
    wedgeLeft (e i) (dxT e k T) = dxT e (k + 1) (Fin.cons i T) := by
  rw [dxT_succ]; simp

theorem wedgeLeft_dxT_of_mem {i : Fin n} {T : Fin k → Fin n} (h : i ∈ Set.range T) :
    wedgeLeft (e i) (dxT e k T) = 0 := by
  induction k generalizing i with
  | zero => obtain ⟨p, _⟩ := h; exact p.elim0
  | succ k ih =>
    obtain ⟨p, rfl⟩ := h
    rw [dxT_succ]
    by_cases hp : p = 0
    · subst hp; exact wedgeLeft_wedgeLeft_self _ _
    · obtain ⟨q, rfl⟩ := Fin.exists_succ_eq.mpr hp
      have := ih (i := T q.succ) (T := Fin.tail T) ⟨q, rfl⟩
      rw [wedgeLeft_wedgeLeft_swap, this]; simp

theorem dxT_eq_zero_of_not_injective {T : Fin k → Fin n} (h : ¬ Function.Injective T) :
    dxT e k T = 0 := by
  induction k with
  | zero => exact absurd (fun a b _ => Subsingleton.elim a b) h
  | succ k ih =>
    rw [dxT_succ]
    by_cases h0 : T 0 ∈ Set.range (Fin.tail T)
    · exact wedgeLeft_dxT_of_mem e h0
    · have ht : ¬ Function.Injective (Fin.tail T) := by
        intro hi
        apply h
        intro a b hab
        induction a using Fin.cases with
        | zero =>
          induction b using Fin.cases with
          | zero => rfl
          | succ b => exact absurd ⟨b, hab.symm⟩ h0
        | succ a =>
          induction b using Fin.cases with
          | zero => exact absurd ⟨a, hab⟩ h0
          | succ b => rw [hi hab]
      rw [ih ht, map_zero]

theorem curryLeft_dxT_of_not_mem {i : Fin n} {T : Fin (k + 1) → Fin n}
    (h : i ∉ Set.range T) : (dxT e (k + 1) T).curryLeft (e i) = 0 := by
  induction k with
  | zero =>
    rw [dxT_succ, curryLeft_wedgeLeft_zero,
      e.orthonormal.inner_eq_zero (fun hh => h ⟨0, hh⟩), zero_smul]
  | succ k ih =>
    have h' : i ∉ Set.range (Fin.tail T) := fun ⟨q, hq⟩ => h ⟨q.succ, hq⟩
    rw [dxT_succ, curryLeft_wedgeLeft, ih h', e.orthonormal.inner_eq_zero (fun hh => h ⟨0, hh⟩)]
    simp

/-- The span of the basis covectors of tuples with values in `R`. -/
noncomputable def UR (R : Set (Fin n)) (k : ℕ) : Submodule ℝ (E [⋀^Fin k]→L[ℝ] ℝ) :=
  Submodule.span ℝ {a | ∃ T : Fin k → Fin n, Set.range T ⊆ R ∧ a = dxT e k T}

theorem dxT_mem_UR {R : Set (Fin n)} {T : Fin k → Fin n} (h : Set.range T ⊆ R) :
    dxT e k T ∈ UR e R k :=
  Submodule.subset_span ⟨T, h, rfl⟩

theorem wedgeLeft_mem_UR {R : Set (Fin n)} {j : Fin n} (hj : j ∈ R)
    {a : E [⋀^Fin k]→L[ℝ] ℝ} (ha : a ∈ UR e R k) : wedgeLeft (e j) a ∈ UR e R (k + 1) := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨T, hT, rfl⟩ := hx
    rw [wedgeLeft_dxT]
    refine dxT_mem_UR e ?_
    rintro _ ⟨p, rfl⟩
    refine Fin.cases ?_ (fun q => ?_) p
    · simpa using hj
    · simpa using hT ⟨q, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem curryLeft_add' (a b : E [⋀^Fin (k + 1)]→L[ℝ] ℝ) (u : E) :
    (a + b).curryLeft u = a.curryLeft u + b.curryLeft u := by
  ext v; simp [ContinuousAlternatingMap.curryLeft_apply_apply]

theorem curryLeft_smul' (c : ℝ) (a : E [⋀^Fin (k + 1)]→L[ℝ] ℝ) (u : E) :
    (c • a).curryLeft u = c • a.curryLeft u := by
  ext v; simp [ContinuousAlternatingMap.curryLeft_apply_apply]

theorem curryLeft_dxT_mem_UR {R : Set (Fin n)} (T : Fin (k + 1) → Fin n)
    (hT : Set.range T ⊆ R) (i : Fin n) : (dxT e (k + 1) T).curryLeft (e i) ∈ UR e R k := by
  induction k with
  | zero =>
    rw [dxT_succ, curryLeft_wedgeLeft_zero]
    exact Submodule.smul_mem _ _ (dxT_mem_UR e (by intro x ⟨p, _⟩; exact p.elim0))
  | succ k ih =>
    have h1 : Set.range (Fin.tail T) ⊆ R := by
      rintro _ ⟨q, rfl⟩; exact hT ⟨q.succ, rfl⟩
    rw [dxT_succ, curryLeft_wedgeLeft]
    refine sub_mem (Submodule.smul_mem _ _ (dxT_mem_UR e h1)) ?_
    exact wedgeLeft_mem_UR e (hT ⟨0, rfl⟩) (ih _ h1)

theorem curryLeft_mem_UR {R : Set (Fin n)} {β : E [⋀^Fin (k + 1)]→L[ℝ] ℝ}
    (hβ : β ∈ UR e R (k + 1)) (i : Fin n) : β.curryLeft (e i) ∈ UR e R k ∧
      (i ∉ R → β.curryLeft (e i) = 0) := by
  induction hβ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨T, hT, rfl⟩ := hx
    refine ⟨curryLeft_dxT_mem_UR e T hT i, fun hi => curryLeft_dxT_of_not_mem e ?_⟩
    exact fun ⟨p, hp⟩ => hi (hp ▸ hT ⟨p, rfl⟩)
  | zero => simp [ContinuousAlternatingMap.curryLeft_apply_apply]
  | add x y _ _ hx hy =>
    rw [curryLeft_add']
    exact ⟨add_mem hx.1 hy.1, fun hi => by rw [hx.2 hi, hy.2 hi, add_zero]⟩
  | smul c x _ hx =>
    rw [curryLeft_smul']
    exact ⟨Submodule.smul_mem _ _ hx.1, fun hi => by rw [hx.2 hi, smul_zero]⟩

theorem range_subset_of_inner_ne {R : Set (Fin n)} :
    ∀ (k : ℕ) (S : Fin k → Fin n) (β : E [⋀^Fin k]→L[ℝ] ℝ), β ∈ UR e R k →
      ⟪Covector.ofAlt (dxT e k S), Covector.ofAlt β⟫ ≠ 0 → Set.range S ⊆ R := by
  intro k
  induction k with
  | zero => intro S β _ _; rintro _ ⟨p, _⟩; exact p.elim0
  | succ k ih =>
    intro S β hβ hne
    rw [dxT_succ, inner_wedgeLeft] at hne
    have hc : β.curryLeft (e (S 0)) ≠ 0 := by
      intro h0; rw [h0] at hne; simp at hne
    have hS0 : S 0 ∈ R := by
      by_contra hn; exact hc ((curryLeft_mem_UR e hβ _).2 hn)
    have ht := ih (Fin.tail S) _ (curryLeft_mem_UR e hβ _).1 hne
    rintro _ ⟨p, rfl⟩
    refine Fin.cases hS0 (fun q => ht ⟨q, rfl⟩) p

/-- Basis covectors of tuples with different ranges are orthogonal. -/
theorem inner_dxT_eq_zero_of_range_ne {S T : Fin k → Fin n} (h : Set.range S ≠ Set.range T) :
    ⟪Covector.ofAlt (dxT e k S), Covector.ofAlt (dxT e k T)⟫ = 0 := by
  by_contra hne
  apply h
  refine Set.Subset.antisymm
    (range_subset_of_inner_ne e k S _ (dxT_mem_UR e (subset_refl _)) hne) ?_
  refine range_subset_of_inner_ne e k T _ (dxT_mem_UR e (subset_refl _)) ?_
  rwa [real_inner_comm]

theorem inner_deg_zero (α β : E [⋀^Fin 0]→L[ℝ] ℝ) :
    ⟪Covector.ofAlt α, Covector.ofAlt β⟫ = α 0 * β 0 := by
  rw [Covector.inner_def]
  simp [Covector.coeff_ofAlt]
  congr 1 <;> congr 1 <;> exact Subsingleton.elim _ _

theorem inner_dxT_zero (T : Fin 0 → Fin n) (α : E [⋀^Fin 0]→L[ℝ] ℝ) :
    ⟪Covector.ofAlt α, Covector.ofAlt (dxT e 0 T)⟫ = α 0 := by
  rw [inner_deg_zero]; simp [dxT]

/-- Resolution of the identity over all tuples. -/
theorem sum_inner_dxT_smul (α : E [⋀^Fin k]→L[ℝ] ℝ) :
    ((k.factorial : ℝ))⁻¹ • ∑ T : Fin k → Fin n,
      ⟪Covector.ofAlt α, Covector.ofAlt (dxT e k T)⟫ • dxT e k T = α := by
  induction k with
  | zero =>
    ext v
    have hv : v = 0 := Subsingleton.elim _ _
    subst hv
    simp
    rw [inner_dxT_zero]
    simp [dxT]
  | succ k ih =>
    have hc : ∀ (i : Fin n) (T : Fin k → Fin n),
        ⟪Covector.ofAlt (α.curryLeft (e i)), Covector.ofAlt (dxT e k T)⟫ =
          ⟪Covector.ofAlt α, Covector.ofAlt (dxT e (k + 1) (Fin.cons i T))⟫ := by
      intro i T
      rw [← wedgeLeft_dxT, ← real_inner_comm (Covector.ofAlt α), inner_wedgeLeft, real_inner_comm]
    have h1 := sum_wedgeLeft_curryLeft e α
    have h2 : ∀ i, wedgeLeft (e i) (α.curryLeft (e i)) = (k.factorial : ℝ)⁻¹ •
        ∑ T : Fin k → Fin n, ⟪Covector.ofAlt α, Covector.ofAlt (dxT e (k + 1) (Fin.cons i T))⟫ •
          dxT e (k + 1) (Fin.cons i T) := by
      intro i
      conv_lhs => rw [← ih (α.curryLeft (e i))]
      rw [map_smul, map_sum]
      simp only [map_smul, hc, wedgeLeft_dxT]
    simp only [h2, ← Finset.smul_sum] at h1
    have h3 : ∑ T' : Fin (k + 1) → Fin n,
        ⟪Covector.ofAlt α, Covector.ofAlt (dxT e (k + 1) T')⟫ • dxT e (k + 1) T' =
        ∑ i : Fin n, ∑ T : Fin k → Fin n,
          ⟪Covector.ofAlt α, Covector.ofAlt (dxT e (k + 1) (Fin.cons i T))⟫ •
            dxT e (k + 1) (Fin.cons i T) := by
      rw [← (Fin.consEquiv (fun _ => Fin n)).sum_comp, Fintype.sum_prod_type]
      rfl
    rw [h3, Nat.factorial_succ]
    have hk : (k.factorial : ℝ) ≠ 0 := by positivity
    have h5 := congrArg (fun x => (k.factorial : ℝ) • x) h1
    simp only [Finset.smul_sum, smul_smul, ← mul_assoc, mul_inv_cancel₀ hk, one_mul] at h5
    rw [h5, smul_smul]
    push_cast
    have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
    have : (((k : ℝ) + 1) * k.factorial)⁻¹ * (k.factorial * ((k : ℝ) + 1)) = 1 := by
      field_simp
    rw [this, one_smul]

theorem norm_ofAlt_dxT_le (T : Fin k → Fin n) : ‖Covector.ofAlt (dxT e k T)‖ ≤ 1 := by
  have key : ∀ (k : ℕ) (T : Fin k → Fin n),
      ⟪Covector.ofAlt (dxT e k T), Covector.ofAlt (dxT e k T)⟫ ≤ 1 := by
    intro k
    induction k with
    | zero => intro T; rw [inner_dxT_zero]; simp [dxT]
    | succ k ih =>
      intro T
      have hee : ⟪e (T 0), e (T 0)⟫ = 1 := by simp
      have hD := ih (Fin.tail T)
      rw [dxT_succ] at *
      set D := dxT e k (Fin.tail T)
      rw [inner_wedgeLeft]
      cases k with
      | zero =>
        rw [curryLeft_wedgeLeft_zero, hee, one_smul]; exact hD
      | succ k =>
        rw [curryLeft_wedgeLeft, hee, one_smul, map_sub, inner_sub_right]
        have : ⟪Covector.ofAlt D, Covector.ofAlt (wedgeLeft (e (T 0)) (D.curryLeft (e (T 0))))⟫
            = ⟪Covector.ofAlt (D.curryLeft (e (T 0))), Covector.ofAlt (D.curryLeft (e (T 0)))⟫ := by
          rw [real_inner_comm, inner_wedgeLeft]
        rw [this]
        have := real_inner_self_nonneg (x := Covector.ofAlt (D.curryLeft (e (T 0))))
        linarith
  have h := key k T
  rw [real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (Covector.ofAlt (dxT e k T))]

end FEEC
