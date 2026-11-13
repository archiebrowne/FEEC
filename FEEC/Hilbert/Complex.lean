/-
Hilbert complexes indexed by the natural numbers, and their three-term segments.
-/
import FEEC.Hilbert.Poincare

/-!
# Hilbert complexes

A `HilbertComplex W V` is the domain complex of a Hilbert complex in the sense of Arnold,
§4.1: Hilbert spaces `W k` (the ambient spaces), Hilbert spaces `V k` (the domains of the
differentials, with the graph inner product), injections `ι k : V k → W k` and bounded
differentials `d k : V k → V (k + 1)` with `d ∘ d = 0`. Completeness of `V k` in the graph
norm encodes closedness of the unbounded operator `d`.

The Hodge Laplacian at level `k` only involves `V (k-1) → V k → V (k+1)`; this is packaged
by `HilbertComplex.segment k` (level `k + 1`) and `HilbertComplex.segmentZero` (level `0`,
where the incoming space is zero), which are `ShortHilbertComplex`es.
-/

namespace FEEC

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- The domain complex of a Hilbert complex, indexed by `ℕ`. -/
structure HilbertComplex (W V : ℕ → Type*)
    [∀ k, NormedAddCommGroup (W k)] [∀ k, InnerProductSpace ℝ (W k)]
    [∀ k, NormedAddCommGroup (V k)] [∀ k, InnerProductSpace ℝ (V k)] where
  /-- The inclusion of the domain `V k` into the ambient space `W k`. -/
  ι : ∀ k, V k →L[ℝ] W k
  ι_injective : ∀ k, Function.Injective (ι k)
  /-- The differential. -/
  d : ∀ k, V k →L[ℝ] V (k + 1)
  d_d : ∀ k (u : V k), d (k + 1) (d k u) = 0
  /-- `V k` carries the graph inner product. -/
  inner_eq : ∀ k (u v : V k),
    ⟪u, v⟫ = ⟪ι k u, ι k v⟫ + ⟪ι (k + 1) (d k u), ι (k + 1) (d k v)⟫

namespace HilbertComplex

variable {W V : ℕ → Type*}
  [∀ k, NormedAddCommGroup (W k)] [∀ k, InnerProductSpace ℝ (W k)]
  [∀ k, NormedAddCommGroup (V k)] [∀ k, InnerProductSpace ℝ (V k)]
  (C : HilbertComplex W V)

/-- The segment `V k → V (k+1) → W (k+2)` of a Hilbert complex, which carries the Hodge
Laplacian at level `k + 1`. -/
def segment (k : ℕ) : ShortHilbertComplex (W k) (W (k + 1)) (W (k + 2)) (V k) (V (k + 1)) where
  ι₀ := C.ι k
  ι₁ := C.ι (k + 1)
  d₀ := C.d k
  d₁ := C.ι (k + 2) ∘L C.d (k + 1)
  d₁_d₀ τ := by simp [C.d_d]
  inner_V₀ := C.inner_eq k
  inner_V₁ := C.inner_eq (k + 1)

/-- The segment `0 → V 0 → W 1` of a Hilbert complex, which carries the Hodge Laplacian at
level `0`. The zero space is realised as the trivial submodule. -/
noncomputable def segmentZero :
    ShortHilbertComplex (⊥ : Submodule ℝ (W 0)) (W 0) (W 1) (⊥ : Submodule ℝ (V 0)) (V 0) where
  ι₀ := 0
  ι₁ := C.ι 0
  d₀ := (⊥ : Submodule ℝ (V 0)).subtypeL
  d₁ := C.ι 1 ∘L C.d 0
  d₁_d₀ τ := by
    have : (τ : V 0) = 0 := (Submodule.mem_bot ℝ).1 τ.2
    simp [this]
  inner_V₀ σ τ := by
    have : σ = 0 := Subsingleton.elim _ _
    simp [this]
  inner_V₁ := C.inner_eq 0

/-- A Hilbert complex is **closed** if the range of each differential is closed in the
ambient space (Arnold, §4.1). -/
def IsClosed : Prop := ∀ k, _root_.IsClosed (Set.range (C.ι (k + 1) ∘ C.d k))

variable [∀ k, CompleteSpace (W k)] [∀ k, CompleteSpace (V k)]

/-- **Poincaré inequality** for closed Hilbert complexes (Arnold, Theorem 4.6), on each
segment. -/
theorem exists_hasPoincareConst_segment (hC : C.IsClosed) (k : ℕ) :
    ∃ c, (C.segment k).HasPoincareConst c :=
  (C.segment k).exists_hasPoincareConst (hC k) (hC (k + 1))

/-- **Poincaré inequality** for closed Hilbert complexes, on the initial segment. -/
theorem exists_hasPoincareConst_segmentZero (hC : C.IsClosed) :
    ∃ c, C.segmentZero.HasPoincareConst c := by
  refine C.segmentZero.exists_hasPoincareConst ?_ (hC 0)
  have : Set.range (C.segmentZero.ι₁ ∘ C.segmentZero.d₀) = {0} := by
    ext x
    simp only [Set.mem_range, Function.comp_apply, Set.mem_singleton_iff]
    constructor
    · rintro ⟨τ, rfl⟩
      have : (τ : V 0) = 0 := (Submodule.mem_bot ℝ).1 τ.2
      simp [segmentZero, this]
    · rintro rfl
      exact ⟨0, by simp⟩
  rw [this]
  exact isClosed_singleton

end HilbertComplex

end FEEC
