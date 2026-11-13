/-
Subcomplexes and cochain projections of ℕ-indexed Hilbert complexes.
-/
import FEEC.Hilbert.Complex
import FEEC.Discrete.Subcomplex

/-!
# Subcomplexes and bounded cochain projections of Hilbert complexes

For an `ℕ`-indexed `HilbertComplex C` (Arnold, §5.2):

* `C.Subcomplex`: subspaces `Vh k ⊆ V k` with `d (Vh k) ⊆ Vh (k + 1)`; `Vh.toComplex` is the
  subcomplex as a Hilbert complex.
* `C.CochainProjection Vh`: projections `π k : V k → Vh k`, bounded in the `V`-norm, with
  `π (k + 1) ∘ d k = d k ∘ π k`.

Both restrict to the three-term segments on which the Hodge Laplacian lives, so the results
of `FEEC.Discrete.ErrorEstimate` apply at every level.
-/

namespace FEEC

namespace HilbertComplex

variable {W V : ℕ → Type*}
  [∀ k, NormedAddCommGroup (W k)] [∀ k, InnerProductSpace ℝ (W k)]
  [∀ k, NormedAddCommGroup (V k)] [∀ k, InnerProductSpace ℝ (V k)]
  (C : HilbertComplex W V)

/-- A subcomplex of a Hilbert complex. -/
structure Subcomplex where
  /-- The discrete spaces `Vh k ⊆ V k`. -/
  carrier : ∀ k, Submodule ℝ (V k)
  map_d : ∀ k, ∀ u ∈ carrier k, C.d k u ∈ carrier (k + 1)

variable {C}

namespace Subcomplex

variable (Vh : C.Subcomplex)

/-- A subcomplex of a Hilbert complex is a Hilbert complex (with the same ambient spaces). -/
noncomputable def toComplex : HilbertComplex W (fun k => Vh.carrier k) where
  ι k := C.ι k ∘L (Vh.carrier k).subtypeL
  ι_injective k := (C.ι_injective k).comp Subtype.val_injective
  d k := (C.d k ∘L (Vh.carrier k).subtypeL).codRestrict (Vh.carrier (k + 1))
    fun u => Vh.map_d k u u.2
  d_d k u := Subtype.ext (C.d_d k u)
  inner_eq k u v := C.inner_eq k u v

/-- The restriction of a subcomplex to the segment carrying the Hodge Laplacian at level
`k + 1`. -/
noncomputable def segment (k : ℕ) : (C.segment k).Subcomplex where
  carrier₀ := Vh.carrier k
  carrier₁ := Vh.carrier (k + 1)
  map_d₀ := Vh.map_d k

/-- The restriction of a subcomplex to the segment carrying the Hodge Laplacian at
level `0`. -/
noncomputable def segmentZero : C.segmentZero.Subcomplex where
  carrier₀ := ⊤
  carrier₁ := Vh.carrier 0
  map_d₀ τ _ := by
    have : (τ : V 0) = 0 := (Submodule.mem_bot ℝ).1 τ.2
    simp [HilbertComplex.segmentZero, this]

instance (k : ℕ) [h : CompleteSpace (Vh.carrier k)] : CompleteSpace (Vh.segment k).carrier₀ := h

instance (k : ℕ) [h : CompleteSpace (Vh.carrier (k + 1))] :
    CompleteSpace (Vh.segment k).carrier₁ := h

instance : CompleteSpace Vh.segmentZero.carrier₀ :=
  inferInstanceAs (CompleteSpace (⊤ : Submodule ℝ (⊥ : Submodule ℝ (V 0))))

instance [h : CompleteSpace (Vh.carrier 0)] : CompleteSpace Vh.segmentZero.carrier₁ := h

end Subcomplex

variable (C) in
/-- A **bounded cochain projection** from a Hilbert complex onto a subcomplex
(Arnold, §5.2). -/
structure CochainProjection (Vh : C.Subcomplex) where
  /-- The projections `V k → Vh k`. -/
  π : ∀ k, V k →L[ℝ] V k
  π_mem : ∀ k u, π k u ∈ Vh.carrier k
  π_id : ∀ k, ∀ u ∈ Vh.carrier k, π k u = u
  comm : ∀ k u, π (k + 1) (C.d k u) = C.d k (π k u)

namespace CochainProjection

variable {Vh : C.Subcomplex} (π : C.CochainProjection Vh)

/-- A cochain projection of a Hilbert complex restricts to each segment. -/
noncomputable def segment (k : ℕ) : (C.segment k).CochainProjection (Vh.segment k) where
  π₀ := π.π k
  π₁ := π.π (k + 1)
  π₀_mem := π.π_mem k
  π₁_mem := π.π_mem (k + 1)
  π₀_id := π.π_id k
  π₁_id := π.π_id (k + 1)
  comm₀ := π.comm k
  comm₁ u v hv h := by
    have h' : C.d (k + 1) u = C.d (k + 1) v := C.ι_injective _ h
    change C.ι (k + 2) (C.d (k + 1) (π.π (k + 1) u)) = C.ι (k + 2) (C.d (k + 1) v)
    rw [← π.comm, h', π.π_id _ _ (Vh.map_d _ v hv)]

/-- A cochain projection of a Hilbert complex restricts to the initial segment. -/
noncomputable def segmentZero : C.segmentZero.CochainProjection Vh.segmentZero where
  π₀ := ContinuousLinearMap.id ℝ _
  π₁ := π.π 0
  π₀_mem _ := Submodule.mem_top
  π₁_mem := π.π_mem 0
  π₀_id _ _ := rfl
  π₁_id := π.π_id 0
  comm₀ τ := by
    have : (τ : V 0) = 0 := (Submodule.mem_bot ℝ).1 τ.2
    simp [HilbertComplex.segmentZero, this]
  comm₁ u v hv h := by
    have h' : C.d 0 u = C.d 0 v := C.ι_injective _ h
    change C.ι 1 (C.d 0 (π.π 0 u)) = C.ι 1 (C.d 0 v)
    rw [← π.comm, h', π.π_id _ _ (Vh.map_d _ v hv)]

end CochainProjection

end HilbertComplex

end FEEC
