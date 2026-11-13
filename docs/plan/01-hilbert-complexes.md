# Part A — Hilbert complexes and the abstract Hodge Laplacian (Arnold Ch. 4)

All spaces are real Hilbert spaces. `⟪·,·⟫` is the inner product of whatever space the
arguments live in; for `u v : V₁` the "W-inner product" is `⟪ι₁ u, ι₁ v⟫`.

## A.0 `InfSup.lean` — Babuška–Nečas, symmetric case

Let `X` be a Hilbert space, `B : X →L[ℝ] X →L[ℝ] ℝ` symmetric, and suppose there are
`γ > 0`, `M ≥ 0` with

  ∀ x, ∃ y, ‖y‖ ≤ M ‖x‖ ∧ γ ‖x‖² ≤ B x y.        (inf-sup, "constructive" form)

Then for every `F : X →L[ℝ] ℝ` there is a unique `x` with `B x y = F y` for all `y`, and
`‖x‖ ≤ (M/γ) ‖F‖`.

*Proof.* Let `A : X →L X` be the Riesz representative, `⟪A x, y⟫ = B x y`
(`InnerProductSpace.continuousLinearMapOfBilin`). From the hypothesis,
`γ‖x‖² ≤ ⟪Ax,y⟫ ≤ ‖Ax‖ M ‖x‖`, so `A` is bounded below by `γ/M`: injective with closed
range (antilipschitz ⇒ closed range, as in Mathlib's `LaxMilgram.lean`). `A` is
self-adjoint by symmetry, so `(range A)ᗮ = ker A = 0`, hence `range A = ⊤`. Take
`x = A⁻¹ (Riesz F)`. ∎

Also the a-priori form: if `B x y = F y ∀ y` then `‖x‖ ≤ (M/γ)‖F‖` (no completeness
needed) — this is what the error analysis uses.

## A.1 `ShortComplex.lean`

```
structure ShortHilbertComplex (W₀ W₁ W₂ V₀ V₁) where
  ι₀ : V₀ →L[ℝ] W₀
  ι₁ : V₁ →L[ℝ] W₁
  d₀ : V₀ →L[ℝ] V₁
  d₁ : V₁ →L[ℝ] W₂
  d₁_comp_d₀ : d₁ ∘L d₀ = 0
  inner_V₀ : ⟪σ, τ⟫ = ⟪ι₀ σ, ι₀ τ⟫ + ⟪ι₁ (d₀ σ), ι₁ (d₀ τ)⟫
  inner_V₁ : ⟪u, v⟫ = ⟪ι₁ u, ι₁ v⟫ + ⟪d₁ u, d₁ v⟫
```

Definitions (submodules of `V₁` unless stated):

* `cocycles 𝔷 := ker d₁` (closed), `coboundaries 𝔅 := range d₀`,
* `cocycles₀ := ker d₀ ≤ V₀`,
* `harmonic 𝔥 := 𝔷 ⊓ 𝔅ᗮ` (V-orthogonal complement).

Basic lemmas:

* `norm_sq_V₁ : ‖u‖² = ‖ι₁ u‖² + ‖d₁ u‖²`, same for `V₀`; `‖ι₁ u‖ ≤ ‖u‖`, `‖d₁ u‖ ≤ ‖u‖`.
* On `𝔷` the V- and W-inner products agree: `d₁ z = 0 → ⟪z, v⟫ = ⟪ι₁ z, ι₁ v⟫`.
* `𝔅 ≤ 𝔷`; `mem_harmonic_iff : p ∈ 𝔥 ↔ d₁ p = 0 ∧ ∀ τ, ⟪ι₁ p, ι₁ (d₀ τ)⟫ = 0`.
* `𝔥`, `𝔷` closed; `𝔥 ⟂ 𝔅`, `𝔷ᗮ ⟂ 𝔷`.

**Hodge decomposition (Arnold Thm 4.5).** If `𝔅` is closed then
`V₁ = 𝔅 ⊕ 𝔥 ⊕ 𝔷ᗮ` orthogonally (for both inner products, where it makes sense):
every `u` is uniquely `u_𝔅 + u_𝔥 + u_⊥`. Formal statement: with `P_𝔅, P_𝔥, P_⊥` the
orthogonal projections, `P_𝔅 u + P_𝔥 u + P_⊥ u = u` and
`‖u‖² = ‖P_𝔅 u‖² + ‖P_𝔥 u‖² + ‖P_⊥ u‖²`.

*Proof.* `V₁ = 𝔷 ⊕ 𝔷ᗮ` since `𝔷` closed. Inside `𝔷`, `𝔅` is closed so `𝔷 = 𝔅 ⊕ (𝔷 ⊓ 𝔅ᗮ)`.
Concretely `P_𝔥 u = P_𝔷 u − P_𝔅 u` using `𝔅 ≤ 𝔷`. ∎

**Harmonic forms ≅ cohomology.** If `𝔅` closed, `𝔥 ≃ₗ 𝔷 ⧸ 𝔅` (the composite
`𝔥 ↪ 𝔷 ↠ 𝔷/𝔅` is bijective by the decomposition `𝔷 = 𝔅 ⊕ 𝔥`).

## A.2 `Poincare.lean`

`structure S.HasPoincareConst (c : ℝ) : Prop`:

* `0 ≤ c`,
* `∀ τ ∈ (ker d₀)ᗮ, ‖τ‖ ≤ c ‖ι₁ (d₀ τ)‖`,
* `∀ v ∈ 𝔷ᗮ, ‖v‖ ≤ c ‖d₁ v‖`.

**Poincaré inequality (Arnold Thm 4.6).** If `range (ι₁ ∘ d₀)` and `range d₁` are closed
(in `W₁`, `W₂`), then `∃ c, S.HasPoincareConst c`.

*Proof.* `d₁` restricted to `𝔷ᗮ` is a continuous injective linear map from a Banach
space with closed range, hence antilipschitz by the open mapping theorem
(Mathlib: `ContinuousLinearMap`/`LinearMap` antilipschitz for injective maps with
closed range; else via `ContinuousLinearEquiv.ofBijective` onto the range). Same for
`ι₁ ∘ d₀` on `(ker d₀)ᗮ` (injective there: `ι₁ (d₀ τ) = 0` gives `‖d₀ τ‖² = ‖ι₁ d₀ τ‖² + ‖d₁ d₀ τ‖² = 0`). ∎

Consequences of `HasPoincareConst c`:

* `𝔅` is closed in `V₁` (so the Hodge decomposition applies).
* *Bounded potentials:* for every `b ∈ 𝔅` there is `ρ ∈ V₀` with `d₀ ρ = b` and
  `‖ρ‖ ≤ c ‖ι₁ b‖` (take any preimage and project onto `(ker d₀)ᗮ`).
* Finite-dimensional `V₀, V₁` ⇒ a Poincaré constant exists (closed ranges automatic).

## A.3 `HodgeLaplace.lean` — the mixed weak formulation (Arnold §4.4)

Unknowns `σ : V₀`, `u : V₁`, `p ∈ 𝔥`; data `f : W₁`.

```
S.IsSolution f σ u p :=
  p ∈ 𝔥 ∧
  (∀ τ, ⟪ι₀ σ, ι₀ τ⟫ − ⟪ι₁ (d₀ τ), ι₁ u⟫ = 0) ∧
  (∀ v, ⟪ι₁ (d₀ σ), ι₁ v⟫ + ⟪d₁ u, d₁ v⟫ + ⟪ι₁ p, ι₁ v⟫ = ⟪f, ι₁ v⟫) ∧
  (∀ q ∈ 𝔥, ⟪ι₁ u, ι₁ q⟫ = 0)
```

More generally, for functionals `F₀ : V₀ →L ℝ`, `F₁ : V₁ →L ℝ`, `F₂ : 𝔥 →L ℝ` we define
`S.IsGenSolution F₀ F₁ F₂ σ u p` (right-hand sides `F₀ τ`, `F₁ v`, `F₂ q`). The general
form is needed for the error analysis.

Product space `X := WithLp 2 (V₀ × WithLp 2 (V₁ × 𝔥))` and the *symmetric* form

  B(σ,u,p; τ,v,q) = ⟪σ,τ⟫_W − ⟪dτ,u⟫_W − ⟪dσ,v⟫_W − ⟪du,dv⟫ − ⟪p,v⟫_W − ⟪u,q⟫_W.

**Inf-sup (Arnold Thm 4.9).** Assume `S.HasPoincareConst c`. For `x = (σ,u,p)` write
`u = u_𝔅 + u_𝔥 + u_⊥`, pick `ρ` with `d₀ ρ = u_𝔅`, `‖ρ‖ ≤ c‖u_𝔅‖`, and test with

  τ = σ − ρ/c'²,  v = −(u + d₀σ + p),  q = p − u_𝔥     (c' = max c 1).

Then
`B(x; y) = ‖σ‖_W² + ‖dσ‖² + ‖du‖² + ‖p‖² + ‖u_𝔥‖² + ‖u_𝔅‖²/c'² − ⟪σ,ρ⟫_W/c'²`
`        ≥ ½‖σ‖_W² + ‖dσ‖² + ‖du‖² + ‖p‖² + ‖u_𝔥‖² + ‖u_𝔅‖²/(2c'²)`
and, using `‖u_⊥‖ ≤ c‖du‖`, this is `≥ γ(c) ‖x‖²` with an explicit `γ(c) > 0`, while
`‖y‖ ≤ M ‖x‖` with an explicit absolute `M`. (Cross terms: `⟪dσ, p⟫ = 0`, `⟪dσ, u⟫`
cancels between the first and second equations, `⟪p, u⟫ − ⟪u, p⟫` cancels, `⟪u, u_𝔥⟫ = ‖u_𝔥‖²`,
`⟪dρ, u⟫ = ‖u_𝔅‖²`.) The exact constants are fixed during formalisation and exposed as
`FEEC.stabilityConst c`.

**Well-posedness (Arnold Thm 4.8).** If `S.HasPoincareConst c` then for all `F₀ F₁ F₂`
there is a unique `(σ,u,p)` solving the general problem, and
`‖σ‖ + ‖u‖ + ‖p‖ ≤ stabilityConst c * (‖F₀‖ + ‖F₁‖ + ‖F₂‖)`. In particular for data
`f : W₁`: `∃! (σ,u,p), S.IsSolution f σ u p` and
`‖σ‖_V + ‖u‖_V + ‖p‖ ≤ stabilityConst c * ‖f‖`.

Also: characterisation of the solution pieces (`p = P_𝔥 f`-type statements) is *not*
needed and is skipped.

## A.4 `Complex.lean`

```
structure HilbertComplex (W V : ℕ → Type*) [Hilbert instances] where
  ι : ∀ k, V k →L[ℝ] W k
  ι_injective : ∀ k, Injective (ι k)
  d : ∀ k, V k →L[ℝ] V (k+1)
  d_comp_d : ∀ k, d (k+1) ∘L d k = 0
  inner_eq : ∀ k u v, ⟪u, v⟫ = ⟪ι k u, ι k v⟫ + ⟪ι (k+1) (d k u), ι (k+1) (d k v)⟫
```

* `C.segment k : ShortHilbertComplex (W k) (W (k+1)) (W (k+2)) (V k) (V (k+1))`
  (Hodge Laplacian at level `k+1`), with `d₁ := ι (k+2) ∘ d (k+1)`.
* `C.segmentZero : ShortHilbertComplex PUnit (W 0) (W 1) PUnit (V 0)` (level 0).
* `C.IsClosed : Prop := ∀ k, IsClosed (range (ι (k+1) ∘L d k))`; closed complexes have a
  Poincaré constant on every segment.
