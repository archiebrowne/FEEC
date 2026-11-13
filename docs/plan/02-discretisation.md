# Part B — Approximation of Hilbert complexes (Arnold Ch. 5, AFW10 §3.3–3.4)

Setting: a `ShortHilbertComplex S` on `V₀ → V₁ → W₂` with Poincaré constant `c_P`.

## B.1 `Subcomplex.lean`

**Subcomplex.** Closed submodules `Vh₀ ≤ V₀`, `Vh₁ ≤ V₁` (in applications
finite-dimensional) with `d₀ Vh₀ ≤ Vh₁`.

`S.restrict Vh₀ Vh₁ h : ShortHilbertComplex W₀ W₁ W₂ Vh₀ Vh₁` — same `W`'s, maps
restricted. The graph-norm identities are inherited because a submodule of an inner
product space carries the restricted inner product. Consequently *all* of Part A applies
verbatim to `S_h := S.restrict …`: discrete cocycles `𝔷_h = 𝔷 ⊓ Vh₁`, discrete
coboundaries `𝔅_h = d₀ Vh₀`, discrete harmonic forms `𝔥_h = 𝔷_h ⊓ 𝔅_hᗮ` (in general
`𝔥_h ⊄ 𝔥`), and the discrete (Galerkin) problem is `S_h.IsSolution f σ_h u_h p_h`.

Lemmas relating the two: `𝔷_h ≤ 𝔷`, `𝔅_h ≤ 𝔅` (after coercion), hence `𝔥_h ⟂ 𝔅_h`,
`𝔥_h ≤ 𝔷`, and `𝔷ᗮ ⟂ 𝔥_h`.

**Bounded cochain projection.**

```
structure S.CochainProjection (Vh₀ Vh₁) where
  π₀ : V₀ →L[ℝ] V₀
  π₁ : V₁ →L[ℝ] V₁
  π₀_mem : ∀ τ, π₀ τ ∈ Vh₀        π₁_mem : ∀ v, π₁ v ∈ Vh₁
  π₀_id  : ∀ τ ∈ Vh₀, π₀ τ = τ    π₁_id  : ∀ v ∈ Vh₁, π₁ v = v
  comm₀  : ∀ τ, π₁ (d₀ τ) = d₀ (π₀ τ)
  comm₁  : ∀ u, ∀ v ∈ Vh₁, d₁ u = d₁ v → d₁ (π₁ u) = d₁ v
```

`comm₁` is the trace on a three-term segment of "`π₂ d₁ = d₁ π₁` and `π₂` is the identity
on `Vh₂`": if `d₁ u = d₁ v ∈ d₁ Vh₁` then `d₁ π₁ u = π₂ d₁ u = π₂ d₁ v = d₁ v`. For a
full `HilbertComplex` with genuine cochain projections `π k` this is derived, not assumed.

**Discrete Poincaré inequality (Arnold Thm 5.3).** If `S.HasPoincareConst c` and `π` is a
cochain projection with `‖π₀‖, ‖π₁‖ ≤ K` (`K ≥ 1` automatic if `Vh ≠ 0`; we take
`max K 1` or assume `1 ≤ K`), then `S_h.HasPoincareConst (c * K)`.

*Proof (level 1).* Let `v ∈ Vh₁`, `v ⟂ 𝔷_h`. Let `z = P_{𝔷ᗮ} v`; then `d₁ z = d₁ v` and
`‖z‖ ≤ c‖d₁ z‖ = c‖d₁ v‖`. Now `π₁ z ∈ Vh₁` and `d₁ π₁ z = d₁ v` by `comm₁`, so
`v − π₁ z ∈ 𝔷_h`, hence `⟪v, v − π₁ z⟫ = 0` and `‖v‖² = ⟪v, π₁ z⟫ ≤ ‖v‖ K ‖z‖ ≤ ‖v‖ K c ‖d₁ v‖`.
*Level 0* is identical with `comm₀`: for `τ ∈ Vh₀ ⟂ ker d₀|_h`, `z = P_{(ker d₀)ᗮ} τ`,
`d₀ π₀ z = π₁ d₀ z = π₁ d₀ τ = d₀ τ`. ∎

## B.2 `Harmonic.lean` — gap between harmonic forms (Arnold Thm 5.2)

With a cochain projection `π` (and `𝔅` closed):

* `∀ q ∈ 𝔥, ‖q − P_{𝔥_h} q‖ ≤ ‖q − π₁ q‖`.
  *Proof.* `π₁ q ∈ 𝔷_h` (as `d₁ π₁ q = d₁ 0 = 0` by `comm₁` with `v = 0`), so
  `π₁ q = P_{𝔥_h} π₁ q + b` with `b ∈ 𝔅_h`. Then `q − P_{𝔥_h} q = (q − π₁ q) + b'`-type
  argument: `P_{𝔥_h} q − q ⟂`… concretely, `q − P_{𝔥_h} q` is the `V`-projection error
  onto `𝔥_h`, and since `q ⟂ 𝔅 ⊇ 𝔅_h` we have `P_{𝔷_h} q = P_{𝔥_h} q`, so
  `‖q − P_{𝔥_h} q‖ = dist(q, 𝔷_h) ≤ ‖q − π₁ q‖`. ∎
* `∀ q ∈ 𝔥_h, ‖q − P_𝔥 q‖ ≤ ‖(1 − π₁) P_𝔥 q‖`.
  *Proof.* `q ∈ 𝔷`, so `q − P_𝔥 q ∈ 𝔅`; and `q ⟂ 𝔅_h`. Since `π₁ (q − P_𝔥 q) ∈ 𝔅_h`
  (by `comm₀`: `π₁ d₀ ρ = d₀ π₀ ρ`), `q − P_𝔥 q ⟂ … ` gives
  `‖q − P_𝔥 q‖² = ⟪q − P_𝔥 q, q − P_𝔥 q − π₁(q − P_𝔥 q)⟫ − …`; cleanest route:
  `q − P_𝔥 q − π₁(q − P_𝔥 q) = −(P_𝔥 q − π₁ P_𝔥 q)` because `π₁ q = q`; and
  `⟪q − P_𝔥 q, π₁(q − P_𝔥 q)⟫ = ⟪q, ·⟫ − ⟪P_𝔥 q, ·⟫ = 0 − 0` (first: `q ⟂ 𝔅_h`; second:
  `𝔥 ⟂ 𝔅`). Hence `‖q − P_𝔥 q‖² = −⟪q − P_𝔥 q, (1 − π₁) P_𝔥 q⟫ ≤ ‖q − P_𝔥 q‖ ‖(1−π₁)P_𝔥 q‖`. ∎

Corollary used later: if `‖r − π₁ r‖ ≤ μ ‖r‖` for all `r ∈ 𝔥`, then for `q ∈ 𝔥_h`,
`‖q − P_𝔥 q‖ ≤ μ ‖q‖`.

## B.3 `ErrorEstimate.lean`

**Stability (Arnold Thm 5.4).** `S_h` is well posed with constant
`stabilityConst (c * K)`: immediate from A.3 applied to `S_h` and B.1.

**Quasi-optimal error estimate (Arnold Thm 5.5, AFW10 Thm 3.9).** Let `(σ,u,p)` solve
`S.IsSolution f` and `(σ_h,u_h,p_h)` solve `S_h.IsSolution f`. Let `μ ≥ 0` with
`‖r − π₁ r‖ ≤ μ‖r‖` for `r ∈ 𝔥`. Then for all `τ ∈ Vh₀`, `v, q, w ∈ Vh₁`:

  ‖σ − σ_h‖ + ‖u − u_h‖ + ‖p − p_h‖
     ≤ C · ( ‖σ − τ‖ + ‖u − v‖ + ‖p − q‖ + μ ‖P_𝔅 u − w‖ ),

all norms `V`-norms, `C` an explicit function of `c` and `K`.

*Proof.* Fix `τ, v ∈ V_h` and put `q' := P_{𝔥_h} p ∈ 𝔥_h`. Subtracting the equations
tested with discrete `(τ', v', q')`:

  B_h(σ_h − τ, u_h − v, p_h − q'; τ', v', q'')
      = B(σ − τ, u − v, p − q'; τ', v', q'') + ⟪u, q''⟫_W ,

because the continuous solution satisfies the first two equations for all test
functions in `V ⊇ V_h`, while its third equation only holds against `𝔥`, not `𝔥_h`.
This exhibits `(σ_h − τ, u_h − v, p_h − q')` as the solution of a *general* discrete
problem with functionals bounded by `‖σ−τ‖ + ‖u−v‖ + ‖p−q'‖ + ‖P_{𝔥_h} u‖`. By discrete
stability, `‖σ_h−τ‖ + ‖u_h−v‖ + ‖p_h−q'‖` is bounded by `stabilityConst (cK)` times that.

* `‖p − q'‖ = ‖p − P_{𝔥_h} p‖ ≤ ‖p − π₁ p‖ = ‖(1−π₁)(p − q)‖ ≤ (1+K)‖p − q‖` for any
  `q ∈ Vh₁` (B.2, first bullet).
* `‖P_{𝔥_h} u‖`: `u ⟂ 𝔥` so `u = u_𝔅 + u_⊥`; `u_⊥ ⟂ 𝔷 ⊇ 𝔥_h`. For `q'' ∈ 𝔥_h`:
  `⟪u, q''⟫ = ⟪u_𝔅, q''⟫ = ⟪u_𝔅, q'' − P_𝔥 q''⟫` (as `𝔅 ⟂ 𝔥`)
  `= ⟪u_𝔅 − π₁ u_𝔅, q'' − P_𝔥 q''⟫` (as `π₁ u_𝔅 ∈ 𝔅_h`, `q'' ⟂ 𝔅_h`, `P_𝔥 q'' ⟂ 𝔅`)
  `≤ ‖(1−π₁)u_𝔅‖ · μ‖q''‖`, and `(1−π₁)u_𝔅 = (1−π₁)(u_𝔅 − w)` for `w ∈ Vh₁`. So
  `‖P_{𝔥_h} u‖ ≤ μ (1+K) ‖P_𝔅 u − w‖`.

The triangle inequality finishes the proof. ∎

## B.4 Full complexes

For an `ℕ`-indexed `HilbertComplex C`:

* `C.Subcomplex`: closed `Vh k ≤ V k` with `d (Vh k) ≤ Vh (k+1)`; `C.restrict Vh` is a
  `HilbertComplex W (fun k ↦ Vh k)`.
* `C.CochainProjection Vh`: `π k : V k →L V k`, idempotent onto `Vh k`,
  `π (k+1) ∘ d k = d k ∘ π k`. Each yields `(C.segment k).CochainProjection …` and one
  for `segmentZero`.
* `(C.restrict Vh).segment k = (C.segment k).restrict …` (definitional or by `rfl`-lemma).

`Main.lean` restates stability and the error estimate for `C`, level `k+1` and level `0`.
