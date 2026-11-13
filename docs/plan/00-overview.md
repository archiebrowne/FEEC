# FEEC in Lean 4 — informal plan

## Goal

A Lean 4 / Mathlib formalisation of the main results of finite element exterior
calculus (FEEC), following

* D. N. Arnold, *Finite Element Exterior Calculus*, SIAM 2018 (the guide; "Arnold"),
* D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge
  theory to numerical stability*, Bull. AMS 47 (2010) ("AFW10") for the abstract theory.

This realises Recommendation 1 of the landscape report
(`PDE_methods_formalisation_landscape_Nov2026.pdf`, §5.1), but as a standalone library in
this repository, depending only on Mathlib (no Tau Ceti dependency).

Chapter/section pointers to Arnold's book are given per file; theorem numbers are quoted
from memory and should be read as "the theorem of that name in that section".

## Scope

We formalise the *main results*, not the whole book.

| Part | Arnold | Content | Status target |
|------|--------|---------|---------------|
| A | Ch. 4 | Hilbert complexes: Hodge decomposition, harmonic forms, Poincaré inequality, the abstract Hodge Laplacian in mixed weak form and its well-posedness | fully proved |
| B | Ch. 5 | Approximation of Hilbert complexes: subcomplexes, bounded cochain projections, discrete Poincaré inequality, gap between harmonic forms, stability, quasi-optimal error estimate | fully proved |
| C | Ch. 6 | The de Rham complex: differential forms on a Euclidean domain, exterior derivative, Koszul operator, homotopy formula, the L² de Rham complex `HΛᵏ(Ω)` as a Hilbert complex | fully proved, except closedness (see below) |
| D | Ch. 7 (§7.1–7.3) | Polynomial differential forms `𝓗ᵣΛᵏ`, `𝓟ᵣΛᵏ`, `𝓟ᵣ⁻Λᵏ`; exactness of the polynomial de Rham and Koszul complexes | fully proved |

### Explicitly out of scope (documented, not attempted)

* Ch. 2–3 background as such (homological algebra, unbounded operators): we use the
  *domain complex* presentation (below), which avoids unbounded operators entirely.
* Closedness of the L² de Rham complex on Lipschitz domains (needs Rellich/Gaffney/
  Poincaré lemma with L² bounds). The abstract theory takes the Poincaré inequality as
  a hypothesis, so the de Rham application is stated *conditionally* on it.
* Improved error estimates (Arnold Thm 5.6, needs compactness + W-bounded projections),
  eigenvalue problems, parabolic/hyperbolic problems (Ch. 8).
* Simplicial meshes, degrees of freedom, unisolvence, geometric decomposition, Whitney
  forms on a triangulation, and the *construction* of bounded cochain projections
  (smoothed projections). The existence of a bounded cochain projection is a hypothesis
  of Part B, exactly as in the abstract theory.
* Dimension counts for `𝓟ᵣΛᵏ`, `𝓟ᵣ⁻Λᵏ`.

## Key design decisions

1. **Domain complexes, not unbounded operators.** A Hilbert complex `(Wᵏ, dᵏ)` with
   closed densely defined `d` is equivalent to its *domain complex* `(Vᵏ, d)`: Hilbert
   spaces `Vᵏ` (graph norm) with *bounded* `d : Vᵏ → Vᵏ⁺¹`, plus bounded injections
   `ι : Vᵏ → Wᵏ` with `⟪u,v⟫_V = ⟪ιu,ιv⟫_W + ⟪ι du, ι dv⟫_W`. Closedness of `d` is encoded
   by completeness of `Vᵏ`. Everything in Arnold Ch. 4–5 needed for the *mixed weak
   formulation* (which never mentions `d*`) can be stated this way, using only Mathlib's
   bounded-operator Hilbert space theory. Density of `ι` is not needed and not assumed —
   so a subcomplex `V_h ⊂ V` *is again* a complex of the same kind (same `W`), and the
   discrete problem is literally the continuous definition applied to the restricted
   complex.

2. **Three-term segments carry the theory.** The Hodge Laplacian at level `k` only sees
   `Vᵏ⁻¹ → Vᵏ → Wᵏ⁺¹`. We develop Parts A–B for a structure `ShortHilbertComplex`
   (`V₀ --d₀--> V₁ --d₁--> W₂`). An `ℕ`-indexed `HilbertComplex` yields a segment for each
   level `k+1`, and for level `0` with `V₋₁ = 0` (`PUnit`). This avoids integer indexing
   and `k-1` casts, and treats `k = 0` correctly (a truncated `k-1 = 0` in `ℕ` would give
   a wrong norm on the σ-variable).

3. **Explicit constants.** Stability constants are explicit functions of the Poincaré
   constant `c_P` (and of `‖π_h‖` in Part B), so that "uniform in `h`" is a theorem
   about one formula rather than a quantifier alternation.

4. **Differential forms = Mathlib's.** A `k`-form on `E` is `E → E [⋀^Fin k]→L[ℝ] ℝ`,
   with Mathlib's `extDeriv` and `extDeriv_extDeriv`. The interior product is
   `ContinuousAlternatingMap.curryLeft`. For L² theory the fibre needs an inner product,
   which we put on a type synonym `Covector E k`.

5. **Weak exterior derivative by duality with the codifferential.** `HΛᵏ(Ω)` is the
   set of pairs `(ω, η) ∈ L²Λᵏ × L²Λᵏ⁺¹` with `∫⟪η, φ⟫ = ∫⟪ω, δφ⟫` for all test forms
   `φ ∈ C_c^∞(Ω; Λᵏ⁺¹)`. It is a closed subspace of a product of Hilbert spaces, hence
   complete, and the graph-norm identity holds by construction.

## File layout

```
FEEC/
  Hilbert/
    InfSup.lean            -- Babuška–Nečas for symmetric forms          (Part A)
    ShortComplex.lean      -- ShortHilbertComplex, 𝔷, 𝔅, 𝔥, Hodge decomp. (Part A)
    Poincare.lean          -- Poincaré inequality ⇔ closed range          (Part A)
    HodgeLaplace.lean      -- mixed problem, inf-sup, well-posedness      (Part A)
    Complex.lean           -- ℕ-indexed HilbertComplex and its segments   (Part A)
  Discrete/
    Subcomplex.lean        -- restriction, cochain projections, discrete Poincaré (Part B)
    Harmonic.lean          -- gap between 𝔥 and 𝔥_h                       (Part B)
    ErrorEstimate.lean     -- stability + quasi-optimality                (Part B)
  DeRham/
    Koszul.lean            -- κ, κ² = 0, homotopy formula                 (Part C/D)
    Homogeneous.lean       -- 𝓗ᵣΛᵏ, Euler, d and κ on homogeneous forms   (Part D)
    Polynomial.lean        -- 𝓟ᵣΛᵏ, 𝓟ᵣ⁻Λᵏ, exactness                      (Part D)
    Covector.lean          -- inner product on k-covectors                (Part C)
    Codifferential.lean    -- δ on smooth forms, δ² = 0, test forms       (Part C)
    L2Complex.lean         -- HΛᵏ(Ω) as a HilbertComplex                  (Part C)
    Classical.lean         -- smooth forms lie in HΛ, weak d = extDeriv   (Part C, stretch)
  Main.lean                -- headline theorems restated in one place
```

Detailed plans: `01-hilbert-complexes.md`, `02-discretisation.md`, `03-de-rham.md`.

## Working method

* Statements and definitions are written first (by the main agent), with `sorry` proofs;
  each file must compile at that stage.
* Proofs are then filled, delegating self-contained lemmas to cheaper sub-agents.
* A commit after each compiled milestone. No `axiom`s; the final state should have no
  `sorry` in Parts A, B, D; any remaining `sorry` in Part C is listed in `STATUS.md`.
