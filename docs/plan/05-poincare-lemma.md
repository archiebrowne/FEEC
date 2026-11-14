# Part F — The L² Poincaré lemma on a box; unconditional well-posedness in every dimension

## Goal

For a box `Ω = {x : aᵢ < ⟨eᵢ, x⟩ < bᵢ}` in a Euclidean space `E` (any dimension `n`, `e` an
orthonormal basis):

1. **L² Poincaré lemma.** There is `C` such that every `ω ∈ L²Λᵏ⁺¹(Ω)` with weak `dω = 0`
   is `ω = dη` for some `η ∈ L²Λᵏ(Ω)` with `‖η‖ ≤ C‖ω‖`.
2. **Closedness.** `(deRhamComplex Ω).IsClosed`.
3. **Unconditional well-posedness.** The Hodge Laplace problem on `HΛᵏ⁺¹(Ω)` is well posed
   for every `k`, with no hypothesis; and there are no harmonic forms of degree `≥ 1`.

### Why a box, not a general star-shaped domain

On a domain star-shaped with respect to a ball the proof needs the averaged Poincaré /
Bogovskiĭ operators, which are weakly singular integral operators: their `L²` bound is a
Schur test and smoothness on test forms is delicate (Costabel–McIntosh). On a box the
homotopy can be done **one coordinate direction at a time**, and every operator is a
one-dimensional integral along a line. That is the version formalised here. The general
star-shaped case is left as a follow-on (see "Not done").

## Strategy: work entirely on test forms

`HasWeakExtDeriv η ω` means `⟪ω, φ⟫ = ⟪η, δφ⟫` for all test forms `φ`. So `η` exists as soon as
the functional `δφ ↦ ⟪ω, φ⟫` is well defined and `L²`-bounded, i.e.

  (★)  `|⟪ω, φ⟫| ≤ C ‖ω‖ ‖δφ‖`  for all test `(k+1)`-forms `φ`,

by the Riesz representation theorem. Since weak `dω = 0` means `⟪ω, δψ⟫ = 0` for test `ψ`,
(★) follows from a purely classical statement about smooth compactly supported forms:

> **Decomposition.** There is `C` such that every test `(k+1)`-form `φ` on `Ω` can be written
> `φ = δψ + χ` with `ψ`, `χ` test forms on `Ω` and `‖χ‖_{L²} ≤ C ‖δφ‖_{L²}`.

No density theorem, mollification or trace is needed: the weak definition is used exactly
as stated.

## F.1 `Wedge.lean` — exterior multiplication by a covector

`wedgeLeft e α := alternatizeUncurryFin (⟨e,·⟩ ⊗ α)`, i.e.
`(e ∧ α)(v₀,…,v_k) = Σᵢ (-1)ⁱ ⟨e,vᵢ⟩ α(v without vᵢ)`.

* Anticommutation: `u ⌟ (e ∧ α) = ⟨e,u⟩ α − e ∧ (u ⌟ α)` (and `u ⌟ (e ∧ α) = ⟨e,u⟩ α` in
  degree 0).
* `tangPart e α := α − e ∧ (e ⌟ α)`. For `‖e‖ = 1`: `e ⌟ tangPart e α = 0`; and if `u ⟂ e`,
  `u ⌟ α = 0` then `u ⌟ tangPart e α = 0`.
* A form of degree `≥ 1` annihilated by `eᵢ ⌟` for all vectors of a basis is zero.

## F.2 `LineIntegral.lean` — integrals along lines

For `f : E → F` smooth with compact support and a unit vector `e`:

* `lineInt e f x := ∫_ℝ f(x + τe) dτ`,  `halfLineInt e f x := ∫_{τ ≤ 0} f(x + τe) dτ`.
* Both are smooth, `D(lineInt e f) = lineInt e (Df)`, same for `halfLineInt`
  (differentiation under the integral; induction on the order).
* `∂_e lineInt e f = 0`, `∂_e halfLineInt e f = f`.
* Both commute with continuous linear maps.

`LineG.lean`: for a bump `θ` on `(a,b)` (`∫θ = 1`), `Θ(s) = ∫_{-∞}^s θ`,

  `lineG e θ f x := Θ(⟨e,x⟩) • lineInt e f x − halfLineInt e f x`.

This is the antiderivative of `−f` along `e`, corrected so that it has compact support:

* `D(lineG f)(x) = θ(⟨e,x⟩) ⟨e,·⟩ ⊗ lineInt e f x + lineG (Df)(x)`; in particular
  `∂_e lineG f = θ(⟨e,x⟩) lineInt e f − f`.
* `lineG f x = 0` when `⟨e,x⟩` is below (`Θ = 0`, half-line misses the support) or above
  (`Θ = 1`, half-line integral = full integral) both supports, or when the line through `x`
  misses `supp f`. Hence if `Ω` is a *slab* in direction `e` over `(a,b)`
  (`⟨e,x⟩ ∈ (a,b)` on `Ω`, and `Ω` invariant under moving `⟨e,x⟩` within `(a,b)`), then
  `lineG` maps `C_c^∞(Ω)` to `C_c^∞(Ω)`.

`LineL2.lean`: for continuous compactly supported `h ≥ 0` vanishing outside `Ω`,

  `∫_Ω (∫_ℝ h(x+τe)dτ)² dx ≤ (b−a)² ∫_Ω h²`

(Cauchy–Schwarz on a segment of length `≤ b−a`, then Tonelli and translation invariance).

## F.3 `BoxHomotopy.lean` — the homotopy in one direction

For forms: `S φ := e ∧ lineG e θ φ` (degree `+1`), `Q φ := θ(⟨e,x⟩) tangPart e (lineInt e φ)`.

**Homotopy identity.** For smooth compactly supported `φ` of degree `k+1`:

  `δ(Sφ) + S(δφ) = φ − Qφ`.

*Proof.* With `δ = −Σᵢ eᵢ ⌟ ∂ᵢ` and anticommutation,
`δ(e ∧ G) = −∂_e G − e ∧ δG`. By F.2, `∂_e Gφ = θ·Aφ − φ` (`A = lineInt`) and
`δ(Gφ) = G(δφ) − θ · e ⌟ Aφ` (`G` commutes with constant-coefficient maps; the extra term is
the derivative of `Θ`). Hence
`δ(Sφ) = φ − θ Aφ − e ∧ G(δφ) + θ e ∧ (e ⌟ Aφ) = φ − Qφ − S(δφ)`. ∎

Consequences: `S`, `Q` preserve test forms on a slab; `δQφ = Qδφ` (apply the identity to
`φ` and `δφ`, use `δδ = 0`); `e ⌟ Qφ = 0`, and `Q` preserves `u ⌟ · = 0` for `u ⟂ e`.

`BoxBounds.lean`: `‖Sφ‖_{L²(Ω)} ≤ C‖φ‖_{L²(Ω)}`, `‖Qφ‖_{L²(Ω)} ≤ C‖φ‖_{L²(Ω)}` from F.2.

## F.4 `PoincareLemma.lean`

**Iteration.** Let `R_j := Q_j ∘ ⋯ ∘ Q_1` (directions `e_1,…,e_j`). By induction on `j`:
`R_jφ` is a test form, `δR_jφ = R_jδφ`, `‖R_jφ‖ ≤ C_j‖φ‖`, `eᵢ ⌟ R_jφ = 0` for `i ≤ j`, and
`φ = δψ_j + χ_j + R_jφ` with `‖χ_j‖ ≤ C_j‖δφ‖`. Step: apply the homotopy identity in
direction `j+1` to `R_jφ`:
`R_jφ = δ(S R_jφ) + S(R_jδφ) + R_{j+1}φ`.
At `j = n`, `R_nφ` is annihilated by every `eᵢ ⌟`, hence is zero (degree `≥ 1`). This is the
Decomposition.

**Riesz step** (abstract): if `j : X →ₗ H`, `g : X →ₗ ℝ` and `|g x| ≤ C‖j x‖` then
`g = ⟪η, j ·⟫` for some `η ∈ H` with `‖η‖ ≤ C`.

**Poincaré lemma, closedness, well-posedness** as in the Goal. Range of `d` equals the
(closed) set of weakly closed forms.

## Not done

* General domains (star-shaped w.r.t. a ball, Lipschitz). The abstract theorems still take
  closedness as a hypothesis there.
* Degree 0 cohomology (`ker d` on `HΛ⁰` = constants) is not needed for closedness and is
  not proved.
