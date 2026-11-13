# Parts C and D — the de Rham complex (Arnold Ch. 6, §7.1–7.3)

Throughout `E` is a finite-dimensional real inner product space (think `ℝⁿ`), and a
*`k`-form* is a map `ω : E → E [⋀^Fin k]→L[ℝ] ℝ` (Mathlib's convention). Mathlib provides
`extDeriv ω : E → E [⋀^Fin (k+1)]→L[ℝ] ℝ`,

  (dω)(x)(v₀,…,v_k) = Σⱼ (−1)ʲ (Dω(x) vⱼ)(v₀,…,v̂ⱼ,…,v_k)        (`extDeriv_apply`)

and `d ∘ d = 0` for `C²` forms (`extDeriv_extDeriv`).

## D.1 `Koszul.lean` (Arnold §7.2)

* `koszul ω : E → E [⋀^Fin k]→L[ℝ] ℝ` for a `(k+1)`-form `ω`:
  `(κω)(x) = (ω x).curryLeft x`, i.e. `(κω)ₓ(v₁,…,v_k) = ωₓ(x, v₁,…,v_k)`.
* `koszul_koszul : κ (κ ω) = 0` (`curryLeft_same`).
* Linearity; `ContDiff` preservation (`curryLeft` is a continuous bilinear operation).
* **Homotopy formula (general form).** For `ω` a differentiable `k`-form, `k ≥ 1`
  (and the appropriate variant for `k = 0`):

    (d κ ω)(x) + (κ d ω)(x) = k • ω(x) + Dω(x) x .

  *Proof.* Evaluate on `(v₁,…,v_k)`.
  `D(κω)(x) w = (Dω(x) w).curryLeft x + (ω x).curryLeft w` (product rule for the bilinear
  map `curryLeft`), so
  `(dκω)(v₁..v_k) = Σᵢ (−1)^{i−1} [ (Dω(x)vᵢ)(x, v̂ᵢ) + ω(vᵢ, v̂ᵢ) ]`, and
  `Σᵢ (−1)^{i−1} ω(vᵢ, v₁..v̂ᵢ..v_k) = k ω(v₁..v_k)` by alternation. On the other side
  `(κdω)(v₁..v_k) = dω(x, v₁..v_k) = (Dω(x)x)(v₁..v_k) − Σᵢ (−1)^{i−1}(Dω(x)vᵢ)(x, v̂ᵢ)`.
  The sums cancel. ∎ (In Lean: `Fin.sum_univ_succ`, `Fin.succAbove`/`removeNth` lemmas,
  and an auxiliary lemma `Σᵢ (−1)ⁱ f (vᵢ, v.removeNth i) = k • f v` for alternating `f`.)

  The `k = 0` case: `κ` of a 0-form is 0 by convention and `(κ d f)(x) = Df(x) x`.
  To keep one statement we phrase the formula for `ω` of degree `k` with
  `κ : Λ^{k+1} → Λ^k` and treat `d κ ω` only when `k = k' + 1`; the degree-0 statement is
  a separate one-line lemma.

## D.2 `Homogeneous.lean` (Arnold §7.1)

`IsHomogeneousForm r ω : Prop := ContDiff ℝ ⊤ ω ∧ ∀ (t : ℝ) x, ω (t • x) = t ^ r • ω x`,
and the submodule `𝓗 r k` (`homogeneousForms E r k`) of such forms. (A smooth map that is
homogeneous of degree `r ∈ ℕ` for all real `t` is a homogeneous polynomial of degree `r`;
we record this remark and prove the Taylor-type identity only if time permits. All the
results below need only homogeneity and smoothness.)

* **Euler:** `ω ∈ 𝓗 r k → Dω(x) x = r • ω x` (differentiate `t ↦ ω(t • x)` at `t = 1`).
* `d : 𝓗 (r+1) k → 𝓗 r (k+1)`: from `ω(t•x) = t^{r+1} ω(x)` differentiate in `x`:
  `t • Dω(t•x) = t^{r+1} • Dω(x)`, so `Dω(t•x) = t^r Dω(x)` for `t ≠ 0`, and at `t = 0`
  by continuity of `Dω` (if `r ≥ 1`) or trivially (`r = 0`, `0⁰ = 1`).
  Also `d` kills `𝓗 0 k` (constants: `ω(x) = ω(0·x)·… ` → `ω x = ω 0`… precisely
  `ω (t•x) = ω x` for all `t`, so `ω x = ω 0`).
* `κ : 𝓗 r (k+1) → 𝓗 (r+1) k`.
* **Homotopy formula (Arnold Thm 7.1).** `ω ∈ 𝓗 r k`:
  `(dκ + κd) ω = (r + k) • ω`.
* **Exactness.** If `ω ∈ 𝓗 r (k+1)`, `dω = 0` then `ω = d (κω /(r+k+1))`;
  if `ω ∈ 𝓗 r k`, `κω = 0`, `r + k > 0`, then `ω = κ(dω/(r+k))`.
* **Direct sum.** `𝓗 r k ∩ (𝓗 (r+1) k ⊕ κ…)`: we need `𝓗 r k = d-closed ⊕ κ-closed` only
  in the form: `ω = (dκω + κdω)/(r+k)` for `r + k > 0`.
* **Independence of degrees.** If `Σ_{j ≤ r} ω_j = 0` with `ω_j ∈ 𝓗 j k` then all
  `ω_j = 0`. (Evaluate at `t • x`: a polynomial in `t` with vector coefficients
  vanishing identically; apply an arbitrary continuous linear functional and use
  `Polynomial` root counting, or induct using the Euler operator.)

## D.3 `Polynomial.lean` (Arnold §7.1–7.3)

* `𝓟 r k := ⨆ j ≤ r, 𝓗 j k` (`polyForms`), as submodules of `E → E [⋀^Fin k]→L[ℝ] ℝ`.
* `𝓟⁻ r k := 𝓟 (r−1) k ⊔ κ (𝓗 (r−1) (k+1))` for `r ≥ 1` (`polyFormsMinus`); Whitney forms
  are `𝓟⁻ 1 k`.
* `d (𝓟 (r+1) k) ≤ 𝓟 r (k+1)`, `κ (𝓟 r (k+1)) ≤ 𝓟 (r+1) k`.
* `𝓟 r k ≤ 𝓟⁻ (r+1) k ≤ 𝓟 (r+1) k`.
* `d (𝓟⁻ (r+1) k) ≤ 𝓟 r (k+1)`.
* **Exactness of the polynomial de Rham complex (Arnold Thm 7.2/Cor.).** If
  `ω ∈ 𝓟 r (k+1)` and `dω = 0`, then `ω = dη` for some `η ∈ 𝓟⁻ (r+1) k`.
  (Componentwise: `dω = 0` ⇒ each `dω_j = 0` by independence of degrees, then
  `η = Σ κω_j/(j+k+1)`.)
* **Closed forms in 𝓟⁻ (Arnold Thm 7.?):** if `ω ∈ 𝓟⁻ (r+1) k` and `dω = 0` then
  `ω ∈ 𝓟 r k`. (Write `ω = α + κβ`, `β ∈ 𝓗 r (k+1)`; top-degree part of `dω = 0` is
  `dκβ = 0`; then `0 = κdκβ = (r+k+1) κβ` using the homotopy formula and `κκ = 0`.)

These give the two families of exact polynomial subcomplexes
`𝓟ᵣΛ⁰ → 𝓟ᵣ₋₁Λ¹ → …` and `𝓟ᵣ⁻Λ⁰ → 𝓟ᵣ⁻Λ¹ → …` that FEEC is built on.

## C.1 `Covector.lean`

Fix `E = EuclideanSpace ℝ (Fin n)` (or a general `E` with a chosen orthonormal basis
`e`; the inner product below is basis independent but we do not need that).

`Covector n k` : a type synonym (one-field structure or `def`) for
`E [⋀^Fin k]→L[ℝ] ℝ` equipped with

  ⟪α, β⟫ := (1/k!) Σ_{I : Fin k → Fin n} α(e_I) β(e_I)     ( = Σ_{I increasing} α(e_I)β(e_I) ).

* `InnerProductSpace ℝ (Covector n k)` via `InnerProductSpace.Core`; definiteness by
  `Basis.ext_multilinear` (a multilinear map vanishing on all basis tuples is zero).
* Continuous linear equivalence with the operator-normed `E [⋀^Fin k]→L[ℝ] ℝ`
  (both directions bounded explicitly, or by finite-dimensionality), so that smoothness
  and measurability transfer.
* **Adjointness of wedge and contraction, in the form we need:**
  for `α : Covector n k`, `β : Covector n (k+1)` and the alternating-sum operator
  `(ε_i α)(v₀..v_k) := Σⱼ (−1)ʲ ⟨e_i, vⱼ⟩ α(v₀..v̂ⱼ..v_k)`,
  `⟪ε_i α, β⟫ = ⟪α, β.curryLeft e_i⟫`. Only needed for C.4 (`Classical.lean`).

## C.2 `Codifferential.lean`

* `codiff φ x := − Σ_i ((fderiv ℝ φ x) (e_i)).curryLeft (e_i)` for a `(k+1)`-form `φ`
  (formal adjoint `δ` of `d`).
* `codiff_codiff : ContDiff ℝ 2 φ → δ (δ φ) = 0`.
  *Proof.* `δδφ = Σ_{i,j} ι_{e_i} ι_{e_j} ∂_i ∂_j φ`; the second derivative is symmetric
  (`second_derivative_symmetric`/`ContDiffAt.isSymmSndFDerivAt`), and
  `ι_{e_i} ι_{e_j} = − ι_{e_j} ι_{e_i}` (alternation), so the double sum equals its own
  negative. ∎
* Test forms: `IsTestForm Ω φ := ContDiff ℝ ⊤ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ω`.
  `δ` preserves test forms. A test form defines an element `φ.toLp` of
  `L²(Ω; Covector n k)`.

## C.3 `L2Complex.lean` (Arnold §6.2)

For `Ω ⊆ E` open, `μ := volume.restrict Ω`:

* `L2Form Ω k := Lp (Covector n k) 2 μ`.
* `HasWeakExtDeriv ω η` for `ω : L2Form Ω k`, `η : L2Form Ω (k+1)`:
  `∀ φ` test `(k+1)`-form, `⟪η, φ.toLp⟫ = ⟪ω, (δφ).toLp⟫`.
* `HΛ Ω k` : the submodule of `WithLp 2 (L2Form Ω k × L2Form Ω (k+1))` of pairs with
  `HasWeakExtDeriv`. It is closed (the condition is an intersection of kernels of
  continuous functionals), hence a Hilbert space.
* **Uniqueness of weak derivative** (`ι = fst` injective): if `(0, η) ∈ HΛ` then
  `⟪η, φ⟫ = 0` for all test `φ`; taking `φ = g • c` with `g` a scalar test function and
  `c` a constant covector, `∫ g ⟪η, c⟫ = 0`, so `⟪η(x), c⟫ = 0` a.e. by Mathlib's
  `ae_eq_zero_of_integral_contDiff_smul_eq_zero`, for each `c` in a basis; hence `η = 0`.
* `d : HΛ Ω k →L HΛ Ω (k+1)`, `(ω, η) ↦ (η, 0)`. Well defined: for a test `(k+2)`-form
  `ψ`, `⟪η, (δψ).toLp⟫ = ⟪ω, (δδψ).toLp⟫ = 0` because `δψ` is a test form and `δδψ = 0`.
* `d ∘ d = 0` is immediate, and `‖(ω,η)‖² = ‖ω‖² + ‖η‖²` is the `WithLp 2` product norm.
* **`deRhamComplex Ω : HilbertComplex (L2Form Ω) (HΛ Ω)`.**

Then Parts A and B specialise: *for any open `Ω` on which the L² de Rham complex has
closed range* (true for bounded Lipschitz domains — not proved here), the Hodge Laplace
problem on `HΛᵏ(Ω)` is well posed, and any subcomplex `V_h ⊂ HΛ(Ω)` admitting bounded
cochain projections gives a stable, quasi-optimal mixed method.

## C.4 `Classical.lean` (stretch)

* Pointwise identity for a `C¹` `k`-form `ω` and `C¹` `(k+1)`-form `φ`:
  `⟪dω(x), φ(x)⟫ = Σ_i ⟪∂_i ω(x), φ(x).curryLeft e_i⟫`.
  (From C.1 adjointness, or directly from the all-tuples definition of the inner product:
  moving the `j`-th index to the front costs `(−1)ʲ`, and the `k+1` positions give the
  factor that converts `1/(k+1)!` into `1/k!`.)
* Integration by parts on `E` against compactly supported `φ`
  (`integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable`) gives:
  a smooth `ω` with `ω, dω ∈ L²(Ω)` satisfies `HasWeakExtDeriv [ω] [dω]`.
* Corollary: on bounded `Ω`, polynomial forms (Part D) define elements of `HΛ(Ω)` and
  the weak `d` agrees with `extDeriv` — so `𝓟ᵣΛ` and `𝓟ᵣ⁻Λ` on a single element are
  finite-dimensional subcomplexes of the L² de Rham complex.

## Order of work

D.1 → D.2 → D.3 are independent of everything else and are done in parallel with
Part A. C.1 → C.2 → C.3 come after Part A's `Complex.lean`. C.4 last.
