# Part H — An unconditional O(h) convergence rate on a box in any dimension

## Goal

`Ω = box e a b`, any dimension `n`, any degree `k + 1 ≥ 1`, tensor-product grids as in Part G,
`h = max_i (b_i − a_i)/N_i`. There is `C` (depending on the box and `k` only) such that for
every grid and every **test form** `f` (smooth, compactly supported in `Ω`)

  ‖σ − σh‖ + ‖u − uh‖ + ‖p − ph‖ ≤ C · h · (‖f‖ + ∑ᵢ ‖∂ᵢ f‖)

(norms: `HΛ` on the left, `L²` on the right). No hypothesis. (The bound extends to the
`H¹`-closure of test forms by continuity; not formalised.)

## Route

Part G gives `error ≤ C (‖σ − πσ‖_{HΛ} + ‖u − πu‖_{HΛ})` with `π` the tensor cochain
projection, and `‖w − πw‖_{HΛ} = ‖w − πw‖ + ‖dw − π dw‖` (commutation). So it suffices:

* **(Approx)** `‖w − πw‖_{L²} ≤ C h N(w)` for every `L²` form `w`, where `N(w)` is a Fourier
  `H¹`-seminorm (below);
* **(Reg)** `N(σ)² + N(dσ)² + N(u)² + N(du)² ≤ C (‖f‖² + N(f)²)`;
* **(Data)** `N(f)² ≤ ∑ᵢ ‖∂ᵢ f‖²` for test forms.

Everything is done with *real* cosine/sine series and never with Sobolev spaces.

### H.1 One dimension (`Fourier/Trig1D.lean`)
On `(a, b)`, `ℓ = b − a`: `C_m(t) = cos(π m (t − a)/ℓ)`, `S_m(t) = sin(π m (t − a)/ℓ)`.
Orthogonality; `C_m' = −(πm/ℓ) S_m`, `S_m' = (πm/ℓ) C_m`; product-to-sum formulas
`C_m C_{m'} = (C_{m+m'} + C_{|m−m'|})/2`, `S_1 C_j = (S_{j+1} − S_{j−1})/2`;
`S_1 > 0` inside; `|S_m(t)| ≤ (πm/ℓ) min(t − a, b − t)`.

### H.2 Completeness (`Fourier/TrigDensity.lean`)
For a pattern `s : Fin n → Bool` (sine in directions with `s i`), `trigProd s m x = ∏ᵢ T_{m_i}(⟪eᵢ,x⟫)`.
If `F ∈ L²(Ω)` is orthogonal to all `trigProd s m` then `F = 0`.
*Proof.* `s = false`: cosine products span an algebra (product-to-sum) separating points of the
closed box ⇒ Stone–Weierstrass ⇒ `F ⟂` all smooth compactly supported functions ⇒ `F = 0`.
General `s`: `F · ∏_{s i} S_1` is orthogonal to all cosine products (`S_1 C_j ∈ span S`) and
`S_1 > 0`.

### H.3 Eigenforms (`Fourier/Eigenforms.lean`)
`φ_{T,m} = trigProd (pat T) m • dx_T` (sine exactly in the directions of `T` — the natural
boundary conditions). Orthogonality; completeness in `L²Λᵏ` (H.2 + resolution of the
identity); `d φ_{T,m}` and `δ φ_{T,m}` are combinations of `φ_{·,m}` with coefficients
`ξ_m = −∑ᵢ (π mᵢ/ℓᵢ) eᵢ`: in coefficient form `(dw)^(m) = ξ_m ∧ ŵ(m)`.
Fourier coefficients `ŵ(m) ∈ Covector`, Parseval `‖w‖² = ∑_m ν_m ‖ŵ(m)‖²`.
`N(w)² := ∑_m ν_m |ξ_m|² ‖ŵ(m)‖²`.

### H.4 Integration by parts against eigenforms (`Fourier/IBP.lean`)
For `τ ∈ HΛᵏ(Ω)`: `⟪dτ, φ_{T,m}⟫ = ⟪τ, δφ_{T,m}⟫` although `φ` is not compactly supported.
Cutoff `χ_ε = ∏ θ_ε(⟪eᵢ,x⟫)`; `δ(χφ) = χδφ − ∑ᵢ ∂ᵢχ eᵢ ⌟ φ`; the error term vanishes for
`i ∉ T` (`eᵢ ⌟ dx_T = 0`) and is `O(1)` on a layer of width `ε` for `i ∈ T` (the sine factor
vanishes linearly); dominated convergence.

### H.5 Regularity (`Fourier/Regularity.lean`)
Test the mixed equations with `E_m(α) ∈ HΛ` and use H.4: `σ̂ = ξ ⌟ û`,
`ξ ∧ σ̂ + ξ ⌟ (ξ ∧ û) = f̂` (`p = 0`), so `û = f̂/|ξ|²` (`ξ ∧ ξ⌟ + ξ⌟ ξ∧ = |ξ|²`). With
`|ξ_m| ≥ π/max ℓ` whenever `ŵ(m)` can be nonzero in degree ≥ 1: (Reg).
(Data): coefficients of `∂ᵢF` in the swapped basis are `±(πmᵢ/ℓᵢ) F̂` (IBP, compact support) +
Bessel.

### H.6 Approximation (`Fourier/CoordSchur.lean`, `Tensor/Ref1DApprox.lean`, `Tensor/Approx.lean`)
* 1D: `∑ⱼ shapeⱼ(t) ∫ dualⱼ = 1`; for `C¹` `g`: `g(t) − (Pg)(t) = ∫ r(t,τ) g'(τ) dτ` with
  Schur constants of `r` `≤ K h`.
* Operators acting in one coordinate of the box with a Schur-bounded kernel are bounded on
  `L²(Ω)` (Fubini through `coordEquiv`).
* Telescoping `G − PG = ∑ᵢ P₁⋯P_{i−1} (I − Pᵢ) G` ⇒ `‖G − PG‖ ≤ C h ∑ᵢ ‖∂ᵢ G‖` for smooth `G`;
  forms componentwise; series by passing to the limit of partial sums.

### H.7 Assembly (`Fourier/Rate.lean`).

## Not included
`H¹` data with no boundary condition (Neumann-data regularity), non-uniform grids, eigenvalues.
