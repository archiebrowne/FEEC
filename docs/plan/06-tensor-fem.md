# Part G — An unconditional finite element theorem on a box in any dimension

## Goal

`Ω = box e a b ⊂ E` (`dim E = n` arbitrary), a tensor-product mesh with `N i` equal cells in
direction `i` (the `N i` are independent, so anisotropic meshes are allowed). Discrete spaces:
the tensor-product Whitney forms `Q₁⁻Λᵏ` — in degree `k`, the span of
`(∏ᵢ gᵢ(xᵢ)) dx_T`, where `gᵢ` is a cell indicator for the directions `i` occurring in `T` and a
hat function for the others. (`k = 0`: continuous multilinears; `k = n-1`: lowest order
Raviart–Thomas on boxes; `k = n`: piecewise constants.)

**Theorem.** There is `C` depending only on `Ω` and `k` — not on the mesh — such that for every
mesh and every `f ∈ L²Λᵏ⁺¹(Ω)` the Galerkin problem for the Hodge Laplacian is uniquely
solvable, stable with constant `C`, and
`‖σ-σh‖ + ‖u-uh‖ + ‖p-ph‖ ≤ C · inf_{τ,v} (‖σ-τ‖ + ‖u-v‖)`.
No hypothesis: closedness is Part F, and the bounded cochain projection is constructed here.

## G.1 Abstract: cochain projections from dual systems (`Discrete/DualSystem.lean`)

For a Hilbert complex `(W, V, d, ι)`, families `Λ k j ∈ V k`, `Ψ k j ∈ W k` (`j` in a finite
type) and scalars `c k`, put `P k u = c k • ∑ⱼ ⟪Ψ k j, ι u⟫ • Λ k j`. Assume

1. `P k (Λ k j) = Λ k j`;
2. `⟪Ψ k j, ι (P k u)⟫ = ⟪Ψ k j, ι u⟫`;
3. `d (Λ k j) ∈ span (Λ (k+1))`;
4. `⟪Ψ (k+1) j, ι (d u)⟫ = ∑ₗ γₗ ⟪Ψ k l, ι u⟫` for some `γ` (i.e. "`δΨ ∈ span Ψ`").

Then `span (Λ k)` is a subcomplex and `P` is a cochain projection onto it.
*Proof of commutation.* By 4, `P (d u)` depends on `u` only through the numbers `⟪Ψ k l, ι u⟫`,
which by 2 are the same for `u` and `P u`; so `P (d u) = P (d (P u)) = d (P u)`, the last
because `d (P u) ∈ span Λ (k+1)` by 3 and `P` fixes that span by 1. ∎
Bound: `‖P k‖ ≤ max (K k) (K (k+1))` if the `W`-operators `w ↦ c k • ∑ⱼ ⟪Ψ k j, w⟫ • ι (Λ k j)`
are bounded by `K k`.

## G.2 Covector algebra (`DeRham/BasisCovector.lean`)

Adjointness `⟪e♭ ∧ α, β⟫ = ⟪α, e ⌟ β⟫`; `dxT T = e_{T 0}♭ ∧ (e_{T 1}♭ ∧ ⋯)` for any tuple
`T : Fin k → Fin n` (no sorting, no determinants). By induction with adjointness and
anticommutation: `e_i♭ ∧ dxT T = 0` if `i ∈ range T`; `e_i ⌟ dxT T = 0` if `i ∉ range T`;
`⟪dxT S, dxT T⟫ = 0` unless `range S = range T`; resolution of the identity
`α = (k!)⁻¹ ∑_T ⟪α, dxT T⟫ dxT T`; `‖dxT T‖ ≤ 1`. Using all tuples with the factor `(k!)⁻¹`
replaces a choice of increasing multi-indices.

## G.3 One dimension (`Tensor/Ref1D*.lean`)

Uniform grid on `(a,b)`, `h = (b-a)/N`, nodes `0..N`, cells `1..N`.
Shape functions: hats `λⱼ`, cell indicators `χ_c`. Dual functions, smooth with compact support
in `(a,b)`: `ψⱼ` = a rescaled fixed `ρ ∈ C_c^∞(0,1)` with `∫ρ = 1`, `∫tρ = 0`, placed in a cell
adjacent to node `j`; `Ψ_c(x) = ∫_{-∞}^x (ψ_{c-1} - ψ_c)/h`.
Facts: biorthogonality `∫λᵢψⱼ = δᵢⱼ`, `∫χ_cΨ_{c'} = δ_{cc'}`; `λⱼ' = (χⱼ - χ_{j+1})/h`;
`Ψ_c' = (ψ_{c-1} - ψ_c)/h`; Schur sums `∑ⱼ |gⱼ(x)| ‖ψⱼ‖_{L¹} ≤ K`, `∑ⱼ ‖gⱼ‖_{L¹} |ψⱼ(y)| ≤ K`
with `K` an absolute constant.

## G.4 Analysis on the box

* `Tensor/BoxIntegral.lean`: `∫_Ω ∏ᵢ fᵢ(⟪eᵢ,x⟫) = ∏ᵢ ∫_{aᵢ}^{bᵢ} fᵢ`.
* `Tensor/WeakDeriv.lean`: integration by parts along a direction for Lipschitz piecewise
  `C¹` functions; hence `(∏ᵢ uᵢ(xᵢ)) α` has weak exterior derivative
  `∑ᵢ uᵢ'(xᵢ) ∏_{j≠i} uⱼ(xⱼ) eᵢ♭ ∧ α` provided each `uᵢ` is Lipschitz or `eᵢ♭ ∧ α = 0`.
* `Tensor/Schur.lean`: Schur test for finite-rank operators `ω ↦ ∑ₘ ⟪ω, bₘβ⟫ aₘα` on `L²`.

## G.5 Assembly (`Tensor/Forms.lean`, `Tensor/Projection.lean`, `Tensor/Main.lean`)

`Λ_{T,m} = (∏ᵢ shapeᵢ) dxT T` in `HΛᵏ`, `Ψ_{T,m} = (∏ᵢ dualᵢ) dxT T` test forms, `c k = (k!)⁻¹`.
Hypotheses 1–2 from biorthogonality and the resolution of the identity; 3 from G.4 and
`λ' = (χ - χ)/h`; 4 from `δ(fβ) = -∑ᵢ ∂ᵢf (eᵢ ⌟ β)` and `Ψ' = (ψ - ψ)/h`; the bound from
Schur with product kernels. Then Part B's error estimate with `μ = 0` (no harmonic forms).

## Not included

* Non-uniform or simplicial meshes.
* A convergence *rate*: needs an approximation estimate for the projection (smooth solutions)
  and, for general data, `H²` regularity on a box.
