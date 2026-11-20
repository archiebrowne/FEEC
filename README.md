# FEEC

A Lean 4 / Mathlib formalisation of the main results of finite element exterior
calculus, following D. N. Arnold, *Finite Element Exterior Calculus* (SIAM, 2018).

## What FEEC is

Finite element exterior calculus explains why some finite element methods for PDEs are
stable and convergent and others fail. It recasts problems such as the Hodge Laplacian,
mixed Poisson, Maxwell and elasticity as problems on a Hilbert complex, with the de Rham
complex as the main example. A discretisation is then stable exactly when its finite
element spaces form a subcomplex and there is a bounded projection onto them that commutes
with `d`. That one criterion yields well-posedness, quasi-optimal error estimates, correct
discrete harmonic forms and, for eigenvalue problems, the absence of spurious modes.

## Main theorem

[`FEEC.Fourier.box_tensor_rate`](FEEC/Fourier/Rate.lean) is an unconditional `O(h)`
convergence theorem for a finite element method in any dimension. Let `Ω` be a box in
ℝⁿ, for any `n`, and fix a form degree `k + 1`. There is a constant `C`, depending only on
`Ω` and `k`, with the following property. For every tensor-product grid with cell sizes at
most `h`, and every smooth form `f` compactly supported in `Ω`, solve the Hodge Laplace
problem `(σ, u, p)` exactly and by the Galerkin method `(σh, uh, ph)` in the
tensor-product Whitney spaces. Then

```
‖σ − σh‖ + ‖u − uh‖ + ‖p − ph‖ ≤ C · h · (‖f‖ + Σᵢ ‖∂ᵢ f‖)
```

where the left-hand side is measured in the full `HΛ` (graph) norms. The Whitney spaces are:
- degree 0: continuous piecewise multilinears;
- degree `n − 1`: lowest-order Raviart–Thomas elements;
- degree `n`: piecewise constants.

No hypothesis is assumed. The two conditions that the abstract theory takes as input are
proved for the box:
- **Closedness of the de Rham complex:** an `L²` Poincaré lemma on boxes.
- **A bounded commuting projection:** constructed from tensor products of one-dimensional
  shape and dual functions.

Regularity of the solution is proved by expanding in cosine/sine eigenforms.

## What else is proved

- **Abstract Hilbert complexes** (Arnold Ch. 4): Hodge decomposition, the Poincaré
  inequality, and well-posedness of the mixed Hodge Laplacian.
- **Approximation of complexes** (Arnold Ch. 5): discrete Poincaré inequality, the gap
  between harmonic forms, uniform stability, and the quasi-optimal error estimate.
- **The de Rham complex** (Arnold Ch. 6–7): the `L²` de Rham complex on domains in ℝⁿ,
  the Koszul operator, and polynomial forms with exact polynomial complexes.
- **Intervals:** an unconditional `O(h)` theorem
  ([`interval_mixed_convergence`](FEEC/Interval/Convergence.lean)).
- **Boxes:** mesh-independent stability and quasi-optimality
  ([`box_tensor_galerkin`](FEEC/Tensor/Main.lean)).

## Not covered

- Simplicial meshes, general (Lipschitz) domains, higher polynomial degree, and eigenvalue
  convergence. On those domains and meshes, closedness and the bounded commuting projection
  remain hypotheses of the general theorems.
- Data that is merely `H¹`, rather than smooth and compactly supported, for the rate.

See `docs/plan/` for the informal plans and `STATUS.md` for a file-by-file account.
