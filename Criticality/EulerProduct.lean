import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

/-!
# Pillar E — the additive↔multiplicative bridge (number theory)

The number-theory avatar of the additive/multiplicative tension that the rest of
the skeleton tracks in Fourier space:

- the **Dirichlet series** `ζ(s) = Σₙ n⁻ˢ` sums *additively* over integers;
- the **Euler product** `ζ(s) = ∏ₚ (1 − p⁻ˢ)⁻¹` factors *multiplicatively* over
  primes.

This file is pure re-exposure and commentary: the theorem is already in mathlib
(`riemannZeta_eulerProduct` in `Mathlib/NumberTheory/EulerProduct/DirichletLSeries.lean`).
We re-state it in the `Criticality` namespace so the capstone's dependency graph
has a concrete node to point at.
-/

noncomputable section

open Filter Nat
open scoped Topology

namespace Criticality

/-- **The Euler product for the Riemann ζ function** (valid for `s.re > 1`), in
`HasProd` form. This is the multiplicative factorization of the additive Dirichlet
series: `ζ(s) = ∏_{p prime} (1 − p⁻ˢ)⁻¹`. Re-exposed from mathlib. -/
theorem eulerProduct_hasProd (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes ↦ (1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹) (riemannZeta s) :=
  riemannZeta_eulerProduct_hasProd hs

/-- The same Euler product, stated as an infinite product (`tprod`). -/
theorem eulerProduct_tprod (s : ℂ) (hs : 1 < s.re) :
    (∏' p : Nat.Primes, (1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹) = riemannZeta s :=
  riemannZeta_eulerProduct_tprod hs

/-- The same Euler product, stated as convergence of finite partial products over
`primesBelow n`. -/
theorem eulerProduct (s : ℂ) (hs : 1 < s.re) :
    Tendsto (fun n : ℕ ↦ ∏ p ∈ primesBelow n, (1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹) atTop
      (𝓝 (riemannZeta s)) :=
  riemannZeta_eulerProduct hs

end Criticality

#print axioms Criticality.eulerProduct_hasProd
#print axioms Criticality.eulerProduct_tprod
#print axioms Criticality.eulerProduct
