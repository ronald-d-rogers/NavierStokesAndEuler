import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Pillar C — the criticality of 3D Navier–Stokes

The Navier–Stokes equation has a scaling symmetry `u_λ(x,t) = λ · u(λx, λ²t)`
(with `p_λ = λ² p`). The *critical* norm is `L^d`: it is exactly the norm that is
scale-invariant. The **energy** is `L²`, and `d = 3` is the first dimension where
`L²` falls *below* the critical `L^d` — a knife's edge (cf. `VISION.md`).

This file records the quantitative form:

* **C2 (critical norm):** the `L^p` integral of a dilation `u(λ·)` scales by
  `λ^{-d}`, so `‖λ·u(λ·)‖_p = λ^{1 - d/p} ‖u‖_p`; the exponent `1 - d/p` vanishes
  exactly at `p = d`.
* **C3 (knife's edge):** for the energy exponent `p = 2`, `1 - d/2` is zero exactly
  at `d = 2` and strictly negative for `d ≥ 3`. So `3` is the first dimension where
  energy falls below criticality.
* **C1 (scaling symmetry):** stated in exponent form — the time derivative, the
  advection `(u·∇)u`, and the Laplacian `Δu` all rescale by `λ³` under
  `u_λ(x,t) = λ·u(λx, λ²t)`, which is exactly why the equation is invariant. (A full
  PDE-level invariance statement is not formalized here; this is the homogeneous
  bookkeeping that underlies it.)
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Criticality

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **C2, step 1 — dilation of the `L^p` integral.** For the Haar measure `volume` on a
finite-dimensional real inner product space `E`, dilating the argument by `c` rescales
the integral of `‖u‖ ^ p` by `|c^{-d}|`, where `d = Module.finrank ℝ E`. This is the
change-of-variables `x ↦ c • x` (the Jacobian is `|c|^d`). -/
theorem integral_norm_comp_smul (u : E → ℝ) (p : ℝ) (c : ℝ) :
    ∫ x, ‖u (c • x)‖ ^ p ∂(volume : Measure E)
      = |(c ^ Module.finrank ℝ E)⁻¹| • ∫ x, ‖u x‖ ^ p ∂(volume : Measure E) := by
  exact MeasureTheory.Measure.integral_comp_smul (μ := volume) (fun x => ‖u x‖ ^ p) c

/-- **C2, step 1' — the same, for a nonnegative dilation.** -/
theorem integral_norm_comp_smul_of_nonneg (u : E → ℝ) (p : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    ∫ x, ‖u (c • x)‖ ^ p ∂(volume : Measure E)
      = (c ^ Module.finrank ℝ E)⁻¹ • ∫ x, ‖u x‖ ^ p ∂(volume : Measure E) := by
  exact MeasureTheory.Measure.integral_comp_smul_of_nonneg (μ := volume) (f := fun x => ‖u x‖ ^ p) (R := c) (hR := hc)

/-- **C2 — the critical exponent.** The scaling exponent `1 - d/p` (for `p > 0`) vanishes
exactly when `p = d`: the `L^d` norm is the unique scale-invariant Lebesgue norm. -/
theorem scaling_exponent_eq_zero_iff {p d : ℝ} (hp : 0 < p) : (1 - d / p = 0) ↔ p = d := by
  constructor
  · intro h
    have hd : d = p := by
      field_simp [hp.ne'] at h
      linarith
    exact hd.symm
  · intro h
    subst h
    field_simp [hp.ne']
    norm_num

/-- **C3 — the knife's edge, lower side.** In dimension `2`, the energy exponent
`1 - d/2` is exactly `0`: `L²` is *at* criticality. -/
theorem energy_critical_in_dim_two : (1 - (2 : ℝ) / 2 = 0) := by norm_num

/-- **C3 — the knife's edge, upper side.** In every dimension `d ≥ 3`, the energy
exponent `1 - d/2` is strictly negative: `L²` is *strictly subcritical*. Hence `3` is
the first dimension where the energy norm falls below the critical scaling. -/
theorem energy_subcritical_of_ge_three {d : ℕ} (hd : 3 ≤ d) : (1 - (d : ℝ) / 2 < 0) := by
  have hd' : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  nlinarith

/-- **C1 — Navier–Stokes scaling symmetry, exponent form.** Under
`u_λ(x, t) = λ · u(λ x, λ² t)` (and `p_λ = λ² p`), the three terms of the equation
`∂ₜu + (u·∇)u = −∇p + νΔu` all rescale by the *same* power `λ³`:

* time derivative: `λ` (prefactor) `+ 2` (from `t ↦ λ² t`) `= 3`;
* advection `(u·∇)u`: `1 + 1 + 1 = 3` (two `u` factors and one `∇ₓ = λ∇`);
* Laplacian `Δu`: `1` (prefactor) `+ 2` (`Δₓ = λ² Δ`) `= 3`.

This common degree `3` is exactly the statement that the equation is scale-invariant. -/
theorem ns_scaling_homogeneous_degree :
    (1 + 2 : ℝ) = 3 ∧ (1 + 1 + 1 : ℝ) = 3 ∧ (1 + 2 : ℝ) = 3 := by
  norm_num

end Criticality

#print axioms Criticality.integral_norm_comp_smul
#print axioms Criticality.integral_norm_comp_smul_of_nonneg
#print axioms Criticality.scaling_exponent_eq_zero_iff
#print axioms Criticality.energy_critical_in_dim_two
#print axioms Criticality.energy_subcritical_of_ge_three
#print axioms Criticality.ns_scaling_homogeneous_degree
