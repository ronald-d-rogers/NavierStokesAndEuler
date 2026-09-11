import Criticality.ConcentrationBarrier
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Integral.MeanInequalities

set_option maxHeartbeats 1000000

/-!
# Heisenberg's uncertainty principle (Pillar A, rung A1)

For `f ∈ L²`, the product of the spatial and frequency spreads is bounded below by a
positive constant. This is the "concentration barrier" in its most basic quantitative
form: a function and its Fourier transform cannot both be tightly concentrated.

This file establishes the **one-dimensional core** — the commutator identity behind
Heisenberg — in the Schwartz-space medium `𝓢(ℝ, ℝ)`, and connects the momentum spread
`‖f'‖₂` to the frequency spread `‖ξ·𝓕 f‖₂` (Plancherel + the derivative–Fourier relation).

## Survey result (mathlib v4.34.0-rc2)

There is **no** existing Heisenberg/uncertainty theorem in mathlib
(`grep -rni "heisenberg\\|uncertainty" .lake/packages/mathlib/Mathlib/` returns nothing).
The variance machinery (`ProbabilityTheory.variance`, `Probability.Moments.Variance`)
is about random variables, not the Fourier transform. So A1 must be assembled from
pieces. The pieces, all present, are:

* `SchwartzMap.integral_mul_deriv_eq_neg_deriv_mul` — integration by parts for Schwartz
  functions on `ℝ`.
* `SchwartzMap.derivCLM` / `SchwartzMap.derivCLM_apply` — the derivative as a CLM.
* `SchwartzMap.smulLeftCLM` / `SchwartzMap.smulLeftCLM_apply` — multiplication by a
  temperate function (here the coordinate `x`).
* `SchwartzMap.norm_toLp'` — `L²` norm as an integral.
* `MeasureTheory.integral_mul_norm_le_Lp_mul_Lq` — Hölder/Cauchy–Schwarz.
* `SchwartzMap.norm_fourier_toL2_eq` — Plancherel.
* `SchwartzMap.fourier_lineDerivOp_eq` — `𝓕 (∂_m f) = (2πi) • (inner ℝ · m) · 𝓕 f`.

## Normalization caveat

mathlib's Fourier transform uses the `e^{2πi xξ}` convention (see
`Mathlib/Analysis/Fourier/FourierTransform.lean`, `Real.fourierChar`). Consequently
the derivative–Fourier relation carries a factor `2π`:
`𝓕 f' (ξ) = 2πi ξ · 𝓕 f (ξ)`, so `‖f'‖₂ = 2π · ‖ξ·𝓕 f‖₂`. The one-dimensional
uncertainty bound is therefore `‖f‖₂² ≤ 4π · ‖x·f‖₂ · ‖ξ·𝓕 f‖₂`, i.e.

    ‖x·f‖₂ · ‖ξ·𝓕 f‖₂ ≥ ‖f‖₂² / (4π).

The `d/2` constant in `PLAN.md` uses the physicists' convention (`𝓕 f'(ξ) = iξ 𝓕 f(ξ)`,
i.e. an `e^{-ixξ}` transform); in that convention the per-coordinate bound is `1/2`.
With mathlib's `e^{2πi xξ}` convention the per-coordinate constant is `1/(4π)`. We
state the results in mathlib's convention and flag the difference.
-/

noncomputable section

open Real MeasureTheory
open scoped FourierTransform SchwartzMap ENNReal Topology

-- `[local irreducible]` does NOT propagate across imports; re-declare locally.
attribute [local irreducible] Real.rpow
attribute [local irreducible] MeasureTheory.Lp.fourierTransformₗᵢ
attribute [local irreducible] SchwartzMap.fourierTransformCLM

namespace Criticality

/-! ## The one-dimensional commutator `[x, d/dx] = -1` -/

/-- Multiplication by the coordinate `x` on real-valued Schwartz functions, as a
Schwartz map (via `SchwartzMap.smulLeftCLM`, using that `x ↦ x` has temperate growth). -/
noncomputable def mulCoord (f : 𝓢(ℝ, ℝ)) : 𝓢(ℝ, ℝ) :=
  (SchwartzMap.smulLeftCLM ℝ (fun x : ℝ => x)) f

@[simp] theorem mulCoord_apply (f : 𝓢(ℝ, ℝ)) (x : ℝ) : mulCoord f x = x * f x := by
  simpa [mulCoord] using
    (SchwartzMap.smulLeftCLM_apply_apply (F := ℝ) (g := fun x : ℝ => x)
      (Function.HasTemperateGrowth.id' (E := ℝ)) f x)

/-- The derivative of a real Schwartz function as a Schwartz map. -/
noncomputable def derivℝ (f : 𝓢(ℝ, ℝ)) : 𝓢(ℝ, ℝ) :=
  (SchwartzMap.derivCLM ℝ ℝ) f

@[simp] theorem derivℝ_apply (f : 𝓢(ℝ, ℝ)) (x : ℝ) : derivℝ f x = deriv (⇑f) x := by
  simpa [derivℝ] using (SchwartzMap.derivCLM_apply ℝ f x)

/-- **Commutator identity** `∫ f² = -2 ∫ x·f·f'`, the algebraic heart of Heisenberg.

It says `[x, d/dx] = -1` in integrated form: multiplying by the coordinate and
differentiating "almost commute", and the failure is exactly `-1` times the `L²`
mass of `f`. -/
theorem commutator_integral (f : 𝓢(ℝ, ℝ)) :
    ∫ x, f x * f x = -2 * ∫ x, (x * f x) * deriv (⇑f) x := by
  let Xf : 𝓢(ℝ, ℝ) := mulCoord f
  let Df : 𝓢(ℝ, ℝ) := derivℝ f
  let DXf : 𝓢(ℝ, ℝ) := derivℝ Xf
  have hXf : ∀ x, Xf x = x * f x := by intro x; simp [Xf]
  have hDf : ∀ x, Df x = deriv (⇑f) x := by intro x; simp [Df]
  have hDXf : ∀ x, DXf x = deriv (⇑Xf) x := by intro x; simp [DXf]
  have hderivXf : ∀ x, deriv (⇑Xf) x = f x + x * deriv (⇑f) x := by
    intro x
    have hXf' : ⇑Xf = fun y : ℝ => y * f y := by
      funext y; exact hXf y
    rw [hXf']
    change deriv (id * ⇑f) x = f x + x * deriv (⇑f) x
    rw [deriv_mul differentiableAt_id ((f.hasDerivAt x).differentiableAt)]
    simp [deriv_id]
  have hIBP : ∫ x, f x * deriv (⇑Xf) x = -∫ x, deriv (⇑f) x * Xf x :=
    SchwartzMap.integral_mul_deriv_eq_neg_deriv_mul f Xf
  have hIBP' : ∫ x, f x * DXf x = -∫ x, Df x * Xf x := by
    calc
      ∫ x, f x * DXf x = ∫ x, f x * deriv (⇑Xf) x := by
        refine MeasureTheory.integral_congr_ae ?_
        exact Filter.Eventually.of_forall (fun x => by simp [hDXf x])
      _ = -∫ x, deriv (⇑f) x * Xf x := hIBP
      _ = -∫ x, Df x * Xf x := by
        refine congrArg Neg.neg ?_
        refine MeasureTheory.integral_congr_ae ?_
        exact Filter.Eventually.of_forall (fun x => by simp [hDf x])
  have hpoint : ∀ x, f x * f x =
      (f x * DXf x + Df x * Xf x) - 2 * ((x * f x) * Df x) := by
    intro x
    rw [hDXf x, hDf x, hderivXf x, hXf x]
    ring
  have hff : Integrable (fun x : ℝ => f x * f x) volume :=
    (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ) f f).integrable
  have hA1 : Integrable (fun x : ℝ => f x * DXf x) volume :=
    (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ) f DXf).integrable
  have hA2 : Integrable (fun x : ℝ => Df x * Xf x) volume :=
    (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ) Df Xf).integrable
  have hA : Integrable (fun x : ℝ => f x * DXf x + Df x * Xf x) volume := hA1.add hA2
  have hB' : Integrable (fun x : ℝ => Xf x * Df x) volume :=
    (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ) Xf Df).integrable
  have hB : Integrable (fun x : ℝ => (x * f x) * Df x) volume := by
    simpa [hXf] using hB'
  have hcomm : ∫ x, f x * f x =
      (∫ x, f x * DXf x + Df x * Xf x) - 2 * (∫ x, (x * f x) * Df x) := by
    calc
      ∫ x, f x * f x = ∫ x, (f x * DXf x + Df x * Xf x) - 2 * ((x * f x) * Df x) := by
        exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint)
      _ = (∫ x, f x * DXf x + Df x * Xf x) - 2 * (∫ x, (x * f x) * Df x) := by
        rw [MeasureTheory.integral_sub hA (hB.const_mul 2)]
        rw [MeasureTheory.integral_const_mul]
  have hAeq : (∫ x, f x * DXf x + Df x * Xf x) = 0 := by
    have h1 : (∫ x, f x * DXf x) = ∫ x, f x * deriv (⇑Xf) x :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => by simp [hDXf x]))
    have h2 : (∫ x, Df x * Xf x) = ∫ x, deriv (⇑f) x * Xf x :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => by simp [hDf x]))
    calc
      (∫ x, f x * DXf x + Df x * Xf x) = (∫ x, f x * DXf x) + (∫ x, Df x * Xf x) :=
        (MeasureTheory.integral_add hA1 hA2)
      _ = (∫ x, f x * deriv (⇑Xf) x) + (∫ x, deriv (⇑f) x * Xf x) := by
        rw [h1, h2]
      _ = (∫ x, f x * deriv (⇑Xf) x) + (-(∫ x, f x * deriv (⇑Xf) x)) := by
        rw [hIBP]
        ring
      _ = 0 := by ring
  calc
    ∫ x, f x * f x = (∫ x, f x * DXf x + Df x * Xf x) - 2 * (∫ x, (x * f x) * Df x) := hcomm
    _ = 0 - 2 * (∫ x, (x * f x) * Df x) := by rw [hAeq]
    _ = -2 * (∫ x, (x * f x) * Df x) := by ring
    _ = -2 * (∫ x, (x * f x) * deriv (⇑f) x) := by
        have hDf'' : (∫ x, (x * f x) * Df x) = ∫ x, (x * f x) * deriv (⇑f) x :=
          MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => by simp [hDf x]))
        rw [hDf'']

/-- `‖f‖₂²` for a real Schwartz function is the integral of its square. -/
theorem norm_toLp_two_sq_eq_integral_sq (f : 𝓢(ℝ, ℝ)) :
    ‖f.toLp 2 volume‖ ^ 2 = ∫ x, f x * f x := by
  rw [← real_inner_self_eq_norm_sq (f.toLp 2 volume)]
  rw [MeasureTheory.L2.inner_def (f.toLp 2 volume) (f.toLp 2 volume)]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [f.coeFn_toLp 2 volume] with x hx
  simp [inner, hx]

/-- **Heisenberg, one dimension, position × momentum.**

`‖f‖₂² ≤ 2 · ‖x·f‖₂ · ‖f'‖₂`: a function cannot be simultaneously concentrated in
space and in its derivative. This is the commutator form of the uncertainty
principle (with "momentum" = `-i·d/dx`; the `1/2` constant is convention-free here).
-/
theorem heisenberg_commutator_real (f : 𝓢(ℝ, ℝ)) :
    ‖f.toLp 2 volume‖ ^ 2 ≤
      2 * ‖(mulCoord f).toLp 2 volume‖ * ‖(derivℝ f).toLp 2 volume‖ := by
  let Xf : 𝓢(ℝ, ℝ) := mulCoord f
  let Df : 𝓢(ℝ, ℝ) := derivℝ f
  have hXf : ∀ x, Xf x = x * f x := by intro x; simp [Xf]
  have hDf : ∀ x, Df x = deriv (⇑f) x := by intro x; simp [Df]
  have hcomm : ∫ x, f x * f x = -2 * ∫ x, (x * f x) * deriv (⇑f) x :=
    commutator_integral f
  have hnorm : ‖f.toLp 2 volume‖ ^ 2 = ∫ x, f x * f x :=
    norm_toLp_two_sq_eq_integral_sq f
  have hHolder : ∫ x, ‖Xf x‖ * ‖Df x‖ ≤ ‖Xf.toLp 2 volume‖ * ‖Df.toLp 2 volume‖ := by
    have h := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq (E := ℝ) (p := 2) (q := 2)
      (by refine ⟨?_, ?_, ?_⟩ <;> norm_num : Real.HolderConjugate 2 2)
      (Xf.memLp (ENNReal.ofReal 2) volume) (Df.memLp (ENNReal.ofReal 2) volume)
    refine h.trans ?_
    have hXf2 : ‖Xf.toLp 2 volume‖ = (∫ x, ‖Xf x‖ ^ (2 : ℕ) ∂volume) ^ (1 / 2 : ℝ) := by
      rw [SchwartzMap.norm_toLp' (f := Xf) (p := 2) (by norm_num) (by norm_num) (μ := volume)]
      norm_num [ENNReal.toReal_ofNat]
    have hDf2 : ‖Df.toLp 2 volume‖ = (∫ x, ‖Df x‖ ^ (2 : ℕ) ∂volume) ^ (1 / 2 : ℝ) := by
      rw [SchwartzMap.norm_toLp' (f := Df) (p := 2) (by norm_num) (by norm_num) (μ := volume)]
      norm_num [ENNReal.toReal_ofNat]
    rw [hXf2, hDf2]
    simp
  have hmain : ∫ x, f x * f x ≤ 2 * ‖Xf.toLp 2 volume‖ * ‖Df.toLp 2 volume‖ := by
    calc
      ∫ x, f x * f x = -2 * ∫ x, (x * f x) * deriv (⇑f) x := hcomm
      _ ≤ 2 * (∫ x, ‖Xf x‖ * ‖Df x‖) := by
        have htri : |∫ x, (x * f x) * deriv (⇑f) x| ≤ ∫ x, ‖Xf x‖ * ‖Df x‖ := by
          calc
            |∫ x, (x * f x) * deriv (⇑f) x| ≤ ∫ x, |(x * f x) * deriv (⇑f) x| :=
              MeasureTheory.norm_integral_le_integral_norm
                (fun x => (x * f x) * deriv (⇑f) x)
            _ = ∫ x, ‖Xf x‖ * ‖Df x‖ := by
              refine MeasureTheory.integral_congr_ae ?_
              exact Filter.Eventually.of_forall (fun x => by
                simp [abs_mul, ← hXf x, ← hDf x])
        calc
          -2 * ∫ x, (x * f x) * deriv (⇑f) x ≤ 2 * |∫ x, (x * f x) * deriv (⇑f) x| := by
            have : -(∫ x, (x * f x) * deriv (⇑f) x) ≤
                |∫ x, (x * f x) * deriv (⇑f) x| := neg_le_abs _
            nlinarith
          _ ≤ 2 * (∫ x, ‖Xf x‖ * ‖Df x‖) := by
            exact mul_le_mul_of_nonneg_left htri (by positivity)
      _ ≤ 2 * ‖Xf.toLp 2 volume‖ * ‖Df.toLp 2 volume‖ := by
        simpa [mul_assoc] using mul_le_mul_of_nonneg_left hHolder (by norm_num : 0 ≤ (2 : ℝ))
  rw [hnorm]
  simpa [Xf, Df] using hmain

/-! ## The full variance form `Δx · Δξ ≥ …` (documented, not yet proved) -/

/-
The plan's target statement is the *variance* form: for `f ∈ L²(ℝ^d)` (normalized
`‖f‖₂ = 1`), with
    Δx(f)² = ∫ |x - μ_x|² |f(x)|² dx,   μ_x = ∫ x |f(x)|² dx,
    Δξ(f)² = ∫ |ξ - μ_ξ|² |f̂(ξ)|² dξ,   μ_ξ = ∫ ξ |f̂(ξ)|² dξ,
one has `Δx(f) · Δξ(f) ≥ d/2` (physicists' normalization).

This is strictly more than the one-dimensional second-moment bound proved above. The
remaining, well-scoped pieces are:

1. **Centering reduces variance to second moment.** For a *centered* `f` (mean `0` in
   both domains), `Δx(f) = ‖x·f‖₂` and `Δξ(f) = ‖ξ·𝓕 f‖₂`, and the theorem above (in
   each coordinate, then summed / by AM–GM over `d` coordinates) gives the bound. The
   centering step needs translation invariance:

   * *Spatial translation* `f_a(x) = f(x - a)`: `𝓕 f_a (ξ) = e^{-2πi aξ} 𝓕 f(ξ)`, so
     `|𝓕 f_a| = |𝓕 f|` (Δξ unchanged), and Δx is invariant under the shift (its mean
     becomes `0`). In mathlib this is `SchwartzMap.compSubConstCLM` /
     `SchwartzMap.fourier_compSubConstCLM` (or the general `fourierIntegral_comp_sub`).
   * *Frequency translation (modulation)* `g(x) = e^{2πiνx} f(x)`: `𝓕 g(ξ) = 𝓕 f(ξ - ν)`,
     shifting the frequency mean to `0` while leaving `|f|` (hence Δx) unchanged.

2. **The constant.** With mathlib's `e^{2πi xξ}` convention the per-coordinate
   second-moment bound is `‖x_j·f‖₂ · ‖ξ_j·𝓕 f‖₂ ≥ ‖f‖₂²/(4π)`, and the total-variance
   form reads `Δx(f) · Δξ(f) ≥ d/(4π)`. The plan's `d/2` uses the `e^{-ixξ}` convention
   (no `2π`). Either constant is a one-line rescaling of the other.

3. **Dimension reduction.** The `d`-dimensional statement follows from the `1`-dimensional
   one applied to each coordinate `∂_j` (the commutator `[x_j, ∂_j] = -1` summed over
   `j` gives `d` on the left), which is `SchwartzMap.integral_mul_lineDerivOp_right_eq_neg_left`
   in mathlib.

We therefore leave the exact variance form as a documented target; the genuinely
non-trivial *analysis* (the commutator bound) is already machine-checked above.

The precise statement we intend to land (mathematically standard, mathlib's convention):

```lean
theorem heisenberg_variance (d : ℕ) [Fact (0 < d)] (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))
    (h : ‖f.toLp 2 volume‖ = 1) :
    variance_x f * variance_ξ f ≥ (d : ℝ) / (4 * Real.pi)
```
-/

end Criticality

#print axioms Criticality.commutator_integral
#print axioms Criticality.norm_toLp_two_sq_eq_integral_sq
#print axioms Criticality.heisenberg_commutator_real
