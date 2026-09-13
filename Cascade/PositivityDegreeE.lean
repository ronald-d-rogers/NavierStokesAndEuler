import Cascade.DissipationThreshold
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-!
# Positivity (comparison) principle for the truncated scalar dyadic model at degree `e`

Cheskidov's Theorem 4.2, specialised to the truncated scalar dyadic model

`du_k/dt = 2^k (u_{k-1})² - 2^{k+1} u_k u_{k+1} - ν 2^{e k} u_k,   0 ≤ k < N`,

with `u(-1) = u(N) = 0`: a nonnegative initial ladder stays nonnegative.

## The model

The scalar model is `Cascade.velocityRHSDegreeE` with buoyancy switched off (`κ = 0`) and the
Katz–Pavlović couplings `A = 1`, `B = 0` (which the existing predicates
`IsUnforcedTruncatedSolutionE` / `IsForcedTruncatedSolutionE` already hardwire):

`velocityRHSDegreeE ν 0 1 0 e u θ k = boussinesqTransferU 1 0 u k - ν * dyadicWeight (e * k) * u k`.

The temperature ladder `θ` does not enter, because `κ = 0`.

## Route: one scalar integrating factor per shell (no shell-by-shell induction)

Write the shell-`k` equation in the form

`du_k/dt = S_k - a_k(t) · u_k`,   `S_k(t) = 2^k (u_{k-1}(t))² ≥ 0`,
`a_k(t) = 2^{k+1} u_{k+1}(t) + ν 2^{e k}`.

The key point is that the **source `S_k` is a square**, hence nonnegative *unconditionally*; no
sign hypothesis on `u_{k-1}` is required.  (This is what removes the apparent circularity in the
one-sided bound `du_k/dt ≥ -(2^{k+1}u_{k+1} + ν2^{ek}) u_k`: the "source" `2^k(u_{k-1})²` is never
negative, so nothing has to be known about shell `k-1`.)  Consequently the positivity principle is
a *single scalar* comparison, not an induction on `k`.

With `A_k(t) = ∫_0^t a_k`, the integrating factor `exp (A_k)` gives

`d/dt (u_k exp (A_k)) = (du_k/dt + a_k u_k) exp (A_k) = S_k exp (A_k) ≥ 0`,

so `t ↦ u_k(t) exp (A_k(t))` is monotone and

`u_k(t) ≥ u_k(0) exp (-A_k(t)) ≥ 0`  whenever  `u_k(0) ≥ 0`.

This is the integrating-factor trick, formalised below as `nonneg_of_hasDerivAt_sub_mul` using
`antitone_of_hasDerivAt_nonpos` (the derivative of the integrating-factor product is
nonpositive after the sign flip).  It uses no bound on `u` and no Grönwall constant: `a_k` is
only required to be continuous (which it is, since `u_{k+1}` is differentiable in time).  In
particular `ν ≥ 0` is *not* needed and is kept only to mirror the intended interface.

The forced model `IsForcedTruncatedSolutionE` adds a time-independent force `f k`:
`S_k` is replaced by `S_k + f k`, so the same proof applies provided `0 ≤ f k` for every shell
`k`.  That is exactly the hypothesis needed (`f` contributes to the source; nothing else about
`f` matters).

## Contents

* `nonneg_of_hasDerivAt_sub_mul` — the abstract scalar integrating-factor comparison.
* `nonneg_of_nonneg` — the unforced positivity principle (`κ = 0`).
* `nonneg_of_nonneg_forced` — the forced version (hypothesis `0 ≤ f k`).
* Non-vacuity checks.
-/

noncomputable section

set_option linter.unusedVariables false

open scoped BigOperators Interval

namespace Cascade

/-! ## 1. The scalar integrating-factor comparison -/

/-- **A scalar linear ODE with nonnegative source preserves nonnegativity.**
If `f' = S - a * f` with `S ≥ 0` pointwise and `a` continuous, and `f 0 ≥ 0`, then `f ≥ 0` on
`[0, ∞)`.

Proof: with the integrating factor `A t = ∫_0^t a`, the product `t ↦ -(f t * exp (A t))` has
derivative `-(S t * exp (A t)) ≤ 0`, hence is antitone; evaluating at `0 ≤ t` gives
`f 0 ≤ f t * exp (A t)`, and `exp (A t) > 0`. -/
theorem nonneg_of_hasDerivAt_sub_mul {f S a : ℝ → ℝ}
    (hS : ∀ s, 0 ≤ S s) (ha : Continuous a)
    (hf : ∀ s, HasDerivAt f (S s - a s * f s) s) (hf0 : 0 ≤ f 0) :
    ∀ s, 0 ≤ s → 0 ≤ f s := by
  intro s hs
  -- The integrating factor `A t = ∫_0^t a`.
  set A : ℝ → ℝ := fun r => ∫ x in (0 : ℝ)..r, a x with hAdef
  have hA_deriv : ∀ r, HasDerivAt A (a r) r := by
    intro r
    have h := ha.integral_hasStrictDerivAt 0 r
    rw [hAdef]
    exact h.hasDerivAt
  have hA_zero : A 0 = 0 := by
    rw [hAdef]
    simp
  -- The flipped integrating-factor product has nonpositive derivative.
  have hprod : ∀ r, HasDerivAt (fun r => -(f r * Real.exp (A r)))
      (-(S r * Real.exp (A r))) r := by
    intro r
    have h1 : HasDerivAt (fun r => f r * Real.exp (A r))
        ((S r - a r * f r) * Real.exp (A r) + f r * (Real.exp (A r) * a r)) r :=
      (hf r).mul ((hA_deriv r).exp)
    have h2 : (S r - a r * f r) * Real.exp (A r) + f r * (Real.exp (A r) * a r)
        = S r * Real.exp (A r) := by ring
    rw [h2] at h1
    exact h1.neg
  have hanti : Antitone (fun r => -(f r * Real.exp (A r))) :=
    antitone_of_hasDerivAt_nonpos hprod fun r => by
      have h1 : 0 ≤ S r * Real.exp (A r) := mul_nonneg (hS r) (Real.exp_pos _).le
      simp only [Pi.zero_apply]
      linarith
  have hle : -(f s * Real.exp (A s)) ≤ -(f 0 * Real.exp (A 0)) := hanti hs
  rw [hA_zero, Real.exp_zero, mul_one] at hle
  have hle' : f 0 ≤ f s * Real.exp (A s) := by linarith
  have hnn : 0 ≤ f s * Real.exp (A s) := le_trans hf0 hle'
  exact (mul_nonneg_iff_of_pos_right (Real.exp_pos (A s))).mp hnn

/-! ## 2. The unforced positivity principle -/

/-- **Cheskidov's Theorem 4.2 for the truncated scalar dyadic model at degree `e` (unforced).**
Along any truncated unforced degree-`e` solution with buoyancy off (`κ = 0`, the scalar model),
if every shell of the initial ladder is nonnegative then every shell stays nonnegative.

The shell-`k` equation reads `du_k/dt = S_k - a_k(t) u_k` with `S_k = 2^k (u_{k-1})² ≥ 0` and
`a_k(t) = 2^{k+1} u_{k+1}(t) + ν 2^{ek}` continuous; `nonneg_of_hasDerivAt_sub_mul` applies
verbatim to `k` fixed.  No boundedness of `u` is used, and no shell-by-shell induction is
needed, because the source `2^k (u_{k-1})²` is a square.  The thermal diffusivity `μ` is
arbitrary: with `κ = 0` the temperature equation and the boundary conditions are never used. -/
theorem nonneg_of_nonneg (ν μ : ℝ) (hν : 0 ≤ ν) (e : ℤ) (N : ℕ) (u θ : ℝ → ℤ → ℝ)
    (h : IsUnforcedTruncatedSolutionE ν μ 0 e N u θ)
    (h0 : ∀ k, 0 ≤ u 0 k) (t : ℝ) (ht : 0 ≤ t) :
    ∀ k, 0 ≤ u t k := by
  intro k
  -- The shell-`k` equation, written as `S - a * f`.
  have hf : ∀ s, HasDerivAt (fun s => u s k)
      (dyadicWeight k * (u s (k - 1)) ^ 2
        - (2 * dyadicWeight k * u s (k + 1) + ν * dyadicWeight (e * k)) * u s k) s := by
    intro s
    have hs := h.1 s k
    have heq : velocityRHSDegreeE ν 0 1 0 e (u s) (θ s) k
        = dyadicWeight k * (u s (k - 1)) ^ 2
          - (2 * dyadicWeight k * u s (k + 1) + ν * dyadicWeight (e * k)) * u s k := by
      simp only [velocityRHSDegreeE, boussinesqTransferU]
      ring
    rwa [heq] at hs
  have hS : ∀ s, 0 ≤ dyadicWeight k * (u s (k - 1)) ^ 2 := fun s =>
    mul_nonneg (dyadicWeight_nonneg k) (sq_nonneg _)
  have ha : Continuous
      (fun s : ℝ => 2 * dyadicWeight k * u s (k + 1) + ν * dyadicWeight (e * k)) := by
    have hdiff : Differentiable ℝ (fun s : ℝ => u s (k + 1)) :=
      fun s => (h.1 s (k + 1)).differentiableAt
    exact (continuous_const.mul hdiff.continuous).add continuous_const
  exact nonneg_of_hasDerivAt_sub_mul
    (f := fun s => u s k)
    (S := fun s => dyadicWeight k * (u s (k - 1)) ^ 2)
    (a := fun s => 2 * dyadicWeight k * u s (k + 1) + ν * dyadicWeight (e * k))
    hS ha hf (h0 k) t ht

/-! ## 3. The forced positivity principle -/

/-- **Cheskidov's Theorem 4.2 for the truncated scalar dyadic model at degree `e` (forced).**
The forced model adds a time-independent force `f k` to the shell-`k` equation, so the source
becomes `S_k + f k`.  The integrating-factor argument applies verbatim, and the only hypothesis
on the force is `0 ≤ f k` for every shell `k` — no bound, no continuity, and no decay of `f` is
needed.  The temperature force `g` is irrelevant (buoyancy is off). -/
theorem nonneg_of_nonneg_forced (ν μ : ℝ) (hν : 0 ≤ ν) (e : ℤ) (N : ℕ) (f g : ℤ → ℝ)
    (u θ : ℝ → ℤ → ℝ)
    (h : IsForcedTruncatedSolutionE ν μ 0 e N f g u θ)
    (hfnn : ∀ k, 0 ≤ f k) (h0 : ∀ k, 0 ≤ u 0 k) (t : ℝ) (ht : 0 ≤ t) :
    ∀ k, 0 ≤ u t k := by
  intro k
  have hf : ∀ s, HasDerivAt (fun s => u s k)
      ((dyadicWeight k * (u s (k - 1)) ^ 2 + f k)
        - (2 * dyadicWeight k * u s (k + 1) + ν * dyadicWeight (e * k)) * u s k) s := by
    intro s
    have hs := h.1 s k
    have heq : velocityRHSDegreeE ν 0 1 0 e (u s) (θ s) k + f k
        = (dyadicWeight k * (u s (k - 1)) ^ 2 + f k)
          - (2 * dyadicWeight k * u s (k + 1) + ν * dyadicWeight (e * k)) * u s k := by
      simp only [velocityRHSDegreeE, boussinesqTransferU]
      ring
    rwa [heq] at hs
  have hS : ∀ s, 0 ≤ dyadicWeight k * (u s (k - 1)) ^ 2 + f k := fun s =>
    add_nonneg (mul_nonneg (dyadicWeight_nonneg k) (sq_nonneg _)) (hfnn k)
  have ha : Continuous
      (fun s : ℝ => 2 * dyadicWeight k * u s (k + 1) + ν * dyadicWeight (e * k)) := by
    have hdiff : Differentiable ℝ (fun s : ℝ => u s (k + 1)) :=
      fun s => (h.1 s (k + 1)).differentiableAt
    exact (continuous_const.mul hdiff.continuous).add continuous_const
  exact nonneg_of_hasDerivAt_sub_mul
    (f := fun s => u s k)
    (S := fun s => dyadicWeight k * (u s (k - 1)) ^ 2 + f k)
    (a := fun s => 2 * dyadicWeight k * u s (k + 1) + ν * dyadicWeight (e * k))
    hS ha hf (h0 k) t ht

/-! ## 4. Non-vacuity -/

/-- The zero ladder is nonnegative at every time and shell. -/
example (t : ℝ) : ∀ k : ℤ, 0 ≤ (fun (_ : ℝ) (_ : ℤ) => (0 : ℝ)) t k := by
  intro k
  norm_num

/-- The unforced positivity principle is not vacuous: it applies to the zero equilibrium. -/
example (e : ℤ) (t : ℝ) (ht : 0 ≤ t) :
    ∀ k : ℤ, 0 ≤ (fun (_ : ℝ) (_ : ℤ) => (0 : ℝ)) t k :=
  nonneg_of_nonneg 1 0 (by norm_num) e 4 (fun _ _ => 0) (fun _ _ => 0)
    (zero_is_unforcedTruncatedSolutionE 1 0 0 e 4) (fun k => le_refl 0) t ht

/-- The forced positivity principle is not vacuous either: the zero state with zero force is a
forced truncated solution, and the hypothesis `0 ≤ f k` holds for `f ≡ 0`. -/
example (e : ℤ) (t : ℝ) (ht : 0 ≤ t) :
    ∀ k : ℤ, 0 ≤ (fun (_ : ℝ) (_ : ℤ) => (0 : ℝ)) t k := by
  refine nonneg_of_nonneg_forced 1 0 (by norm_num) e 4 (fun _ => 0) (fun _ => 0)
    (fun _ _ => 0) (fun _ _ => 0) ?_ (fun k => le_refl 0) (fun k => le_refl 0) t ht
  refine ⟨?_, ?_, ?_⟩
  · intro s k
    have hz : velocityRHSDegreeE 1 0 1 0 e (fun _ : ℤ => (0 : ℝ)) (fun _ : ℤ => (0 : ℝ)) k + 0
        = 0 := by
      simp [velocityRHSDegreeE, boussinesqTransferU, dyadicWeight]
    rw [hz]
    exact hasDerivAt_const s 0
  · intro s k
    have hz : temperatureRHSDegreeE 0 1 1 e (fun _ : ℤ => (0 : ℝ)) (fun _ : ℤ => (0 : ℝ)) k + 0
        = 0 := by
      simp [temperatureRHSDegreeE, boussinesqTransferTheta, dyadicWeight]
    rw [hz]
    exact hasDerivAt_const s 0
  · intro s
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- A concrete nonnegative, **nonzero** ladder: `u 1 = 3`, all other shells `0`.  It is written
inline (rather than as a named `def`) so that the axiom audit below covers every named object in
the file. -/
example : ∀ k : ℤ, 0 ≤ (fun k : ℤ => if k = 1 then (3 : ℝ) else 0) k := by
  intro k
  change 0 ≤ (if k = 1 then (3 : ℝ) else 0)
  split_ifs <;> norm_num

/-- **The key barrier step, numerically, at a concrete nonzero state, `e = 0`.**  At shell `k = 2`
one has `u_2 = 0` but `u_1 = 3 ≠ 0`, so the source `2²·(u_1)² = 36` is strictly positive and the
one-sided condition `u_k = 0 ⟹ du_k/dt ≥ 0` holds strictly (`36 > 0`). -/
example : 0 < velocityRHSDegreeE 1 0 1 0 0
    (fun k : ℤ => if k = 1 then (3 : ℝ) else 0) (fun _ => 0) 2 := by
  norm_num [velocityRHSDegreeE, boussinesqTransferU, dyadicWeight]

/-- **The same barrier step at `e = -1`**, where the dissipation weight is `2^{-2} = 1/4`
(irrelevant because `u_2 = 0`). -/
example : 0 < velocityRHSDegreeE 1 0 1 0 (-1)
    (fun k : ℤ => if k = 1 then (3 : ℝ) else 0) (fun _ => 0) 2 := by
  norm_num [velocityRHSDegreeE, boussinesqTransferU, dyadicWeight]

end Cascade

/-! ## Axiom audit -/

#print axioms Cascade.nonneg_of_hasDerivAt_sub_mul
#print axioms Cascade.nonneg_of_nonneg
#print axioms Cascade.nonneg_of_nonneg_forced
