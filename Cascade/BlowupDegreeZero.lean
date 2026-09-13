/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cascade formalization
-/

import Cascade.BlowupEngine
import Cascade.BlowupRate
import Cascade.PositivityDegreeE
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Finite-time blow-up of the truncated dyadic model at dissipation degree `e = 0`

This is the capstone file: it assembles the already verified ingredients into the project's first
genuine **finite-time blow-up** theorem.

## The model

`u_k' = 2^k (u_{k-1}² - 2 u_k u_{k+1}) - ν u_k`, `u_{-1} = u_N = 0`, buoyancy off (`κ = 0`),
`A = 1`, `B = 0` (the model of `Cascade/BlowupRate.lean`).  The only dissipation is `ν u_k`, i.e.
dissipation degree `e = 0`.

## Contents

1. **A new engine (`le_of_deriv_ge_mul_sqrt_sub`).**  The reversed-Bernoulli engine
   `le_of_deriv_ge_mul_sqrt` of `Cascade/BlowupEngine.lean` needs `y' ≥ c y√y` *everywhere* on
   `[0,T]`.  Here the rate inequality carries an extra `- 2ν·y`, so it only gives that above a
   threshold.  The new engine **absorbs the linear term** by differentiating `f = 1/√y`:

   `f' t ≤ ν · f t - c/2`   (`f₀ = 1/√y₀`,  `δ = c/2 - ν f₀ > 0` under `2ν < c√y₀`).

   Grönwall's inequality (`le_gronwallBound_of_liminf_deriv_right_le`) gives
   `f T ≤ f₀·e^{νT} - (c/2)(e^{νT}-1)/ν =: G`, and the estimate `(e^{νT}-1)/ν ≥ T`
   (valid for `ν > 0`, from `Real.add_one_le_exp`) yields `G ≤ f₀ - δT`.  Since `f T > 0`,
   `δT < f₀`, i.e. `T < f₀/δ = 2/(c√y₀ - 2ν)`.

   **Correction to the intended statement.**  The hypothesis `0 ≤ ν` is *not* removable: the
   conclusion `T ≤ 2/(c√y₀ - 2ν)` is **false for `ν < 0`**.  At `ν = -1`, `c = 1`, `y₀ = 1` the
   exact solution of `f' = ν f - c/2` is `f t = (3/2)e^{-t} - 1/2`, which vanishes at `t = log 3`,
   while `2/(c√y₀ - 2ν) = 2/3 < log 3`.  For `ν ≤ 0` the correct bound is the larger
   `T ≤ 2/(c√y₀)` (proved below as `le_of_deriv_ge_mul_sqrt_sub_nonpos` by reducing to the
   original engine); the unified correct statement is `T ≤ 2/(c√y₀ - 2·max ν 0)`.

2. **The chain (`cubicSum_lower_bound`).**  With `e = 0`, `inverted_holder` reads
   `A · S · √S ≤ cubicSum`, where `A = holderConst 1 = √(1/2)` and `S = blowupNorm`.
   Combined with `(7/10)·lyap ≤ blowupNorm` (from `correction ≤ blowupNorm` at `c₂ = 4/7`) and the
   monotonicity of `√`, this gives `c₀ · lyap · √lyap ≤ cubicSum` with
   `c₀ = A·(7/10)·√(7/10)`, hence

   `lyap' ≥ c · lyap · √lyap - 2ν·lyap`,   `c = (27/28)·c₀ = (27/28)·√(1/2)·(7/10)·√(7/10)`.

   `c` is the `def blowupCoeff` of this file (numerically `27√35/400 ≈ 0.39934`).

3. **The capstone (`no_global_solution_degree_zero`).**  The Lyapunov functional `L` never
   vanishes: the chain with `cubicSum ≥ 0` and `ν ≥ 0` gives `L' ≥ -2νL`, so the product
   `t ↦ Real.exp (-(2|ν| t)) * L t` has nonnegative derivative on `[0,T]` and hence
   `L t ≥ Real.exp (-(2|ν| t)) * L 0 > 0`.  The engine then applies on `[0,T]` for
   `T = 2/(c√y₀ - 2ν) + 1`, contradicting `T ≤ 2/(c√y₀ - 2ν)`: **no global solution exists**.

   The hypothesis `hlarge : blowupThreshold ν < lyap (u 0) N (4/7)`, where
   `blowupThreshold ν = (2ν/c)²`, is exactly the engine's `hgap`, i.e. `2ν < c·√(lyap 0)`;
   nonnegativity of `u t k` for `t ≥ 0` comes from the verified positivity principle
   `nonneg_of_nonneg`, which is why `0 ≤ ν` appears in the capstone (it is needed for the
   *ladder's* positivity and for the sign in the corrected engine).

## Non-vacuity

`c` is computed exactly (`27√35/400`), the single-mode `inverted_holder` bound is evaluated, the
engine's bound is evaluated at concrete data, and an explicit nonnegative ladder with `hlarge`
satisfied is exhibited.

Every declaration is fully proved with no unproved placeholders, and the file introduces no new
axioms; the `#print axioms` audit at the end reports `[propext, Classical.choice, Quot.sound]` for
every declaration.
-/

noncomputable section

set_option linter.unusedVariables false

open scoped BigOperators Topology

namespace Cascade

/-! ## 1. The new engine: logistic-superlinear blow-up -/

/-- **The logistic-superlinear blow-up engine.**  If `y > 0` on `[0,T]`, `c > 0`, `y₀ > 0`,
`ν ≥ 0`, `y 0 = y₀` and `y' ≥ c·y√y - 2ν·y` there, then `T ≤ 2/(c√y₀ - 2ν)`, provided the
denominator is positive, i.e. `2ν < c·√y₀`.

The extra linear term `-2ν·y` is absorbed by the substitution `f = 1/√y`: the deficit
`δ = c/2 - ν f₀ = (c√y₀ - 2ν)/(2√y₀)` is positive precisely under `hgap`.  For `ν < 0` this
statement is false (see the module docstring); use `le_of_deriv_ge_mul_sqrt_sub_nonpos`. -/
theorem le_of_deriv_ge_mul_sqrt_sub (y y' : ℝ → ℝ) {c ν y₀ T : ℝ} (hν : 0 ≤ ν) (hc : 0 < c)
    (hy₀ : 0 < y₀) (hT : 0 < T)
    (hderiv : ∀ t ∈ Set.Icc 0 T, HasDerivAt y (y' t) t)
    (hineq : ∀ t ∈ Set.Icc 0 T, c * (y t * Real.sqrt (y t)) - 2 * ν * y t ≤ y' t)
    (hpos : ∀ t ∈ Set.Icc 0 T, 0 < y t) (hy0 : y 0 = y₀) (hgap : 2 * ν < c * Real.sqrt y₀) :
    T ≤ 2 / (c * Real.sqrt y₀ - 2 * ν) := by
  set f : ℝ → ℝ := fun t => 1 / Real.sqrt (y t) with hf
  set f₀ : ℝ := 1 / Real.sqrt y₀ with hf₀
  set δ : ℝ := c / 2 - ν * f₀ with hδ
  have hspos : 0 < Real.sqrt y₀ := Real.sqrt_pos.mpr hy₀
  have hδpos : 0 < δ := by
    rw [hδ, hf₀, sub_pos]
    have h : (2 * ν) / Real.sqrt y₀ < c := (div_lt_iff₀ hspos).mpr hgap
    have h2 := div_lt_div_of_pos_right h (show (0:ℝ) < 2 by norm_num)
    have heq : (2 * ν) / Real.sqrt y₀ / 2 = ν * (1 / Real.sqrt y₀) := by ring
    rwa [heq] at h2
  have hf0eq : f 0 = f₀ := by
    simp only [hf, hf₀]
    rw [hy0]
  -- The derivative of `f = 1/√y`.
  have hderiv_f : ∀ t ∈ Set.Icc 0 T,
      HasDerivAt f (-(y' t) / (2 * (Real.sqrt (y t)) ^ 3)) t := by
    intro t ht
    have hyt : 0 < y t := hpos t ht
    have hsq : HasDerivAt (fun s => Real.sqrt (y s))
        (y' t * (1 / (2 * Real.sqrt (y t)))) t := by
      have h := (Real.hasDerivAt_sqrt (ne_of_gt hyt)).comp t (hderiv t ht)
      simpa [Function.comp_def, mul_comm] using h
    have hinv := HasDerivAt.div (hasDerivAt_const t (1:ℝ)) hsq
      (ne_of_gt (Real.sqrt_pos.mpr hyt))
    have hval : (0 * Real.sqrt (y t) - 1 * (y' t * (1 / (2 * Real.sqrt (y t)))))
          / (Real.sqrt (y t)) ^ 2 = -(y' t) / (2 * (Real.sqrt (y t)) ^ 3) := by
      field_simp
      ring
    have hfun : ((fun _ : ℝ => (1:ℝ)) / fun s => Real.sqrt (y s)) = f := by
      funext s; rfl
    rw [hfun, hval] at hinv
    exact hinv
  -- The differential inequality `f' ≤ ν f - c/2`.
  have hineq_f : ∀ t ∈ Set.Icc 0 T,
      (-(y' t) / (2 * (Real.sqrt (y t)) ^ 3)) ≤ ν * f t - c / 2 := by
    intro t ht
    have hyt : 0 < y t := hpos t ht
    have hcube : y t * Real.sqrt (y t) = (Real.sqrt (y t)) ^ 3 := by
      rw [show (Real.sqrt (y t)) ^ 3 = (Real.sqrt (y t)) ^ 2 * Real.sqrt (y t) by ring,
        Real.sq_sqrt hyt.le]
    have hkey : c * (Real.sqrt (y t)) ^ 3 - 2 * ν * y t ≤ y' t := by
      rw [← hcube]; exact hineq t ht
    have hden : 0 < 2 * (Real.sqrt (y t)) ^ 3 := by positivity
    have hdiv : -(y' t) / (2 * (Real.sqrt (y t)) ^ 3)
        ≤ (-(c * (Real.sqrt (y t)) ^ 3 - 2 * ν * y t)) / (2 * (Real.sqrt (y t)) ^ 3) :=
      div_le_div_of_nonneg_right (by linarith [hkey]) hden.le
    have hrhs : (-(c * (Real.sqrt (y t)) ^ 3 - 2 * ν * y t)) / (2 * (Real.sqrt (y t)) ^ 3)
        = ν * f t - c / 2 := by
      rw [hf]; field_simp; rw [Real.sq_sqrt hyt.le, ← hcube]; ring
    linarith [hdiv, hrhs.le, hrhs.ge]
  -- Grönwall: `f T ≤ gronwallBound f₀ ν (-c/2) T`.
  have hcont : ContinuousOn f (Set.Icc 0 T) := fun x hx =>
    ((hderiv_f x hx).continuousAt).continuousWithinAt
  have hslope : ∀ x ∈ Set.Ico 0 T, ∀ r, (ν * f x - c/2) < r →
      ∃ᶠ z in 𝓝[>] x, slope f x z < r := by
    intro x hx r hr
    have hxIcc : x ∈ Set.Icc 0 T := ⟨hx.1, hx.2.le⟩
    exact ((hderiv_f x hxIcc).hasDerivWithinAt).liminf_right_slope_le
      (lt_of_le_of_lt (hineq_f x hxIcc) hr)
  have hgron : ∀ x ∈ Set.Icc 0 T, f x ≤ gronwallBound f₀ ν (-c/2) (x - 0) :=
    le_gronwallBound_of_liminf_deriv_right_le (f := f) (f' := fun x => ν * f x - c/2)
      (δ := f₀) (K := ν) (ε := -c/2) (a := 0) (b := T) hcont hslope (le_of_eq hf0eq)
      (fun x hx => le_of_eq (by ring))
  have hfT : f T ≤ gronwallBound f₀ ν (-c/2) T := by
    have := hgron T ⟨hT.le, le_rfl⟩
    simpa using this
  -- The Grönwall bound is at most `f₀ - δT` because `(e^{νT}-1)/ν ≥ T` for `ν > 0`.
  have hgb : gronwallBound f₀ ν (-c/2) T ≤ f₀ - δ * T := by
    rcases eq_or_lt_of_le hν with hν0 | hνpos
    · subst hν0
      rw [gronwallBound_K0]
      simp only
      rw [hδ]
      ring_nf
      exact le_refl _
    · have hK : ν ≠ 0 := ne_of_gt hνpos
      rw [gronwallBound_of_K_ne_0 hK]
      simp only
      have hE : ν * T + 1 ≤ Real.exp (ν * T) := Real.add_one_le_exp _
      have hge : T ≤ (Real.exp (ν * T) - 1) / ν := by
        rw [le_div_iff₀ hνpos]; linarith
      have hkey : f₀ * Real.exp (ν * T) + (-c/2)/ν * (Real.exp (ν * T) - 1) - (f₀ - δ * T)
          = δ * (T - (Real.exp (ν * T) - 1) / ν) := by
        rw [hδ]; field_simp; ring
      have h2 : δ * (T - (Real.exp (ν * T) - 1) / ν) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hδpos.le (by linarith)
      linarith [hkey]
  have hfTpos : 0 < f T := by
    rw [hf]
    exact one_div_pos.mpr (Real.sqrt_pos.mpr (hpos T ⟨hT.le, le_rfl⟩))
  have hlt : δ * T < f₀ := by linarith [hfT, hgb, hfTpos]
  have hf₀pos : 0 < f₀ := by rw [hf₀]; exact one_div_pos.mpr hspos
  have hkey : T ≤ f₀ / δ := by
    rw [le_div_iff₀ hδpos]; linarith
  have hval : f₀ / δ = 2 / (c * Real.sqrt y₀ - 2 * ν) := by
    rw [hδ, hf₀]
    have hden : c * Real.sqrt y₀ - 2 * ν ≠ 0 := by
      have : 0 < c * Real.sqrt y₀ - 2 * ν := by linarith
      exact ne_of_gt this
    field_simp
  rwa [hval] at hkey

/-- **Non-existence form of the new engine.**  If `T` exceeds the critical time
`2/(c√y₀ - 2ν)`, there is no positive solution of `y' ≥ c y√y - 2ν y` on `[0,T]` with
`y 0 = y₀` — every such solution blows up at or before that time. -/
theorem not_exists_solution_of_gt_sub {c ν y₀ T : ℝ} (hν : 0 ≤ ν) (hc : 0 < c) (hy₀ : 0 < y₀)
    (hT : 0 < T) (hgap : 2 * ν < c * Real.sqrt y₀)
    (hgt : 2 / (c * Real.sqrt y₀ - 2 * ν) < T) :
    ¬ ∃ (y y' : ℝ → ℝ), (∀ t ∈ Set.Icc 0 T, HasDerivAt y (y' t) t) ∧
      (∀ t ∈ Set.Icc 0 T, c * (y t * Real.sqrt (y t)) - 2 * ν * y t ≤ y' t) ∧
      (∀ t ∈ Set.Icc 0 T, 0 < y t) ∧ y 0 = y₀ := by
  rintro ⟨y, y', hderiv, hineq, hpos, hy0⟩
  exact absurd (le_of_deriv_ge_mul_sqrt_sub y y' hν hc hy₀ hT hderiv hineq hpos hy0 hgap)
    (not_le.mpr hgt)

/-- **The engine for `ν ≤ 0`.**  The linear term helps when `ν ≤ 0`, so the hypothesis reduces to
the original reversed-Bernoulli engine `c y√y ≤ y'` and the (larger) critical time is
`2/(c√y₀)`.  This is the correct bound in that regime, and it shows that the `ν ≥ 0` hypothesis of
`le_of_deriv_ge_mul_sqrt_sub` cannot be dropped. -/
theorem le_of_deriv_ge_mul_sqrt_sub_nonpos (y y' : ℝ → ℝ) {c ν y₀ T : ℝ} (hν : ν ≤ 0)
    (hc : 0 < c) (hy₀ : 0 < y₀) (hT : 0 < T)
    (hderiv : ∀ t ∈ Set.Icc 0 T, HasDerivAt y (y' t) t)
    (hineq : ∀ t ∈ Set.Icc 0 T, c * (y t * Real.sqrt (y t)) - 2 * ν * y t ≤ y' t)
    (hpos : ∀ t ∈ Set.Icc 0 T, 0 < y t) (hy0 : y 0 = y₀) :
    T ≤ 2 / (c * Real.sqrt y₀) := by
  refine le_of_deriv_ge_mul_sqrt y y' hc hy₀ hT hderiv ?_ hpos hy0
  intro t ht
  have h := hineq t ht
  have h2 : 0 ≤ -2 * ν * y t := by nlinarith [hν, hpos t ht]
  linarith

/-- **The `0 ≤ ν` hypothesis of the engine is necessary.**  The `f`-level statement underlying
`le_of_deriv_ge_mul_sqrt_sub` — `f' ≤ ν·f - c/2` on `[0,T]`, `f > 0`, `f 0 = f₀` implies
`T ≤ f₀/(c/2 - ν f₀)` — is *false* without `0 ≤ ν`: at `c = 1`, `ν = -1`, `f₀ = 1` the function
`f t = (3/2)·e^{-t} - 1/2` satisfies `f' = ν f - c/2` and is positive on `[0, 3/4]`, while
`3/4 > 2/3 = f₀/(c/2 - ν f₀)`. -/
theorem engine_false_without_nonneg :
    ¬ (∀ (f f' : ℝ → ℝ) {c ν f₀ T : ℝ}, 0 < c → 0 < f₀ → 0 < T →
      (∀ t ∈ Set.Icc 0 T, HasDerivAt f (f' t) t) →
      (∀ t ∈ Set.Icc 0 T, f' t ≤ ν * f t - c / 2) →
      (∀ t ∈ Set.Icc 0 T, 0 < f t) → f 0 = f₀ →
      T ≤ f₀ / (c / 2 - ν * f₀)) := by
  intro h
  have hf : ∀ t ∈ Set.Icc (0:ℝ) (3/4),
      HasDerivAt (fun s => (3/2) * Real.exp (-s) - 1/2) (-((3/2) * Real.exp (-t))) t := by
    intro t _
    have h1 : HasDerivAt (fun s : ℝ => Real.exp (-s)) (Real.exp (-t) * (-1)) t := by
      have := (hasDerivAt_id t).neg.exp
      simpa using this
    have h2 : HasDerivAt (fun s : ℝ => (3/2) * Real.exp (-s))
        ((3/2) * (Real.exp (-t) * (-1))) t := h1.const_mul (3/2)
    have h3 := h2.sub_const (1/2)
    have hval : (3/2) * (Real.exp (-t) * (-1)) = -((3/2) * Real.exp (-t)) := by ring
    rw [hval] at h3
    exact h3
  have hpos : ∀ t ∈ Set.Icc (0:ℝ) (3/4), 0 < (3/2) * Real.exp (-t) - 1/2 := by
    intro t ht
    have hexp : Real.exp (-(3/4)) ≤ Real.exp (-t) := Real.exp_le_exp_of_le (by linarith [ht.2])
    have hlt : (1/3 : ℝ) < Real.exp (-(3/4)) := by
      have h1 : Real.exp (3/4) < 3 :=
        lt_trans (Real.exp_lt_exp.mpr (by norm_num)) Real.exp_one_lt_three
      have h2 : (3/4 : ℝ) < Real.log 3 := by
        rw [← Real.exp_lt_exp, Real.exp_log (by norm_num : (0:ℝ) < 3)]
        exact h1
      have h3 : Real.log (1/3) = -Real.log 3 := by
        rw [show (1/3 : ℝ) = 3⁻¹ by norm_num, Real.log_inv]
      have h4 : Real.log (1/3) < -(3/4) := by rw [h3]; linarith
      calc (1/3 : ℝ) = Real.exp (Real.log (1/3)) := (Real.exp_log (by norm_num)).symm
        _ < Real.exp (-(3/4)) := Real.exp_lt_exp.mpr h4
    linarith
  have hineq : ∀ t ∈ Set.Icc (0:ℝ) (3/4),
      -((3/2) * Real.exp (-t)) ≤ (-1) * ((3/2) * Real.exp (-t) - 1/2) - 1 / 2 := by
    intro t _
    ring_nf
    exact le_refl _
  have hbound := h (fun s => (3/2) * Real.exp (-s) - 1/2) (fun t => -((3/2) * Real.exp (-t)))
    (c := 1) (ν := -1) (f₀ := 1) (T := 3/4) (by norm_num) (by norm_num) (by norm_num)
    hf hineq hpos (by norm_num)
  rw [show (1:ℝ) / (1 / 2 - -1 * 1) = 2/3 by norm_num] at hbound
  linarith

/-! ## 2. The chain: the cubic term dominates `lyap·√lyap` -/

/-- The `(k+1)`-shifted weighted square sum is at most `(1/2)·blowupNorm` (the weight identity
`2^k = (1/2)·2^{k+1}` plus `u_N = 0`). -/
theorem sum_shift_sq_le (u : ℤ → ℝ) (N : ℕ) (huN : u (N:ℤ) = 0) :
    (∑ k ∈ Finset.range N, dyadicWeight (k:ℤ) * (u ((k:ℤ)+1))^2)
      ≤ (1/2) * blowupNorm u N := by
  set f : ℕ → ℝ := fun m => dyadicWeight (m:ℤ) * (u (m:ℤ))^2 with hf
  have h1 : (∑ k ∈ Finset.range N, dyadicWeight (k:ℤ) * (u ((k:ℤ)+1))^2)
      = (1/2) * ∑ k ∈ Finset.range N, f (k+1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [hf]
    push_cast
    rw [dyadicWeight_add, show dyadicWeight (1:ℤ) = 2 by norm_num [dyadicWeight]]
    ring
  rw [h1]
  have hsucc' := Finset.sum_range_succ' f N
  have hsucc := Finset.sum_range_succ f N
  have hfN : f N = 0 := by simp only [hf]; rw [huN]; ring
  have hf0 : 0 ≤ f 0 := by
    simp only [hf]; exact mul_nonneg (dyadicWeight_pos _).le (sq_nonneg _)
  have hle : (∑ k ∈ Finset.range N, f (k+1)) ≤ ∑ k ∈ Finset.range N, f k := by
    linarith [hsucc', hsucc, hfN, hf0]
  have hbn : (∑ k ∈ Finset.range N, f k) = blowupNorm u N := by
    unfold blowupNorm; rfl
  rw [hbn] at hle
  exact mul_le_mul_of_nonneg_left hle (by norm_num)

/-- **The sharp correction bound** `correction ≤ (3/4)·blowupNorm` for nonnegative data (pairwise
AM–GM plus the weight shift). -/
theorem correction_le_three_quarters (u : ℤ → ℝ) (N : ℕ) (hnn : ∀ k : ℤ, 0 ≤ u k)
    (huN : u (N:ℤ) = 0) :
    correction u N ≤ (3/4) * blowupNorm u N := by
  have hpoint : ∀ k ∈ Finset.range N,
      dyadicWeight (k:ℤ) * u (k:ℤ) * u ((k:ℤ)+1)
        ≤ (1/2) * (dyadicWeight (k:ℤ) * (u (k:ℤ))^2)
          + (1/2) * (dyadicWeight (k:ℤ) * (u ((k:ℤ)+1))^2) := by
    intro k _
    nlinarith [mul_nonneg (dyadicWeight_pos (k:ℤ)).le (sq_nonneg (u (k:ℤ) - u ((k:ℤ)+1)))]
  have hsum := Finset.sum_le_sum hpoint
  have hsplit : (∑ k ∈ Finset.range N,
        ((1/2) * (dyadicWeight (k:ℤ) * (u (k:ℤ))^2)
          + (1/2) * (dyadicWeight (k:ℤ) * (u ((k:ℤ)+1))^2)))
      = (1/2) * blowupNorm u N
        + (1/2) * (∑ k ∈ Finset.range N, dyadicWeight (k:ℤ) * (u ((k:ℤ)+1))^2) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    unfold blowupNorm
    rfl
  rw [hsplit] at hsum
  have hshift := sum_shift_sq_le u N huN
  unfold correction
  linarith

/-- `(7/10) * lyap ≤ blowupNorm` for nonnegative data with `c₂ = 4/7`, from the sharp
`correction ≤ (3/4)·blowupNorm`: `lyap ≤ (1 + (4/7)(3/4))·blowupNorm = (10/7)·blowupNorm`. -/
theorem blowupNorm_ge_lyap (u : ℤ → ℝ) (N : ℕ) (hnn : ∀ k : ℤ, 0 ≤ u k)
    (huN : u (N:ℤ) = 0) :
    (7/10) * lyap u N (4/7) ≤ blowupNorm u N := by
  have h1 : correction u N ≤ (3/4) * blowupNorm u N := correction_le_three_quarters u N hnn huN
  have h2 : 0 ≤ blowupNorm u N := blowupNorm_nonneg u N
  simp only [lyap]
  linarith

/-- **The chain.**  For a nonnegative time slice at degree `e = 0`, the cubic sum dominates
`lyap·√lyap`:

`c₀ · lyap · √lyap ≤ cubicSum`,   `c₀ = holderConst 1 · (7/10) · Real.sqrt (7/10)`.

This is the inverted Hölder inequality `inverted_holder` (`A · S · √S ≤ cubicSum` with
`A = holderConst 1`) combined with `(7/10)·lyap ≤ blowupNorm = S` and the monotonicity of `√`. -/
theorem cubicSum_lower_bound (u : ℤ → ℝ) (N : ℕ) (hnn : ∀ k : ℤ, 0 ≤ u k)
    (huN : u (N:ℤ) = 0) :
    holderConst 1 * (7/10) * Real.sqrt (7/10) * (lyap u N (4/7) * Real.sqrt (lyap u N (4/7)))
      ≤ cubicSum u N := by
  set S : ℝ := blowupNorm u N with hS
  set L : ℝ := lyap u N (4/7) with hL
  have hSnn : 0 ≤ S := blowupNorm_nonneg u N
  -- `inverted_holder` at `e = 0`, with `|u_k|³ = u_k³` for nonnegative `u`.
  have hholder := inverted_holder 0 le_rfl u N
  have hScongr : (∑ k ∈ Finset.range N,
      dyadicWeight (((0:ℤ) + 1) * (k:ℤ)) * (u (k:ℤ)) ^ 2) = S := by
    rw [hS]
    unfold blowupNorm
    apply Finset.sum_congr rfl
    intro k _
    norm_num
  rw [hScongr] at hholder
  have hQcongr : (∑ k ∈ Finset.range N, dyadicWeight (2 * (k:ℤ)) * |u (k:ℤ)| ^ 3) = cubicSum u N := by
    unfold cubicSum
    apply Finset.sum_congr rfl
    intro k _
    rw [abs_of_nonneg (hnn (k:ℤ))]
  rw [hQcongr] at hholder
  have hA1 : holderConst (1 - 3*0) = holderConst 1 := by norm_num
  rw [hA1] at hholder
  have hCL : (7/10) * L ≤ S := blowupNorm_ge_lyap u N hnn huN
  have hLpos : 0 ≤ L := by
    have hb := blowupNorm_nonneg u N
    have hc := correction_nonneg u N hnn
    simp only [hL, lyap]
    linarith
  have hsq : ((7/10) * L) * Real.sqrt ((7/10) * L) ≤ S * Real.sqrt S :=
    mul_le_mul hCL (Real.sqrt_le_sqrt hCL) (Real.sqrt_nonneg _) hSnn
  have hfac : ((7/10) * L) * Real.sqrt ((7/10) * L)
      = (7/10) * Real.sqrt (7/10) * (L * Real.sqrt L) := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 7/10) L]
    ring
  calc holderConst 1 * (7/10) * Real.sqrt (7/10) * (L * Real.sqrt L)
      = holderConst 1 * ((7/10) * Real.sqrt (7/10) * (L * Real.sqrt L)) := by ring
    _ ≤ holderConst 1 * (S * Real.sqrt S) := by
        rw [← hfac]
        exact mul_le_mul_of_nonneg_left hsq (holderConst_pos 1 (by norm_num)).le
    _ ≤ cubicSum u N := hholder

/-- `A = holderConst 1 = √(1/2)`. -/
theorem holderConst_one_eq : holderConst 1 = Real.sqrt (1/2) := by
  rw [holderConst]
  norm_num [dyadicWeight]

/-- `holderConst 1 = √(1/2) < 1`, so the inverted-Hölder constant is a genuine loss. -/
theorem holderConst_one_lt_one : holderConst 1 < 1 := by
  rw [holderConst_one_eq, show (1:ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- The blow-up coefficient `c = (27/28) · A · (7/10) · √(7/10)`, where `A = holderConst 1 = √(1/2)`
is the inverted-Hölder constant.  Numerically `c = 27√35/400 ≈ 0.39934`. -/
def blowupCoeff : ℝ := (27/28) * (holderConst 1 * (7/10) * Real.sqrt (7/10))

/-- `c > 0`. -/
theorem blowupCoeff_pos : 0 < blowupCoeff := by
  unfold blowupCoeff
  have hA : 0 < holderConst 1 := holderConst_pos 1 (by norm_num)
  have h7 : 0 < Real.sqrt (7/10) := Real.sqrt_pos.mpr (by norm_num)
  positivity

/-- The exact closed form of the coefficient: `c = (27/28)·√(1/2)·(7/10)·√(7/10) = 27√35/400`. -/
theorem blowupCoeff_eq : blowupCoeff = 27 * Real.sqrt 35 / 400 := by
  have h1 : holderConst 1 = Real.sqrt (1/2) := holderConst_one_eq
  rw [blowupCoeff, h1]
  have h2 : Real.sqrt (1/2) * Real.sqrt (7/10) = Real.sqrt (7/20) := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 1/2)]
    norm_num
  have h3 : Real.sqrt (7/20) = Real.sqrt 35 / 10 := by
    rw [show (7/20 : ℝ) = 35 / 100 by norm_num,
      Real.sqrt_div (by norm_num : (0:ℝ) ≤ 35), show Real.sqrt 100 = (10:ℝ) by norm_num]
  rw [show (27/28) * (Real.sqrt (1/2) * (7/10) * Real.sqrt (7/10))
      = (27/28) * ((7/10) * (Real.sqrt (1/2) * Real.sqrt (7/10))) by ring, h2, h3]
  ring

/-- **The Lyapunov derivative dominates `c · lyap · √lyap - 2ν·lyap`.**  This is
`lyap_deriv_ge` (`(27/28)·cubicSum - 2ν·lyap ≤ L'`) composed with `cubicSum_lower_bound`. -/
theorem lyap_deriv_ge_coeff (ν : ℝ) (hν : 0 ≤ ν) (μ : ℝ) (N : ℕ) (u θ : ℝ → ℤ → ℝ)
    (h : IsUnforcedTruncatedSolutionE ν μ 0 0 N u θ) {T : ℝ} (L' : ℝ → ℝ)
    (hderiv : ∀ t ∈ Set.Ico 0 T, HasDerivAt (fun s => lyap (u s) N (4/7)) (L' t) t)
    (hnn : ∀ t ∈ Set.Ico 0 T, ∀ k : ℤ, 0 ≤ u t k) (hN : 1 ≤ N) (t : ℝ)
    (ht : t ∈ Set.Ico 0 T) :
    blowupCoeff * (lyap (u t) N (4/7) * Real.sqrt (lyap (u t) N (4/7)))
      - 2 * ν * lyap (u t) N (4/7) ≤ L' t := by
  have hbase := lyap_deriv_ge ν hν μ N u θ h L' hderiv hnn hN t ht
  have hchain := cubicSum_lower_bound (u t) N (hnn t ht) (h.2.2 t).2.1
  have hcoef : blowupCoeff = (27/28) * (holderConst 1 * (7/10) * Real.sqrt (7/10)) := rfl
  have hstep : blowupCoeff
        * (lyap (u t) N (4/7) * Real.sqrt (lyap (u t) N (4/7)))
      ≤ (27/28) * cubicSum (u t) N := by
    rw [hcoef]
    calc (27/28) * (holderConst 1 * (7/10) * Real.sqrt (7/10))
            * (lyap (u t) N (4/7) * Real.sqrt (lyap (u t) N (4/7)))
        = (27/28) * (holderConst 1 * (7/10) * Real.sqrt (7/10)
            * (lyap (u t) N (4/7) * Real.sqrt (lyap (u t) N (4/7)))) := by ring
      _ ≤ (27/28) * cubicSum (u t) N :=
          mul_le_mul_of_nonneg_left hchain (by norm_num)
  linarith [hbase, hstep]

/-! ## 3. The threshold, the non-vanishing of `lyap`, and the capstone -/

/-- The critical initial size: `blowupThreshold ν = (2ν/c)²`.  The hypothesis
`blowupThreshold ν < lyap (u 0) N (4/7)` is exactly the engine's `hgap`, i.e. `2ν < c·√(lyap 0)`. -/
def blowupThreshold (ν : ℝ) : ℝ := (2 * ν / blowupCoeff) ^ 2

/-- The threshold is nonnegative. -/
theorem blowupThreshold_nonneg (ν : ℝ) : 0 ≤ blowupThreshold ν := by
  unfold blowupThreshold; positivity

/-- From `blowupThreshold ν < L₀`, `L₀` is positive. -/
theorem lyap_pos_of_gt_threshold {ν L₀ : ℝ} (h : blowupThreshold ν < L₀) : 0 < L₀ :=
  lt_of_le_of_lt (blowupThreshold_nonneg ν) h

/-- `blowupThreshold ν < L₀` gives the engine's `hgap`: `2ν < c·√L₀`. -/
theorem sqrt_gt_of_threshold {ν L₀ : ℝ} (h : blowupThreshold ν < L₀) :
    2 * ν < blowupCoeff * Real.sqrt L₀ := by
  have hc : 0 < blowupCoeff := blowupCoeff_pos
  have hL₀ : 0 < L₀ := lyap_pos_of_gt_threshold h
  have hspos : 0 < Real.sqrt L₀ := Real.sqrt_pos.mpr hL₀
  by_cases hx : 0 ≤ 2 * ν / blowupCoeff
  · have hlt : 2 * ν / blowupCoeff < Real.sqrt L₀ := by
      rw [← Real.sqrt_sq hx]
      exact Real.sqrt_lt_sqrt (by positivity) (by simpa [blowupThreshold] using h)
    calc 2 * ν = (2 * ν / blowupCoeff) * blowupCoeff := by field_simp
      _ < Real.sqrt L₀ * blowupCoeff := mul_lt_mul_of_pos_right hlt hc
      _ = blowupCoeff * Real.sqrt L₀ := by ring
  · have hx' : 2 * ν / blowupCoeff < 0 := lt_of_not_ge hx
    have h2ν : 2 * ν < 0 := by
      have hm := mul_lt_mul_of_pos_right hx' hc
      rw [div_mul_cancel₀ _ (ne_of_gt hc)] at hm
      simpa using hm
    have hpos' : 0 < blowupCoeff * Real.sqrt L₀ := mul_pos hc hspos
    linarith

/-- **`lyap` never vanishes.**  For `ν ≥ 0`, the chain gives
`lyap' ≥ c·lyap√lyap - 2ν·lyap ≥ -2ν·lyap`, so `t ↦ Real.exp (2|ν| t) * lyap (u t)` is
non-decreasing on `[0,t]`; hence `lyap (u 0) ≤ Real.exp (2|ν| t) * lyap (u t)` and therefore
`lyap (u t) > 0` whenever `lyap (u 0) > 0`. -/
theorem lyap_pos (ν : ℝ) (hν : 0 ≤ ν) (μ : ℝ) (N : ℕ) (u θ : ℝ → ℤ → ℝ)
    (h : IsUnforcedTruncatedSolutionE ν μ 0 0 N u θ) (h0 : ∀ k, 0 ≤ u 0 k)
    (hpos0 : 0 < lyap (u 0) N (4/7)) (hN : 1 ≤ N) (t : ℝ) (ht : 0 ≤ t) :
    0 < lyap (u t) N (4/7) := by
  set L : ℝ → ℝ := fun r => lyap (u r) N (4/7) with hL
  set L' : ℝ → ℝ := fun r => (4 * quadWeighted (u r) (N-1) - 2*ν*blowupNorm (u r) N)
    + (4/7) * correctionRHS ν (u r) N with hL'
  rcases eq_or_lt_of_le ht with ht0 | htpos
  · rw [← ht0]; exact hpos0
  -- The chain on `[0,t]`, obtained from the interval `[0, t+1)`.
  have hchain : ∀ s ∈ Set.Icc 0 t,
      blowupCoeff * (L s * Real.sqrt (L s)) - 2 * ν * L s ≤ L' s := by
    intro s hs
    exact lyap_deriv_ge_coeff ν hν μ N u θ h L'
      (fun r _ => lyap_hasDerivAt ν μ N u θ (4/7) h hN r)
      (fun r hr k => nonneg_of_nonneg ν μ hν 0 N u θ h h0 r hr.1 k) hN s
      (show s ∈ Set.Ico 0 (t + 1) from ⟨hs.1, by linarith [hs.2]⟩)
  have hderiv : ∀ s ∈ Set.Icc 0 t,
      HasDerivAt (fun r => Real.exp (2 * |ν| * r) * L r)
        (Real.exp (2 * |ν| * s) * (2 * |ν| * L s + L' s)) s := by
    intro s hs
    have hexp : HasDerivAt (fun r : ℝ => Real.exp (2 * |ν| * r))
        (Real.exp (2 * |ν| * s) * (2 * |ν|)) s := by
      have h := ((hasDerivAt_id s).const_mul (2 * |ν|)).exp
      simpa using h
    have hmul := hexp.mul (lyap_hasDerivAt ν μ N u θ (4/7) h hN s)
    have hval : Real.exp (2 * |ν| * s) * (2 * |ν|) * L s
        + Real.exp (2 * |ν| * s) * L' s
        = Real.exp (2 * |ν| * s) * (2 * |ν| * L s + L' s) := by ring
    rw [hval] at hmul
    exact hmul
  have hnn : ∀ s ∈ Set.Icc 0 t, 0 ≤ 2 * |ν| * L s + L' s := by
    intro s hs
    have hch := hchain s hs
    have hcub : 0 ≤ blowupCoeff * (L s * Real.sqrt (L s)) := by
      by_cases hLs : 0 ≤ L s
      · exact mul_nonneg blowupCoeff_pos.le (mul_nonneg hLs (Real.sqrt_nonneg _))
      · have hz : Real.sqrt (L s) = 0 := Real.sqrt_eq_zero_of_nonpos (le_of_lt (not_le.mp hLs))
        rw [hz, mul_zero, mul_zero]
    have habs : |ν| = ν := abs_of_nonneg hν
    rw [habs]
    nlinarith [hch, hcub]
  have hcont : ContinuousOn (fun r => -(Real.exp (2 * |ν| * r) * L r)) (Set.Icc 0 t) :=
    fun s hs => ((hderiv s hs).neg.continuousAt).continuousWithinAt
  have hmono : ∀ s ∈ Set.Icc 0 t,
      -(Real.exp (2 * |ν| * s) * (2 * |ν| * L s + L' s)) ≤ 0 :=
    fun s hs => neg_nonpos.mpr (mul_nonneg (Real.exp_pos _).le (hnn s hs))
  have hanti := le_of_deriv_nonpos_of_hasDerivAt htpos hcont
    (fun s hs => (hderiv s hs).neg) hmono
  have h0' : -(Real.exp (2 * |ν| * 0) * L 0) = -L 0 := by rw [mul_zero]; simp
  rw [h0'] at hanti
  have hle : L 0 ≤ Real.exp (2 * |ν| * t) * L t := by linarith [hanti]
  have hleft : 0 < L 0 := by rw [hL]; exact hpos0
  exact pos_of_mul_pos_right (lt_of_lt_of_le hleft hle) (Real.exp_pos _).le

/-- **THE CAPSTONE: finite-time blow-up at dissipation degree `e = 0`.**  There is no global
solution of the truncated dyadic model

`u_k' = 2^k (u_{k-1}² - 2 u_k u_{k+1}) - ν u_k`,  `u_{-1} = u_N = 0`,

with `ν ≥ 0`, nonnegative initial data `u 0` and initial Lyapunov value above the threshold
`(2ν/c)²` (where `c = blowupCoeff = 27√35/400`): the Lyapunov functional is forced to infinity in
finite time, so the solution cannot exist for all real `t`. -/
theorem no_global_solution_degree_zero (ν : ℝ) (hν : 0 ≤ ν) (μ : ℝ) (N : ℕ) (hN : 1 ≤ N)
    (u θ : ℝ → ℤ → ℝ) (h : IsUnforcedTruncatedSolutionE ν μ 0 0 N u θ)
    (h0 : ∀ k, 0 ≤ u 0 k) (hlarge : blowupThreshold ν < lyap (u 0) N (4/7)) :
    False := by
  set y₀ : ℝ := lyap (u 0) N (4/7) with hy₀def
  have hy₀pos : 0 < y₀ := by rw [hy₀def]; exact lyap_pos_of_gt_threshold hlarge
  have hgap : 2 * ν < blowupCoeff * Real.sqrt y₀ := by
    rw [hy₀def]; exact sqrt_gt_of_threshold hlarge
  set T : ℝ := 2 / (blowupCoeff * Real.sqrt y₀ - 2 * ν) + 1 with hTdef
  have hTpos : 0 < T := by rw [hTdef]; positivity
  have hTgt : 2 / (blowupCoeff * Real.sqrt y₀ - 2 * ν) < T := by rw [hTdef]; linarith
  set L' : ℝ → ℝ := fun t => (4 * quadWeighted (u t) (N-1) - 2*ν*blowupNorm (u t) N)
    + (4/7) * correctionRHS ν (u t) N with hL'def
  have hderiv : ∀ t ∈ Set.Icc 0 T, HasDerivAt (fun s => lyap (u s) N (4/7)) (L' t) t :=
    fun t _ => lyap_hasDerivAt ν μ N u θ (4/7) h hN t
  have hineq : ∀ t ∈ Set.Icc 0 T,
      blowupCoeff * (lyap (u t) N (4/7) * Real.sqrt (lyap (u t) N (4/7)))
        - 2 * ν * lyap (u t) N (4/7) ≤ L' t := by
    intro t ht
    exact lyap_deriv_ge_coeff ν hν μ N u θ h L'
      (fun s _ => lyap_hasDerivAt ν μ N u θ (4/7) h hN s)
      (fun s hs k => nonneg_of_nonneg ν μ hν 0 N u θ h h0 s hs.1 k) hN t
      (show t ∈ Set.Ico 0 (T + 1) from ⟨ht.1, by linarith [ht.2]⟩)
  have hpos : ∀ t ∈ Set.Icc 0 T, 0 < lyap (u t) N (4/7) :=
    fun t ht => lyap_pos ν hν μ N u θ h h0 (hy₀def ▸ hy₀pos) hN t ht.1
  have hy0 : lyap (u 0) N (4/7) = y₀ := hy₀def.symm
  have := le_of_deriv_ge_mul_sqrt_sub (fun t => lyap (u t) N (4/7)) L'
    hν blowupCoeff_pos hy₀pos hTpos hderiv hineq hpos hy0 hgap
  linarith

/-! ## 4. Non-vacuity and sanity checks -/

/-- The single-shell ladder `δ₀`: `u_0 = 1`, `u_k = 0` for `k ≠ 0`. -/
def deltaZero (k : ℤ) : ℝ := if k = 0 then 1 else 0

/-- The single-mode reversed-Hölder inequality `A · 1 · √1 ≤ 1` with `A = holderConst 1`. -/
example : holderConst 1 * (1 * Real.sqrt 1) ≤ (1:ℝ) := by
  have h := holderConst_le_one 1 (by norm_num)
  simpa using h

/-- **Single-mode check of `inverted_holder`** at `e = 0`, `N = 1`, `u = δ₀`: the two sides of
`inverted_holder` are `A·1·√1 = √(1/2) ≈ 0.7071` and `1`, so the inequality holds and the
resulting threshold `2/(c√1 - 0) = 800/(27√35) ≈ 5.01` is finite. -/
example :
    holderConst (1 - 3*0)
      * ((∑ k ∈ Finset.range 1, dyadicWeight (((0:ℤ) + 1) * (k:ℤ)) * (deltaZero (k:ℤ))^2)
          * Real.sqrt (∑ k ∈ Finset.range 1,
              dyadicWeight (((0:ℤ) + 1) * (k:ℤ)) * (deltaZero (k:ℤ))^2))
      ≤ ∑ k ∈ Finset.range 1, dyadicWeight (2 * (k:ℤ)) * |deltaZero (k:ℤ)|^3 :=
  inverted_holder 0 le_rfl deltaZero 1

/-- Evaluation of the single-mode sums: both are `1`. -/
example :
    (∑ k ∈ Finset.range 1, dyadicWeight (((0:ℤ) + 1) * (k:ℤ)) * (deltaZero (k:ℤ))^2) = 1
      ∧ (∑ k ∈ Finset.range 1, dyadicWeight (2 * (k:ℤ)) * |deltaZero (k:ℤ)|^3) = 1 := by
  constructor <;> norm_num [deltaZero, dyadicWeight, Finset.sum_range_succ]

/-- **The exact coefficient**: `c = 27√35/400 ≈ 0.3993`. -/
example : blowupCoeff = 27 * Real.sqrt 35 / 400 := blowupCoeff_eq

/-- **The engine's bound at concrete data**: with `ν = 0`, `y₀ = 1` it reads
`T ≤ 2/blowupCoeff = 800/(27√35)`. -/
theorem engine_bound_concrete :
    2 / (blowupCoeff * Real.sqrt 1 - 2 * 0) = 800 / (27 * Real.sqrt 35) := by
  rw [blowupCoeff_eq, Real.sqrt_one]
  field_simp
  ring

/-- The concrete bound is a positive (finite) real number. -/
example : 0 < 2 / (blowupCoeff * Real.sqrt 1 - 2 * 0) := by
  rw [engine_bound_concrete]
  positivity

/-- The bound is even `> 4`: `800/(27√35) > 800/162 = 400/81 > 4` since `√35 < 6`. -/
example : 4 < 2 / (blowupCoeff * Real.sqrt 1 - 2 * 0) := by
  rw [engine_bound_concrete]
  have h35 : Real.sqrt 35 < 6 := by
    have h : Real.sqrt 35 < Real.sqrt 36 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    rwa [show Real.sqrt 36 = (6:ℝ) by norm_num] at h
  have hpos : 0 < 27 * Real.sqrt 35 := by positivity
  have hlt : 27 * Real.sqrt 35 < 162 := by linarith
  have h1 : (1:ℝ) / 162 < 1 / (27 * Real.sqrt 35) := one_div_lt_one_div_of_lt hpos hlt
  have h2 := mul_lt_mul_of_pos_left h1 (by norm_num : (0:ℝ) < 800)
  have h3 : (800:ℝ) / 162 = 400/81 := by norm_num
  rw [div_eq_mul_one_div, div_eq_mul_one_div]
  linarith [h2, h3]

/-- The indicator ladder on the first two shells: `u_0 = u_1 = 1`, `u_k = 0` otherwise. -/
def ladderTwo (k : ℤ) : ℝ := if 0 ≤ k ∧ k < 2 then 1 else 0

/-- The indicator ladder is nonnegative with `u(-1) = u(2) = 0`. -/
example : ladderTwo (-1) = 0 ∧ ladderTwo 2 = 0 ∧ (∀ k : ℤ, 0 ≤ ladderTwo k) := by
  refine ⟨by norm_num [ladderTwo], by norm_num [ladderTwo], ?_⟩
  intro k; unfold ladderTwo; split <;> norm_num

/-- Evaluation: `lyap ladderTwo 2 (4/7) = 25/7 > 0`. -/
theorem lyap_ladderTwo : lyap ladderTwo 2 (4/7) = 25/7 := by
  norm_num [lyap, blowupNorm, correction, ladderTwo, dyadicWeight, Finset.sum_range_succ]

/-- **`hlarge` is satisfiable.**  With `ν = 0` and the indicator ladder on shells `0,1`,
`blowupThreshold 0 = 0 < 25/7 = lyap ladderTwo 2 (4/7)`. -/
theorem threshold_satisfiable : blowupThreshold 0 < lyap ladderTwo 2 (4/7) := by
  rw [lyap_ladderTwo, blowupThreshold]
  norm_num

/-- The same satisfiability statement with the threshold written out as `(2ν/c)²`. -/
example : (2 * (0:ℝ) / blowupCoeff) ^ 2 < lyap ladderTwo 2 (4/7) :=
  threshold_satisfiable

end Cascade

/-! ## 5. Axiom audit -/

#print axioms Cascade.le_of_deriv_ge_mul_sqrt_sub
#print axioms Cascade.not_exists_solution_of_gt_sub
#print axioms Cascade.le_of_deriv_ge_mul_sqrt_sub_nonpos
#print axioms Cascade.engine_false_without_nonneg
#print axioms Cascade.sum_shift_sq_le
#print axioms Cascade.correction_le_three_quarters
#print axioms Cascade.blowupNorm_ge_lyap
#print axioms Cascade.cubicSum_lower_bound
#print axioms Cascade.blowupCoeff
#print axioms Cascade.blowupCoeff_pos
#print axioms Cascade.blowupCoeff_eq
#print axioms Cascade.lyap_deriv_ge_coeff
#print axioms Cascade.blowupThreshold
#print axioms Cascade.blowupThreshold_nonneg
#print axioms Cascade.lyap_pos_of_gt_threshold
#print axioms Cascade.sqrt_gt_of_threshold
#print axioms Cascade.lyap_pos
#print axioms Cascade.no_global_solution_degree_zero
#print axioms Cascade.deltaZero
#print axioms Cascade.holderConst_one_eq
#print axioms Cascade.holderConst_one_lt_one
#print axioms Cascade.engine_bound_concrete
#print axioms Cascade.ladderTwo
#print axioms Cascade.lyap_ladderTwo
#print axioms Cascade.threshold_satisfiable
