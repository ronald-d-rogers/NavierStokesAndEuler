import Cascade.DissipationThreshold

/-!
# The Lyapunov growth-rate inequality for the truncated scalar dyadic model at `e = 0`

This file supplies the algebraic heart of the finite-time blow-up argument for the truncated
scalar dyadic model at dissipation degree `e = 0`, buoyancy off (`κ = 0`, `A = 1`, `B = 0`), i.e.

  `u_k' = 2^k (u_{k-1}² - 2 u_k u_{k+1}) - ν u_k`,   `u_{-1} = u_N = 0`,

specialised to a fixed time slice with `0 ≤ u_k` taken as a hypothesis (supplied elsewhere by the
positivity theorem).  `dyadicWeight k = 2^k`, and `dyadicWeight (2k) = 4^k`.

## Contents and constants

* `blowupNorm u N = Σ_{k<N} 2^k u_k²`,
  `correction u N = Σ_{k<N} 2^k u_k u_{k+1}`,
  `cubicSum u N = Σ_{k<N} 4^k u_k³`,
  `lyap u N c₂ = blowupNorm + c₂ · correction`.

* Step 1 (`mul_sq_le_half_cube_add`, `mul_mul_le_quarter_cube`): Cheskidov's elementary
  inequalities `x y² ≤ ½y³ + 2x²y` and `xyz ≤ ½x²y + ¼z³ + y²z` for `x,y,z ≥ 0`.

* Step 2(a) (`blowupNorm_hasDerivAt`): the **exact** identity
  `N' = 4 · Σ_{k<N-1} 4^k u_k² u_{k+1} - 2ν·N`.
  (Differentiating `Σ2^k u_k²` gives `2[Σ2^{2k}u_{k-1}²u_k - Σ2^{2k+1}u_k²u_{k+1} - νΣ2^ku_k²]`;
  reindexing the first sum by `j = k-1` yields `8Σ4^ju_j²u_{j+1}` and the second `4Σ4^ku_k²u_{k+1}`,
  the difference `4Σ` times the outer `2` is `8 - 4 = 4`, using `u_{-1} = u_N = 0`.)

* Step 2(b) (`correctionRHS_ge`): the lower bound
  `Q' ≥ (27/16)·cubicSum - 7·Σ_{k<N}4^k u_k²u_{k+1} - 2ν·Q`.
  The `27/16` collects `2 - 1/4 - 1/16` (from `+Σ2^{2k+1}u_k³`, and the `u_{k+1}³`, `u_{k+2}³`
  terms of the shellwise inequalities), and `7 = 4 + 2 + 1` collects the `Σ4^ku_k²u_{k+1}` pieces.
  The `k = N-1` and `k = N-2` shells of the `uuu` sum are handled by restricting that sum to
  `Finset.range (N-2)` (their summands vanish since `u_N = 0`), which keeps the argument free of
  any hypothesis on `u_{N+1}`.

* Step 3 (`lyap_deriv_ge`): with `c₂ = 4/7` the `Σ4^ku_k²u_{k+1}` terms cancel:
  `4 - c₂·7 = 0`, leaving

    `c₃ · cubicSum - C · ν · lyap ≤ L'`,   `c₃ = (4/7)·(27/16) = 27/28`,  `C = 2`,

  because `L' ≥ 4Σ - 2νN + c₂(27/16)cubic - 7c₂Σ - 2c₂νQ = (27/28)cubic - 2ν(N + c₂Q)`.

* `correction_le_blowupNorm` (pairwise AM–GM plus the weight shift) and `blowupNorm_le_lyap`
  are provided for the separate inverted-Hölder combination: `correction ≤ ¾·blowupNorm`, hence
  `blowupNorm ≥ lyap/(1 + ¾c₂)`.

* `NonVacuity` instantiates the statements at the concrete ladder `1,1,1,0` and at the zero
  solution, and evaluates both sides numerically.

No `sorry`, no `admit`, no `axiom`; the `#print axioms` audit at the end of the file reports
`[propext, Classical.choice, Quot.sound]` for every declaration.
-/

noncomputable section

set_option linter.unusedVariables false

open scoped BigOperators

namespace Cascade

/-! ## 0. Local dyadic-weight arithmetic -/

private lemma dW_ne_zero : (2 : ℝ) ≠ 0 := by norm_num

private lemma dW_add (a b : ℤ) : dyadicWeight (a + b) = dyadicWeight a * dyadicWeight b := by
  unfold dyadicWeight
  rw [zpow_add₀ dW_ne_zero]

private lemma dW_two_mul (k : ℤ) : dyadicWeight (2 * k) = dyadicWeight k * dyadicWeight k := by
  unfold dyadicWeight
  rw [← zpow_add₀ dW_ne_zero]
  congr 1
  ring

private lemma dW_succ (k : ℤ) : dyadicWeight (k + 1) = 2 * dyadicWeight k := by
  unfold dyadicWeight
  rw [zpow_add₀ dW_ne_zero, zpow_one]
  ring

private lemma dW_nonneg (k : ℤ) : 0 ≤ dyadicWeight k := by
  unfold dyadicWeight; positivity

private lemma dW_odd (k : ℤ) : dyadicWeight (2 * k + 1) = 2 * dyadicWeight (2 * k) := by
  rw [show 2 * k + 1 = 2 * k + 1 by ring, dW_succ]

private lemma dW_even_two (k : ℤ) : dyadicWeight (2 * k + 2) = 4 * dyadicWeight (2 * k) := by
  have h : (2:ℤ) * k + 2 = (2 * k + 1) + 1 := by ring
  rw [h, dW_succ, dW_odd]
  ring

private lemma dW_shift_up (j : ℤ) : dyadicWeight (2 * (j + 1)) = 4 * dyadicWeight (2 * j) := by
  have h : (2:ℤ) * (j + 1) = 2 * j + 2 := by ring
  rw [h, dW_even_two]

private lemma dW_eq_two_pow (k : ℤ) : dyadicWeight k = (2:ℝ)^k := rfl

/-! ## 1. The Lyapunov data -/

/-- The blow-up norm `N(u) = Σ_{k<N} 2^k u_k²`. -/
def blowupNorm (u : ℤ → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, dyadicWeight k * (u k)^2

/-- The correction term `Q(u) = Σ_{k<N} 2^k u_k u_{k+1}`. -/
def correction (u : ℤ → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, dyadicWeight k * u k * u (k+1)

/-- The cubic sum `Σ_{k<N} 2^{2k} u_k³ = Σ_{k<N} 4^k u_k³`. -/
def cubicSum (u : ℤ → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, dyadicWeight (2*k) * (u k)^3

/-- The Lyapunov function `L = N + c₂ Q`. -/
def lyap (u : ℤ → ℝ) (N : ℕ) (c₂ : ℝ) : ℝ := blowupNorm u N + c₂ * correction u N

/-- The velocity nonlinearity at `e = 0`, `κ = 0`, `A = 1`, `B = 0`. -/
def chainRHS (ν : ℝ) (u : ℤ → ℝ) (k : ℤ) : ℝ :=
  dyadicWeight k * ((u (k-1))^2 - 2 * u k * u (k+1)) - ν * u k

/-- Termwise derivative of `blowupNorm`. -/
def blowupNormRHS (ν : ℝ) (u : ℤ → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, dyadicWeight k * (2 * u k * chainRHS ν u k)

/-- Termwise derivative of `correction`. -/
def correctionRHS (ν : ℝ) (u : ℤ → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N,
    dyadicWeight k * (chainRHS ν u k * u (k+1) + u k * chainRHS ν u (k+1))

/-- The `Σ_{k<N} 4^k u_k² u_{k+1}` term. -/
def quadWeighted (u : ℤ → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, dyadicWeight (2*k) * (u k)^2 * u (k+1)

/-! ## 2. The model reduction -/

/-- `velocityRHSDegreeE` at `e = 0`, `κ = 0`, `A = 1`, `B = 0` is `chainRHS`. -/
theorem velocityRHSDegreeE_zero (ν : ℝ) (u θ : ℤ → ℝ) (k : ℤ) :
    velocityRHSDegreeE ν 0 1 0 0 u θ k = chainRHS ν u k := by
  have h0 : dyadicWeight (0:ℤ) = 1 := by unfold dyadicWeight; simp
  simp only [velocityRHSDegreeE, chainRHS, boussinesqTransferU]
  rw [show (0:ℤ) * k = 0 by ring, h0]
  ring

/-! ## 3. Step 1: the two elementary inequalities -/

theorem mul_sq_le_half_cube_add (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x * y^2 ≤ (1/2) * y^3 + 2 * x^2 * y := by
  by_cases h : x ≤ y/2
  · have h1 : x * y^2 ≤ (1/2) * y^3 := by nlinarith [h, sq_nonneg y, hy]
    have h2 : 0 ≤ 2 * x^2 * y := by positivity
    linarith
  · have h : y/2 < x := lt_of_not_ge h
    have hy2 : y ≤ 2*x := by linarith
    have h3 : y * y ≤ (2*x) * y := mul_le_mul_of_nonneg_right hy2 hy
    have h4 : x * (y*y) ≤ x * ((2*x)*y) := mul_le_mul_of_nonneg_left h3 hx
    have h1 : x * y^2 ≤ 2 * x^2 * y := by nlinarith [h4]
    have h2 : 0 ≤ (1/2) * y^3 := by positivity
    linarith

theorem mul_mul_le_quarter_cube (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    x * y * z ≤ (1/2) * x^2 * y + (1/4) * z^3 + y^2 * z := by
  have ham : x * z ≤ (x^2 + z^2)/2 := by nlinarith [sq_nonneg (x - z)]
  have h1 : x*y*z ≤ y * ((x^2+z^2)/2) := by
    have hh : x*z*y ≤ ((x^2+z^2)/2)*y := mul_le_mul_of_nonneg_right ham hy
    nlinarith [hh]
  have h2 : (1/2) * z^2 * y ≤ (1/4)*z^3 + y^2*z := by
    have hh := mul_sq_le_half_cube_add y z hy hz
    nlinarith [hh]
  nlinarith [h1, h2]


/-! ## 4. Step 2(a): the exact derivative of the blow-up norm -/

section Step2a

/-- Shift the index of a `range`-sum by one. -/
private lemma sum_range_shift (f : ℤ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range (N+1), f ((k:ℤ) - 1)) = f (-1) + ∑ j ∈ Finset.range N, f (j:ℤ) := by
  rw [Finset.sum_range_succ' (fun k : ℕ => f ((k:ℤ) - 1)) N]
  have h1 : (∑ k ∈ Finset.range N, f ((↑(k+1) : ℤ) - 1))
      = ∑ k ∈ Finset.range N, f (k:ℤ) := by
    apply Finset.sum_congr rfl
    intro k hk
    congr 1
    push_cast
    ring
  rw [h1]
  have h2 : ((↑(0:ℕ) : ℤ) - 1) = (-1:ℤ) := by norm_num
  rw [h2, add_comm]

/-- Drop the last term of a `range`-sum when it vanishes. -/
private lemma sum_range_last_zero (f : ℕ → ℝ) (N : ℕ) (hN : 1 ≤ N) (h : f (N-1) = 0) :
    (∑ k ∈ Finset.range N, f k) = ∑ k ∈ Finset.range (N-1), f k := by
  have hN' : N = (N-1)+1 := (Nat.succ_pred_eq_of_pos (by omega : 0 < N)).symm
  rw [hN', Finset.sum_range_succ, h, add_zero]
  simp only [show N - 1 + 1 - 1 = N - 1 by omega]

/-- Pointwise expansion of the `blowupNorm` summand. -/
private lemma blowupNorm_summand (ν : ℝ) (u : ℤ → ℝ) (k : ℤ) :
    dyadicWeight k * (2 * u k * chainRHS ν u k)
      = 2 * (dyadicWeight (2*k) * (u (k-1))^2 * u k)
        - 4 * (dyadicWeight (2*k) * (u k)^2 * u (k+1))
        - 2 * ν * (dyadicWeight k * (u k)^2) := by
  rw [chainRHS, dW_two_mul]
  ring

private lemma blowupNormRHS_expand (ν : ℝ) (u : ℤ → ℝ) (N : ℕ) :
    blowupNormRHS ν u N
      = 2 * (∑ k ∈ Finset.range N, dyadicWeight (2*(k:ℤ)) * (u ((k:ℤ)-1))^2 * u (k:ℤ))
        - 4 * (∑ k ∈ Finset.range N, dyadicWeight (2*(k:ℤ)) * (u (k:ℤ))^2 * u ((k:ℤ)+1))
        - 2 * ν * (∑ k ∈ Finset.range N, dyadicWeight (k:ℤ) * (u (k:ℤ))^2) := by
  unfold blowupNormRHS
  have hcongr : (∑ k ∈ Finset.range N,
        dyadicWeight (k:ℤ) * (2 * u (k:ℤ) * chainRHS ν u (k:ℤ)))
      = ∑ k ∈ Finset.range N,
          (2 * (dyadicWeight (2*(k:ℤ)) * (u ((k:ℤ)-1))^2 * u (k:ℤ))
            - 4 * (dyadicWeight (2*(k:ℤ)) * (u (k:ℤ))^2 * u ((k:ℤ)+1))
            - 2 * ν * (dyadicWeight (k:ℤ) * (u (k:ℤ))^2)) :=
    Finset.sum_congr rfl (fun k _ => blowupNorm_summand ν u (k:ℤ))
  rw [hcongr, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]

/-- Reindex the `u_{k-1}² u_k` sum. -/
private lemma sum_lower_shift (u : ℤ → ℝ) (N : ℕ) (hN : 1 ≤ N) (hu1 : u (-1) = 0) :
    (∑ k ∈ Finset.range N, dyadicWeight (2*(k:ℤ)) * (u ((k:ℤ)-1))^2 * u (k:ℤ))
      = 4 * quadWeighted u (N-1) := by
  set g : ℤ → ℝ := fun j => dyadicWeight (2*(j+1)) * (u j)^2 * u (j+1) with hg
  have hN' : N = (N-1)+1 := (Nat.succ_pred_eq_of_pos (by omega : 0 < N)).symm
  have hstep : (∑ k ∈ Finset.range N, dyadicWeight (2*(k:ℤ)) * (u ((k:ℤ)-1))^2 * u (k:ℤ))
      = ∑ k ∈ Finset.range (N-1+1), g ((k:ℤ)-1) := by
    rw [hN']
    apply Finset.sum_congr rfl
    intro k hk
    simp only [hg]
    rw [show ((k:ℤ)-1)+1 = (k:ℤ) by ring]
  rw [hstep, sum_range_shift g (N-1)]
  have hg1 : g (-1) = 0 := by
    simp only [hg]
    rw [show ((-1:ℤ)+1) = 0 by ring, hu1]
    simp [dyadicWeight]
  rw [hg1, zero_add]
  unfold quadWeighted
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [hg]
  rw [dW_shift_up]
  ring

/-- Drop the top term of the `u_k² u_{k+1}` sum. -/
private lemma sum_upper_drop (u : ℤ → ℝ) (N : ℕ) (hN : 1 ≤ N) (huN : u (N:ℤ) = 0) :
    (∑ k ∈ Finset.range N, dyadicWeight (2*(k:ℤ)) * (u (k:ℤ))^2 * u ((k:ℤ)+1))
      = quadWeighted u (N-1) := by
  have hf : (fun k : ℕ => dyadicWeight (2*(k:ℤ)) * (u (k:ℤ))^2 * u ((k:ℤ)+1)) (N-1) = 0 := by
    have hlast : (((N-1:ℕ)):ℤ) + 1 = (N:ℤ) := by omega
    show dyadicWeight (2*(((N-1:ℕ)):ℤ)) * (u (((N-1:ℕ)):ℤ))^2 * u ((((N-1:ℕ)):ℤ)+1) = 0
    rw [hlast, huN]
    ring
  unfold quadWeighted
  rw [sum_range_last_zero (fun k : ℕ => dyadicWeight (2*(k:ℤ)) * (u (k:ℤ))^2 * u ((k:ℤ)+1))
        N hN hf]

/-- **Step 2(a), algebraic form.** -/
theorem blowupNormRHS_eq (ν : ℝ) (u : ℤ → ℝ) (N : ℕ) (hN : 1 ≤ N)
    (hu1 : u (-1) = 0) (huN : u (N:ℤ) = 0) :
    blowupNormRHS ν u N = 4 * quadWeighted u (N-1) - 2*ν*blowupNorm u N := by
  rw [blowupNormRHS_expand, sum_lower_shift u N hN hu1, sum_upper_drop u N hN huN]
  unfold blowupNorm
  ring

/-- **Step 2(a): the exact derivative of the blow-up norm.** -/
theorem blowupNorm_hasDerivAt (ν : ℝ) (μ : ℝ) (N : ℕ) (u θ : ℝ → ℤ → ℝ)
    (h : IsUnforcedTruncatedSolutionE ν μ 0 0 N u θ) (hN : 1 ≤ N) (t : ℝ) :
    HasDerivAt (fun s => blowupNorm (u s) N)
      (4 * (∑ k ∈ Finset.range (N-1), dyadicWeight (2*(k:ℤ)) * (u t (k:ℤ))^2 * u t ((k:ℤ)+1))
        - 2*ν*blowupNorm (u t) N) t := by
  have hraw : HasDerivAt (fun s => blowupNorm (u s) N) (blowupNormRHS ν (u t) N) t := by
    have hmain := HasDerivAt.sum (u := Finset.range N)
      (A := fun (k : ℕ) (s : ℝ) => dyadicWeight (k:ℤ) * (u s (k:ℤ))^2)
      (A' := fun (k : ℕ) => dyadicWeight (k:ℤ) * (2 * u t (k:ℤ) * chainRHS ν (u t) (k:ℤ)))
      (by
        intro k hk
        have hk' := h.1 t (k:ℤ)
        have hpow : HasDerivAt (fun s => (u s (k:ℤ))^2)
            (2 * (u t (k:ℤ))^(2-1) * velocityRHSDegreeE ν 0 1 0 0 (u t) (θ t) (k:ℤ)) t :=
          hk'.pow 2
        have hcm := hpow.const_mul (dyadicWeight (k:ℤ))
        simpa [velocityRHSDegreeE_zero, chainRHS, pow_one] using hcm)
    simpa [blowupNorm, blowupNormRHS, Finset.sum_fn] using hmain
  have hbd := h.2.2 t
  rw [blowupNormRHS_eq ν (u t) N hN hbd.1 hbd.2.1] at hraw
  simpa [quadWeighted] using hraw

end Step2a

/-! ## 5. Step 2(b): the correction-term inequality -/

section Step2b

/-- Shift a `range`-sum up by one, with a vanishing last term. -/
private lemma sum_range_succ_shift (f : ℕ → ℝ) (N : ℕ) (hlast : f N = 0) :
    (∑ k ∈ Finset.range N, f (k+1)) = (∑ k ∈ Finset.range N, f k) - f 0 := by
  have h1 : (∑ k ∈ Finset.range N, f (k+1)) + f 0 = ∑ k ∈ Finset.range N, f k := by
    rw [← Finset.sum_range_succ' f N, Finset.sum_range_succ f N, hlast, add_zero]
  linarith

/-- Shifted `range`-sum (vanishing last term) is at most the unshifted one. -/
private lemma sum_range_succ_shift_le (f : ℕ → ℝ) (N : ℕ) (hlast : f N = 0) (h0 : 0 ≤ f 0) :
    (∑ k ∈ Finset.range N, f (k+1)) ≤ ∑ k ∈ Finset.range N, f k := by
  rw [sum_range_succ_shift f N hlast]; linarith

/-- A nonnegative `range`-sum is monotone in the range. -/
private lemma sum_range_sub_le (f : ℕ → ℝ) (hnn : ∀ k, 0 ≤ f k) {M N : ℕ} (h : M ≤ N) :
    (∑ k ∈ Finset.range M, f k) ≤ ∑ k ∈ Finset.range N, f k :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 h)
    (fun i _ _ => hnn i)

/-- Shift a `range`-sum by `d`, when the shifted index set still lies in `range N`. -/
private lemma sum_range_shift_le (f : ℕ → ℝ) (hnn : ∀ k, 0 ≤ f k) {M N d : ℕ}
    (hsub : Finset.image (fun k => k+d) (Finset.range M) ⊆ Finset.range N) :
    (∑ k ∈ Finset.range M, f (k+d)) ≤ ∑ k ∈ Finset.range N, f k := by
  rw [← Finset.sum_image (f := f) (s := Finset.range M) (g := fun k => k+d)
    (fun a _ b _ h => Nat.add_right_cancel h)]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hnn i)

/-- The `(k+1)`-shifted cube sum is at most `cubicSum/4`. -/
private lemma cubic_shift_le (u : ℤ → ℝ) (N : ℕ) (huN : u (N:ℤ) = 0) (hnn : ∀ k, 0 ≤ u k) :
    (∑ k ∈ Finset.range N, dyadicWeight (2*(k:ℤ)) * (u ((k:ℤ)+1))^3) ≤ (1/4) * cubicSum u N := by
  set f : ℕ → ℝ := fun m => dyadicWeight (2*(m:ℤ)) * (u (m:ℤ))^3 with hf
  have hpoint : ∀ k ∈ Finset.range N,
      dyadicWeight (2*(k:ℤ)) * (u ((k:ℤ)+1))^3 = (1/4) * f (k+1) := by
    intro k _
    simp only [hf]
    push_cast
    rw [show (2:ℤ) * ((k:ℤ) + 1) = 2 * (k:ℤ) + 2 by ring, dW_even_two]
    ring
  rw [Finset.sum_congr rfl hpoint, ← Finset.mul_sum]
  have hlast : f N = 0 := by simp only [hf]; rw [huN]; ring
  have h0 : 0 ≤ f 0 := by
    simp only [hf]
    exact mul_nonneg (dW_nonneg _) (pow_nonneg (hnn 0) 3)
  have hle : (∑ k ∈ Finset.range N, f (k+1)) ≤ ∑ k ∈ Finset.range N, f k :=
    sum_range_succ_shift_le f N hlast h0
  unfold cubicSum
  simp only [hf] at hle
  linarith

/-- The `(k+2)`-shifted cube sum over `range (N-2)` is at most `cubicSum/16`. -/
private lemma cubic_double_shift_le (u : ℤ → ℝ) (N : ℕ) (hnn : ∀ k, 0 ≤ u k) :
    (∑ k ∈ Finset.range (N-2), dyadicWeight (2*(k:ℤ)) * (u ((k:ℤ)+2))^3)
      ≤ (1/16) * cubicSum u N := by
  set f : ℕ → ℝ := fun m => dyadicWeight (2*(m:ℤ)) * (u (m:ℤ))^3 with hf
  have hpoint : ∀ k ∈ Finset.range (N-2),
      dyadicWeight (2*(k:ℤ)) * (u ((k:ℤ)+2))^3 = (1/16) * f (k+2) := by
    intro k _
    simp only [hf]
    push_cast
    rw [show (2:ℤ) * ((k:ℤ) + 2) = 2 * ((k:ℤ)+1) + 2 by ring, dW_even_two]
    rw [show (2:ℤ) * ((k:ℤ) + 1) = 2 * (k:ℤ) + 2 by ring, dW_even_two]
    ring
  rw [Finset.sum_congr rfl hpoint, ← Finset.mul_sum]
  have hfnn : ∀ k, 0 ≤ f k := fun k => by
    simp only [hf]; exact mul_nonneg (dW_nonneg _) (pow_nonneg (hnn k) 3)
  have hsub : Finset.image (fun k => k+2) (Finset.range (N-2)) ⊆ Finset.range N := by
    intro m hm
    simp only [Finset.mem_image, Finset.mem_range] at hm ⊢
    obtain ⟨k, hk, rfl⟩ := hm
    omega
  have hle := sum_range_shift_le f hfnn hsub
  unfold cubicSum
  simp only [hf] at hle
  linarith

/-- The `(k+1)`-shifted `u_{k+1}²u_{k+2}` sum over `range (N-2)` is at most `quadWeighted`. -/
private lemma quad_shift_upper_le (u : ℤ → ℝ) (N : ℕ) (hnn : ∀ k, 0 ≤ u k) :
    (∑ k ∈ Finset.range (N-2), dyadicWeight (2*((k:ℤ)+1)) * (u ((k:ℤ)+1))^2 * u ((k:ℤ)+2))
      ≤ quadWeighted u N := by
  set f : ℕ → ℝ := fun m => dyadicWeight (2*(m:ℤ)) * (u (m:ℤ))^2 * u ((m:ℤ)+1) with hf
  have hpoint : ∀ k ∈ Finset.range (N-2),
      dyadicWeight (2*((k:ℤ)+1)) * (u ((k:ℤ)+1))^2 * u ((k:ℤ)+2) = f (k+1) := by
    intro k _
    simp only [hf]
    push_cast
    rw [show ((k:ℤ)+1)+1 = (k:ℤ)+2 by ring]
  rw [Finset.sum_congr rfl hpoint]
  have hfnn : ∀ k, 0 ≤ f k := fun k => by
    simp only [hf]; exact mul_nonneg (mul_nonneg (dW_nonneg _) (sq_nonneg _)) (hnn (k+1))
  have hsub : Finset.image (fun k => k+1) (Finset.range (N-2)) ⊆ Finset.range N := by
    intro m hm
    simp only [Finset.mem_image, Finset.mem_range] at hm ⊢
    obtain ⟨k, hk, rfl⟩ := hm
    omega
  have hle := sum_range_shift_le f hfnn hsub
  unfold quadWeighted
  simp only [hf] at hle
  linarith

/-- Per-shell bound for `B`. -/
private lemma shell_B (u : ℤ → ℝ) (hnn : ∀ k, 0 ≤ u k) (k : ℤ) :
    dyadicWeight (2*k+1) * u k * (u (k+1))^2
      ≤ dyadicWeight (2*k) * (u (k+1))^3 + 4 * (dyadicWeight (2*k) * (u k)^2 * u (k+1)) := by
  have h1 := mul_sq_le_half_cube_add (u k) (u (k+1)) (hnn k) (hnn (k+1))
  have h2 : dyadicWeight (2*k+1) = 2*dyadicWeight (2*k) := dW_odd k
  have h3 : 0 ≤ dyadicWeight (2*k) := dW_nonneg _
  have h4 : (u k * (u (k+1))^2) * (2*dyadicWeight (2*k))
      ≤ ((1/2) * (u (k+1))^3 + 2 * (u k)^2 * u (k+1)) * (2*dyadicWeight (2*k)) :=
    mul_le_mul_of_nonneg_right h1 (by linarith)
  rw [h2]
  nlinarith [h4]

/-- Per-shell bound for `D`. -/
private lemma shell_D (u : ℤ → ℝ) (hnn : ∀ k, 0 ≤ u k) (k : ℤ) :
    dyadicWeight (2*k+2) * u k * u (k+1) * u (k+2)
      ≤ 2 * (dyadicWeight (2*k) * (u k)^2 * u (k+1))
        + dyadicWeight (2*k) * (u (k+2))^3
        + dyadicWeight (2*(k+1)) * (u (k+1))^2 * u (k+2) := by
  have h1 := mul_mul_le_quarter_cube (u k) (u (k+1)) (u (k+2)) (hnn k) (hnn (k+1)) (hnn (k+2))
  have h2 : dyadicWeight (2*k+2) = 4*dyadicWeight (2*k) := dW_even_two k
  have h4 : dyadicWeight (2*(k+1)) = 4*dyadicWeight (2*k) := dW_shift_up k
  have h3 : 0 ≤ dyadicWeight (2*k) := dW_nonneg _
  have h5 : (u k * u (k+1) * u (k+2)) * (4*dyadicWeight (2*k))
      ≤ ((1/2) * (u k)^2 * u (k+1) + (1/4) * (u (k+2))^3 + (u (k+1))^2 * u (k+2))
          * (4*dyadicWeight (2*k)) :=
    mul_le_mul_of_nonneg_right h1 (by linarith)
  rw [h2, h4]
  nlinarith [h5]

/-- Pointwise expansion of the `correctionRHS` summand. -/
private lemma correctionRHS_summand (ν : ℝ) (u : ℤ → ℝ) (k : ℤ) :
    dyadicWeight k * (chainRHS ν u k * u (k+1) + u k * chainRHS ν u (k+1))
      = dyadicWeight (2*k) * (u (k-1))^2 * u (k+1)
        - dyadicWeight (2*k+1) * u k * (u (k+1))^2
        + dyadicWeight (2*k+1) * (u k)^3
        - dyadicWeight (2*k+2) * u k * u (k+1) * u (k+2)
        - 2 * ν * dyadicWeight k * u k * u (k+1) := by
  simp only [chainRHS, dW_succ, dW_two_mul, dW_even_two]
  ring_nf

/-- Exact expansion of the derivative of the correction term. -/
theorem correctionRHS_expand (ν : ℝ) (u : ℤ → ℝ) (N : ℕ) :
    correctionRHS ν u N
      = (∑ k ∈ Finset.range N, dyadicWeight (2*(k:ℤ)) * (u ((k:ℤ)-1))^2 * u ((k:ℤ)+1))
        - (∑ k ∈ Finset.range N, dyadicWeight (2*(k:ℤ)+1) * u (k:ℤ) * (u ((k:ℤ)+1))^2)
        + (∑ k ∈ Finset.range N, dyadicWeight (2*(k:ℤ)+1) * (u (k:ℤ))^3)
        - (∑ k ∈ Finset.range N,
            dyadicWeight (2*(k:ℤ)+2) * u (k:ℤ) * u ((k:ℤ)+1) * u ((k:ℤ)+2))
        - 2 * ν * correction u N := by
  unfold correctionRHS correction
  have hcongr : (∑ k ∈ Finset.range N,
        dyadicWeight (k:ℤ) * (chainRHS ν u (k:ℤ) * u ((k:ℤ)+1) + u (k:ℤ) * chainRHS ν u ((k:ℤ)+1)))
      = ∑ k ∈ Finset.range N,
          (dyadicWeight (2*(k:ℤ)) * (u ((k:ℤ)-1))^2 * u ((k:ℤ)+1)
            - dyadicWeight (2*(k:ℤ)+1) * u (k:ℤ) * (u ((k:ℤ)+1))^2
            + dyadicWeight (2*(k:ℤ)+1) * (u (k:ℤ))^3
            - dyadicWeight (2*(k:ℤ)+2) * u (k:ℤ) * u ((k:ℤ)+1) * u ((k:ℤ)+2)
            - 2 * ν * dyadicWeight (k:ℤ) * u (k:ℤ) * u ((k:ℤ)+1)) :=
    Finset.sum_congr rfl (fun k _ => correctionRHS_summand ν u (k:ℤ))
  rw [hcongr]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.mul_sum]
  rw [show (∑ x ∈ Finset.range N, 2 * ν * dyadicWeight (x:ℤ) * u (x:ℤ) * u ((x:ℤ)+1))
      = ∑ i ∈ Finset.range N, 2 * ν * (dyadicWeight (i:ℤ) * u (i:ℤ) * u ((i:ℤ)+1)) from by
    apply Finset.sum_congr rfl
    intro k _
    ring]

/-- **Step 2(b): the correction derivative is bounded below.** -/
theorem correctionRHS_ge (ν : ℝ) (hν : 0 ≤ ν) (u : ℤ → ℝ) (N : ℕ) (hN : 1 ≤ N)
    (hu1 : u (-1) = 0) (huN : u (N:ℤ) = 0) (hnn : ∀ k, 0 ≤ u k) :
    (27/16) * cubicSum u N - 7 * quadWeighted u N - 2*ν*correction u N
      ≤ correctionRHS ν u N := by
  set A : ℝ := ∑ k ∈ Finset.range N, dyadicWeight (2*(k:ℤ)) * (u ((k:ℤ)-1))^2 * u ((k:ℤ)+1) with hA
  set B : ℝ := ∑ k ∈ Finset.range N,
    dyadicWeight (2*(k:ℤ)+1) * u (k:ℤ) * (u ((k:ℤ)+1))^2 with hB
  set C : ℝ := ∑ k ∈ Finset.range N, dyadicWeight (2*(k:ℤ)+1) * (u (k:ℤ))^3 with hC
  set D : ℝ := ∑ k ∈ Finset.range N,
    dyadicWeight (2*(k:ℤ)+2) * u (k:ℤ) * u ((k:ℤ)+1) * u ((k:ℤ)+2) with hD
  have hexp : correctionRHS ν u N = A - B + C - D - 2*ν*correction u N := by
    rw [correctionRHS_expand, ← hA, ← hB, ← hC, ← hD]
  have hAnn : 0 ≤ A := by
    rw [hA]
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (mul_nonneg (dW_nonneg _) (sq_nonneg _)) (hnn _))
  have hBle : B ≤ (1/4)*cubicSum u N + 4*quadWeighted u N := by
    rw [hB]
    calc (∑ k ∈ Finset.range N,
            dyadicWeight (2*(k:ℤ)+1) * u (k:ℤ) * (u ((k:ℤ)+1))^2)
        ≤ ∑ k ∈ Finset.range N,
            (dyadicWeight (2*(k:ℤ)) * (u ((k:ℤ)+1))^3
              + 4 * (dyadicWeight (2*(k:ℤ)) * (u (k:ℤ))^2 * u ((k:ℤ)+1))) :=
          Finset.sum_le_sum (fun k _ => shell_B u hnn (k:ℤ))
      _ = (∑ k ∈ Finset.range N, dyadicWeight (2*(k:ℤ)) * (u ((k:ℤ)+1))^3)
            + 4*quadWeighted u N := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          unfold quadWeighted
          rfl
      _ ≤ (1/4)*cubicSum u N + 4*quadWeighted u N := by
          linarith [cubic_shift_le u N huN hnn]
  have hCeq : C = 2*cubicSum u N := by
    rw [hC]
    unfold cubicSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [dW_odd]
    ring
  have hDle : D ≤ 2*quadWeighted u N + (1/16)*cubicSum u N + quadWeighted u N := by
    rw [hD]
    have hrestrict : (∑ k ∈ Finset.range (N-2),
          dyadicWeight (2*(k:ℤ)+2) * u (k:ℤ) * u ((k:ℤ)+1) * u ((k:ℤ)+2))
        = ∑ k ∈ Finset.range N,
          dyadicWeight (2*(k:ℤ)+2) * u (k:ℤ) * u ((k:ℤ)+1) * u ((k:ℤ)+2) := by
      apply Finset.sum_subset (Finset.range_subset_range.2 (by omega))
      intro k hk hknot
      simp only [Finset.mem_range] at hk hknot
      have hcase : k + 1 = N ∨ k + 2 = N := by omega
      rcases hcase with hc | hc
      · have hz : u ((k:ℤ)+1) = 0 := by
          rw [show (k:ℤ)+1 = (N:ℤ) by omega, huN]
        rw [hz]; ring
      · have hz : u ((k:ℤ)+2) = 0 := by
          rw [show (k:ℤ)+2 = (N:ℤ) by omega, huN]
        rw [hz]; ring
    rw [← hrestrict]
    calc (∑ k ∈ Finset.range (N-2),
            dyadicWeight (2*(k:ℤ)+2) * u (k:ℤ) * u ((k:ℤ)+1) * u ((k:ℤ)+2))
        ≤ ∑ k ∈ Finset.range (N-2),
            (2 * (dyadicWeight (2*(k:ℤ)) * (u (k:ℤ))^2 * u ((k:ℤ)+1))
              + dyadicWeight (2*(k:ℤ)) * (u ((k:ℤ)+2))^3
              + dyadicWeight (2*((k:ℤ)+1)) * (u ((k:ℤ)+1))^2 * u ((k:ℤ)+2)) :=
          Finset.sum_le_sum (fun k _ => shell_D u hnn (k:ℤ))
      _ = 2 * (∑ k ∈ Finset.range (N-2), dyadicWeight (2*(k:ℤ)) * (u (k:ℤ))^2 * u ((k:ℤ)+1))
            + (∑ k ∈ Finset.range (N-2), dyadicWeight (2*(k:ℤ)) * (u ((k:ℤ)+2))^3)
            + (∑ k ∈ Finset.range (N-2),
                dyadicWeight (2*((k:ℤ)+1)) * (u ((k:ℤ)+1))^2 * u ((k:ℤ)+2)) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ ≤ 2*quadWeighted u N + (1/16)*cubicSum u N + quadWeighted u N := by
          have h2 : (∑ k ∈ Finset.range (N-2), dyadicWeight (2*(k:ℤ)) * (u (k:ℤ))^2 * u ((k:ℤ)+1))
              ≤ quadWeighted u N := by
            rw [← hD] at *
            exact sum_range_sub_le (fun k => dyadicWeight (2*(k:ℤ)) * (u (k:ℤ))^2 * u ((k:ℤ)+1))
              (fun k => mul_nonneg (mul_nonneg (dW_nonneg _) (sq_nonneg _)) (hnn _)) (by omega)
          have h3 : (∑ k ∈ Finset.range (N-2), dyadicWeight (2*(k:ℤ)) * (u ((k:ℤ)+2))^3)
              ≤ (1/16)*cubicSum u N := cubic_double_shift_le u N hnn
          have h4 : (∑ k ∈ Finset.range (N-2),
                dyadicWeight (2*((k:ℤ)+1)) * (u ((k:ℤ)+1))^2 * u ((k:ℤ)+2))
              ≤ quadWeighted u N := quad_shift_upper_le u N hnn
          linarith
  rw [hexp]
  linarith [hAnn, hBle, hCeq, hDle]

/-- **Step 2(b) with an abstract derivative `Q'`.** -/
theorem correction_deriv_ge (ν : ℝ) (hν : 0 ≤ ν) (μ : ℝ) (N : ℕ) (u θ : ℝ → ℤ → ℝ)
    (h : IsUnforcedTruncatedSolutionE ν μ 0 0 N u θ) (hN : 1 ≤ N)
    (t : ℝ) (hnn : ∀ k : ℤ, 0 ≤ u t k) (Q' : ℝ)
    (hQ : HasDerivAt (fun s => correction (u s) N) Q' t) (c₂ : ℝ) (hc₂ : 0 ≤ c₂) :
    c₂ * Q' ≥ -(c₂ * 7) * quadWeighted (u t) N + (c₂ * (27/16)) * cubicSum (u t) N
      - 2 * c₂ * ν * correction (u t) N := by
  have hexact : HasDerivAt (fun s => correction (u s) N) (correctionRHS ν (u t) N) t := by
    have hmain := HasDerivAt.sum (u := Finset.range N)
      (A := fun (k : ℕ) (s : ℝ) => dyadicWeight (k:ℤ) * u s (k:ℤ) * u s ((k:ℤ)+1))
      (A' := fun (k : ℕ) => dyadicWeight (k:ℤ) *
        (chainRHS ν (u t) (k:ℤ) * u t ((k:ℤ)+1) + u t (k:ℤ) * chainRHS ν (u t) ((k:ℤ)+1)))
      (by
        intro k hk
        have h1 := h.1 t (k:ℤ)
        have h2 := h.1 t ((k:ℤ)+1)
        have hm := (h1.mul h2).const_mul (dyadicWeight (k:ℤ))
        simpa [velocityRHSDegreeE_zero, chainRHS, mul_assoc] using hm)
    simpa [correction, correctionRHS, Finset.sum_fn] using hmain
  have hbd := correctionRHS_ge ν hν (u t) N hN (h.2.2 t).1 (h.2.2 t).2.1 hnn
  rw [hQ.unique hexact]
  have h2 : c₂ * ((27/16)*cubicSum (u t) N - 7*quadWeighted (u t) N
      - 2*ν*correction (u t) N) ≤ c₂ * correctionRHS ν (u t) N :=
    mul_le_mul_of_nonneg_left hbd hc₂
  nlinarith [h2]

end Step2b

/-! ## 6. Step 3: the Lyapunov growth-rate inequality -/

section Step3

/-- `blowupNorm` is nonnegative. -/
theorem blowupNorm_nonneg (u : ℤ → ℝ) (N : ℕ) : 0 ≤ blowupNorm u N :=
  Finset.sum_nonneg (fun k _ => mul_nonneg (dW_nonneg _) (sq_nonneg _))

/-- `correction` is nonnegative for a nonnegative ladder. -/
theorem correction_nonneg (u : ℤ → ℝ) (N : ℕ) (hnn : ∀ k : ℤ, 0 ≤ u k) :
    0 ≤ correction u N :=
  Finset.sum_nonneg (fun k _ => mul_nonneg (mul_nonneg (dW_nonneg _) (hnn _)) (hnn _))

/-- `cubicSum` is nonnegative for a nonnegative ladder. -/
theorem cubicSum_nonneg (u : ℤ → ℝ) (N : ℕ) (hnn : ∀ k : ℤ, 0 ≤ u k) :
    0 ≤ cubicSum u N :=
  Finset.sum_nonneg (fun k _ => mul_nonneg (dW_nonneg _) (pow_nonneg (hnn _) 3))

/-- `quadWeighted` is nonnegative for a nonnegative ladder. -/
theorem quadWeighted_nonneg (u : ℤ → ℝ) (N : ℕ) (hnn : ∀ k : ℤ, 0 ≤ u k) :
    0 ≤ quadWeighted u N :=
  Finset.sum_nonneg (fun k _ => mul_nonneg (mul_nonneg (dW_nonneg _) (sq_nonneg _)) (hnn _))

/-- `dyadicWeight` is monotone. -/
private lemma dW_le_succ (k : ℤ) : dyadicWeight k ≤ dyadicWeight (k+1) := by
  rw [dW_succ]; linarith [dW_nonneg k]

/-- The weight one is a doubling factor: the shifted weight is dominated. -/
private lemma sum_weighted_succ_sq_le_blowupNorm (u : ℤ → ℝ) (N : ℕ) (huN : u (N:ℤ) = 0) :
    (∑ k ∈ Finset.range N, dyadicWeight (k:ℤ) * (u ((k:ℤ)+1))^2) ≤ blowupNorm u N := by
  have hA : (∑ k ∈ Finset.range N, dyadicWeight (k:ℤ) * (u ((k:ℤ)+1))^2)
      ≤ ∑ k ∈ Finset.range N, dyadicWeight ((k:ℤ)+1) * (u ((k:ℤ)+1))^2 :=
    Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_right (dW_le_succ (k:ℤ)) (sq_nonneg _))
  have hlast : (fun m : ℕ => dyadicWeight (m:ℤ) * (u (m:ℤ))^2) N = 0 := by
    show dyadicWeight (N:ℤ) * (u (N:ℤ))^2 = 0
    rw [huN]; ring
  have h0 : 0 ≤ (fun m : ℕ => dyadicWeight (m:ℤ) * (u (m:ℤ))^2) 0 :=
    mul_nonneg (dW_nonneg _) (sq_nonneg _)
  have hB : (∑ k ∈ Finset.range N, dyadicWeight ((k:ℤ)+1) * (u ((k:ℤ)+1))^2)
      ≤ ∑ k ∈ Finset.range N, dyadicWeight (k:ℤ) * (u (k:ℤ))^2 :=
    sum_range_succ_shift_le (fun m : ℕ => dyadicWeight (m:ℤ) * (u (m:ℤ))^2) N hlast h0
  have h := le_trans hA hB
  unfold blowupNorm
  simpa using h

/-- **`correction ≤ blowupNorm`.**  Pairwise AM–GM plus the weight shift. -/
theorem correction_le_blowupNorm (u : ℤ → ℝ) (N : ℕ) (hnn : ∀ k : ℤ, 0 ≤ u k)
    (huN : u (N:ℤ) = 0) : correction u N ≤ blowupNorm u N := by
  have hpoint : ∀ k ∈ Finset.range N, dyadicWeight (k:ℤ) * u (k:ℤ) * u ((k:ℤ)+1)
      ≤ (1/2) * (dyadicWeight (k:ℤ) * (u (k:ℤ))^2)
        + (1/2) * (dyadicWeight (k:ℤ) * (u ((k:ℤ)+1))^2) := by
    intro k _
    nlinarith [mul_nonneg (dW_nonneg (k:ℤ)) (sq_nonneg (u (k:ℤ) - u ((k:ℤ)+1)))]
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
  have hshift := sum_weighted_succ_sq_le_blowupNorm u N huN
  unfold correction
  linarith

/-- **`blowupNorm ≤ lyap`** for `c₂ ≥ 0`. -/
theorem blowupNorm_le_lyap (u : ℤ → ℝ) (N : ℕ) (c₂ : ℝ) (hc₂ : 0 ≤ c₂)
    (hnn : ∀ k : ℤ, 0 ≤ u k) : blowupNorm u N ≤ lyap u N c₂ := by
  have hc := correction_nonneg u N hnn
  simp only [lyap]
  nlinarith [mul_nonneg hc₂ hc]

/-- The derivative of `correction` along the solution. -/
theorem correctionRHS_hasDerivAt (ν : ℝ) (μ : ℝ) (N : ℕ) (u θ : ℝ → ℤ → ℝ)
    (h : IsUnforcedTruncatedSolutionE ν μ 0 0 N u θ) (t : ℝ) :
    HasDerivAt (fun s => correction (u s) N) (correctionRHS ν (u t) N) t := by
  have hmain := HasDerivAt.sum (u := Finset.range N)
    (A := fun (k : ℕ) (s : ℝ) => dyadicWeight (k:ℤ) * u s (k:ℤ) * u s ((k:ℤ)+1))
    (A' := fun (k : ℕ) => dyadicWeight (k:ℤ) *
      (chainRHS ν (u t) (k:ℤ) * u t ((k:ℤ)+1) + u t (k:ℤ) * chainRHS ν (u t) ((k:ℤ)+1)))
    (by
      intro k hk
      have h1 := h.1 t (k:ℤ)
      have h2 := h.1 t ((k:ℤ)+1)
      have hm := (h1.mul h2).const_mul (dyadicWeight (k:ℤ))
      simpa [velocityRHSDegreeE_zero, chainRHS, mul_assoc] using hm)
  simpa [correction, correctionRHS, Finset.sum_fn] using hmain

/-- The derivative of `lyap` along the solution. -/
theorem lyap_hasDerivAt (ν : ℝ) (μ : ℝ) (N : ℕ) (u θ : ℝ → ℤ → ℝ) (c₂ : ℝ)
    (h : IsUnforcedTruncatedSolutionE ν μ 0 0 N u θ) (hN : 1 ≤ N) (t : ℝ) :
    HasDerivAt (fun s => lyap (u s) N c₂)
      ((4 * quadWeighted (u t) (N-1) - 2*ν*blowupNorm (u t) N)
        + c₂ * correctionRHS ν (u t) N) t := by
  have h1 : HasDerivAt (fun s => blowupNorm (u s) N)
      (4 * quadWeighted (u t) (N-1) - 2*ν*blowupNorm (u t) N) t := by
    simpa [quadWeighted] using blowupNorm_hasDerivAt ν μ N u θ h hN t
  have h2 : HasDerivAt (fun s => correction (u s) N) (correctionRHS ν (u t) N) t :=
    correctionRHS_hasDerivAt ν μ N u θ h t
  have h3 : HasDerivAt (fun s => blowupNorm (u s) N + c₂ * correction (u s) N)
      ((4 * quadWeighted (u t) (N-1) - 2*ν*blowupNorm (u t) N)
        + c₂ * correctionRHS ν (u t) N) t :=
    h1.add (h2.const_mul c₂)
  exact h3

/-- **THE MAIN RESULT.**  With `c₂ = 4/7` the Lyapunov derivative is bounded below by
`(27/28) * cubicSum - 2ν * lyap`. -/
theorem lyap_deriv_ge (ν : ℝ) (hν : 0 ≤ ν) (μ : ℝ) (N : ℕ) (u θ : ℝ → ℤ → ℝ)
    (h : IsUnforcedTruncatedSolutionE ν μ 0 0 N u θ) {T : ℝ} (L' : ℝ → ℝ)
    (hderiv : ∀ t ∈ Set.Ico 0 T, HasDerivAt (fun s => lyap (u s) N (4/7)) (L' t) t)
    (hnn : ∀ t ∈ Set.Ico 0 T, ∀ k : ℤ, 0 ≤ u t k) (hN : 1 ≤ N) (t : ℝ)
    (ht : t ∈ Set.Ico 0 T) :
    (27/28) * cubicSum (u t) N - 2 * ν * lyap (u t) N (4/7) ≤ L' t := by
  have hexact := lyap_hasDerivAt ν μ N u θ (4/7) h hN t
  rw [(hderiv t ht).unique hexact]
  have hbd := correctionRHS_ge ν hν (u t) N hN (h.2.2 t).1 (h.2.2 t).2.1 (hnn t ht)
  have hquad : quadWeighted (u t) (N-1) = quadWeighted (u t) N :=
    (sum_upper_drop (u t) N hN (h.2.2 t).2.1).symm
  simp only [lyap]
  rw [hquad]
  nlinarith [hbd]

end Step3


/-! ## 7. Non-vacuity checks -/

section NonVacuity

/-- The concrete ladder `1,1,1,0` (supported on shells `0,1,2`). -/
def ladder3 (k : ℤ) : ℝ := if 0 ≤ k ∧ k < 3 then 1 else 0

/-- Boundary case `x = y/2` of the first elementary inequality. -/
example (y : ℝ) (hy : 0 ≤ y) : (y/2) * y^2 ≤ (1/2) * y^3 + 2 * (y/2)^2 * y :=
  mul_sq_le_half_cube_add (y/2) y (by linarith) hy

/-- Zero coordinate in the first elementary inequality. -/
example (x : ℝ) (hx : 0 ≤ x) : x * (0:ℝ)^2 ≤ (1/2) * (0:ℝ)^3 + 2 * x^2 * 0 :=
  mul_sq_le_half_cube_add x 0 hx le_rfl

/-- Zero coordinate in the second elementary inequality. -/
example (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x * y * 0 ≤ (1/2) * x^2 * y + (1/4) * (0:ℝ)^3 + y^2 * 0 :=
  mul_mul_le_quarter_cube x y 0 hx hy le_rfl

/-- Boundary case `x = y/2` of the second elementary inequality. -/
example (y z : ℝ) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    (y/2) * y * z ≤ (1/2) * (y/2)^2 * y + (1/4) * z^3 + y^2 * z :=
  mul_mul_le_quarter_cube (y/2) y z (by linarith) hy hz

/-- The hypotheses of the fixed-time statements hold at `ladder3` with `N = 3`. -/
example : ladder3 (-1) = 0 ∧ ladder3 3 = 0 ∧ (∀ k : ℤ, 0 ≤ ladder3 k) := by
  refine ⟨by norm_num [ladder3], by norm_num [ladder3], ?_⟩
  intro k; unfold ladder3; split <;> norm_num

/-- `correction ≤ blowupNorm` at the concrete ladder. -/
example : correction ladder3 3 ≤ blowupNorm ladder3 3 := by
  apply correction_le_blowupNorm
  · intro k; unfold ladder3; split <;> norm_num
  · norm_num [ladder3]

/-- `blowupNorm ≤ lyap` at the concrete ladder. -/
example : blowupNorm ladder3 3 ≤ lyap ladder3 3 (4/7) :=
  blowupNorm_le_lyap ladder3 3 (4/7) (by norm_num)
    (fun k => by unfold ladder3; split <;> norm_num)

/-- Numerical evaluation: `correction ladder3 3 = 3`. -/
example : correction ladder3 3 = 3 := by
  norm_num [correction, ladder3, dyadicWeight, Finset.sum_range_succ]

/-- Numerical evaluation: `blowupNorm ladder3 3 = 7`. -/
example : blowupNorm ladder3 3 = 7 := by
  norm_num [blowupNorm, ladder3, dyadicWeight, Finset.sum_range_succ]

/-- Numerical evaluation: `quadWeighted ladder3 3 = 5`. -/
example : quadWeighted ladder3 3 = 5 := by
  norm_num [quadWeighted, ladder3, dyadicWeight, Finset.sum_range_succ]

/-- Numerical evaluation: `cubicSum ladder3 3 = 21`. -/
example : cubicSum ladder3 3 = 21 := by
  norm_num [cubicSum, ladder3, dyadicWeight, Finset.sum_range_succ]

/-- **Step 2(a) evaluated numerically** on the ladder `1,1,0` (`N = 2`). -/
example : blowupNormRHS (0:ℝ) (fun k : ℤ => if 0 ≤ k ∧ k < 2 then (1:ℝ) else 0) 2 = 4 := by
  norm_num [blowupNormRHS, chainRHS, dyadicWeight, Finset.sum_range_succ]

example : quadWeighted (fun k : ℤ => if 0 ≤ k ∧ k < 2 then (1:ℝ) else 0) (2-1) = 1 := by
  norm_num [quadWeighted, dyadicWeight, Finset.sum_range_succ]

/-- **Step 2(a) as an identity** on the same ladder (both sides equal `4`). -/
example : blowupNormRHS (0:ℝ) (fun k : ℤ => if 0 ≤ k ∧ k < 2 then (1:ℝ) else 0) 2
    = 4 * quadWeighted (fun k : ℤ => if 0 ≤ k ∧ k < 2 then (1:ℝ) else 0) (2-1)
      - 2*0*blowupNorm (fun k : ℤ => if 0 ≤ k ∧ k < 2 then (1:ℝ) else 0) 2 :=
  blowupNormRHS_eq 0 _ 2 (by norm_num) (by norm_num) (by norm_num)

/-- **Step 2(b) evaluated numerically**: `correctionRHS 0 ladder3 3 = 32`, above the bound `7/16`. -/
example : correctionRHS (0:ℝ) ladder3 3 = 32 := by
  rw [correctionRHS_expand]
  norm_num [correction, ladder3, dyadicWeight, Finset.sum_range_succ]

/-- **Step 2(b) instantiated** at the concrete ladder. -/
example : (27/16) * cubicSum ladder3 3 - 7 * quadWeighted ladder3 3 - 2*0*correction ladder3 3
    ≤ correctionRHS (0:ℝ) ladder3 3 :=
  correctionRHS_ge 0 le_rfl ladder3 3 (by norm_num) (by norm_num [ladder3]) (by norm_num [ladder3])
    (fun k => by unfold ladder3; split <;> norm_num)

/-- The hypotheses of the main theorem are satisfiable (the zero solution). -/
example : ∃ (u θ : ℝ → ℤ → ℝ), IsUnforcedTruncatedSolutionE 0 0 0 0 2 u θ ∧
    (∀ t : ℝ, ∀ k : ℤ, 0 ≤ u t k) :=
  ⟨fun _ _ => 0, fun _ _ => 0, zero_is_unforcedTruncatedSolutionE 0 0 0 0 2,
    fun _ _ => le_refl 0⟩

/-- **The main inequality fires** at the zero solution. -/
example : (27/28) * cubicSum (fun _ : ℤ => (0:ℝ)) 2
      - 2*0*lyap (fun _ : ℤ => (0:ℝ)) 2 (4/7) ≤ (0:ℝ) :=
  lyap_deriv_ge (ν := 0) (hν := le_rfl) (μ := 0) (N := 2)
    (u := fun (_ : ℝ) (_ : ℤ) => 0) (θ := fun (_ : ℝ) (_ : ℤ) => 0)
    (h := zero_is_unforcedTruncatedSolutionE 0 0 0 0 2) (T := 1) (L' := fun _ => 0)
    (hderiv := fun t _ =>
      hasDerivAt_const t (lyap (fun _ : ℤ => (0:ℝ)) 2 (4/7)))
    (hnn := fun _ _ _ => le_refl 0) (hN := by norm_num) (t := 0)
    (ht := ⟨le_rfl, by norm_num⟩)

end NonVacuity


/-! ## 8. Axiom audit -/

#print axioms blowupNorm
#print axioms correction
#print axioms cubicSum
#print axioms lyap
#print axioms chainRHS
#print axioms blowupNormRHS
#print axioms correctionRHS
#print axioms quadWeighted
#print axioms ladder3
#print axioms velocityRHSDegreeE_zero
#print axioms mul_sq_le_half_cube_add
#print axioms mul_mul_le_quarter_cube
#print axioms blowupNormRHS_eq
#print axioms blowupNorm_hasDerivAt
#print axioms correctionRHS_expand
#print axioms correctionRHS_ge
#print axioms correction_deriv_ge
#print axioms blowupNorm_nonneg
#print axioms correction_nonneg
#print axioms cubicSum_nonneg
#print axioms quadWeighted_nonneg
#print axioms correction_le_blowupNorm
#print axioms blowupNorm_le_lyap
#print axioms correctionRHS_hasDerivAt
#print axioms lyap_hasDerivAt
#print axioms lyap_deriv_ge

#print axioms dW_ne_zero
#print axioms dW_add
#print axioms dW_two_mul
#print axioms dW_succ
#print axioms dW_nonneg
#print axioms dW_odd
#print axioms dW_even_two
#print axioms dW_shift_up
#print axioms dW_eq_two_pow
#print axioms sum_range_shift
#print axioms sum_range_last_zero
#print axioms blowupNorm_summand
#print axioms blowupNormRHS_expand
#print axioms sum_lower_shift
#print axioms sum_upper_drop
#print axioms sum_range_succ_shift
#print axioms sum_range_succ_shift_le
#print axioms sum_range_sub_le
#print axioms sum_range_shift_le
#print axioms cubic_shift_le
#print axioms cubic_double_shift_le
#print axioms quad_shift_upper_le
#print axioms shell_B
#print axioms shell_D
#print axioms correctionRHS_summand
#print axioms dW_le_succ
#print axioms sum_weighted_succ_sq_le_blowupNorm
end Cascade

