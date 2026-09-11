import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring

/-!
# Pillar B1 — the dyadic (Littlewood–Paley) decomposition

The "multiplicative grouping" side of the additive/multiplicative tension: frequencies
are grouped *multiplicatively* into dyadic octaves `[2ᵏ, 2ᵏ⁺¹)`, even though the
nonlinearity couples them *additively* (Pillar B2: the frequency `ω` of `(u·∇)u` is fed
by every pair `ξ + η = ω`).

This file formalizes the grouping itself:

* the dyadic octaves are **pairwise disjoint** (a partition of `(0, ∞)`), and
* multiplication by `2` **moves a frequency to the next octave** — the multiplicative
  character of the grouping.

The full *Littlewood–Paley* decomposition `f = Σₖ 𝓕⁻(φₖ · 𝓕 f)` (smooth cutoffs `φₖ`
adapted to the octaves) additionally needs a smooth partition of unity; that is a
larger construction and is documented below as remaining work. The disjointness/grouping
facts here are the structural core that the decomposition rests on.
-/

noncomputable section

namespace Criticality

/-- The `k`-th dyadic frequency octave `[2ᵏ, 2ᵏ⁺¹)` (on the positive reals; in a real
inner product space `V` the octave would be `{ξ | 2ᵏ ≤ ‖ξ‖ < 2ᵏ⁺¹}`). -/
def dyadicOctave (k : ℕ) : Set ℝ := {ξ | (2 : ℝ) ^ k ≤ ξ ∧ ξ < (2 : ℝ) ^ (k + 1)}

/-- **The octaves are pairwise disjoint** — the multiplicative grouping is a partition.
Two different dyadic octaves share no frequency. -/
theorem dyadicOctave_disjoint {k l : ℕ} (hkl : k ≠ l) :
    Disjoint (dyadicOctave k) (dyadicOctave l) := by
  rw [Set.disjoint_left]
  intro ξ hk hl
  rcases lt_or_gt_of_ne hkl with hlt | hgt
  · have hpow : (2 : ℝ) ^ (k + 1) ≤ (2 : ℝ) ^ l := by
      exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : k + 1 ≤ l)
    nlinarith [hk.2, hl.1, hpow]
  · have hpow : (2 : ℝ) ^ (l + 1) ≤ (2 : ℝ) ^ k := by
      exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : l + 1 ≤ k)
    nlinarith [hl.2, hk.1, hpow]

/-- **Multiplication by `2` moves a frequency to the next octave.** This is the
multiplicative character of the grouping: the *additive* interaction of Pillar B2 has no
counterpart here — scaling `ξ` to `2ξ` is a *multiplicative* operation that simply walks
the octaves, which is exactly the source of the additive/multiplicative tension. -/
theorem dyadicOctave_shift (ξ : ℝ) (k : ℕ) :
    ξ ∈ dyadicOctave k ↔ (2 : ℝ) * ξ ∈ dyadicOctave (k + 1) := by
  constructor
  · intro h
    rcases h with ⟨hle, hlt⟩
    constructor
    · rw [show (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k by rw [pow_succ]; ring]
      nlinarith [mul_le_mul_of_nonneg_left hle (by norm_num : (0 : ℝ) ≤ 2)]
    · rw [show (2 : ℝ) ^ (k + 2) = 2 * (2 : ℝ) ^ (k + 1) by rw [pow_succ]; ring]
      nlinarith [mul_lt_mul_of_pos_left hlt (by norm_num : (0 : ℝ) < 2)]
  · intro h
    rcases h with ⟨hle, hlt⟩
    constructor
    · rw [show (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k by rw [pow_succ]; ring] at hle
      nlinarith [hle]
    · rw [show (2 : ℝ) ^ (k + 2) = 2 * (2 : ℝ) ^ (k + 1) by rw [pow_succ]; ring] at hlt
      nlinarith [hlt]

/-!
The remaining Littlewood–Paley step (not yet formalized): a smooth partition of unity
`φₖ : V → ℝ` with `supp φₖ ⊆ {ξ | 2ᵏ⁻¹ ≤ ‖ξ‖ ≤ 2ᵏ⁺¹}` and `Σₖ φₖ(ξ) = 1` for `ξ ≠ 0`,
giving `f = Σₖ 𝓕⁻(φₖ · 𝓕 f)` for `f ∈ 𝓢(V, F)`. This is the full decomposition; the
disjointness/grouping facts above are its structural backbone. (Construction via
mathlib's `exists_smoothPartition`/bump-function machinery.)
-/

end Criticality

#print axioms Criticality.dyadicOctave_disjoint
#print axioms Criticality.dyadicOctave_shift
