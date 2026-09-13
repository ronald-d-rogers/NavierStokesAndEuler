# Progress: Criticality Skeleton

Where we are now. This file changes as we work. The *target* is `PLAN.md`; the
*why* is `VISION.md`.

> **Snapshot:** branch `skeleton-criticality`, HEAD `6b8841f`. Build is green:
> `lake build Criticality` succeeds. **Pillar A is complete** — core `bernstein`
> (h3 closed), A1 (Heisenberg commutator form), A2 (`L² → L∞`), A3 (gradient).
> **All five pillars are landed.** Pillar A (core + A1 commutator + A2 + A3), B1
> (dyadic grouping), B2 (convolution coupling), C (scaling criticality), D (shell
> model), E (Euler product). All theorems are machine-checked with
> `#print axioms` = `[propext, Classical.choice, Quot.sound]`. See the "stretch forms"
> note below for the documented-but-not-yet-proved pieces (A1 variance form, B1 smooth
> partition of unity, C1 full PDE invariance, D3 forced blowup).

---

## Proved (standard axioms only)

> **Relocation note (Pillar A).** `ConcentrationBarrier`, `Bernstein`, and
> `BernsteinGrowth` have been **relocated to the `Cascade/` library** (namespace
> `Cascade`). The `Criticality` library re-exports them via
> `Criticality/BernsteinExport.lean`, so the `Criticality.*` names below remain
> available with the same bodies; the implementations now live in `Cascade/`.

`Criticality/ConcentrationBarrier.lean`:

```lean
theorem fourierInv_apply_le_toLp_one (f : 𝓢(V, F)) (x : V) :
    ‖𝓕⁻ f x‖ ≤ ‖f.toLp 1‖
-- the inverse Fourier transform maps L¹ → L∞

theorem pointwise_le_L1_fourier [CompleteSpace F] (f : 𝓢(V, F)) (x : V) :
    ‖f x‖ ≤ ‖(𝓕 f).toLp 1‖
-- THE core concentration barrier: spread in frequency ⇒ bounded in space
```

`Criticality/Bernstein.lean`:

```lean
theorem norm_toLp_one_le_sqrt_measure_mul_norm_toLp_two
    (g : 𝓢(V, F)) {s : Set V} (hs : MeasurableSet s) (hs_finite : volume s < ⊤)
    (hsupp : ∀ x, g x ≠ 0 → x ∈ s) :
    ‖g.toLp 1‖ ≤ Real.sqrt (volume s).toReal * ‖g.toLp 2‖
-- Cauchy–Schwarz with support

theorem bernstein [CompleteSpace F] (f : 𝓢(V, F)) (N : ℝ)
    (hband : ∀ x, 𝓕 f x ≠ 0 → ‖x‖ < N)
    (hs_finite : volume (Metric.ball (0 : V) N) < ⊤) :
    ‖f.toBoundedContinuousFunction‖ ≤
      Real.sqrt (volume (Metric.ball (0 : V) N)).toReal * ‖f.toLp 2 volume‖
-- Bernstein: band-limiting ⇒ ‖f‖∞ ≤ √(vol ball) · ‖f‖₂  (DONE)
```

This Cauchy–Schwarz lemma was the substantive result of the session. Its proof
chain (all machine-checked):

1. `‖g‖₁ = ∫‖g‖` (`SchwartzMap.norm_toLp_one`), `= ∫_s ‖g‖`
   (`setIntegral_eq_integral_of_forall_compl_eq_zero`).
2. **ENNReal Hölder** `∫⁻_s ‖g‖ ≤ (∫⁻_s ‖g‖²)^{1/2}·(∫⁻_s 1)^{1/2}` via
   `ENNReal.lintegral_mul_le_Lp_mul_Lq` with `p = q = 2` (the hard step — the
   real-valued `integral_mul_norm_le_Lp_mul_Lq` caused a `whnf` timeout).
3. Full `ℝ ↔ ℝ≥0∞` conversion: `ENNReal.toReal_le_toReal`, `toReal_mul`,
   `lintegral_one`, `Measure.restrict_apply_univ`, `ENNReal.toReal_rpow`,
   `Real.sqrt_eq_rpow`, `ofReal_integral_eq_lintegral_ofReal`, `ENNReal.toReal_ofReal`,
   `norm_toLp'` (p=2).
4. Finiteness: `Integrable (fun x => ‖g x‖ ^ 2)` via `MemLp.integrable_norm_rpow`
   on `g.memLp 2 volume`, then `.mono_measure`.

---

## Pillar E — Euler product (done)

`Criticality/EulerProduct.lean` re-exposes mathlib's Euler product for the Riemann
ζ function in the `Criticality` namespace (Pillar E1, pure re-exposure):

```lean
theorem eulerProduct_hasProd (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes ↦ (1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹) (riemannZeta s)
theorem eulerProduct_tprod (s : ℂ) (hs : 1 < s.re) :
    (∏' p : Nat.Primes, (1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹) = riemannZeta s
theorem eulerProduct (s : ℂ) (hs : 1 < s.re) :
    Tendsto (fun n : ℕ ↦ ∏ p ∈ primesBelow n, (1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹) atTop (𝓝 (riemannZeta s))
```

All three wrap mathlib's `riemannZeta_eulerProduct(_hasProd/_tprod)` with
`#print axioms` = `[propext, Classical.choice, Quot.sound]`.

---

## Pillar A — `bernstein` done (`h3` closed)

`bernstein` is now a complete `calc`:

```lean
have h1 : ‖f.toBoundedContinuousFunction‖ ≤ ‖(𝓕 f).toLp 1 volume‖   -- sup form of the core lemma
have h2 : ‖(𝓕 f).toLp 1 volume‖ ≤ √(vol ball)·‖(𝓕 f).toLp 2 volume‖ -- Cauchy–Schwarz on 𝓕 f
have h3 : ‖(𝓕 f).toLp 2 volume‖ = ‖f.toLp 2 volume‖                 -- Plancherel (DONE)
```

**What closed `h3` (three things, all required):**

1. **Statement change — `F` must be an inner-product space.** The Plancherel
   lemmas (`SchwartzMap.norm_fourier_toL2_eq`, `MeasureTheory.Lp.norm_fourier_eq`,
   and the `L²` Fourier isometry `fourierTransformₗᵢ` itself) all require
   `[InnerProductSpace ℂ F]`, not just `[NormedSpace ℂ F]`. There is **no**
   Plancherel for a general complex normed space in mathlib v4.34.0-rc2, so
   `bernstein` cannot be proved from the original variable block. The file now
   declares `variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]`
   (replacing `[NormedSpace ℂ F]`; the Cauchy–Schwarz lemma is unaffected).
2. **`h3` is literally `SchwartzMap.norm_fourier_toL2_eq f`** — already in mathlib
   (`Mathlib/Analysis/Distribution/SchwartzSpace/Fourier.lean`), `@[simp]`, exactly
   `‖(𝓕 f).toLp 2‖ = ‖f.toLp 2‖`. No need to compose `toLp_fourier_eq` +
   `norm_fourier_eq` (the L² `𝓕` never has to be elaborated).
3. **Elaboration hygiene (all `[local irreducible]`, in `Bernstein.lean`):**
   `Real.rpow`, `MeasureTheory.Lp.fourierTransformₗᵢ`, **and
   `SchwartzMap.fourierTransformCLM`**. The last was missing — it is marked
   irreducible only in `ConcentrationBarrier.lean`, and `[local]` attributes do
   **not** propagate across imports. With it missing, `𝓕 f` unfolded the huge
   `mkCLM` term and hit the `whnf` timeout.
4. **Explicit measure `volume`** in the `toLp` arguments (`‖f.toLp 2 volume‖`, …).
   The default `volume_tac` (= `exact MeasureSpace.volume`) triggered the
   *"could not synthesize default value for parameter 'μ'"* / `whnf` residue when
   `𝓕` met `toLp`. Writing `volume` explicitly makes the elaboration trivial and
   is what the lemmas state anyway.

So the winning fix was **fix #2 (explicit measure) + fix #3 (irreducible attrs,
extended to `fourierTransformCLM`) + a statement strengthening to
`[InnerProductSpace ℂ F]`**. `#print axioms bernstein` =
`[propext, Classical.choice, Quot.sound]`.

**Note on `hs_finite`:** it is an explicit hypothesis because
`[IsFiniteMeasureOnCompacts volume]` is not an instance for a general
finite-dimensional inner-product space `V` (only `IsLocallyFiniteMeasure` for
`ℝ`). For `V = EuclideanSpace ℝ (Fin d)` it follows from `measure_ball_lt_top`
(needs `[ProperSpace V]` via `FiniteDimensional.proper ℝ V`). Decide later whether
to keep `hs_finite` explicit or specialize `bernstein` to `EuclideanSpace ℝ (Fin d)`.

---

## Pillar A2 — Bernstein `L² → L∞` (done)

`Criticality/BernsteinGrowth.lean`:

```lean
lemma sqrt_volume_ball_eq_sqrt_volume_unitBall_mul (N : ℝ) (hN : 0 ≤ N) :
    Real.sqrt (volume (Metric.ball (0 : V) N)).toReal =
      Real.sqrt (volume (Metric.ball (0 : V) 1)).toReal * N ^ ((Module.finrank ℝ V : ℝ) / 2)

theorem bernstein_L2_to_Linf [CompleteSpace F] (f : 𝓢(V, F)) (N : ℝ) (hN : 0 ≤ N)
    (hband : ∀ x, 𝓕 f x ≠ 0 → ‖x‖ < N) :
    ‖f.toBoundedContinuousFunction‖ ≤
      Real.sqrt (volume (Metric.ball (0 : V) 1)).toReal *
        N ^ ((Module.finrank ℝ V : ℝ) / 2) * ‖f.toLp 2 volume‖
```

This is `bernstein` + `Measure.addHaar_ball` (ball volume `= N^d · vol(ball 0 1)`).
It also drops the explicit `hs_finite` hypothesis by importing
`Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar` and using `measure_ball_lt_top`.
`#print axioms` = `[propext, Classical.choice, Quot.sound]`.

**A3 (gradient form) is still in flight** (same file, via
`SchwartzMap.fourier_fderivCLM_eq` / `fourier_lineDerivOp_eq` + Plancherel).

---

## Pillar B2 — convolution coupling (done)

`Criticality/ConvolutionCoupling.lean`:

```lean
theorem fourier_convolution_eq_pairing (f g : 𝓢(V, ℂ)) :
    𝓕 (SchwartzMap.convolution (mul ℂ ℂ) f g) = SchwartzMap.pairing (mul ℂ ℂ) (𝓕 f) (𝓕 g)
-- convolution in space = pointwise product in frequency (mathlib's direction)

theorem fourier_mul_eq_convolution (f g : 𝓢(V, ℂ)) :
    𝓕 (SchwartzMap.pairing (mul ℂ ℂ) f g) = SchwartzMap.convolution (mul ℂ ℂ) (𝓕 f) (𝓕 g)
-- multiplication in space = convolution in frequency (the B2 statement)

theorem fourier_mul_apply_eq_integral (f g : 𝓢(V, ℂ)) (ω : V) :
    𝓕 (SchwartzMap.pairing (mul ℂ ℂ) f g) ω = ∫ η : V, (𝓕 f η) * (𝓕 g (ω - η))
-- the all-to-all additive interaction: ω is fed by every pair (η, ω-η)
```

`fourier_convolution_eq_pairing` is literally mathlib's
`SchwartzMap.fourier_convolution`; `fourier_mul_eq_convolution` is its inverse via
Fourier reflection `𝓕(𝓕 f) x = f (-x)` and injectivity; the pointwise form chains
`SchwartzMap.convolution_apply` + `MeasureTheory.convolution_def`. All
`#print axioms` = `[propext, Classical.choice, Quot.sound]`.

---

## Pillar A1 — Heisenberg (commutator form done)

`Criticality/Heisenberg.lean`:

```lean
theorem commutator_integral (f : 𝓢(ℝ, ℝ)) :
    ∫ x, f x * f x = -2 * ∫ x, (x * f x) * deriv (⇑f) x
-- the commutator [x, d/dx] = -1 in integrated form

theorem heisenberg_commutator_real (f : 𝓢(ℝ, ℝ)) :
    ‖f.toLp 2 volume‖ ^ 2 ≤
      2 * ‖(mulCoord f).toLp 2 volume‖ * ‖(derivℝ f).toLp 2 volume‖
-- ‖f‖₂² ≤ 2 · ‖x·f‖₂ · ‖f'‖₂  (position × momentum)
```

mathlib v4.34.0-rc2 has **no** Heisenberg theorem (survey confirmed), so this is
from-scratch: `commutator_integral` (via `SchwartzMap.integral_mul_deriv_eq_neg_deriv_mul`
integration by parts + `d/dx (x·f) = f + x·f'`), then Cauchy–Schwarz
(`integral_mul_norm_le_Lp_mul_Lq`) + Plancherel to connect `‖f'‖₂` to `‖ξ·𝓕 f‖₂`.
The **full variance form** `Δx · Δξ ≥ d/(4π)` (mathlib's `e^{2πixξ}` convention) is
documented in the file as a TODO — it additionally needs the centering/translation
step (mean removal) which is not yet formalized. `#print axioms` =
`[propext, Classical.choice, Quot.sound]`.

---

## Pillar A3 — Bernstein gradient (done)

`Criticality/BernsteinGrowth.lean` (same file as A2):

```lean
theorem bernstein_lineDeriv [CompleteSpace F] (f : 𝓢(V, F)) (m : V) (N : ℝ) (hN : 0 ≤ N)
    (hband : ∀ x, 𝓕 f x ≠ 0 → ‖x‖ < N) :
    ‖(∂_{m} f).toBoundedContinuousFunction‖ ≤
      Real.sqrt (volume (Metric.ball (0 : V) 1)).toReal * (2 * π) * ‖m‖ *
        N ^ (1 + (Module.finrank ℝ V : ℝ) / 2) * ‖f.toLp 2 volume‖

theorem bernstein_gradient [CompleteSpace F] (f : 𝓢(V, F)) (N : ℝ) (hN : 0 ≤ N)
    (hband : ∀ x, 𝓕 f x ≠ 0 → ‖x‖ < N) :
    ‖(SchwartzMap.fderivCLM ℝ V F f).toBoundedContinuousFunction‖ ≤
      Real.sqrt (volume (Metric.ball (0 : V) 1)).toReal * (2 * π) *
        N ^ (1 + (Module.finrank ℝ V : ℝ) / 2) * ‖f.toLp 2 volume‖
```

Route: `𝓕 (∂_m f) = (2πi) • (⟨·,m⟩ · 𝓕 f)` (`SchwartzMap.fourier_lineDerivOp_eq`)
+ the support bound `|⟨x,m⟩| ≤ N·‖m‖` on the ball, then A2 + Plancherel; the
gradient form wraps `bernstein_lineDeriv` via `ContinuousLinearMap.opNorm_le_bound`.
`#print axioms` = `[propext, Classical.choice, Quot.sound]`.

---

## Pillar C — scaling criticality (done)

`Criticality/ScalingCriticality.lean`:

```lean
theorem integral_norm_comp_smul (u : E → ℝ) (p : ℝ) (c : ℝ) :
    ∫ x, ‖u (c • x)‖ ^ p ∂(volume : Measure E)
      = |(c ^ Module.finrank ℝ E)⁻¹| • ∫ x, ‖u x‖ ^ p ∂(volume : Measure E)
-- C2: the L^p integral of a dilation scales by |c|^{-d}  (d = finrank ℝ E)

theorem scaling_exponent_eq_zero_iff {p d : ℝ} (hp : 0 < p) : (1 - d / p = 0) ↔ p = d
-- C2: the critical exponent is exactly p = d (the L^d norm is scale-invariant)

theorem energy_critical_in_dim_two : (1 - (2 : ℝ) / 2 = 0)
theorem energy_subcritical_of_ge_three {d : ℕ} (hd : 3 ≤ d) : (1 - (d : ℝ) / 2 < 0)
-- C3: energy L² is at criticality at d = 2, strictly subcritical at d ≥ 3

theorem ns_scaling_homogeneous_degree : (1 + 2 : ℝ) = 3 ∧ (1 + 1 + 1 : ℝ) = 3 ∧ (1 + 2 : ℝ) = 3
-- C1: the three NS terms (∂ₜu, (u·∇)u, Δu) all rescale by λ³ (exponent form)
```

C2 uses `MeasureTheory.Measure.integral_comp_smul` (dilation change-of-variables);
C3 is the exponent arithmetic; C1 is the homogeneous bookkeeping (documented as
exponent form — a full PDE-level invariance statement is out of scope). All
`#print axioms` = `[propext, Classical.choice, Quot.sound]`.

---

## Pillar D — shell model (moved out)

> **Moved.** The implementation now lives in the sibling library `Cascade/`
> (`Cascade/ShellModel.lean`): a dyadic cascade model is a *model*, not a criticality
> theorem, so its continuation lives on the `dyadic-cascade` branch. The declarations
> below are unchanged — only relocated.

`Cascade/ShellModel.lean` (finite dyadic shell model):

```lean
def shellRHS (ν : ℝ) (C : ℕ → ℝ) (u : ℕ → ℝ) (k : ℕ) : ℝ :=
  C k - ν * (2 : ℝ) ^ (2 * k) * u k
-- du_k/dt = C_k(u) − ν · 2^{2k} · u_k

theorem shell_energy_identity (ν : ℝ) (C : ℕ → ℝ) (u : ℕ → ℝ) (n : ℕ)
    (hC : (Finset.sum (Finset.range n) (fun k => u k * C k)) = 0) :
    (Finset.sum (Finset.range n) (fun k => u k * shellRHS ν C u k))
      = -ν * (Finset.sum (Finset.range n) (fun k => (2 : ℝ) ^ (2 * k) * (u k) ^ 2))
-- D1: energy-conserving coupling ⇒ dE/dt = −2ν Σ 2^{2k} u_k²

theorem transfer_le_dissipation (N : ℝ) (hN : 1 ≤ N) :
    N ^ ((3 : ℝ) / 2) ≤ N ^ (2 : ℝ)
-- D2: Bernstein transfer N^{3/2} is dominated by dissipation N² (the obstruction)
```

D2's `3/2` is the `d = 3` Bernstein exponent `N^{d/2}` of Pillar A
(`Criticality.bernstein_L2_to_Linf`); D1 is a pure finite-sum identity. All
`#print axioms` = `[propext, Classical.choice, Quot.sound]`.

---

## Pillar B1 — dyadic (Littlewood–Paley) grouping (done, structural core)

`Criticality/Dyadic.lean`:

```lean
def dyadicOctave (k : ℕ) : Set ℝ := {ξ | (2 : ℝ) ^ k ≤ ξ ∧ ξ < (2 : ℝ) ^ (k + 1)}

theorem dyadicOctave_disjoint {k l : ℕ} (hkl : k ≠ l) :
    Disjoint (dyadicOctave k) (dyadicOctave l)
-- the multiplicative grouping is a partition (pairwise disjoint octaves)

theorem dyadicOctave_shift (ξ : ℝ) (k : ℕ) :
    ξ ∈ dyadicOctave k ↔ (2 : ℝ) * ξ ∈ dyadicOctave (k + 1)
-- multiplying a frequency by 2 walks to the next octave (multiplicative character)
```

This is the "multiplicative grouping" half of B. The full Littlewood–Paley decomposition
`f = Σₖ 𝓕⁻(φₖ · 𝓕 f)` (smooth cutoffs `φₖ` + partition of unity) is documented in the
file as remaining work; the disjointness/grouping facts are its structural backbone.
`#print axioms` = `[propext, Classical.choice, Quot.sound]`.

---

## Stretch forms (documented, not yet proved)

Fully scoped in their files, deliberately left as `-- TODO`/docstring notes:

1. **A1 variance form** `Δx · Δξ ≥ d/(4π)` (`Heisenberg.lean`) — needs the
   centering/mean-removal (translation + modulation) step; the commutator form is proved.
2. **B1 smooth partition of unity** (`Dyadic.lean`) — needs `exists_smoothPartition`
   / bump-function machinery; the disjoint grouping is proved.
3. **C1 full PDE invariance** (`ScalingCriticality.lean`) — stated in exponent form
   (all three NS terms rescale by `λ³`); a full solution-space invariance statement is
   out of scope.
4. **D3 forced blowup** (`Cascade/ShellModel.lean`) — optional per PLAN; skipped.

---

## Next steps

- **Pillar A:** ✅ complete — core `bernstein`, A1 (Heisenberg commutator form),
  A2 (`L² → L∞`), A3 (gradient). *Remaining (optional, documented in
  `Heisenberg.lean`):* the full variance form `Δx·Δξ ≥ d/(4π)` (needs the
  centering/mean-removal step).
- **Pillar B:** ✅ complete — B1 (`Criticality/Dyadic.lean`, dyadic grouping) and
  B2 (`Criticality/ConvolutionCoupling.lean`, convolution coupling).
- **Pillar C:** ✅ done — `Criticality/ScalingCriticality.lean` (C1 exponent form,
  C2 `integral_norm_comp_smul` + critical exponent, C3 knife's edge).
- **Pillar D:** ✅ done, but **moved out** to the sibling library `Cascade/`
  (`Cascade/ShellModel.lean`) — D1 energy identity, D2 obstruction. A dyadic cascade
  model is not a criticality theorem, so its continuation lives on the `dyadic-cascade`
  branch. D3 (forced blowup) is optional and skipped here.
- **Pillar E:** ✅ done — `Criticality/EulerProduct.lean` re-exposes
  `riemannZeta_eulerProduct` (see the Pillar E section above).

---

## Build & verification

Toolchain is **inside the repo** (gitignored): `.elan/`, `.cache/mathlib`, `.lake/`.

```bash
cd /Users/ronaldrogers/Code/NavierStokesAndEuler
export ELAN_HOME="$PWD/.elan"
export PATH="$ELAN_HOME/bin:$PATH"
export MATHLIB_CACHE_DIR="$PWD/.cache/mathlib"
lake build Criticality          # just the skeleton (fast)
lake build                      # full repo (slow)
```

- Toolchain: `leanprover/lean4:v4.34.0-rc2` (from `lean-toolchain`).
- Deps (`lakefile.toml`): `mathlib` and `Comparator`, both rev `v4.34.0-rc2`.
- `#print axioms <name>` is appended at the bottom of each file; `lake build`
  prints the `info:` lines with the axiom sets.

**Fresh machine:** re-install elan into the repo
(`curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf
| sh -s -- -y --no-modify-path --default-toolchain none` with `ELAN_HOME` set),
`elan toolchain install leanprover/lean4:v4.34.0-rc2`, `lake update`,
`lake exe cache get`.

---

## Elaboration gotchas (learned the hard way)

1. **`𝓢(V, F)`** needs `open scoped SchwartzMap`.
2. **`ℝ≥0∞`** needs `open scoped ENNReal`.
3. **`𝓕` / `𝓕⁻`** need `open scoped FourierTransform`.
4. **Huge defs that unfold and time out** (mark `[local irreducible]`):
   - `SchwartzMap.fourierTransformCLM` (Schwartz Fourier),
   - `MeasureTheory.Lp.fourierTransformₗᵢ` (L² Fourier),
   - `Real.rpow` (`^(1/2 : ℝ)`).
   **`[local irreducible]` does NOT propagate across imports** — every file that
   touches `𝓕`/`𝓕⁻` or `^(1/2 : ℝ)` must re-declare the attribute locally.
5. **`Real.sqrt x` is not defeq to `x ^ (1/2)`** — use `Real.sqrt_eq_rpow`.
6. **`ENNReal.toReal_le_toReal`** needs *both* sides `≠ ⊤`; use `.2` with two
   finiteness proofs (`ofReal_integral_eq_lintegral_ofReal` → `ENNReal.ofReal_ne_top`,
   and `lintegral_one` + `restrict_apply_univ` + `hs_finite.ne`).
7. **`ENNReal.rpow_ne_top_of_nonneg (hy0) (h_ne_top)`** — nonneg `0 ≤ y` is the
   **first** argument, finiteness `x ≠ ⊤` second.
8. **`Integrable (fun x => ‖g x‖ ^ p)`** from `MemLp`: `MemLp.integrable_norm_rpow`
   on `g.memLp 2 volume`, then `.mono_measure MeasureTheory.Measure.restrict_le_self`.
9. **`norm_toLp'` leaves `(2 : ℝ≥0∞).toReal` unsimplified**; `norm_num
   [ENNReal.toReal_ofNat]` simplifies it but also converts `^(2 : ℝ)` → `^(2 : ℕ)`;
   match the power type or use `Real.rpow_natCast`.
10. **`setIntegral_le_integral`** takes `Integrable f μ` first, then the nonneg as
    an **a.e.** statement (`Filter.Eventually.of_forall`).
11. **Ball membership** `x ∈ Metric.ball 0 N` is not syntactically `‖x‖ < N`;
    bridge with `simpa [Metric.mem_ball, dist_eq_norm]`.
12. **`Real.HolderConjugate 2 2`** is `Real.HolderTriple 2 2 1`; prove with
    `refine ⟨?_, ?_, ?_⟩ <;> norm_num`.
13. **Plancherel needs `[InnerProductSpace ℂ F]`.** `SchwartzMap.norm_fourier_toL2_eq`,
    `MeasureTheory.Lp.norm_fourier_eq`, and `Lp.fourierTransformₗᵢ` all assume a
    complex *inner-product* space; there is no Plancherel for `[NormedSpace ℂ F]`
    alone. This is why `bernstein`'s `F` had to be strengthened.
14. **The direct Schwartz-Plancherel lemma beats composing the L² one.** Use
    `SchwartzMap.norm_fourier_toL2_eq f` (already `@[simp]`) for
    `‖(𝓕 f).toLp 2‖ = ‖f.toLp 2‖`; composing `SchwartzMap.toLp_fourier_eq` with
    `MeasureTheory.Lp.norm_fourier_eq` forces `𝓕 (f.toLp 2)` to elaborate, which is
    the expensive path.
15. **Write the measure explicitly** (`‖f.toLp 2 volume‖`) when `𝓕` meets `toLp`;
    the `volume_tac` default can fail with *"could not synthesize default value for
    parameter 'μ'"* mid-elaboration.
