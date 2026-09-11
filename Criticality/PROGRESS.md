# Progress: Criticality Skeleton

Where we are now. This file changes as we work. The *target* is `PLAN.md`; the
*why* is `VISION.md`.

> **Snapshot:** branch `skeleton-criticality`, commits `5ee60ab` (skeleton) and
> `aca9e8a` (plan). Build is green: `lake build Criticality` succeeds.
> Three theorems machine-checked (`#print axioms` = `[propext, Classical.choice,
> Quot.sound]`); one theorem (`bernstein`) has one pending proof step.

---

## Proved (standard axioms only)

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

## Stated (one `sorry`)

`Criticality/Bernstein.lean`:

```lean
theorem bernstein [CompleteSpace F] (f : 𝓢(V, F)) (N : ℝ)
    (hband : ∀ x, 𝓕 f x ≠ 0 → ‖x‖ < N)
    (hs_finite : volume (Metric.ball (0 : V) N) < ⊤) :
    ‖f.toBoundedContinuousFunction‖ ≤
      Real.sqrt (volume (Metric.ball (0 : V) N)).toReal * ‖f.toLp 2‖
```

`bernstein` is a **three-line composition**; two lines are written and typecheck
(they are in the file, currently collapsed to one `sorry`):

```lean
have h1 : ‖f.toBoundedContinuousFunction‖ ≤ ‖(𝓕 f).toLp 1‖        -- sup form of the core lemma
have h2 : ‖(𝓕 f).toLp 1‖ ≤ √(vol ball)·‖(𝓕 f).toLp 2‖             -- Cauchy–Schwarz on 𝓕 f
have h3 : ‖(𝓕 f).toLp 2‖ = ‖f.toLp 2‖                             -- Plancherel (BLOCKED)
```

`h1` and `h2` compile; **only `h3` is blocked.**

---

## Pillar A — the one remaining step (`h3`)

**`h3` is the Plancherel step.** It is provable from:

```lean
SchwartzMap.toLp_fourier_eq f   :  𝓕 (f.toLp 2) = (𝓕 f).toLp 2   -- bridges Schwartz 𝓕 and L² 𝓕
MeasureTheory.Lp.norm_fourier_eq (f.toLp 2)  :  ‖𝓕 (f.toLp 2)‖ = ‖f.toLp 2‖
```

**The blocker (elaboration, not mathematics):** the L² Fourier transform
`MeasureTheory.Lp.fourierTransformₗᵢ` is a huge `extendOfIsometry` term.
Elaborating `𝓕 (f.toLp 2)` unfolds it and hits a deterministic `whnf` heartbeat
timeout. `attribute [local irreducible] MeasureTheory.Lp.fourierTransformₗᵢ` is
already in `Bernstein.lean`, but the step still reports
*"could not synthesize default value for parameter 'μ'"*.

**Fixes to try, in order:**

1. Make the *instance* irreducible, not just the def:
   `attribute [local irreducible] MeasureTheory.Lp.instFourierTransform`.
2. Pass the measure explicitly:
   `MeasureTheory.Lp.norm_fourier_eq (E := V) (F := F) (μ := volume) (f.toLp 2 (volume : Measure V))`.
3. Or `convert` / `simpa only [SchwartzMap.toLp_fourier_eq]` (both already tried;
   the `μ` error is the residue).
4. Fallback: state `h3` as a standalone lemma (Plancherel-for-Schwartz) and prove
   it in isolation with a fresh `set_option maxHeartbeats` + the irreducible attrs.

After `h3` closes, `bernstein` is done (the `calc` is written).

**Note on `hs_finite`:** it is an explicit hypothesis because
`[IsFiniteMeasureOnCompacts volume]` is not an instance for a general
finite-dimensional inner-product space `V` (only `IsLocallyFiniteMeasure` for
`ℝ`). For `V = EuclideanSpace ℝ (Fin d)` it follows from `measure_ball_lt_top`
(needs `[ProperSpace V]` via `FiniteDimensional.proper ℝ V`). Decide later whether
to keep `hs_finite` explicit or specialize `bernstein` to `EuclideanSpace ℝ (Fin d)`.

---

## Next steps (after `h3`)

- **Pillar A finish:** close `h3`; then add **A2/A3 (Bernstein)** on top of the
  core + Cauchy–Schwarz (band-limited `‖f‖∞ ≲ N^{d/2}‖f‖₂`, and the gradient form),
  and **A1 (Heisenberg)** from the shared core.
- **Pillar B:** B2 (convolution coupling) first — look in
  `Mathlib/Analysis/Fourier/Convolution.lean` and `FourierTransform.lean` for
  `fourierIntegral_convolution`-type lemmas. Then B1 (Littlewood–Paley dyadic
  decomposition).
- **Pillar C:** reuse the repo's `NavierStokes` definitions; C1 (scaling) is a
  computation, C2 (critical norm) is `‖u_λ‖_{L^p} = λ^{1+d/p}‖u‖_{L^p}`,
  C3 (knife's edge) is the `L²` vs `L^d` comparison.
- **Pillar D:** define the shell ODEs; D1 energy identity; D2 obstruction using
  Pillar A's Bernstein; D3 (optional) forced blowup.
- **Pillar E:** `import Mathlib.NumberTheory.EulerProduct.DirichletLSeries` and
  `#check riemannZeta_eulerProduct` — a re-exposure file.

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
   - `MeasureTheory.Lp.fourierTransformₗᵢ` (L² Fourier) — *still the `h3` blocker*,
   - `Real.rpow` (`^(1/2 : ℝ)`).
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
