# Criticality Skeleton — Plan & Handoff

This is the durable plan for the **"criticality skeleton"** formalization: the
machine-checkable mathematical core of the *additive/multiplicative +
concentration-barrier + 3D-criticality* picture that surfaced in a long
conversation about the OpenAI Navier–Stokes/Euler Lean formalization (repo
`NavierStokesAndEuler`) and the surrounding mathematics.

> **State snapshot:** branch `skeleton-criticality`, commit `5ee60ab`.
> Builds with `lake build Criticality`. Three theorems machine-checked
> (`#print axioms` = `[propext, Classical.choice, Quot.sound]`); one theorem
> (`bernstein`) stated with its last proof step pending.

---

## 0. What this formalizes (the intuition)

A recurring theme in the discussion was a *tension between two organizations*:

- **additive** — frequency interaction is a *convolution* (`ω` is fed by every
  pair `(ξ, η)` with `ξ + η = ω`); in number theory, the Dirichlet series
  `ζ(s) = Σ n⁻ˢ`.
- **multiplicative** — frequencies are *grouped dyadically* (octaves `[2ᵏ, 2ᵏ⁺¹)`);
  in number theory, the Euler product `ζ(s) = ∏ (1 − p⁻ˢ)⁻¹`.

The **concentration barrier** (Heisenberg uncertainty / Bernstein's inequality)
is the quantitative statement that *band-limiting to frequency `N` forces
spatial spread `≳ 1/N`*, hence caps how concentrated a fixed amount of energy
can be. This is exactly the tool that makes the **unforced** frequency cascade
subcritical against viscous dissipation (`~N²`) in 3D — the "obstruction"
(tweet/arXiv:2605.13827, Palasek) to removing the forcing from a Navier–Stokes
blowup.

The skeleton's job: formalize the *provable core* of this picture — not the
physics analogies (AdS/CFT, "why 3D", Hilbert–Pólya), which are **not** Lean-able.

---

## 1. The five pillars (the full plan)

| pillar | content | status |
|---|---|---|
| **A** | concentration barrier: Heisenberg + Bernstein | core **proved**; `bernstein` last step pending |
| **B** | dyadic decomposition + convolution coupling | not started |
| **C** | Navier–Stokes scaling criticality (`L^d`) | not started |
| **D** | dyadic shell model + the transfer-vs-dissipation obstruction | not started |
| **E** | Euler product (`Σ n⁻ˢ = ∏ (1−p⁻ˢ)⁻¹`) | **already in mathlib** (`riemannZeta_eulerProduct`) |

Concrete theorems per pillar:

- **A1 (Heisenberg):** `Δx(f) · Δξ(f) ≥ d/2` for `f ∈ L²(ℝ^d)` (variances).
- **A2 (Bernstein L²→L∞):** `supp(f̂) ⊆ B(0,N) ⟹ ‖f‖∞ ≤ C_d N^{d/2} ‖f‖₂`.
- **A3 (Bernstein gradient):** `‖∇f‖∞ ≤ C_d N^{1+d/2} ‖f‖₂`.
- **A4 (shared core):** one lemma — "band-limiting ⇒ spread ≳ 1/N" — from which
  A1–A3 all follow (the formal "Heisenberg and Bernstein are the same principle").

- **B1 (dyadic decomposition):** any `f` splits into a sum of band-limited pieces
  (Littlewood–Paley).
- **B2 (additive coupling):** multiplication in space = convolution in frequency
  (the Fourier transform of `(u·∇)u` is fed by all pairs summing to `ω`).

- **C1 (scaling symmetry):** `u_λ(x,t) = λ·u(λx, λ²t)` preserves NS (with `p_λ = λ²p`).
- **C2 (critical norm):** `L^d` is scale-invariant (`2/p + d/q = 1` for `LᵖₜL^qₓ`).
- **C3 (knife's edge):** energy `L²` is at criticality at `d = 2`, strictly
  subcritical for `d ≥ 3` (so 3 is the first "just barely supercritical" dimension).

- **D1 (energy identity):** the shell-model energy balance (`d/dt` energy = `−ν Σ 2²ᵏ|u_k|²`).
- **D2 (the obstruction, rigorous in the model):** unforced lacunary cascade has
  transfer `O(N_k^{3/2})` (via Bernstein, pillar A) < dissipation `N_k²` ⇒ cannot
  self-sustain. This is the tweet's argument, made a theorem *in the shell model*.
- **D3 (optional):** with forcing, the shell model blows up (Palasek-type, in the model).

- **E1:** `riemannZeta_eulerProduct` — already in mathlib
  (`Mathlib/NumberTheory/EulerProduct/DirichletLSeries.lean`).

---

## 2. Current status (exactly where we left off)

Files (branch `skeleton-criticality`, commit `5ee60ab`):

- `Criticality/ConcentrationBarrier.lean` — **Pillar A core, fully proved**
- `Criticality/Bernstein.lean` — **Cauchy–Schwarz proved; `bernstein` stated**
- `Criticality.lean` — entry point (`import Criticality.ConcentrationBarrier`)
- `lakefile.toml` — added `[[lean_lib]] name = "Criticality"`
- `.gitignore` — added `.elan/` and `.cache/`

### Proved (standard axioms only)

```lean
-- ConcentrationBarrier.lean
theorem fourierInv_apply_le_toLp_one (f : 𝓢(V, F)) (x : V) :
    ‖𝓕⁻ f x‖ ≤ ‖f.toLp 1‖
-- the inverse Fourier transform maps L¹ → L∞

theorem pointwise_le_L1_fourier [CompleteSpace F] (f : 𝓢(V, F)) (x : V) :
    ‖f x‖ ≤ ‖(𝓕 f).toLp 1‖
-- THE core concentration barrier: spread in frequency ⇒ bounded in space

-- Bernstein.lean
theorem norm_toLp_one_le_sqrt_measure_mul_norm_toLp_two
    (g : 𝓢(V, F)) {s : Set V} (hs : MeasurableSet s) (hs_finite : volume s < ⊤)
    (hsupp : ∀ x, g x ≠ 0 → x ∈ s) :
    ‖g.toLp 1‖ ≤ Real.sqrt (volume s).toReal * ‖g.toLp 2‖
-- Cauchy–Schwarz with support
```

The Cauchy–Schwarz proof is the substantive result of the whole session. Its
chain (all machine-checked):

1. `‖g‖₁ = ∫‖g‖` (`SchwartzMap.norm_toLp_one`), `= ∫_s ‖g‖`
   (`setIntegral_eq_integral_of_forall_compl_eq_zero`).
2. **ENNReal Hölder** `∫⁻_s ‖g‖ ≤ (∫⁻_s ‖g‖²)^{1/2}·(∫⁻_s 1)^{1/2}` via
   `ENNReal.lintegral_mul_le_Lp_mul_Lq` with `p = q = 2` (this was the hard step —
   the real-valued `integral_mul_norm_le_Lp_mul_Lq` caused a `whnf` timeout).
3. Full `ℝ ↔ ℝ≥0∞` conversion: `ENNReal.toReal_le_toReal`, `toReal_mul`,
   `lintegral_one`, `Measure.restrict_apply_univ`, `ENNReal.toReal_rpow`,
   `Real.sqrt_eq_rpow`, `ofReal_integral_eq_lintegral_ofReal`, `ENNReal.toReal_ofReal`,
   `norm_toLp'` (p=2).
4. Finiteness: `Integrable (fun x => ‖g x‖ ^ 2)` via
   `MemLp.integrable_norm_rpow` on `g.memLp 2 volume`, then `.mono_measure`.

### Stated (one `sorry`)

```lean
-- Bernstein.lean
theorem bernstein [CompleteSpace F] (f : 𝓢(V, F)) (N : ℝ)
    (hband : ∀ x, 𝓕 f x ≠ 0 → ‖x‖ < N)
    (hs_finite : volume (Metric.ball (0 : V) N) < ⊤) :
    ‖f.toBoundedContinuousFunction‖ ≤
      Real.sqrt (volume (Metric.ball (0 : V) N)).toReal * ‖f.toLp 2‖
```

`bernstein` is a **three-line composition**, two of which are already written and
typecheck (they are in the file, currently replaced by one `sorry`):

```lean
have h1 : ‖f.toBoundedContinuousFunction‖ ≤ ‖(𝓕 f).toLp 1‖          -- sup form of core lemma
have h2 : ‖(𝓕 f).toLp 1‖ ≤ √(vol ball)·‖(𝓕 f).toLp 2‖               -- Cauchy–Schwarz on 𝓕 f
have h3 : ‖(𝓕 f).toLp 2‖ = ‖f.toLp 2‖                               -- Plancherel (BLOCKED)
```

`h1` and `h2` compile; **only `h3` is blocked** (see §3).

---

## 3. Pillar A — remaining work (exactly one step)

**`h3` is the Plancherel step.** It is provable from:

```lean
SchwartzMap.toLp_fourier_eq f  :  𝓕 (f.toLp 2) = (𝓕 f).toLp 2   -- bridges Schwartz 𝓕 and L² 𝓕
MeasureTheory.Lp.norm_fourier_eq (f.toLp 2)  :  ‖𝓕 (f.toLp 2)‖ = ‖f.toLp 2‖
```

**The blocker** (not mathematics — an elaboration issue):

- The L² Fourier transform `MeasureTheory.Lp.fourierTransformₗᵢ` is a huge
  `extendOfIsometry` term. Elaborating `𝓕 (f.toLp 2)` (and hence
  `norm_fourier_eq (f.toLp 2)` or `toLp_fourier_eq`) unfolds it and hits a
  deterministic `whnf` heartbeat timeout.
- `attribute [local irreducible] MeasureTheory.Lp.fourierTransformₗᵢ` was already
  added to `Bernstein.lean` (line near the top), but the step still times out —
  the remaining issue is the **measure coercion**: `norm_fourier_eq (f.toLp 2)`
  reports *"could not synthesize default value for parameter 'μ'"*.

**Likely fixes to try (in order):**

1. Make the *instance* irreducible, not just the def:
   `attribute [local irreducible] MeasureTheory.Lp.instFourierTransform`.
2. Pass the measure explicitly:
   `MeasureTheory.Lp.norm_fourier_eq (E := V) (F := F) (μ := volume) (f.toLp 2 (volume : Measure V))`.
3. Or route through `SchwartzMap.toLp_fourier_eq` with explicit measures, or use
   `convert` / `simpa only [SchwartzMap.toLp_fourier_eq]` (both already tried;
   the timeout/`μ` error is the residue).
4. Worst case: state `h3` as a separate `theorem` (a small Plancherel-for-Schwartz
   lemma) and prove it in isolation with a fresh `set_option maxHeartbeats` and
   the irreducible attributes.

After `h3` closes, `bernstein` is done (the `calc` is already written).

**Note on `hs_finite`:** it is an explicit hypothesis because
`[IsFiniteMeasureOnCompacts volume]` is **not** an instance for a general
finite-dimensional inner-product space `V` (only `IsLocallyFiniteMeasure` for
`ℝ`). For `V = EuclideanSpace ℝ (Fin d)` the hypothesis follows from
`measure_ball_lt_top` (needs `[ProperSpace V]` via `FiniteDimensional.proper ℝ V`).
Decide later whether to keep `hs_finite` explicit or specialize `bernstein` to
`EuclideanSpace ℝ (Fin d)`.

---

## 4. Pillars B–E — concrete first steps

### Pillar B (dyadic decomposition + convolution coupling)

- **B2 first** (smaller, self-contained): "multiplication in space = convolution
  in frequency." mathlib has `MeasureTheory.convolution` and the Fourier/convolution
  interchange; look in `Mathlib/Analysis/Fourier/Convolution.lean` and
  `Mathlib/Analysis/Fourier/FourierTransform.lean` for
  `fourierIntegral_convolution` / `fourierIntegral_mul`-type lemmas. State:
  `𝓕 (f * g) = (𝓕 f) ⋆ (𝓕 g)` (up to normalization), or the "frequency `ω` is fed
  by all `(ξ, η)` with `ξ + η = ω`" form.
- **B1**: Littlewood–Paley dyadic partition of unity. mathlib has
  `Mathlib/Analysis/Calculus/ContDiff/…`, `Mathlib/Analysis/Distribution/…` and the
  Fourier multipliers; check for existing dyadic decomposition lemmas before
  building from scratch.

### Pillar C (Navier–Stokes scaling criticality)

- Needs a minimal NS definition (the repo already has `NavierStokes` definitions in
  `NavierStokes/ProblemStatement.lean` / the comparator definitions — reuse or
  import them).
- **C1** (scaling): pure computation, `u_λ(x,t) = λ u(λx, λ²t)`.
- **C2** (critical norm): show `‖u_λ‖_{L^p} = λ^{1 + d/p}‖u‖_{L^p}`, invariant iff `p = d`.
- **C3** (knife's edge): compare energy (`L²`) vs `L^d` for `d = 2, 3, ≥4`.

### Pillar D (dyadic shell model + obstruction)

- Define the shell ODEs (self-contained): `du_k/dt = N_k(u) − ν 2^{2k} u_k` with
  nearest-neighbor coupling.
- **D1** energy identity, **D2** the Bernstein-based transfer-vs-dissipation bound
  (uses pillar A's Bernstein), **D3** (optional) forced blowup in the model.

### Pillar E (Euler product)

- Already done in mathlib: `import Mathlib.NumberTheory.EulerProduct.DirichletLSeries`
  and `#check riemannZeta_eulerProduct`. Just a re-exposure/comment file.

---

## 5. Build & verification

Toolchain is **inside the repo** (gitignored): `.elan/` (elan + toolchain),
`.cache/mathlib` (mathlib olean cache), `.lake/` (lake build + cloned deps).

```bash
cd /Users/ronaldrogers/Code/NavierStokesAndEuler
export ELAN_HOME="$PWD/.elan"
export PATH="$ELAN_HOME/bin:$PATH"
export MATHLIB_CACHE_DIR="$PWD/.cache/mathlib"
lake build Criticality          # build just the skeleton (fast)
lake build                      # full repo (NavierStokes + Euler + Comparator + Criticality; slow)
```

- Toolchain: `leanprover/lean4:v4.34.0-rc2` (from `lean-toolchain`).
- Deps (from `lakefile.toml`): `mathlib` and `Comparator`, both at rev `v4.34.0-rc2`.
- `#print axioms <name>` is appended at the bottom of each file; `lake build` prints
  the `info:` lines with the axiom sets.

**If `.elan/`/`.cache/` are missing (fresh machine):** re-install elan
(`curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf
| sh -s -- -y --no-modify-path --default-toolchain none` with `ELAN_HOME` set into
the repo), `elan toolchain install leanprover/lean4:v4.34.0-rc2`,
`lake update`, `lake exe cache get`.

---

## 6. Elaboration gotchas (learned the hard way — for future agents)

1. **`𝓢(V, F)`** (Schwartz space) needs `open scoped SchwartzMap`.
2. **`ℝ≥0∞`** notation needs `open scoped ENNReal`.
3. **`𝓕` / `𝓕⁻`** need `open scoped FourierTransform`.
4. **Huge defs that unfold and time out** (mark `[local irreducible]`):
   - `SchwartzMap.fourierTransformCLM` (Schwartz Fourier).
   - `MeasureTheory.Lp.fourierTransformₗᵢ` (L² Fourier) — *still the blocker for `h3`*.
   - `Real.rpow` (the `^(1/2 : ℝ)`).
5. **`Real.sqrt x` is not defeq to `x ^ (1/2)`** — use `Real.sqrt_eq_rpow`.
6. **`ENNReal.toReal_le_toReal`** (the iff) needs *both* sides `≠ ⊤`; use the
   `.2` direction with two finiteness proofs (via `ofReal_integral_eq_lintegral_ofReal`
   → `ENNReal.ofReal_ne_top`, and `lintegral_one` + `restrict_apply_univ` + `hs_finite.ne`).
7. **`ENNReal.rpow_ne_top_of_nonneg (hy0) (h_ne_top)`** — the nonneg `0 ≤ y` is the
   **first** argument, finiteness `x ≠ ⊤` second.
8. **`Integrable (fun x => ‖g x‖ ^ p)`** from `MemLp`: use
   `MemLp.integrable_norm_rpow` (on `g.memLp 2 volume`), then `.mono_measure
   MeasureTheory.Measure.restrict_le_self` for the restricted measure.
9. **`norm_toLp'` leaves `(2 : ℝ≥0∞).toReal` unsimplified**; `norm_num
   [ENNReal.toReal_ofNat]` simplifies it, but `norm_num` *also* converts `^(2 : ℝ)`
   (rpow) to `^(2 : ℕ)` (pow) — watch for that mismatch; match the power type or
   use `Real.rpow_natCast` to convert.
10. **`setIntegral_le_integral`** takes `Integrable f μ` first, then the nonneg
    as an **a.e.** statement (`Filter.Eventually.of_forall`).
11. **`hband`/ball membership**: `x ∈ Metric.ball 0 N` is *not* syntactically
    `‖x‖ < N`; bridge with `simpa [Metric.mem_ball, dist_eq_norm]`.
12. **`Real.HolderConjugate 2 2`** is `Real.HolderTriple 2 2 1` (a structure);
    prove with `refine ⟨?_, ?_, ?_⟩ <;> norm_num`.

---

## 7. Mathematical context (for a fresh reader/agent)

- The surrounding repo `NavierStokesAndEuler` is OpenAI's Lean formalization of
  finite-time blowup: **forced** Navier–Stokes breakdown (Clay options (C)/(D))
  and an **unforced** Euler `C¹` blowup. All four main theorems there check with
  standard axioms only (verified earlier in the conversation).
- The forced result does **not** transfer to the unforced problem; the specific
  obstruction (tweet, arXiv:2605.13827 by Stan Palasek) is the Bernstein +
  energy-depletion argument: unforced lacunary transfer `O(N^{3/2})` is beaten by
  dissipation `N²`; the force is what overcomes dissipation.
- **3D is the critical dimension**: energy `L²` equals the critical norm `L^d` at
  `d = 2`, and is strictly subcritical at `d ≥ 3` (knife's edge). This is the
  Pillar C content.
- The additive/multiplicative duality has two avatars:
  - frequencies: convolution (additive) vs dyadic grouping (multiplicative);
  - number theory: Dirichlet series (additive) vs Euler product (multiplicative) —
    already equal by `riemannZeta_eulerProduct` (Pillar E).
- **Out of scope (not Lean-able):** AdS/CFT as a bridge, "why is the universe 3D",
  Hilbert–Pólya/Berry–Keating. The skeleton formalizes only the *provable core*.

---

*To resume: solve `h3` (§3), then continue Pillar A→B→C→D as in §1/§4. The build
is green; the only `sorry` is inside `bernstein`.*
