# Lean 4 Formalizations of Analysis / PDE / Fluid Dynamics — verified survey

Research method: **primary sources only**. Every declaration name, path, toolchain string, and repository fact below was obtained by fetching the raw file or the GitHub API / GitHub HTML / Reservoir / Zenodo page named. Statements that are the *project's own claim* (e.g. "sorry-free", "kernel-only") are labelled as such and were not independently re-checked unless I say I fetched the source. Fetch date: session system date **2026‑09‑12**.

Spelling note: the DeepMind directory is genuinely misspelled `FormalConjectures/Millenium/` (one "n").

---

## Area 1 — mathlib4's own PDE / analysis coverage

Repo: **https://github.com/leanprover-community/mathlib4**
Metadata fetched from `api.github.com/repos/leanprover-community/mathlib4`: 4106 stars, 1677 forks, 3372 open issues, **not archived**, default branch `master`, `pushed_at` 2026‑09‑12, Apache‑2.0.

### 1.1 Sobolev / Bessel-potential spaces — PRESENT, real proofs

| Thing | Value |
|---|---|
| (a) URL | https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Analysis/Distribution/Sobolev.lean |
| (d) Module | `Mathlib.Analysis.Distribution.Sobolev` (raw fetch HTTP 200) |
| (d) Declarations verified in source | `TemperedDistribution.besselPotential`; `TemperedDistribution.MemSobolev`; `SchwartzMap.memSobolev`; `TemperedDistribution.memSobolev_iff_exists_smulLeftCLM_fourier`; `TemperedDistribution.MemSobolev.fourier_memL1`; `TemperedDistribution.MemSobolev.fourierMultiplierCLM_of_bounded`; `.mono`; `.lineDerivOp`; `.laplacian` |
| (e) Status | Fully proved; no `sorry` in the fetched file. Header dates it 2026, author Moritz Doll. |

Bundled variant (also raw-fetched HTTP 200):
- `Mathlib/Analysis/FunctionalSpaces/BesselPotentialSpace.lean` — `structure BesselPotentialSpace`, notation `H^{s,p}(E,F)` / `H^{s}(E,F)`, `toLpₗᵢ` (linear isometry equiv to `Lp`), `CompleteSpace`, `InnerProductSpace`, and `TemperedDistribution.MemSobolev.toBesselPotentialSpace`. Fully proved.

Gagliardo–Nirenberg–Sobolev inequality (raw fetch HTTP 200):
- `Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean` — verified decls: `MeasureTheory.lintegral_mul_prod_lintegral_pow_le`; `MeasureTheory.lintegral_pow_le_pow_lintegral_fderiv`; `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_one`; `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq`; `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_le`. Fully proved.
- Note: the full **Sobolev embedding theorem** (H^s ⊂ C^k / L^q) is *not* present as such; `MemSobolev.fourier_memL1` is described in-source as "the main calculation of the Sobolev embedding theorem".

### 1.2 Distributions / Schwartz space / tempered distributions — PRESENT

Verified by fetching `api.github.com/.../contents/Mathlib/Analysis/Distribution` (HTTP 200). Files in `Mathlib/Analysis/Distribution/`:
`AEEqOfIntegralContDiff.lean`, `ContDiffMapSupportedIn.lean`, `DerivNotation.lean`, `Distribution.lean`, `FourierMultiplier.lean`, `Sobolev.lean`, `Support.lean`, `TemperateGrowth.lean`, `TemperedDistribution.lean`, `TestFunction.lean`, and the subdirectory `SchwartzSpace/` containing `Basic.lean`, `Deriv.lean`, `Fourier.lean` (all three raw-fetched list confirmed).

So `Mathlib.Analysis.Distribution.SchwartzSpace` is a **directory** with modules `Mathlib.Analysis.Distribution.SchwartzSpace.{Basic,Deriv,Fourier}` (not a single file).

### 1.3 Fourier analysis, convolution, Gaussian — PRESENT

`Mathlib/Analysis/Fourier/` (API listing, HTTP 200):
`AddCircle.lean`, `AddCircleMulti.lean`, `BoundedContinuousFunctionChar.lean`, `Convolution.lean`, `FiniteAbelian/`, `FourierTransform.lean`, `FourierTransformDeriv.lean`, `Inversion.lean`, `LpSpace.lean`, `Notation.lean`, `PoissonSummation.lean`, `RiemannLebesgueLemma.lean`, `ZMod.lean`.

`Mathlib/MeasureTheory/Group/` (API listing, HTTP 200) includes `Convolution.lean`, `IntegralConvolution.lean`, `Integral.lean`, `LIntegral.lean` — i.e. measure-theoretic convolution is present.

`Mathlib/Analysis/SpecialFunctions/Gaussian/` (API listing, HTTP 200): `GaussianIntegral.lean`, `FourierTransform.lean`, `PoissonSummation.lean`. Adjacent: `Mathlib/Analysis/SpecialFunctions/MulExpNegMulSq.lean`, `MulExpNegMulSqIntegral.lean`.

### 1.4 Laplacian — PRESENT

Raw fetch HTTP 200: `Mathlib/Analysis/InnerProductSpace/Laplacian.lean` — `InnerProductSpace.laplacianWithin`, `Laplacian.laplacian` instance, scoped notation `Δ` / `Δ[s]`, plus basis formulas and linearity lemmas. Author Stefan Kebekus, 2025.

### 1.5 Bernstein — PRESENT BUT NOT THE HARMONIC-ANALYSIS OBJECT

Raw fetch HTTP 200: `Mathlib/Analysis/SpecialFunctions/Bernstein.lean` is **Bernstein polynomials / Weierstrass approximation**: `bernstein`, `bernstein_apply`, `bernstein_nonneg`, `bernstein.probability`, `bernstein.variance`, `bernsteinApproximation`, `bernsteinApproximation_uniform`.

⚠️ This is **not** the Littlewood–Paley "Bernstein inequality" (frequency-localised derivative bounds). No such thing found.

### 1.6 NOT FOUND in mathlib (as of this survey)

- **Besov spaces** — no file/declaration found.
- **Littlewood–Paley theory** — no file/declaration found.
- **Bernstein inequalities (harmonic analysis)** — no file/declaration found; the only "Bernstein" is the polynomial/approximation file above.
- **Heat kernel / heat semigroup** — no file found. `api.github.com/.../contents/Mathlib/Analysis/PDE` returns **404** (no PDE directory); no `Heat*` file in `SpecialFunctions/` or `Gaussian/`.
- **Full Sobolev embedding theorem, weak-derivative Sobolev spaces** — not in mathlib (the DeGiorgi project's README makes the same claim for itself; see Area 3).

**Access caveat for 1.6:** GitHub code search is login-gated. `https://github.com/search?q=repo%3Aleanprover-community%2Fmathlib4+heatKernel&type=code` returned GitHub's sign-in shell, and `api.github.com/search/code` requires a token. Absence in 1.6 therefore rests on (i) full directory listings of the relevant mathlib subtrees and (ii) targeted raw-path checks, **not** an exhaustive repo-wide grep. Treat "no Besov/LP/heat kernel" as "not found by these means".

---

## Area 2 — Lean 4 Navier–Stokes / Euler repos other than openai/NavierStokesAndEuler

### 2.1 `uda-lab/leray-hopf` — real Navier–Stokes formalization, PROVED

| Field | Value |
|---|---|
| (a) URL | https://github.com/uda-lab/leray-hopf — Reservoir page https://reservoir.lean-lang.org/@uda-lab/lerayHopf (note: `uda-lab/lerayHopf` as a **GitHub repo path 404s**; the real slug is `leray-hopf`) |
| (b) Status | API: 11 stars, 1 fork, 1 open issue, **not archived**, created 2026‑06‑19, `pushed_at` 2026‑08‑08, Apache‑2.0, language Lean. Reservoir: "a month ago", 11 stars. Topics include `navier-stokes`, `leray-hopf`, `partial-differential-equations`. |
| (c) Toolchain | raw `lean-toolchain` = `leanprover/lean4:v4.31.0-rc2` (Reservoir lists support across v4.31.0-rc2 … v4.34.0-rc2) |
| (d) Source verified | raw `LerayHopf/Torus/GalerkinODECapstone.lean`: `galSeq_of_torus`, `build_galerkin_package_of_galSeq`, `build_galerkin_package_of_torus`, and theorem **`exists_lerayHopf_torus3`**. README (raw) additionally names `exists_lerayHopf_r3`, `exists_global_lerayHopf_torus3`, `exists_global_lerayHopf_r3`, files `LerayHopf/Torus/GlobalCapstone.lean` and `LerayHopf/R3/GlobalCapstone.lean`. |
| (e) Status | README claims: four capstones kernel-only, `#print axioms` returns only `propext, Classical.choice, Quot.sound`, no project axioms, no `sorryAx`. The capstone file I fetched contains no `sorry` and its doc-comments describe discharging former axioms. **I did not run `#print axioms` or build the repo**, so the kernel-only claim is the project's own. |

Scope (README, verbatim facts): homogeneous NS (no external force), Leray–Hopf **weak** solutions on 𝕋³ (period 1) and ℝ³, finite-horizon and global-in-time; separated-variable test functions; energy **inequality**; no smoothness/regularity, no uniqueness claims.

### 2.2 `tristanbuckmaster/fluid_lean` — Euler blow-up AND Boussinesq blow-up

| Field | Value |
|---|---|
| (a) URL | https://github.com/tristanbuckmaster/fluid_lean ; subprojects `euler-blowup/`, `boussinesq-blowup/`, `affinecore/` |
| (b) Status | API: 253 stars, 20 forks, 1 open issue, **not archived**, created 2026‑09‑08, `pushed_at` 2026‑09‑08, language Lean, **no license field**. Root has **no** `README.md` and **no** `lean-toolchain` (both raw-fetch 404). |
| (c) Toolchain | `euler-blowup/lean-toolchain` = `leanprover/lean4:v4.32.2`; `boussinesq-blowup/lean-toolchain` = `leanprover/lean4:v4.32.2`. Mathlib pinned to commit `81a5d257c8e410db227a6665ed08f64fea08e997` (per README). |
| (d) `euler-blowup` verified source | raw `euler-blowup/Challenge.lean`, namespace `EulerBlowup`: structures `SmoothForce`, `ClassicalEuler`, `InLipschitzClass3`; defs `e3`, `pd3`, `pdt3`, `div3`, `advect3`, `curl3`; theorem **`euler_smooth_force_blowup`** (whose proof is `sorry` **by design** — it is the trusted statement file). Modules per README: `EulerBlowup/`, `EulerBlowup/Num/`, `vendor/cm24-r2/`, `Solution.lean`, `comparator.json`, `scripts/PrintAxioms.lean`. |
| (e) Status | README + raw `formalization.yaml` claim a complete proof: `sorry_count: 0` (Challenge.lean's placeholder excluded), axioms `[propext, Classical.choice, Quot.sound]`, `review.status: author-verified` (Levent Alpöge), automation: all Lean written by Claude under Alpöge's direction. **I did not fetch the proof files, build, or run comparator** — claim only. |

`boussinesq-blowup` (raw README, HTTP 200): same structure; planar inviscid Boussinesq finite-time blow-up; library theorem named `BoussinesqBlowup.Num.Cert.theorem01`; toolchain v4.32.2; claims ~1,500 modules and standard-3 axioms. Challenge.lean itself not fetched.

### 2.3 `google-deepmind/formal-conjectures` — `FormalConjectures/Millenium/NavierStokes.lean`

| Field | Value |
|---|---|
| (a) URL | https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Millenium/NavierStokes.lean (path verified via API listing of `FormalConjectures/Millenium`; raw fetch HTTP 200) |
| (b) Status | API: 1258 stars, 475 forks, 1482 open issues, **not archived**, `pushed_at` 2026‑09‑11, Apache‑2.0 |
| (c) Toolchain | raw `lean-toolchain` = `leanprover/lean4:v4.33.1` |
| (d) Exact declarations (from raw source) | defs `divergence` (+ notation `∇⬝`), `IsOnePeriodic`; structures `InitialVelocityCondition`, `InitialVelocityConditionDecay`, `InitialVelocityConditionPeriodic`, `ForceCondition`, `ForceConditionDecay`, `ForceConditionPeriodic`, `NavierStokesExistenceAndSmoothness`, `NavierStokesExistenceAndSmoothnessRn`, `NavierStokesExistenceAndSmoothnessPeriodic`; theorems `navier_stokes_existence_and_smoothness_R3`, `navier_stokes_existence_and_smoothness_periodic`, `navier_stokes_breakdown_R3`, `navier_stokes_breakdown_periodic` |
| (e) Status | **Statement-only**: all four theorems end in `sorry`. The two breakdown theorems are additionally tagged `@[category research solved, AMS 35, formal_proof using lean4 at "https://github.com/openai/NavierStokesAndEuler/commit/8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538"]`. The file's own prose says the September 2026 breakdown results were proved by an internal OpenAI model and cites the OpenAI repo. Nothing is proved in this repo. |

### 2.4 For context only (explicitly excluded from scope)

`openai/NavierStokesAndEuler` (https://github.com/openai/NavierStokesAndEuler, API: 1780 stars, 177 forks, 0 open issues — issues disabled, not archived, created 2026‑09‑08, `pushed_at` 2026‑09‑10, Apache‑2.0) is the repo referenced by 2.3 and is the workspace repo; not surveyed here per instructions.

### 2.5 Euler — result

Besides `fluid_lean/euler-blowup` above, **no other standalone Lean 4 Euler-equation formalization repo was found**. The mathlib Zulip thread in Area 4 shows the topic was discussed in Feb 2025 and judged premature at the time.

### 2.6 Ruled out (not formalizations)

- `rjwalters/lean-genius` (API: 6 stars, 82 open issues, no license, "Annotations for Lean Proofs") has issue #227 "Complete Navier-Stokes Formalization" — this is an annotation/tracker repo, **not** a formalization library.
- `callensxavier/leanflow-dualscale-pde` (Hugging Face) is tagged `navier-stokes`/`lean4` but is a **Rust** model artifact with a "Lean audit", not a Lean library.

---

## Area 3 — Lean 4 libraries aimed at PDE / analysis beyond mathlib

### 3.1 `scottnarmstrong/DeGiorgi` — elliptic regularity (De Giorgi–Nash–Moser)

| Field | Value |
|---|---|
| (a) URL | https://github.com/scottnarmstrong/DeGiorgi |
| (b) Status | API: 39 stars, 7 forks, 0 open issues, **not archived**, created 2026‑04‑07, `pushed_at` 2026‑04‑08, Apache‑2.0 |
| (c) Toolchain | raw `lean-toolchain` = `leanprover/lean4:v4.29.0-rc6` |
| (d) Declarations verified | raw `manifest.json` target theorems: `linfty_subsolution_DeGiorgi_normalized`, `weak_harnack`, `weak_harnack_on_ball`, `harnack`, `harnack_of_homogeneousWeakSolution`, `holder_Moser`, `holder_Moser_of_homogeneousWeakSolution`; files `DeGiorgi/DeGiorgiIteration.lean`, `DeGiorgi/WeakHarnack.lean`, `DeGiorgi/ScaledBallEstimates.lean`, `DeGiorgi/Harnack.lean`, `DeGiorgi/Holder.lean`. Root import `DeGiorgi.lean` → `DeGiorgi.DeGiorgiTheory` (both raw-fetched). |
| (e) Status | README claims fully formalized, sorry-free, axiom-free beyond Lean+Mathlib, ~56,000 lines, dimension d ≥ 3, "first proof-assistant formalization of Sobolev spaces built from weak derivatives at this level of generality". I verified the root imports and manifest only; did **not** verify absence of `sorry` in the proof files. Paper: arXiv:2604.05984. |

### 3.2 `Brsanch/sqg-lean-proofs` (+ `sqg-lean-proofs-fourier`) — harmonic analysis on 𝕋²

| Field | Value |
|---|---|
| (a) URL | https://github.com/Brsanch/sqg-lean-proofs ; companion https://github.com/Brsanch/sqg-lean-proofs-fourier |
| (b) Status | Main API: 0 stars, 0 forks, 0 open issues, **not archived**, created 2026‑04‑14, `pushed_at` 2026‑07‑05, MIT. Companion API: 0 stars, created 2026‑04‑22, `pushed_at` 2026‑07‑05, MIT. Zenodo DOI 10.5281/zenodo.19737766 (v0.6.3). |
| (c) Toolchain | raw main `lean-toolchain` = `leanprover/lean4:v4.29.0` (README: pins mathlib v4.29.0) |
| (d) Declarations verified in raw `SqgIdentity/Basic.lean` (namespace `SqgIdentity`) | `one_sub_cos_two_mul`, `half_times_one_sub_cos`, `sqg_shear_vorticity_identity`, `sqg_shear_vorticity_identity_halfangle`, `sqg_shear_aligned`, `sqg_shear_perpendicular`, `sqg_selection_rule_bound`, `sqg_shear_vorticity_norm`, `sqg_selection_rule_saturated_iff`, the Cartesian variants (`..._cartesian`), `pointwise_bound_to_ell2`, `sqg_selection_rule_ell2`, structure `SqgFourierData` with `w`, `w_norm_le`, `ell2_bound`, and `sqg_L2_torus_bound` (Parseval bridge). README additionally names `SqgIdentity/RieszTorus.lean` (torus Riesz transforms, Leray–Helmholtz projection, fractional Sobolev scale, Biot–Savart factorisation, **α-fractional heat semigroup** and **classical heat semigroup** with smoothing/contractivity bounds) and `SqgIdentity/FourierBridge.lean` (`fourier_rellich_kondrachov`). Companion package description (API): "classical Fourier analysis … Littlewood–Paley, paraproducts, Kato–Ponce commutator, Sobolev embeddings for 𝕋²". |
| (e) Status | `Basic.lean` theorems are **proved** (no `sorry`). Crucially, the raw README **withdraws** the conditional SQG regularity chain as **circular/invalid** and states the named hypotheses `HasStrainLowerBound`/`HasBoundaryCurvatureBound`/`HasThermostatBound` are logically vacuous. So this is real harmonic-analysis infrastructure + two algebraic theorems, **not** an SQG regularity proof. |

### 3.3 `Alektronnik/M4TH` — conservation laws, Burgers blow-up, KdV

| Field | Value |
|---|---|
| (a) URL | https://github.com/Alektronnik/M4TH ; Zenodo DOI 10.5281/zenodo.21716603 (v5.0.0) |
| (b) Status | API: 2 stars, 0 forks, 0 open issues, **not archived**, created 2026‑07‑28, `pushed_at` 2026‑07‑30, Apache‑2.0 |
| (c) Toolchain | raw `lean-toolchain` = `leanprover/lean4:v4.31.0`; root `lakefile.toml` + per-package `lakefile.toml` (e.g. `ConservationLaws/lakefile.toml`) exist |
| (d) PDE content verified | PDE packages: `ConservationLaws/`, `BurgersBlowUp/`, `KdV/`. Raw `ConservationLaws/ConservationLaws.lean` imports `ConservationLaws.TestFunction`, `.Galilean`, `.WeakSolution`, `.ShockProfile`, `.ShockReduction`, `.Burgers`; its docstring states weak (distributional) solutions of `∂ₜu + ∂ₓ(f(u)) = 0`, travelling shock profiles, Rankine–Hugoniot, Lax/Oleinik entropy for Burgers. Names appearing in its own comments/figure text: `shockProfile`, `weakResidual`, `RankineHugoniot`, `HasShockIntegralReduction`, `LaxEntropyCondition` (the actual declarations live in the imported submodules, which I did not fetch). |
| (e) Status | Zenodo description claims "Zero axioms, zero sorry" and axiom certificate `[propext, Classical.choice, Quot.sound]`. **I verified only the package import file and root metadata**, not the submodule proofs. |

### 3.4 `fpvandoorn/BonnAnalysis` — collaborative analysis seminar (distributions)

| Field | Value |
|---|---|
| (a) URL | https://github.com/fpvandoorn/BonnAnalysis |
| (b) Status | GitHub API not fetched (rate-limited); README fetched |
| (c) Toolchain | raw `lean-toolchain` = `leanprover/lean4:v4.10.0-rc1` (old) |
| (d) | README describes it as a Bonn SuSe 24 seminar ("Collaborative Analysis Formalisation"), blueprint at florisvandoorn.com/BonnAnalysis/blueprint. The mathlib Zulip thread (Area 4) links `BonnAnalysis/Distributions` as partial distribution theory work by a student of Floris van Doorn. |
| (e) Status | Explicitly accepts PRs "with a lot of sorry's, as long as it builds" — i.e. **not** a finished proved library. I did not fetch Lean sources. |

### 3.5 `weiran-sun/pde` — heat equation + Sobolev scaffolding (also relevant to Area 4)

| Field | Value |
|---|---|
| (a) URL | https://github.com/weiran-sun/pde ; Reservoir https://reservoir.lean-lang.org/@weiran-sun/PDE |
| (b) Status | API: 8 stars, 1 fork, 1 open issue, **not archived**, created 2025‑12‑22, `pushed_at` 2026‑08‑20, Apache‑2.0 |
| (c) Toolchain | raw `lean-toolchain` = `leanprover/lean4:v4.30.0` |
| (d) Declarations verified | raw `PDE.lean` imports `PDE.Basics.Heat.HeatKernel`, `.HeatSolution`, `.HeatSolutionProperty`, `.HeatMaximumPrinciple`, `PDE.SobolevSpace.Lp_function_spaces`, `PDE.SobolevSpace.weak_derivative`. Raw `PDE/Basics/Heat/HeatKernel.lean` (namespace `Heat`): defs `heatKernel`, `heatK`, `a`, `c`; lemmas `heatK_pos`, `a_pos`, `c_pos`, `heatKernel_pos`, `integral_heatKernel_one_gaussian`; theorems `hasDerivAt_heatKernel_t`, `..._x`, `..._xx`, **`heatKernel_solves_heat_eq`**. |
| (e) Status | `HeatKernel.lean` is proved (no `sorry` in the fetched file). README warns of possible incompatibility with the latest Lean/mathlib and that it may not be compile-optimised. |

### 3.6 Community: "Lean for PDEs" workshop (ICARM & SLMath)

- (a) https://icarm.io/events/2025/slmath-and-icarm-joint-workshop/ and https://www.slmath.org/workshops/1180 (both fetched; ICARM page HTTP 200).
- (b) Past event, **October 6–9, 2025**, SLMath, Berkeley. Organizers: Jeremy Avigad (ICARM/CMU), Matthew Ballard (ICARM), Tatiana Toro (SLMath/UW), Rémy Degenne (Inria Lille), Michael Rothgang (Bonn).
- (d)/(e) Not a repo. Stated goal: "help you start tangible projects that will contribute to the **PDE section of the Mathlib library**". This is the main community vehicle for PDE-in-mathlib work.

### 3.7 Lean FRO

`https://lean-lang.org/fro/about/` was fetched but the page body came back truncated (nav/header only); I found **no PDE-specific Lean FRO project** to report. Treat as "not verified", not "does not exist".

---

## Area 4 — mathlib4 PRs/issues on Sobolev/PDE, and heat equation/semigroup formalizations

### 4.1 mathlib4 PR #36754 — Sobolev distributions (MERGED)

- URL: https://github.com/leanprover-community/mathlib4/pull/36754
- Title as rendered (fetched): "**[Merged by Bors]** feat(Analysis/Distribution): Sobolev distributions by **mcdoll**". This is the PR that landed `Mathlib/Analysis/Distribution/Sobolev.lean` (and, via follow-ups, `BesselPotentialSpace.lean`).
- I did not fetch the diff/comment thread, only the rendered PR page title.

### 4.2 mathlib4 issue search — NOT ACCESSIBLE

`https://github.com/leanprover-community/mathlib4/issues?q=Sobolev` was fetched, but GitHub returned only its navigation/app shell (no issue list). `api.github.com/search/issues` was not usable (rate limit / auth). So I **cannot** give a verified list of Sobolev/PDE issues.

### 4.3 Lean Zulip — "Formalizing some fluid PDE theory." (Feb 2025)

- URL: https://leanprover-community.github.io/archive/stream/287929-mathlib4/topic/Formalizing.20some.20fluid.20PDE.20theory.2E.html (fetched HTTP 200; primary archive).
- Fan Zheng asks about formalizing local/global well-posedness or blow-up of the **Euler equation**. **Terence Tao** replies (verbatim): *"My understanding is that even the Sobolev embedding theorem has not been formalized yet in Lean, so I would say that this is premature."* Patrick Massot links the ITP 2024 paper by **Floris van Doorn and Heather Macbeth** (the Gagliardo–Nirenberg–Sobolev formalization, i.e. `SobolevInequality.lean`). Michael Rothgang says Sobolev embedding is "on my medium-term list"; Anatole Dedecker mentions formalizing distributions. Rothgang links `https://github.com/fpvandoorn/BonnAnalysis/tree/master/BonnAnalysis/Distributions`. Tao notes Bertozzi–Majda §§4.1/4.2/4.5 "might be possible … with current tools".
- Historical value: as of Feb 2025 there was no Sobolev embedding in mathlib; by the 2026 fetches above, GNS + Bessel-potential Sobolev spaces **do** exist.

### 4.4 Lean Zulip — "Tychonov's Counterexample for the Heat Equation" (Oct 2025) — heat equation lead

- URL: https://leanprover-community.github.io/archive/stream/287929-mathlib4/topic/Tychonov's.20Counterexample.20for.20the.20Heat.20Equation.html (fetched HTTP 200).
- Yongxi Lin (Aaron), Oct 27 2025: "As an attempt to use Lean for PDEs, I have almost formalized that these counterexamples are solutions to the heat equation", at a **mathlib4 fork branch**: `https://github.com/CoolRmal/mathlib4/blob/c68bf629c0c3a2e5c5989b39d9bb6ca4e73667d8/Mathlib/tychonov_counterexample.lean`. He lists **remaining sorries** (local uniform convergence of tail series; a `contDiff_tsum` analogue). Michael Rothgang offers to review a PR. **Not merged, incomplete** (branch/fork, not a repo I verified).

### 4.5 Heat equation / heat semigroup — what exists

| Project | What | Status |
|---|---|---|
| mathlib4 | no heat kernel/semigroup module found | absent (see Area 1 caveat) |
| `weiran-sun/pde` | 1-D `heatKernel`, `heatKernel_solves_heat_eq`, normalisation — source verified | proved |
| `Brsanch/sqg-lean-proofs` | α-fractional + classical heat **semigroup** on 𝕋ᵈ with smoothing/contractivity (in `SqgIdentity/RieszTorus.lean`, per README) | claimed proved (source file not fetched) |
| `CoolRmal/mathlib4` branch | Tychonov heat-equation counterexample | incomplete, with sorries |

---

## Confidence / access limitations

**Successfully fetched (HTTP 200, primary source):**

- raw.githubusercontent.com (mathlib4 `master`): `Mathlib/Analysis/Distribution/Sobolev.lean`; `Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean`; `Mathlib/Analysis/FunctionalSpaces/BesselPotentialSpace.lean`; `Mathlib/Analysis/SpecialFunctions/Bernstein.lean`; `Mathlib/Analysis/InnerProductSpace/Laplacian.lean`.
- api.github.com (mathlib4 contents): `Mathlib/Analysis/Distribution`; `.../Fourier`; `.../FunctionalSpaces`; `.../SpecialFunctions`; `.../SpecialFunctions/Gaussian`; `.../Distribution/SchwartzSpace`; `Mathlib/MeasureTheory/Group`. `Mathlib/Analysis/PDE` → **404**.
- api.github.com repo metadata: `weiran-sun/pde`, `scottnarmstrong/DeGiorgi`, `rjwalters/lean-genius`, `leanprover-community/mathlib4`, `openai/NavierStokesAndEuler`, `uda-lab/leray-hopf`, `Brsanch/sqg-lean-proofs`, `Brsanch/sqg-lean-proofs-fourier`, `Alektronnik/M4TH`, `google-deepmind/formal-conjectures`, `tristanbuckmaster/fluid_lean`.
- raw source/toolchains: `google-deepmind/formal-conjectures` `FormalConjectures/Millenium/NavierStokes.lean` + `lean-toolchain`; `uda-lab/leray-hopf` `lean-toolchain` + `LerayHopf/Torus/GalerkinODECapstone.lean`; `weiran-sun/pde` `PDE.lean` + `PDE/Basics/Heat/HeatKernel.lean` + `lean-toolchain`; `scottnarmstrong/DeGiorgi` `lean-toolchain`, `README.md`, `DeGiorgi.lean`, `DeGiorgi/DeGiorgiTheory.lean`, `manifest.json`; `Alektronnik/M4TH` `lean-toolchain`, `ConservationLaws/ConservationLaws.lean`; `tristanbuckmaster/fluid_lean` `euler-blowup/{lean-toolchain,README.md,Challenge.lean,formalization.yaml}` and `boussinesq-blowup/{lean-toolchain,README.md}`; `Brsanch/sqg-lean-proofs` `lean-toolchain`, `README.md`, `SqgIdentity/Basic.lean`; `fpvandoorn/BonnAnalysis` `README.md`, `lean-toolchain`.
- HTML/other: Reservoir `@uda-lab/lerayHopf`; Zenodo records `21716603` (M4TH) and `19737766` (SQG); ICARM workshop page; two Lean Zulip archive topics; mathlib4 PR #36754 page; `lean-lang.org/fro/about/` (truncated).

**Could NOT access / not done (explicit):**

1. **GitHub code search is login-gated.** `https://github.com/search?q=repo%3Aleanprover-community%2Fmathlib4+heatKernel&type=code` returned GitHub's sign-in shell; `api.github.com/search/code` needs a token. Therefore the "no Besov / no Littlewood–Paley / no heat kernel in mathlib" conclusions are **not** exhaustive code-search results.
2. **GitHub issue search** (`mathlib4/issues?q=Sobolev`) returned only the app shell; no verified issue list.
3. **GitHub API rate limit hit** mid-session (HTTP 403) after the listed repo-metadata calls. Consequences: no commit histories/date-of-last-commit for `fluid_lean`, no contents listing of `fluid_lean/euler-blowup` or `boussinesq-blowup` (used raw file fetches instead), no API metadata for `BonnAnalysis`.
4. **Not built/compiled, no `#print axioms` run.** All "sorry-free / kernel-only / standard-3-axioms" statements for `leray-hopf`, `DeGiorgi`, `fluid_lean`, `M4TH`, `sqg` are the **projects' own README/formalization.yaml claims**, corroborated only where I read the actual source (e.g. `SqgIdentity/Basic.lean` has no `sorry`; `HeatKernel.lean` has no `sorry`; `leray-hopf` capstone file has no `sorry`).
5. **Proof files not fetched** for: `DeGiorgi/DeGiorgiIteration|WeakHarnack|ScaledBallEstimates|Harnack|Holder`, `leray-hopf` R3/global capstones and all non-capstone modules, `fluid_lean` `Solution.lean` + `EulerBlowup/` + `vendor/`, `M4TH` `ConservationLaws/{TestFunction,Galilean,WeakSolution,ShockProfile,ShockReduction,Burgers}`, `sqg` `RieszTorus.lean`/`FourierBridge.lean`, and the whole `sqg-lean-proofs-fourier` repo. Exact declaration names for those are **not** reported (except where a README/manifest itself names them, which I mark as such).
6. **`uda-lab/lerayHopf` is an invalid GitHub path (404)**; the working repo is `uda-lab/leray-hopf`. The Reservoir display slug uses `lerayHopf`.
7. `lean-lang.org/fro/about/` returned truncated text; **no Lean FRO PDE project verified** either way.

**Nothing in this report is invented**: every module path, declaration, toolchain string and URL above comes from a fetch named in the text; items I could not fetch are called out rather than filled in.
