# Lean 4 prior art for PDE / fluid dynamics / harmonic analysis

Survey date: 2026 (workspace checkout of `openai/NavierStokesAndEuler`).
Purpose: prevent a Navier–Stokes criticality project from re-formalizing what already exists.

**Method / honesty note.** Everything below is either (i) read directly from the local
checkout of `openai/NavierStokesAndEuler` (which *is* a git clone of the GitHub repo),
or (ii) fetched from `raw.githubusercontent.com` / Zenodo / project docs for the external
repos. I did **not** run `lake build` anywhere, so "proved" means: no `sorry`/`axiom` in
source, and (where the project or its `#print axioms` lines state it) kernel-only axiom
sets. External projects' self-reported status is attributed to them. Where I could not
reach source, I say so.

---

## 1. The repo `openai/NavierStokesAndEuler`

**(a) URL:** https://github.com/openai/NavierStokesAndEuler

**(b) Maintenance / versions.**
- Published `origin/main` HEAD = `8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538`, dated **2026-09-08**.
- `lean-toolchain`: `leanprover/lean4:v4.34.0-rc2`.
- `lakefile.toml` requires `mathlib` and `leanprover/comparator`, both at rev `v4.34.0-rc2`.
- Size: 643 `.lean` under `NavierStokes/`, 1839 under `Euler/` (≈ **615,802 lines** total).
- The local checkout is on branch **`skeleton-criticality`**, 4 commits ahead of
  `origin/main` and **not pushed** (origin has only `main`). That branch *adds* `Criticality/`
  — see §1.4. Do not mistake it for published upstream content.

**(c) Exact declarations.**

The PDE itself (unit-torus / periodic formulation, viscosity fixed at 1) —
`NavierStokes/ProblemStatement.lean`, namespace `NavierStokes.ProblemStatement`:
- `abbrev Space := EuclideanSpace ℝ (Fin 3)`, `abbrev SpaceTime := ℝ × Space`,
  `VelocityField`, `PressureField`.
- `coordinateVector`, `preSingularDomain`, `futureDomain`, `UnitSpatialPeriodsOn`.
- `temporalDerivative`, `spatialDerivative`, `advection`, `spatialDivergence`,
  `pressureGradient`, `spatialLaplacian`.
- `navierStokesResidual` (the PDE residual), plus `CandidateProperties`,
  `candidateStatement` (the target Prop), `SpeedUnboundedAtOne`.

The whole-space ℝ³ formulation with arbitrary viscosity ν —
`NavierStokes/R3/ProblemStatement.lean`, namespace `NavierStokesR3.ProblemStatement`:
- `navierStokesResidual` (ν multiplies only the Laplacian), `positiveTimeDomain`,
  `CompactPositiveTimeSupport`, `SquareIntegrableAtTime`, `kineticEnergy`,
  `UniformFiniteEnergy`.
- structures `CandidateProperties`, `Candidate`, `GlobalFiniteEnergySolution`;
  Propositions `candidateStatement`, `coreBreakdownStatement`, `breakdownStatement`.

Main theorems (proved):
- `NavierStokes.Comparator.navier_stokes_breakdown_R3` and
  `NavierStokes.Comparator.navier_stokes_breakdown_periodic` — `NavierStokes/ComparatorSolution.lean`
  (adapters over `NavierStokes/ComparatorR3Theorem.lean` / `ComparatorTheorem.lean`).
- `Euler.euler_breakdown_R3`, `Euler.exists_compact_smooth_euler_singularity` — `Euler/Solution.lean`.
- Candidate existence (the real work behind (C)/(D)):
  `NavierStokes.ActualCandidateAssembly.selected_candidate : ProblemStatement.candidateStatement`
  and `NavierStokes.R3CompactCandidate.selected_compact_candidate`;
  `NavierStokes/ComparatorR3Theorem.option_C_of_compact_candidate`,
  `NavierStokes/ComparatorTheorem.option_D_of_candidate`.
- Euler equation statement: `Euler.EulerExistenceAndSmoothness.euler` field (unforced incompressible
  Euler) in `Euler/SolutionDefinitions.lean`; `Euler.EulerExistenceAndSmoothnessR3`,
  `Euler.EulerSobolevExistenceAndSmoothnessR3On`, `Euler.SobolevSmoothOn`,
  `Euler.InitialVelocityConditionDecay`, `Euler.vorticity`, `Euler.velocityC1Norm`,
  `Euler.vorticityNorm`.

Energy estimates (genuine, PDE-level) — `NavierStokes/R3/CompactEnergy.lean`:
`l2Sq`, `energyRate`, `dissipation`, `dissipation_nonneg`, `energy_balance`,
`energy_rate_le`, `energy_hasDerivAt`, `hasDerivAt_energy_balance`,
`integral_laplacian_energy`, `integral_transport_energy_zero`, `integral_pressure_energy_zero`.
Weighted/difference energy — `NavierStokes/R3/LocalizedDifferenceEnergy.lean`:
`weightedEnergy_hasDerivAt`, `difference_energy_balance`, `hasDerivAt_difference_energy_balance`.
Gronwall — `NavierStokes/R3/ScalarEnergyBound.lean`: `forced_gronwall`,
`forced_gronwall_weighted`, `forced_gronwall_uniform`; and `NavierStokes/R3/ComparisonGronwall.lean`.

Sobolev / embeddings (bespoke, not mathlib's):
- Torus Sobolev scale built from closed graphs of strong L² derivatives:
  `EulerCylinderSobolevSpace.SobolevSpace`, `SobolevWord`, `SobolevEdge`, `sobolevSubspace`,
  `word_hasDerivAt`, `ofJet`, `toJet`, `value_injective` — `Euler/CylinderSobolevSpace.lean`.
- ℝ³ weighted Sobolev / Sobolev inequalities: `WeightedSobolev.sobolevConstant`,
  `weightedSobolevConstant`, `weighted_sobolev`, `cutoffL6_le`;
  `SmoothSobolevL6.smooth_eLpNorm_six_le`, `smooth_memLp_six`;
  `Euler/OrdinarySobolevL4.lean` (L⁴/L⁶ interpolation: `eLpNorm_six_le`, `memLp_six`, `memLp_four`, …).
- Embedding: `EulerCylinderSobolevEmbedding.sobolevEmbeddingConstant`, `value_ae_bound`.
- It *imports* mathlib's own Sobolev modules:
  `Mathlib.Analysis.Distribution.Sobolev`, `Mathlib.Analysis.FunctionalSpaces.SobolevInequality`.

Heat kernel / heat semigroup:
- ℝ³ kernel: `heatKernel`, `heatKernelSecond`, `heatKernel_pos`, `norm_heatKernelSecond_le`
  — `NavierStokes/R3/HeatKernel.lean`; `heatSecondSymbol`, `heatSecondTest`,
  `rieszTest_eq_integral_heatSecondTest` — `NavierStokes/R3/RieszHeatRepresentation.lean`.
- Torus semigroup on the Sobolev scale: `EulerSobolevHeat.heatOperator`,
  `heatOperator_semigroup`, `heatOperator_bound`, `heatGain`, `heatGain_semigroup`;
  `EulerGaussianHeatTotal.heatList`, `heatList_semigroup`, `heatListOperator`, `cylinderHeat`;
  `EulerCylinderHeatEquation.realHeatList_strongDerivative`, `realHeatList_generator_pos`;
  divergence-free preservation `DivergenceFreeHeat.heatGain_preserves_gradient_zero`.
- Maximal regularity: `EulerHeatMaximalRegularity.viscous_mild_maximal_regularity`,
  `viscous_mild_ae_H2`, `exists_regularized_mild_limit`.

Scaling arguments:
- Viscosity/time rescaling: `NavierStokes.ComparatorBridge.rescale`, `rescaledForce`
  (`f_ν = ν² • f(ν·t, ·)`), with `rescale_smooth/_periodic/_support`,
  `rescale_spatialDerivative/_divergence/_advection/_gradient/_laplacian/_temporalDerivative`
  — `NavierStokes/ComparatorBridge.lean`.
- Also `Euler/ParameterSobolevScaling.lean`, `dilateField`, `dilation`.

**(d) Proved or stubbed.**
- `grep` over `NavierStokes/` + `Euler/`: **0 `sorry`, 0 `axiom`**.
- The only 5 `sorry`s in the whole repo are intentional Comparator *challenge* placeholders in
  `ComparatorChallenges/NavierStokes.lean` and `ComparatorChallenges/Euler.lean`.
- `formalization.yaml` declares `status.sorry_count: 0` and lists the four main results with
  axioms `[propext, Classical.choice, Quot.sound]`, `review.status: "self-assessed"`.
- Missing entirely (case-insensitive, whole repo): **Besov (0), Littlewood (0), Paley (0),
  Bernstein (0)**.

### 1.4 Local-only `skeleton-criticality` branch (NOT upstream)

Branch `skeleton-criticality`, HEAD `72def14` (2026-09-12), unpushed. Adds `Criticality/`.
Real declarations (each appears in a `#print axioms` line; no `sorry`):

| File | Declarations |
|---|---|
| `Criticality/ConcentrationBarrier.lean` | `fourierInv_apply_le_toLp_one`, `pointwise_le_L1_fourier` |
| `Criticality/Bernstein.lean` | `norm_toLp_one_le_sqrt_measure_mul_norm_toLp_two`, `bernstein` |
| `Criticality/BernsteinGrowth.lean` | `sqrt_volume_ball_eq_sqrt_volume_unitBall_mul`, `bernstein_L2_to_Linf`, `abs_inner_mul_norm_le`, `norm_toLp_one_fourier_lineDeriv_le`, `bernstein_lineDeriv`, `bernstein_gradient` |
| `Criticality/Heisenberg.lean` | `commutator_integral`, `norm_toLp_two_sq_eq_integral_sq`, `heisenberg_commutator_real` |
| `Criticality/Dyadic.lean` | `dyadicOctave`, `dyadicOctave_disjoint`, `dyadicOctave_shift` |
| `Criticality/ConvolutionCoupling.lean` | `fourier_convolution_eq_pairing`, `fourier_mul_eq_convolution`, `fourier_mul_apply_eq_integral` |
| `Criticality/ScalingCriticality.lean` | `integral_norm_comp_smul`, `integral_norm_comp_smul_of_nonneg`, `scaling_exponent_eq_zero_iff`, `energy_critical_in_dim_two`, `energy_subcritical_of_ge_three`, `ns_scaling_homogeneous_degree` |
| `Criticality/ShellModel.lean` | `shellRHS`, `shell_energy_identity`, `transfer_le_dissipation` |
| `Criticality/EulerProduct.lean` | `eulerProduct_hasProd`, `eulerProduct_tprod`, `eulerProduct` |

**Still NOT proved** (documented targets inside doc-comments; `heisenberg_variance` at
`Criticality/Heisenberg.lean:267` is *inside* a `/-! … -/` comment block and must not be
mistaken for a theorem):
- full Heisenberg variance form `Δx·Δξ ≥ d/(4π)`;
- full smooth Littlewood–Paley decomposition `f = Σₖ 𝓕⁻(φₖ·𝓕f)` (only the dyadic *partition*
  `dyadicOctave` is done — no smooth cutoffs / partition of unity);
- full PDE-level scaling invariance (`ns_scaling_homogeneous_degree` is exponent bookkeeping only);
- forced shell blowup (D3).

---

## 2. Other Lean 4 formalizations of NS / Euler / heat / harmonic analysis / PDE

### 2.1 `google-deepmind/formal-conjectures` — NavierStokes (statement-only)
- URL: https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Millenium/NavierStokes.lean
- Verified by fetching the raw file. Contains definitions `divergence`, `IsOnePeriodic`,
  `InitialVelocityCondition`, `InitialVelocityConditionDecay`, `InitialVelocityConditionPeriodic`,
  `ForceCondition`, `ForceConditionDecay`, `ForceConditionPeriodic`,
  `NavierStokesExistenceAndSmoothness`, `…Rn`, `…Periodic`.
- Four theorem **statements**, all `by sorry`:
  `navier_stokes_existence_and_smoothness_R3` (A), `…_periodic` (B),
  `navier_stokes_breakdown_R3` (C), `navier_stokes_breakdown_periodic` (D).
- (C)/(D) are tagged `@[category research solved, formal_proof using lean4 at
  "https://github.com/openai/NavierStokesAndEuler/commit/8937a8f…"]` — i.e. the *proof lives in
  the OpenAI repo*, not here. This is the independent reference the OpenAI repo's
  `ComparatorChallenges/` checks against.

### 2.2 `uda-lab/leray-hopf` — Leray–Hopf weak existence (the strongest general infrastructure)
- URL: https://github.com/uda-lab/leray-hopf (Reservoir: https://reservoir.lean-lang.org/@uda-lab/lerayHopf)
- `lean-toolchain`: `leanprover/lean4:v4.31.0-rc2`; mathlib required at `rev = "master"`
  (pinned in `lake-manifest.json`). Repo metadata: Apache-2.0, Copyright 2026 Tomoki Uda.
- **Capstones** (README + fetched `LerayHopf/Torus/GalerkinODECapstone.lean`):
  `exists_lerayHopf_torus3` (`LerayHopf/Torus/GalerkinODECapstone.lean`),
  `exists_lerayHopf_r3` (`LerayHopf/R3/GalerkinODECapstone.lean`),
  and global-in-time `exists_global_lerayHopf_torus3`, `exists_global_lerayHopf_r3`
  (plus structure form `exists_globalLerayHopfSolutionFull_torus3` / `…_r3`).
  Solution contract: `LerayHopfSolutionFull`, `LerayHopfSolutionFull_R3`,
  `Galerkin.IsLerayHopfOn`; generic bundles `Galerkin.SolutionData`,
  `Galerkin.CompactnessPackage`, `Galerkin.LerayHopfSolution`.
- **Reusable generic layers** (from `docs/architecture.md`; 113 files total):
  - `LerayHopf/Analysis/`: `TensorEdgeGluing.lean`, `PlancherelKernels.lean`,
    `BilinearExtension.lean`, `TensorIntersection.lean`, `RealComplexLpBridge.lean`,
    `SpectralWeakGradient.lean`, `LpInterpolation.lean`, `WeakLeibniz.lean`,
    `FourierParseval.lean`, `BoundedMultiplier.lean`.
  - `LerayHopf/Bochner/`: `GelfandTriple.lean`, `TimeSobolev.lean` (`IsWeakTimeDeriv`, `W1pTime`),
    `DiagonalExtraction.lean`, `WeakLimitToolkit.lean`, plus experimental time-mollification files.
  - `LerayHopf/Galerkin/`: `DissipativeODE.lean`, `QuadraticField.lean`, `Domain.lean`,
    `SolutionBundles.lean`, `GlobalContract.lean`.
  - `LerayHopf/EvolutionTriple.lean` (`DissipativeEvolution`, `WeakFormNS`),
    `LerayHopf/EnergyEstimate.lean` (`AbstractEnergyLaw`).
  - Spatial analysis: `Torus/RellichEmbedding.lean` (`rellich_L2Sigma`, `H1_ball_totallyBounded`,
    Fourier-tail Rellich), `Torus/SobolevTorus.lean` (hand-built H¹(𝕋³)),
    `R3/SobolevEmbedding.lean` (`gns_L6_of_memH1_R3`), `R3/Regularity.lean` (`memH1VF_R3`,
    uses mathlib `MemSobolev`), `R3/FourierL2.lean`, `R3/FrechetKolmogorov.lean`,
    `R3/TrilinearEstimate.lean`, `Torus/Leray.lean` (Leray projection).
- **Status (self-reported + corroborated on one capstone file):** four capstones
  `#print axioms = [propext, Classical.choice, Quot.sound]`, zero project axioms, no `sorryAx`;
  `import LerayHopf` release cone is sorry-free and axiom-free, enforced in CI
  (`scripts/check-release-cone.sh`). Six residual `sorry`s are Lions–Magenes-class Bochner time
  walls, quarantined behind `import LerayHopf.Experimental`. `docs/STATUS.md` records earlier
  false/vacuous statements that were caught and corrected (e.g. `w1pTime_continuous_in_H`).
- **`docs/pdelib-staging.md`**: the project's own inventory for extracting domain-neutral content
  into an external **`pdelib`** PDE-analysis library. It marks `Bochner/TimeSobolev.lean`,
  `Bochner/WeakLimitToolkit.lean`, `EvolutionTriple.lean`, `Galerkin/DissipativeODE.lean`,
  `Galerkin/QuadraticField.lean`, and four `Analysis/*` files **verbatim-ready**.
  No `pdelib` repository itself was found — treat it as *planned, not existing*.

### 2.3 `Brsanch/ns-lean-proofs` — NS Buaria–Lawson–Wilczek gradient chain
- URL: https://github.com/Brsanch/ns-lean-proofs
- `lean-toolchain`: `leanprover/lean4:v4.29.0`. ~130 files / ~18,400 LOC, MIT.
- Conditional regularity: `NSEvolutionAxioms` (`NSBlwChain/Setup/NSHypothesis.lean`),
  `GradBoundHypotheses.gradient_bound` (`BLW/GradientBound.lean`),
  capstone `BLW/ChainHypotheses.proposition_four_of_hypotheses`.
- **Not unconditional.** `NSBlwChain/Setup/ClassicalAxioms.lean` (fetched) declares **three real
  `axiom`s**: `biot_savart_self_strain_bound`, `seregin_type_one_exclusion`,
  `NS_time_analyticity`, wrapped in `BiotSavartSelfStrainBound`, `SereginTypeOneExclusion`,
  `NSTimeAnalyticity`. README claims zero `sorry` in the BLW chain, but the three axioms are by
  design and the README itself notes one axiom absorbs an open sub-problem `(H_C6)`.

### 2.4 `Brsanch/sqg-lean-proofs` + `Brsanch/sqg-lean-proofs-fourier` (harmonic analysis)
- https://github.com/Brsanch/sqg-lean-proofs and https://github.com/Brsanch/sqg-lean-proofs-fourier
- Both `lean-toolchain`: `leanprover/lean4:v4.29.0`; MIT.
- **`sqg-lean-proofs-fourier` (~2800 LOC, CI green)** is the only verified Lean 4 package with
  classical **Littlewood–Paley / Bony paraproduct / Kato–Ponce** content. Modules + verified names:
  - `FourierAnalysis/LittlewoodPaley/Dyadic.lean` — `lpProjector`, `lpPartialSum`,
    dyadic annuli/balls on 𝕋².
  - `FourierAnalysis/LittlewoodPaley/Bernstein.lean` (fetched) — **real Bernstein-type
    inequalities**, exact declarations: `norm_lpPartialSum_le`, `sq_norm_lpPartialSum_le`,
    `norm_lpProjector_le`, `sq_norm_lpProjector_le`, `sq_norm_lpProjector_succ_le`,
    `norm_lpProjector_succ_le`, `sum_shell_sq_mFourierCoeff_le_tsum`,
    `sq_norm_lpProjector_succ_le_tsum`, `norm_lpProjector_succ_le_tsum`
    (shell bound `‖Δ_{N+1}f‖_∞ ≤ 2·2^{N+1}·‖f‖₂`). Its own docstring calls the file the
    "triangle-inequality precursor", so read it before relying on the sharpest constant.
  - `FourierAnalysis/Paraproduct/Defs.lean` — `paraproductPartial`, `remainderPartial`,
    Bony decomposition `f·g = T_f g + T_g f + R`; `Paraproduct/Bounds.lean` — L² Parseval bounds.
  - `FourierAnalysis/KatoPonce/Commutator.lean` — `partialCommutator` with Bony expansion,
    structural + quantitative Ḣˢ-valued + uniform-in-N Kato–Ponce bounds;
    `KatoPonce/SobolevEmbedding.lean` — `Ḣˢ ⊂ L∞` for `s > d/2`.
  - `FourierAnalysis/ArgmaxFromDecay.lean`, `FourierAnalysis/LatticeZeta.lean`
    (`∀ finite A ⊆ ℤᵈ\{0}, ∑ ‖a‖⁻ᵖ ≤ 2·d·3^{d-1}·ζ(p-(d-1))`).
  - Its README explicitly says the package is **"upstream of several PDE projects"** and
    **intended for reuse by future NS / Euler / MHD formalizations**.
- **`sqg-lean-proofs`** itself: `SqgIdentity/Basic.lean` (`sqg_shear_vorticity_identity`,
  `sqg_selection_rule_bound`), `SqgIdentity/RieszTorus.lean` (torus Riesz transforms,
  Leray–Helmholtz, fractional Sobolev scale, α-fractional **and** classical heat semigroup suites),
  `SqgIdentity/FourierBridge.lean` (`fourier_rellich_kondrachov`,
  `countable_diagonal_bounded_sequences` — Rellich–Kondrachov H¹(𝕋²) ⊂⊂ L²).
- **Important caveat (stated by the project):** the "conditional SQG regularity" chain was
  **withdrawn on 2026-05-29 as circular** (its named hypotheses are logically vacuous). Only the
  algebraic identities and the multiplier/heat/Rellich infrastructure are genuine. The current
  README says so prominently; rely on that, not on older/zenodo descriptions claiming a
  conditional regularity theorem.

### 2.5 `scottnarmstrong/DeGiorgi` — De Giorgi–Nash–Moser elliptic regularity
- URL: https://github.com/scottnarmstrong/DeGiorgi
- `lean-toolchain`: `leanprover/lean4:v4.29.0-rc6`; `lakefile.lean` requires mathlib
  `v4.29.0-rc6` and REPL `v4.29.0-rc6`. Apache-2.0. ~56,000 lines. Paper: arXiv:2604.05984
  (Armstrong & Kempe).
- README states **sorry-free and axiom-free beyond Lean and Mathlib**, dimension `d ≥ 3`.
  Headline declarations (from README): `linfty_subsolution_DeGiorgi_normalized`, `weak_harnack`,
  `weak_harnack_on_ball`, `harnack`, `harnack_of_homogeneousWeakSolution`, `holder_Moser`,
  `holder_Moser_of_homogeneousWeakSolution`; root imports `DeGiorgi`, `DeGiorgi.DeGiorgiTheory`.
- Claims to be the first proof-assistant formalization of Sobolev spaces from **weak derivatives**
  at that level of generality. Different PDE class from NS (elliptic, divergence-form) but directly
  relevant analysis infrastructure.

### 2.6 `weiran-sun/pde` — heat equation from Choksi's textbook
- URL: https://github.com/weiran-sun/pde (docs: https://weiran-sun.github.io/pde/)
- `lean-toolchain`: `leanprover/lean4:v4.30.0`.
- Modules `PDE/Basics/Heat/HeatKernel`, `HeatSolution`, `HeatSolutionProperty` — heat kernel,
  convolution solution, and properties. Early-stage; the README itself warns of possible
  incompatibility with current mathlib and that it is not optimized for compilation.
- I did not audit its `sorry`/axiom status file-by-file.

### 2.7 `eric-wieser/navier-stokes-misformalization` — cautionary
- URL: https://github.com/eric-wieser/navier-stokes-misformalization (branch `master`)
- Not a formalization: reproduces a Lean Zulip finding that a particular *mis-stated* NS
  Millennium formalization makes the problem trivial. Useful as a statement-shape warning.

---

## 3. Library-level PDE/analysis infrastructure and the "communities"

### 3.1 mathlib4 itself (inspect the cached source at
`/Users/ronaldrogers/Code/NavierStokesAndEuler/.lake/packages/mathlib`; rev `v4.34.0-rc2`,
commit `85e3a25e…`, 2026-08-21)

Present:
- `Mathlib/Analysis/Distribution/Sobolev.lean` — **Bessel-potential Sobolev spaces**.
  `TemperedDistribution.besselPotential`, `TemperedDistribution.MemSobolev` (definition:
  `∃ f' : Lp F p, besselPotential E F s f = f'`), `memSobolev_zero_iff`,
  `MemSobolev.add/sub/neg/smul/mono`, `MemSobolev.fourierMultiplierCLM_of_bounded`,
  `MemSobolev.lineDerivOp`, `MemSobolev.laplacian`, `SchwartzMap.memSobolev`.
- `Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean` — **Gagliardo–Nirenberg–Sobolev**.
  `eLpNorm_le_eLpNorm_fderiv`, `eLpNorm_le_eLpNorm_fderiv_one`,
  `eLpNorm_le_eLpNorm_fderiv_of_eq`, `eLpNorm_le_eLpNorm_fderiv_of_le`,
  `eLpNormLESNormFDerivOfEqInnerConst`.
- `Mathlib/Analysis/Distribution/FourierMultiplier.lean` — `fourierMultiplierCLM` (Schwartz and
  tempered-distribution), `lineDeriv_eq_fourierMultiplierCLM`, `laplacian_eq_fourierMultiplierCLM`.
- `Mathlib/Analysis/Fourier/*` (FourierTransform, Inversion, LpSpace, PoissonSummation,
  RiemannLebesgueLemma, Convolution, AddCircle, AddCircleMulti); Gaussian:
  `Mathlib/Analysis/SpecialFunctions/Gaussian/{GaussianIntegral,FourierTransform,PoissonSummation}.lean`.

Absent (verified):
- **No heat kernel / heat semigroup** anywhere (a case-insensitive `heat` search only matched
  "t**heat**orem").
- **No Besov, no Littlewood–Paley** (zero hits for `besov|littlewood|paley`).
- **No Rellich–Kondrachov compact embedding** (both leray-hopf and sqg had to build it).
- `Mathlib/Analysis/SpecialFunctions/Bernstein.lean` and `Mathlib/RingTheory/Polynomial/Bernstein.lean`
  are **Bernstein polynomials / Weierstrass approximation** and the Bernstein polynomial basis —
  **not** harmonic-analysis Bernstein inequalities. `Mathlib/SetTheory/Cardinal/SchroederBernstein.lean`
  is unrelated (Cantor–Schröder–Bernstein).

### 3.2 Communities named in the brief
- **"Lean for PDE"** is a *workshop series* (e.g. ICARM & SLMath joint workshop; Univ. of Catania
  "Lean for PDEs" 2025), not a library. No associated Lean PDE package was found.
- **"FormalML"** (`prithvioak/formalML`) is a formalization of **machine-learning** concepts
  (classifiers, loss functions, VC dimension) — **not** PDE/analysis. The brief's association of
  FormalML with PDE appears to be a mislabel.
- **`pdelib`** is named only as a *planned* external PDE-analysis library in leray-hopf's
  `docs/pdelib-staging.md`. No repository or source was found; do not cite it as existing.

---

## 4. Bottom line — what a Navier–Stokes criticality project can reuse

1. **The NS PDE statement, energy method, and scaling are already done** in the workspace itself
   (`openai/NavierStokesAndEuler`): `NavierStokes.ProblemStatement.navierStokesResidual` (+ the ℝ³
   ν-version), `energy_balance`/`energy_rate_le`/`hasDerivAt_energy_balance`,
   `difference_energy_balance`, the `forced_gronwall*` family, and `ComparatorBridge.rescale`
   /`rescaledForce`. Reuse these rather than restating the equation or re-deriving the energy
   identity.
2. **Harmonic-analysis infrastructure specifically wanted for a criticality argument has a real
   home**: `Brsanch/sqg-lean-proofs-fourier` is the only verified Lean 4 package with
   Littlewood–Paley decomposition, Bony paraproducts, Bernstein inequalities, the Sobolev
   embedding `Ḣˢ ⊂ L∞` for `s > d/2`, and uniform-in-N Kato–Ponce commutator bounds — and its
   README states it is intended for NS/Euler/MHD reuse. **Caveat: it is on 𝕋² only, at mathlib
   v4.29.0, ~2800 LOC; porting to the workspace's v4.34.0-rc2 is required.**
   The local `Criticality/` skeleton only has the dyadic *partition* and an ℝᵈ `bernstein`;
   it does **not** have the LP decomposition, smooth partition of unity, Bony paraproducts, or
   Kato–Ponce.
3. **For weak-solution / compactness / Bochner-time machinery**, `uda-lab/leray-hopf` is the
   richest reusable source (Galerkin layer, Aubin–Lions/Bochner `TimeSobolev`, Rellich on 𝕋³,
   Fréchet–Kolmogorov on ℝ³, Leray projection, generic `Analysis/` layer, and a documented
   `pdelib` extraction inventory). **Caveat: mathlib v4.31.0-rc2, not v4.34.0-rc2.**
4. **mathlib already supplies Sobolev space *membership*** (`TemperedDistribution.MemSobolev`,
   Bessel-potential, real `s`) and the **Gagliardo–Nirenberg–Sobolev inequality**
   (`eLpNorm_le_eLpNorm_fderiv*`). Do not re-formalize those. mathlib does **not** supply a heat
   semigroup, Besov spaces, Littlewood–Paley, Bernstein inequalities, or Rellich–Kondrachov.
5. **The exact gap a criticality project would fill**: no existing Lean 4 repo was found that
   combines (i) Littlewood–Paley/Besov on ℝ³, (ii) a heat semigroup with maximal regularity on
   ℝ³, and (iii) NS criticality scaling — although `sqg-lean-proofs-fourier` (LP/Bony/Kato–Ponce
   on 𝕋²), `sqg-lean-proofs` (fractional/classical heat semigroup on 𝕋²), the workspace's own
   `Criticality/` (Bernstein/dyadic/scaling), and `openai/NavierStokesAndEuler`'s ℝ³ heat kernel +
   weighted Sobolev + energy estimates each provide a piece.

### Verification limitations
- No `lake build` was run in any repo. "Proved" = no `sorry`/`axiom` in the files searched, plus
  the project's stated `#print axioms` results.
- Exact declaration names for external repos come from fetched source (SQG-Fourier `Bernstein.lean`,
  leray-hopf `Torus/GalerkinODECapstone.lean`, ns-lean-proofs `Setup/ClassicalAxioms.lean`) or from
  each project's own architecture/README docs (attributed as such).
- GitHub REST API returned HTTP 403 (rate limit), so star counts / last-commit dates for external
  repos could not be pulled via the API; version info comes from `lean-toolchain`/`lakefile`.
