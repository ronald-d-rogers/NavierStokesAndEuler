# Progress: dyadic cascade models

Where we are now. The *target* is `PLAN.md`; the *why* is `VISION.md`.

> **Snapshot:** branch `dyadic-cascade`. Stages **S**, **R**, **A**, **O**, and **O′** are done;
> only **B** (forced blowup) remains. Stage **R** is `Cascade/Boussinesq.lean` (the frozen
> two-species dyadic Boussinesq model), plus `Cascade/BoussinesqScaling.lean` (scaling covariance)
> and `Cascade/BoussinesqEnergy.lean` (the two-species energy balance). Stage **A** is
> `Cascade/Lacunary.lean` (the lacunary ansatz and the *exact* amplitude-ODE reduction) plus
> `Cascade/Amplitude.lean` (the Rayleigh–Taylor growth rate). Stage **O** is
> `Cascade/Obstruction.lean` (the pointwise obstruction), `Cascade/Gronwall.lean` (the abstract
> Grönwall engine) and `Cascade/NoBlowup.lean` (capstone: no finite-time **energy** blowup).
> Stage **O′** is `Cascade/Enstrophy.lean` (the enstrophy budget), `Cascade/Riccati.lean` (the
> Bernoulli barrier engine), `Cascade/EnstrophyBound.lean` (capstone: no finite-time blowup in
> the **enstrophy/`H¹`** norm) and `Cascade/ScaleObstruction.lean` (the frequency-localized
> version, tied to Palasek's `N^{d/2}`-vs-`N²` comparison). `lake build Cascade` and
> `lake build Criticality` are both
> green; **every** new theorem's `#print axioms` is `[propext, Classical.choice, Quot.sound]`;
> no `sorry`.
>
> **Bernstein (Pillar A) has moved into this library.** `ConcentrationBarrier.lean`,
> `Bernstein.lean`, `BernsteinGrowth.lean` were relocated from `Criticality/` to `Cascade/`
> and renamed into the `Cascade` namespace. `Criticality/` now *depends on* `Cascade` and
> re-exports the declarations under the `Criticality` namespace via `Criticality/BernsteinExport.lean`
> (genuine `alias`es — same bodies, same axioms), so the documented `Criticality.bernstein*`
> API still resolves. `Cascade` is self-contained: it imports no `Criticality` module.

---

## Library layout

| File | Contents |
|---|---|
| `Cascade/ShellModel.lean` | stage S — one-species dyadic shell model |
| `Cascade/Boussinesq.lean` | stage R — frozen model + general version + pairing/flux lemmas |
| `Cascade/BoussinesqScaling.lean` | stage R — scaling covariance (general + frozen) |
| `Cascade/BoussinesqEnergy.lean` | stage R — two-species energy balance (general + frozen) |
| `Cascade/Lacunary.lean` | stage A — lacunary ansatz + exact amplitude-ODE reduction |
| `Cascade/Amplitude.lean` | stage A — Rayleigh–Taylor growth of the amplitude system |
| `Cascade/Obstruction.lean` | stage O — pointwise obstruction inequalities |
| `Cascade/Gronwall.lean` | stage O — abstract Grönwall no-blowup engine |
| `Cascade/NoBlowup.lean` | stage O — capstone: no finite-time energy blowup |
| `Cascade/Enstrophy.lean` | stage O′ — enstrophy pairing identity + budget |
| `Cascade/Riccati.lean` | stage O′ — Bernoulli/Riccati barrier engine |
| `Cascade/EnstrophyBound.lean` | stage O′ — capstone: no finite-time `H¹` blowup |
| `Cascade/ScaleObstruction.lean` | stage O′ — frequency-localized dissipation dominance (Palasek, shell form) |
| `Cascade/BernsteinTransfer.lean` | the Bernstein `N^{d/2}` exponent is dominated by dissipation |
| `Cascade/ConcentrationBarrier.lean` | Bernstein chain, part 1 (pointwise `≤ ‖𝓕 f‖₁`) |
| `Cascade/Bernstein.lean` | Bernstein chain, part 2 (`‖f‖∞ ≤ √(vol ball) ‖f‖₂`) |
| `Cascade/BernsteinGrowth.lean` | Bernstein chain, part 3 (`L² → L∞` with the `N^{d/2}` exponent; gradient form) |
| `Criticality/BernsteinExport.lean` | re-exports the moved Pillar A under `Criticality.*` |

`Cascade.lean` imports `ShellModel`, `Boussinesq`, `BoussinesqScaling`, `BoussinesqEnergy`,
`Lacunary`, `Amplitude`, `BernsteinTransfer` (and hence the Bernstein chain).

---

## Done — Stage S (`Cascade/ShellModel.lean`)

```lean
def shellRHS (ν : ℝ) (C : ℕ → ℝ) (u : ℕ → ℝ) (k : ℕ) : ℝ :=
  C k - ν * (2 : ℝ) ^ (2 * k) * u k

theorem shell_energy_identity (ν : ℝ) (C : ℕ → ℝ) (u : ℕ → ℝ) (n : ℕ)
    (hC : (Finset.sum (Finset.range n) (fun k => u k * C k)) = 0) :
    (Finset.sum (Finset.range n) (fun k => u k * shellRHS ν C u k))
      = -ν * (Finset.sum (Finset.range n) (fun k => (2 : ℝ) ^ (2 * k) * (u k) ^ 2))

theorem transfer_le_dissipation (N : ℝ) (hN : 1 ≤ N) :
    N ^ ((3 : ℝ) / 2) ≤ N ^ (2 : ℝ)
```

---

## Done — Stage R (`Cascade/Boussinesq.lean` + scaling + energy)

Two ladders `u θ : ℤ → ℝ`; shell `k` carries wavenumber `2^k`. The **named / frozen** model
is `dyadicBoussinesqRHS (ν μ κ : ℝ) (u θ : ℤ → ℝ) (k : ℤ) : ℝ × ℝ`, the coupling choice
`A = 1, B = 0, Ã = 1, B̃ = 1` of the general model below:

```
du_k/dt = 2^k (u_{k-1}² − 2 u_k u_{k+1}) + κ θ_k − ν 2^{2k} u_k
dθ_k/dt = 2^k (u_{k-1}θ_{k-1} − 2 u_k θ_{k+1} + u_k θ_{k-1} − 2 u_{k+1}θ_{k+1}) − μ 2^{2k} θ_k
```

Nearest-octave; buoyancy `κ θ_k`; viscosity `ν 2^{2k}` and thermal diffusivity `μ 2^{2k}`.
Origin: the standard dyadic (shell) model of natural convection — Mailybaev,
[arXiv:1210.2494](https://ar5iv.labs.arxiv.org/html/1210.2494), eqs (3)–(4) at `h = 2`, `k_n = 2^n`.

### The frozen model API

```lean
def dyadicWeight (k : ℤ) : ℝ := (2 : ℝ) ^ k

def dyadicVelocityRHS (ν κ : ℝ) (u θ : ℤ → ℝ) (k : ℤ) : ℝ
def dyadicTemperatureRHS (μ : ℝ) (u θ : ℤ → ℝ) (k : ℤ) : ℝ
def dyadicBoussinesqRHS (ν μ κ : ℝ) (u θ : ℤ → ℝ) (k : ℤ) : ℝ × ℝ
def dyadicVelocityFlux (u : ℤ → ℝ) (k : ℤ) : ℝ
def dyadicTemperatureFlux (u θ : ℤ → ℝ) (k : ℤ) : ℝ
```

The four-parameter general model is kept as the structural result:

```lean
def boussinesqTransferU (A B : ℝ) (u : ℤ → ℝ) (k : ℤ) : ℝ
def boussinesqTransferTheta (At Bt : ℝ) (u θ : ℤ → ℝ) (k : ℤ) : ℝ
def generalVelocityRHS (ν κ A B : ℝ) (u θ : ℤ → ℝ) (k : ℤ) : ℝ
def generalTemperatureRHS (μ At Bt : ℝ) (u θ : ℤ → ℝ) (k : ℤ) : ℝ
def generalBoussinesqRHS (ν μ κ A B At Bt : ℝ) (u θ : ℤ → ℝ) (k : ℤ) : ℝ × ℝ
def velocityFlux (A B : ℝ) (u : ℤ → ℝ) (k : ℤ) : ℝ
def temperatureFlux (At Bt : ℝ) (u θ : ℤ → ℝ) (k : ℤ) : ℝ
```

### Why this coupling

From the thread that motivated the library, Tao points at the **exact affine wave ODE**,
eq. (3.2) of Alpöge–Buckmaster's `boussinesq.pdf` (Lemma 3.1):

```
ζ̇ = −Dᵀζ,   Θ̇ = −(Jζ·G)/(λ|ζ|²)·Ω,   Ω̇ = λζ₁Θ,
```

a *linear* system whose coefficients `D_{<q}`, `G_{<q}` are frozen from the lower layers. The
coupling choice is fixed by matching the frozen-background linearisation of the frozen model
to (3.2). This matching is **heuristic motivation, not a Lean theorem** (nothing below is
formalized), so the derivation is spelled out so it can be checked by hand:

* Write the temperature perturbation `φ_k` and the vorticity perturbation `Ω_k := 2^k v_k`
  (`v_k` = velocity perturbation). Perturb only octave `k` and freeze every other octave.
  In the temperature equation the *only* surviving linear terms are the two carrying `u_k`
  at fixed `k`: `−2Ã·2^k u_k θ_{k+1}` contributes `−2Ã θ̄_{k+1} Ω_k`, and
  `+B̃·2^k u_k θ_{k−1}` contributes `+B̃ θ̄_{k−1} Ω_k`. Hence
  `φ̇_k = a_k Ω_k − μ4^k φ_k + (background)`, `a_k = B̃ θ̄_{k−1} − 2Ã θ̄_{k+1}`.
  In the velocity equation the surviving linear terms give
  `v̇_k = [2^k(B ū_{k−1} − 2A ū_{k+1}) − ν4^k] v_k + κ φ_k`, i.e., multiplying by `2^k`,
  `Ω̇_k = c_k Ω_k + b_k φ_k + (background)`, `b_k = 2^k κ`,
  `c_k = 2^k(B ū_{k−1} − 2A ū_{k+1}) − ν4^k`.
  Equivalently `a_k = ∂φ̇_k/∂Ω_k`, `b_k = ∂Ω̇_k/∂φ_k`, `c_k = ∂Ω̇_k/∂Ω_k`.
* With `B̃ = 0` and the wave at the newest (highest) octave — so `θ̄_{k+1} = ū_{k+1} = 0`, and
  `Ã`'s contribution vanishes — `a_k = 0`: the temperature equation is triangular and there
  is **no `Θ̇ ∝ Ω` term** — (3.2) cannot be reached. So **`B̃ = 1` is load-bearing**: it is
  the lower-octave temperature-gradient coupling.
* `B` only adds an extra inviscid diagonal `2^k ū_{k−1}` which (3.2) does not have (in the
  PDE it vanishes because the background vorticity is spatially constant). So `B = 0`.
* `A = Ã = 1` is the default; `Ã` does not contribute at the highest octave.

The transfers are individually conservative for **all** `A, B, Ã, B̃`; the choice above is
about fidelity to (3.2), not about conservation. **Caveats recorded for later stages:**
(i) Mailybaev's own "traditional" choice is `A = ε ≈ 0.01`, `B = Ã = B̃ = 1`, so the frozen
choice is not the model he studies nor a small perturbation of it; (ii) a *scalar* shell
model has no `ζ₁` phase direction, so it cannot reproduce the AB **phase-steering control** —
any dyadic blowup will be uncontrolled, not the controlled AB one.

### Scaling covariance (Stage R deliverable)

Theorem `scaling_covariant` (and its components). With `λ = 2^s`, the scaling acts by the
shell shift `k ↦ k − s` and the amplitude factors of the Boussinesq symmetry

```
u_λ = λ^b u(λx, λ^{b+1}t),   θ_λ = λ^{2b+1} θ(λx, λ^{b+1}t),   p_λ = λ^{2b} p,
```

i.e. `scaleVelocity s b u k = dyadicWeight (s*b) * u (k-s)` and
`scaleTemperature s b θ k = dyadicWeight (s*(2*b+1)) * θ (k-s)`:

```lean
theorem scaling_covariant_velocity (s b : ℤ) (ν κ : ℝ) (u θ : ℤ → ℝ) (k : ℤ) :
    dyadicVelocityRHS (ν * dyadicWeight (s * (b - 1))) κ
        (scaleVelocity s b u) (scaleTemperature s b θ) k
      = dyadicWeight (s * (2 * b + 1)) * dyadicVelocityRHS ν κ u θ (k - s)

theorem scaling_covariant_temperature (s b : ℤ) (μ : ℝ) (u θ : ℤ → ℝ) (k : ℤ) :
    dyadicTemperatureRHS (μ * dyadicWeight (s * (b - 1)))
        (scaleVelocity s b u) (scaleTemperature s b θ) k
      = dyadicWeight (s * (3 * b + 2)) * dyadicTemperatureRHS μ u θ (k - s)

theorem scaling_covariant (s b : ℤ) (ν μ κ : ℝ) (u θ : ℤ → ℝ) (k : ℤ) :
    dyadicBoussinesqRHS (ν * dyadicWeight (s * (b - 1))) (μ * dyadicWeight (s * (b - 1))) κ
        (scaleVelocity s b u) (scaleTemperature s b θ) k
      = (dyadicWeight (s * (2 * b + 1)) * (dyadicBoussinesqRHS ν μ κ u θ (k - s)).1,
         dyadicWeight (s * (3 * b + 2)) * (dyadicBoussinesqRHS ν μ κ u θ (k - s)).2)
```

The momentum equation is homogeneous of degree `2b+1`, the temperature equation of degree
`3b+2`, and the viscosity/diffusivity rescale by `λ^{b−1}`. At `b = 1` (the fixed standard
2D choice, `boussinesqB`) the parameters are **unchanged** (`λ^0 = 1`) and the degrees are
`3` and `5`:

```lean
theorem scaling_covariant_b_one_velocity (s : ℤ) (ν κ : ℝ) (u θ : ℤ → ℝ) (k : ℤ) :
    dyadicVelocityRHS ν κ (scaleVelocity s boussinesqB u) (scaleTemperature s boussinesqB θ) k
      = dyadicWeight (3 * s) * dyadicVelocityRHS ν κ u θ (k - s)

theorem scaling_covariant_b_one_temperature (s : ℤ) (μ : ℝ) (u θ : ℤ → ℝ) (k : ℤ) :
    dyadicTemperatureRHS μ (scaleVelocity s boussinesqB u) (scaleTemperature s boussinesqB θ) k
      = dyadicWeight (5 * s) * dyadicTemperatureRHS μ u θ (k - s)

theorem scaling_pressure_gradient_degree (s b : ℤ) :
    dyadicWeight (s * (2 * b)) * dyadicWeight s = dyadicWeight (s * (2 * b + 1))
```

`b = 1` is the *unique* exponent at which `λ^{b−1} = 1` for a nontrivial scaling
(`λ ≠ 1`, i.e. `s ≠ 0`), hence the one that fixes `ν` and `μ`.
For the inviscid model (`ν = μ = 0`) the family is covariant for every `b`; viscosity breaks
it except at `b = 1`. **`b = 1` is fixed here, before any statement about solutions**
(fidelity rule 1). The `general_*` versions of all of the above hold for the four-parameter
model.

### Two-species energy balance (Stage R deliverable)

The pairing lemmas say the nonlinear transfer contributes only a boundary flux:

```lean
theorem dyadic_velocity_pairing_eq_flux (u : ℤ → ℝ) (k : ℤ) :
    u k * boussinesqTransferU 1 0 u k = dyadicVelocityFlux u k - dyadicVelocityFlux u (k + 1)

theorem dyadic_temperature_pairing_eq_flux (u θ : ℤ → ℝ) (k : ℤ) :
    θ k * boussinesqTransferTheta 1 1 u θ k
      = dyadicTemperatureFlux u θ k - dyadicTemperatureFlux u θ (k + 1)
```

Summing over the truncated range `k = 0, …, n−1`:

```lean
theorem dyadic_velocity_energy_identity (ν κ : ℝ) (u θ : ℤ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, u (k : ℤ) * dyadicVelocityRHS ν κ u θ (k : ℤ))
      = dyadicVelocityFlux u 0 - dyadicVelocityFlux u (n : ℤ)
        + κ * (∑ k ∈ Finset.range n, u (k : ℤ) * θ (k : ℤ))
        - ν * (∑ k ∈ Finset.range n, dyadicWeight (2 * (k : ℤ)) * (u (k : ℤ)) ^ 2)

theorem dyadic_temperature_energy_identity (μ : ℝ) (u θ : ℤ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, θ (k : ℤ) * dyadicTemperatureRHS μ u θ (k : ℤ))
      = dyadicTemperatureFlux u θ 0 - dyadicTemperatureFlux u θ (n : ℤ)
        - μ * (∑ k ∈ Finset.range n, dyadicWeight (2 * (k : ℤ)) * (θ (k : ℤ)) ^ 2)

theorem dyadic_energy_identity (ν μ κ : ℝ) (u θ : ℤ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n,
        (u (k : ℤ) * (dyadicBoussinesqRHS ν μ κ u θ (k : ℤ)).1
          + θ (k : ℤ) * (dyadicBoussinesqRHS ν μ κ u θ (k : ℤ)).2))
      = (dyadicVelocityFlux u 0 - dyadicVelocityFlux u (n : ℤ))
        + (dyadicTemperatureFlux u θ 0 - dyadicTemperatureFlux u θ (n : ℤ))
        + κ * (∑ k ∈ Finset.range n, u (k : ℤ) * θ (k : ℤ))
        - ν * (∑ k ∈ Finset.range n, dyadicWeight (2 * (k : ℤ)) * (u (k : ℤ)) ^ 2)
        - μ * (∑ k ∈ Finset.range n, dyadicWeight (2 * (k : ℤ)) * (θ (k : ℤ)) ^ 2)
```

Reading: velocity energy grows at the buoyancy rate `κ Σ u_k θ_k` and decays at the viscous
rate `ν Σ 2^{2k} u_k²`; entropy decays only at `μ Σ 2^{2k} θ_k²`. The nonlinear transfers
survive only as the boundary fluxes at shells `0` and `n`. **`Σ½(u_k² + θ_k²)` is not
conserved** — the missing invariant is the potential term (`∫αgzθ` in the PDE, and `z` is
not a shell variable); cf. the paragraph following Mailybaev eqs (5)–(6). The `general_*`
versions hold for the
four-parameter model.

**Consequence for Stage O (recorded now, from the audit).** Since entropy is non-increasing,
`|κ Σ u_k θ_k| ≤ |κ| √(2E_u) √(2S(0))`, so buoyancy alone cannot produce finite-time blowup
(uniform bound for `ν > 0`, at most linear growth for `ν = 0`). The quantity that can grow is
the **enstrophy `Σ 4^k u_k² = Σ Ω_k²`**, not the transfer-conserved `Σ u_k²`. A Stage O
"dissipation beats transfer" theorem must bound the buoyancy term separately (or state the
entropy hypothesis) rather than assume a conservation law the model lacks.

### Bonus — the Bernstein arrow (`Cascade/BernsteinTransfer.lean`)

`Cascade/ShellModel.lean`'s `transfer_le_dissipation` states the scalar `N^{3/2} ≤ N²` with
the `3/2` hard-coded. This file derives it from the actual Bernstein exponent:

```lean
theorem bernstein_exponent_le_dissipation {d : ℕ} (hd : d ≤ 4) (N : ℝ) (hN : 1 ≤ N) :
    N ^ ((d : ℝ) / 2) ≤ N ^ (2 : ℝ)

theorem finrank_euclideanSpace_fin_three :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3

theorem transfer_le_dissipation_bernstein (N : ℝ) (hN : 1 ≤ N) :
    N ^ ((Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) : ℝ) / 2) ≤ N ^ (2 : ℝ)

theorem bernstein_L2_to_Linf_dissipation (hf : (Module.finrank ℝ V : ℝ) / 2 ≤ 2)
    [CompleteSpace F] (f : 𝓢(V, F)) (N : ℝ) (hN : 1 ≤ N)
    (hband : ∀ x, 𝓕 f x ≠ 0 → ‖x‖ < N) :
    ‖f.toBoundedContinuousFunction‖ ≤
      Real.sqrt (volume (Metric.ball (0 : V) 1)).toReal * N ^ (2 : ℝ) * ‖f.toLp 2 volume‖
```

The `3/2` is no longer a literal: it is `(Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))/2`,
the exact exponent of `Cascade.bernstein_L2_to_Linf`, and the last theorem composes Bernstein
with the exponent comparison in every dimension `d ≤ 4`.

---

## Done — Stage A (`Cascade/Lacunary.lean` + `Cascade/Amplitude.lean`)

### The lacunary ansatz and the exact reduction

At generation `n : ℤ` the active octave is `N_n = 2^n`; the background `(u₋, θ₋)` lives
strictly below `n` and the wave amplitudes `(a, b)` sit at octave `n`
(`u = Function.update u₋ n a`, `θ = Function.update θ₋ n b`, with `u₋ (n+1) = θ₋ (n+1) = 0`).

The reduction is **exact, not a linearisation error**: the shell-`n` RHS is affine in `(a, b)`
because no `u_n²`, `θ_n²` or `u_nθ_n` term exists, and the only discarded couplings are the
`n+1` ones, killed by the support hypotheses.

```lean
def lacunaryVelocity (n : ℤ) (u_minus : ℤ → ℝ) (a : ℝ) : ℤ → ℝ
def lacunaryTemperature (n : ℤ) (θ_minus : ℤ → ℝ) (b : ℝ) : ℤ → ℝ
def lacunaryFrequency (n : ℤ) : ℝ := dyadicWeight n
def lacunaryVorticity (n : ℤ) (a : ℝ) : ℝ := dyadicWeight n * a

def lacunaryVelocityRHS (ν κ A B : ℝ) (n : ℤ) (u_minus : ℤ → ℝ) (a b : ℝ) : ℝ
def lacunaryTemperatureRHS (μ At Bt : ℝ) (n : ℤ) (u_minus θ_minus : ℤ → ℝ) (a b : ℝ) : ℝ
def dyadicLacunaryVelocityRHS (ν κ : ℝ) (n : ℤ) (u_minus : ℤ → ℝ) (a b : ℝ) : ℝ
def dyadicLacunaryTemperatureRHS (μ : ℝ) (n : ℤ) (u_minus θ_minus : ℤ → ℝ) (a b : ℝ) : ℝ

theorem lacunary_reduction_velocity (ν μ κ A B At Bt : ℝ) (n : ℤ) … (hu : u_minus (n+1) = 0) :
    (generalBoussinesqRHS ν μ κ A B At Bt (lacunaryVelocity n u_minus a)
        (lacunaryTemperature n θ_minus b) n).1 = lacunaryVelocityRHS ν κ A B n u_minus a b
theorem lacunary_reduction_temperature …
theorem lacunary_reduction_dyadic_velocity / lacunary_reduction_dyadic_temperature
```

Writing `Ω_n = 2^n a` (vorticity amplitude) and `Θ_n = b` (temperature amplitude), the part
linear in `(Ω, Θ)` is exactly Tao's page-4 ODE (Alpöge–Buckmaster eq. (3.2)):

```
Θ̇ = θ̄_{n−1} Ω − μ 4^n Θ,      θ̄_{n−1} := B̃ θ₋_{n−1},
Ω̇ = 2^n κ Θ − ν 4^n Ω,
```

with off-diagonal couplings `a_n = θ̄_{n−1}` (lower-octave temperature gradient) and
`b_n = 2^n κ` (one-derivative buoyancy `N_n κ`). This **supersedes the previously unformalized
prose** in `Cascade/Boussinesq.lean`; the reduction is a machine-checked theorem, not a sketch.

### The amplitude growth (`Cascade/Amplitude.lean`)

Standalone (Mathlib only). For the inviscid amplitude matrix `M = !![0, b; a, 0]`:

* `rayleighTaylorMatrix_mulVec : M *ᵥ ![Θ, Ω] = ![b*Ω, a*Θ]`;
* `rayleighTaylor_charpoly : charpoly M = X^2 - C (a*b)`, with eigenvectors `![b, ±√(ab)]`
  when `a*b ≥ 0` (`rayleighTaylor_eigenvector_pos/_neg`);
* `rayleighTaylorSolution` — the explicit `cosh`/`sinh` solution of `Θ̇ = bΩ`, `Ω̇ = aΘ` —
  with `rayleighTaylorSolution_hasDerivAt` and `rayleighTaylorSolution_unbounded`
  (`Tendsto … atTop atTop` for `a*b > 0`, `Θ₀ > 0`, plus the documented sign hypothesis
  `0 ≤ b·Ω₀`);
* the stably stratified counterpart `rayleighTaylorOscillation` / `_hasDerivAt` / `_bounded`
  (`cos`/`sin` at the Brunt–Väisälä frequency `√(−ab)` when `a*b < 0`);
* `rayleighTaylor_growthRate_dichotomy`: the growth rate `√(ab)` is positive exactly when
  `a*b > 0`.

Reading: with the frozen `B̃ = 1` we get `a_n = θ₋_{n−1}`, so an unstably stratified background
(`2^n κ θ₋_{n−1} > 0`) grows the wave exponentially at rate `√(N_n κ θ₋_{n−1})` — the
Rayleigh–Taylor instability that Stage B must turn into a finite-time blowup.

---

## Done — Stage O (`Obstruction.lean` + `Gronwall.lean` + `NoBlowup.lean`)

**The obstruction.** The interior nonlinear transfer is exactly energy-conserving: by the Stage-R
pairing/flux lemmas, `Σ_k u_k T^u_k` is a *difference of boundary fluxes*, and the truncation /
Dirichlet conditions `u(−1) = u(N) = θ(−1) = θ(N) = 0` kill both. So there is no interior energy
source; the only bulk source is buoyancy, bounded by the entropy, and viscosity dominates. Hence
the unforced truncated model has **no finite-time energy blowup** — Palasek's obstruction,
formalized.

### Model-side inequalities (`Cascade/Obstruction.lean`)

```lean
theorem sum_mul_le_sqrt_mul_sqrt (s : Finset ℤ) (u θ : ℤ → ℝ) :
    (∑ k ∈ s, u k * θ k) ≤ Real.sqrt (∑ k ∈ s, (u k)^2) * Real.sqrt (∑ k ∈ s, (θ k)^2)

theorem velocity_energy_rate_le (ν κ : ℝ) (hκ : 0 ≤ κ) (hν : 0 ≤ ν) (u θ : ℤ → ℝ) (n : ℕ)
    (hbot : u (-1) = 0) (htop : u (n : ℤ) = 0) :
    (∑ k ∈ Finset.range n, u (k : ℤ) * dyadicVelocityRHS ν κ u θ (k : ℤ))
      ≤ κ * (Real.sqrt (∑u²) * Real.sqrt (∑θ²)) - ν * (∑u²)

theorem temperature_energy_rate_nonpos (μ : ℝ) (hμ : 0 ≤ μ) (u θ : ℤ → ℝ) (n : ℕ)
    (hbot : θ (-1) = 0) (htop : θ (n : ℤ) = 0) :
    (∑ k ∈ Finset.range n, θ (k : ℤ) * dyadicTemperatureRHS μ u θ (k : ℤ)) ≤ 0

theorem no_energy_production_except_buoyancy … : (velocity pairing ≤ κ√E√S - νE) ∧ (temperature pairing ≤ 0)
```

**`hκ : 0 ≤ κ` is required.** As first specified the velocity bound is *false* for `κ < 0`: a
machine-checked counterexample (`ν=1, κ=−1, n=1, u₀=1, u₁=0, θ≡−1` gives LHS `0`, RHS `−2`) was
produced and removed. `κ ≥ 0` is the physical buoyancy sign.

### The Grönwall engine (`Cascade/Gronwall.lean`, standalone)

`le_gronwallBound_of_hasDerivAt` (linear comparison, from mathlib's
`le_gronwallBound_of_liminf_deriv_right_le`), `gronwallBound_le_max_of_neg` (uniform-in-time bound
when `b < 0`). For the model's `E' ≤ 2κ√S₀·√E − 2νE` the AM–GM step `2√E ≤ 1 + E` gives the
linear inequality `E' ≤ a + bE` with `a = κ√S₀`, `b = κ√S₀ − 2ν`; hence
`energy_le_max_of_rate_le` (uniform bound `E t ≤ max (E 0) (κ√S₀/(2ν − κ√S₀))` when `2ν > κ√S₀`)
and `no_finite_time_blowup` (bounded on every compact `[0,T]`, with the explicit constant
`energyBound`). **Continuity is required and was added**: the literal `[0,T)`-derivative
statements are false without it — `E t = exp(−2νt)/t`, `E 0 = 0` satisfies every stated
hypothesis and is unbounded at `0⁺` — so the theorems carry `ContinuousOn`/`ContinuousAt`.

### The capstone (`Cascade/NoBlowup.lean`)

```lean
def IsUnforcedTruncatedSolution (ν μ κ : ℝ) (N : ℕ) (u θ : ℝ → ℤ → ℝ) : Prop
def velocityEnergy (u : ℤ → ℝ) (N : ℕ) : ℝ
def entropy (θ : ℤ → ℝ) (N : ℕ) : ℝ

theorem velocityEnergy_hasDerivAt … : HasDerivAt (fun s => velocityEnergy (u s) N)
    (2 * ∑ k ∈ Finset.range N, u t (k : ℤ) * dyadicVelocityRHS ν κ (u t) (θ t) (k : ℤ)) t
theorem entropy_hasDerivAt …
theorem entropy_antitone (hμ : 0 ≤ μ) … : Antitone fun t => entropy (θ t) N

theorem truncated_unforced_energy_bounded (hν : 0 < ν) (hμ : 0 ≤ μ) (hκ : 0 ≤ κ) … :
    ∃ C, ∀ t ∈ Set.Icc 0 T, velocityEnergy (u t) N ≤ C
theorem truncated_unforced_energy_le_max … (hgap : 0 < 2 * ν - κ * Real.sqrt (entropy (θ 0) N)) :
    ∀ t ∈ Set.Icc 0 T,
      velocityEnergy (u t) N ≤ max (velocityEnergy (u 0) N)
        (κ * Real.sqrt (entropy (θ 0) N) / (2 * ν - κ * Real.sqrt (entropy (θ 0) N)))
```

The predicate is inhabited (`zero_is_unforcedTruncatedSolution`), and the rate inequality is
checked non-vacuously at a concrete non-zero state (`E = 10`, `S = 5`, pairing `= −30`,
`−60 ≤ 2√5·√10 − 20`, strict). The capstone carries a redundant `hcont : ContinuousOn …`
(derivable from differentiability) kept for interface symmetry; note it when reusing.

**Scope caveat.** This is the *truncated* model with Dirichlet ends — the boundary conditions are
an explicit modelling hypothesis. The stronger **enstrophy** statement is a documented stretch:
the conserved pairing is `Σ u_k T^u_k = 0`, but the enstrophy pairing `Σ 4^k u_k T^u_k` does
**not** telescope (`= (3/4)Σ 8^k u_{k−1}²u_k` on a finite range), so enstrophy genuinely
cascades; bounding it is a Riccati/Bernoulli estimate, not claimed here.

---

## Done — Stage O′ (`Enstrophy.lean` + `Riccati.lean` + `EnstrophyBound.lean`)

Stage O bounds the **`L²` energy**, which is *not* the norm blowup is measured in. Stage O′ bounds
the **enstrophy** `H = Σ4^k u_k²`, i.e. the `H¹` norm.

**Key fact — enstrophy cascades.** Energy is conserved by the transfer (`Σ u_k T^u_k = 0`), but
enstrophy is not:

```lean
theorem enstrophy_pairing (ν κ : ℝ) (u θ : ℤ → ℝ) (N : ℕ)
    (huBot : u (-1) = 0) (huTop : u (N : ℤ) = 0) :
    (∑ k ∈ Finset.range N, dyadicWeight (2*(k:ℤ)) * u (k:ℤ) * dyadicVelocityRHS ν κ u θ (k:ℤ))
      = 3 * (∑ k ∈ Finset.range N, (vorticity u ((k:ℤ)-1))^2 * vorticity u (k:ℤ))
        + κ * (∑ k ∈ Finset.range N, dyadicWeight (2*(k:ℤ)) * u (k:ℤ) * θ (k:ℤ))
        - ν * (∑ k ∈ Finset.range N, dyadicWeight (4*(k:ℤ)) * (u (k:ℤ))^2)
```
with `vorticity u k = 2^k u_k` and `dyadicWeight k = 2^k`. On `u = (0,1,3,0)` both sides are `18`.
Proved via an explicit enstrophy flux `enstrophyFlux u k = (1/4)·8^k u_{k-1}²u_k` and telescoping
(`transfer_enstrophy_pointwise`).

**The budget.** `Σ_k 4^k u_k·dyadicVelocityRHS_k ≤ 3H√H + κ√H√T − νH²/E`, assembled from
`sum_vorticity_cubic_le` (`Σa_{k-1}²a_k ≤ H√H`, needs `u(-1)=0` — false without it),
`enstrophy_sq_le_dissipation_mul_energy` (`H² ≤ (Σ16^k u_k²)·E`, Cauchy–Schwarz interpolation) and
`buoyancy_enstrophy_le` (`Σ4^k u_kθ_k ≤ √H√T`). The transfer is **cubic** (`H^{3/2}`) against
**quadratic** dissipation (`H²/E`), ratio `E/√H → 0` — the correct form of "dissipation beats
transfer", as opposed to the naive termwise `N^{3/2}` vs `N²` comparison.

**The engine** (`Cascade/Riccati.lean`, standalone): the Bernoulli barrier
```lean
theorem le_of_deriv_le_bernoulli {y y'} {a b T : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hcont : ContinuousOn y (Set.Icc 0 T)) (hderiv : ∀ t ∈ Set.Ico 0 T, HasDerivAt y (y' t) t)
    (hineq : ∀ t ∈ Set.Ico 0 T, y' t ≤ a * y t * Real.sqrt (y t) - b * (y t)^2) :
    ∀ t ∈ Set.Icc 0 T, y t ≤ max (y 0) ((a / b)^2)
```
proved by first-crossing + mean value theorem (no ODE-comparison black box, **no added
hypotheses**), plus `le_of_deriv_le_const_sub_sq`. `y * √y` is used throughout so no `Real.rpow`
appears.

**The capstone** (`Cascade/EnstrophyBound.lean`):
```lean
theorem truncated_unforced_enstrophy_bounded (hν : 0 < ν) (hμ : 0 < μ) (hκ : 0 ≤ κ) … :
    ∃ C, ∀ t ∈ Set.Icc 0 T, enstrophy (u t) N ≤ C

theorem enstrophy_bounded_isothermal … (hκ0 : κ = 0) … :
    ∀ t ∈ Set.Icc 0 T, enstrophy (u t) N ≤ max (enstrophy (u 0) N) ((3 * E_max / ν) ^ 2)
```
Route: the **Lyapunov function** `enstrophyLyapunov = H + (κ/(2μ))·S`, whose `S' = −2μT` cancels
the `+κT` buoyancy source exactly (`temperature_pairing_eq_neg_mu_tempEnstrophy`); Young
(`young_cubic_le`, `young_linear_le` — both **sharp**, equality at the optimal points) absorbs
`6H√H` and `κH` into the dissipation, giving `Ψ' ≤ enstrophyYoungConst ν κ E_max` and hence
`H(t) ≤ H(0) + (κ/(2μ))S(0) + enstrophyYoungConst ν κ E_max · T`. The bound is **linear in `T`** —
bounded on every compact interval, exactly no finite-time blowup in the `H¹` norm. For `κ = 0` the
source is absent and the barrier gives the strictly better **uniform** bound
`H ≤ max(H(0), (3E_max/ν)²)`.

**Scope caveats.** Still the *truncated* model with Dirichlet ends, still *unforced*. The
uniform-in-`T` bound for `κ > 0` (as opposed to linear-in-`T`) would need the coupled `(H, T)`
system done jointly and is not claimed. The ODE continuation corollary (bounded on compacts ⟹
global existence) is also not formalised.

**Frequency-localized version, tied to Palasek's argument** (`Cascade/ScaleObstruction.lean`):

```lean
theorem dissipation_tail_ge (u : ℤ → ℝ) (K N : ℕ) (hKN : K ≤ N) :
    dyadicWeight (2*(K:ℤ)) * (∑ k ∈ Finset.Ico K N, dyadicWeight (2*(k:ℤ)) * (u (k:ℤ))^2)
      ≤ ∑ k ∈ Finset.Ico K N, dyadicWeight (4*(k:ℤ)) * (u (k:ℤ))^2

theorem tail_transfer_cubic_le (u : ℤ → ℝ) (K N : ℕ) (huBot : u (-1) = 0) :
    |∑ k ∈ Finset.Ico K N, (vorticity u ((k:ℤ)-1))^2 * vorticity u (k:ℤ)|
      ≤ enstrophy u N * Real.sqrt (enstrophy u N)

theorem scale_dissipation_dominates (ν : ℝ) (hν : 0 < ν) … (hthr : 3 * (H * √H) ≤ ν * N_K² * H_tail) :
    3 * |∑_{k∈Ico K N} a_{k-1}²a_k| ≤ ν * (∑_{k∈Ico K N} 16^k u_k²)

theorem bernstein_exponent_gt_dissipation {d : ℕ} (hd : 5 ≤ d) (N : ℝ) (hN : 1 < N) :
    N ^ (2:ℝ) < N ^ ((d:ℝ)/2)
```

**Honest framing** (recorded in the file header). Palasek's argument is a **spatial** one: Bernstein
`L²→L∞` converts an energy bound into an `N_k^{d/2}` amplitude bound, compared against viscous
damping `νN_k²`. A shell model has **explicit amplitudes**, so `|a_k| ≤ √H`
(`vorticity_abs_le_sqrt_enstrophy`) replaces Bernstein and is *stronger* than `N^{d/2}√E`; hence
the factor `N_k^{3/2}` **never appears literally**. This is Palasek's comparison *in shell
variables*, not the literal spatial-Bernstein proof. The `d/2`-vs-`2` dichotomy is recorded
separately — `N^{d/2} ≤ N²` for `d ≤ 4` (`Cascade.bernstein_exponent_le_dissipation`, delegating to
`BernsteinTransfer`) and `N² < N^{d/2}` for `d ≥ 5`, `N > 1`
(`Cascade.bernstein_exponent_gt_dissipation`, the new high-dimension direction, Palasek's "no
obstruction in high dimension"). `tail_transfer_cubic_le` needs `u(-1) = 0` — it is false without
it (`K=0`, `u(-1)=2000`, `u(0)=1`, `N=1` gives `10⁶ > 1`), because the boundary amplitude sits in
the tail with no matching contribution to `H`.

**Upshot.** The dyadic obstruction does not need Bernstein, and is *strictly easier* than the PDE
heuristic — which is exactly Tao's hope that removing unwanted interactions makes the argument
shorter and more transparent. The transfer/dissipation dichotomy is captured by the shell's own
`H^{3/2}`-vs-`H²/E` budget, and the `d/2`-vs-`2` comparison is retained separately as the
"where the obstruction lives" statement.

---

## Not started

- **Stage B** — forced blowup. Needs the *forced* model fixed first: force support, and whether
  `ν, μ` stay. Recommendation: **viscous + force**, i.e. the same model as Stage O with the force
  toggled, so that `B ∧ O` is the same model with the force off/on (Palasek's obstruction is a
  viscous, `N²` statement). Precedents: Cheskidov, *Blow-up in finite time for the dyadic model of
  the Navier–Stokes equations* (`arXiv:math/0601074`); Katz–Pavlović, *Finite time blow up for a
  dyadic model of the Euler equations*. Caveat recorded in `VISION`-fidelity terms: a scalar shell
  model has no `ζ₁` phase direction, so it cannot reproduce the AB *controlled* construction — any
  dyadic blowup will be uncontrolled/self-similar.
- **Capstone `B ∧ O`** — the forced/unforced asymmetry, the formal content of the Tao/Palasek
  exchange *in the model*.

---

## Build

```bash
cd /Users/ronaldrogers/Code/NavierStokesAndEuler
export ELAN_HOME="$PWD/.elan"
export PATH="$ELAN_HOME/bin:$PATH"
export MATHLIB_CACHE_DIR="$PWD/.cache/mathlib"
lake build Cascade        # this library (includes the relocated Bernstein chain)
lake build Criticality    # sibling skeleton (now depends on Cascade for Pillar A)
lake env lean Cascade/<file>.lean   # fast single-file check while iterating
```

`lake build Cascade` and `lake build Criticality` both exit 0. `#print axioms` is appended at
the bottom of each file.

---

## Reference material

- Mastodon thread — all links quoted in `VISION.md` (Tao ×2, Tao→Nalini Joshi, Palasek,
  Buckmaster). Tao's reply to Nalini Joshi names the key ODE:
  <https://mathstodon.xyz/@tao/117234137753542696> → the second display on page 4 of
  `boussinesq.pdf`, i.e. eq. (3.2) "Exact affine wave".
- **Alpöge–Buckmaster**, *Blowup for the Boussinesq equations with smooth forcing* —
  `cims.nyu.edu/~tristanb/` (`boussinesq.pdf`). Lemma 3.1 / eq. (3.2) is the Stage A target;
  §3.2 eq. (3.3) gives the background coefficients `G_{<q}`, `D_{<q}`, `A_j = −λ_j|ζ_j|Θ_j`.
- **Mailybaev**, *Bifurcations of blowup in inviscid shell models of convective turbulence*,
  [arXiv:1210.2494](https://ar5iv.labs.arxiv.org/html/1210.2494) — the source of the
  four-parameter convection shell model (eqs (3)–(4)); the paragraph following its eqs (5)–(6)
  states the entropy
  conservation and the absence of a total-energy invariant.
- `../LEAN_PDE_PRIOR_ART.md` and `../research_lean4_pde_formalizations.md` — prior-art surveys.
- **`tristanbuckmaster/fluid_lean`** — reference only, do not port (see below).

---

## Gotchas

1. **Big-operator binder.** This Mathlib pin rejects `∑ k in s, …`
   (`unexpected token 'in'; expected ','`). Use `∑ k ∈ s, …`, which elaborates to the same
   `Finset.sum s (fun k => …)`.
2. **`b = 1` is the fixed Boussinesq exponent** (`boussinesqB`), fixed in
   `BoussinesqScaling.lean` before any solution statement. For a nontrivial scaling
   (`λ ≠ 1`, i.e. `s ≠ 0`), `λ^{b−1} = 1` only at `b = 1`.
3. **`[local irreducible]` does not propagate across imports.** Files touching `𝓕`/`𝓕⁻` or
   `Real.rpow` must re-declare `attribute [local irreducible] Real.rpow`,
   `SchwartzMap.fourierTransformCLM`, `MeasureTheory.Lp.fourierTransformₗᵢ` locally.
4. **Write the measure explicitly** (`‖f.toLp 2 volume‖`) when `𝓕` meets `toLp`; the default
   `volume_tac` can fail mid-elaboration.
5. **`Real.sqrt x` is not defeq to `x ^ (1/2)`** — use `Real.sqrt_eq_rpow`.
6. **Use `ring_nf`, not `ring`, on the telescoping pairing goals.** `ring` closes them but
   emits a cosmetic `info: Try this: ring_nf …` line; `ring_nf` is silent and yields the
   same kernel-checked term.
7. **Plancherel needs `[InnerProductSpace ℂ F]`.** `SchwartzMap.norm_fourier_toL2_eq`,
   `MeasureTheory.Lp.norm_fourier_eq` and the L² Fourier isometry all assume a complex
   *inner-product* space; there is no Plancherel for `[NormedSpace ℂ F]` alone.
8. **Library plumbing.** `Cascade` is registered in `lakefile.toml` as
   `[[lean_lib]] name = "Cascade" globs = ["Cascade", "Cascade.+"]` with root `Cascade.lean`.
   New submodules must be imported from `Cascade.lean` to be covered by `lake build Cascade`.
9. **`fluid_lean`** (`tristanbuckmaster/fluid_lean`) is reference only: ~1,400 modules (mostly
   machine-generated certificates), Lean `v4.32.2`, ~150 GB build, unmaintained, statement
   module recorded as `review: unreviewed`. Do not port.
10. **The subscript-minus glyph `₋` is not a legal identifier character** in this pin; the
    background ladders are spelled `u_minus` / `θ_minus` in code (the prose writes `u₋`, `θ₋`).
    Also, this pin has no `Function.update_noteq`; use
    `Function.update_of_ne (show n - 1 ≠ n by omega)`.
11. **Sign hypotheses are load-bearing.** The Stage-O velocity rate bound needs `0 ≤ κ` (false
    for `κ < 0`), and the Grönwall no-blowup statements need continuity (`ContinuousOn`/
    `ContinuousAt`); the literal `[0,T)`-derivative forms are false. Don't drop them when
    restating.
12. **`HasDerivAt.sum` returns a sum in the function space**, not the pointwise sum, and plain
    function types lack the `FunLike` instance the generic `sum_apply` needs at this pin;
    `Cascade/NoBlowup.lean` provides `finset_sum_apply` for this. `antitone_of_hasDerivAt_nonpos`
    lives in `Mathlib.Analysis.Calculus.Deriv.MeanValue` (not re-exported by
    `Mathlib.Analysis.Calculus.MeanValue`).
