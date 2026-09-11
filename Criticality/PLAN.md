# Plan: the Criticality Skeleton

The target specification. This file is meant to change slowly; the *current
state* lives in `PROGRESS.md`, the *motivation* in `VISION.md`.

The skeleton is **five pillars** of Lean theorems. The deliverable is not one big
theorem but the **dependency graph** (see the capstone below): each pillar is a
self-contained family, and the arrows between them are explicit proved
implications over a shared core.

---

## Pillar A — The concentration barrier (uncertainty + Bernstein)

The shared fact: *band-limiting to frequency `N` forces spatial spread `≳ 1/N`.*

- **A1 (Heisenberg):** for `f ∈ L²(ℝ^d)`, the product of spatial and frequency
  variances is bounded below: `Δx(f) · Δξ(f) ≥ d/2`.
- **A2 (Bernstein, `L² → L∞`):** if `supp(f̂) ⊆ B(0,N)` then
  `‖f‖∞ ≤ C_d · N^{d/2} · ‖f‖₂`.
- **A3 (Bernstein, gradient):** `‖∇f‖∞ ≤ C_d · N^{1+d/2} · ‖f‖₂`.
- **A4 (the shared core):** a single lemma — "band-limiting ⇒ spatial spread
  `≳ 1/N`" — from which **A1, A2, A3 all follow**. This is the formal statement
  that "Heisenberg and Bernstein are the same principle".

*Working medium:* Schwartz space `𝓢(V, F)` (clean pointwise Fourier transform),
then extend to `L²`/general `L^p` as needed.

---

## Pillar B — The additive/multiplicative structure of frequencies

- **B1 (dyadic decomposition):** any `f` splits into a sum of band-limited pieces,
  one per octave `[2ᵏ, 2ᵏ⁺¹)` (Littlewood–Paley partition of unity). This is the
  "multiplicative grouping".
- **B2 (additive coupling):** multiplication in space = convolution in frequency;
  equivalently, the frequency `ω` of `(u·∇)u` is fed by **every** pair `(ξ, η)`
  with `ξ + η = ω`. This makes precise the all-to-all additive interaction
  against the dyadic grouping.

---

## Pillar C — The criticality of 3D Navier–Stokes

- **C1 (scaling symmetry):** `u_λ(x,t) = λ · u(λx, λ²t)` preserves the Navier–Stokes
  equation (with `p_λ = λ² p`).
- **C2 (critical norm):** the `L^d` norm is exactly scale-invariant; more
  generally `2/p + d/q = 1` for `Lᵖₜ L^qₓ`.
- **C3 (the knife's edge):** the energy norm `L²` is *at* criticality when `d = 2`,
  and *strictly subcritical* when `d ≥ 3`. Formally: **3 is the first dimension
  where energy falls below the critical scaling.**

---

## Pillar D — The dyadic shell model and the obstruction

The dyadic shell model: one complex variable `u_k` per frequency octave, with
nearest-neighbor coupling and viscosity `ν·2^{2k}`:

```
d u_k / dt  =  (nonlinear coupling of k−1, k, k+1)  −  ν · 2^{2k} · u_k
```

- **D1 (energy identity):** the shell-model energy balance.
- **D2 (the obstruction, rigorous *in the model*):** an **unforced** lacunary
  cascade has transfer rate `O(N_k^{3/2})` (by **Bernstein**, Pillar A) which is
  dominated by dissipation `N_k²`, so it cannot self-sustain. This is the tweet's
  argument ([arXiv:2605.13827](https://arxiv.org/abs/2605.13827)) made a theorem.
- **D3 (optional, the flip side):** *with* forcing, the shell model blows up
  (a Palasek-type result, restricted to the ODE model).

---

## Pillar E — The additive↔multiplicative bridge (number theory)

- **E1 (Euler product):** the Dirichlet series equals the Euler product:
  `riemannZeta_eulerProduct`. **Already in mathlib**
  (`Mathlib/NumberTheory/EulerProduct/DirichletLSeries.lean`); this pillar is just
  re-exposure and commentary.

---

## The capstone: the dependency graph

```
A (uncertainty/Bernstein) ──is the tool in──▶  D2 (cascade subcritical in 3D)
B (dyadic vs convolution)  ──structure of──▶   D (shell model)
C (scaling criticality)    ──why 3D is special──▶  D2's knife's edge
E (Euler product)          ──number-theory avatar of──▶  B's additive/multiplicative tension
```

With this in Lean, each arrow is a **proved implication** (or a shared definition)
— except the last ("avatar of"), which is an *observation*, not a theorem. The
skeleton certifies the derivations and the shared structure; it does not certify
the analogy's meaning.

---

## Explicitly out of scope

- AdS/CFT as a bridge between the two dualities;
- "why is the universe 3-dimensional";
- Hilbert–Pólya / Berry–Keating (Riemann zeros as a spectrum).

These are not mathematical theorems, so Lean cannot touch them. See `VISION.md`.
