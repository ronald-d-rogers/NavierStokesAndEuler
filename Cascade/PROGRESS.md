# Progress: dyadic cascade models

Where we are now. The *target* is `PLAN.md`; the *why* is `VISION.md`.

> **Snapshot:** branch `dyadic-cascade`, branched off `skeleton-criticality`. Stage **S**
> is done — `Cascade/ShellModel.lean`, moved here from `Criticality/ShellModel.lean`
> (it was Pillar D of the criticality skeleton, but it is a model of the cascade, not a
> criticality theorem). Stages **R, A, B, O** not started.

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

All `#print axioms` = `[propext, Classical.choice, Quot.sound]`. The file imports only
Mathlib (`Analysis.SpecialFunctions.Pow.Real`, `Tactic.Ring`), so the move was mechanical.

---

## Not started

- **Stage R** — two-species dyadic Boussinesq model + scaling covariance + energy balance.
- **Stage A** — lacunary ansatz + amplitude-frequency ODE.
- **Stage B** — forced blowup.
- **Stage O** — unforced obstruction.

---

## Build

```bash
cd /Users/ronaldrogers/Code/NavierStokesAndEuler
export ELAN_HOME="$PWD/.elan"
export PATH="$ELAN_HOME/bin:$PATH"
export MATHLIB_CACHE_DIR="$PWD/.cache/mathlib"
lake build Cascade        # this library
lake build Criticality    # the sibling skeleton (unchanged by the move)
```

---

## Reference material

- Mastodon thread — all links quoted in `VISION.md` (Tao ×2, Palasek, Buckmaster).
- `../LEAN_PDE_PRIOR_ART.md` and `../research_lean4_pde_formalizations.md` — prior-art
  surveys of Lean PDE / fluids / harmonic analysis, with verified declaration names.
- Alpöge–Buckmaster announcement and papers: `cims.nyu.edu/~tristanb/`
  (`statement.pdf`, `euler.pdf`, `ipm.pdf`, `boussinesq.pdf`).
- **`tristanbuckmaster/fluid_lean`** — the Alpöge–Buckmaster Lean formalisation.
  **Reference only; do not port.** It is ~1,400 modules (about 1,200 of them
  machine-generated interval-arithmetic certificates), on Lean `v4.32.2`, needing on the
  order of 150 GB of RAM to build, explicitly unmaintained ("PRs not accepted"), and its
  trusted statement module is still recorded as `review: unreviewed` in
  `formalization.yaml`. It is a result artifact, not a library to build on.

---

## Gotchas

1. **Boussinesq scaling family.** `u_λ = λ^b u(λx, λ^{b+1}t)`,
   `θ_λ = λ^{2b+1} θ(λx, λ^{b+1}t)`, `p_λ = λ^{2b} p`. Under it the momentum equation is
   homogeneous of degree `2b+1` and the temperature equation of degree `3b+2`
   (both terms of each equation share the degree). `b = 1` is the standard 2D choice.
   **Fix `b` in stage R before stating any blowup theorem** (fidelity rule 1).
2. **The `3/2` in `transfer_le_dissipation` is hard-coded.** Its docstring cites Pillar A's
   Bernstein, but it does not depend on it. To make that arrow real, `import
   Criticality.BernsteinGrowth` and derive `N^{d/2}` from `bernstein_L2_to_Linf` at `d = 3`.
3. **Library plumbing.** The library is registered in `lakefile.toml` as
   `[[lean_lib]] name = "Cascade" globs = ["Cascade", "Cascade.+"]`, with root module
   `Cascade.lean` (which imports `Cascade.ShellModel`). New submodules should be imported
   from `Cascade.lean` so `lake build Cascade` covers them.
