# Vision: why formalize the "criticality skeleton"?

## The trigger

A long conversation about OpenAI's `NavierStokesAndEuler` Lean repository
(finite-time blowup for Navier–Stokes and Euler). While examining what it
actually proves, a deeper mathematical theme kept surfacing — one that connects
**fluid dynamics, harmonic analysis, and number theory** through a single
tension.

## The theme: *additive* vs *multiplicative*

- **Frequencies** interact **additively** — the nonlinear term is a convolution:
  a frequency `ω` is fed by *every* pair `(ξ, η)` with `ξ + η = ω` — yet they are
  grouped **multiplicatively** (dyadic octaves `[2ᵏ, 2ᵏ⁺¹)`).
- **Integers** are summed **additively** (the Dirichlet series `ζ(s) = Σ n⁻ˢ`)
  yet factor **multiplicatively** (the Euler product `ζ(s) = ∏ (1 − p⁻ˢ)⁻¹`).

In both settings the difficulty is the same: the *grouping* is multiplicative and
the *interaction* is additive, and the two don't see each other easily. This is
the "additive vs multiplicative" motif.

## The concentration barrier

The **Heisenberg uncertainty principle** and **Bernstein's inequality** are the
quantitative form of one fact: *band-limiting a function to frequency `N` forces
spatial spread `≳ 1/N`*. Equivalently: a fixed amount of energy cannot be
concentrated arbitrarily tightly. This is the tool that makes the **unforced**
3D Navier–Stokes frequency cascade *subcritical* against viscous dissipation
(`~N²` beats the transfer `O(N^{3/2})`).

## Why 3D is special (the "critical" dimension)

The Navier–Stokes equation has a scaling symmetry, and its *critical* norm is
`L^d`. The **energy** is `L²`:

- `d = 2`: `L²` = `L^d` — exactly critical → regularity is provable.
- `d = 3`: `L²` is strictly weaker than `L³` — *just barely* supercritical → open.
- `d ≥ 4`: deeply supercritical → blowup is "easy".

So **3 is the first dimension where energy falls below criticality, by a hair** —
a knife's edge. This is the same sense of "critical" as the Riemann critical line
`Re(s) = 1/2`, where the additive (Dirichlet) and multiplicative (Euler product)
information come into balance.

## The goal

Formalize the **provable core** of this picture in Lean. Concretely:

- the **concentration barrier** — Heisenberg + Bernstein, from one shared lemma;
- the **scaling criticality** of 3D Navier–Stokes;
- the **additive/multiplicative duality** — convolution vs dyadic grouping, and
  Dirichlet series vs Euler product.

This is the **"criticality skeleton"**: the rigorous spine underneath the analogy.
It is a *family of machine-checked theorems with explicit implications*, not a
single grand theorem — the point is to replace "these are the same idea" with
"these are proved implications over a shared definitional core".

## In scope vs out of scope

**In scope (Lean-able — theorems):**

- Heisenberg uncertainty, Bernstein's inequality (band-limiting ⇒ spread);
- Navier–Stokes scaling symmetry and the `L^d` criticality comparison;
- the dyadic shell model and the transfer-vs-dissipation obstruction;
- the Euler product (`Σ n⁻ˢ = ∏ (1−p⁻ˢ)⁻¹`) — already in mathlib.

**Out of scope (not Lean-able — physics/analogy):**

- AdS/CFT as a bridge between the two "dualities";
- "why is the universe 3-dimensional";
- Hilbert–Pólya / Berry–Keating (Riemann zeros as a spectrum).

Lean is a theorem prover for mathematics: it certifies *derivations*, not
*interpretations*. The skeleton formalizes the *provable core*; the physics
analogies remain outside it.

## The forced/unforced backdrop (why this matters)

The surrounding repo proves a **forced** Navier–Stokes breakdown (Clay options
(C)/(D), which explicitly permit a smooth forcing `f`) and an **unforced** Euler
`C¹` blowup. The famous open problem is the **unforced** Navier–Stokes case
(`f = 0`). A tweet (Palasek, [arXiv:2605.13827](https://arxiv.org/abs/2605.13827))
argues the forced→unforced upgrade is obstructed: an unforced lacunary cascade
has transfer `O(N^{3/2})` (by Bernstein + energy) which is beaten by dissipation
`N²`; the force is what overcomes dissipation. **Bernstein is exactly the tool in
that obstruction** — which is why it is Pillar A of the skeleton.
