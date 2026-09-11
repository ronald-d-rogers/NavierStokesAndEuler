import Mathlib.Analysis.Fourier.Convolution

set_option maxHeartbeats 1000000

/-!
# Additive coupling: multiplication in space = convolution in frequency (Pillar B, rung B2)

This module formalizes the Fourier **convolution theorem** over Schwartz space
`𝓢(V, ℂ)`: the frequency `ω` of a pointwise product is fed by *every* pair
`(ξ, η)` with `ξ + η = ω`. This is the *additive* interaction that stands in
tension with the *multiplicative* dyadic grouping of Pillar B1 (and, by analogy,
the additive Dirichlet series vs the multiplicative Euler product of Pillar E).

In mathlib's normalization (`𝐞 x = exp (2π i x)`, so `𝓕 f ω = ∫ v, 𝐞(-⟪v,ω⟫) • f v`
with *no* `(2π)^d` prefactor) both directions hold with constant `1`:

* `𝓕 (f ⋆ g) = (𝓕 f) · (𝓕 g)`  — convolution in space is a pointwise product in
  frequency (this is mathlib's `SchwartzMap.fourier_convolution`, stated here as
  `fourier_convolution_eq_pairing`);
* `𝓕 (f · g) = (𝓕 f) ⋆ (𝓕 g)`  — pointwise multiplication in space is convolution
  in frequency (stated and proved here as `fourier_mul_eq_convolution`, via Fourier
  inversion).

The pointwise form `fourier_mul_apply_eq_integral` is the "all-to-all" statement:
`𝓕 (f · g) ω = ∫ η, (𝓕 f η) · (𝓕 g (ω - η))`, where the integrand is indexed by
pairs `(η, ω - η)` whose sum is exactly `ω`.

Because Schwartz maps do not carry a `Mul` instance in mathlib, the pointwise
product is written `SchwartzMap.pairing (mul ℂ ℂ) f g`, whose value at `x` is
`(mul ℂ ℂ) (f x) (g x) = f x * g x` (`SchwartzMap.pairing_apply_apply`).
-/

noncomputable section

open Real MeasureTheory
open scoped FourierTransform SchwartzMap Topology
open ContinuousLinearMap

-- The Schwartz Fourier transform unfolds into a huge `mkCLM` construction; keep it opaque
-- so that elaborating `𝓕 f` in proofs does not trigger a heartbeat explosion. `[local
-- irreducible]` attributes do NOT propagate across imports, so this is re-declared here.
attribute [local irreducible] Real.rpow
attribute [local irreducible] SchwartzMap.fourierTransformCLM

namespace Criticality

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- The inverse Fourier transform evaluates to the Fourier transform at the negated
argument: `𝓕⁻ f x = 𝓕 f (-x)`. This is the reflection built into mathlib's `2π`
normalization. -/
lemma fourierInv_apply_eq_neg (f : 𝓢(V, ℂ)) (x : V) : 𝓕⁻ f x = 𝓕 f (-x) := by
  rw [SchwartzMap.fourierInv_apply_eq]
  rfl

/-- Fourier inversion as a *reflection*: applying `𝓕` twice sends `f` to `f ∘ neg`,
i.e. `𝓕 (𝓕 f) x = f (-x)`. (In mathlib's normalization `𝓕²` is the reflection, not
the identity; the identity is `𝓕⁻ ∘ 𝓕`, see `fourierInv_fourier_eq`.) -/
lemma fourier_fourier_apply (f : 𝓢(V, ℂ)) (x : V) : 𝓕 (𝓕 f) x = f (-x) := by
  have h : (𝓕⁻ (𝓕 f)) (-x) = f (-x) :=
    congrArg (fun g : 𝓢(V, ℂ) => g (-x)) (FourierTransform.fourierInv_fourier_eq f)
  rw [← h]
  rw [fourierInv_apply_eq_neg (𝓕 f) (-x)]
  simp

/-- The Schwartz Fourier transform is injective (it is in fact a linear equivalence,
with inverse `𝓕⁻`). -/
lemma fourier_injective : Function.Injective (𝓕 : 𝓢(V, ℂ) → 𝓢(V, ℂ)) := by
  intro a b h
  have h' := congrArg (𝓕⁻ : 𝓢(V, ℂ) → 𝓢(V, ℂ)) h
  simpa using h'

/-- **Convolution in space = pointwise product in frequency** (mathlib's direction).

`𝓕 (f ⋆ g) = (𝓕 f) · (𝓕 g)`, where `⋆` is `SchwartzMap.convolution (mul ℂ ℂ)` and
`·` is the pointwise pairing `SchwartzMap.pairing (mul ℂ ℂ)`. This is literally
mathlib's `SchwartzMap.fourier_convolution`; it is restated here under the scalar
multiplication pairing so it matches the `mul ℂ ℂ` convention used throughout B2. -/
theorem fourier_convolution_eq_pairing (f g : 𝓢(V, ℂ)) :
    𝓕 (SchwartzMap.convolution (mul ℂ ℂ) f g) = SchwartzMap.pairing (mul ℂ ℂ) (𝓕 f) (𝓕 g) := by
  exact SchwartzMap.fourier_convolution (mul ℂ ℂ) f g

/-- **Multiplication in space = convolution in frequency** (the B2 statement).

`𝓕 (f · g) = (𝓕 f) ⋆ (𝓕 g)`, where `f · g` is the pointwise product
`SchwartzMap.pairing (mul ℂ ℂ) f g` and `⋆` is `SchwartzMap.convolution (mul ℂ ℂ)`.

This is the inverse of `fourier_convolution_eq_pairing`. Proof: since `𝓕` is injective
it suffices to show the two sides have equal Fourier transforms; the right-hand side's
transform is `(𝓕 (𝓕 f)) · (𝓕 (𝓕 g)) = (f ∘ neg) · (g ∘ neg)` by
`fourier_convolution`, while the left-hand side's transform is `(f · g) ∘ neg` by the
reflection `fourier_fourier_apply`; the two agree pointwise. -/
theorem fourier_mul_eq_convolution (f g : 𝓢(V, ℂ)) :
    𝓕 (SchwartzMap.pairing (mul ℂ ℂ) f g) = SchwartzMap.convolution (mul ℂ ℂ) (𝓕 f) (𝓕 g) := by
  apply fourier_injective
  rw [SchwartzMap.fourier_convolution (mul ℂ ℂ) (𝓕 f) (𝓕 g)]
  ext x
  simp [fourier_fourier_apply, SchwartzMap.pairing_apply_apply]

/-- **The all-to-all additive interaction, pointwise.**

`𝓕 (f · g) ω = ∫ η : V, (𝓕 f η) · (𝓕 g (ω - η))`. The right-hand side is an integral
over *every* `η`, and the pair `(η, ω - η)` appearing in the integrand always satisfies
`η + (ω - η) = ω`: the frequency `ω` is fed by *all* pairs whose frequencies sum to `ω`.
This is the quantitative form of the "additive vs multiplicative" tension — the
nonlinearity couples frequencies additively, while Pillar B1 groups them
multiplicatively (dyadic octaves). -/
theorem fourier_mul_apply_eq_integral (f g : 𝓢(V, ℂ)) (ω : V) :
    𝓕 (SchwartzMap.pairing (mul ℂ ℂ) f g) ω = ∫ η : V, (𝓕 f η) * (𝓕 g (ω - η)) := by
  rw [fourier_mul_eq_convolution f g]
  rw [SchwartzMap.convolution_apply]
  rw [MeasureTheory.convolution_def]
  rfl

end Criticality

#print axioms Criticality.fourier_convolution_eq_pairing
#print axioms Criticality.fourier_mul_eq_convolution
#print axioms Criticality.fourier_mul_apply_eq_integral
