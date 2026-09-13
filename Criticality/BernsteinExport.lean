import Cascade.BernsteinGrowth
import Cascade.ConcentrationBarrier

/-!
# Pillar A re-export: Bernstein's inequality now lives in `Cascade`

Pillar A (`ConcentrationBarrier`, `Bernstein`, `BernsteinGrowth`) has been
**relocated to the `Cascade/` library**, where the declarations live under the
`Cascade` namespace. The `Criticality/` library depends on `Cascade` for
Bernstein's inequality, not the other way round.

This module keeps `Criticality`'s documented API intact: it re-exports the moved
declarations under the `Criticality` namespace so that names such as
`Criticality.bernstein` and `Criticality.bernstein_L2_to_Linf` still resolve with
the *same bodies* (and hence the same axioms) as their `Cascade` counterparts.

The re-export is a genuine `alias`, not a restatement: each `Criticality.<name>`
is definitionally the corresponding `Cascade.<name>`.
-/

namespace Criticality

alias fourierInv_apply_le_toLp_one := Cascade.fourierInv_apply_le_toLp_one
alias pointwise_le_L1_fourier := Cascade.pointwise_le_L1_fourier
alias norm_toLp_one_le_sqrt_measure_mul_norm_toLp_two :=
  Cascade.norm_toLp_one_le_sqrt_measure_mul_norm_toLp_two
alias bernstein := Cascade.bernstein
alias sqrt_volume_ball_eq_sqrt_volume_unitBall_mul :=
  Cascade.sqrt_volume_ball_eq_sqrt_volume_unitBall_mul
alias bernstein_L2_to_Linf := Cascade.bernstein_L2_to_Linf
alias abs_inner_mul_norm_le := Cascade.abs_inner_mul_norm_le
alias norm_toLp_one_fourier_lineDeriv_le := Cascade.norm_toLp_one_fourier_lineDeriv_le
alias bernstein_lineDeriv := Cascade.bernstein_lineDeriv
alias bernstein_gradient := Cascade.bernstein_gradient

end Criticality

#print axioms Criticality.bernstein_L2_to_Linf
#print axioms Criticality.bernstein
#print axioms Criticality.bernstein_gradient
