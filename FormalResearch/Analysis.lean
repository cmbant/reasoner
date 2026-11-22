module

public import FormalResearch.Analysis.VanDerCorput
public import FormalResearch.Analysis.Scheffe

/-!
# Real and measure-theoretic analysis

General-purpose analysis helpers used across programmes (`namespace FormalResearch.Analysis`):

* `VanDerCorput`: integration-by-parts BV bound and first- and second-derivative van der Corput
  oscillatory integral estimates (`norm_integral_mul_deriv_le_of_boundedVariation`,
  `van_der_corput_first`, `van_der_corput_second`).
* `Scheffe`: Generalized Scheffé lemma for `NormedAddCommGroup`-valued Bochner integrals along a
  countably generated filter (`tendsto_integral_norm_sub_of_tendsto_ae`).
-/
