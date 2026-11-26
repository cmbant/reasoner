module

public import FormalResearch.SignUncertainty.UctCeBandRef
public import FormalResearch.SignUncertainty.UctCePreedgeAux
public import FormalResearch.SignUncertainty.UctCeBandFarRef
public import FormalResearch.SignUncertainty.UctCeBandFar
public import FormalResearch.SignUncertainty.UctCeBandAiry

/-!
# `uct:ce-band` / `uct:ce-preedge`: Auxiliary Fourier-edge and pre-edge estimates for `H_CE` multipliers

Source: `CFT/sign_uncertainty/paper/constant_terms_upper.tex`, Lemma `uct:ce-band` (also labelled
`uct:ce-preedge`, F2b leaf), used by Propositions `fct:ce-band` and `fct:ce-preedge` in
`CFT/sign_uncertainty/paper/constant_terms_five.tex`.

All parts of the lemma are proved unconditionally:
* **Part (1a), reference identity `(uct:hhat-ref-id)`** (`UctCeBandRef`):
  `airySquare_fourier_ref_general` (also serving `(fct:hhat-ref-cfu)`) and `uct_hhat_ref_id`.
* **Part (1b), Airy-window lower bound** (`UctCeBandAiry`):
  `half_disc_zero_of_real_segment_zero`, `uct_hhat_ref_shifted`, and `uct_ce_band_airy`
  (`-U ≤ c^{2/3} L / π² ≤ S_w`, `h_norm^{ĥ}(L)` real and `≥ -C_U c^{-4/3}`).
* **Part (1c), global `O(c^{-1/2})` bound and far-band asymptotic** (`UctCeBandFarRef`, `UctCeBandFar`):
  `uct_ce_band_global_bound`, `regSqrt_cutoff_fourier`, `uct_ce_band_far` (arbitrary `A(0)`),
  and `uct_ce_band_far_unit` (`A(0) = 1`).
* **Part (2a), auxiliary pre-edge floor `T₄ = T₄⁺ - T₄⁻`** (`UctCePreedgeAux`):
  `uct_ce_preedge_T4_pos` and `uct_ce_preedge_T4_neg`.
* **Part (2b), `(iy)^{1/2}` origin inversion `(uct:sqrt-iy-inv)`** (`UctCePreedgeAux`):
  `cpow_half_I_mul_eq_integral` and `uct_sqrt_iy_inv`.
-/
