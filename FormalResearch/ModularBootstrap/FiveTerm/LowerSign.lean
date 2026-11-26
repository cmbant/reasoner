module

public import FormalResearch.ModularBootstrap.FiveTerm.Constants
public import FormalResearch.ModularBootstrap.Bessel.VCorollaries

/-!
# The sign of the Virasoro constant term, `c_0^* < 0` (FIVE-L: `teb:quant_c1_near` is not needed at Virasoro)

Source: `CFT/modular_bootstrap/paper/constant_term_slit_strip.tex`, Theorem C9 (`cts:lower-main`) and
`cts:main`(3): `c_0^* = (3/(4√2))(1 + 2/π) ξ_* - 4 ξ_*² = -0.0713300993…`.

In the proof of `cts:lower-main` a violator has `ũ_1(g) > φ_c(a_1) > a_1` because `c_0^* < 0`; for a general weight
`c_0^*(w,Q)` may be `≥ 0` and the near-threshold remark `teb:quant_c1_near` replaces the violator form of `teb:quant_c1`.
At spinless Virasoro the sign is elementary:

* `c0Star_neg`: `c0Star < 0` (proved from `3/(4π) ≤ ξ_*` and `π + 2 < 4√2`, i.e. `c_0^* = ξ_* ((3/(4√2))(1+2/π) - 4ξ_*)`).

Unconditional; the decimal value is not claimed.
-/

@[expose] public section

open Real

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.ModularBootstrap

/-- **`c_0^* < 0` at spinless Virasoro.** -/
theorem c0Star_neg : c0Star < 0 := by
  have hpi := Real.pi_pos
  have hπ3 := Real.pi_lt_d2
  have hπ3' := Real.pi_gt_three
  have hξ : 3 / 4 ≤ π * xiStar := Bessel.three_quarters_le_pi_mul_xiStar
  have hξ0 := xiStar_pos
  have hs2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < √2 := Real.sqrt_pos.mpr (by norm_num)
  have hs : (14 / 10 : ℝ) ≤ √2 := by nlinarith only [hs2, hs0]
  -- `π + 2 < 4 √2`
  have hkey : π + 2 < 4 * √2 := by linarith only [hπ3, hs]
  unfold c0Star
  -- `c0Star = ξ ((3/(4√2))(1+2/π) - 4 ξ)` and `4 ξ ≥ 3/π > (3/(4√2))(1 + 2/π)`
  have h3π : 3 / π ≤ 4 * xiStar := by
    rw [div_le_iff₀ hpi]; nlinarith only [hξ]
  have hlt : 3 / (4 * √2) * (1 + 2 / π) < 3 / π := by
    have e : 3 / (4 * √2) * (1 + 2 / π) = 3 * (π + 2) / (4 * √2 * π) := by
      field_simp
    rw [e, div_lt_div_iff₀ (by positivity) hpi]
    nlinarith only [hkey, hpi, hs0]
  have hbr : 3 / (4 * √2) * (1 + 2 / π) - 4 * xiStar < 0 := by linarith only [hlt, h3π]
  have : 3 / (4 * √2) * (1 + 2 / π) * xiStar - 4 * xiStar ^ 2 =
      xiStar * (3 / (4 * √2) * (1 + 2 / π) - 4 * xiStar) := by ring
  rw [this]
  exact mul_neg_of_pos_of_neg hξ0 hbr

end FormalResearch.ModularBootstrap.FiveTerm

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.c0Star_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.c0Star_neg
