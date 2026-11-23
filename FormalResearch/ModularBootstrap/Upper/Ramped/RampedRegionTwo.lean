module

public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedRegionTwoNear
public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedRegionTwoMacro

/-!
# Region II of Lemma U* for the ramped comb (`rem:thmU` Steps (3) and (4))

Source: `CFT/notes/n2_ramped_comb.tex`, Lemma U* (`rem:thmU`), Steps (3) (near-tip Region II, `ξ_I ≤ x ≤ χ'_{n_cap+6}`)
and (4) (macroscopic Region II, `x ≥ χ'_{n_cap+6}`).

`rampedRegionII`: there is `C_mid ≥ 1` such that for every parameter set `P : RampedParams` with `P.C_mid = C_mid` (any
`C_I ≥ 1`, any `M_0 > 0`) and `c'` large (the threshold depends on `P`, i.e. on `C_I` and `C_mid`, and not on `d` or
`M_0`), every `d ∈ [0, 1]` (in particular `d ≤ d_0 = min(1, (a_1 - a_2)/8)`, `rampedD0`) and every `x ≥ ξ_I = ξ_* + c'^{-3/5}`,
`0 < twoG c' 1 (n_cap + 6) (1/4) σ ε' x`, i.e. `2 g(c' x²/3) = (h_0 - ĥ_0)(x) > 0` for the test function `g` of the ramped
design `D_*` (`rampedComb`, `rampedSigma`, `rampedEps`; `designProfile = sech² B_{D_*}`, `edgeHankel` the order-zero
Hankel transform in `t = c' x²/3`).

**Order of constants.**  The paper fixes `C_I` (Region I), then `C_mid` (Step 3), then `M_0` (vacuum), and finally `c_0`.
The statement is stronger in that `C_mid` does not depend on `C_I` at all: it is determined by the absolute
constants `C_v` (`nearTip_amp_le`) and `c_fl` (`cFl`) through `C_mid² = max(1, C_2/(4 c_fl))`, `C_2 = C_v (2/k_tip)^{5/6}`
(the paper's requirement `C_mid² ≥ C_2/(8 c_fl)` with room to spare); `M_0` does not enter Region II (`σ`, `ε'` depend
on `d`, `C_I`, `C_mid` only), and `c_0` depends on `(C_I, C_mid)` only.

* range split: the reference cell `n` of `x` (`exists_cell_of_xiI`, `n ≥ N₀`) is either `n ≤ n_cap + 6`
  (`rampedNearTip`: `rampedD_nearTip_twoG` + `ramped_phase_package` (θ = 3/5) + `nearTip_amp_le` + `nearTip_gap_pos`)
  or `n ≥ n_cap + 7` (`rampedMacro`: `ramped_macro_margin`, `ρ_k = 1` on the hole, `S = O(λ)`).

**What R8 (assembly) consumes**: `rampedRegionII` (pick `C_mid`; `P` then has `C_I` from Region I and `M_0` from the
vacuum step; the `c'`-threshold of Region II joins the others).  Combined with `ramped_k7` (`g ∈ Ā`, `g_vac`), the
Region I statement of R5 (`t ≤ t(ξ_I)`) and `rampedVacuum` of R7, it gives `g > 0` for `t ≥ t_* + 1`.

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.ModularBootstrap Upper.Comb Upper.Design Upper.Holes Upper.Positivity

/-- **Region II of Lemma U\*** (`rem:thmU` Steps (3), (4)): positivity of `2g` for all `x ≥ ξ_I`, for the ramped
design with `C_mid` fixed independently of `C_I`, uniformly in `d ∈ [0, 1]` and `M_0`. -/
theorem rampedRegionII : ∃ Cmid : ℝ, 1 ≤ Cmid ∧ ∀ P : RampedParams, P.Cmid = Cmid →
    ∀ᶠ c' : ℝ in atTop, ∀ d : ℝ, 0 ≤ d → d ≤ 1 → ∀ x : ℝ, xiStar + c' ^ (-(3 / 5 : ℝ)) ≤ x →
      0 < twoG c' 1 (nCap P c' + 6) (1 / 4) (rampedSigma d c') (rampedEps P c') x := by
  obtain ⟨Cmid, hCmid, hnear⟩ := rampedNearTip
  refine ⟨Cmid, hCmid, fun P hP => ?_⟩
  obtain ⟨N0, hN⟩ := hnear P hP
  filter_upwards [hN, rampedMacro P, exists_cell_of_xiI (max N0 1) (le_max_right _ _)]
    with c' hn hm hcell d hd hd1 x hx
  obtain ⟨n, hnM, hc⟩ := hcell x hx
  by_cases h : n ≤ nCap P c' + 6
  · exact hn d hd hd1 n x ((le_max_left _ _).trans hnM) h hc hx
  · exact hm d hd hd1 n x (by omega) hc

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.rampedRegionII' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rampedRegionII

end FormalResearch.ModularBootstrap.Upper.Ramped
