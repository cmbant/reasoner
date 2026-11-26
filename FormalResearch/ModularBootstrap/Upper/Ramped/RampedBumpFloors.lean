module

public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedRegionTwoGeom
public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedRegionTwoMacro

/-!
# The unbumped floors of the ramped comb (`fw:Ustar` Steps 4 and 5, `rem:thmU` Steps (3) and (4))

Source: `CFT/notes/n2_ramped_comb.tex`, Lemma `U*` (`rem:thmU`) Steps (3), (4) and Lemma `U*(w)` (`fw:Ustar`) Steps 4, 5:
the floor `h₀^{ramp}/Lev` of the ramped comb alone, with no amplitude and no Hankel transform (so it is independent of
the weight).  `RampedNearTip.lean`/`RampedMacro` of weight one state `2g/Lev ≥ floor - amp` for `twoG`; the bumped combs at weight `w`
need the floor itself, to which the bump factor `R_bump ≥ 1` is applied.

* `rampedD_nearTip_floor` (near tip, cells `N₀ ≤ n ≤ n_cap + 6`): `χ'_1 < x` and `c_fl min(1, 16 η_n²)(1 - ε) ≤ sech² ‖B_{D_*}(x)‖ / Lev`;
* `rampedMacro_floor` (macroscopic, cells `n ≥ n_cap + 7`): `ν Lev ≤ sech² ‖B_{D_*}(x)‖` with `ν = 0.7 · 0.998² · 0.999`
  (the loss `A + B` of `ramped_macro_margin` is made `≤ 0.002`, so `0.7 (1 - A - B) ≥ ν`).

These are the proofs of `rampedD_nearTip_twoG`, `rampedMacro` with the final amplitude step removed (the lemma underneath,
`ramped_hole_floor`, `ramped_macro_floor`, is already the floor).  All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real BigOperators

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.ModularBootstrap Upper.Comb Upper.Design Upper.Holes Upper.Positivity Upper.Hankel

/-- **Near-tip floor of `D_*`** (`rem:thmU` Step (3), the floor before the amplitude is subtracted): for fixed
`P` and `0 < ε ≤ 1` there are `N₀` and `c₀` such that for `c' ≥ c₀`, `d ∈ [0, 1]`, `N₀ ≤ n ≤ n_cap + 6`, `x` in the cell
`n` with `x ≥ ξ_* + c'^{-3/5}`: `c_fl min(1, 16 η_n²)(1 - ε) Lev ≤ sech²(πx/2) ‖B_{D_*}(x)‖`. -/
theorem rampedD_nearTip_floor (P : RampedParams) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ N0 : ℕ, ∀ᶠ c' : ℝ in atTop, ∀ (d : ℝ), 0 ≤ d → d ≤ 1 → ∀ (n : ℕ) (x : ℝ), N0 ≤ n →
      n ≤ nCap P c' + 6 → inCell c' n x → xiStar + c' ^ (-(3 / 5 : ℝ)) ≤ x →
      designSite c' (rampedSigma d c') 1 < x ∧
      cFl * min 1 (16 * rampedEta P c' n ^ 2) * (1 - ε) ≤
        (1 / Real.cosh (π * x / 2) ^ 2 * ‖rampedComb P d c' (x : ℂ)‖) / levComb c' 1 x := by
  obtain ⟨N₀', C, hC, hfl⟩ := ramped_hole_floor
  obtain ⟨Cκ, hCκ, hHole⟩ := rampedHoleHyp_D
  obtain ⟨C_S, hCS, N0s, hN0s, hshift⟩ := rampedShift_package
  obtain ⟨C_L, hCL, hLev⟩ := eLeftComb_bounds
  obtain ⟨cg, Cg, c0g, hcg, hCg, hc0g, hgap⟩ := rampedGap_two_sided
  set Mn := C + 3500 + 4 * C_S + 128 * Cκ ^ 2 + 70 * Cκ with hMn
  set Mc := C * Cg + 2 * C_L + C_S + 23 * Cg with hMc
  have hMn0 : 0 < Mn := by positivity
  have hMc0 : 0 < Mc := by positivity
  obtain ⟨N1, hN1⟩ : ∃ N1 : ℕ, ∀ n : ℕ, N1 ≤ n → 2 * Mn / ε ≤ (n : ℝ) ^ (2 / 3 : ℝ) := by
    have h := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp tendsto_natCast_atTop_atTop
    obtain ⟨N1, hN1⟩ := eventually_atTop.1 (h.eventually_ge_atTop (2 * Mn / ε))
    exact ⟨N1, fun n hn => hN1 n hn⟩
  obtain ⟨N2, hN2⟩ : ∃ N2 : ℕ, ∀ n : ℕ, N2 ≤ n → 98 * Cκ ≤ (n : ℝ) := by
    obtain ⟨N2, hN2⟩ := exists_nat_ge (98 * Cκ)
    exact ⟨N2, fun n hn => hN2.trans (by exact_mod_cast hn)⟩
  refine ⟨max (max (max N₀' N0s) (max N1 N2)) 8, ?_⟩
  filter_upwards [hLev, hfl, hHole P, hshift,
    eventually_ge_atTop (max (max c0g 10000) 1),
    eventually_lam_pow_le (q := 3 / 5) (by norm_num) (show 0 < min (ε / (2 * Mc)) (1 / Cg) by positivity),
    eventually_gt_atTop (0 : ℝ)]
    with c' hLev' hfl' hHole' hshift' hc' hlam hc'0 d hd hd1 n x hn hnc hcell hxξ
  have hc'1 : 1 ≤ c' := (le_max_right _ _).trans hc'
  have hc'4 : 10000 ≤ c' := (le_max_right _ _).trans ((le_max_left _ _).trans hc')
  have hcg' : c0g ≤ c' := (le_max_left _ _).trans ((le_max_left _ _).trans hc')
  have hn8 : 8 ≤ n := (le_max_right _ _).trans hn
  have hnA : max N₀' N0s ≤ n := (le_max_left _ _).trans ((le_max_left _ _).trans hn)
  have hnB : max N1 N2 ≤ n := (le_max_right _ _).trans ((le_max_left _ _).trans hn)
  have hnN₀ : N₀' ≤ n := (le_max_left _ _).trans hnA
  have hnN0s : N0s ≤ n := (le_max_right _ _).trans hnA
  have hnN1 : N1 ≤ n := (le_max_left _ _).trans hnB
  have hnN2 : N2 ≤ n := (le_max_right _ _).trans hnB
  have hl := lambdaComb_pos' hc'0
  have hnr : (8 : ℝ) ≤ n := by exact_mod_cast hn8
  have hn0 : (0 : ℝ) < n := by linarith
  have hT : 1 ≤ c' ^ (3 / 5 : ℝ) := Real.one_le_rpow hc'1 (by norm_num)
  set μ := lambdaComb c' * c' ^ (3 / 5 : ℝ) with hμ
  have hμ0 : 0 ≤ μ := by positivity
  have hμa : μ ≤ ε / (2 * Mc) := hlam.trans (min_le_left _ _)
  have hμb : μ ≤ 1 / Cg := hlam.trans (min_le_right _ _)
  have hCgμ : Cg * μ ≤ 1 := by
    have := (le_div_iff₀ hCg).1 hμb
    linarith
  have hlmu : lambdaComb c' ≤ μ := by
    have : lambdaComb c' * 1 ≤ lambdaComb c' * c' ^ (3 / 5 : ℝ) := mul_le_mul_of_nonneg_left hT hl.le
    linarith
  obtain ⟨hdx1, hdxk, hS⟩ := hshift' P d hd hd1 n x hnN0s hnc hcell hxξ
  have hH := hHole' d hd hd1 n hn8 (by omega)
  have hxs : xiStar < x := by
    have : 0 < c' ^ (-(3 / 5 : ℝ)) := by positivity
    linarith
  -- e_L
  have heL : eLeftComb c' 1 n 4 x ≤ C_L * μ := by
    obtain ⟨-, hb⟩ := hLev' 1 n 4 x le_rfl hxs
    refine hb.trans ?_
    have hx' : c' ^ (-(3 / 5 : ℝ)) ≤ x - xiStar := by linarith
    have hT0 : 0 < c' ^ (-(3 / 5 : ℝ)) := by positivity
    rw [div_le_iff₀ (by linarith)]
    have hinv : c' ^ (3 / 5 : ℝ) * c' ^ (-(3 / 5 : ℝ)) = 1 := by
      rw [← Real.rpow_add hc'0]; norm_num
    calc C_L * lambdaComb c' = C_L * lambdaComb c' * (c' ^ (3 / 5 : ℝ) * c' ^ (-(3 / 5 : ℝ))) := by
          rw [hinv, mul_one]
      _ = C_L * μ * c' ^ (-(3 / 5 : ℝ)) := by rw [hμ]; ring
      _ ≤ C_L * μ * (x - xiStar) := mul_le_mul_of_nonneg_left hx' (by positivity)
  -- ℓ_n
  have hℓ : siteGap c' n ≤ Cg * μ := by
    obtain ⟨-, hu⟩ := hgap P c' hcg' n (by omega) (by omega)
    refine hu.trans ?_
    have h1 : (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
    calc Cg * lambdaComb c' * (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ Cg * lambdaComb c' * 1 := by gcongr
      _ ≤ Cg * μ := by rw [mul_one]; exact mul_le_mul_of_nonneg_left hlmu hCg.le
  have hℓ0 : 0 ≤ siteGap c' n := siteGap_nonneg hc'0 (by omega)
  have hlossle : rampedHoleLoss C (siteGap c' n) (C_L * μ) (C_S * ((n : ℝ) ^ (-(2 / 3 : ℝ)) + Real.log n / n) +
      C_S * μ) (Cκ / n) (n : ℝ) ≤ Mn * (n : ℝ) ^ (-(2 / 3 : ℝ)) + Mc * μ :=
    rampedHoleLoss_le hC hCg hCκ hCS hCL hn8 hℓ0 hℓ hCgμ hμ0 le_rfl le_rfl rfl
  have hn23 : 2 * Mn / ε ≤ (n : ℝ) ^ (2 / 3 : ℝ) := hN1 n hnN1
  have hq : (n : ℝ) ^ (-(2 / 3 : ℝ)) * (n : ℝ) ^ (2 / 3 : ℝ) = 1 := by
    rw [← Real.rpow_add hn0]; norm_num
  have hqpos : 0 < (n : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hn0 _
  have hA : Mn * (n : ℝ) ^ (-(2 / 3 : ℝ)) ≤ ε / 2 := by
    have h := (div_le_iff₀ hε).1 hn23
    have h1 : (n : ℝ) ^ (-(2 / 3 : ℝ)) * (2 * Mn) ≤ (n : ℝ) ^ (-(2 / 3 : ℝ)) * ((n : ℝ) ^ (2 / 3 : ℝ) * ε) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    have h2 : (n : ℝ) ^ (-(2 / 3 : ℝ)) * ((n : ℝ) ^ (2 / 3 : ℝ) * ε) = ε := by
      rw [← mul_assoc, hq, one_mul]
    linarith
  have hB : Mc * μ ≤ ε / 2 := by
    have := (le_div_iff₀ (by positivity)).1 hμa
    linarith
  have hE : rampedHoleLoss C (siteGap c' n) (C_L * μ) (C_S * ((n : ℝ) ^ (-(2 / 3 : ℝ)) + Real.log n / n) +
      C_S * μ) (Cκ / n) (n : ℝ) ≤ ε := by
    refine hlossle.trans ?_
    linarith
  have hκ0 : 0 ≤ Cκ / (n : ℝ) := by positivity
  have hκ98 : Cκ / (n : ℝ) ≤ 1 / 98 := by
    have := hN2 n hnN2
    rw [div_le_div_iff₀ hn0 (by norm_num)]
    linarith
  have hcore := hfl' 1 (nCap P c' + 6) n x (rampedSigma d c') (rampedEta P c') (Cκ / n) (C_L * μ)
    (C_S * ((n : ℝ) ^ (-(2 / 3 : ℝ)) + Real.log n / n) + C_S * μ) le_rfl (by omega) hnN₀ (by omega) hcell
    hH hκ0 hκ98 (by positivity) hdx1.ne hdxk
    (fun k hk1 hkN hk => Or.inr (rampedEta_pos P hc'0 (by omega))) heL hS (hE.trans hε1)
  have hmin : 0 ≤ cFl * min 1 (16 * rampedEta P c' n ^ 2) := by
    have := cFl_gt
    refine mul_nonneg (by linarith) (le_min zero_le_one (by positivity))
  have hlo : cFl * min 1 (16 * rampedEta P c' n ^ 2) * (1 - ε) ≤
      cFl * min 1 (16 * rampedEta P c' n ^ 2) *
        (1 - rampedHoleLoss C (siteGap c' n) (C_L * μ) (C_S * ((n : ℝ) ^ (-(2 / 3 : ℝ)) + Real.log n / n) +
          C_S * μ) (Cκ / n) (n : ℝ)) :=
    mul_le_mul_of_nonneg_left (by linarith) hmin
  exact ⟨hdx1, hlo.trans hcore⟩

/-- The arithmetic of the macroscopic floor: with `A, B ≥ 0` and `A + B ≤ 1/500`,
`ν ≤ μ₄ (1 - A) e^{-B}` where `μ₄ > 0.7` and `ν = 0.7 · 0.998² · 0.999`. -/
lemma macro_floor_arith {A B : ℝ} (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hE : A + B ≤ 1 / 500) :
    (7 / 10 : ℝ) * (998 / 1000) * (998 / 1000) * (999 / 1000) ≤
      muHole 4 (1 / 4) * (1 - A) * Real.exp (-B) := by
  have hμ := muHole_four_quarter_gt
  have hexp := Real.add_one_le_exp (-B)
  have hA' : 0 ≤ 1 - A := by linarith only [hE, hB0]
  have h1' : (1 - A) * (1 - B) ≤ (1 - A) * Real.exp (-B) :=
    mul_le_mul_of_nonneg_left (by linarith only [hexp]) hA'
  have h2' : 1 - (A + B) ≤ (1 - A) * (1 - B) := by nlinarith only [mul_nonneg hA0 hB0]
  have hμ0 : 0 ≤ muHole 4 (1 / 4) := by linarith only [hμ]
  have hE0 : 0 ≤ 1 - (A + B) := by linarith only [hE]
  have h3 : (7 / 10 : ℝ) * (1 - (A + B)) ≤ muHole 4 (1 / 4) * ((1 - A) * Real.exp (-B)) :=
    calc (7 / 10 : ℝ) * (1 - (A + B)) ≤ muHole 4 (1 / 4) * (1 - (A + B)) :=
          mul_le_mul_of_nonneg_right hμ.le hE0
      _ ≤ muHole 4 (1 / 4) * ((1 - A) * Real.exp (-B)) :=
          mul_le_mul_of_nonneg_left (h2'.trans h1') hμ0
  have h4 : (7 / 10 : ℝ) * (998 / 1000) * (998 / 1000) * (999 / 1000) ≤ (7 / 10 : ℝ) * (1 - (A + B)) := by
    nlinarith only [hE]
  calc _ ≤ (7 / 10 : ℝ) * (1 - (A + B)) := h4
    _ ≤ _ := h3
    _ = _ := by ring

/-- **Macroscopic floor of `D_*`** (`rem:thmU` Step (4), the floor before the amplitude is subtracted): for every
parameter set `P` and `c'` large, `d ∈ [0, 1]` and every `x` in a reference cell `n ≥ n_cap + 7`,
`ν Lev ≤ sech²(πx/2) ‖B_{D_*}(x)‖`, `ν = 0.7 · 0.998² · 0.999`. -/
theorem rampedMacro_floor (P : RampedParams) :
    ∀ᶠ c' : ℝ in atTop, ∀ d : ℝ, 0 ≤ d → d ≤ 1 → ∀ (n : ℕ) (x : ℝ), nCap P c' + 7 ≤ n →
      inCell c' n x → designSite c' (rampedSigma d c') 1 < x ∧
      (7 / 10 : ℝ) * (998 / 1000) * (998 / 1000) * (999 / 1000) * levComb c' 1 x ≤
        1 / Real.cosh (π * x / 2) ^ 2 * ‖rampedComb P d c' (x : ℂ)‖ := by
  obtain ⟨N₀, Cm, -, hCm, hfl⟩ := ramped_macro_floor
  obtain ⟨Cs, hCs, hsh⟩ := rampedShift_le
  obtain ⟨CL, hCL, hLev⟩ := eLeftComb_bounds
  obtain ⟨Cg, hCg, hgev⟩ := siteGap_eventually_le
  have hCmid : 0 < P.Cmid ^ 2 := by have := P.one_le_Cmid; positivity
  have hs : 0 < (1 / (32 * P.Cmid ^ 2)) ^ (6 / 5 : ℝ) := by positivity
  obtain ⟨r, hr, hrr⟩ := siteRadius_ge_const hs
  obtain ⟨Sc, hSc⟩ : ∃ Sc : ℝ, Sc = 7 * (4 / r + π) * Cs := ⟨_, rfl⟩
  have hSc0 : 0 ≤ Sc := by have := Real.pi_pos; rw [hSc]; positivity
  obtain ⟨ε0, hε0⟩ : ∃ ε0 : ℝ, ε0 = min (min ((1 / 16) / (Cg + 1)) ((r / 4) / (Cs + 1)))
    ((1 / 1000) / (Cm * Cg + 2 * CL / r + Sc + 1)) := ⟨_, rfl⟩
  have hε0pos : 0 < ε0 := by
    rw [hε0]; exact lt_min (lt_min (by positivity) (by positivity)) (by positivity)
  filter_upwards [hfl, hgev, hLev, nCap_ge P, eventually_nAi_le_nCap P,
    eventually_siteRadius_nAi_le (show 0 < r / 4 by positivity),
    hrr, eventually_lam_pow_le (q := 0) (by norm_num) hε0pos,
    eventually_ge_atTop ((1000 * Cm + N₀) / (1 / (32 * P.Cmid ^ 2)) ^ (6 / 5 : ℝ)),
    eventually_gt_atTop (1 : ℝ)]
    with c' hfl' hg hL hcap hAi hrad hrc hlam hcs hc'1 d hd hd1 n x hn hcell
  have hc'0 : 0 < c' := by linarith
  have hl := lambdaComb_pos' hc'0
  have hlam' : lambdaComb c' ≤ ε0 := by simpa using hlam
  have hn1 : 1 ≤ n := by omega
  have hnr : (1 / (32 * P.Cmid ^ 2)) ^ (6 / 5 : ℝ) * c' ≤ n := by
    have h2 : (nCap P c' : ℝ) ≤ n := by exact_mod_cast (by omega : nCap P c' ≤ n)
    linarith
  have hcs' : 1000 * Cm + N₀ ≤ (1 / (32 * P.Cmid ^ 2)) ^ (6 / 5 : ℝ) * c' := by
    have := (div_le_iff₀ hs).1 hcs
    linarith
  have hN₀ : N₀ ≤ n := by
    have : (N₀ : ℝ) ≤ n := by linarith [hCm.le]
    exact_mod_cast this
  have hxr : r ≤ x - xiStar := by
    have h1 := hrc (n : ℝ) hnr
    unfold siteRadius at h1
    linarith [hcell.1]
  have hxs : xiStar < x := by linarith
  have hnAi1 := one_le_nAi hc'1.le
  -- small parameters
  have hlam_a : Cg * lambdaComb c' ≤ 1 / 16 := by
    refine mul_le_of_le_div_succ hCg.le hl.le (by norm_num) ?_
    rw [hε0] at hlam'; exact hlam'.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hlam_b : Cs * lambdaComb c' ≤ r / 4 := by
    refine mul_le_of_le_div_succ hCs.le hl.le (by positivity) ?_
    rw [hε0] at hlam'; exact hlam'.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hlam_c : (Cm * Cg + 2 * CL / r + Sc) * lambdaComb c' ≤ 1 / 1000 := by
    refine mul_le_of_le_div_succ (by positivity) hl.le (by norm_num) ?_
    rw [hε0] at hlam'; exact hlam'.trans (min_le_right _ _)
  -- the sites below the Airy cut
  have hnear : ∀ k : ℕ, 1 ≤ k → k ≤ nAi c' →
      designSite c' (rampedSigma d c') k + r / 2 ≤ x ∧ r / 2 ≤ |x - chiQuantile c' (k : ℝ)| := by
    intro k hk hkn
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hkp : (k : ℝ) ^ (-(4 / 3 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hk1 (by norm_num)
    have hΔ : |designSite c' (rampedSigma d c') k - chiQuantile c' (k : ℝ)| ≤ r / 4 := by
      refine (hsh c' hc'0 d hd hd1 k hk).trans ?_
      calc Cs * lambdaComb c' * (k : ℝ) ^ (-(4 / 3 : ℝ)) ≤ Cs * lambdaComb c' * 1 :=
            mul_le_mul_of_nonneg_left hkp (by positivity)
        _ ≤ r / 4 := by linarith
    have hχ := hrad k hk hkn
    unfold siteRadius at hχ
    exact near_aux hr hΔ hχ hxr
  obtain ⟨hfx, hout⟩ := macro_out P hc'0 hnAi1 hn1 hcell (fun k a b => (hnear k a b).1) hr
  have hS := macro_shiftCost P hc'0 hd hr hCs.le hnAi1 hn1 hcell hxs.le (fun k a b => (hnear k a b).2)
    (fun k hk => hsh c' hc'0 d hd hd1 k hk) hlam_b
  have hHole := macro_holeHyp P hc'0 hd hAi hn
  have hη14 := macro_eta14 P hc'0 hn
  have heL : eLeftComb c' 1 n 4 x ≤ CL * lambdaComb c' / r := by
    refine (hL 1 n 4 x le_rfl hxs).2.trans ?_
    exact div_le_div_of_nonneg_left (by positivity) hr hxr
  have heL0 : 0 ≤ CL * lambdaComb c' / r := by positivity
  have hgap : siteGap c' n ≤ Cg * lambdaComb c' := by
    obtain ⟨g1, g2, g3, -⟩ := hg
    exact (g1 n hn1).trans (g2.trans g3)
  have hgap16 : siteGap c' n ≤ 1 / 16 := hgap.trans hlam_a
  have hlev := levComb_pos c' 1 x
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn1
  have hA0 : 0 ≤ Cm * (1 / (n : ℝ) + siteGap c' n) := by
    have : 0 ≤ siteGap c' n := siteGap_nonneg hc'0 hn1
    positivity
  have h1 : Cm * (1 / (n : ℝ)) ≤ 1 / 1000 := by
    rw [← div_eq_mul_one_div, div_le_iff₀ hn0]
    have : 1000 * Cm ≤ (1 / (32 * P.Cmid ^ 2)) ^ (6 / 5 : ℝ) * c' := by
      have : (0 : ℝ) ≤ N₀ := Nat.cast_nonneg N₀
      linarith
    linarith
  have h2 : Cm * siteGap c' n ≤ Cm * Cg * lambdaComb c' := by
    have := mul_le_mul_of_nonneg_left hgap hCm.le
    linarith
  have h3 : 2 * (CL * lambdaComb c' / r) = 2 * CL / r * lambdaComb c' := by ring
  have h4 : Cm * (1 / (n : ℝ) + siteGap c' n) = Cm * (1 / (n : ℝ)) + Cm * siteGap c' n := by ring
  have h5 : (Cm * Cg + 2 * CL / r + Sc) * lambdaComb c' =
      Cm * Cg * lambdaComb c' + 2 * CL / r * lambdaComb c' + Sc * lambdaComb c' := by ring
  have hS' : holeShiftCost c' x (rampedSigma d c') 1 (nCap P c' + 6) n 4 ≤ Sc * lambdaComb c' := by
    rw [hSc]; linarith [hS]
  have hp1 : 0 ≤ 2 * CL / r * lambdaComb c' := by positivity
  have hp2 : 0 ≤ Sc * lambdaComb c' := by positivity
  have hE1 : Cm * (1 / (n : ℝ) + siteGap c' n) ≤ 1 := by linarith
  have hmain := hfl' 1 (nCap P c' + 6) n x (rampedSigma d c') (rampedEta P c') (CL * lambdaComb c' / r)
    (Sc * lambdaComb c') le_rfl (by omega) hN₀ (by omega) hcell hHole hη14 heL0 hfx.ne hout heL hS' hgap16 hE1
  have hB0 : 0 ≤ 2 * (CL * lambdaComb c' / r) + Sc * lambdaComb c' := by positivity
  have hAB : Cm * (1 / (n : ℝ) + siteGap c' n) + (2 * (CL * lambdaComb c' / r) + Sc * lambdaComb c') ≤ 1 / 500 := by
    linarith
  have harith := macro_floor_arith hA0 hB0 hAB
  have hfin : (7 / 10 : ℝ) * (998 / 1000) * (998 / 1000) * (999 / 1000) ≤
      (1 / Real.cosh (π * x / 2) ^ 2 * ‖designComb c' 1 (nCap P c' + 6) (1 / 4) (rampedSigma d c')
        (fun k => rampedEta P c' k * siteGap c' k) (x : ℂ)‖) / levComb c' 1 x :=
    harith.trans hmain
  rw [le_div_iff₀ hlev] at hfin
  exact ⟨hfx, hfin⟩

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.rampedD_nearTip_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rampedD_nearTip_floor

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.rampedMacro_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rampedMacro_floor

end FormalResearch.ModularBootstrap.Upper.Ramped
