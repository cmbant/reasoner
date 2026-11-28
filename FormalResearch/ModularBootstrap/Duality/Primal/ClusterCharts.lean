module

public import FormalResearch.ModularBootstrap.Upper.Rigidity.SpectrumCorollary
public import FormalResearch.ModularBootstrap.Rigidity.AiryRigidity
public import FormalResearch.ModularBootstrap.Blowup.NormLimitConcrete
public import FormalResearch.ModularBootstrap.Duality.Primal.Attainment
public import FormalResearch.Special.AiryZeroOrder

/-!
# Chart comparisons, Cardy prefactor asymptotics, and HB extremal zeros for PA2

Shared infrastructure for `dsl:hb-clusters`, `dsl:one-level-clusters`, `dsl:hb-mass`,
and `dsl:near-opt-mass` (`dual_spectrum_limit.tex`, Section 5.1):

* **Chart comparisons** (`uAiry` vs `virasoroDeltaChart` / `chartUT`):
  `virasoroDeltaChart_sub_linear`, `uAiry_virasoroDeltaChart_err`,
  `chartUT_sub_uAiry_err`, `virasoroDeltaChart_deriv_abs_bounds`,
  `tendsto_position_of_uAiry`, `tendsto_uAiry_of_position`.
* **Cardy + Jacobian asymptotics**:
  - `cardyV_mul_jAiry_asymp`: for any `t_n` with `(t_n - ξ̄ c_n) / c_n^{1/3} → -c_* z`,
    putting `b_n = t_n - ξ̄ c_n + c_* z c_n^{1/3}`,
    `2π V(c_n/12, t_n) J_{c_n}(t_n)` matches
    `(2 √ξ_* (2 ξ_*)^{w-1} Q(e^{-4π ξ_*}) / (√3 β)) c_n^{-1/6} exp((2/3) arsinh(1) c_n - (2π z/(3β)) c_n^{1/3} + (π/ξ_*) b_n)`;
  - `cardyV_mul_jAiry_window_ratio`: uniform prefactor ratio `→ 1` and exact log-ratio bound
    `|log-exp| ≤ q_n |t - t₀|` on fixed `uAiry`-windows.
* **Extremal zero multiplicities & complex zeros**:
  - `airyProfile_orderNat_one`, `airyProfile_orderNat_node`, `airyProfile_zero_iff`;
  - `hbProfile_orderNat_S`, `hbProfile_orderNat_offS`, `hbProfile_zero_im`,
  - `even_analyticOrderNatAt_of_nonneg` (double real zeros on the nonnegative ray);
  - `cardyV_window_ratio_sub_one_pos`, `exp_sub_one_le_secant`, `exp_sub_one_le_quadratic`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.FixedWeight

open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.WeightAxioms FormalResearch.ModularBootstrap.ConcreteBootstrap
  FormalResearch.ModularBootstrap.FixedWeightTip FormalResearch.ModularBootstrap.Blowup
  FormalResearch.ModularBootstrap.Upper.Rigidity FormalResearch.ModularBootstrap.Bessel
  FormalResearch.Special FormalResearch.SignUncertainty FormalResearch.ArgPrinciple

/-! ### 1. Langer chart vs linear Airy chart `uAiry` -/

/-- `virasoroDeltaChart c' u - (xiBar * c' - cStar * u * c'^(1/3))` is `O(u² c'^{-1/3})`
uniformly for `|u| ≤ virasoroAC c'^2`. -/
lemma virasoroDeltaChart_sub_linear {c' u : ℝ} (hc' : 0 < c')
    (hu : |u| ≤ virasoroAC c' ^ 2) :
    |virasoroDeltaChart c' u - (xiBar * c' - cStar * u * c' ^ ((1 : ℝ) / 3))| ≤
      virasoroCXi * u ^ 2 * c' ^ (-(1 / 3 : ℝ)) := by
  have hw := virasoro_u_mem_ball hc' (u := (u : ℂ))
    (by simpa [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs] using hu)
  have herr := chartParams.hxi_err _ hw
  have hc23 : 0 ≤ c' ^ (-(2 / 3 : ℝ)) := Real.rpow_nonneg hc'.le _
  have hnorm_w : ‖(u : ℂ) * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)‖ = |u| * c' ^ (-(2 / 3 : ℝ)) := by
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hc23]
  have hre : |((virasoroXiInf ((u : ℂ) * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)) -
      ((xiBar : ℂ) - (cStar : ℂ) * ((u : ℂ) * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ))))).re| ≤
      virasoroCXi * (|u| * c' ^ (-(2 / 3 : ℝ))) ^ 2 := by
    refine (abs_re_le_norm _).trans (herr.trans_eq ?_)
    rw [hnorm_w]; rfl
  have hre_eq : ((virasoroXiInf ((u : ℂ) * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)) -
      ((xiBar : ℂ) - (cStar : ℂ) * ((u : ℂ) * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ))))).re =
      (virasoroXiChartC c' (u : ℂ)).re - (xiBar - cStar * u * c' ^ (-(2 / 3 : ℝ))) := by
    simp only [virasoroXiChartC, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    ring
  rw [hre_eq] at hre
  have hmul_c : c' * ((virasoroXiChartC c' (u : ℂ)).re - (xiBar - cStar * u * c' ^ (-(2 / 3 : ℝ)))) =
      virasoroDeltaChart c' u - (xiBar * c' - cStar * u * c' ^ ((1 : ℝ) / 3)) := by
    have hp : c' * c' ^ (-(2 / 3 : ℝ)) = c' ^ ((1 : ℝ) / 3) := by
      calc c' * c' ^ (-(2 / 3 : ℝ))
          = c' ^ (1 : ℝ) * c' ^ (-(2 / 3 : ℝ)) := by rw [Real.rpow_one]
        _ = c' ^ ((1 : ℝ) + -(2 / 3 : ℝ)) := (Real.rpow_add hc' _ _).symm
        _ = c' ^ ((1 : ℝ) / 3) := by norm_num
    unfold virasoroDeltaChart
    calc c' * ((virasoroXiChartC c' (u : ℂ)).re - (xiBar - cStar * u * c' ^ (-(2 / 3 : ℝ))))
        = c' * (virasoroXiChartC c' (u : ℂ)).re - (xiBar * c' - cStar * u * (c' * c' ^ (-(2 / 3 : ℝ)))) := by
          ring
      _ = virasoroDeltaChart c' u - (xiBar * c' - cStar * u * c' ^ ((1 : ℝ) / 3)) := by
          unfold virasoroDeltaChart; rw [hp]
  have hpow : c' * (c' ^ (-(2 / 3 : ℝ))) ^ 2 = c' ^ (-(1 / 3 : ℝ)) := by
    have hsq : (c' ^ (-(2 / 3 : ℝ))) ^ 2 = c' ^ (-(4 / 3 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hc'.le]; norm_num
    calc c' * (c' ^ (-(2 / 3 : ℝ))) ^ 2
        = c' ^ (1 : ℝ) * c' ^ (-(4 / 3 : ℝ)) := by rw [hsq, Real.rpow_one]
      _ = c' ^ ((1 : ℝ) + -(4 / 3 : ℝ)) := (Real.rpow_add hc' _ _).symm
      _ = c' ^ (-(1 / 3 : ℝ)) := by norm_num
  calc |virasoroDeltaChart c' u - (xiBar * c' - cStar * u * c' ^ ((1 : ℝ) / 3))|
      = c' * |(virasoroXiChartC c' (u : ℂ)).re - (xiBar - cStar * u * c' ^ (-(2 / 3 : ℝ)))| := by
        rw [← hmul_c, abs_mul, abs_of_pos hc']
    _ ≤ c' * (virasoroCXi * (|u| * c' ^ (-(2 / 3 : ℝ))) ^ 2) :=
        mul_le_mul_of_nonneg_left hre hc'.le
    _ = virasoroCXi * u ^ 2 * (c' * (c' ^ (-(2 / 3 : ℝ))) ^ 2) := by
        rw [mul_pow, sq_abs]; ring
    _ = virasoroCXi * u ^ 2 * c' ^ (-(1 / 3 : ℝ)) := by rw [hpow]

/-- Uniform bound `|uAiry c' (virasoroDeltaChart c' u) - u| ≤ C_M c'^{-2/3}` for `|u| ≤ M`
and large `c'`. -/
lemma uAiry_virasoroDeltaChart_err {M : ℝ} (hM : 0 ≤ M) :
    ∃ C c₀ : ℝ, 0 ≤ C ∧ 1 ≤ c₀ ∧ ∀ {c' u : ℝ}, c₀ ≤ c' → |u| ≤ M →
      |uAiry c' (virasoroDeltaChart c' u) - u| ≤ C * c' ^ (-(2 / 3 : ℝ)) := by
  have hxibar : 0 < xiBar := by unfold xiBar; have := xiStar_pos; positivity
  have hc13_inv : ∀ {c' : ℝ}, 1 ≤ c' → c' ^ (-(2 / 3 : ℝ)) ≤ 1 := fun hc' =>
    Real.rpow_le_one_of_one_le_of_nonpos hc' (by norm_num)
  have h1 : Tendsto (fun c' : ℝ => virasoroAC c' ^ 2) atTop atTop :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).const_mul_atTop
      (mul_pos two_pos (pow_pos virasoroBV_pos 2))).congr'
      (by filter_upwards [eventually_ge_atTop (0 : ℝ)] with c' hc'; rw [virasoroAC_sq c' hc'])
  have h2 : Tendsto (fun c' : ℝ => (xiBar * c' - cStar * M * c' ^ ((1 : ℝ) / 3) -
      virasoroCXi * M ^ 2 * c' ^ (-(1 / 3 : ℝ))) / c') atTop (𝓝 xiBar) := by
    have ha : Tendsto (fun c' : ℝ => c' ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by norm_num)
    have hb : Tendsto (fun c' : ℝ => c' ^ (-(4 / 3 : ℝ))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by norm_num)
    have hlim : Tendsto (fun c' : ℝ =>
        xiBar - cStar * M * c' ^ (-(2 / 3 : ℝ)) - virasoroCXi * M ^ 2 * c' ^ (-(4 / 3 : ℝ)))
        atTop (𝓝 xiBar) := by
      simpa using (tendsto_const_nhds.sub (ha.const_mul (cStar * M))).sub
        (hb.const_mul (virasoroCXi * M ^ 2))
    refine hlim.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with c' hc'
    have h13 : c' ^ ((1 : ℝ) / 3) / c' = c' ^ (-(2 / 3 : ℝ)) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one c', ← Real.rpow_add hc']; congr 1; norm_num
    have hn13 : c' ^ (-(1 / 3 : ℝ)) / c' = c' ^ (-(4 / 3 : ℝ)) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one c', ← Real.rpow_add hc']; congr 1; norm_num
    rw [sub_div, sub_div, mul_div_cancel_right₀ _ hc'.ne', mul_div_assoc, mul_div_assoc, h13, hn13]
  have h3 : Tendsto (fun c' : ℝ => (xiBar * c' + cStar * M * c' ^ ((1 : ℝ) / 3) +
      virasoroCXi * M ^ 2 * c' ^ (-(1 / 3 : ℝ))) / c') atTop (𝓝 xiBar) := by
    have ha : Tendsto (fun c' : ℝ => c' ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by norm_num)
    have hb : Tendsto (fun c' : ℝ => c' ^ (-(4 / 3 : ℝ))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by norm_num)
    have hlim : Tendsto (fun c' : ℝ =>
        xiBar + cStar * M * c' ^ (-(2 / 3 : ℝ)) + virasoroCXi * M ^ 2 * c' ^ (-(4 / 3 : ℝ)))
        atTop (𝓝 xiBar) := by
      simpa using (tendsto_const_nhds.add (ha.const_mul (cStar * M))).add
        (hb.const_mul (virasoroCXi * M ^ 2))
    refine hlim.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with c' hc'
    have h13 : c' ^ ((1 : ℝ) / 3) / c' = c' ^ (-(2 / 3 : ℝ)) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one c', ← Real.rpow_add hc']; congr 1; norm_num
    have hn13 : c' ^ (-(1 / 3 : ℝ)) / c' = c' ^ (-(4 / 3 : ℝ)) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one c', ← Real.rpow_add hc']; congr 1; norm_num
    rw [add_div, add_div, mul_div_cancel_right₀ _ hc'.ne', mul_div_assoc, mul_div_assoc, h13, hn13]
  obtain ⟨c₁, hc₁⟩ := eventually_atTop.mp (h1.eventually_ge_atTop M)
  obtain ⟨c₂, hc₂⟩ := eventually_atTop.mp (h2.eventually (lt_mem_nhds (show xiBar / 2 < xiBar by linarith)))
  obtain ⟨c₃, hc₃⟩ := eventually_atTop.mp (h3.eventually (gt_mem_nhds (show xiBar < 2 * xiBar by linarith)))
  let C_t : ℝ := cStar * M + virasoroCXi * M ^ 2
  let C : ℝ := virasoroCXi * M ^ 2 / cStar + (1 / cStar) * (1 / (3 * betaTip ^ 2)) *
    (betaTip * (3 * C_t / (xiStar * (1 / √2 + 1)))) ^ 2
  have hCt_nn : 0 ≤ C_t := by have := cStar_pos; have := virasoroCXi_nn; positivity
  refine ⟨C, max 1 (max c₁ (max c₂ c₃)), by have := virasoroCXi_nn; have := cStar_pos; have := xiStar_pos; have := betaTip_pos; positivity,
    le_max_left _ _, fun {c' u} hc' hu => ?_⟩
  have hc'1 : 1 ≤ c' := (le_max_left _ _).trans hc'
  have hc'pos : 0 < c' := lt_of_lt_of_le zero_lt_one hc'1
  have hu_ac : |u| ≤ virasoroAC c' ^ 2 := hu.trans (hc₁ c' ((le_max_left _ _).trans ((le_max_right _ _).trans hc')))
  set t := virasoroDeltaChart c' u
  have ht_pos : 0 < t := virasoroDeltaChart_pos hc'pos hu_ac
  have hlin := virasoroDeltaChart_sub_linear hc'pos hu_ac
  have hu2 : u ^ 2 ≤ M ^ 2 := by rw [← sq_abs u]; exact pow_le_pow_left₀ (abs_nonneg _) hu 2
  have hlinM : |t - (xiBar * c' - cStar * u * c' ^ ((1 : ℝ) / 3))| ≤
      virasoroCXi * M ^ 2 * c' ^ (-(1 / 3 : ℝ)) := by
    refine hlin.trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu2 virasoroCXi_nn)
      (Real.rpow_nonneg hc'pos.le _)
  have hc13pos : 0 < c' ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hc'pos _
  have hc23 : c' ^ (-(1 / 3 : ℝ)) / c' ^ ((1 : ℝ) / 3) = c' ^ (-(2 / 3 : ℝ)) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg hc'pos.le, ← Real.rpow_add hc'pos]; congr 1; norm_num
  have hpos_id := position_identity hc'pos ht_pos.le
  have hcu : |cStar * u * c' ^ ((1 : ℝ) / 3)| ≤ cStar * M * c' ^ ((1 : ℝ) / 3) := by
    have hcstar_nn : 0 ≤ cStar := cStar_pos.le
    rw [abs_mul, abs_mul, abs_of_pos cStar_pos, abs_of_pos hc13pos]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu hcstar_nn) hc13pos.le
  have hc_le : c' ^ (-(1 / 3 : ℝ)) ≤ c' ^ ((1 : ℝ) / 3) :=
    Real.rpow_le_rpow_of_exponent_le hc'1 (by norm_num)
  -- Bound `√(3 t / c') ≥ xiStar / 2` directly from `hlinM`
  have htc_lo : xiBar / 2 ≤ t / c' := by
    have h2' := hc₂ c' ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc')))
    have hbd3 : xiBar * c' - cStar * M * c' ^ ((1 : ℝ) / 3) - virasoroCXi * M ^ 2 * c' ^ (-(1 / 3 : ℝ)) ≤ t := by
      have hsub := (abs_le.mp hlinM).1
      have hcu' : -(cStar * M * c' ^ ((1 : ℝ) / 3)) ≤ -cStar * u * c' ^ ((1 : ℝ) / 3) := by
        have hmu : -M ≤ -u := by linarith [(abs_le.mp hu).2]
        nlinarith [mul_nonneg cStar_pos.le hc13pos.le]
      linarith
    exact h2'.le.trans ((div_le_div_iff_of_pos_right hc'pos).mpr hbd3)
  have hsqrt_lo : xiStar / √2 ≤ √(3 * t / c') := by
    have h1 : (xiStar / √2) ^ 2 ≤ 3 * t / c' := by
      rw [div_pow, Real.sq_sqrt (by norm_num)]
      have heq : xiStar ^ 2 / 2 = 3 * (xiBar / 2) := by unfold xiBar; ring
      rw [heq, show 3 * t / c' = 3 * (t / c') by ring]
      exact mul_le_mul_of_nonneg_left htc_lo (by norm_num)
    exact Real.le_sqrt_of_sq_le h1
  -- Compute `|t - xiBar*c'| ≤ C_t * c'^{1/3}`
  have ht_diff : |t - xiBar * c'| ≤ C_t * c' ^ ((1 : ℝ) / 3) := by
    have h1 := abs_sub_abs_le_abs_sub (t - xiBar * c') (-(cStar * u * c' ^ ((1 : ℝ) / 3)))
    have e1 : (t - xiBar * c') - (-(cStar * u * c' ^ ((1 : ℝ) / 3))) =
        t - (xiBar * c' - cStar * u * c' ^ ((1 : ℝ) / 3)) := by ring
    rw [e1, abs_neg] at h1
    dsimp [C_t]
    nlinarith [mul_le_mul_of_nonneg_left hc_le (mul_nonneg virasoroCXi_nn (sq_nonneg M))]
  -- Therefore `|√(3t/c') - xiStar| ≤ (3 |t - xiBar*c'| / c') / (xiStar / √2 + xiStar)`
  have hx_diff : |√(3 * t / c') - xiStar| ≤ 3 * C_t / (xiStar * (1 / √2 + 1)) * c' ^ (-(2 / 3 : ℝ)) := by
    have hsum_pos : 0 < √(3 * t / c') + xiStar := by have := xiStar_pos; positivity
    have hsum_ge : xiStar * (1 / √2 + 1) ≤ √(3 * t / c') + xiStar := by
      have : xiStar / √2 + xiStar = xiStar * (1 / √2 + 1) := by ring
      linarith [hsqrt_lo]
    have hmul : (√(3 * t / c') - xiStar) * (√(3 * t / c') + xiStar) = 3 * (t - xiBar * c') / c' := by
      have hsq : √(3 * t / c') ^ 2 = 3 * t / c' := Real.sq_sqrt (by positivity)
      have hxb : xiStar ^ 2 = 3 * xiBar := by unfold xiBar; ring
      calc (√(3 * t / c') - xiStar) * (√(3 * t / c') + xiStar)
          = √(3 * t / c') ^ 2 - xiStar ^ 2 := by ring
        _ = 3 * t / c' - 3 * xiBar := by rw [hsq, hxb]
        _ = 3 * (t - xiBar * c') / c' := by field_simp [hc'pos.ne']
    have heq : √(3 * t / c') - xiStar = (3 * (t - xiBar * c') / c') / (√(3 * t / c') + xiStar) :=
      eq_div_of_mul_eq hsum_pos.ne' hmul
    rw [heq, abs_div, abs_of_pos hsum_pos, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3),
      abs_of_pos hc'pos]
    have hden_le : 1 / (√(3 * t / c') + xiStar) ≤ 1 / (xiStar * (1 / √2 + 1)) :=
      one_div_le_one_div_of_le (by have := xiStar_pos; positivity) hsum_ge
    have hc13_div : c' ^ ((1 : ℝ) / 3) / c' = c' ^ (-(2 / 3 : ℝ)) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one c', ← Real.rpow_add hc'pos]; congr 1; norm_num
    calc 3 * |t - xiBar * c'| / c' / (√(3 * t / c') + xiStar)
        = (3 * (|t - xiBar * c'| / c')) * (1 / (√(3 * t / c') + xiStar)) := by ring
      _ ≤ (3 * (C_t * c' ^ ((1 : ℝ) / 3) / c')) * (1 / (xiStar * (1 / √2 + 1))) := by
          gcongr
      _ = 3 * C_t / (xiStar * (1 / √2 + 1)) * c' ^ (-(2 / 3 : ℝ)) := by
          rw [mul_div_assoc, hc13_div]; ring
  have huAiry_bd : |uAiry c' t| ≤ betaTip * (3 * C_t / (xiStar * (1 / √2 + 1))) := by
    unfold uAiry
    rw [abs_mul, abs_mul, abs_neg, abs_of_pos betaTip_pos,
      abs_of_pos (Real.rpow_pos_of_pos hc'pos _)]
    have hc23p : c' ^ (-(2 / 3 : ℝ)) * c' ^ ((2 : ℝ) / 3) = 1 := by
      rw [← Real.rpow_add hc'pos]; simp
    calc betaTip * |√(3 * t / c') - xiStar| * c' ^ ((2 : ℝ) / 3)
        ≤ betaTip * (3 * C_t / (xiStar * (1 / √2 + 1)) * c' ^ (-(2 / 3 : ℝ))) *
            c' ^ ((2 : ℝ) / 3) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx_diff betaTip_pos.le)
            (Real.rpow_nonneg hc'pos.le _)
      _ = betaTip * (3 * C_t / (xiStar * (1 / √2 + 1))) *
            (c' ^ (-(2 / 3 : ℝ)) * c' ^ ((2 : ℝ) / 3)) := by ring
      _ = betaTip * (3 * C_t / (xiStar * (1 / √2 + 1))) := by rw [hc23p, mul_one]
  -- Now compare `uAiry c' t` and `u` using `position_identity`!
  have hdiff_id : (t - (xiBar * c' - cStar * u * c' ^ ((1 : ℝ) / 3))) / (cStar * c' ^ ((1 : ℝ) / 3)) =
      u - uAiry c' t + epsAiry c' * (uAiry c' t) ^ 2 / (cStar * (3 * betaTip ^ 2)) := by
    have heq : t - xiBar * c' = c' ^ ((1 : ℝ) / 3) *
        (-cStar * uAiry c' t + epsAiry c' * (uAiry c' t) ^ 2 / (3 * betaTip ^ 2)) := hpos_id
    have hcs0 := cStar_pos.ne'
    have hc13_0 := hc13pos.ne'
    calc (t - (xiBar * c' - cStar * u * c' ^ ((1 : ℝ) / 3))) / (cStar * c' ^ ((1 : ℝ) / 3))
        = ((t - xiBar * c') + cStar * u * c' ^ ((1 : ℝ) / 3)) / (cStar * c' ^ ((1 : ℝ) / 3)) := by ring
      _ = (c' ^ ((1 : ℝ) / 3) * (-cStar * uAiry c' t + epsAiry c' * (uAiry c' t) ^ 2 /
            (3 * betaTip ^ 2)) + cStar * u * c' ^ ((1 : ℝ) / 3)) / (cStar * c' ^ ((1 : ℝ) / 3)) := by
          rw [heq]
      _ = u - uAiry c' t + epsAiry c' * (uAiry c' t) ^ 2 / (cStar * (3 * betaTip ^ 2)) := by
          field_simp [hcs0, hc13_0]; ring
  have hmain : |uAiry c' t - u| ≤
      |t - (xiBar * c' - cStar * u * c' ^ ((1 : ℝ) / 3))| / (cStar * c' ^ ((1 : ℝ) / 3)) +
      epsAiry c' * (uAiry c' t) ^ 2 / (cStar * (3 * betaTip ^ 2)) := by
    have heq2 : uAiry c' t - u =
        -( (t - (xiBar * c' - cStar * u * c' ^ ((1 : ℝ) / 3))) / (cStar * c' ^ ((1 : ℝ) / 3)) ) +
        epsAiry c' * (uAiry c' t) ^ 2 / (cStar * (3 * betaTip ^ 2)) := by linarith [hdiff_id]
    rw [heq2]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_neg, abs_div, abs_of_pos (mul_pos cStar_pos hc13pos)]
    · rw [abs_of_nonneg (div_nonneg (mul_nonneg (epsAiry_pos hc'pos).le (sq_nonneg _))
        (mul_nonneg cStar_pos.le (by positivity)))]
  have hterm1 : |t - (xiBar * c' - cStar * u * c' ^ ((1 : ℝ) / 3))| / (cStar * c' ^ ((1 : ℝ) / 3)) ≤
      virasoroCXi * M ^ 2 / cStar * c' ^ (-(2 / 3 : ℝ)) := by
    have hpos_den : 0 ≤ cStar * c' ^ ((1 : ℝ) / 3) := (mul_pos cStar_pos hc13pos).le
    calc |t - (xiBar * c' - cStar * u * c' ^ ((1 : ℝ) / 3))| / (cStar * c' ^ ((1 : ℝ) / 3))
        ≤ (virasoroCXi * M ^ 2 * c' ^ (-(1 / 3 : ℝ))) / (cStar * c' ^ ((1 : ℝ) / 3)) :=
          div_le_div_of_nonneg_right hlinM hpos_den
      _ = virasoroCXi * M ^ 2 / cStar * (c' ^ (-(1 / 3 : ℝ)) / c' ^ ((1 : ℝ) / 3)) := by ring
      _ = virasoroCXi * M ^ 2 / cStar * c' ^ (-(2 / 3 : ℝ)) := by rw [hc23]
  have hterm2 : epsAiry c' * (uAiry c' t) ^ 2 / (cStar * (3 * betaTip ^ 2)) ≤
      (1 / cStar) * (1 / (3 * betaTip ^ 2)) *
        (betaTip * (3 * C_t / (xiStar * (1 / √2 + 1)))) ^ 2 * c' ^ (-(2 / 3 : ℝ)) := by
    have hsq : (uAiry c' t) ^ 2 ≤ (betaTip * (3 * C_t / (xiStar * (1 / √2 + 1)))) ^ 2 := by
      rw [← sq_abs (uAiry c' t)]
      exact pow_le_pow_left₀ (abs_nonneg _) huAiry_bd 2
    have hε : epsAiry c' = c' ^ (-(2 / 3 : ℝ)) := rfl
    rw [hε]
    have hden_nn : 0 ≤ cStar * (3 * betaTip ^ 2) := (mul_pos cStar_pos (by have := betaTip_pos; positivity)).le
    calc c' ^ (-(2 / 3 : ℝ)) * (uAiry c' t) ^ 2 / (cStar * (3 * betaTip ^ 2))
        ≤ c' ^ (-(2 / 3 : ℝ)) * (betaTip * (3 * C_t / (xiStar * (1 / √2 + 1)))) ^ 2 /
            (cStar * (3 * betaTip ^ 2)) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg hc'pos.le _)) hden_nn
      _ = (1 / cStar) * (1 / (3 * betaTip ^ 2)) *
            (betaTip * (3 * C_t / (xiStar * (1 / √2 + 1)))) ^ 2 * c' ^ (-(2 / 3 : ℝ)) := by ring
  have h1' := hmain.trans (add_le_add hterm1 hterm2)
  have hsum : virasoroCXi * M ^ 2 / cStar * c' ^ (-(2 / 3 : ℝ)) +
      (1 / cStar) * (1 / (3 * betaTip ^ 2)) *
        (betaTip * (3 * C_t / (xiStar * (1 / √2 + 1)))) ^ 2 * c' ^ (-(2 / 3 : ℝ)) =
      C * c' ^ (-(2 / 3 : ℝ)) := by dsimp [C]; ring
  linarith [h1', hsum]

/-- Converse comparison: on any bounded Airy window `|uAiry c' t| ≤ M` (`t > 0`), for all
large `c'`, `|chartUT c' t| ≤ M + 1`, `virasoroDeltaChart c' (chartUT c' t) = t`, and
`|uAiry c' t - chartUT c' t| ≤ C * c' ^ (-(2 / 3 : ℝ))`. -/
lemma chartUT_sub_uAiry_err {M : ℝ} (hM : 0 ≤ M) :
    ∃ C c₀ : ℝ, 0 ≤ C ∧ 1 ≤ c₀ ∧ ∀ {c' t : ℝ}, c₀ ≤ c' → 0 < t → |uAiry c' t| ≤ M →
      |chartUT c' t| ≤ M + 1 ∧ virasoroDeltaChart c' (chartUT c' t) = t ∧
        |uAiry c' t - chartUT c' t| ≤ C * c' ^ (-(2 / 3 : ℝ)) := by
  obtain ⟨C, c₁, hC, hc₁, herr⟩ := uAiry_virasoroDeltaChart_err (show 0 ≤ M + 1 by linarith)
  have hev_ac : ∀ᶠ c' : ℝ in atTop, M + 1 ≤ virasoroAC c' ^ 2 := by
    have h1 : Tendsto (fun c' : ℝ => virasoroAC c' ^ 2) atTop atTop :=
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).const_mul_atTop
        (mul_pos two_pos (pow_pos virasoroBV_pos 2))).congr'
        (by filter_upwards [eventually_ge_atTop (0 : ℝ)] with c' hc'; rw [virasoroAC_sq c' hc'])
    exact h1.eventually_ge_atTop (M + 1)
  have hev_err : ∀ᶠ c' : ℝ in atTop, C * c' ^ (-(2 / 3 : ℝ)) < 1 / 2 := by
    have h0 : Tendsto (fun c' : ℝ => C * c' ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).const_mul C
    exact h0.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨c₂, hc₂⟩ := eventually_atTop.mp (hev_ac.and hev_err)
  refine ⟨C, max c₁ (max c₂ 1), hC, le_trans (le_max_right _ _) (le_max_right _ _),
    fun {c' t} hc' ht hu => ?_⟩
  have hc'1 : c₁ ≤ c' := (le_max_left _ _).trans hc'
  have hc'2 : c₂ ≤ c' := (le_max_left _ _).trans ((le_max_right _ _).trans hc')
  have hc'pos : 0 < c' := lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans ((le_max_right _ _).trans hc'))
  obtain ⟨hac, hC_lt⟩ := hc₂ c' hc'2
  have hup := herr hc'1 (show |(M + 1 : ℝ)| ≤ M + 1 by rw [abs_of_nonneg (by linarith)])
  have hlo := herr hc'1 (show |(-(M + 1) : ℝ)| ≤ M + 1 by rw [abs_neg, abs_of_nonneg (by linarith)])
  have h_uplus : uAiry c' t < uAiry c' (virasoroDeltaChart c' (M + 1)) := by
    have := (abs_le.mp hup).1
    have := (abs_le.mp hu).2
    linarith
  have h_uminus : uAiry c' (virasoroDeltaChart c' (-(M + 1))) < uAiry c' t := by
    have := (abs_le.mp hlo).2
    have := (abs_le.mp hu).1
    linarith
  have ht_hi : t < virasoroDeltaChart c' (-(M + 1)) := by
    by_contra hle; push Not at hle
    exact absurd (uAiry_antitone hc'pos hle) (not_le.mpr h_uminus)
  have ht_lo : virasoroDeltaChart c' (M + 1) < t := by
    by_contra hle; push Not at hle
    exact absurd (uAiry_antitone hc'pos hle) (not_le.mpr h_uplus)
  have ht_mem : t / c' ∈ Icc (virasoroDeltaChart c' (virasoroAC c' ^ 2) / c')
      (virasoroDeltaChart c' (-(virasoroAC c' ^ 2)) / c') := by
    have hanti := virasoroDeltaChart_strictAnti hc'pos
    have hhi_ac : virasoroDeltaChart c' (-(M + 1)) ≤ virasoroDeltaChart c' (-(virasoroAC c' ^ 2)) :=
      hanti.antitoneOn ⟨le_rfl, by linarith [sq_nonneg (virasoroAC c')]⟩
        ⟨by linarith [hac], by linarith⟩ (by linarith)
    have hlo_ac : virasoroDeltaChart c' (virasoroAC c' ^ 2) ≤ virasoroDeltaChart c' (M + 1) :=
      hanti.antitoneOn ⟨by linarith [hac], by linarith⟩
        ⟨by linarith [sq_nonneg (virasoroAC c')], le_rfl⟩ hac
    exact ⟨div_le_div_of_nonneg_right (hlo_ac.trans ht_lo.le) hc'pos.le,
      div_le_div_of_nonneg_right (ht_hi.le.trans hhi_ac) hc'pos.le⟩
  have huc_lo := virasoroDeltaChart_div_mem hc'pos (abs_of_nonneg (sq_nonneg _)).le
  have huc_hi := virasoroDeltaChart_div_mem hc'pos (by rw [abs_neg, abs_of_nonneg (sq_nonneg _)])
  have hu_anti := virasoroUChart_strictAnti hc'pos
  have hdiv_mem : t / c' ∈ Icc (xiBar - virasoroChartR0) (xiBar + virasoroChartR0) :=
    ⟨huc_lo.1.trans ht_mem.1, ht_mem.2.trans huc_hi.2⟩
  have hlo_mem : virasoroDeltaChart c' (M + 1) / c' ∈ Icc (xiBar - virasoroChartR0) (xiBar + virasoroChartR0) :=
    virasoroDeltaChart_div_mem hc'pos (by rw [abs_of_nonneg (by linarith)]; exact hac)
  have hhi_mem : virasoroDeltaChart c' (-(M + 1)) / c' ∈ Icc (xiBar - virasoroChartR0) (xiBar + virasoroChartR0) :=
    virasoroDeltaChart_div_mem hc'pos (by rw [abs_neg, abs_of_nonneg (by linarith)]; exact hac)
  have hchart_lo : -(M + 1) < chartUT c' t := by
    have h1 := hu_anti hdiv_mem hhi_mem (div_lt_div_of_pos_right ht_hi hc'pos)
    rwa [virasoroUChart_deltaChart hc'pos (by rw [abs_neg, abs_of_nonneg (by linarith)]; exact hac)] at h1
  have hchart_hi : chartUT c' t < M + 1 := by
    have h1 := hu_anti hlo_mem hdiv_mem (div_lt_div_of_pos_right ht_lo hc'pos)
    rwa [virasoroUChart_deltaChart hc'pos (by rw [abs_of_nonneg (by linarith)]; exact hac)] at h1
  have hchart_abs : |chartUT c' t| ≤ M + 1 := abs_le.mpr ⟨hchart_lo.le, hchart_hi.le⟩
  have hdelta_eq : virasoroDeltaChart c' (chartUT c' t) = t := by
    unfold chartUT
    rw [virasoroDeltaChart_uChart hc'pos ht_mem.1 ht_mem.2, mul_div_cancel₀ _ hc'pos.ne']
  refine ⟨hchart_abs, hdelta_eq, ?_⟩
  have hres := herr hc'1 hchart_abs
  rwa [hdelta_eq] at hres

/-- Two-sided derivative bound on `virasoroDeltaChart`:
`(cStar / 2) * c'^(1/3) ≤ -(deriv (virasoroDeltaChart c') u) ≤ C_d * c'^(1/3)` on `|u| ≤ virasoroAC c'^2`. -/
lemma virasoroDeltaChart_deriv_abs_bounds :
    ∃ C_d : ℝ, cStar / 2 ≤ C_d ∧ ∀ {c' u : ℝ}, 0 < c' → |u| ≤ virasoroAC c' ^ 2 →
      (cStar / 2) * c' ^ ((1 : ℝ) / 3) ≤ -deriv (virasoroDeltaChart c') u ∧
        -deriv (virasoroDeltaChart c') u ≤ C_d * c' ^ ((1 : ℝ) / 3) := by
  have hcont : ContinuousOn (fun w : ℂ => ‖deriv virasoroXiInf w‖) (closedBall (0 : ℂ) (2 * virasoroBV ^ 2)) := by
    have hsub : closedBall (0 : ℂ) (2 * virasoroBV ^ 2) ⊆ ball (0 : ℂ) virasoroRUInf :=
      closedBall_subset_ball (chartParams.h2bV2_lt.trans (half_lt_self virasoroRUInf_pos))
    exact ((virasoroXiInf_an.deriv).mono hsub).continuousOn.norm
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) (2 * virasoroBV ^ 2)).exists_bound_of_continuousOn hcont
  refine ⟨max C (cStar / 2), le_max_right _ _, fun {c' u} hc' hu => ?_⟩
  have hlo := virasoroDeltaChart_deriv_le hc' (abs_le.mp hu)
  have hd := virasoroDeltaChart_hasDerivAt hc' hu
  have hw := virasoro_u_mem_ball hc' (u := (u : ℂ))
    (by simpa [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs] using hu)
  have hnb := hC _ hw
  rw [Real.norm_eq_abs, abs_norm] at hnb
  have hre : -(deriv virasoroXiInf ((u * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)).re ≤ max C (cStar / 2) := by
    have hcast : ((u * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) = (u : ℂ) * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) := by
      push_cast; rfl
    rw [hcast]
    exact (neg_le_abs _).trans ((abs_re_le_norm _).trans (hnb.trans (le_max_left _ _)))
  refine ⟨by linarith, ?_⟩
  rw [hd.deriv]
  have hc13 : 0 ≤ c' ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hc'.le _
  have e1 : -(c' ^ ((1 : ℝ) / 3) * (deriv virasoroXiInf ((u * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)).re) =
      -(deriv virasoroXiInf ((u * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)).re * c' ^ ((1 : ℝ) / 3) := by ring
  rw [e1]
  exact mul_le_mul_of_nonneg_right hre hc13

/-- If `uAiry (c n) (t n) → z`, then eventually `0 < t n`. -/
lemma eventually_pos_of_uAiry_tendsto {c t : ℕ → ℝ} {z : ℝ} (hc : Tendsto c atTop atTop)
    (hu : Tendsto (fun n => uAiry (c n) (t n)) atTop (𝓝 z)) :
    ∀ᶠ n in atTop, 0 < t n := by
  have hlim_bd : Tendsto (fun n => betaTip * xiStar * (c n) ^ ((2 : ℝ) / 3)) atTop atTop :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc).const_mul_atTop
      (mul_pos betaTip_pos xiStar_pos)
  filter_upwards [hc.eventually_gt_atTop 0,
    hu.eventually (gt_mem_nhds (show z < z + 1 by linarith)),
    hlim_bd.eventually_ge_atTop (z + 1)] with n hcn hzu hbig
  by_contra hle; push Not at hle
  have h3t : 3 * t n / c n ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hcn.le
  have huval : uAiry (c n) (t n) = betaTip * xiStar * (c n) ^ ((2 : ℝ) / 3) := by
    unfold uAiry; rw [Real.sqrt_eq_zero_of_nonpos h3t]; ring
  linarith

/-- `uAiry (c n) (t n) → z` implies `(t n - ξ̄ c n) / c_n^{1/3} → -c_* z`. -/
lemma tendsto_position_of_uAiry {c t : ℕ → ℝ} {z : ℝ} (hc : Tendsto c atTop atTop)
    (hu : Tendsto (fun n => uAiry (c n) (t n)) atTop (𝓝 z)) :
    Tendsto (fun n => (t n - xiBar * c n) / (c n) ^ ((1 : ℝ) / 3)) atTop (𝓝 (-cStar * z)) := by
  have ht := eventually_pos_of_uAiry_tendsto hc hu
  have heps : Tendsto (fun n => epsAiry (c n)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc
  have hlim : Tendsto (fun n => -cStar * uAiry (c n) (t n) +
      epsAiry (c n) * (uAiry (c n) (t n)) ^ 2 / (3 * betaTip ^ 2)) atTop (𝓝 (-cStar * z)) := by
    have h1 := hu.const_mul (-cStar)
    have h2 : Tendsto (fun n => epsAiry (c n) * (uAiry (c n) (t n)) ^ 2 / (3 * betaTip ^ 2)) atTop (𝓝 0) := by
      simpa using ((heps.mul (hu.pow 2)).div_const (3 * betaTip ^ 2))
    simpa using h1.add h2
  refine hlim.congr' ?_
  filter_upwards [hc.eventually_gt_atTop 0, ht] with n hcn htn
  have hp : (c n) ^ ((1 : ℝ) / 3) ≠ 0 := (Real.rpow_pos_of_pos hcn _).ne'
  rw [position_identity hcn htn.le, mul_div_cancel_left₀ _ hp]

/-- Converse: `(t n - ξ̄ c n) / c_n^{1/3} → -c_* z` implies `0 < t n` eventually and
`uAiry (c n) (t n) → z`. -/
lemma tendsto_uAiry_of_position {c t : ℕ → ℝ} {z : ℝ} (hc : Tendsto c atTop atTop)
    (ht : Tendsto (fun n => (t n - xiBar * c n) / (c n) ^ ((1 : ℝ) / 3)) atTop (𝓝 (-cStar * z))) :
    (∀ᶠ n in atTop, 0 < t n) ∧ Tendsto (fun n => uAiry (c n) (t n)) atTop (𝓝 z) := by
  have htc : Tendsto (fun n => t n / c n) atTop (𝓝 xiBar) := by
    have hc23 : Tendsto (fun n => (c n) ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc
    have hadd : Tendsto (fun n => xiBar + ((t n - xiBar * c n) / (c n) ^ ((1 : ℝ) / 3)) *
        (c n) ^ (-(2 / 3 : ℝ))) atTop (𝓝 xiBar) := by
      simpa using tendsto_const_nhds.add (ht.mul hc23)
    refine hadd.congr' ?_
    filter_upwards [hc.eventually_gt_atTop 0] with n hcn
    have hpow : (c n) ^ ((1 : ℝ) / 3) * (c n) ^ ((2 : ℝ) / 3) = c n := by
      rw [← Real.rpow_add hcn]; norm_num
    have hneg : (c n) ^ (-(2 / 3 : ℝ)) = 1 / (c n) ^ ((2 : ℝ) / 3) := by
      rw [Real.rpow_neg hcn.le, one_div]
    calc xiBar + (t n - xiBar * c n) / (c n) ^ ((1 : ℝ) / 3) * (c n) ^ (-(2 / 3 : ℝ))
        = xiBar + (t n - xiBar * c n) / ((c n) ^ ((1 : ℝ) / 3) * (c n) ^ ((2 : ℝ) / 3)) := by
          rw [hneg]; ring
      _ = xiBar + (t n - xiBar * c n) / c n := by rw [hpow]
      _ = t n / c n := by field_simp [hcn.ne']; ring
  have hxibar : 0 < xiBar := by unfold xiBar; have := xiStar_pos; positivity
  have hpos : ∀ᶠ n in atTop, 0 < t n := by
    filter_upwards [hc.eventually_gt_atTop 0, htc.eventually (lt_mem_nhds (by linarith : xiBar / 2 < xiBar))]
      with n hcn hdiv
    have : 0 < t n / c n := lt_trans (by positivity) hdiv
    exact (div_pos_iff.mp this).elim (fun h => h.1) (fun h => absurd hcn (not_lt.mpr h.2.le))
  have hsqrt : Tendsto (fun n => Real.sqrt (3 * t n / c n)) atTop (𝓝 xiStar) := by
    have h3 : Tendsto (fun n => 3 * t n / c n) atTop (𝓝 (3 * xiBar)) := by
      simpa only [mul_div_assoc] using htc.const_mul 3
    have hr := h3.sqrt
    have h3x : Real.sqrt (3 * xiBar) = xiStar := by
      have : 3 * xiBar = xiStar ^ 2 := by unfold xiBar; ring
      rw [this, Real.sqrt_sq xiStar_pos.le]
    rwa [h3x] at hr
  have hlim : Tendsto (fun n => ((t n - xiBar * c n) / (c n) ^ ((1 : ℝ) / 3)) *
      (-(3 * betaTip / (Real.sqrt (3 * t n / c n) + xiStar)))) atTop (𝓝 z) := by
    have hden : Tendsto (fun n => -(3 * betaTip / (Real.sqrt (3 * t n / c n) + xiStar))) atTop
        (𝓝 (-(3 * betaTip / (2 * xiStar)))) := by
      have h0 := ((tendsto_const_nhds (x := 3 * betaTip)).div (hsqrt.add tendsto_const_nhds)
        (by linarith [xiStar_pos])).neg
      rwa [show xiStar + xiStar = 2 * xiStar by ring] at h0
    have heq : (-cStar * z) * (-(3 * betaTip / (2 * xiStar))) = z := by
      unfold cStar; field_simp [xiStar_pos.ne', betaTip_pos.ne']
    have hlim' := ht.mul hden
    rwa [heq] at hlim'
  refine ⟨hpos, hlim.congr' ?_⟩
  filter_upwards [hc.eventually_gt_atTop 0, hpos] with n hcn htn
  have hsum_pos : 0 < Real.sqrt (3 * t n / c n) + xiStar := by have := xiStar_pos; positivity
  have hpow : (c n) ^ ((1 : ℝ) / 3) * (c n) ^ ((2 : ℝ) / 3) = c n := by
    rw [← Real.rpow_add hcn]; norm_num
  have hsq : Real.sqrt (3 * t n / c n) ^ 2 = 3 * t n / c n := Real.sq_sqrt (by positivity)
  have hxb : xiStar ^ 2 = 3 * xiBar := by unfold xiBar; ring
  have hmul : (Real.sqrt (3 * t n / c n) - xiStar) * (Real.sqrt (3 * t n / c n) + xiStar) =
      3 * (t n - xiBar * c n) / c n := by
    calc (Real.sqrt (3 * t n / c n) - xiStar) * (Real.sqrt (3 * t n / c n) + xiStar)
        = Real.sqrt (3 * t n / c n) ^ 2 - xiStar ^ 2 := by ring
      _ = 3 * t n / c n - 3 * xiBar := by rw [hsq, hxb]
      _ = 3 * (t n - xiBar * c n) / c n := by field_simp [hcn.ne']
  have hsub : Real.sqrt (3 * t n / c n) - xiStar =
      (3 * (t n - xiBar * c n) / c n) / (Real.sqrt (3 * t n / c n) + xiStar) :=
    eq_div_of_mul_eq hsum_pos.ne' hmul
  unfold uAiry
  rw [hsub]
  have hp13 : (c n) ^ ((1 : ℝ) / 3) ≠ 0 := (Real.rpow_pos_of_pos hcn _).ne'
  have hp23 : (c n) ^ ((2 : ℝ) / 3) ≠ 0 := (Real.rpow_pos_of_pos hcn _).ne'
  calc (t n - xiBar * c n) / (c n) ^ ((1 : ℝ) / 3) * -(3 * betaTip / (√(3 * t n / c n) + xiStar))
      = -betaTip * ((3 * (t n - xiBar * c n) / c n) / (√(3 * t n / c n) + xiStar)) *
          (c n / (c n) ^ ((1 : ℝ) / 3)) := by field_simp [hcn.ne', hsum_pos.ne', hp13]
    _ = -betaTip * ((3 * (t n - xiBar * c n) / c n) / (√(3 * t n / c n) + xiStar)) *
          (c n) ^ ((2 : ℝ) / 3) := by
        congr 1
        rw [div_eq_iff hp13, mul_comm, hpow]

/-! ### 2. Cardy + Jacobian asymptotics (`dsl:hb-raw`, `dsl:d1-asym`, `dsl:hb-mass`) -/

/-- Exact exponential identity for Cardy scaling:
`c * (2π x / 3) = (2/3) * arsinh(1) * c + (π / ξ_*) (t - ξ̄ c) - (π / (3 ξ_*)) c (x - ξ_*)^2`
when `x^2 = 3 t / c`. -/
lemma cardy_exp_exact_id {c t x : ℝ} (hc : c ≠ 0) (hx : x ^ 2 = 3 * t / c) :
    c * (2 * Real.pi * x / 3) =
      (2 / 3 : ℝ) * Real.arsinh 1 * c + (Real.pi / xiStar) * (t - xiBar * c) -
        (Real.pi / (3 * xiStar)) * c * (x - xiStar) ^ 2 := by
  have hxi : Real.arsinh 1 = Real.pi * xiStar := by unfold xiStar; field_simp [Real.pi_ne_zero]
  have hxb : 3 * xiBar = xiStar ^ 2 := by unfold xiBar; ring
  have ht : t - xiBar * c = c * (x ^ 2 - xiStar ^ 2) / 3 := by
    have h1 : 3 * t = c * x ^ 2 := by rw [hx]; field_simp [hc]
    have h2 : 3 * xiBar * c = c * xiStar ^ 2 := by rw [← hxb]; ring
    linarith
  rw [hxi, ht]
  field_simp [xiStar_pos.ne']
  ring

/-- **Cardy × Jacobian raw weight asymptotic** (`dsl:hb-raw`, `dsl:d1-asym`):
for any `prob : FixedWeightProblem`, node coordinate `z : ℝ`, and sequence `t n` with
`uAiry (c n) (t n) → z`, setting `b n := t n - xiBar * c n + cStar * z * (c n)^(1/3)`,
`2π V(c_n/12, t_n) J_{c_n}(t_n)` is asymptotic to
`(2 √ξ_* (2ξ_*)^{w-1} Q(e^{-4πξ_*}) / (√3 β)) · c_n^{-1/6} · exp((2/3) arsinh(1) c_n - (2π z / (3 β)) c_n^{1/3} + (π / ξ_*) b_n)`. -/
theorem cardyV_mul_jAiry_asymp (prob : FixedWeightProblem) {c t : ℕ → ℝ} {z : ℝ}
    (hc : Tendsto c atTop atTop)
    (hu : Tendsto (fun n => uAiry (c n) (t n)) atTop (𝓝 z)) :
    let amp : ℝ := 2 * Real.sqrt xiStar * (2 * xiStar) ^ (prob.w - 1) *
      prob.nullPoly (Real.exp (-4 * Real.pi * xiStar)) / (Real.sqrt 3 * betaTip)
    let b : ℕ → ℝ := fun n => t n - xiBar * c n + cStar * z * (c n) ^ ((1 : ℝ) / 3)
    Tendsto (fun n => (2 * Real.pi * prob.cardyV (c n / 12) (t n) * jAiry (c n) (t n)) /
        (amp * (c n) ^ (-(1 / 6 : ℝ)) *
          Real.exp ((2 / 3 : ℝ) * Real.arsinh 1 * c n -
            (2 * Real.pi * z / (3 * betaTip)) * (c n) ^ ((1 : ℝ) / 3) +
            (Real.pi / xiStar) * b n))) atTop (𝓝 1) := by
  intro amp b
  have hpos_t := eventually_pos_of_uAiry_tendsto hc hu
  let x : ℕ → ℝ := fun n => Real.sqrt (3 * t n / c n)
  have hx_tend : Tendsto x atTop (𝓝 xiStar) := by
    have heq : ∀ᶠ n in atTop, x n = xiStar - uAiry (c n) (t n) / (betaTip * (c n) ^ ((2 : ℝ) / 3)) := by
      filter_upwards [hc.eventually_gt_atTop 0] with n hcn
      have hp : (c n) ^ ((2 : ℝ) / 3) ≠ 0 := (Real.rpow_pos_of_pos hcn _).ne'
      unfold uAiry x
      field_simp [betaTip_pos.ne', hp]; ring
    have h0 : Tendsto (fun n => xiStar - uAiry (c n) (t n) * ((betaTip)⁻¹ * (c n) ^ (-(2 / 3 : ℝ))))
        atTop (𝓝 xiStar) := by
      have h23 : Tendsto (fun n => (c n) ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) :=
        (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc
      simpa using tendsto_const_nhds.sub (hu.mul (h23.const_mul betaTip⁻¹))
    refine h0.congr' ?_
    filter_upwards [heq, hc.eventually_gt_atTop 0] with n hn hcn
    rw [hn, Real.rpow_neg hcn.le]; ring
  have hquad_exp : Tendsto (fun n => (c n) * (x n - xiStar) ^ 2) atTop (𝓝 0) := by
    have heq : ∀ᶠ n in atTop, (c n) * (x n - xiStar) ^ 2 =
        (c n) ^ (-(1 / 3 : ℝ)) * (-(uAiry (c n) (t n)) / betaTip) ^ 2 := by
      filter_upwards [hc.eventually_gt_atTop 0] with n hcn
      have hsub : x n - xiStar = -(uAiry (c n) (t n)) / (betaTip * (c n) ^ ((2 : ℝ) / 3)) := by
        unfold uAiry x
        have hp : (c n) ^ ((2 : ℝ) / 3) ≠ 0 := (Real.rpow_pos_of_pos hcn _).ne'
        field_simp [betaTip_pos.ne', hp]
      have hpow43 : ((c n) ^ ((2 : ℝ) / 3)) ^ 2 = (c n) ^ ((4 : ℝ) / 3) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hcn.le]; norm_num
      have hpow : c n / (c n) ^ ((4 : ℝ) / 3) = (c n) ^ (-(1 / 3 : ℝ)) := by
        calc c n / (c n) ^ ((4 : ℝ) / 3)
            = c n ^ (1 : ℝ) * (c n ^ ((4 : ℝ) / 3))⁻¹ := by rw [div_eq_mul_inv, Real.rpow_one]
          _ = c n ^ (1 : ℝ) * c n ^ (-((4 : ℝ) / 3)) := by rw [← Real.rpow_neg hcn.le]
          _ = c n ^ ((1 : ℝ) + -((4 : ℝ) / 3)) := (Real.rpow_add hcn _ _).symm
          _ = (c n) ^ (-(1 / 3 : ℝ)) := by norm_num
      rw [hsub, div_pow, mul_pow, hpow43]
      calc c n * ((-uAiry (c n) (t n)) ^ 2 / (betaTip ^ 2 * (c n) ^ ((4 : ℝ) / 3)))
          = (c n / (c n) ^ ((4 : ℝ) / 3)) * ((-uAiry (c n) (t n)) ^ 2 / betaTip ^ 2) := by ring
        _ = (c n) ^ (-(1 / 3 : ℝ)) * (-uAiry (c n) (t n) / betaTip) ^ 2 := by
            rw [hpow, div_pow]
    have hlim : Tendsto (fun n => (c n) ^ (-(1 / 3 : ℝ)) * (-(uAiry (c n) (t n)) / betaTip) ^ 2)
        atTop (𝓝 0) := by
      have h13 : Tendsto (fun n => (c n) ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) :=
        (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp hc
      have h2 : Tendsto (fun n => (-(uAiry (c n) (t n)) / betaTip) ^ 2) atTop (𝓝 ((-z / betaTip) ^ 2)) :=
        ((hu.neg.div_const betaTip).pow 2)
      simpa using h13.mul h2
    exact hlim.congr' (heq.mono fun _ h => h.symm)
  -- Use `cardyV_asymptotic_real` on `x₀ = xiStar / 2`.
  obtain ⟨C_V, _, hV_as⟩ := cardyV_asymptotic_real prob (half_pos xiStar_pos)
  obtain ⟨hq0_pos, -⟩ := nullPoly_exp_bounds prob (half_pos xiStar_pos)
  have hQ_pos : 0 < prob.nullPoly (Real.exp (-4 * Real.pi * xiStar)) := by
    have := (nullPoly_exp_bounds prob (half_pos xiStar_pos)).2 (x := xiStar) (by linarith [xiStar_pos])
    linarith [hq0_pos]
  have hV_ratio : Tendsto (fun n => prob.cardyV (c n / 12) (t n) /
      ((2 * x n) ^ (prob.w - 1) * besselAs (c n * (2 * Real.pi * x n / 3))))
      atTop (𝓝 (prob.nullPoly (Real.exp (-4 * Real.pi * xiStar)))) := by
    have hQ_cont : Continuous (fun y : ℝ => prob.nullPoly (Real.exp (-4 * Real.pi * y))) := by
      have heq : (fun y : ℝ => prob.nullPoly (Real.exp (-4 * Real.pi * y))) =
          fun y : ℝ => (nullPolyExpC prob (Complex.ofReal y)).re := by
        ext y; exact congrArg Complex.re (nullPolyExpC_ofReal prob y).symm
      rw [heq]
      exact Complex.continuous_re.comp ((nullPolyExpC_entire prob).continuous.comp Complex.continuous_ofReal)
    have hQ_tend : Tendsto (fun n => prob.nullPoly (Real.exp (-4 * Real.pi * x n))) atTop
        (𝓝 (prob.nullPoly (Real.exp (-4 * Real.pi * xiStar)))) :=
      hQ_cont.continuousAt.tendsto.comp hx_tend
    have hdiff_tend : Tendsto (fun n => prob.cardyV (c n / 12) (t n) /
        ((2 * x n) ^ (prob.w - 1) * besselAs (c n * (2 * Real.pi * x n / 3))) -
        prob.nullPoly (Real.exp (-4 * Real.pi * x n))) atTop (𝓝 0) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      have hCV0 : Tendsto (fun n => C_V / c n) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop hc
      filter_upwards [hc.eventually_ge_atTop (max 1 (24 * prob.totalShift)), hpos_t,
        hx_tend.eventually (lt_mem_nhds (by linarith [xiStar_pos] : xiStar / 2 < xiStar)),
        hCV0.eventually (gt_mem_nhds hε)] with n hcm htn hxh hce
      have hc'0 : 0 < c n := lt_of_lt_of_le (by linarith [le_max_left (1 : ℝ) (24 * prob.totalShift)]) hcm
      have ht_eq : c n * x n ^ 2 / 3 = t n := by
        dsimp [x]; rw [Real.sq_sqrt (by positivity)]; field_simp [hc'0.ne']
      have h1 := hV_as hcm hxh.le
      rw [ht_eq] at h1
      rw [Real.dist_eq, sub_zero]
      exact h1.trans_lt hce
    simpa using hdiff_tend.add hQ_tend
  -- Now multiply by `jAiry` ratio and simplify the prefactors + exponential difference!
  have hpre : Tendsto (fun n => (prob.cardyV (c n / 12) (t n) /
      ((2 * x n) ^ (prob.w - 1) * besselAs (c n * (2 * Real.pi * x n / 3)))) *
      (2 * Real.sqrt (x n) * (2 * x n) ^ (prob.w - 1) / (Real.sqrt 3 * betaTip)) / amp)
      atTop (𝓝 1) := by
    have hamp_pos : 0 < amp := by
      have := xiStar_pos; have := betaTip_pos; positivity
    have hx_lim : Tendsto (fun n => (2 * Real.sqrt (x n) * (2 * x n) ^ (prob.w - 1) /
        (Real.sqrt 3 * betaTip))) atTop
        (𝓝 (2 * Real.sqrt xiStar * (2 * xiStar) ^ (prob.w - 1) / (Real.sqrt 3 * betaTip))) :=
      (((hx_tend.sqrt.const_mul 2).mul ((hx_tend.const_mul 2).pow (prob.w - 1))).div_const _)
    have hprod := (hV_ratio.mul hx_lim).div_const amp
    have heq1 : prob.nullPoly (Real.exp (-4 * Real.pi * xiStar)) *
        (2 * Real.sqrt xiStar * (2 * xiStar) ^ (prob.w - 1) / (Real.sqrt 3 * betaTip)) / amp = 1 := by
      dsimp [amp]
      field_simp [hQ_pos.ne', xiStar_pos.ne', betaTip_pos.ne',
        (Real.sqrt_pos.mpr xiStar_pos).ne']
    rwa [heq1] at hprod
  have hexp_ratio : Tendsto (fun n => Real.exp (-(Real.pi / (3 * xiStar)) * (c n * (x n - xiStar) ^ 2)))
      atTop (𝓝 1) := by
    have h0 : Tendsto (fun n => -(Real.pi / (3 * xiStar)) * (c n * (x n - xiStar) ^ 2)) atTop (𝓝 0) := by
      simpa using hquad_exp.const_mul (-(Real.pi / (3 * xiStar)))
    have hex : Tendsto (Real.exp ∘ fun n => -(Real.pi / (3 * xiStar)) * (c n * (x n - xiStar) ^ 2))
        atTop (𝓝 1) := by
      simpa [Real.exp_zero] using Real.continuous_exp.continuousAt.tendsto.comp h0
    exact hex.congr (fun _ => rfl)
  have hcomb := hpre.mul hexp_ratio
  rw [mul_one] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [hc.eventually_gt_atTop 0, hpos_t,
    hx_tend.eventually (lt_mem_nhds (by linarith [xiStar_pos] : xiStar / 2 < xiStar))] with n hcn htn hxh
  have hxn_pos : 0 < x n := lt_trans (half_pos xiStar_pos) hxh
  have hc16 : (c n) ^ (1 / 3 : ℝ) / Real.sqrt (c n) = (c n) ^ (-(1 / 6 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_neg hcn.le, ← Real.rpow_add hcn]
    congr 1; norm_num
  have hsqrt_b : Real.sqrt (2 * Real.pi * (c n * (2 * Real.pi * x n / 3))) =
      2 * Real.pi * Real.sqrt (c n) * Real.sqrt (x n) / Real.sqrt 3 := by
    have e1 : 2 * Real.pi * (c n * (2 * Real.pi * x n / 3)) =
        (2 * Real.pi) ^ 2 * (c n * x n) / 3 := by ring
    rw [e1, Real.sqrt_div (by positivity), Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq (by positivity), Real.sqrt_mul hcn.le]
    ring
  have hcexp : c n * (2 * Real.pi * x n / 3) -
      ((2 / 3 : ℝ) * Real.arsinh 1 * c n - (2 * Real.pi * z / (3 * betaTip)) * (c n) ^ ((1 : ℝ) / 3) +
        (Real.pi / xiStar) * b n) = -(Real.pi / (3 * xiStar)) * (c n * (x n - xiStar) ^ 2) := by
    have hid := cardy_exp_exact_id hcn.ne' (Real.sq_sqrt (by positivity) : x n ^ 2 = 3 * t n / c n)
    have hpc : (Real.pi / xiStar) * (cStar * z * (c n) ^ ((1 : ℝ) / 3)) =
        (2 * Real.pi * z / (3 * betaTip)) * (c n) ^ ((1 : ℝ) / 3) := by
      unfold cStar; field_simp [xiStar_pos.ne', betaTip_pos.ne']
    dsimp [b]
    linear_combination hid - hpc
  have hbessel : besselAs (c n * (2 * Real.pi * x n / 3)) =
      Real.sqrt 3 / (2 * Real.pi * Real.sqrt (c n) * Real.sqrt (x n)) *
        Real.exp (c n * (2 * Real.pi * x n / 3)) := by
    unfold besselAs
    rw [hsqrt_b, div_div_eq_mul_div]; ring
  have hj_eq : jAiry (c n) (t n) = 2 * x n * (c n) ^ ((1 : ℝ) / 3) / (3 * betaTip) := rfl
  have hexp_split : Real.exp (c n * (2 * Real.pi * x n / 3)) /
      Real.exp ((2 / 3 : ℝ) * Real.arsinh 1 * c n -
        (2 * Real.pi * z / (3 * betaTip)) * (c n) ^ ((1 : ℝ) / 3) +
        (Real.pi / xiStar) * b n) =
      Real.exp (-(Real.pi / (3 * xiStar)) * (c n * (x n - xiStar) ^ 2)) := by
    rw [← Real.exp_sub, hcexp]
  have hden0 : 0 < (2 * x n) ^ (prob.w - 1) * besselAs (c n * (2 * Real.pi * x n / 3)) :=
    mul_pos (pow_pos (by positivity) _) (besselAs_pos (by positivity))
  have hamp_pos : 0 < amp := by
    have := xiStar_pos; have := betaTip_pos; positivity
  have hc16_pos : 0 < (c n) ^ (-(1 / 6 : ℝ)) := Real.rpow_pos_of_pos hcn _
  calc (prob.cardyV (c n / 12) (t n) /
        ((2 * x n) ^ (prob.w - 1) * besselAs (c n * (2 * Real.pi * x n / 3)))) *
        (2 * Real.sqrt (x n) * (2 * x n) ^ (prob.w - 1) / (Real.sqrt 3 * betaTip)) / amp *
        Real.exp (-(Real.pi / (3 * xiStar)) * (c n * (x n - xiStar) ^ 2))
      = (prob.cardyV (c n / 12) (t n) /
          ((2 * x n) ^ (prob.w - 1) * besselAs (c n * (2 * Real.pi * x n / 3)))) *
          (2 * Real.sqrt (x n) * (2 * x n) ^ (prob.w - 1) / (Real.sqrt 3 * betaTip)) / amp *
          (Real.exp (c n * (2 * Real.pi * x n / 3)) /
            Real.exp ((2 / 3 : ℝ) * Real.arsinh 1 * c n -
              (2 * Real.pi * z / (3 * betaTip)) * (c n) ^ ((1 : ℝ) / 3) +
              (Real.pi / xiStar) * b n)) := by rw [hexp_split]
    _ = (2 * Real.pi * prob.cardyV (c n / 12) (t n) * jAiry (c n) (t n)) /
          (amp * (c n) ^ (-(1 / 6 : ℝ)) *
            Real.exp ((2 / 3 : ℝ) * Real.arsinh 1 * c n -
              (2 * Real.pi * z / (3 * betaTip)) * (c n) ^ ((1 : ℝ) / 3) +
              (Real.pi / xiStar) * b n)) := by
          rw [← hc16, hj_eq, hbessel]
          field_simp [hamp_pos.ne', hcn.ne', hxn_pos.ne', Real.pi_ne_zero, betaTip_pos.ne',
            (Real.sqrt_pos.mpr hcn).ne', (Real.sqrt_pos.mpr hxn_pos).ne',
            (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne',
            (Real.rpow_pos_of_pos hcn ((1 : ℝ) / 3)).ne',
            (Real.exp_pos (c n * (2 * Real.pi * x n / 3))).ne',
            (Real.exp_pos _).ne']
          rw [Real.sq_sqrt hxn_pos.le, Real.sq_sqrt (by norm_num)]

end FormalResearch.ModularBootstrap.FixedWeight

