module

public import FormalResearch.ModularBootstrap.FiveTerm.LangerExpansion

/-!
# From the phase of the first site to the dimension (FIVE-U; `gp:E5`, `eq:gp-five-terms`)

Source: `CFT/modular_bootstrap/paper/modular_bootstrap_gap_proof.tex` (reduction to a threshold in the phase
coordinate, `eq:gp-tau-star`-`eq:gp-five-terms`; `gp:U` (U5)) and `constant_term_slit_strip.tex`
(`cts:langer`, `eq:gp-upper-final`).

With the Langer phase `τ(x) = (N(x)/k_tip)^{2/3}` (`tauPhase`) and the threshold `t = c' x²/3`
(dimension `Δ = c'/12 + t`):

* `dimension_chart_expansion`: for `ξ_* < x`, `π (x - ξ_*) ≤ 1/10`, `ε = τ(x)`,
  `|c'/12 + c' x²/3 - (c'/Λ_V + (2ξ_*/3) c' ε + K_2 c' ε²)| ≤ 6 c' ε³`, `K_2 = 1/3 - π ξ_*/(45√2)`;
* `dimension_le_of_phase_le` (**the phase-to-dimension conversion**): for arbitrary reals `c_0`, `γ_0` (in the
  application `c_0^*(w,Q) = α_tip g_1`, `γ_0(w,Q)`) and `C ≥ 0` there are `C₊`, `c₁` such that for all
  `c' ≥ c₁` and every `x > ξ_*` whose phase satisfies
  `τ(x) ≤ τ_*(c') + C c'^{-2} log c'`, with `τ_* = p c'^{-2/3} + q_* c'^{-1} - p γ_0 c'^{-5/3}`,
  `p = |a_1|/β`, `q_* = 3 c_0/(2 ξ_*)` (`eq:gp-tau-star`),
  `c'/12 + c' x²/3 ≤ c'/Λ_V + A_opt c'^{1/3} + c_0 + c_1^Langer c'^{-1/3} + d_2 c'^{-2/3} + C₊ c'^{-1} log c'`,
  `d_2 = (2 c_0/A_opt) c_1^Langer - A_opt γ_0` (`d2Of`; `d2StarOf g₁ g₃` when `c_0 = c0StarOf g₁`,
  `γ_0 = gamma0Of g₁ g₃`).

The conversion is generic in `(c_0, γ_0)`.  The inversion of the chart is the existing `inversion_aux`.
All results are proved unconditionally.
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.Special FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Upper.Comb

/-- The Langer phase coordinate `τ(x) = (N(x)/k_tip)^{2/3}` (`cts:langer`). -/
noncomputable def tauPhase (x : ℝ) : ℝ := (cumulN x / kTip) ^ (2 / 3 : ℝ)

/-- `K_2 = 1/3 - π ξ_*/(45√2)`, so that `c_1^Langer = K_2 (|a_1|/β)²`. -/
noncomputable def K2Langer : ℝ := 1 / 3 - π * xiStar / (45 * √2)

lemma c1Langer_eq_K2 : c1Langer = K2Langer * sLanger ^ 2 := by
  unfold c1Langer K2Langer sLanger; rfl

lemma K2Langer_pos : 0 < K2Langer := by
  have h := c1Langer_pos
  rw [c1Langer_eq_K2] at h
  have := sLanger_pos
  exact (mul_pos_iff_of_pos_right (by positivity)).mp h

/-- The `(w,Q)`-dependent `c'^{-2/3}` coefficient, `d_2 = (2 c_0/A_opt) c_1^Langer - A_opt γ_0`. -/
noncomputable def d2Of (c0 γ0 : ℝ) : ℝ := 2 * c0 / Aopt * c1Langer - Aopt * γ0

lemma d2Of_c0StarOf (g1 g3 : ℝ) : d2Of (c0StarOf g1) (gamma0Of g1 g3) = d2StarOf g1 g3 := rfl

/-- The target phase `τ_*(c') = p c'^{-2/3} + q_* c'^{-1} - p γ_0 c'^{-5/3}`, `q_* = 3 c_0/(2 ξ_*)`
(`eq:gp-tau-star`). -/
noncomputable def tauStar (c0 γ0 c : ℝ) : ℝ :=
  sLanger * c ^ (-(2 / 3) : ℝ) + 3 * c0 / (2 * xiStar) * c ^ (-1 : ℝ) -
    sLanger * γ0 * c ^ (-(5 / 3) : ℝ)

lemma inv_lambdaV_eq_xi : 1 / lambdaV = 1 / 12 + xiStar ^ 2 / 3 := by
  have h := xiBar_eq_inv_lambdaV_sub
  unfold xiBar at h
  linarith

lemma tauPhase_pos {x : ℝ} (hx : xiStar < x) : 0 < tauPhase x := by
  unfold tauPhase
  have h1 : 0 < cumulN x := by
    have := cumulN_strictMonoOn (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx.le) hx
    rwa [cumulN_xiStar] at this
  exact Real.rpow_pos_of_pos (div_pos h1 kTip_pos) _

lemma tauPhase_strictMonoOn : StrictMonoOn tauPhase (Set.Ici xiStar) := by
  intro a ha b hb hab
  unfold tauPhase
  have hk := kTip_pos
  have ha0 : 0 ≤ cumulN a := by
    have := cumulN_strictMonoOn.monotoneOn (Set.mem_Ici.mpr le_rfl) ha (Set.mem_Ici.mp ha)
    rwa [cumulN_xiStar] at this
  have hlt := cumulN_strictMonoOn ha hb hab
  exact Real.rpow_lt_rpow (div_nonneg ha0 hk.le) ((div_lt_div_iff_of_pos_right hk).mpr hlt) (by norm_num)

/-- **Chart expansion of the dimension in the phase** (`eq:gp-five-terms`, one step): for `ξ_* < x = ξ_* + r`,
`π r ≤ 1/10`, `ε = τ(x)`:
`|c/12 + (c/3) x² - (c/Λ_V + (2ξ_*/3) c ε + K_2 c ε²)| ≤ 6 c ε³`. -/
theorem dimension_chart_expansion {c r : ℝ} (hc : 0 < c) (hr : 0 < r) (hr1 : π * r ≤ 1 / 10) :
    |c / 12 + c / 3 * (xiStar + r) ^ 2 -
      (c / lambdaV + 2 * xiStar / 3 * c * tauPhase (xiStar + r) +
        K2Langer * c * tauPhase (xiStar + r) ^ 2)| ≤ 6 * c * tauPhase (xiStar + r) ^ 3 := by
  have hpi := Real.pi_pos
  have hr30 : r ≤ 1 / 30 := by nlinarith only [hr1, Real.pi_gt_three, hr]
  have hτ := tau_tip_expansion hr hr1
  obtain ⟨η0, η1⟩ := eta_bounds
  set ε := tauPhase (xiStar + r) with hε
  have hτ' : |ε - r - π / (30 * √2) * r ^ 2| ≤ 2 * r ^ 3 := hτ
  obtain ⟨-, hε2, hinv, hsq⟩ := inversion_aux hr hr30 η0 η1 hτ'
  have hε0 : 0 < ε := tauPhase_pos (by linarith)
  have hξ := xiStar_le_third
  have hξ0 := xiStar_pos
  have hl := inv_lambdaV_eq_xi
  have hK : K2Langer = 1 / 3 - 2 * xiStar / 3 * (π / (30 * √2)) := by
    unfold K2Langer
    have hu0 : 0 < √2 := Real.sqrt_pos.mpr (by norm_num)
    field_simp
    ring
  set η := π / (30 * √2) with hη
  have key : c / 12 + c / 3 * (xiStar + r) ^ 2 -
      (c / lambdaV + 2 * xiStar / 3 * c * ε + K2Langer * c * ε ^ 2) =
      2 * xiStar / 3 * (c * (r - (ε - η * ε ^ 2))) + c / 3 * (r ^ 2 - ε ^ 2) := by
    rw [div_eq_mul_one_div c lambdaV, hl, hK]
    ring
  rw [key]
  have hb1 : |2 * xiStar / 3 * (c * (r - (ε - η * ε ^ 2)))| ≤
      2 * xiStar / 3 * (c * (24 * ε ^ 3)) := by
    rw [abs_mul, abs_of_pos (by positivity), abs_mul, abs_of_pos hc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinv hc.le) (by positivity)
  have hb2 : |c / 3 * (r ^ 2 - ε ^ 2)| ≤ c / 3 * (2 * ε ^ 3) := by
    rw [abs_mul, abs_of_pos (by positivity)]
    exact mul_le_mul_of_nonneg_left hsq (by positivity)
  have hc3 : 0 ≤ c * ε ^ 3 := by positivity
  refine (abs_add_le _ _).trans ?_
  nlinarith only [hb1, hb2, hξ, hξ0, hc3]

/-- If `τ(x) <` the phase of `ξ_* + 1/(10π)` then `π (x - ξ_*) ≤ 1/10`. -/
lemma le_of_tauPhase_lt {x : ℝ} (hx : xiStar < x)
    (h : tauPhase x < tauPhase (xiStar + 1 / (10 * π))) : π * (x - xiStar) ≤ 1 / 10 := by
  have hpi := Real.pi_pos
  by_contra hcon
  push Not at hcon
  have : xiStar + 1 / (10 * π) ≤ x := by
    have : 1 / (10 * π) < x - xiStar := by
      rw [div_lt_iff₀ (by positivity)]; nlinarith only [hcon]
    linarith
  have hpos1 : 0 < 1 / (10 * π) := by positivity
  have hm := tauPhase_strictMonoOn.monotoneOn
    (Set.mem_Ici.mpr (by linarith)) (Set.mem_Ici.mpr hx.le) this
  linarith

/-- The polynomial-in-`u = c^{-1/3}` bookkeeping of the chart conversion. -/
lemma phase_poly_bound {a K2 p q γ C M u c : ℝ} (hK : 0 ≤ K2) (hp : 0 ≤ p) (hC : 0 ≤ C)
    (hM : 0 ≤ M) (hu : 0 < u) (hu1 : u ≤ 1) (hMu : M * u ≤ 3 * C) (hcu : c * u ^ 3 = 1) :
    a * c * (p * u ^ 2 + q * u ^ 3 - p * γ * u ^ 5 + M * u ^ 6) +
      K2 * c * (p * u ^ 2 + q * u ^ 3 - p * γ * u ^ 5 + M * u ^ 6) ^ 2 +
      6 * c * (p * u ^ 2 + q * u ^ 3 - p * γ * u ^ 5 + M * u ^ 6) ^ 3 ≤
    a * p / u + a * q - a * p * γ * u ^ 2 + a * M * u ^ 3 + K2 * p ^ 2 * u + 2 * K2 * p * q * u ^ 2 +
      (K2 * (q ^ 2 + 2 * p * (p * |γ| + 3 * C) + 2 * |q| * (p * |γ| + 3 * C) + (p * |γ| + 3 * C) ^ 2) +
        6 * (p + |q| + (p * |γ| + 3 * C)) ^ 3) * u ^ 3 := by
  set B : ℝ := p * |γ| + 3 * C with hB
  have hB0 : 0 ≤ B := by positivity
  set s : ℝ := -(p * γ * u ^ 3) + M * u ^ 4 with hs
  have hsb : |s| ≤ B * u ^ 3 := by
    have h1 : |-(p * γ * u ^ 3)| ≤ p * |γ| * u ^ 3 := by
      rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg hp, abs_of_pos (pow_pos hu 3)]
    have h2 : |M * u ^ 4| ≤ 3 * C * u ^ 3 := by
      rw [abs_mul, abs_of_nonneg hM, abs_of_pos (pow_pos hu 4)]
      calc M * u ^ 4 = (M * u) * u ^ 3 := by ring
        _ ≤ 3 * C * u ^ 3 := mul_le_mul_of_nonneg_right hMu (by positivity)
    calc |s| ≤ |-(p * γ * u ^ 3)| + |M * u ^ 4| := abs_add_le _ _
      _ ≤ p * |γ| * u ^ 3 + 3 * C * u ^ 3 := add_le_add h1 h2
      _ = B * u ^ 3 := by rw [hB]; ring
  have hε : p * u ^ 2 + q * u ^ 3 - p * γ * u ^ 5 + M * u ^ 6 = u ^ 2 * (p + q * u + s) := by
    rw [hs]; ring
  rw [hε]
  have hc : c = (u ^ 3)⁻¹ := by
    field_simp; linarith
  have hu3 : 0 < u ^ 3 := pow_pos hu 3
  -- term 1
  have e1 : a * c * (u ^ 2 * (p + q * u + s)) =
      a * p / u + a * q - a * p * γ * u ^ 2 + a * M * u ^ 3 := by
    rw [hs, hc]; field_simp; ring
  -- term 2
  have e2 : K2 * c * (u ^ 2 * (p + q * u + s)) ^ 2 =
      K2 * (p ^ 2 * u + 2 * p * q * u ^ 2 + u * (q ^ 2 * u ^ 2 + 2 * p * s + 2 * q * u * s + s ^ 2)) := by
    rw [hc]; field_simp; ring
  have hR : u * (q ^ 2 * u ^ 2 + 2 * p * s + 2 * q * u * s + s ^ 2) ≤
      (q ^ 2 + 2 * p * B + 2 * |q| * B + B ^ 2) * u ^ 3 := by
    have hsb' : |s| ≤ B * u ^ 2 := hsb.trans (by
      have : u ^ 3 ≤ u ^ 2 := pow_le_pow_of_le_one hu.le hu1 (by norm_num)
      exact mul_le_mul_of_nonneg_left this hB0)
    have t1 : q ^ 2 * u ^ 2 ≤ q ^ 2 * u ^ 2 := le_rfl
    have t2 : 2 * p * s ≤ 2 * p * (B * u ^ 2) :=
      mul_le_mul_of_nonneg_left (le_trans (le_abs_self s) hsb') (by positivity)
    have t3 : 2 * q * u * s ≤ 2 * |q| * B * u ^ 2 := by
      calc 2 * q * u * s ≤ |2 * q * u * s| := le_abs_self _
        _ = 2 * |q| * u * |s| := by
            rw [abs_mul, abs_mul, abs_mul, abs_of_pos (two_pos), abs_of_pos hu]
        _ ≤ 2 * |q| * 1 * (B * u ^ 2) := by
            gcongr
        _ = 2 * |q| * B * u ^ 2 := by ring
    have t4 : s ^ 2 ≤ B ^ 2 * u ^ 2 := by
      have : s ^ 2 = |s| ^ 2 := (sq_abs s).symm
      rw [this]
      have h5 : |s| ≤ B * u := hsb.trans (by
        have : u ^ 3 ≤ u := by
          calc u ^ 3 ≤ u ^ 1 := pow_le_pow_of_le_one hu.le hu1 (by norm_num)
            _ = u := pow_one u
        exact mul_le_mul_of_nonneg_left this hB0)
      calc |s| ^ 2 ≤ (B * u) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h5 2
        _ = B ^ 2 * u ^ 2 := by ring
    have : q ^ 2 * u ^ 2 + 2 * p * s + 2 * q * u * s + s ^ 2 ≤
        (q ^ 2 + 2 * p * B + 2 * |q| * B + B ^ 2) * u ^ 2 := by nlinarith only [t1, t2, t3, t4]
    calc u * (q ^ 2 * u ^ 2 + 2 * p * s + 2 * q * u * s + s ^ 2)
        ≤ u * ((q ^ 2 + 2 * p * B + 2 * |q| * B + B ^ 2) * u ^ 2) :=
          mul_le_mul_of_nonneg_left this hu.le
      _ = (q ^ 2 + 2 * p * B + 2 * |q| * B + B ^ 2) * u ^ 3 := by ring
  -- term 3
  have hP : |p + q * u + s| ≤ p + |q| + B := by
    calc |p + q * u + s| ≤ |p + q * u| + |s| := abs_add_le _ _
      _ ≤ (|p| + |q * u|) + |s| := by gcongr; exact abs_add_le _ _
      _ ≤ p + |q| + B := by
        have h1 : |q * u| ≤ |q| := by
          rw [abs_mul, abs_of_pos hu]; nlinarith only [abs_nonneg q, hu1]
        have h2 : |s| ≤ B := hsb.trans (by nlinarith only [hB0, pow_le_one₀ hu.le hu1 (n := 3)])
        rw [abs_of_nonneg hp]; linarith
  have e3 : 6 * c * (u ^ 2 * (p + q * u + s)) ^ 3 = 6 * u ^ 3 * (p + q * u + s) ^ 3 := by
    rw [hc]; field_simp
  have h3 : (p + q * u + s) ^ 3 ≤ (p + |q| + B) ^ 3 := by
    calc (p + q * u + s) ^ 3 ≤ |p + q * u + s| ^ 3 := by
          rw [← abs_pow]; exact le_abs_self _
      _ ≤ (p + |q| + B) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hP 3
  rw [e1, e2, e3]
  have : 6 * u ^ 3 * (p + q * u + s) ^ 3 ≤ 6 * (p + |q| + B) ^ 3 * u ^ 3 := by
    nlinarith only [h3, hu3]
  have hK2 : K2 * (u * (q ^ 2 * u ^ 2 + 2 * p * s + 2 * q * u * s + s ^ 2)) ≤
      K2 * ((q ^ 2 + 2 * p * B + 2 * |q| * B + B ^ 2) * u ^ 3) := mul_le_mul_of_nonneg_left hR hK
  nlinarith only [this, hK2]


/-- `A_opt = (2 ξ_*/3) p`, `p = |a_1|/β`. -/
lemma Aopt_eq_sLanger : Aopt = 2 * xiStar / 3 * sLanger := by
  rw [Aopt_eq_mul_abs_airyZero_div_betaTip]; unfold sLanger; ring

lemma tendsto_tauPlus (c0 γ0 C : ℝ) :
    Tendsto (fun c : ℝ => tauStar c0 γ0 c + C * c ^ (-2 : ℝ) * Real.log c) atTop (𝓝 0) := by
  have h23 : Tendsto (fun c : ℝ => c ^ (-(2 / 3) : ℝ)) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  have h1 : Tendsto (fun c : ℝ => c ^ (-1 : ℝ)) atTop (𝓝 0) := tendsto_rpow_neg_atTop (by norm_num)
  have h53 : Tendsto (fun c : ℝ => c ^ (-(5 / 3) : ℝ)) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  have h2 : Tendsto (fun c : ℝ => c ^ (-(5 / 3) : ℝ)) atTop (𝓝 0) := h53
  have hlog : Tendsto (fun c : ℝ => C * c ^ (-2 : ℝ) * Real.log c) atTop (𝓝 0) := by
    have hb : Tendsto (fun c : ℝ => 3 * |C| * c ^ (-(5 / 3) : ℝ)) atTop (𝓝 0) := by
      simpa using h53.const_mul (3 * |C|)
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with c hc
    have hc0 : 0 < c := by linarith
    have hl0 : 0 ≤ Real.log c := Real.log_nonneg hc
    have hl := Real.log_le_rpow_div hc0.le (by norm_num : (0 : ℝ) < 1 / 3)
    have e : c ^ (-2 : ℝ) * c ^ (1 / 3 : ℝ) = c ^ (-(5 / 3) : ℝ) := by
      rw [← Real.rpow_add hc0]; norm_num
    have hp : 0 ≤ c ^ (-2 : ℝ) := Real.rpow_nonneg hc0.le _
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hp, abs_of_nonneg hl0]
    calc |C| * c ^ (-2 : ℝ) * Real.log c ≤ |C| * c ^ (-2 : ℝ) * (c ^ (1 / 3 : ℝ) / (1 / 3)) :=
          mul_le_mul_of_nonneg_left hl (by positivity)
      _ = 3 * |C| * c ^ (-(5 / 3) : ℝ) := by rw [← e]; ring
  have := ((h23.const_mul sLanger).add (h1.const_mul (3 * c0 / (2 * xiStar)))).sub
    (h53.const_mul (sLanger * γ0))
  have h' := this.add hlog
  simpa [tauStar] using h'

/-- **Phase-to-dimension conversion** (`gp:E5` and the end of `eq:gp-upper-final`). -/
theorem dimension_le_of_phase_le (c0 γ0 C : ℝ) (hC : 0 ≤ C) :
    ∃ Cp c₁ : ℝ, 3 ≤ c₁ ∧ ∀ c : ℝ, c₁ ≤ c → ∀ x : ℝ, xiStar < x →
      tauPhase x ≤ tauStar c0 γ0 c + C * c ^ (-2 : ℝ) * Real.log c →
      c / 12 + c / 3 * x ^ 2 ≤ c / lambdaV + Aopt * c ^ (1 / 3 : ℝ) + c0 +
        c1Langer * c ^ (-(1 / 3) : ℝ) + d2Of c0 γ0 * c ^ (-(2 / 3) : ℝ) +
        Cp * c ^ (-1 : ℝ) * Real.log c := by
  have hpi := Real.pi_pos
  have hξ0 := xiStar_pos
  have hs0 := sLanger_pos
  have hK0 := K2Langer_pos
  set p := sLanger with hpdef
  set q := 3 * c0 / (2 * xiStar) with hqdef
  set a := 2 * xiStar / 3 with hadef
  set B := p * |γ0| + 3 * C with hBdef
  set Cpoly := K2Langer * (q ^ 2 + 2 * p * B + 2 * |q| * B + B ^ 2) + 6 * (p + |q| + B) ^ 3 with hCpoly
  have hCpoly0 : 0 ≤ Cpoly := by positivity
  set ε₁ := tauPhase (xiStar + 1 / (10 * π)) with hε₁
  have hpos1 : 0 < 1 / (10 * π) := by positivity
  have hε₁0 : 0 < ε₁ := tauPhase_pos (by linarith)
  obtain ⟨c₂, hc₂⟩ := eventually_atTop.1 (((tendsto_tauPlus c0 γ0 C).eventually (gt_mem_nhds hε₁0)).and
    (eventually_ge_atTop (3 : ℝ)))
  refine ⟨a * C + Cpoly, max c₂ 3, le_max_right _ _, fun c hc x hx hτ => ?_⟩
  obtain ⟨hεlt, hc3⟩ := hc₂ c ((le_max_left _ _).trans hc)
  have hc0 : 0 < c := by linarith
  set ε := tauPhase x with hεdef
  have hε0 : 0 < ε := tauPhase_pos hx
  have hεplus : ε < ε₁ := lt_of_le_of_lt hτ hεlt
  have hr1 := le_of_tauPhase_lt hx hεplus
  set r := x - xiStar with hrdef
  have hr0 : 0 < r := sub_pos.mpr hx
  have hxr : x = xiStar + r := by rw [hrdef]; ring
  have hchart := dimension_chart_expansion hc0 hr0 hr1
  rw [← hxr, ← hεdef] at hchart
  have hup := (abs_le.mp hchart).2
  -- u = c^{-1/3}
  set u : ℝ := c ^ (-(1 / 3) : ℝ) with hudef
  have hu0 : 0 < u := Real.rpow_pos_of_pos hc0 _
  have hu1 : u ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have pw : ∀ n : ℕ, u ^ n = c ^ (-(n / 3 : ℝ)) := fun n => by
    rw [hudef, ← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; congr 1; ring
  have e2 : c ^ (-(2 / 3) : ℝ) = u ^ 2 := by rw [pw 2]; norm_num
  have e3 : c ^ (-1 : ℝ) = u ^ 3 := by rw [pw 3]; norm_num
  have e5 : c ^ (-(5 / 3) : ℝ) = u ^ 5 := by rw [pw 5]; norm_num
  have e6 : c ^ (-2 : ℝ) = u ^ 6 := by rw [pw 6]; norm_num
  have e13 : c ^ (1 / 3 : ℝ) = 1 / u := by
    rw [eq_div_iff hu0.ne', hudef, ← Real.rpow_add hc0]; norm_num
  have hcu : c * u ^ 3 = 1 := by rw [← e3, Real.rpow_neg_one]; field_simp
  set M := C * Real.log c with hMdef
  have hlog0 : 0 ≤ Real.log c := Real.log_nonneg (by linarith)
  have hlog1 : 1 ≤ Real.log c := by
    have h3 : (3 : ℝ) ≤ c := hc3
    have : Real.exp 1 ≤ 3 := by
      have := Real.exp_one_lt_d9; linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log c := Real.log_le_log (Real.exp_pos 1) (this.trans h3)
  have hM0 : 0 ≤ M := by positivity
  have hMu : M * u ≤ 3 * C := by
    have hl := Real.log_le_rpow_div hc0.le (by norm_num : (0 : ℝ) < 1 / 3)
    have : Real.log c * u ≤ 3 := by
      calc Real.log c * u ≤ (c ^ (1 / 3 : ℝ) / (1 / 3)) * u :=
            mul_le_mul_of_nonneg_right hl hu0.le
        _ = 3 := by rw [e13]; field_simp
    calc M * u = C * (Real.log c * u) := by rw [hMdef]; ring
      _ ≤ C * 3 := mul_le_mul_of_nonneg_left this hC
      _ = 3 * C := by ring
  have hepsplus : tauStar c0 γ0 c + C * c ^ (-2 : ℝ) * Real.log c =
      p * u ^ 2 + q * u ^ 3 - p * γ0 * u ^ 5 + M * u ^ 6 := by
    unfold tauStar; rw [e2, e3, e5, e6, hMdef]; ring
  rw [hepsplus] at hτ
  -- monotonicity in ε
  have hmono : a * c * ε + K2Langer * c * ε ^ 2 + 6 * c * ε ^ 3 ≤
      a * c * (p * u ^ 2 + q * u ^ 3 - p * γ0 * u ^ 5 + M * u ^ 6) +
      K2Langer * c * (p * u ^ 2 + q * u ^ 3 - p * γ0 * u ^ 5 + M * u ^ 6) ^ 2 +
      6 * c * (p * u ^ 2 + q * u ^ 3 - p * γ0 * u ^ 5 + M * u ^ 6) ^ 3 := by
    set E := p * u ^ 2 + q * u ^ 3 - p * γ0 * u ^ 5 + M * u ^ 6
    have hE0 : 0 ≤ ε := hε0.le
    have h2 : ε ^ 2 ≤ E ^ 2 := pow_le_pow_left₀ hE0 hτ 2
    have h3 : ε ^ 3 ≤ E ^ 3 := pow_le_pow_left₀ hE0 hτ 3
    have ha0 : 0 ≤ a := by positivity
    have := mul_le_mul_of_nonneg_left hτ (by positivity : 0 ≤ a * c)
    have := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ K2Langer * c)
    have := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ 6 * c)
    nlinarith only [‹a * c * ε ≤ a * c * E›, ‹K2Langer * c * ε ^ 2 ≤ K2Langer * c * E ^ 2›,
      ‹6 * c * ε ^ 3 ≤ 6 * c * E ^ 3›]
  have hpoly := phase_poly_bound (a := a) (K2 := K2Langer) (p := p) (q := q) (γ := γ0) (C := C)
    (M := M) (u := u) (c := c) hK0.le hs0.le hC hM0 hu0 hu1 hMu hcu
  -- identities
  have hap : a * p = Aopt := by rw [Aopt_eq_sLanger]
  have haq : a * q = c0 := by
    rw [hadef, hqdef]; field_simp
  have hc1 : c1Langer = K2Langer * p ^ 2 := c1Langer_eq_K2
  have hd2 : d2Of c0 γ0 = -(a * p * γ0) + 2 * K2Langer * p * q := by
    unfold d2Of
    rw [← haq, ← hap, hc1]
    have ha0 : a ≠ 0 := by positivity
    have hp0 : p ≠ 0 := hs0.ne'
    field_simp
    ring
  have hlin : a * p / u = Aopt * c ^ (1 / 3 : ℝ) := by rw [← hap, e13]; ring
  have hfinal : c / 12 + c / 3 * x ^ 2 ≤
      c / lambdaV + Aopt * (1 / u) + c0 + c1Langer * u + d2Of c0 γ0 * u ^ 2 +
        (a * C + Cpoly) * u ^ 3 * Real.log c := by
    have h1 : c / 12 + c / 3 * x ^ 2 ≤ c / lambdaV + (a * c * ε + K2Langer * c * ε ^ 2 + 6 * c * ε ^ 3) := by
      have : 2 * xiStar / 3 = a := rfl
      rw [this] at hup
      linarith only [hup]
    have hCu : Cpoly * u ^ 3 ≤ Cpoly * u ^ 3 * Real.log c := by
      have : 0 ≤ Cpoly * u ^ 3 := by positivity
      nlinarith only [this, hlog1]
    have hlin' : a * p / u = Aopt * (1 / u) := by rw [← hap]; ring
    have hMt : a * M * u ^ 3 = a * C * u ^ 3 * Real.log c := by rw [hMdef]; ring
    rw [hd2, hc1, ← haq]
    rw [hlin', hMt] at hpoly
    nlinarith only [h1, hmono, hpoly, hCu]
  rw [e13, e2, e3]
  exact hfinal

end FormalResearch.ModularBootstrap.FiveTerm

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.dimension_chart_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.dimension_chart_expansion

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.dimension_le_of_phase_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.dimension_le_of_phase_le
