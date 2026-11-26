module

public import FormalResearch.ModularBootstrap.FiveTerm.UpperSmoothEnv
public import FormalResearch.ModularBootstrap.FiveTerm.UpperPhaseChart
public import FormalResearch.ModularBootstrap.Mixtures.Source

/-!
# Assembly of the sharp upper bound from the test family (FIVE-U; `gp:U`, `app:gp-assembly`, `cts:transfer` upper half)

Source: `CFT/modular_bootstrap/paper/modular_bootstrap_gap_proof.tex` (reduction to a threshold in the phase
coordinate) and `five_term_roadmap.tex` (`app:gp-construct`, `app:gp-estimates`, `app:gp-assembly`,
`eq:gp-vacuum-expansion`-`eq:gp-upper-final`).

`SharpUpperFamily src W K G g₁ γ₀` is the content of the supplement's estimates (U1)-(U4) for the comb test
`g = ½(h_0 - 𝓗h_0)`, `h_0 = ℰ_δ B_D`, built from the smoothed minimiser `F_δ = m_δ F_*` (`δ = K_δ c'^{-1} log c'`,
`fDelta`) and shifted Chester-Friedman-Ursell pair sites, as a family `g(c',d)` indexed by the first-site shift
`d`, `|d| ≤ D c'^{-4/3} log c'`:

* (U1) `g(c',d)` is in the test class `Ā`;
* (U4) the vacuum pairing `V^tot = -g_vac/π` satisfies `V^tot/F_c = -d + (c'^{-1/3}/c_*) 𝖡[F_δ] + O(c'^{-4/3} log c')`
  (`eq:gp-vacuum-expansion`, Lemma C14 `cts:upper-vac` with `pm:tip-match`), `F_c > 0`;
* (U2)-(U4) `g(c',d) ≥ 0` for `t ≥ t(χ_1') + C_1' c'^{-1} log c'` (Lemmas C12 `cts:regionII-floor`,
  C13 `cts:shifted-langer`, with C11 `cts:upper-design`), `t(x) = c' x²/3`;
* the first-site phase `τ(χ_1') = (|a_1|+d)/β c'^{-2/3} - 3 c_1(δ)/(8√2) c'^{-1} - (|a_1|/β) γ_0 c'^{-5/3} +
  O(c'^{-2})` (`eq:gp-first-site`), `c_1(δ) = F_δ'(0) = -g_1 - δ/2` (`slope0_fDelta`).

The error constants `C_V`, `C_1'`, `C_τ` are independent of `D` (the paper's "absolute once `c' ≥ c_0(D)`"), the
threshold `c_min` depends on `D`.

**Proved here (no hypothesis beyond `SharpUpperFamily`)**: `sharp_upper_of_family` (`eq:gp-d-choice`-`eq:gp-upper-final`):
choice of `d`, `g_vac > 0`, feasibility at the gap `t(χ_1') + C_1' c'^{-1} log c'`, conversion of the first-site
phase into the dimension (`dimension_le_of_phase_le`, the Langer chart `cts:langer`), giving, for every shift
source `src`,

`Δ_best(c') ≤ c'/Λ_V + A_opt c'^{1/3} + c_0 + c_1^Langer c'^{-1/3} + d_2 c'^{-2/3} + C₊ c'^{-1} log c'`,

`c_0 = α_tip g_1`, `d_2 = (2 c_0/A_opt) c_1^Langer - A_opt γ_0`.  The Virasoro instance is
`spinless_upper_of_family` (`c_0 = c0Star`, `d_2 = d2Star`).

**Not proved**: the existence of the family, i.e. `SharpUpperFamily` itself.  It is the content of Lemmas C10-C14
(`cts:smooth-env`-`pm:tip-match`, `cts:upper-vac`); items (1) of `cts:smooth-env` and the constants/chart are
proved elsewhere in `FiveTerm/Upper*`, see `FIVEU_DESIGN.md` for the status of each label.  Non-vacuity of
`SharpUpperFamily` is not checked.
-/

@[expose] public section

open Real Filter Topology Set Complex

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.Special FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Mixtures

/-- **The test family of the sharp upper bound** (`gp:U`, estimates (U1)-(U4); see the module docstring).
The constants `K_δ, C_V, C_1', C_τ` are independent of `D`; the order is `K_δ` first, then
(`g`, `x₁`, `F_c`), then for each `D` the threshold `c_min`. -/
def SharpUpperFamily (src : ShiftSource) (W : ℝ → ℝ) (K : ℝ → ℂ) (G : ℂ → ℂ) (g1 γ0 : ℝ) : Prop :=
  ∃ (Kδ CV C1 Cτ : ℝ) (g : ℝ → ℝ → ℝ → ℝ) (x1 : ℝ → ℝ → ℝ) (Fc : ℝ → ℝ),
    0 < Kδ ∧ 0 ≤ CV ∧ 0 ≤ C1 ∧ 0 ≤ Cτ ∧
    ∀ D : ℝ, 0 < D → ∃ cmin : ℝ, ∀ c : ℝ, cmin ≤ c → 0 < Fc c ∧
      ∀ d : ℝ, |d| ≤ D * c ^ (-(4 / 3) : ℝ) * Real.log c →
        let δ := Kδ * c ^ (-1 : ℝ) * Real.log c
        TestClass src (c / 12) (g c d) ∧
        |(-(src.gVac (c / 12) (g c d)) / π) / Fc c + d -
            c ^ (-(1 / 3) : ℝ) / cStar * combB W K (fDelta G δ)| ≤
          CV * c ^ (-(4 / 3) : ℝ) * Real.log c ∧
        xiStar < x1 c d ∧
        |tauPhase (x1 c d) - ((|airyZero 1| + d) / betaTip * c ^ (-(2 / 3) : ℝ) -
            3 * (-g1 - δ / 2) / (8 * √2) * c ^ (-1 : ℝ) -
            |airyZero 1| / betaTip * γ0 * c ^ (-(5 / 3) : ℝ))| ≤ Cτ * c ^ (-2 : ℝ) ∧
        ∀ t : ℝ, c / 3 * x1 c d ^ 2 + C1 * c ^ (-1 : ℝ) * Real.log c ≤ t → 0 ≤ g c d t

lemma tendsto_delta_scale (Kδ : ℝ) :
    Tendsto (fun c : ℝ => Kδ * c ^ (-1 : ℝ) * Real.log c) atTop (𝓝 0) := by
  have h23 : Tendsto (fun c : ℝ => c ^ (-(2 / 3) : ℝ)) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  have hb : Tendsto (fun c : ℝ => 3 * |Kδ| * c ^ (-(2 / 3) : ℝ)) atTop (𝓝 0) := by
    simpa using h23.const_mul (3 * |Kδ|)
  refine squeeze_zero_norm' ?_ hb
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with c hc
  have hc0 : 0 < c := by linarith
  have hl0 : 0 ≤ Real.log c := Real.log_nonneg hc
  have hl := Real.log_le_rpow_div hc0.le (by norm_num : (0 : ℝ) < 1 / 3)
  have e : c ^ (-1 : ℝ) * c ^ (1 / 3 : ℝ) = c ^ (-(2 / 3) : ℝ) := by
    rw [← Real.rpow_add hc0]; norm_num
  have hp : 0 ≤ c ^ (-1 : ℝ) := Real.rpow_nonneg hc0.le _
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hp, abs_of_nonneg hl0]
  calc |Kδ| * c ^ (-1 : ℝ) * Real.log c ≤ |Kδ| * c ^ (-1 : ℝ) * (c ^ (1 / 3 : ℝ) / (1 / 3)) :=
        mul_le_mul_of_nonneg_left hl (by positivity)
    _ = 3 * |Kδ| * c ^ (-(2 / 3) : ℝ) := by rw [← e]; ring

/-- **Assembly of the sharp upper bound** (`eq:gp-d-choice`-`eq:gp-upper-final`): a test family
(`SharpUpperFamily`) gives, for every shift source, the five-term upper bound with the remainder
`O(c'^{-1} log c')`. -/
theorem sharp_upper_of_family {src : ShiftSource} {W : ℝ → ℝ} {K : ℝ → ℂ} {G : ℂ → ℂ} {g1 γ0 : ℝ}
    (hG : OuterDatum W K g1 G) (hF : SharpUpperFamily src W K G g1 γ0) :
    ∃ Cp c₀ : ℝ, ∀ c : ℝ, c₀ ≤ c → src.Delta_best c ≤
      c / lambdaV + Aopt * c ^ (1 / 3 : ℝ) + c0StarOf g1 + c1Langer * c ^ (-(1 / 3) : ℝ) +
        d2Of (c0StarOf g1) γ0 * c ^ (-(2 / 3) : ℝ) + Cp * c ^ (-1 : ℝ) * Real.log c := by
  obtain ⟨Kδ, CV, C1, Cτ, g, x1, Fc, hKδ, hCV, hC1, hCτ, hfam⟩ := hF
  have hcs : 0 < cStar := cStar_pos
  have hξ0 := xiStar_pos
  have hβ := betaTip_pos
  have hαT := alphaTip_pos
  have hαC := alphaC_pos
  set CV' : ℝ := max CV 1 with hCV'
  have hCV'1 : 1 ≤ CV' := le_max_right _ _
  have hCVle : CV ≤ CV' := le_max_left _ _
  set Kplus : ℝ := 2 * CV' with hKplus
  have hKplus0 : 0 < Kplus := by rw [hKplus]; linarith
  set D : ℝ := alphaTip * Kδ / cStar + Kplus with hDdef
  have hD : 0 < D := by rw [hDdef]; positivity
  obtain ⟨cmin, hcmin⟩ := hfam D hD
  set Ctot : ℝ := 3 * (25 * alphaC * Kδ ^ 2) / (2 * xiStar) + Kplus / betaTip + Cτ with hCtot
  have hCtot0 : 0 ≤ Ctot := by rw [hCtot]; positivity
  obtain ⟨Cp, c₁, hc₁, hdim⟩ := dimension_le_of_phase_le (c0StarOf g1) γ0 Ctot hCtot0
  set ε0 : ℝ := min 1 (alphaTip / (50 * alphaC)) with hε0def
  have hε0 : 0 < ε0 := lt_min one_pos (by positivity)
  obtain ⟨c₂, hc₂⟩ := eventually_atTop.1
    ((tendsto_delta_scale Kδ).eventually (gt_mem_nhds hε0))
  refine ⟨Cp + C1, max (max c₂ cmin) (max c₁ 3), fun c hc => ?_⟩
  have hc2 : c₂ ≤ c := (le_max_left _ _).trans ((le_max_left _ _).trans hc)
  have hcmin' : cmin ≤ c := (le_max_right _ _).trans ((le_max_left _ _).trans hc)
  have hc1 : c₁ ≤ c := (le_max_left _ _).trans ((le_max_right _ _).trans hc)
  have hc3 : (3 : ℝ) ≤ c := (le_max_right _ _).trans ((le_max_right _ _).trans hc)
  have hc0 : 0 < c := by linarith
  set L : ℝ := Real.log c with hLdef
  have hL1 : 1 ≤ L := by
    have : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log c := Real.log_le_log (Real.exp_pos 1) (this.trans hc3)
  have hL0 : 0 < L := by linarith
  have hLc : L ≤ c := by
    have := Real.log_le_sub_one_of_pos hc0; linarith
  -- rpow identities
  have hmul : ∀ a b : ℝ, c ^ a * c ^ b = c ^ (a + b) := fun a b => (Real.rpow_add hc0 a b).symm
  have e1 : c ^ (-(1 / 3) : ℝ) * c ^ (-(2 / 3) : ℝ) = c ^ (-1 : ℝ) := by rw [hmul]; norm_num
  have e2 : c ^ (-(4 / 3) : ℝ) * c ^ (-(2 / 3) : ℝ) = c ^ (-2 : ℝ) := by rw [hmul]; norm_num
  have e3 : c ^ (-1 : ℝ) * c ^ (-1 : ℝ) = c ^ (-2 : ℝ) := by rw [hmul]; norm_num
  have e4 : c ^ (-(1 / 3) : ℝ) * c ^ (-1 : ℝ) = c ^ (-(4 / 3) : ℝ) := by rw [hmul]; norm_num
  have r1pos : 0 < c ^ (-1 : ℝ) := Real.rpow_pos_of_pos hc0 _
  have r2pos : 0 < c ^ (-2 : ℝ) := Real.rpow_pos_of_pos hc0 _
  have r13pos : 0 < c ^ (-(1 / 3) : ℝ) := Real.rpow_pos_of_pos hc0 _
  have r43pos : 0 < c ^ (-(4 / 3) : ℝ) := Real.rpow_pos_of_pos hc0 _
  have r1L : c ^ (-1 : ℝ) * L ≤ 1 := by
    rw [Real.rpow_neg_one]
    calc c⁻¹ * L ≤ c⁻¹ * c := mul_le_mul_of_nonneg_left hLc (by positivity)
      _ = 1 := by field_simp
  -- δ
  set δ : ℝ := Kδ * c ^ (-1 : ℝ) * L with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  have hδε : δ < ε0 := hc₂ c hc2
  have hδ1 : δ < 1 := hδε.trans_le (min_le_left _ _)
  have hδ2 : 25 * alphaC * δ ≤ alphaTip / 2 := by
    have : δ ≤ alphaTip / (50 * alphaC) := hδε.le.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at this
    nlinarith only [this, hαC]
  -- the band part
  set B : ℝ := combB W K (fDelta G δ) with hBdef
  have hBb : |B + alphaTip / 2 * δ| ≤ 25 * alphaC * δ ^ 2 := combB_fDelta_bounds hG hδ0 hδ1
  have hBabs : |B| ≤ alphaTip * δ := by
    have h1 := (abs_le.mp hBb)
    have h2 : 25 * alphaC * δ ^ 2 ≤ alphaTip / 2 * δ := by
      have := mul_le_mul_of_nonneg_right hδ2 hδ0.le
      nlinarith only [this]
    rw [abs_le]; constructor <;> nlinarith only [h1.1, h1.2, h2, hδ0, hαT]
  obtain ⟨hJ0, hJ1⟩ := combJ_fDelta_bounds hG hδ0 hδ1
  have hJB := combJ_fDelta_eq_B hG hδ0 hδ1
  -- the choice of d
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = c ^ (-(1 / 3) : ℝ) / cStar * B + Kplus * c ^ (-(4 / 3) : ℝ) * L := ⟨_, rfl⟩
  have hdbd : |d| ≤ D * c ^ (-(4 / 3) : ℝ) * L := by
    have h1 : |c ^ (-(1 / 3) : ℝ) / cStar * B| ≤ alphaTip * Kδ / cStar * c ^ (-(4 / 3) : ℝ) * L := by
      rw [abs_mul, abs_of_pos (div_pos r13pos hcs)]
      calc c ^ (-(1 / 3) : ℝ) / cStar * |B| ≤ c ^ (-(1 / 3) : ℝ) / cStar * (alphaTip * δ) :=
            mul_le_mul_of_nonneg_left hBabs (by positivity)
        _ = alphaTip * Kδ / cStar * (c ^ (-(1 / 3) : ℝ) * c ^ (-1 : ℝ)) * L := by
            rw [hδdef]; ring
        _ = _ := by rw [e4]
    have h2 : |Kplus * c ^ (-(4 / 3) : ℝ) * L| = Kplus * c ^ (-(4 / 3) : ℝ) * L := abs_of_pos (by positivity)
    rw [hd]
    calc _ ≤ |c ^ (-(1 / 3) : ℝ) / cStar * B| + |Kplus * c ^ (-(4 / 3) : ℝ) * L| := abs_add_le _ _
      _ ≤ alphaTip * Kδ / cStar * c ^ (-(4 / 3) : ℝ) * L + Kplus * c ^ (-(4 / 3) : ℝ) * L := by
          rw [h2]; exact add_le_add h1 le_rfl
      _ = D * c ^ (-(4 / 3) : ℝ) * L := by rw [hDdef]; ring
  obtain ⟨hFc, hfam'⟩ := hcmin c hcmin'
  obtain ⟨htest, hvac, hx1, hphase, hpos⟩ := hfam' d hdbd
  -- g_vac > 0
  have hVneg : (-(src.gVac (c / 12) (g c d)) / π) / Fc c < 0 := by
    have h1 := (abs_le.mp hvac).2
    have hcb : c ^ (-(1 / 3) : ℝ) / cStar * B = d - Kplus * c ^ (-(4 / 3) : ℝ) * L := by rw [hd]; ring
    have hk : CV * c ^ (-(4 / 3) : ℝ) * L ≤ CV' * c ^ (-(4 / 3) : ℝ) * L := by
      have : 0 ≤ c ^ (-(4 / 3) : ℝ) * L := by positivity
      nlinarith only [hCVle, this]
    have hp : 0 < CV' * c ^ (-(4 / 3) : ℝ) * L := by positivity
    rw [hcb] at h1
    nlinarith only [h1, hk, hp, hKplus]
  have hgvac : 0 < src.gVac (c / 12) (g c d) := by
    have h1 : (-(src.gVac (c / 12) (g c d)) / π) < 0 := by
      by_contra hcon
      push Not at hcon
      have := div_nonneg hcon hFc.le
      linarith
    have hpi := Real.pi_pos
    rw [div_neg_iff] at h1
    rcases h1 with ⟨h, h'⟩ | ⟨h, h'⟩
    · exact absurd h' (not_lt.mpr hpi.le)
    · linarith
  -- feasibility and the threshold
  set T : ℝ := c / 3 * x1 c d ^ 2 + C1 * c ^ (-1 : ℝ) * L with hTdef
  have hx1pos : 0 < x1 c d := hξ0.trans hx1
  have hTpos : 0 < T := by rw [hTdef]; positivity
  have hfeas : src.IsFeasible (c / 12) T (g c d) := ⟨htest, hgvac, fun t ht => hpos t ht⟩
  have hTV : src.T_V c ≤ T :=
    csInf_le ⟨0, fun T' hT' => hT'.1.le⟩ ⟨hTpos, g c d, hfeas⟩
  -- the first-site phase
  have hphase' : tauPhase (x1 c d) ≤ tauStar (c0StarOf g1) γ0 c + Ctot * c ^ (-2 : ℝ) * L := by
    have hτ := (abs_le.mp hphase).2
    have hdr : d * c ^ (-(2 / 3) : ℝ) = c ^ (-1 : ℝ) * B / cStar + Kplus * c ^ (-2 : ℝ) * L := by
      rw [hd]; linear_combination (B / cStar) * e1 + (Kplus * L) * e2
    have hβcs : betaTip * cStar = 2 * xiStar / 3 := by
      unfold cStar; field_simp
    have hJ : combJ W K (fDelta G δ) = B + alphaTip * (g1 + δ / 2) := by
      rw [hJB]; ring
    have hat : alphaTip = xiStar / (4 * √2) := rfl
    have hsq : (0 : ℝ) < √2 := Real.sqrt_pos.mpr (by norm_num)
    -- the bracket
    have hbr : B / (betaTip * cStar) - 3 * (-g1 - δ / 2) / (8 * √2) =
        3 / (2 * xiStar) * combJ W K (fDelta G δ) := by
      rw [hβcs, hJ, hat]
      field_simp
      ring
    have hX : (|airyZero 1| + d) / betaTip * c ^ (-(2 / 3) : ℝ) -
        3 * (-g1 - δ / 2) / (8 * √2) * c ^ (-1 : ℝ) -
        |airyZero 1| / betaTip * γ0 * c ^ (-(5 / 3) : ℝ) =
        sLanger * c ^ (-(2 / 3) : ℝ) - sLanger * γ0 * c ^ (-(5 / 3) : ℝ) +
          c ^ (-1 : ℝ) * (3 / (2 * xiStar) * combJ W K (fDelta G δ)) +
          Kplus / betaTip * c ^ (-2 : ℝ) * L := by
      rw [← hbr]
      have : (|airyZero 1| + d) / betaTip * c ^ (-(2 / 3) : ℝ) =
          sLanger * c ^ (-(2 / 3) : ℝ) + (d * c ^ (-(2 / 3) : ℝ)) / betaTip := by
        unfold sLanger; field_simp
      rw [this, hdr]
      unfold sLanger
      field_simp
      ring
    rw [hX] at hτ
    -- J bound
    have hJle : combJ W K (fDelta G δ) ≤ c0StarOf g1 + 25 * alphaC * δ ^ 2 := by linarith only [hJ1]
    have hq : 3 / (2 * xiStar) * combJ W K (fDelta G δ) ≤
        3 * c0StarOf g1 / (2 * xiStar) + 3 * (25 * alphaC) / (2 * xiStar) * δ ^ 2 := by
      have := mul_le_mul_of_nonneg_left hJle (by positivity : 0 ≤ 3 / (2 * xiStar))
      calc _ ≤ 3 / (2 * xiStar) * (c0StarOf g1 + 25 * alphaC * δ ^ 2) := this
        _ = _ := by ring
    have hr1d : c ^ (-1 : ℝ) * δ ^ 2 ≤ Kδ ^ 2 * c ^ (-2 : ℝ) * L := by
      have hδsq : δ ^ 2 = Kδ ^ 2 * (c ^ (-1 : ℝ) * c ^ (-1 : ℝ)) * L ^ 2 := by rw [hδdef]; ring
      have : c ^ (-1 : ℝ) * δ ^ 2 = Kδ ^ 2 * c ^ (-2 : ℝ) * L * (c ^ (-1 : ℝ) * L) := by
        rw [hδsq, ← e3]; ring
      rw [this]
      have : 0 ≤ Kδ ^ 2 * c ^ (-2 : ℝ) * L := by positivity
      nlinarith only [this, r1L]
    have hmain : c ^ (-1 : ℝ) * (3 / (2 * xiStar) * combJ W K (fDelta G δ)) ≤
        c ^ (-1 : ℝ) * (3 * c0StarOf g1 / (2 * xiStar)) +
          3 * (25 * alphaC) / (2 * xiStar) * (Kδ ^ 2 * c ^ (-2 : ℝ) * L) := by
      have h1 := mul_le_mul_of_nonneg_left hq r1pos.le
      have h2 : c ^ (-1 : ℝ) * (3 * (25 * alphaC) / (2 * xiStar) * δ ^ 2) ≤
          3 * (25 * alphaC) / (2 * xiStar) * (Kδ ^ 2 * c ^ (-2 : ℝ) * L) := by
        have := mul_le_mul_of_nonneg_left hr1d (by positivity : 0 ≤ 3 * (25 * alphaC) / (2 * xiStar))
        calc c ^ (-1 : ℝ) * (3 * (25 * alphaC) / (2 * xiStar) * δ ^ 2)
            = 3 * (25 * alphaC) / (2 * xiStar) * (c ^ (-1 : ℝ) * δ ^ 2) := by ring
          _ ≤ _ := this
      calc _ ≤ c ^ (-1 : ℝ) * (3 * c0StarOf g1 / (2 * xiStar) +
            3 * (25 * alphaC) / (2 * xiStar) * δ ^ 2) := h1
        _ = c ^ (-1 : ℝ) * (3 * c0StarOf g1 / (2 * xiStar)) +
            c ^ (-1 : ℝ) * (3 * (25 * alphaC) / (2 * xiStar) * δ ^ 2) := by ring
        _ ≤ _ := by linarith only [h2]
    have hstar : tauStar (c0StarOf g1) γ0 c = sLanger * c ^ (-(2 / 3) : ℝ) +
        3 * c0StarOf g1 / (2 * xiStar) * c ^ (-1 : ℝ) - sLanger * γ0 * c ^ (-(5 / 3) : ℝ) := rfl
    have hCτ2 : Cτ * c ^ (-2 : ℝ) ≤ Cτ * c ^ (-2 : ℝ) * L := by
      have : 0 ≤ Cτ * c ^ (-2 : ℝ) := by positivity
      nlinarith only [this, hL1]
    have hK2 : Kplus / betaTip * c ^ (-2 : ℝ) * L = Kplus / betaTip * c ^ (-2 : ℝ) * L := rfl
    have hCt : Ctot * c ^ (-2 : ℝ) * L =
        3 * (25 * alphaC) / (2 * xiStar) * (Kδ ^ 2 * c ^ (-2 : ℝ) * L) / 1 +
          Kplus / betaTip * c ^ (-2 : ℝ) * L + Cτ * c ^ (-2 : ℝ) * L := by
      rw [hCtot]; ring
    rw [hstar, hCt]
    linarith only [hτ, hmain, hCτ2]
  have hd2 := hdim c hc1 (x1 c d) hx1 hphase'
  have hDb : src.Delta_best c ≤ c / 12 + T := by
    unfold ShiftSource.Delta_best
    linarith only [hTV]
  rw [hTdef] at hDb
  nlinarith only [hDb, hd2, hC1, r1pos, hL0]

open FormalResearch.ModularBootstrap.Crossing in
/-- **Upper half of `thm:spinless-expansion` (`cts:transfer`, Virasoro), modulo the test family**: if the
Virasoro problem has a `SharpUpperFamily` for the Virasoro outer function (`W = Wslit`, `K = Kedge`,
`G = Gout`, `g₁ = g1Vir`, `γ₀ = gamma0`), then for `c'` large
`Δ_best(c') ≤ c'/Λ_V + A_opt c'^{1/3} + c_0^* + c_1^Langer c'^{-1/3} + d_2^* c'^{-2/3} + C₊ c'^{-1} log c'`
with the closed forms `c0Star`, `d2Star`. -/
theorem spinless_upper_of_family
    (hF : SharpUpperFamily (ShiftSource.ofProblem virasoroProblem) Wslit Kedge Gout g1Vir gamma0) :
    ∃ Cp c₀ : ℝ, ∀ c : ℝ, c₀ ≤ c → virasoroProblem.Delta_best c ≤
      c / lambdaV + Aopt * c ^ (1 / 3 : ℝ) + c0Star + c1Langer * c ^ (-(1 / 3) : ℝ) +
        d2Star * c ^ (-(2 / 3) : ℝ) + Cp * c ^ (-1 : ℝ) * Real.log c := by
  have hG : OuterDatum Wslit Kedge g1Vir Gout := g1Out_eq_g1Vir ▸ gout_outerDatum_g1Out
  obtain ⟨Cp, c₀, h⟩ := sharp_upper_of_family hG hF
  refine ⟨Cp, c₀, fun c hc => ?_⟩
  rw [← ofProblem_Delta_best]
  have := h c hc
  rw [← c0Star_eq_c0StarOf] at this
  exact this

end FormalResearch.ModularBootstrap.FiveTerm

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.sharp_upper_of_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.sharp_upper_of_family

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.spinless_upper_of_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.spinless_upper_of_family
