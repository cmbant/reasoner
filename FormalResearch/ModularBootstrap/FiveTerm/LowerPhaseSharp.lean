module

public import FormalResearch.ModularBootstrap.FiveTerm.LowerPhaseChart

/-!
# Log-free lower phase-to-dimension conversion (FIVE-L, `cts:lower-main`)

Log-free twin of `FiveTerm.LowerPhaseChart`: converts a log-free phase lower bound
`τ_*(c) - C c^{-2} ≤ τ(x)` (`LowerPhaseStatementSharp`) into the log-free five-term
lower bound `-C_- c^{-1}` of Theorem C9 (`cts:lower-main`, first display).
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.Special FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.Crossing

/-- **Log-free lower phase-to-dimension conversion** (the `-C_- c'^{-1}` form of `eq:gp-five-terms`,
used by `cts:lower-main` Theorem C9). -/
theorem dimension_ge_of_phase_ge_sharp (c0 γ0 C : ℝ) (hC : 0 ≤ C) :
    ∃ Cm c₁ : ℝ, 3 ≤ c₁ ∧ ∀ c : ℝ, c₁ ≤ c → ∀ x : ℝ, xiStar < x →
      tauStar c0 γ0 c - C * c ^ (-2 : ℝ) ≤ tauPhase x →
      c / lambdaV + Aopt * c ^ (1 / 3 : ℝ) + c0 + c1Langer * c ^ (-(1 / 3) : ℝ) +
        d2Of c0 γ0 * c ^ (-(2 / 3) : ℝ) - Cm * c ^ (-1 : ℝ) ≤
      c / 12 + c / 3 * x ^ 2 := by
  have hpi := Real.pi_pos
  have hξ0 := xiStar_pos
  have hs0 := sLanger_pos
  have hK0 := K2Langer_pos
  have ha := two_xiStar_div_three_ge
  set p := sLanger with hpdef
  set q := 3 * c0 / (2 * xiStar) with hqdef
  set a := 2 * xiStar / 3 with hadef
  set B := p * |γ0| + 3 * C with hBdef
  set Cpoly := K2Langer * (2 * p * B + 2 * |q| * B) + 6 * (p + |q| + B) ^ 3 with hCpoly
  have hCpoly0 : 0 ≤ Cpoly := by positivity
  set ε₁ := tauPhase (xiStar + 1 / (10 * π)) with hε₁
  set δ0 : ℝ := 1 / (10 * π) with hδ0
  have hδ0pos : 0 < δ0 := by positivity
  have hε₁0 : 0 < ε₁ := tauPhase_pos (by linarith)
  have hε₁s : ε₁ ≤ 1 / 20 := tauPhase_small
  set κ0 : ℝ := ((xiStar + δ0) ^ 2 - xiStar ^ 2) / 3 with hκ0
  have hκ0pos : 0 < κ0 := by
    rw [hκ0]; have : 0 < (xiStar + δ0) ^ 2 - xiStar ^ 2 := by nlinarith only [hξ0, hδ0pos]
    positivity
  set S : ℝ := Aopt + |c0| + |c1Langer| + |d2Of c0 γ0| with hS
  have hS0 : 0 ≤ S := by have := Aopt_pos; positivity
  set uMax : ℝ := p / (2 * (|q| + B + 1)) with huMax
  have huMax0 : 0 < uMax := by rw [huMax]; positivity
  refine ⟨a * C + Cpoly, max (max (3 : ℝ) ((S / κ0) ^ (3 / 2 : ℝ)))
    (max (uMax ^ (-3 : ℝ)) 3), le_max_of_le_right (le_max_right _ _), fun c hc x hx hτ => ?_⟩
  have hc3 : (3 : ℝ) ≤ c := ((le_max_left _ _).trans (le_max_left _ _)).trans hc
  have hcS : (S / κ0) ^ (3 / 2 : ℝ) ≤ c := ((le_max_right _ _).trans (le_max_left _ _)).trans hc
  have hcu : uMax ^ (-3 : ℝ) ≤ c := ((le_max_left _ _).trans (le_max_right _ _)).trans hc
  have hc0 : 0 < c := by linarith
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
  have hcu3 : c * u ^ 3 = 1 := by rw [← e3, Real.rpow_neg_one]; field_simp
  have hCu : C * u ≤ 3 * C := by nlinarith only [hu1, hC]
  set E : ℝ := tauStar c0 γ0 c - C * c ^ (-2 : ℝ) with hEdef
  have hEeq : E = p * u ^ 2 + q * u ^ 3 - p * γ0 * u ^ 5 - C * u ^ 6 := by
    rw [hEdef]; unfold tauStar; rw [e2, e3, e5, e6]
  set ε := tauPhase x with hεdef
  have hε0 : 0 < ε := tauPhase_pos hx
  have hEε : E ≤ ε := hτ
  have hu_le : u ≤ uMax := by
    have h2 : c ^ (-(1 / 3) : ℝ) ≤ (uMax ^ (-3 : ℝ)) ^ (-(1 / 3) : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos huMax0 _) hcu (by norm_num)
    have h3 : (uMax ^ (-3 : ℝ)) ^ (-(1 / 3) : ℝ) = uMax := by
      rw [← Real.rpow_mul huMax0.le]; norm_num
    rw [hudef]; linarith only [h2, h3]
  have hs_abs : |(-(p * γ0 * u ^ 3) - C * u ^ 4)| ≤ B * u ^ 3 := by
    have hu3 : 0 < u ^ 3 := pow_pos hu0 3
    have h1 : |-(p * γ0 * u ^ 3)| ≤ p * |γ0| * u ^ 3 := by
      rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg hs0.le, abs_of_pos hu3]
    have h2 : |C * u ^ 4| ≤ 3 * C * u ^ 3 := by
      rw [abs_mul, abs_of_nonneg hC, abs_of_pos (pow_pos hu0 4)]
      calc C * u ^ 4 = (C * u) * u ^ 3 := by ring
        _ ≤ 3 * C * u ^ 3 := mul_le_mul_of_nonneg_right hCu hu3.le
    calc |(-(p * γ0 * u ^ 3) - C * u ^ 4)| = |-(p * γ0 * u ^ 3) + -(C * u ^ 4)| := by ring_nf
      _ ≤ |-(p * γ0 * u ^ 3)| + |-(C * u ^ 4)| := abs_add_le _ _
      _ = |-(p * γ0 * u ^ 3)| + |C * u ^ 4| := by rw [abs_neg (C * u ^ 4)]
      _ ≤ p * |γ0| * u ^ 3 + 3 * C * u ^ 3 := add_le_add h1 h2
      _ = B * u ^ 3 := by rw [hBdef]; ring
  have hE0 : 0 ≤ E := by
    have hB0 : 0 ≤ B := by positivity
    have hq : -(|q| * u) ≤ q * u := by
      have := neg_abs_le q
      nlinarith only [this, hu0]
    have hsl : -(B * u ^ 3) ≤ (-(p * γ0 * u ^ 3) - C * u ^ 4) := by
      have := neg_abs_le (-(p * γ0 * u ^ 3) - C * u ^ 4)
      linarith only [this, hs_abs]
    have hBu : B * u ^ 3 ≤ B * u := by
      have : u ^ 3 ≤ u := by
        calc u ^ 3 ≤ u ^ 1 := pow_le_pow_of_le_one hu0.le hu1 (by norm_num)
          _ = u := pow_one u
      exact mul_le_mul_of_nonneg_left this hB0
    have hpos : 0 ≤ p + q * u + (-(p * γ0 * u ^ 3) - C * u ^ 4) := by
      have h4 : (|q| + B) * u ≤ p / 2 := by
        have : u ≤ p / (2 * (|q| + B + 1)) := hu_le
        rw [le_div_iff₀ (by positivity)] at this
        nlinarith only [this, abs_nonneg q, hB0, hu0]
      nlinarith only [hq, hsl, hBu, h4, hs0]
    rw [hEeq]
    have : p * u ^ 2 + q * u ^ 3 - p * γ0 * u ^ 5 - C * u ^ 6 =
        u ^ 2 * (p + q * u + (-(p * γ0 * u ^ 3) - C * u ^ 4)) := by ring
    rw [this]; positivity
  by_cases hbig : ε₁ ≤ ε
  · have hxlow : xiStar + δ0 ≤ x := by
      by_contra hcon
      push Not at hcon
      have := tauPhase_strictMonoOn (Set.mem_Ici.mpr hx.le) (Set.mem_Ici.mpr (by linarith)) hcon
      linarith only [this, hbig, hε₁, hεdef]
    have hsq : (xiStar + δ0) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ (by linarith) hxlow 2
    have hD : c / 12 + c / 3 * (xiStar + δ0) ^ 2 ≤ c / 12 + c / 3 * x ^ 2 := by
      nlinarith only [hsq, hc0]
    have hl := inv_lambdaV_eq_xi
    have hbase : c / lambdaV + c * κ0 = c / 12 + c / 3 * (xiStar + δ0) ^ 2 := by
      rw [div_eq_mul_one_div c lambdaV, hl, hκ0]; ring
    have hcκ : S * c ^ (1 / 3 : ℝ) ≤ c * κ0 := by
      have h23 : (S / κ0) ≤ c ^ (2 / 3 : ℝ) := by
        have := Real.rpow_le_rpow (by positivity) hcS (by norm_num : (0 : ℝ) ≤ 2 / 3)
        rwa [← Real.rpow_mul (by positivity), show (3 / 2 : ℝ) * (2 / 3) = 1 by norm_num,
          Real.rpow_one] at this
      have hc23 : c = c ^ (2 / 3 : ℝ) * c ^ (1 / 3 : ℝ) := by
        rw [← Real.rpow_add hc0]; norm_num
      have h1 : S ≤ κ0 * c ^ (2 / 3 : ℝ) := by
        rw [div_le_iff₀ hκ0pos] at h23; linarith only [h23]
      have hc13 : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
      calc S * c ^ (1 / 3 : ℝ) ≤ κ0 * c ^ (2 / 3 : ℝ) * c ^ (1 / 3 : ℝ) :=
            mul_le_mul_of_nonneg_right h1 hc13.le
        _ = c * κ0 := by rw [mul_assoc, ← hc23]; ring
    have hrhs : Aopt * c ^ (1 / 3 : ℝ) + c0 + c1Langer * c ^ (-(1 / 3) : ℝ) +
        d2Of c0 γ0 * c ^ (-(2 / 3) : ℝ) - (a * C + Cpoly) * c ^ (-1 : ℝ) ≤
        S * c ^ (1 / 3 : ℝ) := by
      have hc13 : 1 ≤ c ^ (1 / 3 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
      have hu1' : c ^ (-(1 / 3) : ℝ) ≤ 1 := hu1
      have hu2' : c ^ (-(2 / 3) : ℝ) ≤ 1 := by
        rw [e2]; exact pow_le_one₀ hu0.le hu1
      have t1 : c1Langer * c ^ (-(1 / 3) : ℝ) ≤ |c1Langer| * c ^ (1 / 3 : ℝ) := by
        calc c1Langer * c ^ (-(1 / 3) : ℝ) ≤ |c1Langer| * c ^ (-(1 / 3) : ℝ) :=
              mul_le_mul_of_nonneg_right (le_abs_self _) hu0.le
          _ ≤ |c1Langer| * 1 := mul_le_mul_of_nonneg_left hu1' (abs_nonneg _)
          _ ≤ |c1Langer| * c ^ (1 / 3 : ℝ) := mul_le_mul_of_nonneg_left hc13 (abs_nonneg _)
          _ = _ := rfl
      have t2 : d2Of c0 γ0 * c ^ (-(2 / 3) : ℝ) ≤ |d2Of c0 γ0| * c ^ (1 / 3 : ℝ) := by
        have hu20 : 0 ≤ c ^ (-(2 / 3) : ℝ) := by rw [e2]; positivity
        calc d2Of c0 γ0 * c ^ (-(2 / 3) : ℝ) ≤ |d2Of c0 γ0| * c ^ (-(2 / 3) : ℝ) :=
              mul_le_mul_of_nonneg_right (le_abs_self _) hu20
          _ ≤ |d2Of c0 γ0| * 1 := mul_le_mul_of_nonneg_left hu2' (abs_nonneg _)
          _ ≤ |d2Of c0 γ0| * c ^ (1 / 3 : ℝ) := mul_le_mul_of_nonneg_left hc13 (abs_nonneg _)
      have t0 : c0 ≤ |c0| * c ^ (1 / 3 : ℝ) := by
        calc c0 ≤ |c0| := le_abs_self _
          _ = |c0| * 1 := (mul_one _).symm
          _ ≤ |c0| * c ^ (1 / 3 : ℝ) := mul_le_mul_of_nonneg_left hc13 (abs_nonneg _)
      have tl : 0 ≤ (a * C + Cpoly) * c ^ (-1 : ℝ) := by
        rw [e3]; have : 0 ≤ a * C + Cpoly := by positivity
        positivity
      nlinarith only [t0, t1, t2, tl, hS]
    linarith only [hD, hbase, hcκ, hrhs]
  · push Not at hbig
    have hr1 := le_of_tauPhase_lt hx hbig
    set r := x - xiStar with hrdef
    have hr0 : 0 < r := sub_pos.mpr hx
    have hxr : x = xiStar + r := by rw [hrdef]; ring
    have hchart := dimension_chart_expansion hc0 hr0 hr1
    rw [← hxr, ← hεdef] at hchart
    have hlow := (abs_le.mp hchart).1
    have hεs : ε ≤ 1 / 20 := hbig.le.trans hε₁s
    have hmono := cubic_mono (a := a) (K2 := K2Langer) ha hK0.le hE0 hEε hεs
    have hpoly := phase_poly_lower (a := a) (K2 := K2Langer) (p := p) (q := q) (γ := γ0) (C := C)
      (M := C) (u := u) (c := c) hK0.le hs0.le hC hC hu0 hu1 hCu hcu3
    rw [← hEeq] at hpoly
    have hap : a * p = Aopt := by rw [Aopt_eq_sLanger]
    have haq : a * q = c0 := by rw [hadef, hqdef]; field_simp
    have hc1 : c1Langer = K2Langer * p ^ 2 := c1Langer_eq_K2
    have hd2 : d2Of c0 γ0 = -(a * p * γ0) + 2 * K2Langer * p * q := by
      unfold d2Of
      rw [← haq, ← hap, hc1]
      have ha0 : a ≠ 0 := by positivity
      have hp0 : p ≠ 0 := hs0.ne'
      field_simp; ring
    have hlin' : a * p / u = Aopt * (1 / u) := by rw [← hap]; ring
    have hcmono : c * (a * E + K2Langer * E ^ 2 - 6 * E ^ 3) ≤
        c * (a * ε + K2Langer * ε ^ 2 - 6 * ε ^ 3) :=
      mul_le_mul_of_nonneg_left hmono hc0.le
    have hexp : c * (a * E + K2Langer * E ^ 2 - 6 * E ^ 3) =
        a * c * E + K2Langer * c * E ^ 2 - 6 * c * E ^ 3 := by ring
    have hexp2 : c * (a * ε + K2Langer * ε ^ 2 - 6 * ε ^ 3) =
        a * c * ε + K2Langer * c * ε ^ 2 - 6 * c * ε ^ 3 := by ring
    have hl := inv_lambdaV_eq_xi
    have h1 : c / lambdaV + (a * c * ε + K2Langer * c * ε ^ 2 - 6 * c * ε ^ 3) ≤
        c / 12 + c / 3 * x ^ 2 := by
      have : 2 * xiStar / 3 = a := rfl
      rw [this] at hlow
      linarith only [hlow]
    rw [e13, e2, e3, hd2, hc1, ← haq]
    rw [hlin'] at hpoly
    nlinarith only [h1, hcmono, hexp, hexp2, hpoly]

/-- **Log-free phase statement** (Theorem C9, `cts:lower-main`): every weakly feasible test at `(c/12, T)`
has a point `x > ξ_*` with `τ_*(c) - C c^{-2} ≤ τ(x)` and `c x^2 / 3 ≤ T`. -/
def LowerPhaseStatementSharp (prob : FixedWeightProblem) (c0 γ0 C : ℝ) : Prop :=
  ∃ c₂ : ℝ, ∀ c : ℝ, c₂ ≤ c → ∀ (T : ℝ) (g : ℝ → ℝ), prob.IsWeaklyFeasible (c / 12) T g →
    ∃ x : ℝ, xiStar < x ∧ tauStar c0 γ0 c - C * c ^ (-2 : ℝ) ≤ tauPhase x ∧
      c / 3 * x ^ 2 ≤ T

/-- The log-free phase statement implies the log-bearing `LowerPhaseStatement` (`gp:L`). -/
theorem lowerPhaseStatement_of_sharp {prob : FixedWeightProblem} {c0 γ0 C : ℝ} (hC : 0 ≤ C)
    (hL : LowerPhaseStatementSharp prob c0 γ0 C) : LowerPhaseStatement prob c0 γ0 C := by
  obtain ⟨c₂, hc₂⟩ := hL
  refine ⟨max c₂ 3, fun c hc T g hg => ?_⟩
  have hc3 : 3 ≤ c := (le_max_right _ _).trans hc
  have hc0 : 0 < c := by linarith
  obtain ⟨x, hx, hτ, hxT⟩ := hc₂ c ((le_max_left _ _).trans hc) T g hg
  have hlog : 1 ≤ Real.log c := by
    rw [Real.le_log_iff_exp_le hc0]
    linarith [Real.exp_one_lt_d9]
  have hc2 : 0 ≤ C * c ^ (-2 : ℝ) := mul_nonneg hC (Real.rpow_nonneg hc0.le _)
  refine ⟨x, hx, ?_, hxT⟩
  nlinarith only [hτ, mul_le_mul_of_nonneg_left hlog hc2]

/-- **Log-free lower half of `cts:lower-main` for general `prob`**, conditional on
`LowerPhaseStatementSharp`. -/
theorem delta_best_ge_of_phase_sharp (prob : FixedWeightProblem) (c0 γ0 C : ℝ) (hC : 0 ≤ C)
    (hL : LowerPhaseStatementSharp prob c0 γ0 C) :
    ∃ Cm c₁ : ℝ, ∀ c : ℝ, c₁ ≤ c →
      c / lambdaV + Aopt * c ^ (1 / 3 : ℝ) + c0 + c1Langer * c ^ (-(1 / 3) : ℝ) +
        d2Of c0 γ0 * c ^ (-(2 / 3) : ℝ) - Cm * c ^ (-1 : ℝ) ≤ prob.Delta_best c := by
  obtain ⟨Cm, c₁, hc₁, hconv⟩ := dimension_ge_of_phase_ge_sharp c0 γ0 C hC
  obtain ⟨c₂, hc₂⟩ := hL
  refine ⟨Cm, max (max c₁ c₂) (12 * prob.totalShift), fun c hc => ?_⟩
  have hc1 : c₁ ≤ c := (le_max_left _ _).trans ((le_max_left _ _).trans hc)
  have hc2 : c₂ ≤ c := (le_max_right _ _).trans ((le_max_left _ _).trans hc)
  have hsh : 12 * prob.totalShift ≤ c := (le_max_right _ _).trans hc
  have hne : {T : ℝ | 0 < T ∧ ∃ g, prob.IsFeasible (c / 12) T g}.Nonempty :=
    prob.feasible_nonempty hsh
  unfold FixedWeightProblem.Delta_best FixedWeightProblem.T_V
  have hT : c / lambdaV + Aopt * c ^ (1 / 3 : ℝ) + c0 + c1Langer * c ^ (-(1 / 3) : ℝ) +
        d2Of c0 γ0 * c ^ (-(2 / 3) : ℝ) - Cm * c ^ (-1 : ℝ) - c / 12 ≤
      sInf {T : ℝ | 0 < T ∧ ∃ g, prob.IsFeasible (c / 12) T g} := by
    refine le_csInf hne ?_
    rintro T ⟨_, g, hg⟩
    obtain ⟨x, hx, hτ, hxT⟩ := hc₂ c hc2 T g hg.isWeaklyFeasible
    have := hconv c hc1 x hx hτ
    linarith only [this, hxT]
  linarith only [hT]

/-- The Virasoro instance of `delta_best_ge_of_phase_sharp` (`cts:lower-main`, Theorem C9 first display,
conditional on `LowerPhaseStatementSharp`). -/
theorem spinless_lower_of_phase_sharp (c0 γ0 C : ℝ) (hC : 0 ≤ C)
    (hL : LowerPhaseStatementSharp virasoroProblem c0 γ0 C) :
    ∃ Cm c₁ : ℝ, ∀ c : ℝ, c₁ ≤ c →
      c / lambdaV + Aopt * c ^ (1 / 3 : ℝ) + c0 + c1Langer * c ^ (-(1 / 3) : ℝ) +
        d2Of c0 γ0 * c ^ (-(2 / 3) : ℝ) - Cm * c ^ (-1 : ℝ) ≤
      virasoroProblem.Delta_best c :=
  delta_best_ge_of_phase_sharp virasoroProblem c0 γ0 C hC hL

end FormalResearch.ModularBootstrap.FiveTerm

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.dimension_ge_of_phase_ge_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.dimension_ge_of_phase_ge_sharp

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.delta_best_ge_of_phase_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.delta_best_ge_of_phase_sharp

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.spinless_lower_of_phase_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.spinless_lower_of_phase_sharp
