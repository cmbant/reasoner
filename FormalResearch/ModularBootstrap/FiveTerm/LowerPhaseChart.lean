module

public import FormalResearch.ModularBootstrap.FiveTerm.UpperPhaseChart
public import FormalResearch.ModularBootstrap.Bessel.VCorollaries
public import FormalResearch.ModularBootstrap.Crossing.Setup

/-!
# From a lower bound on the phase of the first site to the dimension (FIVE-L; `gp:L`, `eq:gp-five-terms`)

Source: `CFT/modular_bootstrap/paper/modular_bootstrap_gap_proof.tex` (reduction to a threshold in the phase
coordinate, `eq:gp-tau-star`-`eq:gp-five-terms`, statement `gp:L`) and `constant_term_slit_strip.tex`
(`cts:lower-main`, `cts:langer`).

This is the lower-bound twin of `FiveTerm.dimension_le_of_phase_le` (FIVE-U, `UpperPhaseChart`), in the same generic
form: the constants `(c_0, γ_0)` are arbitrary reals (in the application `c_0^*(w,Q) = α_tip g_1`, `γ_0(w,Q)`).

* `dimension_ge_of_phase_ge` (**the lower phase-to-dimension conversion**): for arbitrary reals `c_0`, `γ_0` and
  `C ≥ 0` there are `C_-`, `c₁` such that for all `c ≥ c₁` and every `x > ξ_*` whose phase satisfies
  `τ(x) ≥ τ_*(c) - C c^{-2} log c`,
  `c/12 + c x²/3 ≥ c/Λ_V + A_opt c^{1/3} + c_0 + c_1^Langer c^{-1/3} + d_2 c^{-2/3} - C_- c^{-1} log c`,
  `d_2 = (2 c_0/A_opt) c_1^Langer - A_opt γ_0` (`d2Of`).
  (If the phase is large, `τ(x) ≥ τ(ξ_* + 1/(10π))`, the dimension exceeds the target by a linear amount.)
* `LowerPhaseStatement prob c₀ γ₀ C` is the statement `gp:L` for the fixed-weight problem `prob`: every weakly feasible
  test at `(c/12, T)` has a first-site phase `≥ τ_*(c) - C c^{-2} log c` below the threshold `T`.  It is **a named
  hypothesis** (it is the content of `cts:lower-main` and is not proved in this file).
* `delta_best_ge_of_phase` and `spinless_lower_of_phase`: **the lower half of `thm:spinless-expansion` (and of
  `thm:fixed-weight-expansion`), conditional on `LowerPhaseStatement`**:
  `Δ_best(c) ≥ c/Λ_V + A_opt c^{1/3} + c_0 + c_1^Langer c^{-1/3} + d_2 c^{-2/3} - C_- c^{-1} log c`.

The chart conversion is unconditional; only the last two theorems carry the hypothesis `LowerPhaseStatement`.
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.Special FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.Crossing

/-- `τ(ξ_* + 1/(10π)) ≤ 1/20`: the chart expansion is applied only below this phase. -/
lemma tauPhase_small : tauPhase (xiStar + 1 / (10 * π)) ≤ 1 / 20 := by
  have hpi := Real.pi_pos
  have hr : 0 < 1 / (10 * π) := by positivity
  have hr1 : π * (1 / (10 * π)) ≤ 1 / 10 := by
    have : π * (1 / (10 * π)) = 1 / 10 := by field_simp
    exact this.le
  have h := tau_tip_expansion hr hr1
  have hr30 : 1 / (10 * π) ≤ 1 / 30 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith only [Real.pi_gt_three]
  obtain ⟨η0, η1⟩ := eta_bounds
  set r := 1 / (10 * π) with hrdef
  have h' : tauPhase (xiStar + r) ≤ r + π / (30 * √2) * r ^ 2 + 2 * r ^ 3 := by
    have := (abs_le.mp h).2
    unfold tauPhase
    linarith only [this]
  have hr2 : r ^ 2 ≤ (1 / 30) ^ 2 := pow_le_pow_left₀ hr.le hr30 2
  have hr3 : r ^ 3 ≤ (1 / 30) ^ 3 := pow_le_pow_left₀ hr.le hr30 3
  have hη : π / (30 * √2) * r ^ 2 ≤ 4 / 50 * (1 / 30) ^ 2 :=
    mul_le_mul η1 hr2 (sq_nonneg _) (by norm_num)
  have : r + π / (30 * √2) * r ^ 2 + 2 * r ^ 3 ≤ 1 / 30 + 4 / 50 * (1 / 30) ^ 2 + 2 * (1 / 30) ^ 3 := by
    linarith only [hr30, hη, hr3]
  linarith only [h', this]

/-- `a = 2ξ_*/3 ≥ 1/10`. -/
lemma two_xiStar_div_three_ge : 1 / 10 ≤ 2 * xiStar / 3 := by
  have h := Bessel.three_quarters_le_pi_mul_xiStar
  have hpi := Real.pi_pos
  have hpi4 := Real.pi_lt_d2
  have hxi : 3 / 4 ≤ π * xiStar := h
  have : (3 / 4) / π ≤ xiStar := by
    rw [div_le_iff₀ hpi]; linarith only [hxi]
  have h2 : (3 / 4 : ℝ) / 3.15 ≤ (3 / 4) / π := by
    apply div_le_div_of_nonneg_left (by norm_num) hpi
    linarith only [Real.pi_lt_d2]
  have : (3 / 4 : ℝ) / 3.15 ≤ xiStar := le_trans h2 this
  norm_num at this
  linarith only [this]

/-- On `0 ≤ E ≤ ε ≤ 1/20` the cubic `g(ε) = aε + K₂ε² - 6ε³` is monotone (`a ≥ 1/10`, `K₂ ≥ 0`). -/
lemma cubic_mono {a K2 E ε : ℝ} (ha : 1 / 10 ≤ a) (hK : 0 ≤ K2) (hE : 0 ≤ E) (hEε : E ≤ ε)
    (hε : ε ≤ 1 / 20) :
    a * E + K2 * E ^ 2 - 6 * E ^ 3 ≤ a * ε + K2 * ε ^ 2 - 6 * ε ^ 3 := by
  have hd : 0 ≤ ε - E := sub_nonneg.mpr hEε
  have h1 : ε ^ 2 + ε * E + E ^ 2 ≤ 3 * (1 / 20) ^ 2 := by
    have h2 : ε ^ 2 ≤ (1 / 20) ^ 2 := pow_le_pow_left₀ (hE.trans hEε) hε 2
    have h3 : E ^ 2 ≤ (1 / 20) ^ 2 := pow_le_pow_left₀ hE (hEε.trans hε) 2
    have h4 : ε * E ≤ (1 / 20) ^ 2 := by
      have := mul_le_mul hε (hEε.trans hε) hE (by norm_num : (0 : ℝ) ≤ 1 / 20)
      nlinarith only [this]
    linarith only [h2, h3, h4]
  have key : (a * ε + K2 * ε ^ 2 - 6 * ε ^ 3) - (a * E + K2 * E ^ 2 - 6 * E ^ 3) =
      (ε - E) * (a + K2 * (ε + E) - 6 * (ε ^ 2 + ε * E + E ^ 2)) := by ring
  have hpos : 0 ≤ a + K2 * (ε + E) - 6 * (ε ^ 2 + ε * E + E ^ 2) := by
    have : 0 ≤ K2 * (ε + E) := mul_nonneg hK (by linarith only [hE, hEε])
    nlinarith only [this, h1, ha]
  have := mul_nonneg hd hpos
  linarith only [key, this]

/-- The polynomial-in-`u = c^{-1/3}` bookkeeping of the lower chart conversion:
`a c g(E) ≥ a p/u + a q - a p γ u² - a M u³ + K₂ p² u + 2 K₂ p q u² - Cpoly u³`,
where `E = p u² + q u³ - p γ u⁵ - M u⁶` and `g(E) = a E + K₂ E² - 6 E³`. -/
lemma phase_poly_lower {a K2 p q γ C M u c : ℝ} (hK : 0 ≤ K2) (hp : 0 ≤ p) (hC : 0 ≤ C)
    (hM : 0 ≤ M) (hu : 0 < u) (hu1 : u ≤ 1) (hMu : M * u ≤ 3 * C) (hcu : c * u ^ 3 = 1) :
    a * p / u + a * q - a * p * γ * u ^ 2 - a * M * u ^ 3 + K2 * p ^ 2 * u + 2 * K2 * p * q * u ^ 2 -
      (K2 * (2 * p * (p * |γ| + 3 * C) + 2 * |q| * (p * |γ| + 3 * C)) +
        6 * (p + |q| + (p * |γ| + 3 * C)) ^ 3) * u ^ 3 ≤
    a * c * (p * u ^ 2 + q * u ^ 3 - p * γ * u ^ 5 - M * u ^ 6) +
      K2 * c * (p * u ^ 2 + q * u ^ 3 - p * γ * u ^ 5 - M * u ^ 6) ^ 2 -
      6 * c * (p * u ^ 2 + q * u ^ 3 - p * γ * u ^ 5 - M * u ^ 6) ^ 3 := by
  set B : ℝ := p * |γ| + 3 * C with hB
  have hB0 : 0 ≤ B := by positivity
  set s : ℝ := -(p * γ * u ^ 3) - M * u ^ 4 with hs
  have hu3 : 0 < u ^ 3 := pow_pos hu 3
  have hsb : |s| ≤ B * u ^ 3 := by
    have h1 : |-(p * γ * u ^ 3)| ≤ p * |γ| * u ^ 3 := by
      rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg hp, abs_of_pos hu3]
    have h2 : |M * u ^ 4| ≤ 3 * C * u ^ 3 := by
      rw [abs_mul, abs_of_nonneg hM, abs_of_pos (pow_pos hu 4)]
      calc M * u ^ 4 = (M * u) * u ^ 3 := by ring
        _ ≤ 3 * C * u ^ 3 := mul_le_mul_of_nonneg_right hMu hu3.le
    calc |s| = |-(p * γ * u ^ 3) + -(M * u ^ 4)| := by rw [hs]; ring_nf
      _ ≤ |-(p * γ * u ^ 3)| + |-(M * u ^ 4)| := abs_add_le _ _
      _ = |-(p * γ * u ^ 3)| + |M * u ^ 4| := by rw [abs_neg (M * u ^ 4)]
      _ ≤ p * |γ| * u ^ 3 + 3 * C * u ^ 3 := add_le_add h1 h2
      _ = B * u ^ 3 := by rw [hB]; ring
  have hε : p * u ^ 2 + q * u ^ 3 - p * γ * u ^ 5 - M * u ^ 6 = u ^ 2 * (p + q * u + s) := by
    rw [hs]; ring
  rw [hε]
  have hc : c = (u ^ 3)⁻¹ := by
    field_simp; linarith
  have e1 : a * c * (u ^ 2 * (p + q * u + s)) =
      a * p / u + a * q - a * p * γ * u ^ 2 - a * M * u ^ 3 := by
    rw [hs, hc]; field_simp; ring
  have e2 : K2 * c * (u ^ 2 * (p + q * u + s)) ^ 2 =
      K2 * (p ^ 2 * u + 2 * p * q * u ^ 2 + u * (q ^ 2 * u ^ 2 + 2 * p * s + 2 * q * u * s + s ^ 2)) := by
    rw [hc]; field_simp; ring
  have hsb' : |s| ≤ B * u ^ 2 := hsb.trans (by
    have : u ^ 3 ≤ u ^ 2 := pow_le_pow_of_le_one hu.le hu1 (by norm_num)
    exact mul_le_mul_of_nonneg_left this hB0)
  have hR : -((2 * p * B + 2 * |q| * B) * u ^ 3) ≤
      u * (q ^ 2 * u ^ 2 + 2 * p * s + 2 * q * u * s + s ^ 2) := by
    have t2 : -(2 * p * (B * u ^ 2)) ≤ 2 * p * s := by
      have := neg_abs_le s
      nlinarith only [this, hsb', hp]
    have t3 : -(2 * |q| * B * u ^ 2) ≤ 2 * q * u * s := by
      have h1 : |2 * q * u * s| ≤ 2 * |q| * B * u ^ 2 := by
        calc |2 * q * u * s| = 2 * |q| * u * |s| := by
              rw [abs_mul, abs_mul, abs_mul, abs_of_pos (two_pos), abs_of_pos hu]
          _ ≤ 2 * |q| * 1 * (B * u ^ 2) := by gcongr
          _ = 2 * |q| * B * u ^ 2 := by ring
      exact (neg_le_neg h1).trans (neg_abs_le _)
    have h4 : 0 ≤ q ^ 2 * u ^ 2 + s ^ 2 := by positivity
    have hsum : -((2 * p * B + 2 * |q| * B) * u ^ 2) ≤
        q ^ 2 * u ^ 2 + 2 * p * s + 2 * q * u * s + s ^ 2 := by
      nlinarith only [t2, t3, h4]
    calc -((2 * p * B + 2 * |q| * B) * u ^ 3) = u * (-((2 * p * B + 2 * |q| * B) * u ^ 2)) := by ring
      _ ≤ u * (q ^ 2 * u ^ 2 + 2 * p * s + 2 * q * u * s + s ^ 2) :=
          mul_le_mul_of_nonneg_left hsum hu.le
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
  have h6 : 6 * u ^ 3 * (p + q * u + s) ^ 3 ≤ 6 * (p + |q| + B) ^ 3 * u ^ 3 := by
    nlinarith only [h3, hu3]
  have hK2 : K2 * (-((2 * p * B + 2 * |q| * B) * u ^ 3)) ≤
      K2 * (u * (q ^ 2 * u ^ 2 + 2 * p * s + 2 * q * u * s + s ^ 2)) :=
    mul_le_mul_of_nonneg_left hR hK
  nlinarith only [h6, hK2]

lemma tendsto_tauMinus (c0 γ0 C : ℝ) :
    Tendsto (fun c : ℝ => tauStar c0 γ0 c - C * c ^ (-2 : ℝ) * Real.log c) atTop (𝓝 0) := by
  have := tendsto_tauPlus c0 γ0 (-C)
  simpa [sub_eq_add_neg, neg_mul] using this

/-- **Lower phase-to-dimension conversion** (`eq:gp-five-terms`, the lower half of the reduction behind `gp:L`). -/
theorem dimension_ge_of_phase_ge (c0 γ0 C : ℝ) (hC : 0 ≤ C) :
    ∃ Cm c₁ : ℝ, 3 ≤ c₁ ∧ ∀ c : ℝ, c₁ ≤ c → ∀ x : ℝ, xiStar < x →
      tauStar c0 γ0 c - C * c ^ (-2 : ℝ) * Real.log c ≤ tauPhase x →
      c / lambdaV + Aopt * c ^ (1 / 3 : ℝ) + c0 + c1Langer * c ^ (-(1 / 3) : ℝ) +
        d2Of c0 γ0 * c ^ (-(2 / 3) : ℝ) - Cm * c ^ (-1 : ℝ) * Real.log c ≤
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
  -- the linear gap in the large-phase case
  set κ0 : ℝ := ((xiStar + δ0) ^ 2 - xiStar ^ 2) / 3 with hκ0
  have hκ0pos : 0 < κ0 := by
    rw [hκ0]; have : 0 < (xiStar + δ0) ^ 2 - xiStar ^ 2 := by nlinarith only [hξ0, hδ0pos]
    positivity
  set S : ℝ := Aopt + |c0| + |c1Langer| + |d2Of c0 γ0| with hS
  have hS0 : 0 ≤ S := by have := Aopt_pos; positivity
  -- thresholds
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
  have hlog0 : 0 ≤ Real.log c := Real.log_nonneg (by linarith)
  have hlog1 : 1 ≤ Real.log c := by
    have : Real.exp 1 ≤ 3 := by
      have := Real.exp_one_lt_d9; linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log c := Real.log_le_log (Real.exp_pos 1) (this.trans hc3)
  set M := C * Real.log c with hMdef
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
  set E : ℝ := tauStar c0 γ0 c - C * c ^ (-2 : ℝ) * Real.log c with hEdef
  have hEeq : E = p * u ^ 2 + q * u ^ 3 - p * γ0 * u ^ 5 - M * u ^ 6 := by
    rw [hEdef]; unfold tauStar; rw [e2, e3, e5, e6, hMdef]; ring
  set ε := tauPhase x with hεdef
  have hε0 : 0 < ε := tauPhase_pos hx
  have hEε : E ≤ ε := hτ
  -- the threshold `u ≤ uMax` gives `E ≥ 0`
  have hu_le : u ≤ uMax := by
    have h1 : uMax ^ (-3 : ℝ) ≤ c := hcu
    have h2 : c ^ (-(1 / 3) : ℝ) ≤ (uMax ^ (-3 : ℝ)) ^ (-(1 / 3) : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos huMax0 _) h1 (by norm_num)
    have h3 : (uMax ^ (-3 : ℝ)) ^ (-(1 / 3) : ℝ) = uMax := by
      rw [← Real.rpow_mul huMax0.le]; norm_num
    rw [hudef]; linarith only [h2, h3]
  have hs_abs : |(-(p * γ0 * u ^ 3) - M * u ^ 4)| ≤ B * u ^ 3 := by
    have hu3 : 0 < u ^ 3 := pow_pos hu0 3
    have h1 : |-(p * γ0 * u ^ 3)| ≤ p * |γ0| * u ^ 3 := by
      rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg hs0.le, abs_of_pos hu3]
    have h2 : |M * u ^ 4| ≤ 3 * C * u ^ 3 := by
      rw [abs_mul, abs_of_nonneg hM0, abs_of_pos (pow_pos hu0 4)]
      calc M * u ^ 4 = (M * u) * u ^ 3 := by ring
        _ ≤ 3 * C * u ^ 3 := mul_le_mul_of_nonneg_right hMu hu3.le
    calc |(-(p * γ0 * u ^ 3) - M * u ^ 4)| = |-(p * γ0 * u ^ 3) + -(M * u ^ 4)| := by ring_nf
      _ ≤ |-(p * γ0 * u ^ 3)| + |-(M * u ^ 4)| := abs_add_le _ _
      _ = |-(p * γ0 * u ^ 3)| + |M * u ^ 4| := by rw [abs_neg (M * u ^ 4)]
      _ ≤ p * |γ0| * u ^ 3 + 3 * C * u ^ 3 := add_le_add h1 h2
      _ = B * u ^ 3 := by rw [hBdef]; ring
  have hE0 : 0 ≤ E := by
    have hB0 : 0 ≤ B := by positivity
    have hq : -(|q| * u) ≤ q * u := by
      have := neg_abs_le q
      nlinarith only [this, hu0]
    have hsl : -(B * u ^ 3) ≤ (-(p * γ0 * u ^ 3) - M * u ^ 4) := by
      have := neg_abs_le (-(p * γ0 * u ^ 3) - M * u ^ 4)
      linarith only [this, hs_abs]
    have hBu : B * u ^ 3 ≤ B * u := by
      have : u ^ 3 ≤ u := by
        calc u ^ 3 ≤ u ^ 1 := pow_le_pow_of_le_one hu0.le hu1 (by norm_num)
          _ = u := pow_one u
      exact mul_le_mul_of_nonneg_left this hB0
    have hpos : 0 ≤ p + q * u + (-(p * γ0 * u ^ 3) - M * u ^ 4) := by
      have h4 : (|q| + B) * u ≤ p / 2 := by
        have : u ≤ p / (2 * (|q| + B + 1)) := hu_le
        rw [le_div_iff₀ (by positivity)] at this
        nlinarith only [this, abs_nonneg q, hB0, hu0]
      nlinarith only [hq, hsl, hBu, h4, hs0]
    rw [hEeq]
    have : p * u ^ 2 + q * u ^ 3 - p * γ0 * u ^ 5 - M * u ^ 6 =
        u ^ 2 * (p + q * u + (-(p * γ0 * u ^ 3) - M * u ^ 4)) := by ring
    rw [this]; positivity
  by_cases hbig : ε₁ ≤ ε
  · -- large phase: linear gap
    have hxlow : xiStar + δ0 ≤ x := by
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
    -- `c κ0 ≥ S c^{1/3}`
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
    -- the right side is below `c / Λ + S c^{1/3}`
    have hrhs : Aopt * c ^ (1 / 3 : ℝ) + c0 + c1Langer * c ^ (-(1 / 3) : ℝ) +
        d2Of c0 γ0 * c ^ (-(2 / 3) : ℝ) - (a * C + Cpoly) * c ^ (-1 : ℝ) * Real.log c ≤
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
      have tl : 0 ≤ (a * C + Cpoly) * c ^ (-1 : ℝ) * Real.log c := by
        rw [e3]; have : 0 ≤ a * C + Cpoly := by positivity
        positivity
      nlinarith only [t0, t1, t2, tl, hS]
    have := hbase
    linarith only [hD, hbase, hcκ, hrhs]
  · -- small phase: the chart expansion
    push Not at hbig
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
      (M := M) (u := u) (c := c) hK0.le hs0.le hC hM0 hu0 hu1 hMu hcu3
    rw [← hEeq] at hpoly
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
    have hlin' : a * p / u = Aopt * (1 / u) := by rw [← hap]; ring
    have hMt : a * M * u ^ 3 = a * C * u ^ 3 * Real.log c := by rw [hMdef]; ring
    have hCu : Cpoly * u ^ 3 ≤ Cpoly * u ^ 3 * Real.log c := by
      have : 0 ≤ Cpoly * u ^ 3 := by positivity
      nlinarith only [this, hlog1]
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
    rw [e13, e2, e3]
    rw [hd2, hc1, ← haq]
    rw [hlin', hMt] at hpoly
    nlinarith only [h1, hcmono, hexp, hexp2, hpoly, hCu]

/-! ### The lower half of the expansion, conditional on the phase statement `gp:L` -/

/-- **The phase statement `gp:L`** for the fixed-weight problem `prob` (with `c = c'`, resp. `c̃`): for every weakly
feasible test at `(c/12, T)` there is a point `x > ξ_*` of phase `τ(x) ≥ τ_*(c) - C c^{-2} log c` with
`c x²/3 ≤ T` (i.e. the largest sign change `t_1(g) ≤ T` is at phase at least `τ_* - C c^{-2} log c`).
This is a **named hypothesis** here; it is the conclusion of `cts:lower-main` (not proved in this file). -/
def LowerPhaseStatement (prob : FixedWeightProblem) (c0 γ0 C : ℝ) : Prop :=
  ∃ c₂ : ℝ, ∀ c : ℝ, c₂ ≤ c → ∀ (T : ℝ) (g : ℝ → ℝ), prob.IsWeaklyFeasible (c / 12) T g →
    ∃ x : ℝ, xiStar < x ∧ tauStar c0 γ0 c - C * c ^ (-2 : ℝ) * Real.log c ≤ tauPhase x ∧
      c / 3 * x ^ 2 ≤ T

/-- **Lower half of `thm:spinless-expansion` / `thm:fixed-weight-expansion`**, conditional on `gp:L`
(`LowerPhaseStatement`): `Δ_best(c) ≥ c/Λ_V + A_opt c^{1/3} + c_0 + c_1^Langer c^{-1/3} + d_2 c^{-2/3}
- C_- c^{-1} log c`.  The chart conversion is the unconditional `dimension_ge_of_phase_ge`. -/
theorem delta_best_ge_of_phase (prob : FixedWeightProblem) (c0 γ0 C : ℝ) (hC : 0 ≤ C)
    (hL : LowerPhaseStatement prob c0 γ0 C) :
    ∃ Cm c₁ : ℝ, ∀ c : ℝ, c₁ ≤ c →
      c / lambdaV + Aopt * c ^ (1 / 3 : ℝ) + c0 + c1Langer * c ^ (-(1 / 3) : ℝ) +
        d2Of c0 γ0 * c ^ (-(2 / 3) : ℝ) - Cm * c ^ (-1 : ℝ) * Real.log c ≤ prob.Delta_best c := by
  obtain ⟨Cm, c₁, hc₁, hconv⟩ := dimension_ge_of_phase_ge c0 γ0 C hC
  obtain ⟨c₂, hc₂⟩ := hL
  refine ⟨Cm, max (max c₁ c₂) (12 * prob.totalShift), fun c hc => ?_⟩
  have hc1 : c₁ ≤ c := (le_max_left _ _).trans ((le_max_left _ _).trans hc)
  have hc2 : c₂ ≤ c := (le_max_right _ _).trans ((le_max_left _ _).trans hc)
  have hsh : 12 * prob.totalShift ≤ c := (le_max_right _ _).trans hc
  have hne : {T : ℝ | 0 < T ∧ ∃ g, prob.IsFeasible (c / 12) T g}.Nonempty :=
    prob.feasible_nonempty hsh
  unfold FixedWeightProblem.Delta_best FixedWeightProblem.T_V
  have hT : c / lambdaV + Aopt * c ^ (1 / 3 : ℝ) + c0 + c1Langer * c ^ (-(1 / 3) : ℝ) +
        d2Of c0 γ0 * c ^ (-(2 / 3) : ℝ) - Cm * c ^ (-1 : ℝ) * Real.log c - c / 12 ≤
      sInf {T : ℝ | 0 < T ∧ ∃ g, prob.IsFeasible (c / 12) T g} := by
    refine le_csInf hne ?_
    rintro T ⟨_, g, hg⟩
    obtain ⟨x, hx, hτ, hxT⟩ := hc₂ c hc2 T g hg.isWeaklyFeasible
    have := hconv c hc1 x hx hτ
    linarith only [this, hxT]
  linarith only [hT]

/-- The Virasoro instance of `delta_best_ge_of_phase` (`thm:spinless-expansion`, lower half, conditional on
`gp:L`); `c = c'` is the paper's `c' = c - 1`, i.e. the problem's `c̃`.  With
`(c_0, γ_0) = (c0StarOf g1, gamma0Of g1 g3)` the constants are those of `cts:main`, `cts:g3-gamma0`
(`d2Of_c0StarOf`). -/
theorem spinless_lower_of_phase (c0 γ0 C : ℝ) (hC : 0 ≤ C)
    (hL : LowerPhaseStatement virasoroProblem c0 γ0 C) :
    ∃ Cm c₁ : ℝ, ∀ c : ℝ, c₁ ≤ c →
      c / lambdaV + Aopt * c ^ (1 / 3 : ℝ) + c0 + c1Langer * c ^ (-(1 / 3) : ℝ) +
        d2Of c0 γ0 * c ^ (-(2 / 3) : ℝ) - Cm * c ^ (-1 : ℝ) * Real.log c ≤
      virasoroProblem.Delta_best c :=
  delta_best_ge_of_phase virasoroProblem c0 γ0 C hC hL

end FormalResearch.ModularBootstrap.FiveTerm

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.dimension_ge_of_phase_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.dimension_ge_of_phase_ge

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.delta_best_ge_of_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.delta_best_ge_of_phase

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.spinless_lower_of_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.spinless_lower_of_phase
