module

public import FormalResearch.ModularBootstrap.Upper.Ramped.LangerTauInv

/-!
# Derivatives of the Langer coordinate: `τ' ≥ 4/5` on `[ξ_*, ∞)` and the logarithmic derivative

`remainder.tex`, Proposition 1.2(2), input `(F1)`.  For `x > ξ_*`, `τ = (N/k_tip)^{2/3}` gives

* `deriv_langerTau_eq`: `τ' = τ · G`, `G = ρ_U/(3N)` (so `(log τ)' = ρ_U/(3N)`);
* `deriv2_langerTau_eq`: `τ'' = τ · (G² + G')`, `G' = ρ_U'/(3N) - ρ_U²/(6N²)`;
* `langerTau_deriv_cube_ge`: `τ'³ ≥ 2/3` for `x > ξ_*` (from `N ≤ r ρ_U/2` and `ρ_U² ≥ 9 k_tip² r`),
  hence `langerTau_deriv_ge`: `τ' ≥ 4/5` on `[ξ_*, ∞)`.
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set Metric
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.ModularBootstrap Upper.Comb

lemma langerTau_pos_of_gt {x : ℝ} (hx : xiStar < x) : 0 < langerTau x := by
  rw [langerTau_eq_of_gt hx]
  exact Real.rpow_pos_of_pos (div_pos (cumulN_pos hx) kTip_pos) _

/-- `G(z) = ρ_U(z)/(3 N(z))`, the logarithmic derivative of `τ`. -/
noncomputable def langerG (z : ℝ) : ℝ := rhoU z / (3 * cumulN z)

/-- The derivative of `G`: `ρ_U'/(3N) - ρ_U²/(6N²)`. -/
noncomputable def langerG' (z : ℝ) : ℝ :=
  rhoUDeriv z / (3 * cumulN z) - rhoU z ^ 2 / (6 * cumulN z ^ 2)

lemma hasDerivAt_langerG {z : ℝ} (hz : xiStar < z) : HasDerivAt langerG (langerG' z) z := by
  have hN := cumulN_pos hz
  have h := (hasDerivAt_rhoU hz).div ((hasDerivAt_cumulN hz).const_mul 3) (by positivity)
  refine h.congr_deriv ?_
  unfold langerG'
  field_simp
  ring

lemma hasDerivAt_langerTau_of_gt {x : ℝ} (hx : xiStar < x) :
    HasDerivAt langerTau (langerTau x * langerG x) x := by
  have hk := kTip_pos
  have hN := cumulN_pos hx
  have hg : HasDerivAt (fun z => (2 / 3 : ℝ) * Real.log (cumulN z / kTip))
      ((2 / 3 : ℝ) * ((rhoU x / 2 / kTip) / (cumulN x / kTip))) x :=
    (((hasDerivAt_cumulN hx).div_const kTip).log (by positivity)).const_mul _
  have he := hg.exp
  have heq : (fun z => Real.exp ((2 / 3 : ℝ) * Real.log (cumulN z / kTip))) =ᶠ[𝓝 x] langerTau := by
    filter_upwards [Ioi_mem_nhds hx] with z hz
    rw [langerTau_eq_of_gt hz, Real.rpow_def_of_pos (div_pos (cumulN_pos hz) hk)]
    congr 1; ring
  have := he.congr_of_eventuallyEq heq.symm
  refine this.congr_deriv ?_
  have hτ : langerTau x = Real.exp ((2 / 3 : ℝ) * Real.log (cumulN x / kTip)) := by
    rw [langerTau_eq_of_gt hx, Real.rpow_def_of_pos (div_pos hN hk)]; congr 1; ring
  rw [← hτ]
  unfold langerG
  field_simp

lemma deriv_langerTau_eq {x : ℝ} (hx : xiStar < x) : deriv langerTau x = langerTau x * langerG x :=
  (hasDerivAt_langerTau_of_gt hx).deriv

lemma deriv2_langerTau_eq {x : ℝ} (hx : xiStar < x) :
    deriv (deriv langerTau) x = langerTau x * (langerG x ^ 2 + langerG' x) := by
  have heq : deriv langerTau =ᶠ[𝓝 x] fun z => langerTau z * langerG z := by
    filter_upwards [Ioi_mem_nhds hx] with z hz
    exact deriv_langerTau_eq hz
  have h := (hasDerivAt_langerTau_of_gt hx).mul (hasDerivAt_langerG hx)
  rw [(h.congr_of_eventuallyEq heq).deriv]
  ring

/-! ### Lower bound `τ' ≥ 4/5` -/

lemma cumulN_le_half_mul {x : ℝ} (hx : xiStar ≤ x) : cumulN x ≤ (x - xiStar) * rhoU x / 2 := by
  unfold cumulN
  have h1 : ∫ t in xiStar..x, rhoU t ≤ ∫ t in xiStar..x, rhoU x := by
    refine intervalIntegral.integral_mono_on hx (intervalIntegrable_rhoU le_rfl hx)
      intervalIntegrable_const fun t ht => ?_
    exact rhoU_strictMonoOn.monotoneOn (Set.mem_Ici.2 ht.1) (Set.mem_Ici.2 hx) ht.2
  rw [intervalIntegral.integral_const, smul_eq_mul] at h1
  linarith

lemma langerTau_cube {x : ℝ} (hx : xiStar < x) : langerTau x ^ 3 = (cumulN x / kTip) ^ 2 := by
  have hk := kTip_pos
  have hN := cumulN_pos hx
  rw [langerTau_eq_of_gt hx, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  have : (2 / 3 : ℝ) * ((3 : ℕ) : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
  rw [this, Real.rpow_natCast]

/-- `τ'³ ≥ 2/3` for `x > ξ_*`. -/
lemma langerTau_deriv_cube_ge {x : ℝ} (hx : xiStar < x) : 2 / 3 ≤ (deriv langerTau x) ^ 3 := by
  have hk := kTip_pos
  have hN := cumulN_pos hx
  have hρ := rhoU_pos hx
  have hτ := langerTau_pos_of_gt hx
  have hr : 0 < x - xiStar := by linarith
  rw [deriv_langerTau_eq hx]
  unfold langerG
  have h3 := langerTau_cube hx
  have hsq := (rhoU_sq_bounds (r := x - xiStar) hr.le).1
  rw [show xiStar + (x - xiStar) = x by ring] at hsq
  have hle := cumulN_le_half_mul hx.le
  have e : (langerTau x * (rhoU x / (3 * cumulN x))) ^ 3 = rhoU x ^ 3 / (27 * kTip ^ 2 * cumulN x) := by
    rw [mul_pow, div_pow, h3]
    field_simp
    norm_num
  rw [e, le_div_iff₀ (by positivity)]
  have h1 : 18 * kTip ^ 2 * cumulN x ≤ rhoU x ^ 3 := by
    have : 18 * kTip ^ 2 * cumulN x ≤ 9 * kTip ^ 2 * ((x - xiStar) * rhoU x) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hsq hρ.le]
  nlinarith

lemma langerTau_deriv_ge {x : ℝ} (hx : xiStar ≤ x) : 4 / 5 ≤ deriv langerTau x := by
  rcases hx.eq_or_lt with h | h
  · rw [← h, deriv_langerTau_xiStar]; norm_num
  · by_contra hlt
    push Not at hlt
    have hpos := deriv_langerTau_pos (lt_trans xiStar_pos h)
    have h1 : (deriv langerTau x) ^ 3 < (4 / 5) ^ 3 := pow_lt_pow_left₀ hlt hpos.le (by norm_num)
    have := langerTau_deriv_cube_ge h
    norm_num at h1
    linarith

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.langerTau_deriv_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms langerTau_deriv_ge

end FormalResearch.ModularBootstrap.Upper.Ramped
