module

public import FormalResearch.ModularBootstrap.TwoLevel.CorollaryTwoFour
public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroTransfer

/-!
# The level times `t = ξ̄ c' + A c'^{1/3}` in the Airy chart

Elementary chart facts used by Theorem 2.5 and Theorem 2.6 (`virasoro_two_level.tex`): with
`levelTime A c' = ξ̄ c' + A c'^{1/3}` (`TwoLevel.CorollaryTwoFour`) and `u = uAiry c' t`,

* `tAiry_eq_levelTime`: `t(u) = levelTime (-c_* u) c' + u² c'^{-1/3}/(3β²)` for `u` in the range of the chart;
* `eventually_tAiry_add_one_le_levelTime`: `t(u) + 1 ≤ levelTime B c'` for large `c'`, if `B > -c_* u`;
* `tendsto_uAiry_levelTime`: `u(levelTime A c') → -A/c_*`.

All results are proved unconditionally.
-/

@[expose] public section

open Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Upper.Rigidity FormalResearch.ModularBootstrap.FixedWeight

lemma tendsto_slopeAiry : Tendsto slopeAiry atTop (𝓝 0) := by
  have h : Tendsto epsAiry atTop (𝓝 0) := tendsto_rpow_neg_atTop (by norm_num)
  have := h.div_const betaTip
  rw [zero_div] at this
  exact this

lemma eventually_lt_uEnd (u : ℝ) : ∀ᶠ c : ℝ in atTop, u < uEnd c := by
  have h : Tendsto (fun c => u * slopeAiry c) atTop (𝓝 0) := by
    simpa using tendsto_slopeAiry.const_mul u
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    h.eventually (gt_mem_nhds (xiStar_pos : (0 : ℝ) < xiStar))] with c hc hlt
  rw [lt_uEnd_iff hc]; linarith

lemma epsAiry_sq_mul {c : ℝ} (hc : 0 < c) : c * epsAiry c ^ 2 = c ^ (-((1 : ℝ) / 3)) := by
  have h4 : epsAiry c ^ 2 = c ^ (-((4 : ℝ) / 3)) := by
    unfold epsAiry
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]; norm_num
  rw [h4]
  calc c * c ^ (-((4 : ℝ) / 3)) = c ^ (1 : ℝ) * c ^ (-((4 : ℝ) / 3)) := by rw [Real.rpow_one]
    _ = c ^ (1 + -((4 : ℝ) / 3)) := (Real.rpow_add hc _ _).symm
    _ = _ := by norm_num

/-- `t(u) = levelTime (-c_* u) c' + u² c'^{-1/3}/(3β²)` on the range of the chart. -/
lemma tAiry_eq_levelTime {c u : ℝ} (hc : 0 < c) (hu : u < uEnd c) :
    tAiry c u = levelTime (-cStar * u) c + u ^ 2 * c ^ (-((1 : ℝ) / 3)) / (3 * betaTip ^ 2) := by
  have hb := betaTip_pos.ne'
  unfold tAiry levelTime
  rw [bAiry_eq_of_lt hc hu]
  unfold slopeAiry
  have h1 := c_mul_eps hc
  have h2 := epsAiry_sq_mul hc
  unfold xiBar cStar
  rw [← h2]
  have : c / 3 * (xiStar - u * (epsAiry c / betaTip)) ^ 2 =
      xiStar ^ 2 / 3 * c - (2 * xiStar / (3 * betaTip)) * u * (c * epsAiry c) +
        u ^ 2 * (c * epsAiry c ^ 2) / (3 * betaTip ^ 2) := by
    field_simp; ring
  rw [this, h1]
  ring

lemma eventually_tAiry_add_one_le_levelTime {u B : ℝ} (h : -cStar * u < B) :
    ∀ᶠ c : ℝ in atTop, tAiry c u + 1 ≤ levelTime B c := by
  have hβ := betaTip_pos
  have hp : Tendsto (fun c : ℝ => c ^ ((1 : ℝ) / 3)) atTop atTop := tendsto_rpow_atTop (by norm_num)
  have hn : Tendsto (fun c : ℝ => c ^ (-((1 : ℝ) / 3))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_lt_uEnd u,
    hp.eventually_ge_atTop ((1 + u ^ 2 / (3 * betaTip ^ 2)) / (B + cStar * u)),
    hn.eventually (ge_mem_nhds (zero_lt_one : (0 : ℝ) < 1))] with c hc hu h1 h2
  have hd : 0 < B + cStar * u := by linarith
  have hc3 : 0 < c ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hc _
  have hcn : 0 < c ^ (-((1 : ℝ) / 3)) := Real.rpow_pos_of_pos hc _
  rw [tAiry_eq_levelTime hc hu]
  have key : 1 + u ^ 2 / (3 * betaTip ^ 2) ≤ (B + cStar * u) * c ^ ((1 : ℝ) / 3) := by
    have := (div_le_iff₀ hd).1 h1
    linarith
  have hu2 : u ^ 2 * c ^ (-((1 : ℝ) / 3)) / (3 * betaTip ^ 2) ≤ u ^ 2 / (3 * betaTip ^ 2) := by
    gcongr
    nlinarith [sq_nonneg u]
  have e : levelTime B c - levelTime (-cStar * u) c = (B + cStar * u) * c ^ ((1 : ℝ) / 3) := by
    rw [levelTime_sub]; ring
  nlinarith

/-- `u(levelTime A c') → -A / c_*`. -/
theorem tendsto_uAiry_levelTime (A : ℝ) :
    Tendsto (fun c : ℝ => uAiry c (levelTime A c)) atTop (𝓝 (-A / cStar)) := by
  have h := tendsto_uAiry_shift (A - Aopt)
  have hval : airyZero 1 - 3 * betaTip * (A - Aopt) / (2 * xiStar) = -A / cStar := by
    have hc : cStar = 2 * xiStar / (3 * betaTip) := rfl
    have ha : Aopt = cStar * |airyZero 1| := rfl
    rw [abs_of_neg (airyZero_neg 1)] at ha
    have hξ := xiStar_pos.ne'
    have hb := betaTip_pos.ne'
    rw [ha, hc]
    field_simp
    ring
  rw [hval] at h
  refine h.congr fun c => ?_
  show uAiry c (TStar c + (A - Aopt) * c ^ ((1 : ℝ) / 3)) = uAiry c (levelTime A c)
  rw [TStar_add_shift]
  unfold levelTime
  congr 1
  ring

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.tendsto_uAiry_levelTime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tendsto_uAiry_levelTime

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.eventually_tAiry_add_one_le_levelTime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eventually_tAiry_add_one_le_levelTime

end FormalResearch.ModularBootstrap.TwoLevel
