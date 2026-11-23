module

public import FormalResearch.ModularBootstrap.Upper.Assembly.DesignG
public import FormalResearch.ModularBootstrap.FixedWeight.OptimalMeasure

/-!
# The first site of the designs against `T_*`: `t_f = T_* + c_* d c^{1/3} + O(c^{-1/3})`

Source: `CFT/modular_bootstrap/paper/spectral_rigidity.tex` (FW-C), `upper_transfer.tex` (`ut:P`).

For the design `D(N, η_*, d)` the first site is `χ'_1 = ξ_* + λ σ_1` with `λ = (k_tip c)^{-2/3}`,
`σ_1 = (|a_1| + d)/κ`, and `t_f = c χ'_1² / 3`.  With `a = c^{1/3}`, `k' = k_tip^{-2/3}`,

`t_f = ξ̄ c + (2 ξ_* k' σ_1 / 3) a + k'² σ_1² / (3 a)`,

and `2 ξ_* k' /(3 κ) = c_*` (`β = κ k_tip^{2/3}`), so that

`t_f = T_*(c) + c_* d c^{1/3} + k'² σ_1² / (3 c^{1/3})`   (`designTf_eq`).

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Assembly

open FormalResearch.Special FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.FixedWeight
  FormalResearch.ModularBootstrap.Upper.Comb FormalResearch.ModularBootstrap.Upper.Design
  FormalResearch.ModularBootstrap.Upper.Window

/-- `β = κ k_tip^{2/3}`. -/
lemma betaTip_eq : betaTip = kappaAiry * kTip ^ (2 / 3 : ℝ) := by
  unfold betaTip KTip kappaAiry
  rw [← Real.mul_rpow (by positivity) kTip_pos.le]
  congr 1
  ring

/-- `c_* = 2 ξ_* k_tip^{-2/3} / (3 κ)`. -/
lemma cStar_eq : cStar = 2 * xiStar * kTip ^ (-(2 / 3 : ℝ)) / (3 * kappaAiry) := by
  have hk := kTip_pos
  have hκ := kappaAiry_pos
  unfold cStar
  rw [betaTip_eq, Real.rpow_neg hk.le]
  have : 0 < kTip ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hk _
  field_simp

lemma lambdaComb_eq {c : ℝ} (hc : 0 < c) :
    lambdaComb c = kTip ^ (-(2 / 3 : ℝ)) / (c ^ ((1 : ℝ) / 3)) ^ 2 := by
  unfold lambdaComb
  rw [Real.mul_rpow kTip_pos.le hc.le, Real.rpow_neg hc.le, div_eq_mul_inv]
  congr 2
  rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]
  norm_num

lemma rpow_third_cube {c : ℝ} (hc : 0 < c) : (c ^ ((1 : ℝ) / 3)) ^ 3 = c := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]
  norm_num

/-- `t_f = ξ̄ c + (2 ξ_* k' σ_1 / 3) c^{1/3} + k'² σ_1² / (3 c^{1/3})`, `k' = k_tip^{-2/3}`. -/
lemma designTf_eq' {c : ℝ} (hc : 0 < c) (d : ℝ) :
    designTf d c = xiBar * c +
      (2 * xiStar * kTip ^ (-(2 / 3 : ℝ)) * designSigma1 d 1 / 3) * c ^ ((1 : ℝ) / 3) +
      (kTip ^ (-(2 / 3 : ℝ))) ^ 2 * designSigma1 d 1 ^ 2 / (3 * c ^ ((1 : ℝ) / 3)) := by
  have ha : 0 < c ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hc _
  set a := c ^ ((1 : ℝ) / 3) with hadef
  have hc3 : c = a ^ 3 := (rpow_third_cube hc).symm
  unfold designTf designSite xiBar
  rw [lambdaComb_eq hc, ← hadef]
  conv_lhs => rw [hc3]
  conv_rhs => rw [hc3]
  field_simp
  ring

lemma designSigma1_one (d : ℝ) : designSigma1 d 1 = (|airyZero 1| + d) / kappaAiry := by
  unfold designSigma1
  simp

/-- `t_f = T_*(c) + c_* d c^{1/3} + k'² σ_1² / (3 c^{1/3})`. -/
lemma designTf_eq {c : ℝ} (hc : 0 < c) (d : ℝ) :
    designTf d c = TStar c + cStar * d * c ^ ((1 : ℝ) / 3) +
      (kTip ^ (-(2 / 3 : ℝ))) ^ 2 * designSigma1 d 1 ^ 2 / (3 * c ^ ((1 : ℝ) / 3)) := by
  rw [designTf_eq' hc d]
  have hκ := kappaAiry_pos
  have key : 2 * xiStar * kTip ^ (-(2 / 3 : ℝ)) * designSigma1 d 1 / 3 =
      cStar * (|airyZero 1| + d) := by
    rw [designSigma1_one, cStar_eq]
    field_simp
  rw [key]
  unfold TStar Aopt
  ring

/-- For `c ≥ 1`: `t_f + 1 ≤ T_*(c) + c_* d c^{1/3} + (1 + R₀)`, `R₀ = k'² σ_1² / 3`. -/
lemma designTf_add_one_le {c : ℝ} (hc : 1 ≤ c) (d : ℝ) :
    designTf d c + 1 ≤ TStar c + cStar * d * c ^ ((1 : ℝ) / 3) +
      (1 + (kTip ^ (-(2 / 3 : ℝ))) ^ 2 * designSigma1 d 1 ^ 2 / 3) := by
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc
  have ha1 : 1 ≤ c ^ ((1 : ℝ) / 3) := Real.one_le_rpow hc (by norm_num)
  rw [designTf_eq hc0 d]
  have hR : 0 ≤ (kTip ^ (-(2 / 3 : ℝ))) ^ 2 * designSigma1 d 1 ^ 2 := by positivity
  have : (kTip ^ (-(2 / 3 : ℝ))) ^ 2 * designSigma1 d 1 ^ 2 / (3 * c ^ ((1 : ℝ) / 3)) ≤
      (kTip ^ (-(2 / 3 : ℝ))) ^ 2 * designSigma1 d 1 ^ 2 / 3 := by
    apply div_le_div_of_nonneg_left hR (by norm_num)
    nlinarith
  linarith

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.designTf_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms designTf_eq

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.designTf_add_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms designTf_add_one_le

end FormalResearch.ModularBootstrap.Upper.Assembly
