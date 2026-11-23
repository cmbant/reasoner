module

public import FormalResearch.ModularBootstrap.Upper.Holes.Peano
public import FormalResearch.ModularBootstrap.Upper.Window.CardyWindow

/-!
# Geometry of the intermediate band of Lemma `T` (`ut:T`, `upper_transfer.tex` §5)

Elementary inputs of the proof of Lemma `T` (`ut:T`) on the band `χ_{N₁+1} ≤ x ≤ ξ_* + r₀`:

* `tanh_ge_div_cosh`, `tanh_mono_nonneg`, `tanh_pi_xiStar`: `tanh z ≥ z/cosh z₀` on `[0, z₀]`,
  monotonicity of `tanh` on `[0, ∞)` and `tanh(πξ_*) = 2^{-1/2}` (`sinh(πξ_*) = 1`).
* `neg_realLogT_le`: for `y ≥ ξ_*`, `d ≤ x - y ≤ r₀`, `-log|T_y(x)| ≤ log(2√2 cosh(πr₀/2)/(π d))`
  (the two `tanh` bounds of the proof of `ut:T`).
* `siteRadius_f_le_half`: for `N₁ ≥ 4f` and `r_{N₁+1} ≤ 1`, `r_f ≤ r_{N₁+1}/2` (the paper's
  `r_f/r_{N₁+1} ≤ (1+C₁)^{2/3} Φ_f/Φ_{N₁+1} ≤ 1/2`, Lemma `K0`(c)), hence
  `x - χ_f ≥ (x - ξ_*)/2` for `x ≥ χ_{N₁+1}`.
* `exists_inCell_of_ge'`: every `x ≥ χ_k` lies in a cell `χ_n ≤ x < χ_{n+1}` with `n ≥ k`.

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Window.Tail

open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Upper.Comb
  FormalResearch.ModularBootstrap.Upper.Holes

/-- Every `x ≥ χ_k` (`k ≥ 1`) lies in a cell `χ_n ≤ x < χ_{n+1}` with `n ≥ k`. -/
lemma exists_inCell_of_ge' {c' : ℝ} (hc' : 0 < c') {k : ℕ} (hk : 1 ≤ k) {x : ℝ}
    (hx : chiQuantile c' (k : ℝ) ≤ x) :
    ∃ n : ℕ, k ≤ n ∧ inCell c' n x := by
  have htend : Tendsto (fun m : ℕ => chiQuantile c' (m : ℝ)) atTop atTop :=
    (tendsto_chiQuantile_atTop hc').comp tendsto_natCast_atTop_atTop
  obtain ⟨M, hM⟩ := (tendsto_atTop_atTop.mp htend) (x + 1)
  have hhi : x < chiQuantile c' ((max k M : ℕ) : ℝ) := by linarith [hM (max k M) (le_max_right _ _)]
  have hex : ∃ m : ℕ, k ≤ m ∧ x < chiQuantile c' (m : ℝ) := ⟨max k M, le_max_left _ _, hhi⟩
  classical
  let m₀ := Nat.find hex
  have hm₀_spec := Nat.find_spec hex
  have hk_lt_m₀ : k < m₀ := by
    rcases eq_or_lt_of_le hm₀_spec.1 with heq | hlt
    · exfalso; rw [← heq] at hm₀_spec; linarith [hm₀_spec.2, hx]
    · exact hlt
  let n := m₀ - 1
  have hn_k : k ≤ n := by omega
  have hm₀_eq : m₀ = n + 1 := by omega
  have hxn : chiQuantile c' (n : ℝ) ≤ x := by
    by_contra hlt
    push Not at hlt
    have hn_lt : n < m₀ := by omega
    exact absurd ⟨hn_k, hlt⟩ (Nat.find_min hex hn_lt)
  refine ⟨n, hn_k, hxn, ?_⟩
  have hcast : chiQuantile c' ((n + 1 : ℕ) : ℝ) = chiQuantile c' (m₀ : ℝ) := by rw [hm₀_eq]
  rw [hcast]
  exact hm₀_spec.2

/-! ### `tanh` bounds -/

/-- `tanh z ≥ z / cosh z₀` for `0 ≤ z ≤ z₀`. -/
lemma tanh_ge_div_cosh {z z₀ : ℝ} (hz : 0 ≤ z) (hzz : z ≤ z₀) : z / cosh z₀ ≤ tanh z := by
  rw [Real.tanh_eq_sinh_div_cosh]
  have h1 : z ≤ sinh z := Real.self_le_sinh_iff.mpr hz
  have h2 : cosh z ≤ cosh z₀ := by
    rw [Real.cosh_le_cosh, abs_of_nonneg hz, abs_of_nonneg (hz.trans hzz)]; exact hzz
  have hc := Real.cosh_pos z
  calc z / cosh z₀ ≤ z / cosh z := div_le_div_of_nonneg_left hz hc h2
    _ ≤ sinh z / cosh z := div_le_div_of_nonneg_right h1 hc.le

/-- `tanh` is monotone: `tanh a ≤ tanh b` for `a ≤ b`. -/
lemma tanh_mono_real {a b : ℝ} (hab : a ≤ b) : tanh a ≤ tanh b := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
    div_le_div_iff₀ (Real.cosh_pos a) (Real.cosh_pos b)]
  have h := Real.sinh_nonneg_iff.mpr (sub_nonneg.mpr hab)
  rw [Real.sinh_sub] at h
  linarith

lemma cosh_pi_xiStar : cosh (π * xiStar) = √2 := by
  have h := Real.cosh_sq (π * xiStar)
  rw [sinh_pi_mul_xiStar] at h
  have h2 : cosh (π * xiStar) ^ 2 = 2 := by
    have := Real.cosh_sq_sub_sinh_sq (π * xiStar)
    rw [sinh_pi_mul_xiStar] at this; linarith
  have hc := Real.cosh_pos (π * xiStar)
  rw [← h2, Real.sqrt_sq hc.le]

/-- `tanh(πξ_*) = 2^{-1/2}`. -/
lemma tanh_pi_xiStar : tanh (π * xiStar) = 1 / √2 := by
  rw [Real.tanh_eq_sinh_div_cosh, sinh_pi_mul_xiStar, cosh_pi_xiStar]

/-- The two `tanh` bounds of the proof of `ut:T`: for `y ≥ ξ_*`, `0 < d ≤ x - y ≤ r₀`,
`-log|T_y(x)| ≤ log(2√2 cosh(πr₀/2)/(π d))`. -/
lemma neg_realLogT_le {x y d r₀ : ℝ} (hy : xiStar ≤ y) (hd : 0 < d) (hdx : d ≤ x - y)
    (hxr : x - y ≤ r₀) :
    -realLogT x y ≤ Real.log (2 * √2 * cosh (π * r₀ / 2) / (π * d)) := by
  have hξ := xiStar_pos
  have hpi := Real.pi_pos
  have hy0 : 0 ≤ y := hξ.le.trans hy
  have hxy : y < x := by linarith
  have hx0 : 0 ≤ x := hy0.trans hxy.le
  rw [realLogT_eq_combH hx0 hy0 hxy.ne]
  unfold combH
  rw [abs_of_pos (sub_pos.mpr hxy)]
  have hcr : 0 < cosh (π * r₀ / 2) := Real.cosh_pos _
  have ha : (π * d / 2) / cosh (π * r₀ / 2) ≤ tanh (π * (x - y) / 2) := by
    have h := tanh_ge_div_cosh (z := π * (x - y) / 2) (z₀ := π * r₀ / 2)
      (by have := sub_pos.mpr hxy; positivity) (by nlinarith)
    refine le_trans ?_ h
    apply div_le_div_of_nonneg_right _ hcr.le
    nlinarith
  have hapos : 0 < (π * d / 2) / cosh (π * r₀ / 2) := by positivity
  have hb : 1 / √2 ≤ tanh (π * (x + y) / 2) := by
    rw [← tanh_pi_xiStar]
    exact tanh_mono_real (by nlinarith)
  have hbpos : 0 < 1 / √2 := by positivity
  have hl1 := Real.log_le_log hapos ha
  have hl2 := Real.log_le_log hbpos hb
  have hs2 : 0 < √2 := Real.sqrt_pos.mpr (by norm_num)
  have e : Real.log (2 * √2 * cosh (π * r₀ / 2) / (π * d)) =
      -(Real.log ((π * d / 2) / cosh (π * r₀ / 2)) + Real.log (1 / √2)) := by
    rw [← Real.log_mul hapos.ne' hbpos.ne', ← Real.log_inv]
    congr 1
    field_simp
  rw [e]
  linarith

/-! ### `K0`(c) comparison of `r_f` and `r_{N₁+1}` -/

lemma c1K0_le : c1K0 ≤ 17 / 50 := by
  unfold c1K0
  have hpi := Real.pi_lt_d2
  have h2 : (1.41 : ℝ) ≤ √2 := Real.le_sqrt_of_sq_le (by norm_num)
  rw [div_le_iff₀ (by positivity)]
  nlinarith

lemma one_add_c1K0_sq_le : (1 + c1K0) ^ 2 ≤ 2 := by
  have h := c1K0_le
  have h0 := c1K0_pos
  nlinarith

/-- For `N₁ ≥ 4f`: `Φ_f ≤ (1/2)(1 + C₁)^{-2/3} Φ_{N₁+1}`. -/
lemma phiQuantile_f_le {f N₁ : ℕ} (hf : 1 ≤ f) (hN : 4 * f ≤ N₁) :
    phiQuantile (f : ℝ) ≤
      (1 / 2) * (1 + c1K0) ^ (-(2 / 3 : ℝ)) * phiQuantile ((N₁ + 1 : ℕ) : ℝ) := by
  have h0 := c1K0_pos
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hN' : (4 * f : ℝ) ≤ N₁ := by exact_mod_cast hN
  set u : ℝ := (f : ℝ) - 1 / 4 with hu
  set v : ℝ := ((N₁ + 1 : ℕ) : ℝ) - 1 / 4 with hv
  have hu0 : 0 ≤ u := by rw [hu]; linarith
  have hv4 : 4 * u ≤ v := by rw [hu, hv]; push_cast; linarith
  have hv0 : 0 ≤ v := by linarith
  have hk0 : 0 < (1 + c1K0) ^ (-(2 / 3 : ℝ)) := Real.rpow_pos_of_pos (by linarith) _
  have cube : ∀ w : ℝ, 0 ≤ w → (w ^ (2 / 3 : ℝ)) ^ 3 = w ^ 2 := fun w hw => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hw]
    norm_num
  have cubeK : ((1 + c1K0) ^ (-(2 / 3 : ℝ))) ^ 3 = ((1 + c1K0) ^ 2)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith), ← Real.rpow_natCast,
      ← Real.rpow_neg (by positivity)]
    norm_num
  unfold phiQuantile
  rw [← hu, ← hv]
  have hpos : 0 ≤ u ^ (2 / 3 : ℝ) := Real.rpow_nonneg hu0 _
  have hrhs : 0 ≤ (1 / 2) * (1 + c1K0) ^ (-(2 / 3 : ℝ)) * v ^ (2 / 3 : ℝ) := by
    have := Real.rpow_nonneg hv0 (2 / 3 : ℝ)
    positivity
  refine le_of_pow_le_pow_left₀ (n := 3) (by norm_num) hrhs ?_
  rw [mul_pow, mul_pow, cube u hu0, cube v hv0, cubeK]
  have hs := one_add_c1K0_sq_le
  have hpp : 0 < (1 + c1K0) ^ 2 := by positivity
  rw [show ((1 : ℝ) / 2) ^ 3 * ((1 + c1K0) ^ 2)⁻¹ * v ^ 2 = v ^ 2 / (8 * (1 + c1K0) ^ 2) by
    field_simp; ring]
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg u, mul_nonneg hu0 hu0, mul_le_mul hv4 hv4 (by positivity) hv0]

/-- For `N₁ ≥ 4f` and `r_{N₁+1} ≤ 1`: `r_f ≤ r_{N₁+1}/2` (`K0`(c); `ut:T`, intermediate band). -/
theorem siteRadius_f_le_half {c' : ℝ} (hc' : 0 < c') {f N₁ : ℕ} (hf : 1 ≤ f) (hN : 4 * f ≤ N₁)
    (hr1 : siteRadius c' ((N₁ + 1 : ℕ) : ℝ) ≤ 1) :
    siteRadius c' (f : ℝ) ≤ siteRadius c' ((N₁ + 1 : ℕ) : ℝ) / 2 := by
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hN1 : (1 / 4 : ℝ) < ((N₁ + 1 : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ ((N₁ + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ N₁ + 1)
    linarith
  have h1 := (siteRadius_bounds hc' (by linarith : (1 / 4 : ℝ) ≤ f)).2
  have h2 := (siteRadius_le_one_bounds hc' hN1 hr1).1
  have h3 := phiQuantile_f_le hf hN
  have hl := Cardy.lambdaComb_pos' hc'
  calc siteRadius c' (f : ℝ) ≤ lambdaComb c' * phiQuantile (f : ℝ) := h1
    _ ≤ lambdaComb c' * ((1 / 2) * (1 + c1K0) ^ (-(2 / 3 : ℝ)) *
        phiQuantile ((N₁ + 1 : ℕ) : ℝ)) := by gcongr
    _ = ((1 + c1K0) ^ (-(2 / 3 : ℝ)) * (lambdaComb c' * phiQuantile ((N₁ + 1 : ℕ) : ℝ))) / 2 := by
        ring
    _ ≤ siteRadius c' ((N₁ + 1 : ℕ) : ℝ) / 2 := by gcongr

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.Tail.siteRadius_f_le_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms siteRadius_f_le_half

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.Tail.neg_realLogT_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms neg_realLogT_le

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.Tail.exists_inCell_of_ge'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_inCell_of_ge'

end FormalResearch.ModularBootstrap.Upper.Window.Tail
