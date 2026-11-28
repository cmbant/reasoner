module

public import FormalResearch.SignUncertainty.HankelChartSecond

/-!
# Third-order expansion of the Hankel Langer chart: `ct:langer-inv` for `hankelXi`

`constant_terms_lower.tex`, `ct:langer-inv`.  **Proved.**  For the Lean Hankel Langer chart (`chartY`, `chartYinv`,
`hankelXi`) the expansion of `HankelChartSecond` is carried one order further:

* `etaC_one : η_D(4) = 7π⁴/720` (`etaC_of_hasSum`, from `ζ(4) = π⁴/90`), whence `a_{G,1} = 7π²/120`, `a_{E,1} = 7π²/100`;
* `norm_chartK_sub_two`, `norm_chartM_sub_two` (with `norm_cpow23_sub_le`, `norm_psW_sub_two_le`): the quadratic
  expansions of `K(u) = u G(u)` and `M(u) = u E(u)^{2/3}` with cubic remainders, `norm_chartKinv_sub_two`,
  `norm_chartXi_sub_two` for `K⁻¹` and `Ξ = M ∘ K⁻¹` (coefficient `(2/3) a_{E,1} - a_{G,1} = -7π²/600`, the
  `-7π²/600 q` of `ct:sec3`);
* `chartY_real_quad`: `y(w) = -w + (9/25) w² + O(|w|³)` for real `|w| ≤ 10⁻³` (`9/25 = 1/2 - 7/50`);
* **`hankelXi_expansion`**: `c ξ(x) = c/π² - x c^{1/3}/β₁ + (9π²/25)(x/β₁)² c^{-1/3} + O(c⁻¹)` for `|x| ≤ 3`,
  `c ≥ 3·10⁶` (`x = ũ = -v`), the Lean-chart form of `ct:langer-inv` (the CE-lane form is `CtCfu.langer_inv`).
-/

@[expose] public section

open Complex Set Metric Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

/-- `η_D(2j+2) = ζ(2j+2) (1 - 2^{1-(2j+2)})`, from the sum of `1/(n+1)^{2j+2}`. -/
lemma etaC_of_hasSum {j : ℕ} {s : ℝ} (hs : HasSum (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ (2 * j + 2)) s) :
    etaC j = s - 2 * (s / 2 ^ (2 * j + 2)) := by
  set g : ℕ → ℝ := fun n => (1 : ℝ) / ((n : ℝ) + 1) ^ (2 * j + 2) with hg
  have hodd : HasSum (fun k : ℕ => g (2 * k + 1)) (s / 2 ^ (2 * j + 2)) := by
    have h := hs.mul_left (1 / 2 ^ (2 * j + 2) : ℝ)
    have e : (fun k : ℕ => g (2 * k + 1)) =
        fun k : ℕ => (1 / 2 ^ (2 * j + 2) : ℝ) * ((1 : ℝ) / ((k : ℝ) + 1) ^ (2 * j + 2)) := by
      funext k
      simp only [hg]
      push_cast
      have : ((2 : ℝ) * k + 1 + 1) = 2 * ((k : ℝ) + 1) := by ring
      rw [this, mul_pow]
      field_simp
    rw [e]
    convert h using 1
    ring
  have hF : Summable (fun n : ℕ => (-1 : ℝ) ^ n * g n) := hs.summable.alternating
  have heg : Summable (fun k : ℕ => g (2 * k)) :=
    hs.summable.comp_injective (mul_right_injective₀ two_ne_zero)
  have hog : Summable (fun k : ℕ => g (2 * k + 1)) := hodd.summable
  have heF : Summable (fun k : ℕ => (-1 : ℝ) ^ (2 * k) * g (2 * k)) :=
    hF.comp_injective (mul_right_injective₀ two_ne_zero)
  have hoF : Summable (fun k : ℕ => (-1 : ℝ) ^ (2 * k + 1) * g (2 * k + 1)) :=
    hF.comp_injective (fun a b (hab : 2 * a + 1 = 2 * b + 1) => by omega)
  have hsplitF : ∑' k : ℕ, (-1 : ℝ) ^ (2 * k) * g (2 * k)
      + ∑' k : ℕ, (-1 : ℝ) ^ (2 * k + 1) * g (2 * k + 1) = ∑' n : ℕ, (-1 : ℝ) ^ n * g n :=
    tsum_even_add_odd (f := fun n : ℕ => (-1 : ℝ) ^ n * g n) heF hoF
  have hsplitG : ∑' k : ℕ, g (2 * k) + ∑' k : ℕ, g (2 * k + 1) = ∑' n : ℕ, g n :=
    tsum_even_add_odd (f := g) heg hog
  have hE : ∑' k : ℕ, (-1 : ℝ) ^ (2 * k) * g (2 * k) = ∑' k : ℕ, g (2 * k) := by
    congr 1
    funext k
    rw [pow_mul]
    norm_num
  have hO : ∑' k : ℕ, (-1 : ℝ) ^ (2 * k + 1) * g (2 * k + 1) = -∑' k : ℕ, g (2 * k + 1) := by
    rw [← tsum_neg]
    congr 1
    funext k
    rw [pow_succ, pow_mul]
    norm_num
  have h0 : etaC j = ∑' n : ℕ, (-1 : ℝ) ^ n * g n := by
    simp only [etaC, hg]
  rw [h0, ← hsplitF, hE, hO]
  have h1 := hs.tsum_eq
  have h2 := hodd.tsum_eq
  rw [← hsplitG, h2] at h1
  linarith

/-- `η_D(4) = 7π⁴/720`. -/
lemma etaC_one : etaC 1 = 7 * π ^ 4 / 720 := by
  have h := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_four
  have h' : HasSum (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ (2 * 1 + 2)) (π ^ 4 / 90) := by simpa using h
  rw [etaC_of_hasSum h']
  norm_num
  ring

lemma aG_etaC_one : aG etaC 1 = 7 * π ^ 2 / 120 := by
  unfold aG; rw [etaC_one]; have : π ≠ 0 := Real.pi_ne_zero; field_simp; push_cast; ring

lemma aE_etaC_one : aE etaC 1 = 7 * π ^ 2 / 100 := by
  unfold aE; rw [etaC_one]; have : π ≠ 0 := Real.pi_ne_zero; field_simp; push_cast; ring


lemma psW_eq_zero_add_mul {a : ℕ → ℝ} {B : ℝ} (ha : ∀ j, |a j| ≤ B) {w : ℂ} (hw : ‖w‖ < 1) :
    psW a w = a 0 + w * psW (fun j => a (j + 1)) w := by
  have hs := summable_psW ha hw
  have hs' : Summable (fun j : ℕ => (a j : ℂ) * w ^ j) := hs.of_norm
  unfold psW
  rw [hs'.tsum_eq_zero_add, ← tsum_mul_left]
  simp only [pow_zero, mul_one]
  congr 1
  refine tsum_congr (fun j => ?_)
  rw [pow_succ]; ring

/-- second-order expansion of a power series with coefficient bounds `|a j| ≤ B` for `j ≥ 1`
 (and `B₀` for `j = 0`) -/
lemma norm_psW_sub_two_le {a : ℕ → ℝ} {B : ℝ} (ha : ∀ j, |a j| ≤ 1) (ha2 : ∀ j, 2 ≤ j → |a j| ≤ B)
    {w : ℂ} (hw : ‖w‖ < 1) :
    ‖psW a w - a 0 - a 1 * w‖ ≤ B * ‖w‖ ^ 2 / (1 - ‖w‖) := by
  rw [psW_eq_zero_add_mul ha hw]
  have h1 : ∀ j, |(fun j => a (j + 1)) j| ≤ 1 := fun j => ha (j + 1)
  have hs := psW_eq_zero_add_mul h1 hw
  have hB : ∀ j, 1 ≤ j → |(fun j => a (j + 1)) j| ≤ B := fun j hj => ha2 (j + 1) (by omega)
  have := norm_psW_sub_le hB hw
  have e : a 0 + w * psW (fun j => a (j + 1)) w - a 0 - a 1 * w = w * (psW (fun j => a (j + 1)) w - a 1) := by ring
  rw [e, norm_mul]
  calc ‖w‖ * ‖psW (fun j => a (j + 1)) w - a 1‖ ≤ ‖w‖ * (B * ‖w‖ / (1 - ‖w‖)) :=
        mul_le_mul_of_nonneg_left this (norm_nonneg _)
    _ = B * ‖w‖ ^ 2 / (1 - ‖w‖) := by ring



lemma norm_cpow23_sub_le {x : ℂ} (hx : ‖x‖ ≤ 0.01) :
    ‖(1 + x) ^ (((2 / 3 : ℝ)) : ℂ) - 1 - (2 / 3 : ℂ) * x‖ ≤ 0.8 * ‖x‖ ^ 2 := by
  set z : ℂ := (1 + x) ^ (((2 / 3 : ℝ)) : ℂ) with hz
  have hz3 : z ^ 3 = (1 + x) ^ 2 := by
    have h := Complex.cpow_nat_mul (1 + x) 3 (((2 / 3 : ℝ)) : ℂ)
    rw [← h]
    have : ((3 : ℕ) : ℂ) * (((2 / 3 : ℝ)) : ℂ) = (2 : ℕ) := by push_cast; ring
    rw [this, Complex.cpow_natCast]
  have hδ : ‖z - 1‖ ≤ (2 / 3 : ℝ) * ‖x‖ / (1 - ‖x‖) :=
    norm_one_add_cpow_sub_one_le (α := 2 / 3) (by norm_num) (by norm_num) (le_refl _) (by linarith)
  set δ : ℂ := z - 1 with hδd
  have hx0 := norm_nonneg x
  have hδ' : ‖δ‖ ≤ 0.68 * ‖x‖ := by
    refine hδ.trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have e : z - 1 - (2 / 3 : ℂ) * x = (1 / 3 : ℂ) * (x ^ 2 - 3 * δ ^ 2 - δ ^ 3) := by
    have hzd : z = 1 + δ := by rw [hδd]; ring
    rw [hzd] at hz3
    linear_combination (1 / 3 : ℂ) * hz3
  rw [e, norm_mul]
  have h1 : ‖x ^ 2 - 3 * δ ^ 2 - δ ^ 3‖ ≤ ‖x‖ ^ 2 + 3 * ‖δ‖ ^ 2 + ‖δ‖ ^ 3 := by
    calc ‖x ^ 2 - 3 * δ ^ 2 - δ ^ 3‖ ≤ ‖x ^ 2 - 3 * δ ^ 2‖ + ‖δ ^ 3‖ := norm_sub_le _ _
      _ ≤ ‖x ^ 2‖ + ‖3 * δ ^ 2‖ + ‖δ ^ 3‖ := by gcongr; exact norm_sub_le _ _
      _ = _ := by simp [norm_pow]
  have hd0 := norm_nonneg δ
  have h2 : ‖δ‖ ^ 2 ≤ (0.68 * ‖x‖) ^ 2 := pow_le_pow_left₀ hd0 hδ' 2
  have h3 : ‖δ‖ ^ 3 ≤ (0.68 * ‖x‖) ^ 3 := pow_le_pow_left₀ hd0 hδ' 3
  have h4 : (0.68 * ‖x‖) ^ 3 ≤ 0.01 * 0.68 ^ 3 * ‖x‖ ^ 2 := by
    have : (0.68 * ‖x‖) ^ 3 = 0.68 ^ 3 * ‖x‖ ^ 2 * ‖x‖ := by ring
    rw [this]
    nlinarith [sq_nonneg ‖x‖, mul_nonneg (sq_nonneg ‖x‖) hx0]
  have hn : ‖(1 / 3 : ℂ)‖ = 1 / 3 := by simp
  rw [hn]
  nlinarith [sq_nonneg ‖x‖]


section Cubic
variable {η : ℕ → ℝ}

private lemma pi_sq_bounds : (9.869 : ℝ) < π ^ 2 ∧ π ^ 2 < 9.87 :=
  ⟨by nlinarith [Real.pi_gt_d4], by nlinarith [Real.pi_lt_d4, Real.pi_pos]⟩

lemma abs_aG_one_le (h : LangerEta η) : |aG η 1| ≤ 0.61 := by
  refine (abs_aG_le h le_rfl).trans ?_
  have := pi_sq_bounds.1
  rw [div_le_iff₀ (by positivity)]; nlinarith

lemma abs_aE_one_le (h : LangerEta η) : |aE η 1| ≤ 0.74 := by
  refine (abs_aE_le h le_rfl).trans ?_
  have := pi_sq_bounds.1
  rw [div_le_iff₀ (by positivity)]; nlinarith

lemma norm_psW_aG_sub_two (h : LangerEta η) {u : ℂ} (hu : ‖u‖ ≤ 0.035 ^ 2) :
    ‖psW (aG η) u - 1 - aG η 1 * u‖ ≤ 0.7 * ‖u‖ ^ 2 := by
  have h1 : ‖u‖ < 1 := lt_of_le_of_lt hu (by norm_num)
  have := norm_psW_sub_two_le (a := aG η) (B := 6 / π ^ 2) (abs_aG_le_one h)
    (fun j hj => abs_aG_le h (by omega)) h1
  rw [aG_zero h] at this
  refine this.trans ?_
  have hp := pi_sq_bounds.1
  have hu0 := norm_nonneg u
  have h2 : (1 - 0.035 ^ 2 : ℝ) ≤ 1 - ‖u‖ := by linarith
  have h3 : 6 / π ^ 2 ≤ 0.608 := by rw [div_le_iff₀ (by positivity)]; nlinarith
  calc 6 / π ^ 2 * ‖u‖ ^ 2 / (1 - ‖u‖) ≤ 0.608 * ‖u‖ ^ 2 / (1 - 0.035 ^ 2) := by
        apply div_le_div₀ (by positivity) (by gcongr) (by norm_num) h2
    _ = (0.608 / (1 - 0.035 ^ 2)) * ‖u‖ ^ 2 := by ring
    _ ≤ 0.7 * ‖u‖ ^ 2 := by
        have : (0.608 / (1 - 0.035 ^ 2) : ℝ) ≤ 0.7 := by norm_num
        gcongr

lemma norm_psW_aE_sub_two (h : LangerEta η) {u : ℂ} (hu : ‖u‖ ≤ 0.035 ^ 2) :
    ‖psW (aE η) u - 1 - aE η 1 * u‖ ≤ 0.8 * ‖u‖ ^ 2 := by
  have h1 : ‖u‖ < 1 := lt_of_le_of_lt hu (by norm_num)
  have := norm_psW_sub_two_le (a := aE η) (B := 36 / (5 * π ^ 2)) (abs_aE_le_one h)
    (fun j hj => abs_aE_le h (by omega)) h1
  rw [aE_zero h] at this
  refine this.trans ?_
  have hp := pi_sq_bounds.1
  have hu0 := norm_nonneg u
  have h2 : (1 - 0.035 ^ 2 : ℝ) ≤ 1 - ‖u‖ := by linarith
  have h3 : 36 / (5 * π ^ 2) ≤ 0.73 := by rw [div_le_iff₀ (by positivity)]; nlinarith
  calc 36 / (5 * π ^ 2) * ‖u‖ ^ 2 / (1 - ‖u‖) ≤ 0.73 * ‖u‖ ^ 2 / (1 - 0.035 ^ 2) := by
        apply div_le_div₀ (by positivity) (by gcongr) (by norm_num) h2
    _ = (0.73 / (1 - 0.035 ^ 2)) * ‖u‖ ^ 2 := by ring
    _ ≤ 0.8 * ‖u‖ ^ 2 := by
        have : (0.73 / (1 - 0.035 ^ 2) : ℝ) ≤ 0.8 := by norm_num
        gcongr

lemma norm_chartK_sub_two (h : LangerEta η) {u : ℂ} (hu : ‖u‖ ≤ 0.035 ^ 2) :
    ‖chartK η u - u - aG η 1 * u ^ 2‖ ≤ 0.7 * ‖u‖ ^ 3 := by
  have h1 := norm_psW_aG_sub_two h hu
  have e : chartK η u - u - aG η 1 * u ^ 2 = u * (psW (aG η) u - 1 - aG η 1 * u) := by
    unfold chartK; ring
  rw [e, norm_mul]
  calc ‖u‖ * ‖psW (aG η) u - 1 - aG η 1 * u‖ ≤ ‖u‖ * (0.7 * ‖u‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = 0.7 * ‖u‖ ^ 3 := by ring

lemma norm_chartM_sub_two (h : LangerEta η) {u : ℂ} (hu : ‖u‖ ≤ 0.035 ^ 2) :
    ‖chartM η u - u - (2 / 3 : ℂ) * aE η 1 * u ^ 2‖ ≤ 1.1 * ‖u‖ ^ 3 := by
  have h1 := norm_psW_aE_sub_two h hu
  have h0 := norm_psW_aE_sub_one_lin h hu
  have hu0 := norm_nonneg u
  have hx : ‖psW (aE η) u - 1‖ ≤ 0.01 := by nlinarith
  have hc := norm_cpow23_sub_le hx
  set x := psW (aE η) u - 1 with hxd
  have hF : (1 + x) = psW (aE η) u := by rw [hxd]; ring
  rw [hF] at hc
  have e : chartM η u - u - (2 / 3 : ℂ) * aE η 1 * u ^ 2 =
      u * ((psW (aE η) u ^ (((2 / 3 : ℝ)) : ℂ) - 1 - (2 / 3 : ℂ) * x) +
        (2 / 3 : ℂ) * (psW (aE η) u - 1 - aE η 1 * u)) := by
    unfold chartM powMapU; rw [hxd]; ring
  rw [e, norm_mul]
  have hxsq : ‖x‖ ^ 2 ≤ (0.8 * ‖u‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h0 2
  have h23 : ‖(2 / 3 : ℂ)‖ = 2 / 3 := by simp
  have hb : ‖(psW (aE η) u ^ (((2 / 3 : ℝ)) : ℂ) - 1 - (2 / 3 : ℂ) * x) +
        (2 / 3 : ℂ) * (psW (aE η) u - 1 - aE η 1 * u)‖ ≤ 1.1 * ‖u‖ ^ 2 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, h23]
    nlinarith [sq_nonneg ‖u‖]
  calc ‖u‖ * _ ≤ ‖u‖ * (1.1 * ‖u‖ ^ 2) := mul_le_mul_of_nonneg_left hb hu0
    _ = 1.1 * ‖u‖ ^ 3 := by ring


lemma norm_chartKinv_sub_two (h : LangerEta η) {v : ℂ} (hv : v ∈ chartVdisc) :
    ‖chartKinv η v - v + aG η 1 * v ^ 2‖ ≤ 2 * ‖v‖ ^ 3 := by
  obtain ⟨hu, hK⟩ := chartKinv_spec h hv
  have hun : ‖chartKinv η v‖ ≤ 0.035 ^ 2 := (mem_ball_zero_iff.1 hu).le
  have hn := norm_chartKinv_le h hv
  set u := chartKinv η v with hud
  have hv0 := norm_nonneg v
  have hu0 := norm_nonneg u
  have hu1 : ‖u‖ ≤ 1.001 * ‖v‖ := by nlinarith
  have h1 := norm_chartK_sub_two h hun
  rw [hK] at h1
  have hg := abs_aG_one_le h
  have hgn : ‖(aG η 1 : ℂ)‖ ≤ 0.61 := by rw [Complex.norm_real, Real.norm_eq_abs]; exact hg
  -- `‖v - u‖ ≤ 0.62 ‖u‖²`
  have hvu : ‖v - u‖ ≤ 0.62 * ‖u‖ ^ 2 := by
    have e : v - u = (v - u - aG η 1 * u ^ 2) + aG η 1 * u ^ 2 := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_pow]
    have : 0.7 * ‖u‖ ^ 3 ≤ 0.7 * 0.035 ^ 2 * ‖u‖ ^ 2 := by
      have : ‖u‖ ^ 3 = ‖u‖ * ‖u‖ ^ 2 := by ring
      rw [this]; nlinarith [sq_nonneg ‖u‖]
    nlinarith [sq_nonneg ‖u‖, norm_nonneg (aG η 1 : ℂ)]
  have e : u - v + aG η 1 * v ^ 2 = -(v - u - aG η 1 * u ^ 2) + aG η 1 * ((v - u) * (v + u)) := by ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_neg]
  have hvu' : ‖v + u‖ ≤ 2.001 * ‖v‖ := by
    refine (norm_add_le _ _).trans ?_; nlinarith
  have hsq : ‖u‖ ^ 2 ≤ (1.001 * ‖v‖) ^ 2 := pow_le_pow_left₀ hu0 hu1 2
  have hcu : ‖u‖ ^ 3 ≤ (1.001 * ‖v‖) ^ 3 := pow_le_pow_left₀ hu0 hu1 3
  have h3 : ‖(v - u) * (v + u)‖ ≤ 0.62 * (1.001 * ‖v‖) ^ 2 * (2.001 * ‖v‖) := by
    rw [norm_mul]
    exact mul_le_mul (hvu.trans (by nlinarith)) hvu' (norm_nonneg _) (by positivity)
  have h4 : ‖aG η 1 * ((v - u) * (v + u))‖ ≤ 0.61 * (0.62 * (1.001 * ‖v‖) ^ 2 * (2.001 * ‖v‖)) := by
    rw [norm_mul]
    exact mul_le_mul hgn h3 (norm_nonneg _) (by norm_num)
  have h5 : 0.7 * ‖u‖ ^ 3 ≤ 0.7 * (1.001 * ‖v‖) ^ 3 := by nlinarith
  nlinarith [pow_nonneg hv0 3]

lemma norm_chartXi_sub_two (h : LangerEta η) {v : ℂ} (hv : v ∈ chartVdisc) :
    ‖chartXi η v - v - ((2 / 3 : ℂ) * aE η 1 - aG η 1) * v ^ 2‖ ≤ 5 * ‖v‖ ^ 3 := by
  obtain ⟨hu, hK⟩ := chartKinv_spec h hv
  have hun : ‖chartKinv η v‖ ≤ 0.035 ^ 2 := (mem_ball_zero_iff.1 hu).le
  have hn := norm_chartKinv_le h hv
  have hk := norm_chartKinv_sub_two h hv
  have hm := norm_chartM_sub_two h hun
  set u := chartKinv η v with hud
  have hv0 := norm_nonneg v
  have hu0 := norm_nonneg u
  have hu1 : ‖u‖ ≤ 1.001 * ‖v‖ := by nlinarith
  have hg := abs_aG_one_le h
  have he := abs_aE_one_le h
  have hgn : ‖(aG η 1 : ℂ)‖ ≤ 0.61 := by rw [Complex.norm_real, Real.norm_eq_abs]; exact hg
  have hen : ‖(aE η 1 : ℂ)‖ ≤ 0.74 := by rw [Complex.norm_real, Real.norm_eq_abs]; exact he
  have hvu : ‖v - u‖ ≤ 0.62 * ‖u‖ ^ 2 := by
    have h1 := norm_chartK_sub_two h hun
    rw [hK] at h1
    have e : v - u = (v - u - aG η 1 * u ^ 2) + aG η 1 * u ^ 2 := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_pow]
    have : 0.7 * ‖u‖ ^ 3 ≤ 0.7 * 0.035 ^ 2 * ‖u‖ ^ 2 := by
      have : ‖u‖ ^ 3 = ‖u‖ * ‖u‖ ^ 2 := by ring
      rw [this]; nlinarith [sq_nonneg ‖u‖]
    nlinarith [sq_nonneg ‖u‖, norm_nonneg (aG η 1 : ℂ)]
  have hvu' : ‖v + u‖ ≤ 2.001 * ‖v‖ := by
    refine (norm_add_le _ _).trans ?_; nlinarith
  have hsq : ‖u‖ ^ 2 ≤ (1.001 * ‖v‖) ^ 2 := pow_le_pow_left₀ hu0 hu1 2
  have hcu : ‖u‖ ^ 3 ≤ (1.001 * ‖v‖) ^ 3 := pow_le_pow_left₀ hu0 hu1 3
  have h3 : ‖(v - u) * (v + u)‖ ≤ 0.62 * (1.001 * ‖v‖) ^ 2 * (2.001 * ‖v‖) := by
    rw [norm_mul]
    exact mul_le_mul (hvu.trans (by nlinarith)) hvu' (norm_nonneg _) (by positivity)
  have e : chartXi η v - v - ((2 / 3 : ℂ) * aE η 1 - aG η 1) * v ^ 2 =
      (chartM η u - u - (2 / 3 : ℂ) * aE η 1 * u ^ 2) + (u - v + aG η 1 * v ^ 2) +
        (2 / 3 : ℂ) * aE η 1 * ((u - v) * (u + v)) := by
    unfold chartXi; rw [← hud]; ring
  rw [e]
  have h23 : ‖(2 / 3 : ℂ)‖ = 2 / 3 := by simp
  have h6 : ‖(2 / 3 : ℂ) * aE η 1 * ((u - v) * (u + v))‖ ≤ (2 / 3) * 0.74 * (0.62 * (1.001 * ‖v‖) ^ 2 * (2.001 * ‖v‖)) := by
    rw [norm_mul, norm_mul, h23]
    have : ‖(u - v) * (u + v)‖ ≤ 0.62 * (1.001 * ‖v‖) ^ 2 * (2.001 * ‖v‖) := by
      have e2 : (u - v) * (u + v) = -((v - u) * (v + u)) := by ring
      rw [e2, norm_neg]; exact h3
    exact mul_le_mul (mul_le_mul le_rfl hen (norm_nonneg _) (by norm_num)) this (norm_nonneg _) (by norm_num)
  have h7 : 1.1 * ‖u‖ ^ 3 ≤ 1.1 * (1.001 * ‖v‖) ^ 3 := by nlinarith
  refine ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans ?_
  nlinarith [pow_nonneg hv0 3]


lemma real_log_one_add_quad {w : ℝ} (hw : |w| ≤ 1e-3) :
    |Real.log (1 + w) - w + w ^ 2 / 2| ≤ 1.002 * |w| ^ 3 := by
  have hw1 : |-w| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hw1 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, abs_neg] at h
  have e : (1 : ℝ) - -w = 1 + w := by ring
  rw [e] at h
  refine le_trans (le_of_eq ?_) (h.trans ?_)
  · congr 1; push_cast; ring
  · rw [div_le_iff₀ (by linarith [abs_nonneg w])]
    nlinarith [pow_nonneg (abs_nonneg w) 3]


/-- `y(w) = -w + (9/25) w² + O(|w|³)` for real `w`, `|w| ≤ 10⁻³` (`ct:langer-inv` at the level of the chart
`y`; the coefficient `9/25 = 1/2 - 7/50` comes from `η_D(4) = 7π⁴/720`). -/
lemma chartY_real_quad {w : ℝ} (hw : |w| ≤ 1e-3) :
    ‖chartY etaC (w : ℂ) - ((-w + 9 / 25 * w ^ 2 : ℝ) : ℂ)‖ ≤ 9 * |w| ^ 3 := by
  have hwn : ‖(w : ℂ)‖ ≤ 1e-3 := by rwa [Complex.norm_real, Real.norm_eq_abs]
  have hw' := abs_le.1 hw
  have hpos : 0 < 1 + w := by linarith
  set L : ℝ := Real.log (1 + w) with hL
  have hLc : Complex.log (1 + (w : ℂ)) = (L : ℂ) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_add, ← Complex.ofReal_log hpos.le]
  set v : ℝ := -(12 / π ^ 2) * L with hvd
  have hv : chartVofW (w : ℂ) = (v : ℂ) := by
    unfold chartVofW; rw [hLc, hvd]; push_cast; ring
  have hmem := chartVofW_mem hwn
  rw [hv] at hmem
  have hX := norm_chartXi_sub_two langerEta_etaC hmem
  rw [aG_etaC_one, aE_etaC_one] at hX
  have hlog := real_log_one_add_quad hw
  have hpi := pi_sq_bounds
  have hpi0 : 0 < π ^ 2 := by positivity
  have hw0 := abs_nonneg w
  have hLw : |L - w| ≤ 0.51 * |w| ^ 2 := by
    have h1 : |L - w + w ^ 2 / 2| ≤ 1.002 * |w| ^ 3 := hlog
    have h2 : |w ^ 2 / 2| = |w| ^ 2 / 2 := by rw [abs_div, abs_pow]; norm_num
    have h3 : |L - w| ≤ |L - w + w ^ 2 / 2| + |w ^ 2 / 2| := by
      have := abs_sub (L - w + w ^ 2 / 2) (w ^ 2 / 2); simpa using this
    have h4 : |w| ^ 3 ≤ 1e-3 * |w| ^ 2 := by
      have : |w| ^ 3 = |w| * |w| ^ 2 := by ring
      rw [this]; nlinarith [sq_nonneg |w|]
    nlinarith
  have hLabs : |L| ≤ 1.001 * |w| := by
    have h1 : |L| ≤ |L - w| + |w| := by
      have := abs_sub_abs_le_abs_sub L w; linarith
    have h4 : |w| ^ 2 ≤ 1e-3 * |w| := by nlinarith
    nlinarith
  have hvn : ‖(v : ℂ)‖ ≤ 1.22 * |w| := by
    rw [Complex.norm_real, Real.norm_eq_abs, hvd, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < 12 / π ^ 2)]
    have h3 : 12 / π ^ 2 ≤ 1.216 := by rw [div_le_iff₀ hpi0]; nlinarith
    calc 12 / π ^ 2 * |L| ≤ 1.216 * (1.001 * |w|) := by gcongr
      _ ≤ 1.22 * |w| := by nlinarith
  have hvc : ‖(v : ℂ)‖ ^ 3 ≤ (1.22 * |w|) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hvn 3
  have hvL : (π ^ 2 / 12 : ℝ) * v = -L := by rw [hvd]; field_simp
  -- the algebra: `y = -L - (7/50) L² + (π²/12) ρ`
  have e : chartY etaC (w : ℂ) - ((-w + 9 / 25 * w ^ 2 : ℝ) : ℂ) =
      (((-L + w - w ^ 2 / 2 : ℝ)) : ℂ) + ((-(7 / 50) * (L ^ 2 - w ^ 2) : ℝ) : ℂ) +
        ((π ^ 2 / 12 : ℝ) : ℂ) * (chartXi etaC (v : ℂ) - (v : ℂ) -
          ((2 / 3 : ℂ) * ((7 * π ^ 2 / 100 : ℝ) : ℂ) - ((7 * π ^ 2 / 120 : ℝ) : ℂ)) * (v : ℂ) ^ 2) := by
    unfold chartY; rw [hv]
    have h1 : ((π ^ 2 / 12 : ℝ) : ℂ) * (v : ℂ) = ((-L : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, hvL]
    have h2 : ((π ^ 2 / 12 : ℝ) : ℂ) * ((2 / 3 : ℂ) * ((7 * π ^ 2 / 100 : ℝ) : ℂ) - ((7 * π ^ 2 / 120 : ℝ) : ℂ)) * (v : ℂ) ^ 2 = ((-(7 / 50) * L ^ 2 : ℝ) : ℂ) := by
      have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
      have : (π ^ 2 / 12 : ℝ) * ((2 / 3) * (7 * π ^ 2 / 100) - 7 * π ^ 2 / 120) * v ^ 2 = -(7 / 50) * L ^ 2 := by
        rw [hvd]; field_simp; ring
      rw [← Complex.ofReal_ofNat, ← Complex.ofReal_ofNat, ← Complex.ofReal_div]
      rw [← this]; push_cast; ring
    push_cast at h1 h2 ⊢
    linear_combination h1 + h2
  rw [e]
  have t1 : ‖(((-L + w - w ^ 2 / 2 : ℝ)) : ℂ)‖ ≤ 1.002 * |w| ^ 3 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    have : |-L + w - w ^ 2 / 2| = |L - w + w ^ 2 / 2| := by rw [← abs_neg]; congr 1; ring
    rw [this]; exact hlog
  have t2 : ‖((-(7 / 50) * (L ^ 2 - w ^ 2) : ℝ) : ℂ)‖ ≤ 0.15 * |w| ^ 3 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_neg]
    have h1 : |L ^ 2 - w ^ 2| = |L - w| * |L + w| := by rw [← abs_mul]; congr 1; ring
    have h2 : |L + w| ≤ 2.01 * |w| := by
      have := abs_add_le L w; nlinarith
    have h3 : |L - w| * |L + w| ≤ 0.51 * |w| ^ 2 * (2.01 * |w|) :=
      mul_le_mul hLw h2 (abs_nonneg _) (by positivity)
    have : |(7 / 50 : ℝ)| = 7 / 50 := abs_of_pos (by norm_num)
    rw [this, h1]
    nlinarith [pow_nonneg hw0 3]
  have t3 : ‖((π ^ 2 / 12 : ℝ) : ℂ) * (chartXi etaC (v : ℂ) - (v : ℂ) -
          ((2 / 3 : ℂ) * ((7 * π ^ 2 / 100 : ℝ) : ℂ) - ((7 * π ^ 2 / 120 : ℝ) : ℂ)) * (v : ℂ) ^ 2)‖ ≤ 7.5 * |w| ^ 3 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have h1 : π ^ 2 / 12 ≤ 0.8225 := by rw [div_le_iff₀ (by norm_num)]; nlinarith
    calc π ^ 2 / 12 * _ ≤ 0.8225 * (5 * ‖(v : ℂ)‖ ^ 3) :=
          mul_le_mul h1 hX (norm_nonneg _) (by norm_num)
      _ ≤ 0.8225 * (5 * (1.22 * |w|) ^ 3) := by gcongr
      _ ≤ 7.5 * |w| ^ 3 := by nlinarith [pow_nonneg hw0 3]
  refine ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans ?_
  nlinarith [pow_nonneg hw0 3]


set_option maxHeartbeats 800000 in
/-- **`ct:langer-inv` for the Lean Hankel chart:** `c ξ(x) = c/π² - x c^{1/3}/β₁ + (9π²/25)(x/β₁)² c^{-1/3} + O(c⁻¹)`
for `|x| ≤ 3` (`x = ũ = -v`), `c ≥ 3·10⁶`.  **Not a duplicate of `CtCfu.langer_inv`:** that statement is about the
function `Ξ(a) = exp(m(τ₀(a)))/π²` of the CE/edge-phase construction, this one about the series-built Hankel chart
`hankelXi` (`chartYinv etaC`); the two are the same chart in the paper, but their identification is not proved in Lean,
and `ctChartGap_sharp` only need this one. -/
theorem hankelXi_expansion : ∃ C : ℝ, ∀ c : ℝ, 3e6 ≤ c → ∀ x : ℝ, |x| ≤ 3 →
    |c * hankelXi c x - (c / π ^ 2 - x * c ^ (1 / 3 : ℝ) / hankelBeta1 +
      9 * π ^ 2 / 25 * (x / hankelBeta1) ^ 2 * c ^ (-(1 / 3) : ℝ))| ≤ C * c⁻¹ := by
  have hkp := langerKappa_pos
  refine ⟨12 * 27 / (π ^ 2 * langerKappa ^ 3), fun c hc x hx => ?_⟩
  have hc0 : 0 < c := by linarith
  have hK := hankelBand_langerScale_ge hc
  have hK0 : 0 < langerScale c := by linarith
  have hx' : |x| ≤ langerScale c * 4.94e-4 := by nlinarith
  obtain ⟨hreal, _⟩ := chartYinv_real_point hc0 hx'
  set yr : ℝ := x / langerScale c with hyr
  set w : ℝ := (chartYinv etaC (yr : ℂ)).re with hw
  have hyn : ‖(yr : ℂ)‖ ≤ 4.94e-4 := by
    rw [Complex.norm_real, Real.norm_eq_abs, hyr, abs_div, abs_of_pos hK0, div_le_iff₀ hK0]
    linarith
  have hq := norm_chartYinv_add_sq hyn
  rw [hreal, ← Complex.ofReal_add, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs] at hq
  have hwn : |w| ≤ 5e-4 := (chartYinv_real_point hc0 hx').2
  obtain ⟨hball, hspec⟩ := chartYinv_spec etaC (exists_chartY_small langerEta_etaC hyn)
  rw [hreal] at hspec
  have hr := chartY_real_quad (w := w) (by linarith)
  rw [hspec, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hr
  have hyabs : |yr| ≤ 3 / langerScale c := by
    rw [hyr, abs_div, abs_of_pos hK0]; gcongr
  have hy0 := abs_nonneg yr
  have hw0 := abs_nonneg w
  have hwy : |w| ≤ 1.0031 * |yr| := by
    have : |w| ≤ |w + yr| + |yr| := by
      have := abs_sub_abs_le_abs_sub w (-yr); rw [abs_neg] at this; simpa [sub_neg_eq_add] using this
    have h2 : |yr| ^ 2 ≤ 1e-3 * |yr| := by
      have : |yr| ≤ 3 / 1e4 := hyabs.trans (by rw [div_le_div_iff₀ hK0 (by norm_num)]; nlinarith)
      nlinarith
    nlinarith [sq_abs yr]
  -- `w = -y + (9/25) y² + R`, `|R| ≤ 12 |y|³`
  have hR : |w - (-yr + 9 / 25 * yr ^ 2)| ≤ 12 * |yr| ^ 3 := by
    have e : w - (-yr + 9 / 25 * yr ^ 2) = (yr - (-w + 9 / 25 * w ^ 2)) + 9 / 25 * ((w - yr) * (w + yr)) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
    have h1 : |w - yr| ≤ 2.0031 * |yr| := by
      have := abs_sub w yr; nlinarith
    have h2 : |(w - yr) * (w + yr)| ≤ 2.0031 * |yr| * (3.1 * yr ^ 2) := by
      rw [abs_mul]
      exact mul_le_mul h1 (hq.trans (by rw [sq_abs])) (abs_nonneg _) (by positivity)
    have h3 : |w| ^ 3 ≤ (1.0031 * |yr|) ^ 3 := pow_le_pow_left₀ hw0 hwy 3
    have h4 : |(9 / 25 : ℝ)| = 9 / 25 := abs_of_pos (by norm_num)
    rw [h4]
    have : yr ^ 2 = |yr| ^ 2 := (sq_abs yr).symm
    rw [this] at h2
    nlinarith [pow_nonneg hy0 3]
  -- assemble
  set k : ℝ := c ^ (1 / 3 : ℝ) with hkdef
  have hk0 : 0 < k := Real.rpow_pos_of_pos hc0 _
  have hk3 : k ^ 3 = c := by
    rw [hkdef, ← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
  have hkm : c ^ (2 / 3 : ℝ) = k ^ 2 := by
    rw [hkdef, ← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
  have hKdef : langerScale c = k ^ 2 * langerKappa := by
    show c ^ (2 / 3 : ℝ) * langerKappa = _
    rw [hkm]
  have hkn : c ^ (-(1 / 3) : ℝ) = k⁻¹ := by
    rw [Real.rpow_neg hc0.le]
  have hβ : hankelBeta1 = langerKappa * π ^ 2 := hankelBeta1_eq_kappa
  have hxi : hankelXi c x = (1 + w) / π ^ 2 := rfl
  have hpi : 0 < π ^ 2 := by positivity
  have hmain : c * hankelXi c x - (c / π ^ 2 - x * k / hankelBeta1 + 9 * π ^ 2 / 25 * (x / hankelBeta1) ^ 2 * k⁻¹) =
      c / π ^ 2 * (w - (-yr + 9 / 25 * yr ^ 2)) := by
    rw [hxi, hyr, hKdef, hβ, ← hk3]
    field_simp
    ring
  rw [hkn, hmain, abs_mul, abs_of_pos (by positivity : 0 < c / π ^ 2)]
  calc c / π ^ 2 * |w - (-yr + 9 / 25 * yr ^ 2)| ≤ c / π ^ 2 * (12 * |yr| ^ 3) :=
        mul_le_mul_of_nonneg_left hR (by positivity)
    _ ≤ c / π ^ 2 * (12 * (3 / langerScale c) ^ 3) := by gcongr
    _ = 12 * 27 / (π ^ 2 * langerKappa ^ 3) * c⁻¹ := by
        rw [hKdef, ← hk3]
        field_simp
        ring

end Cubic

/-- info: 'FormalResearch.SignUncertainty.hankelXi_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelXi_expansion

/-- info: 'FormalResearch.SignUncertainty.etaC_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms etaC_one

end FormalResearch.SignUncertainty
