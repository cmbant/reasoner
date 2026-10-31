import FormalResearch.FourQubitEntropy.RenyiFullHsOne

/-!
# `lem:fqe-hs-polynomial`: the contact point `x* = 3^{1/5}` and the uniform gap

* `xs = 3^{1/5}` (the HS point), `xs⁵ = 3`, `xs³ = 3^{3/5} = u`.
* `EX_xs`: `E(x*) = 0` (the tangency condition that fixes `α = (3/2)k + 65/36`).
* `olv x` is the one-large spectrum `(x⁵/N, 1/N, 1/N, 1/N)`; `Lam qU aU bU gU (olv x) = PhiX aU x`,
  `olv x* = hsSpec`, `olv 1 = c₂`.
* `delta_pos`: the uniform gap `Δ > 0` (`(HUC)`), by the atanh/log series (`n = 10` terms).
-/

namespace FormalResearch.FourQubitEntropy.RenyiFull

open Set

noncomputable def xs : ℝ := (3 : ℝ) ^ (1 / 5 : ℝ)

theorem xs_pow5 : xs ^ 5 = 3 := by
  unfold xs
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num

theorem xs_pow3 : xs ^ 3 = (3 : ℝ) ^ (3 / 5 : ℝ) := by
  unfold xs
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num

theorem one_lt_xs : 1 < xs := by
  unfold xs
  exact Real.one_lt_rpow (by norm_num) (by norm_num)

theorem xs_pos : 0 < xs := by linarith [one_lt_xs]

theorem xs_lt_two : xs < 2 := by
  by_contra h
  push Not at h
  have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h 5
  rw [xs_pow5] at this
  norm_num at this

theorem kU_eq : kU = 16 / (3 * Real.log 2) * ((xs ^ 3 - 1) / (xs ^ 3 + 1)) := by
  unfold kU; rw [xs_pow3]

theorem pX_xs : pX xs = 1 / 3 := by
  unfold pX
  have h10 : xs ^ 10 = 9 := by
    rw [show (10 : ℕ) = 5 * 2 by norm_num, pow_mul, xs_pow5]; norm_num
  rw [h10, xs_pow5]; norm_num

theorem tX_xs : tX xs = 5 / 36 := by
  unfold tX
  have h15 : xs ^ 15 = 27 := by
    rw [show (15 : ℕ) = 5 * 3 by norm_num, pow_mul, xs_pow5]; norm_num
  rw [h15, xs_pow5]; norm_num

theorem MX_xs : MX xs = 6 * (xs ^ 3 - 1) / (xs ^ 3 + 1) := by
  have hx := xs_pos
  have hN := xs_pow5
  have h1 : xs ^ 3 + 1 ≠ 0 := by positivity
  have h2 : xs ^ 4 + xs ^ 3 + xs ^ 2 + xs + 1 ≠ 0 := by positivity
  have h3 : xs ^ 8 + 3 ≠ 0 := by positivity
  unfold MX
  rw [div_eq_div_iff (mul_ne_zero h2 h3) h1]
  linear_combination (-(xs ^ 2 + xs + 1) * (5 * xs ^ 8 - xs ^ 5 + 3 * xs ^ 3 + 9)) * hN

theorem EX_xs : EX aU xs = 0 := by
  have hx := xs_pos
  have hL : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have h1 : xs ^ 3 + 1 ≠ 0 := by positivity
  unfold EX
  rw [MX_xs, pX_xs, xs_pow5]
  unfold aU
  rw [kU_eq]
  field_simp
  ring

/-! ### The one-large spectrum -/

noncomputable def olv (x : ℝ) : Fin 4 → ℝ :=
  ![x ^ 5 / (x ^ 5 + 3), 1 / (x ^ 5 + 3), 1 / (x ^ 5 + 3), 1 / (x ^ 5 + 3)]

theorem pur_olv {x : ℝ} (hx : 0 ≤ x) : pur (olv x) = pX x := by
  have hN := (N_pos hx).ne'
  unfold pur olv pX
  simp [Fin.sum_univ_four]
  field_simp
  ring

theorem cub_olv {x : ℝ} (hx : 0 ≤ x) : cub (olv x) = tX x := by
  have hN := (N_pos hx).ne'
  unfold cub olv tX
  simp [Fin.sum_univ_four]
  field_simp
  ring

theorem renyi_olv {x : ℝ} (hx : 0 < x) : renyiSpec qU (olv x) = HX x := by
  have hN := N_pos hx.le
  have hG := G_pos hx.le
  unfold renyiSpec olv HX qU
  simp only [Fin.sum_univ_four]
  simp
  have e1 : (x ^ 5 / (x ^ 5 + 3)) ^ (8 / 5 : ℝ) = x ^ 8 / (x ^ 5 + 3) ^ (8 / 5 : ℝ) := by
    rw [Real.div_rpow (by positivity) hN.le, ← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    norm_num
  have e2 : ((x ^ 5 + 3)⁻¹) ^ (8 / 5 : ℝ) = 1 / (x ^ 5 + 3) ^ (8 / 5 : ℝ) := by
    rw [Real.inv_rpow hN.le, one_div]
  rw [e1, e2]
  have hP : 0 < (x ^ 5 + 3) ^ (8 / 5 : ℝ) := Real.rpow_pos_of_pos hN _
  have e3 : x ^ 8 / (x ^ 5 + 3) ^ (8 / 5 : ℝ) + 1 / (x ^ 5 + 3) ^ (8 / 5 : ℝ) +
      1 / (x ^ 5 + 3) ^ (8 / 5 : ℝ) + 1 / (x ^ 5 + 3) ^ (8 / 5 : ℝ) =
      (x ^ 8 + 3) / (x ^ 5 + 3) ^ (8 / 5 : ℝ) := by ring
  rw [e3, Real.logb, Real.log_div hG.ne' hP.ne', Real.log_rpow hN]
  have hL : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  field_simp
  ring

theorem Lam_olv {x : ℝ} (hx : 0 < x) : Lam qU aU bU gU (olv x) = PhiX aU x := by
  unfold Lam PhiX
  rw [renyi_olv hx, pur_olv hx.le, cub_olv hx.le]
  unfold bU gU
  ring

theorem olv_xs : olv xs = hsSpec := by
  have h := xs_pow5
  funext i
  unfold olv hsSpec
  rw [h]
  fin_cases i <;> simp <;> norm_num

theorem olv_one : olv 1 = c2 := by
  funext i
  unfold olv c2
  fin_cases i <;> simp <;> norm_num

theorem PhiX_xs : PhiX aU xs = renyiSpec qU hsSpec := by
  rw [← Lam_olv xs_pos, olv_xs]
  have hp : pur hsSpec = 1 / 3 := by unfold pur hsSpec; simp [Fin.sum_univ_four]; norm_num
  have ht : cub hsSpec = 5 / 36 := by unfold cub hsSpec; simp [Fin.sum_univ_four]; norm_num
  unfold Lam bU gU
  rw [hp, ht]
  ring

theorem PhiX_one : PhiX aU 1 = Lam qU aU bU gU c2 := by
  rw [← olv_one, Lam_olv one_pos]

/-! ### The uniform gap -/

theorem log_ub_series :
    Real.log (1 + (19331 / 10000 : ℝ)⁻¹) ≤
      ∑ i ∈ Finset.range 10, (10000 / 29331 : ℝ) ^ (i + 1) / (i + 1) +
        (10000 / 29331 : ℝ) ^ 11 / (1 - 10000 / 29331) := by
  have hx : |(10000 / 29331 : ℝ)| < 1 := by
    rw [abs_of_pos (by norm_num)]; norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 10
  have hl : Real.log (1 - 10000 / 29331) = -Real.log (1 + (19331 / 10000 : ℝ)⁻¹) := by
    rw [← Real.log_inv]; congr 1; norm_num
  rw [abs_of_pos (show (0 : ℝ) < 10000 / 29331 by norm_num), hl] at h
  have := (abs_le.1 h).1
  linarith

theorem u_gt_u0 : (19331 / 10000 : ℝ) < xs ^ 3 := by
  by_contra hle
  push Not at hle
  have h15 : (xs ^ 3) ^ 5 = 27 := by
    rw [← pow_mul]
    show xs ^ 15 = 27
    rw [show (15 : ℕ) = 5 * 3 by norm_num, pow_mul, xs_pow5]; norm_num
  have := pow_le_pow_left₀ (pow_nonneg xs_pos.le 3) hle 5
  rw [h15] at this
  norm_num at this

theorem delta_log :
    0 < 301 / 144 * Real.log 2 - 5 * (Real.log (xs ^ 3 + 1) - Real.log (xs ^ 3)) +
      2 * (xs ^ 3 - 1) / (xs ^ 3 + 1) := by
  have hu := u_gt_u0
  have hxp := xs_pos
  have hu1 : 0 < xs ^ 3 := by positivity
  have hser := log_ub_series
  have hL := Real.log_two_gt_d9
  -- log(u+1) - log u ≤ log (1 + 1/u0)
  have h1 : Real.log (xs ^ 3 + 1) - Real.log (xs ^ 3) ≤ Real.log (1 + (19331 / 10000 : ℝ)⁻¹) := by
    rw [← Real.log_div (by positivity) hu1.ne']
    apply Real.log_le_log (by positivity)
    rw [div_le_iff₀ hu1]
    have : (1 + (19331 / 10000 : ℝ)⁻¹) * xs ^ 3 = xs ^ 3 + xs ^ 3 / (19331 / 10000) := by
      field_simp
    rw [show (1 + (19331 / 10000 : ℝ)⁻¹) * xs ^ 3 = xs ^ 3 + xs ^ 3 * (19331 / 10000 : ℝ)⁻¹ by ring]
    have h2 : (1 : ℝ) ≤ xs ^ 3 * (19331 / 10000 : ℝ)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (by norm_num)]; linarith
    linarith
  have h2 : 2 * ((19331 / 10000 : ℝ) - 1) / (19331 / 10000 + 1) ≤ 2 * (xs ^ 3 - 1) / (xs ^ 3 + 1) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  norm_num [Finset.sum_range_succ] at hser h2
  linarith

theorem PhiX_diff :
    PhiX aU xs - PhiX aU 1 =
      (301 / 144 * Real.log 2 - 5 * (Real.log (xs ^ 3 + 1) - Real.log (xs ^ 3)) +
        2 * (xs ^ 3 - 1) / (xs ^ 3 + 1)) / (3 * Real.log 2) := by
  have hxp := xs_pos
  have hL : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hu1 : 0 < xs ^ 3 := by positivity
  have h1 : xs ^ 3 + 1 ≠ 0 := by positivity
  have h5 := xs_pow5
  have h8 : xs ^ 8 + 3 = 3 * (xs ^ 3 + 1) := by
    have : xs ^ 8 = xs ^ 5 * xs ^ 3 := by ring
    rw [this, h5]; ring
  have e6 : Real.log (xs ^ 5 + 3) = Real.log 2 + Real.log 3 := by
    rw [h5, show (3 : ℝ) + 3 = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have e8 : Real.log (xs ^ 8 + 3) = Real.log 3 + Real.log (xs ^ 3 + 1) := by
    rw [h8, Real.log_mul (by norm_num) h1]
  have e3 : 3 * Real.log 3 = 5 * Real.log (xs ^ 3) := by
    have a1 : Real.log 3 = 5 * Real.log xs := by
      rw [← h5, Real.log_pow]; norm_num
    have a2 : Real.log (xs ^ 3) = 3 * Real.log xs := by rw [Real.log_pow]; norm_num
    rw [a1, a2]; ring
  have e4 : Real.log (1 ^ 5 + 3 : ℝ) = 2 * Real.log 2 := by
    rw [show ((1 : ℝ) ^ 5 + 3) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hHX : HX xs = ((8 / 3) * (Real.log 2 + Real.log 3) -
      (5 / 3) * (Real.log 3 + Real.log (xs ^ 3 + 1))) / Real.log 2 := by
    unfold HX; rw [e6, e8]
  have hH1 : HX 1 = 2 := by
    unfold HX
    rw [show ((1 : ℝ) ^ 8 + 3) = 1 ^ 5 + 3 by norm_num, e4]
    field_simp; ring
  have hp1 : pX 1 = 1 / 4 := by unfold pX; norm_num
  have ht1 : tX 1 = 1 / 16 := by unfold tX; norm_num
  have hrw : PhiX aU xs - PhiX aU 1 = HX xs - 2 - aU * (1 / 4 - 1 / 3) -
      (1 / 12) * (17 * (1 / 4) - 12 * (1 / 16) - 4) + (10 / 3) * ((1 / 4) ^ 2 - 1 / 9) := by
    unfold PhiX
    rw [pX_xs, tX_xs, hH1, hp1, ht1]
    ring
  rw [hrw, hHX]
  unfold aU
  rw [kU_eq]
  have e3' : Real.log 3 = 5 / 3 * Real.log (xs ^ 3) := by linarith
  rw [e3']
  field_simp
  ring

theorem PhiX_one_lt : PhiX aU 1 < PhiX aU xs := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have := PhiX_diff
  have h2 : 0 < PhiX aU xs - PhiX aU 1 := by
    rw [this]; exact div_pos delta_log (by linarith)
  linarith

end FormalResearch.FourQubitEntropy.RenyiFull
