import FormalResearch.FourQubitEntropy.RenyiFullLHConst

/-!
# The rational approximations `(LH2)` of the three `K`-dependent entropy terms

Paper E, `lem:fqe-large-head-dual`.  For `13/25 ≤ v ≤ 1`:

* `|h(127/200, v) - ĥ₀(v)| ≤ 10⁻⁴`,
* `|h(1/2, v) - ĥ_l(v)| ≤ 6·10⁻⁴`,
* `|h_a(127/200, v) - ĥ_a(v)| ≤ 10⁻⁶`,

with `ĥ₀ = H₀ - 2U (v-3/4)/(2ρ+v+3/4)`, `ĥ_l = H_l - 2U (v-3/4)/(v+11/4)`,
`ĥ_a = -2qU((ρ-v)/(ρ+v) - 27/100)/(9271/10000)` and the rounded constants
`U = 2.45774282`, `ρ = 2.40792594`, `H₀ = 1.10489073`, `H_l = 1.32818582`.
-/

namespace FormalResearch.FourQubitEntropy.RenyiFull

open Finset

noncomputable def hh0 (v : ℝ) : ℝ :=
  110489073 / 10 ^ 8 - 2 * (245774282 / 10 ^ 8) * (v - 3 / 4) / (2 * (240792594 / 10 ^ 8) + v + 3 / 4)
noncomputable def hhl (v : ℝ) : ℝ :=
  132818582 / 10 ^ 8 - 2 * (245774282 / 10 ^ 8) * (v - 3 / 4) / (v + 11 / 4)
noncomputable def hha (v : ℝ) : ℝ :=
  -2 * (1587 / 1000) * (245774282 / 10 ^ 8) * ((240792594 / 10 ^ 8 - v) / (240792594 / 10 ^ 8 + v) - 27 / 100) /
    (9271 / 10000)

/-- Generic error propagation. -/
theorem approx_generic {u U y y' E H H' δH δu δy ym Em um Um : ℝ}
    (hH : |H - H'| ≤ δH) (hu : |u - U| ≤ δu) (hy : |y - y'| ≤ δy) (hym : |y| ≤ ym) (hE : |E| ≤ Em)
    (hum : |u| ≤ um) (hUm : |U| ≤ Um) :
    |(H - u * (2 * y + E)) - (H' - 2 * U * y')| ≤ δH + 2 * (δu * ym + Um * δy) + um * Em := by
  have e : (H - u * (2 * y + E)) - (H' - 2 * U * y') =
      (H - H') - 2 * ((u - U) * y + U * (y - y')) - u * E := by ring
  rw [e]
  have h1 : |(u - U) * y| ≤ δu * ym := by
    rw [abs_mul]; exact mul_le_mul hu hym (abs_nonneg _) ((abs_nonneg _).trans hu)
  have h2 : |U * (y - y')| ≤ Um * δy := by
    rw [abs_mul]; exact mul_le_mul hUm hy (abs_nonneg _) ((abs_nonneg _).trans hUm)
  have h3 : |u * E| ≤ um * Em := by
    rw [abs_mul]; exact mul_le_mul hum hE (abs_nonneg _) ((abs_nonneg _).trans hum)
  have h4 : |(u - U) * y + U * (y - y')| ≤ δu * ym + Um * δy := (abs_add_le _ _).trans (add_le_add h1 h2)
  have a1 := abs_le.1 hH
  have a2 := abs_le.1 h4
  have a3 := abs_le.1 h3
  rw [abs_le]
  constructor <;> nlinarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2]


theorem lhR_pos : 0 < lhR := by
  have := lhR_enc.1
  linarith

theorem lhU_pos : 0 < lhU := by
  have := lhU_enc.1
  linarith

theorem lhZ_a0 {v : ℝ} : lhZ qS v (127 / 200) = (73 / 200 : ℝ) ^ qS * (lhR + v) := by
  have h0 : 0 < (73 / 200 : ℝ) ^ qS := Real.rpow_pos_of_pos (by norm_num) _
  have e : lhR = (127 / 200 : ℝ) ^ qS / (73 / 200 : ℝ) ^ qS := by
    unfold lhR
    rw [← Real.div_rpow (by norm_num) (by norm_num)]
    norm_num
  unfold lhZ
  rw [e]
  have e1 : (1 - 127 / 200 : ℝ) = 73 / 200 := by norm_num
  rw [e1]
  field_simp

theorem log_ratio_eq {R v w : ℝ} (hR : 0 < R) (hv : 0 < v) (hw : 0 < w) :
    Real.log (1 + (v - w) / (2 * R + v + w)) - Real.log (1 - (v - w) / (2 * R + v + w)) =
      Real.log (R + v) - Real.log (R + w) := by
  have hD : 0 < 2 * R + v + w := by linarith
  have h1 : 1 + (v - w) / (2 * R + v + w) = 2 * (R + v) / (2 * R + v + w) := by field_simp; ring
  have h2 : 1 - (v - w) / (2 * R + v + w) = 2 * (R + w) / (2 * R + v + w) := by field_simp; ring
  rw [h1, h2, Real.log_div (by positivity) hD.ne', Real.log_div (by positivity) hD.ne',
    Real.log_mul (by norm_num) (by positivity), Real.log_mul (by norm_num) (by positivity)]
  ring

theorem hfun_a0_eq {v : ℝ} (hv : 0 < v) :
    hfun qS v (127 / 200) =
      H0t - lhU * (Real.log (1 + (v - 3 / 4) / (2 * lhR + v + 3 / 4)) -
        Real.log (1 - (v - 3 / 4) / (2 * lhR + v + 3 / 4))) := by
  have hR := lhR_pos
  have h0 : 0 < (73 / 200 : ℝ) ^ qS := Real.rpow_pos_of_pos (by norm_num) _
  rw [log_ratio_eq hR hv (by norm_num : (0 : ℝ) < 3 / 4)]
  have hc : (qS - 1) * Real.log 2 ≠ 0 := by
    have : 0 < qS - 1 := by unfold qS; norm_num
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    positivity
  unfold H0t hfun lhU
  rw [lhZ_a0, lhZ_a0, Real.log_mul h0.ne' (by linarith), Real.log_mul h0.ne' (by linarith)]
  field_simp
  ring


theorem H0_approx {v : ℝ} (hv1 : 13 / 25 ≤ v) (hv2 : v ≤ 1) :
    |hfun qS v (127 / 200) - hh0 v| ≤ 1 / 10000 := by
  have hv : 0 < v := by linarith
  have hRe := lhR_enc
  have hUe := lhU_enc
  have hHe := H0t_enc
  set R := lhR with hR
  have hD : 0 < 2 * R + v + 3 / 4 := by linarith [hRe.1]
  have hD' : 0 < 2 * (240792594 / 10 ^ 8 : ℝ) + v + 3 / 4 := by linarith
  -- bound on y
  have hy : |(v - 3 / 4) / (2 * R + v + 3 / 4)| ≤ 383 / 10000 := by
    rw [abs_div, abs_of_pos hD, div_le_iff₀ hD, abs_le]
    constructor <;> nlinarith [hRe.1]
  have hy' : |(v - 3 / 4) / (2 * R + v + 3 / 4) - (v - 3 / 4) / (2 * (240792594 / 10 ^ 8 : ℝ) + v + 3 / 4)| ≤
      3 / 10 ^ 10 := by
    have e : (v - 3 / 4) / (2 * R + v + 3 / 4) - (v - 3 / 4) / (2 * (240792594 / 10 ^ 8 : ℝ) + v + 3 / 4) =
        (v - 3 / 4) * (2 * (240792594 / 10 ^ 8 : ℝ) - 2 * R) /
          ((2 * R + v + 3 / 4) * (2 * (240792594 / 10 ^ 8 : ℝ) + v + 3 / 4)) := by
      rw [div_sub_div _ _ hD.ne' hD'.ne']
      congr 1
      ring
    rw [e, abs_div, abs_of_pos (mul_pos hD hD'), div_le_iff₀ (mul_pos hD hD'), abs_mul]
    have h1 : |v - 3 / 4| ≤ 1 / 4 := by rw [abs_le]; constructor <;> linarith
    have h2 : |2 * (240792594 / 10 ^ 8 : ℝ) - 2 * R| ≤ 4 / 10 ^ 8 := by
      rw [abs_le]; constructor <;> linarith [hRe.1, hRe.2]
    have h3 : 36 / 10 ^ 10 * 10 ^ 10 / 10 ^ 10 ≤ 0 + 3 / 10 ^ 10 * 1 := by norm_num
    calc |v - 3 / 4| * |2 * (240792594 / 10 ^ 8 : ℝ) - 2 * R| ≤ 1 / 4 * (4 / 10 ^ 8) :=
          mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
      _ ≤ 3 / 10 ^ 10 * ((2 * R + v + 3 / 4) * (2 * (240792594 / 10 ^ 8 : ℝ) + v + 3 / 4)) := by
          nlinarith [hRe.1, mul_pos hD hD']
  have hE := lam_two_term (y := (v - 3 / 4) / (2 * R + v + 3 / 4)) (by linarith [hy])
  have hEm : 2 * |(v - 3 / 4) / (2 * R + v + 3 / 4)| ^ 3 / (3 * (1 - ((v - 3 / 4) / (2 * R + v + 3 / 4)) ^ 2)) ≤
      2 * (383 / 10000 : ℝ) ^ 3 / (3 * (1 - (383 / 10000 : ℝ) ^ 2)) := by
    have hy2 : ((v - 3 / 4) / (2 * R + v + 3 / 4)) ^ 2 ≤ (383 / 10000 : ℝ) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hy 2
    apply div_le_div₀ (by positivity) _ (by nlinarith) (by nlinarith)
    have := pow_le_pow_left₀ (abs_nonneg _) hy 3
    linarith
  have key := approx_generic (u := lhU) (U := 245774282 / 10 ^ 8)
    (y := (v - 3 / 4) / (2 * R + v + 3 / 4))
    (y' := (v - 3 / 4) / (2 * (240792594 / 10 ^ 8 : ℝ) + v + 3 / 4))
    (E := Real.log (1 + (v - 3 / 4) / (2 * R + v + 3 / 4)) - Real.log (1 - (v - 3 / 4) / (2 * R + v + 3 / 4)) -
      2 * ((v - 3 / 4) / (2 * R + v + 3 / 4)))
    (H := H0t) (H' := 110489073 / 10 ^ 8) (δH := 2 / 10 ^ 8) (δu := 2 / 10 ^ 8) (δy := 3 / 10 ^ 10)
    (ym := 383 / 10000) (Em := 2 * (383 / 10000 : ℝ) ^ 3 / (3 * (1 - (383 / 10000 : ℝ) ^ 2)))
    (um := 24578 / 10000) (Um := 24578 / 10000)
    (by rw [abs_le]; constructor <;> linarith [hHe.1, hHe.2])
    (by rw [abs_le]; constructor <;> linarith [hUe.1, hUe.2]) hy' hy (hE.trans hEm)
    (by rw [abs_of_pos lhU_pos]; linarith [hUe.2]) (by norm_num [abs_of_pos])
  have e := hfun_a0_eq hv
  rw [← hR] at e
  have e2 : hfun qS v (127 / 200) - hh0 v =
      (H0t - lhU * (2 * ((v - 3 / 4) / (2 * R + v + 3 / 4)) +
        (Real.log (1 + (v - 3 / 4) / (2 * R + v + 3 / 4)) - Real.log (1 - (v - 3 / 4) / (2 * R + v + 3 / 4)) -
      2 * ((v - 3 / 4) / (2 * R + v + 3 / 4)))))
      - (110489073 / 10 ^ 8 - 2 * (245774282 / 10 ^ 8) * ((v - 3 / 4) / (2 * (240792594 / 10 ^ 8 : ℝ) + v + 3 / 4))) := by
    rw [e]; unfold hh0; ring
  rw [e2]
  refine key.trans ?_
  norm_num


theorem hfun_half_eq {v : ℝ} (hv : 0 < v) :
    hfun qS v (1 / 2) =
      Hlt - lhU * (Real.log (1 + (v - 3 / 4) / (v + 11 / 4)) - Real.log (1 - (v - 3 / 4) / (v + 11 / 4))) := by
  have h1 : (v + 11 / 4 : ℝ) = 2 * 1 + v + 3 / 4 := by ring
  rw [h1, log_ratio_eq (by norm_num : (0 : ℝ) < 1) hv (by norm_num : (0 : ℝ) < 3 / 4)]
  have h0 : 0 < (1 / 2 : ℝ) ^ qS := Real.rpow_pos_of_pos (by norm_num) _
  have hc : (qS - 1) * Real.log 2 ≠ 0 := by
    have : 0 < qS - 1 := by unfold qS; norm_num
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    positivity
  have hZ : ∀ w : ℝ, lhZ qS w (1 / 2) = (1 / 2 : ℝ) ^ qS * (1 + w) := by
    intro w
    unfold lhZ
    have e1 : (1 - 1 / 2 : ℝ) = 1 / 2 := by norm_num
    rw [e1]; ring
  unfold Hlt hfun lhU
  rw [hZ, hZ, Real.log_mul h0.ne' (by linarith), Real.log_mul h0.ne' (by norm_num)]
  field_simp
  ring

theorem Hl_approx {v : ℝ} (hv1 : 13 / 25 ≤ v) (hv2 : v ≤ 1) :
    |hfun qS v (1 / 2) - hhl v| ≤ 6 / 10000 := by
  have hv : 0 < v := by linarith
  have hUe := lhU_enc
  have hHe := Hlt_enc
  have hD : 0 < v + 11 / 4 := by linarith
  have hy : |(v - 3 / 4) / (v + 11 / 4)| ≤ 704 / 10000 := by
    rw [abs_div, abs_of_pos hD, div_le_iff₀ hD, abs_le]
    constructor <;> nlinarith
  have hE := lam_two_term (y := (v - 3 / 4) / (v + 11 / 4)) (by linarith [hy])
  have hEm : 2 * |(v - 3 / 4) / (v + 11 / 4)| ^ 3 / (3 * (1 - ((v - 3 / 4) / (v + 11 / 4)) ^ 2)) ≤
      2 * (704 / 10000 : ℝ) ^ 3 / (3 * (1 - (704 / 10000 : ℝ) ^ 2)) := by
    have hy2 : ((v - 3 / 4) / (v + 11 / 4)) ^ 2 ≤ (704 / 10000 : ℝ) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hy 2
    apply div_le_div₀ (by positivity) _ (by nlinarith) (by nlinarith)
    have := pow_le_pow_left₀ (abs_nonneg _) hy 3
    linarith
  have key := approx_generic (u := lhU) (U := 245774282 / 10 ^ 8)
    (y := (v - 3 / 4) / (v + 11 / 4)) (y' := (v - 3 / 4) / (v + 11 / 4))
    (E := Real.log (1 + (v - 3 / 4) / (v + 11 / 4)) - Real.log (1 - (v - 3 / 4) / (v + 11 / 4)) -
      2 * ((v - 3 / 4) / (v + 11 / 4)))
    (H := Hlt) (H' := 132818582 / 10 ^ 8) (δH := 2 / 10 ^ 8) (δu := 2 / 10 ^ 8) (δy := 0)
    (ym := 704 / 10000) (Em := 2 * (704 / 10000 : ℝ) ^ 3 / (3 * (1 - (704 / 10000 : ℝ) ^ 2)))
    (um := 24578 / 10000) (Um := 24578 / 10000)
    (by rw [abs_le]; constructor <;> linarith [hHe.1, hHe.2])
    (by rw [abs_le]; constructor <;> linarith [hUe.1, hUe.2]) (by simp) hy (hE.trans hEm)
    (by rw [abs_of_pos lhU_pos]; linarith [hUe.2]) (by norm_num [abs_of_pos])
  have e := hfun_half_eq hv
  have e2 : hfun qS v (1 / 2) - hhl v =
      (Hlt - lhU * (2 * ((v - 3 / 4) / (v + 11 / 4)) +
        (Real.log (1 + (v - 3 / 4) / (v + 11 / 4)) - Real.log (1 - (v - 3 / 4) / (v + 11 / 4)) -
      2 * ((v - 3 / 4) / (v + 11 / 4)))))
      - (132818582 / 10 ^ 8 - 2 * (245774282 / 10 ^ 8) * ((v - 3 / 4) / (v + 11 / 4))) := by
    rw [e]; unfold hhl; ring
  rw [e2]
  refine key.trans ?_
  norm_num


theorem lhY_a0 {v : ℝ} (hv : 0 < v) : lhY qS v (127 / 200) = (lhR - v) / (lhR + v) := by
  have hR := lhR_pos
  have h0 : 0 < (73 / 200 : ℝ) ^ qS := Real.rpow_pos_of_pos (by norm_num) _
  have e : lhR = (127 / 200 : ℝ) ^ qS / (73 / 200 : ℝ) ^ qS := by
    unfold lhR
    rw [← Real.div_rpow (by norm_num) (by norm_num)]
    norm_num
  unfold lhY
  rw [lhZ_a0]
  have e1 : (1 - 127 / 200 : ℝ) = 73 / 200 := by norm_num
  rw [e1]
  have hu : (127 / 200 : ℝ) ^ qS = lhR * (73 / 200 : ℝ) ^ qS := by
    rw [e]; field_simp
  rw [hu]
  have : 0 < lhR + v := by linarith
  field_simp

theorem hd1_a0_eq {v : ℝ} (hv : 0 < v) :
    hd1 qS v (127 / 200) =
      lhU * (-2 * qS * ((lhR - v) / (lhR + v) - 27 / 100) / (9271 / 10000)) := by
  unfold hd1 lhm1 lhU
  rw [lhY_a0 hv]
  have : (2 * (127 / 200 : ℝ) - 1) = 27 / 100 := by norm_num
  rw [this]
  have hc : (qS - 1) * Real.log 2 ≠ 0 := by
    have : 0 < qS - 1 := by unfold qS; norm_num
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    positivity
  field_simp
  ring

theorem Ha_approx {v : ℝ} (hv1 : 13 / 25 ≤ v) (hv2 : v ≤ 1) :
    |hd1 qS v (127 / 200) - hha v| ≤ 1 / 10 ^ 6 := by
  have hv : 0 < v := by linarith
  have hRe := lhR_enc
  have hUe := lhU_enc
  have hD : 0 < lhR + v := by linarith [hRe.1]
  have hD' : 0 < 240792594 / 10 ^ 8 + v := by linarith
  rw [hd1_a0_eq hv]
  unfold hha
  -- G(R) and G(ρ)
  set gR := (lhR - v) / (lhR + v) with hgR
  set gρ := (240792594 / 10 ^ 8 - v) / (240792594 / 10 ^ 8 + v) with hgρ
  have hg : |gR - gρ| ≤ 1 / 10 ^ 8 := by
    have e : gR - gρ = 2 * v * (lhR - 240792594 / 10 ^ 8) / ((lhR + v) * (240792594 / 10 ^ 8 + v)) := by
      rw [hgR, hgρ, div_sub_div _ _ hD.ne' hD'.ne']
      congr 1
      ring
    rw [e, abs_div, abs_of_pos (mul_pos hD hD'), div_le_iff₀ (mul_pos hD hD'), abs_mul]
    have h2 : |lhR - 240792594 / 10 ^ 8| ≤ 2 / 10 ^ 8 := by
      rw [abs_le]; constructor <;> linarith [hRe.1, hRe.2]
    have h1 : |2 * v| ≤ 2 := by rw [abs_le]; constructor <;> linarith
    calc |2 * v| * |lhR - 240792594 / 10 ^ 8| ≤ 2 * (2 / 10 ^ 8) := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
      _ ≤ 1 / 10 ^ 8 * ((lhR + v) * (240792594 / 10 ^ 8 + v)) := by
          nlinarith [hRe.1, mul_pos hD hD']
  have hgρ0 : 0 ≤ gρ := div_nonneg (by linarith) hD'.le
  have hgρ1 : gρ ≤ 13 / 20 := by
    rw [hgρ, div_le_iff₀ hD']; linarith
  have hgb : |gρ - 27 / 100| ≤ 2 / 5 := by
    rw [abs_le]; constructor <;> linarith
  have hgb2 : |gR - 27 / 100| ≤ 2 / 5 + 1 / 10 ^ 8 := by
    have : gR - 27 / 100 = (gR - gρ) + (gρ - 27 / 100) := by ring
    rw [this]
    have := (abs_add_le _ _).trans (add_le_add hg hgb)
    linarith
  have hu1 : |lhU - 245774282 / 10 ^ 8| ≤ 2 / 10 ^ 8 := by
    rw [abs_le]; constructor <;> linarith [hUe.1, hUe.2]
  have t1 : |(lhU - 245774282 / 10 ^ 8) * (gR - 27 / 100)| ≤ 2 / 10 ^ 8 * (2 / 5 + 1 / 10 ^ 8) := by
    rw [abs_mul]; exact mul_le_mul hu1 hgb2 (abs_nonneg _) (by norm_num)
  have t2 : |(245774282 / 10 ^ 8 : ℝ) * (gR - gρ)| ≤ 24578 / 10000 * (1 / 10 ^ 8) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 245774282 / 10 ^ 8)]
    exact mul_le_mul (by norm_num) hg (abs_nonneg _) (by norm_num)
  have e : lhU * (-2 * qS * (gR - 27 / 100) / (9271 / 10000)) -
      -2 * (1587 / 1000) * (245774282 / 10 ^ 8) * (gρ - 27 / 100) / (9271 / 10000) =
      (-2 * (1587 / 1000) / (9271 / 10000)) *
        ((lhU - 245774282 / 10 ^ 8) * (gR - 27 / 100) + 245774282 / 10 ^ 8 * (gR - gρ)) := by
    unfold qS; ring
  rw [e, abs_mul, abs_of_neg (by norm_num : (-2 * (1587 / 1000) / (9271 / 10000) : ℝ) < 0)]
  have := (abs_add_le _ _).trans (add_le_add t1 t2)
  calc (-(-2 * (1587 / 1000) / (9271 / 10000) : ℝ)) *
        |(lhU - 245774282 / 10 ^ 8) * (gR - 27 / 100) + 245774282 / 10 ^ 8 * (gR - gρ)|
      ≤ (-(-2 * (1587 / 1000) / (9271 / 10000) : ℝ)) * (2 / 10 ^ 8 * (2 / 5 + 1 / 10 ^ 8) + 24578 / 10000 * (1 / 10 ^ 8)) :=
        mul_le_mul_of_nonneg_left this (by norm_num)
    _ ≤ 1 / 10 ^ 6 := by norm_num

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.H0_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms H0_approx

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.Hl_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hl_approx

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.Ha_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ha_approx

end FormalResearch.FourQubitEntropy.RenyiFull
