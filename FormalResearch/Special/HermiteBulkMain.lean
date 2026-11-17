module

public import Mathlib
public import FormalResearch.Special.HermiteBulkPR
public import FormalResearch.Special.HermiteNorm

/-!
# Plancherel-Rotach asymptotics of the Hermite functions in the bulk (W1 `lem:PR`(a))

`hermite_bulk_PR`: for `0 < ε ≤ 1` there is `C` such that for all `n`, all `|x| ≤ (1-ε)√(2n+1)`,
`φ_n(x) = √(2/π) (2n+1)^{-1/4} (sin t)^{-1/2} [cos Φ + R]`, `|R| ≤ C/(n+1)`, with
`t = arccos(x/√(2n+1))`, `Φ = (2n+1)/4 (2t - sin 2t) - π/4` (`hpr_angle`, `hpr_phase`).  This is the
paper statement with the explicit rate `O(1/(n+1))`, uniform in the bulk.

Route (no Airy matching): Liouville-Green variables of the Weber equation (`HermiteBulkProfile`),
rotation comparison from `x = 0` (`HermiteBulkRot`), initial data from parity, the sign alternation of
`φ_{2m}(0)` and the Wallis product bounds (`HermiteBulkOrigin`), the phase identity
`S = nπ/2 - Φ` (`HermiteBulkPR`), small `n` by the crude sup bound `hermitePhi_sq_le`, negative `x` by
parity.  Numerical check (mpmath, 30 digits, `φ_n` by the three-term recurrence; scratch, not
committed): `(n+1)|φ_n(x)/A - cos Φ| ≤ 1.21` for `n ≤ 59` and `n = 100, 201, 400, 1000`, `|x/√(2n+1)|
≤ 0.95` on a grid of 39 points.  The constant `C` is existential (`C ≈ (10/ε⁵ + O(1)) · 2`, not
sharp).  Not formalised: the transition and forbidden regions, the derivative asymptotics, the
dependence of `C` on `ε` beyond the explicit `ε⁻⁵` growth.
-/

@[expose] public section

open Real

namespace FormalResearch.Special

lemma hbk_c_le_two {c : ℝ} (hc0 : 0 ≤ c) (n : ℕ) (h : |c ^ 2 - 2 / π| ≤ 1 / ((n : ℝ) + 1)) :
    c ≤ 2 := by
  have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have h2 : 2 / π ≤ 1 := by rw [div_le_one Real.pi_pos]; linarith [Real.pi_gt_three]
  have := (abs_le.1 h).2
  nlinarith

lemma hbk_sqrt_two_pi_ge : (1 / 2 : ℝ) ≤ √(2 / π) := by
  apply Real.le_sqrt_of_sq_le
  rw [le_div_iff₀ Real.pi_pos]; nlinarith [Real.pi_lt_four]

lemma hbk_c_close {c : ℝ} (hc0 : 0 ≤ c) (n : ℕ) (h : |c ^ 2 - 2 / π| ≤ 1 / ((n : ℝ) + 1)) :
    |c - √(2 / π)| ≤ 2 / ((n : ℝ) + 1) := by
  have hs := hbk_sqrt_two_pi_ge
  have hsq : √(2 / π) ^ 2 = 2 / π := Real.sq_sqrt (by positivity)
  have e : c ^ 2 - 2 / π = (c - √(2 / π)) * (c + √(2 / π)) := by
    generalize √(2 / π) = r at hsq ⊢; rw [← hsq]; ring
  rw [e, abs_mul, abs_of_nonneg (by linarith : 0 ≤ c + √(2 / π))] at h
  have h1 : |c - √(2 / π)| * (1 / 2) ≤ 1 / ((n : ℝ) + 1) :=
    le_trans (mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)) h
  have : 2 / ((n : ℝ) + 1) = 2 * (1 / ((n : ℝ) + 1)) := by ring
  rw [this]; linarith

/-- **Bulk Plancherel-Rotach, `U`-form, `x ≥ 0`.**  For `0 < ε ≤ 1` there is `C` such that for all `n`
and `0 ≤ b ≤ (1-ε)√(2n+1)`: `|E φ_n(b) - √(2/π) cos Φ_n(b)| ≤ C/(n+1)`, `E = (2n+1-b²)^{1/4}`. -/
theorem hbk_bulk_U (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (b : ℝ), 0 ≤ b → b ≤ (1 - ε) * √(2 * (n : ℝ) + 1) →
      |hbk_U (2 * (n : ℝ) + 1) (hermitePhi n) b - √(2 / π) * cos (hpr_phase b n)| ≤
        C / ((n : ℝ) + 1) := by
  have he5 : 0 < ε ^ 5 := by positivity
  set L0 : ℝ := 5 / (4 * ε ^ 5) with hL0
  have hL0p : 0 < L0 := by positivity
  refine ⟨10 / ε ^ 5 + 2 + L0 * ((1 + L0) * (1 + 2 * L0) + 1), by positivity, ?_⟩
  intro n b hb0 hbε
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hL : 0 < 2 * (n : ℝ) + 1 := by positivity
  have hLn : (n : ℝ) + 1 ≤ 2 * (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  by_cases hμ : 5 / (4 * ε ^ 5 * (2 * (n : ℝ) + 1)) ≤ 1
  · obtain ⟨c, hc0, hcn, hmar⟩ := hbk_march ε hε0 hε1 n b hb0 hbε
    have hc2 := hbk_c_le_two hc0 n hcn
    have hcl := hbk_c_close hc0 n hcn
    set μ := 5 / (4 * ε ^ 5 * (2 * (n : ℝ) + 1)) with hμdef
    have hμ0 : 0 ≤ μ := by positivity
    have hex : exp (μ / 2) ≤ 2 := by
      have h1 : exp (μ / 2) ≤ exp (1 / 2) := exp_le_exp.2 (by linarith)
      have h2 : exp (1 / 2 : ℝ) ^ 2 = exp 1 := by rw [← exp_nat_mul]; norm_num
      have h3 := Real.exp_one_lt_d9
      have h4 : 0 < exp (1 / 2 : ℝ) := exp_pos _
      nlinarith
    have hμn : μ ≤ 5 / (4 * ε ^ 5 * ((n : ℝ) + 1)) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
    have hA : |hbk_U (2 * (n : ℝ) + 1) (hermitePhi n) b - c * cos (hpr_phase b n)| ≤ 8 * μ := by
      refine hmar.trans ?_
      have : 2 * μ * exp (μ / 2) * c ≤ 2 * μ * 2 * 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hex (by positivity)) hc2 hc0 (by positivity)
      linarith
    have hB : |c * cos (hpr_phase b n) - √(2 / π) * cos (hpr_phase b n)| ≤ 2 / ((n : ℝ) + 1) := by
      rw [← sub_mul, abs_mul]
      calc |c - √(2 / π)| * |cos (hpr_phase b n)| ≤ |c - √(2 / π)| * 1 :=
            mul_le_mul_of_nonneg_left (abs_cos_le_one _) (abs_nonneg _)
        _ ≤ _ := by rw [mul_one]; exact hcl
    have htri := abs_sub_le (hbk_U (2 * (n : ℝ) + 1) (hermitePhi n) b)
      (c * cos (hpr_phase b n)) (√(2 / π) * cos (hpr_phase b n))
    have h8 : 8 * μ ≤ 10 / ε ^ 5 / ((n : ℝ) + 1) := by
      have : 8 * μ ≤ 8 * (5 / (4 * ε ^ 5 * ((n : ℝ) + 1))) := by linarith
      refine this.trans (le_of_eq ?_); field_simp; ring
    have hpos : 0 ≤ L0 * ((1 + L0) * (1 + 2 * L0) + 1) / ((n : ℝ) + 1) := by positivity
    have : (10 / ε ^ 5 + 2 + L0 * ((1 + L0) * (1 + 2 * L0) + 1)) / ((n : ℝ) + 1) =
        10 / ε ^ 5 / ((n : ℝ) + 1) + 2 / ((n : ℝ) + 1) +
          L0 * ((1 + L0) * (1 + 2 * L0) + 1) / ((n : ℝ) + 1) := by ring
    rw [this]; linarith
  · -- small `n`: crude sup bound
    have hlt : 2 * (n : ℝ) + 1 < L0 := by
      rw [not_le, lt_div_iff₀ (by positivity)] at hμ
      rw [hL0, lt_div_iff₀ (by positivity)]; linarith
    have hnL : (n : ℝ) + 1 < L0 := by linarith
    set E := hbk_E (2 * (n : ℝ) + 1) b with hE
    have hb2 : b ^ 2 < 2 * (n : ℝ) + 1 := by
      have : b < √(2 * (n : ℝ) + 1) := lt_of_le_of_lt hbε (by
        have := Real.sqrt_pos.2 hL; nlinarith)
      nlinarith [Real.sq_sqrt hL.le]
    have hEp : 0 < E := hbk_E_pos hb2
    have hE4 : E ^ 4 = 2 * (n : ℝ) + 1 - b ^ 2 := hbk_E_four hb2
    have hE1 : E ≤ 1 + L0 := by
      have : E ≤ 1 + E ^ 4 := by
        rcases le_total E 1 with h | h
        · nlinarith [pow_nonneg hEp.le 4]
        · nlinarith [pow_le_pow_right₀ h (by norm_num : 1 ≤ 4)]
      nlinarith [sq_nonneg b]
    have hφ := abs_hermitePhi_le n b
    have hsq : √(2 * (n : ℝ) + 2) ≤ 1 + 2 * L0 := by
      have : √(2 * (n : ℝ) + 2) ≤ 2 * (n : ℝ) + 2 := by
        apply Real.sqrt_le_iff.2; constructor
        · positivity
        · nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      linarith
    have hU : |hbk_U (2 * (n : ℝ) + 1) (hermitePhi n) b| ≤ (1 + L0) * (1 + 2 * L0) := by
      have : hbk_U (2 * (n : ℝ) + 1) (hermitePhi n) b = E * hermitePhi n b := rfl
      rw [this, abs_mul, abs_of_pos hEp]
      exact mul_le_mul hE1 (hφ.trans hsq) (abs_nonneg _) (by positivity)
    have hc : |√(2 / π) * cos (hpr_phase b n)| ≤ 1 := by
      rw [abs_mul]
      have : √(2 / π) ≤ 1 := by
        rw [Real.sqrt_le_one]; rw [div_le_one Real.pi_pos]; linarith [Real.pi_gt_three]
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      calc √(2 / π) * |cos (hpr_phase b n)| ≤ 1 * 1 :=
            mul_le_mul this (abs_cos_le_one _) (abs_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    have h1 := abs_sub (hbk_U (2 * (n : ℝ) + 1) (hermitePhi n) b) (√(2 / π) * cos (hpr_phase b n))
    have h2 : |hbk_U (2 * (n : ℝ) + 1) (hermitePhi n) b - √(2 / π) * cos (hpr_phase b n)| ≤
        (1 + L0) * (1 + 2 * L0) + 1 := by linarith
    rw [le_div_iff₀ hn1]
    have h3 : L0 * ((1 + L0) * (1 + 2 * L0) + 1) ≥ ((n : ℝ) + 1) * ((1 + L0) * (1 + 2 * L0) + 1) :=
      mul_le_mul_of_nonneg_right hnL.le (by positivity)
    have h4 := mul_le_mul_of_nonneg_right h2 hn1.le
    have h5 : 0 ≤ 10 / ε ^ 5 + 2 := by positivity
    nlinarith [mul_nonneg h5 hn1.le]

lemma hbk_angle_neg (n : ℕ) (x : ℝ) : hpr_angle (-x) n = π - hpr_angle x n := by
  unfold hpr_angle; rw [neg_div, Real.arccos_neg]

lemma hbk_phase_neg (n : ℕ) (x : ℝ) : hpr_phase (-x) n + hpr_phase x n = n * π := by
  unfold hpr_phase; rw [hbk_angle_neg]
  have h1 : sin (2 * (π - hpr_angle x n)) = -sin (2 * hpr_angle x n) := by
    rw [mul_sub, sin_two_pi_sub]
  rw [h1]; ring

lemma hbk_sin_angle_neg (n : ℕ) (x : ℝ) : sin (hpr_angle (-x) n) = sin (hpr_angle x n) := by
  rw [hbk_angle_neg, sin_pi_sub]

/-- `E = (2n+1)^{1/4} (sin t)^{1/2}` with `t = arccos(b/√(2n+1))`. -/
lemma hbk_E_eq (n : ℕ) (b : ℝ) (hb : b ^ 2 < 2 * (n : ℝ) + 1) :
    hbk_E (2 * (n : ℝ) + 1) b =
      (2 * (n : ℝ) + 1) ^ (1 / 4 : ℝ) * sin (hpr_angle b n) ^ (1 / 2 : ℝ) := by
  have hL : 0 < 2 * (n : ℝ) + 1 := by positivity
  generalize hLdef : 2 * (n : ℝ) + 1 = L at *
  have hsL : 0 < √L := Real.sqrt_pos.2 hL
  have hsL2 : √L ^ 2 = L := Real.sq_sqrt hL.le
  have hlt : |b / √L| < 1 := by
    rw [abs_div, abs_of_pos hsL, div_lt_one hsL]
    exact abs_lt_of_sq_lt_sq (by rw [hsL2]; exact hb) hsL.le
  have hsin : sin (hpr_angle b n) = √(1 - (b / √L) ^ 2) := by
    unfold hpr_angle; rw [hLdef, Real.sin_arccos]
  have hw : hbk_w L b = √L * sin (hpr_angle b n) := by
    rw [hsin, hbk_w, ← Real.sqrt_mul hL.le]
    congr 1
    field_simp
    rw [hsL2]; ring
  have hs0 : 0 ≤ sin (hpr_angle b n) := by rw [hsin]; exact Real.sqrt_nonneg _
  rw [hbk_E, hw, Real.sqrt_mul hsL.le, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    ← Real.rpow_mul hL.le]
  norm_num

/-- `sin t > 0` in the bulk. -/
lemma hbk_sin_pos (n : ℕ) (b : ℝ) (hb : b ^ 2 < 2 * (n : ℝ) + 1) : 0 < sin (hpr_angle b n) := by
  have hL : 0 < 2 * (n : ℝ) + 1 := by positivity
  have hsL : 0 < √(2 * (n : ℝ) + 1) := Real.sqrt_pos.2 hL
  have hsL2 : √(2 * (n : ℝ) + 1) ^ 2 = 2 * (n : ℝ) + 1 := Real.sq_sqrt hL.le
  have hlt : |b / √(2 * (n : ℝ) + 1)| < 1 := by
    rw [abs_div, abs_of_pos hsL, div_lt_one hsL]
    exact abs_lt_of_sq_lt_sq (by rw [hsL2]; exact hb) hsL.le
  have hab := abs_lt.1 hlt
  unfold hpr_angle
  rw [Real.sin_arccos]
  exact Real.sqrt_pos.2 (by nlinarith [hab.1, hab.2])

/-- **Plancherel-Rotach asymptotics of the Hermite functions in the bulk**
(W1 `lem:PR`(a), `hermite.tex`).  For `0 < ε ≤ 1` there is `C` such that for all `n` and real `x`
with `|x| ≤ (1-ε)√(2n+1)`, writing `t = arccos(x/√(2n+1))`, `Φ = (2n+1)/4 (2t - sin 2t) - π/4`
and `A = √(2/π) (2n+1)^{-1/4} (sin t)^{-1/2}`, `φ_n(x) = A (cos Φ + R)` with `|R| ≤ C/(n+1)`. -/
theorem hermite_bulk_PR (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (x : ℝ), |x| ≤ (1 - ε) * √(2 * (n : ℝ) + 1) →
      ∃ R : ℝ, |R| ≤ C / ((n : ℝ) + 1) ∧
        hermitePhi n x = √(2 / π) * (2 * (n : ℝ) + 1) ^ (-(1 / 4 : ℝ)) *
          sin (hpr_angle x n) ^ (-(1 / 2 : ℝ)) * (cos (hpr_phase x n) + R) := by
  obtain ⟨C, hC, hmain⟩ := hbk_bulk_U ε hε0 hε1
  refine ⟨2 * C, by positivity, ?_⟩
  -- the case `x ≥ 0`, in the `A`-form
  have hpos : ∀ (n : ℕ) (b : ℝ), 0 ≤ b → b ≤ (1 - ε) * √(2 * (n : ℝ) + 1) →
      |hermitePhi n b / (√(2 / π) * (2 * (n : ℝ) + 1) ^ (-(1 / 4 : ℝ)) *
          sin (hpr_angle b n) ^ (-(1 / 2 : ℝ))) - cos (hpr_phase b n)| ≤ 2 * C / ((n : ℝ) + 1) := by
    intro n b hb0 hbε
    have hL : 0 < 2 * (n : ℝ) + 1 := by positivity
    have hsL : 0 < √(2 * (n : ℝ) + 1) := Real.sqrt_pos.2 hL
    have hb2 : b ^ 2 < 2 * (n : ℝ) + 1 := by
      have : b < √(2 * (n : ℝ) + 1) := lt_of_le_of_lt hbε (by nlinarith)
      nlinarith [Real.sq_sqrt hL.le]
    have hsin := hbk_sin_pos n b hb2
    have hEe := hbk_E_eq n b hb2
    have hEp := hbk_E_pos hb2
    have hA : (2 * (n : ℝ) + 1) ^ (-(1 / 4 : ℝ)) * sin (hpr_angle b n) ^ (-(1 / 2 : ℝ)) =
        (hbk_E (2 * (n : ℝ) + 1) b)⁻¹ := by
      rw [hEe, mul_inv, Real.rpow_neg hL.le, Real.rpow_neg hsin.le]
    have hs := hbk_sqrt_two_pi_ge
    have h := hmain n b hb0 hbε
    have e : hermitePhi n b / (√(2 / π) * (2 * (n : ℝ) + 1) ^ (-(1 / 4 : ℝ)) *
          sin (hpr_angle b n) ^ (-(1 / 2 : ℝ))) - cos (hpr_phase b n) =
        (hbk_U (2 * (n : ℝ) + 1) (hermitePhi n) b - √(2 / π) * cos (hpr_phase b n)) /
          √(2 / π) := by
      rw [mul_assoc, hA]
      have : hbk_U (2 * (n : ℝ) + 1) (hermitePhi n) b =
          hbk_E (2 * (n : ℝ) + 1) b * hermitePhi n b := rfl
      rw [this]
      field_simp
    rw [e, abs_div, abs_of_pos (by linarith : 0 < √(2 / π)), div_le_iff₀ (by linarith)]
    have h0 : 0 ≤ C / ((n : ℝ) + 1) := by positivity
    have e2 : 2 * C / ((n : ℝ) + 1) = 2 * (C / ((n : ℝ) + 1)) := by ring
    rw [e2]
    nlinarith [mul_le_mul_of_nonneg_left hs h0]
  intro n x hx
  have hL : 0 < 2 * (n : ℝ) + 1 := by positivity
  set A := √(2 / π) * (2 * (n : ℝ) + 1) ^ (-(1 / 4 : ℝ)) *
    sin (hpr_angle x n) ^ (-(1 / 2 : ℝ)) with hAdef
  refine ⟨hermitePhi n x / A - cos (hpr_phase x n), ?_, ?_⟩
  · rcases le_total 0 x with h0 | h0
    · rw [abs_of_nonneg h0] at hx; exact hpos n x h0 hx
    · rw [abs_of_nonpos h0] at hx
      have h := hpos n (-x) (by linarith) hx
      have hA : √(2 / π) * (2 * (n : ℝ) + 1) ^ (-(1 / 4 : ℝ)) *
          sin (hpr_angle (-x) n) ^ (-(1 / 2 : ℝ)) = A := by rw [hAdef, hbk_sin_angle_neg]
      rw [hA] at h
      have hph : cos (hpr_phase (-x) n) = (-1) ^ n * cos (hpr_phase x n) := by
        have : hpr_phase (-x) n = n * π - hpr_phase x n := by linarith [hbk_phase_neg n x]
        rw [this, cos_sub, cos_nat_mul_pi, sin_nat_mul_pi]; ring
      have hpar := hermitePhi_neg n x
      rw [hpar, hph] at h
      have : (-1 : ℝ) ^ n * hermitePhi n x / A - (-1) ^ n * cos (hpr_phase x n) =
          (-1) ^ n * (hermitePhi n x / A - cos (hpr_phase x n)) := by ring
      rw [this, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] at h
      exact h
  · have hsinx : 0 < sin (hpr_angle x n) := by
      have hb2 : x ^ 2 < 2 * (n : ℝ) + 1 := by
        have hsL : 0 < √(2 * (n : ℝ) + 1) := Real.sqrt_pos.2 hL
        have : |x| < √(2 * (n : ℝ) + 1) := lt_of_le_of_lt hx (by nlinarith)
        have := sq_lt_sq' (by linarith [abs_nonneg x]) this
        rw [sq_abs, Real.sq_sqrt hL.le] at this
        linarith [this]
      exact hbk_sin_pos n x hb2
    have hApos : 0 < A := by
      rw [hAdef]
      have : (0 : ℝ) < √(2 / π) := Real.sqrt_pos.2 (by positivity)
      positivity
    field_simp
    ring

end FormalResearch.Special

/-- info: 'FormalResearch.Special.hbk_bulk_U' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hbk_bulk_U

/-- info: 'FormalResearch.Special.hermite_bulk_PR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hermite_bulk_PR
