import FormalResearch.FourQubitEntropy.RenyiFullNUCells
import FormalResearch.FourQubitEntropy.RenyiFullTaylor
import FormalResearch.FourQubitEntropy.RenyiFullHZ
import FormalResearch.FourQubitEntropy.ThirdMoment

/-!
# `lem:fqe-near-uniform-dual` (NU): proved

Paper E, `lem:fqe-near-uniform-moment` and `lem:fqe-near-uniform-dual` (`sup_renyi.tex`).
`NearUniformDual` (`RenyiFullProps.lean`) is proved here, without hypothesis, in the following steps
(`q = q_s = 1587/1000`, `r = q - 1`, `w_i = λ_i - 1/4`, `x = Σ w_i² = p - 1/4`, `y = Σ w_i³`, `v = y/x`):

1. `nu_taylor_sum`: Taylor's formula through degree five (`taylor_rpow`, the sixth derivative of `z^q`
   is positive) gives `4^{q-1} Σ λ_i^q ≥ 1 + A x + B y + C Σ w_i⁴ + T x y` (Newton: `Σ w_i⁵ = 5xy/6`);
2. `sum_w4_ge`: `x Σ w_i⁴ ≥ x³/4 + y²` (the elementary square identity), hence
   `N := 4^{q-1} Σ λ_i^q ≥ 1 + xV + x²W`, `V = A + Bv + Cv²`, `W = C/4 + Tv`;
3. the third-moment lemma gives `|v| ≤ 3/25` when `x ≤ 1/25`;
4. `ln N ≥ ln(1+z) ≥ z - z²/2 + z³/3 - z⁴/4` (`log_ge_taylor4`, `z = xV + x²W`) and the Bernstein
   certificate `nuG_nonneg` (`RenyiFullNUCells.lean`) give `2 - H_q ≥ (c+d)x - b y - γx²`;
5. `Λ_θ(c₂) - Λ_θ(λ) = 2 - H_q - c x + b y + γ x²` finishes (`d = 1/125`).
-/

namespace FormalResearch.FourQubitEntropy.RenyiFull

open FormalResearch.FourQubitEntropy Finset

theorem qS_lt_two : qS < 2 := by unfold qS; norm_num

/-- Power sums of the centred vector. -/
theorem w_sums {l : Fin 4 → ℝ} (hs : ∑ i, l i = 1) :
    ∑ i, (l i - 1 / 4) ^ 2 = pur l - 1 / 4 ∧
    ∑ i, (l i - 1 / 4) ^ 3 = cub l - 1 / 16 - 3 / 4 * (pur l - 1 / 4) := by
  simp only [Fin.sum_univ_four] at hs
  unfold pur cub
  simp only [Fin.sum_univ_four]
  constructor <;> (have hd : l 3 = 1 - l 0 - l 1 - l 2 := by linarith) <;> rw [hd] <;> ring

set_option maxHeartbeats 2000000 in
/-- `x S₄ ≥ x³/4 + y²` for a centred vector. -/
theorem sum_w4_ge {w0 w1 w2 w3 : ℝ} (hs : w0 + w1 + w2 + w3 = 0) :
    (w0 ^ 2 + w1 ^ 2 + w2 ^ 2 + w3 ^ 2) * (w0 ^ 4 + w1 ^ 4 + w2 ^ 4 + w3 ^ 4) ≥
      (w0 ^ 2 + w1 ^ 2 + w2 ^ 2 + w3 ^ 2) ^ 3 / 4 + (w0 ^ 3 + w1 ^ 3 + w2 ^ 3 + w3 ^ 3) ^ 2 := by
  obtain ⟨x, hx⟩ : ∃ x, x = w0 ^ 2 + w1 ^ 2 + w2 ^ 2 + w3 ^ 2 := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = w0 ^ 3 + w1 ^ 3 + w2 ^ 3 + w3 ^ 3 := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S, S = w0 ^ 4 + w1 ^ 4 + w2 ^ 4 + w3 ^ 4 := ⟨_, rfl⟩
  rw [← hx, ← hy, ← hS]
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hsq : 0 ≤ (x * w0 ^ 2 - x ^ 2 / 4 - y * w0) ^ 2 + (x * w1 ^ 2 - x ^ 2 / 4 - y * w1) ^ 2 +
      (x * w2 ^ 2 - x ^ 2 / 4 - y * w2) ^ 2 + (x * w3 ^ 2 - x ^ 2 / 4 - y * w3) ^ 2 := by positivity
  have hexp : (x * w0 ^ 2 - x ^ 2 / 4 - y * w0) ^ 2 + (x * w1 ^ 2 - x ^ 2 / 4 - y * w1) ^ 2 +
      (x * w2 ^ 2 - x ^ 2 / 4 - y * w2) ^ 2 + (x * w3 ^ 2 - x ^ 2 / 4 - y * w3) ^ 2 =
      x * (x * S - (x ^ 3 / 4 + y ^ 2)) := by
    have hw3 : w3 = -w0 - w1 - w2 := by linarith
    subst hx hy hS
    rw [hw3]; ring
  rw [hexp] at hsq
  rcases hx0.eq_or_lt with h | h
  · have h0 : w0 = 0 := by nlinarith [sq_nonneg w0, sq_nonneg w1, sq_nonneg w2, sq_nonneg w3]
    have h1 : w1 = 0 := by nlinarith [sq_nonneg w0, sq_nonneg w1, sq_nonneg w2, sq_nonneg w3]
    have h2 : w2 = 0 := by nlinarith [sq_nonneg w0, sq_nonneg w1, sq_nonneg w2, sq_nonneg w3]
    have h3 : w3 = 0 := by nlinarith [sq_nonneg w0, sq_nonneg w1, sq_nonneg w2, sq_nonneg w3]
    rw [hy, hS, h0, h1, h2, h3, ← h]; norm_num
  · have := nonneg_of_mul_nonneg_right hsq h
    linarith

/-- The order-`q` coefficients `A, B, C, T` of `lem:fqe-near-uniform-moment`, `r = q - 1`. -/
noncomputable def nuA (q : ℝ) : ℝ := 2 * q * (q - 1)
noncomputable def nuB (q : ℝ) : ℝ := 8 / 3 * q * (q - 1) * (q - 2)
noncomputable def nuC (q : ℝ) : ℝ := 8 / 3 * q * (q - 1) * (q - 2) * (q - 3)
noncomputable def nuT (q : ℝ) : ℝ := 2 / 3 * (q - 4) * nuC q

/-- **Taylor step of `lem:fqe-near-uniform-moment`**:
`4^{q-1} Σ λ_i^q ≥ 1 + A x + B y + C Σ w_i⁴ + T x y` for a probability vector, `w_i = λ_i - 1/4`. -/
theorem nu_taylor_sum {l : Fin 4 → ℝ} (hl : IsProb4 l) :
    1 + nuA qS * (∑ i, (l i - 1 / 4) ^ 2) + nuB qS * (∑ i, (l i - 1 / 4) ^ 3) +
      nuC qS * (∑ i, (l i - 1 / 4) ^ 4) +
      nuT qS * (∑ i, (l i - 1 / 4) ^ 2) * (∑ i, (l i - 1 / 4) ^ 3) ≤
    (4 : ℝ) ^ (qS - 1) * ∑ i, l i ^ qS := by
  have hq1 := qS_gt_one
  have hq2 := qS_lt_two
  have hu : ∀ i, -1 ≤ 4 * l i - 1 := fun i => by have := hl.1 i; linarith
  have tay : ∀ i, ∑ k ∈ range 6, cf qS k * (4 * l i - 1) ^ k ≤ 4 ^ qS * l i ^ qS := by
    intro i
    have h := taylor_rpow hq1 hq2 (hu i)
    rw [show 1 + (4 * l i - 1) = 4 * l i by ring, Real.mul_rpow (by norm_num) (hl.1 i)] at h
    exact h
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) => tay i)
  rw [← Finset.mul_sum] at hsum
  have e4 : (4 : ℝ) ^ (qS - 1) = 4 ^ qS / 4 := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_one]
  have hs := hl.2
  simp only [Fin.sum_univ_four] at hs hsum ⊢
  have hd : l 3 = 1 - l 0 - l 1 - l 2 := by linarith
  have id : ∑ k ∈ range 6, cf qS k * (4 * l 0 - 1) ^ k + ∑ k ∈ range 6, cf qS k * (4 * l 1 - 1) ^ k +
      ∑ k ∈ range 6, cf qS k * (4 * l 2 - 1) ^ k + ∑ k ∈ range 6, cf qS k * (4 * l 3 - 1) ^ k =
      4 * (1 + nuA qS * ((l 0 - 1 / 4) ^ 2 + (l 1 - 1 / 4) ^ 2 + (l 2 - 1 / 4) ^ 2 + (l 3 - 1 / 4) ^ 2) +
        nuB qS * ((l 0 - 1 / 4) ^ 3 + (l 1 - 1 / 4) ^ 3 + (l 2 - 1 / 4) ^ 3 + (l 3 - 1 / 4) ^ 3) +
        nuC qS * ((l 0 - 1 / 4) ^ 4 + (l 1 - 1 / 4) ^ 4 + (l 2 - 1 / 4) ^ 4 + (l 3 - 1 / 4) ^ 4) +
        nuT qS * ((l 0 - 1 / 4) ^ 2 + (l 1 - 1 / 4) ^ 2 + (l 2 - 1 / 4) ^ 2 + (l 3 - 1 / 4) ^ 2) *
          ((l 0 - 1 / 4) ^ 3 + (l 1 - 1 / 4) ^ 3 + (l 2 - 1 / 4) ^ 3 + (l 3 - 1 / 4) ^ 3)) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, cf, ff, Nat.factorial, nuA, nuB, nuC, nuT]
    push_cast
    rw [hd]
    ring
  rw [e4]
  have h4 : 0 < (4 : ℝ) ^ qS := by positivity
  nlinarith [id, hsum, h4]

/-- `|y| ≤ (3/25) x` for `0 ≤ x ≤ 1/25` (third-moment lemma: `|y| ≤ x^{3/2}/√3`, `√x ≤ 1/5`). -/
theorem rpow_three_halves_eq_nu {x : ℝ} (hx : 0 ≤ x) : x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
  rcases hx.eq_or_lt with h | h
  · subst h; simp
  · rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add h, Real.rpow_one, ← Real.sqrt_eq_rpow]

theorem y_le {l : Fin 4 → ℝ} (hl : IsProb4 l) (hx1 : pur l - 1 / 4 ≤ 1 / 25) :
    |cub l - 1 / 16 - 3 / 4 * (pur l - 1 / 4)| ≤ 3 / 25 * (pur l - 1 / 4) := by
  have hx0 : 0 ≤ pur l - 1 / 4 := by have := pur_ge_quarter hl; linarith
  obtain ⟨-, h3, -, -⟩ := third_moment l hl.1 hl.2 (x := pur l - 1 / 4) (by unfold pur; ring)
  have e : cub l = ∑ i, l i ^ 3 := rfl
  rw [e, show (3 : ℝ) / 4 * (pur l - 1 / 4) = 3 * (pur l - 1 / 4) / 4 by ring]
  refine h3.trans ?_
  set x := pur l - 1 / 4 with hx
  rw [rpow_three_halves_eq_nu hx0]
  have hs3 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hs33 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have h53 : 5 / 3 ≤ Real.sqrt 3 := by
    apply Real.le_sqrt_of_sq_le; norm_num
  have hsx : Real.sqrt x ≤ 1 / 5 := by
    rw [Real.sqrt_le_left (by norm_num)]; linarith
  rw [div_le_iff₀ hs3]
  have : x * Real.sqrt x ≤ x * (1 / 5) := mul_le_mul_of_nonneg_left hsx hx0
  nlinarith [mul_nonneg hx0 (sub_nonneg.2 h53)]

theorem nuC_pos : 0 < nuC qS := by
  unfold nuC qS; norm_num

set_option maxHeartbeats 8000000 in
/-- **Entropy step of NU**: for `0 < x = p - 1/4 ≤ 1/25`, with `y = t - 1/16 - 3x/4`,
`2 - H_{q_s}(λ) ≥ (c + d) x - b y - γ x²` for the HT row (`c = α + 8β - γ/2`, `b = 12β`, `d = 1/125`). -/
theorem nu_entropy_bound {l : Fin 4 → ℝ} (hl : IsProb4 l) (hx0 : 0 < pur l - 1 / 4)
    (hx1 : pur l - 1 / 4 ≤ 1 / 25) :
    (aH + 8 * bH - gH / 2 + 1 / 125) * (pur l - 1 / 4) -
      12 * bH * (cub l - 1 / 16 - 3 / 4 * (pur l - 1 / 4)) - gH * (pur l - 1 / 4) ^ 2 ≤
    2 - renyiSpec qS l := by
  obtain ⟨x, hxdef⟩ : ∃ x, x = pur l - 1 / 4 := ⟨_, rfl⟩
  obtain ⟨y, hydef⟩ : ∃ y, y = cub l - 1 / 16 - 3 / 4 * (pur l - 1 / 4) := ⟨_, rfl⟩
  rw [← hydef]
  rw [← hxdef] at hx0 hx1 ⊢
  have hw := w_sums hl.2
  rw [← hydef] at hw
  rw [← hxdef] at hw
  obtain ⟨hw2, hw3⟩ := hw
  have hN := nu_taylor_sum hl
  rw [hw2, hw3] at hN
  obtain ⟨S4, hS4def⟩ : ∃ S, S = ∑ i, (l i - 1 / 4) ^ 4 := ⟨_, rfl⟩
  rw [← hS4def] at hN
  -- x S4 ≥ x³/4 + y²
  have hsum0 : (l 0 - 1 / 4) + (l 1 - 1 / 4) + (l 2 - 1 / 4) + (l 3 - 1 / 4) = 0 := by
    have := hl.2; simp only [Fin.sum_univ_four] at this; linarith
  have hS := sum_w4_ge hsum0
  have hS' : x * S4 ≥ x ^ 3 / 4 + y ^ 2 := by
    have e2 : x = (l 0 - 1 / 4) ^ 2 + (l 1 - 1 / 4) ^ 2 + (l 2 - 1 / 4) ^ 2 + (l 3 - 1 / 4) ^ 2 := by
      rw [← hw2]; simp [Fin.sum_univ_four]
    have e3 : y = (l 0 - 1 / 4) ^ 3 + (l 1 - 1 / 4) ^ 3 + (l 2 - 1 / 4) ^ 3 + (l 3 - 1 / 4) ^ 3 := by
      rw [← hw3]; simp [Fin.sum_univ_four]
    have e4 : S4 = (l 0 - 1 / 4) ^ 4 + (l 1 - 1 / 4) ^ 4 + (l 2 - 1 / 4) ^ 4 + (l 3 - 1 / 4) ^ 4 := by
      rw [hS4def]; simp [Fin.sum_univ_four]
    rw [e2, e3, e4] at *
    exact hS
  -- v = y / x
  obtain ⟨v, hv⟩ : ∃ v, v = y / x := ⟨_, rfl⟩
  have hyv : y = x * v := by rw [hv]; field_simp
  have hyb : |y| ≤ 3 / 25 * x := by
    rw [hydef, hxdef]; exact y_le hl (by rw [← hxdef]; exact hx1)
  have hvb : |v| ≤ 3 / 25 := by
    rw [hv, abs_div, abs_of_pos hx0, div_le_iff₀ hx0]; linarith
  obtain ⟨hv1, hv2⟩ := abs_le.1 hvb
  have hS4v : S4 ≥ x ^ 2 / 4 + x * v ^ 2 := by
    have : x * S4 ≥ x * (x ^ 2 / 4 + x * v ^ 2) := by
      rw [hyv] at hS'; nlinarith [hS']
    exact le_of_mul_le_mul_left this hx0
  -- N ≥ 1 + z
  have hC := nuC_pos
  obtain ⟨z, hzdef⟩ : ∃ z, z = x * ((nuA qS + nuB qS * v + nuC qS * v ^ 2) +
      x * (nuC qS / 4 + nuT qS * v)) := ⟨_, rfl⟩
  have hNz : 1 + z ≤ (4 : ℝ) ^ (qS - 1) * ∑ i, l i ^ qS := by
    have hC4 := mul_le_mul_of_nonneg_left hS4v hC.le
    have e1 : 1 + z = 1 + nuA qS * x + nuB qS * (x * v) + nuC qS * (x ^ 2 / 4 + x * v ^ 2) +
        nuT qS * x * (x * v) := by rw [hzdef]; ring
    rw [hyv] at hN
    linarith [hN, hC4, e1]
  -- z ≥ 0
  have hVpos : 0 ≤ nuA qS + nuB qS * v + nuC qS * v ^ 2 := by
    unfold nuA nuB nuC qS; nlinarith [sq_nonneg v]
  have hWpos : 0 ≤ nuC qS / 4 + nuT qS * v := by
    unfold nuT nuC qS; nlinarith
  have hz0 : 0 ≤ z := by
    rw [hzdef]; positivity
  -- logarithms
  have hZq : 0 < ∑ i, l i ^ qS := sum_rpow_pos hl.1 hl.2
  have hNpos : 0 < (4 : ℝ) ^ (qS - 1) * ∑ i, l i ^ qS := by positivity
  have hlogN : Real.log (1 + z) ≤ Real.log ((4 : ℝ) ^ (qS - 1) * ∑ i, l i ^ qS) :=
    Real.log_le_log (by linarith) hNz
  have hl4 := log_ge_taylor4 hz0
  -- Bernstein certificate
  have hG := nuG_nonneg hx0.le hx1 (by linarith) hv2
  have hKz : x * nuG x v = (z - z ^ 2 / 2 + z ^ 3 / 3 - z ^ 4 / 4) -
      (587 / 1000 * (6931471808 / 10 ^ 10)) * (x * ((aH + 8 * bH - gH / 2 + 1 / 125) - 12 * bH * v - gH * x)) := by
    rw [hzdef]; simp only [nuG, nuA, nuB, nuC, nuT, qS, aH, bH, gH]; ring
  have hLge : (587 / 1000 * (6931471808 / 10 ^ 10)) * (x * ((aH + 8 * bH - gH / 2 + 1 / 125) - 12 * bH * v - gH * x)) ≤
      Real.log ((4 : ℝ) ^ (qS - 1) * ∑ i, l i ^ qS) := by
    have := mul_nonneg hx0.le hG
    linarith
  -- H in terms of logs
  have hL2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hLlt : Real.log 2 < 6931471808 / 10 ^ 10 := by
    have := Real.log_two_lt_d9; norm_num at this ⊢; linarith
  have hlogNeq : Real.log ((4 : ℝ) ^ (qS - 1) * ∑ i, l i ^ qS) =
      (qS - 1) * Real.log 2 * (2 - renyiSpec qS l) := by
    rw [Real.log_mul (by positivity) hZq.ne', Real.log_rpow (by norm_num),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    unfold renyiSpec Real.logb
    have h1 : (1 - qS) ≠ 0 := by unfold qS; norm_num
    field_simp
    push_cast
    ring
  rw [hlogNeq] at hLge
  have hK : 0 ≤ (aH + 8 * bH - gH / 2 + 1 / 125) - 12 * bH * v - gH * x := by
    unfold aH bH gH; nlinarith
  have hr : 0 < qS - 1 := by unfold qS; norm_num
  have hxK : 0 ≤ x * ((aH + 8 * bH - gH / 2 + 1 / 125) - 12 * bH * v - gH * x) := mul_nonneg hx0.le hK
  have step : (qS - 1) * Real.log 2 * (x * ((aH + 8 * bH - gH / 2 + 1 / 125) - 12 * bH * v - gH * x)) ≤
      (qS - 1) * Real.log 2 * (2 - renyiSpec qS l) := by
    refine le_trans ?_ hLge
    have e : (587 / 1000 : ℝ) = qS - 1 := by unfold qS; norm_num
    rw [e]
    have := mul_le_mul_of_nonneg_left hLlt.le (mul_nonneg hr.le hxK)
    nlinarith [this]
  have hpos : 0 < (qS - 1) * Real.log 2 := mul_pos hr hL2
  have := le_of_mul_le_mul_left step hpos
  rw [hyv]
  nlinarith [this]

theorem Lam_c2_sub_Lam {l : Fin 4 → ℝ} :
    Lam qS aH bH gH c2 - Lam qS aH bH gH l =
      (2 - renyiSpec qS l) - (aH + 8 * bH - gH / 2) * (pur l - 1 / 4) +
        12 * bH * (cub l - 1 / 16 - 3 / 4 * (pur l - 1 / 4)) + gH * (pur l - 1 / 4) ^ 2 := by
  have h1 : qS ≠ 1 := by unfold qS; norm_num
  rw [Lam_c2 (by unfold qS; norm_num) h1]
  unfold Lam
  ring

/-- **`lem:fqe-near-uniform-dual` (NU), proved.** -/
theorem nearUniformDual : NearUniformDual := by
  intro l hl hp
  have hq := pur_ge_quarter hl
  rcases hq.eq_or_lt with h | h
  · have hu := pur_eq_quarter hl h.symm
    have : l = c2 := by funext i; rw [hu i]; unfold c2; fin_cases i <;> simp
    subst this
    rw [← h]; simp
  · have hx1 : pur l - 1 / 4 ≤ 1 / 25 := by linarith
    have := nu_entropy_bound hl (by linarith) hx1
    rw [Lam_c2_sub_Lam]
    have hd : (pur l - 1 / 4) / 125 = (1 / 125) * (pur l - 1 / 4) := by ring
    rw [hd]
    nlinarith [this]

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.nearUniformDual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nearUniformDual

end FormalResearch.FourQubitEntropy.RenyiFull
