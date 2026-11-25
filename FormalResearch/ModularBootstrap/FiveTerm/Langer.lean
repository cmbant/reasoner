module

public import FormalResearch.ModularBootstrap.Upper.Comb.ZeroLaw

/-!
# Tip expansions of the zero density and counting function (`cts:langer`(1), Paper II FIVE-0)

Source: `CFT/modular_bootstrap/paper/constant_term_slit_strip.tex`, Proposition C1 (`cts:langer`).

Near the fold tip `ξ_*`, with `r = x - ξ_*`, `ρ_U(x) = (4/(3π)) arccosh(sinh πx)` and
`N(x) = ½ ∫_{ξ_*}^x ρ_U` (`cumulN`):

* `rhoU_tip_expansion`: `ρ_U(ξ_*+r) = 3 k_tip r^{1/2} (1 + (π/(12√2)) r + O(r²))`;
* `cumulN_tip_expansion`: `N(ξ_*+r) = k_tip r^{3/2} (1 + (π/(20√2)) r + O(r²))`;
* `tau_tip_expansion`: `τ(ξ_*+r) = r (1 + (π/(30√2)) r + O(r²))`, `τ(x) = (N(x)/k_tip)^{2/3}`.

All O-terms are explicit (`|·| ≤ C r²`) and the proofs use only the exponential series
(`Real.exp_bound`); the arccosh expansion is obtained from `cosh A = 1 + s` by inverting the cosh
series for `A²` (no arsinh Taylor series).
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Upper.Comb


lemma cosh_bounds {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    1 + t ^ 2 / 2 + t ^ 4 / 24 ≤ Real.cosh t ∧
      Real.cosh t ≤ 1 + t ^ 2 / 2 + t ^ 4 / 24 + t ^ 6 / 500 := by
  have e1 := Real.exp_bound (x := t) (by rw [abs_of_nonneg h0]; exact h1) (n := 8) (by norm_num)
  have e2 := Real.exp_bound (x := -t) (by rw [abs_neg, abs_of_nonneg h0]; exact h1) (n := 8)
    (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, abs_neg,
    abs_of_nonneg h0] at e1 e2
  norm_num at e1 e2
  rw [abs_le] at e1 e2
  rw [Real.cosh_eq]
  have h6 : t ^ 6 ≤ 1 := pow_le_one₀ h0 h1
  have h8 : t ^ 8 ≤ t ^ 6 := pow_le_pow_of_le_one h0 h1 (by norm_num)
  have p6 : 0 ≤ t ^ 6 := by positivity
  constructor
  · nlinarith [e1.1, e2.1, h8, p6]
  · nlinarith [e1.2, e2.2, h8, p6]

lemma sinh_bounds {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    t ≤ Real.sinh t ∧ Real.sinh t ≤ t + t ^ 3 / 5 := by
  refine ⟨Real.self_le_sinh_iff.mpr h0, ?_⟩
  have e1 := Real.exp_bound (x := t) (by rw [abs_of_nonneg h0]; exact h1) (n := 6) (by norm_num)
  have e2 := Real.exp_bound (x := -t) (by rw [abs_neg, abs_of_nonneg h0]; exact h1) (n := 6)
    (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, abs_neg,
    abs_of_nonneg h0] at e1 e2
  norm_num at e1 e2
  rw [abs_le] at e1 e2
  rw [Real.sinh_eq]
  have h3 : t ^ 5 ≤ t ^ 3 := pow_le_pow_of_le_one h0 h1 (by norm_num)
  have h4 : t ^ 6 ≤ t ^ 3 := pow_le_pow_of_le_one h0 h1 (by norm_num)
  nlinarith [e1.2, e2.1, h3, h4]
lemma q_bounds_aux {q s : ℝ} (hq : 0 ≤ q) (hs0 : 0 ≤ s) (hs : s ≤ 1 / 5)
    (hl : q / 2 + q ^ 2 / 24 ≤ s) (hu : s ≤ q / 2 + q ^ 2 / 24 + q ^ 3 / 500) :
    |q - (2 * s - s ^ 2 / 3)| ≤ s ^ 3 / 8 := by
  have hq2 : q ≤ 2 * s := by nlinarith only [hl, sq_nonneg q]
  have hq2' : q ^ 2 ≤ 4 * s ^ 2 := by nlinarith only [hq2, hq]
  have hq3 : q ^ 3 ≤ 8 * s ^ 3 := by
    have := pow_le_pow_left₀ hq hq2 3
    nlinarith only [this]
  have hlo : 2 * s - s ^ 2 / 3 - s ^ 3 / 30 ≤ q := by
    nlinarith only [hu, hq2', hq3, hs0]
  rw [abs_le]
  constructor
  · -- q ≥ 2s - s^2/3 - s^3/8
    nlinarith only [hlo, pow_nonneg hs0 3]
  · -- q ≤ 2s - q²/12, with q² ≥ (2s - s²/3 - s³/30)²
    have hpos : 0 ≤ 2 * s - s ^ 2 / 3 - s ^ 3 / 30 := by nlinarith only [hs0, hs]
    have hsq : (2 * s - s ^ 2 / 3 - s ^ 3 / 30) ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ hpos hlo 2
    nlinarith only [hsq, hl, hs0, hs, pow_nonneg hs0 3, pow_nonneg hs0 4, pow_nonneg hs0 5, pow_nonneg hs0 6]

lemma s_bounds {δ : ℝ} (h0 : 0 < δ) (h1 : δ ≤ 1 / 10) :
    √2 * δ + δ ^ 2 / 2 ≤ Real.cosh δ + √2 * Real.sinh δ - 1 ∧
      Real.cosh δ + √2 * Real.sinh δ - 1 ≤ √2 * δ + δ ^ 2 / 2 + δ ^ 3 / 2 := by
  have h1' : δ ≤ 1 := by linarith
  obtain ⟨c1, c2⟩ := cosh_bounds h0.le h1'
  obtain ⟨s1, s2⟩ := sinh_bounds h0.le h1'
  have hu : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hu0 : 0 ≤ √2 := Real.sqrt_nonneg _
  have hu1 : √2 ≤ 71 / 50 := by nlinarith only [hu, hu0]
  have p4 : δ ^ 4 ≤ δ ^ 3 / 10 := by
    have : δ ^ 4 = δ ^ 3 * δ := by ring
    rw [this]; nlinarith only [pow_pos h0 3, h1]
  have p6 : δ ^ 6 ≤ δ ^ 3 / 1000 := by
    have : δ ^ 6 = δ ^ 3 * δ ^ 3 := by ring
    have h3 : δ ^ 3 ≤ 1 / 1000 := by
      have := pow_le_pow_left₀ h0.le h1 3
      norm_num at this ⊢; linarith
    rw [this]; nlinarith only [pow_pos h0 3, h3]
  have p4' : 0 ≤ δ ^ 4 := by positivity
  constructor
  · nlinarith only [c1, s1, p4', hu0, h0]
  · have := mul_le_mul_of_nonneg_left s2 hu0
    nlinarith only [c2, this, p4, p6, hu1, pow_pos h0 3]

lemma le_one_of_cosh {A s : ℝ} (hA : 0 ≤ A) (hs : s ≤ 1 / 5) (hc : Real.cosh A = 1 + s) : A ≤ 1 := by
  by_contra h
  rw [not_le] at h
  have h1 : Real.cosh 1 < Real.cosh A := by
    rw [Real.cosh_lt_cosh, abs_of_pos one_pos, abs_of_nonneg hA]; exact h
  have h2 := (cosh_bounds (t := 1) zero_le_one le_rfl).1
  norm_num at h2
  linarith

lemma q_expansion {δ A : ℝ} (h0 : 0 < δ) (h1 : δ ≤ 1 / 10) (hA0 : 0 ≤ A)
    (hc : Real.cosh A = Real.cosh δ + √2 * Real.sinh δ) :
    |A ^ 2 - (2 * √2 * δ + δ ^ 2 / 3)| ≤ 5 / 2 * δ ^ 3 := by
  obtain ⟨sl, su⟩ := s_bounds h0 h1
  set s : ℝ := Real.cosh δ + √2 * Real.sinh δ - 1 with hsdef
  have hu : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hu0 : 0 ≤ √2 := Real.sqrt_nonneg _
  have hu1 : √2 ≤ 71 / 50 := by nlinarith only [hu, hu0]
  have hu2 : 7 / 5 ≤ √2 := by nlinarith only [hu, hu0]
  have hs0 : 0 ≤ s := by nlinarith only [sl, hu0, h0, sq_nonneg δ]
  have hs5 : s ≤ 1 / 5 := by
    nlinarith only [su, hu1, h0, h1, pow_pos h0 3, mul_pos h0 h0]
  have hc' : Real.cosh A = 1 + s := by rw [hc, hsdef]; ring
  have hA1 := le_one_of_cosh hA0 hs5 hc'
  obtain ⟨cl, cu⟩ := cosh_bounds hA0 hA1
  rw [hc'] at cl cu
  have hq := q_bounds_aux (q := A ^ 2) (s := s) (by positivity) hs0 hs5 (by nlinarith only [cl])
    (by nlinarith only [cu])
  rw [abs_le] at hq ⊢
  obtain ⟨e, he⟩ : ∃ e, s = √2 * δ + δ ^ 2 / 2 + e := ⟨s - (√2 * δ + δ ^ 2 / 2), by ring⟩
  have he0 : 0 ≤ e := by nlinarith only [he, sl]
  have he1 : e ≤ δ ^ 3 / 2 := by nlinarith only [he, su]
  have hs15 : s ≤ 3 / 2 * δ := by
    nlinarith only [he, he1, hu1, h0, h1, pow_pos h0 3, mul_pos h0 h0]
  have hs3 : s ^ 3 ≤ 27 / 8 * δ ^ 3 := by
    have := pow_le_pow_left₀ hs0 hs15 3
    nlinarith only [this]
  have p3 := pow_pos h0 3
  have hexp : 2 * s - s ^ 2 / 3 - (2 * √2 * δ + δ ^ 2 / 3) =
      2 * e - (1 / 3) * (√2 * δ ^ 3 + δ ^ 4 / 4 + 2 * √2 * δ * e + δ ^ 2 * e + e ^ 2) := by
    rw [he]; nlinarith only [hu]
  have hmid : |2 * s - s ^ 2 / 3 - (2 * √2 * δ + δ ^ 2 / 3)| ≤ 2 * δ ^ 3 := by
    rw [hexp, abs_le]
    have b1 : δ ^ 4 ≤ δ ^ 3 / 10 := by
      have : δ ^ 4 = δ ^ 3 * δ := by ring
      rw [this]; nlinarith only [p3, h1]
    have b2 : δ * e ≤ δ ^ 3 / 20 := by nlinarith only [he0, he1, h0, h1, p3]
    have hδ3 : δ ^ 3 ≤ 1 / 1000 := by
      have := pow_le_pow_left₀ h0.le h1 3
      norm_num at this ⊢; linarith
    have b3 : √2 * δ * e ≤ 3 / 40 * δ ^ 3 := by
      have : √2 * δ * e = √2 * (δ * e) := by ring
      rw [this]
      have := mul_le_mul hu1 b2 (mul_nonneg h0.le he0) (by norm_num)
      nlinarith only [this, p3]
    have b4 : δ ^ 2 * e ≤ δ ^ 3 / 200 := by nlinarith only [he0, he1, h0, h1, p3, b2]
    have b5 : e ^ 2 ≤ δ ^ 3 / 200 := by
      have h := pow_le_pow_left₀ he0 he1 2
      have : (δ ^ 3 / 2) ^ 2 = δ ^ 3 * (δ ^ 3 / 4) := by ring
      nlinarith only [h, this, hδ3, p3]
    have b6 : √2 * δ ^ 3 ≤ 3 / 2 * δ ^ 3 := by nlinarith only [hu1, p3]
    have q1 : 0 ≤ √2 * δ ^ 3 := by positivity
    have q2 : 0 ≤ √2 * δ * e := by positivity
    have q3 : 0 ≤ δ ^ 2 * e := by positivity
    have q4 : 0 ≤ e ^ 2 := sq_nonneg e
    have q5 : 0 ≤ δ ^ 4 := by positivity
    constructor <;> nlinarith only [b1, b3, b4, b5, b6, he0, he1, p3, q1, q2, q3, q4, q5]
  rw [abs_le] at hmid
  constructor <;> nlinarith only [hq.1, hq.2, hmid.1, hmid.2, hs3, p3]

/-! ### Expansion of the zero density -/

lemma abs_sqrt_sub_le {w : ℝ} (hw : 0 ≤ w) : |√w - (1 + (w - 1) / 2)| ≤ (w - 1) ^ 2 / 2 := by
  have hy := Real.sq_sqrt hw
  have hy0 := Real.sqrt_nonneg w
  set y := √w
  have h1 : y - (1 + (w - 1) / 2) = -((y - 1) ^ 2 / 2) := by rw [← hy]; ring
  rw [h1, abs_neg, abs_of_nonneg (by positivity)]
  have h2 : (y - 1) ^ 2 ≤ (w - 1) ^ 2 := by
    have : w - 1 = (y - 1) * (y + 1) := by rw [← hy]; ring
    rw [this, mul_pow]
    nlinarith only [mul_nonneg (sq_nonneg (y - 1)) (by nlinarith only [hy0] : 0 ≤ (y + 1) ^ 2 - 1)]
  linarith

lemma cosh_pi_xiStar : Real.cosh (π * xiStar) = √2 := by
  have h := Real.cosh_sq (π * xiStar)
  rw [sinh_pi_mul_xiStar] at h
  rw [← Real.sqrt_sq (Real.cosh_pos (π * xiStar)).le, h]
  norm_num

lemma cosh_tipArgA_eq {r : ℝ} (hr : 0 ≤ r) :
    Real.cosh (tipArgA r) = Real.cosh (π * r) + √2 * Real.sinh (π * r) := by
  rw [cosh_tipArgA hr, mul_add, Real.sinh_add, sinh_pi_mul_xiStar, cosh_pi_xiStar]
  ring

/-- `(4/(3π)) √(2√2 · π r) = 3 k_tip √r`. -/
lemma three_kTip_mul_sqrt (r : ℝ) :
    4 / (3 * π) * √(2 * √2 * (π * r)) = 3 * kTip * √r := by
  have hpi := Real.pi_pos
  have h2 : (2 : ℝ) ^ (3 / 4 : ℝ) = √(2 * √2) := by
    rw [Real.sqrt_eq_rpow, show (2 * √2 : ℝ) = (2 : ℝ) ^ (3 / 2 : ℝ) by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add two_pos, Real.rpow_one,
        Real.sqrt_eq_rpow], ← Real.rpow_mul (by norm_num)]
    norm_num
  have hsq : √π * √π = π := Real.mul_self_sqrt hpi.le
  have hsp : 0 < √π := Real.sqrt_pos.mpr hpi
  unfold kTip
  have e : √(2 * √2 * (π * r)) = √(2 * √2) * (√π * √r) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hpi.le]
  have hsq2 : √π ^ 2 = π := Real.sq_sqrt hpi.le
  rw [e, ← h2]
  field_simp
  rw [hsq2]
  ring

/-- **Tip expansion of `ρ_U`** (`cts:langer`(1), first line): for `0 < r` with `π r ≤ 1/10`,
`ρ_U(ξ_*+r) = 3 k_tip √r (1 + (π/(12√2)) r + E)`, `|E| ≤ (π²/2) r²`. -/
theorem rhoU_tip_expansion {r : ℝ} (hr : 0 < r) (hr1 : π * r ≤ 1 / 10) :
    |rhoU (xiStar + r) / (3 * kTip * √r) - 1 - π / (12 * √2) * r| ≤ π ^ 2 / 2 * r ^ 2 := by
  have hpi := Real.pi_pos
  set δ : ℝ := π * r with hδ
  have hδ0 : 0 < δ := mul_pos hpi hr
  have hu : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hu0 : 0 < √2 := Real.sqrt_pos.mpr (by norm_num)
  have hu1 : √2 ≤ 71 / 50 := by nlinarith only [hu, hu0]
  have hu2 : 7 / 5 ≤ √2 := by nlinarith only [hu, hu0]
  have hA0 : 0 ≤ tipArgA r := (tipArgA_pos hr).le
  have hq := q_expansion hδ0 hr1 hA0 (cosh_tipArgA_eq hr.le)
  set t : ℝ := 2 * √2 * δ with ht
  have ht0 : 0 < t := by positivity
  set A : ℝ := tipArgA r with hAdef
  set w : ℝ := A ^ 2 / t with hw
  have hw0 : 0 ≤ w := by positivity
  have hAeq : A = √t * √w := by
    rw [← Real.sqrt_mul ht0.le, hw, mul_div_cancel₀ _ ht0.ne', Real.sqrt_sq hA0]
  have hrho : rhoU (xiStar + r) = 4 / (3 * π) * A := by
    rw [rhoU_eq_of_ge (by linarith)]
    rfl
  have hratio : rhoU (xiStar + r) / (3 * kTip * √r) = √w := by
    have h3 := three_kTip_mul_sqrt r
    have hk : 0 < 3 * kTip * √r := by
      have := kTip_pos
      have := Real.sqrt_pos.mpr hr
      positivity
    rw [div_eq_iff hk.ne', hrho, hAeq, ← h3, ← mul_assoc, ← mul_assoc]
    rw [show 2 * √2 * (π * r) = t from rfl]
    ring
  -- w - 1 = δ/(6√2) + R/t with |R| ≤ 5/2 δ^3
  obtain ⟨R, hR, hRb⟩ : ∃ R, A ^ 2 = t + δ ^ 2 / 3 + R ∧ |R| ≤ 5 / 2 * δ ^ 3 :=
    ⟨A ^ 2 - (t + δ ^ 2 / 3), by ring, hq⟩
  have hwm1 : w - 1 = δ / (6 * √2) + R / t := by
    have key : δ ^ 2 / 3 / t = δ / (6 * √2) := by
      rw [ht]; field_simp; nlinarith only [hu]
    rw [hw, hR]
    field_simp
    have := key
    field_simp at this
    nlinarith only [this]
  have hRt : |R / t| ≤ 9 / 10 * δ ^ 2 := by
    rw [abs_div, abs_of_pos ht0, div_le_iff₀ ht0]
    have : 9 / 10 * δ ^ 2 * t = 9 / 5 * √2 * δ ^ 3 := by rw [ht]; ring
    rw [this]
    nlinarith only [hRb, hu2, pow_pos hδ0 3]
  have hz : |w - 1| ≤ δ / 4 := by
    rw [hwm1]
    refine (abs_add_le _ _).trans ?_
    have h1 : |δ / (6 * √2)| ≤ δ / 8 := by
      rw [abs_of_pos (by positivity), div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith only [hu2, hδ0]
    have h2 : δ ^ 2 ≤ δ / 10 := by nlinarith only [hr1, hδ0]
    linarith
  have hsq := abs_sqrt_sub_le hw0
  have hz2 : (w - 1) ^ 2 ≤ δ ^ 2 / 16 := by
    have := sq_le_sq' (by linarith [abs_le.mp hz]) (abs_le.mp hz).2
    nlinarith only [hz, sq_abs (w - 1), abs_nonneg (w - 1), hδ0]
  rw [hratio]
  have e1 : √w - 1 - π / (12 * √2) * r = (√w - (1 + (w - 1) / 2)) + (R / t) / 2 := by
    have : π / (12 * √2) * r = δ / (12 * √2) := by rw [hδ]; ring
    rw [this]
    have h2 : (w - 1) / 2 = δ / (12 * √2) + (R / t) / 2 := by
      rw [hwm1]; field_simp; ring
    linarith
  rw [e1]
  have : π ^ 2 / 2 * r ^ 2 = δ ^ 2 / 2 := by rw [hδ]; ring
  rw [this]
  refine (abs_add_le _ _).trans ?_
  have : |R / t / 2| ≤ 9 / 20 * δ ^ 2 := by
    rw [abs_div, abs_two]; nlinarith only [hRt]
  nlinarith only [hsq, hz2, this, abs_nonneg (R / t)]

/-! ### Expansion of the counting function and of the Langer coordinate -/

private lemma rpow_three_halves {t : ℝ} (ht : 0 ≤ t) : t ^ (3 / 2 : ℝ) = t * √t := by
  rcases ht.eq_or_lt with h | h
  · rw [← h]; simp
  · rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add h, Real.rpow_one, ← Real.sqrt_eq_rpow]

private lemma rpow_five_halves {t : ℝ} (ht : 0 ≤ t) : t ^ (5 / 2 : ℝ) = t ^ 2 * √t := by
  rcases ht.eq_or_lt with h | h
  · rw [← h]; simp
  · rw [show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num, Real.rpow_add h, ← Real.sqrt_eq_rpow]
    norm_num

/-- **Tip expansion of `N`** (`cts:langer`(1), second line): for `0 < r`, `π r ≤ 1/10`,
`N(ξ_*+r) = k_tip (r^{3/2} + (π/(20√2)) r^{5/2}) + E`, `|E| ≤ (3 k_tip π²/14) r^{7/2}`. -/
theorem cumulN_tip_expansion {r : ℝ} (hr : 0 < r) (hr1 : π * r ≤ 1 / 10) :
    |cumulN (xiStar + r) -
        kTip * (r ^ (3 / 2 : ℝ) + π / (20 * √2) * r ^ (5 / 2 : ℝ))| ≤
      3 * kTip * π ^ 2 / 14 * r ^ (7 / 2 : ℝ) := by
  have hpi := Real.pi_pos
  have hk := kTip_pos
  have hu0 : 0 < √2 := Real.sqrt_pos.mpr (by norm_num)
  set a : ℝ := π / (12 * √2) with ha
  set g : ℝ → ℝ := fun t => 3 * kTip * (t ^ (1 / 2 : ℝ) + a * t ^ (3 / 2 : ℝ)) with hg
  set M : ℝ := 3 * kTip * π ^ 2 / 2 with hM
  have hshift : cumulN (xiStar + r) = 1 / 2 * ∫ t in (0 : ℝ)..r, rhoU (xiStar + t) := by
    unfold cumulN
    rw [intervalIntegral.integral_comp_add_left (f := rhoU) xiStar]
    simp
  have hint_rho : IntervalIntegrable (fun t => rhoU (xiStar + t)) volume 0 r := by
    have := intervalIntegrable_rhoU (a := xiStar) (b := xiStar + r) le_rfl (by linarith)
    have h2 := this.comp_add_left xiStar
    simpa using h2
  have hint_g : IntervalIntegrable g volume 0 r := by
    refine IntervalIntegrable.const_mul ?_ _
    exact (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).add
      ((intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul _)
  have hint_M : IntervalIntegrable (fun t : ℝ => M * t ^ (5 / 2 : ℝ)) volume 0 r :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul _
  have hpt : ∀ t ∈ Ioc (0 : ℝ) r, ‖rhoU (xiStar + t) - g t‖ ≤ M * t ^ (5 / 2 : ℝ) := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have ht1 : π * t ≤ 1 / 10 := by nlinarith only [ht.2, hr1, hpi]
    have h := rhoU_tip_expansion ht0 ht1
    have hs : 0 < 3 * kTip * √t := by have := Real.sqrt_pos.mpr ht0; positivity
    have h2 : rhoU (xiStar + t) - g t =
        3 * kTip * √t * (rhoU (xiStar + t) / (3 * kTip * √t) - 1 - a * t) := by
      simp only [hg, ← Real.sqrt_eq_rpow, rpow_three_halves ht0.le]
      field_simp
      ring
    rw [Real.norm_eq_abs, h2, abs_mul, abs_of_pos hs]
    calc 3 * kTip * √t * |rhoU (xiStar + t) / (3 * kTip * √t) - 1 - a * t|
        ≤ 3 * kTip * √t * (π ^ 2 / 2 * t ^ 2) := by
          have : π / (12 * √2) * t = a * t := by rw [ha]
          rw [this] at h
          exact mul_le_mul_of_nonneg_left h hs.le
      _ = M * t ^ (5 / 2 : ℝ) := by rw [rpow_five_halves ht0.le, hM]; ring
  have hbound := intervalIntegral.norm_integral_le_of_norm_le hr.le
    (Filter.Eventually.of_forall hpt) hint_M
  have hsub : ∫ t in (0 : ℝ)..r, (rhoU (xiStar + t) - g t) =
      (∫ t in (0 : ℝ)..r, rhoU (xiStar + t)) - ∫ t in (0 : ℝ)..r, g t :=
    intervalIntegral.integral_sub hint_rho hint_g
  have hIg : ∫ t in (0 : ℝ)..r, g t =
      3 * kTip * (2 / 3 * r ^ (3 / 2 : ℝ) + a * (2 / 5) * r ^ (5 / 2 : ℝ)) := by
    simp only [hg]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
      (intervalIntegral.intervalIntegrable_rpow' (by norm_num))
      ((intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul _),
      intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num)),
      integral_rpow (Or.inl (by norm_num))]
    rw [Real.zero_rpow (by norm_num), Real.zero_rpow (by norm_num),
      show (1 / 2 : ℝ) + 1 = 3 / 2 by norm_num, show (3 / 2 : ℝ) + 1 = 5 / 2 by norm_num]
    ring
  have hIM : ∫ t in (0 : ℝ)..r, M * t ^ (5 / 2 : ℝ) = M * (2 / 7 * r ^ (7 / 2 : ℝ)) := by
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num)),
      Real.zero_rpow (by norm_num), show (5 / 2 : ℝ) + 1 = 7 / 2 by norm_num]
    ring
  rw [hsub, hIg, hIM] at hbound
  rw [hshift]
  generalize (∫ t in (0 : ℝ)..r, rhoU (xiStar + t)) = I at hbound ⊢
  have hmain : 1 / 2 * I - kTip * (r ^ (3 / 2 : ℝ) + π / (20 * √2) * r ^ (5 / 2 : ℝ)) =
      1 / 2 * (I - 3 * kTip * (2 / 3 * r ^ (3 / 2 : ℝ) + a * (2 / 5) * r ^ (5 / 2 : ℝ))) := by
    rw [ha]; field_simp; ring
  rw [hmain, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  rw [Real.norm_eq_abs] at hbound
  calc 1 / 2 * |I - 3 * kTip * (2 / 3 * r ^ (3 / 2 : ℝ) + a * (2 / 5) * r ^ (5 / 2 : ℝ))|
      ≤ 1 / 2 * (M * (2 / 7 * r ^ (7 / 2 : ℝ))) := mul_le_mul_of_nonneg_left hbound (by norm_num)
    _ = _ := by rw [hM]; ring

lemma rpow_two_thirds_bounds {u : ℝ} (hu : |u| ≤ 1 / 2) :
    |(1 + u) ^ (2 / 3 : ℝ) - 1 - 2 * u / 3| ≤ u ^ 2 / 2 := by
  obtain ⟨hu1, hu2⟩ := abs_le.mp hu
  have hpos : 0 < 1 + u := by linarith
  set y : ℝ := (1 + u) ^ (2 / 3 : ℝ) with hy
  have hy0 : 0 < y := Real.rpow_pos_of_pos hpos _
  have hy3 : y ^ 3 = (1 + u) ^ 2 := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
    norm_num
  have hup : y ≤ 1 + 2 * u / 3 := by
    by_contra h
    rw [not_le] at h
    have hM : 0 ≤ 1 + 2 * u / 3 := by linarith
    have := pow_lt_pow_left₀ h hM (by norm_num : (3 : ℕ) ≠ 0)
    rw [hy3] at this
    nlinarith only [this, sq_nonneg u, mul_nonneg (sq_nonneg u) (by linarith : 0 ≤ 1 / 3 + 8 * u / 27)]
  have hlo : 1 + 2 * u / 3 - u ^ 2 / 2 ≤ y := by
    by_contra h
    rw [not_le] at h
    have hL : 0 ≤ 1 + 2 * u / 3 - u ^ 2 / 2 := by nlinarith only [hu1, hu2]
    have := pow_lt_pow_left₀ h hy0.le (by norm_num : (3 : ℕ) ≠ 0)
    rw [hy3] at this
    have hQ : 0 ≤ 27 * u ^ 4 - 108 * u ^ 3 - 18 * u ^ 2 + 368 * u + 252 := by
      nlinarith only [hu1, hu2, sq_nonneg u, sq_nonneg (u ^ 2), mul_nonneg (sq_nonneg u) (by linarith : 0 ≤ u + 1 / 2),
        mul_nonneg (sq_nonneg u) (by linarith : 0 ≤ 1 / 2 - u)]
    nlinarith only [this, mul_nonneg (sq_nonneg u) hQ]
  rw [abs_le]; constructor <;> linarith

/-- **Tip expansion of the Langer coordinate** `τ(x) = (N(x)/k_tip)^{2/3}`
(`cts:langer`(1), third line): for `0 < r`, `π r ≤ 1/10`,
`|τ(ξ_*+r) - r - (π/(30√2)) r²| ≤ 2 r³`. -/
theorem tau_tip_expansion {r : ℝ} (hr : 0 < r) (hr1 : π * r ≤ 1 / 10) :
    |(cumulN (xiStar + r) / kTip) ^ (2 / 3 : ℝ) - r - π / (30 * √2) * r ^ 2| ≤ 2 * r ^ 3 := by
  have hpi := Real.pi_pos
  have hpi3 : π < 3.15 := Real.pi_lt_d2
  have hpi3' : 3 < π := Real.pi_gt_three
  have hk := kTip_pos
  have hu : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hu0 : 0 < √2 := Real.sqrt_pos.mpr (by norm_num)
  have hu2 : 7 / 5 ≤ √2 := by nlinarith only [hu, hu0]
  have hr0 : r ≤ 1 / 30 := by nlinarith only [hr1, hpi3']
  have hE := cumulN_tip_expansion hr hr1
  set b : ℝ := π / (20 * √2) with hb
  set N : ℝ := cumulN (xiStar + r) with hN
  have hr32 : 0 < r ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hr _
  have h52 : r ^ (5 / 2 : ℝ) = r * r ^ (3 / 2 : ℝ) := by
    rw [show (5 / 2 : ℝ) = 1 + 3 / 2 by norm_num, Real.rpow_add hr, Real.rpow_one]
  have h72 : r ^ (7 / 2 : ℝ) = r ^ 2 * r ^ (3 / 2 : ℝ) := by
    rw [show (7 / 2 : ℝ) = 2 + 3 / 2 by norm_num, Real.rpow_add hr]
    norm_num
  -- N / kTip = r^{3/2} (1 + u), u = b r + e
  obtain ⟨e, he, hebd⟩ : ∃ e, N / kTip = r ^ (3 / 2 : ℝ) * (1 + (b * r + e)) ∧
      |e| ≤ 3 * π ^ 2 / 14 * r ^ 2 := by
    refine ⟨(N - kTip * (r ^ (3 / 2 : ℝ) + b * r ^ (5 / 2 : ℝ))) / (kTip * r ^ (3 / 2 : ℝ)), ?_, ?_⟩
    · field_simp; rw [h52]; ring
    · rw [abs_div, abs_of_pos (mul_pos hk hr32), div_le_iff₀ (mul_pos hk hr32)]
      refine hE.trans ?_
      rw [h72]; nlinarith only [hk, hr32, sq_nonneg r]
  have hb0 : 0 < b := by positivity
  have hb1 : b ≤ 0.12 := by
    rw [hb, div_le_iff₀ (by positivity)]; nlinarith only [hpi3, hu2]
  have hu1 : |b * r + e| ≤ 1 / 2 := by
    have h1 : b * r ≤ 0.004 := by nlinarith only [hb1, hr0, hr.le, hb0]
    have h2 : 3 * π ^ 2 / 14 * r ^ 2 ≤ 0.003 := by
      have : π * r ≤ 1 / 10 := hr1
      nlinarith only [this, hpi, mul_pos hpi hr]
    have := abs_le.mp hebd
    rw [abs_le]; constructor <;> nlinarith only [h1, h2, this, hb0, hr]
  have hτ : (N / kTip) ^ (2 / 3 : ℝ) = r * (1 + (b * r + e)) ^ (2 / 3 : ℝ) := by
    have hnn : 0 ≤ 1 + (b * r + e) := by linarith [(abs_le.mp hu1).1]
    rw [he, Real.mul_rpow hr32.le hnn, ← Real.rpow_mul hr.le]
    norm_num
  rw [hτ]
  have hbd := rpow_two_thirds_bounds hu1
  have heta : π / (30 * √2) = 2 * b / 3 := by rw [hb]; field_simp; ring
  rw [heta]
  have hc : 3 * π ^ 2 / 14 ≤ 2.2 := by nlinarith only [hpi3, hpi3']
  set u : ℝ := b * r + e with hu_def
  have hubound : |u| ≤ (0.12 + 2.2 * (1 / 30)) * r := by
    have := abs_add_le (b * r) e
    have hb' : |b * r| ≤ 0.12 * r := by rw [abs_of_pos (mul_pos hb0 hr)]; nlinarith only [hb1, hr]
    have he' : |e| ≤ 2.2 * (1 / 30) * r := by
      have : 3 * π ^ 2 / 14 * r ^ 2 ≤ 2.2 * r ^ 2 := by nlinarith only [hc, sq_nonneg r]
      nlinarith only [hebd, this, hr0, hr, sq_nonneg r]
    exact this.trans (by linarith)
  have hu2' : u ^ 2 ≤ 0.2 * r ^ 2 := by
    have := sq_le_sq' (by linarith [abs_le.mp hubound, abs_nonneg u]) (abs_le.mp hubound).2
    have h := abs_le.mp hubound
    nlinarith only [sq_abs u, hubound, abs_nonneg u, hr, sq_nonneg r]
  have key : r * (1 + u) ^ (2 / 3 : ℝ) - r - 2 * b / 3 * r ^ 2 =
      r * ((1 + u) ^ (2 / 3 : ℝ) - 1 - 2 * u / 3) + 2 / 3 * r * e := by
    rw [hu_def]; ring
  rw [key]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_pos hr]
  have h1 : r * |(1 + u) ^ (2 / 3 : ℝ) - 1 - 2 * u / 3| ≤ r * (0.1 * r ^ 2) := by
    exact mul_le_mul_of_nonneg_left (hbd.trans (by nlinarith only [hu2'])) hr.le
  have h2 : |2 / 3 * r| * |e| ≤ 2 / 3 * r * (2.2 * r ^ 2) := by
    rw [abs_of_pos (by positivity : (0 : ℝ) < 2 / 3 * r)]
    have : |e| ≤ 2.2 * r ^ 2 := by
      refine hebd.trans ?_
      nlinarith only [hc, sq_nonneg r]
    exact mul_le_mul_of_nonneg_left this (by positivity)
  nlinarith only [h1, h2, pow_pos hr 3]

end FormalResearch.ModularBootstrap.FiveTerm


/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.rhoU_tip_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.rhoU_tip_expansion

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.cumulN_tip_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.cumulN_tip_expansion

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.tau_tip_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.tau_tip_expansion
