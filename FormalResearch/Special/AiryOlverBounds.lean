module

public import FormalResearch.Special.AiryOlver

/-!
# Bounds for Olver's weights: `E² ≍ e^{2ξ}`, `2 e^{2ξ}/E² → 1`, `M² ≍ (2+|x|)^{-1/2}`, `N ≲ (2+|x|)^{1/2} M`

Quantitative real-axis bounds for the objects of `AiryOlver` (`airyOlverE`, `airyOlverM`, `airyDerivWeightN`, the derivative majorant of `AiryOlver`, which is **not** Olver's `N`; here `M` is
*Olver's* `M`, which equals the DLMF 9.8 modulus `airyModSq^{1/2}` only for `x ≤ airyCross`).  Everything is
`ξ(x) = airyXi x = (2/3)(x₊)^{3/2}`.

* `airyOlverE_sq_two_sided`: `(1/3200) e^{2ξ} ≤ E² ≤ 320 e^{2ξ}` for `x > airyCross`;
* `airyAi_div_airyBi_asymptotic`: sharp, `|2 e^{2ξ} Ai/Bi - 1| = O(x^{-3/2})` for `x ≥ 2` (from the first-term
  expansions of `Ai`, `Bi`), i.e. `E^{-2} = Ai/Bi ≈ e^{-2ξ}/2`;
* `airyOlverM_sq_neg_bounds`, `airyOlverM_sq_pos_bounds`, `airyOlverM_sq_two_sided`: on all of `ℝ`,
  `(1/8000)/√(2+|x|) ≤ M² ≤ 600/√(2+|x|)` (on `x ≤ -1` the constants are `1/20`, `3/4`, via the first-term expansions of
  `Ai, Ai', Bi, Bi'` on the negative axis; on `x ≥ -1` via the envelopes `airyAi_envelope_real`, `airyBi_envelope_real`);
* `airyOlverM_div_E_sq_bounds`, `airyOlverM_mul_E_sq_bounds`: for `x > airyCross`, `(M/E)² = 2 Ai² ≍ e^{-2ξ}/√(2+x)`
  and `(M E)² = 2 Bi² ≍ e^{2ξ}/√(2+x)`;
* `airyDerivWeightN_le`: `N ≤ 5300 (2+|x|)^{1/2} M` on all of `ℝ` (the constant is that of the Wronskian bound
  `airyBiDeriv_le_mul_airyBi`; the true constant is `O(1)`).

Numerical check (mpmath, 30 digits, 4801-point grid on `[-60, 60]`; on `[-1000, 300]` the ratio bounds below become `0.999` (limit `1`) and `0.705`, `c = -0.366046328...`): `M²√(2+|x|)` lies in
`[0.3235, 0.6366]` for Olver's `M` (the limit is `1/π` as `x → -∞` and `2/π` as `x → +∞`; the proved constants `1/8000`,
`600` are far from optimal); `2 e^{2ξ} Ai/Bi` equals `0.9199, 0.9814, 0.9934, 0.9977` at `x = 2, 5, 10, 20`; and
`N/((2+|x|)^{1/2} M)` is at most `0.984` on `x ≤ c` (DLMF `N`) and at most `0.696` on `x > c` (the `max`-definition of
`airyDerivWeightN`), versus the proved constant `5300`.

**Not formalised:** the sharp constants; Olver's own `N` (only the majorant `airyDerivWeightN` is defined); a uniform `M² ~ 1/(π √|x|)` asymptotic
for `x → -∞` (only two-sided bounds are proved).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

/-- `(1/3200) e^{2ξ(x)} ≤ E(x)² ≤ 320 e^{2ξ(x)}` for `x > airyCross` (from the envelopes of `Ai` and `Bi`),
`ξ(x) = (2/3)(x₊)^{3/2}` (`airyXi`). -/
theorem airyOlverE_sq_two_sided {x : ℝ} (hx : airyCross < x) :
    1 / 3200 * Real.exp (2 * airyXi x) ≤ airyOlverE x ^ 2 ∧ airyOlverE x ^ 2 ≤ 320 * Real.exp (2 * airyXi x) := by
  have hx1 : -1 ≤ x := airyCross_ge.trans hx.le
  have h2 : 0 < 2 + x := by linarith
  obtain ⟨a1, a2⟩ := airyAi_envelope_real hx1
  obtain ⟨b1, b2⟩ := airyBi_envelope_real hx1
  rw [airyOlverE_sq hx]
  have hA := airyAi_pos_of_gt hx
  have hB := airyBi_pos_of_gt hx
  have hq : 0 < (2 + x) ^ (-(1 / 4) : ℝ) := Real.rpow_pos_of_pos h2 _
  have e1 := Real.exp_pos (-airyXi x)
  have e2 := Real.exp_pos (airyXi x)
  have hexp : Real.exp (2 * airyXi x) * Real.exp (-airyXi x) = Real.exp (airyXi x) := by
    rw [← Real.exp_add]; congr 1; ring
  have hexp' : Real.exp (2 * airyXi x) * Real.exp (-airyXi x) * Real.exp (-airyXi x) = 1 := by
    rw [hexp, ← Real.exp_add]; simp
  constructor
  · rw [le_div_iff₀ hA]
    have : 1 / 3200 * Real.exp (2 * airyXi x) * airyAi x ≤ 1 / 3200 * Real.exp (2 * airyXi x) *
        (4 * (2 + x) ^ (-(1 / 4) : ℝ) * Real.exp (-airyXi x)) :=
      mul_le_mul_of_nonneg_left a2 (by positivity)
    have h3 : 1 / 3200 * Real.exp (2 * airyXi x) * (4 * (2 + x) ^ (-(1 / 4) : ℝ) * Real.exp (-airyXi x)) =
        1 / 800 * ((2 + x) ^ (-(1 / 4) : ℝ) * Real.exp (airyXi x)) := by
      rw [← hexp]; ring
    linarith
  · rw [div_le_iff₀ hA]
    have : 320 * Real.exp (2 * airyXi x) * (1 / 20 * (2 + x) ^ (-(1 / 4) : ℝ) * Real.exp (-airyXi x)) ≤
        320 * Real.exp (2 * airyXi x) * airyAi x := mul_le_mul_of_nonneg_left a1 (by positivity)
    have h3 : 320 * Real.exp (2 * airyXi x) * (1 / 20 * (2 + x) ^ (-(1 / 4) : ℝ) * Real.exp (-airyXi x)) =
        16 * ((2 + x) ^ (-(1 / 4) : ℝ) * Real.exp (airyXi x)) := by
      rw [← hexp]; ring
    linarith

/-- **`E(x)² = Bi/Ai` and `2 e^{(4/3) x^{3/2}} Ai/Bi = 1 + O(x^{-3/2})`**: for `x ≥ 2`,
`|2 e^{(4/3) x^{3/2}} Ai(x)/Bi(x) - 1| ≤ 4 x^{-3/2}` (so `Ai/Bi ≈ e^{-2ξ}/2`, `E^{-2} ≈ e^{-2ξ}/2`).
Numerically the left side is `≤ 0.08 x^{-3/2}`-sized for `x ≥ 2` (ratio `0.92` at `x = 2`). -/
theorem airyAi_div_airyBi_asymptotic {x : ℝ} (hx : 2 ≤ x) :
    |2 * Real.exp (4 / 3 * x ^ (3 / 2 : ℝ)) * (airyAi x / airyBi x) - 1| ≤ 4 * x ^ (-(3 / 2) : ℝ) := by
  have hx0 : 0 < x := by linarith
  set ξ := 2 / 3 * x ^ (3 / 2 : ℝ) with hξ
  set U := x ^ (-(1 / 4) : ℝ) * Real.exp ξ with hU
  have hq : 0 < x ^ (-(1 / 4) : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hUp : 0 < U := by positivity
  obtain ⟨hBl, -⟩ := airyBi_large_bounds hx
  have hBpos : 0 < airyBi x := by nlinarith
  have hTA := airyAi_sub_leading_le hx0
  have hTB := airyBi_pos_asymptotic hx0
  set r := x ^ (-(3 / 2) : ℝ) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos hx0 _
  have hrx : 5 / 48 / x ^ (3 / 2 : ℝ) = 5 / 48 * r := by
    rw [hr, Real.rpow_neg hx0.le]; ring
  rw [hrx] at hTA
  have h74 : x ^ (-(7 / 4) : ℝ) = x ^ (-(1 / 4) : ℝ) * r := by
    rw [hr, ← Real.rpow_add hx0]; norm_num
  -- notation
  set PA := 1 / (2 * √π) * x ^ (-(1 / 4) : ℝ) * Real.exp (-(2 / 3) * x ^ (3 / 2 : ℝ)) with hPA
  have hT : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  have hexp : Real.exp (4 / 3 * x ^ (3 / 2 : ℝ)) * Real.exp (-(2 / 3) * x ^ (3 / 2 : ℝ)) =
      Real.exp ξ := by
    rw [← Real.exp_add, hξ]; congr 1; ring
  -- `2 e^{2ξ} PA = U/√π`
  have hPA' : 2 * Real.exp (4 / 3 * x ^ (3 / 2 : ℝ)) * PA = 1 / √π * U := by
    rw [hPA, hU]
    have : 2 * Real.exp (4 / 3 * x ^ (3 / 2 : ℝ)) * (1 / (2 * √π) * x ^ (-(1 / 4) : ℝ) *
        Real.exp (-(2 / 3) * x ^ (3 / 2 : ℝ))) =
        1 / √π * x ^ (-(1 / 4) : ℝ) * (Real.exp (4 / 3 * x ^ (3 / 2 : ℝ)) *
        Real.exp (-(2 / 3) * x ^ (3 / 2 : ℝ))) := by field_simp
    rw [this, hexp]; ring
  set K := Real.exp (4 / 3 * x ^ (3 / 2 : ℝ)) with hK
  have hKp : 0 < K := Real.exp_pos _
  have hr3 : r ≤ 0.36 := by
    rw [hr, Real.rpow_neg hx0.le]
    have hs : 1.41 ≤ √x := by rw [Real.le_sqrt' (by norm_num)]; nlinarith
    have : x ^ (3 / 2 : ℝ) ≥ 2.8 := by
      rw [← sqrt_cube_eq_rpow hx0]
      nlinarith [Real.sqrt_nonneg x, mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg x)]
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    linarith
  -- numerator
  have hnum : |2 * K * airyAi x - airyBi x| ≤ 0.86 * r * U := by
    have e : 2 * K * airyAi x - airyBi x = 2 * K * (airyAi x - PA) -
        (airyBi x - 1 / √π * x ^ (-(1 / 4) : ℝ) * Real.exp ξ) := by
      have : 2 * K * PA = 1 / √π * x ^ (-(1 / 4) : ℝ) * Real.exp ξ := by
        rw [hPA', hU]; ring
      linear_combination this
    rw [e]
    refine (abs_sub _ _).trans ?_
    have hA' : |2 * K * (airyAi x - PA)| ≤ 2 * K * (5 / 48 * r * PA) := by
      rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * K)]
      exact mul_le_mul_of_nonneg_left hTA (by positivity)
    have hA'' : 2 * K * (5 / 48 * r * PA) = 5 / 48 * r * (1 / √π * U) := by
      rw [← hPA']; ring
    have hT1 := sqrt_pi_bounds.1
    have hinv : 1 / √π ≤ 0.57 := by
      rw [div_le_iff₀ hT]; nlinarith
    have hB' : |airyBi x - 1 / √π * x ^ (-(1 / 4) : ℝ) * Real.exp ξ| ≤ 4 / 5 * (r * U) := by
      have := hTB
      rw [← hξ] at this
      refine this.trans (le_of_eq ?_)
      rw [h74, hU]; ring
    have h5 : 5 / 48 * r * (1 / √π * U) ≤ 5 / 48 * r * (0.57 * U) := by gcongr
    nlinarith [mul_pos hr0 hUp]
  rw [← hξ] at hBl
  have hq' : |2 * K * (airyAi x / airyBi x) - 1| = |2 * K * airyAi x - airyBi x| / airyBi x := by
    have : 2 * K * (airyAi x / airyBi x) - 1 = (2 * K * airyAi x - airyBi x) / airyBi x := by
      field_simp
    rw [this, abs_div, abs_of_pos hBpos]
  rw [hq', div_le_iff₀ hBpos]
  have : 0.86 * r * U ≤ 4 * r * (0.27 * U) := by nlinarith [mul_pos hr0 hUp]
  have h6 : 4 * r * (0.27 * U) ≤ 4 * r * airyBi x := by
    have := hBl
    rw [← hU] at this
    exact mul_le_mul_of_nonneg_left this (by positivity)
  linarith


/-! ### Two-sided bounds for `M²` -/

lemma airyOlverM_sq_of_le {x : ℝ} (hx : x ≤ airyCross) : airyOlverM x ^ 2 = airyModSq x := by
  rw [airyOlverM_of_le hx, Real.sq_sqrt]
  unfold airyModSq; positivity

lemma airyOlverM_sq_of_gt {x : ℝ} (hx : airyCross < x) : airyOlverM x ^ 2 = 2 * airyAi x * airyBi x := by
  rw [airyOlverM_of_gt hx, Real.sq_sqrt]
  have := airyAi_pos_of_gt hx
  have := airyBi_pos_of_gt hx
  positivity

lemma airyOlverM_nonneg (x : ℝ) : 0 ≤ airyOlverM x := by
  by_cases hc : x ≤ airyCross
  · rw [airyOlverM_of_le hc]; exact Real.sqrt_nonneg _
  · rw [airyOlverM_of_gt (not_le.mp hc)]; exact Real.sqrt_nonneg _

/-- `N² ≤ 2 √y` for `x = -y`, `y ≥ 1`. -/
lemma airyModDerivSq_neg_le {y : ℝ} (hy : 1 ≤ y) : airyModDerivSq (-y) ≤ 2 * √y := by
  have hy0 : 0 < y := by linarith
  have h1 := airyAi'_neg_asymptotic hy0
  have h2 := airyBiDeriv_neg_asymptotic hy0
  have hq : y ^ (1 / 4 : ℝ) ≥ 1 := Real.one_le_rpow hy (by norm_num)
  have hq2 : y ^ (-(5 / 4) : ℝ) ≤ y ^ (1 / 4 : ℝ) := by
    refine (Real.rpow_le_rpow_of_exponent_le hy (by norm_num : (-(5 / 4) : ℝ) ≤ 1 / 4))
  have hT := sqrt_pi_bounds.1
  have hinv : 1 / √π ≤ 0.57 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hsq : (y ^ (1 / 4 : ℝ)) ^ 2 = √y := by
    rw [← sqrt_sqrt_eq_rpow hy0, Real.sq_sqrt (Real.sqrt_nonneg _)]
  set u := y ^ (1 / 4 : ℝ) with hu
  have hu0 : 0 < u := by linarith
  have hS : |1 / √π * u * Real.sin (2 / 3 * y ^ (3 / 2 : ℝ) - π / 4)| ≤ 0.57 * u := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < 1 / √π * u)]
    calc 1 / √π * u * |Real.sin _| ≤ 1 / √π * u * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (by positivity)
      _ ≤ 0.57 * u := by nlinarith
  have hC : |1 / √π * u * Real.cos (2 / 3 * y ^ (3 / 2 : ℝ) - π / 4)| ≤ 0.57 * u := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < 1 / √π * u)]
    calc 1 / √π * u * |Real.cos _| ≤ 1 / √π * u * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (by positivity)
      _ ≤ 0.57 * u := by nlinarith
  have hA : |airyAi' (-y)| ≤ 0.97 * u := by
    have := abs_sub_abs_le_abs_sub (airyAi' (-y)) (1 / √π * u * Real.sin (2 / 3 * y ^ (3 / 2 : ℝ) - π / 4))
    have h1' : |airyAi' (-y) - 1 / √π * u * Real.sin (2 / 3 * y ^ (3 / 2 : ℝ) - π / 4)| ≤ 0.4 * u := by
      refine h1.trans ?_
      nlinarith
    linarith
  have hB : |airyBiDeriv (-y)| ≤ 0.97 * u := by
    have := abs_sub_abs_le_abs_sub (airyBiDeriv (-y)) (1 / √π * u * Real.cos (2 / 3 * y ^ (3 / 2 : ℝ) - π / 4))
    have h2' : |airyBiDeriv (-y) - 1 / √π * u * Real.cos (2 / 3 * y ^ (3 / 2 : ℝ) - π / 4)| ≤ 0.4 * u := by
      refine h2.trans ?_
      nlinarith
    linarith
  unfold airyModDerivSq
  have a1 : airyAi' (-y) ^ 2 ≤ (0.97 * u) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hA 2
  have b1 : airyBiDeriv (-y) ^ 2 ≤ (0.97 * u) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hB 2
  nlinarith


/-- **`M²` on the oscillatory side**: for `y ≥ 1`, `(1/20)/√y ≤ M(-y)² ≤ (3/4)/√y` (numerically `M² √y ∈ [0.2976, 0.3183]`,
the limit being `1/π`). -/
theorem airyOlverM_sq_neg_bounds {y : ℝ} (hy : 1 ≤ y) :
    1 / 20 * (1 / √y) ≤ airyOlverM (-y) ^ 2 ∧ airyOlverM (-y) ^ 2 ≤ 3 / 4 * (1 / √y) := by
  have hy0 : 0 < y := by linarith
  have hc : -y ≤ airyCross := by linarith [airyCross_ge]
  rw [airyOlverM_sq_of_le hc]
  have hs : 0 < √y := Real.sqrt_pos.mpr hy0
  have hs1 : 1 ≤ √y := by rw [Real.one_le_sqrt]; exact hy
  constructor
  · have h := one_div_pi_sq_le_airyModSq_mul (-y)
    have hN := airyModDerivSq_neg_le hy
    have hM := airyModSq_pos (-y)
    have hp : π ^ 2 ≤ 9.87 := by
      have := Real.pi_lt_d4
      nlinarith [Real.pi_pos]
    have h1 : 1 / 9.87 ≤ 1 / π ^ 2 := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith
    have h2 : 1 / 9.87 ≤ airyModSq (-y) * (2 * √y) :=
      h1.trans (h.trans (mul_le_mul_of_nonneg_left hN hM.le))
    rw [← sub_nonneg]
    have e : airyModSq (-y) - 1 / 20 * (1 / √y) = (airyModSq (-y) * (20 * √y) - 1) / (20 * √y) := by
      field_simp
    rw [e]
    apply div_nonneg
    · nlinarith
    · positivity
  · have h := airyAi_sq_add_airyBi_sq_neg hy
    rw [abs_le] at h
    have hπ : 1 / π ≤ 0.3184 := by
      rw [div_le_iff₀ Real.pi_pos]; have := Real.pi_gt_d4; nlinarith
    have e : 1 / (π * √y) = 1 / π * (1 / √y) := by field_simp
    have hy2 : 2 / 5 / y ^ 2 ≤ 2 / 5 * (1 / √y) := by
      have h4 : y ^ 2 = (√y) ^ 4 := by
        rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hy0.le]
      have hsy : √y ≤ y ^ 2 := by
        rw [h4]; exact le_self_pow₀ hs1 (by norm_num)
      have := one_div_le_one_div_of_le hs hsy
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left this (by norm_num)
    have hs' : 1 / √y > 0 := by positivity
    unfold airyModSq
    nlinarith [mul_le_mul_of_nonneg_right hπ hs'.le]


lemma rpow_neg_half_eq {t : ℝ} (ht : 0 < t) : t ^ (-(1 / 2) : ℝ) = 1 / √t := by
  rw [Real.rpow_neg ht.le, Real.sqrt_eq_rpow]; simp

lemma airyXi_of_nonpos {x : ℝ} (hx : x ≤ 0) : airyXi x = 0 := by
  unfold airyXi; rw [max_eq_right hx]; simp

/-- **`M²` on `x ≥ -1`**: `(1/8000)/√(2+x) ≤ M(x)² ≤ 272/√(2+x)`. -/
theorem airyOlverM_sq_pos_bounds {x : ℝ} (hx : -1 ≤ x) :
    1 / 8000 * (1 / √(2 + x)) ≤ airyOlverM x ^ 2 ∧ airyOlverM x ^ 2 ≤ 272 * (1 / √(2 + x)) := by
  have h2 : 0 < 2 + x := by linarith
  rw [← rpow_neg_half_eq h2]
  by_cases hc : x ≤ airyCross
  · rw [airyOlverM_sq_of_le hc]
    have hx0 : x ≤ 0 := hc.trans airyCross_le_zero
    obtain ⟨a1, a2⟩ := airyAi_envelope_real hx
    obtain ⟨b1, b2⟩ := airyBi_envelope_real hx
    simp only [airyXi_of_nonpos hx0, neg_zero, Real.exp_zero, mul_one] at a1 a2 b2
    have hh : (2 + x) ^ (-(1 / 4) : ℝ) * (2 + x) ^ (-(1 / 4) : ℝ) = (2 + x) ^ (-(1 / 2) : ℝ) := by
      rw [← Real.rpow_add h2]; norm_num
    have hq : 0 < (2 + x) ^ (-(1 / 4) : ℝ) := Real.rpow_pos_of_pos h2 _
    have hA := airyAi_pos_of_neg_one_le hx
    have hB := airyBi_pos_of_neg_eleven_tenth_le (show -(11 / 10 : ℝ) ≤ x by linarith)
    unfold airyModSq
    constructor
    · nlinarith [mul_self_le_mul_self (by positivity : 0 ≤ 1 / 20 * (2 + x) ^ (-(1 / 4) : ℝ)) a1,
        sq_nonneg (airyBi x)]
    · nlinarith [mul_self_le_mul_self hA.le a2, mul_self_le_mul_self hB.le b2]
  · rw [not_le] at hc
    rw [airyOlverM_sq_of_gt hc]
    obtain ⟨p1, p2⟩ := airyAi_mul_airyBi_envelope hx
    constructor <;> nlinarith


lemma sqrt_two_add_abs_le {x : ℝ} (hx : -1 ≤ x) : √(2 + |x|) ≤ 2 * √(2 + x) := by
  have h2 : 0 < 2 + x := by linarith
  have h : 2 + |x| ≤ 3 * (2 + x) := by
    rcases le_or_gt 0 x with h | h
    · rw [abs_of_nonneg h]; linarith
    · rw [abs_of_neg h]; linarith
  have : √(2 + |x|) ≤ √(3 * (2 + x)) := Real.sqrt_le_sqrt h
  rw [Real.sqrt_mul (by norm_num)] at this
  have h3 : √(3 : ℝ) ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have := Real.sqrt_nonneg (2 + x)
  nlinarith

/-- **`M²` two-sided on all of `ℝ`**: `(1/8000)/√(2+|x|) ≤ M(x)² ≤ 600/√(2+|x|)`, where `M` is Olver's `M`
(equal to the DLMF modulus for `x ≤ airyCross`, `(2AiBi)^{1/2}` for `x > airyCross`). -/
theorem airyOlverM_sq_two_sided (x : ℝ) :
    1 / 8000 * (1 / √(2 + |x|)) ≤ airyOlverM x ^ 2 ∧ airyOlverM x ^ 2 ≤ 600 * (1 / √(2 + |x|)) := by
  have hw : 0 < √(2 + |x|) := Real.sqrt_pos.mpr (by positivity)
  rcases le_or_gt (-1) x with hx | hx
  · obtain ⟨l, u⟩ := airyOlverM_sq_pos_bounds hx
    have h2 : 0 < 2 + x := by linarith
    have hv : 0 < √(2 + x) := Real.sqrt_pos.mpr h2
    have hle : √(2 + x) ≤ √(2 + |x|) := Real.sqrt_le_sqrt (by linarith [le_abs_self x])
    have h1 : 1 / √(2 + |x|) ≤ 1 / √(2 + x) := one_div_le_one_div_of_le hv hle
    have h3 : 1 / √(2 + x) ≤ 2 * (1 / √(2 + |x|)) := by
      have := sqrt_two_add_abs_le hx
      rw [mul_one_div, div_le_div_iff₀ hv hw]
      linarith
    constructor <;> nlinarith
  · set y := -x with hy
    have hy1 : 1 ≤ y := by linarith
    have hxy : x = -y := by linarith
    have hab : |x| = y := by rw [hxy, abs_neg, abs_of_pos (by linarith)]
    rw [hab, hxy]
    obtain ⟨l, u⟩ := airyOlverM_sq_neg_bounds hy1
    have hs : 0 < √y := Real.sqrt_pos.mpr (by linarith)
    have hle : √y ≤ √(2 + y) := Real.sqrt_le_sqrt (by linarith)
    have hw' : 0 < √(2 + y) := Real.sqrt_pos.mpr (by linarith)
    have h1 : 1 / √(2 + y) ≤ 1 / √y := one_div_le_one_div_of_le hs hle
    have h3 : 1 / √y ≤ 2 * (1 / √(2 + y)) := by
      have h : √(2 + y) ≤ 2 * √y :=
        Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith [Real.sq_sqrt (show 0 ≤ y by linarith)]⟩
      rw [mul_one_div, div_le_div_iff₀ hs hw']
      linarith
    constructor <;> nlinarith

/-! ### The derivative weight `N` -/

lemma sqrt_two_add_eq {x : ℝ} : (2 + x) ^ (1 / 2 : ℝ) = √(2 + x) := (Real.sqrt_eq_rpow _).symm

/-- `N ≤ 5300 (2+x)^{1/2} M` on `[-1, ∞)` (the constant is that of `airyBiDeriv_le_mul_airyBi`). -/
theorem airyDerivWeightN_le_of_neg_one_le {x : ℝ} (hx : -1 ≤ x) :
    airyDerivWeightN x ≤ 5300 * √(2 + x) * airyOlverM x := by
  have h2 : 0 < 2 + x := by linarith
  have hs : 0 < √(2 + x) := Real.sqrt_pos.mpr h2
  have hD := abs_airyAi'_le_mul_airyAi hx
  have hB := airyBiDeriv_le_mul_airyBi hx
  rw [sqrt_two_add_eq] at hD hB
  have hA := airyAi_pos_of_neg_one_le hx
  have hBp := airyBi_pos_of_neg_eleven_tenth_le (show -(11 / 10 : ℝ) ≤ x by linarith)
  have hBd := airyBiDeriv_pos_of_ge (show -(11 / 10 : ℝ) ≤ x by linarith)
  have hM0 : 0 ≤ airyOlverM x := airyOlverM_nonneg x
  by_cases hc : x ≤ airyCross
  · simp only [airyDerivWeightN, hc, ite_true]
    rw [airyOlverM_of_le hc]
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    rw [mul_pow, mul_pow, Real.sq_sqrt h2.le, Real.sq_sqrt (airyModSq_pos x).le]
    unfold airyModSq airyModDerivSq
    have e1 : airyAi' x ^ 2 ≤ (120 * √(2 + x) * airyAi x) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hD 2
    have e2 : airyBiDeriv x ^ 2 ≤ (5300 * √(2 + x) * airyBi x) ^ 2 :=
      pow_le_pow_left₀ hBd.le hB 2
    rw [mul_pow, mul_pow, Real.sq_sqrt h2.le] at e1 e2
    nlinarith [sq_nonneg (airyAi x), sq_nonneg (airyBi x)]
  · rw [not_le] at hc
    simp only [airyDerivWeightN, not_le.mpr hc, ite_false]
    have hE := airyOlverE_pos x
    have hMe := airyOlverM_eq hc
    have h1 : (1 : ℝ) ≤ √2 := by rw [Real.le_sqrt' (by norm_num)]; norm_num
    have hEA : airyOlverE x * airyAi x ≤ airyOlverM x := by
      rw [hMe]; nlinarith [mul_pos hE hA]
    have hMB := airyOlverM_mul_E hc
    have hBE : airyBi x / airyOlverE x ≤ airyOlverM x := by
      rw [div_le_iff₀ hE]; nlinarith [mul_pos hBp hE]
    refine max_le ?_ ?_
    · calc airyOlverE x * |airyAi' x| ≤ airyOlverE x * (120 * √(2 + x) * airyAi x) :=
            mul_le_mul_of_nonneg_left hD hE.le
        _ = 120 * √(2 + x) * (airyOlverE x * airyAi x) := by ring
        _ ≤ 5300 * √(2 + x) * airyOlverM x := by nlinarith [mul_nonneg hs.le hM0]
    · rw [abs_of_pos hBd]
      calc airyBiDeriv x / airyOlverE x ≤ 5300 * √(2 + x) * airyBi x / airyOlverE x :=
            div_le_div_of_nonneg_right hB hE.le
        _ = 5300 * √(2 + x) * (airyBi x / airyOlverE x) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hBE (by positivity)

/-- **`N ≤ 5300 (2+|x|)^{1/2} M` on all of `ℝ`** (for `x < -1` from `N² ≤ 2√|x|` and `M² ≥ (1/8000)/√(2+|x|)`). -/
theorem airyDerivWeightN_le (x : ℝ) : airyDerivWeightN x ≤ 5300 * √(2 + |x|) * airyOlverM x := by
  rcases le_or_gt (-1) x with hx | hx
  · refine (airyDerivWeightN_le_of_neg_one_le hx).trans ?_
    have hM0 : 0 ≤ airyOlverM x := airyOlverM_nonneg x
    have hle : √(2 + x) ≤ √(2 + |x|) := Real.sqrt_le_sqrt (by linarith [le_abs_self x])
    nlinarith [mul_nonneg hM0 (sub_nonneg.mpr hle)]
  · have hc : x ≤ airyCross := by linarith [airyCross_ge]
    set y := -x with hy
    have hy1 : 1 ≤ y := by linarith
    have hxy : x = -y := by linarith
    have hab : |x| = y := by rw [hxy, abs_neg, abs_of_pos (by linarith)]
    rw [hab]
    have hl := (airyOlverM_sq_two_sided x).1
    rw [hab] at hl
    have hN := airyModDerivSq_neg_le hy1
    rw [← hxy] at hN
    have ht : 0 < √(2 + y) := Real.sqrt_pos.mpr (by linarith)
    have ht2 : √(2 + y) ^ 2 = 2 + y := Real.sq_sqrt (by linarith)
    have hsy : √y ≤ √(2 + y) := Real.sqrt_le_sqrt (by linarith)
    have hM0 : 0 ≤ airyOlverM x := airyOlverM_nonneg x
    have key : √(2 + y) / 8000 ≤ √(2 + y) ^ 2 * airyOlverM x ^ 2 := by
      have := mul_le_mul_of_nonneg_left hl (sq_nonneg (√(2 + y)))
      refine le_trans (le_of_eq ?_) this
      field_simp
    simp only [airyDerivWeightN, hc, ite_true]
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    rw [mul_pow, mul_pow]
    nlinarith

/-- **`(M/E)²` on `x > airyCross`** (`M/E = √2 Ai`): `(1/200) e^{-2ξ}/√(2+x) ≤ (M/E)² ≤ 32 e^{-2ξ}/√(2+x)`. -/
theorem airyOlverM_div_E_sq_bounds {x : ℝ} (hc : airyCross < x) :
    1 / 200 * ((2 + x) ^ (-(1 / 2) : ℝ) * Real.exp (-(2 * airyXi x))) ≤ (airyOlverM x / airyOlverE x) ^ 2 ∧
      (airyOlverM x / airyOlverE x) ^ 2 ≤ 32 * ((2 + x) ^ (-(1 / 2) : ℝ) * Real.exp (-(2 * airyXi x))) := by
  have hx : -1 ≤ x := airyCross_ge.trans hc.le
  have h2 : 0 < 2 + x := by linarith
  obtain ⟨a1, a2⟩ := airyAi_envelope_real hx
  have hh : (2 + x) ^ (-(1 / 4) : ℝ) * (2 + x) ^ (-(1 / 4) : ℝ) = (2 + x) ^ (-(1 / 2) : ℝ) := by
    rw [← Real.rpow_add h2]; norm_num
  have he : Real.exp (-airyXi x) * Real.exp (-airyXi x) = Real.exp (-(2 * airyXi x)) := by
    rw [← Real.exp_add]; ring_nf
  have hq : 0 < (2 + x) ^ (-(1 / 4) : ℝ) := Real.rpow_pos_of_pos h2 _
  have hA := airyAi_pos_of_gt hc
  rw [airyOlverM_div_E hc, mul_pow, Real.sq_sqrt (by norm_num)]
  have s1 := mul_self_le_mul_self (by positivity : 0 ≤ 1 / 20 * (2 + x) ^ (-(1 / 4) : ℝ) *
    Real.exp (-airyXi x)) a1
  have s2 := mul_self_le_mul_self hA.le a2
  have e1 : 1 / 20 * (2 + x) ^ (-(1 / 4) : ℝ) * Real.exp (-airyXi x) *
      (1 / 20 * (2 + x) ^ (-(1 / 4) : ℝ) * Real.exp (-airyXi x)) =
      1 / 400 * ((2 + x) ^ (-(1 / 2) : ℝ) * Real.exp (-(2 * airyXi x))) := by
    rw [← hh, ← he]; ring
  have e2 : 4 * (2 + x) ^ (-(1 / 4) : ℝ) * Real.exp (-airyXi x) *
      (4 * (2 + x) ^ (-(1 / 4) : ℝ) * Real.exp (-airyXi x)) =
      16 * ((2 + x) ^ (-(1 / 2) : ℝ) * Real.exp (-(2 * airyXi x))) := by
    rw [← hh, ← he]; ring
  rw [e1] at s1
  rw [e2] at s2
  constructor <;> nlinarith

/-- **`(M E)²` on `x > airyCross`** (`M E = √2 Bi`): `e^{2ξ}/(320000 √(2+x)) ≤ (M E)² ≤ 512 e^{2ξ}/√(2+x)`. -/
theorem airyOlverM_mul_E_sq_bounds {x : ℝ} (hc : airyCross < x) :
    1 / 320000 * ((2 + x) ^ (-(1 / 2) : ℝ) * Real.exp (2 * airyXi x)) ≤ (airyOlverM x * airyOlverE x) ^ 2 ∧
      (airyOlverM x * airyOlverE x) ^ 2 ≤ 512 * ((2 + x) ^ (-(1 / 2) : ℝ) * Real.exp (2 * airyXi x)) := by
  have hx : -1 ≤ x := airyCross_ge.trans hc.le
  have h2 : 0 < 2 + x := by linarith
  obtain ⟨b1, b2⟩ := airyBi_envelope_real hx
  have hh : (2 + x) ^ (-(1 / 4) : ℝ) * (2 + x) ^ (-(1 / 4) : ℝ) = (2 + x) ^ (-(1 / 2) : ℝ) := by
    rw [← Real.rpow_add h2]; norm_num
  have he : Real.exp (airyXi x) * Real.exp (airyXi x) = Real.exp (2 * airyXi x) := by
    rw [← Real.exp_add]; ring_nf
  have hq : 0 < (2 + x) ^ (-(1 / 4) : ℝ) := Real.rpow_pos_of_pos h2 _
  have hB := airyBi_pos_of_gt hc
  rw [airyOlverM_mul_E hc, mul_pow, Real.sq_sqrt (by norm_num)]
  have s1 := mul_self_le_mul_self (by positivity : 0 ≤ 1 / 800 * ((2 + x) ^ (-(1 / 4) : ℝ) *
    Real.exp (airyXi x))) b1
  have s2 := mul_self_le_mul_self hB.le b2
  have e1 : 1 / 800 * ((2 + x) ^ (-(1 / 4) : ℝ) * Real.exp (airyXi x)) *
      (1 / 800 * ((2 + x) ^ (-(1 / 4) : ℝ) * Real.exp (airyXi x))) =
      1 / 640000 * ((2 + x) ^ (-(1 / 2) : ℝ) * Real.exp (2 * airyXi x)) := by
    rw [← hh, ← he]; ring
  have e2 : 16 * ((2 + x) ^ (-(1 / 4) : ℝ) * Real.exp (airyXi x)) *
      (16 * ((2 + x) ^ (-(1 / 4) : ℝ) * Real.exp (airyXi x))) =
      256 * ((2 + x) ^ (-(1 / 2) : ℝ) * Real.exp (2 * airyXi x)) := by
    rw [← hh, ← he]; ring
  rw [e1] at s1
  rw [e2] at s2
  constructor <;> nlinarith

/-- info: 'FormalResearch.Special.airyOlverE_sq_two_sided' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyOlverE_sq_two_sided

/-- info: 'FormalResearch.Special.airyAi_div_airyBi_asymptotic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAi_div_airyBi_asymptotic

/-- info: 'FormalResearch.Special.airyOlverM_sq_neg_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyOlverM_sq_neg_bounds

/-- info: 'FormalResearch.Special.airyOlverM_sq_pos_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyOlverM_sq_pos_bounds

/-- info: 'FormalResearch.Special.airyOlverM_sq_two_sided' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyOlverM_sq_two_sided

/-- info: 'FormalResearch.Special.airyDerivWeightN_le_of_neg_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyDerivWeightN_le_of_neg_one_le

/-- info: 'FormalResearch.Special.airyDerivWeightN_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyDerivWeightN_le

/-- info: 'FormalResearch.Special.airyOlverM_div_E_sq_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyOlverM_div_E_sq_bounds

/-- info: 'FormalResearch.Special.airyOlverM_mul_E_sq_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyOlverM_mul_E_sq_bounds

end FormalResearch.Special
