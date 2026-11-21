module

public import FormalResearch.CohnElkies.StieltjesMixture
public import FormalResearch.Special.AiryAsymNeg
public import Mathlib.Analysis.Calculus.Taylor

/-!
# Far-axis Airy cardinal asymptotics and exact cancellation formula (CR.3–CR.4)

Source: `CFT/sign_uncertainty/paper/ce_cardinal_resolvent.tex`:
* **Proposition CR.3** (`cecr:CR3`, equations `(CR.11)`, `(CR.12)`, `(CR.12a)`, `(CR.13)`):
  fixed-`q` far-axis asymptotic of `G_q(-x)` and the first-node subtraction `G_q(-x) - c_1² L_1(-x)²`,
  together with the small-`t` expansion `m(a_1 + t) = t⁻¹ + (a_1 / 3) t + O(t²)` and the limiting
  mismatch coefficient `(𝔞(q) - d⁻²) / q⁻¹ = 1 - a/d - 2/d³ + O(q⁻¹)`.
* **Theorem CR.4, Step 1** (equations `(CR.14a)` and `(CR.15)`):
  `D_t(u) = T(u) - G_{1/t}(u) = ∑_n (E_n / (E_n + t)) c_n² L_n(u)²`, and its exact three-Airy-function
  formula `D_t(-x) = A_t(x) Ai(-x)² + B_t(x) Ai(-x) Ai'(-x) + C_t(x) Ai'(-x)²`.
-/

@[expose] public section

open Filter Topology Set Asymptotics Real
open FormalResearch.Special

namespace FormalResearch.CohnElkies

/-! ### Negative-axis Airy WKB in the `ϑ(x) = (2/3) x^{3/2} + π/4` convention -/

/-- Phase `ϑ(x) = (2/3) x^{3/2} + π/4` from `ce_cardinal_resolvent.tex`. -/
noncomputable def cohnTheta (x : ℝ) : ℝ := 2 / 3 * x ^ (3 / 2 : ℝ) + π / 4

private lemma rpow_three_halves_eq_sqrt_cube {x : ℝ} (hx : 0 ≤ x) :
    x ^ (3 / 2 : ℝ) = (√x) ^ 3 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

private lemma rpow_quarter_eq_sqrt_sqrt {x : ℝ} (hx : 0 ≤ x) :
    x ^ (1 / 4 : ℝ) = √(√x) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
  norm_num

private lemma cos_sub_pi_div_four_eq_sin_theta {x : ℝ} (hx : 0 ≤ x) :
    Real.cos (2 / 3 * (√x) ^ 3 - π / 4) = Real.sin (cohnTheta x) := by
  unfold cohnTheta
  rw [rpow_three_halves_eq_sqrt_cube hx]
  rw [show 2 / 3 * √x ^ 3 - π / 4 = (2 / 3 * √x ^ 3 + π / 4) - π / 2 by ring,
    Real.cos_sub_pi_div_two]

private lemma sin_sub_pi_div_four_eq_neg_cos_theta {x : ℝ} (hx : 0 ≤ x) :
    Real.sin (2 / 3 * (√x) ^ 3 - π / 4) = -Real.cos (cohnTheta x) := by
  unfold cohnTheta
  rw [rpow_three_halves_eq_sqrt_cube hx]
  rw [show 2 / 3 * √x ^ 3 - π / 4 = (2 / 3 * √x ^ 3 + π / 4) - π / 2 by ring,
    Real.sin_sub_pi_div_two]

lemma airyAi_neg_asymptotic_theta {x : ℝ} (hx : 0 < x) :
    |airyAi (-x) - Real.sin (cohnTheta x) / (√π * x ^ (1 / 4 : ℝ))| ≤
      1 / (8 * x ^ (7 / 4 : ℝ)) := by
  have h := airyAi_neg_sq_asymptotic (Real.sqrt_pos.mpr hx)
  rw [Real.sq_sqrt hx.le, cos_sub_pi_div_four_eq_sin_theta hx.le,
    ← rpow_quarter_eq_sqrt_sqrt hx.le] at h
  have hpow : x ^ (1 / 4 : ℝ) * √x ^ 3 = x ^ (7 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx.le, ← Real.rpow_add hx]
    norm_num
  rw [hpow] at h
  exact h

lemma airyAi'_neg_asymptotic_theta {x : ℝ} (hx : 0 < x) :
    |airyAi' (-x) + x ^ (1 / 4 : ℝ) * Real.cos (cohnTheta x) / √π| ≤
      2 / (5 * x ^ (5 / 4 : ℝ)) := by
  have h := airyAi'_neg_sq_asymptotic (Real.sqrt_pos.mpr hx)
  rw [Real.sq_sqrt hx.le, sin_sub_pi_div_four_eq_neg_cos_theta hx.le,
    ← rpow_quarter_eq_sqrt_sqrt hx.le] at h
  have hpow : x ^ (1 / 4 : ℝ) * x = x ^ (5 / 4 : ℝ) := by
    conv_lhs => rhs; rw [← Real.rpow_one x]
    rw [← Real.rpow_add hx]
    norm_num
  rw [hpow, show airyAi' (-x) - x ^ (1 / 4 : ℝ) * (-Real.cos (cohnTheta x)) / √π =
      airyAi' (-x) + x ^ (1 / 4 : ℝ) * Real.cos (cohnTheta x) / √π by ring] at h
  exact h

private lemma isBigO_rpow_inv {f : ℝ → ℝ} {p : ℝ}
    (h : ∃ C ≥ 0, ∀ᶠ x in atTop, |f x| ≤ C * x ^ p) :
    f =O[atTop] (fun x : ℝ => x ^ p) := by
  obtain ⟨C, hC, hft⟩ := h
  refine IsBigO.of_bound C ?_
  filter_upwards [hft, eventually_gt_atTop (0 : ℝ)] with x hx hxpos
  rwa [Real.norm_eq_abs, Real.norm_of_nonneg (Real.rpow_nonneg hxpos.le _)]

lemma airyAi_neg_sq_isBigO :
    (fun x : ℝ => airyAi (-x) ^ 2 - Real.sin (cohnTheta x) ^ 2 / (π * x ^ (1 / 2 : ℝ))) =O[atTop]
      (fun x : ℝ => x ^ (-2 : ℝ)) := by
  refine isBigO_rpow_inv ⟨1 / 2, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  have hAi := airyAi_neg_asymptotic_theta hx0
  set L : ℝ := Real.sin (cohnTheta x) / (√π * x ^ (1 / 4 : ℝ))
  have hL : |L| ≤ 1 / (√π * x ^ (1 / 4 : ℝ)) := by
    dsimp [L]
    rw [abs_div, abs_of_pos (mul_pos (Real.sqrt_pos.mpr Real.pi_pos) (Real.rpow_pos_of_pos hx0 _))]
    exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (by positivity)
  have hsum : |airyAi (-x) + L| ≤ 2 * (1 / (√π * x ^ (1 / 4 : ℝ))) + 1 / (8 * x ^ (7 / 4 : ℝ)) := by
    have h1 : |airyAi (-x) + L| ≤ |airyAi (-x) - L| + 2 * |L| := by
      have := abs_add_le (airyAi (-x) - L) (2 * L)
      simpa [show airyAi (-x) - L + 2 * L = airyAi (-x) + L by ring, abs_mul] using this
    linarith
  have hpi : (1 : ℝ) ≤ √π := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
  have hx14 : 1 ≤ x ^ (1 / 4 : ℝ) := Real.one_le_rpow hx (by norm_num)
  have hx74 : x ^ (1 / 4 : ℝ) ≤ x ^ (7 / 4 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have herr : 2 * (1 / (√π * x ^ (1 / 4 : ℝ))) + 1 / (8 * x ^ (7 / 4 : ℝ)) ≤ 4 * x ^ (-1 / 4 : ℝ) := by
    have hx14pos : 0 < x ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hx0 (1 / 4 : ℝ)
    have h1 : 1 / (√π * x ^ (1 / 4 : ℝ)) ≤ (x ^ (1 / 4 : ℝ))⁻¹ := by
      rw [one_div]
      exact inv_anti₀ hx14pos (le_mul_of_one_le_left hx14pos.le hpi)
    have h2 : 1 / (8 * x ^ (7 / 4 : ℝ)) ≤ (x ^ (1 / 4 : ℝ))⁻¹ := by
      rw [one_div]
      exact inv_anti₀ hx14pos (by nlinarith [hx74, hx14pos])
    have heq : x ^ (-1 / 4 : ℝ) = (x ^ (1 / 4 : ℝ))⁻¹ := by
      rw [show (-1 / 4 : ℝ) = -(1 / 4 : ℝ) by norm_num, Real.rpow_neg hx0.le]
    have hx14pos' : 0 ≤ (x ^ (1 / 4 : ℝ))⁻¹ := by positivity
    rw [heq]
    linarith
  have hLsq : L ^ 2 = Real.sin (cohnTheta x) ^ 2 / (π * x ^ (1 / 2 : ℝ)) := by
    dsimp [L]
    have hx12 : (x ^ (1 / 4 : ℝ)) ^ 2 = x ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
    rw [div_pow, mul_pow, Real.sq_sqrt Real.pi_pos.le, hx12]
  rw [← hLsq, show airyAi (-x) ^ 2 - L ^ 2 = (airyAi (-x) - L) * (airyAi (-x) + L) by ring, abs_mul]
  have hcomb : (1 / (8 * x ^ (7 / 4 : ℝ))) * (4 * x ^ (-1 / 4 : ℝ)) = 1 / 2 * x ^ (-2 : ℝ) := by
    rw [Real.rpow_neg hx0.le]
    have hx74' : (x ^ (7 / 4 : ℝ))⁻¹ * x ^ (-1 / 4 : ℝ) = (x ^ (2 : ℝ))⁻¹ := by
      rw [← Real.rpow_neg hx0.le, ← Real.rpow_neg hx0.le, ← Real.rpow_add hx0]; norm_num
    calc (1 / (8 * x ^ (7 / 4 : ℝ))) * (4 * x ^ (-1 / 4 : ℝ))
        = (1 / 2) * ((x ^ (7 / 4 : ℝ))⁻¹ * x ^ (-1 / 4 : ℝ)) := by ring
      _ = (1 / 2) * (x ^ (2 : ℝ))⁻¹ := by rw [hx74']
  calc |airyAi (-x) - L| * |airyAi (-x) + L|
      ≤ (1 / (8 * x ^ (7 / 4 : ℝ))) * (4 * x ^ (-1 / 4 : ℝ)) :=
        mul_le_mul hAi (hsum.trans herr) (abs_nonneg _) (by positivity)
    _ = 1 / 2 * x ^ (-2 : ℝ) := hcomb

lemma airyAi_mul_airyAi'_neg_isBigO :
    (fun x : ℝ => airyAi (-x) * airyAi' (-x)) =O[atTop] (fun _ : ℝ => (1 : ℝ)) := by
  refine IsBigO.of_bound 2 ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  have h1 := airyAi_neg_asymptotic_theta hx0
  have h2 := airyAi'_neg_asymptotic_theta hx0
  have hpi : (1 : ℝ) ≤ √π := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
  have hx14 : 1 ≤ x ^ (1 / 4 : ℝ) := Real.one_le_rpow hx (by norm_num)
  have hAi_bd : |airyAi (-x)| ≤ (1 + 1 / 8) * x ^ (-1 / 4 : ℝ) := by
    have hL : |Real.sin (cohnTheta x) / (√π * x ^ (1 / 4 : ℝ))| ≤ x ^ (-1 / 4 : ℝ) := by
      rw [abs_div, abs_of_pos (mul_pos (Real.sqrt_pos.mpr Real.pi_pos) (Real.rpow_pos_of_pos hx0 _))]
      calc |Real.sin (cohnTheta x)| / (√π * x ^ (1 / 4 : ℝ))
          ≤ 1 / (1 * x ^ (1 / 4 : ℝ)) :=
            div_le_div₀ (by positivity) (Real.abs_sin_le_one _) (by positivity)
              (mul_le_mul_of_nonneg_right hpi (by positivity))
        _ = x ^ (-1 / 4 : ℝ) := by
            rw [one_mul, show (-1 / 4 : ℝ) = -(1 / 4) by norm_num, Real.rpow_neg hx0.le, ← one_div]
    have hx74 : x ^ (-7 / 4 : ℝ) ≤ x ^ (-1 / 4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
    have htri' : |airyAi (-x)| ≤ |airyAi (-x) - Real.sin (cohnTheta x) / (√π * x ^ (1 / 4 : ℝ))| +
        |Real.sin (cohnTheta x) / (√π * x ^ (1 / 4 : ℝ))| := by
      have := abs_add_le (airyAi (-x) - Real.sin (cohnTheta x) / (√π * x ^ (1 / 4 : ℝ)))
        (Real.sin (cohnTheta x) / (√π * x ^ (1 / 4 : ℝ)))
      simpa using this
    have h74_eq : 1 / (8 * x ^ (7 / 4 : ℝ)) ≤ 1 / 8 * (x ^ (1 / 4 : ℝ))⁻¹ := by
      have h7 : x ^ (1 / 4 : ℝ) ≤ x ^ (7 / 4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
      have h7inv : (x ^ (7 / 4 : ℝ))⁻¹ ≤ (x ^ (1 / 4 : ℝ))⁻¹ :=
        inv_anti₀ (Real.rpow_pos_of_pos hx0 _) h7
      rw [show 1 / (8 * x ^ (7 / 4 : ℝ)) = 1 / 8 * (x ^ (7 / 4 : ℝ))⁻¹ by ring]
      gcongr
    have htri'' : |airyAi (-x)| ≤ 1 / (8 * x ^ (7 / 4 : ℝ)) + x ^ (-1 / 4 : ℝ) := by linarith
    rw [show (-1 / 4 : ℝ) = -(1 / 4 : ℝ) by norm_num, Real.rpow_neg hx0.le] at htri'' ⊢
    linarith
  have hAi'_bd : |airyAi' (-x)| ≤ (1 + 2 / 5) * x ^ (1 / 4 : ℝ) := by
    have hL : |x ^ (1 / 4 : ℝ) * Real.cos (cohnTheta x) / √π| ≤ x ^ (1 / 4 : ℝ) := by
      rw [abs_div, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hx0 _), abs_of_pos (Real.sqrt_pos.mpr Real.pi_pos)]
      calc x ^ (1 / 4 : ℝ) * |Real.cos (cohnTheta x)| / √π
          ≤ x ^ (1 / 4 : ℝ) * 1 / 1 := div_le_div₀ (by positivity)
            (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (by positivity)) one_pos hpi
        _ = x ^ (1 / 4 : ℝ) := by ring
    have h5 : 2 / (5 * x ^ (5 / 4 : ℝ)) ≤ 2 / 5 * x ^ (1 / 4 : ℝ) := by
      have hx1 : 1 ≤ x ^ (5 / 4 : ℝ) := Real.one_le_rpow hx (by norm_num)
      have hxinv : (x ^ (5 / 4 : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hx1
      calc 2 / (5 * x ^ (5 / 4 : ℝ)) = 2 / 5 * (x ^ (5 / 4 : ℝ))⁻¹ := by ring
        _ ≤ 2 / 5 * 1 := by gcongr
        _ ≤ 2 / 5 * x ^ (1 / 4 : ℝ) := by gcongr
    have htri : |airyAi' (-x)| ≤ |airyAi' (-x) + x ^ (1 / 4 : ℝ) * Real.cos (cohnTheta x) / √π| +
        |x ^ (1 / 4 : ℝ) * Real.cos (cohnTheta x) / √π| := by
      have := abs_add_le (airyAi' (-x) + x ^ (1 / 4 : ℝ) * Real.cos (cohnTheta x) / √π)
        (-(x ^ (1 / 4 : ℝ) * Real.cos (cohnTheta x) / √π))
      simpa [abs_neg] using this
    linarith
  rw [Real.norm_eq_abs, abs_mul, norm_one, mul_one]
  have hprod : x ^ (-1 / 4 : ℝ) * x ^ (1 / 4 : ℝ) = 1 := by
    rw [← Real.rpow_add hx0]; norm_num
  calc |airyAi (-x)| * |airyAi' (-x)|
      ≤ ((1 + 1 / 8) * x ^ (-1 / 4 : ℝ)) * ((1 + 2 / 5) * x ^ (1 / 4 : ℝ)) :=
        mul_le_mul hAi_bd hAi'_bd (abs_nonneg _) (by positivity)
    _ = (1 + 1 / 8) * (1 + 2 / 5) * (x ^ (-1 / 4 : ℝ) * x ^ (1 / 4 : ℝ)) := by ring
    _ = (1 + 1 / 8) * (1 + 2 / 5) := by rw [hprod, mul_one]
    _ ≤ 2 := by norm_num

lemma airyAi'_neg_sq_isBigO :
    (fun x : ℝ => airyAi' (-x) ^ 2 - x ^ (1 / 2 : ℝ) * Real.cos (cohnTheta x) ^ 2 / π) =O[atTop]
      (fun x : ℝ => x ^ (-1 : ℝ)) := by
  refine isBigO_rpow_inv ⟨2, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  have h2 := airyAi'_neg_asymptotic_theta hx0
  set L : ℝ := -(x ^ (1 / 4 : ℝ) * Real.cos (cohnTheta x) / √π)
  have h2' : |airyAi' (-x) - L| ≤ 2 / (5 * x ^ (5 / 4 : ℝ)) := by simpa [L, sub_neg_eq_add] using h2
  have hpi : (1 : ℝ) ≤ √π := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
  have hx14 : 1 ≤ x ^ (1 / 4 : ℝ) := Real.one_le_rpow hx (by norm_num)
  have hL : |L| ≤ x ^ (1 / 4 : ℝ) := by
    dsimp [L]
    rw [abs_neg, abs_div, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hx0 _),
      abs_of_pos (Real.sqrt_pos.mpr Real.pi_pos)]
    calc x ^ (1 / 4 : ℝ) * |Real.cos (cohnTheta x)| / √π
        ≤ x ^ (1 / 4 : ℝ) * 1 / 1 := div_le_div₀ (by positivity)
          (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (by positivity)) one_pos hpi
      _ = x ^ (1 / 4 : ℝ) := by ring
  have herr : 2 / (5 * x ^ (5 / 4 : ℝ)) + 2 * x ^ (1 / 4 : ℝ) ≤ 3 * x ^ (1 / 4 : ℝ) := by
    have hx1 : 1 ≤ x ^ (5 / 4 : ℝ) := Real.one_le_rpow hx (by norm_num)
    have h1 : 2 / (5 * x ^ (5 / 4 : ℝ)) ≤ 1 := by
      have : 2 / 5 ≤ x ^ (5 / 4 : ℝ) := by linarith
      rw [div_le_one (by positivity)]; linarith
    linarith
  have hsum : |airyAi' (-x) + L| ≤ 3 * x ^ (1 / 4 : ℝ) := by
    have htri := abs_add_le (airyAi' (-x) - L) (2 * L)
    have : airyAi' (-x) - L + 2 * L = airyAi' (-x) + L := by ring
    rw [this, abs_mul, (abs_of_pos two_pos : |(2 : ℝ)| = 2)] at htri
    linarith [htri, h2', hL]
  have hLsq : L ^ 2 = x ^ (1 / 2 : ℝ) * Real.cos (cohnTheta x) ^ 2 / π := by
    dsimp [L]
    have hx12 : (x ^ (1 / 4 : ℝ)) ^ 2 = x ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
    rw [neg_sq, div_pow, mul_pow, hx12, Real.sq_sqrt Real.pi_pos.le]
  rw [← hLsq, show airyAi' (-x) ^ 2 - L ^ 2 = (airyAi' (-x) - L) * (airyAi' (-x) + L) by ring, abs_mul]
  have hcomb : (2 / (5 * x ^ (5 / 4 : ℝ))) * (3 * x ^ (1 / 4 : ℝ)) = 6 / 5 * x ^ (-1 : ℝ) := by
    rw [Real.rpow_neg hx0.le]
    have hxinv : (x ^ (5 / 4 : ℝ))⁻¹ * x ^ (1 / 4 : ℝ) = x⁻¹ := by
      rw [← Real.rpow_neg hx0.le, ← Real.rpow_add hx0]; norm_num; exact Real.rpow_neg_one x
    calc (2 / (5 * x ^ (5 / 4 : ℝ))) * (3 * x ^ (1 / 4 : ℝ))
        = (6 / 5) * ((x ^ (5 / 4 : ℝ))⁻¹ * x ^ (1 / 4 : ℝ)) := by ring
      _ = (6 / 5) * x⁻¹ := by rw [hxinv]
      _ = 6 / 5 * (x ^ (1 : ℝ))⁻¹ := by simp
  calc |airyAi' (-x) - L| * |airyAi' (-x) + L|
      ≤ (2 / (5 * x ^ (5 / 4 : ℝ))) * (3 * x ^ (1 / 4 : ℝ)) :=
        mul_le_mul h2' hsum (abs_nonneg _) (by positivity)
    _ = 6 / 5 * x ^ (-1 : ℝ) := hcomb
    _ ≤ 2 * x ^ (-1 : ℝ) := by gcongr; norm_num

/-! ### Proposition CR.3 (`(CR.11)`, `(CR.12)`, `(CR.12a)`, `(CR.13)`) -/

/-- The leading `sin² ϑ` coefficient `𝔞(q)` of Proposition CR.3 (`cecr:CR3`). -/
noncomputable def cohnMathfrakA (a q : ℝ) : ℝ :=
  let z := airyZero 1 + q⁻¹
  q⁻¹ * (cohnM z / (z - a) ^ 2 + (z - 2 * a) / (z - a))

private lemma isBigO_neg_add_const_inv_sub (c : ℝ) :
    (fun x : ℝ => (-x - c)⁻¹ - (-x)⁻¹) =O[atTop] (fun x : ℝ => x ^ (-2 : ℝ)) := by
  refine isBigO_rpow_inv ⟨2 * (|c| + 1), by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (2 * |c| + 1)] with x hx
  have hx0 : 0 < x := by linarith [abs_nonneg c]
  have hx_c : |c| + 1 / 2 < x := by linarith [abs_nonneg c]
  have h1 : x / 2 ≤ x + c := by
    have : -|c| ≤ c := neg_abs_le c
    linarith
  have h1pos : 0 < x + c := by linarith
  have heq : (-x - c)⁻¹ - (-x)⁻¹ = c / ((x + c) * x) := by
    rw [show -x - c = -(x + c) by ring, inv_neg, inv_neg]
    have h1 : x + c ≠ 0 := h1pos.ne'
    have h2 : x ≠ 0 := hx0.ne'
    field_simp
    ring
  rw [heq, abs_div, abs_of_pos (mul_pos h1pos hx0), Real.rpow_neg hx0.le]
  have hden : x ^ (2 : ℝ) / 2 ≤ (x + c) * x := by
    rw [Real.rpow_two]
    nlinarith
  calc |c| / ((x + c) * x)
      ≤ |c| / (x ^ (2 : ℝ) / 2) := div_le_div_of_nonneg_left (abs_nonneg c) (by positivity) hden
    _ = 2 * |c| * (x ^ (2 : ℝ))⁻¹ := by ring
    _ ≤ 2 * (|c| + 1) * (x ^ (2 : ℝ))⁻¹ := by gcongr; linarith

private lemma inv_neg_sub_sq_asym (a : ℝ) :
    (fun x : ℝ => ((-x - a) ^ 2)⁻¹ - x ^ (-2 : ℝ)) =O[atTop] (fun x : ℝ => x ^ (-3 : ℝ)) := by
  refine isBigO_rpow_inv ⟨8 * |a| + 4 * a ^ 2 + 1, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (2 * |a| + 1)] with x hx
  have hx0 : 0 < x := by linarith [abs_nonneg a]
  have h1 : x / 2 ≤ x + a := by linarith [neg_abs_le a]
  have h1pos : 0 < x + a := by linarith
  have heq : ((-x - a) ^ 2)⁻¹ - x ^ (-2 : ℝ) = -(2 * a * x + a ^ 2) / ((x + a) ^ 2 * x ^ 2) := by
    rw [show (-x - a) ^ 2 = (x + a) ^ 2 by ring, show (-2 : ℝ) = -(2 : ℝ) by norm_num,
      Real.rpow_neg hx0.le, Real.rpow_two]
    have hxa0 : x + a ≠ 0 := h1pos.ne'
    have hxne : x ≠ 0 := hx0.ne'
    field_simp
    ring
  rw [heq, abs_div, abs_neg, abs_of_pos (mul_pos (sq_pos_of_pos h1pos) (sq_pos_of_pos hx0))]
  have hnum : |2 * a * x + a ^ 2| ≤ (2 * |a| + a ^ 2) * x := by
    have : a ^ 2 ≤ a ^ 2 * x := le_mul_of_one_le_right (sq_nonneg a) (by linarith [abs_nonneg a])
    calc |2 * a * x + a ^ 2| ≤ |2 * a * x| + |a ^ 2| := abs_add_le _ _
      _ = 2 * |a| * x + a ^ 2 := by rw [abs_mul, abs_mul, abs_of_pos two_pos, abs_of_pos hx0, abs_sq]
      _ ≤ (2 * |a| + a ^ 2) * x := by linarith
  have hden : x ^ 4 / 4 ≤ (x + a) ^ 2 * x ^ 2 := by
    have hsq : x ^ 2 / 4 ≤ (x + a) ^ 2 := by nlinarith
    nlinarith [sq_nonneg x]
  have hx3 : x ^ (-3 : ℝ) = x / x ^ 4 := by
    rw [show (-3 : ℝ) = -(3 : ℝ) by norm_num, Real.rpow_neg hx0.le,
      show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    field_simp
  rw [hx3]
  calc |2 * a * x + a ^ 2| / ((x + a) ^ 2 * x ^ 2)
      ≤ ((2 * |a| + a ^ 2) * x) / (x ^ 4 / 4) :=
        div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = (8 * |a| + 4 * a ^ 2) * (x / x ^ 4) := by ring
    _ ≤ (8 * |a| + 4 * a ^ 2 + 1) * (x / x ^ 4) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)

private lemma inv_neg_sub_mul_asym (a z : ℝ) :
    (fun x : ℝ => ((-x - a) ^ 2 * (z - -x))⁻¹ - x ^ (-3 : ℝ)) =O[atTop]
      (fun x : ℝ => x ^ (-4 : ℝ)) := by
  refine isBigO_rpow_inv ⟨32 * (2 * |a| + |z|) + 16 * (a ^ 2 + 2 * |a * z|) + 8 * a ^ 2 * |z| + 1,
      by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (2 * max |a| |z| + 1)] with x hx
  have hx0 : 0 < x := by linarith [abs_nonneg a, le_max_left |a| |z|]
  have ha : x / 2 ≤ x + a := by linarith [neg_abs_le a, le_max_left |a| |z|]
  have hz : x / 2 ≤ x + z := by linarith [neg_abs_le z, le_max_right |a| |z|]
  have hapos : 0 < x + a := by linarith
  have hzpos : 0 < x + z := by linarith
  have hx1 : 1 ≤ x := by linarith [le_max_left |a| |z|, abs_nonneg a]
  have heq : ((-x - a) ^ 2 * (z - -x))⁻¹ - x ^ (-3 : ℝ) =
      -((2 * a + z) * x ^ 2 + (a ^ 2 + 2 * a * z) * x + a ^ 2 * z) /
        ((x + a) ^ 2 * (x + z) * x ^ 3) := by
    rw [show (-x - a) ^ 2 = (x + a) ^ 2 by ring, show z - -x = x + z by ring,
      show (-3 : ℝ) = -(3 : ℝ) by norm_num, Real.rpow_neg hx0.le,
      show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have h1 : x + a ≠ 0 := hapos.ne'
    have h2 : x + z ≠ 0 := hzpos.ne'
    have h3 : x ≠ 0 := hx0.ne'
    field_simp
    ring
  rw [heq, abs_div, abs_neg,
    abs_of_pos (mul_pos (mul_pos (sq_pos_of_pos hapos) hzpos) (pow_pos hx0 3))]
  have hnum : |(2 * a + z) * x ^ 2 + (a ^ 2 + 2 * a * z) * x + a ^ 2 * z| ≤
      ((2 * |a| + |z|) + (a ^ 2 + 2 * |a * z|) + a ^ 2 * |z|) * x ^ 2 := by
    have hx_le : x ≤ x ^ 2 := le_self_pow₀ hx1 (by norm_num)
    have h1_le : 1 ≤ x ^ 2 := one_le_pow₀ hx1
    calc |(2 * a + z) * x ^ 2 + (a ^ 2 + 2 * a * z) * x + a ^ 2 * z|
        ≤ |(2 * a + z) * x ^ 2| + |(a ^ 2 + 2 * a * z) * x| + |a ^ 2 * z| := by
          linarith [abs_add_le ((2 * a + z) * x ^ 2 + (a ^ 2 + 2 * a * z) * x) (a ^ 2 * z),
            abs_add_le ((2 * a + z) * x ^ 2) ((a ^ 2 + 2 * a * z) * x)]
      _ = |2 * a + z| * x ^ 2 + |a ^ 2 + 2 * a * z| * x + a ^ 2 * |z| := by
          simp only [abs_mul, abs_of_pos hx0, abs_sq]
      _ ≤ (2 * |a| + |z|) * x ^ 2 + (a ^ 2 + 2 * |a * z|) * x ^ 2 + (a ^ 2 * |z|) * x ^ 2 := by
          have ha1 : |2 * a + z| ≤ 2 * |a| + |z| := by
            calc |2 * a + z| ≤ |2 * a| + |z| := abs_add_le _ _
              _ = 2 * |a| + |z| := by rw [abs_mul, abs_of_pos two_pos]
          have ha2 : |a ^ 2 + 2 * a * z| ≤ a ^ 2 + 2 * |a * z| := by
            calc |a ^ 2 + 2 * a * z| ≤ |a ^ 2| + |2 * (a * z)| := by
                  rw [show 2 * a * z = 2 * (a * z) by ring]; exact abs_add_le _ _
              _ = a ^ 2 + 2 * |a * z| := by rw [abs_sq, abs_mul, abs_of_pos two_pos]
          have ht1 : |2 * a + z| * x ^ 2 ≤ (2 * |a| + |z|) * x ^ 2 :=
            mul_le_mul_of_nonneg_right ha1 (sq_nonneg x)
          have ht2 : |a ^ 2 + 2 * a * z| * x ≤ (a ^ 2 + 2 * |a * z|) * x ^ 2 :=
            mul_le_mul ha2 hx_le hx0.le (by positivity)
          have ht3 : a ^ 2 * |z| ≤ a ^ 2 * |z| * x ^ 2 :=
            le_mul_of_one_le_right (by positivity) h1_le
          linarith
      _ = ((2 * |a| + |z|) + (a ^ 2 + 2 * |a * z|) + a ^ 2 * |z|) * x ^ 2 := by ring
  have hden : x ^ 6 / 8 ≤ (x + a) ^ 2 * (x + z) * x ^ 3 := by
    have hsq : x ^ 2 / 4 ≤ (x + a) ^ 2 := by nlinarith
    have h12 : x ^ 3 / 8 ≤ (x + a) ^ 2 * (x + z) := by nlinarith
    calc x ^ 6 / 8 = (x ^ 3 / 8) * x ^ 3 := by ring
      _ ≤ ((x + a) ^ 2 * (x + z)) * x ^ 3 := mul_le_mul_of_nonneg_right h12 (pow_nonneg hx0.le 3)
  have hx4 : x ^ (-4 : ℝ) = x ^ 2 / x ^ 6 := by
    rw [show (-4 : ℝ) = -(4 : ℝ) by norm_num, Real.rpow_neg hx0.le,
      show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    field_simp
  rw [hx4]
  calc |(2 * a + z) * x ^ 2 + (a ^ 2 + 2 * a * z) * x + a ^ 2 * z| / ((x + a) ^ 2 * (x + z) * x ^ 3)
      ≤ (((2 * |a| + |z|) + (a ^ 2 + 2 * |a * z|) + a ^ 2 * |z|) * x ^ 2) / (x ^ 6 / 8) :=
        div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = (8 * (2 * |a| + |z|) + 8 * (a ^ 2 + 2 * |a * z|) + 8 * a ^ 2 * |z|) * (x ^ 2 / x ^ 6) := by ring
    _ ≤ (32 * (2 * |a| + |z|) + 16 * (a ^ 2 + 2 * |a * z|) + 8 * a ^ 2 * |z| + 1) * (x ^ 2 / x ^ 6) :=
        mul_le_mul_of_nonneg_right
          (by linarith [abs_nonneg a, abs_nonneg z, abs_nonneg (a * z), sq_nonneg a]) (by positivity)

/-- **Proposition CR.3 (`cecr:CR3`, eq. `(CR.11)`):**
For fixed `q > 0` with `z = a_1 + q⁻¹ ≠ a`, as `x → +∞`,
`G_q(-x) = (π x^{5/2})⁻¹ (𝔞(q) sin² ϑ(x) + q⁻¹ cos² ϑ(x)) + O_q(x^{-7/2})`. -/
theorem cohnG_neg_asymptotic {a q : ℝ} (ha : airyAi' a = 0) (hq : 0 < q)
    (hza : airyZero 1 + q⁻¹ ≠ a) :
    (fun x : ℝ => cohnG a q (-x) -
      1 / (π * x ^ (5 / 2 : ℝ)) *
        (cohnMathfrakA a q * Real.sin (cohnTheta x) ^ 2 + q⁻¹ * Real.cos (cohnTheta x) ^ 2)) =O[atTop]
      (fun x : ℝ => x ^ (-7 / 2 : ℝ)) := by
  set z : ℝ := airyZero 1 + q⁻¹
  have hGeq : ∀ᶠ x in atTop, cohnG a q (-x) = closedResolventRHS a q (-x) := by
    filter_upwards [eventually_gt_atTop (max (-a) (-z))] with x hx
    have hx_a : -x ≠ a := by linarith [le_max_left (-a) (-z)]
    have hx_z : -x ≠ z := by linarith [le_max_right (-a) (-z)]
    exact cohnG_eq ha hq hza hx_a hx_z
  -- Check coefficient asymptotics of `closedResolventCoeffA/B/C`:
  -- A_q(-x) = mathfrakA(q) * x^{-2} + O(x^{-3})
  have hA : (fun x : ℝ => closedResolventCoeffA a q (-x) - cohnMathfrakA a q * x ^ (-2 : ℝ)) =O[atTop]
      (fun x : ℝ => x ^ (-3 : ℝ)) := by
    have hsplit : ∀ᶠ x in atTop,
        closedResolventCoeffA a q (-x) - cohnMathfrakA a q * x ^ (-2 : ℝ) =
          q⁻¹ * cohnM z / (z - a) ^ 2 * (((-x - z) ^ 2)⁻¹ - x ^ (-2 : ℝ)) +
            q⁻¹ * (z - 2 * a) / (z - a) * (((-x - a) ^ 2 * (z - -x))⁻¹ * x - x ^ (-2 : ℝ)) -
            q⁻¹ * (a * z) / (z - a) * ((-x - a) ^ 2 * (z - -x))⁻¹ := by
      filter_upwards [eventually_gt_atTop (max (max (-a) (-z) + 1) 1)] with x hx
      have hx0 : 0 < x := by linarith [le_max_right (max (-a) (-z) + 1) 1]
      have hmax : max (-a) (-z) + 1 < x := lt_of_le_of_lt (le_max_left _ 1) hx
      have hxa' : x + a ≠ 0 := by linarith [le_max_left (-a) (-z)]
      have hxz' : x + z ≠ 0 := by linarith [le_max_right (-a) (-z)]
      have hq0 : q ≠ 0 := hq.ne'
      have hza' : z - a ≠ 0 := sub_ne_zero.mpr hza
      unfold closedResolventCoeffA cohnMathfrakA
      dsimp only
      have hzdef : airyZero 1 + q⁻¹ = z := rfl
      rw [hzdef, show (-x - a) ^ 2 = (x + a) ^ 2 by ring,
        show (-x - z) ^ 2 = (x + z) ^ 2 by ring, show z - -x = x + z by ring,
        show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg hx0.le, Real.rpow_two]
      field_simp
      ring
    have h1 := (inv_neg_sub_sq_asym z).congr_left (fun x => by dsimp only)
    have h2 : (fun x : ℝ => ((-x - a) ^ 2 * (z - -x))⁻¹ * x - x ^ (-2 : ℝ)) =O[atTop]
        (fun x : ℝ => x ^ (-3 : ℝ)) := by
      have hmul := (inv_neg_sub_mul_asym a z).mul (isBigO_refl (fun x : ℝ => x) atTop)
      refine hmul.congr' ?_ ?_
      · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
        have hx2 : x ^ (-3 : ℝ) * x = x ^ (-2 : ℝ) := by
          conv_lhs => rhs; rw [← Real.rpow_one x]
          rw [← Real.rpow_add hx]; norm_num
        rw [sub_mul, hx2]
      · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
        conv_lhs => rhs; rw [← Real.rpow_one x]
        rw [← Real.rpow_add hx]; norm_num
    have h3 : (fun x : ℝ => ((-x - a) ^ 2 * (z - -x))⁻¹) =O[atTop] (fun x : ℝ => x ^ (-3 : ℝ)) := by
      have hle : (fun x : ℝ => x ^ (-4 : ℝ)) =O[atTop] (fun x : ℝ => x ^ (-3 : ℝ)) := by
        refine isBigO_rpow_inv ⟨1, by norm_num, ?_⟩
        filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
        rw [abs_of_pos (Real.rpow_pos_of_pos (by linarith) _), one_mul]
        exact Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
      exact ((inv_neg_sub_mul_asym a z).trans hle).add (isBigO_refl _ _) |>.congr_left fun x => by ring
    exact ((((h1.const_mul_left (q⁻¹ * cohnM z / (z - a) ^ 2)).add
      (h2.const_mul_left (q⁻¹ * (z - 2 * a) / (z - a)))).sub
      (h3.const_mul_left (q⁻¹ * (a * z) / (z - a))))).congr'
      (hsplit.mono fun x hx => hx.symm) EventuallyEq.rfl
  -- B_q(-x) = O(x^{-4})
  have hB : (fun x : ℝ => closedResolventCoeffB a q (-x)) =O[atTop] (fun x : ℝ => x ^ (-4 : ℝ)) := by
    refine isBigO_rpow_inv ⟨32 * q⁻¹ * (3 + 2 * |z| + |a|) + 1, by positivity, ?_⟩
    filter_upwards [eventually_ge_atTop (2 * max |a| |z| + 1)] with x hx
    have hx0 : 0 < x := by linarith [abs_nonneg a, le_max_left |a| |z|]
    have hx1 : 1 ≤ x := by linarith [le_max_left |a| |z|, abs_nonneg a]
    have ha' : x / 2 ≤ x + a := by linarith [neg_abs_le a, le_max_left |a| |z|]
    have hz' : x / 2 ≤ x + z := by linarith [neg_abs_le z, le_max_right |a| |z|]
    have hapos : 0 < x + a := by linarith
    have hzpos : 0 < x + z := by linarith
    unfold closedResolventCoeffB
    dsimp only
    rw [show (airyZero 1 + q⁻¹) = z from rfl]
    have heq : q⁻¹ * ((a - 3 * -x + 2 * z) / ((-x - a) ^ 3 * (z - -x) ^ 2)) =
        q⁻¹ * (3 * x + (a + 2 * z)) / ((-(x + a)) ^ 3 * (x + z) ^ 2) := by ring
    rw [heq]
    simp only [abs_div, abs_mul, abs_inv, abs_pow, abs_neg, abs_of_pos hq, abs_of_pos hapos,
      abs_of_pos hzpos]
    have hnum : |3 * x + (a + 2 * z)| ≤ (3 + 2 * |z| + |a|) * x := by
      calc |3 * x + (a + 2 * z)| ≤ |3 * x| + |a + 2 * z| := abs_add_le _ _
        _ ≤ 3 * x + (|a| + 2 * |z|) := by
            rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3), abs_of_pos hx0]
            have h2z : |a + 2 * z| ≤ |a| + 2 * |z| := by
              calc |a + 2 * z| ≤ |a| + |2 * z| := abs_add_le _ _
                _ = |a| + 2 * |z| := by rw [abs_mul, abs_of_pos (two_pos : (0 : ℝ) < 2)]
            linarith
        _ ≤ (3 + 2 * |z| + |a|) * x := by nlinarith [abs_nonneg a, abs_nonneg z]
    have hden : x ^ 5 / 32 ≤ (x + a) ^ 3 * (x + z) ^ 2 := by
      have h3 : x ^ 3 / 8 ≤ (x + a) ^ 3 :=
        calc x ^ 3 / 8 = (x / 2) ^ 3 := by ring
          _ ≤ (x + a) ^ 3 := pow_le_pow_left₀ (by linarith) ha' 3
      have h2 : x ^ 2 / 4 ≤ (x + z) ^ 2 :=
        calc x ^ 2 / 4 = (x / 2) ^ 2 := by ring
          _ ≤ (x + z) ^ 2 := pow_le_pow_left₀ (by linarith) hz' 2
      calc x ^ 5 / 32 = (x ^ 3 / 8) * (x ^ 2 / 4) := by ring
        _ ≤ (x + a) ^ 3 * (x + z) ^ 2 := mul_le_mul h3 h2 (by positivity) (by positivity)
    have hx4 : x ^ (-4 : ℝ) = x / x ^ 5 := by
      rw [show (-4 : ℝ) = -(4 : ℝ) by norm_num, Real.rpow_neg hx0.le,
        show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      field_simp
    rw [hx4]
    calc q⁻¹ * |3 * x + (a + 2 * z)| / ((x + a) ^ 3 * (x + z) ^ 2)
        ≤ (q⁻¹ * ((3 + 2 * |z| + |a|) * x)) / (x ^ 5 / 32) :=
          div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hnum (inv_nonneg.mpr hq.le))
            (by positivity) hden
      _ = 32 * q⁻¹ * (3 + 2 * |z| + |a|) * (x / x ^ 5) := by ring
      _ ≤ (32 * q⁻¹ * (3 + 2 * |z| + |a|) + 1) * (x / x ^ 5) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  -- C_q(-x) = q⁻¹ * x^{-3} + O(x^{-4})
  have hC : (fun x : ℝ => closedResolventCoeffC a q (-x) - q⁻¹ * x ^ (-3 : ℝ)) =O[atTop]
      (fun x : ℝ => x ^ (-4 : ℝ)) := by
    have hCeq : (fun x : ℝ => closedResolventCoeffC a q (-x) - q⁻¹ * x ^ (-3 : ℝ)) =
        fun x : ℝ => q⁻¹ * (((-x - a) ^ 2 * (z - -x))⁻¹ - x ^ (-3 : ℝ)) := by
      funext x
      unfold closedResolventCoeffC
      dsimp only
      rw [show (airyZero 1 + q⁻¹) = z from rfl]
      ring
    rw [hCeq]
    exact (inv_neg_sub_mul_asym a z).const_mul_left _
  -- Combine A_q Ai² + B_q Ai Ai' + C_q Ai'²!
  have hterm1 : (fun x : ℝ => closedResolventCoeffA a q (-x) * airyAi (-x) ^ 2 -
      1 / (π * x ^ (5 / 2 : ℝ)) * (cohnMathfrakA a q * Real.sin (cohnTheta x) ^ 2)) =O[atTop]
      (fun x : ℝ => x ^ (-7 / 2 : ℝ)) := by
    have hAi_bd : (fun x : ℝ => airyAi (-x) ^ 2) =O[atTop] (fun x : ℝ => x ^ (-1 / 2 : ℝ)) := by
      have hmain : (fun x : ℝ => Real.sin (cohnTheta x) ^ 2 / (π * x ^ (1 / 2 : ℝ))) =O[atTop]
          (fun x : ℝ => x ^ (-1 / 2 : ℝ)) := by
        refine isBigO_rpow_inv ⟨π⁻¹, by positivity, ?_⟩
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
        rw [abs_div, abs_of_pos (mul_pos Real.pi_pos (Real.rpow_pos_of_pos hx _))]
        rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by norm_num, Real.rpow_neg hx.le]
        have hsin : |Real.sin (cohnTheta x) ^ 2| ≤ 1 := by
          rw [abs_sq]; exact sq_le_one_iff_abs_le_one _ |>.mpr (Real.abs_sin_le_one _)
        calc |Real.sin (cohnTheta x) ^ 2| / (π * x ^ (1 / 2 : ℝ))
            ≤ 1 / (π * x ^ (1 / 2 : ℝ)) := div_le_div_of_nonneg_right hsin (by positivity)
          _ = π⁻¹ * (x ^ (1 / 2 : ℝ))⁻¹ := by ring
      have h2_le : (fun x : ℝ => x ^ (-2 : ℝ)) =O[atTop] (fun x : ℝ => x ^ (-1 / 2 : ℝ)) := by
        refine isBigO_rpow_inv ⟨1, by norm_num, ?_⟩
        filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
        rw [abs_of_pos (Real.rpow_pos_of_pos (by linarith) _), one_mul]
        exact Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
      exact (airyAi_neg_sq_isBigO.trans h2_le |>.add hmain).congr_left fun x => by ring
    have hp1 : (fun x : ℝ => (closedResolventCoeffA a q (-x) - cohnMathfrakA a q * x ^ (-2 : ℝ)) *
        airyAi (-x) ^ 2) =O[atTop] (fun x : ℝ => x ^ (-7 / 2 : ℝ)) := by
      refine (hA.mul hAi_bd).congr' EventuallyEq.rfl ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [← Real.rpow_add hx]; norm_num
    have hp2 : (fun x : ℝ => cohnMathfrakA a q * x ^ (-2 : ℝ) *
        (airyAi (-x) ^ 2 - Real.sin (cohnTheta x) ^ 2 / (π * x ^ (1 / 2 : ℝ)))) =O[atTop]
        (fun x : ℝ => x ^ (-7 / 2 : ℝ)) := by
      have h4_le : (fun x : ℝ => x ^ (-4 : ℝ)) =O[atTop] (fun x : ℝ => x ^ (-7 / 2 : ℝ)) := by
        refine isBigO_rpow_inv ⟨1, by norm_num, ?_⟩
        filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
        rw [abs_of_pos (Real.rpow_pos_of_pos (by linarith) _), one_mul]
        exact Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
      refine ((isBigO_refl (fun x : ℝ => cohnMathfrakA a q * x ^ (-2 : ℝ)) atTop).mul
        airyAi_neg_sq_isBigO).trans ?_
      refine IsBigO.trans ?_ h4_le
      refine IsBigO.of_bound |cohnMathfrakA a q| ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [Real.norm_eq_abs, abs_mul, abs_mul, Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos hx _),
        abs_of_pos (Real.rpow_pos_of_pos hx _), mul_assoc, ← Real.rpow_add hx]
      norm_num
    refine (hp1.add hp2).congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hx52 : x ^ (2 : ℝ) * x ^ (1 / 2 : ℝ) = x ^ (5 / 2 : ℝ) := by
      rw [← Real.rpow_add hx]; norm_num
    rw [Real.rpow_neg hx.le]
    calc (closedResolventCoeffA a q (-x) - cohnMathfrakA a q * (x ^ (2 : ℝ))⁻¹) * airyAi (-x) ^ 2 +
          cohnMathfrakA a q * (x ^ (2 : ℝ))⁻¹ *
            (airyAi (-x) ^ 2 - Real.sin (cohnTheta x) ^ 2 / (π * x ^ (1 / 2 : ℝ)))
        = closedResolventCoeffA a q (-x) * airyAi (-x) ^ 2 -
            1 / (π * (x ^ (2 : ℝ) * x ^ (1 / 2 : ℝ))) *
              (cohnMathfrakA a q * Real.sin (cohnTheta x) ^ 2) := by ring
      _ = _ := by rw [hx52]
  have hterm2 : (fun x : ℝ => closedResolventCoeffB a q (-x) * (airyAi (-x) * airyAi' (-x))) =O[atTop]
      (fun x : ℝ => x ^ (-7 / 2 : ℝ)) := by
    have h4_le : (fun x : ℝ => x ^ (-4 : ℝ)) =O[atTop] (fun x : ℝ => x ^ (-7 / 2 : ℝ)) := by
      refine isBigO_rpow_inv ⟨1, by norm_num, ?_⟩
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      rw [abs_of_pos (Real.rpow_pos_of_pos (by linarith) _), one_mul]
      exact Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
    exact ((hB.mul airyAi_mul_airyAi'_neg_isBigO).congr_right fun x => mul_one _).trans h4_le
  have hterm3 : (fun x : ℝ => closedResolventCoeffC a q (-x) * airyAi' (-x) ^ 2 -
      1 / (π * x ^ (5 / 2 : ℝ)) * (q⁻¹ * Real.cos (cohnTheta x) ^ 2)) =O[atTop]
      (fun x : ℝ => x ^ (-7 / 2 : ℝ)) := by
    have hAi'_bd : (fun x : ℝ => airyAi' (-x) ^ 2) =O[atTop] (fun x : ℝ => x ^ (1 / 2 : ℝ)) := by
      have hmain : (fun x : ℝ => x ^ (1 / 2 : ℝ) * Real.cos (cohnTheta x) ^ 2 / π) =O[atTop]
          (fun x : ℝ => x ^ (1 / 2 : ℝ)) := by
        refine isBigO_rpow_inv ⟨π⁻¹, by positivity, ?_⟩
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
        rw [abs_div, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hx _), abs_of_pos Real.pi_pos]
        have hcos : |Real.cos (cohnTheta x) ^ 2| ≤ 1 := by
          rw [abs_sq]; exact sq_le_one_iff_abs_le_one _ |>.mpr (Real.abs_cos_le_one _)
        calc x ^ (1 / 2 : ℝ) * |Real.cos (cohnTheta x) ^ 2| / π
            ≤ x ^ (1 / 2 : ℝ) * 1 / π := div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hcos (Real.rpow_nonneg hx.le _)) Real.pi_pos.le
          _ = π⁻¹ * x ^ (1 / 2 : ℝ) := by ring
      have hm1_le : (fun x : ℝ => x ^ (-1 : ℝ)) =O[atTop] (fun x : ℝ => x ^ (1 / 2 : ℝ)) := by
        refine isBigO_rpow_inv ⟨1, by norm_num, ?_⟩
        filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
        rw [abs_of_pos (Real.rpow_pos_of_pos (by linarith) _), one_mul]
        exact Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
      exact (airyAi'_neg_sq_isBigO.trans hm1_le |>.add hmain).congr_left fun x => by ring
    have hp1 : (fun x : ℝ => (closedResolventCoeffC a q (-x) - q⁻¹ * x ^ (-3 : ℝ)) *
        airyAi' (-x) ^ 2) =O[atTop] (fun x : ℝ => x ^ (-7 / 2 : ℝ)) := by
      refine (hC.mul hAi'_bd).congr' EventuallyEq.rfl ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [← Real.rpow_add hx]; norm_num
    have hp2 : (fun x : ℝ => q⁻¹ * x ^ (-3 : ℝ) *
        (airyAi' (-x) ^ 2 - x ^ (1 / 2 : ℝ) * Real.cos (cohnTheta x) ^ 2 / π)) =O[atTop]
        (fun x : ℝ => x ^ (-7 / 2 : ℝ)) := by
      have h4_le : (fun x : ℝ => x ^ (-4 : ℝ)) =O[atTop] (fun x : ℝ => x ^ (-7 / 2 : ℝ)) := by
        refine isBigO_rpow_inv ⟨1, by norm_num, ?_⟩
        filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
        rw [abs_of_pos (Real.rpow_pos_of_pos (by linarith) _), one_mul]
        exact Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
      refine IsBigO.trans ?_ h4_le
      have hprod := (isBigO_refl (fun x : ℝ => x ^ (-3 : ℝ)) atTop).mul airyAi'_neg_sq_isBigO
      have hprod' : (fun x : ℝ => x ^ (-3 : ℝ) *
          (airyAi' (-x) ^ 2 - x ^ (1 / 2 : ℝ) * Real.cos (cohnTheta x) ^ 2 / π)) =O[atTop]
          (fun x : ℝ => x ^ (-4 : ℝ)) := by
        refine hprod.congr' EventuallyEq.rfl ?_
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
        rw [← Real.rpow_add hx]; norm_num
      exact (hprod'.const_mul_left q⁻¹).congr_left (fun x => by ring)
    refine (hp1.add hp2).congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hx_neg3_mul : x ^ (-3 : ℝ) * x ^ (1 / 2 : ℝ) = (x ^ (5 / 2 : ℝ))⁻¹ := by
      rw [← Real.rpow_add hx, show (-3 : ℝ) + 1 / 2 = -(5 / 2 : ℝ) by norm_num, Real.rpow_neg hx.le]
    have hdiv : q⁻¹ * x ^ (-3 : ℝ) * (x ^ (1 / 2 : ℝ) * Real.cos (cohnTheta x) ^ 2 / π) =
        q⁻¹ * (x ^ (5 / 2 : ℝ))⁻¹ * Real.cos (cohnTheta x) ^ 2 / π := by
      rw [show q⁻¹ * x ^ (-3 : ℝ) * (x ^ (1 / 2 : ℝ) * Real.cos (cohnTheta x) ^ 2 / π) =
        q⁻¹ * (x ^ (-3 : ℝ) * x ^ (1 / 2 : ℝ)) * Real.cos (cohnTheta x) ^ 2 / π by ring, hx_neg3_mul]
    rw [mul_sub, hdiv]
    ring
  have hcomb : (fun x : ℝ => closedResolventRHS a q (-x) - 1 / (π * x ^ (5 / 2 : ℝ)) *
      (cohnMathfrakA a q * Real.sin (cohnTheta x) ^ 2 + q⁻¹ * Real.cos (cohnTheta x) ^ 2)) =O[atTop]
      (fun x : ℝ => x ^ (-7 / 2 : ℝ)) := by
    have hsum := (hterm1.add hterm2).add hterm3
    refine hsum.congr' (EventuallyEq.of_eq (funext fun x => ?_)) EventuallyEq.rfl
    rw [closedResolventRHS_eq_three_airy]
    ring
  exact hcomb.congr' (hGeq.mono fun x hx => by dsimp only; rw [← hx]) EventuallyEq.rfl

/-- **Proposition CR.3 (`cecr:CR3`, first-node subtraction, eq. `(CR.12)`):**
the first-node cardinal square `c_1² L_1(-x)² = [π (a_1 - a)² x^{5/2}]⁻¹ sin² ϑ(x) + O(x^{-7/2})`,
so `G_q(-x) - c_1² L_1(-x)²` retains a persistent oscillatory leading term unless `𝔞(q) - (a_1-a)⁻² = q⁻¹`. -/
theorem cohnFirstNode_neg_asymptotic {a : ℝ} (ha : airyAi' a = 0) :
    (fun x : ℝ => cohnC a 0 ^ 2 * cohnL 0 (-x) ^ 2 -
      (1 / (π * (airyZero 1 - a) ^ 2 * x ^ (5 / 2 : ℝ))) * Real.sin (cohnTheta x) ^ 2) =O[atTop]
      (fun x : ℝ => x ^ (-7 / 2 : ℝ)) := by
  have ha0 : airyZero 1 - a ≠ 0 := by
    intro h
    have heq : airyZero 1 = a := sub_eq_zero.mp h
    exact (airyAi_ne_zero_of_deriv_zero ha) (heq ▸ airyAi_airyZero 1)
  have hInv : (fun x : ℝ => ((-x - airyZero 1) ^ 2)⁻¹ - x ^ (-2 : ℝ)) =O[atTop]
      (fun x : ℝ => x ^ (-3 : ℝ)) := inv_neg_sub_sq_asym (airyZero 1)
  have hAi_bd : (fun x : ℝ => airyAi (-x) ^ 2) =O[atTop] (fun x : ℝ => x ^ (-1 / 2 : ℝ)) := by
    have hmain : (fun x : ℝ => Real.sin (cohnTheta x) ^ 2 / (π * x ^ (1 / 2 : ℝ))) =O[atTop]
        (fun x : ℝ => x ^ (-1 / 2 : ℝ)) := by
      refine isBigO_rpow_inv ⟨π⁻¹, by positivity, ?_⟩
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [abs_div, abs_of_pos (mul_pos Real.pi_pos (Real.rpow_pos_of_pos hx _))]
      rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by norm_num, Real.rpow_neg hx.le]
      have hsin : |Real.sin (cohnTheta x) ^ 2| ≤ 1 := by
        rw [abs_sq]; exact sq_le_one_iff_abs_le_one _ |>.mpr (Real.abs_sin_le_one _)
      calc |Real.sin (cohnTheta x) ^ 2| / (π * x ^ (1 / 2 : ℝ))
          ≤ 1 / (π * x ^ (1 / 2 : ℝ)) := div_le_div_of_nonneg_right hsin (by positivity)
        _ = π⁻¹ * (x ^ (1 / 2 : ℝ))⁻¹ := by ring
    have h2_le : (fun x : ℝ => x ^ (-2 : ℝ)) =O[atTop] (fun x : ℝ => x ^ (-1 / 2 : ℝ)) := by
      refine isBigO_rpow_inv ⟨1, by norm_num, ?_⟩
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      rw [abs_of_pos (Real.rpow_pos_of_pos (by linarith) _), one_mul]
      exact Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
    exact (airyAi_neg_sq_isBigO.trans h2_le |>.add hmain).congr_left fun x => by ring
  have h4_le : (fun x : ℝ => x ^ (-4 : ℝ)) =O[atTop] (fun x : ℝ => x ^ (-7 / 2 : ℝ)) := by
    refine isBigO_rpow_inv ⟨1, by norm_num, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    rw [abs_of_pos (Real.rpow_pos_of_pos (by linarith) _), one_mul]
    exact Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have hp1 : (fun x : ℝ => (((-x - airyZero 1) ^ 2)⁻¹ - x ^ (-2 : ℝ)) * airyAi (-x) ^ 2) =O[atTop]
      (fun x : ℝ => x ^ (-7 / 2 : ℝ)) := by
    refine (hInv.mul hAi_bd).congr' EventuallyEq.rfl ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [← Real.rpow_add hx]; norm_num
  have hp2 : (fun x : ℝ => x ^ (-2 : ℝ) *
      (airyAi (-x) ^ 2 - Real.sin (cohnTheta x) ^ 2 / (π * x ^ (1 / 2 : ℝ)))) =O[atTop]
      (fun x : ℝ => x ^ (-7 / 2 : ℝ)) := by
    refine (((isBigO_refl (fun x : ℝ => x ^ (-2 : ℝ)) atTop).mul airyAi_neg_sq_isBigO).congr'
      EventuallyEq.rfl ?_).trans h4_le
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [← Real.rpow_add hx]; norm_num
  have hsum := ((hp1.add hp2).const_mul_left (cohnC a 0 ^ 2))
  refine hsum.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop (-airyZero 1)] with x hx
  have hne : -x ≠ airyZero (0 + 1) := by simp; linarith
  have hL : cohnL 0 (-x) ^ 2 = ((-x - airyZero 1) ^ 2)⁻¹ * airyAi (-x) ^ 2 := by
    rw [cohnL_of_ne hne, div_pow, show (0 + 1 : ℕ) = 1 from rfl]; ring
  have hxpos : 0 < x := by
    have ha1neg : airyZero 1 < 0 := airyZero_neg 1
    linarith
  have hx52 : x ^ (2 : ℝ) * x ^ (1 / 2 : ℝ) = x ^ (5 / 2 : ℝ) := by
    rw [← Real.rpow_add hxpos]; norm_num
  rw [hL, cohnC, show (0 + 1 : ℕ) = 1 from rfl,
    show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg hxpos.le, inv_pow]
  calc ((airyZero 1 - a) ^ 2)⁻¹ *
        ((((-x - airyZero 1) ^ 2)⁻¹ - (x ^ (2 : ℝ))⁻¹) * airyAi (-x) ^ 2 +
          (x ^ (2 : ℝ))⁻¹ * (airyAi (-x) ^ 2 - Real.sin (cohnTheta x) ^ 2 / (π * x ^ (1 / 2 : ℝ))))
      = ((airyZero 1 - a) ^ 2)⁻¹ * (((-x - airyZero 1) ^ 2)⁻¹ * airyAi (-x) ^ 2) -
          1 / (π * (airyZero 1 - a) ^ 2 * (x ^ (2 : ℝ) * x ^ (1 / 2 : ℝ))) *
            Real.sin (cohnTheta x) ^ 2 := by field_simp; ring
    _ = _ := by rw [hx52]

theorem cohnG_sub_first_asymptotic {a q : ℝ} (ha : airyAi' a = 0) (hq : 0 < q)
    (hza : airyZero 1 + q⁻¹ ≠ a) :
    (fun x : ℝ => cohnG a q (-x) - cohnC a 0 ^ 2 * cohnL 0 (-x) ^ 2 -
      1 / (π * x ^ (5 / 2 : ℝ)) *
        ((cohnMathfrakA a q - (airyZero 1 - a)⁻¹ ^ 2) * Real.sin (cohnTheta x) ^ 2 +
          q⁻¹ * Real.cos (cohnTheta x) ^ 2)) =O[atTop]
      (fun x : ℝ => x ^ (-7 / 2 : ℝ)) := by
  have ha0 : airyZero 1 - a ≠ 0 := fun h =>
    airyAi_ne_zero_of_deriv_zero ha (sub_eq_zero.mp h ▸ airyAi_airyZero 1)
  refine ((cohnG_neg_asymptotic ha hq hza).sub (cohnFirstNode_neg_asymptotic ha)).congr_left ?_
  intro x
  simp only [one_div, inv_pow]
  field_simp [ha0]
  ring

/-! ### Limiting small-`t` expansion `(CR.12a)` and `(CR.13)` -/

private lemma abs_le_const_mul_abs_pow_of_deriv {f f' : ℝ → ℝ} {B : ℝ} {k : ℕ}
    (_hB : 0 ≤ B) (hf0 : f 0 = 0) (hd : ∀ t, HasDerivAt f (f' t) t)
    (hbd : ∀ t ∈ Icc (-1 : ℝ) 1, |f' t| ≤ B * |t| ^ k) :
    ∀ t ∈ Icc (-1 : ℝ) 1, |f t| ≤ (B / (k + 1 : ℝ)) * |t| ^ (k + 1) := by
  have hnonneg : ∀ (g g' : ℝ → ℝ), g 0 = 0 → (∀ t, HasDerivAt g (g' t) t) →
      (∀ t ∈ Icc (0 : ℝ) 1, g' t ≤ B * t ^ k) →
      ∀ t ∈ Icc (0 : ℝ) 1, g t ≤ (B / (k + 1 : ℝ)) * t ^ (k + 1) := by
    intro g g' hg0 hgd hgbd t ht
    let H : ℝ → ℝ := fun s => (B / (k + 1 : ℝ)) * s ^ (k + 1) - g s
    have hmono : MonotoneOn H (Icc 0 1) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) ?_ ?_ ?_
      · refine Continuous.continuousOn ?_
        have hgcont : Continuous g := continuous_iff_continuousAt.mpr fun s => (hgd s).continuousAt
        exact (continuous_const.mul (continuous_pow (k + 1))).sub hgcont
      · intro s _
        exact ((hasDerivAt_pow (k + 1) s |>.const_mul (B / (k + 1 : ℝ))).sub (hgd s)).differentiableAt.differentiableWithinAt
      · intro s hs
        have hH : HasDerivAt H (B * s ^ k - g' s) s := by
          have hp : HasDerivAt (fun x : ℝ => B / (k + 1 : ℝ) * x ^ (k + 1)) (B * s ^ k) s := by
            have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
            have hp0 : HasDerivAt (fun x : ℝ => B / (k + 1 : ℝ) * x ^ (k + 1))
                (B / (k + 1 : ℝ) * (((k + 1 : ℕ) : ℝ) * s ^ (k + 1 - 1))) s :=
              (hasDerivAt_pow (k + 1) s).const_mul (B / (k + 1 : ℝ))
            refine hp0.congr_deriv ?_
            rw [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
            field_simp [hk]
          exact hp.sub (hgd s)
        rw [hH.deriv]
        have hs' : s ∈ Icc (0 : ℝ) 1 := interior_subset hs
        linarith [hgbd s hs']
    have h0le : H 0 ≤ H t := hmono ⟨le_rfl, zero_le_one⟩ ht ht.1
    have hH0 : H 0 = 0 := by simp [H, hg0]
    linarith
  intro t ht
  rw [abs_le]
  rcases le_total 0 t with ht0 | ht0
  · have ht_icc : t ∈ Icc (0 : ℝ) 1 := ⟨ht0, ht.2⟩
    rw [abs_of_nonneg ht0]
    constructor
    · have := hnonneg (fun s => -f s) (fun s => -f' s) (by simp [hf0]) (fun s => (hd s).neg)
        (fun s hs => by
          have h := hbd s ⟨by linarith [hs.1], hs.2⟩
          rw [abs_of_nonneg hs.1] at h
          linarith [neg_le_abs (f' s)]) t ht_icc
      linarith
    · exact hnonneg f f' hf0 hd (fun s hs => by
        have h := hbd s ⟨by linarith [hs.1], hs.2⟩
        rw [abs_of_nonneg hs.1] at h
        linarith [le_abs_self (f' s)]) t ht_icc
  · have hnt : -t ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [ht.1]⟩
    rw [abs_of_nonpos ht0]
    have hg_pos := hnonneg (fun s => f (-s)) (fun s => -f' (-s)) (by simp [hf0])
      (fun s => by
        have h : HasDerivAt (fun x => f (-x)) (f' (-s) * (-1)) s :=
          (hd (-s)).comp s (hasDerivAt_neg s)
        exact h.congr_deriv (by ring))
      (fun s hs => by
        have h := hbd (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
        rw [abs_neg, abs_of_nonneg hs.1] at h
        linarith [neg_le_abs (f' (-s))]) (-t) hnt
    have hg_neg := hnonneg (fun s => -f (-s)) (fun s => f' (-s)) (by simp [hf0])
      (fun s => by
        have h : HasDerivAt (fun x => -f (-x)) (-(f' (-s) * (-1))) s :=
          ((hd (-s)).comp s (hasDerivAt_neg s)).neg
        exact h.congr_deriv (by ring))
      (fun s hs => by
        have h := hbd (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
        rw [abs_neg, abs_of_nonneg hs.1] at h
        linarith [le_abs_self (f' (-s))]) (-t) hnt
    simp only [neg_neg] at hg_pos hg_neg
    exact ⟨by linarith, by linarith⟩

/-- **Eq. `(CR.12a)`:** near `t = 0`, `m(a_1 + t) = t⁻¹ + (a_1 / 3) t + O(t²)`. -/
theorem cohnM_airyZero_expansion :
    (fun t : ℝ => cohnM (airyZero 1 + t) - t⁻¹ - (airyZero 1 / 3) * t) =O[𝓝[≠] (0 : ℝ)]
      (fun t : ℝ => t ^ 2) := by
  set a1 : ℝ := airyZero 1
  have hAi0 : airyAi a1 = 0 := airyAi_airyZero 1
  have hAi'0 : airyAi' a1 ≠ 0 := fun h => airyAi_ne_zero_of_deriv_zero h hAi0
  set N : ℝ → ℝ := fun t => t * airyAi' (a1 + t) - (1 + a1 / 3 * t ^ 2) * airyAi (a1 + t)
  set N1 : ℝ → ℝ := fun t =>
    (-a1 / 3 * t ^ 2) * airyAi' (a1 + t) + (t ^ 2 + a1 / 3 * t) * airyAi (a1 + t)
  set N2 : ℝ → ℝ := fun t =>
    (t ^ 2 - a1 / 3 * t) * airyAi' (a1 + t) +
      (2 * t + a1 / 3 - a1 / 3 * t ^ 2 * (a1 + t)) * airyAi (a1 + t)
  set N3 : ℝ → ℝ := fun t =>
    (4 * t - a1 / 3 * t ^ 2 * (a1 + t)) * airyAi' (a1 + t) +
      ((t ^ 2 - a1 / 3 * t) * (a1 + t) + (2 - a1 / 3 * (2 * t * (a1 + t) + t ^ 2))) * airyAi (a1 + t)
  set N4 : ℝ → ℝ := fun t =>
    (4 - a1 / 3 * (2 * t * (a1 + t) + t ^ 2) + (t ^ 2 - a1 / 3 * t) * (a1 + t) +
      (2 - a1 / 3 * (2 * t * (a1 + t) + t ^ 2))) * airyAi' (a1 + t) +
      ((4 * t - a1 / 3 * t ^ 2 * (a1 + t)) * (a1 + t) +
        ((2 * t - a1 / 3) * (a1 + t) + (t ^ 2 - a1 / 3 * t) - a1 / 3 * (2 * (a1 + t) + 2 * t + 2 * t))) *
        airyAi (a1 + t)
  have hN0 : N 0 = 0 := by simp [N, hAi0]
  have hN1_0 : N1 0 = 0 := by simp [N1, hAi0]
  have hN2_0 : N2 0 = 0 := by simp [N2, hAi0]
  have hN3_0 : N3 0 = 0 := by simp [N3, hAi0]
  have hAi_sh : ∀ t, HasDerivAt (fun s => airyAi (a1 + s)) (airyAi' (a1 + t)) t := fun t => by
    have h1 : HasDerivAt (fun s => a1 + s) 1 t := (hasDerivAt_id t).const_add a1
    simpa [Function.comp_def] using (hasDerivAt_airyAi (a1 + t)).comp t h1
  have hAi'_sh : ∀ t, HasDerivAt (fun s => airyAi' (a1 + s)) ((a1 + t) * airyAi (a1 + t)) t := fun t => by
    have h1 : HasDerivAt (fun s => a1 + s) 1 t := (hasDerivAt_id t).const_add a1
    simpa [Function.comp_def] using (hasDerivAt_airyAi' (a1 + t)).comp t h1
  have hN_d : ∀ t, HasDerivAt N (N1 t) t := fun t => by
    have ht1 : HasDerivAt (fun s => s * airyAi' (a1 + s))
        (1 * airyAi' (a1 + t) + t * ((a1 + t) * airyAi (a1 + t))) t :=
      (hasDerivAt_id t).mul (hAi'_sh t)
    have ht2 : HasDerivAt (fun s => (1 + a1 / 3 * s ^ 2) * airyAi (a1 + s))
        ((0 + a1 / 3 * (2 * t)) * airyAi (a1 + t) + (1 + a1 / 3 * t ^ 2) * airyAi' (a1 + t)) t := by
      have hp : HasDerivAt (fun s : ℝ => 1 + a1 / 3 * s ^ 2) (0 + a1 / 3 * (2 * t)) t :=
        ((hasDerivAt_const t (1 : ℝ)).add ((hasDerivAt_pow 2 t).const_mul (a1 / 3))).congr_deriv (by ring)
      exact hp.mul (hAi_sh t)
    exact (ht1.sub ht2).congr_deriv (by dsimp [N1]; ring)
  have hN1_d : ∀ t, HasDerivAt N1 (N2 t) t := fun t => by
    have hp1 : HasDerivAt (fun s : ℝ => -a1 / 3 * s ^ 2) (-a1 / 3 * (2 * t)) t :=
      ((hasDerivAt_pow 2 t).const_mul (-a1 / 3)).congr_deriv (by ring)
    have hp2 : HasDerivAt (fun s : ℝ => s ^ 2 + a1 / 3 * s) (2 * t + a1 / 3 * 1) t :=
      ((hasDerivAt_pow 2 t).add ((hasDerivAt_id t).const_mul (a1 / 3))).congr_deriv (by ring)
    exact ((hp1.mul (hAi'_sh t)).add (hp2.mul (hAi_sh t))).congr_deriv (by dsimp [N2]; ring)
  have hN2_d : ∀ t, HasDerivAt N2 (N3 t) t := fun t => by
    have hp1 : HasDerivAt (fun s : ℝ => s ^ 2 - a1 / 3 * s) (2 * t - a1 / 3 * 1) t :=
      ((hasDerivAt_pow 2 t).sub ((hasDerivAt_id t).const_mul (a1 / 3))).congr_deriv (by ring)
    have hp2 : HasDerivAt (fun s : ℝ => 2 * s + a1 / 3 - a1 / 3 * s ^ 2 * (a1 + s))
        ((2 * 1 + 0) - a1 / 3 * (2 * t * (a1 + t) + t ^ 2 * 1)) t := by
      have hA : HasDerivAt (fun s : ℝ => 2 * s + a1 / 3) (2 * 1 + 0) t :=
        ((hasDerivAt_id t).const_mul 2).add (hasDerivAt_const t _)
      have hB : HasDerivAt (fun s : ℝ => a1 / 3 * s ^ 2 * (a1 + s))
          (a1 / 3 * (2 * t * (a1 + t) + t ^ 2 * 1)) t := by
        have hp : HasDerivAt (fun s : ℝ => a1 / 3 * s ^ 2) (a1 / 3 * (2 * t)) t :=
          ((hasDerivAt_pow 2 t).const_mul (a1 / 3)).congr_deriv (by simp [pow_one])
        exact (hp.mul ((hasDerivAt_id t).const_add a1)).congr_deriv (by dsimp; ring)
      exact (hA.sub hB).congr_deriv (by dsimp)
    exact ((hp1.mul (hAi'_sh t)).add (hp2.mul (hAi_sh t))).congr_deriv (by dsimp [N3]; ring)
  have hN3_d : ∀ t, HasDerivAt N3 (N4 t) t := fun t => by
    have hp1 : HasDerivAt (fun s : ℝ => 4 * s - a1 / 3 * s ^ 2 * (a1 + s))
        (4 * 1 - a1 / 3 * (2 * t * (a1 + t) + t ^ 2 * 1)) t := by
      have hA : HasDerivAt (fun s : ℝ => 4 * s) (4 * 1) t := (hasDerivAt_id t).const_mul 4
      have hp : HasDerivAt (fun s : ℝ => a1 / 3 * s ^ 2) (a1 / 3 * (2 * t)) t :=
        ((hasDerivAt_pow 2 t).const_mul (a1 / 3)).congr_deriv (by simp [pow_one])
      have hm := hp.mul ((hasDerivAt_id t).const_add a1)
      exact (hA.sub hm).congr_deriv (by dsimp; ring)
    have hp2 : HasDerivAt
        (fun s : ℝ => (s ^ 2 - a1 / 3 * s) * (a1 + s) + (2 - a1 / 3 * (2 * s * (a1 + s) + s ^ 2)))
        (((2 * t - a1 / 3 * 1) * (a1 + t) + (t ^ 2 - a1 / 3 * t) * 1) +
          (0 - a1 / 3 * ((2 * 1 * (a1 + t) + 2 * t * 1) + 2 * t))) t := by
      have hA1 : HasDerivAt (fun s : ℝ => s ^ 2 - a1 / 3 * s) (2 * t - a1 / 3 * 1) t :=
        ((hasDerivAt_pow 2 t).sub ((hasDerivAt_id t).const_mul (a1 / 3))).congr_deriv
          (by simp [pow_one])
      have hA := hA1.mul ((hasDerivAt_id t).const_add a1)
      have hB1 : HasDerivAt (fun s : ℝ => 2 * s * (a1 + s) + s ^ 2)
          ((2 * 1 * (a1 + t) + 2 * t * 1) + 2 * t) t := by
        have hx := ((hasDerivAt_id t).const_mul 2).mul ((hasDerivAt_id t).const_add a1)
        exact (hx.add (hasDerivAt_pow 2 t)).congr_deriv (by dsimp; simp [pow_one])
      have hB := (hasDerivAt_const t (2 : ℝ)).sub (hB1.const_mul (a1 / 3))
      exact (hA.add hB).congr_deriv (by dsimp)
    exact ((hp1.mul (hAi'_sh t)).add (hp2.mul (hAi_sh t))).congr_deriv (by dsimp [N4]; ring)
  have hN4_cont : Continuous N4 := by
    have c1 : Continuous airyAi := continuous_iff_continuousAt.mpr fun s => (hasDerivAt_airyAi s).continuousAt
    have c2 : Continuous airyAi' := continuous_iff_continuousAt.mpr fun s => (hasDerivAt_airyAi' s).continuousAt
    have h1 : Continuous (fun t => airyAi (a1 + t)) := c1.comp (continuous_const.add continuous_id)
    have h2 : Continuous (fun t => airyAi' (a1 + t)) := c2.comp (continuous_const.add continuous_id)
    dsimp [N4]
    fun_prop
  obtain ⟨B, hB0, hBbd⟩ : ∃ B ≥ 0, ∀ t ∈ Icc (-1 : ℝ) 1, |N4 t| ≤ B := by
    obtain ⟨t0, -, ht0⟩ := isCompact_Icc.exists_isMaxOn (⟨0, by norm_num⟩ : (Icc (-1 : ℝ) 1).Nonempty)
      hN4_cont.abs.continuousOn
    refine ⟨max |N4 t0| 0, le_max_right _ _, fun t ht => (ht0 ht).trans (le_max_left _ _)⟩
  have hN3_bd : ∀ t ∈ Icc (-1 : ℝ) 1, |N3 t| ≤ B * |t| ^ 1 := by
    have h0 := @abs_le_const_mul_abs_pow_of_deriv N3 N4 B 0 hB0 hN3_0 hN3_d
      (fun t ht => by simpa using hBbd t ht)
    simpa using h0
  have hN2_bd := abs_le_const_mul_abs_pow_of_deriv hB0 hN2_0 hN2_d hN3_bd
  have hN1_bd := abs_le_const_mul_abs_pow_of_deriv (by positivity) hN1_0 hN1_d hN2_bd
  have hN_bd := abs_le_const_mul_abs_pow_of_deriv (by positivity) hN0 hN_d hN1_bd
  -- Lower bound `|airyAi (a1 + t)| ≥ |airyAi' a1| / 2 * |t|` for small `t` via MVT on `D(t) = airyAi (a1 + t) - airyAi' a1 * t`
  set D : ℝ → ℝ := fun t => airyAi (a1 + t) - airyAi' a1 * t
  set D1 : ℝ → ℝ := fun t => airyAi' (a1 + t) - airyAi' a1
  set D2 : ℝ → ℝ := fun t => (a1 + t) * airyAi (a1 + t)
  have hD0 : D 0 = 0 := by simp [D, hAi0]
  have hD1_0 : D1 0 = 0 := by simp [D1]
  have hD_d : ∀ t, HasDerivAt D (D1 t) t := fun t =>
    (hAi_sh t).sub (by simpa using (hasDerivAt_id t).const_mul (airyAi' a1))
  have hD1_d : ∀ t, HasDerivAt D1 (D2 t) t := fun t =>
    ((hAi'_sh t).sub (hasDerivAt_const t (airyAi' a1))).congr_deriv (by dsimp [D2]; ring)
  have hD2_cont : Continuous D2 := by
    have c1 : Continuous airyAi := continuous_iff_continuousAt.mpr fun s => (hasDerivAt_airyAi s).continuousAt
    dsimp [D2]; fun_prop
  obtain ⟨BD, hBD0, hBDbd⟩ : ∃ BD ≥ 0, ∀ t ∈ Icc (-1 : ℝ) 1, |D2 t| ≤ BD := by
    obtain ⟨t0, -, ht0⟩ := isCompact_Icc.exists_isMaxOn (⟨0, by norm_num⟩ : (Icc (-1 : ℝ) 1).Nonempty)
      hD2_cont.abs.continuousOn
    refine ⟨max |D2 t0| 0, le_max_right _ _, fun t ht => (ht0 ht).trans (le_max_left _ _)⟩
  have hD1_bd : ∀ t ∈ Icc (-1 : ℝ) 1, |D1 t| ≤ BD * |t| ^ 1 := by
    simpa using @abs_le_const_mul_abs_pow_of_deriv D1 D2 BD 0 hBD0 hD1_0 hD1_d
      (fun t ht => by simpa using hBDbd t ht)
  have hD_bd := abs_le_const_mul_abs_pow_of_deriv hBD0 hD0 hD_d hD1_bd
  set δ : ℝ := min 1 (|airyAi' a1| / (2 * (BD + 1)))
  have hδpos : 0 < δ := lt_min one_pos (div_pos (abs_pos.mpr hAi'0) (by positivity))
  set C : ℝ := (B / (1 + 1) / (2 + 1) / (3 + 1)) / (|airyAi' a1| / 2)
  refine IsBigO.of_bound C ?_
  have hmem : Metric.ball (0 : ℝ) δ \ {0} ∈ 𝓝[≠] (0 : ℝ) := by
    refine mem_nhdsWithin.mpr ⟨Metric.ball 0 δ, Metric.isOpen_ball, Metric.mem_ball_self hδpos, ?_⟩
    intro t ht; exact ⟨ht.1, ht.2⟩
  filter_upwards [hmem] with t ht
  have ht_ne : t ≠ 0 := ht.2
  have ht_abs : |t| < δ := by simpa [Real.dist_eq] using ht.1
  have ht_icc : t ∈ Icc (-1 : ℝ) 1 := by
    have h1 : |t| ≤ 1 := (ht_abs.trans_le (min_le_left _ _)).le
    exact abs_le.mp h1
  have hD_t : |D t| ≤ |airyAi' a1| / 2 * |t| := by
    have hd := hD_bd t ht_icc
    norm_num at hd
    have hle : |t| ≤ |airyAi' a1| / (2 * (BD + 1)) := (ht_abs.trans_le (min_le_right _ _)).le
    have hpow : t ^ 2 = |t| * |t| := by rw [← sq_abs, sq]
    rw [hpow] at hd
    calc |D t| ≤ BD / 2 * (|t| * |t|) := hd
      _ ≤ (BD + 1) * |t| * |t| := by
          have : BD / 2 ≤ BD + 1 := by linarith
          calc BD / 2 * (|t| * |t|) ≤ (BD + 1) * (|t| * |t|) :=
                mul_le_mul_of_nonneg_right this (by positivity)
            _ = (BD + 1) * |t| * |t| := by ring
      _ ≤ (BD + 1) * (|airyAi' a1| / (2 * (BD + 1))) * |t| := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hle (by linarith)) (abs_nonneg t)
      _ = |airyAi' a1| / 2 * |t| := by
          have : BD + 1 ≠ 0 := by linarith
          field_simp
  have hAi_low : |airyAi' a1| / 2 * |t| ≤ |airyAi (a1 + t)| := by
    have htri : |airyAi' a1 * t| - |D t| ≤ |airyAi (a1 + t)| := by
      have := abs_sub_abs_le_abs_sub (airyAi' a1 * t) (-D t)
      have heq : airyAi' a1 * t - -D t = airyAi (a1 + t) := by dsimp [D]; ring
      rwa [heq, abs_neg] at this
    rw [abs_mul] at htri
    linarith
  have hAi_ne : airyAi (a1 + t) ≠ 0 := by
    intro h0
    have : |airyAi' a1| / 2 * |t| ≤ 0 := by simpa [h0] using hAi_low
    have hpos : 0 < |airyAi' a1| / 2 * |t| := mul_pos (div_pos (abs_pos.mpr hAi'0) two_pos) (abs_pos.mpr ht_ne)
    linarith
  have heq : cohnM (a1 + t) - t⁻¹ - a1 / 3 * t = N t / (t * airyAi (a1 + t)) := by
    unfold cohnM
    dsimp [N]
    field_simp
    ring
  rw [heq, Real.norm_eq_abs, abs_div, abs_mul, Real.norm_eq_abs, abs_pow]
  have hN_t := hN_bd t ht_icc
  norm_num at hN_t
  have hden_pos : 0 < |airyAi' a1| / 2 * t ^ 2 := mul_pos (div_pos (abs_pos.mpr hAi'0) two_pos) (sq_pos_of_ne_zero ht_ne)
  have hden_le : |airyAi' a1| / 2 * t ^ 2 ≤ |t| * |airyAi (a1 + t)| := by
    rw [← sq_abs t, sq]
    calc |airyAi' a1| / 2 * (|t| * |t|) = |t| * (|airyAi' a1| / 2 * |t|) := by ring
      _ ≤ |t| * |airyAi (a1 + t)| := mul_le_mul_of_nonneg_left hAi_low (abs_nonneg t)
  have hpow4 : |t| ^ 4 = t ^ 2 * |t| ^ 2 := by
    calc |t| ^ 4 = |t| ^ 2 * |t| ^ 2 := by ring
      _ = t ^ 2 * |t| ^ 2 := by rw [sq_abs t]
  rw [hpow4] at hN_t
  have hN_t' : |N t| ≤ (B / (1 + 1) / (2 + 1) / (3 + 1)) * (t ^ 2 * |t| ^ 2) := by
    linarith only [hN_t]
  calc |N t| / (|t| * |airyAi (a1 + t)|)
      ≤ ((B / (1 + 1) / (2 + 1) / (3 + 1)) * (t ^ 2 * |t| ^ 2)) / (|airyAi' a1| / 2 * t ^ 2) :=
        div_le_div₀ (by positivity) hN_t' hden_pos hden_le
    _ = C * |t| ^ 2 := by
        have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht_ne
        dsimp [C]; field_simp

/-- **Eq. `(CR.13)`:** with `d = a_1 - a` and `t = q⁻¹ → 0`,
`(𝔞(q) - d⁻²) / q⁻¹ = 1 - a/d - 2/d³ + O(q⁻¹)`. -/
theorem cohnMathfrakA_expansion {a : ℝ} (ha : airyAi' a = 0) :
    (fun t : ℝ =>
      (cohnMathfrakA a t⁻¹ - (airyZero 1 - a)⁻¹ ^ 2) / t -
        (1 - a / (airyZero 1 - a) - 2 / (airyZero 1 - a) ^ 3)) =O[𝓝[≠] (0 : ℝ)] id := by
  set a1 : ℝ := airyZero 1
  set d : ℝ := a1 - a
  have hd : d ≠ 0 := by
    intro h0
    have heq : a1 = a := sub_eq_zero.mp h0
    exact (airyAi_ne_zero_of_deriv_zero ha) (heq ▸ airyAi_airyZero 1)
  have hm := cohnM_airyZero_expansion
  have hsplit : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ),
      (cohnMathfrakA a t⁻¹ - d⁻¹ ^ 2) / t - (1 - a / d - 2 / d ^ 3) =
        (cohnM (a1 + t) - t⁻¹) / (d + t) ^ 2 +
          t * (3 * d + 2 * t) / (d ^ 3 * (d + t) ^ 2) +
          t * a / (d * (d + t)) := by
    have hmem : Metric.ball (0 : ℝ) (|d| / 2) \ {0} ∈ 𝓝[≠] (0 : ℝ) := by
      refine mem_nhdsWithin.mpr ⟨Metric.ball 0 (|d| / 2), Metric.isOpen_ball,
        Metric.mem_ball_self (div_pos (abs_pos.mpr hd) two_pos), fun t ht => ⟨ht.1, ht.2⟩⟩
    filter_upwards [hmem] with t ht
    have ht_ne : t ≠ 0 := ht.2
    have hdt_ne : d + t ≠ 0 := by
      have h1 : |t| < |d| / 2 := by simpa [Real.dist_eq] using ht.1
      intro h0
      have : |d| = |t| := by rw [← neg_eq_iff_add_eq_zero.mpr h0, abs_neg]
      linarith [abs_pos.mpr hd]
    unfold cohnMathfrakA
    dsimp only
    rw [inv_inv, show a1 + t - a = d + t by dsimp [d]; ring,
      show a1 + t - 2 * a = d + t - a by dsimp [d]; ring]
    field_simp
    ring
  -- Show each of the three pieces is `O[𝓝[≠] 0] id`:
  have hm1 : (fun t : ℝ => cohnM (a1 + t) - t⁻¹) =O[𝓝[≠] (0 : ℝ)] id := by
    have ht2 : (fun t : ℝ => t ^ 2) =O[𝓝[≠] (0 : ℝ)] id := by
      refine IsBigO.of_bound 1 ?_
      filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℝ) one_pos)] with t ht
      have ht1 : |t| ≤ 1 := (by simpa [Real.dist_eq] using ht : |t| < 1).le
      rw [Real.norm_eq_abs, abs_pow, id_eq, Real.norm_eq_abs, one_mul, sq]
      exact mul_le_of_le_one_left (abs_nonneg t) ht1
    have hlin : (fun t : ℝ => (a1 / 3) * t) =O[𝓝[≠] (0 : ℝ)] id := by
      simpa using (isBigO_refl id (𝓝[≠] (0 : ℝ))).const_mul_left (a1 / 3)
    exact ((hm.trans ht2).add hlin).congr_left fun t => by ring
  have hden_bd : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ), |d| / 2 ≤ |d + t| := by
    have hmem : Metric.ball (0 : ℝ) (|d| / 2) ∈ 𝓝 (0 : ℝ) :=
      Metric.ball_mem_nhds 0 (div_pos (abs_pos.mpr hd) two_pos)
    filter_upwards [nhdsWithin_le_nhds hmem] with t ht
    have h1 : |t| < |d| / 2 := by simpa [Real.dist_eq] using ht
    have hsub : |d| - |t| ≤ |d + t| := by
      simpa [sub_neg_eq_add, abs_neg] using abs_sub_abs_le_abs_sub d (-t)
    linarith
  have h1 : (fun t : ℝ => (cohnM (a1 + t) - t⁻¹) / (d + t) ^ 2) =O[𝓝[≠] (0 : ℝ)] id := by
    have hinv : (fun t : ℝ => ((d + t) ^ 2)⁻¹) =O[𝓝[≠] (0 : ℝ)] (fun _ : ℝ => (1 : ℝ)) := by
      refine IsBigO.of_bound ((|d| / 2) ^ 2)⁻¹ ?_
      filter_upwards [hden_bd] with t ht
      rw [Real.norm_eq_abs, abs_inv, abs_pow, norm_one, mul_one]
      have hpos : 0 < (|d| / 2) ^ 2 := sq_pos_of_pos (div_pos (abs_pos.mpr hd) two_pos)
      exact inv_anti₀ hpos (pow_le_pow_left₀ (by positivity) ht 2)
    have hmul : (fun t : ℝ => (cohnM (a1 + t) - t⁻¹) * ((d + t) ^ 2)⁻¹) =O[𝓝[≠] (0 : ℝ)]
        (fun t : ℝ => t * 1) := hm1.mul hinv
    exact hmul.congr' (EventuallyEq.of_eq (funext fun t => by rw [div_eq_mul_inv]))
      (EventuallyEq.of_eq (funext fun t => mul_one t))
  have h2 : (fun t : ℝ => t * (3 * d + 2 * t) / (d ^ 3 * (d + t) ^ 2)) =O[𝓝[≠] (0 : ℝ)] id := by
    have hbdd : (fun t : ℝ => (3 * d + 2 * t) / (d ^ 3 * (d + t) ^ 2)) =O[𝓝[≠] (0 : ℝ)]
        (fun _ : ℝ => (1 : ℝ)) := by
      refine IsBigO.of_bound ((3 * |d| + 2) / (|d| ^ 3 * (|d| / 2) ^ 2)) ?_
      filter_upwards [hden_bd, nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℝ) one_pos)] with t hdt ht1
      have ht1' : |t| ≤ 1 := (by simpa [Real.dist_eq] using ht1 : |t| < 1).le
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_pow, norm_one, mul_one]
      have hnum : |3 * d + 2 * t| ≤ 3 * |d| + 2 := by
        calc |3 * d + 2 * t| ≤ |3 * d| + |2 * t| := abs_add_le _ _
          _ = 3 * |d| + 2 * |t| := by
              rw [abs_mul, abs_mul, (abs_of_pos (by norm_num : (0 : ℝ) < 3) : |(3 : ℝ)| = 3),
                (abs_of_pos two_pos : |(2 : ℝ)| = 2)]
          _ ≤ 3 * |d| + 2 := by linarith
      have hden : 0 < |d| ^ 3 * (|d| / 2) ^ 2 := mul_pos (pow_pos (abs_pos.mpr hd) 3)
        (sq_pos_of_pos (div_pos (abs_pos.mpr hd) two_pos))
      have hden_le : |d| ^ 3 * (|d| / 2) ^ 2 ≤ |d| ^ 3 * |d + t| ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hdt 2) (by positivity)
      exact div_le_div₀ (by positivity) hnum hden hden_le
    have hmul : (fun t : ℝ => t * ((3 * d + 2 * t) / (d ^ 3 * (d + t) ^ 2))) =O[𝓝[≠] (0 : ℝ)]
        (fun t : ℝ => t * 1) :=
      (isBigO_refl (fun t : ℝ => t) (𝓝[≠] (0 : ℝ))).mul hbdd
    exact hmul.congr' (EventuallyEq.of_eq (funext fun t => by ring))
      (EventuallyEq.of_eq (funext fun t => mul_one t))
  have h3 : (fun t : ℝ => t * a / (d * (d + t))) =O[𝓝[≠] (0 : ℝ)] id := by
    have hbdd : (fun t : ℝ => a / (d * (d + t))) =O[𝓝[≠] (0 : ℝ)] (fun _ : ℝ => (1 : ℝ)) := by
      refine IsBigO.of_bound (|a| / (|d| * (|d| / 2))) ?_
      filter_upwards [hden_bd] with t hdt
      rw [Real.norm_eq_abs, abs_div, abs_mul, norm_one, mul_one]
      have hden : 0 < |d| * (|d| / 2) := mul_pos (abs_pos.mpr hd) (div_pos (abs_pos.mpr hd) two_pos)
      exact div_le_div₀ (abs_nonneg a) le_rfl hden
        (mul_le_mul_of_nonneg_left hdt (abs_nonneg d))
    have hmul : (fun t : ℝ => t * (a / (d * (d + t)))) =O[𝓝[≠] (0 : ℝ)] (fun t : ℝ => t * 1) :=
      (isBigO_refl (fun t : ℝ => t) (𝓝[≠] (0 : ℝ))).mul hbdd
    exact hmul.congr' (EventuallyEq.of_eq (funext fun t => by ring)) (EventuallyEq.of_eq (funext fun t => mul_one t))
  exact ((h1.add h2).add h3).congr' (hsplit.mono fun t ht => ht.symm) EventuallyEq.rfl

/-! ### Exact single-resolvent cancellation formula (Theorem CR.4 Step 1: `(CR.14a)` & `(CR.15)`) -/

/-- `D_t(u) = T(u) - G_{1/t}(u)` (`ce_cardinal_resolvent.tex`, eq. `(CR.14a)`). -/
noncomputable def cohnD (a t u : ℝ) : ℝ := cohnT a u - cohnG a t⁻¹ u

/-- `v(z) = (m(z) - a (z - a)) / (z - a)²` from `(CR.15)`. -/
noncomputable def cohnV (a z : ℝ) : ℝ := (cohnM z - a * (z - a)) / (z - a) ^ 2

/-- Coefficient `A_t(x)` in `(CR.15)`. -/
noncomputable def cohnAt (a t x : ℝ) : ℝ :=
  (x - a) * (x + airyZero 1) / ((x + a) ^ 2 * (x + airyZero 1 + t)) +
    t / (x + airyZero 1 + t) ^ 2 * (a / (x + a) - cohnV a (airyZero 1 + t))

/-- Coefficient `B_t(x)` in `(CR.15)`. -/
noncomputable def cohnBt (a t x : ℝ) : ℝ :=
  (-2 * (x + airyZero 1) ^ 2 + t * (a - x - 2 * airyZero 1)) /
    ((x + a) ^ 3 * (x + airyZero 1 + t) ^ 2)

/-- Coefficient `C_t(x)` in `(CR.15)`. -/
noncomputable def cohnCt (a t x : ℝ) : ℝ :=
  (x + airyZero 1) / ((x + a) ^ 2 * (x + airyZero 1 + t))

/-- **Theorem CR.4 Step 1, eq. `(CR.14a)`:**
`D_t(u) = ∑_n (E_n / (E_n + t)) c_n² L_n(u)²` for `t > 0`, `a` a zero of `Ai'`, `u ≠ a`. -/
theorem cohnD_hasSum {a t u : ℝ} (ha : airyAi' a = 0) (hua : u ≠ a) (ht : 0 < t) :
    HasSum (fun n : ℕ => cohnE n / (cohnE n + t) * cohnC a n ^ 2 * cohnL n u ^ 2)
      (cohnD a t u) := by
  have hT := (summable_cohnT ha hua).hasSum
  have hG := (summable_cohnG_of_nonneg ha hua (inv_pos.mpr ht).le).hasSum
  have hsub := hT.sub hG
  unfold cohnD cohnT cohnG
  convert hsub using 1
  funext n
  have hEn : 0 ≤ cohnE n := cohnE_nonneg n
  have hden1 : cohnE n + t ≠ 0 := by linarith
  have hden2 : 1 + t⁻¹ * cohnE n ≠ 0 := (one_add_mul_cohnE_pos (inv_pos.mpr ht).le n).ne'
  field_simp
  ring

/-- **Theorem CR.4 Step 1, eq. `(CR.15)`:** exact three-Airy formula for `D_t(-x)` at every
resolvent scale `t > 0` (`z = a_1 + t ≠ a`, `-x ∉ {a, a_1 + t}`). -/
theorem cohnD_neg_eq {a t x : ℝ} (ha : airyAi' a = 0) (ht : 0 < t)
    (hza : airyZero 1 + t ≠ a) (hxa : -x ≠ a) (hxz : -x ≠ airyZero 1 + t) :
    cohnD a t (-x) =
      cohnAt a t x * airyAi (-x) ^ 2 +
        cohnBt a t x * (airyAi (-x) * airyAi' (-x)) +
        cohnCt a t x * airyAi' (-x) ^ 2 := by
  have hG := cohnG_eq ha (inv_pos.mpr ht) (by simpa [inv_inv] using hza) hxa
    (by simpa [inv_inv] using hxz)
  have hT := cohnT_eq ha hxa
  unfold cohnD
  rw [hT, hG, closedResolventRHS_eq_three_airy]
  have hxa' : x + a ≠ 0 := by intro h; apply hxa; linarith
  have hza' : airyZero 1 + t - a ≠ 0 := sub_ne_zero.mpr hza
  have hxz' : x + airyZero 1 + t ≠ 0 := by intro h; apply hxz; linarith
  have ht0 : t ≠ 0 := ht.ne'
  unfold closedResolventCoeffA closedResolventCoeffB closedResolventCoeffC
    cohnAt cohnBt cohnCt cohnV
  dsimp only
  simp only [inv_inv]
  field_simp
  ring

/-- info: 'FormalResearch.CohnElkies.cohnG_neg_asymptotic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cohnG_neg_asymptotic

/-- info: 'FormalResearch.CohnElkies.cohnG_sub_first_asymptotic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cohnG_sub_first_asymptotic

/-- info: 'FormalResearch.CohnElkies.cohnM_airyZero_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cohnM_airyZero_expansion

/-- info: 'FormalResearch.CohnElkies.cohnMathfrakA_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cohnMathfrakA_expansion

/-- info: 'FormalResearch.CohnElkies.cohnD_hasSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cohnD_hasSum

/-- info: 'FormalResearch.CohnElkies.cohnD_neg_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cohnD_neg_eq

end FormalResearch.CohnElkies