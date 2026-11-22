module

public import FormalResearch.CohnElkies.CardinalFractionalSource
public import FormalResearch.CohnElkies.PreEdgeAndSplineFloor
public import FormalResearch.CohnElkies.CardinalAsymptotics
public import FormalResearch.CohnElkies.MellinKernel

/-!
# Airy Seed Floors, Hermite–Biehler Seed Family, and Small-`L` Edge Phase (`u1c_o1_upper.tex`)

Formalizes three foundational inputs from `CFT/sign_uncertainty/paper/u1c_o1_upper.tex` and
`u1c_estimate_proofs.tex` (on `origin/main`, commit `9b51a651f`):

* **Part 1 — Lemma `U.4a` (`u1c:U4a` / `lem:airy-seed-floor`):**
  exact integrals (`∫ f₁ = 0`, `∫ g₁ = 1`, `∫ g₁' = |a₁'|`), strict positivity of `g₁ + g₁'`
  everywhere on `ℝ`, the parameterized positive seed `ceSb b u := g₁ + g₁' - b f₁`, its
  `(e22)`–`(e23)` rational–Airy representation (`β₀₀ = b`, `β₁₁ = 1`, `β_∞(S_b) = 1 + b`) and
  Airy–WKB negative-axis expansion, and the global floor `S_b(u) ≥ C_b (1 + |u|)^{-3/2}` on `u ≤ a₁`.
* **Part 2 — Lemma `lem:hb-seed-mass`:**
  Hermite–Biehler seed package `HBSeedSpec`, construction of the rational–Airy family `F_δ` with
  prescribed integral `-v δ + r_δ`, Hypothesis `(H)` (`SatisfiesH`) at `u₀ = t_{m₀} - 2 γ₁ δ`,
  smoothing-gain corollary via `bspline_floor_smoothing_gain`, `δ / 2` floor near prescribed
  sites `t_j` (`j < m₀ - 1`), and an unconditional non-vacuity witness `hbSeedSpec_airy_witness`
  for `N = Ai` at `m₀ = 1`.
* **Part 3 — Lemma `O.4` (`u1co:O4`) Part (1) & real-axis derivative floor (`(3)`):**
  the imaginary-axis edge phase `edgePhi`, unique saddle `tau0 L`, cubic normal-form scale
  `edgeAlphaTilde L` and `edgeKappa0 L := edgeAlphaTilde L / L` with `1 < edgeKappa0 L ≤ 1 + L / 4`
  on `L ∈ (0, 0.002]`, `2 * tau0 L < 0.0989 < 0.128`, and `-edgePhiDeriv L τ ≥ 0.011` for
  `0.128 ≤ |τ|`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.CohnElkies

open FormalResearch.Special

/-! ### Part 1: Lemma `U.4a` (`u1c:U4a` / `lem:airy-seed-floor`) -/

/-- The parameterized positive Airy seed `S_b = g₁ + g₁' - b f₁` (`u1c_o1_upper.tex`, `u1c:U4a`). -/
noncomputable def ceSb (b u : ℝ) : ℝ :=
  ceG1 (airyZero 1) u + ceG1Deriv airyDerivFirstZero u - b * ceF1 u

private lemma continuous_dslope_airyAi (a : ℝ) : Continuous (dslope airyAi a) := by
  rw [← continuousOn_univ, continuousOn_dslope univ_mem]
  exact ⟨differentiable_airyAi.continuous.continuousOn, differentiable_airyAi a⟩

private lemma continuous_dslope_airyAi' (a : ℝ) : Continuous (dslope airyAi' a) := by
  have hd : Differentiable ℝ airyAi' := fun x => (hasDerivAt_airyAi' x).differentiableAt
  rw [← continuousOn_univ, continuousOn_dslope univ_mem]
  exact ⟨hd.continuous.continuousOn, hd a⟩

lemma continuous_ceG1 (a1 : ℝ) : Continuous (ceG1 a1) := (continuous_dslope_airyAi a1).pow 2
lemma continuous_ceG1Deriv (a1' : ℝ) : Continuous (ceG1Deriv a1') := (continuous_dslope_airyAi' a1').pow 2
lemma continuous_ceF1 : Continuous ceF1 :=
  differentiable_airyAi.continuous.mul (continuous_dslope_airyAi (airyZero 1))
lemma continuous_ceSb (b : ℝ) : Continuous (ceSb b) :=
  (continuous_ceS0 (airyZero 1) airyDerivFirstZero).sub (continuous_const.mul continuous_ceF1)

private lemma ceG1_eq_cohnL_sq (u : ℝ) : ceG1 (airyZero 1) u = cohnL 0 u * cohnL 0 u := by
  unfold ceG1
  have h : dslope airyAi (airyZero 1) u = cohnL 0 u := by
    by_cases hu : u = airyZero 1
    · subst hu; rw [dslope_same, (hasDerivAt_airyAi _).deriv, cohnL_self]
    · rw [dslope_of_ne _ hu, slope_def_field, airyAi_airyZero, sub_zero, cohnL_of_ne (by simpa using hu)]
  rw [h, sq]

lemma ceG1_integrable : Integrable (ceG1 (airyZero 1)) := by
  rw [funext ceG1_eq_cohnL_sq]; exact (cohnL_integral_mul 0 0).1

lemma ceG1_integral_eq_one : ∫ u : ℝ, ceG1 (airyZero 1) u = 1 := by
  simp_rw [ceG1_eq_cohnL_sq]; exact (cohnL_integral_mul 0 0).2

/-- **Lemma `U.4a(1)` (`u1c:U4a`):** exact real-axis integrals of `f₁`, `g₁`, and `g₁'`. -/
theorem airy_seed_integrals :
    (Integrable ceF1 ∧ ∫ u : ℝ, ceF1 u = 0) ∧
    (Integrable (ceG1 (airyZero 1)) ∧ ∫ u : ℝ, ceG1 (airyZero 1) u = 1) ∧
    (Integrable (ceG1Deriv airyDerivFirstZero) ∧
      ∫ u : ℝ, ceG1Deriv airyDerivFirstZero u = |airyDerivFirstZero|) := by
  have hG' := ceG1Deriv_integral_eq_M
  rw [← abs_of_neg airyDerivFirstZero_spec.2.1] at hG'
  exact ⟨ceF1_integral_eq_zero, ⟨ceG1_integrable, ceG1_integral_eq_one⟩, hG'⟩

lemma ceSb_integrable (b : ℝ) : Integrable (ceSb b) :=
  (ceS0_integrable (airyAi_airyZero 1) airyDerivFirstZero_spec.2.2).sub
    (ceF1_integral_eq_zero.1.const_mul b)

lemma ceSb_integral (b : ℝ) : ∫ u : ℝ, ceSb b u = 1 + |airyDerivFirstZero| := by
  have h1 := integral_sub (ceS0_integrable (airyAi_airyZero 1) airyDerivFirstZero_spec.2.2)
    (ceF1_integral_eq_zero.1.const_mul b)
  have h2 := integral_add ceG1_integrable ceG1Deriv_integral_eq_M.1
  change ∫ u : ℝ, ceSb b u = (∫ u : ℝ, ceG1 (airyZero 1) u + ceG1Deriv airyDerivFirstZero u) -
    ∫ u : ℝ, b * ceF1 u at h1
  rw [h1, h2, ceG1_integral_eq_one, airy_seed_integrals.2.2.2,
    integral_const_mul, ceF1_integral_eq_zero.2, mul_zero, sub_zero]

/-- `g₁(u) + g₁'(u) > 0` for all `u ∈ ℝ` (`u1c:U4a`). -/
theorem ceG1_add_ceG1Deriv_pos (u : ℝ) :
    0 < ceG1 (airyZero 1) u + ceG1Deriv airyDerivFirstZero u :=
  ceS0_pos (airyZero 1) airyDerivFirstZero (airyAi_airyZero 1) airyDerivFirstZero_spec.2.2 u

lemma ceF1_nonpos_of_le {u : ℝ} (hu : u ≤ airyZero 1) : ceF1 u ≤ 0 := by
  unfold ceF1
  rcases eq_or_lt_of_le hu with rfl | hlt
  · simp [airyAi_airyZero]
  · rw [dslope_of_ne _ hlt.ne, slope_def_field, airyAi_airyZero, sub_zero, ← mul_div_assoc, ← sq]
    exact div_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (sub_neg.mpr hlt).le

lemma ceG1_le_ceSb {b u : ℝ} (hb : 0 ≤ b) (hu : u ≤ airyZero 1) : ceG1 (airyZero 1) u ≤ ceSb b u := by
  unfold ceSb
  have hg' : 0 ≤ ceG1Deriv airyDerivFirstZero u := sq_nonneg _
  have hf : b * ceF1 u ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb (ceF1_nonpos_of_le hu)
  linarith

lemma ceSb_pos_of_le {b u : ℝ} (hb : 0 ≤ b) (hu : u ≤ airyZero 1) : 0 < ceSb b u := by
  have hS0 := ceG1_add_ceG1Deriv_pos u
  have hf : b * ceF1 u ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb (ceF1_nonpos_of_le hu)
  unfold ceSb; linarith

private lemma inv_add_sub_inv_le {x a : ℝ} (hx : 5 ≤ x) (_ha1 : -2.35 < a) (ha2 : a < 0) :
    |(x + a)⁻¹ - x⁻¹| ≤ 5 * x ^ (-2 : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hsep : x / 2 ≤ x + a := by linarith
  have hpos : 0 < x + a := by linarith
  have heq : (x + a)⁻¹ - x⁻¹ = -a / (x * (x + a)) := by field_simp [hx0.ne', hpos.ne']; ring
  rw [heq, abs_div, abs_of_pos (mul_pos hx0 hpos), abs_neg, abs_of_neg ha2,
    show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg hx0.le, Real.rpow_two, sq]
  calc -a / (x * (x + a)) ≤ 2.35 / (x * (x / 2)) :=
        div_le_div₀ (by positivity) (by linarith) (by positivity) (mul_le_mul_of_nonneg_left hsep hx0.le)
    _ = 4.7 * (x * x)⁻¹ := by ring
    _ ≤ 5 * (x * x)⁻¹ := by gcongr; norm_num

private lemma inv_add_sq_sub_inv_sq_le {x a : ℝ} (hx : 5 ≤ x) (ha1 : -2.35 < a) (ha2 : a < 0) :
    |(x + a) ^ (-2 : ℤ) - x ^ (-2 : ℝ)| ≤ 44 * x ^ (-3 : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hsep : x / 2 ≤ x + a := by linarith
  have hpos : 0 < x + a := by linarith
  have heq : (x + a) ^ (-2 : ℤ) - x ^ (-2 : ℝ) = (-2 * a * x - a ^ 2) / (x ^ 2 * (x + a) ^ 2) := by
    rw [zpow_neg, zpow_two, show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg hx0.le,
      show x ^ (2 : ℝ) = x ^ 2 by norm_cast]
    field_simp [hx0.ne', hpos.ne']; ring
  rw [heq, abs_div, abs_of_pos (by positivity : 0 < x ^ 2 * (x + a) ^ 2),
    show (-3 : ℝ) = -(3 : ℝ) by norm_num, Real.rpow_neg hx0.le, show x ^ (3 : ℝ) = x ^ 3 by norm_cast]
  have hnum : |-2 * a * x - a ^ 2| ≤ 11 * x := by
    have h1 : |-2 * a * x| ≤ 5 * x := by
      rw [abs_mul, abs_mul, abs_neg, abs_two, abs_of_neg ha2, abs_of_pos hx0]; nlinarith
    have h2 : |a ^ 2| ≤ 6 * x := by rw [abs_sq]; nlinarith
    exact (abs_sub _ _).trans (by linarith)
  have hden : x ^ 4 / 4 ≤ x ^ 2 * (x + a) ^ 2 := by
    have hsq := pow_le_pow_left₀ (by positivity) hsep 2
    nlinarith [mul_le_mul_of_nonneg_left hsq (sq_nonneg x)]
  calc |-2 * a * x - a ^ 2| / (x ^ 2 * (x + a) ^ 2)
      ≤ (11 * x) / (x ^ 4 / 4) := div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = 44 * (x ^ 3)⁻¹ := by field_simp [hx0.ne']; ring

private lemma airyAi_neg_sq_err {x : ℝ} (hx : 1 ≤ x) :
    |airyAi (-x) ^ 2 - Real.sin (cohnTheta x) ^ 2 / (π * x ^ (1 / 2 : ℝ))| ≤ 3 / 8 * x ^ (-2 : ℝ) ∧
    airyAi (-x) ^ 2 ≤ x ^ (-(1 / 2 : ℝ)) := by
  have hx0 : 0 < x := by linarith
  have hpi : (1 : ℝ) ≤ √π := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
  have hx14 : 1 ≤ x ^ (1 / 4 : ℝ) := Real.one_le_rpow hx (by norm_num)
  have hx14_pos : 0 < x ^ (1 / 4 : ℝ) := by positivity
  have hx74 : x ^ (1 / 4 : ℝ) ≤ x ^ (7 / 4 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  set L := Real.sin (cohnTheta x) / (√π * x ^ (1 / 4 : ℝ))
  have hAi := airyAi_neg_asymptotic_theta hx0
  have hL : |L| ≤ (x ^ (1 / 4 : ℝ))⁻¹ := by
    dsimp [L]; rw [abs_div, abs_of_pos (mul_pos (Real.sqrt_pos.mpr Real.pi_pos) hx14_pos)]
    have h1 := div_le_div_of_nonneg_right (Real.abs_sin_le_one (cohnTheta x))
      (mul_nonneg (Real.sqrt_nonneg π) hx14_pos.le)
    have h2 : 1 / (√π * x ^ (1 / 4 : ℝ)) ≤ (x ^ (1 / 4 : ℝ))⁻¹ := by
      rw [one_div]
      exact inv_anti₀ hx14_pos (le_mul_of_one_le_left hx14_pos.le hpi)
    exact h1.trans h2
  have hsum : |airyAi (-x) + L| ≤ 3 * (x ^ (1 / 4 : ℝ))⁻¹ := by
    have htri := abs_add_le (airyAi (-x) - L) (2 * L)
    rw [show airyAi (-x) - L + 2 * L = airyAi (-x) + L by ring, abs_mul,
      (abs_of_pos two_pos : |(2 : ℝ)| = 2)] at htri
    have hinv74 : 1 / (8 * x ^ (7 / 4 : ℝ)) ≤ (x ^ (1 / 4 : ℝ))⁻¹ := by
      rw [one_div]; exact inv_anti₀ hx14_pos (by nlinarith)
    linarith
  have hsq : |airyAi (-x) ^ 2 - L ^ 2| ≤ 3 / 8 * x ^ (-2 : ℝ) := by
    rw [show airyAi (-x) ^ 2 - L ^ 2 = (airyAi (-x) - L) * (airyAi (-x) + L) by ring, abs_mul]
    have hcomb : (1 / (8 * x ^ (7 / 4 : ℝ))) * (3 * (x ^ (1 / 4 : ℝ))⁻¹) = 3 / 8 * x ^ (-2 : ℝ) := by
      rw [show (-2 : ℝ) = -(7 / 4 + 1 / 4) by norm_num, Real.rpow_neg hx0.le, Real.rpow_add hx0]; ring
    calc |airyAi (-x) - L| * |airyAi (-x) + L|
        ≤ (1 / (8 * x ^ (7 / 4 : ℝ))) * (3 * (x ^ (1 / 4 : ℝ))⁻¹) :=
          mul_le_mul hAi hsum (abs_nonneg _) (by positivity)
      _ = 3 / 8 * x ^ (-2 : ℝ) := hcomb
  have hLsq : L ^ 2 = Real.sin (cohnTheta x) ^ 2 / (π * x ^ (1 / 2 : ℝ)) := by
    dsimp [L]
    have hx12 : (x ^ (1 / 4 : ℝ)) ^ 2 = x ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
    rw [div_pow, mul_pow, Real.sq_sqrt Real.pi_pos.le, hx12]
  rw [← hLsq]
  refine ⟨hsq, ?_⟩
  have h1 : L ^ 2 ≤ 1 / π * x ^ (-(1 / 2 : ℝ)) := by
    rw [hLsq, Real.rpow_neg hx0.le]
    calc Real.sin (cohnTheta x) ^ 2 / (π * x ^ (1 / 2 : ℝ))
        ≤ 1 / (π * x ^ (1 / 2 : ℝ)) := div_le_div_of_nonneg_right
          ((sq_le_one_iff_abs_le_one _).mpr (Real.abs_sin_le_one _)) (by positivity)
      _ = 1 / π * (x ^ (1 / 2 : ℝ))⁻¹ := by ring
  have h2 : x ^ (-2 : ℝ) ≤ x ^ (-(1 / 2 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have hpi3 : (1 / π : ℝ) < 1 / 3 := div_lt_div_of_pos_left one_pos (by norm_num) Real.pi_gt_three
  have hsq_le : airyAi (-x) ^ 2 ≤ L ^ 2 + 3 / 8 * x ^ (-2 : ℝ) := by linarith [(abs_le.mp hsq).2]
  have hxneg_nn : 0 ≤ x ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hx0.le _
  nlinarith

private lemma airyAi'_neg_sq_err {x : ℝ} (hx : 1 ≤ x) :
    |airyAi' (-x) ^ 2 - x ^ (1 / 2 : ℝ) * Real.cos (cohnTheta x) ^ 2 / π| ≤ 6 / 5 * x ^ (-1 : ℝ) ∧
    airyAi' (-x) ^ 2 ≤ x ^ (1 / 2 : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hpi : (1 : ℝ) ≤ √π := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
  have hx14 : 1 ≤ x ^ (1 / 4 : ℝ) := Real.one_le_rpow hx (by norm_num)
  have hx14_pos : 0 < x ^ (1 / 4 : ℝ) := by positivity
  set L := -(x ^ (1 / 4 : ℝ) * Real.cos (cohnTheta x) / √π)
  have hAi' : |airyAi' (-x) - L| ≤ 2 / (5 * x ^ (5 / 4 : ℝ)) := by
    simpa [L, sub_neg_eq_add] using airyAi'_neg_asymptotic_theta hx0
  have hL_pi : |L| ≤ 1 / √π * x ^ (1 / 4 : ℝ) := by
    dsimp [L]; rw [abs_neg, abs_div, abs_mul, abs_of_pos hx14_pos, abs_of_pos (Real.sqrt_pos.mpr Real.pi_pos)]
    calc x ^ (1 / 4 : ℝ) * |Real.cos (cohnTheta x)| / √π
        ≤ x ^ (1 / 4 : ℝ) * 1 / √π := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) hx14_pos.le) (by positivity)
      _ = 1 / √π * x ^ (1 / 4 : ℝ) := by ring
  have hL : |L| ≤ x ^ (1 / 4 : ℝ) := by
    have : 1 / √π ≤ 1 := div_le_one_of_le₀ hpi (by positivity)
    exact hL_pi.trans (by simpa using mul_le_mul_of_nonneg_right this hx14_pos.le)
  have hsum : |airyAi' (-x) + L| ≤ 3 * x ^ (1 / 4 : ℝ) := by
    have htri := abs_add_le (airyAi' (-x) - L) (2 * L)
    rw [show airyAi' (-x) - L + 2 * L = airyAi' (-x) + L by ring, abs_mul,
      (abs_of_pos two_pos : |(2 : ℝ)| = 2)] at htri
    have h25 : 2 / (5 * x ^ (5 / 4 : ℝ)) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [Real.one_le_rpow hx (by norm_num : (0 : ℝ) ≤ 5 / 4)]
    linarith
  have hLsq : L ^ 2 = x ^ (1 / 2 : ℝ) * Real.cos (cohnTheta x) ^ 2 / π := by
    dsimp [L]
    have hx12 : (x ^ (1 / 4 : ℝ)) ^ 2 = x ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
    rw [neg_sq, div_pow, mul_pow, hx12, Real.sq_sqrt Real.pi_pos.le]
  have hsq : |airyAi' (-x) ^ 2 - L ^ 2| ≤ 6 / 5 * x ^ (-1 : ℝ) := by
    rw [show airyAi' (-x) ^ 2 - L ^ 2 = (airyAi' (-x) - L) * (airyAi' (-x) + L) by ring, abs_mul]
    have hcomb : (2 / (5 * x ^ (5 / 4 : ℝ))) * (3 * x ^ (1 / 4 : ℝ)) = 6 / 5 * x ^ (-1 : ℝ) := by
      rw [show (-1 : ℝ) = 1 / 4 - 5 / 4 by norm_num, Real.rpow_sub hx0]; ring
    calc |airyAi' (-x) - L| * |airyAi' (-x) + L|
        ≤ (2 / (5 * x ^ (5 / 4 : ℝ))) * (3 * x ^ (1 / 4 : ℝ)) :=
          mul_le_mul hAi' hsum (abs_nonneg _) (by positivity)
      _ = 6 / 5 * x ^ (-1 : ℝ) := hcomb
  rw [← hLsq]; refine ⟨hsq, ?_⟩
  have hAi'_abs : |airyAi' (-x)| ≤ (1 / √π + 2 / 5) * x ^ (1 / 4 : ℝ) := by
    have htri := abs_add_le (airyAi' (-x) - L) L
    rw [sub_add_cancel] at htri
    have h54 : 2 / (5 * x ^ (5 / 4 : ℝ)) ≤ 2 / 5 * x ^ (1 / 4 : ℝ) := by
      calc 2 / (5 * x ^ (5 / 4 : ℝ)) = 2 / 5 * (x ^ (5 / 4 : ℝ))⁻¹ := by ring
        _ ≤ 2 / 5 * 1 := mul_le_mul_of_nonneg_left
            (inv_le_one_of_one_le₀ (Real.one_le_rpow hx (by norm_num))) (by norm_num)
        _ ≤ 2 / 5 * x ^ (1 / 4 : ℝ) := mul_le_mul_of_nonneg_left hx14 (by norm_num)
    linarith
  have hpi_sqrt : (17 / 10 : ℝ) ≤ √π := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 17 / 10)]
    exact Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
  have hc_lt : 1 / √π + 2 / 5 ≤ 1 := by
    have : 1 / √π ≤ 10 / 17 := by rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
    linarith
  have hx12 : (x ^ (1 / 4 : ℝ)) ^ 2 = x ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  calc airyAi' (-x) ^ 2 = |airyAi' (-x)| ^ 2 := (sq_abs _).symm
    _ ≤ (1 * x ^ (1 / 4 : ℝ)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _)
        (hAi'_abs.trans (mul_le_mul_of_nonneg_right hc_lt hx14_pos.le)) 2
    _ = x ^ (1 / 2 : ℝ) := by rw [one_mul, hx12]

/-- **`(e22)`–`(e23)` rational–Airy representation of `ceSb b` on `u < airyZero 1`:**
`S_b(u) = R₀₀(u) Ai(u)² + R₀₁(u) Ai(u) Ai'(u) + R₁₁(u) Ai'(u)²` with `R₀₁ = 0`,
`R₀₀(-x) = b x⁻¹ + O(x⁻²)`, `R₁₁(-x) = x⁻² + O(x⁻³)`, so `β₀₀ = b`, `β₁₁ = 1`, `β_∞(S_b) = 1 + b`. -/
theorem ceSb_e23_rational_form (b : ℝ) :
    ∃ (R00 R01 R11 : ℝ → ℝ) (C0 C1 : ℝ), 0 ≤ C0 ∧ 0 ≤ C1 ∧
      (∀ u < airyZero 1,
        ceSb b u = R00 u * airyAi u ^ 2 + R01 u * (airyAi u * airyAi' u) + R11 u * airyAi' u ^ 2) ∧
      (∀ x ≥ (5 : ℝ),
        |R00 (-x) - b * x⁻¹| ≤ C0 * x ^ (-2 : ℝ) ∧ R01 (-x) = 0 ∧
        |R11 (-x) - x ^ (-2 : ℝ)| ≤ C1 * x ^ (-3 : ℝ)) := by
  let a1 : ℝ := airyZero 1; let a1' : ℝ := airyDerivFirstZero
  let R00 : ℝ → ℝ := fun u => (u - a1) ^ (-2 : ℤ) - b * (u - a1)⁻¹
  let R01 : ℝ → ℝ := fun _ => 0
  let R11 : ℝ → ℝ := fun u => (u - a1') ^ (-2 : ℤ)
  refine ⟨R00, R01, R11, 5 * |b| + 4, 44, by positivity, by norm_num, ?_, ?_⟩
  · intro u hu
    have hne1 : u ≠ a1 := hu.ne
    have hne2 : u ≠ a1' := (hu.trans airyDerivFirstZero_spec.1).ne
    have hg1 : ceG1 a1 u = (u - a1) ^ (-2 : ℤ) * airyAi u ^ 2 := by
      rw [ceG1, dslope_of_ne _ hne1, slope_def_field, airyAi_airyZero, sub_zero,
        div_pow, zpow_neg, zpow_two, ← sq]; ring
    have hf1 : ceF1 u = (u - a1)⁻¹ * airyAi u ^ 2 := by
      rw [ceF1, dslope_of_ne _ hne1, slope_def_field, airyAi_airyZero, sub_zero]
      field_simp [sub_ne_zero.mpr hne1]
    have hg1' : ceG1Deriv a1' u = (u - a1') ^ (-2 : ℤ) * airyAi' u ^ 2 := by
      rw [ceG1Deriv, dslope_of_ne _ hne2, slope_def_field, airyDerivFirstZero_spec.2.2, sub_zero,
        div_pow, zpow_neg, zpow_two, ← sq]; ring
    dsimp [R00, R01, R11]; rw [ceSb, hg1, hf1, hg1']; ring
  · intro x hx
    have hx0 : 0 < x := by linarith
    have ha1_lo : -2.35 < a1 := airyZero_one.1
    have ha1_hi : a1 < 0 := airyZero_neg 1
    have ha1'_lo : -2.35 < a1' := ha1_lo.trans airyDerivFirstZero_spec.1
    have ha1'_hi : a1' < 0 := airyDerivFirstZero_spec.2.1
    have hinv1 : |(-x - a1)⁻¹ - (-x⁻¹)| ≤ 5 * x ^ (-2 : ℝ) := by
      have hpos1 : 0 < x + a1 := by linarith
      have hneg1 : -x - a1 ≠ 0 := by linarith
      have h_eq : (-x - a1)⁻¹ - (-x⁻¹) = -((x + a1)⁻¹ - x⁻¹) := by
        field_simp [hx0.ne', hpos1.ne', hneg1]; ring
      rw [h_eq, abs_neg]
      exact inv_add_sub_inv_le hx ha1_lo ha1_hi
    have hinv2 : |(-x - a1) ^ (-2 : ℤ)| ≤ 4 * x ^ (-2 : ℝ) := by
      rw [zpow_neg, zpow_two, ← sq, abs_inv, abs_sq, show (-2 : ℝ) = -(2 : ℝ) by norm_num,
        Real.rpow_neg hx0.le, Real.rpow_two, show (-x - a1) ^ 2 = (x + a1) ^ 2 by ring]
      calc ((x + a1) ^ 2)⁻¹ ≤ ((x / 2) ^ 2)⁻¹ :=
            inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith) 2)
        _ = 4 * (x ^ 2)⁻¹ := by ring
    have hR00 : |R00 (-x) - b * x⁻¹| ≤ (5 * |b| + 4) * x ^ (-2 : ℝ) := by
      rw [show R00 (-x) - b * x⁻¹ = (-x - a1) ^ (-2 : ℤ) - b * ((-x - a1)⁻¹ - (-x⁻¹)) by
        dsimp [R00]; ring]
      have htri := abs_sub ((-x - a1) ^ (-2 : ℤ)) (b * ((-x - a1)⁻¹ - (-x⁻¹)))
      rw [abs_mul] at htri
      calc _ ≤ |(-x - a1) ^ (-2 : ℤ)| + |b| * |(-x - a1)⁻¹ - (-x⁻¹)| := htri
        _ ≤ 4 * x ^ (-2 : ℝ) + |b| * (5 * x ^ (-2 : ℝ)) :=
              add_le_add hinv2 (mul_le_mul_of_nonneg_left hinv1 (abs_nonneg _))
        _ = (5 * |b| + 4) * x ^ (-2 : ℝ) := by ring
    have hR11 : |R11 (-x) - x ^ (-2 : ℝ)| ≤ 44 * x ^ (-3 : ℝ) := by
      rw [show R11 (-x) = (x + a1') ^ (-2 : ℤ) by
        dsimp [R11]; rw [zpow_neg, zpow_neg, zpow_two, zpow_two]; ring]
      exact inv_add_sq_sub_inv_sq_le hx ha1'_lo ha1'_hi
    exact ⟨hR00, rfl, hR11⟩

/-- **Lemma `U.4a(2)`, Airy–WKB expansion (`u1c_o1_upper.tex`, `u1c:U4a`):**
for `x ≥ 5`, both `-b f₁(-x) + g₁'(-x)` and `S_b(-x)` equal
`π⁻¹ x^{-3/2} (b sin² ϑ(x) + cos² ϑ(x) + R(x))` with `|R(x)| ≤ C x⁻¹`. -/
theorem ceSb_neg_asymptotic (b : ℝ) :
    ∃ R0 R : ℝ → ℝ, ∃ C : ℝ, 0 < C ∧ ∀ x ≥ (5 : ℝ),
      (-b * ceF1 (-x) + ceG1Deriv airyDerivFirstZero (-x) =
        π⁻¹ * x ^ (-(3 / 2 : ℝ)) * (b * Real.sin (cohnTheta x) ^ 2 + Real.cos (cohnTheta x) ^ 2 + R0 x)) ∧
      (ceSb b (-x) =
        π⁻¹ * x ^ (-(3 / 2 : ℝ)) * (b * Real.sin (cohnTheta x) ^ 2 + Real.cos (cohnTheta x) ^ 2 + R x)) ∧
      |R0 x| ≤ C * x⁻¹ ∧ |R x| ≤ C * x⁻¹ := by
  let a1 : ℝ := airyZero 1; let a1' : ℝ := airyDerivFirstZero
  let C : ℝ := π * (6 * |b| + 50)
  let R0 : ℝ → ℝ := fun x =>
    π * x ^ (3 / 2 : ℝ) * (-b * ceF1 (-x) + ceG1Deriv a1' (-x)) -
      (b * Real.sin (cohnTheta x) ^ 2 + Real.cos (cohnTheta x) ^ 2)
  let R : ℝ → ℝ := fun x =>
    π * x ^ (3 / 2 : ℝ) * ceSb b (-x) -
      (b * Real.sin (cohnTheta x) ^ 2 + Real.cos (cohnTheta x) ^ 2)
  refine ⟨R0, R, C, by positivity [Real.pi_pos], fun x hx => ?_⟩
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hpi0 : π ≠ 0 := Real.pi_ne_zero
  have hxp32 : x ^ (3 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hx0 _).ne'
  have hx_mul : π⁻¹ * x ^ (-(3 / 2 : ℝ)) * (π * x ^ (3 / 2 : ℝ)) = 1 := by
    rw [Real.rpow_neg hx0.le]; field_simp [hpi0, hxp32]
  have heq0 : -b * ceF1 (-x) + ceG1Deriv a1' (-x) =
      π⁻¹ * x ^ (-(3 / 2 : ℝ)) * (b * Real.sin (cohnTheta x) ^ 2 + Real.cos (cohnTheta x) ^ 2 + R0 x) := by
    dsimp [R0]
    rw [show _ + (_ - _) = π * x ^ (3 / 2 : ℝ) * (-b * ceF1 (-x) + ceG1Deriv a1' (-x)) by ring,
      ← mul_assoc, hx_mul, one_mul]
  have heqS : ceSb b (-x) =
      π⁻¹ * x ^ (-(3 / 2 : ℝ)) * (b * Real.sin (cohnTheta x) ^ 2 + Real.cos (cohnTheta x) ^ 2 + R x) := by
    dsimp [R]
    rw [show _ + (_ - _) = π * x ^ (3 / 2 : ℝ) * ceSb b (-x) by ring, ← mul_assoc, hx_mul, one_mul]
  have ha1_lo : -2.35 < a1 := airyZero_one.1
  have ha1_hi : a1 < 0 := airyZero_neg 1
  have ha1'_lo : -2.35 < a1' := ha1_lo.trans airyDerivFirstZero_spec.1
  have ha1'_hi : a1' < 0 := airyDerivFirstZero_spec.2.1
  have hpos1 : 0 < x + a1 := by linarith
  have hpos2 : 0 < x + a1' := by linarith
  have hne1 : -x ≠ a1 := by linarith
  have hne2 : -x ≠ a1' := by linarith
  obtain ⟨hAi_err, hAi_sq⟩ := airyAi_neg_sq_err hx1
  obtain ⟨hAi'_err, hAi'_sq⟩ := airyAi'_neg_sq_err hx1
  have hf_err : |-ceF1 (-x) - Real.sin (cohnTheta x) ^ 2 / (π * x ^ (3 / 2 : ℝ))| ≤ 6 * x ^ (-(5 / 2 : ℝ)) := by
    have hf_eq : -ceF1 (-x) = (x + a1)⁻¹ * airyAi (-x) ^ 2 := by
      rw [ceF1, dslope_of_ne _ hne1, slope_def_field, airyAi_airyZero, sub_zero,
        show -x - a1 = -(x + a1) by ring]
      field_simp [hpos1.ne']
    have h1 : x⁻¹ * (Real.sin (cohnTheta x) ^ 2 / (π * x ^ (1 / 2 : ℝ))) =
        Real.sin (cohnTheta x) ^ 2 / (π * x ^ (3 / 2 : ℝ)) := by
      have hx32 : x * x ^ (1 / 2 : ℝ) = x ^ (3 / 2 : ℝ) := by
        conv_lhs => lhs; rw [← Real.rpow_one x]
        rw [← Real.rpow_add hx0]; norm_num
      rw [← hx32]; ring
    have hpow1 : x⁻¹ * x ^ (-2 : ℝ) ≤ x ^ (-(5 / 2 : ℝ)) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hx0]; exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    have hpow2 : x ^ (-2 : ℝ) * x ^ (-(1 / 2 : ℝ)) = x ^ (-(5 / 2 : ℝ)) := by
      rw [← Real.rpow_add hx0]; norm_num
    rw [show -ceF1 (-x) - Real.sin (cohnTheta x) ^ 2 / (π * x ^ (3 / 2 : ℝ)) =
        x⁻¹ * (airyAi (-x) ^ 2 - Real.sin (cohnTheta x) ^ 2 / (π * x ^ (1 / 2 : ℝ))) +
          ((x + a1)⁻¹ - x⁻¹) * airyAi (-x) ^ 2 by rw [hf_eq, ← h1]; ring]
    have htri := abs_add_le
      (x⁻¹ * (airyAi (-x) ^ 2 - Real.sin (cohnTheta x) ^ 2 / (π * x ^ (1 / 2 : ℝ))))
      (((x + a1)⁻¹ - x⁻¹) * airyAi (-x) ^ 2)
    rw [abs_mul, abs_mul, abs_inv, abs_of_pos hx0, abs_of_nonneg (sq_nonneg (airyAi (-x)))] at htri
    calc _ ≤ x⁻¹ * |airyAi (-x) ^ 2 - Real.sin (cohnTheta x) ^ 2 / (π * x ^ (1 / 2 : ℝ))| +
            |(x + a1)⁻¹ - x⁻¹| * airyAi (-x) ^ 2 := htri
      _ ≤ x⁻¹ * (3 / 8 * x ^ (-2 : ℝ)) + (5 * x ^ (-2 : ℝ)) * x ^ (-(1 / 2 : ℝ)) :=
          add_le_add (mul_le_mul_of_nonneg_left hAi_err (inv_nonneg.mpr hx0.le))
            (mul_le_mul (inv_add_sub_inv_le hx ha1_lo ha1_hi) hAi_sq (sq_nonneg _) (by positivity))
      _ ≤ 6 * x ^ (-(5 / 2 : ℝ)) := by rw [← hpow2]; nlinarith [hpow1, Real.rpow_nonneg hx0.le (-(5 / 2 : ℝ))]
  have hg'_err : |ceG1Deriv a1' (-x) - Real.cos (cohnTheta x) ^ 2 / (π * x ^ (3 / 2 : ℝ))| ≤
      46 * x ^ (-(5 / 2 : ℝ)) := by
    have hg'_eq : ceG1Deriv a1' (-x) = (x + a1') ^ (-2 : ℤ) * airyAi' (-x) ^ 2 := by
      rw [ceG1Deriv, dslope_of_ne _ hne2, slope_def_field, airyDerivFirstZero_spec.2.2, sub_zero,
        div_pow, zpow_neg, zpow_two, ← sq, show (-x - a1') ^ 2 = (x + a1') ^ 2 by ring]; ring
    have h1 : x ^ (-2 : ℝ) * (x ^ (1 / 2 : ℝ) * Real.cos (cohnTheta x) ^ 2 / π) =
        Real.cos (cohnTheta x) ^ 2 / (π * x ^ (3 / 2 : ℝ)) := by
      have hx_div : x ^ (-2 : ℝ) * x ^ (1 / 2 : ℝ) = (x ^ (3 / 2 : ℝ))⁻¹ := by
        rw [← Real.rpow_neg hx0.le, ← Real.rpow_add hx0]; norm_num
      calc _ = (x ^ (-2 : ℝ) * x ^ (1 / 2 : ℝ)) * Real.cos (cohnTheta x) ^ 2 / π := by ring
        _ = _ := by rw [hx_div]; ring
    have hpow1 : x ^ (-2 : ℝ) * x ^ (-1 : ℝ) ≤ x ^ (-(5 / 2 : ℝ)) := by
      rw [← Real.rpow_add hx0]; exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    have hpow2 : x ^ (-3 : ℝ) * x ^ (1 / 2 : ℝ) = x ^ (-(5 / 2 : ℝ)) := by
      rw [← Real.rpow_add hx0]; norm_num
    rw [show ceG1Deriv a1' (-x) - Real.cos (cohnTheta x) ^ 2 / (π * x ^ (3 / 2 : ℝ)) =
        x ^ (-2 : ℝ) * (airyAi' (-x) ^ 2 - x ^ (1 / 2 : ℝ) * Real.cos (cohnTheta x) ^ 2 / π) +
          ((x + a1') ^ (-2 : ℤ) - x ^ (-2 : ℝ)) * airyAi' (-x) ^ 2 by rw [hg'_eq, ← h1]; ring]
    have htri := abs_add_le
      (x ^ (-2 : ℝ) * (airyAi' (-x) ^ 2 - x ^ (1 / 2 : ℝ) * Real.cos (cohnTheta x) ^ 2 / π))
      (((x + a1') ^ (-2 : ℤ) - x ^ (-2 : ℝ)) * airyAi' (-x) ^ 2)
    rw [abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hx0 (-2 : ℝ)),
      abs_of_nonneg (sq_nonneg (airyAi' (-x)))] at htri
    calc _ ≤ x ^ (-2 : ℝ) * |airyAi' (-x) ^ 2 - x ^ (1 / 2 : ℝ) * Real.cos (cohnTheta x) ^ 2 / π| +
            |(x + a1') ^ (-2 : ℤ) - x ^ (-2 : ℝ)| * airyAi' (-x) ^ 2 := htri
      _ ≤ x ^ (-2 : ℝ) * (6 / 5 * x ^ (-1 : ℝ)) + (44 * x ^ (-3 : ℝ)) * x ^ (1 / 2 : ℝ) :=
          add_le_add (mul_le_mul_of_nonneg_left hAi'_err (Real.rpow_nonneg hx0.le _))
            (mul_le_mul (inv_add_sq_sub_inv_sq_le hx ha1'_lo ha1'_hi) hAi'_sq (sq_nonneg _) (by positivity))
      _ ≤ 46 * x ^ (-(5 / 2 : ℝ)) := by rw [← hpow2]; nlinarith [hpow1, Real.rpow_nonneg hx0.le (-(5 / 2 : ℝ))]
  have hg1_bd : |ceG1 a1 (-x)| ≤ 4 * x ^ (-(5 / 2 : ℝ)) := by
    rw [abs_of_nonneg (by unfold ceG1; positivity), ceG1, dslope_of_ne _ hne1, slope_def_field,
      airyAi_airyZero, sub_zero, div_pow, show (-x - a1) ^ 2 = (x + a1) ^ 2 by ring]
    have h52 : x ^ (-(1 / 2 : ℝ)) / (x / 2) ^ 2 = 4 * x ^ (-(5 / 2 : ℝ)) := by
      have hpow : (x / 2) ^ 2 = x ^ (2 : ℝ) / 4 := by rw [div_pow, Real.rpow_two]; ring
      rw [hpow, show x ^ (-(1 / 2 : ℝ)) / (x ^ (2 : ℝ) / 4) =
        4 * (x ^ (-(1 / 2 : ℝ)) / x ^ (2 : ℝ)) by ring, ← Real.rpow_sub hx0]; norm_num
    exact (div_le_div₀ (by positivity) hAi_sq (by positivity)
      (pow_le_pow_left₀ (by positivity) (by linarith : x / 2 ≤ x + a1) 2)).trans_eq h52
  have hmul_pow : x ^ (3 / 2 : ℝ) * x ^ (-(5 / 2 : ℝ)) = x⁻¹ := by
    rw [← Real.rpow_add hx0, show (3 / 2 : ℝ) + -(5 / 2 : ℝ) = -1 by norm_num, Real.rpow_neg_one]
  have hinner0 : |b * (-ceF1 (-x) - Real.sin (cohnTheta x) ^ 2 / (π * x ^ (3 / 2 : ℝ))) +
        (ceG1Deriv a1' (-x) - Real.cos (cohnTheta x) ^ 2 / (π * x ^ (3 / 2 : ℝ)))| ≤
      (6 * |b| + 46) * x ^ (-(5 / 2 : ℝ)) := by
    have htri := abs_add_le
      (b * (-ceF1 (-x) - Real.sin (cohnTheta x) ^ 2 / (π * x ^ (3 / 2 : ℝ))))
      (ceG1Deriv a1' (-x) - Real.cos (cohnTheta x) ^ 2 / (π * x ^ (3 / 2 : ℝ)))
    rw [abs_mul] at htri
    calc _ ≤ |b| * |-ceF1 (-x) - Real.sin (cohnTheta x) ^ 2 / (π * x ^ (3 / 2 : ℝ))| +
            |ceG1Deriv a1' (-x) - Real.cos (cohnTheta x) ^ 2 / (π * x ^ (3 / 2 : ℝ))| := htri
      _ ≤ |b| * (6 * x ^ (-(5 / 2 : ℝ))) + 46 * x ^ (-(5 / 2 : ℝ)) :=
          add_le_add (mul_le_mul_of_nonneg_left hf_err (abs_nonneg _)) hg'_err
      _ = (6 * |b| + 46) * x ^ (-(5 / 2 : ℝ)) := by ring
  have hR0_tight : |R0 x| ≤ π * (6 * |b| + 46) * x⁻¹ := by
    rw [show R0 x = π * x ^ (3 / 2 : ℝ) *
        (b * (-ceF1 (-x) - Real.sin (cohnTheta x) ^ 2 / (π * x ^ (3 / 2 : ℝ))) +
          (ceG1Deriv a1' (-x) - Real.cos (cohnTheta x) ^ 2 / (π * x ^ (3 / 2 : ℝ)))) by
        dsimp [R0]; field_simp [hpi0, hxp32]; ring,
      abs_mul, abs_of_pos (mul_pos Real.pi_pos (Real.rpow_pos_of_pos hx0 _))]
    calc π * x ^ (3 / 2 : ℝ) * _
        ≤ π * x ^ (3 / 2 : ℝ) * ((6 * |b| + 46) * x ^ (-(5 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hinner0 (by positivity [Real.pi_pos])
      _ = π * (6 * |b| + 46) * x⁻¹ := by rw [← hmul_pow]; ring
  have hR0_bd : |R0 x| ≤ C * x⁻¹ := hR0_tight.trans (by dsimp [C]; gcongr; linarith)
  have hR_bd : |R x| ≤ C * x⁻¹ := by
    rw [show R x = R0 x + π * x ^ (3 / 2 : ℝ) * ceG1 a1 (-x) by dsimp [R, R0, ceSb]; ring]
    have hg_term : |π * x ^ (3 / 2 : ℝ) * ceG1 a1 (-x)| ≤ π * 4 * x⁻¹ := by
      rw [abs_mul, abs_of_pos (mul_pos Real.pi_pos (Real.rpow_pos_of_pos hx0 _))]
      calc π * x ^ (3 / 2 : ℝ) * |ceG1 a1 (-x)|
          ≤ π * x ^ (3 / 2 : ℝ) * (4 * x ^ (-(5 / 2 : ℝ))) :=
            mul_le_mul_of_nonneg_left hg1_bd (by positivity [Real.pi_pos])
        _ = π * 4 * x⁻¹ := by rw [← hmul_pow]; ring
    calc |R0 x + π * x ^ (3 / 2 : ℝ) * ceG1 a1 (-x)|
        ≤ |R0 x| + |π * x ^ (3 / 2 : ℝ) * ceG1 a1 (-x)| := abs_add_le _ _
      _ ≤ π * (6 * |b| + 46) * x⁻¹ + π * 4 * x⁻¹ := add_le_add hR0_tight hg_term
      _ = C * x⁻¹ := by dsimp [C]; ring
  exact ⟨heq0, heqS, hR0_bd, hR_bd⟩

/-- **Lemma `U.4a(2)`, global negative-ray floor (`u1c_o1_upper.tex`, `u1c:U4a`):**
for every `b > 0`, there exists `C_b > 0` such that `S_b(u) ≥ C_b (1 + |u|)^{-3/2}` for all `u ≤ a₁`. -/
theorem ceSb_lower_floor {b : ℝ} (hb : 0 < b) :
    ∃ C_b > 0, ∀ u ≤ airyZero 1, C_b * (1 + |u|) ^ (-(3 / 2 : ℝ)) ≤ ceSb b u := by
  obtain ⟨_R0, R, C, hC, hWKB⟩ := ceSb_neg_asymptotic b
  set m₀ : ℝ := min b 1
  have hm₀ : 0 < m₀ := lt_min hb one_pos
  set X : ℝ := max 5 (2 * C / m₀)
  have hX5 : 5 ≤ X := le_max_left _ _
  have hXC : 2 * C / m₀ ≤ X := le_max_right _ _
  have ha1_gt : -X < airyZero 1 := by linarith [airyZero_one.1]
  obtain ⟨u_min, hu_mem, hu_min⟩ := isCompact_Icc.exists_isMinOn
    ⟨airyZero 1, ha1_gt.le, le_rfl⟩ (continuous_ceSb b).continuousOn
  set m₁ : ℝ := ceSb b u_min
  have hm₁ : 0 < m₁ := ceSb_pos_of_le hb.le hu_mem.2
  refine ⟨min (m₀ / (2 * π)) m₁, lt_min (div_pos hm₀ (mul_pos two_pos Real.pi_pos)) hm₁, fun u hu => ?_⟩
  rcases le_or_gt u (-X) with h_tail | h_cpt
  · set x : ℝ := -u
    have hx : X ≤ x := by dsimp [x]; linarith
    have hx5 : 5 ≤ x := hX5.trans hx
    have hx0 : 0 < x := by linarith
    obtain ⟨_heq0, heqS, _hR0, hRx⟩ := hWKB x hx5
    have hR_le : |R x| ≤ m₀ / 2 := calc
      |R x| ≤ C * x⁻¹ := hRx
      _ ≤ C * (2 * C / m₀)⁻¹ := mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) (hXC.trans hx)) hC.le
      _ = m₀ / 2 := by field_simp [hC.ne', hm₀.ne']
    have htrig : m₀ ≤ b * Real.sin (cohnTheta x) ^ 2 + Real.cos (cohnTheta x) ^ 2 := by
      have h1 := mul_le_mul_of_nonneg_right (min_le_left b 1) (sq_nonneg (Real.sin (cohnTheta x)))
      have h2 := mul_le_mul_of_nonneg_right (min_le_right b 1) (sq_nonneg (Real.cos (cohnTheta x)))
      have hsc := Real.sin_sq_add_cos_sq (cohnTheta x)
      nlinarith
    have hpos_coeff : m₀ / 2 ≤ b * Real.sin (cohnTheta x) ^ 2 + Real.cos (cohnTheta x) ^ 2 + R x := by
      linarith [(abs_le.mp hR_le).1]
    have hpow_le : (1 + |u|) ^ (-(3 / 2 : ℝ)) ≤ x ^ (-(3 / 2 : ℝ)) := by
      rw [abs_of_neg (by linarith : u < 0)]
      exact Real.rpow_le_rpow_of_nonpos hx0 (by change x ≤ 1 + x; linarith) (by norm_num)
    calc min (m₀ / (2 * π)) m₁ * (1 + |u|) ^ (-(3 / 2 : ℝ))
        ≤ (m₀ / (2 * π)) * x ^ (-(3 / 2 : ℝ)) :=
          mul_le_mul (min_le_left _ _) hpow_le (Real.rpow_nonneg (by positivity) _) (by positivity)
      _ = π⁻¹ * x ^ (-(3 / 2 : ℝ)) * (m₀ / 2) := by ring
      _ ≤ π⁻¹ * x ^ (-(3 / 2 : ℝ)) * (b * Real.sin (cohnTheta x) ^ 2 + Real.cos (cohnTheta x) ^ 2 + R x) :=
          mul_le_mul_of_nonneg_left hpos_coeff (mul_nonneg (inv_nonneg.mpr Real.pi_pos.le) (Real.rpow_nonneg hx0.le _))
      _ = ceSb b u := by rw [← heqS]; simp [x]
  · have hpow_le1 : (1 + |u|) ^ (-(3 / 2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg u]) (by norm_num)
    calc min (m₀ / (2 * π)) m₁ * (1 + |u|) ^ (-(3 / 2 : ℝ))
        ≤ m₁ * 1 := mul_le_mul (min_le_right _ _) hpow_le1 (Real.rpow_nonneg (by positivity) _) hm₁.le
      _ ≤ ceSb b u := by rw [mul_one]; exact hu_min ⟨h_cpt.le, hu⟩

/-! ### Part 2: Lemma `lem:hb-seed-mass` (`u1c_o1_upper.tex` lines 455–512) -/

/-- Hermite–Biehler seed package for `lem:hb-seed-mass` (`u1c_o1_upper.tex`, ll. 455–512).
Encodes the `m₀ ≥ 1` real zeros `t₁ > ⋯ > t_{m₀}` (`t_{m₀} ≤ a₁ < 0`), the mean-zero seed `G_N`,
its terminal cardinal companion `H_N(u) = G_N(u) / (t_{m₀} - u)` (`u < t_{m₀}`) with `∫ H_N = I_N > 0`,
vanishing and local Lipschitz bounds near prescribed sites `t_j` (`j < m₀ - 1`), and the
oscillatory Hypothesis `(H)` lower bound on `G_N(-y)`. -/
structure HBSeedSpec where
  m₀ : ℕ
  m₀_pos : 1 ≤ m₀
  nodes : Fin m₀ → ℝ
  nodes_anti : StrictAnti nodes
  last_le_a1 : nodes ⟨m₀ - 1, Nat.sub_lt m₀_pos zero_lt_one⟩ ≤ airyZero 1
  G_N : ℝ → ℝ
  H_N : ℝ → ℝ
  I_N : ℝ
  I_N_pos : 0 < I_N
  continuous_G : Continuous G_N
  continuous_H : Continuous H_N
  integrable_G : Integrable G_N
  integrable_H : Integrable H_N
  integral_G : ∫ u : ℝ, G_N u = 0
  integral_H : ∫ u : ℝ, H_N u = I_N
  G_nonneg_tail : ∀ u ≤ nodes ⟨m₀ - 1, Nat.sub_lt m₀_pos zero_lt_one⟩, 0 ≤ G_N u
  H_eq_div_tail : ∀ u < nodes ⟨m₀ - 1, Nat.sub_lt m₀_pos zero_lt_one⟩,
    H_N u = G_N u / (nodes ⟨m₀ - 1, Nat.sub_lt m₀_pos zero_lt_one⟩ - u)
  node_vanish : ∀ j : Fin m₀, j.val + 1 < m₀ → G_N (nodes j) = 0 ∧ H_N (nodes j) = 0
  r_node : ℝ
  r_node_pos : 0 < r_node
  A_G : ℝ
  A_H : ℝ
  A_G_nonneg : 0 ≤ A_G
  A_H_nonneg : 0 ≤ A_H
  G_lip_near : ∀ j : Fin m₀, j.val + 1 < m₀ → ∀ u, |u - nodes j| ≤ r_node →
    |G_N u| ≤ A_G * |u - nodes j|
  H_lip_near : ∀ j : Fin m₀, j.val + 1 < m₀ → ∀ u, |u - nodes j| ≤ r_node →
    |H_N u| ≤ A_H * |u - nodes j|
  c_osc_G : ℝ
  C_r_G : ℝ
  y₁_G : ℝ
  ϑ_c_G : ℝ
  c_osc_G_pos : 0 < c_osc_G
  C_r_G_nonneg : 0 ≤ C_r_G
  y₁_G_ge : 25 ≤ y₁_G
  G_osc_tail : ∃ r : ℝ → ℝ, ∀ y ≥ y₁_G,
    |r y| ≤ C_r_G * y ^ (-(1 / 2 : ℝ)) ∧
      c_osc_G * y ^ (-(3 / 2 : ℝ)) * (Real.cos ((2 / 3 : ℝ) * y ^ (3 / 2 : ℝ) + ϑ_c_G) + r y) ^ 2 ≤ G_N (-y)

/-- Terminal node `t_{m₀}` of an `HBSeedSpec`. -/
def HBSeedSpec.lastNode (S : HBSeedSpec) : ℝ :=
  S.nodes ⟨S.m₀ - 1, Nat.sub_lt S.m₀_pos zero_lt_one⟩

/-- Because `g₁ + g₁' > 0` everywhere (`ceG1_add_ceG1Deriv_pos`), there always exists `b > 0`
such that `ceSb b (nodes j) > 0` at every prescribed site `t_j` (`j < m₀ - 1`). -/
theorem exists_ceSb_pos_at_nodes (S : HBSeedSpec) :
    ∃ b > 0, ∀ j : Fin S.m₀, j.val + 1 < S.m₀ → 0 < ceSb b (S.nodes j) := by
  let f : Fin S.m₀ → ℝ := fun j =>
    (ceG1 (airyZero 1) (S.nodes j) + ceG1Deriv airyDerivFirstZero (S.nodes j)) /
      (2 * (|ceF1 (S.nodes j)| + 1))
  have hne : (Finset.univ : Finset (Fin S.m₀)).Nonempty := ⟨⟨0, S.m₀_pos⟩, Finset.mem_univ _⟩
  let b : ℝ := Finset.univ.inf' hne f
  have hb_pos : 0 < b := (Finset.lt_inf'_iff hne).mpr fun j _ =>
    div_pos (ceG1_add_ceG1Deriv_pos (S.nodes j)) (by positivity)
  refine ⟨b, hb_pos, fun j _ => ?_⟩
  have hS0 := ceG1_add_ceG1Deriv_pos (S.nodes j)
  have hne_den : |ceF1 (S.nodes j)| + 1 ≠ 0 := by positivity
  have hmul : b * |ceF1 (S.nodes j)| ≤
      (ceG1 (airyZero 1) (S.nodes j) + ceG1Deriv airyDerivFirstZero (S.nodes j)) / 2 := by
    calc b * |ceF1 (S.nodes j)|
        ≤ f j * |ceF1 (S.nodes j)| := mul_le_mul_of_nonneg_right (Finset.inf'_le f (Finset.mem_univ j)) (abs_nonneg _)
      _ = ((ceG1 (airyZero 1) (S.nodes j) + ceG1Deriv airyDerivFirstZero (S.nodes j)) / 2) *
            (|ceF1 (S.nodes j)| / (|ceF1 (S.nodes j)| + 1)) := by
          dsimp [f]; field_simp [hne_den]
      _ ≤ ((ceG1 (airyZero 1) (S.nodes j) + ceG1Deriv airyDerivFirstZero (S.nodes j)) / 2) * 1 :=
          mul_le_mul_of_nonneg_left (by rw [div_le_one (by positivity)]; linarith) (half_pos hS0).le
      _ = _ := mul_one _
  have hbf : b * ceF1 (S.nodes j) ≤ b * |ceF1 (S.nodes j)| :=
    mul_le_mul_of_nonneg_left (le_abs_self _) hb_pos.le
  unfold ceSb; linarith

/-- **Lemma `lem:hb-seed-mass` (`u1c_o1_upper.tex`, ll. 455–512):**
Given `S : HBSeedSpec`, `b > 0` with `S_b > 0` at every prescribed site `t_j` (`j < m₀ - 1`),
and bounds `0 ≤ V_max`, `0 ≤ ε₀`, there exist uniform `δ₁ > 0`, `γ₂ > 0`, `D : OscFloorSeedData`,
and `γ₁ v := (γ₂ (1 + |a₁'|) + v) / I_N > 0` such that for all `v ∈ [0, V_max]`, `δ ∈ (0, δ₁]`,
and any remainder `r_val` with `|r_val| ≤ ε₀ δ`, the seed
`F_δ(u) := G_N(u) - γ₁(v) δ H_N(u) + γ₂ δ S_b(u) + r_val g₁(u)`
has integral `-v δ + r_val`, satisfies Hypothesis `(H)` (`SatisfiesH D`) at `u₀ = t_{m₀} - 2 γ₁(v) δ`,
is `≥ δ / 2` on `|u - t_j| ≤ β₁ δ` for every `j < m₀ - 1`, and equals `G_N + O(δ)` uniformly
on every bounded interval `[-R, R]`. -/
theorem hb_seed_mass_exists (S : HBSeedSpec) {b V_max ε₀ : ℝ} (hb : 0 < b)
    (hb_nodes : ∀ j : Fin S.m₀, j.val + 1 < S.m₀ → 0 < ceSb b (S.nodes j))
    (hV : 0 ≤ V_max) (hε : 0 ≤ ε₀) :
    ∃ δ₁ > 0, ∃ γ₂ > 0, ∃ γ₁ : ℝ → ℝ, ∃ D : OscFloorSeedData,
      (∀ v ∈ Icc (0 : ℝ) V_max, 0 < γ₁ v) ∧
      (∀ v ∈ Icc (0 : ℝ) V_max, ∀ δ ∈ Ioc (0 : ℝ) δ₁, ∀ r_val : ℝ, |r_val| ≤ ε₀ * δ →
        let F := fun u : ℝ => S.G_N u - γ₁ v * δ * S.H_N u + γ₂ * δ * ceSb b u +
          r_val * ceG1 (airyZero 1) u
        let u₀ := S.lastNode - 2 * γ₁ v * δ
        (Integrable F ∧ ∫ u : ℝ, F u = -v * δ + r_val) ∧
        SatisfiesH D F δ u₀ ∧
        (∀ j : Fin S.m₀, j.val + 1 < S.m₀ → ∀ u, |u - S.nodes j| ≤ ceBeta1 * δ →
          δ / 2 ≤ F u)) ∧
      (∀ R ≥ (0 : ℝ), ∃ C_R ≥ 0, ∀ v ∈ Icc (0 : ℝ) V_max, ∀ δ ∈ Ioc (0 : ℝ) δ₁,
        ∀ r_val : ℝ, |r_val| ≤ ε₀ * δ → ∀ u ∈ Icc (-R) R,
        |(S.G_N u - γ₁ v * δ * S.H_N u + γ₂ * δ * ceSb b u +
            r_val * ceG1 (airyZero 1) u) - S.G_N u| ≤ C_R * δ) := by
  have hne : (Finset.univ : Finset (Fin S.m₀)).Nonempty := ⟨⟨0, S.m₀_pos⟩, Finset.mem_univ _⟩
  have hex_site : ∀ j : Fin S.m₀, ∃ r_j > 0,
      j.val + 1 < S.m₀ → ∀ u, |u - S.nodes j| ≤ r_j → ceSb b (S.nodes j) / 2 ≤ ceSb b u := by
    intro j
    by_cases hj : j.val + 1 < S.m₀
    · obtain ⟨ρ, hρ, hball⟩ := Metric.continuousAt_iff.mp (continuous_ceSb b).continuousAt
        (ceSb b (S.nodes j) / 2) (half_pos (hb_nodes j hj))
      refine ⟨ρ / 2, half_pos hρ, fun _ u hu => ?_⟩
      have hsub := abs_sub_lt_iff.mp (by simpa [Real.dist_eq] using hball (by rw [Real.dist_eq]; linarith))
      linarith
    · exact ⟨1, one_pos, fun h => absurd h hj⟩
  let r_fn_j : Fin S.m₀ → ℝ := fun j => Classical.choose (hex_site j)
  let r_site : ℝ := min S.r_node (Finset.univ.inf' hne r_fn_j)
  have hr_site : 0 < r_site := lt_min S.r_node_pos
    ((Finset.lt_inf'_iff hne).mpr fun j _ => (Classical.choose_spec (hex_site j)).1)
  let s_val : Fin S.m₀ → ℝ := fun j => if h : j.val + 1 < S.m₀ then ceSb b (S.nodes j) / 2 else 1
  let s : ℝ := Finset.univ.inf' hne s_val
  have hs_pos : 0 < s := (Finset.lt_inf'_iff hne).mpr fun j _ => by
    dsimp [s_val]; split_ifs with h; exact half_pos (hb_nodes j h); exact one_pos
  let R_site : ℝ := r_site + Finset.univ.sup' hne (fun j => |S.nodes j|)
  have hR_site : 0 ≤ R_site := by
    have h0 : |S.nodes ⟨0, S.m₀_pos⟩| ≤ Finset.univ.sup' hne (fun j => |S.nodes j|) :=
      Finset.le_sup' (fun j => |S.nodes j|) (Finset.mem_univ _)
    linarith [abs_nonneg (S.nodes ⟨0, S.m₀_pos⟩)]
  obtain ⟨t_g1, -, ht_g1_max⟩ := isCompact_Icc.exists_isMaxOn
    ⟨0, neg_nonpos.mpr hR_site, hR_site⟩ (continuous_ceG1 (airyZero 1)).continuousOn
  let M_g1 : ℝ := max (ceG1 (airyZero 1) t_g1) 0
  have h_g1_site : ∀ j : Fin S.m₀, ∀ u, |u - S.nodes j| ≤ r_site → ceG1 (airyZero 1) u ≤ M_g1 := by
    intro j u hu
    have hj_le : |S.nodes j - 0| ≤ Finset.univ.sup' hne (fun k => |S.nodes k|) := by
      rw [sub_zero]; exact Finset.le_sup' (fun k => |S.nodes k|) (Finset.mem_univ j)
    have hu_abs : |u| ≤ R_site := by simpa [sub_zero] using (abs_sub_le u (S.nodes j) 0).trans (add_le_add hu hj_le)
    exact (ht_g1_max (abs_le.mp hu_abs)).trans (le_max_left _ _)
  let γ₂ : ℝ := max (max 1 (2 * ε₀)) ((ceBeta1 * S.A_G + ε₀ * M_g1 + 1) / s)
  have hγ₂_pos : 0 < γ₂ := lt_of_lt_of_le one_pos ((le_max_left _ _).trans (le_max_left _ _))
  have hγ₂_eps : 2 * ε₀ ≤ γ₂ := (le_max_right _ _).trans (le_max_left _ _)
  have hγ₂_site : ceBeta1 * S.A_G + ε₀ * M_g1 + 1 ≤ γ₂ * s := (div_le_iff₀ hs_pos).mp (le_max_right _ _)
  let γ₁ : ℝ → ℝ := fun v => (γ₂ * (1 + |airyDerivFirstZero|) + v) / S.I_N
  let γ₁_max : ℝ := (γ₂ * (1 + |airyDerivFirstZero|) + V_max) / S.I_N
  have hγ₁_pos : ∀ v ∈ Icc (0 : ℝ) V_max, 0 < γ₁ v := fun v hv =>
    div_pos (add_pos_of_pos_of_nonneg (mul_pos hγ₂_pos (by positivity)) hv.1) S.I_N_pos
  have hγ₁_le : ∀ v ∈ Icc (0 : ℝ) V_max, γ₁ v ≤ γ₁_max := fun v hv =>
    div_le_div_of_nonneg_right (by linarith [hv.2]) S.I_N_pos.le
  obtain ⟨C_b, hC_b_pos, h_sb_floor⟩ := ceSb_lower_floor hb
  let D : OscFloorSeedData :=
    { c_lin := γ₂ * C_b / 2, c_osc := S.c_osc_G / 2, C_r := S.C_r_G
      y₁ := max 25 (max S.y₁_G (|S.lastNode| + γ₁_max + 1)), ϑ_c := S.ϑ_c_G
      c_lin_pos := by positivity, c_osc_pos := half_pos S.c_osc_G_pos
      C_r_nonneg := S.C_r_G_nonneg, y₁_ge := le_max_left _ _ }
  let δ₁ : ℝ := min (1 / 2) (min (r_site / ceBeta1) (1 / (2 * (γ₁_max * S.A_H * ceBeta1 + 1))))
  have hγ₁_max_nn : 0 ≤ γ₁_max := div_nonneg (by positivity [hV]) S.I_N_pos.le
  have hδ₁_pos : 0 < δ₁ := lt_min (by norm_num)
    (lt_min (div_pos hr_site ceBeta1_pos) (div_pos one_pos (by positivity [ceBeta1_pos, S.A_H_nonneg])))
  refine ⟨δ₁, hδ₁_pos, γ₂, hγ₂_pos, γ₁, D, hγ₁_pos, fun v hv δ hδ r_val hr => ?_, fun R hR => ?_⟩
  · set F : ℝ → ℝ := fun u => S.G_N u - γ₁ v * δ * S.H_N u + γ₂ * δ * ceSb b u +
      r_val * ceG1 (airyZero 1) u
    set u₀ : ℝ := S.lastNode - 2 * γ₁ v * δ
    have hδ_pos : 0 < δ := hδ.1
    have hδ_le_half : δ ≤ 1 / 2 := hδ.2.trans (min_le_left _ _)
    have hγ₁_v : 0 < γ₁ v := hγ₁_pos v hv
    have hγ₁_v_max : γ₁ v ≤ γ₁_max := hγ₁_le v hv
    have hF1_int := S.integrable_G.sub (S.integrable_H.const_mul (γ₁ v * δ))
    have hF12_int := hF1_int.add ((ceSb_integrable b).const_mul (γ₂ * δ))
    have hF_int : Integrable F := hF12_int.add (ceG1_integrable.const_mul r_val)
    have hF_eval : ∫ u : ℝ, F u = -v * δ + r_val := by
      have h1 : ∫ u : ℝ, F u =
          (∫ u : ℝ, (S.G_N u - γ₁ v * δ * S.H_N u) + γ₂ * δ * ceSb b u) +
            ∫ u : ℝ, r_val * ceG1 (airyZero 1) u :=
        integral_add hF12_int (ceG1_integrable.const_mul r_val)
      have h2 : (∫ u : ℝ, (S.G_N u - γ₁ v * δ * S.H_N u) + γ₂ * δ * ceSb b u) =
          (∫ u : ℝ, S.G_N u - γ₁ v * δ * S.H_N u) + ∫ u : ℝ, γ₂ * δ * ceSb b u :=
        integral_add hF1_int ((ceSb_integrable b).const_mul (γ₂ * δ))
      have h3 : (∫ u : ℝ, S.G_N u - γ₁ v * δ * S.H_N u) =
          (∫ u : ℝ, S.G_N u) - ∫ u : ℝ, γ₁ v * δ * S.H_N u :=
        integral_sub S.integrable_G (S.integrable_H.const_mul (γ₁ v * δ))
      rw [h1, h2, h3, integral_const_mul, integral_const_mul, integral_const_mul,
        S.integral_G, S.integral_H, ceSb_integral, ceG1_integral_eq_one]
      dsimp [γ₁]; field_simp [S.I_N_pos.ne']; ring
    have hu₀_neg : u₀ < 0 := by
      have ha1_neg : airyZero 1 < 0 := airyZero_neg 1
      have hlast : S.lastNode ≤ airyZero 1 := S.last_le_a1
      dsimp [u₀, HBSeedSpec.lastNode] at *; linarith [mul_pos hγ₁_v hδ_pos]
    have hF_cont : Continuous F :=
      ((S.continuous_G.sub (continuous_const.mul S.continuous_H)).add
        (continuous_const.mul (continuous_ceSb b))).add
        (continuous_const.mul (continuous_ceG1 (airyZero 1)))
    have hGH_tail : ∀ u ≤ u₀, S.G_N u / 2 ≤ S.G_N u - γ₁ v * δ * S.H_N u := fun u hu => by
      have h_lt : u < S.lastNode := by
        have : 0 < 2 * γ₁ v * δ := by positivity
        dsimp [u₀, HBSeedSpec.lastNode] at hu ⊢; linarith
      have hden_pos : 0 < S.lastNode - u := by linarith
      have hdiv_le : γ₁ v * δ / (S.lastNode - u) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ hden_pos two_pos]; dsimp [u₀, HBSeedSpec.lastNode] at hu ⊢; linarith
      rw [S.H_eq_div_tail u h_lt]
      change S.G_N u / 2 ≤ S.G_N u - γ₁ v * δ * (S.G_N u / (S.lastNode - u))
      rw [show S.G_N u - γ₁ v * δ * (S.G_N u / (S.lastNode - u)) =
        S.G_N u * (1 - γ₁ v * δ / (S.lastNode - u)) by ring]
      calc S.G_N u / 2 = S.G_N u * (1 / 2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (S.G_nonneg_tail u h_lt.le)
    have hSb_tail : ∀ u ≤ S.lastNode,
        (γ₂ / 2) * δ * ceSb b u ≤ γ₂ * δ * ceSb b u + r_val * ceG1 (airyZero 1) u := fun u hu => by
      have hg1_le := ceG1_le_ceSb hb.le (hu.trans S.last_le_a1)
      have hr_le : -r_val ≤ (γ₂ / 2) * δ := by
        linarith [(abs_le.mp hr).1, mul_le_mul_of_nonneg_right hγ₂_eps hδ_pos.le]
      have hterm : -((γ₂ / 2) * δ * ceSb b u) ≤ r_val * ceG1 (airyZero 1) u := calc
        -((γ₂ / 2) * δ * ceSb b u) ≤ -((γ₂ / 2) * δ * ceG1 (airyZero 1) u) := by gcongr
        _ = (-((γ₂ / 2) * δ)) * ceG1 (airyZero 1) u := by ring
        _ ≤ r_val * ceG1 (airyZero 1) u := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
      linarith
    have hlin : ∀ y ≥ |u₀|, D.c_lin * δ * (1 + y) ^ (-(3 / 2 : ℝ)) ≤ F (-y) := fun y hy => by
      have hy_u0 : -y ≤ u₀ := by rw [abs_of_neg hu₀_neg] at hy; linarith
      have hy_last : -y ≤ S.lastNode := by
        dsimp [u₀, HBSeedSpec.lastNode] at hy_u0 ⊢; linarith [mul_pos hγ₁_v hδ_pos]
      have hG_nn : 0 ≤ S.G_N (-y) := S.G_nonneg_tail (-y) hy_last
      have hfloor := h_sb_floor (-y) (hy_last.trans S.last_le_a1)
      rw [abs_neg, abs_of_nonneg (le_trans (abs_nonneg _) hy)] at hfloor
      have h1 := hGH_tail (-y) hy_u0; have h2 := hSb_tail (-y) hy_last
      dsimp [D, F]
      calc (γ₂ * C_b / 2) * δ * (1 + y) ^ (-(3 / 2 : ℝ))
          = (γ₂ / 2) * δ * (C_b * (1 + y) ^ (-(3 / 2 : ℝ))) := by ring
        _ ≤ (γ₂ / 2) * δ * ceSb b (-y) := mul_le_mul_of_nonneg_left hfloor (by positivity)
        _ ≤ _ := by linarith
    have hosc : ∃ r : ℝ → ℝ, ∀ y ≥ D.y₁,
        |r y| ≤ D.C_r * y ^ (-(1 / 2 : ℝ)) ∧
          D.c_osc * y ^ (-(3 / 2 : ℝ)) * (Real.cos ((2 / 3 : ℝ) * y ^ (3 / 2 : ℝ) + D.ϑ_c) + r y) ^ 2 ≤ F (-y) := by
      obtain ⟨r, hr_tail⟩ := S.G_osc_tail
      refine ⟨r, fun y hy => ?_⟩
      have hy_G : S.y₁_G ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
      have hy_u0_bd : |S.lastNode| + γ₁_max + 1 ≤ y :=
        ((le_max_right _ _).trans (le_max_right _ _)).trans hy
      have hy_u0 : |u₀| ≤ y := by
        have hlast_neg : S.lastNode < 0 := lt_of_le_of_lt S.last_le_a1 (airyZero_neg 1)
        have heq_abs : -u₀ = |S.lastNode| + 2 * γ₁ v * δ := by
          rw [abs_of_neg hlast_neg]; dsimp [u₀, HBSeedSpec.lastNode]; ring
        rw [abs_of_neg hu₀_neg, heq_abs]
        nlinarith [mul_le_mul_of_nonneg_right hγ₁_v_max hδ_pos.le]
      have hy_u0_le : -y ≤ u₀ := by rw [abs_of_neg hu₀_neg] at hy_u0; linarith
      have hy_last : -y ≤ S.lastNode := by
        dsimp [u₀, HBSeedSpec.lastNode] at hy_u0_le ⊢; linarith [mul_pos hγ₁_v hδ_pos]
      have h_sb_nn : 0 ≤ (γ₂ / 2) * δ * ceSb b (-y) :=
        mul_nonneg (by positivity) (ceSb_pos_of_le hb.le (hy_last.trans S.last_le_a1)).le
      obtain ⟨hr_bd, hG_osc⟩ := hr_tail y hy_G
      have h1 := hGH_tail (-y) hy_u0_le; have h2 := hSb_tail (-y) hy_last
      exact ⟨hr_bd, by dsimp [D, F] at *; linarith⟩
    have hpresc : ∀ j : Fin S.m₀, j.val + 1 < S.m₀ → ∀ u, |u - S.nodes j| ≤ ceBeta1 * δ →
        δ / 2 ≤ F u := fun j hj u hu => by
      have h_rad : ceBeta1 * δ ≤ r_site := by
        rw [mul_comm]
        exact (le_div_iff₀ ceBeta1_pos).mp (hδ.2.trans ((min_le_right _ _).trans (min_le_left _ _)))
      have hu_r : |u - S.nodes j| ≤ r_site := hu.trans h_rad
      have hu_rj : |u - S.nodes j| ≤ r_fn_j j :=
        hu_r.trans ((min_le_right _ _).trans (Finset.inf'_le r_fn_j (Finset.mem_univ j)))
      have hG_bd : -(S.A_G * ceBeta1 * δ) ≤ S.G_N u := by
        have h1 := (abs_le.mp ((S.G_lip_near j hj u (hu_r.trans (min_le_left _ _))).trans
          (mul_le_mul_of_nonneg_left hu S.A_G_nonneg))).1
        linarith
      have hH_abs : |S.H_N u| ≤ S.A_H * ceBeta1 * δ :=
        (S.H_lip_near j hj u (hu_r.trans (min_le_left _ _))).trans
          (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hu S.A_H_nonneg)
      have hH_term : -(γ₁_max * S.A_H * ceBeta1 * δ ^ 2) ≤ -(γ₁ v * δ * S.H_N u) := by
        have habs : γ₁ v * δ * S.H_N u ≤ γ₁_max * S.A_H * ceBeta1 * δ ^ 2 := calc
          γ₁ v * δ * S.H_N u ≤ γ₁ v * δ * |S.H_N u| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) (mul_nonneg hγ₁_v.le hδ_pos.le)
          _ ≤ γ₁_max * δ * (S.A_H * ceBeta1 * δ) :=
            mul_le_mul (mul_le_mul_of_nonneg_right hγ₁_v_max hδ_pos.le) hH_abs (abs_nonneg _)
              (mul_nonneg hγ₁_max_nn hδ_pos.le)
          _ = γ₁_max * S.A_H * ceBeta1 * δ ^ 2 := by ring
        linarith
      have hH_sq_le : γ₁_max * S.A_H * ceBeta1 * δ ^ 2 ≤ δ / 2 := by
        have h2 := hδ.2.trans ((min_le_right _ _).trans (min_le_right _ _))
        rw [le_div_iff₀ (by positivity [ceBeta1_pos, S.A_H_nonneg])] at h2
        nlinarith [hδ_pos]
      have hs_sb : s ≤ ceSb b u := by
        have hle : s ≤ s_val j := Finset.inf'_le s_val (Finset.mem_univ j)
        have hs1 : s ≤ ceSb b (S.nodes j) / 2 := by
          dsimp [s_val] at hle; simp only [hj, ↓reduceIte] at hle; exact hle
        exact hs1.trans ((Classical.choose_spec (hex_site j)).2 hj u hu_rj)
      have hSb_term : γ₂ * s * δ ≤ γ₂ * δ * ceSb b u := by
        rw [show γ₂ * δ * ceSb b u = γ₂ * ceSb b u * δ by ring]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs_sb hγ₂_pos.le) hδ_pos.le
      have hr_term : -(ε₀ * M_g1 * δ) ≤ r_val * ceG1 (airyZero 1) u := by
        have h1 : -r_val ≤ ε₀ * δ := by linarith [(abs_le.mp hr).1]
        have h2 := mul_le_mul h1 (h_g1_site j u hu_r) (sq_nonneg _) (mul_nonneg hε hδ_pos.le)
        linarith
      have hsite_mul : δ ≤ (γ₂ * s - ceBeta1 * S.A_G - ε₀ * M_g1) * δ := by
        have : 1 ≤ γ₂ * s - ceBeta1 * S.A_G - ε₀ * M_g1 := by linarith
        nlinarith
      dsimp [F]; linarith
    exact ⟨⟨hF_int, hF_eval⟩, ⟨hu₀_neg, hF_cont.locallyIntegrable, hlin, hosc⟩, hpresc⟩
  · obtain ⟨uH, -, huH_max⟩ := isCompact_Icc.exists_isMaxOn ⟨0, neg_nonpos.mpr hR, hR⟩
      S.continuous_H.abs.continuousOn
    obtain ⟨uS, -, huS_max⟩ := isCompact_Icc.exists_isMaxOn ⟨0, neg_nonpos.mpr hR, hR⟩
      (continuous_ceSb b).abs.continuousOn
    obtain ⟨ug, -, hug_max⟩ := isCompact_Icc.exists_isMaxOn ⟨0, neg_nonpos.mpr hR, hR⟩
      (continuous_ceG1 (airyZero 1)).continuousOn
    have hg_ug_nn : 0 ≤ ceG1 (airyZero 1) ug := sq_nonneg _
    refine ⟨γ₁_max * |S.H_N uH| + γ₂ * |ceSb b uS| + ε₀ * ceG1 (airyZero 1) ug,
      by positivity [abs_nonneg (S.H_N uH), abs_nonneg (ceSb b uS)],
      fun v hv δ hδ r_val hr u hu => ?_⟩
    rw [show (S.G_N u - γ₁ v * δ * S.H_N u + γ₂ * δ * ceSb b u +
        r_val * ceG1 (airyZero 1) u) - S.G_N u =
      -(γ₁ v * δ * S.H_N u) + γ₂ * δ * ceSb b u + r_val * ceG1 (airyZero 1) u by ring]
    have h1 : |-(γ₁ v * δ * S.H_N u)| ≤ γ₁_max * |S.H_N uH| * δ := by
      rw [abs_neg, abs_mul, abs_mul, abs_of_pos (hγ₁_pos v hv), abs_of_pos hδ.1]
      calc _ ≤ γ₁_max * δ * |S.H_N uH| :=
            mul_le_mul (mul_le_mul_of_nonneg_right (hγ₁_le v hv) hδ.1.le) (huH_max hu)
              (abs_nonneg _) (mul_nonneg hγ₁_max_nn hδ.1.le)
        _ = _ := by ring
    have h2 : |γ₂ * δ * ceSb b u| ≤ γ₂ * |ceSb b uS| * δ := by
      rw [abs_mul, abs_mul, abs_of_pos hγ₂_pos, abs_of_pos hδ.1]
      calc _ ≤ γ₂ * δ * |ceSb b uS| :=
            mul_le_mul_of_nonneg_left (huS_max hu) (mul_nonneg hγ₂_pos.le hδ.1.le)
        _ = _ := by ring
    have h3 : |r_val * ceG1 (airyZero 1) u| ≤ ε₀ * ceG1 (airyZero 1) ug * δ := by
      rw [abs_mul, abs_of_nonneg (show 0 ≤ ceG1 (airyZero 1) u from sq_nonneg _)]
      calc _ ≤ (ε₀ * δ) * ceG1 (airyZero 1) ug :=
            mul_le_mul hr (hug_max hu) (sq_nonneg _) (mul_nonneg hε hδ.1.le)
        _ = _ := by ring
    have htri1 := abs_add_le (-(γ₁ v * δ * S.H_N u) + γ₂ * δ * ceSb b u) (r_val * ceG1 (airyZero 1) u)
    have htri2 := abs_add_le (-(γ₁ v * δ * S.H_N u)) (γ₂ * δ * ceSb b u)
    linarith

/-- Connection from `lem:hb-seed-mass` (`hb_seed_mass_exists`) directly to the B-spline
smoothing-gain lemma `PreEdgeAndSplineFloor.bspline_floor_smoothing_gain`. -/
theorem hb_seed_mass_bspline_gain {m : ℕ} (hm : 1 ≤ m) (S : HBSeedSpec) {b V_max ε₀ : ℝ}
    (hb : 0 < b) (hb_nodes : ∀ j : Fin S.m₀, j.val + 1 < S.m₀ → 0 < ceSb b (S.nodes j))
    (hV : 0 ≤ V_max) (hε : 0 ≤ ε₀) :
    ∃ δ₁ > 0, ∃ γ₂ > 0, ∃ γ₁ : ℝ → ℝ, ∃ c₁ > 0, ∃ c₂ > 0,
      ∀ v ∈ Icc (0 : ℝ) V_max, ∀ δ ∈ Ioc (0 : ℝ) δ₁, ∀ r_val : ℝ, |r_val| ≤ ε₀ * δ →
        let F := fun u : ℝ => S.G_N u - γ₁ v * δ * S.H_N u + γ₂ * δ * ceSb b u +
          r_val * ceG1 (airyZero 1) u
        let u₀ := S.lastNode - 2 * γ₁ v * δ
        (∫ u : ℝ, F u = -v * δ + r_val) ∧
        (∀ x ≥ |u₀| + ceBeta1 * δ / 2,
          (1 + x) ^ (-(3 / 2 : ℝ)) * (c₁ * δ + c₂ * min 1 ((ceBeta1 * δ / 2) ^ 2 * x)) ≤
            ∫ t in Icc (0 : ℝ) (ceBeta1 * δ / 2), F (-x + t) * bspline m (ceBeta1 * δ / 2) t) := by
  obtain ⟨δ₁, hδ₁, γ₂, hγ₂, γ₁, D, -, hmain, -⟩ := hb_seed_mass_exists S hb hb_nodes hV hε
  obtain ⟨c₁, hc₁, c₂, hc₂, hgain⟩ := bspline_floor_smoothing_gain hm D
  refine ⟨min δ₁ (1 / 2), lt_min hδ₁ (by norm_num), γ₂, hγ₂, γ₁, c₁, hc₁, c₂, hc₂,
    fun v hv δ hδ r_val hr => ?_⟩
  obtain ⟨⟨-, hint⟩, hsat, -⟩ := hmain v hv δ ⟨hδ.1, hδ.2.trans (min_le_left _ _)⟩ r_val hr
  exact ⟨hint, fun x hx => hgain _ δ _ hδ.1 (hδ.2.trans (min_le_right _ _)) hsat x hx⟩

/-- **Unconditional non-vacuity witness for `HBSeedSpec` (`N = Ai`, `m₀ = 1`):**
`G_Ai = -ceF1`, `H_Ai = ceG1 (airyZero 1)`, `I_Ai = 1`, `t₁ = airyZero 1`. -/
noncomputable def hbSeedSpec_airy_witness : HBSeedSpec where
  m₀ := 1
  m₀_pos := le_rfl
  nodes := fun _ => airyZero 1
  nodes_anti := fun a b h => absurd (Subsingleton.elim a b) h.ne
  last_le_a1 := le_rfl
  G_N := fun u => -ceF1 u
  H_N := ceG1 (airyZero 1)
  I_N := 1
  I_N_pos := one_pos
  continuous_G := continuous_ceF1.neg
  continuous_H := continuous_ceG1 (airyZero 1)
  integrable_G := ceF1_integral_eq_zero.1.neg
  integrable_H := ceG1_integrable
  integral_G := by rw [integral_neg, ceF1_integral_eq_zero.2, neg_zero]
  integral_H := ceG1_integral_eq_one
  G_nonneg_tail := fun u hu => neg_nonneg.mpr (ceF1_nonpos_of_le hu)
  H_eq_div_tail := fun u hu => by
    have hne : u ≠ airyZero 1 := hu.ne
    rw [ceF1, ceG1, dslope_of_ne _ hne, slope_def_field, airyAi_airyZero, sub_zero]
    field_simp [sub_ne_zero.mpr hne]; ring
  node_vanish := fun _ hj => absurd hj (by omega)
  r_node := 1; r_node_pos := one_pos; A_G := 0; A_H := 0; A_G_nonneg := le_rfl; A_H_nonneg := le_rfl
  G_lip_near := fun _ hj => absurd hj (by omega)
  H_lip_near := fun _ hj => absurd hj (by omega)
  c_osc_G := π⁻¹; C_r_G := 1; y₁_G := 25; ϑ_c_G := -π / 4
  c_osc_G_pos := inv_pos.mpr Real.pi_pos; C_r_G_nonneg := zero_le_one; y₁_G_ge := le_rfl
  G_osc_tail := by
    let r : ℝ → ℝ := fun y =>
      √π * y ^ (1 / 4 : ℝ) * airyAi (-y) - Real.cos ((2 / 3 : ℝ) * y ^ (3 / 2 : ℝ) - π / 4)
    refine ⟨r, fun y hy => ?_⟩
    have hy0 : 0 < y := by linarith
    have hAsym := airyAi_neg_asymptotic_theta hy0
    have hsin_eq : Real.sin (cohnTheta y) = Real.cos ((2 / 3 : ℝ) * y ^ (3 / 2 : ℝ) - π / 4) := by
      unfold cohnTheta
      rw [show 2 / 3 * y ^ (3 / 2 : ℝ) - π / 4 = (2 / 3 * y ^ (3 / 2 : ℝ) + π / 4) - π / 2 by ring,
        Real.cos_sub_pi_div_two]
    rw [hsin_eq] at hAsym
    have hpi_sqrt_pos : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
    have hy14_pos : 0 < y ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hy0 _
    have hr_abs : |r y| ≤ √π / (8 * y ^ (3 / 2 : ℝ)) := by
      have hfac : r y = √π * y ^ (1 / 4 : ℝ) *
          (airyAi (-y) - Real.cos ((2 / 3 : ℝ) * y ^ (3 / 2 : ℝ) - π / 4) / (√π * y ^ (1 / 4 : ℝ))) := by
        dsimp [r]; field_simp [hpi_sqrt_pos.ne', hy14_pos.ne']
      rw [hfac, abs_mul, abs_of_pos (mul_pos hpi_sqrt_pos hy14_pos)]
      have hrhs : √π * y ^ (1 / 4 : ℝ) * (1 / (8 * y ^ (7 / 4 : ℝ))) = √π / (8 * y ^ (3 / 2 : ℝ)) := by
        have hy_div : y ^ (1 / 4 : ℝ) / y ^ (7 / 4 : ℝ) = (y ^ (3 / 2 : ℝ))⁻¹ := by
          rw [← Real.rpow_sub hy0, show (1 / 4 : ℝ) - 7 / 4 = -(3 / 2 : ℝ) by norm_num, Real.rpow_neg hy0.le]
        calc _ = √π / 8 * (y ^ (1 / 4 : ℝ) / y ^ (7 / 4 : ℝ)) := by ring
          _ = √π / (8 * y ^ (3 / 2 : ℝ)) := by rw [hy_div]; ring
      exact (mul_le_mul_of_nonneg_left hAsym (by positivity)).trans_eq hrhs
    have hpi_lt_2 : √π ≤ 2 := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]; exact Real.sqrt_le_sqrt (by linarith [Real.pi_lt_d4])
    have hy32 : 25 * y ^ (1 / 2 : ℝ) ≤ y ^ (3 / 2 : ℝ) := by
      have hy_prod : y * y ^ (1 / 2 : ℝ) = y ^ (3 / 2 : ℝ) := by
        calc y * y ^ (1 / 2 : ℝ) = y ^ (1 : ℝ) * y ^ (1 / 2 : ℝ) := by rw [Real.rpow_one]
          _ = y ^ (3 / 2 : ℝ) := by rw [← Real.rpow_add hy0]; norm_num
      rw [← hy_prod]; exact mul_le_mul_of_nonneg_right hy (Real.rpow_nonneg hy0.le _)
    have hr_bd : |r y| ≤ 1 * y ^ (-(1 / 2 : ℝ)) := by
      rw [one_mul, Real.rpow_neg hy0.le]
      calc |r y| ≤ √π / (8 * y ^ (3 / 2 : ℝ)) := hr_abs
        _ ≤ 2 / (8 * (25 * y ^ (1 / 2 : ℝ))) :=
            div_le_div₀ (by positivity) hpi_lt_2 (by positivity) (by linarith)
        _ = (1 / 100) * (y ^ (1 / 2 : ℝ))⁻¹ := by ring
        _ ≤ (y ^ (1 / 2 : ℝ))⁻¹ := by nlinarith [inv_nonneg.mpr (Real.rpow_nonneg hy0.le (1 / 2 : ℝ))]
    refine ⟨hr_bd, ?_⟩
    have hy_comb : y ^ (-(3 / 2 : ℝ)) * y ^ (1 / 2 : ℝ) = y⁻¹ := by
      rw [← Real.rpow_add hy0, show -(3 / 2 : ℝ) + 1 / 2 = -1 by norm_num, Real.rpow_neg_one]
    have hy_sq14 : (y ^ (1 / 4 : ℝ)) ^ 2 = y ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hy0.le]; norm_num
    have hsep : 0 < y + airyZero 1 := by linarith [airyZero_one.1]
    have hf_eq : -ceF1 (-y) = airyAi (-y) ^ 2 / (y + airyZero 1) := by
      rw [ceF1, dslope_of_ne _ (by linarith [airyZero_one.1] : -y ≠ airyZero 1), slope_def_field,
        airyAi_airyZero, sub_zero, show -y - airyZero 1 = -(y + airyZero 1) by ring]
      field_simp [hsep.ne']
    rw [show Real.cos ((2 / 3 : ℝ) * y ^ (3 / 2 : ℝ) + -π / 4) + r y = √π * y ^ (1 / 4 : ℝ) * airyAi (-y) by
        dsimp [r]; rw [show -π / 4 = -(π / 4) by ring, ← sub_eq_add_neg]; ring,
      mul_pow, mul_pow, Real.sq_sqrt Real.pi_pos.le, hy_sq14, hf_eq]
    calc π⁻¹ * y ^ (-(3 / 2 : ℝ)) * (π * y ^ (1 / 2 : ℝ) * airyAi (-y) ^ 2)
        = airyAi (-y) ^ 2 / y := by
          rw [show π⁻¹ * y ^ (-(3 / 2 : ℝ)) * (π * y ^ (1 / 2 : ℝ) * airyAi (-y) ^ 2) =
            (π⁻¹ * π) * (y ^ (-(3 / 2 : ℝ)) * y ^ (1 / 2 : ℝ)) * airyAi (-y) ^ 2 by ring,
            inv_mul_cancel₀ Real.pi_ne_zero, one_mul, hy_comb]; ring
      _ ≤ airyAi (-y) ^ 2 / (y + airyZero 1) :=
          div_le_div_of_nonneg_left (sq_nonneg _) hsep (by linarith [airyZero_neg 1])

/-- Instantiation of `hb_seed_mass_bspline_gain` on the `N = Ai` witness (`hbSeedSpec_airy_witness`)
at `b = 1` (since `m₀ = 1` has no prescribed sites). -/
theorem hbSeedSpec_airy_smoothing_gain {m : ℕ} (hm : 1 ≤ m) {V_max ε₀ : ℝ}
    (hV : 0 ≤ V_max) (hε : 0 ≤ ε₀) :
    ∃ δ₁ > 0, ∃ γ₂ > 0, ∃ γ₁ : ℝ → ℝ, ∃ c₁ > 0, ∃ c₂ > 0,
      ∀ v ∈ Icc (0 : ℝ) V_max, ∀ δ ∈ Ioc (0 : ℝ) δ₁, ∀ r_val : ℝ, |r_val| ≤ ε₀ * δ →
        let F := fun u : ℝ => -ceF1 u - γ₁ v * δ * ceG1 (airyZero 1) u + γ₂ * δ * ceSb 1 u +
          r_val * ceG1 (airyZero 1) u
        let u₀ := airyZero 1 - 2 * γ₁ v * δ
        (∫ u : ℝ, F u = -v * δ + r_val) ∧
        (∀ x ≥ |u₀| + ceBeta1 * δ / 2,
          (1 + x) ^ (-(3 / 2 : ℝ)) * (c₁ * δ + c₂ * min 1 ((ceBeta1 * δ / 2) ^ 2 * x)) ≤
            ∫ t in Icc (0 : ℝ) (ceBeta1 * δ / 2), F (-x + t) * bspline m (ceBeta1 * δ / 2) t) :=
  hb_seed_mass_bspline_gain hm hbSeedSpec_airy_witness one_pos
    (fun _ h => absurd h (by dsimp [hbSeedSpec_airy_witness]; omega)) hV hε

/-! ### Part 3: Lemma `O.4` (`u1co:O4`) Part (1) & real-axis derivative floor -/

/-- Imaginary-axis edge phase `Φ(τ; L) = L τ + ∫₀^τ log(tanh(π u / 2) / (π u / 2)) du`
(`mellin_airy_toolkit.tex`, Lemma T.4(b); `u1c_o1_upper.tex`, `u1co:O4`). -/
noncomputable def edgePhi (L τ : ℝ) : ℝ :=
  L * τ + ∫ u in (0 : ℝ)..τ, Real.log (Real.tanh (π * u / 2) / (π * u / 2))

private lemma continuous_log_tanh_div_real :
    Continuous (fun u : ℝ => Real.log (Real.tanh (π * u / 2) / (π * u / 2))) := by
  rw [continuous_iff_continuousAt]
  intro u
  by_cases hu : u = 0
  · subst hu
    have hlim_pos : Tendsto (fun x : ℝ => Real.log (Real.tanh x / x)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hcongr : (fun x : ℝ => Real.log (Real.tanh x / x)) =ᶠ[𝓝[>] (0 : ℝ)] fun x => -ceEll x := by
        filter_upwards [self_mem_nhdsWithin] with x _; unfold ceEll; rw [← Real.log_inv, inv_div]
      simpa using ceEll_tendsto_zero.neg.congr' hcongr.symm
    have hlim_neg : Tendsto (fun x : ℝ => Real.log (Real.tanh x / x)) (𝓝[<] (0 : ℝ)) (𝓝 0) := by
      have hc0 : Tendsto (fun x : ℝ => -x) (𝓝[<] (0 : ℝ)) (𝓝 0) := by
        simpa using (continuous_neg.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
      have hneg : Tendsto (fun x : ℝ => -x) (𝓝[<] (0 : ℝ)) (𝓝[>] (0 : ℝ)) :=
        tendsto_nhdsWithin_iff.mpr ⟨hc0, by filter_upwards [self_mem_nhdsWithin] with x hx; exact neg_pos.mpr hx⟩
      exact (hlim_pos.comp hneg).congr fun x => by dsimp; rw [Real.tanh_neg, neg_div_neg_eq]
    have hmul : Tendsto (fun v : ℝ => π * v / 2) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℝ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have hc : Continuous (fun v : ℝ => π * v / 2) := by fun_prop
        simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with v hv
        exact div_ne_zero (mul_ne_zero Real.pi_ne_zero hv) two_ne_zero
    have hne := ((nhdsLT_sup_nhdsGT (0 : ℝ)) ▸ (hlim_neg.sup hlim_pos)).comp hmul
    have h0 : Real.log (Real.tanh (π * 0 / 2) / (π * 0 / 2)) = 0 := by simp
    rw [ContinuousAt, h0]
    intro s hs
    change (fun v : ℝ => Real.log (Real.tanh (π * v / 2) / (π * v / 2))) ⁻¹' s ∈ 𝓝 0
    obtain ⟨U, hU, hUs⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp (hne hs)
    refine Filter.mem_of_superset hU fun x hx => ?_
    by_cases hx0 : x = 0
    · subst hx0; simpa [h0] using mem_of_mem_nhds hs
    · exact hUs ⟨hx, hx0⟩
  · have hx0 : π * u / 2 ≠ 0 := div_ne_zero (mul_ne_zero Real.pi_ne_zero hu) two_ne_zero
    have ht_pos : 0 < Real.tanh (π * u / 2) / (π * u / 2) := by
      rcases lt_or_gt_of_ne hu with hlt | hgt
      · rw [← neg_div_neg_eq, ← Real.tanh_neg]
        exact div_pos (tanh_pos_of_pos (by nlinarith [Real.pi_pos])) (by nlinarith [Real.pi_pos])
      · exact div_pos (tanh_pos_of_pos (by positivity)) (by positivity)
    have htanh_cont : Continuous Real.tanh := by
      rw [show Real.tanh = fun x : ℝ => Real.sinh x / Real.cosh x from funext Real.tanh_eq_sinh_div_cosh]
      exact Real.continuous_sinh.div Real.continuous_cosh (fun x => (Real.cosh_pos x).ne')
    have hlin : Continuous (fun v : ℝ => π * v / 2) := by fun_prop
    have hq_cont : ContinuousAt (fun v : ℝ => Real.tanh (π * v / 2) / (π * v / 2)) u :=
      (ContinuousAt.comp (g := Real.tanh) (f := fun v : ℝ => π * v / 2)
        htanh_cont.continuousAt hlin.continuousAt).div hlin.continuousAt hx0
    exact ContinuousAt.comp (g := Real.log)
      (f := fun v : ℝ => Real.tanh (π * v / 2) / (π * v / 2))
      (Real.continuousAt_log ht_pos.ne') hq_cont

lemma edgePhi_eq_stripS0Tilde (L τ : ℝ) :
    edgePhi L τ = L * τ + (stripS0Tilde ((τ : ℂ) * Complex.I)).im := by
  rw [stripS0Tilde_imag]; simp [edgePhi]

lemma hasDerivAt_edgePhi (L τ : ℝ) : HasDerivAt (edgePhi L) (edgePhiDeriv L τ) τ := by
  have h1 : HasDerivAt (fun t : ℝ => L * t) L τ := by simpa using (hasDerivAt_id τ).const_mul L
  have h2 : HasDerivAt (fun t : ℝ => ∫ u in (0 : ℝ)..t, Real.log (Real.tanh (π * u / 2) / (π * u / 2)))
      (Real.log (Real.tanh (π * τ / 2) / (π * τ / 2))) τ :=
    intervalIntegral.integral_hasDerivAt_right (continuous_log_tanh_div_real.intervalIntegrable 0 τ)
      (continuous_log_tanh_div_real.stronglyMeasurableAtFilter volume (𝓝 τ))
      continuous_log_tanh_div_real.continuousAt
  refine (h1.add h2).congr_deriv ?_
  unfold edgePhiDeriv; split_ifs with h0
  · simp [h0]
  · rcases lt_or_gt_of_ne h0 with hlt | hgt
    · rw [abs_of_neg hlt, show π * (-τ) / 2 = -(π * τ / 2) by ring, Real.tanh_neg, neg_div_neg_eq]
    · rw [abs_of_pos hgt]

lemma edgePhi_eq_cubic_add_ceHth (L τ : ℝ) :
    edgePhi L τ = L * τ - π ^ 2 / 36 * τ ^ 3 + ∫ u in (0 : ℝ)..τ, ceHth (π * u / 2) := by
  have hsq : ∫ u in (0 : ℝ)..τ, (π * u / 2) ^ 2 / 3 = π ^ 2 / 36 * τ ^ 3 := by
    simp_rw [show ∀ u : ℝ, (π * u / 2) ^ 2 / 3 = (π ^ 2 / 12) * u ^ 2 from fun u => by ring,
      intervalIntegral.integral_const_mul, integral_pow]; ring
  have hadd : ∫ u in (0 : ℝ)..τ, ceHth (π * u / 2) =
      (∫ u in (0 : ℝ)..τ, Real.log (Real.tanh (π * u / 2) / (π * u / 2))) + π ^ 2 / 36 * τ ^ 3 := by
    simp_rw [ceHth]
    rw [intervalIntegral.integral_add (continuous_log_tanh_div_real.intervalIntegrable 0 τ)
      ((by fun_prop : Continuous fun u : ℝ => (π * u / 2) ^ 2 / 3).intervalIntegrable 0 τ), hsq]
  unfold edgePhi; linarith

/-- Unique positive saddle `τ₀(L) > 0` satisfying `ceEll (π * τ₀(L) / 2) = L` for `L > 0`. -/
theorem existsUnique_tau0 {L : ℝ} (hL : 0 < L) :
    ∃! τ₀ : ℝ, 0 < τ₀ ∧ ceEll (π * τ₀ / 2) = L := by
  let x₁ : ℝ := Real.exp (L + 1)
  have hx₁ : 1 < x₁ := Real.one_lt_exp_iff.mpr (by linarith)
  have hx₁_pos : 0 < x₁ := by linarith
  have hth_lt1 : Real.tanh x₁ < 1 := by
    rw [Real.tanh_eq_sinh_div_cosh, div_lt_one (Real.cosh_pos _), ← sub_pos, Real.cosh_eq, Real.sinh_eq]
    rw [show (Real.exp x₁ + Real.exp (-x₁)) / 2 - (Real.exp x₁ - Real.exp (-x₁)) / 2 =
      Real.exp (-x₁) by ring]
    exact Real.exp_pos _
  have hce_x₁ : L < ceEll x₁ := by
    have hlog : L + 1 = Real.log x₁ := by dsimp [x₁]; rw [Real.log_exp]
    have hx_lt : x₁ < x₁ / Real.tanh x₁ := by
      rw [lt_div_iff₀ (tanh_pos_of_pos hx₁_pos)]
      exact mul_lt_of_lt_one_right hx₁_pos hth_lt1
    have hlog_lt := Real.log_lt_log hx₁_pos hx_lt
    unfold ceEll; linarith
  obtain ⟨x₀, hx₀_lt, hx₀_pos, hx₀_x₁⟩ :=
    ((ceEll_tendsto_zero.eventually (gt_mem_nhds hL)).and (Ioo_mem_nhdsGT hx₁_pos)).exists
  have hcont : ContinuousOn ceEll (Icc x₀ x₁) := fun x hx =>
    (ceEll_hasDerivAt (by linarith [hx.1])).continuousAt.continuousWithinAt
  obtain ⟨x, hx_mem, hx_eq⟩ := intermediate_value_Icc hx₀_x₁.le hcont ⟨hx₀_lt.le, hce_x₁.le⟩
  have hx_pos : 0 < x := by linarith [hx_mem.1]
  refine ⟨2 * x / π, ⟨by positivity [Real.pi_pos], ?_⟩, ?_⟩
  · rwa [show π * (2 * x / π) / 2 = x by field_simp [Real.pi_ne_zero]]
  · rintro τ₀' ⟨hτ₀'_pos, hτ₀'_eq⟩
    have hx' : 0 < π * τ₀' / 2 := by positivity
    have hinj := ceEll_strictMonoOn.injOn (mem_Ioi.mpr hx') (mem_Ioi.mpr hx_pos)
      (hτ₀'_eq.trans hx_eq.symm)
    field_simp [Real.pi_ne_zero] at hinj
    rw [eq_div_iff Real.pi_ne_zero]; linarith

/-- Unique positive saddle `τ₀(L)` satisfying `ceEll (π * τ₀(L) / 2) = L` for `L > 0`. -/
noncomputable def tau0 (L : ℝ) : ℝ :=
  if h : 0 < L then Classical.choose (existsUnique_tau0 h).exists else 0

lemma tau0_pos {L : ℝ} (hL : 0 < L) : 0 < tau0 L := by
  simp only [tau0, hL, ↓reduceDIte]; exact (Classical.choose_spec (existsUnique_tau0 hL).exists).1

lemma ceEll_tau0 {L : ℝ} (hL : 0 < L) : ceEll (π * tau0 L / 2) = L := by
  simp only [tau0, hL, ↓reduceDIte]; exact (Classical.choose_spec (existsUnique_tau0 hL).exists).2

private lemma ceEll_sub_ceHth {x : ℝ} (_hx : 0 < x) : ceEll x = x ^ 2 / 3 - ceHth x := by
  unfold ceEll ceHth
  rw [show Real.tanh x / x = (x / Real.tanh x)⁻¹ by rw [inv_div], Real.log_inv]; ring

private lemma edgePhiDeriv_of_ne {L τ : ℝ} (hτ : τ ≠ 0) :
    edgePhiDeriv L τ = L - ceEll (π * |τ| / 2) := by
  simp only [edgePhiDeriv, ceEll, hτ, ↓reduceIte]
  have heq : Real.log (Real.tanh (π * |τ| / 2) / (π * |τ| / 2)) =
      -Real.log (π * |τ| / 2 / Real.tanh (π * |τ| / 2)) := by
    rw [show Real.tanh (π * |τ| / 2) / (π * |τ| / 2) =
      (π * |τ| / 2 / Real.tanh (π * |τ| / 2))⁻¹ by rw [inv_div], Real.log_inv]
  rw [heq]; ring

lemma tau0_bounds {L : ℝ} (hL0 : 0 < L) (hL2 : L ≤ 0.002) :
    tau0 L < 0.05 ∧ tau0 L ≤ 1.105 * Real.sqrt L ∧ 2 * tau0 L < 0.0989 := by
  have hpi_lo : (3.14 : ℝ) < π := Real.pi_gt_d2
  have hpi_hi : π < 3.1416 := Real.pi_lt_d4
  have h05 : L < ceEll (π * 0.05 / 2) := by
    set x := π * 0.05 / 2
    have hx0 : 0 < x := by positivity
    have hH := ceHth_le_of_le_one hx0 (by dsimp [x]; linarith : x ≤ 1)
    have hpow4 : x ^ 4 ≤ (0.0786 : ℝ) ^ 4 := pow_le_pow_left₀ hx0.le (by dsimp [x]; linarith) 4
    have hpow2 : (0.0785 : ℝ) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ (by norm_num) (by dsimp [x]; linarith) 2
    rw [ceEll_sub_ceHth hx0]; norm_num at hpow2 hpow4; linarith
  have hτ_05 : tau0 L < 0.05 := by
    by_contra hcon; push Not at hcon
    have hmono := ceEll_strictMonoOn.monotoneOn (mem_Ioi.mpr (by positivity))
      (mem_Ioi.mpr (by positivity [tau0_pos hL0])) (by nlinarith [Real.pi_pos] : π * 0.05 / 2 ≤ π * tau0 L / 2)
    linarith [ceEll_tau0 hL0]
  have hτ_sq : tau0 L ≤ 1.105 * Real.sqrt L := by
    set x := π * tau0 L / 2
    have hx0 : 0 < x := by dsimp [x]; positivity [tau0_pos hL0]
    have hx_hi : x < 0.07854 := by dsimp [x]; nlinarith
    have hH := ceHth_le_of_le_one hx0 (by linarith : x ≤ 1)
    have hL_ge : x ^ 2 / 3 * (1 - 2 / 5 * 0.07854 ^ 2) ≤ L := by
      rw [← ceEll_tau0 hL0, ceEll_sub_ceHth hx0]
      have hx2_le := pow_le_pow_left₀ hx0.le hx_hi.le 2
      nlinarith [sq_nonneg x]
    have h12 : 12 * L ≥ 0.9975 * π ^ 2 * tau0 L ^ 2 := by
      rw [show x ^ 2 = π ^ 2 * tau0 L ^ 2 / 4 by dsimp [x]; ring] at hL_ge
      have hc : (0.9975 : ℝ) ≤ 1 - 2 / 5 * 0.07854 ^ 2 := by norm_num
      nlinarith [sq_nonneg π, sq_nonneg (tau0 L)]
    have hpi_sq : (3.14 : ℝ) ^ 2 ≤ π ^ 2 := pow_le_pow_left₀ (by norm_num) hpi_lo.le 2
    have hsq_tau : tau0 L ^ 2 ≤ (1.105 * Real.sqrt L) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hL0.le]; nlinarith [sq_nonneg (tau0 L)]
    exact le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (by positivity) hsq_tau
  have h2τ : 2 * tau0 L < 0.0989 := by
    have hsqrt_le : Real.sqrt L ≤ Real.sqrt 0.002 := Real.sqrt_le_sqrt hL2
    have hsq : (2.21 * Real.sqrt 0.002) ^ 2 < 0.0989 ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 0.002)]; norm_num
    linarith [lt_of_pow_lt_pow_left₀ 2 (by norm_num) hsq]
  exact ⟨hτ_05, hτ_sq, h2τ⟩

private lemma edgePhi_pos_saddle {L : ℝ} (hL : 0 < L) :
    (4 * Real.sqrt 3 / (3 * π)) * L ^ (3 / 2 : ℝ) < edgePhi L (tau0 L) := by
  let τA : ℝ := (2 * Real.sqrt 3 / π) * Real.sqrt L
  have hτA_pos : 0 < τA := by positivity [Real.pi_pos, Real.sqrt_pos.mpr hL]
  have hτA_lt : τA < tau0 L := tau0_gt_sqrt hL (tau0_pos hL) (ceEll_tau0 hL)
  have hmono : MonotoneOn (edgePhi L) (Icc 0 (tau0 L)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 (tau0 L))
      (fun τ _ => (hasDerivAt_edgePhi L τ).continuousAt.continuousWithinAt)
      (fun τ _ => (hasDerivAt_edgePhi L τ).differentiableAt.differentiableWithinAt) fun τ hτ => ?_
    rw [interior_Icc] at hτ; rw [(hasDerivAt_edgePhi L τ).deriv, edgePhiDeriv_of_ne hτ.1.ne']
    have hx_le : π * |τ| / 2 ≤ π * tau0 L / 2 := by rw [abs_of_pos hτ.1]; nlinarith [Real.pi_pos, hτ.2]
    have hce_le := ceEll_strictMonoOn.monotoneOn (mem_Ioi.mpr (by positivity [abs_pos.mpr hτ.1.ne']))
      (mem_Ioi.mpr (by positivity [tau0_pos hL])) hx_le
    linarith [ceEll_tau0 hL]
  have hphi_le : edgePhi L τA ≤ edgePhi L (tau0 L) :=
    hmono ⟨hτA_pos.le, hτA_lt.le⟩ ⟨(tau0_pos hL).le, le_rfl⟩ hτA_lt.le
  have hceH_pos_int : 0 < ∫ u in (0 : ℝ)..τA, ceHth (π * u / 2) := by
    rw [intervalIntegral.integral_of_le hτA_pos.le]
    have hcont : Continuous (fun u : ℝ => ceHth (π * u / 2)) := by
      rw [show (fun u : ℝ => ceHth (π * u / 2)) =
        fun u : ℝ => Real.log (Real.tanh (π * u / 2) / (π * u / 2)) + (π * u / 2) ^ 2 / 3 from rfl]
      exact continuous_log_tanh_div_real.add (by fun_prop)
    rw [setIntegral_pos_iff_support_of_nonneg_ae
      (Eventually.of_forall fun u => by
        rcases lt_trichotomy u 0 with h | rfl | h
        · have hev : ceHth (-(π * u / 2)) = ceHth (π * u / 2) := by
            unfold ceHth; rw [Real.tanh_neg, neg_div_neg_eq, neg_sq]
          rw [← hev]; exact (ceHth_pos (by nlinarith [Real.pi_pos])).le
        · simp [ceHth]
        · exact (ceHth_pos (by positivity)).le)
      hcont.integrableOn_Ioc]
    have hsub : Ioc 0 τA ⊆ Function.support (fun u => ceHth (π * u / 2)) ∩ Ioc 0 τA :=
      fun u hu => ⟨(ceHth_pos (by positivity [hu.1])).ne', hu⟩
    exact (by rw [Real.volume_Ioc, sub_zero, ENNReal.ofReal_pos]; exact hτA_pos :
      0 < volume (Ioc (0 : ℝ) τA)).trans_le (measure_mono hsub)
  have hcubic : L * τA - π ^ 2 / 36 * τA ^ 3 = (4 * Real.sqrt 3 / (3 * π)) * L ^ (3 / 2 : ℝ) := by
    have hL32 : L ^ (3 / 2 : ℝ) = Real.sqrt L * L := by
      rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.rpow_add hL,
        ← Real.sqrt_eq_rpow, Real.rpow_one, mul_comm]
    dsimp [τA]; rw [hL32]; field_simp [Real.pi_ne_zero]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sq_sqrt hL.le]
  rw [edgePhi_eq_cubic_add_ceHth, hcubic] at hphi_le
  linarith

/-- Unique positive cubic normal-form scale `edgeAlphaTilde L > 0` satisfying
`(4 * √3 / (3 * π)) * (edgeAlphaTilde L) ^ (3/2) = edgePhi L (tau0 L)` for `L > 0`. -/
theorem existsUnique_edgeAlphaTilde {L : ℝ} (hL : 0 < L) :
    ∃! α : ℝ, 0 < α ∧ (4 * Real.sqrt 3 / (3 * π)) * α ^ (3 / 2 : ℝ) = edgePhi L (tau0 L) := by
  let c : ℝ := 4 * Real.sqrt 3 / (3 * π)
  have hc : 0 < c := by positivity [Real.pi_pos]
  have hΦ : 0 < edgePhi L (tau0 L) :=
    lt_trans (by positivity [Real.rpow_pos_of_pos hL (3 / 2 : ℝ)]) (edgePhi_pos_saddle hL)
  let α₀ : ℝ := (edgePhi L (tau0 L) / c) ^ (2 / 3 : ℝ)
  have hα₀ : 0 < α₀ := Real.rpow_pos_of_pos (div_pos hΦ hc) _
  refine ⟨α₀, ⟨hα₀, ?_⟩, ?_⟩
  · dsimp [α₀]
    rw [← Real.rpow_mul (div_pos hΦ hc).le, show (2 / 3 : ℝ) * (3 / 2 : ℝ) = 1 by norm_num, Real.rpow_one,
      mul_div_cancel₀ _ hc.ne']
  · rintro α ⟨hα, hα_eq⟩
    have hpow : α ^ (3 / 2 : ℝ) = edgePhi L (tau0 L) / c :=
      eq_div_of_mul_eq hc.ne' (by dsimp [c] at hα_eq ⊢; linarith)
    calc α = (α ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by
          rw [← Real.rpow_mul hα.le, show (3 / 2 : ℝ) * (2 / 3 : ℝ) = 1 by norm_num, Real.rpow_one]
      _ = α₀ := by rw [hpow]

/-- Cubic normal-form scale `α̃(L)` (`u1c_o1_upper.tex`, `u1co:O4`). -/
noncomputable def edgeAlphaTilde (L : ℝ) : ℝ :=
  if h : 0 < L then Classical.choose (existsUnique_edgeAlphaTilde h).exists else 0

/-- Normal-form ratio `κ₀(L) := α̃(L) / L` (`u1c_o1_upper.tex`, `u1co:O4`). -/
noncomputable def edgeKappa0 (L : ℝ) : ℝ := edgeAlphaTilde L / L

lemma edgeAlphaTilde_pos {L : ℝ} (hL : 0 < L) : 0 < edgeAlphaTilde L := by
  simp only [edgeAlphaTilde, hL, ↓reduceDIte]; exact (Classical.choose_spec (existsUnique_edgeAlphaTilde hL).exists).1

lemma edgeAlphaTilde_eq {L : ℝ} (hL : 0 < L) :
    (4 * Real.sqrt 3 / (3 * π)) * edgeAlphaTilde L ^ (3 / 2 : ℝ) = edgePhi L (tau0 L) := by
  simp only [edgeAlphaTilde, hL, ↓reduceDIte]; exact (Classical.choose_spec (existsUnique_edgeAlphaTilde hL).exists).2

/-- **Lemma `O.4` Part (1) (`u1c_o1_upper.tex`, `u1co:O4`):**
for `L ∈ (0, 0.002]`, `1 < κ₀(L) ≤ 1 + L / 4`. -/
theorem edgeKappa0_bounds {L : ℝ} (hL0 : 0 < L) (hL2 : L ≤ 0.002) :
    1 < edgeKappa0 L ∧ edgeKappa0 L ≤ 1 + L / 4 := by
  let c : ℝ := 4 * Real.sqrt 3 / (3 * π)
  have hc : 0 < c := by positivity [Real.pi_pos]
  have hα_pos : 0 < edgeAlphaTilde L := edgeAlphaTilde_pos hL0
  have hα_eq : c * edgeAlphaTilde L ^ (3 / 2 : ℝ) = edgePhi L (tau0 L) := edgeAlphaTilde_eq hL0
  have hL_lt : c * L ^ (3 / 2 : ℝ) < c * edgeAlphaTilde L ^ (3 / 2 : ℝ) := by
    rw [hα_eq]; exact edgePhi_pos_saddle hL0
  have hrpow_lt : L ^ (3 / 2 : ℝ) < edgeAlphaTilde L ^ (3 / 2 : ℝ) := lt_of_mul_lt_mul_left hL_lt hc.le
  have hL_lt_α : L < edgeAlphaTilde L := by
    by_contra hcon; push Not at hcon
    exact absurd (Real.rpow_le_rpow hα_pos.le hcon (by norm_num : (0 : ℝ) ≤ 3 / 2)) hrpow_lt.not_ge
  have hκ_gt : 1 < edgeKappa0 L := (one_lt_div hL0).mpr hL_lt_α
  obtain ⟨hτ_05, hτ_sq, -⟩ := tau0_bounds hL0 hL2
  have hτ_pos : 0 < tau0 L := tau0_pos hL0
  have hcubic_le : L * tau0 L - π ^ 2 / 36 * tau0 L ^ 3 ≤ c * L ^ (3 / 2 : ℝ) := by
    let s : ℝ := π * tau0 L / (2 * Real.sqrt 3)
    let r : ℝ := Real.sqrt L
    have hs : 0 ≤ s := by positivity
    have hr : 0 < r := Real.sqrt_pos.mpr hL0
    have hL_eq : L = r ^ 2 := (Real.sq_sqrt hL0.le).symm
    have hτ_eq : tau0 L = 2 * Real.sqrt 3 / π * s := by dsimp [s]; field_simp [Real.pi_ne_zero]
    have hL32 : L ^ (3 / 2 : ℝ) = r ^ 3 := by
      rw [hL_eq, ← Real.rpow_natCast, ← Real.rpow_mul hr.le]; norm_num
    have hdiff : c * r ^ 3 - (r ^ 2 * (2 * Real.sqrt 3 / π * s) - π ^ 2 / 36 * (2 * Real.sqrt 3 / π * s) ^ 3) =
        (2 * Real.sqrt 3 / π) * ((s - r) ^ 2 * (s + 2 * r) / 3) := by
      have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      dsimp [c]; field_simp [Real.pi_ne_zero]
      rw [hsq3]; ring
    rw [← hL32, ← hL_eq, ← hτ_eq] at hdiff
    have hnn : 0 ≤ (2 * Real.sqrt 3 / π) * ((s - r) ^ 2 * (s + 2 * r) / 3) := by positivity [Real.pi_pos]
    linarith
  have hint_ceH : IntervalIntegrable (fun u : ℝ => ceHth (π * u / 2)) volume 0 (tau0 L) := by
    rw [show (fun u : ℝ => ceHth (π * u / 2)) =
      fun u : ℝ => Real.log (Real.tanh (π * u / 2) / (π * u / 2)) + (π * u / 2) ^ 2 / 3 from rfl]
    exact (continuous_log_tanh_div_real.add (by fun_prop)).intervalIntegrable 0 (tau0 L)
  have hint_bd : IntervalIntegrable (fun u : ℝ => (π ^ 4 / 120) * u ^ 4) volume 0 (tau0 L) :=
    (by fun_prop : Continuous fun u : ℝ => (π ^ 4 / 120) * u ^ 4).intervalIntegrable 0 (tau0 L)
  have hrem_le : ∫ u in (0 : ℝ)..tau0 L, ceHth (π * u / 2) ≤ (π ^ 4 / 600) * tau0 L ^ 5 := by
    have hmono := intervalIntegral.integral_mono_on hτ_pos.le hint_ceH hint_bd fun u hu => by
      rcases eq_or_lt_of_le hu.1 with rfl | hu0
      · simp [ceHth]
      · have hpi_hi : π < 3.1416 := Real.pi_lt_d4
        have hle := ceHth_le_of_le_one (by positivity) (by nlinarith [hu.2] : π * u / 2 ≤ 1)
        rwa [show 2 / 15 * (π * u / 2) ^ 4 = π ^ 4 / 120 * u ^ 4 by ring] at hle
    exact hmono.trans_eq (by rw [intervalIntegral.integral_const_mul, integral_pow]; ring)
  have hpi5 : π ^ 5 < (3.1416 : ℝ) ^ 5 := pow_lt_pow_left₀ Real.pi_lt_d4 Real.pi_pos.le (by norm_num)
  have hsqrt3 : (1.732 : ℝ) < Real.sqrt 3 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1.732)]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hconst_le : (π ^ 4 / 600) * (1.105 : ℝ) ^ 5 ≤ c * 0.365 := by
    have hnum : 3 * π ^ 5 * (1.105 : ℝ) ^ 5 ≤ 876 * Real.sqrt 3 := by norm_num at hpi5; linarith
    dsimp [c]
    rw [show (π ^ 4 / 600) * (1.105 : ℝ) ^ 5 = (π ^ 4 * (1.105 : ℝ) ^ 5) / 600 by ring,
      show (4 * Real.sqrt 3 / (3 * π)) * 0.365 = (876 * Real.sqrt 3) / (600 * (3 * π)) by ring,
      div_le_div_iff₀ (by norm_num) (by positivity [Real.pi_pos])]
    linarith
  have hL52 : tau0 L ^ 5 ≤ (1.105 : ℝ) ^ 5 * L * L ^ (3 / 2 : ℝ) := by
    have hpow5 := pow_le_pow_left₀ hτ_pos.le hτ_sq 5
    have hsqL : Real.sqrt L ^ 5 = L * L ^ (3 / 2 : ℝ) := by
      have h2 : L ^ (3 / 2 : ℝ) = Real.sqrt L ^ 3 := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
      rw [show Real.sqrt L ^ 5 = Real.sqrt L ^ 2 * Real.sqrt L ^ 3 by ring, Real.sq_sqrt hL0.le, h2]
    rwa [mul_pow, hsqL, ← mul_assoc] at hpow5
  have hΦ_ub : edgePhi L (tau0 L) ≤ c * L ^ (3 / 2 : ℝ) * (1 + 0.365 * L) := by
    rw [edgePhi_eq_cubic_add_ceHth]
    have h1 : (π ^ 4 / 600) * tau0 L ^ 5 ≤ ((π ^ 4 / 600) * (1.105 : ℝ) ^ 5) * (L * L ^ (3 / 2 : ℝ)) := by
      calc _ ≤ (π ^ 4 / 600) * ((1.105 : ℝ) ^ 5 * L * L ^ (3 / 2 : ℝ)) := mul_le_mul_of_nonneg_left hL52 (by positivity)
        _ = _ := by ring
    have h2 : ((π ^ 4 / 600) * (1.105 : ℝ) ^ 5) * (L * L ^ (3 / 2 : ℝ)) ≤ (c * 0.365) * (L * L ^ (3 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_right hconst_le (by positivity [Real.rpow_nonneg hL0.le (3 / 2 : ℝ)])
    linarith
  have hκ_pow : edgeKappa0 L ^ (3 / 2 : ℝ) ≤ 1 + 0.365 * L := by
    have heq : c * edgeAlphaTilde L ^ (3 / 2 : ℝ) = (c * L ^ (3 / 2 : ℝ)) * edgeKappa0 L ^ (3 / 2 : ℝ) := by
      rw [show edgeKappa0 L = edgeAlphaTilde L * L⁻¹ from div_eq_mul_inv _ _,
        Real.mul_rpow hα_pos.le (inv_nonneg.mpr hL0.le), Real.inv_rpow hL0.le]
      field_simp [(Real.rpow_pos_of_pos hL0 (3 / 2 : ℝ)).ne']
    rw [← hα_eq, heq] at hΦ_ub
    exact le_of_mul_le_mul_left hΦ_ub (by positivity [Real.rpow_pos_of_pos hL0 (3 / 2 : ℝ)])
  have hκ_cube : edgeKappa0 L ^ 3 ≤ (1 + 0.365 * L) ^ 2 := by
    have hpow := Real.rpow_le_rpow (Real.rpow_nonneg (by linarith : 0 ≤ edgeKappa0 L) _) hκ_pow (by norm_num : (0 : ℝ) ≤ 2)
    rw [← Real.rpow_mul (by linarith : 0 ≤ edgeKappa0 L), show (3 / 2 : ℝ) * 2 = (3 : ℕ) by norm_num,
      Real.rpow_natCast, Real.rpow_two] at hpow
    exact hpow
  have hpoly : (1 + 0.365 * L) ^ 2 ≤ (1 + L / 4) ^ 3 := by
    have hdiff : (1 + L / 4) ^ 3 - (1 + 0.365 * L) ^ 2 = 0.02 * L + 0.054275 * L ^ 2 + L ^ 3 / 64 := by ring
    nlinarith [sq_nonneg L, pow_nonneg hL0.le 3]
  exact ⟨hκ_gt, le_of_pow_le_pow_left₀ (n := 3) (by norm_num) (by linarith) (hκ_cube.trans hpoly)⟩

/-- **Lemma `O.4`, real-axis derivative floor (`u1c_o1_upper.tex`, `u1co:O4(3)`):**
for `L ∈ (0, 0.002]` and all `τ ∈ ℝ` with `0.128 ≤ |τ|` (in particular `0.128 ≤ |τ| < 1`),
`0.011 ≤ -edgePhiDeriv L τ`. -/
theorem edgePhiDeriv_ge_band {L τ : ℝ} (_hL0 : 0 < L) (hL2 : L ≤ 0.002) (hτ : 0.128 ≤ |τ|) :
    0.011 ≤ -edgePhiDeriv L τ := by
  have hτ_ne : τ ≠ 0 := fun h0 => by rw [h0, abs_zero] at hτ; norm_num at hτ
  have hpi_lo : (3.14 : ℝ) < π := Real.pi_gt_d2; have hpi_hi : π < 3.1416 := Real.pi_lt_d4
  let x₀ : ℝ := π * 0.128 / 2; have hx₀_pos : 0 < x₀ := by dsimp [x₀]; positivity
  have hH := ceHth_le_of_le_one hx₀_pos (by dsimp [x₀]; linarith : x₀ ≤ 1)
  have hx₀2 : 0.20096 ^ 2 ≤ x₀ ^ 2 := pow_le_pow_left₀ (by norm_num) (by dsimp [x₀]; linarith) 2
  have hx₀4 : x₀ ^ 4 ≤ 0.202 ^ 4 := pow_le_pow_left₀ hx₀_pos.le (by dsimp [x₀]; linarith) 4
  have hce_x₀ : 0.013 ≤ ceEll x₀ := by rw [ceEll_sub_ceHth hx₀_pos]; norm_num at hx₀2 hx₀4; linarith
  have hce_mono := ceEll_strictMonoOn.monotoneOn (mem_Ioi.mpr hx₀_pos)
    (mem_Ioi.mpr (by positivity [abs_pos.mpr hτ_ne])) (by dsimp [x₀]; nlinarith [Real.pi_pos] : x₀ ≤ π * |τ| / 2)
  rw [edgePhiDeriv_of_ne hτ_ne]; linarith

/-! ### Part 4: Axiom checks -/
/-- info: 'FormalResearch.CohnElkies.airy_seed_integrals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.airy_seed_integrals
/-- info: 'FormalResearch.CohnElkies.ceSb_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.ceSb_integral
/-- info: 'FormalResearch.CohnElkies.ceG1_add_ceG1Deriv_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.ceG1_add_ceG1Deriv_pos
/-- info: 'FormalResearch.CohnElkies.ceSb_e23_rational_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.ceSb_e23_rational_form
/-- info: 'FormalResearch.CohnElkies.ceSb_neg_asymptotic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.ceSb_neg_asymptotic
/-- info: 'FormalResearch.CohnElkies.ceSb_lower_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.ceSb_lower_floor
/-- info: 'FormalResearch.CohnElkies.exists_ceSb_pos_at_nodes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.exists_ceSb_pos_at_nodes
/-- info: 'FormalResearch.CohnElkies.hb_seed_mass_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.hb_seed_mass_exists
/-- info: 'FormalResearch.CohnElkies.hb_seed_mass_bspline_gain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.hb_seed_mass_bspline_gain
/-- info: 'FormalResearch.CohnElkies.hbSeedSpec_airy_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.hbSeedSpec_airy_witness
/-- info: 'FormalResearch.CohnElkies.hbSeedSpec_airy_smoothing_gain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.hbSeedSpec_airy_smoothing_gain
/-- info: 'FormalResearch.CohnElkies.existsUnique_tau0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.existsUnique_tau0
/-- info: 'FormalResearch.CohnElkies.tau0_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.tau0_bounds
/-- info: 'FormalResearch.CohnElkies.existsUnique_edgeAlphaTilde' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.existsUnique_edgeAlphaTilde
/-- info: 'FormalResearch.CohnElkies.edgeKappa0_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.edgeKappa0_bounds
/-- info: 'FormalResearch.CohnElkies.edgePhiDeriv_ge_band' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.edgePhiDeriv_ge_band

end FormalResearch.CohnElkies
