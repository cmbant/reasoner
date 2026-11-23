module

public import FormalResearch.SignUncertainty.LaplaceWeight
public import FormalResearch.SignUncertainty.DeepLobeMass

/-!
# Weighted tails of Hankel eigenfunctions (`ce_shells.tex`, proof of `thm:ce-shell-gap`, `eq:ce-laplace-limit`)

For `c → ∞` and `y ≥ 0` let `W = laplaceWeight c y` (`LaplaceWeight.lean`), `P = c/π²`, `t = c^{1/3}`.
`W` is decreasing in `Δ` and `W(Δ) = W(P) (P/Δ)^{cζ_c}` exactly. This module bounds the weighted
absolute masses `∫ |g| ρ₀ W` of a Hankel eigenfunction `g` on the two regions where the weight is not
yet controlled by the window convergence:

* region II, `Δ ≤ c(1/π² - 1/48)` (`regionII_weighted`): the pointwise bound `ρ₀|g| ≤ B Δ^{c/2-1}` of the
  deep lobe and the exact weight scaling give `16 M[g] e^{-c/25} W(P) (P/Δ₁)^{cζ}`;
* region I, `c(1/π²-1/48) < Δ < P - R t` (`regionI_weighted`): the pointwise envelope `regionI_pointwise`
  with `R = s/2`, and `W(Δ) ≤ W(P) e^{κ s}` give `16 M[g] e^{-10R}` for `R ≥ R₁(y)`.

`right_tail_weighted` combines them: for `y ≥ 0` the weighted mass of `g` on `Δ < P - R t` is at most
`M[g] (16 e^{-10 R} + η)` for `R ≥ R₁(y)` and all large `c`, uniformly in `g`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.SignUncertainty

/-! ### Elementary facts on the weight -/

lemma laplaceZeta_nonneg {c y : ℝ} (hc : 0 < c) (hy : 0 ≤ y) : 0 ≤ laplaceZeta c y :=
  mul_nonneg (div_nonneg hy laplaceCs_pos.le) (radialEps_pos hc).le

lemma tendsto_laplaceZeta (y : ℝ) : Tendsto (fun c : ℝ => laplaceZeta c y) atTop (𝓝 0) := by
  unfold laplaceZeta radialEps
  have := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).const_mul (y / laplaceCs)
  simpa using this

lemma laplaceZeta_mul_cbrt {c y : ℝ} (hc : 0 < c) :
    laplaceZeta c y * c ^ (1 / 3 : ℝ) = y / laplaceCs := by
  unfold laplaceZeta radialEps
  rw [mul_assoc, ← Real.rpow_add hc, neg_add_cancel, Real.rpow_zero, mul_one]

lemma laplaceWeight_anti {c y Δ Δ' : ℝ} (hc : 0 < c) (hy : 0 ≤ y) (hζ : laplaceZeta c y < 1)
    (hΔ : 0 < Δ) (hle : Δ ≤ Δ') : laplaceWeight c y Δ' ≤ laplaceWeight c y Δ := by
  have hΔ' : 0 < Δ' := lt_of_lt_of_le hΔ hle
  rw [laplaceWeight_scale hc hy hζ hΔ hΔ']
  have hW := laplaceWeight_pos hc hy hζ hΔ
  have h1 : (Δ / Δ') ^ (c * laplaceZeta c y) ≤ 1 :=
    Real.rpow_le_one (div_nonneg hΔ.le hΔ'.le) ((div_le_one hΔ').mpr hle)
      (mul_nonneg hc.le (laplaceZeta_nonneg hc hy))
  exact mul_le_of_le_one_right hW.le h1

lemma continuousOn_laplaceWeight {c y : ℝ} (hc : 0 < c) (hy : 0 ≤ y) (hζ : laplaceZeta c y < 1) :
    ContinuousOn (laplaceWeight c y) (Ioi 0) := by
  have h : ∀ Δ ∈ Ioi (0 : ℝ),
      laplaceWeight c y Δ = laplaceWeight c y 1 * (1 / Δ) ^ (c * laplaceZeta c y) :=
    fun Δ hΔ => laplaceWeight_scale hc hy hζ one_pos hΔ
  refine ContinuousOn.congr ?_ h
  refine continuousOn_const.mul (ContinuousOn.rpow_const
    (continuousOn_const.div continuousOn_id (fun Δ hΔ => hΔ.ne')) ?_)
  intro Δ hΔ
  left
  exact one_div_ne_zero hΔ.ne'

lemma pi_sq_bounds : 9.869 < Real.pi ^ 2 ∧ Real.pi ^ 2 < 9.87 := by
  constructor <;> nlinarith [Real.pi_gt_d4, Real.pi_lt_d4, Real.pi_pos]

lemma Delta1_pos {c : ℝ} (hc : 0 < c) : 0 < c * (1 / Real.pi ^ 2 - 1 / 48) := by
  have := pi_sq_bounds
  refine mul_pos hc ?_
  rw [sub_pos, div_lt_div_iff₀ (by norm_num) (by positivity)]
  nlinarith

lemma Delta1_ge {c : ℝ} (hc : 0 < c) : c / 13 ≤ c * (1 / Real.pi ^ 2 - 1 / 48) := by
  have h := pi_sq_bounds
  have h1 : (1 : ℝ) / 9.87 < 1 / Real.pi ^ 2 :=
    one_div_lt_one_div_of_lt (by positivity) h.2
  have h2 : (1 : ℝ) / 13 ≤ 1 / 9.87 - 1 / 48 := by norm_num
  have : (1 : ℝ) / 13 ≤ 1 / Real.pi ^ 2 - 1 / 48 := by linarith
  calc c / 13 = c * (1 / 13) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left this hc.le

lemma Delta1_lt_P {c : ℝ} (hc : 0 < c) : c * (1 / Real.pi ^ 2 - 1 / 48) < c / Real.pi ^ 2 := by
  have : c * (1 / Real.pi ^ 2 - 1 / 48) = c / Real.pi ^ 2 - c / 48 := by ring
  rw [this]; linarith [div_pos hc (by norm_num : (0 : ℝ) < 48)]

/-! ### The deep-lobe constant (the unweighted proof of `deepLobe_regionII`) -/

lemma regionII_B_bound {c M : ℝ} (hc : 56 ≤ c) (hM0 : 0 ≤ M) :
    (18 * M * Real.exp (1 / (6 * c)) * Real.exp (1 / (4 * c)) * Real.exp (c / 18) /
        Real.sqrt (c * (2 * (3 / 56 : ℝ) * (1 / 2))) *
          ((c / (2 * Real.pi)) * (Real.pi ^ 2 / c) ^ (c / 2))) *
      (c * (1 / Real.pi ^ 2 - 1 / 48)) ^ (c / 2) ≤ 4 * M * c * Real.exp (-(c / 25)) := by
  have hc0 : 0 < c := by linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpi2 : Real.pi ^ 2 < 48 := by nlinarith [Real.pi_lt_d2]
  set Δ₁ : ℝ := c * (1 / Real.pi ^ 2 - 1 / 48) with hΔ₁
  have hΔ₁pos : 0 < Δ₁ := Delta1_pos hc0
  set B : ℝ := 18 * M * Real.exp (1 / (6 * c)) * Real.exp (1 / (4 * c)) * Real.exp (c / 18) /
      Real.sqrt (c * (2 * (3 / 56 : ℝ) * (1 / 2))) * ((c / (2 * Real.pi)) * (Real.pi ^ 2 / c) ^ (c / 2))
    with hB
  have hΔ₁c : Real.pi ^ 2 / c * Δ₁ = 1 - Real.pi ^ 2 / 48 := by
    rw [hΔ₁]; field_simp
  have hpowx : (Real.pi ^ 2 / c) ^ (c / 2) * Δ₁ ^ (c / 2) = (1 - Real.pi ^ 2 / 48) ^ (c / 2) := by
    rw [← Real.mul_rpow (by positivity) hΔ₁pos.le, hΔ₁c]
  have hx0 : 0 < 1 - Real.pi ^ 2 / 48 := by linarith
  have hxexp : (1 - Real.pi ^ 2 / 48) ^ (c / 2) ≤ Real.exp (-(Real.pi ^ 2 * c / 96)) := by
    rw [Real.rpow_def_of_pos hx0]
    refine Real.exp_le_exp.mpr ?_
    have := Real.log_le_sub_one_of_pos hx0
    nlinarith [this]
  have hsq : 0 < Real.sqrt (c * (2 * (3 / 56 : ℝ) * (1 / 2))) := Real.sqrt_pos.mpr (by positivity)
  have hsq3 : Real.sqrt 3 ≤ Real.sqrt (c * (2 * (3 / 56 : ℝ) * (1 / 2))) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have hs3 : 1.732 < Real.sqrt 3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have e1 : Real.exp (1 / (6 * c)) ≤ 11 / 10 := exp_le_of_small (by positivity) (by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith)
  have e2 : Real.exp (1 / (4 * c)) ≤ 11 / 10 := exp_le_of_small (by positivity) (by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith)
  have e3 : Real.exp (c / 18) * Real.exp (-(Real.pi ^ 2 * c / 96)) ≤ Real.exp (-(c / 25)) := by
    rw [← Real.exp_add]; refine Real.exp_le_exp.mpr ?_
    nlinarith [deep_lobe_num3, mul_le_mul_of_nonneg_left deep_lobe_num3 hc0.le]
  have hmain : B * ((Δ₁ ^ (c / 2)) / (c / 2)) =
      18 * M * Real.exp (1 / (6 * c)) * Real.exp (1 / (4 * c)) * Real.exp (c / 18) /
        Real.sqrt (c * (2 * (3 / 56 : ℝ) * (1 / 2))) / Real.pi *
          ((Real.pi ^ 2 / c) ^ (c / 2) * Δ₁ ^ (c / 2)) := by
    rw [hB]; field_simp
  have hkey : B * ((Δ₁ ^ (c / 2)) / (c / 2)) ≤ 8 * M * Real.exp (-(c / 25)) := by
    rw [hmain, hpowx]
    have hpos1 : 0 ≤ 18 * M * Real.exp (1 / (6 * c)) * Real.exp (1 / (4 * c)) * Real.exp (c / 18) /
        Real.sqrt (c * (2 * (3 / 56 : ℝ) * (1 / 2))) / Real.pi := by positivity
    calc 18 * M * Real.exp (1 / (6 * c)) * Real.exp (1 / (4 * c)) * Real.exp (c / 18) /
          Real.sqrt (c * (2 * (3 / 56 : ℝ) * (1 / 2))) / Real.pi * (1 - Real.pi ^ 2 / 48) ^ (c / 2)
        ≤ 18 * M * Real.exp (1 / (6 * c)) * Real.exp (1 / (4 * c)) * Real.exp (c / 18) /
          Real.sqrt (c * (2 * (3 / 56 : ℝ) * (1 / 2))) / Real.pi *
            Real.exp (-(Real.pi ^ 2 * c / 96)) :=
          mul_le_mul_of_nonneg_left hxexp hpos1
      _ = (18 * M * Real.exp (1 / (6 * c)) * Real.exp (1 / (4 * c)) /
            Real.sqrt (c * (2 * (3 / 56 : ℝ) * (1 / 2))) / Real.pi) *
          (Real.exp (c / 18) * Real.exp (-(Real.pi ^ 2 * c / 96))) := by ring
      _ ≤ (8 * M) * Real.exp (-(c / 25)) := by
          have hcoef : 18 * M * Real.exp (1 / (6 * c)) * Real.exp (1 / (4 * c)) /
              Real.sqrt (c * (2 * (3 / 56 : ℝ) * (1 / 2))) / Real.pi ≤ 8 * M := by
            rw [div_div, div_le_iff₀ (by positivity)]
            have : Real.exp (1 / (6 * c)) * Real.exp (1 / (4 * c)) ≤ 11 / 10 * (11 / 10) :=
              mul_le_mul e1 e2 (Real.exp_pos _).le (by norm_num)
            have hden : 1.732 * 3.14 ≤ Real.sqrt (c * (2 * (3 / 56 : ℝ) * (1 / 2))) * Real.pi := by
              have := mul_le_mul (hs3.le.trans hsq3) Real.pi_gt_d2.le (by norm_num) hsq.le
              linarith
            have h18 : 18 * M * (Real.exp (1 / (6 * c)) * Real.exp (1 / (4 * c))) ≤
                18 * M * (11 / 10 * (11 / 10)) :=
              mul_le_mul_of_nonneg_left this (by positivity)
            nlinarith [mul_le_mul_of_nonneg_left hden hM0]
          exact mul_le_mul (by simpa [mul_assoc] using hcoef) e3 (by positivity) (by positivity)
      _ = 8 * M * Real.exp (-(c / 25)) := by ring
  have : B * Δ₁ ^ (c / 2) = (c / 2) * (B * ((Δ₁ ^ (c / 2)) / (c / 2))) := by
    field_simp
  rw [this]
  calc (c / 2) * (B * ((Δ₁ ^ (c / 2)) / (c / 2))) ≤ (c / 2) * (8 * M * Real.exp (-(c / 25))) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = 4 * M * c * Real.exp (-(c / 25)) := by ring

lemma continuousOn_weighted_abs {c y ε : ℝ} {g : ℝ → ℝ} (hc : 0 < c) (hy : 0 ≤ y)
    (hζ : laplaceZeta c y < 1) (hg : IsHankelEigenfn c ε g) :
    ContinuousOn (fun Δ => |g Δ| * hankelRho0 c Δ * laplaceWeight c y Δ) (Ioi 0) :=
  ((continuous_abs.comp_continuousOn (hg.cont.mono Ioi_subset_Ici_self)).mul
    (continuousOn_hankelRho0 c)).mul (continuousOn_laplaceWeight hc hy hζ)

/-! ### Region II -/

lemma regionII_weighted {c y ε : ℝ} {g : ℝ → ℝ} (hc : 56 ≤ c) (hy : 0 ≤ y)
    (hζ : laplaceZeta c y ≤ 1 / 4) (hg : IsHankelEigenfn c ε g) (hε : ε = 1 ∨ ε = -1) :
    IntegrableOn (fun Δ => |g Δ| * hankelRho0 c Δ * laplaceWeight c y Δ)
        (Ioc 0 (c * (1 / Real.pi ^ 2 - 1 / 48))) ∧
    ∫ Δ in Ioc 0 (c * (1 / Real.pi ^ 2 - 1 / 48)),
        |g Δ| * hankelRho0 c Δ * laplaceWeight c y Δ ≤
      16 * hankelMass c g * Real.exp (-(c / 25)) * laplaceWeight c y (c / Real.pi ^ 2) *
        ((c / Real.pi ^ 2) / (c * (1 / Real.pi ^ 2 - 1 / 48))) ^ (c * laplaceZeta c y) := by
  have hc0 : 0 < c := by linarith
  have hζ1 : laplaceZeta c y < 1 := by linarith
  have hcont := continuousOn_weighted_abs hc0 hy hζ1 hg
  set x : ℝ := c * laplaceZeta c y with hx
  have hx0 : 0 ≤ x := mul_nonneg hc0.le (laplaceZeta_nonneg hc0 hy)
  have hxc : x ≤ c / 4 := by rw [hx]; nlinarith
  set P : ℝ := c / Real.pi ^ 2 with hP
  have hP0 : 0 < P := by positivity
  set Δ₁ : ℝ := c * (1 / Real.pi ^ 2 - 1 / 48) with hΔ₁
  have hΔ₁pos : 0 < Δ₁ := Delta1_pos hc0
  set M := hankelMass c g with hM
  have hM0 : 0 ≤ M := hankelMass_nonneg hc0 g
  set B : ℝ := 18 * M * Real.exp (1 / (6 * c)) * Real.exp (1 / (4 * c)) * Real.exp (c / 18) /
      Real.sqrt (c * (2 * (3 / 56 : ℝ) * (1 / 2))) * ((c / (2 * Real.pi)) * (Real.pi ^ 2 / c) ^ (c / 2))
    with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  set a : ℝ := c / 2 - x with ha
  have ha4 : c / 4 ≤ a := by rw [ha]; linarith
  have ha0 : 0 < a := by linarith
  set WP : ℝ := laplaceWeight c y P with hWPdef
  have hWP : 0 < WP := laplaceWeight_pos hc0 hy hζ1 hP0
  set K : ℝ := B * WP * P ^ x with hK
  have hK0 : 0 ≤ K := by positivity
  have hpt : ∀ Δ ∈ Ioc (0 : ℝ) Δ₁,
      |g Δ| * hankelRho0 c Δ * laplaceWeight c y Δ ≤ K * Δ ^ (a - 1) := by
    intro Δ hΔ
    have hΔ0 : 0 < Δ := hΔ.1
    have h1 := regionII_pointwise hc hg hε hΔ0
    have hW : laplaceWeight c y Δ = WP * (P / Δ) ^ x := laplaceWeight_scale hc0 hy hζ1 hP0 hΔ0
    rw [hW]
    have hPD : (P / Δ) ^ x = P ^ x * Δ ^ (-x) := by
      rw [Real.div_rpow hP0.le hΔ0.le, Real.rpow_neg hΔ0.le, div_eq_mul_inv]
    have hΔa : Δ ^ (a - 1) = Δ ^ (c / 2 - 1) * Δ ^ (-x) := by
      rw [← Real.rpow_add hΔ0]; congr 1; rw [ha]; ring
    calc |g Δ| * hankelRho0 c Δ * (WP * (P / Δ) ^ x)
        ≤ (B * Δ ^ (c / 2 - 1)) * (WP * (P / Δ) ^ x) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = K * Δ ^ (a - 1) := by rw [hPD, hΔa, hK]; ring
  have hr : -1 < a - 1 := by linarith
  have hmaj : IntegrableOn (fun Δ : ℝ => K * Δ ^ (a - 1)) (Ioc 0 Δ₁) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hΔ₁pos.le).mp
      ((intervalIntegral.intervalIntegrable_rpow' hr).const_mul K)
  have hint : IntegrableOn (fun Δ => |g Δ| * hankelRho0 c Δ * laplaceWeight c y Δ) (Ioc 0 Δ₁) := by
    refine Integrable.mono' hmaj ((hcont.mono Ioc_subset_Ioi_self).aestronglyMeasurable
      measurableSet_Ioc) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioc fun Δ hΔ => ?_
    have hn : 0 ≤ |g Δ| * hankelRho0 c Δ * laplaceWeight c y Δ :=
      mul_nonneg (mul_nonneg (abs_nonneg _) (hankelRho0_nonneg hc0 hΔ.1.le))
        (laplaceWeight_pos hc0 hy hζ1 hΔ.1).le
    rw [Real.norm_eq_abs, abs_of_nonneg hn]
    exact hpt Δ hΔ
  refine ⟨hint, ?_⟩
  have hmono := setIntegral_mono_on hint hmaj measurableSet_Ioc hpt
  refine hmono.trans ?_
  rw [← intervalIntegral.integral_of_le hΔ₁pos.le, intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl hr)]
  rw [show a - 1 + 1 = a by ring, Real.zero_rpow ha0.ne', sub_zero]
  have hΔa : Δ₁ ^ a = Δ₁ ^ (c / 2) * Δ₁ ^ (-x) := by
    rw [← Real.rpow_add hΔ₁pos]; congr 1
  have hPD : (P / Δ₁) ^ x = P ^ x * Δ₁ ^ (-x) := by
    rw [Real.div_rpow hP0.le hΔ₁pos.le, Real.rpow_neg hΔ₁pos.le, div_eq_mul_inv]
  have hBb := regionII_B_bound hc hM0
  rw [← hB] at hBb
  have hrp : 0 ≤ WP * (P / Δ₁) ^ x := by positivity
  calc K * (Δ₁ ^ a / a) = (B * Δ₁ ^ (c / 2)) * (WP * (P / Δ₁) ^ x) / a := by
        rw [hK, hΔa, hPD]; ring
    _ ≤ (4 * M * c * Real.exp (-(c / 25))) * (WP * (P / Δ₁) ^ x) / (c / 4) := by
        gcongr
    _ = 16 * M * Real.exp (-(c / 25)) * WP * (P / Δ₁) ^ x := by
        field_simp; ring

/-! ### Region I -/

/-- `κ_y = 13 y / c_s`. -/
noncomputable def kappaY (y : ℝ) : ℝ := 13 * y / laplaceCs

/-- The threshold from which region I is controlled. -/
noncomputable def regionIThreshold (y : ℝ) : ℝ := max 2 (2 * (2 * kappaY y / 5) ^ 2)

lemma kappaY_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ kappaY y :=
  div_nonneg (by linarith) laplaceCs_pos.le

lemma five_half_pow_ge {κ s : ℝ} (hs : 2 * (2 * κ / 5) ^ 2 ≤ s) :
    κ * s ≤ 5 * (s / 2) ^ ((3 : ℝ) / 2) := by
  have hs0 : 0 ≤ s := le_trans (by positivity) hs
  have h2 : 0 ≤ s / 2 := by positivity
  have hpow : (s / 2) ^ ((3 : ℝ) / 2) = (s / 2) * Real.sqrt (s / 2) := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add' h2 (by norm_num), Real.rpow_one,
      ← Real.sqrt_eq_rpow]
  have hsq : 2 * κ / 5 ≤ Real.sqrt (s / 2) := by
    refine Real.le_sqrt_of_sq_le ?_
    linarith
  rw [hpow]
  nlinarith [mul_le_mul_of_nonneg_left hsq h2]

lemma weight_ratio_le {c y Δ : ℝ} (hc : 0 < c) (hy : 0 ≤ y) (hΔ : c / 13 ≤ Δ)
    (hΔP : Δ < c / Real.pi ^ 2) :
    (c / Real.pi ^ 2 / Δ) ^ (c * laplaceZeta c y) ≤
      Real.exp (kappaY y * ((c / Real.pi ^ 2 - Δ) / c ^ (1 / 3 : ℝ))) := by
  have hΔ0 : 0 < Δ := lt_of_lt_of_le (by positivity) hΔ
  set P : ℝ := c / Real.pi ^ 2 with hP
  set t : ℝ := c ^ (1 / 3 : ℝ) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hc _
  have hx0 : 0 ≤ c * laplaceZeta c y := mul_nonneg hc.le (laplaceZeta_nonneg hc hy)
  have h1 : P / Δ ≤ Real.exp ((P - Δ) / Δ) := by
    have := Real.add_one_le_exp ((P - Δ) / Δ)
    have e : P / Δ = (P - Δ) / Δ + 1 := by field_simp; ring
    linarith
  have h2 : (P / Δ) ^ (c * laplaceZeta c y) ≤ (Real.exp ((P - Δ) / Δ)) ^ (c * laplaceZeta c y) :=
    Real.rpow_le_rpow (by positivity) h1 hx0
  refine h2.trans ?_
  rw [← Real.exp_mul]
  refine Real.exp_le_exp.mpr ?_
  have hPΔ : 0 < P - Δ := by linarith
  have h3 : (P - Δ) / Δ ≤ (P - Δ) / (c / 13) :=
    div_le_div_of_nonneg_left hPΔ.le (by positivity) hΔ
  have hz : laplaceZeta c y * t = y / laplaceCs := laplaceZeta_mul_cbrt hc
  calc (P - Δ) / Δ * (c * laplaceZeta c y) ≤ (P - Δ) / (c / 13) * (c * laplaceZeta c y) :=
        mul_le_mul_of_nonneg_right h3 hx0
    _ = 13 * ((P - Δ) / t) * (laplaceZeta c y * t) := by field_simp
    _ = kappaY y * ((P - Δ) / t) := by rw [hz, kappaY]; ring

lemma regionI_weighted {c y ε : ℝ} {g : ℝ → ℝ} (hc : 56 ≤ c) (hy : 0 ≤ y)
    (hζ : laplaceZeta c y ≤ 1 / 4) (hWP : laplaceWeight c y (c / Real.pi ^ 2) ≤ 2)
    (hg : IsHankelEigenfn c ε g) (hε : ε = 1 ∨ ε = -1) {R : ℝ} (hR : regionIThreshold y ≤ R) :
    IntegrableOn (fun Δ => |g Δ| * hankelRho0 c Δ * laplaceWeight c y Δ)
        (Ioo (c * (1 / Real.pi ^ 2 - 1 / 48)) (c / Real.pi ^ 2 - R * c ^ (1 / 3 : ℝ))) ∧
    ∫ Δ in Ioo (c * (1 / Real.pi ^ 2 - 1 / 48)) (c / Real.pi ^ 2 - R * c ^ (1 / 3 : ℝ)),
        |g Δ| * hankelRho0 c Δ * laplaceWeight c y Δ ≤ 16 * hankelMass c g * Real.exp (-(10 * R)) := by
  have hc0 : 0 < c := by linarith
  have hζ1 : laplaceZeta c y < 1 := by linarith
  have hcont := continuousOn_weighted_abs hc0 hy hζ1 hg
  have hR2 : 2 ≤ R := le_trans (le_max_left _ _) hR
  have hRκ : 2 * (2 * kappaY y / 5) ^ 2 ≤ R := le_trans (le_max_right _ _) hR
  set t : ℝ := c ^ (1 / 3 : ℝ) with htdef
  have ht0 : 0 < t := Real.rpow_pos_of_pos hc0 _
  have htc : t ^ 3 = c := by
    rw [htdef, ← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
  set P : ℝ := c / Real.pi ^ 2 with hP
  have hP0 : 0 < P := by positivity
  set Δ₁ : ℝ := c * (1 / Real.pi ^ 2 - 1 / 48) with hΔ₁
  have hΔ₁pos : 0 < Δ₁ := Delta1_pos hc0
  have hΔ₁ge : c / 13 ≤ Δ₁ := Delta1_ge hc0
  set U : ℝ := P - R * t with hU
  set M := hankelMass c g with hM
  have hM0 : 0 ≤ M := hankelMass_nonneg hc0 g
  set WP : ℝ := laplaceWeight c y P with hWPdef
  have hWP0 : 0 < WP := laplaceWeight_pos hc0 hy hζ1 hP0
  set K : ℝ := 160 * M / t with hKdef
  have hK0 : 0 ≤ K := by positivity
  have hpt : ∀ Δ ∈ Ioo Δ₁ U, |g Δ| * hankelRho0 c Δ * laplaceWeight c y Δ ≤
      K * Real.exp (-(10 * (P - Δ) / t)) := by
    intro Δ hΔ
    have hΔ0 : 0 < Δ := lt_trans hΔ₁pos hΔ.1
    set s : ℝ := (P - Δ) / t with hs
    have hPΔ : P - Δ = s * t := by rw [hs]; field_simp
    have hsR : R < s := by
      rw [hs, lt_div_iff₀ ht0]; have := hΔ.2; rw [hU] at this; linarith
    have hs2 : 2 ≤ s := by linarith
    have h1 := regionI_pointwise hc hg hε (t := t) (R := s / 2) (Δ := Δ) ht0 htc (by linarith)
      hΔ.1 (by rw [← hP]; nlinarith)
    have hW : laplaceWeight c y Δ = WP * (P / Δ) ^ (c * laplaceZeta c y) :=
      laplaceWeight_scale hc0 hy hζ1 hP0 hΔ0
    have hratio := weight_ratio_le hc0 hy (le_trans hΔ₁ge hΔ.1.le)
      (by have := hΔ.2; rw [hU] at this; nlinarith)
    rw [← hP, ← htdef, ← hs] at hratio
    have hκs := five_half_pow_ge (le_trans hRκ hsR.le)
    have hexp1 : Real.exp (-(5 * (s / 2) ^ ((3 : ℝ) / 2))) * Real.exp (kappaY y * s) ≤ 1 := by
      rw [← Real.exp_add]; apply Real.exp_le_one_iff.mpr; linarith
    have hwb : laplaceWeight c y Δ ≤ 2 * Real.exp (kappaY y * s) := by
      rw [hW]
      exact mul_le_mul hWP hratio (by positivity) (by norm_num)
    have hstep1 : |g Δ| * hankelRho0 c Δ * laplaceWeight c y Δ ≤
        ((80 * M / t) * Real.exp (-(5 * (s / 2) ^ ((3 : ℝ) / 2))) *
          Real.exp (-(10 * (P - Δ) / t))) * (2 * Real.exp (kappaY y * s)) := by
      rw [← hP] at h1
      exact mul_le_mul h1 hwb (laplaceWeight_pos hc0 hy hζ1 hΔ0).le (by positivity)
    have hstep2 : ((80 * M / t) * Real.exp (-(5 * (s / 2) ^ ((3 : ℝ) / 2))) *
          Real.exp (-(10 * (P - Δ) / t))) * (2 * Real.exp (kappaY y * s)) =
        K * Real.exp (-(10 * (P - Δ) / t)) *
          (Real.exp (-(5 * (s / 2) ^ ((3 : ℝ) / 2))) * Real.exp (kappaY y * s)) := by
      rw [hKdef]; ring
    have hK2 : 0 ≤ K * Real.exp (-(10 * (P - Δ) / t)) := by positivity
    have hstep3 := mul_le_mul_of_nonneg_left hexp1 hK2
    rw [mul_one] at hstep3
    linarith [hstep1, hstep2, hstep3]
  by_cases hlt : Δ₁ < U
  · have hGc : Continuous fun Δ : ℝ => K * Real.exp (-(10 * (P - Δ) / t)) := by fun_prop
    have hmaj : IntegrableOn (fun Δ : ℝ => K * Real.exp (-(10 * (P - Δ) / t))) (Ioo Δ₁ U) :=
      hGc.integrableOn_Icc.mono_set Ioo_subset_Icc_self
    have hint : IntegrableOn (fun Δ => |g Δ| * hankelRho0 c Δ * laplaceWeight c y Δ) (Ioo Δ₁ U) := by
      refine Integrable.mono' hmaj ((hcont.mono fun Δ hΔ => lt_trans hΔ₁pos hΔ.1).aestronglyMeasurable
        measurableSet_Ioo) ?_
      refine ae_restrict_of_forall_mem measurableSet_Ioo fun Δ hΔ => ?_
      have hΔ0 : 0 < Δ := lt_trans hΔ₁pos hΔ.1
      have hn : 0 ≤ |g Δ| * hankelRho0 c Δ * laplaceWeight c y Δ :=
        mul_nonneg (mul_nonneg (abs_nonneg _) (hankelRho0_nonneg hc0 hΔ0.le))
          (laplaceWeight_pos hc0 hy hζ1 hΔ0).le
      rw [Real.norm_eq_abs, abs_of_nonneg hn]
      exact hpt Δ hΔ
    refine ⟨hint, ?_⟩
    have hmono := setIntegral_mono_on hint hmaj measurableSet_Ioo hpt
    refine hmono.trans ?_
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hlt.le,
      intervalIntegral.integral_const_mul]
    have hd : ∀ Δ : ℝ, HasDerivAt (fun Δ => (t / 10) * Real.exp (-(10 * (P - Δ) / t)))
        (Real.exp (-(10 * (P - Δ) / t))) Δ := by
      intro Δ
      have h1 : HasDerivAt (fun Δ : ℝ => -(10 * (P - Δ) / t)) (10 / t) Δ := by
        have := (((hasDerivAt_id Δ).const_sub P).const_mul 10).div_const t |>.neg
        exact this.congr_deriv (by ring)
      have := (h1.exp).const_mul (t / 10)
      convert this using 1
      field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun Δ _ => hd Δ)
      ((Real.continuous_exp.comp (by fun_prop)).intervalIntegrable _ _)]
    have hPU : P - U = R * t := by rw [hU]; ring
    have h10 : Real.exp (-(10 * (P - U) / t)) = Real.exp (-(10 * R)) := by
      congr 1; rw [hPU]; field_simp
    have : (t / 10) * Real.exp (-(10 * (P - U) / t)) - (t / 10) * Real.exp (-(10 * (P - Δ₁) / t)) ≤
        (t / 10) * Real.exp (-(10 * R)) := by
      rw [h10]
      nlinarith [Real.exp_pos (-(10 * (P - Δ₁) / t)), ht0]
    calc K * ((t / 10) * Real.exp (-(10 * (P - U) / t)) - (t / 10) * Real.exp (-(10 * (P - Δ₁) / t)))
        ≤ K * ((t / 10) * Real.exp (-(10 * R))) := mul_le_mul_of_nonneg_left this hK0
      _ = 16 * M * Real.exp (-(10 * R)) := by rw [hKdef]; field_simp; ring
  · rw [Ioo_eq_empty hlt, Measure.restrict_empty, integral_zero_measure]
    refine ⟨integrableOn_empty, by positivity⟩

/-! ### The right tail -/

lemma exp_decay_cbrt {a : ℝ} :
    Tendsto (fun c : ℝ => Real.exp (-(c / 25) + a * (c ^ (1 / 3 : ℝ)) ^ 2)) atTop (𝓝 0) := by
  have hexp : Tendsto (fun c : ℝ => Real.exp (-(c / 50))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
      (tendsto_id.atTop_div_const (by norm_num)))
  have hcb : ∀ᶠ c : ℝ in atTop, 50 * (a + 1) ≤ c ^ (1 / 3 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).eventually_ge_atTop _
  refine squeeze_zero' (Eventually.of_forall fun c => (Real.exp_pos _).le) ?_ hexp
  filter_upwards [hcb, eventually_gt_atTop 0] with c hc hc0
  refine Real.exp_le_exp.mpr ?_
  set t : ℝ := c ^ (1 / 3 : ℝ) with ht
  have ht3 : t ^ 3 = c := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
  have ht0 : 0 ≤ t := Real.rpow_nonneg hc0.le _
  have : a * t ^ 2 ≤ c / 50 := by
    rw [← ht3]
    nlinarith [mul_nonneg ht0 (sq_nonneg t), mul_le_mul_of_nonneg_right hc (sq_nonneg t)]
  linarith

theorem right_tail_weighted {y : ℝ} (hy : 0 ≤ y) {η : ℝ} (hη : 0 < η) :
    ∃ c₁ : ℝ, ∀ c : ℝ, c₁ ≤ c → ∀ (ε : ℝ) (g : ℝ → ℝ) (R : ℝ), (ε = 1 ∨ ε = -1) →
      IsHankelEigenfn c ε g → regionIThreshold y ≤ R →
      IntegrableOn (fun Δ => |g Δ| * hankelRho0 c Δ * laplaceWeight c y Δ)
          (Ioo 0 (c / Real.pi ^ 2 - R * c ^ (1 / 3 : ℝ))) ∧
      ∫ Δ in Ioo 0 (c / Real.pi ^ 2 - R * c ^ (1 / 3 : ℝ)),
          |g Δ| * hankelRho0 c Δ * laplaceWeight c y Δ ≤
        hankelMass c g * (16 * Real.exp (-(10 * R)) + η) := by
  have hκ0 := kappaY_nonneg hy
  have e1 : ∀ᶠ c : ℝ in atTop, 56 ≤ c := eventually_ge_atTop _
  have e2 : ∀ᶠ c : ℝ in atTop, laplaceZeta c y ≤ 1 / 4 :=
    (tendsto_laplaceZeta y).eventually (Iic_mem_nhds (by norm_num))
  have e3 : ∀ᶠ c : ℝ in atTop, laplaceWeight c y (c / Real.pi ^ 2) ≤ 2 := by
    have h := laplaceWeight_tendsto_const y 0
    simp only [zero_div, zero_mul, sub_zero, mul_zero, add_zero] at h
    have hlt : Real.exp (-(y ^ 3) / 12) < 2 := by
      have h1 : Real.exp (-(y ^ 3) / 12) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : 0 ≤ y ^ 3 := by positivity
        linarith
      linarith
    exact (h.eventually (gt_mem_nhds hlt)).mono fun c hc => hc.le
  have e4 : ∀ᶠ c : ℝ in atTop,
      32 * Real.exp (-(c / 25) + (kappaY y / 48) * (c ^ (1 / 3 : ℝ)) ^ 2) ≤ η := by
    have h := (exp_decay_cbrt (a := kappaY y / 48)).const_mul 32
    rw [mul_zero] at h
    exact h.eventually (Iic_mem_nhds hη)
  obtain ⟨c₁, hc₁⟩ := eventually_atTop.mp (e1.and (e2.and (e3.and e4)))
  refine ⟨c₁, fun c hc ε g R hε hg hR => ?_⟩
  obtain ⟨h56, hζ, hWP, hη'⟩ := hc₁ c hc
  have hc0 : 0 < c := by linarith
  have hζ1 : laplaceZeta c y < 1 := by linarith
  set P : ℝ := c / Real.pi ^ 2 with hP
  set t : ℝ := c ^ (1 / 3 : ℝ) with htdef
  have ht0 : 0 < t := Real.rpow_pos_of_pos hc0 _
  have htc : t ^ 3 = c := by
    rw [htdef, ← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
  set Δ₁ : ℝ := c * (1 / Real.pi ^ 2 - 1 / 48) with hΔ₁
  have hΔ₁pos : 0 < Δ₁ := Delta1_pos hc0
  set U : ℝ := P - R * t with hU
  set M := hankelMass c g with hM
  have hM0 : 0 ≤ M := hankelMass_nonneg hc0 g
  obtain ⟨hIIi, hII⟩ := regionII_weighted h56 hy hζ hg hε
  obtain ⟨hIi, hI⟩ := regionI_weighted h56 hy hζ hWP hg hε hR
  -- bound region II by `M η`
  have hP0 : 0 < P := by positivity
  have hWPpos : 0 < laplaceWeight c y P := laplaceWeight_pos hc0 hy hζ1 hP0
  have hratio := weight_ratio_le hc0 hy (Delta1_ge hc0) (Delta1_lt_P hc0)
  rw [← hP, ← htdef, ← hΔ₁] at hratio
  have hPΔ : P - Δ₁ = c / 48 := by rw [hP, hΔ₁]; ring
  have hq : (P - Δ₁) / t = t ^ 2 / 48 := by
    rw [hPΔ, ← htc]; field_simp
  rw [hq] at hratio
  have hIIb : ∫ Δ in Ioc 0 Δ₁, |g Δ| * hankelRho0 c Δ * laplaceWeight c y Δ ≤ M * η := by
    calc _ ≤ 16 * M * Real.exp (-(c / 25)) * laplaceWeight c y P *
          (P / Δ₁) ^ (c * laplaceZeta c y) := hII
      _ ≤ 16 * M * Real.exp (-(c / 25)) * 2 * Real.exp (kappaY y * (t ^ 2 / 48)) := by
          gcongr
      _ = M * (32 * Real.exp (-(c / 25) + (kappaY y / 48) * t ^ 2)) := by
          rw [Real.exp_add, show kappaY y * (t ^ 2 / 48) = kappaY y / 48 * t ^ 2 by ring]; ring
      _ ≤ M * η := mul_le_mul_of_nonneg_left hη' hM0
  have hsub : Ioo 0 U ⊆ Ioc 0 Δ₁ ∪ Ioo Δ₁ U := by
    intro x hx
    by_cases h : x ≤ Δ₁
    · exact Or.inl ⟨hx.1, h⟩
    · exact Or.inr ⟨not_le.mp h, hx.2⟩
  have hU' : U = c / Real.pi ^ 2 - R * c ^ (1 / 3 : ℝ) := rfl
  have hunion : IntegrableOn (fun Δ => |g Δ| * hankelRho0 c Δ * laplaceWeight c y Δ)
      (Ioc 0 Δ₁ ∪ Ioo Δ₁ U) := hIIi.union hIi
  refine ⟨hunion.mono_set hsub, ?_⟩
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc 0 Δ₁ ∪ Ioo Δ₁ U)]
      fun Δ => |g Δ| * hankelRho0 c Δ * laplaceWeight c y Δ := by
    refine (ae_restrict_iff' (measurableSet_Ioc.union measurableSet_Ioo)).mpr
      (ae_of_all _ fun Δ hΔ => ?_)
    have hΔ0 : 0 < Δ := by
      rcases hΔ with hΔ | hΔ
      · exact hΔ.1
      · exact lt_trans hΔ₁pos hΔ.1
    exact mul_nonneg (mul_nonneg (abs_nonneg _) (hankelRho0_nonneg hc0 hΔ0.le))
      (laplaceWeight_pos hc0 hy hζ1 hΔ0).le
  calc ∫ Δ in Ioo 0 U, |g Δ| * hankelRho0 c Δ * laplaceWeight c y Δ
      ≤ ∫ Δ in Ioc 0 Δ₁ ∪ Ioo Δ₁ U, |g Δ| * hankelRho0 c Δ * laplaceWeight c y Δ :=
        setIntegral_mono_set hunion hnn hsub.eventuallyLE
    _ = (∫ Δ in Ioc 0 Δ₁, |g Δ| * hankelRho0 c Δ * laplaceWeight c y Δ) +
          ∫ Δ in Ioo Δ₁ U, |g Δ| * hankelRho0 c Δ * laplaceWeight c y Δ := by
        refine setIntegral_union ?_ measurableSet_Ioo hIIi hIi
        rw [Set.disjoint_left]
        intro x hx hx'
        exact absurd hx.2 (not_le.2 hx'.1)
    _ ≤ M * η + 16 * M * Real.exp (-(10 * R)) := add_le_add hIIb hI
    _ = M * (16 * Real.exp (-(10 * R)) + η) := by ring

/-- info: 'FormalResearch.SignUncertainty.regionII_weighted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms regionII_weighted

/-- info: 'FormalResearch.SignUncertainty.regionI_weighted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms regionI_weighted

/-- info: 'FormalResearch.SignUncertainty.right_tail_weighted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms right_tail_weighted

end FormalResearch.SignUncertainty
