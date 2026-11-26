module

public import FormalResearch.SignUncertainty.FctCompDTargets
public import FormalResearch.SignUncertainty.FctCompDStrip
public import FormalResearch.SignUncertainty.FctMomentSolver

/-!
# `fct:comp-D` Part (1): localized strip outer compensator construction and bounds (F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma FCT.3 (`fct:comp-D`), Part (1)
(lines 167–206, 231–235).

Constructs the localized compensator density `v = v₀ + v₁ + v_α` with `K₄`-linear splitting
`v₀ = v₀^base + K₄ v₀^marg` and `v₁ = v₁^base + K₄ v₁^marg` via `momentSolver 5 τ₁`, and proves:
* zeroed moments `ℳ_j = 0` (`j = 0..4`) and vanishing odd phase derivatives `ϑ^{(2k+1)}(0) = 0`;
* exact inner form `(fct:v-inner)` on `[-2τ₁, 2τ₁]`;
* all-order derivative bounds `(fct:v-derivs)`–`(fct:v1-derivs)`;
* inner phase bounds `(fct:th-inner)`–`(fct:th1-inner)` on `|t| ≤ 12τ₁`;
* tail phase bounds `(fct:th-tail)` on `|t| ≥ 12τ₁`;
* interior strip bounds `(fct:gD-int)` on `Re ζ ∈ [1/8, 7/8]`;
* **all-order global closed-strip bounds** `‖g_D^{(r)}(ζ)‖ ≤ C_r(K₄) τ₁^{2-r}` on `S̄` for every
  `r ≥ 0`, explicitly including `r = 0` (`g_D`), `r = 1` (`g_D'`), and `r = 2` (`g_D''`),
  repairing the paper's omission of `g_D''` in `fct:comp-D` (1) (used in `fct:ce-band`);
* `D(0) = D(1) = 1` (`stripCompGExt v 0 = stripCompGExt v 1 = 0`).

Class: proved, no hypotheses.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real BigOperators

namespace FormalResearch.SignUncertainty.FctCompD

open FormalResearch.SignUncertainty
open FormalResearch.SignUncertainty.FctMoment
open FormalResearch.CohnElkies

/-! ### Component definitions (`v₀`, `v₁`, `v_α`, `v`) -/

/-- Base leading compensator density `v₀^base = momentSolver 5 τ₁ (-log r₀)` (independent of `K₄`). -/
noncomputable def v0Base (kind : StripKernelChoice) (τ₁ : ℝ) : ℝ → ℝ :=
  momentSolver 5 τ₁ (f0Base kind)

/-- Marginal leading compensator density `v₀^marg = momentSolver 5 τ₁ (-t⁴)` (independent of `K₄`). -/
noncomputable def v0Marg (τ₁ : ℝ) : ℝ → ℝ :=
  momentSolver 5 τ₁ (fun t => -(t ^ 4))

/-- Combined leading compensator density `v₀ = v₀^base + K₄ v₀^marg`. -/
noncomputable def v0 (kind : StripKernelChoice) (K4 τ₁ : ℝ) (t : ℝ) : ℝ :=
  v0Base kind τ₁ t + K4 * v0Marg τ₁ t

/-- Perturbation compensator density `v_α = momentSolver 5 τ₁ (α t²)`. -/
noncomputable def vAlpha (α τ₁ : ℝ) : ℝ → ℝ :=
  momentSolver 5 τ₁ (fun t => α * t ^ 2)

/-- Base curvature compensator density `v₁^base = momentSolver 5 τ₁ (-Δ_curv[ϑ_{D₀^base}])` (independent of `K₄`). -/
noncomputable def v1Base (kind : StripKernelChoice) (c τ₁ : ℝ) : ℝ → ℝ :=
  momentSolver 5 τ₁ (fun t => -deltaCurvSmooth c (fctThetaD (v0Base kind τ₁)) t)

/-- Marginal curvature compensator density `v₁^marg = momentSolver 5 τ₁ (-Δ_curv[ϑ_{D₀^marg}])` (independent of `K₄`). -/
noncomputable def v1Marg (c τ₁ : ℝ) : ℝ → ℝ :=
  momentSolver 5 τ₁ (fun t => -deltaCurvSmooth c (fctThetaD (v0Marg τ₁)) t)

/-- Combined curvature compensator density `v₁ = v₁^base + K₄ v₁^marg`. -/
noncomputable def v1 (kind : StripKernelChoice) (K4 c τ₁ : ℝ) (t : ℝ) : ℝ :=
  v1Base kind c τ₁ t + K4 * v1Marg c τ₁ t

/-- Total localized strip compensator density `v = v₀ + v₁ + v_α`. -/
noncomputable def vTotal (kind : StripKernelChoice) (K4 c α τ₁ : ℝ) (t : ℝ) : ℝ :=
  v0 kind K4 τ₁ t + v1 kind K4 c τ₁ t + vAlpha α τ₁ t

/-! ### Elementary target bounds for `-t⁴` and `α t²` -/

lemma deriv_bounds_neg_pow4 :
    ∃ C_f : ℕ → ℝ, (∀ r, 0 ≤ C_f r) ∧
      ∀ {τ₁ : ℝ}, 0 < τ₁ → τ₁ ≤ 1 / 16 →
        ∀ r t, |t| ≤ 3 * τ₁ →
          |iteratedDeriv r (fun s : ℝ => -(s ^ 4)) t| ≤ C_f r * (τ₁ ^ 2) * τ₁ ^ ((2 : ℤ) - r) := by
  let Cf : ℕ → ℝ := fun r => match r with | 0 => 81 | 1 => 108 | 2 => 108 | 3 => 72 | 4 => 24 | _ => 0
  refine ⟨Cf, fun r => by rcases r with _ | _ | _ | _ | _ | r <;> norm_num [Cf],
    fun {τ₁} hτ₁ _ r t ht => ?_⟩
  have h1 : |t| ≤ 3 * τ₁ := ht
  have hrew : (fun s : ℝ => -(s ^ 4)) = -fun s : ℝ => s ^ 4 := rfl
  rw [hrew, iteratedDeriv_neg, abs_neg]
  have hd1_fn : iteratedDeriv 1 (fun s : ℝ => s ^ 4) = fun s => 4 * s ^ 3 := by
    ext s; rw [iteratedDeriv_one]; exact (hasDerivAt_pow 4 s).deriv
  have hd2_fn : iteratedDeriv 2 (fun s : ℝ => s ^ 4) = fun s => 12 * s ^ 2 := by
    ext s; rw [iteratedDeriv_succ, hd1_fn]
    have h := ((hasDerivAt_pow 3 s).const_mul 4).deriv
    convert h using 1; ring
  have hd3_fn : iteratedDeriv 3 (fun s : ℝ => s ^ 4) = fun s => 24 * s := by
    ext s; rw [iteratedDeriv_succ, hd2_fn]
    have h := ((hasDerivAt_pow 2 s).const_mul 12).deriv
    convert h using 1; ring
  have hd4_fn : iteratedDeriv 4 (fun s : ℝ => s ^ 4) = fun _ => (24 : ℝ) := by
    ext s; rw [iteratedDeriv_succ, hd3_fn]
    simpa only [id_eq, mul_one] using ((hasDerivAt_id s).const_mul 24).deriv
  rcases r with _ | _ | _ | _ | _ | k
  · simp only [Cf, iteratedDeriv_zero, Nat.cast_zero, sub_zero, zpow_two, abs_pow]
    have h4 : |t| ^ 4 ≤ (3 * τ₁) ^ 4 := pow_le_pow_left₀ (abs_nonneg _) h1 4
    linarith [show (3 * τ₁) ^ 4 = 81 * τ₁ ^ 2 * τ₁ ^ 2 by ring]
  · rw [hd1_fn, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_pow]
    have h3 : |t| ^ 3 ≤ (3 * τ₁) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) h1 3
    have hcf : Cf 1 = 108 := rfl
    have hexp : τ₁ ^ ((2 : ℤ) - ((1 : ℕ) : ℤ)) = τ₁ := by norm_num
    rw [hcf, hexp]; linarith [show 4 * (3 * τ₁) ^ 3 = 108 * τ₁ ^ 2 * τ₁ by ring]
  · rw [hd2_fn, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 12), abs_pow]
    have h2 : |t| ^ 2 ≤ (3 * τ₁) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    have hcf : Cf 2 = 108 := rfl
    have hexp : τ₁ ^ ((2 : ℤ) - ((2 : ℕ) : ℤ)) = 1 := by norm_num
    rw [hcf, hexp]; linarith [show 12 * (3 * τ₁) ^ 2 = 108 * τ₁ ^ 2 * 1 by ring]
  · rw [hd3_fn, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 24)]
    have hcf : Cf 3 = 72 := rfl
    have hexp : τ₁ ^ 2 * τ₁ ^ ((2 : ℤ) - ((3 : ℕ) : ℤ)) = τ₁ := by
      rw [show (2 : ℤ) - ((3 : ℕ) : ℤ) = -1 by norm_num, zpow_neg_one]; field_simp [hτ₁.ne']
    rw [hcf, mul_assoc, hexp]; linarith
  · rw [hd4_fn, abs_of_pos (by norm_num : (0 : ℝ) < 24)]
    have hcf : Cf 4 = 24 := rfl
    have hexp : τ₁ ^ 2 * τ₁ ^ ((2 : ℤ) - ((4 : ℕ) : ℤ)) = 1 := by
      rw [show (2 : ℤ) - ((4 : ℕ) : ℤ) = -2 by norm_num, zpow_neg, zpow_two]; field_simp [hτ₁.ne']
    rw [hcf, mul_assoc, hexp, mul_one]
  · have hd5 : iteratedDeriv 5 (fun s : ℝ => s ^ 4) = 0 := by
      ext s; rw [iteratedDeriv_succ, hd4_fn]; simp [deriv_const]
    have hdk : iteratedDeriv (k + 5) (fun s : ℝ => s ^ 4) t = 0 := by
      rw [← iteratedDeriv_iteratedDeriv_eq, hd5, iteratedDeriv_const_zero]
    have hcf : Cf (k + 5) = 0 := rfl
    rw [hcf, hdk, abs_zero, zero_mul, zero_mul]

lemma deriv_bounds_alpha_pow2 :
    ∃ C_f : ℕ → ℝ, (∀ r, 0 ≤ C_f r) ∧
      ∀ {α τ₁ : ℝ}, 0 < τ₁ → τ₁ ≤ 1 / 16 →
        ∀ r t, |t| ≤ 3 * τ₁ →
          |iteratedDeriv r (fun s : ℝ => α * s ^ 2) t| ≤ C_f r * |α| * τ₁ ^ ((2 : ℤ) - r) := by
  let Cf : ℕ → ℝ := fun r => match r with | 0 => 9 | 1 => 6 | 2 => 2 | _ => 0
  refine ⟨Cf, fun r => by rcases r with _ | _ | _ | r <;> norm_num [Cf],
    fun {α τ₁} hτ₁ _ r t ht => ?_⟩
  rw [iteratedDeriv_const_mul_field, abs_mul]
  have hd1_fn : iteratedDeriv 1 (fun s : ℝ => s ^ 2) = fun s => 2 * s := by
    ext s; rw [iteratedDeriv_one]; simp [(hasDerivAt_pow 2 s).deriv]
  have hd2_fn : iteratedDeriv 2 (fun s : ℝ => s ^ 2) = fun _ => (2 : ℝ) := by
    ext s; rw [iteratedDeriv_succ, hd1_fn]
    simpa only [id_eq, mul_one] using ((hasDerivAt_id s).const_mul 2).deriv
  rcases r with _ | _ | _ | k
  · simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero, zpow_two, abs_pow]
    have hcf : Cf 0 = 9 := rfl
    rw [hcf]
    have h2 : |t| ^ 2 ≤ (3 * τ₁) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) ht 2
    calc |α| * |t| ^ 2 ≤ |α| * (3 * τ₁) ^ 2 := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
      _ = 9 * |α| * (τ₁ * τ₁) := by ring
  · rw [hd1_fn, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hcf : Cf 1 = 6 := rfl
    have hexp : τ₁ ^ ((2 : ℤ) - ((1 : ℕ) : ℤ)) = τ₁ := by norm_num
    rw [hcf, hexp]
    calc |α| * (2 * |t|) ≤ |α| * (2 * (3 * τ₁)) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      _ = 6 * |α| * τ₁ := by ring
  · rw [hd2_fn, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hcf : Cf 2 = 2 := rfl
    have hexp : τ₁ ^ ((2 : ℤ) - ((2 : ℕ) : ℤ)) = 1 := by norm_num
    rw [hcf, hexp]; linarith
  · have hd3 : iteratedDeriv 3 (fun s : ℝ => s ^ 2) = 0 := by
      ext s; rw [iteratedDeriv_succ, hd2_fn]; simp [deriv_const]
    have hdk : iteratedDeriv (k + 3) (fun s : ℝ => s ^ 2) t = 0 := by
      rw [← iteratedDeriv_iteratedDeriv_eq, hd3, iteratedDeriv_const_zero]
    have hcf : Cf (k + 3) = 0 := rfl
    rw [hcf, hdk, abs_zero, mul_zero, zero_mul, zero_mul]

/-! ### Linearity helpers for `fctThetaD`, `fctMoment`, `deltaCurvSmooth`, `stripCompG` -/

lemma fctThetaD_linear {w₁ w₂ : ℝ → ℝ} (hw₁ : ContDiff ℝ (⊤ : ℕ∞) w₁) (hs₁ : HasCompactSupport w₁)
    (hw₂ : ContDiff ℝ (⊤ : ℕ∞) w₂) (hs₂ : HasCompactSupport w₂) (a b t : ℝ) :
    fctThetaD (fun s => a * w₁ s + b * w₂ s) t = a * fctThetaD w₁ t + b * fctThetaD w₂ t := by
  obtain ⟨M10, _, hM10⟩ := exists_bound_iteratedDeriv_of_compact hw₁ hs₁ 0
  obtain ⟨M11, _, hM11⟩ := exists_bound_iteratedDeriv_of_compact hw₁ hs₁ 1
  obtain ⟨M20, _, hM20⟩ := exists_bound_iteratedDeriv_of_compact hw₂ hs₂ 0
  obtain ⟨M21, _, hM21⟩ := exists_bound_iteratedDeriv_of_compact hw₂ hs₂ 1
  have hint1 : Integrable (fun z : ℝ => (w₁ (t + z) - w₁ t) / Real.sinh (π * z)) :=
    fctThetaD_integrable hw₁ (fun s => by simpa using hM10 s) (fun s => by simpa [iteratedDeriv_one] using hM11 s) t
  have hint2 : Integrable (fun z : ℝ => (w₂ (t + z) - w₂ t) / Real.sinh (π * z)) :=
    fctThetaD_integrable hw₂ (fun s => by simpa using hM20 s) (fun s => by simpa [iteratedDeriv_one] using hM21 s) t
  unfold fctThetaD
  have hfun : (fun z : ℝ => ((a * w₁ (t + z) + b * w₂ (t + z)) - (a * w₁ t + b * w₂ t)) / Real.sinh (π * z)) =
      fun z => a * ((w₁ (t + z) - w₁ t) / Real.sinh (π * z)) +
               b * ((w₂ (t + z) - w₂ t) / Real.sinh (π * z)) := by
    ext z; ring
  rw [hfun, integral_add (hint1.const_mul a) (hint2.const_mul b), integral_const_mul, integral_const_mul]

lemma deltaCurvSmooth_linear {c : ℝ} {θ₁ θ₂ : ℝ → ℝ} (hθ₁ : ContDiff ℝ (⊤ : ℕ∞) θ₁)
    (hθ₂ : ContDiff ℝ (⊤ : ℕ∞) θ₂) (a b t : ℝ) :
    deltaCurvSmooth c (fun s => a * θ₁ s + b * θ₂ s) t =
      a * deltaCurvSmooth c θ₁ t + b * deltaCurvSmooth c θ₂ t := by
  have h3 : iteratedDeriv 3 (fun s => a * θ₁ s + b * θ₂ s) =
      fun s => a * iteratedDeriv 3 θ₁ s + b * iteratedDeriv 3 θ₂ s := by
    ext s
    have h1 : ContDiffAt ℝ (3 : WithTop ℕ∞) (fun u => a * θ₁ u) s :=
      (contDiff_const.mul hθ₁).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
    have h2 : ContDiffAt ℝ (3 : WithTop ℕ∞) (fun u => b * θ₂ u) s :=
      (contDiff_const.mul hθ₂).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
    change iteratedDeriv 3 ((fun u => a * θ₁ u) + (fun u => b * θ₂ u)) s = _
    rw [iteratedDeriv_add h1 h2, iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field]
  have hd2 : divT_theta2 (fun s => a * θ₁ s + b * θ₂ s) t =
      a * divT_theta2 θ₁ t + b * divT_theta2 θ₂ t := by
    unfold divT_theta2
    rw [h3]
    have hi1 : IntervalIntegrable (fun s : ℝ => a * iteratedDeriv 3 θ₁ (s * t)) volume 0 1 :=
      (continuous_const.mul ((contDiff_iteratedDeriv_infty hθ₁ 3).continuous.comp
        (continuous_id.mul continuous_const))).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun s : ℝ => b * iteratedDeriv 3 θ₂ (s * t)) volume 0 1 :=
      (continuous_const.mul ((contDiff_iteratedDeriv_infty hθ₂ 3).continuous.comp
        (continuous_id.mul continuous_const))).intervalIntegrable _ _
    rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  have hd1 : divT2_theta1 (fun s => a * θ₁ s + b * θ₂ s) t =
      a * divT2_theta1 θ₁ t + b * divT2_theta1 θ₂ t := by
    unfold divT2_theta1
    rw [h3]
    have hrew : (fun s : ℝ => (1 - s) * (a * iteratedDeriv 3 θ₁ (s * t) + b * iteratedDeriv 3 θ₂ (s * t))) =
        fun s => a * ((1 - s) * iteratedDeriv 3 θ₁ (s * t)) + b * ((1 - s) * iteratedDeriv 3 θ₂ (s * t)) := by
      ext s; ring
    rw [hrew]
    have hi1 : IntervalIntegrable (fun s : ℝ => a * ((1 - s) * iteratedDeriv 3 θ₁ (s * t))) volume 0 1 :=
      (continuous_const.mul ((continuous_const.sub continuous_id).mul
        ((contDiff_iteratedDeriv_infty hθ₁ 3).continuous.comp
          (continuous_id.mul continuous_const)))).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun s : ℝ => b * ((1 - s) * iteratedDeriv 3 θ₂ (s * t))) volume 0 1 :=
      (continuous_const.mul ((continuous_const.sub continuous_id).mul
        ((contDiff_iteratedDeriv_infty hθ₂ 3).continuous.comp
          (continuous_id.mul continuous_const)))).intervalIntegrable _ _
    rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  unfold deltaCurvSmooth
  rw [hd2, hd1]; ring

lemma hasCompactSupport_of_support_Ioo {w : ℝ → ℝ} {a b : ℝ} (hsupp : Function.support w ⊆ Ioo a b) :
    HasCompactSupport w :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := a) (b := b))
    (fun _ ht => Ioo_subset_Icc_self (hsupp ht))

/-! ### Main Part (1) theorem: `fct_comp_D_part1` -/

set_option maxHeartbeats 400000 in
/-- **Lemma `fct:comp-D` Part (1)** (`constant_terms_five.tex`, lines 167–206), with the all-order
global closed-strip bound `‖g_D^{(r)}(ζ)‖ ≤ C_r(K₄) τ₁^{2-r}` on `S̄` for all `r ≥ 0` (including
`r = 0, 1, 2`, repairing the paper's omission of `g_D''` in `fct:comp-D` (1)). -/
theorem fct_comp_D_part1 (kind : StripKernelChoice) :
    ∃ τ₀ > 0, τ₀ ≤ 1 / 20 ∧
      ∃ (C_v0b C_v0m C_va C_v1b C_v1m : ℕ → ℝ)
        (C_th0b C_th0m C_tha C_th1b C_th1m : ℕ → ℝ)
        (C_L1_0b C_L1_0m C_L1_a C_L1_1b C_L1_1m : ℝ)
        (C_tail : ℕ → ℝ) (C_int : ℕ → ℝ),
        (∀ r, 0 ≤ C_v0b r ∧ 0 ≤ C_v0m r ∧ 0 ≤ C_va r ∧ 0 ≤ C_v1b r ∧ 0 ≤ C_v1m r) ∧
        (∀ r, 0 ≤ C_th0b r ∧ 0 ≤ C_th0m r ∧ 0 ≤ C_tha r ∧ 0 ≤ C_th1b r ∧ 0 ≤ C_th1m r) ∧
        (0 ≤ C_L1_0b ∧ 0 ≤ C_L1_0m ∧ 0 ≤ C_L1_a ∧ 0 ≤ C_L1_1b ∧ 0 ≤ C_L1_1m) ∧
        (∀ r, 0 ≤ C_tail r ∧ 0 ≤ C_int r) ∧
        ∀ {K4 c α τ₁ : ℝ}, 1 ≤ K4 → 0 < c → 0 < τ₁ → τ₁ ≤ τ₀ →
          τ₁ ^ 4 * c = 1 → |α| ≤ τ₁ ^ 2 →
          let vb0 := v0Base kind τ₁
          let vm0 := v0Marg τ₁
          let v0' := v0 kind K4 τ₁
          let va := vAlpha α τ₁
          let vb1 := v1Base kind c τ₁
          let vm1 := v1Marg c τ₁
          let v1' := v1 kind K4 c τ₁
          let v := vTotal kind K4 c α τ₁
          -- Regularity, evenness, support, vanishing at 0
          (ContDiff ℝ (⊤ : ℕ∞) vb0 ∧ ContDiff ℝ (⊤ : ℕ∞) vm0 ∧ ContDiff ℝ (⊤ : ℕ∞) va ∧
           ContDiff ℝ (⊤ : ℕ∞) vb1 ∧ ContDiff ℝ (⊤ : ℕ∞) vm1 ∧ ContDiff ℝ (⊤ : ℕ∞) v) ∧
          ((∀ t, vb0 (-t) = vb0 t) ∧ (∀ t, vm0 (-t) = vm0 t) ∧ (∀ t, va (-t) = va t) ∧
           (∀ t, vb1 (-t) = vb1 t) ∧ (∀ t, vm1 (-t) = vm1 t) ∧ (∀ t, v (-t) = v t)) ∧
          (vb0 0 = 0 ∧ vm0 0 = 0 ∧ va 0 = 0 ∧ vb1 0 = 0 ∧ vm1 0 = 0 ∧ v 0 = 0) ∧
          (Function.support vb0 ⊆ Ioo (-10 * τ₁) (10 * τ₁) ∧
           Function.support vm0 ⊆ Ioo (-10 * τ₁) (10 * τ₁) ∧
           Function.support va ⊆ Ioo (-10 * τ₁) (10 * τ₁) ∧
           Function.support vb1 ⊆ Ioo (-10 * τ₁) (10 * τ₁) ∧
           Function.support vm1 ⊆ Ioo (-10 * τ₁) (10 * τ₁) ∧
           Function.support v ⊆ Ioo (-10 * τ₁) (10 * τ₁)) ∧
          -- Five zeroed odd moments (`j = 0..4`) and vanishing odd phase derivatives
          (∀ k < 5, fctMoment k v0' = 0 ∧ fctMoment k v1' = 0 ∧ fctMoment k va = 0 ∧ fctMoment k v = 0 ∧
            iteratedDeriv (2 * k + 1) (fctThetaD v0') 0 = 0 ∧
            iteratedDeriv (2 * k + 1) (fctThetaD v1') 0 = 0 ∧
            iteratedDeriv (2 * k + 1) (fctThetaD va) 0 = 0 ∧
            iteratedDeriv (2 * k + 1) (fctThetaD v) 0 = 0) ∧
          -- Exact inner form `(fct:v-inner)` on `|t| ≤ 2 τ₁`
          (∀ t, |t| ≤ 2 * τ₁ →
            vb0 t = f0Base kind t ∧
            vm0 t = -(t ^ 4) ∧
            va t = α * t ^ 2 ∧
            v1' t = -deltaCurvSmooth c (fctThetaD v0') t) ∧
          -- All-order derivative bounds `(fct:v-derivs)`–`(fct:v1-derivs)`
          (∀ r t,
            |iteratedDeriv r vb0 t| ≤ C_v0b r * τ₁ ^ ((2 : ℤ) - r) ∧
            |iteratedDeriv r vm0 t| ≤ C_v0m r * τ₁ ^ ((4 : ℤ) - r) ∧
            |iteratedDeriv r va t| ≤ C_va r * |α| * τ₁ ^ ((2 : ℤ) - r) ∧
            |iteratedDeriv r vb1 t| ≤ C_v1b r * c⁻¹ * τ₁ ^ ((-1 : ℤ) - r) ∧
            |iteratedDeriv r vm1 t| ≤ C_v1m r * c⁻¹ * τ₁ ^ ((1 : ℤ) - r)) ∧
          -- L¹ bounds
          ((∫ t : ℝ, |vb0 t|) ≤ C_L1_0b * τ₁ ^ 3 ∧
           (∫ t : ℝ, |vm0 t|) ≤ C_L1_0m * τ₁ ^ 5 ∧
           (∫ t : ℝ, |va t|) ≤ C_L1_a * |α| * τ₁ ^ 3 ∧
           (∫ t : ℝ, |vb1 t|) ≤ C_L1_1b * c⁻¹ ∧
           (∫ t : ℝ, |vm1 t|) ≤ C_L1_1m * c⁻¹ * τ₁ ^ 2) ∧
          -- Inner phase bounds `(fct:th-inner)`–`(fct:th1-inner)` on `|t| ≤ 12 τ₁`
          (∀ r t, |t| ≤ 12 * τ₁ →
            |iteratedDeriv r (fctThetaD vb0) t| ≤ C_th0b r * τ₁ ^ ((2 : ℤ) - r) * min 1 ((|t| / τ₁) ^ (11 - r)) ∧
            |iteratedDeriv r (fctThetaD vm0) t| ≤ C_th0m r * τ₁ ^ ((4 : ℤ) - r) * min 1 ((|t| / τ₁) ^ (11 - r)) ∧
            |iteratedDeriv r (fctThetaD va) t| ≤ C_tha r * |α| * τ₁ ^ ((2 : ℤ) - r) * min 1 ((|t| / τ₁) ^ (11 - r)) ∧
            |iteratedDeriv r (fctThetaD vb1) t| ≤ C_th1b r * c⁻¹ * τ₁ ^ ((-1 : ℤ) - r) * min 1 ((|t| / τ₁) ^ (11 - r)) ∧
            |iteratedDeriv r (fctThetaD vm1) t| ≤ C_th1m r * c⁻¹ * τ₁ ^ ((1 : ℤ) - r) * min 1 ((|t| / τ₁) ^ (11 - r))) ∧
          -- Tail phase bounds `(fct:th-tail)` on `|t| ≥ 12 τ₁`
          (∀ r t, 12 * τ₁ ≤ |t| →
            |iteratedDeriv r (fctThetaD v0') t| ≤
              C_tail r * (C_L1_0b + K4 * C_L1_0m) * τ₁ ^ 3 * |t| ^ (-(1 + (r : ℤ))) * Real.exp (-(π / 2) * |t|) ∧
            |iteratedDeriv r (fctThetaD v1') t| ≤
              C_tail r * (C_L1_1b + K4 * C_L1_1m) * c⁻¹ * |t| ^ (-(1 + (r : ℤ))) * Real.exp (-(π / 2) * |t|) ∧
            |iteratedDeriv r (fctThetaD va) t| ≤
              C_tail r * C_L1_a * |α| * τ₁ ^ 3 * |t| ^ (-(1 + (r : ℤ))) * Real.exp (-(π / 2) * |t|)) ∧
          -- Interior strip bound `(fct:gD-int)` on `Re ζ ∈ [1/8, 7/8]` for all `r ≥ 0`
          (∀ r (ζ : ℂ), 1 / 8 ≤ ζ.re → ζ.re ≤ 7 / 8 →
            ‖iteratedDeriv r (stripCompG v) ζ‖ ≤
              C_int r * ((C_L1_0b + K4 * C_L1_0m) + (C_L1_1b + K4 * C_L1_1m) + C_L1_a) * τ₁ ^ 3 *
                Real.exp (-(π * |ζ.im|))) ∧
          -- Global closed-strip bound on `S̄` for ALL `r ≥ 0` (including `r = 0, 1, 2`, repairing `g_D''`!)
          (∀ r (ζ : ℂ), ζ ∈ closedStrip →
            ‖(-Complex.I) ^ r * stripCompGExt (iteratedDeriv r v) ζ‖ ≤
              ((C_v0b r + K4 * C_v0m r + C_v1b r + K4 * C_v1m r + C_va r) +
               max (C_th0b r + K4 * C_th0m r + C_th1b r + K4 * C_th1m r + C_tha r)
                 (C_tail r * ((C_L1_0b + K4 * C_L1_0m) + (C_L1_1b + K4 * C_L1_1m) + C_L1_a) *
                   (12 : ℝ) ^ (-(1 + (r : ℤ))))) * τ₁ ^ ((2 : ℤ) - r)) ∧
          -- Normalization `D(0) = D(1) = 1`
          (stripCompGExt v 0 = 0 ∧ stripCompGExt v 1 = 0 ∧
            Complex.exp (stripCompGExt v 0) = 1 ∧ Complex.exp (stripCompGExt v 1) = 1) := by
  -- 1. Instantiate `fct_moment_solver 5`
  obtain ⟨τ_ms, hτ_ms_pos, hms⟩ := fct_moment_solver 5 (by norm_num)
  -- 2. Target derivative-bound profiles for `f0Base`, `-t⁴`, `α t²`
  have hf0b_all := even_smooth_target_bounds (contDiffOn_f0Base kind) (fun t ht => f0Base_even ht) (f0Base_zero kind)
  choose Cf0b hCf0b_nn hCf0b_bd using hf0b_all
  obtain ⟨Cf0m, hCf0m_nn, hCf0m_bd⟩ := deriv_bounds_neg_pow4
  obtain ⟨Cfa, hCfa_nn, hCfa_bd⟩ := deriv_bounds_alpha_pow2
  -- 3. Apply `hms` to the three leading targets
  obtain ⟨Cv0b, CL1_0b, Cth0b, hCv0b_nn, hCL1_0b_nn, hCth0b_nn, hv0b_spec⟩ := hms Cf0b hCf0b_nn
  obtain ⟨Cv0m, CL1_0m, Cth0m, hCv0m_nn, hCL1_0m_nn, hCth0m_nn, hv0m_spec⟩ := hms Cf0m hCf0m_nn
  obtain ⟨Cva, CL1_a, Ctha, hCva_nn, hCL1_a_nn, hCtha_nn, hva_spec⟩ := hms Cfa hCfa_nn
  -- 4. Curvature target derivative-bound profiles from `abs_iteratedDeriv_deltaCurvSmooth_le`
  choose Cf1b hCf1b_nn hCf1b_bd using fun r => abs_iteratedDeriv_deltaCurvSmooth_le r Cth0b hCth0b_nn
  choose Cf1m hCf1m_nn hCf1m_bd using fun r => abs_iteratedDeriv_deltaCurvSmooth_le r Cth0m hCth0m_nn
  -- 5. Apply `hms` to the two curvature targets
  obtain ⟨Cv1b, CL1_1b, Cth1b, hCv1b_nn, hCL1_1b_nn, hCth1b_nn, hv1b_spec⟩ := hms Cf1b hCf1b_nn
  obtain ⟨Cv1m, CL1_1m, Cth1m, hCv1m_nn, hCL1_1m_nn, hCth1m_nn, hv1m_spec⟩ := hms Cf1m hCf1m_nn
  -- 6. Tail and interior strip constants
  choose C_tail hC_tail_nn hC_tail_bd using fun r => abs_iteratedDeriv_fctThetaD_tail r
  choose C_int hC_int_nn hC_int_bd using fun r => norm_iteratedDeriv_stripCompG_interior r
  refine ⟨min τ_ms (1 / 20), lt_min hτ_ms_pos (by norm_num), min_le_right _ _,
    Cv0b, Cv0m, Cva, Cv1b, Cv1m, Cth0b, Cth0m, Ctha, Cth1b, Cth1m,
    CL1_0b, CL1_0m, CL1_a, CL1_1b, CL1_1m, C_tail, C_int,
    fun r => ⟨hCv0b_nn r, hCv0m_nn r, hCva_nn r, hCv1b_nn r, hCv1m_nn r⟩,
    fun r => ⟨hCth0b_nn r, hCth0m_nn r, hCtha_nn r, hCth1b_nn r, hCth1m_nn r⟩,
    ⟨hCL1_0b_nn, hCL1_0m_nn, hCL1_a_nn, hCL1_1b_nn, hCL1_1m_nn⟩,
    fun r => ⟨hC_tail_nn r, hC_int_nn r⟩,
    fun {K4 c α τ₁} hK4 hc hτ₁ hτ₁_le hc_eq hα_le => ?_⟩
  have hτ₁_ms : τ₁ ∈ Ioc (0 : ℝ) τ_ms := ⟨hτ₁, hτ₁_le.trans (min_le_left _ _)⟩
  have hτ₁_20 : τ₁ ≤ 1 / 20 := hτ₁_le.trans (min_le_right _ _)
  have hτ₁_16 : τ₁ ≤ 1 / 16 := by linarith
  have hτ₁_1 : τ₁ ≤ 1 := by linarith
  have hc_inv : c⁻¹ = τ₁ ^ 4 := by
    rw [inv_eq_iff_eq_inv]; field_simp [hc.ne', hτ₁.ne'] at hc_eq ⊢; linarith
  have h3τ_sub : Ioo (-3 * τ₁) (3 * τ₁) ⊆ Ioo (-1 / 4 : ℝ) (1 / 4) := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- Apply `hv0b_spec`, `hv0m_spec`, `hva_spec`
  have hb0 := hv0b_spec (τ₁ := τ₁) (M := 1) (f := f0Base kind) hτ₁_ms zero_le_one
    ((contDiffOn_f0Base kind).mono h3τ_sub)
    (fun t ht => f0Base_even (abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩))
    (f0Base_zero kind)
    (fun r t ht => by
      simpa only [mul_one] using hCf0b_bd r hτ₁ hτ₁_16 t ⟨by linarith [(abs_le.mp ht).1], (abs_le.mp ht).2⟩)
  have hm0 := hv0m_spec (τ₁ := τ₁) (M := τ₁ ^ 2) (f := fun t => -(t ^ 4)) hτ₁_ms (sq_nonneg τ₁)
    ((contDiff_id.pow 4).neg).contDiffOn
    (fun t _ => by ring)
    (by norm_num)
    (fun r t ht => hCf0m_bd hτ₁ hτ₁_16 r t ht)
  have ha0 := hva_spec (τ₁ := τ₁) (M := |α|) (f := fun t => α * t ^ 2) hτ₁_ms (abs_nonneg α)
    (contDiff_const.mul (contDiff_id.pow 2)).contDiffOn
    (fun t _ => by ring)
    (by ring)
    (fun r t ht => hCfa_bd hτ₁ hτ₁_16 r t ht)
  -- Unpack properties of `v0Base`, `v0Marg`, `vAlpha` (folding back to their named definitions!)
  rw [show momentSolver 5 τ₁ (f0Base kind) = v0Base kind τ₁ from rfl] at hb0
  rw [show momentSolver 5 τ₁ (fun t => -(t ^ 4)) = v0Marg τ₁ from rfl] at hm0
  rw [show momentSolver 5 τ₁ (fun t => α * t ^ 2) = vAlpha α τ₁ from rfl] at ha0
  obtain ⟨hb0_cd, hb0_even, hb0_0, hb0_supp, hb0_eq, hb0_mom, hb0_th0, hb0_deriv, hb0_L1, hb0_th⟩ := hb0
  obtain ⟨hm0_cd, hm0_even, hm0_0, hm0_supp, hm0_eq, hm0_mom, hm0_th0, hm0_deriv, hm0_L1, hm0_th⟩ := hm0
  obtain ⟨ha0_cd, ha0_even, ha0_0, ha0_supp, ha0_eq, ha0_mom, ha0_th0, ha0_deriv, ha0_L1, ha0_th⟩ := ha0
  have hb0_cs : HasCompactSupport (v0Base kind τ₁) := hasCompactSupport_of_support_Ioo hb0_supp
  have hm0_cs : HasCompactSupport (v0Marg τ₁) := hasCompactSupport_of_support_Ioo hm0_supp
  have ha0_cs : HasCompactSupport (vAlpha α τ₁) := hasCompactSupport_of_support_Ioo ha0_supp
  -- Smoothness and oddness of `fctThetaD (v0Base kind τ₁)` and `fctThetaD (v0Marg τ₁)`
  have hθ0b_cd : ContDiff ℝ (⊤ : ℕ∞) (fctThetaD (v0Base kind τ₁)) := contDiff_fctThetaD hb0_cd hb0_cs
  have hθ0m_cd : ContDiff ℝ (⊤ : ℕ∞) (fctThetaD (v0Marg τ₁)) := contDiff_fctThetaD hm0_cd hm0_cs
  have hθa_cd : ContDiff ℝ (⊤ : ℕ∞) (fctThetaD (vAlpha α τ₁)) := contDiff_fctThetaD ha0_cd ha0_cs
  have hθ0b_odd : ∀ t, fctThetaD (v0Base kind τ₁) (-t) = -fctThetaD (v0Base kind τ₁) t :=
    fctThetaD_odd hb0_even
  have hθ0m_odd : ∀ t, fctThetaD (v0Marg τ₁) (-t) = -fctThetaD (v0Marg τ₁) t :=
    fctThetaD_odd hm0_even
  -- Curvature targets vanish at 0 since `ϑ'''(0) = 0` (`k = 1 < 5`)
  have hθ0b_30 : iteratedDeriv 3 (fctThetaD (v0Base kind τ₁)) 0 = 0 := hb0_th0 1 (by norm_num)
  have hθ0m_30 : iteratedDeriv 3 (fctThetaD (v0Marg τ₁)) 0 = 0 := hm0_th0 1 (by norm_num)
  have hf1b_0 : -deltaCurvSmooth c (fctThetaD (v0Base kind τ₁)) 0 = 0 := by
    unfold deltaCurvSmooth divT_theta2 divT2_theta1
    simp [hθ0b_30]
  have hf1m_0 : -deltaCurvSmooth c (fctThetaD (v0Marg τ₁)) 0 = 0 := by
    unfold deltaCurvSmooth divT_theta2 divT2_theta1
    simp [hθ0m_30]
  -- Apply `hv1b_spec` and `hv1m_spec`
  have hb1 := hv1b_spec (τ₁ := τ₁) (M := c⁻¹ * τ₁ ^ (-3 : ℤ))
    (f := fun t => -deltaCurvSmooth c (fctThetaD (v0Base kind τ₁)) t) hτ₁_ms (by positivity)
    ((contDiffOn_deltaCurvSmooth hθ0b_cd).neg.mono h3τ_sub)
    (fun t ht => by
      rw [deltaCurvSmooth_even hθ0b_odd (abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)])
    hf1b_0
    (fun r t ht => by
      rw [show (fun s => -deltaCurvSmooth c (fctThetaD (v0Base kind τ₁)) s) =
        -(deltaCurvSmooth c (fctThetaD (v0Base kind τ₁))) from rfl, iteratedDeriv_neg, abs_neg]
      have h := hCf1b_bd r hc zero_le_one hτ₁ hτ₁_16 hθ0b_cd
        (fun k u hu => (hb0_th k u (by linarith)).trans (by
          rw [mul_one]
          exact mul_le_of_le_one_right (mul_nonneg (hCth0b_nn k) (zpow_nonneg hτ₁.le _)) (min_le_left _ _)))
        t ⟨by linarith [(abs_le.mp ht).1], (abs_le.mp ht).2⟩
      simpa only [mul_one] using h)
  have hm1 := hv1m_spec (τ₁ := τ₁) (M := c⁻¹ * τ₁ ^ (-1 : ℤ))
    (f := fun t => -deltaCurvSmooth c (fctThetaD (v0Marg τ₁)) t) hτ₁_ms (by positivity)
    ((contDiffOn_deltaCurvSmooth hθ0m_cd).neg.mono h3τ_sub)
    (fun t ht => by
      rw [deltaCurvSmooth_even hθ0m_odd (abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)])
    hf1m_0
    (fun r t ht => by
      rw [show (fun s => -deltaCurvSmooth c (fctThetaD (v0Marg τ₁)) s) =
        -(deltaCurvSmooth c (fctThetaD (v0Marg τ₁))) from rfl, iteratedDeriv_neg, abs_neg]
      have h := hCf1m_bd r hc (sq_nonneg τ₁) hτ₁ hτ₁_16 hθ0m_cd
        (fun k u hu => (hm0_th k u (by linarith)).trans (by
          exact mul_le_of_le_one_right
            (mul_nonneg (mul_nonneg (hCth0m_nn k) (sq_nonneg τ₁)) (zpow_nonneg hτ₁.le _)) (min_le_left _ _)))
        t ⟨by linarith [(abs_le.mp ht).1], (abs_le.mp ht).2⟩
      have hM_eq : c⁻¹ * τ₁ ^ 2 * τ₁ ^ (-3 : ℤ) = c⁻¹ * τ₁ ^ (-1 : ℤ) := by
        rw [mul_assoc, ← zpow_natCast τ₁ 2, ← zpow_add₀ hτ₁.ne']; norm_num
      rwa [hM_eq] at h)
  rw [show momentSolver 5 τ₁ (fun t => -deltaCurvSmooth c (fctThetaD (v0Base kind τ₁)) t) = v1Base kind c τ₁ from rfl] at hb1
  rw [show momentSolver 5 τ₁ (fun t => -deltaCurvSmooth c (fctThetaD (v0Marg τ₁)) t) = v1Marg c τ₁ from rfl] at hm1
  obtain ⟨hb1_cd, hb1_even, hb1_0, hb1_supp, hb1_eq, hb1_mom, hb1_th0, hb1_deriv, hb1_L1, hb1_th⟩ := hb1
  obtain ⟨hm1_cd, hm1_even, hm1_0, hm1_supp, hm1_eq, hm1_mom, hm1_th0, hm1_deriv, hm1_L1, hm1_th⟩ := hm1
  have hb1_cs : HasCompactSupport (v1Base kind c τ₁) := hasCompactSupport_of_support_Ioo hb1_supp
  have hm1_cs : HasCompactSupport (v1Marg c τ₁) := hasCompactSupport_of_support_Ioo hm1_supp
  -- Combined regularity, evenness, support for `v0`, `v1`, `vTotal`
  have hv0_cd : ContDiff ℝ (⊤ : ℕ∞) (v0 kind K4 τ₁) := hb0_cd.add (contDiff_const.mul hm0_cd)
  have hv1_cd : ContDiff ℝ (⊤ : ℕ∞) (v1 kind K4 c τ₁) := hb1_cd.add (contDiff_const.mul hm1_cd)
  have hv_cd : ContDiff ℝ (⊤ : ℕ∞) (vTotal kind K4 c α τ₁) := (hv0_cd.add hv1_cd).add ha0_cd
  have hv0_even : ∀ t, v0 kind K4 τ₁ (-t) = v0 kind K4 τ₁ t := fun t => by
    unfold v0; rw [hb0_even, hm0_even]
  have hv1_even : ∀ t, v1 kind K4 c τ₁ (-t) = v1 kind K4 c τ₁ t := fun t => by
    unfold v1; rw [hb1_even, hm1_even]
  have hv_even : ∀ t, vTotal kind K4 c α τ₁ (-t) = vTotal kind K4 c α τ₁ t := fun t => by
    unfold vTotal; rw [hv0_even, hv1_even, ha0_even]
  have hv0_supp : Function.support (v0 kind K4 τ₁) ⊆ Ioo (-10 * τ₁) (10 * τ₁) := by
    intro t ht; by_contra hnot
    have h1 : v0Base kind τ₁ t = 0 := by by_contra hne; exact hnot (hb0_supp hne)
    have h2 : v0Marg τ₁ t = 0 := by by_contra hne; exact hnot (hm0_supp hne)
    exact ht (by simp [v0, h1, h2])
  have hv1_supp : Function.support (v1 kind K4 c τ₁) ⊆ Ioo (-10 * τ₁) (10 * τ₁) := by
    intro t ht; by_contra hnot
    have h1 : v1Base kind c τ₁ t = 0 := by by_contra hne; exact hnot (hb1_supp hne)
    have h2 : v1Marg c τ₁ t = 0 := by by_contra hne; exact hnot (hm1_supp hne)
    exact ht (by simp [v1, h1, h2])
  have hv_supp : Function.support (vTotal kind K4 c α τ₁) ⊆ Ioo (-10 * τ₁) (10 * τ₁) := by
    intro t ht; by_contra hnot
    have h1 : v0 kind K4 τ₁ t = 0 := by by_contra hne; exact hnot (hv0_supp hne)
    have h2 : v1 kind K4 c τ₁ t = 0 := by by_contra hne; exact hnot (hv1_supp hne)
    have h3 : vAlpha α τ₁ t = 0 := by by_contra hne; exact hnot (ha0_supp hne)
    exact ht (by simp [vTotal, h1, h2, h3])
  have hv0_cs : HasCompactSupport (v0 kind K4 τ₁) := hasCompactSupport_of_support_Ioo hv0_supp
  have hv1_cs : HasCompactSupport (v1 kind K4 c τ₁) := hasCompactSupport_of_support_Ioo hv1_supp
  have hv_cs : HasCompactSupport (vTotal kind K4 c α τ₁) := hasCompactSupport_of_support_Ioo hv_supp
  -- Linearity of `fctThetaD` on `v0`, `v1`, `vTotal`
  have hθ0_eq : fctThetaD (v0 kind K4 τ₁) =
      fun t => fctThetaD (v0Base kind τ₁) t + K4 * fctThetaD (v0Marg τ₁) t := by
    ext t
    unfold v0
    have h := fctThetaD_linear hb0_cd hb0_cs hm0_cd hm0_cs 1 K4 t
    simpa only [one_mul] using h
  have hθ1_eq : fctThetaD (v1 kind K4 c τ₁) =
      fun t => fctThetaD (v1Base kind c τ₁) t + K4 * fctThetaD (v1Marg c τ₁) t := by
    ext t
    unfold v1
    have h := fctThetaD_linear hb1_cd hb1_cs hm1_cd hm1_cs 1 K4 t
    simpa only [one_mul] using h
  have hθ_eq : fctThetaD (vTotal kind K4 c α τ₁) =
      fun t => fctThetaD (v0 kind K4 τ₁) t + fctThetaD (v1 kind K4 c τ₁) t + fctThetaD (vAlpha α τ₁) t := by
    ext t
    have h1 := fctThetaD_linear hv0_cd hv0_cs hv1_cd hv1_cs 1 1 t
    have h2 := fctThetaD_linear (hv0_cd.add hv1_cd) (hv0_cs.add hv1_cs) ha0_cd ha0_cs 1 1 t
    simp only [one_mul] at h1 h2
    change fctThetaD (fun s => (v0 kind K4 τ₁ s + v1 kind K4 c τ₁ s) + vAlpha α τ₁ s) t = _
    rw [h2, h1]
  -- L¹ norm bounds for components and sums
  have hL1_0b' : (∫ t : ℝ, |v0Base kind τ₁ t|) ≤ CL1_0b * τ₁ ^ 3 := by simpa only [mul_one] using hb0_L1
  have hL1_0m' : (∫ t : ℝ, |v0Marg τ₁ t|) ≤ CL1_0m * τ₁ ^ 5 := by
    have : CL1_0m * τ₁ ^ 2 * τ₁ ^ 3 = CL1_0m * τ₁ ^ 5 := by ring
    linarith
  have hL1_a' : (∫ t : ℝ, |vAlpha α τ₁ t|) ≤ CL1_a * |α| * τ₁ ^ 3 := ha0_L1
  have hL1_1b' : (∫ t : ℝ, |v1Base kind c τ₁ t|) ≤ CL1_1b * c⁻¹ := by
    have : CL1_1b * (c⁻¹ * τ₁ ^ (-3 : ℤ)) * τ₁ ^ 3 = CL1_1b * c⁻¹ := by
      rw [zpow_neg, show (3 : ℤ) = ((3 : ℕ) : ℤ) by rfl, zpow_natCast]; field_simp [hτ₁.ne']
    linarith
  have hL1_1m' : (∫ t : ℝ, |v1Marg c τ₁ t|) ≤ CL1_1m * c⁻¹ * τ₁ ^ 2 := by
    have : CL1_1m * (c⁻¹ * τ₁ ^ (-1 : ℤ)) * τ₁ ^ 3 = CL1_1m * c⁻¹ * τ₁ ^ 2 := by
      rw [zpow_neg_one]; field_simp [hτ₁.ne']
    linarith
  have hL1_v0 : (∫ t : ℝ, |v0 kind K4 τ₁ t|) ≤ (CL1_0b + K4 * CL1_0m) * τ₁ ^ 3 := by
    have hint1 : Integrable (fun t => |v0Base kind τ₁ t|) :=
      hb0_cd.continuous.abs.integrable_of_hasCompactSupport (hb0_cs.comp_left abs_zero)
    have hint2 : Integrable (fun t => |v0Marg τ₁ t|) :=
      hm0_cd.continuous.abs.integrable_of_hasCompactSupport (hm0_cs.comp_left abs_zero)
    have hK4_pos : 0 ≤ K4 := by linarith
    have hmono : (∫ t : ℝ, |v0 kind K4 τ₁ t|) ≤ ∫ t : ℝ, (|v0Base kind τ₁ t| + K4 * |v0Marg τ₁ t|) := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
        (hint1.add (hint2.const_mul K4)) (Filter.Eventually.of_forall fun t => ?_)
      unfold v0
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_nonneg hK4_pos]
    rw [integral_add hint1 (hint2.const_mul K4), integral_const_mul] at hmono
    have hτ5 : τ₁ ^ 5 ≤ τ₁ ^ 3 := by
      have hsq : τ₁ ^ 2 ≤ 1 := by
        calc τ₁ ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ hτ₁.le hτ₁_1 2
          _ = 1 := one_pow 2
      calc τ₁ ^ 5 = τ₁ ^ 3 * τ₁ ^ 2 := by ring
        _ ≤ τ₁ ^ 3 * 1 := mul_le_mul_of_nonneg_left hsq (pow_nonneg hτ₁.le 3)
        _ = τ₁ ^ 3 := mul_one _
    have hK4m : K4 * (CL1_0m * τ₁ ^ 5) ≤ K4 * (CL1_0m * τ₁ ^ 3) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hτ5 hCL1_0m_nn) hK4_pos
    have hK4_step : (∫ t : ℝ, |v0Base kind τ₁ t|) + K4 * (∫ t : ℝ, |v0Marg τ₁ t|) ≤
        CL1_0b * τ₁ ^ 3 + K4 * (CL1_0m * τ₁ ^ 5) :=
      add_le_add hL1_0b' (mul_le_mul_of_nonneg_left hL1_0m' hK4_pos)
    calc (∫ t : ℝ, |v0 kind K4 τ₁ t|)
        ≤ CL1_0b * τ₁ ^ 3 + K4 * (CL1_0m * τ₁ ^ 5) := hmono.trans hK4_step
      _ ≤ CL1_0b * τ₁ ^ 3 + K4 * (CL1_0m * τ₁ ^ 3) := add_le_add le_rfl hK4m
      _ = (CL1_0b + K4 * CL1_0m) * τ₁ ^ 3 := by ring
  have hL1_v1 : (∫ t : ℝ, |v1 kind K4 c τ₁ t|) ≤ (CL1_1b + K4 * CL1_1m) * c⁻¹ := by
    have hint1 : Integrable (fun t => |v1Base kind c τ₁ t|) :=
      hb1_cd.continuous.abs.integrable_of_hasCompactSupport (hb1_cs.comp_left abs_zero)
    have hint2 : Integrable (fun t => |v1Marg c τ₁ t|) :=
      hm1_cd.continuous.abs.integrable_of_hasCompactSupport (hm1_cs.comp_left abs_zero)
    have hK4_pos : 0 ≤ K4 := by linarith
    have hmono : (∫ t : ℝ, |v1 kind K4 c τ₁ t|) ≤ ∫ t : ℝ, (|v1Base kind c τ₁ t| + K4 * |v1Marg c τ₁ t|) := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
        (hint1.add (hint2.const_mul K4)) (Filter.Eventually.of_forall fun t => ?_)
      unfold v1
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_nonneg hK4_pos]
    rw [integral_add hint1 (hint2.const_mul K4), integral_const_mul] at hmono
    have hτ2 : τ₁ ^ 2 ≤ 1 := by
      calc τ₁ ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ hτ₁.le hτ₁_1 2
        _ = 1 := one_pow 2
    have hK4m : K4 * (CL1_1m * c⁻¹ * τ₁ ^ 2) ≤ K4 * (CL1_1m * c⁻¹ * 1) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hτ2 (mul_nonneg hCL1_1m_nn (inv_nonneg.mpr hc.le))) hK4_pos
    have hK4_step : (∫ t : ℝ, |v1Base kind c τ₁ t|) + K4 * (∫ t : ℝ, |v1Marg c τ₁ t|) ≤
        CL1_1b * c⁻¹ + K4 * (CL1_1m * c⁻¹ * τ₁ ^ 2) :=
      add_le_add hL1_1b' (mul_le_mul_of_nonneg_left hL1_1m' hK4_pos)
    calc (∫ t : ℝ, |v1 kind K4 c τ₁ t|)
        ≤ CL1_1b * c⁻¹ + K4 * (CL1_1m * c⁻¹ * τ₁ ^ 2) := hmono.trans hK4_step
      _ ≤ CL1_1b * c⁻¹ + K4 * (CL1_1m * c⁻¹ * 1) := add_le_add le_rfl hK4m
      _ = (CL1_1b + K4 * CL1_1m) * c⁻¹ := by ring
  have hL1_v : (∫ t : ℝ, |vTotal kind K4 c α τ₁ t|) ≤
      ((CL1_0b + K4 * CL1_0m) + (CL1_1b + K4 * CL1_1m) + CL1_a) * τ₁ ^ 3 := by
    have hint0 : Integrable (fun t => |v0 kind K4 τ₁ t|) :=
      hv0_cd.continuous.abs.integrable_of_hasCompactSupport (hv0_cs.comp_left abs_zero)
    have hint1 : Integrable (fun t => |v1 kind K4 c τ₁ t|) :=
      hv1_cd.continuous.abs.integrable_of_hasCompactSupport (hv1_cs.comp_left abs_zero)
    have hinta : Integrable (fun t => |vAlpha α τ₁ t|) :=
      ha0_cd.continuous.abs.integrable_of_hasCompactSupport (ha0_cs.comp_left abs_zero)
    have hint01 : Integrable (fun t => |v0 kind K4 τ₁ t| + |v1 kind K4 c τ₁ t|) := hint0.add hint1
    have hmono : (∫ t : ℝ, |vTotal kind K4 c α τ₁ t|) ≤
        ∫ t : ℝ, ((|v0 kind K4 τ₁ t| + |v1 kind K4 c τ₁ t|) + |vAlpha α τ₁ t|) := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
        (hint01.add hinta) (Filter.Eventually.of_forall fun t => ?_)
      unfold vTotal
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    rw [integral_add hint01 hinta, integral_add hint0 hint1] at hmono
    have hc_le : c⁻¹ ≤ τ₁ ^ 3 := by
      rw [hc_inv]
      calc τ₁ ^ 4 = τ₁ ^ 3 * τ₁ := by ring
        _ ≤ τ₁ ^ 3 * 1 := mul_le_mul_of_nonneg_left hτ₁_1 (pow_nonneg hτ₁.le 3)
        _ = τ₁ ^ 3 := mul_one _
    have hα_le1 : |α| ≤ 1 := hα_le.trans (pow_le_one₀ hτ₁.le hτ₁_1)
    have h1 : (CL1_1b + K4 * CL1_1m) * c⁻¹ ≤ (CL1_1b + K4 * CL1_1m) * τ₁ ^ 3 :=
      mul_le_mul_of_nonneg_left hc_le (by positivity)
    have h2 : CL1_a * |α| * τ₁ ^ 3 ≤ CL1_a * τ₁ ^ 3 := by
      have := mul_le_mul_of_nonneg_left hα_le1 hCL1_a_nn
      rw [mul_one] at this
      exact mul_le_mul_of_nonneg_right this (pow_nonneg hτ₁.le 3)
    linarith
  -- Exponent helpers
  have hexp_m0 : ∀ r : ℕ, τ₁ ^ 2 * τ₁ ^ ((2 : ℤ) - r) = τ₁ ^ ((4 : ℤ) - r) := fun r => by
    rw [← zpow_natCast τ₁ 2, ← zpow_add₀ hτ₁.ne']; congr 1; omega
  have hexp_1b : ∀ r : ℕ, (c⁻¹ * τ₁ ^ (-3 : ℤ)) * τ₁ ^ ((2 : ℤ) - r) = c⁻¹ * τ₁ ^ ((-1 : ℤ) - r) := fun r => by
    rw [mul_assoc, ← zpow_add₀ hτ₁.ne']; congr 2; omega
  have hexp_1m : ∀ r : ℕ, (c⁻¹ * τ₁ ^ (-1 : ℤ)) * τ₁ ^ ((2 : ℤ) - r) = c⁻¹ * τ₁ ^ ((1 : ℤ) - r) := fun r => by
    rw [mul_assoc, ← zpow_add₀ hτ₁.ne']; congr 2; omega
  -- Derivative bounds in exact paper form
  have hderivs : ∀ r t,
      |iteratedDeriv r (v0Base kind τ₁) t| ≤ Cv0b r * τ₁ ^ ((2 : ℤ) - r) ∧
      |iteratedDeriv r (v0Marg τ₁) t| ≤ Cv0m r * τ₁ ^ ((4 : ℤ) - r) ∧
      |iteratedDeriv r (vAlpha α τ₁) t| ≤ Cva r * |α| * τ₁ ^ ((2 : ℤ) - r) ∧
      |iteratedDeriv r (v1Base kind c τ₁) t| ≤ Cv1b r * c⁻¹ * τ₁ ^ ((-1 : ℤ) - r) ∧
      |iteratedDeriv r (v1Marg c τ₁) t| ≤ Cv1m r * c⁻¹ * τ₁ ^ ((1 : ℤ) - r) := by
    intro r t
    refine ⟨by simpa only [mul_one] using hb0_deriv r t, ?_, ha0_deriv r t, ?_, ?_⟩
    · have := hm0_deriv r t; rw [mul_assoc, hexp_m0] at this; exact this
    · have := hb1_deriv r t; rw [mul_assoc, hexp_1b, ← mul_assoc] at this; exact this
    · have := hm1_deriv r t; rw [mul_assoc, hexp_1m, ← mul_assoc] at this; exact this
  -- Inner phase bounds in exact paper form
  have hth_in : ∀ r t, |t| ≤ 12 * τ₁ →
      |iteratedDeriv r (fctThetaD (v0Base kind τ₁)) t| ≤ Cth0b r * τ₁ ^ ((2 : ℤ) - r) * min 1 ((|t| / τ₁) ^ (11 - r)) ∧
      |iteratedDeriv r (fctThetaD (v0Marg τ₁)) t| ≤ Cth0m r * τ₁ ^ ((4 : ℤ) - r) * min 1 ((|t| / τ₁) ^ (11 - r)) ∧
      |iteratedDeriv r (fctThetaD (vAlpha α τ₁)) t| ≤ Ctha r * |α| * τ₁ ^ ((2 : ℤ) - r) * min 1 ((|t| / τ₁) ^ (11 - r)) ∧
      |iteratedDeriv r (fctThetaD (v1Base kind c τ₁)) t| ≤ Cth1b r * c⁻¹ * τ₁ ^ ((-1 : ℤ) - r) * min 1 ((|t| / τ₁) ^ (11 - r)) ∧
      |iteratedDeriv r (fctThetaD (v1Marg c τ₁)) t| ≤ Cth1m r * c⁻¹ * τ₁ ^ ((1 : ℤ) - r) * min 1 ((|t| / τ₁) ^ (11 - r)) := by
    intro r t ht
    have h11 : 2 * 5 + 1 - r = 11 - r := rfl
    refine ⟨by simpa only [mul_one, h11] using hb0_th r t ht, ?_,
      by simpa only [h11] using ha0_th r t ht, ?_, ?_⟩
    · have := hm0_th r t ht; rw [h11, mul_assoc (Cth0m r), hexp_m0] at this; exact this
    · have := hb1_th r t ht; rw [h11, mul_assoc (Cth1b r), hexp_1b, ← mul_assoc (Cth1b r)] at this; exact this
    · have := hm1_th r t ht; rw [h11, mul_assoc (Cth1m r), hexp_1m, ← mul_assoc (Cth1m r)] at this; exact this
  -- Tail phase bounds `(fct:th-tail)`
  have hth_tail : ∀ r t, 12 * τ₁ ≤ |t| →
      |iteratedDeriv r (fctThetaD (v0 kind K4 τ₁)) t| ≤
        C_tail r * (CL1_0b + K4 * CL1_0m) * τ₁ ^ 3 * |t| ^ (-(1 + (r : ℤ))) * Real.exp (-(π / 2) * |t|) ∧
      |iteratedDeriv r (fctThetaD (v1 kind K4 c τ₁)) t| ≤
        C_tail r * (CL1_1b + K4 * CL1_1m) * c⁻¹ * |t| ^ (-(1 + (r : ℤ))) * Real.exp (-(π / 2) * |t|) ∧
      |iteratedDeriv r (fctThetaD (vAlpha α τ₁)) t| ≤
        C_tail r * CL1_a * |α| * τ₁ ^ 3 * |t| ^ (-(1 + (r : ℤ))) * Real.exp (-(π / 2) * |t|) := by
    intro r t ht
    have ht_pos : 0 < |t| := lt_of_lt_of_le (by positivity) ht
    have hfac_nn : 0 ≤ |t| ^ (-(1 + (r : ℤ))) * Real.exp (-(π / 2) * |t|) :=
      mul_nonneg (zpow_nonneg ht_pos.le _) (Real.exp_pos _).le
    refine ⟨?_, ?_, ?_⟩
    · have h := hC_tail_bd r hv0_cd hτ₁ hτ₁_20 hv0_supp t ht
      refine h.trans (by
        rw [mul_assoc, mul_assoc, mul_assoc (C_tail r), mul_assoc (C_tail r * _), mul_assoc]
        have := mul_le_mul_of_nonneg_left hL1_v0 (hC_tail_nn r)
        have := mul_le_mul_of_nonneg_right this hfac_nn
        linarith)
    · have h := hC_tail_bd r hv1_cd hτ₁ hτ₁_20 hv1_supp t ht
      refine h.trans (by
        have := mul_le_mul_of_nonneg_left hL1_v1 (hC_tail_nn r)
        have := mul_le_mul_of_nonneg_right this hfac_nn
        linarith)
    · have h := hC_tail_bd r ha0_cd hτ₁ hτ₁_20 ha0_supp t ht
      refine h.trans (by
        have := mul_le_mul_of_nonneg_left hL1_a' (hC_tail_nn r)
        have := mul_le_mul_of_nonneg_right this hfac_nn
        linarith)
  -- Assemble all conclusions
  refine ⟨⟨hb0_cd, hm0_cd, ha0_cd, hb1_cd, hm1_cd, hv_cd⟩,
    ⟨hb0_even, hm0_even, ha0_even, hb1_even, hm1_even, hv_even⟩,
    ⟨hb0_0, hm0_0, ha0_0, hb1_0, hm1_0, by simp [vTotal, v0, v1, hb0_0, hm0_0, hb1_0, hm1_0, ha0_0]⟩,
    ⟨hb0_supp, hm0_supp, ha0_supp, hb1_supp, hm1_supp, hv_supp⟩,
    ?_, ?_, hderivs, ⟨hL1_0b', hL1_0m', hL1_a', hL1_1b', hL1_1m'⟩, hth_in, hth_tail, ?_, ?_, ?_⟩
  · -- Five zeroed moments and odd phase derivatives
    intro k hk
    have hm_v0 : fctMoment k (v0 kind K4 τ₁) = 0 := by
      unfold v0
      have h := fctMoment_linear hb0_cd hb0_cs hb0_even hm0_cd hm0_cs hm0_even 1 K4 k
      simp only [one_mul, hb0_mom k hk, hm0_mom k hk, mul_zero, add_zero] at h
      exact h
    have hm_v1 : fctMoment k (v1 kind K4 c τ₁) = 0 := by
      unfold v1
      have h := fctMoment_linear hb1_cd hb1_cs hb1_even hm1_cd hm1_cs hm1_even 1 K4 k
      simp only [one_mul, hb1_mom k hk, hm1_mom k hk, mul_zero, add_zero] at h
      exact h
    have hm_va : fctMoment k (vAlpha α τ₁) = 0 := ha0_mom k hk
    have hm_v : fctMoment k (vTotal kind K4 c α τ₁) = 0 := by
      unfold vTotal
      have h1 := fctMoment_linear hv0_cd hv0_cs hv0_even hv1_cd hv1_cs hv1_even 1 1 k
      have h2 := fctMoment_linear (hv0_cd.add hv1_cd) (hv0_cs.add hv1_cs) (fun t => by simp [hv0_even, hv1_even])
        ha0_cd ha0_cs ha0_even 1 1 k
      simp only [one_mul, hm_v0, hm_v1, hm_va, add_zero] at h1 h2
      change fctMoment k (fun s => (v0 kind K4 τ₁ s + v1 kind K4 c τ₁ s) + vAlpha α τ₁ s) = 0
      rw [h2, h1]
    refine ⟨hm_v0, hm_v1, hm_va, hm_v, ?_, ?_, ha0_th0 k hk, ?_⟩
    · rw [iteratedDeriv_odd_fctThetaD_zero hv0_cd hv0_cs hv0_even k, hm_v0, mul_zero]
    · rw [iteratedDeriv_odd_fctThetaD_zero hv1_cd hv1_cs hv1_even k, hm_v1, mul_zero]
    · rw [iteratedDeriv_odd_fctThetaD_zero hv_cd hv_cs hv_even k, hm_v, mul_zero]
  · -- Exact inner form `(fct:v-inner)` on `|t| ≤ 2 τ₁`
    intro t ht
    refine ⟨hb0_eq t ht, hm0_eq t ht, ha0_eq t ht, ?_⟩
    unfold v1
    rw [hb1_eq t ht, hm1_eq t ht, hθ0_eq]
    have hlin := deltaCurvSmooth_linear (c := c) hθ0b_cd hθ0m_cd 1 K4 t
    simp only [one_mul] at hlin
    rw [hlin]; ring
  · -- Interior strip bound `(fct:gD-int)`
    intro r ζ hre1 hre2
    have h := hC_int_bd r hv_cd (R := 10 * τ₁) (by positivity) (by linarith) (by simpa only [neg_mul] using hv_supp) ζ hre1 hre2
    refine h.trans ?_
    have h1 := mul_le_mul_of_nonneg_left hL1_v (hC_int_nn r)
    have h2 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-(π * |ζ.im|))).le
    linarith
  · -- Global closed-strip bound on `S̄` for ALL `r ≥ 0`
    intro r ζ hζ
    have hK4_nn : 0 ≤ K4 := by linarith
    have hτ4_le : τ₁ ^ ((4 : ℤ) - r) ≤ τ₁ ^ ((2 : ℤ) - r) := by
      have hdiff : ((4 : ℤ) - r) = ((2 : ℤ) - r) + 2 := by omega
      rw [hdiff, zpow_add₀ hτ₁.ne', show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast]
      exact mul_le_of_le_one_right (zpow_nonneg hτ₁.le _) (pow_le_one₀ hτ₁.le hτ₁_1)
    have h1b_le : c⁻¹ * τ₁ ^ ((-1 : ℤ) - r) ≤ τ₁ ^ ((2 : ℤ) - r) := by
      rw [hc_inv, ← zpow_natCast τ₁ 4, ← zpow_add₀ hτ₁.ne']
      have hdiff : ((4 : ℕ) : ℤ) + ((-1 : ℤ) - r) = ((2 : ℤ) - r) + 1 := by omega
      rw [hdiff, zpow_add₀ hτ₁.ne', zpow_one]
      exact mul_le_of_le_one_right (zpow_nonneg hτ₁.le _) hτ₁_1
    have h1m_le : c⁻¹ * τ₁ ^ ((1 : ℤ) - r) ≤ τ₁ ^ ((2 : ℤ) - r) := by
      rw [hc_inv, ← zpow_natCast τ₁ 4, ← zpow_add₀ hτ₁.ne']
      have hdiff : ((4 : ℕ) : ℤ) + ((1 : ℤ) - r) = ((2 : ℤ) - r) + 3 := by omega
      rw [hdiff, zpow_add₀ hτ₁.ne', show (3 : ℤ) = ((3 : ℕ) : ℤ) by rfl, zpow_natCast]
      exact mul_le_of_le_one_right (zpow_nonneg hτ₁.le _) (pow_le_one₀ hτ₁.le hτ₁_1)
    have hα_le1 : |α| ≤ 1 := hα_le.trans (pow_le_one₀ hτ₁.le hτ₁_1)
    -- Uniform boundary bound `|v^{(r)}(τ)| + |ϑ_D^{(r)}(τ)| ≤ M_r * τ₁^{2-r}`
    set M_v : ℝ := Cv0b r + K4 * Cv0m r + Cv1b r + K4 * Cv1m r + Cva r
    set M_th : ℝ := max (Cth0b r + K4 * Cth0m r + Cth1b r + K4 * Cth1m r + Ctha r)
      (C_tail r * ((CL1_0b + K4 * CL1_0m) + (CL1_1b + K4 * CL1_1m) + CL1_a) * (12 : ℝ) ^ (-(1 + (r : ℤ))))
    have hMv_nn : 0 ≤ M_v := by
      have := hCv0b_nn r; have := hCv0m_nn r; have := hCv1b_nn r; have := hCv1m_nn r; have := hCva_nn r
      positivity
    have hMth_nn : 0 ≤ M_th := le_trans (by
      have := hCth0b_nn r; have := hCth0m_nn r; have := hCth1b_nn r; have := hCth1m_nn r; have := hCtha_nn r
      positivity) (le_max_left _ _)
    refine norm_iteratedDeriv_stripCompGExt_le r hv_cd (R := 10 * τ₁) (by positivity)
      (mul_nonneg (add_nonneg hMv_nn hMth_nn) (zpow_nonneg hτ₁.le _)) (by simpa only [neg_mul] using hv_supp) (fun τ => ?_) hζ
    -- Bound `|v^{(r)}(τ)| ≤ M_v * τ₁^{2-r}`
    have hv_bd_τ : |iteratedDeriv r (vTotal kind K4 c α τ₁) τ| ≤ M_v * τ₁ ^ ((2 : ℤ) - r) := by
      have hcd0 : ContDiffAt ℝ (r : WithTop ℕ∞) (v0 kind K4 τ₁) τ := hv0_cd.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
      have hcd1 : ContDiffAt ℝ (r : WithTop ℕ∞) (v1 kind K4 c τ₁) τ := hv1_cd.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
      have hcd01 : ContDiffAt ℝ (r : WithTop ℕ∞) (v0 kind K4 τ₁ + v1 kind K4 c τ₁) τ := hcd0.add hcd1
      have hcda : ContDiffAt ℝ (r : WithTop ℕ∞) (vAlpha α τ₁) τ := ha0_cd.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
      have hcdb0 : ContDiffAt ℝ (r : WithTop ℕ∞) (v0Base kind τ₁) τ := hb0_cd.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
      have hcdm0 : ContDiffAt ℝ (r : WithTop ℕ∞) (fun s => K4 * v0Marg τ₁ s) τ :=
        (contDiff_const.mul hm0_cd).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
      have hcdb1 : ContDiffAt ℝ (r : WithTop ℕ∞) (v1Base kind c τ₁) τ := hb1_cd.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
      have hcdm1 : ContDiffAt ℝ (r : WithTop ℕ∞) (fun s => K4 * v1Marg c τ₁ s) τ :=
        (contDiff_const.mul hm1_cd).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
      have heq_v : iteratedDeriv r (vTotal kind K4 c α τ₁) τ =
          (iteratedDeriv r (v0Base kind τ₁) τ + K4 * iteratedDeriv r (v0Marg τ₁) τ) +
          (iteratedDeriv r (v1Base kind c τ₁) τ + K4 * iteratedDeriv r (v1Marg c τ₁) τ) +
          iteratedDeriv r (vAlpha α τ₁) τ := by
        change iteratedDeriv r ((v0 kind K4 τ₁ + v1 kind K4 c τ₁) + vAlpha α τ₁) τ = _
        rw [iteratedDeriv_add hcd01 hcda, iteratedDeriv_add hcd0 hcd1]
        have e0 : iteratedDeriv r (v0 kind K4 τ₁) τ =
            iteratedDeriv r (v0Base kind τ₁) τ + K4 * iteratedDeriv r (v0Marg τ₁) τ := by
          change iteratedDeriv r (v0Base kind τ₁ + fun s => K4 * v0Marg τ₁ s) τ = _
          rw [iteratedDeriv_add hcdb0 hcdm0, iteratedDeriv_const_mul_field]
        have e1 : iteratedDeriv r (v1 kind K4 c τ₁) τ =
            iteratedDeriv r (v1Base kind c τ₁) τ + K4 * iteratedDeriv r (v1Marg c τ₁) τ := by
          change iteratedDeriv r (v1Base kind c τ₁ + fun s => K4 * v1Marg c τ₁ s) τ = _
          rw [iteratedDeriv_add hcdb1 hcdm1, iteratedDeriv_const_mul_field]
        rw [e0, e1]
      rw [heq_v]
      obtain ⟨d1, d2, d3, d4, d5⟩ := hderivs r τ
      have htri : |(iteratedDeriv r (v0Base kind τ₁) τ + K4 * iteratedDeriv r (v0Marg τ₁) τ) +
            (iteratedDeriv r (v1Base kind c τ₁) τ + K4 * iteratedDeriv r (v1Marg c τ₁) τ) +
            iteratedDeriv r (vAlpha α τ₁) τ| ≤
          |iteratedDeriv r (v0Base kind τ₁) τ| + K4 * |iteratedDeriv r (v0Marg τ₁) τ| +
          |iteratedDeriv r (v1Base kind c τ₁) τ| + K4 * |iteratedDeriv r (v1Marg c τ₁) τ| +
          |iteratedDeriv r (vAlpha α τ₁) τ| := by
        have a1 := abs_add_le ((iteratedDeriv r (v0Base kind τ₁) τ + K4 * iteratedDeriv r (v0Marg τ₁) τ) +
          (iteratedDeriv r (v1Base kind c τ₁) τ + K4 * iteratedDeriv r (v1Marg c τ₁) τ)) (iteratedDeriv r (vAlpha α τ₁) τ)
        have a2 := abs_add_le (iteratedDeriv r (v0Base kind τ₁) τ + K4 * iteratedDeriv r (v0Marg τ₁) τ)
          (iteratedDeriv r (v1Base kind c τ₁) τ + K4 * iteratedDeriv r (v1Marg c τ₁) τ)
        have a3 := abs_add_le (iteratedDeriv r (v0Base kind τ₁) τ) (K4 * iteratedDeriv r (v0Marg τ₁) τ)
        have a4 := abs_add_le (iteratedDeriv r (v1Base kind c τ₁) τ) (K4 * iteratedDeriv r (v1Marg c τ₁) τ)
        rw [abs_mul, abs_of_nonneg hK4_nn] at a3 a4
        linarith
      have h2' : |iteratedDeriv r (v0Marg τ₁) τ| ≤ Cv0m r * τ₁ ^ ((2 : ℤ) - r) :=
        d2.trans (mul_le_mul_of_nonneg_left hτ4_le (hCv0m_nn r))
      have h3' : |iteratedDeriv r (vAlpha α τ₁) τ| ≤ Cva r * τ₁ ^ ((2 : ℤ) - r) :=
        d3.trans (by
          have h1 := mul_le_mul_of_nonneg_left hα_le1 (hCva_nn r)
          rw [mul_one] at h1
          exact mul_le_mul_of_nonneg_right h1 (zpow_nonneg hτ₁.le _))
      have h4' : |iteratedDeriv r (v1Base kind c τ₁) τ| ≤ Cv1b r * τ₁ ^ ((2 : ℤ) - r) :=
        d4.trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h1b_le (hCv1b_nn r))
      have h5' : |iteratedDeriv r (v1Marg c τ₁) τ| ≤ Cv1m r * τ₁ ^ ((2 : ℤ) - r) :=
        d5.trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h1m_le (hCv1m_nn r))
      have h2m := mul_le_mul_of_nonneg_left h2' hK4_nn
      have h5m := mul_le_mul_of_nonneg_left h5' hK4_nn
      dsimp only [M_v]
      linarith
    -- Bound `|ϑ_D^{(r)}(τ)| ≤ M_th * τ₁^{2-r}` (split `|τ| ≤ 12 τ₁` vs `12 τ₁ ≤ |τ|`)
    have hθ_bd_τ : |iteratedDeriv r (fctThetaD (vTotal kind K4 c α τ₁)) τ| ≤ M_th * τ₁ ^ ((2 : ℤ) - r) := by
      rcases le_or_gt |τ| (12 * τ₁) with hle | hgt
      · -- Inner region `|τ| ≤ 12 τ₁`
        have hθ1b_cd := contDiff_fctThetaD hb1_cd hb1_cs
        have hθ1m_cd := contDiff_fctThetaD hm1_cd hm1_cs
        have hθ0_cd := contDiff_fctThetaD hv0_cd hv0_cs
        have hθ1_cd := contDiff_fctThetaD hv1_cd hv1_cs
        have heq_θ : iteratedDeriv r (fctThetaD (vTotal kind K4 c α τ₁)) τ =
            (iteratedDeriv r (fctThetaD (v0Base kind τ₁)) τ + K4 * iteratedDeriv r (fctThetaD (v0Marg τ₁)) τ) +
            (iteratedDeriv r (fctThetaD (v1Base kind c τ₁)) τ + K4 * iteratedDeriv r (fctThetaD (v1Marg c τ₁)) τ) +
            iteratedDeriv r (fctThetaD (vAlpha α τ₁)) τ := by
          rw [hθ_eq]
          have c0 : ContDiffAt ℝ (r : WithTop ℕ∞) (fctThetaD (v0 kind K4 τ₁)) τ := hθ0_cd.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
          have c1 : ContDiffAt ℝ (r : WithTop ℕ∞) (fctThetaD (v1 kind K4 c τ₁)) τ := hθ1_cd.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
          have c01 : ContDiffAt ℝ (r : WithTop ℕ∞) (fctThetaD (v0 kind K4 τ₁) + fctThetaD (v1 kind K4 c τ₁)) τ := c0.add c1
          have ca : ContDiffAt ℝ (r : WithTop ℕ∞) (fctThetaD (vAlpha α τ₁)) τ := hθa_cd.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
          change iteratedDeriv r ((fctThetaD (v0 kind K4 τ₁) + fctThetaD (v1 kind K4 c τ₁)) + fctThetaD (vAlpha α τ₁)) τ = _
          rw [iteratedDeriv_add c01 ca, iteratedDeriv_add c0 c1]
          have e0 : iteratedDeriv r (fctThetaD (v0 kind K4 τ₁)) τ =
              iteratedDeriv r (fctThetaD (v0Base kind τ₁)) τ + K4 * iteratedDeriv r (fctThetaD (v0Marg τ₁)) τ := by
            rw [hθ0_eq]
            change iteratedDeriv r (fctThetaD (v0Base kind τ₁) + fun s => K4 * fctThetaD (v0Marg τ₁) s) τ = _
            rw [iteratedDeriv_add (hθ0b_cd.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))
              ((contDiff_const.mul hθ0m_cd).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)),
              iteratedDeriv_const_mul_field]
          have e1 : iteratedDeriv r (fctThetaD (v1 kind K4 c τ₁)) τ =
              iteratedDeriv r (fctThetaD (v1Base kind c τ₁)) τ + K4 * iteratedDeriv r (fctThetaD (v1Marg c τ₁)) τ := by
            rw [hθ1_eq]
            change iteratedDeriv r (fctThetaD (v1Base kind c τ₁) + fun s => K4 * fctThetaD (v1Marg c τ₁) s) τ = _
            rw [iteratedDeriv_add (hθ1b_cd.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))
              ((contDiff_const.mul hθ1m_cd).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)),
              iteratedDeriv_const_mul_field]
          rw [e0, e1]
        rw [heq_θ]
        obtain ⟨t1, t2, t3, t4, t5⟩ := hth_in r τ hle
        have hmin : min (1 : ℝ) ((|τ| / τ₁) ^ (11 - r)) ≤ 1 := min_le_left _ _
        have t1' : |iteratedDeriv r (fctThetaD (v0Base kind τ₁)) τ| ≤ Cth0b r * τ₁ ^ ((2 : ℤ) - r) :=
          t1.trans (mul_le_of_le_one_right (mul_nonneg (hCth0b_nn r) (zpow_nonneg hτ₁.le _)) hmin)
        have t2' : |iteratedDeriv r (fctThetaD (v0Marg τ₁)) τ| ≤ Cth0m r * τ₁ ^ ((2 : ℤ) - r) :=
          (t2.trans (mul_le_of_le_one_right (mul_nonneg (hCth0m_nn r) (zpow_nonneg hτ₁.le _)) hmin)).trans
            (mul_le_mul_of_nonneg_left hτ4_le (hCth0m_nn r))
        have t3' : |iteratedDeriv r (fctThetaD (vAlpha α τ₁)) τ| ≤ Ctha r * τ₁ ^ ((2 : ℤ) - r) :=
          (t3.trans (mul_le_of_le_one_right (by have := hCtha_nn r; positivity) hmin)).trans (by
            have h1 := mul_le_mul_of_nonneg_left hα_le1 (hCtha_nn r)
            rw [mul_one] at h1
            exact mul_le_mul_of_nonneg_right h1 (zpow_nonneg hτ₁.le _))
        have t4' : |iteratedDeriv r (fctThetaD (v1Base kind c τ₁)) τ| ≤ Cth1b r * τ₁ ^ ((2 : ℤ) - r) :=
          (t4.trans (mul_le_of_le_one_right (by have := hCth1b_nn r; positivity) hmin)).trans (by
            rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h1b_le (hCth1b_nn r))
        have t5' : |iteratedDeriv r (fctThetaD (v1Marg c τ₁)) τ| ≤ Cth1m r * τ₁ ^ ((2 : ℤ) - r) :=
          (t5.trans (mul_le_of_le_one_right (by have := hCth1m_nn r; positivity) hmin)).trans (by
            rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h1m_le (hCth1m_nn r))
        have htri : |(iteratedDeriv r (fctThetaD (v0Base kind τ₁)) τ + K4 * iteratedDeriv r (fctThetaD (v0Marg τ₁)) τ) +
              (iteratedDeriv r (fctThetaD (v1Base kind c τ₁)) τ + K4 * iteratedDeriv r (fctThetaD (v1Marg c τ₁)) τ) +
              iteratedDeriv r (fctThetaD (vAlpha α τ₁)) τ| ≤
            (Cth0b r + K4 * Cth0m r + Cth1b r + K4 * Cth1m r + Ctha r) * τ₁ ^ ((2 : ℤ) - r) := by
          have a1 := abs_add_le ((iteratedDeriv r (fctThetaD (v0Base kind τ₁)) τ + K4 * iteratedDeriv r (fctThetaD (v0Marg τ₁)) τ) +
            (iteratedDeriv r (fctThetaD (v1Base kind c τ₁)) τ + K4 * iteratedDeriv r (fctThetaD (v1Marg c τ₁)) τ))
            (iteratedDeriv r (fctThetaD (vAlpha α τ₁)) τ)
          have a2 := abs_add_le (iteratedDeriv r (fctThetaD (v0Base kind τ₁)) τ + K4 * iteratedDeriv r (fctThetaD (v0Marg τ₁)) τ)
            (iteratedDeriv r (fctThetaD (v1Base kind c τ₁)) τ + K4 * iteratedDeriv r (fctThetaD (v1Marg c τ₁)) τ)
          have a3 := abs_add_le (iteratedDeriv r (fctThetaD (v0Base kind τ₁)) τ) (K4 * iteratedDeriv r (fctThetaD (v0Marg τ₁)) τ)
          have a4 := abs_add_le (iteratedDeriv r (fctThetaD (v1Base kind c τ₁)) τ) (K4 * iteratedDeriv r (fctThetaD (v1Marg c τ₁)) τ)
          rw [abs_mul, abs_of_nonneg hK4_nn] at a3 a4
          have t2m := mul_le_mul_of_nonneg_left t2' hK4_nn
          have t5m := mul_le_mul_of_nonneg_left t5' hK4_nn
          linarith
        exact htri.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (zpow_nonneg hτ₁.le _))
      · -- Tail region `12 τ₁ < |τ|`
        have h := hC_tail_bd r hv_cd hτ₁ hτ₁_20 hv_supp τ hgt.le
        have hexp1 : Real.exp (-(π / 2) * |τ|) ≤ 1 :=
          Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith [Real.pi_pos]) (abs_nonneg τ))
        have hpow_le : |τ| ^ (-(1 + (r : ℤ))) ≤ (12 * τ₁) ^ (-(1 + (r : ℤ))) := by
          rw [zpow_neg, zpow_neg]
          refine inv_anti₀ (by positivity) ?_
          rw [show (1 + (r : ℤ)) = ((1 + r : ℕ) : ℤ) by omega, zpow_natCast, zpow_natCast]
          exact pow_le_pow_left₀ (by positivity) hgt.le (1 + r)
        have hpow_split : (12 * τ₁) ^ (-(1 + (r : ℤ))) = (12 : ℝ) ^ (-(1 + (r : ℤ))) * τ₁ ^ (-(1 + (r : ℤ))) :=
          mul_zpow 12 τ₁ _
        have hpow_comb : τ₁ ^ 3 * τ₁ ^ (-(1 + (r : ℤ))) = τ₁ ^ ((2 : ℤ) - r) := by
          rw [← zpow_natCast τ₁ 3, ← zpow_add₀ hτ₁.ne']; congr 1; omega
        have h1 : C_tail r * (∫ s : ℝ, |vTotal kind K4 c α τ₁ s|) * |τ| ^ (-(1 + (r : ℤ))) * Real.exp (-(π / 2) * |τ|) ≤
            C_tail r * (((CL1_0b + K4 * CL1_0m) + (CL1_1b + K4 * CL1_1m) + CL1_a) * τ₁ ^ 3) *
              ((12 : ℝ) ^ (-(1 + (r : ℤ))) * τ₁ ^ (-(1 + (r : ℤ)))) * 1 := by
          have ha : C_tail r * (∫ s : ℝ, |vTotal kind K4 c α τ₁ s|) ≤
              C_tail r * (((CL1_0b + K4 * CL1_0m) + (CL1_1b + K4 * CL1_1m) + CL1_a) * τ₁ ^ 3) :=
            mul_le_mul_of_nonneg_left hL1_v (hC_tail_nn r)
          have hb : |τ| ^ (-(1 + (r : ℤ))) ≤ (12 : ℝ) ^ (-(1 + (r : ℤ))) * τ₁ ^ (-(1 + (r : ℤ))) := by
            rwa [← hpow_split]
          have hc' : C_tail r * (∫ s : ℝ, |vTotal kind K4 c α τ₁ s|) * |τ| ^ (-(1 + (r : ℤ))) ≤
              C_tail r * (((CL1_0b + K4 * CL1_0m) + (CL1_1b + K4 * CL1_1m) + CL1_a) * τ₁ ^ 3) *
                ((12 : ℝ) ^ (-(1 + (r : ℤ))) * τ₁ ^ (-(1 + (r : ℤ)))) :=
            mul_le_mul ha hb (zpow_nonneg (abs_nonneg τ) _) (by have := hC_tail_nn r; positivity)
          exact mul_le_mul hc' hexp1 (Real.exp_pos _).le (by have := hC_tail_nn r; positivity)
        have h2 : C_tail r * (((CL1_0b + K4 * CL1_0m) + (CL1_1b + K4 * CL1_1m) + CL1_a) * τ₁ ^ 3) *
              ((12 : ℝ) ^ (-(1 + (r : ℤ))) * τ₁ ^ (-(1 + (r : ℤ)))) * 1 =
            (C_tail r * ((CL1_0b + K4 * CL1_0m) + (CL1_1b + K4 * CL1_1m) + CL1_a) *
              (12 : ℝ) ^ (-(1 + (r : ℤ)))) * τ₁ ^ ((2 : ℤ) - r) := by
          rw [mul_one, ← hpow_comb]; ring
        exact (h.trans h1).trans (h2.le.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (zpow_nonneg hτ₁.le _)))
    linarith
  · -- Normalization `D(0) = D(1) = 1`
    have hv0_val : vTotal kind K4 c α τ₁ 0 = 0 := by
      simp [vTotal, v0, v1, hb0_0, hm0_0, hb1_0, hm1_0, ha0_0]
    have hθ0_val : fctThetaD (vTotal kind K4 c α τ₁) 0 = 0 := by
      have h := fctThetaD_odd hv_even 0
      simp only [neg_zero] at h; linarith
    have hg0 : stripCompGExt (vTotal kind K4 c α τ₁) 0 = 0 := by
      have h := stripCompGExt_left (vTotal kind K4 c α τ₁) 0
      simp only [Complex.ofReal_zero, zero_mul, hv0_val, hθ0_val, mul_zero, add_zero] at h
      exact h
    have hg1 : stripCompGExt (vTotal kind K4 c α τ₁) 1 = 0 := by
      have h := stripCompGExt_right (vTotal kind K4 c α τ₁) 0
      simp only [Complex.ofReal_zero, zero_mul, add_zero, hv0_val, hθ0_val, mul_zero, sub_zero] at h
      exact h
    exact ⟨hg0, hg1, by rw [hg0, Complex.exp_zero], by rw [hg1, Complex.exp_zero]⟩

/-- info: 'FormalResearch.SignUncertainty.FctCompD.fct_comp_D_part1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.FctCompD.fct_comp_D_part1

end FormalResearch.SignUncertainty.FctCompD
