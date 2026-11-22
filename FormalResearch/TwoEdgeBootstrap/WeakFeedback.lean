module

public import FormalResearch.TwoEdgeBootstrap.Bootstrap

/-!
# Vacuum Error and Weak Feedback Extension (Theorem TE.2(5))

Source: `CFT/common/two_edge_bootstrap.tex` (Theorem `TE.2(5)`, PR 240 `75b8b1b60`).

Extends `FormalResearch.TwoEdgeBootstrap.Bootstrap` to allow a genuine nonzero vacuum error
`0 ≤ η_vac ≤ C_vac * c ^ (-(1 / 3 : ℝ))` in the line estimate `(TE.5)` (without requiring the
`η_vac = 0` bound `hI_line`), general node slope `C_N ≥ 0` and single-`θ` terminal lower bound
(`a_N > 0`, `0 < θ ≤ 1 / 2`) in `(TE.6)`, and weak polynomial/threshold feedback
`L ≤ C_fb * (c ^ (1 / 3 : ℝ) * (B_1 + B_2) + Υ_c)` (`1 ≤ Υ_c`):

* `BootstrapWeakCore`: standalone Stage B package for Theorem `TE.2(5)` allowing `0 < η_vac`.
* `teb_weak_part1`: band/tail mass bound `B_1 + B_2 ≤ C_X * (1 + Real.log L) * c ^ (-(1 / 3 : ℝ))`.
* `teb_weak_K_log_bound`: unclosed displacement bound `K ≤ C_K * (1 + Real.log L)` without feedback.
* `teb_weak_feedback_closure`: weak feedback closure `L ≤ C' * Υ_c` and `K ≤ C'' * (1 + Real.log Υ_c)`.
* `teb_hb_single_theta_aN_pos`: explicit `a_N = κ_* / (4 * w_m^*) > 0` derivation from the
  Hermite–Biehler single-`θ` condition `2 * θ * C_1 * W_inv_sum ≤ κ_* / (4 * w_m^*)`.
* `bootstrapWeakCore_nonvacuous`: unconditional witness with strict `0 < η_vac = C_vac * c^{-1/3}`
  for all `c ≥ 2` and `Υ_c ≥ 1`.
-/

@[expose] public section

open scoped Real

namespace FormalResearch.TwoEdgeBootstrap

open FormalResearch.Asymptotics

/-! ### Algebraic Weak-Feedback Closure -/

section WeakAlgebraic

/-- Weak-feedback fixed-point constant `L_♯^weak(C_*) := 2 C_* (1 + log(2 C_*))`. -/
noncomputable def tebWeakScale (Cstar : ℝ) : ℝ :=
  2 * Cstar * (1 + Real.log (2 * Cstar))

lemma one_le_tebWeakScale {Cstar : ℝ} (hC : 1 ≤ Cstar) : 1 ≤ tebWeakScale Cstar := by
  unfold tebWeakScale
  have hlog : 0 ≤ Real.log (2 * Cstar) := Real.log_nonneg (by linarith)
  nlinarith

/-- If `1 ≤ C_*`, `1 ≤ Υ_c`, `1 ≤ L`, and `L ≤ C_* * (Υ_c + log L)`, then
`L ≤ 2 * C_* * (1 + log(2 * C_*)) * Υ_c`. -/
theorem log_weak_feedback_bound {Cstar Upsilon L : ℝ} (hC : 1 ≤ Cstar) (hU : 1 ≤ Upsilon)
    (hL : 1 ≤ L) (hle : L ≤ Cstar * (Upsilon + Real.log L)) :
    L ≤ tebWeakScale Cstar * Upsilon := by
  have hC_pos : 0 < Cstar := by linarith
  have hL_pos : 0 < L := by linarith
  have h2C_pos : 0 < 2 * Cstar := by linarith
  have hlog_div := Real.log_le_sub_one_of_pos (div_pos hL_pos h2C_pos)
  rw [Real.log_div hL_pos.ne' h2C_pos.ne'] at hlog_div
  have hlogL : Real.log L ≤ Real.log (2 * Cstar) + L / (2 * Cstar) - 1 := by linarith
  have h1 : L ≤ Cstar * (Upsilon + (Real.log (2 * Cstar) + L / (2 * Cstar) - 1)) :=
    hle.trans (mul_le_mul_of_nonneg_left (by linarith) hC_pos.le)
  have h2 : Cstar * (Upsilon + (Real.log (2 * Cstar) + L / (2 * Cstar) - 1)) =
      Cstar * (Upsilon + Real.log (2 * Cstar) - 1) + L / 2 := by
    field_simp [hC_pos.ne']; ring
  have h3 : L ≤ 2 * Cstar * (Upsilon + Real.log (2 * Cstar)) := by linarith
  have hlog2C_nn : 0 ≤ Real.log (2 * Cstar) := Real.log_nonneg (by linarith)
  have h4 : Upsilon + Real.log (2 * Cstar) ≤ (1 + Real.log (2 * Cstar)) * Upsilon := by nlinarith
  calc L ≤ 2 * Cstar * (Upsilon + Real.log (2 * Cstar)) := h3
    _ ≤ 2 * Cstar * ((1 + Real.log (2 * Cstar)) * Upsilon) :=
        mul_le_mul_of_nonneg_left h4 (by linarith)
    _ = tebWeakScale Cstar * Upsilon := by unfold tebWeakScale; ring

end WeakAlgebraic

/-! ### Hermite–Biehler Single-`θ` Node Slope Check -/

/-- Explicit derivation of `a_N = κ_* / (4 w_m^*) > 0` in Theorem `TE.2(5)` from
`w_m ∈ [3/4, 5/4]`, `w_j ≤ 5/4` for `j < m`, and `2 θ C₁ W_inv_sum ≤ κ_* / (4 w_m^*)`
(giving `(3/4) κ_* / w_m^* - (5/2) θ C₁ W_inv_sum ≥ (7/16) κ_* / w_m^* ≥ κ_* / (4 w_m^*)`). -/
theorem teb_hb_single_theta_aN_pos {θ C_1 κ_star w_m W_inv_sum : ℝ}
    (_hC1 : 0 < C_1) (hκ : 0 < κ_star) (hwm : 0 < w_m) (_hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 2)
    (_hW_nn : 0 ≤ W_inv_sum)
    (hcond : 2 * θ * C_1 * W_inv_sum ≤ κ_star / (4 * w_m)) :
    0 < κ_star / (4 * w_m) ∧
      κ_star / (4 * w_m) ≤ (3 / 4 : ℝ) * (2 * (1 - θ) * κ_star) / w_m -
        (5 / 4 : ℝ) * (2 * θ * C_1 * W_inv_sum) := by
  have ha_pos : 0 < κ_star / (4 * w_m) := by positivity
  have h1θ : 1 ≤ 2 * (1 - θ) := by linarith
  have hterm1 : (3 / 4 : ℝ) * κ_star / w_m ≤ (3 / 4 : ℝ) * (2 * (1 - θ) * κ_star) / w_m := by
    have : κ_star ≤ 2 * (1 - θ) * κ_star := le_mul_of_one_le_left hκ.le h1θ
    gcongr
  have hterm2 : (5 / 4 : ℝ) * (2 * θ * C_1 * W_inv_sum) ≤ (5 / 16 : ℝ) * (κ_star / w_m) := by
    calc (5 / 4 : ℝ) * (2 * θ * C_1 * W_inv_sum)
        ≤ (5 / 4 : ℝ) * (κ_star / (4 * w_m)) := by gcongr
      _ = (5 / 16 : ℝ) * (κ_star / w_m) := by ring
  refine ⟨ha_pos, ?_⟩
  linarith [show (3 / 4 : ℝ) * κ_star / w_m = (12 / 16 : ℝ) * (κ_star / w_m) by ring,
    show κ_star / (4 * w_m) = (4 / 16 : ℝ) * (κ_star / w_m) by ring]

/-! ### Packaged Stage B Instance and Theorems for `TE.2(5)` -/

/-- Standalone Stage B data for `CFT/common/two_edge_bootstrap.tex` Theorem `TE.2(5)`:
mirrors the Stage B core bounds with an additive vacuum error `0 ≤ η_vac ≤ C_vac c^{-1/3}`
directly in `hI_line_vac` (without requiring `η_vac = 0`), general node slope `C_N ≥ 0`,
and a fixed-`θ` lower bound at `ℓ = θ x_tilde` for `k = max k₀ ⌈log L⌉_+`. -/
structure BootstrapWeakCore (P : BootstrapParams) where
  c : ℝ
  R : ℝ
  a : ℝ
  B_1 : ℝ
  B_2 : ℝ
  L : ℝ
  x_tilde : ℝ
  r_inf : ℝ
  C_err : ℝ
  hc : 2 ≤ c
  ha_lb : P.b * c ^ (1 / 3 : ℝ) ≤ a
  ha_sq : a ^ 2 = R
  hR_ub : R ≤ 2 * P.b ^ 2 * c ^ (2 / 3 : ℝ) + 1
  hB1 : 0 ≤ B_1
  hB2 : 0 ≤ B_2
  hL_lb : 1 ≤ L
  hL_ub : L ≤ P.C_L * c ^ P.γ
  hx_pos : 0 < x_tilde
  hx_ub : x_tilde ≤ min P.δ_star (min P.η_0 1)
  hr_inf_nn : 0 ≤ r_inf
  hr_inf_ub : r_inf ≤ P.C_0 * c ^ (1 / 3 : ℝ) * Real.exp (-P.κ * c)
  hC_err_nn : 0 ≤ C_err
  hC_err_ub : C_err ≤ P.C_0
  B_1k : ℕ → ℝ
  B_2' : ℕ → ℝ
  P_nodes : ℕ → ℝ → ℝ
  I_line : ℕ → ℝ → ℝ
  Arc_cov : ℕ → ℝ → ℝ
  Arc_unc : ℝ
  hB1k_nn : ∀ k : ℕ, P.k_0 ≤ k → (k : ℝ) ≤ R / 5 → 0 ≤ B_1k k
  hB2'_nn : ∀ k : ℕ, P.k_0 ≤ k → (k : ℝ) ≤ R / 5 → 0 ≤ B_2' k
  hB_sum : ∀ k : ℕ, P.k_0 ≤ k → (k : ℝ) ≤ R / 5 → B_1 + B_2 ≤ B_1k k + B_2' k
  hP_le : ∀ k : ℕ, ∀ ℓ : ℝ, P.k_0 ≤ k → (k : ℝ) ≤ R / 5 →
    ℓ ∈ Set.Icc (P.D_1 * c ^ (-(1 / 3 : ℝ))) (min P.δ_star (min P.η_0 1)) →
    P_nodes k ℓ ≤ I_line k ℓ + Arc_cov k ℓ + Arc_unc
  hArc_cov : ∀ k : ℕ, ∀ ℓ : ℝ, P.k_0 ≤ k → (k : ℝ) ≤ R / 5 →
    ℓ ∈ Set.Icc (P.D_1 * c ^ (-(1 / 3 : ℝ))) (min P.δ_star (min P.η_0 1)) →
    Arc_cov k ℓ ≤ P.C_a * L * a⁻¹ *
      ((2 : ℝ) ^ (k + 1) * Real.Gamma ((k : ℝ) + 1 / 2) *
        (Real.pi / (4 * ℓ * a)) ^ ((k : ℝ) + 1 / 2))
  hArc_unc : Arc_unc ≤ P.C_unc * c ^ (-(3 / 8 : ℝ))
  C_vac : ℝ
  η_vac : ℝ
  C_N : ℝ
  θ : ℝ
  a_N : ℝ
  hCvac : 0 ≤ C_vac
  hη_vac_nn : 0 ≤ η_vac
  hη_vac_ub : η_vac ≤ C_vac * c ^ (-(1 / 3 : ℝ))
  hCN : 0 ≤ C_N
  hθ_pos : 0 < θ
  hθ_half : θ ≤ 1 / 2
  haN_pos : 0 < a_N
  hI_line_vac : ∀ k : ℕ, ∀ ℓ : ℝ, P.k_0 ≤ k → (k : ℝ) ≤ R / 5 →
    ℓ ∈ Set.Icc (P.D_1 * c ^ (-(1 / 3 : ℝ))) (min P.δ_star (min P.η_0 1)) →
    I_line k ℓ ≤ -(63 / 100 : ℝ) * B_1k k - B_2' k + η_vac +
      P.C_a * ((k : ℝ) + 1) / R + R * r_inf + C_err * c * Real.exp (-P.κ * c)
  hP_nodes_lb : ∀ k : ℕ, ∀ ℓ : ℝ, P.k_0 ≤ k → (k : ℝ) ≤ R / 5 →
    ℓ ∈ Set.Icc (P.D_1 * c ^ (-(1 / 3 : ℝ))) (min P.δ_star (min P.η_0 1)) →
    -C_N * ℓ - P.C_α * R ^ (3 / 2 : ℝ) * r_inf ≤ P_nodes k ℓ
  hP_theta_lb : ∀ k : ℕ, P.k_0 ≤ k → (k : ℝ) ≤ R / 5 →
    θ * x_tilde ∈ Set.Icc (P.D_1 * c ^ (-(1 / 3 : ℝ))) (min P.δ_star (min P.η_0 1)) →
    a_N * x_tilde - P.C_α * R ^ (3 / 2 : ℝ) * r_inf ≤ P_nodes k (θ * x_tilde)

/-- Explicit `C_X` constant for `TE.2(5)` including `C_vac`. -/
noncomputable def tebCXWeak (P : BootstrapParams) (C_N C_vac : ℝ) : ℝ :=
  (100 / 63 : ℝ) * (C_N * tebLambda0 P * (P.k_0 : ℝ) +
    2 * P.C_a * (P.k_0 : ℝ) / P.b ^ 2 + 4 * P.C_a / P.b + P.C_unc + C_vac + 1)

lemma tebCXWeak_pos (P : BootstrapParams) {C_N C_vac : ℝ} (hCN : 0 ≤ C_N) (hCvac : 0 ≤ C_vac) :
    0 < tebCXWeak P C_N C_vac := by
  unfold tebCXWeak
  have hlam := (tebLambda0_pos P).le; have hCa := P.hCa; have hCunc := P.hCunc; have hb := P.hb
  positivity

/-- **Theorem TE.2(5)** part `(1)` with vacuum error `η_vac ≤ C_vac c^{-1/3}`:
`B₁ + B₂ ≤ C_X^{weak} (1 + log L) c^{-1/3}` for `c ≥ tebC2 P`. -/
theorem teb_weak_part1 (P : BootstrapParams) (W : BootstrapWeakCore P) (hc : tebC2 P ≤ W.c) :
    W.B_1 + W.B_2 ≤
      tebCXWeak P W.C_N W.C_vac * (1 + Real.log W.L) * W.c ^ (-(1 / 3 : ℝ)) := by
  set k₁ := tebK1 P W.L
  set lam0 := tebLambda0 P
  set ℓ := lam0 * (k₁ : ℝ) * W.c ^ (-(1 / 3 : ℝ))
  have hc_pos : 0 < W.c := by linarith [W.hc]
  have hc1 : 1 ≤ W.c := by linarith [W.hc]
  have h1log_ge1 : 1 ≤ 1 + Real.log W.L := by linarith [Real.log_nonneg W.hL_lb]
  have hR_ge : P.b ^ 2 * W.c ^ (2 / 3 : ℝ) ≤ W.R := by
    have hc_nn : 0 ≤ W.c := hc_pos.le
    have hsq : (P.b * W.c ^ (1 / 3 : ℝ)) ^ 2 ≤ W.a ^ 2 := by
      nlinarith [W.ha_lb, mul_nonneg P.hb.le (Real.rpow_nonneg hc_nn (1 / 3 : ℝ))]
    rw [W.ha_sq, mul_pow, ← Real.rpow_natCast (W.c ^ (1 / 3 : ℝ)) 2, ← Real.rpow_mul hc_nn] at hsq
    norm_num at hsq; exact hsq
  have h_large := tebCThresh_spec P ((le_max_right (2 : ℝ) _).trans hc) W.hL_lb W.hL_ub hR_ge
    W.hR_ub W.hr_inf_nn W.hr_inf_ub W.hC_err_ub
  obtain ⟨hℓ_mem, hk1_le_R5, h_exp_abs⟩ := h_large
  have hk1_ge : P.k_0 ≤ k₁ := le_max_left _ _
  have hk1_pos : 1 ≤ k₁ := P.hk0.trans hk1_ge
  have hlam0_pos : 0 < lam0 := tebLambda0_pos P
  have hℓ_pos : 0 < ℓ :=
    mul_pos (mul_pos hlam0_pos (Nat.cast_pos.mpr hk1_pos)) (Real.rpow_pos_of_pos hc_pos _)
  have ha_pos : 0 < W.a := by
    have : 0 < P.b * W.c ^ (1 / 3 : ℝ) := mul_pos P.hb (Real.rpow_pos_of_pos hc_pos _)
    linarith [W.ha_lb]
  have ha_inv_le : W.a⁻¹ ≤ P.b⁻¹ * W.c ^ (-(1 / 3 : ℝ)) := by
    have hp : 0 < P.b * W.c ^ (1 / 3 : ℝ) := mul_pos P.hb (Real.rpow_pos_of_pos hc_pos _)
    calc W.a⁻¹ ≤ (P.b * W.c ^ (1 / 3 : ℝ))⁻¹ := inv_anti₀ hp W.ha_lb
      _ = P.b⁻¹ * W.c ^ (-(1 / 3 : ℝ)) := by rw [mul_inv, ← Real.rpow_neg hc_pos.le]
  have hR_inv_le : W.R⁻¹ ≤ (P.b ^ 2)⁻¹ * W.c ^ (-(1 / 3 : ℝ)) := by
    have hR_lb13 : P.b ^ 2 * W.c ^ (1 / 3 : ℝ) ≤ W.R :=
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num))
        (sq_nonneg P.b)).trans hR_ge
    have hb := P.hb
    calc W.R⁻¹ ≤ (P.b ^ 2 * W.c ^ (1 / 3 : ℝ))⁻¹ := inv_anti₀ (by positivity) hR_lb13
      _ = (P.b ^ 2)⁻¹ * W.c ^ (-(1 / 3 : ℝ)) := by rw [mul_inv, ← Real.rpow_neg hc_pos.le]
  have hla : (Real.pi / 2) * (k₁ : ℝ) ≤ ℓ * W.a := by
    have hlam0_lb : Real.pi / (2 * P.b) ≤ lam0 := by
      dsimp [lam0, tebLambda0]
      split_ifs with h0
      · exact absurd h0 (Nat.ne_of_gt P.hk0)
      · exact le_max_left _ _
    have hc_inv : W.c ^ (-(1 / 3 : ℝ)) * W.c ^ (1 / 3 : ℝ) = 1 := by
      rw [← Real.rpow_add hc_pos, neg_add_cancel, Real.rpow_zero]
    have hlam_nn : 0 ≤ lam0 * (k₁ : ℝ) * W.c ^ (-(1 / 3 : ℝ)) := by positivity
    have hb_nn : 0 ≤ P.b * W.c ^ (1 / 3 : ℝ) := by have := P.hb; positivity
    calc (Real.pi / 2) * (k₁ : ℝ)
        = (Real.pi / (2 * P.b)) * (k₁ : ℝ) * (W.c ^ (-(1 / 3 : ℝ)) * W.c ^ (1 / 3 : ℝ)) * P.b := by
            rw [hc_inv]; field_simp [P.hb.ne']
      _ = (Real.pi / (2 * P.b)) * (k₁ : ℝ) * W.c ^ (-(1 / 3 : ℝ)) * (P.b * W.c ^ (1 / 3 : ℝ)) := by
            ring
      _ ≤ lam0 * (k₁ : ℝ) * W.c ^ (-(1 / 3 : ℝ)) * (P.b * W.c ^ (1 / 3 : ℝ)) := by gcongr
      _ ≤ lam0 * (k₁ : ℝ) * W.c ^ (-(1 / 3 : ℝ)) * W.a := mul_le_mul_of_nonneg_left W.ha_lb hlam_nn
  have hstir := teb_stirling_bound hk1_pos hℓ_pos ha_pos hla
  have hexp_k1 : Real.exp (-(k₁ : ℝ)) ≤ 1 / W.L := by
    have hlog_le : Real.log W.L ≤ (k₁ : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_max_right P.k_0 ⌈Real.log W.L⌉₊)
    calc Real.exp (-(k₁ : ℝ)) ≤ Real.exp (-Real.log W.L) := Real.exp_le_exp.mpr (by linarith)
      _ = 1 / W.L := by rw [Real.exp_neg, Real.exp_log (by linarith [W.hL_lb]), one_div]
  have hArc_cov_le : W.Arc_cov k₁ ℓ ≤ (4 * P.C_a / P.b) * (1 + Real.log W.L) * W.c ^ (-(1 / 3 : ℝ)) := by
    have hCaL_nn : 0 ≤ P.C_a * W.L * W.a⁻¹ := by have := P.hCa; have := W.hL_lb; positivity
    have hL_pos : 0 < W.L := by linarith [W.hL_lb]
    have h4Ca_nn : 0 ≤ 4 * P.C_a := by linarith [P.hCa]
    calc W.Arc_cov k₁ ℓ
        ≤ P.C_a * W.L * W.a⁻¹ * (4 * Real.exp (-(k₁ : ℝ))) :=
          (W.hArc_cov k₁ ℓ hk1_ge hk1_le_R5 hℓ_mem).trans (mul_le_mul_of_nonneg_left hstir hCaL_nn)
      _ ≤ P.C_a * W.L * W.a⁻¹ * (4 * (1 / W.L)) := by gcongr
      _ = 4 * P.C_a * W.a⁻¹ := by field_simp [hL_pos.ne']
      _ ≤ 4 * P.C_a * (P.b⁻¹ * W.c ^ (-(1 / 3 : ℝ))) := mul_le_mul_of_nonneg_left ha_inv_le h4Ca_nn
      _ = (4 * P.C_a / P.b) * 1 * W.c ^ (-(1 / 3 : ℝ)) := by ring
      _ ≤ (4 * P.C_a / P.b) * (1 + Real.log W.L) * W.c ^ (-(1 / 3 : ℝ)) := by
          gcongr; exact div_nonneg (by linarith [P.hCa]) P.hb.le
  have hArc_unc_le : W.Arc_unc ≤ P.C_unc * (1 + Real.log W.L) * W.c ^ (-(1 / 3 : ℝ)) := by
    calc W.Arc_unc ≤ P.C_unc * W.c ^ (-(3 / 8 : ℝ)) := W.hArc_unc
      _ ≤ P.C_unc * (1 * W.c ^ (-(1 / 3 : ℝ))) := by
          rw [one_mul]
          exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)) P.hCunc
      _ ≤ P.C_unc * (1 + Real.log W.L) * W.c ^ (-(1 / 3 : ℝ)) := by
          rw [mul_assoc]; gcongr; exact P.hCunc
  have hη_vac_le : W.η_vac ≤ W.C_vac * (1 + Real.log W.L) * W.c ^ (-(1 / 3 : ℝ)) := by
    calc W.η_vac ≤ W.C_vac * 1 * W.c ^ (-(1 / 3 : ℝ)) := by
          simpa only [mul_one] using W.hη_vac_ub
      _ ≤ W.C_vac * (1 + Real.log W.L) * W.c ^ (-(1 / 3 : ℝ)) := by gcongr; exact W.hCvac
  have hk1_le_log : (k₁ : ℝ) ≤ (P.k_0 : ℝ) * (1 + Real.log W.L) := by
    have hk0_ge1 : (1 : ℝ) ≤ P.k_0 := by exact_mod_cast P.hk0
    have h1 : (P.k_0 : ℝ) ≤ (P.k_0 : ℝ) * (1 + Real.log W.L) :=
      le_mul_of_one_le_right (by positivity) h1log_ge1
    have h2 : (⌈Real.log W.L⌉₊ : ℝ) ≤ (P.k_0 : ℝ) * (1 + Real.log W.L) := by
      have hceil := Nat.ceil_lt_add_one (Real.log_nonneg W.hL_lb)
      nlinarith
    have hmax : (k₁ : ℝ) = max (P.k_0 : ℝ) (⌈Real.log W.L⌉₊ : ℝ) := by
      dsimp [k₁, tebK1]; push_cast [Nat.cast_max]; rfl
    rw [hmax]; exact max_le h1 h2
  have hLine_k_le : P.C_a * ((k₁ : ℝ) + 1) / W.R ≤
      (2 * P.C_a * (P.k_0 : ℝ) / P.b ^ 2) * (1 + Real.log W.L) * W.c ^ (-(1 / 3 : ℝ)) := by
    have hk1_plus : (k₁ : ℝ) + 1 ≤ 2 * (P.k_0 : ℝ) * (1 + Real.log W.L) := by
      have : (1 : ℝ) ≤ k₁ := by exact_mod_cast hk1_pos
      linarith
    have hR_nn : 0 ≤ W.R⁻¹ := inv_nonneg.mpr (le_trans (by have := P.hb; positivity) hR_ge)
    have hCa_k_nn : 0 ≤ P.C_a * (2 * (P.k_0 : ℝ) * (1 + Real.log W.L)) := by have := P.hCa; positivity
    calc P.C_a * ((k₁ : ℝ) + 1) / W.R
        = P.C_a * ((k₁ : ℝ) + 1) * W.R⁻¹ := div_eq_mul_inv _ _
      _ ≤ P.C_a * (2 * (P.k_0 : ℝ) * (1 + Real.log W.L)) * W.R⁻¹ := by gcongr; exact P.hCa
      _ ≤ P.C_a * (2 * (P.k_0 : ℝ) * (1 + Real.log W.L)) * ((P.b ^ 2)⁻¹ * W.c ^ (-(1 / 3 : ℝ))) :=
          mul_le_mul_of_nonneg_left hR_inv_le hCa_k_nn
      _ = (2 * P.C_a * (P.k_0 : ℝ) / P.b ^ 2) * (1 + Real.log W.L) * W.c ^ (-(1 / 3 : ℝ)) := by ring
  have hCN_ell_le : W.C_N * ℓ ≤ (W.C_N * lam0 * (P.k_0 : ℝ)) * (1 + Real.log W.L) * W.c ^ (-(1 / 3 : ℝ)) := by
    have hCN := W.hCN
    calc W.C_N * (lam0 * (k₁ : ℝ) * W.c ^ (-(1 / 3 : ℝ)))
        ≤ W.C_N * (lam0 * ((P.k_0 : ℝ) * (1 + Real.log W.L)) * W.c ^ (-(1 / 3 : ℝ))) := by gcongr
      _ = (W.C_N * lam0 * (P.k_0 : ℝ)) * (1 + Real.log W.L) * W.c ^ (-(1 / 3 : ℝ)) := by ring
  have hexp_le : W.R * W.r_inf + W.C_err * W.c * Real.exp (-P.κ * W.c) +
      P.C_α * W.R ^ (3 / 2 : ℝ) * W.r_inf ≤ 1 * (1 + Real.log W.L) * W.c ^ (-(1 / 3 : ℝ)) := by
    calc W.R * W.r_inf + W.C_err * W.c * Real.exp (-P.κ * W.c) + P.C_α * W.R ^ (3 / 2 : ℝ) * W.r_inf
        ≤ 1 * 1 * W.c ^ (-(1 / 3 : ℝ)) := by simpa only [one_mul] using h_exp_abs
      _ ≤ 1 * (1 + Real.log W.L) * W.c ^ (-(1 / 3 : ℝ)) := by gcongr
  have hP_comb : (63 / 100 : ℝ) * W.B_1k k₁ + W.B_2' k₁ ≤
      W.C_N * ℓ + W.η_vac + P.C_a * ((k₁ : ℝ) + 1) / W.R +
        (W.R * W.r_inf + W.C_err * W.c * Real.exp (-P.κ * W.c) + P.C_α * W.R ^ (3 / 2 : ℝ) * W.r_inf) +
        W.Arc_cov k₁ ℓ + W.Arc_unc := by
    linarith [W.hP_nodes_lb k₁ ℓ hk1_ge hk1_le_R5 hℓ_mem, W.hP_le k₁ ℓ hk1_ge hk1_le_R5 hℓ_mem,
      W.hI_line_vac k₁ ℓ hk1_ge hk1_le_R5 hℓ_mem]
  have hB_comb : (63 / 100 : ℝ) * (W.B_1 + W.B_2) ≤ (63 / 100 : ℝ) * W.B_1k k₁ + W.B_2' k₁ := by
    nlinarith [W.hB_sum k₁ hk1_ge hk1_le_R5, W.hB2'_nn k₁ hk1_ge hk1_le_R5]
  have h63 : (63 / 100 : ℝ) * (W.B_1 + W.B_2) ≤
      (W.C_N * lam0 * (P.k_0 : ℝ) + 2 * P.C_a * (P.k_0 : ℝ) / P.b ^ 2 +
        4 * P.C_a / P.b + P.C_unc + W.C_vac + 1) * (1 + Real.log W.L) * W.c ^ (-(1 / 3 : ℝ)) := by
    linarith
  calc W.B_1 + W.B_2
      = (100 / 63 : ℝ) * ((63 / 100 : ℝ) * (W.B_1 + W.B_2)) := by ring
    _ ≤ (100 / 63 : ℝ) * ((W.C_N * lam0 * (P.k_0 : ℝ) + 2 * P.C_a * (P.k_0 : ℝ) / P.b ^ 2 +
          4 * P.C_a / P.b + P.C_unc + W.C_vac + 1) * (1 + Real.log W.L) * W.c ^ (-(1 / 3 : ℝ))) :=
        mul_le_mul_of_nonneg_left h63 (by norm_num)
    _ = tebCXWeak P W.C_N W.C_vac * (1 + Real.log W.L) * W.c ^ (-(1 / 3 : ℝ)) := by
        unfold tebCXWeak; ring

/-- Explicit `C_K` constant for `K ≤ C_K (1 + log L)` in `TE.2(5)` without feedback. -/
noncomputable def tebCKWeak (P : BootstrapParams) (θ a_N C_vac : ℝ) : ℝ :=
  max (max (P.D_1 / θ) (Real.pi * (P.k_0 : ℝ) / (2 * P.b * θ)))
    ((2 * P.C_a * (P.k_0 : ℝ) / P.b ^ 2 + 4 * P.C_a / P.b + P.C_unc + C_vac + 1) / a_N)

lemma tebCKWeak_pos (P : BootstrapParams) {θ a_N C_vac : ℝ}
    (_hθ : 0 < θ) (ha : 0 < a_N) (hCvac : 0 ≤ C_vac) :
    0 < tebCKWeak P θ a_N C_vac := by
  unfold tebCKWeak
  have := P.hCa; have := P.hCunc; have := P.hb
  exact lt_of_lt_of_le (by positivity) (le_max_right _ _)

/-- **Theorem TE.2(5)** without feedback: for `c ≥ tebC2 P`,
`K = c^{1/3} x_tilde ≤ C_K (1 + log L)`. -/
theorem teb_weak_K_log_bound (P : BootstrapParams) (W : BootstrapWeakCore P) (hc : tebC2 P ≤ W.c) :
    W.c ^ (1 / 3 : ℝ) * W.x_tilde ≤
      tebCKWeak P W.θ W.a_N W.C_vac * (1 + Real.log W.L) := by
  set K := W.c ^ (1 / 3 : ℝ) * W.x_tilde
  set k₁ := tebK1 P W.L
  have _ := hc
  have hc_pos : 0 < W.c := by linarith [W.hc]
  have hc1 : 1 ≤ W.c := by linarith [W.hc]
  have h1log_ge1 : 1 ≤ 1 + Real.log W.L := by linarith [Real.log_nonneg W.hL_lb]
  have hk1_ge : P.k_0 ≤ k₁ := le_max_left _ _
  have hk1_pos : 1 ≤ k₁ := P.hk0.trans hk1_ge
  have hk1_le_log : (k₁ : ℝ) ≤ (P.k_0 : ℝ) * (1 + Real.log W.L) := by
    have hk0_ge1 : (1 : ℝ) ≤ P.k_0 := by exact_mod_cast P.hk0
    have h1 : (P.k_0 : ℝ) ≤ (P.k_0 : ℝ) * (1 + Real.log W.L) :=
      le_mul_of_one_le_right (by positivity) h1log_ge1
    have h2 : (⌈Real.log W.L⌉₊ : ℝ) ≤ (P.k_0 : ℝ) * (1 + Real.log W.L) := by
      have hceil := Nat.ceil_lt_add_one (Real.log_nonneg W.hL_lb)
      nlinarith
    have hmax : (k₁ : ℝ) = max (P.k_0 : ℝ) (⌈Real.log W.L⌉₊ : ℝ) := by
      dsimp [k₁, tebK1]; push_cast [Nat.cast_max]; rfl
    rw [hmax]; exact max_le h1 h2
  set thresh := max (P.D_1 / W.θ) (Real.pi * (k₁ : ℝ) / (2 * P.b * W.θ))
  rcases le_or_gt K thresh with hK_small | hK_large
  · have h_tr_le : thresh ≤ max (P.D_1 / W.θ) (Real.pi * (P.k_0 : ℝ) / (2 * P.b * W.θ)) *
        (1 + Real.log W.L) := by
      have hD1_le : P.D_1 / W.θ ≤ max (P.D_1 / W.θ) (Real.pi * (P.k_0 : ℝ) / (2 * P.b * W.θ)) *
          (1 + Real.log W.L) := by
        calc P.D_1 / W.θ
            ≤ (P.D_1 / W.θ) * (1 + Real.log W.L) :=
              le_mul_of_one_le_right (div_nonneg P.hD1 W.hθ_pos.le) h1log_ge1
          _ ≤ max (P.D_1 / W.θ) (Real.pi * (P.k_0 : ℝ) / (2 * P.b * W.θ)) * (1 + Real.log W.L) := by
              gcongr; exact le_max_left _ _
      have hpi_le : Real.pi * (k₁ : ℝ) / (2 * P.b * W.θ) ≤
          max (P.D_1 / W.θ) (Real.pi * (P.k_0 : ℝ) / (2 * P.b * W.θ)) * (1 + Real.log W.L) := by
        have h1 : Real.pi * (k₁ : ℝ) / (2 * P.b * W.θ) ≤
            (Real.pi * (P.k_0 : ℝ) / (2 * P.b * W.θ)) * (1 + Real.log W.L) := by
          have hb := P.hb; have _ := W.hθ_pos
          calc Real.pi * (k₁ : ℝ) / (2 * P.b * W.θ)
              ≤ Real.pi * ((P.k_0 : ℝ) * (1 + Real.log W.L)) / (2 * P.b * W.θ) := by gcongr
            _ = (Real.pi * (P.k_0 : ℝ) / (2 * P.b * W.θ)) * (1 + Real.log W.L) := by ring
        exact h1.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith))
      exact max_le hD1_le hpi_le
    exact hK_small.trans (h_tr_le.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)))
  · set ℓ := W.θ * W.x_tilde
    have hc_cancel : W.c ^ (1 / 3 : ℝ) * W.c ^ (-(1 / 3 : ℝ)) = 1 := by
      rw [← Real.rpow_add hc_pos, add_neg_cancel, Real.rpow_zero]
    have hD1_lt : P.D_1 / W.θ < K := lt_of_le_of_lt (le_max_left _ _) hK_large
    have hpi_lt : Real.pi * (k₁ : ℝ) / (2 * P.b * W.θ) < K := lt_of_le_of_lt (le_max_right _ _) hK_large
    have hℓ_lb : P.D_1 * W.c ^ (-(1 / 3 : ℝ)) ≤ ℓ := by
      have h1 : P.D_1 < W.θ * K := (div_lt_iff₀' W.hθ_pos).mp hD1_lt
      have h2 : P.D_1 ≤ W.c ^ (1 / 3 : ℝ) * ℓ := by dsimp [K, ℓ] at h1 ⊢; linarith
      calc P.D_1 * W.c ^ (-(1 / 3 : ℝ)) ≤ (W.c ^ (1 / 3 : ℝ) * ℓ) * W.c ^ (-(1 / 3 : ℝ)) := by gcongr
        _ = ℓ := by rw [mul_comm (W.c ^ (1 / 3 : ℝ)), mul_assoc, hc_cancel, mul_one]
    have hθ_le1 : W.θ ≤ 1 := W.hθ_half.trans (by norm_num)
    have hℓ_mem : ℓ ∈ Set.Icc (P.D_1 * W.c ^ (-(1 / 3 : ℝ))) (min P.δ_star (min P.η_0 1)) :=
      ⟨hℓ_lb, (mul_le_of_le_one_left W.hx_pos.le hθ_le1).trans W.hx_ub⟩
    have hR_ge : P.b ^ 2 * W.c ^ (2 / 3 : ℝ) ≤ W.R := by
      have hc_nn : 0 ≤ W.c := hc_pos.le
      have hsq : (P.b * W.c ^ (1 / 3 : ℝ)) ^ 2 ≤ W.a ^ 2 := by
        nlinarith [W.ha_lb, mul_nonneg P.hb.le (Real.rpow_nonneg hc_nn (1 / 3 : ℝ))]
      rw [W.ha_sq, mul_pow, ← Real.rpow_natCast (W.c ^ (1 / 3 : ℝ)) 2, ← Real.rpow_mul hc_nn] at hsq
      norm_num at hsq; exact hsq
    have h_large := tebCThresh_spec P ((le_max_right (2 : ℝ) _).trans hc) W.hL_lb W.hL_ub hR_ge
      W.hR_ub W.hr_inf_nn W.hr_inf_ub W.hC_err_ub
    obtain ⟨_, hk1_le_R5, h_exp_abs⟩ := h_large
    have hℓ_pos : 0 < ℓ := mul_pos W.hθ_pos W.hx_pos
    have ha_pos : 0 < W.a := by
      have : 0 < P.b * W.c ^ (1 / 3 : ℝ) := mul_pos P.hb (Real.rpow_pos_of_pos hc_pos _)
      linarith [W.ha_lb]
    have hla : (Real.pi / 2) * (k₁ : ℝ) ≤ ℓ * W.a := by
      have hb := P.hb; have hθ := W.hθ_pos
      have h1 : Real.pi * (k₁ : ℝ) ≤ (2 * P.b * W.θ) * K := by
        have := (div_lt_iff₀' (by positivity : 0 < 2 * P.b * W.θ)).mp hpi_lt
        linarith
      have h2 : (Real.pi / 2) * (k₁ : ℝ) ≤ ℓ * (P.b * W.c ^ (1 / 3 : ℝ)) := by
        dsimp [K, ℓ] at h1 ⊢; linarith
      exact h2.trans (mul_le_mul_of_nonneg_left W.ha_lb hℓ_pos.le)
    have hstir := teb_stirling_bound hk1_pos hℓ_pos ha_pos hla
    have hexp_k1 : Real.exp (-(k₁ : ℝ)) ≤ 1 / W.L := by
      have hlog_le : Real.log W.L ≤ (k₁ : ℝ) :=
        (Nat.le_ceil _).trans (by exact_mod_cast le_max_right P.k_0 ⌈Real.log W.L⌉₊)
      calc Real.exp (-(k₁ : ℝ)) ≤ Real.exp (-Real.log W.L) := Real.exp_le_exp.mpr (by linarith)
        _ = 1 / W.L := by rw [Real.exp_neg, Real.exp_log (by linarith [W.hL_lb]), one_div]
    have ha_inv_le : W.a⁻¹ ≤ P.b⁻¹ * W.c ^ (-(1 / 3 : ℝ)) := by
      have hp : 0 < P.b * W.c ^ (1 / 3 : ℝ) := mul_pos P.hb (Real.rpow_pos_of_pos hc_pos _)
      calc W.a⁻¹ ≤ (P.b * W.c ^ (1 / 3 : ℝ))⁻¹ := inv_anti₀ hp W.ha_lb
        _ = P.b⁻¹ * W.c ^ (-(1 / 3 : ℝ)) := by rw [mul_inv, ← Real.rpow_neg hc_pos.le]
    have hR_inv_le : W.R⁻¹ ≤ (P.b ^ 2)⁻¹ * W.c ^ (-(1 / 3 : ℝ)) := by
      have hR_lb13 : P.b ^ 2 * W.c ^ (1 / 3 : ℝ) ≤ W.R :=
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num))
          (sq_nonneg P.b)).trans hR_ge
      have hb := P.hb
      calc W.R⁻¹ ≤ (P.b ^ 2 * W.c ^ (1 / 3 : ℝ))⁻¹ := inv_anti₀ (by positivity) hR_lb13
        _ = (P.b ^ 2)⁻¹ * W.c ^ (-(1 / 3 : ℝ)) := by rw [mul_inv, ← Real.rpow_neg hc_pos.le]
    have hArc_cov_le : W.Arc_cov k₁ ℓ ≤ (4 * P.C_a / P.b) * (1 + Real.log W.L) * W.c ^ (-(1 / 3 : ℝ)) := by
      have hCaL_nn : 0 ≤ P.C_a * W.L * W.a⁻¹ := by have := P.hCa; have := W.hL_lb; positivity
      have hL_pos : 0 < W.L := by linarith [W.hL_lb]
      have h4Ca_nn : 0 ≤ 4 * P.C_a := by linarith [P.hCa]
      calc W.Arc_cov k₁ ℓ
          ≤ P.C_a * W.L * W.a⁻¹ * (4 * Real.exp (-(k₁ : ℝ))) :=
            (W.hArc_cov k₁ ℓ hk1_ge hk1_le_R5 hℓ_mem).trans (mul_le_mul_of_nonneg_left hstir hCaL_nn)
        _ ≤ P.C_a * W.L * W.a⁻¹ * (4 * (1 / W.L)) := by gcongr
        _ = 4 * P.C_a * W.a⁻¹ := by field_simp [hL_pos.ne']
        _ ≤ 4 * P.C_a * (P.b⁻¹ * W.c ^ (-(1 / 3 : ℝ))) := mul_le_mul_of_nonneg_left ha_inv_le h4Ca_nn
        _ = (4 * P.C_a / P.b) * 1 * W.c ^ (-(1 / 3 : ℝ)) := by ring
        _ ≤ (4 * P.C_a / P.b) * (1 + Real.log W.L) * W.c ^ (-(1 / 3 : ℝ)) := by
            gcongr; exact div_nonneg (by linarith [P.hCa]) P.hb.le
    have hArc_unc_le : W.Arc_unc ≤ P.C_unc * (1 + Real.log W.L) * W.c ^ (-(1 / 3 : ℝ)) := by
      calc W.Arc_unc ≤ P.C_unc * W.c ^ (-(3 / 8 : ℝ)) := W.hArc_unc
        _ ≤ P.C_unc * (1 * W.c ^ (-(1 / 3 : ℝ))) := by
            rw [one_mul]
            exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)) P.hCunc
        _ ≤ P.C_unc * (1 + Real.log W.L) * W.c ^ (-(1 / 3 : ℝ)) := by
            rw [mul_assoc]; gcongr; exact P.hCunc
    have hη_vac_le : W.η_vac ≤ W.C_vac * (1 + Real.log W.L) * W.c ^ (-(1 / 3 : ℝ)) := by
      calc W.η_vac ≤ W.C_vac * 1 * W.c ^ (-(1 / 3 : ℝ)) := by
            simpa only [mul_one] using W.hη_vac_ub
        _ ≤ W.C_vac * (1 + Real.log W.L) * W.c ^ (-(1 / 3 : ℝ)) := by gcongr; exact W.hCvac
    have hLine_k_le : P.C_a * ((k₁ : ℝ) + 1) / W.R ≤
        (2 * P.C_a * (P.k_0 : ℝ) / P.b ^ 2) * (1 + Real.log W.L) * W.c ^ (-(1 / 3 : ℝ)) := by
      have hk1_plus : (k₁ : ℝ) + 1 ≤ 2 * (P.k_0 : ℝ) * (1 + Real.log W.L) := by
        have : (1 : ℝ) ≤ k₁ := by exact_mod_cast hk1_pos
        linarith
      have hR_nn : 0 ≤ W.R⁻¹ := inv_nonneg.mpr (le_trans (by have := P.hb; positivity) hR_ge)
      have hCa_k_nn : 0 ≤ P.C_a * (2 * (P.k_0 : ℝ) * (1 + Real.log W.L)) := by have := P.hCa; positivity
      calc P.C_a * ((k₁ : ℝ) + 1) / W.R
          = P.C_a * ((k₁ : ℝ) + 1) * W.R⁻¹ := div_eq_mul_inv _ _
        _ ≤ P.C_a * (2 * (P.k_0 : ℝ) * (1 + Real.log W.L)) * W.R⁻¹ := by gcongr; exact P.hCa
        _ ≤ P.C_a * (2 * (P.k_0 : ℝ) * (1 + Real.log W.L)) * ((P.b ^ 2)⁻¹ * W.c ^ (-(1 / 3 : ℝ))) :=
            mul_le_mul_of_nonneg_left hR_inv_le hCa_k_nn
        _ = (2 * P.C_a * (P.k_0 : ℝ) / P.b ^ 2) * (1 + Real.log W.L) * W.c ^ (-(1 / 3 : ℝ)) := by ring
    have hexp_le : W.R * W.r_inf + W.C_err * W.c * Real.exp (-P.κ * W.c) +
        P.C_α * W.R ^ (3 / 2 : ℝ) * W.r_inf ≤ 1 * (1 + Real.log W.L) * W.c ^ (-(1 / 3 : ℝ)) := by
      calc W.R * W.r_inf + W.C_err * W.c * Real.exp (-P.κ * W.c) + P.C_α * W.R ^ (3 / 2 : ℝ) * W.r_inf
          ≤ 1 * 1 * W.c ^ (-(1 / 3 : ℝ)) := by simpa only [one_mul] using h_exp_abs
        _ ≤ 1 * (1 + Real.log W.L) * W.c ^ (-(1 / 3 : ℝ)) := by gcongr
    have haN_x : W.a_N * W.x_tilde ≤ W.η_vac + P.C_a * ((k₁ : ℝ) + 1) / W.R +
        (W.R * W.r_inf + W.C_err * W.c * Real.exp (-P.κ * W.c) + P.C_α * W.R ^ (3 / 2 : ℝ) * W.r_inf) +
        W.Arc_cov k₁ ℓ + W.Arc_unc := by
      linarith [W.hP_theta_lb k₁ hk1_ge hk1_le_R5 hℓ_mem, W.hP_le k₁ ℓ hk1_ge hk1_le_R5 hℓ_mem,
        W.hI_line_vac k₁ ℓ hk1_ge hk1_le_R5 hℓ_mem, W.hB1k_nn k₁ hk1_ge hk1_le_R5,
        W.hB2'_nn k₁ hk1_ge hk1_le_R5]
    have haN_x' : W.a_N * W.x_tilde ≤
        (2 * P.C_a * (P.k_0 : ℝ) / P.b ^ 2 + 4 * P.C_a / P.b + P.C_unc + W.C_vac + 1) *
          (1 + Real.log W.L) * W.c ^ (-(1 / 3 : ℝ)) := by linarith
    have hc13_nn : 0 ≤ W.c ^ (1 / 3 : ℝ) := Real.rpow_nonneg hc_pos.le _
    have haN_K : W.a_N * K ≤
        (2 * P.C_a * (P.k_0 : ℝ) / P.b ^ 2 + 4 * P.C_a / P.b + P.C_unc + W.C_vac + 1) *
          (1 + Real.log W.L) := by
      calc W.a_N * K = W.c ^ (1 / 3 : ℝ) * (W.a_N * W.x_tilde) := by dsimp [K]; ring
        _ ≤ W.c ^ (1 / 3 : ℝ) * ((2 * P.C_a * (P.k_0 : ℝ) / P.b ^ 2 + 4 * P.C_a / P.b +
              P.C_unc + W.C_vac + 1) * (1 + Real.log W.L) * W.c ^ (-(1 / 3 : ℝ))) :=
            mul_le_mul_of_nonneg_left haN_x' hc13_nn
        _ = (2 * P.C_a * (P.k_0 : ℝ) / P.b ^ 2 + 4 * P.C_a / P.b + P.C_unc + W.C_vac + 1) *
              (1 + Real.log W.L) * (W.c ^ (1 / 3 : ℝ) * W.c ^ (-(1 / 3 : ℝ))) := by ring
        _ = (2 * P.C_a * (P.k_0 : ℝ) / P.b ^ 2 + 4 * P.C_a / P.b + P.C_unc + W.C_vac + 1) *
              (1 + Real.log W.L) := by rw [hc_cancel, mul_one]
    have hK_div : K ≤ ((2 * P.C_a * (P.k_0 : ℝ) / P.b ^ 2 + 4 * P.C_a / P.b +
        P.C_unc + W.C_vac + 1) / W.a_N) * (1 + Real.log W.L) := by
      calc K = (W.a_N * K) / W.a_N := by field_simp [W.haN_pos.ne']
        _ ≤ ((2 * P.C_a * (P.k_0 : ℝ) / P.b ^ 2 + 4 * P.C_a / P.b +
              P.C_unc + W.C_vac + 1) * (1 + Real.log W.L)) / W.a_N :=
            div_le_div_of_nonneg_right haN_K W.haN_pos.le
        _ = ((2 * P.C_a * (P.k_0 : ℝ) / P.b ^ 2 + 4 * P.C_a / P.b +
              P.C_unc + W.C_vac + 1) / W.a_N) * (1 + Real.log W.L) := by ring
    exact hK_div.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith))

/-- Explicit weak-feedback scale `C_*^{weak} := max 1 (C_fb (C_X^{weak} + 1))`. -/
noncomputable def tebCStarWeak (P : BootstrapParams) (C_N C_vac : ℝ) : ℝ :=
  max 1 (P.C_fb * (tebCXWeak P C_N C_vac + 1))

/-- **Theorem TE.2(5)** with weak feedback `L ≤ C_fb (c^{1/3} (B₁ + B₂) + Υ_c)` (`1 ≤ Υ_c`):
`L ≤ C' Υ_c` and `K ≤ C'' (1 + log Υ_c)`. -/
theorem teb_weak_feedback_closure (P : BootstrapParams) (W : BootstrapWeakCore P)
    (hc : tebC2 P ≤ W.c) {Upsilon : ℝ} (hU : 1 ≤ Upsilon)
    (hfb : W.L ≤ P.C_fb * (W.c ^ (1 / 3 : ℝ) * (W.B_1 + W.B_2) + Upsilon)) :
    let L_scale := tebWeakScale (tebCStarWeak P W.C_N W.C_vac)
    W.L ≤ L_scale * Upsilon ∧
      W.c ^ (1 / 3 : ℝ) * W.x_tilde ≤
        tebCKWeak P W.θ W.a_N W.C_vac * (1 + Real.log L_scale) * (1 + Real.log Upsilon) := by
  set Cstar := tebCStarWeak P W.C_N W.C_vac
  set L_scale := tebWeakScale Cstar
  have hc_pos : 0 < W.c := by linarith [W.hc]
  have hc_cancel : W.c ^ (1 / 3 : ℝ) * W.c ^ (-(1 / 3 : ℝ)) = 1 := by
    rw [← Real.rpow_add hc_pos, add_neg_cancel, Real.rpow_zero]
  have h1 := teb_weak_part1 P W hc
  have hcB_le : W.c ^ (1 / 3 : ℝ) * (W.B_1 + W.B_2) ≤
      tebCXWeak P W.C_N W.C_vac * (1 + Real.log W.L) := by
    calc W.c ^ (1 / 3 : ℝ) * (W.B_1 + W.B_2)
        ≤ W.c ^ (1 / 3 : ℝ) *
            (tebCXWeak P W.C_N W.C_vac * (1 + Real.log W.L) * W.c ^ (-(1 / 3 : ℝ))) :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hc_pos.le _)
      _ = tebCXWeak P W.C_N W.C_vac * (1 + Real.log W.L) *
            (W.c ^ (1 / 3 : ℝ) * W.c ^ (-(1 / 3 : ℝ))) := by ring
      _ = tebCXWeak P W.C_N W.C_vac * (1 + Real.log W.L) := by rw [hc_cancel, mul_one]
  have hCX_nn := (tebCXWeak_pos P W.hCN W.hCvac).le
  have hL_ineq : W.L ≤ Cstar * (Upsilon + Real.log W.L) := by
    have hlog_nn : 0 ≤ Real.log W.L := Real.log_nonneg W.hL_lb
    have hU_nn : 0 ≤ Upsilon := by linarith
    have h_inner : tebCXWeak P W.C_N W.C_vac * (1 + Real.log W.L) + Upsilon ≤
        (tebCXWeak P W.C_N W.C_vac + 1) * (Upsilon + Real.log W.L) := by nlinarith
    calc W.L ≤ P.C_fb * (W.c ^ (1 / 3 : ℝ) * (W.B_1 + W.B_2) + Upsilon) := hfb
      _ ≤ P.C_fb * (tebCXWeak P W.C_N W.C_vac * (1 + Real.log W.L) + Upsilon) := by
          gcongr; exact le_trans zero_le_one P.hCfb
      _ ≤ P.C_fb * ((tebCXWeak P W.C_N W.C_vac + 1) * (Upsilon + Real.log W.L)) := by
          gcongr; exact le_trans zero_le_one P.hCfb
      _ = P.C_fb * (tebCXWeak P W.C_N W.C_vac + 1) * (Upsilon + Real.log W.L) := by ring
      _ ≤ Cstar * (Upsilon + Real.log W.L) := by
          gcongr; exact le_max_right _ _
  have hL_ub : W.L ≤ L_scale * Upsilon :=
    log_weak_feedback_bound (le_max_left _ _) hU W.hL_lb hL_ineq
  have hLscale_ge1 : 1 ≤ L_scale := one_le_tebWeakScale (le_max_left _ _)
  have hLscale_pos : 0 < L_scale := by linarith
  have hU_pos : 0 < Upsilon := by linarith
  have hlogL_le : 1 + Real.log W.L ≤ (1 + Real.log L_scale) * (1 + Real.log Upsilon) := by
    have hlog1 : Real.log W.L ≤ Real.log (L_scale * Upsilon) :=
      Real.log_le_log (by linarith [W.hL_lb]) hL_ub
    rw [Real.log_mul hLscale_pos.ne' hU_pos.ne'] at hlog1
    have hlogU_nn : 0 ≤ Real.log Upsilon := Real.log_nonneg hU
    have hlogS_nn : 0 ≤ Real.log L_scale := Real.log_nonneg hLscale_ge1
    nlinarith
  have hCK_nn := (tebCKWeak_pos P W.hθ_pos W.haN_pos W.hCvac).le
  refine ⟨hL_ub, (teb_weak_K_log_bound P W hc).trans ?_⟩
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hlogL_le hCK_nn

/-! ### Non-Vacuity Witness (with strict `η_vac = C_vac * c^{-1/3} > 0`) -/

/-- Non-vacuity witness for `BootstrapWeakCore` (saturating `0 < η_vac = C_vac * c^{-1/3}` and
weak feedback) for all `c ≥ 2` and `Υ_c ≥ 1`. -/
theorem bootstrapWeakCore_nonvacuous :
    ∀ c : ℝ, 2 ≤ c → ∀ Upsilon : ℝ, 1 ≤ Upsilon →
      ∃ W : BootstrapWeakCore defaultBootstrapParams,
        W.c = c ∧ 0 < W.η_vac ∧ W.η_vac = W.C_vac * W.c ^ (-(1 / 3 : ℝ)) ∧
        W.L ≤ defaultBootstrapParams.C_fb *
          (W.c ^ (1 / 3 : ℝ) * (W.B_1 + W.B_2) + Upsilon) := by
  intro c hc Upsilon hU
  have hc_pos : 0 < c := by linarith
  have hc1 : 1 ≤ c := by linarith
  let R : ℝ := c ^ (2 / 3 : ℝ)
  let a : ℝ := c ^ (1 / 3 : ℝ)
  let x_tilde : ℝ := c ^ (-(2 / 3 : ℝ))
  let η : ℝ := c ^ (-(1 / 3 : ℝ))
  have hη_pos : 0 < η := Real.rpow_pos_of_pos hc_pos _
  refine ⟨{
    c := c, R := R, a := a, B_1 := 0, B_2 := 0, L := 1
    x_tilde := x_tilde, r_inf := 0, C_err := 0, hc := hc
    ha_lb := by simp [defaultBootstrapParams, a]
    ha_sq := by
      dsimp [a, R]; rw [← Real.rpow_natCast (c ^ (1 / 3 : ℝ)) 2, ← Real.rpow_mul hc_pos.le]; norm_num
    hR_ub := by dsimp [R, defaultBootstrapParams]; linarith [Real.rpow_nonneg hc_pos.le (2 / 3 : ℝ)]
    hB1 := le_rfl, hB2 := le_rfl, hL_lb := le_rfl
    hL_ub := by simp [defaultBootstrapParams]
    hx_pos := Real.rpow_pos_of_pos hc_pos _
    hx_ub := by
      simp only [defaultBootstrapParams, min_self, x_tilde]
      rw [← Real.rpow_zero c]; exact Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
    hr_inf_nn := le_rfl
    hr_inf_ub := by simp only [defaultBootstrapParams, one_mul, neg_mul]; positivity
    hC_err_nn := le_rfl
    hC_err_ub := by simp [defaultBootstrapParams]
    B_1k := fun _ => 0, B_2' := fun _ => 0
    P_nodes := fun k _ => η + ((k : ℝ) + 1) / R
    I_line := fun k _ => η + ((k : ℝ) + 1) / R
    Arc_cov := fun _ _ => 0, Arc_unc := 0
    hB1k_nn := fun _ _ _ => le_rfl, hB2'_nn := fun _ _ _ => le_rfl
    hB_sum := fun _ _ _ => by norm_num
    hP_le := fun _ _ _ _ _ => by ring_nf; rfl
    hArc_cov := fun k ℓ _ _ hℓ => by
      have hℓ_nn : 0 ≤ ℓ := by simpa [defaultBootstrapParams] using hℓ.1
      have ha_pos : 0 < a := Real.rpow_pos_of_pos hc_pos _
      have hgam_pos : 0 < Real.Gamma ((k : ℝ) + 1 / 2) := Real.Gamma_pos_of_pos (by positivity)
      have hpow_nn : 0 ≤ (Real.pi / (4 * ℓ * a)) ^ ((k : ℝ) + 1 / 2) :=
        Real.rpow_nonneg (by positivity) _
      simp only [defaultBootstrapParams, mul_one]; positivity
    hArc_unc := by simp only [defaultBootstrapParams, one_mul]; positivity
    C_vac := 1, η_vac := η, C_N := 1, θ := 1 / 2, a_N := 1 / 2
    hCvac := zero_le_one, hη_vac_nn := hη_pos.le, hη_vac_ub := by simp [η]
    hCN := zero_le_one, hθ_pos := by norm_num, hθ_half := le_rfl, haN_pos := by norm_num
    hI_line_vac := fun k _ _ _ _ => by
      simp only [defaultBootstrapParams, mul_zero, zero_mul, sub_zero, zero_add, one_mul, η]
      ring_nf; rfl
    hP_nodes_lb := fun k ℓ _ _ hℓ => by
      have hℓ_nn : 0 ≤ ℓ := by simpa [defaultBootstrapParams] using hℓ.1
      have hR_pos : 0 < R := Real.rpow_pos_of_pos hc_pos _
      have hp_nn : 0 ≤ η + ((k : ℝ) + 1) / R := by positivity
      dsimp [defaultBootstrapParams]
      linarith
    hP_theta_lb := fun k _ _ _ => by
      have hR_pos : 0 < R := Real.rpow_pos_of_pos hc_pos _
      have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [show (0 : ℝ) ≤ k by positivity]
      have h1 : (1 / 2 : ℝ) * x_tilde ≤ ((k : ℝ) + 1) / R := by
        dsimp [x_tilde, R]
        rw [Real.rpow_neg hc_pos.le, ← one_div]
        calc (1 / 2 : ℝ) * (1 / c ^ (2 / 3 : ℝ)) ≤ 1 * (1 / c ^ (2 / 3 : ℝ)) := by gcongr; norm_num
          _ ≤ ((k : ℝ) + 1) / c ^ (2 / 3 : ℝ) := by
              rw [one_mul]; exact div_le_div_of_nonneg_right hk1 hR_pos.le
      dsimp [defaultBootstrapParams]
      linarith
  }, rfl, hη_pos, by simp [η], by dsimp [defaultBootstrapParams]; linarith⟩

/-! ### Axiom Verification -/

/-- info: 'FormalResearch.TwoEdgeBootstrap.log_weak_feedback_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.TwoEdgeBootstrap.log_weak_feedback_bound

/-- info: 'FormalResearch.TwoEdgeBootstrap.teb_hb_single_theta_aN_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.TwoEdgeBootstrap.teb_hb_single_theta_aN_pos

/-- info: 'FormalResearch.TwoEdgeBootstrap.teb_weak_part1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.TwoEdgeBootstrap.teb_weak_part1

/-- info: 'FormalResearch.TwoEdgeBootstrap.teb_weak_K_log_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.TwoEdgeBootstrap.teb_weak_K_log_bound

/-- info: 'FormalResearch.TwoEdgeBootstrap.teb_weak_feedback_closure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.TwoEdgeBootstrap.teb_weak_feedback_closure

/-- info: 'FormalResearch.TwoEdgeBootstrap.bootstrapWeakCore_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.TwoEdgeBootstrap.bootstrapWeakCore_nonvacuous

end FormalResearch.TwoEdgeBootstrap
