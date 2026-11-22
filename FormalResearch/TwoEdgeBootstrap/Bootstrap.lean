module

public import FormalResearch.Asymptotics.StirlingHalfInt
public import FormalResearch.TwoEdgeBootstrap.FixedPoint

/-!
# Abstract Two-Edge Riesz–Airy–Poisson Bootstrap (Theorem TE.2 & Corollary TE.4)

Source: `CFT/common/two_edge_bootstrap.tex` (Theorem `TE.2` `teb:bootstrap` parts `(1)`–`(4)` and
Corollary `TE.4` `teb:mellin_o1`).

* `BootstrapParams`, `teb_large_c_exists`: effective constants and large-`c` absorption threshold.
* `BootstrapCore`, `BootstrapInstance`, `BootstrapHBInstance`: packaged `(TE.4)`–`(TE.6)` /
  `(B2_HB)` hypotheses with shared core infrastructure.
* `teb_bootstrap_part1`, `teb_bootstrap_part2`, `teb_bootstrap_part3`: parts `(1)`–`(3)` of
  Theorem `TE.2`.
* `teb_bootstrap_hb_part1`, `teb_bootstrap_hb`: all-level Hermite–Biehler extension, Theorem `TE.2(4)`.
* `teb_mellin_o1_lower`, `teb_mellin_o1_lower_of_thresh`: Corollary `TE.4` (`O(1)` lower remainder).
* `bootstrapInstance_nonvacuous`, `bootstrapHBInstance_nonvacuous`: concrete witnesses for `c ≥ 2`.
-/

@[expose] public section

open scoped Real

namespace FormalResearch.TwoEdgeBootstrap

open FormalResearch.Asymptotics

/-! ### Part 1: Effective Parameters and Large-`c` Absorption Threshold -/

section ParamsAndThreshold

/-- Effective constant package for the abstract two-edge Riesz–Airy–Poisson bootstrap
(`two_edge_bootstrap.tex`, Theorem `TE.2`). -/
structure BootstrapParams where
  b : ℝ
  C_a : ℝ
  C_unc : ℝ
  C_1 : ℝ
  w_star : ℝ
  κ_star : ℝ
  C_α : ℝ
  C_fb : ℝ
  D_1 : ℝ
  η_0 : ℝ
  δ_star : ℝ
  κ : ℝ
  C_0 : ℝ
  C_L : ℝ
  γ : ℝ
  k_0 : ℕ
  hb : 0 < b
  hCa : 0 ≤ C_a
  hCunc : 0 ≤ C_unc
  hC1 : 0 < C_1
  hw_star : 0 < w_star
  hκ_star : 0 < κ_star
  hCα : 0 ≤ C_α
  hCfb : 1 ≤ C_fb
  hD1 : 0 ≤ D_1
  hη0 : 0 < η_0
  hδ_star : 0 < δ_star
  hκ : 0 < κ
  hC0 : 0 < C_0
  hCL : 1 ≤ C_L
  hγ : 0 ≤ γ
  hk0 : 1 ≤ k_0

/-- Auxiliary exponent `k₁(L) := max k₀ ⌈log L⌉₊`. -/
noncomputable def tebK1 (P : BootstrapParams) (L : ℝ) : ℕ :=
  max P.k_0 ⌈Real.log L⌉₊

/-- Auxiliary step factor `λ₀ := max (π / (2 b)) (D₁ / k₀)`. -/
noncomputable def tebLambda0 (P : BootstrapParams) : ℝ :=
  max (Real.pi / (2 * P.b)) (if P.k_0 = 0 then 0 else P.D_1 / (P.k_0 : ℝ))

private lemma tebLambda0_eq (P : BootstrapParams) :
    tebLambda0 P = max (Real.pi / (2 * P.b)) (P.D_1 / (P.k_0 : ℝ)) := by
  simp [tebLambda0, Nat.ne_of_gt P.hk0]

private lemma tebLambda0_pos (P : BootstrapParams) : 0 < tebLambda0 P := by
  rw [tebLambda0_eq]
  exact lt_of_lt_of_le (div_pos Real.pi_pos (by linarith [P.hb])) (le_max_left _ _)

/-- Explicit logarithmic envelope factor `C_k(P) := k₀ + log C_L + 1 + 6 γ`. -/
noncomputable def tebCk (P : BootstrapParams) : ℝ :=
  (P.k_0 : ℝ) + Real.log P.C_L + 1 + 6 * P.γ

private lemma one_le_tebCk (P : BootstrapParams) : 1 ≤ tebCk P := by
  unfold tebCk
  have : (1 : ℝ) ≤ P.k_0 := by exact_mod_cast P.hk0
  linarith [Real.log_nonneg P.hCL, P.hγ]

private lemma k1_le_tebCk_rpow (P : BootstrapParams) {c L : ℝ} (hc : 1 ≤ c) (hL1 : 1 ≤ L)
    (hL_ub : L ≤ P.C_L * c ^ P.γ) :
    (tebK1 P L : ℝ) ≤ tebCk P * c ^ (1 / 6 : ℝ) := by
  have hc_pos : 0 < c := by linarith
  have hc16 : 1 ≤ c ^ (1 / 6 : ℝ) := Real.one_le_rpow hc (by norm_num)
  have hlogCL : 0 ≤ Real.log P.C_L := Real.log_nonneg P.hCL
  have hk0_le : (P.k_0 : ℝ) ≤ tebCk P * c ^ (1 / 6 : ℝ) := by
    have h1 : (P.k_0 : ℝ) ≤ tebCk P := by unfold tebCk; linarith [P.hγ]
    exact h1.trans (le_mul_of_one_le_right (by linarith [one_le_tebCk P]) hc16)
  have hceil_le : (⌈Real.log L⌉₊ : ℝ) ≤ tebCk P * c ^ (1 / 6 : ℝ) := by
    have hceil : (⌈Real.log L⌉₊ : ℝ) < Real.log L + 1 := Nat.ceil_lt_add_one (Real.log_nonneg hL1)
    have hlog_le : Real.log L ≤ Real.log P.C_L + P.γ * Real.log c := by
      have h := Real.log_le_log (by linarith) hL_ub
      rwa [Real.log_mul (by linarith [P.hCL]) (Real.rpow_pos_of_pos hc_pos _).ne',
        Real.log_rpow hc_pos] at h
    have hlogc : Real.log c ≤ 6 * c ^ (1 / 6 : ℝ) := by
      have h1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hc_pos (1 / 6 : ℝ))
      rw [Real.log_rpow hc_pos] at h1; linarith
    have h1 : (⌈Real.log L⌉₊ : ℝ) ≤ (Real.log P.C_L + 1) + 6 * P.γ * c ^ (1 / 6 : ℝ) := by nlinarith [P.hγ]
    have h2 : Real.log P.C_L + 1 ≤ (Real.log P.C_L + 1) * c ^ (1 / 6 : ℝ) := le_mul_of_one_le_right (by linarith) hc16
    have hk0_nn : (0 : ℝ) ≤ P.k_0 := Nat.cast_nonneg _
    have hc16_nn : 0 ≤ c ^ (1 / 6 : ℝ) := by positivity
    have h3 : (Real.log P.C_L + 1) * c ^ (1 / 6 : ℝ) + 6 * P.γ * c ^ (1 / 6 : ℝ) ≤ tebCk P * c ^ (1 / 6 : ℝ) := by
      unfold tebCk; nlinarith
    linarith
  have hmax : (tebK1 P L : ℝ) = max (P.k_0 : ℝ) (⌈Real.log L⌉₊ : ℝ) := by
    unfold tebK1; push_cast [Nat.cast_max]; rfl
  rw [hmax]; exact max_le hk0_le hceil_le

/-- Effective large-`c` threshold expression `c_thresh(P) ≥ 1`. -/
noncomputable def tebCThresh (P : BootstrapParams) : ℝ :=
  let m := min P.δ_star (min P.η_0 1)
  let B_R := 2 * P.b ^ 2 + 1
  let M_exp := B_R * P.C_0 + P.C_0 + P.C_α * B_R ^ (3 / 2 : ℝ) * P.C_0
  max 1 (max ((tebLambda0 P * tebCk P / m) ^ 6)
    (max ((5 * tebCk P / P.b ^ 2) ^ 2) (6 * M_exp / P.κ ^ 3)))

private lemma teb_exp_error_absorption (P : BootstrapParams) {c R r_inf C_line_err : ℝ}
    (hc1 : 1 ≤ c)
    (hc_exp : 6 * ((2 * P.b ^ 2 + 1) * P.C_0 + P.C_0 +
        P.C_α * (2 * P.b ^ 2 + 1) ^ (3 / 2 : ℝ) * P.C_0) / P.κ ^ 3 ≤ c)
    (hR_nn : 0 ≤ R) (hR_ub : R ≤ 2 * P.b ^ 2 * c ^ (2 / 3 : ℝ) + 1)
    (hr_nn : 0 ≤ r_inf) (hr_ub : r_inf ≤ P.C_0 * c ^ (1 / 3 : ℝ) * Real.exp (-P.κ * c))
    (hCerr : C_line_err ≤ P.C_0) :
    R * r_inf + C_line_err * c * Real.exp (-P.κ * c) +
      P.C_α * R ^ (3 / 2 : ℝ) * r_inf ≤ c ^ (-(1 / 3 : ℝ)) := by
  have hc_pos : 0 < c := by linarith
  have hκ_pos : 0 < P.κ := P.hκ
  set B_R : ℝ := 2 * P.b ^ 2 + 1
  set M_exp : ℝ := B_R * P.C_0 + P.C_0 + P.C_α * B_R ^ (3 / 2 : ℝ) * P.C_0
  have hBR_pos : 0 < B_R := by positivity
  have hc23_ge1 : 1 ≤ c ^ (2 / 3 : ℝ) := Real.one_le_rpow hc1 (by norm_num)
  have hR_le : R ≤ B_R * c ^ (2 / 3 : ℝ) := hR_ub.trans (by dsimp [B_R]; nlinarith)
  have hR32_le : R ^ (3 / 2 : ℝ) ≤ B_R ^ (3 / 2 : ℝ) * c := by
    have h1 := Real.rpow_le_rpow hR_nn hR_le (by positivity : 0 ≤ (3 / 2 : ℝ))
    rw [Real.mul_rpow hBR_pos.le (Real.rpow_nonneg hc_pos.le _), ← Real.rpow_mul hc_pos.le] at h1
    norm_num at h1; exact h1
  have hc_prod : c ^ (2 / 3 : ℝ) * c ^ (1 / 3 : ℝ) = c := by rw [← Real.rpow_add hc_pos]; norm_num
  have hc_c43 : c * c ^ (1 / 3 : ℝ) = c ^ (4 / 3 : ℝ) := by
    calc c * c ^ (1 / 3 : ℝ) = c ^ (1 : ℝ) * c ^ (1 / 3 : ℝ) := by rw [Real.rpow_one]
      _ = c ^ (4 / 3 : ℝ) := by rw [← Real.rpow_add hc_pos]; norm_num
  have hc_le_c43 : c ≤ c ^ (4 / 3 : ℝ) := by
    conv_lhs => rw [← Real.rpow_one c]
    exact Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
  have hterm1 : R * r_inf ≤ B_R * P.C_0 * c ^ (4 / 3 : ℝ) * Real.exp (-P.κ * c) := by
    calc R * r_inf
        ≤ (B_R * c ^ (2 / 3 : ℝ)) * (P.C_0 * c ^ (1 / 3 : ℝ) * Real.exp (-P.κ * c)) := by gcongr
      _ = B_R * P.C_0 * (c ^ (2 / 3 : ℝ) * c ^ (1 / 3 : ℝ)) * Real.exp (-P.κ * c) := by ring
      _ = B_R * P.C_0 * c * Real.exp (-P.κ * c) := by rw [hc_prod]
      _ ≤ B_R * P.C_0 * c ^ (4 / 3 : ℝ) * Real.exp (-P.κ * c) := by
          gcongr; exact mul_nonneg hBR_pos.le P.hC0.le
  have hterm2 : C_line_err * c * Real.exp (-P.κ * c) ≤ P.C_0 * c ^ (4 / 3 : ℝ) * Real.exp (-P.κ * c) := by
    have h1 : C_line_err * (c * Real.exp (-P.κ * c)) ≤ P.C_0 * (c * Real.exp (-P.κ * c)) :=
      mul_le_mul_of_nonneg_right hCerr (by positivity)
    calc C_line_err * c * Real.exp (-P.κ * c)
        = C_line_err * (c * Real.exp (-P.κ * c)) := by ring
      _ ≤ P.C_0 * c * Real.exp (-P.κ * c) := by linarith
      _ ≤ P.C_0 * c ^ (4 / 3 : ℝ) * Real.exp (-P.κ * c) := by gcongr; exact P.hC0.le
  have hterm3 : P.C_α * R ^ (3 / 2 : ℝ) * r_inf ≤
      P.C_α * B_R ^ (3 / 2 : ℝ) * P.C_0 * c ^ (4 / 3 : ℝ) * Real.exp (-P.κ * c) := by
    have hCα_nn : 0 ≤ P.C_α * (B_R ^ (3 / 2 : ℝ) * c) := mul_nonneg P.hCα (by positivity)
    calc P.C_α * R ^ (3 / 2 : ℝ) * r_inf
        ≤ P.C_α * (B_R ^ (3 / 2 : ℝ) * c) * r_inf := by gcongr; exact P.hCα
      _ ≤ P.C_α * (B_R ^ (3 / 2 : ℝ) * c) * (P.C_0 * c ^ (1 / 3 : ℝ) * Real.exp (-P.κ * c)) :=
          mul_le_mul_of_nonneg_left hr_ub hCα_nn
      _ = P.C_α * B_R ^ (3 / 2 : ℝ) * P.C_0 * c ^ (4 / 3 : ℝ) * Real.exp (-P.κ * c) := by
          rw [← hc_c43]; ring
  have hsum : R * r_inf + C_line_err * c * Real.exp (-P.κ * c) + P.C_α * R ^ (3 / 2 : ℝ) * r_inf ≤
      M_exp * c ^ (4 / 3 : ℝ) * Real.exp (-P.κ * c) := by dsimp [M_exp]; linarith
  have hc53_le_c2 : c ^ (5 / 3 : ℝ) ≤ c ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast c 2]; exact Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
  have hM_le_exp : M_exp * c ^ (5 / 3 : ℝ) ≤ Real.exp (P.κ * c) := by
    have h1 : M_exp * c ^ 2 ≤ (P.κ * c) ^ 3 / (Nat.factorial 3 : ℝ) := by
      have hmul : 6 * M_exp ≤ P.κ ^ 3 * c := by linarith [(div_le_iff₀ (pow_pos P.hκ 3)).mp hc_exp]
      have hfac : (Nat.factorial 3 : ℝ) = 6 := by norm_num [Nat.factorial]
      rw [hfac, mul_pow]; nlinarith [sq_nonneg c]
    have hκc_nn : 0 ≤ P.κ * c := mul_nonneg hκ_pos.le hc_pos.le
    have hexp := (Finset.single_le_sum (fun i _ => by positivity)
      (Finset.mem_range.mpr (by norm_num : 3 < 4))).trans (Real.sum_le_exp_of_nonneg hκc_nn 4)
    have hM_nn : 0 ≤ M_exp := by dsimp [M_exp]; have := P.hCα; have := P.hC0.le; positivity
    exact (mul_le_mul_of_nonneg_left hc53_le_c2 hM_nn).trans (h1.trans hexp)
  have hsplit : c ^ (4 / 3 : ℝ) = c ^ (5 / 3 : ℝ) * c ^ (-(1 / 3 : ℝ)) := by
    rw [← Real.rpow_add hc_pos]; norm_num
  calc R * r_inf + C_line_err * c * Real.exp (-P.κ * c) + P.C_α * R ^ (3 / 2 : ℝ) * r_inf
      ≤ M_exp * c ^ (4 / 3 : ℝ) * Real.exp (-P.κ * c) := hsum
    _ = (M_exp * c ^ (5 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) * Real.exp (-P.κ * c) := by rw [hsplit]; ring
    _ ≤ Real.exp (P.κ * c) * c ^ (-(1 / 3 : ℝ)) * Real.exp (-P.κ * c) := by gcongr
    _ = c ^ (-(1 / 3 : ℝ)) := by
        rw [mul_right_comm, ← Real.exp_add, show P.κ * c + -P.κ * c = 0 by ring, Real.exp_zero, one_mul]

private lemma tebCThresh_spec (P : BootstrapParams) :
    ∀ {c L R r_inf C_line_err : ℝ},
      tebCThresh P ≤ c → 1 ≤ L → L ≤ P.C_L * c ^ P.γ →
      P.b ^ 2 * c ^ (2 / 3 : ℝ) ≤ R → R ≤ 2 * P.b ^ 2 * c ^ (2 / 3 : ℝ) + 1 →
      0 ≤ r_inf → r_inf ≤ P.C_0 * c ^ (1 / 3 : ℝ) * Real.exp (-P.κ * c) → C_line_err ≤ P.C_0 →
      let k₁ := tebK1 P L; let lam0 := tebLambda0 P
      (lam0 * (k₁ : ℝ) * c ^ (-(1 / 3 : ℝ)) ∈
          Set.Icc (P.D_1 * c ^ (-(1 / 3 : ℝ))) (min P.δ_star (min P.η_0 1))) ∧
        ((k₁ : ℝ) ≤ R / 5) ∧
        (R * r_inf + C_line_err * c * Real.exp (-P.κ * c) +
          P.C_α * R ^ (3 / 2 : ℝ) * r_inf ≤ c ^ (-(1 / 3 : ℝ))) := by
  intro c L R r_inf C_line_err hc hL1 hL_ub hR_lb hR_ub hr_nn hr_ub hCerr
  set m := min P.δ_star (min P.η_0 1)
  have hm_pos : 0 < m := lt_min P.hδ_star (lt_min P.hη0 zero_lt_one)
  have hc1 : 1 ≤ c := (le_max_left _ _).trans hc
  have hc_pos : 0 < c := by linarith
  have hlam0_pos : 0 < tebLambda0 P := tebLambda0_pos P
  have hCk_pos : 0 < tebCk P := lt_of_lt_of_le zero_lt_one (one_le_tebCk P)
  have hk1_ub := k1_le_tebCk_rpow P hc1 hL1 hL_ub
  have hc_ell : (tebLambda0 P * tebCk P / m) ^ 6 ≤ c :=
    (le_trans (le_max_left _ _) (le_max_right (1 : ℝ) _)).trans hc
  have hc_k1 : (5 * tebCk P / P.b ^ 2) ^ 2 ≤ c :=
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right (1 : ℝ) _))).trans hc
  have hc_exp : 6 * ((2 * P.b ^ 2 + 1) * P.C_0 + P.C_0 +
      P.C_α * (2 * P.b ^ 2 + 1) ^ (3 / 2 : ℝ) * P.C_0) / P.κ ^ 3 ≤ c :=
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right (1 : ℝ) _))).trans hc
  have hR_nn : 0 ≤ R := le_trans (by have := P.hb; positivity) hR_lb
  refine ⟨⟨?_, ?_⟩, ?_, teb_exp_error_absorption P hc1 hc_exp hR_nn hR_ub hr_nn hr_ub hCerr⟩
  · have hk0_pos : (0 : ℝ) < P.k_0 := Nat.cast_pos.mpr P.hk0
    have hD1_le : P.D_1 ≤ tebLambda0 P * (P.k_0 : ℝ) := by
      have h1 : P.D_1 / (P.k_0 : ℝ) ≤ tebLambda0 P := by rw [tebLambda0_eq]; exact le_max_right _ _
      calc P.D_1 = (P.D_1 / (P.k_0 : ℝ)) * (P.k_0 : ℝ) := (div_mul_cancel₀ _ hk0_pos.ne').symm
        _ ≤ tebLambda0 P * (P.k_0 : ℝ) := mul_le_mul_of_nonneg_right h1 hk0_pos.le
    have hk0_le : (P.k_0 : ℝ) ≤ (tebK1 P L : ℝ) := by exact_mod_cast le_max_left P.k_0 ⌈Real.log L⌉₊
    exact mul_le_mul_of_nonneg_right (hD1_le.trans (mul_le_mul_of_nonneg_left hk0_le hlam0_pos.le))
      (Real.rpow_nonneg hc_pos.le _)
  · have hbase_nn : 0 ≤ tebLambda0 P * tebCk P / m := by positivity
    have h16 := Real.rpow_le_rpow (by positivity) hc_ell (by positivity : 0 ≤ (1 / 6 : ℝ))
    rw [← Real.rpow_natCast _ 6, ← Real.rpow_mul hbase_nn] at h16; norm_num at h16
    have hm_le : tebLambda0 P * tebCk P ≤ m * c ^ (1 / 6 : ℝ) := by
      linarith [(div_le_iff₀ hm_pos).mp h16]
    have hc_prod : c ^ (1 / 6 : ℝ) * c ^ (-(1 / 3 : ℝ)) = c ^ (-(1 / 6 : ℝ)) := by
      rw [← Real.rpow_add hc_pos]; norm_num
    have hc16_prod : c ^ (1 / 6 : ℝ) * c ^ (-(1 / 6 : ℝ)) = 1 := by
      rw [← Real.rpow_add hc_pos, add_neg_cancel, Real.rpow_zero]
    calc tebLambda0 P * (tebK1 P L : ℝ) * c ^ (-(1 / 3 : ℝ))
        ≤ tebLambda0 P * (tebCk P * c ^ (1 / 6 : ℝ)) * c ^ (-(1 / 3 : ℝ)) := by gcongr
      _ = tebLambda0 P * tebCk P * c ^ (-(1 / 6 : ℝ)) := by rw [← hc_prod]; ring
      _ ≤ (m * c ^ (1 / 6 : ℝ)) * c ^ (-(1 / 6 : ℝ)) := by gcongr
      _ = m := by rw [mul_assoc, hc16_prod, mul_one]
  · have hb2_pos : 0 < P.b ^ 2 := sq_pos_of_pos P.hb
    have h12 := Real.rpow_le_rpow (by positivity) hc_k1 (by positivity : 0 ≤ (1 / 2 : ℝ))
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)] at h12; norm_num at h12
    have h5Ck : 5 * tebCk P ≤ P.b ^ 2 * c ^ (1 / 2 : ℝ) := by
      linarith [(div_le_iff₀ hb2_pos).mp h12]
    have hc_prod : c ^ (1 / 2 : ℝ) * c ^ (1 / 6 : ℝ) = c ^ (2 / 3 : ℝ) := by
      rw [← Real.rpow_add hc_pos]; norm_num
    calc (tebK1 P L : ℝ) ≤ tebCk P * c ^ (1 / 6 : ℝ) := hk1_ub
      _ ≤ (P.b ^ 2 * c ^ (1 / 2 : ℝ) / 5) * c ^ (1 / 6 : ℝ) := by gcongr; linarith
      _ = (P.b ^ 2 * c ^ (2 / 3 : ℝ)) / 5 := by rw [← hc_prod]; ring
      _ ≤ R / 5 := by gcongr

/-- Effective large-`c` threshold lemma for Theorem `TE.2`. -/
theorem teb_large_c_exists (P : BootstrapParams) :
    ∃ c_thresh : ℝ, 1 ≤ c_thresh ∧
      ∀ {c L R r_inf C_line_err : ℝ},
        c_thresh ≤ c → 1 ≤ L → L ≤ P.C_L * c ^ P.γ →
        P.b ^ 2 * c ^ (2 / 3 : ℝ) ≤ R → R ≤ 2 * P.b ^ 2 * c ^ (2 / 3 : ℝ) + 1 →
        0 ≤ r_inf → r_inf ≤ P.C_0 * c ^ (1 / 3 : ℝ) * Real.exp (-P.κ * c) →
        C_line_err ≤ P.C_0 →
        let k₁ := tebK1 P L; let lam0 := tebLambda0 P
        (lam0 * (k₁ : ℝ) * c ^ (-(1 / 3 : ℝ)) ∈
            Set.Icc (P.D_1 * c ^ (-(1 / 3 : ℝ))) (min P.δ_star (min P.η_0 1))) ∧
          ((k₁ : ℝ) ≤ R / 5) ∧
          (R * r_inf + C_line_err * c * Real.exp (-P.κ * c) +
            P.C_α * R ^ (3 / 2 : ℝ) * r_inf ≤ c ^ (-(1 / 3 : ℝ))) :=
  ⟨tebCThresh P, le_max_left _ _, tebCThresh_spec P⟩

/-- Canonical `c₂(P) ≥ 2` threshold for Theorem `TE.2`. -/
noncomputable def tebC2 (P : BootstrapParams) : ℝ := max 2 (tebCThresh P)

lemma two_le_tebC2 (P : BootstrapParams) : 2 ≤ tebC2 P := le_max_left _ _

end ParamsAndThreshold

/-! ### Part 2: Packaged Bootstrap Instances and Shared Core Bounds -/

section InstancesAndCore

/-- Shared `(TE.4)–(TE.5)` and `Arc_unc` structure for `BootstrapInstance` and `BootstrapHBInstance`. -/
structure BootstrapCore (P : BootstrapParams) where
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
  hI_line : ∀ k : ℕ, ∀ ℓ : ℝ, P.k_0 ≤ k → (k : ℝ) ≤ R / 5 →
    ℓ ∈ Set.Icc (P.D_1 * c ^ (-(1 / 3 : ℝ))) (min P.δ_star (min P.η_0 1)) →
    I_line k ℓ ≤ -(63 / 100 : ℝ) * B_1k k - B_2' k +
      P.C_a * ((k : ℝ) + 1) / R + R * r_inf + C_err * c * Real.exp (-P.κ * c)

/-- Standard 1/2-level bootstrap instance packaging `(B1)–(B2)` and `(TE.4)–(TE.6)`. -/
structure BootstrapInstance (P : BootstrapParams) extends BootstrapCore P where
  hP_nodes_lb : ∀ k : ℕ, ∀ ℓ : ℝ, P.k_0 ≤ k → (k : ℝ) ≤ R / 5 →
    ℓ ∈ Set.Icc (P.D_1 * c ^ (-(1 / 3 : ℝ))) (min P.δ_star (min P.η_0 1)) →
    -(P.C_1 / P.w_star) * ℓ - P.C_α * R ^ (3 / 2 : ℝ) * r_inf ≤ P_nodes k ℓ
  P_half_bound : ∀ k : ℕ, P.k_0 ≤ k → (k : ℝ) ≤ R / 5 →
    x_tilde / 2 ∈ Set.Icc (P.D_1 * c ^ (-(1 / 3 : ℝ))) (min P.δ_star (min P.η_0 1)) →
    (P.κ_star / (2 * P.w_star)) * x_tilde - P.C_α * R ^ (3 / 2 : ℝ) * r_inf ≤
      P_nodes k (x_tilde / 2)

/-- Effective node slope constant `Λ_N := 2 C₁ (1 / w_* + W_top)` in Theorem `TE.2(4)`. -/
noncomputable def tebLambdaN (P : BootstrapParams) (W_top : ℝ) : ℝ :=
  2 * P.C_1 * (1 / P.w_star + W_top)

/-- Effective step fraction `θ := min (1/2) (κ_* / (8 w_* C₁ (W_top + 1)))` in Theorem `TE.2(4)`. -/
noncomputable def tebThetaHB (P : BootstrapParams) (W_top : ℝ) : ℝ :=
  min (1 / 2) (P.κ_star / (8 * P.w_star * P.C_1 * (W_top + 1)))

lemma tebLambdaN_nonneg (P : BootstrapParams) {W_top : ℝ} (hW : 0 ≤ W_top) :
    0 ≤ tebLambdaN P W_top := by
  unfold tebLambdaN; have := P.hw_star; have := P.hC1; positivity

lemma tebThetaHB_pos (P : BootstrapParams) {W_top : ℝ} (hW : 0 ≤ W_top) :
    0 < tebThetaHB P W_top := by
  unfold tebThetaHB; have := P.hκ_star; have := P.hw_star; have := P.hC1
  exact lt_min (by norm_num) (by positivity)

lemma tebThetaHB_le_half (P : BootstrapParams) (W_top : ℝ) : tebThetaHB P W_top ≤ 1 / 2 :=
  min_le_left _ _

/-- Hermite–Biehler node-slope lower bound matching `.tex` line 282:
`κ_* / (2 w_*) - 2 C₁ W_top θ ≥ κ_* / (4 w_*)` for `W_top ≥ 0`. -/
lemma hb_theta_node_lower (P : BootstrapParams) {W_top : ℝ} (hW : 0 ≤ W_top) :
    P.κ_star / (4 * P.w_star) ≤
      P.κ_star / (2 * P.w_star) - 2 * P.C_1 * W_top * tebThetaHB P W_top := by
  have hw := P.hw_star; have hC1 := P.hC1
  have hθ_nn : 0 ≤ tebThetaHB P W_top := (tebThetaHB_pos P hW).le
  have h1 : 2 * P.C_1 * W_top * tebThetaHB P W_top ≤
      2 * P.C_1 * (W_top + 1) * (P.κ_star / (8 * P.w_star * P.C_1 * (W_top + 1))) := by
    calc 2 * P.C_1 * W_top * tebThetaHB P W_top
        ≤ 2 * P.C_1 * (W_top + 1) * tebThetaHB P W_top := by gcongr; linarith
      _ ≤ 2 * P.C_1 * (W_top + 1) * (P.κ_star / (8 * P.w_star * P.C_1 * (W_top + 1))) := by
          gcongr; exact min_le_right _ _
  have h2 : 2 * P.C_1 * (W_top + 1) * (P.κ_star / (8 * P.w_star * P.C_1 * (W_top + 1))) =
      P.κ_star / (4 * P.w_star) := by
    have hW1 : W_top + 1 ≠ 0 := by linarith
    field_simp [hw.ne', hC1.ne', hW1]; ring
  have h_half : P.κ_star / (4 * P.w_star) = P.κ_star / (2 * P.w_star) - P.κ_star / (4 * P.w_star) := by ring
  linarith

/-- All-level Hermite–Biehler bootstrap instance packaging `(B1)` and `(B2_HB)` (Theorem `TE.2(4)`). -/
structure BootstrapHBInstance (P : BootstrapParams) (W_top : ℝ) extends BootstrapCore P where
  hW_top : 0 ≤ W_top
  hP_nodes_lb_hb : ∀ k : ℕ, ∀ ℓ : ℝ, P.k_0 ≤ k → (k : ℝ) ≤ R / 5 →
    ℓ ∈ Set.Icc (P.D_1 * c ^ (-(1 / 3 : ℝ))) (min P.δ_star (min P.η_0 1)) →
    -tebLambdaN P W_top * ℓ - P.C_α * R ^ (3 / 2 : ℝ) * r_inf ≤ P_nodes k ℓ
  P_theta_bound : (P.k_0 : ℝ) ≤ R / 5 →
    tebThetaHB P W_top * x_tilde ∈
      Set.Icc (P.D_1 * c ^ (-(1 / 3 : ℝ))) (min P.δ_star (min P.η_0 1)) →
    (P.κ_star / (4 * P.w_star)) * x_tilde - P.C_α * R ^ (3 / 2 : ℝ) * r_inf ≤
      P_nodes P.k_0 (tebThetaHB P W_top * x_tilde)

private lemma core_R_ge (P : BootstrapParams) (I : BootstrapCore P) :
    P.b ^ 2 * I.c ^ (2 / 3 : ℝ) ≤ I.R := by
  have hc_nn : 0 ≤ I.c := by linarith [I.hc]
  have hnn : 0 ≤ P.b * I.c ^ (1 / 3 : ℝ) := mul_nonneg P.hb.le (Real.rpow_nonneg hc_nn _)
  have hsq : (P.b * I.c ^ (1 / 3 : ℝ)) ^ 2 ≤ I.a ^ 2 := by nlinarith [I.ha_lb]
  rw [I.ha_sq, mul_pow, ← Real.rpow_natCast (I.c ^ (1 / 3 : ℝ)) 2, ← Real.rpow_mul hc_nn] at hsq
  norm_num at hsq; exact hsq

private lemma core_a_inv_le (P : BootstrapParams) (I : BootstrapCore P) :
    I.a⁻¹ ≤ P.b⁻¹ * I.c ^ (-(1 / 3 : ℝ)) := by
  have hc_pos : 0 < I.c := by linarith [I.hc]
  have hp : 0 < P.b * I.c ^ (1 / 3 : ℝ) := mul_pos P.hb (Real.rpow_pos_of_pos hc_pos _)
  calc I.a⁻¹ ≤ (P.b * I.c ^ (1 / 3 : ℝ))⁻¹ := inv_anti₀ hp I.ha_lb
    _ = P.b⁻¹ * I.c ^ (-(1 / 3 : ℝ)) := by rw [mul_inv, ← Real.rpow_neg hc_pos.le]

private lemma core_R_inv_le (P : BootstrapParams) (I : BootstrapCore P) :
    I.R⁻¹ ≤ (P.b ^ 2)⁻¹ * I.c ^ (-(1 / 3 : ℝ)) := by
  have hc1 : 1 ≤ I.c := by linarith [I.hc]
  have hc_pos : 0 < I.c := by linarith
  have hR_lb13 : P.b ^ 2 * I.c ^ (1 / 3 : ℝ) ≤ I.R :=
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num))
      (sq_nonneg P.b)).trans (core_R_ge P I)
  have hb := P.hb
  calc I.R⁻¹ ≤ (P.b ^ 2 * I.c ^ (1 / 3 : ℝ))⁻¹ := inv_anti₀ (by positivity) hR_lb13
    _ = (P.b ^ 2)⁻¹ * I.c ^ (-(1 / 3 : ℝ)) := by rw [mul_inv, ← Real.rpow_neg hc_pos.le]

private lemma core_Arc_unc_le (P : BootstrapParams) (I : BootstrapCore P) :
    I.Arc_unc ≤ P.C_unc * I.c ^ (-(1 / 3 : ℝ)) :=
  I.hArc_unc.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by linarith [I.hc]) (by norm_num)) P.hCunc)

private lemma core_large_c_props (P : BootstrapParams) (I : BootstrapCore P) (hc : tebC2 P ≤ I.c) :
    (tebLambda0 P * (tebK1 P I.L : ℝ) * I.c ^ (-(1 / 3 : ℝ)) ∈
        Set.Icc (P.D_1 * I.c ^ (-(1 / 3 : ℝ))) (min P.δ_star (min P.η_0 1))) ∧
      ((tebK1 P I.L : ℝ) ≤ I.R / 5) ∧
      (I.R * I.r_inf + I.C_err * I.c * Real.exp (-P.κ * I.c) +
        P.C_α * I.R ^ (3 / 2 : ℝ) * I.r_inf ≤ I.c ^ (-(1 / 3 : ℝ))) :=
  tebCThresh_spec P ((le_max_right (2 : ℝ) _).trans hc) I.hL_lb I.hL_ub (core_R_ge P I)
    I.hR_ub I.hr_inf_nn I.hr_inf_ub I.hC_err_ub

/-- Generic `C_X` constant for part `(1)` given node slope bound `Λ ≥ 0`. -/
noncomputable def tebCXOf (P : BootstrapParams) (Λ : ℝ) : ℝ :=
  (100 / 63 : ℝ) * (Λ * tebLambda0 P * (P.k_0 : ℝ) +
    2 * P.C_a * (P.k_0 : ℝ) / P.b ^ 2 + 4 * P.C_a / P.b + P.C_unc + 1)

lemma tebCXOf_pos (P : BootstrapParams) {Λ : ℝ} (hΛ : 0 ≤ Λ) : 0 < tebCXOf P Λ := by
  unfold tebCXOf
  have hlam := (tebLambda0_pos P).le; have hCa := P.hCa; have hCunc := P.hCunc; have hb := P.hb
  positivity

private lemma teb_part1_of_core (P : BootstrapParams) (I : BootstrapCore P)
    (hc : tebC2 P ≤ I.c) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hP_lb : ∀ k : ℕ, ∀ ℓ : ℝ, P.k_0 ≤ k → (k : ℝ) ≤ I.R / 5 →
      ℓ ∈ Set.Icc (P.D_1 * I.c ^ (-(1 / 3 : ℝ))) (min P.δ_star (min P.η_0 1)) →
      -Λ * ℓ - P.C_α * I.R ^ (3 / 2 : ℝ) * I.r_inf ≤ I.P_nodes k ℓ) :
    I.B_1 + I.B_2 ≤ tebCXOf P Λ * (1 + Real.log I.L) * I.c ^ (-(1 / 3 : ℝ)) := by
  set k₁ := tebK1 P I.L
  set lam0 := tebLambda0 P
  set ℓ := lam0 * (k₁ : ℝ) * I.c ^ (-(1 / 3 : ℝ))
  have hc_pos : 0 < I.c := by linarith [I.hc]
  have h1log_ge1 : 1 ≤ 1 + Real.log I.L := by linarith [Real.log_nonneg I.hL_lb]
  obtain ⟨hℓ_mem, hk1_le_R5, h_exp_abs⟩ := core_large_c_props P I hc
  have hk1_ge : P.k_0 ≤ k₁ := le_max_left _ _
  have hk1_pos : 1 ≤ k₁ := P.hk0.trans hk1_ge
  have hlam0_pos : 0 < lam0 := tebLambda0_pos P
  have hℓ_pos : 0 < ℓ := mul_pos (mul_pos hlam0_pos (Nat.cast_pos.mpr hk1_pos)) (Real.rpow_pos_of_pos hc_pos _)
  have ha_pos : 0 < I.a := by
    have : 0 < P.b * I.c ^ (1 / 3 : ℝ) := mul_pos P.hb (Real.rpow_pos_of_pos hc_pos _)
    linarith [I.ha_lb]
  have hla : (Real.pi / 2) * (k₁ : ℝ) ≤ ℓ * I.a := by
    have hlam0_lb : Real.pi / (2 * P.b) ≤ lam0 := by dsimp [lam0]; rw [tebLambda0_eq]; exact le_max_left _ _
    have hc_inv : I.c ^ (-(1 / 3 : ℝ)) * I.c ^ (1 / 3 : ℝ) = 1 := by
      rw [← Real.rpow_add hc_pos, neg_add_cancel, Real.rpow_zero]
    have hlam_nn : 0 ≤ lam0 * (k₁ : ℝ) * I.c ^ (-(1 / 3 : ℝ)) := by positivity
    have hb_nn : 0 ≤ P.b * I.c ^ (1 / 3 : ℝ) := by have := P.hb; positivity
    calc (Real.pi / 2) * (k₁ : ℝ)
        = (Real.pi / (2 * P.b)) * (k₁ : ℝ) * I.c ^ (-(1 / 3 : ℝ)) * (P.b * I.c ^ (1 / 3 : ℝ)) := by
          calc (Real.pi / 2) * (k₁ : ℝ)
              = (Real.pi / (2 * P.b)) * (k₁ : ℝ) * (I.c ^ (-(1 / 3 : ℝ)) * I.c ^ (1 / 3 : ℝ)) * P.b := by
                rw [hc_inv]; field_simp [P.hb.ne']
            _ = _ := by ring
      _ ≤ lam0 * (k₁ : ℝ) * I.c ^ (-(1 / 3 : ℝ)) * (P.b * I.c ^ (1 / 3 : ℝ)) := by gcongr
      _ ≤ lam0 * (k₁ : ℝ) * I.c ^ (-(1 / 3 : ℝ)) * I.a := mul_le_mul_of_nonneg_left I.ha_lb hlam_nn
  have hstir := teb_stirling_bound hk1_pos hℓ_pos ha_pos hla
  have hexp_k1 : Real.exp (-(k₁ : ℝ)) ≤ 1 / I.L := by
    have hlog_le : Real.log I.L ≤ (k₁ : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_max_right P.k_0 ⌈Real.log I.L⌉₊)
    calc Real.exp (-(k₁ : ℝ)) ≤ Real.exp (-Real.log I.L) := Real.exp_le_exp.mpr (by linarith)
      _ = 1 / I.L := by rw [Real.exp_neg, Real.exp_log (by linarith [I.hL_lb]), one_div]
  have hArc_cov_le : I.Arc_cov k₁ ℓ ≤ (4 * P.C_a / P.b) * (1 + Real.log I.L) * I.c ^ (-(1 / 3 : ℝ)) := by
    have hCaL_nn : 0 ≤ P.C_a * I.L * I.a⁻¹ := by have := P.hCa; have := I.hL_lb; positivity
    have hL_pos : 0 < I.L := by linarith [I.hL_lb]
    have h4Ca_nn : 0 ≤ 4 * P.C_a := by linarith [P.hCa]
    calc I.Arc_cov k₁ ℓ
        ≤ P.C_a * I.L * I.a⁻¹ * (4 * Real.exp (-(k₁ : ℝ))) :=
          (I.hArc_cov k₁ ℓ hk1_ge hk1_le_R5 hℓ_mem).trans (mul_le_mul_of_nonneg_left hstir hCaL_nn)
      _ ≤ P.C_a * I.L * I.a⁻¹ * (4 * (1 / I.L)) := by gcongr
      _ = 4 * P.C_a * I.a⁻¹ := by field_simp [hL_pos.ne']
      _ ≤ 4 * P.C_a * (P.b⁻¹ * I.c ^ (-(1 / 3 : ℝ))) := mul_le_mul_of_nonneg_left (core_a_inv_le P I) h4Ca_nn
      _ = (4 * P.C_a / P.b) * 1 * I.c ^ (-(1 / 3 : ℝ)) := by ring
      _ ≤ (4 * P.C_a / P.b) * (1 + Real.log I.L) * I.c ^ (-(1 / 3 : ℝ)) := by
          gcongr; exact div_nonneg (by linarith [P.hCa]) P.hb.le
  have hArc_unc_le : I.Arc_unc ≤ P.C_unc * (1 + Real.log I.L) * I.c ^ (-(1 / 3 : ℝ)) := by
    calc I.Arc_unc ≤ P.C_unc * 1 * I.c ^ (-(1 / 3 : ℝ)) := by
          simpa [mul_one] using core_Arc_unc_le P I
      _ ≤ P.C_unc * (1 + Real.log I.L) * I.c ^ (-(1 / 3 : ℝ)) := by gcongr; exact P.hCunc
  have hk1_le_log : (k₁ : ℝ) ≤ (P.k_0 : ℝ) * (1 + Real.log I.L) := by
    have hk0_ge1 : (1 : ℝ) ≤ P.k_0 := by exact_mod_cast P.hk0
    have h1 : (P.k_0 : ℝ) ≤ (P.k_0 : ℝ) * (1 + Real.log I.L) :=
      le_mul_of_one_le_right (by positivity) h1log_ge1
    have h2 : (⌈Real.log I.L⌉₊ : ℝ) ≤ (P.k_0 : ℝ) * (1 + Real.log I.L) := by
      have hceil := Nat.ceil_lt_add_one (Real.log_nonneg I.hL_lb)
      nlinarith
    have hmax : (k₁ : ℝ) = max (P.k_0 : ℝ) (⌈Real.log I.L⌉₊ : ℝ) := by
      dsimp [k₁, tebK1]; push_cast [Nat.cast_max]; rfl
    rw [hmax]; exact max_le h1 h2
  have hLine_k_le : P.C_a * ((k₁ : ℝ) + 1) / I.R ≤
      (2 * P.C_a * (P.k_0 : ℝ) / P.b ^ 2) * (1 + Real.log I.L) * I.c ^ (-(1 / 3 : ℝ)) := by
    have hk1_plus : (k₁ : ℝ) + 1 ≤ 2 * (P.k_0 : ℝ) * (1 + Real.log I.L) := by
      have : (1 : ℝ) ≤ k₁ := by exact_mod_cast hk1_pos
      linarith
    have hR_nn : 0 ≤ I.R⁻¹ := inv_nonneg.mpr (le_trans (by have := P.hb; positivity) (core_R_ge P I))
    have hCa_k_nn : 0 ≤ P.C_a * (2 * (P.k_0 : ℝ) * (1 + Real.log I.L)) := by have := P.hCa; positivity
    calc P.C_a * ((k₁ : ℝ) + 1) / I.R
        = P.C_a * ((k₁ : ℝ) + 1) * I.R⁻¹ := div_eq_mul_inv _ _
      _ ≤ P.C_a * (2 * (P.k_0 : ℝ) * (1 + Real.log I.L)) * I.R⁻¹ := by gcongr; exact P.hCa
      _ ≤ P.C_a * (2 * (P.k_0 : ℝ) * (1 + Real.log I.L)) * ((P.b ^ 2)⁻¹ * I.c ^ (-(1 / 3 : ℝ))) :=
          mul_le_mul_of_nonneg_left (core_R_inv_le P I) hCa_k_nn
      _ = (2 * P.C_a * (P.k_0 : ℝ) / P.b ^ 2) * (1 + Real.log I.L) * I.c ^ (-(1 / 3 : ℝ)) := by ring
  have hLam_ell_le : Λ * ℓ ≤ (Λ * lam0 * (P.k_0 : ℝ)) * (1 + Real.log I.L) * I.c ^ (-(1 / 3 : ℝ)) := by
    calc Λ * (lam0 * (k₁ : ℝ) * I.c ^ (-(1 / 3 : ℝ)))
        ≤ Λ * (lam0 * ((P.k_0 : ℝ) * (1 + Real.log I.L)) * I.c ^ (-(1 / 3 : ℝ))) := by gcongr
      _ = (Λ * lam0 * (P.k_0 : ℝ)) * (1 + Real.log I.L) * I.c ^ (-(1 / 3 : ℝ)) := by ring
  have hexp_le : I.R * I.r_inf + I.C_err * I.c * Real.exp (-P.κ * I.c) +
      P.C_α * I.R ^ (3 / 2 : ℝ) * I.r_inf ≤ 1 * (1 + Real.log I.L) * I.c ^ (-(1 / 3 : ℝ)) := by
    calc I.R * I.r_inf + I.C_err * I.c * Real.exp (-P.κ * I.c) + P.C_α * I.R ^ (3 / 2 : ℝ) * I.r_inf
        ≤ 1 * 1 * I.c ^ (-(1 / 3 : ℝ)) := by simpa only [one_mul] using h_exp_abs
      _ ≤ 1 * (1 + Real.log I.L) * I.c ^ (-(1 / 3 : ℝ)) := by gcongr
  have hP_comb : (63 / 100 : ℝ) * I.B_1k k₁ + I.B_2' k₁ ≤
      Λ * ℓ + P.C_a * ((k₁ : ℝ) + 1) / I.R +
        (I.R * I.r_inf + I.C_err * I.c * Real.exp (-P.κ * I.c) + P.C_α * I.R ^ (3 / 2 : ℝ) * I.r_inf) +
        I.Arc_cov k₁ ℓ + I.Arc_unc := by
    linarith [hP_lb k₁ ℓ hk1_ge hk1_le_R5 hℓ_mem, I.hP_le k₁ ℓ hk1_ge hk1_le_R5 hℓ_mem,
      I.hI_line k₁ ℓ hk1_ge hk1_le_R5 hℓ_mem]
  have hB_comb : (63 / 100 : ℝ) * (I.B_1 + I.B_2) ≤ (63 / 100 : ℝ) * I.B_1k k₁ + I.B_2' k₁ := by
    nlinarith [I.hB_sum k₁ hk1_ge hk1_le_R5, I.hB2'_nn k₁ hk1_ge hk1_le_R5]
  have h63 : (63 / 100 : ℝ) * (I.B_1 + I.B_2) ≤
      (Λ * lam0 * (P.k_0 : ℝ) + 2 * P.C_a * (P.k_0 : ℝ) / P.b ^ 2 +
        4 * P.C_a / P.b + P.C_unc + 1) * (1 + Real.log I.L) * I.c ^ (-(1 / 3 : ℝ)) := by linarith
  calc I.B_1 + I.B_2
      = (100 / 63 : ℝ) * ((63 / 100 : ℝ) * (I.B_1 + I.B_2)) := by ring
    _ ≤ (100 / 63 : ℝ) * ((Λ * lam0 * (P.k_0 : ℝ) + 2 * P.C_a * (P.k_0 : ℝ) / P.b ^ 2 +
          4 * P.C_a / P.b + P.C_unc + 1) * (1 + Real.log I.L) * I.c ^ (-(1 / 3 : ℝ))) :=
        mul_le_mul_of_nonneg_left h63 (by norm_num)
    _ = tebCXOf P Λ * (1 + Real.log I.L) * I.c ^ (-(1 / 3 : ℝ)) := by unfold tebCXOf; ring

private lemma teb_part2_of_part1 (P : BootstrapParams) (I : BootstrapCore P)
    {C_X : ℝ} (h1 : I.B_1 + I.B_2 ≤ C_X * (1 + Real.log I.L) * I.c ^ (-(1 / 3 : ℝ)))
    (hB3 : I.L ≤ P.C_fb * (I.c ^ (1 / 3 : ℝ) * (I.B_1 + I.B_2) + 1)) :
    I.L ≤ tebLogSharp (max 1 (P.C_fb * (C_X + 1))) := by
  have hc_pos : 0 < I.c := by linarith [I.hc]
  have hc_cancel : I.c ^ (1 / 3 : ℝ) * I.c ^ (-(1 / 3 : ℝ)) = 1 := by
    rw [← Real.rpow_add hc_pos, add_neg_cancel, Real.rpow_zero]
  have hcB_le : I.c ^ (1 / 3 : ℝ) * (I.B_1 + I.B_2) ≤ C_X * (1 + Real.log I.L) := by
    calc I.c ^ (1 / 3 : ℝ) * (I.B_1 + I.B_2)
        ≤ I.c ^ (1 / 3 : ℝ) * (C_X * (1 + Real.log I.L) * I.c ^ (-(1 / 3 : ℝ))) :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hc_pos.le _)
      _ = C_X * (1 + Real.log I.L) * (I.c ^ (1 / 3 : ℝ) * I.c ^ (-(1 / 3 : ℝ))) := by ring
      _ = C_X * (1 + Real.log I.L) := by rw [hc_cancel, mul_one]
  have h1log : 1 ≤ 1 + Real.log I.L := by linarith [Real.log_nonneg I.hL_lb]
  have hCstar_ge : P.C_fb * (C_X + 1) ≤ max 1 (P.C_fb * (C_X + 1)) := le_max_right _ _
  have hL_log : I.L ≤ max 1 (P.C_fb * (C_X + 1)) * (1 + Real.log I.L) := by
    calc I.L ≤ P.C_fb * (I.c ^ (1 / 3 : ℝ) * (I.B_1 + I.B_2) + 1) := hB3
      _ ≤ P.C_fb * (C_X * (1 + Real.log I.L) + (1 + Real.log I.L)) := by
          gcongr; exact le_trans (by norm_num) P.hCfb
      _ = P.C_fb * (C_X + 1) * (1 + Real.log I.L) := by ring
      _ ≤ max 1 (P.C_fb * (C_X + 1)) * (1 + Real.log I.L) := by gcongr
  exact log_bootstrap_bound (le_max_left _ _) I.hL_lb hL_log

/-- Generic `A` constant for part `(3)` with step fraction `θ > 0` and node slope `κ_eff > 0`. -/
noncomputable def tebAOf (P : BootstrapParams) (θ κ_eff : ℝ) : ℝ :=
  max ((P.C_a * ((P.k_0 : ℝ) + 1) / P.b ^ 2 + 1 + P.C_unc) / κ_eff)
    ((P.C_a / P.b * ((2 : ℝ) ^ (P.k_0 + 1) * Real.Gamma ((P.k_0 : ℝ) + 1 / 2) *
      (Real.pi / (4 * θ * P.b)) ^ ((P.k_0 : ℝ) + 1 / 2))) / κ_eff)

lemma tebAOf_pos (P : BootstrapParams) {θ κ_eff : ℝ} (hκ : 0 < κ_eff) :
    0 < tebAOf P θ κ_eff := by
  unfold tebAOf; have := P.hCa; have := P.hCunc; have := P.hb
  exact lt_of_lt_of_le (div_pos (by positivity) hκ) (le_max_left _ _)

private lemma teb_part3_of_core (P : BootstrapParams) (I : BootstrapCore P)
    (hc : tebC2 P ≤ I.c) {θ κ_eff L_sharp : ℝ}
    (hθ_pos : 0 < θ) (hθ_le : θ ≤ 1) (hκ_pos : 0 < κ_eff)
    (hL_nn : 0 ≤ L_sharp) (hL_le : I.L ≤ L_sharp)
    (hP_theta : (P.k_0 : ℝ) ≤ I.R / 5 →
      θ * I.x_tilde ∈ Set.Icc (P.D_1 * I.c ^ (-(1 / 3 : ℝ))) (min P.δ_star (min P.η_0 1)) →
      κ_eff * I.x_tilde - P.C_α * I.R ^ (3 / 2 : ℝ) * I.r_inf ≤ I.P_nodes P.k_0 (θ * I.x_tilde)) :
    I.c ^ (1 / 3 : ℝ) * I.x_tilde ≤
      max (P.D_1 / θ) (max 1 (max (2 * tebAOf P θ κ_eff)
        ((2 * tebAOf P θ κ_eff * L_sharp) ^ (1 / ((P.k_0 : ℝ) + 3 / 2))))) := by
  set K := I.c ^ (1 / 3 : ℝ) * I.x_tilde
  have hc_pos : 0 < I.c := by linarith [I.hc]
  have hK_pos : 0 < K := mul_pos (Real.rpow_pos_of_pos hc_pos _) I.hx_pos
  rcases le_or_gt K (P.D_1 / θ) with hK_small | hK_large
  · exact hK_small.trans (le_max_left _ _)
  · set ℓ := θ * I.x_tilde
    have hc_cancel : I.c ^ (1 / 3 : ℝ) * I.c ^ (-(1 / 3 : ℝ)) = 1 := by
      rw [← Real.rpow_add hc_pos, add_neg_cancel, Real.rpow_zero]
    have hℓ_lb : P.D_1 * I.c ^ (-(1 / 3 : ℝ)) ≤ ℓ := by
      have h1 : P.D_1 < θ * K := (div_lt_iff₀' hθ_pos).mp hK_large
      have h2 : P.D_1 ≤ I.c ^ (1 / 3 : ℝ) * ℓ := by dsimp [K, ℓ] at h1 ⊢; linarith
      calc P.D_1 * I.c ^ (-(1 / 3 : ℝ)) ≤ (I.c ^ (1 / 3 : ℝ) * ℓ) * I.c ^ (-(1 / 3 : ℝ)) := by gcongr
        _ = ℓ := by rw [mul_comm (I.c ^ (1 / 3 : ℝ)), mul_assoc, hc_cancel, mul_one]
    have hℓ_mem : ℓ ∈ Set.Icc (P.D_1 * I.c ^ (-(1 / 3 : ℝ))) (min P.δ_star (min P.η_0 1)) :=
      ⟨hℓ_lb, (by dsimp [ℓ]; nlinarith [I.hx_pos] : ℓ ≤ I.x_tilde).trans I.hx_ub⟩
    obtain ⟨_, hk1_le_R5, h_exp_abs⟩ := core_large_c_props P I hc
    have hk0_le_R5 : (P.k_0 : ℝ) ≤ I.R / 5 :=
      (show (P.k_0 : ℝ) ≤ (tebK1 P I.L : ℝ) from by exact_mod_cast le_max_left _ _).trans hk1_le_R5
    have hℓ_pos : 0 < ℓ := mul_pos hθ_pos I.hx_pos
    have ha_pos : 0 < I.a := by
      have : 0 < P.b * I.c ^ (1 / 3 : ℝ) := mul_pos P.hb (Real.rpow_pos_of_pos hc_pos _)
      linarith [I.ha_lb]
    have hℓa_lb : θ * P.b * K ≤ ℓ * I.a := by
      have h1 : θ * I.x_tilde * (P.b * I.c ^ (1 / 3 : ℝ)) ≤ θ * I.x_tilde * I.a := by
        gcongr; exact I.ha_lb
      dsimp [ℓ, K]; linarith
    have hc13_nn : 0 ≤ I.c ^ (1 / 3 : ℝ) := Real.rpow_nonneg hc_pos.le _
    set M_cov : ℝ := P.C_a / P.b * ((2 : ℝ) ^ (P.k_0 + 1) * Real.Gamma ((P.k_0 : ℝ) + 1 / 2) *
      (Real.pi / (4 * θ * P.b)) ^ ((P.k_0 : ℝ) + 1 / 2))
    have hArc_cov_le : I.c ^ (1 / 3 : ℝ) * I.Arc_cov P.k_0 ℓ ≤
        M_cov * L_sharp * K ^ (-((P.k_0 : ℝ) + 1 / 2)) := by
      have hb := P.hb; have hCa := P.hCa
      have harg : Real.pi / (4 * ℓ * I.a) ≤ (Real.pi / (4 * θ * P.b)) * K⁻¹ := by
        calc Real.pi / (4 * ℓ * I.a)
            ≤ Real.pi / (4 * (θ * P.b * K)) := div_le_div_of_nonneg_left Real.pi_pos.le (by positivity) (by linarith)
          _ = (Real.pi / (4 * θ * P.b)) * K⁻¹ := by ring
      have hpow_le : (Real.pi / (4 * ℓ * I.a)) ^ ((P.k_0 : ℝ) + 1 / 2) ≤
          (Real.pi / (4 * θ * P.b)) ^ ((P.k_0 : ℝ) + 1 / 2) * K ^ (-((P.k_0 : ℝ) + 1 / 2)) := by
        have h1 := Real.rpow_le_rpow (by positivity) harg (by positivity : 0 ≤ (P.k_0 : ℝ) + 1 / 2)
        rwa [Real.mul_rpow (by positivity) (inv_nonneg.mpr hK_pos.le),
          Real.inv_rpow hK_pos.le, ← Real.rpow_neg hK_pos.le] at h1
      have ha_inv_c : I.c ^ (1 / 3 : ℝ) * I.a⁻¹ ≤ P.b⁻¹ := by
        calc I.c ^ (1 / 3 : ℝ) * I.a⁻¹ ≤ I.c ^ (1 / 3 : ℝ) * (P.b⁻¹ * I.c ^ (-(1 / 3 : ℝ))) :=
              mul_le_mul_of_nonneg_left (core_a_inv_le P I) hc13_nn
          _ = P.b⁻¹ := by rw [mul_comm (P.b⁻¹), ← mul_assoc, hc_cancel, one_mul]
      have hgam_nn : 0 ≤ Real.Gamma ((P.k_0 : ℝ) + 1 / 2) := (Real.Gamma_pos_of_pos (by positivity)).le
      have h2g_nn : 0 ≤ (2 : ℝ) ^ (P.k_0 + 1) * Real.Gamma ((P.k_0 : ℝ) + 1 / 2) := by positivity
      have hCaIa_nn : 0 ≤ P.C_a * I.L * I.a⁻¹ := by have := I.hL_lb; positivity
      have hcov1 : I.Arc_cov P.k_0 ℓ ≤
          P.C_a * L_sharp * I.a⁻¹ * ((2 : ℝ) ^ (P.k_0 + 1) * Real.Gamma ((P.k_0 : ℝ) + 1 / 2) *
            ((Real.pi / (4 * θ * P.b)) ^ ((P.k_0 : ℝ) + 1 / 2) * K ^ (-((P.k_0 : ℝ) + 1 / 2)))) := by
        have hstep1 := (I.hArc_cov P.k_0 ℓ le_rfl hk0_le_R5 hℓ_mem).trans
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow_le h2g_nn) hCaIa_nn)
        have hfac_nn : 0 ≤ (2 : ℝ) ^ (P.k_0 + 1) * Real.Gamma ((P.k_0 : ℝ) + 1 / 2) *
            ((Real.pi / (4 * θ * P.b)) ^ ((P.k_0 : ℝ) + 1 / 2) * K ^ (-((P.k_0 : ℝ) + 1 / 2))) := by positivity
        exact hstep1.trans (by gcongr)
      have hmid_nn : 0 ≤ (2 : ℝ) ^ (P.k_0 + 1) * Real.Gamma ((P.k_0 : ℝ) + 1 / 2) *
          (Real.pi / (4 * θ * P.b)) ^ ((P.k_0 : ℝ) + 1 / 2) := by positivity
      calc I.c ^ (1 / 3 : ℝ) * I.Arc_cov P.k_0 ℓ
          ≤ (P.C_a * (I.c ^ (1 / 3 : ℝ) * I.a⁻¹)) *
              ((2 : ℝ) ^ (P.k_0 + 1) * Real.Gamma ((P.k_0 : ℝ) + 1 / 2) *
                (Real.pi / (4 * θ * P.b)) ^ ((P.k_0 : ℝ) + 1 / 2)) *
              L_sharp * K ^ (-((P.k_0 : ℝ) + 1 / 2)) := by
            have := mul_le_mul_of_nonneg_left hcov1 hc13_nn; linarith
        _ ≤ (P.C_a * P.b⁻¹) *
              ((2 : ℝ) ^ (P.k_0 + 1) * Real.Gamma ((P.k_0 : ℝ) + 1 / 2) *
                (Real.pi / (4 * θ * P.b)) ^ ((P.k_0 : ℝ) + 1 / 2)) *
              L_sharp * K ^ (-((P.k_0 : ℝ) + 1 / 2)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ha_inv_c hCa) hmid_nn) hL_nn)
              (Real.rpow_nonneg hK_pos.le _)
        _ = M_cov * L_sharp * K ^ (-((P.k_0 : ℝ) + 1 / 2)) := by dsimp [M_cov]; rw [← div_eq_mul_inv P.C_a P.b]
    have hLine_c_le : I.c ^ (1 / 3 : ℝ) * (P.C_a * ((P.k_0 : ℝ) + 1) / I.R) ≤
        P.C_a * ((P.k_0 : ℝ) + 1) / P.b ^ 2 := by
      have hCa_nn : 0 ≤ P.C_a * ((P.k_0 : ℝ) + 1) := mul_nonneg P.hCa (by positivity)
      calc I.c ^ (1 / 3 : ℝ) * (P.C_a * ((P.k_0 : ℝ) + 1) / I.R)
          = P.C_a * ((P.k_0 : ℝ) + 1) * (I.c ^ (1 / 3 : ℝ) * I.R⁻¹) := by rw [div_eq_mul_inv]; ring
        _ ≤ P.C_a * ((P.k_0 : ℝ) + 1) * (I.c ^ (1 / 3 : ℝ) * ((P.b ^ 2)⁻¹ * I.c ^ (-(1 / 3 : ℝ)))) := by
            gcongr; exact core_R_inv_le P I
        _ = P.C_a * ((P.k_0 : ℝ) + 1) * (P.b ^ 2)⁻¹ * (I.c ^ (1 / 3 : ℝ) * I.c ^ (-(1 / 3 : ℝ))) := by ring
        _ = P.C_a * ((P.k_0 : ℝ) + 1) / P.b ^ 2 := by rw [hc_cancel, mul_one, div_eq_mul_inv]
    have hUnc_c_le : I.c ^ (1 / 3 : ℝ) * I.Arc_unc ≤ P.C_unc := by
      calc I.c ^ (1 / 3 : ℝ) * I.Arc_unc
          ≤ I.c ^ (1 / 3 : ℝ) * (P.C_unc * I.c ^ (-(1 / 3 : ℝ))) :=
            mul_le_mul_of_nonneg_left (core_Arc_unc_le P I) hc13_nn
        _ = P.C_unc := by rw [mul_comm P.C_unc, ← mul_assoc, hc_cancel, one_mul]
    have hexp_c_le : I.c ^ (1 / 3 : ℝ) * (I.R * I.r_inf + I.C_err * I.c * Real.exp (-P.κ * I.c) +
        P.C_α * I.R ^ (3 / 2 : ℝ) * I.r_inf) ≤ 1 :=
      (mul_le_mul_of_nonneg_left h_exp_abs hc13_nn).trans hc_cancel.le
    have hcomb0 : κ_eff * I.x_tilde ≤ P.C_a * ((P.k_0 : ℝ) + 1) / I.R +
        (I.R * I.r_inf + I.C_err * I.c * Real.exp (-P.κ * I.c) + P.C_α * I.R ^ (3 / 2 : ℝ) * I.r_inf) +
        I.Arc_cov P.k_0 ℓ + I.Arc_unc := by
      linarith [hP_theta hk0_le_R5 hℓ_mem, I.hP_le P.k_0 ℓ le_rfl hk0_le_R5 hℓ_mem,
        I.hI_line P.k_0 ℓ le_rfl hk0_le_R5 hℓ_mem, I.hB1k_nn P.k_0 le_rfl hk0_le_R5,
        I.hB2'_nn P.k_0 le_rfl hk0_le_R5]
    have hcomb2 : κ_eff * K ≤ (P.C_a * ((P.k_0 : ℝ) + 1) / P.b ^ 2 + 1 + P.C_unc) +
        M_cov * L_sharp * K ^ (-((P.k_0 : ℝ) + 1 / 2)) := by
      have := mul_le_mul_of_nonneg_left hcomb0 hc13_nn
      dsimp [K] at *; linarith
    set A := tebAOf P θ κ_eff
    have hA_pos : 0 < A := tebAOf_pos P hκ_pos
    have h_abs_ineq : K ≤ A * (1 + L_sharp * K ^ (-((P.k_0 : ℝ) + 1 / 2))) := by
      have h1 : (P.C_a * ((P.k_0 : ℝ) + 1) / P.b ^ 2 + 1 + P.C_unc) / κ_eff ≤ A := le_max_left _ _
      have h2 : M_cov / κ_eff ≤ A := le_max_right _ _
      have hKL_nn : 0 ≤ L_sharp * K ^ (-((P.k_0 : ℝ) + 1 / 2)) :=
        mul_nonneg hL_nn (Real.rpow_nonneg hK_pos.le _)
      calc K = (κ_eff * K) / κ_eff := by field_simp [hκ_pos.ne']
        _ ≤ ((P.C_a * ((P.k_0 : ℝ) + 1) / P.b ^ 2 + 1 + P.C_unc) +
              M_cov * L_sharp * K ^ (-((P.k_0 : ℝ) + 1 / 2))) / κ_eff :=
            div_le_div_of_nonneg_right hcomb2 hκ_pos.le
        _ = (P.C_a * ((P.k_0 : ℝ) + 1) / P.b ^ 2 + 1 + P.C_unc) / κ_eff +
              (M_cov / κ_eff) * (L_sharp * K ^ (-((P.k_0 : ℝ) + 1 / 2))) := by ring
        _ ≤ A + A * (L_sharp * K ^ (-((P.k_0 : ℝ) + 1 / 2))) := by gcongr
        _ = A * (1 + L_sharp * K ^ (-((P.k_0 : ℝ) + 1 / 2))) := by ring
    exact (poly_absorption_bound P.k_0 hA_pos hL_nn hK_pos h_abs_ineq).trans (le_max_right _ _)

end InstancesAndCore

/-! ### Part 3: Theorem TE.2 Parts (1)–(4) -/

section BootstrapTheorems

/-- Explicit `C_X`, `C_*`, `L_♯`, `A` constants for Theorem `TE.2(1)–(3)`. -/
noncomputable def tebCX (P : BootstrapParams) : ℝ := tebCXOf P (P.C_1 / P.w_star)
lemma tebCX_pos (P : BootstrapParams) : 0 < tebCX P := tebCXOf_pos P (div_nonneg P.hC1.le P.hw_star.le)
noncomputable def tebCStar (P : BootstrapParams) : ℝ := max 1 (P.C_fb * (tebCX P + 1))
noncomputable def tebLSharp (P : BootstrapParams) : ℝ := tebLogSharp (tebCStar P)
noncomputable def tebAPart3 (P : BootstrapParams) : ℝ := tebAOf P (1 / 2) (P.κ_star / (2 * P.w_star))

/-- **Theorem TE.2(1)**: Under `(B1)–(B2)`, for `c ≥ tebC2 P`, `B₁ + B₂ ≤ C_X (1 + log L) c^{-1/3}`. -/
theorem teb_bootstrap_part1 (P : BootstrapParams) (I : BootstrapInstance P) (hc : tebC2 P ≤ I.c) :
    I.B_1 + I.B_2 ≤ tebCX P * (1 + Real.log I.L) * I.c ^ (-(1 / 3 : ℝ)) :=
  teb_part1_of_core P I.toBootstrapCore hc (div_nonneg P.hC1.le P.hw_star.le) I.hP_nodes_lb

/-- **Theorem TE.2(2)**: Adding `(B3)`, deduce `L ≤ tebLogSharp (max 1 (C_fb (C_X + 1)))`. -/
theorem teb_bootstrap_part2 (P : BootstrapParams) (I : BootstrapInstance P) (hc : tebC2 P ≤ I.c)
    (hB3 : I.L ≤ P.C_fb * (I.c ^ (1 / 3 : ℝ) * (I.B_1 + I.B_2) + 1)) :
    I.L ≤ tebLogSharp (tebCStar P) :=
  teb_part2_of_part1 P I.toBootstrapCore (teb_bootstrap_part1 P I hc) hB3

/-- **Theorem TE.2(3)**: Adding `(B3)` and `(TE.6)` at `x_tilde / 2`, deduce
`K = c^{1/3} x_tilde ≤ max (2 D₁) (max 1 (max (2 A) ((2 A L_♯)^{1 / (k₀ + 3/2)})))`. -/
theorem teb_bootstrap_part3 (P : BootstrapParams) (I : BootstrapInstance P) (hc : tebC2 P ≤ I.c)
    (hB3 : I.L ≤ P.C_fb * (I.c ^ (1 / 3 : ℝ) * (I.B_1 + I.B_2) + 1)) :
    I.c ^ (1 / 3 : ℝ) * I.x_tilde ≤
      max (2 * P.D_1) (max 1 (max (2 * tebAPart3 P)
        ((2 * tebAPart3 P * tebLSharp P) ^ (1 / ((P.k_0 : ℝ) + 3 / 2))))) := by
  have hL_le : I.L ≤ tebLSharp P := teb_bootstrap_part2 P I hc hB3
  have hL_nn : 0 ≤ tebLSharp P := le_trans zero_le_one (one_le_tebLogSharp (le_max_left _ _))
  have hκ_pos : 0 < P.κ_star / (2 * P.w_star) := div_pos P.hκ_star (by linarith [P.hw_star])
  have h12 : (1 / 2 : ℝ) * I.x_tilde = I.x_tilde / 2 := by ring
  have h3 := teb_part3_of_core P I.toBootstrapCore hc (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num) hκ_pos hL_nn hL_le
    (fun hk0 hmem => by rw [h12] at hmem ⊢; exact I.P_half_bound P.k_0 le_rfl hk0 hmem)
  rwa [show P.D_1 / (1 / 2 : ℝ) = 2 * P.D_1 by ring] at h3

/-- Explicit `C_X`, `C_*`, `L_♯`, `A_hb`, `K_0` constants for Theorem `TE.2(4)` (Hermite–Biehler). -/
noncomputable def tebCXHB (P : BootstrapParams) (W_top : ℝ) : ℝ := tebCXOf P (tebLambdaN P W_top)
noncomputable def tebCStarHB (P : BootstrapParams) (W_top : ℝ) : ℝ := max 1 (P.C_fb * (tebCXHB P W_top + 1))
noncomputable def tebLSharpHB (P : BootstrapParams) (W_top : ℝ) : ℝ := tebLogSharp (tebCStarHB P W_top)
noncomputable def tebAHB (P : BootstrapParams) (W_top : ℝ) : ℝ :=
  tebAOf P (tebThetaHB P W_top) (P.κ_star / (4 * P.w_star))
noncomputable def tebK0HB (P : BootstrapParams) (W_top : ℝ) : ℝ :=
  max (P.D_1 / tebThetaHB P W_top) (max 1 (max (2 * tebAHB P W_top)
    ((2 * tebAHB P W_top * tebLSharpHB P W_top) ^ (1 / ((P.k_0 : ℝ) + 3 / 2)))))

/-- **Theorem TE.2(4)** part `(1)` for all-level Hermite–Biehler instances (no `(B3)` needed). -/
theorem teb_bootstrap_hb_part1 (P : BootstrapParams) {W_top : ℝ}
    (I : BootstrapHBInstance P W_top) (hc : tebC2 P ≤ I.c) :
    I.B_1 + I.B_2 ≤ tebCXHB P W_top * (1 + Real.log I.L) * I.c ^ (-(1 / 3 : ℝ)) :=
  teb_part1_of_core P I.toBootstrapCore hc (tebLambdaN_nonneg P I.hW_top) I.hP_nodes_lb_hb

/-- **Theorem TE.2(4)** (All-level Hermite–Biehler extension):
`(B1)+(B2_HB)` imply `(1)`, and `(B1)+(B2_HB)+(B3)` imply `(2)` and `K ≤ K₀`. -/
theorem teb_bootstrap_hb (P : BootstrapParams) {W_top : ℝ}
    (I : BootstrapHBInstance P W_top) (hc : tebC2 P ≤ I.c) :
    (I.B_1 + I.B_2 ≤ tebCXHB P W_top * (1 + Real.log I.L) * I.c ^ (-(1 / 3 : ℝ))) ∧
    (I.L ≤ P.C_fb * (I.c ^ (1 / 3 : ℝ) * (I.B_1 + I.B_2) + 1) →
      I.L ≤ tebLogSharp (tebCStarHB P W_top) ∧
      I.c ^ (1 / 3 : ℝ) * I.x_tilde ≤ tebK0HB P W_top) := by
  have h1 := teb_bootstrap_hb_part1 P I hc
  refine ⟨h1, fun hB3 => ?_⟩
  have h2 : I.L ≤ tebLSharpHB P W_top := teb_part2_of_part1 P I.toBootstrapCore h1 hB3
  have hL_nn : 0 ≤ tebLSharpHB P W_top := le_trans zero_le_one (one_le_tebLogSharp (le_max_left _ _))
  have hθ_pos := tebThetaHB_pos P I.hW_top
  have hθ_le : tebThetaHB P W_top ≤ 1 := (tebThetaHB_le_half P W_top).trans (by norm_num)
  have hκ_pos : 0 < P.κ_star / (4 * P.w_star) := div_pos P.hκ_star (by linarith [P.hw_star])
  exact ⟨h2, teb_part3_of_core P I.toBootstrapCore hc hθ_pos hθ_le hκ_pos hL_nn h2 I.P_theta_bound⟩

end BootstrapTheorems

/-! ### Part 4: Corollary TE.4 (`teb:mellin_o1`) — `O(1)` Lower Remainder -/

section MellinO1

private lemma mellin_case_low {β u_star ξ_star r_0 M_err K_0 c T : ℝ}
    (hβ : 0 < β) (hu_star : u_star < 0) (hr0 : 0 < r_0) (hM : 0 ≤ M_err) (hc1 : 1 ≤ c)
    (hc_thresh : 2 * K_0 / (β * min r_0 (1 / (2 * M_err + 1))) ≤ c)
    (u_tilde err : ℝ → ℝ) (hanti : StrictAnti u_tilde)
    (hexp : ∀ ξ : ℝ, |ξ - ξ_star| ≤ r_0 →
      u_tilde ξ = β * c ^ (2 / 3 : ℝ) * (ξ_star - ξ) * (1 + err ξ) ∧ |err ξ| ≤ M_err * |ξ - ξ_star|)
    (hbound : c ^ (1 / 3 : ℝ) * (u_tilde (T / c) - u_star) ≤ K_0) :
    ξ_star - min r_0 (1 / (2 * M_err + 1)) ≤ T / c := by
  by_contra hlt; push Not at hlt
  set r₁ := min r_0 (1 / (2 * M_err + 1)); set ξ₀ := ξ_star - r₁
  have hr1_pos : 0 < r₁ := lt_min hr0 (by positivity)
  have hc_pos : 0 < c := by linarith
  have hc13_pos : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc_pos _
  have hc_split : c ^ (1 / 3 : ℝ) * c ^ (2 / 3 : ℝ) = c := by rw [← Real.rpow_add hc_pos]; norm_num
  have hMr1 : M_err * r₁ ≤ 1 / 2 := by
    calc M_err * r₁ ≤ M_err * (1 / (2 * M_err + 1)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hM
      _ = M_err / (2 * M_err + 1) := mul_one_div _ _
      _ ≤ 1 / 2 := by rw [div_le_div_iff₀ (by linarith) zero_lt_two]; linarith
  have hξ₀_abs : |ξ₀ - ξ_star| = r₁ := by
    rw [show ξ₀ - ξ_star = -r₁ by dsimp [ξ₀]; ring, abs_neg, abs_of_pos hr1_pos]
  obtain ⟨hu_eq, herr_le⟩ := hexp ξ₀ (hξ₀_abs.le.trans (min_le_left _ _))
  have herr_lb : 1 / 2 ≤ 1 + err ξ₀ := by have := (abs_le.mp herr_le).1; rw [hξ₀_abs] at this; linarith
  have hu_ξ₀ : (1 / 2 : ℝ) * β * r₁ * c ^ (2 / 3 : ℝ) ≤ u_tilde ξ₀ := by
    rw [hu_eq, show ξ_star - ξ₀ = r₁ by dsimp [ξ₀]; ring]
    calc (1 / 2 : ℝ) * β * r₁ * c ^ (2 / 3 : ℝ) = (β * c ^ (2 / 3 : ℝ) * r₁) * (1 / 2) := by ring
      _ ≤ (β * c ^ (2 / 3 : ℝ) * r₁) * (1 + err ξ₀) := mul_le_mul_of_nonneg_left herr_lb (by positivity)
  have hprod_ge : K_0 ≤ (1 / 2 : ℝ) * β * r₁ * c := by
    have := (div_le_iff₀ (mul_pos hβ hr1_pos)).mp hc_thresh; linarith
  have h_contra : K_0 < c ^ (1 / 3 : ℝ) * (u_tilde (T / c) - u_star) := by
    calc K_0 ≤ (1 / 2 : ℝ) * β * r₁ * c := hprod_ge
      _ = (1 / 2 : ℝ) * β * r₁ * (c ^ (1 / 3 : ℝ) * c ^ (2 / 3 : ℝ)) := by rw [hc_split]
      _ = c ^ (1 / 3 : ℝ) * ((1 / 2 : ℝ) * β * r₁ * c ^ (2 / 3 : ℝ)) := by ring
      _ ≤ c ^ (1 / 3 : ℝ) * u_tilde ξ₀ := mul_le_mul_of_nonneg_left hu_ξ₀ hc13_pos.le
      _ < c ^ (1 / 3 : ℝ) * u_tilde (T / c) := mul_lt_mul_of_pos_left (hanti hlt) hc13_pos
      _ < c ^ (1 / 3 : ℝ) * u_tilde (T / c) + c ^ (1 / 3 : ℝ) * (-u_star) := by
          linarith [mul_pos hc13_pos (by linarith : 0 < -u_star)]
      _ = c ^ (1 / 3 : ℝ) * (u_tilde (T / c) - u_star) := by ring
  linarith

private lemma mellin_case_high {β u_star ξ_star r₁ c T : ℝ}
    (hβ : 0 < β) (hr1 : 0 < r₁) (hc1 : 1 ≤ c) (h_high : ξ_star + r₁ < T / c) :
    ξ_star * c + (|u_star| / β) * c ^ (1 / 3 : ℝ) - (|u_star| / β) ^ 2 / (4 * r₁) ≤ T := by
  have hc_pos : 0 < c := by linarith
  have hT_gt : ξ_star * c + r₁ * c < T := by have := (lt_div_iff₀ hc_pos).mp h_high; linarith
  have hc13_le_c12 : c ^ (1 / 3 : ℝ) ≤ c ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
  have hc12_sq : (c ^ (1 / 2 : ℝ)) ^ 2 = c := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hc_pos.le]; norm_num
  set A_u := |u_star| / β
  have hAu_nn : 0 ≤ A_u := by dsimp [A_u]; positivity
  have h1 := mul_le_mul_of_nonneg_left hc13_le_c12 hAu_nn
  have hsq_nn : 0 ≤ r₁ * (c ^ (1 / 2 : ℝ) - A_u / (2 * r₁)) ^ 2 := mul_nonneg hr1.le (sq_nonneg _)
  have hid : r₁ * (c ^ (1 / 2 : ℝ) - A_u / (2 * r₁)) ^ 2 =
      r₁ * (c ^ (1 / 2 : ℝ)) ^ 2 - A_u * c ^ (1 / 2 : ℝ) + A_u ^ 2 / (4 * r₁) := by
    field_simp [hr1.ne']; ring
  rw [hid, hc12_sq] at hsq_nn; linarith

private lemma mellin_case_mid {β u_star ξ_star r_0 M_err K_0 c T : ℝ}
    (hβ : 0 < β) (hu_star : u_star < 0) (hM : 0 ≤ M_err) (hc1 : 1 ≤ c)
    (hK0 : 0 ≤ K_0) (h_abs : |T / c - ξ_star| ≤ min r_0 (1 / (2 * M_err + 1)))
    (u_tilde err : ℝ → ℝ)
    (hexp : ∀ ξ : ℝ, |ξ - ξ_star| ≤ r_0 →
      u_tilde ξ = β * c ^ (2 / 3 : ℝ) * (ξ_star - ξ) * (1 + err ξ) ∧ |err ξ| ≤ M_err * |ξ - ξ_star|)
    (hbound : c ^ (1 / 3 : ℝ) * (u_tilde (T / c) - u_star) ≤ K_0) :
    ξ_star * c + (|u_star| / β) * c ^ (1 / 3 : ℝ) -
      (2 * |u_star| * M_err * ((|u_star| + 2 * K_0) / β) / β + 2 * K_0 / β) ≤ T := by
  set r₁ := min r_0 (1 / (2 * M_err + 1))
  set δ := T / c - ξ_star
  set A_u := |u_star| / β
  set M_δ := (|u_star| + 2 * K_0) / β
  set C_m := 2 * |u_star| * M_err * M_δ / β + 2 * K_0 / β
  have hc_pos : 0 < c := by linarith
  have hc13_pos : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc_pos _
  have hc23_pos : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc_pos _
  have hc_split : c ^ (1 / 3 : ℝ) * c ^ (2 / 3 : ℝ) = c := by rw [← Real.rpow_add hc_pos]; norm_num
  have hc_m23_mul : c * c ^ (-(2 / 3 : ℝ)) = c ^ (1 / 3 : ℝ) := by
    calc c * c ^ (-(2 / 3 : ℝ)) = c ^ (1 : ℝ) * c ^ (-(2 / 3 : ℝ)) := by rw [Real.rpow_one]
      _ = c ^ (1 / 3 : ℝ) := by rw [← Real.rpow_add hc_pos]; norm_num
  have hT_eq : T = ξ_star * c + c * δ := by dsimp [δ]; field_simp [hc_pos.ne']; ring
  have hC_nn : 0 ≤ C_m := by dsimp [C_m, M_δ]; positivity
  rcases le_or_gt (A_u * c ^ (-(2 / 3 : ℝ))) δ with hδ_big | hδ_small
  · have hcδ : A_u * c ^ (1 / 3 : ℝ) ≤ c * δ := by
      calc A_u * c ^ (1 / 3 : ℝ) = c * (A_u * c ^ (-(2 / 3 : ℝ))) := by rw [← hc_m23_mul]; ring
        _ ≤ c * δ := mul_le_mul_of_nonneg_left hδ_big hc_pos.le
    linarith
  · obtain ⟨hu_eq, herr_le⟩ := hexp (T / c) (h_abs.trans (min_le_left _ _))
    set e := err (T / c)
    have hMr1 : M_err * r₁ ≤ 1 / 2 := by
      calc M_err * r₁ ≤ M_err * (1 / (2 * M_err + 1)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hM
        _ = M_err / (2 * M_err + 1) := mul_one_div _ _
        _ ≤ 1 / 2 := by rw [div_le_div_iff₀ (by linarith) zero_lt_two]; linarith
    have herr_bounds : 1 / 2 ≤ 1 + e ∧ 1 + e ≤ 3 / 2 := by
      have := abs_le.mp ((herr_le.trans (mul_le_mul_of_nonneg_left h_abs hM)).trans hMr1)
      constructor <;> linarith
    have h1e_pos : 0 < 1 + e := by linarith [herr_bounds.1]
    have hδ_abs_bound : |δ| ≤ M_δ * c ^ (-(2 / 3 : ℝ)) := by
      rcases le_or_gt 0 δ with hδ_nn | hδ_neg
      · rw [abs_of_nonneg hδ_nn]
        have hAu_le : A_u ≤ M_δ := div_le_div_of_nonneg_right (by linarith) hβ.le
        exact hδ_small.le.trans (mul_le_mul_of_nonneg_right hAu_le (Real.rpow_nonneg hc_pos.le _))
      · rw [abs_of_neg hδ_neg]
        have hu_le : u_tilde (T / c) ≤ u_star + K_0 * c ^ (-(1 / 3 : ℝ)) := by
          have h1 : u_tilde (T / c) - u_star ≤ K_0 / c ^ (1 / 3 : ℝ) := by
            calc u_tilde (T / c) - u_star
                = (c ^ (1 / 3 : ℝ) * (u_tilde (T / c) - u_star)) / c ^ (1 / 3 : ℝ) := by
                  field_simp [hc13_pos.ne']
              _ ≤ K_0 / c ^ (1 / 3 : ℝ) := div_le_div_of_nonneg_right hbound hc13_pos.le
          have h2 : K_0 / c ^ (1 / 3 : ℝ) = K_0 * c ^ (-(1 / 3 : ℝ)) := by
            rw [div_eq_mul_inv, ← Real.rpow_neg hc_pos.le]
          linarith
        have hu_lb : (1 / 2 : ℝ) * β * c ^ (2 / 3 : ℝ) * (-δ) ≤ u_tilde (T / c) := by
          rw [hu_eq, show ξ_star - T / c = -δ by dsimp [δ]; ring]
          have hneg_nn : 0 ≤ -δ := by linarith
          calc (1 / 2 : ℝ) * β * c ^ (2 / 3 : ℝ) * (-δ) = (β * c ^ (2 / 3 : ℝ) * (-δ)) * (1 / 2) := by ring
            _ ≤ (β * c ^ (2 / 3 : ℝ) * (-δ)) * (1 + e) := mul_le_mul_of_nonneg_left herr_bounds.1 (by positivity)
        have hK_le : (1 / 2 : ℝ) * β * c ^ (2 / 3 : ℝ) * (-δ) ≤ K_0 * c ^ (-(1 / 3 : ℝ)) := by linarith
        have h_inv_c : c ^ (-(1 / 3 : ℝ)) * c ^ (-(2 / 3 : ℝ)) = c ^ (-(1 : ℝ)) := by
          rw [← Real.rpow_add hc_pos]; norm_num
        have hneg_δ : -δ ≤ (2 * K_0 / β) * c ^ (-(2 / 3 : ℝ)) := by
          have h1 := (le_div_iff₀' (by positivity : 0 < (1 / 2 : ℝ) * β * c ^ (2 / 3 : ℝ))).mpr hK_le
          have h2 : K_0 * c ^ (-(1 / 3 : ℝ)) / ((1 / 2 : ℝ) * β * c ^ (2 / 3 : ℝ)) =
              (2 * K_0 / β) * c ^ (-(1 : ℝ)) := by
            calc K_0 * c ^ (-(1 / 3 : ℝ)) / ((1 / 2 : ℝ) * β * c ^ (2 / 3 : ℝ))
                = (2 * K_0 / β) * (c ^ (-(1 / 3 : ℝ)) * (c ^ (2 / 3 : ℝ))⁻¹) := by field_simp [hβ.ne']
              _ = (2 * K_0 / β) * c ^ (-(1 : ℝ)) := by rw [← Real.rpow_neg hc_pos.le, h_inv_c]
          rw [h2] at h1
          exact h1.trans (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)) (by positivity))
        exact hneg_δ.trans (mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right (by linarith [abs_nonneg u_star]) hβ.le) (Real.rpow_nonneg hc_pos.le _))
    have hu_abs : -u_star = |u_star| := (abs_of_neg hu_star).symm
    have hu_ineq : c ^ (1 / 3 : ℝ) * (β * c ^ (2 / 3 : ℝ) * (-δ) * (1 + e) - u_star) ≤ K_0 := by
      have hξ : ξ_star - T / c = -δ := by dsimp [δ]; ring
      rw [← hξ, ← hu_eq]; exact hbound
    have hu_ineq2 : -β * (1 + e) * (c * δ) + |u_star| * c ^ (1 / 3 : ℝ) ≤ K_0 := by
      calc -β * (1 + e) * (c * δ) + |u_star| * c ^ (1 / 3 : ℝ)
          = -β * (1 + e) * ((c ^ (1 / 3 : ℝ) * c ^ (2 / 3 : ℝ)) * δ) + (-u_star) * c ^ (1 / 3 : ℝ) := by
            rw [hc_split, hu_abs]
        _ = c ^ (1 / 3 : ℝ) * (β * c ^ (2 / 3 : ℝ) * (-δ) * (1 + e) - u_star) := by ring
        _ ≤ K_0 := hu_ineq
    have hcδ_lb : (|u_star| * c ^ (1 / 3 : ℝ) - K_0) / (β * (1 + e)) ≤ c * δ := by
      rw [div_le_iff₀ (mul_pos hβ h1e_pos)]; linarith
    have hc13_m23 : c ^ (1 / 3 : ℝ) * c ^ (-(2 / 3 : ℝ)) = c ^ (-(1 / 3 : ℝ)) := by
      rw [← Real.rpow_add hc_pos]; norm_num
    have hc_m13_le1 : c ^ (-(1 / 3 : ℝ)) ≤ 1 := by
      rw [← Real.rpow_zero c]; exact Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
    have hMδ_nn : 0 ≤ M_δ := by dsimp [M_δ]; positivity
    have hden_lb : β / 2 ≤ β * (1 + e) := by nlinarith [herr_bounds.1]
    have herr_term : |u_star| * c ^ (1 / 3 : ℝ) * |e| / (β * (1 + e)) ≤
        2 * |u_star| * M_err * M_δ / β := by
      have h1 : |u_star| * c ^ (1 / 3 : ℝ) * |e| ≤ |u_star| * M_err * M_δ := by
        calc |u_star| * c ^ (1 / 3 : ℝ) * |e|
            ≤ |u_star| * c ^ (1 / 3 : ℝ) * (M_err * (M_δ * c ^ (-(2 / 3 : ℝ)))) := by
              gcongr; exact herr_le.trans (mul_le_mul_of_nonneg_left hδ_abs_bound hM)
          _ = |u_star| * M_err * M_δ * (c ^ (1 / 3 : ℝ) * c ^ (-(2 / 3 : ℝ))) := by ring
          _ ≤ |u_star| * M_err * M_δ * 1 := by rw [hc13_m23]; gcongr
          _ = |u_star| * M_err * M_δ := mul_one _
      calc |u_star| * c ^ (1 / 3 : ℝ) * |e| / (β * (1 + e))
          ≤ (|u_star| * M_err * M_δ) / (β / 2) := div_le_div₀ (by positivity) h1 (by positivity) hden_lb
        _ = 2 * |u_star| * M_err * M_δ / β := by ring
    have hK_term : K_0 / (β * (1 + e)) ≤ 2 * K_0 / β := by
      calc K_0 / (β * (1 + e)) ≤ K_0 / (β / 2) := div_le_div_of_nonneg_left hK0 (by positivity) hden_lb
        _ = 2 * K_0 / β := by ring
    have hid_split : (|u_star| * c ^ (1 / 3 : ℝ) - K_0) / (β * (1 + e)) =
        (|u_star| / β) * c ^ (1 / 3 : ℝ) -
          (|u_star| * c ^ (1 / 3 : ℝ) * e / (β * (1 + e)) + K_0 / (β * (1 + e))) := by
      field_simp [hβ.ne', h1e_pos.ne']; ring
    have he_le_abs : |u_star| * c ^ (1 / 3 : ℝ) * e / (β * (1 + e)) ≤
        |u_star| * c ^ (1 / 3 : ℝ) * |e| / (β * (1 + e)) := by gcongr; exact le_abs_self e
    have herr_sum : |u_star| * c ^ (1 / 3 : ℝ) * e / (β * (1 + e)) + K_0 / (β * (1 + e)) ≤ C_m :=
      add_le_add (he_le_abs.trans herr_term) hK_term
    calc ξ_star * c + (|u_star| / β) * c ^ (1 / 3 : ℝ) - C_m
        ≤ ξ_star * c + (|u_star| / β) * c ^ (1 / 3 : ℝ) -
            (|u_star| * c ^ (1 / 3 : ℝ) * e / (β * (1 + e)) + K_0 / (β * (1 + e))) := by linarith
      _ = ξ_star * c + (|u_star| * c ^ (1 / 3 : ℝ) - K_0) / (β * (1 + e)) := by rw [hid_split]; ring
      _ ≤ ξ_star * c + c * δ := by linarith [hcδ_lb]
      _ = T := hT_eq.symm

/-- **Corollary TE.4 (`teb:mellin_o1`)**, fixed-threshold form (`2 K₀ / (β r₁) ≤ c₂` where
`r₁ := min r₀ (1 / (2 M_err + 1))`). -/
theorem teb_mellin_o1_lower_of_thresh
    {β u_star ξ_star r_0 M_err c_2 K_0 : ℝ}
    (hβ : 0 < β) (hu_star : u_star < 0) (hr0 : 0 < r_0)
    (hM : 0 ≤ M_err) (hc2 : 1 ≤ c_2) (hK0 : 0 ≤ K_0)
    (hc2_thresh : 2 * K_0 / (β * min r_0 (1 / (2 * M_err + 1))) ≤ c_2)
    (u_tilde : ℝ → ℝ → ℝ) (err : ℝ → ℝ → ℝ)
    (hanti : ∀ c : ℝ, c_2 ≤ c → StrictAnti (u_tilde c))
    (hexp : ∀ c : ℝ, c_2 ≤ c → ∀ ξ : ℝ, |ξ - ξ_star| ≤ r_0 →
      u_tilde c ξ = β * c ^ (2 / 3 : ℝ) * (ξ_star - ξ) * (1 + err c ξ) ∧
        |err c ξ| ≤ M_err * |ξ - ξ_star|) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, c_2 ≤ c → ∀ T : ℝ,
      c ^ (1 / 3 : ℝ) * (u_tilde c (T / c) - u_star) ≤ K_0 →
      ξ_star * c + (|u_star| / β) * c ^ (1 / 3 : ℝ) - C ≤ T := by
  set r₁ := min r_0 (1 / (2 * M_err + 1))
  have hr1_pos : 0 < r₁ := lt_min hr0 (by positivity)
  set C := max ((|u_star| / β) ^ 2 / (4 * r₁))
    (2 * |u_star| * M_err * ((|u_star| + 2 * K_0) / β) / β + 2 * K_0 / β)
  refine ⟨C, le_trans (by positivity) (le_max_left _ _), fun c hc T hbound => ?_⟩
  have hc1 : 1 ≤ c := hc2.trans hc
  have h_low := mellin_case_low hβ hu_star hr0 hM hc1 (hc2_thresh.trans hc)
    (u_tilde c) (err c) (hanti c hc) (hexp c hc) hbound
  rcases lt_or_ge (ξ_star + r₁) (T / c) with h_high | h_le_high
  · exact le_trans (sub_le_sub_left (le_max_left _ _) _) (mellin_case_high hβ hr1_pos hc1 h_high)
  · exact le_trans (sub_le_sub_left (le_max_right _ _) _)
      (mellin_case_mid hβ hu_star hM hc1 hK0 (abs_le.mpr ⟨by linarith, by linarith⟩)
        (u_tilde c) (err c) (hexp c hc) hbound)

/-- **Corollary TE.4 (`teb:mellin_o1`)**: enlarging `c_2` if necessary to `max c_2 (2 K₀ / (β r₁))`,
there exists `C ≥ 0` such that for all `c ≥ c_3` and `T` with
`c^{1/3} (u_tilde c (T / c) - u_star) ≤ K₀`, `T ≥ ξ_star c + (|u_star| / β) c^{1/3} - C`. -/
theorem teb_mellin_o1_lower
    {β u_star ξ_star r_0 M_err c_2 K_0 : ℝ}
    (hβ : 0 < β) (hu_star : u_star < 0) (hr0 : 0 < r_0)
    (hM : 0 ≤ M_err) (hc2 : 1 ≤ c_2) (hK0 : 0 ≤ K_0)
    (u_tilde : ℝ → ℝ → ℝ) (err : ℝ → ℝ → ℝ)
    (hanti : ∀ c : ℝ, c_2 ≤ c → StrictAnti (u_tilde c))
    (hexp : ∀ c : ℝ, c_2 ≤ c → ∀ ξ : ℝ, |ξ - ξ_star| ≤ r_0 →
      u_tilde c ξ = β * c ^ (2 / 3 : ℝ) * (ξ_star - ξ) * (1 + err c ξ) ∧
        |err c ξ| ≤ M_err * |ξ - ξ_star|) :
    ∃ c_3 : ℝ, c_2 ≤ c_3 ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, c_3 ≤ c → ∀ T : ℝ,
      c ^ (1 / 3 : ℝ) * (u_tilde c (T / c) - u_star) ≤ K_0 →
      ξ_star * c + (|u_star| / β) * c ^ (1 / 3 : ℝ) - C ≤ T := by
  set c_3 := max c_2 (2 * K_0 / (β * min r_0 (1 / (2 * M_err + 1))))
  have hc3_ge : c_2 ≤ c_3 := le_max_left _ _
  obtain ⟨C, hC_nn, hbound⟩ := teb_mellin_o1_lower_of_thresh hβ hu_star hr0 hM
    (hc2.trans hc3_ge) hK0 (le_max_right _ _) u_tilde err
    (fun c hc => hanti c (hc3_ge.trans hc)) (fun c hc => hexp c (hc3_ge.trans hc))
  exact ⟨c_3, hc3_ge, C, hC_nn, hbound⟩

end MellinO1

/-! ### Part 5: Non-Vacuity Witnesses -/

section NonVacuity

/-- Concrete parameter inhabitant for `BootstrapParams`. -/
def defaultBootstrapParams : BootstrapParams where
  b := 1
  C_a := 1
  C_unc := 1
  C_1 := 1
  w_star := 1
  κ_star := 1
  C_α := 1
  C_fb := 1
  D_1 := 0
  η_0 := 1
  δ_star := 1
  κ := 1
  C_0 := 1
  C_L := 1
  γ := 0
  k_0 := 5
  hb := zero_lt_one
  hCa := zero_le_one
  hCunc := zero_le_one
  hC1 := zero_lt_one
  hw_star := zero_lt_one
  hκ_star := zero_lt_one
  hCα := zero_le_one
  hCfb := le_rfl
  hD1 := le_rfl
  hη0 := zero_lt_one
  hδ_star := zero_lt_one
  hκ := zero_lt_one
  hC0 := zero_lt_one
  hCL := le_rfl
  hγ := le_rfl
  hk0 := by norm_num

private noncomputable def defaultBootstrapCore (c : ℝ) (hc : 2 ≤ c) :
    BootstrapCore defaultBootstrapParams :=
  let hc_pos : 0 < c := by linarith
  let hc1 : 1 ≤ c := by linarith
  let R : ℝ := c ^ (2 / 3 : ℝ)
  let a : ℝ := c ^ (1 / 3 : ℝ)
  { c := c, R := R, a := a, B_1 := 0, B_2 := 0, L := 1
    x_tilde := c ^ (-(2 / 3 : ℝ)), r_inf := 0, C_err := 0, hc := hc
    ha_lb := by simp [defaultBootstrapParams, a]
    ha_sq := by
      dsimp [a, R]; rw [← Real.rpow_natCast (c ^ (1 / 3 : ℝ)) 2, ← Real.rpow_mul hc_pos.le]; norm_num
    hR_ub := by dsimp [R, defaultBootstrapParams]; linarith [Real.rpow_nonneg hc_pos.le (2 / 3 : ℝ)]
    hB1 := le_rfl, hB2 := le_rfl, hL_lb := le_rfl
    hL_ub := by simp [defaultBootstrapParams]
    hx_pos := Real.rpow_pos_of_pos hc_pos _
    hx_ub := by
      simp only [defaultBootstrapParams, min_self]
      rw [← Real.rpow_zero c]; exact Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
    hr_inf_nn := le_rfl
    hr_inf_ub := by simp only [defaultBootstrapParams, one_mul, neg_mul]; positivity
    hC_err_nn := le_rfl
    hC_err_ub := by simp [defaultBootstrapParams]
    B_1k := fun _ => 0, B_2' := fun _ => 0
    P_nodes := fun k _ => ((k : ℝ) + 1) / R, I_line := fun k _ => ((k : ℝ) + 1) / R
    Arc_cov := fun _ _ => 0, Arc_unc := 0
    hB1k_nn := fun _ _ _ => le_rfl, hB2'_nn := fun _ _ _ => le_rfl
    hB_sum := fun _ _ _ => by norm_num
    hP_le := fun _ _ _ _ _ => by ring_nf; rfl
    hArc_cov := fun k ℓ _ _ hℓ => by
      have hℓ_nn : 0 ≤ ℓ := by simpa [defaultBootstrapParams] using hℓ.1
      have ha_pos : 0 < a := Real.rpow_pos_of_pos hc_pos _
      have hgam_pos : 0 < Real.Gamma ((k : ℝ) + 1 / 2) := Real.Gamma_pos_of_pos (by positivity)
      have hpow_nn : 0 ≤ (Real.pi / (4 * ℓ * a)) ^ ((k : ℝ) + 1 / 2) := Real.rpow_nonneg (by positivity) _
      simp only [defaultBootstrapParams, mul_one]; positivity
    hArc_unc := by simp only [defaultBootstrapParams, one_mul]; positivity
    hI_line := fun _ _ _ _ _ => by
      simp only [defaultBootstrapParams, mul_zero, zero_mul, sub_zero, zero_add, add_zero, one_mul, le_refl] }

/-- Non-vacuity witness for `BootstrapInstance` (together with `(B3)`) for all `c ≥ 2`. -/
theorem bootstrapInstance_nonvacuous :
    ∀ c : ℝ, 2 ≤ c → ∃ I : BootstrapInstance defaultBootstrapParams,
      I.c = c ∧ I.L ≤ defaultBootstrapParams.C_fb * (I.c ^ (1 / 3 : ℝ) * (I.B_1 + I.B_2) + 1) := by
  intro c hc; have hc_pos : 0 < c := by linarith
  refine ⟨{
    toBootstrapCore := defaultBootstrapCore c hc
    hP_nodes_lb := fun k ℓ _ _ hℓ => by
      have hℓ_nn : 0 ≤ ℓ := by simpa [defaultBootstrapParams] using hℓ.1
      have hR_pos : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc_pos _
      have hp_nn : 0 ≤ ((k : ℝ) + 1) / c ^ (2 / 3 : ℝ) := by positivity
      dsimp [defaultBootstrapCore, defaultBootstrapParams]; linarith
    P_half_bound := fun k _ _ _ => by
      have hR_pos : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc_pos _
      have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [show (0 : ℝ) ≤ k by positivity]
      have h1 : (1 / 2 : ℝ) * (1 / c ^ (2 / 3 : ℝ)) ≤ ((k : ℝ) + 1) / c ^ (2 / 3 : ℝ) := by
        calc (1 / 2 : ℝ) * (1 / c ^ (2 / 3 : ℝ)) ≤ 1 * (1 / c ^ (2 / 3 : ℝ)) := by gcongr; norm_num
          _ ≤ ((k : ℝ) + 1) / c ^ (2 / 3 : ℝ) := by
              rw [one_mul]; exact div_le_div_of_nonneg_right hk1 hR_pos.le
      dsimp [defaultBootstrapCore]; rw [Real.rpow_neg hc_pos.le, ← one_div]
      have h_lhs : (defaultBootstrapParams.κ_star / (2 * defaultBootstrapParams.w_star)) *
          (1 / c ^ (2 / 3 : ℝ)) - defaultBootstrapParams.C_α * (c ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) * 0 =
          (1 / 2 : ℝ) * (1 / c ^ (2 / 3 : ℝ)) := by dsimp [defaultBootstrapParams]; ring
      rw [h_lhs]; exact h1 }, rfl, by simp [defaultBootstrapCore, defaultBootstrapParams]⟩

/-- Non-vacuity witness for `BootstrapHBInstance` (together with `(B3)`) for all `c ≥ 2` and `W_top ≥ 0`. -/
theorem bootstrapHBInstance_nonvacuous :
    ∀ c : ℝ, 2 ≤ c → ∀ W_top : ℝ, 0 ≤ W_top → ∃ I : BootstrapHBInstance defaultBootstrapParams W_top,
      I.c = c ∧ I.L ≤ defaultBootstrapParams.C_fb * (I.c ^ (1 / 3 : ℝ) * (I.B_1 + I.B_2) + 1) := by
  intro c hc W_top hW; have hc_pos : 0 < c := by linarith
  refine ⟨{
    toBootstrapCore := defaultBootstrapCore c hc
    hW_top := hW
    hP_nodes_lb_hb := fun k ℓ _ _ hℓ => by
      have hℓ_nn : 0 ≤ ℓ := by simpa [defaultBootstrapParams] using hℓ.1
      have hΛ_nn := tebLambdaN_nonneg defaultBootstrapParams hW
      have hR_pos : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc_pos _
      have hp_nn : 0 ≤ ((k : ℝ) + 1) / c ^ (2 / 3 : ℝ) := by positivity
      have hmul_nn : 0 ≤ tebLambdaN defaultBootstrapParams W_top * ℓ := mul_nonneg hΛ_nn hℓ_nn
      dsimp [defaultBootstrapCore]
      have h_lhs : -tebLambdaN defaultBootstrapParams W_top * ℓ -
          defaultBootstrapParams.C_α * (c ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) * 0 =
          -(tebLambdaN defaultBootstrapParams W_top * ℓ) := by dsimp [defaultBootstrapParams]; ring
      rw [h_lhs]; linarith
    P_theta_bound := fun _ _ => by
      have hR_pos : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc_pos _
      have h1 : (1 / 4 : ℝ) * (1 / c ^ (2 / 3 : ℝ)) ≤ ((5 : ℝ) + 1) / c ^ (2 / 3 : ℝ) := by
        calc (1 / 4 : ℝ) * (1 / c ^ (2 / 3 : ℝ)) ≤ 1 * (1 / c ^ (2 / 3 : ℝ)) := by gcongr; norm_num
          _ ≤ ((5 : ℝ) + 1) / c ^ (2 / 3 : ℝ) := by
              rw [one_mul]; exact div_le_div_of_nonneg_right (by norm_num) hR_pos.le
      dsimp [defaultBootstrapCore]; rw [Real.rpow_neg hc_pos.le, ← one_div]
      have h_lhs : (defaultBootstrapParams.κ_star / (4 * defaultBootstrapParams.w_star)) *
          (1 / c ^ (2 / 3 : ℝ)) - defaultBootstrapParams.C_α * (c ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) * 0 =
          (1 / 4 : ℝ) * (1 / c ^ (2 / 3 : ℝ)) := by dsimp [defaultBootstrapParams]; ring
      rw [h_lhs]; exact h1 }, rfl, by simp [defaultBootstrapCore, defaultBootstrapParams]⟩

end NonVacuity

/-! ### Axiom Verification -/

/-- info: 'FormalResearch.TwoEdgeBootstrap.teb_large_c_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.TwoEdgeBootstrap.teb_large_c_exists

/-- info: 'FormalResearch.TwoEdgeBootstrap.teb_bootstrap_part1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.TwoEdgeBootstrap.teb_bootstrap_part1

/-- info: 'FormalResearch.TwoEdgeBootstrap.teb_bootstrap_part2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.TwoEdgeBootstrap.teb_bootstrap_part2

/-- info: 'FormalResearch.TwoEdgeBootstrap.teb_bootstrap_part3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.TwoEdgeBootstrap.teb_bootstrap_part3

/-- info: 'FormalResearch.TwoEdgeBootstrap.teb_bootstrap_hb_part1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.TwoEdgeBootstrap.teb_bootstrap_hb_part1

/-- info: 'FormalResearch.TwoEdgeBootstrap.teb_bootstrap_hb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.TwoEdgeBootstrap.teb_bootstrap_hb

/-- info: 'FormalResearch.TwoEdgeBootstrap.teb_mellin_o1_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.TwoEdgeBootstrap.teb_mellin_o1_lower

/-- info: 'FormalResearch.TwoEdgeBootstrap.bootstrapInstance_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.TwoEdgeBootstrap.bootstrapInstance_nonvacuous

/-- info: 'FormalResearch.TwoEdgeBootstrap.bootstrapHBInstance_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.TwoEdgeBootstrap.bootstrapHBInstance_nonvacuous

end FormalResearch.TwoEdgeBootstrap
