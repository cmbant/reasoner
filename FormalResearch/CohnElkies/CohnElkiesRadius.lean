module

public import FormalResearch.CohnElkies.FiniteDimensionCrossings
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Fourier.Convolution

/-!
# Cohn–Elkies Radius at Airy Order and Density Expansion (`ce_radius.tex`)

Formalizes Corollaries `7.12` (`gt:7.12` / `thm:ce-radius`) and `7.12a`
(`gt:7.12a` / `cor:ce-density`) of `CFT/sign_uncertainty/paper/ce_radius.tex`
(PR 240, commit `58dd780c8`), reusing `FiniteGaussianBase` and `FiniteDimensionCrossings`.

* **Section 1 (Corollary `7.12a`):** Uniform even/odd Stirling expansion
  `log_gamma_half_add_one_asymptotic`, unconditional `ce_volume_expansion` (both multiplicative
  enclosure and logarithmic expansion `(gt:7.12a-density)`), and `ce_radii_diff_O_inv_sqrt`.
* **Section 2 (Corollary `7.12`, equivalence of infima):** Normalized continuous-`L¹` and Schwartz
  admissibility (`IsContinuousL1CEAdmissible`, `IsSchwartzCEAdmissible`), origin rescaling,
  Minkowski-type bound `2^{-d} ≤ optimalCohnElkiesBound d`, `ce_schwartz_radius_eq_L1_radius` via
  Gaussian damping and `ContDiffBump` mollification, `ce_schwartz_bound_eq_optimalCohnElkiesBound`,
  and `optimalSchwartzCERadius_le_quadR`.
* **Section 3 (Corollary `7.12`, Airy-order gluing and non-vacuity):** Conditional gluing
  `ce_radius_airy_order_of_bounds` across all dimensions `d ≥ 2` (even and odd) and
  non-vacuity witness `ce_radius_nonvacuous`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real FourierTransform Polynomial RealInnerProductSpace SchwartzMap Convolution ContDiff

namespace FormalResearch.CohnElkies

/-! ### Section 1: Uniform Stirling Expansion and Corollary `7.12a` (`gt:7.12a`) -/

/-- Taylor error bound `|log (1 + t) - t| ≤ 2 * t ^ 2` for `|t| ≤ 1 / 2`. -/
private lemma abs_log_one_add_sub_self_le {t : ℝ} (ht : |t| ≤ 1 / 2) :
    |Real.log (1 + t) - t| ≤ 2 * t ^ 2 := by
  have h1 : |-t| < 1 := by rw [abs_neg]; linarith
  have hser := Real.abs_log_sub_add_sum_range_le h1 1
  simp only [Finset.sum_range_one, pow_one, Nat.cast_zero, zero_add, div_one, sub_neg_eq_add,
    abs_neg, show (1 : ℕ) + 1 = 2 by rfl] at hser
  have hden : 1 / 2 ≤ 1 - |t| := by linarith
  rw [add_comm, ← sub_eq_add_neg, sq_abs] at hser
  calc |Real.log (1 + t) - t|
      ≤ t ^ 2 / (1 - |t|) := hser
    _ ≤ t ^ 2 / (1 / 2) := div_le_div_of_nonneg_left (sq_nonneg t) (by norm_num) hden
    _ = 2 * t ^ 2 := by ring

/-- Extends a tail bound `f d ≤ B_tail` for `d ≥ d₁` to all `d ≥ 2`. -/
private lemma exists_bound_of_tail_bound (f : ℕ → ℝ) (d₁ : ℕ) (B_tail : ℝ)
    (htail : ∀ d : ℕ, d₁ ≤ d → f d ≤ B_tail) : ∃ B : ℝ, ∀ d : ℕ, 2 ≤ d → f d ≤ B := by
  let B_fin : ℝ := (Finset.range (d₁ + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩
    (fun d => if 2 ≤ d then f d else 0)
  refine ⟨max B_tail B_fin, fun d hd => ?_⟩
  rcases lt_or_ge d d₁ with hlt | hge
  · have hle := Finset.le_sup' (fun j => if 2 ≤ j then f j else 0)
      (Finset.mem_range.mpr (by omega : d < d₁ + 1))
    exact (by simpa [hd] using hle : f d ≤ B_fin).trans (le_max_right _ _)
  · exact (htail d hge).trans (le_max_left _ _)

/-- Uniform even/odd Stirling expansion for `log Γ(d / 2 + 1)` (`d ≥ 2`). -/
theorem log_gamma_half_add_one_asymptotic {d : ℕ} (hd : 2 ≤ d) :
    |Real.log (Real.Gamma ((d : ℝ) / 2 + 1)) -
      ((1 / 2 : ℝ) * Real.log (π * (d : ℝ)) +
        ((d : ℝ) / 2) * Real.log ((d : ℝ) / (2 * Real.exp 1)))| ≤ 2 / (d : ℝ) := by
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
  have he_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hsplit : (1 / 2 : ℝ) * Real.log (π * (d : ℝ)) +
      ((d : ℝ) / 2) * Real.log ((d : ℝ) / (2 * Real.exp 1)) =
      (1 / 2 : ℝ) * Real.log (2 * π) + ((d : ℝ) / 2 + 1 / 2) * Real.log ((d : ℝ) / 2) -
        (d : ℝ) / 2 := by
    rw [Real.log_mul Real.pi_pos.ne' hd_pos.ne', Real.log_mul two_ne_zero Real.pi_pos.ne',
      Real.log_div hd_pos.ne' (mul_pos two_pos he_pos).ne',
      Real.log_mul two_ne_zero he_pos.ne', Real.log_exp, Real.log_div hd_pos.ne' two_ne_zero]
    ring
  rw [hsplit]
  rcases Nat.even_or_odd d with ⟨n, rfl⟩ | ⟨n, rfl⟩
  · have hn : 1 ≤ n := by omega
    have hd_eq : ((n + n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
    have hG : Real.Gamma (((n + n : ℕ) : ℝ) / 2 + 1) = (n.factorial : ℝ) := by
      rw [hd_eq, show 2 * (n : ℝ) / 2 + 1 = (n : ℝ) + 1 by ring, Real.Gamma_nat_eq_factorial]
    obtain ⟨hst_lo, hst_hi⟩ := log_factorial_stirling_bounds hn
    rw [hG, hd_eq, show 2 * (n : ℝ) / 2 = (n : ℝ) by ring]
    have hn_ge : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hsq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ hn_ge
    have hlo2 : -(2 / (2 * (n : ℝ))) ≤ -(1 / (144 * (n : ℝ) ^ 3)) := by
      rw [neg_le_neg_iff]
      calc 1 / (144 * (n : ℝ) ^ 3) ≤ 1 / (12 * (n : ℝ)) :=
            one_div_le_one_div_of_le (by positivity) (by nlinarith)
        _ ≤ 2 / (2 * (n : ℝ)) := by rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
    have hhi2 : 1 / (12 * (n : ℝ)) ≤ 2 / (2 * (n : ℝ)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
    have h12 : (0 : ℝ) ≤ 1 / (12 * (n : ℝ)) := by positivity
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · let m := n + 1
    have hm : 2 ≤ m := by omega
    have hm_ge2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
    have hm_pos : (0 : ℝ) < m := by linarith
    have hd_eq : ((2 * n + 1 : ℕ) : ℝ) = 2 * (m : ℝ) - 1 := by dsimp [m]; push_cast; ring
    have hG : Real.Gamma (((2 * n + 1 : ℕ) : ℝ) / 2 + 1) = Real.Gamma ((m : ℝ) + 1 / 2) := by
      rw [hd_eq]; congr 1; ring
    obtain ⟨hg_lo, hg_hi⟩ := log_gamma_half_odd_bounds (m := m) (by omega)
    set c : ℝ := ((2 * n + 1 : ℕ) : ℝ) / 2
    have hm_c : (m : ℝ) = c + 1 / 2 := by dsimp [c]; rw [hd_eq]; ring
    have hc_ge : (3 / 2 : ℝ) ≤ c := by linarith
    have hc_pos : 0 < c := by linarith
    let R_g : ℝ := Real.log (Real.Gamma ((m : ℝ) + 1 / 2)) -
      ((1 / 2 : ℝ) * Real.log (2 * π) + m * Real.log m - m)
    have hm24 : (0 : ℝ) ≤ 1 / (24 * (m : ℝ)) := by positivity
    have hRg_bd : |R_g| ≤ 1 / (24 * m) + 1 / (144 * (m : ℝ) ^ 3) := by
      dsimp [R_g]; rw [abs_le]; constructor <;> linarith
    have hm_sub : (m : ℝ) = c * (1 + 1 / (2 * c)) := by
      rw [hm_c]; field_simp [hc_pos.ne']
    have hlog_m : Real.log m = Real.log c + Real.log (1 + 1 / (2 * c)) := by
      rw [hm_sub, Real.log_mul hc_pos.ne' (by positivity)]
    have hdiff_id : Real.log (Real.Gamma (c + 1)) -
        ((1 / 2 : ℝ) * Real.log (2 * π) + (c + 1 / 2) * Real.log c - c) =
        R_g + (m * (Real.log (1 + 1 / (2 * c)) - 1 / (2 * c)) + 1 / (4 * c)) := by
      have hprod : (m : ℝ) * Real.log m =
          (c + 1 / 2) * Real.log c + (m : ℝ) * Real.log (1 + 1 / (2 * c)) := by
        calc (m : ℝ) * Real.log m
            = (m : ℝ) * (Real.log c + Real.log (1 + 1 / (2 * c))) := by rw [hlog_m]
          _ = (c + 1 / 2) * Real.log c + (m : ℝ) * Real.log (1 + 1 / (2 * c)) := by rw [hm_c]; ring
      have hmc_frac : (m : ℝ) * (1 / (2 * c)) = 1 / 2 + 1 / (4 * c) := by
        rw [hm_c]; field_simp [hc_pos.ne']; ring
      rw [hG]; dsimp [R_g]; linarith
    have ht_bd : |1 / (2 * c)| ≤ 1 / 2 := by
      rw [abs_of_pos (by positivity), div_le_iff₀ (by positivity)]; linarith
    have hm_term : |m * (Real.log (1 + 1 / (2 * c)) - 1 / (2 * c))| ≤ 2 / (3 * c) := by
      rw [abs_mul, abs_of_pos hm_pos]
      calc (m : ℝ) * |Real.log (1 + 1 / (2 * c)) - 1 / (2 * c)|
          ≤ (4 / 3 * c) * (2 * (1 / (2 * c)) ^ 2) :=
            mul_le_mul (by linarith) (abs_log_one_add_sub_self_le ht_bd)
              (abs_nonneg _) (by positivity)
        _ = 2 / (3 * c) := by field_simp [hc_pos.ne']; ring
    have hRg_c : |R_g| ≤ 1 / (12 * c) := by
      refine hRg_bd.trans ?_
      have hmsq : (1 : ℝ) ≤ (m : ℝ) ^ 2 := one_le_pow₀ (by linarith)
      have h1 : 1 / (144 * (m : ℝ) ^ 3) ≤ 1 / (24 * m) :=
        one_div_le_one_div_of_le (by positivity) (by nlinarith)
      have h2 : 1 / (24 * (m : ℝ)) ≤ 1 / (24 * c) := by gcongr; linarith
      linarith [show (1 : ℝ) / (24 * c) + 1 / (24 * c) = 1 / (12 * c) by ring]
    have htot : |R_g + (m * (Real.log (1 + 1 / (2 * c)) - 1 / (2 * c)) + 1 / (4 * c))| ≤ 1 / c := by
      have hc4 : |1 / (4 * c)| = 1 / (4 * c) := abs_of_pos (by positivity)
      calc |R_g + (m * (Real.log (1 + 1 / (2 * c)) - 1 / (2 * c)) + 1 / (4 * c))|
          ≤ |R_g| + |m * (Real.log (1 + 1 / (2 * c)) - 1 / (2 * c))| + |1 / (4 * c)| := by
            linarith [abs_add_le R_g (m * (Real.log (1 + 1 / (2 * c)) - 1 / (2 * c)) + 1 / (4 * c)),
              abs_add_le (m * (Real.log (1 + 1 / (2 * c)) - 1 / (2 * c))) (1 / (4 * c))]
        _ ≤ 1 / (12 * c) + 2 / (3 * c) + 1 / (4 * c) := by rw [hc4]; linarith
        _ = 1 / c := by field_simp [hc_pos.ne']; ring
    change |Real.log (Real.Gamma (c + 1)) -
        ((1 / 2 : ℝ) * Real.log (2 * π) + (c + 1 / 2) * Real.log c - c)| ≤
        2 / ((2 * n + 1 : ℕ) : ℝ)
    rw [hdiff_id]
    exact htot.trans_eq (by dsimp [c]; field_simp [hd_pos.ne'])

/-- **Corollary `7.12a` (`gt:7.12a` / `cor:ce-density`), volume and log-density expansions:**
for any `A_opt : ℝ` and positive sequence `r` with `r d ^ 2 / 2 = d / (2π²) + A_opt (d/2)^{1/3} + O(1)`,
`vol(B_{r d / 2})` satisfies both the multiplicative enclosure and `(gt:7.12a-density)`. -/
theorem ce_volume_expansion (A_opt : ℝ) {r : ℕ → ℝ} (hr_pos : ∀ d : ℕ, 2 ≤ d → 0 < r d)
    (hr_asymp : ∃ C : ℝ, ∀ d : ℕ, 2 ≤ d →
      |r d ^ 2 / 2 - ((d : ℝ) / (2 * π ^ 2) + A_opt * ((d : ℝ) / 2) ^ (1 / 3 : ℝ))| ≤ C) :
    (∃ c₁ c₂ : ℝ, 0 < c₁ ∧ ∀ d : ℕ, 2 ≤ d →
      c₁ * ((π * (d : ℝ)) ^ (-(1 / 2 : ℝ)) * (Real.exp 1 / (2 * π)) ^ ((d : ℝ) / 2) *
          Real.exp (π ^ 2 * A_opt * ((d : ℝ) / 2) ^ (1 / 3 : ℝ))) ≤
        (volume : Measure (Euc d)).real (Metric.ball 0 (r d / 2)) ∧
      (volume : Measure (Euc d)).real (Metric.ball 0 (r d / 2)) ≤
        c₂ * ((π * (d : ℝ)) ^ (-(1 / 2 : ℝ)) * (Real.exp 1 / (2 * π)) ^ ((d : ℝ) / 2) *
          Real.exp (π ^ 2 * A_opt * ((d : ℝ) / 2) ^ (1 / 3 : ℝ)))) ∧
    (∃ C' : ℝ, ∀ d : ℕ, 2 ≤ d →
      |Real.log ((volume : Measure (Euc d)).real (Metric.ball 0 (r d / 2))) -
        (((d : ℝ) / 2) * Real.log (Real.exp 1 / (2 * π)) +
          π ^ 2 * A_opt * ((d : ℝ) / 2) ^ (1 / 3 : ℝ) - (1 / 2 : ℝ) * Real.log (d : ℝ))| ≤ C') := by
  obtain ⟨C₀, hC₀⟩ := hr_asymp
  have hC₀_nn : 0 ≤ C₀ := (abs_nonneg _).trans (hC₀ 2 le_rfl)
  let K₁ : ℝ := π ^ 2 * (|A_opt| + C₀)
  let d₁ : ℕ := max 2 (Nat.ceil (2 * (2 * K₁ + 1) ^ (3 / 2 : ℝ)) + 1)
  have hd₁_ge2 : 2 ≤ d₁ := le_max_left _ _
  let vol : ℕ → ℝ := fun d => (volume : Measure (Euc d)).real (Metric.ball 0 (r d / 2))
  let modelLog : ℕ → ℝ := fun d =>
    ((d : ℝ) / 2) * Real.log (Real.exp 1 / (2 * π)) +
      π ^ 2 * A_opt * ((d : ℝ) / 2) ^ (1 / 3 : ℝ) - (1 / 2 : ℝ) * Real.log (π * (d : ℝ))
  have hvol_pos : ∀ d : ℕ, 2 ≤ d → 0 < vol d := fun d hd => by
    have hrd := hr_pos d hd
    dsimp [vol]; rw [volume_half_ball_eq (by omega) hrd.le]
    have hG := Real.Gamma_pos_of_pos (by positivity : (0 : ℝ) < (d : ℝ) / 2 + 1)
    positivity
  have hlarge : ∀ d : ℕ, d₁ ≤ d → |Real.log (vol d) - modelLog d| ≤ π ^ 2 * C₀ + 1 + 2 * K₁ ^ 2 := by
    intro d hd
    have hd2 : 2 ≤ d := hd₁_ge2.trans hd
    have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
    let c : ℝ := (d : ℝ) / 2
    have hc_ge1 : 1 ≤ c := by dsimp [c]; linarith [show (2 : ℝ) ≤ d by exact_mod_cast hd2]
    have hc_pos : 0 < c := by linarith
    let R : ℝ := r d ^ 2 / 2 - (c / π ^ 2 + A_opt * c ^ (1 / 3 : ℝ))
    have hR_bd : |R| ≤ C₀ := by
      dsimp [R, c]; rw [show (d : ℝ) / 2 / π ^ 2 = (d : ℝ) / (2 * π ^ 2) by ring]; exact hC₀ d hd2
    let δ : ℝ := π ^ 2 * A_opt * c ^ (-(2 / 3 : ℝ)) + π ^ 2 * R / c
    have hc_m1_le : c⁻¹ ≤ c ^ (-(2 / 3 : ℝ)) := by
      rw [← Real.rpow_neg_one c]; exact Real.rpow_le_rpow_of_exponent_le hc_ge1 (by norm_num)
    have hδ_le_K : |δ| ≤ K₁ * c ^ (-(2 / 3 : ℝ)) := by
      have h1 : |π ^ 2 * A_opt * c ^ (-(2 / 3 : ℝ))| = π ^ 2 * |A_opt| * c ^ (-(2 / 3 : ℝ)) := by
        rw [abs_mul, abs_mul, abs_of_pos (sq_pos_of_pos Real.pi_pos),
          abs_of_pos (Real.rpow_pos_of_pos hc_pos _)]
      have h2 : |π ^ 2 * R / c| ≤ π ^ 2 * C₀ * c ^ (-(2 / 3 : ℝ)) := by
        rw [abs_div, abs_mul, abs_of_pos (sq_pos_of_pos Real.pi_pos), abs_of_pos hc_pos, div_eq_mul_inv]
        exact mul_le_mul (mul_le_mul_of_nonneg_left hR_bd (sq_nonneg π)) hc_m1_le
          (inv_nonneg.mpr hc_pos.le) (by positivity)
      calc |δ| ≤ |π ^ 2 * A_opt * c ^ (-(2 / 3 : ℝ))| + |π ^ 2 * R / c| := abs_add_le _ _
        _ ≤ π ^ 2 * |A_opt| * c ^ (-(2 / 3 : ℝ)) + π ^ 2 * C₀ * c ^ (-(2 / 3 : ℝ)) := by linarith
        _ = K₁ * c ^ (-(2 / 3 : ℝ)) := by dsimp [K₁]; ring
    have hc_gt : (2 * K₁ + 1) ^ (3 / 2 : ℝ) < c := by
      have hd_ceil : (Nat.ceil (2 * (2 * K₁ + 1) ^ (3 / 2 : ℝ)) : ℝ) + 1 ≤ d := by
        exact_mod_cast (le_max_right _ _).trans hd
      have hlc : 2 * (2 * K₁ + 1) ^ (3 / 2 : ℝ) ≤ Nat.ceil (2 * (2 * K₁ + 1) ^ (3 / 2 : ℝ)) :=
        Nat.le_ceil _
      dsimp [c]; linarith
    have hK_c : K₁ * c ^ (-(2 / 3 : ℝ)) ≤ 1 / 2 := by
      have h23 : 2 * K₁ + 1 < c ^ (2 / 3 : ℝ) := by
        have hlt := Real.rpow_lt_rpow (by positivity) hc_gt (by norm_num : (0 : ℝ) < 2 / 3)
        rw [← Real.rpow_mul (by positivity)] at hlt; norm_num at hlt; exact hlt
      have hinv : c ^ (-(2 / 3 : ℝ)) < (2 * K₁ + 1)⁻¹ := by
        rw [Real.rpow_neg hc_pos.le]; exact inv_strictAnti₀ (by positivity) h23
      have hle : K₁ * c ^ (-(2 / 3 : ℝ)) ≤ K₁ / (2 * K₁ + 1) := by
        rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_left hinv.le (by positivity)
      exact hle.trans ((div_le_iff₀ (by positivity)).mpr (by linarith))
    have hδ_half : |δ| ≤ 1 / 2 := hδ_le_K.trans hK_c
    have h1δ_pos : 0 < 1 + δ := by linarith [(abs_le.mp hδ_half).1]
    have hc_rpow : c * c ^ (-(2 / 3 : ℝ)) = c ^ (1 / 3 : ℝ) := by
      conv_lhs => lhs; rw [← Real.rpow_one c]
      rw [← Real.rpow_add hc_pos]; congr 1; norm_num
    have hcδ : c * δ = π ^ 2 * A_opt * c ^ (1 / 3 : ℝ) + π ^ 2 * R := by
      dsimp [δ]
      calc c * (π ^ 2 * A_opt * c ^ (-(2 / 3 : ℝ)) + π ^ 2 * R / c)
          = π ^ 2 * A_opt * (c * c ^ (-(2 / 3 : ℝ))) + π ^ 2 * R * (c / c) := by ring
        _ = π ^ 2 * A_opt * c ^ (1 / 3 : ℝ) + π ^ 2 * R := by rw [hc_rpow, div_self hc_pos.ne', mul_one]
    have hT_eq : π * r d ^ 2 / 4 = (c / (2 * π)) * (1 + δ) := by
      have hr_eq : r d ^ 2 / 2 = c / π ^ 2 + A_opt * c ^ (1 / 3 : ℝ) + R := by dsimp [R]; ring
      calc π * r d ^ 2 / 4 = π * (r d ^ 2 / 2) / 2 := by ring
        _ = (c + π ^ 2 * A_opt * c ^ (1 / 3 : ℝ) + π ^ 2 * R) / (2 * π) := by
            rw [hr_eq]; field_simp [Real.pi_ne_zero]
        _ = (c + c * δ) / (2 * π) := by rw [hcδ]; ring
        _ = (c / (2 * π)) * (1 + δ) := by field_simp [Real.pi_ne_zero, hc_pos.ne']
    have hvol_log : Real.log (vol d) =
        c * Real.log (c / (2 * π)) + c * Real.log (1 + δ) - Real.log (Real.Gamma (c + 1)) := by
      dsimp [vol]; rw [volume_half_ball_eq (by omega) (hr_pos d hd2).le, hT_eq]
      have hG_pos : 0 < Real.Gamma (c + 1) := Real.Gamma_pos_of_pos (by positivity)
      have hc2pi : 0 < c / (2 * π) := by positivity
      have hmul_pos : 0 < c / (2 * π) * (1 + δ) := mul_pos hc2pi h1δ_pos
      rw [Real.log_div (Real.rpow_pos_of_pos hmul_pos _).ne' hG_pos.ne',
        Real.log_rpow hmul_pos, Real.log_mul hc2pi.ne' h1δ_pos.ne']
      dsimp [c]; ring
    have hlog_id : c * Real.log (c / (2 * π)) -
        ((1 / 2 : ℝ) * Real.log (π * (d : ℝ)) + c * Real.log ((d : ℝ) / (2 * Real.exp 1))) =
        c * Real.log (Real.exp 1 / (2 * π)) - (1 / 2 : ℝ) * Real.log (π * (d : ℝ)) := by
      have he_pos : 0 < Real.exp 1 := Real.exp_pos 1
      rw [show (d : ℝ) / (2 * Real.exp 1) = c / Real.exp 1 by dsimp [c]; ring,
        Real.log_div hc_pos.ne' (mul_pos two_pos Real.pi_pos).ne',
        Real.log_div hc_pos.ne' he_pos.ne',
        Real.log_div he_pos.ne' (mul_pos two_pos Real.pi_pos).ne', Real.log_exp]
      ring
    let stErr := Real.log (Real.Gamma (c + 1)) -
      ((1 / 2 : ℝ) * Real.log (π * (d : ℝ)) + c * Real.log ((d : ℝ) / (2 * Real.exp 1)))
    have hst1 : |stErr| ≤ 1 := (log_gamma_half_add_one_asymptotic hd2).trans
      (by rw [div_le_one hd_pos]; exact_mod_cast hd2)
    have hlog1_bd : |c * (Real.log (1 + δ) - δ)| ≤ 2 * K₁ ^ 2 := by
      rw [abs_mul, abs_of_pos hc_pos]
      have hpow : c * (c ^ (-(2 / 3 : ℝ))) ^ 2 = c ^ (-(1 / 3 : ℝ)) := by
        rw [← Real.rpow_natCast (c ^ (-(2 / 3 : ℝ))) 2, ← Real.rpow_mul hc_pos.le]
        conv_lhs => lhs; rw [← Real.rpow_one c]
        rw [← Real.rpow_add hc_pos]; congr 1; norm_num
      have hδ2 : δ ^ 2 ≤ (K₁ * c ^ (-(2 / 3 : ℝ))) ^ 2 := by
        rw [← sq_abs δ]; exact pow_le_pow_left₀ (abs_nonneg _) hδ_le_K 2
      have hc_m13 : c ^ (-(1 / 3 : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hc_ge1 (by norm_num)
      calc c * |Real.log (1 + δ) - δ| ≤ c * (2 * δ ^ 2) :=
            mul_le_mul_of_nonneg_left (abs_log_one_add_sub_self_le hδ_half) hc_pos.le
        _ ≤ c * (2 * (K₁ * c ^ (-(2 / 3 : ℝ))) ^ 2) := by gcongr
        _ = 2 * K₁ ^ 2 * (c * (c ^ (-(2 / 3 : ℝ))) ^ 2) := by ring
        _ = 2 * K₁ ^ 2 * c ^ (-(1 / 3 : ℝ)) := by rw [hpow]
        _ ≤ 2 * K₁ ^ 2 := mul_le_of_le_one_right (by positivity) hc_m13
    have hdiff_eq : Real.log (vol d) - modelLog d =
        π ^ 2 * R - stErr + c * (Real.log (1 + δ) - δ) := by
      have hG_eq : Real.log (Real.Gamma (c + 1)) =
          ((1 / 2 : ℝ) * Real.log (π * (d : ℝ)) + c * Real.log ((d : ℝ) / (2 * Real.exp 1))) + stErr := by
        dsimp [stErr]; ring
      dsimp [modelLog]
      rw [hvol_log, hG_eq, show (d : ℝ) / 2 = c from rfl]
      linarith [hlog_id, hcδ]
    rw [hdiff_eq]
    have hR_pi : |π ^ 2 * R| ≤ π ^ 2 * C₀ := by
      rw [abs_mul, abs_of_pos (sq_pos_of_pos Real.pi_pos)]
      exact mul_le_mul_of_nonneg_left hR_bd (sq_nonneg π)
    linarith [abs_add_le (π ^ 2 * R - stErr) (c * (Real.log (1 + δ) - δ)), abs_sub (π ^ 2 * R) stErr]
  obtain ⟨B, hB_all⟩ := exists_bound_of_tail_bound (fun d => |Real.log (vol d) - modelLog d|)
    d₁ (π ^ 2 * C₀ + 1 + 2 * K₁ ^ 2) hlarge
  refine ⟨⟨Real.exp (-B), Real.exp B, Real.exp_pos (-B), fun d hd => ?_⟩,
    ⟨B + |(1 / 2 : ℝ) * Real.log π|, fun d hd => ?_⟩⟩
  · have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
    let M : ℝ := (π * (d : ℝ)) ^ (-(1 / 2 : ℝ)) * (Real.exp 1 / (2 * π)) ^ ((d : ℝ) / 2) *
      Real.exp (π ^ 2 * A_opt * ((d : ℝ) / 2) ^ (1 / 3 : ℝ))
    have hM_pos : 0 < M := by
      dsimp [M]
      have := Real.rpow_pos_of_pos (mul_pos Real.pi_pos hd_pos) (-(1 / 2 : ℝ))
      have := Real.rpow_pos_of_pos (div_pos (Real.exp_pos 1) (mul_pos two_pos Real.pi_pos)) ((d : ℝ) / 2)
      positivity
    have hlog_M : Real.log M = modelLog d := by
      dsimp [M, modelLog]
      rw [Real.log_mul (mul_pos (Real.rpow_pos_of_pos (mul_pos Real.pi_pos hd_pos) _)
            (Real.rpow_pos_of_pos (div_pos (Real.exp_pos 1) (mul_pos two_pos Real.pi_pos)) _)).ne'
          (Real.exp_pos _).ne',
        Real.log_mul (Real.rpow_pos_of_pos (mul_pos Real.pi_pos hd_pos) _).ne'
          (Real.rpow_pos_of_pos (div_pos (Real.exp_pos 1) (mul_pos two_pos Real.pi_pos)) _).ne',
        Real.log_rpow (mul_pos Real.pi_pos hd_pos),
        Real.log_rpow (div_pos (Real.exp_pos 1) (mul_pos two_pos Real.pi_pos)), Real.log_exp]
      ring
    obtain ⟨hlo, hhi⟩ := abs_le.mp (hB_all d hd)
    exact ⟨(Real.log_le_log_iff (mul_pos (Real.exp_pos _) hM_pos) (hvol_pos d hd)).mp
        (by rw [Real.log_mul (Real.exp_pos _).ne' hM_pos.ne', Real.log_exp, hlog_M]; linarith),
      (Real.log_le_log_iff (hvol_pos d hd) (mul_pos (Real.exp_pos _) hM_pos)).mp
        (by rw [Real.log_mul (Real.exp_pos _).ne' hM_pos.ne', Real.log_exp, hlog_M]; linarith)⟩
  · have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
    have hsplit : Real.log (vol d) -
        (((d : ℝ) / 2) * Real.log (Real.exp 1 / (2 * π)) +
          π ^ 2 * A_opt * ((d : ℝ) / 2) ^ (1 / 3 : ℝ) - (1 / 2 : ℝ) * Real.log (d : ℝ)) =
        (Real.log (vol d) - modelLog d) - (1 / 2 : ℝ) * Real.log π := by
      dsimp [modelLog]; rw [Real.log_mul Real.pi_ne_zero hd_pos.ne']; ring
    rw [hsplit]
    linarith [abs_sub (Real.log (vol d) - modelLog d) ((1 / 2 : ℝ) * Real.log π), hB_all d hd]

/-- **Corollary `7.12a` (`gt:7.12a`), radius comparison:** if two nonnegative sequences `r₁, r₂`
share the expansion `rᵢ(d)² / 2 = d / (2π²) + A_opt (d / 2)^{1/3} + O(1)` for `d ≥ 2`, then
`|r₁ d - r₂ d| = O(d^{-1/2})`. -/
theorem ce_radii_diff_O_inv_sqrt (A_opt : ℝ) {r₁ r₂ : ℕ → ℝ}
    (hr₁_nn : ∀ d : ℕ, 2 ≤ d → 0 ≤ r₁ d) (hr₂_nn : ∀ d : ℕ, 2 ≤ d → 0 ≤ r₂ d)
    (hr₁ : ∃ C₁ : ℝ, ∀ d : ℕ, 2 ≤ d →
      |r₁ d ^ 2 / 2 - ((d : ℝ) / (2 * π ^ 2) + A_opt * ((d : ℝ) / 2) ^ (1 / 3 : ℝ))| ≤ C₁)
    (hr₂ : ∃ C₂ : ℝ, ∀ d : ℕ, 2 ≤ d →
      |r₂ d ^ 2 / 2 - ((d : ℝ) / (2 * π ^ 2) + A_opt * ((d : ℝ) / 2) ^ (1 / 3 : ℝ))| ≤ C₂) :
    ∃ C : ℝ, ∀ d : ℕ, 2 ≤ d → |r₁ d - r₂ d| ≤ C * (d : ℝ) ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨C₁, hC₁⟩ := hr₁
  obtain ⟨C₂, hC₂⟩ := hr₂
  have hC₁_nn : 0 ≤ C₁ := (abs_nonneg _).trans (hC₁ 2 le_rfl)
  let K : ℝ := 4 * π ^ 2 * (|A_opt| + C₁) + 1
  let d₁ : ℕ := max 2 (Nat.ceil (K ^ (3 / 2 : ℝ)) + 1)
  have hsq_diff : ∀ d : ℕ, 2 ≤ d → |r₁ d ^ 2 - r₂ d ^ 2| ≤ 2 * (C₁ + C₂) := fun d hd => by
    have htri : |r₁ d ^ 2 / 2 - r₂ d ^ 2 / 2| ≤ C₁ + C₂ :=
      calc |r₁ d ^ 2 / 2 - r₂ d ^ 2 / 2|
          = |(r₁ d ^ 2 / 2 - ((d : ℝ) / (2 * π ^ 2) + A_opt * ((d : ℝ) / 2) ^ (1 / 3 : ℝ))) -
              (r₂ d ^ 2 / 2 - ((d : ℝ) / (2 * π ^ 2) + A_opt * ((d : ℝ) / 2) ^ (1 / 3 : ℝ)))| := by
            ring_nf
        _ ≤ _ := abs_sub _ _
        _ ≤ C₁ + C₂ := add_le_add (hC₁ d hd) (hC₂ d hd)
    rw [show r₁ d ^ 2 - r₂ d ^ 2 = 2 * (r₁ d ^ 2 / 2 - r₂ d ^ 2 / 2) by ring, abs_mul,
      abs_of_pos two_pos]
    linarith
  have htail : ∀ d : ℕ, d₁ ≤ d → |r₁ d - r₂ d| * √(d : ℝ) ≤ 2 * (C₁ + C₂) * (√2 * π) := by
    intro d hd
    have hd2 : 2 ≤ d := (le_max_left _ _).trans hd
    have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
    have hd_ge1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
    have hK_lt : K ^ (3 / 2 : ℝ) < (d : ℝ) := by
      have hceil : (Nat.ceil (K ^ (3 / 2 : ℝ)) : ℝ) + 1 ≤ d :=
        by exact_mod_cast (le_max_right _ _).trans hd
      linarith [Nat.le_ceil (K ^ (3 / 2 : ℝ))]
    have hK_pow : K < (d : ℝ) ^ (2 / 3 : ℝ) := by
      have hK_pos : 0 < K := by positivity
      have hlt := Real.rpow_lt_rpow (by positivity) hK_lt (by norm_num : (0 : ℝ) < 2 / 3)
      rw [← Real.rpow_mul hK_pos.le] at hlt; norm_num at hlt; exact hlt
    have hc13_le : ((d : ℝ) / 2) ^ (1 / 3 : ℝ) ≤ (d : ℝ) ^ (1 / 3 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
    have hA_term : |A_opt| * ((d : ℝ) / 2) ^ (1 / 3 : ℝ) + C₁ ≤
        (|A_opt| + C₁) * (d : ℝ) ^ (1 / 3 : ℝ) := by
      have h1 : (1 : ℝ) ≤ (d : ℝ) ^ (1 / 3 : ℝ) := Real.one_le_rpow hd_ge1 (by norm_num)
      nlinarith [abs_nonneg A_opt]
    have hsplit_d : (d : ℝ) = (d : ℝ) ^ (2 / 3 : ℝ) * (d : ℝ) ^ (1 / 3 : ℝ) := by
      rw [← Real.rpow_add hd_pos]; norm_num
    have hdom : (|A_opt| + C₁) * (d : ℝ) ^ (1 / 3 : ℝ) ≤ (d : ℝ) / (4 * π ^ 2) := by
      have h1 : 4 * π ^ 2 * (|A_opt| + C₁) ≤ (d : ℝ) ^ (2 / 3 : ℝ) := by dsimp [K] at hK_pow; linarith
      have h2 := mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hd_pos.le (1 / 3 : ℝ))
      rw [← hsplit_d] at h2
      exact (le_div_iff₀ (by positivity)).mpr (by linarith)
    have hr1_sq : (d : ℝ) / (2 * π ^ 2) ≤ r₁ d ^ 2 := by
      have h1 := (abs_le.mp (hC₁ d hd2)).1
      have h2 : |A_opt * ((d : ℝ) / 2) ^ (1 / 3 : ℝ)| ≤ |A_opt| * ((d : ℝ) / 2) ^ (1 / 3 : ℝ) := by
        rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
      have h3 : -(A_opt * ((d : ℝ) / 2) ^ (1 / 3 : ℝ)) ≤ |A_opt| * ((d : ℝ) / 2) ^ (1 / 3 : ℝ) :=
        (neg_le_abs _).trans h2
      have hhalf : (d : ℝ) / (2 * π ^ 2) = 2 * ((d : ℝ) / (4 * π ^ 2)) := by ring
      linarith
    have hr1_ge : √(d : ℝ) / (√2 * π) ≤ r₁ d := by
      refine le_of_pow_le_pow_left₀ two_ne_zero (hr₁_nn d hd2) ?_
      rw [div_pow, mul_pow, Real.sq_sqrt hd_pos.le, Real.sq_sqrt zero_le_two]; linarith
    have hsum_ge : √(d : ℝ) / (√2 * π) ≤ r₁ d + r₂ d := by linarith [hr₂_nn d hd2]
    have hsum_pos : 0 < r₁ d + r₂ d := lt_of_lt_of_le (by positivity) hsum_ge
    have hquot : √(d : ℝ) / (r₁ d + r₂ d) ≤ √2 * π := by
      rw [div_le_iff₀ hsum_pos]
      calc √(d : ℝ) = (√2 * π) * (√(d : ℝ) / (√2 * π)) := by
            field_simp [Real.pi_ne_zero, (Real.sqrt_pos.mpr zero_lt_two).ne']
        _ ≤ (√2 * π) * (r₁ d + r₂ d) := mul_le_mul_of_nonneg_left hsum_ge (by positivity)
    calc |r₁ d - r₂ d| * √(d : ℝ)
        = |r₁ d ^ 2 - r₂ d ^ 2| * (√(d : ℝ) / (r₁ d + r₂ d)) := by
          rw [show r₁ d ^ 2 - r₂ d ^ 2 = (r₁ d - r₂ d) * (r₁ d + r₂ d) by ring,
            abs_mul, abs_of_pos hsum_pos]; field_simp [hsum_pos.ne']
      _ ≤ (2 * (C₁ + C₂)) * (√2 * π) := by
          exact mul_le_mul (hsq_diff d hd2) hquot (by positivity)
            (le_trans (abs_nonneg _) (hsq_diff d hd2))
  obtain ⟨C, hC⟩ := exists_bound_of_tail_bound (fun d => |r₁ d - r₂ d| * √(d : ℝ))
    d₁ (2 * (C₁ + C₂) * (√2 * π)) htail
  refine ⟨C, fun d hd => ?_⟩
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
  rw [Real.rpow_neg hd_pos.le, ← Real.sqrt_eq_rpow]
  exact (le_mul_inv_iff₀ (Real.sqrt_pos.mpr hd_pos)).mpr (hC d hd)

/-- Ordered specialization of `ce_radii_diff_O_inv_sqrt`: `0 ≤ r₁ d - r₂ d ≤ O(d^{-1/2})`. -/
theorem ce_radii_diff_nonneg_O_inv_sqrt (A_opt : ℝ) {r₁ r₂ : ℕ → ℝ}
    (hle : ∀ d : ℕ, 2 ≤ d → r₂ d ≤ r₁ d) (hr₂_nn : ∀ d : ℕ, 2 ≤ d → 0 ≤ r₂ d)
    (hr₁ : ∃ C₁ : ℝ, ∀ d : ℕ, 2 ≤ d →
      |r₁ d ^ 2 / 2 - ((d : ℝ) / (2 * π ^ 2) + A_opt * ((d : ℝ) / 2) ^ (1 / 3 : ℝ))| ≤ C₁)
    (hr₂ : ∃ C₂ : ℝ, ∀ d : ℕ, 2 ≤ d →
      |r₂ d ^ 2 / 2 - ((d : ℝ) / (2 * π ^ 2) + A_opt * ((d : ℝ) / 2) ^ (1 / 3 : ℝ))| ≤ C₂) :
    ∃ C : ℝ, ∀ d : ℕ, 2 ≤ d → 0 ≤ r₁ d - r₂ d ∧ r₁ d - r₂ d ≤ C * (d : ℝ) ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨C, hC⟩ := ce_radii_diff_O_inv_sqrt A_opt (fun d hd => (hr₂_nn d hd).trans (hle d hd))
    hr₂_nn hr₁ hr₂
  exact ⟨C, fun d hd => ⟨sub_nonneg.mpr (hle d hd), (abs_le.mp (hC d hd)).2⟩⟩

/-! ### Section 2: Continuous-`L¹` vs Schwartz Cohn–Elkies Infima (`gt:7.12`) -/

/-- Normalized continuous-`L¹` Cohn–Elkies admissibility on `ℝ^d`: `IsCohnElkiesAdmissible`
together with `h 0 = (𝓕 (fun x => (h x : ℂ)) 0).re`. -/
structure IsContinuousL1CEAdmissible (d : ℕ) (r : ℝ) (h : Euc d → ℝ) : Prop
    extends IsCohnElkiesAdmissible d r h where
  origin_eq : h 0 = (𝓕 (fun x : Euc d => (h x : ℂ)) 0).re

/-- Normalized Schwartz Cohn–Elkies admissibility on `ℝ^d`. -/
structure IsSchwartzCEAdmissible (d : ℕ) (r : ℝ) (h : Euc d → ℝ) : Prop
    extends IsContinuousL1CEAdmissible d r h where
  schwartz : ∃ S : 𝓢(Euc d, ℂ), ∀ x : Euc d, S x = (h x : ℂ)

/-- Infimum of admissible radii over normalized continuous-`L¹` Cohn–Elkies functions on `ℝ^d`. -/
noncomputable def optimalL1CERadius (d : ℕ) : ℝ :=
  sInf { r : ℝ | ∃ h, IsContinuousL1CEAdmissible d r h }

/-- Infimum of admissible radii over normalized Schwartz Cohn–Elkies functions on `ℝ^d`. -/
noncomputable def optimalSchwartzCERadius (d : ℕ) : ℝ :=
  sInf { r : ℝ | ∃ h, IsSchwartzCEAdmissible d r h }

/-- Infimum of `cohnElkiesBound` over normalized Schwartz Cohn–Elkies functions on `ℝ^d`. -/
noncomputable def optimalSchwartzCEBound (d : ℕ) : ℝ :=
  sInf { V : ℝ | ∃ r h, IsSchwartzCEAdmissible d r h ∧ V = cohnElkiesBound d r h }

/-- Fourier transform of spatial reflection of a real integrable function equals the conjugate. -/
private lemma fourier_comp_neg {d : ℕ} {f : Euc d → ℝ} (hf : Integrable f) (y : Euc d) :
    𝓕 (fun x : Euc d => (f (-x) : ℂ)) y = star (𝓕 (fun x : Euc d => (f x : ℂ)) y) := by
  have hC : Integrable (fun x : Euc d => (f x : ℂ)) := Complex.ofRealCLM.integrable_comp hf
  have hconj : star (∫ x : Euc d, 𝐞 (-⟪x, y⟫) • (f x : ℂ)) =
      ∫ x : Euc d, star (𝐞 (-⟪x, y⟫) • (f x : ℂ)) :=
    ((Complex.conjCLE : ℂ →L[ℝ] ℂ).integral_comp_comm
      ((Real.fourierIntegral_convergent_iff y).mpr hC)).symm
  rw [Real.fourier_eq, Real.fourier_eq, hconj, ← integral_neg_eq_self]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  dsimp only
  rw [neg_neg, inner_neg_left, neg_neg, Circle.smul_def, Circle.smul_def, smul_eq_mul, smul_eq_mul,
    star_mul, Complex.star_def, Complex.conj_ofReal, ← Circle.coe_inv_eq_conj,
    ← AddChar.map_neg_eq_inv, neg_neg, mul_comm (f x : ℂ)]

/-- Fourier transform at `0` of an integrable real function equals its real integral coerced to `ℂ`. -/
private lemma fourier_zero_eq {d : ℕ} {f : Euc d → ℝ} (hf : Integrable f) :
    𝓕 (fun x : Euc d => (f x : ℂ)) 0 = ((∫ x : Euc d, f x : ℝ) : ℂ) := by
  have h0 : 𝓕 (fun x : Euc d => (f x : ℂ)) 0 = ∫ x : Euc d, (f x : ℂ) := by
    simp [Real.fourier_eq]
  rw [h0]
  change ∫ x : Euc d, Complex.ofRealCLM (f x) = Complex.ofRealCLM (∫ x : Euc d, f x)
  rw [← Complex.ofRealCLM.integral_comp_comm hf]

/-- Real part of the Fourier transform at `0` of an integrable real function equals its integral. -/
private lemma fourier_zero_re_eq {d : ℕ} {f : Euc d → ℝ} (hf : Integrable f) :
    (𝓕 (fun x : Euc d => (f x : ℂ)) 0).re = ∫ x : Euc d, f x := by
  rw [fourier_zero_eq hf, Complex.ofReal_re]

/-- Symmetrizing a continuous `L¹` function `h` whose Fourier transform has integrable nonnegative
real part produces an `IsContinuousL1CEAdmissible` function `x ↦ (h x + h (-x)) / 2`. -/
theorem IsContinuousL1CEAdmissible.ofRealPartNonneg {d : ℕ} {r : ℝ} {h : Euc d → ℝ}
    (hr : 0 < r) (hc : Continuous h) (hi : Integrable h)
    (hfi_re : Integrable (fun y : Euc d => (𝓕 (fun x : Euc d => (h x : ℂ)) y).re))
    (h0 : 0 < h 0) (heq : h 0 = (𝓕 (fun x : Euc d => (h x : ℂ)) 0).re)
    (hout : ∀ x : Euc d, r ≤ ‖x‖ → h x ≤ 0)
    (hfnn : ∀ y : Euc d, 0 ≤ (𝓕 (fun x : Euc d => (h x : ℂ)) y).re) :
    IsContinuousL1CEAdmissible d r (fun x => (h x + h (-x)) / 2) := by
  set h_even : Euc d → ℝ := fun x => (h x + h (-x)) / 2
  have hneg_int : Integrable (fun x : Euc d => h (-x)) := by
    simpa [Function.comp_def] using
      ((LinearIsometryEquiv.neg ℝ (E := Euc d)).measurePreserving.integrable_comp_emb
        (LinearIsometryEquiv.neg ℝ (E := Euc d)).toHomeomorph.measurableEmbedding).mpr hi
  have hft_even : ∀ y : Euc d,
      𝓕 (fun x : Euc d => (h_even x : ℂ)) y = ((𝓕 (fun x : Euc d => (h x : ℂ)) y).re : ℂ) := by
    intro y
    have hC1 : Integrable (fun x : Euc d => (h x : ℂ)) := Complex.ofRealCLM.integrable_comp hi
    have hC2 : Integrable (fun x : Euc d => (h (-x) : ℂ)) := Complex.ofRealCLM.integrable_comp hneg_int
    have hrew : (fun x : Euc d => (h_even x : ℂ)) =
        fun x => (1 / 2 : ℂ) * ((h x : ℂ) + (h (-x) : ℂ)) := by
      ext x; dsimp [h_even]; push_cast; ring
    have hlin : 𝓕 (fun x : Euc d => (1 / 2 : ℂ) * ((h x : ℂ) + (h (-x) : ℂ))) y =
        (1 / 2 : ℂ) * (𝓕 (fun x : Euc d => (h x : ℂ)) y +
          𝓕 (fun x : Euc d => (h (-x) : ℂ)) y) := by
      simp only [Real.fourier_eq]
      have hi1 := (Real.fourierIntegral_convergent_iff y).mpr hC1
      have hi2 := (Real.fourierIntegral_convergent_iff y).mpr hC2
      have hsum : (fun x : Euc d => 𝐞 (-⟪x, y⟫) • ((1 / 2 : ℂ) * ((h x : ℂ) + (h (-x) : ℂ)))) =
          fun x => (1 / 2 : ℂ) * (𝐞 (-⟪x, y⟫) • (h x : ℂ) + 𝐞 (-⟪x, y⟫) • (h (-x) : ℂ)) := by
        ext x; simp only [Circle.smul_def]; ring
      rw [hsum, integral_const_mul, integral_add hi1 hi2]
    rw [hrew, hlin, fourier_comp_neg hi y, Complex.star_def, Complex.add_conj]
    push_cast; ring
  have hfi_even : Integrable (𝓕 (fun x : Euc d => (h_even x : ℂ))) := by
    simpa only [funext hft_even, Complex.ofRealCLM_apply] using Complex.ofRealCLM.integrable_comp hfi_re
  refine ⟨⟨hr, (hc.add (hc.comp continuous_neg)).div_const 2, (hi.add hneg_int).div_const 2,
      hfi_even, by dsimp [h_even]; rw [neg_zero]; linarith, ?_, ?_, ?_⟩, ?_⟩
  · rw [hft_even 0, Complex.ofReal_re, ← heq]; exact h0
  · intro x hx; dsimp [h_even]
    linarith [hout x hx, hout (-x) (by simpa only [norm_neg] using hx)]
  · intro y; rw [hft_even y, Complex.ofReal_im, Complex.ofReal_re]; exact ⟨rfl, hfnn y⟩
  · dsimp [h_even]; rw [hft_even 0, Complex.ofReal_re, neg_zero, ← heq]; ring

/-- Dilation scaling of the Fourier transform on `ℝ^d`: for `0 < μ`,
`𝓕 (fun x => f (μ • x)) y = μ ^ (-d) * 𝓕 f (μ⁻¹ • y)`. -/
lemma fourier_comp_smul {d : ℕ} (f : Euc d → ℂ) {μ : ℝ} (hμ : 0 < μ) (y : Euc d) :
    𝓕 (fun x : Euc d => f (μ • x)) y = ((μ ^ (-(d : ℝ)) : ℝ) : ℂ) * 𝓕 f (μ⁻¹ • y) := by
  calc 𝓕 (fun x : Euc d => f (μ • x)) y
      = ∫ x : Euc d, 𝐞 (-⟪x, y⟫) • f (μ • x) := rfl
    _ = ∫ x : Euc d, 𝐞 (-⟪μ • x, μ⁻¹ • y⟫) • f (μ • x) := by
        congr 1; ext x; congr 2
        simp only [inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial]
        rw [← mul_assoc, inv_mul_cancel₀ hμ.ne', one_mul]
    _ = (μ ^ d)⁻¹ • ∫ z : Euc d, 𝐞 (-⟪z, μ⁻¹ • y⟫) • f z := by
        simpa [finrank_euclideanSpace_fin] using
          (Measure.integral_comp_smul_of_nonneg (μ := (volume : Measure (Euc d)))
            (fun z : Euc d => 𝐞 (-⟪z, μ⁻¹ • y⟫) • f z) μ (hR := hμ.le))
    _ = ((μ ^ (-(d : ℝ)) : ℝ) : ℂ) * 𝓕 f (μ⁻¹ • y) := by
        rw [← Real.rpow_natCast μ d, ← Real.rpow_neg hμ.le, Complex.real_smul]; rfl

/-- Rescaling an arbitrary `IsCohnElkiesAdmissible d r h` (`d ≥ 1`) by
`μ = ((𝓕 h 0).re / h 0) ^ (1 / d)` preserves `cohnElkiesBound` and Schwartz regularity. -/
theorem IsCohnElkiesAdmissible.rescale_to_normalized {d : ℕ} (hd : 1 ≤ d) {r : ℝ} {h : Euc d → ℝ}
    (hadm : IsCohnElkiesAdmissible d r h) :
    let μ : ℝ := ((𝓕 (fun x : Euc d => (h x : ℂ)) 0).re / h 0) ^ (1 / (d : ℝ))
    let h' : Euc d → ℝ := fun x => h (μ • x)
    IsContinuousL1CEAdmissible d (r / μ) h' ∧
      (volume : Measure (Euc d)).real (Metric.ball 0 ((r / μ) / 2)) = cohnElkiesBound d r h ∧
      ((∃ S : 𝓢(Euc d, ℂ), ∀ x, S x = (h x : ℂ)) → IsSchwartzCEAdmissible d (r / μ) h') := by
  intro μ h'
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hμ_pos : 0 < μ := Real.rpow_pos_of_pos (div_pos hadm.fourier_origin_pos hadm.origin_pos) _
  have hμ_pow : μ ^ (d : ℝ) = (𝓕 (fun x : Euc d => (h x : ℂ)) 0).re / h 0 := by
    dsimp [μ]
    rw [← Real.rpow_mul (div_pos hadm.fourier_origin_pos hadm.origin_pos).le,
      one_div_mul_cancel hd_pos.ne', Real.rpow_one]
  have hμ_neg : μ ^ (-(d : ℝ)) = h 0 / (𝓕 (fun x : Euc d => (h x : ℂ)) 0).re := by
    rw [Real.rpow_neg hμ_pos.le, hμ_pow, inv_div]
  have hft : ∀ y : Euc d, 𝓕 (fun x : Euc d => (h' x : ℂ)) y =
      ((μ ^ (-(d : ℝ)) : ℝ) : ℂ) * 𝓕 (fun x : Euc d => (h x : ℂ)) (μ⁻¹ • y) := fun y =>
    fourier_comp_smul (fun x => (h x : ℂ)) hμ_pos y
  have hfi : Integrable (𝓕 (fun x : Euc d => (h' x : ℂ))) :=
    ((hadm.fourier_integrable.comp_smul (μ := (volume : Measure (Euc d)))
      (inv_ne_zero hμ_pos.ne')).const_mul _).congr (Eventually.of_forall fun y => (hft y).symm)
  have h0_eq : h' 0 = (𝓕 (fun x : Euc d => (h' x : ℂ)) 0).re := by
    dsimp [h']; rw [smul_zero, hft 0, smul_zero, Complex.re_ofReal_mul, hμ_neg]
    field_simp [hadm.fourier_origin_pos.ne']
  have hadm' : IsContinuousL1CEAdmissible d (r / μ) h' := by
    refine ⟨⟨div_pos hadm.r_pos hμ_pos, hadm.continuous.comp (continuous_const_smul μ),
        hadm.integrable.comp_smul (μ := (volume : Measure (Euc d))) hμ_pos.ne', hfi,
        by dsimp [h']; rw [smul_zero]; exact hadm.origin_pos,
        by rw [← h0_eq]; dsimp [h']; rw [smul_zero]; exact hadm.origin_pos,
        fun x hx => hadm.nonpos_outside (μ • x) ?_, fun y => ?_⟩, h0_eq⟩
    · rw [norm_smul, Real.norm_of_nonneg hμ_pos.le]; exact (div_le_iff₀' hμ_pos).mp hx
    · obtain ⟨him, hre⟩ := hadm.fourier_nonneg (μ⁻¹ • y)
      rw [hft y, Complex.im_ofReal_mul, Complex.re_ofReal_mul, him, mul_zero]
      exact ⟨rfl, mul_nonneg (Real.rpow_nonneg hμ_pos.le _) hre⟩
  have hvol : (volume : Measure (Euc d)).real (Metric.ball 0 ((r / μ) / 2)) =
      cohnElkiesBound d r h := by
    rw [volume_half_ball_eq hd (div_pos hadm.r_pos hμ_pos).le,
      cohnElkiesBound, volume_half_ball_eq hd hadm.r_pos.le]
    have hpow_div : (π * (r / μ) ^ 2 / 4) ^ ((d : ℝ) / 2) =
        μ ^ (-(d : ℝ)) * (π * r ^ 2 / 4) ^ ((d : ℝ) / 2) := by
      have hrw : π * (r / μ) ^ 2 / 4 = μ ^ (-2 : ℝ) * (π * r ^ 2 / 4) := by
        rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hμ_pos.le,
          Real.rpow_natCast, div_pow]; ring
      rw [hrw, Real.mul_rpow (Real.rpow_nonneg hμ_pos.le _) (by positivity),
        ← Real.rpow_mul hμ_pos.le]
      congr 2; ring
    rw [hpow_div, hμ_neg]; ring
  refine ⟨hadm', hvol, fun ⟨S, hS⟩ => ⟨hadm', ?_⟩⟩
  let e : Euc d ≃L[ℝ] Euc d :=
    { toFun := (μ • ·), map_add' := smul_add μ, map_smul' := fun c x => smul_comm μ c x,
      invFun := (μ⁻¹ • ·), left_inv := fun x => by simp [hμ_pos.ne'],
      right_inv := fun x => by simp [hμ_pos.ne'],
      continuous_toFun := continuous_const_smul μ, continuous_invFun := continuous_const_smul μ⁻¹ }
  exact ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e S, fun x => hS (μ • x)⟩

/-- Boundedness and Minkowski-type volume lower bound for `IsContinuousL1CEAdmissible`. -/
lemma IsContinuousL1CEAdmissible.abs_le_origin_and_vol_ge {d : ℕ} (hd : 1 ≤ d) {r : ℝ}
    {h : Euc d → ℝ} (hadm : IsContinuousL1CEAdmissible d r h) :
    (∀ x : Euc d, |h x| ≤ h 0) ∧
      1 ≤ (volume : Measure (Euc d)).real (Metric.ball 0 r) ∧
      (2 : ℝ) ^ (-(d : ℝ)) ≤ cohnElkiesBound d r h := by
  have hC_cont : Continuous (fun x : Euc d => (h x : ℂ)) := Complex.continuous_ofReal.comp hadm.continuous
  have hC_int : Integrable (fun x : Euc d => (h x : ℂ)) := Complex.ofRealCLM.integrable_comp hadm.integrable
  have hinv : ∀ x : Euc d, 𝓕⁻ (𝓕 (fun t : Euc d => (h t : ℂ))) x = (h x : ℂ) := fun x =>
    congrFun (hC_cont.fourierInv_fourier_eq hC_int hadm.fourier_integrable) x
  have hnorm_ft : ∀ y : Euc d,
      ‖𝓕 (fun t : Euc d => (h t : ℂ)) y‖ = (𝓕 (fun t : Euc d => (h t : ℂ)) y).re := by
    intro y; obtain ⟨him, hre⟩ := hadm.fourier_nonneg y
    conv_lhs => rw [show 𝓕 (fun t : Euc d => (h t : ℂ)) y =
      ((𝓕 (fun t : Euc d => (h t : ℂ)) y).re : ℂ) from Complex.ext rfl him]
    rw [Complex.norm_real, Real.norm_of_nonneg hre]
  have hint_ft : ∫ y : Euc d, ‖𝓕 (fun t : Euc d => (h t : ℂ)) y‖ = h 0 := by
    have h0_inv : (h 0 : ℂ) = ∫ y : Euc d, 𝓕 (fun t : Euc d => (h t : ℂ)) y := by
      simpa [Real.fourierInv_eq] using (hinv 0).symm
    have hre0 := congrArg Complex.re h0_inv
    change h 0 = Complex.reCLM (∫ y : Euc d, 𝓕 (fun t : Euc d => (h t : ℂ)) y) at hre0
    rw [← Complex.reCLM.integral_comp_comm hadm.fourier_integrable] at hre0
    simpa [Complex.reCLM_apply, hnorm_ft] using hre0.symm
  have h_abs : ∀ x : Euc d, |h x| ≤ h 0 := fun x => by
    have hx_inv : (h x : ℂ) = ∫ y : Euc d, 𝐞 ⟪y, x⟫ • 𝓕 (fun t : Euc d => (h t : ℂ)) y := by
      simpa [Real.fourierInv_eq] using (hinv x).symm
    rw [show |h x| = ‖(h x : ℂ)‖ by rw [Complex.norm_real, Real.norm_eq_abs], hx_inv]
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    simp_rw [Circle.norm_smul, hint_ft]
  have h_ind_int : Integrable ((Metric.ball (0 : Euc d) r).indicator (fun _ => h 0)) :=
    (integrableOn_const (hs := measure_ball_lt_top.ne)).integrable_indicator measurableSet_ball
  have h_le_ind : h 0 ≤ (volume : Measure (Euc d)).real (Metric.ball 0 r) * h 0 := by
    have hmono : ∫ x : Euc d, h x ≤
        ∫ x : Euc d, (Metric.ball (0 : Euc d) r).indicator (fun _ => h 0) x := by
      refine integral_mono hadm.integrable h_ind_int fun x => ?_
      by_cases hx : x ∈ Metric.ball (0 : Euc d) r
      · rw [indicator_of_mem hx]; exact (le_abs_self _).trans (h_abs x)
      · rw [indicator_of_notMem hx]
        rw [Metric.mem_ball, dist_zero_right, not_lt] at hx
        exact hadm.nonpos_outside x hx
    rw [integral_indicator measurableSet_ball, setIntegral_const, smul_eq_mul] at hmono
    linarith [hadm.origin_eq, fourier_zero_re_eq hadm.integrable]
  have hvol_ge : 1 ≤ (volume : Measure (Euc d)).real (Metric.ball 0 r) :=
    (mul_le_mul_iff_left₀ hadm.origin_pos).mp (by simpa using h_le_ind)
  have hvol_eq : (volume : Measure (Euc d)).real (Metric.ball 0 (r / 2)) =
      (2 : ℝ) ^ (-(d : ℝ)) * (volume : Measure (Euc d)).real (Metric.ball 0 r) := by
    have h1 := volume_half_ball_eq hd hadm.r_pos.le
    have h2 := volume_half_ball_eq hd (r := 2 * r) (mul_nonneg zero_le_two hadm.r_pos.le)
    rw [show 2 * r / 2 = r by ring, show π * (2 * r) ^ 2 / 4 = 4 * (π * r ^ 2 / 4) by ring] at h2
    rw [h1, h2, Real.mul_rpow (by norm_num) (by positivity),
      show (4 : ℝ) ^ ((d : ℝ) / 2) = (2 : ℝ) ^ (d : ℝ) by
        rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul two_pos.le]; congr 1; ring,
      Real.rpow_neg two_pos.le]
    field_simp [(Real.rpow_pos_of_pos two_pos _).ne']
  have hbound : cohnElkiesBound d r h = (volume : Measure (Euc d)).real (Metric.ball 0 (r / 2)) := by
    unfold cohnElkiesBound; rw [← hadm.origin_eq, div_self hadm.origin_pos.ne', one_mul]
  exact ⟨h_abs, hvol_ge, by rw [hbound, hvol_eq]; exact le_mul_of_one_le_right (by positivity) hvol_ge⟩

/-- Nonemptiness and positive radius lower bound for `IsSchwartzCEAdmissible` (`d ≥ 1`). -/
lemma schwartzCE_nonempty_and_lower_bound {d : ℕ} (hd : 1 ≤ d) :
    (∃ r h, IsSchwartzCEAdmissible d r h) ∧
      ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r h, IsContinuousL1CEAdmissible d r h → r₀ ≤ r := by
  have hu : 0 < cubicU d := by
    unfold cubicU
    have : 2 < ((d : ℝ) + 6) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) d]
    exact div_pos (by linarith) (by positivity)
  have hcubic_adm : IsCohnElkiesAdmissible d (cubicR d) (cubicH d) := by
    unfold cubicR
    obtain ⟨⟨S, hS⟩, _⟩ := cubicH_radial d
    have hS_eq : (fun x : Euc d => (cubicH d x : ℂ)) = S := funext fun x => (hS x).symm
    refine ⟨Real.sqrt_pos.mpr (by positivity), by unfold cubicH; fun_prop,
      (Complex.reCLM.integrable_comp (hS_eq ▸ S.integrable)).congr (Eventually.of_forall fun _ => by simp),
      by rw [hS_eq]; exact (𝓕 S).integrable,
      by rw [(cubicH_origin d).1]; unfold cubicTheta; positivity,
      by rw [(cubicH_origin d).2, Complex.ofReal_re]; unfold cubicTheta; positivity,
      fun x hx => (cubicH_neg_ge_u d x hx).le, fun y => ?_⟩
    rw [cubicH_fourier_eq]
    refine ⟨rfl, ?_⟩
    simp only [Complex.ofReal_re]; unfold cubicTheta
    exact mul_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) (Real.exp_pos _).le
  have hcubic_eq : cubicH d 0 = (𝓕 (fun x : Euc d => (cubicH d x : ℂ)) 0).re := by
    rw [(cubicH_origin d).1, (cubicH_origin d).2, Complex.ofReal_re]
  let r₀ : ℝ := Real.sqrt (Real.Gamma ((d : ℝ) / 2 + 1) ^ (2 / (d : ℝ)) / π)
  have hr₀_pos : 0 < r₀ := by
    dsimp [r₀]; have := Real.Gamma_pos_of_pos (by positivity : (0 : ℝ) < (d : ℝ) / 2 + 1); positivity
  refine ⟨⟨cubicR d, cubicH d, ⟨⟨hcubic_adm, hcubic_eq⟩, (cubicH_radial d).1⟩⟩,
    r₀, hr₀_pos, fun r h hadm => ?_⟩
  have hvol := (hadm.abs_le_origin_and_vol_ge hd).2.1
  have hvol_eq := volume_half_ball_eq hd (r := 2 * r) (mul_nonneg zero_le_two hadm.r_pos.le)
  rw [show 2 * r / 2 = r by ring, show π * (2 * r) ^ 2 / 4 = π * r ^ 2 by ring] at hvol_eq
  rw [hvol_eq, one_le_div (Real.Gamma_pos_of_pos (by positivity))] at hvol
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hG_rpow := Real.rpow_le_rpow (Real.Gamma_pos_of_pos (by positivity)).le hvol
    (by positivity : (0 : ℝ) ≤ 2 / (d : ℝ))
  rw [← Real.rpow_mul (by positivity), show ((d : ℝ) / 2) * (2 / (d : ℝ)) = 1 by
    field_simp [hd_pos.ne'], Real.rpow_one] at hG_rpow
  have hr_sq : Real.Gamma ((d : ℝ) / 2 + 1) ^ (2 / (d : ℝ)) / π ≤ r ^ 2 := by
    rwa [div_le_iff₀' Real.pi_pos]
  rw [← Real.sqrt_sq hadm.r_pos.le]
  exact Real.sqrt_le_sqrt hr_sq

/-- Schwartz decay of `g ⋆[L, volume] ψ` for continuous Gaussian-bounded `g` and `ψ ∈ C^∞_c`. -/
private lemma convolution_gaussian_bound_decay {d : ℕ} {g : Euc d → ℝ}
    (hg_cont : Continuous g) {M η : ℝ} (hM : 0 ≤ M) (hη : 0 < η)
    (hg_bd : ∀ x : Euc d, |g x| ≤ M * Real.exp (-π * η * ‖x‖ ^ 2)) :
    ∀ (n : ℕ) (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
      (G : Type) [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
      (L : ℝ →L[ℝ] F →L[ℝ] G) (ψ : Euc d → F),
      HasCompactSupport ψ → ContDiff ℝ ∞ ψ →
      ∀ k : ℕ, ∃ C : ℝ, ∀ x : Euc d,
        ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (g ⋆[L, volume] ψ) x‖ ≤ C := by
  intro n
  induction n with
  | zero =>
    intro F _ _ _ G _ _ _ L ψ hψ_supp hψ_cd k
    obtain ⟨R₀, hR₀⟩ := hψ_supp.isCompact.isBounded.subset_closedBall 0
    let R : ℝ := max R₀ 0
    have hR_nn : 0 ≤ R := le_max_right _ _
    have hψ_supp_R : tsupport ψ ⊆ Metric.closedBall 0 R :=
      hR₀.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
    let a : ℝ := π * η
    have ha : 0 < a := mul_pos Real.pi_pos hη
    let C₁ : ℝ := 2 ^ k * (1 + (Nat.factorial k : ℝ) / a ^ k)
    have hC₁ : ∀ z : Euc d, (1 + ‖z‖) ^ k * Real.exp (-π * η * ‖z‖ ^ 2) ≤ C₁ := fun z => by
      have h1 : (1 + ‖z‖) ^ k ≤ 2 ^ k * (1 + ‖z‖ ^ (2 * k)) := by
        by_cases hz : ‖z‖ ≤ 1
        · exact (pow_le_pow_left₀ (by positivity) (by linarith) k).trans
            (le_mul_of_one_le_right (by positivity) (le_add_of_nonneg_right (by positivity)))
        · have hz1 : 1 ≤ ‖z‖ := le_of_not_ge hz
          calc (1 + ‖z‖) ^ k ≤ (2 * ‖z‖) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
            _ = 2 ^ k * ‖z‖ ^ k := mul_pow _ _ _
            _ ≤ 2 ^ k * (1 + ‖z‖ ^ (2 * k)) := by
                gcongr; linarith [pow_le_pow_right₀ hz1 (by omega : k ≤ 2 * k)]
      have hexp_le : Real.exp (-a * ‖z‖ ^ 2) ≤ 1 :=
        Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _))
      have hterm : ‖z‖ ^ (2 * k) * Real.exp (-a * ‖z‖ ^ 2) ≤ (Nat.factorial k : ℝ) / a ^ k := by
        have hpow := Real.pow_div_factorial_le_exp (a * ‖z‖ ^ 2) (mul_nonneg ha.le (sq_nonneg ‖z‖)) k
        rw [mul_pow, ← pow_mul, div_le_iff₀ (by positivity)] at hpow
        rw [show -a * ‖z‖ ^ 2 = -(a * ‖z‖ ^ 2) by ring, Real.exp_neg, ← div_eq_mul_inv,
          div_le_div_iff₀ (Real.exp_pos _) (pow_pos ha k)]
        linarith [hpow]
      have hmain : (1 + ‖z‖) ^ k * Real.exp (-a * ‖z‖ ^ 2) ≤ C₁ := by
        calc (1 + ‖z‖) ^ k * Real.exp (-a * ‖z‖ ^ 2)
            ≤ 2 ^ k * (1 + ‖z‖ ^ (2 * k)) * Real.exp (-a * ‖z‖ ^ 2) :=
              mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
          _ = 2 ^ k * (Real.exp (-a * ‖z‖ ^ 2) + ‖z‖ ^ (2 * k) * Real.exp (-a * ‖z‖ ^ 2)) := by ring
          _ ≤ C₁ := by dsimp [C₁]; gcongr
      rw [show (-π * η * ‖z‖ ^ 2) = -a * ‖z‖ ^ 2 by dsimp [a]; ring]
      exact hmain
    let C : ℝ := (1 + R) ^ k * ‖L‖ * M * C₁ * ∫ y : Euc d, ‖ψ y‖
    refine ⟨C, fun x => ?_⟩
    rw [norm_iteratedFDeriv_zero, ← convolution_flip]
    have hconv_ex := hψ_supp.convolutionExists_right L (hg_cont.locallyIntegrable : LocallyIntegrable g volume)
      hψ_cd.continuous x
    have hnorm_le : ‖(ψ ⋆[L.flip, volume] g) x‖ ≤ ∫ y : Euc d, ‖L (g (x - y)) (ψ y)‖ :=
      norm_integral_le_integral_norm _
    have hψ_norm_int : Integrable (fun y : Euc d => ‖ψ y‖) :=
      (hψ_cd.continuous.integrable_of_hasCompactSupport hψ_supp).norm
    have hpt : ∀ y : Euc d,
        ‖x‖ ^ k * ‖L (g (x - y)) (ψ y)‖ ≤ ((1 + R) ^ k * ‖L‖ * M * C₁) * ‖ψ y‖ := fun y => by
      by_cases hy : y ∈ tsupport ψ
      · have hyR : ‖y‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hψ_supp_R hy
        have htri : ‖x‖ ≤ (1 + R) * (1 + ‖x - y‖) := by
          have : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by simpa [sub_add_cancel] using norm_add_le (x - y) y
          nlinarith [norm_nonneg (x - y)]
        have hpow_x : ‖x‖ ^ k ≤ (1 + R) ^ k * (1 + ‖x - y‖) ^ k := by
          rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) htri k
        have hL_bd : ‖L (g (x - y)) (ψ y)‖ ≤ ‖L‖ * |g (x - y)| * ‖ψ y‖ := by
          simpa [Real.norm_eq_abs] using L.le_opNorm₂ (g (x - y)) (ψ y)
        calc ‖x‖ ^ k * ‖L (g (x - y)) (ψ y)‖
            ≤ ((1 + R) ^ k * (1 + ‖x - y‖) ^ k) *
                (‖L‖ * (M * Real.exp (-π * η * ‖x - y‖ ^ 2)) * ‖ψ y‖) := by
              refine mul_le_mul hpow_x (hL_bd.trans ?_) (norm_nonneg _) (by positivity)
              gcongr; exact hg_bd (x - y)
          _ = (1 + R) ^ k * ‖L‖ * M *
                ((1 + ‖x - y‖) ^ k * Real.exp (-π * η * ‖x - y‖ ^ 2)) * ‖ψ y‖ := by ring
          _ ≤ ((1 + R) ^ k * ‖L‖ * M * C₁) * ‖ψ y‖ := by gcongr; exact hC₁ (x - y)
      · rw [image_eq_zero_of_notMem_tsupport hy, (L _).map_zero, norm_zero, mul_zero]; positivity
    have h_int_norm : Integrable (fun y : Euc d => ‖L (g (x - y)) (ψ y)‖) :=
      (convolutionExistsAt_flip.mpr hconv_ex).integrable.norm
    have hmul_le : ‖x‖ ^ k * ∫ y : Euc d, ‖L (g (x - y)) (ψ y)‖ ≤ C := by
      rw [← integral_const_mul]
      calc ∫ y : Euc d, ‖x‖ ^ k * ‖L (g (x - y)) (ψ y)‖
          ≤ ∫ y : Euc d, ((1 + R) ^ k * ‖L‖ * M * C₁) * ‖ψ y‖ :=
            integral_mono (h_int_norm.const_mul _) (hψ_norm_int.const_mul _) hpt
        _ = C := by rw [integral_const_mul]
    exact (mul_le_mul_of_nonneg_left hnorm_le (pow_nonneg (norm_nonneg _) k)).trans hmul_le
  | succ n ih =>
    intro F _ _ _ G _ _ _ L ψ hψ_supp hψ_cd k
    have hfderiv : fderiv ℝ (g ⋆[L, volume] ψ) = g ⋆[L.precompR (Euc d), volume] (fderiv ℝ ψ) := by
      ext1 x
      exact (hψ_supp.hasFDerivAt_convolution_right L hg_cont.locallyIntegrable
        (hψ_cd.of_le (by simp)) x).fderiv
    obtain ⟨C, hC⟩ := ih (Euc d →L[ℝ] F) (Euc d →L[ℝ] G) (L.precompR (Euc d)) (fderiv ℝ ψ)
      (hψ_supp.fderiv ℝ) (contDiff_infty_iff_fderiv.mp hψ_cd).2 k
    exact ⟨C, fun x => by rw [← norm_iteratedFDeriv_fderiv, hfderiv]; exact hC x⟩

/-- Gaussian damping preserves nonnegativity and reality of the Fourier transform via
Fubini's theorem (`𝓕 (h · e^{-π η ‖·‖²}) = 𝓕 h * u_η`). -/
private lemma fourier_mul_gaussian_nonneg {d : ℕ} {h : Euc d → ℝ} (hc : Continuous h)
    (hi : Integrable h) (hft_cont : Continuous (𝓕 (fun x : Euc d => (h x : ℂ))))
    (hfnn : ∀ y : Euc d, (𝓕 (fun x : Euc d => (h x : ℂ)) y).im = 0 ∧
      0 ≤ (𝓕 (fun x : Euc d => (h x : ℂ)) y).re)
    {η : ℝ} (hη : 0 < η) (y : Euc d) :
    (𝓕 (fun x : Euc d => ((h x * Real.exp (-π * η * ‖x‖ ^ 2) : ℝ) : ℂ)) y).im = 0 ∧
      0 ≤ (𝓕 (fun x : Euc d => ((h x * Real.exp (-π * η * ‖x‖ ^ 2) : ℝ) : ℂ)) y).re := by
  let u : Euc d → ℝ := fun z => η ^ (-(d : ℝ) / 2) * Real.exp (-π * ‖z‖ ^ 2 / η)
  have hu_pos : ∀ z, 0 < u z := fun z => by dsimp [u]; positivity
  have hu_cont : Continuous u :=
    continuous_const.mul (Real.continuous_exp.comp ((continuous_const.mul (continuous_norm.pow 2)).div_const _))
  have hu_int : Integrable u := by
    have hS : Integrable (gaussianSchwartz d (inv_pos.mpr hη)) volume :=
      (gaussianSchwartz d (inv_pos.mpr hη)).integrable
    refine ((Complex.reCLM.integrable_comp hS).const_mul (η ^ (-(d : ℝ) / 2))).congr
      (Eventually.of_forall fun z => ?_)
    change η ^ (-(d : ℝ) / 2) * (Real.exp (-π * η⁻¹ * ‖z‖ ^ 2) : ℂ).re = u z
    rw [Complex.ofReal_re]
    dsimp [u]
    rw [show -π * ‖z‖ ^ 2 / η = -π * η⁻¹ * ‖z‖ ^ 2 by ring]
  have hexp_rep : ∀ x : Euc d, (Real.exp (-π * η * ‖x‖ ^ 2) : ℂ) =
      ∫ z : Euc d, Complex.exp (↑(2 * π * ⟪x, z⟫) * I) * (u z : ℂ) := fun x => by
    have hfG := fourier_normSq_pow_gaussian d 0 (inv_pos.mpr hη) x
    simp only [pow_zero, one_mul, Nat.cast_zero, sub_zero, fourierBasisPoly,
      Polynomial.eval_one, mul_one, div_inv_eq_mul] at hfG
    rw [Real.fourier_eq', ← integral_neg_eq_self] at hfG
    have hscale : (η⁻¹) ^ (-(d : ℝ) / 2) = η ^ ((d : ℝ) / 2) := by
      rw [Real.inv_rpow hη.le, ← Real.rpow_neg hη.le]; congr 1; ring
    have h1 : (η ^ (-(d : ℝ) / 2) : ℝ) * η ^ ((d : ℝ) / 2) = 1 := by
      rw [← Real.rpow_add hη, neg_div, neg_add_cancel, Real.rpow_zero]
    have hmul_eq : (Real.exp (-π * η * ‖x‖ ^ 2) : ℂ) = ((η ^ (-(d : ℝ) / 2) : ℝ) : ℂ) *
        ∫ z : Euc d, Complex.exp (↑(-2 * π * ⟪-z, x⟫) * I) •
          (Real.exp (-π * η⁻¹ * ‖-z‖ ^ 2) : ℂ) := by
      rw [hfG, hscale, Complex.ofReal_mul, ← mul_assoc, ← Complex.ofReal_mul, h1,
        Complex.ofReal_one, one_mul, mul_right_comm (-π) (‖x‖ ^ 2) η]
    rw [hmul_eq, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [smul_eq_mul, inner_neg_left, norm_neg, real_inner_comm, u]
    have hexp : Complex.exp (↑(-2 * π * -⟪x, z⟫) * I) = Complex.exp (↑(2 * π * ⟪x, z⟫) * I) :=
      congrArg Complex.exp (congrArg (· * I) (congrArg ((↑) : ℝ → ℂ) (by ring)))
    have hrexp : Real.exp (-π * η⁻¹ * ‖z‖ ^ 2) = Real.exp (-π * ‖z‖ ^ 2 / η) :=
      congrArg Real.exp (by ring)
    rw [hexp, hrexp, mul_left_comm ((η ^ (-(d : ℝ) / 2) : ℝ) : ℂ), ← Complex.ofReal_mul]
  have hcont_prod : Continuous (Function.uncurry fun x z : Euc d =>
      Complex.exp (↑(-2 * π * ⟪x, y⟫) * I) * ((h x : ℂ) *
        (Complex.exp (↑(2 * π * ⟪x, z⟫) * I) * (u z : ℂ)))) :=
    (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
      (continuous_const.mul (continuous_fst.inner continuous_const))).mul continuous_const)).mul
      ((Complex.continuous_ofReal.comp (hc.comp continuous_fst)).mul
        ((Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
          (continuous_const.mul (continuous_fst.inner continuous_snd))).mul continuous_const)).mul
          (Complex.continuous_ofReal.comp (hu_cont.comp continuous_snd))))
  have hprod_int : Integrable (Function.uncurry fun x z : Euc d =>
      Complex.exp (↑(-2 * π * ⟪x, y⟫) * I) * ((h x : ℂ) *
        (Complex.exp (↑(2 * π * ⟪x, z⟫) * I) * (u z : ℂ)))) (volume.prod volume) := by
    refine (hi.abs.smul_prod hu_int).mono' hcont_prod.aestronglyMeasurable
      (Eventually.of_forall fun ⟨x, z⟩ => ?_)
    dsimp only [Function.uncurry, smul_eq_mul]
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
      Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_of_nonneg (hu_pos z).le]
  have hg_ft : 𝓕 (fun x : Euc d => ((h x * Real.exp (-π * η * ‖x‖ ^ 2) : ℝ) : ℂ)) y =
      ∫ z : Euc d, (u z : ℂ) * 𝓕 (fun x : Euc d => (h x : ℂ)) (y - z) := by
    rw [Real.fourier_eq']
    calc ∫ x : Euc d, Complex.exp (↑(-2 * π * ⟪x, y⟫) * I) •
            ((h x * Real.exp (-π * η * ‖x‖ ^ 2) : ℝ) : ℂ)
        = ∫ x : Euc d, ∫ z : Euc d, Complex.exp (↑(-2 * π * ⟪x, y⟫) * I) * ((h x : ℂ) *
            (Complex.exp (↑(2 * π * ⟪x, z⟫) * I) * (u z : ℂ))) := by
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          simp only [Complex.ofReal_mul, smul_eq_mul, hexp_rep x, ← integral_const_mul]
      _ = ∫ z : Euc d, ∫ x : Euc d, Complex.exp (↑(-2 * π * ⟪x, y⟫) * I) * ((h x : ℂ) *
            (Complex.exp (↑(2 * π * ⟪x, z⟫) * I) * (u z : ℂ))) :=
          integral_integral_swap hprod_int
      _ = ∫ z : Euc d, (u z : ℂ) * 𝓕 (fun x : Euc d => (h x : ℂ)) (y - z) := by
          refine integral_congr_ae (Eventually.of_forall fun z => ?_)
          dsimp only; rw [Real.fourier_eq', ← integral_const_mul]
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          have hexp_eq : Complex.exp (↑(-2 * π * ⟪x, y⟫) * I) *
              Complex.exp (↑(2 * π * ⟪x, z⟫) * I) =
              Complex.exp (↑(-2 * π * ⟪x, y - z⟫) * I) := by
            rw [← Complex.exp_add]; congr 1
            rw [inner_sub_right]; push_cast; ring
          calc Complex.exp (↑(-2 * π * ⟪x, y⟫) * I) * ((h x : ℂ) *
                (Complex.exp (↑(2 * π * ⟪x, z⟫) * I) * (u z : ℂ)))
              = (u z : ℂ) * ((Complex.exp (↑(-2 * π * ⟪x, y⟫) * I) *
                  Complex.exp (↑(2 * π * ⟪x, z⟫) * I)) * (h x : ℂ)) := by ring
            _ = (u z : ℂ) * (Complex.exp (↑(-2 * π * ⟪x, y - z⟫) * I) * (h x : ℂ)) := by
                rw [hexp_eq]
            _ = (u z : ℂ) * (Complex.exp (↑(-2 * π * ⟪x, y - z⟫) * I) • (h x : ℂ)) := rfl
  have hint_z : Integrable (fun z : Euc d =>
      (u z : ℂ) * 𝓕 (fun x : Euc d => (h x : ℂ)) (y - z)) := by
    refine (hu_int.const_mul (∫ x : Euc d, |h x|)).mono' ?_ (Eventually.of_forall fun z => ?_)
    · exact ((Complex.continuous_ofReal.comp hu_cont).aestronglyMeasurable).mul
        ((hft_cont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
    · have hre_le : ‖𝓕 (fun x : Euc d => (h x : ℂ)) (y - z)‖ ≤ ∫ x : Euc d, |h x| := by
        refine (Real.norm_fourier_le_integral_norm _ _).trans_eq ?_
        simp_rw [Complex.norm_real, Real.norm_eq_abs]
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hu_pos z).le, mul_comm]
      exact mul_le_mul_of_nonneg_right hre_le (hu_pos z).le
  have h_real_z : (fun z : Euc d => (u z : ℂ) * 𝓕 (fun x : Euc d => (h x : ℂ)) (y - z)) =
      fun z => ((u z * (𝓕 (fun x : Euc d => (h x : ℂ)) (y - z)).re : ℝ) : ℂ) := by
    ext z; obtain ⟨him, _⟩ := hfnn (y - z)
    conv_lhs => rw [show 𝓕 (fun x : Euc d => (h x : ℂ)) (y - z) =
      ((𝓕 (fun x : Euc d => (h x : ℂ)) (y - z)).re : ℂ) from Complex.ext rfl him]
    rw [← Complex.ofReal_mul]
  rw [hg_ft, h_real_z]
  have him0 : (∫ z : Euc d, ((u z * (𝓕 (fun x : Euc d => (h x : ℂ)) (y - z)).re : ℝ) : ℂ)).im = 0 := by
    rw [← Complex.imCLM_apply, ← Complex.imCLM.integral_comp_comm (h_real_z ▸ hint_z)]; simp
  have hre_nn : 0 ≤ (∫ z : Euc d, ((u z * (𝓕 (fun x : Euc d => (h x : ℂ)) (y - z)).re : ℝ) : ℂ)).re := by
    rw [← Complex.reCLM_apply, ← Complex.reCLM.integral_comp_comm (h_real_z ▸ hint_z)]
    exact integral_nonneg fun z => mul_nonneg (hu_pos z).le (hfnn (y - z)).2
  exact ⟨him0, hre_nn⟩

/-- Gaussian damping + `ContDiffBump` mollification + origin rescaling approximates any
`IsContinuousL1CEAdmissible d r h` (`d ≥ 1`) by an `IsSchwartzCEAdmissible` function at radius
arbitrarily close to `r`. -/
theorem ce_mollify_approx {d : ℕ} (hd : 1 ≤ d) {r : ℝ} {h : Euc d → ℝ}
    (hadm : IsContinuousL1CEAdmissible d r h) {ε : ℝ} (hε : 0 < ε) :
    ∃ r' h', IsSchwartzCEAdmissible d r' h' ∧ r' < r + ε := by
  have hM : ∀ x : Euc d, |h x| ≤ h 0 := (hadm.abs_le_origin_and_vol_ge hd).1
  have hC_int : Integrable (fun x : Euc d => (h x : ℂ)) := Complex.ofRealCLM.integrable_comp hadm.integrable
  have hft_cont : Continuous (𝓕 (fun x : Euc d => (h x : ℂ))) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hC_int
  let g_fn : ℝ → Euc d → ℝ := fun η x => h x * Real.exp (-π * η * ‖x‖ ^ 2)
  let φ_bump : ℝ → ContDiffBump (0 : Euc d) := fun η =>
    if hη : 0 < η then ⟨η / 2, η, half_pos hη, half_lt_self hη⟩ else ⟨1, 2, zero_lt_one, one_lt_two⟩
  let φ_fn : ℝ → Euc d → ℝ := fun η => (φ_bump η).normed volume
  let ψ_fn : ℝ → Euc d → ℝ := fun η => φ_fn η ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] φ_fn η
  let h_fn : ℝ → Euc d → ℝ := fun η => g_fn η ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] ψ_fn η
  have hφ_neg : ∀ η x, φ_fn η (-x) = φ_fn η x := fun η x => (φ_bump η).normed_neg x
  have hφ_nonneg : ∀ η x, 0 ≤ φ_fn η x := fun η x => (φ_bump η).nonneg_normed x
  have hφ_int1 : ∀ η, ∫ x : Euc d, φ_fn η x = 1 := fun η => (φ_bump η).integral_normed
  have hφ_supp : ∀ η, HasCompactSupport (φ_fn η) := fun η => (φ_bump η).hasCompactSupport_normed
  have hφ_cd : ∀ η, ContDiff ℝ ∞ (φ_fn η) := fun η => (φ_bump η).contDiff_normed
  have hφ_int : ∀ η, Integrable (φ_fn η) := fun η => (φ_bump η).integrable_normed
  have hφ_ball : ∀ {η : ℝ}, 0 < η → ∀ x : Euc d, η ≤ ‖x‖ → φ_fn η x = 0 := by
    intro η hη x hx
    refine Function.notMem_support.mp ?_
    rw [ContDiffBump.support_normed_eq, show (φ_bump η).rOut = η by simp [φ_bump, hη],
      Metric.mem_ball, dist_zero_right, not_lt]
    exact hx
  have hψ_supp : ∀ η, HasCompactSupport (ψ_fn η) := fun η =>
    (hφ_supp η).convolution (ContinuousLinearMap.mul ℝ ℝ) (hφ_supp η)
  have hψ_cd : ∀ η, ContDiff ℝ ∞ (ψ_fn η) := fun η =>
    (hφ_supp η).contDiff_convolution_left (ContinuousLinearMap.mul ℝ ℝ) (hφ_cd η)
      (hφ_int η).locallyIntegrable
  have hψ_int : ∀ η, Integrable (ψ_fn η) := fun η =>
    (hψ_cd η).continuous.integrable_of_hasCompactSupport (hψ_supp η)
  have hψ_nonneg : ∀ η x, 0 ≤ ψ_fn η x := fun η x =>
    integral_nonneg fun t => mul_nonneg (hφ_nonneg η t) (hφ_nonneg η (x - t))
  have hψ_int1 : ∀ η, ∫ x : Euc d, ψ_fn η x = 1 := fun η => by
    dsimp [ψ_fn]; rw [integral_convolution (ContinuousLinearMap.mul ℝ ℝ) (hφ_int η) (hφ_int η)]
    simp [hφ_int1 η]
  have hψ_ball : ∀ {η : ℝ} (_ : 0 < η) (z : Euc d), 2 * η ≤ ‖z‖ → ψ_fn η z = 0 := by
    intro η hη z hz; dsimp [ψ_fn, convolution_def]
    refine integral_eq_zero_of_ae (Eventually.of_forall fun t => ?_)
    change φ_fn η t * φ_fn η (z - t) = 0
    by_cases ht : η ≤ ‖t‖
    · rw [hφ_ball hη t ht, zero_mul]
    · have hzt : η ≤ ‖z - t‖ := by
        have htri : ‖z‖ ≤ ‖t‖ + ‖z - t‖ := by simpa [sub_add_cancel] using norm_add_le t (z - t)
        linarith
      rw [hφ_ball hη (z - t) hzt, mul_zero]
  have hg_cont : ∀ η, Continuous (g_fn η) := fun η =>
    hadm.continuous.mul (Real.continuous_exp.comp (continuous_const.mul (continuous_norm.pow 2)))
  have hg_int : ∀ η, 0 < η → Integrable (g_fn η) := fun η hη => by
    have hcont_e : Continuous (fun x : Euc d => Real.exp (-π * η * ‖x‖ ^ 2)) :=
      Real.continuous_exp.comp (continuous_const.mul (continuous_norm.pow 2))
    refine hadm.integrable.abs.mono' (hadm.continuous.mul hcont_e).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    dsimp [g_fn]
    simp only [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (by nlinarith [Real.pi_pos]) (sq_nonneg _)))
  have hg_bd : ∀ η, ∀ x : Euc d, |g_fn η x| ≤ h 0 * Real.exp (-π * η * ‖x‖ ^ 2) := fun η x => by
    dsimp [g_fn]; rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right (hM x) (Real.exp_pos _).le
  have hh_schwartz : ∀ {η : ℝ}, 0 < η → ∃ S : 𝓢(Euc d, ℂ), ∀ x : Euc d, S x = (h_fn η x : ℂ) := by
    intro η hη
    let S_R : 𝓢(Euc d, ℝ) :=
      { toFun := h_fn η
        smooth' := (hψ_supp η).contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
          (hg_cont η).locallyIntegrable (hψ_cd η)
        decay' := fun k n =>
          convolution_gaussian_bound_decay (hg_cont η) hadm.origin_pos.le hη (hg_bd η) n ℝ ℝ
            (ContinuousLinearMap.mul ℝ ℝ) (ψ_fn η) (hψ_supp η) (hψ_cd η) k }
    exact ⟨S_R.postcompCLM Complex.ofRealCLM, fun x => rfl⟩
  have hC_conv_of_real : ∀ (f₁ f₂ : Euc d → ℝ), LocallyIntegrable f₁ volume →
      Continuous f₂ → HasCompactSupport f₂ → ∀ x : Euc d,
      ((f₁ ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] f₂) x : ℂ) =
        ((fun t : Euc d => (f₁ t : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
          (fun t : Euc d => (f₂ t : ℂ))) x := fun f₁ f₂ hf₁ hf₂c hf₂s x => by
    have hex := hf₂s.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ) hf₁ hf₂c x
    rw [convolution_def, convolution_def]
    change Complex.ofRealCLM (∫ t : Euc d, ContinuousLinearMap.mul ℝ ℝ (f₁ t) (f₂ (x - t))) =
      ∫ t : Euc d, (f₁ t : ℂ) * (f₂ (x - t) : ℂ)
    rw [← Complex.ofRealCLM.integral_comp_comm hex.integrable]
    congr 1; ext t; simp
  have hh_ft_eq : ∀ {η : ℝ} (hη : 0 < η) (y : Euc d),
      𝓕 (fun x : Euc d => (h_fn η x : ℂ)) y =
        𝓕 (fun x : Euc d => (g_fn η x : ℂ)) y * (𝓕 (fun x : Euc d => (φ_fn η x : ℂ)) y) ^ 2 := by
    intro η hη y
    have hgC : Integrable (fun t : Euc d => (g_fn η t : ℂ)) :=
      Complex.ofRealCLM.integrable_comp (hg_int η hη)
    have hψC : Integrable (fun t : Euc d => (ψ_fn η t : ℂ)) :=
      Complex.ofRealCLM.integrable_comp (hψ_int η)
    have hφC : Integrable (fun t : Euc d => (φ_fn η t : ℂ)) :=
      Complex.ofRealCLM.integrable_comp (hφ_int η)
    rw [show (fun x : Euc d => (h_fn η x : ℂ)) =
        (fun t => (g_fn η t : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
          (fun t => (ψ_fn η t : ℂ)) from
        funext (hC_conv_of_real (g_fn η) (ψ_fn η) (hg_cont η).locallyIntegrable
          (hψ_cd η).continuous (hψ_supp η)),
      Real.fourier_mul_convolution_eq hgC hψC y,
      show (fun x : Euc d => (ψ_fn η x : ℂ)) =
        (fun t => (φ_fn η t : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
          (fun t => (φ_fn η t : ℂ)) from
        funext (hC_conv_of_real (φ_fn η) (φ_fn η) (hφ_int η).locallyIntegrable
          (hφ_cd η).continuous (hφ_supp η)),
      Real.fourier_mul_convolution_eq hφC hφC y, sq]
  have hh_ft_nonneg : ∀ {η : ℝ}, 0 < η → ∀ y : Euc d,
      (𝓕 (fun x : Euc d => (h_fn η x : ℂ)) y).im = 0 ∧
        0 ≤ (𝓕 (fun x : Euc d => (h_fn η x : ℂ)) y).re := by
    intro η hη y
    have hφ_real : (𝓕 (fun x : Euc d => (φ_fn η x : ℂ)) y).im = 0 := by
      have hconj : star (𝓕 (fun x : Euc d => (φ_fn η x : ℂ)) y) =
          𝓕 (fun x : Euc d => (φ_fn η x : ℂ)) y := by
        rw [← fourier_comp_neg (hφ_int η) y]; simp_rw [hφ_neg η]
      have him := congrArg Complex.im hconj
      simp only [Complex.star_def, Complex.conj_im] at him; linarith
    have hg_nn := fourier_mul_gaussian_nonneg hadm.continuous hadm.integrable hft_cont
      hadm.fourier_nonneg hη y
    rw [hh_ft_eq hη y]
    set zg := 𝓕 (fun x : Euc d => (g_fn η x : ℂ)) y
    set zφ := 𝓕 (fun x : Euc d => (φ_fn η x : ℂ)) y
    rw [show zg = ((zg.re : ℝ) : ℂ) from Complex.ext rfl hg_nn.1,
      show zφ = ((zφ.re : ℝ) : ℂ) from Complex.ext rfl hφ_real]
    simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_im, Complex.ofReal_re]
    exact ⟨trivial, mul_nonneg hg_nn.2 (sq_nonneg _)⟩
  have hh_nonpos : ∀ {η : ℝ}, 0 < η → ∀ x : Euc d, r + 2 * η ≤ ‖x‖ → h_fn η x ≤ 0 := by
    intro η hη x hx; dsimp [h_fn]; rw [convolution_def]
    refine integral_nonpos fun y => ?_
    change g_fn η y * ψ_fn η (x - y) ≤ 0
    by_cases hxy : 2 * η ≤ ‖x - y‖
    · rw [hψ_ball hη (x - y) hxy, mul_zero]
    · rw [not_le] at hxy
      have hy : r ≤ ‖y‖ := by
        have htri : ‖x‖ ≤ ‖y‖ + ‖x - y‖ := by simpa [add_sub_cancel] using norm_add_le y (x - y)
        linarith
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (hadm.nonpos_outside y hy) (Real.exp_pos _).le)
        (hψ_nonneg η (x - y))
  let ηseq : ℕ → ℝ := fun n => (1 : ℝ) / ((n : ℝ) + 1)
  have hη_pos : ∀ n, 0 < ηseq n := fun n => by dsimp [ηseq]; positivity
  have hη_tend : Tendsto ηseq atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hh0_tend : Tendsto (fun n => h_fn (ηseq n) 0) atTop (𝓝 (h 0)) := by
    rw [Metric.tendsto_nhds]; intro δ hδ
    obtain ⟨ρ, hρ_pos, hρ⟩ := Metric.continuousAt_iff.mp hadm.continuous.continuousAt (δ / 4) (by linarith)
    have hη_small : ∀ᶠ n in atTop, 2 * ηseq n < ρ ∧ h 0 * (π * ηseq n * (2 * ηseq n) ^ 2) < δ / 4 := by
      have h1 : Tendsto (fun n => 2 * ηseq n) atTop (𝓝 0) := by simpa using hη_tend.const_mul 2
      have h2 : Tendsto (fun n => h 0 * (π * ηseq n * (2 * ηseq n) ^ 2)) atTop (𝓝 0) := by
        simpa [mul_assoc] using ((hη_tend.mul ((hη_tend.const_mul 2).pow 2)).const_mul π).const_mul (h 0)
      exact (h1.eventually (gt_mem_nhds hρ_pos)).and (h2.eventually (gt_mem_nhds (by linarith)))
    filter_upwards [hη_small] with n ⟨hηρ, hη_exp⟩
    have hi1 : Integrable (fun y : Euc d => g_fn (ηseq n) (-y) * ψ_fn (ηseq n) y) := by
      refine ((hψ_int (ηseq n)).const_mul (h 0)).mono'
        (((hg_cont (ηseq n)).comp continuous_neg).mul (hψ_cd (ηseq n)).continuous).aestronglyMeasurable
        (Eventually.of_forall fun y => ?_)
      simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hψ_nonneg (ηseq n) y)]
      have hgle : |g_fn (ηseq n) (-y)| ≤ h 0 := (hg_bd (ηseq n) (-y)).trans
        (mul_le_of_le_one_right hadm.origin_pos.le (Real.exp_le_one_iff.mpr
          (mul_nonpos_of_nonpos_of_nonneg (by nlinarith [Real.pi_pos, hη_pos n]) (sq_nonneg _))))
      exact mul_le_mul_of_nonneg_right hgle (hψ_nonneg (ηseq n) y)
    have hdiff : h_fn (ηseq n) 0 - h 0 =
        ∫ y : Euc d, (g_fn (ηseq n) (-y) - h 0) * ψ_fn (ηseq n) y := by
      have h0_eq : h_fn (ηseq n) 0 = ∫ y : Euc d, g_fn (ηseq n) (-y) * ψ_fn (ηseq n) y := by
        dsimp [h_fn]; rw [← convolution_flip, convolution_def]
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp [ContinuousLinearMap.mul_apply', mul_comm]
      rw [h0_eq]
      calc (∫ y : Euc d, g_fn (ηseq n) (-y) * ψ_fn (ηseq n) y) - h 0
          = (∫ y : Euc d, g_fn (ηseq n) (-y) * ψ_fn (ηseq n) y) -
              (∫ y : Euc d, h 0 * ψ_fn (ηseq n) y) := by
              rw [integral_const_mul, hψ_int1, mul_one]
        _ = (∫ y : Euc d, g_fn (ηseq n) (-y) * ψ_fn (ηseq n) y - h 0 * ψ_fn (ηseq n) y) := by
              rw [integral_sub hi1 ((hψ_int (ηseq n)).const_mul _)]
        _ = ∫ y : Euc d, (g_fn (ηseq n) (-y) - h 0) * ψ_fn (ηseq n) y := by
              refine integral_congr_ae (Eventually.of_forall fun y => by ring)
    have hpt_bd : ∀ y : Euc d,
        ‖(g_fn (ηseq n) (-y) - h 0) * ψ_fn (ηseq n) y‖ ≤ (δ / 2) * ψ_fn (ηseq n) y := fun y => by
      by_cases hy : 2 * ηseq n ≤ ‖y‖
      · rw [hψ_ball (hη_pos n) y hy, mul_zero, norm_zero, mul_zero]
      · rw [not_le] at hy
        have h1 : |h (-y) - h 0| < δ / 4 := by
          simpa [Real.dist_eq] using hρ (by simpa [dist_zero_right, norm_neg] using hy.trans hηρ)
        have h2 : |g_fn (ηseq n) (-y) - h (-y)| ≤ h 0 * (π * ηseq n * (2 * ηseq n) ^ 2) := by
          dsimp [g_fn]
          rw [show h (-y) * Real.exp (-π * ηseq n * ‖-y‖ ^ 2) - h (-y) =
              -(h (-y) * (1 - Real.exp (-π * ηseq n * ‖y‖ ^ 2))) by simp [norm_neg]; ring,
            abs_neg, abs_mul]
          have hexp_nn : 0 ≤ 1 - Real.exp (-π * ηseq n * ‖y‖ ^ 2) := by
            rw [sub_nonneg, Real.exp_le_one_iff]
            exact mul_nonpos_of_nonpos_of_nonneg (by nlinarith [Real.pi_pos, hη_pos n]) (sq_nonneg _)
          have hexp_le : 1 - Real.exp (-π * ηseq n * ‖y‖ ^ 2) ≤ π * ηseq n * (2 * ηseq n) ^ 2 := by
            have hadd := Real.add_one_le_exp (-(π * ηseq n * ‖y‖ ^ 2))
            rw [show -π * ηseq n * ‖y‖ ^ 2 = -(π * ηseq n * ‖y‖ ^ 2) by ring]
            have hsq : ‖y‖ ^ 2 ≤ (2 * ηseq n) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hy.le 2
            have hmul : π * ηseq n * ‖y‖ ^ 2 ≤ π * ηseq n * (2 * ηseq n) ^ 2 :=
              mul_le_mul_of_nonneg_left hsq (by positivity)
            linarith [hadd, hmul]
          rw [abs_of_nonneg hexp_nn]
          exact mul_le_mul (hM (-y)) hexp_le hexp_nn hadm.origin_pos.le
        have h3 : |g_fn (ηseq n) (-y) - h 0| ≤ δ / 2 :=
          (abs_sub_le (g_fn (ηseq n) (-y)) (h (-y)) (h 0)).trans (by linarith)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hψ_nonneg (ηseq n) y)]
        exact mul_le_mul_of_nonneg_right h3 (hψ_nonneg (ηseq n) y)
    rw [Real.dist_eq, hdiff]
    have hnorm_le : |∫ y : Euc d, (g_fn (ηseq n) (-y) - h 0) * ψ_fn (ηseq n) y| ≤
        ∫ y : Euc d, (δ / 2) * ψ_fn (ηseq n) y :=
      (norm_integral_le_integral_norm _).trans (integral_mono
        (((hi1.sub ((hψ_int (ηseq n)).const_mul (h 0))).congr
          (Eventually.of_forall fun y => by simp only [Pi.sub_apply]; ring)).norm)
        ((hψ_int (ηseq n)).const_mul (δ / 2)) hpt_bd)
    rw [integral_const_mul, hψ_int1, mul_one] at hnorm_le; linarith
  have hft0_tend : Tendsto (fun n => (𝓕 (fun x : Euc d => (h_fn (ηseq n) x : ℂ)) 0).re)
      atTop (𝓝 (h 0)) := by
    have hft0_eq : ∀ n, (𝓕 (fun x : Euc d => (h_fn (ηseq n) x : ℂ)) 0).re =
        ∫ x : Euc d, g_fn (ηseq n) x := fun n => by
      rw [hh_ft_eq (hη_pos n) 0, fourier_zero_eq (hφ_int (ηseq n)), hφ_int1,
        fourier_zero_eq (hg_int (ηseq n) (hη_pos n))]
      simp
    simp_rw [hft0_eq]; rw [hadm.origin_eq, fourier_zero_re_eq hadm.integrable]
    refine tendsto_integral_filter_of_dominated_convergence (fun x => |h x|)
      (Eventually.of_forall fun n => (hg_cont (ηseq n)).aestronglyMeasurable)
      (Eventually.of_forall fun n => Eventually.of_forall fun x => ?_)
      hadm.integrable.abs (Eventually.of_forall fun x => ?_)
    · dsimp [g_fn]; simp only [abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (by nlinarith [Real.pi_pos, hη_pos n]) (sq_nonneg _)))
    · have hexp : Tendsto (fun n => Real.exp (-π * ηseq n * ‖x‖ ^ 2)) atTop (𝓝 (Real.exp 0)) :=
        Real.continuous_exp.continuousAt.tendsto.comp
          (by simpa using ((hη_tend.const_mul (-π)).mul_const (‖x‖ ^ 2)))
      rw [Real.exp_zero] at hexp; simpa [g_fn] using tendsto_const_nhds.mul hexp
  have hpos_ev : ∀ᶠ n in atTop,
      0 < h_fn (ηseq n) 0 ∧ 0 < (𝓕 (fun x : Euc d => (h_fn (ηseq n) x : ℂ)) 0).re :=
    (hh0_tend.eventually (lt_mem_nhds hadm.origin_pos)).and
      (hft0_tend.eventually (lt_mem_nhds hadm.origin_pos))
  let μseq : ℕ → ℝ := fun n =>
    ((𝓕 (fun x : Euc d => (h_fn (ηseq n) x : ℂ)) 0).re / h_fn (ηseq n) 0) ^ (1 / (d : ℝ))
  have hμ_tend : Tendsto μseq atTop (𝓝 1) := by
    have hdiv := hft0_tend.div hh0_tend hadm.origin_pos.ne'
    rw [div_self hadm.origin_pos.ne'] at hdiv
    simpa [μseq, Function.comp_def, Pi.div_apply] using
      (Real.continuousAt_rpow_const 1 (1 / (d : ℝ)) (Or.inl one_ne_zero)).tendsto.comp hdiv
  have hrad_tend : Tendsto (fun n => (r + 2 * ηseq n) / μseq n) atTop (𝓝 r) := by
    have hrad : Tendsto ((fun x => r + 2 * ηseq x) / μseq) atTop (𝓝 r) := by
      simpa only [mul_zero, add_zero, div_one] using
        ((tendsto_const_nhds (x := r)).add (hη_tend.const_mul 2)).div hμ_tend one_ne_zero
    exact hrad.congr (fun _ => rfl)
  obtain ⟨n, ⟨hn_h0, hn_ft0⟩, hn_rad⟩ :=
    (hpos_ev.and (hrad_tend.eventually (gt_mem_nhds (by linarith : r < r + ε)))).exists
  have hadm_n : IsCohnElkiesAdmissible d (r + 2 * ηseq n) (h_fn (ηseq n)) :=
    ⟨by linarith [hadm.r_pos, hη_pos n],
      ((hψ_supp (ηseq n)).contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
        ((hg_cont (ηseq n)).locallyIntegrable : LocallyIntegrable (g_fn (ηseq n)) volume)
        (hψ_cd (ηseq n))).continuous,
      (hg_int (ηseq n) (hη_pos n)).integrable_convolution (ContinuousLinearMap.mul ℝ ℝ)
        (hψ_int (ηseq n)),
      by obtain ⟨S, hS⟩ := hh_schwartz (hη_pos n)
         simpa [funext fun x => (hS x).symm] using (𝓕 S).integrable,
      hn_h0, hn_ft0, hh_nonpos (hη_pos n), hh_ft_nonneg (hη_pos n)⟩
  obtain ⟨_, _, hsw⟩ := hadm_n.rescale_to_normalized hd
  exact ⟨(r + 2 * ηseq n) / μseq n, fun x => h_fn (ηseq n) (μseq n • x),
    hsw (hh_schwartz (hη_pos n)), hn_rad⟩

/-- **Corollary `7.12` (`gt:7.12`), Schwartz vs continuous-`L¹` radius infimum equality:**
for every `d ≥ 1`, `optimalSchwartzCERadius d = optimalL1CERadius d`. -/
theorem ce_schwartz_radius_eq_L1_radius {d : ℕ} (hd : 1 ≤ d) :
    optimalSchwartzCERadius d = optimalL1CERadius d := by
  obtain ⟨r₀, h₀, hsw₀⟩ := (schwartzCE_nonempty_and_lower_bound hd).1
  have hL_bdd : BddBelow { r : ℝ | ∃ h, IsContinuousL1CEAdmissible d r h } :=
    ⟨0, fun _ ⟨_, hadm⟩ => hadm.r_pos.le⟩
  have hle : optimalL1CERadius d ≤ optimalSchwartzCERadius d :=
    csInf_le_csInf hL_bdd ⟨r₀, h₀, hsw₀⟩ fun r ⟨h, hsw⟩ => ⟨h, hsw.toIsContinuousL1CEAdmissible⟩
  have hge : optimalSchwartzCERadius d ≤ optimalL1CERadius d := by
    refine le_csInf ⟨r₀, h₀, hsw₀.toIsContinuousL1CEAdmissible⟩ fun r ⟨h, hadm⟩ => ?_
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨r', h', hsw', hr'⟩ := ce_mollify_approx hd hadm hε
    exact (csInf_le (s := { r : ℝ | ∃ h, IsSchwartzCEAdmissible d r h })
      ⟨0, fun _ ⟨_, hsw⟩ => hsw.r_pos.le⟩ ⟨h', hsw'⟩).trans hr'.le
  exact le_antisymm hge hle

/-- Positivity of optimal radii and Minkowski lower bound `2 ^ (-d) ≤ optimalCohnElkiesBound d`. -/
theorem optimalCERadius_pos_and_bound_ge {d : ℕ} (hd : 1 ≤ d) :
    0 < optimalSchwartzCERadius d ∧ 0 < optimalL1CERadius d ∧
      (2 : ℝ) ^ (-(d : ℝ)) ≤ optimalCohnElkiesBound d := by
  obtain ⟨⟨r₀, h₀, hsw₀⟩, r_min, hr_min_pos, hr_min⟩ := schwartzCE_nonempty_and_lower_bound hd
  have hL_pos : 0 < optimalL1CERadius d :=
    hr_min_pos.trans_le (le_csInf ⟨r₀, h₀, hsw₀.toIsContinuousL1CEAdmissible⟩ fun r ⟨h, hadm⟩ =>
      hr_min r h hadm)
  have hS_pos : 0 < optimalSchwartzCERadius d := by rwa [ce_schwartz_radius_eq_L1_radius hd]
  have hB_ge : (2 : ℝ) ^ (-(d : ℝ)) ≤ optimalCohnElkiesBound d := by
    refine le_csInf ⟨cohnElkiesBound d r₀ h₀, r₀, h₀, hsw₀.toIsCohnElkiesAdmissible, rfl⟩
      fun V ⟨r, h, hadm, hV⟩ => ?_
    subst hV
    obtain ⟨hadm', hvol, _⟩ := hadm.rescale_to_normalized hd
    have h1 := (hadm'.abs_le_origin_and_vol_ge hd).2.2
    have hbound' : cohnElkiesBound d (r / ((𝓕 (fun x : Euc d => (h x : ℂ)) 0).re / h 0) ^ (1 / (d : ℝ)))
        (fun x => h (((𝓕 (fun x : Euc d => (h x : ℂ)) 0).re / h 0) ^ (1 / (d : ℝ)) • x)) =
        (volume : Measure (Euc d)).real (Metric.ball 0
          ((r / ((𝓕 (fun x : Euc d => (h x : ℂ)) 0).re / h 0) ^ (1 / (d : ℝ))) / 2)) := by
      unfold cohnElkiesBound; rw [← hadm'.origin_eq, div_self hadm'.origin_pos.ne', one_mul]
    rw [hbound', hvol] at h1; exact h1
  exact ⟨hS_pos, hL_pos, hB_ge⟩

/-- Identification `optimalSchwartzCEBound d = optimalCohnElkiesBound d = vol(B_{r_CE(d) / 2})`. -/
theorem ce_schwartz_bound_eq_optimalCohnElkiesBound {d : ℕ} (hd : 1 ≤ d) :
    optimalSchwartzCEBound d = optimalCohnElkiesBound d ∧
      optimalCohnElkiesBound d =
        (volume : Measure (Euc d)).real (Metric.ball 0 (optimalSchwartzCERadius d / 2)) := by
  obtain ⟨r₀, h₀, hsw₀⟩ := (schwartzCE_nonempty_and_lower_bound hd).1
  have hS_ne : { r : ℝ | ∃ h, IsSchwartzCEAdmissible d r h }.Nonempty := ⟨r₀, h₀, hsw₀⟩
  have hB_ne : { V : ℝ | ∃ r h, IsCohnElkiesAdmissible d r h ∧ V = cohnElkiesBound d r h }.Nonempty :=
    ⟨cohnElkiesBound d r₀ h₀, r₀, h₀, hsw₀.toIsCohnElkiesAdmissible, rfl⟩
  have hB_bdd : BddBelow { V : ℝ | ∃ r h, IsCohnElkiesAdmissible d r h ∧ V = cohnElkiesBound d r h } :=
    ⟨0, fun V ⟨r, h, hadm, hV⟩ => hV ▸ mul_nonneg
      (div_nonneg hadm.origin_pos.le hadm.fourier_origin_pos.le) ENNReal.toReal_nonneg⟩
  have hSB_bdd : BddBelow { V : ℝ | ∃ r h, IsSchwartzCEAdmissible d r h ∧ V = cohnElkiesBound d r h } :=
    ⟨0, fun V ⟨r, h, hsw, hV⟩ => hV ▸ mul_nonneg
      (div_nonneg hsw.origin_pos.le hsw.fourier_origin_pos.le) ENNReal.toReal_nonneg⟩
  have hr_pos := (optimalCERadius_pos_and_bound_ge hd).1
  let R : ℝ := optimalSchwartzCERadius d
  let V_opt : ℝ := (volume : Measure (Euc d)).real (Metric.ball 0 (R / 2))
  let f : ℝ → ℝ := fun ρ => (π * ρ ^ 2 / 4) ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2 + 1)
  have hf_eq : ∀ {ρ : ℝ}, 0 ≤ ρ → (volume : Measure (Euc d)).real (Metric.ball 0 (ρ / 2)) = f ρ :=
    fun hρ => volume_half_ball_eq hd hρ
  have hf_cont : ContinuousAt f R := by
    have hR_pos : 0 < R := hr_pos
    exact ((continuousAt_const.mul (continuousAt_id.pow 2) |>.div_const 4).rpow_const
      (Or.inl (div_ne_zero (mul_ne_zero Real.pi_ne_zero (pow_ne_zero 2 hR_pos.ne'))
        (by norm_num)))).div_const _
  have h1 : optimalCohnElkiesBound d ≤ optimalSchwartzCEBound d :=
    csInf_le_csInf hB_bdd ⟨cohnElkiesBound d r₀ h₀, r₀, h₀, hsw₀, rfl⟩
      fun V ⟨r, h, hsw, hV⟩ => ⟨r, h, hsw.toIsCohnElkiesAdmissible, hV⟩
  have h2 : optimalSchwartzCEBound d ≤ V_opt := by
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    obtain ⟨ε, hε_pos, hε⟩ := Metric.continuousAt_iff.mp hf_cont δ hδ
    obtain ⟨r, ⟨h, hsw⟩, hr_lt⟩ := exists_lt_of_csInf_lt hS_ne (by linarith : R < R + ε)
    have hr_ge : R ≤ r := csInf_le ⟨0, fun _ ⟨_, h'⟩ => h'.r_pos.le⟩ ⟨h, hsw⟩
    have hfr_lt : f r < f R + δ := by
      have := hε (by rw [Real.dist_eq, abs_of_nonneg (by linarith)]; linarith)
      rw [Real.dist_eq, abs_lt] at this; linarith
    have hbound_eq : cohnElkiesBound d r h = f r := by
      unfold cohnElkiesBound
      rw [← hsw.origin_eq, div_self hsw.origin_pos.ne', one_mul, hf_eq hsw.r_pos.le]
    have hV_le : optimalSchwartzCEBound d ≤ cohnElkiesBound d r h :=
      csInf_le hSB_bdd ⟨r, h, hsw, rfl⟩
    dsimp [V_opt]; rw [hf_eq hr_pos.le]; linarith
  have h3 : V_opt ≤ optimalCohnElkiesBound d := by
    refine le_csInf hB_ne fun V ⟨r, h, hadm, hV⟩ => ?_
    subst hV
    obtain ⟨hadm', hvol, _⟩ := hadm.rescale_to_normalized hd
    let r' := r / ((𝓕 (fun x : Euc d => (h x : ℂ)) 0).re / h 0) ^ (1 / (d : ℝ))
    have hr'_le : R ≤ r' := by
      rw [show R = optimalL1CERadius d from ce_schwartz_radius_eq_L1_radius hd]
      exact csInf_le ⟨0, fun _ ⟨_, h'⟩ => h'.r_pos.le⟩ ⟨_, hadm'⟩
    have hf_mono : f R ≤ f r' := by
      dsimp [f]
      refine div_le_div_of_nonneg_right
        (Real.rpow_le_rpow (by positivity) (by gcongr) (by positivity))
        (Real.Gamma_pos_of_pos (by positivity)).le
    rw [← hvol, hf_eq hadm'.r_pos.le]
    calc V_opt = f R := hf_eq hr_pos.le
      _ ≤ f r' := hf_mono
  exact ⟨le_antisymm (h2.trans h3) h1, le_antisymm (h1.trans h2) h3⟩

/-- Upper bound `optimalSchwartzCERadius d ≤ quadR d` for `d ≥ 2`. -/
theorem optimalSchwartzCERadius_le_quadR {d : ℕ} (hd : 2 ≤ d) :
    optimalSchwartzCERadius d ≤ quadR d := by
  have hB_le := optimalCohnElkiesBound_le_quadD hd
  rw [(ce_schwartz_bound_eq_optimalCohnElkiesBound (by omega)).2, ← quadH_bound_eq_quadD hd,
    show cohnElkiesBound d (quadR d) (quadH d) =
      (volume : Measure (Euc d)).real (Metric.ball 0 (quadR d / 2)) by
      unfold cohnElkiesBound; rw [(quadH_origin hd).1, (quadH_origin hd).2, Complex.one_re, div_one, one_mul],
    volume_half_ball_eq (by omega) (optimalCERadius_pos_and_bound_ge (by omega)).1.le,
    volume_half_ball_eq (by omega) (quadR_pos hd).le] at hB_le
  have hG := Real.Gamma_pos_of_pos (by positivity : (0 : ℝ) < (d : ℝ) / 2 + 1)
  have hpow : (π * optimalSchwartzCERadius d ^ 2 / 4) ^ ((d : ℝ) / 2) ≤
      (π * quadR d ^ 2 / 4) ^ ((d : ℝ) / 2) := (div_le_div_iff_of_pos_right hG).mp hB_le
  have hrpow := Real.rpow_le_rpow (by positivity) hpow (by positivity : (0 : ℝ) ≤ 2 / (d : ℝ))
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
  rw [← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity),
    show ((d : ℝ) / 2) * (2 / (d : ℝ)) = 1 by field_simp [hd_pos.ne'],
    Real.rpow_one, Real.rpow_one] at hrpow
  exact le_of_pow_le_pow_left₀ two_ne_zero (quadR_pos hd).le (by nlinarith [Real.pi_pos])

/-! ### Section 3: Airy-Order Gluing (`gt:7.12`) and Non-Vacuity Witnesses -/

/-- Abstract Airy-order gluing across all integer dimensions `d ≥ 2`. -/
theorem airy_order_gluing {R_opt R_L1 : ℕ → ℝ} {d₀ : ℕ} (hd₀ : 2 ≤ d₀) (A_opt C_lo C_hi : ℝ)
    (h_eq : ∀ d : ℕ, 2 ≤ d → R_opt d = R_L1 d)
    (h_lo : ∀ d : ℕ, d₀ ≤ d → (d : ℝ) / (2 * π ^ 2) + A_opt * ((d : ℝ) / 2) ^ (1 / 3 : ℝ) - C_lo ≤
      R_L1 d ^ 2 / 2)
    (h_hi : ∀ d : ℕ, d₀ ≤ d → R_L1 d ^ 2 / 2 ≤
      (d : ℝ) / (2 * π ^ 2) + A_opt * ((d : ℝ) / 2) ^ (1 / 3 : ℝ) + C_hi) :
    ∃ C : ℝ, ∀ d : ℕ, 2 ≤ d →
      |R_opt d ^ 2 / 2 - ((d : ℝ) / (2 * π ^ 2) + A_opt * ((d : ℝ) / 2) ^ (1 / 3 : ℝ))| ≤ C := by
  let M_fin : ℝ := (Finset.range d₀).sup' ⟨0, Finset.mem_range.mpr (by omega)⟩
    (fun d => if 2 ≤ d then
      |R_opt d ^ 2 / 2 - ((d : ℝ) / (2 * π ^ 2) + A_opt * ((d : ℝ) / 2) ^ (1 / 3 : ℝ))| else 0)
  refine ⟨max (max C_lo C_hi) M_fin, fun d hd => ?_⟩
  rcases lt_or_ge d d₀ with hlt | hge
  · have hle := Finset.le_sup' (fun j => if 2 ≤ j then
        |R_opt j ^ 2 / 2 - ((j : ℝ) / (2 * π ^ 2) + A_opt * ((j : ℝ) / 2) ^ (1 / 3 : ℝ))| else 0)
      (Finset.mem_range.mpr hlt)
    have hle' : |R_opt d ^ 2 / 2 - ((d : ℝ) / (2 * π ^ 2) + A_opt * ((d : ℝ) / 2) ^ (1 / 3 : ℝ))| ≤
        M_fin := by simpa [M_fin, hd] using hle
    exact hle'.trans (le_max_right _ _)
  · rw [h_eq d hd]
    have hC : |R_L1 d ^ 2 / 2 - ((d : ℝ) / (2 * π ^ 2) + A_opt * ((d : ℝ) / 2) ^ (1 / 3 : ℝ))| ≤
        max C_lo C_hi :=
      abs_le.mpr ⟨by linarith [h_lo d hge, le_max_left C_lo C_hi],
        by linarith [h_hi d hge, le_max_right C_lo C_hi]⟩
    exact hC.trans (le_max_left _ _)

/-- **Corollary `7.12` (`gt:7.12`) & Corollary `7.12a` (`gt:7.12a`):**
given any `d₀ ≥ 2`, `A_opt`, an asymptotic lower bound for `optimalL1CERadius d` (`d ≥ d₀`), and a
continuous-`L¹` upper witness (`d ≥ d₀`), yields for ALL `d ≥ 2` (even and odd):
1. `|r_CE(d)² / 2 - (d / (2π²) + A_opt (d/2)^{1/3})| ≤ C` (Schwartz and `L¹`);
2. multiplicative and logarithmic density expansions for `optimalCohnElkiesBound d`. -/
theorem ce_radius_airy_order_of_bounds {d₀ : ℕ} (hd₀ : 2 ≤ d₀) (A_opt C_lo C_hi : ℝ)
    (hlo : ∀ d : ℕ, d₀ ≤ d →
      (d : ℝ) / (2 * π ^ 2) + A_opt * ((d : ℝ) / 2) ^ (1 / 3 : ℝ) - C_lo ≤
        optimalL1CERadius d ^ 2 / 2)
    (hhi : ∀ d : ℕ, d₀ ≤ d → ∃ r h, IsContinuousL1CEAdmissible d r h ∧
      r ^ 2 / 2 ≤ (d : ℝ) / (2 * π ^ 2) + A_opt * ((d : ℝ) / 2) ^ (1 / 3 : ℝ) + C_hi) :
    (∃ C : ℝ, ∀ d : ℕ, 2 ≤ d →
      |optimalSchwartzCERadius d ^ 2 / 2 -
        ((d : ℝ) / (2 * π ^ 2) + A_opt * ((d : ℝ) / 2) ^ (1 / 3 : ℝ))| ≤ C) ∧
    (∃ C : ℝ, ∀ d : ℕ, 2 ≤ d →
      |optimalL1CERadius d ^ 2 / 2 -
        ((d : ℝ) / (2 * π ^ 2) + A_opt * ((d : ℝ) / 2) ^ (1 / 3 : ℝ))| ≤ C) ∧
    (∃ c₁ c₂ : ℝ, 0 < c₁ ∧ ∀ d : ℕ, 2 ≤ d →
      c₁ * ((π * (d : ℝ)) ^ (-(1 / 2 : ℝ)) * (Real.exp 1 / (2 * π)) ^ ((d : ℝ) / 2) *
          Real.exp (π ^ 2 * A_opt * ((d : ℝ) / 2) ^ (1 / 3 : ℝ))) ≤
        optimalCohnElkiesBound d ∧
      optimalCohnElkiesBound d ≤
        c₂ * ((π * (d : ℝ)) ^ (-(1 / 2 : ℝ)) * (Real.exp 1 / (2 * π)) ^ ((d : ℝ) / 2) *
          Real.exp (π ^ 2 * A_opt * ((d : ℝ) / 2) ^ (1 / 3 : ℝ)))) ∧
    (∃ C' : ℝ, ∀ d : ℕ, 2 ≤ d →
      |Real.log (optimalCohnElkiesBound d) -
        (((d : ℝ) / 2) * Real.log (Real.exp 1 / (2 * π)) +
          π ^ 2 * A_opt * ((d : ℝ) / 2) ^ (1 / 3 : ℝ) - (1 / 2 : ℝ) * Real.log (d : ℝ))| ≤ C') := by
  have _ : ∀ d : ℕ, 2 ≤ d → optimalSchwartzCERadius d ≤ quadR d := fun _ hd =>
    optimalSchwartzCERadius_le_quadR hd
  have h_hi_L1 : ∀ d : ℕ, d₀ ≤ d → optimalL1CERadius d ^ 2 / 2 ≤
      (d : ℝ) / (2 * π ^ 2) + A_opt * ((d : ℝ) / 2) ^ (1 / 3 : ℝ) + C_hi := by
    intro d hd; obtain ⟨r, h, hadm, hr_bd⟩ := hhi d hd
    have hL_pos := (optimalCERadius_pos_and_bound_ge (by omega : 1 ≤ d)).2.1
    have hL_le : optimalL1CERadius d ≤ r := csInf_le ⟨0, fun _ ⟨_, h'⟩ => h'.r_pos.le⟩ ⟨h, hadm⟩
    linarith [pow_le_pow_left₀ hL_pos.le hL_le 2]
  obtain ⟨C, hC⟩ := airy_order_gluing hd₀ A_opt C_lo C_hi
    (fun d hd => ce_schwartz_radius_eq_L1_radius (by omega : 1 ≤ d)) hlo h_hi_L1
  have hC_L1 : ∀ d : ℕ, 2 ≤ d →
      |optimalL1CERadius d ^ 2 / 2 -
        ((d : ℝ) / (2 * π ^ 2) + A_opt * ((d : ℝ) / 2) ^ (1 / 3 : ℝ))| ≤ C := fun d hd => by
    rw [← ce_schwartz_radius_eq_L1_radius (by omega : 1 ≤ d)]; exact hC d hd
  obtain ⟨⟨c₁, c₂, hc₁, hmult⟩, ⟨C', hlog⟩⟩ := ce_volume_expansion A_opt
    (fun d hd => (optimalCERadius_pos_and_bound_ge (by omega : 1 ≤ d)).1) ⟨C, hC⟩
  have hvol_eq : ∀ d : ℕ, 2 ≤ d →
      (volume : Measure (Euc d)).real (Metric.ball 0 (optimalSchwartzCERadius d / 2)) =
        optimalCohnElkiesBound d := fun d hd =>
    (ce_schwartz_bound_eq_optimalCohnElkiesBound (by omega : 1 ≤ d)).2.symm
  refine ⟨⟨C, hC⟩, ⟨C, hC_L1⟩, ⟨c₁, c₂, hc₁, fun d hd => ?_⟩, ⟨C', fun d hd => ?_⟩⟩
  · simpa only [hvol_eq d hd] using hmult d hd
  · simpa only [hvol_eq d hd] using hlog d hd

/-- Explicit non-vacuity check for `IsSchwartzCEAdmissible`, `ce_volume_expansion`, and
`ce_radius_airy_order_of_bounds`. -/
theorem ce_radius_nonvacuous :
    (∀ d : ℕ, 2 ≤ d → IsSchwartzCEAdmissible d (quadR d) (quadH d)) ∧
    (∃ (A_opt : ℝ) (r₁ r₂ : ℕ → ℝ),
      (∀ d : ℕ, 2 ≤ d → 0 < r₁ d) ∧ (∀ d : ℕ, 2 ≤ d → 0 ≤ r₂ d) ∧
      (∃ C₁, ∀ d : ℕ, 2 ≤ d → |r₁ d ^ 2 / 2 - ((d : ℝ) / (2 * π ^ 2) + A_opt * ((d : ℝ) / 2) ^ (1 / 3 : ℝ))| ≤ C₁) ∧
      (∃ C₂, ∀ d : ℕ, 2 ≤ d → |r₂ d ^ 2 / 2 - ((d : ℝ) / (2 * π ^ 2) + A_opt * ((d : ℝ) / 2) ^ (1 / 3 : ℝ))| ≤ C₂)) ∧
    (∃ (R_opt R_L1 : ℕ → ℝ) (d₀ : ℕ) (A_opt C_lo C_hi : ℝ), 2 ≤ d₀ ∧
      (∀ d : ℕ, 2 ≤ d → R_opt d = R_L1 d) ∧
      (∀ d : ℕ, d₀ ≤ d → (d : ℝ) / (2 * π ^ 2) + A_opt * ((d : ℝ) / 2) ^ (1 / 3 : ℝ) - C_lo ≤ R_L1 d ^ 2 / 2) ∧
      (∀ d : ℕ, d₀ ≤ d → R_L1 d ^ 2 / 2 ≤ (d : ℝ) / (2 * π ^ 2) + A_opt * ((d : ℝ) / 2) ^ (1 / 3 : ℝ) + C_hi)) := by
  refine ⟨fun d hd => ⟨⟨quadH_admissible hd, ?_⟩, (quadH_radial d).1⟩, ?_, ?_⟩
  · rw [(quadH_origin hd).1, (quadH_origin hd).2, Complex.one_re]
  · let r : ℕ → ℝ := fun d => Real.sqrt (2 * ((d : ℝ) / (2 * π ^ 2) + ((d : ℝ) / 2) ^ (1 / 3 : ℝ)))
    refine ⟨1, r, r, fun d hd => Real.sqrt_pos.mpr (by positivity),
      fun _ _ => Real.sqrt_nonneg _, ⟨0, fun d hd => ?_⟩, ⟨0, fun d hd => ?_⟩⟩ <;>
    · dsimp [r]; rw [Real.sq_sqrt (by positivity)]; simp
  · let r : ℕ → ℝ := fun d =>
      if d < 10 then quadR d else Real.sqrt (2 * ((d : ℝ) / (2 * π ^ 2) + ((d : ℝ) / 2) ^ (1 / 3 : ℝ)))
    refine ⟨r, r, 10, 1, 0, 0, by norm_num, fun _ _ => rfl, fun d hd => ?_, fun d hd => ?_⟩ <;>
    · dsimp [r]; simp only [show ¬ d < 10 by omega, ↓reduceIte]
      rw [Real.sq_sqrt (by positivity)]; linarith

/-! ### Axiom Verification -/

/-- info: 'FormalResearch.CohnElkies.log_gamma_half_add_one_asymptotic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms log_gamma_half_add_one_asymptotic

/-- info: 'FormalResearch.CohnElkies.ce_volume_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ce_volume_expansion

/-- info: 'FormalResearch.CohnElkies.ce_radii_diff_O_inv_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ce_radii_diff_O_inv_sqrt

/-- info: 'FormalResearch.CohnElkies.ce_radii_diff_nonneg_O_inv_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ce_radii_diff_nonneg_O_inv_sqrt

/-- info: 'FormalResearch.CohnElkies.IsContinuousL1CEAdmissible.ofRealPartNonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IsContinuousL1CEAdmissible.ofRealPartNonneg

/-- info: 'FormalResearch.CohnElkies.IsCohnElkiesAdmissible.rescale_to_normalized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IsCohnElkiesAdmissible.rescale_to_normalized

/-- info: 'FormalResearch.CohnElkies.ce_mollify_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ce_mollify_approx

/-- info: 'FormalResearch.CohnElkies.ce_schwartz_radius_eq_L1_radius' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ce_schwartz_radius_eq_L1_radius

/-- info: 'FormalResearch.CohnElkies.optimalCERadius_pos_and_bound_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms optimalCERadius_pos_and_bound_ge

/-- info: 'FormalResearch.CohnElkies.ce_schwartz_bound_eq_optimalCohnElkiesBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ce_schwartz_bound_eq_optimalCohnElkiesBound

/-- info: 'FormalResearch.CohnElkies.optimalSchwartzCERadius_le_quadR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms optimalSchwartzCERadius_le_quadR

/-- info: 'FormalResearch.CohnElkies.airy_order_gluing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airy_order_gluing

/-- info: 'FormalResearch.CohnElkies.ce_radius_airy_order_of_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ce_radius_airy_order_of_bounds

/-- info: 'FormalResearch.CohnElkies.ce_radius_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ce_radius_nonvacuous

end FormalResearch.CohnElkies
