module

public import FormalResearch.ModularBootstrap.ComplexBessel.BesselI0Sector
public import FormalResearch.ModularBootstrap.Bessel.ComplexExpansion

/-!
# Complex-Neighbourhood Cardy Expansion and Cauchy Derivative Bounds (`BesselComplexExpansion`)

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, Lemma B (`vlo:Bessel`), part (c),
second and third sentences.

Proves `Bessel.BesselComplexExpansion I` for every set `I : Set ℝ`:
for compact `I ⊂ (0, ∞)`, `V(c' b^2 / 3) = as(c' L(b)) [(1 - e^{-4πb})^2 + E_{c'}(b)]`
holds holomorphically and uniformly on a fixed complex `δ`-neighbourhood of `I` with
`‖E_{c'}(b)‖ ≤ C / c'`, and Cauchy's estimate gives `‖∂_b^n E_{c'}(x)‖ ≤ C_n / c'` on `I`.

## Main results
* `besselVC_eq_V_C`: `Bessel.besselVC (c' / 12) t = V_C (c' : ℂ) t` for all `c' : ℝ`, `t : ℂ`.
* `besselErrC_bound_on_box`: uniform `O(1/c')` bound on `{b : ℂ | m ≤ b.re ∧ |b.im| ≤ b.re ∧ ‖b‖ ≤ M}`.
* `besselComplexExpansion`: proof of `Bessel.BesselComplexExpansion I` for all `I : Set ℝ`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Nat

namespace FormalResearch.ModularBootstrap.ComplexBessel

/-! ### Section 1: Equivalence between `besselVC` and `V_C` -/

private lemma summable_regularizedHGFun_one (w : ℂ) :
    Summable fun k : ℕ => w ^ k / ((k ! : ℂ) ^ 2) := by
  refine Summable.of_norm_bounded (Real.summable_pow_div_factorial ‖w‖) fun k => ?_
  rw [norm_div, norm_pow, norm_pow, Complex.norm_natCast]
  have hk_ge1 : (1 : ℝ) ≤ (k ! : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hk_pos : (0 : ℝ) < (k ! : ℝ) := by positivity
  rw [div_le_div_iff₀ (sq_pos_of_pos hk_pos) hk_pos]
  exact mul_le_mul_of_nonneg_left (by nlinarith [hk_ge1, hk_pos]) (pow_nonneg (norm_nonneg w) k)

private lemma KalphaC_eq_tsum (α t : ℂ) :
    KalphaC α t = ∑' k : ℕ, (4 * (Real.pi : ℂ) ^ 2 * α) ^ k / ((k ! : ℂ) ^ 2) * t ^ k := by
  unfold KalphaC
  rw [FormalResearch.Special.regularizedHGFun_zero_singleton]
  congr 1
  ext k
  rw [add_comm (1 : ℂ) (k : ℂ), Complex.Gamma_nat_eq_factorial, mul_pow, mul_pow]
  ring

/-- `Bessel.besselVC (c' / 12) t` coincides with `V_C (c' : ℂ) t` for all `c' : ℝ`, `t : ℂ`. -/
theorem besselVC_eq_V_C (c' : ℝ) (t : ℂ) :
    Bessel.besselVC (c' / 12) t = V_C (c' : ℂ) t := by
  unfold Bessel.besselVC V_C
  have hs : ∀ α : ℂ, Summable fun k : ℕ =>
      (4 * (Real.pi : ℂ) ^ 2 * α) ^ k / ((k ! : ℂ) ^ 2) * t ^ k := fun α => by
    have h0 := summable_regularizedHGFun_one (4 * (Real.pi : ℂ) ^ 2 * α * t)
    have heq : (fun k : ℕ => (4 * (Real.pi : ℂ) ^ 2 * α * t) ^ k / ((k ! : ℂ) ^ 2)) =
        fun k : ℕ => (4 * (Real.pi : ℂ) ^ 2 * α) ^ k / ((k ! : ℂ) ^ 2) * t ^ k := by
      ext k; rw [mul_pow]; ring
    rwa [heq] at h0
  have hs0 := hs ((c' : ℂ) / 12)
  have hs1 := hs ((c' : ℂ) / 12 - 1)
  have hs2 := hs ((c' : ℂ) / 12 - 2)
  have hK0 : KalphaC ((c' : ℂ) / 12) t =
      ∑' k : ℕ, (4 * (Real.pi : ℂ) ^ 2 * ((c' : ℂ) / 12)) ^ k / ((k ! : ℂ) ^ 2) * t ^ k :=
    KalphaC_eq_tsum _ t
  have hK1 : KalphaC ((c' : ℂ) / 12 - 1) t =
      ∑' k : ℕ, (4 * (Real.pi : ℂ) ^ 2 * ((c' : ℂ) / 12 - 1)) ^ k / ((k ! : ℂ) ^ 2) * t ^ k :=
    KalphaC_eq_tsum _ t
  have hK2 : KalphaC ((c' : ℂ) / 12 - 2) t =
      ∑' k : ℕ, (4 * (Real.pi : ℂ) ^ 2 * ((c' : ℂ) / 12 - 2)) ^ k / ((k ! : ℂ) ^ 2) * t ^ k :=
    KalphaC_eq_tsum _ t
  have has := (hs0.hasSum.sub (hs1.hasSum.mul_left 2)).add hs2.hasSum
  rw [hK0, hK1, hK2, ← has.tsum_eq]
  refine tsum_congr fun k => ?_
  unfold Bessel.besselVCoeff
  push_cast
  simp only [mul_pow]
  ring

/-! ### Section 2: Uniform `O(1/c')` bound on a sectorial box -/

private lemma norm_exp_sub_one_le_of_re_nonpos' {w : ℂ} (hw : w.re ≤ 0) :
    ‖Complex.exp w - 1‖ ≤ 2 * ‖w‖ := by
  by_cases h1 : ‖w‖ ≤ 1
  · exact Complex.norm_exp_sub_one_le h1
  · have hge : 1 ≤ ‖w‖ := le_of_not_ge h1
    have hexp_le : ‖Complex.exp w‖ ≤ 1 := by
      rw [Complex.norm_exp]; exact Real.exp_le_one_iff.mpr hw
    calc ‖Complex.exp w - 1‖ ≤ ‖Complex.exp w‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := by rw [norm_one]; linarith
      _ = 2 := by norm_num
      _ ≤ 2 * ‖w‖ := by linarith

/-- Uniform bracket error bound for `besselErrC` on `{b : ℂ | m ≤ b.re ∧ |b.im| ≤ b.re ∧ ‖b‖ ≤ M}`
with `0 < m`. -/
theorem besselErrC_bound_on_box {m M : ℝ} (hm : 0 < m) (hM : 0 ≤ M) :
    ∃ C c₀ : ℝ, 0 ≤ C ∧ 48 ≤ c₀ ∧
      ∀ {c' : ℝ}, c₀ ≤ c' → ∀ {b : ℂ}, m ≤ b.re → |b.im| ≤ b.re → ‖b‖ ≤ M →
        ‖Bessel.besselErrC c' b‖ ≤ C / c' := by
  obtain ⟨C_I0, hCI0_nn, hI0_bd⟩ := besselI0Asymptotic
  let c₀ : ℝ := max 48 (6 / m)
  let C_j : ℝ := 2 * C_I0 / m + 48 + 605 * M
  let C : ℝ := 4 * C_j
  refine ⟨C, c₀, by positivity, le_max_left _ _, fun {c'} hc' {b} hm_b him_b hM_b => ?_⟩
  have hc48 : 48 ≤ c' := (le_max_left 48 (6 / m)).trans hc'
  have hc6m : 6 / m ≤ c' := (le_max_right 48 (6 / m)).trans hc'
  have hc'_pos : 0 < c' := by linarith
  have hmc' : 6 ≤ m * c' := by linarith [(div_le_iff₀ hm).mp hc6m]
  let z₀ : ℂ := (c' : ℂ) * tipL b
  have hz₀_eq : z₀ = ((c' * (2 * Real.pi / 3) : ℝ) : ℂ) * b := by
    dsimp [z₀]; unfold tipL; push_cast; ring
  have hc2pi3_pos : 0 < c' * (2 * Real.pi / 3) := by positivity
  have hz₀_re : z₀.re = (c' * (2 * Real.pi / 3)) * b.re := by
    rw [hz₀_eq, Complex.re_ofReal_mul]
  have hz₀_im : z₀.im = (c' * (2 * Real.pi / 3)) * b.im := by
    rw [hz₀_eq, Complex.im_ofReal_mul]
  have hz₀_norm_le : ‖z₀‖ ≤ c' * (2.1 * M) := by
    rw [hz₀_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc2pi3_pos]
    have h2pi3_le : 2 * Real.pi / 3 ≤ 2.1 := by nlinarith [Real.pi_lt_d4]
    calc c' * (2 * Real.pi / 3) * ‖b‖ ≤ c' * 2.1 * M :=
          mul_le_mul (mul_le_mul_of_nonneg_left h2pi3_le hc'_pos.le) hM_b (norm_nonneg _)
            (by positivity)
      _ = c' * (2.1 * M) := by ring
  have hz₀_re_ge : 2 * c' * m ≤ z₀.re := by
    rw [hz₀_re]
    have h2pi3_ge : 2 ≤ 2 * Real.pi / 3 := by nlinarith [Real.pi_gt_d4]
    calc 2 * c' * m ≤ (c' * (2 * Real.pi / 3)) * m := by nlinarith
      _ ≤ (c' * (2 * Real.pi / 3)) * b.re := by gcongr
  have hz₀_pos : 0 < z₀.re := by
    have : 0 < 2 * c' * m := by positivity
    linarith
  have hz₀_ne : z₀ ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hz₀_pos; exact lt_irrefl 0 hz₀_pos
  have hpi_ne : (2 * (Real.pi : ℂ) * z₀) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')) hz₀_ne
  have has0_ne : asC z₀ ≠ 0 := by
    unfold asC
    exact div_ne_zero (Complex.exp_ne_zero _) (Complex.cpow_ne_zero_iff.mpr (Or.inl hpi_ne))
  have hj_bound : ∀ j : ℕ, j ≤ 2 → ∃ err_j : ℂ,
      KalphaC ((c' / 12 - (j : ℝ) : ℝ) : ℂ) ((c' : ℂ) * b ^ 2 / 3) =
        asC z₀ * (Complex.exp (-4 * (Real.pi : ℂ) * (j : ℂ) * b) + err_j) ∧
      ‖err_j‖ ≤ C_j / c' := by
    intro j hj
    have hj_r : (j : ℝ) ≤ 2 := by exact_mod_cast hj
    have hα_pos : 0 < c' / 12 - (j : ℝ) := by linarith
    let r : ℝ := √(1 - 12 * (j : ℝ) / c')
    have hrad_ge : (1 : ℝ) / 2 ≤ 1 - 12 * (j : ℝ) / c' := by
      have : 12 * (j : ℝ) / c' ≤ 24 / 48 := by
        calc 12 * (j : ℝ) / c' ≤ 24 / c' := by gcongr; linarith
          _ ≤ 24 / 48 := by gcongr
      linarith
    have hrad_le : 1 - 12 * (j : ℝ) / c' ≤ 1 := by
      have : 0 ≤ 12 * (j : ℝ) / c' := by positivity
      linarith
    have hr_pos : 0 < r := Real.sqrt_pos.mpr (by linarith)
    have hr_gt_half : (1 / 2 : ℝ) < r := by
      rw [show (1 / 2 : ℝ) = √(1 / 4 : ℝ) by norm_num [Real.sqrt_div, Real.sqrt_one]]
      exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
    have hr_le1 : r ≤ 1 := Real.sqrt_le_one.mpr hrad_le
    let zj : ℂ := (r : ℂ) * z₀
    have hK_eq : KalphaC ((c' / 12 - (j : ℝ) : ℝ) : ℂ) ((c' : ℂ) * b ^ 2 / 3) = besselI0C zj := by
      rw [KalphaC_eq_besselI0C hα_pos.le hc'_pos.le b]
      congr 1
      have hsqrt_id : 4 * Real.pi * √((c' / 12 - (j : ℝ)) * c' / 3) =
          c' * (2 * Real.pi / 3) * r := by
        have harg : (c' / 12 - (j : ℝ)) * c' / 3 = (c' / 6) ^ 2 * (1 - 12 * (j : ℝ) / c') := by
          field_simp [hc'_pos.ne']; ring
        rw [harg, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
        dsimp [r]; ring
      rw [show 4 * (Real.pi : ℂ) * b * ((√((c' / 12 - (j : ℝ)) * c' / 3) : ℝ) : ℂ) =
          ((4 * Real.pi * √((c' / 12 - (j : ℝ)) * c' / 3) : ℝ) : ℂ) * b by push_cast; ring,
        hsqrt_id]
      rw [show zj = ((c' * (2 * Real.pi / 3) * r : ℝ) : ℂ) * b by
        dsimp [zj]; rw [hz₀_eq]; push_cast; ring]
    have hzj_re : 2 ≤ zj.re := by
      rw [show zj = (r : ℂ) * z₀ from rfl, Complex.re_ofReal_mul]
      calc (2 : ℝ) ≤ (1 / 2 : ℝ) * 6 := by norm_num
        _ ≤ (1 / 2 : ℝ) * (2 * c' * m) := by nlinarith
        _ ≤ r * z₀.re := mul_le_mul hr_gt_half.le hz₀_re_ge (by positivity) hr_pos.le
    have hzj_im : |zj.im| ≤ zj.re := by
      rw [show zj = (r : ℂ) * z₀ from rfl, Complex.re_ofReal_mul, Complex.im_ofReal_mul,
        abs_mul, abs_of_pos hr_pos, hz₀_im, hz₀_re, abs_mul, abs_of_pos hc2pi3_pos]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left him_b hc2pi3_pos.le) hr_pos.le
    have hzj_norm : m * c' ≤ ‖zj‖ := by
      have hzj_eq_re : zj.re = r * z₀.re := Complex.re_ofReal_mul r z₀
      calc m * c' = (1 / 2 : ℝ) * (2 * c' * m) := by ring
        _ ≤ r * z₀.re := mul_le_mul hr_gt_half.le hz₀_re_ge (by positivity) hr_pos.le
        _ = zj.re := hzj_eq_re.symm
        _ ≤ |zj.re| := le_abs_self _
        _ ≤ ‖zj‖ := Complex.abs_re_le_norm zj
    have hI0_z := hI0_bd zj hzj_re hzj_im
    have has_ratio : asC zj = asC z₀ *
        (((r ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Complex.exp (-((1 - r : ℝ) : ℂ) * z₀)) := by
      unfold asC
      have hden : (2 * (Real.pi : ℂ) * zj) ^ (1 / 2 : ℂ) =
          ((√r : ℝ) : ℂ) * (2 * (Real.pi : ℂ) * z₀) ^ (1 / 2 : ℂ) := by
        rw [show 2 * (Real.pi : ℂ) * zj = (r : ℂ) * (2 * (Real.pi : ℂ) * z₀) by dsimp [zj]; ring,
          ofReal_mul_cpow hr_pos (2 * (Real.pi : ℂ) * z₀) (1 / 2 : ℂ),
          show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
          ← Complex.ofReal_cpow hr_pos.le, ← Real.sqrt_eq_rpow]
      have hexp_zj : Complex.exp zj =
          Complex.exp z₀ * Complex.exp (-((1 - r : ℝ) : ℂ) * z₀) := by
        rw [← Complex.exp_add]; congr 1; dsimp [zj]; push_cast; ring
      have hsqrt_inv : ((√r : ℝ) : ℂ)⁻¹ = ((r ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
        rw [Real.sqrt_eq_rpow, ← Complex.ofReal_inv, ← Real.rpow_neg hr_pos.le]
      rw [hden, hexp_zj, ← hsqrt_inv]
      have hsqrt_c : ((√r : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hr_pos).ne'
      have h2pi_c : (2 * (Real.pi : ℂ) * z₀) ^ (1 / 2 : ℂ) ≠ 0 :=
        Complex.cpow_ne_zero_iff.mpr (Or.inl hpi_ne)
      field_simp [hsqrt_c, h2pi_c]
    let η : ℝ := 1 - r - 6 * (j : ℝ) / c'
    have hη_nn : 0 ≤ η := by
      dsimp [η]
      have h1 : 0 ≤ 1 - 6 * (j : ℝ) / c' := by
        have : 6 * (j : ℝ) / c' ≤ 12 / 48 := by
          calc 6 * (j : ℝ) / c' ≤ 12 / c' := by gcongr; linarith
            _ ≤ 12 / 48 := by gcongr
        linarith
      have hsq_le : r ^ 2 ≤ (1 - 6 * (j : ℝ) / c') ^ 2 := by
        have hexp : (1 - 6 * (j : ℝ) / c') ^ 2 = 1 - 12 * (j : ℝ) / c' + (6 * (j : ℝ) / c') ^ 2 := by
          ring
        rw [Real.sq_sqrt (by linarith), hexp]
        linarith only [sq_nonneg (6 * (j : ℝ) / c')]
      have := Real.sqrt_le_sqrt hsq_le
      rw [Real.sqrt_sq h1, Real.sqrt_sq hr_pos.le] at this
      linarith
    have hη_le : η ≤ 144 / c' ^ 2 := by
      have hsum_ge1 : (1 : ℝ) ≤ (1 - 6 * (j : ℝ) / c') + r := by
        have h1 : 6 * (j : ℝ) / c' ≤ 12 / 48 := by
          calc 6 * (j : ℝ) / c' ≤ 12 / c' := by gcongr; linarith
            _ ≤ 12 / 48 := by gcongr
        linarith
      have hdiff_sq : ((1 - 6 * (j : ℝ) / c') + r) * η = (6 * (j : ℝ) / c') ^ 2 := by
        have hsq : r ^ 2 = 1 - 12 * (j : ℝ) / c' := Real.sq_sqrt (by linarith)
        dsimp [η]; linear_combination -hsq
      have hnum_le : (6 * (j : ℝ) / c') ^ 2 ≤ 144 / c' ^ 2 := by
        have : 6 * (j : ℝ) ≤ 12 := by linarith
        calc (6 * (j : ℝ) / c') ^ 2 ≤ (12 / c') ^ 2 := by gcongr
          _ = 144 / c' ^ 2 := by ring
      nlinarith
    let δ : ℂ := (η : ℂ) * z₀
    have hδ_re : (-δ).re ≤ 0 := by
      rw [show (-δ).re = -η * z₀.re by dsimp [δ]; simp]
      have hηz : 0 ≤ η * z₀.re := mul_nonneg hη_nn hz₀_pos.le
      linarith only [hηz]
    have hδ_norm : ‖-δ‖ ≤ 302.4 * M / c' := by
      rw [norm_neg]; dsimp [δ]; rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hη_nn]
      calc η * ‖z₀‖ ≤ (144 / c' ^ 2) * (c' * (2.1 * M)) :=
            mul_le_mul hη_le hz₀_norm_le (norm_nonneg _) (by positivity)
        _ = 302.4 * M / c' := by field_simp [hc'_pos.ne']; ring
    have hexp_split : Complex.exp (-((1 - r : ℝ) : ℂ) * z₀) =
        Complex.exp (-4 * (Real.pi : ℂ) * (j : ℂ) * b) * Complex.exp (-δ) := by
      rw [← Complex.exp_add]
      congr 1
      dsimp [δ, η]
      rw [hz₀_eq]
      push_cast
      field_simp [hc'_pos.ne']
      ring
    have hexp_jb_norm : ‖Complex.exp (-4 * (Real.pi : ℂ) * (j : ℂ) * b)‖ ≤ 1 := by
      rw [Complex.norm_exp, Real.exp_le_one_iff]
      have hre_eq : (-4 * (Real.pi : ℂ) * (j : ℂ) * b).re = -4 * Real.pi * (j : ℝ) * b.re := by
        have h1 : (-4 * (Real.pi : ℂ) * (j : ℂ) : ℂ) =
            ((-4 * Real.pi * (j : ℝ) : ℝ) : ℂ) := by push_cast; ring
        rw [h1, Complex.re_ofReal_mul]
      rw [hre_eq]
      have : 0 ≤ 4 * Real.pi * (j : ℝ) * b.re := by
        have : 0 ≤ b.re := by linarith
        positivity
      linarith only [this]
    have hr_pow_bd : |r ^ (-(1 / 2 : ℝ)) - 1| ≤ 48 / c' := by
      have hden_ge : (1 / 2 : ℝ) ≤ √r * (1 + √r) := by
        have hsq_half : (1 / 2 : ℝ) ≤ √r * √r := by rw [Real.mul_self_sqrt hr_pos.le]; exact hr_gt_half.le
        have hmul_pos : 0 ≤ √r := Real.sqrt_nonneg _
        calc (1 / 2 : ℝ) ≤ √r * √r := hsq_half
          _ ≤ √r * (1 + √r) := by nlinarith only [hmul_pos]
      have h_id : (r ^ (-(1 / 2 : ℝ)) - 1) * (√r * (1 + √r)) = 1 - r := by
        rw [Real.rpow_neg hr_pos.le, ← Real.sqrt_eq_rpow]
        have hsq : √r ^ 2 = r := Real.sq_sqrt hr_pos.le
        have hne : √r ≠ 0 := (Real.sqrt_pos.mpr hr_pos).ne'
        field_simp [hne]; linear_combination -hsq
      have hr_pow_ge1 : 1 ≤ r ^ (-(1 / 2 : ℝ)) := by
        rw [Real.rpow_neg hr_pos.le, one_le_inv₀ (Real.rpow_pos_of_pos hr_pos _)]
        exact Real.rpow_le_one hr_pos.le hr_le1 (by norm_num)
      have h1_sub_r : 1 - r ≤ 24 / c' := by
        have h1 : (1 + r) * (1 - r) = 12 * (j : ℝ) / c' := by
          have hsq : r ^ 2 = 1 - 12 * (j : ℝ) / c' := Real.sq_sqrt (by linarith only [hrad_ge])
          linarith only [hsq, show (1 + r) * (1 - r) = 1 - r ^ 2 by ring]
        have h12 : 12 * (j : ℝ) / c' ≤ 24 / c' :=
          div_le_div_of_nonneg_right (by linarith only [hj_r]) hc'_pos.le
        have h_ir_nn : 0 ≤ 1 - r := by linarith only [hr_le1]
        have h_1r_ge1 : 1 ≤ 1 + r := by linarith only [hr_pos]
        calc 1 - r ≤ (1 + r) * (1 - r) := le_mul_of_one_le_left h_ir_nn h_1r_ge1
          _ = 12 * (j : ℝ) / c' := h1
          _ ≤ 24 / c' := h12
      have h0 : 0 ≤ r ^ (-(1 / 2 : ℝ)) - 1 := sub_nonneg.mpr hr_pow_ge1
      have h_mul : (r ^ (-(1 / 2 : ℝ)) - 1) * (1 / 2 : ℝ) ≤ 24 / c' :=
        calc (r ^ (-(1 / 2 : ℝ)) - 1) * (1 / 2 : ℝ)
            ≤ (r ^ (-(1 / 2 : ℝ)) - 1) * (√r * (1 + √r)) := mul_le_mul_of_nonneg_left hden_ge h0
          _ = 1 - r := h_id
          _ ≤ 24 / c' := h1_sub_r
      rw [abs_of_nonneg h0]
      calc r ^ (-(1 / 2 : ℝ)) - 1
          = 2 * ((r ^ (-(1 / 2 : ℝ)) - 1) * (1 / 2 : ℝ)) := by ring
        _ ≤ 2 * (24 / c') := mul_le_mul_of_nonneg_left h_mul (by norm_num)
        _ = 48 / c' := by ring
    have hr_pow_le2' : ‖((r ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ ≤ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hr_pos.le _),
        Real.rpow_neg hr_pos.le, inv_le_comm₀ (Real.rpow_pos_of_pos hr_pos _) (by norm_num)]
      have hsqrt_ge : (1 / 2 : ℝ) ≤ √r := by
        have : (1 / 4 : ℝ) ≤ r := by linarith only [hrad_ge, hr_gt_half]
        have : √(1 / 4 : ℝ) ≤ √r := Real.sqrt_le_sqrt this
        rwa [show √(1 / 4 : ℝ) = 1 / 2 by norm_num [Real.sqrt_div, Real.sqrt_one]] at this
      rw [← Real.sqrt_eq_rpow]
      linarith only [hsqrt_ge]
    let mainFac : ℂ := Complex.exp (-4 * (Real.pi : ℂ) * (j : ℂ) * b)
    let asympFac : ℂ := (((r ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Complex.exp (-((1 - r : ℝ) : ℂ) * z₀))
    let diff1 : ℂ := besselI0C zj - asC zj
    let err_j : ℂ := diff1 / asC z₀ + (asympFac - mainFac)
    refine ⟨err_j, ?_, ?_⟩
    · have has_mul : asC z₀ * asympFac = asC zj := has_ratio.symm
      rw [hK_eq]
      calc besselI0C zj = (besselI0C zj - asC zj) + asC z₀ * asympFac := by rw [has_mul]; ring
        _ = asC z₀ * (mainFac + err_j) := by
            dsimp [err_j, diff1, mainFac]; field_simp [has0_ne]; ring
    · have has_rel : ‖asC zj‖ / ‖asC z₀‖ ≤ 2 := by
        rw [has_ratio, norm_mul, norm_mul, mul_div_cancel_left₀ _ (norm_ne_zero_iff.mpr has0_ne)]
        have hexp_re_le : ‖Complex.exp (-((1 - r : ℝ) : ℂ) * z₀)‖ ≤ 1 := by
          rw [Complex.norm_exp, Real.exp_le_one_iff]
          have h1 : (-((1 - r : ℝ) : ℂ) * z₀).re = -(1 - r) * z₀.re := by
            rw [show -((1 - r : ℝ) : ℂ) = ((-(1 - r) : ℝ) : ℂ) by push_cast; rfl,
              Complex.re_ofReal_mul]
          rw [h1]
          exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by linarith)) hz₀_pos.le
        calc ‖((r ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ * ‖Complex.exp (-((1 - r : ℝ) : ℂ) * z₀)‖
            ≤ 2 * 1 := mul_le_mul hr_pow_le2' hexp_re_le (norm_nonneg _) (by norm_num)
          _ = 2 := mul_one 2
      have hterm1 : ‖diff1 / asC z₀‖ ≤ (2 * C_I0 / m) / c' := by
        rw [norm_div]
        calc ‖besselI0C zj - asC zj‖ / ‖asC z₀‖
            ≤ ((C_I0 / ‖zj‖) * ‖asC zj‖) / ‖asC z₀‖ :=
              div_le_div_of_nonneg_right hI0_z (norm_nonneg _)
          _ = (C_I0 / ‖zj‖) * (‖asC zj‖ / ‖asC z₀‖) := by ring
          _ ≤ (C_I0 / (m * c')) * 2 :=
              mul_le_mul (div_le_div_of_nonneg_left hCI0_nn (by positivity) hzj_norm)
                has_rel (by positivity) (by positivity)
          _ = (2 * C_I0 / m) / c' := by ring
      have hterm2 : ‖asympFac - mainFac‖ ≤ (48 + 605 * M) / c' := by
        have hid : asympFac - mainFac =
            (((r ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) - 1) * (mainFac * Complex.exp (-δ)) +
              mainFac * (Complex.exp (-δ) - 1) := by
          dsimp [asympFac, mainFac]; rw [hexp_split]; ring
        have hexp_δ_le1 : ‖Complex.exp (-δ)‖ ≤ 1 := by
          rw [Complex.norm_exp, Real.exp_le_one_iff]; exact hδ_re
        have hexp_δ_sub : ‖Complex.exp (-δ) - 1‖ ≤ 604.8 * M / c' := by
          calc ‖Complex.exp (-δ) - 1‖ ≤ 2 * ‖-δ‖ := norm_exp_sub_one_le_of_re_nonpos' hδ_re
            _ ≤ 2 * (302.4 * M / c') := by gcongr
            _ = 604.8 * M / c' := by ring
        have hr_c : ‖((r ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) - 1‖ ≤ 48 / c' := by
          rw [show (((r ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) - 1) = (((r ^ (-(1 / 2 : ℝ)) - 1 : ℝ) : ℂ)) by
            push_cast; rfl, Complex.norm_real, Real.norm_eq_abs]
          exact hr_pow_bd
        rw [hid]
        calc ‖(((r ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) - 1) * (mainFac * Complex.exp (-δ)) +
                mainFac * (Complex.exp (-δ) - 1)‖
            ≤ ‖(((r ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) - 1)‖ * (‖mainFac‖ * ‖Complex.exp (-δ)‖) +
                ‖mainFac‖ * ‖Complex.exp (-δ) - 1‖ := by
              refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
              · rw [norm_mul, norm_mul]
              · rw [norm_mul]
          _ ≤ (48 / c') * (1 * 1) + 1 * (604.8 * M / c') := by gcongr
          _ = (48 + 604.8 * M) / c' := by ring
          _ ≤ (48 + 605 * M) / c' := by
              gcongr; norm_num
      calc ‖err_j‖ ≤ ‖diff1 / asC z₀‖ + ‖asympFac - mainFac‖ := norm_add_le _ _
        _ ≤ (2 * C_I0 / m) / c' + (48 + 605 * M) / c' := add_le_add hterm1 hterm2
        _ = C_j / c' := by dsimp [C_j]; ring
  obtain ⟨err₀, hK0, herr0⟩ := hj_bound 0 (by norm_num)
  obtain ⟨err₁, hK1, herr1⟩ := hj_bound 1 (by norm_num)
  obtain ⟨err₂, hK2, herr2⟩ := hj_bound 2 (by norm_num)
  let ε_V : ℂ := err₀ - 2 * err₁ + err₂
  have hV_eq : V_C (c' : ℂ) ((c' : ℂ) * b ^ 2 / 3) =
      asC z₀ * ((1 - Complex.exp (-4 * (Real.pi : ℂ) * b)) ^ 2 + ε_V) := by
    unfold V_C
    have h0' : KalphaC ((c' : ℂ) / 12) ((c' : ℂ) * b ^ 2 / 3) = asC z₀ * (1 + err₀) := by
      simpa using hK0
    have h1' : KalphaC ((c' : ℂ) / 12 - 1) ((c' : ℂ) * b ^ 2 / 3) =
        asC z₀ * (Complex.exp (-4 * (Real.pi : ℂ) * b) + err₁) := by
      simpa using hK1
    have h2' : KalphaC ((c' : ℂ) / 12 - 2) ((c' : ℂ) * b ^ 2 / 3) =
        asC z₀ * (Complex.exp (-4 * (Real.pi : ℂ) * (2 : ℂ) * b) + err₂) := by
      simpa using hK2
    rw [h0', h1', h2']
    have hexp2 : Complex.exp (-4 * (Real.pi : ℂ) * (2 : ℂ) * b) =
        (Complex.exp (-4 * (Real.pi : ℂ) * b)) ^ 2 := by
      rw [sq, ← Complex.exp_add]; congr 1; ring
    rw [hexp2]
    change asC z₀ * (1 + err₀) - 2 * (asC z₀ * (Complex.exp (-4 * (Real.pi : ℂ) * b) + err₁)) +
        asC z₀ * ((Complex.exp (-4 * (Real.pi : ℂ) * b)) ^ 2 + err₂) =
      asC z₀ * ((1 - Complex.exp (-4 * (Real.pi : ℂ) * b)) ^ 2 + ε_V)
    dsimp [ε_V]; ring
  have herr_eq : Bessel.besselErrC c' b = ε_V := by
    unfold Bessel.besselErrC Bessel.besselAsC
    rw [besselVC_eq_V_C, show (c' : ℂ) * (2 * (Real.pi : ℂ) * b / 3) = z₀ by
      dsimp [z₀]; unfold tipL; push_cast; ring]
    change V_C (c' : ℂ) ((c' : ℂ) * b ^ 2 / 3) / asC z₀ -
        (1 - Complex.exp (-(4 * (Real.pi : ℂ) * b))) ^ 2 = ε_V
    rw [hV_eq, mul_div_cancel_left₀ _ has0_ne]
    rw [show -(4 * (Real.pi : ℂ) * b) = -4 * (Real.pi : ℂ) * b by ring]
    ring
  rw [herr_eq]
  have hnorm_tri : ‖ε_V‖ ≤ ‖err₀‖ + 2 * ‖err₁‖ + ‖err₂‖ := by
    have h2err : ‖(2 : ℂ) * err₁‖ = 2 * ‖err₁‖ := by
      rw [norm_mul, Complex.norm_ofNat]
    calc ‖err₀ - 2 * err₁ + err₂‖ ≤ ‖err₀ - 2 * err₁‖ + ‖err₂‖ := norm_add_le _ _
      _ ≤ (‖err₀‖ + ‖(2 : ℂ) * err₁‖) + ‖err₂‖ :=
          add_le_add (norm_sub_le err₀ ((2 : ℂ) * err₁)) le_rfl
      _ = ‖err₀‖ + 2 * ‖err₁‖ + ‖err₂‖ := by rw [h2err]
  calc ‖ε_V‖ ≤ ‖err₀‖ + 2 * ‖err₁‖ + ‖err₂‖ := hnorm_tri
    _ ≤ C_j / c' + 2 * (C_j / c') + C_j / c' :=
        add_le_add (add_le_add herr0 (mul_le_mul_of_nonneg_left herr1 (by norm_num))) herr2
    _ = C / c' := by dsimp [C]; ring

/-! ### Section 3: Holomorphicity on the neighbourhood and Cauchy derivative bounds -/

lemma besselErrC_differentiableOn {c' : ℝ} (hc' : 0 < c') :
    DifferentiableOn ℂ (Bessel.besselErrC c') {b : ℂ | 0 < b.re} := by
  intro b hb
  have hV : DifferentiableAt ℂ (fun w : ℂ => Bessel.besselVC (c' / 12) ((c' : ℂ) * w ^ 2 / 3)) b := by
    have heq : (fun w : ℂ => Bessel.besselVC (c' / 12) ((c' : ℂ) * w ^ 2 / 3)) =
        fun w : ℂ => V_C (c' : ℂ) ((c' : ℂ) * w ^ 2 / 3) := by
      ext w; exact besselVC_eq_V_C c' _
    rw [heq]
    exact (V_C_entire (c' : ℂ) _).comp b
      ((((differentiableAt_id.pow 2).const_mul (c' : ℂ)).div_const 3))
  have harg_re : 0 < (2 * (Real.pi : ℂ) * ((c' : ℂ) * (2 * (Real.pi : ℂ) * b / 3))).re := by
    have heq : 2 * (Real.pi : ℂ) * ((c' : ℂ) * (2 * (Real.pi : ℂ) * b / 3)) =
        ((4 * Real.pi ^ 2 * c' / 3 : ℝ) : ℂ) * b := by push_cast; ring
    rw [heq, Complex.re_ofReal_mul]
    exact mul_pos (by positivity) hb
  have harg_slit : 2 * (Real.pi : ℂ) * ((c' : ℂ) * (2 * (Real.pi : ℂ) * b / 3)) ∈
      Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl harg_re)
  have harg_diff : DifferentiableAt ℂ
      (fun w : ℂ => 2 * (Real.pi : ℂ) * ((c' : ℂ) * (2 * (Real.pi : ℂ) * w / 3))) b := by
    fun_prop
  have hcpow_diff : DifferentiableAt ℂ
      (fun w : ℂ => (2 * (Real.pi : ℂ) * ((c' : ℂ) * (2 * (Real.pi : ℂ) * w / 3))) ^ (1 / 2 : ℂ)) b :=
    harg_diff.cpow (differentiableAt_const (1 / 2 : ℂ)) harg_slit
  have hcpow_ne : (2 * (Real.pi : ℂ) * ((c' : ℂ) * (2 * (Real.pi : ℂ) * b / 3))) ^ (1 / 2 : ℂ) ≠ 0 := by
    refine Complex.cpow_ne_zero_iff.mpr (Or.inl ?_)
    intro h0
    rw [h0, Complex.zero_re] at harg_re
    exact lt_irrefl 0 harg_re
  have has_diff : DifferentiableAt ℂ
      (fun w : ℂ => Bessel.besselAsC ((c' : ℂ) * (2 * (Real.pi : ℂ) * w / 3))) b := by
    unfold Bessel.besselAsC
    have hnum : DifferentiableAt ℂ
        (fun w : ℂ => Complex.exp ((c' : ℂ) * (2 * (Real.pi : ℂ) * w / 3))) b := by fun_prop
    exact hnum.div hcpow_diff hcpow_ne
  have has_ne : Bessel.besselAsC ((c' : ℂ) * (2 * (Real.pi : ℂ) * b / 3)) ≠ 0 := by
    unfold Bessel.besselAsC
    exact div_ne_zero (Complex.exp_ne_zero _) hcpow_ne
  have hbr_diff : DifferentiableAt ℂ
      (fun w : ℂ => (1 - Complex.exp (-(4 * (Real.pi : ℂ) * w))) ^ 2) b := by fun_prop
  exact ((hV.div has_diff has_ne).sub hbr_diff).differentiableWithinAt

/-- **Lemma B (c), complex-neighbourhood statement** (`lower_o1_two_edge.tex`, Lemma B `vlo:Bessel`):
discharges `Bessel.BesselComplexExpansion I` for every set `I : Set ℝ`. -/
theorem besselComplexExpansion (I : Set ℝ) : Bessel.BesselComplexExpansion I := by
  intro hI_cpct hI_sub
  by_cases hne : I.Nonempty
  · obtain ⟨m₀, hm₀_mem, hm₀_min⟩ := hI_cpct.exists_isMinOn hne continuousOn_id
    obtain ⟨M₀, hM₀_mem, hM₀_max⟩ := hI_cpct.exists_isMaxOn hne continuousOn_id
    have hm₀_pos : 0 < m₀ := hI_sub hm₀_mem
    have hm₀_le_M₀ : m₀ ≤ M₀ := hm₀_min hM₀_mem
    let δ : ℝ := m₀ / 2
    have hδ_pos : 0 < δ := by positivity
    let m : ℝ := m₀ / 2
    let M : ℝ := M₀ + m₀ / 2
    have hM_nn : 0 ≤ M := by dsimp [M]; linarith
    obtain ⟨C, c₀, hC_nn, hc₀_ge, hbox⟩ :=
      besselErrC_bound_on_box (m := m) (M := M) (by positivity) hM_nn
    refine ⟨δ, hδ_pos, C, c₀, ?_, ?_⟩
    · intro c' hc' b ⟨x, hx_mem, hbx⟩
      have hx_lo : m₀ ≤ x := hm₀_min hx_mem
      have hx_hi : x ≤ M₀ := hM₀_max hx_mem
      have hre_sub : |b.re - x| ≤ ‖b - (x : ℂ)‖ := by
        simpa [Complex.sub_re] using Complex.abs_re_le_norm (b - (x : ℂ))
      have him_sub : |b.im| ≤ ‖b - (x : ℂ)‖ := by
        simpa [Complex.sub_im] using Complex.abs_im_le_norm (b - (x : ℂ))
      have hb_re : m ≤ b.re := by
        have := (abs_lt.mp (hre_sub.trans_lt hbx)).1
        dsimp [m, δ] at *; linarith
      have hb_im : |b.im| ≤ b.re := by
        have := him_sub.trans_lt hbx
        dsimp [m, δ] at *; linarith
      have hb_norm : ‖b‖ ≤ M := by
        have hx_norm : ‖(x : ℂ)‖ = x := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hI_sub hx_mem)]
        calc ‖b‖ = ‖(b - (x : ℂ)) + (x : ℂ)‖ := by ring_nf
          _ ≤ ‖b - (x : ℂ)‖ + ‖(x : ℂ)‖ := norm_add_le _ _
          _ ≤ δ + x := add_le_add hbx.le hx_norm.le
          _ ≤ m₀ / 2 + M₀ := by dsimp [δ]; linarith
          _ = M := by dsimp [M]; ring
      exact hbox hc' hb_re hb_im hb_norm
    · intro n
      let r : ℝ := δ / 2
      have hr_pos : 0 < r := by positivity
      refine ⟨n ! * C / r ^ n, fun c' hc' x hx_mem => ?_⟩
      have hc'_pos : 0 < c' := by linarith
      have hx_pos : 0 < x := hI_sub hx_mem
      have hx_lo : m₀ ≤ x := hm₀_min hx_mem
      have hcl_sub : closedBall (x : ℂ) r ⊆ {w : ℂ | 0 < w.re} := by
        intro w hw
        have hdist : ‖w - (x : ℂ)‖ ≤ r := by simpa [Complex.dist_eq] using mem_closedBall.mp hw
        have hre_sub : |w.re - x| ≤ ‖w - (x : ℂ)‖ := by
          simpa [Complex.sub_re] using Complex.abs_re_le_norm (w - (x : ℂ))
        have := (abs_le.mp (hre_sub.trans hdist)).1
        change 0 < w.re
        dsimp [r, δ] at *; linarith
      have hdiff_cl : DiffContOnCl ℂ (Bessel.besselErrC c') (ball (x : ℂ) r) :=
        ⟨(besselErrC_differentiableOn hc'_pos).mono
            (Metric.ball_subset_closedBall.trans hcl_sub),
          ((besselErrC_differentiableOn hc'_pos).continuousOn).mono
            (closure_ball_subset_closedBall.trans hcl_sub)⟩
      have hsphere : ∀ w ∈ sphere (x : ℂ) r, ‖Bessel.besselErrC c' w‖ ≤ C / c' := by
        intro w hw
        have hdist : ‖w - (x : ℂ)‖ = r := by simpa [Complex.dist_eq] using mem_sphere.mp hw
        have hw_re : m ≤ w.re := by
          have hre_sub : |w.re - x| ≤ ‖w - (x : ℂ)‖ := by
            simpa [Complex.sub_re] using Complex.abs_re_le_norm (w - (x : ℂ))
          have := (abs_le.mp (hre_sub.trans hdist.le)).1
          have hx_lo' : m₀ ≤ x := hm₀_min hx_mem
          dsimp [m, r, δ] at *; linarith
        have hw_im : |w.im| ≤ w.re := by
          have him_sub : |w.im| ≤ ‖w - (x : ℂ)‖ := by
            simpa [Complex.sub_im] using Complex.abs_im_le_norm (w - (x : ℂ))
          have := him_sub.trans hdist.le
          dsimp [m, r, δ] at *; linarith
        have hw_norm : ‖w‖ ≤ M := by
          have hx_hi : x ≤ M₀ := hM₀_max hx_mem
          have hx_norm : ‖(x : ℂ)‖ = x := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx_pos]
          calc ‖w‖ = ‖(w - (x : ℂ)) + (x : ℂ)‖ := by ring_nf
            _ ≤ ‖w - (x : ℂ)‖ + ‖(x : ℂ)‖ := norm_add_le _ _
            _ ≤ r + x := add_le_add hdist.le hx_norm.le
            _ ≤ M := by dsimp [r, δ, M]; linarith
        exact hbox hc' hw_re hw_im hw_norm
      have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr_pos
        hdiff_cl hsphere
      calc ‖iteratedDeriv n (Bessel.besselErrC c') (x : ℂ)‖
          ≤ (n ! : ℝ) * (C / c') / r ^ n := hcauchy
        _ = ((n ! : ℝ) * C / r ^ n) / c' := by ring
  · rw [not_nonempty_iff_eq_empty] at hne
    subst hne
    exact ⟨1, one_pos, 0, 0, fun _ _ _ ⟨_, hx, _⟩ => False.elim hx,
      fun _ => ⟨0, fun _ _ _ hx => False.elim hx⟩⟩

/-! ### Axiom Verification -/

/-- info: 'FormalResearch.ModularBootstrap.ComplexBessel.besselVC_eq_V_C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms besselVC_eq_V_C

/-- info: 'FormalResearch.ModularBootstrap.ComplexBessel.besselComplexExpansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms besselComplexExpansion

end FormalResearch.ModularBootstrap.ComplexBessel