module

public import FormalResearch.SignUncertainty.O4SigmaBounds
public import FormalResearch.SignUncertainty.O4RhoSeries
public import FormalResearch.CohnElkies.O4CircleReduction

/-!
# `O4QuotientBound L` for `0 < L ≤ 0.002` (`u1co:O4(2)`, `[O4C (B)]`): the analytic estimate on `|θ| = 1/4`

On the circle `|θ| = 1/4` write `τ = σ₀ θ`, `Φ_L(τ) = L τ - π² τ³/36 + ρ(τ)` and `σ = σ₀`, `a = α̃`. Then

`Φ̂(θ) - Φ_mod(θ) = (L σ - a) θ - (π²/36)(σ³ - 1) θ³ + ρ(σ θ)`,

and `𝓕 = (Φ̂ - Φ_mod) / (θ (θ² - θ₀²)²)` is bounded as in the paper:

* `|L σ - a| ≤ 0.606 L² < 0.0000025` (`o4Sigma0_sharp`, `edgeKappa0_bounds`);
* `0.99975 ≤ σ ≤ 1.001212`, so `(π²/36) |σ³ - 1| < 0.001`;
* `‖ρ(τ)‖ ≤ d₂ T⁵ + d₃ T⁷ + T⁹/(18(1 - T²)) < 0.0000962` for `‖τ‖ ≤ T = 1.001212/4`, with `d₂ = 7π⁴/7200`,
  `d₃ = 31π⁶/635040` and `d_n ≤ 1/18` for `n ≥ 4` (`edgePhiC_rho_bound`, `3.14159 < π < 3.1416`);
* `θ₀² ≤ 0.00244`, so `‖θ (θ² - θ₀²)²‖ ≥ (1/4)(1/16 - 0.0025)² = 0.0009`.

Hence `‖𝓕‖ ≤ (0.0000025/4 + 0.001/64 + 0.0000962)/0.0009 < 0.125 ≤ 0.13` on `|θ| = 1/4`, and the maximum principle
(`o4QuotientBound_of_circle`) gives `O4QuotientBound L`.

**Formalised (proved, unconditional):** `o4QuotientBound : 0 < L → L ≤ 0.002 → O4QuotientBound L`.  All numerical inequalities
are exact rational arithmetic (`norm_num`) from `π < 3.1416`.

Status: proved.
-/

@[expose] public section

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies Complex
open scoped Real

/-- The scalar bound on `ρ`: with `T = (1 + 0.606·0.002)/4`, `d₂ T⁵ + d₃ T⁷ + T⁹/(18(1-T²)) ≤ 0.0000962`. -/
lemma o4_rho_numeric :
    7 / 7200 * π ^ 4 * ((1 + 0.606 * 0.002) / 4) ^ 5 + 31 / 635040 * π ^ 6 * ((1 + 0.606 * 0.002) / 4) ^ 7
      + 1 / 18 * ((1 + 0.606 * 0.002) / 4) ^ 9 / (1 - ((1 + 0.606 * 0.002) / 4) ^ 2) ≤ 0.0000962 := by
  have h0 := Real.pi_pos
  have h1 : π ≤ 3.1416 := Real.pi_lt_d4.le
  have h4 : π ^ 4 ≤ 3.1416 ^ 4 := pow_le_pow_left₀ h0.le h1 4
  have h6 : π ^ 6 ≤ 3.1416 ^ 6 := pow_le_pow_left₀ h0.le h1 6
  have e1 : 7 / 7200 * π ^ 4 * ((1 + 0.606 * 0.002) / 4) ^ 5 ≤
      7 / 7200 * 3.1416 ^ 4 * ((1 + 0.606 * 0.002) / 4) ^ 5 := by gcongr
  have e2 : 31 / 635040 * π ^ 6 * ((1 + 0.606 * 0.002) / 4) ^ 7 ≤
      31 / 635040 * 3.1416 ^ 6 * ((1 + 0.606 * 0.002) / 4) ^ 7 := by gcongr
  have e3 : 7 / 7200 * (3.1416 : ℝ) ^ 4 * ((1 + 0.606 * 0.002) / 4) ^ 5 +
      31 / 635040 * 3.1416 ^ 6 * ((1 + 0.606 * 0.002) / 4) ^ 7 +
      1 / 18 * ((1 + 0.606 * 0.002) / 4) ^ 9 / (1 - ((1 + 0.606 * 0.002) / 4) ^ 2) ≤ 0.0000962 := by
    norm_num
  linarith

/-- `(π²/36) |σ³ - 1| < 0.001` for `0.99975 ≤ σ ≤ 1.001212`. -/
lemma o4_cubic_numeric {σ : ℝ} (h1 : 0.99975 ≤ σ) (h2 : σ ≤ 1.001212) : π ^ 2 / 36 * |σ ^ 3 - 1| ≤ 0.001 := by
  have h0 := Real.pi_pos
  have hπ : π ^ 2 ≤ 3.1416 ^ 2 := pow_le_pow_left₀ h0.le Real.pi_lt_d4.le 2
  have hu : σ ^ 3 ≤ 1.001212 ^ 3 := pow_le_pow_left₀ (by linarith) h2 3
  have hl : 0.99975 ^ 3 ≤ σ ^ 3 := pow_le_pow_left₀ (by norm_num) h1 3
  have habs : |σ ^ 3 - 1| ≤ 0.0036405 := by
    rw [abs_le]; constructor <;> norm_num at hu hl ⊢ <;> linarith
  calc π ^ 2 / 36 * |σ ^ 3 - 1| ≤ 3.1416 ^ 2 / 36 * 0.0036405 := by
        gcongr
    _ ≤ 0.001 := by norm_num

/-- **`[O4C (B)]`**: `‖𝓕‖ ≤ 0.13` on `D(0, 0.25)` away from the removable singularities, for every `L ∈ (0, 0.002]`. -/
theorem o4QuotientBound {L : ℝ} (hL0 : 0 < L) (hL2 : L ≤ 0.002) : O4QuotientBound L := by
  apply o4QuotientBound_of_circle hL0 hL2
  intro θ hθ
  obtain ⟨hσ1, hσ2⟩ := o4Sigma0_sharp hL0 hL2
  obtain ⟨hk1, hk2⟩ := edgeKappa0_bounds hL0 hL2
  have hσpos := o4Sigma0_pos hL0
  have hθ0 := o4Theta0Sq_le hL0 hL2
  have hθ0pos := o4Theta0Sq_pos hL0
  set σ := o4Sigma0 L with hσdef
  set a := edgeAlphaTilde L with hadef
  have ha : a = edgeKappa0 L * L := by
    unfold edgeKappa0; rw [div_mul_cancel₀ _ hL0.ne']
  have hLL : L * L ≤ 0.000004 := by nlinarith
  have haL : L ≤ a := by rw [ha]; nlinarith
  have haU : a ≤ L + L * L / 4 := by
    rw [ha]; nlinarith [mul_le_mul_of_nonneg_right hk2 hL0.le]
  -- `|L σ - a| < 0.0000025`
  have hA : |L * σ - a| ≤ 0.0000025 := by
    have h1 := mul_le_mul_of_nonneg_left hσ1 hL0.le
    have h2 := mul_le_mul_of_nonneg_left hσ2 hL0.le
    rw [abs_le]; constructor <;> nlinarith
  -- `(π²/36)|σ³ - 1| < 0.001`
  have hB : π ^ 2 / 36 * |σ ^ 3 - 1| ≤ 0.001 :=
    o4_cubic_numeric (by linarith) (by linarith)
  -- the remainder `ρ`
  set τ : ℂ := (σ : ℂ) * θ with hτ
  have hτn : ‖τ‖ ≤ (1 + 0.606 * 0.002) / 4 := by
    rw [hτ, norm_mul, Complex.norm_real, hθ, Real.norm_of_nonneg hσpos.le]
    nlinarith
  set ρ : ℂ := edgePhiC L τ - ((L : ℂ) * τ - (π : ℂ) ^ 2 * τ ^ 3 / 36) with hρdef
  have hρ : ‖ρ‖ ≤ 0.0000962 :=
    (edgePhiC_rho_bound L hτn (by norm_num)).trans o4_rho_numeric
  -- numerator
  have hN : o4PhiHat L θ - o4PhiMod L θ =
      ((L * σ - a : ℝ) : ℂ) * θ - ((π ^ 2 / 36 * (σ ^ 3 - 1) : ℝ) : ℂ) * θ ^ 3 + ρ := by
    unfold o4PhiHat o4PhiMod
    rw [hρdef, hτ]
    push_cast
    ring
  have hNn : ‖o4PhiHat L θ - o4PhiMod L θ‖ ≤ 0.0000025 / 4 + 0.001 / 64 + 0.0000962 := by
    rw [hN]
    refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add ?_ ?_)) hρ)
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hθ]
      linarith
    · rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, hθ, abs_mul,
        abs_of_nonneg (by positivity : 0 ≤ π ^ 2 / 36)]
      nlinarith
  -- denominator
  have hq : (1 / 16 : ℝ) - 0.00244 ≤ ‖θ ^ 2 - (o4Theta0Sq L : ℂ)‖ := by
    have h := norm_sub_norm_le (θ ^ 2) (o4Theta0Sq L : ℂ)
    rw [norm_pow, hθ, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hθ0pos] at h
    norm_num at h ⊢
    linarith
  have hD : 0.0009 ≤ ‖θ * (θ ^ 2 - (o4Theta0Sq L : ℂ)) ^ 2‖ := by
    rw [norm_mul, norm_pow, hθ]
    have h0 : (0 : ℝ) ≤ 1 / 16 - 0.00244 := by norm_num
    have := pow_le_pow_left₀ h0 hq 2
    nlinarith
  unfold o4Quot
  rw [norm_div, div_le_iff₀ (lt_of_lt_of_le (by norm_num) hD)]
  nlinarith

/-- info: 'FormalResearch.SignUncertainty.o4QuotientBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms o4QuotientBound

end FormalResearch.SignUncertainty
