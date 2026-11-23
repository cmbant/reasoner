module

public import FormalResearch.SignUncertainty.HankelBessel

/-!
# Moments of the concrete Hankel kernel against `s^a e^{-2πs} ρ₀`

For `c > 0` (no `HankelKernelData` needed): the power series `φ_c(w) = Γ(c) ∑ (-1)^k (2π)^{2k} w^k/(k! Γ(c+k))`
(`hankelPhi_tsum`), termwise integration against `s^a e^{-2πs} ρ₀(s)` (`integral_hankel_rpow_exp`), and
the two cases `a = 0, 1`: `integral_hankel_exp` (`𝓗_c e^{-2πs} = e^{-2πΔ}`) and
`integral_hankel_linear_exp` (`𝓗_c (s e^{-2πs}) = (c/(2π) - Δ) e^{-2πΔ}`).
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped Real Nat

namespace FormalResearch.SignUncertainty

open FormalResearch.Special

/-- The power series of `φ_c` in `w = Δ s ≥ 0`. -/
theorem hankelPhi_tsum {c : ℝ} {w : ℝ} (hw : 0 ≤ w) :
    hankelPhi c w = Real.Gamma c *
      ∑' k : ℕ, (-1) ^ k * ((2 * π) ^ (2 * k) * w ^ k) / ((k ! : ℝ) * Real.Gamma (c + k)) := by
  unfold hankelPhi besselNorm
  rw [sub_add_cancel]
  congr 1
  refine tsum_congr fun k => ?_
  have h1 : (4 * π * √w / 2) = 2 * π * √w := by ring
  have h2 : (2 * π * √w) ^ (2 * k) = (2 * π) ^ (2 * k) * w ^ k := by
    rw [mul_pow, pow_mul (√w) 2 k, Real.sq_sqrt hw]
  rw [h1, h2, besselNormCoeff, show c - 1 + k + 1 = c + k by ring]
  ring


/-- The algebra of one term of the termwise integration. -/
private lemma term_algebra {r Δ c a : ℝ} (hr : 0 < r) (k : ℕ) (hc : 0 < c) :
    ((1 / r) ^ (c + k + a) * Real.Gamma (c + k + a)) *
        (r ^ c * r ^ (2 * k) * Δ ^ k / ((k ! : ℝ) * Real.Gamma (c + k))) =
      (1 / r) ^ a * ((r * Δ) ^ k / (k ! : ℝ) * (Real.Gamma (c + k + a) / Real.Gamma (c + k))) := by
  have hr1 : 0 < 1 / r := by positivity
  have h1 : (1 / r) ^ (c + k + a) = (r ^ c)⁻¹ * (r ^ k)⁻¹ * (1 / r) ^ a := by
    rw [Real.rpow_add hr1, Real.rpow_add hr1, Real.rpow_natCast, one_div, Real.inv_rpow hr.le,
      inv_pow]
  have h2 : r ^ (2 * k) = r ^ k * r ^ k := by rw [two_mul, pow_add]
  have hA : 0 < r ^ c := Real.rpow_pos_of_pos hr c
  have hB : 0 < r ^ k := pow_pos hr k
  have hG : 0 < Real.Gamma (c + k) := Real.Gamma_pos_of_pos (by positivity)
  have hf : (k ! : ℝ) ≠ 0 := by positivity
  rw [h1, h2, mul_pow]
  generalize r ^ c = A at *
  generalize r ^ k = B at *
  generalize (1 / r) ^ a = D at *
  generalize Real.Gamma (c + k) = G at *
  generalize Real.Gamma (c + k + a) = G' at *
  generalize (k ! : ℝ) = f at *
  field_simp


/-- **Termwise integration core.** For `c > 0`, `a ≥ 0`, `Δ ≥ 0` with the summability hypothesis
(checked below for `a = 0, 1`),
`∫_0^∞ s^a e^{-2πs} ρ₀(s) φ_c(Δ s) ds = (2π)^{-a} ∑_k (-1)^k (2πΔ)^k/k! · Γ(c+k+a)/Γ(c+k)`. -/
theorem integral_hankel_rpow_exp {c : ℝ} (hc : 0 < c) {a : ℝ} (ha : 0 ≤ a) {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hsum : Summable fun k : ℕ => (2 * π * Δ) ^ k / (k ! : ℝ) *
      (Real.Gamma (c + k + a) / Real.Gamma (c + k))) :
    ∫ s in Ioi (0 : ℝ), s ^ a * Real.exp (-(2 * π * s)) * hankelRho0 c s * hankelPhi c (Δ * s) =
      (1 / (2 * π)) ^ a * ∑' k : ℕ, (-1) ^ k * ((2 * π * Δ) ^ k / (k ! : ℝ) *
        (Real.Gamma (c + k + a) / Real.Gamma (c + k))) := by
  set r : ℝ := 2 * π with hr
  have hr0 : 0 < r := by positivity
  set C : ℕ → ℝ := fun k =>
    (-1) ^ k * (r ^ c * r ^ (2 * k) * Δ ^ k / ((k ! : ℝ) * Real.Gamma (c + k))) with hC
  set F : ℕ → ℝ → ℝ := fun k s =>
    C k * (s ^ (c + k + a - 1) * Real.exp (-(r * s))) with hF
  have hpos : ∀ k : ℕ, 0 < c + k + a := fun k => by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hFint : ∀ k, Integrable (F k) (volume.restrict (Ioi 0)) := by
    intro k
    have := integrableOn_rpow_mul_exp_neg_mul_Ioi (p := c + k + a - 1) (a := r)
      (by linarith [hpos k]) hr0
    simp only [neg_mul] at this
    exact this.const_mul (C k)
  have hFval : ∀ k, ∫ s in Ioi (0 : ℝ), F k s =
      C k * ((1 / r) ^ (c + k + a) * Real.Gamma (c + k + a)) := by
    intro k
    simp only [hF]
    rw [integral_const_mul]
    have := Real.integral_rpow_mul_exp_neg_mul_Ioi (hpos k) hr0
    rw [show c + k + a - 1 = c + k + a - 1 from rfl] at *
    rw [this]
  have hnorm : ∀ k, ∫ s in Ioi (0 : ℝ), ‖F k s‖ =
      |C k| * ((1 / r) ^ (c + k + a) * Real.Gamma (c + k + a)) := by
    intro k
    have hpt : ∀ s ∈ Ioi (0 : ℝ), ‖F k s‖ = |C k| * (s ^ (c + k + a - 1) * Real.exp (-(r * s))) := by
      intro s hs
      simp only [hF, norm_mul, Real.norm_eq_abs]
      rw [abs_of_nonneg (Real.rpow_nonneg (le_of_lt hs) _), abs_of_pos (Real.exp_pos _)]
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
      Real.integral_rpow_mul_exp_neg_mul_Ioi (hpos k) hr0]
  have hterm : ∀ k : ℕ, ((1 / r) ^ (c + k + a) * Real.Gamma (c + k + a)) * (r ^ c * r ^ (2 * k) *
      Δ ^ k / ((k ! : ℝ) * Real.Gamma (c + k))) = (1 / r) ^ a * ((r * Δ) ^ k / (k ! : ℝ) *
        (Real.Gamma (c + k + a) / Real.Gamma (c + k))) := fun k => term_algebra hr0 k hc
  have hCval : ∀ k, C k * ((1 / r) ^ (c + k + a) * Real.Gamma (c + k + a)) =
      (-1) ^ k * ((1 / r) ^ a * ((r * Δ) ^ k / (k ! : ℝ) *
        (Real.Gamma (c + k + a) / Real.Gamma (c + k)))) := by
    intro k
    rw [← hterm k, hC]
    ring
  have hCabs : ∀ k, |C k| * ((1 / r) ^ (c + k + a) * Real.Gamma (c + k + a)) =
      (1 / r) ^ a * ((r * Δ) ^ k / (k ! : ℝ) *
        (Real.Gamma (c + k + a) / Real.Gamma (c + k))) := by
    intro k
    have hCn : |C k| = r ^ c * r ^ (2 * k) * Δ ^ k / ((k ! : ℝ) * Real.Gamma (c + k)) := by
      rw [hC]
      simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      rw [abs_of_nonneg]
      have : 0 < Real.Gamma (c + k) := Real.Gamma_pos_of_pos (by positivity)
      have := Real.rpow_pos_of_pos hr0 c
      positivity
    rw [hCn, mul_comm, ← hterm k]
  have hsumm : Summable fun k : ℕ => ∫ s in Ioi (0 : ℝ), ‖F k s‖ := by
    simp_rw [hnorm, hCabs]
    exact hsum.mul_left _
  have hint := integral_tsum_of_summable_integral_norm
    (μ := volume.restrict (Ioi (0 : ℝ))) (F := F) hFint hsumm
  have hpt : ∀ s ∈ Ioi (0 : ℝ),
      s ^ a * Real.exp (-(r * s)) * hankelRho0 c s * hankelPhi c (Δ * s) = ∑' k, F k s := by
    intro s hs
    have hs0 : 0 < s := hs
    rw [hankelPhi_tsum (mul_nonneg hΔ hs0.le)]
    unfold hankelRho0
    rw [← hr]
    simp only [hF, hC]
    have hG : Real.Gamma c ≠ 0 := (Real.Gamma_pos_of_pos hc).ne'
    rw [show s ^ a * Real.exp (-(r * s)) * (r ^ c / Real.Gamma c * s ^ (c - 1)) *
        (Real.Gamma c * ∑' k : ℕ, (-1) ^ k * (r ^ (2 * k) * (Δ * s) ^ k) /
          ((k ! : ℝ) * Real.Gamma (c + k))) =
      (s ^ a * Real.exp (-(r * s)) * (r ^ c / Real.Gamma c * s ^ (c - 1)) * Real.Gamma c) *
        ∑' k : ℕ, (-1) ^ k * (r ^ (2 * k) * (Δ * s) ^ k) /
          ((k ! : ℝ) * Real.Gamma (c + k)) by ring, ← tsum_mul_left]
    refine tsum_congr fun k => ?_
    have hsk : s ^ (c + k + a - 1) = s ^ (c - 1) * s ^ a * s ^ k := by
      rw [show c + k + a - 1 = (c - 1) + a + k by ring, Real.rpow_add hs0, Real.rpow_add hs0,
        Real.rpow_natCast]
    rw [hsk, mul_pow]
    field_simp
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, ← hint]
  simp_rw [hFval, hCval]
  rw [← tsum_mul_left]
  exact tsum_congr fun k => by ring


/-! ### Exponential series -/

lemma hasSum_neg_pow_div_factorial (y : ℝ) :
    HasSum (fun k : ℕ => (-1) ^ k * (y ^ k / (k ! : ℝ))) (Real.exp (-y)) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (-y)
  rw [← Real.exp_eq_exp_ℝ] at h
  have e : ∀ k : ℕ, (-y) ^ k / (k ! : ℝ) = (-1) ^ k * (y ^ k / (k ! : ℝ)) := fun k => by
    rw [neg_pow y k, mul_div_assoc]
  simpa only [e] using h

lemma hasSum_nat_mul_pow_div_factorial (z : ℝ) :
    HasSum (fun k : ℕ => (k : ℝ) * (z ^ k / (k ! : ℝ))) (z * Real.exp z) := by
  have h := NormedSpace.expSeries_div_hasSum_exp z
  rw [← Real.exp_eq_exp_ℝ] at h
  rw [← hasSum_nat_add_iff' 1]
  rw [Finset.sum_range_one]
  rw [Nat.cast_zero, zero_mul, sub_zero]
  convert h.mul_left z using 2 with n
  rw [Nat.factorial_succ]
  push_cast
  have : ((n ! : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  ring


lemma integrableOn_rpow_exp_rho0 {c : ℝ} (hc : 0 < c) {a : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (fun s : ℝ => s ^ a * Real.exp (-(2 * π * s)) * hankelRho0 c s) (Ioi 0) := by
  have h : IntegrableOn (fun s : ℝ => (2 * π) ^ c / Real.Gamma c *
      (s ^ (c - 1 + a) * Real.exp (-(2 * π) * s))) (Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_Ioi (p := c - 1 + a) (a := 2 * π)
      (by linarith) (by positivity)).const_mul ((2 * π) ^ c / Real.Gamma c)
  refine h.congr_fun (fun s hs => ?_) measurableSet_Ioi
  have hs0 : 0 < s := hs
  simp only [hankelRho0, neg_mul]
  rw [Real.rpow_add hs0]
  ring

/-- `𝓗_c e^{-2πs} = e^{-2πΔ}` (the integral form, `Δ ≥ 0`, `c > 0`). -/
theorem integral_hankel_exp {c : ℝ} (hc : 0 < c) {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    ∫ s in Ioi (0 : ℝ), Real.exp (-(2 * π * s)) * hankelRho0 c s * hankelPhi c (Δ * s) =
      Real.exp (-(2 * π * Δ)) := by
  have hT : ∀ k : ℕ, (2 * π * Δ) ^ k / (k ! : ℝ) *
      (Real.Gamma (c + k + 0) / Real.Gamma (c + k)) = (2 * π * Δ) ^ k / (k ! : ℝ) := by
    intro k
    have : Real.Gamma (c + k) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
    rw [add_zero, div_self this, mul_one]
  have hsum : Summable fun k : ℕ => (2 * π * Δ) ^ k / (k ! : ℝ) *
      (Real.Gamma (c + k + 0) / Real.Gamma (c + k)) := by
    simp_rw [hT]; exact Real.summable_pow_div_factorial _
  have h := integral_hankel_rpow_exp hc (le_refl 0) hΔ hsum
  simp only [Real.rpow_zero, one_mul] at h
  rw [h]
  simp_rw [hT]
  exact (hasSum_neg_pow_div_factorial (2 * π * Δ)).tsum_eq

/-- `𝓗_c (s e^{-2πs}) = (c/(2π) - Δ) e^{-2πΔ}` (the integral form). -/
theorem integral_hankel_linear_exp {c : ℝ} (hc : 0 < c) {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    ∫ s in Ioi (0 : ℝ), s * Real.exp (-(2 * π * s)) * hankelRho0 c s * hankelPhi c (Δ * s) =
      (c / (2 * π) - Δ) * Real.exp (-(2 * π * Δ)) := by
  have hT : ∀ k : ℕ, (2 * π * Δ) ^ k / (k ! : ℝ) *
      (Real.Gamma (c + k + 1) / Real.Gamma (c + k)) = (c : ℝ) * ((2 * π * Δ) ^ k / (k ! : ℝ)) +
        (k : ℝ) * ((2 * π * Δ) ^ k / (k ! : ℝ)) := by
    intro k
    have h0 : 0 < c + k := by positivity
    rw [Real.Gamma_add_one h0.ne', mul_div_assoc, div_self (Real.Gamma_pos_of_pos h0).ne', mul_one]
    ring
  have hs1 : HasSum (fun k : ℕ => (-1) ^ k * ((c : ℝ) * ((2 * π * Δ) ^ k / (k ! : ℝ)) +
        (k : ℝ) * ((2 * π * Δ) ^ k / (k ! : ℝ)))) ((c - 2 * π * Δ) * Real.exp (-(2 * π * Δ))) := by
    have h1 := (hasSum_neg_pow_div_factorial (2 * π * Δ)).mul_left c
    have h2 := hasSum_nat_mul_pow_div_factorial (-(2 * π * Δ))
    have h3 := h1.add h2
    have e : (c - 2 * π * Δ) * Real.exp (-(2 * π * Δ)) =
        c * Real.exp (-(2 * π * Δ)) + -(2 * π * Δ) * Real.exp (-(2 * π * Δ)) := by ring
    rw [e]
    convert h3 using 1
    funext k
    rw [neg_pow (2 * π * Δ) k]
    ring
  have hsum : Summable fun k : ℕ => (2 * π * Δ) ^ k / (k ! : ℝ) *
      (Real.Gamma (c + k + 1) / Real.Gamma (c + k)) := by
    simp_rw [hT]
    exact ((Real.summable_pow_div_factorial _).mul_left c).add
      (( hasSum_nat_mul_pow_div_factorial (2 * π * Δ)).summable)
  have h := integral_hankel_rpow_exp hc zero_le_one hΔ hsum
  simp only [Real.rpow_one] at h
  rw [h]
  simp_rw [hT]
  rw [hs1.tsum_eq]
  field_simp



lemma integrableOn_exp_rho0 {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun s : ℝ => Real.exp (-(2 * π * s)) * hankelRho0 c s) (Ioi 0) := by
  refine (integrableOn_rpow_exp_rho0 hc le_rfl).congr_fun (fun s _ => ?_) measurableSet_Ioi
  simp

lemma integrableOn_linear_exp_rho0 {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun s : ℝ => s * Real.exp (-(2 * π * s)) * hankelRho0 c s) (Ioi 0) := by
  refine (integrableOn_rpow_exp_rho0 hc zero_le_one).congr_fun (fun s _ => ?_) measurableSet_Ioi
  simp

end FormalResearch.SignUncertainty
