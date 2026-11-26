module

public import FormalResearch.SignUncertainty.UctE0Remainder
public import FormalResearch.SignUncertainty.UctFourierTwice
public import FormalResearch.SignUncertainty.UctBumpMain

/-!
# Two integrations by parts for `ε · Φ` against `e^{iωτ}` (F2a, `uct:bump-weighted` far band)

`fourier_twice`: if `f' = g₁`, `g₁' = g₂` everywhere, `g₁, g₂` continuous and `f, g₁, g₂` integrable, then `‖∫ f e^{iωτ}‖ ≤ (∫‖g₂‖)/ω²`.
`eps_ibp_bound`: for the remainder `ε` of `E0_poly_remainder` (`|ε^{(i)}| ≤ C_ε h^{4-i}(1+|τ/h|)^p`) and a transform `Φ₀` with `Φ₀' = -(ic)Φ₁`, `Φ₁' = -(ic)Φ₂`
and `|Φ_j| ≤ D_j (1 + a|τ|/h)^{-(p+2)}`, `c = h⁻²`:
`‖∫ ε Φ₀ e^{icLτ}‖ ≤ C_ε U^p (I₂/a) h⁵ L⁻² (h² D₀ + 2 h D₁ + D₂)` (`U = max 1 (1/a)`).

Class: proved, no hypotheses.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

lemma fourier_twice {f g1 g2 : ℝ → ℂ} (hf : ∀ τ, HasDerivAt f (g1 τ) τ) (hg1 : ∀ τ, HasDerivAt g1 (g2 τ) τ)
    (hc1 : Continuous g1) (hc2 : Continuous g2) (i0 : Integrable f) (i1 : Integrable g1) (i2 : Integrable g2)
    {ω : ℝ} (hω : ω ≠ 0) :
    ‖∫ τ : ℝ, f τ * Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ))‖ ≤ (∫ τ : ℝ, ‖g2 τ‖) / ω ^ 2 := by
  have hd0 : deriv f = g1 := funext fun τ => (hf τ).deriv
  have hd1 : deriv g1 = g2 := funext fun τ => (hg1 τ).deriv
  have s1 := ibp_line (g := f) (fun τ => (hf τ).differentiableAt) (by rw [hd0]; exact hc1) i0 (by rw [hd0]; exact i1) hω
  have s2 := ibp_line (g := g1) (fun τ => (hg1 τ).differentiableAt) (by rw [hd1]; exact hc2) i1 (by rw [hd1]; exact i2) hω
  rw [hd0] at s1
  rw [hd1] at s2
  rw [s1, s2]
  have hn : ‖(1 / (Complex.I * (ω : ℂ)))‖ = 1 / |ω| := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [← mul_assoc, norm_mul, norm_mul, norm_neg, hn]
  have hint : ‖∫ τ : ℝ, g2 τ * Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ))‖ ≤ ∫ τ : ℝ, ‖g2 τ‖ := by
    refine norm_integral_le_of_norm_le i2.norm (ae_of_all _ fun τ => ?_)
    rw [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
  have hω2 : 0 < |ω| := abs_pos.mpr hω
  calc 1 / |ω| * (1 / |ω|) * ‖∫ τ : ℝ, g2 τ * Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ))‖
      ≤ 1 / |ω| * (1 / |ω|) * ∫ τ : ℝ, ‖g2 τ‖ := by gcongr
    _ = (∫ τ : ℝ, ‖g2 τ‖) / ω ^ 2 := by
        rw [← sq_abs ω]; field_simp

lemma pow_le_scaled {a : ℝ} (ha : 0 < a) (t : ℝ) (ht : 0 ≤ t) (p : ℕ) :
    (1 + t) ^ p ≤ (max 1 (1 / a)) ^ p * (1 + a * t) ^ p := by
  rw [← mul_pow]
  refine pow_le_pow_left₀ (by linarith) ?_ p
  have hU : 1 ≤ max 1 (1 / a) := le_max_left _ _
  have hU2 : 1 / a ≤ max 1 (1 / a) := le_max_right _ _
  have h1 : t ≤ max 1 (1 / a) * (a * t) := by
    have : 1 ≤ max 1 (1 / a) * a := by
      have := mul_le_mul_of_nonneg_right hU2 ha.le
      rw [one_div, inv_mul_cancel₀ ha.ne'] at this
      simpa [one_div] using this
    nlinarith
  nlinarith

lemma eps_ibp_bound {ε Φ0 Φ1 Φ2 : ℝ → ℂ} {h c L Cε D0 D1 D2 a : ℝ} {p : ℕ}
    (hh : 0 < h) (hc : c = (h ^ 2)⁻¹) (ha : 0 < a) (hL : 0 < L) (hCε : 0 ≤ Cε)
    (_hD0 : 0 ≤ D0) (_hD1 : 0 ≤ D1) (_hD2 : 0 ≤ D2)
    (hε : ContDiff ℝ 2 ε)
    (hε0 : ∀ τ, ‖ε τ‖ ≤ Cε * h ^ 4 * (1 + |τ / h|) ^ p)
    (hε1 : ∀ τ, ‖deriv ε τ‖ ≤ Cε * h ^ 3 * (1 + |τ / h|) ^ p)
    (hε2 : ∀ τ, ‖deriv (deriv ε) τ‖ ≤ Cε * h ^ 2 * (1 + |τ / h|) ^ p)
    (hΦ0 : ∀ τ, HasDerivAt Φ0 (-((c : ℂ) * Complex.I) * Φ1 τ) τ)
    (hΦ1 : ∀ τ, HasDerivAt Φ1 (-((c : ℂ) * Complex.I) * Φ2 τ) τ)
    (hΦ2c : Continuous Φ2)
    (hb0 : ∀ τ, ‖Φ0 τ‖ ≤ D0 / (1 + a * |τ / h|) ^ (p + 2))
    (hb1 : ∀ τ, ‖Φ1 τ‖ ≤ D1 / (1 + a * |τ / h|) ^ (p + 2))
    (hb2 : ∀ τ, ‖Φ2 τ‖ ≤ D2 / (1 + a * |τ / h|) ^ (p + 2)) :
    Integrable (fun τ : ℝ => ε τ * Φ0 τ * Complex.exp (Complex.I * ((c * L * τ : ℝ) : ℂ))) ∧
    ‖∫ τ : ℝ, ε τ * Φ0 τ * Complex.exp (Complex.I * ((c * L * τ : ℝ) : ℂ))‖ ≤
      Cε * (max 1 (1 / a)) ^ p * ((∫ x : ℝ, ((1 + |x|) ^ 2)⁻¹) / (a / h)) * (h ^ 4 / L ^ 2) *
        (h ^ 2 * D0 + 2 * h * D1 + D2) := by
  set U : ℝ := max 1 (1 / a) with hU
  have hU0 : 0 < U := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hc0 : 0 < c := by rw [hc]; positivity
  have hah : 0 < a / h := div_pos ha hh
  obtain ⟨hGi, hGv⟩ := integral_inv_sq_scaled hah
  set G : ℝ → ℝ := fun τ => ((1 + a / h * |τ|) ^ 2)⁻¹ with hG
  have hG0 : ∀ τ, 0 ≤ G τ := fun τ => by simp only [hG]; positivity
  have hY : ∀ τ : ℝ, a * |τ / h| = a / h * |τ| := fun τ => by
    rw [abs_div, abs_of_pos hh]; field_simp
  -- pointwise transfer
  have key : ∀ (τ : ℝ) (D : ℝ) (Φ : ℝ → ℂ), ‖Φ τ‖ ≤ D / (1 + a * |τ / h|) ^ (p + 2) →
      (1 + |τ / h|) ^ p * ‖Φ τ‖ ≤ D * U ^ p * G τ := by
    intro τ D Φ hb
    have hY0 : 0 < 1 + a * |τ / h| := by positivity
    have h1 := pow_le_scaled ha |τ / h| (abs_nonneg _) p
    calc (1 + |τ / h|) ^ p * ‖Φ τ‖ ≤ (U ^ p * (1 + a * |τ / h|) ^ p) * (D / (1 + a * |τ / h|) ^ (p + 2)) :=
          mul_le_mul h1 hb (norm_nonneg _) (by positivity)
      _ = D * U ^ p * G τ := by
          simp only [hG, ← hY τ]
          field_simp
          ring
  have hεc : Continuous ε := hε.continuous
  have hε1c : Continuous (deriv ε) := (cd1_of_cd2 hε).continuous
  have hε2c : Continuous (deriv (deriv ε)) := (cd1_of_cd2 hε).continuous_deriv le_rfl
  have hεd : ∀ τ, HasDerivAt ε (deriv ε τ) τ := fun τ => (hε.differentiable (by norm_num) τ).hasDerivAt
  have hεd1 : ∀ τ, HasDerivAt (deriv ε) (deriv (deriv ε) τ) τ :=
    fun τ => ((cd1_of_cd2 hε).differentiable (by norm_num) τ).hasDerivAt
  have hΦ0c : Continuous Φ0 := continuous_iff_continuousAt.mpr fun τ => (hΦ0 τ).continuousAt
  have hΦ1c : Continuous Φ1 := continuous_iff_continuousAt.mpr fun τ => (hΦ1 τ).continuousAt
  set cI : ℂ := -((c : ℂ) * Complex.I) with hcI
  set f : ℝ → ℂ := fun τ => ε τ * Φ0 τ with hf
  set g1 : ℝ → ℂ := fun τ => deriv ε τ * Φ0 τ + ε τ * (cI * Φ1 τ) with hg1
  set g2 : ℝ → ℂ := fun τ => (deriv (deriv ε) τ * Φ0 τ + deriv ε τ * (cI * Φ1 τ)) +
      (deriv ε τ * (cI * Φ1 τ) + ε τ * (cI * (cI * Φ2 τ))) with hg2
  have hfd : ∀ τ, HasDerivAt f (g1 τ) τ := fun τ => (hεd τ).mul (hΦ0 τ)
  have hg1d : ∀ τ, HasDerivAt g1 (g2 τ) τ := fun τ =>
    ((hεd1 τ).mul (hΦ0 τ)).add ((hεd τ).mul (((hΦ1 τ).const_mul cI).congr_deriv (by rw [hcI])))
  have hg1c : Continuous g1 := by
    simp only [hg1]
    exact (hε1c.mul hΦ0c).add (hεc.mul (continuous_const.mul hΦ1c))
  have hg2c : Continuous g2 := by
    simp only [hg2]
    exact ((hε2c.mul hΦ0c).add (hε1c.mul (continuous_const.mul hΦ1c))).add
      ((hε1c.mul (continuous_const.mul hΦ1c)).add (hεc.mul (continuous_const.mul (continuous_const.mul hΦ2c))))
  have hcn : ‖cI‖ = c := by
    rw [hcI, norm_neg, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_of_nonneg hc0.le]
  -- pointwise bounds by multiples of `G`
  have hcc : c * h ^ 2 = 1 := by rw [hc]; field_simp
  have bf : ∀ τ, ‖f τ‖ ≤ (Cε * h ^ 4 * D0 * U ^ p) * G τ := by
    intro τ
    simp only [hf]; rw [norm_mul]
    have := key τ D0 Φ0 (hb0 τ)
    calc ‖ε τ‖ * ‖Φ0 τ‖ ≤ (Cε * h ^ 4 * (1 + |τ / h|) ^ p) * ‖Φ0 τ‖ :=
          mul_le_mul_of_nonneg_right (hε0 τ) (norm_nonneg _)
      _ = Cε * h ^ 4 * ((1 + |τ / h|) ^ p * ‖Φ0 τ‖) := by ring
      _ ≤ Cε * h ^ 4 * (D0 * U ^ p * G τ) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  have bg1 : ∀ τ, ‖g1 τ‖ ≤ (Cε * U ^ p * (h ^ 3 * D0 + h ^ 2 * D1)) * G τ := by
    intro τ
    simp only [hg1]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_mul, hcn]
    have k0 := key τ D0 Φ0 (hb0 τ)
    have k1 := key τ D1 Φ1 (hb1 τ)
    have t1 : ‖deriv ε τ‖ * ‖Φ0 τ‖ ≤ Cε * h ^ 3 * (D0 * U ^ p * G τ) :=
      calc _ ≤ (Cε * h ^ 3 * (1 + |τ / h|) ^ p) * ‖Φ0 τ‖ := mul_le_mul_of_nonneg_right (hε1 τ) (norm_nonneg _)
        _ = Cε * h ^ 3 * ((1 + |τ / h|) ^ p * ‖Φ0 τ‖) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left k0 (by positivity)
    have t2 : ‖ε τ‖ * (c * ‖Φ1 τ‖) ≤ Cε * h ^ 2 * (D1 * U ^ p * G τ) := by
      calc ‖ε τ‖ * (c * ‖Φ1 τ‖) ≤ (Cε * h ^ 4 * (1 + |τ / h|) ^ p) * (c * ‖Φ1 τ‖) :=
            mul_le_mul_of_nonneg_right (hε0 τ) (by positivity)
        _ = Cε * (c * h ^ 2) * h ^ 2 * ((1 + |τ / h|) ^ p * ‖Φ1 τ‖) := by ring
        _ = Cε * h ^ 2 * ((1 + |τ / h|) ^ p * ‖Φ1 τ‖) := by rw [hcc]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left k1 (by positivity)
    nlinarith [t1, t2]
  have bg2 : ∀ τ, ‖g2 τ‖ ≤ (Cε * U ^ p * (h ^ 2 * D0 + 2 * h * D1 + D2)) * G τ := by
    intro τ
    simp only [hg2]
    have k0 := key τ D0 Φ0 (hb0 τ)
    have k1 := key τ D1 Φ1 (hb1 τ)
    have k2 := key τ D2 Φ2 (hb2 τ)
    have t1 : ‖deriv (deriv ε) τ‖ * ‖Φ0 τ‖ ≤ Cε * h ^ 2 * (D0 * U ^ p * G τ) :=
      calc _ ≤ (Cε * h ^ 2 * (1 + |τ / h|) ^ p) * ‖Φ0 τ‖ := mul_le_mul_of_nonneg_right (hε2 τ) (norm_nonneg _)
        _ = Cε * h ^ 2 * ((1 + |τ / h|) ^ p * ‖Φ0 τ‖) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left k0 (by positivity)
    have t2 : ‖deriv ε τ‖ * (c * ‖Φ1 τ‖) ≤ Cε * h * (D1 * U ^ p * G τ) := by
      calc ‖deriv ε τ‖ * (c * ‖Φ1 τ‖) ≤ (Cε * h ^ 3 * (1 + |τ / h|) ^ p) * (c * ‖Φ1 τ‖) :=
            mul_le_mul_of_nonneg_right (hε1 τ) (by positivity)
        _ = Cε * h * (c * h ^ 2) * ((1 + |τ / h|) ^ p * ‖Φ1 τ‖) := by ring
        _ = Cε * h * ((1 + |τ / h|) ^ p * ‖Φ1 τ‖) := by rw [hcc]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left k1 (by positivity)
    have t3 : ‖ε τ‖ * (c * (c * ‖Φ2 τ‖)) ≤ Cε * (D2 * U ^ p * G τ) := by
      calc ‖ε τ‖ * (c * (c * ‖Φ2 τ‖)) ≤ (Cε * h ^ 4 * (1 + |τ / h|) ^ p) * (c * (c * ‖Φ2 τ‖)) :=
            mul_le_mul_of_nonneg_right (hε0 τ) (by positivity)
        _ = Cε * (c * h ^ 2) * (c * h ^ 2) * ((1 + |τ / h|) ^ p * ‖Φ2 τ‖) := by ring
        _ = Cε * ((1 + |τ / h|) ^ p * ‖Φ2 τ‖) := by rw [hcc]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left k2 hCε
    refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) (norm_add_le _ _)).trans ?_)
    simp only [norm_mul, hcn]
    nlinarith [t1, t2, t3]
  have mkint : ∀ (F : ℝ → ℂ) (K : ℝ), Continuous F → (∀ τ, ‖F τ‖ ≤ K * G τ) → Integrable F := fun F K hFc hFb =>
    (hGi.const_mul K).mono' hFc.aestronglyMeasurable (ae_of_all _ hFb)
  have hfc : Continuous f := hεc.mul hΦ0c
  have i0 := mkint f _ hfc bf
  have i1 := mkint g1 _ hg1c bg1
  have i2 := mkint g2 _ hg2c bg2
  have hmain := fourier_twice hfd hg1d hg1c hg2c i0 i1 i2 (ω := c * L) (mul_ne_zero hc0.ne' hL.ne')
  have hint : ∫ τ : ℝ, ‖g2 τ‖ ≤ (Cε * U ^ p * (h ^ 2 * D0 + 2 * h * D1 + D2)) * ((∫ x : ℝ, ((1 + |x|) ^ 2)⁻¹) / (a / h)) := by
    rw [← hGv, ← integral_const_mul]
    exact integral_mono i2.norm (hGi.const_mul _) bg2
  have hcL : (c * L) ^ 2 = L ^ 2 / h ^ 4 := by rw [hc]; field_simp
  have hecont : Continuous fun τ : ℝ => Complex.exp (Complex.I * ((c * L * τ : ℝ) : ℂ)) := by fun_prop
  refine ⟨i0.mul_bdd hecont.aestronglyMeasurable (c := 1)
      (ae_of_all _ fun τ => (Complex.norm_exp_I_mul_ofReal _).le), ?_⟩
  calc ‖∫ τ : ℝ, ε τ * Φ0 τ * Complex.exp (Complex.I * ((c * L * τ : ℝ) : ℂ))‖
      ≤ (∫ τ : ℝ, ‖g2 τ‖) / (c * L) ^ 2 := hmain
    _ ≤ ((Cε * U ^ p * (h ^ 2 * D0 + 2 * h * D1 + D2)) * ((∫ x : ℝ, ((1 + |x|) ^ 2)⁻¹) / (a / h))) / (c * L) ^ 2 := by
        gcongr
    _ = _ := by
        rw [hcL]; field_simp

/-- info: 'FormalResearch.SignUncertainty.eps_ibp_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eps_ibp_bound

end FormalResearch.SignUncertainty
