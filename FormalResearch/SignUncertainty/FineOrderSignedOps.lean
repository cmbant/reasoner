module

public import FormalResearch.SignUncertainty.FineOrderSignedCore

/-!
# Contour operators, integration-by-parts, and `B3` helpers for `fs:half-cubic`

Helper lemmas for `fsOpCh` linearity, `Chain3.B3` moment bounds, contour integration by parts,
and exponential ray-tail bounds used by `FineOrderSigned`.
-/

@[expose] public section

open Complex MeasureTheory Metric Set Filter Topology intervalIntegral
open scoped Real

namespace FormalResearch.SignUncertainty.FineOrderSigned

open FormalResearch.SignUncertainty CtSd

/-- Congruence of `ch.intE U` for amplitudes agreeing on `ball 0 R₀ ∩ {Re ≥ 0} \ {0}`. -/
lemma chain3_intE_congr_ne_zero {R₀ : ℝ} {p : ℂ} (ch : Chain3 R₀ p) (U : ℝ)
    {f₁ f₂ : ℂ → ℂ} {A B C : ℝ} (hb : ch.B3 f₂ A B C)
    (hc₁ : ∀ z ∈ ball (0 : ℂ) R₀, 0 ≤ z.re → z ≠ 0 → ContinuousAt f₁ z)
    (hc₂ : ∀ z ∈ ball (0 : ℂ) R₀, 0 ≤ z.re → z ≠ 0 → ContinuousAt f₂ z)
    (heq : ∀ z ∈ ball (0 : ℂ) R₀, 0 ≤ z.re → z ≠ 0 → f₁ z = f₂ z) :
    ch.intE U f₁ = ch.intE U f₂ := by
  have hdiff : ch.B3 (fun w => f₁ w - f₂ w) 0 0 0 :=
    Chain3.B3.of_pointwise ch le_rfl le_rfl le_rfl
      (fun z hz hre hz0 => (hc₁ z hz hre hz0).sub (hc₂ z hz hre hz0))
      (fun z hz hre hz0 => by simp [heq z hz hre hz0])
  have hn : ‖ch.intE U (fun w => f₁ w - f₂ w)‖ ≤ 0 := by
    have := hdiff.norm_intE_le (U := U); linarith only [this]
  have h0 : ch.intE U (fun w => f₁ w - f₂ w) = 0 := norm_le_zero_iff.1 hn
  have hsum : f₁ = fun w => f₂ w + (f₁ w - f₂ w) := funext fun w => by ring
  rw [hsum, hb.intE_add hdiff, h0, add_zero]

/-- Phase integration by parts for `fsOpCh`: `L_U[G(w) (κ U + w^2)] = L_U[i (G(w)/(2w) + G'(w))] + O(√R e^{-R^3/12})`. -/
lemma fs_ibp_eval {R R₀ U : ℝ} (hR1 : 1 ≤ R) (hUR : kap * |U| ≤ R ^ 2 / 16)
    (ch : Chain3 R₀ ((R : ℂ) * d6)) {G G' : ℂ → ℂ} {KG KG' : ℝ}
    (hKG : 0 ≤ KG) (hKG' : 0 ≤ KG')
    (hG : ∀ w ∈ ball (0 : ℂ) R₀, HasDerivAt G (G' w) w)
    (hG' : ContinuousOn G' (ball 0 R₀))
    (hGb : ∀ w ∈ ball (0 : ℂ) R₀, ‖G w‖ ≤ KG)
    (hGb' : ∀ w ∈ ball (0 : ℂ) R₀, ‖G' w‖ ≤ KG') :
    |fsOpCh ch U (fun w => G w * ((kap : ℂ) * U + w ^ 2)) -
        fsOpCh ch U (fun w => Complex.I * (G w / (2 * w) + G' w))| ≤
      (1 / √π) * Real.sqrt R * KG * Real.exp (-(R ^ 3 / 12)) := by
  have hibp := Chain3.ibp ch U hKG hKG' hG hG' hGb hGb'
  have hmul : ch.intE U (fun w => csr w * (G w * ((kap : ℂ) * U + w ^ 2))) =
      ch.intE U (fun w => csr w * (Complex.I * (G w / (2 * w) + G' w))) -
        Complex.I * (csr ((R : ℂ) * d6) * G ((R : ℂ) * d6) *
          Complex.exp (Complex.I * PhU U ((R : ℂ) * d6))) := by
    have h1 : ch.intE U (fun w => csr w * (G w * ((kap : ℂ) * U + w ^ 2))) =
        ch.intE U (fun w => csr w * G w * ((kap : ℂ) * U + w ^ 2)) := by
      congr 1; ext w; ring
    have h2 : ch.intE U (fun w => csr w * (Complex.I * (G w / (2 * w) + G' w))) =
        Complex.I * ch.intE U (fun w => csr w / (2 * w) * G w + csr w * G' w) := by
      rw [← Chain3.intE_const_mul]
      congr 1; ext w; ring
    rw [h1, h2]
    have h3 : Complex.I * (Complex.I * ch.intE U (fun w => csr w * G w * ((kap : ℂ) * U + w ^ 2))) =
        -ch.intE U (fun w => csr w * G w * ((kap : ℂ) * U + w ^ 2)) := by
      rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
    have h4 := congrArg (Complex.I * ·) hibp
    rw [mul_add, h3] at h4
    linear_combination -h4
  have hRR0 : (R : ℂ) * d6 ∈ ball (0 : ℂ) R₀ := by
    have hstop := ch.ok3.2.1 ch.q3.b ⟨ch.ok3.1, le_rfl⟩
    rw [← show ch.q3.stop = (R : ℂ) * d6 from ch.h3]; exact hstop.1
  have hpi : 0 < √π := Real.sqrt_pos.2 Real.pi_pos
  have hnorm_p : ‖(R : ℂ) * d6‖ = R := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith only [hR1]), norm_d6, mul_one]
  have hnorm_csr : ‖csr ((R : ℂ) * d6)‖ ≤ Real.sqrt R := by
    rw [norm_csr, hnorm_p, Real.sqrt_eq_rpow]
  have hnorm_exp : ‖Complex.exp (Complex.I * PhU U ((R : ℂ) * d6))‖ ≤ Real.exp (-(R ^ 3 / 12)) := by
    rw [norm_exp_I_mul]
    exact Real.exp_le_exp.2 (by linarith only [fs_end_im hR1 hUR])
  have hGp : ‖G ((R : ℂ) * d6)‖ ≤ KG := hGb _ hRR0
  unfold fsOpCh
  rw [hmul, mul_sub, Complex.sub_re, mul_sub, sub_sub_cancel_left, abs_neg,
    abs_mul, abs_neg, abs_of_pos (one_div_pos.2 hpi)]
  calc (1 / √π) * |(Complex.exp (Complex.I * (π / 4 : ℝ)) *
        (Complex.I * (csr ((R : ℂ) * d6) * G ((R : ℂ) * d6) *
          Complex.exp (Complex.I * PhU U ((R : ℂ) * d6))))).re|
      ≤ (1 / √π) * ‖Complex.exp (Complex.I * (π / 4 : ℝ)) *
          (Complex.I * (csr ((R : ℂ) * d6) * G ((R : ℂ) * d6) *
            Complex.exp (Complex.I * PhU U ((R : ℂ) * d6))))‖ :=
          mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by positivity)
    _ ≤ (1 / √π) * (Real.sqrt R * KG * Real.exp (-(R ^ 3 / 12))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [norm_mul, mul_comm Complex.I _, Complex.norm_exp_ofReal_mul_I, one_mul,
            norm_mul, Complex.norm_I, one_mul, norm_mul, norm_mul]
          exact mul_le_mul (mul_le_mul hnorm_csr hGp (norm_nonneg _) (Real.sqrt_nonneg _))
            hnorm_exp (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hKG)
    _ = (1 / √π) * Real.sqrt R * KG * Real.exp (-(R ^ 3 / 12)) := by ring

/-- Polynomial bound on `exp(-R^3 / 12)` for `1 ≤ R`. -/
lemma exp_cubic_tail_bound {R : ℝ} (hR : 1 ≤ R) :
    Real.sqrt R * Real.exp (-(R ^ 3 / 12)) ≤ 288 / R ^ 5 ∧
      Real.exp (-(R ^ 3 / 12)) ≤ 288 / R ^ 6 := by
  have hR0 : 0 < R := by linarith only [hR]
  have hx : 0 ≤ R ^ 3 / 12 := by positivity
  have hexp : (R ^ 3 / 12) ^ 2 / 2 ≤ Real.exp (R ^ 3 / 12) := by
    have := Real.pow_div_factorial_le_exp (R ^ 3 / 12) hx 2
    simpa [Nat.factorial] using this
  have hpos : 0 < (R ^ 3 / 12) ^ 2 / 2 := by positivity
  have h2 : Real.exp (-(R ^ 3 / 12)) ≤ 288 / R ^ 6 := by
    rw [Real.exp_neg]
    calc (Real.exp (R ^ 3 / 12))⁻¹ ≤ ((R ^ 3 / 12) ^ 2 / 2)⁻¹ := inv_anti₀ hpos hexp
      _ = 288 / R ^ 6 := by ring
  have hsq : Real.sqrt R ≤ R := by
    calc Real.sqrt R ≤ Real.sqrt (R ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = R := Real.sqrt_sq hR0.le
  have h1 : Real.sqrt R * Real.exp (-(R ^ 3 / 12)) ≤ 288 / R ^ 5 := by
    calc Real.sqrt R * Real.exp (-(R ^ 3 / 12))
        ≤ R * (288 / R ^ 6) := mul_le_mul hsq h2 (Real.exp_pos _).le hR0.le
      _ = 288 / R ^ 5 := by field_simp [hR0.ne']
  exact ⟨h1, h2⟩

lemma fsOpCh_real_mul {R₀ : ℝ} {p : ℂ} (ch : Chain3 R₀ p) (U : ℝ)
    {k : ℂ} (hk : k.im = 0) (g : ℂ → ℂ) :
    fsOpCh ch U (fun w => k * g w) = k.re * fsOpCh ch U g := by
  have hkeq : k = (k.re : ℂ) := Complex.ext rfl hk
  unfold fsOpCh
  have h1 : ch.intE U (fun w => csr w * (k * g w)) = k * ch.intE U (fun w => csr w * g w) := by
    rw [← Chain3.intE_const_mul]; congr 1; ext w; ring
  rw [h1, ← mul_assoc, mul_comm (Complex.exp _) k, mul_assoc, hkeq, Complex.re_ofReal_mul,
    Complex.ofReal_re]
  ring

lemma fsOpCh_add {R₀ : ℝ} {p : ℂ} (ch : Chain3 R₀ p) (U : ℝ)
    {f₁ f₂ : ℂ → ℂ} {A₁ B₁ C₁ A₂ B₂ C₂ : ℝ}
    (hb₁ : ch.B3 (fun w => csr w * f₁ w) A₁ B₁ C₁)
    (hb₂ : ch.B3 (fun w => csr w * f₂ w) A₂ B₂ C₂) :
    fsOpCh ch U (fun w => f₁ w + f₂ w) = fsOpCh ch U f₁ + fsOpCh ch U f₂ := by
  unfold fsOpCh
  have h1 : (fun w => csr w * (f₁ w + f₂ w)) = fun w => csr w * f₁ w + csr w * f₂ w :=
    funext fun w => mul_add _ _ _
  rw [h1, hb₁.intE_add hb₂, mul_add, Complex.add_re]
  ring

lemma b3_csr_bounded {R₀ : ℝ} {p : ℂ} (ch : Chain3 R₀ p) {f : ℂ → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hc : ContinuousOn f (ball 0 R₀)) (hbd : ∀ w ∈ ball (0 : ℂ) R₀, ‖f w‖ ≤ M) :
    ch.B3 (fun w => csr w * f w) 0 M 0 := by
  refine Chain3.B3.of_pointwise ch le_rfl hM le_rfl ?_ ?_
  · intro z hz hre _
    exact (continuousAt_csr (Or.inl hre)).mul (hc.continuousAt (isOpen_ball.mem_nhds hz))
  · intro z hz _ _
    rw [norm_mul, norm_csr, Real.sqrt_eq_rpow, zero_mul, zero_mul, zero_add, add_zero, mul_comm]
    exact mul_le_mul_of_nonneg_right (hbd z hz) (Real.rpow_nonneg (norm_nonneg z) _)

lemma b3_csr_iw {R₀ : ℝ} {p : ℂ} (ch : Chain3 R₀ p) :
    ch.B3 (fun w => csr w * (Complex.I * w)) 0 0 1 := by
  refine Chain3.B3.of_pointwise ch le_rfl le_rfl zero_le_one ?_ ?_
  · intro z _ hre _
    exact (continuousAt_csr (Or.inl hre)).mul (continuous_const.mul continuous_id).continuousAt
  · intro z _ _ hz0
    have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz0
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, norm_csr, Real.sqrt_eq_rpow,
      zero_mul, zero_mul, zero_add, zero_add, one_mul]
    refine le_of_eq ?_
    calc ‖z‖ ^ (1 / 2 : ℝ) * ‖z‖ = ‖z‖ ^ (1 / 2 : ℝ) * ‖z‖ ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = ‖z‖ ^ (3 / 2 : ℝ) := by rw [← Real.rpow_add hzn]; norm_num

lemma b3_csr_idiv {R₀ : ℝ} {p : ℂ} (ch : Chain3 R₀ p) :
    ch.B3 (fun w => csr w * (Complex.I / w)) 1 0 0 := by
  refine Chain3.B3.of_pointwise ch zero_le_one le_rfl le_rfl ?_ ?_
  · intro z _ hre hz0
    exact (continuousAt_csr (Or.inl hre)).mul (continuousAt_const.div continuousAt_id hz0)
  · intro z _ _ hz0
    have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz0
    rw [norm_mul, norm_div, Complex.norm_I, norm_csr, Real.sqrt_eq_rpow, one_mul,
      zero_mul, zero_mul, add_zero, add_zero, one_div ‖z‖]
    refine le_of_eq ?_
    calc ‖z‖ ^ (1 / 2 : ℝ) * ‖z‖⁻¹ = ‖z‖ ^ (1 / 2 : ℝ) * ‖z‖ ^ (-1 : ℝ) := by
          rw [Real.rpow_neg_one]
      _ = ‖z‖ ^ (-(1 / 2 : ℝ)) := by rw [← Real.rpow_add hzn]; norm_num

private lemma chain3_mom_nonneg {R₀ : ℝ} {p : ℂ} (ch : Chain3 R₀ p) (U α : ℝ) :
    0 ≤ ch.mom U α := by
  have hp : ∀ q : Piece, q.a ≤ q.b →
      0 ≤ ∫ t in q.a..q.b, ‖q.z0 + (t : ℂ) * q.d‖ ^ α *
        Real.exp (-(PhU U (q.z0 + (t : ℂ) * q.d)).im) * ‖q.d‖ := fun q hq =>
    intervalIntegral.integral_nonneg hq fun t _ => by positivity
  unfold Chain3.mom
  exact add_nonneg (add_nonneg (hp ch.q1 ch.ok1.1) (hp ch.q2 ch.ok2.1)) (hp ch.q3 ch.ok3.1)

/-- Uniform IBP bound on `L_u[(Efn(λ^2 w^2) + i λ w Ofn(λ^2 w^2)) (κ u + w^2)]` via `fs_ibp_eval`
and `MomOK`. Used for both the second IBP in `(fs:principal)` and the first IBP in `(fs:aux)`. -/
lemma fs_ibp_shift_bound {R R₀ lam u s₁ Rs M_E M_O M_ED M_OD Cm : ℝ}
    (hR1 : 1 ≤ R) (hUR : kap * |u| ≤ R ^ 2 / 16) (hl0 : 0 < lam) (hl1 : lam ≤ 1)
    (hs₁ : 0 < s₁) (hRs : 0 ≤ Rs) (hRdef : R = s₁ / lam) (hlamR₀ : lam * R₀ = Rs)
    (ch : Chain3 R₀ ((R : ℂ) * d6)) (hmom : MomOK Cm u ch) (hCm : 0 ≤ Cm)
    {Efn Ofn : ℂ → ℂ} {r_sup r_sub : ℝ} (hsub_lt : r_sub < r_sup) (hRs_sub : Rs ^ 2 ≤ r_sub)
    (hE_d : DifferentiableOn ℂ Efn (ball 0 r_sup)) (hO_d : DifferentiableOn ℂ Ofn (ball 0 r_sup))
    (hE_bd : ∀ q ∈ ball (0 : ℂ) r_sup, ‖Efn q‖ ≤ M_E)
    (hO_bd : ∀ q ∈ ball (0 : ℂ) r_sup, ‖Ofn q‖ ≤ M_O)
    (hED_bd : ∀ q ∈ ball (0 : ℂ) r_sub, ‖deriv Efn q‖ ≤ M_ED)
    (hOD_bd : ∀ q ∈ ball (0 : ℂ) r_sub, ‖deriv Ofn q‖ ≤ M_OD)
    (hME : 0 ≤ M_E) (hMO : 0 ≤ M_O) (hMED : 0 ≤ M_ED) (hMOD : 0 ≤ M_OD) :
    |fsOpCh ch u (fun w => (Efn (((lam : ℂ) * w) ^ 2) +
        Complex.I * ((lam : ℂ) * w) * Ofn (((lam : ℂ) * w) ^ 2)) * ((kap : ℂ) * u + w ^ 2))| ≤
      (1 / √π) * ((M_E + Rs * M_O) * (288 / s₁ ^ 5) * lam ^ 5 +
        ((M_E / 2) * Cm + (3 / 2 * M_O + 2 * Rs ^ 2 * M_OD) * Cm +
          (2 * M_ED) * (Cm * Real.sqrt (1 + s₁ ^ 2 / 16)))) := by
  have hR0 : 0 < R := by linarith only [hR1]
  have hpi : 0 < √π := Real.sqrt_pos.2 Real.pi_pos
  have hq_sub : ∀ w ∈ ball (0 : ℂ) R₀, ((lam : ℂ) * w) ^ 2 ∈ ball (0 : ℂ) r_sub ∧
      ((lam : ℂ) * w) ^ 2 ∈ ball (0 : ℂ) r_sup := fun w hw => by
    have hlw : ‖(lam : ℂ) * w‖ < Rs := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hl0.le]
      calc lam * ‖w‖ < lam * R₀ := mul_lt_mul_of_pos_left (mem_ball_zero_iff.1 hw) hl0
        _ = Rs := hlamR₀
    have hsq : ‖((lam : ℂ) * w) ^ 2‖ < Rs ^ 2 := by
      rw [norm_pow]; nlinarith [norm_nonneg ((lam : ℂ) * w), hlw, hRs]
    have h1 : ((lam : ℂ) * w) ^ 2 ∈ ball (0 : ℂ) r_sub := mem_ball_zero_iff.2 (hsq.trans_le hRs_sub)
    exact ⟨h1, ball_subset_ball hsub_lt.le h1⟩
  set G : ℂ → ℂ := fun w => Efn (((lam : ℂ) * w) ^ 2) +
    Complex.I * ((lam : ℂ) * w) * Ofn (((lam : ℂ) * w) ^ 2)
  set G' : ℂ → ℂ := fun w =>
    2 * (lam : ℂ) ^ 2 * w * deriv Efn (((lam : ℂ) * w) ^ 2) +
    Complex.I * (lam : ℂ) * Ofn (((lam : ℂ) * w) ^ 2) +
    Complex.I * 2 * (lam : ℂ) ^ 3 * w ^ 2 * deriv Ofn (((lam : ℂ) * w) ^ 2)
  have hE_an : AnalyticOnNhd ℂ Efn (ball 0 r_sup) := hE_d.analyticOnNhd isOpen_ball
  have hO_an : AnalyticOnNhd ℂ Ofn (ball 0 r_sup) := hO_d.analyticOnNhd isOpen_ball
  have hG_der : ∀ w ∈ ball (0 : ℂ) R₀, HasDerivAt G (G' w) w := fun w hw => by
    have hqm := (hq_sub w hw).2
    have hdsq : HasDerivAt (fun z : ℂ => ((lam : ℂ) * z) ^ 2) (2 * (lam : ℂ) ^ 2 * w) w :=
      (((hasDerivAt_id w).const_mul (lam : ℂ)).pow 2).congr_deriv (by dsimp only [id]; ring)
    have hde : HasDerivAt (fun z => Efn (((lam : ℂ) * z) ^ 2))
        (2 * (lam : ℂ) ^ 2 * w * deriv Efn (((lam : ℂ) * w) ^ 2)) w :=
      ((hE_d.differentiableAt (isOpen_ball.mem_nhds hqm)).hasDerivAt.comp w hdsq).congr_deriv (by ring)
    have hdo : HasDerivAt (fun z => Ofn (((lam : ℂ) * z) ^ 2))
        (2 * (lam : ℂ) ^ 2 * w * deriv Ofn (((lam : ℂ) * w) ^ 2)) w :=
      ((hO_d.differentiableAt (isOpen_ball.mem_nhds hqm)).hasDerivAt.comp w hdsq).congr_deriv (by ring)
    have hds : HasDerivAt (fun z : ℂ => Complex.I * ((lam : ℂ) * z)) (Complex.I * (lam : ℂ)) w :=
      (((hasDerivAt_id w).const_mul (lam : ℂ)).const_mul Complex.I).congr_deriv (by ring)
    exact (hde.add (hds.mul hdo)).congr_deriv (by dsimp [G']; ring)
  have hG'_cont : ContinuousOn G' (ball 0 R₀) := by
    have hsq_c : ContinuousOn (fun w : ℂ => ((lam : ℂ) * w) ^ 2) (ball 0 R₀) :=
      ((continuous_const.mul continuous_id).pow 2).continuousOn
    have hmaps : MapsTo (fun w : ℂ => ((lam : ℂ) * w) ^ 2) (ball 0 R₀) (ball 0 r_sup) :=
      fun w hw => (hq_sub w hw).2
    refine (((continuousOn_const.mul continuousOn_id).mul
      (hE_an.deriv.continuousOn.comp hsq_c hmaps)).add
      (continuousOn_const.mul (hO_d.continuousOn.comp hsq_c hmaps))).add
      ((continuousOn_const.mul (continuousOn_id.pow 2)).mul
        (hO_an.deriv.continuousOn.comp hsq_c hmaps))
  have hG_bd : ∀ w ∈ ball (0 : ℂ) R₀, ‖G w‖ ≤ M_E + Rs * M_O := fun w hw => by
    have hqm := (hq_sub w hw).2
    have hlw : ‖(lam : ℂ) * w‖ ≤ Rs := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hl0.le]
      calc lam * ‖w‖ ≤ lam * R₀ := mul_le_mul_of_nonneg_left (mem_ball_zero_iff.1 hw).le hl0.le
        _ = Rs := hlamR₀
    dsimp [G]
    calc ‖Efn (((lam : ℂ) * w) ^ 2) + Complex.I * ((lam : ℂ) * w) * Ofn (((lam : ℂ) * w) ^ 2)‖
        ≤ ‖Efn (((lam : ℂ) * w) ^ 2)‖ + ‖Complex.I‖ * ‖(lam : ℂ) * w‖ * ‖Ofn (((lam : ℂ) * w) ^ 2)‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_mul, norm_mul]
      _ ≤ M_E + 1 * Rs * M_O := by rw [Complex.norm_I]; gcongr; exact hE_bd _ hqm; exact hO_bd _ hqm
      _ = M_E + Rs * M_O := by ring
  have hG'_bd : ∀ w ∈ ball (0 : ℂ) R₀, ‖G' w‖ ≤ lam * (2 * Rs * M_ED + M_O + 2 * Rs ^ 2 * M_OD) :=
    fun w hw => by
    have hqm := (hq_sub w hw).2
    have hqs := (hq_sub w hw).1
    have hlw : lam * ‖w‖ ≤ Rs := by
      calc lam * ‖w‖ ≤ lam * R₀ := mul_le_mul_of_nonneg_left (mem_ball_zero_iff.1 hw).le hl0.le
        _ = Rs := hlamR₀
    have hl2w2 : lam ^ 2 * ‖w‖ ^ 2 ≤ Rs ^ 2 := by
      calc lam ^ 2 * ‖w‖ ^ 2 = (lam * ‖w‖) ^ 2 := by ring
        _ ≤ Rs ^ 2 := pow_le_pow_left₀ (by positivity) hlw 2
    dsimp [G']
    calc ‖2 * (lam : ℂ) ^ 2 * w * deriv Efn (((lam : ℂ) * w) ^ 2) +
            Complex.I * (lam : ℂ) * Ofn (((lam : ℂ) * w) ^ 2) +
            Complex.I * 2 * (lam : ℂ) ^ 3 * w ^ 2 * deriv Ofn (((lam : ℂ) * w) ^ 2)‖
        ≤ 2 * lam ^ 2 * ‖w‖ * ‖deriv Efn (((lam : ℂ) * w) ^ 2)‖ +
            lam * ‖Ofn (((lam : ℂ) * w) ^ 2)‖ +
            2 * lam ^ 3 * ‖w‖ ^ 2 * ‖deriv Ofn (((lam : ℂ) * w) ^ 2)‖ := by
          refine (norm_add₃_le).trans (add_le_add_three ?_ ?_ ?_) <;>
          simp only [norm_mul, norm_pow, Complex.norm_I, Complex.norm_real,
            Real.norm_of_nonneg hl0.le, show ‖(2 : ℂ)‖ = 2 by norm_num, one_mul, mul_assoc] <;>
          exact le_rfl
      _ ≤ 2 * lam * Rs * M_ED + lam * M_O + 2 * lam * Rs ^ 2 * M_OD := by
          refine add_le_add_three ?_ ?_ ?_
          · calc 2 * lam ^ 2 * ‖w‖ * ‖deriv Efn (((lam : ℂ) * w) ^ 2)‖
                = 2 * lam * (lam * ‖w‖) * ‖deriv Efn (((lam : ℂ) * w) ^ 2)‖ := by ring
              _ ≤ 2 * lam * Rs * M_ED := by gcongr; exact hED_bd _ hqs
          · gcongr; exact hO_bd _ hqm
          · calc 2 * lam ^ 3 * ‖w‖ ^ 2 * ‖deriv Ofn (((lam : ℂ) * w) ^ 2)‖
                = 2 * lam * (lam ^ 2 * ‖w‖ ^ 2) * ‖deriv Ofn (((lam : ℂ) * w) ^ 2)‖ := by ring
              _ ≤ 2 * lam * Rs ^ 2 * M_OD := by gcongr; exact hOD_bd _ hqs
      _ = lam * (2 * Rs * M_ED + M_O + 2 * Rs ^ 2 * M_OD) := by ring
  have hibp := fs_ibp_eval hR1 hUR ch (by positivity) (by positivity) hG_der hG'_cont hG_bd hG'_bd
  have hB3_main : ch.B3 (fun w => csr w * (Complex.I * (G w / (2 * w) + G' w)))
      (M_E / 2) (lam * (3 / 2 * M_O + 2 * Rs ^ 2 * M_OD)) (2 * lam ^ 2 * M_ED) := by
    refine Chain3.B3.of_pointwise ch (by positivity) (by positivity) (by positivity) ?_ ?_
    · intro z hz hre hz0
      have hGc : ContinuousAt G z := (hG_der z hz).differentiableAt.continuousAt
      have hG'c : ContinuousAt G' z := hG'_cont.continuousAt (isOpen_ball.mem_nhds hz)
      exact (continuousAt_csr (Or.inl hre)).mul
        (((hGc.div (continuousAt_const.mul continuousAt_id) (by simp [hz0])).add hG'c).const_mul _)
    · intro z hz _ hz0
      have hqm := (hq_sub z hz).2
      have hqs := (hq_sub z hz).1
      have hzn0 : 0 < ‖z‖ := norm_pos_iff.2 hz0
      have hlw : lam * ‖z‖ ≤ Rs := by
        calc lam * ‖z‖ ≤ lam * R₀ := mul_le_mul_of_nonneg_left (mem_ball_zero_iff.1 hz).le hl0.le
          _ = Rs := hlamR₀
      have hl2z2 : lam ^ 2 * ‖z‖ ^ 2 ≤ Rs ^ 2 := by
        calc lam ^ 2 * ‖z‖ ^ 2 = (lam * ‖z‖) ^ 2 := by ring
          _ ≤ Rs ^ 2 := pow_le_pow_left₀ (by positivity) hlw 2
      have hcsrp : ‖csr z‖ = ‖z‖ ^ (1 / 2 : ℝ) := by rw [norm_csr, Real.sqrt_eq_rpow]
      have hcsrm : ‖csr z‖ * ‖z‖⁻¹ = ‖z‖ ^ (-(1 / 2 : ℝ)) := by
        calc ‖csr z‖ * ‖z‖⁻¹ = ‖z‖ ^ (1 / 2 : ℝ) * ‖z‖ ^ (-1 : ℝ) := by
              rw [hcsrp, Real.rpow_neg_one]
          _ = ‖z‖ ^ (-(1 / 2 : ℝ)) := by rw [← Real.rpow_add hzn0]; norm_num
      have hcsrz : ‖csr z‖ * ‖z‖ = ‖z‖ ^ (3 / 2 : ℝ) := by
        calc ‖csr z‖ * ‖z‖ = ‖z‖ ^ (1 / 2 : ℝ) * ‖z‖ ^ (1 : ℝ) := by rw [hcsrp, Real.rpow_one]
          _ = ‖z‖ ^ (3 / 2 : ℝ) := by rw [← Real.rpow_add hzn0]; norm_num
      have hdec : csr z * (Complex.I * (G z / (2 * z) + G' z)) =
          Complex.I / 2 * (csr z / z) * Efn (((lam : ℂ) * z) ^ 2) +
          (-(3 / 2 : ℂ) * (lam : ℂ) * csr z * Ofn (((lam : ℂ) * z) ^ 2) +
            (-(2 : ℂ)) * (lam : ℂ) ^ 3 * z ^ 2 * csr z * deriv Ofn (((lam : ℂ) * z) ^ 2)) +
          2 * Complex.I * (lam : ℂ) ^ 2 * z * csr z * deriv Efn (((lam : ℂ) * z) ^ 2) := by
        dsimp [G, G']; field_simp [hz0]; ring_nf; rw [Complex.I_sq]; ring
      rw [hdec]
      refine (norm_add₃_le).trans (add_le_add_three ?_ ?_ ?_)
      · rw [norm_mul, norm_mul, norm_div, Complex.norm_I, show ‖(2 : ℂ)‖ = 2 by norm_num,
          norm_div, div_eq_mul_inv ‖csr z‖, hcsrm]
        calc 1 / 2 * ‖z‖ ^ (-(1 / 2 : ℝ)) * ‖Efn (((lam : ℂ) * z) ^ 2)‖
            ≤ 1 / 2 * ‖z‖ ^ (-(1 / 2 : ℝ)) * M_E := by gcongr; exact hE_bd _ hqm
          _ = M_E / 2 * ‖z‖ ^ (-(1 / 2 : ℝ)) := by ring
      · have hm1 : ‖-(3 / 2 : ℂ) * (lam : ℂ) * csr z * Ofn (((lam : ℂ) * z) ^ 2)‖ ≤
            lam * (3 / 2 * M_O) * ‖z‖ ^ (1 / 2 : ℝ) := by
          simp only [norm_mul, norm_neg, show ‖(3 / 2 : ℂ)‖ = 3 / 2 by norm_num,
            Complex.norm_real, Real.norm_of_nonneg hl0.le, hcsrp]
          calc 3 / 2 * lam * ‖z‖ ^ (1 / 2 : ℝ) * ‖Ofn (((lam : ℂ) * z) ^ 2)‖
              ≤ 3 / 2 * lam * ‖z‖ ^ (1 / 2 : ℝ) * M_O := by gcongr; exact hO_bd _ hqm
            _ = lam * (3 / 2 * M_O) * ‖z‖ ^ (1 / 2 : ℝ) := by ring
        have hm2 : ‖-(2 : ℂ) * (lam : ℂ) ^ 3 * z ^ 2 * csr z * deriv Ofn (((lam : ℂ) * z) ^ 2)‖ ≤
            lam * (2 * Rs ^ 2 * M_OD) * ‖z‖ ^ (1 / 2 : ℝ) := by
          simp only [norm_mul, norm_neg, norm_pow, show ‖(2 : ℂ)‖ = 2 by norm_num,
            Complex.norm_real, Real.norm_of_nonneg hl0.le, hcsrp]
          calc 2 * lam ^ 3 * ‖z‖ ^ 2 * ‖z‖ ^ (1 / 2 : ℝ) * ‖deriv Ofn (((lam : ℂ) * z) ^ 2)‖
              ≤ 2 * lam * (lam ^ 2 * ‖z‖ ^ 2) * ‖z‖ ^ (1 / 2 : ℝ) * M_OD := by
                have e1 : 2 * lam ^ 3 * ‖z‖ ^ 2 = 2 * lam * (lam ^ 2 * ‖z‖ ^ 2) := by ring
                rw [e1]; gcongr; exact hOD_bd _ hqs
            _ ≤ 2 * lam * Rs ^ 2 * ‖z‖ ^ (1 / 2 : ℝ) * M_OD := by gcongr
            _ = lam * (2 * Rs ^ 2 * M_OD) * ‖z‖ ^ (1 / 2 : ℝ) := by ring
        calc ‖-(3 / 2 : ℂ) * (lam : ℂ) * csr z * Ofn (((lam : ℂ) * z) ^ 2) +
              -(2 : ℂ) * (lam : ℂ) ^ 3 * z ^ 2 * csr z * deriv Ofn (((lam : ℂ) * z) ^ 2)‖
            ≤ ‖-(3 / 2 : ℂ) * (lam : ℂ) * csr z * Ofn (((lam : ℂ) * z) ^ 2)‖ +
              ‖-(2 : ℂ) * (lam : ℂ) ^ 3 * z ^ 2 * csr z * deriv Ofn (((lam : ℂ) * z) ^ 2)‖ :=
              norm_add_le _ _
          _ ≤ lam * (3 / 2 * M_O) * ‖z‖ ^ (1 / 2 : ℝ) +
              lam * (2 * Rs ^ 2 * M_OD) * ‖z‖ ^ (1 / 2 : ℝ) := add_le_add hm1 hm2
          _ = lam * (3 / 2 * M_O + 2 * Rs ^ 2 * M_OD) * ‖z‖ ^ (1 / 2 : ℝ) := by ring
      · simp only [norm_mul, norm_pow, Complex.norm_I, show ‖(2 : ℂ)‖ = 2 by norm_num,
          Complex.norm_real, Real.norm_of_nonneg hl0.le, mul_one]
        rw [mul_assoc (2 * lam ^ 2) ‖z‖ ‖csr z‖, mul_comm ‖z‖ ‖csr z‖, hcsrz]
        calc 2 * lam ^ 2 * ‖z‖ ^ (3 / 2 : ℝ) * ‖deriv Efn (((lam : ℂ) * z) ^ 2)‖
            ≤ 2 * lam ^ 2 * ‖z‖ ^ (3 / 2 : ℝ) * M_ED := by gcongr; exact hED_bd _ hqs
          _ = 2 * lam ^ 2 * M_ED * ‖z‖ ^ (3 / 2 : ℝ) := by ring
  have hm_int := hB3_main.norm_intE_le (U := u)
  have h1u : (1 + |u|) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg u]) (by norm_num)
  have hUR_lam : lam * (1 + |u|) ^ (1 / 2 : ℝ) ≤ Real.sqrt (1 + s₁ ^ 2 / 16) := by
    have hu_le : |u| ≤ (s₁ ^ 2 / 16) * lam ^ (-2 : ℤ) := by
      have hku : 1 * |u| ≤ kap * |u| := mul_le_mul_of_nonneg_right kap_ge_one (abs_nonneg u)
      have hRsq : R ^ 2 / 16 = (s₁ ^ 2 / 16) * lam ^ (-2 : ℤ) := by
        rw [hRdef, div_pow, zpow_neg, zpow_two, div_eq_mul_inv]; ring
      linarith only [hku, hUR, hRsq]
    have hl2_ge : lam ^ 2 ≤ 1 := by nlinarith only [hl0, hl1]
    have hsum : lam ^ 2 * (1 + |u|) ≤ 1 + s₁ ^ 2 / 16 := by
      calc lam ^ 2 * (1 + |u|) = lam ^ 2 + lam ^ 2 * |u| := by ring
        _ ≤ 1 + lam ^ 2 * ((s₁ ^ 2 / 16) * lam ^ (-2 : ℤ)) := by gcongr
        _ = 1 + s₁ ^ 2 / 16 := by rw [zpow_neg, zpow_two]; field_simp [hl0.ne']
    calc lam * (1 + |u|) ^ (1 / 2 : ℝ)
        = Real.sqrt (lam ^ 2 * (1 + |u|)) := by
          rw [Real.sqrt_mul (sq_nonneg lam), Real.sqrt_sq hl0.le, Real.sqrt_eq_rpow]
      _ ≤ Real.sqrt (1 + s₁ ^ 2 / 16) := Real.sqrt_le_sqrt hsum
  have hm_le : ‖ch.intE u (fun w => csr w * (Complex.I * (G w / (2 * w) + G' w)))‖ ≤
      (M_E / 2) * Cm + (3 / 2 * M_O + 2 * Rs ^ 2 * M_OD) * Cm +
        (2 * M_ED) * (Cm * Real.sqrt (1 + s₁ ^ 2 / 16)) := by
    have hm1' : ch.mom u (-(1 / 2)) ≤ Cm := hmom.1.trans (mul_le_of_le_one_right hCm h1u)
    have hm2_nn : 0 ≤ ch.mom u (1 / 2) := chain3_mom_nonneg ch u _
    have hlam_m2 : lam * (3 / 2 * M_O + 2 * Rs ^ 2 * M_OD) * ch.mom u (1 / 2) ≤
        (3 / 2 * M_O + 2 * Rs ^ 2 * M_OD) * Cm := by
      calc lam * (3 / 2 * M_O + 2 * Rs ^ 2 * M_OD) * ch.mom u (1 / 2)
          ≤ 1 * (3 / 2 * M_O + 2 * Rs ^ 2 * M_OD) * Cm := by gcongr; exact hmom.2.1
        _ = (3 / 2 * M_O + 2 * Rs ^ 2 * M_OD) * Cm := by rw [one_mul]
    have hlam_m3 : 2 * lam ^ 2 * M_ED * ch.mom u (3 / 2) ≤
        (2 * M_ED) * (Cm * Real.sqrt (1 + s₁ ^ 2 / 16)) := by
      calc 2 * lam ^ 2 * M_ED * ch.mom u (3 / 2)
          ≤ 2 * lam ^ 2 * M_ED * (Cm * (1 + |u|) ^ (1 / 2 : ℝ)) := by gcongr; exact hmom.2.2
        _ = 2 * lam * M_ED * (Cm * (lam * (1 + |u|) ^ (1 / 2 : ℝ))) := by ring
        _ ≤ 2 * 1 * M_ED * (Cm * Real.sqrt (1 + s₁ ^ 2 / 16)) := by gcongr
        _ = (2 * M_ED) * (Cm * Real.sqrt (1 + s₁ ^ 2 / 16)) := by ring
    linarith [hm_int, mul_le_mul_of_nonneg_left hm1' (by positivity : 0 ≤ M_E / 2)]
  have hOp_mom : |fsOpCh ch u (fun w => Complex.I * (G w / (2 * w) + G' w))| ≤
      (1 / √π) * ((M_E / 2) * Cm + (3 / 2 * M_O + 2 * Rs ^ 2 * M_OD) * Cm +
        (2 * M_ED) * (Cm * Real.sqrt (1 + s₁ ^ 2 / 16))) := by
    unfold fsOpCh
    rw [abs_mul, abs_neg, abs_of_pos (one_div_pos.2 hpi)]
    refine mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans ?_) (by positivity)
    rw [norm_mul, mul_comm Complex.I _, Complex.norm_exp_ofReal_mul_I, one_mul]
    exact hm_le
  have hTail : (1 / √π) * Real.sqrt R * (M_E + Rs * M_O) * Real.exp (-(R ^ 3 / 12)) ≤
      (1 / √π) * ((M_E + Rs * M_O) * (288 / s₁ ^ 5) * lam ^ 5) := by
    have hexp := (exp_cubic_tail_bound hR1).1
    have hR5 : 288 / R ^ 5 = (288 / s₁ ^ 5) * lam ^ 5 := by
      rw [hRdef, div_pow]; field_simp [hs₁.ne', hl0.ne']
    calc (1 / √π) * Real.sqrt R * (M_E + Rs * M_O) * Real.exp (-(R ^ 3 / 12))
        = (1 / √π) * (M_E + Rs * M_O) * (Real.sqrt R * Real.exp (-(R ^ 3 / 12))) := by ring
      _ ≤ (1 / √π) * (M_E + Rs * M_O) * (288 / R ^ 5) := by gcongr
      _ = (1 / √π) * ((M_E + Rs * M_O) * (288 / s₁ ^ 5) * lam ^ 5) := by rw [hR5]; ring
  calc |fsOpCh ch u (fun w => G w * ((kap : ℂ) * u + w ^ 2))|
      = |(fsOpCh ch u (fun w => G w * ((kap : ℂ) * u + w ^ 2)) -
          fsOpCh ch u (fun w => Complex.I * (G w / (2 * w) + G' w))) +
          fsOpCh ch u (fun w => Complex.I * (G w / (2 * w) + G' w))| := by congr 1; ring
    _ ≤ |fsOpCh ch u (fun w => G w * ((kap : ℂ) * u + w ^ 2)) -
          fsOpCh ch u (fun w => Complex.I * (G w / (2 * w) + G' w))| +
          |fsOpCh ch u (fun w => Complex.I * (G w / (2 * w) + G' w))| := abs_add_le _ _
    _ ≤ _ := by linarith [hibp, hTail, hOp_mom]

end FineOrderSigned

end FormalResearch.SignUncertainty
