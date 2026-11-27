module

public import FormalResearch.SignUncertainty.FineOrderSignedCascade
public import FormalResearch.SignUncertainty.FineOrderSignedOps

/-!
# Shared signed half-cubic reduction (`fs:half-cubic`): Parts (1) and (2)

Source: `CFT/common/fine_order_signed.tex`, Lemma FS.1 (`fs:half-cubic`), equations `(fs:principal)`
and `(fs:aux)`. Phase-free; shared between Paper I (`SignUncertainty`) and Paper II (`ModularBootstrap`).
-/

@[expose] public section

open Complex MeasureTheory Metric Set Filter Topology intervalIntegral
open scoped Real

namespace FormalResearch.SignUncertainty.FineOrderSigned

open FormalResearch.SignUncertainty CtSd HalfCubicInternal

private lemma hasDerivAt_even_odd_shift {fE fO : ℂ → ℂ} {r_q lam R₀ : ℝ}
    (hmap : ∀ w ∈ ball (0 : ℂ) R₀, ((lam : ℂ) * w) ^ 2 ∈ ball (0 : ℂ) r_q)
    (hE : DifferentiableOn ℂ fE (ball 0 r_q)) (hO : DifferentiableOn ℂ fO (ball 0 r_q))
    (w : ℂ) (hw : w ∈ ball (0 : ℂ) R₀) :
    HasDerivAt (fun z => fE (((lam : ℂ) * z) ^ 2) +
        Complex.I * ((lam : ℂ) * z) * fO (((lam : ℂ) * z) ^ 2))
      (2 * (lam : ℂ) ^ 2 * w * deriv fE (((lam : ℂ) * w) ^ 2) +
        Complex.I * (lam : ℂ) * fO (((lam : ℂ) * w) ^ 2) +
        Complex.I * 2 * (lam : ℂ) ^ 3 * w ^ 2 * deriv fO (((lam : ℂ) * w) ^ 2)) w := by
  have hqm := hmap w hw
  have hdsq : HasDerivAt (fun z : ℂ => ((lam : ℂ) * z) ^ 2) (2 * (lam : ℂ) ^ 2 * w) w :=
    (((hasDerivAt_id w).const_mul (lam : ℂ)).pow 2).congr_deriv (by dsimp only [id]; ring)
  have hde : HasDerivAt (fun z => fE (((lam : ℂ) * z) ^ 2))
      (2 * (lam : ℂ) ^ 2 * w * deriv fE (((lam : ℂ) * w) ^ 2)) w :=
    ((hE.differentiableAt (isOpen_ball.mem_nhds hqm)).hasDerivAt.comp w hdsq).congr_deriv (by ring)
  have hdo : HasDerivAt (fun z => fO (((lam : ℂ) * z) ^ 2))
      (2 * (lam : ℂ) ^ 2 * w * deriv fO (((lam : ℂ) * w) ^ 2)) w :=
    ((hO.differentiableAt (isOpen_ball.mem_nhds hqm)).hasDerivAt.comp w hdsq).congr_deriv (by ring)
  have hds : HasDerivAt (fun z : ℂ => Complex.I * ((lam : ℂ) * z)) (Complex.I * (lam : ℂ)) w :=
    (((hasDerivAt_id w).const_mul (lam : ℂ)).const_mul Complex.I).congr_deriv (by ring)
  exact (hde.add (hds.mul hdo)).congr_deriv (by ring)

private lemma continuousOn_even_odd_deriv {fE fO : ℂ → ℂ} {r_q lam R₀ : ℝ}
    (hmap : ∀ w ∈ ball (0 : ℂ) R₀, ((lam : ℂ) * w) ^ 2 ∈ ball (0 : ℂ) r_q)
    (hE : DifferentiableOn ℂ fE (ball 0 r_q)) (hO : DifferentiableOn ℂ fO (ball 0 r_q)) :
    ContinuousOn (fun w : ℂ =>
      2 * (lam : ℂ) ^ 2 * w * deriv fE (((lam : ℂ) * w) ^ 2) +
      Complex.I * (lam : ℂ) * fO (((lam : ℂ) * w) ^ 2) +
      Complex.I * 2 * (lam : ℂ) ^ 3 * w ^ 2 * deriv fO (((lam : ℂ) * w) ^ 2)) (ball 0 R₀) := by
  have hsq_c : ContinuousOn (fun w : ℂ => ((lam : ℂ) * w) ^ 2) (ball 0 R₀) :=
    ((continuous_const.mul continuous_id).pow 2).continuousOn
  have hE_an : AnalyticOnNhd ℂ fE (ball 0 r_q) := hE.analyticOnNhd isOpen_ball
  have hO_an : AnalyticOnNhd ℂ fO (ball 0 r_q) := hO.analyticOnNhd isOpen_ball
  refine (((continuousOn_const.mul continuousOn_id).mul
    (hE_an.deriv.continuousOn.comp hsq_c hmap)).add
    (continuousOn_const.mul (hO.continuousOn.comp hsq_c hmap))).add
    ((continuousOn_const.mul (continuousOn_id.pow 2)).mul
      (hO_an.deriv.continuousOn.comp hsq_c hmap))

private lemma norm_even_odd_deriv_le {nO nED nOD lam R₀ Rs M_O M_ED M_OD : ℝ}
    (hl0 : 0 < lam) (hlamR₀ : lam * R₀ = Rs)
    (hO : nO ≤ M_O) (hED : nED ≤ M_ED) (hOD : nOD ≤ M_OD)
    (_hnO : 0 ≤ nO) (hnED : 0 ≤ nED) (hnOD : 0 ≤ nOD)
    {w : ℂ} (hw : ‖w‖ < R₀) (hRs0 : 0 ≤ Rs) :
    2 * lam ^ 2 * ‖w‖ * nED + lam * nO + 2 * lam ^ 3 * ‖w‖ ^ 2 * nOD ≤
      lam * (2 * Rs * M_ED + M_O + 2 * Rs ^ 2 * M_OD) := by
  have hlw : lam * ‖w‖ ≤ Rs := by
    calc lam * ‖w‖ ≤ lam * R₀ := mul_le_mul_of_nonneg_left hw.le hl0.le
      _ = Rs := hlamR₀
  have hl2w2 : lam ^ 2 * ‖w‖ ^ 2 ≤ Rs ^ 2 := by
    calc lam ^ 2 * ‖w‖ ^ 2 = (lam * ‖w‖) ^ 2 := by ring
      _ ≤ Rs ^ 2 := pow_le_pow_left₀ (by positivity) hlw 2
  have ha : 2 * lam ^ 2 * ‖w‖ * nED ≤ 2 * lam * Rs * M_ED := by
    calc 2 * lam ^ 2 * ‖w‖ * nED = 2 * lam * (lam * ‖w‖) * nED := by ring
      _ ≤ 2 * lam * Rs * M_ED := by gcongr
  have hb : lam * nO ≤ lam * M_O := by gcongr
  have hc : 2 * lam ^ 3 * ‖w‖ ^ 2 * nOD ≤ 2 * lam * Rs ^ 2 * M_OD := by
    calc 2 * lam ^ 3 * ‖w‖ ^ 2 * nOD = 2 * lam * (lam ^ 2 * ‖w‖ ^ 2) * nOD := by ring
      _ ≤ 2 * lam * Rs ^ 2 * M_OD := by gcongr
  linarith

private lemma b3_even_odd_quad {fE fO : ℂ → ℂ} {r_q lam R₀ Rs u M_E M_O : ℝ}
    {p : ℂ} (ch : Chain3 R₀ p) (hl0 : 0 < lam) (hlamR₀ : lam * R₀ = Rs)
    (hME : 0 ≤ M_E) (hMO : 0 ≤ M_O) (hRs : 0 ≤ Rs)
    (hmap : ∀ w ∈ ball (0 : ℂ) R₀, ((lam : ℂ) * w) ^ 2 ∈ ball (0 : ℂ) r_q)
    (hE_d : DifferentiableOn ℂ fE (ball 0 r_q)) (hO_d : DifferentiableOn ℂ fO (ball 0 r_q))
    (hE_bd : ∀ w ∈ ball (0 : ℂ) R₀, ‖fE (((lam : ℂ) * w) ^ 2)‖ ≤ M_E)
    (hO_bd : ∀ w ∈ ball (0 : ℂ) R₀, ‖fO (((lam : ℂ) * w) ^ 2)‖ ≤ M_O) :
    ch.B3 (fun w => csr w * ((fE (((lam : ℂ) * w) ^ 2) +
        Complex.I * ((lam : ℂ) * w) * fO (((lam : ℂ) * w) ^ 2)) * ((kap : ℂ) * u + w ^ 2)))
      0 ((M_E + Rs * M_O) * (kap * |u| + R₀ ^ 2)) 0 :=
  b3_csr_bounded ch (mul_nonneg (add_nonneg hME (mul_nonneg hRs hMO))
      (add_nonneg (mul_nonneg kap_pos.le (abs_nonneg _)) (sq_nonneg _)))
    (((hE_d.continuousOn.comp ((continuous_const.mul continuous_id).pow 2).continuousOn hmap).add
      ((continuousOn_const.mul (continuousOn_const.mul continuousOn_id)).mul
        (hO_d.continuousOn.comp ((continuous_const.mul continuous_id).pow 2).continuousOn hmap))).mul
      (continuousOn_const.add (continuousOn_id.pow 2)))
    (fun w hw => by
      have hlw : ‖(lam : ℂ) * w‖ ≤ Rs := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hl0.le]
        calc lam * ‖w‖ ≤ lam * R₀ := mul_le_mul_of_nonneg_left (mem_ball_zero_iff.1 hw).le hl0.le
          _ = Rs := hlamR₀
      rw [norm_mul]
      refine mul_le_mul ?_ ?_ (norm_nonneg _) (add_nonneg hME (mul_nonneg hRs hMO))
      · calc ‖fE (((lam : ℂ) * w) ^ 2) + Complex.I * ((lam : ℂ) * w) * fO (((lam : ℂ) * w) ^ 2)‖
            ≤ M_E + 1 * Rs * M_O := by
              refine (norm_add_le _ _).trans ?_; rw [norm_mul, norm_mul, Complex.norm_I]
              gcongr; exact hE_bd w hw; exact hO_bd w hw
          _ = M_E + Rs * M_O := by ring
      · calc ‖(kap : ℂ) * u + w ^ 2‖ ≤ ‖(kap : ℂ) * u‖ + ‖w ^ 2‖ := norm_add_le _ _
          _ ≤ kap * |u| + R₀ ^ 2 := by
              rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg kap_pos.le, Complex.norm_real,
                Real.norm_eq_abs, norm_pow]
              have := (mem_ball_zero_iff.1 hw).le; gcongr)

private lemma fs_first_div_expand (d : HalfCubicData) {n a R R₀ u : ℝ} (hn : d.n₀ ≤ n)
    (ha : |a| < d.rAShrunk) (hu : u = d.uReal n a) (hlamR₀ : n ^ (-(1 / 3 : ℝ)) * R₀ = Rs d)
    (ch : Chain3 R₀ ((R : ℂ) * d6)) :
    let lam := n ^ (-(1 / 3 : ℝ))
    let G₁ : ℂ → ℂ := fun w => Qe d n (((lam : ℂ) * w) ^ 2) a +
      Complex.I * ((lam : ℂ) * w) * Qo d n (((lam : ℂ) * w) ^ 2) a
    fsOpCh ch u (fun w => d.B n a ((lam : ℂ) * w)) =
      (A0 d n a).re * fsOpCh ch u (fun _ => 1) +
        lam * (A1 d n a).re * fsOpCh ch u (fun w => Complex.I * w) +
        lam ^ 2 * fsOpCh ch u (fun w => G₁ w * ((kap : ℂ) * u + w ^ 2)) := by
  have ⟨hn1, _, _, _, _, _⟩ := aHat_facts d hn
  have ⟨_, _, h1, h2, h3, h4, h5, h6, h7, _, hrs⟩ := radii_chain d
  have ⟨hl0, _, _, _, _, _, _⟩ := rpow_lam_rels hn1
  have ⟨_, _, _, hU_eq⟩ := uReal_facts d hn ha
  have hAreal := (A0_A1_facts d hn).2.2.2
  have ⟨hqE_d, hqO_d, hbdQ, _⟩ := (Q_facts d hn).1 a (by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact ha)
  have hRs0 : 0 ≤ Rs d := Real.sqrt_nonneg _
  have hMQe0 : 0 ≤ MQe d := div_nonneg (mul_nonneg (by linarith) d.hM_E) (sq_nonneg _)
  have hMQo0 : 0 ≤ MQo d := div_nonneg (mul_nonneg (by linarith) d.hM_O) (sq_nonneg _)
  set lam := n ^ (-(1 / 3 : ℝ))
  have ha_ball : (a : ℂ) ∈ ball (0 : ℂ) d.rAShrunk := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact ha
  have hsub : ball (0 : ℂ) d.rAShrunk ⊆ ball (0 : ℂ) d.r_a := ball_subset_ball d.rAShrunk_lt.le
  have hc_b := c_ball d hn ha_ball
  have hq_mem : ∀ w ∈ ball (0 : ℂ) R₀,
      ((lam : ℂ) * w) ^ 2 ∈ ball (0 : ℂ) (r1 d) ∧ ((lam : ℂ) * w) ^ 2 ∈ ball (0 : ℂ) (r0 d) := by
    intro w hw
    have hnw : ‖(lam : ℂ) * w‖ < Rs d := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hl0.le]
      calc lam * ‖w‖ < lam * R₀ := mul_lt_mul_of_pos_left (mem_ball_zero_iff.1 hw) hl0
        _ = Rs d := hlamR₀
    have hnq : ‖((lam : ℂ) * w) ^ 2‖ < rsSq d := by
      rw [norm_pow, ← hrs]; nlinarith [norm_nonneg ((lam : ℂ) * w), hnw, hRs0]
    refine ⟨?_, ?_⟩ <;> rw [mem_ball_zero_iff] <;> linarith
  set G₁ : ℂ → ℂ := fun w => Qe d n (((lam : ℂ) * w) ^ 2) a +
    Complex.I * ((lam : ℂ) * w) * Qo d n (((lam : ℂ) * w) ^ 2) a
  have hB_split : ∀ w ∈ ball (0 : ℂ) R₀, d.B n a ((lam : ℂ) * w) =
      A0 d n a + (Complex.I * (lam : ℂ) * A1 d n a) * w +
        (lam : ℂ) ^ 2 * (G₁ w * ((kap : ℂ) * u + w ^ 2)) := by
    intro w hw
    have hq0 := (hq_mem w hw).2
    have hEq := divQ_eq (by linarith) h7 (d.hE_q n a hn1 (hsub ha_ball)) hc_b.2.2.2.2.1 hq0
    have hOq := divQ_eq (by linarith) h7 (d.hO_q n a hn1 (hsub ha_ball)) hc_b.2.2.2.2.1 hq0
    have hfac : ((lam : ℂ) * w) ^ 2 - (-d.aHat n a) = (lam : ℂ) ^ 2 * ((kap : ℂ) * u + w ^ 2) := by
      rw [sub_neg_eq_add, hu, ← hU_eq]; ring
    unfold HalfCubicData.B A0 A1
    calc d.E n (((lam : ℂ) * w) ^ 2) a + Complex.I * ((lam : ℂ) * w) * d.O n (((lam : ℂ) * w) ^ 2) a
        = (d.E n (-d.aHat n a) a + (((lam : ℂ) * w) ^ 2 - (-d.aHat n a)) *
            divQ (fun ζ => d.E n ζ a) (r0 d) (-d.aHat n a) (((lam : ℂ) * w) ^ 2)) +
          Complex.I * ((lam : ℂ) * w) * (d.O n (-d.aHat n a) a +
            (((lam : ℂ) * w) ^ 2 - (-d.aHat n a)) *
              divQ (fun ζ => d.O n ζ a) (r0 d) (-d.aHat n a) (((lam : ℂ) * w) ^ 2)) := by
          rw [← hEq, ← hOq]; ring
      _ = d.E n (-d.aHat n a) a + (Complex.I * (lam : ℂ) * d.O n (-d.aHat n a) a) * w +
            (lam : ℂ) ^ 2 * (G₁ w * ((kap : ℂ) * u + w ^ 2)) := by
          rw [hfac]; dsimp [G₁]; unfold Qe Qo; ring
  have hb_1 : ch.B3 (fun w => csr w * (1 : ℂ)) 0 1 0 :=
    b3_csr_bounded ch zero_le_one continuousOn_const (fun _ _ => by simp)
  have hb_iw : ch.B3 (fun w => csr w * (Complex.I * w)) 0 0 1 := b3_csr_iw ch
  have hG₁_B3 := b3_even_odd_quad ch hl0 hlamR₀ hMQe0 hMQo0 hRs0 (fun w hw => (hq_mem w hw).2)
    hqE_d hqO_d (fun w hw => (hbdQ _ (ball_subset_closedBall (hq_mem w hw).1)).1)
    (fun w hw => (hbdQ _ (ball_subset_closedBall (hq_mem w hw).1)).2)
  have hB_congr : ch.intE u (fun w => csr w * d.B n a ((lam : ℂ) * w)) =
      ch.intE u (fun w => csr w * (A0 d n a * 1 + ((lam : ℂ) * A1 d n a) * (Complex.I * w) +
        (lam : ℂ) ^ 2 * (G₁ w * ((kap : ℂ) * u + w ^ 2)))) :=
    chain3_intE_congr_ne_zero ch u
      ((hb_1.smul _).add (hb_iw.smul _) |>.add (hG₁_B3.smul _))
      (fun z hz hre _ => (continuousAt_csr (Or.inl hre)).mul (by
        have hq0 := (hq_mem z hz).2
        have hdE := ((d.hE_q n a hn1 (hsub ha_ball)).differentiableAt
          (isOpen_ball.mem_nhds (ball_subset_ball h7.le hq0))).continuousAt
        have hdO := ((d.hO_q n a hn1 (hsub ha_ball)).differentiableAt
          (isOpen_ball.mem_nhds (ball_subset_ball h7.le hq0))).continuousAt
        have hsq : ContinuousAt (fun w : ℂ => ((lam : ℂ) * w) ^ 2) z :=
          ((continuous_const.mul continuous_id).pow 2).continuousAt
        exact (hdE.comp hsq).add
          ((continuous_const.mul (continuous_const.mul continuous_id)).continuousAt.mul
            (hdO.comp hsq))))
      (fun z hz hre _ => (continuousAt_csr (Or.inl hre)).mul (by
        have hG₁c : ContinuousAt G₁ z := (hasDerivAt_even_odd_shift
          (fun w hw => (hq_mem w hw).2) hqE_d hqO_d z hz).differentiableAt.continuousAt
        exact ((continuousAt_const.add
          (continuousAt_const.mul (continuousAt_const.mul continuousAt_id))).add
          (continuousAt_const.mul (hG₁c.mul (continuousAt_const.add (continuous_pow 2 z).continuousAt))))))
      (fun z hz _ _ => by rw [hB_split z hz]; ring)
  have heqOp : fsOpCh ch u (fun w => d.B n a ((lam : ℂ) * w)) =
      fsOpCh ch u (fun w => A0 d n a * 1 + ((lam : ℂ) * A1 d n a) * (Complex.I * w) +
        (lam : ℂ) ^ 2 * (G₁ w * ((kap : ℂ) * u + w ^ 2))) := by
    unfold fsOpCh; rw [hB_congr]; simp only [mul_add, ← mul_assoc]
    congr 2; ext w; ring
  rw [heqOp, fsOpCh_add ch u ((hb_1.smul _).add (hb_iw.smul _)) (hG₁_B3.smul _),
    fsOpCh_add ch u (hb_1.smul _) (hb_iw.smul _),
    fsOpCh_real_mul ch u (hAreal a ha).1,
    fsOpCh_real_mul ch u (by simp [Complex.mul_im, (hAreal a ha).2] : ((lam : ℂ) * A1 d n a).im = 0),
    fsOpCh_real_mul ch u (by norm_cast; simp : ((lam : ℂ) ^ 2).im = 0)]
  simp only [Complex.re_ofReal_mul, ← Complex.ofReal_pow, Complex.ofReal_re]; ring

/-- **Lemma FS.1 Part (1) (`fs:principal`)**: uniform expansion with `O(n^{-5/3})` remainder and
uniformly bounded, holomorphic, real-symmetric coefficients `C_n, Q_n, T_n`. -/
theorem fs_principal (d : HalfCubicData) {K_E K_O : ℝ} (hKE : 0 ≤ K_E) (hKO : 0 ≤ K_O)
    (hEnorm : ∀ n a, 1 ≤ n → a ∈ ball (0 : ℂ) d.r_a → ‖d.E n (-a) a - 1‖ ≤ K_E * n⁻¹)
    (hOnorm : ∀ n a, 1 ≤ n → a ∈ ball (0 : ℂ) d.r_a → ‖d.O n (-a) a‖ ≤ K_O * n⁻¹) :
    ∃ M_C M_Q M_T C_rem : ℝ, 0 ≤ M_C ∧ 0 ≤ M_Q ∧ 0 ≤ M_T ∧ 0 ≤ C_rem ∧
      ∀ n : ℝ, d.n₀ ≤ n →
        DifferentiableOn ℂ (d.Cn n) (ball 0 d.rAShrunk) ∧
        DifferentiableOn ℂ (d.Qn n) (ball 0 d.rAShrunk) ∧
        DifferentiableOn ℂ (d.Tn n) (ball 0 d.rAShrunk) ∧
        (∀ a ∈ ball (0 : ℂ) d.rAShrunk,
          ‖d.Cn n a‖ ≤ M_C ∧ ‖d.Qn n a‖ ≤ M_Q ∧ ‖d.Tn n a‖ ≤ M_T) ∧
        (∀ a : ℝ, |a| < d.rAShrunk →
          (d.Cn n a).im = 0 ∧ (d.Qn n a).im = 0 ∧ (d.Tn n a).im = 0) ∧
        (∀ a : ℝ, |a| < d.rAShrunk →
          let lam := n ^ (-(1 / 3 : ℝ))
          let R := d.s₁ / lam
          let R₀ := Rs d / lam
          let u := d.uReal n a
          ∀ (hR1 : 1 ≤ R) (hRR : R < R₀) (hUR : kap * |u| ≤ R ^ 2 / 16),
          |fsOpCh (fsChain hR1 hRR hUR) u (fun w => d.B n a ((lam : ℂ) * w)) -
            (fsK u + n⁻¹ * (d.Cn n a).re * fsK u + n ^ (-(2 / 3 : ℝ)) * (d.Qn n a).re * fsJ u +
              n ^ (-(4 / 3 : ℝ)) * (d.Tn n a).re * fsKp u)| ≤
            C_rem * n ^ (-(5 / 3 : ℝ))) := by
  obtain ⟨Cm, hCm, hmom⟩ := fsChain_momOK
  have ⟨_, _, h1, h2, h3, h4, h5, h6, h7, hss, hrs⟩ := radii_chain d
  have hs1_0 : 0 ≤ d.s₁ := d.hs₁.le
  have hr_sub_rc : 0 ≤ r0 d - rc d := by linarith
  have hr0_nn : 0 ≤ r0 d := by linarith
  have hr1_nn : 0 ≤ r1 d := by linarith
  have hr2_nn : 0 ≤ r2 d := by linarith
  have hr3_nn : 0 ≤ r3 d := by linarith
  have hRs0 : 0 ≤ Rs d := Real.sqrt_nonneg _
  have hME0 : 0 ≤ d.M_E := d.hM_E
  have hMO0 : 0 ≤ d.M_O := d.hM_O
  have hMψ0 : 0 ≤ d.M_ψ := d.hM_ψ
  have hMQe0 : 0 ≤ MQe d := by unfold MQe; positivity
  have hMQo0 : 0 ≤ MQo d := by unfold MQo; positivity
  have hMQeD0 : 0 ≤ MQeD d := by unfold MQeD; positivity
  have hMQoD0 : 0 ≤ MQoD d := by unfold MQoD; positivity
  have hMQe00 : 0 ≤ MQe0 d := by unfold MQe0; positivity
  have hMDe0 : 0 ≤ MDe d := by unfold MDe; positivity
  have hMDo0 : 0 ≤ MDo d := by unfold MDo; positivity
  have hMRe0 : 0 ≤ MRe d := by unfold MRe; positivity
  have hMRo0 : 0 ≤ MRo d := by unfold MRo; positivity
  have hMReD0 : 0 ≤ MReD d := by unfold MReD; positivity
  have hMRoD0 : 0 ≤ MRoD d := by unfold MRoD; positivity
  set L_E : ℝ := (rc d + r0 d) / 2 * d.M_E / ((r0 d - rc d) / 2) ^ 2
  set L_O : ℝ := (rc d + r0 d) / 2 * d.M_O / ((r0 d - rc d) / 2) ^ 2
  set M_C : ℝ := L_E * d.M_ψ + K_E + MDe d
  set M_Q : ℝ := (2 : ℝ) ^ (-(1 / 3 : ℝ)) * π * MQe d
  set M_T : ℝ := (2 : ℝ) ^ (-(2 / 3 : ℝ)) * (L_O * d.M_ψ + K_O + MDo d)
  have hLE0 : 0 ≤ L_E := by dsimp [L_E]; positivity
  have hLO0 : 0 ≤ L_O := by dsimp [L_O]; positivity
  have hMC0 : 0 ≤ M_C := by dsimp [M_C]; positivity
  have hMQ0 : 0 ≤ M_Q := by dsimp [M_Q]; positivity
  have hMT0 : 0 ≤ M_T := by dsimp [M_T]; positivity
  set C_ibp2 : ℝ := (1 / √π) * ((MRe d + Rs d * MRo d) * (288 / d.s₁ ^ 5) +
    ((MRe d / 2) * Cm + (3 / 2 * MRo d + 2 * Rs d ^ 2 * MRoD d) * Cm +
      (2 * MReD d) * (Cm * Real.sqrt (1 + d.s₁ ^ 2 / 16))))
  set C_rem : ℝ := (1 / √π) * (MQe d + Rs d * MQo d) * (288 / d.s₁ ^ 5) +
    (144 / √π) * (288 / d.s₁ ^ 6) * (1 + M_C + (2 : ℝ) ^ (2 / 3 : ℝ) * M_T) +
    (578 / √π) * (288 / d.s₁ ^ 5) * (MQe d / 2) + C_ibp2
  refine ⟨M_C, M_Q, M_T, C_rem, hMC0, hMQ0, hMT0, by dsimp [C_rem, C_ibp2]; positivity, ?_⟩
  intro n hn
  have ⟨hn1, _, _, _, _, _⟩ := aHat_facts d hn
  have hn0 : 0 < n := by linarith
  have ⟨hA0d, hA1d, _, hAreal⟩ := A0_A1_facts d hn
  have ⟨hQ1, hQ2, hQ3⟩ := Q_facts d hn
  have ⟨hD1, hD0d, hD1d, hDbd, hDreal⟩ := D_facts d hn
  have hsub : ball (0 : ℂ) d.rAShrunk ⊆ ball (0 : ℂ) d.r_a := ball_subset_ball d.rAShrunk_lt.le
  have hCn_d : DifferentiableOn ℂ (d.Cn n) (ball 0 d.rAShrunk) :=
    ((differentiableOn_const _).mul (hA0d.sub (differentiableOn_const _))).add hD0d
  have hQn_d : DifferentiableOn ℂ (d.Qn n) (ball 0 d.rAShrunk) :=
    (differentiableOn_const _).mul (hQ2 0 (mem_closedBall_self (by linarith))).1
  have hTn_d : DifferentiableOn ℂ (d.Tn n) (ball 0 d.rAShrunk) :=
    (differentiableOn_const _).mul (((differentiableOn_const _).mul hA1d).add hD1d)
  have hcoeff_bd : ∀ a ∈ ball (0 : ℂ) d.rAShrunk,
      ‖d.Cn n a‖ ≤ M_C ∧ ‖d.Qn n a‖ ≤ M_Q ∧ ‖d.Tn n a‖ ≤ M_T := by
    intro a ha
    have ha_ra : a ∈ ball (0 : ℂ) d.r_a := hsub ha
    have ha_rc : a ∈ closedBall (0 : ℂ) (rc d) :=
      mem_closedBall_zero_iff.2 ((mem_ball_zero_iff.1 ha).le.trans
        ((min_le_right _ _).trans (by unfold rc; linarith [sq_nonneg d.s₁])))
    have hna_rc : -a ∈ closedBall (0 : ℂ) (rc d) := by simpa using ha_rc
    have hnah_rc : -d.aHat n a ∈ closedBall (0 : ℂ) (rc d) :=
      mem_closedBall_zero_iff.2 (c_ball d hn ha).1
    have hdiff_c : -d.aHat n a - (-a) = -((n⁻¹ : ℂ) * d.ψ n a) := by
      unfold HalfCubicData.aHat; ring
    have hELip : ‖d.E n (-d.aHat n a) a - d.E n (-a) a‖ ≤ L_E * d.M_ψ * n⁻¹ := by
      have hl := holo_lipschitz_ball (by linarith) (by linarith : rc d < r0 d)
        ((d.hE_q n a hn1 ha_ra).mono (ball_subset_ball h7.le))
        (fun ζ hζ => d.hE_bd n ζ a hn1 (ball_subset_ball h7.le hζ) ha_ra) hnah_rc hna_rc
      have hψ := d.hψ_bd n a hn1 ha_ra
      rw [hdiff_c, norm_neg, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hn0.le] at hl
      calc ‖d.E n (-d.aHat n a) a - d.E n (-a) a‖
          ≤ L_E * (n⁻¹ * ‖d.ψ n a‖) := hl
        _ ≤ L_E * (n⁻¹ * d.M_ψ) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hψ (by positivity)) hLE0
        _ = L_E * d.M_ψ * n⁻¹ := by ring
    have hA0_bd : ‖A0 d n a - 1‖ ≤ (L_E * d.M_ψ + K_E) * n⁻¹ := by
      calc ‖A0 d n a - 1‖ ≤ ‖d.E n (-d.aHat n a) a - d.E n (-a) a‖ + ‖d.E n (-a) a - 1‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ L_E * d.M_ψ * n⁻¹ + K_E * n⁻¹ := add_le_add hELip (hEnorm n a hn1 ha_ra)
        _ = (L_E * d.M_ψ + K_E) * n⁻¹ := by ring
    have hOLip : ‖d.O n (-d.aHat n a) a - d.O n (-a) a‖ ≤ L_O * d.M_ψ * n⁻¹ := by
      have hl := holo_lipschitz_ball (by linarith) (by linarith : rc d < r0 d)
        ((d.hO_q n a hn1 ha_ra).mono (ball_subset_ball h7.le))
        (fun ζ hζ => d.hO_bd n ζ a hn1 (ball_subset_ball h7.le hζ) ha_ra) hnah_rc hna_rc
      have hψ := d.hψ_bd n a hn1 ha_ra
      rw [hdiff_c, norm_neg, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hn0.le] at hl
      calc ‖d.O n (-d.aHat n a) a - d.O n (-a) a‖
          ≤ L_O * (n⁻¹ * ‖d.ψ n a‖) := hl
        _ ≤ L_O * (n⁻¹ * d.M_ψ) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hψ (by positivity)) hLO0
        _ = L_O * d.M_ψ * n⁻¹ := by ring
    have hA1_bd : ‖A1 d n a‖ ≤ (L_O * d.M_ψ + K_O) * n⁻¹ := by
      calc ‖A1 d n a‖ = ‖d.O n (-d.aHat n a) a‖ := rfl
        _ ≤ ‖d.O n (-d.aHat n a) a - d.O n (-a) a‖ + ‖d.O n (-a) a‖ :=
            norm_le_norm_sub_add (d.O n (-d.aHat n a) a) (d.O n (-a) a)
        _ ≤ L_O * d.M_ψ * n⁻¹ + K_O * n⁻¹ := add_le_add hOLip (hOnorm n a hn1 ha_ra)
        _ = (L_O * d.M_ψ + K_O) * n⁻¹ := by ring
    have hn_abs : ‖(n : ℂ)‖ = n := by rw [Complex.norm_real, Real.norm_of_nonneg hn0.le]
    refine ⟨?_, ?_, ?_⟩
    · unfold HalfCubicData.Cn
      calc ‖(n : ℂ) * (A0 d n a - 1) + D0 d n a‖
          ≤ ‖(n : ℂ) * (A0 d n a - 1)‖ + ‖D0 d n a‖ := norm_add_le _ _
        _ = n * ‖A0 d n a - 1‖ + ‖D0 d n a‖ := by rw [norm_mul, hn_abs]
        _ ≤ n * ((L_E * d.M_ψ + K_E) * n⁻¹) + MDe d :=
            add_le_add (mul_le_mul_of_nonneg_left hA0_bd hn0.le) (hDbd a ha).1
        _ = M_C := by field_simp [hn0.ne']; dsimp [M_C]
    · unfold HalfCubicData.Qn
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left ((hQ1 a ha).2.2.1 0 (mem_closedBall_self (by linarith))).1
        (by positivity)
    · unfold HalfCubicData.Tn
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc ‖(n : ℂ) * A1 d n a + D1 d n a‖
          ≤ ‖(n : ℂ) * A1 d n a‖ + ‖D1 d n a‖ := norm_add_le _ _
        _ = n * ‖A1 d n a‖ + ‖D1 d n a‖ := by rw [norm_mul, hn_abs]
        _ ≤ n * ((L_O * d.M_ψ + K_O) * n⁻¹) + MDo d :=
            add_le_add (mul_le_mul_of_nonneg_left hA1_bd hn0.le) (hDbd a ha).2
        _ = L_O * d.M_ψ + K_O + MDo d := by field_simp [hn0.ne']
  have hcoeff_real : ∀ a : ℝ, |a| < d.rAShrunk →
      (d.Cn n a).im = 0 ∧ (d.Qn n a).im = 0 ∧ (d.Tn n a).im = 0 := fun a ha => by
    obtain ⟨ha0i, ha1i⟩ := hAreal a ha
    obtain ⟨hd0i, hd1i⟩ := hDreal a ha
    have hqe0i : (Qe d n 0 a).im = 0 := by simpa using (hQ3 0 a (by rw [abs_zero]; linarith) ha).1
    refine ⟨?_, ?_, ?_⟩
    · unfold HalfCubicData.Cn; simp [ha0i, hd0i]
    · unfold HalfCubicData.Qn; simp [Complex.mul_im, hqe0i]
    · unfold HalfCubicData.Tn; simp [Complex.mul_im, ha1i, hd1i]
  refine ⟨hCn_d, hQn_d, hTn_d, hcoeff_bd, hcoeff_real, ?_⟩
  intro a ha lam R R₀ u hR1 hRR hUR
  set ch := fsChain hR1 hRR hUR
  have ha_ball : (a : ℂ) ∈ ball (0 : ℂ) d.rAShrunk := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact ha
  obtain ⟨hl0, hl1, hl2, hl3, hl4, hl5, _⟩ := rpow_lam_rels hn1
  obtain ⟨_, _, _, hU_eq⟩ := uReal_facts d hn ha
  have hlamR₀ : lam * R₀ = Rs d := mul_div_cancel₀ _ hl0.ne'
  have hq_mem : ∀ w ∈ ball (0 : ℂ) R₀, ‖(lam : ℂ) * w‖ ^ 2 < rsSq d ∧
      ((lam : ℂ) * w) ^ 2 ∈ ball (0 : ℂ) (r3 d) ∧
      ((lam : ℂ) * w) ^ 2 ∈ ball (0 : ℂ) (r2 d) ∧
      ((lam : ℂ) * w) ^ 2 ∈ ball (0 : ℂ) (r1 d) ∧
      ((lam : ℂ) * w) ^ 2 ∈ ball (0 : ℂ) (r0 d) := by
    intro w hw
    have hnw : ‖(lam : ℂ) * w‖ < Rs d := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hl0.le]
      calc lam * ‖w‖ < lam * R₀ := mul_lt_mul_of_pos_left (mem_ball_zero_iff.1 hw) hl0
        _ = Rs d := hlamR₀
    have hsq : ‖(lam : ℂ) * w‖ ^ 2 < rsSq d := by
      rw [← hrs]; exact pow_lt_pow_left₀ hnw (norm_nonneg _) two_ne_zero
    have hnq : ‖((lam : ℂ) * w) ^ 2‖ < rsSq d := by rw [norm_pow]; exact hsq
    refine ⟨hsq, ?_, ?_, ?_, ?_⟩ <;> rw [mem_ball_zero_iff] <;> linarith only [hnq, h3, h4, h5, h6]
  have hc_b := c_ball d hn ha_ball
  obtain ⟨hqE_d, hqO_d, hbdQ, hbdQD⟩ := hQ1 a ha_ball
  obtain ⟨hDe_d, hDo_d, hD_bd⟩ := hD1 a ha_ball
  set G₁ : ℂ → ℂ := fun w => Qe d n (((lam : ℂ) * w) ^ 2) a +
    Complex.I * ((lam : ℂ) * w) * Qo d n (((lam : ℂ) * w) ^ 2) a
  set G₁' : ℂ → ℂ := fun w =>
    2 * (lam : ℂ) ^ 2 * w * deriv (fun ζ => Qe d n ζ a) (((lam : ℂ) * w) ^ 2) +
    Complex.I * (lam : ℂ) * Qo d n (((lam : ℂ) * w) ^ 2) a +
    Complex.I * 2 * (lam : ℂ) ^ 3 * w ^ 2 * deriv (fun ζ => Qo d n ζ a) (((lam : ℂ) * w) ^ 2)
  have hL_B := fs_first_div_expand d hn ha rfl hlamR₀ ch
  have hG₁_der : ∀ w ∈ ball (0 : ℂ) R₀, HasDerivAt G₁ (G₁' w) w := fun w hw =>
    hasDerivAt_even_odd_shift (fun z hz => (hq_mem z hz).2.2.2.2) hqE_d hqO_d w hw
  have hG₁'_cont : ContinuousOn G₁' (ball 0 R₀) :=
    continuousOn_even_odd_deriv (fun z hz => (hq_mem z hz).2.2.2.2) hqE_d hqO_d
  have hG₁_bd : ∀ w ∈ ball (0 : ℂ) R₀, ‖G₁ w‖ ≤ MQe d + Rs d * MQo d := fun w hw => by
    have hq1 := ball_subset_closedBall (hq_mem w hw).2.2.2.1
    have hlw : ‖(lam : ℂ) * w‖ ≤ Rs d := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hl0.le]
      calc lam * ‖w‖ ≤ lam * R₀ := mul_le_mul_of_nonneg_left (mem_ball_zero_iff.1 hw).le hl0.le
        _ = Rs d := hlamR₀
    dsimp [G₁]
    calc ‖Qe d n (((lam : ℂ) * w) ^ 2) a + Complex.I * ((lam : ℂ) * w) * Qo d n (((lam : ℂ) * w) ^ 2) a‖
        ≤ MQe d + 1 * Rs d * MQo d := by
          refine (norm_add_le _ _).trans ?_; rw [norm_mul, norm_mul, Complex.norm_I]
          gcongr; exact (hbdQ _ hq1).1; exact (hbdQ _ hq1).2
      _ = MQe d + Rs d * MQo d := by ring
  have hG₁'_bd : ∀ w ∈ ball (0 : ℂ) R₀, ‖G₁' w‖ ≤
      lam * (2 * Rs d * MQeD d + MQo d + 2 * Rs d ^ 2 * MQoD d) := fun w hw => by
    have hq1 := ball_subset_closedBall (hq_mem w hw).2.2.2.1
    have hq2 := ball_subset_closedBall (hq_mem w hw).2.2.1
    dsimp [G₁']
    calc ‖2 * (lam : ℂ) ^ 2 * w * deriv (fun ζ => Qe d n ζ a) (((lam : ℂ) * w) ^ 2) +
            Complex.I * (lam : ℂ) * Qo d n (((lam : ℂ) * w) ^ 2) a +
            Complex.I * 2 * (lam : ℂ) ^ 3 * w ^ 2 * deriv (fun ζ => Qo d n ζ a) (((lam : ℂ) * w) ^ 2)‖
        ≤ 2 * lam ^ 2 * ‖w‖ * ‖deriv (fun ζ => Qe d n ζ a) (((lam : ℂ) * w) ^ 2)‖ +
            lam * ‖Qo d n (((lam : ℂ) * w) ^ 2) a‖ +
            2 * lam ^ 3 * ‖w‖ ^ 2 * ‖deriv (fun ζ => Qo d n ζ a) (((lam : ℂ) * w) ^ 2)‖ := by
          refine (norm_add₃_le).trans (add_le_add_three ?_ ?_ ?_) <;>
          simp only [norm_mul, norm_pow, Complex.norm_I, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos hl0, show ‖(2 : ℂ)‖ = 2 by norm_num, one_mul, mul_assoc] <;>
          exact le_rfl
      _ ≤ lam * (2 * Rs d * MQeD d + MQo d + 2 * Rs d ^ 2 * MQoD d) :=
          norm_even_odd_deriv_le hl0 hlamR₀ (hbdQ _ hq1).2 (hbdQD _ hq2).1 (hbdQD _ hq2).2
            (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (mem_ball_zero_iff.1 hw) hRs0
  have hibp₁ := fs_ibp_eval hR1 hUR ch (by positivity) (by positivity) hG₁_der hG₁'_cont hG₁_bd hG₁'_bd
  have hRe_d : DifferentiableOn ℂ (fun q => Re2 d n q a) (ball 0 (r2 d)) :=
    differentiableOn_divQ_fst (by linarith) h5 hDe_d hc_b.2.2.1
  have hRo_d : DifferentiableOn ℂ (fun q => Ro2 d n q a) (ball 0 (r2 d)) :=
    differentiableOn_divQ_fst (by linarith) h5 hDo_d hc_b.2.2.1
  have hbdR2 : ∀ q ∈ closedBall (0 : ℂ) (r3 d), ‖Re2 d n q a‖ ≤ MRe d ∧ ‖Ro2 d n q a‖ ≤ MRo d :=
    fun q hq => by
    have hqr : ‖q‖ ≤ r3 d := mem_closedBall_zero_iff.1 hq
    have hcr : ‖-d.aHat n a‖ ≤ r3 d := hc_b.1.trans (by linarith)
    refine ⟨norm_divQ_le (by linarith) h4 (fun ζ hζ => (hD_bd ζ (sphere_subset_closedBall hζ)).1) hcr hqr,
      norm_divQ_le (by linarith) h4 (fun ζ hζ => (hD_bd ζ (sphere_subset_closedBall hζ)).2) hcr hqr⟩
  have hbdRD2 : ∀ q ∈ ball (0 : ℂ) (rsSq d), ‖deriv (fun ζ => Re2 d n ζ a) q‖ ≤ MReD d ∧
      ‖deriv (fun ζ => Ro2 d n ζ a) q‖ ≤ MRoD d := fun q hq => by
    have hqr : ‖q‖ ≤ rsSq d := (mem_ball_zero_iff.1 hq).le
    refine ⟨cauchy_deriv_bound (by linarith) h3 h4 hRe_d hqr (fun ζ hζ =>
        (hbdR2 ζ (sphere_subset_closedBall hζ)).1),
      cauchy_deriv_bound (by linarith) h3 h4 hRo_d hqr (fun ζ hζ =>
        (hbdR2 ζ (sphere_subset_closedBall hζ)).2)⟩
  set G₂ : ℂ → ℂ := fun w => Re2 d n (((lam : ℂ) * w) ^ 2) a +
    Complex.I * ((lam : ℂ) * w) * Ro2 d n (((lam : ℂ) * w) ^ 2) a
  have hI_split : ∀ w ∈ ball (0 : ℂ) R₀, w ≠ 0 →
      Complex.I * (G₁ w / (2 * w) + G₁' w) =
        (Qe d n 0 a / 2) * (Complex.I / w) +
          ((lam : ℂ) * D0 d n a) * 1 +
          ((lam : ℂ) ^ 2 * D1 d n a) * (Complex.I * w) +
          (lam : ℂ) ^ 3 * (G₂ w * ((kap : ℂ) * u + w ^ 2)) := by
    intro w hw hw0
    have hq1 := (hq_mem w hw).2.2.2.1
    have hq2 := (hq_mem w hw).2.2.1
    have hdiv0 := divQ_eq (by linarith : 0 < r1 d) h6 hqE_d (mem_ball_self (by linarith)) hq1
    have hDe_q := divQ_eq (by linarith : 0 < r2 d) h5 hDe_d hc_b.2.2.1 hq2
    have hDo_q := divQ_eq (by linarith : 0 < r2 d) h5 hDo_d hc_b.2.2.1 hq2
    have hqe_eq : Qe d n (((lam : ℂ) * w) ^ 2) a =
        Qe d n 0 a + ((lam : ℂ) * w) ^ 2 * Qe0 d n (((lam : ℂ) * w) ^ 2) a := by
      unfold Qe0; rw [sub_zero] at hdiv0; exact eq_add_of_sub_eq' hdiv0
    have hfac : ((lam : ℂ) * w) ^ 2 - (-d.aHat n a) = (lam : ℂ) ^ 2 * ((kap : ℂ) * u + w ^ 2) := by
      rw [sub_neg_eq_add, ← hU_eq]; ring
    have hDe_eq : De d n (((lam : ℂ) * w) ^ 2) a = D0 d n a +
        (lam : ℂ) ^ 2 * ((kap : ℂ) * u + w ^ 2) * Re2 d n (((lam : ℂ) * w) ^ 2) a := by
      unfold D0 Re2; rw [← hfac]; exact (eq_add_of_sub_eq' hDe_q).trans (by ring)
    have hDo_eq : Do d n (((lam : ℂ) * w) ^ 2) a = D1 d n a +
        (lam : ℂ) ^ 2 * ((kap : ℂ) * u + w ^ 2) * Ro2 d n (((lam : ℂ) * w) ^ 2) a := by
      unfold D1 Ro2; rw [← hfac]; exact (eq_add_of_sub_eq' hDo_q).trans (by ring)
    have hbase : Complex.I * (G₁ w / (2 * w) + G₁' w) = (Qe d n 0 a / 2) * (Complex.I / w) +
        (lam : ℂ) * (De d n (((lam : ℂ) * w) ^ 2) a +
          Complex.I * ((lam : ℂ) * w) * Do d n (((lam : ℂ) * w) ^ 2) a) := by
      dsimp [G₁, G₁']; unfold De Do; rw [hqe_eq]; field_simp [hw0]; ring_nf; simp [Complex.I_sq]; ring
    rw [hbase, hDe_eq, hDo_eq]; dsimp [G₂]; ring
  have hb_1 : ch.B3 (fun w => csr w * (1 : ℂ)) 0 1 0 :=
    b3_csr_bounded ch zero_le_one continuousOn_const (fun _ _ => by simp)
  have hb_iw : ch.B3 (fun w => csr w * (Complex.I * w)) 0 0 1 := b3_csr_iw ch
  have hb_idiv : ch.B3 (fun w => csr w * (Complex.I / w)) 1 0 0 := b3_csr_idiv ch
  have hG₂_B3 := b3_even_odd_quad ch hl0 hlamR₀ hMRe0 hMRo0 hRs0 (fun w hw => (hq_mem w hw).2.2.1)
    hRe_d hRo_d (fun w hw => (hbdR2 _ (ball_subset_closedBall (hq_mem w hw).2.1)).1)
    (fun w hw => (hbdR2 _ (ball_subset_closedBall (hq_mem w hw).2.1)).2)
  have hI_congr : ch.intE u (fun w => csr w * (Complex.I * (G₁ w / (2 * w) + G₁' w))) =
      ch.intE u (fun w => csr w * (((Qe d n 0 a / 2) * (Complex.I / w) +
        ((lam : ℂ) * D0 d n a) * 1 + ((lam : ℂ) ^ 2 * D1 d n a) * (Complex.I * w)) +
        (lam : ℂ) ^ 3 * (G₂ w * ((kap : ℂ) * u + w ^ 2)))) :=
    chain3_intE_congr_ne_zero ch u
      (((hb_idiv.smul _).add (hb_1.smul _)).add (hb_iw.smul _) |>.add (hG₂_B3.smul _))
      (fun z hz hre hz0 => (continuousAt_csr (Or.inl hre)).mul (by
        have hG₁c : ContinuousAt G₁ z := (hG₁_der z hz).differentiableAt.continuousAt
        have hG₁'c : ContinuousAt G₁' z := hG₁'_cont.continuousAt (isOpen_ball.mem_nhds hz)
        exact ((hG₁c.div (continuousAt_const.mul continuousAt_id) (by simp [hz0])).add hG₁'c).const_mul _))
      (fun z hz hre hz0 => (continuousAt_csr (Or.inl hre)).mul (by
        have hq2 := (hq_mem z hz).2.2.1
        have hsq : ContinuousAt (fun w : ℂ => ((lam : ℂ) * w) ^ 2) z :=
          ((continuous_const.mul continuous_id).pow 2).continuousAt
        have hRe_c : ContinuousAt (fun w => Re2 d n (((lam : ℂ) * w) ^ 2) a) z :=
          ((hRe_d.differentiableAt (isOpen_ball.mem_nhds hq2)).continuousAt).comp hsq
        have hRo_c : ContinuousAt (fun w => Ro2 d n (((lam : ℂ) * w) ^ 2) a) z :=
          ((hRo_d.differentiableAt (isOpen_ball.mem_nhds hq2)).continuousAt).comp hsq
        have hG₂c : ContinuousAt G₂ z :=
          hRe_c.add ((continuous_const.mul (continuous_const.mul continuous_id)).continuousAt.mul hRo_c)
        exact ((((continuousAt_const.mul (continuousAt_const.div continuousAt_id hz0)).add
          continuousAt_const).add (continuousAt_const.mul (continuousAt_const.mul continuousAt_id))).add
          (continuousAt_const.mul (hG₂c.mul (continuousAt_const.add (continuous_pow 2 z).continuousAt))))))
      (fun z hz _ hz0 => by rw [hI_split z hz hz0]; ring)
  have hQe0_im : (Qe d n 0 a / 2).im = 0 := by
    have h0 := (hQ3 0 a (by rw [abs_zero]; linarith) ha).1; simp [Complex.div_im, h0]
  have hL_I : fsOpCh ch u (fun w => Complex.I * (G₁ w / (2 * w) + G₁' w)) =
      (Qe d n 0 a).re / 2 * fsOpCh ch u (fun w => Complex.I / w) +
        lam * (D0 d n a).re * fsOpCh ch u (fun _ => 1) +
        lam ^ 2 * (D1 d n a).re * fsOpCh ch u (fun w => Complex.I * w) +
        lam ^ 3 * fsOpCh ch u (fun w => G₂ w * ((kap : ℂ) * u + w ^ 2)) := by
    have heqOp : fsOpCh ch u (fun w => Complex.I * (G₁ w / (2 * w) + G₁' w)) =
        fsOpCh ch u (fun w => ((Qe d n 0 a / 2) * (Complex.I / w) +
          ((lam : ℂ) * D0 d n a) * 1 + ((lam : ℂ) ^ 2 * D1 d n a) * (Complex.I * w)) +
          (lam : ℂ) ^ 3 * (G₂ w * ((kap : ℂ) * u + w ^ 2))) := by
      unfold fsOpCh; rw [hI_congr]; simp only [mul_add, ← mul_assoc]; congr 2; ext w; ring
    rw [heqOp, fsOpCh_add ch u (((hb_idiv.smul _).add (hb_1.smul _)).add (hb_iw.smul _)) (hG₂_B3.smul _),
      fsOpCh_add ch u ((hb_idiv.smul _).add (hb_1.smul _)) (hb_iw.smul _),
      fsOpCh_add ch u (hb_idiv.smul _) (hb_1.smul _),
      fsOpCh_real_mul ch u hQe0_im,
      fsOpCh_real_mul ch u (by simp [Complex.mul_im, (hDreal a ha).1] : ((lam : ℂ) * D0 d n a).im = 0),
      fsOpCh_real_mul ch u (by norm_cast; simp [Complex.mul_im, (hDreal a ha).2] : ((lam : ℂ) ^ 2 * D1 d n a).im = 0),
      fsOpCh_real_mul ch u (by norm_cast; simp : ((lam : ℂ) ^ 3).im = 0)]
    simp only [Complex.re_ofReal_mul, ← Complex.ofReal_pow, Complex.ofReal_re]; ring
  have hG₂_ibp := fs_ibp_shift_bound hR1 hUR hl0 hl1 d.hs₁ hRs0 rfl hlamR₀ ch (hmom hR1 hRR hUR) hCm
    (h3.trans h4) hrs.le hRe_d hRo_d
    (fun q hq => (hbdR2 q (ball_subset_closedBall (ball_subset_ball h3.le hq))).1)
    (fun q hq => (hbdR2 q (ball_subset_closedBall (ball_subset_ball h3.le hq))).2)
    (fun q hq => (hbdRD2 q hq).1) (fun q hq => (hbdRD2 q hq).2) hMRe0 hMRo0 hMReD0 hMRoD0
  have hG₂_bd5 : lam ^ 5 * |fsOpCh ch u (fun w => G₂ w * ((kap : ℂ) * u + w ^ 2))| ≤
      C_ibp2 * lam ^ 5 := by
    have hlam5_le : lam ^ 5 ≤ 1 := pow_le_one₀ hl0.le hl1
    calc lam ^ 5 * |fsOpCh ch u (fun w => G₂ w * ((kap : ℂ) * u + w ^ 2))|
        ≤ lam ^ 5 * ((1 / √π) * ((MRe d + Rs d * MRo d) * (288 / d.s₁ ^ 5) * lam ^ 5 +
            ((MRe d / 2) * Cm + (3 / 2 * MRo d + 2 * Rs d ^ 2 * MRoD d) * Cm +
              (2 * MReD d) * (Cm * Real.sqrt (1 + d.s₁ ^ 2 / 16))))) := by gcongr
      _ ≤ lam ^ 5 * C_ibp2 := by
            gcongr; dsimp [C_ibp2]
            calc (1 / √π) * ((MRe d + Rs d * MRo d) * (288 / d.s₁ ^ 5) * lam ^ 5 + _)
                ≤ (1 / √π) * ((MRe d + Rs d * MRo d) * (288 / d.s₁ ^ 5) * 1 + _) := by gcongr
              _ = C_ibp2 := by ring
      _ = C_ibp2 * lam ^ 5 := by ring
  have hs_1 := fs_scalar_one (by linarith : 0 < R₀) hR1 hRR hUR ch
  have hs_w := fs_scalar_Iw (by linarith : 0 < R₀) hR1 hRR hUR ch
  have hs_d := fs_scalar_Idiv (by linarith : 0 < R₀) hR1 hRR hUR ch
  have hTail := exp_cubic_tail_bound hR1
  have hR5 : 288 / R ^ 5 = (288 / d.s₁ ^ 5) * lam ^ 5 := by
    dsimp [R]; rw [div_pow]; field_simp [d.hs₁.ne', hl0.ne']
  have hR6 : 288 / R ^ 6 = (288 / d.s₁ ^ 6) * lam ^ 6 := by
    dsimp [R]; rw [div_pow]; field_simp [d.hs₁.ne', hl0.ne']
  have hexp6 : Real.exp (-(R ^ 3 / 12)) ≤ (288 / d.s₁ ^ 6) * lam ^ 5 := by
    calc Real.exp (-(R ^ 3 / 12)) ≤ 288 / R ^ 6 := hTail.2
      _ = (288 / d.s₁ ^ 6) * lam ^ 6 := hR6
      _ = (288 / d.s₁ ^ 6) * lam ^ 5 * lam := by ring
      _ ≤ (288 / d.s₁ ^ 6) * lam ^ 5 * 1 := by gcongr
      _ = (288 / d.s₁ ^ 6) * lam ^ 5 := mul_one _
  have hCn_re : n⁻¹ * (d.Cn n a).re = (A0 d n a).re - 1 + lam ^ 3 * (D0 d n a).re := by
    unfold HalfCubicData.Cn
    have hn_r : ((n : ℂ) * (A0 d n a - 1) + D0 d n a).re = n * ((A0 d n a).re - 1) + (D0 d n a).re := by
      simp
    rw [hn_r, hl3]; field_simp [hn0.ne']; ring
  have hQn_re : n ^ (-(2 / 3 : ℝ)) * (d.Qn n a).re =
      lam ^ 2 * ((Qe d n 0 a).re / 2) * ((2 : ℝ) ^ (2 / 3 : ℝ) * π) := by
    unfold HalfCubicData.Qn
    rw [Complex.re_ofReal_mul, ← hl2]
    have h2p : (2 : ℝ) ^ (-(1 / 3 : ℝ)) = (2 : ℝ) ^ (2 / 3 : ℝ) / 2 := by
      calc (2 : ℝ) ^ (-(1 / 3 : ℝ)) = (2 : ℝ) ^ (2 / 3 + (-1 : ℝ)) := by norm_num
        _ = (2 : ℝ) ^ (2 / 3 : ℝ) * (2 : ℝ) ^ (-1 : ℝ) := Real.rpow_add two_pos _ _
        _ = (2 : ℝ) ^ (2 / 3 : ℝ) / 2 := by rw [Real.rpow_neg_one, div_eq_mul_inv]
    rw [h2p]; ring
  have hTn_re : n ^ (-(4 / 3 : ℝ)) * (d.Tn n a).re =
      (lam * (A1 d n a).re + lam ^ 4 * (D1 d n a).re) * (2 : ℝ) ^ (-(2 / 3 : ℝ)) := by
    unfold HalfCubicData.Tn
    rw [Complex.re_ofReal_mul]; simp only [Complex.add_re, Complex.re_ofReal_mul]
    have hl4' : lam ^ 4 = lam * lam ^ 3 := by ring
    rw [← hl4, hl4', hl3]; ring
  have hCn_le : |1 + n⁻¹ * (d.Cn n a).re| ≤ 1 + M_C := by
    calc |1 + n⁻¹ * (d.Cn n a).re| ≤ 1 + |n⁻¹ * (d.Cn n a).re| := abs_add_le _ _
      _ = 1 + n⁻¹ * |(d.Cn n a).re| := by rw [abs_mul, abs_of_pos (inv_pos.2 hn0)]
      _ ≤ 1 + 1 * M_C := by
          gcongr
          · exact inv_le_one_of_one_le₀ hn1
          · exact (Complex.abs_re_le_norm _).trans (hcoeff_bd a ha_ball).1
      _ = 1 + M_C := by ring
  have hTn_le : |lam * (A1 d n a).re + lam ^ 4 * (D1 d n a).re| ≤ (2 : ℝ) ^ (2 / 3 : ℝ) * M_T := by
    have hTbd : |(d.Tn n a).re| ≤ M_T := (Complex.abs_re_le_norm _).trans (hcoeff_bd a ha_ball).2.2
    have heqT : lam * (A1 d n a).re + lam ^ 4 * (D1 d n a).re =
        (2 : ℝ) ^ (2 / 3 : ℝ) * (n ^ (-(4 / 3 : ℝ)) * (d.Tn n a).re) := by
      rw [hTn_re, ← mul_assoc, mul_comm ((2 : ℝ) ^ (2 / 3 : ℝ)) _, mul_assoc,
        ← Real.rpow_add two_pos]; norm_num
    rw [heqT, abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos two_pos _),
      abs_of_pos (Real.rpow_pos_of_pos hn0 _)]
    have hn4 : n ^ (-(4 / 3 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num)
    calc (2 : ℝ) ^ (2 / 3 : ℝ) * (n ^ (-(4 / 3 : ℝ)) * |(d.Tn n a).re|)
        ≤ (2 : ℝ) ^ (2 / 3 : ℝ) * (1 * M_T) := by gcongr
      _ = (2 : ℝ) ^ (2 / 3 : ℝ) * M_T := by ring
  have hQe_le : |(Qe d n 0 a).re / 2| ≤ MQe d / 2 := by
    rw [abs_div, abs_two]
    exact div_le_div_of_nonneg_right ((Complex.abs_re_le_norm _).trans
      ((hbdQ 0 (mem_closedBall_self (by linarith))).1)) (by norm_num)
  have hDecomp : fsOpCh ch u (fun w => d.B n a ((lam : ℂ) * w)) -
      (fsK u + n⁻¹ * (d.Cn n a).re * fsK u + n ^ (-(2 / 3 : ℝ)) * (d.Qn n a).re * fsJ u +
        n ^ (-(4 / 3 : ℝ)) * (d.Tn n a).re * fsKp u) =
      lam ^ 2 * (fsOpCh ch u (fun w => G₁ w * ((kap : ℂ) * u + w ^ 2)) -
        fsOpCh ch u (fun w => Complex.I * (G₁ w / (2 * w) + G₁' w))) +
      (1 + n⁻¹ * (d.Cn n a).re) * (fsOpCh ch u (fun _ => 1) - fsK u) +
      lam ^ 2 * ((Qe d n 0 a).re / 2) *
        (fsOpCh ch u (fun w => Complex.I / w) - (2 : ℝ) ^ (2 / 3 : ℝ) * π * fsJ u) +
      (lam * (A1 d n a).re + lam ^ 4 * (D1 d n a).re) *
        (fsOpCh ch u (fun w => Complex.I * w) - (2 : ℝ) ^ (-(2 / 3 : ℝ)) * fsKp u) +
      lam ^ 5 * fsOpCh ch u (fun w => G₂ w * ((kap : ℂ) * u + w ^ 2)) := by
    rw [hL_B, hL_I, hCn_re, hQn_re, hTn_re]; ring
  rw [hDecomp]
  have hp1 : |lam ^ 2 * (fsOpCh ch u (fun w => G₁ w * ((kap : ℂ) * u + w ^ 2)) -
      fsOpCh ch u (fun w => Complex.I * (G₁ w / (2 * w) + G₁' w)))| ≤
      (1 / √π) * (MQe d + Rs d * MQo d) * (288 / d.s₁ ^ 5) * lam ^ 5 := by
    rw [abs_mul, abs_of_pos (sq_pos_of_pos hl0)]
    calc lam ^ 2 * |fsOpCh ch u (fun w => G₁ w * ((kap : ℂ) * u + w ^ 2)) -
          fsOpCh ch u (fun w => Complex.I * (G₁ w / (2 * w) + G₁' w))|
        ≤ 1 * ((1 / √π) * (MQe d + Rs d * MQo d) * (Real.sqrt R * Real.exp (-(R ^ 3 / 12)))) := by
          gcongr
          · nlinarith only [hl0, hl1]
          · exact hibp₁.trans_eq (by ring)
      _ ≤ (1 / √π) * (MQe d + Rs d * MQo d) * ((288 / d.s₁ ^ 5) * lam ^ 5) := by
          rw [one_mul]; gcongr; exact hTail.1.trans_eq hR5
      _ = (1 / √π) * (MQe d + Rs d * MQo d) * (288 / d.s₁ ^ 5) * lam ^ 5 := by ring
  have hp2 : |(1 + n⁻¹ * (d.Cn n a).re) * (fsOpCh ch u (fun _ => 1) - fsK u)| ≤
      (144 / √π) * (288 / d.s₁ ^ 6) * (1 + M_C) * lam ^ 5 := by
    rw [abs_mul]
    calc |1 + n⁻¹ * (d.Cn n a).re| * |fsOpCh ch u (fun _ => 1) - fsK u|
        ≤ (1 + M_C) * (144 / √π * Real.exp (-(R ^ 3 / 12))) :=
          mul_le_mul hCn_le hs_1 (abs_nonneg _) (by positivity)
      _ ≤ (1 + M_C) * (144 / √π * ((288 / d.s₁ ^ 6) * lam ^ 5)) := by gcongr
      _ = (144 / √π) * (288 / d.s₁ ^ 6) * (1 + M_C) * lam ^ 5 := by ring
  have hp3 : |lam ^ 2 * ((Qe d n 0 a).re / 2) *
      (fsOpCh ch u (fun w => Complex.I / w) - (2 : ℝ) ^ (2 / 3 : ℝ) * π * fsJ u)| ≤
      (578 / √π) * (288 / d.s₁ ^ 5) * (MQe d / 2) * lam ^ 5 := by
    rw [abs_mul, abs_mul, abs_of_pos (sq_pos_of_pos hl0)]
    have hl2_le : lam ^ 2 ≤ 1 := by nlinarith only [hl0, hl1]
    calc lam ^ 2 * |(Qe d n 0 a).re / 2| *
          |fsOpCh ch u (fun w => Complex.I / w) - (2 : ℝ) ^ (2 / 3 : ℝ) * π * fsJ u|
        ≤ 1 * (MQe d / 2) * (578 * Real.sqrt R / √π * Real.exp (-(R ^ 3 / 12))) := by gcongr
      _ = (578 / √π) * (MQe d / 2) * (Real.sqrt R * Real.exp (-(R ^ 3 / 12))) := by ring
      _ ≤ (578 / √π) * (MQe d / 2) * ((288 / d.s₁ ^ 5) * lam ^ 5) := by
          gcongr; exact hTail.1.trans_eq hR5
      _ = (578 / √π) * (288 / d.s₁ ^ 5) * (MQe d / 2) * lam ^ 5 := by ring
  have hp4 : |(lam * (A1 d n a).re + lam ^ 4 * (D1 d n a).re) *
      (fsOpCh ch u (fun w => Complex.I * w) - (2 : ℝ) ^ (-(2 / 3 : ℝ)) * fsKp u)| ≤
      (144 / √π) * (288 / d.s₁ ^ 6) * ((2 : ℝ) ^ (2 / 3 : ℝ) * M_T) * lam ^ 5 := by
    rw [abs_mul]
    calc |lam * (A1 d n a).re + lam ^ 4 * (D1 d n a).re| *
          |fsOpCh ch u (fun w => Complex.I * w) - (2 : ℝ) ^ (-(2 / 3 : ℝ)) * fsKp u|
        ≤ ((2 : ℝ) ^ (2 / 3 : ℝ) * M_T) * (144 / √π * Real.exp (-(R ^ 3 / 12))) :=
          mul_le_mul hTn_le hs_w (abs_nonneg _) (by positivity)
      _ ≤ ((2 : ℝ) ^ (2 / 3 : ℝ) * M_T) * (144 / √π * ((288 / d.s₁ ^ 6) * lam ^ 5)) := by gcongr
      _ = (144 / √π) * (288 / d.s₁ ^ 6) * ((2 : ℝ) ^ (2 / 3 : ℝ) * M_T) * lam ^ 5 := by ring
  have hp5 : |lam ^ 5 * fsOpCh ch u (fun w => G₂ w * ((kap : ℂ) * u + w ^ 2))| ≤
      C_ibp2 * lam ^ 5 := by
    rw [abs_mul, abs_of_pos (pow_pos hl0 5)]; exact hG₂_bd5
  rw [← hl5]
  have htri := (norm_add₄_le _ _ _ _).trans (add_le_add_four hp1 hp2 hp3 hp4)
  calc |_ + _ + _ + _ + _| ≤ |_ + _ + _ + _| + |_| := abs_add_le _ _
    _ ≤ C_rem * lam ^ 5 := by dsimp [C_rem]; linarith

/-- **Lemma FS.1 Part (2) (`fs:aux`)**: without saddle normalization,
`L_u[B_n] = C_n^*(a) K(u) + n^{-1/3} T_n^*(a) K'(u) + O(n^{-2/3})`. -/
theorem fs_aux (d : HalfCubicData) :
    ∃ M_C M_T C_rem : ℝ, 0 ≤ M_C ∧ 0 ≤ M_T ∧ 0 ≤ C_rem ∧
      ∀ n : ℝ, d.n₀ ≤ n →
        DifferentiableOn ℂ (d.CnStar n) (ball 0 d.rAShrunk) ∧
        DifferentiableOn ℂ (d.TnStar n) (ball 0 d.rAShrunk) ∧
        (∀ a ∈ ball (0 : ℂ) d.rAShrunk, ‖d.CnStar n a‖ ≤ M_C ∧ ‖d.TnStar n a‖ ≤ M_T) ∧
        (∀ a : ℝ, |a| < d.rAShrunk → (d.CnStar n a).im = 0 ∧ (d.TnStar n a).im = 0) ∧
        (∀ a : ℝ, |a| < d.rAShrunk →
          let lam := n ^ (-(1 / 3 : ℝ))
          let R := d.s₁ / lam
          let R₀ := Rs d / lam
          let u := d.uReal n a
          ∀ (hR1 : 1 ≤ R) (hRR : R < R₀) (hUR : kap * |u| ≤ R ^ 2 / 16),
          |fsOpCh (fsChain hR1 hRR hUR) u (fun w => d.B n a ((lam : ℂ) * w)) -
            ((d.CnStar n a).re * fsK u + n ^ (-(1 / 3 : ℝ)) * (d.TnStar n a).re * fsKp u)| ≤
            C_rem * n ^ (-(2 / 3 : ℝ))) := by
  obtain ⟨Cm, hCm, hmom⟩ := fsChain_momOK
  have ⟨_, _, h1, h2, h3, h4, h5, h6, h7, hss, hrs⟩ := radii_chain d
  have hRs0 : 0 ≤ Rs d := Real.sqrt_nonneg _
  have hME0 : 0 ≤ d.M_E := d.hM_E
  have hMO0 : 0 ≤ d.M_O := d.hM_O
  have hMQe0 : 0 ≤ MQe d := div_nonneg (mul_nonneg (by linarith) d.hM_E) (sq_nonneg _)
  have hMQo0 : 0 ≤ MQo d := div_nonneg (mul_nonneg (by linarith) d.hM_O) (sq_nonneg _)
  have hMQeD0 : 0 ≤ MQeD d := div_nonneg (mul_nonneg (by linarith) hMQe0) (sq_nonneg _)
  have hMQoD0 : 0 ≤ MQoD d := div_nonneg (mul_nonneg (by linarith) hMQo0) (sq_nonneg _)
  set M_C : ℝ := d.M_E
  set M_T : ℝ := (2 : ℝ) ^ (-(2 / 3 : ℝ)) * d.M_O
  set C_ibp1 : ℝ := (1 / √π) * ((MQe d + Rs d * MQo d) * (288 / d.s₁ ^ 5) +
    ((MQe d / 2) * Cm + (3 / 2 * MQo d + 2 * Rs d ^ 2 * MQoD d) * Cm +
      (2 * MQeD d) * (Cm * Real.sqrt (1 + d.s₁ ^ 2 / 16))))
  set C_rem : ℝ := (144 / √π) * (288 / d.s₁ ^ 6) * (M_C + d.M_O) + C_ibp1
  refine ⟨M_C, M_T, C_rem, hME0, by dsimp [M_T]; positivity,
    by dsimp only [C_rem, C_ibp1, M_C]; have := d.hs₁; positivity, ?_⟩
  intro n hn
  have ⟨hn1, _, _, _, _, _⟩ := aHat_facts d hn
  have ⟨hA0d, hA1d, hAbd, hAreal⟩ := A0_A1_facts d hn
  have ⟨hQ1, _, _⟩ := Q_facts d hn
  refine ⟨hA0d, (differentiableOn_const _).mul hA1d, ?_, ?_, ?_⟩
  · intro a ha
    refine ⟨(hAbd a ha).1, ?_⟩
    unfold HalfCubicData.TnStar
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (hAbd a ha).2 (by positivity)
  · intro a ha
    refine ⟨(hAreal a ha).1, ?_⟩
    unfold HalfCubicData.TnStar
    simp [Complex.mul_im, (hAreal a ha).2]
  · intro a ha lam R R₀ u hR1 hRR hUR
    set ch := fsChain hR1 hRR hUR
    have ha_ball : (a : ℂ) ∈ ball (0 : ℂ) d.rAShrunk := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact ha
    obtain ⟨hl0, hl1, hl2, _, _, _, _⟩ := rpow_lam_rels hn1
    have hlamR₀ : lam * R₀ = Rs d := mul_div_cancel₀ _ hl0.ne'
    obtain ⟨hqE_d, hqO_d, hbdQ, hbdQD⟩ := hQ1 a ha_ball
    have hL_B := fs_first_div_expand d hn ha rfl hlamR₀ ch
    have hG₁_ibp := fs_ibp_shift_bound hR1 hUR hl0 hl1 d.hs₁ hRs0 rfl hlamR₀ ch (hmom hR1 hRR hUR) hCm
      (h3.trans (h4.trans h5)) hrs.le (hqE_d.mono (ball_subset_ball h6.le)) (hqO_d.mono (ball_subset_ball h6.le))
      (fun q hq => (hbdQ q (ball_subset_closedBall hq)).1)
      (fun q hq => (hbdQ q (ball_subset_closedBall hq)).2)
      (fun q hq => (hbdQD q (mem_closedBall_zero_iff.2 ((mem_ball_zero_iff.1 hq).le.trans
        (by linarith : rsSq d ≤ r2 d)))).1)
      (fun q hq => (hbdQD q (mem_closedBall_zero_iff.2 ((mem_ball_zero_iff.1 hq).le.trans
        (by linarith : rsSq d ≤ r2 d)))).2)
      hMQe0 hMQo0 hMQeD0 hMQoD0
    have hs_1 := fs_scalar_one (by linarith : 0 < R₀) hR1 hRR hUR ch
    have hs_w := fs_scalar_Iw (by linarith : 0 < R₀) hR1 hRR hUR ch
    have hTail := (exp_cubic_tail_bound hR1).2
    have hR6 : 288 / R ^ 6 = (288 / d.s₁ ^ 6) * lam ^ 6 := by
      dsimp [R]; rw [div_pow]; field_simp [d.hs₁.ne', hl0.ne']
    have hexp2 : Real.exp (-(R ^ 3 / 12)) ≤ (288 / d.s₁ ^ 6) * lam ^ 2 := by
      have hl4_1 : lam ^ 4 ≤ 1 := pow_le_one₀ hl0.le hl1
      calc Real.exp (-(R ^ 3 / 12)) ≤ 288 / R ^ 6 := hTail
        _ = (288 / d.s₁ ^ 6) * lam ^ 2 * lam ^ 4 := by rw [hR6]; ring
        _ ≤ (288 / d.s₁ ^ 6) * lam ^ 2 * 1 := by gcongr
        _ = (288 / d.s₁ ^ 6) * lam ^ 2 := mul_one _
    have hTnStar_re : n ^ (-(1 / 3 : ℝ)) * (d.TnStar n a).re =
        lam * (A1 d n a).re * (2 : ℝ) ^ (-(2 / 3 : ℝ)) := by
      unfold HalfCubicData.TnStar; rw [Complex.re_ofReal_mul]; ring
    have hDecomp : fsOpCh ch u (fun w => d.B n a ((lam : ℂ) * w)) -
        ((d.CnStar n a).re * fsK u + n ^ (-(1 / 3 : ℝ)) * (d.TnStar n a).re * fsKp u) =
        (A0 d n a).re * (fsOpCh ch u (fun _ => 1) - fsK u) +
        (lam * (A1 d n a).re) * (fsOpCh ch u (fun w => Complex.I * w) - (2 : ℝ) ^ (-(2 / 3 : ℝ)) * fsKp u) +
        lam ^ 2 * fsOpCh ch u (fun w => (Qe d n (((lam : ℂ) * w) ^ 2) a +
          Complex.I * ((lam : ℂ) * w) * Qo d n (((lam : ℂ) * w) ^ 2) a) * ((kap : ℂ) * u + w ^ 2)) := by
      unfold HalfCubicData.CnStar; rw [hL_B, hTnStar_re]; ring
    rw [hDecomp]
    have hp1 : |(A0 d n a).re * (fsOpCh ch u (fun _ => 1) - fsK u)| ≤
        (144 / √π) * (288 / d.s₁ ^ 6) * M_C * lam ^ 2 := by
      rw [abs_mul]
      calc |(A0 d n a).re| * |fsOpCh ch u (fun _ => 1) - fsK u|
          ≤ M_C * (144 / √π * Real.exp (-(R ^ 3 / 12))) :=
            mul_le_mul ((Complex.abs_re_le_norm _).trans (hAbd a ha_ball).1) hs_1 (abs_nonneg _) hME0
        _ ≤ M_C * (144 / √π * ((288 / d.s₁ ^ 6) * lam ^ 2)) := by gcongr
        _ = (144 / √π) * (288 / d.s₁ ^ 6) * M_C * lam ^ 2 := by ring
    have hp2 : |(lam * (A1 d n a).re) * (fsOpCh ch u (fun w => Complex.I * w) -
        (2 : ℝ) ^ (-(2 / 3 : ℝ)) * fsKp u)| ≤
        (144 / √π) * (288 / d.s₁ ^ 6) * d.M_O * lam ^ 2 := by
      rw [abs_mul, abs_mul, abs_of_pos hl0]
      calc lam * |(A1 d n a).re| * |fsOpCh ch u (fun w => Complex.I * w) -
            (2 : ℝ) ^ (-(2 / 3 : ℝ)) * fsKp u|
          ≤ 1 * d.M_O * (144 / √π * Real.exp (-(R ^ 3 / 12))) := by
            gcongr; exact (Complex.abs_re_le_norm _).trans (hAbd a ha_ball).2
        _ ≤ 1 * d.M_O * (144 / √π * ((288 / d.s₁ ^ 6) * lam ^ 2)) := by gcongr
        _ = (144 / √π) * (288 / d.s₁ ^ 6) * d.M_O * lam ^ 2 := by ring
    have hp3 : |lam ^ 2 * fsOpCh ch u (fun w => (Qe d n (((lam : ℂ) * w) ^ 2) a +
        Complex.I * ((lam : ℂ) * w) * Qo d n (((lam : ℂ) * w) ^ 2) a) *
          ((kap : ℂ) * u + w ^ 2))| ≤ C_ibp1 * lam ^ 2 := by
      rw [abs_mul, abs_of_pos (sq_pos_of_pos hl0)]
      have hl5_1 : lam ^ 5 ≤ 1 := pow_le_one₀ hl0.le hl1
      refine mul_le_mul_of_nonneg_left (hG₁_ibp.trans ?_) (sq_nonneg lam)
      dsimp [C_ibp1]
      calc (1 / √π) * ((MQe d + Rs d * MQo d) * (288 / d.s₁ ^ 5) * lam ^ 5 + _)
          ≤ (1 / √π) * ((MQe d + Rs d * MQo d) * (288 / d.s₁ ^ 5) * 1 + _) := by gcongr
        _ = C_ibp1 := by ring
    rw [← hl2]
    refine (norm_add₃_le).trans ?_
    calc |(A0 d n a).re * _| + |(lam * (A1 d n a).re) * _| + |lam ^ 2 * _|
        ≤ (144 / √π) * (288 / d.s₁ ^ 6) * M_C * lam ^ 2 +
            (144 / √π) * (288 / d.s₁ ^ 6) * d.M_O * lam ^ 2 + C_ibp1 * lam ^ 2 :=
          add_le_add_three hp1 hp2 hp3
      _ = C_rem * lam ^ 2 := by dsimp [C_rem]; ring

end FineOrderSigned

end FormalResearch.SignUncertainty
