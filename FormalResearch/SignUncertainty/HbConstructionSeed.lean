module

public import FormalResearch.SignUncertainty.CeHbSeedGen

/-!
# Unconditional Rational–Airy Representation and `HBSeedSpec` for All `ShellHBData`

Extends `CeHbSeedGen.lean` (which handled `Odd D.S.card`) to `Even D.S.card`, packaging
`hbSeedSpec_of_shellHBData_all : ∀ D : ShellHBData, ...` and unconditional
`HasGenRationalAiryCoeffs` membership for `D.G` (`β₀₀ + β₁₁ > 0`) and `dslope (-D.G) D.tm` (`(0, 0)`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real BigOperators Polynomial

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

private lemma shellPoly_props_even (S : Finset ℝ) (hSne : S.Nonempty) :
    let B : ℝ := S.sup' hSne (fun t => |t|)
    let Q_S : ℝ[X] := ∏ t ∈ S, (Polynomial.X - Polynomial.C t)
    Q_S.Monic ∧ Q_S.natDegree = S.card ∧
    (∀ z : ℂ, Polynomial.aeval z Q_S = ∏ t ∈ S, (z - (t : ℂ))) ∧
    (∀ z : ℂ, Polynomial.aeval z Q_S = 0 → z.im = 0 ∧ ‖z‖ ≤ B) := by
  intro B Q_S
  have hmon : Q_S.Monic := Polynomial.monic_prod_of_monic S _ fun t _ => Polynomial.monic_X_sub_C t
  have hdeg : Q_S.natDegree = S.card := by
    dsimp [Q_S]
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun t _ => Polynomial.monic_X_sub_C t)]
    simp
  have haev : ∀ z : ℂ, Polynomial.aeval z Q_S = ∏ t ∈ S, (z - (t : ℂ)) := fun z => by
    dsimp [Q_S]
    simp only [map_prod, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Complex.coe_algebraMap]
  have hrt : ∀ z : ℂ, Polynomial.aeval z Q_S = 0 → z.im = 0 ∧ ‖z‖ ≤ B := by
    intro z hz
    rw [haev z, Finset.prod_eq_zero_iff] at hz
    obtain ⟨t, htS, hzt⟩ := hz
    have heq : z = (t : ℂ) := sub_eq_zero.mp hzt
    rw [heq, Complex.ofReal_im, Complex.norm_real, Real.norm_eq_abs]
    exact ⟨rfl, Finset.le_sup' (fun s => |s|) htS⟩
  exact ⟨hmon, hdeg, haev, hrt⟩

private lemma aeval_eq_airyPQc_even (p : ℝ[X]) (z : ℂ) : Polynomial.aeval z p = airyPQc p z := by
  unfold airyPQc
  rw [Polynomial.eval_map, Polynomial.aeval_def]

lemma shellHBData_Q_degree_of_even (D : ShellHBData) (hEven : Even D.S.card) :
    D.Q ≠ 0 ∧ 2 * D.Q.natDegree + 2 = D.S.card ∧
      (D.P = 0 ∨ 2 * D.P.natDegree + 2 ≤ D.S.card) := by
  rcases D.m_eq with ⟨_, hcard1⟩ | ⟨hQne, hcardm⟩
  · rw [hcard1] at hEven; exact absurd hEven (by decide)
  · unfold at47_m at hcardm
    have hnot_odd : D.S.card ≠ 2 * D.P.natDegree + 1 := by
      intro h
      rw [h] at hEven
      exact (Nat.not_even_iff_odd.mpr ⟨D.P.natDegree, by ring⟩) hEven
    have hmQ : D.S.card = 2 * D.Q.natDegree + 2 := by omega
    refine ⟨hQne, hmQ.symm, ?_⟩
    by_cases hP0 : D.P = 0
    · exact Or.inl hP0
    · right; omega

theorem hasGenRationalAiryCoeffs_shellHBData_G_even (D : ShellHBData) (hEven : Even D.S.card) :
    HasGenRationalAiryCoeffs D.G 0 (D.Q.leadingCoeff ^ 2) := by
  obtain ⟨hQne, hmQ, hPcase⟩ := shellHBData_Q_degree_of_even D hEven
  let B : ℝ := D.S.sup' D.S_nonempty (fun t => |t|)
  let Q_S : ℝ[X] := ∏ t ∈ D.S, (Polynomial.X - Polynomial.C t)
  obtain ⟨hQ_monic, hQ_deg, hQ_eq, hQ_rt⟩ := shellPoly_props_even D.S D.S_nonempty
  have hB : ∀ t ∈ D.S, |t| ≤ B := fun t ht => Finset.le_sup' (fun s => |s|) ht
  have hB0 : 0 ≤ B := (abs_nonneg D.tm).trans (hB D.tm D.tm_mem)
  have hm1 : 1 ≤ D.S.card := Finset.card_pos.mpr D.S_nonempty
  have hm2 : 2 ≤ D.S.card := by omega
  have hpos1 : (-1 : ℝ) ^ D.S.card = 1 := hEven.neg_one_pow
  let P00 : ℝ[X] := D.P ^ 2
  let P01 : ℝ[X] := Polynomial.C (2 : ℝ) * (D.P * D.Q)
  let P11 : ℝ[X] := D.Q ^ 2
  have hP00_deg : ∀ k, D.S.card ≤ k → P00.coeff k = 0 := fun k hk => by
    rcases hPcase with hP0 | hPdeg
    · simp [P00, hP0]
    · apply Polynomial.coeff_eq_zero_of_natDegree_lt
      have hsq : P00.natDegree ≤ 2 * D.P.natDegree := Polynomial.natDegree_pow_le
      omega
  have hP00_c1 : P00.coeff (D.S.card - 1) = 0 := by
    rcases hPcase with hP0 | hPdeg
    · simp [P00, hP0]
    · apply Polynomial.coeff_eq_zero_of_natDegree_lt
      have hsq : P00.natDegree ≤ 2 * D.P.natDegree := Polynomial.natDegree_pow_le
      omega
  have hP01_deg : ∀ k, D.S.card ≤ k → P01.coeff k = 0 := fun k hk => by
    rcases hPcase with hP0 | hPdeg
    · simp [P01, hP0]
    · apply Polynomial.coeff_eq_zero_of_natDegree_lt
      have hmul : (D.P * D.Q).natDegree ≤ D.P.natDegree + D.Q.natDegree := Polynomial.natDegree_mul_le
      have hcmul : P01.natDegree ≤ (D.P * D.Q).natDegree := by
        dsimp [P01]; exact (Polynomial.natDegree_mul_le).trans (by rw [Polynomial.natDegree_C, zero_add])
      omega
  have hP01_c1 : P01.coeff (D.S.card - 1) = 0 := by
    rcases hPcase with hP0 | hPdeg
    · simp [P01, hP0]
    · apply Polynomial.coeff_eq_zero_of_natDegree_lt
      have hmul : (D.P * D.Q).natDegree ≤ D.P.natDegree + D.Q.natDegree := Polynomial.natDegree_mul_le
      have hcmul : P01.natDegree ≤ (D.P * D.Q).natDegree := by
        dsimp [P01]; exact (Polynomial.natDegree_mul_le).trans (by rw [Polynomial.natDegree_C, zero_add])
      omega
  have hP11_deg : ∀ k, D.S.card - 1 ≤ k → P11.coeff k = 0 := fun k hk => by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have hsq : P11.natDegree ≤ 2 * D.Q.natDegree := Polynomial.natDegree_pow_le
    omega
  have hP11_c2 : P11.coeff (D.S.card - 2) = D.Q.leadingCoeff ^ 2 := by
    have hsq : (D.Q ^ 2).coeff (2 * D.Q.natDegree) = D.Q.leadingCoeff ^ 2 := by
      have hdeg2 : (D.Q ^ 2).natDegree = 2 * D.Q.natDegree := Polynomial.natDegree_pow D.Q 2
      have hlead : (D.Q ^ 2).leadingCoeff = D.Q.leadingCoeff ^ 2 := Polynomial.leadingCoeff_pow D.Q 2
      rw [← hdeg2, Polynomial.coeff_natDegree, hlead]
    simp only [P11, show D.S.card - 2 = 2 * D.Q.natDegree by omega, hsq]
  have hQ_lb : ∀ w : ℂ, 2 * B + 2 ≤ ‖w‖ → (1 / 2 : ℝ) ^ D.S.card * ‖w‖ ^ D.S.card ≤ ‖Polynomial.aeval (-w) Q_S‖ :=
    fun w hw => by rw [hQ_eq (-w)]; exact poly_prod_norm_ge D.S hB hw
  obtain ⟨C0, hC0, has0⟩ := poly_div_monic_coeff1 D.S.card hQ_lb hQ_monic hQ_deg hm1 hP00_deg
  obtain ⟨C1, hC1, has1⟩ := poly_div_monic_coeff1 D.S.card hQ_lb hQ_monic hQ_deg hm1 hP01_deg
  obtain ⟨C2, hC2, has2⟩ := poly_div_monic_coeff2 D.S.card hQ_lb hQ_monic hQ_deg hm2 hP11_deg
  simp only [hP00_c1, neg_zero, Complex.ofReal_zero, zero_mul, sub_zero] at has0
  simp only [hP01_c1, neg_zero, Complex.ofReal_zero, zero_mul, sub_zero] at has1
  rw [hP11_c2] at has2
  let R_star : ℝ := max 4 (2 * B + 2)
  have hR4 : 4 ≤ R_star := le_max_left _ _
  have hB_R : B ≤ R_star := by linarith [le_max_right (4 : ℝ) (2 * B + 2)]
  refine ⟨D.G_inAiryClass, R_star, max C0 (max C1 C2), P00, Q_S, P01, Q_S, P11, Q_S,
    hR4, by positivity, hQ_monic, hQ_monic, hQ_monic,
    fun z hz => ⟨(hQ_rt z hz).1, (hQ_rt z hz).2.trans hB_R⟩,
    fun z hz => ⟨(hQ_rt z hz).1, (hQ_rt z hz).2.trans hB_R⟩,
    fun z hz => ⟨(hQ_rt z hz).1, (hQ_rt z hz).2.trans hB_R⟩,
    fun z hz => ?_, fun w hw => ?_⟩
  · have hQnz : Polynomial.aeval z Q_S ≠ 0 := fun h0 => not_le_of_gt hz ((hQ_rt z h0).2.trans hB_R)
    have hpr_eq : at47_pr D.S z = Polynomial.aeval z Q_S := (hQ_eq z).symm
    have hG := D.G_prod_eq z
    rw [hpr_eq, hpos1] at hG
    apply mul_right_cancel₀ hQnz
    have hG_alg : D.G z * Polynomial.aeval z Q_S = airyPQN D.P D.Q z ^ 2 := by simpa using hG
    rw [hG_alg]
    have hsum :
        ((Polynomial.aeval z P00 / Polynomial.aeval z Q_S) * airyAiC z ^ 2 +
          (Polynomial.aeval z P01 / Polynomial.aeval z Q_S) * (airyAiC z * deriv airyAiC z) +
          (Polynomial.aeval z P11 / Polynomial.aeval z Q_S) * deriv airyAiC z ^ 2) *
          Polynomial.aeval z Q_S =
        Polynomial.aeval z P00 * airyAiC z ^ 2 +
          Polynomial.aeval z P01 * (airyAiC z * deriv airyAiC z) +
          Polynomial.aeval z P11 * deriv airyAiC z ^ 2 := by field_simp [hQnz]
    rw [hsum]
    dsimp [P00, P01, P11]
    simp only [airyPQN, map_pow, map_mul, aeval_C, Complex.coe_algebraMap, aeval_eq_airyPQc_even]
    norm_num; ring
  · have hw0 : ‖w‖ ^ (-2 : ℝ) ≥ 0 := by positivity
    have hw03 : ‖w‖ ^ (-3 : ℝ) ≥ 0 := by positivity
    refine ⟨?_, ?_, (has2 w hw).trans (mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) hw03)⟩
    · simpa only [Complex.ofReal_zero, zero_mul, sub_zero] using
        (has0 w hw).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hw0)
    · exact (has1 w hw).trans (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) hw0)

theorem hasGenRationalAiryCoeffs_terminal_cardinal_even (D : ShellHBData) (hEven : Even D.S.card) :
    HasGenRationalAiryCoeffs (dslope (fun z => -D.G z) (D.tm : ℂ)) 0 0 := by
  obtain ⟨_, hmQ, hPcase⟩ := shellHBData_Q_degree_of_even D hEven
  let B : ℝ := D.S.sup' D.S_nonempty (fun t => |t|)
  let Q_S : ℝ[X] := ∏ t ∈ D.S, (Polynomial.X - Polynomial.C t)
  obtain ⟨hQ_monic, hQ_deg, hQ_eq, hQ_rt⟩ := shellPoly_props_even D.S D.S_nonempty
  have hB : ∀ t ∈ D.S, |t| ≤ B := fun t ht => Finset.le_sup' (fun s => |s|) ht
  have hB_tm : |D.tm| ≤ B := hB D.tm D.tm_mem
  let Q_H : ℝ[X] := (Polynomial.X - Polynomial.C D.tm) * Q_S
  have hQH_monic : Q_H.Monic := (Polynomial.monic_X_sub_C D.tm).mul hQ_monic
  have hQH_deg : Q_H.natDegree = D.S.card + 1 := by
    dsimp [Q_H]
    rw [Polynomial.natDegree_mul (Polynomial.monic_X_sub_C D.tm).ne_zero hQ_monic.ne_zero,
      Polynomial.natDegree_X_sub_C, hQ_deg, add_comm]
  have hQH_eq : ∀ z : ℂ, Polynomial.aeval z Q_H = (z - (D.tm : ℂ)) * Polynomial.aeval z Q_S := fun z => by
    dsimp [Q_H]; simp only [map_mul, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Complex.coe_algebraMap]
  have hQH_lb : ∀ w : ℂ, 2 * B + 2 ≤ ‖w‖ →
      (1 / 2 : ℝ) ^ (D.S.card + 1) * ‖w‖ ^ (D.S.card + 1) ≤ ‖Polynomial.aeval (-w) Q_H‖ := fun w hw => by
    rw [hQH_eq (-w), norm_mul, hQ_eq (-w)]
    have htm_lb : 1 / 2 * ‖w‖ ≤ ‖-w - (D.tm : ℂ)‖ := by
      have htri := norm_sub_norm_le (-w) (D.tm : ℂ)
      have htB : ‖(D.tm : ℂ)‖ ≤ B := by rw [Complex.norm_real, Real.norm_eq_abs]; exact hB_tm
      rw [norm_neg] at htri; linarith
    have hQS_lb := poly_prod_norm_ge D.S hB hw
    calc (1 / 2 : ℝ) ^ (D.S.card + 1) * ‖w‖ ^ (D.S.card + 1)
        = (1 / 2 * ‖w‖) * ((1 / 2 : ℝ) ^ D.S.card * ‖w‖ ^ D.S.card) := by rw [pow_succ, pow_succ]; ring
      _ ≤ ‖-w - (D.tm : ℂ)‖ * ‖∏ t ∈ D.S, (-w - (t : ℂ))‖ :=
          mul_le_mul htm_lb hQS_lb (by positivity) (norm_nonneg _)
  let P00 : ℝ[X] := -D.P ^ 2
  let P01 : ℝ[X] := Polynomial.C (-2 : ℝ) * (D.P * D.Q)
  let P11 : ℝ[X] := -D.Q ^ 2
  have hP00_deg : ∀ k, D.S.card + 1 ≤ k → P00.coeff k = 0 := fun k hk => by
    rcases hPcase with hP0 | hPdeg
    · simp [P00, hP0]
    · apply Polynomial.coeff_eq_zero_of_natDegree_lt
      have hsq : P00.natDegree ≤ 2 * D.P.natDegree := by dsimp [P00]; rw [Polynomial.natDegree_neg]; exact Polynomial.natDegree_pow_le
      omega
  have hP00_c1 : P00.coeff (D.S.card + 1 - 1) = 0 := by
    rcases hPcase with hP0 | hPdeg
    · simp [P00, hP0]
    · apply Polynomial.coeff_eq_zero_of_natDegree_lt
      have hsq : P00.natDegree ≤ 2 * D.P.natDegree := by dsimp [P00]; rw [Polynomial.natDegree_neg]; exact Polynomial.natDegree_pow_le
      omega
  have hP01_deg : ∀ k, D.S.card + 1 ≤ k → P01.coeff k = 0 := fun k hk => by
    rcases hPcase with hP0 | hPdeg
    · simp [P01, hP0]
    · apply Polynomial.coeff_eq_zero_of_natDegree_lt
      have hmul : (D.P * D.Q).natDegree ≤ D.P.natDegree + D.Q.natDegree := Polynomial.natDegree_mul_le
      have hcmul : P01.natDegree ≤ (D.P * D.Q).natDegree := by
        dsimp [P01]; exact (Polynomial.natDegree_mul_le).trans (by rw [Polynomial.natDegree_C, zero_add])
      omega
  have hP01_c1 : P01.coeff (D.S.card + 1 - 1) = 0 := by
    rcases hPcase with hP0 | hPdeg
    · simp [P01, hP0]
    · apply Polynomial.coeff_eq_zero_of_natDegree_lt
      have hmul : (D.P * D.Q).natDegree ≤ D.P.natDegree + D.Q.natDegree := Polynomial.natDegree_mul_le
      have hcmul : P01.natDegree ≤ (D.P * D.Q).natDegree := by
        dsimp [P01]; exact (Polynomial.natDegree_mul_le).trans (by rw [Polynomial.natDegree_C, zero_add])
      omega
  have hP11_deg : ∀ k, D.S.card + 1 - 1 ≤ k → P11.coeff k = 0 := fun k hk => by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have hsq : P11.natDegree ≤ 2 * D.Q.natDegree := by dsimp [P11]; rw [Polynomial.natDegree_neg]; exact Polynomial.natDegree_pow_le
    omega
  have hP11_c2 : P11.coeff (D.S.card + 1 - 2) = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have hsq : P11.natDegree ≤ 2 * D.Q.natDegree := by dsimp [P11]; rw [Polynomial.natDegree_neg]; exact Polynomial.natDegree_pow_le
    omega
  have hm1 : 1 ≤ D.S.card + 1 := by omega
  have hm2 : 2 ≤ D.S.card + 1 := by have := Finset.card_pos.mpr D.S_nonempty; omega
  obtain ⟨C0, hC0, has0⟩ := poly_div_monic_coeff1 (D.S.card + 1) hQH_lb hQH_monic hQH_deg hm1 hP00_deg
  obtain ⟨C1, hC1, has1⟩ := poly_div_monic_coeff1 (D.S.card + 1) hQH_lb hQH_monic hQH_deg hm1 hP01_deg
  obtain ⟨C2, hC2, has2⟩ := poly_div_monic_coeff2 (D.S.card + 1) hQH_lb hQH_monic hQH_deg hm2 hP11_deg
  simp only [hP00_c1, neg_zero, Complex.ofReal_zero, zero_mul, sub_zero] at has0
  simp only [hP01_c1, neg_zero, Complex.ofReal_zero, zero_mul, sub_zero] at has1
  simp only [hP11_c2, Complex.ofReal_zero, zero_mul, sub_zero] at has2
  let R_star : ℝ := max 4 (2 * B + 2)
  have hR4 : 4 ≤ R_star := le_max_left _ _
  have hB_R : B ≤ R_star := by have hB0 : 0 ≤ B := (abs_nonneg D.tm).trans hB_tm; linarith [le_max_right (4 : ℝ) (2 * B + 2)]
  have hQH_rt : ∀ z : ℂ, Polynomial.aeval z Q_H = 0 → z.im = 0 ∧ ‖z‖ ≤ R_star := fun z hz => by
    rw [hQH_eq z, mul_eq_zero] at hz
    rcases hz with htm | hqs
    · have heq : z = (D.tm : ℂ) := sub_eq_zero.mp htm
      rw [heq, Complex.ofReal_im, Complex.norm_real, Real.norm_eq_abs]; exact ⟨rfl, hB_tm.trans hB_R⟩
    · exact ⟨(hQ_rt z hqs).1, (hQ_rt z hqs).2.trans hB_R⟩
  have hpos1 : (-1 : ℝ) ^ D.S.card = 1 := hEven.neg_one_pow
  refine ⟨(terminal_cardinal_integral D).1, R_star, max C0 (max C1 C2),
    P00, Q_H, P01, Q_H, P11, Q_H, hR4, by positivity, hQH_monic, hQH_monic, hQH_monic,
    hQH_rt, hQH_rt, hQH_rt, fun z hz => ?_, fun w hw => ?_⟩
  · have hQH_nz : Polynomial.aeval z Q_H ≠ 0 := fun h0 => not_le_of_gt hz (hQH_rt z h0).2
    have htm_nz : z - (D.tm : ℂ) ≠ 0 := fun h0 => hQH_nz (by rw [hQH_eq z, h0, zero_mul])
    have hdsl : dslope (fun u => -D.G u) (D.tm : ℂ) z = (-D.G z) / (z - (D.tm : ℂ)) := by
      rw [dslope_of_ne _ (sub_ne_zero.mp htm_nz), slope_def_field, D.G_eq_zero_on_S D.tm D.tm_mem, neg_zero, sub_zero]
    have hpr_eq : at47_pr D.S z = Polynomial.aeval z Q_S := (hQ_eq z).symm
    have hG := D.G_prod_eq z
    rw [hpr_eq, hpos1] at hG
    rw [hdsl]
    apply mul_right_cancel₀ hQH_nz
    have hLHS : ((-D.G z) / (z - (D.tm : ℂ))) * Polynomial.aeval z Q_H = (-D.G z) * Polynomial.aeval z Q_S := by
      rw [hQH_eq z]; field_simp [htm_nz]
    rw [hLHS]
    have hG_alg : (-D.G z) * Polynomial.aeval z Q_S = -(airyPQN D.P D.Q z ^ 2) := by
      have hG' : D.G z * Polynomial.aeval z Q_S = airyPQN D.P D.Q z ^ 2 := by simpa using hG
      linear_combination -hG'
    rw [hG_alg]
    have hsum :
        ((Polynomial.aeval z P00 / Polynomial.aeval z Q_H) * airyAiC z ^ 2 +
          (Polynomial.aeval z P01 / Polynomial.aeval z Q_H) * (airyAiC z * deriv airyAiC z) +
          (Polynomial.aeval z P11 / Polynomial.aeval z Q_H) * deriv airyAiC z ^ 2) *
          Polynomial.aeval z Q_H =
        Polynomial.aeval z P00 * airyAiC z ^ 2 +
          Polynomial.aeval z P01 * (airyAiC z * deriv airyAiC z) +
          Polynomial.aeval z P11 * deriv airyAiC z ^ 2 := by field_simp [hQH_nz]
    rw [hsum]
    dsimp [P00, P01, P11]
    simp only [airyPQN, map_neg, map_pow, map_mul, aeval_C, Complex.coe_algebraMap, aeval_eq_airyPQc_even]
    norm_num; ring
  · have hw0 : ‖w‖ ^ (-2 : ℝ) ≥ 0 := by positivity
    have hw03 : ‖w‖ ^ (-3 : ℝ) ≥ 0 := by positivity
    refine ⟨?_, ?_, ?_⟩
    · simpa only [Complex.ofReal_zero, zero_mul, sub_zero] using
        (has0 w hw).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hw0)
    · exact (has1 w hw).trans (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) hw0)
    · simpa only [Complex.ofReal_zero, zero_mul, sub_zero] using
        (has2 w hw).trans (mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) hw03)

lemma hb_osc_tail_of_even (D : ShellHBData) (hEven : Even D.S.card) :
    ∃ (c_osc C_r y₁ ϑ_c : ℝ), 0 < c_osc ∧ 0 ≤ C_r ∧ 25 ≤ y₁ ∧
      ∃ r : ℝ → ℝ, ∀ y ≥ y₁,
        |r y| ≤ C_r * y ^ (-(1 / 2 : ℝ)) ∧
        c_osc * y ^ (-(3 / 2 : ℝ)) * (Real.cos ((2 / 3 : ℝ) * y ^ (3 / 2 : ℝ) + ϑ_c) + r y) ^ 2 ≤
          (D.G ((-y : ℝ) : ℂ)).re := by
  obtain ⟨hQne, hmQ, hPcase⟩ := shellHBData_Q_degree_of_even D hEven
  let d : ℕ := D.Q.natDegree
  let q_d : ℝ := D.Q.leadingCoeff
  have hq_d : q_d ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQne
  let sgn : ℝ := -((-1 : ℝ) ^ d * q_d)
  have hsgn : sgn ≠ 0 := neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ (by norm_num)) hq_d)
  let B : ℝ := D.S.sup' D.S_nonempty (fun t => |t|)
  have hB : ∀ t ∈ D.S, |t| ≤ B := fun t ht => Finset.le_sup' (fun s => |s|) ht
  have hB0 : 0 ≤ B := (abs_nonneg D.tm).trans (hB D.tm D.tm_mem)
  let Q_plus : ℝ[X] := ∏ t ∈ D.S, (Polynomial.X + Polynomial.C t)
  have hQp_monic : Q_plus.Monic := Polynomial.monic_prod_of_monic D.S _ fun t _ => Polynomial.monic_X_add_C t
  have hQp_deg : Q_plus.natDegree = D.S.card := by
    dsimp [Q_plus]; rw [Polynomial.natDegree_prod_of_monic _ _ (fun t _ => Polynomial.monic_X_add_C t)]; simp
  have hQp_eval : ∀ y : ℝ, Q_plus.eval y = ∏ t ∈ D.S, (y + t) := fun y => by dsimp [Q_plus]; simp [Polynomial.eval_prod]
  let R_den : ℝ[X] := Q_plus - Polynomial.X ^ D.S.card
  have hR_den_deg : R_den.natDegree ≤ 2 * d + 1 := by
    by_cases h0 : R_den = 0
    · simp [h0]
    · have hlt : R_den.natDegree < D.S.card := by
        have hlc : R_den.coeff D.S.card = 0 := by
          have h1 : Q_plus.coeff D.S.card = 1 := by rw [← hQp_deg, Polynomial.coeff_natDegree]; exact hQp_monic.leadingCoeff
          have h2 : (Polynomial.X ^ D.S.card : ℝ[X]).coeff D.S.card = 1 := Polynomial.coeff_X_pow_self D.S.card
          simp only [R_den, Polynomial.coeff_sub]; linarith [h1, h2]
        have hle : R_den.natDegree ≤ D.S.card := (Polynomial.natDegree_sub_le _ _).trans (by rw [hQp_deg, Polynomial.natDegree_X_pow, max_self])
        rcases hle.eq_or_lt with heq | hlt
        · exfalso; exact h0 (Polynomial.leadingCoeff_eq_zero.mp (by rw [← Polynomial.coeff_natDegree, heq, hlc]))
        · exact hlt
      omega
  let C_den : ℝ := ∑ k ∈ Finset.range (2 * d + 2), |R_den.coeff k|
  have hR_den_bd : ∀ y : ℝ, 1 ≤ y → |Q_plus.eval y - y ^ (2 * d + 2)| ≤ C_den * y ^ (2 * d + 1) := fun y hy1 => by
    have hsub : Q_plus.eval y - y ^ (2 * d + 2) = R_den.eval y := by dsimp [R_den]; rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, hmQ]
    rw [hsub, Polynomial.eval_eq_sum_range]
    calc |∑ k ∈ Finset.range (R_den.natDegree + 1), R_den.coeff k * y ^ k|
        ≤ ∑ k ∈ Finset.range (R_den.natDegree + 1), |R_den.coeff k * y ^ k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range (R_den.natDegree + 1), |R_den.coeff k| * y ^ (2 * d + 1) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk_lt : k < R_den.natDegree + 1 := Finset.mem_range.mp hk
          rw [abs_mul, abs_of_nonneg (a := y ^ k) (pow_nonneg (by linarith) _)]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hy1 (by omega)) (abs_nonneg _)
      _ = (∑ k ∈ Finset.range (R_den.natDegree + 1), |R_den.coeff k|) * y ^ (2 * d + 1) := (Finset.sum_mul _ _ _).symm
      _ ≤ C_den * y ^ (2 * d + 1) := mul_le_mul_of_nonneg_right (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) fun _ _ _ => abs_nonneg _) (by positivity)
  let Q_rem : ℝ[X] := D.Q - Polynomial.C q_d * Polynomial.X ^ d
  have hQ_rem_deg : ∀ k, d ≤ k → Q_rem.coeff k = 0 := fun k hk => by
    simp only [Q_rem, Polynomial.coeff_sub, Polynomial.coeff_C_mul_X_pow]
    split_ifs with hkd
    · subst hkd; change D.Q.coeff D.Q.natDegree - D.Q.leadingCoeff = 0; rw [Polynomial.coeff_natDegree, sub_self]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_ne hk (Ne.symm hkd)), sub_zero]
  let C_Qrem : ℝ := ∑ k ∈ Finset.range d, |Q_rem.coeff k|
  let C_P : ℝ := ∑ k ∈ Finset.range (d + 1), |D.P.coeff k|
  let y₁ : ℝ := max 25 (2 * B + 2)
  have hy₁_25 : 25 ≤ y₁ := le_max_left _ _
  have hy₁_B : 2 * B + 2 ≤ y₁ := le_max_right _ _
  let C_den' : ℝ := 2 ^ (2 * d + 2) * C_den
  let C_Qrem' : ℝ := C_Qrem / |q_d|
  let C_α : ℝ := (1 + C_Qrem') * C_den' + C_Qrem'
  let C_S : ℝ := 2 * √π / 5
  let K_Q : ℝ := (√π + 1) * C_α + C_S
  let K_P : ℝ := √π * 2 ^ (d + 1) * 3 * C_P / |q_d|
  let C_r : ℝ := K_Q + K_P
  let r : ℝ → ℝ := fun y =>
    if y₁ ≤ y then (√π * y ^ (3 / 4 : ℝ) / sgn) * (at47_Nf D.P D.Q (-y) / √(∏ t ∈ D.S, (y + t))) - Real.cos (cohnTheta y) else 0
  refine ⟨q_d ^ 2 / π, C_r, y₁, -(π / 4), div_pos (sq_pos_of_ne_zero hq_d) Real.pi_pos, by positivity, hy₁_25, r, fun y hy => ?_⟩
  have hy25 : 25 ≤ y := hy₁_25.trans hy
  have hy1 : 1 ≤ y := by linarith
  have hy0 : 0 < y := by linarith
  have hyB : 2 * B + 2 ≤ y := hy₁_B.trans hy
  have hprod_lb : (y / 2) ^ (2 * d + 2) ≤ ∏ t ∈ D.S, (y + t) := by
    rw [show 2 * d + 2 = D.S.card from hmQ, ← Finset.prod_const (b := y / 2)]
    gcongr with t ht; have := (abs_le.mp (hB t ht)).1; linarith
  have hprod_pos : 0 < ∏ t ∈ D.S, (y + t) := lt_of_lt_of_le (by positivity) hprod_lb
  let den : ℝ := √(∏ t ∈ D.S, (y + t))
  have hden_pos : 0 < den := Real.sqrt_pos.mpr hprod_pos
  have hden_lb : (1 / 2 : ℝ) ^ (d + 1) * y ^ (d + 1 : ℕ) ≤ den := by
    have hsq_lb : (1 / 2 : ℝ) ^ (2 * d + 2) * (y ^ (d + 1)) ^ 2 ≤ ∏ t ∈ D.S, (y + t) := by
      calc (1 / 2 : ℝ) ^ (2 * d + 2) * (y ^ (d + 1)) ^ 2
          = (y / 2) ^ (2 * d + 2) := by ring
        _ ≤ _ := hprod_lb
    have hsq_rt : √((1 / 2 : ℝ) ^ (2 * d + 2) * (y ^ (d + 1)) ^ 2) = (1 / 2 : ℝ) ^ (d + 1) * y ^ (d + 1 : ℕ) := by
      rw [Real.sqrt_mul (by positivity), show (1 / 2 : ℝ) ^ (2 * d + 2) = ((1 / 2 : ℝ) ^ (d + 1)) ^ 2 by ring,
        Real.sqrt_sq (by positivity), Real.sqrt_sq (pow_nonneg hy0.le _)]
    rw [← hsq_rt]; exact Real.sqrt_le_sqrt hsq_lb
  have hcos_eq : Real.cos ((2 / 3 : ℝ) * y ^ (3 / 2 : ℝ) + -(π / 4)) = Real.cos (cohnTheta y) := by unfold cohnTheta; ring_nf
  have hr_def : r y = (√π * y ^ (3 / 4 : ℝ) / sgn) * (at47_Nf D.P D.Q (-y) / den) - Real.cos (cohnTheta y) := by
    simp only [r, hy, ↓reduceIte]; rfl
  have hyS : -y ∉ D.S := fun hmem => by have := (abs_le.mp (hB (-y) hmem)).1; linarith
  have hG_eq : (D.G ((-y : ℝ) : ℂ)).re = at47_Nf D.P D.Q (-y) ^ 2 / den ^ 2 := by
    have hF := at47_F_real_formula D.G_prod_eq hyS
    rw [hF, Complex.ofReal_re]
    have hprod_neg : ∏ t ∈ D.S, (-y - t) = (-1 : ℝ) ^ D.S.card * ∏ t ∈ D.S, (y + t) := by
      have he : ∀ t ∈ D.S, -y - t = (-1 : ℝ) * (y + t) := fun t _ => by ring
      rw [Finset.prod_congr rfl he, Finset.prod_mul_distrib, Finset.prod_const]
    rw [hprod_neg, Real.sq_sqrt hprod_pos.le, hEven.neg_one_pow, one_mul]
  refine ⟨?_, ?_⟩
  · let α : ℝ := (y ^ (d + 1 : ℕ) / ((-1 : ℝ) ^ d * q_d)) * (D.Q.eval (-y) / (den * y ^ d))
    let C_Ai' : ℝ := -(√π * y ^ (-(1 / 4 : ℝ)) * airyAi' (-y))
    let P_term : ℝ := (√π * y ^ (3 / 4 : ℝ) / sgn) * (D.P.eval (-y) * airyAi (-y) / den)
    have hy34' : y ^ (3 / 4 : ℝ) * y ^ (1 / 4 : ℝ) = y := by
      rw [← Real.rpow_add hy0]; norm_num
    have hα_simp : α = (y / ((-1 : ℝ) ^ d * q_d)) * (D.Q.eval (-y) / den) := by
      dsimp [α]; rw [show y ^ (d + 1 : ℕ) = y ^ d * y from by ring]; field_simp [pow_ne_zero d hy0.ne', hsgn, hden_pos.ne']
    have hr_split : r y = (α * C_Ai' - Real.cos (cohnTheta y)) + P_term := by
      have hy34m : y ^ (3 / 4 : ℝ) = y * y ^ (-(1 / 4 : ℝ)) := by
        calc y ^ (3 / 4 : ℝ) = y ^ (1 + -(1 / 4 : ℝ)) := by norm_num
          _ = y ^ (1 : ℝ) * y ^ (-(1 / 4 : ℝ)) := Real.rpow_add hy0 _ _
          _ = y * y ^ (-(1 / 4 : ℝ)) := by rw [Real.rpow_one]
      rw [hr_def]; unfold at47_Nf; dsimp [P_term]
      rw [hα_simp]
      dsimp [C_Ai', sgn]
      rw [hy34m]; ring
    have hy_m1_le_m12 : y⁻¹ ≤ y ^ (-(1 / 2 : ℝ)) := by rw [← Real.rpow_neg_one y]; exact Real.rpow_le_rpow_of_exponent_le hy1 (by norm_num)
    have hy_m32_le_m12 : y ^ (-(3 / 2 : ℝ)) ≤ y ^ (-(1 / 2 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hy1 (by norm_num)
    have hCAi'_bd : |C_Ai' - Real.cos (cohnTheta y)| ≤ C_S * y ^ (-(3 / 2 : ℝ)) := by
      have hAi' := airyAi'_neg_asymptotic_theta hy0
      have hid : C_Ai' - Real.cos (cohnTheta y) = -(√π * y ^ (-(1 / 4 : ℝ))) *
          (airyAi' (-y) + (y ^ (1 / 4 : ℝ) * Real.cos (cohnTheta y) / √π)) := by
        have hp0 : y ^ (-(1 / 4 : ℝ)) * y ^ (1 / 4 : ℝ) = 1 := by rw [← Real.rpow_add hy0]; norm_num
        dsimp [C_Ai']
        calc -(√π * y ^ (-(1 / 4 : ℝ)) * airyAi' (-y)) - Real.cos (cohnTheta y)
            = -(√π * y ^ (-(1 / 4 : ℝ))) * airyAi' (-y) - (√π * (√π)⁻¹) * (y ^ (-(1 / 4 : ℝ)) * y ^ (1 / 4 : ℝ)) * Real.cos (cohnTheta y) := by
              rw [mul_inv_cancel₀ (Real.sqrt_pos.mpr Real.pi_pos).ne', hp0]; ring
          _ = -(√π * y ^ (-(1 / 4 : ℝ))) * (airyAi' (-y) + (y ^ (1 / 4 : ℝ) * Real.cos (cohnTheta y) / √π)) := by
              rw [div_eq_mul_inv]; ring
      rw [hid, abs_mul, abs_neg, abs_of_pos (mul_pos (Real.sqrt_pos.mpr Real.pi_pos) (by positivity))]
      have hm := mul_le_mul_of_nonneg_left hAi' (by positivity : 0 ≤ √π * y ^ (-(1 / 4 : ℝ)))
      have hexp : y ^ (-(1 / 4 : ℝ)) * (y ^ (5 / 4 : ℝ))⁻¹ = y ^ (-(3 / 2 : ℝ)) := by
        rw [← Real.rpow_neg hy0.le, ← Real.rpow_add hy0]; norm_num
      calc √π * y ^ (-(1 / 4 : ℝ)) * |airyAi' (-y) + y ^ (1 / 4 : ℝ) * Real.cos (cohnTheta y) / √π|
          ≤ √π * y ^ (-(1 / 4 : ℝ)) * (2 / (5 * y ^ (5 / 4 : ℝ))) := hm
        _ = (2 * √π / 5) * (y ^ (-(1 / 4 : ℝ)) * (y ^ (5 / 4 : ℝ))⁻¹) := by ring
        _ = C_S * y ^ (-(3 / 2 : ℝ)) := by rw [hexp]
    have hCAi'_abs : |C_Ai'| ≤ √π + 1 := by
      have htri := abs_add_le (C_Ai' - Real.cos (cohnTheta y)) (Real.cos (cohnTheta y))
      rw [sub_add_cancel] at htri
      have hy32_le : y ^ (-(3 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hy1 (by norm_num)
      have h1 : |C_Ai' - Real.cos (cohnTheta y)| ≤ √π := calc
        |C_Ai' - Real.cos (cohnTheta y)| ≤ C_S * y ^ (-(3 / 2 : ℝ)) := hCAi'_bd
        _ ≤ C_S * 1 := mul_le_mul_of_nonneg_left hy32_le (by dsimp [C_S]; positivity)
        _ = 2 * √π / 5 := mul_one _
        _ ≤ √π := by linarith [Real.sqrt_pos.mpr Real.pi_pos]
      linarith [Real.abs_cos_le_one (cohnTheta y)]
    have hQrem_bd : |Q_rem.eval (-y)| * y ≤ C_Qrem * y ^ d := eval_neg_poly_bound Q_rem d hQ_rem_deg hy1
    let q_rat : ℝ := D.Q.eval (-y) / ((-1 : ℝ) ^ d * q_d * y ^ d)
    let u : ℝ := y ^ (d + 1 : ℕ) / den
    have hα_eq : α = q_rat * u := by
      dsimp [α, q_rat, u]
      have hden_ne : den ≠ 0 := hden_pos.ne'
      have hsgn0 : (-1 : ℝ) ^ d * q_d ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) hq_d
      field_simp [hsgn0, pow_ne_zero d hy0.ne', hden_ne]
    have hq_rat_bd : |q_rat - 1| ≤ C_Qrem' * y⁻¹ := by
      have hid : q_rat - 1 = Q_rem.eval (-y) / ((-1 : ℝ) ^ d * q_d * y ^ d) := by
        have hQ_eval : D.Q.eval (-y) = Q_rem.eval (-y) + (-1 : ℝ) ^ d * q_d * y ^ d := by
          dsimp [Q_rem]; rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, neg_pow]; ring
        have hsgn0 : (-1 : ℝ) ^ d * q_d ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) hq_d
        dsimp [q_rat]; rw [hQ_eval]; field_simp [hsgn0, pow_ne_zero d hy0.ne']; ring
      have hsgn_abs : |(-1 : ℝ) ^ d * q_d| = |q_d| := by rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      rw [hid, abs_div, abs_mul, hsgn_abs, abs_of_pos (pow_pos hy0 d)]
      calc |Q_rem.eval (-y)| / (|q_d| * y ^ d)
          = (|Q_rem.eval (-y)| * y) / (|q_d| * y ^ d * y) := by field_simp [hy0.ne']
        _ ≤ (C_Qrem * y ^ d) / (|q_d| * y ^ d * y) := div_le_div_of_nonneg_right hQrem_bd (by positivity)
        _ = C_Qrem' * y⁻¹ := by dsimp [C_Qrem']; field_simp [abs_pos.mpr hq_d, pow_ne_zero d hy0.ne', hy0.ne']
    have hu_bd : |u - 1| ≤ C_den' * y⁻¹ := by
      have hu_sq : u ^ 2 - 1 = (y ^ (2 * d + 2) - Q_plus.eval y) / Q_plus.eval y := by
        have hden_sq : den ^ 2 = Q_plus.eval y := by rw [hQp_eval y, Real.sq_sqrt hprod_pos.le]
        dsimp [u]; rw [div_pow, hden_sq, show (y ^ (d + 1)) ^ 2 = y ^ (2 * d + 2) by ring]; field_simp [hQp_eval y ▸ hprod_pos.ne']
      have hQp_lb : (1 / 2 : ℝ) ^ (2 * d + 2) * y ^ (2 * d + 2) ≤ Q_plus.eval y := by
        rw [hQp_eval y]; refine le_trans ?_ hprod_lb; rw [div_eq_mul_inv, mul_pow]; ring_nf; rfl
      have hQp_pos : 0 < Q_plus.eval y := by rw [hQp_eval y]; exact hprod_pos
      have hu2_bd : |u ^ 2 - 1| ≤ C_den' * y⁻¹ := by
        rw [hu_sq, abs_div, abs_of_pos hQp_pos, abs_sub_comm]
        calc |Q_plus.eval y - y ^ (2 * d + 2)| / Q_plus.eval y
            ≤ (C_den * y ^ (2 * d + 1)) / ((1 / 2 : ℝ) ^ (2 * d + 2) * y ^ (2 * d + 2)) :=
              div_le_div₀ (by positivity) (hR_den_bd y hy1) (by positivity) hQp_lb
          _ = C_den' * y⁻¹ := by
              dsimp [C_den']
              rw [div_eq_mul_inv, mul_inv, one_div, inv_pow, inv_inv, show y ^ (2 * d + 2) = y ^ (2 * d + 1) * y from pow_succ y (2 * d + 1), mul_inv]
              field_simp [pow_ne_zero (2 * d + 1) hy0.ne', hy0.ne']
      have hu1_ge : 1 ≤ u + 1 := by have : 0 < u := by dsimp [u]; positivity; linarith
      have hid_u : |u - 1| * (u + 1) = |u ^ 2 - 1| := by rw [← abs_of_pos (by linarith : 0 < u + 1), ← abs_mul]; congr 1; ring
      calc |u - 1| = |u ^ 2 - 1| / (u + 1) := eq_div_of_mul_eq (by linarith) hid_u
        _ ≤ |u ^ 2 - 1| / 1 := div_le_div_of_nonneg_left (abs_nonneg _) zero_lt_one hu1_ge
        _ = |u ^ 2 - 1| := div_one _
        _ ≤ C_den' * y⁻¹ := hu2_bd
    have hα_bd : |α - 1| ≤ C_α * y ^ (-(1 / 2 : ℝ)) := by
      have hq_abs : |q_rat| ≤ 1 + C_Qrem' := by
        have htri := abs_add_le (q_rat - 1) 1
        rw [sub_add_cancel, abs_one] at htri
        have h1 : C_Qrem' * y⁻¹ ≤ C_Qrem' := mul_le_of_le_one_right (by dsimp [C_Qrem']; positivity) (inv_le_one_of_one_le₀ hy1)
        linarith
      have hα_eq1 : α - 1 = q_rat * (u - 1) + (q_rat - 1) := by rw [hα_eq]; ring
      calc |α - 1| ≤ |q_rat * (u - 1)| + |q_rat - 1| := hα_eq1 ▸ abs_add_le _ _
        _ = |q_rat| * |u - 1| + |q_rat - 1| := by rw [abs_mul]
        _ ≤ (1 + C_Qrem') * (C_den' * y⁻¹) + C_Qrem' * y⁻¹ := by gcongr
        _ = C_α * y⁻¹ := by dsimp [C_α]; ring
        _ ≤ C_α * y ^ (-(1 / 2 : ℝ)) := mul_le_mul_of_nonneg_left hy_m1_le_m12 (by dsimp [C_α, C_Qrem', C_den']; positivity)
    have hP_term_bd : |P_term| ≤ K_P * y ^ (-(1 / 2 : ℝ)) := by
      have hP_coeff : ∀ k, d + 1 ≤ k → D.P.coeff k = 0 := fun k hk => by
        rcases hPcase with hP0 | hPdeg
        · simp [hP0]
        · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      have hP_poly := eval_neg_poly_bound D.P (d + 1) hP_coeff hy1
      have hAi_bd : |airyAi (-y)| ≤ 3 * y ^ (-(1 / 4 : ℝ)) := by
        have hb := (airyAi_and_deriv_neg_bounds (neg_nonpos.mpr hy0.le)).1
        rw [abs_neg, abs_of_pos hy0] at hb
        exact hb.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hy0 (by linarith only [hy0]) (by norm_num)) (by norm_num))
      have hsgn_abs : |sgn| = |q_d| := by dsimp [sgn]; rw [abs_neg, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      have hpow_simp : y ^ (3 / 4 : ℝ) * (y ^ (d + 1 : ℕ) * y⁻¹) * y ^ (-(1 / 4 : ℝ)) / y ^ (d + 1 : ℕ) =
          y ^ (-(1 / 2 : ℝ)) := by
        have hyd0 : y ^ (d + 1 : ℕ) ≠ 0 := pow_ne_zero _ hy0.ne'
        calc y ^ (3 / 4 : ℝ) * (y ^ (d + 1 : ℕ) * y⁻¹) * y ^ (-(1 / 4 : ℝ)) / y ^ (d + 1 : ℕ)
            = y ^ (3 / 4 : ℝ) * y ^ (-1 : ℝ) * y ^ (-(1 / 4 : ℝ)) := by
              rw [Real.rpow_neg_one]; field_simp [hyd0]
          _ = y ^ (3 / 4 + (-1 : ℝ) + -(1 / 4 : ℝ)) := by rw [← Real.rpow_add hy0, ← Real.rpow_add hy0]
          _ = y ^ (-(1 / 2 : ℝ)) := by norm_num
      dsimp [P_term]
      rw [abs_mul, abs_div, abs_mul, abs_of_pos (Real.sqrt_pos.mpr Real.pi_pos),
        abs_of_pos (Real.rpow_pos_of_pos hy0 _), hsgn_abs, abs_div, abs_mul, abs_of_pos hden_pos]
      calc (√π * y ^ (3 / 4 : ℝ) / |q_d|) * (|D.P.eval (-y)| * |airyAi (-y)| / den)
          ≤ (√π * y ^ (3 / 4 : ℝ) / |q_d|) *
              (((C_P * y ^ (d + 1 : ℕ) * y⁻¹) * (3 * y ^ (-(1 / 4 : ℝ)))) /
                ((1 / 2 : ℝ) ^ (d + 1) * y ^ (d + 1 : ℕ))) := by
            have hP1 : |D.P.eval (-y)| ≤ C_P * y ^ (d + 1 : ℕ) * y⁻¹ := by rw [le_mul_inv_iff₀ hy0]; exact hP_poly
            gcongr
        _ = (√π * 2 ^ (d + 1) * 3 * C_P / |q_d|) *
              (y ^ (3 / 4 : ℝ) * (y ^ (d + 1 : ℕ) * y⁻¹) * y ^ (-(1 / 4 : ℝ)) / y ^ (d + 1 : ℕ)) := by
            simp only [one_div (2 : ℝ), inv_pow, div_eq_mul_inv, mul_inv, inv_inv]; ring
        _ = K_P * y ^ (-(1 / 2 : ℝ)) := by rw [hpow_simp]
    have hQ_bd : |α * C_Ai' - Real.cos (cohnTheta y)| ≤ K_Q * y ^ (-(1 / 2 : ℝ)) := by
      have hid : α * C_Ai' - Real.cos (cohnTheta y) = (α - 1) * C_Ai' + (C_Ai' - Real.cos (cohnTheta y)) := by ring
      rw [hid]
      calc |(α - 1) * C_Ai' + (C_Ai' - Real.cos (cohnTheta y))|
          ≤ |α - 1| * |C_Ai'| + |C_Ai' - Real.cos (cohnTheta y)| := by rw [← abs_mul]; exact abs_add_le _ _
        _ ≤ (C_α * y ^ (-(1 / 2 : ℝ))) * (√π + 1) + C_S * y ^ (-(1 / 2 : ℝ)) :=
            add_le_add (mul_le_mul hα_bd hCAi'_abs (abs_nonneg _) (by positivity))
              (hCAi'_bd.trans (mul_le_mul_of_nonneg_left hy_m32_le_m12 (by positivity)))
        _ = K_Q * y ^ (-(1 / 2 : ℝ)) := by dsimp [K_Q]; ring
    rw [hr_split]
    calc |(α * C_Ai' - Real.cos (cohnTheta y)) + P_term|
        ≤ |α * C_Ai' - Real.cos (cohnTheta y)| + |P_term| := abs_add_le _ _
      _ ≤ K_Q * y ^ (-(1 / 2 : ℝ)) + K_P * y ^ (-(1 / 2 : ℝ)) := add_le_add hQ_bd hP_term_bd
      _ = C_r * y ^ (-(1 / 2 : ℝ)) := by dsimp [C_r]; ring
  · rw [hcos_eq, hr_def, add_sub_cancel, hG_eq]
    have hsgn2 : sgn ^ 2 = q_d ^ 2 := by dsimp [sgn]; rw [neg_sq, mul_pow, pow_right_comm, neg_one_sq, one_pow, one_mul]
    have hy32 : (y ^ (3 / 4 : ℝ)) ^ 2 = y ^ (3 / 2 : ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hy0.le]; norm_num
    have hy_inv : y ^ (-(3 / 2 : ℝ)) * y ^ (3 / 2 : ℝ) = 1 := by rw [← Real.rpow_add hy0]; norm_num
    have hmul_sq : (√π * y ^ (3 / 4 : ℝ) / sgn) ^ 2 = π * y ^ (3 / 2 : ℝ) / q_d ^ 2 := by
      rw [div_pow, mul_pow, Real.sq_sqrt Real.pi_pos.le, hy32, hsgn2]
    rw [mul_pow, hmul_sq, div_pow]
    calc (q_d ^ 2 / π) * y ^ (-(3 / 2 : ℝ)) * ((π * y ^ (3 / 2 : ℝ) / q_d ^ 2) * (at47_Nf D.P D.Q (-y) ^ 2 / den ^ 2))
        = (q_d ^ 2 / q_d ^ 2) * (π / π) * (y ^ (-(3 / 2 : ℝ)) * y ^ (3 / 2 : ℝ)) * (at47_Nf D.P D.Q (-y) ^ 2 / den ^ 2) := by ring
      _ ≤ at47_Nf D.P D.Q (-y) ^ 2 / den ^ 2 := by
          rw [div_self (pow_ne_zero 2 hq_d), div_self Real.pi_pos.ne', hy_inv, one_mul, one_mul, one_mul]

/-- Constructs `HBSeedSpec` (`AirySeedFloors.lean`) for any `D : ShellHBData` with `Even D.S.card`. -/
noncomputable def hbSeedSpec_of_shellHBData_even (D : ShellHBData) (hEven : Even D.S.card) : HBSeedSpec := by
  classical
  let m₀ : ℕ := D.S.card
  have hm₀ : 1 ≤ m₀ := Finset.card_pos.mpr D.S_nonempty
  let iso : Fin m₀ ≃o D.S := D.S.orderIsoOfFin rfl
  let nodes : Fin m₀ → ℝ := shellNodes D
  have hnodes_anti : StrictAnti nodes := shellNodes_strictAnti D
  have hlast_eq : nodes ⟨m₀ - 1, Nat.sub_lt hm₀ zero_lt_one⟩ = D.tm := shellNodes_last D
  let H_C : ℂ → ℂ := dslope (fun z => -D.G z) (D.tm : ℂ)
  obtain ⟨hH_inAiry, hdiv_int, hI_eq, hI_pos⟩ := terminal_cardinal_integral D
  let I_N : ℝ := ∫ u : ℝ, (-(D.G (u : ℂ)).re) / (u - D.tm)
  have hH_ae : (fun u : ℝ => (H_C (u : ℂ)).re) =ᵐ[MeasureTheory.volume] (fun u : ℝ => (-(D.G (u : ℂ)).re) / (u - D.tm)) := by
    have hne_ae : ∀ᵐ u : ℝ ∂MeasureTheory.volume, u ≠ D.tm := ae_iff.mpr (by simpa using measure_singleton D.tm)
    filter_upwards [hne_ae] with u hu
    have huc : (u : ℂ) ≠ (D.tm : ℂ) := fun h => hu (Complex.ofReal_injective h)
    have hd : H_C (u : ℂ) = (-D.G (u : ℂ)) / ((u : ℂ) - (D.tm : ℂ)) := by
      dsimp [H_C]; rw [dslope_of_ne _ huc, slope_def_field, D.G_eq_zero_on_S D.tm D.tm_mem, neg_zero, sub_zero]
    have hc : -D.G (u : ℂ) = ((-(D.G (u : ℂ)).re : ℝ) : ℂ) := Complex.ext rfl (by simp [D.G_real u])
    rw [hd, hc, show ((u : ℂ) - (D.tm : ℂ)) = ((u - D.tm : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_div, Complex.ofReal_re]
  let B : ℝ := D.S.sup' D.S_nonempty (fun t => |t|)
  let R_lip : ℝ := B + 1
  let hG_ex := lip_on_Icc_of_entire D.G_diff R_lip
  let hH_ex := lip_on_Icc_of_entire hH_inAiry.1 R_lip
  have hnode_mem : ∀ j : Fin m₀, nodes j ∈ D.S := fun j => (iso _).2
  have hnode_bd : ∀ j : Fin m₀, |nodes j| ≤ B := fun j => Finset.le_sup' (fun s => |s|) (hnode_mem j)
  let hosc := hb_osc_tail_of_even D hEven
  exact
    { m₀ := m₀
      m₀_pos := hm₀
      nodes := nodes
      nodes_anti := hnodes_anti
      last_le_a1 := hlast_eq ▸ D.tm_le_airyZero_one
      G_N := fun u => (D.G (u : ℂ)).re
      H_N := fun u => (H_C (u : ℂ)).re
      I_N := I_N
      I_N_pos := hI_pos
      continuous_G := Complex.continuous_re.comp (D.G_diff.continuous.comp Complex.continuous_ofReal)
      continuous_H := Complex.continuous_re.comp (hH_inAiry.1.continuous.comp Complex.continuous_ofReal)
      integrable_G := D.G_int.re
      integrable_H := hH_inAiry.2.1.re
      integral_G := by change ∫ u : ℝ, RCLike.re (D.G (u : ℂ)) = 0; rw [integral_re D.G_int, D.G_integral_zero]; rfl
      integral_H := integral_congr_ae hH_ae
      G_nonneg_tail := fun u hu => D.G_nonneg_left u (hlast_eq ▸ hu)
      H_eq_div_tail := fun u hu => by
        have hult : u < D.tm := hlast_eq ▸ hu
        have huc : (u : ℂ) ≠ (D.tm : ℂ) := fun h => hult.ne (Complex.ofReal_injective h)
        have hd : H_C (u : ℂ) = (-D.G (u : ℂ)) / ((u : ℂ) - (D.tm : ℂ)) := by
          dsimp [H_C]; rw [dslope_of_ne _ huc, slope_def_field, D.G_eq_zero_on_S D.tm D.tm_mem, neg_zero, sub_zero]
        have hc : -D.G (u : ℂ) = ((-(D.G (u : ℂ)).re : ℝ) : ℂ) := by apply Complex.ext <;> simp [D.G_real u]
        rw [hd, hc, show ((u : ℂ) - (D.tm : ℂ)) = ((u - D.tm : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_div, Complex.ofReal_re, hlast_eq]
        field_simp [show u - D.tm ≠ 0 by linarith, show -u + D.tm ≠ 0 by linarith]; ring
      node_vanish := fun j hj => by
        have hmem := hnode_mem j
        have hG0 : (D.G (nodes j : ℂ)).re = 0 := by rw [D.G_eq_zero_on_S _ hmem, Complex.zero_re]
        have hlt_idx : j < (⟨m₀ - 1, Nat.sub_lt hm₀ zero_lt_one⟩ : Fin m₀) := Fin.lt_def.mpr (by dsimp only; omega)
        have hgt : D.tm < nodes j := hlast_eq ▸ hnodes_anti hlt_idx
        have hne : (nodes j : ℂ) ≠ (D.tm : ℂ) := fun h => hgt.ne' (Complex.ofReal_injective h)
        have hd : H_C (nodes j : ℂ) = (-D.G (nodes j : ℂ)) / ((nodes j : ℂ) - (D.tm : ℂ)) := by
          dsimp [H_C]; rw [dslope_of_ne _ hne, slope_def_field, D.G_eq_zero_on_S D.tm D.tm_mem, neg_zero, sub_zero]
        exact ⟨hG0, by rw [hd, D.G_eq_zero_on_S _ hmem, neg_zero, zero_div, Complex.zero_re]⟩
      r_node := 1
      r_node_pos := one_pos
      A_G := hG_ex.choose
      A_H := hH_ex.choose
      A_G_nonneg := hG_ex.choose_spec.1
      A_H_nonneg := hH_ex.choose_spec.1
      G_lip_near := fun j _ u hu => by
        have hjn : |nodes j| ≤ R_lip := (hnode_bd j).trans (by linarith)
        have hu_r : |u| ≤ R_lip := by
          calc |u| = |(u - nodes j) + nodes j| := by ring_nf
            _ ≤ |u - nodes j| + |nodes j| := abs_add_le _ _
            _ ≤ 1 + B := add_le_add hu (hnode_bd j)
            _ = R_lip := by dsimp [R_lip]; ring
        calc |(D.G (u : ℂ)).re| = |(D.G (u : ℂ) - D.G (nodes j : ℂ)).re| := by rw [D.G_eq_zero_on_S _ (hnode_mem j), sub_zero]
          _ ≤ ‖D.G (u : ℂ) - D.G (nodes j : ℂ)‖ := Complex.abs_re_le_norm _
          _ ≤ hG_ex.choose * |u - nodes j| := hG_ex.choose_spec.2 u (nodes j) hu_r hjn
      H_lip_near := fun j hj u hu => by
        have hjn : |nodes j| ≤ R_lip := (hnode_bd j).trans (by linarith)
        have hu_r : |u| ≤ R_lip := by
          calc |u| = |(u - nodes j) + nodes j| := by ring_nf
            _ ≤ |u - nodes j| + |nodes j| := abs_add_le _ _
            _ ≤ 1 + B := add_le_add hu (hnode_bd j)
            _ = R_lip := by dsimp [R_lip]; ring
        have hlt_idx : j < (⟨m₀ - 1, Nat.sub_lt hm₀ zero_lt_one⟩ : Fin m₀) := Fin.lt_def.mpr (by dsimp only; omega)
        have hgt : D.tm < nodes j := hlast_eq ▸ hnodes_anti hlt_idx
        have hne : (nodes j : ℂ) ≠ (D.tm : ℂ) := fun h => hgt.ne' (Complex.ofReal_injective h)
        have hH0 : H_C (nodes j : ℂ) = 0 := by
          dsimp [H_C]; rw [dslope_of_ne _ hne, slope_def_field, D.G_eq_zero_on_S _ (hnode_mem j), D.G_eq_zero_on_S D.tm D.tm_mem, neg_zero, sub_self, zero_div]
        calc |(H_C (u : ℂ)).re| = |(H_C (u : ℂ) - H_C (nodes j : ℂ)).re| := by rw [hH0, sub_zero]
          _ ≤ ‖H_C (u : ℂ) - H_C (nodes j : ℂ)‖ := Complex.abs_re_le_norm _
          _ ≤ hH_ex.choose * |u - nodes j| := hH_ex.choose_spec.2 u (nodes j) hu_r hjn
      c_osc_G := hosc.choose
      C_r_G := hosc.choose_spec.choose
      y₁_G := hosc.choose_spec.choose_spec.choose
      ϑ_c_G := hosc.choose_spec.choose_spec.choose_spec.choose
      c_osc_G_pos := hosc.choose_spec.choose_spec.choose_spec.choose_spec.1
      C_r_G_nonneg := hosc.choose_spec.choose_spec.choose_spec.choose_spec.2.1
      y₁_G_ge := hosc.choose_spec.choose_spec.choose_spec.choose_spec.2.2.1
      G_osc_tail := hosc.choose_spec.choose_spec.choose_spec.choose_spec.2.2.2 }

/-- Unified `HBSeedSpec` and `HasGenRationalAiryCoeffs` package for every `D : ShellHBData`
(covering both odd and even `D.S.card`). -/
theorem hbSeedSpec_of_shellHBData_all (D : ShellHBData) :
    ∃ (S : HBSeedSpec) (β₀₀ β₁₁ : ℝ),
      0 < β₀₀ + β₁₁ ∧ S.lastNode = D.tm ∧ Set.range S.nodes = (D.S : Set ℝ) ∧
      (∀ t ∈ D.S, t ≠ D.tm → ∃ j : Fin S.m₀, j.val + 1 < S.m₀ ∧ S.nodes j = t) ∧
      S.G_N = (fun u : ℝ => (D.G (u : ℂ)).re) ∧
      S.H_N = (fun u : ℝ => (dslope (fun z => -D.G z) (D.tm : ℂ) (u : ℂ)).re) ∧
      HasGenRationalAiryCoeffs D.G β₀₀ β₁₁ ∧
      HasGenRationalAiryCoeffs (dslope (fun z => -D.G z) (D.tm : ℂ)) 0 0 := by
  rcases Nat.even_or_odd D.S.card with hEven | hOdd
  · obtain ⟨hQne, _, _⟩ := shellHBData_Q_degree_of_even D hEven
    let S := hbSeedSpec_of_shellHBData_even D hEven
    have hrange : Set.range S.nodes = (D.S : Set ℝ) := by
      change Set.range (shellNodes D) = (D.S : Set ℝ)
      ext x
      constructor
      · rintro ⟨j, rfl⟩; exact ((D.S.orderIsoOfFin rfl) _).2
      · intro hx
        let iso : Fin D.S.card ≃o D.S := D.S.orderIsoOfFin rfl
        let k := iso.symm ⟨x, hx⟩
        have hklt : k.val < D.S.card := k.isLt
        refine ⟨⟨D.S.card - 1 - k.val, by omega⟩, ?_⟩
        have hidx : (⟨D.S.card - 1 - (D.S.card - 1 - k.val), by omega⟩ : Fin D.S.card) = k :=
          Fin.ext (by simp; omega)
        dsimp [shellNodes]
        exact (congrArg Subtype.val (iso.congr_arg hidx)).trans
          (congrArg Subtype.val (iso.apply_symm_apply ⟨x, hx⟩))
    refine ⟨S, 0, D.Q.leadingCoeff ^ 2, by positivity [Polynomial.leadingCoeff_ne_zero.mpr hQne],
      shellNodes_last D, hrange, fun t htS htm => ?_, rfl, rfl,
      hasGenRationalAiryCoeffs_shellHBData_G_even D hEven,
      hasGenRationalAiryCoeffs_terminal_cardinal_even D hEven⟩
    obtain ⟨j, hj⟩ := hrange ▸ htS
    refine ⟨j, ?_, hj⟩
    by_contra hge
    push Not at hge
    have hjlt : j.val < S.m₀ := j.isLt
    have hjeq : j = ⟨D.S.card - 1, Nat.sub_lt (Finset.card_pos.mpr D.S_nonempty) zero_lt_one⟩ :=
      Fin.ext (by dsimp only [S, hbSeedSpec_of_shellHBData_even] at hjlt ⊢; omega)
    have hnd : S.nodes j = shellNodes D j := rfl
    rw [hnd, hjeq] at hj
    exact htm (hj.symm.trans (shellNodes_last D))
  · obtain ⟨hPne, _, _⟩ := shellHBData_P_degree_of_odd D hOdd
    exact ⟨hbSeedSpec_of_shellHBData D hOdd, D.P.leadingCoeff ^ 2, 0,
      by positivity [Polynomial.leadingCoeff_ne_zero.mpr hPne],
      hbSeedSpec_of_shellHBData_lastNode D hOdd,
      hbSeedSpec_of_shellHBData_nodes_range D hOdd,
      fun t htS htm => hbSeedSpec_of_shellHBData_exists_site D hOdd htS htm,
      rfl, rfl,
      hasGenRationalAiryCoeffs_shellHBData_G D hOdd,
      hasGenRationalAiryCoeffs_terminal_cardinal D hOdd⟩

end FormalResearch.SignUncertainty
