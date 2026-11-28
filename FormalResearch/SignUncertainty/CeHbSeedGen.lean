module

public import FormalResearch.SignUncertainty.AiryRationalSeeds
public import FormalResearch.SignUncertainty.CeTerminalDeflation

/-!
# Rational–Airy Representation and `HBSeedSpec` for General `ShellHBData`

Proves the `ShellHBData`-level prerequisites for `thm:ce-hb-lift` (`CeHbLift`):

* `airySbC`, `hasGenRationalAiryCoeffs_airySbC`: complex extension of `ceSb b` in
  `ℛ_{\mathrm{Ai}}^{\mathrm{gen}}` (`HasGenRationalAiryCoeffs (airySbC b) b 1`).
* `poly_prod_norm_ge`, `poly_div_monic_coeff1`, `poly_div_monic_coeff2`: asymptotic bounds for
  monic-denominator real rational functions `A(-w) / Q(-w)`.
* `hasGenRationalAiryCoeffs_shellHBData_G`, `hasGenRationalAiryCoeffs_shellHBData_negG`,
  `hasGenRationalAiryCoeffs_terminal_cardinal`: for odd `m = D.S.card` (forced by weak Laplace
  positivity via `even_m_laplace_sign`), `-D.G` has `(β₀₀, β₁₁) = (-p₀², 0)` (`β_∞ < 0 < β_+`)
  and `H_N = dslope (-D.G) D.tm` has `(0, 0)`.
* `hbSeedSpec_of_shellHBData`: constructs `HBSeedSpec` (`AirySeedFloors.lean`) for every
  `D : ShellHBData` with `Odd D.S.card`, enabling `hb_seed_mass_exists` at all levels `m`.
-/

@[expose] public section

open Complex Polynomial MeasureTheory Filter Topology Set Metric
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.Special FormalResearch.CohnElkies

/-! ### Part 1: Complex `ceF1` and `ceSb` in `ℛ_Ai^gen` -/

lemma airyCardinalR_zero_eq_dslope' : airyCardinalR 0 = dslope airyAi (airyZero 1) := by
  have hne_eq : ∀ x : ℝ, x ≠ airyZero 1 →
      airyCardinalR 0 x = dslope airyAi (airyZero 1) x := by
    intro x hx
    rw [airyCardinalR_of_ne 0 hx, dslope_of_ne _ hx, slope_def_field, airyAi_airyZero 1, sub_zero]
    rfl
  ext u
  by_cases hu : u = airyZero 1
  · subst hu
    have h0_seq : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hseq : Tendsto (fun n : ℕ => airyZero 1 + 1 / ((n : ℝ) + 1)) atTop (𝓝 (airyZero 1)) := by
      simpa only [add_zero] using (tendsto_const_nhds (x := airyZero 1)).add h0_seq
    have hne_n : ∀ n : ℕ, airyZero 1 + 1 / ((n : ℝ) + 1) ≠ airyZero 1 := fun n h => by
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    have hcont_d : Continuous (dslope airyAi (airyZero 1)) := by
      rw [← continuousOn_univ, continuousOn_dslope univ_mem]
      exact ⟨differentiable_airyAi.continuous.continuousOn, differentiable_airyAi _⟩
    exact tendsto_nhds_unique ((continuous_airyCardinalR 0).tendsto _ |>.comp hseq)
      ((hcont_d.tendsto _ |>.comp hseq).congr fun n => (hne_eq _ (hne_n n)).symm)
  · exact hne_eq u hu

lemma airySeedF0_re_eq_ceF1 (u : ℝ) : (airySeedF 0 (u : ℂ)).re = ceF1 u := by
  rw [airySeedF_re, airyCardinalR_zero_eq_dslope']; rfl

lemma airySeedG0_re_eq_ceG1 (u : ℝ) : (airySeedG 0 (u : ℂ)).re = ceG1 (airyZero 1) u := by
  rw [airySeedG_re, airyCardinalR_zero_eq_dslope']; rfl

/-- Complex extension of `ceSb b = g₁ + g₁' - b f₁`. -/
noncomputable def airySbC (b : ℝ) (z : ℂ) : ℂ :=
  airySeedG 0 z + airySeedG1Deriv z - (b : ℂ) * airySeedF 0 z

lemma airySbC_re (b u : ℝ) : (airySbC b (u : ℂ)).re = ceSb b u := by
  unfold airySbC ceSb
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  rw [airySeedG0_re_eq_ceG1, airySeedG1Deriv_re, airySeedF0_re_eq_ceF1]

theorem hasGenRationalAiryCoeffs_airySbC (b : ℝ) :
    HasGenRationalAiryCoeffs (airySbC b) b 1 := by
  have hG := hasGenRationalAiryCoeffs_airySeedG 0
  have hGd := hasGenRationalAiryCoeffs_airySeedG1Deriv
  have hF := (hasGenRationalAiryCoeffs_airySeedF 0).smul b
  have hsum := hG.add hGd
  have hsub := hsum.sub hF
  change HasGenRationalAiryCoeffs (airySbC b) (0 + 0 - b * -1) (0 + 1 - b * 0) at hsub
  simpa only [zero_add, mul_neg, mul_one, mul_zero, sub_neg_eq_add, sub_zero] using hsub

/-! ### Part 2: Monic-Denominator Rational Asymptotics -/

lemma poly_prod_norm_ge (S : Finset ℝ) {B : ℝ} (hB : ∀ t ∈ S, |t| ≤ B)
    {w : ℂ} (hw : 2 * B + 2 ≤ ‖w‖) :
    (1 / 2 : ℝ) ^ S.card * ‖w‖ ^ S.card ≤ ‖∏ t ∈ S, (-w - (t : ℂ))‖ := by
  have hw0 : 0 ≤ ‖w‖ := norm_nonneg w
  rw [norm_prod]
  calc (1 / 2 : ℝ) ^ S.card * ‖w‖ ^ S.card
      = (1 / 2 * ‖w‖) ^ S.card := (mul_pow _ _ _).symm
    _ = ∏ _t ∈ S, (1 / 2 * ‖w‖) := (Finset.prod_const _).symm
    _ ≤ ∏ t ∈ S, ‖-w - (t : ℂ)‖ := by
        gcongr with t ht
        have htB : ‖(t : ℂ)‖ ≤ B := by rw [Complex.norm_real, Real.norm_eq_abs]; exact hB t ht
        have htri := norm_sub_norm_le (-w) (t : ℂ)
        rw [norm_neg] at htri
        linarith

private lemma aeval_poly_bound (R : ℝ[X]) (m : ℕ) (hdeg : ∀ k, m ≤ k → R.coeff k = 0)
    {w : ℂ} (hw1 : 1 ≤ ‖w‖) (hm : 1 ≤ m) :
    ‖Polynomial.aeval (-w) R‖ ≤ (∑ k ∈ Finset.range m, |R.coeff k|) * ‖w‖ ^ (m - 1) := by
  by_cases hR : R = 0
  · subst hR
    simp only [map_zero, norm_zero, coeff_zero, abs_zero, Finset.sum_const_zero, zero_mul, le_refl]
  · have hlt : R.natDegree < m := by
      by_contra hge
      push Not at hge
      exact leadingCoeff_ne_zero.mpr hR (hdeg R.natDegree hge)
    have hsub : Finset.range (R.natDegree + 1) ⊆ Finset.range m := Finset.range_mono (by omega)
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range]
    calc ‖∑ k ∈ Finset.range (R.natDegree + 1), algebraMap ℝ ℂ (R.coeff k) * (-w) ^ k‖
        ≤ ∑ k ∈ Finset.range (R.natDegree + 1), ‖algebraMap ℝ ℂ (R.coeff k) * (-w) ^ k‖ :=
          norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range (R.natDegree + 1), |R.coeff k| * ‖w‖ ^ (m - 1) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk_lt : k < R.natDegree + 1 := Finset.mem_range.mp hk
          simp only [norm_mul, Complex.coe_algebraMap, Complex.norm_real, Real.norm_eq_abs,
            norm_pow, norm_neg]
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          exact pow_le_pow_right₀ hw1 (by omega)
      _ = (∑ k ∈ Finset.range (R.natDegree + 1), |R.coeff k|) * ‖w‖ ^ (m - 1) :=
          (Finset.sum_mul _ _ _).symm
      _ ≤ (∑ k ∈ Finset.range m, |R.coeff k|) * ‖w‖ ^ (m - 1) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => abs_nonneg _

lemma poly_div_monic_coeff1 {A Q : ℝ[X]} (m : ℕ) {B : ℝ}
    (hQ_lb : ∀ w : ℂ, 2 * B + 2 ≤ ‖w‖ → (1 / 2 : ℝ) ^ m * ‖w‖ ^ m ≤ ‖Polynomial.aeval (-w) Q‖)
    (hQ_monic : Q.Monic) (hQ_deg : Q.natDegree = m) (hm : 1 ≤ m)
    (hA : ∀ k, m ≤ k → A.coeff k = 0) :
    ∃ C ≥ 0, ∀ w : ℂ, max 4 (2 * B + 2) + 2 ≤ ‖w‖ →
      ‖Polynomial.aeval (-w) A / Polynomial.aeval (-w) Q -
        ((-(A.coeff (m - 1)) : ℝ) : ℂ) * w⁻¹‖ ≤ C * ‖w‖ ^ (-2 : ℝ) := by
  let c₁ := A.coeff (m - 1)
  let R := Polynomial.X * A - Polynomial.C c₁ * Q
  have hR : ∀ k, m ≤ k → R.coeff k = 0 := by
    intro k hk
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    simp only [R, Nat.succ_eq_add_one, Polynomial.coeff_sub, Polynomial.coeff_X_mul, Polynomial.coeff_C_mul]
    rcases hk.eq_or_lt with hkm | hk_gt
    · have hn : n = m - 1 := by omega
      rw [hn]
      have hQm : Q.coeff (m - 1 + 1) = 1 := by
        rw [Nat.sub_add_cancel hm, ← hQ_deg, Polynomial.coeff_natDegree]
        exact hQ_monic.leadingCoeff
      rw [hQm, mul_one, sub_self]
    · have hk1 : m ≤ n := by omega
      have hQ0 : Q.coeff (n + 1) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      rw [hA n hk1, hQ0, mul_zero, sub_zero]
  let C : ℝ := 2 ^ m * ∑ k ∈ Finset.range m, |R.coeff k|
  refine ⟨C, by positivity, fun w hw => ?_⟩
  have hw4 : 4 ≤ ‖w‖ := by linarith [le_max_left (4 : ℝ) (2 * B + 2)]
  have hwB : 2 * B + 2 ≤ ‖w‖ := by linarith [le_max_right (4 : ℝ) (2 * B + 2)]
  have hw0 : w ≠ 0 := norm_pos_iff.mp (by linarith)
  have hw1 : 1 ≤ ‖w‖ := by linarith
  have hQ_low : (1 / 2 : ℝ) ^ m * ‖w‖ ^ m ≤ ‖Polynomial.aeval (-w) Q‖ := hQ_lb w hwB
  have hQ_pos : 0 < ‖Polynomial.aeval (-w) Q‖ :=
    lt_of_lt_of_le (by positivity) hQ_low
  have hQ0 : Polynomial.aeval (-w) Q ≠ 0 := norm_pos_iff.mp hQ_pos
  have hid : Polynomial.aeval (-w) A / Polynomial.aeval (-w) Q - ((-c₁ : ℝ) : ℂ) * w⁻¹ =
      -Polynomial.aeval (-w) R / (w * Polynomial.aeval (-w) Q) := by
    have hReq : Polynomial.aeval (-w) R = -w * Polynomial.aeval (-w) A - (c₁ : ℂ) * Polynomial.aeval (-w) Q := by
      dsimp [R]; simp only [map_sub, map_mul, aeval_X, aeval_C, Complex.coe_algebraMap]
    field_simp [hw0, hQ0]
    rw [Complex.ofReal_neg, hReq]
    ring
  rw [hid, norm_div, norm_neg, norm_mul]
  have hR_ub := aeval_poly_bound R m hR hw1 hm
  have hden : (1 / 2 : ℝ) ^ m * ‖w‖ ^ (m + 1) ≤ ‖w‖ * ‖Polynomial.aeval (-w) Q‖ := by
    calc (1 / 2 : ℝ) ^ m * ‖w‖ ^ (m + 1)
        = ‖w‖ * ((1 / 2 : ℝ) ^ m * ‖w‖ ^ m) := by rw [pow_succ]; ring
      _ ≤ ‖w‖ * ‖Polynomial.aeval (-w) Q‖ := mul_le_mul_of_nonneg_left hQ_low (norm_nonneg _)
  have hw_pos : 0 < ‖w‖ := by linarith
  have hinv_eq : ‖w‖ ^ (m - 1) / ((1 / 2 : ℝ) ^ m * ‖w‖ ^ (m + 1)) =
      (2 : ℝ) ^ m * ‖w‖ ^ (-2 : ℝ) := by
    rw [← Real.rpow_natCast ‖w‖ (m - 1), ← Real.rpow_natCast ‖w‖ (m + 1)]
    have hpow : ‖w‖ ^ ((m - 1 : ℕ) : ℝ) / ‖w‖ ^ ((m + 1 : ℕ) : ℝ) = ‖w‖ ^ (-2 : ℝ) := by
      rw [← Real.rpow_sub hw_pos]
      congr 1
      rw [Nat.cast_sub hm]; push_cast; ring
    calc ‖w‖ ^ ((m - 1 : ℕ) : ℝ) / ((1 / 2 : ℝ) ^ m * ‖w‖ ^ ((m + 1 : ℕ) : ℝ))
        = (2 : ℝ) ^ m * (‖w‖ ^ ((m - 1 : ℕ) : ℝ) / ‖w‖ ^ ((m + 1 : ℕ) : ℝ)) := by
          rw [one_div, inv_pow, div_mul_eq_div_mul_one_div, div_inv_eq_mul, mul_comm]; ring
      _ = (2 : ℝ) ^ m * ‖w‖ ^ (-2 : ℝ) := by rw [hpow]
  calc ‖Polynomial.aeval (-w) R‖ / (‖w‖ * ‖Polynomial.aeval (-w) Q‖)
      ≤ ((∑ k ∈ Finset.range m, |R.coeff k|) * ‖w‖ ^ (m - 1)) /
          ((1 / 2 : ℝ) ^ m * ‖w‖ ^ (m + 1)) :=
        div_le_div₀ (by positivity) hR_ub (by positivity) hden
    _ = (∑ k ∈ Finset.range m, |R.coeff k|) *
          (‖w‖ ^ (m - 1) / ((1 / 2 : ℝ) ^ m * ‖w‖ ^ (m + 1))) := by ring
    _ = C * ‖w‖ ^ (-2 : ℝ) := by rw [hinv_eq]; dsimp [C]; ring

lemma poly_div_monic_coeff2 {A Q : ℝ[X]} (m : ℕ) {B : ℝ}
    (hQ_lb : ∀ w : ℂ, 2 * B + 2 ≤ ‖w‖ → (1 / 2 : ℝ) ^ m * ‖w‖ ^ m ≤ ‖Polynomial.aeval (-w) Q‖)
    (hQ_monic : Q.Monic) (hQ_deg : Q.natDegree = m) (hm2 : 2 ≤ m)
    (hA : ∀ k, m - 1 ≤ k → A.coeff k = 0) :
    ∃ C ≥ 0, ∀ w : ℂ, max 4 (2 * B + 2) + 2 ≤ ‖w‖ →
      ‖Polynomial.aeval (-w) A / Polynomial.aeval (-w) Q -
        ((A.coeff (m - 2) : ℝ) : ℂ) * (w ^ 2)⁻¹‖ ≤ C * ‖w‖ ^ (-3 : ℝ) := by
  let c₂ := A.coeff (m - 2)
  let R := Polynomial.X ^ 2 * A - Polynomial.C c₂ * Q
  have hR : ∀ k, m ≤ k → R.coeff k = 0 := by
    intro k hk
    simp only [R, Polynomial.coeff_sub, Polynomial.coeff_X_pow_mul', Polynomial.coeff_C_mul]
    split_ifs with hk2
    · rcases hk.eq_or_lt with rfl | hk_gt
      · have hQm : Q.coeff m = 1 := hQ_deg ▸ hQ_monic.leadingCoeff
        rw [hQm, mul_one, sub_self]
      · have hk1 : m - 1 ≤ k - 2 := by omega
        have hQ0 : Q.coeff k = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (hQ_deg ▸ hk_gt)
        rw [hA (k - 2) hk1, hQ0, mul_zero, sub_zero]
    · exfalso; omega
  let C : ℝ := 2 ^ m * ∑ k ∈ Finset.range m, |R.coeff k|
  refine ⟨C, by positivity, fun w hw => ?_⟩
  have hwB : 2 * B + 2 ≤ ‖w‖ := by linarith [le_max_right (4 : ℝ) (2 * B + 2)]
  have hw0 : w ≠ 0 := norm_pos_iff.mp (by linarith [le_max_left (4 : ℝ) (2 * B + 2)])
  have hw1 : 1 ≤ ‖w‖ := by linarith [le_max_left (4 : ℝ) (2 * B + 2)]
  have hQ_low : (1 / 2 : ℝ) ^ m * ‖w‖ ^ m ≤ ‖Polynomial.aeval (-w) Q‖ := hQ_lb w hwB
  have hQ0 : Polynomial.aeval (-w) Q ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hQ_low)
  have hid : Polynomial.aeval (-w) A / Polynomial.aeval (-w) Q - ((c₂ : ℝ) : ℂ) * (w ^ 2)⁻¹ =
      Polynomial.aeval (-w) R / (w ^ 2 * Polynomial.aeval (-w) Q) := by
    have hReq : Polynomial.aeval (-w) R = w ^ 2 * Polynomial.aeval (-w) A - (c₂ : ℂ) * Polynomial.aeval (-w) Q := by
      dsimp [R]; simp only [map_sub, map_mul, map_pow, aeval_X, aeval_C, Complex.coe_algebraMap, neg_sq]
    field_simp [pow_ne_zero 2 hw0, hQ0]
    rw [hReq]; ring
  rw [hid, norm_div, norm_mul, norm_pow]
  have hR_ub := aeval_poly_bound R m hR hw1 (by omega)
  have hden : (1 / 2 : ℝ) ^ m * ‖w‖ ^ (m + 2) ≤ ‖w‖ ^ 2 * ‖Polynomial.aeval (-w) Q‖ := by
    calc (1 / 2 : ℝ) ^ m * ‖w‖ ^ (m + 2)
        = ‖w‖ ^ 2 * ((1 / 2 : ℝ) ^ m * ‖w‖ ^ m) := by rw [pow_add]; ring
      _ ≤ ‖w‖ ^ 2 * ‖Polynomial.aeval (-w) Q‖ := mul_le_mul_of_nonneg_left hQ_low (sq_nonneg _)
  have hw_pos : 0 < ‖w‖ := by linarith
  have hinv_eq : ‖w‖ ^ (m - 1) / ((1 / 2 : ℝ) ^ m * ‖w‖ ^ (m + 2)) =
      (2 : ℝ) ^ m * ‖w‖ ^ (-3 : ℝ) := by
    rw [← Real.rpow_natCast ‖w‖ (m - 1), ← Real.rpow_natCast ‖w‖ (m + 2)]
    have hpow : ‖w‖ ^ ((m - 1 : ℕ) : ℝ) / ‖w‖ ^ ((m + 2 : ℕ) : ℝ) = ‖w‖ ^ (-3 : ℝ) := by
      rw [← Real.rpow_sub hw_pos]
      congr 1
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    calc ‖w‖ ^ ((m - 1 : ℕ) : ℝ) / ((1 / 2 : ℝ) ^ m * ‖w‖ ^ ((m + 2 : ℕ) : ℝ))
        = (2 : ℝ) ^ m * (‖w‖ ^ ((m - 1 : ℕ) : ℝ) / ‖w‖ ^ ((m + 2 : ℕ) : ℝ)) := by
          rw [one_div, inv_pow, div_mul_eq_div_mul_one_div, div_inv_eq_mul, mul_comm]; ring
      _ = (2 : ℝ) ^ m * ‖w‖ ^ (-3 : ℝ) := by rw [hpow]
  calc ‖Polynomial.aeval (-w) R‖ / (‖w‖ ^ 2 * ‖Polynomial.aeval (-w) Q‖)
      ≤ ((∑ k ∈ Finset.range m, |R.coeff k|) * ‖w‖ ^ (m - 1)) /
          ((1 / 2 : ℝ) ^ m * ‖w‖ ^ (m + 2)) :=
        div_le_div₀ (by positivity) hR_ub (by positivity) hden
    _ = (∑ k ∈ Finset.range m, |R.coeff k|) *
          (‖w‖ ^ (m - 1) / ((1 / 2 : ℝ) ^ m * ‖w‖ ^ (m + 2))) := by ring
    _ = C * ‖w‖ ^ (-3 : ℝ) := by rw [hinv_eq]; dsimp [C]; ring

/-! ### Part 3: `D.G` and `H_N = dslope (-D.G) D.tm` in `ℛ_Ai^gen` -/

lemma shellHBData_P_degree_of_odd (D : ShellHBData) (hOdd : Odd D.S.card) :
    D.P ≠ 0 ∧ 2 * D.P.natDegree + 1 = D.S.card ∧
      (D.Q = 0 ∨ 2 * D.Q.natDegree + 3 ≤ D.S.card) := by
  rcases D.m_eq with ⟨hQ0, hcard1⟩ | ⟨hQne, hcardm⟩
  · obtain ⟨p₀, hp₀, hP⟩ := airyPQHB_eq_C_of_Q_eq_zero (hQ0 ▸ D.hHB)
    refine ⟨?_, ?_, Or.inl hQ0⟩
    · rw [hP]; exact Polynomial.C_ne_zero.mpr hp₀
    · rw [hP, Polynomial.natDegree_C, hcard1]
  · unfold at47_m at hcardm
    have hnot_even : D.S.card ≠ 2 * D.Q.natDegree + 2 := by
      intro h
      rw [h] at hOdd
      exact (Nat.not_odd_iff_even.mpr ⟨D.Q.natDegree + 1, by ring⟩) hOdd
    have hmP : D.S.card = 2 * D.P.natDegree + 1 := by omega
    have hPne : D.P ≠ 0 := by
      intro hP0
      rw [hP0, Polynomial.natDegree_zero] at hmP
      omega
    refine ⟨hPne, hmP.symm, Or.inr (by omega)⟩

private lemma shellPoly_props (S : Finset ℝ) (hSne : S.Nonempty) :
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

private lemma aeval_eq_airyPQc (p : ℝ[X]) (z : ℂ) : Polynomial.aeval z p = airyPQc p z := by
  unfold airyPQc
  rw [Polynomial.eval_map, Polynomial.aeval_def]

theorem hasGenRationalAiryCoeffs_shellHBData_G (D : ShellHBData) (hOdd : Odd D.S.card) :
    HasGenRationalAiryCoeffs D.G (D.P.leadingCoeff ^ 2) 0 := by
  obtain ⟨hPne, hmP, hQcase⟩ := shellHBData_P_degree_of_odd D hOdd
  let B : ℝ := D.S.sup' D.S_nonempty (fun t => |t|)
  let Q_S : ℝ[X] := ∏ t ∈ D.S, (Polynomial.X - Polynomial.C t)
  obtain ⟨hQ_monic, hQ_deg, hQ_eq, hQ_rt⟩ := shellPoly_props D.S D.S_nonempty
  have hB : ∀ t ∈ D.S, |t| ≤ B := fun t ht => Finset.le_sup' (fun s => |s|) ht
  have hB0 : 0 ≤ B := (abs_nonneg D.tm).trans (hB D.tm D.tm_mem)
  have hm1 : 1 ≤ D.S.card := Finset.card_pos.mpr D.S_nonempty
  have hneg1 : (-1 : ℝ) ^ D.S.card = -1 := hOdd.neg_one_pow
  let P00 : ℝ[X] := -D.P ^ 2
  let P01 : ℝ[X] := Polynomial.C (-2 : ℝ) * (D.P * D.Q)
  let P11 : ℝ[X] := -D.Q ^ 2
  have hP00_deg : ∀ k, D.S.card ≤ k → P00.coeff k = 0 := fun k hk => by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have hsq : (D.P ^ 2).natDegree ≤ 2 * D.P.natDegree := Polynomial.natDegree_pow_le
    dsimp [P00]; rw [Polynomial.natDegree_neg]; omega
  have hP00_c1 : P00.coeff (D.S.card - 1) = -(D.P.leadingCoeff ^ 2) := by
    have hsq : (D.P ^ 2).coeff (2 * D.P.natDegree) = D.P.leadingCoeff ^ 2 := by
      have hdeg2 : (D.P ^ 2).natDegree = 2 * D.P.natDegree := Polynomial.natDegree_pow D.P 2
      have hlead : (D.P ^ 2).leadingCoeff = D.P.leadingCoeff ^ 2 := Polynomial.leadingCoeff_pow D.P 2
      rw [← hdeg2, Polynomial.coeff_natDegree, hlead]
    simp only [P00, Polynomial.coeff_neg, show D.S.card - 1 = 2 * D.P.natDegree by omega, hsq]
  have hP01_deg : ∀ k, D.S.card ≤ k → P01.coeff k = 0 := fun k hk => by
    rcases hQcase with hQ0 | hQdeg
    · simp [P01, hQ0]
    · apply Polynomial.coeff_eq_zero_of_natDegree_lt
      have hmul : (D.P * D.Q).natDegree ≤ D.P.natDegree + D.Q.natDegree :=
        Polynomial.natDegree_mul_le
      have hcmul : P01.natDegree ≤ (D.P * D.Q).natDegree := by
        dsimp [P01]
        exact (Polynomial.natDegree_mul_le).trans (by rw [Polynomial.natDegree_C, zero_add])
      omega
  have hP01_c1 : P01.coeff (D.S.card - 1) = 0 := by
    rcases hQcase with hQ0 | hQdeg
    · simp [P01, hQ0]
    · apply Polynomial.coeff_eq_zero_of_natDegree_lt
      have hmul : (D.P * D.Q).natDegree ≤ D.P.natDegree + D.Q.natDegree :=
        Polynomial.natDegree_mul_le
      have hcmul : P01.natDegree ≤ (D.P * D.Q).natDegree := by
        dsimp [P01]
        exact (Polynomial.natDegree_mul_le).trans (by rw [Polynomial.natDegree_C, zero_add])
      omega
  have hQ_lb : ∀ w : ℂ, 2 * B + 2 ≤ ‖w‖ → (1 / 2 : ℝ) ^ D.S.card * ‖w‖ ^ D.S.card ≤ ‖Polynomial.aeval (-w) Q_S‖ :=
    fun w hw => by rw [hQ_eq (-w)]; exact poly_prod_norm_ge D.S hB hw
  obtain ⟨C0, hC0, has0⟩ := poly_div_monic_coeff1 D.S.card hQ_lb hQ_monic hQ_deg hm1 hP00_deg
  obtain ⟨C1, hC1, has1⟩ := poly_div_monic_coeff1 D.S.card hQ_lb hQ_monic hQ_deg hm1 hP01_deg
  rw [hP00_c1, neg_neg] at has0
  simp only [hP01_c1, neg_zero, Complex.ofReal_zero, zero_mul, sub_zero] at has1
  let R_star : ℝ := max 4 (2 * B + 2)
  have hR4 : 4 ≤ R_star := le_max_left _ _
  have hB_R : B ≤ R_star := by linarith [le_max_right (4 : ℝ) (2 * B + 2)]
  -- `P11`: either `D.Q = 0` or `2 * D.Q.natDegree + 3 ≤ D.S.card` (hence `3 ≤ D.S.card`).
  have hex_P11 : ∃ C2 ≥ 0, ∀ w : ℂ, R_star + 2 ≤ ‖w‖ →
      ‖Polynomial.aeval (-w) P11 / Polynomial.aeval (-w) Q_S - ((0 : ℝ) : ℂ) * (w ^ 2)⁻¹‖ ≤
        C2 * ‖w‖ ^ (-3 : ℝ) := by
    rcases hQcase with hQ0 | hQdeg
    · refine ⟨0, le_rfl, fun w _ => ?_⟩
      dsimp [P11]; rw [hQ0]; simp
    · have hm3 : 2 ≤ D.S.card := by omega
      have hP11_deg : ∀ k, D.S.card - 1 ≤ k → P11.coeff k = 0 := fun k hk => by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        have hsq : (D.Q ^ 2).natDegree ≤ 2 * D.Q.natDegree := Polynomial.natDegree_pow_le
        dsimp [P11]; rw [Polynomial.natDegree_neg]; omega
      obtain ⟨C2, hC2, has2⟩ := poly_div_monic_coeff2 D.S.card hQ_lb hQ_monic hQ_deg hm3 hP11_deg
      have hP11_c2 : P11.coeff (D.S.card - 2) = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        have hsq : (D.Q ^ 2).natDegree ≤ 2 * D.Q.natDegree := Polynomial.natDegree_pow_le
        dsimp [P11]; rw [Polynomial.natDegree_neg]; omega
      rw [hP11_c2] at has2
      exact ⟨C2, hC2, has2⟩
  obtain ⟨C2, hC2, has2⟩ := hex_P11
  refine ⟨D.G_inAiryClass, R_star, max C0 (max C1 C2), P00, Q_S, P01, Q_S, P11, Q_S,
    hR4, by positivity, hQ_monic, hQ_monic, hQ_monic,
    fun z hz => ⟨(hQ_rt z hz).1, (hQ_rt z hz).2.trans hB_R⟩,
    fun z hz => ⟨(hQ_rt z hz).1, (hQ_rt z hz).2.trans hB_R⟩,
    fun z hz => ⟨(hQ_rt z hz).1, (hQ_rt z hz).2.trans hB_R⟩,
    fun z hz => ?_, fun w hw => ?_⟩
  · have hQnz : Polynomial.aeval z Q_S ≠ 0 := fun h0 => not_le_of_gt hz ((hQ_rt z h0).2.trans hB_R)
    have hpr_eq : at47_pr D.S z = Polynomial.aeval z Q_S := (hQ_eq z).symm
    have hG := D.G_prod_eq z
    rw [hpr_eq, hneg1] at hG
    apply mul_right_cancel₀ hQnz
    have hG_alg : D.G z * Polynomial.aeval z Q_S = (-1 : ℂ) * airyPQN D.P D.Q z ^ 2 := by
      simpa using hG
    rw [hG_alg]
    have hsum :
        ((Polynomial.aeval z P00 / Polynomial.aeval z Q_S) * airyAiC z ^ 2 +
          (Polynomial.aeval z P01 / Polynomial.aeval z Q_S) * (airyAiC z * deriv airyAiC z) +
          (Polynomial.aeval z P11 / Polynomial.aeval z Q_S) * deriv airyAiC z ^ 2) *
          Polynomial.aeval z Q_S =
        Polynomial.aeval z P00 * airyAiC z ^ 2 +
          Polynomial.aeval z P01 * (airyAiC z * deriv airyAiC z) +
          Polynomial.aeval z P11 * deriv airyAiC z ^ 2 := by
      field_simp [hQnz]
    rw [hsum]
    dsimp [P00, P01, P11]
    simp only [airyPQN, map_neg, map_pow, map_mul, aeval_C, Complex.coe_algebraMap, aeval_eq_airyPQc]
    norm_num
    ring
  · have hw0 : ‖w‖ ^ (-2 : ℝ) ≥ 0 := by positivity
    have hw03 : ‖w‖ ^ (-3 : ℝ) ≥ 0 := by positivity
    refine ⟨(has0 w hw).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hw0),
      (has1 w hw).trans (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) hw0),
      ?_⟩
    simpa only [Complex.ofReal_zero, zero_mul, sub_zero] using
      (has2 w hw).trans (mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) hw03)

theorem hasGenRationalAiryCoeffs_shellHBData_negG (D : ShellHBData) (hOdd : Odd D.S.card) :
    HasGenRationalAiryCoeffs (fun z => -D.G z) (-(D.P.leadingCoeff ^ 2)) 0 := by
  simpa using (hasGenRationalAiryCoeffs_shellHBData_G D hOdd).neg

theorem hasGenRationalAiryCoeffs_terminal_cardinal (D : ShellHBData) (hOdd : Odd D.S.card) :
    HasGenRationalAiryCoeffs (dslope (fun z => -D.G z) (D.tm : ℂ)) 0 0 := by
  obtain ⟨_, hmP, hQcase⟩ := shellHBData_P_degree_of_odd D hOdd
  let B : ℝ := D.S.sup' D.S_nonempty (fun t => |t|)
  let Q_S : ℝ[X] := ∏ t ∈ D.S, (Polynomial.X - Polynomial.C t)
  obtain ⟨hQ_monic, hQ_deg, hQ_eq, hQ_rt⟩ := shellPoly_props D.S D.S_nonempty
  have hB : ∀ t ∈ D.S, |t| ≤ B := fun t ht => Finset.le_sup' (fun s => |s|) ht
  have hB0 : 0 ≤ B := (abs_nonneg D.tm).trans (hB D.tm D.tm_mem)
  have hB_tm : |D.tm| ≤ B := hB D.tm D.tm_mem
  let Q_H : ℝ[X] := (Polynomial.X - Polynomial.C D.tm) * Q_S
  have hQH_monic : Q_H.Monic := (Polynomial.monic_X_sub_C D.tm).mul hQ_monic
  have hQH_deg : Q_H.natDegree = D.S.card + 1 := by
    dsimp [Q_H]
    rw [Polynomial.natDegree_mul (Polynomial.monic_X_sub_C D.tm).ne_zero hQ_monic.ne_zero,
      Polynomial.natDegree_X_sub_C, hQ_deg, add_comm]
  have hQH_eq : ∀ z : ℂ, Polynomial.aeval z Q_H = (z - (D.tm : ℂ)) * Polynomial.aeval z Q_S := by
    intro z; dsimp [Q_H]
    simp only [map_mul, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Complex.coe_algebraMap]
  have hQH_lb : ∀ w : ℂ, 2 * B + 2 ≤ ‖w‖ →
      (1 / 2 : ℝ) ^ (D.S.card + 1) * ‖w‖ ^ (D.S.card + 1) ≤ ‖Polynomial.aeval (-w) Q_H‖ := by
    intro w hw
    rw [hQH_eq (-w), norm_mul, hQ_eq (-w)]
    have htm_lb : 1 / 2 * ‖w‖ ≤ ‖-w - (D.tm : ℂ)‖ := by
      have htri := norm_sub_norm_le (-w) (D.tm : ℂ)
      have htB : ‖(D.tm : ℂ)‖ ≤ B := by rw [Complex.norm_real, Real.norm_eq_abs]; exact hB_tm
      rw [norm_neg] at htri; linarith
    have hQS_lb := poly_prod_norm_ge D.S hB hw
    calc (1 / 2 : ℝ) ^ (D.S.card + 1) * ‖w‖ ^ (D.S.card + 1)
        = (1 / 2 * ‖w‖) * ((1 / 2 : ℝ) ^ D.S.card * ‖w‖ ^ D.S.card) := by
          rw [pow_succ, pow_succ]; ring
      _ ≤ ‖-w - (D.tm : ℂ)‖ * ‖∏ t ∈ D.S, (-w - (t : ℂ))‖ :=
          mul_le_mul htm_lb hQS_lb (by positivity) (norm_nonneg _)
  let P00 : ℝ[X] := D.P ^ 2
  let P01 : ℝ[X] := Polynomial.C (2 : ℝ) * (D.P * D.Q)
  let P11 : ℝ[X] := D.Q ^ 2
  have hP00_deg : ∀ k, D.S.card + 1 ≤ k → P00.coeff k = 0 := fun k hk => by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have hsq : P00.natDegree ≤ 2 * D.P.natDegree := Polynomial.natDegree_pow_le
    omega
  have hP00_c1 : P00.coeff (D.S.card + 1 - 1) = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have hsq : P00.natDegree ≤ 2 * D.P.natDegree := Polynomial.natDegree_pow_le
    omega
  have hP01_deg : ∀ k, D.S.card + 1 ≤ k → P01.coeff k = 0 := fun k hk => by
    rcases hQcase with hQ0 | hQdeg
    · simp [P01, hQ0]
    · apply Polynomial.coeff_eq_zero_of_natDegree_lt
      have hmul : (D.P * D.Q).natDegree ≤ D.P.natDegree + D.Q.natDegree := Polynomial.natDegree_mul_le
      have hcmul : P01.natDegree ≤ (D.P * D.Q).natDegree := by
        dsimp [P01]
        exact (Polynomial.natDegree_mul_le).trans (by rw [Polynomial.natDegree_C, zero_add])
      omega
  have hP01_c1 : P01.coeff (D.S.card + 1 - 1) = 0 := by
    rcases hQcase with hQ0 | hQdeg
    · simp [P01, hQ0]
    · apply Polynomial.coeff_eq_zero_of_natDegree_lt
      have hmul : (D.P * D.Q).natDegree ≤ D.P.natDegree + D.Q.natDegree := Polynomial.natDegree_mul_le
      have hcmul : P01.natDegree ≤ (D.P * D.Q).natDegree := by
        dsimp [P01]
        exact (Polynomial.natDegree_mul_le).trans (by rw [Polynomial.natDegree_C, zero_add])
      omega
  have hP11_deg : ∀ k, D.S.card + 1 - 1 ≤ k → P11.coeff k = 0 := fun k hk => by
    rcases hQcase with hQ0 | hQdeg
    · simp [P11, hQ0]
    · apply Polynomial.coeff_eq_zero_of_natDegree_lt
      have hsq : P11.natDegree ≤ 2 * D.Q.natDegree := Polynomial.natDegree_pow_le
      omega
  have hP11_c2 : P11.coeff (D.S.card + 1 - 2) = 0 := by
    rcases hQcase with hQ0 | hQdeg
    · simp [P11, hQ0]
    · apply Polynomial.coeff_eq_zero_of_natDegree_lt
      have hsq : P11.natDegree ≤ 2 * D.Q.natDegree := Polynomial.natDegree_pow_le
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
  have hB_R : B ≤ R_star := by
    have hB0 : 0 ≤ B := (abs_nonneg D.tm).trans hB_tm
    linarith [le_max_right (4 : ℝ) (2 * B + 2)]
  have hQH_rt : ∀ z : ℂ, Polynomial.aeval z Q_H = 0 → z.im = 0 ∧ ‖z‖ ≤ R_star := by
    intro z hz
    rw [hQH_eq z, mul_eq_zero] at hz
    rcases hz with htm | hqs
    · have heq : z = (D.tm : ℂ) := sub_eq_zero.mp htm
      rw [heq, Complex.ofReal_im, Complex.norm_real, Real.norm_eq_abs]
      exact ⟨rfl, hB_tm.trans hB_R⟩
    · exact ⟨(hQ_rt z hqs).1, (hQ_rt z hqs).2.trans hB_R⟩
  have hneg1 : (-1 : ℝ) ^ D.S.card = -1 := hOdd.neg_one_pow
  refine ⟨(terminal_cardinal_integral D).1, R_star, max C0 (max C1 C2),
    P00, Q_H, P01, Q_H, P11, Q_H, hR4, by positivity, hQH_monic, hQH_monic, hQH_monic,
    hQH_rt, hQH_rt, hQH_rt, fun z hz => ?_, fun w hw => ?_⟩
  · have hQH_nz : Polynomial.aeval z Q_H ≠ 0 := fun h0 => not_le_of_gt hz (hQH_rt z h0).2
    have htm_nz : z - (D.tm : ℂ) ≠ 0 := fun h0 =>
      hQH_nz (by rw [hQH_eq z, h0, zero_mul])
    have hdsl : dslope (fun u => -D.G u) (D.tm : ℂ) z = (-D.G z) / (z - (D.tm : ℂ)) := by
      rw [dslope_of_ne _ (sub_ne_zero.mp htm_nz), slope_def_field, D.G_eq_zero_on_S D.tm D.tm_mem,
        neg_zero, sub_zero]
    have hpr_eq : at47_pr D.S z = Polynomial.aeval z Q_S := (hQ_eq z).symm
    have hG := D.G_prod_eq z
    rw [hpr_eq, hneg1] at hG
    rw [hdsl]
    apply mul_right_cancel₀ hQH_nz
    have hLHS : ((-D.G z) / (z - (D.tm : ℂ))) * Polynomial.aeval z Q_H =
        (-D.G z) * Polynomial.aeval z Q_S := by
      rw [hQH_eq z]; field_simp [htm_nz]
    rw [hLHS]
    have hG_alg : (-D.G z) * Polynomial.aeval z Q_S = airyPQN D.P D.Q z ^ 2 := by
      have hG' : D.G z * Polynomial.aeval z Q_S = (-1 : ℂ) * airyPQN D.P D.Q z ^ 2 := by
        simpa using hG
      linear_combination -hG'
    rw [hG_alg]
    have hsum :
        ((Polynomial.aeval z P00 / Polynomial.aeval z Q_H) * airyAiC z ^ 2 +
          (Polynomial.aeval z P01 / Polynomial.aeval z Q_H) * (airyAiC z * deriv airyAiC z) +
          (Polynomial.aeval z P11 / Polynomial.aeval z Q_H) * deriv airyAiC z ^ 2) *
          Polynomial.aeval z Q_H =
        Polynomial.aeval z P00 * airyAiC z ^ 2 +
          Polynomial.aeval z P01 * (airyAiC z * deriv airyAiC z) +
          Polynomial.aeval z P11 * deriv airyAiC z ^ 2 := by
      field_simp [hQH_nz]
    rw [hsum]
    dsimp [P00, P01, P11]
    simp only [airyPQN, map_pow, map_mul, aeval_C, Complex.coe_algebraMap, aeval_eq_airyPQc]
    norm_num
    ring
  · have hw0 : ‖w‖ ^ (-2 : ℝ) ≥ 0 := by positivity
    have hw03 : ‖w‖ ^ (-3 : ℝ) ≥ 0 := by positivity
    refine ⟨?_, ?_, ?_⟩
    · simpa only [Complex.ofReal_zero, zero_mul, sub_zero] using
        (has0 w hw).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hw0)
    · exact (has1 w hw).trans (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) hw0)
    · simpa only [Complex.ofReal_zero, zero_mul, sub_zero] using
        (has2 w hw).trans (mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) hw03)


/-! ### Part 4: `HBSeedSpec` for General `ShellHBData` with `Odd D.S.card` -/

lemma lip_on_Icc_of_entire {F : ℂ → ℂ} (hF : Differentiable ℂ F) (R : ℝ) :
    ∃ A ≥ 0, ∀ x y : ℝ, |x| ≤ R → |y| ≤ R → ‖F (x : ℂ) - F (y : ℂ)‖ ≤ A * |x - y| := by
  by_cases hR : R < 0
  · refine ⟨0, le_rfl, fun x _ hx => absurd ((abs_nonneg x).trans hx) (not_le_of_gt hR)⟩
  have hR0 : 0 ≤ R := not_lt.mp hR
  have hcont : Continuous (deriv F) :=
    continuousOn_univ.mp (hF.differentiableOn.analyticOnNhd isOpen_univ).deriv.continuousOn
  obtain ⟨z₀, -, hz₀⟩ := (isCompact_closedBall (0 : ℂ) R).exists_isMaxOn
    ⟨(0 : ℂ), Metric.mem_closedBall_self hR0⟩ hcont.norm.continuousOn
  let A : ℝ := max ‖deriv F z₀‖ 0
  refine ⟨A, le_max_right _ _, fun x y hx hy => ?_⟩
  let f : ℝ → ℂ := fun t => F (t : ℂ)
  have hf_deriv : ∀ t ∈ Icc (-R) R, HasDerivAt f (deriv F (t : ℂ)) t := fun t _ => by
    simpa only [mul_one] using (hF (t : ℂ)).hasDerivAt.comp_ofReal
  have hx_mem : x ∈ Icc (-R) R := abs_le.mp hx
  have hy_mem : y ∈ Icc (-R) R := abs_le.mp hy
  have hz_mem : ∀ t ∈ Icc (-R) R, (t : ℂ) ∈ Metric.closedBall (0 : ℂ) R := fun t ht => by
    simp only [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ht
  have hle := (convex_Icc (-R) R).norm_image_sub_le_of_norm_deriv_le (C := A)
    (fun t ht => (hf_deriv t ht).differentiableAt)
    (fun t ht => by rw [(hf_deriv t ht).deriv]; exact (hz₀ (hz_mem t ht)).trans (le_max_left _ _))
    hy_mem hx_mem
  simpa [f, Real.norm_eq_abs, abs_sub_comm] using hle

lemma eval_neg_poly_bound (R : ℝ[X]) (d : ℕ) (hR : ∀ k, d ≤ k → R.coeff k = 0)
    {y : ℝ} (hy1 : 1 ≤ y) :
    |R.eval (-y)| * y ≤ (∑ k ∈ Finset.range d, |R.coeff k|) * y ^ d := by
  by_cases hR0 : R = 0
  · subst hR0
    simp only [Polynomial.eval_zero, abs_zero, zero_mul, Polynomial.coeff_zero,
      Finset.sum_const_zero, le_refl]
  · have hlt : R.natDegree < d := by
      by_contra hge; push Not at hge
      exact Polynomial.leadingCoeff_ne_zero.mpr hR0 (hR R.natDegree hge)
    have hd1 : 1 ≤ d := by omega
    rw [Polynomial.eval_eq_sum_range]
    have hsum_le : |∑ k ∈ Finset.range (R.natDegree + 1), R.coeff k * (-y) ^ k| ≤
        (∑ k ∈ Finset.range d, |R.coeff k|) * y ^ (d - 1) := by
      calc |∑ k ∈ Finset.range (R.natDegree + 1), R.coeff k * (-y) ^ k|
          ≤ ∑ k ∈ Finset.range (R.natDegree + 1), |R.coeff k * (-y) ^ k| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k ∈ Finset.range (R.natDegree + 1), |R.coeff k| * y ^ (d - 1) := by
            refine Finset.sum_le_sum fun k hk => ?_
            have hk_lt : k < R.natDegree + 1 := Finset.mem_range.mp hk
            rw [abs_mul, abs_pow, abs_neg, abs_of_nonneg (a := y) (by linarith)]
            exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hy1 (by omega)) (abs_nonneg _)
        _ = (∑ k ∈ Finset.range (R.natDegree + 1), |R.coeff k|) * y ^ (d - 1) :=
            (Finset.sum_mul _ _ _).symm
        _ ≤ (∑ k ∈ Finset.range d, |R.coeff k|) * y ^ (d - 1) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) fun _ _ _ => abs_nonneg _
    calc |∑ k ∈ Finset.range (R.natDegree + 1), R.coeff k * (-y) ^ k| * y
        ≤ ((∑ k ∈ Finset.range d, |R.coeff k|) * y ^ (d - 1)) * y :=
          mul_le_mul_of_nonneg_right hsum_le (by linarith)
      _ = (∑ k ∈ Finset.range d, |R.coeff k|) * (y ^ (d - 1) * y) := by ring
      _ = (∑ k ∈ Finset.range d, |R.coeff k|) * y ^ d := by
          rw [← pow_succ, Nat.sub_add_cancel hd1]

lemma hb_osc_tail_of_odd (D : ShellHBData) (hOdd : Odd D.S.card) :
    ∃ (c_osc C_r y₁ ϑ_c : ℝ), 0 < c_osc ∧ 0 ≤ C_r ∧ 25 ≤ y₁ ∧
      ∃ r : ℝ → ℝ, ∀ y ≥ y₁,
        |r y| ≤ C_r * y ^ (-(1 / 2 : ℝ)) ∧
        c_osc * y ^ (-(3 / 2 : ℝ)) * (Real.cos ((2 / 3 : ℝ) * y ^ (3 / 2 : ℝ) + ϑ_c) + r y) ^ 2 ≤
          (D.G ((-y : ℝ) : ℂ)).re := by
  obtain ⟨hPne, hmP, hQcase⟩ := shellHBData_P_degree_of_odd D hOdd
  let d : ℕ := D.P.natDegree
  let p_d : ℝ := D.P.leadingCoeff
  have hp_d : p_d ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hPne
  let sgn : ℝ := (-1 : ℝ) ^ d * p_d
  have hsgn : sgn ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) hp_d
  let B : ℝ := D.S.sup' D.S_nonempty (fun t => |t|)
  have hB : ∀ t ∈ D.S, |t| ≤ B := fun t ht => Finset.le_sup' (fun s => |s|) ht
  have hB0 : 0 ≤ B := (abs_nonneg D.tm).trans (hB D.tm D.tm_mem)
  let Q_plus : ℝ[X] := ∏ t ∈ D.S, (Polynomial.X + Polynomial.C t)
  have hQp_monic : Q_plus.Monic :=
    Polynomial.monic_prod_of_monic D.S _ fun t _ => Polynomial.monic_X_add_C t
  have hQp_deg : Q_plus.natDegree = D.S.card := by
    dsimp [Q_plus]
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun t _ => Polynomial.monic_X_add_C t)]
    simp
  have hQp_eval : ∀ y : ℝ, Q_plus.eval y = ∏ t ∈ D.S, (y + t) := fun y => by
    dsimp [Q_plus]; simp [Polynomial.eval_prod]
  let R_den : ℝ[X] := Q_plus - Polynomial.X ^ D.S.card
  have hR_den_deg : R_den.natDegree ≤ 2 * d := by
    by_cases h0 : R_den = 0
    · simp [h0]
    · have hlt : R_den.natDegree < D.S.card := by
        have hlc : R_den.coeff D.S.card = 0 := by
          have h1 : Q_plus.coeff D.S.card = 1 := by
            rw [← hQp_deg, Polynomial.coeff_natDegree]
            exact hQp_monic.leadingCoeff
          have h2 : (Polynomial.X ^ D.S.card : ℝ[X]).coeff D.S.card = 1 :=
            Polynomial.coeff_X_pow_self D.S.card
          simp only [R_den, Polynomial.coeff_sub]
          linarith [h1, h2]
        have hle : R_den.natDegree ≤ D.S.card := by
          refine (Polynomial.natDegree_sub_le _ _).trans ?_
          rw [hQp_deg, Polynomial.natDegree_X_pow, max_self]
        rcases hle.eq_or_lt with heq | hlt
        · exfalso; exact h0 (Polynomial.leadingCoeff_eq_zero.mp (by rw [← Polynomial.coeff_natDegree, heq, hlc]))
        · exact hlt
      omega
  let C_den : ℝ := ∑ k ∈ Finset.range (2 * d + 1), |R_den.coeff k|
  have hR_den_bd : ∀ y : ℝ, 1 ≤ y → |Q_plus.eval y - y ^ (2 * d + 1)| ≤ C_den * y ^ (2 * d) := by
    intro y hy1
    have hsub : Q_plus.eval y - y ^ (2 * d + 1) = R_den.eval y := by
      dsimp [R_den]; rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, hmP]
    rw [hsub, Polynomial.eval_eq_sum_range]
    calc |∑ k ∈ Finset.range (R_den.natDegree + 1), R_den.coeff k * y ^ k|
        ≤ ∑ k ∈ Finset.range (R_den.natDegree + 1), |R_den.coeff k * y ^ k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range (R_den.natDegree + 1), |R_den.coeff k| * y ^ (2 * d) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk_lt : k < R_den.natDegree + 1 := Finset.mem_range.mp hk
          rw [abs_mul, abs_of_nonneg (a := y ^ k) (pow_nonneg (by linarith) _)]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hy1 (by omega)) (abs_nonneg _)
      _ = (∑ k ∈ Finset.range (R_den.natDegree + 1), |R_den.coeff k|) * y ^ (2 * d) :=
          (Finset.sum_mul _ _ _).symm
      _ ≤ C_den * y ^ (2 * d) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) fun _ _ _ => abs_nonneg _
  let P_rem : ℝ[X] := D.P - Polynomial.C p_d * Polynomial.X ^ d
  have hP_rem_deg : ∀ k, d ≤ k → P_rem.coeff k = 0 := by
    intro k hk
    simp only [P_rem, Polynomial.coeff_sub, Polynomial.coeff_C_mul_X_pow]
    split_ifs with hkd
    · subst hkd
      change D.P.coeff D.P.natDegree - D.P.leadingCoeff = 0
      rw [Polynomial.coeff_natDegree, sub_self]
    · have hkgt : d < k := lt_of_le_of_ne hk (Ne.symm hkd)
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hkgt, sub_zero]
  let C_Prem : ℝ := ∑ k ∈ Finset.range d, |P_rem.coeff k|
  let C_Q : ℝ := ∑ k ∈ Finset.range d, |D.Q.coeff k|
  let y₁ : ℝ := max 25 (2 * B + 2)
  have hy₁_25 : 25 ≤ y₁ := le_max_left _ _
  have hy₁_B : 2 * B + 2 ≤ y₁ := le_max_right _ _
  let C_den' : ℝ := 2 ^ (2 * d + 1) * C_den
  let C_Prem' : ℝ := C_Prem / |p_d|
  let C_α : ℝ := (1 + C_Prem') * C_den' + C_Prem'
  let C_S : ℝ := √π / 8
  let K_P : ℝ := (√π + 1) * C_α + C_S
  let K_Q : ℝ := √π * 2 ^ ((2 * d + 1 : ℕ) / 2 + 1) * 10 * C_Q / |p_d|
  let C_r : ℝ := K_P + K_Q
  let r : ℝ → ℝ := fun y =>
    if y₁ ≤ y then
      (√π * y ^ (3 / 4 : ℝ) / sgn) * (at47_Nf D.P D.Q (-y) / √(∏ t ∈ D.S, (y + t))) -
        Real.sin (cohnTheta y)
    else 0
  refine ⟨p_d ^ 2 / π, C_r, y₁, -(π / 4), div_pos (sq_pos_of_ne_zero hp_d) Real.pi_pos,
    by positivity, hy₁_25, r, fun y hy => ?_⟩
  have hy25 : 25 ≤ y := hy₁_25.trans hy
  have hy1 : 1 ≤ y := by linarith
  have hy0 : 0 < y := by linarith
  have hyB : 2 * B + 2 ≤ y := hy₁_B.trans hy
  have hyt_lb : ∀ t ∈ D.S, y / 2 ≤ y + t := fun t ht => by
    have := (abs_le.mp (hB t ht)).1; linarith
  have hprod_lb : (y / 2) ^ (2 * d + 1) ≤ ∏ t ∈ D.S, (y + t) := by
    rw [show 2 * d + 1 = D.S.card from hmP, ← Finset.prod_const (b := y / 2)]
    gcongr with t ht
    exact hyt_lb t ht
  have hprod_pos : 0 < ∏ t ∈ D.S, (y + t) := lt_of_lt_of_le (by positivity) hprod_lb
  let den : ℝ := √(∏ t ∈ D.S, (y + t))
  have hden_pos : 0 < den := Real.sqrt_pos.mpr hprod_pos
  have hden_lb : (1 / 2 : ℝ) ^ ((2 * d + 1 : ℕ) / 2 + 1) * y ^ (d + 1 / 2 : ℝ) ≤ den := by
    have hpow_le : (y / 2) ^ (2 * d + 1) = (1 / 2 : ℝ) ^ (2 * d + 1) * y ^ (2 * d + 1) := by ring
    have hsq_lb : (1 / 2 : ℝ) ^ (2 * d + 2) * y ^ (2 * d + 1) ≤ ∏ t ∈ D.S, (y + t) := by
      have h12 : (1 / 2 : ℝ) ^ (2 * d + 2) ≤ (1 / 2 : ℝ) ^ (2 * d + 1) := by
        rw [pow_succ]; linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (2 * d + 1)]
      calc (1 / 2 : ℝ) ^ (2 * d + 2) * y ^ (2 * d + 1)
          ≤ (1 / 2 : ℝ) ^ (2 * d + 1) * y ^ (2 * d + 1) := by gcongr
        _ = (y / 2) ^ (2 * d + 1) := hpow_le.symm
        _ ≤ _ := hprod_lb
    have hsq_rt : √((1 / 2 : ℝ) ^ (2 * d + 2) * y ^ (2 * d + 1)) =
        (1 / 2 : ℝ) ^ (d + 1) * y ^ (d + 1 / 2 : ℝ) := by
      rw [Real.sqrt_mul (by positivity), ← Real.rpow_natCast (1 / 2 : ℝ) (2 * d + 2),
        ← Real.rpow_natCast y (2 * d + 1), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
        ← Real.rpow_mul (by norm_num), ← Real.rpow_mul hy0.le]
      have e1 : ((2 * d + 2 : ℕ) : ℝ) * (1 / 2 : ℝ) = ((d + 1 : ℕ) : ℝ) := by push_cast; ring
      have e2 : ((2 * d + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) = (d : ℝ) + 1 / 2 := by push_cast; ring
      rw [e1, e2, Real.rpow_natCast]
    have hexp_eq : ((2 * d + 1 : ℕ) / 2 + 1 : ℕ) = d + 1 := by omega
    rw [hexp_eq, ← hsq_rt]
    exact Real.sqrt_le_sqrt hsq_lb
  have hcos_eq : Real.cos ((2 / 3 : ℝ) * y ^ (3 / 2 : ℝ) + -(π / 4)) = Real.sin (cohnTheta y) := by
    rw [← Real.cos_sub_pi_div_two (cohnTheta y)]
    unfold cohnTheta
    congr 1; ring
  have hr_def : r y = (√π * y ^ (3 / 4 : ℝ) / sgn) * (at47_Nf D.P D.Q (-y) / den) - Real.sin (cohnTheta y) := by
    simp only [r, hy, ↓reduceIte]; rfl
  have hyS : -y ∉ D.S := fun hmem => by
    have := (abs_le.mp (hB (-y) hmem)).1; linarith
  have hG_eq : (D.G ((-y : ℝ) : ℂ)).re = at47_Nf D.P D.Q (-y) ^ 2 / den ^ 2 := by
    have hF := at47_F_real_formula D.G_prod_eq hyS
    rw [hF, Complex.ofReal_re]
    have hprod_neg : ∏ t ∈ D.S, (-y - t) = (-1 : ℝ) ^ D.S.card * ∏ t ∈ D.S, (y + t) := by
      have he : ∀ t ∈ D.S, -y - t = (-1 : ℝ) * (y + t) := fun t _ => by ring
      rw [Finset.prod_congr rfl he, Finset.prod_mul_distrib, Finset.prod_const]
    rw [hprod_neg, Real.sq_sqrt hprod_pos.le]
    have hne1 : (-1 : ℝ) ^ D.S.card = -1 := hOdd.neg_one_pow
    rw [hne1]; ring
  refine ⟨?_, ?_⟩
  · -- Bound `|r y| ≤ C_r * y ^ (-1/2)`.
    let α : ℝ := (y ^ (1 / 2 : ℝ) / sgn) * (D.P.eval (-y) / den)
    let S_Ai : ℝ := √π * y ^ (1 / 4 : ℝ) * airyAi (-y)
    let Q_term : ℝ := (√π * y ^ (3 / 4 : ℝ) / sgn) * (D.Q.eval (-y) * airyAi' (-y) / den)
    have hr_split : r y = (α * S_Ai - Real.sin (cohnTheta y)) + Q_term := by
      have hy34 : y ^ (1 / 2 : ℝ) * y ^ (1 / 4 : ℝ) = y ^ (3 / 4 : ℝ) := by
        rw [← Real.rpow_add hy0]; norm_num
      rw [hr_def]; unfold at47_Nf; dsimp [α, S_Ai, Q_term]
      calc (√π * y ^ (3 / 4 : ℝ) / sgn) *
            ((D.P.eval (-y) * airyAi (-y) + D.Q.eval (-y) * airyAi' (-y)) / den) - Real.sin (cohnTheta y)
          = (√π * (y ^ (1 / 2 : ℝ) * y ^ (1 / 4 : ℝ)) / sgn) *
              (D.P.eval (-y) * airyAi (-y) / den) +
              (√π * y ^ (3 / 4 : ℝ) / sgn) * (D.Q.eval (-y) * airyAi' (-y) / den) -
              Real.sin (cohnTheta y) := by rw [hy34]; ring
        _ = ((y ^ (1 / 2 : ℝ) / sgn) * (D.P.eval (-y) / den) * (√π * y ^ (1 / 4 : ℝ) * airyAi (-y)) -
              Real.sin (cohnTheta y)) +
              (√π * y ^ (3 / 4 : ℝ) / sgn) * (D.Q.eval (-y) * airyAi' (-y) / den) := by ring
    -- Common rpow helpers
    have hy_m1_le_m12 : y⁻¹ ≤ y ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_neg_one y]
      exact Real.rpow_le_rpow_of_exponent_le hy1 (by norm_num)
    have hy_m32_le_m12 : y ^ (-(3 / 2 : ℝ)) ≤ y ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hy1 (by norm_num)
    -- 1. `|S_Ai - sin(cohnTheta y)| ≤ C_S * y^(-3/2)` and `|S_Ai| ≤ √π + 1`
    have hSAi_bd : |S_Ai - Real.sin (cohnTheta y)| ≤ C_S * y ^ (-(3 / 2 : ℝ)) := by
      have hAi := airyAi_neg_asymptotic_theta hy0
      have hid : S_Ai - Real.sin (cohnTheta y) =
          (√π * y ^ (1 / 4 : ℝ)) * (airyAi (-y) - Real.sin (cohnTheta y) / (√π * y ^ (1 / 4 : ℝ))) := by
        dsimp [S_Ai]; field_simp [Real.sqrt_pos.mpr Real.pi_pos, Real.rpow_pos_of_pos hy0 _]
      rw [hid, abs_mul, abs_of_pos (mul_pos (Real.sqrt_pos.mpr Real.pi_pos) (by positivity))]
      have hm := mul_le_mul_of_nonneg_left hAi (by positivity : 0 ≤ √π * y ^ (1 / 4 : ℝ))
      have hexp : y ^ (1 / 4 : ℝ) * (y ^ (7 / 4 : ℝ))⁻¹ = y ^ (-(3 / 2 : ℝ)) := by
        rw [← Real.rpow_neg hy0.le, ← Real.rpow_add hy0]; norm_num
      calc √π * y ^ (1 / 4 : ℝ) * |airyAi (-y) - Real.sin (cohnTheta y) / (√π * y ^ (1 / 4 : ℝ))|
          ≤ √π * y ^ (1 / 4 : ℝ) * (1 / (8 * y ^ (7 / 4 : ℝ))) := hm
        _ = (√π / 8) * (y ^ (1 / 4 : ℝ) * (y ^ (7 / 4 : ℝ))⁻¹) := by ring
        _ = C_S * y ^ (-(3 / 2 : ℝ)) := by rw [hexp]
    have hSAi_abs : |S_Ai| ≤ √π + 1 := by
      have htri := abs_add_le (S_Ai - Real.sin (cohnTheta y)) (Real.sin (cohnTheta y))
      rw [sub_add_cancel] at htri
      have hy32_le : y ^ (-(3 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hy1 (by norm_num)
      have hC_S0 : 0 ≤ C_S := by dsimp [C_S]; positivity
      have h1 : |S_Ai - Real.sin (cohnTheta y)| ≤ √π := by
        calc |S_Ai - Real.sin (cohnTheta y)| ≤ C_S * y ^ (-(3 / 2 : ℝ)) := hSAi_bd
          _ ≤ C_S * 1 := mul_le_mul_of_nonneg_left hy32_le hC_S0
          _ = √π / 8 := mul_one _
          _ ≤ √π := by linarith [Real.sqrt_pos.mpr Real.pi_pos]
      linarith [Real.abs_sin_le_one (cohnTheta y)]
    -- 2. `|α - 1| ≤ C_α * y⁻¹`
    have hPrem_bd : |P_rem.eval (-y)| * y ≤ C_Prem * y ^ d :=
      eval_neg_poly_bound P_rem d hP_rem_deg hy1
    let p_rat : ℝ := D.P.eval (-y) / (sgn * y ^ d)
    let u : ℝ := y ^ (d + 1 / 2 : ℝ) / den
    have hu_pos : 0 < u := by positivity
    have hα_eq : α = p_rat * u := by
      have hy_d : y ^ (1 / 2 : ℝ) * y ^ d = y ^ (d + 1 / 2 : ℝ) := by
        rw [← Real.rpow_natCast y d, ← Real.rpow_add hy0]; congr 1; ring
      dsimp [α, p_rat, u]
      calc (y ^ (1 / 2 : ℝ) / sgn) * (D.P.eval (-y) / den)
          = (D.P.eval (-y) / (sgn * y ^ d)) * ((y ^ (1 / 2 : ℝ) * y ^ d) / den) := by
            field_simp [hsgn, pow_ne_zero d hy0.ne', hden_pos.ne']
        _ = (D.P.eval (-y) / (sgn * y ^ d)) * (y ^ (d + 1 / 2 : ℝ) / den) := by rw [hy_d]
    have hp_rat_bd : |p_rat - 1| ≤ C_Prem' * y⁻¹ := by
      have hid : p_rat - 1 = P_rem.eval (-y) / (sgn * y ^ d) := by
        have hP_eval : D.P.eval (-y) = P_rem.eval (-y) + sgn * y ^ d := by
          dsimp [P_rem, sgn]
          rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
            Polynomial.eval_X, neg_pow]
          ring
        dsimp [p_rat]; rw [hP_eval]; field_simp [hsgn, pow_ne_zero d hy0.ne']; ring
      have hsgn_abs : |sgn| = |p_d| := by
        dsimp [sgn]; rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      rw [hid, abs_div, abs_mul, hsgn_abs, abs_of_pos (pow_pos hy0 d)]
      calc |P_rem.eval (-y)| / (|p_d| * y ^ d)
          = (|P_rem.eval (-y)| * y) / (|p_d| * y ^ d * y) := by field_simp [hy0.ne']
        _ ≤ (C_Prem * y ^ d) / (|p_d| * y ^ d * y) := div_le_div_of_nonneg_right hPrem_bd (by positivity)
        _ = C_Prem' * y⁻¹ := by
            dsimp [C_Prem']; field_simp [abs_pos.mpr hp_d, pow_ne_zero d hy0.ne', hy0.ne']
    have hu_bd : |u - 1| ≤ C_den' * y⁻¹ := by
      have hu_sq : u ^ 2 - 1 = (y ^ (2 * d + 1) - Q_plus.eval y) / Q_plus.eval y := by
        have hden_sq : den ^ 2 = Q_plus.eval y := by rw [hQp_eval y, Real.sq_sqrt hprod_pos.le]
        have hy_sq : (y ^ (d + 1 / 2 : ℝ)) ^ 2 = y ^ (2 * d + 1) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hy0.le, ← Real.rpow_natCast]
          congr 1; push_cast; ring
        dsimp [u]; rw [div_pow, hy_sq, hden_sq]; field_simp [hQp_eval y ▸ hprod_pos.ne']
      have hQp_lb : (1 / 2 : ℝ) ^ (2 * d + 1) * y ^ (2 * d + 1) ≤ Q_plus.eval y := by
        rw [hQp_eval y]; refine le_trans ?_ hprod_lb; rw [div_eq_mul_inv, mul_pow]; ring_nf; rfl
      have hQp_pos : 0 < Q_plus.eval y := by rw [hQp_eval y]; exact hprod_pos
      have hu2_bd : |u ^ 2 - 1| ≤ C_den' * y⁻¹ := by
        rw [hu_sq, abs_div, abs_of_pos hQp_pos, abs_sub_comm]
        calc |Q_plus.eval y - y ^ (2 * d + 1)| / Q_plus.eval y
            ≤ (C_den * y ^ (2 * d)) / ((1 / 2 : ℝ) ^ (2 * d + 1) * y ^ (2 * d + 1)) :=
              div_le_div₀ (by positivity) (hR_den_bd y hy1) (by positivity) hQp_lb
          _ = C_den' * y⁻¹ := by
              dsimp [C_den']
              have hinv : ((1 / 2 : ℝ) ^ (2 * d + 1))⁻¹ = (2 : ℝ) ^ (2 * d + 1) := by
                simp only [one_div, inv_pow, inv_inv]
              rw [div_eq_mul_inv, mul_inv, hinv, show y ^ (2 * d + 1) = y ^ (2 * d) * y from pow_succ y (2 * d),
                mul_inv]
              field_simp [pow_ne_zero (2 * d) hy0.ne', hy0.ne']
      have hu1_ge : 1 ≤ u + 1 := by linarith
      have hid_u : |u - 1| * (u + 1) = |u ^ 2 - 1| := by
        rw [← abs_of_pos (by linarith : 0 < u + 1), ← abs_mul]
        congr 1; ring
      calc |u - 1| = |u ^ 2 - 1| / (u + 1) := eq_div_of_mul_eq (by linarith) hid_u
        _ ≤ |u ^ 2 - 1| / 1 := div_le_div_of_nonneg_left (abs_nonneg _) zero_lt_one hu1_ge
        _ = |u ^ 2 - 1| := div_one _
        _ ≤ C_den' * y⁻¹ := hu2_bd
    have hα_bd : |α - 1| ≤ C_α * y ^ (-(1 / 2 : ℝ)) := by
      have hp_abs : |p_rat| ≤ 1 + C_Prem' := by
        have htri := abs_add_le (p_rat - 1) 1
        rw [sub_add_cancel, abs_one] at htri
        have h1 : C_Prem' * y⁻¹ ≤ C_Prem' :=
          mul_le_of_le_one_right (by dsimp [C_Prem']; positivity) (inv_le_one_of_one_le₀ hy1)
        linarith
      have hα_eq1 : α - 1 = p_rat * (u - 1) + (p_rat - 1) := by rw [hα_eq]; ring
      calc |α - 1| ≤ |p_rat * (u - 1)| + |p_rat - 1| := hα_eq1 ▸ abs_add_le _ _
        _ = |p_rat| * |u - 1| + |p_rat - 1| := by rw [abs_mul]
        _ ≤ (1 + C_Prem') * (C_den' * y⁻¹) + C_Prem' * y⁻¹ := by gcongr
        _ = C_α * y⁻¹ := by dsimp [C_α]; ring
        _ ≤ C_α * y ^ (-(1 / 2 : ℝ)) := mul_le_mul_of_nonneg_left hy_m1_le_m12 (by dsimp [C_α, C_Prem', C_den']; positivity)
    -- 3. `|Q_term| ≤ K_Q * y^(-1/2)`
    have hQ_term_bd : |Q_term| ≤ K_Q * y ^ (-(1 / 2 : ℝ)) := by
      have hQ_coeff : ∀ k, d ≤ k → D.Q.coeff k = 0 := fun k hk => by
        rcases hQcase with hQ0 | hQdeg
        · simp [hQ0]
        · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      have hQ_poly := eval_neg_poly_bound D.Q d hQ_coeff hy1
      have hAi'_bd : |airyAi' (-y)| ≤ 10 * y ^ (1 / 4 : ℝ) := by
        have hb := (airyAi_and_deriv_neg_bounds (neg_nonpos.mpr hy0.le)).2
        rw [abs_neg, abs_of_pos hy0] at hb
        have h1y : 1 + y ≤ 2 * y := by linarith
        have hrpow : (1 + y) ^ (1 / 4 : ℝ) ≤ (2 : ℝ) ^ (1 / 4 : ℝ) * y ^ (1 / 4 : ℝ) := by
          rw [← Real.mul_rpow (by norm_num) hy0.le]
          exact Real.rpow_le_rpow (by linarith) h1y (by norm_num)
        have h214 : (2 : ℝ) ^ (1 / 4 : ℝ) ≤ 2 :=
          Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
        have hy40 : 0 ≤ y ^ (1 / 4 : ℝ) := by positivity
        nlinarith [hb, hrpow, h214, hy40]
      have hsgn_abs : |sgn| = |p_d| := by
        dsimp [sgn]; rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      have hpow_simp : y ^ (3 / 4 : ℝ) * (y ^ d * y⁻¹) * y ^ (1 / 4 : ℝ) / y ^ (d + 1 / 2 : ℝ) =
          y ^ (-(1 / 2 : ℝ)) := by
        rw [← Real.rpow_natCast y d, ← Real.rpow_neg_one y, ← Real.rpow_add hy0,
          ← Real.rpow_add hy0, ← Real.rpow_add hy0, ← Real.rpow_sub hy0]
        congr 1; ring
      dsimp [Q_term]
      rw [abs_mul, abs_div, abs_mul, abs_of_pos (Real.sqrt_pos.mpr Real.pi_pos),
        abs_of_pos (Real.rpow_pos_of_pos hy0 _), hsgn_abs, abs_div, abs_mul, abs_of_pos hden_pos]
      calc (√π * y ^ (3 / 4 : ℝ) / |p_d|) * (|D.Q.eval (-y)| * |airyAi' (-y)| / den)
          ≤ (√π * y ^ (3 / 4 : ℝ) / |p_d|) *
              (((C_Q * y ^ d * y⁻¹) * (10 * y ^ (1 / 4 : ℝ))) /
                ((1 / 2 : ℝ) ^ ((2 * d + 1 : ℕ) / 2 + 1) * y ^ (d + 1 / 2 : ℝ))) := by
            have hQ1 : |D.Q.eval (-y)| ≤ C_Q * y ^ d * y⁻¹ := by
              rw [le_mul_inv_iff₀ hy0]; exact hQ_poly
            gcongr
        _ = (√π * 2 ^ ((2 * d + 1 : ℕ) / 2 + 1) * 10 * C_Q / |p_d|) *
              (y ^ (3 / 4 : ℝ) * (y ^ d * y⁻¹) * y ^ (1 / 4 : ℝ) / y ^ (d + 1 / 2 : ℝ)) := by
            simp only [one_div (2 : ℝ), inv_pow, div_eq_mul_inv, mul_inv, inv_inv]
            ring
        _ = K_Q * y ^ (-(1 / 2 : ℝ)) := by rw [hpow_simp]
    -- Combine `|r y|`
    have hP_bd : |α * S_Ai - Real.sin (cohnTheta y)| ≤ K_P * y ^ (-(1 / 2 : ℝ)) := by
      have hid : α * S_Ai - Real.sin (cohnTheta y) = (α - 1) * S_Ai + (S_Ai - Real.sin (cohnTheta y)) := by ring
      rw [hid]
      calc |(α - 1) * S_Ai + (S_Ai - Real.sin (cohnTheta y))|
          ≤ |α - 1| * |S_Ai| + |S_Ai - Real.sin (cohnTheta y)| := by
            rw [← abs_mul]; exact abs_add_le _ _
        _ ≤ (C_α * y ^ (-(1 / 2 : ℝ))) * (√π + 1) + C_S * y ^ (-(1 / 2 : ℝ)) := by
            have h1 := mul_le_mul hα_bd hSAi_abs (abs_nonneg _) (by positivity)
            have h2 := hSAi_bd.trans (mul_le_mul_of_nonneg_left hy_m32_le_m12 (by positivity))
            exact add_le_add h1 h2
        _ = K_P * y ^ (-(1 / 2 : ℝ)) := by dsimp [K_P]; ring
    rw [hr_split]
    calc |(α * S_Ai - Real.sin (cohnTheta y)) + Q_term|
        ≤ |α * S_Ai - Real.sin (cohnTheta y)| + |Q_term| := abs_add_le _ _
      _ ≤ K_P * y ^ (-(1 / 2 : ℝ)) + K_Q * y ^ (-(1 / 2 : ℝ)) := add_le_add hP_bd hQ_term_bd
      _ = C_r * y ^ (-(1 / 2 : ℝ)) := by dsimp [C_r]; ring
  · -- Identity `c_osc * y ^ (-3/2) * (cos + r)^2 = G_N(-y)`.
    rw [hcos_eq, hr_def, add_sub_cancel, hG_eq]
    have hsgn2 : sgn ^ 2 = p_d ^ 2 := by
      dsimp [sgn]; rw [mul_pow, pow_right_comm, neg_one_sq, one_pow, one_mul]
    have hy32 : (y ^ (3 / 4 : ℝ)) ^ 2 = y ^ (3 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hy0.le]; norm_num
    have hy_inv : y ^ (-(3 / 2 : ℝ)) * y ^ (3 / 2 : ℝ) = 1 := by
      rw [← Real.rpow_add hy0]; norm_num
    have hmul_sq : (√π * y ^ (3 / 4 : ℝ) / sgn) ^ 2 = π * y ^ (3 / 2 : ℝ) / p_d ^ 2 := by
      rw [div_pow, mul_pow, Real.sq_sqrt Real.pi_pos.le, hy32, hsgn2]
    rw [mul_pow, hmul_sq, div_pow]
    calc (p_d ^ 2 / π) * y ^ (-(3 / 2 : ℝ)) *
          ((π * y ^ (3 / 2 : ℝ) / p_d ^ 2) * (at47_Nf D.P D.Q (-y) ^ 2 / den ^ 2))
        = (p_d ^ 2 / p_d ^ 2) * (π / π) * (y ^ (-(3 / 2 : ℝ)) * y ^ (3 / 2 : ℝ)) *
            (at47_Nf D.P D.Q (-y) ^ 2 / den ^ 2) := by ring
      _ ≤ at47_Nf D.P D.Q (-y) ^ 2 / den ^ 2 := by
          rw [div_self (pow_ne_zero 2 hp_d), div_self Real.pi_pos.ne', hy_inv, one_mul, one_mul, one_mul]


/-- Descending enumeration of `D.S` (`t_1 > ⋯ > t_{m₀}`). -/
noncomputable def shellNodes (D : ShellHBData) : Fin D.S.card → ℝ :=
  fun j => ((D.S.orderIsoOfFin rfl) ⟨D.S.card - 1 - j.val, by omega⟩ : ℝ)

lemma shellNodes_strictAnti (D : ShellHBData) : StrictAnti (shellNodes D) := by
  intro i j hij
  dsimp [shellNodes]
  have hlt : (⟨D.S.card - 1 - j.val, by omega⟩ : Fin D.S.card) <
      ⟨D.S.card - 1 - i.val, by omega⟩ := by
    change D.S.card - 1 - j.val < D.S.card - 1 - i.val; omega
  exact (D.S.orderIsoOfFin rfl).strictMono hlt

lemma shellNodes_last (D : ShellHBData) :
    shellNodes D ⟨D.S.card - 1, Nat.sub_lt (Finset.card_pos.mpr D.S_nonempty) zero_lt_one⟩ = D.tm := by
  have hm₀ : 1 ≤ D.S.card := Finset.card_pos.mpr D.S_nonempty
  let iso : Fin D.S.card ≃o D.S := D.S.orderIsoOfFin rfl
  let t_last : ℝ := shellNodes D ⟨D.S.card - 1, Nat.sub_lt hm₀ zero_lt_one⟩
  have hmem : t_last ∈ D.S := (iso ⟨D.S.card - 1 - (D.S.card - 1), by omega⟩).2
  have hle1 : D.tm ≤ t_last := D.tm_min t_last hmem
  have hle2 : t_last ≤ D.tm := by
    let k := iso.symm ⟨D.tm, D.tm_mem⟩
    have hidx : (⟨0, hm₀⟩ : Fin D.S.card) ≤ k := Nat.zero_le k.val
    have := iso.monotone hidx
    change (iso ⟨0, hm₀⟩ : ℝ) ≤ (iso k : ℝ) at this
    rw [iso.apply_symm_apply] at this
    have h0_eq : (⟨D.S.card - 1 - (D.S.card - 1), by omega⟩ : Fin D.S.card) = ⟨0, hm₀⟩ :=
      Fin.ext (by simp)
    dsimp [t_last, shellNodes]
    rw [h0_eq]
    exact this
  exact le_antisymm hle2 hle1

/-- Constructs `HBSeedSpec` (`AirySeedFloors.lean`) for any `D : ShellHBData` with `Odd D.S.card`. -/
noncomputable def hbSeedSpec_of_shellHBData (D : ShellHBData) (hOdd : Odd D.S.card) : HBSeedSpec := by
  classical
  let m₀ : ℕ := D.S.card
  have hm₀ : 1 ≤ m₀ := Finset.card_pos.mpr D.S_nonempty
  let iso : Fin m₀ ≃o D.S := D.S.orderIsoOfFin rfl
  let nodes : Fin m₀ → ℝ := shellNodes D
  have hnodes_anti : StrictAnti nodes := shellNodes_strictAnti D
  have hlast_eq : nodes ⟨m₀ - 1, Nat.sub_lt hm₀ zero_lt_one⟩ = D.tm := shellNodes_last D
  have hlast_a1 : nodes ⟨m₀ - 1, Nat.sub_lt hm₀ zero_lt_one⟩ ≤ airyZero 1 :=
    hlast_eq ▸ D.tm_le_airyZero_one
  let H_C : ℂ → ℂ := dslope (fun z => -D.G z) (D.tm : ℂ)
  obtain ⟨hH_inAiry, hdiv_int, hI_eq, hI_pos⟩ := terminal_cardinal_integral D
  let I_N : ℝ := ∫ u : ℝ, (-(D.G (u : ℂ)).re) / (u - D.tm)
  have hH_ae : (fun u : ℝ => (H_C (u : ℂ)).re) =ᵐ[MeasureTheory.volume]
      (fun u : ℝ => (-(D.G (u : ℂ)).re) / (u - D.tm)) := by
    have hne_ae : ∀ᵐ u : ℝ ∂MeasureTheory.volume, u ≠ D.tm :=
      ae_iff.mpr (by simpa using measure_singleton D.tm)
    filter_upwards [hne_ae] with u hu
    have huc : (u : ℂ) ≠ (D.tm : ℂ) := fun h => hu (Complex.ofReal_injective h)
    have hd : H_C (u : ℂ) = (-D.G (u : ℂ)) / ((u : ℂ) - (D.tm : ℂ)) := by
      dsimp [H_C]; rw [dslope_of_ne _ huc, slope_def_field, D.G_eq_zero_on_S D.tm D.tm_mem, neg_zero, sub_zero]
    have hc : -D.G (u : ℂ) = ((-(D.G (u : ℂ)).re : ℝ) : ℂ) :=
      Complex.ext rfl (by simp [D.G_real u])
    rw [hd, hc, show ((u : ℂ) - (D.tm : ℂ)) = ((u - D.tm : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_div, Complex.ofReal_re]
  have hI_int_H : ∫ u : ℝ, (H_C (u : ℂ)).re = I_N := integral_congr_ae hH_ae
  let B : ℝ := D.S.sup' D.S_nonempty (fun t => |t|)
  let R_lip : ℝ := B + 1
  let hG_ex := lip_on_Icc_of_entire D.G_diff R_lip
  let A_G : ℝ := hG_ex.choose
  have hAG : 0 ≤ A_G := hG_ex.choose_spec.1
  have hG_lip : ∀ x y : ℝ, |x| ≤ R_lip → |y| ≤ R_lip → ‖D.G (x : ℂ) - D.G (y : ℂ)‖ ≤ A_G * |x - y| :=
    hG_ex.choose_spec.2
  let hH_ex := lip_on_Icc_of_entire hH_inAiry.1 R_lip
  let A_H : ℝ := hH_ex.choose
  have hAH : 0 ≤ A_H := hH_ex.choose_spec.1
  have hH_lip : ∀ x y : ℝ, |x| ≤ R_lip → |y| ≤ R_lip → ‖H_C (x : ℂ) - H_C (y : ℂ)‖ ≤ A_H * |x - y| :=
    hH_ex.choose_spec.2
  have hnode_mem : ∀ j : Fin m₀, nodes j ∈ D.S := fun j => (iso _).2
  have hnode_bd : ∀ j : Fin m₀, |nodes j| ≤ B := fun j =>
    Finset.le_sup' (fun s => |s|) (hnode_mem j)
  let hosc := hb_osc_tail_of_odd D hOdd
  exact
    { m₀ := m₀
      m₀_pos := hm₀
      nodes := nodes
      nodes_anti := hnodes_anti
      last_le_a1 := hlast_a1
      G_N := fun u => (D.G (u : ℂ)).re
      H_N := fun u => (H_C (u : ℂ)).re
      I_N := I_N
      I_N_pos := hI_pos
      continuous_G := Complex.continuous_re.comp (D.G_diff.continuous.comp Complex.continuous_ofReal)
      continuous_H := Complex.continuous_re.comp (hH_inAiry.1.continuous.comp Complex.continuous_ofReal)
      integrable_G := D.G_int.re
      integrable_H := hH_inAiry.2.1.re
      integral_G := by
        change ∫ u : ℝ, RCLike.re (D.G (u : ℂ)) = 0
        rw [integral_re D.G_int, D.G_integral_zero]; rfl
      integral_H := hI_int_H
      G_nonneg_tail := fun u hu => D.G_nonneg_left u (hlast_eq ▸ hu)
      H_eq_div_tail := fun u hu => by
        have hult : u < D.tm := hlast_eq ▸ hu
        have huc : (u : ℂ) ≠ (D.tm : ℂ) := fun h => hult.ne (Complex.ofReal_injective h)
        have hd : H_C (u : ℂ) = (-D.G (u : ℂ)) / ((u : ℂ) - (D.tm : ℂ)) := by
          dsimp [H_C]; rw [dslope_of_ne _ huc, slope_def_field, D.G_eq_zero_on_S D.tm D.tm_mem, neg_zero, sub_zero]
        have hc : -D.G (u : ℂ) = ((-(D.G (u : ℂ)).re : ℝ) : ℂ) := by
          apply Complex.ext <;> simp [D.G_real u]
        rw [hd, hc, show ((u : ℂ) - (D.tm : ℂ)) = ((u - D.tm : ℝ) : ℂ) by push_cast; ring,
          ← Complex.ofReal_div, Complex.ofReal_re, hlast_eq]
        field_simp [show u - D.tm ≠ 0 by linarith, show -u + D.tm ≠ 0 by linarith]
        ring
      node_vanish := fun j hj => by
        have hmem := hnode_mem j
        have hG0 : (D.G (nodes j : ℂ)).re = 0 := by rw [D.G_eq_zero_on_S _ hmem, Complex.zero_re]
        have hlt_idx : j < (⟨m₀ - 1, Nat.sub_lt hm₀ zero_lt_one⟩ : Fin m₀) :=
          Fin.lt_def.mpr (by dsimp only; omega)
        have hgt : D.tm < nodes j := hlast_eq ▸ hnodes_anti hlt_idx
        have hne : (nodes j : ℂ) ≠ (D.tm : ℂ) := fun h => hgt.ne' (Complex.ofReal_injective h)
        have hd : H_C (nodes j : ℂ) = (-D.G (nodes j : ℂ)) / ((nodes j : ℂ) - (D.tm : ℂ)) := by
          dsimp [H_C]; rw [dslope_of_ne _ hne, slope_def_field, D.G_eq_zero_on_S D.tm D.tm_mem, neg_zero, sub_zero]
        have hH0 : (H_C (nodes j : ℂ)).re = 0 := by
          rw [hd, D.G_eq_zero_on_S _ hmem, neg_zero, zero_div, Complex.zero_re]
        exact ⟨hG0, hH0⟩
      r_node := 1
      r_node_pos := one_pos
      A_G := A_G
      A_H := A_H
      A_G_nonneg := hAG
      A_H_nonneg := hAH
      G_lip_near := fun j _ u hu => by
        have hjn : |nodes j| ≤ R_lip := (hnode_bd j).trans (by linarith)
        have hu_r : |u| ≤ R_lip := by
          calc |u| = |(u - nodes j) + nodes j| := by ring_nf
            _ ≤ |u - nodes j| + |nodes j| := abs_add_le _ _
            _ ≤ 1 + B := add_le_add hu (hnode_bd j)
            _ = R_lip := by dsimp [R_lip]; ring
        have hG0 : D.G (nodes j : ℂ) = 0 := D.G_eq_zero_on_S _ (hnode_mem j)
        calc |(D.G (u : ℂ)).re| = |(D.G (u : ℂ) - D.G (nodes j : ℂ)).re| := by rw [hG0, sub_zero]
          _ ≤ ‖D.G (u : ℂ) - D.G (nodes j : ℂ)‖ := Complex.abs_re_le_norm _
          _ ≤ A_G * |u - nodes j| := hG_lip u (nodes j) hu_r hjn
      H_lip_near := fun j hj u hu => by
        have hjn : |nodes j| ≤ R_lip := (hnode_bd j).trans (by linarith)
        have hu_r : |u| ≤ R_lip := by
          calc |u| = |(u - nodes j) + nodes j| := by ring_nf
            _ ≤ |u - nodes j| + |nodes j| := abs_add_le _ _
            _ ≤ 1 + B := add_le_add hu (hnode_bd j)
            _ = R_lip := by dsimp [R_lip]; ring
        have hlt_idx : j < (⟨m₀ - 1, Nat.sub_lt hm₀ zero_lt_one⟩ : Fin m₀) :=
          Fin.lt_def.mpr (by dsimp only; omega)
        have hgt : D.tm < nodes j := hlast_eq ▸ hnodes_anti hlt_idx
        have hne : (nodes j : ℂ) ≠ (D.tm : ℂ) := fun h => hgt.ne' (Complex.ofReal_injective h)
        have hH0 : H_C (nodes j : ℂ) = 0 := by
          dsimp [H_C]; rw [dslope_of_ne _ hne, slope_def_field, D.G_eq_zero_on_S _ (hnode_mem j),
            D.G_eq_zero_on_S D.tm D.tm_mem, neg_zero, sub_self, zero_div]
        calc |(H_C (u : ℂ)).re| = |(H_C (u : ℂ) - H_C (nodes j : ℂ)).re| := by rw [hH0, sub_zero]
          _ ≤ ‖H_C (u : ℂ) - H_C (nodes j : ℂ)‖ := Complex.abs_re_le_norm _
          _ ≤ A_H * |u - nodes j| := hH_lip u (nodes j) hu_r hjn
      c_osc_G := hosc.choose
      C_r_G := hosc.choose_spec.choose
      y₁_G := hosc.choose_spec.choose_spec.choose
      ϑ_c_G := hosc.choose_spec.choose_spec.choose_spec.choose
      c_osc_G_pos := hosc.choose_spec.choose_spec.choose_spec.choose_spec.1
      C_r_G_nonneg := hosc.choose_spec.choose_spec.choose_spec.choose_spec.2.1
      y₁_G_ge := hosc.choose_spec.choose_spec.choose_spec.choose_spec.2.2.1
      G_osc_tail := hosc.choose_spec.choose_spec.choose_spec.choose_spec.2.2.2 }

lemma hbSeedSpec_of_shellHBData_lastNode (D : ShellHBData) (hOdd : Odd D.S.card) :
    (hbSeedSpec_of_shellHBData D hOdd).lastNode = D.tm :=
  shellNodes_last D

lemma hbSeedSpec_of_shellHBData_nodes_range (D : ShellHBData) (hOdd : Odd D.S.card) :
    Set.range (hbSeedSpec_of_shellHBData D hOdd).nodes = (D.S : Set ℝ) := by
  change Set.range (shellNodes D) = (D.S : Set ℝ)
  ext x
  constructor
  · rintro ⟨j, rfl⟩
    exact ((D.S.orderIsoOfFin rfl) _).2
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

lemma hbSeedSpec_of_shellHBData_exists_site (D : ShellHBData) (hOdd : Odd D.S.card)
    {t : ℝ} (htS : t ∈ D.S) (htm : t ≠ D.tm) :
    ∃ j : Fin (hbSeedSpec_of_shellHBData D hOdd).m₀,
      j.val + 1 < (hbSeedSpec_of_shellHBData D hOdd).m₀ ∧
      (hbSeedSpec_of_shellHBData D hOdd).nodes j = t := by
  have hmem : t ∈ Set.range (hbSeedSpec_of_shellHBData D hOdd).nodes := by
    rw [hbSeedSpec_of_shellHBData_nodes_range]; exact htS
  obtain ⟨j, hj⟩ := hmem
  refine ⟨j, ?_, hj⟩
  by_contra hge
  push Not at hge
  have hjlt : j.val < (hbSeedSpec_of_shellHBData D hOdd).m₀ := j.isLt
  have hjeq : j = ⟨D.S.card - 1, Nat.sub_lt (Finset.card_pos.mpr D.S_nonempty) zero_lt_one⟩ := by
    have hm_eq : (hbSeedSpec_of_shellHBData D hOdd).m₀ = D.S.card := rfl
    exact Fin.ext (by dsimp only; omega)
  have hlast : shellNodes D ⟨D.S.card - 1, Nat.sub_lt (Finset.card_pos.mpr D.S_nonempty) zero_lt_one⟩ = D.tm :=
    shellNodes_last D
  have hnd : (hbSeedSpec_of_shellHBData D hOdd).nodes j = shellNodes D j := rfl
  rw [hnd, hjeq] at hj
  exact htm (hj.symm.trans hlast)

end FormalResearch.SignUncertainty
