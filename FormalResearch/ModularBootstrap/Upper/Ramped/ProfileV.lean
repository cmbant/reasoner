module

public import FormalResearch.ModularBootstrap.Upper.Ramped.ProfileR1

/-!
# Lemma V for profiles (`ut:V`, `rem:profile`): Airy quadrature

For an arbitrary admissible profile `(uSite, epsU)` and shift `d`, the entire product
`W = profW uSite epsU d = airyWindowProd 1 (a_1 - d) uSite epsU` satisfies

* `profV_hasSum`: `∫ W = ∑_{n ≥ 1} W(a_n) / Ai'(a_n)²`, absolutely convergent;
* `profV_eval_one`, `profV_eval_succ`: `W(a_1)/Ai'(a_1)² = -d R_1`, `W(a_n)/Ai'(a_n)² = Π_n(d)`;
* `profV_identity`: for `d ∈ [0, |a_1 - a_2|)`, `Π_n(d) ∈ [0, Π_n(0)]`,
  `∫ W = -d R_1 + ∑_{n ≥ 2} Π_n(d) ≤ -d R_1 + E_0`.

This is the profile version of `lemma_V_hasSum`, `profV_eval_one`, `profV_eval_succ`,
`lemma_V_identity` (`Window/Quadrature.lean`), with the proofs of those lemmas.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real BigOperators

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.Special FormalResearch.ModularBootstrap.Upper.Window

/-- The profile Airy product `W = W^{(1)}` with first site `a_1 - d`. -/
noncomputable def profW (uSite epsU : ℕ → ℝ) (d : ℝ) (u : ℂ) : ℂ :=
  airyWindowProd 1 (airyZero 1 - d) uSite epsU u

theorem profW_differentiable (uSite epsU : ℕ → ℝ) (hH : AiryProdTailHypothesis 1 uSite epsU) (d : ℝ) :
    Differentiable ℂ (profW uSite epsU d) :=
  airyWindowProd_differentiable 1 le_rfl (airyZero 1 - d) uSite epsU hH

theorem profW_bound (uSite epsU : ℕ → ℝ) (hH : AiryProdTailHypothesis 1 uSite epsU) (d : ℝ) :
    ∃ C > 0, ∀ u : ℂ, ‖profW uSite epsU d u‖ ≤ C * (1 + ‖u‖) ^ (-(3 / 2 : ℝ)) * airyEnv u := by
  obtain ⟨C, hC, hbd⟩ := airyWindowProd_bound 1 le_rfl (airyZero 1 - d) uSite epsU hH
  refine ⟨C, hC, fun u => ?_⟩
  have := hbd u
  rw [show -((2 * ((1 : ℕ) : ℝ) - 1 / 2)) = -(3 / 2 : ℝ) by norm_num] at this
  exact this

theorem profW_integrable (uSite epsU : ℕ → ℝ) (hH : AiryProdTailHypothesis 1 uSite epsU) (d : ℝ) :
    Integrable (fun x : ℝ => profW uSite epsU d (x : ℂ)) := by
  obtain ⟨C, hC, hbd⟩ := profW_bound uSite epsU hH d
  exact airy_integrable_real (profW_differentiable uSite epsU hH d) hC.le (by norm_num) hbd

/-- **Lemma V (`ut:V`), quadrature and absolute convergence**:
$\int_{\mathbb{R}} W(u)\,du = \sum_{n \ge 1} W(a_n) / \Ai'(a_n)^2$, with the series absolutely convergent. -/
theorem profV_hasSum (uSite epsU : ℕ → ℝ) (hH : AiryProdTailHypothesis 1 uSite epsU) (d : ℝ) :
    HasSum (fun n : ℕ => profW uSite epsU d (airyZero (n + 1) : ℂ) /
        (deriv airyAiC (airyZero (n + 1) : ℂ)) ^ 2)
      (∫ x : ℝ, profW uSite epsU d (x : ℂ)) ∧
    Summable (fun n : ℕ => ‖profW uSite epsU d (airyZero (n + 1) : ℂ) /
        (deriv airyAiC (airyZero (n + 1) : ℂ)) ^ 2‖) := by
  obtain ⟨C, hC, hbd'⟩ := profW_bound uSite epsU hH d
  have hdiff := profW_differentiable uSite epsU hH d
  exact ⟨airy_quadrature hdiff hC.le (by norm_num) hbd',
    (airy_summable_weighted hC.le (by norm_num) hbd').norm⟩

/-- Evaluation at $a_1$: $W(a_1) / \Ai'(a_1)^2 = -d R_1$. -/
theorem profV_eval_one (uSite epsU : ℕ → ℝ) (hH : AiryProdTailHypothesis 1 uSite epsU) (d : ℝ) :
    profW uSite epsU d (airyZero 1 : ℂ) / (deriv airyAiC (airyZero 1 : ℂ)) ^ 2 =
      ((-d * profR1 uSite epsU : ℝ) : ℂ) := by
  unfold profW
  rw [airyWindowProd_at_airyZero_le 1 (airyZero 1 - d) (uSite) (epsU)
    le_rfl le_rfl]
  have htail := (profR1_hasProd uSite epsU hH).2
  rw [htail]
  have h_erase : (Finset.Icc 1 1).erase 1 = ∅ := by decide
  rw [h_erase, Finset.prod_empty, div_one]
  have hderiv_ne : deriv airyAiC (airyZero 1 : ℂ) ≠ 0 := airyZero_deriv_ne_zero 1
  have hsub : (airyZero 1 : ℂ) - ((airyZero 1 - d : ℝ) : ℂ) = (d : ℂ) := by push_cast; ring
  rw [hsub]
  field_simp [hderiv_ne]
  push_cast
  ring

/-- Evaluation at $a_n$ ($n \ge 2$): $W(a_n) / \Ai'(a_n)^2 = \Pi_n(d)$. -/
theorem profV_eval_succ (uSite epsU : ℕ → ℝ) (hH : AiryProdTailHypothesis 1 uSite epsU) (d : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    profW uSite epsU d (airyZero n : ℂ) / (deriv airyAiC (airyZero n : ℂ)) ^ 2 =
      (profPi uSite epsU d n : ℂ) := by
  unfold profW
  rw [airyWindowProd_at_airyZero_gt 1 (airyZero 1 - d) (uSite) (epsU)
    (by omega : 1 < n)]
  have htail := (profPi0_hasProd uSite epsU hH hn).2
  rw [htail]
  have hIcc : Finset.Icc 1 1 = {1} := by decide
  rw [hIcc, Finset.prod_singleton]
  have hderiv_ne : deriv airyAiC (airyZero n : ℂ) ≠ 0 := airyZero_deriv_ne_zero n
  have han_lt : airyZero n < airyZero 1 := airyZero_lt_of_lt le_rfl (by omega)
  have hdiff_ne : (airyZero n : ℂ) - (airyZero 1 : ℂ) ≠ 0 := by
    exact_mod_cast (sub_ne_zero.mpr han_lt.ne)
  have habs : |airyZero n - airyZero 1| = airyZero 1 - airyZero n := by
    rw [abs_of_neg (by linarith)]
    ring
  have hnum : -((airyZero n : ℂ) - ((airyZero 1 - d : ℝ) : ℂ)) / ((airyZero n : ℂ) - (airyZero 1 : ℂ)) ^ 2 =
      (((1 - d / |airyZero n - airyZero 1|) / |airyZero n - airyZero 1| : ℝ) : ℂ) := by
    have h1 : airyZero 1 - airyZero n ≠ 0 := by linarith
    have hnum_r : -(airyZero n - (airyZero 1 - d)) / (airyZero n - airyZero 1) ^ 2 =
        (1 - d / |airyZero n - airyZero 1|) / |airyZero n - airyZero 1| := by
      rw [habs]
      have hne_sq : airyZero n - airyZero 1 ≠ 0 := by linarith
      field_simp [h1, hne_sq]
      ring
    exact_mod_cast hnum_r
  have heq_lhs : -(deriv airyAiC (airyZero n : ℂ)) ^ 2 * ((airyZero n : ℂ) - ((airyZero 1 - d : ℝ) : ℂ)) /
      ((airyZero n : ℂ) - (airyZero 1 : ℂ)) ^ 2 *
      (((airyZero n : ℂ) - (uSite n : ℂ)) ^ 2 + (epsU n : ℂ) ^ 2) *
      ((∏' m : ℕ, if m + 2 = n then (1 : ℝ) else profRealFactor uSite epsU n (m + 2) : ℝ) : ℂ) /
      (deriv airyAiC (airyZero n : ℂ)) ^ 2 =
      (-((airyZero n : ℂ) - ((airyZero 1 - d : ℝ) : ℂ)) / ((airyZero n : ℂ) - (airyZero 1 : ℂ)) ^ 2) *
      (((airyZero n : ℂ) - (uSite n : ℂ)) ^ 2 + (epsU n : ℂ) ^ 2) *
      ((∏' m : ℕ, if m + 2 = n then (1 : ℝ) else profRealFactor uSite epsU n (m + 2) : ℝ) : ℂ) := by
    generalize deriv airyAiC (airyZero n : ℂ) = D at hderiv_ne ⊢
    generalize (airyZero n : ℂ) - ((airyZero 1 - d : ℝ) : ℂ) = Num
    generalize (airyZero n : ℂ) - (airyZero 1 : ℂ) = Den at hdiff_ne ⊢
    generalize (((airyZero n : ℂ) - (uSite n : ℂ)) ^ 2 + (epsU n : ℂ) ^ 2) = Q
    generalize ((∏' m : ℕ, if m + 2 = n then (1 : ℝ) else profRealFactor uSite epsU n (m + 2) : ℝ) : ℂ) = T
    field_simp [hderiv_ne, hdiff_ne]
  rw [heq_lhs, hnum]
  unfold profPi profPi0
  push_cast
  ring

/-- **Lemma V (`ut:V`), real identity and upper bound**:
for $d \in [0, |a_1 - a_2|)$, $\Pi_n(d) \ge 0$,
$V := \int_{\mathbb{R}} W(u)\,du = -d R_1 + \sum_{n \ge 2} \Pi_n(d) \le -d R_1 + E_0$. -/
theorem profV_identity (uSite epsU : ℕ → ℝ) (hH : AiryProdTailHypothesis 1 uSite epsU) (d : ℝ) (hd0 : 0 ≤ d) (hd1 : d < |airyZero 1 - airyZero 2|) :
    (∀ n : ℕ, 2 ≤ n → 0 ≤ profPi uSite epsU d n ∧ profPi uSite epsU d n ≤ profPi0 uSite epsU n) ∧
    Summable (fun n : ℕ => profPi uSite epsU d (n + 2)) ∧
    Summable (fun n : ℕ => profPi0 uSite epsU (n + 2)) ∧
    (∫ x : ℝ, (profW uSite epsU d (x : ℂ)).re) =
      -d * profR1 uSite epsU + ∑' n : ℕ, profPi uSite epsU d (n + 2) ∧
    (∫ x : ℝ, (profW uSite epsU d (x : ℂ)).re) ≤
      -d * profR1 uSite epsU + profE0 uSite epsU := by
  have hpi_le : ∀ n : ℕ, 2 ≤ n →
      0 ≤ profPi uSite epsU d n ∧ profPi uSite epsU d n ≤ profPi0 uSite epsU n := by
    intro n hn
    have h12 : airyZero 1 - airyZero 2 ≤ airyZero 1 - airyZero n := by
      rcases hn.eq_or_lt with rfl | h2n
      · exact le_rfl
      · linarith [airyZero_lt_of_lt (by omega) h2n]
    have habs_12 : |airyZero 1 - airyZero 2| = airyZero 1 - airyZero 2 :=
      abs_of_nonneg (by linarith [airyZero_strictAnti le_rfl])
    have habs_n : |airyZero n - airyZero 1| = airyZero 1 - airyZero n := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith [airyZero_lt_of_lt le_rfl (by omega : 1 < n)])]
    have hd_lt : d < |airyZero n - airyZero 1| := by linarith
    have hpos : 0 < |airyZero n - airyZero 1| := lt_of_le_of_lt hd0 hd_lt
    have hfac_ge : 0 ≤ 1 - d / |airyZero n - airyZero 1| := by
      rw [sub_nonneg, div_le_one hpos]; exact hd_lt.le
    have hfac_le : 1 - d / |airyZero n - airyZero 1| ≤ 1 := by
      have : 0 ≤ d / |airyZero n - airyZero 1| := div_nonneg hd0 hpos.le
      linarith
    have h0 := profPi0_nonneg uSite epsU hH hn
    unfold profPi
    exact ⟨mul_nonneg h0 hfac_ge, mul_le_of_le_one_right h0 hfac_le⟩
  obtain ⟨hhas, hsum_norm⟩ := profV_hasSum uSite epsU hH d
  have hhas_re : HasSum (fun n : ℕ =>
      (profW uSite epsU d (airyZero (n + 1) : ℂ) /
        (deriv airyAiC (airyZero (n + 1) : ℂ)) ^ 2).re)
      (∫ x : ℝ, (profW uSite epsU d (x : ℂ)).re) := by
    have hint := profW_integrable uSite epsU hH d
    have h_int : (∫ x : ℝ, profW uSite epsU d (x : ℂ)).re =
        ∫ x : ℝ, (profW uSite epsU d (x : ℂ)).re := (integral_re hint).symm
    rw [← h_int]
    exact Complex.reCLM.hasSum hhas
  have hsplit := hasSum_nat_add_iff' 1 |>.mpr hhas_re
  have hterm0 : (profW uSite epsU d (airyZero 1 : ℂ) /
      (deriv airyAiC (airyZero 1 : ℂ)) ^ 2).re = -d * profR1 uSite epsU := by
    rw [profV_eval_one uSite epsU hH d, Complex.ofReal_re]
  have hterm_succ : ∀ n : ℕ, (profW uSite epsU d (airyZero (n + 2) : ℂ) /
      (deriv airyAiC (airyZero (n + 2) : ℂ)) ^ 2).re = profPi uSite epsU d (n + 2) := fun n => by
    rw [profV_eval_succ uSite epsU hH d (by omega), Complex.ofReal_re]
  have hsum_pi : Summable (fun n : ℕ => profPi uSite epsU d (n + 2)) := by
    have hs1 := (summable_nat_add_iff 1).mpr hhas_re.summable
    refine hs1.congr fun n => ?_
    simpa [Nat.add_assoc] using (hterm_succ n)
  have hid : (∫ x : ℝ, (profW uSite epsU d (x : ℂ)).re) =
      -d * profR1 uSite epsU + ∑' n : ℕ, profPi uSite epsU d (n + 2) := by
    have htsum := hhas_re.tsum_eq.symm
    rw [Summable.tsum_eq_zero_add hhas_re.summable] at htsum
    simp only [zero_add] at htsum
    have hshift : (∑' n : ℕ, (profW uSite epsU d (airyZero (n + 1 + 1) : ℂ) /
        (deriv airyAiC (airyZero (n + 1 + 1) : ℂ)) ^ 2).re) =
        ∑' n : ℕ, profPi uSite epsU d (n + 2) := by
      refine tsum_congr fun n => ?_
      rw [show n + 1 + 1 = n + 2 by ring, hterm_succ n]
    rw [hterm0, hshift] at htsum
    exact htsum
  have hsum_pi0 : Summable (fun n : ℕ => profPi0 uSite epsU (n + 2)) := by
    have h_ratio_pos : 0 < 1 - d / |airyZero 1 - airyZero 2| := by
      have hpos : 0 < |airyZero 1 - airyZero 2| := lt_of_le_of_lt hd0 hd1
      rw [sub_pos, div_lt_one hpos]; exact hd1
    have h_le : ∀ n : ℕ, profPi0 uSite epsU (n + 2) ≤
        (1 - d / |airyZero 1 - airyZero 2|)⁻¹ * profPi uSite epsU d (n + 2) := fun n => by
      have h12 : airyZero 1 - airyZero 2 ≤ airyZero 1 - airyZero (n + 2) := by
        rcases eq_or_lt_of_le (by omega : 2 ≤ n + 2) with h2 | h2n
        · rw [← h2]
        · linarith [airyZero_lt_of_lt (by omega) h2n]
      have habs_12 : |airyZero 1 - airyZero 2| = airyZero 1 - airyZero 2 :=
        abs_of_nonneg (by linarith [airyZero_strictAnti le_rfl])
      have habs_n : |airyZero (n + 2) - airyZero 1| = airyZero 1 - airyZero (n + 2) := by
        rw [abs_sub_comm, abs_of_nonneg (by linarith [airyZero_lt_of_lt le_rfl (by omega : 1 < n + 2)])]
      have hfac_ge : 1 - d / |airyZero 1 - airyZero 2| ≤ 1 - d / |airyZero (n + 2) - airyZero 1| := by
        have hpos12 : 0 < |airyZero 1 - airyZero 2| := lt_of_le_of_lt hd0 hd1
        have hpos12 : 0 < |airyZero 1 - airyZero 2| := lt_of_le_of_lt hd0 hd1
        have : d / |airyZero (n + 2) - airyZero 1| ≤ d / |airyZero 1 - airyZero 2| :=
          div_le_div_of_nonneg_left hd0 hpos12 (by linarith)
        linarith
      unfold profPi
      have h0 := profPi0_nonneg uSite epsU hH (by omega : 2 ≤ n + 2)
      calc profPi0 uSite epsU (n + 2)
          = profPi0 uSite epsU (n + 2) * ((1 - d / |airyZero 1 - airyZero 2|)⁻¹ *
              (1 - d / |airyZero 1 - airyZero 2|)) := by
              rw [inv_mul_cancel₀ h_ratio_pos.ne', mul_one]
        _ ≤ profPi0 uSite epsU (n + 2) * ((1 - d / |airyZero 1 - airyZero 2|)⁻¹ *
              (1 - d / |airyZero (n + 2) - airyZero 1|)) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hfac_ge (inv_nonneg.mpr h_ratio_pos.le)) h0
        _ = (1 - d / |airyZero 1 - airyZero 2|)⁻¹ *
              (profPi0 uSite epsU (n + 2) * (1 - d / |airyZero (n + 2) - airyZero 1|)) := by ring
    refine Summable.of_nonneg_of_le (fun n => profPi0_nonneg uSite epsU hH (by omega))
      h_le (hsum_pi.mul_left _)
  have hle : (∫ x : ℝ, (profW uSite epsU d (x : ℂ)).re) ≤
      -d * profR1 uSite epsU + profE0 uSite epsU := by
    rw [hid]
    unfold profE0
    exact add_le_add_right (hsum_pi.tsum_le_tsum (fun n => (hpi_le (n + 2) (by omega)).2) hsum_pi0) _
  exact ⟨hpi_le, hsum_pi, hsum_pi0, hid, hle⟩

end FormalResearch.ModularBootstrap.Upper.Ramped
