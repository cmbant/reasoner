module

public import FormalResearch.SignUncertainty.HankelBootData
public import FormalResearch.SignUncertainty.HankelQuantC1Feasible

/-!
# Hankel node sums (`hP_nodes_lb_hb`, `P_theta_bound`) with explicit `r_∞` slack

The Hankel transcription of the node-sum lower bounds of the FixedWeightBand file
`BootstrapWNodes.lean`.  The good-circle node sum `∑_{n=1}^N Re f_{k,ℓ}(a_n)/Ai'(a_n)²` of the shifted
Hankel test `Ψ̃(u+ℓ)(1+u/R)^{k+1}` is bounded below using `Re Ψ̃ ≥ -r_∞` on the zeros left of `u_T`
(`hankel_psi_sign`).  Every lost term carries the explicit slack `(6π)² r_∞`; the counting bound
`N ≤ C R^{3/2}` is not part of this module, so `(N : ℝ)` stays in the slack.

Claim classes: all results are proved (no numerical input); the inputs are the Hankel lemmas
`hankel_psi_sign`, `hankel_phi_anti`, `analyticOnNhd_hankelPsi`, `hankelPsi_real`,
`hankelRinf_nonneg`, and the Airy zero facts `airyZero_one`, `airyZero_two`, `airyZero_anti`,
`airyZero_neg`, `airyZero_inv_deriv_sq_le`, and the `QuantC1B2Holds` constants.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set Metric
open scoped Real Interval

namespace FormalResearch.SignUncertainty

open FormalResearch.Special FormalResearch.ModularBootstrap.ConcreteBootstrap

/-- Good-circle node sum `Σ_{n=1}^N Re f_{k,ℓ}(a_n)/Ai'(a_n)²` of the shifted Hankel test. -/
noncomputable def hankelBootNodes (c : ℝ) (f : ℝ → ℝ) (R ℓ : ℝ) (k N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, (hankelBootShifted c f R ℓ k (airyZero n : ℂ)).re / airyAi' (airyZero n) ^ 2

/-- `1 / Ai'(a_n)² ≤ (6π)²` for every zero index, from `airyZero_inv_deriv_sq_le` and `a_n < 0`. -/
theorem hankelBoot_airyAi'_sq_inv_le (n : ℕ) : (airyAi' (airyZero n) ^ 2)⁻¹ ≤ (6 * π) ^ 2 := by
  have hderiv := airyZero_inv_deriv_sq_le n
  have hneg : airyZero n < 0 := airyZero_neg n
  have hrp : (1 + (-airyZero n)) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have hD : ‖((deriv airyAiC (airyZero n : ℂ)) ^ 2)⁻¹‖ = (airyAi' (airyZero n) ^ 2)⁻¹ := by
    rw [deriv_airyAiC_ofReal, ← Complex.ofReal_pow, ← Complex.ofReal_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
  rw [← hD]
  calc ‖((deriv airyAiC (airyZero n : ℂ)) ^ 2)⁻¹‖
      ≤ 36 * π ^ 2 * (1 + (-airyZero n)) ^ (-(1 / 2 : ℝ)) := hderiv
    _ ≤ 36 * π ^ 2 * 1 := by gcongr
    _ = (6 * π) ^ 2 := by ring

/-- `x ∈ [0,1]` and `-Q ≤ P` with `Q ≥ 0` give `-Q ≤ x P`. -/
theorem hankelBoot_mul_ge {x P Q : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hQ : 0 ≤ Q) (hP : -Q ≤ P) :
    -Q ≤ x * P := by
  nlinarith [mul_nonneg hx0 (by linarith : (0 : ℝ) ≤ P + Q),
    mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - x) hQ]

/-- Mean-value bound for the real part of `Ψ̃` on a real segment (copy of `psiTilde_real_mv_sub`). -/
theorem hankelBoot_psi_mv_sub {c : ℝ} {f : ℝ → ℝ} {R_dom : ℝ}
    (hΨ_an : AnalyticOnNhd ℂ (hankelPsi c f) (closedBall (0 : ℂ) R_dom))
    {a b : ℝ} (hab : a ≤ b) (ha : -R_dom ≤ a) (hb : b ≤ R_dom) (C₁ : ℝ)
    (hder : ∀ x ∈ Icc a b, ‖deriv (hankelPsi c f) (x : ℂ)‖ ≤ C₁) :
    |(hankelPsi c f (b : ℂ)).re - (hankelPsi c f (a : ℂ)).re| ≤ C₁ * (b - a) := by
  have hΨ_diff : ∀ t ∈ Icc a b,
      HasDerivAt (fun x : ℝ => (hankelPsi c f (x : ℂ)).re)
        ((deriv (hankelPsi c f) (t : ℂ)).re) t := by
    intro t ht
    have ht_ball : (t : ℂ) ∈ closedBall (0 : ℂ) R_dom := by
      rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hc : HasDerivAt (hankelPsi c f) (deriv (hankelPsi c f) (t : ℂ)) (t : ℂ) :=
      (hΨ_an (t : ℂ) ht_ball).differentiableAt.hasDerivAt
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hc.comp_ofReal
  have hcont_der : ContinuousOn (fun t : ℝ => (deriv (hankelPsi c f) (t : ℂ)).re) (Icc a b) := by
    refine Complex.continuous_re.comp_continuousOn ?_
    refine hΨ_an.deriv.continuousOn.comp continuous_ofReal.continuousOn fun t ht => ?_
    rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hftc : (hankelPsi c f (b : ℂ)).re - (hankelPsi c f (a : ℂ)).re =
      ∫ t in a..b, (deriv (hankelPsi c f) (t : ℂ)).re :=
    (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hΨ_diff t (Set.uIcc_of_le hab ▸ ht))
      (hcont_der.intervalIntegrable_of_Icc hab)).symm
  have h_norm := intervalIntegral.norm_integral_le_integral_norm
    (f := fun t : ℝ => (deriv (hankelPsi c f) (t : ℂ)).re) (μ := volume) hab
  rw [← hftc, Real.norm_eq_abs] at h_norm
  have hint_bd : ∫ t in a..b, ‖(deriv (hankelPsi c f) (t : ℂ)).re‖ ≤ ∫ _ in a..b, C₁ := by
    refine intervalIntegral.integral_mono_on hab
      ((continuous_norm.comp_continuousOn hcont_der).intervalIntegrable_of_Icc hab)
      (intervalIntegrable_const) fun t ht => ?_
    rw [Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm _).trans (hder t ht)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hint_bd
  have hle : |(hankelPsi c f (b : ℂ)).re - (hankelPsi c f (a : ℂ)).re| ≤ (b - a) * C₁ :=
    h_norm.trans hint_bd
  linarith [hle]

/-- The shifted test at a real point: its real part is the real weight times `Re Ψ̃(x + ℓ)`. -/
theorem hankelBoot_shifted_re (c : ℝ) (f : ℝ → ℝ) (R ℓ : ℝ) (k : ℕ) (x : ℝ) :
    (hankelBootShifted c f R ℓ k (x : ℂ)).re = (1 + x / R) ^ (k + 1) * hankelPsiR c f (x + ℓ) := by
  unfold hankelBootShifted hankelPsiR
  have h1 : (1 + (x : ℂ) / (R : ℂ)) ^ (k + 1) = (((1 + x / R) ^ (k + 1) : ℝ) : ℂ) := by
    push_cast; ring
  have h2 : (x : ℂ) + (ℓ : ℂ) = ((x + ℓ : ℝ) : ℂ) := by push_cast; ring
  rw [h1, h2, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  ring

/-- The real node weight `(1 + x/R)^{k+1}` lies in `[0,1]` for `-R ≤ x ≤ 0`. -/
theorem hankelBoot_weight_bounds {R x : ℝ} (hR : 0 < R) (hx1 : -R ≤ x) (hx2 : x ≤ 0) (k : ℕ) :
    0 ≤ (1 + x / R) ^ (k + 1) ∧ (1 + x / R) ^ (k + 1) ≤ 1 := by
  have hdiv1 : -1 ≤ x / R := by rw [le_div_iff₀ hR]; linarith
  have hdiv2 : x / R ≤ 0 := div_nonpos_of_nonpos_of_nonneg hx2 hR.le
  have hb0 : 0 ≤ 1 + x / R := by linarith
  have hb1 : 1 + x / R ≤ 1 := by linarith
  exact ⟨pow_nonneg hb0 _, pow_le_one₀ hb0 hb1⟩

/-- At `k = 9` and `R ≥ 48`, `x ≥ -2.35` gives the weight `(1 + x/R)^{10} ≥ 1/2`. -/
theorem hankelBoot_weight_ge_half {R x : ℝ} (hR : 48 ≤ R) (hx : -2.35 ≤ x) :
    (1 / 2 : ℝ) ≤ (1 + x / R) ^ (9 + 1) := by
  have hR0 : 0 < R := by linarith
  have hdiv : -2.35 / 48 ≤ x / R := by
    calc (-2.35 / 48 : ℝ) ≤ -2.35 / R := by
          rw [neg_div, neg_div, neg_le_neg_iff]
          exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hR
      _ ≤ x / R := div_le_div_of_nonneg_right hx hR0.le
  have h1 : (1 - 2.35 / 48 : ℝ) ≤ 1 + x / R := by linarith
  have h2 : (1 / 2 : ℝ) ≤ (1 - 2.35 / 48 : ℝ) ^ (9 + 1) := by norm_num
  exact h2.trans (pow_le_pow_left₀ (by norm_num) h1 _)

/-- The Hankel sign bound `-r_∞ ≤ Re Ψ̃(x)` on the Langer disc to the right of `u_T`. -/
theorem hankelBoot_sign_of_le {c ε T u_T R : ℝ} {f : ℝ → ℝ} (hc : 3e6 ≤ c)
    (hf : IsHankelFeasible c ε T f) (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1)
    (hT : c * hankelXi c u_T = T) (hu0 : u_T ≤ 0) (hu3 : -3 ≤ u_T) (hR48 : 48 ≤ R)
    (hRA : R + 1 ≤ langerRadius c) {x : ℝ} (hx : |x| ≤ langerRadius c) (hxu : x ≤ u_T) :
    -hankelRinf c ≤ hankelPsiR c f x := by
  have hc5 : (5000 : ℝ) ≤ c := by linarith
  have hc0 : 0 < c := by linarith
  have huA : |u_T| ≤ langerRadius c := abs_le.2 ⟨by linarith, by linarith⟩
  refine hankel_psi_sign hc5 hf hε hM hx ?_
  rw [← hT]
  exact hankel_phi_anti hc0 hx huA hxu

/-- Localisation of the zero `a_n` (`n ≥ 2`) and of its shift: `|a_n + ℓ| ≤ A` and `a_n + ℓ ≤ u_T`. -/
theorem hankelBoot_node_arg {c u_T R ℓ : ℝ} (hu0 : u_T ≤ 0) (hu3 : -3 ≤ u_T) (hR48 : 48 ≤ R)
    (hRA : R + 1 ≤ langerRadius c) (hℓ0 : 0 ≤ ℓ) (hℓ : ℓ ≤ 1 / 2) {n : ℕ} (hn : 2 ≤ n)
    (hnR : -R < airyZero n) :
    |airyZero n + ℓ| ≤ langerRadius c ∧ airyZero n + ℓ ≤ u_T := by
  have h2 : airyZero n ≤ airyZero 2 := airyZero_anti (by norm_num) hn
  have h2' : airyZero 2 < -4 := airyZero_two.2
  have hu : airyZero n + ℓ ≤ u_T := by linarith
  exact ⟨abs_le.2 ⟨by linarith, by linarith⟩, hu⟩

/-- Per-node lower bound for `n ≥ 2` with `-R < a_n`: the node term is at least `-(6π)² r_∞`. -/
theorem hankelBoot_node_lb {c ε T u_T R ℓ : ℝ} {f : ℝ → ℝ} (hc : 3e6 ≤ c)
    (hf : IsHankelFeasible c ε T f) (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1)
    (hT : c * hankelXi c u_T = T) (hu0 : u_T ≤ 0) (hu3 : -3 ≤ u_T) (hR48 : 48 ≤ R)
    (hRA : R + 1 ≤ langerRadius c) (hℓ0 : 0 ≤ ℓ) (hℓ : ℓ ≤ 1 / 2) (k : ℕ) {n : ℕ} (hn : 2 ≤ n)
    (hnR : -R < airyZero n) :
    -((6 * π) ^ 2 * hankelRinf c) ≤
      (hankelBootShifted c f R ℓ k (airyZero n : ℂ)).re / airyAi' (airyZero n) ^ 2 := by
  have hr := hankelRinf_nonneg (by linarith : (5000 : ℝ) ≤ c) hf.toIsHankelEigenfn hε hM
  obtain ⟨hA, hu⟩ := hankelBoot_node_arg hu0 hu3 hR48 hRA hℓ0 hℓ hn hnR
  have hP := hankelBoot_sign_of_le hc hf hε hM hT hu0 hu3 hR48 hRA hA hu
  have hX := hankelBoot_weight_bounds (by linarith : (0 : ℝ) < R) hnR.le (airyZero_neg n).le k
  have hI0 : 0 ≤ (airyAi' (airyZero n) ^ 2)⁻¹ := inv_nonneg.2 (sq_nonneg _)
  have hI1 : (airyAi' (airyZero n) ^ 2)⁻¹ ≤ (6 * π) ^ 2 := hankelBoot_airyAi'_sq_inv_le n
  rw [hankelBoot_shifted_re, div_eq_mul_inv]
  have hXP := hankelBoot_mul_ge hX.1 hX.2 hr hP
  have h1 := mul_le_mul_of_nonneg_right hXP hI0
  have h2 := mul_le_mul_of_nonneg_left hI1 hr
  linarith

/-- Splitting off the `n = 1` term of the node sum. -/
theorem hankelBoot_nodes_split (c : ℝ) (f : ℝ → ℝ) (R ℓ : ℝ) (k N : ℕ) (h1N : 1 ≤ N) :
    hankelBootNodes c f R ℓ k N =
      (hankelBootShifted c f R ℓ k (airyZero 1 : ℂ)).re / airyAi' (airyZero 1) ^ 2 +
        ∑ n ∈ (Finset.Icc 1 N).erase 1,
          (hankelBootShifted c f R ℓ k (airyZero n : ℂ)).re / airyAi' (airyZero n) ^ 2 := by
  have h1_mem : (1 : ℕ) ∈ Finset.Icc 1 N := Finset.mem_Icc.2 ⟨le_rfl, h1N⟩
  unfold hankelBootNodes
  exact (Finset.add_sum_erase (Finset.Icc 1 N)
    (fun n : ℕ => (hankelBootShifted c f R ℓ k (airyZero n : ℂ)).re / airyAi' (airyZero n) ^ 2)
    h1_mem).symm

/-- Lower bound for the lost node terms `n ∈ (Icc 1 N).erase 1`: at least `-N (6π)² r_∞`. -/
theorem hankelBoot_tail_lb {c ε T u_T R ℓ : ℝ} {N : ℕ} {f : ℝ → ℝ} (hc : 3e6 ≤ c)
    (hf : IsHankelFeasible c ε T f) (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1)
    (hT : c * hankelXi c u_T = T) (hu0 : u_T ≤ 0) (hu3 : -3 ≤ u_T) (hR48 : 48 ≤ R)
    (hRA : R + 1 ≤ langerRadius c) (hN : ∀ n : ℕ, 1 ≤ n → (n ≤ N ↔ -airyZero n < R))
    (hℓ0 : 0 ≤ ℓ) (hℓ : ℓ ≤ 1 / 2) (k : ℕ) :
    -((N : ℝ) * ((6 * π) ^ 2 * hankelRinf c)) ≤
      ∑ n ∈ (Finset.Icc 1 N).erase 1,
        (hankelBootShifted c f R ℓ k (airyZero n : ℂ)).re / airyAi' (airyZero n) ^ 2 := by
  have hr := hankelRinf_nonneg (by linarith : (5000 : ℝ) ≤ c) hf.toIsHankelEigenfn hε hM
  have hcard : (((Finset.Icc 1 N).erase 1).card : ℝ) ≤ N := by
    have h : ((Finset.Icc 1 N).erase 1).card ≤ N := by
      refine Finset.card_erase_le.trans ?_
      simp
    exact_mod_cast h
  have hX : 0 ≤ (6 * π) ^ 2 * hankelRinf c := mul_nonneg (sq_nonneg _) hr
  have hlow := Finset.card_nsmul_le_sum ((Finset.Icc 1 N).erase 1)
    (fun n : ℕ => (hankelBootShifted c f R ℓ k (airyZero n : ℂ)).re / airyAi' (airyZero n) ^ 2)
    (-((6 * π) ^ 2 * hankelRinf c))
    (fun n hn => by
      rw [Finset.mem_erase, Finset.mem_Icc] at hn
      obtain ⟨hne, hn1, hnN⟩ := hn
      have hn2 : 2 ≤ n := by omega
      have hnR : -R < airyZero n := by linarith [(hN n hn1).mp hnN]
      exact hankelBoot_node_lb hc hf hε hM hT hu0 hu3 hR48 hRA hℓ0 hℓ k hn2 hnR)
  rw [nsmul_eq_mul] at hlow
  have hmul := mul_le_mul_of_nonneg_right hcard hX
  linarith

/-- The `n = 1` term of the node sum, in the form used by the bounds. -/
theorem hankelBoot_term1_eq (c : ℝ) (f : ℝ → ℝ) (R ℓ : ℝ) (k : ℕ) :
    (hankelBootShifted c f R ℓ k (airyZero 1 : ℂ)).re / airyAi' (airyZero 1) ^ 2 =
      (1 + airyZero 1 / R) ^ (k + 1) * hankelPsiR c f (airyZero 1 + ℓ) / quantC1WStar := by
  rw [hankelBoot_shifted_re]
  unfold quantC1WStar
  ring

/-- The `n = 1` term of the node sum with the inverse weight `1/w_*` written as a factor. -/
theorem hankelBoot_term1_eq' (c : ℝ) (f : ℝ → ℝ) (R ℓ : ℝ) (k : ℕ) :
    (hankelBootShifted c f R ℓ k (airyZero 1 : ℂ)).re / airyAi' (airyZero 1) ^ 2 =
      (1 + airyZero 1 / R) ^ (k + 1) * hankelPsiR c f (airyZero 1 + ℓ) * (1 / quantC1WStar) := by
  rw [hankelBoot_term1_eq]
  ring

/-- Lower bound at `a_1 + ℓ`: `Re Ψ̃(a_1 + ℓ) ≥ -r_∞ - C₁ ℓ` (mean value on `[a_1, a_1 + ℓ]`). -/
theorem hankelBoot_node1_re_lb {c ε T u_T R : ℝ} {f : ℝ → ℝ} (hc : 3e6 ≤ c)
    (hf : IsHankelFeasible c ε T f) (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1)
    (hT : c * hankelXi c u_T = T) (ha1 : airyZero 1 < u_T)
    (hB2 : QuantC1B2Holds (hankelPsi c f) u_T) (hu0 : u_T ≤ 0) (hu3 : -3 ≤ u_T)
    (hR48 : 48 ≤ R) (hRA : R + 1 ≤ langerRadius c) {ℓ : ℝ} (hℓ0 : 0 ≤ ℓ)
    (hℓ : ℓ ≤ quantC1DeltaStar) :
    -hankelRinf c - quantC1C1 * ℓ ≤ hankelPsiR c f (airyZero 1 + ℓ) := by
  have hc0 : 0 < c := by linarith
  have hfe := hf.toIsHankelEigenfn
  have hAn : AnalyticOnNhd ℂ (hankelPsi c f) (closedBall (0 : ℂ) (langerRadius c)) :=
    analyticOnNhd_hankelPsi hc0 hfe
  have ha1_bd : |airyZero 1| ≤ 3 := abs_le.2 ⟨by linarith [airyZero_one.1], by linarith [airyZero_one.2]⟩
  have hA1 : |airyZero 1| ≤ langerRadius c := by linarith
  have hp1 : -hankelRinf c ≤ hankelPsiR c f (airyZero 1) :=
    hankelBoot_sign_of_le hc hf hε hM hT hu0 hu3 hR48 hRA hA1 ha1.le
  have hδpos := quantC1DeltaStar_pos
  have hδ := quantC1DeltaStar_le
  have hder : ∀ x ∈ Icc (airyZero 1) (airyZero 1 + ℓ), ‖deriv (hankelPsi c f) (x : ℂ)‖ ≤ quantC1C1 :=
    fun x hx => (hB2.2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩).1
  have hmv := hankelBoot_psi_mv_sub hAn (a := airyZero 1) (b := airyZero 1 + ℓ) (by linarith)
    (by linarith [(abs_le.1 hA1).1]) (by linarith [(abs_le.1 hA1).2, airyZero_one.2]) quantC1C1 hder
  obtain ⟨hlo, _⟩ := abs_le.1 hmv
  show -hankelRinf c - quantC1C1 * ℓ ≤ (hankelPsi c f ((airyZero 1 + ℓ : ℝ) : ℂ)).re
  have hp1' : -hankelRinf c ≤ (hankelPsi c f (airyZero 1 : ℂ)).re := hp1
  linarith

/-- **Auxiliary lower bound** (node sum, `n = 1` term kept, `n ≥ 2` terms lost). -/
theorem hankelBoot_nodes_aux {c ε T u_T R : ℝ} {N : ℕ} {f : ℝ → ℝ} (hc : 3e6 ≤ c)
    (hf : IsHankelFeasible c ε T f) (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1)
    (hT : c * hankelXi c u_T = T) (ha1 : airyZero 1 < u_T)
    (hB2 : QuantC1B2Holds (hankelPsi c f) u_T) (hu0 : u_T ≤ 0) (hu3 : -3 ≤ u_T)
    (hR48 : 48 ≤ R) (hRA : R + 1 ≤ langerRadius c)
    (hN : ∀ n : ℕ, 1 ≤ n → (n ≤ N ↔ -airyZero n < R))
    {ℓ : ℝ} (hℓ0 : 0 ≤ ℓ) (hℓ : ℓ ≤ min quantC1DeltaStar (min quantC1Eta0 1))
    {k : ℕ} (hkR : (k : ℝ) ≤ R / 5) :
    (1 + airyZero 1 / R) ^ (k + 1) * hankelPsiR c f (airyZero 1 + ℓ) / quantC1WStar -
        (6 * π) ^ 2 * (N : ℝ) * hankelRinf c
      ≤ hankelBootNodes c f R ℓ k N := by
  have hℓ_half : ℓ ≤ 1 / 2 := hℓ.trans ((min_le_left _ _).trans quantC1DeltaStar_le)
  have h1N : 1 ≤ N := (hN 1 le_rfl).mpr (by linarith [airyZero_one.1])
  have hsplit := hankelBoot_nodes_split c f R ℓ k N h1N
  have htail := hankelBoot_tail_lb hc hf hε hM hT hu0 hu3 hR48 hRA hN hℓ0 hℓ_half k
  rw [hankelBoot_term1_eq] at hsplit
  linarith

/-- **Slope bound** (`hP_nodes_lb_hb`): the node sum is bounded below by the linear-in-`ℓ` term. -/
theorem hankelBoot_nodes_lb {c ε T u_T R : ℝ} {N : ℕ} {f : ℝ → ℝ} (hc : 3e6 ≤ c)
    (hf : IsHankelFeasible c ε T f) (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1)
    (hT : c * hankelXi c u_T = T) (ha1 : airyZero 1 < u_T)
    (hB2 : QuantC1B2Holds (hankelPsi c f) u_T) (hu0 : u_T ≤ 0) (hu3 : -3 ≤ u_T)
    (hR48 : 48 ≤ R) (hRA : R + 1 ≤ langerRadius c)
    (hN : ∀ n : ℕ, 1 ≤ n → (n ≤ N ↔ -airyZero n < R))
    {ℓ : ℝ} (hℓ0 : 0 ≤ ℓ) (hℓ : ℓ ≤ min quantC1DeltaStar (min quantC1Eta0 1))
    {k : ℕ} (hkR : (k : ℝ) ≤ R / 5) :
    -(2 * quantC1C1 * (1 / quantC1WStar)) * ℓ - (6 * π) ^ 2 * ((N : ℝ) + 1) * hankelRinf c
      ≤ hankelBootNodes c f R ℓ k N := by
  have hℓ_half : ℓ ≤ 1 / 2 := hℓ.trans ((min_le_left _ _).trans quantC1DeltaStar_le)
  have hδ : ℓ ≤ quantC1DeltaStar := hℓ.trans (min_le_left _ _)
  have h1N : 1 ≤ N := (hN 1 le_rfl).mpr (by linarith [airyZero_one.1])
  have hsplit := hankelBoot_nodes_split c f R ℓ k N h1N
  have htail := hankelBoot_tail_lb hc hf hε hM hT hu0 hu3 hR48 hRA hN hℓ0 hℓ_half k
  have hr := hankelRinf_nonneg (by linarith : (5000 : ℝ) ≤ c) hf.toIsHankelEigenfn hε hM
  have hnode1 := hankelBoot_node1_re_lb hc hf hε hM hT ha1 hB2 hu0 hu3 hR48 hRA hℓ0 hδ
  have hw := hankelBoot_weight_bounds (by linarith : (0 : ℝ) < R)
    (by linarith [airyZero_one.1]) (airyZero_neg 1).le k
  have hxP := hankelBoot_mul_ge hw.1 hw.2 (by
      have := quantC1C1_pos; have := hℓ0; positivity)
    (by linarith [hnode1] : -(hankelRinf c + quantC1C1 * ℓ) ≤ hankelPsiR c f (airyZero 1 + ℓ))
  have hI1 : (airyAi' (airyZero 1) ^ 2)⁻¹ = 1 / quantC1WStar := by
    unfold quantC1WStar; rw [one_div]
  have hI1n : 0 ≤ (airyAi' (airyZero 1) ^ 2)⁻¹ := inv_nonneg.2 (sq_nonneg _)
  have hI1le : (airyAi' (airyZero 1) ^ 2)⁻¹ ≤ (6 * π) ^ 2 := hankelBoot_airyAi'_sq_inv_le 1
  have ha := mul_le_mul_of_nonneg_right hxP hI1n
  have hb := mul_le_mul_of_nonneg_left hI1le hr
  rw [hI1] at ha hb
  have hterm1 := hankelBoot_term1_eq' c f R ℓ k
  have hc' : 0 ≤ quantC1C1 * ℓ * (1 / quantC1WStar) :=
    mul_nonneg (mul_nonneg quantC1C1_pos.le hℓ0) (one_div_nonneg.2 quantC1WStar_pos.le)
  linarith

/-- **Theta bound** (`P_theta_bound`): the node sum at the `θ`-shift and weight index `k = 9`. -/
theorem hankelBoot_nodes_theta {c ε T u_T R : ℝ} {N : ℕ} {f : ℝ → ℝ} (hc : 3e6 ≤ c)
    (hf : IsHankelFeasible c ε T f) (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1)
    (hT : c * hankelXi c u_T = T) (ha1 : airyZero 1 < u_T)
    (hB2 : QuantC1B2Holds (hankelPsi c f) u_T) (hu0 : u_T ≤ 0) (hu3 : -3 ≤ u_T)
    (hR48 : 48 ≤ R) (hRA : R + 1 ≤ langerRadius c)
    (hN : ∀ n : ℕ, 1 ≤ n → (n ≤ N ↔ -airyZero n < R))
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 2)
    (hℓ0 : 0 ≤ θ * (u_T - airyZero 1))
    (hℓ : θ * (u_T - airyZero 1) ≤ min quantC1DeltaStar (min quantC1Eta0 1)) :
    (quantC1KappaStar / (4 * quantC1WStar)) * (u_T - airyZero 1) -
        (6 * π) ^ 2 * ((N : ℝ) + 1) * hankelRinf c
      ≤ hankelBootNodes c f R (θ * (u_T - airyZero 1)) 9 N := by
  obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ : ℝ, ℓ = θ * (u_T - airyZero 1) := ⟨_, rfl⟩
  rw [← hℓdef] at hℓ0 hℓ ⊢
  have hℓ_half : ℓ ≤ 1 / 2 := hℓ.trans ((min_le_left _ _).trans quantC1DeltaStar_le)
  have hc0 : 0 < c := by linarith
  have hfe := hf.toIsHankelEigenfn
  have hr := hankelRinf_nonneg (by linarith : (5000 : ℝ) ≤ c) hfe hε hM
  have hA49 : (49 : ℝ) ≤ langerRadius c := by linarith
  have hAn : AnalyticOnNhd ℂ (hankelPsi c f) (closedBall (0 : ℂ) (langerRadius c)) :=
    analyticOnNhd_hankelPsi hc0 hfe
  have hΨan : AnalyticOnNhd ℂ (fun z => hankelPsi c f z + (hankelRinf c : ℂ))
      (closedBall (0 : ℂ) (langerRadius c)) :=
    fun z hz => (hAn z hz).add analyticAt_const
  have ha1_bd : |airyZero 1| ≤ 3 := abs_le.2 ⟨by linarith [airyZero_one.1], by linarith [airyZero_one.2]⟩
  have huA : |u_T| ≤ langerRadius c := abs_le.2 ⟨by linarith, by linarith⟩
  have hu_nn : 0 ≤ u_T - airyZero 1 := by linarith
  have hpos : 0 ≤ ((fun z => hankelPsi c f z + (hankelRinf c : ℂ)) (u_T : ℂ)).re := by
    have := hankelBoot_sign_of_le hc hf hε hM hT hu0 hu3 hR48 hRA huA le_rfl
    show 0 ≤ (hankelPsi c f (u_T : ℂ) + (hankelRinf c : ℂ)).re
    rw [Complex.add_re, Complex.ofReal_re]
    unfold hankelPsiR at this
    linarith
  have hd : ∀ x : ℂ, deriv (fun z => hankelPsi c f z + (hankelRinf c : ℂ)) x =
      deriv (hankelPsi c f) x := fun x => deriv_add_const _
  have hB2' : QuantC1B2Holds (fun z => hankelPsi c f z + (hankelRinf c : ℂ)) u_T := by
    unfold QuantC1B2Holds at hB2 ⊢
    refine ⟨hB2.1, fun x hx => ?_⟩
    rw [hd]
    exact hB2.2 x hx
  have hR_dom : |airyZero 1| + 1 ≤ langerRadius c := by linarith
  have hsec := quantC1B2_secant_lower (Ψ := fun z => hankelPsi c f z + (hankelRinf c : ℂ))
    (u_T := u_T) (R_dom := langerRadius c) hR_dom hΨan ha1 hpos hB2' hθ0.le
    (by linarith : θ ≤ 1)
  rw [← hℓdef] at hsec
  simp only [Complex.add_re, Complex.ofReal_re] at hsec
  have hPM : quantC1KappaStar * (u_T - airyZero 1) - hankelRinf c ≤
      hankelPsiR c f (airyZero 1 + ℓ) := by
    unfold hankelPsiR
    nlinarith [mul_nonneg (mul_nonneg quantC1KappaStar_pos.le hu_nn) (by linarith : (0 : ℝ) ≤ 1 - 2 * θ)]
  have hw_half := hankelBoot_weight_ge_half hR48 airyZero_one.1.le
  have hw := hankelBoot_weight_bounds (by linarith : (0 : ℝ) < R)
    (by linarith [airyZero_one.1]) (airyZero_neg 1).le 9
  have hA' := mul_le_mul_of_nonneg_left hPM hw.1
  have hB' : (1 / 2 : ℝ) * (quantC1KappaStar * (u_T - airyZero 1)) - hankelRinf c ≤
      (1 + airyZero 1 / R) ^ (9 + 1) *
        (quantC1KappaStar * (u_T - airyZero 1) - hankelRinf c) := by
    nlinarith [mul_nonneg (by linarith [hw_half] : (0 : ℝ) ≤ (1 + airyZero 1 / R) ^ (9 + 1) - 1 / 2)
        (mul_nonneg quantC1KappaStar_pos.le hu_nn),
      mul_nonneg (by linarith [hw.2] : (0 : ℝ) ≤ 1 - (1 + airyZero 1 / R) ^ (9 + 1)) hr]
  have hI1 : (airyAi' (airyZero 1) ^ 2)⁻¹ = 1 / quantC1WStar := by
    unfold quantC1WStar; rw [one_div]
  have hI1n : 0 ≤ 1 / quantC1WStar := one_div_nonneg.2 quantC1WStar_pos.le
  have hI1le : (airyAi' (airyZero 1) ^ 2)⁻¹ ≤ (6 * π) ^ 2 := hankelBoot_airyAi'_sq_inv_le 1
  rw [hI1] at hI1le
  have hterm_lb := mul_le_mul_of_nonneg_right (hB'.trans hA') hI1n
  have hb := mul_le_mul_of_nonneg_left hI1le hr
  have hE : 0 ≤ quantC1KappaStar * (1 / quantC1WStar) * (u_T - airyZero 1) :=
    mul_nonneg (mul_nonneg quantC1KappaStar_pos.le hI1n) hu_nn
  have hq : quantC1KappaStar / (4 * quantC1WStar) =
      1 / 4 * (quantC1KappaStar * (1 / quantC1WStar)) := by ring
  have h1N : 1 ≤ N := (hN 1 le_rfl).mpr (by linarith [airyZero_one.1])
  have hsplit := hankelBoot_nodes_split c f R ℓ 9 N h1N
  have htail := hankelBoot_tail_lb hc hf hε hM hT hu0 hu3 hR48 hRA hN hℓ0 hℓ_half 9
  rw [hankelBoot_term1_eq'] at hsplit
  rw [hq]
  linarith

/-- info: 'FormalResearch.SignUncertainty.hankelBoot_airyAi'_sq_inv_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBoot_airyAi'_sq_inv_le

/-- info: 'FormalResearch.SignUncertainty.hankelBoot_mul_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBoot_mul_ge

/-- info: 'FormalResearch.SignUncertainty.hankelBoot_psi_mv_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBoot_psi_mv_sub

/-- info: 'FormalResearch.SignUncertainty.hankelBoot_shifted_re' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBoot_shifted_re

/-- info: 'FormalResearch.SignUncertainty.hankelBoot_weight_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBoot_weight_bounds

/-- info: 'FormalResearch.SignUncertainty.hankelBoot_weight_ge_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBoot_weight_ge_half

/-- info: 'FormalResearch.SignUncertainty.hankelBoot_sign_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBoot_sign_of_le

/-- info: 'FormalResearch.SignUncertainty.hankelBoot_node_arg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBoot_node_arg

/-- info: 'FormalResearch.SignUncertainty.hankelBoot_node_lb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBoot_node_lb

/-- info: 'FormalResearch.SignUncertainty.hankelBoot_nodes_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBoot_nodes_split

/-- info: 'FormalResearch.SignUncertainty.hankelBoot_tail_lb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBoot_tail_lb

/-- info: 'FormalResearch.SignUncertainty.hankelBoot_term1_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBoot_term1_eq

/-- info: 'FormalResearch.SignUncertainty.hankelBoot_term1_eq'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBoot_term1_eq'

/-- info: 'FormalResearch.SignUncertainty.hankelBoot_node1_re_lb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBoot_node1_re_lb

/-- info: 'FormalResearch.SignUncertainty.hankelBoot_nodes_aux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBoot_nodes_aux

/-- info: 'FormalResearch.SignUncertainty.hankelBoot_nodes_lb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBoot_nodes_lb

/-- info: 'FormalResearch.SignUncertainty.hankelBoot_nodes_theta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBoot_nodes_theta

end FormalResearch.SignUncertainty

end
