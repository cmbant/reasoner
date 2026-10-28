import FormalResearch.FourQubitEntropy.SevenQubitLinearPurity

/-!
# `cor:seven-entropy-eigen-cap-497` (conditional): `λ_max < 497/1000` on every three-qubit cut

Formalizes the corollary of `seven_qubit_entropy_compatibility.tex` (SP7-6) in three layers.
Entropies are in nats (as in `SevenQubitConseq*`); the paper's bits statements are these divided by
`ln 2`.

1. **Spectrum-level core (proved, no hypotheses).**  `eigenCap_core`: for an eight-point spectrum
   `μ` sorted descending (`Antitone μ`), nonnegative, summing to `1`, with `μ 0 ≥ 497/1000`,
   `(4851/4000) ln 2 < 3 ln 2 - S(μ) + (32/5) ln 2 · v(μ)`, where `S = ∑ -μ ln μ` and
   `v(μ) = ∑_{i<4} (μ_i + μ_{7-i})² - 1/4` (`vSpec`).  This is the `J(t,a)` argument: concavity
   bounds `S` by the `(t, a, b^6)` spike entropy (`t = μ 0`, `a = μ 7`, `b = (1-t-a)/6`),
   Cauchy-Schwarz bounds `v ≥ (4/3)(t+a-1/4)²`, `J(·,a)` increases in `t` (tangent inequality of
   `x ln x`), and at `t = 497/1000` strong convexity in `a` about `a₀ = 17/4000` gives a value
   `> 4851/4000` (rational `arctanh` enclosures of `ln 2`, `ln(500/497)`, `ln(136/125)`,
   `ln(133/100)`).
2. **Aggregation (hypothesis).**  `eigenCap_of_aggregate`: if the linear aggregation inequality
   `3 ln 2 - S(μ) + (32/5) ln 2 · v(μ) ≤ 35 (3 ln 2 - E₃)` holds and `E₃ > (59307/20000) ln 2`
   (the SC-2 lower witness `E₃(ψ_{7/100}) > 59307/20000`, **assumed, not proved**), then `μ 0 < 497/1000`.
3. **States.**  `cut_aggregate` derives the aggregation inequality from the per-cut
   spin-flip cross-cut inequality `e_S + 16 v(μ_S) ≤ R` (`SpinFlipCrossCut`, an explicit `Prop`
   hypothesis, to be supplied by the `SevenQubitSpectralPair*` development) and
   `lem:seven-entropy-linear-purity` on the other 34 cuts.  `eigenCap_497` is the corollary for
   a unit vector `ψ`: `E₃(ψ) > (59307/20000) ln 2` and `SpinFlipCrossCut ψ` imply every eigenvalue of every
   three-qubit marginal is `< 497/1000`.
-/

open Real Finset

namespace FormalResearch.FourQubitEntropy.SevenQubitConseq

open FormalResearch.FourQubitEntropy.SevenQubitIco

namespace EigCap

open LinPur

/-- `v(μ)` of the spin-flip pairing for a descending eight-point spectrum:
`∑_{i<4} (μ_i + μ_{7-i})² - 1/4`. -/
noncomputable def vSpec (μ : Fin 8 → ℝ) : ℝ :=
  (μ 0 + μ 7) ^ 2 + (μ 1 + μ 6) ^ 2 + (μ 2 + μ 5) ^ 2 + (μ 3 + μ 4) ^ 2 - 1 / 4

/-- `Φ(t,a) = 3 ln 2 + (t ln t + a ln a + 6 b ln b) + (128/15) ln 2 (t+a-1/4)²`, `b = (1-t-a)/6`:
`ln 2` times the paper's `J(t,a)` (in nats). -/
noncomputable def Phi (t a : ℝ) : ℝ :=
  3 * log 2 + (t * log t + a * log a + 6 * (((1 - t - a) / 6) * log ((1 - t - a) / 6))) +
    (128 / 15) * log 2 * (t + a - 1 / 4) ^ 2

/-- `Φ(·, a)` is increasing on `t ≥ 497/1000` (`∂_tΦ > 0`), via the tangent inequality of `x ln x`. -/
theorem Phi_mono {t a : ℝ} (ht : 497 / 1000 ≤ t) (ha0 : 0 ≤ a) (ha : 7 * a ≤ 1 - t) :
    Phi (497 / 1000) a ≤ Phi t a := by
  have l2 : 0 < log 2 := Real.log_pos (by norm_num)
  have hK : 0 ≤ (128 / 15) * log 2 := by positivity
  have hb' : 0 < (1 - 497 / 1000 - a) / 6 := by linarith
  have hb : 0 ≤ (1 - t - a) / 6 := by linarith
  have h1 := xlogx_tangent (x := t) (y := 497 / 1000) (by linarith) (by norm_num)
  have h2 := xlogx_tangent (x := (1 - t - a) / 6) (y := (1 - 497 / 1000 - a) / 6) hb hb'
  have hlog : log ((1 - 497 / 1000 - a) / 6) ≤ log (497 / 1000) :=
    Real.log_le_log hb' (by linarith)
  have p1 := mul_nonneg (sub_nonneg.2 hlog) (sub_nonneg.2 ht)
  have p2 := mul_nonneg hK (mul_nonneg (by linarith : (0 : ℝ) ≤ 497 / 1000 + a - 1 / 4)
    (sub_nonneg.2 ht))
  have p3 := mul_nonneg hK (sq_nonneg (t - 497 / 1000))
  unfold Phi
  nlinarith [h1, h2, p1, p2, p3]

/-- The `a`-direction: strong convexity about `a₀ = 17/4000` at `t₀ = 497/1000`. -/
theorem Phi_t0_lower {a : ℝ} (ha0 : 0 ≤ a) (ha : 7 * a ≤ 1 - 497 / 1000) :
    Phi (497 / 1000) (17 / 4000) +
      ((log (17 / 4000) - log (133 / 1600) + 2 * ((128 / 15) * log 2) * (497 / 1000 + 17 / 4000 - 1 / 4)) *
          (a - 17 / 4000) + (128 / 15) * log 2 * (a - 17 / 4000) ^ 2) ≤ Phi (497 / 1000) a := by
  have l2 : 0 < log 2 := Real.log_pos (by norm_num)
  have hK : 0 ≤ (128 / 15) * log 2 := by positivity
  have hb : 0 ≤ (1 - 497 / 1000 - a) / 6 := by linarith
  have h1 := xlogx_tangent (x := a) (y := 17 / 4000) ha0 (by norm_num)
  have h2 := xlogx_tangent (x := (1 - 497 / 1000 - a) / 6) (y := 133 / 1600) hb (by norm_num)
  have hb0 : (1 - 497 / 1000 - 17 / 4000 : ℝ) / 6 = 133 / 1600 := by norm_num
  unfold Phi
  rw [hb0]
  nlinarith [h1, h2]

/-- Numerical core: `Φ(497/1000, 17/4000) > (4851/4000) ln 2 + 1/200000`, and `|D| ≤ 1/100`. -/
theorem Phi_t0_a0_numerics :
    (4851 / 4000) * log 2 + 1 / 200000 < Phi (497 / 1000) (17 / 4000) ∧
    |log (17 / 4000) - log (133 / 1600) + 2 * ((128 / 15) * log 2) * (497 / 1000 + 17 / 4000 - 1 / 4)|
      ≤ 1 / 100 := by
  have l2 := log2_lo; have l2' := log2_hi
  have eP : log (497 / 1000) = -log (500 / 497) - log 2 := by
    rw [show (497 / 1000 : ℝ) = (500 / 497 * 2)⁻¹ by norm_num, Real.log_inv,
      Real.log_mul (by norm_num) (by norm_num)]; ring
  have eQ : log (17 / 4000) = log (136 / 125) - 8 * log 2 := by
    rw [show (17 / 4000 : ℝ) = 136 / 125 / 2 ^ 8 by norm_num, Real.log_div (by norm_num) (by norm_num),
      Real.log_pow]; norm_num
  have eR : log (133 / 1600) = log (133 / 100) - 4 * log 2 := by
    rw [show (133 / 1600 : ℝ) = 133 / 100 / 2 ^ 4 by norm_num, Real.log_div (by norm_num) (by norm_num),
      Real.log_pow]; norm_num
  have P1 := log_ge_lo (x := 500 / 497) (by norm_num)
  have P2 := log_ge_hi (x := 500 / 497) (by norm_num)
  have Q1 := log_ge_lo (x := 136 / 125) (by norm_num)
  have Q2 := log_ge_hi (x := 136 / 125) (by norm_num)
  have R1 := log_ge_lo (x := 133 / 100) (by norm_num)
  have R2 := log_ge_hi (x := 133 / 100) (by norm_num)
  norm_num at P1 P2 Q1 Q2 R1 R2
  have hb0 : (1 - 497 / 1000 - 17 / 4000 : ℝ) / 6 = 133 / 1600 := by norm_num
  constructor
  · unfold Phi
    rw [hb0, eP, eQ, eR]
    nlinarith [P1, P2, Q1, Q2, R1, R2]
  · rw [eQ, eR, abs_le]
    constructor <;> nlinarith [P1, P2, Q1, Q2, R1, R2]

/-- **The `J(t,a)` bound.**  For `t ≥ 497/1000` and `0 ≤ a ≤ (1-t)/7`: `Φ(t,a) > (4851/4000) ln 2`. -/
theorem Phi_gt {t a : ℝ} (ht : 497 / 1000 ≤ t) (ha0 : 0 ≤ a) (ha : 7 * a ≤ 1 - t) :
    (4851 / 4000) * log 2 < Phi t a := by
  have l2 := log2_lo
  have h1 := Phi_mono ht ha0 ha
  have h2 := Phi_t0_lower ha0 (by linarith)
  obtain ⟨hN1, hN2⟩ := Phi_t0_a0_numerics
  set D := log (17 / 4000) - log (133 / 1600) +
    2 * ((128 / 15) * log 2) * (497 / 1000 + 17 / 4000 - 1 / 4) with hD
  have hD2 : D ^ 2 ≤ (1 / 100) ^ 2 := by
    have := abs_le.1 hN2
    nlinarith [this.1, this.2]
  have hKm : (5 : ℝ) ≤ (128 / 15) * log 2 := by nlinarith
  set x := a - 17 / 4000 with hx
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  have h3 : D * x + (128 / 15) * log 2 * x ^ 2 ≥ -(1 / 200000) := by
    nlinarith [sq_nonneg (x + D / 10), mul_le_mul_of_nonneg_right hKm hx2]
  linarith

/-! ### From the spectrum to `Φ` -/

/-- Cauchy-Schwarz: `v ≥ (4/3)(t + a - 1/4)²`. -/
theorem vSpec_ge {μ : Fin 8 → ℝ} (hsum : μ 0 + μ 1 + μ 2 + μ 3 + μ 4 + μ 5 + μ 6 + μ 7 = 1) :
    (4 / 3) * (μ 0 + μ 7 - 1 / 4) ^ 2 ≤ vSpec μ := by
  unfold vSpec
  nlinarith [sq_nonneg ((μ 1 + μ 6) - (μ 2 + μ 5)), sq_nonneg ((μ 1 + μ 6) - (μ 3 + μ 4)),
    sq_nonneg ((μ 2 + μ 5) - (μ 3 + μ 4))]

/-- Concavity: the entropy of a descending spectrum is at most the `(t, a, b⁶)` spike entropy. -/
theorem entropy_le_spike {μ : Fin 8 → ℝ} (h0 : ∀ i, 0 ≤ μ i)
    (hsum : μ 0 + μ 1 + μ 2 + μ 3 + μ 4 + μ 5 + μ 6 + μ 7 = 1) :
    ∑ i, negMulLog (μ i) ≤
      negMulLog (μ 0) + negMulLog (μ 7) + 6 * negMulLog ((1 - μ 0 - μ 7) / 6) := by
  have hJ := Real.concaveOn_negMulLog.le_map_sum (t := (Finset.univ : Finset (Fin 6)))
    (w := fun _ => (1 / 6 : ℝ)) (p := ![μ 1, μ 2, μ 3, μ 4, μ 5, μ 6])
    (fun _ _ => by norm_num) (by simp)
    (fun i _ => by fin_cases i <;> simp [h0])
  simp only [Fin.sum_univ_six, smul_eq_mul] at hJ
  simp at hJ
  rw [Fin.sum_univ_eight]
  have e : (6⁻¹ * μ 1 + 6⁻¹ * μ 2 + 6⁻¹ * μ 3 + 6⁻¹ * μ 4 + 6⁻¹ * μ 5 + 6⁻¹ * μ 6 : ℝ) =
      (1 - μ 0 - μ 7) / 6 := by linarith
  rw [e] at hJ
  linarith

/-- **Spectrum-level core of `cor:seven-entropy-eigen-cap-497` (proved).**  For a descending
probability spectrum on eight points with largest entry at least `497/1000`,
`(4851/4000) ln 2 < 3 ln 2 - S(μ) + (32/5) ln 2 · v(μ)`. -/
theorem eigenCap_core {μ : Fin 8 → ℝ} (hanti : Antitone μ) (h0 : ∀ i, 0 ≤ μ i)
    (hsum : ∑ i, μ i = 1) (ht : 497 / 1000 ≤ μ 0) :
    (4851 / 4000) * log 2 <
      3 * log 2 - ∑ i, negMulLog (μ i) + (32 / 5) * log 2 * vSpec μ := by
  rw [Fin.sum_univ_eight] at hsum
  have l2 : 0 < log 2 := Real.log_pos (by norm_num)
  have a1 : μ 7 ≤ μ 1 := hanti (by decide)
  have a2 : μ 7 ≤ μ 2 := hanti (by decide)
  have a3 : μ 7 ≤ μ 3 := hanti (by decide)
  have a4 : μ 7 ≤ μ 4 := hanti (by decide)
  have a5 : μ 7 ≤ μ 5 := hanti (by decide)
  have a6 : μ 7 ≤ μ 6 := hanti (by decide)
  have h7 : 7 * μ 7 ≤ 1 - μ 0 := by linarith
  have hS := entropy_le_spike h0 hsum
  have hv := vSpec_ge hsum
  have hP := Phi_gt ht (h0 7) h7
  have hmul := mul_le_mul_of_nonneg_left hv (by positivity : (0 : ℝ) ≤ (32 / 5) * log 2)
  unfold Phi at hP
  simp only [negMulLog] at hS ⊢
  nlinarith [hS, hP, hmul]

/-- **Corollary (aggregation as hypothesis).**  If `3 ln 2 - S(μ) + (32/5) ln 2 · v(μ) ≤ 35 (3 ln 2 - E)`
(the linear aggregation over the 35 cuts) and `E > (59307/20000) ln 2` (the SC-2 lower witness,
assumed), then `μ 0 < 497/1000`. -/
theorem eigenCap_of_aggregate {μ : Fin 8 → ℝ} (hanti : Antitone μ) (h0 : ∀ i, 0 ≤ μ i)
    (hsum : ∑ i, μ i = 1) {E : ℝ}
    (hagg : 3 * log 2 - ∑ i, negMulLog (μ i) + (32 / 5) * log 2 * vSpec μ ≤ 35 * (3 * log 2 - E))
    (hE : (59307 / 20000) * log 2 < E) : μ 0 < 497 / 1000 := by
  by_contra h
  have := eigenCap_core hanti h0 hsum (not_lt.1 h)
  nlinarith [this, hagg, hE]

/-! ### States -/

/-- Index equivalence `Fin 8 ≃ (Fin 3 → Bool)` used to read the eigenvalue family as a sorted list. -/
noncomputable def specEquiv : Fin 8 ≃ (Fin 3 → Bool) :=
  (finCongr card_triple.symm).trans
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin 3 → Bool))))

/-- The spectrum of the reduced state of a `3|4` cut, as a list `Fin 8 → ℝ` (descending). -/
noncomputable def sortedSpec (c : Cut 3 4) (ψ : BitString → ℂ) : Fin 8 → ℝ :=
  fun i => (redMatPsi_isHermitian c ψ).eigenvalues (specEquiv i)

theorem sortedSpec_antitone (c : Cut 3 4) (ψ : BitString → ℂ) : Antitone (sortedSpec c ψ) := by
  intro i j hij
  have h := (redMatPsi_isHermitian c ψ).eigenvalues₀_antitone
  have e : ∀ k : Fin 8, sortedSpec c ψ k =
      (redMatPsi_isHermitian c ψ).eigenvalues₀ (finCongr card_triple.symm k) := by
    intro k
    simp only [sortedSpec, Matrix.IsHermitian.eigenvalues, specEquiv, Equiv.trans_apply,
      Equiv.symm_apply_apply]
  rw [e i, e j]
  apply h
  exact hij

theorem sortedSpec_nonneg (c : Cut 3 4) (ψ : BitString → ℂ) (i : Fin 8) : 0 ≤ sortedSpec c ψ i :=
  spec_nonneg c ψ _

theorem sortedSpec_sum (c : Cut 3 4) (hc : Function.Bijective c) (ψ : BitString → ℂ)
    (hψ : UnitVec ψ) : ∑ i, sortedSpec c ψ i = 1 := by
  rw [← spec_sum c hc ψ hψ]
  exact Fintype.sum_equiv specEquiv _ _ (fun _ => rfl)

theorem sortedSpec_entropy (c : Cut 3 4) (ψ : BitString → ℂ) :
    ∑ i, negMulLog (sortedSpec c ψ i) = cutEntropy c ψ :=
  Fintype.sum_equiv specEquiv _ _ (fun _ => rfl)

theorem eigenvalue_le_sortedSpec_zero (c : Cut 3 4) (ψ : BitString → ℂ) (x : Fin 3 → Bool) :
    (redMatPsi_isHermitian c ψ).eigenvalues x ≤ sortedSpec c ψ 0 := by
  have : (redMatPsi_isHermitian c ψ).eigenvalues x = sortedSpec c ψ (specEquiv.symm x) := by
    simp [sortedSpec]
  rw [this]
  exact sortedSpec_antitone c ψ (Fin.zero_le _)

/-- **Hypothesis (spin-flip cross-cut inequality, `eq:seven-spinflip-cross-cut`).**  For every
three-qubit cut `S` of `ψ`, `e_S + 16 v(ρ_S) ≤ R`, where `e_S = 8 tr ρ_S² - 1`,
`R = ∑_T e_T` and `v` is computed from the descending spectrum.  (Not proved here.) -/
def SpinFlipCrossCut (ψ : BitString → ℂ) : Prop :=
  ∀ m ∈ tripleMasks, excess m ψ + 16 * vSpec (sortedSpec (maskCut 3 4 m) ψ) ≤ excessSum ψ

/-- **Linear aggregation.**  The cross-cut inequality at `S` and `lem:seven-entropy-linear-purity` on the
other 34 cuts give `3 ln 2 - S(ρ_S) + (32/5) ln 2 · v(ρ_S) ≤ 35 (3 ln 2 - E₃)`. -/
theorem cut_aggregate (ψ : BitString → ℂ) (hψ : UnitVec ψ) (hS : SpinFlipCrossCut ψ)
    {m : Fin 7 → Bool} (hm : m ∈ tripleMasks) :
    3 * log 2 - cutEntropy (maskCut 3 4 m) ψ +
        (32 / 5) * log 2 * vSpec (sortedSpec (maskCut 3 4 m) ψ) ≤
      35 * (3 * log 2 - meanEntropy3 ψ) := by
  have l2 : 0 < log 2 := Real.log_pos (by norm_num)
  have hmem : ∀ T ∈ tripleMasks, weight T = 3 := fun T hT => (Finset.mem_filter.1 hT).2
  have hT : ∀ T ∈ tripleMasks, (2 / 5) * log 2 * excess T ψ ≤
      3 * log 2 - cutEntropy (maskCut 3 4 T) ψ := fun T hT =>
    cutEntropy_linear_purity _ ψ (maskCut_bijective_three T (hmem T hT)) hψ
  have hsum := Finset.sum_le_sum (s := tripleMasks.erase m)
    (fun T hT' => hT T (Finset.mem_of_mem_erase hT'))
  have e1 : ∑ T ∈ tripleMasks.erase m, (2 / 5) * log 2 * excess T ψ =
      (2 / 5) * log 2 * (excessSum ψ - excess m ψ) := by
    rw [← Finset.mul_sum, Finset.sum_erase_eq_sub hm]; rfl
  have e2 : (3 * log 2 - cutEntropy (maskCut 3 4 m) ψ) +
      ∑ T ∈ tripleMasks.erase m, (3 * log 2 - cutEntropy (maskCut 3 4 T) ψ) =
      ∑ T ∈ tripleMasks, (3 * log 2 - cutEntropy (maskCut 3 4 T) ψ) :=
    Finset.add_sum_erase tripleMasks (fun T => 3 * log 2 - cutEntropy (maskCut 3 4 T) ψ) hm
  have e3 : ∑ T ∈ tripleMasks, (3 * log 2 - cutEntropy (maskCut 3 4 T) ψ) =
      35 * (3 * log 2 - meanEntropy3 ψ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, tripleMasks_card]
    unfold meanEntropy3
    simp only [nsmul_eq_mul]
    push_cast
    ring
  have hv := hS m hm
  have h16 : 16 * ((2 / 5) * log 2 * vSpec (sortedSpec (maskCut 3 4 m) ψ)) ≤
      (2 / 5) * log 2 * (excessSum ψ - excess m ψ) := by nlinarith
  rw [e1] at hsum
  nlinarith [hsum, e2, e3, h16]

/-- **`cor:seven-entropy-eigen-cap-497` (conditional).**  Let `ψ` be a unit vector satisfying the
spin-flip cross-cut inequality (`SpinFlipCrossCut`, hypothesis), and suppose `E₃(ψ) ≥ Eref` where
`Eref > (59307/20000) ln 2` (the SC-2 lower witness for `E₃(ψ_{7/100})`, hypothesis).  Then every
eigenvalue of every three-qubit marginal of `ψ` is `< 497/1000`. -/
theorem eigenCap_497 (ψ : BitString → ℂ) (hψ : UnitVec ψ) (hS : SpinFlipCrossCut ψ)
    {Eref : ℝ} (hwit : (59307 / 20000) * log 2 < Eref) (hE : Eref ≤ meanEntropy3 ψ) :
    ∀ m ∈ tripleMasks, ∀ x, (redMatPsi_isHermitian (maskCut 3 4 m) ψ).eigenvalues x < 497 / 1000 := by
  intro m hm x
  have hmem : weight m = 3 := (Finset.mem_filter.1 hm).2
  have hb := maskCut_bijective_three m hmem
  have hagg := cut_aggregate ψ hψ hS hm
  rw [← sortedSpec_entropy] at hagg
  have h := eigenCap_of_aggregate (sortedSpec_antitone (maskCut 3 4 m) ψ)
    (sortedSpec_nonneg (maskCut 3 4 m) ψ) (sortedSpec_sum _ hb ψ hψ) hagg (hwit.trans_le hE)
  exact (eigenvalue_le_sortedSpec_zero _ ψ x).trans_lt h

end EigCap

end FormalResearch.FourQubitEntropy.SevenQubitConseq
