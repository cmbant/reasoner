import FormalResearch.FourQubitEntropy.Corollaries
import FormalResearch.FourQubitEntropy.Checks

/-!
# The moment defect `𝒟`, the sextic `Q`, and entropy gaps in terms of them

Paper E, `lu_orbit_stability.tex` (eq. `eq:fqe-orbit-surrogate`, `cor:fqe-orbit-spectral`) and
`sextic_identity.tex` (the zero set of `Q`).  Everything here is at the level of the moments
`n, P, T, F, W₁, τ`; the *distance* `d(ψ)` to the two `M₄` orbits, and the constants `c_D, c_C`
relating `d²` to `𝒟`, rest on exact-rational certificates and are not formalized.

* `sexticQ ψ = F + n (P - n²) = 18 n P - 12 T - 13 n³ ≥ 0`; for unit `ψ`, `Q = 0 ↔ F = 0 ∧ P = 1`,
  and `Q = 0` on both `M₄` orbits (the converse, that these are *all* the zeros of `Q`, is the
  zero-set classification of `F`, not formalized).
* `defectD ψ = F + 3 (W₁ + τ) = F + 6 (P - 1) = Q + (5/2)(W₁ + τ)` for unit `ψ`.
* `entropy_gap_ge_defect`: `δ ≥ k 𝒟` with `k = (ln 3 - 1)/(2 ln 2) > 16/225`, so `δ ≥ (16/225) Q`
  (the paper's `δ ≥ k 𝒟 ≥ k Q`, `eq:fqe-orbit-surrogate`; the intermediate `α > 6β` is
  `entropy_alpha_gt_six_beta`).
* `majorant_gap_ge_defect`, `tsallis_gap_ge_defect`: the moment form of
  `cor:fqe-orbit-spectral`, `3 (E_f(M₄) - E_f(ψ)) ≥ min(α/6, a/12) 𝒟`.
-/

open scoped ComplexConjugate Matrix ComplexOrder

namespace FormalResearch.FourQubitEntropy

open Real

/-! ### `Q` and `𝒟` -/

/-- The homogeneous sextic `Q = F + n (P - n²) = 18 n P - 12 T - 13 n³`
(`lu_orbit_stability.tex`). -/
noncomputable def sexticQ (ψ : Psi) : ℝ :=
  sexticF ψ + normSqPsi ψ * (purity ψ - normSqPsi ψ ^ 2)

theorem sexticQ_eq (ψ : Psi) :
    sexticQ ψ = 18 * normSqPsi ψ * purity ψ - 12 * cubicMoment ψ - 13 * normSqPsi ψ ^ 3 := by
  unfold sexticQ sexticF; ring

theorem sexticQ_nonneg (ψ : Psi) : 0 ≤ sexticQ ψ := by
  have h1 := sexticF_nonneg ψ
  have h2 := purity_ge ψ
  have h3 := normSqPsi_nonneg ψ
  unfold sexticQ
  nlinarith [mul_nonneg h3 (sub_nonneg.2 h2)]

/-- For a unit vector, `Q = 0` exactly when `F = 0` and `P = 1`. -/
theorem sexticQ_eq_zero_iff (ψ : Psi) (hn : normSqPsi ψ = 1) :
    sexticQ ψ = 0 ↔ sexticF ψ = 0 ∧ purity ψ = 1 := by
  have h1 := sexticF_nonneg ψ
  have h2 := purity_ge ψ
  rw [hn] at h2
  unfold sexticQ
  rw [hn]
  constructor
  · intro h; constructor <;> nlinarith
  · rintro ⟨hF, hP⟩; rw [hF, hP]; ring

/-- `Q` vanishes on a local-unitary image of a vector with the three cut quadratics
`(R - 1/6)(R - 1/2) = 0` (in particular on both `M₄` orbits). -/
theorem sexticQ_eq_zero_of_quadratics {ψ : Psi} (hψ : normSqPsi ψ = 1) (hq : CutQuadratics ψ) :
    sexticQ ψ = 0 := by
  have hP : purity ψ = 1 := by
    have h := meanSpec_of_quadratics (fun x => x ^ 2) hψ hq
    have e : ∀ {R : Mat4} (hR : R.IsHermitian), cutSum (fun x => x ^ 2) hR
        = (Matrix.trace (R * R)).re := by
      intro R hR
      unfold cutSum
      rw [sum_eigenvalues_pow hR 2, pow_two]
    unfold meanSpec at h
    rw [e, e, e] at h
    unfold purity
    norm_num at h
    linarith
  have hT : cubicMoment ψ = 5 / 12 := by
    have h := meanSpec_of_quadratics (fun x => x ^ 3) hψ hq
    have e : ∀ {R : Mat4} (hR : R.IsHermitian), cutSum (fun x => x ^ 3) hR
        = (Matrix.trace (R * R * R)).re := by
      intro R hR
      unfold cutSum
      rw [sum_eigenvalues_pow hR 3, pow_succ, pow_two]
    unfold meanSpec at h
    rw [e, e, e] at h
    unfold cubicMoment
    norm_num at h
    linarith
  rw [sexticQ_eq, hψ, hP, hT]; norm_num

theorem sexticQ_eq_zero_of_M4_orbit {ψ : Psi}
    (h : LUEquiv M4 ψ ∨ LUEquiv (Psi.conj M4) ψ) : sexticQ ψ = 0 := by
  rcases h with h | h
  · obtain ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩ := h
    exact sexticQ_eq_zero_of_quadratics (by rw [normSqPsi_localApply ha hb hc hd, M4_unit])
      (M4_cutQuadratics.localApply ha hb hc hd)
  · obtain ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩ := h
    have hu : normSqPsi (Psi.conj M4) = 1 := by rw [normSqPsi_conj]; exact M4_unit
    exact sexticQ_eq_zero_of_quadratics (by rw [normSqPsi_localApply ha hb hc hd, hu])
      (M4_cutQuadratics.conj.localApply ha hb hc hd)

/-- The weighted moment defect `𝒟 = F + 3 (W₁ + τ)`. -/
noncomputable def defectD (ψ : Psi) : ℝ :=
  sexticF ψ + 3 * (blochSq ψ + Complex.normSq (spinFlipForm ψ))

theorem defectD_eq_purity (ψ : Psi) (hn : normSqPsi ψ = 1) :
    defectD ψ = sexticF ψ + 6 * (purity ψ - 1) := by
  have h := purity_identity_exact ψ
  rw [hn] at h
  unfold defectD
  linarith

theorem defectD_eq_Q (ψ : Psi) (hn : normSqPsi ψ = 1) :
    defectD ψ = sexticQ ψ + 5 / 2 * (blochSq ψ + Complex.normSq (spinFlipForm ψ)) := by
  have h := purity_identity_exact ψ
  rw [hn] at h
  unfold defectD sexticQ
  rw [hn]
  linarith

theorem sexticQ_le_defectD (ψ : Psi) (hn : normSqPsi ψ = 1) : sexticQ ψ ≤ defectD ψ := by
  rw [defectD_eq_Q ψ hn]
  have := blochSq_nonneg ψ
  have := Complex.normSq_nonneg (spinFlipForm ψ)
  linarith

theorem defectD_nonneg (ψ : Psi) (hn : normSqPsi ψ = 1) : 0 ≤ defectD ψ :=
  le_trans (sexticQ_nonneg ψ) (sexticQ_le_defectD ψ hn)

/-! ### Moment form of `cor:fqe-orbit-spectral` -/

/-- **Spectral-majorant stability, moment form.** For a cubic majorant,
`3 (E_f(M₄) - E_f(ψ)) ≥ min(α/6, a/12) · 𝒟` with `α = -b - 17a/12`. The bound is informative when
`a > 0` and `α > 0` (then the minimum is positive); it holds for any `a, b`. -/
theorem majorant_gap_ge_defect {f : ℝ → ℝ} {a b c d : ℝ} (hM : Majorant f a b c d)
    (ψ : Psi) (hψ : normSqPsi ψ = 1) :
    min ((-b - 17 * a / 12) / 6) (a / 12) * defectD ψ ≤ 3 * (meanSpec f M4 - meanSpec f ψ) := by
  have g := majorant_gap hM ψ hψ
  have hs := majorantSlack_nonneg hM ψ hψ
  have hP : 0 ≤ purity ψ - 1 := by have := purity_ge ψ; rw [hψ] at this; linarith
  have hF := sexticF_nonneg ψ
  have m1 : min ((-b - 17 * a / 12) / 6) (a / 12) ≤ (-b - 17 * a / 12) / 6 := min_le_left _ _
  have m2 : min ((-b - 17 * a / 12) / 6) (a / 12) ≤ a / 12 := min_le_right _ _
  rw [defectD_eq_purity ψ hψ]
  set m := min ((-b - 17 * a / 12) / 6) (a / 12)
  have k1 : m * (6 * (purity ψ - 1)) ≤ (-b - 17 * a / 12) * (purity ψ - 1) := by
    nlinarith [mul_nonneg (sub_nonneg.2 m1) hP]
  have k2 : m * sexticF ψ ≤ a / 12 * sexticF ψ := by
    nlinarith [mul_nonneg (sub_nonneg.2 m2) hF]
  nlinarith

/-- The Tsallis case: for `0 < q < 2`, `q ≠ 1`, with `a_q = tsA q`, `α_q = -tsB q - 17 tsA q/12`,
`min(α_q/6, a_q/12) > 0` and `3 (ceiling - E_q) ≥ min(α_q/6, a_q/12) 𝒟`. -/
theorem tsallis_gap_ge_defect {q : ℝ} (h0 : 0 < q) (h2 : q < 2) (h1 : q ≠ 1) (ψ : Psi)
    (hψ : normSqPsi ψ = 1) :
    0 < min ((-tsB q - 17 * tsA q / 12) / 6) (tsA q / 12) ∧
    min ((-tsB q - 17 * tsA q / 12) / 6) (tsA q / 12) * defectD ψ
      ≤ 3 * (tsallisCeiling q - meanTsallis q ψ) := by
  obtain ⟨hpos, ha⟩ := tsallis_hermite h0 h2 h1
  have hb := tsallis_coeff_neg h0 h2 h1
  refine ⟨lt_min (by linarith) (by linarith), ?_⟩
  have := majorant_gap_ge_defect (tsallis_majorant h0 h2 h1) ψ hψ
  rw [meanTsallis_eq_meanSpec q ψ hψ, tsallisCeiling_eq, ← meanSpec_M4]
  exact this

/-! ### The von Neumann entropy: `δ ≥ k 𝒟`, `k > 16/225` -/

theorem log_three_lt_eleven_tenths : Real.log 3 < 11 / 10 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h1 := Real.exp_one_gt_d9
  have h2 := Real.quadratic_le_exp_of_nonneg (x := (1 / 10 : ℝ)) (by norm_num)
  have : Real.exp (11 / 10) = Real.exp 1 * Real.exp (1 / 10) := by
    rw [← Real.exp_add]; norm_num
  rw [this]
  nlinarith [Real.exp_pos (1 / 10 : ℝ), Real.exp_pos 1]

/-- `log (3/2) ≥ 2 (1/5 + 1/375 + 1/15625 + 1/546875)`, from the series for `log (1 + 1/2)`. -/
theorem log_three_halves_ge : (2 : ℝ) * (1 / 5 + 1 / 375 + 1 / 15625 + 1 / 546875)
    ≤ Real.log (3 / 2) := by
  have h := Real.hasSum_log_one_add_inv (a := 2) (by norm_num)
  have h4 := sum_le_hasSum (Finset.range 4) (fun i _ => by positivity) h
  have e : (1 : ℝ) + (2 : ℝ)⁻¹ = 3 / 2 := by norm_num
  rw [e] at h4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h4
  norm_num at h4 ⊢
  linarith

/-- `k = (ln 3 - 1)/(2 ln 2) > 16/225` (DD-3 of the paper), as `1 + (32/225) ln 2 < ln 3`. -/
theorem one_add_log_two_lt_log_three : 1 + 32 / 225 * Real.log 2 < Real.log 3 := by
  have h1 := log_three_halves_ge
  have e : Real.log 3 = Real.log 2 + Real.log (3 / 2) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h2 := Real.log_two_gt_d9
  rw [e]
  norm_num at h1 h2 ⊢
  nlinarith

theorem entropy_coeff_gt : 16 / 225 < (Real.log 3 - 1) / (2 * Real.log 2) := by
  have l2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [lt_div_iff₀ (by positivity)]
  have := one_add_log_two_lt_log_three
  nlinarith

/-- The coefficients `α = 15/2 - 6 ln 3` of `P - 1` and `β = 3 (ln 3 - 1)/2` of `F` satisfy
`α > 6 β` (since `ln 3 < 11/10`). -/
theorem entropy_alpha_gt_six_beta :
    6 * (3 * (Real.log 3 - 1) / 2) < 15 / 2 - 6 * Real.log 3 := by
  have := log_three_lt_eleven_tenths
  linarith

/-- **Entropy gap against the moment defect** (`eq:fqe-orbit-surrogate`):
`δ(ψ) = E(M₄) - E(ψ) ≥ k 𝒟(ψ)` with `k = (ln 3 - 1)/(2 ln 2)`. -/
theorem entropy_gap_ge_defect (ψ : Psi) (hψ : normSqPsi ψ = 1) :
    (Real.log 3 - 1) / (2 * Real.log 2) * defectD ψ ≤ meanEntropy M4 - meanEntropy ψ := by
  have l2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have g := majorant_gap majorant_negMulLog ψ hψ
  have hs := majorantSlack_nonneg majorant_negMulLog ψ hψ
  have hP : 0 ≤ purity ψ - 1 := by have := purity_ge ψ; rw [hψ] at this; linarith
  have hF := sexticF_nonneg ψ
  have hα := entropy_alpha_gt_six_beta
  have e : 3 * Real.log 2 * (meanEntropy M4 - meanEntropy ψ)
      = 3 * (meanSpec Real.negMulLog M4 - meanSpec Real.negMulLog ψ) := by
    rw [meanEntropy_eq_meanSpec, meanEntropy_eq_meanSpec]
    field_simp
  have ca : -hermB - 17 * hermA / 12 = 15 / 2 - 6 * Real.log 3 := by unfold hermA hermB; ring
  have cb : hermA / 12 = 3 * (Real.log 3 - 1) / 2 := by unfold hermA; ring
  rw [ca, cb] at g
  have hβ : 0 ≤ 3 * (Real.log 3 - 1) / 2 := by have := lt_log_three; linarith
  rw [defectD_eq_purity ψ hψ]
  have key : 3 * (Real.log 3 - 1) / 2 * (sexticF ψ + 6 * (purity ψ - 1))
      ≤ 3 * Real.log 2 * (meanEntropy M4 - meanEntropy ψ) := by
    rw [e, g]
    nlinarith [mul_nonneg hP (sub_nonneg.2 hα.le)]
  have h2 : (Real.log 3 - 1) / (2 * Real.log 2) * (sexticF ψ + 6 * (purity ψ - 1))
      = 3 * (Real.log 3 - 1) / 2 * (sexticF ψ + 6 * (purity ψ - 1)) / (3 * Real.log 2) := by
    field_simp
  rw [h2, div_le_iff₀ (by positivity)]
  linarith

/-- `δ ≥ (16/225) Q`, the explicit nonoptimal surrogate (`k 𝒟 ≥ k Q > (16/225) Q`). -/
theorem entropy_gap_ge_Q (ψ : Psi) (hψ : normSqPsi ψ = 1) :
    16 / 225 * sexticQ ψ ≤ meanEntropy M4 - meanEntropy ψ := by
  have h := entropy_gap_ge_defect ψ hψ
  have hk := entropy_coeff_gt
  have hQ := sexticQ_nonneg ψ
  have hD := sexticQ_le_defectD ψ hψ
  have : 16 / 225 * sexticQ ψ ≤ (Real.log 3 - 1) / (2 * Real.log 2) * defectD ψ := by
    have h3 : 16 / 225 * sexticQ ψ ≤ (Real.log 3 - 1) / (2 * Real.log 2) * sexticQ ψ :=
      mul_le_mul_of_nonneg_right hk.le hQ
    have h4 : (Real.log 3 - 1) / (2 * Real.log 2) * sexticQ ψ
        ≤ (Real.log 3 - 1) / (2 * Real.log 2) * defectD ψ :=
      mul_le_mul_of_nonneg_left hD (by linarith)
    linarith
  linarith

/-- info: 'FormalResearch.FourQubitEntropy.entropy_gap_ge_Q' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 sexticDefect_check._native.native_decide.ax_1_1] -/
#guard_msgs in
#print axioms entropy_gap_ge_Q

/-- info: 'FormalResearch.FourQubitEntropy.sexticQ_eq_zero_of_M4_orbit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sexticQ_eq_zero_of_M4_orbit

/-- info: 'FormalResearch.FourQubitEntropy.entropy_coeff_gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms entropy_coeff_gt

/-- info: 'FormalResearch.FourQubitEntropy.sexticQ_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sexticQ_eq
/-- info: 'FormalResearch.FourQubitEntropy.sexticQ_nonneg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 sexticDefect_check._native.native_decide.ax_1_1] -/
#guard_msgs in
#print axioms sexticQ_nonneg
/-- info: 'FormalResearch.FourQubitEntropy.sexticQ_eq_zero_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 sexticDefect_check._native.native_decide.ax_1_1] -/
#guard_msgs in
#print axioms sexticQ_eq_zero_iff
/-- info: 'FormalResearch.FourQubitEntropy.defectD_eq_purity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms defectD_eq_purity
/-- info: 'FormalResearch.FourQubitEntropy.defectD_eq_Q' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms defectD_eq_Q
/-- info: 'FormalResearch.FourQubitEntropy.majorant_gap_ge_defect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 sexticDefect_check._native.native_decide.ax_1_1] -/
#guard_msgs in
#print axioms majorant_gap_ge_defect
/-- info: 'FormalResearch.FourQubitEntropy.tsallis_gap_ge_defect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 sexticDefect_check._native.native_decide.ax_1_1] -/
#guard_msgs in
#print axioms tsallis_gap_ge_defect
/-- info: 'FormalResearch.FourQubitEntropy.entropy_gap_ge_defect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 sexticDefect_check._native.native_decide.ax_1_1] -/
#guard_msgs in
#print axioms entropy_gap_ge_defect
/-- info: 'FormalResearch.FourQubitEntropy.entropy_alpha_gt_six_beta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms entropy_alpha_gt_six_beta
/-- info: 'FormalResearch.FourQubitEntropy.one_add_log_two_lt_log_three' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms one_add_log_two_lt_log_three

end FormalResearch.FourQubitEntropy
