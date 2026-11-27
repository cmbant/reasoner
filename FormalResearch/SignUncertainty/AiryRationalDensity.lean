module

public import FormalResearch.SignUncertainty.AirySmoothApprox
public import FormalResearch.SignUncertainty.AiryHermiteApprox
public import FormalResearch.SignUncertainty.CeCanonicalDefs
public import FormalResearch.SignUncertainty.EuclidCELift

/-!
# Rational–Airy Density and Conditional Shifted Transfer (`thm:al-rational-density`, `thm:ce-airy-transfer`(1))

Source:
* `CFT/sign_uncertainty/paper/ce_airy_lp_proofs.tex`:
  - Theorem `thm:al-rational-density` (`thm_al_rational_density`, `thm_al_rational_density_hb`,
    `airyUStrict_eq_airyUSh`, lines 893–969):
    strict-site Airy LP witnesses are approximated from below in cutoff by lift seeds
    `H_0 ∈ ℛ_{\mathrm{Ai}}^{\mathrm{gen}}` satisfying `(a)`–`(c)` of `thm:ce-shifted-lift`
    with strict Laplace positivity `ℒ_y(H_0) > 0` for all `y > 0`, yielding
    `u_{\mathrm{strict}}(S) = u_{\mathrm{sh}}(S)`;
  - Proof of `thm:ce-airy-transfer`(1) upper bound (lines 973–981):
    `ce_airy_transfer_upper_of_shifted_lift` derives the `CeCanonicalInputs.ce_airy_transfer_upper`
    field from the Hankel-level statement `CeShiftedLift` of `thm:ce-shifted-lift`.
* `CFT/sign_uncertainty/paper/ce_shifted_witnesses.tex`:
  - Theorem `thm:ce-shifted-lift`: its Hankel-level statement `CeShiftedLift : Prop` and the seed class
    `IsAiryLiftSeed` are in `CeShiftedLiftDefs.lean` (**not proved**; open M6 Mellin–Hankel lift work,
    parallel to `CeHbLiftAssembly.CeHankelPair`); `CeShiftedLift` is the field `shifted_lift` of
    `CeCanonicalInputs`, and `CeCanonicalInputs.ce_airy_transfer_upper` (the former field) is derived here.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set Metric FormalResearch.Special FormalResearch.CohnElkies
open scoped Real Polynomial FourierTransform

namespace FormalResearch.SignUncertainty

/-! ### Section 1: Lift Seeds and Threshold `u_{\mathrm{strict}}(S)` (`thm:ce-shifted-lift` (a)–(c)) -/

/-- Strict-cutoff rational–Airy lift seed at `(S, d_0)` (`thm:al-rational-density` output):
`H_0 ∈ ℛ_{\mathrm{Ai}}^{\mathrm{gen}}` with `∫ H_0 = 0`, `H_0(s) < 0` on `S`, uniform negative-axis
floor `-H_0(u) ≥ c_0 (1 + |u|)^{-3/2}` on `(-∞, d_0]`, `β_+(H_0) > 0`, and strict Laplace positivity
`ℒ_y(H_0) > 0` for all `y > 0`. -/
def IsAiryStrictLiftSeed (S : Set ℝ) (d₀ : ℝ) (H₀ : ℂ → ℂ) : Prop :=
  InGenRationalAiry H₀ ∧
  (∫ u : ℝ, (H₀ (u : ℂ)).re) = 0 ∧
  (∀ s ∈ S, (H₀ (s : ℂ)).re < 0) ∧
  (∃ c₀ : ℝ, 0 < c₀ ∧ ∀ u : ℝ, u ≤ d₀ → c₀ * (1 + |u|) ^ (-(3 / 2 : ℝ)) ≤ -(H₀ (u : ℂ)).re) ∧
  0 < airyBetaPlus H₀ ∧
  (∀ y : ℝ, 0 < y → 0 < airyLaplace (fun u => (H₀ (u : ℂ)).re) y)

/-- Supremum `u_{\mathrm{strict}}(S)` of cutoffs `u_*` admitting a rational–Airy lift seed
(`ce_airy_lp_proofs.tex` line 900). -/
noncomputable def airyUStrict (S : Set ℝ) : EReal :=
  ⨆ (u : ℝ) (_ : ∃ H₀, IsAiryLiftSeed S u H₀), (u : EReal)

lemma IsAiryStrictLiftSeed.to_isAiryLiftSeed {S : Set ℝ} {d₀ : ℝ} {H₀ : ℂ → ℂ}
    (h : IsAiryStrictLiftSeed S d₀ H₀) : IsAiryLiftSeed S d₀ H₀ :=
  ⟨h.1, h.2.1, h.2.2.1, Or.inl h.2.2.2.1, h.2.2.2.2.1, fun y hy => (h.2.2.2.2.2 y hy).le⟩

/-- Every `IsAiryLiftSeed S u_* H₀` is a strict-site Airy LP witness (`IsAiryStrictWitness S u_* H₀`). -/
lemma IsAiryLiftSeed.to_isAiryStrictWitness {S : Set ℝ} {u_star : ℝ} {H₀ : ℂ → ℂ}
    (h : IsAiryLiftSeed S u_star H₀) : IsAiryStrictWitness S u_star H₀ := by
  obtain ⟨hRat, hint0, hsites, hfloor, hbplus, hlap⟩ := h
  have hcl : InAiryClass H₀ := hRat.inAiryClass
  have hnz : ∃ z : ℂ, H₀ z ≠ 0 := by
    by_contra hall
    push Not at hall
    have hzero : H₀ = fun _ => 0 := funext hall
    rw [hzero, HasGenRationalAiryCoeffs.zero.beta_eq.2.2.2] at hbplus
    linarith
  have hray : ∀ u : ℝ, u ≤ u_star → (H₀ (u : ℂ)).re ≤ 0 := by
    intro u hu
    rcases hfloor with ⟨c₀, hc₀, hb⟩ | ⟨hlt, heq0, _, _⟩
    · have hnn : 0 ≤ c₀ * (1 + |u|) ^ (-(3 / 2 : ℝ)) := by positivity
      linarith [hb u hu]
    · rcases hu.lt_or_eq with hlt_u | rfl
      · exact (hlt u hlt_u).le
      · exact heq0.le
  have hlap0 : ∀ y : ℝ, 0 ≤ y → 0 ≤ airyLaplace (fun u => (H₀ (u : ℂ)).re) y := by
    intro y hy
    rcases hy.eq_or_lt with rfl | hy_pos
    · unfold airyLaplace
      simp [hint0]
    · exact hlap y hy_pos
  exact ⟨⟨hcl, hnz, fun s hs => (hsites s hs).le, hray, hlap0⟩, hsites⟩

/-! ### Section 2: Supporting Lemmas for `thm:al-rational-density` -/

private lemma airyLaplace_zero_eq_integral (f : ℝ → ℝ) :
    airyLaplace f 0 = ∫ u : ℝ, f u := by
  unfold airyLaplace
  have hexp0 : Real.exp (-(0 ^ 3) / 12) = 1 := by norm_num
  rw [hexp0, one_mul]
  simp

private lemma airyLaplace_add_re {F G : ℂ → ℂ} (hF : InAiryClass F) (hG : InAiryClass G)
    {y : ℝ} (hy : 0 ≤ y) :
    airyLaplace (fun u => (F (u : ℂ) + G (u : ℂ)).re) y =
      airyLaplace (fun u => (F (u : ℂ)).re) y + airyLaplace (fun u => (G (u : ℂ)).re) y := by
  unfold airyLaplace
  have hFy := hF.integrable_exp_nonneg hy
  have hGy := hG.integrable_exp_nonneg hy
  have heq : (fun u : ℝ => (F (u : ℂ) + G (u : ℂ)).re * Real.exp (y * u)) =
      fun u : ℝ => (F (u : ℂ)).re * Real.exp (y * u) + (G (u : ℂ)).re * Real.exp (y * u) := by
    ext u; simp [Complex.add_re, add_mul]
  rw [heq, integral_add hFy hGy, mul_add]

private lemma airyLaplace_sub_re {F G : ℂ → ℂ} (hF : InAiryClass F) (hG : InAiryClass G)
    {y : ℝ} (hy : 0 ≤ y) :
    airyLaplace (fun u => (F (u : ℂ) - G (u : ℂ)).re) y =
      airyLaplace (fun u => (F (u : ℂ)).re) y - airyLaplace (fun u => (G (u : ℂ)).re) y := by
  unfold airyLaplace
  have hFy := hF.integrable_exp_nonneg hy
  have hGy := hG.integrable_exp_nonneg hy
  have heq : (fun u : ℝ => (F (u : ℂ) - G (u : ℂ)).re * Real.exp (y * u)) =
      fun u : ℝ => (F (u : ℂ)).re * Real.exp (y * u) - (G (u : ℂ)).re * Real.exp (y * u) := by
    ext u; simp [Complex.sub_re, sub_mul]
  rw [heq, integral_sub hFy hGy, mul_sub]

private lemma airyLaplace_smul_re {F : ℂ → ℂ} (_hF : InAiryClass F) (c : ℝ)
    {y : ℝ} (_hy : 0 ≤ y) :
    airyLaplace (fun u => ((c : ℂ) * F (u : ℂ)).re) y =
      c * airyLaplace (fun u => (F (u : ℂ)).re) y := by
  unfold airyLaplace
  have heq : (fun u : ℝ => ((c : ℂ) * F (u : ℂ)).re * Real.exp (y * u)) =
      fun u : ℝ => c * ((F (u : ℂ)).re * Real.exp (y * u)) := by
    ext u; simp [mul_assoc]
  rw [heq, integral_const_mul]
  ring

private lemma airyBetaPlus_add {F G : ℂ → ℂ} (hF : InGenRationalAiry F) (hG : InGenRationalAiry G) :
    airyBetaPlus (fun z => F z + G z) = airyBetaPlus F + airyBetaPlus G := by
  have hsum := hF.hasCoeffs.add hG.hasCoeffs
  rw [hsum.beta_eq.2.2.2, hF.hasCoeffs.beta_eq.2.2.2, hG.hasCoeffs.beta_eq.2.2.2]
  ring

private lemma airyBetaPlus_sub {F G : ℂ → ℂ} (hF : InGenRationalAiry F) (hG : InGenRationalAiry G) :
    airyBetaPlus (fun z => F z - G z) = airyBetaPlus F - airyBetaPlus G := by
  have hsub := hF.hasCoeffs.sub hG.hasCoeffs
  rw [hsub.beta_eq.2.2.2, hF.hasCoeffs.beta_eq.2.2.2, hG.hasCoeffs.beta_eq.2.2.2]
  ring

private lemma airyBetaPlus_smul {F : ℂ → ℂ} (hF : InGenRationalAiry F) (c : ℝ) :
    airyBetaPlus (fun z => (c : ℂ) * F z) = c * airyBetaPlus F := by
  have hsm := hF.hasCoeffs.smul c
  rw [hsm.beta_eq.2.2.2, hF.hasCoeffs.beta_eq.2.2.2]
  ring

/-- Compact positive minimum via `exists_bound_of_continuousOn` on the reciprocal (works for
possibly empty `K`). -/
private lemma exists_pos_lower_bound_on_compact {α : Type*} [TopologicalSpace α]
    {K : Set α} (hK : IsCompact K) {g : α → ℝ}
    (hg_cont : ContinuousOn g K) (hg_pos : ∀ x ∈ K, 0 < g x) :
    ∃ m : ℝ, 0 < m ∧ ∀ x ∈ K, m ≤ g x := by
  have hinv_cont : ContinuousOn (fun x => (g x)⁻¹) K :=
    hg_cont.inv₀ fun x hx => (hg_pos x hx).ne'
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hinv_cont
  set B : ℝ := max M 1
  have hB_pos : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨1 / B, by positivity, fun x hx => ?_⟩
  have hgx : 0 < g x := hg_pos x hx
  have h1 := (hM x hx).trans (le_max_left M 1)
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hgx)] at h1
  have hmul : 1 ≤ B * g x := by
    have hm := mul_le_mul_of_nonneg_right h1 hgx.le
    rwa [inv_mul_cancel₀ hgx.ne'] at hm
  exact (div_le_iff₀' hB_pos).mpr hmul

private lemma exists_sub_Ioo_avoid {a b : ℝ} (hab : a < b) (c : ℝ) :
    ∃ a' b' : ℝ, a ≤ a' ∧ b' ≤ b ∧ a' < b' ∧ c ∉ Ioo a' b' := by
  by_cases hc : c ≤ (a + b) / 2
  · refine ⟨(a + b) / 2, b, by linarith, le_rfl, by linarith, ?_⟩
    intro hmem; linarith [hmem.1]
  · refine ⟨a, (a + b) / 2, le_rfl, by linarith, by linarith, ?_⟩
    intro hmem; linarith [hmem.2]

private lemma airySeedG1Deriv_re_of_ne {x : ℝ} (hx : x ≠ airyDerivFirstZero) :
    (airySeedG1Deriv (x : ℂ)).re = (airyAi' x / (x - airyDerivFirstZero)) ^ 2 := by
  have hne_c : (x : ℂ) ≠ (airyDerivFirstZero : ℂ) := fun h => hx (Complex.ofReal_injective h)
  have ha1'_zero : deriv airyAiC (airyDerivFirstZero : ℂ) = 0 := by
    rw [deriv_airyAiC_ofReal, airyDerivFirstZero_spec.2.2, Complex.ofReal_zero]
  have hcard : airyDerivCardinalC (x : ℂ) = ((airyAi' x / (x - airyDerivFirstZero) : ℝ) : ℂ) := by
    unfold airyDerivCardinalC
    rw [dslope_of_ne _ hne_c, slope_def_field, ha1'_zero, sub_zero, deriv_airyAiC_ofReal,
      ← Complex.ofReal_sub, ← Complex.ofReal_div]
  unfold airySeedG1Deriv
  rw [hcard, ← Complex.ofReal_pow, Complex.ofReal_re]

/-- In every nonempty open interval `(v, v_0)`, there is a point `d_0` where `g_1'(d_0) > 0`. -/
private lemma exists_cutoff_airySeedG1Deriv_pos {v v₀ : ℝ} (hvv₀ : v < v₀) :
    ∃ d₀ : ℝ, v < d₀ ∧ d₀ < v₀ ∧ 0 < (airySeedG1Deriv (d₀ : ℂ)).re := by
  by_contra hnone
  push Not at hnone
  obtain ⟨a₁, b₁, ha₁, hb₁, hab₁, hav1⟩ := exists_sub_Ioo_avoid hvv₀ airyDerivFirstZero
  obtain ⟨a₂, b₂, ha₂, hb₂, hab₂, hav0⟩ := exists_sub_Ioo_avoid hab₁ 0
  have hAi'_zero_on : ∀ x ∈ Ioo a₂ b₂, airyAi' x = 0 := by
    intro x hx
    have hx_vv₀ : x ∈ Ioo v v₀ := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hx_ab₁ : x ∈ Ioo a₁ b₁ := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hx_ne : x ≠ airyDerivFirstZero := fun h => hav1 (h ▸ hx_ab₁)
    have hg0 : (airySeedG1Deriv (x : ℂ)).re = 0 :=
      le_antisymm (hnone x hx_vv₀.1 hx_vv₀.2) (airySeedG1Deriv_re_nonneg x)
    rw [airySeedG1Deriv_re_of_ne hx_ne] at hg0
    have hdiv0 : airyAi' x / (x - airyDerivFirstZero) = 0 := sq_eq_zero_iff.mp hg0
    exact (div_eq_zero_iff.mp hdiv0).resolve_right (sub_ne_zero.mpr hx_ne)
  set x₀ : ℝ := (a₂ + b₂) / 2
  have hx₀_mem : x₀ ∈ Ioo a₂ b₂ := ⟨by dsimp [x₀]; linarith, by dsimp [x₀]; linarith⟩
  have hx₀_ne0 : x₀ ≠ 0 := fun h => hav0 (h ▸ hx₀_mem)
  have hev : airyAi' =ᶠ[𝓝 x₀] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx₀_mem] with x hx
    exact hAi'_zero_on x hx
  have hd0 : deriv airyAi' x₀ = 0 := by
    rw [hev.deriv_eq, deriv_const]
  have hd_ode : deriv airyAi' x₀ = x₀ * airyAi x₀ := (hasDerivAt_airyAi' x₀).deriv
  have hAi0 : airyAi x₀ = 0 := (mul_eq_zero.mp (hd_ode.symm.trans hd0)).resolve_left hx₀_ne0
  have hAiC0 : airyAiC (x₀ : ℂ) = 0 := by rw [airyAiC_ofReal, hAi0, Complex.ofReal_zero]
  obtain ⟨k, hk1, hkz⟩ := (airyAiC_eq_zero_iff (x₀ : ℂ)).mp hAiC0
  have hx₀_z : x₀ = airyZ (k - 1) := by
    have hreal := Complex.ofReal_injective hkz
    rw [hreal]; unfold airyZ; rw [Nat.sub_add_cancel hk1]
  have hAi'0 : airyAi' (airyZ (k - 1)) = 0 := hx₀_z ▸ hAi'_zero_on x₀ hx₀_mem
  exact airyAi'_airyZ_ne_zero (k - 1) hAi'0

/-- Rational–Airy strict buffer `R = B_1 - α g_1'` (`ce_airy_lp_proofs.tex` lines 906–929). -/
private lemma exists_rational_buffer {d₀ : ℝ} (hd₀ : d₀ < airyZ 0)
    (hg1_pos : 0 < (airySeedG1Deriv (d₀ : ℂ)).re) :
    ∃ R : ℂ → ℂ,
      InGenRationalAiry R ∧
      (0 < ∫ u : ℝ, (R (u : ℂ)).re) ∧
      1 / 2 ≤ airyBetaPlus R ∧
      (∃ c_R : ℝ, 0 < c_R ∧ ∀ u : ℝ, u ≤ d₀ →
        c_R * (1 + |u|) ^ (-(3 / 2 : ℝ)) ≤ -(R (u : ℂ)).re) ∧
      (∃ c_L : ℝ, 0 < c_L ∧ ∀ y : ℝ, 0 ≤ y →
        c_L * (1 + y) ^ (-(5 / 2 : ℝ)) ≤ airyLaplace (fun u => (R (u : ℂ)).re) y) := by
  let c1 : Fin 1 → ℝ := fun _ => 1
  have hc1_sum_ne : (∑ n : Fin 1, c1 n) ≠ 0 := by simp [c1]
  let B₁ : ℂ → ℂ := airyTrialSquareWitness 1 c1 d₀
  have hB₁_cl : InAiryClass B₁ := airyTrialSquareWitness_inAiryClass c1 d₀
  have hB₁_eq : ∀ z : ℂ, B₁ z = airySeedF 0 z + ((airyZ 0 - d₀ : ℝ) : ℂ) * airySeedG 0 z := by
    intro z
    dsimp [B₁]
    unfold airyTrialSquareWitness airySectionPoly airySeedF airySeedG
    simp only [Fin.sum_univ_one, Fin.val_zero, c1, Complex.ofReal_one, one_mul, Complex.ofReal_sub]
    calc (z - (d₀ : ℂ)) * airyCardinal 0 z ^ 2
        = ((z - (airyZ 0 : ℂ)) * airyCardinal 0 z) * airyCardinal 0 z +
            ((airyZ 0 : ℂ) - (d₀ : ℂ)) * airyCardinal 0 z ^ 2 := by ring
      _ = airyAiC z * airyCardinal 0 z + ((airyZ 0 : ℂ) - (d₀ : ℂ)) * airyCardinal 0 z ^ 2 := by
          rw [mul_airyCardinal]
  have hB₁_coeffs : HasGenRationalAiryCoeffs B₁ (-1) 0 := by
    have hsum := (hasGenRationalAiryCoeffs_airySeedF 0).add
      ((hasGenRationalAiryCoeffs_airySeedG 0).smul (airyZ 0 - d₀))
    simp only [mul_zero, add_zero] at hsum
    rwa [← funext hB₁_eq] at hsum
  have hB₁_re : ∀ u : ℝ, (B₁ (u : ℂ)).re = (u - d₀) * (airySeedG 0 (u : ℂ)).re := by
    intro u
    dsimp [B₁]
    rw [airyTrialSquareWitness_re, airySeedG_re]
    unfold airySectionPolyR
    simp [c1]
  have hB₁_int : (∫ u : ℝ, (B₁ (u : ℂ)).re) = airyZ 0 - d₀ := by
    dsimp [B₁]
    rw [integral_airyTrialSquareWitness]
    simp [c1]
  -- 1. Large-`y` Laplace lower bound for `B₁` via `airyTrialSquareWitness_ge_refJ0_tail`
  obtain ⟨U, b, hU_gt, hb_pos, htail_ge⟩ := airyTrialSquareWitness_ge_refJ0_tail hc1_sum_ne d₀
  obtain ⟨c_J, C_J1, hc_J_pos, hcle_J, hJ_lap_bd⟩ := airyLaplace_airyRefJ0_bounds
  have hCJ1_pos : 0 < C_J1 := lt_of_lt_of_le hc_J_pos hcle_J
  let g_err : ℝ → ℝ := fun u => (B₁ (u : ℂ)).re - b * (airyRefJ0 (u : ℂ)).re
  have hg_err_int : Integrable g_err := hB₁_cl.2.1.re.sub (airyRefJ0_inAiryClass.2.1.re.const_mul b)
  let M_err : ℝ := ∫ u : ℝ, |g_err u|
  have hM_err_nn : 0 ≤ M_err := integral_nonneg fun _ => abs_nonneg _
  have hlim_err : Tendsto (fun y : ℝ =>
      M_err * (1 + y) ^ (5 / 2 : ℝ) * Real.exp (y * U - y ^ 3 / 12)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun y : ℝ => (2 * y) ^ (5 / 2 : ℝ) * Real.exp (-(1 / 24 : ℝ) * y))
        atTop (𝓝 0) := by
      have ha := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (5 / 2 : ℝ) (1 / 24 : ℝ) (by norm_num)
      have hb := ha.const_mul ((2 : ℝ) ^ (5 / 2 : ℝ))
      rw [mul_zero] at hb
      refine hb.congr' ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy0
      rw [Real.mul_rpow (by norm_num) hy0, mul_assoc]
    have h2 := h1.const_mul M_err
    rw [mul_zero] at h2
    refine squeeze_zero_norm' ?_ h2
    have hU_nn : 0 ≤ 24 * U + 2 := by
      have : 0 < U := lt_of_le_of_lt (le_max_left 0 d₀) hU_gt
      positivity
    filter_upwards [eventually_ge_atTop (max 1 (Real.sqrt (24 * U + 2)))] with y hy
    have hy1 : 1 ≤ y := (le_max_left _ _).trans hy
    have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy1
    have hy_sq : 24 * U + 2 ≤ y ^ 2 := by
      have hsr : Real.sqrt (24 * U + 2) ≤ y := (le_max_right _ _).trans hy
      calc 24 * U + 2 = (Real.sqrt (24 * U + 2)) ^ 2 := (Real.sq_sqrt hU_nn).symm
        _ ≤ y ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsr 2
    have hexp_le : y * U - y ^ 3 / 12 ≤ -(1 / 24 : ℝ) * y := by
      have hmul : (24 * U + 2) * y ≤ y ^ 3 :=
        (mul_le_mul_of_nonneg_right hy_sq hy0.le).trans_eq (by ring)
      have hy3 : 0 ≤ y ^ 3 := by positivity
      have h24 : 24 * (y * U - y ^ 3 / 12 + (1 / 24 : ℝ) * y) =
          ((24 * U + 2) * y - y ^ 3) - y ^ 3 - y := by ring
      linarith
    have hrpow_le : (1 + y) ^ (5 / 2 : ℝ) ≤ (2 * y) ^ (5 / 2 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
    rw [Real.norm_of_nonneg (by positivity)]
    calc M_err * (1 + y) ^ (5 / 2 : ℝ) * Real.exp (y * U - y ^ 3 / 12)
        = M_err * ((1 + y) ^ (5 / 2 : ℝ) * Real.exp (y * U - y ^ 3 / 12)) := by ring
      _ ≤ M_err * ((2 * y) ^ (5 / 2 : ℝ) * Real.exp (-(1 / 24 : ℝ) * y)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul hrpow_le (Real.exp_le_exp.mpr hexp_le) (Real.exp_pos _).le (by positivity))
            hM_err_nn
  obtain ⟨Y₁, hY₁⟩ := eventually_atTop.mp
    (hlim_err.eventually (gt_mem_nhds (mul_pos (half_pos hb_pos) hc_J_pos)))
  set Y_B : ℝ := max Y₁ 1
  have hY_B_ge1 : 1 ≤ Y_B := le_max_right _ _
  have hB₁_lap_large : ∀ y : ℝ, Y_B ≤ y →
      ((b / 2) * c_J) * (1 + y) ^ (-(5 / 2 : ℝ)) ≤ airyLaplace (fun u => (B₁ (u : ℂ)).re) y := by
    intro y hy
    have hy0 : 0 ≤ y := le_trans zero_le_one (hY_B_ge1.trans hy)
    have hyY₁ : Y₁ ≤ y := (le_max_left _ _).trans hy
    have hF_y : Integrable (fun u : ℝ => (B₁ (u : ℂ)).re * Real.exp (y * u)) :=
      hB₁_cl.integrable_exp_nonneg hy0
    have hJ_y : Integrable (fun u : ℝ => (airyRefJ0 (u : ℂ)).re * Real.exp (y * u)) :=
      airyRefJ0_inAiryClass.integrable_exp_nonneg hy0
    have hg_y : Integrable (fun u : ℝ => g_err u * Real.exp (y * u)) := by
      have heq : (fun u : ℝ => g_err u * Real.exp (y * u)) =
          fun u : ℝ => (B₁ (u : ℂ)).re * Real.exp (y * u) -
            b * ((airyRefJ0 (u : ℂ)).re * Real.exp (y * u)) := by ext u; dsimp [g_err]; ring
      rw [heq]; exact hF_y.sub (hJ_y.const_mul b)
    have hsplit_g : (∫ u : ℝ, g_err u * Real.exp (y * u)) =
        (∫ u in Iic U, g_err u * Real.exp (y * u)) + ∫ u in Ioi U, g_err u * Real.exp (y * u) := by
      rw [← compl_Iic]
      exact (integral_add_compl measurableSet_Iic hg_y).symm
    have hIoi_nn : 0 ≤ ∫ u in Ioi U, g_err u * Real.exp (y * u) :=
      setIntegral_nonneg measurableSet_Ioi fun u (hu : U < u) =>
        mul_nonneg (by dsimp [g_err]; linarith [htail_ge u hu.le]) (Real.exp_pos _).le
    have hIic_lb : -M_err * Real.exp (y * U) ≤ ∫ u in Iic U, g_err u * Real.exp (y * u) := by
      have h1 : (∫ u in Iic U, -(g_err u * Real.exp (y * u))) ≤
          ∫ u in Iic U, |g_err u| * Real.exp (y * U) := by
        refine setIntegral_mono_on hg_y.neg.integrableOn (hg_err_int.abs.mul_const _).integrableOn
          measurableSet_Iic fun u (hu : u ≤ U) => ?_
        have hexp : Real.exp (y * u) ≤ Real.exp (y * U) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu hy0)
        nlinarith [neg_abs_le (g_err u), Real.exp_pos (y * u), abs_nonneg (g_err u)]
      have h2 : (∫ u in Iic U, |g_err u| * Real.exp (y * U)) ≤ M_err * Real.exp (y * U) := by
        rw [integral_mul_const]
        exact mul_le_mul_of_nonneg_right
          (setIntegral_le_integral hg_err_int.abs (Eventually.of_forall fun _ => abs_nonneg _))
          (Real.exp_pos _).le
      rw [integral_neg] at h1
      linarith
    have hg_int_eq : (∫ u : ℝ, g_err u * Real.exp (y * u)) =
        (∫ u : ℝ, (B₁ (u : ℂ)).re * Real.exp (y * u)) -
          b * ∫ u : ℝ, (airyRefJ0 (u : ℂ)).re * Real.exp (y * u) := by
      have heq : (fun u : ℝ => g_err u * Real.exp (y * u)) =
          fun u : ℝ => (B₁ (u : ℂ)).re * Real.exp (y * u) -
            b * ((airyRefJ0 (u : ℂ)).re * Real.exp (y * u)) := by ext u; dsimp [g_err]; ring
      rw [heq, integral_sub hF_y (hJ_y.const_mul b), integral_const_mul]
    have hdiff_lap : -M_err * Real.exp (y * U - y ^ 3 / 12) ≤
        airyLaplace (fun u => (B₁ (u : ℂ)).re) y -
          b * airyLaplace (fun u => (airyRefJ0 (u : ℂ)).re) y := by
      unfold airyLaplace
      have hexp_split : Real.exp (y * U - y ^ 3 / 12) =
          Real.exp (-y ^ 3 / 12) * Real.exp (y * U) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [hexp_split]
      have hmul_lb := mul_le_mul_of_nonneg_left
        (by linarith : -M_err * Real.exp (y * U) ≤
          (∫ u : ℝ, (B₁ (u : ℂ)).re * Real.exp (y * u)) -
            b * ∫ u : ℝ, (airyRefJ0 (u : ℂ)).re * Real.exp (y * u))
        (Real.exp_pos (-y ^ 3 / 12)).le
      linarith
    have herr_lt := hY₁ y hyY₁
    have h1y_neg_pos : 0 < (1 + y) ^ (-(5 / 2 : ℝ)) := Real.rpow_pos_of_pos (by linarith) _
    have hrpow_inv : (1 + y) ^ (5 / 2 : ℝ) * (1 + y) ^ (-(5 / 2 : ℝ)) = 1 := by
      rw [← Real.rpow_add (by linarith : 0 < 1 + y)]; norm_num
    have herr_small : M_err * Real.exp (y * U - y ^ 3 / 12) <
        ((b / 2) * c_J) * (1 + y) ^ (-(5 / 2 : ℝ)) := by
      have hmul := mul_lt_mul_of_pos_right herr_lt h1y_neg_pos
      calc M_err * Real.exp (y * U - y ^ 3 / 12)
          = M_err * Real.exp (y * U - y ^ 3 / 12) *
              ((1 + y) ^ (5 / 2 : ℝ) * (1 + y) ^ (-(5 / 2 : ℝ))) := by rw [hrpow_inv, mul_one]
        _ = (M_err * (1 + y) ^ (5 / 2 : ℝ) * Real.exp (y * U - y ^ 3 / 12)) *
              (1 + y) ^ (-(5 / 2 : ℝ)) := by ring
        _ < ((b / 2) * c_J) * (1 + y) ^ (-(5 / 2 : ℝ)) := hmul
    have hJ_lb := mul_le_mul_of_nonneg_left (hJ_lap_bd y hy0).1 hb_pos.le
    linarith
  -- 2. Bounded-`y` Laplace lower bound (`0 ≤ y ≤ Y_B`) via `(u - d₀)(e^{y u} - e^{y d₀}) ≥ 0`
  have hd₀_neg : d₀ < 0 := hd₀.trans (airyZ_neg 0)
  set c_small : ℝ := Real.exp (-(Y_B ^ 3) / 12 + Y_B * d₀) * (airyZ 0 - d₀)
  have hc_small_pos : 0 < c_small := mul_pos (Real.exp_pos _) (sub_pos.mpr hd₀)
  have hB₁_lap_small : ∀ y : ℝ, 0 ≤ y → y ≤ Y_B →
      c_small * (1 + y) ^ (-(5 / 2 : ℝ)) ≤ airyLaplace (fun u => (B₁ (u : ℂ)).re) y := by
    intro y hy0 hyB
    have hpt : ∀ u : ℝ, (B₁ (u : ℂ)).re * Real.exp (y * d₀) ≤
        (B₁ (u : ℂ)).re * Real.exp (y * u) := by
      intro u
      rw [hB₁_re u]
      have hg_nn := airySeedG_re_nonneg 0 u
      rcases le_or_gt d₀ u with hdu | hdu
      · have hexp : Real.exp (y * d₀) ≤ Real.exp (y * u) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hdu hy0)
        exact mul_le_mul_of_nonneg_left hexp (mul_nonneg (sub_nonneg.mpr hdu) hg_nn)
      · have hexp : Real.exp (y * u) ≤ Real.exp (y * d₀) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hdu.le hy0)
        have hnonpos : (u - d₀) * (airySeedG 0 (u : ℂ)).re ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by linarith) hg_nn
        exact mul_le_mul_of_nonpos_left hexp hnonpos
    have hint_ge : Real.exp (y * d₀) * (airyZ 0 - d₀) ≤
        ∫ u : ℝ, (B₁ (u : ℂ)).re * Real.exp (y * u) := by
      have hm := integral_mono (hB₁_cl.2.1.re.mul_const (Real.exp (y * d₀)))
        (hB₁_cl.integrable_exp_nonneg hy0) hpt
      rw [integral_mul_const] at hm
      change (∫ u : ℝ, (B₁ (u : ℂ)).re) * Real.exp (y * d₀) ≤
        ∫ u : ℝ, (B₁ (u : ℂ)).re * Real.exp (y * u) at hm
      rw [hB₁_int] at hm
      linarith
    have hexp_ge : Real.exp (-(Y_B ^ 3) / 12 + Y_B * d₀) ≤
        Real.exp (-(y ^ 3) / 12) * Real.exp (y * d₀) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hy3 : y ^ 3 ≤ Y_B ^ 3 := pow_le_pow_left₀ hy0 hyB 3
      have hyd : Y_B * d₀ ≤ y * d₀ := mul_le_mul_of_nonpos_right hyB hd₀_neg.le
      linarith
    have hrpow_le1 : (1 + y) ^ (-(5 / 2 : ℝ)) ≤ 1 := by
      have h := Real.rpow_le_rpow_of_nonpos zero_lt_one (by linarith : (1 : ℝ) ≤ 1 + y)
        (by norm_num : -(5 / 2 : ℝ) ≤ 0)
      rwa [Real.one_rpow] at h
    unfold airyLaplace
    calc c_small * (1 + y) ^ (-(5 / 2 : ℝ))
        ≤ c_small * 1 := mul_le_mul_of_nonneg_left hrpow_le1 hc_small_pos.le
      _ = Real.exp (-(Y_B ^ 3) / 12 + Y_B * d₀) * (airyZ 0 - d₀) := mul_one _
      _ ≤ (Real.exp (-(y ^ 3) / 12) * Real.exp (y * d₀)) * (airyZ 0 - d₀) :=
          mul_le_mul_of_nonneg_right hexp_ge (sub_pos.mpr hd₀).le
      _ = Real.exp (-(y ^ 3) / 12) * (Real.exp (y * d₀) * (airyZ 0 - d₀)) := by ring
      _ ≤ Real.exp (-(y ^ 3) / 12) * ∫ u : ℝ, (B₁ (u : ℂ)).re * Real.exp (y * u) :=
          mul_le_mul_of_nonneg_left hint_ge (Real.exp_pos _).le
  set c_B : ℝ := min ((b / 2) * c_J) c_small
  have hc_B_pos : 0 < c_B := lt_min (by positivity) hc_small_pos
  have hB₁_lap : ∀ y : ℝ, 0 ≤ y →
      c_B * (1 + y) ^ (-(5 / 2 : ℝ)) ≤ airyLaplace (fun u => (B₁ (u : ℂ)).re) y := by
    intro y hy0
    by_cases hyB : y ≤ Y_B
    · exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)).trans
        (hB₁_lap_small y hy0 hyB)
    · push Not at hyB
      exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)).trans
        (hB₁_lap_large y hyB.le)
  -- 3. Subtract `α • airySeedG1Deriv`
  have hg1_lap_ub : ∀ y : ℝ, 0 ≤ y →
      airyLaplace (fun u => (airySeedG1Deriv (u : ℂ)).re) y ≤
        C_J1 * (1 + y) ^ (-(5 / 2 : ℝ)) := by
    intro y hy0
    have hpt : ∀ u : ℝ, (airySeedG1Deriv (u : ℂ)).re * Real.exp (y * u) ≤
        (airyRefJ0 (u : ℂ)).re * Real.exp (y * u) := by
      intro u
      have hsub := congrArg Complex.re (airySeedG1Deriv_eq_sub_refJ0 (u : ℂ))
      rw [Complex.sub_re] at hsub
      have hle : (airySeedG1Deriv (u : ℂ)).re ≤ (airyRefJ0 (u : ℂ)).re := by
        linarith [airySeedG_re_nonneg 0 u]
      exact mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
    have hmono : airyLaplace (fun u => (airySeedG1Deriv (u : ℂ)).re) y ≤
        airyLaplace (fun u => (airyRefJ0 (u : ℂ)).re) y := by
      unfold airyLaplace
      exact mul_le_mul_of_nonneg_left
        (integral_mono (airySeedG1Deriv_inAiryClass.integrable_exp_nonneg hy0)
          (airyRefJ0_inAiryClass.integrable_exp_nonneg hy0) hpt)
        (Real.exp_pos _).le
    exact hmono.trans (hJ_lap_bd y hy0).2
  set α : ℝ := min (1 / 2) (c_B / (2 * C_J1))
  have hα_pos : 0 < α := lt_min (by norm_num) (by positivity)
  have hα_le_half : α ≤ 1 / 2 := min_le_left _ _
  have hα_CJ1 : α * C_J1 ≤ c_B / 2 := by
    calc α * C_J1 ≤ (c_B / (2 * C_J1)) * C_J1 :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hCJ1_pos.le
      _ = c_B / 2 := by field_simp [hCJ1_pos.ne']
  let R : ℂ → ℂ := fun z => B₁ z - (α : ℂ) * airySeedG1Deriv z
  have hR_coeffs : HasGenRationalAiryCoeffs R (-1) (-α) := by
    have hs := hB₁_coeffs.sub (hasGenRationalAiryCoeffs_airySeedG1Deriv.smul α)
    simpa only [mul_zero, sub_zero, mul_one, zero_sub] using hs
  have hR_rat : InGenRationalAiry R := ⟨-1, -α, hR_coeffs⟩
  have hR_bplus : 1 / 2 ≤ airyBetaPlus R := by
    rw [hR_coeffs.beta_eq.2.2.2]
    linarith
  have hR_lap : ∀ y : ℝ, 0 ≤ y →
      (c_B / 2) * (1 + y) ^ (-(5 / 2 : ℝ)) ≤ airyLaplace (fun u => (R (u : ℂ)).re) y := by
    intro y hy0
    have hlin : airyLaplace (fun u => (R (u : ℂ)).re) y =
        airyLaplace (fun u => (B₁ (u : ℂ)).re) y -
          α * airyLaplace (fun u => (airySeedG1Deriv (u : ℂ)).re) y := by
      change airyLaplace (fun u => (B₁ (u : ℂ) - (α : ℂ) * airySeedG1Deriv (u : ℂ)).re) y = _
      rw [airyLaplace_sub_re hB₁_cl (airySeedG1Deriv_inAiryClass.smul α) hy0,
        airyLaplace_smul_re airySeedG1Deriv_inAiryClass α hy0]
    rw [hlin]
    have h1 := hB₁_lap y hy0
    have h2 := mul_le_mul_of_nonneg_left (hg1_lap_ub y hy0) hα_pos.le
    have h3 : α * (C_J1 * (1 + y) ^ (-(5 / 2 : ℝ))) ≤
        (c_B / 2) * (1 + y) ^ (-(5 / 2 : ℝ)) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hα_CJ1 (by positivity)
    linarith
  have hR_int_pos : 0 < ∫ u : ℝ, (R (u : ℂ)).re := by
    rw [← airyLaplace_zero_eq_integral]
    have h0 := hR_lap 0 le_rfl
    have hp : 0 < (c_B / 2) * (1 + (0 : ℝ)) ^ (-(5 / 2 : ℝ)) := by positivity
    linarith
  -- 4. Strict negativity `(R (u : ℂ)).re < 0` on `(-∞, d₀]`
  have hR_re : ∀ u : ℝ,
      (R (u : ℂ)).re = (u - d₀) * (airySeedG 0 (u : ℂ)).re - α * (airySeedG1Deriv (u : ℂ)).re := by
    intro u
    dsimp [R]
    rw [hB₁_re u, Complex.re_ofReal_mul]
  have hR_neg_ray : ∀ u : ℝ, u ≤ d₀ → (R (u : ℂ)).re < 0 := by
    intro u hu
    rw [hR_re u]
    rcases hu.eq_or_lt with rfl | hlt
    · simp only [sub_self, zero_mul, zero_sub]
      nlinarith
    · have hterm1 : (u - d₀) * (airySeedG 0 (u : ℂ)).re ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) (airySeedG_re_nonneg 0 u)
      have hterm2 : 0 ≤ α * (airySeedG1Deriv (u : ℂ)).re :=
        mul_nonneg hα_pos.le (airySeedG1Deriv_re_nonneg u)
      by_contra hge
      push Not at hge
      have hg0 : (airySeedG 0 (u : ℂ)).re = 0 := by
        have hprod0 : (u - d₀) * (airySeedG 0 (u : ℂ)).re = 0 := by linarith
        exact (mul_eq_zero.mp hprod0).resolve_left (by linarith)
      have hg1_0 : (airySeedG1Deriv (u : ℂ)).re = 0 := by
        have hprod0 : α * (airySeedG1Deriv (u : ℂ)).re = 0 := by linarith
        exact (mul_eq_zero.mp hprod0).resolve_left hα_pos.ne'
      have hu_ne_z0 : u ≠ airyZ 0 := by linarith
      rw [airySeedG_re_of_ne 0 hu_ne_z0] at hg0
      have hAi_sq0 : airyAi u ^ 2 = 0 :=
        (div_eq_zero_iff.mp hg0).resolve_right (pow_ne_zero 2 (sub_ne_zero.mpr hu_ne_z0))
      have hAi0 : airyAi u = 0 := sq_eq_zero_iff.mp hAi_sq0
      have hAiC0 : airyAiC (u : ℂ) = 0 := by rw [airyAiC_ofReal, hAi0, Complex.ofReal_zero]
      obtain ⟨k, hk1, hkz⟩ := (airyAiC_eq_zero_iff (u : ℂ)).mp hAiC0
      have hu_z : u = airyZ (k - 1) := by
        have hreal := Complex.ofReal_injective hkz
        rw [hreal]; unfold airyZ; rw [Nat.sub_add_cancel hk1]
      have hAi'_ne : airyAi' u ≠ 0 := hu_z ▸ airyAi'_airyZ_ne_zero (k - 1)
      have hu_ne_a1' : u ≠ airyDerivFirstZero := fun heq =>
        hAi'_ne (heq ▸ airyDerivFirstZero_spec.2.2)
      rw [airySeedG1Deriv_re_of_ne hu_ne_a1'] at hg1_0
      have hdiv0 := sq_eq_zero_iff.mp hg1_0
      exact hAi'_ne ((div_eq_zero_iff.mp hdiv0).resolve_right (sub_ne_zero.mpr hu_ne_a1'))
  -- 5. WKB asymptotic floor on `(-∞, -X₀]` + compact floor on `[-X₀, d₀]`
  have hnegR_coeffs : HasGenRationalAiryCoeffs (fun z => -R z) 1 α := by
    simpa using hR_coeffs.neg
  obtain ⟨R₀, K, hR₀_ge5, hK_nn, hwkb⟩ := hnegR_coeffs.neg_axis_wkb
  set X₀ : ℝ := max (max R₀ (-d₀ + 1)) (((2 * K + 1) / α) ^ 2 + 1)
  have hX₀_ge5 : 5 ≤ X₀ := hR₀_ge5.trans ((le_max_left _ _).trans (le_max_left _ _))
  have hfar_floor : ∀ u : ℝ, u ≤ -X₀ →
      (α / (2 * π)) * (1 + |u|) ^ (-(3 / 2 : ℝ)) ≤ -(R (u : ℂ)).re := by
    intro u hu
    set x : ℝ := -u
    have hx_ge : X₀ ≤ x := by dsimp [x]; linarith
    have hx_pos : 0 < x := by linarith [hX₀_ge5]
    have hx_R₀ : R₀ ≤ x := ((le_max_left _ _).trans (le_max_left _ _)).trans hx_ge
    have hw := hwkb x hx_R₀
    have htrig : α ≤ 1 * Real.sin (cohnTheta x) ^ 2 + α * Real.cos (cohnTheta x) ^ 2 := by
      have hsc : Real.sin (cohnTheta x) ^ 2 + Real.cos (cohnTheta x) ^ 2 = 1 :=
        Real.sin_sq_add_cos_sq (cohnTheta x)
      have hα_le1 : α ≤ 1 := hα_le_half.trans (by norm_num)
      nlinarith [sq_nonneg (Real.sin (cohnTheta x))]
    have herr_le : K * x ^ (-(1 / 2 : ℝ)) ≤ α / 2 := by
      have hx_sqrt_sq : ((2 * K + 1) / α) ^ 2 ≤ x := by
        have h := (le_max_right _ _).trans hx_ge
        linarith
      have hsqrt_ge : (2 * K + 1) / α ≤ Real.sqrt x := Real.le_sqrt_of_sq_le hx_sqrt_sq
      have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx_pos
      have hrpow_inv : x ^ (-(1 / 2 : ℝ)) = (Real.sqrt x)⁻¹ := by
        rw [Real.rpow_neg hx_pos.le, ← Real.sqrt_eq_rpow]
      rw [hrpow_inv, ← div_eq_mul_inv, div_le_iff₀ hsqrt_pos]
      have hmul := (div_le_iff₀ hα_pos).mp hsqrt_ge
      nlinarith
    have hneg_re : (-(R ((-x : ℝ) : ℂ))).re = -(R (u : ℂ)).re := by
      have hux : ((-x : ℝ) : ℂ) = (u : ℂ) := by dsimp [x]; push_cast; ring
      rw [hux, Complex.neg_re]
    have hpi_lb : α / 2 ≤ π * x ^ (3 / 2 : ℝ) * -(R (u : ℂ)).re := by
      have habs := (abs_le.mp hw).1
      rw [hneg_re] at habs
      linarith
    have hx_pos32 : 0 < π * x ^ (3 / 2 : ℝ) := mul_pos Real.pi_pos (Real.rpow_pos_of_pos hx_pos _)
    have hpt_x : (α / (2 * π)) * x ^ (-(3 / 2 : ℝ)) ≤ -(R (u : ℂ)).re := by
      rw [Real.rpow_neg hx_pos.le, ← div_eq_mul_inv]
      have hden_pos : 0 < 2 * π * x ^ (3 / 2 : ℝ) := mul_pos (by positivity) (Real.rpow_pos_of_pos hx_pos _)
      have hlhs : (α / (2 * π)) / x ^ (3 / 2 : ℝ) = α / (2 * π * x ^ (3 / 2 : ℝ)) := by
        rw [div_div, mul_assoc]
      rw [hlhs, div_le_iff₀ hden_pos]
      linarith
    have h1x_le : (1 + |u|) ^ (-(3 / 2 : ℝ)) ≤ x ^ (-(3 / 2 : ℝ)) := by
      have habs_u : |u| = x := by dsimp [x]; rw [abs_of_neg (by linarith)]
      rw [habs_u]
      exact Real.rpow_le_rpow_of_nonpos hx_pos (by linarith) (by norm_num)
    exact (mul_le_mul_of_nonneg_left h1x_le (by positivity)).trans hpt_x
  have hcont_w : ContinuousOn
      (fun u : ℝ => (1 + |u|) ^ (3 / 2 : ℝ) * -(R (u : ℂ)).re) (Icc (-X₀) d₀) := by
    refine Continuous.continuousOn ?_
    refine (Continuous.rpow_const (continuous_const.add continuous_abs)
      (fun _ => Or.inr (by norm_num))).mul ?_
    exact (Complex.continuous_re.comp (hR_rat.inAiryClass.1.continuous.comp Complex.continuous_ofReal)).neg
  obtain ⟨m_mid, hm_mid_pos, hm_mid⟩ := exists_pos_lower_bound_on_compact isCompact_Icc hcont_w
    (fun u hu => mul_pos (Real.rpow_pos_of_pos (by positivity) _) (neg_pos.mpr (hR_neg_ray u hu.2)))
  set c_R : ℝ := min (α / (2 * π)) m_mid
  have hc_R_pos : 0 < c_R := lt_min (by positivity) hm_mid_pos
  refine ⟨R, hR_rat, hR_int_pos, hR_bplus, ⟨c_R, hc_R_pos, fun u hu => ?_⟩,
    ⟨c_B / 2, by positivity, hR_lap⟩⟩
  by_cases huX : u ≤ -X₀
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)).trans (hfar_floor u huX)
  · push Not at huX
    have hmid := hm_mid u ⟨huX.le, hu⟩
    have hrpow_inv : (1 + |u|) ^ (3 / 2 : ℝ) * (1 + |u|) ^ (-(3 / 2 : ℝ)) = 1 := by
      rw [← Real.rpow_add (by positivity : 0 < 1 + |u|)]; norm_num
    calc c_R * (1 + |u|) ^ (-(3 / 2 : ℝ))
        ≤ m_mid * (1 + |u|) ^ (-(3 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      _ ≤ ((1 + |u|) ^ (3 / 2 : ℝ) * -(R (u : ℂ)).re) * (1 + |u|) ^ (-(3 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right hmid (by positivity)
      _ = -(R (u : ℂ)).re * ((1 + |u|) ^ (3 / 2 : ℝ) * (1 + |u|) ^ (-(3 / 2 : ℝ))) := by ring
      _ = -(R (u : ℂ)).re := by rw [hrpow_inv, mul_one]

/-- Small-`y` `√y` Laplace growth from a negative-axis `(1 + |u|)^{-3/2}` floor
(`ce_airy_lp_proofs.tex` lines 956–961). -/
private lemma laplace_origin_sqrt_floor {Q : ℂ → ℂ} (hQ : InAiryClass Q)
    {d₀ a_floor : ℝ} (_hd₀_neg : d₀ < 0) (ha_pos : 0 < a_floor)
    (hfloor : ∀ u : ℝ, u ≤ d₀ → a_floor * (1 + |u|) ^ (-(3 / 2 : ℝ)) ≤ -(Q (u : ℂ)).re)
    (hc₀_pos : 0 < ∫ u : ℝ, (Q (u : ℂ)).re) :
    ∃ y₀ A_sqrt : ℝ, 0 < y₀ ∧ 0 < A_sqrt ∧ ∀ y : ℝ, 0 ≤ y → y ≤ y₀ →
      (∫ u : ℝ, (Q (u : ℂ)).re) + A_sqrt * Real.sqrt y ≤
        airyLaplace (fun u => (Q (u : ℂ)).re) y := by
  set c₀ : ℝ := ∫ u : ℝ, (Q (u : ℂ)).re
  set X : ℝ := max 1 (-d₀)
  have hX_ge1 : 1 ≤ X := le_max_left _ _
  have hX_pos : 0 < X := lt_of_lt_of_le zero_lt_one hX_ge1
  have hd₀_ge_negX : -X ≤ d₀ := by
    have : -d₀ ≤ X := le_max_right _ _
    linarith
  have hQ_int : Integrable (fun u : ℝ => (Q (u : ℂ)).re) := hQ.2.1.re
  have hQ_abs_int : Integrable (fun u : ℝ => |(Q (u : ℂ)).re|) := hQ_int.abs
  have hQ_exp2_int : Integrable (fun u : ℝ => |(Q (u : ℂ)).re * Real.exp (2 * u)|) :=
    (hQ.integrable_exp_nonneg (by norm_num : (0 : ℝ) ≤ 2)).abs
  set I_mid : ℝ := ∫ u : ℝ, |(Q (u : ℂ)).re|
  set I_pos : ℝ := ∫ u : ℝ, |(Q (u : ℂ)).re * Real.exp (2 * u)|
  have hI_mid_nn : 0 ≤ I_mid := integral_nonneg fun _ => abs_nonneg _
  have hI_pos_nn : 0 ≤ I_pos := integral_nonneg fun _ => abs_nonneg _
  set A₁ : ℝ := a_floor / 16
  have hA₁_pos : 0 < A₁ := by positivity
  set C_lin : ℝ := X * I_mid + I_pos
  have hC_lin_nn : 0 ≤ C_lin := by positivity
  set s_cap : ℝ := A₁ / (8 * (C_lin + c₀ + 1))
  have hs_cap_pos : 0 < s_cap := by positivity
  set y₀ : ℝ := min (min (1 / (2 * X)) (1 / 8)) (s_cap ^ 2)
  have hy₀_pos : 0 < y₀ := lt_min (lt_min (by positivity) (by norm_num)) (sq_pos_of_pos hs_cap_pos)
  refine ⟨y₀, A₁ / 2, hy₀_pos, by positivity, fun y hy0 hy_hi => ?_⟩
  rcases hy0.eq_or_lt with rfl | hy_pos
  · rw [Real.sqrt_zero, mul_zero, add_zero, airyLaplace_zero_eq_integral]
  · have hy_2X : y ≤ 1 / (2 * X) := (hy_hi.trans (min_le_left _ _)).trans (min_le_left _ _)
    have hy_eighth : y ≤ 1 / 8 := (hy_hi.trans (min_le_left _ _)).trans (min_le_right _ _)
    have hy_sq : y ≤ s_cap ^ 2 := hy_hi.trans (min_le_right _ _)
    have hsqrt_le : Real.sqrt y ≤ s_cap :=
      (Real.sqrt_le_sqrt hy_sq).trans_eq (Real.sqrt_sq hs_cap_pos.le)
    let g : ℝ → ℝ := fun u => (Q (u : ℂ)).re * (Real.exp (y * u) - 1)
    have hg_eq : ∀ u : ℝ, g u = (Q (u : ℂ)).re * Real.exp (y * u) - (Q (u : ℂ)).re := by
      intro u; dsimp [g]; ring
    have hg_int : Integrable g := by
      rw [funext hg_eq]
      exact (hQ.integrable_exp_nonneg hy_pos.le).sub hQ_int
    have hL_diff : (∫ u : ℝ, (Q (u : ℂ)).re * Real.exp (y * u)) - c₀ = ∫ u : ℝ, g u := by
      dsimp [c₀]
      rw [← integral_sub (hQ.integrable_exp_nonneg hy_pos.le) hQ_int]
      exact integral_congr_ae (Eventually.of_forall fun u => (hg_eq u).symm)
    have h_left : A₁ * Real.sqrt y ≤ ∫ u in Iic (-X), g u := by
      have hg_nn_left : ∀ u ∈ Iic (-X), 0 ≤ g u := by
        intro u (hu : u ≤ -X)
        have hQu : (Q (u : ℂ)).re ≤ 0 := by
          have hf := hfloor u (hu.trans hd₀_ge_negX)
          have hp : 0 ≤ a_floor * (1 + |u|) ^ (-(3 / 2 : ℝ)) := by positivity
          linarith
        have hexp_le1 : Real.exp (y * u) - 1 ≤ 0 := by
          have : Real.exp (y * u) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
          linarith
        exact mul_nonneg_of_nonpos_of_nonpos hQu hexp_le1
      have hsub_Iic : Ioc (-2 / y) (-1 / y) ⊆ Iic (-X) := by
        intro u hu
        change u ≤ -X
        have h1 : X ≤ 1 / (2 * y) := by
          have hm := (le_div_iff₀ (by positivity : 0 < 2 * X)).mp hy_2X
          rw [le_div_iff₀ (by positivity : 0 < 2 * y)]
          linarith
        have h2 : 1 / (2 * y) ≤ 1 / y :=
          one_div_le_one_div_of_le hy_pos (by linarith)
        have h3 : -1 / y = -(1 / y) := neg_div _ _
        linarith [hu.2]
      have hmono_set : (∫ u in Ioc (-2 / y) (-1 / y), g u) ≤ ∫ u in Iic (-X), g u :=
        setIntegral_mono_set hg_int.integrableOn
          (ae_restrict_of_forall_mem measurableSet_Iic hg_nn_left)
          (Eventually.of_forall hsub_Iic)
      have hpt_box : ∀ u ∈ Ioc (-2 / y) (-1 / y), A₁ * y ^ (3 / 2 : ℝ) ≤ g u := by
        intro u ⟨hu_lo, hu_hi⟩
        have hu_negX : u ≤ -X := hsub_Iic ⟨hu_lo, hu_hi⟩
        have hQu_lb := hfloor u (hu_negX.trans hd₀_ge_negX)
        have hexp_half : 1 / 2 ≤ 1 - Real.exp (y * u) := by
          have hyu : y * u ≤ -1 := by
            have hm := (le_div_iff₀ hy_pos).mp (by linarith : u ≤ -1 / y)
            linarith
          have he1 : Real.exp (y * u) ≤ Real.exp (-1) := Real.exp_le_exp.mpr hyu
          have he_inv : Real.exp (-1) ≤ 1 / 2 := by
            rw [Real.exp_neg, inv_eq_one_div]
            exact one_div_le_one_div_of_le (by norm_num) (by linarith [Real.add_one_le_exp 1])
          linarith
        have h1u_le : 1 + |u| ≤ 4 / y := by
          have hu_neg : u < 0 := by linarith
          rw [abs_of_neg hu_neg]
          have h1 : -u < 2 / y := by
            have : -2 / y < u := hu_lo
            have hneg_eq : -2 / y = -(2 / y) := neg_div _ _
            linarith
          have h2 : (1 : ℝ) ≤ 2 / y := by rw [le_div_iff₀ hy_pos]; linarith
          have h24 : 2 / y + 2 / y = 4 / y := by ring
          linarith
        have hrpow_box : (1 / 8 : ℝ) * y ^ (3 / 2 : ℝ) ≤ (1 + |u|) ^ (-(3 / 2 : ℝ)) := by
          have h1 : (4 / y) ^ (-(3 / 2 : ℝ)) ≤ (1 + |u|) ^ (-(3 / 2 : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) h1u_le (by norm_num)
          have h2 : (4 / y) ^ (-(3 / 2 : ℝ)) = (1 / 8 : ℝ) * y ^ (3 / 2 : ℝ) := by
            rw [div_eq_mul_inv, Real.mul_rpow (by norm_num) (inv_nonneg.mpr hy_pos.le),
              Real.inv_rpow hy_pos.le, ← Real.rpow_neg hy_pos.le, neg_neg]
            have h4 : (4 : ℝ) ^ (-(3 / 2 : ℝ)) = 1 / 8 := by
              rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
              norm_num
            rw [h4]
          rwa [h2] at h1
        have hg_pos_form : g u = (-(Q (u : ℂ)).re) * (1 - Real.exp (y * u)) := by
          dsimp [g]; ring
        rw [hg_pos_form]
        calc A₁ * y ^ (3 / 2 : ℝ)
            = (a_floor * ((1 / 8 : ℝ) * y ^ (3 / 2 : ℝ))) * (1 / 2) := by dsimp [A₁]; ring
          _ ≤ (-(Q (u : ℂ)).re) * (1 - Real.exp (y * u)) :=
              mul_le_mul
                ((mul_le_mul_of_nonneg_left hrpow_box ha_pos.le).trans hQu_lb)
                hexp_half (by norm_num)
                (le_trans (by positivity) hQu_lb)
      have hbox_lb : A₁ * Real.sqrt y ≤ ∫ u in Ioc (-2 / y) (-1 / y), g u := by
        have hconst := setIntegral_mono_on
          (continuousOn_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
          hg_int.integrableOn measurableSet_Ioc hpt_box
        have hlen : (-1 / y) - (-2 / y) = 1 / y := by ring
        rw [setIntegral_const, Real.volume_real_Ioc_of_le (by
            have : 1 / y ≤ 2 / y := div_le_div_of_nonneg_right (by norm_num) hy_pos.le
            rw [neg_div, neg_div]
            linarith), smul_eq_mul, hlen] at hconst
        have hy_alg : (1 / y) * (A₁ * y ^ (3 / 2 : ℝ)) = A₁ * Real.sqrt y := by
          rw [Real.sqrt_eq_rpow]
          have h1 : y ^ (3 / 2 : ℝ) = y * y ^ (1 / 2 : ℝ) := by
            rw [← Real.rpow_one_add' hy_pos.le (by norm_num)]; norm_num
          rw [h1]
          field_simp [hy_pos.ne']
        rwa [hy_alg] at hconst
      exact hbox_lb.trans hmono_set
    have h_mid : -(y * X * I_mid) ≤ ∫ u in Ioc (-X) 0, g u := by
      have h1 : (∫ u in Ioc (-X) 0, -g u) ≤ ∫ u in Ioc (-X) 0, (y * X) * |(Q (u : ℂ)).re| := by
        refine setIntegral_mono_on hg_int.neg.integrableOn
          (hQ_abs_int.const_mul (y * X)).integrableOn measurableSet_Ioc fun u hu => ?_
        have hyu_le0 : y * u ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hy_pos.le hu.2
        have hexp_lb := Real.add_one_le_exp (y * u)
        have hdiff_ub : |Real.exp (y * u) - 1| ≤ y * X := by
          rw [abs_of_nonpos (by linarith [Real.exp_le_one_iff.mpr hyu_le0])]
          nlinarith [hu.1]
        calc -g u ≤ |g u| := neg_le_abs _
          _ = |(Q (u : ℂ)).re| * |Real.exp (y * u) - 1| := abs_mul _ _
          _ ≤ |(Q (u : ℂ)).re| * (y * X) :=
              mul_le_mul_of_nonneg_left hdiff_ub (abs_nonneg _)
          _ = (y * X) * |(Q (u : ℂ)).re| := mul_comm _ _
      have h2 : (∫ u in Ioc (-X) 0, (y * X) * |(Q (u : ℂ)).re|) ≤ (y * X) * I_mid := by
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left
          (setIntegral_le_integral hQ_abs_int (Eventually.of_forall fun _ => abs_nonneg _))
          (by positivity)
      rw [integral_neg] at h1
      linarith
    have h_right : -(y * I_pos) ≤ ∫ u in Ioi (0 : ℝ), g u := by
      have h1 : (∫ u in Ioi (0 : ℝ), -g u) ≤
          ∫ u in Ioi (0 : ℝ), y * |(Q (u : ℂ)).re * Real.exp (2 * u)| := by
        refine setIntegral_mono_on hg_int.neg.integrableOn
          (hQ_exp2_int.const_mul y).integrableOn measurableSet_Ioi fun u (hu : 0 < u) => ?_
        have hs_pos : 0 < y * u := mul_pos hy_pos hu
        have hexp_diff : Real.exp (y * u) - 1 ≤ (y * u) * Real.exp (y * u) := by
          have hm := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-(y * u)))
            (Real.exp_pos (y * u)).le
          rw [add_mul, one_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero] at hm
          linarith
        have hu_exp : u * Real.exp (y * u) ≤ Real.exp (2 * u) := by
          have hu_le : u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
          have hyu_le : Real.exp (y * u) ≤ Real.exp u :=
            Real.exp_le_exp.mpr (by nlinarith)
          calc u * Real.exp (y * u) ≤ Real.exp u * Real.exp u :=
                mul_le_mul hu_le hyu_le (Real.exp_pos _).le (Real.exp_pos _).le
            _ = Real.exp (2 * u) := by rw [← Real.exp_add]; ring_nf
        have hdiff_ub : |Real.exp (y * u) - 1| ≤ y * Real.exp (2 * u) := by
          rw [abs_of_nonneg (by linarith [Real.one_le_exp hs_pos.le])]
          calc Real.exp (y * u) - 1 ≤ y * (u * Real.exp (y * u)) := by linarith
            _ ≤ y * Real.exp (2 * u) := mul_le_mul_of_nonneg_left hu_exp hy_pos.le
        calc -g u ≤ |g u| := neg_le_abs _
          _ = |(Q (u : ℂ)).re| * |Real.exp (y * u) - 1| := abs_mul _ _
          _ ≤ |(Q (u : ℂ)).re| * (y * Real.exp (2 * u)) :=
              mul_le_mul_of_nonneg_left hdiff_ub (abs_nonneg _)
          _ = y * |(Q (u : ℂ)).re * Real.exp (2 * u)| := by
              rw [abs_mul, abs_of_pos (Real.exp_pos _)]; ring
      have h2 : (∫ u in Ioi (0 : ℝ), y * |(Q (u : ℂ)).re * Real.exp (2 * u)|) ≤ y * I_pos := by
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left
          (setIntegral_le_integral hQ_exp2_int (Eventually.of_forall fun _ => abs_nonneg _))
          hy_pos.le
      rw [integral_neg] at h1
      linarith
    have hsplit_all : (∫ u : ℝ, g u) =
        (∫ u in Iic (-X), g u) + (∫ u in Ioc (-X) 0, g u) + ∫ u in Ioi (0 : ℝ), g u := by
      have hd1 : Disjoint (Iic (0 : ℝ)) (Ioi (0 : ℝ)) :=
        Set.disjoint_left.mpr fun _ h1 h2 => not_lt_of_ge h1 h2
      have hd2 : Disjoint (Iic (-X)) (Ioc (-X) 0) :=
        Set.disjoint_left.mpr fun _ h1 h2 => not_lt_of_ge h1 h2.1
      rw [← setIntegral_univ, ← Iic_union_Ioi,
        setIntegral_union hd1 measurableSet_Ioi hg_int.integrableOn hg_int.integrableOn,
        ← Iic_union_Ioc_eq_Iic (by linarith : -X ≤ 0),
        setIntegral_union hd2 measurableSet_Ioc hg_int.integrableOn hg_int.integrableOn]
    have hy_lin_small : (C_lin + c₀ + 1) * Real.sqrt y ≤ A₁ / 8 := by
      have hm := mul_le_mul_of_nonneg_left hsqrt_le (by positivity : 0 ≤ C_lin + c₀ + 1)
      have hrhs : (C_lin + c₀ + 1) * s_cap = A₁ / 8 := by
        dsimp [s_cap]
        have hden : 8 * (C_lin + c₀ + 1) ≠ 0 := by positivity
        field_simp [hden]
      rwa [hrhs] at hm
    have hy_eq_sq : y = Real.sqrt y * Real.sqrt y := (Real.mul_self_sqrt hy_pos.le).symm
    have hClin_y : C_lin * y ≤ (A₁ / 8) * Real.sqrt y := by
      conv_lhs => rw [hy_eq_sq]
      rw [← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg y)
      nlinarith [Real.sqrt_nonneg y, hc₀_pos]
    have hc₀_y : c₀ * y ≤ (A₁ / 8) * Real.sqrt y := by
      conv_lhs => rw [hy_eq_sq]
      rw [← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg y)
      nlinarith [Real.sqrt_nonneg y, hC_lin_nn]
    have hA_y : (7 * A₁ / 8) * y * Real.sqrt y ≤ (A₁ / 8) * Real.sqrt y := by
      refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg y)
      nlinarith [hA₁_pos, hy_eighth]
    have hL_lb : c₀ + (7 * A₁ / 8) * Real.sqrt y ≤
        ∫ u : ℝ, (Q (u : ℂ)).re * Real.exp (y * u) := by
      have h1 : c₀ + A₁ * Real.sqrt y - C_lin * y ≤
          ∫ u : ℝ, (Q (u : ℂ)).re * Real.exp (y * u) := by
        dsimp [C_lin]
        linarith [hL_diff, hsplit_all, h_left, h_mid, h_right]
      linarith
    have hexp_twist : 1 - y ≤ Real.exp (-(y ^ 3) / 12) := by
      have h1 := Real.add_one_le_exp (-(y ^ 3) / 12)
      have hy3_le : y ^ 3 / 12 ≤ y := by nlinarith [sq_nonneg y]
      linarith
    unfold airyLaplace
    calc c₀ + (A₁ / 2) * Real.sqrt y
        ≤ (1 - y) * (c₀ + (7 * A₁ / 8) * Real.sqrt y) := by nlinarith
      _ ≤ Real.exp (-(y ^ 3) / 12) * ∫ u : ℝ, (Q (u : ℂ)).re * Real.exp (y * u) :=
          mul_le_mul hexp_twist hL_lb (by positivity) (Real.exp_pos _).le

/-- Step 1 of `thm:al-rational-density` (`ce_airy_lp_proofs.tex` lines 930–945):
regularize and translate `H` to `F ∈ 𝒢 ∩ 𝓢(ℝ)` strictly negative on `S`, nonpositive on
`(-∞, d₀]`, and Laplace-bounded from below by `-η_lap (1 + y)^{-5/2}`. -/
private lemma exists_shifted_smooth_stage {S : Set ℝ} (hS : IsCompact S)
    {v₀ d₀ m_S η_lap : ℝ} {H : ℂ → ℂ}
    (hWit : IsAiryStrictWitness S v₀ H) (hd₀_lt : d₀ < v₀)
    (hm_S_pos : 0 < m_S) (hS_margin : ∀ s ∈ S, (H (s : ℂ)).re ≤ -m_S)
    (hη_pos : 0 < η_lap) :
    ∃ F : ℂ → ℂ,
      InAiryClass F ∧
      (∀ u : ℝ, (F (u : ℂ)).im = 0) ∧
      (∃ S_F : SchwartzMap ℝ ℝ, ∀ u : ℝ, S_F u = (F (u : ℂ)).re) ∧
      (∀ s ∈ S, (F (s : ℂ)).re ≤ -(3 * m_S / 4)) ∧
      (∀ u : ℝ, u ≤ d₀ → (F (u : ℂ)).re ≤ 0) ∧
      (∀ y : ℝ, 0 ≤ y →
        -η_lap * (1 + y) ^ (-(5 / 2 : ℝ)) ≤ airyLaplace (fun u => (F (u : ℂ)).re) y) := by
  have hH_cl : InAiryClass H := hWit.1.1
  -- 1. Uniform continuity on a compact box enclosing `S` to choose positive translation `s_shift`
  obtain ⟨R_S, hSR⟩ := hS.isBounded.subset_closedBall (0 : ℝ)
  set B_S : ℝ := max R_S 0 + 1
  have hH_re_cont : Continuous (fun x : ℝ => (H (x : ℂ)).re) :=
    Complex.continuous_re.comp (hH_cl.1.continuous.comp Complex.continuous_ofReal)
  have hunif_box : UniformContinuousOn (fun x : ℝ => (H (x : ℂ)).re) (Icc (-B_S - 1) (B_S + 1)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hH_re_cont.continuousOn
  obtain ⟨δ_u, hδ_u_pos, hδ_u⟩ :=
    Metric.uniformContinuousOn_iff.mp hunif_box (m_S / 8) (by positivity)
  set s_shift : ℝ := min ((v₀ - d₀) / 2) (min (1 / 2) (δ_u / 2))
  have hs_pos : 0 < s_shift := lt_min (by linarith) (lt_min (by norm_num) (by positivity))
  have hs_le_half_gap : s_shift ≤ (v₀ - d₀) / 2 := min_le_left _ _
  have hs_le_half : s_shift ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hs_lt_δu : s_shift < δ_u :=
    lt_of_le_of_lt ((min_le_right _ _).trans (min_le_right _ _)) (half_lt_self hδ_u_pos)
  have hH_shift_sites : ∀ t ∈ S, (H ((t + s_shift : ℝ) : ℂ)).re ≤ -(7 * m_S / 8) := by
    intro t ht
    have ht_norm : |t| ≤ max R_S 0 := by
      have h := hSR ht
      rw [mem_closedBall_zero_iff, Real.norm_eq_abs] at h
      exact h.trans (le_max_left _ _)
    have ht_in : t ∈ Icc (-B_S - 1) (B_S + 1) := by
      obtain ⟨h1, h2⟩ := abs_le.mp ht_norm
      exact ⟨by dsimp [B_S]; linarith, by dsimp [B_S]; linarith⟩
    have hts_in : t + s_shift ∈ Icc (-B_S - 1) (B_S + 1) := by
      obtain ⟨h1, h2⟩ := abs_le.mp ht_norm
      exact ⟨by dsimp [B_S]; linarith, by dsimp [B_S]; linarith⟩
    have hdist_in : dist t (t + s_shift) < δ_u := by
      rw [Real.dist_eq, show t - (t + s_shift) = -s_shift by ring, abs_neg, abs_of_pos hs_pos]
      exact hs_lt_δu
    have hd_val := hδ_u t ht_in (t + s_shift) hts_in hdist_in
    rw [Real.dist_eq] at hd_val
    linarith [hS_margin t ht, (abs_lt.mp hd_val).1]
  -- 2. Invoke `lem_al_smooth` and choose height cutoff `Y_big ≥ 1` independent of `ε`
  obtain ⟨hReg_props, hLocUnif, hWL1, C_H, hC_H_nn, _, hShiftLap⟩ := lem_al_smooth hH_cl
  have hlim_Y : Tendsto (fun y : ℝ =>
      C_H * (1 + y) ^ (5 / 2 : ℝ) * Real.exp (-s_shift * y)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun y : ℝ =>
        C_H * ((2 * y) ^ (5 / 2 : ℝ) * Real.exp (-s_shift * y))) atTop (𝓝 0) := by
      have ha := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (5 / 2 : ℝ) s_shift hs_pos
      have hb := (ha.const_mul ((2 : ℝ) ^ (5 / 2 : ℝ))).const_mul C_H
      rw [mul_zero, mul_zero] at hb
      refine hb.congr' ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy0
      rw [Real.mul_rpow (by norm_num) hy0]
      ring
    refine squeeze_zero_norm' ?_ h1
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy1
    rw [Real.norm_of_nonneg (by positivity), mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hC_H_nn
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)) (Real.exp_pos _).le
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp (hlim_Y.eventually (gt_mem_nhds hη_pos))
  set Y_big : ℝ := max Y₀ 1
  -- 3. Choose `ε > 0` small in `𝓝[>] 0`
  set η_small : ℝ := η_lap * (1 + Y_big) ^ (-(5 / 2 : ℝ))
  have hη_small_pos : 0 < η_small := mul_pos hη_pos (Real.rpow_pos_of_pos (by positivity) _)
  let K_C : Set ℂ := (fun t : ℝ => ((t + s_shift : ℝ) : ℂ)) '' S
  have hK_C : IsCompact K_C :=
    hS.image (Complex.continuous_ofReal.comp (continuous_id'.add continuous_const))
  have hev_K : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ z ∈ K_C, dist (H z) (airySmoothReg H ε z) < m_S / 8 := by
    have hU_mem : {p : ℂ × ℂ | dist p.1 p.2 < m_S / 8} ∈ uniformity ℂ :=
      Metric.dist_mem_uniformity (by positivity)
    choose U hU_nhds hU_ev using fun z : ℂ => hLocUnif _ hU_mem z
    obtain ⟨t, _, ht_cover⟩ := hK_C.elim_nhds_subcover U (fun z _ => hU_nhds z)
    have hall : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ x ∈ t, ∀ y ∈ U x, dist (H y) (airySmoothReg H ε y) < m_S / 8 :=
      t.eventually_all.mpr fun x _ => hU_ev x
    filter_upwards [hall] with ε hε z hz
    obtain ⟨x, hx_t, hz_Ux⟩ := Set.mem_iUnion₂.mp (ht_cover hz)
    exact hε x hx_t z hz_Ux
  have hev_L1 := (Metric.tendsto_nhds.mp (hWL1 Y_big (le_trans zero_le_one (le_max_right Y₀ 1)))
    η_small hη_small_pos)
  set ε_cap : ℝ := min 1 ((v₀ - d₀ - s_shift) / 2)
  have hε_cap_pos : 0 < ε_cap := lt_min zero_lt_one (by linarith)
  have hev_Ioc : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioc 0 ε_cap :=
    Filter.eventually_of_mem (Ioc_mem_nhdsGT hε_cap_pos) fun _ h => h
  obtain ⟨ε, ⟨⟨hε_mem, hε_K⟩, hε_L1⟩⟩ :=
    ((hev_Ioc.and hev_K).and hev_L1).exists
  have hε_pos : 0 < ε := hε_mem.1
  have hε_le1 : ε ≤ 1 := hε_mem.2.trans (min_le_left _ _)
  have hε_gap : d₀ + s_shift + 2 * ε ≤ v₀ := by
    have h := hε_mem.2.trans (min_le_right _ _)
    linarith
  obtain ⟨_, hMSq_real, _, _, hReg_cl, _, ⟨S_ε, hS_ε⟩⟩ := hReg_props ε ⟨hε_pos, hε_le1⟩
  let F : ℂ → ℂ := fun z => airySmoothReg H ε (z + (s_shift : ℂ))
  have hF_cl : InAiryClass F := inAiryClass_shift_nonneg hReg_cl hs_pos.le
  obtain ⟨S_F, hS_F⟩ := schwartz_shift S_ε s_shift
  have hF_ofReal : ∀ u : ℝ, F (u : ℂ) = airySmoothReg H ε ((u + s_shift : ℝ) : ℂ) := fun u => by
    dsimp [F]
    have hc : (u : ℂ) + (s_shift : ℂ) = ((u + s_shift : ℝ) : ℂ) := by push_cast; rfl
    rw [hc]
  refine ⟨F, hF_cl, hF_cl.2.2.2, ⟨S_F, fun u => by rw [hS_F u, hS_ε (u + s_shift), hF_ofReal u]⟩,
    ?_, ?_, ?_⟩
  · -- Strict margin on `S`
    intro t ht
    rw [hF_ofReal t]
    have hmem_K : ((t + s_shift : ℝ) : ℂ) ∈ K_C := ⟨t, ht, rfl⟩
    have hd := hε_K ((t + s_shift : ℝ) : ℂ) hmem_K
    rw [Complex.dist_eq] at hd
    have hre_diff : |(airySmoothReg H ε ((t + s_shift : ℝ) : ℂ)).re -
        (H ((t + s_shift : ℝ) : ℂ)).re| < m_S / 8 := by
      rw [abs_sub_comm, ← Complex.sub_re]
      exact (Complex.abs_re_le_norm _).trans_lt hd
    linarith [hH_shift_sites t ht, (abs_lt.mp hre_diff).2]
  · -- Nonpositivity on `(-∞, d₀]`
    intro u hu
    rw [hF_ofReal u]
    unfold airySmoothReg
    have hc : ((u + s_shift : ℝ) : ℂ) + ((2 * ε : ℝ) : ℂ) =
        ((u + s_shift + 2 * ε : ℝ) : ℂ) := by push_cast; ring
    rw [hc, Complex.mul_re, (hMSq_real (u + s_shift)).1,
      hH_cl.2.2.2 (u + s_shift + 2 * ε), mul_zero, sub_zero]
    exact mul_nonpos_of_nonneg_of_nonpos (hMSq_real (u + s_shift)).2
      (hWit.1.2.2.2.1 (u + s_shift + 2 * ε) (by linarith))
  · -- Laplace lower bound `-η_lap (1 + y)^{-5/2}` for all `y ≥ 0`
    intro y hy0
    have hF_re_eq : (fun u : ℝ => (F (u : ℂ)).re) =
        fun u : ℝ => (airySmoothReg H ε ((u + s_shift : ℝ) : ℂ)).re :=
      funext fun u => congrArg Complex.re (hF_ofReal u)
    rw [hF_re_eq]
    by_cases hy_big : Y_big ≤ y
    · have hsh := hShiftLap s_shift hs_pos ε ⟨hε_pos, hε_le1⟩ y hy0
      have hyY₀ : Y₀ ≤ y := (le_max_left _ _).trans hy_big
      have hlt := hY₀ y hyY₀
      have h1y_neg_pos : 0 < (1 + y) ^ (-(5 / 2 : ℝ)) := Real.rpow_pos_of_pos (by linarith) _
      have hrpow_inv : (1 + y) ^ (5 / 2 : ℝ) * (1 + y) ^ (-(5 / 2 : ℝ)) = 1 := by
        rw [← Real.rpow_add (by linarith : 0 < 1 + y)]; norm_num
      have hsmall : C_H * Real.exp (-s_shift * y) < η_lap * (1 + y) ^ (-(5 / 2 : ℝ)) := by
        have hm := mul_lt_mul_of_pos_right hlt h1y_neg_pos
        calc C_H * Real.exp (-s_shift * y)
            = C_H * Real.exp (-s_shift * y) *
                ((1 + y) ^ (5 / 2 : ℝ) * (1 + y) ^ (-(5 / 2 : ℝ))) := by rw [hrpow_inv, mul_one]
          _ = (C_H * (1 + y) ^ (5 / 2 : ℝ) * Real.exp (-s_shift * y)) *
                (1 + y) ^ (-(5 / 2 : ℝ)) := by ring
          _ < η_lap * (1 + y) ^ (-(5 / 2 : ℝ)) := hm
      linarith [(abs_le.mp hsh).1]
    · push Not at hy_big
      have hHs_cl : InAiryClass (fun z => H (z + (s_shift : ℂ))) :=
        inAiryClass_shift_nonneg hH_cl hs_pos.le
      have hHs_lap_nn : 0 ≤ airyLaplace (fun u => (H ((u + s_shift : ℝ) : ℂ)).re) y := by
        have hlin : ∀ u : ℝ, (H ((u + s_shift : ℝ) : ℂ)).re * Real.exp (y * u) =
            Real.exp (-s_shift * y) * ((H ((u + s_shift : ℝ) : ℂ)).re *
              Real.exp (y * (u + s_shift))) := by
          intro u
          rw [mul_comm (Real.exp (-s_shift * y)), mul_assoc, ← Real.exp_add]
          congr 2; ring
        have heq : airyLaplace (fun u => (H ((u + s_shift : ℝ) : ℂ)).re) y =
            Real.exp (-s_shift * y) * airyLaplace (fun u => (H (u : ℂ)).re) y := by
          unfold airyLaplace
          simp_rw [hlin]
          rw [integral_const_mul, integral_add_right_eq_self
            (fun w : ℝ => (H (w : ℂ)).re * Real.exp (y * w)) s_shift]
          ring
        rw [heq]
        exact mul_nonneg (Real.exp_pos _).le (hWit.1.2.2.2.2 y hy0)
      have hdiff_ub : |airyLaplace (fun u => (airySmoothReg H ε ((u + s_shift : ℝ) : ℂ)).re) y -
          airyLaplace (fun u => (H ((u + s_shift : ℝ) : ℂ)).re) y| < η_small := by
        have hint1 : Integrable (fun u : ℝ =>
            (airySmoothReg H ε ((u + s_shift : ℝ) : ℂ)).re * Real.exp (y * u)) :=
          (hF_cl.integrable_exp_nonneg hy0).congr (Eventually.of_forall fun u => by
            dsimp only; rw [hF_ofReal u])
        have hint2 : Integrable (fun u : ℝ =>
            (H ((u + s_shift : ℝ) : ℂ)).re * Real.exp (y * u)) :=
          (hHs_cl.integrable_exp_nonneg hy0).congr (Eventually.of_forall fun u => by
            dsimp only
            have hc : (u : ℂ) + (s_shift : ℂ) = ((u + s_shift : ℝ) : ℂ) := by push_cast; rfl
            rw [hc])
        unfold airyLaplace
        rw [← mul_sub, ← integral_sub hint1 hint2, abs_mul, abs_of_pos (Real.exp_pos _)]
        have hexp_le1 : Real.exp (-(y ^ 3) / 12) ≤ 1 :=
          Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
            (neg_nonpos.mpr (by positivity)) (by norm_num))
        have hshift_int : (∫ u : ℝ,
            ((airySmoothReg H ε ((u + s_shift : ℝ) : ℂ)).re * Real.exp (y * u) -
              (H ((u + s_shift : ℝ) : ℂ)).re * Real.exp (y * u))) =
            ∫ w : ℝ, ((airySmoothReg H ε (w : ℂ)).re - (H (w : ℂ)).re) *
              Real.exp (y * (w - s_shift)) := by
          have heq_fn : (fun u : ℝ =>
              (airySmoothReg H ε ((u + s_shift : ℝ) : ℂ)).re * Real.exp (y * u) -
                (H ((u + s_shift : ℝ) : ℂ)).re * Real.exp (y * u)) =
              fun u : ℝ => ((airySmoothReg H ε ((u + s_shift : ℝ) : ℂ)).re -
                (H ((u + s_shift : ℝ) : ℂ)).re) * Real.exp (y * ((u + s_shift) - s_shift)) := by
            ext u; ring_nf
          rw [heq_fn]
          exact integral_add_right_eq_self
            (fun w : ℝ => ((airySmoothReg H ε (w : ℂ)).re - (H (w : ℂ)).re) *
              Real.exp (y * (w - s_shift))) s_shift
        rw [hshift_int]
        have hdom_w : Integrable (fun w : ℝ =>
            ‖airySmoothReg H ε (w : ℂ) - H (w : ℂ)‖ * Real.exp (Y_big * max w 0)) := by
          have hsub_cl : InAiryClass (fun z => airySmoothReg H ε z - H z) := hReg_cl.sub hH_cl
          have hleft : IntegrableOn (fun w : ℝ =>
              ‖airySmoothReg H ε (w : ℂ) - H (w : ℂ)‖ * Real.exp (Y_big * max w 0)) (Iic 0) := by
            refine hsub_cl.2.1.norm.integrableOn.congr_fun (fun w (hw : w ≤ 0) => ?_) measurableSet_Iic
            dsimp only
            rw [max_eq_right hw, mul_zero, Real.exp_zero, mul_one]
          have hright : IntegrableOn (fun w : ℝ =>
              ‖airySmoothReg H ε (w : ℂ) - H (w : ℂ)‖ * Real.exp (Y_big * max w 0)) (Ioi 0) := by
            have hY_nn : 0 ≤ Y_big := le_trans zero_le_one (le_max_right Y₀ 1)
            have hmaj : Integrable (fun w : ℝ =>
                (airySmoothReg H ε (w : ℂ) - H (w : ℂ)).re * Real.exp (Y_big * w)) :=
              hsub_cl.integrable_exp_nonneg hY_nn
            have him0 : ∀ w : ℝ, (airySmoothReg H ε (w : ℂ) - H (w : ℂ)).im = 0 := fun w => by
              rw [Complex.sub_im, hReg_cl.2.2.2 w, hH_cl.2.2.2 w, sub_self]
            refine hmaj.abs.integrableOn.congr_fun (fun w (hw : 0 < w) => ?_) measurableSet_Ioi
            dsimp only
            rw [abs_mul, abs_of_pos (Real.exp_pos _), max_eq_left hw.le]
            congr 1
            have hz : airySmoothReg H ε (w : ℂ) - H (w : ℂ) =
                (((airySmoothReg H ε (w : ℂ) - H (w : ℂ)).re : ℝ) : ℂ) := by
              apply Complex.ext <;> simp [him0 w]
            conv_rhs => rw [hz, Complex.norm_real, Real.norm_eq_abs]
          rw [← integrableOn_univ, ← Iic_union_Ioi]
          exact hleft.union hright
        have hsub_int : Integrable (fun w : ℝ =>
            ((airySmoothReg H ε (w : ℂ)).re - (H (w : ℂ)).re) *
              Real.exp (y * (w - s_shift))) := by
          have hcomp := (hint1.sub hint2).comp_add_right (-s_shift)
          refine hcomp.congr (Eventually.of_forall fun w => ?_)
          dsimp only [Pi.sub_apply]
          have hws : w + -s_shift + s_shift = w := by ring
          have hws' : w + -s_shift = w - s_shift := by ring
          rw [hws, hws']
          ring
        have habs_int_le : |∫ w : ℝ, ((airySmoothReg H ε (w : ℂ)).re - (H (w : ℂ)).re) *
            Real.exp (y * (w - s_shift))| ≤
            ∫ w : ℝ, ‖airySmoothReg H ε (w : ℂ) - H (w : ℂ)‖ * Real.exp (Y_big * max w 0) := by
          refine abs_integral_le_integral_abs.trans (integral_mono hsub_int.abs hdom_w fun w => ?_)
          rw [abs_mul, abs_of_pos (Real.exp_pos _), ← Complex.sub_re]
          have hexp_le : Real.exp (y * (w - s_shift)) ≤ Real.exp (Y_big * max w 0) := by
            apply Real.exp_le_exp.mpr
            have h1 : y * (w - s_shift) ≤ y * max w 0 :=
              mul_le_mul_of_nonneg_left ((by linarith : w - s_shift ≤ w).trans (le_max_left w 0)) hy0
            have h2 : y * max w 0 ≤ Y_big * max w 0 :=
              mul_le_mul_of_nonneg_right hy_big.le (le_max_right w 0)
            exact h1.trans h2
          exact mul_le_mul (Complex.abs_re_le_norm _) hexp_le (Real.exp_pos _).le (norm_nonneg _)
        rw [Real.dist_eq, sub_zero, abs_of_nonneg
          (integral_nonneg fun _ => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)] at hε_L1
        calc Real.exp (-(y ^ 3) / 12) *
              |∫ w : ℝ, ((airySmoothReg H ε (w : ℂ)).re - (H (w : ℂ)).re) *
                Real.exp (y * (w - s_shift))|
            ≤ 1 * ∫ w : ℝ, ‖airySmoothReg H ε (w : ℂ) - H (w : ℂ)‖ *
                Real.exp (Y_big * max w 0) :=
              mul_le_mul hexp_le1 habs_int_le (abs_nonneg _) zero_le_one
          _ < η_small := by rw [one_mul]; exact hε_L1
      have hrpow_mono : η_small ≤ η_lap * (1 + y) ^ (-(5 / 2 : ℝ)) := by
        dsimp [η_small]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)) hη_pos.le
      linarith [hHs_lap_nn, (abs_lt.mp hdiff_ub).1, hrpow_mono]

/-! ### Section 3: Main Density Theorem (`thm:al-rational-density`) and Conditional Transfer -/

/-- **Theorem `thm:al-rational-density`** (`ce_airy_lp_proofs.tex` lines 893–969):
for any compact set `S ⊆ ℝ` (possibly empty) and strict-site witness `H ∈ 𝒢` at cutoff `v₀`,
`v₀ ≤ a₁`, and for every `v < v₀` there exist a strict cutoff `d₀ ∈ (v, v₀)` and
`H₀ ∈ ℛ_{\mathrm{Ai}}^{\mathrm{gen}}` satisfying `(a)`–`(c)` of `thm:ce-shifted-lift` with strict
ray floor and strict Laplace positivity (`IsAiryStrictLiftSeed S d₀ H₀`). -/
theorem thm_al_rational_density {S : Set ℝ} (hS : IsCompact S)
    {v₀ : ℝ} {H : ℂ → ℂ} (hWit : IsAiryStrictWitness S v₀ H) :
    v₀ ≤ airyZ 0 ∧
    ∀ v : ℝ, v < v₀ → ∃ d₀ ∈ Ioo v v₀, ∃ H₀ : ℂ → ℂ, IsAiryStrictLiftSeed S d₀ H₀ := by
  have hv₀_le : v₀ ≤ airyZ 0 := by
    have h1 : (v₀ : EReal) ≤ airyULP S := le_iSup₂_of_le v₀ ⟨H, hWit.1⟩ le_rfl
    exact EReal.coe_le_coe_iff.mp (h1.trans (airyULP_le_airyZ_zero S))
  refine ⟨hv₀_le, fun v hvv₀ => ?_⟩
  -- Cutoff `d₀ ∈ (v, v₀)` with `g_1'(d₀) > 0` and rational buffer `R`
  obtain ⟨d₀, hvd₀, hd₀v₀, hg1_pos⟩ := exists_cutoff_airySeedG1Deriv_pos hvv₀
  have hd₀_lt_a1 : d₀ < airyZ 0 := hd₀v₀.trans_le hv₀_le
  have hd₀_neg : d₀ < 0 := hd₀_lt_a1.trans (airyZ_neg 0)
  obtain ⟨R, hR_rat, _, hR_bplus, ⟨c_R, hc_R_pos, hR_floor⟩, ⟨c_L, hc_L_pos, hR_lap⟩⟩ :=
    exists_rational_buffer hd₀_lt_a1 hg1_pos
  -- Compact site margins on `S`
  have hH_neg_cont : ContinuousOn (fun s : ℝ => -(H (s : ℂ)).re) S :=
    (Complex.continuous_re.comp (hWit.1.1.1.continuous.comp Complex.continuous_ofReal)).neg.continuousOn
  obtain ⟨m_S, hm_S_pos, hm_S_lb⟩ := exists_pos_lower_bound_on_compact hS hH_neg_cont
    (fun s hs => neg_pos.mpr (hWit.2 s hs))
  have hS_margin : ∀ s ∈ S, (H (s : ℂ)).re ≤ -m_S := fun s hs => by linarith [hm_S_lb s hs]
  obtain ⟨M_R₀, hM_R₀⟩ := hS.exists_bound_of_continuousOn
    (Complex.continuous_re.comp (hR_rat.inAiryClass.1.continuous.comp Complex.continuous_ofReal)).continuousOn
  set M_R : ℝ := max M_R₀ 1
  have hM_R_pos : 0 < M_R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  set lam : ℝ := m_S / (2 * M_R)
  have hlam_pos : 0 < lam := by positivity
  have hlam_R_sites : ∀ s ∈ S, lam * |(R (s : ℂ)).re| ≤ m_S / 2 := by
    intro s hs
    have hb : |(R (s : ℂ)).re| ≤ M_R := by
      have h := hM_R₀ s hs
      rw [Real.norm_eq_abs] at h
      exact h.trans (le_max_left _ _)
    calc lam * |(R (s : ℂ)).re| ≤ (m_S / (2 * M_R)) * M_R :=
          mul_le_mul_of_nonneg_left hb hlam_pos.le
      _ = m_S / 2 := by field_simp [hM_R_pos.ne']
  -- Step 1: Smooth shifted stage `F ∈ 𝒢 ∩ 𝓢(ℝ)`
  obtain ⟨F, hF_cl, -, hF_sch, hF_sites, hF_ray, hF_lap⟩ :=
    exists_shifted_smooth_stage hS hWit hd₀v₀ hm_S_pos hS_margin
      (by positivity : 0 < (lam * c_L) / 2)
  -- Step 2: Hermite–Airy rational truncation `F_N` (`lem_al_hermite_approx`)
  obtain ⟨_, _, hFN_rat_and_beta, hFN_unif, _, _, hFN_neg, hFN_lap, _, hFN_bplus⟩ :=
    lem_al_hermite_approx hF_cl hF_sch
  have hS_C : IsCompact ((Complex.ofReal) '' S) := hS.image Complex.continuous_ofReal
  have hev_S := Metric.tendstoUniformlyOn_iff.mp (hFN_unif _ hS_C) (m_S / 8) (by positivity)
  have hev_neg := hFN_neg ((lam * c_R) / 2) (by positivity)
  have hev_lap := hFN_lap ((lam * c_L) / 4) (by positivity)
  have hev_bp := Metric.tendsto_nhds.mp hFN_bplus (lam / 4) (by positivity)
  obtain ⟨N, ⟨⟨⟨hN_S, hN_neg⟩, hN_lap⟩, hN_bp⟩⟩ :=
    (hev_S.and hev_neg |>.and hev_lap |>.and hev_bp).exists
  let P_N : ℂ → ℂ := airyHermitePartialSum F N
  have hPN_rat : InGenRationalAiry P_N := (hFN_rat_and_beta N).1
  let Q : ℂ → ℂ := fun z => P_N z + (lam : ℂ) * R z
  have hQ_rat : InGenRationalAiry Q := hPN_rat.add (hR_rat.smul lam)
  have hQ_cl : InAiryClass Q := hQ_rat.inAiryClass
  have hQ_sites : ∀ s ∈ S, (Q (s : ℂ)).re < 0 := by
    intro s hs
    have hd_s := hN_S (s : ℂ) ⟨s, hs, rfl⟩
    rw [Complex.dist_eq] at hd_s
    have hPN_diff : |(P_N (s : ℂ)).re - (F (s : ℂ)).re| < m_S / 8 := by
      rw [abs_sub_comm, ← Complex.sub_re]
      exact (Complex.abs_re_le_norm _).trans_lt hd_s
    have hlamR : lam * (R (s : ℂ)).re ≤ m_S / 2 :=
      (mul_le_mul_of_nonneg_left (le_abs_self _) hlam_pos.le).trans (hlam_R_sites s hs)
    have hQ_re : (Q (s : ℂ)).re = (P_N (s : ℂ)).re + lam * (R (s : ℂ)).re := by
      dsimp [Q]; rw [Complex.re_ofReal_mul]
    rw [hQ_re]
    linarith [hF_sites s hs, (abs_lt.mp hPN_diff).2]
  have hQ_floor : ∀ u : ℝ, u ≤ d₀ →
      ((lam * c_R) / 2) * (1 + |u|) ^ (-(3 / 2 : ℝ)) ≤ -(Q (u : ℂ)).re := by
    intro u hu
    have hu_le0 : u ≤ 0 := hu.trans hd₀_neg.le
    have hneg_u := hN_neg u hu_le0
    have hrpow_pos : 0 < (1 + |u|) ^ (-(3 / 2 : ℝ)) := Real.rpow_pos_of_pos (by positivity) _
    have hrpow_inv : (1 + |u|) ^ (3 / 2 : ℝ) * (1 + |u|) ^ (-(3 / 2 : ℝ)) = 1 := by
      rw [← Real.rpow_add (by positivity : 0 < 1 + |u|)]; norm_num
    have herr_u : |(F (u : ℂ)).re - (P_N (u : ℂ)).re| <
        ((lam * c_R) / 2) * (1 + |u|) ^ (-(3 / 2 : ℝ)) := by
      have hm := mul_lt_mul_of_pos_right hneg_u hrpow_pos
      calc |(F (u : ℂ)).re - (P_N (u : ℂ)).re|
          = |(F (u : ℂ)).re - (P_N (u : ℂ)).re| *
              ((1 + |u|) ^ (3 / 2 : ℝ) * (1 + |u|) ^ (-(3 / 2 : ℝ))) := by rw [hrpow_inv, mul_one]
        _ = ((1 + |u|) ^ (3 / 2 : ℝ) * |(F (u : ℂ)).re - (P_N (u : ℂ)).re|) *
              (1 + |u|) ^ (-(3 / 2 : ℝ)) := by ring
        _ < ((lam * c_R) / 2) * (1 + |u|) ^ (-(3 / 2 : ℝ)) := hm
    have hR_u := mul_le_mul_of_nonneg_left (hR_floor u hu) hlam_pos.le
    have hQ_re : (Q (u : ℂ)).re = (P_N (u : ℂ)).re + lam * (R (u : ℂ)).re := by
      dsimp [Q]; rw [Complex.re_ofReal_mul]
    rw [hQ_re]
    linarith [hF_ray u hu, (abs_lt.mp herr_u).1, hR_u]
  have hQ_lap : ∀ y : ℝ, 0 ≤ y →
      ((lam * c_L) / 4) * (1 + y) ^ (-(5 / 2 : ℝ)) ≤ airyLaplace (fun u => (Q (u : ℂ)).re) y := by
    intro y hy0
    have hlap_y := hN_lap y hy0
    have h1y_neg_pos : 0 < (1 + y) ^ (-(5 / 2 : ℝ)) := Real.rpow_pos_of_pos (by linarith) _
    have hrpow_inv : (1 + y) ^ (5 / 2 : ℝ) * (1 + y) ^ (-(5 / 2 : ℝ)) = 1 := by
      rw [← Real.rpow_add (by linarith : 0 < 1 + y)]; norm_num
    have herr_y : |airyLaplace (fun u => (F (u : ℂ)).re) y -
        airyLaplace (fun u => (P_N (u : ℂ)).re) y| <
        ((lam * c_L) / 4) * (1 + y) ^ (-(5 / 2 : ℝ)) := by
      have hm := mul_lt_mul_of_pos_right hlap_y h1y_neg_pos
      calc |airyLaplace (fun u => (F (u : ℂ)).re) y -
              airyLaplace (fun u => (P_N (u : ℂ)).re) y|
          = |airyLaplace (fun u => (F (u : ℂ)).re) y -
              airyLaplace (fun u => (P_N (u : ℂ)).re) y| *
              ((1 + y) ^ (5 / 2 : ℝ) * (1 + y) ^ (-(5 / 2 : ℝ))) := by rw [hrpow_inv, mul_one]
        _ = ((1 + y) ^ (5 / 2 : ℝ) *
              |airyLaplace (fun u => (F (u : ℂ)).re) y -
                airyLaplace (fun u => (P_N (u : ℂ)).re) y|) *
              (1 + y) ^ (-(5 / 2 : ℝ)) := by ring
        _ < ((lam * c_L) / 4) * (1 + y) ^ (-(5 / 2 : ℝ)) := hm
    have hlin : airyLaplace (fun u => (Q (u : ℂ)).re) y =
        airyLaplace (fun u => (P_N (u : ℂ)).re) y +
          lam * airyLaplace (fun u => (R (u : ℂ)).re) y := by
      change airyLaplace (fun u => (P_N (u : ℂ) + (lam : ℂ) * R (u : ℂ)).re) y = _
      rw [airyLaplace_add_re hPN_rat.inAiryClass (hR_rat.inAiryClass.smul lam) hy0,
        airyLaplace_smul_re hR_rat.inAiryClass lam hy0]
    rw [hlin]
    have hFl := hF_lap y hy0
    have hRl := mul_le_mul_of_nonneg_left (hR_lap y hy0) hlam_pos.le
    have hRl' : lam * c_L * (1 + y) ^ (-(5 / 2 : ℝ)) ≤
        lam * airyLaplace (fun u => (R (u : ℂ)).re) y := by linarith
    linarith [(abs_lt.mp herr_y).2, hFl, hRl']
  have hQ_bplus : 0 < airyBetaPlus Q := by
    have hbp_eq : airyBetaPlus Q = airyBetaPlus P_N + lam * airyBetaPlus R := by
      dsimp [Q]
      rw [airyBetaPlus_add hPN_rat (hR_rat.smul lam), airyBetaPlus_smul hR_rat lam]
    rw [Real.dist_eq, sub_zero] at hN_bp
    have hlam_bp : lam / 2 ≤ lam * airyBetaPlus R := by
      have hm := mul_le_mul_of_nonneg_left hR_bplus hlam_pos.le
      linarith
    rw [hbp_eq]
    linarith [(abs_lt.mp hN_bp).1, hlam_bp]
  -- Step 3: Zero the integral with a far Airy cardinal `g_k` (`lem_al_far_cardinal_laplace`)
  set c₀ : ℝ := ∫ u : ℝ, (Q (u : ℂ)).re
  have hc₀_pos : 0 < c₀ := by
    dsimp [c₀]
    rw [← airyLaplace_zero_eq_integral]
    have h0 := hQ_lap 0 le_rfl
    have hp : 0 < ((lam * c_L) / 4) * (1 + (0 : ℝ)) ^ (-(5 / 2 : ℝ)) := by positivity
    linarith
  obtain ⟨y₀, A_sqrt, hy₀_pos, hA_sqrt_pos, hQ_origin_sqrt⟩ :=
    laplace_origin_sqrt_floor hQ_cl hd₀_neg (by positivity) hQ_floor hc₀_pos
  obtain ⟨hfar_props, hfar_tail⟩ := lem_al_far_cardinal_laplace
  obtain ⟨C_far, hC_far_pos, hfar_ub⟩ := hfar_tail y₀ hy₀_pos
  obtain ⟨k, hk_far⟩ := eventually_atTop.mp
    (eventually_le_neg_airyZ ((8 * c₀ * C_far) / (lam * c_L) + 1))
  have hk_abs : (8 * c₀ * C_far) / (lam * c_L) < |airyZ k| := by
    rw [abs_of_neg (airyZ_neg k)]
    linarith [hk_far k le_rfl]
  obtain ⟨hgk_rat, hgk_nn, hgk_int1, _, hgk_bplus0, hgk_lap_le1⟩ := hfar_props k
  let H₀ : ℂ → ℂ := fun z => Q z - (c₀ : ℂ) * airySeedG k z
  refine ⟨d₀, ⟨hvd₀, hd₀v₀⟩, H₀, ?_⟩
  refine ⟨hQ_rat.sub (hgk_rat.smul c₀), ?_, ?_, ?_, ?_, ?_⟩
  · -- `∫ H₀ = 0`
    have heq : (fun u : ℝ => (H₀ (u : ℂ)).re) =
        fun u : ℝ => (Q (u : ℂ)).re - c₀ * (airySeedG k (u : ℂ)).re := by
      ext u; dsimp [H₀]; rw [Complex.re_ofReal_mul]
    have hQ_re_int : Integrable (fun u : ℝ => (Q (u : ℂ)).re) := hQ_cl.2.1.re
    have hgk_re_int : Integrable (fun u : ℝ => c₀ * (airySeedG k (u : ℂ)).re) :=
      hgk_rat.inAiryClass.2.1.re.const_mul c₀
    rw [heq, integral_sub hQ_re_int hgk_re_int, integral_const_mul, hgk_int1, mul_one]
    dsimp [c₀]; ring
  · -- Strict negativity on `S`
    intro s hs
    dsimp [H₀]
    rw [Complex.re_ofReal_mul]
    have hnn : 0 ≤ c₀ * (airySeedG k (s : ℂ)).re := mul_nonneg hc₀_pos.le (hgk_nn s)
    linarith [hQ_sites s hs]
  · -- Uniform `(1 + |u|)^{-3/2}` floor on `(-∞, d₀]`
    refine ⟨(lam * c_R) / 2, by positivity, fun u hu => ?_⟩
    dsimp [H₀]
    rw [Complex.re_ofReal_mul]
    have hnn : 0 ≤ c₀ * (airySeedG k (u : ℂ)).re := mul_nonneg hc₀_pos.le (hgk_nn u)
    linarith [hQ_floor u hu]
  · -- `0 < airyBetaPlus H₀`
    have hbp : airyBetaPlus H₀ = airyBetaPlus Q - c₀ * airyBetaPlus (airySeedG k) := by
      dsimp [H₀]
      rw [airyBetaPlus_sub hQ_rat (hgk_rat.smul c₀), airyBetaPlus_smul hgk_rat c₀]
    rw [hbp, hgk_bplus0, mul_zero, sub_zero]
    exact hQ_bplus
  · -- Strict Laplace positivity `∀ y > 0, 0 < airyLaplace H₀ y`
    intro y hy_pos
    have hlin : airyLaplace (fun u => (H₀ (u : ℂ)).re) y =
        airyLaplace (fun u => (Q (u : ℂ)).re) y -
          c₀ * airyLaplace (fun u => (airySeedG k (u : ℂ)).re) y := by
      change airyLaplace (fun u => (Q (u : ℂ) - (c₀ : ℂ) * airySeedG k (u : ℂ)).re) y = _
      rw [airyLaplace_sub_re hQ_cl (hgk_rat.inAiryClass.smul c₀) hy_pos.le,
        airyLaplace_smul_re hgk_rat.inAiryClass c₀ hy_pos.le]
    rw [hlin]
    by_cases hy_small : y ≤ y₀
    · have h1 := hQ_origin_sqrt y hy_pos.le hy_small
      have h2 := mul_le_mul_of_nonneg_left (hgk_lap_le1 y hy_pos.le).2 hc₀_pos.le
      have hsqrt_pos : 0 < A_sqrt * Real.sqrt y :=
        mul_pos hA_sqrt_pos (Real.sqrt_pos.mpr hy_pos)
      linarith
    · push Not at hy_small
      have h1 := hQ_lap y hy_pos.le
      have h2 := mul_le_mul_of_nonneg_left (hfar_ub k y hy_small.le) hc₀_pos.le
      have hc_far_small : c₀ * (C_far / |airyZ k|) < (lam * c_L) / 8 := by
        have hA_pos : 0 < |airyZ k| := lt_trans (by positivity) hk_abs
        rw [← mul_div_assoc, div_lt_iff₀ hA_pos]
        have hm := (div_lt_iff₀ (by positivity : 0 < lam * c_L)).mp hk_abs
        linarith
      have h1y_pos : 0 < (1 + y) ^ (-(5 / 2 : ℝ)) := Real.rpow_pos_of_pos (by positivity) _
      have h3 : c₀ * ((C_far / |airyZ k|) * (1 + y) ^ (-(5 / 2 : ℝ))) <
          ((lam * c_L) / 8) * (1 + y) ^ (-(5 / 2 : ℝ)) := by
        rw [← mul_assoc]
        exact mul_lt_mul_of_pos_right hc_far_small h1y_pos
      have hpos_margin : 0 < ((lam * c_L) / 8) * (1 + y) ^ (-(5 / 2 : ℝ)) := by positivity
      linarith

/-- info: 'FormalResearch.SignUncertainty.thm_al_rational_density' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.thm_al_rational_density

/-- Hermite–Biehler shell-site specialization of `thm:al-rational-density`
(`ce_airy_lp_proofs.tex` line 898): for `OneProfileStrictFeasible D v₀` and `v < v₀`, the lift seed
cutoff satisfies `d₀ < D.tm`. -/
theorem thm_al_rational_density_hb (D : ShellHBData) {v₀ : ℝ}
    (hfeas : OneProfileStrictFeasible D v₀) {v : ℝ} (hvv₀ : v < v₀) :
    ∃ d₀ ∈ Ioo v v₀, d₀ < D.tm ∧
      ∃ H₀ : ℂ → ℂ, IsAiryStrictLiftSeed (shellSites D : Set ℝ) d₀ H₀ := by
  obtain ⟨H, hH_weak, hH_strict⟩ := hfeas
  have hWit : IsAiryStrictWitness (shellSites D : Set ℝ) v₀ H := by
    refine ⟨⟨hH_weak.1, hH_weak.2.1, ?_, hH_weak.2.2.2.1, ?_⟩, ?_⟩
    · intro s hs
      rw [shellSites, Finset.mem_coe, Finset.mem_erase] at hs
      exact hH_weak.2.2.1 s hs.2 hs.1
    · intro y hy
      unfold airyLaplace
      exact mul_nonneg (Real.exp_pos _).le (hH_weak.2.2.2.2 y hy)
    · intro s hs
      rw [shellSites, Finset.mem_coe, Finset.mem_erase] at hs
      exact hH_strict s hs.2 hs.1
  have hv₀_le_tm : v₀ ≤ D.tm :=
    (one_profile_threshold_le_and_endpoint_iff D).1 v₀ ⟨H, hH_weak⟩
  obtain ⟨_, hdens⟩ := thm_al_rational_density (shellSites D).finite_toSet.isCompact hWit
  obtain ⟨d₀, hd₀_mem, H₀, hH₀⟩ := hdens v hvv₀
  exact ⟨d₀, hd₀_mem, hd₀_mem.2.trans_le hv₀_le_tm, H₀, hH₀⟩

/-- info: 'FormalResearch.SignUncertainty.thm_al_rational_density_hb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.thm_al_rational_density_hb

/-- Supremum identity `u_{\mathrm{strict}}(S) = u_{\mathrm{sh}}(S)` for compact `S ⊆ ℝ`
(`thm:al-rational-density`, `ce_airy_lp_proofs.tex` lines 899–900). -/
theorem airyUStrict_eq_airyUSh {S : Set ℝ} (hS : IsCompact S) :
    airyUStrict S = airyUSh S := by
  apply le_antisymm
  · unfold airyUStrict airyUSh
    refine iSup₂_le fun u ⟨H₀, hH₀⟩ => ?_
    exact le_iSup₂_of_le u ⟨H₀, hH₀.to_isAiryStrictWitness⟩ le_rfl
  · unfold airyUSh
    refine iSup₂_le fun v₀ ⟨H, hWit⟩ => ?_
    obtain ⟨_, hdens⟩ := thm_al_rational_density hS hWit
    by_contra hlt
    push Not at hlt
    cases h_u : airyUStrict S with
    | bot =>
      obtain ⟨d₀, _, H₀, hH₀⟩ := hdens (v₀ - 1) (by linarith)
      have hd₀_le : (d₀ : EReal) ≤ airyUStrict S :=
        le_iSup₂_of_le d₀ ⟨H₀, hH₀.to_isAiryLiftSeed⟩ le_rfl
      rw [h_u] at hd₀_le
      exact not_le_of_gt (EReal.bot_lt_coe d₀) hd₀_le
    | top =>
      rw [h_u] at hlt
      exact not_top_lt hlt
    | coe v =>
      rw [h_u] at hlt
      have hvv₀ : v < v₀ := EReal.coe_lt_coe_iff.mp hlt
      obtain ⟨d₀, ⟨hvd₀, _⟩, H₀, hH₀⟩ := hdens v hvv₀
      have hd₀_le : (d₀ : EReal) ≤ airyUStrict S :=
        le_iSup₂_of_le d₀ ⟨H₀, hH₀.to_isAiryLiftSeed⟩ le_rfl
      rw [h_u, EReal.coe_le_coe_iff] at hd₀_le
      linarith

/-- info: 'FormalResearch.SignUncertainty.airyUStrict_eq_airyUSh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.airyUStrict_eq_airyUSh

/-! ### Section 4: `CeShiftedLift` (`thm:ce-shifted-lift`) and Conditional `ce_airy_transfer_upper` -/

/-- **`CeCanonicalInputs.ce_airy_transfer_upper` (`thm:ce-airy-transfer`(1), upper bound) from
`CeShiftedLift`** (`ce_airy_lp_proofs.tex` lines 975–981):
combines the unconditional `thm_al_rational_density` with `CeShiftedLift` (`thm:ce-shifted-lift`)
and the Euclidean radial lift `ceAdmissible_of_hankelPair`. -/
theorem ce_airy_transfer_upper_of_shifted_lift (hLift : CeShiftedLift) (D : ShellHBData) :
    ∀ v : ℝ, (v : EReal) < uSh D → ∀ r : ℝ → ℕ → ℝ, ShellOffsetsSmall r →
      ∀ᶠ d : ℕ in atTop, ∃ R ∈ ceShellRadiusSet D r d,
        R ^ 2 / 2 ≤ (d : ℝ) / (2 * π ^ 2) - (v / hankelBeta1) * ((d : ℝ) / 2) ^ (1 / 3 : ℝ) := by
  intro v hv r hr
  -- 1. Extract a strict-site witness at `v₀ > v` and lift seed `H₀` at `d_cut ∈ (v, v₀)`
  rw [← airyUSh_shellHBData D] at hv
  have hS_eq : ((D.S : Set ℝ) \ {D.tm}) = (shellSites D : Set ℝ) := by
    rw [shellSites, Finset.coe_erase]
  rw [hS_eq] at hv
  unfold airyUSh at hv
  obtain ⟨v₀, hv₀_ex⟩ := lt_iSup_iff.mp hv
  obtain ⟨⟨H, hWit⟩, hvv₀_ereal⟩ := lt_iSup_iff.mp hv₀_ex
  have hvv₀ : v < v₀ := EReal.coe_lt_coe_iff.mp hvv₀_ereal
  have hS_compact : IsCompact (shellSites D : Set ℝ) := (shellSites D).finite_toSet.isCompact
  obtain ⟨_, hdens⟩ := thm_al_rational_density hS_compact hWit
  obtain ⟨d_cut, ⟨hvd_cut, _⟩, H₀, hH₀_strict⟩ := hdens v hvv₀
  -- 2. Apply `CeShiftedLift` to `(shellSites D, d_cut, H₀)`
  obtain ⟨K₀, ρ₁, d₀, hK₀_pos, hρ₁_pos, hd₀_pair⟩ :=
    hLift (shellSites D : Set ℝ) hS_compact d_cut H₀ hH₀_strict.to_isAiryLiftSeed
  have hβ_pos : 0 < hankelBeta1 := hankelBeta1_pos
  -- 3. Eventual smallness of `o(c^{1/3})` shell offsets on the finite set `shellSites D`
  have hev_shells : ∀ᶠ d : ℕ in atTop, ∀ t ∈ shellSites D,
      |hankelBeta1 * (r t d / ((d : ℝ) / 2) ^ (1 / 3 : ℝ))| ≤ ρ₁ := by
    rw [Filter.eventually_all_finset]
    intro t _
    have ht_lim := (hr t).const_mul hankelBeta1
    rw [mul_zero] at ht_lim
    filter_upwards [Metric.tendsto_nhds.mp ht_lim ρ₁ hρ₁_pos] with d hd
    rw [Real.dist_eq, sub_zero] at hd
    exact hd.le
  -- 4. Eventual domination of `K₀` by `((d_cut - v) / β₁) (d / 2)^{1/3}`
  set gap : ℝ := (d_cut - v) / hankelBeta1
  have hgap_pos : 0 < gap := div_pos (sub_pos.mpr hvd_cut) hβ_pos
  set d_gap : ℕ := ⌈2 * (K₀ / gap) ^ 3⌉₊ + 2
  filter_upwards [eventually_ge_atTop (max d₀ d_gap), hev_shells] with d hd_ge hshells_d
  have hd_d₀ : d₀ ≤ d := (le_max_left _ _).trans hd_ge
  have hd_gap : d_gap ≤ d := (le_max_right _ _).trans hd_ge
  have hd2 : 2 ≤ d := by dsimp [d_gap] at hd_gap; omega
  obtain ⟨G, hcont, hint, hhat_pos, hhat_int, hG0, horigin, htail_strict, hshell_strict⟩ :=
    hd₀_pair d hd_d₀
  set c : ℝ := (d : ℝ) / 2
  have hc_pos : 0 < c := by
    dsimp [c]
    have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2
    linarith
  have hc13_pos : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc_pos _
  set T : ℝ := c / π ^ 2 - (d_cut / hankelBeta1) * c ^ (1 / 3 : ℝ) + K₀
  have hT_pos : 0 < T := by
    by_contra hle
    push Not at hle
    exact absurd (htail_strict 0 hle) (not_lt.mpr hG0.le)
  have hK₀_le_gap : K₀ ≤ gap * c ^ (1 / 3 : ℝ) := by
    have h1 : 2 * (K₀ / gap) ^ 3 ≤ (d : ℝ) := by
      calc 2 * (K₀ / gap) ^ 3 ≤ (⌈2 * (K₀ / gap) ^ 3⌉₊ : ℝ) := Nat.le_ceil _
        _ ≤ (d_gap : ℝ) := by dsimp [d_gap]; exact_mod_cast Nat.le_add_right _ 2
        _ ≤ (d : ℝ) := by exact_mod_cast hd_gap
    have h2 : (K₀ / gap) ^ 3 ≤ c := by dsimp [c]; linarith
    have h3 : ((K₀ / gap) ^ 3) ^ (1 / 3 : ℝ) ≤ c ^ (1 / 3 : ℝ) :=
      Real.rpow_le_rpow (by positivity) h2 (by norm_num)
    have h4 : ((K₀ / gap) ^ 3) ^ (1 / 3 : ℝ) = K₀ / gap := by
      rw [← Real.rpow_natCast (K₀ / gap) 3, ← Real.rpow_mul (by positivity : 0 ≤ K₀ / gap)]
      norm_num
    rw [h4, div_le_iff₀ hgap_pos] at h3
    linarith
  have hT_ub : T ≤ (d : ℝ) / (2 * π ^ 2) - (v / hankelBeta1) * ((d : ℝ) / 2) ^ (1 / 3 : ℝ) := by
    have hc_pi : c / π ^ 2 = (d : ℝ) / (2 * π ^ 2) := by dsimp [c]; ring
    have hsub_gap : gap * c ^ (1 / 3 : ℝ) =
        (d_cut / hankelBeta1) * c ^ (1 / 3 : ℝ) - (v / hankelBeta1) * c ^ (1 / 3 : ℝ) := by
      dsimp [gap]; ring
    dsimp [T]
    rw [hc_pi]
    dsimp [c] at hK₀_le_gap hsub_gap ⊢
    linarith
  -- 5. Lift `G` to `Euc d` via `ceAdmissible_of_hankelPair`
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, d = n + 1 := ⟨d - 1, by omega⟩
  have hn : 1 ≤ n := by omega
  have hc_eq : (((n + 1 : ℕ) : ℝ) / 2) = ((n : ℝ) + 1) / 2 := by push_cast; ring
  have hint' : IntegrableOn (fun Δ => G Δ * hankelRho0 (((n : ℝ) + 1) / 2) Δ) (Ioi 0) := by
    rwa [← hc_eq]
  have hhat_nn' : ∀ Δ : ℝ, 0 ≤ Δ → 0 ≤ besselHankelTransform (((n : ℝ) + 1) / 2) G Δ := by
    intro Δ hΔ; rw [← hc_eq]; exact (hhat_pos Δ hΔ).le
  have hhat_int' : IntegrableOn (fun Δ =>
      besselHankelTransform (((n : ℝ) + 1) / 2) G Δ * hankelRho0 (((n : ℝ) + 1) / 2) Δ) (Ioi 0) := by
    rwa [← hc_eq]
  have horigin' : G 0 = besselHankelTransform (((n : ℝ) + 1) / 2) G 0 := by rwa [← hc_eq]
  have hadm := ceAdmissible_of_hankelPair n hn hT_pos hcont hint' hhat_nn' hhat_int' hG0 horigin'
    (fun Δ hΔ => (htail_strict Δ hΔ).le)
  refine ⟨√(2 * T), ⟨fun x : Euc (n + 1) => G (‖x‖ ^ 2 / 2),
    ⟨hadm, fun x y hxy => by simp only [hxy], ?_⟩⟩, ?_⟩
  · intro t ht htm x hx_shell
    have ht_mem : t ∈ shellSites D := Finset.mem_erase.mpr ⟨htm, ht⟩
    set s' : ℝ := t - hankelBeta1 * (r t (n + 1) / c ^ (1 / 3 : ℝ))
    have hs'_near : ∃ s ∈ (shellSites D : Set ℝ), |s' - s| ≤ ρ₁ := by
      refine ⟨t, ht_mem, ?_⟩
      have hd_sub : s' - t = -(hankelBeta1 * (r t (n + 1) / c ^ (1 / 3 : ℝ))) := by
        dsimp [s']; ring
      rw [hd_sub, abs_neg]
      exact hshells_d t ht_mem
    have hsite_eq : shellSite t (r t) (n + 1) =
        c / π ^ 2 - (s' / hankelBeta1) * c ^ (1 / 3 : ℝ) := by
      unfold shellSite
      dsimp [c, s']
      have hβ_ne : hankelBeta1 ≠ 0 := hβ_pos.ne'
      have hc13_ne : (((n + 1 : ℕ) : ℝ) / 2) ^ (1 / 3 : ℝ) ≠ 0 := hc13_pos.ne'
      field_simp [hβ_ne, hc13_ne]
      ring
    have hΔ_nn : 0 ≤ c / π ^ 2 - (s' / hankelBeta1) * c ^ (1 / 3 : ℝ) := by
      rw [← hsite_eq, ← hx_shell]
      positivity
    rw [hx_shell, hsite_eq]
    exact (hshell_strict s' hs'_near hΔ_nn).le
  · rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * T)]
    linarith [hT_ub]

/-- info: 'FormalResearch.SignUncertainty.ce_airy_transfer_upper_of_shifted_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.ce_airy_transfer_upper_of_shifted_lift

/-- The former field `ce_airy_transfer_upper` of `CeCanonicalInputs` (`thm:ce-airy-transfer`(1), upper bound),
derived from the field `shifted_lift : CeShiftedLift` by `ce_airy_transfer_upper_of_shifted_lift`. -/
theorem CeCanonicalInputs.ce_airy_transfer_upper {D : ShellHBData} {t : ℕ → ℝ}
    (I : CeCanonicalInputs D t) :
    ∀ v : ℝ, (v : EReal) < uSh D → ∀ r : ℝ → ℕ → ℝ, ShellOffsetsSmall r →
      ∀ᶠ d : ℕ in atTop, ∃ R ∈ ceShellRadiusSet D r d,
        R ^ 2 / 2 ≤ (d : ℝ) / (2 * π ^ 2) - (v / hankelBeta1) * ((d : ℝ) / 2) ^ (1 / 3 : ℝ) :=
  ce_airy_transfer_upper_of_shifted_lift I.shifted_lift D

/-- info: 'FormalResearch.SignUncertainty.CeCanonicalInputs.ce_airy_transfer_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.CeCanonicalInputs.ce_airy_transfer_upper

end FormalResearch.SignUncertainty
