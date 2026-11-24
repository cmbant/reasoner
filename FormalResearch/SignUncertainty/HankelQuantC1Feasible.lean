module

public import FormalResearch.SignUncertainty.HankelQuantC1

/-!
# Hankel `TE.0` for feasible profiles (`gt:7.7p` (d) conclusion)

Instantiation of `hankel_quant_c1_typeI` (`HankelQuantC1`) at the Langer-disc density
`Ψ̃ = hankelPsi c f` of a feasible `f` with `M[f] = 1`: the hypotheses are supplied by
`hankelPsi_envelope` (type-(I) envelope, `C₀ = 60`), `analyticOnNhd_hankelPsi`, `hankelPsi_real` and the
mass hypotheses of `HankelTransportMass`, with the single error function
`δ(c) = hankelLobe c + (2A + 1) r_∞ → 0` (`A = langerRadius c`).  The threshold `T` is parametrised by the
point `u_T` of the Langer disc with `c ξ(u_T) = T`; a *violator* is `T < c ξ(a₁)` (`a₁ = airyZero 1`,
equivalently `u_T > a₁`), and the conclusion is `QuantC1B2Holds (hankelPsi c f) u_T`: `u_T - a₁` small and
`‖Ψ̃'‖ ≤ C₁`, `Re Ψ̃' ≤ -2κ_*` on `[a₁ - δ_*, a₁ + δ_*]` (same constants as for type (II)).
The cut bound `|Ψ̃| ≤ 32 e^{5/2}·60 (1+R₁)^{3/2} e^{(4/3)R₁^{3/2}}` on `|u| ≤ R₁` is `hankelI_cut_bound`.
-/

@[expose] public section

open Complex Set Filter Topology Metric MeasureTheory
open scoped Real Interval

namespace FormalResearch.SignUncertainty

open FormalResearch.Special FormalResearch.ModularBootstrap.ConcreteBootstrap

lemma hankelLobe_nonneg (c : ℝ) : 0 ≤ hankelLobe c := by unfold hankelLobe; positivity

lemma hankelLobe_tendsto : Tendsto hankelLobe atTop (𝓝 0) := by
  have h1 : Tendsto (fun c : ℝ => 4.9e-5 * c ^ (2 / 3 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).const_mul_atTop (by norm_num)
  have h2 : Tendsto (fun c : ℝ => (4.9e-5 * c ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 2)).comp h1
  have h3 : Tendsto (fun c : ℝ => -5 * (4.9e-5 * c ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ)) atTop atBot :=
    h2.const_mul_atTop_of_neg (by norm_num)
  have h4 : Tendsto (fun c : ℝ => -(1 / 25) * c) atTop atBot :=
    tendsto_id.const_mul_atTop_of_neg (by norm_num)
  have := ((Real.tendsto_exp_atBot.comp h3).add (Real.tendsto_exp_atBot.comp h4)).const_mul 8
  rw [show (8 : ℝ) * (0 + 0) = 0 by norm_num] at this
  exact this

lemma tendsto_langerRadius : Tendsto langerRadius atTop atTop := by
  have h1 : Tendsto (fun c : ℝ => c ^ (2 / 3 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)
  have h2 := (h1.atTop_mul_const langerKappa_pos).atTop_mul_const (by norm_num : (0 : ℝ) < 4.94e-4)
  exact h2

lemma hankelRinf_delta_tendsto :
    Tendsto (fun c : ℝ => (2 * langerRadius c + 1) * |hankelRinf c|) atTop (𝓝 0) := by
  set I : ℝ := |hankelTailI0| with hI
  have e1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1 / 40000) (by norm_num)
  have e2 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / 3) (1 / 40000) (by norm_num)
  have := (e1.const_mul (4 * (langerKappa * 4.94e-4) * I)).add (e2.const_mul (2 * I))
  simp only [mul_zero, add_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with c hc
  have hr : |hankelRinf c| = 2 * I * c ^ (1 / 3 : ℝ) * Real.exp (-(1 / 40000) * c) := by
    unfold hankelRinf
    have : Real.exp (-(c / 40000)) = Real.exp (-(1 / 40000) * c) := by congr 1; ring
    rw [this, abs_mul, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
      abs_of_pos (Real.rpow_pos_of_pos hc _)]
    simp [hI]
  have hp : c ^ (2 / 3 : ℝ) * c ^ (1 / 3 : ℝ) = c ^ (1 : ℝ) := by
    rw [← Real.rpow_add hc]; norm_num
  rw [hr]
  unfold langerRadius langerScale
  have : c ^ (2 / 3 : ℝ) * c ^ (1 / 3 : ℝ) = c ^ (1 : ℝ) := hp
  calc 4 * (langerKappa * 4.94e-4) * I * (c ^ (1 : ℝ) * Real.exp (-(1 / 40000) * c)) +
        2 * I * (c ^ (1 / 3 : ℝ) * Real.exp (-(1 / 40000) * c))
      = 4 * (langerKappa * 4.94e-4) * I * ((c ^ (2 / 3 : ℝ) * c ^ (1 / 3 : ℝ)) * Real.exp (-(1 / 40000) * c)) +
        2 * I * (c ^ (1 / 3 : ℝ) * Real.exp (-(1 / 40000) * c)) := by rw [this]
    _ = _ := by ring

lemma hankel_norm_exp_eq_airyEnv (u : ℂ) :
    ‖Complex.exp (-(4 / 3 : ℂ) * u ^ (3 / 2 : ℂ))‖ = airyEnv u := by
  rw [Complex.norm_exp]
  unfold airyEnv
  congr 1
  simp [Complex.mul_re]

/-- The negative mass of a profile below `cξ(A)` is at most the lobe mass. -/
lemma hankel_gN_lobe_le {c ε : ℝ} (hc : 3e6 ≤ c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1) :
    ∫ u in Ioc (0 : ℝ) (c * hankelXi c (langerRadius c)), hankelRho0 c u * max 0 (-f u) ≤
      hankelLobe c := by
  have hc0 : 0 < c := by linarith
  refine le_trans ?_ (hankel_lobe_small hc hf hε hM)
  have hcomm : (∫ u in Ioc (0 : ℝ) (c * hankelXi c (langerRadius c)), |f u| * hankelRho0 c u) =
      ∫ u in Ioc (0 : ℝ) (c * hankelXi c (langerRadius c)), hankelRho0 c u * |f u| := by
    simp only [mul_comm]
  rw [hcomm]
  exact setIntegral_mono_on ((hankel_gN_int hc0 hf).mono_set (fun u hu => hu.1))
    ((hankel_gA_int hc0 hf).mono_set (fun u hu => hu.1)) measurableSet_Ioc fun u hu =>
    mul_le_mul_of_nonneg_left (max_le (abs_nonneg _) (neg_le_abs _)) (hankelRho0_nonneg hc0 hu.1.le)

/-- **`TE.0` for feasible Hankel profiles** (`gt:7.7p` (d)).  There is `c₁ ≥ 3·10⁶` such that for every
`c ≥ c₁` and every `f` feasible at `T` with `M[f] = 1` and `T < cξ(a₁)` (`a₁ = airyZero 1`), the unique
`u_T ∈ [-A, A]` with `cξ(u_T) = T` satisfies `a₁ < u_T` and `QuantC1B2Holds (hankelPsi c f) u_T`. -/
theorem hankel_quantC1_of_feasible :
    ∃ c₁ : ℝ, 3e6 ≤ c₁ ∧ ∀ (c ε T : ℝ) (f : ℝ → ℝ), c₁ ≤ c → IsHankelFeasible c ε T f →
      (ε = 1 ∨ ε = -1) → hankelMass c f = 1 → T < c * hankelXi c (airyZero 1) →
      ∃ u_T : ℝ, airyZero 1 < u_T ∧ u_T ≤ langerRadius c ∧ c * hankelXi c u_T = T ∧
        QuantC1B2Holds (hankelPsi c f) u_T := by
  let δ : ℝ → ℝ := fun c => hankelLobe c + (2 * langerRadius c + 1) * |hankelRinf c|
  have hδ_lim : Tendsto δ atTop (𝓝 0) := by
    have := hankelLobe_tendsto.add hankelRinf_delta_tendsto
    rw [add_zero] at this
    exact this
  have hδ_nn : ∀ᶠ c in atTop, 0 ≤ δ c := by
    filter_upwards [eventually_gt_atTop 0] with c hc
    have := langerRadius_pos hc
    exact add_nonneg (hankelLobe_nonneg c) (mul_nonneg (by linarith) (abs_nonneg _))
  obtain ⟨c₁', hc₁'2, hmain⟩ := hankel_quant_c1_typeI (C_0 := 60) (by norm_num) langerRadius δ
    tendsto_langerRadius hδ_nn hδ_lim
  obtain ⟨c₂, hc₂⟩ := eventually_atTop.mp (hankelLobe_tendsto (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)))
  obtain ⟨c₃, hc₃⟩ := eventually_atTop.mp (tendsto_langerRadius.eventually_ge_atTop |airyZero 1|)
  refine ⟨max (max c₁' c₂) (max c₃ 3e6), le_max_of_le_right (le_max_right _ _), ?_⟩
  intro c ε T f hc hf hε hM hT
  have hc1 : c₁' ≤ c := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hc
  have hc2 : c₂ ≤ c := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hc
  have hc3 : c₃ ≤ c := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hc
  have hc6 : (3e6 : ℝ) ≤ c := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hc
  have hc0 : 0 < c := by linarith
  have hc5 : (5000 : ℝ) ≤ c := by linarith
  have hfe := hf.toIsHankelEigenfn
  have hA := langerRadius_pos hc0
  have hAA : |langerRadius c| ≤ langerRadius c := by rw [abs_of_pos hA]
  have ha1 : |airyZero 1| ≤ langerRadius c := hc₃ c hc3
  have hlobe_le : hankelLobe c ≤ 1 / 4 := hc₂ c hc2
  have hr := hankelRinf_nonneg hc5 hfe hε hM
  have hr_abs : |hankelRinf c| = hankelRinf c := abs_of_nonneg hr
  have hδ_ge : hankelLobe c + 2 * langerRadius c * hankelRinf c ≤ δ c := by
    show _ ≤ hankelLobe c + (2 * langerRadius c + 1) * |hankelRinf c|
    rw [hr_abs]; nlinarith
  have hδ_ge2 : hankelRinf c ≤ δ c := by
    have := hankelLobe_nonneg c
    show _ ≤ hankelLobe c + (2 * langerRadius c + 1) * |hankelRinf c|
    rw [hr_abs]; nlinarith
  have hcont : ContinuousOn (fun x => c * hankelXi c x) (Icc (-langerRadius c) (langerRadius c)) :=
    fun x hx => ((hasDerivAt_hankelXi hc0 (abs_le.2 hx)).const_mul c).continuousAt.continuousWithinAt
  have hmA : |-langerRadius c| ≤ langerRadius c := by rw [abs_neg]; exact hAA
  -- `T` lies above the value at the disc edge
  have hT_lo : c * hankelXi c (langerRadius c) < T := by
    by_contra hle
    push Not at hle
    have hgN := hankel_gN_int hc0 hfe
    have hpA : 0 < c * hankelXi c (langerRadius c) := mul_pos hc0 (hankelXi_pos hc0 hAA)
    have hsplit := hankel_split3 hgN hpA.le (le_refl (c * hankelXi c (langerRadius c)))
    have hzero : ∫ u in Ioi (c * hankelXi c (langerRadius c)), hankelRho0 c u * max 0 (-f u) = 0 := by
      refine setIntegral_eq_zero_of_forall_eq_zero fun u hu => ?_
      rw [max_eq_left (by linarith [hf.tail_nonneg u (hle.trans (le_of_lt hu))]), mul_zero]
    have hhalf := hankel_gN_integral hc0 hfe hM
    have horig : ε * f 0 ≤ 0 := hf.origin_sign
    have hl := hankel_gN_lobe_le hc6 hfe hε hM
    rw [intervalIntegral.integral_same] at hsplit
    linarith
  have ha1_lo : -langerRadius c ≤ airyZero 1 := by linarith [(abs_le.1 ha1).1]
  have hT_up : T < c * hankelXi c (-langerRadius c) :=
    lt_of_lt_of_le hT (hankel_phi_anti hc0 hmA ha1 ha1_lo)
  obtain ⟨u_T, hu_mem, hu_eq⟩ := intermediate_value_Icc' (by linarith : -langerRadius c ≤ langerRadius c)
    hcont ⟨hT_lo.le, hT_up.le⟩
  have hu_abs : |u_T| ≤ langerRadius c := abs_le.2 hu_mem
  have hu_eq' : c * hankelXi c u_T = T := hu_eq
  have ha1_lt : airyZero 1 < u_T := by
    by_contra hle
    push Not at hle
    have := hankel_phi_anti hc0 hu_abs ha1 hle
    linarith
  have hanti : ∀ x, |x| ≤ langerRadius c → x ≤ u_T → T ≤ c * hankelXi c x := fun x hx hxu => by
    rw [← hu_eq']; exact hankel_phi_anti hc0 hx hu_abs hxu
  have hB2 := hmain c hc1 (hankelPsi c f) u_T
    (analyticOnNhd_hankelPsi hc0 hfe)
    (fun x hx => hankelPsi_real hc0 f (abs_le.2 hx))
    (fun u hu hcut => by
      have h := hankelPsi_envelope (by linarith : (2 : ℝ) ≤ c) hfe hε hM (u := u)
        (mem_closedBall_zero_iff.1 hu) hcut
      rw [hankel_norm_exp_eq_airyEnv] at h
      exact h)
    ha1_lt hu_mem.2
    (fun x hx => by
      have hxA : |x| ≤ langerRadius c := abs_le.2 ⟨hx.1, hx.2.trans hu_mem.2⟩
      have := hankel_psi_sign hc5 hf hε hM hxA (hanti x hxA hx.2)
      show -δ c ≤ hankelPsiR c f x
      linarith)
    (by
      have h := hankel_psi_abs_mass hc5 hfe hε hM
      have hcongr : ∫ x in (-langerRadius c)..(langerRadius c), ‖hankelPsi c f (x : ℂ)‖ =
          ∫ x in (-langerRadius c)..(langerRadius c), |hankelPsiR c f x| := by
        refine intervalIntegral.integral_congr fun x hx => ?_
        rw [uIcc_of_le (by linarith : -langerRadius c ≤ langerRadius c)] at hx
        have him := hankelPsi_real hc0 f (abs_le.2 hx)
        show ‖hankelPsi c f (x : ℂ)‖ = |(hankelPsi c f (x : ℂ)).re|
        rw [Complex.abs_re_eq_norm.2 him]
      rw [hcongr]
      have := hankelLobe_nonneg c
      show _ ≤ 1 + δ c
      linarith)
    (by
      have := hankel_psi_neg_mass hc6 hf hε hM hu_abs hu_eq'.ge
      show 1 / 2 - δ c ≤ ∫ x in u_T..(langerRadius c), max 0 (-hankelPsiR c f x)
      linarith)
    (fun R' hR' hle => by
      have hR'A : |-R'| ≤ langerRadius c := by rw [abs_neg, abs_of_nonneg hR'.1]; exact hR'.2
      have := hankel_psi_total_upper hc6 hf hε hM hR'A (hanti (-R') hR'A hle)
      show ∫ x in (-R')..(langerRadius c), hankelPsiR c f x ≤ δ c
      linarith)
  exact ⟨u_T, ha1_lt, hu_mem.2, hu_eq', hB2⟩

/-- info: 'FormalResearch.SignUncertainty.hankel_quantC1_of_feasible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel_quantC1_of_feasible

end FormalResearch.SignUncertainty
