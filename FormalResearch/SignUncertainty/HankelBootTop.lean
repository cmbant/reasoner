module

public import FormalResearch.SignUncertainty.HankelTransportMass
public import FormalResearch.SignUncertainty.HankelBandMeasure

/-!
# Top mass bound with the tail mass kept (M5-S6a, `hI_line`)

`hankel_psi_total_upper_tail`: for `f ≥ 0` at the Hankel point of `a`,
`∫_a^A Re Ψ̃ + ∫_{u > cξ(a)} ρ₀ f ≤ lobe + 2 A r_∞`.  The proof is that of `hankel_psi_total_upper`, keeping the tail mass
`∫_{(cξ(a), ∞)} ρ₀ f` (which is the dm-side mass `B_2` when `a = -R`) on the left instead of dropping it by positivity.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real Interval

namespace FormalResearch.SignUncertainty

theorem hankel_psi_total_upper_tail {c ε T : ℝ} (hc : 3e6 ≤ c) {f : ℝ → ℝ} (hf : IsHankelFeasible c ε T f)
    (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1) {a : ℝ} (ha : |a| ≤ langerRadius c)
    (hT : T ≤ c * hankelXi c a) :
    (∫ x in a..(langerRadius c), hankelPsiR c f x) +
        ∫ u in Ioi (c * hankelXi c a), hankelRho0 c u * f u ≤
      hankelLobe c + 2 * langerRadius c * hankelRinf c := by
  have hc0 : 0 < c := by linarith
  have hc5 : (5000 : ℝ) ≤ c := by linarith
  have hfe := hf.toIsHankelEigenfn
  have hA := langerRadius_pos hc0
  have hAA : |langerRadius c| ≤ langerRadius c := by rw [abs_of_pos hA]
  have haA : a ≤ langerRadius c := (abs_le.1 ha).2
  have hr := hankelRinf_nonneg hc5 hfe hε hM
  have hG := hankel_transport_G hc5 hfe hε hM (G := fun v => v) continuous_id
    (fun s t => le_rfl) (fun l v hl => rfl) ha hAA haA
  beta_reduce at hG
  rw [abs_le] at hG
  have hpA : 0 < c * hankelXi c (langerRadius c) := mul_pos hc0 (hankelXi_pos hc0 hAA)
  have hmono := hankel_phi_anti hc0 ha hAA haA
  have hgF := hankel_gF_int hfe
  have hsplit := hankel_split3 hgF hpA.le hmono
  have hlobe : -hankelLobe c ≤ ∫ u in Ioc (0 : ℝ) (c * hankelXi c (langerRadius c)), hankelRho0 c u * f u := by
    have hcomm : (∫ u in Ioc (0 : ℝ) (c * hankelXi c (langerRadius c)), |f u| * hankelRho0 c u) =
        ∫ u in Ioc (0 : ℝ) (c * hankelXi c (langerRadius c)), hankelRho0 c u * |f u| := by
      simp only [mul_comm]
    have h1 := hankel_lobe_small hc hfe hε hM
    rw [hcomm] at h1
    have h2 : -∫ u in Ioc (0 : ℝ) (c * hankelXi c (langerRadius c)), hankelRho0 c u * |f u| ≤
        ∫ u in Ioc (0 : ℝ) (c * hankelXi c (langerRadius c)), hankelRho0 c u * f u := by
      rw [← integral_neg]
      exact setIntegral_mono_on ((hankel_gA_int hc0 hfe).mono_set (fun u (hu : u ∈ Ioc (0 : ℝ) _) => hu.1) |>.neg)
        (hgF.mono_set (fun u hu => hu.1)) measurableSet_Ioc fun u hu => by
          have := mul_le_mul_of_nonneg_left (neg_abs_le (f u)) (hankelRho0_nonneg hc0 hu.1.le)
          linarith
    linarith
  rw [hankel_gF_integral hc0 hfe] at hsplit
  have horig : ε * f 0 ≤ 0 := hf.origin_sign
  have h2 : (langerRadius c - a) * hankelRinf c ≤ 2 * langerRadius c * hankelRinf c :=
    mul_le_mul_of_nonneg_right (by linarith [(abs_le.1 ha).1]) hr
  linarith [hG.1, hG.2]

/-- info: 'FormalResearch.SignUncertainty.hankel_psi_total_upper_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel_psi_total_upper_tail

/-- The dm-side tail mass `dm_+([s, ∞))` is the `ρ₀ f`-mass above `c s` when `f ≥ 0` there (`B_2`, `s = ξ(-R)`). -/
theorem hankelBoot_B2_eq {c ε : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) {s : ℝ} (hs : 0 < s)
    (hnn : ∀ ξ : ℝ, s ≤ ξ → 0 ≤ f (c * ξ)) :
    (hankelDmPos c f (Ici s)).toReal = ∫ u in Ioi (c * s), hankelRho0 c u * f u := by
  have hsub : Ici s ⊆ Ioi (0 : ℝ) := fun x hx => lt_of_lt_of_le hs hx
  rw [hankelDmPos_apply measurableSet_Ici, inter_eq_left.2 hsub,
    ← integral_eq_lintegral_of_nonneg_ae]
  · rw [integral_Ici_eq_integral_Ioi]
    have h1 : ∀ x : ℝ, hankelDmDens c f x = c • (hankelRho0 c (c * x) * f (c * x)) := fun x => by
      unfold hankelDmDens; rw [smul_eq_mul, mul_comm (f _)]
    simp_rw [h1]
    rw [integral_smul, integral_comp_mul_left_Ioi (fun u => hankelRho0 c u * f u) s hc, smul_eq_mul, smul_eq_mul,
      ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
  · exact ae_restrict_of_forall_mem measurableSet_Ici fun x hx =>
      mul_nonneg hc.le (mul_nonneg (hnn x hx) (hankelRho0_nonneg hc (mul_nonneg hc.le (hs.le.trans hx))))
  · exact ((hankelDmDens_continuousOn hc hf).mono hsub).aestronglyMeasurable measurableSet_Ici

/-- info: 'FormalResearch.SignUncertainty.hankelBoot_B2_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBoot_B2_eq

end FormalResearch.SignUncertainty
