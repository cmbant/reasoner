module

public import FormalResearch.SignUncertainty.HankelBesselLaguerre
public import FormalResearch.SignUncertainty.HankelBesselMellin
public import FormalResearch.SignUncertainty.HankelInversion
public import FormalResearch.SignUncertainty.HankelThresholds
public import FormalResearch.SignUncertainty.HbMultilevelDefs

/-!
# Exact Origin Condition for Prescribed-Site Hankel Minimizers (`gt:7.9b`)

Proves `hankelExactOrigin_proved : HankelExactOrigin`:
for every real `c > 1/2`, sign `ε ∈ {1, -1}`, and finite set `sites` of positive points,
every `IsHankelSiteMinimizer c ε sites T f` satisfies `f 0 = 0`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.SignUncertainty

private lemma isHankelEigenfn_add {c ε : ℝ} (hc : 1 / 2 < c) {f g : ℝ → ℝ}
    (hf : IsHankelEigenfn c ε f) (hg : IsHankelEigenfn c ε g) :
    IsHankelEigenfn c ε (fun Δ => f Δ + g Δ) where
  cont := hf.cont.add hg.cont
  int := (hf.int.add hg.int).congr_fun (fun s _ => by dsimp; ring) measurableSet_Ioi
  eigen Δ hΔ := by
    rw [besselHankelTransform_add hc hf.int hg.int Δ, hf.eigen Δ hΔ, hg.eigen Δ hΔ]
    ring

private lemma hankel_site_minimizer_pos {c ε : ℝ} (hc : 1 / 2 < c) {sites : Finset ℝ} {T : ℝ}
    {f : ℝ → ℝ} (hmin : IsHankelSiteMinimizer c ε sites T f) : 0 < T := by
  have hc0 : 0 < c := by linarith
  have hf := hmin.feasible
  by_contra hT
  push Not at hT
  have hnonneg : ∀ s : ℝ, 0 < s → 0 ≤ f s := fun s hs => hf.tail_nonneg s (by linarith)
  have hint0 : ∫ s in Ioi (0 : ℝ), f s * hankelRho0 c s ≤ 0 := by
    have h0 := hf.eigen 0 self_mem_Ici
    rw [besselHankelTransform_zero hc0] at h0
    linarith [hf.origin_sign]
  have hint_nn : 0 ≤ ∫ s in Ioi (0 : ℝ), f s * hankelRho0 c s :=
    setIntegral_nonneg measurableSet_Ioi fun s hs =>
      mul_nonneg (hnonneg s hs) (hankelRho0_nonneg hc0 hs.le)
  have hint_eq : ∫ s in Ioi (0 : ℝ), f s * hankelRho0 c s = 0 := le_antisymm hint0 hint_nn
  have hrho_cont : ContinuousOn (hankelRho0 c) (Ioi 0) := by
    unfold hankelRho0
    exact continuousOn_const.mul (continuousOn_id.rpow_const fun s hs => Or.inl (ne_of_gt hs))
  have hcont_on : ContinuousOn (fun s : ℝ => f s * hankelRho0 c s) (Ioi 0) :=
    (hf.cont.mono Ioi_subset_Ici_self).mul hrho_cont
  have h_ae : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), f s * hankelRho0 c s = 0 := by
    have h := (integral_eq_zero_iff_of_nonneg_ae
      (ae_restrict_of_forall_mem measurableSet_Ioi fun s (hs : 0 < s) =>
        mul_nonneg (hnonneg s hs) (hankelRho0_nonneg hc0 hs.le)) hf.int).mp hint_eq
    exact h
  have hf_pos_zero : ∀ s : ℝ, 0 < s → f s = 0 := fun s hs => by
    have hmul0 : f s * hankelRho0 c s = 0 := by
      by_contra hnz
      have hpos : 0 < f s * hankelRho0 c s :=
        lt_of_le_of_ne (mul_nonneg (hnonneg s hs) (hankelRho0_nonneg hc0 hs.le)) (Ne.symm hnz)
      obtain ⟨δ, hδ, hball⟩ := Metric.continuousWithinAt_iff.mp (hcont_on s hs)
        (f s * hankelRho0 c s / 2) (by linarith)
      let a : ℝ := max (s / 2) (s - δ / 2)
      let b' : ℝ := s + δ / 2
      have ha_pos : 0 < a := lt_max_of_lt_left (by linarith)
      have hab : a < b' := by dsimp [a, b']; exact max_lt (by linarith) (by linarith)
      have hsub : Ioo a b' ⊆ {x : ℝ | f x * hankelRho0 c x ≠ 0} := fun x hx => by
        have hx0 : 0 < x := lt_trans ha_pos hx.1
        dsimp [a, b'] at hx
        have hdist : dist x s < δ := by
          rw [Real.dist_eq, abs_lt]
          constructor <;> [linarith [le_max_right (s / 2) (s - δ / 2), hx.1]; linarith [hx.2]]
        have hb := (abs_lt.mp (by simpa [Real.dist_eq] using hball hx0 hdist)).1
        exact ne_of_gt (by linarith)
      have hsub_pos : Ioo a b' ⊆ Ioi (0 : ℝ) := fun x hx => lt_trans ha_pos hx.1
      have hvol0 : (volume.restrict (Ioi (0 : ℝ))) (Ioo a b') = 0 :=
        measure_mono_null hsub (ae_iff.mp h_ae)
      rw [Measure.restrict_apply measurableSet_Ioo,
        Set.inter_eq_left.mpr hsub_pos, Real.volume_Ioo,
        ENNReal.ofReal_eq_zero] at hvol0
      linarith
    have hrho : 0 < hankelRho0 c s := by
      unfold hankelRho0
      exact mul_pos (div_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.Gamma_pos_of_pos hc0))
        (Real.rpow_pos_of_pos hs _)
    exact (mul_eq_zero.mp hmul0).resolve_right hrho.ne'
  have hf0 : f 0 = 0 := by
    have hlim : Tendsto f (𝓝[>] 0) (𝓝 (f 0)) :=
      (hf.cont 0 self_mem_Ici).mono_left (nhdsWithin_mono 0 Ioi_subset_Ici_self)
    have hzero : Tendsto f (𝓝[>] 0) (𝓝 0) :=
      tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun s hs => (hf_pos_zero s hs).symm)
    exact tendsto_nhds_unique hlim hzero
  obtain ⟨Δ, hΔ, hne⟩ := hf.nonzero
  rcases eq_or_lt_of_le hΔ with rfl | hpos
  · exact hne hf0
  · exact hne (hf_pos_zero Δ hpos)

private lemma integrableOn_exp_mul_rho0 {c p : ℝ} (hc : 0 < c) (hp : 0 < p) :
    IntegrableOn (fun s => Real.exp (-(p * s)) * hankelRho0 c s) (Ioi 0) := by
  let C : ℝ := (2 * π) ^ c / Real.Gamma c
  have h1 : IntegrableOn (fun s : ℝ => s ^ (c - 1) * Real.exp (-p * s)) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_Ioi (by linarith : (-1 : ℝ) < c - 1) hp
  refine IntegrableOn.congr_fun (h1.const_mul C) (fun s _ => ?_) measurableSet_Ioi
  dsimp [C, hankelRho0]
  rw [neg_mul]
  ring

private lemma isHankelEigenfn_recip_neg {c b : ℝ} (hc : 1 / 2 < c) (hb : 1 < b) :
    IsHankelEigenfn c (-1)
      (fun Δ => b ^ (-c) * Real.exp (-(2 * π / b * Δ)) - Real.exp (-(2 * π * b * Δ))) := by
  have hc0 : 0 < c := by linarith
  have hb0 : 0 < b := by linarith
  have hp1 : 0 < 2 * π / b := by positivity
  have hp2 : 0 < 2 * π * b := by positivity
  refine ⟨by fun_prop, ?_, fun Δ hΔ => ?_⟩
  · have h1 := (integrableOn_exp_mul_rho0 hc0 hp1).const_mul (b ^ (-c))
    have h2 := integrableOn_exp_mul_rho0 hc0 hp2
    refine IntegrableOn.congr_fun (h1.sub h2) (fun s _ => ?_) measurableSet_Ioi
    dsimp only [Pi.sub_apply]
    ring
  · have hL1 := hankel_laplace hc0 hΔ hp1
    have hL2 := hankel_laplace hc0 hΔ hp2
    have hpow1 : (2 * π / (2 * π / b)) ^ c = b ^ c := by
      have h2π : (2 : ℝ) * π ≠ 0 := by positivity
      rw [div_div_cancel₀ h2π]
    have hpow2 : (2 * π / (2 * π * b)) ^ c = b ^ (-c) := by
      have h2π : (2 : ℝ) * π ≠ 0 := by positivity
      rw [div_mul_cancel_left₀ h2π, ← Real.rpow_neg_one, ← Real.rpow_mul hb0.le, neg_one_mul]
    have hexp1 : 4 * π ^ 2 * Δ / (2 * π / b) = 2 * π * b * Δ := by
      have h2π : (2 : ℝ) * π ≠ 0 := by positivity
      field_simp [h2π, hb0.ne']; ring
    have hexp2 : 4 * π ^ 2 * Δ / (2 * π * b) = 2 * π / b * Δ := by
      have h2π : (2 : ℝ) * π ≠ 0 := by positivity
      field_simp [h2π, hb0.ne']; ring
    rw [hpow1, hexp1] at hL1
    rw [hpow2, hexp2] at hL2
    unfold besselHankelTransform
    have e1 : (fun s : ℝ => (b ^ (-c) * Real.exp (-(2 * π / b * s)) - Real.exp (-(2 * π * b * s))) *
          hankelRho0 c s * hankelKernel c Δ s) = fun s =>
        b ^ (-c) * (Real.exp (-(2 * π / b * s)) * (hankelRho0 c s * hankelPhi c (Δ * s))) -
          Real.exp (-(2 * π * b * s)) * (hankelRho0 c s * hankelPhi c (Δ * s)) := by
      funext s; unfold hankelKernel; ring
    have hI1' : IntegrableOn (fun s => b ^ (-c) * (Real.exp (-(2 * π / b * s)) *
        (hankelRho0 c s * hankelPhi c (Δ * s)))) (Ioi 0) :=
      IntegrableOn.congr_fun
        ((integrableOn_mul_hankelKernel hc (integrableOn_exp_mul_rho0 hc0 hp1) Δ).const_mul (b ^ (-c)))
        (fun s _ => by unfold hankelKernel; ring) measurableSet_Ioi
    have hI2' : IntegrableOn (fun s => Real.exp (-(2 * π * b * s)) *
        (hankelRho0 c s * hankelPhi c (Δ * s))) (Ioi 0) :=
      IntegrableOn.congr_fun (integrableOn_mul_hankelKernel hc (integrableOn_exp_mul_rho0 hc0 hp2) Δ)
        (fun s _ => by unfold hankelKernel; ring) measurableSet_Ioi
    rw [e1, integral_sub hI1' hI2', integral_const_mul, hL1, hL2]
    have hc_cancel : b ^ (-c) * b ^ c = 1 := by
      rw [← Real.rpow_add hb0, neg_add_cancel, Real.rpow_zero]
    calc b ^ (-c) * (b ^ c * Real.exp (-(2 * π * b * Δ))) - b ^ (-c) * Real.exp (-(2 * π / b * Δ))
        = (b ^ (-c) * b ^ c) * Real.exp (-(2 * π * b * Δ)) - b ^ (-c) * Real.exp (-(2 * π / b * Δ)) := by ring
      _ = Real.exp (-(2 * π * b * Δ)) - b ^ (-c) * Real.exp (-(2 * π / b * Δ)) := by rw [hc_cancel, one_mul]
      _ = -1 * (b ^ (-c) * Real.exp (-(2 * π / b * Δ)) - Real.exp (-(2 * π * b * Δ))) := by ring

private lemma exact_origin_contradiction {c ε T : ℝ} {sites : Finset ℝ} {f f₀ : ℝ → ℝ}
    (hmin : IsHankelSiteMinimizer c ε sites T f) (hT_pos : 0 < T)
    (heig : IsHankelEigenfn c ε f₀) (hf0_sign : ε * f₀ 0 ≤ 0)
    (hf0_sites : ∀ s ∈ sites, 0 ≤ f₀ s) (hf0_tail : ∀ Δ ≥ T, 0 ≤ f₀ Δ) (hf0_T : 0 < f₀ T) :
    False := by
  have hcont_T : ContinuousAt f₀ T := by
    have hwithin : ContinuousWithinAt f₀ (Ici 0) T := heig.cont T hT_pos.le
    exact hwithin.continuousAt (Ici_mem_nhds hT_pos)
  obtain ⟨δ', hδ', hball⟩ :=
    Metric.continuousAt_iff.mp hcont_T (f₀ T / 2) (by linarith)
  let δ : ℝ := min (T / 2) (δ' / 2)
  have hδ_pos : 0 < δ := lt_min (by linarith) (by linarith)
  have hfeas : IsHankelFeasible c ε (T - δ) f₀ :=
    { toIsHankelEigenfn := heig
      nonzero := ⟨T, hT_pos.le, hf0_T.ne'⟩
      origin_sign := hf0_sign
      tail_nonneg := fun Δ hΔ => by
        rcases le_or_gt T Δ with h | h
        · exact hf0_tail Δ h
        · have hdist : dist Δ T < δ' := by
            rw [Real.dist_eq, abs_lt]
            constructor <;> [linarith [min_le_right (T / 2) (δ' / 2)]; linarith]
          have hfx := (abs_lt.mp (by simpa [Real.dist_eq] using hball hdist)).1
          linarith }
  have hle := hmin.least (T - δ) f₀ hfeas hf0_sites
  linarith

/-- **Proposition 7.9b (`gt:7.9b`)** for every real `c > 1/2`, both eigenvalues `ε = ±1`, and every
finite set of positive sites: every `IsHankelSiteMinimizer c ε sites T f` satisfies `f 0 = 0`. -/
theorem hankelExactOrigin_proved : HankelExactOrigin := by
  intro c hc ε hε sites hsites T f hmin
  have hc0 : 0 < c := by linarith
  have hf := hmin.feasible
  have hT_pos := hankel_site_minimizer_pos hc hmin
  by_contra hf0_ne
  rcases hε with rfl | rfl
  · have hf0_neg : f 0 < 0 := lt_of_le_of_ne (by linarith [hf.origin_sign]) hf0_ne
    have he1 : IsHankelEigenfn c 1 (fun s => Real.exp (-(2 * π * s))) :=
      (hankelKernelData hc).isRadialEigenfn_iff rfl 1 _ |>.1 (isRadialEigenfn_exp_bessel hc)
    let f₀ : ℝ → ℝ := fun Δ => f Δ + (-f 0) * Real.exp (-(2 * π * Δ))
    have hf₀_eig := isHankelEigenfn_add hc hf.toIsHankelEigenfn (he1.smul (-f 0))
    have hf₀_zero : f₀ 0 = 0 := by dsimp [f₀]; simp
    have hf₀_gt : ∀ Δ : ℝ, f Δ < f₀ Δ := fun Δ => by
      dsimp [f₀]
      have hpos : 0 < (-f 0) * Real.exp (-(2 * π * Δ)) := mul_pos (by linarith) (Real.exp_pos _)
      linarith
    exact exact_origin_contradiction hmin hT_pos hf₀_eig (by show 1 * f₀ 0 ≤ 0; rw [hf₀_zero, mul_zero])
      (fun s hs => (hf₀_gt s).le.trans' (hmin.sites_nonneg s hs))
      (fun Δ hΔ => (hf₀_gt Δ).le.trans' (hf.tail_nonneg Δ hΔ))
      ((hf.tail_nonneg T le_rfl).trans_lt (hf₀_gt T))
  · have hf0_pos : 0 < f 0 := lt_of_le_of_ne (by linarith [hf.origin_sign]) (Ne.symm hf0_ne)
    let m : ℝ := if hne : sites.Nonempty then min T (sites.inf' hne id) else T
    have hm_pos : 0 < m := by
      dsimp [m]
      split_ifs with hne
      · exact lt_min hT_pos ((Finset.lt_inf'_iff hne).mpr hsites)
      · exact hT_pos
    have hm_sites : ∀ s ∈ sites, m ≤ s := fun s hs => by
      dsimp [m]
      have hne : sites.Nonempty := ⟨s, hs⟩
      simp only [hne, reduceDIte]
      exact (min_le_right _ _).trans (Finset.inf'_le id hs)
    have hm_T : m ≤ T := by
      dsimp [m]
      split_ifs with hne
      · exact min_le_left _ _
      · exact le_rfl
    let b : ℝ := max 2 ((2 * c / (π * m) + 1) ^ 2)
    have hb2 : 2 ≤ b := le_max_left _ _
    have hb1 : 1 < b := by linarith
    have hb0 : 0 < b := by linarith
    let u_b : ℝ → ℝ := fun Δ => b ^ (-c) * Real.exp (-(2 * π / b * Δ)) - Real.exp (-(2 * π * b * Δ))
    have hu_eig : IsHankelEigenfn c (-1) u_b := isHankelEigenfn_recip_neg hc hb1
    have hu0 : u_b 0 = b ^ (-c) - 1 := by simp [u_b]
    have hbc_lt1 : b ^ (-c) < 1 := by
      rw [Real.rpow_neg hb0.le, inv_lt_one_iff₀]
      exact Or.inr (Real.one_lt_rpow hb1 hc0)
    have hden_pos : 0 < 1 - b ^ (-c) := by linarith
    let a : ℝ := f 0 / (1 - b ^ (-c))
    have ha_pos : 0 < a := div_pos hf0_pos hden_pos
    let f₀ : ℝ → ℝ := fun Δ => f Δ + a * u_b Δ
    have hf₀_eig := isHankelEigenfn_add hc hf.toIsHankelEigenfn (hu_eig.smul a)
    have hf₀_zero : f₀ 0 = 0 := by
      dsimp [f₀, a]
      rw [hu0]
      have h1 : 1 - b ^ (-c) ≠ 0 := hden_pos.ne'
      field_simp [h1]; ring
    have hu_pos_ge : ∀ Δ : ℝ, m ≤ Δ → 0 < u_b Δ := fun Δ hΔ => by
      dsimp [u_b]
      have hlog : c * Real.log b < 2 * π * (b - b⁻¹) * Δ := by
        have hsqrt_le : √b ≥ 2 * c / (π * m) + 1 := by
          have h1 : (2 * c / (π * m) + 1) ^ 2 ≤ b := le_max_right _ _
          have hpos : 0 ≤ 2 * c / (π * m) + 1 := by positivity
          exact Real.le_sqrt_of_sq_le h1
        have hlog_le : Real.log b ≤ 2 * √b := by
          have hsq : Real.sqrt b > 0 := Real.sqrt_pos.mpr hb0
          have h1 : Real.log (√b) ≤ √b := by linarith [Real.log_le_sub_one_of_pos hsq]
          have e : Real.log b = ((2 : ℕ) : ℝ) * Real.log (√b) := by
            rw [← Real.log_pow, Real.sq_sqrt hb0.le]
          have e2 : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
          rw [e, ← e2]; linarith
        have hsub : b / 2 ≤ b - b⁻¹ := by
          have hb_inv : b⁻¹ ≤ 1 / 2 := inv_le_of_inv_le₀ (by norm_num) (by linarith)
          linarith
        have hb_sub : 0 ≤ b - b⁻¹ := by linarith
        have h_b : 2 * c / (π * m) < √b := by linarith
        have h_lt1 : 2 * c < π * m * √b := by
          have := (div_lt_iff₀ (mul_pos Real.pi_pos hm_pos)).mp h_b
          linarith
        have h_lt2 : 2 * c * √b < π * m * b := by
          calc 2 * c * √b < (π * m * √b) * √b := mul_lt_mul_of_pos_right h_lt1 (Real.sqrt_pos.mpr hb0)
            _ = π * m * (√b * √b) := by ring
            _ = π * m * b := by rw [Real.mul_self_sqrt hb0.le]
        have h_lt3 : c * Real.log b < π * m * b :=
          (mul_le_mul_of_nonneg_left hlog_le hc0.le).trans_lt (by linarith)
        have h_le4 : π * m * b ≤ 2 * π * (b - b⁻¹) * m := by
          have := mul_le_mul_of_nonneg_left hsub (mul_pos (by positivity : (0 : ℝ) < 2 * π) hm_pos).le
          linarith
        have h_le5 : 2 * π * (b - b⁻¹) * m ≤ 2 * π * (b - b⁻¹) * Δ := by
          gcongr
        linarith
      have hdiv : b ^ (-c) * Real.exp (-(2 * π / b * Δ)) =
          Real.exp (-c * Real.log b - 2 * π / b * Δ) := by
        rw [Real.rpow_def_of_pos hb0, ← Real.exp_add]
        congr 1; ring
      rw [hdiv, sub_pos, Real.exp_lt_exp]
      have hid : -(2 * π * b * Δ) + (2 * π * (b - b⁻¹) * Δ) = -(2 * π / b * Δ) := by
        field_simp [hb0.ne']; ring
      linarith
    have hf₀_gt : ∀ Δ : ℝ, m ≤ Δ → f Δ < f₀ Δ := fun Δ hΔ => by
      dsimp [f₀]
      have hpos : 0 < a * u_b Δ := mul_pos ha_pos (hu_pos_ge Δ hΔ)
      linarith
    exact exact_origin_contradiction hmin hT_pos hf₀_eig (by show (-1 : ℝ) * f₀ 0 ≤ 0; rw [hf₀_zero, mul_zero])
      (fun s hs => (hf₀_gt s (hm_sites s hs)).le.trans' (hmin.sites_nonneg s hs))
      (fun Δ hΔ => (hf₀_gt Δ (hm_T.trans hΔ)).le.trans' (hf.tail_nonneg Δ hΔ))
      ((hf.tail_nonneg T le_rfl).trans_lt (hf₀_gt T hm_T))

/-- info: 'FormalResearch.SignUncertainty.hankelExactOrigin_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelExactOrigin_proved

end FormalResearch.SignUncertainty
