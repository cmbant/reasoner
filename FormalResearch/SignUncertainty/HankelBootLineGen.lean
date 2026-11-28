module

public import FormalResearch.SignUncertainty.HankelBootBandGen

/-!
# Generalized Hankel moments and line estimate (`hI_line`) for `-U ≤ u_T ≤ 0`

Extends the band moment lemmas of `HankelBootData`, `HankelBootNumerics`, `HankelBootLine`, and
`HankelBootLineAsm` from `-3 ≤ u_T` to arbitrary `-U ≤ u_T ≤ 0` (`3 ≤ U`) when `U + 1 ≤ R`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set Metric
open scoped Real Interval

namespace FormalResearch.SignUncertainty

open FormalResearch.ModularBootstrap.ConcreteBootstrap

theorem hankelBoot_psi_ge_gen {c ε T u_T R : ℝ} {f : ℝ → ℝ} (hc : 3e6 ≤ c)
    (hf : IsHankelFeasible c ε T f) (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1)
    (hT : c * hankelXi c u_T = T) (huA : |u_T| ≤ langerRadius c)
    (hRA : R ≤ langerRadius c) {u : ℝ} (hu1 : -R ≤ u) (hu2 : u ≤ u_T) :
    -hankelRinf c ≤ hankelPsiR c f u := by
  have hc0 : 0 < c := by linarith
  have hc5 : (5000 : ℝ) ≤ c := by linarith
  have hx : |u| ≤ langerRadius c := hankelBoot_mem_Icc huA hRA ⟨hu1, hu2⟩
  refine hankel_psi_sign hc5 hf hε hM hx ?_
  rw [← hT]
  exact hankel_phi_anti hc0 hx huA hu2

theorem hankelBootB1_le_moment_gen {c ε T u_T R : ℝ} {f : ℝ → ℝ} (hc : 3e6 ≤ c)
    (hf : IsHankelFeasible c ε T f) (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1)
    (hT : c * hankelXi c u_T = T) (hu0 : u_T ≤ 0) (huA : |u_T| ≤ langerRadius c)
    (hR0 : 0 < R) (hRu : -R ≤ u_T) (hRA : R ≤ langerRadius c) :
    hankelBootB1 c f R u_T ≤
      (∫ u in (-R)..u_T, ((-u) / R) * hankelPsiR c f u) + R * hankelRinf c := by
  have hc0 : 0 < c := by linarith
  have hc5 : (5000 : ℝ) ≤ c := by linarith
  have hfe := hf.toIsHankelEigenfn
  have hr : 0 ≤ hankelRinf c := hankelRinf_nonneg hc5 hfe hε hM
  have hR := hankelBoot_R_mul_B1 hc0 hf hT huA hRA hR0 hRu
  have hΨc := hankelBoot_psiR_cont hc0 hfe huA hRA
  have hQc := hankelBoot_psiLead_cont hc0 hfe huA hRA
  have hint1 : IntervalIntegrable (fun x => (-x) * hankelPsiLead c f x) volume (-R) u_T :=
    ((continuousOn_id.neg).mul hQc).intervalIntegrable_of_Icc hRu
  have hint2 : IntervalIntegrable (fun x => (-x) * hankelPsiR c f x) volume (-R) u_T :=
    ((continuousOn_id.neg).mul hΨc).intervalIntegrable_of_Icc hRu
  have hpt : ∀ x ∈ Icc (-R) u_T,
      (-x) * hankelPsiLead c f x ≤ (-x) * hankelPsiR c f x + R * hankelRinf c := by
    intro x hx
    have hxA := hankelBoot_mem_Icc huA hRA hx
    have hd := abs_le.1 (hankelPsiR_sub_Q_le hc5 hfe hε hM hxA)
    have h1 : (-x) * (hankelPsiLead c f x - hankelPsiR c f x) ≤ (-x) * hankelRinf c :=
      mul_le_mul_of_nonneg_left (by linarith [hd.1]) (by linarith [hx.2, hu0])
    have h2 : (-x) * hankelRinf c ≤ R * hankelRinf c :=
      mul_le_mul_of_nonneg_right (by linarith [hx.1]) hr
    nlinarith [h1, h2]
  have hmono := intervalIntegral.integral_mono_on hRu hint1 (hint2.add intervalIntegrable_const) hpt
  rw [intervalIntegral.integral_add hint2 intervalIntegrable_const, intervalIntegral.integral_const,
    smul_eq_mul] at hmono
  have hJ : ∫ u in (-R)..u_T, ((-u) / R) * hankelPsiR c f u =
      R⁻¹ * ∫ u in (-R)..u_T, (-u) * hankelPsiR c f u := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u _ => ?_
    show ((-u) / R) * hankelPsiR c f u = R⁻¹ * ((-u) * hankelPsiR c f u)
    ring
  have hlen := mul_le_mul_of_nonneg_right (show u_T - -R ≤ R by linarith) (mul_nonneg hR0.le hr)
  have hkey : R * hankelBootB1 c f R u_T ≤
      (∫ u in (-R)..u_T, (-u) * hankelPsiR c f u) + R * (R * hankelRinf c) := by
    rw [hR]; linarith
  rw [hJ]
  calc hankelBootB1 c f R u_T = R⁻¹ * (R * hankelBootB1 c f R u_T) := by
        rw [← mul_assoc, inv_mul_cancel₀ hR0.ne', one_mul]
    _ ≤ R⁻¹ * ((∫ u in (-R)..u_T, (-u) * hankelPsiR c f u) + R * (R * hankelRinf c)) :=
        mul_le_mul_of_nonneg_left hkey (inv_nonneg.2 hR0.le)
    _ = R⁻¹ * (∫ u in (-R)..u_T, (-u) * hankelPsiR c f u) + R * hankelRinf c := by
        rw [mul_add]; congr 1; field_simp

theorem hankelBootMoment_ge_gen {c ε T u_T R : ℝ} {f : ℝ → ℝ} (hc : 3e6 ≤ c)
    (hf : IsHankelFeasible c ε T f) (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1)
    (hT : c * hankelXi c u_T = T) (hu0 : u_T ≤ 0) (huA : |u_T| ≤ langerRadius c)
    (hR0 : 0 < R) (hRu : -R ≤ u_T) (hRA : R ≤ langerRadius c) (k : ℕ) :
    -(R * hankelRinf c) ≤ hankelBootMoment c f R u_T k := by
  have hc0 : 0 < c := by linarith
  have hc5 : (5000 : ℝ) ≤ c := by linarith
  have hfe := hf.toIsHankelEigenfn
  have hr : 0 ≤ hankelRinf c := hankelRinf_nonneg hc5 hfe hε hM
  have hΨc := hankelBoot_psiR_cont hc0 hfe huA hRA
  have hmc : Continuous (fun u : ℝ => min 1 (((k : ℝ) + 1) * (-u) / R)) := by fun_prop
  have hint : IntervalIntegrable (fun u => min 1 (((k : ℝ) + 1) * (-u) / R) * hankelPsiR c f u)
      volume (-R) u_T :=
    (hmc.continuousOn.mul hΨc).intervalIntegrable_of_Icc hRu
  have hpt : ∀ u ∈ Icc (-R) u_T,
      -hankelRinf c ≤ min 1 (((k : ℝ) + 1) * (-u) / R) * hankelPsiR c f u := by
    intro u hu'
    have hψ := hankelBoot_psi_ge_gen hc hf hε hM hT huA hRA hu'.1 hu'.2
    have hm0 : 0 ≤ min 1 (((k : ℝ) + 1) * (-u) / R) :=
      le_min zero_le_one (div_nonneg (mul_nonneg (by positivity) (by linarith [hu'.2, hu0])) hR0.le)
    have hm1 : min 1 (((k : ℝ) + 1) * (-u) / R) ≤ 1 := min_le_left _ _
    have h1 : min 1 (((k : ℝ) + 1) * (-u) / R) * (-hankelRinf c) ≤
        min 1 (((k : ℝ) + 1) * (-u) / R) * hankelPsiR c f u :=
      mul_le_mul_of_nonneg_left hψ hm0
    have h2 : -hankelRinf c ≤ min 1 (((k : ℝ) + 1) * (-u) / R) * (-hankelRinf c) := by
      nlinarith [hm0, hm1, hr]
    linarith
  have hmono := intervalIntegral.integral_mono_on hRu intervalIntegrable_const hint hpt
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  unfold hankelBootMoment
  have hlen := mul_le_mul_of_nonneg_right (show u_T - -R ≤ R by linarith) hr
  linarith

theorem hankelBootB1_le_B1k_gen {c ε T u_T R : ℝ} {f : ℝ → ℝ} (hc : 3e6 ≤ c)
    (hf : IsHankelFeasible c ε T f) (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1)
    (hT : c * hankelXi c u_T = T) (hu0 : u_T ≤ 0) (huA : |u_T| ≤ langerRadius c)
    (hR0 : 0 < R) (hRu : -R ≤ u_T) (hRA : R ≤ langerRadius c) (k : ℕ) :
    hankelBootB1 c f R u_T ≤ hankelBootB1k c f R u_T k := by
  have hc0 : 0 < c := by linarith
  have hc5 : (5000 : ℝ) ≤ c := by linarith
  have hfe := hf.toIsHankelEigenfn
  have hr : 0 ≤ hankelRinf c := hankelRinf_nonneg hc5 hfe hε hM
  have hbase := hankelBootB1_le_moment_gen hc hf hε hM hT hu0 huA hR0 hRu hRA
  have hΨc := hankelBoot_psiR_cont hc0 hfe huA hRA
  have hmc : Continuous (fun u : ℝ => min 1 (((k : ℝ) + 1) * (-u) / R)) := by fun_prop
  have hint_a : IntervalIntegrable (fun u => ((-u) / R) * hankelPsiR c f u) volume (-R) u_T :=
    ((((continuousOn_id.neg).div_const R)).mul hΨc).intervalIntegrable_of_Icc hRu
  have hint_b : IntervalIntegrable (fun u => min 1 (((k : ℝ) + 1) * (-u) / R) * hankelPsiR c f u)
      volume (-R) u_T :=
    (hmc.continuousOn.mul hΨc).intervalIntegrable_of_Icc hRu
  have hpt : ∀ u ∈ Icc (-R) u_T,
      ((-u) / R) * hankelPsiR c f u ≤
        min 1 (((k : ℝ) + 1) * (-u) / R) * hankelPsiR c f u + hankelRinf c := by
    intro u hu'
    have hψ := hankelBoot_psi_ge_gen hc hf hε hM hT huA hRA hu'.1 hu'.2
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have ht0 : 0 ≤ (-u) / R := div_nonneg (by linarith [hu'.2, hu0]) hR0.le
    have ht1 : (-u) / R ≤ 1 := (div_le_one hR0).2 (by linarith [hu'.1])
    have htm : (-u) / R ≤ min 1 (((k : ℝ) + 1) * (-u) / R) := by
      refine le_min ht1 ?_
      rw [div_le_div_iff_of_pos_right hR0]
      nlinarith [mul_nonneg hk (show 0 ≤ -u by linarith [hu'.2, hu0])]
    have hm1 : min 1 (((k : ℝ) + 1) * (-u) / R) ≤ 1 := min_le_left _ _
    have h1 : ((-u) / R - min 1 (((k : ℝ) + 1) * (-u) / R)) * hankelPsiR c f u ≤
        ((-u) / R - min 1 (((k : ℝ) + 1) * (-u) / R)) * (-hankelRinf c) :=
      mul_le_mul_of_nonpos_left hψ (by linarith)
    have h2 : ((-u) / R - min 1 (((k : ℝ) + 1) * (-u) / R)) * (-hankelRinf c) ≤ hankelRinf c := by
      nlinarith [hr, hm1, ht0]
    nlinarith [h1, h2]
  have hmono := intervalIntegral.integral_mono_on hRu hint_a (hint_b.add intervalIntegrable_const) hpt
  rw [intervalIntegral.integral_add hint_b intervalIntegrable_const, intervalIntegral.integral_const,
    smul_eq_mul] at hmono
  unfold hankelBootB1k hankelBootMoment
  have hlen := mul_le_mul_of_nonneg_right (show u_T - -R ≤ R by linarith) hr
  linarith

theorem hankelBootB1k_nonneg_gen {c ε T u_T R : ℝ} {f : ℝ → ℝ} (hc : 3e6 ≤ c)
    (hf : IsHankelFeasible c ε T f) (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1)
    (hT : c * hankelXi c u_T = T) (hu0 : u_T ≤ 0) (huA : |u_T| ≤ langerRadius c)
    (hR0 : 0 < R) (hRu : -R ≤ u_T) (hRA : R ≤ langerRadius c) (k : ℕ) :
    0 ≤ hankelBootB1k c f R u_T k := by
  have hc5 : (5000 : ℝ) ≤ c := by linarith
  have hr : 0 ≤ hankelRinf c := hankelRinf_nonneg hc5 hf.toIsHankelEigenfn hε hM
  have hmom := hankelBootMoment_ge_gen hc hf hε hM hT hu0 huA hR0 hRu hRA k
  have hRr := mul_nonneg hR0.le hr
  unfold hankelBootB1k
  linarith

theorem hankelBootB1k_le_two_gen {c ε T u_T R : ℝ} {f : ℝ → ℝ} (hc : 3e6 ≤ c)
    (hf : IsHankelFeasible c ε T f) (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1)
    (hu0 : u_T ≤ 0) (huA : |u_T| ≤ langerRadius c)
    (hRu : -R ≤ u_T) (hRA : R ≤ langerRadius c) (hR0 : 0 < R)
    (hsmall : (2 * langerRadius c + 2 * R) * hankelRinf c ≤ 1) (k : ℕ) :
    hankelBootB1k c f R u_T k ≤ 2 := by
  have hc0 : 0 < c := by linarith
  have hc5 : (5000 : ℝ) ≤ c := by linarith
  have hfe := hf.toIsHankelEigenfn
  have hr : 0 ≤ hankelRinf c := hankelRinf_nonneg hc5 hfe hε hM
  have hA := langerRadius_pos hc0
  have hmass := hankel_psi_abs_mass hc5 hfe hε hM
  have hcont := continuousOn_hankelPsiR hc0 hfe
  have hi : ∀ a b : ℝ, -langerRadius c ≤ a → a ≤ b → b ≤ langerRadius c →
      IntervalIntegrable (fun x => |hankelPsiR c f x|) volume a b := fun a b ha hab hb =>
    (continuous_abs.comp_continuousOn (hcont.mono (Icc_subset_Icc ha hb))).intervalIntegrable_of_Icc hab
  have hRu' : -langerRadius c ≤ -R := by linarith
  have hu_A : u_T ≤ langerRadius c := (abs_le.1 huA).2
  have hs1 := intervalIntegral.integral_add_adjacent_intervals
    (hi (-langerRadius c) (-R) le_rfl hRu' (by linarith)) (hi (-R) u_T hRu' hRu hu_A)
  have hs2 := intervalIntegral.integral_add_adjacent_intervals
    (hi (-langerRadius c) u_T le_rfl (by linarith) hu_A) (hi u_T (langerRadius c) (by linarith) hu_A le_rfl)
  have hn1 : 0 ≤ ∫ x in (-langerRadius c)..(-R), |hankelPsiR c f x| :=
    intervalIntegral.integral_nonneg hRu' fun x _ => abs_nonneg _
  have hn2 : 0 ≤ ∫ x in u_T..(langerRadius c), |hankelPsiR c f x| :=
    intervalIntegral.integral_nonneg hu_A fun x _ => abs_nonneg _
  have hband : ∫ x in (-R)..u_T, |hankelPsiR c f x| ≤ 1 + 2 * langerRadius c * hankelRinf c := by
    linarith
  have hM1 : hankelBootMoment c f R u_T k ≤ ∫ x in (-R)..u_T, |hankelPsiR c f x| := by
    unfold hankelBootMoment
    refine intervalIntegral.integral_mono_on hRu ?_ (hi (-R) u_T hRu' hRu hu_A) fun x hx => ?_
    · exact (((continuous_const.min ((continuous_const.mul continuous_neg).div_const R)).continuousOn).mul
        (hcont.mono (Icc_subset_Icc hRu' hu_A))).intervalIntegrable_of_Icc hRu
    · have h0 : 0 ≤ min 1 (((k : ℝ) + 1) * (-x) / R) :=
        le_min zero_le_one (div_nonneg (mul_nonneg (by positivity) (by linarith [hx.2, hu0])) hR0.le)
      have h1 : min 1 (((k : ℝ) + 1) * (-x) / R) ≤ 1 := min_le_left _ _
      calc min 1 (((k : ℝ) + 1) * (-x) / R) * hankelPsiR c f x
          ≤ |min 1 (((k : ℝ) + 1) * (-x) / R) * hankelPsiR c f x| := le_abs_self _
        _ = min 1 (((k : ℝ) + 1) * (-x) / R) * |hankelPsiR c f x| := by rw [abs_mul, abs_of_nonneg h0]
        _ ≤ 1 * |hankelPsiR c f x| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ = |hankelPsiR c f x| := one_mul _
  unfold hankelBootB1k
  nlinarith

noncomputable def hankelLineCaGen (U : ℝ) : ℝ :=
  (U + 2) * Real.exp ((3 / 10 : ℝ) * (U + 2)) + 180

noncomputable def hankelLineRinfCoeffGen (U : ℝ) : ℝ :=
  21 / 10 * (U + 2) * Real.exp ((3 / 10 : ℝ) * (U + 2)) + 11

lemma hankelLineCaGen_pos {U : ℝ} (hU : 0 ≤ U) : 0 < hankelLineCaGen U := by
  unfold hankelLineCaGen; positivity

lemma hankelLineRinfCoeffGen_pos {U : ℝ} (hU : 0 ≤ U) : 0 < hankelLineRinfCoeffGen U := by
  unfold hankelLineRinfCoeffGen; positivity

theorem hankelBoot_line_band_gen {c ε T u_T R ℓ U : ℝ} {f : ℝ → ℝ} (hc : 3e6 ≤ c)
    (hf : IsHankelFeasible c ε T f) (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1)
    (hT : c * hankelXi c u_T = T) (hu0 : u_T ≤ 0) (huU : -U ≤ u_T) (huA : |u_T| ≤ langerRadius c)
    (hUR : U + 1 ≤ R) (hR10 : 10 ≤ R) (hRA : R + 1 ≤ langerRadius c)
    (hℓ0 : 0 ≤ ℓ) (hℓ1 : ℓ ≤ 1 / 2) (k : ℕ) :
    -(∫ v in (-R + ℓ)..u_T, (1 - (1 + (v - ℓ) / R) ^ (k + 1)) * hankelPsiR c f v)
      - (∫ v in (-R)..(-R + ℓ), hankelPsiR c f v)
    ≤ -(63 / 100 : ℝ) * hankelBootMoment c f R u_T k + (R + 1) * hankelRinf c := by
  have hc5 : (5000 : ℝ) ≤ c := by linarith
  have hc0 : 0 < c := by linarith
  have hR_pos : 0 < R := by linarith
  have hfe := hf.toIsHankelEigenfn
  have hr : 0 ≤ hankelRinf c := hankelRinf_nonneg hc5 hfe hε hM
  have hcont := continuousOn_hankelPsiR hc0 hfe
  have hsub : ∀ {a b : ℝ}, -R ≤ a → b ≤ R + ℓ → Icc a b ⊆ Icc (-(langerRadius c)) (langerRadius c) :=
    fun ha hb => Icc_subset_Icc (by linarith) (by linarith)
  have hI : ∀ {a b : ℝ}, -R ≤ a → a ≤ b → b ≤ R + ℓ →
      IntervalIntegrable (hankelPsiR c f) volume a b :=
    fun ha hab hb => (hcont.mono (hsub ha hb)).intervalIntegrable_of_Icc hab
  have hWc : Continuous (fun v : ℝ => (1 + (v - ℓ) / R) ^ (k + 1)) :=
    (continuous_const.add ((continuous_id.sub continuous_const).div_const R)).pow (k + 1)
  have hmc : Continuous (fun v : ℝ => min (1 : ℝ) (((k : ℝ) + 1) * (-v) / R)) :=
    continuous_const.min ((continuous_const.mul continuous_neg).div_const R)
  have hc63 : Continuous (fun _ : ℝ => (63 / 100 : ℝ)) := continuous_const
  have hI_w : ∀ {a b : ℝ}, -R ≤ a → a ≤ b → b ≤ R + ℓ →
      IntervalIntegrable (fun v : ℝ => (1 - (1 + (v - ℓ) / R) ^ (k + 1)) * hankelPsiR c f v)
        volume a b :=
    fun ha hab hb => ((continuousOn_const.sub hWc.continuousOn).mul
      (hcont.mono (hsub ha hb))).intervalIntegrable_of_Icc hab
  have hI_m0 : ∀ {a b : ℝ}, -R ≤ a → a ≤ b → b ≤ R + ℓ →
      IntervalIntegrable (fun v : ℝ => min (1 : ℝ) (((k : ℝ) + 1) * (-v) / R) * hankelPsiR c f v)
        volume a b :=
    fun ha hab hb => (hmc.continuousOn.mul (hcont.mono (hsub ha hb))).intervalIntegrable_of_Icc hab
  have hI_m : ∀ {a b : ℝ}, -R ≤ a → a ≤ b → b ≤ R + ℓ →
      IntervalIntegrable (fun v : ℝ => (63 / 100 : ℝ) * min (1 : ℝ) (((k : ℝ) + 1) * (-v) / R) *
        hankelPsiR c f v) volume a b :=
    fun ha hab hb => ((hc63.continuousOn.mul hmc.continuousOn).mul
      (hcont.mono (hsub ha hb))).intervalIntegrable_of_Icc hab
  have hAv : ∀ v ∈ Icc (-R) u_T, |v| ≤ langerRadius c := fun v hv =>
    abs_le.2 ⟨by linarith [hv.1], by linarith [hv.2, (abs_le.1 huA).2]⟩
  have hsign : ∀ v ∈ Icc (-R) u_T, -hankelRinf c ≤ hankelPsiR c f v := by
    intro v hv
    refine hankel_psi_sign hc5 hf hε hM (x := v) (hAv v hv) ?_
    rw [← hT]
    exact hankel_phi_anti hc0 (hAv v hv) huA hv.2
  have hnegRl_le_uT : -R + ℓ ≤ u_T := by linarith
  have hlowpt : ∀ v ∈ Icc (-R) (-R + ℓ),
      (63 / 100 : ℝ) * min (1 : ℝ) (((k : ℝ) + 1) * (-v) / R) * hankelPsiR c f v ≤
        (1 : ℝ) * hankelPsiR c f v + hankelRinf c := by
    intro v hv
    have hyv : 0 ≤ ((k : ℝ) + 1) * (-v) / R :=
      div_nonneg (mul_nonneg (by positivity) (by linarith [hv.2, hnegRl_le_uT, hu0])) hR_pos.le
    have hmin0 : 0 ≤ (63 / 100 : ℝ) * min (1 : ℝ) (((k : ℝ) + 1) * (-v) / R) :=
      mul_nonneg (by norm_num) (le_min zero_le_one hyv)
    have hmin1 : (63 / 100 : ℝ) * min (1 : ℝ) (((k : ℝ) + 1) * (-v) / R) ≤ 1 := by
      linarith [min_le_left (1 : ℝ) (((k : ℝ) + 1) * (-v) / R)]
    exact hankelBoot_weight_pt hmin0 hmin1 (le_refl _) (hsign v ⟨hv.1, by linarith [hv.2]⟩) hr
  have hmainpt : ∀ v ∈ Icc (-R + ℓ) u_T,
      (63 / 100 : ℝ) * min (1 : ℝ) (((k : ℝ) + 1) * (-v) / R) * hankelPsiR c f v ≤
        (1 - (1 + (v - ℓ) / R) ^ (k + 1)) * hankelPsiR c f v + hankelRinf c := by
    intro v hv
    have hv0 : v ≤ 0 := by linarith [hv.2]
    have hyv : 0 ≤ ((k : ℝ) + 1) * (-v) / R :=
      div_nonneg (mul_nonneg (by positivity) (by linarith)) hR_pos.le
    have hq : -1 ≤ (v - ℓ) / R := by rw [le_div_iff₀ hR_pos]; linarith [hv.1]
    have hbase : 0 ≤ 1 + (v - ℓ) / R := by linarith
    have hbase_le : 1 + (v - ℓ) / R ≤ Real.exp (-(-v / R)) := by
      have hv_div : (v - ℓ) / R ≤ v / R := div_le_div_of_nonneg_right (by linarith) hR_pos.le
      have hexp1 : 1 + v / R ≤ Real.exp (v / R) := by linarith [Real.add_one_le_exp (v / R)]
      rw [show -(-v / R) = v / R by ring]; linarith only [hv_div, hexp1]
    have hW_le : (1 + (v - ℓ) / R) ^ (k + 1) ≤ Real.exp (-(((k : ℝ) + 1) * (-v) / R)) := by
      calc (1 + (v - ℓ) / R) ^ (k + 1) ≤ (Real.exp (-(-v / R))) ^ (k + 1) :=
            pow_le_pow_left₀ hbase hbase_le _
        _ = Real.exp (((k + 1 : ℕ) : ℝ) * (-(-v / R))) := (Real.exp_nat_mul _ _).symm
        _ = Real.exp (-(((k : ℝ) + 1) * (-v) / R)) := by congr 1; push_cast; ring
    have hmin : (63 / 100 : ℝ) * min (1 : ℝ) (((k : ℝ) + 1) * (-v) / R) ≤
        1 - (1 + (v - ℓ) / R) ^ (k + 1) :=
      (sixtythree_hundredths_min_le_one_sub_exp hyv).trans (sub_le_sub_left hW_le 1)
    have hW0 : 0 ≤ (1 + (v - ℓ) / R) ^ (k + 1) := pow_nonneg hbase _
    have hmin0 : 0 ≤ (63 / 100 : ℝ) * min (1 : ℝ) (((k : ℝ) + 1) * (-v) / R) :=
      mul_nonneg (by norm_num) (le_min zero_le_one hyv)
    exact hankelBoot_weight_pt hmin0 hmin (by linarith) (hsign v ⟨by linarith [hv.1], hv.2⟩) hr
  have hlow_int := hankelBoot_weight_integral (r := hankelRinf c) (x := hankelPsiR c f)
    (a := fun v : ℝ => (63 / 100 : ℝ) * min (1 : ℝ) (((k : ℝ) + 1) * (-v) / R))
    (b := fun _ : ℝ => (1 : ℝ)) (p := -R) (q := -R + ℓ) (by linarith)
    (hI_m le_rfl (by linarith) (by linarith))
    (by simpa only [one_mul] using hI le_rfl (by linarith) (by linarith)) hlowpt
  have hmain_int := hankelBoot_weight_integral (r := hankelRinf c) (x := hankelPsiR c f)
    (a := fun v : ℝ => (63 / 100 : ℝ) * min (1 : ℝ) (((k : ℝ) + 1) * (-v) / R))
    (b := fun v : ℝ => 1 - (1 + (v - ℓ) / R) ^ (k + 1)) (p := -R + ℓ) (q := u_T) hnegRl_le_uT
    (hI_m (by linarith) hnegRl_le_uT (by linarith))
    (hI_w (by linarith) hnegRl_le_uT (by linarith)) hmainpt
  beta_reduce at hlow_int hmain_int
  simp only [one_mul] at hlow_int
  have eL : (∫ v in (-R)..(-R + ℓ), (63 / 100 : ℝ) * min (1 : ℝ) (((k : ℝ) + 1) * (-v) / R) *
      hankelPsiR c f v) = (63 / 100 : ℝ) * ∫ v in (-R)..(-R + ℓ),
        min (1 : ℝ) (((k : ℝ) + 1) * (-v) / R) * hankelPsiR c f v := by
    rw [← intervalIntegral.integral_const_mul]; congr 1; funext v; ring
  have eM : (∫ v in (-R + ℓ)..u_T, (63 / 100 : ℝ) * min (1 : ℝ) (((k : ℝ) + 1) * (-v) / R) *
      hankelPsiR c f v) = (63 / 100 : ℝ) * ∫ v in (-R + ℓ)..u_T,
        min (1 : ℝ) (((k : ℝ) + 1) * (-v) / R) * hankelPsiR c f v := by
    rw [← intervalIntegral.integral_const_mul]; congr 1; funext v; ring
  have hsplit : (∫ v in (-R)..u_T, min (1 : ℝ) (((k : ℝ) + 1) * (-v) / R) * hankelPsiR c f v) =
      (∫ v in (-R)..(-R + ℓ), min (1 : ℝ) (((k : ℝ) + 1) * (-v) / R) * hankelPsiR c f v) +
        ∫ v in (-R + ℓ)..u_T, min (1 : ℝ) (((k : ℝ) + 1) * (-v) / R) * hankelPsiR c f v :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hI_m0 le_rfl (by linarith) (by linarith)) (hI_m0 (by linarith) hnegRl_le_uT (by linarith))).symm
  unfold hankelBootMoment
  rw [hsplit]
  rw [eL] at hlow_int
  rw [eM] at hmain_int
  nlinarith [hlow_int, hmain_int, mul_nonneg (by linarith : (0 : ℝ) ≤ -u_T) hr, hr]

theorem hankelBoot_line_mid_gen {c ε T u_T R ℓ U : ℝ} {f : ℝ → ℝ} (hU : 0 ≤ U) (hc : 3e6 ≤ c)
    (hf : IsHankelFeasible c ε T f) (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1)
    (hu0 : u_T ≤ 0) (huU : -U ≤ u_T) (hUR : U + 1 ≤ R) (hR10 : 10 ≤ R)
    (hRA : R + 1 ≤ langerRadius c) (hℓ0 : 0 ≤ ℓ) (hℓ1 : ℓ ≤ 1 / 2) (k : ℕ) (hkR : (k : ℝ) ≤ R / 5) :
    -(∫ v in u_T..(1 : ℝ), (1 - (1 + (v - ℓ) / R) ^ (k + 1)) * hankelPsiR c f v)
    ≤ (U + 2) * Real.exp ((3 / 10 : ℝ) * (U + 2)) * ((k : ℝ) + 1) / R *
        (1 + 2 * langerRadius c * hankelRinf c) := by
  have hc5 : (5000 : ℝ) ≤ c := by linarith
  have hc0 : 0 < c := by linarith
  have hR_pos : 0 < R := by linarith
  have hfe := hf.toIsHankelEigenfn
  have hcont := continuousOn_hankelPsiR hc0 hfe
  have hr : 0 ≤ hankelRinf c := hankelRinf_nonneg hc5 hfe hε hM
  have hu_le1 : u_T ≤ 1 := by linarith
  have hsubA : Icc u_T (1 : ℝ) ⊆ Icc (-(langerRadius c)) (langerRadius c) :=
    Icc_subset_Icc (by linarith) (by linarith [(hankel_radius_ge hc).1])
  have hWc : Continuous (fun v : ℝ => (1 + (v - ℓ) / R) ^ (k + 1)) :=
    (continuous_const.add ((continuous_id.sub continuous_const).div_const R)).pow (k + 1)
  have hi_w : IntervalIntegrable (fun v : ℝ => (1 - (1 + (v - ℓ) / R) ^ (k + 1)) * hankelPsiR c f v)
      volume u_T 1 :=
    ((continuousOn_const.sub hWc.continuousOn).mul (hcont.mono hsubA)).intervalIntegrable_of_Icc hu_le1
  have hΨabs : IntervalIntegrable (fun v : ℝ => |hankelPsiR c f v|) volume u_T 1 :=
    (continuous_abs.comp_continuousOn (hcont.mono hsubA)).intervalIntegrable_of_Icc hu_le1
  have hC_nonneg : 0 ≤ (U + 2) * Real.exp ((3 / 10 : ℝ) * (U + 2)) * ((k : ℝ) + 1) / R := by positivity
  have hpt : ∀ v ∈ Icc u_T (1 : ℝ),
      |(1 - (1 + (v - ℓ) / R) ^ (k + 1)) * hankelPsiR c f v| ≤
        (U + 2) * Real.exp ((3 / 10 : ℝ) * (U + 2)) * ((k : ℝ) + 1) / R * |hankelPsiR c f v| := by
    intro v hv
    have hvl : |v - ℓ| ≤ U + 2 := abs_le.mpr ⟨by linarith [hv.1], by linarith [hv.2]⟩
    have hpow := abs_one_add_pow_sub_one_le ((v - ℓ) / R) (k + 1)
    have h_exp : ((k + 1 : ℕ) : ℝ) * |(v - ℓ) / R| ≤ (3 / 10 : ℝ) * (U + 2) := by
      rw [abs_div, abs_of_pos hR_pos]
      have hk1R : ((k + 1 : ℕ) : ℝ) / R ≤ 3 / 10 := by
        push_cast; rw [div_le_iff₀ hR_pos]; linarith
      calc ((k + 1 : ℕ) : ℝ) * (|v - ℓ| / R) = (((k + 1 : ℕ) : ℝ) / R) * |v - ℓ| := by ring
        _ ≤ (3 / 10 : ℝ) * (U + 2) := mul_le_mul hk1R hvl (abs_nonneg _) (by norm_num)
    have hW_bd : |1 - (1 + (v - ℓ) / R) ^ (k + 1)| ≤
        (U + 2) * Real.exp ((3 / 10 : ℝ) * (U + 2)) * ((k : ℝ) + 1) / R := by
      rw [abs_sub_comm]
      calc |(1 + (v - ℓ) / R) ^ (k + 1) - 1|
          ≤ ((k + 1 : ℕ) : ℝ) * |(v - ℓ) / R| * Real.exp (((k + 1 : ℕ) : ℝ) * |(v - ℓ) / R|) := hpow
        _ ≤ ((k + 1 : ℕ) : ℝ) * ((U + 2) / R) * Real.exp ((3 / 10 : ℝ) * (U + 2)) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left ?_ (by positivity))
              (Real.exp_le_exp.mpr h_exp) (Real.exp_pos _).le (by positivity)
            rw [abs_div, abs_of_pos hR_pos]
            exact div_le_div_of_nonneg_right hvl hR_pos.le
        _ = (U + 2) * Real.exp ((3 / 10 : ℝ) * (U + 2)) * ((k : ℝ) + 1) / R := by push_cast; ring
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hW_bd (abs_nonneg _)
  have hint_abs : |∫ v in u_T..(1 : ℝ), (1 - (1 + (v - ℓ) / R) ^ (k + 1)) * hankelPsiR c f v| ≤
      ∫ v in u_T..(1 : ℝ), |(1 - (1 + (v - ℓ) / R) ^ (k + 1)) * hankelPsiR c f v| := by
    simpa [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_integral_norm
      (f := fun v : ℝ => (1 - (1 + (v - ℓ) / R) ^ (k + 1)) * hankelPsiR c f v) (μ := volume) hu_le1
  have hpt2 : (∫ v in u_T..(1 : ℝ), |(1 - (1 + (v - ℓ) / R) ^ (k + 1)) * hankelPsiR c f v|) ≤
      ∫ v in u_T..(1 : ℝ), (U + 2) * Real.exp ((3 / 10 : ℝ) * (U + 2)) * ((k : ℝ) + 1) / R *
        |hankelPsiR c f v| :=
    intervalIntegral.integral_mono_on hu_le1 hi_w.abs (hΨabs.const_mul _) hpt
  have hfull : IntegrableOn (fun v : ℝ => |hankelPsiR c f v|) (Icc (-(langerRadius c)) (langerRadius c)) :=
    (continuous_abs.comp_continuousOn hcont).integrableOn_Icc
  have hL1 : (∫ v in u_T..(1 : ℝ), |hankelPsiR c f v|) ≤ 1 + 2 * langerRadius c * hankelRinf c := by
    have hsub : (∫ v in u_T..(1 : ℝ), |hankelPsiR c f v|) ≤
        ∫ v in (-(langerRadius c))..(langerRadius c), |hankelPsiR c f v| := by
      rw [intervalIntegral.integral_of_le hu_le1,
        intervalIntegral.integral_of_le (by linarith [(hankel_radius_ge hc).1])]
      exact setIntegral_mono_set (hfull.mono_set Ioc_subset_Icc_self)
        (Eventually.of_forall fun _ => abs_nonneg _)
        (Eventually.of_forall (Ioc_subset_Ioc (by linarith) (by linarith [(hankel_radius_ge hc).1])))
    exact hsub.trans (hankel_psi_abs_mass hc5 hfe hε hM)
  calc -(∫ v in u_T..(1 : ℝ), (1 - (1 + (v - ℓ) / R) ^ (k + 1)) * hankelPsiR c f v)
      ≤ |∫ v in u_T..(1 : ℝ), (1 - (1 + (v - ℓ) / R) ^ (k + 1)) * hankelPsiR c f v| := neg_le_abs _
    _ ≤ ∫ v in u_T..(1 : ℝ), |(1 - (1 + (v - ℓ) / R) ^ (k + 1)) * hankelPsiR c f v| := hint_abs
    _ ≤ ∫ v in u_T..(1 : ℝ), (U + 2) * Real.exp ((3 / 10 : ℝ) * (U + 2)) * ((k : ℝ) + 1) / R *
          |hankelPsiR c f v| := hpt2
    _ = (U + 2) * Real.exp ((3 / 10 : ℝ) * (U + 2)) * ((k : ℝ) + 1) / R *
          ∫ v in u_T..(1 : ℝ), |hankelPsiR c f v| := intervalIntegral.integral_const_mul _ _
    _ ≤ (U + 2) * Real.exp ((3 / 10 : ℝ) * (U + 2)) * ((k : ℝ) + 1) / R *
          (1 + 2 * langerRadius c * hankelRinf c) := mul_le_mul_of_nonneg_left hL1 hC_nonneg

theorem hankelBoot_line_right_gen {c ε : ℝ} {f : ℝ → ℝ} (hc : 3e6 ≤ c)
    (hf : IsHankelEigenfn c ε f) (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1)
    {R ℓ : ℝ} (hR10 : 10 ≤ R) (hRA : R + 1 ≤ langerRadius c) (hℓ0 : 0 ≤ ℓ) (hℓ1 : ℓ ≤ 1 / 2)
    (k : ℕ) (hkR : (k : ℝ) ≤ R / 5) :
    -(∫ v in (1 : ℝ)..(R + ℓ), (1 - (1 + (v - ℓ) / R) ^ (k + 1)) * hankelPsiR c f v)
    ≤ 120 * ((k : ℝ) + 1) / R := by
  have hc0 : 0 < c := by linarith
  have hR_pos : 0 < R := by linarith
  have hcont := continuousOn_hankelPsiR hc0 hf
  have h1R : (1 : ℝ) ≤ R + ℓ := by linarith
  have hsubA : Icc (1 : ℝ) (R + ℓ) ⊆ Icc (-(langerRadius c)) (langerRadius c) :=
    Icc_subset_Icc (by linarith [(hankel_radius_ge hc).1]) (by linarith)
  have hWc : Continuous (fun v : ℝ => (1 + (v - ℓ) / R) ^ (k + 1)) :=
    (continuous_const.add ((continuous_id.sub continuous_const).div_const R)).pow (k + 1)
  have hi_w : IntervalIntegrable (fun v : ℝ => (1 - (1 + (v - ℓ) / R) ^ (k + 1)) * hankelPsiR c f v)
      volume 1 (R + ℓ) :=
    ((continuousOn_const.sub hWc.continuousOn).mul (hcont.mono hsubA)).intervalIntegrable_of_Icc h1R
  have hpt : ∀ v ∈ Icc (1 : ℝ) (R + ℓ),
      |(1 - (1 + (v - ℓ) / R) ^ (k + 1)) * hankelPsiR c f v| ≤
        60 * (((k : ℝ) + 1) / R) * Real.exp (-(8 / 15 : ℝ) * v) := by
    intro v hv
    have hv1 : 1 ≤ v := hv.1
    have hvA : v ≤ langerRadius c := by linarith [hv.2]
    have hΨb := hankelBoot_psi_real_env hc hf hε hM hv1 hvA
    have hvl : |v - ℓ| ≤ v := abs_le.mpr ⟨by linarith, by linarith⟩
    have hpow := abs_one_add_pow_sub_one_le ((v - ℓ) / R) (k + 1)
    have h_exp_310 : ((k + 1 : ℕ) : ℝ) * |(v - ℓ) / R| ≤ (3 / 10 : ℝ) * v := by
      rw [abs_div, abs_of_pos hR_pos]
      have hk1R : ((k + 1 : ℕ) : ℝ) / R ≤ 3 / 10 := by push_cast; rw [div_le_iff₀ hR_pos]; linarith
      calc ((k + 1 : ℕ) : ℝ) * (|v - ℓ| / R) = (((k + 1 : ℕ) : ℝ) / R) * |v - ℓ| := by ring
        _ ≤ (3 / 10 : ℝ) * v := mul_le_mul hk1R hvl (abs_nonneg _) (by norm_num)
    have hW_bd : |1 - (1 + (v - ℓ) / R) ^ (k + 1)| ≤
        (((k : ℝ) + 1) / R) * v * Real.exp ((3 / 10 : ℝ) * v) := by
      rw [abs_sub_comm]
      calc |(1 + (v - ℓ) / R) ^ (k + 1) - 1|
          ≤ ((k + 1 : ℕ) : ℝ) * |(v - ℓ) / R| * Real.exp (((k + 1 : ℕ) : ℝ) * |(v - ℓ) / R|) := hpow
        _ ≤ (((k + 1 : ℕ) : ℝ) * (v / R)) * Real.exp ((3 / 10 : ℝ) * v) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left ?_ (by positivity))
              (Real.exp_le_exp.mpr h_exp_310) (Real.exp_pos _).le (by positivity)
            rw [abs_div, abs_of_pos hR_pos]
            exact div_le_div_of_nonneg_right hvl hR_pos.le
        _ = (((k : ℝ) + 1) / R) * v * Real.exp ((3 / 10 : ℝ) * v) := by push_cast; ring
    have hexp_eq : Real.exp ((3 / 10 : ℝ) * v) * Real.exp (-(4 / 3 : ℝ) * v ^ (3 / 2 : ℝ)) =
        Real.exp ((3 / 10 : ℝ) * v - (4 / 3 : ℝ) * v ^ (3 / 2 : ℝ)) := by rw [← Real.exp_add]; congr 1; ring
    calc |(1 - (1 + (v - ℓ) / R) ^ (k + 1)) * hankelPsiR c f v|
        = |1 - (1 + (v - ℓ) / R) ^ (k + 1)| * |hankelPsiR c f v| := abs_mul _ _
      _ ≤ ((((k : ℝ) + 1) / R) * v * Real.exp ((3 / 10 : ℝ) * v)) *
            (60 * Real.exp (-(4 / 3 : ℝ) * v ^ (3 / 2 : ℝ))) :=
          mul_le_mul hW_bd hΨb (abs_nonneg _) (by positivity)
      _ = (60 * (((k : ℝ) + 1) / R)) *
            (v * Real.exp ((3 / 10 : ℝ) * v - (4 / 3 : ℝ) * v ^ (3 / 2 : ℝ))) := by rw [← hexp_eq]; ring
      _ ≤ (60 * (((k : ℝ) + 1) / R)) * Real.exp (-(8 / 15 : ℝ) * v) :=
          mul_le_mul_of_nonneg_left (hankelBoot_exp_right hv1) (by positivity)
      _ = 60 * (((k : ℝ) + 1) / R) * Real.exp (-(8 / 15 : ℝ) * v) := rfl
  have hint_abs : |∫ v in (1 : ℝ)..(R + ℓ), (1 - (1 + (v - ℓ) / R) ^ (k + 1)) * hankelPsiR c f v| ≤
      ∫ v in (1 : ℝ)..(R + ℓ), |(1 - (1 + (v - ℓ) / R) ^ (k + 1)) * hankelPsiR c f v| := by
    simpa [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_integral_norm
      (f := fun v : ℝ => (1 - (1 + (v - ℓ) / R) ^ (k + 1)) * hankelPsiR c f v) (μ := volume) h1R
  have hmono : (∫ v in (1 : ℝ)..(R + ℓ), |(1 - (1 + (v - ℓ) / R) ^ (k + 1)) * hankelPsiR c f v|) ≤
      ∫ v in (1 : ℝ)..(R + ℓ), 60 * (((k : ℝ) + 1) / R) * Real.exp (-(8 / 15 : ℝ) * v) :=
    intervalIntegral.integral_mono_on h1R hi_w.abs
      ((continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).intervalIntegrable
        1 (R + ℓ)) hpt
  have hK0 : 0 ≤ 60 * (((k : ℝ) + 1) / R) := by positivity
  calc -(∫ v in (1 : ℝ)..(R + ℓ), (1 - (1 + (v - ℓ) / R) ^ (k + 1)) * hankelPsiR c f v)
      ≤ |∫ v in (1 : ℝ)..(R + ℓ), (1 - (1 + (v - ℓ) / R) ^ (k + 1)) * hankelPsiR c f v| := neg_le_abs _
    _ ≤ ∫ v in (1 : ℝ)..(R + ℓ), |(1 - (1 + (v - ℓ) / R) ^ (k + 1)) * hankelPsiR c f v| := hint_abs
    _ ≤ ∫ v in (1 : ℝ)..(R + ℓ), 60 * (((k : ℝ) + 1) / R) * Real.exp (-(8 / 15 : ℝ) * v) := hmono
    _ ≤ 2 * (60 * (((k : ℝ) + 1) / R)) := hankelBoot_exp_int_le hK0 h1R
    _ = 120 * ((k : ℝ) + 1) / R := by ring

theorem hankelBoot_line_tail_gen {c ε : ℝ} {f : ℝ → ℝ} (hc : 3e6 ≤ c)
    (hf : IsHankelEigenfn c ε f) (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1)
    {R ℓ : ℝ} (hR10 : 10 ≤ R) (hRA : R + 1 ≤ langerRadius c) (hℓ0 : 0 ≤ ℓ) (hℓ1 : ℓ ≤ 1 / 2) :
    -(∫ v in (R + ℓ)..(langerRadius c), hankelPsiR c f v)
    ≤ (6 / 5 : ℝ) * 60 * Real.exp (-(5 / 6 : ℝ) * R) := by
  have hc0 : 0 < c := by linarith
  have hcont := continuousOn_hankelPsiR hc0 hf
  have hab : R + ℓ ≤ langerRadius c := by linarith
  have hsubA : Icc (R + ℓ) (langerRadius c) ⊆ Icc (-(langerRadius c)) (langerRadius c) :=
    Icc_subset_Icc (by linarith [(hankel_radius_ge hc).1]) (by linarith)
  have hΨi : IntervalIntegrable (hankelPsiR c f) volume (R + ℓ) (langerRadius c) :=
    (hcont.mono hsubA).intervalIntegrable_of_Icc hab
  have hpt : ∀ v ∈ Icc (R + ℓ) (langerRadius c),
      -hankelPsiR c f v ≤ 60 * Real.exp (-(5 / 6 : ℝ) * v) := by
    intro v hv
    have hv1 : 1 ≤ v := by linarith [hv.1]
    have hb := hankelBoot_psi_real_env hc hf hε hM hv1 hv.2
    have hv32 : v ≤ v ^ (3 / 2 : ℝ) := by
      conv_lhs => rw [← Real.rpow_one v]
      exact Real.rpow_le_rpow_of_exponent_le hv1 (by norm_num)
    have hex : Real.exp (-(4 / 3 : ℝ) * v ^ (3 / 2 : ℝ)) ≤ Real.exp (-(5 / 6 : ℝ) * v) :=
      Real.exp_le_exp.mpr (by linarith)
    have habs : -hankelPsiR c f v ≤ |hankelPsiR c f v| := neg_le_abs _
    linarith [mul_le_mul_of_nonneg_left hex (by norm_num : (0 : ℝ) ≤ 60)]
  have hmono : -(∫ v in (R + ℓ)..(langerRadius c), hankelPsiR c f v) ≤
      ∫ v in (R + ℓ)..(langerRadius c), 60 * Real.exp (-(5 / 6 : ℝ) * v) := by
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_mono_on hab hΨi.neg
      ((continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).intervalIntegrable
        _ _) hpt
  have hderiv : ∀ x ∈ uIcc (R + ℓ) (langerRadius c),
      HasDerivAt (fun t : ℝ => -(6 / 5 : ℝ) * 60 * Real.exp (-(5 / 6 : ℝ) * t))
        (60 * Real.exp (-(5 / 6 : ℝ) * x)) x := fun x _ => by
    have hd := ((hasDerivAt_id x).const_mul (-(5 / 6 : ℝ))).exp.const_mul (-(6 / 5 : ℝ) * 60)
    refine hd.congr_deriv ?_
    simp only [id_eq]; ring
  have heval := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).intervalIntegrable
      _ _)
  have h1 : Real.exp (-(5 / 6 : ℝ) * (R + ℓ)) ≤ Real.exp (-(5 / 6 : ℝ) * R) :=
    Real.exp_le_exp.mpr (by linarith)
  have h2 : 0 ≤ (6 / 5 : ℝ) * 60 * Real.exp (-(5 / 6 : ℝ) * langerRadius c) := by positivity
  linarith

theorem hankelBoot_line_bound_gen {c ε T u_T R ℓ U : ℝ} {f : ℝ → ℝ} (hU : 0 ≤ U) (hc : 3e6 ≤ c)
    (hf : IsHankelFeasible c ε T f) (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1)
    (hT : c * hankelXi c u_T = T) (hu0 : u_T ≤ 0) (huU : -U ≤ u_T) (huA : |u_T| ≤ langerRadius c)
    (hUR : U + 1 ≤ R) (hR10 : 10 ≤ R) (hRA : R + 1 ≤ langerRadius c)
    (hAR : langerRadius c ≤ 7 / 2 * R) (hℓ0 : 0 ≤ ℓ) (hℓ1 : ℓ ≤ 1 / 2)
    {k : ℕ} (hk5 : 5 ≤ k) (hkR : (k : ℝ) ≤ R / 5) :
    ∫ x in (-R)..R, (hankelBootShifted c f R ℓ k (x : ℂ)).re ≤
      -(63 / 100 : ℝ) * hankelBootB1k c f R u_T k - hankelBootB2 c f R +
        hankelLineCaGen U * ((k : ℝ) + 1) / R + hankelLobe c +
        hankelLineRinfCoeffGen U * R * hankelRinf c := by
  have hc0 : 0 < c := by linarith
  have hc5 : (5000 : ℝ) ≤ c := by linarith
  have hfe := hf.toIsHankelEigenfn
  have hR_pos : 0 < R := by linarith
  have hr : 0 ≤ hankelRinf c := hankelRinf_nonneg hc5 hfe hε hM
  have hA_pos := langerRadius_pos hc0
  have hRA' : R ≤ langerRadius c := by linarith
  have hcont := continuousOn_hankelPsiR hc0 hfe
  have hi : ∀ a b : ℝ, -langerRadius c ≤ a → a ≤ b → b ≤ langerRadius c →
      IntervalIntegrable (hankelPsiR c f) volume a b := fun a b ha hab hb =>
    (hcont.mono (Icc_subset_Icc ha hb)).intervalIntegrable_of_Icc hab
  let W : ℝ → ℝ := fun v => (1 + (v - ℓ) / R) ^ (k + 1)
  have hW_cont : Continuous W :=
    (continuous_const.add ((continuous_id.sub continuous_const).div_const R)).pow (k + 1)
  have hiW : ∀ a b : ℝ, -langerRadius c ≤ a → a ≤ b → b ≤ langerRadius c →
      IntervalIntegrable (fun v => (1 - W v) * hankelPsiR c f v) volume a b := fun a b ha hab hb =>
    ((continuousOn_const.sub hW_cont.continuousOn).mul (hcont.mono (Icc_subset_Icc ha hb))).intervalIntegrable_of_Icc hab
  have h_shift : ∫ x in (-R)..R, (hankelBootShifted c f R ℓ k (x : ℂ)).re =
      ∫ v in (-R + ℓ)..(R + ℓ), W v * hankelPsiR c f v := by
    have hrew : (fun x : ℝ => (hankelBootShifted c f R ℓ k (x : ℂ)).re) =
        fun x : ℝ => (1 + x / R) ^ (k + 1) * hankelPsiR c f (x + ℓ) := by
      ext x
      unfold hankelBootShifted hankelPsiR
      have hreal_pow : ((1 + (x : ℂ) / (R : ℂ)) ^ (k + 1)) = (((1 + x / R) ^ (k + 1) : ℝ) : ℂ) := by
        push_cast; ring
      rw [hreal_pow, show (x : ℂ) + (ℓ : ℂ) = ((x + ℓ : ℝ) : ℂ) by push_cast; ring,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]; ring
    rw [hrew]
    simpa [W, add_sub_cancel_right] using
      intervalIntegral.integral_comp_add_right
        (fun v : ℝ => (1 + (v - ℓ) / R) ^ (k + 1) * hankelPsiR c f v) ℓ (a := -R) (b := R)
  rw [h_shift]
  have hmR : -langerRadius c ≤ -R + ℓ := by linarith
  have hRlA : R + ℓ ≤ langerRadius c := by linarith
  have hnRl : -R + ℓ ≤ u_T := by linarith
  have h1RA : (1 : ℝ) ≤ R + ℓ := by linarith
  have hsplit_W : ∫ v in (-R + ℓ)..(R + ℓ), W v * hankelPsiR c f v =
      (∫ v in (-R + ℓ)..(R + ℓ), hankelPsiR c f v) -
        ∫ v in (-R + ℓ)..(R + ℓ), (1 - W v) * hankelPsiR c f v := by
    rw [← intervalIntegral.integral_sub (hi _ _ hmR (by linarith) hRlA) (hiW _ _ hmR (by linarith) hRlA)]
    exact intervalIntegral.integral_congr fun v _ => by ring
  have hsplit3 : ∫ v in (-R + ℓ)..(R + ℓ), (1 - W v) * hankelPsiR c f v =
      (∫ v in (-R + ℓ)..u_T, (1 - W v) * hankelPsiR c f v) +
        (∫ v in u_T..(1 : ℝ), (1 - W v) * hankelPsiR c f v) +
        ∫ v in (1 : ℝ)..(R + ℓ), (1 - W v) * hankelPsiR c f v := by
    have h12 := intervalIntegral.integral_add_adjacent_intervals
      (hiW (-R + ℓ) u_T hmR hnRl (by linarith [(hankel_radius_ge hc).1]))
      (hiW u_T 1 (by linarith) (by linarith) (by linarith [(hankel_radius_ge hc).1]))
    have h23 := intervalIntegral.integral_add_adjacent_intervals
      (hiW (-R + ℓ) 1 hmR (by linarith) (by linarith [(hankel_radius_ge hc).1]))
      (hiW 1 (R + ℓ) (by linarith) h1RA hRlA)
    linarith only [h12, h23]
  have hsplitΨ : (∫ v in (-R + ℓ)..(R + ℓ), hankelPsiR c f v) =
      (∫ v in (-R + ℓ)..(langerRadius c), hankelPsiR c f v) -
        ∫ v in (R + ℓ)..(langerRadius c), hankelPsiR c f v := by
    have := intervalIntegral.integral_add_adjacent_intervals
      (hi (-R + ℓ) (R + ℓ) hmR (by linarith) hRlA) (hi (R + ℓ) (langerRadius c) (by linarith) hRlA le_rfl)
    linarith only [this]
  have hsplitTop : (∫ v in (-R)..(langerRadius c), hankelPsiR c f v) =
      (∫ v in (-R)..(-R + ℓ), hankelPsiR c f v) + ∫ v in (-R + ℓ)..(langerRadius c), hankelPsiR c f v := by
    rw [intervalIntegral.integral_add_adjacent_intervals
      (hi (-R) (-R + ℓ) (by linarith) (by linarith) (by linarith))
      (hi (-R + ℓ) (langerRadius c) hmR (by linarith) le_rfl)]
  have hband := hankelBoot_line_band_gen hc hf hε hM hT hu0 huU huA hUR hR10 hRA hℓ0 hℓ1 k
  have hmid := hankelBoot_line_mid_gen hU hc hf hε hM hu0 huU hUR hR10 hRA hℓ0 hℓ1 k hkR
  have hright := hankelBoot_line_right_gen hc hfe hε hM hR10 hRA hℓ0 hℓ1 k hkR
  have htail := hankelBoot_line_tail_gen hc hfe hε hM hR10 hRA hℓ0 hℓ1
  have htailc := hankelBoot_tail_le_coeff hR10 hk5
  have hmR' : |-R| ≤ langerRadius c := by rw [abs_neg, abs_of_pos hR_pos]; exact hRA'
  have hTa : T ≤ c * hankelXi c (-R) := by
    rw [← hT]; exact hankel_phi_anti hc0 hmR' huA (by linarith)
  have htop := hankel_psi_total_upper_tail hc hf hε hM hmR' hTa
  have hxi_pos : 0 < hankelXi c (-R) := hankelXi_pos hc0 hmR'
  have hB2eq : hankelBootB2 c f R = ∫ u in Ioi (c * hankelXi c (-R)), hankelRho0 c u * f u :=
    hankelBoot_B2_eq hc0 hfe hxi_pos (fun ξ hξ => hf.tail_nonneg _ (hTa.trans (by nlinarith)))
  set Cmid : ℝ := (U + 2) * Real.exp ((3 / 10 : ℝ) * (U + 2)) with hCmid
  have hCmid_nn : 0 ≤ Cmid := mul_nonneg (by linarith) (Real.exp_pos _).le
  have hkr : ((k : ℝ) + 1) / R ≤ 3 / 10 := by rw [div_le_iff₀ hR_pos]; linarith
  have hmid_bd : Cmid * ((k : ℝ) + 1) / R * (2 * langerRadius c * hankelRinf c) ≤
      21 / 10 * Cmid * R * hankelRinf c := by
    have h1 : Cmid * ((k : ℝ) + 1) / R ≤ Cmid * (3 / 10) := by
      rw [show Cmid * ((k : ℝ) + 1) / R = Cmid * (((k : ℝ) + 1) / R) by ring]
      exact mul_le_mul_of_nonneg_left hkr hCmid_nn
    have h2 : 2 * langerRadius c * hankelRinf c ≤ 7 * R * hankelRinf c := by
      have : 2 * langerRadius c ≤ 7 * R := by linarith
      exact mul_le_mul_of_nonneg_right this hr
    calc Cmid * ((k : ℝ) + 1) / R * (2 * langerRadius c * hankelRinf c)
        ≤ (Cmid * (3 / 10)) * (7 * R * hankelRinf c) :=
          mul_le_mul h1 h2 (mul_nonneg (mul_nonneg (by linarith) hA_pos.le) hr)
            (mul_nonneg hCmid_nn (by norm_num))
      _ = 21 / 10 * Cmid * R * hankelRinf c := by ring
  have hmid2 : Cmid * ((k : ℝ) + 1) / R * (1 + 2 * langerRadius c * hankelRinf c) ≤
      Cmid * ((k : ℝ) + 1) / R + 21 / 10 * Cmid * R * hankelRinf c := by
    nlinarith
  have hArR : langerRadius c * hankelRinf c ≤ 7 / 2 * R * hankelRinf c :=
    mul_le_mul_of_nonneg_right hAR hr
  have h1r : 1 * hankelRinf c ≤ R / 10 * hankelRinf c :=
    mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ R / 10 by linarith) hr
  have hB1k : hankelBootB1k c f R u_T k = hankelBootMoment c f R u_T k + 2 * R * hankelRinf c := rfl
  rw [hsplit_W, hsplit3, hsplitΨ, hB1k, hB2eq]
  dsimp only [W]
  have hE1 : hankelLineCaGen U * ((k : ℝ) + 1) / R =
      Cmid * (((k : ℝ) + 1) / R) + 180 * (((k : ℝ) + 1) / R) := by
    unfold hankelLineCaGen; rw [← hCmid]; ring
  have hE2 : Cmid * ((k : ℝ) + 1) / R = Cmid * (((k : ℝ) + 1) / R) := by ring
  have hE3 : 120 * ((k : ℝ) + 1) / R = 120 * (((k : ℝ) + 1) / R) := by ring
  have hE4 : 60 * ((k : ℝ) + 1) / R = 60 * (((k : ℝ) + 1) / R) := by ring
  have hE5 : hankelLineRinfCoeffGen U * R * hankelRinf c =
      (21 / 10 * Cmid + 11) * R * hankelRinf c := by
    unfold hankelLineRinfCoeffGen
    rw [mul_assoc (21 / 10 : ℝ), ← hCmid]
  have hRr0 : 0 ≤ R * hankelRinf c := mul_nonneg hR_pos.le hr
  linarith

/-- info: 'FormalResearch.SignUncertainty.hankelBoot_line_bound_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBoot_line_bound_gen

end FormalResearch.SignUncertainty
