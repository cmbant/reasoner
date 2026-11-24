module

public import FormalResearch.SignUncertainty.HankelBootLine
public import FormalResearch.SignUncertainty.HankelBootTop

/-!
# The Hankel line estimate `hI_line` (M5-S6a)

`hankelBoot_line_bound`: for the shifted test `f_{k,ℓ}(u) = Ψ̃(u+ℓ)(1+u/R)^{k+1}`,
`∫_{-R}^{R} Re f_{k,ℓ} ≤ -(63/100) B₁^{(k)} - B₂ + C (k+1)/R + lobe + 70 R r_∞`, with `B₁^{(k)} = hankelBootB1k` (moment plus `2 R r_∞`),
`B₂ = hankelBootB2`, `C = 4e^{6/5} + 180`.  The explicit slack is `70 R r_∞` (`r_∞ = hankelRinf c`), assembled from the pieces
`hankelBoot_line_band/mid/right/tail` (each with its own explicit `r_∞` term), the top mass bound `hankel_psi_total_upper_tail` and
`hankelBoot_B2_eq`; `A ≤ (7/2) R` (`A` the Langer radius) is a hypothesis, true for `R ≥ (1/100)² c^{2/3}`.
-/

@[expose] public section

open MeasureTheory Set
open scoped Real Interval

namespace FormalResearch.SignUncertainty

lemma hankelBoot_exp_six_fifths_le : Real.exp (6 / 5 : ℝ) ≤ 25 / 4 := by
  have h := Real.exp_bound_div_one_sub_of_interval' (x := 3 / 5) (by norm_num) (by norm_num)
  have h2 : Real.exp (6 / 5 : ℝ) = Real.exp (3 / 5) * Real.exp (3 / 5) := by
    rw [← Real.exp_add]; norm_num
  have h3 : Real.exp (3 / 5 : ℝ) < 5 / 2 := by
    have : (1 : ℝ) / (1 - 3 / 5) = 5 / 2 := by norm_num
    rw [this] at h; exact h
  have h4 : 0 < Real.exp (3 / 5 : ℝ) := Real.exp_pos _
  rw [h2]; nlinarith

theorem hankelBoot_line_bound {c ε T u_T R ℓ : ℝ} {f : ℝ → ℝ} (hc : 3e6 ≤ c)
    (hf : IsHankelFeasible c ε T f) (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1)
    (hT : c * hankelXi c u_T = T) (hu0 : u_T ≤ 0) (hu3 : -3 ≤ u_T) (hR10 : 10 ≤ R)
    (hRA : R + 1 ≤ langerRadius c) (hAR : langerRadius c ≤ 7 / 2 * R)
    (hℓ0 : 0 ≤ ℓ) (hℓ1 : ℓ ≤ 1 / 2) {k : ℕ} (hk5 : 5 ≤ k) (hkR : (k : ℝ) ≤ R / 5) :
    ∫ x in (-R)..R, (hankelBootShifted c f R ℓ k (x : ℂ)).re ≤
      -(63 / 100 : ℝ) * hankelBootB1k c f R u_T k - hankelBootB2 c f R +
        (4 * Real.exp (6 / 5) + 180) * ((k : ℝ) + 1) / R + hankelLobe c + 70 * R * hankelRinf c := by
  have hc0 : 0 < c := by linarith
  have hc5 : (5000 : ℝ) ≤ c := by linarith
  have hfe := hf.toIsHankelEigenfn
  have hR_pos : 0 < R := by linarith
  have hr : 0 ≤ hankelRinf c := hankelRinf_nonneg hc5 hfe hε hM
  have hA_pos := langerRadius_pos hc0
  have hAA : |langerRadius c| ≤ langerRadius c := by rw [abs_of_pos hA_pos]
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
  -- shift
  have h_shift : ∫ x in (-R)..R, (hankelBootShifted c f R ℓ k (x : ℂ)).re =
      ∫ v in (-R + ℓ)..(R + ℓ), W v * hankelPsiR c f v := by
    have hrew : (fun x : ℝ => (hankelBootShifted c f R ℓ k (x : ℂ)).re) =
        fun x : ℝ => (1 + x / R) ^ (k + 1) * hankelPsiR c f (x + ℓ) := by
      ext x
      unfold hankelBootShifted hankelPsiR
      have hreal_pow : ((1 + (x : ℂ) / (R : ℂ)) ^ (k + 1)) = (((1 + x / R) ^ (k + 1) : ℝ) : ℂ) := by
        push_cast; ring
      rw [hreal_pow, show (x : ℂ) + (ℓ : ℂ) = ((x + ℓ : ℝ) : ℂ) by push_cast; ring,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      ring
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
      (hiW u_T 1 (by linarith [(hankel_radius_ge hc).1]) (by linarith) (by linarith [(hankel_radius_ge hc).1]))
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
      (hi (-R) (-R + ℓ) (by linarith) (by linarith) (by linarith)) (hi (-R + ℓ) (langerRadius c) hmR (by linarith) le_rfl)]
  -- pieces
  have hband := hankelBoot_line_band hc hf hε hM hT hu0 hu3 hR10 hRA hℓ0 hℓ1 k
  have hmid := hankelBoot_line_mid hc hf hε hM hT hu0 hu3 hR10 hRA hℓ0 hℓ1 k hkR
  have hright := hankelBoot_line_right hc hf hε hM hT hu0 hu3 hR10 hRA hℓ0 hℓ1 k hkR
  have htail := hankelBoot_line_tail hc hf hε hM hT hu0 hu3 hR10 hRA hℓ0 hℓ1 k
  have htailc := hankelBoot_tail_le_coeff hR10 hk5
  have hmR' : |-R| ≤ langerRadius c := by rw [abs_neg, abs_of_pos hR_pos]; exact hRA'
  have hu : |u_T| ≤ langerRadius c := hankelBoot_abs_uT hc hu0 hu3
  have hTa : T ≤ c * hankelXi c (-R) := by
    rw [← hT]; exact hankel_phi_anti hc0 hmR' hu (by linarith)
  have htop := hankel_psi_total_upper_tail hc hf hε hM hmR' hTa
  have hxi_pos : 0 < hankelXi c (-R) := hankelXi_pos hc0 hmR'
  have hB2eq : hankelBootB2 c f R = ∫ u in Ioi (c * hankelXi c (-R)), hankelRho0 c u * f u :=
    hankelBoot_B2_eq hc0 hfe hxi_pos (fun ξ hξ => hf.tail_nonneg _ (hTa.trans (by nlinarith)))
  -- numerical slack
  have hexp := hankelBoot_exp_six_fifths_le
  have hkr : ((k : ℝ) + 1) / R ≤ 3 / 10 := by
    rw [div_le_iff₀ hR_pos]; linarith
  have hq : 4 * Real.exp (6 / 5) * ((k : ℝ) + 1) / R ≤ 15 / 2 := by
    have : 4 * Real.exp (6 / 5) * ((k : ℝ) + 1) / R = 4 * Real.exp (6 / 5) * (((k : ℝ) + 1) / R) := by ring
    rw [this]
    have hE := Real.exp_pos (6 / 5 : ℝ)
    calc 4 * Real.exp (6 / 5) * (((k : ℝ) + 1) / R) ≤ 4 * (25 / 4) * (3 / 10) := by gcongr
      _ = 15 / 2 := by norm_num
  have hq0 : 0 ≤ 4 * Real.exp (6 / 5) * ((k : ℝ) + 1) / R := by positivity
  have hAr : 0 ≤ langerRadius c * hankelRinf c := mul_nonneg hA_pos.le hr
  have hmid2 : 4 * Real.exp (6 / 5) * ((k : ℝ) + 1) / R * (1 + 2 * langerRadius c * hankelRinf c) ≤
      4 * Real.exp (6 / 5) * ((k : ℝ) + 1) / R + 15 * (langerRadius c * hankelRinf c) := by
    have : 4 * Real.exp (6 / 5) * ((k : ℝ) + 1) / R * (2 * langerRadius c * hankelRinf c) ≤
        15 / 2 * (2 * (langerRadius c * hankelRinf c)) := by
      have h0 : 0 ≤ 2 * (langerRadius c * hankelRinf c) := by positivity
      calc 4 * Real.exp (6 / 5) * ((k : ℝ) + 1) / R * (2 * langerRadius c * hankelRinf c)
          = 4 * Real.exp (6 / 5) * ((k : ℝ) + 1) / R * (2 * (langerRadius c * hankelRinf c)) := by ring
        _ ≤ 15 / 2 * (2 * (langerRadius c * hankelRinf c)) := mul_le_mul_of_nonneg_right hq h0
    nlinarith
  have hArR : langerRadius c * hankelRinf c ≤ 7 / 2 * R * hankelRinf c :=
    mul_le_mul_of_nonneg_right hAR hr
  have h1r : hankelRinf c ≤ R / 10 * hankelRinf c := by
    have := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ R / 10 by linarith) hr
    linarith
  have hB1k : hankelBootB1k c f R u_T k = hankelBootMoment c f R u_T k + 2 * R * hankelRinf c := rfl
  rw [hsplit_W, hsplit3, hsplitΨ]
  rw [hB1k, hB2eq]
  dsimp only [W]
  have hE1 : (4 * Real.exp (6 / 5) + 180) * ((k : ℝ) + 1) / R =
      4 * Real.exp (6 / 5) * (((k : ℝ) + 1) / R) + 180 * (((k : ℝ) + 1) / R) := by ring
  have hE2 : 4 * Real.exp (6 / 5) * ((k : ℝ) + 1) / R = 4 * Real.exp (6 / 5) * (((k : ℝ) + 1) / R) := by ring
  have hE3 : 120 * ((k : ℝ) + 1) / R = 120 * (((k : ℝ) + 1) / R) := by ring
  have hE4 : 60 * ((k : ℝ) + 1) / R = 60 * (((k : ℝ) + 1) / R) := by ring
  linarith

/-- info: 'FormalResearch.SignUncertainty.hankelBoot_line_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBoot_line_bound

end FormalResearch.SignUncertainty
