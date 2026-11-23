module

public import FormalResearch.SignUncertainty.HankelPhaseSeries
public import FormalResearch.SignUncertainty.HankelLangerIdentity
public import FormalResearch.SignUncertainty.HankelLangerChartMain
public import FormalResearch.CohnElkies.MellinKernel

/-!
# The strip function `g` of `mat:T3` is the Langer series (`gt:7.7b` (0), identification)

`HankelLangerIdentity` proves `log(tan(πz/2)/(πz/2)) = P(z)` for `‖z‖ < 1/8` only (a proof device).  Here the
identity theorem on the half disc `{‖ζ‖ < 1, Re ζ > 0}` gives `tan(πζ/2)/(πζ/2) = exp(gSer η ζ)` there, and since
`‖gSer ζ‖ < π` for `‖ζ‖ ≤ 0.35` the principal logarithm of `CohnElkies.stripG` equals the series:
`stripG ζ = gSer etaC ζ` (`stripG_eq_gSer`).
-/

@[expose] public section

open Complex Set Filter Topology Metric
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

lemma gSer_etaC_eq_Pser (ζ : ℂ) : gSer etaC ζ = Pser ζ := by
  unfold gSer Pser psW
  rw [← tsum_mul_left]
  refine tsum_congr fun j => ?_
  unfold langerc
  rw [show 2 * j + 2 = 2 + 2 * j by ring, pow_add, pow_mul]; ring

/-- Norm of the series: `‖g(ζ)‖ ≤ a/(1-a)·1.1` for `a = ‖ζ‖² < 1`... crude, used for `‖ζ‖ ≤ 0.35`. -/
lemma norm_gSer_le {ζ : ℂ} (hζ : ‖ζ‖ ≤ 0.35) : ‖gSer etaC ζ‖ < Real.pi := by
  have hu : ‖ζ ^ 2‖ ≤ 0.35 ^ 2 := by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hζ 2
  have h1 : ‖ζ ^ 2‖ < 1 := lt_of_le_of_lt hu (by norm_num)
  have hb : ∀ j, 1 ≤ j → |etaC j / ((j : ℝ) + 1)| ≤ 1 := fun j _ => abs_eta_div_le langerEta_etaC j
  have h2 := norm_psW_sub_le (a := fun j => etaC j / ((j : ℝ) + 1)) (B := 1) hb h1
  have h0 : (etaC 0 / (((0 : ℕ) : ℝ) + 1)) = π ^ 2 / 12 := by simp [etaC_zero]
  have h3 : ‖psW (fun j => etaC j / ((j : ℝ) + 1)) (ζ ^ 2)‖ ≤
      π ^ 2 / 12 + 1 * ‖ζ ^ 2‖ / (1 - ‖ζ ^ 2‖) := by
    have := norm_le_insert' (psW (fun j => etaC j / ((j : ℝ) + 1)) (ζ ^ 2))
      ((etaC 0 / (((0 : ℕ) : ℝ) + 1) : ℝ) : ℂ)
    rw [h0] at this h2
    have h4 : ‖((π ^ 2 / 12 : ℝ) : ℂ)‖ = π ^ 2 / 12 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  rw [one_mul] at h3
  unfold gSer
  rw [norm_mul, norm_pow]
  have hm : ‖ζ ^ 2‖ / (1 - ‖ζ ^ 2‖) ≤ 0.35 ^ 2 / (1 - 0.35 ^ 2) := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; nlinarith [norm_nonneg (ζ ^ 2)]
  have hpi2 : π ^ 2 / 12 ≤ 1 := by
    have : π ^ 2 < 3.15 ^ 2 := pow_lt_pow_left₀ Real.pi_lt_d2 Real.pi_pos.le (by norm_num)
    linarith
  have hζ0 := norm_nonneg ζ
  have : ‖ζ‖ ^ 2 * ‖psW (fun j => etaC j / ((j : ℝ) + 1)) (ζ ^ 2)‖ ≤ 0.35 ^ 2 * (1 + 0.35 ^ 2 / (1 - 0.35 ^ 2)) := by
    have hq : ‖ζ‖ ^ 2 ≤ 0.35 ^ 2 := pow_le_pow_left₀ hζ0 hζ 2
    have : ‖psW (fun j => etaC j / ((j : ℝ) + 1)) (ζ ^ 2)‖ ≤ 1 + 0.35 ^ 2 / (1 - 0.35 ^ 2) := by
      linarith
    exact mul_le_mul hq this (norm_nonneg _) (by norm_num)
  nlinarith [Real.pi_gt_three]

/-- The half disc `{‖ζ‖ < 1, Re ζ > 0}`. -/
def halfDisc : Set ℂ := {ζ : ℂ | ‖ζ‖ < 1 ∧ 0 < ζ.re}

lemma isOpen_halfDisc : IsOpen halfDisc :=
  (isOpen_lt continuous_norm continuous_const).inter (isOpen_lt continuous_const Complex.continuous_re)

lemma convex_halfDisc : Convex ℝ halfDisc := by
  have : halfDisc = ball (0 : ℂ) 1 ∩ {c : ℂ | 0 < c.re} := by
    ext ζ; simp [halfDisc]
  rw [this]
  exact (convex_ball (0 : ℂ) 1).inter (convex_halfSpace_re_gt 0)

lemma halfDisc_ne_zero {ζ : ℂ} (h : ζ ∈ halfDisc) : ζ ≠ 0 := by
  rintro rfl; simp [halfDisc] at h

lemma differentiableOn_gSer : DifferentiableOn ℂ (gSer etaC) (ball (0 : ℂ) 1) := fun ζ hζ =>
  (hasDerivAt_gSer langerEta_etaC (by simpa using hζ)).differentiableAt.differentiableWithinAt

lemma differentiableAt_langerU {ζ : ℂ} (hζ0 : ζ ≠ 0) (hζ : ‖ζ‖ < 1) : DifferentiableAt ℂ langerU ζ := by
  unfold langerU
  have hcos : Complex.cos (π * ζ / 2) ≠ 0 := by
    have := cos_pi_half_ne_zero hζ
    rwa [← mul_div_assoc] at this
  have hd : DifferentiableAt ℂ (fun z : ℂ => (π : ℂ) * z / 2) ζ := by fun_prop
  have h1 : DifferentiableAt ℂ (fun z : ℂ => Complex.tan (π * z / 2)) ζ :=
    DifferentiableAt.comp ζ (Complex.differentiableAt_tan.2 hcos) hd
  refine h1.div (by fun_prop) ?_
  have := pi_ne_zero_c
  simpa [hζ0] using this

/-- `tan(πζ/2)/(πζ/2) = exp(g(ζ))` on the half disc (identity theorem). -/
theorem langerU_eq_exp_gSer {ζ : ℂ} (hζ : ζ ∈ halfDisc) :
    langerU ζ = Complex.exp (gSer etaC ζ) := by
  have hF : AnalyticOnNhd ℂ langerU halfDisc := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) isOpen_halfDisc
    exact (differentiableAt_langerU (halfDisc_ne_zero hz) hz.1).differentiableWithinAt
  have hG : AnalyticOnNhd ℂ (fun ζ => Complex.exp (gSer etaC ζ)) halfDisc := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) isOpen_halfDisc
    have : DifferentiableAt ℂ (gSer etaC) z :=
      (hasDerivAt_gSer langerEta_etaC hz.1).differentiableAt
    exact this.cexp.differentiableWithinAt
  have hz0 : ((1 / 16 : ℝ) : ℂ) ∈ halfDisc := by
    refine ⟨?_, ?_⟩
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]; norm_num
    · simp
  have hev : langerU =ᶠ[𝓝 ((1 / 16 : ℝ) : ℂ)] fun ζ => Complex.exp (gSer etaC ζ) := by
    have hopen : IsOpen (ball (0 : ℂ) (1 / 8) ∩ {z : ℂ | z ≠ 0}) :=
      isOpen_ball.inter isOpen_compl_singleton
    have hmem : ((1 / 16 : ℝ) : ℂ) ∈ ball (0 : ℂ) (1 / 8) ∩ {z : ℂ | z ≠ 0} := by
      refine ⟨?_, ?_⟩
      · rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]; norm_num
      · simp
    filter_upwards [hopen.mem_nhds hmem] with z hz
    rw [langerU_eq_exp hz.2 (mem_ball_zero_iff.1 hz.1), gSer_etaC_eq_Pser]
  exact hF.eqOn_of_preconnected_of_eventuallyEq hG convex_halfDisc.isPreconnected hz0 hev hζ

/-- **`stripG` is the Langer series** on the half disc `‖ζ‖ ≤ 0.35`, `Re ζ > 0`. -/
theorem stripG_eq_gSer {ζ : ℂ} (hζ : ‖ζ‖ ≤ 0.35) (hre : 0 < ζ.re) : stripG ζ = gSer etaC ζ := by
  have hmem : ζ ∈ halfDisc := ⟨lt_of_le_of_lt hζ (by norm_num), hre⟩
  have hne := halfDisc_ne_zero hmem
  unfold stripG
  rw [if_neg hne]
  have : Complex.tan (π * ζ / 2) / (π * ζ / 2) = Complex.exp (gSer etaC ζ) := langerU_eq_exp_gSer hmem
  rw [this]
  have hP := norm_gSer_le hζ
  have him := Complex.abs_im_le_norm (gSer etaC ζ)
  have hab := abs_le.mp (le_trans him hP.le)
  apply Complex.log_exp
  · have : -Real.pi < (gSer etaC ζ).im := by
      by_contra hc; push Not at hc
      have h2 : |(gSer etaC ζ).im| < Real.pi := lt_of_le_of_lt him hP
      rw [abs_lt] at h2; linarith [h2.1]
    exact this
  · exact hab.2

/-- info: 'FormalResearch.SignUncertainty.stripG_eq_gSer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stripG_eq_gSer

/-- `S̃(ζ) = ∑ η_j/((j+1)(2j+3)) ζ^{2j+3}`. -/
noncomputable def SSer (η : ℕ → ℝ) (ζ : ℂ) : ℂ :=
  ζ ^ 3 * psW (fun j => η j / (((j : ℝ) + 1) * (2 * (j : ℝ) + 3))) (ζ ^ 2)

lemma abs_eta_div2_le (h : LangerEta η) (j : ℕ) : |η j / (((j : ℝ) + 1) * (2 * (j : ℝ) + 3))| ≤ 1 := by
  rw [abs_of_pos (div_pos (h.pos j) (by positivity)), div_le_one (by positivity)]
  have := h.le_one j
  have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  nlinarith

lemma three_psW_add_two_mul_psWD {a : ℕ → ℝ} {B : ℝ} (ha : ∀ j, |a j| ≤ B) {u : ℂ} (hu : ‖u‖ < 1) :
    3 * psW a u + 2 * (u * psWD a u) = psW (fun j => (2 * (j : ℝ) + 3) * a j) u := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (ha 0)
  have s1 := (summable_psW (a := a) (B := B) ha hu).of_norm
  have s2 : Summable (fun j : ℕ => (((2 * (j : ℝ) + 3) * a j : ℝ) : ℂ) * u ^ j) := by
    have hb : ∀ j : ℕ, |(2 * (j : ℝ) + 3) * a j| ≤ (2 * j + 3) * B := by
      intro j; rw [abs_mul, abs_of_pos (by positivity)]
      exact mul_le_mul_of_nonneg_left (ha j) (by positivity)
    refine Summable.of_norm_bounded ((hasSum_odd_weight (a := ‖u‖) (norm_nonneg u) hu).summable.mul_left B) ?_
    intro j
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    calc |(2 * (j : ℝ) + 3) * a j| * ‖u‖ ^ j ≤ (2 * j + 3) * B * ‖u‖ ^ j :=
          mul_le_mul_of_nonneg_right (hb j) (by positivity)
      _ = B * ((2 * (j : ℝ) + 3) * ‖u‖ ^ j) := by ring
  have hP : psW a u = (a 0 : ℂ) + ∑' j : ℕ, (a (j + 1) : ℂ) * u ^ (j + 1) := by
    unfold psW; rw [s1.tsum_eq_zero_add]; simp
  have hQ : psW (fun j => (2 * (j : ℝ) + 3) * a j) u =
      (3 * a 0 : ℂ) + ∑' j : ℕ, (((2 * ((j + 1 : ℕ) : ℝ) + 3) * a (j + 1) : ℝ) : ℂ) * u ^ (j + 1) := by
    unfold psW; rw [s2.tsum_eq_zero_add]; simp
  have hD : u * psWD a u = ∑' j : ℕ, ((a (j + 1) : ℂ) * ((j + 1 : ℕ) : ℂ)) * u ^ (j + 1) := by
    unfold psWD; rw [← tsum_mul_left]; refine tsum_congr fun j => ?_; ring
  have s3 : Summable (fun j : ℕ => (a (j + 1) : ℂ) * u ^ (j + 1)) := (summable_nat_add_iff 1).2 s1
  have s4 : Summable (fun j : ℕ => (((2 * ((j + 1 : ℕ) : ℝ) + 3) * a (j + 1) : ℝ) : ℂ) * u ^ (j + 1)) :=
    (summable_nat_add_iff 1).2 s2
  have s5 : Summable (fun j : ℕ => ((a (j + 1) : ℂ) * ((j + 1 : ℕ) : ℂ)) * u ^ (j + 1)) := by
    have := (s4.sub (s3.mul_left 3)).mul_left ((1 / 2 : ℂ))
    refine this.congr fun j => ?_
    push_cast; ring
  rw [hP, hD, hQ]
  have : ∑' j : ℕ, (((2 * ((j + 1 : ℕ) : ℝ) + 3) * a (j + 1) : ℝ) : ℂ) * u ^ (j + 1) =
      3 * ∑' j : ℕ, (a (j + 1) : ℂ) * u ^ (j + 1) +
        2 * ∑' j : ℕ, ((a (j + 1) : ℂ) * ((j + 1 : ℕ) : ℂ)) * u ^ (j + 1) := by
    rw [← tsum_mul_left, ← tsum_mul_left, ← Summable.tsum_add (s3.mul_left 3) (s5.mul_left 2)]
    refine tsum_congr fun j => ?_
    push_cast; ring
  rw [this]; ring

lemma hasDerivAt_SSer (h : LangerEta η) {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    HasDerivAt (SSer η) (gSer η ζ) ζ := by
  have hu : ‖ζ ^ 2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg ζ]
  set c : ℕ → ℝ := fun j => η j / (((j : ℝ) + 1) * (2 * (j : ℝ) + 3)) with hc
  have hC := hasDerivAt_psW (a := c) (B := 1) (abs_eta_div2_le h) hu
  have h3 : HasDerivAt (fun ζ : ℂ => ζ ^ 3) (3 * ζ ^ 2) ζ := by simpa using hasDerivAt_pow 3 ζ
  have h2 : HasDerivAt (fun ζ : ℂ => ζ ^ 2) (2 * ζ) ζ := by simpa using hasDerivAt_pow 2 ζ
  have hC' : HasDerivAt (psW c) (psWD c (ζ ^ 2)) ((fun ζ : ℂ => ζ ^ 2) ζ) := hC
  have hcomp := HasDerivAt.comp (h₂ := psW c) (h := fun ζ : ℂ => ζ ^ 2) ζ hC' h2
  have hm := h3.mul hcomp
  have hfun : SSer η = (fun ζ : ℂ => ζ ^ 3) * (psW c ∘ fun ζ : ℂ => ζ ^ 2) := by
    funext x; simp [SSer, hc]
  rw [hfun]
  convert hm using 1
  have key := three_psW_add_two_mul_psWD (a := c) (B := 1) (abs_eta_div2_le h) hu
  have hcb : (fun j : ℕ => (2 * (j : ℝ) + 3) * c j) = fun j => η j / ((j : ℝ) + 1) := by
    funext j; simp only [hc]; field_simp
  rw [hcb] at key
  have hg : gSer η ζ = ζ ^ 2 * psW (fun j => η j / ((j : ℝ) + 1)) (ζ ^ 2) := rfl
  rw [hg, ← key]
  simp only [Function.comp_apply]
  ring

lemma SSer_zero (η : ℕ → ℝ) : SSer η 0 = 0 := by simp [SSer]

lemma gSer_zero (η : ℕ → ℝ) : gSer η 0 = 0 := by simp [gSer]

/-- `S̃₀(ζ) = S̃(ζ)` (series) on `‖ζ‖ ≤ 0.35`, `Re ζ > 0`. -/
theorem stripS0Tilde_eq_SSer {ζ : ℂ} (hζ : ‖ζ‖ ≤ 0.35) (hre : 0 < ζ.re) :
    stripS0Tilde ζ = SSer etaC ζ := by
  unfold stripS0Tilde
  have hcong : ∫ s in (0 : ℝ)..1, stripG ((s : ℂ) * ζ) * ζ = ∫ s in (0 : ℝ)..1, gSer etaC ((s : ℂ) * ζ) * ζ := by
    refine intervalIntegral.integral_congr (fun s hs => ?_)
    rw [Set.uIcc_of_le zero_le_one] at hs
    rcases eq_or_lt_of_le hs.1 with h0 | hpos
    · rw [← h0]; simp [stripG, gSer_zero]
    · have : ‖(s : ℂ) * ζ‖ ≤ 0.35 := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
        calc s * ‖ζ‖ ≤ 1 * 0.35 := mul_le_mul hs.2 hζ (norm_nonneg _) zero_le_one
          _ = 0.35 := one_mul _
      rw [stripG_eq_gSer this (by simp [Complex.mul_re]; exact mul_pos hpos hre)]
  rw [hcong]
  have hnormB : ∀ s ∈ Set.uIcc (0 : ℝ) 1, ‖(s : ℂ) * ζ‖ < 1 := by
    intro s hs
    rw [Set.uIcc_of_le zero_le_one] at hs
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
    calc s * ‖ζ‖ ≤ 1 * 0.35 := mul_le_mul hs.2 hζ (norm_nonneg _) zero_le_one
      _ < 1 := by norm_num
  have hd : ∀ s ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => SSer etaC ((s : ℂ) * ζ))
      (gSer etaC ((s : ℂ) * ζ) * ζ) s := by
    intro s hs
    have hS := hasDerivAt_SSer langerEta_etaC (hnormB s hs)
    have hp : HasDerivAt (fun s : ℝ => (s : ℂ) * ζ) ζ s := by
      simpa using ((hasDerivAt_id s).ofReal_comp).mul_const ζ
    have := hS.scomp s hp
    have e : (fun s : ℝ => SSer etaC ((s : ℂ) * ζ)) = SSer etaC ∘ fun s : ℝ => (s : ℂ) * ζ := rfl
    rw [e]
    convert this using 1
    simp [smul_eq_mul, mul_comm]
  have hcont : ContinuousOn (fun s : ℝ => gSer etaC ((s : ℂ) * ζ) * ζ) (Set.uIcc 0 1) := by
    refine ContinuousOn.mul ?_ continuousOn_const
    exact differentiableOn_gSer.continuousOn.comp (by fun_prop : Continuous fun s : ℝ => (s : ℂ) * ζ).continuousOn
      (fun s hs => mem_ball_zero_iff.2 (hnormB s hs))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hcont.intervalIntegrable]
  simp [SSer_zero]

/-- info: 'FormalResearch.SignUncertainty.stripS0Tilde_eq_SSer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stripS0Tilde_eq_SSer

/-- info: 'FormalResearch.SignUncertainty.hasDerivAt_SSer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_SSer

end FormalResearch.SignUncertainty
