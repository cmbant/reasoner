module

public import FormalResearch.ModularBootstrap.Upper.Membership.FWM
public import FormalResearch.ModularBootstrap.Upper.Membership.HankelTransform
public import FormalResearch.ModularBootstrap.Upper.Hankel.EdgeGlobalBound
public import FormalResearch.ModularBootstrap.Upper.Hankel.EdgeGlobalBoundP
public import FormalResearch.ModularBootstrap.Upper.Hankel.EdgeExample

/-!
# Lemma `K7`, decay and membership for the comb `h₀ = sech²(πb/2) B` (`cmb:K7`)

Source: `comb_estimates.tex`, Lemma `K7` (`cmb:K7`).  For an inner Blaschke comb `B` with the
properties (i), (iii) of `InnerCombHyp` the profile `u(t) = h₀(√(3t/c'))` and its order-zero Hankel
transform `ĥ = hankelTransform 1 u` satisfy `|u| + |ĥ| ≤ C(c) e^{-c' L(x) - πx}`
(`t = c' x²/3`, `L(x) = 2πx/3`):

* `|u| ≤ 4 e^{-πx} |B|` and (iii) (`combProfile_decay`);
* `|ĥ| ≤ 2π ∫ |u|` on the compact range `x ≤ ξ_*/2` (`norm_fourier_le_integral_norm`);
* `ξ_*/2 ≤ x ≤ x_I = ξ_* + c'^{-3/5}`: Lemma `SD_G` (`edge_global_bound_xiStar`, `C_E = 1` from `|B| = 1`
  on `E_+`) together with the link `edgeHankel = hankelTransform 1` (`hankelTransform_one_eq_edgeHankel`);
* `x ≥ x_I`: Lemma `SD_V` (two-saddle descent).  This is the named hypothesis
  `SaddleTailBound c' B` below: `|ĥ₀(t)| ≤ C(c) e^{-c' L - πx}` for `x ≥ x_I`.  It is derived from the
  amplitude hypotheses of `SD_V` in `SaddleTail.lean` (`saddleTailBound_of_sdv`).

`k7_membership_vacuum` assembles the decay with `fwM_of_decay`: `g = ½(h₀ - ĥ₀) ∈ Ā`, and the
vacuum identity `g_vac = ½ h_{0,vac} - π ∫ h₀ V` with `|h_{0,vac}| ≤ 8` for `Q = (1-q)²`
(`2^m · 2` in general).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real FourierTransform

namespace FormalResearch.ModularBootstrap.Upper.Membership

open FormalResearch.ModularBootstrap.Crossing FormalResearch.ModularBootstrap.WeightAxioms
  FormalResearch.ModularBootstrap.Upper.Hankel

/-! ### The comb and its hypotheses (i), (iii) -/

/-- The comb `h₀(b) = sech²(πb/2) B(b)`. -/
noncomputable def combH0 (B : ℂ → ℂ) (b : ℂ) : ℂ := sechSqProfile b * B b

/-- Hypotheses (i) and (iii) of Lemma `K7` used for the decay and membership:
(i) `B` even and real on `ℝ`, analytic on `|Im b| < 7/8`, `|B| ≤ 1` on `|Im b| ≤ 1/2` and `|B| = 1` on
`E_+` (the statement on `E_-` follows by reflection and is not used), and
(iii) `sup_{x ≥ 0} |B(x)| e^{c' L(x)} < ∞` with `L(x) = 2πx/3`. -/
structure InnerCombHyp (c' : ℝ) (B : ℂ → ℂ) : Prop where
  even : ∀ r : ℝ, B (-(r : ℂ)) = B (r : ℂ)
  real : ∀ r : ℝ, (B (r : ℂ)).im = 0
  holo : DifferentiableOn ℂ B {b : ℂ | |b.im| < 7 / 8}
  bound : ∀ b : ℂ, |b.im| ≤ 1 / 2 → ‖B b‖ ≤ 1
  unit_edge : ∀ v : ℝ, ‖B ((v : ℂ) + Complex.I / 2)‖ = 1
  tail : ∃ C : ℝ, ∀ x : ℝ, 0 ≤ x → ‖B (x : ℂ)‖ * Real.exp (c' * (2 * π * x / 3)) ≤ C

/-- The real radial profile `u(t) = h₀(√(3t/c'))` of the comb. -/
noncomputable def combProfile (c' : ℝ) (B : ℂ → ℂ) (t : ℝ) : ℝ :=
  (combH0 B ((xOf c' t : ℝ) : ℂ)).re

/-- The threshold `x_I = ξ_* + c'^{-3/5}`. -/
noncomputable def xI (c' : ℝ) : ℝ := xiStar + c' ^ (-(3 / 5 : ℝ))

/-- **Named hypothesis (conclusion of Lemma `FW-SD`, order `p`).**  The order-`p` transform of the comb
satisfies `‖(𝓗_{p+1} h₀)(c' x²/3)‖ ≤ C(c) e^{-c' L(x) - πx}` for `x ≥ x_I = ξ_* + c'^{-3/5}`, with
`𝓗_{p+1} h₀ = edgeHankelP p c' h₀` the `J_p`-form of the Hankel transform.  In `upper_transfer.tex` this is
`fw:e1.4` of Lemma `FW-SD` (`fw:SDp`) with `𝒜_x e^{c' L} ≤ C(c) |sech²(π b_x/2)| ≤ C(c) e^{-πx}` and
`R_p(x) ≤ C_p`; at `p = 0` it is `(SD.3)--(SD.4)` of `SD_V`.  It is derived from the amplitude hypotheses in
`SaddleTail.lean` (`saddleTailBoundP_of_fwsd`). -/
def SaddleTailBoundP (p : ℕ) (c' : ℝ) (B : ℂ → ℂ) : Prop :=
  ∃ C : ℝ, ∀ x : ℝ, xI c' ≤ x →
    ‖edgeHankelP p c' (combH0 B) (c' * x ^ 2 / 3)‖ ≤
      C * Real.exp (-(c' * (2 * π * x / 3)) - π * x)

/-- **Named hypothesis (conclusion of Lemma `SD_V`).**  The order-zero case of `SaddleTailBoundP`:
`‖ĥ₀(c' x²/3)‖ ≤ C(c) e^{-c' L(x) - πx}` for `x ≥ x_I = ξ_* + c'^{-3/5}`, with `ĥ₀ = edgeHankel c' h₀`
the `J₀`-form of the Hankel transform. -/
def SaddleTailBound (c' : ℝ) (B : ℂ → ℂ) : Prop := SaddleTailBoundP 0 c' B

lemma saddleTailBound_iff (c' : ℝ) (B : ℂ → ℂ) :
    SaddleTailBound c' B ↔ ∃ C : ℝ, ∀ x : ℝ, xI c' ≤ x →
      ‖edgeHankel c' (combH0 B) (c' * x ^ 2 / 3)‖ ≤ C * Real.exp (-(c' * (2 * π * x / 3)) - π * x) := by
  unfold SaddleTailBound SaddleTailBoundP
  simp only [edgeHankelP_zero]

/-! ### Elementary facts on the comb -/

lemma cosh_ne_zero_closedStrip {b : ℂ} (hb : |b.im| ≤ 1 / 2) : Complex.cosh (π * b / 2) ≠ 0 := by
  rcases le_total 0 b.im with h | h
  · exact cosh_ne_zero_strip h (abs_le.mp hb).2
  · have h1 : Complex.cosh (π * b / 2) = Complex.cosh (π * (-b) / 2) := by
      rw [show (π : ℂ) * (-b) / 2 = -((π : ℂ) * b / 2) by ring, Complex.cosh_neg]
    rw [h1]
    have hb2 := (abs_le.mp hb).1
    exact cosh_ne_zero_strip (by simp only [Complex.neg_im]; linarith)
      (by simp only [Complex.neg_im]; linarith)

lemma sechSqProfile_ofReal (x : ℝ) :
    sechSqProfile (x : ℂ) = ((1 / Real.cosh (π * x / 2) ^ 2 : ℝ) : ℂ) := by
  unfold sechSqProfile
  rw [show (π : ℂ) * (x : ℂ) / 2 = ((π * x / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cosh]
  push_cast; rfl

lemma sechSqProfile_neg (b : ℂ) : sechSqProfile (-b) = sechSqProfile b := by
  unfold sechSqProfile
  rw [show (π : ℂ) * -b / 2 = -((π : ℂ) * b / 2) by ring, Complex.cosh_neg]

lemma norm_sechSqProfile_ofReal_le (x : ℝ) : ‖sechSqProfile (x : ℂ)‖ ≤ 4 * Real.exp (-π * |x|) := by
  rw [sechSqProfile_ofReal, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have h := two_div_cosh_sq_le (π * x / 2)
  have hu : -2 * |π * x / 2| = -π * |x| := by
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_two]; ring
  rw [hu] at h
  have hc : 0 < Real.cosh (π * x / 2) ^ 2 := by have := Real.cosh_pos (π * x / 2); positivity
  have : 1 / Real.cosh (π * x / 2) ^ 2 = (2 / Real.cosh (π * x / 2) ^ 2) / 2 := by ring
  rw [this]; linarith

variable {c' : ℝ} {B : ℂ → ℂ}

lemma InnerCombHyp.continuous_B_real (hB : InnerCombHyp c' B) :
    Continuous fun x : ℝ => B (x : ℂ) :=
  hB.holo.continuousOn.comp_continuous Complex.continuous_ofReal
    (fun x => by simp)

lemma InnerCombHyp.combH0_real (hB : InnerCombHyp c' B) (x : ℝ) :
    (combH0 B (x : ℂ)).im = 0 := by
  unfold combH0
  rw [sechSqProfile_ofReal, Complex.im_ofReal_mul, hB.real x]
  simp

lemma InnerCombHyp.combH0_even (x : ℝ) (hB : InnerCombHyp c' B) :
    combH0 B (-(x : ℂ)) = combH0 B (x : ℂ) := by
  unfold combH0
  rw [sechSqProfile_neg, hB.even]

lemma InnerCombHyp.continuous_combH0_real (hB : InnerCombHyp c' B) :
    Continuous fun x : ℝ => combH0 B (x : ℂ) := by
  unfold combH0
  refine Continuous.mul ?_ hB.continuous_B_real
  have : Continuous fun x : ℝ => (1 : ℝ) / Real.cosh (π * x / 2) ^ 2 := by
    refine continuous_const.div (by fun_prop) (fun x => ?_)
    have := Real.cosh_pos (π * x / 2); positivity
  have h2 := Complex.continuous_ofReal.comp this
  refine h2.congr fun x => ?_
  simp only [Function.comp_apply]
  rw [sechSqProfile_ofReal]

lemma InnerCombHyp.continuousOn_combProfile (hc' : 0 < c') (hB : InnerCombHyp c' B) :
    ContinuousOn (combProfile c' B) (Ici 0) := by
  unfold combProfile
  exact (Complex.continuous_re.comp (hB.continuous_combH0_real.comp (continuousOn_xOf c'))
    ).continuousOn

lemma InnerCombHyp.combProfile_eq (hB : InnerCombHyp c' B) {s : ℝ} (hs : 0 < s) :
    combH0 B ((Real.sqrt (3 * s / c') : ℝ) : ℂ) = (combProfile c' B s : ℂ) := by
  unfold combProfile xOf
  exact (Complex.ext (by simp) (by simpa using hB.combH0_real _))

/-- `|u(t)| ≤ ‖h₀(x)‖ ≤ 4 e^{-πx} |B(x)|` and (iii) give the decay of the comb profile. -/
theorem InnerCombHyp.combProfile_decay (hc' : 0 < c') (hB : InnerCombHyp c' B) :
    ∃ C : ℝ, 0 ≤ C ∧ DecayBound c' C (combProfile c' B) := by
  obtain ⟨C, hC⟩ := hB.tail
  have hC0 : 0 ≤ C := by
    have := hC 0 le_rfl
    simp only [mul_zero, zero_div, Real.exp_zero, mul_one] at this
    exact (norm_nonneg _).trans this
  refine ⟨4 * C, by positivity, fun t ht => ?_⟩
  set x := xOf c' t with hx
  have hx0 : 0 ≤ x := xOf_nonneg c' t
  unfold decayEnv combProfile
  rw [← hx]
  have h1 : |(combH0 B (x : ℂ)).re| ≤ ‖combH0 B (x : ℂ)‖ := Complex.abs_re_le_norm _
  have h2 : ‖combH0 B (x : ℂ)‖ ≤ 4 * Real.exp (-π * |x|) * ‖B (x : ℂ)‖ := by
    unfold combH0; rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_sechSqProfile_ofReal_le x) (norm_nonneg _)
  have h3 : ‖B (x : ℂ)‖ ≤ C * Real.exp (-(c' * (2 * π * x / 3))) := by
    have := hC x hx0
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]
    exact this
  rw [abs_of_nonneg hx0] at h2
  calc |(combH0 B (x : ℂ)).re| ≤ 4 * Real.exp (-π * x) * (C * Real.exp (-(c' * (2 * π * x / 3)))) :=
        h1.trans (h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity)))
    _ = 4 * C * Real.exp (-(c' * (2 * π * x / 3)) - π * x) := by
        rw [sub_eq_add_neg, Real.exp_add]
        have : Real.exp (-π * x) = Real.exp (-(π * x)) := by rw [neg_mul]
        rw [this]; ring

/-- The comb as a strip function: continuous on `|Im b| ≤ 1/2`, holomorphic on `|Im b| < 1/2`, and
`h₀(b) = u(c' b²/3)` on `ℝ`. -/
theorem InnerCombHyp.stripContinuation (hc' : 0 < c') (hB : InnerCombHyp c' B) :
    StripContinuation c' (combProfile c' B) (combH0 B) := by
  have hsub : ∀ b : ℂ, |b.im| ≤ 1 / 2 → |b.im| < 7 / 8 := fun b hb => by linarith
  have hopen : IsOpen {b : ℂ | |b.im| < 7 / 8} :=
    isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  have hBat : ∀ b : ℂ, |b.im| ≤ 1 / 2 → DifferentiableAt ℂ B b := fun b hb =>
    hB.holo.differentiableAt (hopen.mem_nhds (hsub b hb))
  have hsechat : ∀ b : ℂ, |b.im| ≤ 1 / 2 → DifferentiableAt ℂ sechSqProfile b := fun b hb => by
    have hne := cosh_ne_zero_closedStrip hb
    unfold sechSqProfile
    refine (differentiableAt_const _).div ?_ (pow_ne_zero 2 hne)
    fun_prop
  refine ⟨?_, ?_, fun b => ?_⟩
  · intro b hb
    exact ((hsechat b hb).continuousAt.mul (hBat b hb).continuousAt).continuousWithinAt
  · intro b hb
    exact ((hsechat b (le_of_lt hb)).mul (hBat b (le_of_lt hb))).differentiableWithinAt
  · have hx : xOf c' (c' * b ^ 2 / 3) = |b| := by
      rw [← sq_abs b]; exact xOf_comp hc' (abs_nonneg b)
    unfold combProfile
    rw [hx]
    have h1 : combH0 B ((|b| : ℝ) : ℂ) = combH0 B (b : ℂ) := by
      rcases abs_cases b with ⟨h, _⟩ | ⟨h, _⟩
      · rw [h]
      · rw [h, Complex.ofReal_neg, hB.combH0_even]
    rw [h1]
    exact (Complex.ext (by simp) (by simpa using (hB.combH0_real b).symm)).symm

/-- `h₀` satisfies the hypotheses of Lemma `SD_H` (`a = π`, `C = 8`). -/
theorem InnerCombHyp.edgeHankelHyp (hB : InnerCombHyp c' B) : EdgeHankelHyp (combH0 B) π 8 where
  even := fun r => by simpa using hB.combH0_even r
  holo := by
    intro b hb
    have hb1 : |b.im| < 7 / 8 := by
      rw [abs_of_nonneg hb.1.le]; linarith [hb.2]
    have hne := cosh_ne_zero_strip hb.1.le hb.2.le
    have hs : DifferentiableAt ℂ sechSqProfile b := by
      unfold sechSqProfile
      refine (differentiableAt_const _).div ?_ (pow_ne_zero 2 hne)
      fun_prop
    have hopen : IsOpen {b : ℂ | |b.im| < 7 / 8} :=
      isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
    exact (hs.mul (hB.holo.differentiableAt (hopen.mem_nhds hb1))).differentiableWithinAt
  cont := by
    intro b hb
    have hb1 : |b.im| < 7 / 8 := by
      rw [abs_of_nonneg hb.1]; linarith [hb.2]
    have hne := cosh_ne_zero_strip hb.1 hb.2
    have hs : ContinuousAt sechSqProfile b := by
      unfold sechSqProfile
      refine continuousAt_const.div ?_ (pow_ne_zero 2 hne)
      fun_prop
    have hopen : IsOpen {b : ℂ | |b.im| < 7 / 8} :=
      isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
    exact (hs.mul (hB.holo.differentiableAt (hopen.mem_nhds hb1)).continuousAt).continuousWithinAt
  decay := by
    intro b h0 h1
    have hb1 : |b.im| ≤ 1 / 2 := by rw [abs_of_nonneg h0]; exact h1
    unfold combH0
    rw [norm_mul]
    have := sech_sq_le_strip h0 h1
    have hs : ‖sechSqProfile b‖ ≤ 8 * Real.exp (-π * |b.re|) := by simpa [sechSqProfile] using this
    calc ‖sechSqProfile b‖ * ‖B b‖ ≤ 8 * Real.exp (-π * |b.re|) * 1 :=
          mul_le_mul hs (hB.bound b hb1) (norm_nonneg _) (by positivity)
      _ = 8 * Real.exp (-π * |b.re|) := mul_one _

/-- `‖h₀(v + i/2)‖ ≤ ‖sech²(π(v + i/2)/2)‖` from `|B| = 1` on `E_+`. -/
theorem InnerCombHyp.edgeSechBound (hB : InnerCombHyp c' B) : EdgeSechBound (combH0 B) 1 :=
  edgeSechBound_of_unit hB.unit_edge

/-! ### The Hankel transform of the comb profile -/

lemma InnerCombHyp.integrable_liftW {w : ℕ} (hw : 1 ≤ w) (hc' : 0 < c') (hB : InnerCombHyp c' B)
    {C : ℝ} (hd : DecayBound c' C (combProfile c' B)) : Integrable (radialLift w (combProfile c' B)) :=
  radialLift_integrable_of_decay hw hc' (hB.continuousOn_combProfile hc') hd

lemma InnerCombHyp.integrable_lift (hc' : 0 < c') (hB : InnerCombHyp c' B) {C : ℝ}
    (hd : DecayBound c' C (combProfile c' B)) : Integrable (radialLift 1 (combProfile c' B)) :=
  hB.integrable_liftW le_rfl hc' hd

lemma InnerCombHyp.edgeHankel_eq (hc' : 0 < c') (hB : InnerCombHyp c' B) {C : ℝ}
    (hd : DecayBound c' C (combProfile c' B)) {t : ℝ} (ht : 0 < t) :
    edgeHankel c' (combH0 B) t = (hankelTransform 1 (combProfile c' B) t : ℂ) :=
  hankelTransform_one_eq_edgeHankel hc' (fun s hs => hB.combProfile_eq hs)
    (hB.continuousOn_combProfile hc') (hB.integrable_lift hc' hd) ht

/-- The order-`p` link for the comb: `edgeHankelP p c' h₀ = hankelTransform (p+1) u` on `t > 0`
(`hankelTransform_eq_edgeHankelP`). -/
lemma InnerCombHyp.edgeHankelP_eq (p : ℕ) (hc' : 0 < c') (hB : InnerCombHyp c' B) {C : ℝ}
    (hd : DecayBound c' C (combProfile c' B)) {t : ℝ} (ht : 0 < t) :
    edgeHankelP p c' (combH0 B) t = (hankelTransform (p + 1) (combProfile c' B) t : ℂ) :=
  hankelTransform_eq_edgeHankelP p (fun s hs => hB.combProfile_eq hs)
    (hB.continuousOn_combProfile hc') (hB.integrable_liftW (by omega) hc' hd) ht

/-- **Decay of the order-`p` Hankel transform of the comb profile**, given the `FW-SD` input on `x ≥ x_I`
(`fw:e1.4`): for `ĥ = 𝓗_{p+1} u = hankelTransform (p+1) u` and `u = combProfile c' B`,
`|ĥ(t)| ≤ C e^{-c' L(x) - πx}` for all `t ≥ 0` (`t = c' x²/3`).  `x ≤ X₀ = max(ξ_*/2, 3/(4π c'))` by the
trivial `L¹` bound; `X₀ ≤ x ≤ x_I` by `edge_global_bound_P` (`fw:e1.3`, valid for `k = 4π c' x/3 ≥ 1`, with
`x^{-p}` bounded by `x ≥ ξ_*/2`) and the link `edgeHankelP = hankelTransform (p+1)`. -/
theorem InnerCombHyp.hankelTransform_decayP (p : ℕ) (hc' : 0 < c') (hB : InnerCombHyp c' B)
    {C₀ : ℝ} (hd : DecayBound c' C₀ (combProfile c' B)) (htail : SaddleTailBoundP p c' B) :
    ∃ C : ℝ, 0 ≤ C ∧ DecayBound c' C (hankelTransform (p + 1) (combProfile c' B)) := by
  set u := combProfile c' B with hu
  have hw1 : 1 ≤ p + 1 := by omega
  have hint := hB.integrable_liftW hw1 hc' hd
  obtain ⟨CT, hCT⟩ := htail
  obtain ⟨K, hK0, hK⟩ := edge_global_bound_P p
  set β : ℝ := c' * (2 * π / 3) + π with hβ
  have hβpos : 0 < β := by rw [hβ]; positivity
  set I₁ : ℝ := ∫ ξ, ‖radialLift (p + 1) u ξ‖ with hI₁
  have hI₁0 : 0 ≤ I₁ := integral_nonneg fun _ => norm_nonneg _
  have hxi := xiStar_pos
  set X₀ : ℝ := max (xiStar / 2) (3 / (4 * π * c')) with hX₀
  have hX₀1 : xiStar / 2 ≤ X₀ := le_max_left _ _
  have hX₀2 : 3 / (4 * π * c') ≤ X₀ := le_max_right _ _
  have hnorm_bound : ∀ t : ℝ, |hankelTransform (p + 1) u t| ≤ I₁ := fun t => by
    unfold hankelTransform
    rw [dif_pos hw1]
    exact (Complex.abs_re_le_norm _).trans (Real.norm_fourier_le_integral_norm _ _)
  set K₂ : ℝ := K * 1 * (√(2 / xiStar) * √c' * (2 / xiStar) ^ p) with hK₂
  have hK₂0 : 0 ≤ K₂ := by rw [hK₂]; positivity
  set C : ℝ := max (max (I₁ * Real.exp (β * X₀)) (K₂ * Real.exp (π * xI c'))) (max CT 0) with hCdef
  refine ⟨C, le_max_of_le_right (le_max_right _ _), fun t ht => ?_⟩
  unfold decayEnv
  set x := xOf c' t with hx
  have hx0 : 0 ≤ x := xOf_nonneg c' t
  have hexp : Real.exp (-(c' * (2 * π * x / 3)) - π * x) = Real.exp (-β * x) := by
    congr 1; rw [hβ]; ring
  rw [hexp]
  have hepos := Real.exp_pos (-β * x)
  have hC1 : I₁ * Real.exp (β * X₀) ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hC2 : K₂ * Real.exp (π * xI c') ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have hC3 : CT ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hxI_gt : xiStar / 2 < xI c' := by
    unfold xI
    have : 0 < c' ^ (-(3 / 5 : ℝ)) := Real.rpow_pos_of_pos hc' _
    linarith
  have hlink : ∀ y : ℝ, 0 < y → t = c' * y ^ 2 / 3 → y = x → 0 < t →
      edgeHankelP p c' (combH0 B) t = (hankelTransform (p + 1) u t : ℂ) := fun y _ _ _ ht0 =>
    hB.edgeHankelP_eq p hc' hd ht0
  rcases le_or_gt x X₀ with h1 | h1
  · -- trivial bound on the compact range
    have : I₁ ≤ I₁ * Real.exp (β * X₀) * Real.exp (-β * x) := by
      have h3 : 1 ≤ Real.exp (β * X₀) * Real.exp (-β * x) := by
        rw [← Real.exp_add]; exact Real.one_le_exp (by nlinarith)
      calc I₁ = I₁ * 1 := (mul_one _).symm
        _ ≤ I₁ * (Real.exp (β * X₀) * Real.exp (-β * x)) :=
            mul_le_mul_of_nonneg_left h3 hI₁0
        _ = _ := by ring
    calc |hankelTransform (p + 1) u t| ≤ I₁ := hnorm_bound t
      _ ≤ I₁ * Real.exp (β * X₀) * Real.exp (-β * x) := this
      _ ≤ C * Real.exp (-β * x) := mul_le_mul_of_nonneg_right hC1 hepos.le
  · have hxh : xiStar / 2 < x := lt_of_le_of_lt hX₀1 h1
    have ht0 : 0 < t := by
      by_contra hneg
      have : t = 0 := le_antisymm (not_lt.mp hneg) ht
      have : x = 0 := by rw [hx, this]; simp [xOf]
      linarith
    have htx : t = c' * x ^ 2 / 3 := by
      rw [hx, sq_xOf hc' ht]; field_simp
    rcases le_or_gt x (xI c') with h2 | h2
    · -- `SD_G` of order `p` on `X₀ < x ≤ x_I`
      have hx_pos : 0 < x := by linarith
      have hk1 : 1 ≤ 4 * π * c' * x / 3 := by
        have h3 : 3 / (4 * π * c') < x := lt_of_le_of_lt hX₀2 h1
        rw [div_lt_iff₀ (by positivity)] at h3
        nlinarith
      have hsd := hK (combH0 B) π 8 1 Real.pi_pos hB.edgeHankelHyp zero_le_one hB.edgeSechBound
        c' x hc' hx_pos hk1
      rw [← htx, hB.edgeHankelP_eq p hc' hd ht0, Complex.norm_real, Real.norm_eq_abs] at hsd
      unfold edgeL at hsd
      have h1a : √(c' / x) ≤ √(2 / xiStar) * √c' := by
        rw [← Real.sqrt_mul (by positivity)]
        apply Real.sqrt_le_sqrt
        rw [div_le_iff₀ hx_pos]
        have : 2 / xiStar * c' * x ≥ 2 / xiStar * c' * (xiStar / 2) :=
          mul_le_mul_of_nonneg_left hxh.le (by positivity)
        have e : 2 / xiStar * c' * (xiStar / 2) = c' := by field_simp
        linarith
      have h1b : (1 / x) ^ p ≤ (2 / xiStar) ^ p := by
        refine pow_le_pow_left₀ (by positivity) ?_ p
        rw [div_le_div_iff₀ hx_pos hxi]; linarith
      have h4 : |hankelTransform (p + 1) u t| ≤
          K₂ * Real.exp (-(c' * (2 * π * x / 3))) := by
        rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]
        have hsd' : |hankelTransform (p + 1) u t| * Real.exp (c' * (2 * π * x / 3)) ≤
            K * 1 * √(c' / x) * (1 / x) ^ p := by
          rw [mul_comm]; exact hsd
        refine hsd'.trans ?_
        calc K * 1 * √(c' / x) * (1 / x) ^ p
            ≤ K * 1 * (√(2 / xiStar) * √c') * (2 / xiStar) ^ p := by gcongr
          _ = K₂ := by rw [hK₂]; ring
      have h5 : Real.exp (-(c' * (2 * π * x / 3))) =
          Real.exp (π * x) * Real.exp (-β * x) := by
        rw [← Real.exp_add]; congr 1; rw [hβ]; ring
      calc |hankelTransform (p + 1) u t| ≤ K₂ * Real.exp (-(c' * (2 * π * x / 3))) := h4
        _ = K₂ * Real.exp (π * x) * Real.exp (-β * x) := by rw [h5]; ring
        _ ≤ K₂ * Real.exp (π * xI c') * Real.exp (-β * x) := by gcongr
        _ ≤ C * Real.exp (-β * x) := mul_le_mul_of_nonneg_right hC2 hepos.le
    · -- the tail
      have := hCT x h2.le
      rw [← htx, hB.edgeHankelP_eq p hc' hd ht0, Complex.norm_real, Real.norm_eq_abs, hexp] at this
      calc |hankelTransform (p + 1) u t| ≤ CT * Real.exp (-β * x) := this
        _ ≤ C * Real.exp (-β * x) := mul_le_mul_of_nonneg_right hC3 hepos.le

/-- Decay of the Hankel transform of the comb profile, given the `SD_V` input on `x ≥ x_I`
(`ξ_*/2 ≤ x ≤ x_I` by `SD_G`, `x ≤ ξ_*/2` by the trivial `L¹` bound): the case `p = 0` of
`hankelTransform_decayP`. -/
theorem InnerCombHyp.hankelTransform_decay (hc' : 0 < c') (hB : InnerCombHyp c' B)
    {C₀ : ℝ} (hd : DecayBound c' C₀ (combProfile c' B)) (htail : SaddleTailBound c' B) :
    ∃ C : ℝ, 0 ≤ C ∧ DecayBound c' C (hankelTransform 1 (combProfile c' B)) :=
  hB.hankelTransform_decayP 0 hc' hd htail

/-! ### Vacuum values and the assembled Lemma `K7` -/

lemma DecayBound.mono {c' C C' : ℝ} {ψ : ℝ → ℝ} (hd : DecayBound c' C ψ) (hC : C ≤ C') :
    DecayBound c' C' ψ := fun t ht =>
  (hd t ht).trans (by unfold decayEnv; exact mul_le_mul_of_nonneg_right hC (Real.exp_pos _).le)

/-- `|sech²(π b/2)| ≤ 2` at the vacuum points `b = i y`, `0 ≤ y ≤ 1/2`. -/
lemma norm_sechSqProfile_imag_le {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) :
    ‖sechSqProfile (Complex.I * (y : ℂ))‖ ≤ 2 := by
  unfold sechSqProfile
  have h1 : Complex.cosh ((π : ℂ) * (Complex.I * (y : ℂ)) / 2) = ((Real.cos (π * y / 2) : ℝ) : ℂ) := by
    rw [show (π : ℂ) * (Complex.I * (y : ℂ)) / 2 = ((π * y / 2 : ℝ) : ℂ) * Complex.I by
      push_cast; ring, Complex.cosh_mul_I, Complex.ofReal_cos]
  rw [h1, norm_div, norm_one, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have hw0 : 0 ≤ π * y / 2 := by positivity
  have hw1 : π * y / 2 ≤ π / 4 := by nlinarith [Real.pi_pos]
  have hcos : Real.cos (π / 4) ≤ Real.cos (π * y / 2) :=
    Real.cos_le_cos_of_nonneg_of_le_pi hw0 (by linarith [Real.pi_pos]) hw1
  rw [Real.cos_pi_div_four] at hcos
  have hpos : 0 < Real.cos (π * y / 2) := lt_of_lt_of_le (by positivity) hcos
  rw [abs_of_pos hpos, div_le_iff₀ (by positivity)]
  have h4 : (√2 / 2) ^ 2 = 1 / 2 := by rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have h3 : 0 ≤ √2 / 2 := by positivity
  nlinarith

/-- **Lemma `K7` at every weight** (`cmb:K7`, `fw:FWM`; Lean theorem `k7_membership_vacuumW`).
For an inner Blaschke comb `B` satisfying (i), (iii) (`InnerCombHyp`) and the order-`(w-1)` tail input
`SaddleTailBoundP (w-1)` (derived from the `FW-SD` amplitude hypotheses in `SaddleTail.lean`), with
`a = c'/12 ≥ S` for a problem `prob` of weight `w = prob.w ≥ 1`:
`h = u`, `ĥ = hankelTransform w u` decay like `C e^{-c' L(x) - πx}`, `g = ½ (h - ĥ) ∈ Ā`,
and the vacuum identity `g_vac = ½ h_{0,vac} - π ∫ h₀ V` holds with
`h_{0,vac} = ∑_s (-1)^{|s|} h₀(b_{a - r_s})` and `|½ h_{0,vac}| ≤ 2^m`.  For `w = 1` this is `k7_membership_vacuum`. -/
theorem k7_membership_vacuumW {prob : FixedWeightProblem} (hc' : 0 < c')
    (hS : prob.totalShift ≤ c' / 12) (hB : InnerCombHyp c' B)
    (htail : SaddleTailBoundP (prob.w - 1) c' B) :
    ∃ C : ℝ, 0 ≤ C ∧ DecayBound c' C (combProfile c' B) ∧
      DecayBound c' C (hankelTransform prob.w (combProfile c' B)) ∧
      TestClass prob (c' / 12)
        (pairOdd (combProfile c' B) (hankelTransform prob.w (combProfile c' B))) ∧
      ((prob.gVac (c' / 12)
          (pairOdd (combProfile c' B) (hankelTransform prob.w (combProfile c' B))) : ℝ) : ℂ) =
        (1 / 2 : ℂ) * ∑ s : Finset (Fin prob.m), (-1 : ℂ) ^ s.card *
            combH0 B (bAlpha c' (c' / 12 - prob.shiftSum s)) -
          (π : ℂ) * ((∫ t in Ioi (0 : ℝ), combProfile c' B t * prob.cardyV (c' / 12) t : ℝ) : ℂ) ∧
      ‖(1 / 2 : ℂ) * ∑ s : Finset (Fin prob.m), (-1 : ℂ) ^ s.card *
          combH0 B (bAlpha c' (c' / 12 - prob.shiftSum s))‖ ≤ 2 ^ prob.m := by
  obtain ⟨C₀, hC₀, hd₀⟩ := hB.combProfile_decay hc'
  obtain ⟨C₁, hC₁, hd₁⟩ := hB.hankelTransform_decayP (prob.w - 1) hc' hd₀ htail
  rw [Nat.sub_add_cancel prob.hw] at hd₁
  set C := max C₀ C₁ with hC
  have hd : DecayBound c' C (combProfile c' B) := hd₀.mono (le_max_left _ _)
  have hd' : DecayBound c' C (hankelTransform prob.w (combProfile c' B)) :=
    hd₁.mono (le_max_right _ _)
  have hF : 𝓕 (radialLift prob.w (combProfile c' B)) =
      radialLift prob.w (hankelTransform prob.w (combProfile c' B)) :=
    fourier_radialLift_eq_hankelTransform prob.hw _
  have hcont' : ContinuousOn (hankelTransform prob.w (combProfile c' B)) (Ici 0) :=
    continuousOn_hankelTransform prob.hw (hB.integrable_liftW prob.hw hc' hd₀)
  have hcont : ContinuousOn (combProfile c' B) (Ici 0) := hB.continuousOn_combProfile hc'
  obtain ⟨hmem, -, hvac⟩ := fwM_of_decay hc' hS hcont hcont' hd hd' hF (hB.stripContinuation hc')
  refine ⟨C, le_max_of_le_left hC₀, hd, hd', hmem, hvac, ?_⟩
  refine norm_vacuum_head_le (fun s => ?_)
  set α := c' / 12 - prob.shiftSum s with hα
  have hα0 : 0 ≤ α := by linarith [prob.shiftSum_le_totalShift s]
  have hα1 : α ≤ c' / 12 := by linarith [prob.shiftSum_nonneg s]
  have hmem' := bAlpha_mem_closedStrip hc' hα1
  have hbim : |(bAlpha c' α).im| ≤ 1 / 2 := hmem'
  have hy0 : 0 ≤ Real.sqrt (3 * α / c') := Real.sqrt_nonneg _
  have hy1 : Real.sqrt (3 * α / c') ≤ 1 / 2 := by
    have := hbim
    simpa [bAlpha, abs_of_nonneg hy0] using this
  unfold combH0
  rw [norm_mul]
  have e1 : bAlpha c' α = Complex.I * ((Real.sqrt (3 * α / c') : ℝ) : ℂ) := rfl
  calc ‖sechSqProfile (bAlpha c' α)‖ * ‖B (bAlpha c' α)‖ ≤ 2 * 1 := by
        rw [e1]
        exact mul_le_mul (norm_sechSqProfile_imag_le hy0 hy1) (hB.bound _ (by rw [← e1]; exact hbim))
          (norm_nonneg _) (by norm_num)
    _ = 2 := by norm_num


/-- **Lemma `K7`** (`cmb:K7`, weight `w = 1`; Lean theorem `k7_membership_vacuum`).
For an inner Blaschke comb `B` satisfying (i), (iii) (`InnerCombHyp`) and the `SD_V` tail input
`SaddleTailBound` (derived from `SDVAmplitudeInput` in `SaddleTail.lean`), with `a = c'/12 ≥ S` for a problem `prob` with `w = 1`:
`h = u`, `ĥ = hankelTransform 1 u` decay like `C e^{-c' L(x) - πx}`, `g = ½ (h - ĥ) ∈ Ā`,
and the vacuum identity `g_vac = ½ h_{0,vac} - π ∫ h₀ V` holds with
`h_{0,vac} = ∑_s (-1)^{|s|} h₀(b_{a - r_s})` (`= h₀(b_a) - 2h₀(b_{a-1}) + h₀(b_{a-2})` for
`Q = (1-q)²`) and `|½ h_{0,vac}| ≤ 2^m` (so `|h_{0,vac}| ≤ 8` for `m = 2`).
Not covered: the clause `g_vac` for the specific comb families `B^{(f)}`, `B_D`, `B_2` (hypotheses
(i)-(iii) there are `K1(a)`, `K3`, `K6(a)`, `ut:Phi`, `ut:T2`). -/
theorem k7_membership_vacuum {prob : FixedWeightProblem} (hw : prob.w = 1) (hc' : 0 < c')
    (hS : prob.totalShift ≤ c' / 12) (hB : InnerCombHyp c' B) (htail : SaddleTailBound c' B) :
    ∃ C : ℝ, 0 ≤ C ∧ DecayBound c' C (combProfile c' B) ∧
      DecayBound c' C (hankelTransform 1 (combProfile c' B)) ∧
      TestClass prob (c' / 12) (pairOdd (combProfile c' B) (hankelTransform 1 (combProfile c' B))) ∧
      ((prob.gVac (c' / 12) (pairOdd (combProfile c' B) (hankelTransform 1 (combProfile c' B))) :
          ℝ) : ℂ) =
        (1 / 2 : ℂ) * ∑ s : Finset (Fin prob.m), (-1 : ℂ) ^ s.card *
            combH0 B (bAlpha c' (c' / 12 - prob.shiftSum s)) -
          (π : ℂ) * ((∫ t in Ioi (0 : ℝ), combProfile c' B t * prob.cardyV (c' / 12) t : ℝ) : ℂ) ∧
      ‖(1 / 2 : ℂ) * ∑ s : Finset (Fin prob.m), (-1 : ℂ) ^ s.card *
          combH0 B (bAlpha c' (c' / 12 - prob.shiftSum s))‖ ≤ 2 ^ prob.m := by
  have h := k7_membership_vacuumW (prob := prob) hc' hS hB (by rw [hw]; exact htail)
  rw [hw] at h
  exact h

/-- Non-vacuity of `SaddleTailBoundP`: it holds for the zero comb at every order `p`. -/
theorem saddleTailBoundP_zero (p : ℕ) (c' : ℝ) : SaddleTailBoundP p c' (fun _ => 0) := by
  refine ⟨0, fun x _ => ?_⟩
  have : combH0 (fun _ => (0 : ℂ)) = fun _ => 0 := by
    ext b; simp [combH0]
  simp [this, edgeHankelP, hankelTransformOrd]

/-- Non-vacuity of `SaddleTailBound`: it holds for the zero comb (`h₀ = 0`, `ĥ₀ = 0`); for a genuine
comb it is the output of Lemma `SD_V` (`saddleTailBound_of_sdv`). -/
theorem saddleTailBound_zero (c' : ℝ) : SaddleTailBound c' (fun _ => 0) :=
  saddleTailBoundP_zero 0 c'

/-- info: 'FormalResearch.ModularBootstrap.Upper.Membership.k7_membership_vacuumW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms k7_membership_vacuumW

/-- info: 'FormalResearch.ModularBootstrap.Upper.Membership.k7_membership_vacuum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms k7_membership_vacuum

/-- info: 'FormalResearch.ModularBootstrap.Upper.Membership.InnerCombHyp.hankelTransform_decay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms InnerCombHyp.hankelTransform_decay

/-- info: 'FormalResearch.ModularBootstrap.Upper.Membership.InnerCombHyp.stripContinuation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms InnerCombHyp.stripContinuation

end FormalResearch.ModularBootstrap.Upper.Membership
