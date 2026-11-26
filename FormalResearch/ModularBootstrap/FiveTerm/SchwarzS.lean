module

public import FormalResearch.ModularBootstrap.FiveTerm.HalfDiscCauchy
public import FormalResearch.SignUncertainty.CtOuterEdge

/-!
# The function `S(u) = ∫_0^1 (1 + u t²)^{-1/2} dt = arcsinh(√u)/√u` (FIVE-0 slice 2; `cts:involution` (2))

The antisymmetric part of `log G_outer` is `-½ log R` with `R = (2√2)⁻¹ Q z^{1/2}(1+z)^{7/2}(1-z)^{-1/2}`,
`Q⁴ = -b(σz)²/b(z)²` (`cts:R-id`).  Since `b² = u S(u)²/π²` with `u(z) = (1-6z²+z⁴)/(1+z²)² = sinh²(πb)` and
`u(σ z) = -u(z)`, one has `Q⁴ = (S(-u)/S(u))²`, so `Q = Ŝ^{1/2}` with `Ŝ(u) = S(-u)/S(u)`.  This file defines `S` by the
integral (no `arccosh`, no branch bookkeeping), proves `S` holomorphic on `D₁ = ℂ ∖ (-∞,-1]` with `Re S > 0`,
`Ŝ(u) ∈ slitPlane` on `D = D₁ ∩ (-D₁)`, `Ŝ(-u) = 1/Ŝ(u)`, and the algebra of `u(z)` on `Ω`:
`u(σ z) = -u(z)`, `1 - u = 8z²/(1+z²)²`, `u(Ω) ⊆ D`.  All proved unconditionally.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real
open FormalResearch.SignUncertainty.CtOuter

namespace FormalResearch.ModularBootstrap.FiveTerm

/-- `S(u) = ∫_0^1 (1 + u t²)^{-1/2} dt`. -/
noncomputable def sInt (u : ℂ) : ℂ := ∫ t in Icc (0 : ℝ) 1, (1 + u * (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))

/-- `ℂ ∖ (-∞, -1]`. -/
def sDom : Set ℂ := {u : ℂ | ¬ (u.im = 0 ∧ u.re ≤ -1)}

lemma isOpen_sDom : IsOpen sDom := by
  have : IsClosed {u : ℂ | u.im = 0 ∧ u.re ≤ -1} :=
    (isClosed_eq Complex.continuous_im continuous_const).inter
      (isClosed_le Complex.continuous_re continuous_const)
  exact this.isOpen_compl

lemma one_add_mul_mem_slit {u : ℂ} (hu : u ∈ sDom) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    1 + u * (t : ℂ) ^ 2 ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_contra hcon
  push Not at hcon
  obtain ⟨hre, him⟩ := hcon
  have him' : u.im * t ^ 2 = 0 := by
    simpa [Complex.mul_im, pow_two] using him
  have hre' : 1 + u.re * t ^ 2 ≤ 0 := by
    have : (1 + u * (t : ℂ) ^ 2).re = 1 + u.re * t ^ 2 := by
      simp [Complex.mul_re, pow_two]
    linarith
  rcases mul_eq_zero.mp him' with h | h
  · apply hu
    refine ⟨h, ?_⟩
    have ht0 : 0 < t := by
      rcases ht.1.eq_or_lt with h0 | h0
      · rw [← h0] at hre'; norm_num at hre'
      · exact h0
    have ht1 : t ^ 2 ≤ 1 := by nlinarith [ht.2]
    nlinarith [sq_nonneg t, mul_pos ht0 ht0]
  · have : t = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp h
    rw [this] at hre'; norm_num at hre'

lemma re_cpow_neg_half_pos {z : ℂ} (hz : z ∈ Complex.slitPlane) : 0 < (z ^ (-(1 / 2 : ℂ))).re := by
  have hz0 : z ≠ 0 := Complex.slitPlane_ne_zero hz
  rw [Complex.cpow_def_of_ne_zero hz0, Complex.exp_re]
  refine mul_pos (Real.exp_pos _) ?_
  have him : (Complex.log z * (-(1 / 2 : ℂ))).im = -(Complex.arg z) / 2 := by
    simp [Complex.mul_im, Complex.log_im, Complex.log_re]
    ring
  rw [him]
  apply Real.cos_pos_of_mem_Ioo
  have h1 := Complex.neg_pi_lt_arg z
  have h2 : Complex.arg z < π := lt_of_le_of_ne (Complex.arg_le_pi z)
    (fun h => by
      have := Complex.arg_eq_pi_iff.mp h
      rw [Complex.mem_slitPlane_iff] at hz
      rcases hz with hz | hz
      · linarith [this.1]
      · exact hz this.2)
  constructor <;> linarith

lemma continuousOn_sIntegrand {u : ℂ} (hu : u ∈ sDom) :
    ContinuousOn (fun t : ℝ => (1 + u * (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) (Icc (0 : ℝ) 1) := by
  refine ContinuousOn.cpow_const (by fun_prop) (fun t ht => one_add_mul_mem_slit hu ht)

lemma re_sInt_pos {u : ℂ} (hu : u ∈ sDom) : 0 < (sInt u).re := by
  unfold sInt
  have hint : IntegrableOn (fun t : ℝ => (1 + u * (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) (Icc (0 : ℝ) 1) :=
    (continuousOn_sIntegrand hu).integrableOn_Icc
  rw [← RCLike.re_to_complex, ← integral_re hint]
  simp only [RCLike.re_to_complex]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ (fun t ht => ?_) one_pos
  · exact (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr hint.re
  · exact re_cpow_neg_half_pos (one_add_mul_mem_slit hu ⟨ht.1.le, ht.2.le⟩)

lemma sInt_ne_zero {u : ℂ} (hu : u ∈ sDom) : sInt u ≠ 0 := by
  intro h; have := re_sInt_pos hu; rw [h] at this; simp at this

lemma differentiableOn_sInt : DifferentiableOn ℂ sInt sDom := by
  unfold sInt
  refine differentiableOn_intervalParam (Φ := fun u t => (1 + u * (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)))
    isOpen_sDom (fun u hu => continuousOn_sIntegrand hu) (fun t ht => ?_) (fun u₀ hu₀ => ?_)
  · exact DifferentiableOn.cpow_const (by fun_prop) (fun u hu => one_add_mul_mem_slit hu ht)
  · obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_sDom u₀ hu₀
    set K : Set (ℂ × ℝ) := closedBall u₀ (r / 2) ×ˢ Icc (0 : ℝ) 1 with hK
    have hKc : IsCompact K := (isCompact_closedBall _ _).prod isCompact_Icc
    have hKsub : ∀ p ∈ K, 1 + p.1 * (p.2 : ℂ) ^ 2 ∈ Complex.slitPlane := fun p hp =>
      one_add_mul_mem_slit (hball (by
        have := mem_closedBall.mp hp.1
        rw [mem_ball]; linarith)) hp.2
    have hKne : K.Nonempty := ⟨(u₀, 0), by simp [hK]; exact (by linarith : (0 : ℝ) ≤ r / 2)⟩
    have hcont : ContinuousOn (fun p : ℂ × ℝ => ‖1 + p.1 * (p.2 : ℂ) ^ 2‖) K := by
      fun_prop
    obtain ⟨p0, hp0, hmin⟩ := hKc.exists_isMinOn hKne hcont
    have hm : 0 < ‖1 + p0.1 * (p0.2 : ℂ) ^ 2‖ :=
      norm_pos_iff.mpr (Complex.slitPlane_ne_zero (hKsub p0 hp0))
    refine ⟨r / 2, by linarith, ‖1 + p0.1 * (p0.2 : ℂ) ^ 2‖ ^ (-(1 / 2 : ℝ)), fun t ht w hw => ?_⟩
    have hwK : (w, t) ∈ K := ⟨by
      rw [mem_closedBall]; exact (mem_ball.mp hw).le, ht⟩
    have hle : ‖1 + p0.1 * (p0.2 : ℂ) ^ 2‖ ≤ ‖1 + w * (t : ℂ) ^ 2‖ := hmin hwK
    have hne : 1 + w * (t : ℂ) ^ 2 ≠ 0 := Complex.slitPlane_ne_zero (hKsub _ hwK)
    have : ‖(1 + w * (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))‖ = ‖1 + w * (t : ℂ) ^ 2‖ ^ (-(1 / 2 : ℝ)) := by
      have := Complex.norm_cpow_of_ne_zero hne (-(1 / 2 : ℂ))
      simpa using this
    rw [this]
    exact Real.rpow_le_rpow_of_nonpos hm hle (by norm_num)

/-! ### The ratio `Ŝ(u) = S(-u)/S(u)` -/

/-- `Ŝ(u) = S(-u)/S(u)`. -/
noncomputable def sHat (u : ℂ) : ℂ := sInt (-u) / sInt u

/-- `D = D₁ ∩ (-D₁) = ℂ ∖ ((-∞,-1] ∪ [1,∞))`. -/
def sHatDom : Set ℂ := {u : ℂ | u ∈ sDom ∧ -u ∈ sDom}

lemma isOpen_sHatDom : IsOpen sHatDom :=
  isOpen_sDom.inter (isOpen_sDom.preimage continuous_neg)

lemma sHat_mem_slit {u : ℂ} (hu : u ∈ sHatDom) : sHat u ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_contra hcon
  push Not at hcon
  obtain ⟨hre, him⟩ := hcon
  have h1 := re_sInt_pos hu.2
  have h2 := re_sInt_pos hu.1
  have hne := sInt_ne_zero hu.1
  have e : sInt (-u) = sHat u * sInt u := by unfold sHat; field_simp
  have : (sInt (-u)).re = (sHat u).re * (sInt u).re := by
    rw [e, Complex.mul_re, him]; ring
  nlinarith [mul_nonneg (neg_nonneg.mpr hre) h2.le]

lemma sHat_neg {u : ℂ} (_hu : u ∈ sHatDom) : sHat (-u) = (sHat u)⁻¹ := by
  unfold sHat
  rw [neg_neg, inv_div]

lemma log_sHat_neg {u : ℂ} (hu : u ∈ sHatDom) : Complex.log (sHat (-u)) = -Complex.log (sHat u) := by
  rw [sHat_neg hu]
  have h := sHat_mem_slit hu
  have harg : (sHat u).arg ≠ Real.pi := by
    intro h'
    rw [Complex.mem_slitPlane_iff] at h
    have := Complex.arg_eq_pi_iff.mp h'
    rcases h with h | h
    · linarith [this.1]
    · exact h this.2
  exact Complex.log_inv _ harg

lemma differentiableOn_sHat : DifferentiableOn ℂ sHat sHatDom := by
  unfold sHat
  intro u hu
  have h1 : DifferentiableAt ℂ sInt (-u) :=
    (differentiableOn_sInt.differentiableAt (isOpen_sDom.mem_nhds hu.2))
  have h2 : DifferentiableAt ℂ sInt u :=
    (differentiableOn_sInt.differentiableAt (isOpen_sDom.mem_nhds hu.1))
  exact ((h1.comp u (differentiableAt_id.neg)).div h2 (sInt_ne_zero hu.1)).differentiableWithinAt

/-- `log Ŝ` is holomorphic on `D`. -/
lemma differentiableOn_log_sHat : DifferentiableOn ℂ (fun u => Complex.log (sHat u)) sHatDom := by
  intro u hu
  exact ((differentiableOn_sHat u hu).differentiableAt (isOpen_sHatDom.mem_nhds hu)).clog
    (sHat_mem_slit hu) |>.differentiableWithinAt

/-! ### The coordinate `u(z) = (1 - 6z² + z⁴)/(1 + z²)²` on `Ω` -/

/-- `u(z) = sinh²(π b(z)) = (1 - 6z² + z⁴)/(1+z²)²`. -/
noncomputable def uC (z : ℂ) : ℂ := (1 - 6 * z ^ 2 + z ^ 4) / (1 + z ^ 2) ^ 2

lemma one_add_sq_ne_zero_of_halfDisc {z : ℂ} (hz : z ∈ halfDisc) : 1 + z ^ 2 ≠ 0 := by
  intro h
  have : (z - Complex.I) * (z + Complex.I) = 0 := by
    have hI := Complex.I_sq
    linear_combination h + (-1 : ℂ) * hI
  rcases mul_eq_zero.mp this with h | h
  · have := sub_eq_zero.mp h
    have h1 := hz.1
    rw [this] at h1; simp at h1
  · have := eq_neg_of_add_eq_zero_left h
    have h1 := hz.1
    rw [this] at h1; simp at h1

lemma one_sub_uC {z : ℂ} (hz : 1 + z ^ 2 ≠ 0) : 1 - uC z = 8 * z ^ 2 / (1 + z ^ 2) ^ 2 := by
  unfold uC
  have : (1 + z ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 hz
  field_simp
  ring

lemma one_add_uC {z : ℂ} (hz : 1 + z ^ 2 ≠ 0) :
    1 + uC z = 2 * ((1 - z ^ 2) / (1 + z ^ 2)) ^ 2 := by
  unfold uC
  have : (1 + z ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 hz
  field_simp
  ring

lemma uC_sigma {z : ℂ} (hz : 1 + z ^ 2 ≠ 0) (hz1 : 1 + z ≠ 0) :
    uC ((1 - z) / (1 + z)) = -uC z := by
  unfold uC
  have h2 : (1 + z ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 hz
  have h3 : 1 + ((1 - z) / (1 + z)) ^ 2 ≠ 0 := by
    have : 1 + ((1 - z) / (1 + z)) ^ 2 = 2 * (1 + z ^ 2) / (1 + z) ^ 2 := by
      field_simp; ring
    rw [this]
    exact div_ne_zero (mul_ne_zero two_ne_zero hz) (pow_ne_zero 2 hz1)
  have hd : 1 + ((1 - z) / (1 + z)) ^ 2 = 2 * (1 + z ^ 2) / (1 + z) ^ 2 := by
    field_simp; ring
  have hn : 1 - 6 * ((1 - z) / (1 + z)) ^ 2 + ((1 - z) / (1 + z)) ^ 4
      = -4 * (1 - 6 * z ^ 2 + z ^ 4) / (1 + z) ^ 4 := by
    field_simp; ring
  rw [hd, hn]
  field_simp
  ring

lemma not_sq_nonpos {w : ℂ} (hw : 0 < w.re) : ¬ ((w ^ 2).im = 0 ∧ (w ^ 2).re ≤ 0) := by
  rintro ⟨him, hre⟩
  have h1 : (w ^ 2).im = 2 * w.re * w.im := by simp [pow_two, Complex.mul_im]; ring
  have h2 : (w ^ 2).re = w.re ^ 2 - w.im ^ 2 := by simp [pow_two, Complex.mul_re]
  rw [h1] at him
  have : w.im = 0 := by
    rcases mul_eq_zero.mp him with h | h
    · rcases mul_eq_zero.mp h with h | h <;> [norm_num at h; linarith]
    · exact h
  rw [h2, this] at hre
  nlinarith [sq_nonneg w.re, mul_pos hw hw]

lemma re_one_sub_sq_div_pos {z : ℂ} (hz : ‖z‖ < 1) (hne : 1 + z ^ 2 ≠ 0) :
    0 < ((1 - z ^ 2) / (1 + z ^ 2)).re := by
  have hn : Complex.normSq (1 + z ^ 2) ≠ 0 := by
    rw [Ne, Complex.normSq_eq_zero]; exact hne
  have hnpos : 0 < Complex.normSq (1 + z ^ 2) := lt_of_le_of_ne (Complex.normSq_nonneg _) (Ne.symm hn)
  rw [Complex.div_re, ← add_div]
  refine div_pos ?_ hnpos
  have e : (1 - z ^ 2).re * (1 + z ^ 2).re + (1 - z ^ 2).im * (1 + z ^ 2).im = 1 - ‖z‖ ^ 4 := by
    have h1 : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have : ‖z‖ ^ 4 = (z.re ^ 2 + z.im ^ 2) ^ 2 := by rw [← h1]; ring
    rw [this]
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.one_re,
      Complex.one_im, pow_two, Complex.mul_re, Complex.mul_im]
    ring
  rw [e]
  have : ‖z‖ ^ 4 < 1 := pow_lt_one₀ (norm_nonneg z) hz (by norm_num)
  linarith

lemma re_div_one_add_sq_pos {z : ℂ} (hz : 0 < z.re) (hne : 1 + z ^ 2 ≠ 0) :
    0 < (z / (1 + z ^ 2)).re := by
  have hn : Complex.normSq (1 + z ^ 2) ≠ 0 := by
    rw [Ne, Complex.normSq_eq_zero]; exact hne
  have hnpos : 0 < Complex.normSq (1 + z ^ 2) := lt_of_le_of_ne (Complex.normSq_nonneg _) (Ne.symm hn)
  rw [Complex.div_re, ← add_div]
  refine div_pos ?_ hnpos
  simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, pow_two, Complex.mul_re,
    Complex.mul_im]
  nlinarith [mul_pos hz (add_pos_of_pos_of_nonneg one_pos (add_nonneg (sq_nonneg z.re) (sq_nonneg z.im))),
    sq_nonneg z.re, sq_nonneg z.im]

lemma two_mul_re_aux (n : ℕ) [n.AtLeastTwo] (w : ℂ) :
    ((OfNat.ofNat n : ℂ) * w).re = OfNat.ofNat n * w.re := by
  simp [Complex.mul_re]

lemma two_mul_im_aux (n : ℕ) [n.AtLeastTwo] (w : ℂ) :
    ((OfNat.ofNat n : ℂ) * w).im = OfNat.ofNat n * w.im := by
  simp [Complex.mul_im]

/-- `u(Ω) ⊆ D`: `u(z)` avoids `(-∞,-1] ∪ [1,∞)` for `z ∈ Ω`. -/
lemma uC_mem_sHatDom {z : ℂ} (hz : z ∈ halfDisc) : uC z ∈ sHatDom := by
  have hne := one_add_sq_ne_zero_of_halfDisc hz
  constructor
  · -- `u ∉ (-∞,-1]`
    rintro ⟨him, hre⟩
    have h1 := one_add_uC hne
    have hr := re_one_sub_sq_div_pos hz.1 hne
    apply not_sq_nonpos hr
    have e1 : (((1 - z ^ 2) / (1 + z ^ 2)) ^ 2).im = 0 := by
      have := congrArg Complex.im h1
      rw [Complex.add_im, Complex.one_im, two_mul_im_aux] at this
      linarith
    have e2 : (((1 - z ^ 2) / (1 + z ^ 2)) ^ 2).re ≤ 0 := by
      have := congrArg Complex.re h1
      rw [Complex.add_re, Complex.one_re, two_mul_re_aux] at this
      linarith
    exact ⟨e1, e2⟩
  · rintro ⟨him, hre⟩
    simp only [Complex.neg_im, Complex.neg_re] at him hre
    have h1 := one_sub_uC hne
    have hm := re_div_one_add_sq_pos hz.2 hne
    apply not_sq_nonpos hm
    have e : 8 * z ^ 2 / (1 + z ^ 2) ^ 2 = 8 * (z / (1 + z ^ 2)) ^ 2 := by
      field_simp
    rw [e] at h1
    have e1 : ((z / (1 + z ^ 2)) ^ 2).im = 0 := by
      have := congrArg Complex.im h1
      rw [Complex.sub_im, Complex.one_im, two_mul_im_aux] at this
      linarith
    have e2 : ((z / (1 + z ^ 2)) ^ 2).re ≤ 0 := by
      have := congrArg Complex.re h1
      rw [Complex.sub_re, Complex.one_re, two_mul_re_aux] at this
      linarith
    exact ⟨e1, e2⟩

lemma differentiableOn_uC : DifferentiableOn ℂ uC halfDisc := by
  intro z hz
  have hne := one_add_sq_ne_zero_of_halfDisc hz
  unfold uC
  exact (((by fun_prop : Differentiable ℂ fun z : ℂ => 1 - 6 * z ^ 2 + z ^ 4).differentiableAt).div
    ((by fun_prop : Differentiable ℂ fun z : ℂ => (1 + z ^ 2) ^ 2).differentiableAt)
    (pow_ne_zero 2 hne)).differentiableWithinAt

/-- The holomorphic `log Q⁴ / 2 = log Ŝ(u(z))` on `Ω`: `ℓ_Q(z) = ½ Log Ŝ(u(z))` is `log Q`. -/
noncomputable def logQ (z : ℂ) : ℂ := (1 / 2 : ℂ) * Complex.log (sHat (uC z))

lemma differentiableOn_logQ : DifferentiableOn ℂ logQ halfDisc := by
  intro z hz
  have h1 : DifferentiableAt ℂ (fun u => Complex.log (sHat u)) (uC z) :=
    (differentiableOn_log_sHat.differentiableAt (isOpen_sHatDom.mem_nhds (uC_mem_sHatDom hz)))
  have h2 : DifferentiableAt ℂ uC z :=
    differentiableOn_uC.differentiableAt (isOpen_halfDisc.mem_nhds hz)
  exact (((h1.comp z h2).const_mul (1 / 2 : ℂ))).differentiableWithinAt

/-- `σ`-antisymmetry of `log Q`. -/
lemma logQ_sigma {z : ℂ} (hz : z ∈ halfDisc) : logQ ((1 - z) / (1 + z)) = -logQ z := by
  have hne := one_add_sq_ne_zero_of_halfDisc hz
  have hz1 : 1 + z ≠ 0 := by
    intro h
    have : z = -1 := eq_neg_of_add_eq_zero_right h
    have h1 := hz.2; rw [this] at h1; norm_num at h1
  unfold logQ
  rw [uC_sigma hne hz1, log_sHat_neg (uC_mem_sHatDom hz)]
  ring

end FormalResearch.ModularBootstrap.FiveTerm
