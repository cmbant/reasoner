module

public import FormalResearch.SignUncertainty.CtOuterPhase
public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan

/-!
# `ct:outer` (2): oddness, smoothness and holomorphy of `θ_ε` on `|τ| < 1/2`

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, `ct:outer` (2).  **Proved.**

* `outerTheta_neg`: `θ_ε` is odd;
* `contDiff_outerTheta`: `θ_ε` is `C^∞` on `ℝ` (local holomorphic continuation of `h` across the edge);
* `exists_theta_holo`: `θ_ε` is the restriction of a function holomorphic on the disc `|τ| < 1/2`:
  `Θ_ε(z) = (H(iz) - H(-iz))/(2i) - arctan z - i Log b_{1/2}(i z)·[ε = +1]`, where `H` is the holomorphic continuation
  of `h` to `B(0, 1/2)` (`outerH_eq_contH` at `y₀ = 0`, `δ = 1/2`, `R = 3/5`).
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty.CtOuter

lemma outerTheta_neg (ε : ℝ) (τ : ℝ) : outerTheta ε (-τ) = -outerTheta ε τ := by
  have hcl : Complex.I * (τ : ℂ) ∈ closedStrip := ⟨by simp, by simp⟩
  have h1 : Complex.I * ((-τ : ℝ) : ℂ) = starRingEnd ℂ (Complex.I * (τ : ℂ)) := by simp
  have h2 : (outerHbar (Complex.I * ((-τ : ℝ) : ℂ))).im = -(outerHbar (Complex.I * (τ : ℂ))).im := by
    rw [h1, outerHbar_conj hcl, Complex.conj_im]
  unfold outerTheta
  rw [h2, Real.arctan_neg, mul_neg, neg_div, Real.tanh_neg, Real.arctan_neg]
  split_ifs <;> ring

lemma contDiff_tanh_real : ContDiff ℝ ⊤ Real.tanh := by
  have : Real.tanh = fun x => Real.sinh x / Real.cosh x := by
    ext x; rw [Real.tanh_eq_sinh_div_cosh]
  rw [this]
  exact Real.contDiff_sinh.div Real.contDiff_cosh (fun x => (Real.cosh_pos x).ne')

lemma contDiffAt_imHbar (τ₀ : ℝ) :
    ContDiffAt ℝ ⊤ (fun τ : ℝ => (outerHbar (Complex.I * (τ : ℂ))).im) τ₀ := by
  obtain ⟨δ, hδ, H, hH, heq, _⟩ := exists_edge_data τ₀
  have hmem : Complex.I * (τ₀ : ℂ) ∈ ball (Complex.I * (τ₀ : ℂ)) δ := mem_ball_self hδ
  have hcd : ContDiffAt ℝ ⊤ H (Complex.I * (τ₀ : ℂ)) :=
    ((hH.contDiffOn isOpen_ball).restrict_scalars ℝ).contDiffAt (isOpen_ball.mem_nhds hmem)
  have hline : ContDiff ℝ ⊤ (fun τ : ℝ => Complex.I * (τ : ℂ)) :=
    contDiff_const.mul Complex.ofRealCLM.contDiff
  have h1 : ContDiffAt ℝ ⊤ (fun τ : ℝ => (H (Complex.I * (τ : ℂ))).im) τ₀ :=
    (Complex.imCLM.contDiff.contDiffAt).comp τ₀ (hcd.comp τ₀ hline.contDiffAt)
  refine h1.congr_of_eventuallyEq ?_
  have hnb : ∀ᶠ τ : ℝ in 𝓝 τ₀, Complex.I * (τ : ℂ) ∈ ball (Complex.I * (τ₀ : ℂ)) δ := by
    have hc : Continuous fun τ : ℝ => Complex.I * (τ : ℂ) := by fun_prop
    exact hc.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds hmem)
  filter_upwards [hnb] with τ hτ
  have hcl : Complex.I * (τ : ℂ) ∈ closedStrip := ⟨by simp, by simp⟩
  rw [outerHbar_eq_local hH heq hτ hcl]

/-- **`ct:outer` (2): smoothness.** `θ_ε` is `C^∞` on `ℝ`. -/
theorem contDiff_outerTheta (ε : ℝ) : ContDiff ℝ ⊤ (outerTheta ε) := by
  rw [contDiff_iff_contDiffAt]
  intro τ₀
  have h1 := contDiffAt_imHbar τ₀
  have h2 : ContDiffAt ℝ ⊤ (fun τ : ℝ => Real.arctan τ) τ₀ := Real.contDiff_arctan.contDiffAt
  have h3 : ContDiffAt ℝ ⊤ (fun τ : ℝ => 2 * Real.arctan (Real.tanh (π * τ / 2))) τ₀ := by
    have : ContDiff ℝ ⊤ (fun τ : ℝ => 2 * Real.arctan (Real.tanh (π * τ / 2))) :=
      contDiff_const.mul (Real.contDiff_arctan.comp (contDiff_tanh_real.comp (by fun_prop)))
    exact this.contDiffAt
  unfold outerTheta
  by_cases h : ε = 1
  · simp only [h, ↓reduceIte]; exact (h1.sub h2).sub h3
  · simp only [h, ↓reduceIte, sub_zero]; exact h1.sub h2

/-! ### Holomorphy on the disc `|τ| < 1/2` -/

lemma re_tan_pos {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < π / 2) : 0 < (Complex.tan w).re := by
  have hc : 0 < Real.cos w.re := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩
  have hs : 0 < Real.sin w.re := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
  have hnorm : 0 < Complex.normSq (Complex.cos w) := by
    rw [Complex.normSq_eq_norm_sq, norm_cos_sq]; positivity
  rw [Complex.tan, Complex.div_re]
  have hre : (Complex.sin w).re = Real.sin w.re * Real.cosh w.im := by
    conv_lhs => rw [sin_eq_re_im]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
  have him : (Complex.sin w).im = Real.cos w.re * Real.sinh w.im := by
    conv_lhs => rw [sin_eq_re_im]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, mul_zero,
      Complex.ofReal_re, Complex.I_im, mul_one, zero_add, add_zero]
  have hcre : (Complex.cos w).re = Real.cos w.re * Real.cosh w.im := by
    conv_lhs => rw [cos_eq_re_im]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, sub_zero]
  have hcim : (Complex.cos w).im = -(Real.sin w.re * Real.sinh w.im) := by
    conv_lhs => rw [cos_eq_re_im]
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, mul_zero,
      Complex.ofReal_re, Complex.I_im, mul_one, zero_sub, add_zero]
  rw [hre, him, hcre, hcim]
  have hcosh := Real.cosh_sq w.im
  have : Real.sin w.re * Real.cosh w.im * (Real.cos w.re * Real.cosh w.im) / Complex.normSq (Complex.cos w) +
      Real.cos w.re * Real.sinh w.im * -(Real.sin w.re * Real.sinh w.im) / Complex.normSq (Complex.cos w) =
      Real.sin w.re * Real.cos w.re / Complex.normSq (Complex.cos w) := by
    rw [← add_div]; congr 1; linear_combination (Real.sin w.re * Real.cos w.re) * hcosh
  rw [this]
  positivity

lemma bArg_re_mem {ζ : ℂ} (h1 : -(1 / 2 : ℝ) < ζ.re) (h2 : ζ.re < 1 / 2) :
    0 < (bArg ζ).re ∧ (bArg ζ).re < π / 2 := by
  rw [bArg_re]
  have := Real.pi_pos
  constructor <;> nlinarith

lemma differentiableAt_bHalf_disc {ζ : ℂ} (h1 : -(1 / 2 : ℝ) < ζ.re) (h2 : ζ.re < 1 / 2) :
    DifferentiableAt ℂ bHalf ζ := by
  obtain ⟨a0, a1⟩ := bArg_re_mem h1 h2
  have hc : 0 < Real.cos (bArg ζ).re := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], a1⟩
  have hne : Complex.cos (bArg ζ) ≠ 0 := by
    intro h
    have h1' := norm_cos_sq (bArg ζ)
    rw [h, norm_zero] at h1'
    nlinarith [sq_nonneg (Real.sinh (bArg ζ).im), pow_pos hc 2]
  have hb : DifferentiableAt ℂ (fun ζ : ℂ => (π : ℂ) / 4 - π * ζ / 2) ζ := by fun_prop
  have h1'' : DifferentiableAt ℂ Complex.tan (bArg ζ) := (Complex.hasDerivAt_tan hne).differentiableAt
  exact h1''.comp ζ hb

lemma re_bHalf_pos {ζ : ℂ} (h1 : -(1 / 2 : ℝ) < ζ.re) (h2 : ζ.re < 1 / 2) : 0 < (bHalf ζ).re := by
  obtain ⟨a0, a1⟩ := bArg_re_mem h1 h2
  exact re_tan_pos a0 a1

lemma re_div_one_sub_pos {u : ℂ} (hu : ‖u‖ < 1) : 0 < ((1 + u) / (1 - u)).re := by
  have hne : (1 - u) ≠ 0 := by
    intro h
    have : u = 1 := by linear_combination -h
    rw [this] at hu; simp at hu
  have hpos : 0 < Complex.normSq (1 - u) := Complex.normSq_pos.mpr hne
  rw [Complex.div_re]
  have hsq : u.re ^ 2 + u.im ^ 2 < 1 := by
    have : ‖u‖ ^ 2 < 1 := by nlinarith [norm_nonneg u]
    rwa [Complex.sq_norm, Complex.normSq_apply, ← sq, ← sq] at this
  simp only [Complex.add_re, Complex.one_re, Complex.sub_re, Complex.add_im, Complex.one_im,
    Complex.sub_im, zero_add, zero_sub]
  rw [← add_div]
  apply div_pos _ hpos
  nlinarith

lemma differentiableOn_arctan_ball : DifferentiableOn ℂ Complex.arctan (ball (0 : ℂ) 1) := by
  intro z hz
  have hzn : ‖z * Complex.I‖ < 1 := by
    rw [norm_mul, Complex.norm_I, mul_one]; exact mem_ball_zero_iff.mp hz
  have hne : (1 - z * Complex.I) ≠ 0 := by
    intro h
    have : z * Complex.I = 1 := by linear_combination -h
    rw [this] at hzn; simp at hzn
  have hslit : (1 + z * Complex.I) / (1 - z * Complex.I) ∈ slitPlane := Or.inl (re_div_one_sub_pos hzn)
  have h1 : DifferentiableAt ℂ (fun z : ℂ => (1 + z * Complex.I) / (1 - z * Complex.I)) z :=
    (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => 1 + z * Complex.I) z).div
      (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => 1 - z * Complex.I) z) hne
  have h2 := (h1.clog hslit).const_mul (-Complex.I / 2)
  exact h2.differentiableWithinAt

/-- The holomorphic continuation `H₀` of `h` to the disc `B(0, 1/2)` (`y₀ = 0`, `δ = 1/2`, `R = 3/5`). -/
noncomputable def H0 : ℂ → ℂ := contH utilde0 0 (1 / 2)

lemma ball_I_zero : ball (Complex.I * ((0 : ℝ) : ℂ)) (1 / 2 : ℝ) = ball (0 : ℂ) (1 / 2) := by simp

lemma differentiableOn_H0 : DifferentiableOn ℂ H0 (ball (0 : ℂ) (1 / 2)) := by
  have hv : DifferentiableOn ℂ utilde0 (ball (((0 : ℝ) : ℂ)) (3 / 5 : ℝ)) := by
    simpa using differentiableOn_utilde0
  have := differentiableOn_contH (y₀ := 0) (δ := 1 / 2) (R := 3 / 5) (by norm_num) (by norm_num)
    (by norm_num) hv
  simpa [H0] using this

lemma outerH_eq_H0 {ζ : ℂ} (hζ : ζ ∈ strip) (hb : ζ ∈ ball (0 : ℂ) (1 / 2)) : outerH ζ = H0 ζ := by
  have hv : DifferentiableOn ℂ utilde0 (ball (((0 : ℝ) : ℂ)) (3 / 5 : ℝ)) := by
    simpa using differentiableOn_utilde0
  have hvu : ∀ t : ℝ, |t - 0| < 3 / 5 → utilde0 (t : ℂ) = (uR t : ℂ) := fun t ht =>
    utilde0_ofReal (by simpa using ht)
  have hb' : ζ ∈ ball (Complex.I * ((0 : ℝ) : ℂ)) (1 / 2 : ℝ) := by simpa using hb
  exact outerH_eq_contH (y₀ := 0) (δ := 1 / 2) (R := 3 / 5) (v := utilde0) (by norm_num) (by norm_num) hv hvu hζ hb'

lemma outerHbar_eq_H0 {ζ : ℂ} (hcl : ζ ∈ closedStrip) (hb : ζ ∈ ball (0 : ℂ) (1 / 2)) :
    outerHbar ζ = H0 ζ := by
  have hb' : ζ ∈ ball (Complex.I * ((0 : ℝ) : ℂ)) (1 / 2 : ℝ) := by simpa using hb
  exact outerHbar_eq_local (y₀ := 0) (δ := 1 / 2) (H := H0)
    (by simpa using differentiableOn_H0) (fun ζ hζ hb => outerH_eq_H0 hζ (by simpa using hb)) hb' hcl

/-- The holomorphic extension `Θ_ε` of `θ_ε` to the disc `|z| < 1/2`. -/
noncomputable def thetaExt (ε : ℝ) (z : ℂ) : ℂ :=
  (H0 (Complex.I * z) - H0 (-(Complex.I * z))) / (2 * Complex.I) - Complex.arctan z +
    (if ε = 1 then -Complex.I * Complex.log (bHalf (Complex.I * z)) else 0)

lemma differentiableOn_thetaExt (ε : ℝ) : DifferentiableOn ℂ (thetaExt ε) (ball (0 : ℂ) (1 / 2)) := by
  have hIz : ∀ z ∈ ball (0 : ℂ) (1 / 2), Complex.I * z ∈ ball (0 : ℂ) (1 / 2) := by
    intro z hz
    simpa [mem_ball_zero_iff, norm_mul] using hz
  have hIz' : ∀ z ∈ ball (0 : ℂ) (1 / 2), -(Complex.I * z) ∈ ball (0 : ℂ) (1 / 2) := by
    intro z hz
    simpa [mem_ball_zero_iff, norm_mul] using hz
  have d1 : DifferentiableOn ℂ (fun z : ℂ => H0 (Complex.I * z)) (ball (0 : ℂ) (1 / 2)) :=
    differentiableOn_H0.comp (by fun_prop : Differentiable ℂ fun z : ℂ => Complex.I * z).differentiableOn hIz
  have d2 : DifferentiableOn ℂ (fun z : ℂ => H0 (-(Complex.I * z))) (ball (0 : ℂ) (1 / 2)) :=
    differentiableOn_H0.comp (by fun_prop : Differentiable ℂ fun z : ℂ => -(Complex.I * z)).differentiableOn hIz'
  have d3 : DifferentiableOn ℂ Complex.arctan (ball (0 : ℂ) (1 / 2)) :=
    differentiableOn_arctan_ball.mono (ball_subset_ball (by norm_num))
  have d4 : DifferentiableOn ℂ (fun z : ℂ => -Complex.I * Complex.log (bHalf (Complex.I * z)))
      (ball (0 : ℂ) (1 / 2)) := by
    intro z hz
    have hre : |(Complex.I * z).re| < 1 / 2 := by
      have := Complex.abs_re_le_norm (Complex.I * z)
      have h2 : ‖Complex.I * z‖ < 1 / 2 := by simpa [mem_ball_zero_iff, norm_mul] using hz
      linarith
    rw [abs_lt] at hre
    have hdiff : DifferentiableAt ℂ bHalf (Complex.I * z) := differentiableAt_bHalf_disc hre.1 hre.2
    have hslit : bHalf (Complex.I * z) ∈ slitPlane := Or.inl (re_bHalf_pos hre.1 hre.2)
    have := ((hdiff.comp z (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => Complex.I * z) z)).clog hslit).const_mul
      (-Complex.I)
    exact this.differentiableWithinAt
  unfold thetaExt
  by_cases h : ε = 1
  · simp only [h, ↓reduceIte]
    exact (((d1.sub d2).div_const _).sub d3).add d4
  · simp only [h, ↓reduceIte, add_zero]
    exact ((d1.sub d2).div_const _).sub d3

lemma log_bHalf_I_mul (τ : ℝ) :
    -Complex.I * Complex.log (bHalf (Complex.I * (τ : ℂ))) =
      ((-(2 * Real.arctan (Real.tanh (π * τ / 2))) : ℝ) : ℂ) := by
  set X : ℝ := Real.arctan (Real.tanh (π * τ / 2)) with hX
  have hX1 : |X| < π / 2 := by
    rw [hX]; exact abs_lt.mpr ⟨Real.neg_pi_div_two_lt_arctan _, Real.arctan_lt_pi_div_two _⟩
  have him : (-(2 * Complex.I * (X : ℂ))).im = -(2 * X) := by simp
  have hl : Complex.log (Complex.exp (-(2 * Complex.I * (X : ℂ)))) = -(2 * Complex.I * (X : ℂ)) := by
    apply Complex.log_exp
    · rw [him]; have := (abs_lt.mp hX1).2; linarith
    · rw [him]; have := (abs_lt.mp hX1).1; linarith
  rw [bHalf_I_mul, hl]
  push_cast
  ring_nf
  simp [Complex.I_sq]

lemma thetaExt_real {ε : ℝ} {τ : ℝ} (hτ : |τ| < 1 / 2) : thetaExt ε (τ : ℂ) = (outerTheta ε τ : ℂ) := by
  have hn : ‖Complex.I * (τ : ℂ)‖ < 1 / 2 := by simpa [norm_mul] using hτ
  have hb : Complex.I * (τ : ℂ) ∈ ball (0 : ℂ) (1 / 2) := mem_ball_zero_iff.mpr hn
  have hb' : -(Complex.I * (τ : ℂ)) ∈ ball (0 : ℂ) (1 / 2) := by
    rw [mem_ball_zero_iff, norm_neg]; exact hn
  have hcl : Complex.I * (τ : ℂ) ∈ closedStrip := ⟨by simp, by simp⟩
  have hcl' : -(Complex.I * (τ : ℂ)) ∈ closedStrip := ⟨by simp, by simp⟩
  have e1 : H0 (Complex.I * (τ : ℂ)) = outerHbar (Complex.I * (τ : ℂ)) := (outerHbar_eq_H0 hcl hb).symm
  have e2 : H0 (-(Complex.I * (τ : ℂ))) = starRingEnd ℂ (outerHbar (Complex.I * (τ : ℂ))) := by
    rw [← outerHbar_eq_H0 hcl' hb', ← outerHbar_conj hcl]
    congr 1; simp
  unfold thetaExt outerTheta
  rw [e1, e2, ← Complex.ofReal_arctan]
  have hIm : ((outerHbar (Complex.I * (τ : ℂ))).im : ℂ) =
      (outerHbar (Complex.I * (τ : ℂ)) - starRingEnd ℂ (outerHbar (Complex.I * (τ : ℂ)))) / (2 * Complex.I) :=
    Complex.im_eq_sub_conj _
  rw [← hIm]
  by_cases h : ε = 1
  · simp only [h, ↓reduceIte]
    rw [log_bHalf_I_mul]
    push_cast
    ring
  · simp only [h, ↓reduceIte]
    push_cast
    ring

/-- **`ct:outer` (2): structure of `θ_ε`.** `θ_ε` is odd, `C^∞` on `ℝ`, and the restriction of a function holomorphic on
the disc `|τ| < 1/2`. -/
theorem outerTheta_structure (ε : ℝ) :
    (∀ τ : ℝ, outerTheta ε (-τ) = -outerTheta ε τ) ∧ ContDiff ℝ ⊤ (outerTheta ε) ∧
      ∃ Θ : ℂ → ℂ, DifferentiableOn ℂ Θ (ball (0 : ℂ) (1 / 2)) ∧
        ∀ τ : ℝ, |τ| < 1 / 2 → Θ (τ : ℂ) = (outerTheta ε τ : ℂ) :=
  ⟨outerTheta_neg ε, contDiff_outerTheta ε, thetaExt ε, differentiableOn_thetaExt ε,
    fun _ hτ => thetaExt_real hτ⟩

end FormalResearch.SignUncertainty.CtOuter
