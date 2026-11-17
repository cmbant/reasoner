module

public import FormalResearch.Special.BarnesIntegral
public import FormalResearch.Special.BarnesEntire

/-!
# `thm:BG`: the Barnes/Gamma identity (real form)

For real `|θ| < π` and `b = θ/(2π)`:

`-(1/4π) ∫_ℝ log((cosh πx + cos θ)/(cosh πx + 1)) · Re ψ(1/2 + ix/2) dx = log (G(1+b) G(1-b))`,

with `G` Barnes' function (`barnesG`, normalised by `G(1) = 1`, `G(z+1) = Γ(z) G(z)`), i.e. the second
equality of (BG) in the real form (BGreal) of `thm:BG`
(Weyl/free_fermion/paper/parts/constants.tex).

* `bgInt_hasDerivAt_closed` : `B'(θ) = Re(Q(1+b) - Q(1-b))/(2π)` (the formula (BGpsi) before the last
  form), from `hasDerivAt_bgInt` and the contour shift `integral_digamma_div_kerD`;
* `hasDerivAt_logGG`: the same derivative for `Re(log G(1+b) + log G(1-b))` (termwise from `Q = (log G)'`);
* `bgInt_eq_logGG` and the headline `barnes_gamma_identity` (`B(θ) = log [G(1+b) G(1-b)]`);
* `barnes_gamma_deriv`: (BGpsi) `B'(θ) = (b/2π)[ψ(1+b) + ψ(1-b) - 2]`.
-/

@[expose] public section

namespace FormalResearch.Special.Barnes

open Filter Topology Set Complex MeasureTheory Metric
open scoped Real

local notation "γ" => Real.eulerMascheroniConstant

/-- `Re ∫ ψ(z(x))/K_θ(x) dx` in real form. -/
lemma integral_rho_div_kerR {θ : ℝ} (hθ : |θ| < π) :
    ∫ x : ℝ, rhoR x / kerR θ x = (∫ x : ℝ, psiKer θ x).re := by
  have := integral_re (integrable_psiKer hθ)
  simp only [RCLike.re_to_complex] at this
  rw [← this]
  exact integral_congr_ae (Eventually.of_forall fun x => (re_psiKer θ x).symm)

/-- (BGderiv) + contour shift: `B'(θ) = Re(Q(1+b) - Q(1-b))/(2π)`. -/
theorem bgInt_hasDerivAt_closed {θ0 : ℝ} (hθ0 : |θ0| < π) :
    HasDerivAt bgInt
      ((barnesQ (1 + (θ0 : ℂ) / (2 * π)) - barnesQ (1 - (θ0 : ℂ) / (2 * π))).re / (2 * π)) θ0 := by
  have h := hasDerivAt_bgInt hθ0
  by_cases h0 : θ0 = 0
  · subst h0
    simpa using h
  · refine h.congr_deriv ?_
    rw [integral_rho_div_kerR hθ0]
    have hI : (∫ x : ℝ, psiKer θ0 x) =
        2 * (barnesQ (1 + (θ0 : ℂ) / (2 * π)) - barnesQ (1 - (θ0 : ℂ) / (2 * π))) /
          (Real.sin θ0 : ℂ) := integral_digamma_div_kerD h0 hθ0
    rw [hI]
    have hs : Real.sin θ0 ≠ 0 := sin_ne_zero_of_abs_lt h0 hθ0
    have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
    have : (2 * (barnesQ (1 + (θ0 : ℂ) / (2 * π)) - barnesQ (1 - (θ0 : ℂ) / (2 * π))) /
        (Real.sin θ0 : ℂ)).re =
        2 * (barnesQ (1 + (θ0 : ℂ) / (2 * π)) - barnesQ (1 - (θ0 : ℂ) / (2 * π))).re /
          Real.sin θ0 := by
      rw [Complex.div_ofReal_re]
      simp
    rw [this]
    field_simp
    ring


/-- `Re(log G(1+b) + log G(1-b))` as a function of `θ`, `b = θ/(2π)`. -/
noncomputable def logGG (θ : ℝ) : ℝ :=
  (barnesLogG1 ((θ : ℂ) / (2 * π)) + barnesLogG1 (-((θ : ℂ) / (2 * π)))).re

lemma hasDerivAt_barnesLogG1_real {y : ℝ} (hy : -1 < y) :
    HasDerivAt (fun t : ℝ => barnesLogG1 (t : ℂ)) (barnesQ (1 + (y : ℂ))) y := by
  have := hasDerivAt_barnesLogG1 (z := (y : ℂ)) (by simpa using hy)
  exact this.comp_ofReal

theorem hasDerivAt_logGG {θ0 : ℝ} (hθ0 : |θ0| < π) :
    HasDerivAt logGG
      ((barnesQ (1 + (θ0 : ℂ) / (2 * π)) - barnesQ (1 - (θ0 : ℂ) / (2 * π))).re / (2 * π)) θ0 := by
  have hθ' := abs_lt.mp hθ0
  have hpi := Real.pi_pos
  have hb1 : -1 < θ0 / (2 * π) := by rw [lt_div_iff₀ (by positivity)]; linarith
  have hb2 : θ0 / (2 * π) < 1 := by rw [div_lt_one (by positivity)]; linarith
  have hlin : HasDerivAt (fun θ : ℝ => θ / (2 * π)) (1 / (2 * π)) θ0 := by
    simpa using (hasDerivAt_id θ0).div_const (2 * π)
  have h1 := (hasDerivAt_barnesLogG1_real hb1).scomp θ0 hlin
  have hneg : HasDerivAt (fun θ : ℝ => -(θ / (2 * π))) (-(1 / (2 * π))) θ0 := hlin.neg
  have h2 := (hasDerivAt_barnesLogG1_real (y := -(θ0 / (2 * π))) (by linarith)).scomp θ0 hneg
  have h3 := h1.add h2
  have h4 := (Complex.reCLM.hasFDerivAt (x := _)).comp_hasDerivAt θ0 h3
  have hfun : logGG = (Complex.reCLM ∘ fun θ : ℝ => (barnesLogG1 (((θ / (2 * π) : ℝ)) : ℂ) +
      barnesLogG1 (((-(θ / (2 * π)) : ℝ)) : ℂ))) := by
    funext θ
    simp [logGG]
  rw [hfun]
  refine h4.congr_deriv ?_
  simp only [Complex.reCLM_apply]
  have e1 : (1 : ℂ) + ((θ0 / (2 * π) : ℝ) : ℂ) = 1 + (θ0 : ℂ) / (2 * π) := by push_cast; ring
  have e2 : (1 : ℂ) + ((-(θ0 / (2 * π)) : ℝ) : ℂ) = 1 - (θ0 : ℂ) / (2 * π) := by push_cast; ring
  rw [e1, e2, Complex.real_smul, Complex.real_smul]
  have e3 : (((1 / (2 * π) : ℝ) : ℂ) * barnesQ (1 + (θ0 : ℂ) / (2 * π)) +
      ((-(1 / (2 * π)) : ℝ) : ℂ) * barnesQ (1 - (θ0 : ℂ) / (2 * π))) =
      ((1 / (2 * π) : ℝ) : ℂ) * (barnesQ (1 + (θ0 : ℂ) / (2 * π)) - barnesQ (1 - (θ0 : ℂ) / (2 * π))) := by
    push_cast; ring
  rw [e3, Complex.re_ofReal_mul]
  ring


lemma bgInt_zero : bgInt 0 = 0 := by
  unfold bgInt bgFun
  simp [kerR_zero]

lemma logGG_zero : logGG 0 = 0 := by
  simp [logGG, barnesLogG1_zero]

/-- `B(θ) = Re(log G(1+b) + log G(1-b))` for `|θ| < π`. -/
theorem bgInt_eq_logGG {θ : ℝ} (hθ : |θ| < π) : bgInt θ = logGG θ := by
  have hd : ∀ t ∈ Ioo (-π) π, HasDerivAt (fun θ => bgInt θ - logGG θ) 0 t := by
    intro t ht
    have ht' : |t| < π := abs_lt.mpr ⟨ht.1, ht.2⟩
    have h := (bgInt_hasDerivAt_closed ht').sub (hasDerivAt_logGG ht')
    rw [sub_self] at h
    exact h
  have hc := isOpen_Ioo.is_const_of_deriv_eq_zero (f := fun θ => bgInt θ - logGG θ)
    (s := Ioo (-π) π) isPreconnected_Ioo
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hd t ht).deriv) (x := θ) (y := 0)
    (abs_lt.mp hθ |> fun h => ⟨h.1, h.2⟩) ⟨by linarith [Real.pi_pos], Real.pi_pos⟩
  simp only [bgInt_zero, logGG_zero, sub_zero] at hc
  linarith

lemma barnesTerm_ofReal {y : ℝ} (hy : -1 < y) (k : ℕ) :
    barnesTerm k (y : ℂ) = (((k : ℝ) + 1) * Real.log (1 + y / ((k : ℝ) + 1)) - y +
      y ^ 2 / (2 * ((k : ℝ) + 1)) : ℝ) := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hpos : 0 ≤ 1 + y / ((k : ℝ) + 1) := by
    have : -1 ≤ y / ((k : ℝ) + 1) * 1 := by
      rw [mul_one, le_div_iff₀ hk]
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      nlinarith
    linarith
  unfold barnesTerm
  have h1 : (1 : ℂ) + (y : ℂ) / ((k : ℂ) + 1) = ((1 + y / ((k : ℝ) + 1) : ℝ) : ℂ) := by
    push_cast; rfl
  rw [h1, ← Complex.ofReal_log hpos]
  push_cast
  ring

lemma barnesLogG1_ofReal {y : ℝ} (hy : -1 < y) :
    barnesLogG1 (y : ℂ) = (((Real.log (2 * π) / 2 - 1 / 2) * y - (1 + γ) * y ^ 2 / 2 +
      ∑' k : ℕ, (((k : ℝ) + 1) * Real.log (1 + y / ((k : ℝ) + 1)) - y +
        y ^ 2 / (2 * ((k : ℝ) + 1))) : ℝ) : ℂ) := by
  unfold barnesLogG1 barnesLogSeries
  simp_rw [barnesTerm_ofReal hy]
  rw [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_tsum]
  push_cast
  ring_nf

lemma barnesLogG1_im_ofReal {y : ℝ} (hy : -1 < y) : (barnesLogG1 (y : ℂ)).im = 0 := by
  rw [barnesLogG1_ofReal hy]; exact Complex.ofReal_im _

lemma barnesLogG1_eq_re {y : ℝ} (hy : -1 < y) : barnesLogG1 (y : ℂ) = ((barnesLogG1 (y : ℂ)).re : ℂ) :=
  Complex.ext (by simp) (by simpa using barnesLogG1_im_ofReal hy)

/-- Real values of Barnes' `G`. -/
noncomputable def barnesGR (x : ℝ) : ℝ := (barnesG (x : ℂ)).re

lemma barnesG_ofReal_one_add {y : ℝ} (hy : -1 < y) :
    barnesG ((1 + y : ℝ) : ℂ) = ((Real.exp (barnesLogG1 (y : ℂ)).re : ℝ) : ℂ) := by
  have hre : 0 < (((1 + y : ℝ)) : ℂ).re := by simpa using (by linarith : 0 < 1 + y)
  rw [barnesG_eq_barnesG0 hre, barnesG0]
  have : (((1 + y : ℝ)) : ℂ) - 1 = (y : ℂ) := by push_cast; ring
  rw [this, Complex.ofReal_exp, ← barnesLogG1_eq_re hy]

lemma barnesGR_one_add {y : ℝ} (hy : -1 < y) :
    barnesGR (1 + y) = Real.exp (barnesLogG1 (y : ℂ)).re := by
  unfold barnesGR
  rw [barnesG_ofReal_one_add hy, Complex.ofReal_re]

lemma barnesGR_pos {x : ℝ} (hx : 0 < x) : 0 < barnesGR x := by
  have := barnesGR_one_add (y := x - 1) (by linarith)
  rw [show 1 + (x - 1) = x by ring] at this
  rw [this]; exact Real.exp_pos _


/-- **`thm:BG` (real form).**  For real `|θ| < π`, `b = θ/(2π)`,
`-(1/4π) ∫_ℝ log((cosh πx + cos θ)/(cosh πx + 1)) Re ψ(1/2 + ix/2) dx = log (G(1+b) G(1-b))`,
with `G = barnesG` Barnes' function (`G(1) = 1`, `G(z+1) = Γ(z) G(z)`), `G(1 ± b) > 0`. -/
theorem barnes_gamma_identity {θ : ℝ} (hθ : |θ| < π) :
    -(1 / (4 * π)) * ∫ x : ℝ, Real.log ((Real.cosh (π * x) + Real.cos θ) /
        (Real.cosh (π * x) + 1)) * (digamma (zOf (x : ℂ))).re =
      Real.log (barnesGR (1 + θ / (2 * π)) * barnesGR (1 - θ / (2 * π))) := by
  have hθ' := abs_lt.mp hθ
  have hpi := Real.pi_pos
  have hb1 : -1 < θ / (2 * π) := by rw [lt_div_iff₀ (by positivity)]; linarith
  have hb2 : -1 < -(θ / (2 * π)) := by
    have : θ / (2 * π) < 1 := by rw [div_lt_one (by positivity)]; linarith
    linarith
  have h := bgInt_eq_logGG hθ
  have e1 := barnesGR_one_add hb1
  have e2 := barnesGR_one_add hb2
  rw [show 1 - θ / (2 * π) = 1 + -(θ / (2 * π)) by ring, e1, e2, ← Real.exp_add, Real.log_exp]
  have : bgInt θ = -(1 / (4 * π)) * ∫ x : ℝ, Real.log ((Real.cosh (π * x) + Real.cos θ) /
        (Real.cosh (π * x) + 1)) * (digamma (zOf (x : ℂ))).re := by
    unfold bgInt bgFun kerR rhoR
    simp
  rw [← this, h]
  simp only [logGG, Complex.add_re]
  push_cast
  rfl

/-- (BGpsi): `B'(θ) = (b/2π) [Re ψ(1+b) + Re ψ(1-b) - 2]`, `b = θ/(2π)`. -/
theorem barnes_gamma_deriv {θ : ℝ} (hθ : |θ| < π) :
    HasDerivAt bgInt ((θ / (2 * π)) / (2 * π) *
      ((digamma ((1 + θ / (2 * π) : ℝ) : ℂ)).re + (digamma ((1 - θ / (2 * π) : ℝ) : ℂ)).re - 2)) θ := by
  have h := bgInt_hasDerivAt_closed hθ
  refine h.congr_deriv ?_
  have hb : ((θ : ℂ) / (2 * π)) = ((θ / (2 * π) : ℝ) : ℂ) := by push_cast; rfl
  rw [hb]
  set b : ℝ := θ / (2 * π)
  have hQ : barnesQ (1 + (b : ℂ)) - barnesQ (1 - (b : ℂ)) =
      (b : ℂ) * (digamma ((1 + b : ℝ) : ℂ) + digamma ((1 - b : ℝ) : ℂ) - 2) := by
    unfold barnesQ
    push_cast
    ring
  rw [hQ, show ((b : ℂ) * (digamma ((1 + b : ℝ) : ℂ) + digamma ((1 - b : ℝ) : ℂ) - 2)) =
      ((b : ℝ) : ℂ) * (digamma ((1 + b : ℝ) : ℂ) + digamma ((1 - b : ℝ) : ℂ) - 2) from rfl,
    Complex.re_ofReal_mul]
  simp
  ring

/-- info: 'FormalResearch.Special.Barnes.barnes_gamma_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms barnes_gamma_identity

/-- info: 'FormalResearch.Special.Barnes.barnes_gamma_deriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms barnes_gamma_deriv

end FormalResearch.Special.Barnes
