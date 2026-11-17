module

public import FormalResearch.Special.BarnesNormalisation

/-!
# Barnes' `G` function on the right half-plane

`G(w) = exp (barnesLogG1 (w - 1))` for `Re w > 0`, where
`barnesLogG1 z = ((1/2) log 2π - 1/2) z - (1+γ) z²/2 + ∑_k barnesTerm k z`
is the logarithm of the Weierstrass product (DLMF 5.17.3).  Proved:

* `barnesG0_one : G(1) = 1`;
* `barnesG0_add_one : G(w+1) = Γ(w) G(w)` for `Re w > 0` (the logarithmic derivative `Q` satisfies
  `Q(w+1) = Q(w) + ψ(w)`, so the ratio is constant, and `G(2) = 1` is Stirling's formula);
* `hasDerivAt_barnesG0`: `G' = Q G` with `Q(w) = (1/2) log 2π - 1/2 - (w-1) + (w-1) ψ(w)`
  (`barnesQ`), the formula of `thm:BG` (Weyl/free_fermion/paper/parts/constants.tex);
* `barnesG0_ne_zero`.

The entire extension and zeros are in `BarnesEntire`.  Not formalised: uniqueness of `G` under the
functional equation (needs a growth condition, Vignéras / Bohr–Mollerup-type).
-/

@[expose] public section

namespace FormalResearch.Special.Barnes

open Filter Topology Set Complex

local notation "γ" => Real.eulerMascheroniConstant

/-- Logarithmic derivative `Q = (log G)'` of Barnes' function (`thm:BG`, proof). -/
noncomputable def barnesQ (w : ℂ) : ℂ :=
  ((Real.log (2 * Real.pi) / 2 - 1 / 2 : ℝ) : ℂ) - (w - 1) + (w - 1) * digamma w

/-- `log G(1+z)` for `Re z > -1`. -/
noncomputable def barnesLogG1 (z : ℂ) : ℂ :=
  ((Real.log (2 * Real.pi) / 2 - 1 / 2 : ℝ) : ℂ) * z - (1 + γ) * z ^ 2 / 2 + barnesLogSeries z

/-- Barnes' `G` on `Re w > 0`. -/
noncomputable def barnesG0 (w : ℂ) : ℂ := Complex.exp (barnesLogG1 (w - 1))

lemma barnesSeries_zero : barnesLogSeries 0 = 0 := by simp [barnesLogSeries, barnesTerm_zero]

lemma barnesLogG1_zero : barnesLogG1 0 = 0 := by simp [barnesLogG1, barnesSeries_zero]

lemma barnesLogG1_one : barnesLogG1 1 = 0 := by
  rw [barnesLogG1, barnesLogSeries_one]
  push_cast
  ring

lemma barnesG0_one : barnesG0 1 = 1 := by simp [barnesG0, barnesLogG1_zero]

lemma barnesG0_two : barnesG0 2 = 1 := by
  rw [barnesG0, show (2 : ℂ) - 1 = 1 by norm_num, barnesLogG1_one, Complex.exp_zero]

lemma hasDerivAt_barnesLogG1 {z : ℂ} (hz : -1 < z.re) :
    HasDerivAt barnesLogG1 (barnesQ (1 + z)) z := by
  have h1 : HasDerivAt (fun z : ℂ => ((Real.log (2 * Real.pi) / 2 - 1 / 2 : ℝ) : ℂ) * z)
      ((Real.log (2 * Real.pi) / 2 - 1 / 2 : ℝ) : ℂ) z := by
    simpa using (hasDerivAt_id z).const_mul ((Real.log (2 * Real.pi) / 2 - 1 / 2 : ℝ) : ℂ)
  have h2 : HasDerivAt (fun z : ℂ => (1 + (γ : ℂ)) * z ^ 2 / 2) ((1 + (γ : ℂ)) * z) z := by
    have := ((hasDerivAt_pow 2 z).const_mul (1 + (γ : ℂ))).div_const 2
    convert this using 1
    simp; ring
  have h3 := (h1.sub h2).add (hasDerivAt_barnesLogSeries hz)
  refine h3.congr_deriv ?_
  unfold barnesQ
  rw [show 1 + z - 1 = z by ring]
  ring

lemma re_pos_of_mem {w : ℂ} (hw : 0 < w.re) : -1 < (w - 1).re := by simp; linarith

lemma hasDerivAt_barnesG0 {w : ℂ} (hw : 0 < w.re) :
    HasDerivAt barnesG0 (barnesQ w * barnesG0 w) w := by
  have h := (hasDerivAt_barnesLogG1 (re_pos_of_mem hw)).comp_sub_const w 1
  have h2 := h.cexp
  unfold barnesG0
  convert h2 using 1
  rw [show 1 + (w - 1) = w by ring]
  ring

lemma barnesG0_ne_zero (w : ℂ) : barnesG0 w ≠ 0 := Complex.exp_ne_zero _

lemma barnesQ_add_one {w : ℂ} (hw : 0 < w.re) : barnesQ (w + 1) = barnesQ w + digamma w := by
  have hw' : w ≠ 0 := fun h => by simp [h] at hw
  have hψ := digamma_apply_add_one w (mem_rhp_ne_neg_nat hw)
  unfold barnesQ
  rw [hψ]
  field_simp
  ring

lemma hasDerivAt_Gamma_rhp {w : ℂ} (hw : 0 < w.re) :
    HasDerivAt Gamma (digamma w * Gamma w) w := by
  have hd := differentiableAt_Gamma w (mem_rhp_ne_neg_nat hw)
  have : deriv Gamma w = digamma w * Gamma w := by
    rw [digamma_def, logDeriv_apply]
    field_simp [Gamma_ne_zero (mem_rhp_ne_neg_nat hw)]
  rw [← this]; exact hd.hasDerivAt

/-- **Functional equation** `G(w+1) = Γ(w) G(w)` for `Re w > 0`. -/
theorem barnesG0_add_one {w : ℂ} (hw : 0 < w.re) : barnesG0 (w + 1) = Gamma w * barnesG0 w := by
  set φ : ℂ → ℂ := fun w => barnesG0 (w + 1) / (Gamma w * barnesG0 w) with hφ
  have hne : ∀ w ∈ rhp, Gamma w * barnesG0 w ≠ 0 := fun w hw =>
    mul_ne_zero (Gamma_ne_zero (mem_rhp_ne_neg_nat hw)) (barnesG0_ne_zero w)
  have hder : ∀ w ∈ rhp, HasDerivAt φ 0 w := by
    intro w hw
    have hw' : 0 < w.re := hw
    have hA : HasDerivAt (fun w => barnesG0 (w + 1)) (barnesQ (w + 1) * barnesG0 (w + 1)) w :=
      (hasDerivAt_barnesG0 (by simp; linarith : 0 < (w + 1).re)).comp_add_const w 1
    have hB : HasDerivAt (fun w => Gamma w * barnesG0 w)
        (digamma w * Gamma w * barnesG0 w + Gamma w * (barnesQ w * barnesG0 w)) w :=
      (hasDerivAt_Gamma_rhp hw').mul (hasDerivAt_barnesG0 hw')
    have := hA.div hB (hne w hw)
    refine this.congr_deriv ?_
    rw [barnesQ_add_one hw']
    have hB0 := hne w hw
    field_simp
    ring
  have hconst := isOpen_rhp.is_const_of_deriv_eq_zero isPreconnected_rhp
    (fun w hw => (hder w hw).differentiableAt.differentiableWithinAt)
    (fun w hw => (hder w hw).deriv) (x := w) (y := 1) hw (by simp [rhp])
  have h1 : φ 1 = 1 := by
    simp only [hφ]
    rw [show (1 : ℂ) + 1 = 2 by norm_num, barnesG0_two, barnesG0_one, Gamma_one]; simp
  have h2 : φ w = 1 := by rw [hconst, h1]
  simp only [hφ] at h2
  rw [div_eq_one_iff_eq (hne w hw)] at h2
  exact h2

/-- info: 'FormalResearch.Special.Barnes.barnesG0_add_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms barnesG0_add_one

end FormalResearch.Special.Barnes
