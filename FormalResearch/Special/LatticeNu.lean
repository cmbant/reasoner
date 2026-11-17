module

public import FormalResearch.Special.LatticeVar

/-!
# The Fermi weight `w(s) = 2π ν(2πs)(1 - ν(2πs))` and its primitive `ν(2π·)`

Ingredients of `lem:latticesum` (iii) (`Weyl/free_fermion/paper/parts/constants.tex`).  With
`ν(e) = (1 + e^e)⁻¹` (`nuR`) and `w(s) = π/(2 cosh²(πs)) = -2π ν'(2πs)` (the paper's `w`; here `wnu`):

* `hasDerivAt_nu2pi` : `d/ds ν(2πs) = -w(s)`; `integral_wnu` : `∫_a^b w = ν(2πa) - ν(2πb)`;
  `integral_wnu_sym` : `∫_{-X}^{X} w = 1 - 2ν(2πX)`;
* `wnu_neg` (`w` is even), `wnu_nonneg`, `continuous_wnu`, `nuR_le_exp` (`ν(e) ≤ e^{-e}`);
* the complex weight `wC s = 2π · hvar s` is analytic on `|Im s| ≤ ¼` with `‖wC s‖ ≤ 4π e^{-2π|Re s|}`
  (`differentiableOn_wC`, `norm_wC_le`) and agrees with `wnu` on `ℝ` (`wC_real`).
-/

@[expose] public section

namespace FormalResearch.Special.Lattice

open Filter Topology Set Complex Barnes MeasureTheory intervalIntegral

lemma hasDerivAt_nuR (e : ℝ) : HasDerivAt nuR (-(nuR e * (1 - nuR e))) e := by
  have hE := Real.exp_pos e
  have h := ((Real.hasDerivAt_exp e).const_add 1).inv (by positivity)
  unfold nuR
  refine h.congr_deriv ?_
  field_simp
  ring

lemma continuous_nuR : Continuous nuR :=
  continuous_iff_continuousAt.2 fun e => (hasDerivAt_nuR e).continuousAt

lemma nuR_neg (e : ℝ) : nuR (-e) = 1 - nuR e := by
  unfold nuR
  have h1 : 0 < 1 + Real.exp e := by positivity
  rw [Real.exp_neg]
  have := Real.exp_pos e
  field_simp
  ring

lemma nuR_le_exp (e : ℝ) : nuR e ≤ Real.exp (-e) := by
  unfold nuR
  have hE := Real.exp_pos e
  rw [Real.exp_neg]
  exact inv_anti₀ hE (by linarith)

/-- The Fermi weight `w(s) = 2π ν(2πs)(1 - ν(2πs)) = π/(2cosh²(πs))`. -/
noncomputable def wnu (s : ℝ) : ℝ := 2 * Real.pi * (nuR (2 * Real.pi * s) * (1 - nuR (2 * Real.pi * s)))

lemma wnu_nonneg (s : ℝ) : 0 ≤ wnu s := by
  have h := nuR_mem (2 * Real.pi * s)
  unfold wnu
  have := Real.pi_pos
  have : 0 ≤ nuR (2 * Real.pi * s) * (1 - nuR (2 * Real.pi * s)) := mul_nonneg h.1 (by linarith [h.2])
  positivity

lemma continuous_wnu : Continuous wnu := by
  unfold wnu
  have : Continuous fun s : ℝ => nuR (2 * Real.pi * s) :=
    continuous_nuR.comp (continuous_const.mul continuous_id)
  fun_prop

lemma wnu_neg (s : ℝ) : wnu (-s) = wnu s := by
  unfold wnu
  have : 2 * Real.pi * -s = -(2 * Real.pi * s) := by ring
  rw [this, nuR_neg]
  ring

lemma hasDerivAt_nu2pi (s : ℝ) : HasDerivAt (fun s : ℝ => nuR (2 * Real.pi * s)) (-wnu s) s := by
  have h := (hasDerivAt_nuR (2 * Real.pi * s)).comp s ((hasDerivAt_id s).const_mul (2 * Real.pi))
  refine h.congr_deriv ?_
  unfold wnu; simp; ring

theorem integral_wnu (a b : ℝ) : ∫ s in a..b, wnu s = nuR (2 * Real.pi * a) - nuR (2 * Real.pi * b) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a) (b := b)
    (f := fun s : ℝ => -nuR (2 * Real.pi * s)) (f' := wnu)
    (fun s _ => (hasDerivAt_nu2pi s).neg.congr_deriv (by ring))
    (continuous_wnu.intervalIntegrable _ _)
  rw [h]; ring

theorem integral_wnu_sym {X : ℝ} :
    ∫ s in (-X)..X, wnu s = 1 - 2 * nuR (2 * Real.pi * X) := by
  rw [integral_wnu]
  have : 2 * Real.pi * -X = -(2 * Real.pi * X) := by ring
  rw [this, nuR_neg]; ring

/-- The complex weight `2π · hvar`. -/
noncomputable def wC (s : ℂ) : ℂ := (2 * Real.pi : ℂ) * hvar s

lemma differentiableOn_wC : DifferentiableOn ℂ wC {s | |s.im| ≤ 1 / 4} :=
  (differentiableOn_const _).mul differentiableOn_hvar

lemma norm_wC_le {s : ℂ} (hs : |s.im| ≤ 1 / 4) :
    ‖wC s‖ ≤ (4 * Real.pi) * Real.exp (-(2 * Real.pi) * |s.re|) := by
  unfold wC
  rw [norm_mul]
  have h := norm_hvar_le hs
  have hn : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by
    rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
  rw [hn]
  calc 2 * Real.pi * ‖hvar s‖ ≤ 2 * Real.pi * (2 * Real.exp (-(2 * Real.pi) * |s.re|)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

lemma wC_real (x : ℝ) : wC (x : ℂ) = ((wnu x : ℝ) : ℂ) := by
  unfold wC wnu
  rw [hvar_real, ← nuR_mul_one_sub]
  push_cast; ring

end FormalResearch.Special.Lattice
