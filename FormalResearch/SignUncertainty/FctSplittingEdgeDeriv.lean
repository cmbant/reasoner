/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctCauchyEdgeDeriv
public import FormalResearch.SignUncertainty.FctWarpEdge

/-!
# Right-edge derivative bounds and left-edge `F_-`/`q₁` tail (`fct:splitting` (2))

Paper I (`constant_terms_five.tex`), `fct:splitting` (2), `(fct:Eminus-edge)` and `(fct:Fminus-edge)`.

From `FctDescentStmt h` (`(fct:F-38-bnd)`), `1 ≤ K₄`, and `fctCauchy_line_deriv_bounds` / `fctQ1_deriv_bounds`:
* `fctPhiHat_right_deriv`: `Φ̂_c(1 - iτ)` has first and second `τ`-derivatives uniformly bounded (`right_deriv`).
* `fctLeftTail`, `fctPhiHatAt_left_eq_add_tail`, `fctPhiHat_left_tail_EJ`: the left-edge `F_-`/`q₁` tail
  `-fctCauchy (7/16) (iτ) / N_c + β_c q₁(iτ)` belongs to `EJ · 0 1 0 M` (`fct:s4-proof` Step 1 on `|τ| ≥ 1/2`).

Class: proved from `FctDescentStmt` (named input).
-/

@[expose] public section

open Set Filter Topology MeasureTheory Metric
open scoped Real

namespace FormalResearch.SignUncertainty

private lemma fct_Nc_beta_bounds {K4 : ℝ} (hK4 : 1 ≤ K4) {h : FctWarpSolveStmt K4} (hD : FctDescentStmt h) :
    ∃ Kβ c₀ : ℝ, 0 ≤ Kβ ∧ ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      ‖(fctNcC K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c))⁻¹‖ ≤ 2 ∧
      ‖fctBetaC K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c)‖ ≤ Kβ * c⁻¹ ∧
      ‖fctBetaC K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c)‖ ≤ Kβ := by
  obtain ⟨C, c₀, hC⟩ := hD
  obtain ⟨Cz, cz, hz⟩ := fctWarpZero_of_solve h
  have hα : ∃ Kα c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → |fctWarpAlpha h ε c| ≤ Kα * c ^ (-(2 / 3 : ℝ)) :=
    ⟨Cz, cz, fun ε c hε hc => (hz ε c hε hc).2⟩
  obtain ⟨cD, hcD⟩ := fctDcomp_compData hK4 hα
  obtain ⟨K0, K1, _, hK0, hK1, _, hCau⟩ :=
    fctCauchy_line_deriv_bounds (σ := 3 / 8) (σζ := 1) le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  set C' : ℝ := |C| / Real.log 2 with hC'
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC'0 : 0 ≤ C' := by positivity
  set c_cut : ℝ := max (max c₀ cD) (max 1 (2 * K0 * C' + 1))
  refine ⟨2 * K1 * C', c_cut, by positivity, fun ε c hε hc => ?_⟩
  have hc0' : c₀ ≤ c := ((le_max_left _ _).trans (le_max_left _ _)).trans hc
  have hcD' : cD ≤ c := ((le_max_right _ _).trans (le_max_left _ _)).trans hc
  have hc1 : 1 ≤ c := ((le_max_left _ _).trans (le_max_right _ _)).trans hc
  have hcbig : 2 * K0 * C' + 1 ≤ c := ((le_max_right _ _).trans (le_max_right _ _)).trans hc
  have hcpos : 0 < c := by linarith
  have hDD := hcD ε c hε hcD'
  have hB : ∀ y : ℝ, ‖fctFint K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c)
      (((3 / 8 : ℝ) : ℂ) + (y : ℂ) * Complex.I)‖ ≤ C' * c⁻¹ := by
    intro y
    refine (hC ε c hε hc0' (3 / 8) y (by norm_num) (by norm_num)).trans ?_
    have hl : Real.log 2 ≤ Real.log (2 + |y|) := Real.log_le_log (by norm_num) (by linarith [abs_nonneg y])
    calc C * c⁻¹ / Real.log (2 + |y|) ≤ |C| * c⁻¹ / Real.log (2 + |y|) := by
          gcongr
          · exact (Real.log_pos (by linarith [abs_nonneg y])).le
          · exact le_abs_self C
      _ ≤ |C| * c⁻¹ / Real.log 2 := by gcongr
      _ = _ := by rw [hC']; ring
  have hline := hCau K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) (C' * c⁻¹) hcpos hDD.cont (by positivity) hB 0
  simp only [Complex.ofReal_one, Complex.ofReal_zero, zero_mul, add_zero, abs_zero, mul_one] at hline
  have hNc_sub : ‖fctNcC K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) - 1‖ ≤ K0 * (C' * c⁻¹) := by
    unfold fctNcC fctPhiWarp
    have hnot : ¬ ((1 : ℂ).re < 7 / 16) := by norm_num
    simp only [hnot, ite_false, show (1 - fctCauchy K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) (3 / 8) 1) - 1 =
      -fctCauchy K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) (3 / 8) 1 by ring, norm_neg]
    exact hline.1
  have hhalf : K0 * (C' * c⁻¹) ≤ 1 / 2 := by
    have : 2 * K0 * C' ≤ c := by linarith
    calc K0 * (C' * c⁻¹) = (2 * K0 * C') / (2 * c) := by ring
      _ ≤ c / (2 * c) := by gcongr
      _ = 1 / 2 := by field_simp
  have hNc_lb : 1 / 2 ≤ ‖fctNcC K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c)‖ := by
    have htri := norm_sub_norm_le (1 : ℂ) (1 - fctNcC K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c))
    have h1 : ‖1 - fctNcC K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c)‖ ≤ 1 / 2 := by
      rw [norm_sub_rev]; exact hNc_sub.trans hhalf
    have e : (1 : ℂ) - (1 - fctNcC K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c)) =
        fctNcC K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) := by ring
    rw [e, norm_one] at htri
    linarith
  have hNc_inv : ‖(fctNcC K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c))⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    exact inv_le_of_inv_le₀ (by norm_num) (by norm_num; exact hNc_lb)
  have hW_eq : fctPhiWarp K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) =ᶠ[𝓝 (1 : ℂ)]
      fun z => 1 - fctCauchy K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) (3 / 8) z := by
    have hopen : IsOpen {z : ℂ | 7 / 16 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have h1mem : (1 : ℂ) ∈ {z : ℂ | 7 / 16 < z.re} := by change (7 / 16 : ℝ) < (1 : ℂ).re; simp; norm_num
    filter_upwards [hopen.mem_nhds h1mem] with z hz
    unfold fctPhiWarp
    have hnot : ¬ (z.re < 7 / 16) := by have : 7 / 16 < z.re := hz; linarith
    simp only [hnot, ite_false]
  have hdW1 : deriv (fctPhiWarp K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c)) 1 =
      -deriv (fctCauchy K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) (3 / 8)) 1 := by
    rw [hW_eq.deriv_eq, deriv_const_sub]
  have hβ_bd : ‖fctBetaC K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c)‖ ≤ (2 * K1 * C') * c⁻¹ := by
    unfold fctBetaC
    rw [div_eq_mul_inv, norm_mul, hdW1, norm_neg]
    calc ‖deriv (fctCauchy K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) (3 / 8)) 1‖ *
          ‖(fctNcC K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c))⁻¹‖
        ≤ (K1 * (C' * c⁻¹)) * 2 := mul_le_mul hline.2.1 hNc_inv (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hc1_inv : c⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hc1
  refine ⟨hNc_inv, hβ_bd, hβ_bd.trans (mul_le_of_le_one_right (by positivity) hc1_inv)⟩

/-- Uniform bound `‖N_c⁻¹‖ ≤ 2` for large `c` and `ε = ±1` (from `FctDescentStmt`). -/
lemma fctNcC_inv_bound {K4 : ℝ} (hK4 : 1 ≤ K4) {h : FctWarpSolveStmt K4} (hD : FctDescentStmt h) :
    ∃ c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      ‖(fctNcC K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c))⁻¹‖ ≤ 2 := by
  obtain ⟨_, c₀, _, hNb⟩ := fct_Nc_beta_bounds hK4 hD
  exact ⟨c₀, fun ε c hε hc => (hNb ε c hε hc).1⟩

private lemma trace_deriv_line {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (a b : ℂ) (hb : ‖b‖ = 1) (hmem : ∀ t : ℝ, a + (t : ℂ) * b ∈ U) (τ : ℝ) :
    ContDiff ℝ 2 (fun t : ℝ => f (a + (t : ℂ) * b)) ∧
    ‖deriv (fun t : ℝ => f (a + (t : ℂ) * b)) τ‖ = ‖deriv f (a + (τ : ℂ) * b)‖ ∧
    ‖deriv (deriv (fun t : ℝ => f (a + (t : ℂ) * b))) τ‖ = ‖deriv (deriv f) (a + (τ : ℂ) * b)‖ := by
  have hg_cd : ContDiff ℝ 2 (fun t : ℝ => a + (t : ℂ) * b) :=
    contDiff_const.add (Complex.ofRealCLM.contDiff.mul contDiff_const)
  have hf_r : ContDiffOn ℝ 2 f U := (hf.contDiffOn hU).restrict_scalars ℝ
  have hcomp_cd : ContDiff ℝ 2 (fun t : ℝ => f (a + (t : ℂ) * b)) := by
    rw [← contDiffOn_univ]
    exact hf_r.comp hg_cd.contDiffOn fun t _ => hmem t
  have hg : ∀ t : ℝ, HasDerivAt (fun s : ℝ => a + (s : ℂ) * b) b t := fun t => by
    have := (hasDerivAt_const t a).add ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const b)
    refine this.congr_deriv ?_
    simp
  have hf1 : ∀ t : ℝ, DifferentiableAt ℂ f (a + (t : ℂ) * b) := fun t =>
    hf.differentiableAt (hU.mem_nhds (hmem t))
  have hf2 : DifferentiableAt ℂ (deriv f) (a + (τ : ℂ) * b) :=
    (hf.deriv hU).differentiableAt (hU.mem_nhds (hmem τ))
  have hd1 : ∀ t : ℝ, HasDerivAt (fun s : ℝ => f (a + (s : ℂ) * b))
      (deriv f (a + (t : ℂ) * b) * b) t := fun t => by
    have hcomp := (((hf1 t).hasDerivAt).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t (hg t)
    simpa [Function.comp_def, smul_eq_mul, mul_comm] using hcomp
  have hd2 : HasDerivAt (fun t : ℝ => deriv f (a + (t : ℂ) * b) * b)
      (deriv (deriv f) (a + (τ : ℂ) * b) * b * b) τ := by
    have hcomp := (((hf2.hasDerivAt).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt τ (hg τ)).mul_const b
    simpa [Function.comp_def, smul_eq_mul, mul_comm, mul_assoc] using hcomp
  have hev : deriv (fun t : ℝ => f (a + (t : ℂ) * b)) = fun (t : ℝ) => deriv f (a + (t : ℂ) * b) * b :=
    funext fun t => (hd1 t).deriv
  refine ⟨hcomp_cd, ?_, ?_⟩
  · rw [hev, norm_mul, hb, mul_one]
  · rw [hev, hd2.deriv, norm_mul, norm_mul, hb, mul_one, mul_one]

/-- **`fct:splitting` (2), `(fct:Eminus-edge)` (`right_deriv` of `SplittingRest`)**: for large `c` and `ε = ±1`,
`τ ↦ Φ̂_c(1 - iτ)` has uniformly bounded first and second derivatives on `ℝ`. -/
theorem fctPhiHat_right_deriv {K4 : ℝ} (hK4 : 1 ≤ K4) {h : FctWarpSolveStmt K4} (hD : FctDescentStmt h) :
    ∃ c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      ∃ M : ℝ, 0 ≤ M ∧ ∀ τ : ℝ,
        ‖deriv (fun t : ℝ => fctPhiHat h ε c (1 - (t : ℂ) * Complex.I)) τ‖ ≤ M ∧
        ‖deriv (deriv (fun t : ℝ => fctPhiHat h ε c (1 - (t : ℂ) * Complex.I))) τ‖ ≤ M := by
  obtain ⟨c0s, B, hSetup⟩ := fctSplitting_setup hK4 hD
  obtain ⟨Kβ, c0b, hKβ, hNb⟩ := fct_Nc_beta_bounds hK4 hD
  obtain ⟨_, K1, K2, _, hK1, hK2, hCau⟩ :=
    fctCauchy_line_deriv_bounds (σ := 3 / 8) (σζ := 1) le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨max c0s c0b, fun ε c hε hc => ?_⟩
  obtain ⟨hcpos, _, hDc, _, hF, _⟩ := hSetup ε c hε ((le_max_left _ _).trans hc)
  obtain ⟨hNc_inv, _, hβ_ub⟩ := hNb ε c hε ((le_max_right _ _).trans hc)
  have hB : 0 ≤ B := (norm_nonneg _).trans (hF (3 / 8) 0 le_rfl (by norm_num))
  have hF38 : ∀ y : ℝ, ‖fctFint K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) (((3 / 8 : ℝ) : ℂ) + y * Complex.I)‖ ≤ B :=
    fun y => hF (3 / 8) y le_rfl (by norm_num)
  set L1 := fctWarpL1 h ε c
  set α := fctWarpAlpha h ε c
  set Nc := fctNcC K4 ε c L1 α
  set β := fctBetaC K4 ε c L1 α
  have hU : IsOpen {z : ℂ | 7 / 16 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hC_hol : DifferentiableOn ℂ (fctCauchy K4 ε c L1 α (3 / 8)) {z : ℂ | 7 / 16 < z.re} :=
    fctCauchy_differentiableOn hcpos hDc le_rfl (by norm_num) hF38 hU fun w hw => by
      have hw' : 7 / 16 < w.re := hw
      exact ⟨by linarith, by linarith⟩
  have hQ_hol : DifferentiableOn ℂ fctQ1 {z : ℂ | 7 / 16 < z.re} :=
    fctQ1_differentiableOn_rhp.mono fun z hz => by
      have hz' : 7 / 16 < z.re := hz
      change -1 / 2 < z.re
      linarith
  have hmem : ∀ t : ℝ, (1 : ℂ) + (t : ℂ) * (-Complex.I) ∈ {z : ℂ | 7 / 16 < z.re} := fun t => by
    change (7 / 16 : ℝ) < ((1 : ℂ) + (t : ℂ) * (-Complex.I)).re
    simp; norm_num
  have hfn_eq : ∀ t : ℝ, fctPhiHat h ε c (1 - (t : ℂ) * Complex.I) =
      Nc⁻¹ - Nc⁻¹ * fctCauchy K4 ε c L1 α (3 / 8) ((1 : ℂ) + (t : ℂ) * (-Complex.I)) +
        β * fctQ1 ((1 : ℂ) + (t : ℂ) * (-Complex.I)) := fun t => by
    show fctPhiHatAt K4 ε c L1 α (1 - (t : ℂ) * Complex.I) = _
    unfold fctPhiHatAt fctPhiWarp
    have hnot : ¬ ((1 - (t : ℂ) * Complex.I).re < 7 / 16) := by simp; norm_num
    simp only [hnot, ite_false]
    rw [show (1 : ℂ) + (t : ℂ) * (-Complex.I) = 1 - (t : ℂ) * Complex.I by ring]
    ring
  refine ⟨2 * max K1 K2 * B + 4000 * Kβ, by positivity, fun τ => ?_⟩
  obtain ⟨hC_cd, hC_d1, hC_d2⟩ := trace_deriv_line hU hC_hol 1 (-Complex.I) (by simp) hmem τ
  obtain ⟨hQ_cd, hQ_d1, hQ_d2⟩ := trace_deriv_line hU hQ_hol 1 (-Complex.I) (by simp) hmem τ
  have hCau_bd := hCau K4 ε c L1 α B hcpos hDc hB hF38 (-τ)
  dsimp only at hCau_bd
  have hw0 : ((1 : ℝ) : ℂ) + ((-τ : ℝ) : ℂ) * Complex.I = (1 : ℂ) + (τ : ℂ) * (-Complex.I) := by
    push_cast; ring
  rw [hw0] at hCau_bd
  have hQ_bd := fctQ1_deriv_bounds (ζ := (1 : ℂ) + (τ : ℂ) * (-Complex.I)) (by simp)
  have hd_f1 : ∀ t : ℝ, deriv (fun s : ℝ => fctPhiHat h ε c (1 - (s : ℂ) * Complex.I)) t =
      -(Nc⁻¹ * deriv (fun s : ℝ => fctCauchy K4 ε c L1 α (3 / 8) ((1 : ℂ) + (s : ℂ) * (-Complex.I))) t) +
        β * deriv (fun s : ℝ => fctQ1 ((1 : ℂ) + (s : ℂ) * (-Complex.I))) t := fun t => by
    rw [show (fun s : ℝ => fctPhiHat h ε c (1 - (s : ℂ) * Complex.I)) = fun s : ℝ =>
        Nc⁻¹ - Nc⁻¹ * fctCauchy K4 ε c L1 α (3 / 8) ((1 : ℂ) + (s : ℂ) * (-Complex.I)) +
          β * fctQ1 ((1 : ℂ) + (s : ℂ) * (-Complex.I)) from funext hfn_eq]
    have h1 : DifferentiableAt ℝ (fun s : ℝ => fctCauchy K4 ε c L1 α (3 / 8) ((1 : ℂ) + (s : ℂ) * (-Complex.I))) t :=
      (hC_cd.differentiable (by norm_num)) t
    have h2 : DifferentiableAt ℝ (fun s : ℝ => fctQ1 ((1 : ℂ) + (s : ℂ) * (-Complex.I))) t :=
      (hQ_cd.differentiable (by norm_num)) t
    have ha := ((hasDerivAt_const t Nc⁻¹).sub ((h1.hasDerivAt).const_mul Nc⁻¹)).add ((h2.hasDerivAt).const_mul β)
    refine ha.deriv.trans ?_
    ring
  have hd_f2 : deriv (deriv (fun s : ℝ => fctPhiHat h ε c (1 - (s : ℂ) * Complex.I))) τ =
      -(Nc⁻¹ * deriv (deriv (fun s : ℝ => fctCauchy K4 ε c L1 α (3 / 8) ((1 : ℂ) + (s : ℂ) * (-Complex.I)))) τ) +
        β * deriv (deriv (fun s : ℝ => fctQ1 ((1 : ℂ) + (s : ℂ) * (-Complex.I)))) τ := by
    rw [show deriv (fun s : ℝ => fctPhiHat h ε c (1 - (s : ℂ) * Complex.I)) = fun t =>
        -(Nc⁻¹ * deriv (fun s : ℝ => fctCauchy K4 ε c L1 α (3 / 8) ((1 : ℂ) + (s : ℂ) * (-Complex.I))) t) +
          β * deriv (fun s : ℝ => fctQ1 ((1 : ℂ) + (s : ℂ) * (-Complex.I))) t from funext hd_f1]
    have hC1 : ContDiff ℝ 1 (deriv (fun s : ℝ => fctCauchy K4 ε c L1 α (3 / 8) ((1 : ℂ) + (s : ℂ) * (-Complex.I)))) :=
      hC_cd.iterate_deriv' 1 1
    have hQ1 : ContDiff ℝ 1 (deriv (fun s : ℝ => fctQ1 ((1 : ℂ) + (s : ℂ) * (-Complex.I)))) :=
      hQ_cd.iterate_deriv' 1 1
    have h1 : DifferentiableAt ℝ
        (deriv (fun s : ℝ => fctCauchy K4 ε c L1 α (3 / 8) ((1 : ℂ) + (s : ℂ) * (-Complex.I)))) τ :=
      (hC1.differentiable one_ne_zero) τ
    have h2 : DifferentiableAt ℝ (deriv (fun s : ℝ => fctQ1 ((1 : ℂ) + (s : ℂ) * (-Complex.I)))) τ :=
      (hQ1.differentiable one_ne_zero) τ
    exact (((h1.hasDerivAt.const_mul Nc⁻¹).neg).add (h2.hasDerivAt.const_mul β)).deriv
  refine ⟨?_, ?_⟩
  · rw [hd_f1 τ]
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg, norm_mul, norm_mul, hC_d1, hQ_d1]
    calc ‖Nc⁻¹‖ * ‖deriv (fctCauchy K4 ε c L1 α (3 / 8)) _‖ + ‖β‖ * ‖deriv fctQ1 _‖
        ≤ 2 * (K1 * B) + Kβ * 4000 :=
          add_le_add (mul_le_mul hNc_inv hCau_bd.2.1 (norm_nonneg _) (by positivity))
            (mul_le_mul hβ_ub hQ_bd.2.1 (norm_nonneg _) (by positivity))
      _ ≤ 2 * max K1 K2 * B + 4000 * Kβ := by
          have : K1 ≤ max K1 K2 := le_max_left _ _
          nlinarith
  · rw [hd_f2]
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg, norm_mul, norm_mul, hC_d2, hQ_d2]
    calc ‖Nc⁻¹‖ * ‖deriv (deriv (fctCauchy K4 ε c L1 α (3 / 8))) _‖ + ‖β‖ * ‖deriv (deriv fctQ1) _‖
        ≤ 2 * (K2 * B) + Kβ * 4000 :=
          add_le_add (mul_le_mul hNc_inv hCau_bd.2.2 (norm_nonneg _) (by positivity))
            (mul_le_mul hβ_ub hQ_bd.2.2 (norm_nonneg _) (by positivity))
      _ ≤ 2 * max K1 K2 * B + 4000 * Kβ := by
          have : K2 ≤ max K1 K2 := le_max_right _ _
          nlinarith

/-- The `F_-`/`q₁` tail on the left edge `Re ζ = 0`: `τ ↦ -F_-(iτ)/N_c + β_c q₁(iτ)`. -/
noncomputable def fctLeftTail (K4 ε c L1 α : ℝ) (τ : ℝ) : ℂ :=
  -(fctCauchy K4 ε c L1 α (7 / 16) ((τ : ℂ) * Complex.I) / fctNcC K4 ε c L1 α) +
    fctBetaC K4 ε c L1 α * fctQ1 ((τ : ℂ) * Complex.I)

/-- On the left edge `Re ζ = 0`, `Φ̂_c(iτ) = Φ_c(iτ)/N_c + fctLeftTail τ`. -/
lemma fctPhiHatAt_left_eq_add_tail (K4 ε c L1 α τ : ℝ) :
    fctPhiHatAt K4 ε c L1 α ((τ : ℂ) * Complex.I) =
      fctPhiC K4 ε c L1 α ((τ : ℂ) * Complex.I) / fctNcC K4 ε c L1 α + fctLeftTail K4 ε c L1 α τ := by
  unfold fctPhiHatAt fctPhiWarp fctLeftTail
  have hlt : ((τ : ℂ) * Complex.I).re < 7 / 16 := by simp
  simp only [hlt, ↓reduceIte]
  ring

/-- **The `F_-`/`q₁` left-edge tail lies in `EJ · 0 1 0`** (`(fct:Fminus-edge)` on `ℝ`, used by `fct:s4-proof` Step 1 for `|τ| ≥ 1/2`),
proved unconditionally from `FctDescentStmt`. -/
theorem fctPhiHat_left_tail_EJ {K4 : ℝ} (hK4 : 1 ≤ K4) {h : FctWarpSolveStmt K4} (hD : FctDescentStmt h) :
    ∃ c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      ∃ M : ℝ, EJ (fctLeftTail K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c)) 0 1 0 M := by
  obtain ⟨c0s, B, hSetup⟩ := fctSplitting_setup hK4 hD
  obtain ⟨Kβ, c0b, hKβ, hNb⟩ := fct_Nc_beta_bounds hK4 hD
  obtain ⟨K0, K1, K2, hK0, hK1, hK2, hCau⟩ :=
    fctCauchy_line_deriv_bounds (σ := 7 / 16) (σζ := 0) (by norm_num) le_rfl (by norm_num) (by norm_num) (by norm_num)
  refine ⟨max c0s c0b, fun ε c hε hc => ?_⟩
  obtain ⟨hcpos, _, hDc, _, hF, _⟩ := hSetup ε c hε ((le_max_left _ _).trans hc)
  obtain ⟨hNc_inv, _, hβ_ub⟩ := hNb ε c hε ((le_max_right _ _).trans hc)
  have hB : 0 ≤ B := (norm_nonneg _).trans (hF (7 / 16) 0 (by norm_num) le_rfl)
  have hF716 : ∀ y : ℝ, ‖fctFint K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) (((7 / 16 : ℝ) : ℂ) + y * Complex.I)‖ ≤ B :=
    fun y => hF (7 / 16) y (by norm_num) le_rfl
  set L1 := fctWarpL1 h ε c
  set α := fctWarpAlpha h ε c
  set Nc := fctNcC K4 ε c L1 α
  set β := fctBetaC K4 ε c L1 α
  have hU : IsOpen {z : ℂ | |z.re| < 1 / 4} := isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const
  have hC_hol : DifferentiableOn ℂ (fctCauchy K4 ε c L1 α (7 / 16)) {z : ℂ | |z.re| < 1 / 4} :=
    fctCauchy_differentiableOn hcpos hDc (by norm_num) le_rfl hF716 hU fun w hw => by
      have hw' : |w.re| < 1 / 4 := hw
      have := abs_lt.mp hw'
      exact ⟨by linarith, by linarith⟩
  have hQ_hol : DifferentiableOn ℂ fctQ1 {z : ℂ | |z.re| < 1 / 4} :=
    fctQ1_differentiableOn_rhp.mono fun z hz => by
      have hz' : |z.re| < 1 / 4 := hz
      have := abs_lt.mp hz'
      change -1 / 2 < z.re
      linarith
  have hmem : ∀ t : ℝ, (0 : ℂ) + (t : ℂ) * Complex.I ∈ {z : ℂ | |z.re| < 1 / 4} := fun t => by
    change |((0 : ℂ) + (t : ℂ) * Complex.I).re| < 1 / 4
    simp
  have hfn_eq : fctLeftTail K4 ε c L1 α = fun t : ℝ =>
      -(Nc⁻¹ * fctCauchy K4 ε c L1 α (7 / 16) ((0 : ℂ) + (t : ℂ) * Complex.I)) +
        β * fctQ1 ((0 : ℂ) + (t : ℂ) * Complex.I) := by
    funext t
    unfold fctLeftTail
    simp only [zero_add, div_eq_mul_inv]
    ring
  have hC_cd_all : ContDiff ℝ 2 (fun t : ℝ => fctCauchy K4 ε c L1 α (7 / 16) ((0 : ℂ) + (t : ℂ) * Complex.I)) :=
    (trace_deriv_line hU hC_hol 0 Complex.I (by simp) hmem 0).1
  have hQ_cd_all : ContDiff ℝ 2 (fun t : ℝ => fctQ1 ((0 : ℂ) + (t : ℂ) * Complex.I)) :=
    (trace_deriv_line hU hQ_hol 0 Complex.I (by simp) hmem 0).1
  have h_cd : ContDiff ℝ 2 (fctLeftTail K4 ε c L1 α) := by
    rw [hfn_eq]
    exact (contDiff_const.mul hC_cd_all).neg.add (contDiff_const.mul hQ_cd_all)
  set M := 2 * max K0 (max K1 K2) * B + 4000 * Kβ with hM
  refine ⟨M, ⟨by positivity, h_cd.contDiffOn, fun τ hτ => ?_, fun τ hτ => ?_, fun τ hτ => ?_⟩⟩
  · have hCau_bd := hCau K4 ε c L1 α B hcpos hDc hB hF716 τ
    simp only [Complex.ofReal_zero, zero_add] at hCau_bd
    have hQ_bd := fctQ1_deriv_bounds (ζ := (τ : ℂ) * Complex.I) (by simp)
    have hm1 : 1 ≤ 1 + |τ| := by linarith [abs_nonneg τ]
    have e0 : ejW 0 1 0 0 τ = 1 + |τ| := by unfold ejW; simp
    rw [e0]
    unfold fctLeftTail
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg, div_eq_mul_inv, norm_mul, norm_mul]
    have hK0le : K0 ≤ max K0 (max K1 K2) := le_max_left _ _
    have hMbd : 2 * K0 * B + 4000 * Kβ ≤ M := by
      rw [hM]; nlinarith [hK0le]
    calc ‖fctCauchy K4 ε c L1 α (7 / 16) ((τ : ℂ) * Complex.I)‖ * ‖Nc⁻¹‖ + ‖β‖ * ‖fctQ1 ((τ : ℂ) * Complex.I)‖
        ≤ (K0 * B * (1 + |τ|)) * 2 + Kβ * (4000 * (1 + |τ|)) := by
          refine add_le_add (mul_le_mul hCau_bd.1 hNc_inv (norm_nonneg _) (by positivity))
            (mul_le_mul hβ_ub (hQ_bd.1.trans (by nlinarith)) (norm_nonneg _) (by positivity))
      _ = (2 * K0 * B + 4000 * Kβ) * (1 + |τ|) := by ring
      _ ≤ M * (1 + |τ|) := mul_le_mul_of_nonneg_right hMbd (by positivity)
  · obtain ⟨_, hC_d1, _⟩ := trace_deriv_line hU hC_hol 0 Complex.I (by simp) hmem τ
    obtain ⟨_, hQ_d1, _⟩ := trace_deriv_line hU hQ_hol 0 Complex.I (by simp) hmem τ
    have hCau_bd := hCau K4 ε c L1 α B hcpos hDc hB hF716 τ
    dsimp only at hCau_bd
    simp only [Complex.ofReal_zero] at hCau_bd
    have hQ_bd := fctQ1_deriv_bounds (ζ := (0 : ℂ) + (τ : ℂ) * Complex.I) (by simp)
    have h1 : DifferentiableAt ℝ (fun s : ℝ => fctCauchy K4 ε c L1 α (7 / 16) ((0 : ℂ) + (s : ℂ) * Complex.I)) τ :=
      (hC_cd_all.differentiable (by norm_num)) τ
    have h2 : DifferentiableAt ℝ (fun s : ℝ => fctQ1 ((0 : ℂ) + (s : ℂ) * Complex.I)) τ :=
      (hQ_cd_all.differentiable (by norm_num)) τ
    have hd : deriv (fctLeftTail K4 ε c L1 α) τ =
        -(Nc⁻¹ * deriv (fun s : ℝ => fctCauchy K4 ε c L1 α (7 / 16) ((0 : ℂ) + (s : ℂ) * Complex.I)) τ) +
          β * deriv (fun s : ℝ => fctQ1 ((0 : ℂ) + (s : ℂ) * Complex.I)) τ := by
      rw [hfn_eq]
      exact (((h1.hasDerivAt.const_mul Nc⁻¹).neg).add (h2.hasDerivAt.const_mul β)).deriv
    have e1 : ejW 0 1 0 1 τ = |τ|⁻¹ * (1 + |τ|) ^ 2 := by
      unfold ejW
      rw [show (0 : ℝ) - ((1 : ℕ) : ℝ) = -1 by norm_num, Real.rpow_neg_one]
      simp
    have hw1 : 1 ≤ |τ|⁻¹ * (1 + |τ|) ^ 2 := by
      have ha : 0 < |τ| := abs_pos.mpr hτ
      have hle : |τ| ≤ (1 + |τ|) ^ 2 := by nlinarith [abs_nonneg τ]
      rw [← div_eq_inv_mul, le_div_iff₀ ha]
      linarith
    have hK1le : K1 ≤ max K0 (max K1 K2) := (le_max_left _ _).trans (le_max_right _ _)
    rw [e1, hd]
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg, norm_mul, norm_mul, hC_d1, hQ_d1]
    calc ‖Nc⁻¹‖ * ‖deriv (fctCauchy K4 ε c L1 α (7 / 16)) _‖ + ‖β‖ * ‖deriv fctQ1 _‖
        ≤ 2 * (K1 * B) + Kβ * 4000 :=
          add_le_add (mul_le_mul hNc_inv hCau_bd.2.1 (norm_nonneg _) (by positivity))
            (mul_le_mul hβ_ub hQ_bd.2.1 (norm_nonneg _) (by positivity))
      _ ≤ M * 1 := by rw [hM]; nlinarith [hK1le]
      _ ≤ M * (|τ|⁻¹ * (1 + |τ|) ^ 2) := mul_le_mul_of_nonneg_left hw1 (by positivity)
  · obtain ⟨_, _, hC_d2⟩ := trace_deriv_line hU hC_hol 0 Complex.I (by simp) hmem τ
    obtain ⟨_, _, hQ_d2⟩ := trace_deriv_line hU hQ_hol 0 Complex.I (by simp) hmem τ
    have hCau_bd := hCau K4 ε c L1 α B hcpos hDc hB hF716 τ
    dsimp only at hCau_bd
    simp only [Complex.ofReal_zero] at hCau_bd
    have hQ_bd := fctQ1_deriv_bounds (ζ := (0 : ℂ) + (τ : ℂ) * Complex.I) (by simp)
    have hdf1 : ∀ t : ℝ, deriv (fctLeftTail K4 ε c L1 α) t =
        -(Nc⁻¹ * deriv (fun s : ℝ => fctCauchy K4 ε c L1 α (7 / 16) ((0 : ℂ) + (s : ℂ) * Complex.I)) t) +
          β * deriv (fun s : ℝ => fctQ1 ((0 : ℂ) + (s : ℂ) * Complex.I)) t := fun t => by
      have h1 : DifferentiableAt ℝ (fun s : ℝ => fctCauchy K4 ε c L1 α (7 / 16) ((0 : ℂ) + (s : ℂ) * Complex.I)) t :=
        (hC_cd_all.differentiable (by norm_num)) t
      have h2 : DifferentiableAt ℝ (fun s : ℝ => fctQ1 ((0 : ℂ) + (s : ℂ) * Complex.I)) t :=
        (hQ_cd_all.differentiable (by norm_num)) t
      rw [hfn_eq]
      exact (((h1.hasDerivAt.const_mul Nc⁻¹).neg).add (h2.hasDerivAt.const_mul β)).deriv
    have hC1 : ContDiff ℝ 1 (deriv (fun s : ℝ => fctCauchy K4 ε c L1 α (7 / 16) ((0 : ℂ) + (s : ℂ) * Complex.I))) :=
      hC_cd_all.iterate_deriv' 1 1
    have hQ1 : ContDiff ℝ 1 (deriv (fun s : ℝ => fctQ1 ((0 : ℂ) + (s : ℂ) * Complex.I))) :=
      hQ_cd_all.iterate_deriv' 1 1
    have h1 : DifferentiableAt ℝ
        (deriv (fun s : ℝ => fctCauchy K4 ε c L1 α (7 / 16) ((0 : ℂ) + (s : ℂ) * Complex.I))) τ :=
      (hC1.differentiable one_ne_zero) τ
    have h2 : DifferentiableAt ℝ (deriv (fun s : ℝ => fctQ1 ((0 : ℂ) + (s : ℂ) * Complex.I))) τ :=
      (hQ1.differentiable one_ne_zero) τ
    have hd2 : deriv (deriv (fctLeftTail K4 ε c L1 α)) τ =
        -(Nc⁻¹ * deriv (deriv (fun s : ℝ => fctCauchy K4 ε c L1 α (7 / 16) ((0 : ℂ) + (s : ℂ) * Complex.I))) τ) +
          β * deriv (deriv (fun s : ℝ => fctQ1 ((0 : ℂ) + (s : ℂ) * Complex.I))) τ := by
      rw [funext hdf1]
      exact (((h1.hasDerivAt.const_mul Nc⁻¹).neg).add (h2.hasDerivAt.const_mul β)).deriv
    have e2 : ejW 0 1 0 2 τ = (τ ^ 2)⁻¹ * (1 + |τ|) ^ 3 := by
      unfold ejW
      rw [show (0 : ℝ) - ((2 : ℕ) : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (abs_nonneg τ),
        Real.rpow_natCast, sq_abs]
      simp
    have hw2 : 1 ≤ (τ ^ 2)⁻¹ * (1 + |τ|) ^ 3 := by
      have ha : 0 < τ ^ 2 := sq_pos_of_ne_zero hτ
      have hle : τ ^ 2 ≤ (1 + |τ|) ^ 3 := by
        rw [← sq_abs]
        nlinarith [abs_nonneg τ, sq_nonneg |τ|]
      rw [← div_eq_inv_mul, le_div_iff₀ ha]
      linarith
    have hK2le : K2 ≤ max K0 (max K1 K2) := (le_max_right _ _).trans (le_max_right _ _)
    rw [e2, hd2]
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg, norm_mul, norm_mul, hC_d2, hQ_d2]
    calc ‖Nc⁻¹‖ * ‖deriv (deriv (fctCauchy K4 ε c L1 α (7 / 16))) _‖ + ‖β‖ * ‖deriv (deriv fctQ1) _‖
        ≤ 2 * (K2 * B) + Kβ * 4000 :=
          add_le_add (mul_le_mul hNc_inv hCau_bd.2.2 (norm_nonneg _) (by positivity))
            (mul_le_mul hβ_ub hQ_bd.2.2 (norm_nonneg _) (by positivity))
      _ ≤ M * 1 := by rw [hM]; nlinarith [hK2le]
      _ ≤ M * ((τ ^ 2)⁻¹ * (1 + |τ|) ^ 3) := mul_le_mul_of_nonneg_left hw2 (by positivity)

/-- info: 'FormalResearch.SignUncertainty.fctPhiHat_right_deriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctPhiHat_right_deriv

/-- info: 'FormalResearch.SignUncertainty.fctPhiHat_left_tail_EJ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctPhiHat_left_tail_EJ

end FormalResearch.SignUncertainty
