/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctSplittingConj
public import FormalResearch.SignUncertainty.FctDescentRay

/-!
# The descent bound `(fct:F-38-bnd)` from the interior-strip ray estimates (`fct:splitting` (1))

Paper I (`constant_terms_five.tex`), Lemma FCT.6 `fct:splitting` (1), proof, steps (a)-(e).

* `FctRayData K4 ε c L₁ α B₀ q₀ ζ`: the **interior-strip analytic estimates along the ray `ζ + i[0,∞)`**, for one `ζ = σ + iy`,
  `5/16 ≤ σ ≤ 7/16`, `y ≥ 0`:
  1. `(b)` the ray representation `ζ ∫₀¹ K₀A_ε(sζ) ds = -i ∫₀^∞ K₀A_ε(ζ + is) ds` (Cauchy on the strip with `I_ε(L₁, α) = 0` and the decay
     `|K₀A_ε(σ'+iu)| ≤ C_c (1+u)^{C_c} e^{-πu}`);
  2. `(a)` `Im g_tan(σ+iu) ≥ 0` is proved (`im_stripG_nonneg`) and is not an input;
  3. `(e)` `|g_tan(ζ+is) + L₁| ≥ q₀ log(2+y)` (`Re g_tan(σ+iu) = -log(πu/2) + O(1)`); `|g_tan'| ≤ D₀ = π/sin(5π/16) + 16/5` (`|Φ''| ≤ C`) is proved (`norm_deriv_stripG_le`);
  4. `(d)` `|W^{(j)}(ζ+is)| ≤ B₀ |A₀(ζ)| e^{-3s}`, `j = 0,1,2` (the paper's `C|A₀(ζ)|(1+s)^C e^{-πs}` is below `C' e^{-3s}`; `|A₀(ζ)|` is
     `‖N(ζ)‖/‖e^{cΦ(ζ)}‖`), `W = K₀A_ε/(e^{cΦ}Φ')`;
  5. `|W(ζ)/A₀(ζ) - 1| ≤ B₀ c⁻¹/log(2+y)` (`W(ζ)/A₀(ζ) = 1 - L₁(1-φ_kill)/(g_tan+L₁)`, `fct:phikill` (1)).
* `FctRayStmt h`: these estimates hold uniformly in `ε = ±1`, `c ≥ c₀`, `σ`, `y ≥ 0`, for the chosen zero pair.  This is the named input replacing `FctDescentStmt`.
* `fctDescent_of_ray`: **`FctRayStmt h → FctDescentStmt h`**: the two integrations by parts (`fctRay_ibp_bound`, `fctPhiC_ray_bound`), the monotone phase, and the
  reflection `y ↦ -y` (real symmetry of `F`).

Class: proved from `FctRayStmt` (named input).
-/
@[expose] public section

open Set Filter Topology MeasureTheory
open scoped Real
open FormalResearch.CohnElkies FormalResearch.SignUncertainty.CtOuter

namespace FormalResearch.SignUncertainty

/-- **The interior-strip ray estimates** of `fct:splitting` (1) at one point `ζ` (see the module docstring); `‖N(ζ)‖/‖e^{cΦ(ζ)}‖ = |A₀(ζ)|`. -/
structure FctRayData (K4 ε c L1 α B0 q0 : ℝ) (ζ : ℂ) : Prop where
  /-- `(b)`: `ζ ∫₀¹ K₀A_ε(sζ) ds = -i ∫₀^∞ K₀A_ε(ζ + is) ds`. -/
  shift : ζ * ∫ s in (0 : ℝ)..1, mellinK0 c ((s : ℂ) * ζ) (fctXi1 L1) * fctWarpA K4 ε c L1 α ((s : ℂ) * ζ) =
    -(Complex.I * ∫ s in Ioi (0 : ℝ), fctWarpKA K4 ε c L1 α (ζ + (s : ℂ) * Complex.I))
  /-- `(e)`: `|g_tan(ζ+is) + L₁| ≥ q₀ log(2 + y)`. -/
  phase_lower : ∀ s : ℝ, 0 ≤ s → q0 * Real.log (2 + ζ.im) ≤ ‖fctRayP L1 (ζ + (s : ℂ) * Complex.I)‖
  /-- `(d)`, `j = 0`. -/
  W0 : ∀ s : ℝ, 0 ≤ s → ‖fctRayW K4 ε c L1 α (ζ + (s : ℂ) * Complex.I)‖ ≤
    B0 * (‖fctRayN K4 ε c L1 α ζ‖ / ‖fctRayE c L1 ζ‖) * Real.exp (-3 * s)
  /-- `(d)`, `j = 1`. -/
  W1 : ∀ s : ℝ, 0 ≤ s → ‖deriv (fctRayW K4 ε c L1 α) (ζ + (s : ℂ) * Complex.I)‖ ≤
    B0 * (‖fctRayN K4 ε c L1 α ζ‖ / ‖fctRayE c L1 ζ‖) * Real.exp (-3 * s)
  /-- `(d)`, `j = 2`. -/
  W2 : ∀ s : ℝ, 0 ≤ s → ‖deriv (deriv (fctRayW K4 ε c L1 α)) (ζ + (s : ℂ) * Complex.I)‖ ≤
    B0 * (‖fctRayN K4 ε c L1 α ζ‖ / ‖fctRayE c L1 ζ‖) * Real.exp (-3 * s)
  /-- `|W(ζ)/A₀(ζ) - 1| ≤ B₀ c⁻¹/log(2+y)`. -/
  W_near_one : ‖fctRayE c L1 ζ * fctRayW K4 ε c L1 α ζ / fctRayN K4 ε c L1 α ζ - 1‖ ≤
    B0 / (c * Real.log (2 + ζ.im))

/-- **The named input replacing `FctDescentStmt`** (`fct:splitting` (1), steps (a)-(e)): the interior-strip ray estimates `FctRayData` hold uniformly for `ε = ±1`,
`c ≥ c₀`, `5/16 ≤ σ ≤ 7/16`, `y ≥ 0`, for the chosen zero pair of `fct:warp-asymp` (1) and `K₄`. -/
def FctRayStmt {K4 : ℝ} (h : FctWarpSolveStmt K4) : Prop :=
  ∃ B0 q0 c₀ : ℝ, 0 < q0 ∧ ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → ∀ σ y : ℝ, 5 / 16 ≤ σ → σ ≤ 7 / 16 → 0 ≤ y →
    FctRayData K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) B0 q0 ((σ : ℂ) + y * Complex.I)

/-- `N(ζ) ≠ 0` on the band `0 < Re ζ < 1/2`. -/
lemma fctRayN_ne_zero {K4 ε c L1 α : ℝ} {ζ : ℂ} (h0 : 0 < ζ.re) (h1 : ζ.re < 1 / 2) :
    fctRayN K4 ε c L1 α ζ ≠ 0 := by
  unfold fctRayN
  exact mul_ne_zero (mul_ne_zero (mellinK0_ne_zero c (by linarith) _) (Complex.exp_ne_zero _))
    (ctHG_ne_zero_of_band ε h0 h1)

/-- **`(fct:F-38-bnd)` from the ray estimates** (`fct:splitting` (1)): `FctRayStmt h → FctDescentStmt h` (`K₄ ≥ 1`). -/
theorem fctDescent_of_ray {K4 : ℝ} (hK4 : 1 ≤ K4) {h : FctWarpSolveStmt K4} (hR : FctRayStmt h) : FctDescentStmt h := by
  obtain ⟨B0, q0, c₀, hq0, hR⟩ := hR
  set D0 : ℝ := π / Real.sin (5 * π / 16) + 16 / 5 with hD0def
  have hD0 : 0 ≤ D0 := by
    have : 0 < Real.sin (5 * π / 16) := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
    positivity
  obtain ⟨Cz, cz, hz⟩ := fctWarpZero_of_solve h
  have hα : ∃ Kα c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → |fctWarpAlpha h ε c| ≤ Kα * c ^ (-(2 / 3 : ℝ)) :=
    ⟨Cz, cz, fun ε c hε hc => (hz ε c hε hc).2⟩
  obtain ⟨cD, hcD⟩ := fctDcomp_compData hK4 hα
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set l2 := Real.log 2 with hl2def
  -- the constant
  set K : ℝ := 1 / q0 + (1 / q0 + D0 / (q0 ^ 2 * l2)) / 3 with hK
  refine ⟨B0 * K + B0, max (max c₀ cD) 1, fun ε c hε hc => ?_⟩
  have hc1 : 1 ≤ c := (le_max_right _ _).trans hc
  have hcpos : 0 < c := by linarith
  have hDD := hcD ε c hε ((le_max_right _ _).trans ((le_max_left _ _).trans hc))
  have hRc := hR ε c hε ((le_max_left _ _).trans ((le_max_left _ _).trans hc))
  -- the case `y ≥ 0`
  have key : ∀ σ y : ℝ, 5 / 16 ≤ σ → σ ≤ 7 / 16 → 0 ≤ y →
      ‖fctFint K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ((σ : ℂ) + y * Complex.I)‖ ≤
        (B0 * K + B0) * c⁻¹ / Real.log (2 + y) := by
    intro σ y hσ1 hσ2 hy
    have hd := hRc σ y hσ1 hσ2 hy
    set ζ : ℂ := (σ : ℂ) + y * Complex.I with hζ
    have hζre : ζ.re = σ := by simp [hζ]
    have hζim : ζ.im = y := by simp [hζ]
    have hζS : ζ ∈ strip := ⟨by rw [hζre]; linarith, by rw [hζre]; linarith⟩
    set L := Real.log (2 + y) with hL
    have hLl : l2 ≤ L := Real.log_le_log (by norm_num) (by linarith)
    have hLpos : 0 < L := by linarith
    have hq : 0 < q0 * L := mul_pos hq0 hLpos
    have hN := fctRayN_ne_zero (K4 := K4) (ε := ε) (c := c) (L1 := fctWarpL1 h ε c) (α := fctWarpAlpha h ε c)
      (ζ := ζ) hζS.1 (by rw [hζre]; linarith)
    have hnear := hd.W_near_one
    rw [hζim] at hnear
    have hray := fctPhiC_ray_bound (ε := ε) (B0 := B0) (D := D0) hcpos hq hD0 hDD.hol hζS hN hd.shift (by rw [hζim]; exact hy)
      (fun s hs => by have := hd.phase_lower s hs; rw [hζim] at this; exact this) (fun s _ => norm_deriv_stripG_le (by simp [hζre]; linarith) (by simp [hζre]; linarith)) hd.W0 hd.W1 hd.W2
    unfold fctFint
    have h1 := norm_add_le (fctPhiC K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ζ - fctRayE c (fctWarpL1 h ε c) ζ *
        fctRayW K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ζ / fctRayN K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ζ)
      (fctRayE c (fctWarpL1 h ε c) ζ * fctRayW K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ζ /
        fctRayN K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ζ - 1)
    rw [sub_add_sub_cancel] at h1
    refine h1.trans ?_
    have hB0 : 0 ≤ B0 := by
      have := hd.W0 0 le_rfl
      simp only [mul_zero, Real.exp_zero, mul_one] at this
      have hE : 0 < ‖fctRayE c (fctWarpL1 h ε c) ζ‖ := norm_pos_iff.mpr (fctRayE_ne_zero _ _ _)
      have hNn : 0 < ‖fctRayN K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ζ‖ := norm_pos_iff.mpr hN
      have h2 := (norm_nonneg _).trans this
      by_contra hneg
      have hneg := not_le.mp hneg
      have : B0 * (‖fctRayN K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ζ‖ / ‖fctRayE c (fctWarpL1 h ε c) ζ‖) < 0 :=
        mul_neg_of_neg_of_pos hneg (div_pos hNn hE)
      linarith
    have hkap : (1 / (q0 * L) + (1 / (q0 * L) + D0 / (q0 * L) ^ 2) / 3) ≤ K / L := by
      have e1 : D0 / (q0 * L) ^ 2 ≤ D0 / (q0 ^ 2 * l2) / L := by
        rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
        have : q0 ^ 2 * l2 * L ≤ q0 ^ 2 * L ^ 2 := by
          have := mul_le_mul_of_nonneg_left hLl (by positivity : 0 ≤ q0 ^ 2 * L)
          nlinarith [this]
        nlinarith [mul_le_mul_of_nonneg_left this hD0]
      have e2 : 1 / (q0 * L) = (1 / q0) / L := by field_simp
      rw [hK, e2]
      have : (1 / q0 + (1 / q0 + D0 / (q0 ^ 2 * l2)) / 3) / L =
          1 / q0 / L + (1 / q0 / L + D0 / (q0 ^ 2 * l2) / L) / 3 := by ring
      rw [this]
      linarith
    calc _ ≤ B0 * (1 / (q0 * L) + (1 / (q0 * L) + D0 / (q0 * L) ^ 2) / 3) / c + B0 / (c * L) := add_le_add hray hnear
      _ ≤ B0 * (K / L) / c + B0 / (c * L) := by gcongr
      _ = (B0 * K + B0) * c⁻¹ / L := by field_simp
  intro σ y hσ1 hσ2
  rcases le_or_gt 0 y with hy | hy
  · rw [abs_of_nonneg hy]; exact key σ y hσ1 hσ2 hy
  · have hk := key σ (-y) hσ1 hσ2 (by linarith)
    rw [abs_of_neg hy]
    have hcj : starRingEnd ℂ ((σ : ℂ) + ((-y : ℝ) : ℂ) * Complex.I) = (σ : ℂ) + (y : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    rw [← hcj, fctFint_conj hDD.conj (by simp; linarith) (by simp; linarith), Complex.norm_conj]
    exact hk

/-- info: 'FormalResearch.SignUncertainty.fctDescent_of_ray' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctDescent_of_ray

end FormalResearch.SignUncertainty
