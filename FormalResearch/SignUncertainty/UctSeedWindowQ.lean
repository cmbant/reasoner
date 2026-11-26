module

public import FormalResearch.SignUncertainty.UctSeedWindowY
public import FormalResearch.SignUncertainty.UctSeedWindowSym

/-!
# Expansion of `Q = T(a)⁻¹ Z_ε e^{-H_0} T(a(1-ζ))` near `ζ = 0` (F2a, `uct:seed-asymp` (1))

`seedQ = ρ · Y_ε` with `ρ(ζ) = φ(1-ζ)/φ(1)` (`seedQ_eq_rho_mul`).  For `c ≥ c₁`, `0 ≤ δ ≤ 1`, `|ζ| ≤ 1/4`:
`|ρ(ζ) - 1| ≤ C c^{-2/3}|ζ|` (`rho_sub_one_bound`) and hence
`|seedQ(ζ) - e^{-λ_ε ζ}| ≤ C (c^{-2/3}|ζ| + |ζ|²)` (`seedQ_expansion`).
-/

@[expose] public section

open Complex Filter Topology Metric Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.SignUncertainty.CtOuter

lemma phi_deriv_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ c δ : ℝ, 64 ≤ c → 0 ≤ δ → δ ≤ 1 → ∀ w : ℂ, 0 < w.re → 1 / 2 ≤ ‖w‖ →
    ‖deriv (uctPhi c δ) w‖ ≤ C * c ^ (-(2 / 3 : ℝ)) := by
  obtain ⟨C, hC, h⟩ := uct_airy_trans_phi 1
  refine ⟨8 * C, by positivity, fun c δ hc hδ0 hδ1 w hre hwn => ?_⟩
  have hc0 : 0 < c := by linarith
  have hς := liftEps_le_quarter hc
  have hςe : liftEps c = c ^ (-(1 / 3 : ℝ)) := rfl
  have h1 := h c δ hc0 hδ0 hδ1 w hre.le (by rw [← hςe]; linarith)
  have hU : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hF : DifferentiableOn ℂ (fun w : ℂ => uctPhi c δ w - 1) {w : ℂ | 0 < w.re} :=
    (differentiableOn_uctPhi hc0 δ).sub_const 1
  have hcd : ContDiffAt ℂ 1 (fun w : ℂ => uctPhi c δ w - 1) w :=
    ((hF.contDiffOn hU).contDiffAt (hU.mem_nhds hre)).of_le (by exact_mod_cast le_top)
  rw [iteratedDerivWithin_eq_iteratedDeriv uniqueDiffOn_halfplane hcd hre.le, iteratedDeriv_one,
    deriv_sub_const] at h1
  refine h1.trans ?_
  have hp : ‖w‖ ^ (-((2 : ℝ) + (1 : ℕ))) ≤ 8 := by
    have : ‖w‖ ^ (-((2 : ℝ) + (1 : ℕ))) ≤ (1 / 2 : ℝ) ^ (-((2 : ℝ) + (1 : ℕ))) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hwn (by push_cast; linarith)
    refine this.trans (le_of_eq ?_)
    push_cast
    rw [show (-((2 : ℝ) + 1)) = -(3 : ℕ) by norm_num, Real.rpow_neg (by norm_num), Real.rpow_natCast]
    norm_num
  have hp0 : 0 ≤ c ^ (-(2 / 3 : ℝ)) := (Real.rpow_pos_of_pos hc0 _).le
  nlinarith [mul_nonneg (mul_nonneg hC hp0) (sub_nonneg.mpr hp)]

lemma rho_sub_one_bound : ∃ c1 C : ℝ, 64 ≤ c1 ∧ 0 ≤ C ∧ ∀ c δ : ℝ, c1 ≤ c → 0 ≤ δ → δ ≤ 1 → ∀ ζ : ℂ, ‖ζ‖ ≤ 1 / 4 →
    ‖uctPhi c δ (1 - ζ) / uctPhi c δ 1 - 1‖ ≤ C * c ^ (-(2 / 3 : ℝ)) * ‖ζ‖ ∧
    ‖uctPhi c δ (1 - ζ) / uctPhi c δ 1‖ ≤ 1 + C := by
  obtain ⟨C0, hC0, hphi⟩ := phi_sub_one_bound
  obtain ⟨Cd, hCd, hd⟩ := phi_deriv_bound
  set x : ℝ := 4 * C0 + 4 with hx
  have hx1 : 1 ≤ x := by rw [hx]; linarith
  refine ⟨max 64 (x ^ 3), 4 / 3 * Cd, le_max_left _ _, by positivity, fun c δ hc hδ0 hδ1 ζ hζ => ?_⟩
  have hc64 : 64 ≤ c := (le_max_left _ _).trans hc
  have hcx : x ^ 3 ≤ c := (le_max_right _ _).trans hc
  have hc0 : 0 < c := by linarith
  have hς := liftEps_le_quarter hc64
  have hςe : liftEps c = c ^ (-(1 / 3 : ℝ)) := rfl
  have hp := rpow_neg_two_thirds_le hx1 hcx
  have hp0 : 0 ≤ c ^ (-(2 / 3 : ℝ)) := (Real.rpow_pos_of_pos hc0 _).le
  have hp1 : c ^ (-(2 / 3 : ℝ)) ≤ 1 := by
    refine hp.trans ?_
    rw [div_le_one (by linarith)]; exact hx1
  have hC0p : C0 * c ^ (-(2 / 3 : ℝ)) ≤ 1 / 4 := by
    calc C0 * c ^ (-(2 / 3 : ℝ)) ≤ C0 * (1 / x) := mul_le_mul_of_nonneg_left hp hC0
      _ ≤ 1 / 4 := by
        rw [mul_one_div, div_le_div_iff₀ (by linarith) (by norm_num)]
        nlinarith
  have hφ1 : ‖uctPhi c δ 1 - 1‖ ≤ 1 / 4 := by
    have := hphi c δ hc0 hδ0 hδ1 1 (by simp) (by rw [norm_one]; rw [← hςe]; linarith)
    rw [norm_one, Real.one_rpow, mul_one] at this
    exact this.trans hC0p
  have hφ1n : 3 / 4 ≤ ‖uctPhi c δ 1‖ := by
    have := norm_sub_norm_le (uctPhi c δ 1) 1
    rw [norm_one] at this
    have h3 : ‖(1 : ℂ) - uctPhi c δ 1‖ = ‖uctPhi c δ 1 - 1‖ := norm_sub_rev _ _
    have h4 := norm_sub_norm_le (1 : ℂ) (uctPhi c δ 1)
    rw [norm_one] at h4
    linarith
  have hφ1ne : uctPhi c δ 1 ≠ 0 := by
    intro h; rw [h, norm_zero] at hφ1n; linarith
  -- mean value estimate on the disc around 1
  have hmv : ‖uctPhi c δ (1 - ζ) - uctPhi c δ 1‖ ≤ Cd * c ^ (-(2 / 3 : ℝ)) * ‖ζ‖ := by
    have hs : ∀ y ∈ closedBall (1 : ℂ) (1 / 4), 3 / 4 ≤ y.re := by
      intro y hy
      have h1 : ‖y - 1‖ ≤ 1 / 4 := by simpa [dist_eq_norm] using hy
      have h2 := Complex.abs_re_le_norm (y - 1)
      rw [Complex.sub_re, Complex.one_re, abs_le] at h2
      linarith [h2.1]
    have hdf : ∀ y ∈ closedBall (1 : ℂ) (1 / 4), DifferentiableAt ℂ (uctPhi c δ) y := fun y hy =>
      ((differentiableOn_uctPhi hc0 δ).differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (show 0 < y.re by linarith [hs y hy])))
    have := Convex.norm_image_sub_le_of_norm_deriv_le (f := uctPhi c δ) (s := closedBall (1 : ℂ) (1 / 4))
      (C := Cd * c ^ (-(2 / 3 : ℝ))) hdf
      (fun y hy => hd c δ hc64 hδ0 hδ1 y (by linarith [hs y hy])
        ((by norm_num : (1 / 2 : ℝ) ≤ 3 / 4).trans ((hs y hy).trans (Complex.re_le_norm _))))
      (convex_closedBall _ _) (by simp : (1 : ℂ) ∈ closedBall (1 : ℂ) (1 / 4))
      (show 1 - ζ ∈ closedBall (1 : ℂ) (1 / 4) by simpa [dist_eq_norm] using hζ)
    simpa using this
  have e : uctPhi c δ (1 - ζ) / uctPhi c δ 1 - 1 = (uctPhi c δ (1 - ζ) - uctPhi c δ 1) / uctPhi c δ 1 := by
    field_simp
  have hb : ‖uctPhi c δ (1 - ζ) / uctPhi c δ 1 - 1‖ ≤ 4 / 3 * Cd * c ^ (-(2 / 3 : ℝ)) * ‖ζ‖ := by
    rw [e, norm_div]
    rw [div_le_iff₀ (by linarith)]
    calc ‖uctPhi c δ (1 - ζ) - uctPhi c δ 1‖ ≤ Cd * c ^ (-(2 / 3 : ℝ)) * ‖ζ‖ := hmv
      _ ≤ _ := by
        have : 0 ≤ Cd * c ^ (-(2 / 3 : ℝ)) * ‖ζ‖ := by positivity
        nlinarith
  refine ⟨hb, ?_⟩
  have h1 : ‖uctPhi c δ (1 - ζ) / uctPhi c δ 1‖ ≤ ‖uctPhi c δ (1 - ζ) / uctPhi c δ 1 - 1‖ + 1 := by
    have := norm_add_le (uctPhi c δ (1 - ζ) / uctPhi c δ 1 - 1) 1
    simpa using this
  have h2 : 4 / 3 * Cd * c ^ (-(2 / 3 : ℝ)) * ‖ζ‖ ≤ 4 / 3 * Cd := by
    have hz : ‖ζ‖ ≤ 1 := by linarith
    have : 0 ≤ 4 / 3 * Cd := by positivity
    calc 4 / 3 * Cd * c ^ (-(2 / 3 : ℝ)) * ‖ζ‖ ≤ 4 / 3 * Cd * 1 * 1 := by
          gcongr
      _ = _ := by ring
  linarith

lemma seedQ_eq_rho_mul {ε δ c : ℝ} (hc : 0 < c) {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    seedQ ε δ c ζ = (uctPhi c δ (1 - ζ) / uctPhi c δ 1) * seedYw ε ζ := by
  have hre : 0 < (1 - ζ).re := by
    have := Complex.re_le_norm ζ
    simp only [Complex.sub_re, Complex.one_re]; linarith
  have hw0 : (1 - ζ) ≠ 0 := fun h => by rw [h] at hre; simp at hre
  have hK : ((c ^ (5 / 6 : ℝ) / uctCAi : ℝ) : ℂ) ≠ 0 := by
    have : c ^ (5 / 6 : ℝ) / uctCAi ≠ 0 := div_ne_zero (Real.rpow_pos_of_pos hc _).ne' uctCAi_ne
    exact_mod_cast this
  have h5 : (1 - ζ) ^ (5 / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; tauto
  have h5' : (1 - ζ) ^ (-(5 / 2 : ℂ)) * (1 - ζ) ^ (5 / 2 : ℂ) = 1 := by
    rw [Complex.cpow_neg]; exact inv_mul_cancel₀ h5
  rw [uctPhi_eq_seedT, uctPhi_one]
  unfold seedQ seedYw
  set K : ℂ := ((c ^ (5 / 6 : ℝ) / uctCAi : ℝ) : ℂ)
  set Z := uctSeedZ ε ζ * Complex.exp (-H0 ζ)
  set P := (1 - ζ) ^ (5 / 2 : ℂ)
  set Pi := (1 - ζ) ^ (-(5 / 2 : ℂ))
  set Ta := seedT δ (seedScale c : ℂ)
  set Tb := seedT δ ((seedScale c : ℂ) * (1 - ζ))
  by_cases hTa : Ta = 0
  · simp [hTa]
  · field_simp
    linear_combination (-(uctSeedZ ε ζ * Complex.exp (-H0 ζ) * Tb)) * h5'

theorem seedQ_expansion {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    ∃ c1 C : ℝ, 64 ≤ c1 ∧ 0 ≤ C ∧ ∀ c δ : ℝ, c1 ≤ c → 0 ≤ δ → δ ≤ 1 → ∀ ζ : ℂ, ‖ζ‖ ≤ 1 / 4 →
      ‖seedQ ε δ c ζ - Complex.exp (-((seedLam ε : ℝ) : ℂ) * ζ)‖ ≤ C * (c ^ (-(2 / 3 : ℝ)) * ‖ζ‖ + ‖ζ‖ ^ 2) := by
  obtain ⟨c1, Cr, hc1, hCr, hρ⟩ := rho_sub_one_bound
  obtain ⟨CY, hCY, hY⟩ := seedYw_taylor hε
  set lam : ℝ := seedLam ε with hlam
  set E : ℝ := Real.exp (|lam| / 4) with hE
  have hE1 : 0 ≤ E := (Real.exp_pos _).le
  refine ⟨c1, (1 + Cr) * CY + Cr * E, hc1, by positivity, fun c δ hc hδ0 hδ1 ζ hζ => ?_⟩
  have hc0 : 0 < c := by linarith
  have hζ1 : ‖ζ‖ < 1 := by linarith
  obtain ⟨hρ1, hρ2⟩ := hρ c δ hc hδ0 hδ1 ζ hζ
  have hY1 := hY ζ hζ
  have hEx : ‖Complex.exp (-((lam : ℝ) : ℂ) * ζ)‖ ≤ E := by
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.mpr ?_
    have : (-((lam : ℝ) : ℂ) * ζ).re ≤ ‖(-((lam : ℝ) : ℂ) * ζ)‖ := Complex.re_le_norm _
    refine this.trans ?_
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    nlinarith [abs_nonneg lam, norm_nonneg ζ]
  rw [seedQ_eq_rho_mul hc0 hζ1]
  set ρ : ℂ := uctPhi c δ (1 - ζ) / uctPhi c δ 1
  set Ex := Complex.exp (-((lam : ℝ) : ℂ) * ζ)
  have e : ρ * seedYw ε ζ - Ex = ρ * (seedYw ε ζ - Ex) + (ρ - 1) * Ex := by ring
  rw [e]
  have hp0 : 0 ≤ c ^ (-(2 / 3 : ℝ)) := (Real.rpow_pos_of_pos hc0 _).le
  calc ‖ρ * (seedYw ε ζ - Ex) + (ρ - 1) * Ex‖ ≤ ‖ρ‖ * ‖seedYw ε ζ - Ex‖ + ‖ρ - 1‖ * ‖Ex‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul]
    _ ≤ (1 + Cr) * (CY * ‖ζ‖ ^ 2) + (Cr * c ^ (-(2 / 3 : ℝ)) * ‖ζ‖) * E := by
        gcongr
    _ ≤ _ := by
        nlinarith [mul_nonneg hp0 (norm_nonneg ζ), sq_nonneg ‖ζ‖, mul_nonneg hCr hE1, mul_nonneg hCr hCY]

/-- info: 'FormalResearch.SignUncertainty.seedQ_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms seedQ_expansion

end FormalResearch.SignUncertainty
