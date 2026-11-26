module

public import FormalResearch.SignUncertainty.UctE0Exp
public import FormalResearch.SignUncertainty.UctBumpE0

/-!
# `uct:bump-weighted`: the pointwise remainder bound for `E₀` (F2a)

`E0_poly_expansion`: there are a finite set `S` of monomials `a_d h^{d₀} v^{d₁}` (`1 ≤ d₀ ≤ 3`, `1 ≤ d₁ ≤ 3 d₀`) and `C_R` such that, for all `c ≥ 1` and all real `τ`, with
`h = c^{-1/2}`, `v = c^{1/2} τ`,
`|E₀(τ) - ∑_S a_d h^{d₀} v^{d₁}| ≤ C_R h⁴ (1+|v|)^{21}`.
(Inside the region `h(1+|v|)³ ≤ 1` this is the weight-four Taylor remainder `WExp.expansion`; outside it, `|E₀| ≤ 2` and the monomials are bounded by `(1+|v|)^9`.)

Class: proved, no hypotheses.
-/

@[expose] public section

open Set Filter Topology
open FormalResearch.CohnElkies

namespace FormalResearch.SignUncertainty

lemma norm_kernelAmp_le_one {c : ℝ} (hc : 0 < c) (τ : ℝ) : ‖kernelAmp c τ‖ ≤ 1 := by
  have h1 := norm_mellinK0_imag_le_one hc (one_pos : (0 : ℝ) < 1) τ
  rw [mellinK0_imag_eq one_pos τ, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one] at h1
  exact h1

theorem E0_poly_expansion :
    ∃ (S : Finset (Fin 2 →₀ ℕ)) (a : (Fin 2 →₀ ℕ) → ℂ) (CR : ℝ),
      (∀ d ∈ S, 1 ≤ d 0 ∧ d 0 < 4 ∧ d 1 ≤ 3 * d 0 ∧ 1 ≤ d 1) ∧ 0 ≤ CR ∧
      ∀ c : ℝ, 1 ≤ c → ∀ τ : ℝ,
        ‖bumpE0 c τ - ∑ d ∈ S, a d * ((((Real.sqrt c)⁻¹ : ℝ) : ℂ) ^ (d 0) * (((Real.sqrt c * τ : ℝ)) : ℂ) ^ (d 1))‖ ≤
          CR * ((Real.sqrt c)⁻¹) ^ 4 * (1 + |Real.sqrt c * τ|) ^ 21 := by
  obtain ⟨S, a, CE, hS, hCE, hexp⟩ := (E0_wexp (N := 4) (by norm_num) (by norm_num)).expansion (le_refl (1 : ℝ))
  set A : ℝ := ∑ d ∈ S, ‖a d‖ with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨S, a, max CE (2 + A), hS, le_max_of_le_left hCE, fun c hc τ => ?_⟩
  have hc0 : 0 < c := by linarith
  have hsq : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc0
  set h : ℝ := (Real.sqrt c)⁻¹ with hh
  set v : ℝ := Real.sqrt c * τ with hv
  have hh0 : 0 < h := inv_pos.mpr hsq
  have hh1 : h ≤ 1 := inv_le_one_of_one_le₀ (by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hc)
  have e1 : (h ^ 2)⁻¹ = c := by rw [hh, inv_pow, Real.sq_sqrt hc0.le, inv_inv]
  have e2 : h * v = τ := by rw [hh, hv, ← mul_assoc, inv_mul_cancel₀ hsq.ne', one_mul]
  have hE : bumpE0 c τ = kernelAmp ((h ^ 2)⁻¹) (h * v) - 1 := by rw [e1, e2]; rfl
  rw [hE]
  by_cases hreg : h * (1 + |v|) ^ 3 ≤ 1
  · have := hexp h v ⟨hh0, hreg⟩
    refine this.trans ?_
    unfold wx
    rw [mul_pow, ← pow_mul]
    have : 1 ≤ (1 + |v|) ^ 9 := one_le_pow₀ (by linarith [abs_nonneg v])
    calc CE * (h ^ 4 * (1 + |v|) ^ (3 * 4)) ≤ max CE (2 + A) * (h ^ 4 * (1 + |v|) ^ 21) := by
          refine mul_le_mul (le_max_left _ _) ?_ (by positivity) (le_trans hCE (le_max_left _ _))
          refine mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith [abs_nonneg v]) (by norm_num)) (by positivity)
      _ = _ := by ring
  · have hreg := not_le.mp hreg
    have hpos : 0 < 1 + |v| := by positivity
    have hnorm1 : ‖kernelAmp ((h ^ 2)⁻¹) (h * v) - 1‖ ≤ 2 := by
      have := norm_kernelAmp_le_one (c := (h ^ 2)⁻¹) (by positivity) (h * v)
      calc _ ≤ ‖kernelAmp ((h ^ 2)⁻¹) (h * v)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ ≤ 2 := by simp; linarith
    have hpoly : ‖∑ d ∈ S, a d * ((h : ℂ) ^ (d 0) * (v : ℂ) ^ (d 1))‖ ≤ A * (1 + |v|) ^ 9 := by
      refine (norm_sum_le _ _).trans ?_
      rw [hA, Finset.sum_mul]
      refine Finset.sum_le_sum fun d hd => ?_
      obtain ⟨h1, h2, h3, h4⟩ := hS d hd
      rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos hh0]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have hp1 : h ^ (d 0) ≤ 1 := pow_le_one₀ hh0.le hh1
      have hp2 : |v| ^ (d 1) ≤ (1 + |v|) ^ 9 :=
        (pow_le_pow_left₀ (abs_nonneg v) (by linarith) _).trans
          (pow_le_pow_right₀ (by linarith [abs_nonneg v]) (by omega))
      calc h ^ (d 0) * |v| ^ (d 1) ≤ 1 * (1 + |v|) ^ 9 :=
            mul_le_mul hp1 hp2 (by positivity) zero_le_one
        _ = _ := one_mul _
    have hbig : 1 ≤ h ^ 4 * (1 + |v|) ^ 12 := by
      have := one_le_pow₀ (n := 4) hreg.le
      rw [mul_pow, ← pow_mul] at this
      simpa using this
    have hcomb : (2 + A) * (1 + |v|) ^ 9 ≤ max CE (2 + A) * (h ^ 4 * (1 + |v|) ^ 21) := by
      have h9 : 0 ≤ (1 + |v|) ^ 9 := by positivity
      have : (1 + |v|) ^ 9 ≤ h ^ 4 * (1 + |v|) ^ 21 := by
        calc (1 + |v|) ^ 9 = 1 * (1 + |v|) ^ 9 := (one_mul _).symm
          _ ≤ (h ^ 4 * (1 + |v|) ^ 12) * (1 + |v|) ^ 9 := mul_le_mul_of_nonneg_right hbig h9
          _ = h ^ 4 * (1 + |v|) ^ 21 := by ring
      calc (2 + A) * (1 + |v|) ^ 9 ≤ (2 + A) * (h ^ 4 * (1 + |v|) ^ 21) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    calc ‖kernelAmp ((h ^ 2)⁻¹) (h * v) - 1 - ∑ d ∈ S, a d * ((h : ℂ) ^ (d 0) * (v : ℂ) ^ (d 1))‖
        ≤ ‖kernelAmp ((h ^ 2)⁻¹) (h * v) - 1‖ + ‖∑ d ∈ S, a d * ((h : ℂ) ^ (d 0) * (v : ℂ) ^ (d 1))‖ := norm_sub_le _ _
      _ ≤ 2 + A * (1 + |v|) ^ 9 := add_le_add hnorm1 hpoly
      _ ≤ (2 + A) * (1 + |v|) ^ 9 := by
          have : 1 ≤ (1 + |v|) ^ 9 := one_le_pow₀ (by linarith [abs_nonneg v])
          nlinarith
      _ ≤ _ := hcomb.trans (le_of_eq (by ring))

/-- info: 'FormalResearch.SignUncertainty.E0_poly_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms E0_poly_expansion

end FormalResearch.SignUncertainty
