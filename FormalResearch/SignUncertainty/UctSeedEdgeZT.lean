module

public import FormalResearch.SignUncertainty.UctEnvHolo
public import FormalResearch.SignUncertainty.UctSeedWHolder

/-!
# `W^seed` edge trace: the factors `Z_ε(iτ)` and `T(a(1-iτ))` as `Env2` (F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_upper.tex`, `(uct:Wseed-def)`.  **Proved.**

Both are holomorphic along the edge (`Z_ε` on `-1 < Re < 2`, `T(a(1-ζ))` on `Re ζ < 1`), so their `τ`-derivatives on the edge
are controlled by Cauchy's estimates (`env2_holo_line`) from the bounds
* `uctSeedZ_bound_wide`: `|Z_ε| ≤ 32π²(2+|τ|)⁴e^{-π|τ|}` on `-1 ≤ Re ≤ 2`, `|τ| ≥ 1/3`;
* `seedT_bound`: `T` bounded on `Re ≥ 0`.

Results: `env2_seedZi` (`Z_ε(iτ)`, envelope `C(1+|τ|)⁴e^{-π|τ|}`) and `env2_seedTi` (`T(a(1-iτ))`, constant envelope).
-/

@[expose] public section

open Complex Filter Topology Metric Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.SignUncertainty.CtOuter

/-- `|Z_ε(σ+iτ)| ≤ 32π²(2+|τ|)⁴ e^{-π|τ|}` for `-1 ≤ σ ≤ 2`, `|τ| ≥ 1/3`. -/
theorem uctSeedZ_bound_wide (ε : ℝ) {ζ : ℂ} (h0 : -1 ≤ ζ.re) (h1 : ζ.re ≤ 2) (hτ : 1 / 3 ≤ |ζ.im|) :
    ‖uctSeedZ ε ζ‖ ≤ 32 * π ^ 2 * (2 + |ζ.im|) ^ 4 * Real.exp (-(π * |ζ.im|)) := by
  set a : ℝ := π * |ζ.im| with ha
  have ha1 : 1 ≤ a := by
    have := Real.pi_gt_three; rw [ha]; nlinarith
  have hcosh : Real.cosh (π * ζ.im) = Real.cosh a := by
    rw [ha]; rcases abs_cases ζ.im with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, mul_neg, Real.cosh_neg]
  have hsh : Real.sinh (π * ζ.im) ^ 2 = Real.sinh a ^ 2 := by
    rw [ha]; rcases abs_cases ζ.im with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, mul_neg, Real.sinh_neg, neg_sq]
  have hsinhpos : 0 < Real.sinh a := Real.sinh_pos_iff.mpr (by linarith)
  have hsin2 : Real.sinh a ^ 2 ≤ ‖Complex.sin (π * ζ)‖ ^ 2 := by
    rw [← hsh]; exact norm_sin_pi_sq_ge ζ
  have hsne : Complex.sin (π * ζ) ≠ 0 := by
    intro h; rw [h, norm_zero] at hsin2; nlinarith [pow_pos hsinhpos 2]
  rw [uctSeedZ_eq_of_sin hsne, norm_mul, norm_pow, norm_div, norm_mul, norm_mul]
  have hn1 : ‖ζ‖ ≤ 2 + |ζ.im| := by
    have := Complex.norm_le_abs_re_add_abs_im ζ
    have h2 : |ζ.re| ≤ 2 := by rw [abs_le]; constructor <;> linarith
    linarith
  have hn2 : ‖1 - ζ‖ ≤ 2 + |ζ.im| := by
    have := Complex.norm_le_abs_re_add_abs_im (1 - ζ)
    have h2 : |(1 - ζ).re| ≤ 2 := by rw [abs_le]; simp; constructor <;> linarith
    simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] at this
    linarith
  have hπ : ‖(π : ℂ)‖ = π := by simp [abs_of_pos Real.pi_pos]
  rw [hπ]
  have hA := norm_seedA_le ε ζ
  rw [hcosh] at hA
  have hcs := cosh_div_sinh_sq_le ha1
  have hsinpos : 0 < ‖Complex.sin (π * ζ)‖ := norm_pos_iff.mpr hsne
  set N : ℝ := π * ‖ζ‖ * ‖1 - ζ‖ with hN
  have hN0 : 0 ≤ N := by positivity
  have hNb : N ≤ π * (2 + |ζ.im|) ^ 2 := by
    rw [hN, mul_assoc, sq]
    have : ‖ζ‖ * ‖1 - ζ‖ ≤ (2 + |ζ.im|) * (2 + |ζ.im|) :=
      mul_le_mul hn1 hn2 (norm_nonneg _) (by positivity)
    exact mul_le_mul_of_nonneg_left this Real.pi_pos.le
  have hsq : (N / ‖Complex.sin (π * ζ)‖) ^ 2 ≤ π ^ 2 * (2 + |ζ.im|) ^ 4 / Real.sinh a ^ 2 := by
    rw [div_pow]
    have h1 : N ^ 2 ≤ (π * (2 + |ζ.im|) ^ 2) ^ 2 := pow_le_pow_left₀ hN0 hNb 2
    calc N ^ 2 / ‖Complex.sin (π * ζ)‖ ^ 2 ≤ (π * (2 + |ζ.im|) ^ 2) ^ 2 / ‖Complex.sin (π * ζ)‖ ^ 2 :=
          div_le_div_of_nonneg_right h1 (by positivity)
      _ ≤ (π * (2 + |ζ.im|) ^ 2) ^ 2 / Real.sinh a ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hsin2
      _ = π ^ 2 * (2 + |ζ.im|) ^ 4 / Real.sinh a ^ 2 := by ring
  calc ‖seedA ε ζ‖ * (N / ‖Complex.sin (π * ζ)‖) ^ 2
      ≤ 2 * Real.cosh a * (π ^ 2 * (2 + |ζ.im|) ^ 4 / Real.sinh a ^ 2) :=
        mul_le_mul hA hsq (by positivity) (by positivity)
    _ = 2 * π ^ 2 * (2 + |ζ.im|) ^ 4 * (Real.cosh a / Real.sinh a ^ 2) := by ring
    _ ≤ 2 * π ^ 2 * (2 + |ζ.im|) ^ 4 * (16 * Real.exp (-a)) :=
        mul_le_mul_of_nonneg_left hcs (by positivity)
    _ = _ := by rw [ha]; ring

/-- Near the imaginary axis: `|Z_ε(ζ)| ≤ C (1+|Im ζ|)⁴ e^{-π|Im ζ|}` for `|Re ζ| ≤ 1/12`. -/
lemma uctSeedZ_envelope (ε : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ ζ : ℂ, |ζ.re| ≤ 1 / 12 →
    ‖uctSeedZ ε ζ‖ ≤ C * ((1 + |ζ.im|) ^ 4 * Real.exp (-(π * |ζ.im|))) := by
  have hcomp : IsCompact (Icc (-(1 / 12 : ℝ)) (1 / 12) ×ℂ Icc (-(1 / 3 : ℝ)) (1 / 3)) :=
    isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨B, hB⟩ := hcomp.exists_bound_of_continuousOn
    ((differentiableOn_uctSeedZ ε).continuousOn.mono (fun ζ hζ => ⟨by linarith [hζ.1.1], by linarith [hζ.1.2]⟩))
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩)
  refine ⟨max (512 * π ^ 2) (B * Real.exp (π / 3)), by positivity, fun ζ hζ => ?_⟩
  have hp := abs_le.mp hζ
  have hy0 := abs_nonneg ζ.im
  have hW0 : 0 ≤ (1 + |ζ.im|) ^ 4 * Real.exp (-(π * |ζ.im|)) := by positivity
  rcases le_or_gt (1 / 3) |ζ.im| with hy | hy
  · have := uctSeedZ_bound_wide ε (by linarith [hp.1]) (by linarith [hp.2]) hy
    have h16 : (2 + |ζ.im|) ^ 4 ≤ 16 * (1 + |ζ.im|) ^ 4 := by
      have : 2 + |ζ.im| ≤ 2 * (1 + |ζ.im|) := by linarith
      calc (2 + |ζ.im|) ^ 4 ≤ (2 * (1 + |ζ.im|)) ^ 4 := pow_le_pow_left₀ (by linarith) this 4
        _ = 16 * (1 + |ζ.im|) ^ 4 := by ring
    calc ‖uctSeedZ ε ζ‖ ≤ 32 * π ^ 2 * (2 + |ζ.im|) ^ 4 * Real.exp (-(π * |ζ.im|)) := this
      _ ≤ 32 * π ^ 2 * (16 * (1 + |ζ.im|) ^ 4) * Real.exp (-(π * |ζ.im|)) := by gcongr
      _ = 512 * π ^ 2 * ((1 + |ζ.im|) ^ 4 * Real.exp (-(π * |ζ.im|))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hW0
  · have hmem : ζ ∈ Icc (-(1 / 12 : ℝ)) (1 / 12) ×ℂ Icc (-(1 / 3 : ℝ)) (1 / 3) :=
      ⟨⟨hp.1, hp.2⟩, ⟨by linarith [(abs_lt.mp hy).1], by linarith [(abs_lt.mp hy).2]⟩⟩
    have h1 := hB ζ hmem
    have h2 : Real.exp (-(π / 3)) ≤ Real.exp (-(π * |ζ.im|)) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    have h3 : (1 : ℝ) ≤ (1 + |ζ.im|) ^ 4 := one_le_pow₀ (by linarith)
    have h4 : B ≤ B * Real.exp (π / 3) * ((1 + |ζ.im|) ^ 4 * Real.exp (-(π * |ζ.im|))) := by
      have e : Real.exp (π / 3) * Real.exp (-(π / 3)) = 1 := by rw [← Real.exp_add]; simp
      have : 1 ≤ Real.exp (π / 3) * ((1 + |ζ.im|) ^ 4 * Real.exp (-(π * |ζ.im|))) := by
        calc (1 : ℝ) = Real.exp (π / 3) * Real.exp (-(π / 3)) := e.symm
          _ ≤ Real.exp (π / 3) * ((1 + |ζ.im|) ^ 4 * Real.exp (-(π * |ζ.im|))) := by
            gcongr
            nlinarith [Real.exp_pos (-(π * |ζ.im|))]
      nlinarith
    calc ‖uctSeedZ ε ζ‖ ≤ B := h1
      _ ≤ _ := h4
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hW0

lemma weight_shift {y τ R : ℝ} (hR : 0 ≤ R) (h : |y - τ| ≤ R) :
    (1 + |y|) ^ 4 * Real.exp (-(π * |y|)) ≤ ((1 + R) ^ 4 * Real.exp (π * R)) * ((1 + |τ|) ^ 4 * Real.exp (-(π * |τ|))) := by
  have h1 : |y| ≤ |τ| + R := by
    have := abs_sub_abs_le_abs_sub y τ
    linarith
  have h2 : |τ| - R ≤ |y| := by
    have := abs_sub_abs_le_abs_sub τ y
    rw [abs_sub_comm] at this
    linarith
  have h3 : 1 + |y| ≤ (1 + R) * (1 + |τ|) := by nlinarith [abs_nonneg τ]
  have h4 : (1 + |y|) ^ 4 ≤ ((1 + R) * (1 + |τ|)) ^ 4 := pow_le_pow_left₀ (by linarith [abs_nonneg y]) h3 4
  have h5 : Real.exp (-(π * |y|)) ≤ Real.exp (π * R) * Real.exp (-(π * |τ|)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  calc (1 + |y|) ^ 4 * Real.exp (-(π * |y|)) ≤ ((1 + R) * (1 + |τ|)) ^ 4 * (Real.exp (π * R) * Real.exp (-(π * |τ|))) :=
        mul_le_mul h4 h5 (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

theorem env2_seedZi (ε : ℝ) : ∃ C : ℝ, 0 ≤ C ∧
    Env2 (fun τ : ℝ => uctSeedZ ε (0 + Complex.I * (τ : ℂ))) (fun τ => C * ((1 + |τ|) ^ 4 * Real.exp (-(π * |τ|)))) := by
  obtain ⟨C, hC0, hC⟩ := uctSeedZ_envelope ε
  have hU : IsOpen {ζ : ℂ | -1 < ζ.re ∧ ζ.re < 2} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt Complex.continuous_re continuous_const)
  have hR : (0 : ℝ) < 1 / 12 := by norm_num
  have hball : ∀ τ : ℝ, closedBall (0 + Complex.I * (τ : ℂ)) (1 / 12) ⊆ {ζ : ℂ | -1 < ζ.re ∧ ζ.re < 2} := by
    intro τ z hz
    have := Complex.abs_re_le_norm (z - (0 + Complex.I * (τ : ℂ)))
    have h2 : ‖z - (0 + Complex.I * (τ : ℂ))‖ ≤ 1 / 12 := by simpa [dist_eq_norm] using hz
    have hre : (z - (0 + Complex.I * (τ : ℂ))).re = z.re := by simp
    rw [hre] at this
    rw [abs_le] at this
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  set K : ℝ := (1 + 1 / 12) ^ 4 * Real.exp (π * (1 / 12)) with hK
  have hK0 : 0 ≤ K := by positivity
  have hsph : ∀ τ : ℝ, ∀ z ∈ sphere (0 + Complex.I * (τ : ℂ)) (1 / 12),
      ‖uctSeedZ ε z‖ ≤ C * K * ((1 + |τ|) ^ 4 * Real.exp (-(π * |τ|))) := by
    intro τ z hz
    have h2 : ‖z - (0 + Complex.I * (τ : ℂ))‖ = 1 / 12 := by simpa [dist_eq_norm] using hz
    have hre : (z - (0 + Complex.I * (τ : ℂ))).re = z.re := by simp
    have him : (z - (0 + Complex.I * (τ : ℂ))).im = z.im - τ := by simp
    have h3 := Complex.abs_re_le_norm (z - (0 + Complex.I * (τ : ℂ)))
    have h4 := Complex.abs_im_le_norm (z - (0 + Complex.I * (τ : ℂ)))
    rw [hre, h2] at h3
    rw [him, h2] at h4
    have := hC z h3
    have h5 := weight_shift (by norm_num : (0 : ℝ) ≤ 1 / 12) h4
    calc ‖uctSeedZ ε z‖ ≤ C * ((1 + |z.im|) ^ 4 * Real.exp (-(π * |z.im|))) := this
      _ ≤ C * (K * ((1 + |τ|) ^ 4 * Real.exp (-(π * |τ|)))) := mul_le_mul_of_nonneg_left h5 hC0
      _ = _ := by ring
  have hcen : ∀ τ : ℝ, ‖uctSeedZ ε (0 + Complex.I * (τ : ℂ))‖ ≤ C * ((1 + |τ|) ^ 4 * Real.exp (-(π * |τ|))) := by
    intro τ
    have := hC (0 + Complex.I * (τ : ℂ)) (by simp)
    simpa using this
  have hmain := env2_holo_line (F := uctSeedZ ε) hU
    ((differentiableOn_uctSeedZ ε)) (c₀ := 0) (d := Complex.I) (by simp) hR hball
    (fun τ => C * ((1 + |τ|) ^ 4 * Real.exp (-(π * |τ|))))
    (fun τ => C * K * ((1 + |τ|) ^ 4 * Real.exp (-(π * |τ|)))) hcen hsph
  refine ⟨C + C * K * 12 + 2 * (C * K) * 144, by positivity, hmain.mono fun τ => ?_⟩
  have hW0 : 0 ≤ (1 + |τ|) ^ 4 * Real.exp (-(π * |τ|)) := by positivity
  have : C * ((1 + |τ|) ^ 4 * Real.exp (-(π * |τ|))) + C * K * ((1 + |τ|) ^ 4 * Real.exp (-(π * |τ|))) / (1 / 12) +
      2 * (C * K * ((1 + |τ|) ^ 4 * Real.exp (-(π * |τ|)))) / (1 / 12) ^ 2 =
      (C + C * K * 12 + 2 * (C * K) * 144) * ((1 + |τ|) ^ 4 * Real.exp (-(π * |τ|))) := by ring
  exact this.le

theorem env2_seedTi (δ c : ℝ) (hc : 0 < c) : ∃ B : ℝ, 0 ≤ B ∧
    Env2 (fun τ : ℝ => seedT δ ((seedScale c : ℂ) * (1 - (0 + Complex.I * (τ : ℂ))))) (fun _ => B) := by
  obtain ⟨B, hB⟩ := seedT_bound δ
  have ha := seedScale_pos hc
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (by simp))
  have hU : IsOpen {ζ : ℂ | ζ.re < 1} := isOpen_lt Complex.continuous_re continuous_const
  have hF : DifferentiableOn ℂ (fun w : ℂ => seedT δ ((seedScale c : ℂ) * (1 - w))) {ζ : ℂ | ζ.re < 1} :=
    (seedT_differentiableOn δ).comp (by fun_prop : Differentiable ℂ fun w : ℂ => (seedScale c : ℂ) * (1 - w)).differentiableOn
      fun w hw => by
        show 0 < ((seedScale c : ℂ) * (1 - w)).re
        rw [re_mul_real_one_sub]; exact mul_pos ha (by have : w.re < 1 := hw; linarith)
  have hbd : ∀ w : ℂ, w.re ≤ 1 → ‖seedT δ ((seedScale c : ℂ) * (1 - w))‖ ≤ B := fun w hw =>
    hB _ (by rw [re_mul_real_one_sub]; exact mul_nonneg ha.le (by linarith))
  have hR : (0 : ℝ) < 1 / 2 := by norm_num
  have hball : ∀ τ : ℝ, closedBall (0 + Complex.I * (τ : ℂ)) (1 / 2) ⊆ {ζ : ℂ | ζ.re < 1} := by
    intro τ z hz
    have h2 : ‖z - (0 + Complex.I * (τ : ℂ))‖ ≤ 1 / 2 := by simpa [dist_eq_norm] using hz
    have h3 := Complex.abs_re_le_norm (z - (0 + Complex.I * (τ : ℂ)))
    have hre : (z - (0 + Complex.I * (τ : ℂ))).re = z.re := by simp
    rw [hre] at h3
    have := (abs_le.mp h3).2
    show z.re < 1
    linarith
  have hmain := env2_holo_line (F := fun w : ℂ => seedT δ ((seedScale c : ℂ) * (1 - w))) hU hF (c₀ := 0)
    (d := Complex.I) (by simp) hR hball (fun _ => B) (fun _ => B)
    (fun τ => hbd _ (by simp)) (fun τ z hz => by
      have h2 : ‖z - (0 + Complex.I * (τ : ℂ))‖ = 1 / 2 := by simpa [dist_eq_norm] using hz
      have h3 := Complex.abs_re_le_norm (z - (0 + Complex.I * (τ : ℂ)))
      have hre : (z - (0 + Complex.I * (τ : ℂ))).re = z.re := by simp
      rw [hre, h2] at h3
      exact hbd z (by linarith [(abs_le.mp h3).2]))
  refine ⟨B + B / (1 / 2) + 2 * B / (1 / 2) ^ 2, by positivity, hmain.mono fun τ => le_rfl⟩

/-- info: 'FormalResearch.SignUncertainty.uctSeedZ_envelope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uctSeedZ_envelope

/-- info: 'FormalResearch.SignUncertainty.env2_seedZi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms env2_seedZi

/-- info: 'FormalResearch.SignUncertainty.env2_seedTi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms env2_seedTi

end FormalResearch.SignUncertainty
