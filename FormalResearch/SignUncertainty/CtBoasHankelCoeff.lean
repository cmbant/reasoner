module

public import Mathlib
public import FormalResearch.SignUncertainty.CtBoasHhatHol
public import FormalResearch.SignUncertainty.CtFejer

/-!
# `ct:boas` Step 4: the higher-harmonic bound `‖ĝ(kω₀)‖` (Regions A and B)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, `ct:boas` Step 4.  For `h = hankelHL c f` and the
Gaussian-windowed `g(L) = G_W(L - L₀) h(L)` (normalised Gaussian `gaussK`), the contour-shift bound
(`windowCoeff_gauss_shift_bound`) with `ĥ` from `hankelHhat_bound` and `S0_ineq` gives, for `k ≥ 2`,
`ω₀ = cτ₀`, `m(τ₀) = L₀`, `0 < σ ≤ min(τ₀/4, 1/4)` and `W²c²σ²/2 ≤ cσΔ_{3/2}/8`
(`Δ_{3/2} = m(3τ₀/2) - m(τ₀)`):

`‖ĝ(kω₀)‖ ≤ 3M[f] ( (3cτ₀/2π) e^{-q_B} + e^{-cσΔ_{3/2}/2} √(π/(2π²W²)) )`, `q_B = W²c²(k-3/2)²τ₀²/2 - (W²c²σ²/2 + cσL₀ + cπ²σ³/20)`

(Region B contributes the first term, Region A the second).  **Proved**, unconditional (`c > 3/2`, `ε = ±1`).
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Asymptotics
open FormalResearch.SignUncertainty.CtBoasWindow FormalResearch.SignUncertainty.CtFejer

/-- `hankelHcoord` at `ω - ν' + i a` is `ĥ(σ + iτ)` with `σ = 2πa/c`, `τ = -2π(ω - ν')/c`. -/
lemma hankelHcoord_shift_eq {c : ℝ} (hc : 0 < c) (f : ℝ → ℝ) (ω ν a : ℝ) :
    hankelHcoord c f (((ω : ℂ) + a * Complex.I) - ν) =
      hankelHhat c f (((2 * π * a / c : ℝ) : ℂ) + ((-(2 * π * (ω - ν) / c) : ℝ) : ℂ) * Complex.I) := by
  unfold hankelHcoord
  congr 1
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **`ct:boas` Step 4** (Regions A and B): the contour-shifted bound for the `k`-th Fourier coefficient of the
Gaussian-windowed Hankel density, as displayed in the module docstring. -/
theorem hankel_gauss_coeff_bound {c ε : ℝ} (hc : 3 / 2 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) {W : ℝ} (hW : 0 < W) {τ0 σ L0 k : ℝ} (hτ0 : 0 < τ0) (hσ0 : 0 < σ)
    (hσ : σ ≤ τ0 / 4) (hσ4 : σ ≤ 1 / 4) (hL : hankelEdgeM τ0 = L0) (hk : 2 ≤ k)
    (hA : W ^ 2 * c ^ 2 * σ ^ 2 / 2 ≤ c * σ * (hankelEdgeM (3 * τ0 / 2) - hankelEdgeM τ0) / 8) :
    ‖fhat (fun L => gaussK W (L - L0) * hankelHL c f L) (k * (c * τ0))‖ ≤
      3 * hankelMass c f *
        ((3 * c * τ0 / (2 * π)) *
            Real.exp (-(W ^ 2 * c ^ 2 * (k - 3 / 2) ^ 2 * τ0 ^ 2 / 2 -
              (W ^ 2 * c ^ 2 * σ ^ 2 / 2 + c * σ * L0 + c * π ^ 2 * σ ^ 3 / 20))) +
          Real.exp (-(c * σ * (hankelEdgeM (3 * τ0 / 2) - hankelEdgeM τ0) / 2)) *
            √(π / (2 * π ^ 2 * W ^ 2))) := by
  have hc0 : 0 < c := by linarith
  have hpi := Real.pi_pos
  set b : ℝ := 2 * π ^ 2 * W ^ 2 with hb
  have hb0 : 0 < b := by positivity
  set a : ℝ := c * σ / (2 * π) with ha
  have ha0 : 0 < a := by positivity
  have haH : a ≤ c / (8 * π) := by
    rw [ha, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_pos hc0 hpi).le (by linarith : (0 : ℝ) ≤ 1 - 4 * σ)]
  set ν' : ℝ := k * (c * τ0) / (2 * π) with hν'
  set K : ℝ := 3 * hankelMass c f with hK
  have hK0 : 0 ≤ K := by have := hankelMass_nonneg hc0 f; rw [hK]; positivity
  set Δ : ℝ := hankelEdgeM (3 * τ0 / 2) - hankelEdgeM τ0 with hΔ
  have hΔ0 : 0 ≤ Δ := by
    have := hankelEdgeM_strictMonoOn.monotoneOn (Set.mem_Ici.2 hτ0.le)
      (Set.mem_Ici.2 (by linarith : (0 : ℝ) ≤ 3 * τ0 / 2)) (by linarith : τ0 ≤ 3 * τ0 / 2)
    rw [hΔ]; linarith
  set Q : ℝ := W ^ 2 * c ^ 2 * σ ^ 2 / 2 + c * σ * L0 + c * π ^ 2 * σ ^ 3 / 20 with hQ
  set CB : ℝ := Real.exp (-(W ^ 2 * c ^ 2 * (k - 3 / 2) ^ 2 * τ0 ^ 2 / 2 - Q)) with hCB
  set CA : ℝ := Real.exp (-(c * σ * Δ / 2)) with hCA
  set r : ℝ := 3 * c * τ0 / (4 * π) with hr
  have hr0 : 0 < r := by positivity
  -- the Fourier coefficient as a `2π`-convention integral
  have hh := integrable_hankelHL hc0 hf
  have hfh : fhat (fun L => gaussK W (L - L0) * hankelHL c f L) (k * (c * τ0)) =
      ∫ x : ℝ, (gaussK W (x - L0) : ℂ) * (hankelHL c f x : ℂ) *
        Complex.exp (-(2 * π * Complex.I * ν' * x)) := by
    unfold fhat
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    have hpi' : (π : ℂ) ≠ 0 := by exact_mod_cast hpi.ne'
    have : (2 * π * Complex.I * (ν' : ℂ) * x) = Complex.I * ((k * (c * τ0) : ℝ) : ℂ) * x := by
      rw [hν']; push_cast; field_simp
    beta_reduce
    rw [this]; push_cast; ring
  rw [hfh]
  set M : ℝ := K * Real.exp (c * (π ^ 2 / 1280)) with hM
  have hbd : ∀ z : ℂ, 0 ≤ z.im → z.im ≤ a → ‖hankelHcoord c f z‖ ≤ M := fun z h0 h1 =>
    hankelHcoord_bound hc hf hε h0 (h1.trans haH)
  have hshift := windowCoeff_gauss_shift_bound hh hW L0 ν' a ha0
    (fun x => (fh_hankelHL_eq hc0.ne' f x).symm) (hankelHcoord_continuousOn hc hf haH)
    (hankelHcoord_differentiableOn hc hf haH) hbd
  refine hshift.trans ?_
  -- majorant
  set G : ℝ → ℝ := fun ω => K * (Set.indicator (Ioo (ν' - r) (ν' + r)) (fun _ => CB) ω +
      CA * Real.exp (-b * ω ^ 2)) with hG
  have hGi : Integrable G := by
    have i1 : Integrable (Set.indicator (Ioo (ν' - r) (ν' + r)) (fun _ : ℝ => CB)) :=
      (integrable_indicator_iff measurableSet_Ioo).2 (by
        simpa using (integrableOn_const (μ := volume) (s := Ioo (ν' - r) (ν' + r)) (C := CB)
          (by simp) ).2 (Or.inr (by simp)))
    exact (i1.add ((integrable_exp_neg_mul_sq hb0).const_mul CA)).const_mul K
  have hmono : ∀ ω : ℝ, Real.exp (-b * (ω ^ 2 - a ^ 2) + 2 * π * a * L0) *
      ‖hankelHcoord c f (((ω : ℂ) + a * Complex.I) - ν')‖ ≤ G ω := by
    intro ω
    set τ : ℝ := -(2 * π * (ω - ν') / c) with hτ
    have hσe : 2 * π * a / c = σ := by rw [ha]; field_simp
    have hshape := hankelHcoord_shift_eq hc0 f ω ν' a
    rw [hσe] at hshape
    rw [hshape]
    have hbound := hankelHhat_bound hc hf hε hσ0.le hσ4 τ
    have hωτ : ω = ν' - c * τ / (2 * π) := by rw [hτ]; field_simp <;> ring
    have hba : b * a ^ 2 = W ^ 2 * c ^ 2 * σ ^ 2 / 2 := by rw [hb, ha]; field_simp <;> ring
    have hbω : b * ω ^ 2 = W ^ 2 * c ^ 2 * (k * τ0 - τ) ^ 2 / 2 := by
      rw [hb, hωτ, hν']; field_simp <;> ring
    have h2πa : 2 * π * a * L0 = c * σ * L0 := by rw [ha]; field_simp
    have hexp_nn := Real.exp_pos (-b * (ω ^ 2 - a ^ 2) + 2 * π * a * L0)
    have hmain : Real.exp (-b * (ω ^ 2 - a ^ 2) + 2 * π * a * L0) *
        ‖hankelHhat c f ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
        K * Real.exp (-b * (ω ^ 2 - a ^ 2) + 2 * π * a * L0 +
          c * (stripS0Tilde ((σ : ℂ) + (τ : ℂ) * Complex.I)).re) := by
      calc _ ≤ Real.exp (-b * (ω ^ 2 - a ^ 2) + 2 * π * a * L0) *
            (3 * hankelMass c f * Real.exp (c * (stripS0Tilde ((σ : ℂ) + (τ : ℂ) * Complex.I)).re)) :=
            mul_le_mul_of_nonneg_left hbound hexp_nn.le
        _ = K * Real.exp (-b * (ω ^ 2 - a ^ 2) + 2 * π * a * L0 +
              c * (stripS0Tilde ((σ : ℂ) + (τ : ℂ) * Complex.I)).re) := by
            rw [hK]; simp only [Real.exp_add]; ring
    refine hmain.trans ?_
    simp only [hG]
    by_cases hreg : |τ| < 3 * τ0 / 2
    · -- Region B
      have hmem : ω ∈ Ioo (ν' - r) (ν' + r) := by
        have : |ω - ν'| < r := by
          rw [hωτ, show ν' - c * τ / (2 * π) - ν' = -(c / (2 * π)) * τ by ring, abs_mul, abs_neg,
            abs_of_pos (by positivity : 0 < c / (2 * π)), hr]
          calc c / (2 * π) * |τ| < c / (2 * π) * (3 * τ0 / 2) :=
                mul_lt_mul_of_pos_left hreg (by positivity)
            _ = 3 * c * τ0 / (4 * π) := by field_simp; ring
        rw [abs_lt] at this
        exact ⟨by linarith [this.1], by linarith [this.2]⟩
      rw [Set.indicator_of_mem hmem]
      have hS := re_stripS0Tilde_le_cubic hσ0.le hσ4 τ
      have hτb : τ < 3 * τ0 / 2 := (abs_lt.1 hreg).2
      have hkb : (k - 3 / 2) * τ0 ≤ k * τ0 - τ := by linarith
      have hkb0 : 0 ≤ (k - 3 / 2) * τ0 := mul_nonneg (by linarith) hτ0.le
      have hsq : ((k - 3 / 2) * τ0) ^ 2 ≤ (k * τ0 - τ) ^ 2 := pow_le_pow_left₀ hkb0 hkb 2
      have hexp : -b * (ω ^ 2 - a ^ 2) + 2 * π * a * L0 +
          c * (stripS0Tilde ((σ : ℂ) + (τ : ℂ) * Complex.I)).re ≤
          -(W ^ 2 * c ^ 2 * (k - 3 / 2) ^ 2 * τ0 ^ 2 / 2 - Q) := by
        have h1 : c * (stripS0Tilde ((σ : ℂ) + (τ : ℂ) * Complex.I)).re ≤ c * (π ^ 2 * σ ^ 3 / 20) :=
          mul_le_mul_of_nonneg_left hS hc0.le
        have h3 : W ^ 2 * c ^ 2 * ((k - 3 / 2) * τ0) ^ 2 ≤ W ^ 2 * c ^ 2 * (k * τ0 - τ) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
        have e1 : -b * (ω ^ 2 - a ^ 2) = -(b * ω ^ 2) + b * a ^ 2 := by ring
        rw [e1, hba, hbω, h2πa, hQ]
        linarith [h1, h3]
      have : Real.exp (-b * (ω ^ 2 - a ^ 2) + 2 * π * a * L0 +
          c * (stripS0Tilde ((σ : ℂ) + (τ : ℂ) * Complex.I)).re) ≤ CB := Real.exp_le_exp.2 hexp
      have hgn : 0 ≤ CA * Real.exp (-b * ω ^ 2) := by positivity
      exact mul_le_mul_of_nonneg_left (by linarith) hK0
    · -- Region A
      have hreg' : 3 * τ0 / 2 ≤ |τ| := not_lt.1 hreg
      have hS := S0_ineq hτ0 hσ0 hσ hσ4 hreg'
      have hmono' : hankelEdgeM (3 * τ0 / 2) ≤ hankelEdgeM |τ| :=
        hankelEdgeM_strictMonoOn.monotoneOn (Set.mem_Ici.2 (by linarith)) (Set.mem_Ici.2 (abs_nonneg _)) hreg'
      have hΔle : Δ ≤ hankelEdgeM |τ| - hankelEdgeM τ0 := by rw [hΔ]; linarith
      have hcs : c * (stripS0Tilde ((σ : ℂ) + (τ : ℂ) * Complex.I)).re ≤
          -(c * σ * L0) - (4 / 5) * (c * σ * Δ) := by
        have h1 : (4 / 5) * σ * Δ ≤ (4 / 5) * σ * (hankelEdgeM |τ| - hankelEdgeM τ0) := by
          have := mul_le_mul_of_nonneg_left hΔle (by positivity : 0 ≤ (4 / 5) * σ)
          linarith
        have h2 : (stripS0Tilde ((σ : ℂ) + (τ : ℂ) * Complex.I)).re ≤ -σ * L0 - (4 / 5) * σ * Δ := by
          rw [hL] at hS h1; linarith [h1, hS]
        have := mul_le_mul_of_nonneg_left h2 hc0.le
        linarith [this]
      have hexp : -b * (ω ^ 2 - a ^ 2) + 2 * π * a * L0 +
          c * (stripS0Tilde ((σ : ℂ) + (τ : ℂ) * Complex.I)).re ≤ -(c * σ * Δ / 2) + -b * ω ^ 2 := by
        have e1 : -b * (ω ^ 2 - a ^ 2) = -(b * ω ^ 2) + b * a ^ 2 := by ring
        rw [e1, hba, h2πa]
        have hcσΔ : 0 ≤ c * σ * Δ := by positivity
        linarith [hcs, hA, hcσΔ]
      have h4 : Real.exp (-b * (ω ^ 2 - a ^ 2) + 2 * π * a * L0 +
          c * (stripS0Tilde ((σ : ℂ) + (τ : ℂ) * Complex.I)).re) ≤ CA * Real.exp (-b * ω ^ 2) := by
        rw [hCA, ← Real.exp_add]; exact Real.exp_le_exp.2 hexp
      have hi : 0 ≤ Set.indicator (Ioo (ν' - r) (ν' + r)) (fun _ : ℝ => CB) ω :=
        Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _
      exact mul_le_mul_of_nonneg_left (by linarith) hK0
  have hnn : ∀ ω : ℝ, 0 ≤ Real.exp (-b * (ω ^ 2 - a ^ 2) + 2 * π * a * L0) *
      ‖hankelHcoord c f (((ω : ℂ) + a * Complex.I) - ν')‖ := fun ω => by positivity
  have hmono2 := integral_mono_of_nonneg (ae_of_all _ hnn) hGi (ae_of_all _ hmono)
  refine hmono2.trans (le_of_eq ?_)
  -- evaluate `∫ G`
  simp only [hG]
  rw [integral_const_mul, integral_add, integral_const_mul]
  · have i1 : ∫ ω : ℝ, Set.indicator (Ioo (ν' - r) (ν' + r)) (fun _ : ℝ => CB) ω = 2 * r * CB := by
      rw [integral_indicator measurableSet_Ioo]
      simp only [setIntegral_const, Real.volume_real_Ioo, smul_eq_mul]
      rw [max_eq_left (by linarith)]
      ring
    rw [i1, integral_gaussian]
    have : 2 * r = 3 * c * τ0 / (2 * π) := by rw [hr]; field_simp; ring
    rw [this, hK]
  · exact (integrable_indicator_iff measurableSet_Ioo).2 (by
      simpa using (integrableOn_const (μ := volume) (s := Ioo (ν' - r) (ν' + r)) (C := CB)
        (by simp)).2 (Or.inr (by simp)))
  · exact (integrable_exp_neg_mul_sq hb0).const_mul CA

/-- The windowed Hankel density `g(L) = G_W(L - L₀) h(L)` is integrable. -/
theorem integrable_hankel_window {c ε : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) {W : ℝ}
    (hW : 0 < W) (L0 : ℝ) : Integrable (fun L => hankelHL c f L * gaussK W (L - L0)) := by
  refine int_mul_cont (integrable_hankelHL hc hf) (w := fun L => gaussK W (L - L0)) (C := 1 / (√(2 * π) * W)) ?_ ?_
  · unfold gaussK; fun_prop
  · intro x
    unfold gaussK
    have hp : 0 < √(2 * π) * W := by positivity
    rw [abs_of_nonneg (by positivity)]
    apply div_le_div_of_nonneg_right _ hp.le
    have h0 : 0 ≤ (1 / (2 * W ^ 2)) * (x - L0) ^ 2 := by positivity
    exact (Real.exp_le_one_iff.2 (by linarith)).trans_eq (by norm_num)

/-- **`ct:boas` Step 4 + Fejér** (abstract assembly of `ct:P-lb`): for the Gaussian-windowed Hankel density
`g = G_W(· - L₀) h`, every `n ≥ 2` and phase `φ`,
`∫ g (1 + 2cos(cτ₀ L + φ)) ≥ -n ∫ g₋ - (2/n) ∫|g| - 2 n ε`, where `ε` is the (`k = 2`) Region A/B bound of
`hankel_gauss_coeff_bound`, valid uniformly for `k ≥ 2`. -/
theorem hankel_window_fejer {c ε : ℝ} (hc : 3 / 2 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) {W : ℝ} (hW : 0 < W) {τ0 σ L0 : ℝ} (hτ0 : 0 < τ0) (hσ0 : 0 < σ)
    (hσ : σ ≤ τ0 / 4) (hσ4 : σ ≤ 1 / 4) (hL : hankelEdgeM τ0 = L0)
    (hA : W ^ 2 * c ^ 2 * σ ^ 2 / 2 ≤ c * σ * (hankelEdgeM (3 * τ0 / 2) - hankelEdgeM τ0) / 8)
    {n : ℕ} (hn : 2 ≤ n) (φ : ℝ) :
    -((n : ℝ) * ∫ x, max (-(gaussK W (x - L0) * hankelHL c f x)) 0) -
        (2 / n) * (∫ x, |gaussK W (x - L0) * hankelHL c f x|) -
        2 * n * (3 * hankelMass c f *
          ((3 * c * τ0 / (2 * π)) *
              Real.exp (-(W ^ 2 * c ^ 2 * τ0 ^ 2 / 8 -
                (W ^ 2 * c ^ 2 * σ ^ 2 / 2 + c * σ * L0 + c * π ^ 2 * σ ^ 3 / 20))) +
            Real.exp (-(c * σ * (hankelEdgeM (3 * τ0 / 2) - hankelEdgeM τ0) / 2)) *
              √(π / (2 * π ^ 2 * W ^ 2)))) ≤
      ∫ x, gaussK W (x - L0) * hankelHL c f x * (1 + 2 * Real.cos (c * τ0 * x + φ)) := by
  have hc0 : 0 < c := by linarith
  have hg : Integrable (fun L => gaussK W (L - L0) * hankelHL c f L) := by
    refine (integrable_hankel_window hc0 hf hW L0).congr (ae_of_all _ fun L => ?_)
    simp only [mul_comm]
  have hF := ct_fejer hg hn (c * τ0) φ
  refine le_trans ?_ hF
  have hpi := Real.pi_pos
  set E : ℝ := 3 * hankelMass c f *
          ((3 * c * τ0 / (2 * π)) *
              Real.exp (-(W ^ 2 * c ^ 2 * τ0 ^ 2 / 8 -
                (W ^ 2 * c ^ 2 * σ ^ 2 / 2 + c * σ * L0 + c * π ^ 2 * σ ^ 3 / 20))) +
            Real.exp (-(c * σ * (hankelEdgeM (3 * τ0 / 2) - hankelEdgeM τ0) / 2)) *
              √(π / (2 * π ^ 2 * W ^ 2))) with hE
  have hk : ∀ k ∈ Finset.Ico 2 n, ‖fhat (fun L => gaussK W (L - L0) * hankelHL c f L) ((k : ℝ) * (c * τ0))‖ ≤ E := by
    intro k hk
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Ico.1 hk).1
    refine (hankel_gauss_coeff_bound hc hf hε hW hτ0 hσ0 hσ hσ4 hL hk2 hA).trans ?_
    rw [hE]
    have hm := hankelMass_nonneg hc0 f
    refine mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_)
      (by positivity)) le_rfl) (by positivity)
    have : (1 : ℝ) / 4 ≤ ((k : ℝ) - 3 / 2) ^ 2 := by nlinarith
    have h2 : W ^ 2 * c ^ 2 * τ0 ^ 2 / 8 ≤ W ^ 2 * c ^ 2 * ((k : ℝ) - 3 / 2) ^ 2 * τ0 ^ 2 / 2 := by
      have := mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ W ^ 2 * c ^ 2 * τ0 ^ 2)
      nlinarith
    linarith
  have hE0 : 0 ≤ E := by
    rw [hE]; have := hankelMass_nonneg hc0 f; positivity
  have hsum : ∑ k ∈ Finset.Ico 2 n, ‖fhat (fun L => gaussK W (L - L0) * hankelHL c f L) ((k : ℝ) * (c * τ0))‖ ≤
      n * E := by
    refine (Finset.sum_le_card_nsmul _ _ _ hk).trans ?_
    rw [nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ hE0
    simp
  linarith [hsum]

/-- info: 'FormalResearch.SignUncertainty.hankel_gauss_coeff_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel_gauss_coeff_bound

/-- info: 'FormalResearch.SignUncertainty.hankel_window_fejer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel_window_fejer

end FormalResearch.SignUncertainty
