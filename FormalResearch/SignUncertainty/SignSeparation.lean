module

public import FormalResearch.SignUncertainty.HardyMellinIntertwiner

/-!
# Active Origin Constraint and Sign Separation (`general_theorems.tex` Prop 7.9b, Thm 7.9c)

Source: `CFT/sign_uncertainty/paper/general_theorems.tex` (PR 240, commit `c3d8c90fe`).

* **Proposition 7.9b (`gt:7.9b`):** Explicit odd Laguerre mode `oddLaguerreMode`,
  `active_origin_constraint`, and constrained/unconstrained infimum equality for `T_c^{-1} > c / (4π)`.
* **Theorem 7.9c (`gt:7.9c`):** `integral_linear_exp_tail_lower`, the `C¹` profile-convergence
  reduction (`SignSeparationPackage.langer_approx`, derived from `c1_profile`; no Langer chart),
  `sign_separation_limsup` (`limsup (T_c^{+1} - T_c^{-1}) ≤ -2 / π²`), integer
  `A_+(d) - A_-(d)` and `κ_{+1} - κ_{-1}` corollaries, plus `langerProfileFamily_nonvacuous`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real ENNReal Polynomial

namespace FormalResearch.SignUncertainty

open FormalResearch.Special
open FormalResearch.Analysis

/-! ### Section 4: Active Origin Constraint (`gt:7.9b`, Proposition 7.9b) -/

/-- Explicit odd Laguerre mode `u₀(Δ) = (4πΔ / c - 1) exp(-2πΔ)`, satisfying `u₀(0) = -1` and
`u₀(Δ) > 0` for `Δ > c / (4π)`. -/
noncomputable def oddLaguerreMode (c Δ : ℝ) : ℝ :=
  (4 * π * Δ / c - 1) * Real.exp (-2 * π * Δ)

@[simp]
theorem oddLaguerreMode_zero (c : ℝ) : oddLaguerreMode c 0 = -1 := by
  simp [oddLaguerreMode]

theorem oddLaguerreMode_continuous (c : ℝ) : Continuous (oddLaguerreMode c) := by
  unfold oddLaguerreMode; fun_prop

theorem oddLaguerreMode_pos {c Δ : ℝ} (hc : 0 < c) (hΔ : c / (4 * π) < Δ) :
    0 < oddLaguerreMode c Δ := by
  unfold oddLaguerreMode
  have hlt : 1 < 4 * π * Δ / c := by
    rw [one_lt_div hc]
    exact (div_lt_iff₀' (by positivity : 0 < 4 * π)).mp hΔ
  exact mul_pos (sub_pos.mpr hlt) (Real.exp_pos _)

theorem oddLaguerreMode_nonneg {c Δ : ℝ} (hc : 0 < c) (hΔ : c / (4 * π) ≤ Δ) :
    0 ≤ oddLaguerreMode c Δ := by
  unfold oddLaguerreMode
  have hle : 1 ≤ 4 * π * Δ / c := by
    rw [one_le_div hc]
    exact (div_le_iff₀' (by positivity : 0 < 4 * π)).mp hΔ
  exact mul_nonneg (sub_nonneg.mpr hle) (Real.exp_pos _).le

theorem oddLaguerreMode_neg {c Δ : ℝ} (hc : 0 < c) (hΔ : Δ < c / (4 * π)) :
    oddLaguerreMode c Δ < 0 := by
  unfold oddLaguerreMode
  have hlt : 4 * π * Δ / c < 1 := by
    rw [div_lt_one hc]
    exact (lt_div_iff₀' (by positivity : 0 < 4 * π)).mp hΔ
  exact mul_neg_of_neg_of_pos (sub_neg.mpr hlt) (Real.exp_pos _)

private lemma isRadialEigenfn_add {c : ℝ} {K : HankelKernelData c} {ε : ℝ} {f g : ℝ → ℝ}
    (hf : IsRadialEigenfn c K ε f) (hg : IsRadialEigenfn c K ε g) :
    IsRadialEigenfn c K ε (fun Δ => f Δ + g Δ) := by
  refine ⟨hf.cont.add hg.cont, ?_, fun Δ hΔ => ?_⟩
  · exact (hf.int.add hg.int).congr_fun (fun s _ => by dsimp; ring) measurableSet_Ioi
  · have hIf := hankelTransform_integrand_integrableOn (K := K) hf.int hΔ
    have hIg := hankelTransform_integrand_integrableOn (K := K) hg.int hΔ
    unfold hankelTransform
    calc ∫ s in Ioi (0 : ℝ), (f s + g s) * hankelRho0 c s * K.φ (Δ * s)
        = ∫ s in Ioi (0 : ℝ),
            (f s * hankelRho0 c s * K.φ (Δ * s) + g s * hankelRho0 c s * K.φ (Δ * s)) := by
          refine setIntegral_congr_fun measurableSet_Ioi fun s _ => by ring
      _ = (∫ s in Ioi (0 : ℝ), f s * hankelRho0 c s * K.φ (Δ * s)) +
            ∫ s in Ioi (0 : ℝ), g s * hankelRho0 c s * K.φ (Δ * s) := integral_add hIf hIg
      _ = ε * f Δ + ε * g Δ := by
          have ef := hf.eigen Δ hΔ
          have eg := hg.eigen Δ hΔ
          unfold hankelTransform at ef eg
          rw [ef, eg]
      _ = ε * (f Δ + g Δ) := by ring

private lemma isRadialEigenfn_const_mul {c : ℝ} {K : HankelKernelData c} {ε : ℝ} {f : ℝ → ℝ}
    (a : ℝ) (hf : IsRadialEigenfn c K ε f) :
    IsRadialEigenfn c K ε (fun Δ => a * f Δ) := by
  refine ⟨continuousOn_const.mul hf.cont, ?_, fun Δ hΔ => ?_⟩
  · have hm : IntegrableOn (fun s => a * (f s * hankelRho0 c s)) (Ioi 0) := hf.int.const_mul a
    exact hm.congr_fun (fun s _ => by dsimp; ring) measurableSet_Ioi
  · unfold hankelTransform
    calc ∫ s in Ioi (0 : ℝ), (a * f s) * hankelRho0 c s * K.φ (Δ * s)
        = ∫ s in Ioi (0 : ℝ), a * (f s * hankelRho0 c s * K.φ (Δ * s)) := by
          refine setIntegral_congr_fun measurableSet_Ioi fun s _ => by ring
      _ = a * ∫ s in Ioi (0 : ℝ), f s * hankelRho0 c s * K.φ (Δ * s) := integral_const_mul _ _
      _ = a * (ε * f Δ) := by
          have ef := hf.eigen Δ hΔ
          unfold hankelTransform at ef
          rw [ef]
      _ = ε * (a * f Δ) := by ring

theorem oddLaguerreMode_integrable {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun s => oddLaguerreMode c s * hankelRho0 c s) (Ioi 0) := by
  let C₀ : ℝ := (2 * π) ^ c / Real.Gamma c
  let C₁ : ℝ := (4 * π / c) * C₀
  have h1 : IntegrableOn (fun s : ℝ => C₁ * (s ^ c * Real.exp (-(2 * π) * s))) (Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_Ioi (by linarith : (-1 : ℝ) < c) (by positivity : 0 < 2 * π)).const_mul C₁
  have h2 : IntegrableOn (fun s : ℝ => C₀ * (s ^ (c - 1) * Real.exp (-(2 * π) * s))) (Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_Ioi (by linarith : (-1 : ℝ) < c - 1) (by positivity : 0 < 2 * π)).const_mul C₀
  refine (h1.sub h2).congr_fun (fun s (hs : 0 < s) => ?_) measurableSet_Ioi
  dsimp only [Pi.sub_apply]
  unfold oddLaguerreMode hankelRho0
  have hs_pow : s * s ^ (c - 1) = s ^ c := by
    calc s * s ^ (c - 1) = s ^ (1 : ℝ) * s ^ (c - 1) := by rw [Real.rpow_one]
      _ = s ^ (1 + (c - 1)) := (Real.rpow_add hs 1 (c - 1)).symm
      _ = s ^ c := by congr 1; ring
  have hsp : s ^ (c - 1) * s = s ^ c := by rw [mul_comm, hs_pow]
  dsimp [C₀, C₁]
  calc (4 * π / c * ((2 * π) ^ c / Real.Gamma c)) * (s ^ c * Real.exp (-(2 * π) * s)) -
        ((2 * π) ^ c / Real.Gamma c) * (s ^ (c - 1) * Real.exp (-(2 * π) * s))
      = (4 * π / c) * ((2 * π) ^ c / Real.Gamma c) * (s * s ^ (c - 1)) * Real.exp (-2 * π * s) -
          ((2 * π) ^ c / Real.Gamma c) * s ^ (c - 1) * Real.exp (-2 * π * s) := by
        rw [hs_pow]; ring
    _ = (4 * π * s / c - 1) * Real.exp (-2 * π * s) * ((2 * π) ^ c / Real.Gamma c * s ^ (c - 1)) := by ring

/-- Unconditional verification of the `Δ = 0` Hankel eigenvalue `-1` identity for `oddLaguerreMode c`:
`∫_0^∞ oddLaguerreMode c s * ρ₀(c, s) ds = 1 = -oddLaguerreMode c 0`. -/
theorem oddLaguerreMode_integral {c : ℝ} (hc : 0 < c) :
    ∫ s in Ioi (0 : ℝ), oddLaguerreMode c s * hankelRho0 c s = 1 := by
  let C₀ : ℝ := (2 * π) ^ c / Real.Gamma c
  let C₁ : ℝ := (4 * π / c) * C₀
  have h1_base : IntegrableOn (fun s : ℝ => s ^ c * Real.exp (-(2 * π) * s)) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_Ioi (by linarith : (-1 : ℝ) < c) (by positivity : 0 < 2 * π)
  have h2_base : IntegrableOn (fun s : ℝ => s ^ (c - 1) * Real.exp (-(2 * π) * s)) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_Ioi (by linarith : (-1 : ℝ) < c - 1) (by positivity : 0 < 2 * π)
  have h1 : IntegrableOn (fun s : ℝ => C₁ * (s ^ c * Real.exp (-(2 * π) * s))) (Ioi 0) :=
    h1_base.const_mul C₁
  have h2 : IntegrableOn (fun s : ℝ => C₀ * (s ^ (c - 1) * Real.exp (-(2 * π) * s))) (Ioi 0) :=
    h2_base.const_mul C₀
  have hsplit : ∫ s in Ioi (0 : ℝ), oddLaguerreMode c s * hankelRho0 c s =
      C₁ * (∫ s in Ioi (0 : ℝ), s ^ ((c + 1) - 1) * Real.exp (-(2 * π * s))) -
        C₀ * ∫ s in Ioi (0 : ℝ), s ^ (c - 1) * Real.exp (-(2 * π * s)) := by
    have hcongr1 : ∫ s in Ioi (0 : ℝ), oddLaguerreMode c s * hankelRho0 c s =
        ∫ s in Ioi (0 : ℝ), (C₁ * (s ^ c * Real.exp (-(2 * π) * s)) -
          C₀ * (s ^ (c - 1) * Real.exp (-(2 * π) * s))) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun s (hs : 0 < s) => ?_
      unfold oddLaguerreMode hankelRho0
      have hs_pow : s * s ^ (c - 1) = s ^ c := by
        calc s * s ^ (c - 1) = s ^ (1 : ℝ) * s ^ (c - 1) := by rw [Real.rpow_one]
          _ = s ^ (1 + (c - 1)) := (Real.rpow_add hs 1 (c - 1)).symm
          _ = s ^ c := by congr 1; ring
      dsimp [C₀, C₁]
      calc (4 * π * s / c - 1) * Real.exp (-2 * π * s) * ((2 * π) ^ c / Real.Gamma c * s ^ (c - 1))
          = (4 * π / c) * ((2 * π) ^ c / Real.Gamma c) * (s * s ^ (c - 1)) * Real.exp (-2 * π * s) -
              ((2 * π) ^ c / Real.Gamma c) * s ^ (c - 1) * Real.exp (-2 * π * s) := by ring
        _ = (4 * π / c * ((2 * π) ^ c / Real.Gamma c)) * (s ^ c * Real.exp (-(2 * π) * s)) -
              ((2 * π) ^ c / Real.Gamma c) * (s ^ (c - 1) * Real.exp (-(2 * π) * s)) := by
            rw [hs_pow]; ring
    rw [hcongr1, integral_sub h1 h2, integral_const_mul, integral_const_mul]
    congr 2
    · refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
      rw [show (c + 1) - 1 = c by ring, neg_mul]
    · refine setIntegral_congr_fun measurableSet_Ioi fun s _ => by rw [neg_mul]
  rw [hsplit, Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith : 0 < c + 1) (by positivity : 0 < 2 * π),
    Real.integral_rpow_mul_exp_neg_mul_Ioi hc (by positivity : 0 < 2 * π)]
  have hGc1 : Real.Gamma (c + 1) = c * Real.Gamma c := Real.Gamma_add_one hc.ne'
  have hpow1 : (1 / (2 * π)) ^ (c + 1) = (1 / (2 * π)) ^ c * (1 / (2 * π)) := by
    rw [Real.rpow_add (by positivity : (0 : ℝ) < 1 / (2 * π)), Real.rpow_one]
  have hinv : (2 * π) ^ c * (1 / (2 * π)) ^ c = 1 := by
    rw [← Real.mul_rpow (by positivity) (by positivity), mul_one_div_cancel (by positivity), Real.one_rpow]
  rw [hGc1, hpow1]
  dsimp [C₀, C₁]
  have hGc_ne : Real.Gamma c ≠ 0 := (Real.Gamma_pos_of_pos hc).ne'
  calc (4 * π / c * ((2 * π) ^ c / Real.Gamma c)) * (((1 / (2 * π)) ^ c * (1 / (2 * π))) * (c * Real.Gamma c)) -
        ((2 * π) ^ c / Real.Gamma c) * ((1 / (2 * π)) ^ c * Real.Gamma c)
      = 2 * ((2 * π) ^ c * (1 / (2 * π)) ^ c) * (Real.Gamma c / Real.Gamma c) * (c / c) * (π / π) -
          ((2 * π) ^ c * (1 / (2 * π)) ^ c) * (Real.Gamma c / Real.Gamma c) := by
        ring
    _ = 2 * 1 * 1 * 1 * 1 - 1 * 1 := by
        rw [hinv, div_self hGc_ne, div_self hc.ne', div_self Real.pi_pos.ne']
    _ = 1 := by norm_num

/-- Proposition 7.9b: Adding `f(0) * oddLaguerreMode c` to a `(-1)`-feasible eigenfunction at
`T > c / (4π)` produces a `(-1)`-feasible eigenfunction `f₀` with `f₀(0) = 0` and `f₀ ≥ f` on
`[c / (4π), ∞)`. -/
theorem active_origin_constraint {c T : ℝ} (hc : 0 < c) {K : HankelKernelData c} {f : ℝ → ℝ}
    (hf : IsFeasible c K (-1) T f)
    (hu₀ : IsRadialEigenfn c K (-1) (oddLaguerreMode c))
    (hT : c / (4 * π) < T) :
    let f₀ : ℝ → ℝ := fun Δ => f Δ + f 0 * oddLaguerreMode c Δ
    IsRadialEigenfn c K (-1) f₀ ∧
      f₀ 0 = 0 ∧
      (∀ Δ ≥ c / (4 * π), f Δ ≤ f₀ Δ) ∧
      IsFeasible c K (-1) T f₀ := by
  intro f₀
  have hf0_nn : 0 ≤ f 0 := by linarith [hf.origin_sign]
  have heig : IsRadialEigenfn c K (-1) f₀ :=
    isRadialEigenfn_add hf.eigenfn (isRadialEigenfn_const_mul (f 0) hu₀)
  have hzero : f₀ 0 = 0 := by
    dsimp [f₀]; rw [oddLaguerreMode_zero]; ring
  have hdom : ∀ Δ ≥ c / (4 * π), f Δ ≤ f₀ Δ := fun Δ hΔ => by
    dsimp [f₀]
    have hu_nn : 0 ≤ oddLaguerreMode c Δ := oddLaguerreMode_nonneg hc hΔ
    linarith [mul_nonneg hf0_nn hu_nn]
  have hnz : ∃ Δ ∈ Ici (0 : ℝ), f₀ Δ ≠ 0 := by
    rcases eq_or_lt_of_le hf0_nn with hf00 | hf0pos
    · obtain ⟨Δ, hΔ, hne⟩ := hf.nonzero
      refine ⟨Δ, hΔ, ?_⟩
      dsimp [f₀]; rw [← hf00, zero_mul, add_zero]; exact hne
    · have hT0 : 0 ≤ T := by
        have : 0 < c / (4 * π) := by positivity
        linarith
      have hT_pos : 0 < oddLaguerreMode c T := oddLaguerreMode_pos hc hT
      have hmul_pos : 0 < f 0 * oddLaguerreMode c T := mul_pos hf0pos hT_pos
      have hfT_nn : 0 ≤ f T := hf.tail_nonneg T le_rfl
      refine ⟨T, hT0, ?_⟩
      dsimp [f₀]; linarith
  have htail : ∀ Δ ≥ T, 0 ≤ f₀ Δ := fun Δ hΔ =>
    (hf.tail_nonneg Δ hΔ).trans (hdom Δ (hT.le.trans hΔ))
  have horig : (-1 : ℝ) * f₀ 0 ≤ 0 := by rw [hzero]; norm_num
  exact ⟨heig, hzero, hdom, ⟨heig, hnz, horig, htail⟩⟩

/-- Constrained one-level threshold enforcing vanishing origin `f(0) = 0`. -/
noncomputable def hankelThresholdZeroOrigin (c : ℝ) (K : HankelKernelData c) (ε : ℝ) : ℝ :=
  sInf { T : ℝ | ∃ f, IsFeasible c K ε T f ∧ f 0 = 0 }

/-- Proposition 7.9b, equality of thresholds: whenever `T_c^{-1} > c / (4π)`, the constrained
threshold with `f(0) = 0` equals the unconstrained threshold `T_c^{-1}`. -/
theorem constrained_threshold_eq_unconstrained {c : ℝ} (hc : 0 < c) {K : HankelKernelData c}
    (hu₀ : IsRadialEigenfn c K (-1) (oddLaguerreMode c))
    (hnonempty : ∃ T f, IsFeasible c K (-1) T f)
    (hT : c / (4 * π) < hankelThreshold c K (-1)) :
    hankelThresholdZeroOrigin c K (-1) = hankelThreshold c K (-1) := by
  obtain ⟨T₀, f₀, hf₀⟩ := hnonempty
  have hS_bdd : BddBelow { T : ℝ | ∃ f, IsFeasible c K (-1) T f } :=
    ⟨0, fun T ⟨_, hf⟩ => (feasible_threshold_pos hc hf).le⟩
  have hS0_ne : { T : ℝ | ∃ f, IsFeasible c K (-1) T f ∧ f 0 = 0 }.Nonempty := by
    have hT₀ : c / (4 * π) < T₀ := lt_of_lt_of_le hT (csInf_le hS_bdd ⟨f₀, hf₀⟩)
    obtain ⟨_, h0, _, hfeas⟩ := active_origin_constraint hc hf₀ hu₀ hT₀
    exact ⟨T₀, _, hfeas, h0⟩
  have hle : hankelThreshold c K (-1) ≤ hankelThresholdZeroOrigin c K (-1) :=
    le_csInf hS0_ne fun T ⟨f, hf, _⟩ => csInf_le hS_bdd ⟨f, hf⟩
  have hge : hankelThresholdZeroOrigin c K (-1) ≤ hankelThreshold c K (-1) := by
    refine le_csInf ⟨T₀, f₀, hf₀⟩ fun T ⟨f, hf⟩ => ?_
    have hTc : c / (4 * π) < T := lt_of_lt_of_le hT (csInf_le hS_bdd ⟨f, hf⟩)
    obtain ⟨_, h0, _, hfeas⟩ := active_origin_constraint hc hf hu₀ hTc
    exact csInf_le ⟨0, fun _ ⟨_, hf', _⟩ => (feasible_threshold_pos hc hf').le⟩ ⟨_, hfeas, h0⟩
  exact le_antisymm hge hle

/-! ### Section 5: Separation of Bounded Remainders (`gt:7.9c`, Theorem 7.9c) -/

/-- Exact exponential tail integral: for `b > 0` and any `h : ℝ`,
`∫ y in Ioi (-h), y * exp(-b (y + h)) dy = b^{-2} - h b^{-1}`, which is bounded below by
`ε₀ / b` when `b = π² / 2` and `h ≤ 2 / π² - ε₀`. -/
theorem integral_linear_exp_tail_lower {b : ℝ} (hb : 0 < b) (h : ℝ) :
    IntegrableOn (fun y : ℝ => y * Real.exp (-b * (y + h))) (Ioi (-h)) ∧
      ∫ y in Ioi (-h), y * Real.exp (-b * (y + h)) = 1 / b ^ 2 - h / b := by
  let H : ℝ → ℝ := fun y => -((y + 1 / b) / b) * Real.exp (-b * (y + h))
  have hderiv : ∀ y : ℝ, HasDerivAt H (y * Real.exp (-b * (y + h))) y := fun y => by
    have hp : HasDerivAt (fun x : ℝ => -((x + 1 / b) / b)) (-(1 / b)) y := by
      have := (((hasDerivAt_id' y).add_const (1 / b)).div_const b).neg
      exact this.congr_deriv (by ring)
    have he : HasDerivAt (fun x : ℝ => Real.exp (-b * (x + h)))
        (-b * Real.exp (-b * (y + h))) y := by
      have := ((hasDerivAt_id' y).add_const h).const_mul (-b) |>.exp
      exact this.congr_deriv (by ring)
    exact (hp.mul he).congr_deriv (by field_simp [hb.ne']; ring)
  have hint_Ioi0 : IntegrableOn (fun y : ℝ => |y| * Real.exp (-b * (y + h))) (Ioi 0) := by
    have hdom : IntegrableOn (fun y : ℝ => Real.exp (-b * h) * (y ^ (1 : ℝ) * Real.exp (-b * y))) (Ioi 0) :=
      (integrableOn_rpow_mul_exp_neg_mul_Ioi (by norm_num : (-1 : ℝ) < 1) hb).const_mul (Real.exp (-b * h))
    refine hdom.congr_fun (fun y (hy : 0 < y) => ?_) measurableSet_Ioi
    dsimp only
    rw [abs_of_pos hy, Real.rpow_one, show -b * (y + h) = -b * h + (-b * y) by ring, Real.exp_add]
    ring
  have hint_neg_h : IntegrableOn (fun y : ℝ => y * Real.exp (-b * (y + h))) (Ioi (-h)) := by
    have hsm : AEStronglyMeasurable (fun y : ℝ => y * Real.exp (-b * (y + h))) (volume.restrict (Ioi (-h))) :=
      (by fun_prop : Continuous fun y : ℝ => y * Real.exp (-b * (y + h))).aestronglyMeasurable
    rcases le_or_gt (-h) 0 with hneg | hpos
    · have h1 : IntegrableOn (fun y : ℝ => y * Real.exp (-b * (y + h))) (Ioc (-h) 0) :=
        ((by fun_prop : Continuous fun y : ℝ => y * Real.exp (-b * (y + h))).continuousOn.integrableOn_Icc).mono_set
          Ioc_subset_Icc_self
      have h2 : IntegrableOn (fun y : ℝ => y * Real.exp (-b * (y + h))) (Ioi 0) :=
        hint_Ioi0.mono' (hsm.mono_measure (Measure.restrict_mono (Ioi_subset_Ioi hneg) le_rfl))
          ((ae_restrict_mem measurableSet_Ioi).mono fun y (hy : 0 < y) => by
            rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)])
      rw [← Set.Ioc_union_Ioi_eq_Ioi hneg]
      exact h1.union h2
    · refine (hint_Ioi0.mono_set (Ioi_subset_Ioi hpos.le)).mono' hsm ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y (hy : -h < y)
      have hy0 : 0 < y := hpos.trans hy
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  refine ⟨hint_neg_h, ?_⟩
  have hlim_int : Tendsto (fun R : ℝ => ∫ y in (-h)..R, y * Real.exp (-b * (y + h)))
      atTop (𝓝 (∫ y in Ioi (-h), y * Real.exp (-b * (y + h)))) :=
    intervalIntegral_tendsto_integral_Ioi (-h) hint_neg_h tendsto_id
  have hlim_ftc : Tendsto (fun R : ℝ => ∫ y in (-h)..R, y * Real.exp (-b * (y + h)))
      atTop (𝓝 (1 / b ^ 2 - h / b)) := by
    have hev : (fun R : ℝ => ∫ y in (-h)..R, y * Real.exp (-b * (y + h))) =ᶠ[atTop]
        fun R : ℝ => H R - H (-h) := by
      filter_upwards [eventually_ge_atTop (-h)] with R _
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hderiv y)
        ((by fun_prop : Continuous fun y : ℝ => y * Real.exp (-b * (y + h))).intervalIntegrable (-h) R)
    refine Tendsto.congr' hev.symm ?_
    have hH_lim : Tendsto H atTop (𝓝 0) := by
      refine squeeze_zero_norm' (a := fun y : ℝ => (Real.exp (-b * h) * (2 / b ^ 2 + 1 / b ^ 2)) *
          Real.exp (-(b / 2) * y)) ?_ ?_
      · filter_upwards [eventually_ge_atTop (1 : ℝ)] with y (hy : 1 ≤ y)
        have hby : (b / 2) * y ≤ Real.exp ((b / 2) * y) := by
          linarith [Real.add_one_le_exp ((b / 2) * y)]
        have hy_le : y ≤ (2 / b) * Real.exp ((b / 2) * y) := by
          have : b / 2 * y ≤ Real.exp (b / 2 * y) := hby
          calc y = (2 / b) * ((b / 2) * y) := by field_simp [hb.ne']
            _ ≤ (2 / b) * Real.exp ((b / 2) * y) := mul_le_mul_of_nonneg_left this (by positivity)
        have hexp_eq : Real.exp ((b / 2) * y) * Real.exp (-b * (y + h)) =
            Real.exp (-b * h) * Real.exp (-(b / 2) * y) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
        have h1e : Real.exp (-b * (y + h)) ≤ Real.exp (-b * h) * Real.exp (-(b / 2) * y) := by
          have hre := mul_le_mul_of_nonneg_right
            (Real.one_le_exp (by positivity : 0 ≤ (b / 2) * y))
            (Real.exp_pos (-b * (y + h))).le
          rw [one_mul] at hre
          exact hre.trans_eq hexp_eq
        rw [Real.norm_eq_abs]
        dsimp [H]
        rw [abs_mul, abs_neg, abs_div, abs_of_pos hb, abs_of_pos (by positivity : 0 < y + 1 / b),
          abs_of_pos (Real.exp_pos _)]
        calc (y + 1 / b) / b * Real.exp (-b * (y + h))
            = (y / b) * Real.exp (-b * (y + h)) + (1 / b ^ 2) * Real.exp (-b * (y + h)) := by ring
          _ ≤ ((2 / b ^ 2) * Real.exp ((b / 2) * y)) * Real.exp (-b * (y + h)) +
                (1 / b ^ 2) * (Real.exp (-b * h) * Real.exp (-(b / 2) * y)) := by
              refine add_le_add (mul_le_mul_of_nonneg_right (by
                calc y / b ≤ ((2 / b) * Real.exp ((b / 2) * y)) / b := div_le_div_of_nonneg_right hy_le hb.le
                  _ = (2 / b ^ 2) * Real.exp ((b / 2) * y) := by ring) (Real.exp_pos _).le)
                (mul_le_mul_of_nonneg_left h1e (by positivity))
          _ = (Real.exp (-b * h) * (2 / b ^ 2 + 1 / b ^ 2)) * Real.exp (-(b / 2) * y) := by
              rw [mul_assoc, hexp_eq]; ring
      · have ht : Tendsto (fun y : ℝ => Real.exp (-(b / 2) * y)) atTop (𝓝 0) :=
          Real.tendsto_exp_atBot.comp (tendsto_const_nhds.neg_mul_atTop (neg_lt_zero.mpr (half_pos hb)) tendsto_id)
        have hcm : Tendsto (fun y : ℝ => (Real.exp (-b * h) * (2 / b ^ 2 + 1 / b ^ 2)) *
            Real.exp (-(b / 2) * y)) atTop (𝓝 0) := by
          simpa only [mul_zero] using ht.const_mul (Real.exp (-b * h) * (2 / b ^ 2 + 1 / b ^ 2))
        exact hcm.congr' (Eventually.of_forall fun y => by simp only [neg_mul])
    have hH_val : -H (-h) = 1 / b ^ 2 - h / b := by
      dsimp [H]; simp only [neg_add_cancel, mul_zero, Real.exp_zero, mul_one]; ring
    simpa [sub_eq_add_neg, hH_val] using hH_lim.sub_const (H (-h))
  exact tendsto_nhds_unique hlim_int hlim_ftc

private lemma exp_linear_tail_tendsto {b : ℝ} (hb : 0 < b) :
    Tendsto (fun M : ℝ => ∫ y in Ioi M, y * Real.exp (-b * y)) atTop (𝓝 0) := by
  have hint0 : IntegrableOn (fun y : ℝ => y * Real.exp (-b * y)) (Ioi 0) := by
    have hbase := integrableOn_rpow_mul_exp_neg_mul_Ioi (by norm_num : (-1 : ℝ) < 1) hb
    exact hbase.congr_fun (fun y _ => by dsimp only; rw [Real.rpow_one]) measurableSet_Ioi
  have hzero : ∫ _y in Ioi (0 : ℝ), (0 : ℝ) = 0 := by simp
  rw [← hzero]
  have hev : (fun M : ℝ => ∫ y in Ioi M, y * Real.exp (-b * y)) =ᶠ[atTop]
      fun M : ℝ => ∫ y in Ioi (0 : ℝ), (Ioi M).indicator (fun y : ℝ => y * Real.exp (-b * y)) y := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with M hM
    rw [setIntegral_indicator measurableSet_Ioi, Set.inter_eq_right.mpr (Ioi_subset_Ioi hM)]
  refine Tendsto.congr' hev.symm ?_
  refine tendsto_integral_filter_of_dominated_convergence (fun y => y * Real.exp (-b * y))
    (Eventually.of_forall fun M => hint0.aestronglyMeasurable.indicator measurableSet_Ioi)
    (Eventually.of_forall fun M => (ae_restrict_mem measurableSet_Ioi).mono fun y (hy : 0 < y) => by
      by_cases hm : y ∈ Ioi M
      · simp only [Set.indicator_of_mem hm, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg hy.le (Real.exp_pos _).le), le_refl]
      · simp only [Set.indicator_of_notMem hm, norm_zero]
        exact mul_nonneg hy.le (Real.exp_pos _).le)
    hint0 ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y (hy : 0 < y)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop y] with M hMy
  rw [Set.indicator_of_notMem (fun hm => absurd (mem_Ioi.mp hm) (not_lt_of_ge hMy))]

private lemma log_one_add_sub_abs_le {u : ℝ} (hu : 0 ≤ u) :
    |Real.log (1 + u) - u| ≤ u ^ 2 / 2 := by
  have hup : Real.log (1 + u) ≤ u := by
    linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + u)]
  have hlow : u - u ^ 2 / 2 ≤ Real.log (1 + u) := by
    let g : ℝ → ℝ := fun t => Real.log (1 + t) - (t - t ^ 2 / 2)
    have hderiv : ∀ t ∈ uIcc (0 : ℝ) u, HasDerivAt g (t ^ 2 / (1 + t)) t := fun t ht => by
      rw [Set.uIcc_of_le hu] at ht
      have h1t : 0 < 1 + t := by linarith [ht.1]
      have hd1 : HasDerivAt (fun x : ℝ => Real.log (1 + x)) (1 / (1 + t)) t := by
        have hlin : HasDerivAt (fun x : ℝ => 1 + x) 1 t := (hasDerivAt_id' t).const_add 1
        exact (hlin.log h1t.ne').congr_deriv (by ring)
      have hd2 : HasDerivAt (fun x : ℝ => x - x ^ 2 / 2) (1 - t) t :=
        ((hasDerivAt_id' t).sub ((hasDerivAt_pow 2 t).div_const 2)).congr_deriv
          (by simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]; ring)
      exact (hd1.sub hd2).congr_deriv (by field_simp [h1t.ne']; ring)
    have hint : IntervalIntegrable (fun t : ℝ => t ^ 2 / (1 + t)) volume 0 u := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hu]
      exact (continuousOn_pow 2).div (continuousOn_const.add continuousOn_id) fun x hx => by linarith [hx.1]
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    have hnn : 0 ≤ ∫ t in (0 : ℝ)..u, t ^ 2 / (1 + t) := by
      refine intervalIntegral.integral_nonneg hu fun t ht => div_nonneg (sq_nonneg t) (by linarith [ht.1])
    dsimp [g] at hftc
    simp only [add_zero, Real.log_one, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, zero_div] at hftc
    linarith
  rw [abs_le]
  constructor <;> linarith

private lemma abs_exp_sub_exp_le_of_nonpos {a b : ℝ} (ha : a ≤ 0) (hb : b ≤ 0) :
    |Real.exp a - Real.exp b| ≤ |a - b| := by
  wlog hab : a ≤ b generalizing a b
  · rw [abs_sub_comm (Real.exp a), abs_sub_comm a b]
    exact this hb ha (le_of_not_ge hab)
  have hsub : Real.exp b - Real.exp a ≤ b - a := by
    have hderiv : ∀ t ∈ uIcc a b, HasDerivAt (fun x : ℝ => Real.exp x - x) (Real.exp t - 1) t :=
      fun t _ => (Real.hasDerivAt_exp t).sub (hasDerivAt_id' t)
    have hint : IntervalIntegrable (fun t : ℝ => Real.exp t - 1) volume a b :=
      (by fun_prop : Continuous fun t : ℝ => Real.exp t - 1).intervalIntegrable a b
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    have hnp : ∫ t in a..b, (Real.exp t - 1) ≤ 0 := by
      rw [← intervalIntegral.integral_zero (a := a) (b := b)]
      exact intervalIntegral.integral_mono_on hab hint continuousOn_const.intervalIntegrable
        fun t ht => sub_nonpos.mpr (Real.exp_le_one_iff.mpr (ht.2.trans hb))
    linarith
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr hab)),
    abs_sub_comm a b, abs_of_nonneg (sub_nonneg.mpr hab)]
  exact hsub

/-- Uniform convergence of the Langer weight ratio `((T' + y) / (T' - h))^{-c/2}` to
`exp(-(π²/2)(y + h))` on `y ∈ [-h, M]`, uniformly in `h ∈ [0, δ]` and `T' ∈ [T_c, T_c + 1 / c]`,
assuming only `T_c / c → 1 / π²`. -/
theorem tendsto_rpow_ratio_exp {T : ℝ → ℝ}
    (hT : Tendsto (fun c : ℝ => T c / c) atTop (𝓝 (1 / π ^ 2)))
    {δ M η : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M) (hη : 0 < η) :
    ∀ᶠ c in atTop, ∀ T' ∈ Icc (T c) (T c + 1 / c), ∀ h ∈ Icc (0 : ℝ) δ, ∀ y ∈ Icc (-h) M,
      0 < T' - h ∧ 0 < T' + y ∧
        |((T' + y) / (T' - h)) ^ (-(c / 2)) - Real.exp (-(π ^ 2 / 2) * (y + h))| ≤ η := by
  let M' : ℝ := δ + M
  let b : ℝ := π ^ 2 / 2
  have hpi2 : 0 < π ^ 2 := sq_pos_of_pos Real.pi_pos
  have h1pi2 : (0 : ℝ) < 1 / (2 * π ^ 2) := by positivity
  let ε₁ : ℝ := min (1 / (4 * π ^ 2)) (η / (2 * π ^ 4 * (M' + 1)))
  have hε₁ : 0 < ε₁ := by positivity
  have hT_close : ∀ᶠ c in atTop, |T c / c - 1 / π ^ 2| < ε₁ / 2 := by
    have := hT.eventually (Metric.ball_mem_nhds (1 / π ^ 2) (half_pos hε₁))
    refine this.mono fun c hc => by rwa [Real.dist_eq] at hc
  have hδ_c : ∀ᶠ c in atTop, (δ + 1) / c < ε₁ / 2 := by
    have ht : Tendsto (fun c : ℝ => (δ + 1) / c) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    exact (ht.eventually (Metric.ball_mem_nhds 0 (half_pos hε₁))).mono fun c hc => by
      rw [Real.dist_eq, sub_zero] at hc
      exact (le_abs_self _).trans_lt hc
  have hquad_c : ∀ᶠ c in atTop, 2 * π ^ 4 * M' ^ 2 / c ≤ η / 2 := by
    have ht : Tendsto (fun c : ℝ => 2 * π ^ 4 * M' ^ 2 / c) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    exact ht.eventually (eventually_le_nhds (by positivity : (0 : ℝ) < η / 2))
  filter_upwards [eventually_ge_atTop (1 : ℝ), hT_close, hδ_c, hquad_c] with
    c hc1 hTc hδc hqc T' hT' h hh y hy
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  have hAc_dist : |((T' - h) / c) - 1 / π ^ 2| < ε₁ := by
    have htri : |((T' - h) / c) - 1 / π ^ 2| ≤ |T c / c - 1 / π ^ 2| + |(T' - T c - h) / c| := by
      rw [show (T' - h) / c - 1 / π ^ 2 = (T c / c - 1 / π ^ 2) + (T' - T c - h) / c by ring]
      exact abs_add_le _ _
    have h1c_le : 1 / c ≤ 1 := (div_le_one hc0).mpr hc1
    have hTdiff : |T' - T c - h| ≤ δ + 1 := by
      rw [abs_le]; constructor <;> linarith [hT'.1, hT'.2, hh.1, hh.2]
    have hhc : |(T' - T c - h) / c| ≤ (δ + 1) / c := by
      rw [abs_div, abs_of_pos hc0]
      exact div_le_div_of_nonneg_right hTdiff hc0.le
    linarith
  have hAc_low : 1 / (2 * π ^ 2) ≤ (T' - h) / c := by
    have h1 : 1 / π ^ 2 - ε₁ ≤ (T' - h) / c := by linarith [(abs_lt.mp hAc_dist).1]
    have h2 : ε₁ ≤ 1 / (4 * π ^ 2) := min_le_left _ _
    have h3 : 1 / (2 * π ^ 2) ≤ 1 / π ^ 2 - 1 / (4 * π ^ 2) := by
      rw [show 1 / π ^ 2 - 1 / (4 * π ^ 2) = 3 / (4 * π ^ 2) by ring,
        show (1 / (2 * π ^ 2) : ℝ) = 2 / (4 * π ^ 2) by ring]
      exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
    linarith
  have hAc_pos : 0 < T' - h := by
    have := mul_pos h1pi2 hc0
    have hmul := (le_div_iff₀ hc0).mp hAc_low
    linarith
  have hyh_nn : 0 ≤ y + h := by linarith [hy.1]
  have hyh_le : y + h ≤ M' := by dsimp [M']; linarith [hh.2, hy.2]
  have hTy_pos : 0 < T' + y := by linarith
  let u : ℝ := (y + h) / (T' - h)
  have hu_nn : 0 ≤ u := div_nonneg hyh_nn hAc_pos.le
  have hratio : (T' + y) / (T' - h) = 1 + u := by
    dsimp [u]; field_simp [hAc_pos.ne']; ring
  have hlog_nn : 0 ≤ Real.log (1 + u) := Real.log_nonneg (by linarith)
  have hexp_lhs : ((T' + y) / (T' - h)) ^ (-(c / 2)) = Real.exp (-(c / 2) * Real.log (1 + u)) := by
    rw [hratio, Real.rpow_def_of_pos (by linarith : 0 < 1 + u), mul_comm]
  have harg1 : -(c / 2) * Real.log (1 + u) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hlog_nn
  have harg2 : -b * (y + h) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by dsimp [b]; linarith) hyh_nn
  have hdiff_rpow := abs_exp_sub_exp_le_of_nonpos harg1 harg2
  have hcoeff_bd : |c / (2 * (T' - h)) - b| ≤ η / (2 * (M' + 1)) := by
    have hratio_id : c / (2 * (T' - h)) - b =
        (π ^ 2 / 2) * (1 / π ^ 2 - (T' - h) / c) / ((T' - h) / c) := by
      field_simp [hc0.ne', hAc_pos.ne', hpi2.ne']
      dsimp [b]; ring
    rw [hratio_id, abs_div, abs_mul, abs_of_pos (by positivity : 0 < π ^ 2 / 2),
      abs_of_pos (lt_of_lt_of_le h1pi2 hAc_low)]
    have hnum_le : (π ^ 2 / 2) * |1 / π ^ 2 - (T' - h) / c| ≤ (π ^ 2 / 2) * ε₁ := by
      gcongr; rw [abs_sub_comm]; exact hAc_dist.le
    calc (π ^ 2 / 2) * |1 / π ^ 2 - (T' - h) / c| / ((T' - h) / c)
        ≤ (π ^ 2 / 2) * ε₁ / (1 / (2 * π ^ 2)) :=
          div_le_div₀ (by positivity) hnum_le h1pi2 hAc_low
      _ = π ^ 4 * ε₁ := by rw [div_div_eq_mul_div, div_one]; ring
      _ ≤ π ^ 4 * (η / (2 * π ^ 4 * (M' + 1))) := mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
      _ = η / (2 * (M' + 1)) := by field_simp [Real.pi_pos.ne']
  have hquad_bd : (c / 2) * (u ^ 2 / 2) ≤ η / 2 := by
    have hAc_c : c / (2 * π ^ 2) ≤ T' - h := by
      have := (le_div_iff₀ hc0).mp hAc_low
      linarith [show 1 / (2 * π ^ 2) * c = c / (2 * π ^ 2) by ring]
    have hu_bd : u ≤ M' / (c / (2 * π ^ 2)) := by
      dsimp [u]
      exact div_le_div₀ (by dsimp [M']; positivity : 0 ≤ M') hyh_le (by positivity) hAc_c
    have hcu : (c / 2) * (u ^ 2 / 2) ≤ 2 * π ^ 4 * M' ^ 2 / c := by
      have hsq : u ^ 2 ≤ (M' / (c / (2 * π ^ 2))) ^ 2 :=
        pow_le_pow_left₀ hu_nn hu_bd 2
      calc (c / 2) * (u ^ 2 / 2)
          ≤ (c / 2) * ((M' / (c / (2 * π ^ 2))) ^ 2 / 2) := by gcongr
        _ = (π ^ 4 * M' ^ 2) / c := by field_simp [hc0.ne', Real.pi_pos.ne']
        _ ≤ 2 * π ^ 4 * M' ^ 2 / c := by
            have : (0 : ℝ) ≤ π ^ 4 * M' ^ 2 / c := by positivity
            linarith [show 2 * π ^ 4 * M' ^ 2 / c = 2 * (π ^ 4 * M' ^ 2 / c) by ring]
    exact hcu.trans hqc
  have hlin_bd : (y + h) * |c / (2 * (T' - h)) - b| ≤ η / 2 := by
    calc (y + h) * |c / (2 * (T' - h)) - b|
        ≤ M' * (η / (2 * (M' + 1))) := mul_le_mul hyh_le hcoeff_bd (abs_nonneg _) (by positivity)
      _ ≤ (M' + 1) * (η / (2 * (M' + 1))) := by gcongr; linarith
      _ = η / 2 := by field_simp [(by positivity : 0 < M' + 1).ne']
  have harg_diff : |-(c / 2) * Real.log (1 + u) - (-b * (y + h))| ≤ η := by
    have hid : -(c / 2) * Real.log (1 + u) - (-b * (y + h)) =
        -(c / 2) * (Real.log (1 + u) - u) - (y + h) * (c / (2 * (T' - h)) - b) := by
      dsimp [u]; field_simp [hAc_pos.ne']; ring
    rw [hid]
    calc |-(c / 2) * (Real.log (1 + u) - u) - (y + h) * (c / (2 * (T' - h)) - b)|
        ≤ |-(c / 2) * (Real.log (1 + u) - u)| + |(y + h) * (c / (2 * (T' - h)) - b)| := abs_sub _ _
      _ = (c / 2) * |Real.log (1 + u) - u| + (y + h) * |c / (2 * (T' - h)) - b| := by
          rw [abs_mul, abs_neg, abs_of_pos (half_pos hc0), abs_mul, abs_of_nonneg hyh_nn]
      _ ≤ (c / 2) * (u ^ 2 / 2) + (y + h) * |c / (2 * (T' - h)) - b| := by
          gcongr; exact log_one_add_sub_abs_le hu_nn
      _ ≤ η / 2 + η / 2 := add_le_add hquad_bd hlin_bd
      _ = η := add_halves η
  rw [hexp_lhs]
  exact ⟨hAc_pos, hTy_pos, hdiff_rpow.trans harg_diff⟩

/-- Core Langer + exponential-tail positivity lemma (`gt:7.9c`): if `f` is continuous and integrable
against `s^{c/2 - 1}` on `(0, ∞)`, `f ≥ 0` on `[T, ∞)`, `f (T + y) * ρ₀(c, T + y)` is uniformly
approximated by a `C¹` curve `Q` with `Q'/K_c ∈ [1 - ηp, 1 + ηp]` on `[-δ, M]`, and the Mellin
weight `((T + y) / (T - h))^{-c/2}` is uniformly within `ηw` of `exp(-(π²/2)(y + h))`, then
`intertwiner c f (T - h) ≥ 0` for every `h ∈ [0, δ]`. -/
private lemma langer_intertwiner_pos_near_thresh
    {c T δ M Kc ηp ηw ε₀ : ℝ}
    (hc : 0 < c) (hδ : 0 < δ) (hM : 0 ≤ M) (hKc : 0 < Kc) (_hε₀ : 0 < ε₀)
    (hδ_up : δ ≤ 2 / π ^ 2 - ε₀)
    {f Q Q' R : ℝ → ℝ}
    (hf_cont : ContinuousOn f (Ici 0))
    (hf_int : IntegrableOn (fun s => |f s| * s ^ (c / 2 - 1)) (Ioi 0))
    (hf_tail : ∀ Δ ≥ T, 0 ≤ f Δ)
    (hT_gt : δ < T)
    (hdecomp : ∀ y ∈ Icc (-δ) M, f (T + y) * hankelRho0 c (T + y) = Q y + R y)
    (hR_bd : ∀ y ∈ Icc (-δ) M, |R y| ≤ ηp * Kc)
    (hQ'_cont : ContinuousOn Q' (Icc (-δ) M))
    (hQ_deriv : ∀ y ∈ Icc (-δ) M, HasDerivAt Q (Q' y) y)
    (hQ'_bd : ∀ y ∈ Icc (-δ) M, (1 - ηp) * Kc ≤ Q' y ∧ Q' y ≤ (1 + ηp) * Kc)
    (hw_unif : ∀ h ∈ Icc (0 : ℝ) δ, ∀ y ∈ Icc (-h) M,
      |((T + y) / (T - h)) ^ (-(c / 2)) - Real.exp (-(π ^ 2 / 2) * (y + h))| ≤ ηw)
    (htail_exp : ∫ y in Ioi M, y * Real.exp (-(π ^ 2 / 2) * y) ≤ ε₀ / (2 * (π ^ 2 / 2)))
    (herr_small : (δ + M) * ((δ + M) * ηw + ηp * (2 + δ + M) * (1 + ηw)) ≤ ε₀ / (2 * (π ^ 2 / 2))) :
    ∀ h ∈ Icc (0 : ℝ) δ, 0 ≤ intertwiner c f (T - h) := by
  intro h hh
  have hb : (0 : ℝ) < π ^ 2 / 2 := by positivity
  have hΔ : 0 < T - h := by linarith [hh.2]
  have hQ0_ge : -ηp * Kc ≤ Q 0 := by
    have h0mem : (0 : ℝ) ∈ Icc (-δ) M := ⟨by linarith, hM⟩
    have hTpos : 0 < T := hδ.trans hT_gt
    have hfT : 0 ≤ f T * hankelRho0 c T :=
      mul_nonneg (hf_tail T le_rfl) (hankelRho0_nonneg hc hTpos.le)
    have hdec0 := hdecomp 0 h0mem
    rw [add_zero] at hdec0
    have hR0 : R 0 ≤ ηp * Kc := (abs_le.mp (hR_bd 0 h0mem)).2
    linarith
  have hP_low : ∀ y ∈ Icc (-h) M, Kc * y - ηp * (2 + δ + M) * Kc ≤
      f (T + y) * hankelRho0 c (T + y) := by
    intro y hy
    have hy_big : y ∈ Icc (-δ) M := ⟨by linarith [hh.2, hy.1], hy.2⟩
    have hdec := hdecomp y hy_big
    have hR_low : -(ηp * Kc) ≤ R y := (abs_le.mp (hR_bd y hy_big)).1
    have hQ_low : Kc * y - ηp * (1 + δ + M) * Kc ≤ Q y := by
      rcases le_or_gt 0 y with hy0 | hyneg
      · have hsub : Icc 0 y ⊆ Icc (-δ) M := fun t ht => ⟨by linarith [ht.1], ht.2.trans hy.2⟩
        have hftc : Q y - Q 0 = ∫ t in (0 : ℝ)..y, Q' t :=
          (intervalIntegral.integral_eq_sub_of_hasDerivAt
            (fun t ht => hQ_deriv t (hsub (by rwa [Set.uIcc_of_le hy0] at ht)))
            ((hQ'_cont.mono hsub).intervalIntegrable_of_Icc hy0)).symm
        have hint_low : (1 - ηp) * Kc * y ≤ ∫ t in (0 : ℝ)..y, Q' t := by
          have hconst : ∫ _t in (0 : ℝ)..y, (1 - ηp) * Kc = (1 - ηp) * Kc * y := by
            rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]; ring
          rw [← hconst]
          exact intervalIntegral.integral_mono_on hy0 continuousOn_const.intervalIntegrable
            ((hQ'_cont.mono hsub).intervalIntegrable_of_Icc hy0)
            fun t ht => (hQ'_bd t (hsub ht)).1
        have hηy : ηp * Kc * y ≤ ηp * Kc * M := by
          rcases le_or_gt 0 ηp with hηnn | hηneg
          · exact mul_le_mul_of_nonneg_left hy.2 (mul_nonneg hηnn hKc.le)
          · have hfalse : (1 + ηp) * Kc < (1 - ηp) * Kc := by nlinarith
            have h0bd := hQ'_bd 0 ⟨by linarith, hM⟩
            linarith
        have hηnn : 0 ≤ ηp * Kc := by
          have h0bd := hQ'_bd 0 ⟨by linarith, hM⟩
          linarith
        nlinarith
      · have hy0 : y ≤ 0 := hyneg.le
        have hsub : Icc y 0 ⊆ Icc (-δ) M := fun t ht => ⟨by linarith [hh.2, hy.1, ht.1], ht.2.trans hM⟩
        have hftc : Q 0 - Q y = ∫ t in y..0, Q' t :=
          (intervalIntegral.integral_eq_sub_of_hasDerivAt
            (fun t ht => hQ_deriv t (hsub (by rwa [Set.uIcc_of_le hy0] at ht)))
            ((hQ'_cont.mono hsub).intervalIntegrable_of_Icc hy0)).symm
        have hint_up : ∫ t in y..0, Q' t ≤ (1 + ηp) * Kc * (-y) := by
          have hconst : ∫ _t in y..0, (1 + ηp) * Kc = (1 + ηp) * Kc * (-y) := by
            rw [intervalIntegral.integral_const, smul_eq_mul, zero_sub]; ring
          rw [← hconst]
          exact intervalIntegral.integral_mono_on hy0
            ((hQ'_cont.mono hsub).intervalIntegrable_of_Icc hy0)
            continuousOn_const.intervalIntegrable
            fun t ht => (hQ'_bd t (hsub ht)).2
        have hηnn : 0 ≤ ηp * Kc := by
          have h0bd := hQ'_bd 0 ⟨by linarith, hM⟩
          linarith
        have hy_abs : -y ≤ δ := by linarith [hh.2, hy.1]
        have hηy : ηp * Kc * (-y) ≤ ηp * Kc * δ := mul_le_mul_of_nonneg_left hy_abs hηnn
        nlinarith
    linarith
  have hIoc_low : Kc * (ε₀ / (2 * (π ^ 2 / 2))) -
      Kc * ((δ + M) * ((δ + M) * ηw + ηp * (2 + δ + M) * (1 + ηw))) ≤
      ∫ y in Ioc (-h) M,
        (f (T + y) * hankelRho0 c (T + y)) * ((T + y) / (T - h)) ^ (-(c / 2)) := by
    have hηw_nn : 0 ≤ ηw := (abs_nonneg _).trans (hw_unif h hh 0 ⟨by linarith [hh.1], hM⟩)
    let G_low : ℝ → ℝ := fun y =>
      Kc * (y * Real.exp (-(π ^ 2 / 2) * (y + h)) -
        ((δ + M) * ηw + ηp * (2 + δ + M) * (1 + ηw)))
    have hP_int : IntegrableOn (fun y : ℝ =>
        (f (T + y) * hankelRho0 c (T + y)) * ((T + y) / (T - h)) ^ (-(c / 2))) (Ioc (-h) M) := by
      have hcontP : ContinuousOn (fun y : ℝ =>
          (f (T + y) * hankelRho0 c (T + y)) * ((T + y) / (T - h)) ^ (-(c / 2))) (Icc (-h) M) := by
        have hTy_pos : ∀ y ∈ Icc (-h) M, 0 < T + y := fun y hy => by linarith [hy.1]
        refine ((hf_cont.comp (continuous_const_add T).continuousOn fun y hy => (hTy_pos y hy).le).mul
          ((continuousOn_hankelRho0 c).comp (continuous_const_add T).continuousOn fun y hy => hTy_pos y hy)).mul ?_
        exact ContinuousOn.rpow_const
          ((continuousOn_const.add continuousOn_id).div_const (T - h))
          fun y hy => Or.inl (div_pos (hTy_pos y hy) hΔ).ne'
      exact hcontP.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    have hG_int : IntegrableOn G_low (Ioc (-h) M) := by
      have hcontG : ContinuousOn G_low (Icc (-h) M) := by dsimp [G_low]; fun_prop
      exact hcontG.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    have hpt : ∀ y ∈ Ioc (-h) M,
        G_low y ≤ (f (T + y) * hankelRho0 c (T + y)) * ((T + y) / (T - h)) ^ (-(c / 2)) := by
      intro y hy
      have hyc : y ∈ Icc (-h) M := Ioc_subset_Icc_self hy
      have hTy : 0 < T + y := by linarith [hyc.1]
      let w : ℝ := ((T + y) / (T - h)) ^ (-(c / 2))
      let e : ℝ := Real.exp (-(π ^ 2 / 2) * (y + h))
      have hw_nn : 0 ≤ w := Real.rpow_nonneg (div_nonneg hTy.le hΔ.le) _
      have he_bd : 0 ≤ e ∧ e ≤ 1 := ⟨(Real.exp_pos _).le,
        Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith [hyc.1]))⟩
      have hw_diff : |w - e| ≤ ηw := hw_unif h hh y hyc
      have hw_le : w ≤ 1 + ηw := by linarith [(abs_le.mp hw_diff).2, he_bd.2]
      have hy_abs : |y| ≤ δ + M := abs_le.mpr ⟨by linarith [hh.2, hyc.1], by linarith [hh.1, hyc.2]⟩
      have hyw_bd : y * e - (δ + M) * ηw ≤ y * w := by
        have h1 : |y * (w - e)| ≤ (δ + M) * ηw := by
          rw [abs_mul]; exact mul_le_mul hy_abs hw_diff (abs_nonneg _) (by positivity)
        linarith [(abs_le.mp h1).1]
      have hP1 := hP_low y hyc
      have hP2 : Kc * (y - ηp * (2 + δ + M)) * w ≤ (f (T + y) * hankelRho0 c (T + y)) * w := by
        calc Kc * (y - ηp * (2 + δ + M)) * w
            = (Kc * y - ηp * (2 + δ + M) * Kc) * w := by ring
          _ ≤ (f (T + y) * hankelRho0 c (T + y)) * w := mul_le_mul_of_nonneg_right hP1 hw_nn
      have hηp_nn : 0 ≤ ηp := by
        have := (abs_nonneg (R 0)).trans (hR_bd 0 ⟨by linarith, hM⟩)
        exact nonneg_of_mul_nonneg_left this hKc
      have h3 : y * e - (δ + M) * ηw - ηp * (2 + δ + M) * (1 + ηw) ≤ (y - ηp * (2 + δ + M)) * w := by
        have := mul_le_mul_of_nonneg_left hw_le (mul_nonneg hηp_nn (by positivity : 0 ≤ 2 + δ + M))
        linarith
      calc G_low y = Kc * (y * e - (δ + M) * ηw - ηp * (2 + δ + M) * (1 + ηw)) := by dsimp [G_low, e]; ring
        _ ≤ Kc * ((y - ηp * (2 + δ + M)) * w) := mul_le_mul_of_nonneg_left h3 hKc.le
        _ = Kc * (y - ηp * (2 + δ + M)) * w := by ring
        _ ≤ (f (T + y) * hankelRho0 c (T + y)) * w := hP2
    have hint_mono := setIntegral_mono_on hG_int hP_int measurableSet_Ioc hpt
    have hG_eval : Kc * (∫ y in Ioc (-h) M, y * Real.exp (-(π ^ 2 / 2) * (y + h))) -
        Kc * ((δ + M) * ((δ + M) * ηw + ηp * (2 + δ + M) * (1 + ηw))) ≤
        ∫ y in Ioc (-h) M, G_low y := by
      have hm_le : M - (-h) ≤ δ + M := by linarith [hh.2]
      have hsub1 : IntegrableOn (fun y : ℝ => Kc * (y * Real.exp (-(π ^ 2 / 2) * (y + h)))) (Ioc (-h) M) :=
        ((by fun_prop : Continuous fun y : ℝ =>
          Kc * (y * Real.exp (-(π ^ 2 / 2) * (y + h)))).continuousOn.integrableOn_Icc).mono_set Ioc_subset_Icc_self
      have hsub2 : IntegrableOn (fun _ : ℝ => Kc * ((δ + M) * ηw + ηp * (2 + δ + M) * (1 + ηw))) (Ioc (-h) M) :=
        continuousOn_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self
      have hG_eq : ∫ y in Ioc (-h) M, G_low y =
          Kc * (∫ y in Ioc (-h) M, y * Real.exp (-(π ^ 2 / 2) * (y + h))) -
            (M - (-h)) * (Kc * ((δ + M) * ηw + ηp * (2 + δ + M) * (1 + ηw))) := by
        have : ∫ y in Ioc (-h) M, G_low y =
            (∫ y in Ioc (-h) M, Kc * (y * Real.exp (-(π ^ 2 / 2) * (y + h)))) -
              ∫ _y in Ioc (-h) M, Kc * ((δ + M) * ηw + ηp * (2 + δ + M) * (1 + ηw)) := by
          rw [← integral_sub hsub1 hsub2]
          refine setIntegral_congr_fun measurableSet_Ioc fun y _ => by dsimp [G_low]; ring
        rw [this, integral_const_mul, setIntegral_const, smul_eq_mul, Measure.real_def,
          Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith [hh.1])]
      have hC_nn : 0 ≤ Kc * ((δ + M) * ηw + ηp * (2 + δ + M) * (1 + ηw)) := by
        have hηp_nn : 0 ≤ ηp := by
          have := (abs_nonneg (R 0)).trans (hR_bd 0 ⟨by linarith, hM⟩)
          exact nonneg_of_mul_nonneg_left this hKc
        positivity
      rw [hG_eq]
      nlinarith
    have hIoc_exp : ε₀ / (2 * (π ^ 2 / 2)) ≤
        ∫ y in Ioc (-h) M, y * Real.exp (-(π ^ 2 / 2) * (y + h)) := by
      have ⟨hint_all, hval_all⟩ := integral_linear_exp_tail_lower hb h
      have hsplit_exp : ∫ y in Ioi (-h), y * Real.exp (-(π ^ 2 / 2) * (y + h)) =
          (∫ y in Ioc (-h) M, y * Real.exp (-(π ^ 2 / 2) * (y + h))) +
            ∫ y in Ioi M, y * Real.exp (-(π ^ 2 / 2) * (y + h)) := by
        have hleM : -h ≤ M := by linarith [hh.1]
        rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
          (hint_all.mono_set Ioc_subset_Ioi_self) (hint_all.mono_set (Ioi_subset_Ioi hleM)),
          Set.Ioc_union_Ioi_eq_Ioi hleM]
      have htail_bd : ∫ y in Ioi M, y * Real.exp (-(π ^ 2 / 2) * (y + h)) ≤
          ∫ y in Ioi M, y * Real.exp (-(π ^ 2 / 2) * y) := by
        have hleM : -h ≤ M := by linarith [hh.1]
        have hint_b : IntegrableOn (fun y : ℝ => y * Real.exp (-(π ^ 2 / 2) * y)) (Ioi M) := by
          have hbase := (integrableOn_rpow_mul_exp_neg_mul_Ioi (by norm_num : (-1 : ℝ) < 1) hb).mono_set
            (Ioi_subset_Ioi hM)
          exact hbase.congr_fun (fun y _ => by dsimp only; rw [Real.rpow_one]) measurableSet_Ioi
        refine setIntegral_mono_on (hint_all.mono_set (Ioi_subset_Ioi hleM)) hint_b measurableSet_Ioi fun y (hy : M < y) => ?_
        have hy_nn : 0 ≤ y := hM.trans hy.le
        have hexp_le : Real.exp (-(π ^ 2 / 2) * (y + h)) ≤ Real.exp (-(π ^ 2 / 2) * y) :=
          Real.exp_le_exp.mpr (by nlinarith [hh.1])
        exact mul_le_mul_of_nonneg_left hexp_le hy_nn
      have htot_low : ε₀ / (π ^ 2 / 2) ≤ 1 / (π ^ 2 / 2) ^ 2 - h / (π ^ 2 / 2) := by
        have hb2 : (1 / (π ^ 2 / 2) : ℝ) = 2 / π ^ 2 := by ring
        calc ε₀ / (π ^ 2 / 2) ≤ (2 / π ^ 2 - h) / (π ^ 2 / 2) := by
              gcongr; linarith [hh.2]
          _ = 1 / (π ^ 2 / 2) ^ 2 - h / (π ^ 2 / 2) := by field_simp [Real.pi_pos.ne']
      have hhalf : ε₀ / (π ^ 2 / 2) - ε₀ / (2 * (π ^ 2 / 2)) = ε₀ / (2 * (π ^ 2 / 2)) := by ring
      linarith [hval_all, hsplit_exp, htail_bd, htail_exp, htot_low, hhalf]
    calc Kc * (ε₀ / (2 * (π ^ 2 / 2))) -
          Kc * ((δ + M) * ((δ + M) * ηw + ηp * (2 + δ + M) * (1 + ηw)))
        ≤ Kc * (∫ y in Ioc (-h) M, y * Real.exp (-(π ^ 2 / 2) * (y + h))) -
            Kc * ((δ + M) * ((δ + M) * ηw + ηp * (2 + δ + M) * (1 + ηw))) := by
          gcongr
      _ ≤ ∫ y in Ioc (-h) M, G_low y := hG_eval
      _ ≤ _ := hint_mono
  have hC_pos : 0 < (2 * π) ^ c / Real.Gamma c * (T - h) ^ (c / 2) :=
    mul_pos (div_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.Gamma_pos_of_pos hc))
      (Real.rpow_pos_of_pos hΔ _)
  have hIoc_nn : 0 ≤ ∫ y in Ioc (-h) M,
      (f (T + y) * hankelRho0 c (T + y)) * ((T + y) / (T - h)) ^ (-(c / 2)) := by
    have hbd : 0 ≤ Kc * (ε₀ / (2 * (π ^ 2 / 2))) -
        Kc * ((δ + M) * ((δ + M) * ηw + ηp * (2 + δ + M) * (1 + ηw))) := by
      have : (δ + M) * ((δ + M) * ηw + ηp * (2 + δ + M) * (1 + ηw)) ≤ ε₀ / (2 * (π ^ 2 / 2)) := herr_small
      nlinarith [hKc]
    exact hbd.trans hIoc_low
  have hf_rpow_int : IntegrableOn (fun s : ℝ => f s * s ^ (c / 2 - 1)) (Ioi (T - h)) := by
    refine (hf_int.mono_set (Ioi_subset_Ioi hΔ.le)).mono'
      (((hf_cont.mono Ioi_subset_Ici_self).mul
        (ContinuousOn.rpow_const continuousOn_id fun s hs =>
          Or.inl (ne_of_gt (mem_Ioi.mp hs)))).aestronglyMeasurable measurableSet_Ioi |>.mono_measure
          (Measure.restrict_mono (Ioi_subset_Ioi hΔ.le) le_rfl)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s (hs : T - h < s)
    have hs0 : 0 < s := hΔ.trans hs
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hs0.le _)]
  have htail_pos : ∀ R : ℝ, M ≤ R →
      0 ≤ ∫ s in (T - h)..(T + R), f s * s ^ (c / 2 - 1) := by
    intro R hMR
    let g : ℝ → ℝ := fun y => (f (T + y) * hankelRho0 c (T + y)) * ((T + y) / (T - h)) ^ (-(c / 2))
    have hle1 : -h ≤ M := by linarith [hh.1]
    have hg_Ioc1 : IntervalIntegrable g volume (-h) M := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle1]
      have hTy_pos : ∀ y ∈ Icc (-h) M, 0 < T + y := fun y hy => by linarith [hy.1]
      have hcontg : ContinuousOn g (Icc (-h) M) := by
        refine ((hf_cont.comp (continuous_const_add T).continuousOn fun y hy => (hTy_pos y hy).le).mul
          ((continuousOn_hankelRho0 c).comp (continuous_const_add T).continuousOn fun y hy => hTy_pos y hy)).mul ?_
        exact ContinuousOn.rpow_const
          ((continuousOn_const.add continuousOn_id).div_const (T - h))
          fun y hy => Or.inl (div_pos (hTy_pos y hy) hΔ).ne'
      exact hcontg.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    have hg_Ioc2 : IntervalIntegrable g volume M R := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hMR]
      have hTy_pos : ∀ y ∈ Icc M R, 0 < T + y := fun y hy => by linarith [hy.1, hM, hδ.trans hT_gt]
      have hcontg : ContinuousOn g (Icc M R) := by
        refine ((hf_cont.comp (continuous_const_add T).continuousOn fun y hy => (hTy_pos y hy).le).mul
          ((continuousOn_hankelRho0 c).comp (continuous_const_add T).continuousOn fun y hy => hTy_pos y hy)).mul ?_
        exact ContinuousOn.rpow_const
          ((continuousOn_const.add continuousOn_id).div_const (T - h))
          fun y hy => Or.inl (div_pos (hTy_pos y hy) hΔ).ne'
      exact hcontg.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    have hg_add : ∫ y in (-h)..R, g y = (∫ y in (-h)..M, g y) + ∫ y in M..R, g y :=
      (intervalIntegral.integral_add_adjacent_intervals hg_Ioc1 hg_Ioc2).symm
    have hg1_nn : 0 ≤ ∫ y in (-h)..M, g y := by
      rw [intervalIntegral.integral_of_le hle1]; exact hIoc_nn
    have hg2_nn : 0 ≤ ∫ y in M..R, g y := by
      rw [intervalIntegral.integral_of_le hMR]
      refine setIntegral_nonneg measurableSet_Ioc fun y (hy : y ∈ Ioc M R) => ?_
      have hTy : T ≤ T + y := by linarith [hy.1, hM]
      have hTy0 : 0 < T + y := by linarith [hδ.trans hT_gt, hy.1, hM]
      exact mul_nonneg (mul_nonneg (hf_tail (T + y) hTy) (hankelRho0_nonneg hc hTy0.le))
        (Real.rpow_nonneg (div_nonneg hTy0.le hΔ.le) _)
    have hshift : ∫ y in (-h)..R, g y =
        ((2 * π) ^ c / Real.Gamma c * (T - h) ^ (c / 2)) * ∫ s in (T - h)..(T + R), f s * s ^ (c / 2 - 1) := by
      have hcongr : ∫ y in (-h)..R, g y =
          ∫ y in (-h)..R, ((2 * π) ^ c / Real.Gamma c * (T - h) ^ (c / 2)) *
            (f (y + T) * (y + T) ^ (c / 2 - 1)) := by
        rw [intervalIntegral.integral_of_le (hle1.trans hMR), intervalIntegral.integral_of_le (hle1.trans hMR)]
        refine setIntegral_congr_fun measurableSet_Ioc fun y (hy : y ∈ Ioc (-h) R) => ?_
        have hTy : 0 < T + y := by linarith [hy.1]
        dsimp [g]; unfold hankelRho0
        rw [Real.div_rpow hTy.le hΔ.le]
        have hp1 : (T + y) ^ (c - 1) * ((T + y) ^ (-(c / 2))) = (T + y) ^ (c / 2 - 1) := by
          rw [← Real.rpow_add hTy]; congr 1; ring
        have hp2 : ((T - h) ^ (-(c / 2)))⁻¹ = (T - h) ^ (c / 2) := by
          rw [Real.rpow_neg hΔ.le, inv_inv]
        calc f (T + y) * ((2 * π) ^ c / Real.Gamma c * (T + y) ^ (c - 1)) *
              ((T + y) ^ (-(c / 2)) / (T - h) ^ (-(c / 2)))
            = ((2 * π) ^ c / Real.Gamma c * ((T - h) ^ (-(c / 2)))⁻¹) *
                (f (T + y) * ((T + y) ^ (c - 1) * (T + y) ^ (-(c / 2)))) := by ring
          _ = ((2 * π) ^ c / Real.Gamma c * (T - h) ^ (c / 2)) *
                (f (y + T) * (y + T) ^ (c / 2 - 1)) := by
              rw [hp1, hp2, add_comm T y]
      rw [hcongr, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_add_right (fun s => f s * s ^ (c / 2 - 1)) T]
      rw [show -h + T = T - h by ring, show R + T = T + R by ring]
    have hmul_nn : 0 ≤ ((2 * π) ^ c / Real.Gamma c * (T - h) ^ (c / 2)) *
        ∫ s in (T - h)..(T + R), f s * s ^ (c / 2 - 1) := by
      linarith [hg_add, hg1_nn, hg2_nn, hshift]
    exact nonneg_of_mul_nonneg_right hmul_nn hC_pos
  have hlim_Ioi : Tendsto (fun R : ℝ => ∫ s in (T - h)..(T + R), f s * s ^ (c / 2 - 1))
      atTop (𝓝 (∫ s in Ioi (T - h), f s * s ^ (c / 2 - 1))) :=
    intervalIntegral_tendsto_integral_Ioi (T - h) hf_rpow_int (tendsto_const_nhds.add_atTop tendsto_id)
  have hIoi_nn : 0 ≤ ∫ s in Ioi (T - h), f s * s ^ (c / 2 - 1) :=
    ge_of_tendsto hlim_Ioi (eventually_atTop.mpr ⟨M, htail_pos⟩)
  unfold intertwiner
  simp only [hΔ, ↓reduceIte]
  exact mul_nonneg (Real.rpow_nonneg hΔ.le _) hIoi_nn

/-- Analytic package of hypotheses for Theorem 7.9c (`gt:7.9c`): a family of Hankel kernels
`K c` (`c ≥ c₀`) having `(-1)`-feasible eigenfunctions whose one-level thresholds have the Airy
order `T_c^{-1} = c/π² + (|a₁|/β₁) c^{1/3} + o(c^{1/3})` (`gt:7.5` lower bound with the one-level
`O.9'`), and whose near-optimal `(-1)`-feasible eigenfunctions have window profiles
`Ψ_{f,c}/M[f]` converging to the normalised Airy extremal `G_Ai/‖G_Ai‖₁` locally uniformly together
with the first derivative (`gt:7.5`, identification of the limit, and `lem:radial-compactness`, whose
`C¹` clause is the content of this field). The Langer chart is not used (`gt:7.9c` no longer needs it).

Content of the fields: see `Headlines.lean` (`radial_rigidity_lower` and `radial_profile_c1` are theorems
there, from `radial_compactness`; `hb_thresholds_upper` is the one open input). -/
structure SignSeparationPackage where
  c₀ : ℝ
  hc₀ : 0 < c₀
  K : ∀ c ≥ c₀, HankelKernelData c
  neg_feasible : ∀ (c : ℝ) (hc : c₀ ≤ c), ∃ T f, IsFeasible c (K c hc) (-1) T f
  Tneg_airy_order : Tendsto (fun c : ℝ =>
    if hc : c₀ ≤ c then (hankelThreshold c (K c hc) (-1) - c / π ^ 2) / c ^ (1 / 3 : ℝ) else 0)
    atTop (𝓝 (|airyZero 1| / hankelBeta1))
  c1_profile : ∀ (R η : ℝ), 0 < η →
    ∀ᶠ c in atTop, ∀ (hc : c₀ ≤ c) (T : ℝ) (f : ℝ → ℝ),
      IsFeasible c (K c hc) (-1) T f →
      hankelThreshold c (K c hc) (-1) ≤ T →
      T ≤ hankelThreshold c (K c hc) (-1) + 1 / c →
      ContDiffOn ℝ 1 (fun u => hankelWindowProfile c f u / hankelMass c f) (Ioo (-R) R) ∧
      ∀ u ∈ Ioo (-R) R,
        |hankelWindowProfile c f u / hankelMass c f - HermiteBiehlerData.airy.normG u| ≤ η ∧
        |deriv (fun v => hankelWindowProfile c f v / hankelMass c f) u -
            deriv HermiteBiehlerData.airy.normG u| ≤ η

noncomputable def SignSeparationPackage.Tneg (P : SignSeparationPackage) (c : ℝ) : ℝ :=
  if hc : P.c₀ ≤ c then hankelThreshold c (P.K c hc) (-1) else 0

noncomputable def SignSeparationPackage.Tpos (P : SignSeparationPackage) (c : ℝ) : ℝ :=
  if hc : P.c₀ ≤ c then hankelThreshold c (P.K c hc) 1 else 0

/-- The normalised Airy extremal is `C¹` (indeed smooth). -/
lemma airy_normG_contDiff : ContDiff ℝ 1 HermiteBiehlerData.airy.normG := by
  have h1 : ContDiff ℝ 1 (fun u : ℝ => airyExtremal (u : ℂ)) :=
    ((differentiable_airyExtremal.contDiff (n := 1)).restrict_scalars ℝ).comp
      Complex.ofRealCLM.contDiff
  have h2 : ContDiff ℝ 1 (fun u : ℝ => (airyExtremal (u : ℂ)).re) :=
    Complex.reCLM.contDiff.comp h1
  exact h2.div_const _

/-- `T_c^{-1} / c → 1/π²` follows from the Airy-order asymptotics of `T_c^{-1}`. -/
theorem SignSeparationPackage.Tneg_asymp (P : SignSeparationPackage) :
    Tendsto (fun c : ℝ =>
      if hc : P.c₀ ≤ c then hankelThreshold c (P.K c hc) (-1) / c else 0) atTop (𝓝 (1 / π ^ 2)) := by
  have h0 : Tendsto (fun c : ℝ => c ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  have h1 := (P.Tneg_airy_order.mul h0).const_add (1 / π ^ 2)
  rw [mul_zero, add_zero] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop P.c₀, eventually_gt_atTop (0 : ℝ)] with c hc hc0
  rw [dif_pos hc, dif_pos hc]
  have hab : c ^ (1 / 3 : ℝ) * c ^ (2 / 3 : ℝ) = c := by
    rw [← Real.rpow_add hc0]; norm_num
  have h3 : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
  have h4 : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
  rw [Real.rpow_neg hc0.le]
  field_simp
  linear_combination (c - π ^ 2 * hankelThreshold c (P.K c hc) (-1)) * hab

/-- From the `C¹` profile convergence to the two-sided slope window used by Theorem 7.9c: near the
terminal threshold the density `y ↦ f(T + y) ρ₀(T + y)` of a near-optimal `(-1)`-feasible `f` has
derivative within a factor `1 ± η` of a fixed positive multiple `K_c` (so `R = 0` below; no Langer
transport is needed). -/
theorem SignSeparationPackage.langer_approx (P : SignSeparationPackage) (δ M η : ℝ) (hδ : 0 < δ)
    (hM : 0 ≤ M) (hη : 0 < η) :
    ∀ᶠ c in atTop, ∀ (hc : P.c₀ ≤ c) (T : ℝ) (f : ℝ → ℝ),
      IsFeasible c (P.K c hc) (-1) T f →
      hankelThreshold c (P.K c hc) (-1) ≤ T →
      T ≤ hankelThreshold c (P.K c hc) (-1) + 1 / c →
      ∃ (Q Q' R : ℝ → ℝ) (Kc : ℝ),
        0 < Kc ∧
        (∀ y ∈ Icc (-δ) M, f (T + y) * hankelRho0 c (T + y) = Q y + R y) ∧
        (∀ y ∈ Icc (-δ) M, |R y| ≤ η * Kc) ∧
        ContinuousOn Q' (Icc (-δ) M) ∧
        (∀ y ∈ Icc (-δ) M, HasDerivAt Q (Q' y) y) ∧
        (∀ y ∈ Icc (-δ) M, (1 - η) * Kc ≤ Q' y ∧ Q' y ≤ (1 + η) * Kc) := by
  classical
  set N : ℝ → ℝ := HermiteBiehlerData.airy.normG with hN_def
  set a : ℝ := airyZero 1 with ha_def
  set g' : ℝ := deriv N a with hg'_def
  have hg' : g' < 0 := HermiteBiehlerData.normG_airy_deriv_neg
  have hgabs : 0 < |g'| := abs_pos.mpr hg'.ne
  have ha_neg : a < 0 := airyZero_neg 1
  have hNd_cont : Continuous (deriv N) := airy_normG_contDiff.continuous_deriv le_rfl
  obtain ⟨r, hr, hrN⟩ : ∃ r : ℝ, 0 < r ∧ ∀ u : ℝ, |u - a| < r →
      |deriv N u - g'| ≤ η * |g'| / 4 := by
    obtain ⟨r, hr, h⟩ := Metric.continuousAt_iff.mp hNd_cont.continuousAt (η * |g'| / 4)
      (by positivity)
    exact ⟨r, hr, fun u hu => by
      have := h (show dist u a < r by rwa [Real.dist_eq]); rw [Real.dist_eq] at this; exact this.le⟩
  set ρ : ℝ := min 1 r with hρ
  have hρpos : 0 < ρ := lt_min one_pos hr
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hρr : ρ ≤ r := min_le_right _ _
  set R : ℝ := |a| + 2 with hR_def
  have h1c := P.c1_profile R (η * |g'| / 4) (by positivity)
  have hβ := hankelBeta1_pos
  set β := hankelBeta1 with hβ_def
  have hTn_def : ∀ c : ℝ, ∀ hc : P.c₀ ≤ c, P.Tneg c = hankelThreshold c (P.K c hc) (-1) := fun c hc => by
    unfold SignSeparationPackage.Tneg; rw [dif_pos hc]
  have hT_asymp_real : Tendsto (fun c : ℝ => P.Tneg c / c) atTop (𝓝 (1 / π ^ 2)) :=
    P.Tneg_asymp.congr' (Eventually.of_forall fun c => by
      dsimp [SignSeparationPackage.Tneg]; split_ifs <;> simp)
  have hTinf : Tendsto (fun c : ℝ => P.Tneg c) atTop atTop := by
    have hmul : Tendsto (fun c : ℝ => (P.Tneg c / c) * c) atTop atTop :=
      Filter.Tendsto.pos_mul_atTop (by positivity : (0 : ℝ) < 1 / π ^ 2) hT_asymp_real tendsto_id
    refine hmul.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc0
    rw [div_mul_cancel₀ _ hc0.ne']
  have hs : Tendsto (fun c : ℝ => (P.Tneg c - c / π ^ 2) / c ^ (1 / 3 : ℝ)) atTop
      (𝓝 (|a| / β)) :=
    P.Tneg_airy_order.congr' (by
      filter_upwards [eventually_ge_atTop P.c₀] with c hc
      simp only [SignSeparationPackage.Tneg, dif_pos hc])
  have hs_ev : ∀ᶠ c in atTop, |(P.Tneg c - c / π ^ 2) / c ^ (1 / 3 : ℝ) - |a| / β| < ρ / (2 * β) :=
    hs.eventually (Metric.ball_mem_nhds (|a| / β) (show 0 < ρ / (2 * β) by positivity)) |>.mono fun c hc => by
      rwa [Real.dist_eq] at hc
  have hq0 : Tendsto (fun c : ℝ => β * (1 + δ + M) * c ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).const_mul (β * (1 + δ + M))
  have hq_ev : ∀ᶠ c in atTop, β * (1 + δ + M) * c ^ (-(1 / 3 : ℝ)) < ρ / 2 :=
    hq0.eventually (gt_mem_nhds (by positivity))
  filter_upwards [eventually_ge_atTop (1 : ℝ), hs_ev, hq_ev, hTinf.eventually (eventually_gt_atTop δ),
    h1c] with c hc1 hsc hqc hTδ h1 hc' T f hf hT1 hT2
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc1
  have hTn := hTn_def c hc'
  set q : ℝ := c ^ (1 / 3 : ℝ) with hq_def
  have hq : 0 < q := Real.rpow_pos_of_pos hc0 _
  have hqinv : c ^ (-(1 / 3 : ℝ)) = q⁻¹ := Real.rpow_neg hc0.le _
  rw [hqinv] at hqc
  obtain ⟨hcd, hclose⟩ := h1 hc' T f hf hT1 hT2
  have hMf : 0 < hankelMass c f :=
    hankelMass_pos_of_continuousOn hc0 hf.eigenfn.cont hf.eigenfn.int
      (by obtain ⟨Δ, hΔ, hne⟩ := hf.nonzero; exact ⟨Δ, hΔ, hne⟩)
  set Mf : ℝ := hankelMass c f with hMf_def
  set Ψ : ℝ → ℝ := fun v => hankelWindowProfile c f v / Mf with hΨ_def
  set u : ℝ → ℝ := fun y => β * (c / π ^ 2 - (T + y)) / q with hu_def
  have hTn_pos : δ < T := by
    have := hTδ; rw [hTn] at this; linarith [hT1]
  -- the window in the `u` variable
  have hu_close : ∀ y ∈ Icc (-δ) M, |u y - a| < ρ := by
    intro y hy
    have hs' := hsc
    rw [hTn] at hs'
    set s : ℝ := (hankelThreshold c (P.K c hc') (-1) - c / π ^ 2) / q with hs_def
    have hτ : T = hankelThreshold c (P.K c hc') (-1) + (T - hankelThreshold c (P.K c hc') (-1)) := by ring
    have hτ0 : 0 ≤ T - hankelThreshold c (P.K c hc') (-1) := by linarith
    have hτ1 : T - hankelThreshold c (P.K c hc') (-1) ≤ 1 := by
      have : 1 / c ≤ 1 := (div_le_one hc0).mpr hc1
      linarith
    have hid : u y - a = -(β * (s - |a| / β)) - β * ((T - hankelThreshold c (P.K c hc') (-1)) + y) / q := by
      have hba : β * (|a| / β) = -a := by rw [mul_div_cancel₀ _ hβ.ne', abs_of_neg ha_neg]
      simp only [hu_def, hs_def, abs_of_neg ha_neg]
      field_simp
      ring
    have hb1 : |β * (s - |a| / β)| < ρ / 2 := by
      rw [abs_mul, abs_of_pos hβ]
      calc β * |s - |a| / β| < β * (ρ / (2 * β)) := mul_lt_mul_of_pos_left hs' hβ
        _ = ρ / 2 := by field_simp
    have hb2 : |β * ((T - hankelThreshold c (P.K c hc') (-1)) + y) / q| < ρ / 2 := by
      have hnum : |(T - hankelThreshold c (P.K c hc') (-1)) + y| ≤ 1 + δ + M := by
        rw [abs_le]; constructor <;> linarith [hy.1, hy.2]
      rw [abs_div, abs_mul, abs_of_pos hβ, abs_of_pos hq]
      calc β * |(T - hankelThreshold c (P.K c hc') (-1)) + y| / q
          ≤ β * (1 + δ + M) / q := by gcongr
        _ = β * (1 + δ + M) * q⁻¹ := by rw [div_eq_mul_inv]
        _ < ρ / 2 := hqc
    rw [hid, abs_sub_comm, sub_neg_eq_add]
    calc |β * ((T - hankelThreshold c (P.K c hc') (-1)) + y) / q + β * (s - |a| / β)|
        ≤ |β * ((T - hankelThreshold c (P.K c hc') (-1)) + y) / q| + |β * (s - |a| / β)| :=
          abs_add_le _ _
      _ < ρ / 2 + ρ / 2 := add_lt_add hb2 hb1
      _ = ρ := by ring
  have hu_mem : ∀ y ∈ Icc (-δ) M, u y ∈ Ioo (-R) R := by
    intro y hy
    have h := hu_close y hy
    rw [abs_lt] at h
    constructor <;> [skip; skip] <;> (rw [hR_def, abs_of_neg ha_neg]; linarith [h.1, h.2])
  have hu_cont : Continuous u := by simp only [hu_def]; fun_prop
  have hu_deriv : ∀ y, HasDerivAt u (β * (-1) / q) y := fun y => by
    have := ((((hasDerivAt_id y).const_add T).const_sub (c / π ^ 2)).const_mul β).div_const q
    simpa [hu_def, Function.comp_def] using this
  have hΨdiff : ∀ v ∈ Ioo (-R) R, DifferentiableAt ℝ Ψ v := fun v hv =>
    (hcd.differentiableOn one_ne_zero v hv).differentiableAt (Ioo_mem_nhds hv.1 hv.2)
  have hΨ'cont : ContinuousOn (deriv Ψ) (Ioo (-R) R) :=
    hcd.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl
  set B : ℝ := (β / q) ^ 2 * Mf with hB_def
  have hB : 0 < B := by positivity
  set Kc : ℝ := |g'| * B with hKc_def
  have hKc : 0 < Kc := by positivity
  refine ⟨fun y => (β / q) * Mf * Ψ (u y), fun y => -B * deriv Ψ (u y), fun _ => 0, Kc, hKc,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    have hpos : 0 < T + y := by linarith [hy.1]
    have hΔeq : c / π ^ 2 - u y / β * q = T + y := by
      simp only [hu_def]; field_simp; ring
    have hw : hankelWindowProfile c f (u y) = (q / β) * (f (T + y) * hankelRho0 c (T + y)) := by
      unfold hankelWindowProfile
      dsimp only
      rw [hΔeq, if_pos hpos]
    simp only [hΨ_def, hw]
    field_simp
    ring
  · intro y hy; simp [mul_nonneg hη.le hKc.le]
  · refine ContinuousOn.mul continuousOn_const ?_
    exact hΨ'cont.comp hu_cont.continuousOn (fun y hy => hu_mem y hy)
  · intro y hy
    have h := ((hΨdiff _ (hu_mem y hy)).hasDerivAt.comp y (hu_deriv y)).const_mul ((β / q) * Mf)
    refine h.congr_deriv ?_
    simp only [hB_def]
    field_simp
  · intro y hy
    have hmem := hu_mem y hy
    have hclo := (hclose (u y) hmem).2
    have hNclose : |deriv N (u y) - g'| ≤ η * |g'| / 4 :=
      hrN _ (lt_of_lt_of_le (hu_close y hy) hρr)
    have he : |deriv Ψ (u y) - g'| ≤ η * |g'| / 2 := by
      calc |deriv Ψ (u y) - g'|
          = |(deriv Ψ (u y) - deriv N (u y)) + (deriv N (u y) - g')| := by ring_nf
        _ ≤ |deriv Ψ (u y) - deriv N (u y)| + |deriv N (u y) - g'| := abs_add_le _ _
        _ ≤ η * |g'| / 4 + η * |g'| / 4 := add_le_add hclo hNclose
        _ = η * |g'| / 2 := by ring
    have hdec : -B * deriv Ψ (u y) = Kc - B * (deriv Ψ (u y) - g') := by
      simp only [hKc_def, abs_of_neg hg']; ring
    have hBe := abs_le.mp he
    have h1' : B * (deriv Ψ (u y) - g') ≤ B * (η * |g'| / 2) :=
      mul_le_mul_of_nonneg_left hBe.2 hB.le
    have h2' : B * (-(η * |g'| / 2)) ≤ B * (deriv Ψ (u y) - g') :=
      mul_le_mul_of_nonneg_left hBe.1 hB.le
    have hBη : B * (η * |g'| / 2) = η * Kc / 2 := by simp only [hKc_def]; ring
    have hBη' : B * (-(η * |g'| / 2)) = -(η * Kc / 2) := by simp only [hKc_def]; ring
    have hKη : 0 < η * Kc := mul_pos hη hKc
    show (1 - η) * Kc ≤ -B * deriv Ψ (u y) ∧ -B * deriv Ψ (u y) ≤ (1 + η) * Kc
    rw [hdec]
    constructor <;> linarith [hBη, hBη', hKη]


/-- Theorem 7.9c(1), quantitative form: for every `ε₀ > 0`, eventually as `c → ∞`,
`T_c^{+1} - T_c^{-1} ≤ -2 / π² + ε₀`. -/
theorem sign_separation_eventually_le (P : SignSeparationPackage) :
    ∀ ε₀ > 0, ∀ᶠ c in atTop,
      P.Tpos c - P.Tneg c ≤ -(2 / π ^ 2) + ε₀ := by
  intro ε₀ hε₀
  let ε₁ : ℝ := min ε₀ (2 / π ^ 2) / 2
  have hε₁ : 0 < ε₁ := by positivity
  have hε₁_lt : ε₁ < 2 / π ^ 2 := by
    have : ε₁ ≤ (2 / π ^ 2) / 2 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
    linarith [show (0 : ℝ) < 2 / π ^ 2 by positivity]
  let δ : ℝ := 2 / π ^ 2 - ε₁
  have hδ : 0 < δ := sub_pos.mpr hε₁_lt
  have hb : (0 : ℝ) < π ^ 2 / 2 := by positivity
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp
    ((exp_linear_tail_tendsto hb).eventually (eventually_le_nhds (by positivity : 0 < ε₁ / (2 * (π ^ 2 / 2)))))
  let M : ℝ := max M₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  have htail_exp : ∫ y in Ioi M, y * Real.exp (-(π ^ 2 / 2) * y) ≤ ε₁ / (2 * (π ^ 2 / 2)) :=
    hM₀ M (le_max_left _ _)
  let err_budget : ℝ := ε₁ / (2 * (π ^ 2 / 2))
  have herr_pos : 0 < err_budget := by positivity
  let ηw : ℝ := err_budget / (2 * (δ + M + 1) ^ 2)
  have hηw : 0 < ηw := by positivity
  let ηp : ℝ := err_budget / (2 * (δ + M + 1) * (2 + δ + M) * (1 + ηw))
  have hηp : 0 < ηp := by positivity
  have herr_small : (δ + M) * ((δ + M) * ηw + ηp * (2 + δ + M) * (1 + ηw)) ≤ err_budget := by
    have h1 : (δ + M) * ((δ + M) * ηw) ≤ err_budget / 2 := by
      dsimp [ηw]
      have hdm : 0 ≤ δ + M := by positivity
      have hsq : (δ + M) ^ 2 ≤ (δ + M + 1) ^ 2 := by nlinarith
      calc (δ + M) * ((δ + M) * (err_budget / (2 * (δ + M + 1) ^ 2)))
          = ((δ + M) ^ 2 * err_budget) / ((δ + M + 1) ^ 2 * 2) := by ring
        _ = ((δ + M) ^ 2 / (δ + M + 1) ^ 2) * (err_budget / 2) :=
            (div_mul_div_comm ((δ + M) ^ 2) ((δ + M + 1) ^ 2) err_budget 2).symm
        _ ≤ 1 * (err_budget / 2) := by
            gcongr; exact (div_le_one (by positivity)).mpr hsq
        _ = err_budget / 2 := one_mul _
    have h2 : (δ + M) * (ηp * (2 + δ + M) * (1 + ηw)) ≤ err_budget / 2 := by
      dsimp [ηp]
      have hne1 : 2 + δ + M ≠ 0 := by positivity
      have hne2 : 1 + ηw ≠ 0 := by positivity
      have hne3 : δ + M + 1 ≠ 0 := by positivity
      calc (δ + M) * (err_budget / (2 * (δ + M + 1) * (2 + δ + M) * (1 + ηw)) * (2 + δ + M) * (1 + ηw))
          = ((δ + M) / (δ + M + 1)) * (err_budget / 2) := by
            field_simp [hne1, hne2, hne3]
        _ ≤ 1 * (err_budget / 2) := by
            gcongr; exact (div_le_one (by positivity)).mpr (by linarith)
        _ = err_budget / 2 := one_mul _
    linarith
  have hT_asymp_real : Tendsto (fun c : ℝ => P.Tneg c / c) atTop (𝓝 (1 / π ^ 2)) :=
    P.Tneg_asymp.congr' (Eventually.of_forall fun c => by
      dsimp [SignSeparationPackage.Tneg]; split_ifs <;> simp)
  have hw_unif := tendsto_rpow_ratio_exp hT_asymp_real hδ hM hηw
  have hlanger := P.langer_approx δ M ηp hδ hM hηp
  have hc_large : ∀ᶠ c in atTop, P.c₀ ≤ c ∧ 0 < c ∧ 1 / c ≤ ε₁ ∧ δ < P.Tneg c := by
    have hc_pos : ∀ᶠ c in atTop, P.c₀ ≤ c ∧ 0 < c := by
      filter_upwards [eventually_ge_atTop P.c₀, eventually_gt_atTop (0 : ℝ)] with c hc1 hc2
      exact ⟨hc1, hc2⟩
    have h1c : ∀ᶠ c in atTop, 1 / c ≤ ε₁ := by
      have ht : Tendsto (fun c : ℝ => 1 / c) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      exact ht.eventually (eventually_le_nhds hε₁)
    have hTgt : ∀ᶠ c in atTop, δ < P.Tneg c := by
      have ht : Tendsto (fun c : ℝ => P.Tneg c) atTop atTop := by
        have hmul : Tendsto (fun c : ℝ => (P.Tneg c / c) * c) atTop atTop :=
          Filter.Tendsto.pos_mul_atTop (by positivity : (0 : ℝ) < 1 / π ^ 2) hT_asymp_real tendsto_id
        refine hmul.congr' ?_
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc0
        rw [div_mul_cancel₀ _ hc0.ne']
      exact ht.eventually (eventually_gt_atTop δ)
    filter_upwards [hc_pos, h1c, hTgt] with c ⟨hc1, hc2⟩ h1c' hTgt'
    exact ⟨hc1, hc2, h1c', hTgt'⟩
  filter_upwards [hc_large, hw_unif, hlanger] with c ⟨hc_ge, hc0, h1c, hTgt⟩ hw_c hl_c
  have hc_ge' : P.c₀ ≤ c := hc_ge
  let Sneg := { T : ℝ | ∃ f, IsFeasible c (P.K c hc_ge') (-1) T f }
  have hSneg_ne : Sneg.Nonempty := P.neg_feasible c hc_ge'
  have hSneg_bdd : BddBelow Sneg := ⟨0, fun T ⟨_, hf⟩ => (feasible_threshold_pos hc0 hf).le⟩
  have hlt_inf : sInf Sneg < sInf Sneg + 1 / c := by linarith [one_div_pos.mpr hc0]
  obtain ⟨T, ⟨f, hf_feas⟩, hT_lt⟩ := exists_lt_of_csInf_lt hSneg_ne hlt_inf
  have hT_ge : hankelThreshold c (P.K c hc_ge') (-1) ≤ T := csInf_le hSneg_bdd ⟨f, hf_feas⟩
  have hT_le : T ≤ hankelThreshold c (P.K c hc_ge') (-1) + 1 / c := hT_lt.le
  obtain ⟨Q, Q', R, Kc, hKc, hdecomp, hR_bd, hQ'_cont, hQ_deriv, hQ'_bd⟩ :=
    hl_c hc_ge' T f hf_feas hT_ge hT_le
  have hTneg_eq : P.Tneg c = hankelThreshold c (P.K c hc_ge') (-1) := by
    dsimp [SignSeparationPackage.Tneg]; split_ifs; rfl
  have hTpos_eq : P.Tpos c = hankelThreshold c (P.K c hc_ge') 1 := by
    dsimp [SignSeparationPackage.Tpos]; split_ifs; rfl
  have hT_gt_δ : δ < T := by linarith [hTneg_eq, hT_ge, hTgt]
  have hw_c' : ∀ h ∈ Icc (0 : ℝ) δ, ∀ y ∈ Icc (-h) M,
      |((T + y) / (T - h)) ^ (-(c / 2)) - Real.exp (-(π ^ 2 / 2) * (y + h))| ≤ ηw := fun h hh y hy =>
    (hw_c T ⟨by linarith [hTneg_eq, hT_ge], by linarith [hTneg_eq, hT_le]⟩ h hh y hy).2.2
  have hinter_nonneg : ∀ h ∈ Icc (0 : ℝ) δ, 0 ≤ intertwiner c f (T - h) :=
    langer_intertwiner_pos_near_thresh hc0 hδ hM hKc hε₁ (le_refl δ)
      hf_feas.eigenfn.cont (intertwiner_integrable hc0 hf_feas.eigenfn)
      hf_feas.tail_nonneg hT_gt_δ hdecomp hR_bd hQ'_cont hQ_deriv hQ'_bd
      hw_c' htail_exp herr_small
  have hg_feas : IsFeasible c (P.K c hc_ge') 1 (T - δ) (intertwiner c f) := by
    have h1 := intertwiner_feasible hc0 hf_feas
    refine ⟨h1.eigenfn, h1.nonzero, h1.origin_sign, fun Δ hΔ => ?_⟩
    rcases le_or_gt T Δ with hTΔ | hΔT
    · exact h1.tail_nonneg Δ hTΔ
    · have hhmem : T - Δ ∈ Icc (0 : ℝ) δ := ⟨by linarith, by linarith⟩
      simpa [sub_sub_cancel] using hinter_nonneg (T - Δ) hhmem
  have hSpos_bdd : BddBelow { T : ℝ | ∃ f, IsFeasible c (P.K c hc_ge') 1 T f } :=
    ⟨0, fun _ ⟨_, hf⟩ => (feasible_threshold_pos hc0 hf).le⟩
  have hTpos_le : hankelThreshold c (P.K c hc_ge') 1 ≤ T - δ := csInf_le hSpos_bdd ⟨intertwiner c f, hg_feas⟩
  have hε₁_le : ε₁ ≤ ε₀ / 2 := (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
  linarith [hTpos_eq, hTneg_eq]

/-- Theorem 7.9c(1), `limsup` form: under upper/lower coboundedness of `T_c^{+1} - T_c^{-1}`,
`limsup_{c → ∞} (T_c^{+1} - T_c^{-1}) ≤ -2 / π²`. -/
theorem sign_separation_limsup (P : SignSeparationPackage)
    (hcob : Filter.IsCoboundedUnder (· ≤ ·) atTop (fun c => P.Tpos c - P.Tneg c)) :
    Filter.limsup (fun c => P.Tpos c - P.Tneg c) atTop ≤ -(2 / π ^ 2) := by
  have hbdd : Filter.IsBoundedUnder (· ≤ ·) atTop (fun c => P.Tpos c - P.Tneg c) :=
    ⟨-(2 / π ^ 2) + 1, (sign_separation_eventually_le P 1 one_pos).mono fun c hc => hc⟩
  rw [Filter.limsup_le_iff hcob hbdd]
  intro y hy
  let ε₀ : ℝ := (y - (-(2 / π ^ 2))) / 2
  have hε₀ : 0 < ε₀ := half_pos (sub_pos.mpr hy)
  exact (sign_separation_eventually_le P ε₀ hε₀).mono fun c hc => by dsimp [ε₀] at hc; linarith

/-- Theorem 7.9c(2), integer dimensions `d → ∞`: for `A_ε(d) = √(2 T_{d/2}^ε)`,
eventually `(1/2)(A_+(d)² - A_-(d)²) ≤ -2 / π² + ε₀` and `√d (A_+(d) - A_-(d)) ≤ -2 / π + ε₀`. -/
theorem sign_separation_radii (P : SignSeparationPackage) :
    let Apos : ℕ → ℝ := fun d => Real.sqrt (2 * P.Tpos ((d : ℝ) / 2))
    let Aneg : ℕ → ℝ := fun d => Real.sqrt (2 * P.Tneg ((d : ℝ) / 2))
    (∀ ε₀ > 0, ∀ᶠ d : ℕ in atTop,
      (1 / 2 : ℝ) * (Apos d ^ 2 - Aneg d ^ 2) ≤ -(2 / π ^ 2) + ε₀) ∧
    (∀ ε₀ > 0, ∀ᶠ d : ℕ in atTop,
      Real.sqrt d * (Apos d - Aneg d) ≤ -(2 / π) + ε₀) := by
  intro Apos Aneg
  have hc_tend : Tendsto (fun d : ℕ => (d : ℝ) / 2) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num : (0 : ℝ) < 2)
  have hT_asymp_real : Tendsto (fun c : ℝ => P.Tneg c / c) atTop (𝓝 (1 / π ^ 2)) :=
    P.Tneg_asymp.congr' (Eventually.of_forall fun c => by
      dsimp [SignSeparationPackage.Tneg]; split_ifs <;> simp)
  have hT_nn : ∀ᶠ d : ℕ in atTop, 0 ≤ P.Tpos ((d : ℝ) / 2) ∧ 0 < P.Tneg ((d : ℝ) / 2) ∧
      P.Tpos ((d : ℝ) / 2) ≤ P.Tneg ((d : ℝ) / 2) := by
    have hTasymp : Tendsto (fun d : ℕ => P.Tneg ((d : ℝ) / 2) / ((d : ℝ) / 2)) atTop (𝓝 (1 / π ^ 2)) :=
      hT_asymp_real.comp hc_tend
    have hlt1 : (1 / (2 * π ^ 2) : ℝ) < 1 / π ^ 2 := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith [Real.pi_pos]
    have hd_large : ∀ᶠ d : ℕ in atTop, P.c₀ ≤ (d : ℝ) / 2 ∧ (0 : ℝ) < (d : ℝ) / 2 ∧
        0 < P.Tneg ((d : ℝ) / 2) / ((d : ℝ) / 2) := by
      filter_upwards [hc_tend.eventually (eventually_ge_atTop P.c₀),
        hc_tend.eventually (eventually_gt_atTop (0 : ℝ)),
        hTasymp.eventually (eventually_gt_nhds hlt1)] with
        d hc1 hc2 htr
      exact ⟨hc1, hc2, lt_trans (by positivity : (0 : ℝ) < 1 / (2 * π ^ 2)) htr⟩
    refine hd_large.mono fun d ⟨hc1, hc2, htr⟩ => ?_
    have hpos_nn : 0 ≤ P.Tpos ((d : ℝ) / 2) := by
      dsimp [SignSeparationPackage.Tpos]
      split_ifs
      exact Real.sInf_nonneg fun _ ⟨_, hf⟩ => (feasible_threshold_pos hc2 hf).le
    have hneg_pos : 0 < P.Tneg ((d : ℝ) / 2) := by
      have := mul_pos htr hc2
      rwa [div_mul_cancel₀ _ hc2.ne'] at this
    have hle : P.Tpos ((d : ℝ) / 2) ≤ P.Tneg ((d : ℝ) / 2) := by
      dsimp [SignSeparationPackage.Tpos, SignSeparationPackage.Tneg]
      split_ifs
      exact threshold_pos_le_neg hc2 (P.neg_feasible _ hc1)
    exact ⟨hpos_nn, hneg_pos, hle⟩
  have h1 : ∀ ε₀ > 0, ∀ᶠ d : ℕ in atTop,
      (1 / 2 : ℝ) * (Apos d ^ 2 - Aneg d ^ 2) ≤ -(2 / π ^ 2) + ε₀ := by
    intro ε₀ hε₀
    filter_upwards [hT_nn, hc_tend.eventually (sign_separation_eventually_le P ε₀ hε₀)] with
      d ⟨hp_nn, hn_pos, _⟩ hdiff
    have hsq1 : Apos d ^ 2 = 2 * P.Tpos ((d : ℝ) / 2) := Real.sq_sqrt (by linarith)
    have hsq2 : Aneg d ^ 2 = 2 * P.Tneg ((d : ℝ) / 2) := Real.sq_sqrt (by linarith)
    rw [hsq1, hsq2]
    linarith
  refine ⟨h1, ?_⟩
  intro ε₀ hε₀
  let ε₁ : ℝ := min (1 / π ^ 2) (ε₀ / (2 * π))
  have hε₁ : 0 < ε₁ := by positivity
  have hnum_neg : -(2 / π ^ 2) + ε₁ ≤ -(1 / π ^ 2) := by
    have : ε₁ ≤ 1 / π ^ 2 := min_le_left _ _
    linarith [show -(2 / π ^ 2) + 1 / π ^ 2 = -(1 / π ^ 2) by ring]
  have hden_lim : Tendsto (fun d : ℕ => Aneg d / Real.sqrt d) atTop (𝓝 (1 / π)) := by
    have hsq_lim : Tendsto (fun d : ℕ => P.Tneg ((d : ℝ) / 2) / ((d : ℝ) / 2)) atTop (𝓝 (1 / π ^ 2)) :=
      hT_asymp_real.comp hc_tend
    have hr := (Real.continuous_sqrt.continuousAt.tendsto.comp hsq_lim)
    rw [Real.sqrt_div zero_le_one, Real.sqrt_one, Real.sqrt_sq Real.pi_pos.le] at hr
    refine hr.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℕ), hT_nn] with d (hd : 0 < d) ⟨_, hn_pos, _⟩
    have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr hd
    dsimp [Aneg]
    rw [← Real.sqrt_div (by linarith : 0 ≤ 2 * P.Tneg ((d : ℝ) / 2))]
    congr 1; ring
  have hbound_lim : Tendsto (fun d : ℕ => (-(2 / π ^ 2) + ε₁) / (Aneg d / Real.sqrt d))
      atTop (𝓝 ((-(2 / π ^ 2) + ε₁) / (1 / π))) :=
    tendsto_const_nhds.div hden_lim (by positivity : (1 / π : ℝ) ≠ 0)
  have hlim_lt : (-(2 / π ^ 2) + ε₁) / (1 / π) < -(2 / π) + ε₀ := by
    have hε₁_le : ε₁ ≤ ε₀ / (2 * π) := min_le_right _ _
    calc (-(2 / π ^ 2) + ε₁) / (1 / π)
        = -(2 / π) + π * ε₁ := by field_simp [Real.pi_pos.ne']
      _ ≤ -(2 / π) + π * (ε₀ / (2 * π)) := by gcongr
      _ = -(2 / π) + ε₀ / 2 := by field_simp [Real.pi_pos.ne']
      _ < -(2 / π) + ε₀ := by linarith
  have hlt2 : (1 / (2 * π) : ℝ) < 1 / π := by
    rw [div_lt_div_iff₀ (by positivity) Real.pi_pos]
    linarith [Real.pi_pos]
  filter_upwards [hT_nn, h1 ε₁ hε₁, hden_lim.eventually (eventually_gt_nhds hlt2),
    hbound_lim.eventually (eventually_lt_nhds hlim_lt)] with
    d ⟨hp_nn, hn_pos, hle⟩ hX hden_pos hbound
  have hsq1 : Apos d ^ 2 = 2 * P.Tpos ((d : ℝ) / 2) := Real.sq_sqrt (by linarith)
  have hsq2 : Aneg d ^ 2 = 2 * P.Tneg ((d : ℝ) / 2) := Real.sq_sqrt (by linarith)
  have hX' : P.Tpos ((d : ℝ) / 2) - P.Tneg ((d : ℝ) / 2) ≤ -(2 / π ^ 2) + ε₁ := by linarith
  have hAp_le : Apos d ≤ Aneg d := Real.sqrt_le_sqrt (by linarith)
  have hAp_nn : 0 ≤ Apos d := Real.sqrt_nonneg _
  have hAn_pos : 0 < Aneg d := Real.sqrt_pos.mpr (by linarith)
  have hd_pos : 0 < Real.sqrt d := by
    by_contra hd0
    have : Real.sqrt d = 0 := le_antisymm (not_lt.mp hd0) (Real.sqrt_nonneg _)
    rw [this, div_zero] at hden_pos
    linarith [show (0 : ℝ) < 1 / (2 * π) by positivity]
  have hsum_pos : 0 < Apos d + Aneg d := by linarith
  have hsum_le : Apos d + Aneg d ≤ 2 * Aneg d := by linarith
  have hdiff_neg : Apos d ^ 2 - Aneg d ^ 2 ≤ 2 * (-(2 / π ^ 2) + ε₁) := by linarith
  have hnum_neg' : 2 * (-(2 / π ^ 2) + ε₁) ≤ 0 := by
    linarith [hnum_neg, show (0 : ℝ) ≤ 1 / π ^ 2 by positivity]
  calc Real.sqrt d * (Apos d - Aneg d)
      = Real.sqrt d * ((Apos d ^ 2 - Aneg d ^ 2) / (Apos d + Aneg d)) := by
          have : Apos d ^ 2 - Aneg d ^ 2 = (Apos d - Aneg d) * (Apos d + Aneg d) := by ring
          rw [this, mul_div_cancel_right₀ _ hsum_pos.ne']
    _ ≤ Real.sqrt d * ((2 * (-(2 / π ^ 2) + ε₁)) / (Apos d + Aneg d)) := by
          gcongr
    _ ≤ Real.sqrt d * ((2 * (-(2 / π ^ 2) + ε₁)) / (2 * Aneg d)) := by
          have hdiv_le : 1 / (2 * Aneg d) ≤ 1 / (Apos d + Aneg d) :=
            one_div_le_one_div_of_le hsum_pos hsum_le
          have := mul_le_mul_of_nonpos_left hdiv_le hnum_neg'
          rw [mul_one_div, mul_one_div] at this
          exact mul_le_mul_of_nonneg_left this hd_pos.le
    _ = (-(2 / π ^ 2) + ε₁) / (Aneg d / Real.sqrt d) := by
          field_simp [hd_pos.ne', hAn_pos.ne']
    _ ≤ -(2 / π) + ε₀ := hbound.le

/-- Theorem 7.9c(3): if `T_c^ε = c / π² + a₁ c^{1/3} + κ_ε + o(1)` for both `ε = ±1`, then
`κ_{+1} - κ_{-1} ≤ -2 / π²`. -/
theorem sign_separation_kappa (P : SignSeparationPackage) {a1 κpos κneg : ℝ}
    (hpos : Tendsto (fun c : ℝ => P.Tpos c - c / π ^ 2 - a1 * c ^ (1 / 3 : ℝ) - κpos) atTop (𝓝 0))
    (hneg : Tendsto (fun c : ℝ => P.Tneg c - c / π ^ 2 - a1 * c ^ (1 / 3 : ℝ) - κneg) atTop (𝓝 0)) :
    κpos - κneg ≤ -(2 / π ^ 2) := by
  have hdiff : Tendsto (fun c : ℝ => P.Tpos c - P.Tneg c) atTop (𝓝 (κpos - κneg)) := by
    have hsub := hpos.sub hneg
    rw [sub_zero] at hsub
    have hadd := hsub.add_const (κpos - κneg)
    rw [zero_add] at hadd
    refine hadd.congr' (Eventually.of_forall fun c => ?_)
    ring
  refine le_of_forall_pos_le_add fun ε₀ hε₀ => ?_
  exact le_of_tendsto hdiff (sign_separation_eventually_le P ε₀ hε₀)

/-- Standalone Langer profile package on `(c, T_c, f_c)` isolating the exponential-tail positivity
step of Theorem 7.9c for clean non-vacuity checking. -/
structure LangerProfileFamily where
  c₀ : ℝ
  hc₀ : 0 < c₀
  T : ℝ → ℝ
  f : ℝ → ℝ → ℝ
  f_cont : ∀ c ≥ c₀, ContinuousOn (f c) (Ici 0)
  f_rpow_int : ∀ c ≥ c₀, IntegrableOn (fun s => |f c s| * s ^ (c / 2 - 1)) (Ioi 0)
  f_tail_nonneg : ∀ c ≥ c₀, ∀ Δ ≥ T c, 0 ≤ f c Δ
  T_asymp : Tendsto (fun c => T c / c) atTop (𝓝 (1 / π ^ 2))
  langer_approx : ∀ (δ M η : ℝ), 0 < δ → 0 ≤ M → 0 < η →
    ∀ᶠ c in atTop, ∀ _ : c₀ ≤ c,
      ∃ (Q Q' R : ℝ → ℝ) (Kc : ℝ),
        0 < Kc ∧
        (∀ y ∈ Icc (-δ) M, f c (T c + y) * hankelRho0 c (T c + y) = Q y + R y) ∧
        (∀ y ∈ Icc (-δ) M, |R y| ≤ η * Kc) ∧
        ContinuousOn Q' (Icc (-δ) M) ∧
        (∀ y ∈ Icc (-δ) M, HasDerivAt Q (Q' y) y) ∧
        (∀ y ∈ Icc (-δ) M, (1 - η) * Kc ≤ Q' y ∧ Q' y ≤ (1 + η) * Kc)

/-- For any `LangerProfileFamily` and any `0 < δ < 2 / π²`, eventually as `c → ∞`,
`0 ≤ intertwiner c (f c) Δ` for all `Δ ≥ T c - δ`. -/
theorem langerProfileFamily_tail_nonneg (L : LangerProfileFamily) {δ : ℝ}
    (hδ : 0 < δ) (hδ_up : δ < 2 / π ^ 2) :
    ∀ᶠ c in atTop, c ≥ L.c₀ ∧ ∀ Δ ≥ L.T c - δ, 0 ≤ intertwiner c (L.f c) Δ := by
  let ε₀ : ℝ := 2 / π ^ 2 - δ
  have hε₀ : 0 < ε₀ := sub_pos.mpr hδ_up
  have hb : (0 : ℝ) < π ^ 2 / 2 := by positivity
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp
    ((exp_linear_tail_tendsto hb).eventually (eventually_le_nhds (by positivity : 0 < ε₀ / (2 * (π ^ 2 / 2)))))
  let M : ℝ := max M₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  have htail_exp : ∫ y in Ioi M, y * Real.exp (-(π ^ 2 / 2) * y) ≤ ε₀ / (2 * (π ^ 2 / 2)) :=
    hM₀ M (le_max_left _ _)
  let err_budget : ℝ := ε₀ / (2 * (π ^ 2 / 2))
  have herr_pos : 0 < err_budget := by positivity
  let ηw : ℝ := err_budget / (2 * (δ + M + 1) ^ 2)
  have hηw : 0 < ηw := by positivity
  let ηp : ℝ := err_budget / (2 * (δ + M + 1) * (2 + δ + M) * (1 + ηw))
  have hηp : 0 < ηp := by positivity
  have herr_small : (δ + M) * ((δ + M) * ηw + ηp * (2 + δ + M) * (1 + ηw)) ≤ err_budget := by
    have h1 : (δ + M) * ((δ + M) * ηw) ≤ err_budget / 2 := by
      dsimp [ηw]
      have hdm : 0 ≤ δ + M := by positivity
      have hsq : (δ + M) ^ 2 ≤ (δ + M + 1) ^ 2 := by nlinarith
      calc (δ + M) * ((δ + M) * (err_budget / (2 * (δ + M + 1) ^ 2)))
          = ((δ + M) ^ 2 * err_budget) / ((δ + M + 1) ^ 2 * 2) := by ring
        _ = ((δ + M) ^ 2 / (δ + M + 1) ^ 2) * (err_budget / 2) :=
            (div_mul_div_comm ((δ + M) ^ 2) ((δ + M + 1) ^ 2) err_budget 2).symm
        _ ≤ 1 * (err_budget / 2) := by gcongr; exact (div_le_one (by positivity)).mpr hsq
        _ = err_budget / 2 := one_mul _
    have h2 : (δ + M) * (ηp * (2 + δ + M) * (1 + ηw)) ≤ err_budget / 2 := by
      dsimp [ηp]
      calc (δ + M) * (err_budget / (2 * (δ + M + 1) * (2 + δ + M) * (1 + ηw)) * (2 + δ + M) * (1 + ηw))
          = ((δ + M) / (δ + M + 1)) * (err_budget / 2) := by
            field_simp [(by positivity : 2 + δ + M ≠ 0), (by positivity : 1 + ηw ≠ 0),
              (by positivity : δ + M + 1 ≠ 0)]
        _ ≤ 1 * (err_budget / 2) := by gcongr; exact (div_le_one (by positivity)).mpr (by linarith)
        _ = err_budget / 2 := one_mul _
    linarith
  have hT_tend : Tendsto L.T atTop atTop := by
    have hmul := Filter.Tendsto.pos_mul_atTop (by positivity : (0 : ℝ) < 1 / π ^ 2) L.T_asymp tendsto_id
    refine hmul.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc0
    rw [id_eq, div_mul_cancel₀ _ hc0.ne']
  have hw_unif := tendsto_rpow_ratio_exp L.T_asymp hδ hM hηw
  have hlanger := L.langer_approx δ M ηp hδ hM hηp
  filter_upwards [eventually_ge_atTop L.c₀, eventually_gt_atTop (0 : ℝ),
    hT_tend.eventually (eventually_gt_atTop δ), hw_unif, hlanger] with
    c hc_ge hc0 hTgt hw_c hl_c
  refine ⟨hc_ge, fun Δ hΔ => ?_⟩
  rcases le_or_gt (L.T c) Δ with hTΔ | hΔT
  · have hΔpos : 0 < Δ := hδ.trans (hTgt.trans_le hTΔ)
    unfold intertwiner
    simp only [hΔpos, ↓reduceIte]
    refine mul_nonneg (Real.rpow_nonneg hΔpos.le _) (setIntegral_nonneg measurableSet_Ioi fun s hs => ?_)
    exact mul_nonneg (L.f_tail_nonneg c hc_ge s (hTΔ.trans hs.le)) (Real.rpow_nonneg (hΔpos.trans hs).le _)
  · obtain ⟨Q, Q', R, Kc, hKc, hdecomp, hR_bd, hQ'_cont, hQ_deriv, hQ'_bd⟩ := hl_c hc_ge
    have hw_c' : ∀ h ∈ Icc (0 : ℝ) δ, ∀ y ∈ Icc (-h) M,
        |((L.T c + y) / (L.T c - h)) ^ (-(c / 2)) - Real.exp (-(π ^ 2 / 2) * (y + h))| ≤ ηw := fun h hh y hy =>
      (hw_c (L.T c) ⟨le_rfl, by linarith [one_div_pos.mpr hc0]⟩ h hh y hy).2.2
    have hres := langer_intertwiner_pos_near_thresh hc0 hδ hM hKc hε₀ (by dsimp [ε₀]; linarith)
      (L.f_cont c hc_ge) (L.f_rpow_int c hc_ge) (L.f_tail_nonneg c hc_ge) hTgt
      hdecomp hR_bd hQ'_cont hQ_deriv hQ'_bd hw_c' htail_exp herr_small
      (L.T c - Δ) ⟨by linarith, by linarith⟩
    simpa [sub_sub_cancel] using hres

/-- Explicit unconditional non-vacuity witness for `LangerProfileFamily`, realized by the
ramp-smoothed profile `f_c(Δ) = max 0 (min 1 (Δ - 1)) * (Δ - c/π²) * exp(-Δ/c) / ρ₀(c, max Δ 1)`. -/
theorem langerProfileFamily_nonvacuous : Nonempty LangerProfileFamily := by
  let T : ℝ → ℝ := fun c => c / π ^ 2
  let f : ℝ → ℝ → ℝ := fun c Δ =>
    max 0 (min 1 (Δ - 1)) * (Δ - T c) * Real.exp (-Δ / c) / hankelRho0 c (max Δ 1)
  have hKc_pos : 0 < Real.exp (-(1 / π ^ 2)) := Real.exp_pos _
  refine ⟨⟨100, by norm_num, T, f, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro c (hc : 100 ≤ c)
    have hc0 : 0 < c := by linarith
    have hnum : Continuous (fun Δ : ℝ => max 0 (min 1 (Δ - 1)) * (Δ - T c) * Real.exp (-Δ / c)) :=
      ((continuous_const.max (continuous_const.min (continuous_id.sub continuous_const))).mul
        (continuous_id.sub continuous_const)).mul (Real.continuous_exp.comp (continuous_neg.div_const c))
    have hden : Continuous (fun Δ : ℝ => hankelRho0 c (max Δ 1)) := by
      unfold hankelRho0
      exact continuous_const.mul ((Continuous.rpow_const (continuous_id.max continuous_const)
        fun Δ => Or.inl (lt_of_lt_of_le zero_lt_one (le_max_right Δ 1)).ne'))
    exact (hnum.div hden fun Δ => (hankelRho0_pos hc0 (lt_of_lt_of_le zero_lt_one (le_max_right Δ 1))).ne').continuousOn
  · intro c (hc : 100 ≤ c)
    have hc0 : 0 < c := by linarith
    have hsm : AEStronglyMeasurable (fun s : ℝ => |f c s| * s ^ (c / 2 - 1)) (volume.restrict (Ioi 0)) := by
      have hnum : Continuous (fun s : ℝ => max 0 (min 1 (s - 1)) * (s - T c) * Real.exp (-s / c)) :=
        ((continuous_const.max (continuous_const.min (continuous_id.sub continuous_const))).mul
          (continuous_id.sub continuous_const)).mul (Real.continuous_exp.comp (continuous_neg.div_const c))
      have hden : Continuous (fun s : ℝ => hankelRho0 c (max s 1)) := by
        unfold hankelRho0
        exact continuous_const.mul ((Continuous.rpow_const (continuous_id.max continuous_const)
          fun s => Or.inl (lt_of_lt_of_le zero_lt_one (le_max_right s 1)).ne'))
      have hf_cont : Continuous (f c) :=
        hnum.div hden fun s => (hankelRho0_pos hc0 (lt_of_lt_of_le zero_lt_one (le_max_right s 1))).ne'
      exact ((hf_cont.abs.continuousOn.mono Ioi_subset_Ici_self).mul
        (ContinuousOn.rpow_const continuousOn_id fun s hs => Or.inl (ne_of_gt (mem_Ioi.mp hs)))).aestronglyMeasurable
        measurableSet_Ioi
    have h1 : IntegrableOn (fun s : ℝ => |f c s| * s ^ (c / 2 - 1)) (Ioc 0 1) := by
      refine (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Ioc 0 1)).congr_fun ?_ measurableSet_Ioc
      intro s (hs : s ∈ Ioc 0 1)
      have hmin : min 1 (s - 1) ≤ 0 := min_le_of_right_le (by linarith [hs.2])
      dsimp [f]
      rw [max_eq_left hmin, zero_mul, zero_mul, zero_div, abs_zero, zero_mul]
    have h2 : IntegrableOn (fun s : ℝ => |f c s| * s ^ (c / 2 - 1)) (Ioi 1) := by
      let C0 : ℝ := Real.Gamma c / (2 * π) ^ c
      have hC0 : 0 ≤ C0 := (div_pos (Real.Gamma_pos_of_pos hc0) (Real.rpow_pos_of_pos (by positivity) _)).le
      have hint1 : IntegrableOn (fun s : ℝ => C0 * (s ^ (1 : ℝ) * Real.exp (-(1 / c) * s))) (Ioi 1) :=
        ((integrableOn_rpow_mul_exp_neg_mul_Ioi (by norm_num : (-1 : ℝ) < 1) (one_div_pos.mpr hc0)).mono_set
          (Ioi_subset_Ioi zero_le_one)).const_mul C0
      have hint0 : IntegrableOn (fun s : ℝ => (C0 * T c) * (s ^ (0 : ℝ) * Real.exp (-(1 / c) * s))) (Ioi 1) :=
        ((integrableOn_rpow_mul_exp_neg_mul_Ioi (by norm_num : (-1 : ℝ) < 0) (one_div_pos.mpr hc0)).mono_set
          (Ioi_subset_Ioi zero_le_one)).const_mul (C0 * T c)
      refine (hint1.add hint0).mono' (hsm.mono_measure (Measure.restrict_mono (Ioi_subset_Ioi zero_le_one) le_rfl))
        ((ae_restrict_mem measurableSet_Ioi).mono fun s (hs : 1 < s) => ?_)
      have hmax_s : max s 1 = s := max_eq_left hs.le
      have hramp : |max 0 (min 1 (s - 1))| ≤ 1 := by
        rw [abs_of_nonneg (le_max_left _ _)]
        exact max_le zero_le_one (min_le_left _ _)
      have hT_nn : 0 ≤ T c := by dsimp [T]; positivity
      have hlin : |s - T c| ≤ s + T c := (abs_sub _ _).trans_eq (by
        rw [abs_of_pos (by linarith), abs_of_nonneg hT_nn])
      have hden_pos : 0 < hankelRho0 c s := hankelRho0_pos hc0 (by linarith)
      have hpow_le : s ^ (-(c / 2)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hs.le (by linarith)
      have hrho : (hankelRho0 c s)⁻¹ * s ^ (c / 2 - 1) = C0 * s ^ (-(c / 2)) := by
        have hp : (s ^ (c - 1))⁻¹ * s ^ (c / 2 - 1) = s ^ (-(c / 2)) := by
          rw [← Real.rpow_neg (by linarith), ← Real.rpow_add (by linarith)]; congr 1; ring
        calc (hankelRho0 c s)⁻¹ * s ^ (c / 2 - 1)
            = ((2 * π) ^ c / Real.Gamma c * s ^ (c - 1))⁻¹ * s ^ (c / 2 - 1) := by
                unfold hankelRho0; rfl
          _ = C0 * ((s ^ (c - 1))⁻¹ * s ^ (c / 2 - 1)) := by
                dsimp [C0]; rw [mul_inv, inv_div]; ring
          _ = C0 * s ^ (-(c / 2)) := by rw [hp]
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (by linarith) _))]
      dsimp [f]
      rw [hmax_s, abs_div, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos hden_pos,
        show -s / c = -(1 / c) * s by ring]
      calc (|max 0 (min 1 (s - 1))| * |s - T c| * Real.exp (-(1 / c) * s) / hankelRho0 c s) * s ^ (c / 2 - 1)
          = |max 0 (min 1 (s - 1))| * |s - T c| * Real.exp (-(1 / c) * s) *
              ((hankelRho0 c s)⁻¹ * s ^ (c / 2 - 1)) := by ring
        _ = |max 0 (min 1 (s - 1))| * |s - T c| * Real.exp (-(1 / c) * s) * (C0 * s ^ (-(c / 2))) := by
            rw [hrho]
        _ ≤ 1 * (s + T c) * Real.exp (-(1 / c) * s) * (C0 * 1) := by
            gcongr
        _ = C0 * (s ^ (1 : ℝ) * Real.exp (-(1 / c) * s)) +
              (C0 * T c) * (s ^ (0 : ℝ) * Real.exp (-(1 / c) * s)) := by
            rw [Real.rpow_one, Real.rpow_zero]; ring
    rw [← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ)]
    exact h1.union h2
  · intro c (hc : 100 ≤ c) Δ hΔ
    have hc0 : 0 < c := by linarith
    have hT2 : 2 ≤ T c := by
      dsimp [T]
      have : (2 : ℝ) * π ^ 2 ≤ 100 := by
        have hpi4 : π ^ 2 ≤ 16 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
        linarith
      rw [le_div_iff₀ (sq_pos_of_pos Real.pi_pos)]
      linarith
    have hΔ1 : 1 ≤ max Δ 1 := le_max_right _ _
    dsimp [f]
    exact div_nonneg (mul_nonneg (mul_nonneg (le_max_left _ _) (sub_nonneg.mpr hΔ)) (Real.exp_pos _).le)
      (hankelRho0_nonneg hc0 (le_trans zero_le_one hΔ1))
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc0
    dsimp [T]; field_simp [hc0.ne']
  · intro δ M η hδ hM hη
    let B : ℝ := δ + M
    have hB : 0 ≤ B := by positivity
    let η' : ℝ := min 1 (η / 2)
    have hη' : 0 < η' := by positivity
    have hη'_le1 : η' ≤ 1 := min_le_left _ _
    have hη'_le_half : 2 * η' ≤ η := by linarith [min_le_right (1 : ℝ) (η / 2)]
    have hc_large : ∀ᶠ c in atTop,
        π ^ 2 * (2 + δ) ≤ c ∧ B + 1 ≤ c ∧ (B + 1) / c ≤ η' / 2 := by
      have h1 : ∀ᶠ c in atTop, (B + 1) / c ≤ η' / 2 :=
        (tendsto_const_nhds.div_atTop tendsto_id).eventually (eventually_le_nhds (by positivity : 0 < η' / 2))
      filter_upwards [eventually_ge_atTop (π ^ 2 * (2 + δ)), eventually_ge_atTop (B + 1), h1] with c h2δ hB1 hdiv
      exact ⟨h2δ, hB1, hdiv⟩
    filter_upwards [hc_large] with c ⟨h2δ, _hB1, hdiv⟩ hc_ge
    have hc0 : 0 < c := by linarith
    let Kc : ℝ := Real.exp (-(1 / π ^ 2))
    have hKc_pos : 0 < Kc := Real.exp_pos _
    let Q : ℝ → ℝ := fun y => Kc * (y * Real.exp (-y / c))
    let Q' : ℝ → ℝ := fun y => Kc * ((1 - y / c) * Real.exp (-y / c))
    refine ⟨Q, Q', fun _ => 0, Kc, hKc_pos, ?_, ?_, ?_, ?_, ?_⟩
    · intro y hy
      have hTy2 : 2 ≤ T c + y := by
        dsimp [T]
        have : π ^ 2 * (2 + δ) ≤ c := h2δ
        have hle : 2 + δ ≤ c / π ^ 2 := (le_div_iff₀ (sq_pos_of_pos Real.pi_pos)).mpr (by linarith)
        linarith [hy.1]
      have hmin1 : max 0 (min 1 (T c + y - 1)) = 1 := by
        rw [min_eq_left (by linarith), max_eq_right zero_le_one]
      have hmax1 : max (T c + y) 1 = T c + y := max_eq_left (by linarith)
      have hrho_pos : hankelRho0 c (T c + y) ≠ 0 := (hankelRho0_pos hc0 (by linarith)).ne'
      dsimp [f, Q, Kc, T]
      rw [hmin1, hmax1, one_mul, div_mul_cancel₀ _ hrho_pos]
      rw [show -(c / π ^ 2 + y) / c = -(1 / π ^ 2) + (-y / c) by field_simp [hc0.ne']; ring, Real.exp_add]
      ring
    · intro y _; rw [abs_zero]; exact mul_nonneg hη.le hKc_pos.le
    · dsimp [Q']; fun_prop
    · intro y _
      have hd1 : HasDerivAt (fun x : ℝ => x * Real.exp (-x / c)) ((1 - y / c) * Real.exp (-y / c)) y := by
        have he : HasDerivAt (fun x : ℝ => Real.exp (-x / c)) (-(1 / c) * Real.exp (-y / c)) y := by
          have := ((hasDerivAt_neg y).div_const c).exp
          exact this.congr_deriv (by ring)
        exact ((hasDerivAt_id' y).mul he).congr_deriv (by ring)
      exact hd1.const_mul Kc
    · intro y hy
      have hy_abs : |y| ≤ B := abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
      have hyc : |y / c| ≤ η' / 2 := by
        rw [abs_div, abs_of_pos hc0]
        calc |y| / c ≤ B / c := div_le_div_of_nonneg_right hy_abs hc0.le
          _ ≤ (B + 1) / c := div_le_div_of_nonneg_right (by linarith) hc0.le
          _ ≤ η' / 2 := hdiv
      have huc : |-y / c| ≤ η' / 2 := by
        simpa only [neg_div, abs_neg] using hyc
      have hexp_sub : |Real.exp (-y / c) - 1| ≤ η' := by
        rcases le_or_gt 0 (-y / c) with hpos | hneg
        · have h1 := Real.add_one_le_exp (-(-y / c))
          rw [Real.exp_neg] at h1
          have hinv : (1 - (-y / c)) * Real.exp (-y / c) ≤ 1 := by
            have := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-y / c)).le
            rw [inv_mul_cancel₀ (Real.exp_pos (-y / c)).ne'] at this
            linarith
          have hu_le_half : -y / c ≤ 1 / 2 := by linarith [(abs_le.mp huc).2]
          have hexp_le2 : Real.exp (-y / c) ≤ 2 := by
            have : (1 / 2 : ℝ) * Real.exp (-y / c) ≤ (1 - (-y / c)) * Real.exp (-y / c) :=
              mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos (-y / c)).le
            linarith
          have hexp_ge1 : 1 ≤ Real.exp (-y / c) := Real.one_le_exp hpos
          have hu_le_eta : -y / c ≤ η' / 2 := (abs_le.mp huc).2
          have hsub_le : Real.exp (-y / c) - 1 ≤ η' := by nlinarith
          rw [abs_of_nonneg (sub_nonneg.mpr hexp_ge1)]
          exact hsub_le
        · have h1 := Real.add_one_le_exp (-y / c)
          have hu_ge : -(η' / 2) ≤ -y / c := (abs_le.mp huc).1
          have hexp_le1 : Real.exp (-y / c) ≤ 1 := Real.exp_le_one_iff.mpr hneg.le
          exact abs_le.mpr ⟨by linarith, by linarith⟩
      have hexp_le2 : Real.exp (-y / c) ≤ 2 := by
        linarith [(abs_le.mp hexp_sub).2, hη'_le1]
      have hprod_sub : |(1 - y / c) * Real.exp (-y / c) - 1| ≤ η := by
        have hid : (1 - y / c) * Real.exp (-y / c) - 1 =
            (Real.exp (-y / c) - 1) - (y / c) * Real.exp (-y / c) := by ring
        rw [hid]
        calc |(Real.exp (-y / c) - 1) - (y / c) * Real.exp (-y / c)|
            ≤ |Real.exp (-y / c) - 1| + |(y / c) * Real.exp (-y / c)| := abs_sub _ _
          _ = |Real.exp (-y / c) - 1| + |y / c| * Real.exp (-y / c) := by
              rw [abs_mul, abs_of_pos (Real.exp_pos _)]
          _ ≤ η' + (η' / 2) * 2 := by
              gcongr
          _ = 2 * η' := by ring
          _ ≤ η := hη'_le_half
      have hbounds := abs_le.mp hprod_sub
      dsimp [Q']
      exact ⟨by nlinarith [hKc_pos, hbounds.1], by nlinarith [hKc_pos, hbounds.2]⟩

end FormalResearch.SignUncertainty

/-! ### Axiom Checks (`#guard_msgs`) -/

/-- info: 'FormalResearch.SignUncertainty.oddLaguerreMode_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.oddLaguerreMode_integral

/-- info: 'FormalResearch.SignUncertainty.active_origin_constraint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.active_origin_constraint

/-- info: 'FormalResearch.SignUncertainty.constrained_threshold_eq_unconstrained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.constrained_threshold_eq_unconstrained

/-- info: 'FormalResearch.SignUncertainty.integral_linear_exp_tail_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.integral_linear_exp_tail_lower

/-- info: 'FormalResearch.SignUncertainty.tendsto_rpow_ratio_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.tendsto_rpow_ratio_exp

/-- info: 'FormalResearch.SignUncertainty.sign_separation_eventually_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.sign_separation_eventually_le

/-- info: 'FormalResearch.SignUncertainty.sign_separation_limsup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.sign_separation_limsup

/-- info: 'FormalResearch.SignUncertainty.sign_separation_radii' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.sign_separation_radii

/-- info: 'FormalResearch.SignUncertainty.sign_separation_kappa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.sign_separation_kappa

/-- info: 'FormalResearch.SignUncertainty.langerProfileFamily_tail_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.langerProfileFamily_tail_nonneg

/-- info: 'FormalResearch.SignUncertainty.langerProfileFamily_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.langerProfileFamily_nonvacuous
