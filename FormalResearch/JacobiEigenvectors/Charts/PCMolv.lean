module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Charts.ParabolicCylinder
public import FormalResearch.JacobiEigenvectors.Charts.PCExact
public import DLMF.ParabolicCylinder.Basic.Wronskians

/-!
# Paper J, Layer 4 (phase B2): `molv_well`, `molv_bar`, and `env_bar` symmetry

Purely conditional derivations of the `PCEnvelopeFacts` fields `molv_well` and `molv_bar` (for `pcU, pcV`)
from the envelope upper bounds `env_well` and `env_bar`, together with the derivation of the second conjunct
of `env_bar` from its first conjunct. No new analytic estimates are proved here.

## Headline theorems (all axiom-pinned to `[propext, Classical.choice, Quot.sound]`)

* `env_bar_second_of_first`: for `a > 0`, the second conjunct of `env_bar` (for `U(a, -z)`) follows from the
  first conjunct applied at `-z`, with the **same** constant `C`, using `Ebar a (-z) = (Ebar a z)⁻¹` and
  evenness of `k2` and `Mbal` in `z`.
* `molv_well_of_env_well`: for `a ≤ 0` and all `z`, assuming `env_well` for `pcU, pcV` with constant `C > 0`,
  proves `molv_well` with explicit constants
  `c_well = 1 / (C * sqrt(pi / 2))` and `C_well = sqrt((1 + sqrt(2 / pi))^2 + 2 / pi) * C`.
  - Upper bound: for `z ≥ 0`, directly from `env_well`; for `z < 0`, from `pc_reflect` + `env_well` at `|z|`.
  - Lower bound: from `pc_wronsk` and the Cauchy-Schwarz inequality (`wronsk_le_Env2`), pairing `EU` with
    `EV` (for `z ≥ 0`) or using `Molv ≥ Gamma(1/2 - a) EV(|z|)` with `EU(|z|)` (for `z < 0`).
* `molv_bar_of_env_bar`: for `a > 0` and all `z`, assuming `env_bar` for `pcU` with constant `C > 0`,
  proves `molv_bar` with explicit constants `c_bar = 1 / C` and `C_bar = C`, using `pc_wronsk_neg`
  (real restriction of `parabolicCylinderU_wronskian_neg`) and Cauchy-Schwarz.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.Charts

open Real DLMF.Confluent

/-! ### Local envelope and algebraic helpers -/

private def molvEnv2 (k x x' : ℝ) : ℝ := Real.sqrt (x ^ 2 + x' ^ 2 / k)

private lemma molvEnv2_nonneg (k x x' : ℝ) : 0 ≤ molvEnv2 k x x' := Real.sqrt_nonneg _

private lemma molvEnv2_sq {k : ℝ} (hk : 0 < k) (x x' : ℝ) :
    molvEnv2 k x x' ^ 2 = x ^ 2 + x' ^ 2 / k := by
  unfold molvEnv2
  exact Real.sq_sqrt (by positivity)

private lemma wronsk_le_molvEnv2 {k : ℝ} (hk : 0 < k) (x x' y y' : ℝ) :
    |x * y' - x' * y| ≤ Real.sqrt k * molvEnv2 k x x' * molvEnv2 k y y' := by
  have hsq : (x * y' - x' * y) ^ 2 ≤ (Real.sqrt k * molvEnv2 k x x' * molvEnv2 k y y') ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hk.le, molvEnv2_sq hk, molvEnv2_sq hk]
    have h1 : (x * y' - x' * y) ^ 2 ≤ (x ^ 2 + x' ^ 2 / k) * (k * y ^ 2 + y' ^ 2) := by
      have h2 : (x ^ 2 + x' ^ 2 / k) * (k * y ^ 2 + y' ^ 2) - (x * y' - x' * y) ^ 2
          = (x * Real.sqrt k * y + x' / Real.sqrt k * y') ^ 2 := by
        have hs : Real.sqrt k ^ 2 = k := Real.sq_sqrt hk.le
        have hsn : Real.sqrt k ≠ 0 := (Real.sqrt_pos.mpr hk).ne'
        field_simp
        rw [hs]
        ring
      nlinarith [sq_nonneg (x * Real.sqrt k * y + x' / Real.sqrt k * y')]
    calc (x * y' - x' * y) ^ 2 ≤ (x ^ 2 + x' ^ 2 / k) * (k * y ^ 2 + y' ^ 2) := h1
      _ = k * (x ^ 2 + x' ^ 2 / k) * (y ^ 2 + y' ^ 2 / k) := by field_simp
  exact abs_le_of_sq_le_sq hsq (by have := molvEnv2_nonneg k x x'; have := molvEnv2_nonneg k y y'; positivity)

private lemma molvEnv2_comb_le {k : ℝ} (hk : 0 < k) (α β p p' q q' : ℝ) :
    molvEnv2 k (α * p + β * q) (α * p' + β * q') ≤ |α| * molvEnv2 k p p' + |β| * molvEnv2 k q q' := by
  have hA := molvEnv2_sq hk p p'
  have hB := molvEnv2_sq hk q q'
  have hA0 := molvEnv2_nonneg k p p'
  have hB0 := molvEnv2_nonneg k q q'
  have hsq : (molvEnv2 k (α * p + β * q) (α * p' + β * q')) ^ 2
      ≤ (|α| * molvEnv2 k p p' + |β| * molvEnv2 k q q') ^ 2 := by
    rw [molvEnv2_sq hk]
    have e : (α * p + β * q) ^ 2 + (α * p' + β * q') ^ 2 / k
        = α ^ 2 * (p ^ 2 + p' ^ 2 / k) + β ^ 2 * (q ^ 2 + q' ^ 2 / k) + 2 * α * β * (p * q + p' * q' / k) := by
      field_simp; ring
    rw [e]
    have e2 : (|α| * molvEnv2 k p p' + |β| * molvEnv2 k q q') ^ 2
        = α ^ 2 * (p ^ 2 + p' ^ 2 / k) + β ^ 2 * (q ^ 2 + q' ^ 2 / k)
          + 2 * (|α| * |β|) * (molvEnv2 k p p' * molvEnv2 k q q') := by
      have := sq_abs α; have := sq_abs β
      nlinarith [hA, hB]
    rw [e2]
    have hp_abs : |p * q + p' * q' / k| ≤ molvEnv2 k p p' * molvEnv2 k q q' := by
      have h2' : (p * q + p' * q' / k) ^ 2 ≤ (molvEnv2 k p p' * molvEnv2 k q q') ^ 2 := by
        rw [mul_pow, hA, hB]
        have : (p ^ 2 + p' ^ 2 / k) * (q ^ 2 + q' ^ 2 / k) - (p * q + p' * q' / k) ^ 2
            = (p * q' - p' * q) ^ 2 / k := by field_simp; ring
        have h3 : 0 ≤ (p * q' - p' * q) ^ 2 / k := by positivity
        linarith
      exact abs_le_of_sq_le_sq h2' (by positivity)
    have hlin : α * β * (p * q + p' * q' / k) ≤ |α| * |β| * (molvEnv2 k p p' * molvEnv2 k q q') := by
      calc α * β * (p * q + p' * q' / k)
          ≤ |α * β * (p * q + p' * q' / k)| := le_abs_self _
        _ = |α| * |β| * |p * q + p' * q' / k| := by rw [abs_mul, abs_mul]
        _ ≤ |α| * |β| * (molvEnv2 k p p' * molvEnv2 k q q') :=
            mul_le_mul_of_nonneg_left hp_abs (by positivity)
    linarith
  have := abs_le_of_sq_le_sq hsq (by positivity)
  rwa [abs_of_nonneg (molvEnv2_nonneg k _ _)] at this

private lemma k2_pos (a z : ℝ) : 0 < k2 a z := by
  unfold k2
  exact lt_max_of_lt_right (Real.rpow_pos_of_pos (lt_max_of_lt_right one_pos) _)

private lemma k2_neg (a z : ℝ) : k2 a (-z) = k2 a z := by simp [k2]

private lemma Mbal_neg (a z : ℝ) : Mbal a (-z) = Mbal a z := by simp [Mbal, k2_neg]

private lemma Mbal_pos (a z : ℝ) : 0 < Mbal a z :=
  Real.rpow_pos_of_pos (k2_pos a z) _

private lemma Mbal_sq_mul (a z : ℝ) : Real.sqrt (k2 a z) * Mbal a z ^ 2 = 1 := by
  have hk := k2_pos a z
  unfold Mbal
  rw [← Real.rpow_natCast, ← Real.rpow_mul hk.le, Real.sqrt_eq_rpow, ← Real.rpow_add hk]
  norm_num

private lemma kappaBal_nonpos_props {a : ℝ} (ha : a ≤ 0) :
    0 < kappaBal a ∧ kappaBal a ^ 2 * Real.Gamma (1 / 2 - a) = 1 := by
  have hG : 0 < Real.Gamma (1 / 2 - a) := Real.Gamma_pos_of_pos (by linarith)
  have hk : kappaBal a = (Real.Gamma (1 / 2 - a)) ^ (-(1 : ℝ) / 2) := by
    unfold kappaBal; exact ite_eq_left_iff.mpr (fun h => absurd ha h)
  rw [hk]
  refine ⟨Real.rpow_pos_of_pos hG _, ?_⟩
  rw [← Real.rpow_natCast, ← Real.rpow_mul hG.le]
  have : (-(1 : ℝ) / 2 * ((2 : ℕ) : ℝ)) = -1 := by norm_num
  rw [this, Real.rpow_neg_one]
  exact inv_mul_cancel₀ hG.ne'

private lemma kappaBal_pos_props {a : ℝ} (ha : 0 < a) :
    0 < kappaBal a ∧ kappaBal a ^ 2 * (Real.sqrt (2 * Real.pi) / Real.Gamma (1 / 2 + a)) = 1 := by
  have hG : 0 < Real.Gamma (1 / 2 + a) := Real.Gamma_pos_of_pos (by linarith)
  have h2pi : 0 < 2 * Real.pi := by positivity
  have hk : kappaBal a = (2 * Real.pi) ^ (-(1 : ℝ) / 4) * Real.sqrt (Real.Gamma (1 / 2 + a)) := by
    unfold kappaBal; exact ite_eq_right_iff.mpr (fun h => absurd ha (not_lt.mpr h))
  refine ⟨by rw [hk]; positivity, ?_⟩
  have hsq : kappaBal a ^ 2 = (Real.sqrt (2 * Real.pi))⁻¹ * Real.Gamma (1 / 2 + a) := by
    rw [hk, mul_pow, Real.sq_sqrt hG.le, ← Real.rpow_natCast, ← Real.rpow_mul h2pi.le]
    have : (-(1 : ℝ) / 4 * ((2 : ℕ) : ℝ)) = -(1 : ℝ) / 2 := by norm_num
    rw [this, show -(1 : ℝ) / 2 = -((1 : ℝ) / 2) by ring, Real.rpow_neg h2pi.le, Real.sqrt_eq_rpow]
  rw [hsq]
  have hs : Real.sqrt (2 * Real.pi) ≠ 0 := (Real.sqrt_pos.mpr h2pi).ne'
  field_simp

private lemma Ewell_pos (a z : ℝ) : 0 < Ewell a z := by
  unfold Ewell
  split_ifs <;> positivity

private lemma Ewell_le_one (a z : ℝ) : Ewell a z ≤ 1 := by
  unfold Ewell
  split_ifs with h
  · rw [Real.exp_le_one_iff, neg_nonpos]
    exact intervalIntegral.integral_nonneg h.le (fun _ _ => Real.sqrt_nonneg _)
  · exact le_rfl

private lemma deriv_pcU_comp_neg (a z : ℝ) :
    deriv (fun w => pcU a (-w)) z = -deriv (pcU a) (-z) := by
  have h : HasDerivAt (fun w => pcU a (-w)) (-pcUD a (-z)) z := by
    simpa [Function.comp_def] using (hasDerivAt_pcU a (-z)).comp z (hasDerivAt_neg z)
  rw [h.deriv, deriv_pcU]

private lemma deriv_pcU_reflect {a : ℝ} (ha : a ≤ 0) (w : ℝ) :
    deriv (pcU a) (-w) = -((-Real.sin (Real.pi * a) * deriv (pcU a) w
      + Real.cos (Real.pi * a) * Real.Gamma (1 / 2 - a) * deriv (pcV a) w)) := by
  have hfun : (fun t => pcU a (-t)) = fun t => -Real.sin (Real.pi * a) * pcU a t
      + Real.cos (Real.pi * a) * Real.Gamma (1 / 2 - a) * pcV a t :=
    funext (pc_reflect a ha)
  have h1 : deriv (fun t => pcU a (-t)) w = -deriv (pcU a) (-w) := deriv_pcU_comp_neg a w
  have h2 : HasDerivAt (fun t => -Real.sin (Real.pi * a) * pcU a t
      + Real.cos (Real.pi * a) * Real.Gamma (1 / 2 - a) * pcV a t)
      (-Real.sin (Real.pi * a) * pcUD a w
        + Real.cos (Real.pi * a) * Real.Gamma (1 / 2 - a) * pcVD a w) w :=
    ((hasDerivAt_pcU a w).const_mul _).add ((hasDerivAt_pcV a w).const_mul _)
  rw [hfun, h2.deriv, ← deriv_pcU, ← deriv_pcV] at h1
  linarith

/-! ### Part 3: Second conjunct of `env_bar` from the first -/

/-- For `a > 0`, `Ebar a (-z) = (Ebar a z)⁻¹`. -/
lemma Ebar_neg (a z : ℝ) : Ebar a (-z) = (Ebar a z)⁻¹ := by
  unfold Ebar
  rw [← Real.exp_neg]
  congr 1
  have h := intervalIntegral.integral_comp_neg (fun t => Real.sqrt (t ^ 2 / 4 + a)) (a := 0) (b := z)
  simp only [neg_zero, neg_sq] at h
  rw [intervalIntegral.integral_symm 0 (-z)] at h
  linarith

/-- The second conjunct of `env_bar` follows from the first applied at `-z`, with the same constant `C`. -/
theorem env_bar_second_of_first {C : ℝ}
    (h : ∀ a, 0 < a → ∀ z,
      Real.sqrt ((kappaBal a * pcU a z) ^ 2 + (kappaBal a * deriv (pcU a) z) ^ 2 / k2 a z)
        ≤ C * Ebar a z * Mbal a z) :
    ∀ a, 0 < a → ∀ z,
      Real.sqrt ((kappaBal a * pcU a z) ^ 2 + (kappaBal a * deriv (pcU a) z) ^ 2 / k2 a z)
        ≤ C * Ebar a z * Mbal a z ∧
      Real.sqrt ((kappaBal a * pcU a (-z)) ^ 2 + (kappaBal a * deriv (fun w => pcU a (-w)) z) ^ 2 / k2 a z)
        ≤ C * (Ebar a z)⁻¹ * Mbal a z := by
  intro a ha z
  refine ⟨h a ha z, ?_⟩
  have hneg := h a ha (-z)
  rw [deriv_pcU_comp_neg, k2_neg, Mbal_neg, Ebar_neg] at *
  simpa [mul_neg, neg_sq] using hneg

/-! ### Part 1: `molv_well` from `env_well` -/

/-- `molv_well` for `pcU, pcV` derived conditionally from `env_well` with constant `C > 0`,
with explicit constants `c_well = 1 / (C * sqrt(pi / 2))` and
`C_well = sqrt((1 + sqrt(2 / pi))^2 + 2 / pi) * C`. -/
theorem molv_well_of_env_well {C : ℝ} (hC : 0 < C)
    (h : ∀ a ≤ 0, ∀ z, 0 ≤ z →
      Real.sqrt (ut pcU a z ^ 2 + (kappaBal a * deriv (pcU a) z) ^ 2 / k2 a z) ≤ C * Ewell a z * Mbal a z ∧
      Real.sqrt (vt pcV a z ^ 2 + (Real.sqrt (Real.pi / 2) * (kappaBal a)⁻¹ * deriv (pcV a) z) ^ 2 / k2 a z)
        ≤ C * (Ewell a z)⁻¹ * Mbal a z) :
    ∀ a ≤ 0, ∀ z,
      (1 / (C * Real.sqrt (Real.pi / 2))) * (kappaBal a)⁻¹ * Wwell a z * Mbal a z ≤ Molv pcU pcV a z ∧
      Molv pcU pcV a z ≤ (Real.sqrt ((1 + Real.sqrt (2 / Real.pi)) ^ 2 + 2 / Real.pi) * C) *
        (kappaBal a)⁻¹ * Wwell a z * Mbal a z := by
  intro a ha z
  obtain ⟨hκ, hκ2⟩ := kappaBal_nonpos_props ha
  have hk := k2_pos a z
  have hm := Mbal_pos a z
  have hm2 := Mbal_sq_mul a z
  have hsp_pos : 0 < Real.sqrt (Real.pi / 2) := Real.sqrt_pos.mpr (by positivity)
  have h2p_pos : 0 < Real.sqrt (2 / Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hsp_mul : Real.sqrt (Real.pi / 2) * Real.sqrt (2 / Real.pi) = 1 := by
    rw [← Real.sqrt_mul (by positivity), show Real.pi / 2 * (2 / Real.pi) = 1 by field_simp, Real.sqrt_one]
  set κ := kappaBal a with hκdef
  set Γ := Real.Gamma (1 / 2 - a) with hΓdef
  have hΓ_eq : Γ = κ⁻¹ ^ 2 := by
    have : κ ^ 2 * Γ = 1 := hκ2
    field_simp at this ⊢
    nlinarith
  have hEU_scale : ∀ w, κ * Real.sqrt (pcU a w ^ 2 + deriv (pcU a) w ^ 2 / k2 a w)
      = molvEnv2 (k2 a w) (κ * pcU a w) (κ * deriv (pcU a) w) := by
    intro w
    unfold molvEnv2
    rw [show (κ * pcU a w) ^ 2 + (κ * deriv (pcU a) w) ^ 2 / k2 a w
        = κ ^ 2 * (pcU a w ^ 2 + deriv (pcU a) w ^ 2 / k2 a w) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hκ.le]
  have hEV_scale : ∀ w, Real.sqrt (Real.pi / 2) * κ⁻¹ * Real.sqrt (pcV a w ^ 2 + deriv (pcV a) w ^ 2 / k2 a w)
      = molvEnv2 (k2 a w) (Real.sqrt (Real.pi / 2) * κ⁻¹ * pcV a w) (Real.sqrt (Real.pi / 2) * κ⁻¹ * deriv (pcV a) w) := by
    intro w
    unfold molvEnv2
    rw [show (Real.sqrt (Real.pi / 2) * κ⁻¹ * pcV a w) ^ 2 +
          (Real.sqrt (Real.pi / 2) * κ⁻¹ * deriv (pcV a) w) ^ 2 / k2 a w
        = (Real.sqrt (Real.pi / 2) * κ⁻¹) ^ 2 * (pcV a w ^ 2 + deriv (pcV a) w ^ 2 / k2 a w) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  rcases lt_or_ge z 0 with hz0 | hz0
  · -- Case 1: z < 0
    have hz_neg : ¬ (0 ≤ z ∨ 0 < a) := not_or.mpr ⟨not_le.mpr hz0, not_lt.mpr ha⟩
    have hMolv : Molv pcU pcV a z = Real.sqrt (Real.sqrt (pcU a z ^ 2 + deriv (pcU a) z ^ 2 / k2 a z) ^ 2 +
        Γ ^ 2 * Real.sqrt (pcV a |z| ^ 2 + deriv (pcV a) |z| ^ 2 / k2 a |z|) ^ 2) := by
      unfold Molv; exact ite_eq_right_iff.mpr (fun h => absurd h hz_neg)
    have hWwell : Wwell a z = (Ewell a |z|)⁻¹ := by
      unfold Wwell; exact ite_eq_right_iff.mpr (fun h => absurd h (not_le.mpr hz0))
    rw [hMolv, hWwell]
    set w := |z| with hwdef
    have hw_eq : z = -w := by rw [hwdef, abs_of_neg hz0, neg_neg]
    have hw0 : 0 ≤ w := abs_nonneg z
    have hk_w : k2 a w = k2 a z := by rw [hw_eq, k2_neg]
    have hm_w : Mbal a w = Mbal a z := by rw [hw_eq, Mbal_neg]
    obtain ⟨hUw, hVw⟩ := h a ha w hw0
    simp only [ut, vt] at hUw hVw
    set EUz := Real.sqrt (pcU a z ^ 2 + deriv (pcU a) z ^ 2 / k2 a z)
    set EVw := Real.sqrt (pcV a w ^ 2 + deriv (pcV a) w ^ 2 / k2 a w)
    have hEUz_nn : 0 ≤ EUz := Real.sqrt_nonneg _
    have hEVw_nn : 0 ≤ EVw := Real.sqrt_nonneg _
    have hEw_pos : 0 < Ewell a w := Ewell_pos a w
    have hEw_le1 : Ewell a w ≤ 1 := Ewell_le_one a w
    have hEw_le_inv : Ewell a w ≤ (Ewell a w)⁻¹ :=
      hEw_le1.trans ((one_le_inv₀ hEw_pos).mpr hEw_le1)
    refine ⟨?_, ?_⟩
    · -- Lower bound for z < 0: Molv ≥ Γ * EVw, and EVw from wronsk + env_well.1 at w
      have hM_ge : Γ * EVw ≤ Real.sqrt (EUz ^ 2 + Γ ^ 2 * EVw ^ 2) := by
        have hΓ_nn : 0 ≤ Γ := (Real.Gamma_pos_of_pos (by linarith)).le
        calc Γ * EVw = Real.sqrt ((Γ * EVw) ^ 2) := (Real.sqrt_sq (mul_nonneg hΓ_nn hEVw_nn)).symm
          _ = Real.sqrt (Γ ^ 2 * EVw ^ 2) := by ring_nf
          _ ≤ Real.sqrt (EUz ^ 2 + Γ ^ 2 * EVw ^ 2) := Real.sqrt_le_sqrt (by linarith [sq_nonneg EUz])
      set x := κ * pcU a w
      set x' := κ * deriv (pcU a) w
      set y := Real.sqrt (Real.pi / 2) * κ⁻¹ * pcV a w
      set y' := Real.sqrt (Real.pi / 2) * κ⁻¹ * deriv (pcV a) w
      have hW : x * y' - x' * y = 1 := by
        have hw := pc_wronsk a w
        have : x * y' - x' * y = Real.sqrt (Real.pi / 2) * (κ * κ⁻¹) *
            (pcU a w * deriv (pcV a) w - deriv (pcU a) w * pcV a w) := by
          dsimp [x, x', y, y']; ring
        rw [this, mul_inv_cancel₀ hκ.ne', mul_one, hw, hsp_mul]
      have hcs := wronsk_le_molvEnv2 (k2_pos a w) x x' y y'
      rw [hW, abs_one, ← hEV_scale w] at hcs
      have h1 : 1 ≤ Real.sqrt (k2 a w) * (C * Ewell a w * Mbal a w) *
          (Real.sqrt (Real.pi / 2) * κ⁻¹ * EVw) :=
        hcs.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hUw (Real.sqrt_nonneg _)) (by positivity))
      have hm_w2 := Mbal_sq_mul a w
      have h2 : (Ewell a w)⁻¹ * Mbal a w ≤ C * Real.sqrt (Real.pi / 2) * (κ⁻¹ * EVw) := by
        have hmul : (Ewell a w)⁻¹ * Mbal a w ≤ (Ewell a w)⁻¹ * Mbal a w *
            (Real.sqrt (k2 a w) * (C * Ewell a w * Mbal a w) * (Real.sqrt (Real.pi / 2) * κ⁻¹ * EVw)) :=
          le_mul_of_one_le_right (mul_nonneg (inv_nonneg.mpr hEw_pos.le) (Mbal_pos a w).le) h1
        have heq : (Ewell a w)⁻¹ * Mbal a w *
            (Real.sqrt (k2 a w) * (C * Ewell a w * Mbal a w) * (Real.sqrt (Real.pi / 2) * κ⁻¹ * EVw))
            = (Real.sqrt (k2 a w) * Mbal a w ^ 2) * ((Ewell a w)⁻¹ * Ewell a w) *
              (C * Real.sqrt (Real.pi / 2) * (κ⁻¹ * EVw)) := by ring
        rw [heq, hm_w2, inv_mul_cancel₀ hEw_pos.ne', one_mul, one_mul] at hmul
        exact hmul
      have h3 : 1 / (C * Real.sqrt (Real.pi / 2)) * κ⁻¹ * (Ewell a w)⁻¹ * Mbal a z ≤ Γ * EVw := by
        rw [hΓ_eq, ← hm_w]
        have h4 : 1 / (C * Real.sqrt (Real.pi / 2)) * ((Ewell a w)⁻¹ * Mbal a w) ≤ κ⁻¹ * EVw := by
          rw [one_div, inv_mul_le_iff₀ (mul_pos hC hsp_pos)]
          exact h2
        calc 1 / (C * Real.sqrt (Real.pi / 2)) * κ⁻¹ * (Ewell a w)⁻¹ * Mbal a w
            = κ⁻¹ * (1 / (C * Real.sqrt (Real.pi / 2)) * ((Ewell a w)⁻¹ * Mbal a w)) := by ring
          _ ≤ κ⁻¹ * (κ⁻¹ * EVw) := mul_le_mul_of_nonneg_left h4 (inv_nonneg.mpr hκ.le)
          _ = κ⁻¹ ^ 2 * EVw := by ring
      exact h3.trans hM_ge
    · -- Upper bound for z < 0: bound κ * EUz via pc_reflect and κ * Γ * EVw via env_well.2
      have hEUz_bd : κ * EUz ≤ (1 + Real.sqrt (2 / Real.pi)) * C * (Ewell a w)⁻¹ * Mbal a z := by
        rw [hEU_scale z, hw_eq, k2_neg, ← hw_eq, ← hm_w]
        have hUz : κ * pcU a (-w) = (-Real.sin (Real.pi * a)) * (κ * pcU a w) +
            (Real.cos (Real.pi * a) * Real.sqrt (2 / Real.pi)) * (Real.sqrt (Real.pi / 2) * κ⁻¹ * pcV a w) := by
          rw [pc_reflect a ha w]
          have hkap : κ * Γ = κ⁻¹ := by rw [hΓ_eq]; field_simp
          calc κ * (-Real.sin (Real.pi * a) * pcU a w + Real.cos (Real.pi * a) * Γ * pcV a w)
              = (-Real.sin (Real.pi * a)) * (κ * pcU a w) + Real.cos (Real.pi * a) * (κ * Γ) * pcV a w := by ring
            _ = (-Real.sin (Real.pi * a)) * (κ * pcU a w) + Real.cos (Real.pi * a) * κ⁻¹ * pcV a w := by rw [hkap]
            _ = (-Real.sin (Real.pi * a)) * (κ * pcU a w) +
                Real.cos (Real.pi * a) * (Real.sqrt (2 / Real.pi) * Real.sqrt (Real.pi / 2)) * κ⁻¹ * pcV a w := by
                  rw [mul_comm (Real.sqrt (2 / Real.pi)), hsp_mul, mul_one]
            _ = _ := by ring
        have hUz' : κ * deriv (pcU a) (-w) = -((-Real.sin (Real.pi * a)) * (κ * deriv (pcU a) w) +
            (Real.cos (Real.pi * a) * Real.sqrt (2 / Real.pi)) * (Real.sqrt (Real.pi / 2) * κ⁻¹ * deriv (pcV a) w)) := by
          rw [deriv_pcU_reflect ha w]
          have hkap : κ * Γ = κ⁻¹ := by rw [hΓ_eq]; field_simp
          calc κ * -(-Real.sin (Real.pi * a) * deriv (pcU a) w + Real.cos (Real.pi * a) * Γ * deriv (pcV a) w)
              = -((-Real.sin (Real.pi * a)) * (κ * deriv (pcU a) w) +
                  Real.cos (Real.pi * a) * (κ * Γ) * deriv (pcV a) w) := by ring
            _ = -((-Real.sin (Real.pi * a)) * (κ * deriv (pcU a) w) +
                  Real.cos (Real.pi * a) * κ⁻¹ * deriv (pcV a) w) := by rw [hkap]
            _ = -((-Real.sin (Real.pi * a)) * (κ * deriv (pcU a) w) +
                  Real.cos (Real.pi * a) * (Real.sqrt (2 / Real.pi) * Real.sqrt (Real.pi / 2)) * κ⁻¹ * deriv (pcV a) w) := by
                  rw [mul_comm (Real.sqrt (2 / Real.pi)), hsp_mul, mul_one]
            _ = _ := by ring
        have hEyeq : molvEnv2 (k2 a w) (κ * pcU a (-w)) (κ * deriv (pcU a) (-w))
            = molvEnv2 (k2 a w)
              ((-Real.sin (Real.pi * a)) * (κ * pcU a w) +
                (Real.cos (Real.pi * a) * Real.sqrt (2 / Real.pi)) * (Real.sqrt (Real.pi / 2) * κ⁻¹ * pcV a w))
              ((-Real.sin (Real.pi * a)) * (κ * deriv (pcU a) w) +
                (Real.cos (Real.pi * a) * Real.sqrt (2 / Real.pi)) * (Real.sqrt (Real.pi / 2) * κ⁻¹ * deriv (pcV a) w)) := by
          unfold molvEnv2
          rw [hUz, hUz']
          congr 1; ring
        rw [← hw_eq] at hEyeq
        rw [hEyeq]
        refine (molvEnv2_comb_le (k2_pos a w) (-Real.sin (Real.pi * a))
          (Real.cos (Real.pi * a) * Real.sqrt (2 / Real.pi))
          (κ * pcU a w) (κ * deriv (pcU a) w)
          (Real.sqrt (Real.pi / 2) * κ⁻¹ * pcV a w) (Real.sqrt (Real.pi / 2) * κ⁻¹ * deriv (pcV a) w)).trans ?_
        have hsin : |-Real.sin (Real.pi * a)| ≤ 1 := by rw [abs_neg]; exact Real.abs_sin_le_one _
        have hcos : |Real.cos (Real.pi * a) * Real.sqrt (2 / Real.pi)| ≤ Real.sqrt (2 / Real.pi) := by
          rw [abs_mul, abs_of_nonneg h2p_pos.le]
          exact mul_le_of_le_one_left h2p_pos.le (Real.abs_cos_le_one _)
        have hUw' : molvEnv2 (k2 a w) (κ * pcU a w) (κ * deriv (pcU a) w) ≤ C * (Ewell a w)⁻¹ * Mbal a w :=
          hUw.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hEw_le_inv hC.le) (Mbal_pos a w).le)
        calc |-Real.sin (Real.pi * a)| * molvEnv2 (k2 a w) (κ * pcU a w) (κ * deriv (pcU a) w)
              + |Real.cos (Real.pi * a) * Real.sqrt (2 / Real.pi)| *
                molvEnv2 (k2 a w) (Real.sqrt (Real.pi / 2) * κ⁻¹ * pcV a w)
                  (Real.sqrt (Real.pi / 2) * κ⁻¹ * deriv (pcV a) w)
            ≤ 1 * (C * (Ewell a w)⁻¹ * Mbal a w) + Real.sqrt (2 / Real.pi) * (C * (Ewell a w)⁻¹ * Mbal a w) := by
              apply add_le_add
              · exact mul_le_mul hsin hUw' (molvEnv2_nonneg _ _ _) zero_le_one
              · exact mul_le_mul hcos hVw (molvEnv2_nonneg _ _ _) h2p_pos.le
          _ = (1 + Real.sqrt (2 / Real.pi)) * C * (Ewell a w)⁻¹ * Mbal a w := by ring
      have hEVw_bd : κ * (Γ * EVw) ≤ Real.sqrt (2 / Real.pi) * C * (Ewell a w)⁻¹ * Mbal a z := by
        have hV' : Real.sqrt (Real.pi / 2) * κ⁻¹ * EVw ≤ C * (Ewell a w)⁻¹ * Mbal a w := by
          rw [hEV_scale w]; exact hVw
        have hkap : κ * Γ = κ⁻¹ := by
          rw [hΓ_eq]; field_simp
        rw [← mul_assoc, hkap, ← hm_w]
        calc κ⁻¹ * EVw = Real.sqrt (2 / Real.pi) * (Real.sqrt (Real.pi / 2) * κ⁻¹ * EVw) := by
              rw [show Real.sqrt (2 / Real.pi) * (Real.sqrt (Real.pi / 2) * κ⁻¹ * EVw)
                  = (Real.sqrt (Real.pi / 2) * Real.sqrt (2 / Real.pi)) * κ⁻¹ * EVw by ring,
                hsp_mul, one_mul]
          _ ≤ Real.sqrt (2 / Real.pi) * (C * (Ewell a w)⁻¹ * Mbal a w) :=
              mul_le_mul_of_nonneg_left hV' h2p_pos.le
          _ = Real.sqrt (2 / Real.pi) * C * (Ewell a w)⁻¹ * Mbal a w := by ring
      have hsq : (κ * Real.sqrt (EUz ^ 2 + Γ ^ 2 * EVw ^ 2)) ^ 2
          ≤ (Real.sqrt ((1 + Real.sqrt (2 / Real.pi)) ^ 2 + 2 / Real.pi) * C * (Ewell a w)⁻¹ * Mbal a z) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by positivity), mul_pow, mul_pow, mul_pow,
          Real.sq_sqrt (show 0 ≤ (1 + Real.sqrt (2 / Real.pi)) ^ 2 + 2 / Real.pi by positivity)]
        have h1sq : (κ * EUz) ^ 2 ≤ ((1 + Real.sqrt (2 / Real.pi)) * C * (Ewell a w)⁻¹ * Mbal a z) ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg hκ.le hEUz_nn) hEUz_bd 2
        have h2sq : (κ * (Γ * EVw)) ^ 2 ≤ (Real.sqrt (2 / Real.pi) * C * (Ewell a w)⁻¹ * Mbal a z) ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg hκ.le (mul_nonneg (Real.Gamma_pos_of_pos (by linarith)).le hEVw_nn)) hEVw_bd 2
        have hsum : (κ * EUz) ^ 2 + (κ * (Γ * EVw)) ^ 2
            ≤ ((1 + Real.sqrt (2 / Real.pi)) * C * (Ewell a w)⁻¹ * Mbal a z) ^ 2 +
              (Real.sqrt (2 / Real.pi) * C * (Ewell a w)⁻¹ * Mbal a z) ^ 2 := add_le_add h1sq h2sq
        have hL : κ ^ 2 * (EUz ^ 2 + Γ ^ 2 * EVw ^ 2)
            = (κ * EUz) ^ 2 + (κ * (Γ * EVw)) ^ 2 := by ring
        have hR : ((1 + Real.sqrt (2 / Real.pi)) ^ 2 + 2 / Real.pi) * C ^ 2 * (Ewell a w)⁻¹ ^ 2 * Mbal a z ^ 2
            = ((1 + Real.sqrt (2 / Real.pi)) * C * (Ewell a w)⁻¹ * Mbal a z) ^ 2 +
              (Real.sqrt (2 / Real.pi) * C * (Ewell a w)⁻¹ * Mbal a z) ^ 2 := by
          set s := Real.sqrt (2 / Real.pi)
          have hs : s ^ 2 = 2 / Real.pi := Real.sq_sqrt (by positivity)
          rw [← hs]
          ring
        rw [hL, hR]
        exact hsum
      have hprod : κ * Real.sqrt (EUz ^ 2 + Γ ^ 2 * EVw ^ 2)
          ≤ Real.sqrt ((1 + Real.sqrt (2 / Real.pi)) ^ 2 + 2 / Real.pi) * C * (Ewell a w)⁻¹ * Mbal a z := by
        have := abs_le_of_sq_le_sq hsq (by positivity)
        rwa [abs_of_nonneg (by positivity)] at this
      rw [show Real.sqrt ((1 + Real.sqrt (2 / Real.pi)) ^ 2 + 2 / Real.pi) * C * κ⁻¹ * (Ewell a w)⁻¹ * Mbal a z
          = (Real.sqrt ((1 + Real.sqrt (2 / Real.pi)) ^ 2 + 2 / Real.pi) * C * (Ewell a w)⁻¹ * Mbal a z) / κ by ring,
        le_div_iff₀ hκ, mul_comm _ κ]
      exact hprod
  · -- Case 2: 0 ≤ z
    have hMolv : Molv pcU pcV a z = Real.sqrt (pcU a z ^ 2 + deriv (pcU a) z ^ 2 / k2 a z) := by
      unfold Molv; exact ite_eq_left_iff.mpr (fun h => absurd (Or.inl hz0) h)
    have hWwell : Wwell a z = Ewell a z := by
      unfold Wwell; exact ite_eq_left_iff.mpr (fun h => absurd hz0 h)
    rw [hMolv, hWwell]
    obtain ⟨hU, hV⟩ := h a ha z hz0
    simp only [ut, vt] at hU hV
    have hU' : κ * Real.sqrt (pcU a z ^ 2 + deriv (pcU a) z ^ 2 / k2 a z) ≤ C * Ewell a z * Mbal a z := by
      rw [hEU_scale z]; exact hU
    have hV' : molvEnv2 (k2 a z) (Real.sqrt (Real.pi / 2) * κ⁻¹ * pcV a z)
        (Real.sqrt (Real.pi / 2) * κ⁻¹ * deriv (pcV a) z) ≤ C * (Ewell a z)⁻¹ * Mbal a z := hV
    refine ⟨?_, ?_⟩
    · -- Lower bound for z ≥ 0 via wronsk + env_well.2
      set x := κ * pcU a z
      set x' := κ * deriv (pcU a) z
      set y := Real.sqrt (Real.pi / 2) * κ⁻¹ * pcV a z
      set y' := Real.sqrt (Real.pi / 2) * κ⁻¹ * deriv (pcV a) z
      have hW : x * y' - x' * y = 1 := by
        have hw := pc_wronsk a z
        have : x * y' - x' * y = Real.sqrt (Real.pi / 2) * (κ * κ⁻¹) *
            (pcU a z * deriv (pcV a) z - deriv (pcU a) z * pcV a z) := by
          dsimp [x, x', y, y']; ring
        rw [this, mul_inv_cancel₀ hκ.ne', mul_one, hw, hsp_mul]
      have hcs := wronsk_le_molvEnv2 hk x x' y y'
      rw [hW, abs_one, ← hEU_scale z] at hcs
      set EU := Real.sqrt (pcU a z ^ 2 + deriv (pcU a) z ^ 2 / k2 a z)
      have h1 : 1 ≤ Real.sqrt (k2 a z) * (κ * EU) * (C * (Ewell a z)⁻¹ * Mbal a z) :=
        hcs.trans (mul_le_mul_of_nonneg_left hV' (by positivity))
      have hEw : 0 < Ewell a z := Ewell_pos a z
      have h2 : Ewell a z * Mbal a z ≤ C * (κ * EU) := by
        have hmul : Ewell a z * Mbal a z ≤ Ewell a z * Mbal a z *
            (Real.sqrt (k2 a z) * (κ * EU) * (C * (Ewell a z)⁻¹ * Mbal a z)) :=
          le_mul_of_one_le_right (by positivity) h1
        have heq : Ewell a z * Mbal a z *
            (Real.sqrt (k2 a z) * (κ * EU) * (C * (Ewell a z)⁻¹ * Mbal a z))
            = (Real.sqrt (k2 a z) * Mbal a z ^ 2) * (Ewell a z * (Ewell a z)⁻¹) * (C * (κ * EU)) := by ring
        rw [heq, hm2, mul_inv_cancel₀ hEw.ne', one_mul, one_mul] at hmul
        exact hmul
      have h3 : (1 / C) * κ⁻¹ * Ewell a z * Mbal a z ≤ EU := by
        rw [show (1 / C) * κ⁻¹ * Ewell a z * Mbal a z = (Ewell a z * Mbal a z) / (C * κ) by ring,
          div_le_iff₀ (mul_pos hC hκ)]
        linarith
      have hc_le : 1 / (C * Real.sqrt (Real.pi / 2)) ≤ 1 / C := by
        refine one_div_le_one_div_of_le hC ?_
        refine le_mul_of_one_le_right hC.le ?_
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
      calc (1 / (C * Real.sqrt (Real.pi / 2))) * κ⁻¹ * Ewell a z * Mbal a z
          ≤ (1 / C) * κ⁻¹ * Ewell a z * Mbal a z := by gcongr
        _ ≤ EU := h3
    · -- Upper bound for z ≥ 0 directly from env_well.1
      have hU_le : Real.sqrt (pcU a z ^ 2 + deriv (pcU a) z ^ 2 / k2 a z)
          ≤ C * κ⁻¹ * Ewell a z * Mbal a z := by
        rw [show C * κ⁻¹ * Ewell a z * Mbal a z = (C * Ewell a z * Mbal a z) / κ by ring,
          le_div_iff₀ hκ, mul_comm _ κ]
        exact hU'
      have hC_le : C ≤ Real.sqrt ((1 + Real.sqrt (2 / Real.pi)) ^ 2 + 2 / Real.pi) * C := by
        refine le_mul_of_one_le_left hC.le ?_
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt (by rw [Real.sqrt_one]; nlinarith [h2p_pos.le, show (0 : ℝ) ≤ 2 / Real.pi by positivity])
      have hEw_nn : 0 ≤ Ewell a z := (Ewell_pos a z).le
      calc Real.sqrt (pcU a z ^ 2 + deriv (pcU a) z ^ 2 / k2 a z)
          ≤ C * κ⁻¹ * Ewell a z * Mbal a z := hU_le
        _ ≤ (Real.sqrt ((1 + Real.sqrt (2 / Real.pi)) ^ 2 + 2 / Real.pi) * C) *
            κ⁻¹ * Ewell a z * Mbal a z := by gcongr

/-! ### Part 2: `molv_bar` from `env_bar` and `parabolicCylinderU_wronskian_neg` -/

/-- Real restriction of `parabolicCylinderU_wronskian_neg` (DLMF 12.2.11):
`U(a, z) * d/dz(U(a, -z)) - U'(a, z) * U(a, -z) = sqrt(2 * pi) / Gamma(1/2 + a)`. -/
theorem pc_wronsk_neg (a z : ℝ) :
    pcU a z * deriv (fun w => pcU a (-w)) z - deriv (pcU a) z * pcU a (-z) =
      Real.sqrt (2 * Real.pi) / Real.Gamma (1 / 2 + a) := by
  have h := congrArg Complex.re (parabolicCylinderU_wronskian_neg (a : ℂ) (z : ℂ))
  have hd_neg : deriv (fun w : ℂ => parabolicCylinderU (a : ℂ) (-w)) (z : ℂ) =
      -parabolicCylinderUDeriv (a : ℂ) (-(z : ℂ)) :=
    (hasDerivAt_parabolicCylinderU_neg (a : ℂ) (z : ℂ)).deriv
  rw [hd_neg, deriv_parabolicCylinderU] at h
  have hU_z := pcU_ofReal a z
  have hU_nz : parabolicCylinderU (a : ℂ) (-(z : ℂ)) = (pcU a (-z) : ℂ) := by
    simpa using pcU_ofReal a (-z)
  have hL : (parabolicCylinderU (a : ℂ) (z : ℂ) * (-parabolicCylinderUDeriv (a : ℂ) (-(z : ℂ))) -
      parabolicCylinderUDeriv (a : ℂ) (z : ℂ) * parabolicCylinderU (a : ℂ) (-(z : ℂ))).re =
      pcU a z * deriv (fun w => pcU a (-w)) z - deriv (pcU a) z * pcU a (-z) := by
    rw [hU_z, hU_nz, deriv_pcU, deriv_pcU_comp_neg, deriv_pcU]
    simp only [pcUD, Complex.sub_re, Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, mul_zero]
    push_cast; ring
  have hR : ((Real.sqrt (2 * Real.pi) : ℂ) / Complex.Gamma (1 / 2 + (a : ℂ))).re =
      Real.sqrt (2 * Real.pi) / Real.Gamma (1 / 2 + a) := by
    have hG : Complex.Gamma (1 / 2 + (a : ℂ)) = (Real.Gamma (1 / 2 + a) : ℂ) := by
      have : (1 / 2 + (a : ℂ)) = ((1 / 2 + a : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.Gamma_ofReal]
    rw [hG, ← Complex.ofReal_div, Complex.ofReal_re]
  rw [hL, hR] at h
  exact h

/-- `molv_bar` for `pcU, pcV` derived conditionally from `env_bar` with constant `C > 0`,
with explicit constants `c_bar = 1 / C` and `C_bar = C`. -/
theorem molv_bar_of_env_bar {C : ℝ} (hC : 0 < C)
    (h : ∀ a, 0 < a → ∀ z,
      Real.sqrt ((kappaBal a * pcU a z) ^ 2 + (kappaBal a * deriv (pcU a) z) ^ 2 / k2 a z)
        ≤ C * Ebar a z * Mbal a z ∧
      Real.sqrt ((kappaBal a * pcU a (-z)) ^ 2 + (kappaBal a * deriv (fun w => pcU a (-w)) z) ^ 2 / k2 a z)
        ≤ C * (Ebar a z)⁻¹ * Mbal a z) :
    ∀ a, 0 < a → ∀ z,
      (1 / C) * (kappaBal a)⁻¹ * Ebar a z * Mbal a z ≤ Molv pcU pcV a z ∧
      Molv pcU pcV a z ≤ C * (kappaBal a)⁻¹ * Ebar a z * Mbal a z := by
  intro a ha z
  obtain ⟨hκ, hκ2⟩ := kappaBal_pos_props ha
  have hk := k2_pos a z
  have hm := Mbal_pos a z
  have hm2 := Mbal_sq_mul a z
  have hEb : 0 < Ebar a z := by unfold Ebar; positivity
  have hMolv : Molv pcU pcV a z = Real.sqrt (pcU a z ^ 2 + deriv (pcU a) z ^ 2 / k2 a z) := by
    unfold Molv; exact ite_eq_left_iff.mpr (fun h => absurd (Or.inr ha) h)
  rw [hMolv]
  obtain ⟨h1, h2⟩ := h a ha z
  set κ := kappaBal a
  set EU := Real.sqrt (pcU a z ^ 2 + deriv (pcU a) z ^ 2 / k2 a z)
  have hEU_scale : κ * EU = molvEnv2 (k2 a z) (κ * pcU a z) (κ * deriv (pcU a) z) := by
    unfold molvEnv2
    rw [show (κ * pcU a z) ^ 2 + (κ * deriv (pcU a) z) ^ 2 / k2 a z
        = κ ^ 2 * (pcU a z ^ 2 + deriv (pcU a) z ^ 2 / k2 a z) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hκ.le]
  refine ⟨?_, ?_⟩
  · -- Lower bound via pc_wronsk_neg + env_bar.2
    set x := κ * pcU a z
    set x' := κ * deriv (pcU a) z
    set y := κ * pcU a (-z)
    set y' := κ * deriv (fun w => pcU a (-w)) z
    have hW : x * y' - x' * y = 1 := by
      have hw := pc_wronsk_neg a z
      have : x * y' - x' * y = κ ^ 2 *
          (pcU a z * deriv (fun w => pcU a (-w)) z - deriv (pcU a) z * pcU a (-z)) := by
        dsimp [x, x', y, y']; ring
      rw [this, hw, hκ2]
    have hcs := wronsk_le_molvEnv2 hk x x' y y'
    rw [hW, abs_one, ← hEU_scale] at hcs
    have h1' : 1 ≤ Real.sqrt (k2 a z) * (κ * EU) * (C * (Ebar a z)⁻¹ * Mbal a z) :=
      hcs.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
    have hEb_bd : Ebar a z * Mbal a z ≤ C * (κ * EU) := by
      have hmul : Ebar a z * Mbal a z ≤ Ebar a z * Mbal a z *
          (Real.sqrt (k2 a z) * (κ * EU) * (C * (Ebar a z)⁻¹ * Mbal a z)) :=
        le_mul_of_one_le_right (by positivity) h1'
      have heq : Ebar a z * Mbal a z *
          (Real.sqrt (k2 a z) * (κ * EU) * (C * (Ebar a z)⁻¹ * Mbal a z))
          = (Real.sqrt (k2 a z) * Mbal a z ^ 2) * (Ebar a z * (Ebar a z)⁻¹) * (C * (κ * EU)) := by ring
      rw [heq, hm2, mul_inv_cancel₀ hEb.ne', one_mul, one_mul] at hmul
      exact hmul
    rw [show (1 / C) * κ⁻¹ * Ebar a z * Mbal a z = (Ebar a z * Mbal a z) / (C * κ) by ring,
      div_le_iff₀ (mul_pos hC hκ)]
    linarith
  · -- Upper bound directly from env_bar.1
    rw [show C * κ⁻¹ * Ebar a z * Mbal a z = (C * Ebar a z * Mbal a z) / κ by ring,
      le_div_iff₀ hκ, mul_comm _ κ, hEU_scale]
    exact h1

/-! ### Axiom pins -/

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.env_bar_second_of_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms env_bar_second_of_first

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.molv_well_of_env_well' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms molv_well_of_env_well

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.pc_wronsk_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pc_wronsk_neg

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.molv_bar_of_env_bar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms molv_bar_of_env_bar

end FormalResearch.JacobiEigenvectors.Charts
