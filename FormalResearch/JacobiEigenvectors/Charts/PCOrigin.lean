module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Charts.PCExact

/-!
# Paper J, Layer 4 (phase B2, E0): the Gamma normalisation of `U, V` at the origin

`LAYER4_PCF_PLAN.md`, section 3, step E0.  The initial values of the actual functions `pcU, pcV` (`Charts/PCExact.lean`) are explicit
Gamma quotients (DLMF 12.2.6--12.2.9 as vendored):

`U(a,0) = sqrt(pi) 2^{-(a/2+1/4)} / Gamma(3/4+a/2)`, `U'(a,0) = -sqrt(pi) 2^{-(a/2-1/4)} / Gamma(1/4+a/2)`,
`V(a,0) = pi 2^{a/2+1/4} / (Gamma(3/4-a/2)^2 Gamma(1/4+a/2))`, `V'(a,0) = pi 2^{a/2+3/4} / (Gamma(1/4-a/2)^2 Gamma(3/4+a/2))`.

Here: these four values for real `a` (real `Gamma`, `pcU_zero`, `pcUD_zero`, `pcV_zero`, `pcVD_zero`), the Wendel-type bound
`y / sqrt(y+1/2) <= Gamma(y+1/2)/Gamma(y) <= sqrt y` from log-convexity (`Gamma_add_half_le`, `le_Gamma_add_half`), and the **origin envelopes**.
With `E_U(a,0)^2 = U(a,0)^2 + U'(a,0)^2 / k_2(a,0)` (`EU0`), `E_V` likewise (`EV0`), `kappa = kappaBal a`, `M_bal = Mbal a 0 = k_2(a,0)^{-1/4}`:

* `a <= 0` (`origin_well_U`, `origin_well_V`): `1/2 kappa^{-1} M_bal <= E_U <= 2 kappa^{-1} M_bal` and `1/2 M_bal <= sqrt(pi/2) kappa^{-1} E_V <= 2 M_bal`;
* `a > 0` (`origin_bar_U`): `1/2 kappa^{-1} M_bal <= E_U <= 2 kappa^{-1} M_bal`;

and the same in the shape of the `PCEnvelopeFacts` fields at `z = 0` (`origin_env_well_U`, `origin_env_well_V`, `origin_env_bar`, using `E_well(a,0) = E_bar(a,0) = 1`).
The constants `1/2, 2` are absolute.  For `a <= 0` the proof is resonance-free: by the reflection formula `U(a,0)` and `U'(a,0)` carry the factors `sin theta`,
`cos theta`, `theta = pi (1/4 - a/2)`, so that `E_U^2` is a convex combination of two terms of the same size (`sin^2 + cos^2 = 1`, `convex_bounds`); the sizes compare through
`Gamma(x+3/4) / Gamma(x+1/4) ~ sqrt(k_2)` (`Gamma_ratio_origin`, with `7/25 <= t <= 7/4`) and the duplication formula (`Gamma_dup_origin`).
`kappaBal` jumps by the factor `(pi/2)^{1/4}` at `a = 0` (`pi^{-1/4}` from the left, `(2 pi)^{-1/4} pi^{1/4}` from the right) (finding F6 of the plan), hence the two ranges.  mpmath check (scratch): `kappa E_U / M_bal` lies in `[0.88, 1.28]` over `a in [-300, 300]`.
Also `pcU_zero_zero_pos : 0 < U(0,0)`, the sign anchor for `U_pos`.

All statements are *proved* (no hypothesis).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.Charts

open DLMF.Confluent Real

/-! ### The four initial values, real form -/

private lemma cG (s : ℝ) : Complex.Gamma (s : ℂ) = ((Real.Gamma s : ℝ) : ℂ) := Complex.Gamma_ofReal s

private lemma c2pow (y : ℝ) : (2 : ℂ) ^ (y : ℂ) = (((2 : ℝ) ^ y : ℝ) : ℂ) := by
  rw [Complex.ofReal_cpow (by norm_num)]; norm_num

/-- `U(a,0)` for real `a` (DLMF 12.2.6). -/
theorem pcU_zero (a : ℝ) :
    pcU a 0 = Real.sqrt π * (2 : ℝ) ^ (-(a / 2 + 1 / 4)) * (Real.Gamma (3 / 4 + a / 2))⁻¹ := by
  apply Complex.ofReal_injective
  have h := parabolicCylinderU_zero' (a : ℂ)
  rw [← pcU_ofReal a 0] at *
  have e : ((0 : ℝ) : ℂ) = 0 := by simp
  rw [e, h]
  have e1 : (-((a : ℂ) / 2 + 1 / 4)) = ((-(a / 2 + 1 / 4) : ℝ) : ℂ) := by push_cast; ring
  have e2 : (3 / 4 + (a : ℂ) / 2) = ((3 / 4 + a / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [e1, e2, c2pow, cG]
  push_cast; rfl

/-- `U'(a,0)` for real `a` (DLMF 12.2.7). -/
theorem pcUD_zero (a : ℝ) :
    pcUD a 0 = -(Real.sqrt π * (2 : ℝ) ^ (-(a / 2 - 1 / 4)) * (Real.Gamma (1 / 4 + a / 2))⁻¹) := by
  have h := parabolicCylinderUDeriv_zero' (a : ℂ)
  have e1 : (-((a : ℂ) / 2 - 1 / 4)) = ((-(a / 2 - 1 / 4) : ℝ) : ℂ) := by push_cast; ring
  have e2 : (1 / 4 + (a : ℂ) / 2) = ((1 / 4 + a / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [e1, e2, c2pow, cG] at h
  have h2 : pcUD a 0 = (parabolicCylinderUDeriv (a : ℂ) 0).re := by simp [pcUD]
  rw [h2, h]
  have : (-((Real.sqrt π : ℂ) * (((2 : ℝ) ^ (-(a / 2 - 1 / 4)) : ℝ) : ℂ) *
      (((Real.Gamma (1 / 4 + a / 2)) : ℝ) : ℂ)⁻¹)) =
      ((-(Real.sqrt π * (2 : ℝ) ^ (-(a / 2 - 1 / 4)) * (Real.Gamma (1 / 4 + a / 2))⁻¹) : ℝ) : ℂ) := by
    push_cast; ring
  rw [this, Complex.ofReal_re]

/-- `V(a,0)` for real `a` (DLMF 12.2.8). -/
theorem pcV_zero (a : ℝ) :
    pcV a 0 = π * (2 : ℝ) ^ (a / 2 + 1 / 4) / (Real.Gamma (3 / 4 - a / 2) ^ 2 * Real.Gamma (1 / 4 + a / 2)) := by
  have h := parabolicCylinderV_zero (a : ℂ)
  have e1 : ((a : ℂ) / 2 + 1 / 4) = ((a / 2 + 1 / 4 : ℝ) : ℂ) := by push_cast; ring
  have e2 : (3 / 4 - (a : ℂ) / 2) = ((3 / 4 - a / 2 : ℝ) : ℂ) := by push_cast; ring
  have e3 : (1 / 4 + (a : ℂ) / 2) = ((1 / 4 + a / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [e1, e2, e3, c2pow, cG, cG] at h
  have h2 : pcV a 0 = (parabolicCylinderV (a : ℂ) 0).re := by simp [pcV]
  rw [h2, h]
  have : ((π : ℂ) * (((2 : ℝ) ^ (a / 2 + 1 / 4) : ℝ) : ℂ) /
      ((((Real.Gamma (3 / 4 - a / 2)) : ℝ) : ℂ) ^ 2 * (((Real.Gamma (1 / 4 + a / 2)) : ℝ) : ℂ))) =
      ((π * (2 : ℝ) ^ (a / 2 + 1 / 4) / (Real.Gamma (3 / 4 - a / 2) ^ 2 * Real.Gamma (1 / 4 + a / 2)) : ℝ) : ℂ) := by
    push_cast; rfl
  rw [this, Complex.ofReal_re]

/-- `V'(a,0)` for real `a` (DLMF 12.2.9). -/
theorem pcVD_zero (a : ℝ) :
    pcVD a 0 = π * (2 : ℝ) ^ (a / 2 + 3 / 4) / (Real.Gamma (1 / 4 - a / 2) ^ 2 * Real.Gamma (3 / 4 + a / 2)) := by
  have h := parabolicCylinderVDeriv_zero (a : ℂ)
  have e1 : ((a : ℂ) / 2 + 3 / 4) = ((a / 2 + 3 / 4 : ℝ) : ℂ) := by push_cast; ring
  have e2 : (1 / 4 - (a : ℂ) / 2) = ((1 / 4 - a / 2 : ℝ) : ℂ) := by push_cast; ring
  have e3 : (3 / 4 + (a : ℂ) / 2) = ((3 / 4 + a / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [e1, e2, e3, c2pow, cG, cG] at h
  have h2 : pcVD a 0 = (parabolicCylinderVDeriv (a : ℂ) 0).re := by simp [pcVD]
  rw [h2, h]
  have : ((π : ℂ) * (((2 : ℝ) ^ (a / 2 + 3 / 4) : ℝ) : ℂ) /
      ((((Real.Gamma (1 / 4 - a / 2)) : ℝ) : ℂ) ^ 2 * (((Real.Gamma (3 / 4 + a / 2)) : ℝ) : ℂ))) =
      ((π * (2 : ℝ) ^ (a / 2 + 3 / 4) / (Real.Gamma (1 / 4 - a / 2) ^ 2 * Real.Gamma (3 / 4 + a / 2)) : ℝ) : ℂ) := by
    push_cast; rfl
  rw [this, Complex.ofReal_re]

/-! ### A Wendel-type bound for `Gamma(y + 1/2) / Gamma(y)` -/

/-- `Gamma(y + 1/2) <= sqrt y Gamma(y)` (log-convexity of `Gamma`). -/
theorem Gamma_add_half_le {y : ℝ} (hy : 0 < y) : Real.Gamma (y + 1 / 2) ≤ Real.sqrt y * Real.Gamma y := by
  have h := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma (s := y) (t := y + 1) (a := 1 / 2) (b := 1 / 2)
    hy (by linarith) (by norm_num) (by norm_num) (by norm_num)
  have e : 1 / 2 * y + 1 / 2 * (y + 1) = y + 1 / 2 := by ring
  rw [e, Real.Gamma_add_one hy.ne'] at h
  have hg : 0 < Real.Gamma y := Real.Gamma_pos_of_pos hy
  have h2 : Real.Gamma y ^ (1 / 2 : ℝ) * (y * Real.Gamma y) ^ (1 / 2 : ℝ) = Real.sqrt y * Real.Gamma y := by
    rw [← Real.mul_rpow hg.le (by positivity), ← Real.sqrt_eq_rpow]
    rw [show Real.Gamma y * (y * Real.Gamma y) = y * Real.Gamma y ^ 2 by ring, Real.sqrt_mul hy.le,
      Real.sqrt_sq hg.le]
  rw [h2] at h
  exact h

/-- `y / sqrt(y + 1/2) * Gamma(y) <= Gamma(y + 1/2)` (log-convexity of `Gamma`). -/
theorem le_Gamma_add_half {y : ℝ} (hy : 0 < y) : y / Real.sqrt (y + 1 / 2) * Real.Gamma y ≤ Real.Gamma (y + 1 / 2) := by
  have hy2 : 0 < y + 1 / 2 := by linarith
  have h := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma (s := y + 1 / 2) (t := y + 3 / 2) (a := 1 / 2)
    (b := 1 / 2) hy2 (by linarith) (by norm_num) (by norm_num) (by norm_num)
  have e : 1 / 2 * (y + 1 / 2) + 1 / 2 * (y + 3 / 2) = y + 1 := by ring
  have e2 : y + 3 / 2 = (y + 1 / 2) + 1 := by ring
  rw [e, e2, Real.Gamma_add_one hy2.ne', Real.Gamma_add_one hy.ne'] at h
  have hg : 0 < Real.Gamma (y + 1 / 2) := Real.Gamma_pos_of_pos hy2
  have h2 : Real.Gamma (y + 1 / 2) ^ (1 / 2 : ℝ) * ((y + 1 / 2) * Real.Gamma (y + 1 / 2)) ^ (1 / 2 : ℝ) =
      Real.sqrt (y + 1 / 2) * Real.Gamma (y + 1 / 2) := by
    rw [← Real.mul_rpow hg.le (by positivity), ← Real.sqrt_eq_rpow]
    rw [show Real.Gamma (y + 1 / 2) * ((y + 1 / 2) * Real.Gamma (y + 1 / 2)) =
      (y + 1 / 2) * Real.Gamma (y + 1 / 2) ^ 2 by ring, Real.sqrt_mul hy2.le, Real.sqrt_sq hg.le]
  rw [h2] at h
  have hs : 0 < Real.sqrt (y + 1 / 2) := Real.sqrt_pos.mpr hy2
  rw [div_mul_eq_mul_div, div_le_iff₀ hs]
  nlinarith

/-- `k_2(a, 0) = |a|` for `|a| >= 1` and `1` for `|a| < 1`. -/
theorem k2_zero (a : ℝ) : k2 a 0 = if 1 ≤ |a| then |a| else 1 := by
  unfold k2
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, zero_add]
  split_ifs with h
  · rw [max_eq_left h]
    exact max_eq_left (by
      calc |a| ^ ((1 : ℝ) / 3) ≤ |a| ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le h (by norm_num)
        _ = |a| := Real.rpow_one _)
  · have h := not_le.mp h
    rw [max_eq_right h.le, Real.one_rpow]
    exact max_eq_right h.le

/-- **Gamma ratio at the origin.**  Let `G1 = Gamma(x + 1/4)`, `G3 = Gamma(x + 3/4)` and `k = max(2x, 1)` for `x >= 1/2`, `k = 1` for `x < 1/2`
(the value `k_2(a,0)` for `|a| = 2x`).  Then `(7/25) sqrt k G1 <= G3 <= (7/4) sqrt k G1`. -/
theorem Gamma_ratio_origin {x k : ℝ} (hx : 0 ≤ x) (hk : (1 / 2 ≤ x ∧ k = 2 * x) ∨ (x < 1 / 2 ∧ k = 1)) :
    7 / 25 * (Real.sqrt k * Real.Gamma (x + 1 / 4)) ≤ Real.Gamma (x + 3 / 4) ∧
      Real.Gamma (x + 3 / 4) ≤ 7 / 4 * (Real.sqrt k * Real.Gamma (x + 1 / 4)) := by
  set y : ℝ := x + 1 / 4 with hy
  have hy0 : 0 < y := by rw [hy]; linarith
  have hG1 : 0 < Real.Gamma y := Real.Gamma_pos_of_pos hy0
  have e : x + 3 / 4 = y + 1 / 2 := by rw [hy]; ring
  rw [e]
  have hk0 : 0 < k := by rcases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> [rw [h2]; rw [h2]] <;> linarith
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk0
  constructor
  · have h1 := le_Gamma_add_half hy0
    have h2 : 7 / 25 * Real.sqrt k ≤ y / Real.sqrt (y + 1 / 2) := by
      have hs2 : 0 < Real.sqrt (y + 1 / 2) := Real.sqrt_pos.mpr (by linarith)
      rw [le_div_iff₀ hs2, mul_assoc, ← Real.sqrt_mul hk0.le]
      have : Real.sqrt (k * (y + 1 / 2)) ≤ 25 / 7 * y := by
        rw [Real.sqrt_le_left (by positivity)]
        rcases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h2, hy]; nlinarith
        · rw [h2, hy]; nlinarith
      linarith
    calc 7 / 25 * (Real.sqrt k * Real.Gamma y) = (7 / 25 * Real.sqrt k) * Real.Gamma y := by ring
      _ ≤ y / Real.sqrt (y + 1 / 2) * Real.Gamma y := by gcongr
      _ ≤ _ := h1
  · have h1 := Gamma_add_half_le hy0
    have h2 : Real.sqrt y ≤ 7 / 4 * Real.sqrt k := by
      have : 7 / 4 * Real.sqrt k = Real.sqrt ((7 / 4) ^ 2 * k) := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
      rw [this]
      apply Real.sqrt_le_sqrt
      rcases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h2, hy]; nlinarith
      · rw [h2, hy]; nlinarith
    calc Real.Gamma (y + 1 / 2) ≤ Real.sqrt y * Real.Gamma y := h1
      _ ≤ (7 / 4 * Real.sqrt k) * Real.Gamma y := by gcongr
      _ = _ := by ring

/-! ### Reflection form of the initial values for `a <= 0` -/

/-- `1 / Gamma(1 - s) = Gamma(s) sin(pi s) / pi` for `s > 0` (no pole bookkeeping: both sides vanish when `sin(pi s) = 0`). -/
theorem inv_Gamma_one_sub {s : ℝ} (hs : 0 < s) :
    (Real.Gamma (1 - s))⁻¹ = Real.Gamma s * Real.sin (π * s) / π := by
  have h := Real.Gamma_mul_Gamma_one_sub s
  have hg : 0 < Real.Gamma s := Real.Gamma_pos_of_pos hs
  by_cases h0 : Real.sin (π * s) = 0
  · rw [h0, div_zero] at h
    have : Real.Gamma (1 - s) = 0 := by
      rcases mul_eq_zero.mp h with h1 | h1
      · exact absurd h1 hg.ne'
      · exact h1
    rw [this, h0]; simp
  · have h1 : Real.Gamma (1 - s) = π / Real.sin (π * s) / Real.Gamma s := by
      rw [eq_div_iff hg.ne', mul_comm]; exact h
    rw [h1]
    field_simp

/-- The initial values for `a = -2x`, `x >= 0`, in terms of `Q = 2^{x - 1/4}`, `G1 = Gamma(x+1/4)`, `G3 = Gamma(x+3/4)`,
`sin theta`, `cos theta` with `theta = pi (x + 1/4)`. -/
theorem origin_values_well {x : ℝ} (hx : 0 ≤ x) :
    pcU (-(2 * x)) 0 = (2 : ℝ) ^ (x - 1 / 4) * Real.Gamma (x + 1 / 4) * Real.sin (π * (x + 1 / 4)) / Real.sqrt π ∧
    pcUD (-(2 * x)) 0 = -(Real.sqrt 2 * (2 : ℝ) ^ (x - 1 / 4) * Real.Gamma (x + 3 / 4) * Real.cos (π * (x + 1 / 4)) / Real.sqrt π) ∧
    pcV (-(2 * x)) 0 = ((2 : ℝ) ^ (x - 1 / 4))⁻¹ * Real.cos (π * (x + 1 / 4)) / Real.Gamma (x + 3 / 4) ∧
    pcVD (-(2 * x)) 0 = Real.sqrt 2 * ((2 : ℝ) ^ (x - 1 / 4))⁻¹ * Real.sin (π * (x + 1 / 4)) / Real.Gamma (x + 1 / 4) := by
  have hπ : 0 < π := Real.pi_pos
  have hsπ : 0 < Real.sqrt π := Real.sqrt_pos.mpr hπ
  have hs2 : Real.sqrt 2 = (2 : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow 2
  have hG1 : 0 < Real.Gamma (x + 1 / 4) := Real.Gamma_pos_of_pos (by linarith)
  have hG3 : 0 < Real.Gamma (x + 3 / 4) := Real.Gamma_pos_of_pos (by linarith)
  have hcos : Real.sin (π * (x + 3 / 4)) = Real.cos (π * (x + 1 / 4)) := by
    rw [show π * (x + 3 / 4) = π * (x + 1 / 4) + π / 2 by ring, Real.sin_add_pi_div_two]
  have hsq : Real.sqrt π * Real.sqrt π = π := Real.mul_self_sqrt hπ.le
  have r1 : (Real.Gamma (3 / 4 - x))⁻¹ = Real.Gamma (x + 1 / 4) * Real.sin (π * (x + 1 / 4)) / π := by
    rw [show 3 / 4 - x = 1 - (x + 1 / 4) by ring]; exact inv_Gamma_one_sub (by linarith)
  have r3 : (Real.Gamma (1 / 4 - x))⁻¹ = Real.Gamma (x + 3 / 4) * Real.cos (π * (x + 1 / 4)) / π := by
    rw [show 1 / 4 - x = 1 - (x + 3 / 4) by ring, inv_Gamma_one_sub (by linarith), hcos]
  have p1 : (2 : ℝ) ^ (x + 1 / 4) = (2 : ℝ) ^ (x - 1 / 4) * Real.sqrt 2 := by
    rw [hs2, ← Real.rpow_add (by norm_num)]; ring_nf
  have p2 : (2 : ℝ) ^ (1 / 4 - x) = ((2 : ℝ) ^ (x - 1 / 4))⁻¹ := by
    rw [← Real.rpow_neg (by norm_num)]; ring_nf
  have p3 : (2 : ℝ) ^ (3 / 4 - x) = ((2 : ℝ) ^ (x - 1 / 4))⁻¹ * Real.sqrt 2 := by
    rw [hs2, show (3 / 4 - x : ℝ) = (1 / 4 - x) + 1 / 2 by ring, Real.rpow_add (by norm_num), p2]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [pcU_zero, show -(-(2 * x) / 2 + 1 / 4) = x - 1 / 4 by ring, show 3 / 4 + -(2 * x) / 2 = 3 / 4 - x by ring, r1]
    field_simp
    rw [Real.sq_sqrt hπ.le]
  · rw [pcUD_zero, show -(-(2 * x) / 2 - 1 / 4) = x + 1 / 4 by ring, show 1 / 4 + -(2 * x) / 2 = 1 / 4 - x by ring, r3, p1]
    field_simp
    rw [Real.sq_sqrt hπ.le]
  · rw [pcV_zero, show -(2 * x) / 2 + 1 / 4 = 1 / 4 - x by ring, show 3 / 4 - -(2 * x) / 2 = x + 3 / 4 by ring,
      show 1 / 4 + -(2 * x) / 2 = 1 / 4 - x by ring, p2]
    rw [div_eq_mul_inv (π * _), mul_inv, r3]
    field_simp
  · rw [pcVD_zero, show -(2 * x) / 2 + 3 / 4 = 3 / 4 - x by ring, show 1 / 4 - -(2 * x) / 2 = x + 1 / 4 by ring,
      show 3 / 4 + -(2 * x) / 2 = 3 / 4 - x by ring, p3]
    rw [div_eq_mul_inv (π * _), mul_inv, r1]
    field_simp

/-! ### The algebra of the three origin envelopes -/

theorem sqrt_pi_bounds : 177 / 100 ≤ Real.sqrt π ∧ Real.sqrt π ≤ 178 / 100 := by
  have h1 := Real.pi_gt_d2
  have h2 := Real.pi_lt_d2
  constructor
  · apply Real.le_sqrt_of_sq_le; nlinarith
  · rw [Real.sqrt_le_left (by norm_num)]; nlinarith

/-- the two-term convexity bound used by all three origin envelopes: for `s^2 + c^2 = 1`, `lam1 * 1 + ... `. -/
theorem convex_bounds {s c m1 m2 lo hi : ℝ} (hsc : s ^ 2 + c ^ 2 = 1) (h1 : lo ≤ m1) (h2 : lo ≤ m2) (h3 : m1 ≤ hi) (h4 : m2 ≤ hi) :
    lo ≤ m1 * s ^ 2 + m2 * c ^ 2 ∧ m1 * s ^ 2 + m2 * c ^ 2 ≤ hi := by
  have hs : 0 ≤ s ^ 2 := sq_nonneg s
  have hc : 0 ≤ c ^ 2 := sq_nonneg c
  have el : lo = lo * (s ^ 2 + c ^ 2) := by rw [hsc]; ring
  have eh : hi = hi * (s ^ 2 + c ^ 2) := by rw [hsc]; ring
  constructor
  · nlinarith [mul_nonneg hs (sub_nonneg.mpr h1), mul_nonneg hc (sub_nonneg.mpr h2)]
  · nlinarith [mul_nonneg hs (sub_nonneg.mpr h3), mul_nonneg hc (sub_nonneg.mpr h4)]

/-- `a <= 0`, `U`: with `G3 = t w G1` (`w = sqrt k`), `E_U^2 = (Q G1 s / P)^2 + 2 (Q G3 c / P)^2 / w^2` lies between `A / 4` and `3 A`,
`A = G1 G3 Q^2 / (P w)`. -/
theorem alg_well_U {Q G1 t w s c P : ℝ} (hQ : 0 < Q) (hG1 : 0 < G1) (hw : 0 < w) (hP1 : 177 / 100 ≤ P) (hP2 : P ≤ 178 / 100)
    (hsc : s ^ 2 + c ^ 2 = 1) (ht1 : 7 / 25 ≤ t) (ht2 : t ≤ 7 / 4) :
    (1 / 4) * (G1 * (t * w * G1) * Q ^ 2 / P / w) ≤
        (Q * G1 * s / P) ^ 2 + (Real.sqrt 2 * Q * (t * w * G1) * c / P) ^ 2 / w ^ 2 ∧
      (Q * G1 * s / P) ^ 2 + (Real.sqrt 2 * Q * (t * w * G1) * c / P) ^ 2 / w ^ 2 ≤
        3 * (G1 * (t * w * G1) * Q ^ 2 / P / w) := by
  have hP : 0 < P := by linarith
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have e1 : (Q * G1 * s / P) ^ 2 + (Real.sqrt 2 * Q * (t * w * G1) * c / P) ^ 2 / w ^ 2 =
      Q ^ 2 * G1 ^ 2 / P ^ 2 * (1 * s ^ 2 + 2 * t ^ 2 * c ^ 2) := by
    field_simp; rw [h2]; ring
  have e2 : G1 * (t * w * G1) * Q ^ 2 / P / w = Q ^ 2 * G1 ^ 2 / P ^ 2 * (P * t) := by
    field_simp
  rw [e1, e2]
  have hpos : 0 < Q ^ 2 * G1 ^ 2 / P ^ 2 := by positivity
  have key := convex_bounds (m1 := 1) (m2 := 2 * t ^ 2) (lo := P * t / 4) (hi := 3 * (P * t)) hsc
    (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left key.1 hpos.le]
  · nlinarith [mul_le_mul_of_nonneg_left key.2 hpos.le]

/-- `a <= 0`, `V`: `(P^2/2) Gamma(1/2-a) E_V^2 w` lies between `1/4` and `4` (`Gamma(1/2-a) = G1 G3 Q^2 / P`). -/
theorem alg_well_V {Q G1 t w s c P : ℝ} (hQ : 0 < Q) (hG1 : 0 < G1) (ht0 : 0 < t) (hw : 0 < w) (hP1 : 177 / 100 ≤ P) (_hP2 : P ≤ 178 / 100)
    (hsc : s ^ 2 + c ^ 2 = 1) (ht1 : 7 / 25 ≤ t) (ht2 : t ≤ 7 / 4) :
    1 / 4 * (1 / w) ≤ (P ^ 2 / 2) * (G1 * (t * w * G1) * Q ^ 2 / P) *
        ((Q⁻¹ * c / (t * w * G1)) ^ 2 + (Real.sqrt 2 * Q⁻¹ * s / G1) ^ 2 / w ^ 2) ∧
      (P ^ 2 / 2) * (G1 * (t * w * G1) * Q ^ 2 / P) *
        ((Q⁻¹ * c / (t * w * G1)) ^ 2 + (Real.sqrt 2 * Q⁻¹ * s / G1) ^ 2 / w ^ 2) ≤ 4 * (1 / w) := by
  have hP : 0 < P := by linarith
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have e1 : (P ^ 2 / 2) * (G1 * (t * w * G1) * Q ^ 2 / P) *
        ((Q⁻¹ * c / (t * w * G1)) ^ 2 + (Real.sqrt 2 * Q⁻¹ * s / G1) ^ 2 / w ^ 2) =
      (1 / w) * ((P * t) * s ^ 2 + (P / (2 * t)) * c ^ 2) := by
    field_simp; rw [h2]; ring
  rw [e1]
  have key := convex_bounds (m1 := P * t) (m2 := P / (2 * t)) (lo := 1 / 4) (hi := 4) hsc
    (by nlinarith) (by rw [le_div_iff₀ (by positivity)]; nlinarith) (by nlinarith)
    (by rw [div_le_iff₀ (by positivity)]; nlinarith)
  have hw' : 0 < 1 / w := by positivity
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left key.1 hw'.le]
  · nlinarith [mul_le_mul_of_nonneg_left key.2 hw'.le]

/-- `a > 0`, `U`: with `Q' = 2^{-x-1/4}`, `E_U^2 = (P Q' / G3)^2 + (P sqrt 2 Q' / G1)^2 / w^2` lies between `1/4` and `3` times
`2 sqrt 2 P^2 Q'^2 / (G1 G3 w)` (`= kappa^{-2} M^2`). -/
theorem alg_bar_U {Q G1 t w P : ℝ} (hQ : 0 < Q) (hG1 : 0 < G1) (ht0 : 0 < t) (hw : 0 < w) (hP1 : 177 / 100 ≤ P) (_hP2 : P ≤ 178 / 100)
    (ht1 : 7 / 25 ≤ t) (ht2 : t ≤ 7 / 4) :
    1 / 4 * (2 * Real.sqrt 2 * P ^ 2 * Q ^ 2 / (G1 * (t * w * G1) * w)) ≤
        (P * Q / (t * w * G1)) ^ 2 + (P * Real.sqrt 2 * Q / G1) ^ 2 / w ^ 2 ∧
      (P * Q / (t * w * G1)) ^ 2 + (P * Real.sqrt 2 * Q / G1) ^ 2 / w ^ 2 ≤
        3 * (2 * Real.sqrt 2 * P ^ 2 * Q ^ 2 / (G1 * (t * w * G1) * w)) := by
  have hP : 0 < P := by linarith
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2' : Real.sqrt 2 < 3 / 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hs2'' : 1 < Real.sqrt 2 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have e1 : (P * Q / (t * w * G1)) ^ 2 + (P * Real.sqrt 2 * Q / G1) ^ 2 / w ^ 2 =
      (2 * Real.sqrt 2 * P ^ 2 * Q ^ 2 / (G1 * (t * w * G1) * w)) * ((1 / t + 2 * t) / (2 * Real.sqrt 2)) := by
    field_simp; rw [h2]
  rw [e1]
  have hpos : 0 < 2 * Real.sqrt 2 * P ^ 2 * Q ^ 2 / (G1 * (t * w * G1) * w) := by positivity
  have hr1 : 1 / 4 ≤ (1 / t + 2 * t) / (2 * Real.sqrt 2) := by
    rw [le_div_iff₀ (by positivity)]
    have : 4 / 7 ≤ 1 / t := by rw [le_div_iff₀ ht0]; nlinarith
    nlinarith
  have hr2 : (1 / t + 2 * t) / (2 * Real.sqrt 2) ≤ 3 := by
    rw [div_le_iff₀ (by positivity)]
    have : 1 / t ≤ 25 / 7 := by rw [div_le_iff₀ ht0]; nlinarith
    nlinarith
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hr1 hpos.le]
  · nlinarith [mul_le_mul_of_nonneg_left hr2 hpos.le]

/-! ### `kappa_bal`, `M_bal` and the duplication formula -/

theorem k2_pos (a z : ℝ) : 0 < k2 a z := by
  unfold k2
  refine lt_of_lt_of_le ?_ (le_max_right _ _)
  exact Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (le_max_right _ _)) _

theorem Mbal_sq (a z : ℝ) : Mbal a z ^ 2 = (Real.sqrt (k2 a z))⁻¹ := by
  have hk := k2_pos a z
  have : Mbal a z ^ 2 = k2 a z ^ (-(1 : ℝ) / 2) := by
    unfold Mbal; rw [← Real.rpow_natCast, ← Real.rpow_mul hk.le]; norm_num
  rw [this, show (-(1 : ℝ) / 2) = -(1 / 2) by ring, Real.rpow_neg hk.le, ← Real.sqrt_eq_rpow]

theorem Mbal_pos (a z : ℝ) : 0 < Mbal a z := Real.rpow_pos_of_pos (k2_pos a z) _

theorem kappaBal_pos (a : ℝ) : 0 < kappaBal a := by
  unfold kappaBal
  split_ifs with h
  · exact Real.rpow_pos_of_pos (Real.Gamma_pos_of_pos (by linarith)) _
  · have h := not_le.mp h
    exact mul_pos (Real.rpow_pos_of_pos (by positivity) _)
      (Real.sqrt_pos.mpr (Real.Gamma_pos_of_pos (by linarith)))

theorem kappa_inv_sq_nonpos {a : ℝ} (ha : a ≤ 0) : (kappaBal a)⁻¹ ^ 2 = Real.Gamma (1 / 2 - a) := by
  have hg : 0 < Real.Gamma (1 / 2 - a) := Real.Gamma_pos_of_pos (by linarith)
  unfold kappaBal
  simp only [ha, ↓reduceIte]
  rw [← Real.rpow_neg hg.le, ← Real.rpow_natCast, ← Real.rpow_mul hg.le]
  norm_num

theorem kappa_inv_sq_pos {a : ℝ} (ha : 0 < a) :
    (kappaBal a)⁻¹ ^ 2 = Real.sqrt 2 * Real.sqrt π / Real.Gamma (1 / 2 + a) := by
  have hg : 0 < Real.Gamma (1 / 2 + a) := Real.Gamma_pos_of_pos (by linarith)
  have h2π : 0 < 2 * π := by positivity
  unfold kappaBal
  simp only [not_le.mpr ha, ↓reduceIte]
  rw [mul_inv, mul_pow, inv_pow, inv_pow, Real.sq_sqrt hg.le]
  have h1 : ((2 * π) ^ (-(1 : ℝ) / 4)) ^ 2 = (Real.sqrt (2 * π))⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h2π.le, show (-(1 : ℝ) / 4) * ((2 : ℕ) : ℝ) = -(1 / 2) by norm_num,
      Real.rpow_neg h2π.le, ← Real.sqrt_eq_rpow]
  rw [h1, inv_inv, Real.sqrt_mul (by norm_num)]
  ring

/-- Legendre duplication at the origin: `Gamma(1/2 + 2x) = Gamma(x+1/4) Gamma(x+3/4) / (sqrt pi 2^{1/2-2x})`. -/
theorem Gamma_dup_origin {x : ℝ} (hx : 0 ≤ x) :
    Real.Gamma (1 / 2 + 2 * x) = Real.Gamma (x + 1 / 4) * Real.Gamma (x + 3 / 4) / (Real.sqrt π * (2 : ℝ) ^ (1 / 2 - 2 * x)) := by
  have h := Real.Gamma_mul_Gamma_add_half (x + 1 / 4)
  rw [show 1 - 2 * (x + 1 / 4) = 1 / 2 - 2 * x by ring, show 2 * (x + 1 / 4) = 1 / 2 + 2 * x by ring,
    show x + 1 / 4 + 1 / 2 = x + 3 / 4 by ring] at h
  have hπ : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have hp : 0 < (2 : ℝ) ^ (1 / 2 - 2 * x) := Real.rpow_pos_of_pos (by norm_num) _
  rw [h]
  field_simp

/-- the origin envelopes -/
def EU0 (a : ℝ) : ℝ := Real.sqrt (pcU a 0 ^ 2 + deriv (pcU a) 0 ^ 2 / k2 a 0)
def EV0 (a : ℝ) : ℝ := Real.sqrt (pcV a 0 ^ 2 + deriv (pcV a) 0 ^ 2 / k2 a 0)

theorem k2_zero_cases {x : ℝ} (_hx : 0 ≤ x) (σ : ℝ) (hσ : |σ| = 2 * x) :
    (1 / 2 ≤ x ∧ k2 σ 0 = 2 * x) ∨ (x < 1 / 2 ∧ k2 σ 0 = 1) := by
  rw [k2_zero, hσ]
  by_cases h : 1 ≤ 2 * x
  · left; simp only [h, ↓reduceIte]; exact ⟨by linarith, trivial⟩
  · right; simp only [h, ↓reduceIte]; exact ⟨by linarith, trivial⟩

/-- `1 / 2 * kappa^{-1} M_bal <= E_U(a,0) <= 2 kappa^{-1} M_bal` for `a <= 0`. -/
theorem origin_well_U {a : ℝ} (ha : a ≤ 0) :
    1 / 2 * ((kappaBal a)⁻¹ * Mbal a 0) ≤ EU0 a ∧ EU0 a ≤ 2 * ((kappaBal a)⁻¹ * Mbal a 0) := by
  obtain ⟨x, hx, rfl⟩ : ∃ x, 0 ≤ x ∧ a = -(2 * x) := ⟨-a / 2, by linarith, by ring⟩
  have hk := k2_zero_cases hx (-(2 * x)) (by rw [abs_neg, abs_of_nonneg (by linarith)])
  have hk0 := k2_pos (-(2 * x)) 0
  set k := k2 (-(2 * x)) 0 with hkdef
  have hw : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk0
  set w := Real.sqrt k with hwdef
  have hG1 : 0 < Real.Gamma (x + 1 / 4) := Real.Gamma_pos_of_pos (by linarith)
  have hG3 : 0 < Real.Gamma (x + 3 / 4) := Real.Gamma_pos_of_pos (by linarith)
  obtain ⟨hr1, hr2⟩ := Gamma_ratio_origin hx hk
  set G1 := Real.Gamma (x + 1 / 4) with hG1d
  set G3 := Real.Gamma (x + 3 / 4) with hG3d
  set t := G3 / (w * G1) with htd
  have ht3 : G3 = t * w * G1 := by rw [htd]; field_simp
  have ht1 : 7 / 25 ≤ t := by rw [htd, le_div_iff₀ (by positivity)]; linarith
  have ht2 : t ≤ 7 / 4 := by rw [htd, div_le_iff₀ (by positivity)]; linarith
  obtain ⟨hU0, hU1, -, -⟩ := origin_values_well hx
  set Q := (2 : ℝ) ^ (x - 1 / 4) with hQd
  have hQ : 0 < Q := Real.rpow_pos_of_pos (by norm_num) _
  set P := Real.sqrt π with hPd
  have hP1 : 177 / 100 ≤ P := sqrt_pi_bounds.1
  have hP2 : P ≤ 178 / 100 := sqrt_pi_bounds.2
  have hsc := Real.sin_sq_add_cos_sq (π * (x + 1 / 4))
  have hdup : Real.Gamma (1 / 2 + 2 * x) = G1 * G3 / (P * (2 : ℝ) ^ (1 / 2 - 2 * x)) := Gamma_dup_origin hx
  have hQ2 : (2 : ℝ) ^ (1 / 2 - 2 * x) = (Q ^ 2)⁻¹ := by
    rw [hQd, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_neg (by norm_num)]
    norm_num; ring_nf
  have hA : ((kappaBal (-(2 * x)))⁻¹ * Mbal (-(2 * x)) 0) ^ 2 = G1 * G3 * Q ^ 2 / P / w := by
    rw [mul_pow, kappa_inv_sq_nonpos ha, Mbal_sq, ← hkdef, ← hwdef,
      show 1 / 2 - -(2 * x) = 1 / 2 + 2 * x by ring, hdup, hQ2]
    field_simp
  have halg := alg_well_U hQ hG1 hw hP1 hP2 hsc ht1 ht2
  rw [← ht3] at halg
  have hE : EU0 (-(2 * x)) = Real.sqrt ((Q * G1 * Real.sin (π * (x + 1 / 4)) / P) ^ 2 +
      (Real.sqrt 2 * Q * G3 * Real.cos (π * (x + 1 / 4)) / P) ^ 2 / w ^ 2) := by
    unfold EU0
    rw [deriv_pcU, hU0, hU1, neg_sq, Real.sq_sqrt hk0.le, ← hkdef]
  have hA0 : 0 ≤ G1 * G3 * Q ^ 2 / P / w := hA ▸ sq_nonneg _
  have hκM : 0 ≤ (kappaBal (-(2 * x)))⁻¹ * Mbal (-(2 * x)) 0 :=
    mul_nonneg (inv_nonneg.mpr (kappaBal_pos _).le) (Mbal_pos _ _).le
  constructor
  · rw [hE]
    apply Real.le_sqrt_of_sq_le
    calc (1 / 2 * ((kappaBal (-(2 * x)))⁻¹ * Mbal (-(2 * x)) 0)) ^ 2
        = 1 / 4 * (((kappaBal (-(2 * x)))⁻¹ * Mbal (-(2 * x)) 0) ^ 2) := by ring
      _ = 1 / 4 * (G1 * G3 * Q ^ 2 / P / w) := by rw [hA]
      _ ≤ _ := halg.1
  · rw [hE]
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    calc _ ≤ 3 * (G1 * G3 * Q ^ 2 / P / w) := halg.2
      _ ≤ 4 * (G1 * G3 * Q ^ 2 / P / w) := by linarith
      _ = (2 * ((kappaBal (-(2 * x)))⁻¹ * Mbal (-(2 * x)) 0)) ^ 2 := by rw [mul_pow, hA]; ring

/-- `1/2 M_bal <= sqrt(pi/2) kappa^{-1} E_V(a,0) <= 2 M_bal` for `a <= 0`. -/
theorem origin_well_V {a : ℝ} (ha : a ≤ 0) :
    1 / 2 * Mbal a 0 ≤ Real.sqrt (π / 2) * (kappaBal a)⁻¹ * EV0 a ∧
      Real.sqrt (π / 2) * (kappaBal a)⁻¹ * EV0 a ≤ 2 * Mbal a 0 := by
  obtain ⟨x, hx, rfl⟩ : ∃ x, 0 ≤ x ∧ a = -(2 * x) := ⟨-a / 2, by linarith, by ring⟩
  have hk := k2_zero_cases hx (-(2 * x)) (by rw [abs_neg, abs_of_nonneg (by linarith)])
  have hk0 := k2_pos (-(2 * x)) 0
  set k := k2 (-(2 * x)) 0 with hkdef
  have hw : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk0
  have hkw : k = Real.sqrt k ^ 2 := (Real.sq_sqrt hk0.le).symm
  set w := Real.sqrt k with hwdef
  have hG1 : 0 < Real.Gamma (x + 1 / 4) := Real.Gamma_pos_of_pos (by linarith)
  have hG3 : 0 < Real.Gamma (x + 3 / 4) := Real.Gamma_pos_of_pos (by linarith)
  obtain ⟨hr1, hr2⟩ := Gamma_ratio_origin hx hk
  obtain ⟨-, -, hV0, hV1⟩ := origin_values_well hx
  have hQ : 0 < (2 : ℝ) ^ (x - 1 / 4) := Real.rpow_pos_of_pos (by norm_num) _
  have hP1 := sqrt_pi_bounds.1
  have hP2 := sqrt_pi_bounds.2
  have hsc := Real.sin_sq_add_cos_sq (π * (x + 1 / 4))
  have hdup := Gamma_dup_origin hx
  have hQ2 : (2 : ℝ) ^ (1 / 2 - 2 * x) = (((2 : ℝ) ^ (x - 1 / 4)) ^ 2)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_neg (by norm_num)]
    norm_num; ring_nf
  have hPP : Real.sqrt π ^ 2 = π := Real.sq_sqrt Real.pi_pos.le
  have hEV : EV0 (-(2 * x)) ^ 2 = pcV (-(2 * x)) 0 ^ 2 + pcVD (-(2 * x)) 0 ^ 2 / w ^ 2 := by
    unfold EV0
    rw [deriv_pcV, Real.sq_sqrt (by have := hk0; positivity), ← hkw]
  have hκ := kappa_inv_sq_nonpos ha
  rw [show 1 / 2 - -(2 * x) = 1 / 2 + 2 * x by ring, hdup, hQ2] at hκ
  have hM2 : Mbal (-(2 * x)) 0 ^ 2 = 1 / w := by rw [Mbal_sq, one_div]
  have hX0 : 0 ≤ Real.sqrt (π / 2) * (kappaBal (-(2 * x)))⁻¹ * EV0 (-(2 * x)) :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (inv_nonneg.mpr (kappaBal_pos _).le)) (Real.sqrt_nonneg _)
  have hMp := Mbal_pos (-(2 * x)) 0
  have hX2 : (Real.sqrt (π / 2) * (kappaBal (-(2 * x)))⁻¹ * EV0 (-(2 * x))) ^ 2 =
      (π / 2) * ((kappaBal (-(2 * x)))⁻¹ ^ 2) * (pcV (-(2 * x)) 0 ^ 2 + pcVD (-(2 * x)) 0 ^ 2 / w ^ 2) := by
    rw [mul_pow, mul_pow, hEV, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ π / 2)]
  rw [hκ, hV0, hV1] at hX2
  rw [← hwdef] at hr1 hr2
  clear_value w
  generalize hG1d : Real.Gamma (x + 1 / 4) = G1 at *
  generalize hG3d : Real.Gamma (x + 3 / 4) = G3 at *
  generalize hQd : (2 : ℝ) ^ (x - 1 / 4) = Q at *
  generalize hPd : Real.sqrt π = P at *
  set t := G3 / (w * G1) with htd
  have ht3 : G3 = t * w * G1 := by rw [htd]; field_simp
  have ht1 : 7 / 25 ≤ t := by rw [htd, le_div_iff₀ (by positivity)]; linarith
  have ht2 : t ≤ 7 / 4 := by rw [htd, div_le_iff₀ (by positivity)]; linarith
  have ht0 : 0 < t := by linarith
  have halg := alg_well_V hQ hG1 ht0 hw hP1 hP2 hsc ht1 ht2
  rw [← ht3] at halg
  have hPpos : 0 < P := by linarith
  have e : (π / 2) * (G1 * G3 / (P * (Q ^ 2)⁻¹)) *
      ((Q⁻¹ * Real.cos (π * (x + 1 / 4)) / G3) ^ 2 + (Real.sqrt 2 * Q⁻¹ * Real.sin (π * (x + 1 / 4)) / G1) ^ 2 / w ^ 2) =
      (P ^ 2 / 2) * (G1 * G3 * Q ^ 2 / P) *
        ((Q⁻¹ * Real.cos (π * (x + 1 / 4)) / G3) ^ 2 + (Real.sqrt 2 * Q⁻¹ * Real.sin (π * (x + 1 / 4)) / G1) ^ 2 / w ^ 2) := by
    rw [hPP]; field_simp
  constructor
  · apply le_of_sq_le_sq _ hX0
    rw [hX2, e, mul_pow, hM2]
    linarith [halg.1]
  · apply le_of_sq_le_sq _ (by positivity)
    rw [hX2, e, mul_pow, hM2]
    linarith [halg.2]

/-- `1/2 kappa^{-1} M_bal <= E_U(a,0) <= 2 kappa^{-1} M_bal` for `a > 0`. -/
theorem origin_bar_U {a : ℝ} (ha : 0 < a) :
    1 / 2 * ((kappaBal a)⁻¹ * Mbal a 0) ≤ EU0 a ∧ EU0 a ≤ 2 * ((kappaBal a)⁻¹ * Mbal a 0) := by
  obtain ⟨x, hx, rfl⟩ : ∃ x, 0 < x ∧ a = 2 * x := ⟨a / 2, by linarith, by ring⟩
  have hx0 := hx.le
  have hk := k2_zero_cases hx0 (2 * x) (by rw [abs_of_nonneg (by linarith)])
  have hk0 := k2_pos (2 * x) 0
  set k := k2 (2 * x) 0 with hkdef
  have hw : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk0
  have hkw : k = Real.sqrt k ^ 2 := (Real.sq_sqrt hk0.le).symm
  set w := Real.sqrt k with hwdef
  have hG1 : 0 < Real.Gamma (x + 1 / 4) := Real.Gamma_pos_of_pos (by linarith)
  have hG3 : 0 < Real.Gamma (x + 3 / 4) := Real.Gamma_pos_of_pos (by linarith)
  obtain ⟨hr1, hr2⟩ := Gamma_ratio_origin hx0 hk
  have hQ : 0 < (2 : ℝ) ^ (-x - 1 / 4) := Real.rpow_pos_of_pos (by norm_num) _
  have hP1 := sqrt_pi_bounds.1
  have hP2 := sqrt_pi_bounds.2
  have hdup := Gamma_dup_origin hx0
  have hs2 : Real.sqrt 2 = (2 : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow 2
  have hQ2 : (2 : ℝ) ^ (1 / 2 - 2 * x) = 2 * ((2 : ℝ) ^ (-x - 1 / 4)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    rw [show (1 / 2 - 2 * x : ℝ) = 1 + (-x - 1 / 4) * ((2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_add (by norm_num),
      Real.rpow_one]
  have hU0 : pcU (2 * x) 0 = Real.sqrt π * (2 : ℝ) ^ (-x - 1 / 4) / Real.Gamma (x + 3 / 4) := by
    rw [pcU_zero, show -(2 * x / 2 + 1 / 4) = -x - 1 / 4 by ring, show 3 / 4 + 2 * x / 2 = x + 3 / 4 by ring]
    ring
  have hU1 : pcUD (2 * x) 0 = -(Real.sqrt π * Real.sqrt 2 * (2 : ℝ) ^ (-x - 1 / 4) / Real.Gamma (x + 1 / 4)) := by
    rw [pcUD_zero, show -(2 * x / 2 - 1 / 4) = (-x - 1 / 4) + 1 / 2 by ring, Real.rpow_add (by norm_num), ← hs2,
      show 1 / 4 + 2 * x / 2 = x + 1 / 4 by ring]
    ring
  have hE : EU0 (2 * x) ^ 2 = pcU (2 * x) 0 ^ 2 + pcUD (2 * x) 0 ^ 2 / w ^ 2 := by
    unfold EU0
    rw [deriv_pcU, Real.sq_sqrt (by have := hk0; positivity), ← hkw]
  have hκ := kappa_inv_sq_pos ha
  rw [show 1 / 2 + 2 * x = 1 / 2 + 2 * x by ring, hdup, hQ2] at hκ
  have hM2 : Mbal (2 * x) 0 ^ 2 = 1 / w := by rw [Mbal_sq, one_div]
  have hA : ((kappaBal (2 * x))⁻¹ * Mbal (2 * x) 0) ^ 2 =
      Real.sqrt 2 * Real.sqrt π / (Real.Gamma (x + 1 / 4) * Real.Gamma (x + 3 / 4) /
        (Real.sqrt π * (2 * ((2 : ℝ) ^ (-x - 1 / 4)) ^ 2))) * (1 / w) := by
    rw [mul_pow, hκ, hM2]
  have hA0 : 0 ≤ ((kappaBal (2 * x))⁻¹ * Mbal (2 * x) 0) := 
    mul_nonneg (inv_nonneg.mpr (kappaBal_pos _).le) (Mbal_pos _ _).le
  have hEn : 0 ≤ EU0 (2 * x) := Real.sqrt_nonneg _
  rw [hU0, hU1] at hE
  rw [← hwdef] at hr1 hr2
  clear_value w
  generalize hG1d : Real.Gamma (x + 1 / 4) = G1 at *
  generalize hG3d : Real.Gamma (x + 3 / 4) = G3 at *
  generalize hQd : (2 : ℝ) ^ (-x - 1 / 4) = Q at *
  generalize hPd : Real.sqrt π = P at *
  set t := G3 / (w * G1) with htd
  have ht3 : G3 = t * w * G1 := by rw [htd]; field_simp
  have ht1 : 7 / 25 ≤ t := by rw [htd, le_div_iff₀ (by positivity)]; linarith
  have ht2 : t ≤ 7 / 4 := by rw [htd, div_le_iff₀ (by positivity)]; linarith
  have ht0 : 0 < t := by linarith
  have halg := alg_bar_U hQ hG1 ht0 hw hP1 hP2 ht1 ht2
  rw [← ht3] at halg
  have hPpos : 0 < P := by linarith
  have e : Real.sqrt 2 * P / (G1 * G3 / (P * (2 * Q ^ 2))) * (1 / w) = 2 * Real.sqrt 2 * P ^ 2 * Q ^ 2 / (G1 * G3 * w) := by
    field_simp
  rw [e] at hA
  rw [neg_sq] at hE
  have hApos : 0 ≤ 2 * Real.sqrt 2 * P ^ 2 * Q ^ 2 / (G1 * G3 * w) := by positivity
  constructor
  · apply le_of_sq_le_sq _ hEn
    rw [hE, mul_pow, hA]
    linarith [halg.1]
  · apply le_of_sq_le_sq _ (by positivity)
    rw [hE, mul_pow, hA]
    linarith [halg.2]

/-! ### The origin envelopes in the form of `PCEnvelopeFacts` -/

theorem Ewell_zero (a : ℝ) : Ewell a 0 = 1 := by
  have h : ¬ (2 * Real.sqrt |a| < 0) := not_lt.mpr (by positivity)
  unfold Ewell
  simp only [h, ↓reduceIte]

theorem Ebar_zero (a : ℝ) : Ebar a 0 = 1 := by
  unfold Ebar; simp

/-- `U(a,0) > 0` for `a > 0`... and in particular `U(0,0) > 0` (used as the sign anchor of `U_pos`). -/
theorem pcU_zero_zero_pos : 0 < pcU 0 0 := by
  rw [pcU_zero]
  have h3 : 0 < Real.Gamma (3 / 4 + 0 / 2) := Real.Gamma_pos_of_pos (by norm_num)
  have := Real.sqrt_pos.mpr Real.pi_pos
  positivity

/-- **E0, `a <= 0`, `U`-part of `env_well` at `z = 0`**: `1/2 M_bal <= sqrt(u~^2 + u~'^2 / k_2) <= 2 M_bal` (`E_well(a,0) = 1`). -/
theorem origin_env_well_U {a : ℝ} (ha : a ≤ 0) :
    1 / 2 * (Ewell a 0 * Mbal a 0) ≤
        Real.sqrt (ut pcU a 0 ^ 2 + (kappaBal a * deriv (pcU a) 0) ^ 2 / k2 a 0) ∧
      Real.sqrt (ut pcU a 0 ^ 2 + (kappaBal a * deriv (pcU a) 0) ^ 2 / k2 a 0) ≤ 2 * (Ewell a 0 * Mbal a 0) := by
  have hκ := kappaBal_pos a
  have e : Real.sqrt (ut pcU a 0 ^ 2 + (kappaBal a * deriv (pcU a) 0) ^ 2 / k2 a 0) = kappaBal a * EU0 a := by
    unfold EU0 ut
    rw [← Real.sqrt_sq hκ.le, ← Real.sqrt_mul (by positivity), Real.sqrt_sq hκ.le]
    congr 1; ring
  rw [e, Ewell_zero, one_mul]
  obtain ⟨h1, h2⟩ := origin_well_U ha
  constructor
  · calc 1 / 2 * Mbal a 0 = kappaBal a * (1 / 2 * ((kappaBal a)⁻¹ * Mbal a 0)) := by field_simp
      _ ≤ _ := by gcongr
  · calc _ ≤ kappaBal a * (2 * ((kappaBal a)⁻¹ * Mbal a 0)) := by gcongr
      _ = _ := by field_simp

/-- **E0, `a <= 0`, `V`-part of `env_well` at `z = 0`**. -/
theorem origin_env_well_V {a : ℝ} (ha : a ≤ 0) :
    1 / 2 * ((Ewell a 0)⁻¹ * Mbal a 0) ≤
        Real.sqrt (vt pcV a 0 ^ 2 + (Real.sqrt (π / 2) * (kappaBal a)⁻¹ * deriv (pcV a) 0) ^ 2 / k2 a 0) ∧
      Real.sqrt (vt pcV a 0 ^ 2 + (Real.sqrt (π / 2) * (kappaBal a)⁻¹ * deriv (pcV a) 0) ^ 2 / k2 a 0) ≤
        2 * ((Ewell a 0)⁻¹ * Mbal a 0) := by
  have hκ := kappaBal_pos a
  have hc : 0 ≤ Real.sqrt (π / 2) * (kappaBal a)⁻¹ := by positivity
  have e : Real.sqrt (vt pcV a 0 ^ 2 + (Real.sqrt (π / 2) * (kappaBal a)⁻¹ * deriv (pcV a) 0) ^ 2 / k2 a 0) =
      Real.sqrt (π / 2) * (kappaBal a)⁻¹ * EV0 a := by
    unfold EV0 vt
    rw [← Real.sqrt_sq hc, ← Real.sqrt_mul (by positivity), Real.sqrt_sq hc]
    congr 1; ring
  rw [e, Ewell_zero, inv_one, one_mul]
  exact origin_well_V ha

/-- **E0, `a > 0`, `env_bar` at `z = 0`** (both members; `U(a,-w)` has derivative `-U'(a,0)` at `0`). -/
theorem origin_env_bar {a : ℝ} (ha : 0 < a) :
    1 / 2 * (Ebar a 0 * Mbal a 0) ≤
        Real.sqrt ((kappaBal a * pcU a 0) ^ 2 + (kappaBal a * deriv (pcU a) 0) ^ 2 / k2 a 0) ∧
      Real.sqrt ((kappaBal a * pcU a 0) ^ 2 + (kappaBal a * deriv (pcU a) 0) ^ 2 / k2 a 0) ≤ 2 * (Ebar a 0 * Mbal a 0) ∧
    1 / 2 * ((Ebar a 0)⁻¹ * Mbal a 0) ≤
        Real.sqrt ((kappaBal a * pcU a (-0)) ^ 2 + (kappaBal a * deriv (fun w => pcU a (-w)) 0) ^ 2 / k2 a 0) ∧
      Real.sqrt ((kappaBal a * pcU a (-0)) ^ 2 + (kappaBal a * deriv (fun w => pcU a (-w)) 0) ^ 2 / k2 a 0) ≤
        2 * ((Ebar a 0)⁻¹ * Mbal a 0) := by
  have hκ := kappaBal_pos a
  have e : Real.sqrt ((kappaBal a * pcU a 0) ^ 2 + (kappaBal a * deriv (pcU a) 0) ^ 2 / k2 a 0) = kappaBal a * EU0 a := by
    unfold EU0
    rw [← Real.sqrt_sq hκ.le, ← Real.sqrt_mul (by positivity), Real.sqrt_sq hκ.le]
    congr 1; ring
  have hneg : deriv (fun w => pcU a (-w)) 0 = -deriv (pcU a) 0 := by
    have h : HasDerivAt (fun w : ℝ => pcU a (-w)) (pcUD a (-0) * (-1)) 0 :=
      (hasDerivAt_pcU a (-0)).comp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
    rw [h.deriv, deriv_pcU]
    simp
  have e2 : Real.sqrt ((kappaBal a * pcU a (-0)) ^ 2 + (kappaBal a * deriv (fun w => pcU a (-w)) 0) ^ 2 / k2 a 0) =
      kappaBal a * EU0 a := by
    rw [neg_zero, hneg, ← e]; congr 1; ring
  rw [e2, e, Ebar_zero, inv_one, one_mul]
  obtain ⟨h1, h2⟩ := origin_bar_U ha
  have hl : 1 / 2 * Mbal a 0 ≤ kappaBal a * EU0 a :=
    calc 1 / 2 * Mbal a 0 = kappaBal a * (1 / 2 * ((kappaBal a)⁻¹ * Mbal a 0)) := by field_simp
      _ ≤ _ := by gcongr
  have hu : kappaBal a * EU0 a ≤ 2 * Mbal a 0 :=
    calc _ ≤ kappaBal a * (2 * ((kappaBal a)⁻¹ * Mbal a 0)) := by gcongr
      _ = _ := by field_simp
  exact ⟨hl, hu, hl, hu⟩

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.origin_env_well_U' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms origin_env_well_U

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.origin_env_well_V' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms origin_env_well_V

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.origin_env_bar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms origin_env_bar

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.pcU_zero_zero_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pcU_zero_zero_pos

end FormalResearch.JacobiEigenvectors.Charts
