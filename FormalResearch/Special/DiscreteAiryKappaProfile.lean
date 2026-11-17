module

public import FormalResearch.Special.DiscreteAiryKappaMassId

/-!
# The Ermakov profile of the Hahn chain: elementary defect bounds (plan K1, step K-1)

For `q_* = √(1 - x²)`, `h > 0`, `q_k = (k + ½)h`, `α_k = √(q_*² - q_k²)` the WKB (Ermakov) profile is `P_k = ρ_k² = 2/α_k`, i.e. `1/(a sin θ)` at `q_k`
with `2 a sin θ = √(4a² - c²) = √(q_*² - q²)`.  This module bounds, by **elementary real algebra only** (no derivatives, no Taylor),
the Ermakov defect `E_k = s_{k+1} + s_k - c_k P_k` (`DiscreteAiryKappaErmakov`) for the closed-form Hahn coefficients
`a_k² = (1+η_k)(1 - (kh)²)/4`, `c_k = x - κ_k` (`η_k = rr_k² - 1 = O(1/k²)`, `κ_k = Mσ/(k(k+1))`) on a band where `α_j ≥ A > 0`:

* exact relations: `α_k² - α_{k-1}² = -2k h²`, hence `δ_k = α_k - α_{k-1} = -h(q_k + q_{k-1})/(α_k + α_{k-1})`, `|δ_k| ≤ h/A`, `|δ_{k+1} - δ_k| ≤ 2h²/A³`;
* the radicand `a_k² P_k P_{k-1} - 1 = (x² + ε_k + η_k(1 - (kh)²))/(α_kα_{k-1})`, `ε_k = δ_k²/2 + h²/4` (exact);
* `|s_k - x/√(α_kα_{k-1})| ≤ (ε_k + |η_k|)/(x √(α_kα_{k-1}))`;
* `|t_{k+1} + t_k - 2/α_k| ≤ 3h²/A⁶` (`t_k = 1/√(α_kα_{k-1})`; AM–GM against `½(1/α_k + 1/α_{k-1})` and the exact second difference);
* **`|E_k| ≤ (5/x) h²/A⁶ + (2/x) η̄/A + 2 κ̄/A`** (`kp_defect`) and `B_k ≤ 40/A` (`kp_B`), so `ε_k := 40|E_k|/A` sums over a band of `n` sites to
  `n·O(h² A⁻⁷) + O(Σ(η̄ + κ̄)/A²)`.

These bounds are crude (powers of `A` are not optimal: the sharp WKB count is `A⁻⁵`), but they suffice for the sharp constant with an explicit
rate.  Numerics (mpmath 40 digits, scratch `r29_num/chk_bounds.py`, 20000 random `(x, N, k)`): the ratios of the exact quantities to the
claimed bounds are `≤ 0.97` (`b1`), `0.50` (`b2`), `0.21` (`τ`), `0.05` (`E`), `0.50` (`s`-closeness).

**Claim class: proved** (real algebra).  The identification of this profile with the Langer data of the Airy matching and the sums over a
band are in `DiscreteAiryKappaSharp`.
-/

@[expose] public section

open Finset FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- **First difference of the profile radius.**  `α_0² = q_*² - u_0²`, `α_-² = q_*² - (u_0 - h)²`:
`α_0 - α_- = -h(u_0 + u_-)/(α_0 + α_-)` and `|α_0 - α_-| ≤ h/A` when `α ≥ A`, `0 < u_- , u_0 < 1`. -/
lemma kp_delta {h u0 qs α0 αm A : ℝ} (hh : 0 < h) (hu : 0 < u0 - h) (hu1 : u0 < 1) (ha0 : α0 ^ 2 = qs ^ 2 - u0 ^ 2)
    (ham : αm ^ 2 = qs ^ 2 - (u0 - h) ^ 2) (hA0 : 0 < A) (hA : A ≤ α0) (hAm : A ≤ αm) :
    (α0 - αm) * (α0 + αm) = -(h * (u0 + (u0 - h))) ∧ |α0 - αm| ≤ h / A := by
  have e : (α0 - αm) * (α0 + αm) = -(h * (u0 + (u0 - h))) := by nlinarith [ha0, ham]
  refine ⟨e, ?_⟩
  have hS : 2 * A ≤ α0 + αm := by linarith
  have hS0 : 0 < α0 + αm := by linarith
  have h1 : |α0 - αm| * (α0 + αm) = h * (u0 + (u0 - h)) := by
    calc |α0 - αm| * (α0 + αm) = |(α0 - αm) * (α0 + αm)| := by rw [abs_mul, abs_of_pos hS0]
      _ = h * (u0 + (u0 - h)) := by rw [e, abs_neg, abs_of_pos (mul_pos hh (by linarith))]
  have h2 : |α0 - αm| * (2 * A) ≤ h * 2 := by
    calc |α0 - αm| * (2 * A) ≤ |α0 - αm| * (α0 + αm) := mul_le_mul_of_nonneg_left hS (abs_nonneg _)
      _ = h * (u0 + (u0 - h)) := h1
      _ ≤ h * 2 := by nlinarith
  rw [le_div_iff₀ hA0]
  nlinarith [abs_nonneg (α0 - αm)]

lemma kp_alpha_le_one {qs u α : ℝ} (hq : qs ^ 2 ≤ 1) (hα : α ^ 2 = qs ^ 2 - u ^ 2) (hα0 : 0 < α) : α ≤ 1 := by
  nlinarith [sq_nonneg u]

/-- **Second difference of the profile radius**: `|δ_{+} - δ_0| ≤ 2h²/A³` for three consecutive sites `u_0 - h, u_0, u_0 + h`
(`α_j ≥ A`, `A ≤ 1`, `q_*² ≤ 1`). -/
lemma kp_delta2 {h u0 qs αp α0 αm A : ℝ} (hh : 0 < h) (hu : 0 < u0 - h) (hu1 : u0 + h < 1) (hq : qs ^ 2 ≤ 1)
    (hap : αp ^ 2 = qs ^ 2 - (u0 + h) ^ 2) (ha0 : α0 ^ 2 = qs ^ 2 - u0 ^ 2)
    (ham : αm ^ 2 = qs ^ 2 - (u0 - h) ^ 2) (hA0 : 0 < A) (hA1 : A ≤ 1) (hAp : A ≤ αp) (hA : A ≤ α0)
    (hAm : A ≤ αm) :
    |(αp - α0) - (α0 - αm)| ≤ 2 * h ^ 2 / A ^ 3 := by
  obtain ⟨e0, b0⟩ := kp_delta (h := h) (u0 := u0) (qs := qs) (α0 := α0) (αm := αm) (A := A) hh hu (by linarith) ha0 ham hA0 hA hAm
  obtain ⟨ep, bp⟩ := kp_delta (h := h) (u0 := u0 + h) (qs := qs) (α0 := αp) (αm := α0) (A := A) hh (by linarith) hu1
    hap (by simpa using ha0) hA0 hAp hA
  simp only [add_sub_cancel_right] at ep
  have hα0 : α0 ≤ 1 := kp_alpha_le_one hq ha0 (by linarith)
  have hαm : αm ≤ 1 := kp_alpha_le_one hq ham (by linarith)
  have hαp : αp ≤ 1 := kp_alpha_le_one hq hap (by linarith)
  set S0 := α0 + αm with hS0
  set Sp := αp + α0 with hSp
  set δ0 := α0 - αm with hδ0
  set δp := αp - α0 with hδp
  have hS0p : 2 * A ≤ S0 := by linarith
  have hSpp : 2 * A ≤ Sp := by linarith
  have hS0u : S0 ≤ 2 := by linarith
  have key : (δp - δ0) * (S0 * Sp) = h * ((u0 + (u0 - h)) * (δp + δ0) - 2 * h * S0) := by
    have hsub : Sp - S0 = δp + δ0 := by rw [hSp, hS0, hδp, hδ0]; ring
    linear_combination (S0) * ep - (Sp) * e0 + (h * (u0 + (u0 - h))) * hsub
  have hden : 0 < S0 * Sp := mul_pos (by linarith) (by linarith)
  have hnum : |h * ((u0 + (u0 - h)) * (δp + δ0) - 2 * h * S0)| ≤ h * (2 * (2 * h / A) + 2 * h * 2) := by
    rw [abs_mul, abs_of_pos hh]
    apply mul_le_mul_of_nonneg_left _ hh.le
    have hsum : |δp + δ0| ≤ 2 * h / A := by
      calc |δp + δ0| ≤ |δp| + |δ0| := abs_add_le _ _
        _ ≤ h / A + h / A := add_le_add bp b0
        _ = 2 * h / A := by ring
    calc |(u0 + (u0 - h)) * (δp + δ0) - 2 * h * S0| ≤ |(u0 + (u0 - h)) * (δp + δ0)| + |2 * h * S0| := abs_sub _ _
      _ = |u0 + (u0 - h)| * |δp + δ0| + 2 * h * S0 := by
          rw [abs_mul, abs_of_pos (mul_pos (by linarith : (0:ℝ) < 2 * h) (by linarith : 0 < S0))]
      _ ≤ 2 * (2 * h / A) + 2 * h * 2 := by
          apply add_le_add
          · apply mul_le_mul _ hsum (abs_nonneg _) (by norm_num)
            rw [abs_of_pos (by linarith)]; linarith
          · nlinarith
  have h1 : |δp - δ0| * (S0 * Sp) ≤ h * (2 * (2 * h / A) + 2 * h * 2) := by
    have : |δp - δ0| * (S0 * Sp) = |(δp - δ0) * (S0 * Sp)| := by rw [abs_mul, abs_of_pos hden]
    rw [this, key]; exact hnum
  have h2 : 4 * A ^ 2 ≤ S0 * Sp := by nlinarith
  have h3 : |δp - δ0| * (4 * A ^ 2) ≤ h * (2 * (2 * h / A) + 2 * h * 2) :=
    (mul_le_mul_of_nonneg_left h2 (abs_nonneg _)).trans h1
  rw [le_div_iff₀ (pow_pos hA0 3)]
  have hAi : 0 < A := hA0
  have : h * (2 * (2 * h / A) + 2 * h * 2) ≤ 8 * h ^ 2 / A := by
    rw [show h * (2 * (2 * h / A) + 2 * h * 2) = 4 * h ^ 2 / A + 4 * h ^ 2 by field_simp; ring]
    have : 4 * h ^ 2 ≤ 4 * h ^ 2 / A := by
      rw [le_div_iff₀ hAi]; nlinarith [mul_nonneg (sub_nonneg.2 hA1) (sq_nonneg h)]
    have e8 : 8 * h ^ 2 / A = 4 * h ^ 2 / A + 4 * h ^ 2 / A := by ring
    linarith
  have h4 : |δp - δ0| * (4 * A ^ 2) ≤ 8 * h ^ 2 / A := h3.trans this
  have h5 : |δp - δ0| * (4 * A ^ 2) * A ≤ 8 * h ^ 2 := by
    calc |δp - δ0| * (4 * A ^ 2) * A ≤ 8 * h ^ 2 / A * A := mul_le_mul_of_nonneg_right h4 hAi.le
      _ = 8 * h ^ 2 := div_mul_cancel₀ _ hAi.ne'
  nlinarith [h5]

end FormalResearch.Special
