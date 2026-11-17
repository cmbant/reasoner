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

/-- **AM–GM defect of `t = 1/√(ab)`**: `|1/√(ab) - ½(1/a + 1/b)| ≤ (a - b)²/(4A³)` for `a, b ≥ A > 0`. -/
lemma kp_t_am {a b A : ℝ} (hA : 0 < A) (ha : A ≤ a) (hb : A ≤ b) :
    |1 / Real.sqrt (a * b) - (1 / a + 1 / b) / 2| ≤ (a - b) ^ 2 / (4 * A ^ 3) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hab : 0 < a * b := mul_pos ha0 hb0
  set r := 1 / Real.sqrt (a * b) with hr
  have hr0 : 0 < r := by rw [hr]; positivity
  have hr2 : r ^ 2 = 1 / (a * b) := by
    rw [hr, div_pow, Real.sq_sqrt hab.le]; ring
  set M := (1 / a + 1 / b) / 2 with hM
  have hM0 : 0 < M := by rw [hM]; positivity
  have hM2 : M ^ 2 - r ^ 2 = (a - b) ^ 2 / (4 * (a * b) ^ 2) := by
    rw [hr2, hM]; field_simp; ring
  have hMr : r ≤ M := by
    by_contra hcon
    push Not at hcon
    have : M ^ 2 < r ^ 2 := by nlinarith
    have h0 : 0 ≤ (a - b) ^ 2 / (4 * (a * b) ^ 2) := by positivity
    linarith
  rw [abs_of_nonpos (by linarith)]
  have h1 : M - r = (a - b) ^ 2 / (4 * (a * b) ^ 2) / (M + r) := by
    rw [← hM2]; field_simp; ring
  have h2 : (a - b) ^ 2 / (4 * (a * b) ^ 2) / (M + r) ≤ (a - b) ^ 2 / (4 * (a * b) ^ 2) / M := by
    apply div_le_div_of_nonneg_left (by positivity) hM0 (by linarith)
  have h3 : (a - b) ^ 2 / (4 * (a * b) ^ 2) / M = (a - b) ^ 2 / (2 * (a * b) * (a + b)) := by
    rw [hM]; field_simp; ring
  have h4 : (a - b) ^ 2 / (2 * (a * b) * (a + b)) ≤ (a - b) ^ 2 / (4 * A ^ 3) := by
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    have : A ^ 2 ≤ a * b := by nlinarith
    nlinarith [mul_pos hA hA]
  linarith [h1, h2, h3, h4]

/-- Second difference of the inverse radius: `|1/α_+ + 1/α_- - 2/α_0| ≤ 4h²/A⁶`. -/
lemma kp_inv_second {h u0 qs αp α0 αm A : ℝ} (hh : 0 < h) (hu : 0 < u0 - h) (hu1 : u0 + h < 1) (hq : qs ^ 2 ≤ 1)
    (hap : αp ^ 2 = qs ^ 2 - (u0 + h) ^ 2) (ha0 : α0 ^ 2 = qs ^ 2 - u0 ^ 2)
    (ham : αm ^ 2 = qs ^ 2 - (u0 - h) ^ 2) (hA0 : 0 < A) (hA1 : A ≤ 1) (hAp : A ≤ αp) (hA : A ≤ α0)
    (hAm : A ≤ αm) :
    |1 / αp + 1 / αm - 2 / α0| ≤ 4 * h ^ 2 / A ^ 6 := by
  have hd2 := kp_delta2 hh hu hu1 hq hap ha0 ham hA0 hA1 hAp hA hAm
  obtain ⟨e0, b0⟩ := kp_delta (h := h) (u0 := u0) (qs := qs) (α0 := α0) (αm := αm) (A := A) hh hu (by linarith) ha0 ham hA0 hA hAm
  obtain ⟨ep, bp⟩ := kp_delta (h := h) (u0 := u0 + h) (qs := qs) (α0 := αp) (αm := α0) (A := A) hh (by linarith) hu1
    hap (by simpa using ha0) hA0 hAp hA
  have hαm : αm ≤ 1 := kp_alpha_le_one hq ham (by linarith)
  have hA6 : 0 < A ^ 6 := by positivity
  have hα0p : 0 < α0 := by linarith
  have hαmp : 0 < αm := by linarith
  have hαpp : 0 < αp := by linarith
  set δ0 := α0 - αm with hδ0
  set δp := αp - α0 with hδp
  have hD2 : 1 / αp + 1 / αm - 2 / α0 = (αm * (δ0 - δp) + δ0 * (δ0 + δp)) / (αp * α0 * αm) := by
    rw [hδ0, hδp]; field_simp; ring
  rw [hD2, abs_div, abs_of_pos (by positivity : 0 < αp * α0 * αm)]
  have h1 : |αm * (δ0 - δp)| ≤ 2 * h ^ 2 / A ^ 3 := by
    rw [abs_mul, abs_of_pos hαmp, abs_sub_comm]
    have : |δp - δ0| ≤ 2 * h ^ 2 / A ^ 3 := by
      have := hd2
      rw [show (αp - α0) - (α0 - αm) = δp - δ0 by rw [hδp, hδ0]] at this
      exact this
    calc αm * |δp - δ0| ≤ 1 * (2 * h ^ 2 / A ^ 3) := mul_le_mul hαm this (abs_nonneg _) (by norm_num)
      _ = _ := by ring
  have h2 : |δ0 * (δ0 + δp)| ≤ 2 * h ^ 2 / A ^ 2 := by
    rw [abs_mul]
    calc |δ0| * |δ0 + δp| ≤ (h / A) * (2 * h / A) := by
          apply mul_le_mul b0 _ (abs_nonneg _) (by positivity)
          calc |δ0 + δp| ≤ |δ0| + |δp| := abs_add_le _ _
            _ ≤ h / A + h / A := add_le_add b0 bp
            _ = 2 * h / A := by ring
      _ = 2 * h ^ 2 / A ^ 2 := by ring
  have hnum : |αm * (δ0 - δp) + δ0 * (δ0 + δp)| ≤ 4 * h ^ 2 / A ^ 3 := by
    have : 2 * h ^ 2 / A ^ 2 ≤ 2 * h ^ 2 / A ^ 3 := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith [pow_pos hA0 2]
    have e : 4 * h ^ 2 / A ^ 3 = 2 * h ^ 2 / A ^ 3 + 2 * h ^ 2 / A ^ 3 := by ring
    calc |αm * (δ0 - δp) + δ0 * (δ0 + δp)| ≤ |αm * (δ0 - δp)| + |δ0 * (δ0 + δp)| := abs_add_le _ _
      _ ≤ 4 * h ^ 2 / A ^ 3 := by linarith
  have hden : A ^ 3 ≤ αp * α0 * αm := by
    have : A * A ≤ αp * α0 := mul_le_mul hAp hA hA0.le (by linarith)
    calc A ^ 3 = A * A * A := by ring
      _ ≤ αp * α0 * αm := mul_le_mul this hAm hA0.le (by positivity)
  calc |αm * (δ0 - δp) + δ0 * (δ0 + δp)| / (αp * α0 * αm) ≤ (4 * h ^ 2 / A ^ 3) / A ^ 3 :=
        div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = 4 * h ^ 2 / A ^ 6 := by rw [div_div, ← pow_add]

lemma kp_sq_aux {d h A : ℝ} (hA0 : 0 < A) (hA1 : A ≤ 1) (hd : |d| ≤ h / A) :
    d ^ 2 / (4 * A ^ 3) ≤ h ^ 2 / A ^ 6 / 4 := by
  have h1 : d ^ 2 ≤ (h / A) ^ 2 := by
    have := sq_le_sq' (abs_le.1 hd).1 (abs_le.1 hd).2
    simpa using this
  have h2 : d ^ 2 / (4 * A ^ 3) ≤ (h / A) ^ 2 / (4 * A ^ 3) := by gcongr
  have h3 : (h / A) ^ 2 / (4 * A ^ 3) = h ^ 2 / (4 * A ^ 5) := by field_simp
  have h4 : h ^ 2 / (4 * A ^ 5) ≤ h ^ 2 / A ^ 6 / 4 := by
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 ≤ h ^ 2 * A ^ 5 := by positivity
    nlinarith [mul_nonneg this (sub_nonneg.2 hA1), pow_pos hA0 5]
  linarith

/-- **Second difference of `t_k = 1/√(α_kα_{k-1})` against `2/α_k`**: `|t_{k+1} + t_k - 2/α_k| ≤ 3h²/A⁶`. -/
lemma kp_tau {h u0 qs αp α0 αm A : ℝ} (hh : 0 < h) (hu : 0 < u0 - h) (hu1 : u0 + h < 1) (hq : qs ^ 2 ≤ 1)
    (hap : αp ^ 2 = qs ^ 2 - (u0 + h) ^ 2) (ha0 : α0 ^ 2 = qs ^ 2 - u0 ^ 2)
    (ham : αm ^ 2 = qs ^ 2 - (u0 - h) ^ 2) (hA0 : 0 < A) (hA1 : A ≤ 1) (hAp : A ≤ αp) (hA : A ≤ α0)
    (hAm : A ≤ αm) :
    |1 / Real.sqrt (αp * α0) + 1 / Real.sqrt (α0 * αm) - 2 / α0| ≤ 3 * (h ^ 2 / A ^ 6) := by
  have hD2b := kp_inv_second hh hu hu1 hq hap ha0 ham hA0 hA1 hAp hA hAm
  obtain ⟨e0, b0⟩ := kp_delta (h := h) (u0 := u0) (qs := qs) (α0 := α0) (αm := αm) (A := A) hh hu (by linarith) ha0 ham hA0 hA hAm
  obtain ⟨ep, bp⟩ := kp_delta (h := h) (u0 := u0 + h) (qs := qs) (α0 := αp) (αm := α0) (A := A) hh (by linarith) hu1
    hap (by simpa using ha0) hA0 hAp hA
  have tp := kp_t_am hA0 hAp hA
  have t0 := kp_t_am hA0 hA hAm
  have hsplit : 1 / Real.sqrt (αp * α0) + 1 / Real.sqrt (α0 * αm) - 2 / α0 =
      (1 / Real.sqrt (αp * α0) - (1 / αp + 1 / α0) / 2) + (1 / Real.sqrt (α0 * αm) - (1 / α0 + 1 / αm) / 2) +
        (1 / αp + 1 / αm - 2 / α0) / 2 := by ring
  rw [hsplit]
  set Q := h ^ 2 / A ^ 6 with hQ
  have hX1 : |1 / Real.sqrt (αp * α0) - (1 / αp + 1 / α0) / 2| ≤ Q / 4 :=
    tp.trans (kp_sq_aux hA0 hA1 bp)
  have hX2 : |1 / Real.sqrt (α0 * αm) - (1 / α0 + 1 / αm) / 2| ≤ Q / 4 :=
    t0.trans (kp_sq_aux hA0 hA1 b0)
  have hX3 : |(1 / αp + 1 / αm - 2 / α0) / 2| ≤ 2 * Q := by
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    have : 4 * h ^ 2 / A ^ 6 = 4 * Q := by rw [hQ]; ring
    linarith [hD2b]
  calc _ ≤ |1 / Real.sqrt (αp * α0) - (1 / αp + 1 / α0) / 2| + |1 / Real.sqrt (α0 * αm) - (1 / α0 + 1 / αm) / 2| +
        |(1 / αp + 1 / αm - 2 / α0) / 2| := by
          refine (abs_add_le _ _).trans ?_
          gcongr
          exact abs_add_le _ _
    _ ≤ 3 * Q := by have : 0 ≤ Q := by positivity
                    linarith

/-- **Square-root closeness**: `|r - w²| ≤ D`, `r ≥ 0`, `w > 0` give `|√r - w| ≤ D/w`. -/
lemma kp_sqrt_close {r w D : ℝ} (hw : 0 < w) (hr : 0 ≤ r) (h : |r - w ^ 2| ≤ D) : |Real.sqrt r - w| ≤ D / w := by
  have hs := Real.sqrt_nonneg r
  have hsq := Real.sq_sqrt hr
  have e : (Real.sqrt r - w) * (Real.sqrt r + w) = r - w ^ 2 := by nlinarith [hsq]
  have hpos : 0 < Real.sqrt r + w := by linarith
  have h1 : |Real.sqrt r - w| * (Real.sqrt r + w) = |r - w ^ 2| := by
    rw [← e, abs_mul, abs_of_pos hpos]
  rw [le_div_iff₀ hw]
  nlinarith [abs_nonneg (Real.sqrt r - w)]

/-- **The radicand of the Hahn profile, exactly**: with `a² = (1+η)(1-m²)/4`, `m = u - h/2`, `P = 2/α`, `α_a² = q_*² - u²`,
`α_b² = q_*² - (u-h)²`, `q_*² = 1 - x²`:
`a² P_a P_b - 1 = (x² + (α_a - α_b)²/2 + h²/4 + η(1 - m²))/(α_aα_b)`. -/
lemma kp_radicand {x qs h u η αa αb : ℝ} (hqs : qs ^ 2 = 1 - x ^ 2) (hαa : αa ^ 2 = qs ^ 2 - u ^ 2)
    (hαb : αb ^ 2 = qs ^ 2 - (u - h) ^ 2) (ha0 : 0 < αa) (hb0 : 0 < αb) :
    (1 + η) * ((1 - (u - h / 2) ^ 2) / 4) * (2 / αa) * (2 / αb) - 1 =
      (x ^ 2 + ((αa - αb) ^ 2 / 2 + h ^ 2 / 4) + η * (1 - (u - h / 2) ^ 2)) / (αa * αb) := by
  have key : (1 - (u - h / 2) ^ 2) - αa * αb = x ^ 2 + (αa - αb) ^ 2 / 2 + h ^ 2 / 4 := by
    nlinarith [hqs, hαa, hαb]
  field_simp
  nlinarith [key]

/-- Core of `kp_s_close` (pure scalar algebra): `r = (x² + ε + η m₂) t²`, `0 ≤ m₂ ≤ 1`, `|η| ≤ x²`, `ε ≥ 0`, `t > 0`
give `|√r - x t| ≤ (ε + |η|) t/x`. -/
lemma kp_s_core {x t ε η m2 r : ℝ} (hx : 0 < x) (ht0 : 0 < t) (hε0 : 0 ≤ ε) (hm0 : 0 ≤ m2) (hm1 : m2 ≤ 1)
    (hη : |η| ≤ x ^ 2) (hr : r = (x ^ 2 + ε + η * m2) * t ^ 2) :
    |Real.sqrt r - x * t| ≤ (ε + |η|) * t / x := by
  have hηm : |η * m2| ≤ |η| := by
    rw [abs_mul, abs_of_nonneg hm0]
    nlinarith [abs_nonneg η]
  have hr0 : 0 ≤ r := by
    rw [hr]
    have : 0 ≤ x ^ 2 + ε + η * m2 := by
      have := (abs_le.1 hηm).1
      have := (abs_le.1 hη).1
      nlinarith
    positivity
  have hw : 0 < x * t := mul_pos hx ht0
  have hD : |r - (x * t) ^ 2| ≤ (ε + |η|) * t ^ 2 := by
    have : r - (x * t) ^ 2 = (ε + η * m2) * t ^ 2 := by rw [hr]; ring
    rw [this, abs_mul, abs_of_nonneg (sq_nonneg t)]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg t)
    calc |ε + η * m2| ≤ |ε| + |η * m2| := abs_add_le _ _
      _ ≤ ε + |η| := by rw [abs_of_nonneg hε0]; linarith
  have hc := kp_sqrt_close hw hr0 hD
  refine hc.trans (le_of_eq ?_)
  field_simp

lemma kp_eps_le {a b h A : ℝ} (hA0 : 0 < A) (hA1 : A ≤ 1) (hδ : |a - b| ≤ h / A) :
    (a - b) ^ 2 / 2 + h ^ 2 / 4 ≤ h ^ 2 / A ^ 2 := by
  have h1 : (a - b) ^ 2 ≤ (h / A) ^ 2 := by
    have := sq_le_sq' (abs_le.1 hδ).1 (abs_le.1 hδ).2
    simpa using this
  have h2 : (h / A) ^ 2 = h ^ 2 / A ^ 2 := by rw [div_pow]
  have hA2 : A ^ 2 ≤ 1 := by nlinarith
  have h3 : h ^ 2 / 4 ≤ h ^ 2 / (2 * A ^ 2) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith [sq_nonneg h, mul_nonneg (sq_nonneg h) (sub_nonneg.2 hA2)]
  have h4 : h ^ 2 / (2 * A ^ 2) = (h ^ 2 / A ^ 2) / 2 := by field_simp
  nlinarith [h1, h2, h3, h4]

/-- **`s_k` is close to `x t_k`**, `t_k = 1/√(α_aα_b)`:
`|√(a² P_a P_b - 1) - x/√(α_aα_b)| ≤ (h²/A² + |η|)/(x A)` for `|η| ≤ x²`, `α ≥ A`, `|α_a - α_b| ≤ h/A`. -/
lemma kp_s_close {x qs h u η αa αb A : ℝ} (hx : 0 < x) (hqs : qs ^ 2 = 1 - x ^ 2) (hαa : αa ^ 2 = qs ^ 2 - u ^ 2)
    (hαb : αb ^ 2 = qs ^ 2 - (u - h) ^ 2) (hA0 : 0 < A) (hA1 : A ≤ 1) (hAa : A ≤ αa) (hAb : A ≤ αb)
    (hδ : |αa - αb| ≤ h / A) (hη : |η| ≤ x ^ 2) (hm : (u - h / 2) ^ 2 ≤ 1) :
    |Real.sqrt ((1 + η) * ((1 - (u - h / 2) ^ 2) / 4) * (2 / αa) * (2 / αb) - 1) - x / Real.sqrt (αa * αb)| ≤
      (h ^ 2 / A ^ 2 + |η|) / (x * A) := by
  have ha0 : 0 < αa := by linarith
  have hb0 : 0 < αb := by linarith
  have hab : 0 < αa * αb := mul_pos ha0 hb0
  have hrad := kp_radicand (x := x) (η := η) (h := h) hqs hαa hαb ha0 hb0
  set t := 1 / Real.sqrt (αa * αb) with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have ht2 : t ^ 2 = 1 / (αa * αb) := by rw [ht, div_pow, Real.sq_sqrt hab.le]; ring
  have htA : t ≤ 1 / A := by
    rw [ht]
    apply one_div_le_one_div_of_le hA0
    apply Real.le_sqrt_of_sq_le; nlinarith
  have hr2 : (1 + η) * ((1 - (u - h / 2) ^ 2) / 4) * (2 / αa) * (2 / αb) - 1 =
      (x ^ 2 + ((αa - αb) ^ 2 / 2 + h ^ 2 / 4) + η * (1 - (u - h / 2) ^ 2)) * t ^ 2 := by
    rw [hrad, ht2]; ring
  have hc := kp_s_core hx ht0 (by positivity) (by linarith) (by nlinarith [sq_nonneg (u - h / 2)]) hη hr2
  have e1 : x / Real.sqrt (αa * αb) = x * t := by rw [ht]; ring
  rw [e1]
  refine hc.trans ?_
  have hε1 := kp_eps_le hA0 hA1 hδ
  calc ((αa - αb) ^ 2 / 2 + h ^ 2 / 4 + |η|) * t / x ≤ (h ^ 2 / A ^ 2 + |η|) * (1 / A) / x := by
        apply div_le_div_of_nonneg_right _ hx.le
        apply mul_le_mul (by linarith) htA ht0.le (by positivity)
    _ = (h ^ 2 / A ^ 2 + |η|) / (x * A) := by field_simp

/-- The lattice position `q_k = (k + ½)h`. -/
noncomputable def kpU (h : ℝ) (k : ℤ) : ℝ := ((k : ℝ) + 1 / 2) * h

/-- The profile radius `α_k = √(q_*² - q_k²)`. -/
noncomputable def kpα (qs h : ℝ) (k : ℤ) : ℝ := Real.sqrt (qs ^ 2 - kpU h k ^ 2)

/-- The Ermakov profile `P_k = ρ_k² = 2/α_k` of the Hahn chain. -/
noncomputable def kpP (qs h : ℝ) (k : ℤ) : ℝ := 2 / kpα qs h k

lemma kpU_succ (h : ℝ) (k : ℤ) : kpU h (k + 1) - h = kpU h k := by unfold kpU; push_cast; ring

lemma kpU_pred (h : ℝ) (k : ℤ) : kpU h k - h = kpU h (k - 1) := by unfold kpU; push_cast; ring

lemma kpα_sq {qs h A : ℝ} {j : ℤ} (hA : A ^ 2 ≤ qs ^ 2 - kpU h j ^ 2) :
    kpα qs h j ^ 2 = qs ^ 2 - kpU h j ^ 2 ∧ A ≤ kpα qs h j := by
  refine ⟨Real.sq_sqrt (by nlinarith [sq_nonneg A]), ?_⟩
  exact Real.le_sqrt_of_sq_le hA

lemma kpU_mid {h : ℝ} {k : ℤ} (hh : 0 < h) (hk : 0 ≤ k) : 0 ≤ kpU h k - h / 2 := by
  unfold kpU
  have : (0 : ℝ) ≤ k := by exact_mod_cast hk
  nlinarith

lemma kp_sq_le_one {a : ℝ} (h0 : 0 ≤ a) (h1 : a < 1) : a ^ 2 ≤ 1 := by nlinarith

lemma kpU_lt_one {qs h A : ℝ} {j : ℤ} (hq : qs ^ 2 ≤ 1) (hA : 0 < A) (hj : A ^ 2 ≤ qs ^ 2 - kpU h j ^ 2)
    (hU : 0 < kpU h j) : kpU h j < 1 := by
  by_contra hcon
  push Not at hcon
  nlinarith [mul_pos hA hA]

/-- **The Ermakov defect of the Hahn profile** (`kp_defect`).  Closed-form coefficients at the bonds `k, k+1`:
`a_j² = (1+η_j)(1 - (jh)²)/4`, `c_k = x - κ_k`; band `A² ≤ q_*² - q_j²` for `j = k-1, k, k+1`, `k ≥ 1`, `|η| ≤ η̄ ≤ x²`, `|κ_k| ≤ κ̄`:
`|E_k| ≤ 2(h²/A² + η̄)/(x A) + 3x h²/A⁶ + 2κ̄/A`. -/
theorem kp_defect {x qs h A ηb κb : ℝ} {k : ℤ} {a c η κ : ℤ → ℝ} (hx : 0 < x) (hqs : qs ^ 2 = 1 - x ^ 2) (hh : 0 < h)
    (hk : 1 ≤ k) (hA0 : 0 < A) (hA1 : A ≤ 1) (hAm : A ^ 2 ≤ qs ^ 2 - kpU h (k - 1) ^ 2)
    (hA0' : A ^ 2 ≤ qs ^ 2 - kpU h k ^ 2) (hAp : A ^ 2 ≤ qs ^ 2 - kpU h (k + 1) ^ 2)
    (ha0 : a k ^ 2 = (1 + η k) * ((1 - ((k : ℝ) * h) ^ 2) / 4))
    (hap : a (k + 1) ^ 2 = (1 + η (k + 1)) * ((1 - (((k + 1 : ℤ) : ℝ) * h) ^ 2) / 4))
    (hη0 : |η k| ≤ ηb) (hηp : |η (k + 1)| ≤ ηb) (hηb : ηb ≤ x ^ 2) (hc : c k = x - κ k) (hκ : |κ k| ≤ κb) :
    |kermE a c (kpP qs h) k| ≤ 2 * (h ^ 2 / A ^ 2 + ηb) / (x * A) + 3 * x * (h ^ 2 / A ^ 6) + 2 * κb / A := by
  have hqs1 : qs ^ 2 ≤ 1 := by nlinarith [sq_nonneg x]
  obtain ⟨sm, bm⟩ := kpα_sq hAm
  obtain ⟨s0, b0⟩ := kpα_sq hA0'
  obtain ⟨sp, bp⟩ := kpα_sq hAp
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hU0 : 0 < kpU h k := by unfold kpU; exact mul_pos (by linarith) hh
  have hUm : 0 < kpU h (k - 1) := by unfold kpU; push_cast; exact mul_pos (by linarith) hh
  have hUp0 : 0 < kpU h (k + 1) := by unfold kpU; push_cast; exact mul_pos (by linarith) hh
  have hUp1 : kpU h (k + 1) < 1 := kpU_lt_one hqs1 hA0 hAp hUp0
  have hU01 : kpU h k < 1 := by rw [← kpU_succ h k] at *; linarith
  have hkk : kpU h k - h = kpU h (k - 1) := kpU_pred h k
  have hkk' : kpU h (k + 1) - h = kpU h k := kpU_succ h k
  have hkk2 : kpU h k + h = kpU h (k + 1) := by linarith [hkk']
  obtain ⟨-, bδ0⟩ := kp_delta (h := h) (u0 := kpU h k) (qs := qs) (α0 := kpα qs h k) (αm := kpα qs h (k - 1)) (A := A) hh
    (by rw [hkk]; exact hUm) hU01 s0 (by rw [hkk]; exact sm) hA0 b0 bm
  obtain ⟨-, bδp⟩ := kp_delta (h := h) (u0 := kpU h (k + 1)) (qs := qs) (α0 := kpα qs h (k + 1)) (αm := kpα qs h k) (A := A) hh
    (by rw [hkk']; exact hU0) hUp1 sp (by rw [hkk']; exact s0) hA0 bp b0
  have hτ := kp_tau (h := h) (u0 := kpU h k) (qs := qs) (αp := kpα qs h (k + 1)) (α0 := kpα qs h k)
    (αm := kpα qs h (k - 1)) (A := A) hh (by rw [hkk]; exact hUm) (by rw [hkk2]; exact hUp1) hqs1
    (by rw [hkk2]; exact sp) s0 (by rw [hkk]; exact sm) hA0 hA1 bp b0 bm
  have hx2 : ηb ≤ x ^ 2 := hηb
  have hmid0 : 0 ≤ kpU h k - h / 2 := kpU_mid hh (by omega)
  have hmidp : 0 ≤ kpU h (k + 1) - h / 2 := kpU_mid hh (by omega)
  have ep : kermS a (kpP qs h) (k + 1) = Real.sqrt ((1 + η (k + 1)) * ((1 - (kpU h (k + 1) - h / 2) ^ 2) / 4) *
      (2 / kpα qs h (k + 1)) * (2 / kpα qs h k) - 1) := by
    unfold kermS kpP
    simp only [add_sub_cancel_right]
    rw [hap, show ((k + 1 : ℤ) : ℝ) * h = kpU h (k + 1) - h / 2 by unfold kpU; push_cast; ring]
  have e0 : kermS a (kpP qs h) k = Real.sqrt ((1 + η k) * ((1 - (kpU h k - h / 2) ^ 2) / 4) *
      (2 / kpα qs h k) * (2 / kpα qs h (k - 1)) - 1) := by
    unfold kermS kpP
    rw [ha0, show (k : ℝ) * h = kpU h k - h / 2 by unfold kpU; ring]
  have Sp := kp_s_close (x := x) (qs := qs) (h := h) (u := kpU h (k + 1)) (η := η (k + 1)) (αa := kpα qs h (k + 1))
    (αb := kpα qs h k) (A := A) hx hqs sp (by rw [hkk']; exact s0) hA0 hA1 bp b0 bδp (hηp.trans hηb)
    (kp_sq_le_one hmidp (by linarith))
  have S0 := kp_s_close (x := x) (qs := qs) (h := h) (u := kpU h k) (η := η k) (αa := kpα qs h k)
    (αb := kpα qs h (k - 1)) (A := A) hx hqs s0 (by rw [hkk]; exact sm) hA0 hA1 b0 bm bδ0 (hη0.trans hηb)
    (kp_sq_le_one hmid0 (by linarith))
  rw [← ep] at Sp
  rw [← e0] at S0
  have hα0p : 0 < kpα qs h k := by linarith
  have hdec : kermE a c (kpP qs h) k =
      (kermS a (kpP qs h) (k + 1) - x / Real.sqrt (kpα qs h (k + 1) * kpα qs h k)) +
      (kermS a (kpP qs h) k - x / Real.sqrt (kpα qs h k * kpα qs h (k - 1))) +
      x * (1 / Real.sqrt (kpα qs h (k + 1) * kpα qs h k) + 1 / Real.sqrt (kpα qs h k * kpα qs h (k - 1)) -
        2 / kpα qs h k) + κ k * (2 / kpα qs h k) := by
    unfold kermE kpP
    rw [hc]
    ring
  rw [hdec]
  have hκt : |κ k * (2 / kpα qs h k)| ≤ 2 * κb / A := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < 2 / kpα qs h k)]
    calc |κ k| * (2 / kpα qs h k) ≤ κb * (2 / A) := by
          apply mul_le_mul hκ _ (by positivity) ((abs_nonneg _).trans hκ)
          exact div_le_div_of_nonneg_left (by norm_num) hA0 b0
      _ = 2 * κb / A := by ring
  have hxt : |x * (1 / Real.sqrt (kpα qs h (k + 1) * kpα qs h k) + 1 / Real.sqrt (kpα qs h k * kpα qs h (k - 1)) -
        2 / kpα qs h k)| ≤ 3 * x * (h ^ 2 / A ^ 6) := by
    rw [abs_mul, abs_of_pos hx]
    calc x * _ ≤ x * (3 * (h ^ 2 / A ^ 6)) := mul_le_mul_of_nonneg_left hτ hx.le
      _ = 3 * x * (h ^ 2 / A ^ 6) := by ring
  calc _ ≤ |kermS a (kpP qs h) (k + 1) - x / Real.sqrt (kpα qs h (k + 1) * kpα qs h k)| +
        |kermS a (kpP qs h) k - x / Real.sqrt (kpα qs h k * kpα qs h (k - 1))| +
        |x * (1 / Real.sqrt (kpα qs h (k + 1) * kpα qs h k) + 1 / Real.sqrt (kpα qs h k * kpα qs h (k - 1)) -
          2 / kpα qs h k)| + |κ k * (2 / kpα qs h k)| := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ ≤ (h ^ 2 / A ^ 2 + ηb) / (x * A) + (h ^ 2 / A ^ 2 + ηb) / (x * A) + 3 * x * (h ^ 2 / A ^ 6) + 2 * κb / A := by
        have h1 : (h ^ 2 / A ^ 2 + |η (k + 1)|) / (x * A) ≤ (h ^ 2 / A ^ 2 + ηb) / (x * A) := by gcongr
        have h2 : (h ^ 2 / A ^ 2 + |η k|) / (x * A) ≤ (h ^ 2 / A ^ 2 + ηb) / (x * A) := by gcongr
        linarith [Sp, S0, hxt, hκt]
    _ = _ := by ring

lemma kpP_pos {qs h A : ℝ} {j : ℤ} (hA0 : 0 < A) (hj : A ^ 2 ≤ qs ^ 2 - kpU h j ^ 2) : 0 < kpP qs h j := by
  have := (kpα_sq hj).2
  unfold kpP; exact div_pos (by norm_num) (by linarith)

lemma kpP_le {qs h A : ℝ} {j : ℤ} (hA0 : 0 < A) (hj : A ^ 2 ≤ qs ^ 2 - kpU h j ^ 2) : kpP qs h j ≤ 2 / A := by
  have := (kpα_sq hj).2
  unfold kpP; exact div_le_div_of_nonneg_left (by norm_num) hA0 this

/-- `s_j ≤ 2/A` when `a ≤ 1` and `P, P' ≤ 2/A` (`s = √(a² P P' - 1)`). -/
lemma kermS_le {a P : ℤ → ℝ} {j : ℤ} {A : ℝ} (hA0 : 0 < A) (ha0 : 0 ≤ a j) (ha1 : a j ≤ 1) (hP0 : 0 ≤ P j)
    (hP1 : 0 ≤ P (j - 1)) (hPa : P j ≤ 2 / A) (hPb : P (j - 1) ≤ 2 / A) : kermS a P j ≤ 2 / A := by
  unfold kermS
  apply Real.sqrt_le_iff.2
  refine ⟨by positivity, ?_⟩
  have h1 : a j ^ 2 ≤ 1 := by nlinarith
  have h2 : P j * P (j - 1) ≤ (2 / A) * (2 / A) := mul_le_mul hPa hPb hP1 (by positivity)
  have h3 : a j ^ 2 * (P j * P (j - 1)) ≤ 1 * ((2 / A) * (2 / A)) :=
    mul_le_mul h1 h2 (mul_nonneg hP0 hP1) (by norm_num)
  nlinarith [h3]

/-- **`B_k ≤ 40/A`**: the coefficient of the one-step bound of `DiscreteAiryKappaErmakov` is `O(1/A)`. -/
lemma kp_B {a c P : ℤ → ℝ} {k : ℤ} {A : ℝ} (hA0 : 0 < A) (ha0 : 0 < a k) (ha1 : a k ≤ 1) (ha0' : 0 < a (k + 1))
    (ha1' : a (k + 1) ≤ 1) (hc : |c k| ≤ 2) (hP0 : 0 < P k) (hPm : 0 < P (k - 1)) (hPp : 0 < P (k + 1))
    (hPa : P k ≤ 2 / A) (hPb : P (k - 1) ≤ 2 / A) (hPc : P (k + 1) ≤ 2 / A) :
    2 * |c k * P k + kermS a P (k + 1) - kermS a P k| + 4 * P k * |c k| + 2 * a k * (P k + P (k - 1)) ≤ 40 / A := by
  have hs1 : kermS a P (k + 1) ≤ 2 / A := by
    apply kermS_le hA0 ha0'.le ha1' hPp.le (by simpa using hP0.le) hPc
    simpa using hPa
  have hs0 : kermS a P k ≤ 2 / A := kermS_le hA0 ha0.le ha1 hP0.le hPm.le hPa hPb
  have hs1' := kermS_nonneg a P (k + 1)
  have hs0' := kermS_nonneg a P k
  have hcP : |c k * P k| ≤ 4 / A := by
    rw [abs_mul, abs_of_pos hP0]
    calc |c k| * P k ≤ 2 * (2 / A) := mul_le_mul hc hPa hP0.le (by norm_num)
      _ = 4 / A := by ring
  have hdiff : |kermS a P (k + 1) - kermS a P k| ≤ 2 / A := by
    rw [abs_le]; constructor <;> linarith
  have hC : |c k * P k + kermS a P (k + 1) - kermS a P k| ≤ 6 / A := by
    calc |c k * P k + kermS a P (k + 1) - kermS a P k| = |c k * P k + (kermS a P (k + 1) - kermS a P k)| := by ring_nf
      _ ≤ |c k * P k| + |kermS a P (k + 1) - kermS a P k| := abs_add_le _ _
      _ ≤ 4 / A + 2 / A := add_le_add hcP hdiff
      _ = 6 / A := by ring
  have h2 : 4 * P k * |c k| ≤ 16 / A := by
    calc 4 * P k * |c k| ≤ 4 * (2 / A) * 2 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hPa (by norm_num)) hc (abs_nonneg _) (by positivity)
      _ = 16 / A := by ring
  have h3 : 2 * a k * (P k + P (k - 1)) ≤ 8 / A := by
    calc 2 * a k * (P k + P (k - 1)) ≤ 2 * 1 * (2 / A + 2 / A) := by
          apply mul_le_mul (by linarith) (by linarith) (by positivity) (by norm_num)
      _ = 8 / A := by ring
  have e : 40 / A = 12 / A + 16 / A + 8 / A + 4 / A := by ring
  have : 0 ≤ 4 / A := by positivity
  linarith [mul_le_mul_of_nonneg_left hC (by norm_num : (0:ℝ) ≤ 2), show 2 * (6 / A) = 12 / A by ring]

/-- **Radicand positivity**: `a² P_k P_{k-1} ≥ 1` on the band. -/
lemma kp_rad_ge {x qs h A η : ℝ} {k : ℤ} {a : ℤ → ℝ} (hqs : qs ^ 2 = 1 - x ^ 2) (hk : 1 ≤ k)
    (hh : 0 < h) (hA0 : 0 < A) (hAm : A ^ 2 ≤ qs ^ 2 - kpU h (k - 1) ^ 2) (hA0' : A ^ 2 ≤ qs ^ 2 - kpU h k ^ 2)
    (ha : a k ^ 2 = (1 + η) * ((1 - ((k : ℝ) * h) ^ 2) / 4)) (hη : |η| ≤ x ^ 2) :
    1 ≤ a k ^ 2 * kpP qs h k * kpP qs h (k - 1) := by
  obtain ⟨sm, bm⟩ := kpα_sq hAm
  obtain ⟨s0, b0⟩ := kpα_sq hA0'
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hUm : 0 < kpU h (k - 1) := by unfold kpU; push_cast; exact mul_pos (by linarith) hh
  have hU0 : 0 < kpU h k := by unfold kpU; exact mul_pos (by linarith) hh
  have hqs1 : qs ^ 2 ≤ 1 := by nlinarith [sq_nonneg x]
  have hU01 : kpU h k < 1 := kpU_lt_one hqs1 hA0 hA0' hU0
  have hkk : kpU h k - h = kpU h (k - 1) := kpU_pred h k
  have hm0 : 0 ≤ kpU h k - h / 2 := kpU_mid hh (by omega)
  have hm1 := kp_sq_le_one hm0 (by linarith)
  have hrad := kp_radicand (x := x) (η := η) (h := h) (u := kpU h k) hqs s0 (by rw [hkk]; exact sm) (by linarith)
    (by linarith)
  have hk2 : (k : ℝ) * h = kpU h k - h / 2 := by unfold kpU; ring
  have : a k ^ 2 * kpP qs h k * kpP qs h (k - 1) - 1 =
      (x ^ 2 + ((kpα qs h k - kpα qs h (k - 1)) ^ 2 / 2 + h ^ 2 / 4) + η * (1 - (kpU h k - h / 2) ^ 2)) /
        (kpα qs h k * kpα qs h (k - 1)) := by
    rw [← hrad, ha, hk2]; unfold kpP; ring
  have hnn : 0 ≤ x ^ 2 + ((kpα qs h k - kpα qs h (k - 1)) ^ 2 / 2 + h ^ 2 / 4) + η * (1 - (kpU h k - h / 2) ^ 2) := by
    have h1 : |η * (1 - (kpU h k - h / 2) ^ 2)| ≤ |η| := by
      rw [abs_mul, abs_of_nonneg (sub_nonneg.2 hm1)]
      nlinarith [abs_nonneg η, sq_nonneg (kpU h k - h / 2)]
    have := (abs_le.1 h1).1
    have := (abs_le.1 hη).1
    nlinarith [sq_nonneg (kpα qs h k - kpα qs h (k - 1)), sq_nonneg h]
  have : 0 ≤ a k ^ 2 * kpP qs h k * kpP qs h (k - 1) - 1 := by
    rw [this]; exact div_nonneg hnn (mul_pos (by linarith) (by linarith)).le
  linarith

/-- info: 'FormalResearch.Special.kp_delta2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.kp_delta2

/-- info: 'FormalResearch.Special.kp_tau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.kp_tau

/-- info: 'FormalResearch.Special.kp_s_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.kp_s_close

/-- info: 'FormalResearch.Special.kp_defect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.kp_defect

/-- info: 'FormalResearch.Special.kp_B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.kp_B

/-- info: 'FormalResearch.Special.kp_rad_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.kp_rad_ge

end FormalResearch.Special
