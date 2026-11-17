module

public import FormalResearch.Special.DiscreteAiryKappaBandMass

/-!
# Explicit error terms of the Hahn band mass (plan K1, step K-2)

For the Hahn profile `P = 2/α` and weights `v = P/2 = 1/α` this module bounds, on a band `α_j ≥ A`,

* `|t_{k+1} - t_k| ≤ h/A³ + h²/(2A⁶)` (`kp_t_diff`; `t_k = 1/√(α_kα_{k-1})`),
* `|u_{k+1} - u_k| ≤ 2h/A⁴ + (2ε̄ + x(h/A³ + h²/(2A⁶)))/A`, `ε̄ = (h²/A² + η̄)/(xA)`, `u = (P/2)s` (`kp_du`),
* `|Ω_k - 1| ≤ h/(2A²) + |Δu|/A + |E_k|/A²` (`kp_omega_bound`, via the exact `kp_omega_eq`).

**Claim class: proved** (real algebra).
-/

@[expose] public section

open Finset FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- **First difference of `t_k`**: `|t_{k+1} - t_k| ≤ h/A³ + h²/(2A⁶)`. -/
lemma kp_t_diff {h u0 qs αp α0 αm A : ℝ} (hh : 0 < h) (hu : 0 < u0 - h) (hu1 : u0 + h < 1)
    (hap : αp ^ 2 = qs ^ 2 - (u0 + h) ^ 2) (ha0 : α0 ^ 2 = qs ^ 2 - u0 ^ 2)
    (ham : αm ^ 2 = qs ^ 2 - (u0 - h) ^ 2) (hA0 : 0 < A) (hA1 : A ≤ 1) (hAp : A ≤ αp) (hA : A ≤ α0)
    (hAm : A ≤ αm) :
    |1 / Real.sqrt (αp * α0) - 1 / Real.sqrt (α0 * αm)| ≤ h / A ^ 3 + h ^ 2 / A ^ 6 / 2 := by
  obtain ⟨e0, b0⟩ := kp_delta (h := h) (u0 := u0) (qs := qs) (α0 := α0) (αm := αm) (A := A) hh hu (by linarith) ha0 ham hA0 hA hAm
  obtain ⟨ep, bp⟩ := kp_delta (h := h) (u0 := u0 + h) (qs := qs) (α0 := αp) (αm := α0) (A := A) hh (by linarith) hu1
    hap (by simpa using ha0) hA0 hAp hA
  have tp := kp_t_am hA0 hAp hA
  have t0 := kp_t_am hA0 hA hAm
  have hX1 := tp.trans (kp_sq_aux hA0 hA1 bp)
  have hX2 := t0.trans (kp_sq_aux hA0 hA1 b0)
  have hαp : 0 < αp := by linarith
  have hαm : 0 < αm := by linarith
  have hα0 : 0 < α0 := by linarith
  have hAM : |(1 / αp + 1 / α0) / 2 - (1 / α0 + 1 / αm) / 2| ≤ h / A ^ 3 := by
    have : (1 / αp + 1 / α0) / 2 - (1 / α0 + 1 / αm) / 2 = (αm - αp) / (2 * (αp * αm)) := by
      field_simp; ring
    rw [this, abs_div, abs_of_pos (by positivity : 0 < 2 * (αp * αm))]
    have hnum : |αm - αp| ≤ 2 * h / A := by
      have : αm - αp = -((αp - α0) + (α0 - αm)) := by ring
      rw [this, abs_neg]
      calc |(αp - α0) + (α0 - αm)| ≤ |αp - α0| + |α0 - αm| := abs_add_le _ _
        _ ≤ h / A + h / A := add_le_add bp b0
        _ = 2 * h / A := by ring
    have hden : 2 * A ^ 2 ≤ 2 * (αp * αm) := by nlinarith [mul_le_mul hAp hAm hA0.le (by linarith)]
    calc |αm - αp| / (2 * (αp * αm)) ≤ (2 * h / A) / (2 * A ^ 2) :=
          div_le_div₀ (by positivity) hnum (by positivity) hden
      _ = h / A ^ 3 := by field_simp
  set Q := h ^ 2 / A ^ 6 with hQ
  have hsplit : 1 / Real.sqrt (αp * α0) - 1 / Real.sqrt (α0 * αm) =
      (1 / Real.sqrt (αp * α0) - (1 / αp + 1 / α0) / 2) - (1 / Real.sqrt (α0 * αm) - (1 / α0 + 1 / αm) / 2) +
        ((1 / αp + 1 / α0) / 2 - (1 / α0 + 1 / αm) / 2) := by ring
  rw [hsplit]
  calc _ ≤ |1 / Real.sqrt (αp * α0) - (1 / αp + 1 / α0) / 2| + |1 / Real.sqrt (α0 * αm) - (1 / α0 + 1 / αm) / 2| +
        |(1 / αp + 1 / α0) / 2 - (1 / α0 + 1 / αm) / 2| := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_sub _ _
    _ ≤ Q / 4 + Q / 4 + h / A ^ 3 := by gcongr
    _ = h / A ^ 3 + Q / 2 := by ring

/-- Core bound for `Δu`: `u = (P/2) s`, `|P_1 - P_0| ≤ ΔP`, `0 ≤ s_1 ≤ 2/A`, `0 ≤ P_0 ≤ 2/A`, `|s_1 - s_0| ≤ Δs`
give `|u_1 - u_0| ≤ ΔP/A + Δs/A`. -/
lemma kp_du_core {P0 P1 s0 s1 ΔP Δs A : ℝ} (hA : 0 < A) (hs1 : s1 ≤ 2 / A) (hs1' : 0 ≤ s1) (hP0 : 0 ≤ P0)
    (hP0' : P0 ≤ 2 / A) (hdP : |P1 - P0| ≤ ΔP) (hds : |s1 - s0| ≤ Δs) :
    |P1 / 2 * s1 - P0 / 2 * s0| ≤ ΔP / A + Δs / A := by
  have e : P1 / 2 * s1 - P0 / 2 * s0 = (P1 - P0) * s1 / 2 + P0 * (s1 - s0) / 2 := by ring
  rw [e]
  have h1 : |(P1 - P0) * s1 / 2| ≤ ΔP / A := by
    rw [abs_div, abs_mul, abs_of_nonneg hs1', abs_of_pos (by norm_num : (0:ℝ) < 2)]
    calc |P1 - P0| * s1 / 2 ≤ ΔP * (2 / A) / 2 := by
          apply div_le_div_of_nonneg_right _ (by norm_num)
          exact mul_le_mul hdP hs1 hs1' ((abs_nonneg _).trans hdP)
      _ = ΔP / A := by ring
  have h2 : |P0 * (s1 - s0) / 2| ≤ Δs / A := by
    rw [abs_div, abs_mul, abs_of_nonneg hP0, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    calc P0 * |s1 - s0| / 2 ≤ (2 / A) * Δs / 2 := by
          apply div_le_div_of_nonneg_right _ (by norm_num)
          exact mul_le_mul hP0' hds (abs_nonneg _) (by positivity)
      _ = Δs / A := by ring
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

/-- Core bound for `Ω - 1` from the exact formula of `kp_omega_eq` (`v = P/2`). -/
lemma kp_omega_core {P0 P1 s0 s1 E A h Du : ℝ} (hA : 0 < A) (hA1 : A ≤ 1) (hP0 : 2 ≤ P0) (hs1 : s1 ≤ 2 / A)
    (hs1' : 0 ≤ s1) (hs0 : 0 ≤ s0) (hs0' : s0 ≤ 2 / A) (hdP : |P1 - P0| / (2 * P0) ≤ h / (2 * A ^ 2))
    (hdu : |P1 / 2 * s1 - P0 / 2 * s0| ≤ Du) :
    |(P0 + P1) / (2 * P0) + (s1 * (P1 / 2 * s1 - P0 / 2 * s0) + P0 / 2 * s0 * E) / P0 - 1| ≤
      h / (2 * A ^ 2) + Du / A + |E| / A ^ 2 := by
  have hP0p : 0 < P0 := by linarith
  have e : (P0 + P1) / (2 * P0) + (s1 * (P1 / 2 * s1 - P0 / 2 * s0) + P0 / 2 * s0 * E) / P0 - 1 =
      (P1 - P0) / (2 * P0) + (s1 * (P1 / 2 * s1 - P0 / 2 * s0)) / P0 + (s0 / 2) * E := by
    field_simp; ring
  rw [e]
  have h1 : |(P1 - P0) / (2 * P0)| ≤ h / (2 * A ^ 2) := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * P0)]; exact hdP
  have h2 : |(s1 * (P1 / 2 * s1 - P0 / 2 * s0)) / P0| ≤ Du / A := by
    rw [abs_div, abs_of_pos hP0p, abs_mul, abs_of_nonneg hs1']
    have : s1 * |P1 / 2 * s1 - P0 / 2 * s0| ≤ (2 / A) * Du := mul_le_mul hs1 hdu (abs_nonneg _) (by positivity)
    calc s1 * |P1 / 2 * s1 - P0 / 2 * s0| / P0 ≤ (2 / A) * Du / 2 := by
          rw [div_le_iff₀ hP0p]
          nlinarith [abs_nonneg (P1 / 2 * s1 - P0 / 2 * s0), mul_nonneg (by positivity : (0:ℝ) ≤ 2 / A) ((abs_nonneg _).trans hdu)]
      _ = Du / A := by ring
  have h3 : |s0 / 2 * E| ≤ |E| / A ^ 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ s0 / 2)]
    have : s0 / 2 ≤ 1 / A ^ 2 := by
      have : s0 / 2 ≤ (2 / A) / 2 := by linarith
      calc s0 / 2 ≤ 1 / A := by linarith [show (2 / A) / 2 = 1 / A by ring]
        _ ≤ 1 / A ^ 2 := one_div_le_one_div_of_le (by positivity) (by nlinarith)
    calc s0 / 2 * |E| ≤ 1 / A ^ 2 * |E| := mul_le_mul_of_nonneg_right this (abs_nonneg _)
      _ = |E| / A ^ 2 := by ring
  calc _ ≤ |(P1 - P0) / (2 * P0)| + |(s1 * (P1 / 2 * s1 - P0 / 2 * s0)) / P0| + |s0 / 2 * E| := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ ≤ h / (2 * A ^ 2) + Du / A + |E| / A ^ 2 := by linarith

/-- **Site bounds for `Ω` and `Δu`** on the Hahn band (same hypotheses as `kp_defect`, plus `a_k, a_{k+1} ≤ 1`):
`|Δu| a_{k+1} ≤ Dub` and `|Ω_k - 1| ≤ h/(2A²) + Dub/A + Ebd/A²` with
`Dub = 2h/A⁴ + (2ε̄ + x(h/A³ + h²/(2A⁶)))/A`, `ε̄ = (h²/A² + η̄)/(xA)`, `Ebd` the bound of `kp_defect`. -/
theorem kp_site_bounds {x qs h A ηb κb : ℝ} {k : ℤ} {a c η κ : ℤ → ℝ} (hx : 0 < x) (hqs : qs ^ 2 = 1 - x ^ 2)
    (hh : 0 < h) (hk : 1 ≤ k) (hA0 : 0 < A) (hA1 : A ≤ 1) (hAm : A ^ 2 ≤ qs ^ 2 - kpU h (k - 1) ^ 2)
    (hA0' : A ^ 2 ≤ qs ^ 2 - kpU h k ^ 2) (hAp : A ^ 2 ≤ qs ^ 2 - kpU h (k + 1) ^ 2)
    (ha0 : a k ^ 2 = (1 + η k) * ((1 - ((k : ℝ) * h) ^ 2) / 4))
    (hap : a (k + 1) ^ 2 = (1 + η (k + 1)) * ((1 - (((k + 1 : ℤ) : ℝ) * h) ^ 2) / 4))
    (hη0 : |η k| ≤ ηb) (hηp : |η (k + 1)| ≤ ηb) (hηb : ηb ≤ x ^ 2) (hc : c k = x - κ k) (hκ : |κ k| ≤ κb)
    (hapos : 0 < a k) (hapos' : 0 < a (k + 1)) (hale0 : a k ≤ 1) (hale1 : a (k + 1) ≤ 1) :
    |kmOmega a c (kpP qs h) (fun j => kpP qs h j / 2) k - 1| ≤
        h / (2 * A ^ 2) +
          (2 * h / A ^ 4 + (2 * ((h ^ 2 / A ^ 2 + ηb) / (x * A)) + x * (h / A ^ 3 + h ^ 2 / A ^ 6 / 2)) / A) / A +
          (2 * (h ^ 2 / A ^ 2 + ηb) / (x * A) + 3 * x * (h ^ 2 / A ^ 6) + 2 * κb / A) / A ^ 2 ∧
      |kpP qs h (k + 1) / 2 * kermS a (kpP qs h) (k + 1) - kpP qs h k / 2 * kermS a (kpP qs h) k| * a (k + 1) ≤
        2 * h / A ^ 4 + (2 * ((h ^ 2 / A ^ 2 + ηb) / (x * A)) + x * (h / A ^ 3 + h ^ 2 / A ^ 6 / 2)) / A := by
  have hqs1 : qs ^ 2 ≤ 1 := by nlinarith [sq_nonneg x]
  obtain ⟨sm, bm⟩ := kpα_sq hAm
  obtain ⟨s0, b0⟩ := kpα_sq hA0'
  obtain ⟨sp, bp⟩ := kpα_sq hAp
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hU0 : 0 < kpU h k := by unfold kpU; exact mul_pos (by linarith) hh
  have hUm : 0 < kpU h (k - 1) := by unfold kpU; push_cast; exact mul_pos (by linarith) hh
  have hUp0 : 0 < kpU h (k + 1) := by unfold kpU; push_cast; exact mul_pos (by linarith) hh
  have hUp1 : kpU h (k + 1) < 1 := kpU_lt_one hqs1 hA0 hAp hUp0
  have hkk : kpU h k - h = kpU h (k - 1) := kpU_pred h k
  have hkk' : kpU h (k + 1) - h = kpU h k := kpU_succ h k
  have hkk2 : kpU h k + h = kpU h (k + 1) := by linarith [hkk']
  have hU01 : kpU h k < 1 := by linarith
  obtain ⟨-, bδ0⟩ := kp_delta (h := h) (u0 := kpU h k) (qs := qs) (α0 := kpα qs h k) (αm := kpα qs h (k - 1)) (A := A) hh
    (by rw [hkk]; exact hUm) hU01 s0 (by rw [hkk]; exact sm) hA0 b0 bm
  obtain ⟨-, bδp⟩ := kp_delta (h := h) (u0 := kpU h (k + 1)) (qs := qs) (α0 := kpα qs h (k + 1)) (αm := kpα qs h k) (A := A) hh
    (by rw [hkk']; exact hU0) hUp1 sp (by rw [hkk']; exact s0) hA0 bp b0
  have hdt := kp_t_diff (h := h) (u0 := kpU h k) (qs := qs) (αp := kpα qs h (k + 1)) (α0 := kpα qs h k)
    (αm := kpα qs h (k - 1)) (A := A) hh (by rw [hkk]; exact hUm) (by rw [hkk2]; exact hUp1)
    (by rw [hkk2]; exact sp) s0 (by rw [hkk]; exact sm) hA0 hA1 bp b0 bm
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
  have hαpp : 0 < kpα qs h (k + 1) := by linarith
  -- bounds on P and s
  have hPk := kpP_pos (h := h) (qs := qs) hA0 hA0'
  have hPk1 := kpP_pos (h := h) (qs := qs) hA0 hAp
  have hPkm := kpP_pos (h := h) (qs := qs) hA0 hAm
  have hPk' := kpP_le (h := h) (qs := qs) hA0 hA0'
  have hPk1' := kpP_le (h := h) (qs := qs) hA0 hAp
  have hPkm' := kpP_le (h := h) (qs := qs) hA0 hAm
  have hs0 : kermS a (kpP qs h) k ≤ 2 / A := kermS_le hA0 hapos.le hale0 hPk.le hPkm.le hPk' hPkm'
  have hs1 : kermS a (kpP qs h) (k + 1) ≤ 2 / A := by
    apply kermS_le hA0 hapos'.le hale1 hPk1.le (by simpa using hPk.le) hPk1'
    simpa using hPk'
  have hs0' := kermS_nonneg a (kpP qs h) k
  have hs1' := kermS_nonneg a (kpP qs h) (k + 1)
  set εb := (h ^ 2 / A ^ 2 + ηb) / (x * A) with hεb
  have hεp : |kermS a (kpP qs h) (k + 1) - x / Real.sqrt (kpα qs h (k + 1) * kpα qs h k)| ≤ εb := by
    refine Sp.trans ?_
    rw [hεb]; gcongr
  have hε0 : |kermS a (kpP qs h) k - x / Real.sqrt (kpα qs h k * kpα qs h (k - 1))| ≤ εb := by
    refine S0.trans ?_
    rw [hεb]; gcongr
  have hds : |kermS a (kpP qs h) (k + 1) - kermS a (kpP qs h) k| ≤ 2 * εb + x * (h / A ^ 3 + h ^ 2 / A ^ 6 / 2) := by
    have e : kermS a (kpP qs h) (k + 1) - kermS a (kpP qs h) k =
        (kermS a (kpP qs h) (k + 1) - x / Real.sqrt (kpα qs h (k + 1) * kpα qs h k)) -
        (kermS a (kpP qs h) k - x / Real.sqrt (kpα qs h k * kpα qs h (k - 1))) +
        x * (1 / Real.sqrt (kpα qs h (k + 1) * kpα qs h k) - 1 / Real.sqrt (kpα qs h k * kpα qs h (k - 1))) := by ring
    rw [e]
    calc _ ≤ |kermS a (kpP qs h) (k + 1) - x / Real.sqrt (kpα qs h (k + 1) * kpα qs h k)| +
          |kermS a (kpP qs h) k - x / Real.sqrt (kpα qs h k * kpα qs h (k - 1))| +
          |x * (1 / Real.sqrt (kpα qs h (k + 1) * kpα qs h k) - 1 / Real.sqrt (kpα qs h k * kpα qs h (k - 1)))| := by
          refine (abs_add_le _ _).trans ?_
          gcongr
          exact abs_sub _ _
      _ ≤ εb + εb + x * (h / A ^ 3 + h ^ 2 / A ^ 6 / 2) := by
          have : |x * (1 / Real.sqrt (kpα qs h (k + 1) * kpα qs h k) - 1 / Real.sqrt (kpα qs h k * kpα qs h (k - 1)))| ≤
              x * (h / A ^ 3 + h ^ 2 / A ^ 6 / 2) := by
            rw [abs_mul, abs_of_pos hx]; exact mul_le_mul_of_nonneg_left hdt hx.le
          linarith
      _ = _ := by ring
  have hdP : |kpP qs h (k + 1) - kpP qs h k| ≤ 2 * h / A ^ 3 := by
    unfold kpP
    have e : 2 / kpα qs h (k + 1) - 2 / kpα qs h k =
        2 * (kpα qs h k - kpα qs h (k + 1)) / (kpα qs h (k + 1) * kpα qs h k) := by field_simp
    rw [e, abs_div, abs_mul, abs_of_pos (mul_pos hαpp hα0p), abs_of_pos (by norm_num : (0:ℝ) < 2)]
    have hn : |kpα qs h k - kpα qs h (k + 1)| ≤ h / A := by rw [abs_sub_comm]; exact bδp
    calc 2 * |kpα qs h k - kpα qs h (k + 1)| / (kpα qs h (k + 1) * kpα qs h k) ≤ 2 * (h / A) / (A * A) := by
          apply div_le_div₀ (by positivity) (by linarith) (by positivity) (mul_le_mul bp b0 hA0.le (by linarith))
      _ = 2 * h / A ^ 3 := by field_simp
  have hdP2 : |kpP qs h (k + 1) - kpP qs h k| / (2 * kpP qs h k) ≤ h / (2 * A ^ 2) := by
    unfold kpP
    have e : 2 / kpα qs h (k + 1) - 2 / kpα qs h k =
        2 * (kpα qs h k - kpα qs h (k + 1)) / (kpα qs h (k + 1) * kpα qs h k) := by field_simp
    rw [e, abs_div, abs_mul, abs_of_pos (mul_pos hαpp hα0p), abs_of_pos (by norm_num : (0:ℝ) < 2)]
    have hn : |kpα qs h k - kpα qs h (k + 1)| ≤ h / A := by rw [abs_sub_comm]; exact bδp
    have e2 : 2 * |kpα qs h k - kpα qs h (k + 1)| / (kpα qs h (k + 1) * kpα qs h k) / (2 * (2 / kpα qs h k)) =
        |kpα qs h k - kpα qs h (k + 1)| / (2 * kpα qs h (k + 1)) := by field_simp
    rw [e2]
    calc |kpα qs h k - kpα qs h (k + 1)| / (2 * kpα qs h (k + 1)) ≤ (h / A) / (2 * A) :=
          div_le_div₀ (by positivity) hn (by positivity) (by linarith)
      _ = h / (2 * A ^ 2) := by field_simp
  have hdu := kp_du_core (P0 := kpP qs h k) (P1 := kpP qs h (k + 1)) (s0 := kermS a (kpP qs h) k)
    (s1 := kermS a (kpP qs h) (k + 1)) hA0 hs1 hs1' hPk.le hPk' hdP hds
  have hP2 : 2 ≤ kpP qs h k := by
    have hα1 : kpα qs h k ≤ 1 := kp_alpha_le_one hqs1 s0 hα0p
    unfold kpP; rw [le_div_iff₀ hα0p]; linarith
  have hrad0 := kp_rad_ge (a := a) (η := η k) hqs hk hh hA0 hAm hA0' ha0 (hη0.trans hηb)
  have hrad1 := kp_rad_ge (a := a) (η := η (k + 1)) (k := k + 1) hqs (by omega) hh hA0 (by simpa using hA0') hAp hap
    (hηp.trans hηb)
  have h0 : a k ^ 2 * kpP qs h k * kpP qs h (k - 1) = kermS a (kpP qs h) k ^ 2 + 1 := by
    rw [kermS_sq hrad0]; ring
  have h1 : a (k + 1) ^ 2 * kpP qs h (k + 1) * kpP qs h k = kermS a (kpP qs h) (k + 1) ^ 2 + 1 := by
    have := kermS_sq (a := a) (P := kpP qs h) (k := k + 1) hrad1
    simp only [add_sub_cancel_right] at this
    rw [this]; ring
  have hE := kp_defect (x := x) (qs := qs) (h := h) (A := A) (ηb := ηb) (κb := κb) (k := k) (a := a) (c := c) (η := η)
    (κ := κ) hx hqs hh hk hA0 hA1 hAm hA0' hAp ha0 hap hη0 hηp hηb hc hκ
  refine ⟨?_, ?_⟩
  · rw [kp_omega_eq hPk h0 h1]
    have hc2 := kp_omega_core (P0 := kpP qs h k) (P1 := kpP qs h (k + 1)) (s0 := kermS a (kpP qs h) k)
      (s1 := kermS a (kpP qs h) (k + 1)) (E := kermE a c (kpP qs h) k) (A := A) (h := h)
      (Du := 2 * h / A ^ 3 / A + (2 * εb + x * (h / A ^ 3 + h ^ 2 / A ^ 6 / 2)) / A) hA0 hA1 hP2 hs1 hs1' hs0' hs0 hdP2 hdu
    refine hc2.trans ?_
    have h4 : |kermE a c (kpP qs h) k| / A ^ 2 ≤ (2 * (h ^ 2 / A ^ 2 + ηb) / (x * A) + 3 * x * (h ^ 2 / A ^ 6) + 2 * κb / A) / A ^ 2 := by
      gcongr
    have h5 : 2 * h / A ^ 3 / A = 2 * h / A ^ 4 := by field_simp
    rw [h5]
    linarith
  · have h5 : 2 * h / A ^ 3 / A = 2 * h / A ^ 4 := by field_simp
    calc _ ≤ |kpP qs h (k + 1) / 2 * kermS a (kpP qs h) (k + 1) - kpP qs h k / 2 * kermS a (kpP qs h) k| * 1 :=
          mul_le_mul_of_nonneg_left hale1 (abs_nonneg _)
      _ ≤ 2 * h / A ^ 3 / A + (2 * εb + x * (h / A ^ 3 + h ^ 2 / A ^ 6 / 2)) / A := by linarith [hdu]
      _ = _ := by rw [h5]

/-- The bound of `|Δu|` of `kp_site_bounds`. -/
noncomputable def kpDub (x h A ηb : ℝ) : ℝ :=
  2 * h / A ^ 4 + (2 * ((h ^ 2 / A ^ 2 + ηb) / (x * A)) + x * (h / A ^ 3 + h ^ 2 / A ^ 6 / 2)) / A

/-- The bound of `|Ω - 1|` of `kp_site_bounds`. -/
noncomputable def kpRb (x h A ηb κb : ℝ) : ℝ :=
  h / (2 * A ^ 2) + kpDub x h A ηb / A + (2 * (h ^ 2 / A ^ 2 + ηb) / (x * A) + 3 * x * (h ^ 2 / A ^ 6) + 2 * κb / A) / A ^ 2

/-- `a_k ≤ 1` for the closed-form Hahn coefficient on the band. -/
lemma kp_a_le_one {x qs h A η : ℝ} {k : ℤ} {a : ℤ → ℝ} (hqs : qs ^ 2 = 1 - x ^ 2) (hh : 0 < h) (hk : 1 ≤ k)
    (hA0 : 0 < A) (hj : A ^ 2 ≤ qs ^ 2 - kpU h k ^ 2) (ha : a k ^ 2 = (1 + η) * ((1 - ((k : ℝ) * h) ^ 2) / 4))
    (hη : |η| ≤ x ^ 2) (hapos : 0 < a k) : a k ≤ 1 := by
  have hqs1 : qs ^ 2 ≤ 1 := by nlinarith [sq_nonneg x]
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [sq_nonneg qs]
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hU : 0 < kpU h k := by unfold kpU; exact mul_pos (by linarith) hh
  have hm : 0 ≤ (k : ℝ) * h := by positivity
  have hlt : (k : ℝ) * h ≤ kpU h k := by unfold kpU; nlinarith
  have hU1 := kpU_lt_one hqs1 hA0 hj hU
  have hm1 : ((k : ℝ) * h) ^ 2 ≤ 1 := kp_sq_le_one hm (by linarith)
  have h3 := (abs_le.1 hη).2
  have h4 : (1 - ((k : ℝ) * h) ^ 2) / 4 ≤ 1 / 4 := by nlinarith [sq_nonneg ((k : ℝ) * h)]
  have h5 : 0 ≤ (1 - ((k : ℝ) * h) ^ 2) / 4 := by linarith
  have : a k ^ 2 ≤ 1 := by
    rw [ha]; nlinarith
  nlinarith

/-- **The mass of the Hahn chain on a band** (`kp_hahn_band_mass`; the first conjunct is `I_{k₀} ≥ 0`, the second the transport `I_{k₀+i} ≤ e^S I_{k₀}`, `I_{k₀} ≤ e^{2S} I_{k₀+i}`, `i ≤ m+1`).  On the sites `k₀, …, k₀+m` of a band where `q_*² - q_j² ≥ A²`
(`j = k₀-1, …, k₀+m+1`) with closed-form coefficients `a_j² = (1+η_j)(1-(jh)²)/4`, `c_j = x - κ_j` (`|η_j| ≤ η̄_j ≤ η_B ≤ x²`,
`|κ_j| ≤ κ̄_j ≤ κ_B ≤ 1`) and `ε_j = kpEps(η̄_j, κ̄_j) ≤ ½`, a solution `Y` of the Jacobi rows satisfies, with `I = I_{k₀}(Y)` the amplitude form,
`S = Σ ε_j`, `r = kpRb(η_B, κ_B)`, `τ = kpDub(η_B)`, `Σv = Σ_{i≤m} P_{k₀+i}/2 = Σ 1/α_{k₀+i}`:

`|Σ_{i≤m} Y_{k₀+i}² - I Σv| ≤ I [ ((e^{2S} - 1)e^S + 4(|r| + τ)e^S) Σv + (2τ/A + 32/A³) e^S ]`. -/
theorem kp_hahn_band_mass {x qs h A ηB κB : ℝ} {a c η κ ηb κb Y : ℤ → ℝ} {k0 : ℤ} (m : ℕ) (hx : 0 < x)
    (hqs : qs ^ 2 = 1 - x ^ 2) (hh : 0 < h) (hk0 : 1 ≤ k0) (hA0 : 0 < A) (hA1 : A ≤ 1)
    (hband : ∀ j : ℤ, k0 - 1 ≤ j → j ≤ k0 + ((m + 1 : ℕ) : ℤ) → A ^ 2 ≤ qs ^ 2 - kpU h j ^ 2)
    (hrow : ∀ i : ℕ, i < m + 1 → jac a c Y (k0 + (i : ℤ)) = 0)
    (hapos : ∀ i : ℕ, i ≤ m + 1 → 0 < a (k0 + (i : ℤ)))
    (ha : ∀ i : ℕ, i ≤ m + 1 → a (k0 + (i : ℤ)) ^ 2 =
      (1 + η (k0 + (i : ℤ))) * ((1 - (((k0 + (i : ℤ) : ℤ) : ℝ) * h) ^ 2) / 4))
    (hη : ∀ i : ℕ, i ≤ m + 1 → |η (k0 + (i : ℤ))| ≤ x ^ 2)
    (hηb : ∀ i : ℕ, i < m + 1 → |η (k0 + (i : ℤ))| ≤ ηb (k0 + (i : ℤ)) ∧ |η (k0 + (i : ℤ) + 1)| ≤ ηb (k0 + (i : ℤ)) ∧
      ηb (k0 + (i : ℤ)) ≤ ηB ∧ ηB ≤ x ^ 2)
    (hc : ∀ i : ℕ, i < m + 1 → c (k0 + (i : ℤ)) = x - κ (k0 + (i : ℤ)))
    (hκ : ∀ i : ℕ, i < m + 1 → |κ (k0 + (i : ℤ))| ≤ κb (k0 + (i : ℤ)) ∧ κb (k0 + (i : ℤ)) ≤ κB ∧ κB ≤ 1)
    (hε : ∀ i : ℕ, i < m + 1 → kpEps x h A (ηb (k0 + (i : ℤ))) (κb (k0 + (i : ℤ))) ≤ 1 / 2) :
    0 ≤ kermI a (kpP qs h) Y k0 ∧ (∀ i : ℕ, i ≤ m + 1 →
      kermI a (kpP qs h) Y (k0 + (i : ℤ)) ≤
          Real.exp (∑ i ∈ range (m + 1), kpEps x h A (ηb (k0 + (i : ℤ))) (κb (k0 + (i : ℤ)))) * kermI a (kpP qs h) Y k0 ∧
        kermI a (kpP qs h) Y k0 ≤
          Real.exp (2 * ∑ i ∈ range (m + 1), kpEps x h A (ηb (k0 + (i : ℤ))) (κb (k0 + (i : ℤ)))) *
            kermI a (kpP qs h) Y (k0 + (i : ℤ))) ∧
    |∑ i ∈ range (m + 1), Y (k0 + (i : ℤ)) ^ 2 - kermI a (kpP qs h) Y k0 * ∑ i ∈ range (m + 1), kpP qs h (k0 + (i : ℤ)) / 2| ≤
      kermI a (kpP qs h) Y k0 *
        (((Real.exp (2 * ∑ i ∈ range (m + 1), kpEps x h A (ηb (k0 + (i : ℤ))) (κb (k0 + (i : ℤ)))) - 1) *
            Real.exp (∑ i ∈ range (m + 1), kpEps x h A (ηb (k0 + (i : ℤ))) (κb (k0 + (i : ℤ)))) +
          4 * (|kpRb x h A ηB κB| + kpDub x h A ηB) *
            Real.exp (∑ i ∈ range (m + 1), kpEps x h A (ηb (k0 + (i : ℤ))) (κb (k0 + (i : ℤ))))) *
          ∑ i ∈ range (m + 1), kpP qs h (k0 + (i : ℤ)) / 2 +
        (2 * kpDub x h A ηB / A + 32 / A ^ 3) *
          Real.exp (∑ i ∈ range (m + 1), kpEps x h A (ηb (k0 + (i : ℤ))) (κb (k0 + (i : ℤ))))) := by
  set S := ∑ i ∈ range (m + 1), kpEps x h A (ηb (k0 + (i : ℤ))) (κb (k0 + (i : ℤ))) with hSdef
  have hqs1 : qs ^ 2 ≤ 1 := by nlinarith [sq_nonneg x]
  have heps0 : ∀ i : ℕ, i < m + 1 → 0 ≤ kpEps x h A (ηb (k0 + (i : ℤ))) (κb (k0 + (i : ℤ))) := by
    intro i hi
    have h1 : 0 ≤ ηb (k0 + (i : ℤ)) := (abs_nonneg _).trans (hηb i hi).1
    have h2 : 0 ≤ κb (k0 + (i : ℤ)) := (abs_nonneg _).trans (hκ i hi).1
    unfold kpEps; positivity
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i hi => heps0 i (Finset.mem_range.1 hi)
  have hP : ∀ j : ℤ, k0 - 1 ≤ j → j ≤ k0 + ((m + 1 : ℕ) : ℤ) → 0 < kpP qs h j ∧ kpP qs h j ≤ 2 / A := fun j h1 h2 =>
    ⟨kpP_pos hA0 (hband j h1 h2), kpP_le hA0 (hband j h1 h2)⟩
  have hale : ∀ i : ℕ, i ≤ m + 1 → a (k0 + (i : ℤ)) ≤ 1 := fun i hi =>
    kp_a_le_one (η := η (k0 + (i : ℤ))) hqs hh (by omega) hA0 (hband _ (by omega) (by omega)) (ha i hi) (hη i hi) (hapos i hi)
  have hsucc : ∀ i : ℕ, k0 + ((i + 1 : ℕ) : ℤ) = k0 + (i : ℤ) + 1 := fun i => by push_cast; ring
  have htr : ∀ i : ℕ, i ≤ m + 1 → kermI a (kpP qs h) Y (k0 + (i : ℤ)) ≤ Real.exp S * kermI a (kpP qs h) Y k0 ∧
      kermI a (kpP qs h) Y k0 ≤ Real.exp (2 * S) * kermI a (kpP qs h) Y (k0 + (i : ℤ)) := by
    intro i hi
    have := kp_transport (x := x) (qs := qs) (h := h) (A := A) (a := a) (c := c) (η := η) (κ := κ) (ηb := ηb) (κb := κb)
      (Y := Y) (k0 := k0) i hx hqs hh hk0 hA0 hA1 (fun j h1 h2 => hband j h1 (by omega))
      (fun i' hi' => hrow i' (by omega)) (fun i' hi' => hapos i' (by omega)) (fun i' hi' => ha i' (by omega))
      (fun i' hi' => hη i' (by omega))
      (fun i' hi' => ⟨(hηb i' (by omega)).1, (hηb i' (by omega)).2.1, (hηb i' (by omega)).2.2.1.trans (hηb i' (by omega)).2.2.2⟩)
      (fun i' hi' => hc i' (by omega))
      (fun i' hi' => ⟨(hκ i' (by omega)).1, (hκ i' (by omega)).2.1.trans (hκ i' (by omega)).2.2⟩)
      (fun i' hi' => hε i' (by omega))
    obtain ⟨t1, t2⟩ := this
    have hsub : ∑ i' ∈ range i, kpEps x h A (ηb (k0 + (i' : ℤ))) (κb (k0 + (i' : ℤ))) ≤ S :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hi)
        (fun i' hi' _ => heps0 i' (by have := Finset.mem_range.1 hi'; omega))
    have hI0 : 0 ≤ kermI a (kpP qs h) Y k0 := by
      have := kermI_nonneg (a := a) (Y := Y) (P := kpP qs h) (k := k0) (hP k0 (by omega) (by omega)).1
        (hP (k0 - 1) (by omega) (by omega)).1
        (kp_rad_ge (a := a) (η := η k0) hqs hk0 hh hA0 (hband _ (by omega) (by omega)) (hband _ (by omega) (by omega))
          (by simpa using ha 0 (by omega)) (by simpa using hη 0 (by omega)))
      exact this
    have hIi0 : 0 ≤ kermI a (kpP qs h) Y (k0 + (i : ℤ)) := by
      refine kermI_nonneg (a := a) (Y := Y) (P := kpP qs h) (k := k0 + (i : ℤ)) (hP _ (by omega) (by omega)).1
        (hP _ (by omega) (by omega)).1 (kp_rad_ge (a := a) (η := η (k0 + (i : ℤ))) hqs (by omega) hh hA0 (hband _ (by omega) (by omega))
          (hband _ (by omega) (by omega)) (ha i hi) (hη i hi))
    constructor
    · exact t1.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hsub) hI0)
    · exact t2.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by linarith)) hIi0)
  have hsite : ∀ i : ℕ, i ≤ m → |kmOmega a c (kpP qs h) (fun j => kpP qs h j / 2) (k0 + (i : ℤ)) - 1| ≤ kpRb x h A ηB κB ∧
      |kpP qs h (k0 + (i : ℤ) + 1) / 2 * kermS a (kpP qs h) (k0 + (i : ℤ) + 1) -
        kpP qs h (k0 + (i : ℤ)) / 2 * kermS a (kpP qs h) (k0 + (i : ℤ))| * a (k0 + (i : ℤ) + 1) ≤ kpDub x h A ηB := by
    intro i hi
    have hk1 : 1 ≤ k0 + (i : ℤ) := by omega
    have hb := kp_site_bounds (x := x) (qs := qs) (h := h) (A := A) (ηb := ηb (k0 + (i : ℤ))) (κb := κb (k0 + (i : ℤ)))
      (k := k0 + (i : ℤ)) (a := a) (c := c) (η := η) (κ := κ) hx hqs hh hk1 hA0 hA1 (hband _ (by omega) (by omega))
      (hband _ (by omega) (by omega)) (hband _ (by omega) (by omega)) (ha i (by omega))
      (by have := ha (i + 1) (by omega); rw [hsucc] at this; push_cast at this ⊢; exact this)
      (hηb i (by omega)).1 (hηb i (by omega)).2.1 ((hηb i (by omega)).2.2.1.trans (hηb i (by omega)).2.2.2) (hc i (by omega))
      (hκ i (by omega)).1 (hapos i (by omega)) (by have := hapos (i + 1) (by omega); rwa [hsucc] at this)
      (hale i (by omega)) (by have := hale (i + 1) (by omega); rwa [hsucc] at this)
    have hη' := (hηb i (by omega)).2.2.1
    have hκ' := (hκ i (by omega)).2.1
    constructor
    · refine hb.1.trans ?_
      unfold kpRb kpDub
      have h1 : 0 ≤ ηb (k0 + (i : ℤ)) := (abs_nonneg _).trans (hηb i (by omega)).1
      have h2 : 0 ≤ κb (k0 + (i : ℤ)) := (abs_nonneg _).trans (hκ i (by omega)).1
      gcongr
    · refine hb.2.trans ?_
      unfold kpDub
      have h1 : 0 ≤ ηb (k0 + (i : ℤ)) := (abs_nonneg _).trans (hηb i (by omega)).1
      gcongr
  have hbm := kp_band_mass (a := a) (c := c) (P := kpP qs h) (Y := Y) (p := k0) m (r := kpRb x h A ηB κB)
    (τ := kpDub x h A ηB) (S := S) (A := A) (Ip := kermI a (kpP qs h) Y k0) hA0 hS0 ?_ (fun i hi => hrow i (by omega))
    (fun i hi => hP _ (by omega) (by omega)) (hP (k0 - 1) (by omega) (by omega))
    (fun i hi => kp_rad_ge (a := a) (η := η (k0 + (i : ℤ))) hqs (by omega) hh hA0 (hband _ (by omega) (by omega))
      (hband _ (by omega) (by omega)) (ha i hi) (hη i hi)) hapos hale htr (fun i hi => (hsite i hi).1)
    (fun i hi => (hsite i hi).2)
  · have hI0' : 0 ≤ kermI a (kpP qs h) Y k0 := by
      have := kermI_nonneg (a := a) (Y := Y) (P := kpP qs h) (k := k0) (hP k0 (by omega) (by omega)).1
        (hP (k0 - 1) (by omega) (by omega)).1
        (kp_rad_ge (a := a) (η := η k0) hqs hk0 hh hA0 (hband _ (by omega) (by omega)) (hband _ (by omega) (by omega))
          (by simpa using ha 0 (by omega)) (by simpa using hη 0 (by omega)))
      exact this
    exact ⟨hI0', htr, hbm⟩
  · unfold kpDub
    have h1 : 0 ≤ ηB := (abs_nonneg _).trans ((hηb 0 (by omega)).1.trans (hηb 0 (by omega)).2.2.1)
    positivity

/-- info: 'FormalResearch.Special.kp_hahn_band_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.kp_hahn_band_mass

/-- info: 'FormalResearch.Special.kp_site_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.kp_site_bounds

end FormalResearch.Special
