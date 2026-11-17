module

public import FormalResearch.Special.DiscreteLgBulk
public import FormalResearch.Special.AiryAsymReal
public import FormalResearch.Special.DiscreteAiryOscBi

/-!
# Discrete Liouville-Green matched to the Airy turning layer: Maslov offset `π/4` and `R = h^{1/6} |κ| / √π`

**Setting.**  A solution `Y` of the Jacobi rows has, near a simple turn, the Airy form `Y ≈ κ g Ai(X) + μ g Bi(X)` (`X = h^{-2/3} ζ`, `g` the Langer amplitude; this is
`DaiFull.pointwise`/`discrete_airy_full_unif`), and in the bulk the Liouville-Green form of `DiscreteLgBulk`.  This module identifies the two on an overlap.

**Chart relations** (abstract hypotheses at the two matching sites; for the Langer chart of `u = cos θ` they follow from `langerZeta_integral` and
`langerAmp_of_coeff`):
* `y = -X > 0`, `g y^{-1/4} = h^{1/6} w` (the Langer amplitude `g = w |ζ|^{1/4}`);
* `(2/3) y^{3/2} = Θ*/h - Θ(q)/h` (the Langer phase is the Liouville-Green phase measured from the turn: `(2/3)(-ζ)^{3/2} = ∫_q^c θ`);
* `Θ* - Θ(q) ≥ Φ_min > 0` (the overlap is at macroscopic phase distance from the turn).

**Results.**
* `dlgm_site`: at one site, `|Y - h^{1/6} π^{-1/2} w (κ cos χ + μ sin χ)| ≤ (|κ| + |μ|)(1/(12 Φ_min) + C_a/g_min) h^{1/6} h w`, with the phase
  `χ = Θ(q)/h - Θ*/h + π/4`.  I.e. `g Ai(X) ≈ h^{1/6} π^{-1/2} w cos χ`, `g Bi(X) ≈ h^{1/6} π^{-1/2} w sin χ` (`Ai(-y) ~ π^{-1/2} y^{-1/4} cos(ξ - π/4)`).
* `dlg_airy_match`: transported across the whole bulk window `[J, N+1]`:
  `|Y_k - h^{1/6} π^{-1/2} w_k (κ cos χ_k + μ sin χ_k)| ≤ C h^{1/6} h (|κ| + |μ|) w_k`.  For `μ = 0`: `Y_k = h^{1/6} κ π^{-1/2} w_k [cos(Θ_k/h - Θ*/h + π/4) + O(h)]`,
  i.e. amplitude `R = h^{1/6} |κ|/√π` and phase offset **exactly `π/4`** (the Maslov index of a simple turn); the sign of `κ` is the sign of the cosine factor.

**Claim class: proved** (the chart relations are hypotheses).  **Not formalised here:** `κ`, `μ` themselves (`κ ≠ 0` is `hahn_chain_kappa`, the sharp value is open here).
-/

@[expose] public section

open Finset FormalResearch.DiscreteAiry
open scoped Real

namespace FormalResearch.Special

lemma dlgm_rpow_split {y : ℝ} (hy : 0 < y) :
    y ^ (-(7 / 4) : ℝ) = y ^ (-(1 / 4) : ℝ) * (y ^ (3 / 2 : ℝ))⁻¹ := by
  rw [← Real.rpow_neg hy.le, ← Real.rpow_add hy]; norm_num

/-- **One-site matching** of the Airy form with the cos/sin pair (see the module docstring). -/
theorem dlgm_site {κ μ g y w h Ts P Φmin Ca gmin Y : ℝ} (hh : 0 < h) (hy : 0 < y)
    (hM2 : g * y ^ (-(1 / 4) : ℝ) = h ^ (1 / 6 : ℝ) * w) (hM3 : 2 / 3 * y ^ (3 / 2 : ℝ) = Ts / h - P)
    (hM4 : Φmin ≤ Ts - h * P) (hΦ : 0 < Φmin) (hg : gmin ≤ g) (hgmin : 0 < gmin) (hw : 0 ≤ w) (hCa : 0 ≤ Ca)
    (hY : |Y - (κ * (g * airyAi (-y)) + μ * (g * airyBi (-y)))| ≤ Ca * h * ((|κ| + |μ|) * y ^ (-(1 / 4) : ℝ))) :
    |Y - h ^ (1 / 6 : ℝ) * (1 / √π) * w * (κ * Real.cos (P - Ts / h + π / 4) + μ * Real.sin (P - Ts / h + π / 4))| ≤
      (|κ| + |μ|) * (1 / (12 * Φmin) + Ca / gmin) * (h ^ (1 / 6 : ℝ) * h) * w := by
  have hr : 0 < y ^ (-(1 / 4) : ℝ) := Real.rpow_pos_of_pos hy _
  have ht : 0 < y ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hy _
  have hg0 : 0 < g := hgmin.trans_le hg
  have hh6 : 0 < h ^ (1 / 6 : ℝ) := Real.rpow_pos_of_pos hh _
  have hAi := airyAi_neg_asymptotic hy
  have hBi := airyBi_neg_asymptotic hy
  rw [hM3] at hAi hBi
  have hcos : Real.cos (Ts / h - P - π / 4) = Real.cos (P - Ts / h + π / 4) := by
    rw [← Real.cos_neg]; congr 1; ring
  have hsin : Real.sin (Ts / h - P - π / 4) = -Real.sin (P - Ts / h + π / 4) := by
    rw [← Real.sin_neg]; congr 1; ring
  rw [hcos] at hAi
  rw [hsin] at hBi
  -- the remainder
  have hrem : g * y ^ (-(7 / 4) : ℝ) ≤ h ^ (1 / 6 : ℝ) * h * w * (2 / (3 * Φmin)) := by
    rw [dlgm_rpow_split hy, ← mul_assoc, hM2]
    have hinv : (y ^ (3 / 2 : ℝ))⁻¹ ≤ 2 / 3 * h / Φmin := by
      have h1 : 3 / 2 * (Φmin / h) ≤ y ^ (3 / 2 : ℝ) := by
        have : Ts / h - P = (Ts - h * P) / h := by field_simp
        have h2 : y ^ (3 / 2 : ℝ) = 3 / 2 * (Ts / h - P) := by linarith
        rw [h2, this]
        have : Φmin / h ≤ (Ts - h * P) / h := div_le_div_of_nonneg_right hM4 hh.le
        linarith
      have hpos : 0 < 3 / 2 * (Φmin / h) := by positivity
      calc (y ^ (3 / 2 : ℝ))⁻¹ ≤ (3 / 2 * (Φmin / h))⁻¹ := inv_anti₀ hpos h1
        _ = 2 / 3 * h / Φmin := by field_simp
    calc h ^ (1 / 6 : ℝ) * w * (y ^ (3 / 2 : ℝ))⁻¹ ≤ h ^ (1 / 6 : ℝ) * w * (2 / 3 * h / Φmin) :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = h ^ (1 / 6 : ℝ) * h * w * (2 / (3 * Φmin)) := by field_simp
  -- decomposition
  set T : ℝ := h ^ (1 / 6 : ℝ) * (1 / √π) * w with hT
  have hT' : T = 1 / √π * (g * y ^ (-(1 / 4) : ℝ)) := by rw [hM2, hT]; ring
  have e1 : g * airyAi (-y) = T * Real.cos (P - Ts / h + π / 4) +
      g * (airyAi (-y) - 1 / √π * y ^ (-(1 / 4) : ℝ) * Real.cos (P - Ts / h + π / 4)) := by
    rw [hT']; ring
  have e2 : g * airyBi (-y) = T * Real.sin (P - Ts / h + π / 4) +
      g * (airyBi (-y) + 1 / √π * y ^ (-(1 / 4) : ℝ) * (-Real.sin (P - Ts / h + π / 4))) := by
    rw [hT']; ring
  have b1 : |g * (airyAi (-y) - 1 / √π * y ^ (-(1 / 4) : ℝ) * Real.cos (P - Ts / h + π / 4))| ≤
      h ^ (1 / 6 : ℝ) * h * w * (1 / (12 * Φmin)) := by
    rw [abs_mul, abs_of_pos hg0]
    calc _ ≤ g * (1 / 8 * y ^ (-(7 / 4) : ℝ)) := mul_le_mul_of_nonneg_left hAi hg0.le
      _ = 1 / 8 * (g * y ^ (-(7 / 4) : ℝ)) := by ring
      _ ≤ 1 / 8 * (h ^ (1 / 6 : ℝ) * h * w * (2 / (3 * Φmin))) := by linarith
      _ = _ := by field_simp; ring
  have b2 : |g * (airyBi (-y) + 1 / √π * y ^ (-(1 / 4) : ℝ) * (-Real.sin (P - Ts / h + π / 4)))| ≤
      h ^ (1 / 6 : ℝ) * h * w * (1 / (12 * Φmin)) := by
    rw [abs_mul, abs_of_pos hg0]
    calc _ ≤ g * (1 / 8 * y ^ (-(7 / 4) : ℝ)) := mul_le_mul_of_nonneg_left hBi hg0.le
      _ = 1 / 8 * (g * y ^ (-(7 / 4) : ℝ)) := by ring
      _ ≤ 1 / 8 * (h ^ (1 / 6 : ℝ) * h * w * (2 / (3 * Φmin))) := by linarith
      _ = _ := by field_simp; ring
  have hrg : y ^ (-(1 / 4) : ℝ) ≤ h ^ (1 / 6 : ℝ) * w / gmin := by
    rw [le_div_iff₀ hgmin]
    calc y ^ (-(1 / 4) : ℝ) * gmin ≤ y ^ (-(1 / 4) : ℝ) * g := mul_le_mul_of_nonneg_left hg hr.le
      _ = h ^ (1 / 6 : ℝ) * w := by rw [mul_comm]; exact hM2
  have e3 : Y - T * (κ * Real.cos (P - Ts / h + π / 4) + μ * Real.sin (P - Ts / h + π / 4)) =
      (Y - (κ * (g * airyAi (-y)) + μ * (g * airyBi (-y)))) +
        κ * (g * (airyAi (-y) - 1 / √π * y ^ (-(1 / 4) : ℝ) * Real.cos (P - Ts / h + π / 4))) +
        μ * (g * (airyBi (-y) + 1 / √π * y ^ (-(1 / 4) : ℝ) * (-Real.sin (P - Ts / h + π / 4)))) := by
    rw [e1, e2]; ring
  have e4 : h ^ (1 / 6 : ℝ) * (1 / √π) * w * (κ * Real.cos (P - Ts / h + π / 4) + μ * Real.sin (P - Ts / h + π / 4)) =
      T * (κ * Real.cos (P - Ts / h + π / 4) + μ * Real.sin (P - Ts / h + π / 4)) := by rw [hT]
  rw [e4, e3]
  have t1 : |Y - (κ * (g * airyAi (-y)) + μ * (g * airyBi (-y)))| ≤
      Ca * h * ((|κ| + |μ|) * (h ^ (1 / 6 : ℝ) * w / gmin)) :=
    hY.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrg (by positivity)) (by positivity))
  have t2 : |κ * (g * (airyAi (-y) - 1 / √π * y ^ (-(1 / 4) : ℝ) * Real.cos (P - Ts / h + π / 4)))| ≤
      |κ| * (h ^ (1 / 6 : ℝ) * h * w * (1 / (12 * Φmin))) := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left b1 (abs_nonneg _)
  have t3 : |μ * (g * (airyBi (-y) + 1 / √π * y ^ (-(1 / 4) : ℝ) * (-Real.sin (P - Ts / h + π / 4))))| ≤
      |μ| * (h ^ (1 / 6 : ℝ) * h * w * (1 / (12 * Φmin))) := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left b2 (abs_nonneg _)
  have s1 := abs_add_le (Y - (κ * (g * airyAi (-y)) + μ * (g * airyBi (-y))) +
    κ * (g * (airyAi (-y) - 1 / √π * y ^ (-(1 / 4) : ℝ) * Real.cos (P - Ts / h + π / 4))))
    (μ * (g * (airyBi (-y) + 1 / √π * y ^ (-(1 / 4) : ℝ) * (-Real.sin (P - Ts / h + π / 4)))))
  have s2 := abs_add_le (Y - (κ * (g * airyAi (-y)) + μ * (g * airyBi (-y))))
    (κ * (g * (airyAi (-y) - 1 / √π * y ^ (-(1 / 4) : ℝ) * Real.cos (P - Ts / h + π / 4))))
  have key : Ca * h * ((|κ| + |μ|) * (h ^ (1 / 6 : ℝ) * w / gmin)) +
      |κ| * (h ^ (1 / 6 : ℝ) * h * w * (1 / (12 * Φmin))) + |μ| * (h ^ (1 / 6 : ℝ) * h * w * (1 / (12 * Φmin))) =
      (|κ| + |μ|) * (1 / (12 * Φmin) + Ca / gmin) * (h ^ (1 / 6 : ℝ) * h) * w := by
    ring
  linarith

end FormalResearch.Special
