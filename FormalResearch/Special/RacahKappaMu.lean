module

public import FormalResearch.Special.DiscreteAiryKappaOrderSetup

/-!
# Absorbing the exponentially small `μ`-term into an amplitude `K ≥ |κ|`

`kk_rest` (`DiscreteAiryKappaOrderSetup`) removes the `μ g Bi` part of the Airy matching under the hypothesis `(450G + C)|μ| E ≤ δ³|κ|`, which needs a lower bound on `|κ|`.  `rk_rest` does it with a free
amplitude `K ≥ |κ|` (the conclusion is `|Y - κ g Ai| ≤ (C+1)δ³K`, `K = |κ| + K_μ` with `K_μ = (450G + C)|μ|E/δ³` always admissible), and `rk_Kmu_small` shows `K_μ ≤ κ_min` for `δ` small when
`|μ| ≤ C_μ (c_s/δ³) e^{-ξ₀/δ³}/δ`.

**Claim class: proved.**
-/

@[expose] public section

namespace FormalResearch.Special

/-- `kk_rest` with a free amplitude `K ≥ |κ|`. -/
lemma rk_rest {Y g A B κ μ C δ G W W' E K : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hG : 0 ≤ G)
    (hY : |Y - (κ * (g * A) + μ * (g * B))| ≤ C * δ ^ 3 * (|κ| * W + |μ| * W')) (hg : |g| ≤ G) (hW : W ≤ 1)
    (hW' : W' ≤ E) (hW'0 : 0 ≤ W') (hB : |B| ≤ 450 * W') (hK : |κ| ≤ K)
    (hμ : (450 * G + C) * |μ| * E ≤ δ ^ 3 * K) : |Y - κ * (g * A)| ≤ (C + 1) * δ ^ 3 * K := by
  have hδ3 : δ ^ 3 ≤ 1 := pow_le_one₀ hδ.le hδ1
  have hE : 0 ≤ E := hW'0.trans hW'
  have t1 : |μ * (g * B)| ≤ 450 * G * |μ| * E := by
    rw [abs_mul, abs_mul]
    have h1 : |g| * |B| ≤ G * (450 * E) := mul_le_mul hg (hB.trans (by linarith)) (abs_nonneg _) hG
    nlinarith [abs_nonneg μ]
  have t2 : C * δ ^ 3 * (|κ| * W + |μ| * W') ≤ C * δ ^ 3 * K + C * |μ| * E := by
    have a1 : |κ| * W ≤ K := (mul_le_of_le_one_right (abs_nonneg _) hW).trans hK
    have a2 : |μ| * W' ≤ |μ| * E := mul_le_mul_of_nonneg_left hW' (abs_nonneg _)
    have a3 : C * δ ^ 3 * (|μ| * E) ≤ C * (|μ| * E) := by
      have : 0 ≤ C * (|μ| * E) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hδ3 this]
    have a4 : C * δ ^ 3 * (|κ| * W) ≤ C * δ ^ 3 * K := mul_le_mul_of_nonneg_left a1 (by positivity)
    have a5 : C * δ ^ 3 * (|μ| * W') ≤ C * δ ^ 3 * (|μ| * E) := mul_le_mul_of_nonneg_left a2 (by positivity)
    have e1 : C * δ ^ 3 * (|κ| * W + |μ| * W') = C * δ ^ 3 * (|κ| * W) + C * δ ^ 3 * (|μ| * W') := by ring
    have e2 : C * |μ| * E = C * (|μ| * E) := by ring
    rw [e1, e2]; linarith
  have e : Y - κ * (g * A) = (Y - (κ * (g * A) + μ * (g * B))) + μ * (g * B) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  nlinarith

/-- `K_μ = (450 G + C)|μ| e^{7/δ²}/δ³` is `≤ κ_min` for `|μ| ≤ C_μ (c_s/δ³) e^{-ξ₀/δ³}/δ` and `δ` small. -/
lemma rk_Kmu_small {δ ξ0 Cmu cs G C κmin μ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hξ : 0 < ξ0) (hCmu : 0 ≤ Cmu) (hcs : 0 ≤ cs)
    (hG : 0 ≤ G) (hC : 0 ≤ C) (h1 : δ ≤ ξ0 / 14) (h2 : δ ≤ κmin * ξ0 ^ 3 / (48 * ((450 * G + C) * Cmu * cs + 1)))
    (hμ : |μ| ≤ Cmu * (cs / δ ^ 3) * Real.exp (-ξ0 / δ ^ 3) / δ) :
    (450 * G + C) * |μ| * Real.exp (7 / δ ^ 2) / δ ^ 3 ≤ κmin := by
  have hδ3 : 0 < δ ^ 3 := by positivity
  have hB : 0 ≤ (450 * G + C) * Cmu * cs := by positivity
  have hsm := kk_mu_small hδ hδ1 hξ hB h1 h2
  rw [div_le_iff₀ hδ3]
  have h0 : 0 ≤ (450 * G + C) * Real.exp (7 / δ ^ 2) := by positivity
  calc (450 * G + C) * |μ| * Real.exp (7 / δ ^ 2) = ((450 * G + C) * Real.exp (7 / δ ^ 2)) * |μ| := by ring
    _ ≤ ((450 * G + C) * Real.exp (7 / δ ^ 2)) * (Cmu * (cs / δ ^ 3) * Real.exp (-ξ0 / δ ^ 3) / δ) :=
        mul_le_mul_of_nonneg_left hμ h0
    _ = (450 * G + C) * Cmu * cs * (1 / δ ^ 3) * (Real.exp (-ξ0 / δ ^ 3) / δ) * Real.exp (7 / δ ^ 2) := by ring
    _ ≤ δ ^ 3 * κmin := hsm
    _ = κmin * δ ^ 3 := by ring

end FormalResearch.Special
