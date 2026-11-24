module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Final arithmetic of the Hankel window lemma (M5-S6b)

`hankel_window_arith` combines the three terms of the local density bound (window integral, outside-window
tail, connectors) into the single shape `C Λ N34 / (X √X)` of `YVEnvBound`.
-/

@[expose] public section

namespace FormalResearch.SignUncertainty

/-- Abstract form of the final combination; `X = Re √ũ`, `Xs = √X`, `s = ‖ũ‖^{1/2}`, `G = √(cσ)`,
`ci = c⁻¹`, `e = exp(-0.035 c σ)`, `N34 = ‖ũ‖^{-3/4}`, `Λ = c^{1/3}(B₁+B₂)+1`, `Cy = C_Y`. -/
lemma hankel_window_arith {k X Xs s σ nz G W Q Λ Cy N34 ci e : ℝ}
    (hk : 0 < k) (hX : 0 < X) (hXs : 0 < Xs) (hs : 0 < s) (hσ : 0 < σ) (hnz : 0 ≤ nz)
    (hG : 0 < G) (hQ : 0 ≤ Q) (hΛ : 1 ≤ Λ) (hCy : 0 < Cy) (hN : 0 ≤ N34) (hci : 0 < ci) (he : 0 ≤ e)
    (hW : W ≤ Q * (11 / 10 * nz / σ)) (hnzσ : nz / σ ≤ 1.002 * s / X) (hQs : Q * s ≤ Cy * Λ * N34)
    (hGk : k * Xs ≤ G) (hci_le : ci ≤ N34 / (X * Xs)) (hkc : k * ci ≤ 1) (hek : e * k ≤ 1)
    {A : ℝ} (hA : A ≤ (100 / 81) * W * (3 / G)) :
    0.272 * k * (A + (4 / 3) * ci ^ 2 + 2 * (2 * e * ci / 0.07)) ≤
      (1.2 * Cy * Λ + 17) * (N34 / (X * Xs)) := by
  set D := X * Xs with hD
  have hD0 : 0 < D := mul_pos hX hXs
  -- k / G ≤ 1 / Xs
  have hkG : k / G ≤ 1 / Xs := by
    rw [div_le_div_iff₀ hG hXs]; linarith
  -- W / Xs bound
  have hWb : W ≤ Q * (1.1 * 1.002 * s / X) := by
    have h1 : 11 / 10 * nz / σ = 1.1 * (nz / σ) := by ring
    rw [h1] at hW
    have h2 : 1.1 * (nz / σ) ≤ 1.1 * (1.002 * s / X) := by gcongr
    have h3 := mul_le_mul_of_nonneg_left h2 hQ
    have e1 : Q * (1.1 * 1.002 * s / X) = Q * (1.1 * (1.002 * s / X)) := by ring
    rw [e1]; exact hW.trans h3
  have hT1 : 0.272 * k * A ≤ 1.2 * Cy * Λ * (N34 / D) := by
    have h1 : 0.272 * k * A ≤ 0.272 * k * ((100 / 81) * W * (3 / G)) := by gcongr
    have h2 : 0.272 * k * ((100 / 81) * W * (3 / G)) = 0.272 * (100 / 81) * 3 * W * (k / G) := by ring
    have hW1 : 0 ≤ W ∨ W < 0 := le_or_gt 0 W
    rcases hW1 with hW1 | hW1
    · have h3 : W * (k / G) ≤ W * (1 / Xs) := by gcongr
      have h4 : W / Xs ≤ Q * (1.1 * 1.002 * s / X) / Xs := by gcongr
      have h5 : Q * (1.1 * 1.002 * s / X) / Xs = 1.1 * 1.002 * (Q * s) / D := by
        rw [hD]; field_simp
      have h6 : 1.1 * 1.002 * (Q * s) / D ≤ 1.1 * 1.002 * (Cy * Λ * N34) / D := by gcongr
      have h7 : 0.272 * (100 / 81) * 3 * W * (k / G) ≤ 0.272 * (100 / 81) * 3 * (1.1 * 1.002 * (Cy * Λ * N34) / D) := by
        have : W * (k / G) ≤ 1.1 * 1.002 * (Cy * Λ * N34) / D := by
          calc W * (k / G) ≤ W * (1 / Xs) := h3
            _ = W / Xs := by ring
            _ ≤ _ := h4.trans (h5 ▸ h6)
        nlinarith
      have h8 : 0.272 * (100 / 81) * 3 * (1.1 * 1.002 * (Cy * Λ * N34) / D) ≤ 1.2 * Cy * Λ * (N34 / D) := by
        have hh : 0 ≤ Cy * Λ * (N34 / D) := by positivity
        have : 0.272 * (100 / 81) * 3 * (1.1 * 1.002 * (Cy * Λ * N34) / D) =
            (0.272 * (100 / 81) * 3 * 1.1 * 1.002) * (Cy * Λ * (N34 / D)) := by ring
        rw [this]
        have : 1.2 * Cy * Λ * (N34 / D) = 1.2 * (Cy * Λ * (N34 / D)) := by ring
        rw [this]
        have hc : (0.272 * (100 / 81) * 3 * 1.1 * 1.002 : ℝ) ≤ 1.2 := by norm_num
        exact mul_le_mul_of_nonneg_right hc hh
      linarith
    · have : 0.272 * (100 / 81) * 3 * W * (k / G) ≤ 0 := by
        have : 0 ≤ k / G := by positivity
        nlinarith
      have : 0 ≤ 1.2 * Cy * Λ * (N34 / D) := by positivity
      linarith
  have hT2 : 0.272 * k * ((4 / 3) * ci ^ 2) ≤ 0.4 * ci := by
    have : k * ci ^ 2 ≤ ci := by nlinarith
    nlinarith
  have hT3 : 0.272 * k * (2 * (2 * e * ci / 0.07)) ≤ 16 * ci := by
    have h1 : e * k * ci ≤ ci := by nlinarith
    have h2 : 0.272 * k * (2 * (2 * e * ci / 0.07)) = (4 * 0.272 / 0.07) * (e * k * ci) := by ring
    rw [h2]
    have h3 : (4 * 0.272 / 0.07 : ℝ) ≤ 16 := by norm_num
    nlinarith [mul_nonneg (mul_nonneg he hk.le) hci.le]
  have hci' : ci ≤ N34 / D := hci_le
  have hΛN : 0 ≤ Cy * Λ * (N34 / D) := by positivity
  have hND : 0 ≤ N34 / D := by positivity
  nlinarith

end FormalResearch.SignUncertainty
