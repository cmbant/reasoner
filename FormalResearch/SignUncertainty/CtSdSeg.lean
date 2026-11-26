module

public import FormalResearch.SignUncertainty.CtSdLine

/-!
# Two integrations by parts along a complex segment (`ct:cfu` Step 3, connecting arc)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu`, Step 3 ("Tail and connecting arc": integrating by parts
twice with `e^{kP} = (kP')^{-1}∂e^{kP}`, `k = i`).  **Proved.**  For functions `F`, `G = P'` holomorphic near a segment with `G ≠ 0`:
`∫ F e^{kP} = [Ψ₁ - k^{-1}Ψ₂]_{start}^{end} + k^{-2} ∫ Q e^{kP}` with `Ψ₁ = F/(kG) e^{kP}`, `Ψ₂ = H/(kG) e^{kP}`, `H = (F/G)'`,
`Q = (H/G)'` (explicit in `F, F', F'', G, G', G''`).
-/

@[expose] public section

open Set Filter Topology MeasureTheory Metric Complex
open scoped Real

namespace FormalResearch.SignUncertainty.CtSd

/-- `H = (F/G)'` written with `F' = F1`, `G' = G1`. -/
noncomputable def segH (F F1 G G1 : ℂ → ℂ) (z : ℂ) : ℂ := (F1 z * G z - F z * G1 z) / G z ^ 2

/-- `H'` written with `F'' = F2`, `G'' = G2`. -/
noncomputable def segHd (F F1 F2 G G1 G2 : ℂ → ℂ) (z : ℂ) : ℂ :=
  (F2 z * G z - F z * G2 z) / G z ^ 2 - 2 * ((F1 z * G z - F z * G1 z) / G z ^ 2) * G1 z / G z

/-- `Q = (H/G)'`. -/
noncomputable def segQ (F F1 F2 G G1 G2 : ℂ → ℂ) (z : ℂ) : ℂ :=
  (segHd F F1 F2 G G1 G2 z * G z - segH F F1 G G1 z * G1 z) / G z ^ 2

lemma hasDerivAt_segH {F F1 F2 G G1 G2 : ℂ → ℂ} {z : ℂ} (hF : HasDerivAt F (F1 z) z) (hF1 : HasDerivAt F1 (F2 z) z)
    (hG : HasDerivAt G (G1 z) z) (hG1 : HasDerivAt G1 (G2 z) z) (hne : G z ≠ 0) :
    HasDerivAt (segH F F1 G G1) (segHd F F1 F2 G G1 G2 z) z := by
  have hN : HasDerivAt (fun y => F1 y * G y - F y * G1 y)
      (F2 z * G z + F1 z * G1 z - (F1 z * G1 z + F z * G2 z)) z := (hF1.mul hG).sub (hF.mul hG1)
  have hD : HasDerivAt (fun y => G y ^ 2) (2 * G z * G1 z) z := by
    have := hG.mul hG
    convert this using 1
    · funext y; simp [sq]
    · ring
  have h := hN.div hD (pow_ne_zero 2 hne)
  unfold segH segHd
  refine h.congr_deriv ?_
  field_simp
  ring

lemma hasDerivAt_segHG {F F1 F2 G G1 G2 : ℂ → ℂ} {z : ℂ} (hF : HasDerivAt F (F1 z) z) (hF1 : HasDerivAt F1 (F2 z) z)
    (hG : HasDerivAt G (G1 z) z) (hG1 : HasDerivAt G1 (G2 z) z) (hne : G z ≠ 0) :
    HasDerivAt (fun y => segH F F1 G G1 y / G y) (segQ F F1 F2 G G1 G2 z) z := by
  have h := (hasDerivAt_segH hF hF1 hG hG1 hne).div hG hne
  unfold segQ
  exact h

lemma continuousOn_line_of_hasDerivAt {z₀ d : ℂ} {a b : ℝ} {f f' : ℂ → ℂ}
    (h : ∀ t ∈ Icc a b, HasDerivAt f (f' (z₀ + (t : ℂ) * d)) (z₀ + (t : ℂ) * d)) :
    ContinuousOn (fun t : ℝ => f (z₀ + (t : ℂ) * d)) (Icc a b) := by
  have hpt : Continuous fun t : ℝ => z₀ + (t : ℂ) * d := by fun_prop
  intro t ht
  exact ((h t ht).continuousAt.comp (f := fun t : ℝ => z₀ + (t : ℂ) * d) hpt.continuousAt).continuousWithinAt

/-- **Double integration by parts along a segment.** -/
theorem seg_ibp2 {k : ℂ} (hk : k ≠ 0) {z₀ d : ℂ} {a b : ℝ} (hab : a ≤ b) {P F F1 F2 G G1 G2 : ℂ → ℂ}
    (hP : ∀ t ∈ Icc a b, HasDerivAt P (G (z₀ + (t : ℂ) * d)) (z₀ + (t : ℂ) * d))
    (hF : ∀ t ∈ Icc a b, HasDerivAt F (F1 (z₀ + (t : ℂ) * d)) (z₀ + (t : ℂ) * d))
    (hF1 : ∀ t ∈ Icc a b, HasDerivAt F1 (F2 (z₀ + (t : ℂ) * d)) (z₀ + (t : ℂ) * d))
    (hG : ∀ t ∈ Icc a b, HasDerivAt G (G1 (z₀ + (t : ℂ) * d)) (z₀ + (t : ℂ) * d))
    (hG1 : ∀ t ∈ Icc a b, HasDerivAt G1 (G2 (z₀ + (t : ℂ) * d)) (z₀ + (t : ℂ) * d))
    (hne : ∀ t ∈ Icc a b, G (z₀ + (t : ℂ) * d) ≠ 0)
    (hcF2 : ContinuousOn (fun t : ℝ => F2 (z₀ + (t : ℂ) * d)) (Icc a b))
    (hcG2 : ContinuousOn (fun t : ℝ => G2 (z₀ + (t : ℂ) * d)) (Icc a b)) :
    lineInt z₀ d a b (fun z => F z * Complex.exp (k * P z)) =
      (F (z₀ + (b : ℂ) * d) / (k * G (z₀ + (b : ℂ) * d)) * Complex.exp (k * P (z₀ + (b : ℂ) * d)) -
        F (z₀ + (a : ℂ) * d) / (k * G (z₀ + (a : ℂ) * d)) * Complex.exp (k * P (z₀ + (a : ℂ) * d))) -
      (1 / k) *
        (segH F F1 G G1 (z₀ + (b : ℂ) * d) / (k * G (z₀ + (b : ℂ) * d)) * Complex.exp (k * P (z₀ + (b : ℂ) * d)) -
          segH F F1 G G1 (z₀ + (a : ℂ) * d) / (k * G (z₀ + (a : ℂ) * d)) * Complex.exp (k * P (z₀ + (a : ℂ) * d))) +
      (1 / k) ^ 2 * lineInt z₀ d a b (fun z => segQ F F1 F2 G G1 G2 z * Complex.exp (k * P z)) := by
  set e : ℂ → ℂ := fun z => Complex.exp (k * P z) with he
  have hdE : ∀ t ∈ Icc a b, HasDerivAt e (e (z₀ + (t : ℂ) * d) * (k * G (z₀ + (t : ℂ) * d)))
      (z₀ + (t : ℂ) * d) := fun t ht => ((hP t ht).const_mul k).cexp
  have cF := continuousOn_line_of_hasDerivAt hF
  have cF1 := continuousOn_line_of_hasDerivAt hF1
  have cG := continuousOn_line_of_hasDerivAt hG
  have cG1 := continuousOn_line_of_hasDerivAt hG1
  have cE := continuousOn_line_of_hasDerivAt (f' := fun z => e z * (k * G z)) hdE
  have hH : ∀ t ∈ Icc a b, HasDerivAt (segH F F1 G G1) (segHd F F1 F2 G G1 G2 (z₀ + (t : ℂ) * d)) (z₀ + (t : ℂ) * d) :=
    fun t ht => hasDerivAt_segH (hF t ht) (hF1 t ht) (hG t ht) (hG1 t ht) (hne t ht)
  have cH := continuousOn_line_of_hasDerivAt hH
  have hHG : ∀ t ∈ Icc a b, HasDerivAt (fun y => segH F F1 G G1 y / G y) (segQ F F1 F2 G G1 G2 (z₀ + (t : ℂ) * d))
      (z₀ + (t : ℂ) * d) := fun t ht => hasDerivAt_segHG (hF t ht) (hF1 t ht) (hG t ht) (hG1 t ht) (hne t ht)
  have cHG := continuousOn_line_of_hasDerivAt hHG
  have cQ : ContinuousOn (fun t : ℝ => segQ F F1 F2 G G1 G2 (z₀ + (t : ℂ) * d)) (Icc a b) := by
    have hHd : ContinuousOn (fun t : ℝ => segHd F F1 F2 G G1 G2 (z₀ + (t : ℂ) * d)) (Icc a b) := by
      unfold segHd
      have c1 : ContinuousOn (fun t : ℝ => (F2 (z₀ + (t : ℂ) * d) * G (z₀ + (t : ℂ) * d) -
          F (z₀ + (t : ℂ) * d) * G2 (z₀ + (t : ℂ) * d)) / G (z₀ + (t : ℂ) * d) ^ 2) (Icc a b) :=
        ContinuousOn.div ((hcF2.mul cG).sub (cF.mul hcG2)) (cG.pow 2) (fun t ht => pow_ne_zero 2 (hne t ht))
      have c2 : ContinuousOn (fun t : ℝ => 2 * (segH F F1 G G1 (z₀ + (t : ℂ) * d)) * G1 (z₀ + (t : ℂ) * d) /
          G (z₀ + (t : ℂ) * d)) (Icc a b) :=
        ContinuousOn.div ((continuousOn_const.mul cH).mul cG1) cG (fun t ht => hne t ht)
      refine c1.sub ?_
      refine c2.congr (fun t _ => ?_)
      simp [segH]
    unfold segQ
    exact ContinuousOn.div ((hHd.mul cG).sub (cH.mul cG1)) (cG.pow 2) (fun t ht => pow_ne_zero 2 (hne t ht))
  -- Ψ₁ and Ψ₂
  set Ψ1 : ℂ → ℂ := fun z => F z / (k * G z) * e z with hΨ1
  set Ψ2 : ℂ → ℂ := fun z => segH F F1 G G1 z / (k * G z) * e z with hΨ2
  set D1 : ℂ → ℂ := fun z => (1 / k * segH F F1 G G1 z + F z) * e z with hD1
  set D2 : ℂ → ℂ := fun z => (1 / k * segQ F F1 F2 G G1 G2 z + segH F F1 G G1 z) * e z with hD2
  have hΨ1d : ∀ t ∈ Icc a b, HasDerivAt Ψ1 (D1 (z₀ + (t : ℂ) * d)) (z₀ + (t : ℂ) * d) := by
    intro t ht
    have h1 := ((hF t ht).div ((hG t ht).const_mul k) (mul_ne_zero hk (hne t ht))).mul (hdE t ht)
    refine h1.congr_deriv ?_
    have hn := hne t ht
    simp only [hD1, segH, Pi.div_apply]
    field_simp
  have hΨ2d : ∀ t ∈ Icc a b, HasDerivAt Ψ2 (D2 (z₀ + (t : ℂ) * d)) (z₀ + (t : ℂ) * d) := by
    intro t ht
    have h1 := ((hH t ht).div ((hG t ht).const_mul k) (mul_ne_zero hk (hne t ht))).mul (hdE t ht)
    refine h1.congr_deriv ?_
    have hn := hne t ht
    have hq := (hHG t ht).deriv
    simp only [hD2, segQ, segHd, segH, Pi.div_apply]
    field_simp
  have cD1 : ContinuousOn (fun t : ℝ => D1 (z₀ + (t : ℂ) * d)) (Icc a b) := by
    simp only [hD1]
    exact ((continuousOn_const.mul cH).add cF).mul cE
  have cD2 : ContinuousOn (fun t : ℝ => D2 (z₀ + (t : ℂ) * d)) (Icc a b) := by
    simp only [hD2]
    exact ((continuousOn_const.mul cQ).add cH).mul cE
  have f1 := lineInt_ftc hab hΨ1d cD1
  have f2 := lineInt_ftc hab hΨ2d cD2
  -- integral decomposition
  have intg : ∀ f : ℂ → ℂ, ContinuousOn (fun t : ℝ => f (z₀ + (t : ℂ) * d)) (Icc a b) →
      IntervalIntegrable (fun t : ℝ => f (z₀ + (t : ℂ) * d) * d) volume a b := fun f hf =>
    (hf.mul continuousOn_const).intervalIntegrable_of_Icc hab
  have lin : ∀ f g : ℂ → ℂ, ContinuousOn (fun t : ℝ => f (z₀ + (t : ℂ) * d)) (Icc a b) →
      ContinuousOn (fun t : ℝ => g (z₀ + (t : ℂ) * d)) (Icc a b) → ∀ c : ℂ,
      lineInt z₀ d a b (fun z => c * f z + g z) = c * lineInt z₀ d a b f + lineInt z₀ d a b g := by
    intro f g hf hg c
    unfold lineInt
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add
      ((intg f hf).const_mul c) (intg g hg)]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    simp only [add_mul, mul_assoc]
  have cHe : ContinuousOn (fun t : ℝ => (segH F F1 G G1 * e) (z₀ + (t : ℂ) * d)) (Icc a b) := cH.mul cE
  have cFe : ContinuousOn (fun t : ℝ => (F * e) (z₀ + (t : ℂ) * d)) (Icc a b) := cF.mul cE
  have cQe : ContinuousOn (fun t : ℝ => (segQ F F1 F2 G G1 G2 * e) (z₀ + (t : ℂ) * d)) (Icc a b) := cQ.mul cE
  have eD1 : lineInt z₀ d a b D1 = (1 / k) * lineInt z₀ d a b (fun z => segH F F1 G G1 z * e z) +
      lineInt z₀ d a b (fun z => F z * e z) := by
    have := lin (fun z => segH F F1 G G1 z * e z) (fun z => F z * e z) cHe cFe (1 / k)
    rw [← this]
    unfold lineInt
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    simp only [hD1]
    ring
  have eD2 : lineInt z₀ d a b D2 = (1 / k) * lineInt z₀ d a b (fun z => segQ F F1 F2 G G1 G2 z * e z) +
      lineInt z₀ d a b (fun z => segH F F1 G G1 z * e z) := by
    have := lin (fun z => segQ F F1 F2 G G1 G2 z * e z) (fun z => segH F F1 G G1 z * e z) cQe cHe (1 / k)
    rw [← this]
    unfold lineInt
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    simp only [hD2]
    ring
  rw [eD1] at f1
  rw [eD2] at f2
  simp only [hΨ1, hΨ2, he] at f1 f2 ⊢
  have hk' : (1 / k) * k = 1 := by field_simp
  linear_combination f1 - (1 / k) * f2

end FormalResearch.SignUncertainty.CtSd
