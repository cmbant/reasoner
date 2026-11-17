module

public import FormalResearch.Special.BulkKappaDef
public import FormalResearch.Special.RacahKappaFam

/-!
# The explicit amplitude and phase of the Liouville-Green bulk form (Hahn / centred Racah)

Real-analysis lemmas used to turn the bulk form `BkBulkAt` (amplitude `h^{1/6}π^{-1/2} w(q)`, phase `Θ(q)/h - Θ_*/h + π/4`) into explicit closed forms once `κ² δ → 2` is known:

* `bkw_eq`: the profile of the smooth LG datum, `w(q) = dlgsW (hrA1 P Q) (hrU P Q τ x) q = √2 (s (q_*² - q²))^{-1/4}`, `s = rkS P Q x` (from `A w² sin θ = 1` and `ẽ² - (x - β₀q²)² = s(q_*² - q²)`);
* `bk_phase_sub`: `Θ(q) - Θ_* = -∫_q^{q_*} arccos u`;
* `bk_amp_est`: the algebra `h^{1/6}π^{-1/2} w κ cos χ = ± A cos χ (1 + O(κ²δ - 2))` with the explicit amplitude `A(q) = (2/√π)(s(q_*² - q²))^{-1/4}`.

**Claim class: proved.**
-/

@[expose] public section

open Finset Set FormalResearch.Racah.P3 FormalResearch.DiscreteAiry
open scoped Real

namespace FormalResearch.Special

/-- The explicit bulk amplitude `A(q) = (2/√π) (s (q_*² - q²))^{-1/4}` (`s = rkS P Q x`; `s = 1` for the `3j` chain). -/
noncomputable def bkAmp (P Q x qs q : ℝ) : ℝ := 2 / √π * (√(√(rkS P Q x * (qs ^ 2 - q ^ 2))))⁻¹

/-- The phase integral `Φ(q) = ∫_q^{q_*} arccos u(t) dt`, `u = hrU P Q τ x` (`Θ_* - Θ(q) = Φ(q)`). -/
noncomputable def bkPhase (P Q τ x qs q : ℝ) : ℝ := ∫ t in q..qs, Real.arccos (hrU P Q τ x t)

/-- **The LG profile of the Hahn / centred Racah datum**: `w(q) = √2 (s (q_*² - q²))^{-1/4}` on `0 < q < q_*`. -/
lemma bkw_eq {P Q τ x qs q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hτ : τ ^ 2 = 1) (hs : 1 - x ^ 2 = rkS P Q x * qs ^ 2)
    (hspos : 0 < rkS P Q x) (hq : 0 < q) (hqq : q < qs) (hα : 0 < 1 - P * qs ^ 2) (hβ : 0 < 1 - Q * qs ^ 2) :
    dlgsW (hrA1 P Q) (hrU P Q τ x) q = √2 * (√(√(rkS P Q x * (qs ^ 2 - q ^ 2))))⁻¹ := by
  have hq2 : q ^ 2 < qs ^ 2 := by nlinarith only [hq, hqq]
  have hP1 : 0 < 1 - P * q ^ 2 := by nlinarith only [mul_le_mul_of_nonneg_left hq2.le hP, hα]
  have hQ1 : 0 < 1 - Q * q ^ 2 := by nlinarith only [mul_le_mul_of_nonneg_left hq2.le hQ, hβ]
  have hpos : 0 < (1 - P * q ^ 2) * (1 - Q * q ^ 2) := mul_pos hP1 hQ1
  have he : etilde P Q (q ^ 2) ^ 2 = (1 - P * q ^ 2) * (1 - Q * q ^ 2) := by
    unfold etilde; exact Real.sq_sqrt hpos.le
  have hep : 0 < etilde P Q (q ^ 2) := by unfold etilde; exact Real.sqrt_pos.2 hpos
  have hkey := rl_key (P := P) (Q := Q) (x := x) (qs := qs) (σ := q ^ 2) hP hQ hs
  have hD : 0 < rkS P Q x * (qs ^ 2 - q ^ 2) := mul_pos hspos (by linarith)
  set D : ℝ := rkS P Q x * (qs ^ 2 - q ^ 2) with hDdef
  have h1u : 1 - hrU P Q τ x q ^ 2 = D / etilde P Q (q ^ 2) ^ 2 := by
    unfold hrU
    rw [div_pow, mul_pow, hτ, one_mul, ← hkey, he]
    field_simp
  have hsq : √(1 - hrU P Q τ x q ^ 2) = √D / etilde P Q (q ^ 2) := by
    rw [h1u, Real.sqrt_div hD.le, Real.sqrt_sq hep.le]
  have hA : hrA1 P Q q * √(1 - hrU P Q τ x q ^ 2) = √D / 2 := by
    unfold hrA1
    rw [hsq]; field_simp
  unfold dlgsW
  rw [hA]
  have hsD : 0 < √D := Real.sqrt_pos.2 hD
  have hssD : 0 < √(√D) := Real.sqrt_pos.2 hsD
  rw [Real.sqrt_div hsD.le, inv_div, div_eq_mul_inv]

/-- `Θ(q) - Θ_* = -Φ(q)` for the integral phase of the smooth datum. -/
lemma bk_phase_sub {P Q τ x qs c1 q : ℝ} (hcont : ContinuousOn (fun s => Real.arccos (hrU P Q τ x s)) (Set.Icc c1 qs))
    (h1 : c1 ≤ q) (h2 : q ≤ qs) :
    dlgsPhase (hrU P Q τ x) c1 q - ∫ s in c1..qs, Real.arccos (hrU P Q τ x s) = -bkPhase P Q τ x qs q := by
  have hc1 : c1 ≤ qs := h1.trans h2
  have i1 : IntervalIntegrable (fun s => Real.arccos (hrU P Q τ x s)) MeasureTheory.volume c1 q :=
    (hcont.mono (by rw [Set.uIcc_of_le h1]; exact Set.Icc_subset_Icc le_rfl h2)).intervalIntegrable
  have i2 : IntervalIntegrable (fun s => Real.arccos (hrU P Q τ x s)) MeasureTheory.volume c1 qs :=
    (hcont.mono (by rw [Set.uIcc_of_le hc1])).intervalIntegrable
  unfold dlgsPhase dlgsTheta bkPhase
  rw [intervalIntegral.integral_interval_sub_left i1 i2, intervalIntegral.integral_symm]

/-- **The amplitude algebra.**  From the bulk form `|Y - ρ π^{-1/2} W (κ cos χ + μ sin χ)| ≤ C (|κ| + |μ|) ρ δ³ W` (`ρ² = δ`), `|κ² δ - 2| ≤ t ≤ 1` and `ρ|μ| ≤ m`, for the sign
`s = ±1` with `κ = s|κ|` (the sign of `κ`): `|Y - s A cos χ| ≤ A (t/2 + m + 2C(2+m)δ³)`, `A = √2 π^{-1/2} W`. -/
lemma bk_amp_est {Y ρ δ W κ μ χ C t m : ℝ} (hρ : 0 < ρ) (hρδ : ρ ^ 2 = δ) (hW : 0 < W) (hC : 0 ≤ C) (ht : t ≤ 1)
    (hm0 : 0 ≤ m) (hδ : 0 < δ) (hk : |κ ^ 2 * δ - 2| ≤ t) (hμ : ρ * |μ| ≤ m) (s : ℝ) (hs : s = 1 ∨ s = -1) (hκs : κ = s * |κ|)
    (hb : |Y - ρ * (1 / √π) * W * (κ * Real.cos χ + μ * Real.sin χ)| ≤ C * ((|κ| + |μ|) * (ρ * δ ^ 3)) * W) :
    |Y - s * (√2 * (1 / √π) * W) * Real.cos χ| ≤ (√2 * (1 / √π) * W) * (t / 2 + m + 2 * C * (2 + m) * δ ^ 3) := by
  have hR : 0 < √π := Real.sqrt_pos.2 Real.pi_pos
  have hR2 : √π ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; nlinarith [Real.pi_lt_four]
  have hs2 : (0 : ℝ) < √2 := Real.sqrt_pos.2 (by norm_num)
  have hs2sq : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  set a : ℝ := ρ * |κ| with hadef
  have ha0 : 0 ≤ a := by positivity
  have ha2 : a ^ 2 = κ ^ 2 * δ := by rw [hadef, mul_pow, hρδ, sq_abs]; ring
  have hab : |a ^ 2 - 2| ≤ t := by rw [ha2]; exact hk
  have ha2' := abs_le.1 hab
  have ha3 : a ≤ 2 := by nlinarith [ha2'.2]
  have hass : |a - √2| ≤ t / √2 := by
    have h1 : (a - √2) * (a + √2) = a ^ 2 - 2 := by nlinarith [hs2sq]
    have h2 : √2 ≤ a + √2 := by linarith
    have h3 : |a - √2| * √2 ≤ |a - √2| * (a + √2) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    have h4 : |a - √2| * (a + √2) = |a ^ 2 - 2| := by
      rw [← h1, abs_mul, abs_of_nonneg (by linarith : 0 ≤ a + √2)]
    rw [le_div_iff₀ hs2]
    linarith
  have hs1 : |s| = 1 := by rcases hs with rfl | rfl <;> simp
  have hρκ : ρ * κ = s * a := by rw [hκs, hadef]; ring
  have hcs : |Real.cos χ| ≤ 1 := Real.abs_cos_le_one _
  have hsn : |Real.sin χ| ≤ 1 := Real.abs_sin_le_one _
  set A : ℝ := √2 * (1 / √π) * W with hA
  have hA0 : 0 < A := by positivity
  have hWA : W ≤ 2 * A := by
    have : W * (√2 * (1 / √π)) ≥ W / 2 * 1 := by
      have : 1 / 2 ≤ √2 * (1 / √π) := by
        have h1 : (1 : ℝ) ≤ √2 := by rw [Real.one_le_sqrt]; norm_num
        rw [mul_one_div, le_div_iff₀ hR]
        nlinarith
      nlinarith
    nlinarith
  -- the three terms
  have hdecomp : Y - s * A * Real.cos χ =
      (Y - ρ * (1 / √π) * W * (κ * Real.cos χ + μ * Real.sin χ)) +
        (1 / √π) * W * ((s * a - s * √2) * Real.cos χ) + ρ * (1 / √π) * W * μ * Real.sin χ := by
    rw [hA]
    linear_combination ((1 / √π) * W * Real.cos χ) * hρκ
  have t1 : |Y - ρ * (1 / √π) * W * (κ * Real.cos χ + μ * Real.sin χ)| ≤ 2 * C * (2 + m) * δ ^ 3 * A := by
    refine hb.trans ?_
    have h1 : (|κ| + |μ|) * ρ ≤ 2 + m := by
      have : (|κ| + |μ|) * ρ = a + ρ * |μ| := by rw [hadef]; ring
      rw [this]; linarith
    have h2 : (|κ| + |μ|) * (ρ * δ ^ 3) ≤ (2 + m) * δ ^ 3 := by
      have : (|κ| + |μ|) * (ρ * δ ^ 3) = ((|κ| + |μ|) * ρ) * δ ^ 3 := by ring
      rw [this]; exact mul_le_mul_of_nonneg_right h1 (by positivity)
    calc C * ((|κ| + |μ|) * (ρ * δ ^ 3)) * W ≤ C * ((2 + m) * δ ^ 3) * W := by
          apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hC) hW.le
      _ ≤ C * ((2 + m) * δ ^ 3) * (2 * A) := mul_le_mul_of_nonneg_left hWA (by positivity)
      _ = 2 * C * (2 + m) * δ ^ 3 * A := by ring
  have t2 : |(1 / √π) * W * ((s * a - s * √2) * Real.cos χ)| ≤ A * (t / 2) := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by positivity : 0 < 1 / √π), abs_of_pos hW]
    have h1 : |s * a - s * √2| = |a - √2| := by rw [← mul_sub, abs_mul, hs1, one_mul]
    rw [h1]
    have h2 : |a - √2| * |Real.cos χ| ≤ t / √2 := by
      calc |a - √2| * |Real.cos χ| ≤ |a - √2| * 1 := mul_le_mul_of_nonneg_left hcs (abs_nonneg _)
        _ ≤ t / √2 := by rw [mul_one]; exact hass
    calc 1 / √π * W * (|a - √2| * |Real.cos χ|) ≤ 1 / √π * W * (t / √2) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = A * (t / 2) := by
          rw [hA]; field_simp; rw [hs2sq]
  have t3 : |ρ * (1 / √π) * W * μ * Real.sin χ| ≤ A * m := by
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos hρ, abs_of_pos (by positivity : 0 < 1 / √π), abs_of_pos hW]
    have h1 : |μ| * |Real.sin χ| ≤ |μ| := by
      calc |μ| * |Real.sin χ| ≤ |μ| * 1 := mul_le_mul_of_nonneg_left hsn (abs_nonneg _)
        _ = |μ| := mul_one _
    calc ρ * (1 / √π) * W * |μ| * |Real.sin χ| ≤ ρ * (1 / √π) * W * |μ| :=
          mul_le_of_le_one_right (by positivity) hsn
      _ = (1 / √π) * W * (ρ * |μ|) := by ring
      _ ≤ (1 / √π) * W * m := mul_le_mul_of_nonneg_left hμ (by positivity)
      _ ≤ A * m := by
          apply mul_le_mul_of_nonneg_right _ hm0
          rw [hA]
          have : (1 : ℝ) ≤ √2 := by rw [Real.one_le_sqrt]; norm_num
          nlinarith [mul_pos (one_div_pos.2 hR) hW]
  rw [hdecomp]
  calc _ ≤ |Y - ρ * (1 / √π) * W * (κ * Real.cos χ + μ * Real.sin χ)| +
        |(1 / √π) * W * ((s * a - s * √2) * Real.cos χ)| + |ρ * (1 / √π) * W * μ * Real.sin χ| := abs_add_three _ _ _
    _ ≤ 2 * C * (2 + m) * δ ^ 3 * A + A * (t / 2) + A * m := by linarith
    _ = A * (t / 2 + m + 2 * C * (2 + m) * δ ^ 3) := by ring

/-- Continuity of the phase integrand `arccos ∘ u` on `[c₁, q_*]`. -/
lemma bk_cont {P Q τ x qs c1 : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hα : 0 < 1 - P * qs ^ 2) (hβ : 0 < 1 - Q * qs ^ 2) (hc1 : 0 ≤ c1) :
    ContinuousOn (fun s => Real.arccos (hrU P Q τ x s)) (Set.Icc c1 qs) := by
  have hu : ContinuousOn (hrU P Q τ x) (Set.Icc c1 qs) := by
    unfold hrU etilde
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro t ht
    have ht0 : 0 ≤ t := hc1.trans ht.1
    have h2 : t ^ 2 ≤ qs ^ 2 := by nlinarith [ht.2, ht.1, hc1]
    have h1 : 0 < 1 - P * t ^ 2 := by nlinarith only [mul_le_mul_of_nonneg_left h2 hP, hα]
    have h3 : 0 < 1 - Q * t ^ 2 := by nlinarith only [mul_le_mul_of_nonneg_left h2 hQ, hβ]
    exact (Real.sqrt_pos.2 (mul_pos h1 h3)).ne'
  exact Real.continuous_arccos.comp_continuousOn hu

/-- info: 'FormalResearch.Special.bk_amp_est' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.bk_amp_est

end FormalResearch.Special
