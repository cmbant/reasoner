module

public import Mathlib

/-!
# A smooth `O(c'^{-1})` factor against the tip kernel (FIVE-U; `cts:tip-shared` (d))

Source: `CFT/modular_bootstrap/paper/constant_term_slit_strip.tex`, Lemma C11$_0$ (`cts:tip-shared`) (d).

`tipShared_d` is (d) in explicit-constant form: over `σ̂ ∈ [lo, hi]` with `|W| ≤ C₀ (1+|σ̂|)^{-3/2}`,
`|∫ W| ≤ M₁`, `|G| ≤ C_G`, `|G-1| ≤ C_λ λ (1+|σ̂|)`, `|H₀| ≤ η`, `|H - H₀| ≤ C_H η λ (1+|σ̂|)` and
`∫ (1+|σ̂|)^{-1/2} ≤ A`, one has
`|∫ W G H| ≤ η (M₁ + C₀ C_λ λ A) + C₀ C_G C_H η λ A`. The paper's scalings (`η = c'^{-1}`, `λ = c'^{-2/3}`,
`M₁ = C c'^{-1/3}`, `A ≤ C c'^{1/3}`) give `O(c'^{-4/3})`. The hypothesis `|H - H₀| ≤ C_H η λ (1+|σ̂|)` is the
paper's `|h(x) - h(ξ_*)| ≤ C c'^{-5/3}(1+|σ̂|)` (from `|h'| ≤ C c'^{-1}` and `|x - ξ_*| ≤ Cλ(1+|σ̂|)`).

Proved (no numerical input). The kernel hypotheses (`cts:shifted-langer` (2)) are inputs, not proved here.
-/

@[expose] public section

open MeasureTheory Set intervalIntegral

namespace FormalResearch.ModularBootstrap.FiveTerm

lemma tipShared_d_aux {lo hi : ℝ} (hlo : lo ≤ hi) {W G : ℝ → ℝ} {CG : ℝ}
    (hW : IntervalIntegrable W volume lo hi) (hGm : AEStronglyMeasurable G (volume.restrict (Ioc lo hi)))
    (hGb : ∀ s ∈ Icc lo hi, |G s| ≤ CG) :
    IntervalIntegrable (fun s => W s * G s) volume lo hi := by
  have hW' : IntervalIntegrable (fun s => |CG| * |W s|) volume lo hi := by
    have := (hW.norm).const_mul |CG|
    simpa using this
  refine hW'.mono_fun ?_ ?_
  · rw [uIoc_of_le hlo]; exact hW.1.aestronglyMeasurable.mul hGm
  rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
  refine Filter.Eventually.of_forall fun s hs => ?_
  rw [uIoc_of_le hlo] at hs
  have := hGb s ⟨hs.1.le, hs.2⟩
  simp only [norm_mul, Real.norm_eq_abs, abs_abs]
  nlinarith only [this, abs_nonneg (W s), le_abs_self CG, abs_nonneg (G s)]


/-- **Smooth `O(c'^{-1})` factor against the tip kernel** (`cts:tip-shared` (d), explicit-constant form).
Over `σ̂ ∈ [lo, hi]`: `|W| ≤ C₀ (1+|σ̂|)^{-3/2}`, `|∫ W| ≤ M₁`, `|G| ≤ C_G`, `|G-1| ≤ C_λ λ (1+|σ̂|)`,
`|H₀| ≤ η`, `|H - H₀| ≤ C_H η λ (1+|σ̂|)`, `∫ (1+|σ̂|)^{-1/2} ≤ A`. Then
`|∫ W G H| ≤ η (M₁ + C₀ C_λ λ A) + C₀ C_G C_H η λ A`.
(The paper's scalings: `η = c'^{-1}`, `λ = c'^{-2/3}`, `M₁ = C c'^{-1/3}`, `A ≤ C c'^{1/3}`, giving `O(c'^{-4/3})`.) -/
theorem tipShared_d {lo hi : ℝ} (hlo : lo ≤ hi) {W G H : ℝ → ℝ}
    {C0 CG Cl CH M1 lam eta H0 A : ℝ}
    (hC0 : 0 ≤ C0) (hCG : 0 ≤ CG) (hCl : 0 ≤ Cl) (hCH : 0 ≤ CH) (hlam : 0 ≤ lam) (heta : 0 ≤ eta)
    (hW : IntervalIntegrable W volume lo hi)
    (hGm : AEStronglyMeasurable G (volume.restrict (Ioc lo hi)))
    (hHm : AEStronglyMeasurable H (volume.restrict (Ioc lo hi)))
    (hWb : ∀ s ∈ Icc lo hi, |W s| ≤ C0 * (1 + |s|) ^ (-(3 / 2 : ℝ)))
    (hWi : |∫ s in lo..hi, W s| ≤ M1)
    (hGb : ∀ s ∈ Icc lo hi, |G s| ≤ CG)
    (hG1 : ∀ s ∈ Icc lo hi, |G s - 1| ≤ Cl * lam * (1 + |s|))
    (hH0 : |H0| ≤ eta)
    (hHb : ∀ s ∈ Icc lo hi, |H s - H0| ≤ CH * eta * lam * (1 + |s|))
    (hA : ∫ s in lo..hi, (1 + |s|) ^ (-(1 / 2 : ℝ)) ≤ A) :
    |∫ s in lo..hi, W s * G s * H s| ≤
      eta * (M1 + C0 * Cl * lam * A) + C0 * CG * CH * eta * lam * A := by
  have hrp : ∀ s : ℝ, 0 ≤ (1 + |s|) ^ (-(1 / 2 : ℝ)) := fun s => by positivity
  have hrp1 : ∀ s : ℝ, (1 + |s|) ^ (-(3 / 2 : ℝ)) * (1 + |s|) = (1 + |s|) ^ (-(1 / 2 : ℝ)) := by
    intro s
    have h0 : (0 : ℝ) < 1 + |s| := by positivity
    have := Real.rpow_add h0 (-(3 / 2 : ℝ)) 1
    rw [Real.rpow_one] at this
    rw [← this]; norm_num
  have hgi : IntervalIntegrable (fun s : ℝ => (1 + |s|) ^ (-(1 / 2 : ℝ))) volume lo hi := by
    apply Continuous.intervalIntegrable
    exact Continuous.rpow_const (by fun_prop) (fun s => Or.inl (by positivity))
  have hWG : IntervalIntegrable (fun s => W s * G s) volume lo hi := tipShared_d_aux hlo hW hGm hGb
  have hBH : ∃ B, ∀ s ∈ Icc lo hi, |H s - H0| ≤ B :=
    ⟨CH * eta * lam * (1 + max |lo| |hi|), fun s hs => (hHb s hs).trans (by
      have : |s| ≤ max |lo| |hi| := by
        rcases le_total 0 s with h | h
        · rw [abs_of_nonneg h]; exact le_max_of_le_right (by rw [abs_of_nonneg (h.trans hs.2)]; exact hs.2)
        · rw [abs_of_nonpos h]; exact le_max_of_le_left (by
            rw [abs_of_nonpos (hs.1.trans h)]; linarith [hs.1])
      have hc : 0 ≤ CH * eta * lam := by positivity
      exact mul_le_mul_of_nonneg_left (by linarith) hc)⟩
  obtain ⟨B, hB⟩ := hBH
  have hWGH : IntervalIntegrable (fun s => W s * G s * (H s - H0)) volume lo hi :=
    tipShared_d_aux hlo hWG (hHm.sub aestronglyMeasurable_const) hB
  have hsplit : (fun s => W s * G s * H s) = fun s => H0 * (W s * G s) + W s * G s * (H s - H0) := by
    funext s; ring
  have hsplit2 : (fun s => W s * G s) = fun s => W s + W s * (G s - 1) := by funext s; ring
  have hWG1 : IntervalIntegrable (fun s => W s * (G s - 1)) volume lo hi := by
    have := hWG.sub hW
    refine this.congr ?_
    exact fun s _ => by ring
  have hb1 : |∫ s in lo..hi, W s * (G s - 1)| ≤ ∫ s in lo..hi, C0 * Cl * lam * (1 + |s|) ^ (-(1 / 2 : ℝ)) := by
    have := intervalIntegral.norm_integral_le_of_norm_le hlo (f := fun s => W s * (G s - 1))
      (g := fun s => C0 * Cl * lam * (1 + |s|) ^ (-(1 / 2 : ℝ))) ?_ (hgi.const_mul _)
    · simpa using this
    · refine Filter.Eventually.of_forall fun s hs => ?_
      have hs' : s ∈ Icc lo hi := ⟨hs.1.le, hs.2⟩
      rw [Real.norm_eq_abs, abs_mul]
      calc |W s| * |G s - 1| ≤ (C0 * (1 + |s|) ^ (-(3 / 2 : ℝ))) * (Cl * lam * (1 + |s|)) :=
            mul_le_mul (hWb s hs') (hG1 s hs') (abs_nonneg _) (by positivity)
        _ = C0 * Cl * lam * ((1 + |s|) ^ (-(3 / 2 : ℝ)) * (1 + |s|)) := by ring
        _ = _ := by rw [hrp1]
  have hb2 : |∫ s in lo..hi, W s * G s * (H s - H0)| ≤
      ∫ s in lo..hi, C0 * CG * CH * eta * lam * (1 + |s|) ^ (-(1 / 2 : ℝ)) := by
    have := intervalIntegral.norm_integral_le_of_norm_le hlo (f := fun s => W s * G s * (H s - H0))
      (g := fun s => C0 * CG * CH * eta * lam * (1 + |s|) ^ (-(1 / 2 : ℝ))) ?_ (hgi.const_mul _)
    · simpa using this
    · refine Filter.Eventually.of_forall fun s hs => ?_
      have hs' : s ∈ Icc lo hi := ⟨hs.1.le, hs.2⟩
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      calc |W s| * |G s| * |H s - H0| ≤ (C0 * (1 + |s|) ^ (-(3 / 2 : ℝ))) * CG *
            (CH * eta * lam * (1 + |s|)) :=
            mul_le_mul (mul_le_mul (hWb s hs') (hGb s hs') (abs_nonneg _) (by positivity))
              (hHb s hs') (abs_nonneg _) (by positivity)
        _ = C0 * CG * CH * eta * lam * ((1 + |s|) ^ (-(3 / 2 : ℝ)) * (1 + |s|)) := by ring
        _ = _ := by rw [hrp1]
  rw [intervalIntegral.integral_const_mul] at hb1 hb2
  rw [hsplit, intervalIntegral.integral_add (hWG.const_mul H0) hWGH, intervalIntegral.integral_const_mul]
  have hI1 : ∫ s in lo..hi, W s * G s = (∫ s in lo..hi, W s) + ∫ s in lo..hi, W s * (G s - 1) := by
    rw [hsplit2, intervalIntegral.integral_add hW hWG1]
  have hI1b : |∫ s in lo..hi, W s * G s| ≤ M1 + C0 * Cl * lam * A := by
    rw [hI1]
    refine (abs_add_le _ _).trans (add_le_add hWi (hb1.trans ?_))
    exact mul_le_mul_of_nonneg_left hA (by positivity)
  have hI2b : |∫ s in lo..hi, W s * G s * (H s - H0)| ≤ C0 * CG * CH * eta * lam * A :=
    hb2.trans (mul_le_mul_of_nonneg_left hA (by positivity))
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul]
  have hM : 0 ≤ M1 + C0 * Cl * lam * A := (abs_nonneg _).trans hI1b
  nlinarith only [mul_le_mul hH0 hI1b (abs_nonneg _) heta, hI2b]

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.tipShared_d' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tipShared_d

end FormalResearch.ModularBootstrap.FiveTerm
