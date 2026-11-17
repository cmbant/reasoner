module

public import FormalResearch.Special.DiscreteAirySecondCh

/-!
# Second-order Airy parametrix, part 2: third-order Grönwall remainders at fixed `ζ`, signed `t`

With `h = t³` (`t ≠ 0` of **either sign**: the scaled shift functions `apuCs z t s = C(z/t², t s)`, `apuSs z t s = S(z/t², t s)/t`
solve `Y_ss = (z + t³ s) Y` for every `t ≠ 0`) and the closed forms of `DiscreteAirySecondCh`:

* `apu2_C_remainder`: `|Cs - (E + h O + h² C₂)| ≤ K |h|³` and `|Cs' - (E' + h O' + h² C₂')| ≤ K |h|³`;
* `apu2_S_remainder`: `|Ss - (A + h B + h² S₂)| ≤ K |h|³` and `|Ss' - (E + h B' + h² S₂')| ≤ K |h|³`,

uniformly for `|ζ| ≤ Z₀`, `|s| ≤ S`, `0 < |t| ≤ 1`.  The remainder `R = Cs - (E+hO+h²C₂)` solves
`R'' = (ζ + h s) R + h³ s C₂` (`R(0) = R'(0) = 0`), resp. `h³ s S₂`; `apu_gron` gives `R`, and `R'` follows by the mean value
theorem from `R'' = qR + f`.  **Claim class: proved**; constants existential.
-/

@[expose] public section

open Set

namespace FormalResearch.Special

/-- From `R'' = q R + f` and `|R| ≤ Rb`: `|R'| ≤ S (L Rb + φ)` on `|x| ≤ S` (`R'(0) = 0`). -/
lemma apu2_R1_bound {R R1 q f : ℝ → ℝ} {L φ S Rb : ℝ}
    (hR1 : ∀ x, HasDerivAt R1 (q x * R x + f x) x) (hq : ∀ x, |x| ≤ S → |q x| ≤ L)
    (hf : ∀ x, |x| ≤ S → |f x| ≤ φ) (hR : ∀ x, |x| ≤ S → |R x| ≤ Rb) (hR10 : R1 0 = 0) (hL : 0 ≤ L)
    (hRb : 0 ≤ Rb) (x : ℝ) (hx : |x| ≤ S) : |R1 x| ≤ (L * Rb + φ) * S := by
  have hφ : 0 ≤ φ := (abs_nonneg _).trans (hf 0 (by simpa using (abs_nonneg x).trans hx))
  have h := apx_taylor_step (g := R1) (g' := fun y => q y * R y + f y) (s := x) (B := L * Rb + φ)
    (fun t _ => hR1 t) (fun t ht => by
      have ht' : |t| ≤ S := by
        have : |t| ≤ |x| := by
          rcases le_total 0 x with h0 | h0
          · rw [uIcc_of_le h0] at ht; rw [abs_of_nonneg ht.1, abs_of_nonneg h0]; exact ht.2
          · rw [uIcc_of_ge h0] at ht; rw [abs_of_nonpos ht.2, abs_of_nonpos h0]; linarith [ht.1]
        exact this.trans hx
      calc |q t * R t + f t| ≤ |q t * R t| + |f t| := abs_add_le _ _
        _ ≤ L * Rb + φ := by
          rw [abs_mul]
          exact add_le_add (mul_le_mul (hq t ht') (hR t ht') (abs_nonneg _) hL) (hf t ht'))
    x right_mem_uIcc
  rw [hR10, sub_zero] at h
  have h0 : 0 ≤ L * Rb + φ := by positivity
  calc |R1 x| ≤ (L * Rb + φ) * |x| := h
    _ ≤ (L * Rb + φ) * S := mul_le_mul_of_nonneg_left hx h0


lemma apu2_q_bound {Z0 S t z x : ℝ} (hz : |z| ≤ Z0) (hx : |x| ≤ S) (ht : |t| ≤ 1) :
    |z + t ^ 3 * x| ≤ Z0 + S := by
  have h3 : |t ^ 3| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) ht
  calc |z + t ^ 3 * x| ≤ |z| + |t ^ 3 * x| := abs_add_le _ _
    _ ≤ Z0 + S := by
        rw [abs_mul]
        have : |t ^ 3| * |x| ≤ 1 * S := mul_le_mul h3 hx (abs_nonneg _) zero_le_one
        linarith

/-- Abstract third-order remainder step: `R'' = q R + f` with `|q| ≤ L`, `|f| ≤ φ`, zero data at `0` gives
`|R| ≤ φ (S+1) e^{(2+L)S}` and `|R'| ≤ (L Rb + φ) S`. -/
lemma apu2_gron_both {R R1 q f : ℝ → ℝ} {L φ S : ℝ} (hR : ∀ x, HasDerivAt R (R1 x) x)
    (hR1 : ∀ x, HasDerivAt R1 (q x * R x + f x) x) (hq : ∀ x, |x| ≤ S → |q x| ≤ L)
    (hf : ∀ x, |x| ≤ S → |f x| ≤ φ) (hR0 : R 0 = 0) (hR10 : R1 0 = 0) (hL : 0 ≤ L) (hS : 0 ≤ S) :
    ∀ x, |x| ≤ S → |R x| ≤ φ * (S + 1) * Real.exp ((2 + L) * S) ∧
      |R1 x| ≤ (L * (φ * (S + 1) * Real.exp ((2 + L) * S)) + φ) * S := by
  have hφ : 0 ≤ φ := (abs_nonneg _).trans (hf 0 (by simpa using hS))
  have hRb : 0 ≤ φ * (S + 1) * Real.exp ((2 + L) * S) := by positivity
  have h1 := apu_gron hR hR1 hq hf hR0 hR10 hL hS
  intro x hx
  exact ⟨h1 x hx, apu2_R1_bound hR1 hq hf h1 hR10 hL hRb x hx⟩

/-- **`C` and `C'` at fixed `ζ`, third order** (signed `t`, `h = t³`). -/
theorem apu2_C_remainder (Z0 S : ℝ) (hZ0 : 0 ≤ Z0) (hS : 0 ≤ S) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z t s : ℝ, |z| ≤ Z0 → |s| ≤ S → t ≠ 0 → |t| ≤ 1 →
      |apuCs z t s - (apuE z s + t ^ 3 * apuO z s + (t ^ 3) ^ 2 * apuC2 z s)| ≤ K * |t ^ 3| ^ 3 ∧
      |apuCs1 z t s - (apuE1 z s + t ^ 3 * apuO1 z s + (t ^ 3) ^ 2 * apuC21 z s)| ≤ K * |t ^ 3| ^ 3 := by
  obtain ⟨M, hM0, hM⟩ := apu_bounds Z0 S hZ0 hS
  obtain ⟨M2, hM20, hM2⟩ := apu2_bounds Z0 S hZ0 hS
  set φ0 : ℝ := S * M2 with hφ0
  set Rb0 : ℝ := φ0 * (S + 1) * Real.exp ((2 + (Z0 + S)) * S) with hRb0
  refine ⟨Rb0 + ((Z0 + S) * Rb0 + φ0) * S, by positivity, ?_⟩
  intro z t s hz hs ht ht1
  have h3 : |t ^ 3| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) ht1
  have h30 : 0 ≤ |t ^ 3| := abs_nonneg _
  have hq0 : t ^ 3 ≠ 0 := pow_ne_zero 3 ht
  set R : ℝ → ℝ := fun x => apuCs z t x - (apuE z x + t ^ 3 * apuO z x + (t ^ 3) ^ 2 * apuC2 z x) with hRdef
  set R1 : ℝ → ℝ := fun x => apuCs1 z t x -
    (apuE1 z x + t ^ 3 * apuO1 z x + (t ^ 3) ^ 2 * apuC21 z x) with hR1def
  have hRd : ∀ x, HasDerivAt R (R1 x) x := fun x =>
    (apu_hasDerivAt_Cs z t x).sub (((apu_hasDerivAt_E z x).add ((apu_hasDerivAt_O z x).const_mul _)).add
      ((apu2_hasDerivAt_C2 z x).const_mul _))
  have hR1d : ∀ x, HasDerivAt R1 ((z + t ^ 3 * x) * R x + (t ^ 3) ^ 3 * (x * apuC2 z x)) x := by
    intro x
    have := (apu_hasDerivAt_Cs1 ht z x).sub
      (((apu_hasDerivAt_E1 z x).add ((apu_hasDerivAt_O1 z x).const_mul (t ^ 3))).add
        ((apu2_hasDerivAt_C21 z x).const_mul ((t ^ 3) ^ 2)))
    refine this.congr_deriv ?_
    simp only [hRdef]; ring
  have hq : ∀ x, |x| ≤ S → |z + t ^ 3 * x| ≤ Z0 + S := fun x hx => apu2_q_bound hz hx ht1
  have hf : ∀ x, |x| ≤ S → |(t ^ 3) ^ 3 * (x * apuC2 z x)| ≤ |t ^ 3| ^ 3 * φ0 := by
    intro x hx
    rw [abs_mul, abs_mul, ← abs_pow]
    exact mul_le_mul_of_nonneg_left (mul_le_mul hx (hM2 z x hz hx).1 (abs_nonneg _) hS) (by positivity)
  have key := apu2_gron_both hRd hR1d hq hf (by simp [hRdef, apuCs_zero, apuE_zero, apuO_zero, apuC2_zero])
    (by simp [hR1def, apuCs1_zero, apuE1_zero, apuO1_zero, apuC21_zero]) (by positivity) hS s hs
  obtain ⟨k1, k2⟩ := key
  simp only [hRdef, hR1def] at k1 k2
  have hT : 0 ≤ |t ^ 3| ^ 3 := by positivity
  have hRb0nn : 0 ≤ Rb0 := by positivity
  have hX : 0 ≤ ((Z0 + S) * Rb0 + φ0) * S := by positivity
  constructor
  · refine k1.trans ?_
    have e : |t ^ 3| ^ 3 * φ0 * (S + 1) * Real.exp ((2 + (Z0 + S)) * S) = |t ^ 3| ^ 3 * Rb0 := by
      rw [hRb0]; ring
    rw [e]
    nlinarith [mul_nonneg hT hX]
  · refine k2.trans ?_
    have e : ((Z0 + S) * (|t ^ 3| ^ 3 * φ0 * (S + 1) * Real.exp ((2 + (Z0 + S)) * S)) + |t ^ 3| ^ 3 * φ0) * S =
        |t ^ 3| ^ 3 * (((Z0 + S) * Rb0 + φ0) * S) := by rw [hRb0]; ring
    rw [e]
    nlinarith [mul_nonneg hT hRb0nn]

/-- **`S` and `S'` at fixed `ζ`, third order** (signed `t`, `h = t³`). -/
theorem apu2_S_remainder (Z0 S : ℝ) (hZ0 : 0 ≤ Z0) (hS : 0 ≤ S) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z t s : ℝ, |z| ≤ Z0 → |s| ≤ S → t ≠ 0 → |t| ≤ 1 →
      |apuSs z t s - (apuA z s + t ^ 3 * apuB z s + (t ^ 3) ^ 2 * apuS2 z s)| ≤ K * |t ^ 3| ^ 3 ∧
      |apuSs1 z t s - (apuE z s + t ^ 3 * apuB1 z s + (t ^ 3) ^ 2 * apuS21 z s)| ≤ K * |t ^ 3| ^ 3 := by
  obtain ⟨M2, hM20, hM2⟩ := apu2_bounds Z0 S hZ0 hS
  set φ0 : ℝ := S * M2 with hφ0
  set Rb0 : ℝ := φ0 * (S + 1) * Real.exp ((2 + (Z0 + S)) * S) with hRb0
  refine ⟨Rb0 + ((Z0 + S) * Rb0 + φ0) * S, by positivity, ?_⟩
  intro z t s hz hs ht ht1
  have h3 : |t ^ 3| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) ht1
  have h30 : 0 ≤ |t ^ 3| := abs_nonneg _
  set R : ℝ → ℝ := fun x => apuSs z t x - (apuA z x + t ^ 3 * apuB z x + (t ^ 3) ^ 2 * apuS2 z x) with hRdef
  set R1 : ℝ → ℝ := fun x => apuSs1 z t x -
    (apuE z x + t ^ 3 * apuB1 z x + (t ^ 3) ^ 2 * apuS21 z x) with hR1def
  have hRd : ∀ x, HasDerivAt R (R1 x) x := fun x =>
    (apu_hasDerivAt_Ss ht z x).sub (((apu_hasDerivAt_A z x).add ((apu_hasDerivAt_B z x).const_mul _)).add
      ((apu2_hasDerivAt_S2 z x).const_mul _))
  have hR1d : ∀ x, HasDerivAt R1 ((z + t ^ 3 * x) * R x + (t ^ 3) ^ 3 * (x * apuS2 z x)) x := by
    intro x
    have := (apu_hasDerivAt_Ss1 ht z x).sub
      (((apu_hasDerivAt_E z x).add ((apu_hasDerivAt_B1 z x).const_mul (t ^ 3))).add
        ((apu2_hasDerivAt_S21 z x).const_mul ((t ^ 3) ^ 2)))
    refine this.congr_deriv ?_
    simp only [hRdef, apuE1_eq]; ring
  have hq : ∀ x, |x| ≤ S → |z + t ^ 3 * x| ≤ Z0 + S := fun x hx => apu2_q_bound hz hx ht1
  have hf : ∀ x, |x| ≤ S → |(t ^ 3) ^ 3 * (x * apuS2 z x)| ≤ |t ^ 3| ^ 3 * φ0 := by
    intro x hx
    rw [abs_mul, abs_mul, ← abs_pow]
    exact mul_le_mul_of_nonneg_left (mul_le_mul hx (hM2 z x hz hx).2.2.1 (abs_nonneg _) hS) (by positivity)
  have key := apu2_gron_both hRd hR1d hq hf (by simp [hRdef, apuSs_zero, apuA_zero, apuB_zero, apuS2_zero])
    (by simp [hR1def, apuSs1_zero, apuE_zero, apuB1_zero, apuS21_zero]) (by positivity) hS s hs
  obtain ⟨k1, k2⟩ := key
  simp only [hRdef, hR1def] at k1 k2
  have hT : 0 ≤ |t ^ 3| ^ 3 := by positivity
  have hRb0nn : 0 ≤ Rb0 := by positivity
  have hX : 0 ≤ ((Z0 + S) * Rb0 + φ0) * S := by positivity
  constructor
  · refine k1.trans ?_
    have e : |t ^ 3| ^ 3 * φ0 * (S + 1) * Real.exp ((2 + (Z0 + S)) * S) = |t ^ 3| ^ 3 * Rb0 := by
      rw [hRb0]; ring
    rw [e]
    nlinarith [mul_nonneg hT hX]
  · refine k2.trans ?_
    have e : ((Z0 + S) * (|t ^ 3| ^ 3 * φ0 * (S + 1) * Real.exp ((2 + (Z0 + S)) * S)) + |t ^ 3| ^ 3 * φ0) * S =
        |t ^ 3| ^ 3 * (((Z0 + S) * Rb0 + φ0) * S) := by rw [hRb0]; ring
    rw [e]
    nlinarith [mul_nonneg hT hRb0nn]

/-- info: 'FormalResearch.Special.apu2_C_remainder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.apu2_C_remainder

/-- info: 'FormalResearch.Special.apu2_S_remainder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.apu2_S_remainder

end FormalResearch.Special
