module

public import FormalResearch.Special.DiscreteLgSmooth
public import FormalResearch.Special.DiscreteLgHahnMatch
public import FormalResearch.Special.DiscreteAiryKappaSharpGeom

/-!
# The LG amplitude of the Hahn / centred Racah chains is explicit: `w² = kpP/√s`

For the closed-form Hahn / centred Racah data `A(q) = ½ ẽ(q²)`, `u(q) = τ(x - β₀q²)/ẽ(q²)` (`hrA1`, `hrU`; `β₀ = √(PQ)`, `τ² = 1`) put
`s = P + Q - 2xβ₀` (`rkS`).  At a simple turn `Φ(q_*²) = 0` one has the exact identity `1 - x² = s q_*²` and, on `0 ≤ q < q_*`,

`A(q) √(1 - u(q)²) = ½ √s √(q_*² - q²)`,    hence    `w² = 1/(A sin θ) = 2/(√s √(q_*² - q²)) = kpP/√s`

(`kpP = 2/α`, `α = √(q_*² - q²)`, the Ermakov profile of `DiscreteAiryKappaProfile`).  The Hahn chain is `s = 1`; for the actual Racah chain `P = 1/(4α²)`, `Q = 1/(4β²)`
(`α, β` the scaled triangle sides) `s = γ²/(4α²β²)`, so `1/√s = 2αβ/γ`, which is exactly the Gauss-weight constant `4AB/(2C) = (2αβ/γ)/h`.
This is the origin of the universal `κ²δ → 2` (`∫_0^{q_*} w² dq = π/√s` against the total mass `1/(√s h)`).

**Claim class: proved** (real algebra).
-/

@[expose] public section

open FormalResearch.Racah.P3 FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- `s = P + Q - 2xβ₀`, `β₀ = √(PQ)`. -/
noncomputable def rkS (P Q x : ℝ) : ℝ := P + Q - 2 * x * Real.sqrt (P * Q)

/-- The turn identity `1 - x² = s q_*²` from `Φ(q_*²) = 0` (`τ² = 1`, `P, Q ≥ 0`, `1 - Pq_*² > 0`, `1 - Qq_*² > 0`). -/
lemma rk_turn_id {P Q τ x qs : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hτ : τ ^ 2 = 1) (hα : 0 < 1 - P * qs ^ 2)
    (hβ : 0 < 1 - Q * qs ^ 2) (hturn : Phi P Q τ x (qs ^ 2) = 0) : 1 - x ^ 2 = rkS P Q x * qs ^ 2 := by
  have hint : 0 < (1 - P * qs ^ 2) * (1 - Q * qs ^ 2) := mul_pos hα hβ
  have he : etilde P Q (qs ^ 2) ^ 2 = (1 - P * qs ^ 2) * (1 - Q * qs ^ 2) := by
    unfold etilde; exact Real.sq_sqrt hint.le
  have hΦ : τ * (x - Real.sqrt (P * Q) * qs ^ 2) = etilde P Q (qs ^ 2) := by
    unfold Phi at hturn; linarith
  have hb : Real.sqrt (P * Q) ^ 2 = P * Q := Real.sq_sqrt (mul_nonneg hP hQ)
  have h1 : (τ * (x - Real.sqrt (P * Q) * qs ^ 2)) ^ 2 = (x - Real.sqrt (P * Q) * qs ^ 2) ^ 2 := by
    rw [mul_pow, hτ, one_mul]
  have h2 : (x - Real.sqrt (P * Q) * qs ^ 2) ^ 2 = (1 - P * qs ^ 2) * (1 - Q * qs ^ 2) := by
    rw [← h1, hΦ, he]
  unfold rkS
  linear_combination (-1) * h2 + qs ^ 4 * hb

/-- `|x| < 1` at a simple turn with positive `1 - Pq_*²`, `1 - Qq_*²`. -/
lemma rk_abs_x_lt {P Q τ x qs : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hτ : τ ^ 2 = 1) (hqs : 0 < qs) (hα : 0 < 1 - P * qs ^ 2)
    (hβ : 0 < 1 - Q * qs ^ 2) (hκ : 0 < 1 - τ * x) (hturn : Phi P Q τ x (qs ^ 2) = 0) : x ^ 2 < 1 := by
  have hint : 0 < (1 - P * qs ^ 2) * (1 - Q * qs ^ 2) := mul_pos hα hβ
  have hΦ : τ * (x - Real.sqrt (P * Q) * qs ^ 2) = etilde P Q (qs ^ 2) := by
    unfold Phi at hturn; linarith
  have hep : 0 < etilde P Q (qs ^ 2) := by unfold etilde; exact Real.sqrt_pos.2 hint
  have hb : Real.sqrt (P * Q) * qs ^ 2 < 1 := by
    have h1 : (Real.sqrt (P * Q) * qs ^ 2) ^ 2 < 1 := by
      have : (Real.sqrt (P * Q) * qs ^ 2) ^ 2 = (P * qs ^ 2) * (Q * qs ^ 2) := by
        rw [mul_pow, Real.sq_sqrt (mul_nonneg hP hQ)]; ring
      rw [this]
      have h2 : P * qs ^ 2 < 1 := by linarith
      have h3 : Q * qs ^ 2 < 1 := by linarith
      have h4 : 0 ≤ P * qs ^ 2 := by positivity
      have h5 : 0 ≤ Q * qs ^ 2 := by positivity
      nlinarith
    nlinarith [sq_nonneg (Real.sqrt (P * Q) * qs ^ 2), Real.sqrt_nonneg (P * Q), sq_nonneg qs]
  have hb0 : 0 ≤ Real.sqrt (P * Q) * qs ^ 2 := by positivity
  have hτc : τ = 1 ∨ τ = -1 := by
    have : (τ - 1) * (τ + 1) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h | h
    · left; linarith
    · right; linarith
  rcases hτc with rfl | rfl
  · -- τ = 1: x > β₀ qs² ≥ 0 and x < 1
    have : 0 < x - Real.sqrt (P * Q) * qs ^ 2 := by linarith
    nlinarith
  · have : 0 < -(x - Real.sqrt (P * Q) * qs ^ 2) := by linarith
    nlinarith

/-- **`A sin θ = ½ √s √(q_*² - q²)`** on the oscillatory side. -/
lemma rk_A_sin {P Q τ x qs q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hτ : τ ^ 2 = 1) (hs : 1 - x ^ 2 = rkS P Q x * qs ^ 2)
    (hq : 0 ≤ q) (hqq : q < qs) (hint : 0 < (1 - P * q ^ 2) * (1 - Q * q ^ 2)) (hspos : 0 < rkS P Q x) :
    hrA1 P Q q * Real.sqrt (1 - hrU P Q τ x q ^ 2) = 1 / 2 * (Real.sqrt (rkS P Q x) * Real.sqrt (qs ^ 2 - q ^ 2)) := by
  have hep : 0 < etilde P Q (q ^ 2) := by unfold etilde; exact Real.sqrt_pos.2 hint
  have he : etilde P Q (q ^ 2) ^ 2 = (1 - P * q ^ 2) * (1 - Q * q ^ 2) := by
    unfold etilde; exact Real.sq_sqrt hint.le
  have hb : Real.sqrt (P * Q) ^ 2 = P * Q := Real.sq_sqrt (mul_nonneg hP hQ)
  have hu2 : hrU P Q τ x q ^ 2 = (x - Real.sqrt (P * Q) * q ^ 2) ^ 2 / etilde P Q (q ^ 2) ^ 2 := by
    unfold hrU; rw [div_pow, mul_pow, hτ, one_mul]
  have hrad : etilde P Q (q ^ 2) ^ 2 - (x - Real.sqrt (P * Q) * q ^ 2) ^ 2 = rkS P Q x * (qs ^ 2 - q ^ 2) := by
    rw [he]; unfold rkS at hs ⊢; linear_combination hs - q ^ 4 * hb
  have hpos : 0 < rkS P Q x * (qs ^ 2 - q ^ 2) := mul_pos hspos (by nlinarith)
  have h1 : 1 - hrU P Q τ x q ^ 2 = (rkS P Q x * (qs ^ 2 - q ^ 2)) / etilde P Q (q ^ 2) ^ 2 := by
    rw [hu2, ← hrad]; field_simp
  rw [h1, Real.sqrt_div hpos.le, Real.sqrt_sq hep.le, Real.sqrt_mul hspos.le]
  unfold hrA1
  field_simp

/-- **The LG amplitude**: `w² = (A sin θ)⁻¹ = (2/√s)/α`. -/
lemma rk_w_sq {P Q τ x qs q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hτ : τ ^ 2 = 1) (hs : 1 - x ^ 2 = rkS P Q x * qs ^ 2)
    (hq : 0 ≤ q) (hqq : q < qs) (hint : 0 < (1 - P * q ^ 2) * (1 - Q * q ^ 2)) (hspos : 0 < rkS P Q x) :
    dlgsW (hrA1 P Q) (hrU P Q τ x) q ^ 2 = 2 / Real.sqrt (rkS P Q x) / Real.sqrt (qs ^ 2 - q ^ 2) := by
  have hA := rk_A_sin (τ := τ) hP hQ hτ hs hq hqq hint hspos
  have hpos : 0 < Real.sqrt (rkS P Q x) * Real.sqrt (qs ^ 2 - q ^ 2) :=
    mul_pos (Real.sqrt_pos.2 hspos) (Real.sqrt_pos.2 (by nlinarith))
  unfold dlgsW
  rw [inv_pow, Real.sq_sqrt (by rw [hA]; positivity), hA]
  field_simp

/-- In terms of the Ermakov profile `kpP = 2/α`: `w²(q_k) = kpP/√s`. -/
lemma rk_w_sq_kpP {P Q τ x qs h : ℝ} {k : ℤ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hτ : τ ^ 2 = 1)
    (hs : 1 - x ^ 2 = rkS P Q x * qs ^ 2) (hq : 0 ≤ kpU h k) (hqq : kpU h k < qs)
    (hint : 0 < (1 - P * kpU h k ^ 2) * (1 - Q * kpU h k ^ 2)) (hspos : 0 < rkS P Q x) :
    dlgsW (hrA1 P Q) (hrU P Q τ x) (kpU h k) ^ 2 = kpP qs h k / Real.sqrt (rkS P Q x) := by
  rw [rk_w_sq hP hQ hτ hs hq hqq hint hspos]
  unfold kpP kpα
  ring

/-- Racah geometry: `P = 1/(4α²)`, `Q = 1/(4β²)`, `γ² = α² + β² - 2αβx`: `s = γ²/(4α²β²)` and `1/√s = 2αβ/γ`. -/
lemma rk_racah_s {α β x γ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hg : γ ^ 2 = α ^ 2 + β ^ 2 - 2 * α * β * x) :
    rkS (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) x = γ ^ 2 / (4 * α ^ 2 * β ^ 2) ∧
      1 / Real.sqrt (rkS (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) x) = 2 * α * β / γ := by
  have hPQ : Real.sqrt (1 / (4 * α ^ 2) * (1 / (4 * β ^ 2))) = 1 / (4 * α * β) := by
    have : 1 / (4 * α ^ 2) * (1 / (4 * β ^ 2)) = (1 / (4 * α * β)) ^ 2 := by field_simp
    rw [this, Real.sqrt_sq (by positivity)]
  have hs : rkS (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) x = γ ^ 2 / (4 * α ^ 2 * β ^ 2) := by
    unfold rkS; rw [hPQ, hg]; field_simp; ring
  refine ⟨hs, ?_⟩
  rw [hs]
  have : γ ^ 2 / (4 * α ^ 2 * β ^ 2) = (γ / (2 * α * β)) ^ 2 := by field_simp; ring
  rw [this, Real.sqrt_sq (by positivity)]
  field_simp

/-- info: 'FormalResearch.Special.rk_turn_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.rk_turn_id

/-- info: 'FormalResearch.Special.rk_A_sin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.rk_A_sin

/-- info: 'FormalResearch.Special.rk_w_sq_kpP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.rk_w_sq_kpP

/-- info: 'FormalResearch.Special.rk_racah_s' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.rk_racah_s

end FormalResearch.Special
