module

public import Mathlib

/-!
# Sharp `κ`: the real algebra of the mass assembly (plan K1, sharp constant, step 7)

Quantities at a node: `t = κ²δ/2` (the target is `t → 1`), `N = δ^{-3}`, the band mass `B`, `sv = Σ P/2`, the Ermakov amplitudes `I₀ = I_{k₀}`,
`I_a = I_{k_b}`, the left mass `L ≤ L_c I₀`, the zone mass `Z ≤ 2 t N ζ`.  Inputs: `B ≤ N` and `N ≤ L + B + Z`;
`|B - I₀ sv| ≤ I₀ (18 S sv + ω₁)`; `(π/2)N(1 - a) ≤ sv ≤ (π/2)N`; transport `I₀ ≤ (1 + 4S) I_a`, `I_a ≤ (1 + 2S) I₀`;
the match `(1 - E)² (2t/π) ≤ I_a ≤ (1 + E)² (2t/π)`.

* `ksa_up`: `t (1 - (2E + a + 20 S + ω₁/N)) ≤ 1`;
* `ksa_low`: `1 ≤ t (1 + θ)` with `θ = 40 S + 12 E + 4 (ω₁ + L_c)/N + 2ζ` (small `S, E`);
* `ksa_final`: both give `|t - 1| ≤ 2 max(θ_up, θ_low)`.

**Claim class: proved** (real algebra).
-/

@[expose] public section

namespace FormalResearch.Special

/-- `pqr ≥ 1 - (1-p) - (1-q) - (1-r)` and `pqr ≤ 1` for `p, q, r ∈ [0, 1]`. -/
lemma ksa_p3 {p q r : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    p + q + r - 2 ≤ p * q * r ∧ p * q * r ≤ 1 := by
  have h1 : p + q - 1 ≤ p * q := by nlinarith
  have h2 : p * q ≤ 1 := by nlinarith
  have h3 : 0 ≤ p * q := mul_nonneg hp0 hq0
  constructor
  · nlinarith [mul_nonneg h3 (sub_nonneg.2 hr1), mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 hr1)]
  · nlinarith

/-- The expansion used in the upper bound. -/
lemma ksa_U3 {t N S E a ω1 : ℝ} (hN : 0 < N) (ht : 0 ≤ t) (hS0 : 0 ≤ S) (hS : S ≤ 1 / 100) (hE0 : 0 ≤ E) (hE : E ≤ 1 / 4)
    (ha0 : 0 ≤ a) (ha : a ≤ 1 / 4) (hω0 : 0 ≤ ω1) :
    t * N * (1 - 2 * E - a - 20 * S) - t * ω1 ≤
      (1 - E) ^ 2 * (2 * t / Real.pi) / (1 + 2 * S) * (Real.pi / 2 * N * (1 - a) * (1 - 18 * S) - ω1) := by
  have hπ := Real.pi_pos
  have hπ4 := Real.pi_lt_four
  have hπ3 := Real.pi_gt_three
  have hp0 : 0 ≤ (1 - E) ^ 2 := by positivity
  have hp2 : (1 - E) ^ 2 ≤ 1 := by nlinarith
  have hp1 : 1 - 2 * E ≤ (1 - E) ^ 2 := by nlinarith [sq_nonneg E]
  have hP := ksa_p3 hp0 hp2 (by linarith : 0 ≤ 1 - a) (by linarith : 1 - a ≤ 1) (by linarith : 0 ≤ 1 - 18 * S)
    (by linarith : 1 - 18 * S ≤ 1)
  have hexp : (1 - E) ^ 2 * (2 * t / Real.pi) / (1 + 2 * S) * (Real.pi / 2 * N * (1 - a) * (1 - 18 * S) - ω1) =
      t * N * ((1 - E) ^ 2 * (1 - a) * (1 - 18 * S) / (1 + 2 * S)) - (2 * t / Real.pi) * ω1 * ((1 - E) ^ 2 / (1 + 2 * S)) := by
    field_simp
  rw [hexp]
  have h7 : 1 - 2 * E - a - 20 * S ≤ (1 - E) ^ 2 * (1 - a) * (1 - 18 * S) / (1 + 2 * S) := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith [hP.1, hP.2, hp1]
  have h8 : t * N * (1 - 2 * E - a - 20 * S) ≤ t * N * ((1 - E) ^ 2 * (1 - a) * (1 - 18 * S) / (1 + 2 * S)) :=
    mul_le_mul_of_nonneg_left h7 (by positivity)
  have hpS : (1 - E) ^ 2 / (1 + 2 * S) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hpS0 : 0 ≤ (1 - E) ^ 2 / (1 + 2 * S) := by positivity
  have h6 : (2 * t / Real.pi) * ω1 * ((1 - E) ^ 2 / (1 + 2 * S)) ≤ t * ω1 := by
    have : 2 * t / Real.pi ≤ t := by
      rw [div_le_iff₀ hπ]; nlinarith
    calc (2 * t / Real.pi) * ω1 * ((1 - E) ^ 2 / (1 + 2 * S)) ≤ t * ω1 * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_right this hω0) hpS hpS0 (by positivity)
      _ = t * ω1 := by ring
  linarith

/-- **The upper bound for `t`** (from `B ≤ N`). -/
lemma ksa_up {t N B sv I0 Ia S E a ω1 : ℝ} (hN : 0 < N) (ht : 0 ≤ t) (hS0 : 0 ≤ S) (hS : S ≤ 1 / 100) (hE0 : 0 ≤ E) (hE : E ≤ 1 / 4)
    (ha0 : 0 ≤ a) (ha : a ≤ 1 / 4) (hω0 : 0 ≤ ω1) (hω : ω1 ≤ N / 4) (hB : B ≤ N)
    (hmass : |B - I0 * sv| ≤ I0 * (18 * S * sv + ω1)) (hsv : Real.pi / 2 * N * (1 - a) ≤ sv) (hI0 : 0 ≤ I0)
    (hIa : Ia ≤ (1 + 2 * S) * I0) (hlow : (1 - E) ^ 2 * (2 * t / Real.pi) ≤ Ia) :
    t * (1 - (2 * E + a + 20 * S + ω1 / N)) ≤ 1 := by
  have hπ := Real.pi_pos
  have hπ3 := Real.pi_gt_three
  have h1 : I0 * (sv * (1 - 18 * S) - ω1) ≤ N := by
    have := (abs_le.1 hmass).1
    nlinarith
  have hX : 0 ≤ Real.pi / 2 * N * (1 - a) * (1 - 18 * S) - ω1 := by
    have h3 : 3 / 2 * N ≤ Real.pi / 2 * N := by nlinarith
    have hb : 0 ≤ Real.pi / 2 * N := by positivity
    have h4 : 3 / 2 * N * (3 / 4) ≤ Real.pi / 2 * N * (1 - a) :=
      mul_le_mul h3 (by linarith) (by norm_num) hb
    have h5 : 3 / 2 * N * (3 / 4) * (1 / 2) ≤ Real.pi / 2 * N * (1 - a) * (1 - 18 * S) :=
      mul_le_mul h4 (by linarith) (by norm_num) (le_trans (by positivity) h4)
    nlinarith
  have hsv' : Real.pi / 2 * N * (1 - a) * (1 - 18 * S) ≤ sv * (1 - 18 * S) :=
    mul_le_mul_of_nonneg_right hsv (by linarith)
  have hI0' : (1 - E) ^ 2 * (2 * t / Real.pi) / (1 + 2 * S) ≤ I0 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hJ0 : 0 ≤ (1 - E) ^ 2 * (2 * t / Real.pi) / (1 + 2 * S) := by
    have : 0 ≤ 1 - E := by linarith
    positivity
  have h3 : (1 - E) ^ 2 * (2 * t / Real.pi) / (1 + 2 * S) * (Real.pi / 2 * N * (1 - a) * (1 - 18 * S) - ω1) ≤ N := by
    refine le_trans (mul_le_mul_of_nonneg_right hI0' hX) ?_
    refine le_trans ?_ h1
    exact mul_le_mul_of_nonneg_left (by linarith) hI0
  have h4 := ksa_U3 hN ht hS0 hS hE0 hE ha0 ha hω0
  have h10 : t * (1 - (2 * E + a + 20 * S + ω1 / N)) * N ≤ N := by
    have e : t * (1 - (2 * E + a + 20 * S + ω1 / N)) * N = t * N * (1 - 2 * E - a - 20 * S) - t * ω1 := by
      field_simp; ring
    linarith
  exact le_of_mul_le_mul_right (by linarith) hN

/-- Elementary: `(1+4S)(1+E)²(1+18S) ≤ 1 + 24 S + 3 E` for `0 ≤ S ≤ 1/100`, `0 ≤ E ≤ 1/4`. -/
lemma ksa_c3 {S E : ℝ} (hS0 : 0 ≤ S) (hS : S ≤ 1 / 100) (hE0 : 0 ≤ E) (hE : E ≤ 1 / 4) :
    (1 + 4 * S) * (1 + E) ^ 2 * (1 + 18 * S) ≤ 1 + 24 * S + 3 * E := by
  have h1 : (1 + E) ^ 2 ≤ 1 + 9 / 4 * E := by nlinarith
  have h2 : (1 + 4 * S) * (1 + 18 * S) ≤ 1 + 23 * S := by nlinarith
  have h3 : 0 ≤ (1 + 4 * S) * (1 + 18 * S) := by positivity
  have h4 : (1 + 4 * S) * (1 + E) ^ 2 * (1 + 18 * S) ≤ (1 + 23 * S) * (1 + 9 / 4 * E) := by
    calc (1 + 4 * S) * (1 + E) ^ 2 * (1 + 18 * S) = ((1 + 4 * S) * (1 + 18 * S)) * (1 + E) ^ 2 := by ring
      _ ≤ (1 + 23 * S) * (1 + 9 / 4 * E) :=
        mul_le_mul h2 h1 (by positivity) (by positivity)
  nlinarith

/-- **The lower bound for `t`** (from `N ≤ L + B + Z`). -/
lemma ksa_low {t N B L Z sv I0 Ia S E ω1 Lc ζ : ℝ} (hN : 0 < N) (ht : 0 ≤ t) (hS0 : 0 ≤ S) (hS : S ≤ 1 / 100)
    (hE0 : 0 ≤ E) (hE : E ≤ 1 / 4) (hω0 : 0 ≤ ω1) (hLc : 0 ≤ Lc)
    (hsum : N ≤ L + B + Z) (hL : L ≤ Lc * I0) (hZ : Z ≤ 2 * t * N * ζ)
    (hmass : |B - I0 * sv| ≤ I0 * (18 * S * sv + ω1)) (hsv : sv ≤ Real.pi / 2 * N) (hI0 : 0 ≤ I0)
    (hI0a : I0 ≤ (1 + 4 * S) * Ia) (hup : Ia ≤ (1 + E) ^ 2 * (2 * t / Real.pi)) :
    1 ≤ t * (1 + (24 * S + 3 * E + 2 * ζ + 2 * (Lc + ω1) / N)) := by
  have hπ := Real.pi_pos
  have hπ3 := Real.pi_gt_three
  have hπ4 := Real.pi_lt_four
  have hB : B ≤ I0 * (sv * (1 + 18 * S) + ω1) := by
    have := (abs_le.1 hmass).2
    nlinarith
  have hsv1 : sv * (1 + 18 * S) ≤ Real.pi / 2 * N * (1 + 18 * S) :=
    mul_le_mul_of_nonneg_right hsv (by linarith)
  have hB2 : B ≤ I0 * (Real.pi / 2 * N * (1 + 18 * S) + ω1) :=
    le_trans hB (mul_le_mul_of_nonneg_left (by linarith) hI0)
  have hK : N ≤ I0 * (Lc + ω1 + Real.pi / 2 * N * (1 + 18 * S)) + 2 * t * N * ζ := by nlinarith
  have hI1 : I0 ≤ (1 + 4 * S) * (1 + E) ^ 2 * (2 * t / Real.pi) := by
    calc I0 ≤ (1 + 4 * S) * Ia := hI0a
      _ ≤ (1 + 4 * S) * ((1 + E) ^ 2 * (2 * t / Real.pi)) := mul_le_mul_of_nonneg_left hup (by linarith)
      _ = _ := by ring
  have hQ : 0 ≤ Lc + ω1 + Real.pi / 2 * N * (1 + 18 * S) := by positivity
  have hK2 : N ≤ (1 + 4 * S) * (1 + E) ^ 2 * (2 * t / Real.pi) * (Lc + ω1 + Real.pi / 2 * N * (1 + 18 * S)) +
      2 * t * N * ζ := le_trans hK (by nlinarith [mul_le_mul_of_nonneg_right hI1 hQ])
  have hc := ksa_c3 hS0 hS hE0 hE
  have hD : (1 + 4 * S) * (1 + E) ^ 2 ≤ 2 := by nlinarith
  have hD0 : 0 ≤ (1 + 4 * S) * (1 + E) ^ 2 := by positivity
  have hexp : (1 + 4 * S) * (1 + E) ^ 2 * (2 * t / Real.pi) * (Lc + ω1 + Real.pi / 2 * N * (1 + 18 * S)) =
      t * N * ((1 + 4 * S) * (1 + E) ^ 2 * (1 + 18 * S)) + t * ((1 + 4 * S) * (1 + E) ^ 2) * (2 / Real.pi) * (Lc + ω1) := by
    field_simp
    ring
  have h9 : t * ((1 + 4 * S) * (1 + E) ^ 2) * (2 / Real.pi) * (Lc + ω1) ≤ t * (2 * (Lc + ω1)) := by
    have h2p : 2 / Real.pi ≤ 1 := by rw [div_le_one hπ]; linarith
    have h2p0 : 0 ≤ 2 / Real.pi := by positivity
    have hLw : 0 ≤ Lc + ω1 := by linarith
    have : ((1 + 4 * S) * (1 + E) ^ 2) * (2 / Real.pi) ≤ 2 * 1 := mul_le_mul hD h2p h2p0 (by norm_num)
    calc t * ((1 + 4 * S) * (1 + E) ^ 2) * (2 / Real.pi) * (Lc + ω1)
        = t * ((((1 + 4 * S) * (1 + E) ^ 2) * (2 / Real.pi)) * (Lc + ω1)) := by ring
      _ ≤ t * ((2 * 1) * (Lc + ω1)) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right this hLw) ht
      _ = t * (2 * (Lc + ω1)) := by ring
  have h10 : t * N * ((1 + 4 * S) * (1 + E) ^ 2 * (1 + 18 * S)) ≤ t * N * (1 + 24 * S + 3 * E) :=
    mul_le_mul_of_nonneg_left hc (by positivity)
  have h11 : N ≤ t * N * (1 + 24 * S + 3 * E + 2 * ζ) + t * (2 * (Lc + ω1)) := by
    rw [hexp] at hK2
    have e2 : 2 * t * N * ζ = t * N * (2 * ζ) := by ring
    have e3 : t * N * (1 + 24 * S + 3 * E + 2 * ζ) = t * N * (1 + 24 * S + 3 * E) + t * N * (2 * ζ) := by ring
    linarith only [hK2, h9, h10, e2, e3]
  have e : t * (1 + (24 * S + 3 * E + 2 * ζ + 2 * (Lc + ω1) / N)) * N =
      t * N * (1 + 24 * S + 3 * E + 2 * ζ) + t * (2 * (Lc + ω1)) := by
    field_simp
    ring
  have : 1 * N ≤ t * (1 + (24 * S + 3 * E + 2 * ζ + 2 * (Lc + ω1) / N)) * N := by linarith only [e, h11]
  exact le_of_mul_le_mul_right this hN

/-- **Sharp constant, real part.**  If `t(1 - θ₁) ≤ 1 ≤ t(1 + θ₂)` with `0 ≤ θ₁ < 1`, `0 ≤ θ₂`, then
`|t - 1| ≤ max(θ₁, θ₂)/(1 - max(θ₁,θ₂))`; here the form `|t - 1| ≤ 2 max(θ₁, θ₂)` for `θ₁, θ₂ ≤ 1/2`. -/
lemma ksa_final {t θ1 θ2 : ℝ} (h1 : t * (1 - θ1) ≤ 1) (h2 : 1 ≤ t * (1 + θ2)) (hθ1 : 0 ≤ θ1) (hθ2 : 0 ≤ θ2)
    (hθ1' : θ1 ≤ 1 / 2) (hθ2' : θ2 ≤ 1 / 2) : |t - 1| ≤ 2 * max θ1 θ2 := by
  have hm1 : θ1 ≤ max θ1 θ2 := le_max_left _ _
  have hm2 : θ2 ≤ max θ1 θ2 := le_max_right _ _
  have hm : max θ1 θ2 ≤ 1 / 2 := max_le hθ1' hθ2'
  have ht0 : 0 ≤ t := by
    by_contra h
    replace h := not_le.1 h
    nlinarith
  rw [abs_le]
  constructor
  · by_contra h
    replace h := not_le.1 h
    nlinarith [mul_nonneg ht0 (sub_nonneg.2 hm2)]
  · by_contra h
    replace h := not_le.1 h
    nlinarith [mul_nonneg ht0 (sub_nonneg.2 hm1)]

/-- info: 'FormalResearch.Special.ksa_up' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.ksa_up

/-- info: 'FormalResearch.Special.ksa_low' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.ksa_low

/-- info: 'FormalResearch.Special.ksa_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.ksa_final

end FormalResearch.Special
