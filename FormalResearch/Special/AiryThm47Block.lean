module

public import FormalResearch.Special.AiryThm47Sizes
public import FormalResearch.Special.AiryThm47Neg

/-!
# Pointwise block bound for `N²` on the negative axis (input to Theorem 4.7)

For real polynomials `P`, `Q ≠ 0` and `N = P Ai + Q Ai'`, put `A = Ai`, `B = Ai'`, `K = B² - xA²` (so `K' = -A²`)
and `x = -s < 0`.  Then, for `x ≠ 0`,
`N² = α K + β (AB)' + γ (A²)'`, with `α = (Q² - P²/x)/2`, `β = (Q² + P²/x)/2`, `γ = PQ`,
because `B² = (K + (AB)')/2` and `x A² = ((AB)' - K)/2`.  With `W := β·AB + γ·A²` one gets
`N² - W' = α K - ε`, `ε = β' AB + γ' A²`.  This file proves (**all proved**):

* `at47_eps_bound`: `s |ε(-s)| ≤ 66 C s^e` (arithmetic from `at47_sizes`, `at47_neg_bounds`),
* `at47_pointwise`: `N(-s)² - W'(-s) ≥ c0 s^e √s` for `s ≥ S`  (using `K(-s) ≥ √s/(2π)`),
* `at47_W_bound`: `|W(-s)| ≤ C' s^e`.
-/

@[expose] public section

open Polynomial
open scoped Real

namespace FormalResearch.Special


lemma at47_amgm (x y : ℝ) : |x * y| ≤ (x ^ 2 + y ^ 2) / 2 := by
  rw [abs_mul]; nlinarith [sq_nonneg (|x| - |y|), sq_abs x, sq_abs y]

lemma at47_eps_core {X1 X2 X3 X4 AB rA2 D : ℝ} (h1 : X1 ^ 2 ≤ D) (h2 : X2 ^ 2 ≤ D) (h3 : X3 ^ 2 ≤ D)
    (h4 : X4 ^ 2 ≤ D) (hAB : |AB| ≤ 19) (hA0 : 0 ≤ rA2) (hA : rA2 ≤ 9) :
    |(X1 * X2 - X3 * X4 - X3 ^ 2 / 2) * AB + rA2 * (X1 * X4 + X2 * X3)| ≤ 66 * D := by
  have e12 := at47_amgm X1 X2
  have e34 := at47_amgm X3 X4
  have e14 := at47_amgm X1 X4
  have e23 := at47_amgm X2 X3
  have hD : 0 ≤ D := (sq_nonneg _).trans h1
  have a1 : |X1 * X2 - X3 * X4 - X3 ^ 2 / 2| ≤ 5 / 2 * D := by
    have := abs_sub (X1 * X2 - X3 * X4) (X3 ^ 2 / 2)
    have := abs_sub (X1 * X2) (X3 * X4)
    rw [abs_of_nonneg (by positivity : 0 ≤ X3 ^ 2 / 2)] at *
    linarith
  have a2 : |rA2 * (X1 * X4 + X2 * X3)| ≤ 18 * D := by
    rw [abs_mul, abs_of_nonneg hA0]
    have := abs_add_le (X1 * X4) (X2 * X3)
    have h5 : |X1 * X4 + X2 * X3| ≤ 2 * D := by
      have := at47_amgm X1 X4; have := at47_amgm X2 X3; linarith
    calc rA2 * |X1 * X4 + X2 * X3| ≤ 9 * (2 * D) := by gcongr
      _ = 18 * D := by ring
  calc _ ≤ |(X1 * X2 - X3 * X4 - X3 ^ 2 / 2) * AB| + |rA2 * (X1 * X4 + X2 * X3)| := abs_add_le _ _
    _ ≤ (5 / 2 * D) * 19 + 18 * D := by
        rw [abs_mul]; gcongr
    _ ≤ 66 * D := by linarith

lemma at47_eps_bound {r p q p1 q1 A B C E : ℝ} (hr : 0 < r)
    (hq : q ^ 2 ≤ C * E) (hp : p ^ 2 ≤ C * r ^ 2 * E) (hq1 : (r ^ 2 * q1) ^ 2 ≤ C * E)
    (hp1 : (r ^ 2 * p1) ^ 2 ≤ C * r ^ 2 * E) (hA : r * A ^ 2 ≤ 9) (hB : B ^ 2 ≤ 38 * r) :
    r ^ 2 * |(q * q1 - p * p1 / r ^ 2 - p ^ 2 / (2 * r ^ 4)) * (A * B) + (p1 * q + p * q1) * A ^ 2| ≤
      66 * (C * E) := by
  have hr2 : 0 < r ^ 2 := by positivity
  have hAB : |A * B| ≤ 19 := by
    have h1 : r * (A ^ 2 * B ^ 2) ≤ 342 * r := by
      calc r * (A ^ 2 * B ^ 2) = (r * A ^ 2) * B ^ 2 := by ring
        _ ≤ 9 * B ^ 2 := by gcongr
        _ ≤ 9 * (38 * r) := by gcongr
        _ = 342 * r := by ring
    have h2 : A ^ 2 * B ^ 2 ≤ 342 := le_of_mul_le_mul_left (by linarith) hr
    have : (A * B) ^ 2 ≤ 19 ^ 2 := by rw [mul_pow]; linarith
    exact abs_le_of_sq_le_sq' this (by norm_num) |> fun h => abs_le.mpr h
  have hX3 : (p / r) ^ 2 ≤ C * E := by
    rw [div_pow, div_le_iff₀ hr2]; linarith
  have hX4 : (r * p1) ^ 2 ≤ C * E := by
    have : (r * p1) ^ 2 * r ^ 2 = (r ^ 2 * p1) ^ 2 := by ring
    have h : (r * p1) ^ 2 * r ^ 2 ≤ (C * E) * r ^ 2 := by nlinarith
    exact le_of_mul_le_mul_right h hr2
  have hA0 : 0 ≤ r * A ^ 2 := by positivity
  have core := at47_eps_core hq hq1 hX3 hX4 hAB hA0 hA
  have e : r ^ 2 * ((q * q1 - p * p1 / r ^ 2 - p ^ 2 / (2 * r ^ 4)) * (A * B) + (p1 * q + p * q1) * A ^ 2) =
      (q * (r ^ 2 * q1) - (p / r) * (r * p1) - (p / r) ^ 2 / 2) * (A * B) +
        (r * A ^ 2) * (q * (r * p1) + (r ^ 2 * q1) * (p / r)) := by
    field_simp
  rw [← abs_of_pos hr2, ← abs_mul, abs_of_pos hr2, e]
  exact core

/-! ### The functions `β`, `W` and the derivative of `W` -/

/-- `β = (Q² + P²/x)/2`. -/
noncomputable def at47_beta (P Q : ℝ[X]) (x : ℝ) : ℝ := (Q.eval x ^ 2 + P.eval x ^ 2 / x) / 2

/-- `W = β·(Ai Ai') + P Q Ai²`. -/
noncomputable def at47_W (P Q : ℝ[X]) (x : ℝ) : ℝ :=
  at47_beta P Q x * (airyAi x * airyAi' x) + P.eval x * Q.eval x * airyAi x ^ 2

/-- The derivative of `W` (for `x ≠ 0`). -/
noncomputable def at47_Wd (P Q : ℝ[X]) (x : ℝ) : ℝ :=
  (Q.eval x * (derivative Q).eval x + P.eval x * (derivative P).eval x / x - P.eval x ^ 2 / (2 * x ^ 2)) *
      (airyAi x * airyAi' x) +
    at47_beta P Q x * (airyAi' x ^ 2 + x * airyAi x ^ 2) +
    ((derivative P).eval x * Q.eval x + P.eval x * (derivative Q).eval x) * airyAi x ^ 2 +
    P.eval x * Q.eval x * (2 * airyAi x * airyAi' x)

lemma hasDerivAt_at47_W (P Q : ℝ[X]) {x : ℝ} (hx : x ≠ 0) : HasDerivAt (at47_W P Q) (at47_Wd P Q x) x := by
  have hP := Polynomial.hasDerivAt P x
  have hQ := Polynomial.hasDerivAt Q x
  have hA := hasDerivAt_airyAi x
  have hB := hasDerivAt_airyAi' x
  have hid : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have hb : HasDerivAt (at47_beta P Q)
      ((2 * Q.eval x * (derivative Q).eval x + (2 * P.eval x * (derivative P).eval x * x - P.eval x ^ 2) / x ^ 2) / 2) x := by
    have h1 := (hQ.pow 2).add ((hP.pow 2).div hid hx)
    have h2 := h1.div_const 2
    convert h2 using 1
    · funext y; simp [at47_beta]
    · simp
  have hAB := hA.mul hB
  have hW := (hb.mul hAB).add (((hP.mul hQ).mul (hA.pow 2)))
  convert hW using 1
  · funext y; simp [at47_W]
  · unfold at47_Wd
    simp only [Nat.cast_ofNat, Pi.mul_apply, Pi.pow_apply]
    field_simp
    ring

lemma at47_N_sq_sub_Wd (P Q : ℝ[X]) {x : ℝ} (hx : x ≠ 0) :
    (P.eval x * airyAi x + Q.eval x * airyAi' x) ^ 2 - at47_Wd P Q x =
      (Q.eval x ^ 2 - P.eval x ^ 2 / x) / 2 * (airyAi' x ^ 2 - x * airyAi x ^ 2) -
        ((Q.eval x * (derivative Q).eval x + P.eval x * (derivative P).eval x / x - P.eval x ^ 2 / (2 * x ^ 2)) *
          (airyAi x * airyAi' x) + ((derivative P).eval x * Q.eval x + P.eval x * (derivative Q).eval x) * airyAi x ^ 2) := by
  unfold at47_Wd at47_beta
  field_simp
  ring

/-- **Pointwise bound** in the variable `r = √s`: `N(-r²)² - W'(-r²) ≥ c0 (r²)^e r` for `r ≥ R0`. -/
theorem at47_pointwise (P Q : ℝ[X]) (hQ : Q ≠ 0) :
    ∃ c0 R0 : ℝ, 0 < c0 ∧ 1 ≤ R0 ∧ ∀ r : ℝ, R0 ≤ r →
      c0 * (r ^ 2) ^ (at47_e P Q) * r ≤
        (P.eval (-r ^ 2) * airyAi (-r ^ 2) + Q.eval (-r ^ 2) * airyAi' (-r ^ 2)) ^ 2 - at47_Wd P Q (-r ^ 2) := by
  obtain ⟨C, c, S, hC, hc, hS, hsz⟩ := at47_sizes P Q hQ
  have hpi := Real.pi_pos
  refine ⟨c / (8 * π), max 2 (max (√S) (√(528 * π * C / c + 1))), by positivity,
    le_trans (by norm_num) (le_max_left _ _), fun r hr => ?_⟩
  have hr2 : 2 ≤ r := (le_max_left _ _).trans hr
  have hrS : √S ≤ r := ((le_max_left _ _).trans (le_max_right _ _)).trans hr
  have hrT : √(528 * π * C / c + 1) ≤ r := ((le_max_right _ _).trans (le_max_right _ _)).trans hr
  have hr0 : 0 < r := by linarith
  have hrr : 0 < r ^ 2 := by positivity
  have hSs : S ≤ r ^ 2 := by
    have := Real.sqrt_le_left (by linarith : (0:ℝ) ≤ r) |>.mp hrS
    exact this
  have hTs : 528 * π * C / c + 1 ≤ r ^ 2 := by
    have := Real.sqrt_le_left (by linarith : (0:ℝ) ≤ r) |>.mp hrT
    exact this
  obtain ⟨hq, hp, hq1, hp1, hv⟩ := hsz (r ^ 2) hSs
  have hsq : √(r ^ 2) = r := Real.sqrt_sq hr0.le
  have hs1 : 1 ≤ r ^ 2 := by nlinarith
  obtain ⟨hA, hB⟩ := at47_neg_bounds hs1
  rw [hsq] at hA hB
  have hK := at47_ker_neg_lower (s := r ^ 2) (by nlinarith)
  rw [hsq, airyKer_self] at hK
  set E : ℝ := (r ^ 2) ^ (at47_e P Q) with hE
  have hE0 : 0 < E := by positivity
  have hp' : P.eval (-r ^ 2) ^ 2 ≤ C * r ^ 2 * E := by
    have h := pow_succ (r ^ 2) (at47_e P Q)
    rw [h] at hp; linarith
  have hp1' : (r ^ 2 * (derivative P).eval (-r ^ 2)) ^ 2 ≤ C * r ^ 2 * E := by
    have h := pow_succ (r ^ 2) (at47_e P Q)
    rw [h] at hp1; linarith
  have heps := at47_eps_bound (p := P.eval (-r ^ 2)) (q := Q.eval (-r ^ 2)) (p1 := (derivative P).eval (-r ^ 2))
    (q1 := (derivative Q).eval (-r ^ 2)) (A := airyAi (-r ^ 2)) (B := airyAi' (-r ^ 2)) (C := C) (E := E)
    hr0 hq hp' hq1 hp1' hA hB
  have hx : (-r ^ 2 : ℝ) ≠ 0 := by simp [hr0.ne']
  rw [at47_N_sq_sub_Wd P Q hx]
  -- notation
  set q := Q.eval (-r ^ 2)
  set p := P.eval (-r ^ 2)
  set A := airyAi (-r ^ 2)
  set B := airyAi' (-r ^ 2)
  have eα : (q ^ 2 - p ^ 2 / (-r ^ 2)) / 2 = (q ^ 2 + p ^ 2 / r ^ 2) / 2 := by ring
  have hαge : c / 2 * E ≤ (q ^ 2 - p ^ 2 / (-r ^ 2)) / 2 := by rw [eα]; linarith
  have hKK : B ^ 2 - -r ^ 2 * A ^ 2 = B ^ 2 + r ^ 2 * A ^ 2 := by ring
  set ε : ℝ := (q * (derivative Q).eval (-r ^ 2) + p * (derivative P).eval (-r ^ 2) / (-r ^ 2) -
      p ^ 2 / (2 * (-r ^ 2) ^ 2)) * (A * B) +
        ((derivative P).eval (-r ^ 2) * q + p * (derivative Q).eval (-r ^ 2)) * A ^ 2 with hεdef
  have hε : ε = (q * (derivative Q).eval (-r ^ 2) - p * (derivative P).eval (-r ^ 2) / r ^ 2 -
      p ^ 2 / (2 * r ^ 4)) * (A * B) + ((derivative P).eval (-r ^ 2) * q + p * (derivative Q).eval (-r ^ 2)) * A ^ 2 := by
    rw [hεdef]; congr 2 <;> field_simp <;> ring
  rw [← hε] at heps
  have hεb : |ε| ≤ 66 * (C * E) / r ^ 2 := by
    rw [le_div_iff₀ hrr]; linarith
  have hKpos : 0 ≤ r / (2 * π) := by positivity
  have hαK : c / 2 * E * (r / (2 * π)) ≤ (q ^ 2 - p ^ 2 / (-r ^ 2)) / 2 * (B ^ 2 - -r ^ 2 * A ^ 2) := by
    exact mul_le_mul hαge hK hKpos ((by positivity : 0 ≤ c / 2 * E).trans hαge)
  have hbig : 66 * (C * E) / r ^ 2 ≤ c / (8 * π) * E * r := by
    have h1 : 528 * π * C / c ≤ r ^ 2 := by linarith
    have h2 : 528 * π * C ≤ c * r ^ 2 := by
      rw [div_le_iff₀ hc] at h1; linarith
    rw [div_le_iff₀ hrr]
    have : 66 * (C * E) = (528 * π * C) * E / (8 * π) := by field_simp; ring
    rw [this]
    have h3 : (528 * π * C) * E ≤ (c * r ^ 2) * E := by gcongr
    have h4 : c / (8 * π) * E * r * r ^ 2 = (c * r ^ 2 * E) * r / (8 * π) := by field_simp
    have h5 : (c * r ^ 2) * E / (8 * π) ≤ (c * r ^ 2 * E) * r / (8 * π) := by
      have h6 : c * r ^ 2 * E ≤ c * r ^ 2 * E * r :=
        le_mul_of_one_le_right (mul_pos (mul_pos hc hrr) hE0).le (by linarith)
      gcongr
    rw [h4]
    calc (528 * π * C) * E / (8 * π) ≤ (c * r ^ 2) * E / (8 * π) := by gcongr
      _ ≤ _ := h5
  have hfin : c / (8 * π) * E * r ≤ (q ^ 2 - p ^ 2 / (-r ^ 2)) / 2 * (B ^ 2 - -r ^ 2 * A ^ 2) - ε := by
    have : c / 2 * E * (r / (2 * π)) = 2 * (c / (8 * π) * E * r) := by field_simp; ring
    have := le_abs_self ε
    linarith
  linarith

/-- **Boundary term**: `|W(-r²)| ≤ C' (r²)^e` for `r ≥ R0`. -/
theorem at47_W_bound (P Q : ℝ[X]) (hQ : Q ≠ 0) :
    ∃ C' R0 : ℝ, 0 < C' ∧ 1 ≤ R0 ∧ ∀ r : ℝ, R0 ≤ r → |at47_W P Q (-r ^ 2)| ≤ C' * (r ^ 2) ^ (at47_e P Q) := by
  obtain ⟨C, c, S, hC, hc, hS, hsz⟩ := at47_sizes P Q hQ
  refine ⟨28 * C, max 1 (√S), by positivity, le_max_left _ _, fun r hr => ?_⟩
  have hr1 : 1 ≤ r := (le_max_left _ _).trans hr
  have hrS : √S ≤ r := (le_max_right _ _).trans hr
  have hr0 : 0 < r := by linarith
  have hrr : 0 < r ^ 2 := by positivity
  have hSs : S ≤ r ^ 2 := (Real.sqrt_le_left hr0.le).mp hrS
  obtain ⟨hq, hp, -, -, -⟩ := hsz (r ^ 2) hSs
  have hsq : √(r ^ 2) = r := Real.sqrt_sq hr0.le
  have hs1 : 1 ≤ r ^ 2 := by nlinarith
  obtain ⟨hA, hB⟩ := at47_neg_bounds hs1
  rw [hsq] at hA hB
  set E : ℝ := (r ^ 2) ^ (at47_e P Q) with hE
  have hE0 : 0 < E := by positivity
  have hp' : P.eval (-r ^ 2) ^ 2 ≤ C * r ^ 2 * E := by
    have h := pow_succ (r ^ 2) (at47_e P Q)
    rw [h] at hp; linarith
  set q := Q.eval (-r ^ 2)
  set p := P.eval (-r ^ 2)
  set A := airyAi (-r ^ 2)
  set B := airyAi' (-r ^ 2)
  have hAB : |A * B| ≤ 19 := by
    have h1 : r * (A ^ 2 * B ^ 2) ≤ 342 * r := by
      calc r * (A ^ 2 * B ^ 2) = (r * A ^ 2) * B ^ 2 := by ring
        _ ≤ 9 * B ^ 2 := by gcongr
        _ ≤ 9 * (38 * r) := by gcongr
        _ = 342 * r := by ring
    have h2 : A ^ 2 * B ^ 2 ≤ 342 := le_of_mul_le_mul_left (by linarith) hr0
    have : (A * B) ^ 2 ≤ 19 ^ 2 := by rw [mul_pow]; linarith
    exact abs_le.mpr (abs_le_of_sq_le_sq' this (by norm_num))
  have hpr : (p / r) ^ 2 ≤ C * E := by
    rw [div_pow, div_le_iff₀ hrr]; linarith
  have hβ : |at47_beta P Q (-r ^ 2)| ≤ C * E := by
    have : at47_beta P Q (-r ^ 2) = (q ^ 2 - (p / r) ^ 2) / 2 := by
      unfold at47_beta; simp only [q, p]; field_simp; ring
    rw [this, abs_le]
    constructor <;> nlinarith [sq_nonneg q, sq_nonneg (p / r)]
  have hγ : |p * q * A ^ 2| ≤ 9 * (C * E) := by
    have h0 : 0 ≤ r * A ^ 2 := by positivity
    have : |p * q * A ^ 2| = |(p / r) * q| * (r * A ^ 2) := by
      rw [abs_mul, abs_mul, abs_mul, abs_div, abs_of_pos hr0, abs_of_nonneg (sq_nonneg A)]
      field_simp
    rw [this]
    have h1 := at47_amgm (p / r) q
    calc |(p / r) * q| * (r * A ^ 2) ≤ (C * E) * 9 := by
          gcongr; linarith
      _ = _ := by ring
  unfold at47_W
  calc |at47_beta P Q (-r ^ 2) * (A * B) + p * q * A ^ 2|
      ≤ |at47_beta P Q (-r ^ 2) * (A * B)| + |p * q * A ^ 2| := abs_add_le _ _
    _ ≤ (C * E) * 19 + 9 * (C * E) := by
        rw [abs_mul]; gcongr
    _ = _ := by ring

/-- The real function `N = P Ai + Q Ai'`. -/
noncomputable def at47_Nf (P Q : ℝ[X]) (x : ℝ) : ℝ := P.eval x * airyAi x + Q.eval x * airyAi' x

lemma at47_Wd_continuousOn (P Q : ℝ[X]) {a b : ℝ} (hb : b < 0) :
    ContinuousOn (at47_Wd P Q) (Set.Icc a b) := by
  have hne : ∀ x ∈ Set.Icc a b, x ≠ 0 := fun x hx => (lt_of_le_of_lt hx.2 hb).ne
  have h1 := continuous_airyAi
  have h2 := continuous_airyAi'
  unfold at47_Wd at47_beta
  have hP := Polynomial.continuous P (R := ℝ)
  fun_prop (disch := first | exact hne | (intro x hx; have := hne x hx; positivity))

/-- **Block lower bound**: `∫_{-2R}^{-R} N² ≥ c R^{e+1} √R` for `R ≥ R1`. -/
theorem at47_block_integral (P Q : ℝ[X]) (hQ : Q ≠ 0) :
    ∃ c R1 : ℝ, 0 < c ∧ 1 ≤ R1 ∧ ∀ R : ℝ, R1 ≤ R →
      c * (R ^ (at47_e P Q + 1) * √R) ≤ ∫ x in (-(2 * R))..(-R), at47_Nf P Q x ^ 2 := by
  obtain ⟨c0, R0, hc0, hR0, hpt⟩ := at47_pointwise P Q hQ
  obtain ⟨C', R0', hC', hR0', hW⟩ := at47_W_bound P Q hQ
  set e := at47_e P Q
  have hpt' : ∀ s : ℝ, R0 ^ 2 ≤ s → c0 * s ^ e * √s ≤ at47_Nf P Q (-s) ^ 2 - at47_Wd P Q (-s) := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs
    have hr : R0 ≤ √s := Real.le_sqrt_of_sq_le hs
    have h := hpt (√s) hr
    rw [Real.sq_sqrt hs0.le] at h
    exact h
  have hW' : ∀ s : ℝ, R0' ^ 2 ≤ s → |at47_W P Q (-s)| ≤ C' * s ^ e := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs
    have hr : R0' ≤ √s := Real.le_sqrt_of_sq_le hs
    have h := hW (√s) hr
    rw [Real.sq_sqrt hs0.le] at h
    exact h
  set T : ℝ := max (R0 ^ 2) (R0' ^ 2) with hT
  have hT1 : 1 ≤ T := le_trans (by nlinarith) (le_max_left _ _)
  refine ⟨c0 / 2, max T (max 1 (2 * C' * (1 + 2 ^ e) / c0)), by positivity,
    (le_max_left _ _).trans' hT1 |>.trans' le_rfl, fun R hR => ?_⟩
  have hRT : T ≤ R := (le_max_left _ _).trans hR
  have hR1 : 1 ≤ R := hT1.trans hRT
  have hR0 : 0 < R := by linarith
  have hRc : 2 * C' * (1 + 2 ^ e) / c0 ≤ R := ((le_max_right _ _).trans (le_max_right _ _)).trans hR
  have hab : -(2 * R) ≤ -R := by linarith
  have hneg : -R < 0 := by linarith
  -- FTC for W
  have hFTC : ∫ x in (-(2 * R))..(-R), at47_Wd P Q x = at47_W P Q (-R) - at47_W P Q (-(2 * R)) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => ?_) ?_
    · rw [Set.uIcc_of_le hab] at hx
      exact hasDerivAt_at47_W P Q (lt_of_le_of_lt hx.2 hneg).ne
    · exact (at47_Wd_continuousOn P Q hneg).intervalIntegrable_of_Icc hab
  have hcontN : ContinuousOn (fun x => at47_Nf P Q x ^ 2) (Set.Icc (-(2 * R)) (-R)) := by
    unfold at47_Nf
    have := continuous_airyAi; have := continuous_airyAi'
    have hP := Polynomial.continuous P (R := ℝ)
    have hQc := Polynomial.continuous Q (R := ℝ)
    fun_prop
  have hIN : IntervalIntegrable (fun x => at47_Nf P Q x ^ 2) MeasureTheory.volume (-(2 * R)) (-R) :=
    hcontN.intervalIntegrable_of_Icc hab
  have hIW : IntervalIntegrable (at47_Wd P Q) MeasureTheory.volume (-(2 * R)) (-R) :=
    (at47_Wd_continuousOn P Q hneg).intervalIntegrable_of_Icc hab
  have hsplit : ∫ x in (-(2 * R))..(-R), at47_Nf P Q x ^ 2 =
      (∫ x in (-(2 * R))..(-R), (at47_Nf P Q x ^ 2 - at47_Wd P Q x)) + ∫ x in (-(2 * R))..(-R), at47_Wd P Q x := by
    rw [← intervalIntegral.integral_add (hIN.sub hIW) hIW]; simp
  have hmono : ∫ x in (-(2 * R))..(-R), c0 * R ^ e * √R ≤
      ∫ x in (-(2 * R))..(-R), (at47_Nf P Q x ^ 2 - at47_Wd P Q x) := by
    refine intervalIntegral.integral_mono_on hab (by simp) (hIN.sub hIW) (fun x hx => ?_)
    have hs : R ≤ -x := by linarith [hx.2]
    have hTx : R0 ^ 2 ≤ -x := ((le_max_left _ _).trans hRT).trans hs
    have h := hpt' (-x) hTx
    have h1 : c0 * R ^ e * √R ≤ c0 * (-x) ^ e * √(-x) := by
      have := Real.sqrt_le_sqrt hs
      have hc : 0 ≤ c0 * (-x) ^ e := mul_nonneg hc0.le (pow_nonneg (by linarith [hs, hR0]) e)
      have hpw : R ^ e ≤ (-x) ^ e := pow_le_pow_left₀ hR0.le hs e
      calc c0 * R ^ e * √R ≤ c0 * (-x) ^ e * √R := by gcongr
        _ ≤ _ := by gcongr
    rw [neg_neg] at h
    exact h1.trans h
  have hW1 : |at47_W P Q (-R)| ≤ C' * R ^ e := hW' R (((le_max_right _ _).trans hRT).trans' le_rfl)
  have hW2 : |at47_W P Q (-(2 * R))| ≤ C' * (2 * R) ^ e :=
    hW' (2 * R) (by have := (le_max_right _ _).trans hRT; nlinarith [sq_nonneg R0'])
  have hconst : ∫ x in (-(2 * R))..(-R), c0 * R ^ e * √R = R * (c0 * R ^ e * √R) := by
    rw [intervalIntegral.integral_const]; simp only [smul_eq_mul]; ring
  rw [hsplit, hFTC]
  rw [hconst] at hmono
  have hRe : 0 < R ^ e := by positivity
  have hsq : 1 ≤ √R := by rw [Real.one_le_sqrt]; exact hR1
  have hkey : C' * (1 + 2 ^ e) * R ^ e ≤ c0 / 2 * (R * (R ^ e * √R)) := by
    have h1 : 2 * C' * (1 + 2 ^ e) ≤ c0 * R := by rw [div_le_iff₀ hc0] at hRc; linarith
    have h2 : R ≤ R * √R := le_mul_of_one_le_right hR0.le hsq
    have h3 : c0 * R ≤ c0 * (R * √R) := by gcongr
    nlinarith [mul_le_mul_of_nonneg_right (h1.trans h3) hRe.le]
  have e1 := (abs_le.mp hW1).1
  have e2 := (abs_le.mp hW2).2
  have e3 : (2 * R) ^ e = 2 ^ e * R ^ e := mul_pow _ _ _
  rw [e3] at hW2
  have e4 := (abs_le.mp hW2).1
  have e5 := (abs_le.mp hW1).2
  rw [pow_succ]
  nlinarith

/-- info: 'FormalResearch.Special.at47_pointwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.at47_pointwise

/-- info: 'FormalResearch.Special.at47_W_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.at47_W_bound

/-- info: 'FormalResearch.Special.at47_block_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.at47_block_integral

end FormalResearch.Special
