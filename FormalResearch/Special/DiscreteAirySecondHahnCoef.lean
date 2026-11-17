module

public import FormalResearch.Special.DiscreteAiryLimitHahn

/-!
# Second-order coefficient closeness for the closed-form Hahn / centred Racah chains (S4, part 1)

The closed forms of P3 `A:1319-1322` (`DiscreteAiryLimitHahn`: `hrAk`, `hrCk`) are `O(h²)`-close to the first-order data
`A(q - h/2)`, `2A(q)u(q)` (`hr_perturb`).  Here the `h²` terms are extracted exactly and the remainder is shown to be `O(h⁴)`
(a fortiori `O(h³)`, the closeness `E δ⁹ = E h³` that the second-order Airy bracket `airy2_turn_full` consumes):

* off-diagonal: `a_k = A_k = ½ r_k ẽ((kh)²)`, `r_k = [(1-a²/k²)(1-b²/k²)/(1-1/(4k²))]^{1/2}`,
  `|A_k - (A + h² A₂)(kh)| ≤ E h⁴`, `A(q) = ½ ẽ(q²)`, **`A₂(q) = ½ ẽ(q²) c_{ab}/q²`, `c_{ab} = 1/8 - (a²+b²)/2`**
  (`hsA2`; P3 `eq:class-a2b2`: `a₂ = a₀ [c_{ab}/q² + η_π(q²)]`, `η_π = 0` for the Hahn and centred Racah closed forms);
* diagonal: `c_k = τ(x - B_k)`, `|c_k - (τ(x - β₀q²) + h² c₂(q))| ≤ E h⁴` at `q = q_k = (k+½)h`, where
  `τ(x - β₀q²) = 2A(q)u(q)` and **`c₂(q) = -τ[β₀(1/4 - (a²+b²)/2) + ab/q²]`** (`hsCq`; this is `-τ b₂` with
  `b₂ = ab/q² + ∂_t v_π(q², 0)` of P3 `eq:class-a2b2`, `∂_t v_π(q²,0) = β₀(1/4 - (a²+b²)/2)`; for Hahn `β₀ = 0`, `b₂ = Mσ/q²`).

The proofs are exact algebra: `√R - 1 - (R-1)/2 = -(√R - 1)²/2`, `R - 1 - Dt = t²(a²b² + D/4)/(1 - t/4)` for
`R = (1-a²t)(1-b²t)/(1-t/4)`, and `ab/(k(k+1)) - ab h²/q² = ab h⁴/(4q²(q²-h²/4))`.  The constants are explicit (`hsE`); no
numerical constant is claimed beyond that.  Numerical check (mpmath, 30 digits, scratch only; `P = 1, Q = 0.3, a = 2, b = 1.5,
τ = 1, x = 0.4`, `q ∈ {0.3, 0.6}`, `h ∈ {10⁻², 5·10⁻³, 2.5·10⁻³}`): `(A_k - (A + h²A₂))/h⁴` and `(c_k - (c + h²c₂))/h⁴` are
constant to three digits (`-43.57`, `-2.186` resp. `-92.6`, `-5.787`; the latter is the leading term `-ab/(4q⁴)` of the exact
diagonal identity `hsc_C_alg`), i.e. the remainder is exactly of order `h⁴`.

**Claim class: proved.**  Not formalised here: the half-integer (shifted-lattice) and mixed-parity forms, the `q`-Racah chain with
its `η_π ≠ 0` data; the identification with the actual `3j`/`6j` chains is `hahn_class_chain`, `racah_class_chain`
(`DiscreteAiryLimitChains{3j,6j}`).
-/

@[expose] public section

open FormalResearch.Racah.P3 FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- `c_{ab} = 1/8 - (a² + b²)/2` (P3 `eq:class-a2b2`). -/
noncomputable def hsCab (a b : ℝ) : ℝ := 1 / 8 - (a ^ 2 + b ^ 2) / 2

/-- The second-order off-diagonal coefficient `A₂(q) = ½ ẽ(q²) c_{ab}/q²` of the Hahn / centred Racah closed form. -/
noncomputable def hsA2 (P Q a b : ℝ) (q : ℝ) : ℝ := 1 / 2 * etilde P Q (q ^ 2) * (hsCab a b / q ^ 2)

/-- The second-order diagonal coefficient `c₂(q) = -τ[β₀(1/4 - (a²+b²)/2) + ab/q²]` of the Hahn / centred Racah closed form
(`c = 2 A u = τ(x - β₀ q²)`). -/
noncomputable def hsCq (P Q a b τ : ℝ) (q : ℝ) : ℝ :=
  -τ * (Real.sqrt (P * Q) * (1 / 4 - (a ^ 2 + b ^ 2) / 2) + a * b / q ^ 2)

/-- The size `S = |1/4 - a² - b²| + a²b²` entering the ratio expansion. -/
noncomputable def hsS (a b : ℝ) : ℝ := |1 / 4 - a ^ 2 - b ^ 2| + a ^ 2 * b ^ 2

lemma hsS_nonneg (a b : ℝ) : 0 ≤ hsS a b := by unfold hsS; positivity

/-- `|√R - 1 - (R-1)/2| ≤ (R-1)²/2` for `R ≥ 0`. -/
lemma hs_sqrt_second {R : ℝ} (hR : 0 ≤ R) : |Real.sqrt R - 1 - (R - 1) / 2| ≤ (R - 1) ^ 2 / 2 := by
  set s := Real.sqrt R with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg R
  have hs2 : s ^ 2 = R := Real.sq_sqrt hR
  have e : s - 1 - (R - 1) / 2 = -((s - 1) ^ 2 / 2) := by rw [← hs2]; ring
  rw [e, abs_neg, abs_of_nonneg (by positivity)]
  have h1 : (s - 1) ^ 2 ≤ (R - 1) ^ 2 := by
    have e2 : R - 1 = (s - 1) * (s + 1) := by rw [← hs2]; ring
    rw [e2, mul_pow]
    have : 1 ≤ (s + 1) ^ 2 := by nlinarith
    nlinarith [sq_nonneg (s - 1)]
  linarith

/-- Abstract form of the ratio expansion: `R ≥ 0` with `R - 1 - D t = t²(P + D/4)/(1 - t/4)`, `P ≥ 0`, `S = |D| + P`,
`0 < t ≤ 1` gives `|√R - 1 - (D/2) t| ≤ 5 (S+1)² t²`. -/
lemma hs_ratio_abs {R D P S t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (hR0 : 0 ≤ R) (hP : 0 ≤ P) (hS : S = |D| + P)
    (hRD : R - 1 - D * t = t ^ 2 * (P + D / 4) / (1 - t / 4)) :
    |Real.sqrt R - 1 - D / 2 * t| ≤ 5 * (S + 1) ^ 2 * t ^ 2 := by
  have hd : 0 < 1 - t / 4 := by linarith
  have hS0 : 0 ≤ S := by rw [hS]; positivity
  have hDS : |D| ≤ S := by rw [hS]; linarith
  have hq : |P + D / 4| ≤ S := by
    have h1 : |P + D / 4| ≤ |P| + |D / 4| := abs_add_le _ _
    rw [abs_of_nonneg hP, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)] at h1
    have := abs_nonneg D
    rw [hS]; linarith
  have ht2 : 0 < t ^ 2 := by positivity
  have h2 : |R - 1 - D * t| ≤ 4 / 3 * S * t ^ 2 := by
    rw [hRD, abs_div, abs_mul, abs_of_pos hd, abs_of_pos ht2, div_le_iff₀ hd]
    have h1 : t ^ 2 * |P + D / 4| ≤ t ^ 2 * S := mul_le_mul_of_nonneg_left hq ht2.le
    have h3 : 0 ≤ t ^ 2 * S := by positivity
    have h4 : 4 / 3 * S * t ^ 2 * (1 - t / 4) ≥ 4 / 3 * S * t ^ 2 * (3 / 4) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have htt : t ^ 2 ≤ t := by nlinarith
  have h3 : |R - 1| ≤ 3 * S * t := by
    have e : R - 1 = D * t + (R - 1 - D * t) := by ring
    have h4 : |D * t| ≤ S * t := by
      rw [abs_mul, abs_of_pos ht0]
      exact mul_le_mul_of_nonneg_right hDS ht0.le
    have h5 : S * t ^ 2 ≤ S * t := mul_le_mul_of_nonneg_left htt hS0
    have h6 : 0 ≤ S * t := by positivity
    have h7 := abs_add_le (D * t) (R - 1 - D * t)
    rw [← e] at h7
    nlinarith [h7, h4, h2, h5, h6]
  have h6 := hs_sqrt_second hR0
  have h7 : (R - 1) ^ 2 / 2 ≤ 9 / 2 * S ^ 2 * t ^ 2 := by
    have h8 : (R - 1) ^ 2 ≤ (3 * S * t) ^ 2 := by
      rw [← sq_abs (R - 1)]
      exact pow_le_pow_left₀ (abs_nonneg _) h3 2
    nlinarith [h8]
  have e : Real.sqrt R - 1 - D / 2 * t =
      (Real.sqrt R - 1 - (R - 1) / 2) + (R - 1 - D * t) / 2 := by ring
  rw [e]
  have h8 := abs_le.1 h2
  have h9 := abs_le.1 h6
  have hfin : 9 / 2 * S ^ 2 * t ^ 2 + 2 / 3 * S * t ^ 2 ≤ 5 * (S + 1) ^ 2 * t ^ 2 := by
    have : 9 / 2 * S ^ 2 + 2 / 3 * S ≤ 5 * (S + 1) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right this ht2.le]
  rw [abs_le]
  constructor <;> nlinarith [h9.1, h9.2, h8.1, h8.2, h7, hfin]

/-- **Second-order expansion of the ratio.**  For `t ∈ (0, 1]` with `a²t, b²t ≤ 1`,
`|√((1-a²t)(1-b²t)/(1-t/4)) - 1 - c_{ab} t| ≤ 5 (S+1)² t²`. -/
lemma hs_ratio_second {a b t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (ha : a ^ 2 * t ≤ 1) (hb : b ^ 2 * t ≤ 1) :
    |Real.sqrt ((1 - a ^ 2 * t) * (1 - b ^ 2 * t) / (1 - t / 4)) - 1 - hsCab a b * t| ≤
      5 * (hsS a b + 1) ^ 2 * t ^ 2 := by
  have hd : 0 < 1 - t / 4 := by linarith
  have hR0 : 0 ≤ (1 - a ^ 2 * t) * (1 - b ^ 2 * t) / (1 - t / 4) :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) hd.le
  have hcab : hsCab a b * t = (1 / 4 - a ^ 2 - b ^ 2) / 2 * t := by unfold hsCab; ring
  rw [hcab]
  refine hs_ratio_abs (P := a ^ 2 * b ^ 2) ht0 ht1 hR0 (by positivity) rfl ?_
  rw [eq_div_iff hd.ne', sub_mul, sub_mul, div_mul_cancel₀ _ hd.ne']
  ring

/-- `A_k` against `A + h² A₂` at `q = kh`: `|A_k - (A(kh) + h² A₂(kh))| ≤ 8·5 (S+1)² h⁴/q_*⁴`. -/
lemma hsc_coef_A {P Q a b h k qs : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hh : 0 < h) (hqs : 0 < qs) (hk : 1 ≤ k)
    (ha : a ^ 2 ≤ k ^ 2) (hb : b ^ 2 ≤ k ^ 2) (hkq : qs ≤ 2 * k * h) (hdom : (k * h) ^ 2 ∈ Dom P Q) :
    |1 / 2 * rr a b k * etilde P Q ((k * h) ^ 2) - (1 / 2 * etilde P Q ((k * h) ^ 2) + h ^ 2 * hsA2 P Q a b (k * h))| ≤
      40 * (hsS a b + 1) ^ 2 / qs ^ 4 * h ^ 4 := by
  have hk0 : 0 < k := by linarith
  set e := etilde P Q ((k * h) ^ 2) with he
  have he0 : 0 ≤ e := etilde_nonneg _ _ _
  have he1 : e ≤ 1 := etilde_le_one hP hQ hdom
  set t : ℝ := 1 / k ^ 2 with ht
  have ht0 : 0 < t := by positivity
  have hk2 : 1 ≤ k ^ 2 := by nlinarith
  have ht1 : t ≤ 1 := by rw [ht, div_le_one (by positivity)]; exact hk2
  have hat : a ^ 2 * t ≤ 1 := by
    rw [ht, mul_one_div, div_le_one (by positivity)]; exact ha
  have hbt : b ^ 2 * t ≤ 1 := by
    rw [ht, mul_one_div, div_le_one (by positivity)]; exact hb
  have hrr : rr a b k = Real.sqrt ((1 - a ^ 2 * t) * (1 - b ^ 2 * t) / (1 - t / 4)) := by
    unfold rr
    congr 1
    rw [ht]
    field_simp
  have hA2 : h ^ 2 * hsA2 P Q a b (k * h) = 1 / 2 * e * (hsCab a b * t) := by
    unfold hsA2
    rw [← he, ht]
    field_simp
  have hmain := hs_ratio_second ht0 ht1 hat hbt
  rw [← hrr] at hmain
  have eq : 1 / 2 * rr a b k * e - (1 / 2 * e + h ^ 2 * hsA2 P Q a b (k * h)) =
      1 / 2 * e * (rr a b k - 1 - hsCab a b * t) := by rw [hA2]; ring
  rw [eq, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / 2 * e)]
  have ht2 : t ^ 2 ≤ 16 / qs ^ 4 * h ^ 4 := by
    have h1 : t ≤ 4 * h ^ 2 / qs ^ 2 := by
      rw [ht, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have h2 : t ^ 2 ≤ (4 * h ^ 2 / qs ^ 2) ^ 2 := by gcongr
    calc t ^ 2 ≤ (4 * h ^ 2 / qs ^ 2) ^ 2 := h2
      _ = 16 / qs ^ 4 * h ^ 4 := by field_simp; ring
  have hc : 0 ≤ 5 * (hsS a b + 1) ^ 2 := by positivity
  calc 1 / 2 * e * |rr a b k - 1 - hsCab a b * t| ≤ 1 / 2 * 1 * (5 * (hsS a b + 1) ^ 2 * t ^ 2) := by
        apply mul_le_mul (by linarith) hmain (abs_nonneg _) (by norm_num)
    _ ≤ 1 / 2 * (5 * (hsS a b + 1) ^ 2 * (16 / qs ^ 4 * h ^ 4)) := by
        have := mul_le_mul_of_nonneg_left ht2 hc
        linarith
    _ = 40 * (hsS a b + 1) ^ 2 / qs ^ 4 * h ^ 4 := by ring

/-- The exact `h⁴` identity behind the diagonal: with `q = (k+½)h`, `k(k+1) = (q² - h²/4)/h²`. -/
lemma hsc_C_alg {β₀ a b h k : ℝ} (hh : 0 < h) (hk : 1 ≤ k) :
    β₀ * (((k + 1 / 2) * h) ^ 2 + h ^ 2 / 4) - β₀ * h ^ 2 * (a ^ 2 + b ^ 2) / 2 + a * b / (k * (k + 1)) -
        (β₀ * ((k + 1 / 2) * h) ^ 2 + h ^ 2 * (β₀ * (1 / 4 - (a ^ 2 + b ^ 2) / 2) + a * b / ((k + 1 / 2) * h) ^ 2)) =
      a * b * h ^ 4 / (4 * ((k + 1 / 2) * h) ^ 2 * (((k + 1 / 2) * h) ^ 2 - h ^ 2 / 4)) := by
  have hk0 : 0 < k := by linarith
  have h1 : (k + 1 / 2) * h ≠ 0 := by positivity
  have h2 : ((k + 1 / 2) * h) ^ 2 - h ^ 2 / 4 = k * (k + 1) * h ^ 2 := by ring
  rw [h2]
  field_simp
  ring

/-- `c_k` against `τ(x - β₀q²) + h² c₂(q)` at `q = q_k = (k+½)h`: the remainder is `≤ 6|ab| h⁴/q_*⁴`. -/
lemma hsc_coef_C {P Q a b τ x h k qs : ℝ} (hh : 0 < h) (hqs : 0 < qs) (hτ : τ ^ 2 = 1) (hk : 1 ≤ k)
    (hkq : qs ≤ 2 * k * h) :
    |τ * (x - hrB (Real.sqrt (P * Q)) a b h k) -
        (τ * (x - Real.sqrt (P * Q) * ((k + 1 / 2) * h) ^ 2) + h ^ 2 * hsCq P Q a b τ ((k + 1 / 2) * h))| ≤
      6 * |a * b| / qs ^ 4 * h ^ 4 := by
  have hk0 : 0 < k := by linarith
  set q : ℝ := (k + 1 / 2) * h with hq
  have hq0 : 0 < q := by positivity
  have hhq : h ≤ q := by rw [hq]; nlinarith
  have hqs2 : qs / 2 ≤ q := by rw [hq]; nlinarith
  have hτa : |τ| = 1 := by
    have : |τ| ^ 2 = 1 := by rw [sq_abs]; exact hτ
    nlinarith [abs_nonneg τ]
  have e := hsc_C_alg (β₀ := Real.sqrt (P * Q)) (a := a) (b := b) hh hk
  rw [← hq] at e
  have e2 : τ * (x - hrB (Real.sqrt (P * Q)) a b h k) -
      (τ * (x - Real.sqrt (P * Q) * q ^ 2) + h ^ 2 * hsCq P Q a b τ q) =
      -τ * (a * b * h ^ 4 / (4 * q ^ 2 * (q ^ 2 - h ^ 2 / 4))) := by
    rw [← e]; unfold hrB hsCq; rw [hq]; ring
  rw [e2, abs_mul, abs_neg, hτa, one_mul, abs_div, abs_mul (a * b) (h ^ 4), abs_pow, abs_of_pos hh]
  have hden : 3 / 4 * q ^ 2 ≤ q ^ 2 - h ^ 2 / 4 := by nlinarith
  have hden0 : 0 < q ^ 2 - h ^ 2 / 4 := by nlinarith [pow_pos hq0 2]
  rw [abs_of_pos (by positivity : 0 < 4 * q ^ 2 * (q ^ 2 - h ^ 2 / 4))]
  rw [div_le_iff₀ (by positivity)]
  have hq4 : qs ^ 4 ≤ 16 * q ^ 4 := by
    have : (qs / 2) ^ 4 ≤ q ^ 4 := by gcongr
    nlinarith [this]
  have hab : 0 ≤ |a * b| := abs_nonneg _
  have h4 : 0 ≤ h ^ 4 := by positivity
  have key : |a * b| * h ^ 4 * qs ^ 4 ≤
      6 * |a * b| / qs ^ 4 * h ^ 4 * (4 * q ^ 2 * (q ^ 2 - h ^ 2 / 4)) * qs ^ 4 := by
    have h1 : 4 * q ^ 2 * (q ^ 2 - h ^ 2 / 4) ≥ 3 * q ^ 4 := by nlinarith [pow_pos hq0 2]
    have h2 : 6 * |a * b| / qs ^ 4 * h ^ 4 * (4 * q ^ 2 * (q ^ 2 - h ^ 2 / 4)) * qs ^ 4 =
        6 * |a * b| * h ^ 4 * (4 * q ^ 2 * (q ^ 2 - h ^ 2 / 4)) := by field_simp
    rw [h2]
    have h3 : 0 ≤ 6 * |a * b| * h ^ 4 := by positivity
    have hw : 0 ≤ |a * b| * h ^ 4 := by positivity
    have h5 := mul_le_mul_of_nonneg_left hq4 hw
    have h6 := mul_le_mul_of_nonneg_left h1 hw
    have h7 : 0 ≤ |a * b| * h ^ 4 * (4 * q ^ 2 * (q ^ 2 - h ^ 2 / 4)) := by positivity
    nlinarith [h5, h6, h7]
  have hqs4 : 0 < qs ^ 4 := by positivity
  exact le_of_mul_le_mul_right key hqs4

/-- The perturbation size `E = max(40 (S+1)²/q_*⁴, 6|ab|/q_*⁴)` of the second-order closeness (`h⁴`; a fortiori `h³`). -/
noncomputable def hsE (a b qs : ℝ) : ℝ := max (40 * (hsS a b + 1) ^ 2 / qs ^ 4) (6 * |a * b| / qs ^ 4)

lemma hsE_nonneg (a b qs : ℝ) : 0 ≤ hsE a b qs :=
  (show 0 ≤ 40 * (hsS a b + 1) ^ 2 / qs ^ 4 by positivity).trans (le_max_left _ _)

/-- **Second-order closeness on a window** (the analogue of `hr_perturb` with the `h²` terms subtracted): on the window
`k ∈ [J+1, N+1]` with `|q_k - q_*| ≤ r ≤ r₀` (`q_k = (k+½)δ³`), `δ ≤ 1`, `δ ≤ 3q_*/(4M)` (`M = hrM a b`):
`|A_k - (A + δ⁶ A₂)(q_k - h/2)| ≤ E δ⁹` and `|c_k - (2A(q_k)u(q_k) + δ⁶ c₂(q_k))| ≤ E δ⁹` (`h = δ³`; the true remainder is
`O(h⁴)`). -/
lemma hs_perturb {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (a b τ x qs : ℝ) (hqs : 0 < qs) (hτ : τ ^ 2 = 1)
    {r r0 δ : ℝ} {J N : ℤ} (hr4 : r ≤ qs / 4) (hrr : r ≤ r0)
    (hdom : ∀ q ∈ Set.Icc (qs - r0) (qs + r0), 0 < 1 - P * q ^ 2 ∧ 0 < 1 - Q * q ^ 2)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδM : δ ≤ 3 * qs / (4 * hrM a b))
    (hwin : ∀ k ∈ Finset.Icc J (N + 1), dalQ (δ ^ 3 / 2) δ k ∈ Set.Icc (qs - r) (qs + r)) :
    (∀ k ∈ Finset.Icc (J + 1) (N + 1),
      |hrAk P Q a b (δ ^ 3) k - (hrA1 P Q (dalQ (δ ^ 3 / 2) δ k - δ ^ 3 / 2) +
        (δ ^ 3) ^ 2 * hsA2 P Q a b (dalQ (δ ^ 3 / 2) δ k - δ ^ 3 / 2))| ≤ hsE a b qs * δ ^ 9) ∧
    (∀ k ∈ Finset.Icc (J + 1) N,
      |hrCk P Q τ x a b (δ ^ 3) k - (2 * hrA1 P Q (dalQ (δ ^ 3 / 2) δ k) * hrU P Q τ x (dalQ (δ ^ 3 / 2) δ k) +
        (δ ^ 3) ^ 2 * hsCq P Q a b τ (dalQ (δ ^ 3 / 2) δ k))| ≤ hsE a b qs * δ ^ 9) := by
  have hM1 : 1 ≤ hrM a b := le_max_left _ _
  have hMa : |a| ≤ hrM a b := (le_max_left _ _).trans (le_max_right _ _)
  have hMb : |b| ≤ hrM a b := (le_max_right _ _).trans (le_max_right _ _)
  have h3 : 0 < δ ^ 3 := by positivity
  have h3δ : δ ^ 3 ≤ δ := by
    have h1 : δ ^ 2 ≤ 1 := pow_le_one₀ hδ.le hδ1
    calc δ ^ 3 = δ * δ ^ 2 := by ring
      _ ≤ δ * 1 := mul_le_mul_of_nonneg_left h1 hδ.le
      _ = δ := mul_one _
  have h31 : δ ^ 3 ≤ 1 := h3δ.trans hδ1
  have hyw : ∀ k ∈ Finset.Icc (J + 1) (N + 1), qs - r ≤ (k : ℝ) * δ ^ 3 ∧ (k : ℝ) * δ ^ 3 ≤ qs + r := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have h1 := hwin (k - 1) (by rw [Finset.mem_Icc]; omega)
    have h2 := hwin k (by rw [Finset.mem_Icc]; omega)
    have e1 : dalQ (δ ^ 3 / 2) δ (k - 1) = (k : ℝ) * δ ^ 3 - δ ^ 3 / 2 := by unfold dalQ; push_cast; ring
    have e2 : dalQ (δ ^ 3 / 2) δ k = (k : ℝ) * δ ^ 3 + δ ^ 3 / 2 := by unfold dalQ; ring
    rw [e1] at h1; rw [e2] at h2
    constructor <;> linarith [h1.1, h2.2]
  have hkM : ∀ k ∈ Finset.Icc (J + 1) (N + 1), hrM a b ≤ (k : ℝ) := by
    intro k hk
    have := (hyw k hk).1
    have h4 : 3 * qs / 4 ≤ (k : ℝ) * δ ^ 3 := by linarith
    have h5 : δ ^ 3 ≤ 3 * qs / (4 * hrM a b) := h3δ.trans hδM
    rw [le_div_iff₀ (by positivity)] at h5
    by_contra hlt
    push Not at hlt
    nlinarith [mul_lt_mul_of_pos_right hlt h3]
  have hk1 : ∀ k ∈ Finset.Icc (J + 1) (N + 1),
      1 ≤ (k : ℝ) ∧ a ^ 2 ≤ (k : ℝ) ^ 2 ∧ b ^ 2 ≤ (k : ℝ) ^ 2 ∧ qs ≤ 2 * (k : ℝ) * δ ^ 3 ∧
        ((k : ℝ) * δ ^ 3) ^ 2 ∈ Dom P Q := by
    intro k hk
    have hM' := hkM k hk
    have hy := hyw k hk
    have hyd := hdom ((k : ℝ) * δ ^ 3) ⟨by linarith [hy.1], by linarith [hy.2]⟩
    refine ⟨hM1.trans hM', ?_, ?_, ?_, ⟨by positivity, ?_, ?_⟩⟩
    · have : |a| ≤ (k : ℝ) := hMa.trans hM'
      nlinarith [sq_abs a, abs_nonneg a]
    · have : |b| ≤ (k : ℝ) := hMb.trans hM'
      nlinarith [sq_abs b, abs_nonneg b]
    · nlinarith [hy.1]
    · linarith [hyd.1]
    · linarith [hyd.2]
  have h9 : (δ ^ 3) ^ 4 ≤ δ ^ 9 := by
    have : (δ ^ 3) ^ 4 = δ ^ 12 := by ring
    rw [this]
    exact pow_le_pow_of_le_one hδ.le hδ1 (by norm_num)
  have h49 : (δ ^ 3) ^ 4 ≤ δ ^ 9 := h9
  constructor
  · intro k hk
    obtain ⟨k1, ka, kb, kq, kd⟩ := hk1 k hk
    have e : dalQ (δ ^ 3 / 2) δ k - δ ^ 3 / 2 = (k : ℝ) * δ ^ 3 := by unfold dalQ; ring
    rw [e]
    unfold hrAk hrA1
    have := hsc_coef_A (P := P) (Q := Q) (a := a) (b := b) hP hQ h3 hqs k1 ka kb kq kd
    refine this.trans ?_
    have hE : 40 * (hsS a b + 1) ^ 2 / qs ^ 4 ≤ hsE a b qs := le_max_left _ _
    calc 40 * (hsS a b + 1) ^ 2 / qs ^ 4 * (δ ^ 3) ^ 4 ≤ hsE a b qs * (δ ^ 3) ^ 4 :=
          mul_le_mul_of_nonneg_right hE (by positivity)
      _ ≤ hsE a b qs * δ ^ 9 := mul_le_mul_of_nonneg_left h49 (hsE_nonneg a b qs)
  · intro k hk
    have hk' : k ∈ Finset.Icc (J + 1) (N + 1) := by rw [Finset.mem_Icc] at hk ⊢; omega
    obtain ⟨k1, ka, kb, kq, kd⟩ := hk1 k hk'
    have hqw := hwin k (by rw [Finset.mem_Icc] at hk ⊢; omega)
    have hqd := hdom (dalQ (δ ^ 3 / 2) δ k) ⟨by linarith [hqw.1], by linarith [hqw.2]⟩
    have e2 : dalQ (δ ^ 3 / 2) δ k = ((k : ℝ) + 1 / 2) * δ ^ 3 := by unfold dalQ; ring
    have hpos : 0 < etilde P Q ((((k : ℝ) + 1 / 2) * δ ^ 3) ^ 2) := by
      rw [e2] at hqd
      unfold etilde; exact Real.sqrt_pos.2 (mul_pos hqd.1 hqd.2)
    have e1 : 2 * hrA1 P Q (dalQ (δ ^ 3 / 2) δ k) * hrU P Q τ x (dalQ (δ ^ 3 / 2) δ k) =
        τ * (x - Real.sqrt (P * Q) * (((k : ℝ) + 1 / 2) * δ ^ 3) ^ 2) := by
      unfold hrA1 hrU
      rw [e2]
      generalize etilde P Q ((((k : ℝ) + 1 / 2) * δ ^ 3) ^ 2) = e at hpos ⊢
      field_simp
    rw [e1, e2]
    unfold hrCk
    have := hsc_coef_C (P := P) (Q := Q) (a := a) (b := b) (τ := τ) (x := x) (qs := qs) h3 hqs hτ k1 kq
    refine this.trans ?_
    have hE : 6 * |a * b| / qs ^ 4 ≤ hsE a b qs := le_max_right _ _
    calc 6 * |a * b| / qs ^ 4 * (δ ^ 3) ^ 4 ≤ hsE a b qs * (δ ^ 3) ^ 4 :=
          mul_le_mul_of_nonneg_right hE (by positivity)
      _ ≤ hsE a b qs * δ ^ 9 := mul_le_mul_of_nonneg_left h49 (hsE_nonneg a b qs)

/-- info: 'FormalResearch.Special.hsc_coef_A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hsc_coef_A

/-- info: 'FormalResearch.Special.hs_perturb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hs_perturb

/-- info: 'FormalResearch.Special.hsc_coef_C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hsc_coef_C

end FormalResearch.Special
