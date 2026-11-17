module

public import FormalResearch.Special.DiscreteAiryKappaOrderLow

/-!
# Arithmetic and window lemmas for the order-sharp `κ` (plan K1, assembly)

Small lemmas used by `DiscreteAiryKappaOrder`: the position of `X_J` from the lattice gaps (`kk_xJ`, `kk_span_up`), the exponential growth
bound for the `Bi` weight on the window (`kk_biwt_le`), the reduction of the pointwise matching to `|Y - κ g Ai(X)| ≤ (C+1) δ³ |κ|`
when `μ` is exponentially small (`kk_rest`, `kk_mu_small`).

**Claim class: proved.**
-/

@[expose] public section

open Finset

namespace FormalResearch.Special

/-- Span of a lattice with gaps `≤ ε'`: `X_m - X_J ≤ (m - J) ε'`. -/
lemma kk_span_up {X : ℤ → ℝ} {J m : ℤ} {ε' : ℝ} (hJm : J ≤ m)
    (hgap : ∀ k : ℤ, J ≤ k → k < m → X (k + 1) - X k ≤ ε') : X m - X J ≤ ((m - J : ℤ) : ℝ) * ε' := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = m - J := ⟨(m - J).toNat, Int.toNat_of_nonneg (by omega)⟩
  have key : ∀ n : ℕ, J + (n : ℤ) ≤ m → X (J + (n : ℤ)) - X J ≤ (n : ℝ) * ε' := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hj
      have h1 := ih (by push_cast at hj; omega)
      have h2 := hgap (J + (n : ℤ)) (by omega) (by push_cast at hj; omega)
      have e : J + ((n + 1 : ℕ) : ℤ) = J + (n : ℤ) + 1 := by push_cast; ring
      rw [e]; push_cast; linarith
  have := key n (by omega)
  rw [show J + (n : ℤ) = m by omega] at this
  have e : ((m - J : ℤ) : ℝ) = (n : ℝ) := by rw [← hn]; simp
  rw [e]; exact this

/-- **Position of `X_J`**: gaps `≥ c₁δ`, `X_m ≤ c₂δ`, `(m - J)δ³ ≥ r - δ³` give `X_J ≤ -(σ₀/δ)²`, `σ₀² ≤ 3c₁r/4`. -/
lemma kk_xJ {X : ℤ → ℝ} {J m : ℤ} {δ c1 c2 r σ0 : ℝ} (hJm : J ≤ m) (hδ : 0 < δ) (hc1 : 0 < c1)
    (hσ2 : σ0 ^ 2 ≤ 3 * c1 * r / 4) (hδ3 : δ ^ 3 ≤ r / 8) (hδc : c2 * δ ^ 3 ≤ c1 * r / 8)
    (hgap : ∀ k : ℤ, J ≤ k → k < m → c1 * δ ≤ X (k + 1) - X k) (hXm : X m ≤ c2 * δ)
    (hpos : r - δ ^ 3 ≤ ((m - J : ℤ) : ℝ) * δ ^ 3) : X J ≤ -((σ0 / δ) ^ 2) := by
  have hspan := kk_span (X := X) (ε0 := c1 * δ) hJm hgap
  have hδ0 : 0 < δ ^ 3 := by positivity
  have h1 : ((m - J : ℤ) : ℝ) * (c1 * δ) ≥ c1 * (r - δ ^ 3) / δ ^ 2 := by
    rw [ge_iff_le, div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hpos hc1.le]
  have h2 : (σ0 / δ) ^ 2 + c2 * δ ≤ c1 * (r - δ ^ 3) / δ ^ 2 := by
    have e : (σ0 / δ) ^ 2 + c2 * δ = (σ0 ^ 2 + c2 * δ ^ 3) / δ ^ 2 := by field_simp
    rw [e]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hδ3 hc1.le]
  linarith

/-- `airyBiWt X ≤ exp(7/δ²)` for `X ≤ 2/δ`, `0 < δ ≤ 1`. -/
lemma kk_biwt_le {δ X : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hX : X ≤ 2 / δ) : airyBiWt X ≤ Real.exp (7 / δ ^ 2) := by
  rw [airyBiWt_eq_mul]
  have h1 := airyWt_le_one X
  have h0 := (airyWt_pos X).le
  have hm : 0 ≤ max X 0 := le_max_right _ _
  have hm2 : max X 0 ≤ 2 / δ := max_le hX (by positivity)
  have hm3 : (max X 0) ^ 2 ≤ 4 / δ ^ 2 := by
    calc (max X 0) ^ 2 ≤ (2 / δ) ^ 2 := pow_le_pow_left₀ hm hm2 2
      _ = 4 / δ ^ 2 := by ring
  have hr : (max X 0) ^ (3 / 2 : ℝ) ≤ (max X 0) ^ 2 + 1 := by
    rcases le_total (max X 0) 1 with h | h
    · have := Real.rpow_le_one hm h (by norm_num : (0 : ℝ) ≤ 3 / 2)
      nlinarith [sq_nonneg (max X 0)]
    · have : (max X 0) ^ (3 / 2 : ℝ) ≤ (max X 0) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h (by norm_num)
      rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this
      linarith
  have hδ2 : 1 ≤ 1 / δ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hξ : 2 * airyXi X ≤ 7 / δ ^ 2 := by
    unfold airyXi
    have : (4 / δ ^ 2 : ℝ) + 1 ≤ 5 / δ ^ 2 := by
      have : 4 / δ ^ 2 + 1 / δ ^ 2 = 5 / δ ^ 2 := by ring
      linarith
    have h5 : 2 * (2 / 3 * (max X 0) ^ (3 / 2 : ℝ)) ≤ 4 / 3 * (5 / δ ^ 2) := by linarith
    have h6 : 4 / 3 * (5 / δ ^ 2) ≤ 7 / δ ^ 2 := by
      have : (0 : ℝ) ≤ 1 / δ ^ 2 := by positivity
      have e : 4 / 3 * (5 / δ ^ 2) = 20 / 3 * (1 / δ ^ 2) := by ring
      have e2 : 7 / δ ^ 2 = 7 * (1 / δ ^ 2) := by ring
      rw [e, e2]; linarith
    linarith
  have := Real.exp_le_exp.2 hξ
  calc airyWt X * Real.exp (2 * airyXi X) ≤ 1 * Real.exp (7 / δ ^ 2) :=
        mul_le_mul h1 this (Real.exp_pos _).le (by norm_num)
    _ = _ := one_mul _

/-- **Pointwise reduction**: if `|Y - (κ g Ai + μ g Bi)| ≤ Cδ³(|κ| W + |μ| W̃)`, `|g| ≤ G`, `W ≤ 1`, `W̃ ≤ E`,
`|Bi| ≤ 450 W̃`, `δ³ ≤ 1`, and `(450 G + C)|μ|E ≤ δ³|κ|`, then `|Y - κ g Ai| ≤ (C+1) δ³ |κ|`. -/
lemma kk_rest {Y g A B κ μ C δ G W W' E : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hG : 0 ≤ G)
    (hY : |Y - (κ * (g * A) + μ * (g * B))| ≤ C * δ ^ 3 * (|κ| * W + |μ| * W')) (hg : |g| ≤ G) (hW : W ≤ 1)
    (hW' : W' ≤ E) (hW'0 : 0 ≤ W') (hB : |B| ≤ 450 * W')
    (hμ : (450 * G + C) * |μ| * E ≤ δ ^ 3 * |κ|) : |Y - κ * (g * A)| ≤ (C + 1) * δ ^ 3 * |κ| := by
  have hδ3 : δ ^ 3 ≤ 1 := pow_le_one₀ hδ.le hδ1
  have hE : 0 ≤ E := hW'0.trans hW'
  have t1 : |μ * (g * B)| ≤ 450 * G * |μ| * E := by
    rw [abs_mul, abs_mul]
    have h1 : |g| * |B| ≤ G * (450 * E) := mul_le_mul hg (hB.trans (by linarith)) (abs_nonneg _) hG
    nlinarith [abs_nonneg μ]
  have t2 : C * δ ^ 3 * (|κ| * W + |μ| * W') ≤ C * δ ^ 3 * |κ| + C * |μ| * E := by
    have a1 : |κ| * W ≤ |κ| := mul_le_of_le_one_right (abs_nonneg _) hW
    have a2 : |μ| * W' ≤ |μ| * E := mul_le_mul_of_nonneg_left hW' (abs_nonneg _)
    have a3 : C * δ ^ 3 * (|μ| * E) ≤ C * (|μ| * E) := by
      have : 0 ≤ C * (|μ| * E) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hδ3 this]
    have a4 : C * δ ^ 3 * (|κ| * W) ≤ C * δ ^ 3 * |κ| := mul_le_mul_of_nonneg_left a1 (by positivity)
    have a5 : C * δ ^ 3 * (|μ| * W') ≤ C * δ ^ 3 * (|μ| * E) := mul_le_mul_of_nonneg_left a2 (by positivity)
    have e1 : C * δ ^ 3 * (|κ| * W + |μ| * W') = C * δ ^ 3 * (|κ| * W) + C * δ ^ 3 * (|μ| * W') := by ring
    have e2 : C * |μ| * E = C * (|μ| * E) := by ring
    rw [e1, e2]; linarith
  have e : Y - κ * (g * A) = (Y - (κ * (g * A) + μ * (g * B))) + μ * (g * B) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  nlinarith

/-- **Smallness of the `μ` term**: `B₀ (1/δ³) (e^{-ξ₀/δ³}/δ) e^{7/δ²} ≤ δ³ κ_min` for `δ ≤ ξ₀/14`, `δ ≤ κ_min ξ₀³/(48 (B₀+1))`. -/
lemma kk_mu_small {δ ξ0 B0 κmin : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hξ : 0 < ξ0) (hB : 0 ≤ B0)
    (h1 : δ ≤ ξ0 / 14) (h2 : δ ≤ κmin * ξ0 ^ 3 / (48 * (B0 + 1))) :
    B0 * (1 / δ ^ 3) * (Real.exp (-ξ0 / δ ^ 3) / δ) * Real.exp (7 / δ ^ 2) ≤ δ ^ 3 * κmin := by
  have hδ3 : 0 < δ ^ 3 := by positivity
  have hexp : Real.exp (-ξ0 / δ ^ 3) * Real.exp (7 / δ ^ 2) ≤ Real.exp (-(ξ0 / (2 * δ ^ 3))) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have h3 : 7 / δ ^ 2 ≤ ξ0 / (2 * δ ^ 3) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg δ), sq_nonneg δ]
    have e : -ξ0 / δ ^ 3 = -(ξ0 / (2 * δ ^ 3)) - ξ0 / (2 * δ ^ 3) := by field_simp; ring
    linarith
  set t : ℝ := ξ0 / (2 * δ ^ 3) with ht
  have ht0 : 0 < t := by positivity
  have h6 : Real.exp (-t) ≤ 6 / t ^ 3 := by
    have : t ^ 3 / 6 ≤ Real.exp t := by
      have := Real.pow_div_factorial_le_exp t ht0.le 3
      simpa [Nat.factorial] using this
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
    nlinarith
  have h7 : 6 / t ^ 3 = 48 * δ ^ 9 / ξ0 ^ 3 := by rw [ht]; field_simp; ring
  have h8 : B0 * (1 / δ ^ 3) * (Real.exp (-ξ0 / δ ^ 3) / δ) * Real.exp (7 / δ ^ 2) =
      B0 / δ ^ 4 * (Real.exp (-ξ0 / δ ^ 3) * Real.exp (7 / δ ^ 2)) := by field_simp
  rw [h8]
  have h9 : B0 / δ ^ 4 * (Real.exp (-ξ0 / δ ^ 3) * Real.exp (7 / δ ^ 2)) ≤ B0 / δ ^ 4 * (48 * δ ^ 9 / ξ0 ^ 3) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact hexp.trans (h6.trans h7.le)
  refine h9.trans ?_
  have e : B0 / δ ^ 4 * (48 * δ ^ 9 / ξ0 ^ 3) = 48 * B0 * δ ^ 5 / ξ0 ^ 3 := by field_simp
  rw [e, div_le_iff₀ (by positivity)]
  have h10 : δ * (48 * (B0 + 1)) ≤ κmin * ξ0 ^ 3 := by
    rw [le_div_iff₀ (by positivity)] at h2; linarith
  have h11 : 48 * B0 * δ ^ 5 ≤ δ ^ 3 * (δ * (48 * (B0 + 1))) := by
    have : 0 ≤ δ ^ 5 := by positivity
    nlinarith [mul_nonneg this hB]
  calc 48 * B0 * δ ^ 5 ≤ δ ^ 3 * (δ * (48 * (B0 + 1))) := h11
    _ ≤ δ ^ 3 * (κmin * ξ0 ^ 3) := mul_le_mul_of_nonneg_left h10 hδ3.le
    _ = δ ^ 3 * κmin * ξ0 ^ 3 := by ring

/-- info: 'FormalResearch.Special.kk_mu_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.kk_mu_small

end FormalResearch.Special
