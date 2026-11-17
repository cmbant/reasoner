module

public import FormalResearch.Special.AiryAsymReal
public import FormalResearch.Special.AiryKernelOpFormula

/-!
# Lattice sums of `Ai²` on the oscillatory side (plan K1, step 2: the near-turn mass)

`∫ Ai² = x Ai² - Ai'²` (since `Ai'' = x Ai`), and `Ai'(-y)² + y Ai(-y)² = K(-y,-y) = √y/π + O(1/y)` (`airyKer_diag_neg`).  Hence a
lattice sum of `Ai(X_k)²` over a monotone lattice with gaps `≤ ε'` is bounded below by a Riemann sum of the antiderivative:

* `kai_lip`: `|2 Ai(-y) Ai'(-y)| ≤ 2` for `y ≥ 1` (so `Ai²` is `2`-Lipschitz on `(-∞, -1]`);
* `kai_step`: for `s < t ≤ -1`, `F(t) - F(s) ≤ (t - s)(Ai(s)² + 2(t - s))`, `F = x Ai² - Ai'²`;
* `kai_sum`: `ε' Σ_{a ≤ k < b} Ai(X_k)² ≥ K(X_a) - K(X_b) - 2ε'(X_b - X_a)` for a lattice `X_a < ⋯ < X_b ≤ -1` with gaps in `(0, ε']`;
* `kai_sum_lower`: the same with `K` replaced by `√y/π`: `ε' Σ ≥ (√y_a - √y_b)/π - 1/y_a - 1/y_b - 2ε'(y_a - y_b)`.

**Claim class: proved.**  **Not formalised:** the sharp value of the constants (these are the lattice Riemann sums, error `O(ε' · length)`).
-/

@[expose] public section

open Finset Set

namespace FormalResearch.Special

/-- `F(x) = x Ai(x)² - Ai'(x)²` has derivative `Ai(x)²`. -/
lemma kai_F_deriv (x : ℝ) :
    HasDerivAt (fun x => x * airyAi x ^ 2 - airyAi' x ^ 2) (airyAi x ^ 2) x := by
  have h1 := hasDerivAt_airyAi x
  have h2 := hasDerivAt_airyAi' x
  have h3 := ((hasDerivAt_id' x).mul (h1.mul h1)).sub (h2.mul h2)
  have e : (fun x => x * airyAi x ^ 2 - airyAi' x ^ 2) = fun x => x * (airyAi x * airyAi x) - airyAi' x * airyAi' x := by
    funext y; ring
  rw [e]
  convert h3 using 1
  simp only [Pi.mul_apply]
  ring

/-- `|2 Ai(-y) Ai'(-y)| ≤ 2` for `y ≥ 1`. -/
lemma kai_lip {y : ℝ} (hy : 1 ≤ y) : |2 * (airyAi (-y) * airyAi' (-y))| ≤ 2 := by
  have hK := airyKer_diag_neg hy
  rw [airyKer_self] at hK
  have hK1 : airyAi' (-y) ^ 2 + y * airyAi (-y) ^ 2 ≤ √y / Real.pi + 1 / y := by
    have := (abs_le.1 hK).2
    nlinarith
  have hy0 : 0 < y := by linarith
  have hs : 0 < √y := Real.sqrt_pos.2 hy0
  have hss : √y * √y = y := Real.mul_self_sqrt hy0.le
  have hs1 : 1 ≤ √y := by rw [Real.one_le_sqrt]; exact hy
  have hπ := Real.pi_gt_three
  have h1 : 2 * √y * |airyAi (-y) * airyAi' (-y)| ≤ airyAi' (-y) ^ 2 + y * airyAi (-y) ^ 2 := by
    rw [abs_mul]
    nlinarith [sq_nonneg (√y * |airyAi (-y)| - |airyAi' (-y)|), sq_abs (airyAi (-y)), sq_abs (airyAi' (-y))]
  have h2 : √y / Real.pi ≤ √y := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have h3 : 1 / y ≤ √y := by
    rw [div_le_iff₀ hy0]; nlinarith
  have h4 : 2 * √y * |airyAi (-y) * airyAi' (-y)| ≤ 2 * √y := by linarith
  have h5 : |airyAi (-y) * airyAi' (-y)| ≤ 1 := by
    have : √y * (2 * |airyAi (-y) * airyAi' (-y)|) ≤ √y * 2 := by nlinarith
    have := le_of_mul_le_mul_left this hs
    linarith
  rw [abs_mul, abs_two]
  rw [abs_mul] at h5 ⊢
  linarith

/-- `Ai²` is `2`-Lipschitz on `(-∞, -1]`. -/
lemma kai_lipschitz {s t : ℝ} (hst : s ≤ t) (ht : t ≤ -1) :
    airyAi t ^ 2 - airyAi s ^ 2 ≤ 2 * (t - s) := by
  rcases hst.eq_or_lt with h | h
  · rw [h]; simp
  have hd : ∀ x ∈ Set.Ioo s t, HasDerivAt (fun x => airyAi x ^ 2) (2 * (airyAi x * airyAi' x)) x := by
    intro x _
    have := (hasDerivAt_airyAi x).pow 2
    convert this using 1
    simp only [Nat.cast_ofNat]; ring
  obtain ⟨η, hη, he⟩ := exists_hasDerivAt_eq_slope (fun x => airyAi x ^ 2) (fun x => 2 * (airyAi x * airyAi' x)) h
    (fun x _ => by
      have := (hasDerivAt_airyAi x).pow 2
      exact this.continuousAt.continuousWithinAt) hd
  have hη1 : 1 ≤ -η := by linarith [hη.2]
  have hb := kai_lip hη1
  rw [neg_neg] at hb
  have h' : airyAi t ^ 2 - airyAi s ^ 2 = 2 * (airyAi η * airyAi' η) * (t - s) := by
    field_simp at he
    linarith
  rw [h']
  nlinarith [abs_le.1 hb, sub_pos.2 h]

/-- `Ai²` is `2`-Lipschitz on `(-∞, -1]` (reverse direction). -/
lemma kai_lipschitz_rev {s t : ℝ} (hst : s ≤ t) (ht : t ≤ -1) :
    airyAi s ^ 2 - airyAi t ^ 2 ≤ 2 * (t - s) := by
  rcases hst.eq_or_lt with h | h
  · rw [h]; simp
  have hd : ∀ x ∈ Set.Ioo s t, HasDerivAt (fun x => airyAi x ^ 2) (2 * (airyAi x * airyAi' x)) x := by
    intro x _
    have := (hasDerivAt_airyAi x).pow 2
    convert this using 1
    simp only [Nat.cast_ofNat]; ring
  obtain ⟨η, hη, he⟩ := exists_hasDerivAt_eq_slope (fun x => airyAi x ^ 2) (fun x => 2 * (airyAi x * airyAi' x)) h
    (fun x _ => by
      have := (hasDerivAt_airyAi x).pow 2
      exact this.continuousAt.continuousWithinAt) hd
  have hη1 : 1 ≤ -η := by linarith [hη.2]
  have hb := kai_lip hη1
  rw [neg_neg] at hb
  have h' : airyAi t ^ 2 - airyAi s ^ 2 = 2 * (airyAi η * airyAi' η) * (t - s) := by
    field_simp at he
    linarith
  have h'' : airyAi s ^ 2 - airyAi t ^ 2 = -(2 * (airyAi η * airyAi' η) * (t - s)) := by linarith
  rw [h'']
  nlinarith [abs_le.1 hb, sub_pos.2 h]

/-- **One step**: for `s < t ≤ -1`, `F(t) - F(s) ≤ (t - s)(Ai(s)² + 2(t - s))`. -/
lemma kai_step {s t : ℝ} (hst : s < t) (ht : t ≤ -1) :
    (t * airyAi t ^ 2 - airyAi' t ^ 2) - (s * airyAi s ^ 2 - airyAi' s ^ 2) ≤
      (t - s) * (airyAi s ^ 2 + 2 * (t - s)) := by
  obtain ⟨ξ, hξ, he⟩ := exists_hasDerivAt_eq_slope (fun x => x * airyAi x ^ 2 - airyAi' x ^ 2) (fun x => airyAi x ^ 2) hst
    (fun x _ => (kai_F_deriv x).continuousAt.continuousWithinAt) (fun x _ => kai_F_deriv x)
  have h1 : (t * airyAi t ^ 2 - airyAi' t ^ 2) - (s * airyAi s ^ 2 - airyAi' s ^ 2) = airyAi ξ ^ 2 * (t - s) := by
    field_simp at he
    linarith
  have h2 := kai_lipschitz hξ.1.le (by linarith [hξ.2])
  rw [h1]
  have h3 : airyAi ξ ^ 2 ≤ airyAi s ^ 2 + 2 * (t - s) := by
    have := kai_lipschitz (s := s) (t := ξ) hξ.1.le (by linarith [hξ.2])
    nlinarith [hξ.2]
  nlinarith [sub_pos.2 hst]

/-- **Lattice sum of `Ai²`** against the antiderivative: a lattice `X_a < ⋯ < X_{a+n} ≤ -1` with gaps in `(0, ε']`:
`ε' Σ_{i<n} Ai(X_{a+i})² ≥ F(X_{a+n}) - F(X_a) - 2ε'(X_{a+n} - X_a)`, `F = x Ai² - Ai'²`. -/
lemma kai_sum {X : ℤ → ℝ} {a : ℤ} {ε' : ℝ} (n : ℕ)
    (hgap : ∀ i : ℕ, i < n → 0 < X (a + (i + 1 : ℕ)) - X (a + (i : ℕ)) ∧ X (a + (i + 1 : ℕ)) - X (a + (i : ℕ)) ≤ ε')
    (hend : X (a + (n : ℕ)) ≤ -1) :
    (X (a + (n : ℕ)) * airyAi (X (a + (n : ℕ))) ^ 2 - airyAi' (X (a + (n : ℕ))) ^ 2) -
        (X a * airyAi (X a) ^ 2 - airyAi' (X a) ^ 2) - 2 * ε' * (X (a + (n : ℕ)) - X a) ≤
      ε' * ∑ i ∈ range n, airyAi (X (a + (i : ℕ))) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hg := hgap n (by omega)
    have hend' : X (a + (n : ℕ)) ≤ -1 := by
      have : X (a + (n : ℕ)) ≤ X (a + ((n + 1 : ℕ) : ℤ)) := by linarith [hg.1]
      linarith
    have h1 := ih (fun i hi => hgap i (by omega)) hend'
    have hst := kai_step (s := X (a + (n : ℕ))) (t := X (a + ((n + 1 : ℕ) : ℤ))) (by linarith [hg.1]) hend
    rw [Finset.sum_range_succ]
    have hA0 : 0 ≤ airyAi (X (a + (n : ℕ))) ^ 2 := sq_nonneg _
    set s := X (a + (n : ℕ)) with hs
    set t := X (a + ((n + 1 : ℕ) : ℤ)) with ht
    have hd : t - s ≤ ε' := hg.2
    have hd0 : 0 < t - s := hg.1
    have h2 : (t - s) * (airyAi s ^ 2 + 2 * (t - s)) ≤ ε' * airyAi s ^ 2 + 2 * ε' * (t - s) := by
      nlinarith [mul_le_mul_of_nonneg_right hd hA0]
    nlinarith

/-- **Lower bound for the lattice sum of `Ai²`** in terms of the Airy kernel asymptotics (`airyKer_diag_neg`): for a lattice
`X_a < ⋯ < X_{a+n} ≤ -1`, `X_a ≤ -1`, gaps in `(0, ε']`, `y_a = -X_a`, `y_b = -X_{a+n}`:
`ε' Σ_{i<n} Ai(X_{a+i})² ≥ (√y_a - √y_b)/π - 1/y_a - 1/y_b - 2ε'(y_a - y_b)`. -/
lemma kai_sum_lower {X : ℤ → ℝ} {a : ℤ} {ε' : ℝ} (n : ℕ)
    (hgap : ∀ i : ℕ, i < n → 0 < X (a + (i + 1 : ℕ)) - X (a + (i : ℕ)) ∧ X (a + (i + 1 : ℕ)) - X (a + (i : ℕ)) ≤ ε')
    (hXa : X a ≤ -1) (hend : X (a + (n : ℕ)) ≤ -1) :
    (√(-X a) - √(-X (a + (n : ℕ)))) / Real.pi - 1 / (-X a) - 1 / (-X (a + (n : ℕ))) -
        2 * ε' * (-X a + X (a + (n : ℕ))) ≤ ε' * ∑ i ∈ range n, airyAi (X (a + (i : ℕ))) ^ 2 := by
  have hs := kai_sum n hgap hend
  have h1 := airyKer_diag_neg (y := -X a) (by linarith)
  have h2 := airyKer_diag_neg (y := -X (a + (n : ℕ))) (by linarith)
  rw [neg_neg, airyKer_self] at h1 h2
  have h1' := (abs_le.1 h1).1
  have h2' := (abs_le.1 h2).2
  have e : (√(-X a) - √(-X (a + (n : ℕ)))) / Real.pi =
      √(-X a) / Real.pi - √(-X (a + (n : ℕ))) / Real.pi := by ring
  rw [e]
  nlinarith

/-- **One step, reverse**: for `s < t ≤ -1`, `F(t) - F(s) ≥ (t - s)(Ai(s)² - 2(t - s))`. -/
lemma kai_step_rev {s t : ℝ} (hst : s < t) (ht : t ≤ -1) :
    (t - s) * (airyAi s ^ 2 - 2 * (t - s)) ≤
      (t * airyAi t ^ 2 - airyAi' t ^ 2) - (s * airyAi s ^ 2 - airyAi' s ^ 2) := by
  obtain ⟨ξ, hξ, he⟩ := exists_hasDerivAt_eq_slope (fun x => x * airyAi x ^ 2 - airyAi' x ^ 2) (fun x => airyAi x ^ 2) hst
    (fun x _ => (kai_F_deriv x).continuousAt.continuousWithinAt) (fun x _ => kai_F_deriv x)
  have h1 : (t * airyAi t ^ 2 - airyAi' t ^ 2) - (s * airyAi s ^ 2 - airyAi' s ^ 2) = airyAi ξ ^ 2 * (t - s) := by
    field_simp at he
    linarith
  rw [h1]
  have h3 : airyAi s ^ 2 - 2 * (t - s) ≤ airyAi ξ ^ 2 := by
    have := kai_lipschitz_rev (s := s) (t := ξ) hξ.1.le (by linarith [hξ.2])
    nlinarith [hξ.2]
  nlinarith [sub_pos.2 hst]

/-- **Lattice sum of `Ai²`, upper form**: gaps in `[ε₀, ε']`, `X_{a+n} ≤ -1`:
`ε₀ Σ_{i<n} Ai(X_{a+i})² ≤ F(X_{a+n}) - F(X_a) + 2ε'(X_{a+n} - X_a)`, `F = x Ai² - Ai'²`. -/
lemma kai_sum_upper {X : ℤ → ℝ} {a : ℤ} {ε0 ε' : ℝ} (n : ℕ)
    (hgap : ∀ i : ℕ, i < n → ε0 ≤ X (a + (i + 1 : ℕ)) - X (a + (i : ℕ)) ∧ X (a + (i + 1 : ℕ)) - X (a + (i : ℕ)) ≤ ε')
    (hε0 : 0 < ε0) (hend : X (a + (n : ℕ)) ≤ -1) :
    ε0 * ∑ i ∈ range n, airyAi (X (a + (i : ℕ))) ^ 2 ≤
      (X (a + (n : ℕ)) * airyAi (X (a + (n : ℕ))) ^ 2 - airyAi' (X (a + (n : ℕ))) ^ 2) -
        (X a * airyAi (X a) ^ 2 - airyAi' (X a) ^ 2) + 2 * ε' * (X (a + (n : ℕ)) - X a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hg := hgap n (by omega)
    have hend' : X (a + (n : ℕ)) ≤ -1 := by
      have : X (a + (n : ℕ)) ≤ X (a + ((n + 1 : ℕ) : ℤ)) := by linarith [hg.1]
      linarith
    have h1 := ih (fun i hi => hgap i (by omega)) hend'
    have hst := kai_step_rev (s := X (a + (n : ℕ))) (t := X (a + ((n + 1 : ℕ) : ℤ))) (by linarith [hg.1]) hend
    rw [Finset.sum_range_succ]
    have hA0 : 0 ≤ airyAi (X (a + (n : ℕ))) ^ 2 := sq_nonneg _
    set s := X (a + (n : ℕ)) with hs
    set t := X (a + ((n + 1 : ℕ) : ℤ)) with ht
    have hd : t - s ≤ ε' := hg.2
    have hd0 : ε0 ≤ t - s := hg.1
    have h2 : ε0 * airyAi s ^ 2 ≤ (t - s) * (airyAi s ^ 2 - 2 * (t - s)) + 2 * ε' * (t - s) := by
      nlinarith [mul_le_mul_of_nonneg_right hd0 hA0]
    nlinarith

/-- **Upper bound for the lattice sum of `Ai²`**: `ε₀ Σ_{i<n} Ai(X_{a+i})² ≤ √y_a/π + 1/y_a + 2ε' y_a`, `y_a = -X_a ≥ 1`. -/
lemma kai_sum_upper_bound {X : ℤ → ℝ} {a : ℤ} {ε0 ε' : ℝ} (n : ℕ)
    (hgap : ∀ i : ℕ, i < n → ε0 ≤ X (a + (i + 1 : ℕ)) - X (a + (i : ℕ)) ∧ X (a + (i + 1 : ℕ)) - X (a + (i : ℕ)) ≤ ε')
    (hε0 : 0 < ε0) (hε' : 0 ≤ ε') (hXa : X a ≤ -1) (hend : X (a + (n : ℕ)) ≤ -1) :
    ε0 * ∑ i ∈ range n, airyAi (X (a + (i : ℕ))) ^ 2 ≤ √(-X a) / Real.pi + 1 / (-X a) + 2 * ε' * (-X a) := by
  have hs := kai_sum_upper n hgap hε0 hend
  have h1 := airyKer_diag_neg (y := -X a) (by linarith)
  rw [neg_neg, airyKer_self] at h1
  have h1' := (abs_le.1 h1).2
  have hb : 0 ≤ airyAi' (X (a + (n : ℕ))) ^ 2 - X (a + (n : ℕ)) * airyAi (X (a + (n : ℕ))) ^ 2 := by
    nlinarith [sq_nonneg (airyAi' (X (a + (n : ℕ)))), sq_nonneg (airyAi (X (a + (n : ℕ))))]
  have hXb : X (a + (n : ℕ)) - X a ≤ -X a := by linarith
  have := mul_le_mul_of_nonneg_left hXb (by linarith : (0 : ℝ) ≤ 2 * ε')
  nlinarith

/-- `Ai(-y)² ≤ 2/√y` for `y ≥ 1`. -/
lemma kai_sq_le {y : ℝ} (hy : 1 ≤ y) : airyAi (-y) ^ 2 ≤ 2 / √y := by
  have h1 := airyKer_diag_neg hy
  rw [airyKer_self] at h1
  have h1' := (abs_le.1 h1).2
  have hy0 : 0 < y := by linarith
  have hs : 0 < √y := Real.sqrt_pos.2 hy0
  have hss : √y * √y = y := Real.mul_self_sqrt hy0.le
  have hs1 : 1 ≤ √y := by rw [Real.one_le_sqrt]; exact hy
  have hπ := Real.pi_gt_three
  have h2 : y * airyAi (-y) ^ 2 ≤ √y / Real.pi + 1 / y := by
    nlinarith [sq_nonneg (airyAi' (-y))]
  have h3 : √y / Real.pi ≤ √y := by rw [div_le_iff₀ (by linarith)]; nlinarith
  have h4 : 1 / y ≤ 1 := by rw [div_le_one hy0]; exact hy
  have h5 : y * airyAi (-y) ^ 2 ≤ 2 * √y := by nlinarith
  rw [le_div_iff₀ hs]
  have : √y * (√y * airyAi (-y) ^ 2) ≤ √y * 2 := by nlinarith
  nlinarith [le_of_mul_le_mul_left this hs]

/-- info: 'FormalResearch.Special.kai_sum_upper_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.kai_sum_upper_bound

/-- info: 'FormalResearch.Special.kai_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.kai_sq_le

/-- info: 'FormalResearch.Special.kai_sum_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.kai_sum_lower

end FormalResearch.Special
