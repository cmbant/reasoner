module

public import FormalResearch.Special.DiscreteAiryKappaAiSum
public import FormalResearch.Special.AiryEnvelopeReal

/-!
# Order-sharp upper bound for `κ`, abstract part (plan K1, steps 1-2)

For a lattice `X_J ≤ ⋯ ≤ X_m` with gaps in `[ε₀, ε']` crossing the oscillatory region (`X_J ≤ -s²`, `X_m ≥ 0`), `kk_lat` selects the sub-lattice
`-s² < X_{k_a} < ⋯ < X_{k_a+n} ≤ -1` on which `ε' Σ Ai(X_k)² ≥ s/20` (from `kai_sum_lower`, i.e. from the Airy kernel
asymptotics `airyKer_diag_neg`) and `n ε₀ ≤ s²`.  `kk_ub_abs` turns this into a mass bound for any sequence `Y = κ g Ai(X) + rest`:

`gmin² s/(40 ε') · κ² ≤ N + s² ρ²/ε₀`  if `|rest_k| ≤ ρ`, `g ≥ gmin`, and every finite lattice sum of `Y²` is `≤ N`.

For the actual `3j` chain, `X_k` has gaps `≍ δ = N^{-1/3}` (`c₁δ, c₂δ`), `X_J ≍ -δ^{-2}`, `s ≍ δ^{-1}`, so `κ² ≲ N · δ ε'/s ≍ N^{1/3}`.

**Claim class: proved** (abstract, Airy-kernel input only).
-/

@[expose] public section

open Finset

namespace FormalResearch.Special

/-- **Discrete intermediate value**: `X_J ≤ t < X_b` gives an index `k ∈ [J, b)` with `X_k ≤ t < X_{k+1}`. -/
lemma kk_ivt {X : ℤ → ℝ} {J b : ℤ} {t : ℝ} (hJ : X J ≤ t) (hb : t < X b) (hJb : J ≤ b) :
    ∃ k : ℤ, J ≤ k ∧ k < b ∧ X k ≤ t ∧ t < X (k + 1) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = b - J := ⟨(b - J).toNat, Int.toNat_of_nonneg (by omega)⟩
  have key : ∀ n : ℕ, t < X (J + (n : ℤ)) → ∃ k : ℤ, J ≤ k ∧ k < J + (n : ℤ) ∧ X k ≤ t ∧ t < X (k + 1) := by
    intro n
    induction n with
    | zero => intro h; simp at h; linarith
    | succ n ih =>
      intro h
      by_cases h1 : t < X (J + (n : ℤ))
      · obtain ⟨k, hk1, hk2, hk3, hk4⟩ := ih h1
        exact ⟨k, hk1, by push_cast; omega, hk3, hk4⟩
      · push Not at h1
        exact ⟨J + (n : ℤ), by omega, by push_cast; omega, h1, by
          have e : J + ((n + 1 : ℕ) : ℤ) = J + (n : ℤ) + 1 := by push_cast; ring
          rw [e] at h; exact h⟩
  have := key n (by rw [hn]; simpa using hb)
  obtain ⟨k, h1, h2, h3, h4⟩ := this
  exact ⟨k, h1, by omega, h3, h4⟩

/-- The numerical core: `√y_a ≥ s - 1`, etc. -/
lemma kk_num {s ε' ya yb : ℝ} (hs : 100 ≤ s) (hε0 : 0 < ε') (hε : ε' * s ≤ 1 / 20)
    (hya1 : s ^ 2 - 1 ≤ ya) (hya2 : ya ≤ s ^ 2) (hyb1 : 1 ≤ yb) (hyb2 : yb ≤ 2) :
    s / 20 ≤ (√ya - √yb) / Real.pi - 1 / ya - 1 / yb - 2 * ε' * (ya - yb) := by
  have hπ1 := Real.pi_gt_three
  have hπ2 := Real.pi_lt_d2
  have hs0 : 0 < s := by linarith
  have h1 : s - 1 ≤ √ya := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have h2 : √yb ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith
  have h3 : 1 / ya ≤ 1 / 100 := by
    rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]; nlinarith
  have h4 : 1 / yb ≤ 1 := by
    rw [div_le_one (by linarith)]; exact hyb1
  have h5 : 2 * ε' * (ya - yb) ≤ s / 10 := by
    have : ya - yb ≤ s ^ 2 := by linarith
    have h6 : 2 * ε' * (ya - yb) ≤ 2 * ε' * s ^ 2 := mul_le_mul_of_nonneg_left this (by positivity)
    have h7 : 2 * ε' * s ^ 2 = 2 * (ε' * s) * s := by ring
    nlinarith
  have h6 : (s - 5 / 2) / Real.pi ≤ (√ya - √yb) / Real.pi :=
    div_le_div_of_nonneg_right (by linarith) Real.pi_pos.le
  have h7 : s * (3 / 10) - 3 / 4 ≤ (s - 5 / 2) / Real.pi := by
    rw [le_div_iff₀ Real.pi_pos]
    nlinarith
  linarith

/-- **Sub-lattice on which `Ai²` sums to `≳ s/ε'`.**  `X_J ≤ -s²`, `X_m ≥ 0`, gaps in `[ε₀, ε']` on `[J, m)`, `ε' s ≤ 1/20`, `s ≥ 100`. -/
lemma kk_lat {X : ℤ → ℝ} {J m : ℤ} {ε0 ε' s : ℝ} (hJm : J ≤ m) (hε0 : 0 < ε0) (hε' : 0 < ε') (hε1 : ε' ≤ 1) (hε : ε' * s ≤ 1 / 20)
    (hgap : ∀ k : ℤ, J ≤ k → k < m → ε0 ≤ X (k + 1) - X k ∧ X (k + 1) - X k ≤ ε') (hXm : 0 ≤ X m)
    (hs : 100 ≤ s) (hXJ : X J ≤ -(s ^ 2)) :
    ∃ (ka : ℤ) (n : ℕ), J ≤ ka ∧ ka + (n : ℤ) ≤ m ∧
      s / 20 ≤ ε' * ∑ i ∈ range n, airyAi (X (ka + (i : ℤ))) ^ 2 ∧ (n : ℝ) * ε0 ≤ s ^ 2 := by
  have hs0 : 0 < s := by linarith
  have hs2 : 1 ≤ s ^ 2 := by nlinarith
  -- the upper end
  obtain ⟨kb, hkb1, hkb2, hkb3, hkb4⟩ := kk_ivt (X := X) (t := -1) (by linarith) (by linarith) hJm
  have hXb1 : -1 - ε' < X kb := by
    have := (hgap kb hkb1 hkb2).2
    linarith
  -- the lower end
  obtain ⟨k', hk'1, hk'2, hk'3, hk'4⟩ := kk_ivt (X := X) (t := -(s ^ 2)) hXJ (by nlinarith) hkb1
  set ka : ℤ := k' + 1 with hka
  have hka1 : J ≤ ka := by omega
  have hka2 : ka ≤ kb := by omega
  have hXa2 : X ka ≤ -(s ^ 2) + ε' := by
    have := (hgap k' hk'1 (by omega)).2
    linarith
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = kb - ka := ⟨(kb - ka).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hkbn : ka + (n : ℤ) = kb := by omega
  have hgap' : ∀ i : ℕ, i < n → 0 < X (ka + ((i + 1 : ℕ) : ℤ)) - X (ka + (i : ℤ)) ∧
      X (ka + ((i + 1 : ℕ) : ℤ)) - X (ka + (i : ℤ)) ≤ ε' := by
    intro i hi
    have h := hgap (ka + (i : ℤ)) (by omega) (by omega)
    have e : ka + ((i + 1 : ℕ) : ℤ) = ka + (i : ℤ) + 1 := by push_cast; ring
    rw [e]
    exact ⟨by linarith [h.1], h.2⟩
  have hXa : X ka ≤ -1 := by nlinarith
  have hend : X (ka + (n : ℤ)) ≤ -1 := by rw [hkbn]; exact hkb3
  have hL := kai_sum_lower n hgap' hXa hend
  rw [hkbn] at hL
  have hnum := kk_num (s := s) (ε' := ε') (ya := -X ka) (yb := -X kb) hs hε' hε
    (by linarith) (by nlinarith) (by linarith) (by linarith)
  refine ⟨ka, n, hka1, by omega, by linarith, ?_⟩
  -- count
  have hcount : ∀ j : ℕ, j ≤ n → (j : ℝ) * ε0 ≤ X (ka + (j : ℤ)) - X ka := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      have h2 := (hgap (ka + (j : ℤ)) (by omega) (by omega)).1
      have e : ka + ((j + 1 : ℕ) : ℤ) = ka + (j : ℤ) + 1 := by push_cast; ring
      rw [e]; push_cast; linarith
  have := hcount n le_rfl
  rw [hkbn] at this
  nlinarith

/-- **The mass bound** for `Y = κ g Ai(X) + rest`: with `g ≥ g_min`, `|rest| ≤ ρ` on the window and every lattice sum of `Y²` at most `N`,
`g_min² s/(40 ε') κ² ≤ N + s² ρ²/ε₀`. -/
lemma kk_ub_abs {X Y g : ℤ → ℝ} {J m : ℤ} {ε0 ε' s κ ρ gmin N : ℝ} (hJm : J ≤ m) (hε0 : 0 < ε0) (hε' : 0 < ε') (hε1 : ε' ≤ 1)
    (hε : ε' * s ≤ 1 / 20) (hgap : ∀ k : ℤ, J ≤ k → k < m → ε0 ≤ X (k + 1) - X k ∧ X (k + 1) - X k ≤ ε')
    (hXm : 0 ≤ X m) (hs : 100 ≤ s) (hXJ : X J ≤ -(s ^ 2))
    (hg : ∀ k : ℤ, J ≤ k → k ≤ m → gmin ≤ g k) (hgmin : 0 < gmin)
    (hrest : ∀ k : ℤ, J ≤ k → k ≤ m → |Y k - κ * (g k * airyAi (X k))| ≤ ρ)
    (hmass : ∀ (ka : ℤ) (n : ℕ), ∑ i ∈ range n, Y (ka + (i : ℤ)) ^ 2 ≤ N) :
    gmin ^ 2 * s / (40 * ε') * κ ^ 2 ≤ N + s ^ 2 * ρ ^ 2 / ε0 := by
  obtain ⟨ka, n, hka, hkn, hS, hn⟩ := kk_lat hJm hε0 hε' hε1 hε hgap hXm hs hXJ
  have hpt : ∀ i ∈ range n, (1 / 2) * (κ ^ 2 * gmin ^ 2 * airyAi (X (ka + (i : ℤ))) ^ 2) - ρ ^ 2 ≤ Y (ka + (i : ℤ)) ^ 2 := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    have hr := hrest (ka + (i : ℤ)) (by omega) (by omega)
    have hgi := hg (ka + (i : ℤ)) (by omega) (by omega)
    set A : ℝ := κ * (g (ka + (i : ℤ)) * airyAi (X (ka + (i : ℤ)))) with hA
    have h1 : (Y (ka + (i : ℤ)) - A) ^ 2 ≤ ρ ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hr 2
    have h2 : κ ^ 2 * gmin ^ 2 * airyAi (X (ka + (i : ℤ))) ^ 2 ≤ A ^ 2 := by
      have : A ^ 2 = κ ^ 2 * g (ka + (i : ℤ)) ^ 2 * airyAi (X (ka + (i : ℤ))) ^ 2 := by rw [hA]; ring
      rw [this]
      have : gmin ^ 2 ≤ g (ka + (i : ℤ)) ^ 2 := pow_le_pow_left₀ hgmin.le hgi 2
      have h3 : 0 ≤ κ ^ 2 * airyAi (X (ka + (i : ℤ))) ^ 2 := by positivity
      nlinarith
    nlinarith [sq_nonneg (Y (ka + (i : ℤ)) - A + (Y (ka + (i : ℤ)) - A) - Y (ka + (i : ℤ))), sq_nonneg (Y (ka + (i : ℤ)) + (Y (ka + (i : ℤ)) - A))]
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hm := hmass ka n
  have hSAi : s / 20 / ε' ≤ ∑ i ∈ range n, airyAi (X (ka + (i : ℤ))) ^ 2 := by
    rw [div_le_iff₀ hε']; linarith
  have h5 : κ ^ 2 * gmin ^ 2 * (s / 20 / ε') ≤ κ ^ 2 * gmin ^ 2 * ∑ i ∈ range n, airyAi (X (ka + (i : ℤ))) ^ 2 :=
    mul_le_mul_of_nonneg_left hSAi (by positivity)
  have h6 : (n : ℝ) * ρ ^ 2 ≤ s ^ 2 * ρ ^ 2 / ε0 := by
    rw [le_div_iff₀ hε0]
    nlinarith [sq_nonneg ρ, mul_le_mul_of_nonneg_right hn (sq_nonneg ρ)]
  have e : gmin ^ 2 * s / (40 * ε') * κ ^ 2 = (1 / 2) * (κ ^ 2 * gmin ^ 2 * (s / 20 / ε')) := by
    field_simp; ring
  rw [e]
  nlinarith

/-- info: 'FormalResearch.Special.kk_ub_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.kk_ub_abs



/-- Span of a lattice with gaps `≥ ε₀`: `(m - J) ε₀ ≤ X_m - X_J`. -/
lemma kk_span {X : ℤ → ℝ} {J m : ℤ} {ε0 : ℝ} (hJm : J ≤ m)
    (hgap : ∀ k : ℤ, J ≤ k → k < m → ε0 ≤ X (k + 1) - X k) : ((m - J : ℤ) : ℝ) * ε0 ≤ X m - X J := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = m - J := ⟨(m - J).toNat, Int.toNat_of_nonneg (by omega)⟩
  have key : ∀ n : ℕ, J + (n : ℤ) ≤ m → (n : ℝ) * ε0 ≤ X (J + (n : ℤ)) - X J := by
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

/-- **Upper bound `κ² δ ≤ 80 c₂/(g_min² σ₀)`**, abstract form for the Airy window of the `3j` chain (`δ³ = 1/N`).  Lattice gaps in
`[c₁δ, c₂δ]` on `[J, m)`, `0 ≤ X_m`, `(m - J)δ³ ≥ r - δ³`, `g ≥ g_min`, `|Y - κ g Ai(X)| ≤ (C+1) δ³ |κ|` on `[J, m]`, every lattice sum
of `Y²` at most `N = δ^{-3}`; `σ₀ = min(√(3c₁r/4), 1/(20c₂))`; `δ` small. -/
lemma kk_ub_final {X Y g : ℤ → ℝ} {J m : ℤ} {δ c1 c2 r gmin C κ σ0 : ℝ} (hJm : J ≤ m) (hδ : 0 < δ) (hc1 : 0 < c1)
    (hc12 : c1 ≤ c2) (hr : 0 < r) (hgmin : 0 < gmin) (hC : 0 < C)
    (hσ0 : σ0 = min (√(3 * c1 * r / 4)) (1 / (20 * c2)))
    (hδ3 : δ ^ 3 ≤ r / 8) (hδc : c2 * δ ^ 3 ≤ c1 * r / 8) (hδσ : 100 * δ ≤ σ0)
    (hδ5 : δ ^ 5 ≤ gmin ^ 2 * c1 / (80 * c2 * σ0 * (C + 1) ^ 2))
    (hgap : ∀ k : ℤ, J ≤ k → k < m → c1 * δ ≤ X (k + 1) - X k ∧ X (k + 1) - X k ≤ c2 * δ)
    (hXm : 0 ≤ X m ∧ X m ≤ c2 * δ) (hpos : r - δ ^ 3 ≤ ((m - J : ℤ) : ℝ) * δ ^ 3)
    (hg : ∀ k : ℤ, J ≤ k → k ≤ m → gmin ≤ g k)
    (hrest : ∀ k : ℤ, J ≤ k → k ≤ m → |Y k - κ * (g k * airyAi (X k))| ≤ (C + 1) * δ ^ 3 * |κ|)
    (hmass : ∀ (ka : ℤ) (n : ℕ), ∑ i ∈ range n, Y (ka + (i : ℤ)) ^ 2 ≤ 1 / δ ^ 3) :
    κ ^ 2 * δ ≤ 80 * c2 / (gmin ^ 2 * σ0) := by
  have hc2 : 0 < c2 := lt_of_lt_of_le hc1 hc12
  have hσ0p : 0 < σ0 := by
    rw [hσ0]; exact lt_min (Real.sqrt_pos.2 (by positivity)) (by positivity)
  have hσ1 : σ0 ≤ 1 / (20 * c2) := hσ0 ▸ min_le_right _ _
  have hσ2 : σ0 ^ 2 ≤ 3 * c1 * r / 4 := by
    have := (hσ0 ▸ min_le_left _ _ : σ0 ≤ √(3 * c1 * r / 4))
    calc σ0 ^ 2 ≤ √(3 * c1 * r / 4) ^ 2 := pow_le_pow_left₀ hσ0p.le this 2
      _ = 3 * c1 * r / 4 := Real.sq_sqrt (by positivity)
  have hδ0 : 0 < δ ^ 3 := by positivity
  -- X_J
  have hspan := kk_span (X := X) (ε0 := c1 * δ) hJm (fun k h1 h2 => (hgap k h1 h2).1)
  have hXJ : X J ≤ -((σ0 / δ) ^ 2) := by
    have h1 : ((m - J : ℤ) : ℝ) * (c1 * δ) ≥ c1 * (r - δ ^ 3) / δ ^ 2 := by
      have : (r - δ ^ 3) ≤ ((m - J : ℤ) : ℝ) * δ ^ 3 := hpos
      rw [ge_iff_le, div_le_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left this hc1.le]
    have h2 : (σ0 / δ) ^ 2 + c2 * δ ≤ c1 * (r - δ ^ 3) / δ ^ 2 := by
      have e : (σ0 / δ) ^ 2 + c2 * δ = (σ0 ^ 2 + c2 * δ ^ 3) / δ ^ 2 := by field_simp
      rw [e]
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [mul_le_mul_of_nonneg_left hδ3 hc1.le]
    linarith [hXm.2]
  have hε1 : c2 * δ ≤ 1 := by
    have : 100 * δ ≤ 1 / (20 * c2) := hδσ.trans hσ1
    rw [le_div_iff₀ (by positivity)] at this
    nlinarith
  have hε : c2 * δ * (σ0 / δ) ≤ 1 / 20 := by
    have : c2 * δ * (σ0 / δ) = c2 * σ0 := by field_simp
    rw [this]
    have := mul_le_mul_of_nonneg_left hσ1 hc2.le
    calc c2 * σ0 ≤ c2 * (1 / (20 * c2)) := this
      _ = 1 / 20 := by field_simp
  have hs : 100 ≤ σ0 / δ := by rw [le_div_iff₀ hδ]; linarith
  have H := kk_ub_abs (X := X) (Y := Y) (g := g) (J := J) (m := m) (ε0 := c1 * δ) (ε' := c2 * δ) (s := σ0 / δ)
    (κ := κ) (ρ := (C + 1) * δ ^ 3 * |κ|) (gmin := gmin) (N := 1 / δ ^ 3) hJm (by positivity) (by positivity) hε1 hε
    hgap hXm.1 hs hXJ hg hgmin hrest hmass
  set A : ℝ := gmin ^ 2 * σ0 / (40 * c2) with hA
  have hA0 : 0 < A := by positivity
  set B : ℝ := σ0 ^ 2 * (C + 1) ^ 2 / c1 with hB
  have e1 : gmin ^ 2 * (σ0 / δ) / (40 * (c2 * δ)) * κ ^ 2 = A * (κ ^ 2 * δ) / δ ^ 3 := by
    rw [hA]; field_simp
  have e2 : (σ0 / δ) ^ 2 * ((C + 1) * δ ^ 3 * |κ|) ^ 2 / (c1 * δ) = B * (κ ^ 2 * δ) * δ ^ 2 := by
    rw [hB, mul_pow, mul_pow, sq_abs]; field_simp
  rw [e1, e2] at H
  set P : ℝ := κ ^ 2 * δ with hP
  have hP0 : 0 ≤ P := by positivity
  have hBδ : B * δ ^ 5 ≤ A / 2 := by
    calc B * δ ^ 5 ≤ B * (gmin ^ 2 * c1 / (80 * c2 * σ0 * (C + 1) ^ 2)) :=
          mul_le_mul_of_nonneg_left hδ5 (by positivity)
      _ = A / 2 := by rw [hB, hA]; field_simp; norm_num
  have H2 : A * P ≤ 1 + A / 2 * P := by
    have h3 := mul_le_mul_of_nonneg_right H (pow_pos hδ 3).le
    have e3 : A * P / δ ^ 3 * δ ^ 3 = A * P := by field_simp
    have e4 : (1 / δ ^ 3 + B * P * δ ^ 2) * δ ^ 3 = 1 + B * δ ^ 5 * P := by field_simp
    rw [e3, e4] at h3
    linarith [mul_le_mul_of_nonneg_right hBδ hP0]
  have h5 : P ≤ 2 / A := by
    rw [le_div_iff₀ hA0]; linarith
  calc P ≤ 2 / A := h5
    _ = 80 * c2 / (gmin ^ 2 * σ0) := by rw [hA]; field_simp; ring

/-- info: 'FormalResearch.Special.kk_ub_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.kk_ub_final

end FormalResearch.Special
