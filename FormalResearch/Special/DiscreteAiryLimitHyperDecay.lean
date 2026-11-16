module

public import FormalResearch.Special.DiscreteAiryLimitHahn

/-!
# Hard-edge monotone decay beyond the turn for the closed-form Hahn / centred Racah chains

Source: Weyl P3 `weyl_midpoint_semiclassics.tex`, `prop:forbidden-decay`(a) (T:1008) and `rem:airy2-R`(b) (T:965): a solution of the
Jacobi recurrence that satisfies the hard-edge row (`A_{k_max+1} = 0`) of an *exactly hyperbolic* chain
(`A_k + A_{k+1} ≤ c_k`, `prop:exact-hyperbolicity`) is nonzero and `|Y_{k+1}| ≤ |Y_k|` from the turn to the hard edge.
This module formalises that step for the closed forms `hrAk`, `hrCk` of `DiscreteAiryLimitHahn`, by combining
`backward_ratio` and `exact_hyperbolicity_hahn_racah` (`Racah/P3JacobiComparison`).  It is the input that discharges hypothesis `(R)`
of `discrete_airy_hahn_racah(_window)` in `DiscreteAiryLimitHyperWindow`.

## What is proved (claim class: **proved**; pure real-inequality arguments, no hypothesis beyond those stated)

* `hd_zero_backward`, `hd_backward_decay`: abstract version for any `A, c, Y : ℕ → ℝ` with `A_i > 0` on `[j, N]`,
  `A_{N+1} = 0`, `A_i + A_{i+1} ≤ c_i`, rows `A_{i+1}Y_{i+1} + A_iY_{i-1} = c_iY_i` on `[j, N]`:
  `|Y_k| ≤ |Y_{j-1}|` for all `j-1 ≤ k ≤ N` (this is `backward_ratio` with `y = 1`, plus the degenerate case `Y_N = 0`,
  where the recurrence forces `Y ≡ 0` on `[j-1, N]`; `backward_ratio` assumes `Y_N ≠ 0`).
* `hr_Ak_pos`: `A_i = ½ r_i ẽ((ih)²) > 0` for `max(|a|,|b|) < i ≤ k_max` when `((k_max+1)h)² ∈ Dom` (positivity of the
  coefficients on the chain).
* `hr_hardedge_decay`: for the closed-form chain `jac (hrAk …) (hrCk …) Y = 0` on the rows `[k₁+1, k_max]` with the hard edge
  `ẽ(((k_max+1)h)²) = 0`, `((k_max+1)h)² ∈ Dom`, and `(k₁+½)h ≥ q_*` (the site `k₁` is at or beyond the turn):
  `|Y_k| ≤ |Y_{k₁}|` for all `k₁ ≤ k ≤ k_max`.  Hypotheses: the simple-turn hypotheses of `exact_hyperbolicity_hahn_racah`
  (`Φ(q_*²) = 0`, `τ² = 1`, `1 - τx > 0`, `q_* > 0`) and two smallness conditions on `h`:
  `2 M h ≤ q_*` (`M = max(1,|a|,|b|)`, so that the rank is above `|a|, |b|`) and
  `h (ρ₁+ρ₂) ≤ 2κ q_*` (`hrRho`, `κ = (1-τx)/q_*²`; this is the gap condition `q_k - q_* ≥ C₀h²` of `prop:exact-hyperbolicity`
  at every site `k ≥ k₁ + 1`, i.e. one lattice spacing past `q_*`).

## Numerical check (mpmath, 30 digits; `explore`-level evidence, not part of the proof)

Hahn closed forms `P = 1`, `Q = 0`, `τ = 1`, `a = b = ½`, `x = 0.6`, `q_* = 0.8`, `h = 1/N`, `k_max = N-1`, `A_k = ½ r_k √(1-(kh)²)`,
`c_k = x - ab/(k(k+1))`, solution started backward from `Y_{k_max} = 1`: for `N = 100, 400, 1600, 6400` the last index with
`A_k + A_{k+1} > c_k` has `q_k = 0.795, 0.79875, 0.7996875, 0.79992` (all `< q_*`, within `h` of the turn), the last index with
`|Y_{k+1}| > |Y_k|` has `q_k = 0.765, 0.786, 0.795, 0.798` (`< q_*`), and `max_{k ≥ m} |Y_k| / |Y_m| = 1` for `m` the first
site `≥ q_*`.

## Not formalised

The identification of the closed forms with the actual `3j`/`6j` chains and of the actual hard-edge row `k_max` is in
`DiscreteAiryLimitChains*` (not here); the
normalisation of `Y` (a bound on `|Y_{k₁}|` is *not* derived here: the decay goes from `k₁` forward, so a bound at the end of
the chain does not control `Y` at `k₁`); the quantum-`6j` (`sinh/cosh`) variant; the sharper exponential decay of
`prop:forbidden-decay`(b).
-/

@[expose] public section

open FormalResearch.Racah.P3 FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- Zero propagation from the hard edge: if `Y_N = 0` then the recurrence with `A_i > 0` and `A_{N+1} = 0`
forces `Y_i = 0` on `[j-1, N]`. -/
lemma hd_zero_backward (A c Y : ℕ → ℝ) (j N : ℕ) (hj : 1 ≤ j)
    (hA : ∀ i, j ≤ i → i ≤ N → 0 < A i) (hend : A (N + 1) = 0)
    (hrow : ∀ i, j ≤ i → i ≤ N → A (i + 1) * Y (i + 1) + A i * Y (i - 1) = c i * Y i)
    (hYN : Y N = 0) : ∀ i, j - 1 ≤ i → i ≤ N → Y i = 0 := by
  have key : ∀ d, d + j ≤ N + 1 → Y (N - d) = 0 ∧ A (N - d + 1) * Y (N - d + 1) = 0 := by
    intro d
    induction d with
    | zero => intro _; simp [hYN, hend]
    | succ d ih =>
      intro hd
      obtain ⟨h1, h2⟩ := ih (by omega)
      have hi : j ≤ N - d := by omega
      have hiN : N - d ≤ N := by omega
      have row := hrow (N - d) hi hiN
      have hAi := hA (N - d) hi hiN
      rw [h1, mul_zero] at row
      have h3 : A (N - d) * Y (N - d - 1) = 0 := by linarith
      have h4 : Y (N - d - 1) = 0 := (mul_eq_zero.1 h3).resolve_left hAi.ne'
      have e1 : N - (d + 1) = N - d - 1 := by omega
      have e2 : N - (d + 1) + 1 = N - d := by omega
      refine ⟨by rw [e1]; exact h4, ?_⟩
      rw [e2, h1, mul_zero]
  intro i hi1 hiN
  have := (key (N - i) (by omega)).1
  have e : N - (N - i) = i := by omega
  rwa [e] at this

/-- **Monotone decay to the hard edge** (`prop:forbidden-decay`(a), including the degenerate case `Y_N = 0`):
`A_i > 0` on `[j, N]`, `A_{N+1} = 0`, `A_i + A_{i+1} ≤ c_i` and the rows `A_{i+1}Y_{i+1} + A_iY_{i-1} = c_iY_i` on `[j, N]`
imply `|Y_k| ≤ |Y_{j-1}|` for `j - 1 ≤ k ≤ N`. -/
theorem hd_backward_decay (A c Y : ℕ → ℝ) (j N : ℕ) (hj : 1 ≤ j) (hjN : j ≤ N)
    (hA : ∀ i, j ≤ i → i ≤ N → 0 < A i) (hend : A (N + 1) = 0)
    (hsup : ∀ i, j ≤ i → i ≤ N → A (i + 1) + A i ≤ c i)
    (hrow : ∀ i, j ≤ i → i ≤ N → A (i + 1) * Y (i + 1) + A i * Y (i - 1) = c i * Y i) :
    ∀ k, j - 1 ≤ k → k ≤ N → |Y k| ≤ |Y (j - 1)| := by
  by_cases hYN : Y N = 0
  · intro k hk1 hkN
    rw [hd_zero_backward A c Y j N hj hA hend hrow hYN k hk1 hkN,
      hd_zero_backward A c Y j N hj hA hend hrow hYN (j - 1) le_rfl (by omega)]
  · have hbr := backward_ratio A c Y j N 1 one_pos hj hjN hA hend
      (fun i h1 h2 => by simpa using hsup i h1 h2) hrow hYN
    have mono : ∀ d, j - 1 + d ≤ N → |Y (j - 1 + d)| ≤ |Y (j - 1)| := by
      intro d
      induction d with
      | zero => intro _; simp
      | succ d ih =>
        intro hd
        have h1 := ih (by omega)
        have h2 := (hbr (j - 1 + d) (by omega) (by omega)).2 (by omega)
        rw [one_mul] at h2
        have e : j - 1 + (d + 1) = j - 1 + d + 1 := by omega
        rw [e]; linarith
    intro k hk1 hkN
    have := mono (k - (j - 1)) (by omega)
    have e : j - 1 + (k - (j - 1)) = k := by omega
    rwa [e] at this

/-- The constant `ρ₁ + ρ₂` of `exact_hyperbolicity_hahn_racah` (`A:1352-1353`). -/
noncomputable def hrRho (P Q a b qs : ℝ) : ℝ :=
  4 * (a ^ 2 + b ^ 2 + 1 / 3) / qs ^ 2 +
    (Real.sqrt (P * Q) * (1 + 2 * (a ^ 2 + b ^ 2)) / 4 + 4 * |a * b| / qs ^ 2)

/-- Positivity of the off-diagonal coefficients on the chain: `A_i > 0` for `max(|a|,|b|) < i ≤ k_max`
when the hard-edge site `((k_max+1)h)²` lies in the domain. -/
lemma hr_Ak_pos {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) {a b h : ℝ} (hh : 0 < h) {i kmax : ℕ} (hik : i ≤ kmax)
    (hi : 1 ≤ (i : ℝ)) (ha : a ^ 2 < (i : ℝ) ^ 2) (hb : b ^ 2 < (i : ℝ) ^ 2)
    (hedge : (((kmax : ℝ) + 1) * h) ^ 2 ∈ Dom P Q) : 0 < hrAk P Q a b h (i : ℤ) := by
  unfold hrAk
  simp only [Int.cast_natCast]
  have hi2 : 0 < (i : ℝ) ^ 2 := by positivity
  have hrr : 0 < rr a b (i : ℝ) := by
    unfold rr
    refine Real.sqrt_pos.2 (div_pos (mul_pos ?_ ?_) ?_)
    · exact sub_pos.2 ((div_lt_one hi2).2 ha)
    · exact sub_pos.2 ((div_lt_one hi2).2 hb)
    · exact sub_pos.2 ((div_lt_one (by positivity)).2 (by nlinarith))
  have hik' : (i : ℝ) ≤ kmax := Nat.cast_le.2 hik
  have hlt : ((i : ℝ) * h) ^ 2 < (((kmax : ℝ) + 1) * h) ^ 2 :=
    pow_lt_pow_left₀ (mul_lt_mul_of_pos_right (by linarith) hh) (by positivity) two_ne_zero
  have hP1 : 0 < 1 - P * ((i : ℝ) * h) ^ 2 := by
    rcases hP.eq_or_lt with h0 | h0
    · simp [← h0]
    · have := mul_lt_mul_of_pos_left hlt h0
      nlinarith [hedge.2.1]
  have hQ1 : 0 < 1 - Q * ((i : ℝ) * h) ^ 2 := by
    rcases hQ.eq_or_lt with h0 | h0
    · simp [← h0]
    · have := mul_lt_mul_of_pos_left hlt h0
      nlinarith [hedge.2.2]
  have het : 0 < etilde P Q (((i : ℝ) * h) ^ 2) := by
    unfold etilde
    exact Real.sqrt_pos.2 (mul_pos hP1 hQ1)
  exact mul_pos (mul_pos (by norm_num) hrr) het

/-- **Hard-edge monotone decay beyond the turn for the closed-form Hahn / centred Racah chains** (`prop:forbidden-decay`(a)
with `prop:exact-hyperbolicity`; see the module docstring).  Let `Y` satisfy the rows `jac (hrAk …) (hrCk …) Y k = 0` for
`k ∈ [k₁+1, k_max]`, with hard edge `ẽ(((k_max+1)h)²) = 0`, `((k_max+1)h)² ∈ Dom`, and `q_* ≤ (k₁+½)h`.  If
`2 M h ≤ q_*` and `h (ρ₁+ρ₂) ≤ 2κq_*`, then `|Y_k| ≤ |Y_{k₁}|` for `k₁ ≤ k ≤ k_max`. -/
theorem hr_hardedge_decay {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (a b τ x qs h : ℝ) (hqs : 0 < qs)
    (hh : 0 < h) (hτ : τ ^ 2 = 1) (hκ : 0 < 1 - τ * x) (hturn : Phi P Q τ x (qs ^ 2) = 0)
    (hhM : h * (2 * hrM a b) ≤ qs)
    (hhC : h * hrRho P Q a b qs ≤ 2 * ((1 - τ * x) / qs ^ 2) * qs)
    (kmax k1 : ℕ) (hedge : (((kmax : ℝ) + 1) * h) ^ 2 ∈ Dom P Q)
    (hedge0 : etilde P Q ((((kmax : ℝ) + 1) * h) ^ 2) = 0)
    (hk1 : qs ≤ ((k1 : ℝ) + 1 / 2) * h) (hk1k : k1 ≤ kmax) (Y : ℤ → ℝ)
    (hY : ∀ k ∈ Finset.Icc ((k1 : ℤ) + 1) (kmax : ℤ),
      jac (hrAk P Q a b h) (hrCk P Q τ x a b h) Y k = 0) :
    ∀ k : ℤ, (k1 : ℤ) ≤ k → k ≤ kmax → |Y k| ≤ |Y k1| := by
  rcases hk1k.eq_or_lt with hEq | hlt
  · intro k hk1' hk2
    have : k = k1 := by omega
    rw [this]
  have hM1 : 1 ≤ hrM a b := le_max_left _ _
  have hMa : |a| ≤ hrM a b := (le_max_left _ _).trans (le_max_right _ _)
  have hMb : |b| ≤ hrM a b := (le_max_right _ _).trans (le_max_right _ _)
  -- the facts at every row site `i ∈ [k₁+1, k_max]`
  have hfacts : ∀ i : ℕ, k1 + 1 ≤ i → 1 ≤ (i : ℝ) ∧ a ^ 2 < (i : ℝ) ^ 2 ∧ b ^ 2 < (i : ℝ) ^ 2 ∧
      qs + h ≤ ((i : ℝ) + 1 / 2) * h := by
    intro i hi
    have hik : ((k1 : ℝ) + 1) ≤ (i : ℝ) := by exact_mod_cast hi
    have hqh : qs + h ≤ ((i : ℝ) + 1 / 2) * h := by
      nlinarith [mul_le_mul_of_nonneg_right hik hh.le]
    have h2M : 2 * hrM a b ≤ (i : ℝ) + 1 / 2 := by
      have : 2 * hrM a b * h ≤ ((i : ℝ) + 1 / 2) * h := by nlinarith
      exact le_of_mul_le_mul_right this hh
    have hiM : hrM a b < (i : ℝ) := by linarith
    refine ⟨by linarith, ?_, ?_, hqh⟩
    · have : |a| < (i : ℝ) := lt_of_le_of_lt hMa hiM
      have := pow_lt_pow_left₀ this (abs_nonneg a) two_ne_zero
      rwa [sq_abs] at this
    · have : |b| < (i : ℝ) := lt_of_le_of_lt hMb hiM
      have := pow_lt_pow_left₀ this (abs_nonneg b) two_ne_zero
      rwa [sq_abs] at this
  have hA : ∀ i, k1 + 1 ≤ i → i ≤ kmax → 0 < (fun n : ℕ => hrAk P Q a b h (n : ℤ)) i := by
    intro i hi1 hi2
    obtain ⟨f1, f2, f3, -⟩ := hfacts i hi1
    exact hr_Ak_pos hP hQ hh hi2 f1 f2 f3 hedge
  have hend : (fun n : ℕ => hrAk P Q a b h (n : ℤ)) (kmax + 1) = 0 := by
    show hrAk P Q a b h (((kmax + 1 : ℕ) : ℤ)) = 0
    unfold hrAk
    push_cast
    rw [hedge0]; simp
  have hsup : ∀ i, k1 + 1 ≤ i → i ≤ kmax →
      (fun n : ℕ => hrAk P Q a b h (n : ℤ)) (i + 1) + (fun n : ℕ => hrAk P Q a b h (n : ℤ)) i ≤
        (fun n : ℕ => hrCk P Q τ x a b h (n : ℤ)) i := by
    intro i hi1 hi2
    obtain ⟨f1, f2, f3, f4⟩ := hfacts i hi1
    have hik' : (i : ℝ) ≤ kmax := Nat.cast_le.2 hi2
    have hD : (((i : ℝ) + 1) * h) ^ 2 ∈ Dom P Q :=
      Dom_mono hP hQ (by positivity)
        (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right (by linarith) hh.le) 2) hedge
    have hkq : qs ≤ 2 * (i : ℝ) * h := by nlinarith
    have hK : 0 ≤ 2 * ((1 - τ * x) / qs ^ 2) * qs :=
      mul_nonneg (mul_nonneg (by norm_num) (div_nonneg hκ.le (sq_nonneg _))) hqs.le
    have hgap : hrRho P Q a b qs * h ^ 2 ≤
        2 * ((1 - τ * x) / qs ^ 2) * qs * (((i : ℝ) + 1 / 2) * h - qs) := by
      calc hrRho P Q a b qs * h ^ 2 = (h * hrRho P Q a b qs) * h := by ring
        _ ≤ (2 * ((1 - τ * x) / qs ^ 2) * qs) * h := mul_le_mul_of_nonneg_right hhC hh.le
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hK
    have := exact_hyperbolicity_hahn_racah hP hQ a b τ x qs h (i : ℝ) hh hqs hτ hκ hturn f1
      f2.le f3.le hkq hD hgap
    simp only [hrAk, hrCk]
    push_cast
    linarith
  have hrow : ∀ i, k1 + 1 ≤ i → i ≤ kmax →
      (fun n : ℕ => hrAk P Q a b h (n : ℤ)) (i + 1) * (fun n : ℕ => Y (n : ℤ)) (i + 1) +
        (fun n : ℕ => hrAk P Q a b h (n : ℤ)) i * (fun n : ℕ => Y (n : ℤ)) (i - 1) =
      (fun n : ℕ => hrCk P Q τ x a b h (n : ℤ)) i * (fun n : ℕ => Y (n : ℤ)) i := by
    intro i hi1 hi2
    have h0 := hY (i : ℤ) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    unfold jac at h0
    show hrAk P Q a b h ((i + 1 : ℕ) : ℤ) * Y ((i + 1 : ℕ) : ℤ) +
      hrAk P Q a b h (i : ℤ) * Y ((i - 1 : ℕ) : ℤ) = hrCk P Q τ x a b h (i : ℤ) * Y (i : ℤ)
    rw [show ((i + 1 : ℕ) : ℤ) = (i : ℤ) + 1 by push_cast; ring,
      show ((i - 1 : ℕ) : ℤ) = (i : ℤ) - 1 by omega]
    linarith
  have H := hd_backward_decay (fun n : ℕ => hrAk P Q a b h (n : ℤ))
    (fun n : ℕ => hrCk P Q τ x a b h (n : ℤ)) (fun n : ℕ => Y (n : ℤ)) (k1 + 1) kmax (by omega)
    (by omega) hA hend hsup hrow
  intro k hk1' hk2
  lift k to ℕ using (by omega)
  have := H k (by omega) (by omega)
  simpa using this

/-- info: 'FormalResearch.Special.hd_backward_decay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hd_backward_decay

/-- info: 'FormalResearch.Special.hr_hardedge_decay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hr_hardedge_decay

end FormalResearch.Special
