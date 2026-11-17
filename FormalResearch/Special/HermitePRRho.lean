module

public import FormalResearch.Special.HermitePRDeriv

/-!
# Derivative bound for Hermite functions (W1 `lem:PR(b)`, second half)

**Theorem (`hpr_deriv_bound`).** For `N ≥ 1`, `x₀² ≤ 2N` and every `n ≥ 0`,
`|φ_n'(x₀)| ≤ 12000 · N^{1/4} · ρ_n^{1/2}`, with `ρ_n` as in the paper (`hpr_rho`):
`ρ_n = min(d_n^{-1/2}, N^{1/2}(2n+1)^{-1/6})` for `n < 2N`, `d_n = |2n+1-x₀²|/N`, and `ρ_n = (n/N)^{1/2}` for `n ≥ 2N`.

The proof is the paper's: the exact ladder `φ_n' = √(n/2) φ_{n-1} - √((n+1)/2) φ_{n+1}` (`hasDerivAt_hermitePsi`,
via `hpr_abs_deriv_le_ladder`), the size bound at `n ± 1` from `hermite_envelope` / `hermite_PR_b`
(`HermiteKappaSup`), and the neighbour comparability `ρ_{n±1} ≤ 3 ρ_n` for `n < 2N`, proved here in the form
`hpr_den_le` for the denominator.  For `n ≥ 2N` it uses `|y_k| ≤ C k^{-1/4}`, which here comes directly from
`hermite_envelope` since `|2k+1-x₀²| ≥ k` there (not from part (a)).  The two branches of `ρ` are never
compared with each other (no transition lemma is needed).

Convention: for `n < 2N`, `ρ_n = N^{1/2} / max(|2n+1-x₀²|^{1/2}, (2n+1)^{1/6})`, which equals the paper's `min` whenever
`2n+1 ≠ x₀²` (`hpr_rho_eq_min`) and is the intended value (`N^{1/2}(2n+1)^{-1/6}`) when `2n+1 = x₀²`, where
`d_n^{-1/2}` is `+∞`.

**Claim class: proved.**  The constant `12000` is crude (`√(12 · 12·10⁶)`, from the crude constant of `hermite_envelope`).
Not formalised: the bulk oscillatory asymptotic `lem:PR(a)` (phase value and remainder).
-/

@[expose] public section

open Real

namespace FormalResearch.Special

/-- Denominator of `ρ_n` on `n < 2N`: `max(|2n+1-x₀²|^{1/2}, (2n+1)^{1/6})`. -/
noncomputable def hpr_den (x₀ : ℝ) (n : ℕ) : ℝ :=
  max (√|2 * (n : ℝ) + 1 - x₀ ^ 2|) ((2 * (n : ℝ) + 1) ^ (1 / 6 : ℝ))

/-- The paper's `ρ_n` (see the module docstring for the convention at `2n+1 = x₀²`). -/
noncomputable def hpr_rho (N n : ℕ) (x₀ : ℝ) : ℝ :=
  if n < 2 * N then √(N : ℝ) / hpr_den x₀ n else √((n : ℝ) / N)

lemma hpr_one_le_rpow (n : ℕ) : 1 ≤ (2 * (n : ℝ) + 1) ^ (1 / 6 : ℝ) :=
  Real.one_le_rpow (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith) (by norm_num)

lemma hpr_den_pos (x₀ : ℝ) (n : ℕ) : 0 < hpr_den x₀ n :=
  lt_of_lt_of_le one_pos ((hpr_one_le_rpow n).trans (le_max_right _ _))

/-- For `2n+1 ≠ x₀²` and `n < 2N`, `hpr_rho` is the paper's `min(d_n^{-1/2}, N^{1/2}(2n+1)^{-1/6})`. -/
theorem hpr_rho_eq_min (N n : ℕ) (x₀ : ℝ) (hN : 1 ≤ N) (hn : n < 2 * N)
    (hx : 2 * (n : ℝ) + 1 ≠ x₀ ^ 2) :
    hpr_rho N n x₀ =
      min ((|2 * (n : ℝ) + 1 - x₀ ^ 2| / (N : ℝ)) ^ (-(1 / 2) : ℝ))
        ((N : ℝ) ^ (1 / 2 : ℝ) * (2 * (n : ℝ) + 1) ^ (-(1 / 6) : ℝ)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hA : 0 < |2 * (n : ℝ) + 1 - x₀ ^ 2| := abs_pos.2 (sub_ne_zero.2 hx)
  have hB : (0 : ℝ) < 2 * n + 1 := by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
  rw [hpr_rho, hpr_den]
  simp only [hn, ↓reduceIte]
  have e1 : (|2 * (n : ℝ) + 1 - x₀ ^ 2| / (N : ℝ)) ^ (-(1 / 2) : ℝ) =
      √(N : ℝ) / √|2 * (n : ℝ) + 1 - x₀ ^ 2| := by
    rw [Real.div_rpow hA.le hN0.le, Real.rpow_neg hA.le, Real.rpow_neg hN0.le]
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    field_simp
  have e2 : (N : ℝ) ^ (1 / 2 : ℝ) * (2 * (n : ℝ) + 1) ^ (-(1 / 6) : ℝ) =
      √(N : ℝ) / (2 * (n : ℝ) + 1) ^ (1 / 6 : ℝ) := by
    rw [Real.rpow_neg hB.le, Real.sqrt_eq_rpow]; ring
  rw [e1, e2]
  have hs : 0 < √|2 * (n : ℝ) + 1 - x₀ ^ 2| := Real.sqrt_pos.2 hA
  have hp : 0 < (2 * (n : ℝ) + 1) ^ (1 / 6 : ℝ) := Real.rpow_pos_of_pos hB _
  have hsN : 0 < √(N : ℝ) := Real.sqrt_pos.2 hN0
  rcases le_total (√|2 * (n : ℝ) + 1 - x₀ ^ 2|) ((2 * (n : ℝ) + 1) ^ (1 / 6 : ℝ)) with h | h
  · rw [max_eq_right h, min_eq_right (div_le_div_of_nonneg_left hsN.le hs h)]
  · rw [max_eq_left h, min_eq_left (div_le_div_of_nonneg_left hsN.le hp h)]

/-- Neighbour comparability of the denominators: `den_n ≤ 3 den_k` for `|n-k| ≤ 1`. -/
theorem hpr_den_le (x₀ : ℝ) (n k : ℕ) (h1 : n ≤ k + 1) (h2 : k ≤ n + 1) :
    hpr_den x₀ n ≤ 3 * hpr_den x₀ k := by
  have h1' : (n : ℝ) ≤ k + 1 := by exact_mod_cast h1
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hp1 := hpr_one_le_rpow k
  have hDk : √|2 * (k : ℝ) + 1 - x₀ ^ 2| ≤ hpr_den x₀ k := le_max_left _ _
  have hDk' : (2 * (k : ℝ) + 1) ^ (1 / 6 : ℝ) ≤ hpr_den x₀ k := le_max_right _ _
  have hA : |2 * (n : ℝ) + 1 - x₀ ^ 2| ≤ |2 * (k : ℝ) + 1 - x₀ ^ 2| + 2 := by
    have : 2 * (n : ℝ) + 1 - x₀ ^ 2 = (2 * (k : ℝ) + 1 - x₀ ^ 2) + 2 * ((n : ℝ) - k) := by ring
    rw [this]
    refine (abs_add_le _ _).trans ?_
    have : |2 * ((n : ℝ) - k)| ≤ 2 := by
      rw [abs_le]; have h2' : (k : ℝ) ≤ n + 1 := by exact_mod_cast h2
      constructor <;> linarith
    linarith
  have hsq : √|2 * (n : ℝ) + 1 - x₀ ^ 2| ≤ 3 * hpr_den x₀ k := by
    refine (Real.sqrt_le_sqrt hA).trans ?_
    have h3 : √(|2 * (k : ℝ) + 1 - x₀ ^ 2| + 2) ≤
        √|2 * (k : ℝ) + 1 - x₀ ^ 2| + √2 := by
      rw [Real.sqrt_le_left (by positivity), add_sq, Real.sq_sqrt (abs_nonneg _),
        Real.sq_sqrt (by norm_num)]
      have := Real.sqrt_nonneg |2 * (k : ℝ) + 1 - x₀ ^ 2|
      have := Real.sqrt_nonneg 2
      nlinarith [mul_nonneg (Real.sqrt_nonneg |2 * (k : ℝ) + 1 - x₀ ^ 2|) (Real.sqrt_nonneg 2)]
    have h2le : √(2 : ℝ) ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    linarith
  have hB : (2 * (n : ℝ) + 1) ^ (1 / 6 : ℝ) ≤ 3 * hpr_den x₀ k := by
    have hle : 2 * (n : ℝ) + 1 ≤ 3 ^ 6 * (2 * (k : ℝ) + 1) := by nlinarith
    calc (2 * (n : ℝ) + 1) ^ (1 / 6 : ℝ)
        ≤ (3 ^ 6 * (2 * (k : ℝ) + 1)) ^ (1 / 6 : ℝ) :=
          Real.rpow_le_rpow (by positivity) hle (by norm_num)
      _ = 3 * (2 * (k : ℝ) + 1) ^ (1 / 6 : ℝ) := by
          rw [Real.mul_rpow (by positivity) (by positivity)]
          congr 1
          rw [show (3 : ℝ) ^ 6 = 3 ^ (6 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
          norm_num
      _ ≤ 3 * hpr_den x₀ k := by linarith
  exact max_le hsq hB

/-- `φ_k² · den_k ≤ 12·10⁶` (the two bounds of `hermite_PR_b`). -/
lemma hpr_sq_den (N k : ℕ) (hN : 1 ≤ N) (x₀ : ℝ) (hx : x₀ ^ 2 ≤ 2 * N) :
    hermitePhi k x₀ ^ 2 * hpr_den x₀ k ≤ 12000000 := by
  obtain ⟨h1, h2, -⟩ := hermite_PR_b N k hN x₀ hx
  have e : √((2 * (k : ℝ) + 1) ^ (1 / 3 : ℝ)) = (2 * (k : ℝ) + 1) ^ (1 / 6 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)]
    norm_num
  rw [e] at h1
  unfold hpr_den
  rcases le_total (√|2 * (k : ℝ) + 1 - x₀ ^ 2|) ((2 * (k : ℝ) + 1) ^ (1 / 6 : ℝ)) with h | h
  · rwa [max_eq_right h]
  · rwa [max_eq_left h]

lemma hpr_deriv_sq (n : ℕ) (x : ℝ) :
    deriv (hermitePhi n) x ^ 2 ≤
      (n : ℝ) * hermitePsi ((n : ℤ) - 1) x ^ 2 + ((n : ℝ) + 1) * hermitePhi (n + 1) x ^ 2 := by
  have h := hpr_abs_deriv_le_ladder (n : ℤ) (by positivity) x
  have hm : hermitePsi (n : ℤ) = hermitePhi n := funext (hermitePsi_natCast n)
  rw [hm] at h
  have hp : hermitePsi ((n : ℤ) + 1) x = hermitePhi (n + 1) x := by
    have := hermitePsi_natCast (n + 1) x; simpa using this
  rw [hp] at h
  simp only [Int.cast_natCast] at h
  set a := √((n : ℝ) / 2)
  set b := √(((n : ℝ) + 1) / 2)
  have ha : a ^ 2 = n / 2 := Real.sq_sqrt (by positivity)
  have hb : b ^ 2 = (n + 1) / 2 := Real.sq_sqrt (by positivity)
  set u := |hermitePsi ((n : ℤ) - 1) x|
  set v := |hermitePhi (n + 1) x|
  have hsq := pow_le_pow_left₀ (abs_nonneg _) h 2
  rw [sq_abs] at hsq
  have hu : u ^ 2 = hermitePsi ((n : ℤ) - 1) x ^ 2 := sq_abs _
  have hv : v ^ 2 = hermitePhi (n + 1) x ^ 2 := sq_abs _
  have key : (a * u + b * v) ^ 2 ≤ 2 * a ^ 2 * u ^ 2 + 2 * b ^ 2 * v ^ 2 := by
    nlinarith [sq_nonneg (a * u - b * v)]
  rw [← hu, ← hv]
  nlinarith

/-- **Derivative bound** `|y_n'| ≤ C N^{1/4} ρ_n^{1/2}` of W1 `lem:PR(b)` (explicit `C = 12000`). -/
theorem hpr_deriv_bound (N n : ℕ) (hN : 1 ≤ N) (x₀ : ℝ) (hx : x₀ ^ 2 ≤ 2 * N) :
    |deriv (hermitePhi n) x₀| ≤ 12000 * (N : ℝ) ^ (1 / 4 : ℝ) * √(hpr_rho N n x₀) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN4 : ((N : ℝ) ^ (1 / 4 : ℝ)) ^ 2 = √(N : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le, Real.sqrt_eq_rpow]; norm_num
  have hrho : 0 ≤ hpr_rho N n x₀ := by
    unfold hpr_rho; split_ifs
    · exact div_nonneg (Real.sqrt_nonneg _) (hpr_den_pos _ _).le
    · exact Real.sqrt_nonneg _
  have main : deriv (hermitePhi n) x₀ ^ 2 ≤ 12000 ^ 2 * (√(N : ℝ) * hpr_rho N n x₀) := by
    refine (hpr_deriv_sq n x₀).trans ?_
    by_cases hn : n < 2 * N
    · have hn' : (n : ℝ) + 1 ≤ 2 * N := by exact_mod_cast hn
      have hr : hpr_rho N n x₀ = √(N : ℝ) / hpr_den x₀ n := by simp only [hpr_rho, hn, ↓reduceIte]
      have hsN : √(N : ℝ) * √(N : ℝ) = N := Real.mul_self_sqrt hN0.le
      have hD := hpr_den_pos x₀ n
      -- bounds at n+1 and n-1
      have hup : hermitePhi (n + 1) x₀ ^ 2 ≤ 3 * 12000000 / hpr_den x₀ n := by
        have := hpr_sq_den N (n + 1) hN x₀ hx
        have hle := hpr_den_le x₀ n (n + 1) (by omega) (by omega)
        have hD1 := hpr_den_pos x₀ (n + 1)
        rw [le_div_iff₀ hD]
        nlinarith [sq_nonneg (hermitePhi (n + 1) x₀)]
      have hdn : (n : ℝ) * hermitePsi ((n : ℤ) - 1) x₀ ^ 2 ≤ (n + 1) * (3 * 12000000 / hpr_den x₀ n) := by
        rcases Nat.eq_zero_or_pos n with h0 | h0
        · subst h0; simp; positivity
        · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
          have hp : hermitePsi (((m + 1 : ℕ) : ℤ) - 1) x₀ = hermitePhi m x₀ := by
            have := hermitePsi_natCast m x₀; simpa using this
          rw [hp]
          have := hpr_sq_den N m hN x₀ hx
          have hle := hpr_den_le x₀ (m + 1) m (by omega) (by omega)
          have hD1 := hpr_den_pos x₀ m
          have h3 : hermitePhi m x₀ ^ 2 ≤ 3 * 12000000 / hpr_den x₀ (m + 1) := by
            rw [le_div_iff₀ hD]
            nlinarith [sq_nonneg (hermitePhi m x₀)]
          have hmm : ((m + 1 : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) + 1 := by linarith
          calc ((m + 1 : ℕ) : ℝ) * hermitePhi m x₀ ^ 2
              ≤ (((m + 1 : ℕ) : ℝ) + 1) * (3 * 12000000 / hpr_den x₀ (m + 1)) :=
                mul_le_mul hmm h3 (sq_nonneg _) (by positivity)
            _ = _ := rfl
      have hfin : ((n : ℝ) + 1) * (3 * 12000000 / hpr_den x₀ n) ≤ 2 * N * (3 * 12000000 / hpr_den x₀ n) :=
        mul_le_mul_of_nonneg_right hn' (by positivity)
      rw [hr]
      have : (n : ℝ) * hermitePsi ((n : ℤ) - 1) x₀ ^ 2 + ((n : ℝ) + 1) * hermitePhi (n + 1) x₀ ^ 2 ≤
          2 * ((n + 1) * (3 * 12000000 / hpr_den x₀ n)) := by
        have := mul_le_mul_of_nonneg_left hup (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)
        linarith
      refine this.trans ?_
      have e : 12000 ^ 2 * (√(N : ℝ) * (√(N : ℝ) / hpr_den x₀ n)) =
          N * (144000000 / hpr_den x₀ n) := by
        have : (12000 : ℝ) ^ 2 * (√(N : ℝ) * (√(N : ℝ) / hpr_den x₀ n)) =
            12000 ^ 2 * (√(N : ℝ) * √(N : ℝ)) / hpr_den x₀ n := by ring
        rw [this, hsN]
        ring
      rw [e]
      have : 2 * (((n : ℝ) + 1) * (3 * 12000000 / hpr_den x₀ n)) ≤
          2 * (2 * N * (3 * 12000000 / hpr_den x₀ n)) := by linarith
      refine this.trans (le_of_eq ?_)
      ring
    · replace hn := not_lt.1 hn
      have hn2 : (2 * N : ℝ) ≤ n := by exact_mod_cast hn
      have hr : hpr_rho N n x₀ = √((n : ℝ) / N) := by simp only [hpr_rho, show ¬ n < 2 * N by omega, ↓reduceIte]
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have : 1 ≤ N := hN; omega⟩
      push_cast at hn2 ⊢
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have hs1 : (0 : ℝ) < √((m : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
      have hs1' : √((m : ℝ) + 1) * √((m : ℝ) + 1) = (m : ℝ) + 1 := Real.mul_self_sqrt (by positivity)
      push_cast at hr
      set s := √((m : ℝ) + 1) with hs
      have hm0 : (1 : ℝ) ≤ m := by
        have : 1 ≤ m := by omega
        exact_mod_cast this
      have hhalf : s / 2 ≤ √|2 * (m : ℝ) + 1 - x₀ ^ 2| := by
        apply Real.le_sqrt_of_sq_le
        rw [div_pow, hs, Real.sq_sqrt (by positivity), abs_of_nonneg (by nlinarith)]
        nlinarith
      have hhalf2 : s / 2 ≤ √|2 * (((m + 2 : ℕ)) : ℝ) + 1 - x₀ ^ 2| := by
        apply Real.le_sqrt_of_sq_le
        rw [div_pow, hs, Real.sq_sqrt (by positivity), abs_of_nonneg (by push_cast; nlinarith)]
        push_cast
        nlinarith
      obtain ⟨-, hb1, -⟩ := hermite_PR_b N m hN x₀ hx
      obtain ⟨-, hb2, -⟩ := hermite_PR_b N (m + 2) hN x₀ hx
      have sq1 : hermitePhi m x₀ ^ 2 * s ≤ 2 * 12000000 := by
        have := mul_le_mul_of_nonneg_left hhalf (sq_nonneg (hermitePhi m x₀))
        nlinarith
      have sq2 : hermitePhi (m + 2) x₀ ^ 2 * s ≤ 2 * 12000000 := by
        have := mul_le_mul_of_nonneg_left hhalf2 (sq_nonneg (hermitePhi (m + 2) x₀))
        nlinarith
      have hss : s * s = (m : ℝ) + 1 := Real.mul_self_sqrt (by positivity)
      have hp : hermitePsi (((m + 1 : ℕ) : ℤ) - 1) x₀ = hermitePhi m x₀ := by
        have := hermitePsi_natCast m x₀; simpa using this
      rw [show ((m : ℤ) + 1 - 1) = (m : ℤ) by ring, hermitePsi_natCast, hr]
      have e : √(N : ℝ) * √(((m : ℝ) + 1) / N) = s := by
        rw [← Real.sqrt_mul hN0.le, mul_div_cancel₀ _ hN0.ne']
      rw [e]
      have hsp : 0 ≤ s := Real.sqrt_nonneg _
      have e1 : ((m : ℝ) + 1) * hermitePhi m x₀ ^ 2 ≤ 2 * 12000000 * s := by
        rw [← hss]; nlinarith [sq1]
      have e2 : ((m : ℝ) + 1 + 1) * hermitePhi (m + 2) x₀ ^ 2 ≤ 2 * (2 * 12000000 * s) := by
        have : ((m : ℝ) + 1 + 1) * hermitePhi (m + 2) x₀ ^ 2 ≤
            2 * (((m : ℝ) + 1) * hermitePhi (m + 2) x₀ ^ 2) := by
          nlinarith [sq_nonneg (hermitePhi (m + 2) x₀)]
        have h3 : ((m : ℝ) + 1) * hermitePhi (m + 2) x₀ ^ 2 ≤ 2 * 12000000 * s := by
          rw [← hss]; nlinarith [sq2]
        linarith
      have hc : hermitePhi (m + 1 + 1) x₀ = hermitePhi (m + 2) x₀ := rfl
      rw [hc]
      nlinarith
  have hRHS : (12000 * (N : ℝ) ^ (1 / 4 : ℝ) * √(hpr_rho N n x₀)) ^ 2 =
      12000 ^ 2 * (√(N : ℝ) * hpr_rho N n x₀) := by
    rw [mul_pow, mul_pow, hN4, Real.sq_sqrt hrho]
    ring
  have h0 : 0 ≤ 12000 * (N : ℝ) ^ (1 / 4 : ℝ) * √(hpr_rho N n x₀) := by positivity
  rw [← hRHS] at main
  exact abs_le.2 (abs_le_of_sq_le_sq' main h0)

end FormalResearch.Special

/-- info: 'FormalResearch.Special.hpr_deriv_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hpr_deriv_bound

/-- info: 'FormalResearch.Special.hpr_rho_eq_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hpr_rho_eq_min
