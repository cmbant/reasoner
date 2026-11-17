module

public import FormalResearch.Special.HermiteKappaEnvelope
public import FormalResearch.Special.HermiteKappaOde

/-!
# Uniform envelope of the Hermite functions (W1 `lem:PR(b)`)

**Theorem (`hermite_envelope`).**  For all `n ≥ 0` and all real `x`,
`φ_n(x)² · √(|2n + 1 - x²| + (2n+1)^{1/3}) ≤ 12·10⁶`.
(Numerics, double-precision scan, not committed: the sharp constant is `√2/√π ≈ 0.798`, attained at `n = 0`, `x = 0`; for `n = 1, 2, 5, 10, 100, 1000`
the supremum over `x` is `0.777, 0.770, 0.762, 0.758, 0.753, 0.752`, tending to `≈ 0.75`.  So the claim is true and the constant `12·10⁶` is crude.)

This is the size statement of W1 `lem:PR(b)` (`Weyl/free_fermion/paper/parts/hermite.tex`): for `x₀ = ξ√(2N)`, `y_n = φ_n(x₀)`,
`|y_n|² ≤ C N^{-1/2} ρ_n` with `ρ_n = min(d_n^{-1/2}, N^{1/2}(2n+1)^{-1/6})`, `d_n = |2n+1-x₀²|/N` for `n < 2N`, and
`ρ_n = (n/N)^{1/2}` for `n ≥ 2N` (`hermite_PR_b`); it holds uniformly in `ξ` (no `ξ₀ < 1` needed).  It does **not** use the
Airy amplitude `κ` of `HermiteAiryEdge`: the proof is in the `x` variable (Weber ODE `φ'' = (x² - 2n - 1) φ`, the adiabatic invariant
`T = w φ² + φ'²/w`, `w = √(2n+1 - x²)`, and `∫ φ_n² = 1`), see `HermiteKappaEnvelope`.

**Claim class: proved.**  Not formalised: the oscillatory form `y_n = √(2/π)(2n+1)^{-1/4}(sin t_n)^{-1/2}[cos Φ_n + O(1/n)]`
(`lem:PR(a)`), the sharp constant, the bound on `y_n'` (follows from `y_n' = a_{n-1}y_{n-1} - a_n y_{n+1}`, not restated).
-/

@[expose] public section

open Real

namespace FormalResearch.Special

lemma hermite_lam_rpow (n : ℕ) :
    ∃ q : ℝ, 1 ≤ q ∧ q ^ 6 = 2 * (n : ℝ) + 1 ∧ q ^ 2 = (2 * (n : ℝ) + 1) ^ (1 / 3 : ℝ) := by
  have hl : (1 : ℝ) ≤ 2 * (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hl0 : (0 : ℝ) ≤ 2 * (n : ℝ) + 1 := by linarith
  refine ⟨(2 * (n : ℝ) + 1) ^ (1 / 6 : ℝ), Real.one_le_rpow hl (by norm_num), ?_, ?_⟩
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hl0]; norm_num
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hl0]; norm_num

/-- **Uniform envelope of the Hermite functions**: `φ_n(x)² √(|2n+1-x²| + (2n+1)^{1/3}) ≤ 12·10⁶`. -/
theorem hermite_envelope (n : ℕ) (x : ℝ) :
    hermitePhi n x ^ 2 * √(|2 * (n : ℝ) + 1 - x ^ 2| + (2 * (n : ℝ) + 1) ^ (1 / 3 : ℝ)) ≤ 12000000 := by
  obtain ⟨q, hq1, hq6, hq2⟩ := hermite_lam_rpow n
  rw [← hq2, ← hq6]
  have hW : WeberData (q ^ 6) (hermitePhi n) (hkDer n) (fun x => ∫ t in (0 : ℝ)..x, hermitePhi n t ^ 2) := by
    rw [hq6]; exact hermite_weberData n
  have hq0 : 0 < q := by linarith
  -- reduce to `x ≥ 0` by parity
  suffices H : ∀ y : ℝ, 0 ≤ y → hermitePhi n y ^ 2 * √(|q ^ 6 - y ^ 2| + q ^ 2) ≤ 12000000 by
    rcases le_total 0 x with hx | hx
    · exact H x hx
    · have := H (-x) (by linarith)
      have e : hermitePhi n (-x) ^ 2 = hermitePhi n x ^ 2 := by
        rw [← sq_abs, abs_hermitePhi_neg, sq_abs]
      rw [e] at this
      simpa using this
  intro y hy
  rcases le_or_gt 4 q with h4 | h4
  · exact weber_envelope h4 hW hy
  · -- small `n`: `q < 4`, `φ² ≤ q⁶ + 1 ≤ 4097`
    have hsup : hermitePhi n y ^ 2 ≤ q ^ 6 + 1 := by
      have := hermitePhi_sq_le n y
      rw [hq6]; linarith
    have hq6le : q ^ 6 ≤ 4096 := by
      have : q ^ 6 ≤ 4 ^ 6 := pow_le_pow_left₀ hq0.le h4.le 6
      linarith
    have hq2le : q ^ 2 ≤ 16 := by nlinarith
    rcases le_total y (q ^ 3) with hy1 | hy1
    · have hd : |q ^ 6 - y ^ 2| + q ^ 2 ≤ 65 ^ 2 := by
        have : 0 ≤ q ^ 6 - y ^ 2 := by nlinarith [pow_pos hq0 3]
        rw [abs_of_nonneg this]
        nlinarith [sq_nonneg y]
      have hs : √(|q ^ 6 - y ^ 2| + q ^ 2) ≤ 65 := Real.sqrt_le_iff.2 ⟨by norm_num, hd⟩
      calc hermitePhi n y ^ 2 * √(|q ^ 6 - y ^ 2| + q ^ 2) ≤ 4097 * 65 :=
            mul_le_mul (by linarith) hs (Real.sqrt_nonneg _) (by norm_num)
        _ ≤ 12000000 := by norm_num
    · have hK : hermitePhi n (q ^ 3) ^ 2 ≤ 16388 / q := by
        have h1 : hermitePhi n (q ^ 3) ^ 2 ≤ 4097 := by
          have := hermitePhi_sq_le n (q ^ 3)
          nlinarith
        rw [le_div_iff₀ hq0]
        nlinarith
      have := forbidden_bound hq1 hW (K := 16388) (by norm_num) hK hy1
      linarith

/-- **W1 `lem:PR(b)`** (size statement), in product form.  For `N ≥ 1`, `x₀² ≤ 2N` (i.e. `x₀ = ξ√(2N)`, `|ξ| ≤ 1`), `y_n = φ_n(x₀)`:

* `y_n² √t ≤ C`, `t = (2n+1)^{1/3}` (so `y_n² ≤ C (2n+1)^{-1/6}`, the `N^{1/2}(2n+1)^{-1/6}` branch of `ρ_n`);
* `y_n² √|2n+1-x₀²| ≤ C` (so `y_n² ≤ C N^{-1/2} d_n^{-1/2}`, `d_n = |2n+1-x₀²|/N`, the other branch of `ρ_n`);
* for `n ≥ 2N`: `y_n² N ≤ C √n` (`y_n² ≤ C N^{-1/2} (n/N)^{1/2}`);

with `C = 12·10⁶`.  Elementary algebra (not formalised here) turns the three conjuncts into the paper's `y_n² ≤ C N^{-1/2} ρ_n`
for all `n ≥ 0`: for `n < 2N` the first two conjuncts give `y_n² ≤ C min(|2n+1-x₀²|^{-1/2}, (2n+1)^{-1/6}) = C N^{-1/2} ρ_n`
(the case `2n+1 = x₀²` being covered by the first conjunct alone), and for `n ≥ 2N` the third gives `y_n² ≤ C N^{-1/2} (n/N)^{1/2}`.
The Lean statement holds for every real `x₀` (the hypothesis `x₀² ≤ 2N` is only used in the third conjunct).  It does not contain the
paper's bound `|y_n'| ≤ C N^{1/4} ρ_n^{1/2}` nor the oscillatory form `lem:PR(a)`. -/
theorem hermite_PR_b (N n : ℕ) (hN : 1 ≤ N) (x₀ : ℝ) (hx : x₀ ^ 2 ≤ 2 * N) :
    hermitePhi n x₀ ^ 2 * √((2 * (n : ℝ) + 1) ^ (1 / 3 : ℝ)) ≤ 12000000 ∧
    hermitePhi n x₀ ^ 2 * √|2 * (n : ℝ) + 1 - x₀ ^ 2| ≤ 12000000 ∧
    (2 * N ≤ n → hermitePhi n x₀ ^ 2 * N ≤ 12000000 * √(n : ℝ)) := by
  have H := hermite_envelope n x₀
  have hsq : 0 ≤ hermitePhi n x₀ ^ 2 := sq_nonneg _
  have ht : 0 ≤ (2 * (n : ℝ) + 1) ^ (1 / 3 : ℝ) :=
    Real.rpow_nonneg (by positivity) _
  refine ⟨?_, ?_, ?_⟩
  · refine le_trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hsq) H
    have := abs_nonneg (2 * (n : ℝ) + 1 - x₀ ^ 2)
    linarith
  · refine le_trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hsq) H
    linarith
  · intro h2
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have h2' : (2 * N : ℝ) ≤ n := by exact_mod_cast h2
    have hn : (N : ℝ) ≤ n := by linarith
    have hd : (n : ℝ) ≤ |2 * (n : ℝ) + 1 - x₀ ^ 2| := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    have h1 : hermitePhi n x₀ ^ 2 * √(n : ℝ) ≤ 12000000 :=
      le_trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by
        have := abs_nonneg (2 * (n : ℝ) + 1 - x₀ ^ 2)
        linarith [ht])) hsq) H
    have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have e : (n : ℝ) = √(n : ℝ) * √(n : ℝ) := (Real.mul_self_sqrt hnn).symm
    calc hermitePhi n x₀ ^ 2 * N ≤ hermitePhi n x₀ ^ 2 * n := mul_le_mul_of_nonneg_left hn hsq
      _ = hermitePhi n x₀ ^ 2 * √(n : ℝ) * √(n : ℝ) := by rw [mul_assoc, ← e]
      _ ≤ 12000000 * √(n : ℝ) := mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)

/-- info: 'FormalResearch.Special.hermite_weberData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hermite_weberData

/-- info: 'FormalResearch.Special.hermite_envelope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hermite_envelope

/-- info: 'FormalResearch.Special.hermite_PR_b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hermite_PR_b

end FormalResearch.Special
