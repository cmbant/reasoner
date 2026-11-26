module

public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Topology.Algebra.Polynomial

/-!
# Laguerre polynomials `L_k^{(w-1)}`: coefficients, three-term recurrence, growth bounds

Paper II (`CFT/modular_bootstrap/paper/dual_spectrum.tex`, before `ds:LP`), for a real weight `w > 0`:

* `lagL w k x = L_k^{(w-1)}(x) = ∑_{j ≤ k} (-1)^j C(k + w - 1, k - j) x^j / j!`, defined through the
  Pochhammer coefficients `lagCoef w j m = (w + j)_m / m!`;
* `lagP w k t = P_k(t) = (-1)^k k! (4π)^{-k} L_k^{(w-1)}(4π t)`, the monic polynomial of the paper,
  with `P_1 = t - w/(4π)`.

Proved here (no generating function yet): the three-term recurrence (`lagL_rec`, `lagP_rec`), and two
growth bounds for `t ≥ 0` which replace the Jacobi-matrix zero localisation in the proof of
`ds:mom` (`dual_spectrum_limit.tex`, Lemma LP-M):

* `lagP_lower`: `(t/2)^n ≤ P_n(t)` for `t ≥ 2(n + w)/π` (induction on the ratios `P_{j+1}/P_j ≥ t/2`);
* `abs_lagP_le`: `|P_n(t)| ≤ (t + (3 + w) n/(4π))^n` for `t ≥ 0`.
-/

@[expose] public section

open Polynomial Finset

namespace FormalResearch.ModularBootstrap.LP

/-! ### Pochhammer symbols -/

/-- The rising factorial `(a)_m = a (a+1) ⋯ (a+m-1)`. -/
noncomputable def poch (a : ℝ) : ℕ → ℝ
  | 0 => 1
  | m + 1 => poch a m * (a + m)

@[simp] lemma poch_zero (a : ℝ) : poch a 0 = 1 := rfl

lemma poch_succ (a : ℝ) (m : ℕ) : poch a (m + 1) = poch a m * (a + m) := rfl

lemma poch_eq_ascPochhammer (a : ℝ) (m : ℕ) : poch a m = (ascPochhammer ℝ m).eval a := by
  induction m with
  | zero => simp
  | succ m ih => rw [poch_succ, ascPochhammer_succ_eval, ih]

lemma poch_succ_left (a : ℝ) (m : ℕ) : poch a (m + 1) = a * poch (a + 1) m := by
  induction m generalizing a with
  | zero => simp [poch_succ]
  | succ m ih =>
    rw [poch_succ, ih, poch_succ]
    push_cast
    ring

lemma poch_pos {a : ℝ} (ha : 0 < a) (m : ℕ) : 0 < poch a m := by
  induction m with
  | zero => exact one_pos
  | succ m ih => rw [poch_succ]; exact mul_pos ih (by positivity)

/-! ### Laguerre coefficients and polynomials -/

/-- `(w + j)_m / m!`, i.e. `C(w + j + m - 1, m)`; the coefficient of `x^j` in `L_{j+m}^{(w-1)}` is
`(-1)^j lagCoef w j m / j!`. -/
noncomputable def lagCoef (w : ℝ) (j m : ℕ) : ℝ := poch (w + j) m / m.factorial

lemma lagCoef_pos {w : ℝ} (hw : 0 < w) (j m : ℕ) : 0 < lagCoef w j m := by
  unfold lagCoef
  have : 0 < w + j := by positivity
  exact div_pos (poch_pos this m) (by positivity)

/-- The Laguerre polynomial `L_k^{(w-1)}` as a polynomial in `x`. -/
noncomputable def lagPoly (w : ℝ) (k : ℕ) : ℝ[X] :=
  ∑ j ∈ range (k + 1),
    C ((-1) ^ j * lagCoef w j (k - j) / (j.factorial : ℝ)) * X ^ j

/-- The Laguerre polynomial `L_k^{(w-1)}(x)`. -/
noncomputable def lagL (w : ℝ) (k : ℕ) (x : ℝ) : ℝ := (lagPoly w k).eval x

lemma lagL_eq_sum (w : ℝ) (k : ℕ) (x : ℝ) :
    lagL w k x = ∑ j ∈ range (k + 1), (-1) ^ j * lagCoef w j (k - j) / (j.factorial : ℝ) * x ^ j := by
  simp [lagL, lagPoly, eval_finsetSum]

lemma lagPoly_coeff (w : ℝ) (k j : ℕ) :
    (lagPoly w k).coeff j =
      if j ≤ k then (-1) ^ j * lagCoef w j (k - j) / (j.factorial : ℝ) else 0 := by
  unfold lagPoly
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq (range (k + 1)) j]
  simp

@[simp] lemma lagL_zero (w x : ℝ) : lagL w 0 x = 1 := by
  simp [lagL_eq_sum, lagCoef]

lemma lagL_one (w x : ℝ) : lagL w 1 x = w - x := by
  simp [lagL_eq_sum, lagCoef, Finset.sum_range_succ, poch_succ]
  ring

/-! ### The three-term recurrence -/

/-- Signed coefficient of `x^j` in `L_k^{(w-1)}`, as in `lagPoly_coeff`. -/
private noncomputable def cc (w : ℝ) (k j : ℕ) : ℝ :=
  if j ≤ k then (-1) ^ j * lagCoef w j (k - j) / (j.factorial : ℝ) else 0

private lemma cc_rec_zero (w : ℝ) (k : ℕ) :
    ((k : ℝ) + 2) * cc w (k + 2) 0 =
      (2 * ((k : ℝ) + 1) + w) * cc w (k + 1) 0 - ((k : ℝ) + w) * cc w k 0 := by
  simp only [cc, Nat.zero_le, ite_true, pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one,
    div_one, Nat.sub_zero, lagCoef, Nat.cast_zero, add_zero]
  simp only [poch_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have h1 : (k.factorial : ℝ) ≠ 0 := by positivity
  have h2 : ((k : ℝ) + 1) ≠ 0 := by positivity
  have h3 : ((k : ℝ) + 1 + 1) ≠ 0 := by positivity
  field_simp
  ring


private lemma cc_rec_mid (w : ℝ) (i m : ℕ) :
    ((i + 1 + m : ℕ) + 2 : ℝ) * cc w (i + 1 + m + 2) (i + 1) =
      (2 * ((i + 1 + m : ℕ) + 1 : ℝ) + w) * cc w (i + 1 + m + 1) (i + 1)
        - cc w (i + 1 + m + 1) i - ((i + 1 + m : ℕ) + w : ℝ) * cc w (i + 1 + m) (i + 1) := by
  have e1 : i + 1 + m + 2 - (i + 1) = m + 2 := by omega
  have e2 : i + 1 + m + 1 - (i + 1) = m + 1 := by omega
  have e3 : i + 1 + m - (i + 1) = m := by omega
  have e4 : i + 1 + m + 1 - i = m + 2 := by omega
  simp only [cc, show i + 1 ≤ i + 1 + m + 2 by omega, show i + 1 ≤ i + 1 + m + 1 by omega,
    show i + 1 ≤ i + 1 + m by omega, show i ≤ i + 1 + m + 1 by omega, ite_true, e1, e2, e3, e4,
    lagCoef]
  -- Pochhammer reductions
  have p1 : poch (w + ((i + 1 : ℕ) : ℝ)) (m + 2) =
      poch (w + ((i + 1 : ℕ) : ℝ)) m * (w + ((i + 1 : ℕ) : ℝ) + m) *
        (w + ((i + 1 : ℕ) : ℝ) + (m + 1 : ℕ)) := by
    rw [poch_succ, poch_succ]
  have p2 : poch (w + ((i + 1 : ℕ) : ℝ)) (m + 1) =
      poch (w + ((i + 1 : ℕ) : ℝ)) m * (w + ((i + 1 : ℕ) : ℝ) + m) := poch_succ _ _
  have p3 : poch (w + (i : ℝ)) (m + 2) =
      (w + i) * (poch (w + ((i + 1 : ℕ) : ℝ)) m * (w + ((i + 1 : ℕ) : ℝ) + m)) := by
    rw [poch_succ_left, show w + (i : ℝ) + 1 = w + ((i + 1 : ℕ) : ℝ) by push_cast; ring, poch_succ]
  rw [p1, p2, p3]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  have h1 : (m.factorial : ℝ) ≠ 0 := by positivity
  have h2 : (i.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring


private lemma cc_rec_succ (w : ℝ) (k i : ℕ) :
    ((k : ℝ) + 2) * cc w (k + 2) (i + 1) =
      (2 * ((k : ℝ) + 1) + w) * cc w (k + 1) (i + 1) - cc w (k + 1) i
        - ((k : ℝ) + w) * cc w k (i + 1) := by
  rcases lt_trichotomy (i + 1) (k + 1) with h | h | h
  · -- `i + 1 ≤ k`
    obtain ⟨m, rfl⟩ : ∃ m, k = i + 1 + m := ⟨k - (i + 1), by omega⟩
    exact cc_rec_mid w i m
  · -- `i = k`
    have hik : i = k := by omega
    subst hik
    have e1 : i + 2 - (i + 1) = 1 := by omega
    simp only [cc, show i + 1 ≤ i + 2 by omega, show i + 1 ≤ i + 1 by omega,
      show ¬ (i + 1 ≤ i) by omega, show i ≤ i + 1 by omega, ite_true, ite_false, e1, Nat.sub_self, show i + 1 - i = 1 by omega,
      lagCoef]
    simp only [poch_succ, poch_zero, Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_add,
      Nat.cast_one, Nat.cast_zero, zero_add, one_mul, mul_zero, sub_zero, pow_succ]
    have h2 : (i.factorial : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  · by_cases h2 : i = k + 1
    · subst h2
      simp only [cc, show k + 1 + 1 ≤ k + 2 by omega, show ¬ (k + 1 + 1 ≤ k + 1) by omega, show ¬ (k + 1 + 1 ≤ k) by omega,
        show k + 1 ≤ k + 1 by omega, ite_true, ite_false, Nat.sub_self,
        show k + 2 - (k + 1 + 1) = 0 by omega, lagCoef]
      simp only [poch_zero, Nat.factorial_zero, Nat.cast_one, div_one, Nat.factorial_succ, Nat.cast_mul,
        Nat.cast_add, pow_succ]
      have h3 : (k.factorial : ℝ) ≠ 0 := by positivity
      field_simp
      ring
    · have h3 : k + 2 ≤ i := by omega
      simp only [cc, show ¬ (i + 1 ≤ k + 2) by omega, show ¬ (i + 1 ≤ k + 1) by omega,
        show ¬ (i + 1 ≤ k) by omega, show ¬ (i ≤ k + 1) by omega, ite_false]
      ring

/-- The three-term recurrence of the Laguerre polynomials, as polynomials in `x`:
`(k+2) L_{k+2} = (2(k+1) + w - x) L_{k+1} - (k + w) L_k`. -/
lemma lagPoly_rec (w : ℝ) (k : ℕ) :
    C ((k : ℝ) + 2) * lagPoly w (k + 2) =
      (C (2 * ((k : ℝ) + 1) + w) - X) * lagPoly w (k + 1) - C ((k : ℝ) + w) * lagPoly w k := by
  ext j
  have hc : ∀ n j, (lagPoly w n).coeff j = cc w n j := fun n j => lagPoly_coeff w n j
  rw [sub_mul, coeff_sub, coeff_C_mul, coeff_sub, coeff_C_mul, coeff_C_mul, hc, hc, hc]
  rcases j with _ | i
  · rw [coeff_X_mul_zero]
    simpa [smul_eq_mul, sub_eq_add_neg] using cc_rec_zero w k
  · rw [coeff_X_mul, hc]
    rw [cc_rec_succ w k i]

/-- The recurrence for `L_k^{(w-1)}(x)`. -/
lemma lagL_rec (w x : ℝ) (k : ℕ) :
    ((k : ℝ) + 2) * lagL w (k + 2) x =
      (2 * ((k : ℝ) + 1) + w - x) * lagL w (k + 1) x - ((k : ℝ) + w) * lagL w k x := by
  have := congrArg (Polynomial.eval x) (lagPoly_rec w k)
  simp only [eval_sub, eval_mul, eval_C, eval_X] at this
  simpa [lagL] using this


/-! ### The monic normalisation -/

/-- The monic (in `x`) Laguerre polynomial `(-1)^k k! L_k^{(w-1)}(x)`. -/
noncomputable def lagM (w : ℝ) (k : ℕ) (x : ℝ) : ℝ := (-1) ^ k * (k.factorial : ℝ) * lagL w k x

@[simp] lemma lagM_zero (w x : ℝ) : lagM w 0 x = 1 := by simp [lagM]

lemma lagM_one (w x : ℝ) : lagM w 1 x = x - w := by simp [lagM, lagL_one]

lemma lagM_rec (w x : ℝ) (k : ℕ) :
    lagM w (k + 2) x =
      (x - (2 * ((k : ℝ) + 1) + w)) * lagM w (k + 1) x
        - ((k : ℝ) + 1) * ((k : ℝ) + w) * lagM w k x := by
  have h := lagL_rec w x k
  have hf : ((k + 2).factorial : ℝ) = ((k : ℝ) + 2) * ((k + 1 : ℕ).factorial : ℝ) := by
    rw [Nat.factorial_succ (k + 1)]; push_cast; ring
  have hf' : ((k + 1).factorial : ℝ) = ((k : ℝ) + 1) * (k.factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  simp only [lagM]
  rw [hf, hf']
  have e1 : ((-1 : ℝ)) ^ (k + 2) = (-1) ^ k := by rw [pow_add]; norm_num
  have e2 : ((-1 : ℝ)) ^ (k + 1) = -(-1) ^ k := by rw [pow_succ]; ring
  rw [e1, e2]
  have : ((k : ℝ) + 2) * lagL w (k + 2) x =
      (2 * ((k : ℝ) + 1) + w - x) * lagL w (k + 1) x - ((k : ℝ) + w) * lagL w k x := h
  linear_combination ((-1 : ℝ) ^ k * ((k : ℝ) + 1) * (k.factorial : ℝ)) * this

/-- The paper's monic polynomial `P_k(t) = (-1)^k k! (4π)^{-k} L_k^{(w-1)}(4π t)`
(`dual_spectrum.tex`, Section "The infinite-order derivative limit"). -/
noncomputable def lagP (w : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  lagM w k (4 * Real.pi * t) / (4 * Real.pi) ^ k

lemma lagP_eq (w : ℝ) (k : ℕ) (t : ℝ) :
    lagP w k t = (-1) ^ k * (k.factorial : ℝ) / (4 * Real.pi) ^ k * lagL w k (4 * Real.pi * t) := by
  unfold lagP lagM; ring

@[simp] lemma lagP_zero (w t : ℝ) : lagP w 0 t = 1 := by simp [lagP]

lemma lagP_one (w t : ℝ) : lagP w 1 t = t - w / (4 * Real.pi) := by
  have : (4 * Real.pi) ≠ 0 := by positivity
  simp [lagP, lagM_one]
  field_simp

lemma lagP_rec (w t : ℝ) (k : ℕ) :
    lagP w (k + 2) t =
      (t - (2 * ((k : ℝ) + 1) + w) / (4 * Real.pi)) * lagP w (k + 1) t
        - ((k : ℝ) + 1) * ((k : ℝ) + w) / (4 * Real.pi) ^ 2 * lagP w k t := by
  have hπ : (4 * Real.pi) ≠ 0 := by positivity
  unfold lagP
  rw [lagM_rec]
  simp only [pow_succ]
  field_simp

lemma continuous_lagP (w : ℝ) (k : ℕ) : Continuous (lagP w k) := by
  have h : Continuous (lagL w k) := Polynomial.continuous (p := lagPoly w k)
  unfold lagP lagM
  fun_prop


/-! ### Growth bounds from the recurrence -/

section Bounds

variable {w x : ℝ} {s : ℕ → ℝ}

/-- Lower bound: if `x ≥ 8(n + w)` the ratios `s_{j+1}/s_j` (`j < n`) are at least `x/2`. -/
private lemma seq_ratio (hw : 0 < w) (h0 : s 0 = 1) (h1 : s 1 = x - w)
    (hrec : ∀ k : ℕ, s (k + 2) =
      (x - (2 * ((k : ℝ) + 1) + w)) * s (k + 1) - ((k : ℝ) + 1) * ((k : ℝ) + w) * s k)
    (n : ℕ) (hx : 8 * ((n : ℝ) + w) ≤ x) :
    ∀ j : ℕ, j + 1 ≤ n → 0 ≤ s j ∧ x / 2 * s j ≤ s (j + 1) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hxpos : 0 < x := by linarith
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨by rw [h0]; exact zero_le_one, ?_⟩
    rw [h0, h1]; linarith
  | succ j ih =>
    intro hj
    obtain ⟨hs0, hs1⟩ := ih (by omega)
    have hjn : (j : ℝ) + 2 ≤ n := by exact_mod_cast hj
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hsj1 : 0 ≤ s (j + 1) := by nlinarith
    refine ⟨hsj1, ?_⟩
    rw [hrec j]
    -- `x s_j ≤ 2 s_{j+1}`
    have h2 : x * s j ≤ 2 * s (j + 1) := by nlinarith
    have hA : 2 * ((j : ℝ) + 1) + w ≤ x / 4 := by nlinarith
    have hB : 2 * (((j : ℝ) + 1) * ((j : ℝ) + w)) ≤ x ^ 2 / 32 := by
      have : ((j : ℝ) + 1) * ((j : ℝ) + w) ≤ n * (n + w) := by nlinarith
      nlinarith
    have hC : 0 ≤ x ^ 2 / 2 - (2 * ((j : ℝ) + 1) + w) * x - 2 * (((j : ℝ) + 1) * ((j : ℝ) + w)) := by
      nlinarith
    have hcoef : 0 ≤ ((j : ℝ) + 1) * ((j : ℝ) + w) := by positivity
    -- multiply the target by `x > 0`
    have key : 0 ≤ x * ((x - (2 * ((j : ℝ) + 1) + w)) * s (j + 1)
        - ((j : ℝ) + 1) * ((j : ℝ) + w) * s j - x / 2 * s (j + 1)) := by
      have e : x * ((x - (2 * ((j : ℝ) + 1) + w)) * s (j + 1)
        - ((j : ℝ) + 1) * ((j : ℝ) + w) * s j - x / 2 * s (j + 1))
          = (x ^ 2 / 2 - (2 * ((j : ℝ) + 1) + w) * x) * s (j + 1)
            - ((j : ℝ) + 1) * ((j : ℝ) + w) * (x * s j) := by ring
      rw [e]
      nlinarith [mul_nonneg hC hsj1, mul_le_mul_of_nonneg_left h2 hcoef]
    have := nonneg_of_mul_nonneg_right key hxpos
    linarith

private lemma seq_lower (hw : 0 < w) (h0 : s 0 = 1) (h1 : s 1 = x - w)
    (hrec : ∀ k : ℕ, s (k + 2) =
      (x - (2 * ((k : ℝ) + 1) + w)) * s (k + 1) - ((k : ℝ) + 1) * ((k : ℝ) + w) * s k)
    (n : ℕ) (hx : 8 * ((n : ℝ) + w) ≤ x) : (x / 2) ^ n ≤ s n := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hxpos : 0 < x := by linarith
  have key : ∀ j : ℕ, j ≤ n → (x / 2) ^ j ≤ s j := by
    intro j
    induction j with
    | zero => intro _; simp [h0]
    | succ j ih =>
      intro hj
      have ih' := ih (by omega)
      obtain ⟨_, hr⟩ := seq_ratio hw h0 h1 hrec n hx j hj
      rw [pow_succ, mul_comm]
      calc x / 2 * (x / 2) ^ j ≤ x / 2 * s j := by gcongr
        _ ≤ s (j + 1) := hr
  exact key n le_rfl

/-- Upper bound `|s_n| ≤ (x + (3 + w) n)^n` for `x ≥ 0`. -/
private lemma seq_upper (hw : 0 < w) (hx : 0 ≤ x) (h0 : s 0 = 1) (h1 : s 1 = x - w)
    (hrec : ∀ k : ℕ, s (k + 2) =
      (x - (2 * ((k : ℝ) + 1) + w)) * s (k + 1) - ((k : ℝ) + 1) * ((k : ℝ) + w) * s k)
    (n : ℕ) : |s n| ≤ (x + (3 + w) * n) ^ n := by
  have key : ∀ n : ℕ, |s n| ≤ (x + (3 + w) * n) ^ n ∧
      |s (n + 1)| ≤ (x + (3 + w) * ((n + 1 : ℕ) : ℝ)) ^ (n + 1) := by
    intro n
    induction n with
    | zero =>
      refine ⟨by simp [h0], ?_⟩
      rw [h1]
      simp only [zero_add, Nat.cast_one, mul_one, pow_one]
      rw [abs_le]; constructor <;> linarith
    | succ n ih =>
      obtain ⟨ihn, ihn1⟩ := ih
      refine ⟨ihn1, ?_⟩
      push_cast at ihn1 ⊢
      set A : ℝ := x + (3 + w) * ((n : ℝ) + 1) with hA
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hA1 : (n : ℝ) + 1 ≤ A := by rw [hA]; nlinarith
      have hApos : 0 < A := by linarith
      have hB : |s n| ≤ A ^ n := by
        refine ihn.trans ?_
        gcongr
        rw [hA]; nlinarith
      have hrec' := hrec n
      have hsn2 : |s (n + 2)| ≤ |x - (2 * ((n : ℝ) + 1) + w)| * |s (n + 1)|
          + ((n : ℝ) + 1) * ((n : ℝ) + w) * |s n| := by
        rw [hrec']
        calc _ ≤ |(x - (2 * ((n : ℝ) + 1) + w)) * s (n + 1)| + |((n : ℝ) + 1) * ((n : ℝ) + w) * s n| :=
              abs_sub _ _
          _ = _ := by
              rw [abs_mul, abs_mul, abs_mul]
              congr 2
              rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
      have hxn : |x - (2 * ((n : ℝ) + 1) + w)| ≤ x + (2 * ((n : ℝ) + 1) + w) := by
        rw [abs_le]; constructor <;> nlinarith
      have hmain : (x + (2 * ((n : ℝ) + 1) + w)) * A ^ (n + 1) + ((n : ℝ) + 1) * ((n : ℝ) + w) * A ^ n
          ≤ (A + (3 + w)) ^ (n + 2) := by
        have hq : (x + (2 * ((n : ℝ) + 1) + w)) * A + ((n : ℝ) + 1) * ((n : ℝ) + w) ≤ (A + (3 + w)) ^ 2 := by
          have hxe : x = A - (3 + w) * ((n : ℝ) + 1) := by rw [hA]; ring
          rw [hxe]
          have hD : 0 ≤ (1 + w) * ((n : ℝ) + 1) + 6 + w := by positivity
          nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ A - ((n : ℝ) + 1)) hD,
            mul_nonneg (by linarith : (0 : ℝ) ≤ (n : ℝ) + 1)
              (by positivity : (0 : ℝ) ≤ w * ((n : ℝ) + 1) + 7)]
        have hpow : A ^ n * (A + (3 + w)) ^ 2 ≤ (A + (3 + w)) ^ (n + 2) := by
          rw [pow_add]
          gcongr
          linarith
        calc (x + (2 * ((n : ℝ) + 1) + w)) * A ^ (n + 1) + ((n : ℝ) + 1) * ((n : ℝ) + w) * A ^ n
            = A ^ n * ((x + (2 * ((n : ℝ) + 1) + w)) * A + ((n : ℝ) + 1) * ((n : ℝ) + w)) := by ring
          _ ≤ A ^ n * (A + (3 + w)) ^ 2 := by gcongr
          _ ≤ _ := hpow
      calc |s (n + 2)| ≤ |x - (2 * ((n : ℝ) + 1) + w)| * |s (n + 1)|
            + ((n : ℝ) + 1) * ((n : ℝ) + w) * |s n| := hsn2
        _ ≤ (x + (2 * ((n : ℝ) + 1) + w)) * A ^ (n + 1) + ((n : ℝ) + 1) * ((n : ℝ) + w) * A ^ n := by
            gcongr
        _ ≤ (A + (3 + w)) ^ (n + 2) := hmain
        _ = (x + (3 + w) * ((n : ℝ) + 1 + 1)) ^ (n + 1 + 1) := by rw [hA]; ring_nf
  exact (key n).1

end Bounds

/-- **Lower bound for large `t`** (replaces the zero localisation of `ds:mom`): for `w > 0` and
`t ≥ 2(n + w)/π`, `(t/2)^n ≤ P_n(t)`. -/
theorem lagP_lower {w : ℝ} (hw : 0 < w) (n : ℕ) {t : ℝ} (ht : 2 * ((n : ℝ) + w) / Real.pi ≤ t) :
    (t / 2) ^ n ≤ lagP w n t := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hx : 8 * ((n : ℝ) + w) ≤ 4 * Real.pi * t := by
    rw [div_le_iff₀ hπ] at ht; nlinarith
  have := seq_lower hw (s := fun k => lagM w k (4 * Real.pi * t)) (x := 4 * Real.pi * t)
    (by simp) (by simp [lagM_one]) (fun k => lagM_rec w _ k) n hx
  unfold lagP
  rw [le_div_iff₀ (by positivity)]
  calc (t / 2) ^ n * (4 * Real.pi) ^ n = (4 * Real.pi * t / 2) ^ n := by
        rw [← mul_pow]; congr 1; ring
    _ ≤ _ := this

/-- **Upper bound**: `|P_n(t)| ≤ (t + (3 + w) n/(4π))^n` for `t ≥ 0`. -/
theorem abs_lagP_le {w : ℝ} (hw : 0 < w) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    |lagP w n t| ≤ (t + (3 + w) * n / (4 * Real.pi)) ^ n := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have := seq_upper hw (s := fun k => lagM w k (4 * Real.pi * t)) (x := 4 * Real.pi * t)
    (by positivity) (by simp) (by simp [lagM_one]) (fun k => lagM_rec w _ k) n
  unfold lagP
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (4 * Real.pi) ^ n), div_le_iff₀ (by positivity)]
  calc _ ≤ (4 * Real.pi * t + (3 + w) * n) ^ n := this
    _ = (t + (3 + w) * n / (4 * Real.pi)) ^ n * (4 * Real.pi) ^ n := by
        rw [← mul_pow]; congr 1; field_simp


/-- info: 'FormalResearch.ModularBootstrap.LP.lagL_rec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.LP.lagL_rec

/-- info: 'FormalResearch.ModularBootstrap.LP.lagP_rec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.LP.lagP_rec

/-- info: 'FormalResearch.ModularBootstrap.LP.lagP_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.LP.lagP_lower

/-- info: 'FormalResearch.ModularBootstrap.LP.abs_lagP_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.LP.abs_lagP_le

end FormalResearch.ModularBootstrap.LP
