import FormalResearch.FourQubitEntropy.SpinFlipOddQSum
import FormalResearch.FourQubitEntropy.SpinFlipOddSector

/-!
# Engine of the odd-`n` tradeoff: `π_m + ((n-3)/2) O = 1/2 + Σ oddW_j A_j`

The pointwise generating-function identity `odd_tradeoff_identity` for `n = 2m + 1` with the coefficient `(n-3)/2`,
and the weights `oddW`.  The statement of `thm:odd-spinflip-tradeoff` (sharp coefficient `c_n`, positivity of the
weights, equality case, GHZ) is `SpinFlipTradeoffOddSharp.lean`, which derives it from this identity and `Omean_eq`.
-/

open Polynomial Finset
open FormalResearch.FrameFree.NQubit

namespace FormalResearch.FourQubitEntropy.SpinFlip

section PolyToolkit

/-- `p ↦ p(-X)`. -/
noncomputable def sgm (p : ℝ[X]) : ℝ[X] := p.comp (-X)

theorem coeff_sgm (p : ℝ[X]) (j : ℕ) : (sgm p).coeff j = (-1) ^ j * p.coeff j := by
  unfold sgm
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [add_comp, hp, hq, mul_add]
  | monomial k a =>
    rw [← C_mul_X_pow_eq_monomial]
    have h1 : (-X : ℝ[X]) = C (-1) * X := by simp
    simp only [mul_comp, C_comp, pow_comp, X_comp]
    rw [h1, mul_pow, ← C_pow, ← mul_assoc, ← C_mul, coeff_C_mul, coeff_C_mul, coeff_X_pow]
    by_cases h : j = k
    · subst h; simp; ring
    · simp [h]

/-- `x = (1 + X) / 2`. -/
noncomputable def xp : ℝ[X] := C (1 / 2) * (1 + X)

theorem coeff_xp_pow (k j : ℕ) : (xp ^ k).coeff j = (1 / 2 : ℝ) ^ k * (k.choose j : ℝ) := by
  unfold xp
  rw [mul_pow, ← C_pow, coeff_C_mul, coeff_one_add_X_pow]

theorem sgm_pow (p : ℝ[X]) (k : ℕ) : sgm (p ^ k) = (sgm p) ^ k := by
  unfold sgm; rw [pow_comp]

theorem coeff_sub_one_pow (m i : ℕ) : ((1 - X : ℝ[X]) ^ m).coeff i = (-1) ^ i * (m.choose i : ℝ) := by
  have : (1 - X : ℝ[X]) ^ m = sgm ((1 + X) ^ m) := by
    simp [sgm, pow_comp, sub_eq_add_neg]
  rw [this, coeff_sgm, coeff_one_add_X_pow]

/-- `[X^{2i+1}] X (1 - X²)^m = (-1)^i C(m,i)`. -/
theorem coeff_Tpoly (m i : ℕ) : (X * (1 - X ^ 2 : ℝ[X]) ^ m).coeff (2 * i + 1) = (-1) ^ i * (m.choose i : ℝ) := by
  rw [coeff_X_mul]
  have h : (1 - X ^ 2 : ℝ[X]) ^ m = expand ℝ 2 ((1 - X) ^ m) := by
    simp [map_pow, map_sub, expand_X]
  rw [h, coeff_expand (by norm_num)]
  simp [coeff_sub_one_pow]

/-- Coefficient numerator `N_j^{(n)}`, `n = 2m+1`, of `thm:odd-spinflip-tradeoff`. -/
noncomputable def oddNum (m j : ℕ) : ℝ :=
  2 ^ m * ((m.choose (j - 1) : ℝ) + 3 * (m.choose j : ℝ))
    + (-1) ^ ((2 * m + 1 - j) / 2) * (m.choose ((2 * m + 1 - j) / 2) : ℝ)
    + (2 * (m : ℝ) - 2) * ((2 * m).choose j : ℝ) - ((2 * m + 1).choose j : ℝ)

/-- The weight `w_j^{(n)}` (`eq:odd-tradeoff-weights`), `n = 2m+1`. -/
noncomputable def oddW (m j : ℕ) : ℝ :=
  oddNum m j / (2 ^ (2 * m + 1) * ((2 * m + 1).choose j : ℝ))

noncomputable def tcoef (m : ℕ) : ℝ := (-1) ^ m / (2 * 4 ^ m)

noncomputable def Gp (m : ℕ) : ℝ[X] :=
  xp ^ m + xp ^ (m + 1) + C ((2 * (m : ℝ) - 2) / 2) * xp ^ (2 * m) - xp ^ (2 * m + 1)
    + C (tcoef m) * (X * (1 - X ^ 2) ^ m)

noncomputable def Wcl (m : ℕ) : ℝ[X] := C (1 / 2) * (Gp m - sgm (Gp m))

theorem coeff_Wcl_odd (m i : ℕ) (hi : i ≤ m) :
    (Wcl m).coeff (2 * i + 1) = oddNum m (2 * i + 1) / 2 ^ (2 * m + 1) := by
  unfold Wcl
  rw [coeff_C_mul, coeff_sub, coeff_sgm]
  have hodd : ((-1 : ℝ)) ^ (2 * i + 1) = -1 := by rw [pow_succ, pow_mul]; simp
  rw [hodd]
  unfold Gp
  simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_xp_pow, coeff_Tpoly]
  have e1 : 2 * m + 1 - (2 * i + 1) = 2 * (m - i) := by omega
  have e2 : 2 * (m - i) / 2 = m - i := by omega
  unfold oddNum
  rw [e1, e2, Nat.add_sub_cancel]
  have hs : (-1 : ℝ) ^ (m - i) = (-1) ^ m * (-1) ^ i := by
    have h1 : (-1 : ℝ) ^ (m - i) * (-1) ^ i = (-1) ^ m := by
      rw [← pow_add, Nat.sub_add_cancel hi]
    have h2 : ((-1 : ℝ) ^ i) * (-1) ^ i = 1 := by rw [← mul_pow]; simp
    linear_combination ((-1 : ℝ) ^ i) * h1 - ((-1) ^ (m - i)) * h2
  have hc : m.choose (m - i) = m.choose i := Nat.choose_symm hi
  have hsucc : ((m + 1).choose (2 * i + 1) : ℝ) = (m.choose (2 * i) : ℝ) + (m.choose (2 * i + 1) : ℝ) := by
    exact_mod_cast Nat.choose_succ_succ m (2 * i)
  rw [hs, hc, hsucc]
  unfold tcoef
  have hu : (0 : ℝ) < 2 ^ m := by positivity
  generalize hU : (2 : ℝ) ^ m = u at hu
  have h4 : (4 : ℝ) ^ m = u ^ 2 := by rw [← hU, ← pow_mul, mul_comm, pow_mul]; norm_num
  have p1 : (1 / 2 : ℝ) ^ m = 1 / u := by rw [one_div_pow, hU]
  have p2 : (1 / 2 : ℝ) ^ (m + 1) = 1 / (2 * u) := by rw [one_div_pow, pow_succ, hU]; ring
  have p3 : (1 / 2 : ℝ) ^ (2 * m) = 1 / u ^ 2 := by rw [one_div_pow, pow_mul', hU]
  have p4 : (1 / 2 : ℝ) ^ (2 * m + 1) = 1 / (2 * u ^ 2) := by rw [one_div_pow, pow_succ, pow_mul', hU]; ring
  have p5 : (2 : ℝ) ^ (2 * m + 1) = 2 * u ^ 2 := by rw [pow_succ, pow_mul', hU]; ring
  rw [h4, p1, p2, p3, p4, p5]
  field_simp
  ring

end PolyToolkit

section PointwiseIdentity

/-- The real function `g(x)` behind `Gp`. -/
noncomputable def Ge (m : ℕ) (x : ℝ) : ℝ :=
  x ^ m + x ^ (m + 1) + ((2 * (m : ℝ) - 2) / 2) * x ^ (2 * m) - x ^ (2 * m + 1)
    + ((-1) ^ m / 2) * (2 * x - 1) * x ^ m * (1 - x) ^ m

theorem eval_xp (y : ℝ) : xp.eval y = (1 + y) / 2 := by
  simp [xp]; ring

theorem eval_sgm (p : ℝ[X]) (y : ℝ) : (sgm p).eval y = p.eval (-y) := by
  simp [sgm, eval_comp]

theorem eval_Gp (m : ℕ) (y : ℝ) : (Gp m).eval y = Ge m ((1 + y) / 2) := by
  have hx : (2 * ((1 + y) / 2) - 1) = y := by ring
  have hv : (1 - (1 + y) / 2) = (1 - y) / 2 := by ring
  unfold Gp Ge
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_xp, eval_X, eval_one]
  rw [hx, hv]
  have hxv : ((1 + y) / 2) ^ m * ((1 - y) / 2) ^ m = (1 - y ^ 2) ^ m / 4 ^ m := by
    rw [← mul_pow, ← div_pow]; congr 1; ring
  have : tcoef m * (y * (1 - y ^ 2) ^ m)
      = (-1) ^ m / 2 * y * ((1 + y) / 2) ^ m * ((1 - y) / 2) ^ m := by
    rw [mul_assoc ((-1) ^ m / 2 * y), hxv]
    unfold tcoef
    have : (4 : ℝ) ^ m ≠ 0 := by positivity
    have : (2 : ℝ) * 4 ^ m ≠ 0 := by positivity
    field_simp
  rw [this]

/-- `P_O = ½ (x^{n-1} - (1-x)^{n-1})`, the generating polynomial of `O`. -/
noncomputable def POp (m : ℕ) : ℝ[X] := C (1 / 2) * (xp ^ (2 * m) - sgm (xp ^ (2 * m)))

/-- The left-hand side of the generating-function identity of `thm:odd-spinflip-tradeoff`. -/
noncomputable def LHSp (m : ℕ) : ℝ[X] :=
  xp ^ m + C ((2 * (m : ℝ) - 2) / 2) * POp m - C (1 / 2)
    - ∑ s ∈ range (m + 1), C (qc ℝ m s / 2) * (xp ^ s - xp ^ (2 * m + 1 - s))

/-- **The polynomial identity** in the proof of `thm:odd-spinflip-tradeoff`. -/
theorem LHSp_eq_Wcl (m : ℕ) : LHSp m = Wcl m := by
  apply Polynomial.funext
  intro y
  have hsum := qSum_eq ((1 + y) / 2) m
  have hv : (1 + -y) / 2 = 1 - (1 + y) / 2 := by ring
  have hy : 1 - (1 + y) / 2 = (1 - y) / 2 := by ring
  have h1 : ∑ s ∈ range (m + 1), (qc ℝ m s / 2) * (((1 + y) / 2) ^ s - ((1 + y) / 2) ^ (2 * m + 1 - s))
      = (1 / 2) * ∑ s ∈ range (m + 1), qc ℝ m s * (((1 + y) / 2) ^ s - ((1 + y) / 2) ^ (2 * m + 1 - s)) := by
    rw [mul_sum]; exact sum_congr rfl fun s _ => by ring
  simp only [LHSp, POp, Wcl, eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_xp, eval_sgm,
    eval_Gp, eval_finsetSum, h1, hsum, hv]
  unfold Ge
  rw [hy]
  ring

end PointwiseIdentity

section WithPsi

variable {m : ℕ}

/-- `Λ g = Σ_{j ≤ n} [X^j] g · B_j`, `B_j = A_j / C(n,j)` (`n = 2m+1`). -/
noncomputable def Lam (ψ : Ψ (2 * m + 1)) : ℝ[X] →ₗ[ℝ] ℝ :=
  ∑ j ∈ range (2 * m + 1 + 1), (A ψ j / ((2 * m + 1).choose j : ℝ)) • Polynomial.lcoeff ℝ j

theorem Lam_apply (ψ : Ψ (2 * m + 1)) (g : ℝ[X]) :
    Lam ψ g = ∑ j ∈ range (2 * m + 1 + 1), g.coeff j * (A ψ j / ((2 * m + 1).choose j : ℝ)) := by
  unfold Lam
  simp [LinearMap.sum_apply, mul_comm]

theorem Lam_xp_pow (ψ : Ψ (2 * m + 1)) {s : ℕ} (hs : s ≤ 2 * m + 1) :
    Lam ψ (xp ^ s) = purMean ψ s := by
  rw [Lam_apply, PurAvg_eq ψ hs]
  exact sum_congr rfl fun j _ => by rw [coeff_xp_pow]

theorem Lam_C (ψ : Ψ (2 * m + 1)) (c : ℝ) : Lam ψ (C c) = c * A ψ 0 := by
  rw [Lam_apply, sum_range_succ']
  simp [coeff_C]

theorem Lam_POp (ψ : Ψ (2 * m + 1)) : Lam ψ (POp m) = Omean ψ := by
  rw [Omean_eq (by omega) ψ, Lam_apply]
  refine sum_congr rfl fun j hj => ?_
  have hjn : j ≤ 2 * m + 1 := Nat.lt_succ_iff.mp (mem_range.mp hj)
  have hCj : ((2 * m + 1).choose j : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hjn).ne'
  unfold POp
  rw [coeff_C_mul, coeff_sub, coeff_sgm, coeff_xp_pow]
  have key : ((2 * m).choose j : ℝ) * ((2 * m + 1 : ℕ) : ℝ)
      = ((2 * m + 1).choose j : ℝ) * (((2 * m + 1 : ℕ) : ℝ) - j) := by
    have := Nat.choose_mul_succ_eq (2 * m) j
    have h2 : ((2 * m + 1 - j : ℕ) : ℝ) = ((2 * m + 1 : ℕ) : ℝ) - j := by
      rw [Nat.cast_sub hjn]
    rw [← h2]; exact_mod_cast this
  have hn : ((2 * m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  by_cases hj2 : Odd j
  · have : (-1 : ℝ) ^ j = -1 := hj2.neg_one_pow
    rw [this]
    simp only [hj2, ite_true, Nat.add_sub_cancel]
    field_simp
    have hp : (1 / 2 : ℝ) ^ (2 * m) * 2 ^ (2 * m) = 1 := by rw [← mul_pow]; norm_num
    linear_combination (2 * A ψ j * ((2 * m).choose j : ℝ) * ((2 * m + 1 : ℕ) : ℝ)) * hp
      + 2 * A ψ j * key
  · have : (-1 : ℝ) ^ j = 1 := (Nat.not_odd_iff_even.mp hj2).neg_one_pow
    rw [this]; simp [hj2]

theorem Lam_Wcl (ψ : Ψ (2 * m + 1)) :
    Lam ψ (Wcl m) = ∑ j ∈ range (2 * m + 1 + 1), (if Odd j then oddW m j else 0) * A ψ j := by
  rw [Lam_apply]
  refine sum_congr rfl fun j hj => ?_
  have hjn : j ≤ 2 * m + 1 := Nat.lt_succ_iff.mp (mem_range.mp hj)
  have hCj : ((2 * m + 1).choose j : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hjn).ne'
  by_cases hj2 : Odd j
  · obtain ⟨i, rfl⟩ := hj2
    rw [coeff_Wcl_odd m i (by omega)]
    simp only [odd_two_mul_add_one, ite_true]
    unfold oddW
    have : (2 : ℝ) ^ (2 * m + 1) ≠ 0 := by positivity
    field_simp
  · have : (-1 : ℝ) ^ j = 1 := (Nat.not_odd_iff_even.mp hj2).neg_one_pow
    simp only [hj2, ite_false, zero_mul]
    unfold Wcl
    rw [coeff_C_mul, coeff_sub, coeff_sgm, this]
    simp

theorem purMean_compl (ψ : Ψ (2 * m + 1)) {s : ℕ} (hs : s ≤ 2 * m + 1) :
    purMean ψ (2 * m + 1 - s) = purMean ψ s := by
  unfold purMean
  rw [← Pur_compl ψ s hs, Nat.choose_symm hs]

/-- **`thm:odd-spinflip-tradeoff`, the identity, for every odd `n = 2m+1`.**
`π_m + (n-3)/2 · O = 1/2 + Σ_{j odd} w_j^{(n)} A_j` (the `j = n` term has `w_n = 0`). -/
theorem odd_tradeoff_identity (ψ : Ψ (2 * m + 1)) (hψ : nsq ψ = 1) :
    purMean ψ m + ((((2 * m + 1 : ℕ) : ℝ) - 3) / 2) * Omean ψ
      = 1 / 2 + ∑ j ∈ range (2 * m + 1 + 1), (if Odd j then oddW m j else 0) * A ψ j := by
  have h := congrArg (Lam ψ) (LHSp_eq_Wcl m)
  rw [Lam_Wcl] at h
  have hA0 := A_zero ψ
  rw [hψ] at hA0
  have hs : ∀ s ∈ range (m + 1),
      Lam ψ (C (qc ℝ m s / 2) * (xp ^ s - xp ^ (2 * m + 1 - s))) = 0 := by
    intro s hs
    have hsm : s ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hs)
    rw [← smul_eq_C_mul, map_smul, map_sub, Lam_xp_pow ψ (by omega), Lam_xp_pow ψ (by omega),
      purMean_compl ψ (by omega)]
    simp
  unfold LHSp at h
  rw [map_sub, map_sub, map_add, ← smul_eq_C_mul (a := (2 * (m : ℝ) - 2) / 2), map_smul,
    Lam_xp_pow ψ (by omega), Lam_POp, Lam_C, map_sum, sum_congr rfl hs] at h
  simp only [sum_const_zero, sub_zero, smul_eq_mul, hA0] at h
  push_cast at h ⊢
  linarith

end WithPsi

section Positivity

theorem oddNum_top (m : ℕ) (hm : 1 ≤ m) : oddNum m (2 * m + 1) = 0 := by
  unfold oddNum
  have h1 : m.choose (2 * m + 1 - 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  have h2 : m.choose (2 * m + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  have h3 : (2 * m).choose (2 * m + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  rw [h1, h2, h3, Nat.sub_self, Nat.zero_div]
  simp

theorem oddNum_two_one : oddNum 2 1 = 32 := by
  norm_num [oddNum, Nat.choose]

theorem oddNum_two_three : oddNum 2 3 = 0 := by
  norm_num [oddNum, Nat.choose]

/-- `N_{n-2}^{(n)} = 2m(m-3)` for `n = 2m+1`, `m ≥ 3`. -/
theorem oddNum_last (m : ℕ) (hm : 3 ≤ m) : oddNum m (2 * m - 1) = 2 * m * (m - 3) := by
  unfold oddNum
  have e1 : 2 * m + 1 - (2 * m - 1) = 2 := by omega
  have h1 : m.choose (2 * m - 1 - 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  have h2 : m.choose (2 * m - 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  have h3 : (2 * m).choose (2 * m - 1) = 2 * m :=
    (Nat.choose_symm (n := 2 * m) (k := 1) (by omega)).trans (by simp)
  have h4 : (2 * m + 1).choose (2 * m - 1) = m * (2 * m + 1) := by
    have h := Nat.choose_symm (n := 2 * m + 1) (k := 2) (by omega)
    rw [show 2 * m + 1 - 2 = 2 * m - 1 by omega] at h
    rw [h, Nat.choose_two_right]
    have : (2 * m + 1) * (2 * m + 1 - 1) = 2 * (m * (2 * m + 1)) := by
      rw [Nat.add_sub_cancel]; ring
    rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
  rw [e1, h1, h2, h3, h4]
  push_cast
  norm_num
  ring

theorem choose_le_choose_double (m k : ℕ) (hk : k ≤ m) (hk1 : 1 ≤ k) :
    m.choose k ≤ (2 * m + 1).choose (2 * k) := by
  have hV : m.choose k * m.choose k ≤ (m + m).choose (k + k) := by
    rw [Nat.add_choose_eq]
    have hmem : (k, k) ∈ Finset.HasAntidiagonal.antidiagonal (k + k) := by simp
    exact Finset.single_le_sum (f := fun ij : ℕ × ℕ => m.choose ij.1 * m.choose ij.2)
      (fun _ _ => Nat.zero_le _) hmem
  have hpos : 1 ≤ m.choose k := Nat.choose_pos hk
  have h1 : m.choose k ≤ m.choose k * m.choose k := Nat.le_mul_of_pos_left _ hpos
  have h2 : (m + m).choose (k + k) ≤ (2 * m + 1).choose (2 * k) := by
    obtain ⟨a, ha⟩ : ∃ a, 2 * k = a + 1 := ⟨2 * k - 1, by omega⟩
    rw [ha, show 2 * m + 1 = 2 * m + 1 from rfl, Nat.choose_succ_succ]
    rw [show m + m = 2 * m by ring, show k + k = 2 * k by ring, ha]
    exact Nat.le_add_left _ _
  exact h1.trans (hV.trans h2)

/-- `oddW m (n) = 0` (the `j = n` term of the identity vanishes). -/
theorem oddW_top (m : ℕ) (hm : 1 ≤ m) : oddW m (2 * m + 1) = 0 := by
  unfold oddW; rw [oddNum_top m hm]; simp

end Positivity

end FormalResearch.FourQubitEntropy.SpinFlip
