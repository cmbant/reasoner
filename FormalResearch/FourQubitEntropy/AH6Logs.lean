import FormalResearch.FourQubitEntropy.AH6Enc

/-!
# Enclosures of logarithms by the `atanh` series

`log ((1+z)/(1-z)) = ∑_{k<N} 2 z^{2k+1}/(2k+1) + ρ`, `|ρ| ≤ 2 w^{2N+1}/(1-w²)` for `|z| ≤ w < 1`
(`log_atanh_err`).  `lnB Z N` is the corresponding ball: the partial sum computed in ball arithmetic plus a ball of
radius `2 w^{2N+1}/(1-w²)` with `w` an upper bound of `|z|` read off `Z`; `lnB_enc` is its soundness.
-/

namespace FormalResearch.FourQubitEntropy.AH6

section Generic

variable {α : Type} [Add α] [Mul α] [Neg α] [Inv α] [IntCast α]

/-- `∑_{j<n} 2 t_j/(2(k+j)+1)` with `t_{j+1} = t_j z²`: the partial sums of `2 atanh z`. -/
def atanhLoop (z2 : α) : ℕ → ℕ → α → α
  | 0, _, _ => ic 0
  | n + 1, k, t => ic 2 * t * (ic ((2 * k + 1 : ℕ) : ℤ))⁻¹ + atanhLoop z2 n (k + 1) (t * z2)

def powG (b : α) : ℕ → α
  | 0 => ic 1
  | n + 1 => b * powG b n

end Generic

theorem powG_real (b : ℝ) (n : ℕ) : powG b n = b ^ n := by
  induction n with
  | zero => simp [powG]
  | succ n ih => simp [powG, ih, pow_succ, mul_comm]

theorem powG_enc {b : ℝ} {B : Ball} (hb : Enc b B) (n : ℕ) : Enc (powG b n) (powG B n) := by
  induction n with
  | zero => exact Enc.ic 1
  | succ n ih => exact Enc.mul hb ih

theorem atanhLoop_enc {z2 : ℝ} {Z2 : Ball} (hz : Enc z2 Z2) (N k : ℕ) {t : ℝ} {T : Ball}
    (ht : Enc t T) : Enc (atanhLoop z2 N k t) (atanhLoop Z2 N k T) := by
  induction N generalizing k t T with
  | zero => exact Enc.ic 0
  | succ N ih =>
    exact Enc.add (Enc.mul (Enc.mul (Enc.ic 2) ht) (Enc.inv (Enc.ic _))) (ih (k + 1) (Enc.mul ht hz))

theorem atanhLoop_real (z : ℝ) (N k : ℕ) :
    atanhLoop (z * z) N k (z ^ (2 * k + 1)) =
      ∑ j ∈ Finset.range N, 2 * (1 / (2 * ((k + j : ℕ) : ℝ) + 1)) * z ^ (2 * (k + j) + 1) := by
  induction N generalizing k with
  | zero => simp [atanhLoop]
  | succ N ih =>
    rw [Finset.sum_range_succ', atanhLoop]
    have h1 : z ^ (2 * k + 1) * (z * z) = z ^ (2 * (k + 1) + 1) := by ring
    rw [h1, ih (k + 1)]
    simp only [ic_real]
    have h2 : (((2 * k + 1 : ℕ) : ℤ) : ℝ) = 2 * (k : ℝ) + 1 := by push_cast; ring
    rw [h2]
    have h3 : ∀ j : ℕ, 2 * (1 / (2 * ((k + 1 + j : ℕ) : ℝ) + 1)) * z ^ (2 * (k + 1 + j) + 1) =
        2 * (1 / (2 * ((k + (j + 1) : ℕ) : ℝ) + 1)) * z ^ (2 * (k + (j + 1)) + 1) := by
      intro j; congr 3 <;> push_cast <;> ring
    simp only [h3]
    simp
    ring

/-- The remainder of the `atanh` series. -/
theorem log_atanh_err {z w : ℝ} (hz : |z| ≤ w) (hw : w < 1) (N : ℕ) :
    |Real.log ((1 + z) / (1 - z)) -
        ∑ j ∈ Finset.range N, 2 * (1 / (2 * (j : ℝ) + 1)) * z ^ (2 * j + 1)| ≤
      2 * w ^ (2 * N + 1) / (1 - w ^ 2) := by
  have hz1 : |z| < 1 := lt_of_le_of_lt hz hw
  have hw0 : 0 ≤ w := le_trans (abs_nonneg _) hz
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one hz1
  have hlog : Real.log ((1 + z) / (1 - z)) = Real.log (1 + z) - Real.log (1 - z) := by
    have h1 : 1 + z ≠ 0 := by have := abs_lt.mp hz1; linarith
    have h2 : 1 - z ≠ 0 := by have := abs_lt.mp hz1; linarith
    exact Real.log_div h1 h2
  rw [hlog]
  have hT := (hasSum_nat_add_iff' N).mpr hs
  have hw2 : w ^ 2 < 1 := by nlinarith
  have hg : HasSum (fun k : ℕ => 2 * w ^ (2 * N + 1) * (w ^ 2) ^ k)
      (2 * w ^ (2 * N + 1) / (1 - w ^ 2)) := by
    have := (hasSum_geometric_of_lt_one (by positivity) hw2).mul_left (2 * w ^ (2 * N + 1))
    simpa [div_eq_mul_inv] using this
  have := hT.norm_le_of_bounded hg ?_
  · simpa [Real.norm_eq_abs] using this
  · intro k
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow]
    have h1 : |(2 : ℝ)| = 2 := abs_of_pos (by norm_num)
    have h2 : |1 / (2 * ((k + N : ℕ) : ℝ) + 1)| ≤ 1 := by
      rw [abs_of_pos (by positivity), div_le_one (by positivity)]
      have : (0 : ℝ) ≤ ((k + N : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    have h3 : |z| ^ (2 * (k + N) + 1) ≤ w ^ (2 * (k + N) + 1) := pow_le_pow_left₀ (abs_nonneg _) hz _
    have h4 : w ^ (2 * (k + N) + 1) = w ^ (2 * N + 1) * (w ^ 2) ^ k := by ring
    rw [h1]
    calc 2 * |1 / (2 * ((k + N : ℕ) : ℝ) + 1)| * |z| ^ (2 * (k + N) + 1)
        ≤ 2 * 1 * w ^ (2 * (k + N) + 1) := by gcongr
      _ = 2 * w ^ (2 * N + 1) * (w ^ 2) ^ k := by rw [h4]; ring

/-- The ball enclosing `log((1+z)/(1-z))`. -/
def lnB (z : Ball) (N : ℕ) : Ball :=
  let zbar : Ball := ⟨(z.m.natAbs + z.r : ℕ), 0, z.ok⟩
  let den : Ball := ic 1 + -(zbar * zbar)
  let t : Ball := ic 2 * powG zbar (2 * N + 1) * den⁻¹
  atanhLoop (z * z) N 0 z + ⟨0, t.m.natAbs + t.r, z.ok && t.ok && den.pos⟩

theorem lnB_enc {z : ℝ} {Z : Ball} (hz : Enc z Z) (N : ℕ) :
    Enc (Real.log ((1 + z) / (1 - z))) (lnB Z N) := by
  intro hok
  set zbar : Ball := ⟨(Z.m.natAbs + Z.r : ℕ), 0, Z.ok⟩ with hzbar
  set den : Ball := ic 1 + -(zbar * zbar) with hden
  set t : Ball := ic 2 * powG zbar (2 * N + 1) * den⁻¹ with ht
  have hA : Enc (atanhLoop (z * z) N 0 z) (atanhLoop (Z * Z) N 0 Z) :=
    atanhLoop_enc (Enc.mul hz hz) N 0 hz
  -- the ok flags
  have hok' : (atanhLoop (Z * Z) N 0 Z).ok = true ∧ (Z.ok && t.ok && den.pos) = true := by
    have h0 : ((atanhLoop (Z * Z) N 0 Z).ok &&
        (Z.ok && t.ok && den.pos)) = true := hok
    exact Bool.and_eq_true_iff.mp h0
  obtain ⟨hokA, hok2⟩ := hok'
  have hok3 : (Z.ok && t.ok) = true ∧ den.pos = true := Bool.and_eq_true_iff.mp hok2
  have hok4 : Z.ok = true ∧ t.ok = true := Bool.and_eq_true_iff.mp hok3.1
  obtain ⟨hZok, htok⟩ := hok4
  have hdenpos := hok3.2
  have hSC := SC_real_pos
  -- w
  set w : ℝ := ((Z.m.natAbs + Z.r : ℕ) : ℝ) / SC with hw
  have hzbarEnc : Enc w zbar := by
    intro _
    show |w * (SC : ℝ) - (((Z.m.natAbs + Z.r : ℕ) : ℤ) : ℝ)| ≤ ((0 : ℕ) : ℝ)
    rw [hw]; field_simp; simp
  have hzw : |z| ≤ w := by
    have h1 := hz hZok
    have h2 : |z * (SC : ℝ)| ≤ ((Z.m.natAbs + Z.r : ℕ) : ℝ) := by
      calc |z * (SC : ℝ)| = |(z * SC - Z.m) + Z.m| := by ring_nf
        _ ≤ |z * SC - Z.m| + |(Z.m : ℝ)| := abs_add_le _ _
        _ ≤ (Z.r : ℝ) + (Z.m.natAbs : ℝ) := by
          refine add_le_add h1 ?_
          rw [Nat.cast_natAbs]; simp
        _ = _ := by push_cast; ring
    rw [abs_mul, abs_of_pos hSC] at h2
    rw [hw, le_div_iff₀ hSC]; exact h2
  have hdenEnc : Enc (1 + -(w * w)) den := by
    rw [hden]; enc
  have hden0 : 0 < 1 + -(w * w) := Enc.pos hdenEnc hdenpos
  have hw1 : w < 1 := by
    have hw0 : 0 ≤ w := le_trans (abs_nonneg _) hzw
    nlinarith
  have htEnc : Enc (2 * w ^ (2 * N + 1) * (1 + -(w * w))⁻¹) t := by
    have h := Enc.mul (Enc.mul (Enc.ic 2) (powG_enc hzbarEnc (2 * N + 1))) (Enc.inv hdenEnc)
    rw [powG_real] at h
    simpa [ht] using h
  have htb := htEnc htok
  have hτ : 2 * w ^ (2 * N + 1) * (1 + -(w * w))⁻¹ * (SC : ℝ) ≤ ((t.m.natAbs + t.r : ℕ) : ℝ) := by
    rw [abs_le] at htb
    have : (t.m : ℝ) ≤ (t.m.natAbs : ℝ) := by
      rw [Nat.cast_natAbs]; exact_mod_cast le_abs_self t.m
    push_cast; linarith [htb.2]
  have herr := log_atanh_err hzw hw1 N
  have hτ' : 2 * w ^ (2 * N + 1) / (1 - w ^ 2) = 2 * w ^ (2 * N + 1) * (1 + -(w * w))⁻¹ := by
    rw [div_eq_mul_inv]; congr 2; ring
  rw [hτ'] at herr
  -- assemble
  have hrho : Enc (Real.log ((1 + z) / (1 - z)) -
      ∑ j ∈ Finset.range N, 2 * (1 / (2 * (j : ℝ) + 1)) * z ^ (2 * j + 1))
      (⟨0, t.m.natAbs + t.r, Z.ok && t.ok && den.pos⟩ : Ball) := by
    intro _
    show |_ * (SC : ℝ) - ((0 : ℤ) : ℝ)| ≤ ((t.m.natAbs + t.r : ℕ) : ℝ)
    rw [Int.cast_zero, sub_zero, abs_mul, abs_of_pos hSC]
    calc _ ≤ 2 * w ^ (2 * N + 1) * (1 + -(w * w))⁻¹ * (SC : ℝ) :=
          mul_le_mul_of_nonneg_right herr hSC.le
      _ ≤ _ := hτ
  have hS := hA
  have hR := atanhLoop_real z N 0
  simp only [mul_zero, zero_add, pow_one] at hR
  rw [hR] at hS
  have := Enc.add hS hrho
  simp only [add_sub_cancel] at this
  exact this hok

end FormalResearch.FourQubitEntropy.AH6
