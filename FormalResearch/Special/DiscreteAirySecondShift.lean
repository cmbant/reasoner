module

public import FormalResearch.Special.DiscreteAirySecondDefect

/-!
# Second-order Airy parametrix, part 11: the shifted form `g · y(X + h^{4/3} q₁/g)` (Q4, pointwise part)

The paper's two forms of the second-order parametrix are `(g + h² p) y(X) + h^{4/3} q₁ y'(X)` (`a2Psi`, `X = ζ/δ²`, `h = δ³`) and
`g · y(X + h^{4/3} B)`, `B = q₁/g` (so `h^{4/3} B = δ⁴ B`).  With `p = ζ q₁²/(2 g)` they agree up to `O(h³)` in the Airy envelope.

* `a2_taylor_seg`: for `y'' = x y` and a segment `[X, X+s]` on which `|y + x y'| ≤ M`:
  `|y(X+s) - (y + y' s + X y s²/2)| ≤ M |s|³` (`y''' = y + x y'`);
* `a2_nbr`: the neighbour constant `w X' ≤ (6/5) e^{c√(1+B)} w X` for any weight with local constancy (`airyWt`, `airyBiWt`);
* `a2_shift_rem`: the remainder `|y(X+s) - (y + y' s + X y s²/2)| ≤ C_w (C_y + (|X|+1) C_{y'} √(3+|X|)) w(X) |s|³`
  whenever `|s| ≤ 1`, `|s|√(1+|X|) ≤ 1`.

**Claim class: proved.**  The lattice form (`airy2_shifted_defect`) is in `DiscreteAirySecondShiftLattice`.
-/

@[expose] public section

open Set FormalResearch.DiscreteAiry

namespace FormalResearch.Special

open SturmAiry

/-- **Taylor remainder of order 3 for `y'' = x y`** on a segment with `|y + x y'| ≤ M`. -/
lemma a2_taylor_seg {y y' : ℝ → ℝ} (hy : IsAirySol y y') {X s M : ℝ}
    (hb : ∀ t ∈ uIcc 0 s, |y (X + t) + (X + t) * y' (X + t)| ≤ M) :
    |y (X + s) - (y X + y' X * s + X * y X * s ^ 2 / 2)| ≤ M * |s| ^ 3 := by
  let Fk : ℕ → ℝ → ℝ := fun k => match k with
    | 0 => y | 1 => y' | 2 => fun x => x * y x | _ => fun x => y x + x * y' x
  have h := apx_taylor_chain 3 Fk X s M (fun k hk t _ => by
      interval_cases k
      · exact (hy _).1
      · exact (hy _).2
      · have := (hasDerivAt_id (X + t)).mul (hy (X + t)).1
        exact this.congr_deriv (by simp [Fk])) (fun t ht => hb t ht) s right_mem_uIcc
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Fk, Nat.factorial] at h
  norm_num at h
  convert h using 2

/-- **Local constancy of a weight at lattice scale** (the proof of `dal_airyWt_nbr`, for any weight with the
`airyWt_le_of_close` property). -/
lemma a2_nbr {w : ℝ → ℝ}
    (hnb : ∀ {X ξ Λ : ℝ}, |ξ - X| ≤ 1 → |ξ - X| * √(1 + |X|) ≤ Λ → w ξ ≤ 6 / 5 * Real.exp Λ * w X)
    {X X' c2 B δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hc2 : 0 ≤ c2) (hc2δ : c2 * δ ≤ 1)
    (hX : |X| ≤ B / δ ^ 2) (hB : 0 ≤ B) (hd : |X' - X| ≤ c2 * δ) :
    w X' ≤ 6 / 5 * Real.exp (c2 * √(1 + B)) * w X := by
  refine hnb (hd.trans hc2δ) ?_
  have h1 : |X' - X| * √(1 + |X|) ≤ c2 * δ * √(1 + B / δ ^ 2) :=
    mul_le_mul hd (Real.sqrt_le_sqrt (by linarith)) (Real.sqrt_nonneg _) (by positivity)
  refine h1.trans ?_
  have h2 : δ * √(1 + B / δ ^ 2) = √(δ ^ 2 + B) := by
    have : (δ ^ 2 + B) = δ ^ 2 * (1 + B / δ ^ 2) := by field_simp
    rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq hδ.le]
  have h3 : √(δ ^ 2 + B) ≤ √(1 + B) := Real.sqrt_le_sqrt (by nlinarith)
  calc c2 * δ * √(1 + B / δ ^ 2) = c2 * (δ * √(1 + B / δ ^ 2)) := by ring
    _ = c2 * √(δ ^ 2 + B) := by rw [h2]
    _ ≤ c2 * √(1 + B) := mul_le_mul_of_nonneg_left h3 hc2

/-- **The shifted-argument remainder** `y(X+s) - (y + y' s + X y s²/2) = O(|s|³ (1+|X|)^{3/2} w(X))`. -/
lemma a2_shift_rem {y y' w : ℝ → ℝ} (hy : IsAirySol y y') {Cy Cy' Cw : ℝ} (hCy : 0 ≤ Cy) (hCy' : 0 ≤ Cy')
    (hw0 : ∀ x, 0 ≤ w x) (hyb : ∀ x, |y x| ≤ Cy * w x)
    (hyb' : ∀ x, |y' x| ≤ Cy' * √(2 + |x|) * w x)
    (hnb : ∀ {X ξ : ℝ}, |ξ - X| ≤ 1 → |ξ - X| * √(1 + |X|) ≤ 1 → w ξ ≤ Cw * w X)
    {X s : ℝ} (hs1 : |s| ≤ 1) (hs2 : |s| * √(1 + |X|) ≤ 1) :
    |y (X + s) - (y X + y' X * s + X * y X * s ^ 2 / 2)| ≤
      Cw * (Cy + (|X| + 1) * Cy' * √(3 + |X|)) * w X * |s| ^ 3 := by
  have hM : ∀ t ∈ uIcc 0 s, |y (X + t) + (X + t) * y' (X + t)| ≤
      Cw * (Cy + (|X| + 1) * Cy' * √(3 + |X|)) * w X := by
    intro t ht
    have htabs : |t| ≤ |s| := by
      rcases le_total 0 s with h0 | h0
      · rw [uIcc_of_le h0] at ht
        rw [abs_of_nonneg ht.1, abs_of_nonneg h0]; exact ht.2
      · rw [uIcc_of_ge h0] at ht
        rw [abs_of_nonpos ht.2, abs_of_nonpos h0]; linarith [ht.1]
    have e1 : |X + t - X| = |t| := by simp
    have hw := hnb (X := X) (ξ := X + t) (by rw [e1]; linarith) (by
      rw [e1]
      exact (mul_le_mul_of_nonneg_right htabs (Real.sqrt_nonneg _)).trans hs2)
    have hξ : |X + t| ≤ |X| + 1 := by
      have := abs_add_le X t
      linarith
    have hsq : √(2 + |X + t|) ≤ √(3 + |X|) := Real.sqrt_le_sqrt (by linarith)
    have hw1 := hw0 (X + t)
    have hw2 := hw0 X
    have b1 : |y (X + t)| ≤ Cy * w (X + t) := hyb _
    have b2 : |(X + t) * y' (X + t)| ≤ (|X| + 1) * Cy' * √(3 + |X|) * w (X + t) := by
      rw [abs_mul]
      calc |X + t| * |y' (X + t)| ≤ (|X| + 1) * (Cy' * √(2 + |X + t|) * w (X + t)) :=
            mul_le_mul hξ (hyb' _) (abs_nonneg _) (by positivity)
        _ ≤ (|X| + 1) * (Cy' * √(3 + |X|) * w (X + t)) := by gcongr
        _ = _ := by ring
    calc |y (X + t) + (X + t) * y' (X + t)| ≤ |y (X + t)| + |(X + t) * y' (X + t)| := abs_add_le _ _
      _ ≤ (Cy + (|X| + 1) * Cy' * √(3 + |X|)) * w (X + t) := by nlinarith
      _ ≤ (Cy + (|X| + 1) * Cy' * √(3 + |X|)) * (Cw * w X) := by
          gcongr
      _ = _ := by ring
  exact a2_taylor_seg hy hM

/-- **Lattice-scale remainder**: `X = z/δ²`, shift `δ⁴ b`: `O(δ⁹ w(X))`. -/
lemma a2_rem_lat {y y' w : ℝ → ℝ} (hy : IsAirySol y y') {Cy Cy' Cw : ℝ} (hCy : 0 ≤ Cy) (hCy' : 0 ≤ Cy')
    (hCw : 0 ≤ Cw) (hw0 : ∀ x, 0 ≤ w x) (hyb : ∀ x, |y x| ≤ Cy * w x) (hyb' : ∀ x, |y' x| ≤ Cy' * √(2 + |x|) * w x)
    (hnb : ∀ {X ξ : ℝ}, |ξ - X| ≤ 1 → |ξ - X| * √(1 + |X|) ≤ 1 → w ξ ≤ Cw * w X)
    {z b Mz Bm δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hz : |z| ≤ Mz) (hb : |b| ≤ Bm)
    (hsm : δ * (Bm * √(1 + Mz)) ≤ 1) (hBm1 : δ * Bm ≤ 1) :
    |y (z / δ ^ 2 + δ ^ 4 * b) - (y (z / δ ^ 2) + y' (z / δ ^ 2) * (δ ^ 4 * b) +
        z / δ ^ 2 * y (z / δ ^ 2) * (δ ^ 4 * b) ^ 2 / 2)| ≤
      (Cw * (Cy + (Mz + 1) * √(3 + Mz) * Cy') * Bm ^ 3) * δ ^ 9 * w (z / δ ^ 2) := by
  have hBm0 : 0 ≤ Bm := (abs_nonneg _).trans hb
  have hMz0 : 0 ≤ Mz := (abs_nonneg _).trans hz
  have hδ2 : 0 < δ ^ 2 := by positivity
  have hX : |z / δ ^ 2| ≤ Mz / δ ^ 2 := by
    rw [abs_div, abs_of_pos hδ2]; exact div_le_div_of_nonneg_right hz hδ2.le
  have hs : |δ ^ 4 * b| ≤ δ ^ 4 * Bm := by
    rw [abs_mul, abs_of_pos (by positivity)]; exact mul_le_mul_of_nonneg_left hb (by positivity)
  have hs1 : |δ ^ 4 * b| ≤ 1 := by
    refine hs.trans ?_
    have : δ ^ 4 ≤ δ := by nlinarith [pow_pos hδ 2, pow_pos hδ 3, pow_pos hδ 4]
    nlinarith [mul_le_mul_of_nonneg_right this hBm0]
  have hs2 : |δ ^ 4 * b| * √(1 + |z / δ ^ 2|) ≤ 1 := by
    have h1 : √(1 + |z / δ ^ 2|) ≤ √(1 + Mz / δ ^ 2) := Real.sqrt_le_sqrt (by linarith)
    have h2 : δ * √(1 + Mz / δ ^ 2) = √(δ ^ 2 + Mz) := by
      have : (δ ^ 2 + Mz) = δ ^ 2 * (1 + Mz / δ ^ 2) := by field_simp
      rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq hδ.le]
    have h3 : √(δ ^ 2 + Mz) ≤ √(1 + Mz) := Real.sqrt_le_sqrt (by nlinarith)
    calc |δ ^ 4 * b| * √(1 + |z / δ ^ 2|) ≤ (δ ^ 4 * Bm) * √(1 + Mz / δ ^ 2) :=
          mul_le_mul hs h1 (Real.sqrt_nonneg _) (by positivity)
      _ = δ ^ 3 * Bm * (δ * √(1 + Mz / δ ^ 2)) := by ring
      _ ≤ δ ^ 3 * Bm * √(1 + Mz) := by rw [h2]; gcongr
      _ ≤ δ * (Bm * √(1 + Mz)) := by
          have : δ ^ 3 ≤ δ := by nlinarith [pow_pos hδ 2, pow_pos hδ 3]
          nlinarith [mul_nonneg hBm0 (Real.sqrt_nonneg (1 + Mz)), mul_le_mul_of_nonneg_right this
            (mul_nonneg hBm0 (Real.sqrt_nonneg (1 + Mz)))]
      _ ≤ 1 := hsm
  have hmain := a2_shift_rem hy hCy hCy' hw0 hyb hyb' hnb hs1 hs2
  refine hmain.trans ?_
  -- bound `(|X|+1) √(3+|X|) ≤ (Mz+1) √(3+Mz) / δ³`
  have hT : (|z / δ ^ 2| + 1) * √(3 + |z / δ ^ 2|) ≤ (Mz + 1) * √(3 + Mz) / δ ^ 3 := by
    have hq1 : |z / δ ^ 2| + 1 ≤ (Mz + 1) / δ ^ 2 := by
      have : (1 : ℝ) ≤ 1 / δ ^ 2 := by rw [le_div_iff₀ hδ2]; nlinarith [pow_le_one₀ hδ.le hδ1 (n := 2)]
      calc |z / δ ^ 2| + 1 ≤ Mz / δ ^ 2 + 1 / δ ^ 2 := add_le_add hX this
        _ = _ := by ring
    have hq2 : √(3 + |z / δ ^ 2|) ≤ √(3 + Mz) / δ := by
      have : 3 + |z / δ ^ 2| ≤ (3 + Mz) / δ ^ 2 := by
        have h1 : (3 : ℝ) ≤ 3 / δ ^ 2 := by
          rw [le_div_iff₀ hδ2]; nlinarith [pow_le_one₀ hδ.le hδ1 (n := 2)]
        calc 3 + |z / δ ^ 2| ≤ 3 / δ ^ 2 + Mz / δ ^ 2 := add_le_add h1 hX
          _ = _ := by ring
      calc √(3 + |z / δ ^ 2|) ≤ √((3 + Mz) / δ ^ 2) := Real.sqrt_le_sqrt this
        _ = √(3 + Mz) / δ := by rw [Real.sqrt_div (by linarith), Real.sqrt_sq hδ.le]
    calc (|z / δ ^ 2| + 1) * √(3 + |z / δ ^ 2|) ≤ ((Mz + 1) / δ ^ 2) * (√(3 + Mz) / δ) :=
          mul_le_mul hq1 hq2 (Real.sqrt_nonneg _) (by positivity)
      _ = _ := by field_simp
  have hw := hw0 (z / δ ^ 2)
  have hs3 : |δ ^ 4 * b| ^ 3 ≤ δ ^ 12 * Bm ^ 3 := by
    calc |δ ^ 4 * b| ^ 3 ≤ (δ ^ 4 * Bm) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hs 3
      _ = _ := by ring
  have hCyδ : Cy ≤ Cy / δ ^ 3 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [pow_le_one₀ hδ.le hδ1 (n := 3)]
  have hsum : Cy + (|z / δ ^ 2| + 1) * Cy' * √(3 + |z / δ ^ 2|) ≤
      (Cy + (Mz + 1) * √(3 + Mz) * Cy') / δ ^ 3 := by
    have : (|z / δ ^ 2| + 1) * Cy' * √(3 + |z / δ ^ 2|) =
        ((|z / δ ^ 2| + 1) * √(3 + |z / δ ^ 2|)) * Cy' := by ring
    rw [this]
    calc _ ≤ Cy / δ ^ 3 + ((Mz + 1) * √(3 + Mz) / δ ^ 3) * Cy' :=
          add_le_add hCyδ (mul_le_mul_of_nonneg_right hT hCy')
      _ = _ := by ring
  have hpos : 0 ≤ Cy + (|z / δ ^ 2| + 1) * Cy' * √(3 + |z / δ ^ 2|) := by positivity
  calc Cw * (Cy + (|z / δ ^ 2| + 1) * Cy' * √(3 + |z / δ ^ 2|)) * w (z / δ ^ 2) * |δ ^ 4 * b| ^ 3
      ≤ Cw * ((Cy + (Mz + 1) * √(3 + Mz) * Cy') / δ ^ 3) * w (z / δ ^ 2) * (δ ^ 12 * Bm ^ 3) := by
        have h1 : Cw * (Cy + (|z / δ ^ 2| + 1) * Cy' * √(3 + |z / δ ^ 2|)) ≤
            Cw * ((Cy + (Mz + 1) * √(3 + Mz) * Cy') / δ ^ 3) := mul_le_mul_of_nonneg_left hsum hCw
        have h2 := mul_le_mul_of_nonneg_right h1 hw
        exact mul_le_mul h2 hs3 (by positivity) (by positivity)
    _ = _ := by field_simp

/-- info: 'FormalResearch.Special.a2_shift_rem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.a2_shift_rem

end FormalResearch.Special
