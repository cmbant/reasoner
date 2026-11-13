module

public import FormalResearch.Racah.P2AnalyticBridge3j
public import FormalResearch.Racah.P2AnalyticCarrier6jShape

/-!
# The `6j` `t = 0` carrier is Wigner's small `d`-function (Weyl P2, `thm:6jeven`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `thm:6jeven` (`G_{f,0} = d^f_{nm}(arccos x)`,
including the transposition phase `(-1)^{m-n}` of chambers II/III); the carrier is in
`FormalResearch/Racah/P2AnalyticCarrier6j*.lean`.

## Dictionary (no extra sign, row `n`, column `m`)

For `f m n` with `f ± m`, `f ± n` natural (the four integrality facts of a physical point), all
four chambers, and `x ∈ [-1,1]`:

  `dZero6 f m n x = wignerSmallDx f n m x = d^f_{nm}(arccos x)`.

In the canonical sector `|n| ≤ m` this is `dZero6c m n d x = d^{m+d}_{nm}(arccos x)`: the extremal value
is `d^m_{nm} = (-1)^{m-n} d^m_{mn}`, and the sign `(-1)^{m-n}` of Wigner's `d^m_{mn}` is cancelled by the
transposition `d^f_{nm} = (-1)^{m-n} d^f_{mn}` (`wignerSmallD_swap`).  The chamber signs
`(-1)^{⌊m-n⌋}` of `dZero6` (chambers II and III) are exactly the transposition phases of
`wignerSmallD_swap`; chambers II and IV use `d^f_{-m,-n} = d^f_{nm}` (`wignerSmallD_neg`).  So the
paper's `d^f_{nm}` (first index `n`) is the right index order, and the carrier's chamber phases
`(-1)^{m-n}` are *not* an extra sign in the final identity: they convert the canonical-sector
formula for `(n,m)` (resp. `(-m,-n)`) into `d^f_{nm}`.

## Results

* `dZero6c_eq_wignerD`: canonical sector `dZero6c m n d x = d^{m+d}_{nm}(arccos x)`.
* `dZero6_eq_wignerD`: all chambers.
* `G6_zero_eq_dZero6`, `G6_zero_eq_wignerD`: `G6 f m n α β γ 0 = d^f_{nm}(arccos (cosA α β γ))`
  (`cosA` in `[-1,1]` assumed, e.g. `cosA_mem_Icc` for a triangle).
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner FormalResearch.Racah.SixJ

lemma wigR_eq_rootR (j n m : ℚ) : wigR j n m = rootR (m : ℝ) (n : ℝ) (j : ℝ) := rfl

/-- `d^j_{nm} = (-1)^k d^j_{mn}` when `m - n = k` is an integer. -/
lemma wignerSmallD_swap_int (j m n : ℚ) (k : ℤ) (hk : m - n = k) (θ : ℝ) :
    (-1 : ℝ) ^ k * wignerSmallD j m n θ = wignerSmallD j n m θ := by
  rw [wignerSmallD_swap j n m θ, show n - m = -(m - n) by ring, sgn_neg', hk, sgn_intCast]

lemma rootR_pos_canon {m n : ℚ} (p q : ℕ) (hp : m - n = p) (hq : m + n = q) {k : ℝ}
    (hk : (m : ℝ) < k) : 0 < rootR (m : ℝ) (n : ℝ) k := by
  have hp' : (m : ℝ) - n = p := by exact_mod_cast hp
  have hq' : (m : ℝ) + n = q := by exact_mod_cast hq
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hm0 : (0 : ℝ) ≤ m := by linarith
  have h1 : (m : ℝ) ^ 2 < k ^ 2 := by nlinarith
  have h2 : (n : ℝ) ^ 2 < k ^ 2 := by nlinarith
  unfold rootR
  exact Real.sqrt_pos.mpr (mul_pos (by linarith) (by linarith))

/-- The extremal value of the canonical sector: `dZero6c m n 0 x = d^m_{nm}(arccos x)`. -/
theorem dZero6c_start_eq_wignerD (m n : ℚ) (p q : ℕ) (hp : m - n = p) (hq : m + n = q)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    dZero6c m n 0 x = wignerSmallDx (m + ((0 : ℕ) : ℚ)) n m x := by
  obtain ⟨h1, h2, h3⟩ := floor_labels m n p q hp hq
  unfold dZero6c wignerSmallDx
  rw [ptilde6_zero, h1, h2, h3, wignerSmallD_chamber_C (μ := p) (ν := q) (k := 0)
    (by rw [hp]) (by rw [hq]) (by push_cast; ring), wignerJacobiForm_zero_arccos _ _ hx,
    Nat.cast_choose ℝ (Nat.le_add_left q p), Nat.add_sub_cancel, mul_comm (q.factorial : ℝ)]
  ring

/-- **Canonical sector**: `dZero6c m n d x = d^{m+d}_{nm}(arccos x)` for `m ∓ n` natural. -/
theorem dZero6c_eq_wignerD (m n : ℚ) (p q : ℕ) (hp : m - n = p) (hq : m + n = q)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) (d : ℕ) :
    dZero6c m n d x = wignerSmallDx (m + (d : ℚ)) n m x := by
  have hp' : (m : ℝ) - n = p := by exact_mod_cast hp
  have hq' : (m : ℝ) + n = q := by exact_mod_cast hq
  have hm0 : (0 : ℝ) ≤ m := by
    have : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    have : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    linarith
  have hst := dZero6c_start_eq_wignerD m n p q hp hq hx
  have e : (1 : ℝ) - 2 * ((1 - x) / 2) = x := by ring
  -- the second start
  have h1 : dZero6c m n 1 x = wignerSmallDx (m + ((1 : ℕ) : ℚ)) n m x := by
    by_cases hm : m = 0
    · have hp0 : p = 0 := by
        have : (p : ℝ) + q = 0 := by rw [← hp', ← hq']; subst hm; simp
        have : (p : ℝ) = 0 := by linarith [(Nat.cast_nonneg q : (0 : ℝ) ≤ q), (Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
        exact_mod_cast this
      have hn : n = 0 := by
        subst hm; rw [hp0] at hp; simpa using hp
      subst hm hn
      unfold dZero6c wignerSmallDx
      rw [ptilde6_one_of_eq]
      simp only [sub_zero, add_zero, Nat.floor_zero, pow_zero, Real.sqrt_one,
        one_mul, Nat.cast_one, zero_add]
      rw [wignerSmallD_one_zero_zero, Real.cos_arccos hx.1 hx.2]
      ring
    · have hmr : (m : ℝ) ≠ 0 := by exact_mod_cast hm
      have hR : 0 < rootR (m : ℝ) (n : ℝ) ((m : ℝ) + 1) := rootR_pos_canon p q hp hq (by linarith)
      have hW := wignerSmallDx_rank_rec m n m hx
      have hR0 : wigR m n m = 0 := by unfold wigR; simp
      rw [hR0, zero_mul, mul_zero, zero_add, wigR_eq_rootR] at hW
      have hc : ((m + 1 : ℚ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
      rw [hc] at hW
      have hq0 := ptilde6_one_of_ne m n hm ((1 - x) / 2) 0 0 0
      have e1 : m + ((1 : ℕ) : ℚ) = m + 1 := by push_cast; ring
      rw [e1]
      have ha0 : dZero6c m n 0 x = wignerSmallDx m n m x := by simpa using hst
      refine mul_left_cancel₀ (mul_ne_zero hmr hR.ne') ?_
      have hs : (m : ℝ) * rootR (m : ℝ) (n : ℝ) ((m : ℝ) + 1) * dZero6c m n 1 x =
          (2 * (m : ℝ) + 1) * ((m : ℝ) * (m + 1) * x - m * n) * dZero6c m n 0 x := by
        unfold dZero6c
        rw [hq0, ptilde6_zero]
        simp only [mul_zero, sub_zero]
        rw [e]
        field_simp
      rw [hs, ha0]
      linear_combination hW
  have hgen : ∀ d : ℕ, dZero6c m n d x = wignerSmallDx (m + (d : ℚ)) n m x := by
    refine rec_seq_ext (fun d => dZero6c m n d x) (fun d => wignerSmallDx (m + (d : ℚ)) n m x)
      (fun d => ((m : ℝ) + d + 1) * rootR (m : ℝ) (n : ℝ) ((m : ℝ) + d + 1 + 1))
      (fun d => (2 * ((m : ℝ) + d + 1) + 1) *
        (((m : ℝ) + d + 1) * (((m : ℝ) + d + 1) + 1) * x - m * n))
      (fun d => (((m : ℝ) + d + 1) + 1) * rootR (m : ℝ) (n : ℝ) ((m : ℝ) + d + 1))
      (by simpa using hst) (by simpa using h1) ?_ ?_ ?_
    · intro d
      have hF : (0 : ℝ) < (m : ℝ) + d + 1 := by positivity
      have hR := rootR_pos_canon p q hp hq (k := (m : ℝ) + d + 1 + 1)
        (by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith)
      exact mul_ne_zero hF.ne' hR.ne'
    · intro d
      have hF : (0 : ℝ) < (m : ℝ) + d + 1 := by positivity
      have hR := rootR_pos_canon p q hp hq (k := (m : ℝ) + d + 1 + 1)
        (by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith)
      have h := ptilde6_succ_succ m n ((1 - x) / 2) 0 0 0 d
      simp only [mul_zero, sub_zero, mul_one] at h
      rw [e] at h
      have hne : ((m : ℝ) + d + 1) * rootR (m : ℝ) (n : ℝ) ((m : ℝ) + d + 1 + 1) ≠ 0 :=
        mul_ne_zero hF.ne' hR.ne'
      have hP : ((m : ℝ) + d + 1) * rootR (m : ℝ) (n : ℝ) ((m : ℝ) + d + 1 + 1) *
          ptilde6 m n ((1 - x) / 2) 0 0 0 (d + 2) =
          (2 * ((m : ℝ) + d + 1) + 1) *
            (((m : ℝ) + d + 1) * (((m : ℝ) + d + 1) + 1) * x - m * n) *
              ptilde6 m n ((1 - x) / 2) 0 0 0 (d + 1) -
          (((m : ℝ) + d + 1) + 1) * rootR (m : ℝ) (n : ℝ) ((m : ℝ) + d + 1) *
            ptilde6 m n ((1 - x) / 2) 0 0 0 d := by
        rw [h]; field_simp
      show _ * (Real.sqrt _ * ptilde6 m n ((1 - x) / 2) 0 0 0 (d + 2)) =
        _ * (Real.sqrt _ * ptilde6 m n ((1 - x) / 2) 0 0 0 (d + 1)) -
          _ * (Real.sqrt _ * ptilde6 m n ((1 - x) / 2) 0 0 0 d)
      linear_combination
        (Real.sqrt (((1 - x) / 2) ^ ⌊m - n⌋₊ * ((1 + x) / 2) ^ ⌊m + n⌋₊)) * hP
    · intro d
      have hW := wignerSmallDx_rank_rec (m + ((d + 1 : ℕ) : ℚ)) n m hx
      rw [show m + ((d + 1 : ℕ) : ℚ) - 1 = m + (d : ℚ) by push_cast; ring] at hW
      have e2 : wignerSmallDx (m + ((d + 1 : ℕ) : ℚ) + 1) n m x =
          wignerSmallDx (m + ((d + 2 : ℕ) : ℚ)) n m x := by
        rw [show m + ((d + 1 : ℕ) : ℚ) + 1 = m + ((d + 2 : ℕ) : ℚ) by push_cast; ring]
      rw [e2] at hW
      simp only [wigR_eq_rootR] at hW
      have c0 : ((m + ((d + 1 : ℕ) : ℚ) : ℚ) : ℝ) = (m : ℝ) + d + 1 := by push_cast; ring
      have c1 : ((m + ((d + 1 : ℕ) : ℚ) + 1 : ℚ) : ℝ) = (m : ℝ) + d + 1 + 1 := by
        push_cast; ring
      rw [c1, c0] at hW
      show _ * wignerSmallDx (m + ((d + 2 : ℕ) : ℚ)) n m x =
        _ * wignerSmallDx (m + ((d + 1 : ℕ) : ℚ)) n m x - _ * wignerSmallDx (m + (d : ℚ)) n m x
      linear_combination -hW
  exact hgen d

/-- **`thm:6jeven` at `t = 0`, all chambers**: for `f ± m`, `f ± n` natural and `x ∈ [-1,1]`,
`dZero6 f m n x = d^f_{nm}(arccos x)` (index order `n, m`; no extra phase). -/
theorem dZero6_eq_wignerD (f m n : ℚ) (n1 : IsNat (f + m)) (n2 : IsNat (f - m))
    (n3 : IsNat (f + n)) (n4 : IsNat (f - n)) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    dZero6 f m n x = wignerSmallDx f n m x := by
  -- the integer `⌊m - n⌋`
  obtain ⟨a, ha⟩ := n4
  obtain ⟨b, hb⟩ := n2
  have hk : m - n = (((a : ℤ) - (b : ℤ) : ℤ) : ℚ) := by push_cast; linarith
  have hfl : ⌊m - n⌋ = (a : ℤ) - (b : ℤ) := by rw [hk]; exact Int.floor_intCast _
  have n4 : IsNat (f - n) := ⟨a, ha⟩
  have n2 : IsNat (f - m) := ⟨b, hb⟩
  unfold dZero6
  by_cases c1 : |n| ≤ m
  · simp only [c1, ↓reduceIte]
    obtain ⟨⟨p, q, hp, hq⟩, hf⟩ := canon_labels c1 n2 n3 n4
    rw [dZero6c_eq_wignerD m n p q hp hq hx, ← hf]
  by_cases c2 : |n| ≤ -m
  · simp only [c1, c2, ↓reduceIte, hfl]
    obtain ⟨⟨p, q, hp, hq⟩, hf⟩ := canon_labels (f := f) (m := -m) (n := -n) (by simpa using c2)
      (by simpa using n1) (by simpa [sub_eq_add_neg] using n4) (by simpa using n3)
    rw [sub_neg_eq_add] at hf
    rw [dZero6c_eq_wignerD (-m) (-n) p q hp hq hx, ← hf]
    unfold wignerSmallDx
    rw [wignerSmallD_neg f m n]
    exact wignerSmallD_swap_int f m n _ hk _
  by_cases c3 : |m| ≤ n
  · simp only [c1, c2, c3, ↓reduceIte, hfl]
    obtain ⟨⟨p, q, hp, hq⟩, hf⟩ := canon_labels (f := f) (m := n) (n := m) c3 n4 n1 n2
    rw [dZero6c_eq_wignerD n m p q hp hq hx, ← hf]
    unfold wignerSmallDx
    exact wignerSmallD_swap_int f m n _ hk _
  have c4 : |m| ≤ -n := by
    rcases le_total 0 n with hn | hn
    · rw [abs_of_nonneg hn] at c1 c2
      exfalso; apply c3; rw [abs_le]; constructor <;> push Not at c1 c2 <;> linarith
    · rw [abs_of_nonpos hn] at c1 c2
      rw [abs_le]; push Not at c1 c2; constructor <;> linarith
  simp only [c1, c2, c3, ↓reduceIte]
  obtain ⟨⟨p, q, hp, hq⟩, hf⟩ := canon_labels (f := f) (m := -n) (n := -m) (by simpa using c4)
    (by simpa using n3) (by simpa [sub_eq_add_neg] using n2) (by simpa using n1)
  rw [sub_neg_eq_add] at hf
  rw [dZero6c_eq_wignerD (-n) (-m) p q hp hq hx, ← hf]
  unfold wignerSmallDx
  exact wignerSmallD_neg f n m _

lemma cosA_comm' (A B C : ℝ) : cosA B A C = cosA A B C := by
  unfold cosA; ring

/-- `t = 0` of the closed-form germ in every chamber: `G6 f m n α β γ 0 = dZero6 f m n (cosA α β γ)`. -/
theorem G6_zero_eq_dZero6 (f m n : ℚ) (n1 : IsNat (f + m)) (n2 : IsNat (f - m))
    (n3 : IsNat (f + n)) (n4 : IsNat (f - n)) (α β γ : ℝ) (hα : α ≠ 0) (hβ : β ≠ 0) :
    G6 f m n α β γ 0 = dZero6 f m n (cosA α β γ) := by
  unfold G6 dZero6
  by_cases c1 : |n| ≤ m
  · simp only [c1, ↓reduceIte]
    obtain ⟨⟨p, q, hp, hq⟩, -⟩ := canon_labels c1 n2 n3 n4
    exact G6c_zero m n p q hp hq _ α β γ hα hβ
  by_cases c2 : |n| ≤ -m
  · simp only [c1, c2, ↓reduceIte]
    obtain ⟨⟨p, q, hp, hq⟩, -⟩ := canon_labels (f := f) (m := -m) (n := -n) (by simpa using c2)
      (by simpa using n1) (by simpa [sub_eq_add_neg] using n4) (by simpa using n3)
    rw [G6c_zero (-m) (-n) p q hp hq _ α β γ hα hβ]
  by_cases c3 : |m| ≤ n
  · simp only [c1, c2, c3, ↓reduceIte]
    obtain ⟨⟨p, q, hp, hq⟩, -⟩ := canon_labels (f := f) (m := n) (n := m) c3 n4 n1 n2
    rw [G6c_zero n m p q hp hq _ β α γ hβ hα, cosA_comm']
  have c4 : |m| ≤ -n := by
    rcases le_total 0 n with hn | hn
    · rw [abs_of_nonneg hn] at c1 c2
      exfalso; apply c3; rw [abs_le]; constructor <;> push Not at c1 c2 <;> linarith
    · rw [abs_of_nonpos hn] at c1 c2
      rw [abs_le]; push Not at c1 c2; constructor <;> linarith
  simp only [c1, c2, c3, ↓reduceIte]
  obtain ⟨⟨p, q, hp, hq⟩, -⟩ := canon_labels (f := f) (m := -n) (n := -m) (by simpa using c4)
    (by simpa using n3) (by simpa [sub_eq_add_neg] using n2) (by simpa using n1)
  rw [G6c_zero (-n) (-m) p q hp hq _ β α γ hβ hα, cosA_comm']

/-- **`thm:6jeven`, germ form**: `G_{f,0} = d^f_{nm}(arccos x)`, `x = cosA α β γ`
(`f ± m`, `f ± n` natural, `x ∈ [-1,1]`). -/
theorem G6_zero_eq_wignerD (f m n : ℚ) (n1 : IsNat (f + m)) (n2 : IsNat (f - m))
    (n3 : IsNat (f + n)) (n4 : IsNat (f - n)) (α β γ : ℝ) (hα : α ≠ 0) (hβ : β ≠ 0)
    (hx : cosA α β γ ∈ Set.Icc (-1 : ℝ) 1) :
    G6 f m n α β γ 0 = wignerSmallDx f n m (cosA α β γ) := by
  rw [G6_zero_eq_dZero6 f m n n1 n2 n3 n4 α β γ hα hβ, dZero6_eq_wignerD f m n n1 n2 n3 n4 hx]

/-- The cosine of a triangle lies in `[-1,1]`. -/
theorem cosA_mem_Icc (A B C : ℝ) (hA : 0 < A) (hB : 0 < B) (h1 : |A - B| ≤ C) (h2 : C ≤ A + B) :
    cosA A B C ∈ Set.Icc (-1 : ℝ) 1 := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) h1
  have h1' := abs_le.mp h1
  have hAB : 0 < 2 * A * B := by positivity
  unfold cosA
  constructor
  · rw [le_div_iff₀ hAB]; nlinarith
  · rw [div_le_iff₀ hAB]; nlinarith

/-- info: 'FormalResearch.Racah.dZero6c_eq_wignerD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dZero6c_eq_wignerD

/-- info: 'FormalResearch.Racah.dZero6_eq_wignerD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dZero6_eq_wignerD

/-- info: 'FormalResearch.Racah.G6_zero_eq_wignerD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms G6_zero_eq_wignerD

/-- info: 'FormalResearch.Racah.cosA_mem_Icc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cosA_mem_Icc

end FormalResearch.Racah
