module

public import FormalResearch.Special.AiryZeroSpacing
public import FormalResearch.Special.AiryZeroGap
public import FormalResearch.Special.AiryNodes
public import FormalResearch.Special.AiryEnvelopeNeg
public import FormalResearch.Special.AiryAsymReal

/-!
# Bulk window, part 2: zeros of `Ai`, their count, and the sign of `Ai` in terms of the count

With `airyZeroCount x` = the number of zeros of `Ai` in `(x, 0]` (`AiryZeroOrder`):

* **`bwn_sign`**: for `x ≤ 0` with `Ai x ≠ 0`, `(-1)^{airyZeroCount x} Ai(x) > 0` (from the Prüfer angle).
* `bwn_count_anti`, `bwn_count_step`, `bwn_count_zero`: the count is antitone; it drops by at most one across `[x, x']` when
  `(x' - x) √Y < π`, `-Y ≤ x` (zero spacing `airy_zero_gap`); it vanishes on `[-1, 0]`.
* `bwn_phase`: `|(2/3) ρ_n³ - (n - 1/4)π| ≤ 1/20` for **all** `n ≥ 1` (`ρ_n = √|a_n|`; `n ≥ 2` is `airyZero_phase_weak`, `n = 1` from the
  bounds `-2.35 < a_1 < -2.33`).
* **`bwn_count_floor`**: for `v > 0` with `|cos((2/3) v^{3/2} - π/4)| > 1/10`, the number of zeros of `Ai` in `(-v, 0]` is
  `⌊(2/3) v^{3/2}/π + 1/4⌋`.

**Claim class: proved.**  **Not formalised:** the sharp phase of the zeros (`1/20` is not optimal) and the resonant window
`|cos| ≤ 1/10` (there the count is `⌊·⌋` or `⌊·⌋ - 1`; not needed).
-/

@[expose] public section

open Set
open scoped Real

namespace FormalResearch.Special


/-- Sign of `Ai` at a nonzero point `x ≤ 0`: `(-1)^{#zeros in (x,0]} Ai x > 0`. -/
theorem bwn_sign {x : ℝ} (hx : x ≤ 0) (hne : airyAi x ≠ 0) :
    0 < (-1 : ℝ) ^ (airyZeroCount x) * airyAi x := by
  obtain ⟨θ, hθ, hlo, hhi, -⟩ := airy_exists_prufer
  have hpi := Real.pi_pos
  have hc := airy_zeros_ncard hθ (by linarith) hhi hx
  have hcnt : (airyZeroCount x : ℤ) = -⌊θ x / π⌋ := hc
  obtain ⟨r, hr, hy, -⟩ := hθ.exists_r
  set k := ⌊θ x / π⌋ with hk
  have hs : (-1 : ℝ) ^ k * Real.sin (θ x) = Real.sin (θ x - k * π) := (Real.sin_sub_int_mul_pi _ _).symm
  have hnn : 0 ≤ Real.sin (θ x - k * π) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · have := Int.floor_le (θ x / π)
      rw [le_div_iff₀ hpi] at this; linarith
    · have := Int.lt_floor_add_one (θ x / π)
      rw [div_lt_iff₀ hpi] at this; linarith
  have hpow : (-1 : ℝ) ^ (airyZeroCount x) = (-1 : ℝ) ^ k := by
    have : (-1 : ℝ) ^ (airyZeroCount x) = (-1 : ℝ) ^ ((airyZeroCount x : ℤ)) := (zpow_natCast _ _).symm
    rw [this, hcnt, zpow_neg]
    have h2 : ((-1 : ℝ) ^ k) * ((-1 : ℝ) ^ k) = 1 := by rw [← zpow_add₀ (by norm_num)]; 
                                                         rw [← two_mul, zpow_mul]; norm_num
    exact inv_eq_of_mul_eq_one_right h2
  rw [hpow, hy x]
  have hne' : Real.sin (θ x) ≠ 0 := by
    intro h; apply hne; rw [hy x, h, mul_zero]
  have : 0 < Real.sin (θ x - k * π) := by
    refine lt_of_le_of_ne hnn (fun h0 => hne' ?_)
    rw [← hs] at h0
    rcases mul_eq_zero.1 h0.symm with h | h
    · exact absurd h (zpow_ne_zero _ (by norm_num))
    · exact h
  calc (0:ℝ) < r x * Real.sin (θ x - k * π) := mul_pos (hr x) this
    _ = (-1 : ℝ) ^ k * (r x * Real.sin (θ x)) := by rw [← hs]; ring


lemma bwn_count_anti {x y : ℝ} (h : x ≤ y) : airyZeroCount y ≤ airyZeroCount x := by
  unfold airyZeroCount
  refine Set.ncard_le_ncard ?_ (airyZeroSet_finite x)
  intro t ht
  exact ⟨⟨h.trans_lt ht.1.1, ht.1.2⟩, ht.2⟩

lemma bwn_count_step {x x' Y : ℝ} (hY : 0 < Y) (hx : -Y ≤ x) (_hxx : x ≤ x') (hx' : x' ≤ 0)
    (hs : (x' - x) * √Y < π) :
    airyZeroCount x ≤ airyZeroCount x' + 1 := by
  have hsY : 0 < √Y := Real.sqrt_pos.2 hY
  set A : Set ℝ := {t | t ∈ Ioc x x' ∧ airyAi t = 0} with hA
  have hsub : airyZeroSet x ⊆ airyZeroSet x' ∪ A := by
    intro t ht
    by_cases h : x' < t
    · left; exact ⟨⟨h, ht.1.2⟩, ht.2⟩
    · right; exact ⟨⟨ht.1.1, not_lt.1 h⟩, ht.2⟩
  have hAfin : A.Finite := (airyZeroSet_finite x).subset (fun t ht => ⟨⟨ht.1.1, ht.1.2.trans hx'⟩, ht.2⟩)
  have hA1 : A.ncard ≤ 1 := by
    have key : ∀ t t' : ℝ, t ∈ A → t' ∈ A → t < t' → False := by
      intro t t' ht ht' hlt
      have := airy_zero_gap hY (by linarith [ht.1.1]) hlt (ht'.1.2.trans hx') ht.2 ht'.2
      rw [div_le_iff₀ hsY] at this
      nlinarith [ht.1.1, ht'.1.2]
    rw [Set.ncard_le_one_iff hAfin]
    intro t t' ht ht'
    rcases lt_trichotomy t t' with h | h | h
    · exact (key t t' ht ht' h).elim
    · exact h
    · exact (key t' t ht' ht h).elim
  calc airyZeroCount x ≤ (airyZeroSet x' ∪ A).ncard :=
        Set.ncard_le_ncard hsub ((airyZeroSet_finite x').union hAfin)
    _ ≤ (airyZeroSet x').ncard + A.ncard := Set.ncard_union_le _ _
    _ ≤ airyZeroCount x' + 1 := by unfold airyZeroCount; omega

lemma bwn_count_zero {x : ℝ} (hx : -1 ≤ x) : airyZeroCount x = 0 := by
  unfold airyZeroCount
  rw [Set.ncard_eq_zero (airyZeroSet_finite x)]
  ext t
  simp only [airyZeroSet, Set.mem_ofPred_eq, mem_Ioc, mem_empty_iff_false, iff_false, not_and]
  intro ⟨h1, h2⟩ h3
  have := airyAi_pos_of_neg_one_le (x := t) (by linarith)
  linarith

lemma bwn_phase_one : |2 / 3 * airyZeroRoot 1 ^ 3 - (((1 : ℕ) : ℝ) - 1 / 4) * π| ≤ 1 / 20 := by
  obtain ⟨h1, h2⟩ := airyZero_one
  have hr : (1.5264 : ℝ) < airyZeroRoot 1 ∧ airyZeroRoot 1 < 1.533 := by
    constructor
    · rw [airyZeroRoot, Real.lt_sqrt (by norm_num)]; norm_num; linarith
    · rw [airyZeroRoot, Real.sqrt_lt' (by norm_num)]; norm_num; linarith
  obtain ⟨hr1, hr2⟩ := hr
  have c1 : (1.5264 : ℝ) ^ 3 < airyZeroRoot 1 ^ 3 := pow_lt_pow_left₀ hr1 (by norm_num) (by norm_num)
  have c2 : airyZeroRoot 1 ^ 3 < (1.533 : ℝ) ^ 3 := pow_lt_pow_left₀ hr2 (airyZeroRoot_pos 1).le (by norm_num)
  have hp1 : (3.14 : ℝ) < π := Real.pi_gt_d2
  have hp2 : π < (3.15 : ℝ) := Real.pi_lt_d2
  norm_num at c1 c2 ⊢
  rw [abs_le]; constructor <;> nlinarith

lemma bwn_phase (n : ℕ) (hn : 1 ≤ n) : |2 / 3 * airyZeroRoot n ^ 3 - ((n : ℝ) - 1 / 4) * π| ≤ 1 / 20 := by
  rcases Nat.eq_or_lt_of_le hn with h | h
  · subst h; exact bwn_phase_one
  · exact airyZero_phase_weak (by omega)


/-- **The number of zeros of `Ai` in `(-v, 0]`** is `⌊ξ/π + 1/4⌋`, `ξ = (2/3) v^{3/2}`, at every non-resonant `v`
(`|cos(ξ - π/4)| > 1/10`). -/
theorem bwn_count_floor {v : ℝ} (hv : 0 < v)
    (hcos : 1 / 10 < |Real.cos (2 / 3 * v ^ (3 / 2 : ℝ) - π / 4)|) :
    (airyZeroCount (-v) : ℤ) = ⌊2 / 3 * v ^ (3 / 2 : ℝ) / π + 1 / 4⌋ := by
  set ξ : ℝ := 2 / 3 * v ^ (3 / 2 : ℝ) with hξ
  have hξ' : ξ = 2 / 3 * (√v) ^ 3 := by rw [hξ, sqrt_cube_eq_rpow hv]
  have hpi := Real.pi_pos
  have hp1 : (3.14 : ℝ) < π := Real.pi_gt_d2
  set n0 := airyZeroCount (-v) with hn0
  set w : ℝ := ξ / π + 1 / 4 with hw
  have hξpos : 0 < ξ := by rw [hξ]; positivity
  -- lower bound
  have hlow : (n0 : ℝ) - 1 / 62 < w := by
    rcases Nat.eq_zero_or_pos n0 with h0 | hpos
    · rw [h0]; have : 0 < ξ / π := by positivity
      simp only [Nat.cast_zero]; rw [hw]; linarith
    · -- a_{n0} > -v
      have hgt : -v < airyZero n0 := by
        by_contra hle
        push Not at hle
        have h1 := bwn_count_anti hle
        rw [airyZeroCount_airyZero] at h1
        omega
      have hr : airyZeroRoot n0 < √v := by
        rw [airyZeroRoot]; exact Real.sqrt_lt_sqrt (neg_nonneg.mpr (airyZero_nonpos _)) (by linarith)
      have hc : airyZeroRoot n0 ^ 3 < (√v) ^ 3 := pow_lt_pow_left₀ hr (airyZeroRoot_pos _).le (by norm_num)
      have hph := abs_le.1 (bwn_phase n0 hpos)
      rw [hw]
      have : ((n0 : ℝ) - 1 / 4) * π - 1 / 20 < ξ := by rw [hξ']; linarith [hph.1]
      rw [show ξ / π + 1 / 4 = (ξ + π / 4) / π by field_simp]
      rw [lt_div_iff₀ hpi]
      nlinarith
  have hup : w ≤ (n0 : ℝ) + 1 + 1 / 62 := by
    have hlt : airyZero (n0 + 1) ≤ -v := by
      by_contra hle
      push Not at hle
      have h1 := airyZeroCount_lt (airyAi_airyZero (n0 + 1)) (airyZero_nonpos _) hle
      rw [airyZeroCount_airyZero] at h1
      simp only [Nat.add_sub_cancel] at h1
      rw [← hn0] at h1; exact lt_irrefl _ h1
    have hr : √v ≤ airyZeroRoot (n0 + 1) := by
      rw [airyZeroRoot]; exact Real.sqrt_le_sqrt (by linarith)
    have hc : (√v) ^ 3 ≤ airyZeroRoot (n0 + 1) ^ 3 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hr 3
    have hph := abs_le.1 (bwn_phase (n0 + 1) (by omega))
    push_cast at hph
    have : ξ ≤ ((n0 : ℝ) + 1 - 1 / 4) * π + 1 / 20 := by rw [hξ']; linarith [hph.2]
    rw [hw, show ξ / π + 1 / 4 = (ξ + π / 4) / π by field_simp, div_le_iff₀ hpi]
    nlinarith
  -- the sine
  have hsin : |Real.sin (π * w)| = |Real.cos (ξ - π / 4)| := by
    have : ξ - π / 4 = π * w - π / 2 := by rw [hw]; field_simp; ring
    rw [this, Real.cos_sub_pi_div_two]
  have hsinm : ∀ m : ℤ, |Real.sin (π * w)| ≤ π * |w - m| := by
    intro m
    have h1 : Real.sin (π * w - m * π) = (-1) ^ m * Real.sin (π * w) := Real.sin_sub_int_mul_pi _ _
    have h2 : |Real.sin (π * w - m * π)| = |Real.sin (π * w)| := by
      rw [h1, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
    rw [← h2]
    refine Real.abs_sin_le_abs.trans ?_
    rw [show π * w - m * π = π * (w - m) by ring, abs_mul, abs_of_pos hpi]
  have hfl : ⌊w⌋ = (n0 : ℤ) := by
    rw [Int.floor_eq_iff]
    push_cast
    constructor
    · by_contra hlt
      push Not at hlt
      have := hsinm n0
      have e : |w - (n0 : ℤ)| ≤ 1 / 62 := by
        rw [abs_le]; push_cast; constructor <;> linarith
      have : |Real.sin (π * w)| ≤ π * (1 / 62) := (hsinm n0).trans (mul_le_mul_of_nonneg_left e hpi.le)
      have hp2 : π < (3.15 : ℝ) := Real.pi_lt_d2
      linarith
    · by_contra hge
      push Not at hge
      have e : |w - ((n0 + 1 : ℕ) : ℤ)| ≤ 1 / 62 := by
        rw [abs_le]; push_cast; constructor <;> linarith
      have : |Real.sin (π * w)| ≤ π * (1 / 62) :=
        (hsinm ((n0 + 1 : ℕ) : ℤ)).trans (mul_le_mul_of_nonneg_left e hpi.le)
      have hp2 : π < (3.15 : ℝ) := Real.pi_lt_d2
      linarith
  rw [hfl]


/-- info: 'FormalResearch.Special.bwn_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.bwn_sign

/-- info: 'FormalResearch.Special.bwn_count_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.bwn_count_floor

end FormalResearch.Special
