module

public import Mathlib
public import FormalResearch.SignUncertainty.CtBoasAssembly
public import FormalResearch.SignUncertainty.CtBoasBlocks

/-!
# `ct:boas` Step 3: the tent partition of unity on the logarithmic band variable

`constant_terms_lower.tex`, proof of `ct:boas`, Step 3 ("Adaptive partition on `[L_min, L_far+1]`").  The paper asks for
`O(log c)` overlapping intervals `I_j = [L_j - δ_j, L_j + δ_j]`, `δ_j ≍ min(L_j, 1)`, and a Lipschitz partition of unity
`χ_j ≥ 0` (`Σ_j χ_j = 1` on `[L_min, L_far + 1]`, `Σ_j χ_j ≤ 1` on `ℝ`, `|χ_j'| ≤ C/δ_j`, bounded overlap).  Step 5 only
uses the Lipschitz bound, so piecewise linear hats suffice.

* `tent x j = ramp x j - ramp x (j+1)`, `ramp x k = clamp((L - x_k)/(x_{k+1} - x_k))`, for a strictly increasing node
  sequence `x`: `Σ_{j<J} tent x j = ramp x 0 - ramp x J` telescopes, which gives `0 ≤ χ_j`, `Σχ_j ≤ 1`, `Σχ_j = 1` on
  `[x_1, x_J]` without case analysis (`tentPartition`, an instance of `BoasPartition`).
* The node grid `tentNode a`: `x_{k+1} = x_k + min(x_k, 1)/36` (geometric of ratio `37/36` below `1`, uniform of step `1/36`
  above); the block `j` has centre `L_j = x_{j+1}`, `δ_j = min(L_j,1)/36`, `supp χ_j ⊂ [L_j - δ_j, L_j + δ_j]`
  (`tentNode_block_support`), the Lipschitz constant `3/δ_j` (`tent_lipschitz_tentNode`), the block count
  `J ≤ 37 log(1/a) + 36 b + 3` for `x_J ≥ b` (`exists_tentNode_ge`, `tentGrid_boasPartition`), the bounded overlap `≤ 7` of the
  enlarged blocks `I_j^{**} = [L_j - 3δ_j, L_j + 3δ_j]` (`tentQ_overlap`) and the Harnack ratio of `τ₀` on `I_j^{**}`
  (`tentBlock_tau0_ratio`).

**Proved**, unconditional.
-/

@[expose] public section

open Set MeasureTheory Finset
open FormalResearch.CohnElkies

namespace FormalResearch.SignUncertainty

/-- The ramp `clamp((L - x_k)/(x_{k+1} - x_k))`: `0` for `L ≤ x_k`, `1` for `L ≥ x_{k+1}`, linear in between. -/
noncomputable def tentRamp (x : ℕ → ℝ) (k : ℕ) (L : ℝ) : ℝ :=
  max 0 (min 1 ((L - x k) / (x (k + 1) - x k)))

/-- The hat function with feet `x_j`, `x_{j+2}` and peak `x_{j+1}`: `ramp_j - ramp_{j+1}`. -/
noncomputable def tent (x : ℕ → ℝ) (j : ℕ) (L : ℝ) : ℝ := tentRamp x j L - tentRamp x (j + 1) L

section generic

variable {x : ℕ → ℝ}

lemma tentRamp_nonneg (x : ℕ → ℝ) (k : ℕ) (L : ℝ) : 0 ≤ tentRamp x k L := le_max_left _ _

lemma tentRamp_le_one (x : ℕ → ℝ) (k : ℕ) (L : ℝ) : tentRamp x k L ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

lemma tentRamp_of_le (hx : StrictMono x) {k : ℕ} {L : ℝ} (h : L ≤ x k) : tentRamp x k L = 0 := by
  have hp : 0 < x (k + 1) - x k := sub_pos.2 (hx (Nat.lt_succ_self k))
  have : (L - x k) / (x (k + 1) - x k) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hp.le
  unfold tentRamp
  exact max_eq_left ((min_le_right _ _).trans this)

lemma tentRamp_of_ge (hx : StrictMono x) {k : ℕ} {L : ℝ} (h : x (k + 1) ≤ L) : tentRamp x k L = 1 := by
  have hp : 0 < x (k + 1) - x k := sub_pos.2 (hx (Nat.lt_succ_self k))
  have : 1 ≤ (L - x k) / (x (k + 1) - x k) := by rw [le_div_iff₀ hp]; linarith
  unfold tentRamp
  rw [min_eq_left this]; exact max_eq_right zero_le_one

lemma tentRamp_anti (hx : StrictMono x) (k : ℕ) (L : ℝ) : tentRamp x (k + 1) L ≤ tentRamp x k L := by
  rcases le_total L (x (k + 1)) with h | h
  · rw [tentRamp_of_le hx h]; exact tentRamp_nonneg x k L
  · rw [tentRamp_of_ge hx h]; exact tentRamp_le_one x (k + 1) L

lemma tent_nonneg (hx : StrictMono x) (j : ℕ) (L : ℝ) : 0 ≤ tent x j L :=
  sub_nonneg.2 (tentRamp_anti hx j L)

lemma tent_le_one (x : ℕ → ℝ) (j : ℕ) (L : ℝ) : tent x j L ≤ 1 := by
  unfold tent; linarith [tentRamp_le_one x j L, tentRamp_nonneg x (j + 1) L]

lemma tent_of_le (hx : StrictMono x) {j : ℕ} {L : ℝ} (h : L ≤ x j) : tent x j L = 0 := by
  unfold tent
  rw [tentRamp_of_le hx h, tentRamp_of_le hx (h.trans (hx.monotone (Nat.le_succ j)))]; simp

lemma tent_of_ge (hx : StrictMono x) {j : ℕ} {L : ℝ} (h : x (j + 2) ≤ L) : tent x j L = 0 := by
  unfold tent
  rw [tentRamp_of_ge hx ((hx.monotone (Nat.le_succ _)).trans h), tentRamp_of_ge hx h]; simp

/-- Telescoping: `Σ_{j<J} tent x j = ramp x 0 - ramp x J`. -/
lemma sum_tent (x : ℕ → ℝ) (J : ℕ) (L : ℝ) :
    ∑ j ∈ range J, tent x j L = tentRamp x 0 L - tentRamp x J L :=
  Finset.sum_range_sub' (fun k => tentRamp x k L) J

lemma continuous_tentRamp (x : ℕ → ℝ) (k : ℕ) : Continuous (tentRamp x k) := by
  unfold tentRamp
  exact (continuous_const.max ((continuous_const.min ((continuous_id.sub continuous_const).div_const _))))

lemma continuous_tent (x : ℕ → ℝ) (j : ℕ) : Continuous (tent x j) :=
  (continuous_tentRamp x j).sub (continuous_tentRamp x (j + 1))

/-- Each ramp is `1/(x_{k+1} - x_k)`-Lipschitz. -/
lemma tentRamp_lipschitz (hx : StrictMono x) (k : ℕ) (L L' : ℝ) :
    |tentRamp x k L - tentRamp x k L'| ≤ |L - L'| / (x (k + 1) - x k) := by
  have hp : 0 < x (k + 1) - x k := sub_pos.2 (hx (Nat.lt_succ_self k))
  unfold tentRamp
  refine (abs_max_sub_max_le_max _ _ _ _).trans ?_
  refine max_le (by simp; positivity) ?_
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  refine max_le (by simp; positivity) ?_
  rw [← sub_div, abs_div, abs_of_pos hp]
  have : (L - x k) - (L' - x k) = L - L' := by ring
  rw [this]

/-- The tent `χ_j` is `(1/g_j + 1/g_{j+1})`-Lipschitz, `g_k = x_{k+1} - x_k`. -/
lemma tent_lipschitz (hx : StrictMono x) (j : ℕ) (L L' : ℝ) :
    |tent x j L - tent x j L'| ≤ |L - L'| / (x (j + 1) - x j) + |L - L'| / (x (j + 2) - x (j + 1)) := by
  unfold tent
  have h1 := tentRamp_lipschitz hx j L L'
  have h2 := tentRamp_lipschitz hx (j + 1) L L'
  have e : (L - L' : ℝ) = L - L' := rfl
  calc |tentRamp x j L - tentRamp x (j + 1) L - (tentRamp x j L' - tentRamp x (j + 1) L')|
      = |(tentRamp x j L - tentRamp x j L') - (tentRamp x (j + 1) L - tentRamp x (j + 1) L')| := by ring_nf
    _ ≤ |tentRamp x j L - tentRamp x j L'| + |tentRamp x (j + 1) L - tentRamp x (j + 1) L'| := abs_sub _ _
    _ ≤ _ := by
      have : x (j + 1 + 1) = x (j + 2) := rfl
      rw [this] at h2
      linarith

/-- The tent partition of unity: `χ_j = tent x j`, `j < J`, is a `BoasPartition` of `[a, b] ⊆ [x_1, x_J]`, supported in
`[x_0, x_{J+1}]`. -/
theorem tentPartition (hx : StrictMono x) {J : ℕ} {a b : ℝ} (ha : x 1 ≤ a) (hb : b ≤ x J) :
    BoasPartition J (tent x) a b (x 0) (x (J + 1)) where
  meas j _ := (continuous_tent x j).measurable
  nonneg j _ L := tent_nonneg hx j L
  sum_le_one L := by
    rw [sum_tent]; linarith [tentRamp_le_one x 0 L, tentRamp_nonneg x J L]
  sum_eq_one L hL := by
    rw [sum_tent, tentRamp_of_ge hx (ha.trans hL.1), tentRamp_of_le hx (hL.2.trans hb)]; ring
  supp j hj L hL := by
    rcases not_and_or.1 hL with h | h
    · exact tent_of_le hx ((not_le.1 h).le.trans (hx.monotone (Nat.zero_le j)))
    · exact tent_of_ge hx ((hx.monotone (by omega : j + 2 ≤ J + 1)).trans (not_le.1 h).le)
  lo_le_hi := hx.monotone (Nat.zero_le _)

end generic

/-! ### The node grid `x_{k+1} = x_k + min(x_k, 1)/36` -/

/-- The node grid of the tent partition: `x_0 = a`, `x_{k+1} = x_k + min(x_k, 1)/36`. -/
noncomputable def tentNode (a : ℝ) : ℕ → ℝ
  | 0 => a
  | k + 1 => tentNode a k + min (tentNode a k) 1 / 36

lemma tentNode_succ (a : ℝ) (k : ℕ) : tentNode a (k + 1) = tentNode a k + min (tentNode a k) 1 / 36 := rfl

lemma tentNode_pos {a : ℝ} (ha : 0 < a) (k : ℕ) : 0 < tentNode a k := by
  induction k with
  | zero => exact ha
  | succ k ih => rw [tentNode_succ]; have := lt_min ih one_pos; linarith

lemma tentNode_strictMono {a : ℝ} (ha : 0 < a) : StrictMono (tentNode a) := by
  refine strictMono_nat_of_lt_succ fun k => ?_
  rw [tentNode_succ]; have := lt_min (tentNode_pos ha k) one_pos; linarith


section grid

variable {a : ℝ}

/-- The half-width `δ_j = min(L_j, 1)/36` of block `j`, with centre `L_j = x_{j+1}`. -/
noncomputable def tentDelta (a : ℝ) (j : ℕ) : ℝ := min (tentNode a (j + 1)) 1 / 36

lemma tentDelta_pos (ha : 0 < a) (j : ℕ) : 0 < tentDelta a j := by
  unfold tentDelta; have := lt_min (tentNode_pos ha (j + 1)) one_pos; positivity

/-- `x_{j+2} = L_j + δ_j`. -/
lemma tentNode_add_delta (a : ℝ) (j : ℕ) : tentNode a (j + 2) = tentNode a (j + 1) + tentDelta a j := rfl

/-- `L_j - δ_j ≤ x_j`. -/
lemma tentNode_sub_delta_le (ha : 0 < a) (j : ℕ) : tentNode a (j + 1) - tentDelta a j ≤ tentNode a j := by
  have h1 : tentNode a j ≤ tentNode a (j + 1) := (tentNode_strictMono ha).monotone (Nat.le_succ j)
  have h2 : min (tentNode a j) 1 ≤ min (tentNode a (j + 1)) 1 := min_le_min h1 le_rfl
  have e := tentNode_succ a j
  unfold tentDelta; linarith

/-- **Block support**: `supp χ_j ⊆ [L_j - δ_j, L_j + δ_j]`, `L_j = x_{j+1}`, `δ_j = min(L_j,1)/36`. -/
theorem tentNode_block_support (ha : 0 < a) (j : ℕ) (L : ℝ) (hL : tent (tentNode a) j L ≠ 0) :
    L ∈ Icc (tentNode a (j + 1) - tentDelta a j) (tentNode a (j + 1) + tentDelta a j) := by
  have hx := tentNode_strictMono ha
  constructor
  · by_contra h
    exact hL (tent_of_le hx (by linarith [tentNode_sub_delta_le ha j, not_le.1 h]))
  · by_contra h
    exact hL (tent_of_ge hx (by rw [tentNode_add_delta]; exact (not_le.1 h).le))

/-- `min(x_{j+1}, 1) ≤ (37/36) min(x_j, 1)`. -/
lemma min_tentNode_succ_le (ha : 0 < a) (j : ℕ) :
    min (tentNode a (j + 1)) 1 ≤ 37 / 36 * min (tentNode a j) 1 := by
  have hp := tentNode_pos ha j
  have e := tentNode_succ a j
  have m1 := min_le_left (tentNode a (j + 1)) 1
  have m2 := min_le_right (tentNode a (j + 1)) 1
  rcases le_total (tentNode a j) 1 with h | h
  · rw [min_eq_left h] at e ⊢; linarith
  · rw [min_eq_right h]; linarith

/-- **Lipschitz bound of the tent**: `|χ_j(L) - χ_j(L')| ≤ (3/δ_j)|L - L'|` for all `L, L' ∈ ℝ` (the zero extension). -/
theorem tent_lipschitz_tentNode (ha : 0 < a) (j : ℕ) (L L' : ℝ) :
    |tent (tentNode a) j L - tent (tentNode a) j L'| ≤ 3 / tentDelta a j * |L - L'| := by
  have hx := tentNode_strictMono ha
  refine (tent_lipschitz hx j L L').trans ?_
  have hδ := tentDelta_pos ha j
  have e1 : tentNode a (j + 2) - tentNode a (j + 1) = tentDelta a j := by rw [tentNode_add_delta]; ring
  have e2 : tentNode a (j + 1) - tentNode a j = min (tentNode a j) 1 / 36 := by rw [tentNode_succ]; ring
  have hg : 0 < min (tentNode a j) 1 / 36 := by have := lt_min (tentNode_pos ha j) one_pos; positivity
  have h37 : tentDelta a j ≤ 37 / 36 * (min (tentNode a j) 1 / 36) := by
    unfold tentDelta; have := min_tentNode_succ_le ha j; linarith
  rw [e1, e2]
  have h3 : |L - L'| / (min (tentNode a j) 1 / 36) ≤ 37 / 36 / tentDelta a j * |L - L'| := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hg hδ]
    have := abs_nonneg (L - L')
    nlinarith [mul_le_mul_of_nonneg_left h37 this]
  have h4 : |L - L'| / tentDelta a j = 1 / tentDelta a j * |L - L'| := by ring
  have h5 : 37 / 36 / tentDelta a j * |L - L'| + 1 / tentDelta a j * |L - L'| ≤ 3 / tentDelta a j * |L - L'| := by
    rw [← add_mul]; refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rw [← add_div]; exact div_le_div_of_nonneg_right (by norm_num) hδ.le
  linarith

/-- Above `1` the grid is uniform: `x_{K+m} ≥ 1 + m/36` once `x_K ≥ 1`. -/
lemma tentNode_uniform {K : ℕ} (hK : 1 ≤ tentNode a K) (m : ℕ) :
    1 + (m : ℝ) / 36 ≤ tentNode a (K + m) := by
  induction m with
  | zero => simpa using hK
  | succ m ih =>
    have h1 : 1 ≤ tentNode a (K + m) := by have : (0 : ℝ) ≤ m / 36 := by positivity
                                           linarith
    rw [← add_assoc, tentNode_succ, min_eq_right h1]
    push_cast; linarith

/-- Below `1` the grid is geometric: `x_k ≥ (37/36)^k a` as long as the earlier nodes are `≤ 1`. -/
lemma tentNode_geometric (a : ℝ) (k : ℕ) (h : ∀ i < k, tentNode a i ≤ 1) :
    (37 / 36 : ℝ) ^ k * a ≤ tentNode a k := by
  induction k with
  | zero => simp [tentNode]
  | succ k ih =>
    have h1 := h k (Nat.lt_succ_self k)
    have := ih fun i hi => h i (Nat.lt_succ_of_lt hi)
    rw [tentNode_succ, min_eq_left h1, pow_succ]
    nlinarith

/-- `log(37/36) ≥ 1/37`. -/
lemma one_div_le_log_37_36 : (1 : ℝ) / 37 ≤ Real.log (37 / 36) := by
  have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 37 / 36 by norm_num)
  have e : (1 : ℝ) - (37 / 36)⁻¹ = 1 / 37 := by norm_num
  linarith

/-- For `0 < a ≤ 1` some node `x_K ≥ 1` with `K ≤ 37 log(1/a) + 1`. -/
lemma exists_tentNode_one_le (ha : 0 < a) (ha1 : a ≤ 1) :
    ∃ K : ℕ, (K : ℝ) ≤ 37 * Real.log (1 / a) + 1 ∧ 1 ≤ tentNode a K := by
  have hl : 0 < Real.log (37 / 36) := lt_of_lt_of_le (by norm_num) one_div_le_log_37_36
  have hla : 0 ≤ Real.log (1 / a) := Real.log_nonneg (by rw [le_div_iff₀ ha]; linarith)
  refine ⟨⌈Real.log (1 / a) / Real.log (37 / 36)⌉₊, ?_, ?_⟩
  · have h1 := Nat.ceil_lt_add_one (div_nonneg hla hl.le)
    have h2 : Real.log (1 / a) / Real.log (37 / 36) ≤ 37 * Real.log (1 / a) := by
      rw [div_le_iff₀ hl]; nlinarith [one_div_le_log_37_36]
    linarith
  · by_contra hK
    rw [not_le] at hK
    set K := ⌈Real.log (1 / a) / Real.log (37 / 36)⌉₊ with hKdef
    have hx := tentNode_strictMono ha
    have hgeo := tentNode_geometric a K (fun i hi => ((hx.monotone hi.le).trans hK.le))
    have hK2 : Real.log (1 / a) ≤ K * Real.log (37 / 36) := by
      have := Nat.le_ceil (Real.log (1 / a) / Real.log (37 / 36))
      rwa [div_le_iff₀ hl] at this
    have h3 : 1 / a ≤ (37 / 36 : ℝ) ^ K := by
      have : Real.log (1 / a) ≤ Real.log ((37 / 36 : ℝ) ^ K) := by rw [Real.log_pow]; exact hK2
      exact (Real.log_le_log_iff (by positivity) (by positivity)).1 this
    have : 1 ≤ (37 / 36 : ℝ) ^ K * a := by
      have := mul_le_mul_of_nonneg_right h3 ha.le
      rwa [one_div, inv_mul_cancel₀ ha.ne'] at this
    linarith

/-- **Block count**: for `0 < a ≤ 1`, `b ≥ 0` there is `J ≥ 1` with `x_J ≥ b` and
`J ≤ 37 log(1/a) + 36 b + 3` (that is `O(log c)` for `a ≍ c^{-2/21}`, `b = O(log log c)`). -/
theorem exists_tentNode_ge (ha : 0 < a) (ha1 : a ≤ 1) {b : ℝ} (hb : 0 ≤ b) :
    ∃ J : ℕ, 1 ≤ J ∧ b ≤ tentNode a J ∧ (J : ℝ) ≤ 37 * Real.log (1 / a) + 36 * b + 3 := by
  obtain ⟨K, hK, hK1⟩ := exists_tentNode_one_le ha ha1
  refine ⟨K + (⌈36 * b⌉₊ + 1), by omega, ?_, ?_⟩
  · have h1 := tentNode_uniform hK1 (⌈36 * b⌉₊ + 1)
    have h2 := Nat.le_ceil (36 * b)
    push_cast at h1
    linarith
  · have h2 := Nat.ceil_lt_add_one (show 0 ≤ 36 * b by positivity)
    push_cast
    linarith

/-- `x_1 ≤ L_min` for the start `x_0 = 5L_min/6`. -/
lemma tentNode_one_le {Lmin : ℝ} (hL : 0 < Lmin) : tentNode (5 / 6 * Lmin) 1 ≤ Lmin := by
  rw [tentNode_succ]
  have : min (tentNode (5 / 6 * Lmin) 0) 1 ≤ 5 / 6 * Lmin := min_le_left _ _
  have e0 : tentNode (5 / 6 * Lmin) 0 = 5 / 6 * Lmin := rfl
  rw [e0] at this ⊢
  linarith

/-- **The tent partition of `[L_min, L_far + 1]`** (`ct:boas` Step 3): for `0 < L_min ≤ 1`, `L_far + 1 ≥ 0` there is a number
`J ≥ 1` of blocks, `J ≤ 37 log(6/(5 L_min)) + 36(L_far + 1) + 3 = O(log c)`, such that `χ_j = tent x j` (`x = tentNode (5L_min/6)`)
form a `BoasPartition` with `Σ_j χ_j = 1` on `[L_min, L_far+1]` and supports in `[5L_min/6, x_{J+1}]`. -/
theorem tentGrid_boasPartition {Lmin Lfar : ℝ} (hL : 0 < Lmin) (hL1 : Lmin ≤ 1) (hF : 0 ≤ Lfar + 1) :
    ∃ J : ℕ, 1 ≤ J ∧ (J : ℝ) ≤ 37 * Real.log (6 / (5 * Lmin)) + 36 * (Lfar + 1) + 3 ∧
      BoasPartition J (tent (tentNode (5 / 6 * Lmin))) Lmin (Lfar + 1) (5 / 6 * Lmin)
        (tentNode (5 / 6 * Lmin) (J + 1)) := by
  have ha : 0 < 5 / 6 * Lmin := by positivity
  have ha1 : 5 / 6 * Lmin ≤ 1 := by linarith
  obtain ⟨J, hJ1, hJb, hJc⟩ := exists_tentNode_ge ha ha1 hF
  refine ⟨J, hJ1, ?_, ?_⟩
  · have e : 1 / (5 / 6 * Lmin) = 6 / (5 * Lmin) := by field_simp
    rwa [e] at hJc
  · exact tentPartition (tentNode_strictMono ha) (tentNode_one_le hL) hJb

/-- **Harnack ratio of `τ₀` on `I_j^{**}`** (`ct:boas` Step 3, with the block width `3δ_j = min(L_j,1)/12`): if
`δ = min(L_j, 1)/36` and `L, L' ∈ [L_j - 3δ, L_j + 3δ]` then `L, L' > 0` and `τ₀(L)/3 ≤ τ₀(L') ≤ 3τ₀(L)`
(`tau0_ratio`; this is the block comparison `τ_j/3 ≤ τ₀(L₀) ≤ 3τ_j` needed by `hankel_frozen_P_lb`). -/
theorem tentBlock_tau0_ratio {Lj δ : ℝ} (hLj : 0 < Lj) (hδ : δ = min Lj 1 / 36) {L L' : ℝ}
    (hL : L ∈ Icc (Lj - 3 * δ) (Lj + 3 * δ)) (hL' : L' ∈ Icc (Lj - 3 * δ) (Lj + 3 * δ)) :
    0 < L ∧ 0 < L' ∧ tau0 L / 3 ≤ tau0 L' ∧ tau0 L' ≤ 3 * tau0 L := by
  have hl0 : 0 < min Lj 1 := lt_min hLj one_pos
  have hl1 : min Lj 1 ≤ Lj := min_le_left _ _
  have hl2 : min Lj 1 ≤ 1 := min_le_right _ _
  have hL0 : 0 < L := by rw [hδ] at hL; linarith [hL.1]
  have hL0' : 0 < L' := by rw [hδ] at hL'; linarith [hL'.1]
  refine ⟨hL0, hL0', ?_⟩
  apply tau0_ratio hL0 hL0'
  rw [hδ] at hL hL'
  have hm : 11 / 12 * min Lj 1 ≤ min (min L L') 1 :=
    le_min (le_min (by linarith [hL.1]) (by linarith [hL'.1])) (by linarith)
  rw [abs_le]; constructor <;> linarith [hL.1, hL.2, hL'.1, hL'.2]

/-- The enlarged block `I_j^{**} = [L_j - 3δ_j, L_j + 3δ_j]`, `L_j = x_{j+1}`, `δ_j = min(L_j,1)/36`. -/
noncomputable def tentQ (a : ℝ) (j : ℕ) : Set ℝ :=
  Icc (tentNode a (j + 1) - 3 * tentDelta a j) (tentNode a (j + 1) + 3 * tentDelta a j)

lemma measurableSet_tentQ (a : ℝ) (j : ℕ) : MeasurableSet (tentQ a j) := measurableSet_Icc

/-- The gaps are nondecreasing: `x_{n+m} - x_n ≥ m·min(x_n,1)/36`. -/
lemma tentNode_gap_ge (ha : 0 < a) (n m : ℕ) :
    (m : ℝ) * (min (tentNode a n) 1 / 36) ≤ tentNode a (n + m) - tentNode a n := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : min (tentNode a n) 1 ≤ min (tentNode a (n + m)) 1 :=
      min_le_min ((tentNode_strictMono ha).monotone (Nat.le_add_right n m)) le_rfl
    rw [← add_assoc, tentNode_succ]
    push_cast; linarith

/-- Two blocks `I_j^{**}`, `I_{j'}^{**}` (`j ≤ j'`) with a common point have `j' - j ≤ 6`. -/
lemma tentQ_index_gap (ha : 0 < a) {j j' : ℕ} (hjj : j ≤ j') {L : ℝ} (h1 : L ∈ tentQ a j)
    (h2 : L ∈ tentQ a j') : j' - j ≤ 6 := by
  have hℓ : 0 < min (tentNode a (j + 1)) 1 := lt_min (tentNode_pos ha _) one_pos
  have hgap := tentNode_gap_ge ha (j + 1) (j' - j)
  have e : j + 1 + (j' - j) = j' + 1 := by omega
  rw [e] at hgap
  -- `ℓ' ≤ ℓ + (v - u)`
  have hu : tentNode a (j + 1) ≤ tentNode a (j' + 1) :=
    (tentNode_strictMono ha).monotone (by omega)
  have hm : min (tentNode a (j' + 1)) 1 ≤ min (tentNode a (j + 1)) 1 + (tentNode a (j' + 1) - tentNode a (j + 1)) := by
    rcases le_total (tentNode a (j + 1)) 1 with h | h
    · rw [min_eq_left h]; linarith [min_le_left (tentNode a (j' + 1)) 1]
    · rw [min_eq_right h]; linarith [min_le_right (tentNode a (j' + 1)) 1, sub_nonneg.2 hu]
  unfold tentQ tentDelta at h1 h2
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  by_contra hcon
  have h7 : (7 : ℝ) ≤ ((j' - j : ℕ) : ℝ) := by exact_mod_cast (by omega : 7 ≤ j' - j)
  set ℓ := min (tentNode a (j + 1)) 1
  set ℓ' := min (tentNode a (j' + 1)) 1
  set d := tentNode a (j' + 1) - tentNode a (j + 1)
  have hd : d ≤ (ℓ + ℓ') / 12 := by linarith
  have hd2 : (7 : ℝ) * (ℓ / 36) ≤ d := by
    have := mul_le_mul_of_nonneg_right h7 (show 0 ≤ ℓ / 36 by positivity)
    linarith
  nlinarith

/-- **Bounded overlap** (`ct:Bj-pointwise`(a)): at most `7` of the blocks `I_j^{**}` contain a given `L`. -/
theorem tentQ_overlap (ha : 0 < a) (J : ℕ) (L : ℝ) :
    ∑ j ∈ range J, (tentQ a j).indicator (fun _ => (1 : ℝ)) L ≤ 7 := by
  classical
  set S := (range J).filter (fun j => L ∈ tentQ a j) with hS
  have e : ∑ j ∈ range J, (tentQ a j).indicator (fun _ => (1 : ℝ)) L = (S.card : ℝ) := by
    rw [hS, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hL : L ∈ tentQ a j <;> simp [hL, Set.indicator]
  rw [e]
  have hc : S.card ≤ 7 := by
    rcases S.eq_empty_or_nonempty with h | h
    · rw [h]; simp
    · set j1 := S.min' h
      have hsub : S ⊆ Finset.Icc j1 (j1 + 6) := by
        intro j hj
        have hj1 : j1 ≤ j := S.min'_le j hj
        have hm1 : j1 ∈ S := S.min'_mem h
        have := tentQ_index_gap ha hj1 (Finset.mem_filter.1 hm1).2 (Finset.mem_filter.1 hj).2
        exact Finset.mem_Icc.2 ⟨hj1, by omega⟩
      have := Finset.card_le_card hsub
      rw [Nat.card_Icc] at this
      omega
  exact_mod_cast hc

/-- **`ct:boas-ineq` for the tent partition.**  `boas_ineq_assembled` for `χ_j = tent x j`, `Q_j = I_j^{**}`
(`tentQ`), `x = tentNode (5L_min/6)`, with the geometry discharged: measurability of `Q_j`, the overlap bound `K₀ = 7`
(`tentQ_overlap`), the partition property on `[L_min, L_far + 1]` (`tentPartition`; any `J` with `L_far + 1 ≤ x_J`, and
`exists_tentNode_ge` gives one with `J = O(log c)`).  The remaining hypotheses are `BoasSetting` and the paper inputs
`BoasInputs`. -/
theorem boas_ineq_tent {h X ν wt sf : ℝ → ℝ} {Lmin Lfar : ℝ} (hL : 0 < Lmin) {J : ℕ}
    (hJ : Lfar + 1 ≤ tentNode (5 / 6 * Lmin) J)
    {W A B Kd s : ℕ → ℝ} {e : ℝ → ℝ} {M εfar εhi εlo Pb κ Kstar εe εs : ℝ}
    (hS : BoasSetting h X ν wt sf)
    (hI : BoasInputs h X ν wt sf Lmin Lfar J (tent (tentNode (5 / 6 * Lmin))) (tentQ (5 / 6 * Lmin))
      W A B Kd s e M εfar εhi εlo Pb κ Kstar εe εs) :
    -(εfar + 3 * εhi + 3 * εlo + Pb * (tentNode (5 / 6 * Lmin) (J + 1) - 5 / 6 * Lmin) + Kstar * 7 * εe + 3 * εs +
        J * κ * M) ≤ ∫ L in Ici Lmin, wt L * (h L * boasKernel X L) :=
  boas_ineq_assembled (K0 := 7) hS (tentPartition (tentNode_strictMono (by positivity)) (tentNode_one_le hL) hJ)
    (fun j _ => measurableSet_tentQ _ j) (fun L => tentQ_overlap (by positivity) J L) hI

end grid

/-- info: 'FormalResearch.SignUncertainty.tentPartition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tentPartition

/-- info: 'FormalResearch.SignUncertainty.tentGrid_boasPartition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tentGrid_boasPartition

/-- info: 'FormalResearch.SignUncertainty.tent_lipschitz_tentNode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tent_lipschitz_tentNode

/-- info: 'FormalResearch.SignUncertainty.tentNode_block_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tentNode_block_support

/-- info: 'FormalResearch.SignUncertainty.exists_tentNode_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_tentNode_ge

/-- info: 'FormalResearch.SignUncertainty.tentQ_overlap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tentQ_overlap

/-- info: 'FormalResearch.SignUncertainty.boas_ineq_tent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boas_ineq_tent

/-- info: 'FormalResearch.SignUncertainty.tentBlock_tau0_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tentBlock_tau0_ratio

end FormalResearch.SignUncertainty
