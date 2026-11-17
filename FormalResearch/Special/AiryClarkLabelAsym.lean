module

public import FormalResearch.Special.AiryClarkLabel

/-!
# The Clark nodes lie asymptotically half-way between consecutive zeros of `Ai`

For fixed `c = cot α` (`sin α ≠ 0`) the node `z_{k+1}(c)` of `ψ_α` in the gap `(a_{k+1}, a_k)` is within `|c|/|a_k|` of the zero `b` of `Ai'` in
that gap, and `b` is asymptotically the midpoint (`airyAi'_zero_midpoint`).  Hence, **proved** for every real `c` and `k ≥ 2`,

`|(a_k - z_{k+1}(c))/(a_k - a_{k+1}) - 1/2| ≤ 0.4/k + 0.3 |c| k^{-1/3}`        (`airyClarkNode_fraction_le`),

so the fraction tends to `1/2` (`tendsto_airyClarkNode_fraction`): the CFT note's "the nodes lie asymptotically half-way between consecutive
Airy zeros" (`GENERAL_THEOREMS.md` §1, `verify_gen_clark_airy.py` (1b): fractions `0.4645, 0.5275, 0.5000` at `k = 2000`), with the explicit
`k^{-1/3}` rate that the survey predicts.  Numerical check of the stated bound (mpmath, 30 digits, `c ∈ {1, -3, 1/2, 20, -0.01}`, `k = 2…59`):
the largest ratio `|fraction - 1/2| / (0.4/k + 0.3|c|k^{-1/3})` is `0.58`.

Proof.  `m = Ai'/Ai` satisfies `m' = x - m² ≤ x` (Riccati), so on the gap `(a_{k+1}, a_k)` (where `x ≤ a_k < 0`) one has
`m(x) - m(y) ≥ |a_k| (y - x)` (`airyRatio_sub_ge`); with `m(z_{k+1}(c)) = c` and `m(b) = 0` this is `|z - b| ≤ |c|/|a_k|`
(`airyClarkNode_sub_le`).  The explicit rate uses `|a_k| ≥ 2.5 k^{2/3}` and `a_k - a_{k+1} ≥ 1.8 (k+1)^{-1/3}` (`AiryZeroSpacing`).

Not formalised: the node *phase* statement `ψ_α(-v) ≍ v^{1/4} cos(ζ + π/4 + O(v^{-1/2}))` itself (this module proves the consequence for
the node location, in the form used by the labelling); the sharp constant in the rate; uniformity in `α` (the bound is `O(|cot α|)`, so it
is uniform on compact subsets of `α ∈ (0, π)`).
-/

@[expose] public section

open Set Filter Topology
open scoped Real

namespace FormalResearch.Special

/-- Riccati equation: `m' = x - m²` for `m = Ai'/Ai`. -/
lemma hasDerivAt_airyRatio_riccati {x : ℝ} (hx : airyAi x ≠ 0) :
    HasDerivAt airyRatio (x - airyRatio x ^ 2) x := by
  refine (hasDerivAt_airyRatio hx).congr_deriv ?_
  unfold airyRatio
  field_simp
  ring

/-- On the gap `G_n`, `n ≥ 2`: `m(x) - m(y) ≥ |a_{n-1}| (y - x)` for `x ≤ y`. -/
lemma airyRatio_sub_ge {n : ℕ} (hn : 2 ≤ n) {x y : ℝ} (hx : x ∈ airyClarkGap n) (hy : y ∈ airyClarkGap n)
    (hxy : x ≤ y) : (-airyZero (n - 1)) * (y - x) ≤ airyRatio x - airyRatio y := by
  have hn1 : 1 ≤ n := by omega
  have key := (convex_airyClarkGap n).image_sub_le_mul_sub_of_deriv_le
    (f := airyRatio) (C := airyZero (n - 1)) (continuousOn_airyRatio hn1)
    (fun z hz => by
      rw [(isOpen_airyClarkGap n).interior_eq] at hz
      exact (hasDerivAt_airyRatio (airyAi_ne_zero_of_mem_gap hn1 hz)).differentiableAt.differentiableWithinAt)
    (fun z hz => by
      rw [(isOpen_airyClarkGap n).interior_eq] at hz
      rw [(hasDerivAt_airyRatio_riccati (airyAi_ne_zero_of_mem_gap hn1 hz)).deriv]
      have hz2 := (mem_airyClarkGap.1 hz).2.resolve_left (by omega)
      nlinarith [sq_nonneg (airyRatio z)]) x hx y hy hxy
  linarith

/-- **The node is within `|c|/|a_{n-1}|` of the zero `z_n(0)` of `Ai'`** (`n ≥ 2`). -/
theorem airyClarkNode_sub_le {n : ℕ} (hn : 2 ≤ n) (c : ℝ) :
    |airyClarkNode c n - airyClarkNode 0 n| * (-airyZero (n - 1)) ≤ |c| := by
  have hn1 : 1 ≤ n := by omega
  have hc := airyClarkNode_mem_gap hn1 c
  have h0 := airyClarkNode_mem_gap hn1 0
  have rc := airyRatio_airyClarkNode hn1 c
  have r0 := airyRatio_airyClarkNode hn1 0
  have hpos : 0 < -airyZero (n - 1) := neg_pos.2 (airyZero_neg _)
  rcases le_total (airyClarkNode c n) (airyClarkNode 0 n) with h | h
  · have := airyRatio_sub_ge hn hc h0 h
    rw [rc, r0] at this
    rw [abs_of_nonpos (by linarith : airyClarkNode c n - airyClarkNode 0 n ≤ 0)]
    have : c ≥ 0 := by nlinarith
    rw [abs_of_nonneg this]
    nlinarith
  · have := airyRatio_sub_ge hn h0 hc h
    rw [rc, r0] at this
    rw [abs_of_nonneg (by linarith : 0 ≤ airyClarkNode c n - airyClarkNode 0 n)]
    have : c ≤ 0 := by nlinarith
    rw [abs_of_nonpos this]
    nlinarith

/-- **Half-way location, explicit form** (`k ≥ 2`): the node `z_{k+1}(c)` in the gap `(a_{k+1}, a_k)`. -/
theorem airyClarkNode_fraction_le' {k : ℕ} (hk : 2 ≤ k) (c : ℝ) :
    |(airyZero k - airyClarkNode c (k + 1)) / (airyZero k - airyZero (k + 1)) - 1 / 2| ≤
      0.4 / k + |c| / ((-airyZero k) * (airyZero k - airyZero (k + 1))) := by
  have hn : 2 ≤ k + 1 := by omega
  have hgap : 0 < airyZero k - airyZero (k + 1) := by
    have := airyZero_strictAnti (n := k) (by omega); linarith
  have hb := airyClarkNode_spec (n := k + 1) (by omega) 0
  have hbz : airyAi' (airyClarkNode 0 (k + 1)) = 0 := by rw [hb.2]; simp
  have hb1 : airyZero (k + 1) < airyClarkNode 0 (k + 1) := airyZero_lt_airyClarkNode (by omega) 0
  have hb2 : airyClarkNode 0 (k + 1) < airyZero k := by
    have := airyClarkNode_lt_airyZero (n := k + 1) hn 0
    simpa using this
  have hmid := airyAi'_zero_midpoint hk hb1 hb2 hbz
  have hsub := airyClarkNode_sub_le (n := k + 1) hn c
  have e : k + 1 - 1 = k := by omega
  rw [e] at hsub
  have hak : 0 < -airyZero k := neg_pos.2 (airyZero_neg k)
  set z := airyClarkNode c (k + 1)
  set b := airyClarkNode 0 (k + 1)
  set g := airyZero k - airyZero (k + 1) with hg
  have h1 : (airyZero k - z) / g - 1 / 2 = ((airyZero k - b) / g - 1 / 2) + (b - z) / g := by
    field_simp; ring
  rw [h1]
  refine (abs_add_le _ _).trans ?_
  refine add_le_add hmid ?_
  rw [abs_div, abs_of_pos hgap, div_le_div_iff₀ hgap (mul_pos hak hgap)]
  have : |b - z| * (-airyZero k) ≤ |c| := by rw [abs_sub_comm]; exact hsub
  nlinarith [abs_nonneg (b - z)]

/-- The cube-root comparison `k^{1/3} ≤ 1.35 · k^{2/3} (k+1)^{-1/3}` for `k ≥ 2`. -/
lemma airyClark_rpow_aux {k : ℕ} (hk : 2 ≤ k) :
    (k : ℝ) ^ (1 / 3 : ℝ) ≤ 1.35 * ((k : ℝ) ^ (2 / 3 : ℝ) * ((k : ℝ) + 1) ^ (-(1 / 3) : ℝ)) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hP : ((k : ℝ) ^ (2 / 3 : ℝ)) ^ 3 = (k : ℝ) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hk0.le]; norm_num
  have hT : ((k : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = (k : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hk0.le]; norm_num
  have hQ : (((k : ℝ) + 1) ^ (-(1 / 3) : ℝ)) ^ 3 = 1 / ((k : ℝ) + 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
    rw [Real.rpow_neg_one]
  have hpos : 0 ≤ 1.35 * ((k : ℝ) ^ (2 / 3 : ℝ) * ((k : ℝ) + 1) ^ (-(1 / 3) : ℝ)) := by positivity
  refine le_of_pow_le_pow_left₀ (by norm_num : 3 ≠ 0) hpos ?_
  rw [hT, mul_pow, mul_pow, hP, hQ]
  rw [show (1.35 : ℝ) ^ 3 * ((k : ℝ) ^ 2 * (1 / ((k : ℝ) + 1))) = 1.35 ^ 3 * (k : ℝ) ^ 2 / ((k : ℝ) + 1) by ring]
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- **The nodes lie asymptotically half-way between consecutive zeros of `Ai`, with rate `k^{-1/3}`** (`k ≥ 2`). -/
theorem airyClarkNode_fraction_le {k : ℕ} (hk : 2 ≤ k) (c : ℝ) :
    |(airyZero k - airyClarkNode c (k + 1)) / (airyZero k - airyZero (k + 1)) - 1 / 2| ≤
      0.4 / k + 0.3 * |c| * (k : ℝ) ^ (-(1 / 3) : ℝ) := by
  refine (airyClarkNode_fraction_le' hk c).trans ?_
  refine add_le_add le_rfl ?_
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  obtain ⟨h1, -⟩ := airyZero_abs_bounds hk
  obtain ⟨h2, -⟩ := airyZero_gap_bounds hk
  set P := (k : ℝ) ^ (2 / 3 : ℝ) with hP
  set Q := ((k : ℝ) + 1) ^ (-(1 / 3) : ℝ) with hQ
  have hPpos : 0 < P := by positivity
  have hQpos : 0 < Q := by positivity
  have hprod : 2.5 * P * (1.8 * Q) ≤ (-airyZero k) * (airyZero k - airyZero (k + 1)) :=
    mul_le_mul h1 h2 (by positivity) (by linarith [neg_pos.2 (airyZero_neg k)])
  have haux := airyClark_rpow_aux hk
  have hT : 0 < (k : ℝ) ^ (1 / 3 : ℝ) := by positivity
  have hrel : (k : ℝ) ^ (-(1 / 3) : ℝ) * (k : ℝ) ^ (1 / 3 : ℝ) = 1 := by
    rw [← Real.rpow_add hk0]; norm_num
  have hpos' : 0 < (-airyZero k) * (airyZero k - airyZero (k + 1)) :=
    mul_pos (neg_pos.2 (airyZero_neg k)) (by have := airyZero_strictAnti (n := k) (by omega); linarith)
  rw [div_le_iff₀ hpos']
  have hc0 := abs_nonneg c
  have hm : 0 < (k : ℝ) ^ (-(1 / 3) : ℝ) := by positivity
  -- `(0.3 |c| k^{-1/3}) · (-a_k)(gap) ≥ 0.3 |c| k^{-1/3} · 4.5 P Q ≥ |c|`
  have hkey : 1 ≤ 0.3 * (k : ℝ) ^ (-(1 / 3) : ℝ) * (2.5 * P * (1.8 * Q)) := by
    have : 1 = (k : ℝ) ^ (-(1 / 3) : ℝ) * (k : ℝ) ^ (1 / 3 : ℝ) := hrel.symm
    calc (1 : ℝ) = (k : ℝ) ^ (-(1 / 3) : ℝ) * (k : ℝ) ^ (1 / 3 : ℝ) := this
      _ ≤ (k : ℝ) ^ (-(1 / 3) : ℝ) * (1.35 * (P * Q)) := by gcongr
      _ = 0.3 * (k : ℝ) ^ (-(1 / 3) : ℝ) * (2.5 * P * (1.8 * Q)) / 1 * (1.35 / (0.3 * 2.5 * 1.8)) := by ring
      _ ≤ 0.3 * (k : ℝ) ^ (-(1 / 3) : ℝ) * (2.5 * P * (1.8 * Q)) := by
        have : 0 ≤ 0.3 * (k : ℝ) ^ (-(1 / 3) : ℝ) * (2.5 * P * (1.8 * Q)) := by positivity
        nlinarith
  calc |c| = |c| * 1 := (mul_one _).symm
    _ ≤ |c| * (0.3 * (k : ℝ) ^ (-(1 / 3) : ℝ) * (2.5 * P * (1.8 * Q))) := by gcongr
    _ ≤ |c| * (0.3 * (k : ℝ) ^ (-(1 / 3) : ℝ) * ((-airyZero k) * (airyZero k - airyZero (k + 1)))) := by gcongr
    _ = _ := by ring

/-- **The fraction tends to `1/2`** for every fixed `c = cot α`: the nodes `z_{k+1}(α)` lie asymptotically half-way between `a_{k+1}` and `a_k`. -/
theorem tendsto_airyClarkNode_fraction (c : ℝ) :
    Tendsto (fun k : ℕ => (airyZero k - airyClarkNode c (k + 1)) / (airyZero k - airyZero (k + 1))) atTop (𝓝 (1 / 2)) := by
  have hg : Tendsto (fun k : ℕ => 0.4 / (k : ℝ) + 0.3 * |c| * (k : ℝ) ^ (-(1 / 3) : ℝ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => (0.4 : ℝ) / (k : ℝ)) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat 0.4
    have h2 : Tendsto (fun k : ℕ => (k : ℝ) ^ (-(1 / 3) : ℝ)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp tendsto_natCast_atTop_atTop
    simpa using h1.add (h2.const_mul (0.3 * |c|))
  have := squeeze_zero_norm' (f := fun k : ℕ => (airyZero k - airyClarkNode c (k + 1)) / (airyZero k - airyZero (k + 1)) - 1 / 2)
    (a := fun k : ℕ => 0.4 / (k : ℝ) + 0.3 * |c| * (k : ℝ) ^ (-(1 / 3) : ℝ))
    (by
      filter_upwards [eventually_ge_atTop 2] with k hk
      rw [Real.norm_eq_abs]
      exact airyClarkNode_fraction_le hk c) hg
  simpa using (tendsto_sub_nhds_zero_iff.1 this)

/-- info: 'FormalResearch.Special.airyClarkNode_fraction_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyClarkNode_fraction_le

/-- info: 'FormalResearch.Special.tendsto_airyClarkNode_fraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.tendsto_airyClarkNode_fraction

end FormalResearch.Special
