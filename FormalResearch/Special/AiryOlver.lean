module

public import FormalResearch.Special.AiryBiEnvelope

/-!
# Olver's weight functions `E`, `M`, `N` for the Airy pair, and the DLMF 9.8 modulus

**Notation.**  Two different objects are called `M` in the literature the Weyl programme quotes:

* the *DLMF 9.8 modulus*: `M²(x) = Ai(x)² + Bi(x)²` for all real `x` (`airyModSq`), with `N²(x) = Ai'(x)² + Bi'(x)²`
  (`airyModDerivSq`);
* *Olver's weight functions* (Olver, *Asymptotics and Special Functions*, Ch. 11, the pair `(E, M)` used for error
  bounds of Airy-type expansions): with `c` the point where `Ai = Bi` (numerically `c = -0.36604632...`),
  `E(x) = 1`, `M(x) = (Ai² + Bi²)^{1/2}` for `x ≤ c`, and `E(x) = (Bi/Ai)^{1/2}`, `M(x) = (2 Ai Bi)^{1/2}` for `x > c`
  (`airyOlverE`, `airyOlverM`), so that on `x > c`: `M/E = √2 Ai`, `M E = √2 Bi`.

They agree for `x ≤ c` and differ for `x > c`, where `Olver's M² = 2 Ai Bi ≤ Ai² + Bi²` (equality only at `x = c`).  Both
inequality directions quoted in the Weyl sources (`|Ai| ≤ M/E`, `|Bi| ≤ M E`) hold for Olver's `M`
(`abs_airyAi_le_airyOlverM_div_E`, `abs_airyBi_le_airyOlverM_mul_E`).

**The crossing point.**  `airyCross` is *defined* as `inf {x ≥ -1 : Ai x ≤ Bi x}`.  Proved: `-1 ≤ airyCross ≤ 0`,
`Ai ≤ Bi` on `[airyCross, ∞)`, `Bi < Ai` on `[-1, airyCross)`, and `Ai = Bi` at `airyCross` as soon as `airyCross > -1`.
**Not formalised:** the strict inequality `airyCross > -1` (it needs `Bi(-1) < Ai(-1)`, numerically `0.104 < 0.536`, with
better numerics than the ones in `AiryBiNeg`), hence the value `-0.366...`.  Nothing below uses it: all properties of
`E, M, N` hold for this `airyCross`.

**The derivative weight `N`.**  The survey does not quote Olver's formula for `N`; the downstream uses are
`|Ai'| ≤ N/E` and `N ≤ C (2+|x|)^{1/2} M`.  `airyOlverN` is therefore *defined* as the least function with
`|Ai'| ≤ N/E`, `|Bi'| ≤ N E` for `x > c` (`N = max(E|Ai'|, |Bi'|/E)`) and `N = (Ai'² + Bi'²)^{1/2}` for `x ≤ c`; this is
not claimed to coincide with Olver's `N` (numerically `Olver's N = (-2 Ai' Bi')^{1/2}` for `x > c`, which is `≥` ours there).

**Proved here:** the definitions; `E ≥ 1`, `E` monotone, `E² = Bi/Ai` for `x > c`; `M/E`, `M E`; `|Ai| ≤ M/E`, `|Bi| ≤ M E`,
`|Ai'| ≤ N/E`, `|Bi'| ≤ N E`; the elementary Wronskian bound `1/π² ≤ M² N²` for the DLMF modulus; `E^{-2} = Ai/Bi ≍ e^{-2ξ}`
and the quantitative bounds (`E² ≍ e^{2ξ}`, the sharp `2 e^{2ξ} Ai/Bi = 1 + O(x^{-3/2})`, `M² ≍ (2+|x|)^{-1/2}`,
`N ≲ (2+|x|)^{1/2} M`) are in `AiryOlverBounds`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

/-- DLMF 9.8: the squared modulus `M²(x) = Ai(x)² + Bi(x)²` (not Olver's `M²` for `x > c`, see `airyOlverM`). -/
noncomputable def airyModSq (x : ℝ) : ℝ := airyAi x ^ 2 + airyBi x ^ 2

/-- DLMF 9.8: `N²(x) = Ai'(x)² + Bi'(x)²`. -/
noncomputable def airyModDerivSq (x : ℝ) : ℝ := airyAi' x ^ 2 + airyBiDeriv x ^ 2

/-- The crossing point of `Ai` and `Bi`: `inf {x ≥ -1 : Ai x ≤ Bi x}` (numerically `-0.36604632...`, where `Ai = Bi`). -/
noncomputable def airyCross : ℝ := sInf {x : ℝ | -1 ≤ x ∧ airyAi x ≤ airyBi x}

private lemma airyCross_set_closed : IsClosed {x : ℝ | -1 ≤ x ∧ airyAi x ≤ airyBi x} :=
  (isClosed_le continuous_const continuous_id).inter
    (isClosed_le differentiable_airyAi.continuous differentiable_airyBi.continuous)

private lemma airyCross_set_nonempty : {x : ℝ | -1 ≤ x ∧ airyAi x ≤ airyBi x}.Nonempty := by
  refine ⟨0, by norm_num, ?_⟩
  rw [airyBi_zero_real]
  have := airyAi_pos (le_refl (0 : ℝ))
  have h3 : (1 : ℝ) ≤ √3 := by rw [Real.le_sqrt' (by norm_num)]; norm_num
  nlinarith

private lemma airyCross_set_bdd : BddBelow {x : ℝ | -1 ≤ x ∧ airyAi x ≤ airyBi x} :=
  ⟨-1, fun _ hx => hx.1⟩

lemma airyCross_ge : -1 ≤ airyCross :=
  le_csInf airyCross_set_nonempty (fun _ hx => hx.1)

lemma airyCross_le_zero : airyCross ≤ 0 :=
  csInf_le airyCross_set_bdd ⟨by norm_num, by
    rw [airyBi_zero_real]
    have := airyAi_pos (le_refl (0 : ℝ))
    have h3 : (1 : ℝ) ≤ √3 := by rw [Real.le_sqrt' (by norm_num)]; norm_num
    nlinarith⟩

lemma airyAi_le_airyBi_airyCross : airyAi airyCross ≤ airyBi airyCross :=
  (airyCross_set_closed.csInf_mem airyCross_set_nonempty airyCross_set_bdd).2

/-- `Ai ≤ Bi` on `[airyCross, ∞)`. -/
theorem airyAi_le_airyBi_of_ge {x : ℝ} (hx : airyCross ≤ x) : airyAi x ≤ airyBi x := by
  have hc := airyAi_le_airyBi_airyCross
  have hA := airyAi_pos_of_neg_one_le airyCross_ge
  have hA' := airyAi_pos_of_neg_one_le (airyCross_ge.trans hx)
  have h := strictMonoOn_airyBi_div_airyAi.monotoneOn (show airyCross ∈ Ici (-1) from airyCross_ge)
    (show x ∈ Ici (-1) from airyCross_ge.trans hx) hx
  have h1 : 1 ≤ airyBi airyCross / airyAi airyCross := by rw [le_div_iff₀ hA]; linarith
  have h2 : 1 ≤ airyBi x / airyAi x := h1.trans h
  rw [le_div_iff₀ hA'] at h2
  linarith

/-- `Bi < Ai` on `[-1, airyCross)`. -/
theorem airyBi_lt_airyAi_of_lt {x : ℝ} (hx1 : -1 ≤ x) (hx : x < airyCross) : airyBi x < airyAi x := by
  by_contra h
  rw [not_lt] at h
  have := csInf_le airyCross_set_bdd (show x ∈ {x : ℝ | -1 ≤ x ∧ airyAi x ≤ airyBi x} from ⟨hx1, h⟩)
  exact absurd hx (not_lt.mpr this)

/-- If `airyCross > -1` then `Ai = Bi` there (the weight functions are continuous across `airyCross`). -/
theorem airyAi_eq_airyBi_airyCross (h : -1 < airyCross) : airyAi airyCross = airyBi airyCross := by
  refine le_antisymm airyAi_le_airyBi_airyCross ?_
  have hcl : IsClosed {x : ℝ | airyBi x ≤ airyAi x} :=
    isClosed_le differentiable_airyBi.continuous differentiable_airyAi.continuous
  have hsub : Ioo (-1 : ℝ) airyCross ⊆ {x : ℝ | airyBi x ≤ airyAi x} := fun x hx =>
    (airyBi_lt_airyAi_of_lt hx.1.le hx.2).le
  have := hcl.closure_subset_iff.mpr hsub
  have hmem : airyCross ∈ closure (Ioo (-1 : ℝ) airyCross) := by
    rw [closure_Ioo (ne_of_lt h)]
    exact ⟨h.le, le_rfl⟩
  exact this hmem


/-! ### The weight functions -/

/-- Olver's weight `E`: `1` for `x ≤ airyCross`, `(Bi/Ai)^{1/2}` for `x > airyCross`. -/
noncomputable def airyOlverE (x : ℝ) : ℝ := if x ≤ airyCross then 1 else √(airyBi x / airyAi x)

/-- Olver's modulus `M`: `(Ai² + Bi²)^{1/2}` for `x ≤ airyCross`, `(2 Ai Bi)^{1/2}` for `x > airyCross`. -/
noncomputable def airyOlverM (x : ℝ) : ℝ :=
  if x ≤ airyCross then √(airyModSq x) else √(2 * airyAi x * airyBi x)

/-- The derivative weight `N` (see the module docstring): `(Ai'² + Bi'²)^{1/2}` for `x ≤ airyCross`,
`max (E |Ai'|) (|Bi'|/E)` for `x > airyCross`. -/
noncomputable def airyOlverN (x : ℝ) : ℝ :=
  if x ≤ airyCross then √(airyModDerivSq x) else max (airyOlverE x * |airyAi' x|) (|airyBiDeriv x| / airyOlverE x)

lemma airyBi_pos_of_gt {x : ℝ} (hx : airyCross < x) : 0 < airyBi x := by
  have hA := airyAi_pos_of_neg_one_le (airyCross_ge.trans hx.le)
  exact lt_of_lt_of_le hA (airyAi_le_airyBi_of_ge hx.le)

lemma airyAi_pos_of_gt {x : ℝ} (hx : airyCross < x) : 0 < airyAi x :=
  airyAi_pos_of_neg_one_le (airyCross_ge.trans hx.le)

lemma airyOlverE_of_le {x : ℝ} (hx : x ≤ airyCross) : airyOlverE x = 1 := by
  simp [airyOlverE, hx]

lemma airyOlverE_of_gt {x : ℝ} (hx : airyCross < x) : airyOlverE x = √(airyBi x / airyAi x) := by
  simp [airyOlverE, not_le.mpr hx]

/-- `E ≥ 1`. -/
theorem one_le_airyOlverE (x : ℝ) : 1 ≤ airyOlverE x := by
  by_cases hx : x ≤ airyCross
  · rw [airyOlverE_of_le hx]
  · rw [not_le] at hx
    rw [airyOlverE_of_gt hx]
    have hA := airyAi_pos_of_gt hx
    have h := airyAi_le_airyBi_of_ge hx.le
    exact Real.one_le_sqrt.mpr (by rw [le_div_iff₀ hA]; linarith)

lemma airyOlverE_pos (x : ℝ) : 0 < airyOlverE x := lt_of_lt_of_le one_pos (one_le_airyOlverE x)

/-- `E² = Bi/Ai` for `x > airyCross`. -/
theorem airyOlverE_sq {x : ℝ} (hx : airyCross < x) : airyOlverE x ^ 2 = airyBi x / airyAi x := by
  rw [airyOlverE_of_gt hx, Real.sq_sqrt]
  exact (div_pos (airyBi_pos_of_gt hx) (airyAi_pos_of_gt hx)).le

/-- **`E` is nondecreasing** (`E = 1` up to `airyCross`, then `(Bi/Ai)^{1/2}`, increasing since `Bi/Ai` is). -/
theorem monotone_airyOlverE : Monotone airyOlverE := by
  intro x y hxy
  by_cases hy : y ≤ airyCross
  · rw [airyOlverE_of_le hy, airyOlverE_of_le (hxy.trans hy)]
  · rw [not_le] at hy
    by_cases hx : x ≤ airyCross
    · rw [airyOlverE_of_le hx]; exact one_le_airyOlverE y
    · rw [not_le] at hx
      rw [airyOlverE_of_gt hx, airyOlverE_of_gt hy]
      refine Real.sqrt_le_sqrt ?_
      exact strictMonoOn_airyBi_div_airyAi.monotoneOn (show x ∈ Ici (-1) from airyCross_ge.trans hx.le)
        (show y ∈ Ici (-1) from airyCross_ge.trans hy.le) hxy

lemma airyOlverM_of_le {x : ℝ} (hx : x ≤ airyCross) : airyOlverM x = √(airyModSq x) := by
  simp [airyOlverM, hx]

lemma airyOlverM_of_gt {x : ℝ} (hx : airyCross < x) : airyOlverM x = √(2 * airyAi x * airyBi x) := by
  simp [airyOlverM, not_le.mpr hx]

/-- `M = √2 · Ai · E` for `x > airyCross`. -/
theorem airyOlverM_eq {x : ℝ} (hx : airyCross < x) : airyOlverM x = √2 * airyAi x * airyOlverE x := by
  have hA := airyAi_pos_of_gt hx
  have hB := airyBi_pos_of_gt hx
  have h : 2 * airyAi x * airyBi x = (√2 * airyAi x * airyOlverE x) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num), airyOlverE_sq hx]
    field_simp
  rw [airyOlverM_of_gt hx, h]
  exact Real.sqrt_sq (by have := airyOlverE_pos x; positivity)

/-- **`M/E = √2 Ai`** for `x > airyCross`. -/
theorem airyOlverM_div_E {x : ℝ} (hx : airyCross < x) : airyOlverM x / airyOlverE x = √2 * airyAi x := by
  rw [airyOlverM_eq hx]
  have := (airyOlverE_pos x).ne'
  field_simp

/-- **`M E = √2 Bi`** for `x > airyCross`. -/
theorem airyOlverM_mul_E {x : ℝ} (hx : airyCross < x) : airyOlverM x * airyOlverE x = √2 * airyBi x := by
  rw [airyOlverM_eq hx]
  have h := airyOlverE_sq hx
  have hA := (airyAi_pos_of_gt hx).ne'
  calc √2 * airyAi x * airyOlverE x * airyOlverE x = √2 * airyAi x * airyOlverE x ^ 2 := by ring
    _ = _ := by rw [h]; field_simp

/-- `|Ai| ≤ M/E` (all `x`). -/
theorem abs_airyAi_le_airyOlverM_div_E (x : ℝ) : |airyAi x| ≤ airyOlverM x / airyOlverE x := by
  by_cases hx : x ≤ airyCross
  · rw [airyOlverM_of_le hx, airyOlverE_of_le hx, div_one]
    exact Real.abs_le_sqrt (by unfold airyModSq; nlinarith [sq_nonneg (airyBi x)])
  · rw [not_le] at hx
    rw [airyOlverM_div_E hx, abs_of_pos (airyAi_pos_of_gt hx)]
    have := airyAi_pos_of_gt hx
    have h2 : (1 : ℝ) ≤ √2 := by rw [Real.le_sqrt' (by norm_num)]; norm_num
    nlinarith

/-- `|Bi| ≤ M E` (all `x`). -/
theorem abs_airyBi_le_airyOlverM_mul_E (x : ℝ) : |airyBi x| ≤ airyOlverM x * airyOlverE x := by
  by_cases hx : x ≤ airyCross
  · rw [airyOlverM_of_le hx, airyOlverE_of_le hx, mul_one]
    exact Real.abs_le_sqrt (by unfold airyModSq; nlinarith [sq_nonneg (airyAi x)])
  · rw [not_le] at hx
    rw [airyOlverM_mul_E hx, abs_of_pos (airyBi_pos_of_gt hx)]
    have := airyBi_pos_of_gt hx
    have h2 : (1 : ℝ) ≤ √2 := by rw [Real.le_sqrt' (by norm_num)]; norm_num
    nlinarith

/-- `|Ai'| ≤ N/E` (all `x`). -/
theorem abs_airyAi'_le_airyOlverN_div_E (x : ℝ) : |airyAi' x| ≤ airyOlverN x / airyOlverE x := by
  by_cases hx : x ≤ airyCross
  · simp only [airyOlverN, hx, ite_true]
    rw [airyOlverE_of_le hx, div_one]
    exact Real.abs_le_sqrt (by unfold airyModDerivSq; nlinarith [sq_nonneg (airyBiDeriv x)])
  · simp only [airyOlverN, hx, ite_false]
    rw [le_div_iff₀ (airyOlverE_pos x)]
    calc |airyAi' x| * airyOlverE x = airyOlverE x * |airyAi' x| := by ring
      _ ≤ _ := le_max_left _ _

/-- `|Bi'| ≤ N E` (all `x`). -/
theorem abs_airyBiDeriv_le_airyOlverN_mul_E (x : ℝ) : |airyBiDeriv x| ≤ airyOlverN x * airyOlverE x := by
  by_cases hx : x ≤ airyCross
  · simp only [airyOlverN, hx, ite_true]
    rw [airyOlverE_of_le hx, mul_one]
    exact Real.abs_le_sqrt (by unfold airyModDerivSq; nlinarith [sq_nonneg (airyAi' x)])
  · simp only [airyOlverN, hx, ite_false]
    have h := le_max_right (airyOlverE x * |airyAi' x|) (|airyBiDeriv x| / airyOlverE x)
    have hE := airyOlverE_pos x
    calc |airyBiDeriv x| = |airyBiDeriv x| / airyOlverE x * airyOlverE x := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right h hE.le

/-- **Wronskian bound for the DLMF modulus**: `1/π² ≤ M² N²` (`M² = Ai² + Bi²`, `N² = Ai'² + Bi'²`). -/
theorem one_div_pi_sq_le_airyModSq_mul (x : ℝ) : 1 / π ^ 2 ≤ airyModSq x * airyModDerivSq x := by
  have hW := airyWronskian_real x
  have : (1 / π) ^ 2 = (airyAi x * airyBiDeriv x - airyAi' x * airyBi x) ^ 2 := by rw [hW]
  rw [one_div_pow] at this
  rw [this]
  unfold airyModSq airyModDerivSq
  nlinarith [sq_nonneg (airyAi x * airyAi' x + airyBi x * airyBiDeriv x)]

lemma airyModSq_pos (x : ℝ) : 0 < airyModSq x := by
  have h := one_div_pi_sq_le_airyModSq_mul x
  have hp : 0 < 1 / π ^ 2 := by positivity
  have hN : 0 ≤ airyModDerivSq x := by unfold airyModDerivSq; positivity
  by_contra hle
  rw [not_lt] at hle
  have h0 : airyModSq x = 0 := le_antisymm hle (by unfold airyModSq; positivity)
  rw [h0, zero_mul] at h
  linarith

/-- info: 'FormalResearch.Special.airyAi_le_airyBi_of_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAi_le_airyBi_of_ge

/-- info: 'FormalResearch.Special.airyBi_lt_airyAi_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyBi_lt_airyAi_of_lt

/-- info: 'FormalResearch.Special.airyAi_eq_airyBi_airyCross' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAi_eq_airyBi_airyCross

/-- info: 'FormalResearch.Special.one_le_airyOlverE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.one_le_airyOlverE

/-- info: 'FormalResearch.Special.airyOlverE_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyOlverE_sq

/-- info: 'FormalResearch.Special.monotone_airyOlverE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.monotone_airyOlverE

/-- info: 'FormalResearch.Special.airyOlverM_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyOlverM_eq

/-- info: 'FormalResearch.Special.airyOlverM_div_E' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyOlverM_div_E

/-- info: 'FormalResearch.Special.airyOlverM_mul_E' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyOlverM_mul_E

/-- info: 'FormalResearch.Special.abs_airyAi_le_airyOlverM_div_E' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.abs_airyAi_le_airyOlverM_div_E

/-- info: 'FormalResearch.Special.abs_airyBi_le_airyOlverM_mul_E' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.abs_airyBi_le_airyOlverM_mul_E

/-- info: 'FormalResearch.Special.abs_airyAi'_le_airyOlverN_div_E' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.abs_airyAi'_le_airyOlverN_div_E

/-- info: 'FormalResearch.Special.abs_airyBiDeriv_le_airyOlverN_mul_E' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.abs_airyBiDeriv_le_airyOlverN_mul_E

/-- info: 'FormalResearch.Special.one_div_pi_sq_le_airyModSq_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.one_div_pi_sq_le_airyModSq_mul

end FormalResearch.Special
