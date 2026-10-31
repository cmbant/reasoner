import FormalResearch.FourQubitEntropy.PaperECriticalRenyiEq

/-!
# Necessity of the threshold `q_b` (`lem:fqe-renyi-grouping`, `prop:fqe-cubic-bound`)

Paper E, `renyi_cubic_bound.tex`. With `q_b = 4 ln 2/(4 ln 2 - 1)` (`qb`) and `H_q = renyiSpec q` (bits):

* **Binary threshold** (`renyi_binary_iff`): for `q > 0`, `q ≠ 1`,
  `H_q(a, 1-a) ≤ 4a(1-a)` for every `a ∈ [0,1]` iff `q ≥ q_b`. The counterexample family is
  `a = ε ↓ 0`: for `1 < q < q_b` an `ε` found from the derivative `-q` at `0` of `ε ↦ ε^q + (1-ε)^q`
  (`binary_violation_gt`), for `0 < q < 1` an explicit `ε = K^{-1/(1-q)}` (`binary_violation_lt`).
  The order `q = 1` (Shannon, not covered by `renyiSpec`, which is junk at `q = 1`) is handled
  separately by `shannon_binary_violation` (`a = 1/32`).
* **Cubic threshold** (`renyi_cubic_iff`): for `q > 0`, `q ≠ 1`, the bound
  `H_q(λ) ≤ 10/3 - 6 Σλ² + (8/3) Σλ³` holds on the whole four-point simplex iff `q ≥ q_b`
  (necessity by the binary restriction `λ = (a, 1-a, 0, 0)`, on which the right side is `4a(1-a)`).
* **Equality cases for every `q ≥ q_b`** (`renyi_binary_eq_iff_ge`): `H_q(a,1-a) = 4a(1-a)` iff
  `a ∈ {0, 1/2, 1}` (the lemma's last sentence; `renyi_binary_eq_iff` is the case `q = q_b`).
* **Numerical bounds** (`eq:fqe-binary-threshold`): `qb_bounds` (`3/2 < q_b < 313/200 < 1587/1000`),
  `rb_bounds` (`1/2 < r_b < 1`), `qb_div` (`q_b/(r_b ln 2) = 4`), `log_two_series_bounds`
  (`56/81 + 2/1215 < ln 2 < 1123/1620 < 3/4`; here from Mathlib's decimal bounds on `ln 2`, not from
  the atanh series the paper quotes).
-/

open Real Filter Topology

namespace FormalResearch.FourQubitEntropy.PaperECritical
open FormalResearch.FourQubitEntropy

/-! ### Numerical bounds on `q_b` -/

theorem rb_mul : rb * (4 * Lg - 1) = 1 := by
  have := four_Lg_sub_one_pos
  unfold rb; field_simp

/-- `56/81 + 2/1215 < ln 2 < 1123/1620 < 3/4`. -/
theorem log_two_series_bounds :
    (56 / 81 + 2 / 1215 : ℝ) < Lg ∧ Lg < 1123 / 1620 ∧ (1123 / 1620 : ℝ) < 3 / 4 := by
  have h1 := Lg_gt
  have h2 := Lg_lt
  refine ⟨?_, ?_, by norm_num⟩ <;> norm_num at h1 h2 ⊢ <;> linarith

/-- `1/2 < r_b < 1`. -/
theorem rb_bounds : 1 / 2 < rb ∧ rb < 1 := by
  have h := rb_mul
  have h1 := Lg_gt
  have h2 := Lg_lt
  have hp := four_Lg_sub_one_pos
  have hr : 0 < rb := by unfold rb; positivity
  norm_num at h1 h2
  constructor <;> nlinarith

/-- `3/2 < q_b < 313/200 < 1587/1000` (`eq:fqe-binary-threshold`). -/
theorem qb_bounds : 3 / 2 < qb ∧ qb < 313 / 200 ∧ (313 / 200 : ℝ) < 1587 / 1000 := by
  have h := rb_mul
  have h1 := Lg_gt
  have h2 := Lg_lt
  have hp := four_Lg_sub_one_pos
  have hr : 0 < rb := by unfold rb; positivity
  rw [qb_eq_rb_add_one]
  norm_num at h1 h2
  refine ⟨?_, ?_, by norm_num⟩ <;> nlinarith

/-- `q_b/(r_b ln 2) = 4`. -/
theorem qb_div : qb / (rb * Lg) = 4 := by
  have hL : 0 < Lg := by have := Lg_gt; linarith
  have hp := four_Lg_sub_one_pos
  have hr : 0 < rb := by unfold rb; positivity
  rw [div_eq_iff (by positivity)]
  unfold qb rb; field_simp

/-! ### Violation for `1 < q < q_b` -/

theorem renyiSpec_binary_eq {q : ℝ} (hq : 1 < q) {a : ℝ} :
    renyiSpec q ![a, 1 - a] = -Real.log (a ^ q + (1 - a) ^ q) / ((q - 1) * Lg) := by
  unfold renyiSpec
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  change Real.log _ / Real.log 2 / (1 - q) = _
  have : (q - 1) ≠ 0 := (sub_pos.2 hq).ne'
  have hL : Lg ≠ 0 := by have := Lg_gt; linarith
  have h1q : 1 - q ≠ 0 := by intro h; apply this; linarith
  unfold Lg
  field_simp
  ring

/-- For `1 < q < q_b` the binary bound fails for small `a`. -/
theorem binary_violation_gt {q : ℝ} (hq : 1 < q) (hlt : q < qb) :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧ 4 * a * (1 - a) < renyiSpec q ![a, 1 - a] := by
  have hL : 0 < Lg := by have := Lg_gt; linarith
  have hp := four_Lg_sub_one_pos
  -- c = 4 (q-1) L < q
  have hc : 4 * (q - 1) * Lg < q := by
    have : q * (4 * Lg - 1) < 4 * Lg := by
      have h := hlt; unfold qb at h
      rwa [lt_div_iff₀ hp] at h
    nlinarith
  set c' := (4 * (q - 1) * Lg + q) / 2 with hc'
  have hc1 : 4 * (q - 1) * Lg < c' := by rw [hc']; linarith
  have hc2 : c' < q := by rw [hc']; linarith
  -- derivative of log S at 0
  have h1 : HasDerivAt (fun x : ℝ => x ^ q) (1 * q * 0 ^ (q - 1)) 0 :=
    (hasDerivAt_id (0 : ℝ)).rpow_const (Or.inr hq.le)
  have h2 : HasDerivAt (fun x : ℝ => (1 - x) ^ q) (-1 * q * (1 - 0) ^ (q - 1)) 0 :=
    ((hasDerivAt_id (0 : ℝ)).const_sub 1).rpow_const (Or.inl (by norm_num))
  have h0 : (0 : ℝ) ^ (q - 1) = 0 := Real.zero_rpow (sub_pos.2 hq).ne'
  have hS := h1.add h2
  have hq0 : (0 : ℝ) ^ q = 0 := Real.zero_rpow (by linarith)
  have hSne : ((fun x : ℝ => x ^ q) + fun x : ℝ => (1 - x) ^ q) 0 ≠ 0 := by simp [hq0]
  have hlog0 := (hS.log (by simpa using hSne) : HasDerivAt _ _ _)
  have hlog : HasDerivAt (fun x : ℝ => Real.log (x ^ q + (1 - x) ^ q)) (-q) 0 := by
    convert hlog0 using 1
    simp [h0, hq0]
  have hslope := (hasDerivAt_iff_tendsto_slope.1 hlog).mono_left (nhdsGT_le_nhdsNE (0 : ℝ))
  have hev : ∀ᶠ x in 𝓝[>] (0 : ℝ),
      slope (fun x : ℝ => Real.log (x ^ q + (1 - x) ^ q)) 0 x < -c' ∧ x < 1 := by
    refine (hslope.eventually (gt_mem_nhds (show -q < -c' by linarith))).and ?_
    exact mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨a, ha, ha0⟩ := (hev.and self_mem_nhdsWithin).exists
  obtain ⟨hsl, ha1⟩ := ha
  have ha0' : 0 < a := ha0
  have hapos : 0 < a ^ q + (1 - a) ^ q := by
    have : 0 < (1 - a) ^ q := Real.rpow_pos_of_pos (by linarith) q
    have : 0 ≤ a ^ q := Real.rpow_nonneg ha0'.le q
    linarith
  refine ⟨a, ha0', ha1, ?_⟩
  rw [renyiSpec_binary_eq hq]
  rw [slope_def_field] at hsl
  simp only [hq0, zero_add, Real.one_rpow, sub_zero, Real.log_one] at hsl
  rw [div_lt_iff₀ ha0'] at hsl
  rw [lt_div_iff₀ (by positivity)]
  have hq1' : 0 < q - 1 := sub_pos.2 hq
  nlinarith [mul_lt_mul_of_pos_right hc1 ha0', mul_pos (mul_pos ha0' ha0') (mul_pos hq1' hL)]

/-! ### Violation for `0 < q < 1` -/

theorem renyiSpec_binary_eq_lt {q : ℝ} (hq : q < 1) {a : ℝ} :
    renyiSpec q ![a, 1 - a] = Real.log (a ^ q + (1 - a) ^ q) / ((1 - q) * Lg) := by
  unfold renyiSpec
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  change Real.log _ / Real.log 2 / (1 - q) = _
  have hL : Lg ≠ 0 := by have := Lg_gt; linarith
  have h1q : 1 - q ≠ 0 := by intro h; linarith
  unfold Lg
  field_simp

/-- For `0 < q < 1` the binary bound fails at `a = K^{-1/(1-q)}`, `K = 2 + 8(1-q)`. -/
theorem binary_violation_lt {q : ℝ} (hq0 : 0 < q) (hq : q < 1) :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧ 4 * a * (1 - a) < renyiSpec q ![a, 1 - a] := by
  have hL : 0 < Lg := by have := Lg_gt; linarith
  have hL1 : Lg < 1 := by have := Lg_lt; linarith
  set K : ℝ := 2 + 8 * (1 - q) with hK
  have hK1 : 1 < K := by rw [hK]; linarith
  have hK0 : 0 < K := by linarith
  set a : ℝ := K ^ (-(1 / (1 - q))) with ha
  have h1q : 0 < 1 - q := by linarith
  have ha0 : 0 < a := Real.rpow_pos_of_pos hK0 _
  have ha1 : a < 1 := Real.rpow_lt_one_of_one_lt_of_neg hK1 (by
    have : 0 < 1 / (1 - q) := by positivity
    linarith)
  have hexp : a ^ (q - 1) = K := by
    rw [ha, ← Real.rpow_mul hK0.le]
    have : -(1 / (1 - q)) * (q - 1) = 1 := by field_simp; ring
    rw [this, Real.rpow_one]
  have haq : a ^ q = a * K := by
    have : a ^ q = a ^ (1 + (q - 1)) := by ring_nf
    rw [this, Real.rpow_add ha0, Real.rpow_one, hexp]
  have haq1 : a ^ q ≤ 1 := Real.rpow_le_one ha0.le ha1.le hq0.le
  have hb : 1 - a ≤ (1 - a) ^ q := by
    have := Real.rpow_le_rpow_of_exponent_ge (show 0 < 1 - a by linarith) (show 1 - a ≤ 1 by linarith)
      hq.le
    simpa using this
  set x : ℝ := a * K - a with hx
  have hx0 : 0 < x := by rw [hx]; nlinarith
  have hx1 : x ≤ 1 := by rw [hx]; rw [haq] at haq1; linarith
  have hS : 1 + x ≤ a ^ q + (1 - a) ^ q := by rw [haq]; rw [hx]; linarith
  have hlog : x / 2 ≤ Real.log (a ^ q + (1 - a) ^ q) := by
    have h1 := Real.one_sub_inv_le_log_of_pos (show 0 < 1 + x by linarith)
    have h2 := Real.log_le_log (show 0 < 1 + x by linarith) hS
    have h3 : x / 2 ≤ 1 - (1 + x)⁻¹ := by
      have : (1 + x)⁻¹ ≤ 1 - x / 2 := by
        rw [inv_eq_one_div, div_le_iff₀ (by linarith)]
        nlinarith
      linarith
    linarith
  refine ⟨a, ha0, ha1, ?_⟩
  rw [renyiSpec_binary_eq_lt hq, lt_div_iff₀ (by positivity)]
  rw [hx, hK] at hlog
  nlinarith [mul_pos ha0 hL, mul_pos ha0 h1q, mul_pos (mul_pos ha0 h1q) (sub_pos.2 hL1),
    mul_pos (mul_pos ha0 ha0) (mul_pos h1q hL)]

/-! ### The order `q = 1` (Shannon) -/

/-- The binary Shannon entropy in bits, `(h(a) + h(1-a))/ln 2` with `h = negMulLog`, exceeds `4a(1-a)`
at `a = 1/32`. (`renyiSpec` is not the Shannon entropy at `q = 1`, so this order is stated separately.) -/
theorem shannon_binary_violation :
    4 * (1 / 32 : ℝ) * (1 - 1 / 32) <
      (Real.negMulLog (1 / 32) + Real.negMulLog (1 - 1 / 32)) / Real.log 2 := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h32 : Real.log (1 / 32 : ℝ) = -(5 * Real.log 2) := by
    rw [one_div, Real.log_inv, show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]; push_cast; ring
  have h1 : Real.negMulLog (1 / 32 : ℝ) = 5 / 32 * Real.log 2 := by
    rw [Real.negMulLog, h32]; ring
  have h2 : 0 ≤ Real.negMulLog (1 - 1 / 32 : ℝ) := Real.negMulLog_nonneg (by norm_num) (by norm_num)
  rw [lt_div_iff₀ hL, h1]
  nlinarith [Lg_lt, show Lg = Real.log 2 from rfl]

/-! ### The threshold theorems -/

/-- Padding a binary spectrum with two zeros does not change `H_q`. -/
theorem renyiSpec_pad {q : ℝ} (hq : 0 < q) (a : ℝ) :
    renyiSpec q ![a, 1 - a, 0, 0] = renyiSpec q ![a, 1 - a] := by
  unfold renyiSpec
  simp [Fin.sum_univ_four, Fin.sum_univ_two, Real.zero_rpow hq.ne']

/-- **Threshold of the binary bound** (`lem:fqe-renyi-grouping`, last sentence): for an order `q > 0`,
`q ≠ 1`, the inequality `H_q(a, 1-a) ≤ 4a(1-a)` holds for every `a ∈ [0,1]` iff `q ≥ q_b`. -/
theorem renyi_binary_iff {q : ℝ} (hq0 : 0 < q) (hq1 : q ≠ 1) :
    (∀ a : ℝ, 0 ≤ a → a ≤ 1 → renyiSpec q ![a, 1 - a] ≤ 4 * a * (1 - a)) ↔ qb ≤ q := by
  constructor
  · intro H
    by_contra hlt
    push Not at hlt
    obtain ⟨a, ha0, ha1, hviol⟩ : ∃ a : ℝ, 0 < a ∧ a < 1 ∧ 4 * a * (1 - a) < renyiSpec q ![a, 1 - a] := by
      rcases lt_or_gt_of_ne hq1 with h | h
      · exact binary_violation_lt hq0 h
      · exact binary_violation_gt h hlt
    exact absurd (H a ha0.le ha1.le) (not_le.2 hviol)
  · intro hq a ha0 ha1
    have hl : ∀ i, 0 ≤ (![a, 1 - a] : Fin 2 → ℝ) i := by
      intro i; fin_cases i <;> simp <;> linarith
    have hs : ∑ i, (![a, 1 - a] : Fin 2 → ℝ) i = 1 := by simp [Fin.sum_univ_two]
    exact (renyiSpec_anti one_lt_qb hq hl hs).trans (renyi_binary_bound ha0 ha1)

/-- **Threshold of the cubic bound** (`prop:fqe-cubic-bound`): for an order `q > 0`, `q ≠ 1`, the bound
`H_q(λ) ≤ 10/3 - 6 Σλ² + (8/3) Σλ³` holds for every four-point probability vector iff `q ≥ q_b`. -/
theorem renyi_cubic_iff {q : ℝ} (hq0 : 0 < q) (hq1 : q ≠ 1) :
    (∀ l : Fin 4 → ℝ, (∀ i, 0 ≤ l i) → ∑ i, l i = 1 →
      renyiSpec q l ≤ 10 / 3 - 6 * ∑ i, l i ^ 2 + 8 / 3 * ∑ i, l i ^ 3) ↔ qb ≤ q := by
  constructor
  · intro H
    refine (renyi_binary_iff hq0 hq1).1 fun a ha0 ha1 => ?_
    have hl : ∀ i, 0 ≤ (![a, 1 - a, 0, 0] : Fin 4 → ℝ) i := by
      intro i; fin_cases i <;> simp <;> linarith
    have hs : ∑ i, (![a, 1 - a, 0, 0] : Fin 4 → ℝ) i = 1 := by simp [Fin.sum_univ_four]
    have h := H _ hl hs
    rw [renyiSpec_pad hq0] at h
    simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three] at h
    refine h.trans (le_of_eq ?_)
    simp
    ring
  · intro hq l hl hs
    exact renyi_cubic_bound hq l hl hs

/-- **Equality cases of the binary bound for every `q ≥ q_b`** (`lem:fqe-renyi-grouping`):
`H_q(a, 1-a) = 4a(1-a)` iff `a ∈ {0, 1/2, 1}`. -/
theorem renyi_binary_eq_iff_ge {q : ℝ} (hq : qb ≤ q) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    renyiSpec q ![a, 1 - a] = 4 * a * (1 - a) ↔ a = 0 ∨ a = 1 / 2 ∨ a = 1 := by
  have hq0 : 0 < q := lt_of_lt_of_le qb_pos hq
  have hq1 : q ≠ 1 := (lt_of_lt_of_le one_lt_qb hq).ne'
  have hl : ∀ i, 0 ≤ (![a, 1 - a] : Fin 2 → ℝ) i := by
    intro i; fin_cases i <;> simp <;> linarith
  have hs : ∑ i, (![a, 1 - a] : Fin 2 → ℝ) i = 1 := by simp [Fin.sum_univ_two]
  constructor
  · intro h
    have h1 := renyiSpec_anti one_lt_qb hq hl hs
    have h2 := renyi_binary_bound ha0 ha1
    exact (renyi_binary_eq_iff ha0 ha1).1 (le_antisymm h2 (h ▸ h1))
  · intro h
    rcases h with rfl | rfl | rfl
    · simpa using renyiSpec_pure_pair hq0
    · have := (renyiSpec_eq_iff hq0 hq1 (l := (![1 / 2, 1 - 1 / 2] : Fin 2 → ℝ))
        (by intro i; fin_cases i <;> simp <;> norm_num) (by simp [Fin.sum_univ_two])).2
        (by intro i; fin_cases i <;> simp <;> norm_num)
      rw [this]; norm_num
    · simpa using renyiSpec_pure_pair' hq0

/-- info: 'FormalResearch.FourQubitEntropy.PaperECritical.renyi_binary_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms renyi_binary_iff

/-- info: 'FormalResearch.FourQubitEntropy.PaperECritical.renyi_cubic_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms renyi_cubic_iff

/-- info: 'FormalResearch.FourQubitEntropy.PaperECritical.renyi_binary_eq_iff_ge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms renyi_binary_eq_iff_ge

/-- info: 'FormalResearch.FourQubitEntropy.PaperECritical.shannon_binary_violation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms shannon_binary_violation

/-- info: 'FormalResearch.FourQubitEntropy.PaperECritical.qb_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms qb_bounds

end FormalResearch.FourQubitEntropy.PaperECritical
