module

public import FormalResearch.Special.AiryParametrixUniformODE

/-!
# Second-order Airy parametrix, part 1: the `h²` coefficients of the shift functions

The shift functions `C(s; ζ, h)`, `S(s; ζ, h)` (`Y_ss = (ζ + h s) Y`, data `(1,0)`, `(0,1)`) have at fixed `ζ` the
expansions (`c_k := Ch^{(k)}(w)`, `w = ζ s²`; `AiryParametrixUniformCh` has the `h⁰`, `h¹` coefficients)

* `C = E + h O + h² C₂ + O(h³)`, `C₂ = s⁶ (c₂/8 - 7 c₃/12)`,
* `S = A + h B + h² S₂ + O(h³)`, `S₂ = s⁷ (c₃/4 - c₄/6)`.

This module proves (i) the general confluent equation `Ch^{(n)} = (4n+2) Ch^{(n+1)} + 4 w Ch^{(n+2)}` (`apu2_ode`), (ii) the
closed forms `apuC2`, `apuS2` and their `s`-derivatives with the second-order identities
`C₂'' = ζ C₂ + s O`, `S₂'' = ζ S₂ + s B` (so that `R = C - (E + hO + h²C₂)` solves `R'' = (ζ + h s) R + h³ s C₂`), parity and
initial data, and (iii) compact-uniform bounds.  The closed forms were found by sympy (ansatz `s^m Σ p_j(w) Ch^{(j)}(w)`, the
operator `L_m F = 4w²F'' + (4m+2) w F' + (m(m-1) - w) F` on `Y = s^m F(ζ s²)`) and checked against the exact `C`, `S`
(`mpmath` ODE integration, error `/h³` between `1e-5` and `1.5e-4` for `ζ ∈ {1.3,-2}`, `s ∈ {0.8, 1.1}`, `h ∈ {1e-2, 1e-3}`;
`/home/user/scratch/r13_numerics/num2.py`).

**Claim class: proved.**
-/

@[expose] public section

open Set

namespace FormalResearch.Special

/-- **General confluent equation** `Ch^{(n)} = (4n+2) Ch^{(n+1)} + 4 w Ch^{(n+2)}` (the `n`-th derivative of
`Ch = 4 w Ch'' + 2 Ch'`). -/
lemma apu2_ode : ∀ (n : ℕ) (w : ℝ),
    apuc n w = (4 * (n : ℝ) + 2) * apuc (n + 1) w + 4 * w * apuc (n + 2) w
  | 0, w => by have := apuc_ode0 w; simp; linarith
  | n + 1, w => by
      have hf : ∀ x, HasDerivAt (apuc (n + 1)) (apuc (n + 2) x) x := apuc_hasDerivAt (n + 1)
      have hg : ∀ x, HasDerivAt (fun w => (4 * (n : ℝ) + 2) * apuc (n + 1) w + 4 * w * apuc (n + 2) w)
          ((4 * (n : ℝ) + 2) * apuc (n + 2) x + (4 * apuc (n + 2) x + 4 * x * apuc (n + 3) x)) x := by
        intro x
        have := ((apuc_hasDerivAt (n + 1) x).const_mul (4 * (n : ℝ) + 2)).add
          (((hasDerivAt_id x).const_mul 4).mul (apuc_hasDerivAt (n + 2) x))
        refine this.congr_deriv ?_
        simp
      have hfg : apuc n = fun w => (4 * (n : ℝ) + 2) * apuc (n + 1) w + 4 * w * apuc (n + 2) w :=
        funext (apu2_ode n)
      have hf0 : ∀ x, HasDerivAt (apuc n) (apuc (n + 1) x) x := apuc_hasDerivAt n
      have h := (hf0 w).unique (hfg ▸ hg w)
      push_cast
      linarith

lemma apu2_ode3 (w : ℝ) : apuc 3 w = 14 * apuc 4 w + 4 * w * apuc 5 w := by
  have := apu2_ode 3 w; norm_num at this; linarith

lemma apu2_ode4 (w : ℝ) : apuc 4 w = 18 * apuc 5 w + 4 * w * apuc 6 w := by
  have := apu2_ode 4 w; norm_num at this; linarith

/-! ### The closed forms -/

/-- `C₂(ζ,s) = s⁶ (Ch''/8 - 7 Ch'''/12)(ζ s²)`: the `h²` coefficient of `C`. -/
noncomputable def apuC2 (z s : ℝ) : ℝ :=
  s ^ 6 * (apuc 2 (z * s ^ 2) / 8 - 7 * apuc 3 (z * s ^ 2) / 12)
/-- `∂_s C₂`. -/
noncomputable def apuC21 (z s : ℝ) : ℝ :=
  6 * s ^ 5 * (apuc 2 (z * s ^ 2) / 8 - 7 * apuc 3 (z * s ^ 2) / 12) +
    2 * z * s ^ 7 * (apuc 3 (z * s ^ 2) / 8 - 7 * apuc 4 (z * s ^ 2) / 12)
/-- `S₂(ζ,s) = s⁷ (Ch'''/4 - Ch''''/6)(ζ s²)`: the `h²` coefficient of `S`. -/
noncomputable def apuS2 (z s : ℝ) : ℝ :=
  s ^ 7 * (apuc 3 (z * s ^ 2) / 4 - apuc 4 (z * s ^ 2) / 6)
/-- `∂_s S₂`. -/
noncomputable def apuS21 (z s : ℝ) : ℝ :=
  7 * s ^ 6 * (apuc 3 (z * s ^ 2) / 4 - apuc 4 (z * s ^ 2) / 6) +
    2 * z * s ^ 8 * (apuc 4 (z * s ^ 2) / 4 - apuc 5 (z * s ^ 2) / 6)

lemma apu2_hasDerivAt_C2 (z s : ℝ) : HasDerivAt (apuC2 z) (apuC21 z s) s := by
  have := (hasDerivAt_pow 6 s).mul (((apu_hd 2 z s).div_const 8).sub (((apu_hd 3 z s).const_mul 7).div_const 12))
  unfold apuC2 apuC21
  refine this.congr_deriv ?_
  simp; ring

/-- `∂_s² C₂ = ζ C₂ + s O`. -/
lemma apu2_hasDerivAt_C21 (z s : ℝ) : HasDerivAt (apuC21 z) (z * apuC2 z s + s * apuO z s) s := by
  have h1 := ((hasDerivAt_pow 5 s).const_mul 6).mul
    (((apu_hd 2 z s).div_const 8).sub (((apu_hd 3 z s).const_mul 7).div_const 12))
  have h2 := ((hasDerivAt_pow 7 s).const_mul (2 * z)).mul
    (((apu_hd 3 z s).div_const 8).sub (((apu_hd 4 z s).const_mul 7).div_const 12))
  have := h1.add h2
  have o1 := apuc_ode1 (z * s ^ 2)
  have o2 := apuc_ode2 (z * s ^ 2)
  have o3 := apu2_ode3 (z * s ^ 2)
  unfold apuC21 apuC2 apuO
  refine this.congr_deriv ?_
  simp only [Pi.sub_apply, Nat.cast_ofNat, Nat.reduceAdd, Nat.reduceSub]
  rw [o1, o2, o3]; ring

lemma apu2_hasDerivAt_S2 (z s : ℝ) : HasDerivAt (apuS2 z) (apuS21 z s) s := by
  have := (hasDerivAt_pow 7 s).mul (((apu_hd 3 z s).div_const 4).sub ((apu_hd 4 z s).div_const 6))
  unfold apuS2 apuS21
  refine this.congr_deriv ?_
  simp; ring

/-- `∂_s² S₂ = ζ S₂ + s B`. -/
lemma apu2_hasDerivAt_S21 (z s : ℝ) : HasDerivAt (apuS21 z) (z * apuS2 z s + s * apuB z s) s := by
  have h1 := ((hasDerivAt_pow 6 s).const_mul 7).mul
    (((apu_hd 3 z s).div_const 4).sub ((apu_hd 4 z s).div_const 6))
  have h2 := ((hasDerivAt_pow 8 s).const_mul (2 * z)).mul
    (((apu_hd 4 z s).div_const 4).sub ((apu_hd 5 z s).div_const 6))
  have := h1.add h2
  have o2 := apuc_ode2 (z * s ^ 2)
  have o3 := apu2_ode3 (z * s ^ 2)
  have o4 := apu2_ode4 (z * s ^ 2)
  unfold apuS21 apuS2 apuB
  refine this.congr_deriv ?_
  simp only [Pi.sub_apply, Nat.cast_ofNat, Nat.reduceAdd, Nat.reduceSub]
  rw [o2, o3, o4]; ring

/-! ### Parity and initial data -/

lemma apuC2_neg (z s : ℝ) : apuC2 z (-s) = apuC2 z s := by unfold apuC2; rw [neg_sq]; ring
lemma apuS2_neg (z s : ℝ) : apuS2 z (-s) = -apuS2 z s := by unfold apuS2; rw [neg_sq]; ring
lemma apuC2_zero (z : ℝ) : apuC2 z 0 = 0 := by unfold apuC2; simp
lemma apuC21_zero (z : ℝ) : apuC21 z 0 = 0 := by unfold apuC21; simp
lemma apuS2_zero (z : ℝ) : apuS2 z 0 = 0 := by unfold apuS2; simp
lemma apuS21_zero (z : ℝ) : apuS21 z 0 = 0 := by unfold apuS21; simp

/-! ### Compact-uniform bounds -/

/-- `Ch^{(k)}` for `k ≤ 6` are bounded on `|w| ≤ W`. -/
lemma apu2_cbound (W : ℝ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ w : ℝ, |w| ≤ W → ∀ k : ℕ, k ≤ 6 → |apuc k w| ≤ M := by
  have hc : IsCompact (Icc (-|W|) |W|) := isCompact_Icc
  have hcont : Continuous fun w => ∑ k ∈ Finset.range 7, |apuc k w| :=
    continuous_finsetSum _ fun k _ => (apuc_continuous k).abs
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨|C|, abs_nonneg _, fun w hw k hk => ?_⟩
  have hw' : w ∈ Icc (-|W|) |W| :=
    ⟨by linarith [neg_abs_le w, le_abs_self W], by linarith [le_abs_self w, le_abs_self W]⟩
  have h1 := hC w hw'
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun k _ => abs_nonneg _)] at h1
  have h2 : |apuc k w| ≤ ∑ k ∈ Finset.range 7, |apuc k w| :=
    Finset.single_le_sum (f := fun k => |apuc k w|) (fun k _ => abs_nonneg _) (Finset.mem_range.2 (by omega))
  exact h2.trans (h1.trans (le_abs_self C))

/-- **Uniform bounds** for `C₂, ∂C₂, S₂, ∂S₂` on `|ζ| ≤ Z₀`, `|s| ≤ S`. -/
lemma apu2_bounds (Z0 S : ℝ) (hZ0 : 0 ≤ Z0) (hS : 0 ≤ S) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z s : ℝ, |z| ≤ Z0 → |s| ≤ S →
      |apuC2 z s| ≤ M ∧ |apuC21 z s| ≤ M ∧ |apuS2 z s| ≤ M ∧ |apuS21 z s| ≤ M := by
  obtain ⟨Mc, hMc0, hMc⟩ := apu2_cbound (Z0 * S ^ 2)
  refine ⟨S ^ 6 * (2 * Mc) + (6 * S ^ 5 * (2 * Mc) + 2 * Z0 * S ^ 7 * (2 * Mc)) + S ^ 7 * (2 * Mc) +
    (7 * S ^ 6 * (2 * Mc) + 2 * Z0 * S ^ 8 * (2 * Mc)), by positivity, fun z s hz hs => ?_⟩
  have hw : |z * s ^ 2| ≤ Z0 * S ^ 2 := by
    rw [abs_mul, abs_pow]; exact mul_le_mul hz (pow_le_pow_left₀ (abs_nonneg _) hs 2) (by positivity) hZ0
  have b := fun k (hk : k ≤ 6) => hMc _ hw k hk
  have b2 := b 2 (by norm_num)
  have b3 := b 3 (by norm_num)
  have b4 := b 4 (by norm_num)
  have b5 := b 5 (by norm_num)
  have q23 : |apuc 2 (z * s ^ 2) / 8 - 7 * apuc 3 (z * s ^ 2) / 12| ≤ 2 * Mc := by
    have h1 := abs_sub (apuc 2 (z * s ^ 2) / 8) (7 * apuc 3 (z * s ^ 2) / 12)
    have e1 : |apuc 2 (z * s ^ 2) / 8| = |apuc 2 (z * s ^ 2)| / 8 := by rw [abs_div]; norm_num
    have e2 : |7 * apuc 3 (z * s ^ 2) / 12| = 7 * |apuc 3 (z * s ^ 2)| / 12 := by
      rw [abs_div, abs_mul]; norm_num
    rw [e1, e2] at h1; linarith
  have q34 : |apuc 3 (z * s ^ 2) / 8 - 7 * apuc 4 (z * s ^ 2) / 12| ≤ 2 * Mc := by
    have h1 := abs_sub (apuc 3 (z * s ^ 2) / 8) (7 * apuc 4 (z * s ^ 2) / 12)
    have e1 : |apuc 3 (z * s ^ 2) / 8| = |apuc 3 (z * s ^ 2)| / 8 := by rw [abs_div]; norm_num
    have e2 : |7 * apuc 4 (z * s ^ 2) / 12| = 7 * |apuc 4 (z * s ^ 2)| / 12 := by
      rw [abs_div, abs_mul]; norm_num
    rw [e1, e2] at h1; linarith
  have r34 : |apuc 3 (z * s ^ 2) / 4 - apuc 4 (z * s ^ 2) / 6| ≤ 2 * Mc := by
    have h1 := abs_sub (apuc 3 (z * s ^ 2) / 4) (apuc 4 (z * s ^ 2) / 6)
    have e1 : |apuc 3 (z * s ^ 2) / 4| = |apuc 3 (z * s ^ 2)| / 4 := by rw [abs_div]; norm_num
    have e2 : |apuc 4 (z * s ^ 2) / 6| = |apuc 4 (z * s ^ 2)| / 6 := by rw [abs_div]; norm_num
    rw [e1, e2] at h1; linarith
  have r45 : |apuc 4 (z * s ^ 2) / 4 - apuc 5 (z * s ^ 2) / 6| ≤ 2 * Mc := by
    have h1 := abs_sub (apuc 4 (z * s ^ 2) / 4) (apuc 5 (z * s ^ 2) / 6)
    have e1 : |apuc 4 (z * s ^ 2) / 4| = |apuc 4 (z * s ^ 2)| / 4 := by rw [abs_div]; norm_num
    have e2 : |apuc 5 (z * s ^ 2) / 6| = |apuc 5 (z * s ^ 2)| / 6 := by rw [abs_div]; norm_num
    rw [e1, e2] at h1; linarith
  have hz0 := abs_nonneg z
  have hs0 := abs_nonneg s
  have eC2 : |apuC2 z s| ≤ S ^ 6 * (2 * Mc) := by
    unfold apuC2; rw [abs_mul, abs_pow]; gcongr
  have eC21 : |apuC21 z s| ≤ 6 * S ^ 5 * (2 * Mc) + 2 * Z0 * S ^ 7 * (2 * Mc) := by
    unfold apuC21
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_mul, abs_pow, abs_of_pos (by norm_num : (0:ℝ) < 6)]; gcongr
    · rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_two]; gcongr
  have eS2 : |apuS2 z s| ≤ S ^ 7 * (2 * Mc) := by
    unfold apuS2; rw [abs_mul, abs_pow]; gcongr
  have eS21 : |apuS21 z s| ≤ 7 * S ^ 6 * (2 * Mc) + 2 * Z0 * S ^ 8 * (2 * Mc) := by
    unfold apuS21
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_mul, abs_pow, abs_of_pos (by norm_num : (0:ℝ) < 7)]; gcongr
    · rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_two]; gcongr
  have t1 : 0 ≤ S ^ 6 * (2 * Mc) := by positivity
  have t2 : 0 ≤ 6 * S ^ 5 * (2 * Mc) + 2 * Z0 * S ^ 7 * (2 * Mc) := by positivity
  have t3 : 0 ≤ S ^ 7 * (2 * Mc) := by positivity
  have t4 : 0 ≤ 7 * S ^ 6 * (2 * Mc) + 2 * Z0 * S ^ 8 * (2 * Mc) := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- info: 'FormalResearch.Special.apu2_ode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.apu2_ode

/-- info: 'FormalResearch.Special.apu2_hasDerivAt_C21' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.apu2_hasDerivAt_C21

/-- info: 'FormalResearch.Special.apu2_hasDerivAt_S21' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.apu2_hasDerivAt_S21

/-- info: 'FormalResearch.Special.apu2_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.apu2_bounds

end FormalResearch.Special
