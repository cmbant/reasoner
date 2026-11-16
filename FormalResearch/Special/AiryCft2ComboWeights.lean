module

public import FormalResearch.Special.AiryCft2ComboZeros

/-!
# Weights `D/N'²` of the Clark summation and absolute convergence

Continuation of `AiryCft2ComboZeros` (`N = P Ai + Q Ai'`, `Q ≠ 0`).  At a zero `t` of `N`, `N'(t) M(t) = -D(t)/π`
(`airyNC_mul_airyMC_at_zero`), so the weight `D(t)/N'(t)²` equals `-π M(t)/N'(t)` (`airyNC_weight_eq`) and, since `N(t) = 0`,
`M(t) = (M - iN)(t)`:

* `airyNC_weight_norm_le`: for a real zero `t ≤ -1`,
  `‖D(t)/N'(t)²‖ ≤ 8π² (3|P|+5|Q|)² Q^{-2} (1 + |t|)^{-1/2}`;
  proof: `‖D/N'²‖ = π² ‖M(t)‖²/D(t)`, `‖M(t)‖² ≤ 4(3|P|+5|Q|)²(1+|t|)^{1/2}` (`airyMC_sub_I_mul_sq_le` at the real point
  `t`, where `e(t) = 1`) and `D(t) = P² - tQ² ≥ Q²|t|`.
* `airyNC_summable_weighted`: if `‖f(u)‖ ≤ C (1+|u|)^ν e(u)` with `ν < -1` then `Σ_{N(z)=0} f(z) D(z)/N'(z)²` is absolutely
  summable (over the subtype of zeros of `N`): the zeros inject into `ℕ` by `airyNIdx` with `|t| ≥ 2.5 n^{2/3}`, so the
  terms are `O(n^{(2/3)(ν - 1/2)})`, exponent `< -1` (as in `airy_summable_weighted` for `Ai`).

This is the analogue of `GENERAL_THEOREMS.md` Theorem 1.1 (iv) / Lemma 1.0′(d), *without* the Carleson-disc argument: the
weight bound follows from the numerator bound `‖M - iN‖` alone.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

/-- At a zero `t` of `N` with `N'(t) ≠ 0`: `-π M(t)/N'(t) = D(t)/N'(t)²`. -/
lemma airyNC_weight_eq (P Q : ℝ) {t : ℂ} (h : airyNC P Q t = 0) (hd : airyNC' P Q t ≠ 0) :
    -((π : ℂ) * (airyMC P Q t / airyNC' P Q t)) = airyDC P Q t / airyNC' P Q t ^ 2 := by
  have h1 := airyNC_mul_airyMC_at_zero h
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have e : ((1 / π : ℝ) : ℂ) = 1 / (π : ℂ) := by push_cast; ring
  rw [e] at h1
  field_simp
  field_simp at h1
  linear_combination -h1

/-- **Weight bound.** For a real zero `t ≤ -1` of `N`:
`‖D(t)/N'(t)²‖ ≤ 8π² (3|P|+5|Q|)² Q^{-2} (1+|t|)^{-1/2}`. -/
theorem airyNC_weight_norm_le (P Q : ℝ) (hQ : Q ≠ 0) {t : ℝ} (h : airyNC P Q (t : ℂ) = 0) (ht : t ≤ -1) :
    ‖airyDC P Q (t : ℂ) / airyNC' P Q (t : ℂ) ^ 2‖ ≤
      8 * π ^ 2 * (3 * |P| + 5 * |Q|) ^ 2 / Q ^ 2 * (1 + |t|) ^ (-(1 / 2) : ℝ) := by
  obtain ⟨hD, hd⟩ := airyNC_zero_weight_pos P Q hQ h
  have hw := airyNC_weight_eq P Q h hd
  have hM : airyMC P Q (t : ℂ) = airyMC P Q (t : ℂ) - I * airyNC P Q (t : ℂ) := by rw [h]; ring
  have hnum := airyMC_sub_I_mul_sq_le P Q (u := (t : ℂ)) (by simp)
  rw [← hM, airyEnv_ofReal_neg (by linarith), mul_one, Complex.norm_real, Real.norm_eq_abs] at hnum
  set K := 3 * |P| + 5 * |Q| with hK
  have hDn : airyDC P Q (t : ℂ) = ((P ^ 2 - t * Q ^ 2 : ℝ) : ℂ) := by
    unfold airyDC; push_cast; ring
  have hQ2 : 0 < Q ^ 2 := by positivity
  have hnt : 0 < ‖airyNC' P Q (t : ℂ)‖ := norm_pos_iff.mpr hd
  -- ‖D/N'^2‖ = D π² ‖M‖² / D²  ... use  ‖N'‖ ‖M‖ = D/π
  have hprod : ‖airyNC' P Q (t : ℂ)‖ * ‖airyMC P Q (t : ℂ)‖ = (P ^ 2 - t * Q ^ 2) / π := by
    have h1 := airyNC_mul_airyMC_at_zero h
    have := congrArg norm h1
    rw [norm_mul, norm_neg, norm_mul, hDn, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hD, abs_of_pos (by positivity : (0 : ℝ) < 1 / π)] at this
    rw [this]; field_simp
  rw [hDn, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD]
  set Dv := P ^ 2 - t * Q ^ 2 with hDv
  set a := ‖airyNC' P Q (t : ℂ)‖ with ha
  set m := ‖airyMC P Q (t : ℂ)‖ with hm
  have hm0 : 0 ≤ m := norm_nonneg _
  have hpi := Real.pi_pos
  have hmpos : 0 < m := by
    rcases hm0.lt_or_eq with h1 | h1
    · exact h1
    · rw [← h1, mul_zero] at hprod
      have : 0 < Dv / π := by positivity
      linarith
  -- Dv / a^2 = π² m² / Dv
  have e1 : Dv / a ^ 2 = π ^ 2 * m ^ 2 / Dv := by
    have ha' : a = Dv / (π * m) := by
      have hpm : π * m ≠ 0 := by positivity
      rw [eq_div_iff hpm]
      calc a * (π * m) = (a * m) * π := by ring
        _ = Dv / π * π := by rw [hprod]
        _ = Dv := by field_simp
    rw [ha']
    field_simp
  rw [e1]
  have hDq : Q ^ 2 * (-t) ≤ Dv := by rw [hDv]; nlinarith [sq_nonneg P]
  have hab : |t| = -t := abs_of_neg (by linarith)
  have hm2 : m ^ 2 ≤ 4 * K ^ 2 * (1 + |t|) ^ (1 / 2 : ℝ) := by
    have := hnum
    simpa using this
  have hp : (1 + |t|) ^ (1 / 2 : ℝ) ≤ 2 * |t| * (1 + |t|) ^ (-(1 / 2) : ℝ) := by
    have h1 : (1 + |t|) ^ (1 / 2 : ℝ) = (1 + |t|) * (1 + |t|) ^ (-(1 / 2) : ℝ) := by
      rw [← Real.rpow_one_add' (by positivity) (by norm_num)]; norm_num
    rw [h1]
    have : 0 < (1 + |t|) ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos (by positivity) _
    have : 1 + |t| ≤ 2 * |t| := by rw [hab]; linarith
    nlinarith
  have hDpos : 0 < Dv := hD
  rw [div_le_iff₀ hDpos]
  have hq : 0 < (1 + |t|) ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  have h3 : π ^ 2 * m ^ 2 ≤ π ^ 2 * (4 * K ^ 2 * (2 * |t| * (1 + |t|) ^ (-(1 / 2) : ℝ))) := by
    refine mul_le_mul_of_nonneg_left (hm2.trans ?_) (by positivity)
    have := mul_le_mul_of_nonneg_left hp (by positivity : (0 : ℝ) ≤ 4 * K ^ 2)
    linarith
  have h4 : 8 * π ^ 2 * K ^ 2 / Q ^ 2 * (1 + |t|) ^ (-(1 / 2) : ℝ) * Dv ≥
      8 * π ^ 2 * K ^ 2 / Q ^ 2 * (1 + |t|) ^ (-(1 / 2) : ℝ) * (Q ^ 2 * (-t)) := by
    gcongr
  have h5 : 8 * π ^ 2 * K ^ 2 / Q ^ 2 * (1 + |t|) ^ (-(1 / 2) : ℝ) * (Q ^ 2 * (-t)) =
      π ^ 2 * (4 * K ^ 2 * (2 * |t| * (1 + |t|) ^ (-(1 / 2) : ℝ))) := by
    rw [hab]; field_simp; ring
  linarith

/-- **Absolute convergence of the Clark-type series**: if `‖f(u)‖ ≤ C (1+|u|)^ν e(u)` with `ν < -1`, then
`Σ_{N(z)=0} f(z) D(z)/N'(z)²` is absolutely summable over the zero set of `N`. -/
theorem airyNC_summable_weighted (P Q : ℝ) (hQ : Q ≠ 0) {f : ℂ → ℂ} {C ν : ℝ} (hC : 0 ≤ C) (hν : ν < -1)
    (hb : ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u) :
    Summable (fun z : {z : ℂ // airyNC P Q z = 0} =>
      f z * (airyDC P Q z / airyNC' P Q z ^ 2)) := by
  set q : ℝ := ν - 1 / 2 with hq
  have hq0 : q < 0 := by rw [hq]; linarith
  set cw : ℝ := 8 * π ^ 2 * (3 * |P| + 5 * |Q|) ^ 2 / Q ^ 2 with hcw
  have hcw0 : 0 ≤ cw := by positivity
  have hg : Summable (fun k : ℕ => (k : ℝ) ^ (2 / 3 * q)) :=
    Real.summable_nat_rpow.mpr (by rw [hq]; linarith)
  set ψ : {z : ℂ // airyNC P Q z = 0} → ℕ := fun z => airyNIdx z.1.re with hψ
  have hinj : Function.Injective ψ := by
    intro z₁ z₂ h12
    have i1 := airyNC_zero_im P Q hQ z₁.2
    have i2 := airyNC_zero_im P Q hQ z₂.2
    have e1 : z₁.1 = (z₁.1.re : ℂ) := Complex.ext (by simp) (by simp [i1])
    have e2 : z₂.1 = (z₂.1.re : ℂ) := Complex.ext (by simp) (by simp [i2])
    have h1 : airyNC P Q (z₁.1.re : ℂ) = 0 := by rw [← e1]; exact z₁.2
    have h2 : airyNC P Q (z₂.1.re : ℂ) = 0 := by rw [← e2]; exact z₂.2
    have := airyNIdx_injOn P Q hQ h1 h2 h12
    exact Subtype.ext (by rw [e1, e2, this])
  have hgs : Summable (fun z : {z : ℂ // airyNC P Q z = 0} => (C * cw * 2.5 ^ q) * (ψ z : ℝ) ^ (2 / 3 * q)) :=
    (hg.mul_left (C * cw * 2.5 ^ q)).comp_injective hinj
  refine Summable.of_norm_bounded_eventually hgs ?_
  rw [Filter.eventually_cofinite]
  refine (Set.Finite.preimage (f := ψ) (s := {n : ℕ | n < 3}) hinj.injOn (Set.finite_lt_nat 3)).subset ?_
  intro z hz
  by_contra hmem
  apply hz
  have h3 : 3 ≤ ψ z := by
    have : ¬ ψ z < 3 := hmem
    omega
  have i1 := airyNC_zero_im P Q hQ z.2
  have e1 : z.1 = (z.1.re : ℂ) := Complex.ext (by simp) (by simp [i1])
  have hz0 : airyNC P Q (z.1.re : ℂ) = 0 := by rw [← e1]; exact z.2
  set t := z.1.re with ht
  have h3t : 3 ≤ airyNIdx t := h3
  have hb2 := airyNIdx_abs_ge P Q hQ hz0 (by omega)
  have hψt : ψ z = airyNIdx t := rfl
  rw [← hψt] at hb2
  have hk : (3 : ℝ) ≤ (ψ z : ℝ) := by exact_mod_cast h3
  have hk0 : (0 : ℝ) < (ψ z : ℝ) := by linarith
  have hk23 : 1 ≤ (ψ z : ℝ) ^ (2 / 3 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have htle : t ≤ -1 := by norm_num at hb2; linarith
  have hw := airyNC_weight_norm_le P Q hQ hz0 htle
  have hbt := hb (t : ℂ)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith), airyEnv_ofReal_neg (by linarith),
    mul_one] at hbt
  have hz' : z.1 = (t : ℂ) := e1
  show ‖f z.1 * (airyDC P Q z.1 / airyNC' P Q z.1 ^ 2)‖ ≤ _
  rw [hz', norm_mul]
  have hpos : 0 < 1 + -t := by linarith
  have e2 : (1 + -t) ^ ν * (1 + -t) ^ (-(1 / 2) : ℝ) = (1 + -t) ^ q := by
    rw [hq, ← Real.rpow_add hpos]; ring_nf
  have hab : |t| = -t := abs_of_neg (by linarith)
  rw [hab] at hw
  have hpow : (1 + -t) ^ q ≤ (2.5 * (ψ z : ℝ) ^ (2 / 3 : ℝ)) ^ q := by
    refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ hq0.le
    linarith
  have hpow2 : (2.5 * (ψ z : ℝ) ^ (2 / 3 : ℝ)) ^ q = 2.5 ^ q * (ψ z : ℝ) ^ (2 / 3 * q) := by
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hk0.le]
  calc ‖f (t : ℂ)‖ * ‖airyDC P Q (t : ℂ) / airyNC' P Q (t : ℂ) ^ 2‖
      ≤ (C * (1 + -t) ^ ν) * (cw * (1 + -t) ^ (-(1 / 2) : ℝ)) := by gcongr
    _ = C * cw * (1 + -t) ^ q := by rw [← e2]; ring
    _ ≤ C * cw * (2.5 ^ q * (ψ z : ℝ) ^ (2 / 3 * q)) := by rw [← hpow2]; gcongr
    _ = _ := by ring

/-- info: 'FormalResearch.Special.airyNC_weight_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyNC_weight_norm_le

/-- info: 'FormalResearch.Special.airyNC_summable_weighted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyNC_summable_weighted

end FormalResearch.Special
