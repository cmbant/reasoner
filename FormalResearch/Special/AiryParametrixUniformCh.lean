module

public import FormalResearch.Special.AiryParametrixTaylor

/-!
# Uniform parametrix defect, part 1: the differential equation of `Ch` and the closed forms

`Ch = langerCosh` (`= cosh √w` for `w ≥ 0`, `cos √(-w)` for `w ≤ 0`) satisfies the confluent equation
`4 w Ch''(w) + 2 Ch'(w) = Ch(w)` (`apuc_ode0`), hence `E(ζ, s) := Ch(ζ s²)` solves `E'' = ζ E` in `s`
(`E = cosh(√ζ s)`).  The `h`-expansion at *fixed* `ζ` of the solutions of `Y'' = (ζ + h s) Y` (the paper's
`C(s; ζ, h)`, `S(s; ζ, h)`, `A:1068-1104`) has the closed-form coefficients (`c_k = Ch^{(k)}(ζ s²)`)

* `C = E + h O + O(h²)`, `E = c₀`, `O = s³ (c₁/2 - c₂)`  (`O'' = ζ O + s E`, `O(0) = O'(0) = 0`);
* `S = A + h B + O(h²)`, `A = 2 s c₁`, `B = s⁴ c₂`  (`A' = E`, `A'' = ζ A`, `B'' = ζ B + s A`, `B(0) = B'(0) = 0`).

This file proves the ODE of `Ch` (and its first two derivatives), these four second-order identities with
their `s`-derivatives, parities, initial data and compact-uniform bounds.  Verified symbolically
(`sympy`, `ζ, s > 0`) and numerically (`mpmath`, 80 digits: exact `C, S` of the Airy shift identity against
`E + hO`, `A + hB` has error `/h²` between `1.7e-3` and `7.1e-3` for `ζ ∈ {-2,-0.5,0.3,2}`,
`s ∈ {-1,-0.4,0.3,1}`, `h ∈ {1e-2, 1e-4, 1e-6}`).  All proved; the constants are existential.
-/

@[expose] public section

open Set
open scoped ContDiff

namespace FormalResearch.Special

/-- `apuc k = Ch^{(k)}`. -/
noncomputable abbrev apuc (k : ℕ) : ℝ → ℝ := deriv^[k] langerCosh

lemma apuc_contDiff : ∀ n : ℕ, ContDiff ℝ ∞ (apuc n)
  | 0 => contDiff_langerCosh
  | n + 1 => by
      have h := (contDiff_infty_iff_deriv.1 (apuc_contDiff n)).2
      have e : apuc (n + 1) = deriv (apuc n) := by
        funext x; exact Function.iterate_succ_apply' deriv n langerCosh ▸ rfl
      rw [e]; exact h

lemma apuc_succ (k : ℕ) (w : ℝ) : apuc (k + 1) w = deriv (apuc k) w := by
  have := Function.iterate_succ_apply' deriv k langerCosh
  exact congrFun this w

lemma apuc_hasDerivAt (k : ℕ) (w : ℝ) : HasDerivAt (apuc k) (apuc (k + 1) w) w := by
  have hd : DifferentiableAt ℝ (apuc k) w :=
    ((apuc_contDiff k).differentiable (by simp)).differentiableAt
  rw [apuc_succ]; exact hd.hasDerivAt

lemma apuc_continuous (k : ℕ) : Continuous (apuc k) := (apuc_contDiff k).continuous

lemma apuc_zero_eq (w : ℝ) : apuc 0 w = langerCosh w := rfl

lemma apuc_zero_at : apuc 0 0 = 1 := by
  have h := langerCosh_nonneg (le_refl (0 : ℝ))
  simp [apuc, h]

lemma apuc_one_at : apuc 1 0 = 1 / 2 := by
  have := deriv_langerP_zero
  rw [deriv_langerP] at this
  exact this

/-- If two functions agree, so do their second derivatives. -/
lemma apu_deriv2_eq {f g f1 f2 g1 g2 : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f1 x) x)
    (hf1 : ∀ x, HasDerivAt f1 (f2 x) x) (hg : ∀ x, HasDerivAt g (g1 x) x)
    (hg1 : ∀ x, HasDerivAt g1 (g2 x) x) (hfg : f = g) : ∀ x, f2 x = g2 x := by
  subst hfg
  have h1 : f1 = g1 := funext fun x => (hf x).unique (hg x)
  subst h1
  exact fun x => (hf1 x).unique (hg1 x)

lemma apu_hd (k : ℕ) (z s : ℝ) :
    HasDerivAt (fun s => apuc k (z * s ^ 2)) (apuc (k + 1) (z * s ^ 2) * (2 * z * s)) s := by
  have hw : HasDerivAt (fun s : ℝ => z * s ^ 2) (z * (2 * s)) s := by
    simpa using (hasDerivAt_pow 2 s).const_mul z
  have := (apuc_hasDerivAt k (z * s ^ 2)).comp s hw
  refine this.congr_deriv ?_
  ring

/-- **The confluent equation** `4 w Ch'' + 2 Ch' = Ch` for `w ≠ 0`, from `E(s) = Ch(w s²) = cosh(√w s)`
(resp. `cos(√(-w) s)`) satisfying `E'' = w E`. -/
lemma apuc_ode0_ne {w : ℝ} (hw : w ≠ 0) : apuc 0 w = 4 * w * apuc 2 w + 2 * apuc 1 w := by
  -- `E(s) = Ch(w s²)`; second derivative at `s = 1`
  have hE1 : ∀ s, HasDerivAt (fun s => apuc 0 (w * s ^ 2)) (apuc 1 (w * s ^ 2) * (2 * w * s)) s :=
    fun s => apu_hd 0 w s
  have hE2 : ∀ s, HasDerivAt (fun s => apuc 1 (w * s ^ 2) * (2 * w * s))
      (apuc 2 (w * s ^ 2) * (2 * w * s) * (2 * w * s) + apuc 1 (w * s ^ 2) * (2 * w)) s := by
    intro s
    have := (apu_hd 1 w s).mul ((hasDerivAt_id s).const_mul (2 * w))
    refine this.congr_deriv ?_
    simp
  rcases lt_or_gt_of_ne hw with hneg | hpos
  · -- `w < 0`: `E = cos(k s)`, `k = √(-w)`
    set k : ℝ := √(-w) with hk
    have hk2 : k ^ 2 = -w := Real.sq_sqrt (by linarith)
    have hfg : (fun s => apuc 0 (w * s ^ 2)) = fun s => Real.cos (k * s) := by
      funext s
      rw [apuc_zero_eq, langerCosh_nonpos (by nlinarith [sq_nonneg s])]
      have : -(w * s ^ 2) = (k * s) ^ 2 := by rw [mul_pow, hk2]; ring
      rw [this, Real.sqrt_sq_eq_abs, Real.cos_abs]
    have hg1 : ∀ s, HasDerivAt (fun s => Real.cos (k * s)) (-(k * Real.sin (k * s))) s := by
      intro s
      have := (Real.hasDerivAt_cos (k * s)).comp s ((hasDerivAt_id s).const_mul k)
      refine this.congr_deriv ?_
      simp; ring
    have hg2 : ∀ s, HasDerivAt (fun s => -(k * Real.sin (k * s))) (-(k ^ 2 * Real.cos (k * s))) s := by
      intro s
      have := ((Real.hasDerivAt_sin (k * s)).comp s ((hasDerivAt_id s).const_mul k)).const_mul k |>.neg
      refine this.congr_deriv ?_
      simp; ring
    have := apu_deriv2_eq hE1 hE2 hg1 hg2 hfg 1
    simp only [one_pow, mul_one] at this
    have hc : Real.cos (k * 1) = apuc 0 w := by
      have := congrFun hfg 1
      simp only [one_pow, mul_one] at this ⊢
      exact this.symm
    rw [mul_one] at hc
    rw [hk2, hc] at this
    have h2 : w * (apuc 0 w) = w * (4 * w * apuc 2 w + 2 * apuc 1 w) := by
      linear_combination (-1 : ℝ) * this
    exact mul_left_cancel₀ hw h2
  · -- `w > 0`: `E = cosh(k s)`
    set k : ℝ := √w with hk
    have hk2 : k ^ 2 = w := Real.sq_sqrt hpos.le
    have hfg : (fun s => apuc 0 (w * s ^ 2)) = fun s => Real.cosh (k * s) := by
      funext s
      rw [apuc_zero_eq, langerCosh_nonneg (by positivity)]
      have : w * s ^ 2 = (k * s) ^ 2 := by rw [mul_pow, hk2]
      rw [this, Real.sqrt_sq_eq_abs, Real.cosh_abs]
    have hg1 : ∀ s, HasDerivAt (fun s => Real.cosh (k * s)) (k * Real.sinh (k * s)) s := by
      intro s
      have := (Real.hasDerivAt_cosh (k * s)).comp s ((hasDerivAt_id s).const_mul k)
      refine this.congr_deriv ?_
      simp; ring
    have hg2 : ∀ s, HasDerivAt (fun s => k * Real.sinh (k * s)) (k ^ 2 * Real.cosh (k * s)) s := by
      intro s
      have := ((Real.hasDerivAt_sinh (k * s)).comp s ((hasDerivAt_id s).const_mul k)).const_mul k
      refine this.congr_deriv ?_
      simp; ring
    have := apu_deriv2_eq hE1 hE2 hg1 hg2 hfg 1
    simp only [one_pow, mul_one] at this
    have hc : Real.cosh (k * 1) = apuc 0 w := by
      have := congrFun hfg 1
      simp only [one_pow, mul_one] at this ⊢
      exact this.symm
    rw [mul_one] at hc
    rw [hk2, hc] at this
    have h2 : w * (apuc 0 w) = w * (4 * w * apuc 2 w + 2 * apuc 1 w) := by
      linear_combination (-1 : ℝ) * this
    exact mul_left_cancel₀ hw h2

/-- `4 w Ch'' + 2 Ch' = Ch` for all `w`. -/
lemma apuc_ode0 (w : ℝ) : apuc 0 w = 4 * w * apuc 2 w + 2 * apuc 1 w := by
  by_cases hw : w = 0
  · subst hw; rw [apuc_zero_at, apuc_one_at]; ring
  · exact apuc_ode0_ne hw

/-- First derivative of the ODE: `Ch' = 6 Ch'' + 4 w Ch'''`. -/
lemma apuc_ode1 (w : ℝ) : apuc 1 w = 6 * apuc 2 w + 4 * w * apuc 3 w := by
  have hf : ∀ x, HasDerivAt (apuc 0) (apuc 1 x) x := apuc_hasDerivAt 0
  have hg : ∀ x, HasDerivAt (fun w => 4 * w * apuc 2 w + 2 * apuc 1 w)
      (4 * apuc 2 x + 4 * x * apuc 3 x + 2 * apuc 2 x) x := by
    intro x
    have := (((hasDerivAt_id x).const_mul 4).mul (apuc_hasDerivAt 2 x)).add
      ((apuc_hasDerivAt 1 x).const_mul 2)
    refine this.congr_deriv ?_
    simp
  have hfg : apuc 0 = fun w => 4 * w * apuc 2 w + 2 * apuc 1 w := funext apuc_ode0
  have h := (hf w).unique (hfg ▸ hg w)
  linarith

/-- Second derivative of the ODE: `Ch'' = 10 Ch''' + 4 w Ch''''`. -/
lemma apuc_ode2 (w : ℝ) : apuc 2 w = 10 * apuc 3 w + 4 * w * apuc 4 w := by
  have hf : ∀ x, HasDerivAt (apuc 1) (apuc 2 x) x := apuc_hasDerivAt 1
  have hg : ∀ x, HasDerivAt (fun w => 6 * apuc 2 w + 4 * w * apuc 3 w)
      (6 * apuc 3 x + 4 * apuc 3 x + 4 * x * apuc 4 x) x := by
    intro x
    have := ((apuc_hasDerivAt 2 x).const_mul 6).add
      (((hasDerivAt_id x).const_mul 4).mul (apuc_hasDerivAt 3 x))
    refine this.congr_deriv ?_
    simp; ring
  have hfg : apuc 1 = fun w => 6 * apuc 2 w + 4 * w * apuc 3 w := funext apuc_ode1
  have h := (hf w).unique (hfg ▸ hg w)
  linarith

/-! ### The closed forms -/

/-- `E(ζ,s) = Ch(ζ s²)`. -/
noncomputable def apuE (z s : ℝ) : ℝ := apuc 0 (z * s ^ 2)
/-- `∂_s E = 2 ζ s Ch'(ζ s²)`. -/
noncomputable def apuE1 (z s : ℝ) : ℝ := 2 * z * s * apuc 1 (z * s ^ 2)
/-- `O(ζ,s) = s³ (Ch'/2 - Ch'')(ζ s²)` (the `h¹` coefficient of `C`). -/
noncomputable def apuO (z s : ℝ) : ℝ := s ^ 3 * (apuc 1 (z * s ^ 2) / 2 - apuc 2 (z * s ^ 2))
/-- `∂_s O`. -/
noncomputable def apuO1 (z s : ℝ) : ℝ :=
  3 * s ^ 2 * (apuc 1 (z * s ^ 2) / 2 - apuc 2 (z * s ^ 2)) +
    2 * z * s ^ 4 * (apuc 2 (z * s ^ 2) / 2 - apuc 3 (z * s ^ 2))
/-- `A(ζ,s) = 2 s Ch'(ζ s²) = s Sh(ζ s²) = sinh(√ζ s)/√ζ` (the `h⁰` coefficient of `S`). -/
noncomputable def apuA (z s : ℝ) : ℝ := 2 * s * apuc 1 (z * s ^ 2)
/-- `B(ζ,s) = s⁴ Ch''(ζ s²)` (the `h¹` coefficient of `S`). -/
noncomputable def apuB (z s : ℝ) : ℝ := s ^ 4 * apuc 2 (z * s ^ 2)
/-- `∂_s B`. -/
noncomputable def apuB1 (z s : ℝ) : ℝ :=
  4 * s ^ 3 * apuc 2 (z * s ^ 2) + 2 * z * s ^ 5 * apuc 3 (z * s ^ 2)

lemma apu_hasDerivAt_E (z s : ℝ) : HasDerivAt (apuE z) (apuE1 z s) s := by
  have := apu_hd 0 z s
  unfold apuE apuE1
  refine this.congr_deriv ?_
  simp; ring

/-- `∂_s² E = ζ E`. -/
lemma apu_hasDerivAt_E1 (z s : ℝ) : HasDerivAt (apuE1 z) (z * apuE z s) s := by
  have := ((hasDerivAt_id s).const_mul (2 * z)).mul (apu_hd 1 z s)
  have h0 := apuc_ode0 (z * s ^ 2)
  unfold apuE1 apuE
  refine (this.congr_deriv ?_)
  simp only [id]
  rw [h0]; ring

lemma apu_hasDerivAt_O (z s : ℝ) : HasDerivAt (apuO z) (apuO1 z s) s := by
  have := (hasDerivAt_pow 3 s).mul (((apu_hd 1 z s).div_const 2).sub (apu_hd 2 z s))
  unfold apuO apuO1
  refine this.congr_deriv ?_
  simp; ring

/-- `∂_s² O = ζ O + s E`. -/
lemma apu_hasDerivAt_O1 (z s : ℝ) : HasDerivAt (apuO1 z) (z * apuO z s + s * apuE z s) s := by
  have h1 := ((hasDerivAt_pow 2 s).const_mul 3).mul (((apu_hd 1 z s).div_const 2).sub (apu_hd 2 z s))
  have h2 := (((hasDerivAt_pow 4 s).const_mul (2 * z))).mul (((apu_hd 2 z s).div_const 2).sub (apu_hd 3 z s))
  have := h1.add h2
  have o0 := apuc_ode0 (z * s ^ 2)
  have o1 := apuc_ode1 (z * s ^ 2)
  have o2 := apuc_ode2 (z * s ^ 2)
  unfold apuO1 apuO apuE
  refine this.congr_deriv ?_
  simp only [Pi.sub_apply, Nat.cast_ofNat, Nat.reduceAdd, Nat.reduceSub, pow_one]
  rw [o0, o1, o2]; ring

lemma apu_hasDerivAt_A (z s : ℝ) : HasDerivAt (apuA z) (apuE z s) s := by
  have := ((hasDerivAt_id s).const_mul 2).mul (apu_hd 1 z s)
  have h0 := apuc_ode0 (z * s ^ 2)
  unfold apuA apuE
  refine this.congr_deriv ?_
  simp only [id]
  rw [h0]; ring

lemma apu_hasDerivAt_B (z s : ℝ) : HasDerivAt (apuB z) (apuB1 z s) s := by
  have := (hasDerivAt_pow 4 s).mul (apu_hd 2 z s)
  unfold apuB apuB1
  refine this.congr_deriv ?_
  simp; ring

/-- `∂_s² B = ζ B + s A`. -/
lemma apu_hasDerivAt_B1 (z s : ℝ) : HasDerivAt (apuB1 z) (z * apuB z s + s * apuA z s) s := by
  have h1 := ((hasDerivAt_pow 3 s).const_mul 4).mul (apu_hd 2 z s)
  have h2 := ((hasDerivAt_pow 5 s).const_mul (2 * z)).mul (apu_hd 3 z s)
  have := h1.add h2
  have o1 := apuc_ode1 (z * s ^ 2)
  have o2 := apuc_ode2 (z * s ^ 2)
  unfold apuB1 apuB apuA
  refine this.congr_deriv ?_
  simp only [Nat.cast_ofNat, Nat.reduceAdd, Nat.reduceSub]
  rw [o1, o2]; ring

/-! ### Parity and initial data -/

lemma apuE_neg (z s : ℝ) : apuE z (-s) = apuE z s := by unfold apuE; rw [neg_sq]
lemma apuO_neg (z s : ℝ) : apuO z (-s) = -apuO z s := by unfold apuO; rw [neg_sq]; ring
lemma apuA_neg (z s : ℝ) : apuA z (-s) = -apuA z s := by unfold apuA; rw [neg_sq]; ring
lemma apuB_neg (z s : ℝ) : apuB z (-s) = apuB z s := by unfold apuB; rw [neg_sq]; ring

lemma apuE_zero (z : ℝ) : apuE z 0 = 1 := by unfold apuE; simp [apuc_zero_at]
lemma apuE1_zero (z : ℝ) : apuE1 z 0 = 0 := by unfold apuE1; simp
lemma apuO_zero (z : ℝ) : apuO z 0 = 0 := by unfold apuO; simp
lemma apuO1_zero (z : ℝ) : apuO1 z 0 = 0 := by unfold apuO1; simp
lemma apuA_zero (z : ℝ) : apuA z 0 = 0 := by unfold apuA; simp
lemma apuB_zero (z : ℝ) : apuB z 0 = 0 := by unfold apuB; simp
lemma apuB1_zero (z : ℝ) : apuB1 z 0 = 0 := by unfold apuB1; simp

/-! ### Compact-uniform bounds -/

/-- `Ch, Ch', Ch'', Ch'''` are bounded on `|w| ≤ W`. -/
lemma apuc_bound (W : ℝ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ w : ℝ, |w| ≤ W →
    |apuc 0 w| ≤ M ∧ |apuc 1 w| ≤ M ∧ |apuc 2 w| ≤ M ∧ |apuc 3 w| ≤ M := by
  have hc : IsCompact (Icc (-|W|) |W|) := isCompact_Icc
  have key : ∀ k : ℕ, ∃ C : ℝ, ∀ w ∈ Icc (-|W|) |W|, |apuc k w| ≤ C := fun k => by
    obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn (apuc_continuous k).continuousOn
    exact ⟨C, fun w hw => by simpa using hC w hw⟩
  obtain ⟨C0, h0⟩ := key 0
  obtain ⟨C1, h1⟩ := key 1
  obtain ⟨C2, h2⟩ := key 2
  obtain ⟨C3, h3⟩ := key 3
  refine ⟨|C0| + |C1| + |C2| + |C3|, by positivity, fun w hw => ?_⟩
  have hw' : w ∈ Icc (-|W|) |W| :=
    ⟨by linarith [neg_abs_le w, le_abs_self W], by linarith [le_abs_self w, le_abs_self W]⟩
  have a0 := (h0 w hw').trans (le_abs_self C0)
  have a1 := (h1 w hw').trans (le_abs_self C1)
  have a2 := (h2 w hw').trans (le_abs_self C2)
  have a3 := (h3 w hw').trans (le_abs_self C3)
  have := abs_nonneg C0; have := abs_nonneg C1; have := abs_nonneg C2; have := abs_nonneg C3
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- **Uniform bounds** for the seven functions `E, ∂E, O, ∂O, A, B, ∂B` on `|ζ| ≤ Z₀`, `|s| ≤ S`. -/
lemma apu_bounds (Z0 S : ℝ) (hZ0 : 0 ≤ Z0) (hS : 0 ≤ S) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z s : ℝ, |z| ≤ Z0 → |s| ≤ S →
      |apuE z s| ≤ M ∧ |apuE1 z s| ≤ M ∧ |apuO z s| ≤ M ∧ |apuO1 z s| ≤ M ∧ |apuA z s| ≤ M ∧
        |apuB z s| ≤ M ∧ |apuB1 z s| ≤ M := by
  obtain ⟨Mc, hMc0, hMc⟩ := apuc_bound (Z0 * S ^ 2)
  refine ⟨Mc + 2 * Z0 * S * Mc + S ^ 3 * (3 / 2 * Mc) +
    (3 * S ^ 2 * (3 / 2 * Mc) + 2 * Z0 * S ^ 4 * (3 / 2 * Mc)) + 2 * S * Mc + S ^ 4 * Mc +
    (4 * S ^ 3 * Mc + 2 * Z0 * S ^ 5 * Mc), by positivity, fun z s hz hs => ?_⟩
  have hw : |z * s ^ 2| ≤ Z0 * S ^ 2 := by
    rw [abs_mul, abs_pow]; exact mul_le_mul hz (pow_le_pow_left₀ (abs_nonneg _) hs 2) (by positivity) hZ0
  obtain ⟨b0, b1, b2, b3⟩ := hMc _ hw
  have hz0 := abs_nonneg z
  have hs0 := abs_nonneg s
  -- the cross factors
  have q1 : |apuc 1 (z * s ^ 2) / 2 - apuc 2 (z * s ^ 2)| ≤ 3 / 2 * Mc := by
    have := abs_sub (apuc 1 (z * s ^ 2) / 2) (apuc 2 (z * s ^ 2))
    rw [abs_div, abs_two] at this; linarith
  have q2 : |apuc 2 (z * s ^ 2) / 2 - apuc 3 (z * s ^ 2)| ≤ 3 / 2 * Mc := by
    have := abs_sub (apuc 2 (z * s ^ 2) / 2) (apuc 3 (z * s ^ 2))
    rw [abs_div, abs_two] at this; linarith
  have eE : |apuE z s| ≤ Mc := b0
  have eE1 : |apuE1 z s| ≤ 2 * Z0 * S * Mc := by
    unfold apuE1
    rw [abs_mul, abs_mul, abs_mul, abs_two]
    gcongr
  have eO : |apuO z s| ≤ S ^ 3 * (3 / 2 * Mc) := by
    unfold apuO
    rw [abs_mul, abs_pow]
    gcongr
  have eO1 : |apuO1 z s| ≤ 3 * S ^ 2 * (3 / 2 * Mc) + 2 * Z0 * S ^ 4 * (3 / 2 * Mc) := by
    unfold apuO1
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_mul, abs_pow, abs_of_pos (by norm_num : (0:ℝ) < 3)]
      gcongr
    · rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_two]
      gcongr
  have eA : |apuA z s| ≤ 2 * S * Mc := by
    unfold apuA
    rw [abs_mul, abs_mul, abs_two]
    gcongr
  have eB : |apuB z s| ≤ S ^ 4 * Mc := by
    unfold apuB
    rw [abs_mul, abs_pow]
    gcongr
  have eB1 : |apuB1 z s| ≤ 4 * S ^ 3 * Mc + 2 * Z0 * S ^ 5 * Mc := by
    unfold apuB1
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_mul, abs_pow, abs_of_pos (by norm_num : (0:ℝ) < 4)]
      gcongr
    · rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_two]
      gcongr
  have t1 : 0 ≤ 2 * Z0 * S * Mc := by positivity
  have t2 : 0 ≤ S ^ 3 * (3 / 2 * Mc) := by positivity
  have t3 : 0 ≤ 3 * S ^ 2 * (3 / 2 * Mc) + 2 * Z0 * S ^ 4 * (3 / 2 * Mc) := by positivity
  have t4 : 0 ≤ 2 * S * Mc := by positivity
  have t5 : 0 ≤ S ^ 4 * Mc := by positivity
  have t6 : 0 ≤ 4 * S ^ 3 * Mc + 2 * Z0 * S ^ 5 * Mc := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- info: 'FormalResearch.Special.apuc_ode0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.apuc_ode0

/-- info: 'FormalResearch.Special.apuc_ode1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.apuc_ode1

/-- info: 'FormalResearch.Special.apuc_ode2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.apuc_ode2

/-- info: 'FormalResearch.Special.apu_hasDerivAt_O1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.apu_hasDerivAt_O1

/-- info: 'FormalResearch.Special.apu_hasDerivAt_B1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.apu_hasDerivAt_B1

/-- info: 'FormalResearch.Special.apu_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.apu_bounds

end FormalResearch.Special
