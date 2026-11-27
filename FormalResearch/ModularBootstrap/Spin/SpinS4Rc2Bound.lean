module

public import FormalResearch.ModularBootstrap.Spin.ScalC1
public import FormalResearch.ModularBootstrap.Spin.SpinS4Statements

/-!
# SPIN-S4 Adjoint Ratio Bounds and Measurability (`s4:eR.7`)

Proves:
1. `spinWc_zero`, `spinG_d4_neg_left`, `spinG_d4_neg_right`, `spinG_d4_swap`.
2. Global nonnegativity, `d`-evenness, and measurability of `spinRc1`, `spinRc2`, `spinRc`.
3. `spinRc2_le_div_n`: global `O(n⁻¹)` upper bound on the swapped adjoint term `spinRc2 a ξ d`
   for `|d| ≤ ξ` and `c ≥ 40` (`(s4:eR.7)`).
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.Spin

open FormalResearch.ModularBootstrap

/-! ### Elementary `spinWc`, `spinG`, and `tanh` properties -/

lemma spinWc_zero (a : ℝ) : spinWc a 0 = 0 := by
  unfold spinWc spinV1
  simp

lemma spinG_d4_neg_left {a : ℝ} {Φ : ℝ × ℝ → ℝ} (hΦ : SpinTestClass a Φ) (xL xR : ℝ) :
    spinG a Φ (-xL) xR = spinG a Φ xL xR := by
  unfold spinG
  rw [show 2 * Real.sqrt a * (-xL) = -(2 * Real.sqrt a * xL) by ring]
  exact hΦ.d4_inv.1 _ _

lemma spinG_d4_neg_right {a : ℝ} {Φ : ℝ × ℝ → ℝ} (hΦ : SpinTestClass a Φ) (xL xR : ℝ) :
    spinG a Φ xL (-xR) = spinG a Φ xL xR := by
  unfold spinG
  rw [show 2 * Real.sqrt a * (-xR) = -(2 * Real.sqrt a * xR) by ring]
  exact hΦ.d4_inv.2.1 _ _

lemma spinG_d4_swap {a : ℝ} {Φ : ℝ × ℝ → ℝ} (hΦ : SpinTestClass a Φ) (xL xR : ℝ) :
    spinG a Φ xR xL = spinG a Φ xL xR := by
  unfold spinG
  exact hΦ.d4_inv.2.2 _ _

lemma continuous_spinTanh : Continuous Real.tanh := by
  have : Real.tanh = fun x => Real.sinh x / Real.cosh x := by
    ext x; exact Real.tanh_eq_sinh_div_cosh x
  rw [this]
  exact Real.continuous_sinh.div Real.continuous_cosh (fun x => (Real.cosh_pos x).ne')

lemma spinTanh_pos {r : ℝ} (hr : 0 < r) : 0 < Real.tanh r := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos (Real.sinh_pos_iff.mpr hr) (Real.cosh_pos r)

lemma spinTanh_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ Real.tanh r := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_nonneg (Real.sinh_nonneg_iff.mpr hr) (Real.cosh_pos r).le

lemma spinTanh_le_one (r : ℝ) : Real.tanh r ≤ 1 := by
  rw [Real.tanh_eq_sinh_div_cosh, div_le_one (Real.cosh_pos r), Real.sinh_eq, Real.cosh_eq]
  linarith [Real.exp_pos (-r)]

private lemma spinTanh_half_le_half {x : ℝ} (hx : 0 ≤ x) : Real.tanh (x / 2) ≤ x / 2 := by
  rw [Real.tanh_eq_sinh_div_cosh, div_le_iff₀ (Real.cosh_pos _)]
  let g : ℝ → ℝ := fun u => u * Real.cosh u - Real.sinh u
  have hg_deriv : ∀ u : ℝ, HasDerivAt g (u * Real.sinh u) u := fun u => by
    have h1 : HasDerivAt (fun t : ℝ => t * Real.cosh t) (1 * Real.cosh u + u * Real.sinh u) u :=
      (hasDerivAt_id u).mul (Real.hasDerivAt_cosh u)
    have h2 : HasDerivAt Real.sinh (Real.cosh u) u := Real.hasDerivAt_sinh u
    exact (h1.sub h2).congr_deriv (by ring)
  have hg_mono : MonotoneOn g (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact ((continuous_id.mul Real.continuous_cosh).sub Real.continuous_sinh).continuousOn
    · intro u _; exact (hg_deriv u).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [interior_Ici] at hu
      have hu0 : 0 ≤ u := (mem_Ioi.mp hu).le
      rw [(hg_deriv u).deriv]
      exact mul_nonneg hu0 (Real.sinh_nonneg_iff.mpr hu0)
  have h0 : g 0 ≤ g (x / 2) := hg_mono (mem_Ici.mpr le_rfl) (mem_Ici.mpr (by linarith)) (by linarith)
  dsimp [g] at h0
  simp only [zero_mul, Real.sinh_zero, sub_zero] at h0
  linarith

lemma spinCalF_pos' {x : ℝ} (hx : 0 < x) : 0 < spinCalF x := by
  unfold spinCalF
  have h1 : Real.exp (-4 * π * x) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  linarith

lemma spinCalPhi_pos' {x : ℝ} (hx : 0 < x) : 0 < spinCalPhi x := by
  unfold spinCalPhi
  exact div_pos (pow_pos (spinTanh_pos (half_pos hx)) 2) (spinCalF_pos' hx)

lemma spinCalFc_nonneg_of_nonneg {a x : ℝ} (ha : 2 ≤ a) (hx : 0 ≤ x) :
    0 ≤ spinCalFc a x := by
  unfold spinCalFc
  have ha0 : 0 < a := by linarith
  have hg0 : 0 ≤ spinGamma a := Real.sqrt_nonneg _
  have hg1 : spinGamma a ≤ 1 := by
    unfold spinGamma
    exact Real.sqrt_le_one.mpr (by linarith [div_nonneg two_pos.le ha0.le])
  have h1g : 0 ≤ 1 - spinGamma a := sub_nonneg.mpr hg1
  have h1 : Real.exp (-π * (12 * a) * (1 + spinGamma a) * x / 3) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by
      have : 0 ≤ π * (12 * a) * (1 + spinGamma a) * x / 3 := by positivity
      linarith)
  have h2 : Real.exp (-π * (12 * a) * (1 - spinGamma a) * x / 3) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by
      have : 0 ≤ π * (12 * a) * (1 - spinGamma a) * x / 3 := by positivity
      linarith)
  exact mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)

lemma spinCalFc_pos_of_pos {a x : ℝ} (ha : 2 < a) (hx : 0 < x) :
    0 < spinCalFc a x := by
  unfold spinCalFc
  have hg0 : 0 ≤ spinGamma a := (spinGamma_pos ha).le
  have hg1 : spinGamma a < 1 := spinGamma_lt_one ha
  have ha0 : 0 < a := by linarith
  have h1g : 0 < 1 - spinGamma a := sub_pos.mpr hg1
  have h1 : Real.exp (-π * (12 * a) * (1 + spinGamma a) * x / 3) < 1 :=
    Real.exp_lt_one_iff.mpr (by
      have : 0 < π * (12 * a) * (1 + spinGamma a) * x / 3 := by positivity
      linarith)
  have h2 : Real.exp (-π * (12 * a) * (1 - spinGamma a) * x / 3) < 1 :=
    Real.exp_lt_one_iff.mpr (by
      have : 0 < π * (12 * a) * (1 - spinGamma a) * x / 3 := by positivity
      linarith)
  exact mul_pos (sub_pos.mpr h1) (sub_pos.mpr h2)

lemma spinCalPhic_nonneg_all {a : ℝ} (ha : 2 ≤ a) (x : ℝ) : 0 ≤ spinCalPhic a x := by
  rcases le_total 0 x with hx | hx
  · unfold spinCalPhic
    split_ifs with hx0
    · exact le_rfl
    · exact div_nonneg (sq_nonneg _) (spinCalFc_nonneg_of_nonneg ha hx)
  · by_cases hx0 : x = 0
    · subst hx0; simp [spinCalPhic]
    · have hnx0 : -x ≠ 0 := neg_ne_zero.mpr hx0
      have hpos : 0 ≤ -x := neg_nonneg.mpr hx
      have hneg : spinCalPhic a x = Real.exp (-8 * π * a * (-x)) * spinCalPhic a (-x) := by
        unfold spinCalPhic
        simp only [hx0, hnx0, ite_false]
        rw [show x / 2 = -((-x) / 2) by ring, Real.tanh_neg, neg_sq]
        unfold spinCalFc
        set u1 := π * (12 * a) * (1 + spinGamma a) * (-x) / 3
        set u2 := π * (12 * a) * (1 - spinGamma a) * (-x) / 3
        have hsum : u1 + u2 = 8 * π * a * (-x) := by dsimp [u1, u2]; ring
        have hrew1 : -π * (12 * a) * (1 + spinGamma a) * x / 3 = u1 := by dsimp [u1]; ring
        have hrew2 : -π * (12 * a) * (1 - spinGamma a) * x / 3 = u2 := by dsimp [u2]; ring
        have hrew3 : -π * (12 * a) * (1 + spinGamma a) * (-x) / 3 = -u1 := by dsimp [u1]; ring
        have hrew4 : -π * (12 * a) * (1 - spinGamma a) * (-x) / 3 = -u2 := by dsimp [u2]; ring
        rw [hrew1, hrew2, hrew3, hrew4]
        have e1 : 1 - Real.exp u1 = -(Real.exp u1 * (1 - Real.exp (-u1))) := by
          rw [mul_sub, mul_one, ← Real.exp_add, add_neg_cancel, Real.exp_zero]; ring
        have e2 : 1 - Real.exp u2 = -(Real.exp u2 * (1 - Real.exp (-u2))) := by
          rw [mul_sub, mul_one, ← Real.exp_add, add_neg_cancel, Real.exp_zero]; ring
        rw [e1, e2]
        have heq : (-(Real.exp u1 * (1 - Real.exp (-u1)))) *
            (-(Real.exp u2 * (1 - Real.exp (-u2)))) =
            Real.exp (8 * π * a * (-x)) * ((1 - Real.exp (-u1)) * (1 - Real.exp (-u2))) := by
          rw [← hsum, Real.exp_add]; ring
        rw [heq]
        have hrec : (Real.exp (8 * π * a * (-x)))⁻¹ = Real.exp (-8 * π * a * (-x)) := by
          rw [← Real.exp_neg]; congr 1; ring
        rw [div_mul_eq_div_div, div_eq_mul_inv, div_eq_mul_inv, hrec]; ring
      rw [hneg]
      refine mul_nonneg (Real.exp_pos _).le ?_
      unfold spinCalPhic
      split_ifs with hnx
      · exact le_rfl
      · exact div_nonneg (sq_nonneg _) (spinCalFc_nonneg_of_nonneg ha hpos)

lemma spinRc1_nonneg {a : ℝ} (ha : 2 ≤ a) (ξ d : ℝ) : 0 ≤ spinRc1 a ξ d := by
  unfold spinRc1
  have h1 := spinCalPhic_nonneg_all ha (ξ + d)
  have h2 := spinCalPhic_nonneg_all ha (ξ - d)
  positivity

lemma spinRc2_nonneg {a : ℝ} (ha : 2 ≤ a) (ξ d : ℝ) : 0 ≤ spinRc2 a ξ d := by
  unfold spinRc2
  have h1 := spinCalPhic_nonneg_all ha (ξ + d)
  have h2 := spinCalPhic_nonneg_all ha (ξ - d)
  positivity

lemma spinRc_nonneg_all' {a : ℝ} (ha : 2 ≤ a) (ξ d : ℝ) : 0 ≤ spinRc a ξ d :=
  add_nonneg (spinRc1_nonneg ha ξ d) (spinRc2_nonneg ha ξ d)

lemma spinRc1_even_d (a ξ d : ℝ) : spinRc1 a ξ (-d) = spinRc1 a ξ d := by
  unfold spinRc1
  have h1 : ξ + -d = ξ - d := by ring
  have h2 : ξ - -d = ξ + d := by ring
  rw [h1, h2, neg_sq]; ring

lemma spinRc2_even_d (a ξ d : ℝ) : spinRc2 a ξ (-d) = spinRc2 a ξ d := by
  unfold spinRc2
  have h1 : ξ + -d = ξ - d := by ring
  have h2 : ξ - -d = ξ + d := by ring
  rw [h1, h2, abs_neg, neg_sq, mul_comm (spinCalPhic a (ξ - d)) (spinCalPhic a (ξ + d))]

lemma measurable_spinCalPhic' (a : ℝ) : Measurable (spinCalPhic a) := by
  unfold spinCalPhic spinCalFc
  have ht : Measurable (fun x : ℝ => Real.tanh (x / 2) ^ 2) :=
    (continuous_spinTanh.comp (continuous_id.div_const 2)).measurable.pow_const 2
  have hf : Measurable (fun x : ℝ =>
      (1 - Real.exp (-π * (12 * a) * (1 + spinGamma a) * x / 3)) *
        (1 - Real.exp (-π * (12 * a) * (1 - spinGamma a) * x / 3))) :=
    ((measurable_const.sub (Real.measurable_exp.comp ((measurable_const.mul measurable_id).div_const 3))).mul
      (measurable_const.sub (Real.measurable_exp.comp ((measurable_const.mul measurable_id).div_const 3))))
  exact Measurable.ite measurableSet_eq measurable_const (ht.div hf)

lemma measurable_spinRc1 (a : ℝ) :
    Measurable (fun p : ℝ × ℝ => spinRc1 a (spinLongDist p) ((|p.1| - |p.2|) / 2)) := by
  unfold spinRc1 spinLongDist
  have hξ : Measurable (fun p : ℝ × ℝ => (1 / 2 : ℝ) * (|p.1| + |p.2|)) :=
    measurable_const.mul ((measurable_fst.abs).add (measurable_snd.abs))
  have hd : Measurable (fun p : ℝ × ℝ => (|p.1| - |p.2|) / 2) :=
    ((measurable_fst.abs).sub (measurable_snd.abs)).div_const 2
  have hp1 : Measurable (fun p : ℝ × ℝ => spinCalPhic a ((1 / 2 : ℝ) * (|p.1| + |p.2|) + (|p.1| - |p.2|) / 2)) :=
    (measurable_spinCalPhic' a).comp (hξ.add hd)
  have hp2 : Measurable (fun p : ℝ × ℝ => spinCalPhic a ((1 / 2 : ℝ) * (|p.1| + |p.2|) - (|p.1| - |p.2|) / 2)) :=
    (measurable_spinCalPhic' a).comp (hξ.sub hd)
  refine ((measurable_const.div (measurable_const.add (hξ.pow_const 2))).mul
    ((hp1.mul hp2).div_const _)).mul ?_
  exact Real.measurable_exp.comp (((((hd.pow_const 2).neg.div_const _).sub
    ((measurable_const.mul ((hξ.pow_const 2).sub measurable_const)).div_const _))).sub
    (((hξ.pow_const 2).sub measurable_const).pow_const 2))

lemma measurable_spinRc2 (a : ℝ) :
    Measurable (fun p : ℝ × ℝ => spinRc2 a (spinLongDist p) ((|p.1| - |p.2|) / 2)) := by
  unfold spinRc2 spinLongDist
  have hξ : Measurable (fun p : ℝ × ℝ => (1 / 2 : ℝ) * (|p.1| + |p.2|)) :=
    measurable_const.mul ((measurable_fst.abs).add (measurable_snd.abs))
  have hd : Measurable (fun p : ℝ × ℝ => (|p.1| - |p.2|) / 2) :=
    ((measurable_fst.abs).sub (measurable_snd.abs)).div_const 2
  have hp1 : Measurable (fun p : ℝ × ℝ => spinCalPhic a ((1 / 2 : ℝ) * (|p.1| + |p.2|) + (|p.1| - |p.2|) / 2)) :=
    (measurable_spinCalPhic' a).comp (hξ.add hd)
  have hp2 : Measurable (fun p : ℝ × ℝ => spinCalPhic a ((1 / 2 : ℝ) * (|p.1| + |p.2|) - (|p.1| - |p.2|) / 2)) :=
    (measurable_spinCalPhic' a).comp (hξ.sub hd)
  refine (((Real.measurable_exp.comp (measurable_const.mul (hξ.sub hd.abs))).mul
    (measurable_const.div (measurable_const.add (hd.pow_const 2)))).mul
    ((hp1.mul hp2).div_const _)).mul ?_
  exact Real.measurable_exp.comp (((((hξ.pow_const 2).neg.div_const _).sub
    ((measurable_const.mul ((hd.pow_const 2).sub measurable_const)).div_const _))).sub
    (((hd.pow_const 2).sub measurable_const).pow_const 2))

/-! ### Global `O(n⁻¹)` bound on `spinRc2` (`(s4:eR.7)`) -/

private lemma one_sub_exp_ge_div_one_add {t : ℝ} (ht : 0 ≤ t) :
    t / (1 + t) ≤ 1 - Real.exp (-t) := by
  have hexp : 1 + t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
  have hinv : Real.exp (-t) ≤ (1 + t)⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ (by linarith) hexp
  have hpos : 0 < 1 + t := by linarith
  have hrew : t / (1 + t) = 1 - (1 + t)⁻¹ := by field_simp [hpos.ne']; ring
  linarith

private lemma one_sub_exp_ge_half_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    (1 / 2 : ℝ) ≤ 1 - Real.exp (-t) := by
  have hexp : (2 : ℝ) ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
  have hinv : Real.exp (-t) ≤ (1 / 2 : ℝ) := by
    rw [Real.exp_neg]
    exact (inv_anti₀ (by norm_num) hexp).trans_eq (by norm_num)
  linarith

private lemma spinCalFc_lower_small {c x : ℝ} (hc : 40 ≤ c) (hx0 : 0 < x) (hx1 : x < 1) :
    let n := c - 1
    let a := n / 12
    (1 / 2 : ℝ) * x ≤ 1 - Real.exp (-π * (12 * a) * (1 - spinGamma a) * x / 3) ∧
      ((1 / 2 : ℝ) * (min (π * n * x / 3) 1)) ≤
        1 - Real.exp (-π * (12 * a) * (1 + spinGamma a) * x / 3) := by
  intro n a
  have ha2 : 2 < a := by dsimp [a, n]; linarith
  have ha0 : 0 < a := by linarith
  have hn0 : 0 < n := by dsimp [n]; linarith
  have h12a : 12 * a = n := by dsimp [a]; ring
  have hg0 : 0 < spinGamma a := spinGamma_pos ha2
  have hg1 : spinGamma a < 1 := spinGamma_lt_one ha2
  have h1mg : 1 / a ≤ 1 - spinGamma a := by
    have hdiff : 1 - spinGamma a ^ 2 = 2 / a := by rw [spinGamma_sq ha2.le]; ring
    have hpos : 0 < 1 + spinGamma a := by linarith
    calc 1 / a = (2 / a) / 2 := by ring
      _ ≤ (2 / a) / (1 + spinGamma a) :=
          div_le_div_of_nonneg_left (div_nonneg two_pos.le ha0.le) hpos (by linarith)
      _ = 1 - spinGamma a := by
          rw [← hdiff, show 1 - spinGamma a ^ 2 = (1 - spinGamma a) * (1 + spinGamma a) by ring,
            mul_div_cancel_right₀ _ hpos.ne']
  have hu2_ge : 4 * π * x ≤ π * (12 * a) * (1 - spinGamma a) * x / 3 := by
    calc 4 * π * x = π * (12 * a) * (1 / a) * x / 3 := by field_simp [ha0.ne']; ring
      _ ≤ π * (12 * a) * (1 - spinGamma a) * x / 3 := by gcongr
  have hu1_ge : π * n * x / 3 ≤ π * (12 * a) * (1 + spinGamma a) * x / 3 := by
    rw [h12a]
    have : 0 ≤ π * n * x := by positivity
    nlinarith
  refine ⟨?_, ?_⟩
  · by_cases h4pi : 4 * π * x ≤ 1
    · have hu2_pos : 0 ≤ π * (12 * a) * (1 - spinGamma a) * x / 3 := by
        nlinarith [Real.pi_pos, hx0]
      have hd1 : 0 < 1 + 4 * π * x := by positivity
      have hd2 : 0 < 1 + π * (12 * a) * (1 - spinGamma a) * x / 3 := by linarith
      have hdiv : (4 * π * x) / (1 + 4 * π * x) ≤
          (π * (12 * a) * (1 - spinGamma a) * x / 3) /
            (1 + π * (12 * a) * (1 - spinGamma a) * x / 3) := by
        rw [div_le_div_iff₀ hd1 hd2]
        nlinarith
      have hhalf : (1 / 2 : ℝ) * x ≤ (4 * π * x) / (1 + 4 * π * x) := by
        rw [le_div_iff₀ hd1]
        have : 2 ≤ 4 * π := by linarith [Real.pi_gt_three]
        nlinarith
      exact hhalf.trans (hdiv.trans (by
        have hrew : -π * (12 * a) * (1 - spinGamma a) * x / 3 =
            -(π * (12 * a) * (1 - spinGamma a) * x / 3) := by ring
        rw [hrew]
        exact one_sub_exp_ge_div_one_add hu2_pos))
    · push Not at h4pi
      have hu2_ge1 : 1 ≤ π * (12 * a) * (1 - spinGamma a) * x / 3 := by linarith
      have := one_sub_exp_ge_half_of_one_le hu2_ge1
      have hrew : -π * (12 * a) * (1 - spinGamma a) * x / 3 =
          -(π * (12 * a) * (1 - spinGamma a) * x / 3) := by ring
      rw [hrew]
      exact (mul_le_of_le_one_right (by norm_num) hx1.le).trans this
  · by_cases hpn : π * n * x / 3 ≤ 1
    · rw [min_eq_left hpn]
      have hu1_nn : 0 ≤ π * (12 * a) * (1 + spinGamma a) * x / 3 := by
        nlinarith [Real.pi_pos, hx0, hn0]
      have hpn_nn : 0 ≤ π * n * x / 3 := by positivity
      have hd1 : 0 < 1 + π * n * x / 3 := by linarith
      have hd2 : 0 < 1 + π * (12 * a) * (1 + spinGamma a) * x / 3 := by linarith
      have hdiv : (π * n * x / 3) / (1 + π * n * x / 3) ≤
          (π * (12 * a) * (1 + spinGamma a) * x / 3) /
            (1 + π * (12 * a) * (1 + spinGamma a) * x / 3) := by
        rw [div_le_div_iff₀ hd1 hd2]
        nlinarith
      have hhalf : (1 / 2 : ℝ) * (π * n * x / 3) ≤ (π * n * x / 3) / (1 + π * n * x / 3) := by
        rw [le_div_iff₀ hd1]
        nlinarith
      exact hhalf.trans (hdiv.trans (by
        have hrew : -π * (12 * a) * (1 + spinGamma a) * x / 3 =
            -(π * (12 * a) * (1 + spinGamma a) * x / 3) := by ring
        rw [hrew]
        exact one_sub_exp_ge_div_one_add hu1_nn))
    · push Not at hpn
      rw [min_eq_right hpn.le, mul_one]
      have hu1_ge1 : 1 ≤ π * (12 * a) * (1 + spinGamma a) * x / 3 := by linarith
      have hrew : -π * (12 * a) * (1 + spinGamma a) * x / 3 =
          -(π * (12 * a) * (1 + spinGamma a) * x / 3) := by ring
      rw [hrew]
      exact one_sub_exp_ge_half_of_one_le hu1_ge1

private lemma spinCalPhic_le_four {c x : ℝ} (hc : 40 ≤ c) (hx : 0 ≤ x) :
    spinCalPhic ((c - 1) / 12) x ≤ 4 := by
  let n := c - 1
  let a := n / 12
  change spinCalPhic a x ≤ 4
  have ha2 : 2 < a := by dsimp [a, n]; linarith
  have hn0 : 0 < n := by dsimp [n]; linarith
  rcases eq_or_lt_of_le hx with rfl | hx_pos
  · simp [spinCalPhic]
  · rcases le_or_gt 1 x with hx1 | hx1
    · unfold spinCalPhic
      simp only [hx_pos.ne', ↓reduceIte]
      have h12a : 12 * a = n := by dsimp [a]; ring
      have ha0 : 0 < a := by linarith
      have hg0 : 0 < spinGamma a := spinGamma_pos ha2
      have hg1 : spinGamma a < 1 := spinGamma_lt_one ha2
      have h1mg : 1 / a ≤ 1 - spinGamma a := by
        have hdiff : 1 - spinGamma a ^ 2 = 2 / a := by rw [spinGamma_sq ha2.le]; ring
        have hpos : 0 < 1 + spinGamma a := by linarith
        calc 1 / a = (2 / a) / 2 := by ring
          _ ≤ (2 / a) / (1 + spinGamma a) :=
              div_le_div_of_nonneg_left (div_nonneg two_pos.le ha0.le) hpos (by linarith)
          _ = 1 - spinGamma a := by
              rw [← hdiff, show 1 - spinGamma a ^ 2 = (1 - spinGamma a) * (1 + spinGamma a) by ring,
                mul_div_cancel_right₀ _ hpos.ne']
      have hu2_ge1 : 1 ≤ π * (12 * a) * (1 - spinGamma a) * x / 3 := by
        calc (1 : ℝ) ≤ 4 * π := by linarith [Real.pi_gt_three]
          _ ≤ 4 * π * x := le_mul_of_one_le_right (by positivity) hx1
          _ = π * (12 * a) * (1 / a) * x / 3 := by field_simp [ha0.ne']; ring
          _ ≤ π * (12 * a) * (1 - spinGamma a) * x / 3 := by gcongr
      have hu1_ge1 : 1 ≤ π * (12 * a) * (1 + spinGamma a) * x / 3 := by
        have : 1 - spinGamma a ≤ 1 + spinGamma a := by linarith
        calc (1 : ℝ) ≤ π * (12 * a) * (1 - spinGamma a) * x / 3 := hu2_ge1
          _ ≤ π * (12 * a) * (1 + spinGamma a) * x / 3 := by gcongr
      have hf1 : (1 / 2 : ℝ) ≤ 1 - Real.exp (-π * (12 * a) * (1 + spinGamma a) * x / 3) := by
        rw [show -π * (12 * a) * (1 + spinGamma a) * x / 3 =
          -(π * (12 * a) * (1 + spinGamma a) * x / 3) by ring]
        exact one_sub_exp_ge_half_of_one_le hu1_ge1
      have hf2 : (1 / 2 : ℝ) ≤ 1 - Real.exp (-π * (12 * a) * (1 - spinGamma a) * x / 3) := by
        rw [show -π * (12 * a) * (1 - spinGamma a) * x / 3 =
          -(π * (12 * a) * (1 - spinGamma a) * x / 3) by ring]
        exact one_sub_exp_ge_half_of_one_le hu2_ge1
      have hfc_ge : (1 / 4 : ℝ) ≤ spinCalFc a x := by unfold spinCalFc; nlinarith
      have ht_le : Real.tanh (x / 2) ^ 2 ≤ 1 := by
        have h0 : 0 ≤ Real.tanh (x / 2) := spinTanh_nonneg (by positivity)
        have h1 : Real.tanh (x / 2) ≤ 1 := spinTanh_le_one (x / 2)
        nlinarith
      calc Real.tanh (x / 2) ^ 2 / spinCalFc a x ≤ 1 / (1 / 4) :=
            div_le_div₀ (by positivity) ht_le (by norm_num) hfc_ge
        _ = 4 := by norm_num
    · obtain ⟨hf2, hf1⟩ := spinCalFc_lower_small hc hx_pos hx1
      have hf1' : (1 / 2 : ℝ) * min (π * n * x / 3) 1 ≤
          1 - Real.exp (-π * (12 * a) * (1 + spinGamma a) * x / 3) := hf1
      have hf2' : (1 / 2 : ℝ) * x ≤
          1 - Real.exp (-π * (12 * a) * (1 - spinGamma a) * x / 3) := hf2
      have hfc_pos : 0 < spinCalFc a x := spinCalFc_pos_of_pos ha2 hx_pos
      have ht_le : Real.tanh (x / 2) ^ 2 ≤ x ^ 2 / 4 := by
        have h0 : 0 ≤ Real.tanh (x / 2) := spinTanh_nonneg (half_pos hx_pos).le
        have h1 : Real.tanh (x / 2) ≤ x / 2 := spinTanh_half_le_half hx_pos.le
        nlinarith
      unfold spinCalPhic
      simp only [hx_pos.ne', ↓reduceIte]
      by_cases hpn : π * n * x / 3 ≤ 1
      · rw [min_eq_left hpn] at hf1'
        have hfc_ge : (π * n / 12) * x ^ 2 ≤ spinCalFc a x := by
          unfold spinCalFc
          have heq : (1 / 2 : ℝ) * (π * n * x / 3) * ((1 / 2 : ℝ) * x) = (π * n / 12) * x ^ 2 := by ring
          rw [← heq]
          have hb0 : 0 ≤ (1 / 2 : ℝ) * (π * n * x / 3) := by positivity
          have hf1_nn : 0 ≤ 1 - Real.exp (-π * (12 * a) * (1 + spinGamma a) * x / 3) := by linarith [hf1']
          exact mul_le_mul hf1' hf2' (mul_nonneg (by norm_num) hx_pos.le) hf1_nn
        have hfc_ge_pos : 0 < (π * n / 12) * x ^ 2 := by positivity
        have hbound : Real.tanh (x / 2) ^ 2 / spinCalFc a x ≤ 3 / (π * n) := by
          have hdiv : (x ^ 2 / 4) / ((π * n / 12) * x ^ 2) = 3 / (π * n) := by
            field_simp [hx_pos.ne', Real.pi_pos.ne', hn0.ne']; ring
          conv_rhs => rw [← hdiv]
          exact div_le_div₀ (by positivity) ht_le hfc_ge_pos hfc_ge
        have h3n : 3 / (π * n) ≤ 4 := by
          rw [div_le_iff₀ (by positivity)]
          nlinarith [Real.pi_gt_three]
        exact hbound.trans h3n
      · push Not at hpn
        rw [min_eq_right hpn.le, mul_one] at hf1'
        have hfc_ge : (1 / 4 : ℝ) * x ≤ spinCalFc a x := by
          unfold spinCalFc
          have heq : (1 / 2 : ℝ) * ((1 / 2 : ℝ) * x) = (1 / 4 : ℝ) * x := by ring
          rw [← heq]
          exact mul_le_mul hf1' hf2' (mul_nonneg (by norm_num) hx_pos.le) (by linarith [hf1'])
        have hbound : Real.tanh (x / 2) ^ 2 / spinCalFc a x ≤ x := by
          have hdiv : (x ^ 2 / 4) / ((1 / 4 : ℝ) * x) = x := by field_simp [hx_pos.ne']
          conv_rhs => rw [← hdiv]
          exact div_le_div₀ (by positivity) ht_le (by positivity) hfc_ge
        exact hbound.trans (hx1.le.trans (by norm_num))

private lemma exp_mul_spinCalPhic_le_div_n {c q : ℝ} (hc : 40 ≤ c) (hq : 0 ≤ q) :
    let n := c - 1
    let a := n / 12
    Real.exp (-12 * a * (2 * π / 3) * q) * spinCalPhic a q ≤ 4 / n := by
  intro n a
  have ha2 : 2 < a := by dsimp [a, n]; linarith
  have hn0 : 0 < n := by dsimp [n]; linarith
  have h12a : 12 * a = n := by dsimp [a]; ring
  have hrew : -12 * a * (2 * π / 3) * q = -(2 * π * n * q / 3) := by dsimp [a]; ring
  rw [hrew]
  rcases eq_or_lt_of_le hq with rfl | hq_pos
  · simp [spinCalPhic]; positivity
  · have ht_exp : ∀ t : ℝ, 0 ≤ t → t * Real.exp (-t) ≤ 1 := fun t ht => by
      have h1 : t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
      calc t * Real.exp (-t) ≤ Real.exp t * Real.exp (-t) :=
            mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add]; simp
    rcases le_or_gt 1 q with hq1 | hq1
    · have hphi4 : spinCalPhic a q ≤ 4 := spinCalPhic_le_four hc hq
      have hexp1 : Real.exp (-(2 * π * n * q / 3)) ≤ (2 * π * n / 3)⁻¹ := by
        have h21 : 2 * π * n / 3 ≤ 2 * π * n * q / 3 := by
          calc 2 * π * n / 3 = (2 * π * n / 3) * 1 := by ring
            _ ≤ (2 * π * n / 3) * q := mul_le_mul_of_nonneg_left hq1 (by positivity)
            _ = 2 * π * n * q / 3 := by ring
        have h3 : 2 * π * n * q / 3 ≤ Real.exp (2 * π * n * q / 3) := by
          linarith [Real.add_one_le_exp (2 * π * n * q / 3)]
        rw [Real.exp_neg]
        exact inv_anti₀ (by positivity) (h21.trans h3)
      have hinv1 : (2 * π * n / 3)⁻¹ ≤ 1 / n := by
        rw [inv_le_comm₀ (by positivity) (by positivity)]
        have : (1 / n)⁻¹ = n := by simp
        rw [this]
        nlinarith [Real.pi_gt_three]
      calc Real.exp (-(2 * π * n * q / 3)) * spinCalPhic a q
          ≤ (1 / n) * 4 := mul_le_mul (hexp1.trans hinv1) hphi4 (spinCalPhic_nonneg_all ha2.le q) (by positivity)
        _ = 4 / n := by ring
    · obtain ⟨hf2, hf1⟩ := spinCalFc_lower_small hc hq_pos hq1
      have hf1' : (1 / 2 : ℝ) * min (π * n * q / 3) 1 ≤
          1 - Real.exp (-π * (12 * a) * (1 + spinGamma a) * q / 3) := hf1
      have hf2' : (1 / 2 : ℝ) * q ≤
          1 - Real.exp (-π * (12 * a) * (1 - spinGamma a) * q / 3) := hf2
      have hfc_pos : 0 < spinCalFc a q := spinCalFc_pos_of_pos ha2 hq_pos
      have ht_le : Real.tanh (q / 2) ^ 2 ≤ q ^ 2 / 4 := by
        have h0 : 0 ≤ Real.tanh (q / 2) := spinTanh_nonneg (half_pos hq_pos).le
        have h1 : Real.tanh (q / 2) ≤ q / 2 := spinTanh_half_le_half hq_pos.le
        nlinarith
      by_cases hpn : π * n * q / 3 ≤ 1
      · rw [min_eq_left hpn] at hf1'
        have hfc_ge : (π * n / 12) * q ^ 2 ≤ spinCalFc a q := by
          unfold spinCalFc
          have heq : (1 / 2 : ℝ) * (π * n * q / 3) * ((1 / 2 : ℝ) * q) = (π * n / 12) * q ^ 2 := by ring
          rw [← heq]
          have hb0 : 0 ≤ (1 / 2 : ℝ) * (π * n * q / 3) := by positivity
          exact mul_le_mul hf1' hf2' (mul_nonneg (by norm_num) hq_pos.le) (by linarith [hf1'])
        have hfc_ge_pos : 0 < (π * n / 12) * q ^ 2 := by positivity
        have hphi_bd : spinCalPhic a q ≤ 3 / (π * n) := by
          unfold spinCalPhic
          simp only [hq_pos.ne', ↓reduceIte]
          have hdiv : (q ^ 2 / 4) / ((π * n / 12) * q ^ 2) = 3 / (π * n) := by
            field_simp [hq_pos.ne', Real.pi_pos.ne', hn0.ne']; ring
          conv_rhs => rw [← hdiv]
          exact div_le_div₀ (by positivity) ht_le hfc_ge_pos hfc_ge
        have hexp_le1 : Real.exp (-(2 * π * n * q / 3)) ≤ 1 :=
          Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
        have h3n : 3 / (π * n) ≤ 4 / n := by
          rw [div_le_div_iff₀ (by positivity) hn0]
          nlinarith [Real.pi_gt_three]
        exact (mul_le_mul hexp_le1 hphi_bd (spinCalPhic_nonneg_all ha2.le q) zero_le_one).trans
          ((one_mul _).le.trans h3n)
      · push Not at hpn
        rw [min_eq_right hpn.le, mul_one] at hf1'
        have hfc_ge : (1 / 4 : ℝ) * q ≤ spinCalFc a q := by
          unfold spinCalFc
          have heq : (1 / 2 : ℝ) * ((1 / 2 : ℝ) * q) = (1 / 4 : ℝ) * q := by ring
          rw [← heq]
          exact mul_le_mul hf1' hf2' (mul_nonneg (by norm_num) hq_pos.le) (by linarith [hf1'])
        have hphi_bd : spinCalPhic a q ≤ q := by
          unfold spinCalPhic
          simp only [hq_pos.ne', ↓reduceIte]
          have hdiv : (q ^ 2 / 4) / ((1 / 4 : ℝ) * q) = q := by field_simp [hq_pos.ne']
          conv_rhs => rw [← hdiv]
          exact div_le_div₀ (by positivity) ht_le (by positivity) hfc_ge
        have hq_exp : Real.exp (-(2 * π * n * q / 3)) * q ≤ 4 / n := by
          have halg : Real.exp (-(2 * π * n * q / 3)) * q =
              (3 / (2 * π * n)) * ((2 * π * n * q / 3) * Real.exp (-(2 * π * n * q / 3))) := by
            field_simp [Real.pi_pos.ne', hn0.ne']
          rw [halg]
          have ht1 := ht_exp (2 * π * n * q / 3) (by positivity)
          have h3n : 3 / (2 * π * n) ≤ 4 / n := by
            rw [div_le_div_iff₀ (by positivity) hn0]
            nlinarith [Real.pi_gt_three]
          exact (mul_le_of_le_one_right (by positivity) ht1).trans h3n
        exact (mul_le_mul_of_nonneg_left hphi_bd (Real.exp_pos _).le).trans hq_exp

lemma spinRc2_le_div_n :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ {c : ℝ}, 40 ≤ c →
      let a := (c - 1) / 12
      ∀ ξ d : ℝ, |d| ≤ ξ → spinRc2 a ξ d ≤ C₂ / (c - 1) := by
  let k0 : ℝ := spinAlpha1 / (2 * xiStar)
  let K0 : ℝ := (1 + xiStar ^ 2) / spinCalPhi xiStar ^ 2 * Real.exp (k0 ^ 2 / 4)
  have hphi_pos : 0 < spinCalPhi xiStar := spinCalPhi_pos' xiStar_pos
  have hK0_pos : 0 < K0 := by dsimp [K0]; positivity
  refine ⟨K0 * 16, by positivity, fun {c} hc ξ d hd => ?_⟩
  let n := c - 1
  let a := n / 12
  have ha2 : 2 < a := by dsimp [a, n]; linarith
  have hn0 : 0 < n := by dsimp [n]; linarith
  have hxd_p : 0 ≤ ξ + d := by linarith [abs_le.mp hd]
  have hxd_m : 0 ≤ ξ - d := by linarith [abs_le.mp hd]
  have hpref : (1 + xiStar ^ 2) / (1 + d ^ 2) / spinCalPhi xiStar ^ 2 *
      Real.exp (-ξ ^ 2 / spinSigma0 ^ 2 - spinAlpha1 * (d ^ 2 - xiStar ^ 2) / (2 * xiStar) -
        (d ^ 2 - xiStar ^ 2) ^ 2) ≤ K0 := by
    have h1 : (1 + xiStar ^ 2) / (1 + d ^ 2) / spinCalPhi xiStar ^ 2 ≤
        (1 + xiStar ^ 2) / spinCalPhi xiStar ^ 2 := by
      refine div_le_div_of_nonneg_right ?_ (sq_nonneg _)
      exact div_le_self (by positivity) (by linarith [sq_nonneg d])
    have h2 : Real.exp (-ξ ^ 2 / spinSigma0 ^ 2 - spinAlpha1 * (d ^ 2 - xiStar ^ 2) / (2 * xiStar) -
        (d ^ 2 - xiStar ^ 2) ^ 2) ≤ Real.exp (k0 ^ 2 / 4) := by
      refine Real.exp_le_exp.mpr ?_
      set t := d ^ 2 - xiStar ^ 2
      have hsq1 : -ξ ^ 2 / spinSigma0 ^ 2 ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg ξ)) (sq_nonneg _)
      have hsq2 : 0 ≤ (t + k0 / 2) ^ 2 := sq_nonneg _
      have hid : -spinAlpha1 * t / (2 * xiStar) - t ^ 2 = -(t + k0 / 2) ^ 2 + k0 ^ 2 / 4 := by
        dsimp [k0]; field_simp [xiStar_pos.ne']; ring
      rw [show -ξ ^ 2 / spinSigma0 ^ 2 - spinAlpha1 * t / (2 * xiStar) - t ^ 2 =
          (-ξ ^ 2 / spinSigma0 ^ 2) + (-spinAlpha1 * t / (2 * xiStar) - t ^ 2) by ring, hid]
      linarith [hsq1, hsq2]
    exact mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
  let q := ξ - |d|
  have hq_nn : 0 ≤ q := sub_nonneg.mpr hd
  have hpair : spinCalPhic a (ξ + d) * spinCalPhic a (ξ - d) ≤ 4 * spinCalPhic a q := by
    rcases le_total 0 d with hd0 | hd0
    · have hq_eq : q = ξ - d := by dsimp [q]; rw [abs_of_nonneg hd0]
      rw [hq_eq]
      exact mul_le_mul_of_nonneg_right (spinCalPhic_le_four hc hxd_p)
        (spinCalPhic_nonneg_all ha2.le (ξ - d))
    · have hq_eq : q = ξ + d := by dsimp [q]; rw [abs_of_nonpos hd0]; ring
      rw [hq_eq, mul_comm]
      exact mul_le_mul_of_nonneg_right (spinCalPhic_le_four hc hxd_m)
        (spinCalPhic_nonneg_all ha2.le (ξ + d))
  have hq_exp := exp_mul_spinCalPhic_le_div_n hc hq_nn
  unfold spinRc2
  have hrew : Real.exp (-(12 * a) * (2 * π / 3) * (ξ - |d|)) * ((1 + xiStar ^ 2) / (1 + d ^ 2)) *
      (spinCalPhic a (ξ + d) * spinCalPhic a (ξ - d) / spinCalPhi xiStar ^ 2) *
      Real.exp (-ξ ^ 2 / spinSigma0 ^ 2 - spinAlpha1 * (d ^ 2 - xiStar ^ 2) / (2 * xiStar) -
        (d ^ 2 - xiStar ^ 2) ^ 2) =
      ((1 + xiStar ^ 2) / (1 + d ^ 2) / spinCalPhi xiStar ^ 2 *
        Real.exp (-ξ ^ 2 / spinSigma0 ^ 2 - spinAlpha1 * (d ^ 2 - xiStar ^ 2) / (2 * xiStar) -
          (d ^ 2 - xiStar ^ 2) ^ 2)) *
      (Real.exp (-12 * a * (2 * π / 3) * q) * (spinCalPhic a (ξ + d) * spinCalPhic a (ξ - d))) := by
    dsimp [q]; ring
  rw [hrew]
  have hprod_le : Real.exp (-12 * a * (2 * π / 3) * q) *
      (spinCalPhic a (ξ + d) * spinCalPhic a (ξ - d)) ≤ 16 / n := by
    calc Real.exp (-12 * a * (2 * π / 3) * q) * (spinCalPhic a (ξ + d) * spinCalPhic a (ξ - d))
        ≤ Real.exp (-12 * a * (2 * π / 3) * q) * (4 * spinCalPhic a q) :=
          mul_le_mul_of_nonneg_left hpair (Real.exp_pos _).le
      _ = 4 * (Real.exp (-12 * a * (2 * π / 3) * q) * spinCalPhic a q) := by ring
      _ ≤ 4 * (4 / n) := mul_le_mul_of_nonneg_left hq_exp (by norm_num)
      _ = 16 / n := by ring
  have hprod_nn : 0 ≤ Real.exp (-12 * a * (2 * π / 3) * q) *
      (spinCalPhic a (ξ + d) * spinCalPhic a (ξ - d)) :=
    mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (spinCalPhic_nonneg_all ha2.le _) (spinCalPhic_nonneg_all ha2.le _))
  calc ((1 + xiStar ^ 2) / (1 + d ^ 2) / spinCalPhi xiStar ^ 2 *
          Real.exp (-ξ ^ 2 / spinSigma0 ^ 2 - spinAlpha1 * (d ^ 2 - xiStar ^ 2) / (2 * xiStar) -
            (d ^ 2 - xiStar ^ 2) ^ 2)) *
        (Real.exp (-12 * a * (2 * π / 3) * q) * (spinCalPhic a (ξ + d) * spinCalPhic a (ξ - d)))
      ≤ K0 * (16 / n) := mul_le_mul hpref hprod_le hprod_nn hK0_pos.le
    _ = K0 * 16 / (c - 1) := by dsimp [n]; ring

end FormalResearch.ModularBootstrap.Spin
