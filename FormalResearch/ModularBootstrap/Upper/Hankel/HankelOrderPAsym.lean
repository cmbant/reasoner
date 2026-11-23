module

public import FormalResearch.ModularBootstrap.Upper.Hankel.HankelOrderP
public import FormalResearch.ModularBootstrap.Upper.Hankel.HankelAsym
public import FormalResearch.ModularBootstrap.Upper.Design.HankelEpsDeriv

/-!
# Large-argument expansion of `H_p¹`, uniform on the upper half-plane

Source: `CFT/modular_bootstrap/paper/upper_transfer.tex`, proof of Lemma `FW-SD` (`fw:SDp`), step (2):
`H_p¹(z) = (2/(π z))^{1/2} e^{i(z - pπ/2 - π/4)} (1 + ε_p(z))` and the bound for `|ε_p|`;
plan item A3, order `p`.

Put `R_p(w) = K_p(w) e^{w} (2w)^{1/2}` (`hankelRp`), so `R_0 = hankelR`.  The three-term relation of `K_ν`
gives `R_{p+2} = R_p + (2(p+1)/w) R_{p+1}` and `R_1 = R_0 + R_0/(2w) - R_0'`; with
`‖R_0'(w)‖ ≤ √π/(8‖w‖²)` (`norm_deriv_hankelR_le'`) induction yields, for every `p`,

`‖R_p(w) - √π‖ ≤ C_p / ‖w‖`  on `Re w > 0`, `‖w‖ ≥ 1/2`   (`exists_norm_hankelRp_sub_le`).

With `ε_p(z) = (R_p(-i z) - √π)/√π`:
* `hankelOrd_expansion`: `H_p¹(z) = (2/(π z))^{1/2} e^{i(z - pπ/2 - π/4)} (1 + ε_p(z))` for `Im z > 0`;
* `exists_hankelEpsOrd_bounds`: `‖ε_p(z)‖ ≤ C_p/‖z‖` for `‖z‖ ≥ 1/2`, and the Cauchy bounds (discs of radius
  `Im z / 2`) `‖ε_p'(z)‖ ≤ C_p/(‖z‖ Im z)` (`‖z‖ ≥ 1`), `‖ε_p''(z)‖ ≤ C_p/(‖z‖ (Im z)²)` (`‖z‖ ≥ 2`),
  hence `‖z ε_p'‖ + ‖z² ε_p''‖ ≤ C_p/‖z‖` on every sector `Im z ≥ θ ‖z‖` (`hankelEpsOrd_sector_bound`);
* `exists_norm_hankelOrd_le`: `‖H_p¹(z)‖ ≤ C_p ‖z‖^{-1/2} e^{-Im z}` for `‖z‖ ≥ 1/2`.

The uniform-on-the-whole-sector form of the derivative bounds quoted in the TeX (disc of radius `|z|/2` on
the continued branch) is not formalised: the Cauchy discs here stay in `Im > 0`, which is what the
edge strip `Im b ≥ 1/4` needs.

All results are proved unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology Metric
open scoped Real Nat

namespace FormalResearch.ModularBootstrap.Upper.Hankel

/-! ### `‖R_0'‖` in terms of `‖w‖` -/

lemma norm_hankelRDeriv_le' {w : ℂ} (hw : 0 ≤ w.re) (hw0 : w ≠ 0) {t : ℝ} (ht : 0 < t) :
    ‖hankelRDeriv w t‖ ≤ (1 / ‖w‖ ^ 2) / 4 * (Real.exp (-t) * t ^ (1 / 2 : ℝ)) := by
  have h1 := norm_half_pow_sub_one_le (re_div_two_mul_nonneg hw ht.le)
  unfold hankelRDeriv
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_exp, norm_cpow_neg_half_ofReal ht]
  simp only [neg_re, ofReal_re, norm_neg, norm_inv, norm_pow, norm_div, Complex.norm_real,
    Real.norm_of_nonneg ht.le]
  have e1 : t ^ (1 / 2 : ℝ) = t ^ (-(1 / 2 : ℝ)) * t := by
    rw [← Real.rpow_add_one ht.ne']; norm_num
  have h3 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [norm_one, h3]
  have hb := Real.exp_pos (-t)
  have hb2 : 0 < t ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos ht _
  calc Real.exp (-t) * t ^ (-(1 / 2 : ℝ)) * (1 / 2 * ‖(1 + (t : ℂ) / (2 * w)) ^ (-(1 / 2 : ℂ) - 1)‖ *
        (t / 2 * (‖w‖ ^ 2)⁻¹))
      ≤ Real.exp (-t) * t ^ (-(1 / 2 : ℝ)) * (1 / 2 * 1 * (t / 2 * (‖w‖ ^ 2)⁻¹)) := by
        gcongr
    _ = (1 / ‖w‖ ^ 2) / 4 * (Real.exp (-t) * (t ^ (-(1 / 2 : ℝ)) * t)) := by ring
    _ = _ := by rw [e1]

/-- `‖R_0'(w)‖ ≤ √π / (8 ‖w‖²)` on `Re w > 0`. -/
theorem norm_deriv_hankelR_le' {w : ℂ} (hw : 0 < w.re) : ‖deriv hankelR w‖ ≤ √π / (8 * ‖w‖ ^ 2) := by
  have hw0 : w ≠ 0 := by intro h; rw [h] at hw; simp at hw
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  rw [(hasDerivAt_hankelR hw).deriv]
  have hg : IntegrableOn (fun t : ℝ => (1 / ‖w‖ ^ 2) / 4 * (Real.exp (-t) * t ^ (1 / 2 : ℝ))) (Ioi 0) :=
    integrableOn_gamma_three_half.const_mul _
  calc ‖∫ t in Ioi (0 : ℝ), hankelRDeriv w t‖
      ≤ ∫ t in Ioi (0 : ℝ), (1 / ‖w‖ ^ 2) / 4 * (Real.exp (-t) * t ^ (1 / 2 : ℝ)) := by
        refine norm_integral_le_of_norm_le hg ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact norm_hankelRDeriv_le' hw.le hw0 ht
    _ = √π / (8 * ‖w‖ ^ 2) := by
        rw [integral_const_mul, integral_gamma_three_half]
        field_simp
        ring

/-! ### The functions `R_p` -/

/-- `R_p(w) = K_p(w) e^{w} (2w)^{1/2}`. -/
noncomputable def hankelRp (p : ℕ) (w : ℂ) : ℂ :=
  besselKP (p : ℝ) w * Complex.exp w * (2 * w) ^ (1 / 2 : ℂ)

lemma re_pos_ne_zero {w : ℂ} (hw : 0 < w.re) : w ≠ 0 := by
  intro h; rw [h] at hw; simp at hw

lemma two_mul_mem_slitPlane {w : ℂ} (hw : 0 < w.re) : (2 * w) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; left; simp; exact hw

lemma cpow_half_mul_neg_half {w : ℂ} (hw : 0 < w.re) :
    (2 * w) ^ (-(1 / 2 : ℂ)) * (2 * w) ^ (1 / 2 : ℂ) = 1 := by
  have h2 : (2 * w) ≠ 0 := mul_ne_zero two_ne_zero (re_pos_ne_zero hw)
  rw [← Complex.cpow_add _ _ h2]; norm_num

lemma cpow_half_mul_self {w : ℂ} (hw : 0 < w.re) :
    (2 * w) ^ (1 / 2 : ℂ) * (2 * w) ^ (1 / 2 : ℂ) = 2 * w := by
  have h2 : (2 * w) ≠ 0 := mul_ne_zero two_ne_zero (re_pos_ne_zero hw)
  rw [← Complex.cpow_add _ _ h2]; norm_num

lemma cpow_half_ne_zero {w : ℂ} (hw : 0 < w.re) : (2 * w) ^ (1 / 2 : ℂ) ≠ 0 := by
  have h2 : (2 * w) ≠ 0 := mul_ne_zero two_ne_zero (re_pos_ne_zero hw)
  exact (Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).mpr h2

lemma besselKP_eq_hankelRp {w : ℂ} (hw : 0 < w.re) (p : ℕ) :
    besselKP (p : ℝ) w = Complex.exp (-w) * (2 * w) ^ (-(1 / 2 : ℂ)) * hankelRp p w := by
  unfold hankelRp
  have h1 : Complex.exp (-w) * Complex.exp w = 1 := by rw [← Complex.exp_add]; simp
  calc besselKP (p : ℝ) w = (Complex.exp (-w) * Complex.exp w) *
        ((2 * w) ^ (-(1 / 2 : ℂ)) * (2 * w) ^ (1 / 2 : ℂ)) * besselKP (p : ℝ) w := by
        rw [h1, cpow_half_mul_neg_half hw]; ring
    _ = _ := by ring

lemma hankelRp_zero {w : ℂ} (hw : 0 < w.re) : hankelRp 0 w = hankelR w := by
  unfold hankelRp
  have h1 : Complex.exp (-w) * Complex.exp w = 1 := by rw [← Complex.exp_add]; simp
  rw [Nat.cast_zero, besselKP_zero, besselK0_eq hw]
  calc Complex.exp (-w) * (2 * w) ^ (-(1 / 2 : ℂ)) * hankelR w * Complex.exp w * (2 * w) ^ (1 / 2 : ℂ)
      = (Complex.exp (-w) * Complex.exp w) *
        ((2 * w) ^ (-(1 / 2 : ℂ)) * (2 * w) ^ (1 / 2 : ℂ)) * hankelR w := by ring
    _ = _ := by rw [h1, cpow_half_mul_neg_half hw]; ring

/-- The recurrence `R_{p+2} = R_p + (2(p+1)/w) R_{p+1}`. -/
lemma hankelRp_add_two {w : ℂ} (hw : 0 < w.re) (p : ℕ) :
    hankelRp (p + 2) w = hankelRp p w + (2 * ((p : ℂ) + 1) / w) * hankelRp (p + 1) w := by
  have hrec := besselKP_add_one_sub (((p + 1 : ℕ) : ℝ)) hw
  have e1 : (((p + 1 : ℕ) : ℝ) + 1) = ((p + 2 : ℕ) : ℝ) := by push_cast; ring
  have e2 : (((p + 1 : ℕ) : ℝ) - 1) = (p : ℝ) := by push_cast; ring
  rw [e1, e2] at hrec
  unfold hankelRp
  have : besselKP ((p + 2 : ℕ) : ℝ) w = besselKP (p : ℝ) w +
      (2 * (((p + 1 : ℕ) : ℝ) : ℂ) / w) * besselKP (((p + 1 : ℕ) : ℝ)) w := by
    rw [← hrec]; ring
  rw [this]
  push_cast
  ring

/-- `R_1 = R_0 + R_0/(2w) - R_0'`. -/
lemma hankelRp_one {w : ℂ} (hw : 0 < w.re) :
    hankelRp 1 w = hankelR w + hankelR w / (2 * w) - deriv hankelR w := by
  have hw0 := re_pos_ne_zero hw
  have h2w : (2 * w) ≠ 0 := mul_ne_zero two_ne_zero hw0
  -- `K_0' = -K_1`
  have hK0 := hasDerivAt_besselKP 0 hw
  have hK1 : besselKP ((0 : ℝ) - 1) w = besselKP ((0 : ℝ) + 1) w := by
    unfold besselKP laplaceCosh
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only [zero_sub, zero_add, neg_mul, Real.cosh_neg]
  rw [hK1] at hK0
  have hK0' : HasDerivAt (besselKP 0) (-besselKP 1 w) w := by
    refine hK0.congr_deriv ?_
    rw [zero_add]; ring
  -- `K_0 = e^{-w} (2w)^{-1/2} R_0` near `w`
  let a : ℂ → ℂ := fun w => (2 * w) ^ (-(1 / 2 : ℂ))
  have hdiffR : DifferentiableAt ℂ hankelR w :=
    (differentiableOn_hankelR.differentiableAt (isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds hw))
  have hRd := hdiffR.hasDerivAt
  have hE : HasDerivAt (fun w : ℂ => Complex.exp (-w)) (-Complex.exp (-w)) w := by
    simpa using (hasDerivAt_id w).neg.cexp
  have hlin : HasDerivAt (fun w : ℂ => 2 * w) 2 w := by
    simpa using (hasDerivAt_id w).const_mul (2 : ℂ)
  have hA : HasDerivAt a (2 * (-(1 / 2 : ℂ)) * (2 * w) ^ (-(1 / 2 : ℂ) - 1)) w :=
    (hlin.cpow_const (c := -(1 / 2 : ℂ)) (two_mul_mem_slitPlane hw)).congr_deriv (by ring)
  have hG := (hE.mul hA).mul hRd
  have hev : (fun w => Complex.exp (-w) * a w * hankelR w) =ᶠ[𝓝 w] besselKP 0 := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw] with z hz
    rw [besselKP_zero, besselK0_eq hz]
  have hG' := hK0'.congr_of_eventuallyEq hev
  have hU := hG.unique hG'
  simp only [Pi.mul_apply] at hU
  have hsub : (2 * w) ^ (-(1 / 2 : ℂ) - 1) = a w / (2 * w) := by
    rw [Complex.cpow_sub _ _ h2w, Complex.cpow_one]
  have h1 : Complex.exp (-w) * Complex.exp w = 1 := by rw [← Complex.exp_add]; simp
  have h2 : a w * (2 * w) ^ (1 / 2 : ℂ) = 1 := cpow_half_mul_neg_half hw
  rw [hsub] at hU
  have hKone : besselKP 1 w = -((-Complex.exp (-w) * a w + Complex.exp (-w) *
      (2 * (-(1 / 2 : ℂ)) * (a w / (2 * w)))) * hankelR w + Complex.exp (-w) * a w * deriv hankelR w) := by
    linear_combination hU
  unfold hankelRp
  rw [Nat.cast_one, hKone]
  linear_combination ((hankelR w + hankelR w / (2 * w) - deriv hankelR w) * (a w * (2 * w) ^ (1 / 2 : ℂ))) * h1 +
    (hankelR w + hankelR w / (2 * w) - deriv hankelR w) * h2

/-! ### The bound `‖R_p(w) - √π‖ ≤ C_p/‖w‖` -/

/-- `‖R_p(w) - √π‖ ≤ C/‖w‖` on `Re w > 0`, `‖w‖ ≥ 1/2`. -/
def RBound (p : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, 0 < w.re → 1 / 2 ≤ ‖w‖ →
    ‖hankelRp p w - ((√π : ℝ) : ℂ)‖ ≤ C / ‖w‖

lemma rbound_zero : RBound 0 := by
  refine ⟨√π / 4, by positivity, fun w hw hn => ?_⟩
  have hw0 := re_pos_ne_zero hw
  have hwpos : 0 < ‖w‖ := by linarith
  rw [hankelRp_zero hw]
  refine (norm_hankelR_sub_le hw.le hw0).trans (le_of_eq ?_)
  field_simp

lemma rbound_one : RBound 1 := by
  refine ⟨√π, Real.sqrt_nonneg _, fun w hw hn => ?_⟩
  have hw0 := re_pos_ne_zero hw
  have hwpos : 0 < ‖w‖ := by linarith
  have h0 := norm_hankelR_sub_le hw.le hw0
  have h1 := norm_hankelR_le hw.le
  have h2 := norm_deriv_hankelR_le' hw
  have eq : hankelRp 1 w - ((√π : ℝ) : ℂ) =
      (hankelR w - ((√π : ℝ) : ℂ)) + hankelR w / (2 * w) - deriv hankelR w := by
    rw [hankelRp_one hw]; ring
  rw [eq]
  have n1 : ‖hankelR w / (2 * w)‖ ≤ √π / (2 * ‖w‖) := by
    have h3 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [norm_div, norm_mul, h3]
    exact div_le_div_of_nonneg_right h1 (by positivity)
  have h8 : √π / (8 * ‖w‖ ^ 2) ≤ √π / (4 * ‖w‖) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have := Real.sqrt_nonneg π
    nlinarith [mul_nonneg this hwpos.le]
  calc ‖(hankelR w - ((√π : ℝ) : ℂ)) + hankelR w / (2 * w) - deriv hankelR w‖
      ≤ ‖hankelR w - ((√π : ℝ) : ℂ)‖ + ‖hankelR w / (2 * w)‖ + ‖deriv hankelR w‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ √π / (4 * ‖w‖) + √π / (2 * ‖w‖) + √π / (4 * ‖w‖) := by
        gcongr
        exact h2.trans h8
    _ = √π / ‖w‖ := by field_simp; ring

lemma rbound_step {p : ℕ} (h0 : RBound p) (h1 : RBound (p + 1)) : RBound (p + 2) := by
  obtain ⟨C0, hC0, hb0⟩ := h0
  obtain ⟨C1, hC1, hb1⟩ := h1
  refine ⟨C0 + 2 * ((p : ℝ) + 1) * (√π + 2 * C1), by positivity, fun w hw hn => ?_⟩
  have hw0 := re_pos_ne_zero hw
  have hwpos : 0 < ‖w‖ := by linarith
  have hinv : 1 / ‖w‖ ≤ 2 := by
    rw [div_le_iff₀ hwpos]; linarith
  have eq : hankelRp (p + 2) w - ((√π : ℝ) : ℂ) = (hankelRp p w - ((√π : ℝ) : ℂ)) +
      (2 * ((p : ℂ) + 1) / w) * (((√π : ℝ) : ℂ) + (hankelRp (p + 1) w - ((√π : ℝ) : ℂ))) := by
    rw [hankelRp_add_two hw p]; ring
  rw [eq]
  have hc : ‖(2 * ((p : ℂ) + 1) / w)‖ = 2 * ((p : ℝ) + 1) / ‖w‖ := by
    have h3 : ‖(2 * ((p : ℂ) + 1))‖ = 2 * ((p : ℝ) + 1) := by
      have : (2 * ((p : ℂ) + 1)) = ((2 * ((p : ℝ) + 1) : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [norm_div, h3]
  have hs : ‖((√π : ℝ) : ℂ) + (hankelRp (p + 1) w - ((√π : ℝ) : ℂ))‖ ≤ √π + 2 * C1 := by
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    have := hb1 w hw hn
    have h5 : C1 / ‖w‖ ≤ 2 * C1 := by
      rw [div_eq_mul_one_div]; nlinarith [mul_le_mul_of_nonneg_left hinv hC1]
    linarith
  calc ‖(hankelRp p w - ((√π : ℝ) : ℂ)) +
        (2 * ((p : ℂ) + 1) / w) * (((√π : ℝ) : ℂ) + (hankelRp (p + 1) w - ((√π : ℝ) : ℂ)))‖
      ≤ ‖hankelRp p w - ((√π : ℝ) : ℂ)‖ +
        ‖(2 * ((p : ℂ) + 1) / w)‖ * ‖((√π : ℝ) : ℂ) + (hankelRp (p + 1) w - ((√π : ℝ) : ℂ))‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul]
    _ ≤ C0 / ‖w‖ + (2 * ((p : ℝ) + 1) / ‖w‖) * (√π + 2 * C1) := by
        gcongr
        · exact hb0 w hw hn
        · rw [hc]
    _ = _ := by field_simp

lemma rbound_pair (p : ℕ) : RBound p ∧ RBound (p + 1) := by
  induction p with
  | zero => exact ⟨rbound_zero, rbound_one⟩
  | succ n ih => exact ⟨ih.2, rbound_step ih.1 ih.2⟩

/-- For every `p`: `‖R_p(w) - √π‖ ≤ C_p/‖w‖` on `Re w > 0`, `‖w‖ ≥ 1/2`. -/
theorem exists_norm_hankelRp_sub_le (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, 0 < w.re → 1 / 2 ≤ ‖w‖ →
      ‖hankelRp p w - ((√π : ℝ) : ℂ)‖ ≤ C / ‖w‖ := (rbound_pair p).1

/-! ### The expansion -/

/-- The relative remainder `ε_p(z) = (R_p(-i z) - √π)/√π` of the large-argument expansion of `H_p¹`. -/
noncomputable def hankelEpsOrd (p : ℕ) (z : ℂ) : ℂ :=
  (hankelRp p (-I * z) - ((√π : ℝ) : ℂ)) / ((√π : ℝ) : ℂ)

lemma one_add_hankelEpsOrd (p : ℕ) (z : ℂ) :
    1 + hankelEpsOrd p z = hankelRp p (-I * z) / ((√π : ℝ) : ℂ) := by
  have hsp : ((√π : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  unfold hankelEpsOrd
  field_simp
  ring

/-- The leading factor `e^{-iπp/2} (2/(π z))^{1/2} e^{i(z - π/4)}` of the expansion. -/
noncomputable def hankelLeadingOrd (p : ℕ) (z : ℂ) : ℂ :=
  Complex.exp (-(I * (π : ℂ) * (p : ℂ) / 2)) * hankelLeading z

theorem hankelOrd_eq_leading_mul (p : ℕ) {z : ℂ} (hz : 0 < z.im) :
    hankelOrd p z = hankelLeadingOrd p z * (1 + hankelEpsOrd p z) := by
  have hw : 0 < (-I * z).re := by rw [neg_I_mul_re]; exact hz
  have hsp : ((√π : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hpf := hankel_prefactor hz
  unfold hankelOrd hankelLeadingOrd hankelLeading
  rw [besselKP_eq_hankelRp hw p, one_add_hankelEpsOrd]
  have e1 : -(-I * z) = I * z := by ring
  have e2 : Complex.exp (I * (z - (π : ℂ) / 4)) =
      Complex.exp (I * z) * Complex.exp (-(I * (π : ℂ) / 4)) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [e1, e2]
  have key : (2 / ((π : ℂ) * I)) * (2 * (-I * z)) ^ (-(1 / 2 : ℂ)) =
      (2 / ((π : ℂ) * z)) ^ (1 / 2 : ℂ) * Complex.exp (-(I * (π : ℂ) / 4)) / ((√π : ℝ) : ℂ) := by
    rw [eq_div_iff hsp]; exact hpf
  calc 2 / (↑π * I) * Complex.exp (-(I * (π : ℂ) * (p : ℂ) / 2)) *
        (Complex.exp (I * z) * (2 * (-I * z)) ^ (-(1 / 2 : ℂ)) * hankelRp p (-I * z))
      = Complex.exp (-(I * (π : ℂ) * (p : ℂ) / 2)) * Complex.exp (I * z) *
        ((2 / ((π : ℂ) * I)) * (2 * (-I * z)) ^ (-(1 / 2 : ℂ))) * hankelRp p (-I * z) := by ring
    _ = _ := by
        rw [key]
        field_simp

/-- **Large-argument expansion of `H_p¹`** (order `p`), in the shape required by `FWSDHypotheses.hankel_p`:
`H_p¹(z) = (2/(π z))^{1/2} e^{i(z - pπ/2 - π/4)} (1 + ε_p(z))` for every `z` with `Im z > 0`. -/
theorem hankelOrd_expansion (p : ℕ) {z : ℂ} (hz : 0 < z.im) :
    hankelOrd p z = (2 / ((π : ℂ) * z)) ^ (1 / 2 : ℂ) *
      Complex.exp (I * (z - (π : ℂ) * (p : ℂ) / 2 - (π : ℂ) / 4)) * (1 + hankelEpsOrd p z) := by
  rw [hankelOrd_eq_leading_mul p hz]
  unfold hankelLeadingOrd hankelLeading
  have : Complex.exp (-(I * (π : ℂ) * (p : ℂ) / 2)) * ((2 / ((π : ℂ) * z)) ^ (1 / 2 : ℂ) *
      Complex.exp (I * (z - (π : ℂ) / 4))) = (2 / ((π : ℂ) * z)) ^ (1 / 2 : ℂ) *
      Complex.exp (I * (z - (π : ℂ) * (p : ℂ) / 2 - (π : ℂ) / 4)) := by
    have : Complex.exp (I * (z - (π : ℂ) * (p : ℂ) / 2 - (π : ℂ) / 4)) =
        Complex.exp (-(I * (π : ℂ) * (p : ℂ) / 2)) * Complex.exp (I * (z - (π : ℂ) / 4)) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [this]; ring
  rw [this]

/-! ### Holomorphy and bounds -/

lemma differentiableOn_hankelRp (p : ℕ) : DifferentiableOn ℂ (hankelRp p) {w : ℂ | 0 < w.re} := by
  unfold hankelRp
  refine DifferentiableOn.mul (DifferentiableOn.mul (differentiableOn_besselKP (p : ℝ)) (by fun_prop)) ?_
  intro z hz
  exact ((differentiableAt_id.const_mul 2).cpow (differentiableAt_const _)
    (two_mul_mem_slitPlane (show 0 < z.re from hz))).differentiableWithinAt

lemma differentiableOn_hankelEpsOrd (p : ℕ) :
    DifferentiableOn ℂ (hankelEpsOrd p) {z : ℂ | 0 < z.im} := by
  unfold hankelEpsOrd
  refine DifferentiableOn.div_const (DifferentiableOn.sub_const ?_ _) _
  refine (differentiableOn_hankelRp p).comp (by fun_prop) ?_
  intro z hz
  simpa [neg_I_mul_re] using hz

lemma norm_neg_I_mul (z : ℂ) : ‖-I * z‖ = ‖z‖ := by simp

/-- `‖ε_p(z)‖ ≤ C/‖z‖` for `Im z > 0`, `‖z‖ ≥ 1/2`. -/
theorem exists_norm_hankelEpsOrd_le (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, 0 < z.im → 1 / 2 ≤ ‖z‖ → ‖hankelEpsOrd p z‖ ≤ C / ‖z‖ := by
  obtain ⟨C, hC, hb⟩ := exists_norm_hankelRp_sub_le p
  have hsp : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  refine ⟨C / √π, by positivity, fun z hz hn => ?_⟩
  have h := hb (-I * z) (by rw [neg_I_mul_re]; exact hz) (by rw [norm_neg_I_mul]; exact hn)
  rw [norm_neg_I_mul] at h
  unfold hankelEpsOrd
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hsp.le, div_le_iff₀ hsp]
  calc _ ≤ C / ‖z‖ := h
    _ = _ := by field_simp

lemma sphere_im_ge {z z' : ℂ} {r : ℝ} (h : z' ∈ sphere z r) : z.im - r ≤ z'.im := by
  have h1 : ‖z' - z‖ = r := by simpa [Complex.dist_eq] using h
  have h2 := Complex.abs_im_le_norm (z' - z)
  have h3 : (z' - z).im = z'.im - z.im := by simp
  rw [h3] at h2
  have := (abs_le.mp h2).1
  linarith

lemma sphere_norm_ge {z z' : ℂ} {r : ℝ} (h : z' ∈ sphere z r) : ‖z‖ - r ≤ ‖z'‖ := by
  have h1 : ‖z' - z‖ = r := by simpa [Complex.dist_eq] using h
  have := norm_sub_norm_le z z'
  rw [norm_sub_rev] at this
  linarith

lemma closedBall_im_pos {z z' : ℂ} (hz : 0 < z.im) (h : z' ∈ closedBall z (z.im / 2)) : 0 < z'.im := by
  have h1 : ‖z' - z‖ ≤ z.im / 2 := by simpa [Complex.dist_eq] using h
  have h2 := Complex.abs_im_le_norm (z' - z)
  have h3 : (z' - z).im = z'.im - z.im := by simp
  rw [h3] at h2
  have := (abs_le.mp h2).1
  linarith

/-- First Cauchy bound. -/
lemma norm_deriv_hankelEpsOrd_le (p : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ z : ℂ, 0 < z.im → 1 / 2 ≤ ‖z‖ → ‖hankelEpsOrd p z‖ ≤ C / ‖z‖) {z : ℂ} (hz : 0 < z.im)
    (hn : 1 ≤ ‖z‖) : ‖deriv (hankelEpsOrd p) z‖ ≤ 4 * C / (‖z‖ * z.im) := by
  have hr : 0 < z.im / 2 := by positivity
  have hzn : 0 < ‖z‖ := by linarith
  have hdiff : DifferentiableOn ℂ (hankelEpsOrd p) (closedBall z (z.im / 2)) :=
    (differentiableOn_hankelEpsOrd p).mono fun z' hz' => closedBall_im_pos hz hz'
  have hcl : DiffContOnCl ℂ (hankelEpsOrd p) (ball z (z.im / 2)) :=
    hdiff.diffContOnCl_of_closedBall
  have hC' : ∀ z' ∈ sphere z (z.im / 2), ‖hankelEpsOrd p z'‖ ≤ 2 * C / ‖z‖ := by
    intro z' hz'
    have him := sphere_im_ge hz'
    have hnorm := sphere_norm_ge hz'
    have hzim : z.im ≤ ‖z‖ := (Complex.im_le_norm z)
    have hz'n : ‖z‖ / 2 ≤ ‖z'‖ := by linarith
    refine (hb z' (by linarith) (by linarith)).trans ?_
    rw [div_le_div_iff₀ (by linarith) hzn]
    nlinarith
  have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hcl hC'
  refine this.trans (le_of_eq ?_)
  field_simp
  ring

/-- Second Cauchy bound. -/
lemma norm_deriv2_hankelEpsOrd_le (p : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ z : ℂ, 0 < z.im → 1 / 2 ≤ ‖z‖ → ‖hankelEpsOrd p z‖ ≤ C / ‖z‖) {z : ℂ} (hz : 0 < z.im)
    (hn : 2 ≤ ‖z‖) : ‖deriv (deriv (hankelEpsOrd p)) z‖ ≤ 32 * C / (‖z‖ * z.im ^ 2) := by
  have hr : 0 < z.im / 4 := by positivity
  have hzn : 0 < ‖z‖ := by linarith
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hder : DifferentiableOn ℂ (deriv (hankelEpsOrd p)) {z : ℂ | 0 < z.im} :=
    ((differentiableOn_hankelEpsOrd p).analyticOnNhd hopen).deriv.differentiableOn
  have hsub : closedBall z (z.im / 4) ⊆ {z : ℂ | 0 < z.im} := by
    intro z' hz'
    have h1 : ‖z' - z‖ ≤ z.im / 4 := by simpa [Complex.dist_eq] using hz'
    have h2 := Complex.abs_im_le_norm (z' - z)
    have h3 : (z' - z).im = z'.im - z.im := by simp
    rw [h3] at h2
    have := (abs_le.mp h2).1
    show 0 < z'.im
    linarith
  have hdiff : DifferentiableOn ℂ (deriv (hankelEpsOrd p)) (closedBall z (z.im / 4)) := hder.mono hsub
  have hcl : DiffContOnCl ℂ (deriv (hankelEpsOrd p)) (ball z (z.im / 4)) :=
    hdiff.diffContOnCl_of_closedBall
  have hC' : ∀ z' ∈ sphere z (z.im / 4), ‖deriv (hankelEpsOrd p) z'‖ ≤ 8 * C / (‖z‖ * z.im) := by
    intro z' hz'
    have him := sphere_im_ge hz'
    have hnorm := sphere_norm_ge hz'
    have hzim : z.im ≤ ‖z‖ := (Complex.im_le_norm z)
    have hz'n : 3 * ‖z‖ / 4 ≤ ‖z'‖ := by linarith
    have hz'i : 3 * z.im / 4 ≤ z'.im := by linarith
    have hz'p : 0 < z'.im := by linarith
    have hz'q : 0 < ‖z'‖ := by linarith
    have h1 := norm_deriv_hankelEpsOrd_le p hC hb (z := z') hz'p (by linarith)
    refine h1.trans ?_
    rw [div_le_div_iff₀ (mul_pos hz'q hz'p) (mul_pos hzn hz)]
    have : 9 / 16 * (‖z‖ * z.im) ≤ ‖z'‖ * z'.im := by
      have := mul_le_mul hz'n hz'i (by positivity) hz'q.le
      nlinarith
    nlinarith [mul_nonneg hC (mul_pos hzn hz).le]
  have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hcl hC'
  refine this.trans (le_of_eq ?_)
  field_simp
  ring

/-- **Bounds for `ε_p`**: `‖ε_p(z)‖ ≤ C/‖z‖` (`‖z‖ ≥ 1/2`), `‖ε_p'(z)‖ ≤ C/(‖z‖ Im z)` (`‖z‖ ≥ 1`),
`‖ε_p''(z)‖ ≤ C/(‖z‖ (Im z)²)` (`‖z‖ ≥ 2`), all for `Im z > 0`; `C = C_p` depends only on `p`. -/
theorem exists_hankelEpsOrd_bounds (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, 0 < z.im →
      (1 / 2 ≤ ‖z‖ → ‖hankelEpsOrd p z‖ ≤ C / ‖z‖) ∧
      (1 ≤ ‖z‖ → ‖deriv (hankelEpsOrd p) z‖ ≤ C / (‖z‖ * z.im)) ∧
      (2 ≤ ‖z‖ → ‖deriv (deriv (hankelEpsOrd p)) z‖ ≤ C / (‖z‖ * z.im ^ 2)) := by
  obtain ⟨C, hC, hb⟩ := exists_norm_hankelEpsOrd_le p
  refine ⟨32 * C, by positivity, fun z hz => ⟨fun hn => ?_, fun hn => ?_, fun hn => ?_⟩⟩
  · refine (hb z hz hn).trans ?_
    gcongr
    linarith
  · refine (norm_deriv_hankelEpsOrd_le p hC hb hz hn).trans ?_
    gcongr
    linarith
  · exact norm_deriv2_hankelEpsOrd_le p hC hb hz hn

/-- On every sector `Im z ≥ θ ‖z‖` (`0 < θ`), `‖z ε_p'(z)‖ + ‖z² ε_p''(z)‖ ≤ C_p (1/θ + 1/θ²)/‖z‖`
for `‖z‖ ≥ 2`. -/
theorem hankelEpsOrd_sector_bound (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (θ : ℝ) (z : ℂ), 0 < θ → θ * ‖z‖ ≤ z.im → 2 ≤ ‖z‖ →
      ‖z‖ * ‖deriv (hankelEpsOrd p) z‖ + ‖z‖ ^ 2 * ‖deriv (deriv (hankelEpsOrd p)) z‖ ≤
        C * (1 / θ + 1 / θ ^ 2) / ‖z‖ := by
  obtain ⟨C, hC, hb⟩ := exists_hankelEpsOrd_bounds p
  refine ⟨C, hC, fun θ z hθ hz hn => ?_⟩
  have hzn : 0 < ‖z‖ := by linarith
  have hzim : 0 < z.im := lt_of_lt_of_le (by positivity) hz
  obtain ⟨-, h1, h2⟩ := hb z hzim
  have h1 := h1 (by linarith)
  have h2 := h2 hn
  have e1 : ‖z‖ * (C / (‖z‖ * z.im)) = C / z.im := by field_simp
  have e2 : ‖z‖ ^ 2 * (C / (‖z‖ * z.im ^ 2)) = C * ‖z‖ / z.im ^ 2 := by field_simp
  have i1 : C / z.im ≤ C / (θ * ‖z‖) := by
    gcongr
  have i2 : C * ‖z‖ / z.im ^ 2 ≤ C * ‖z‖ / (θ * ‖z‖) ^ 2 := by
    gcongr
  calc ‖z‖ * ‖deriv (hankelEpsOrd p) z‖ + ‖z‖ ^ 2 * ‖deriv (deriv (hankelEpsOrd p)) z‖
      ≤ ‖z‖ * (C / (‖z‖ * z.im)) + ‖z‖ ^ 2 * (C / (‖z‖ * z.im ^ 2)) := by gcongr
    _ ≤ C / (θ * ‖z‖) + C * ‖z‖ / (θ * ‖z‖) ^ 2 := by rw [e1, e2]; exact add_le_add i1 i2
    _ = _ := by field_simp

/-- `1 + ε_p(z) ≠ 0` when `‖z‖ > C` (for the constant `C` of `exists_norm_hankelEpsOrd_le`). -/
lemma one_add_hankelEpsOrd_ne_zero {p : ℕ} {C : ℝ}
    (hb : ∀ z : ℂ, 0 < z.im → 1 / 2 ≤ ‖z‖ → ‖hankelEpsOrd p z‖ ≤ C / ‖z‖) {z : ℂ} (hz : 0 < z.im)
    (hn : max C (1 / 2) < ‖z‖) : 1 + hankelEpsOrd p z ≠ 0 := by
  have hC : C < ‖z‖ := lt_of_le_of_lt (le_max_left _ _) hn
  have h12 : 1 / 2 < ‖z‖ := lt_of_le_of_lt (le_max_right _ _) hn
  have hzn : 0 < ‖z‖ := by linarith
  have h := hb z hz h12.le
  have : ‖hankelEpsOrd p z‖ < 1 := by
    refine h.trans_lt ?_
    rw [div_lt_one hzn]; exact hC
  intro h0
  have h4 : hankelEpsOrd p z = -1 := by linear_combination h0
  have h5 : ‖hankelEpsOrd p z‖ = 1 := by rw [h4]; simp
  linarith

/-- **Uniform bound**: `‖H_p¹(z)‖ ≤ C_p ‖z‖^{-1/2} e^{-Im z}` for `Im z > 0`, `‖z‖ ≥ 1/2`. -/
theorem exists_norm_hankelOrd_le (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, 0 < z.im → 1 / 2 ≤ ‖z‖ →
      ‖hankelOrd p z‖ ≤ C * ‖z‖ ^ (-(1 / 2 : ℝ)) * Real.exp (-z.im) := by
  obtain ⟨C, hC, hb⟩ := exists_norm_hankelEpsOrd_le p
  refine ⟨√(2 / π) * (1 + 2 * C), by positivity, fun z hz hn => ?_⟩
  have hzn : 0 < ‖z‖ := by linarith
  rw [hankelOrd_eq_leading_mul p hz, norm_mul]
  unfold hankelLeadingOrd
  rw [norm_mul, norm_exp_phase, one_mul, norm_hankelLeading hz]
  have h1 : ‖1 + hankelEpsOrd p z‖ ≤ 1 + 2 * C := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_one]
    have h2 := hb z hz hn
    have h3 : C / ‖z‖ ≤ 2 * C := by
      rw [div_le_iff₀ hzn]; nlinarith
    linarith
  have hpos : 0 ≤ √(2 / π) * ‖z‖ ^ (-(1 / 2 : ℝ)) * Real.exp (-z.im) := by positivity
  calc √(2 / π) * ‖z‖ ^ (-(1 / 2 : ℝ)) * Real.exp (-z.im) * ‖1 + hankelEpsOrd p z‖
      ≤ √(2 / π) * ‖z‖ ^ (-(1 / 2 : ℝ)) * Real.exp (-z.im) * (1 + 2 * C) :=
        mul_le_mul_of_nonneg_left h1 hpos
    _ = _ := by ring

/-- info: 'FormalResearch.ModularBootstrap.Upper.Hankel.hankelOrd_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelOrd_expansion

/-- info: 'FormalResearch.ModularBootstrap.Upper.Hankel.exists_hankelEpsOrd_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_hankelEpsOrd_bounds

/-- info: 'FormalResearch.ModularBootstrap.Upper.Hankel.hankelEpsOrd_sector_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelEpsOrd_sector_bound

/-- info: 'FormalResearch.ModularBootstrap.Upper.Hankel.exists_norm_hankelOrd_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_norm_hankelOrd_le

end FormalResearch.ModularBootstrap.Upper.Hankel
