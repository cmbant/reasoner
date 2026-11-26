module

public import FormalResearch.ModularBootstrap.FiveTerm.VirasoroG1Main

/-!
# Elementary integrals for the third jet (FIVE-0b), part 1

For `t > 0` and `c = cosh πt`, `s = sinh πt`, `ch = cosh(πt/2)`: the integrals over `(δ, ∞)` of
`1/(c s²)`, `1/(ch s²)`, `c/s²`, `1/ch`, `1/((1+c) s²)` in closed form, together with the behaviour of their
primitives as `δ → 0⁺` relative to `1/sinh(πδ)`.  Proved.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

/-- Integral of a nonnegative derivative over `(δ, ∞)`. -/
lemma int_of_prim {q Q : ℝ → ℝ} {m : ℝ} (hd : ∀ t : ℝ, 0 < t → HasDerivAt Q (q t) t)
    (hq : ∀ t : ℝ, 0 < t → 0 ≤ q t) (hlim : Tendsto Q atTop (𝓝 m)) {δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn q (Ioi δ) ∧ ∫ t in Ioi δ, q t = m - Q δ := by
  have h1 : ∀ x ∈ Ici δ, HasDerivAt Q (q x) x := fun x hx => hd x (lt_of_lt_of_le hδ hx)
  have h2 : ∀ x ∈ Ioi δ, 0 ≤ q x := fun x hx => hq x (lt_trans hδ hx)
  exact ⟨integrableOn_Ioi_deriv_of_nonneg' h1 h2 hlim, integral_Ioi_of_hasDerivAt_of_nonneg' h1 h2 hlim⟩

lemma hd_sinh1 (t : ℝ) : HasDerivAt (fun t : ℝ => Real.sinh (π * t)) (π * Real.cosh (π * t)) t := by
  have h := (Real.hasDerivAt_sinh (π * t)).comp t ((hasDerivAt_id t).const_mul π)
  exact h.congr_deriv (by simp [mul_comm])

lemma hd_cosh1 (t : ℝ) : HasDerivAt (fun t : ℝ => Real.cosh (π * t)) (π * Real.sinh (π * t)) t := by
  have h := (Real.hasDerivAt_cosh (π * t)).comp t ((hasDerivAt_id t).const_mul π)
  exact h.congr_deriv (by simp [mul_comm])

lemma hd_sinh2 (t : ℝ) :
    HasDerivAt (fun t : ℝ => Real.sinh (π * t / 2)) (π / 2 * Real.cosh (π * t / 2)) t := by
  have := hasDerivAt_sinh_arg 2 t
  simpa [mul_comm] using this

lemma hd_cosh2 (t : ℝ) :
    HasDerivAt (fun t : ℝ => Real.cosh (π * t / 2)) (π / 2 * Real.sinh (π * t / 2)) t := by
  have := hasDerivAt_cosh_arg 2 t
  simpa [mul_comm] using this

lemma sinh_pos_of_pos {t : ℝ} (ht : 0 < t) : 0 < Real.sinh (π * t) :=
  Real.sinh_pos_iff.mpr (by have := Real.pi_pos; positivity)

lemma sinh2_pos_of_pos {t : ℝ} (ht : 0 < t) : 0 < Real.sinh (π * t / 2) :=
  Real.sinh_pos_iff.mpr (by have := Real.pi_pos; positivity)

lemma tendsto_sinh_arg_atTop {k : ℝ} (hk : 0 < k) :
    Tendsto (fun t : ℝ => Real.sinh (π * t / k)) atTop atTop := by
  have hpi := Real.pi_pos
  have : Tendsto (fun t : ℝ => π * t / k) atTop atTop :=
    (tendsto_id.const_mul_atTop (show 0 < π / k by positivity)).congr (fun t => by simp; ring)
  exact tendsto_sinh_atTop'.comp this

/-! ### `1/(c s²)` -/

/-- `1/(cosh πt sinh² πt)`. -/
noncomputable def qA (t : ℝ) : ℝ := 1 / (Real.cosh (π * t) * Real.sinh (π * t) ^ 2)

/-- Primitive of `qA`. -/
noncomputable def QA (t : ℝ) : ℝ := (-(Real.sinh (π * t))⁻¹ - Real.arctan (Real.sinh (π * t))) / π

lemma hasDerivAt_QA {t : ℝ} (ht : 0 < t) : HasDerivAt QA (qA t) t := by
  have hpi := Real.pi_pos
  have hs := sinh_pos_of_pos ht
  have hc := Real.cosh_pos (π * t)
  have h1 := ((hd_sinh1 t).inv hs.ne').neg
  have h2 := (Real.hasDerivAt_arctan (Real.sinh (π * t))).comp t (hd_sinh1 t)
  have h := (h1.sub h2).div_const π
  unfold QA
  refine h.congr_deriv ?_
  unfold qA
  have hcs : Real.cosh (π * t) ^ 2 = Real.sinh (π * t) ^ 2 + 1 := Real.cosh_sq _
  rw [add_comm (1 : ℝ) (Real.sinh (π * t) ^ 2), ← hcs]
  field_simp
  nlinarith only [hcs]

lemma qA_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ qA t := by
  unfold qA
  have := Real.cosh_pos (π * t)
  positivity

lemma tendsto_QA : Tendsto QA atTop (𝓝 (-1 / 2)) := by
  have hpi := Real.pi_pos
  have hs : Tendsto (fun t : ℝ => Real.sinh (π * t)) atTop atTop := by
    simpa using tendsto_sinh_arg_atTop (k := 1) one_pos
  have h1 : Tendsto (fun t : ℝ => (Real.sinh (π * t))⁻¹) atTop (𝓝 0) := hs.inv_tendsto_atTop
  have h2 : Tendsto (fun t : ℝ => Real.arctan (Real.sinh (π * t))) atTop (𝓝 (π / 2)) := tendsto_arctan_sinh
  have := ((h1.neg.sub h2).div_const π)
  have e : (-1 / 2 : ℝ) = (-0 - π / 2) / π := by field_simp; ring
  rw [e]
  exact this

lemma int_qA {δ : ℝ} (hδ : 0 < δ) : IntegrableOn qA (Ioi δ) ∧ ∫ t in Ioi δ, qA t = -1 / 2 - QA δ :=
  int_of_prim (fun _ ht => hasDerivAt_QA ht) (fun _ ht => qA_nonneg ht) tendsto_QA hδ

lemma tendsto_zero_of_cont {g : ℝ → ℝ} (hg : Continuous g) (h0 : g 0 = 0) :
    Tendsto g (𝓝[>] 0) (𝓝 0) := by
  have := hg.tendsto 0
  rw [h0] at this
  exact this.mono_left nhdsWithin_le_nhds

lemma sinh_arg_zero_eq : ∀ k : ℝ, Real.sinh (π * 0 / k) = 0 := fun k => by simp

lemma sing_QA : Tendsto (fun δ : ℝ => QA δ - (-1 / π) * (Real.sinh (π * δ))⁻¹) (𝓝[>] 0) (𝓝 0) := by
  have hpi := Real.pi_pos
  have hc : Continuous fun δ : ℝ => -(Real.arctan (Real.sinh (π * δ))) / π := by fun_prop
  have := tendsto_zero_of_cont hc (by simp)
  refine this.congr (fun δ => ?_)
  unfold QA
  field_simp
  ring

/-! ### `1/(ch s²)` -/

/-- `1/(cosh(πt/2) sinh² πt)`. -/
noncomputable def qB (t : ℝ) : ℝ := 1 / (Real.cosh (π * t / 2) * Real.sinh (π * t) ^ 2)

/-- The `w`-primitive for `qB`. -/
noncomputable def GB (w : ℝ) : ℝ := (-w⁻¹ - w / (2 * (1 + w ^ 2)) - 3 / 2 * Real.arctan w) / (2 * π)

lemma hasDerivAt_GB {w : ℝ} (hw : w ≠ 0) : HasDerivAt GB (1 / (2 * π) * (1 / (w ^ 2 * (1 + w ^ 2) ^ 2))) w := by
  have hpi := Real.pi_pos
  have h1 : HasDerivAt (fun w : ℝ => w⁻¹) (-(w ^ 2)⁻¹) w := hasDerivAt_inv hw
  have hpos : (0 : ℝ) < 1 + w ^ 2 := by positivity
  have h2 : HasDerivAt (fun w : ℝ => 2 * (1 + w ^ 2)) (2 * (0 + 2 * w)) w := by
    simpa using ((hasDerivAt_pow 2 w).const_add 1).const_mul 2
  have h3 := (hasDerivAt_id w).div h2 (by positivity)
  have h4 := Real.hasDerivAt_arctan w
  have h := (((h1.neg).sub h3).sub (h4.const_mul (3 / 2))).div_const (2 * π)
  unfold GB
  refine h.congr_deriv ?_
  simp only [id]
  field_simp
  ring

/-- `QB(t) = GB(sinh(πt/2))`. -/
noncomputable def QB (t : ℝ) : ℝ := GB (Real.sinh (π * t / 2))

lemma sinh_one_add_sq (t : ℝ) : 1 + Real.sinh (π * t / 2) ^ 2 = Real.cosh (π * t / 2) ^ 2 := by
  linarith [Real.cosh_sq (π * t / 2)]

lemma hasDerivAt_QB {t : ℝ} (ht : 0 < t) : HasDerivAt QB (qB t) t := by
  have hpi := Real.pi_pos
  have hw := sinh2_pos_of_pos ht
  have hch := Real.cosh_pos (π * t / 2)
  have h := (hasDerivAt_GB hw.ne').comp t (hd_sinh2 t)
  unfold QB
  refine h.congr_deriv ?_
  unfold qB
  rw [sinh_double t, sinh_one_add_sq]
  field_simp

lemma qB_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ qB t := by
  unfold qB
  have := Real.cosh_pos (π * t / 2)
  positivity

lemma tendsto_QB : Tendsto QB atTop (𝓝 (-3 / 8)) := by
  have hpi := Real.pi_pos
  have hs : Tendsto (fun t : ℝ => Real.sinh (π * t / 2)) atTop atTop := tendsto_sinh_arg_atTop two_pos
  have h1 : Tendsto (fun t : ℝ => (Real.sinh (π * t / 2))⁻¹) atTop (𝓝 0) := hs.inv_tendsto_atTop
  have h2 : Tendsto (fun t : ℝ => Real.sinh (π * t / 2) / (2 * (1 + Real.sinh (π * t / 2) ^ 2))) atTop
      (𝓝 0) := by
    have h3 : Tendsto (fun w : ℝ => w / (2 * (1 + w ^ 2))) atTop (𝓝 0) := by
      have h4 : Tendsto (fun w : ℝ => w⁻¹ / (2 * (w⁻¹ ^ 2 + 1))) atTop (𝓝 (0 / (2 * (0 ^ 2 + 1)))) :=
        Tendsto.div tendsto_inv_atTop_zero (tendsto_const_nhds.mul ((tendsto_inv_atTop_zero.pow 2).add
          tendsto_const_nhds)) (by norm_num)
      rw [show (0 : ℝ) / (2 * (0 ^ 2 + 1)) = 0 by norm_num] at h4
      refine h4.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with w hw
      field_simp
    exact h3.comp hs
  have h5 : Tendsto (fun t : ℝ => Real.arctan (Real.sinh (π * t / 2))) atTop (𝓝 (π / 2)) :=
    (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp hs
  have := ((h1.neg.sub h2).sub (h5.const_mul (3 / 2))).div_const (2 * π)
  have e : (-3 / 8 : ℝ) = (-0 - 0 - 3 / 2 * (π / 2)) / (2 * π) := by field_simp; ring
  rw [e]
  exact this

lemma int_qB {δ : ℝ} (hδ : 0 < δ) : IntegrableOn qB (Ioi δ) ∧ ∫ t in Ioi δ, qB t = -3 / 8 - QB δ :=
  int_of_prim (fun _ ht => hasDerivAt_QB ht) (fun _ ht => qB_nonneg ht) tendsto_QB hδ

lemma sing_QB : Tendsto (fun δ : ℝ => QB δ - (-1 / π) * (Real.sinh (π * δ))⁻¹) (𝓝[>] 0) (𝓝 0) := by
  have hpi := Real.pi_pos
  have hc : Continuous fun δ : ℝ =>
      (-(Real.sinh (π * δ / 2) / (Real.cosh (π * δ / 2) * (Real.cosh (π * δ / 2) + 1))) -
        Real.sinh (π * δ / 2) / (2 * Real.cosh (π * δ / 2) ^ 2) -
        3 / 2 * Real.arctan (Real.sinh (π * δ / 2))) / (2 * π) := by
    have h1 : ∀ δ : ℝ, Real.cosh (π * δ / 2) ≠ 0 := fun δ => (Real.cosh_pos _).ne'
    have h2 : ∀ δ : ℝ, Real.cosh (π * δ / 2) + 1 ≠ 0 := fun δ => by have := Real.cosh_pos (π * δ / 2); positivity
    refine Continuous.div_const (Continuous.sub (Continuous.sub ?_ ?_) ?_) _
    · exact (Continuous.div (by fun_prop) (by fun_prop) (fun δ => mul_ne_zero (h1 δ) (h2 δ))).neg
    · exact Continuous.div (by fun_prop) (by fun_prop) (fun δ => by have := h1 δ; positivity)
    · fun_prop
  have := tendsto_zero_of_cont hc (by simp)
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ0 : 0 < δ := hδ
  have hw := sinh2_pos_of_pos hδ0
  have hch := Real.cosh_pos (π * δ / 2)
  unfold QB GB
  rw [sinh_double δ, sinh_one_add_sq]
  have hrel : Real.sinh (π * δ / 2) ^ 2 = Real.cosh (π * δ / 2) ^ 2 - 1 := by
    linarith [Real.cosh_sq (π * δ / 2)]
  field_simp
  ring_nf
  simp only [mul_one_div]
  linear_combination (-2 * Real.cosh (π * δ / 2)) * hrel

/-! ### `c/s²` -/

/-- Primitive of `kern/π = cosh/sinh²`. -/
noncomputable def QC (t : ℝ) : ℝ := -(π * Real.sinh (π * t))⁻¹

lemma hasDerivAt_QC {t : ℝ} (ht : 0 < t) : HasDerivAt QC (kern t) t := hasDerivAt_neg_inv_sinh ht

lemma tendsto_QC : Tendsto QC atTop (𝓝 0) := by
  have hpi := Real.pi_pos
  have hs : Tendsto (fun t : ℝ => Real.sinh (π * t)) atTop atTop := by
    simpa using tendsto_sinh_arg_atTop (k := 1) one_pos
  have h1 : Tendsto (fun t : ℝ => π * Real.sinh (π * t)) atTop atTop := hs.const_mul_atTop hpi
  have h2 := h1.inv_tendsto_atTop.neg
  rw [neg_zero] at h2
  exact h2

lemma int_kern {δ : ℝ} (hδ : 0 < δ) : IntegrableOn kern (Ioi δ) ∧ ∫ t in Ioi δ, kern t = 0 - QC δ :=
  int_of_prim (fun _ ht => hasDerivAt_QC ht) (fun t _ => kern_nonneg t) tendsto_QC hδ

lemma sing_QC : Tendsto (fun δ : ℝ => QC δ - (-1 / π) * (Real.sinh (π * δ))⁻¹) (𝓝[>] 0) (𝓝 0) := by
  have hpi := Real.pi_pos
  refine tendsto_const_nhds.congr (fun δ => ?_)
  unfold QC
  field_simp
  ring

/-! ### `1/ch` -/

/-- `1/cosh(πt/2)`. -/
noncomputable def qD (t : ℝ) : ℝ := 1 / Real.cosh (π * t / 2)

/-- Primitive of `qD`. -/
noncomputable def QD (t : ℝ) : ℝ := 2 / π * Real.arctan (Real.sinh (π * t / 2))

lemma hasDerivAt_QD (t : ℝ) : HasDerivAt QD (qD t) t := by
  have hpi := Real.pi_pos
  have hch := Real.cosh_pos (π * t / 2)
  have h := ((Real.hasDerivAt_arctan (Real.sinh (π * t / 2))).comp t (hd_sinh2 t)).const_mul (2 / π)
  unfold QD
  refine h.congr_deriv ?_
  unfold qD
  rw [sinh_one_add_sq]
  field_simp

lemma tendsto_QD : Tendsto QD atTop (𝓝 1) := by
  have hpi := Real.pi_pos
  have hs : Tendsto (fun t : ℝ => Real.sinh (π * t / 2)) atTop atTop := tendsto_sinh_arg_atTop two_pos
  have h5 : Tendsto (fun t : ℝ => Real.arctan (Real.sinh (π * t / 2))) atTop (𝓝 (π / 2)) :=
    (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp hs
  have := h5.const_mul (2 / π)
  have e : (1 : ℝ) = 2 / π * (π / 2) := by field_simp
  rw [e]
  exact this

lemma int_qD {δ : ℝ} (hδ : 0 < δ) : IntegrableOn qD (Ioi δ) ∧ ∫ t in Ioi δ, qD t = 1 - QD δ :=
  int_of_prim (fun t _ => hasDerivAt_QD t) (fun t _ => by unfold qD; have := Real.cosh_pos (π * t / 2); positivity)
    tendsto_QD hδ

lemma tendsto_QD_zero : Tendsto QD (𝓝[>] 0) (𝓝 0) := by
  have hc : Continuous QD := by unfold QD; fun_prop
  exact tendsto_zero_of_cont hc (by simp [QD])

/-! ### `1/((1+c) s²)` -/

lemma one_sub_tanh_sq_eq (x : ℝ) : 1 - Real.tanh x ^ 2 = 1 / Real.cosh x ^ 2 := by
  have hc := Real.cosh_pos x
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp
  linarith [Real.cosh_sq x]

lemma one_sub_tanh_sq_pos (x : ℝ) : 0 < 1 - Real.tanh x ^ 2 := by
  rw [one_sub_tanh_sq_eq]; have := Real.cosh_pos x; positivity

lemma cosh_two_mul_tanh (x : ℝ) : Real.cosh (2 * x) = (1 + Real.tanh x ^ 2) / (1 - Real.tanh x ^ 2) := by
  have hc := Real.cosh_pos x
  rw [Real.cosh_two_mul, Real.tanh_eq_sinh_div_cosh]
  have h : Real.cosh x ^ 2 - Real.sinh x ^ 2 = 1 := by linarith [Real.cosh_sq x]
  field_simp
  nlinarith only [h]

lemma sinh_two_mul_tanh (x : ℝ) : Real.sinh (2 * x) = 2 * Real.tanh x / (1 - Real.tanh x ^ 2) := by
  have hc := Real.cosh_pos x
  rw [Real.sinh_two_mul, Real.tanh_eq_sinh_div_cosh]
  have h : Real.cosh x ^ 2 - Real.sinh x ^ 2 = 1 := by linarith [Real.cosh_sq x]
  field_simp
  linear_combination (Real.sinh x) * h

lemma hd_tanh2 (t : ℝ) : HasDerivAt (fun t : ℝ => Real.tanh (π * t / 2))
    (π / 2 * (1 - Real.tanh (π * t / 2) ^ 2)) t := by
  have h := hasDerivAt_tanh_arg 2 t
  refine h.congr_deriv ?_
  rw [one_sub_tanh_sq_eq]; ring

lemma hd_tanh4 (t : ℝ) : HasDerivAt (fun t : ℝ => Real.tanh (π * t / 4))
    (π / 4 * (1 - Real.tanh (π * t / 4) ^ 2)) t := by
  have h := hasDerivAt_tanh_arg 4 t
  refine h.congr_deriv ?_
  rw [one_sub_tanh_sq_eq]; ring

/-- `1/((1+cosh πt) sinh² πt)`. -/
noncomputable def qE (t : ℝ) : ℝ := 1 / ((1 + Real.cosh (π * t)) * Real.sinh (π * t) ^ 2)

/-- The `τ`-primitive for `qE`. -/
noncomputable def GE (τ : ℝ) : ℝ := (-τ⁻¹ - 2 * τ + τ ^ 3 / 3) / (4 * π)

lemma hasDerivAt_GE {τ : ℝ} (hτ : τ ≠ 0) :
    HasDerivAt GE (1 / (4 * π) * ((1 - τ ^ 2) ^ 2 / τ ^ 2)) τ := by
  have hpi := Real.pi_pos
  have h1 : HasDerivAt (fun τ : ℝ => τ⁻¹) (-(τ ^ 2)⁻¹) τ := hasDerivAt_inv hτ
  have h3 : HasDerivAt (fun τ : ℝ => τ ^ 3 / 3) (3 * τ ^ 2 / 3) τ := by
    simpa using (hasDerivAt_pow 3 τ).div_const 3
  have h := ((h1.neg.sub ((hasDerivAt_id τ).const_mul 2)).add h3).div_const (4 * π)
  unfold GE
  refine h.congr_deriv ?_
  field_simp
  ring

/-- `QE(t) = GE(tanh(πt/2))`. -/
noncomputable def QE (t : ℝ) : ℝ := GE (Real.tanh (π * t / 2))

lemma cosh_pi_tanh (t : ℝ) : Real.cosh (π * t) = (1 + Real.tanh (π * t / 2) ^ 2) / (1 - Real.tanh (π * t / 2) ^ 2) := by
  rw [← cosh_two_mul_tanh]; congr 1; ring

lemma sinh_pi_tanh (t : ℝ) : Real.sinh (π * t) = 2 * Real.tanh (π * t / 2) / (1 - Real.tanh (π * t / 2) ^ 2) := by
  rw [← sinh_two_mul_tanh]; congr 1; ring

lemma tanh2_pos {t : ℝ} (ht : 0 < t) : 0 < Real.tanh (π * t / 2) := by
  have := Real.pi_pos
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos (Real.sinh_pos_iff.mpr (by positivity)) (Real.cosh_pos _)

lemma hasDerivAt_QE {t : ℝ} (ht : 0 < t) : HasDerivAt QE (qE t) t := by
  have hpi := Real.pi_pos
  have hτ := tanh2_pos ht
  have hq := one_sub_tanh_sq_pos (π * t / 2)
  have h := (hasDerivAt_GE hτ.ne').comp t (hd_tanh2 t)
  unfold QE
  refine h.congr_deriv ?_
  unfold qE
  rw [cosh_pi_tanh, sinh_pi_tanh]
  field_simp
  ring

lemma qE_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ qE t := by
  unfold qE
  have := Real.cosh_pos (π * t)
  positivity

lemma tendsto_QE : Tendsto QE atTop (𝓝 (-2 / (3 * π))) := by
  have hpi := Real.pi_pos
  have h := tendsto_tanh_arg (k := 2) two_pos
  have h1 : Tendsto (fun t : ℝ => (Real.tanh (π * t / 2))⁻¹) atTop (𝓝 1⁻¹) := h.inv₀ one_ne_zero
  have := (((h1.neg.sub (h.const_mul 2)).add ((h.pow 3).div_const 3)).div_const (4 * π))
  have e : (-2 / (3 * π) : ℝ) = (-1⁻¹ - 2 * 1 + 1 ^ 3 / 3) / (4 * π) := by field_simp; norm_num
  rw [e]
  exact this

lemma int_qE {δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn qE (Ioi δ) ∧ ∫ t in Ioi δ, qE t = -2 / (3 * π) - QE δ :=
  int_of_prim (fun _ ht => hasDerivAt_QE ht) (fun _ ht => qE_nonneg ht) tendsto_QE hδ

lemma sing_QE : Tendsto (fun δ : ℝ => QE δ - (-1 / (2 * π)) * (Real.sinh (π * δ))⁻¹) (𝓝[>] 0) (𝓝 0) := by
  have hpi := Real.pi_pos
  have hc : Continuous fun δ : ℝ =>
      (-3 * Real.tanh (π * δ / 2) + Real.tanh (π * δ / 2) ^ 3 / 3) / (4 * π) := by
    have : Continuous fun δ : ℝ => Real.tanh (π * δ / 2) := by
      simp_rw [Real.tanh_eq_sinh_div_cosh]
      exact Continuous.div (by fun_prop) (by fun_prop) (fun δ => (Real.cosh_pos _).ne')
    fun_prop
  have := tendsto_zero_of_cont hc (by simp)
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ0 : 0 < δ := hδ
  have hτ := tanh2_pos hδ0
  have hq := one_sub_tanh_sq_pos (π * δ / 2)
  unfold QE GE
  rw [sinh_pi_tanh]
  field_simp
  ring

end FormalResearch.ModularBootstrap.FiveTerm
