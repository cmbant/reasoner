module

public import FormalResearch.ModularBootstrap.FiveTerm.VirasoroG3Elem1

/-!
# Elementary integrals for the third jet (FIVE-0b), part 2

The integrals over `(δ, ∞)` of `1/(√(c(1+c)) s²)` and `g₄/s²` (`c = cosh πt`, `s = sinh πt`) in closed form,
with the behaviour of the primitives as `δ → 0⁺` relative to `1/sinh(πδ)`.  Proved.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

/-! ### `1/(√(c(1+c)) s²)` -/

/-- `1/(√(c(1+c)) sinh² πt)`. -/
noncomputable def qF (t : ℝ) : ℝ :=
  1 / (√(Real.cosh (π * t) * (1 + Real.cosh (π * t))) * Real.sinh (π * t) ^ 2)

/-- The `τ`-primitive for `qF`. -/
noncomputable def GF (τ : ℝ) : ℝ :=
  (-(√(1 + τ ^ 2)) / τ + τ * √(1 + τ ^ 2) / 2 - 5 / 2 * Real.arsinh τ) / (2 * √2 * π)

lemma hasDerivAt_GF {τ : ℝ} (hτ : τ ≠ 0) :
    HasDerivAt GF (1 / (2 * √2 * π) * ((1 - τ ^ 2) ^ 2 / (τ ^ 2 * √(1 + τ ^ 2)))) τ := by
  have hpi := Real.pi_pos
  have h2 : (0 : ℝ) < √2 := by positivity
  have hp : (0 : ℝ) < 1 + τ ^ 2 := by positivity
  have hr0 : 0 < √(1 + τ ^ 2) := Real.sqrt_pos.mpr hp
  have hr2 : √(1 + τ ^ 2) ^ 2 = 1 + τ ^ 2 := Real.sq_sqrt hp.le
  have hr : HasDerivAt (fun τ : ℝ => √(1 + τ ^ 2)) (2 * τ / (2 * √(1 + τ ^ 2))) τ := by
    have := ((hasDerivAt_pow 2 τ).const_add 1).sqrt hp.ne'
    simpa using this
  have hn := hr.neg.div (hasDerivAt_id τ) hτ
  have hm := ((hasDerivAt_id τ).mul hr).div_const 2
  have ha := (Real.hasDerivAt_arsinh τ).const_mul (5 / 2)
  have h := ((hn.add hm).sub ha).div_const (2 * √2 * π)
  unfold GF
  refine h.congr_deriv ?_
  simp only [id, Pi.neg_apply]
  field_simp
  nlinarith only [hr2]

/-- `QF(t) = GF(tanh(πt/2))`. -/
noncomputable def QF (t : ℝ) : ℝ := GF (Real.tanh (π * t / 2))

lemma qF_eq {t : ℝ} (ht : 0 < t) :
    qF t = (1 - Real.tanh (π * t / 2) ^ 2) ^ 3 /
      (4 * √2 * (Real.tanh (π * t / 2) ^ 2 * √(1 + Real.tanh (π * t / 2) ^ 2))) := by
  have hτ := tanh2_pos ht
  have hq := one_sub_tanh_sq_pos (π * t / 2)
  set τ := Real.tanh (π * t / 2) with hτdef
  have h2 : (0 : ℝ) < √2 := by positivity
  have hs2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hp : (0 : ℝ) < 1 + τ ^ 2 := by positivity
  have hr0 : 0 < √(1 + τ ^ 2) := Real.sqrt_pos.mpr hp
  have hr2 : √(1 + τ ^ 2) ^ 2 = 1 + τ ^ 2 := Real.sq_sqrt hp.le
  have hc : Real.cosh (π * t) = (1 + τ ^ 2) / (1 - τ ^ 2) := cosh_pi_tanh t
  have hs : Real.sinh (π * t) = 2 * τ / (1 - τ ^ 2) := sinh_pi_tanh t
  have hprod : Real.cosh (π * t) * (1 + Real.cosh (π * t)) = (√2 * √(1 + τ ^ 2) / (1 - τ ^ 2)) ^ 2 := by
    rw [hc, div_pow, mul_pow, hs2, hr2]
    field_simp
    ring
  unfold qF
  rw [hprod, Real.sqrt_sq (by positivity), hs]
  field_simp
  norm_num

lemma hasDerivAt_QF {t : ℝ} (ht : 0 < t) : HasDerivAt QF (qF t) t := by
  have hpi := Real.pi_pos
  have hτ := tanh2_pos ht
  have hq := one_sub_tanh_sq_pos (π * t / 2)
  have h := (hasDerivAt_GF hτ.ne').comp t (hd_tanh2 t)
  unfold QF
  refine h.congr_deriv ?_
  rw [qF_eq ht]
  have h2 : (0 : ℝ) < √2 := by positivity
  have hp : (0 : ℝ) < 1 + Real.tanh (π * t / 2) ^ 2 := by positivity
  have hr0 : 0 < √(1 + Real.tanh (π * t / 2) ^ 2) := Real.sqrt_pos.mpr hp
  field_simp
  norm_num

lemma qF_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ qF t := by
  unfold qF
  have := Real.cosh_pos (π * t)
  positivity

lemma tendsto_QF : Tendsto QF atTop (𝓝 ((-√2 + √2 / 2 - 5 / 2 * Real.arsinh 1) / (2 * √2 * π))) := by
  have hpi := Real.pi_pos
  have h2 : (0 : ℝ) < √2 := by positivity
  have h := tendsto_tanh_arg (k := 2) two_pos
  have hc : ContinuousAt GF 1 := by
    unfold GF
    fun_prop (disch := first | norm_num | positivity)
  have := hc.tendsto.comp h
  have e : GF 1 = (-√2 + √2 / 2 - 5 / 2 * Real.arsinh 1) / (2 * √2 * π) := by
    unfold GF
    have : √(1 + (1 : ℝ) ^ 2) = √2 := by norm_num
    rw [this]; ring
  rw [e] at this
  exact this

lemma int_qF {δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn qF (Ioi δ) ∧
      ∫ t in Ioi δ, qF t = (-√2 + √2 / 2 - 5 / 2 * Real.arsinh 1) / (2 * √2 * π) - QF δ :=
  int_of_prim (fun _ ht => hasDerivAt_QF ht) (fun _ ht => qF_nonneg ht) tendsto_QF hδ

lemma sing_QF : Tendsto (fun δ : ℝ => QF δ - (-1 / (√2 * π)) * (Real.sinh (π * δ))⁻¹) (𝓝[>] 0) (𝓝 0) := by
  have hpi := Real.pi_pos
  have h2 : (0 : ℝ) < √2 := by positivity
  set RF : ℝ → ℝ := fun τ =>
    (-τ - τ / (√(1 + τ ^ 2) + 1) + τ * √(1 + τ ^ 2) / 2 - 5 / 2 * Real.arsinh τ) / (2 * √2 * π) with hRF
  have hcont : Continuous fun δ : ℝ => RF (Real.tanh (π * δ / 2)) := by
    have ht : Continuous fun δ : ℝ => Real.tanh (π * δ / 2) := by
      simp_rw [Real.tanh_eq_sinh_div_cosh]
      exact Continuous.div (by fun_prop) (by fun_prop) (fun δ => (Real.cosh_pos _).ne')
    have hR : Continuous RF := by
      simp only [hRF]
      have hr : ∀ τ : ℝ, √(1 + τ ^ 2) + 1 ≠ 0 := fun τ => by positivity
      refine Continuous.div_const ?_ _
      have h1 : Continuous fun τ : ℝ => τ / (√(1 + τ ^ 2) + 1) :=
        Continuous.div continuous_id (by fun_prop) hr
      have h2 : Continuous fun τ : ℝ => τ * √(1 + τ ^ 2) / 2 := by fun_prop
      have h3 : Continuous fun τ : ℝ => 5 / 2 * Real.arsinh τ := continuous_const.mul Real.continuous_arsinh
      exact ((continuous_neg.sub h1).add h2).sub h3
    exact hR.comp ht
  have := tendsto_zero_of_cont hcont (by simp [hRF])
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ0 : 0 < δ := hδ
  have hτ := tanh2_pos hδ0
  have hq := one_sub_tanh_sq_pos (π * δ / 2)
  set τ := Real.tanh (π * δ / 2) with hτdef
  have hp : (0 : ℝ) < 1 + τ ^ 2 := by positivity
  have hr0 : 0 < √(1 + τ ^ 2) := Real.sqrt_pos.mpr hp
  have hr2 : √(1 + τ ^ 2) ^ 2 = 1 + τ ^ 2 := Real.sq_sqrt hp.le
  unfold QF GF
  rw [sinh_pi_tanh]
  simp only [hRF, ← hτdef]
  field_simp
  nlinarith only [hr2]

/-! ### `g₄/s²` -/

/-- `g₄(t)/sinh² πt`. -/
noncomputable def qG (t : ℝ) : ℝ := g4 t / Real.sinh (π * t) ^ 2

/-- The `y`-primitive for `qG` (`y = tanh(πt/4)`). -/
noncomputable def GG (y : ℝ) : ℝ :=
  (33 * y ^ 4 + 6 * y ^ 2 - 3) / (48 * y * (1 + y ^ 2) ^ 2) - y ^ 3 / 48 + y / 2 - 5 / 4 * Real.arctan y

lemma hasDerivAt_GG {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt GG ((1 - y ^ 2) ^ 5 / (16 * y ^ 2 * (1 + y ^ 2) ^ 3)) y := by
  have hp : (0 : ℝ) < 1 + y ^ 2 := by positivity
  have hnum : HasDerivAt (fun y : ℝ => 33 * y ^ 4 + 6 * y ^ 2 - 3)
      (33 * (4 * y ^ 3) + 6 * (2 * y)) y := by
    have h4 := (hasDerivAt_pow 4 y).const_mul 33
    have h2 := (hasDerivAt_pow 2 y).const_mul 6
    have := (h4.add h2).sub_const 3
    simpa using this
  have hden : HasDerivAt (fun y : ℝ => 48 * y * (1 + y ^ 2) ^ 2)
      (48 * (1 + y ^ 2) ^ 2 + 48 * y * (2 * (1 + y ^ 2) * (2 * y))) y := by
    have h1 : HasDerivAt (fun y : ℝ => (1 + y ^ 2) ^ 2) (2 * (1 + y ^ 2) * (2 * y)) y := by
      have := ((hasDerivAt_pow 2 y).const_add 1).fun_pow 2
      exact this.congr_deriv (by simp)
    have h2 : HasDerivAt (fun y : ℝ => 48 * y) 48 y := by
      simpa using (hasDerivAt_id y).const_mul 48
    exact (h2.fun_mul h1).congr_deriv (by simp)
  have hq := hnum.div hden (by positivity)
  have h3 : HasDerivAt (fun y : ℝ => y ^ 3 / 48) (3 * y ^ 2 / 48) y := by
    simpa using (hasDerivAt_pow 3 y).div_const 48
  have h4 : HasDerivAt (fun y : ℝ => y / 2) (1 / 2) y := by
    simpa using (hasDerivAt_id y).div_const 2
  have h5 := (Real.hasDerivAt_arctan y).const_mul (5 / 4)
  have h := ((hq.sub h3).add h4).sub h5
  unfold GG
  refine h.congr_deriv ?_
  field_simp
  ring

/-- `QG(t) = GG(tanh(πt/4))`. -/
noncomputable def QG (t : ℝ) : ℝ := GG (Real.tanh (π * t / 4))

lemma tanh4_pos {t : ℝ} (ht : 0 < t) : 0 < Real.tanh (π * t / 4) := by
  have := Real.pi_pos
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos (Real.sinh_pos_iff.mpr (by positivity)) (Real.cosh_pos _)

lemma qG_eq {t : ℝ} (ht : 0 < t) :
    qG t = π * (1 - Real.tanh (π * t / 4) ^ 2) ^ 6 /
      (64 * Real.tanh (π * t / 4) ^ 2 * (1 + Real.tanh (π * t / 4) ^ 2) ^ 3) := by
  have hy := tanh4_pos ht
  have hq := one_sub_tanh_sq_pos (π * t / 4)
  set y := Real.tanh (π * t / 4) with hydef
  have hc4 : Real.cosh (π * t / 4) ^ 2 = 1 / (1 - y ^ 2) := by
    have := one_sub_tanh_sq_eq (π * t / 4)
    rw [← hydef] at this
    rw [this]; field_simp
  have hc2 : Real.cosh (π * t / 2) = (1 + y ^ 2) / (1 - y ^ 2) := by
    rw [show π * t / 2 = 2 * (π * t / 4) by ring, cosh_two_mul_tanh]
  have hs2 : Real.sinh (π * t / 2) = 2 * y / (1 - y ^ 2) := by
    rw [show π * t / 2 = 2 * (π * t / 4) by ring, sinh_two_mul_tanh]
  have hs : Real.sinh (π * t) = 4 * y * (1 + y ^ 2) / (1 - y ^ 2) ^ 2 := by
    rw [sinh_double t, hs2, hc2]
    field_simp
    ring
  unfold qG g4
  rw [hc4, hc2, hs]
  have hp : (0 : ℝ) < 1 + y ^ 2 := by positivity
  field_simp
  ring

lemma hasDerivAt_QG {t : ℝ} (ht : 0 < t) : HasDerivAt QG (qG t) t := by
  have hpi := Real.pi_pos
  have hy := tanh4_pos ht
  have hq := one_sub_tanh_sq_pos (π * t / 4)
  have h := (hasDerivAt_GG hy.ne').comp t (hd_tanh4 t)
  unfold QG
  refine h.congr_deriv ?_
  rw [qG_eq ht]
  have hp : (0 : ℝ) < 1 + Real.tanh (π * t / 4) ^ 2 := by positivity
  field_simp
  ring

lemma qG_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ qG t := by
  unfold qG g4
  have h1 := Real.cosh_pos (π * t / 2)
  have h2 := Real.cosh_pos (π * t / 4)
  have := Real.pi_pos
  positivity

lemma tendsto_QG : Tendsto QG atTop (𝓝 (2 / 3 - 5 * π / 16)) := by
  have hpi := Real.pi_pos
  have h := tendsto_tanh_arg (k := 4) (by norm_num)
  have hc : ContinuousAt GG 1 := by
    unfold GG
    fun_prop (disch := first | norm_num | positivity)
  have := hc.tendsto.comp h
  have e : GG 1 = 2 / 3 - 5 * π / 16 := by
    unfold GG
    rw [Real.arctan_one]
    norm_num
    ring
  rw [e] at this
  exact this

lemma int_qG {δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn qG (Ioi δ) ∧ ∫ t in Ioi δ, qG t = 2 / 3 - 5 * π / 16 - QG δ :=
  int_of_prim (fun _ ht => hasDerivAt_QG ht) (fun _ ht => qG_nonneg ht) tendsto_QG hδ

lemma sing_QG : Tendsto (fun δ : ℝ => QG δ - (-1 / 4) * (Real.sinh (π * δ))⁻¹) (𝓝[>] 0) (𝓝 0) := by
  have hpi := Real.pi_pos
  set RG : ℝ → ℝ := fun y =>
    y * (y ^ 4 + 10 * y ^ 2 + 1) / (16 * (1 + y ^ 2) ^ 2) - y ^ 3 / 48 + y / 2 - 5 / 4 * Real.arctan y with hRG
  have hcont : Continuous fun δ : ℝ => RG (Real.tanh (π * δ / 4)) := by
    have ht : Continuous fun δ : ℝ => Real.tanh (π * δ / 4) := by
      simp_rw [Real.tanh_eq_sinh_div_cosh]
      exact Continuous.div (by fun_prop) (by fun_prop) (fun δ => (Real.cosh_pos _).ne')
    have hR : Continuous RG := by
      simp only [hRG]
      have : ∀ y : ℝ, 16 * (1 + y ^ 2) ^ 2 ≠ 0 := fun y => by positivity
      have h1 : Continuous fun y : ℝ => y * (y ^ 4 + 10 * y ^ 2 + 1) / (16 * (1 + y ^ 2) ^ 2) :=
        Continuous.div (by fun_prop) (by fun_prop) this
      have h3 : Continuous fun y : ℝ => 5 / 4 * Real.arctan y := continuous_const.mul Real.continuous_arctan
      exact ((h1.sub (by fun_prop)).add (by fun_prop)).sub h3
    exact hR.comp ht
  have := tendsto_zero_of_cont hcont (by simp [hRG])
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ0 : 0 < δ := hδ
  have hy := tanh4_pos hδ0
  have hq := one_sub_tanh_sq_pos (π * δ / 4)
  set y := Real.tanh (π * δ / 4) with hydef
  have hs2 : Real.sinh (π * δ / 2) = 2 * y / (1 - y ^ 2) := by
    rw [show π * δ / 2 = 2 * (π * δ / 4) by ring, sinh_two_mul_tanh]
  have hc2 : Real.cosh (π * δ / 2) = (1 + y ^ 2) / (1 - y ^ 2) := by
    rw [show π * δ / 2 = 2 * (π * δ / 4) by ring, cosh_two_mul_tanh]
  have hs : Real.sinh (π * δ) = 4 * y * (1 + y ^ 2) / (1 - y ^ 2) ^ 2 := by
    rw [sinh_double δ, hs2, hc2]
    field_simp
    ring
  have hp : (0 : ℝ) < 1 + y ^ 2 := by positivity
  unfold QG GG
  rw [hs]
  simp only [hRG, ← hydef]
  field_simp
  ring

end FormalResearch.ModularBootstrap.FiveTerm
