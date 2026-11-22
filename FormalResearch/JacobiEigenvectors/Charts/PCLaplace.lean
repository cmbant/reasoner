module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Charts.PCOrigin

/-!
# Paper J, Layer 4 (phase B2, `U_pos`): the Laplace representation of `U(a, x)` and the decay of `U`

DLMF 12.5.1 for real `a > -1/2` and real `x`: `U(a,x) = e^{-x^2/4} / Gamma(1/2 + a) * int_0^infty t^{a-1/2} e^{-t^2/2 - x t} dt`
(`pcU_eq_laplace`).  Proved here from scratch in real variables: the moments `lapI c z = int_0^infty t^c e^{-t^2/2 - z t} dt` (`c > -1`) satisfy
`lapI c' = -lapI (c+1)` and `lapI (c+2) + z lapI (c+1) = (c+1) lapI c` (`hasDerivAt_lapI`, `lapI_ibp`), so `W = e^{-z^2/4} lapI (a-1/2) / Gamma(1/2+a)` solves
Weber's equation; its initial values at `0` are `pcU a 0, pcUD a 0` (Gamma duplication, `Charts/PCOrigin.lean`), and a real solution of Weber's equation is
determined by its initial data (`weber_unique`, from the Wronskians with `pcU, pcV` and `pc_wronsk`).  (The vendored lean-DLMF closure has the complex
version only in the module `EquationAndIntegrals`, whose import closure contains unproved upstream declarations; this module does not use it.)

Consequences (all proved): `pcU a x > 0` for `a > -1/2` (`pcU_pos_of_gt`), the polynomial-Gaussian bound
`|pcU a x| <= C (1+x)^n e^{-x^2/4}` for all real `a` and `x >= 0` (`pcU_decay_bound`, by the shifts `U(a-1) = x U(a) + (a+1/2) U(a+1)`), and `pcU a x -> 0` (`tendsto_pcU`).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.Charts

open MeasureTheory Set Real Filter Topology

/-- The moment `int_0^infty t^c e^{-t^2/2 - z t} dt`. -/
def lapI (c z : ℝ) : ℝ := ∫ t in Ioi (0 : ℝ), t ^ c * Real.exp (-t ^ 2 / 2 - z * t)

theorem exp_bound_aux (t z : ℝ) : -t ^ 2 / 2 - z * t ≤ -t ^ 2 / 4 + z ^ 2 := by
  nlinarith [sq_nonneg (t / 2 + z)]

theorem integrableOn_rpow_exp_sq4 {c : ℝ} (hc : -1 < c) :
    IntegrableOn (fun t : ℝ => t ^ c * Real.exp (-t ^ 2 / 4)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := c) (p := 2) (b := 1 / 4) hc (by norm_num) (by norm_num)
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
  simp only
  rw [show (t ^ (2 : ℝ)) = t ^ 2 from Real.rpow_two t]
  ring_nf

theorem continuousOn_lapIntegrand (c z : ℝ) :
    ContinuousOn (fun t : ℝ => t ^ c * Real.exp (-t ^ 2 / 2 - z * t)) (Ioi 0) := by
  refine ContinuousOn.mul (fun t ht => ?_) (by fun_prop)
  exact (Real.continuousAt_rpow_const t c (Or.inl (ne_of_gt ht))).continuousWithinAt

theorem integrableOn_lapIntegrand {c : ℝ} (hc : -1 < c) (z : ℝ) :
    IntegrableOn (fun t : ℝ => t ^ c * Real.exp (-t ^ 2 / 2 - z * t)) (Ioi 0) := by
  refine Integrable.mono' ((integrableOn_rpow_exp_sq4 hc).const_mul (Real.exp (z ^ 2)))
    ((continuousOn_lapIntegrand c z).aestronglyMeasurable measurableSet_Ioi) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
  have ht0 : 0 < t := ht
  rw [Real.norm_of_nonneg (by positivity)]
  calc t ^ c * Real.exp (-t ^ 2 / 2 - z * t) ≤ t ^ c * (Real.exp (z ^ 2) * Real.exp (-t ^ 2 / 4)) := by
        gcongr
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith [exp_bound_aux t z])
    _ = _ := by ring

/-- `d/dz lapI c z = - lapI (c+1) z`. -/
theorem hasDerivAt_lapI {c : ℝ} (hc : -1 < c) (z₀ : ℝ) : HasDerivAt (lapI c) (-lapI (c + 1) z₀) z₀ := by
  set R : ℝ := |z₀| + 1 with hR
  have hc1 : -1 < c + 1 := by linarith
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun (z : ℝ) (t : ℝ) => t ^ c * Real.exp (-t ^ 2 / 2 - z * t))
    (F' := fun (z : ℝ) (t : ℝ) => -(t ^ (c + 1) * Real.exp (-t ^ 2 / 2 - z * t)))
    (x₀ := z₀) (bound := fun t => Real.exp (R ^ 2) * (t ^ (c + 1) * Real.exp (-t ^ 2 / 4)))
    (s := Metric.ball z₀ 1) (Metric.ball_mem_nhds z₀ one_pos)
    (Eventually.of_forall fun z => (continuousOn_lapIntegrand c z).aestronglyMeasurable measurableSet_Ioi)
    (integrableOn_lapIntegrand hc z₀)
    ((continuousOn_lapIntegrand (c + 1) z₀).aestronglyMeasurable measurableSet_Ioi).neg
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht z hz => by
      have ht0 : 0 < t := ht
      have hzR : |z| ≤ R := by
        have h1 : |z - z₀| < 1 := by rwa [Metric.mem_ball, Real.dist_eq] at hz
        have := abs_sub_abs_le_abs_sub z z₀
        rw [hR]; linarith
      have hz2 : z ^ 2 ≤ R ^ 2 := by
        have := sq_abs z ▸ pow_le_pow_left₀ (abs_nonneg _) hzR 2
        exact this
      rw [norm_neg, Real.norm_of_nonneg (by positivity)]
      calc t ^ (c + 1) * Real.exp (-t ^ 2 / 2 - z * t)
          ≤ t ^ (c + 1) * (Real.exp (R ^ 2) * Real.exp (-t ^ 2 / 4)) := by
            gcongr
            rw [← Real.exp_add]
            exact Real.exp_le_exp.mpr (by linarith [exp_bound_aux t z])
        _ = _ := by ring)
    ((integrableOn_rpow_exp_sq4 hc1).const_mul _)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht z _ => by
      have ht0 : 0 < t := ht
      have h := (((hasDerivAt_id z).mul_const t).const_sub (-t ^ 2 / 2)).exp.const_mul (t ^ c)
      refine h.congr_deriv ?_
      rw [Real.rpow_add ht0, Real.rpow_one]
      simp only [id]
      ring)
  have hfun : (fun z => ∫ t in Ioi (0 : ℝ), t ^ c * Real.exp (-t ^ 2 / 2 - z * t)) = lapI c := rfl
  rw [hfun, integral_neg] at key
  exact key.2

/-- Integration by parts: `lapI (c+2) z + z lapI (c+1) z = (c+1) lapI c z`. -/
theorem lapI_ibp {c : ℝ} (hc : -1 < c) (z : ℝ) :
    lapI (c + 2) z + z * lapI (c + 1) z = (c + 1) * lapI c z := by
  have hc1 : -1 < c + 1 := by linarith
  have hc2 : -1 < c + 2 := by linarith
  have hc0 : 0 < c + 1 := by linarith
  set E : ℝ → ℝ := fun t => Real.exp (-t ^ 2 / 2 - z * t) with hE
  set g : ℝ → ℝ := fun t => t ^ (c + 1) * E t with hg
  set g' : ℝ → ℝ := fun t => (c + 1) * (t ^ c * E t) - (t ^ (c + 2) * E t) - z * (t ^ (c + 1) * E t) with hg'
  have hEd (t : ℝ) : HasDerivAt E (E t * (-t - z)) t := by
    have hi : HasDerivAt (fun w : ℝ => -w ^ 2 / 2 - z * w) (-t - z) t := by
      convert (((hasDerivAt_pow 2 t).div_const 2).neg.sub ((hasDerivAt_id t).const_mul z)) using 1
      · funext w; simp only [Pi.sub_apply, Pi.neg_apply, id]; ring
      · simp
    exact hi.exp
  have hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt g (g' t) t := fun t ht => by
    have ht0 : 0 < t := ht
    have hp := Real.hasDerivAt_rpow_const (x := t) (p := c + 1) (Or.inl ht0.ne')
    have h1 : t ^ (c + 1) = t ^ c * t := by rw [Real.rpow_add ht0, Real.rpow_one]
    have h2 : t ^ (c + 2) = t ^ c * t ^ 2 := by
      rw [Real.rpow_add ht0]; norm_num
    refine (hp.mul (hEd t)).congr_deriv ?_
    simp only [hg']
    rw [show c + 1 - 1 = c by ring, h1, h2]
    ring
  have hcont : ContinuousWithinAt g (Ici 0) 0 := by
    refine ContinuousAt.continuousWithinAt (ContinuousAt.mul ?_ (by fun_prop))
    exact Real.continuousAt_rpow_const 0 (c + 1) (Or.inr hc0.le)
  have hint : IntegrableOn g' (Ioi 0) :=
    (((integrableOn_lapIntegrand hc z).const_mul (c + 1)).sub
      (integrableOn_lapIntegrand hc2 z)).sub ((integrableOn_lapIntegrand hc1 z).const_mul z)
  have hlim : Tendsto g atTop (𝓝 0) := by
    have hb : Tendsto (fun t : ℝ => Real.exp (z ^ 2) * (t ^ (c + 1) * Real.exp (-(1 / 4) * t))) atTop (𝓝 0) := by
      have := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (c + 1) (1 / 4) (by norm_num)).const_mul (Real.exp (z ^ 2))
      rwa [mul_zero] at this
    refine squeeze_zero' ?_ ?_ hb
    · filter_upwards [eventually_gt_atTop 0] with t ht
      positivity
    · filter_upwards [eventually_ge_atTop 1] with t ht
      have ht0 : 0 < t := by linarith
      simp only [hg, hE]
      calc t ^ (c + 1) * Real.exp (-t ^ 2 / 2 - z * t)
          ≤ t ^ (c + 1) * (Real.exp (z ^ 2) * Real.exp (-(1 / 4) * t)) := by
            gcongr
            rw [← Real.exp_add]
            exact Real.exp_le_exp.mpr (by nlinarith [exp_bound_aux t z])
        _ = _ := by ring
  have hibp := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim
  have hg0 : g 0 = 0 := by
    simp only [hg]
    rw [Real.zero_rpow hc0.ne', zero_mul]
  rw [hg0, sub_zero] at hibp
  have hsplit : ∫ t in Ioi (0 : ℝ), g' t = (c + 1) * lapI c z - lapI (c + 2) z - z * lapI (c + 1) z := by
    have i0 := (integrableOn_lapIntegrand hc z).const_mul (c + 1)
    have i1 := integrableOn_lapIntegrand hc2 z
    have i2 := (integrableOn_lapIntegrand hc1 z).const_mul z
    have e1 := integral_sub i0 i1
    have e2 := integral_sub (i0.sub i1) i2
    simp only [Pi.sub_apply] at e1 e2
    simp only [lapI]
    rw [← integral_const_mul, ← integral_const_mul, ← e1, ← e2]
  rw [hsplit] at hibp
  linarith

/-- The moment at `0`: `lapI c 0 = 2^{(c+1)/2 - 1} Gamma((c+1)/2)`. -/
theorem lapI_zero {c : ℝ} (hc : -1 < c) : lapI c 0 = (2 : ℝ) ^ ((c + 1) / 2) / 2 * Real.Gamma ((c + 1) / 2) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := c) (b := 1 / 2) (by norm_num) hc (by norm_num)
  have e : lapI c 0 = ∫ x in Ioi (0 : ℝ), x ^ c * Real.exp (-(1 / 2) * x ^ (2 : ℝ)) := by
    unfold lapI
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    simp only [Real.rpow_two, zero_mul, sub_zero]
    congr 2; ring
  rw [e, h]
  have : ((1 : ℝ) / 2) ^ (-(c + 1) / 2) = (2 : ℝ) ^ ((c + 1) / 2) := by
    rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
    ring_nf
  rw [this]; ring

/-! ### Uniqueness for real Weber solutions and the representation -/

/-- A real solution of Weber's equation with zero initial data vanishes (Wronskians with `pcU, pcV`, and `pc_wronsk`). -/
theorem weber_unique {a : ℝ} {f f' : ℝ → ℝ} (hf : ∀ z, HasDerivAt f (f' z) z)
    (hf' : ∀ z, HasDerivAt f' ((z ^ 2 / 4 + a) * f z) z) (h0 : f 0 = 0) (h1 : f' 0 = 0) (z : ℝ) : f z = 0 := by
  have hW1 : ∀ w, HasDerivAt (fun w => f w * pcUD a w - f' w * pcU a w) 0 w := fun w =>
    (((hf w).mul (hasDerivAt_pcUD a w)).sub ((hf' w).mul (hasDerivAt_pcU a w))).congr_deriv (by ring)
  have hW2 : ∀ w, HasDerivAt (fun w => f w * pcVD a w - f' w * pcV a w) 0 w := fun w =>
    (((hf w).mul (hasDerivAt_pcVD a w)).sub ((hf' w).mul (hasDerivAt_pcV a w))).congr_deriv (by ring)
  have c1 := is_const_of_deriv_eq_zero (fun w => (hW1 w).differentiableAt) (fun w => (hW1 w).deriv) z 0
  have c2 := is_const_of_deriv_eq_zero (fun w => (hW2 w).differentiableAt) (fun w => (hW2 w).deriv) z 0
  simp only [h0, h1, zero_mul, sub_zero] at c1 c2
  have hw := pc_wronsk a z
  rw [deriv_pcU, deriv_pcV] at hw
  have hs : Real.sqrt (2 / π) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have : f z * Real.sqrt (2 / π) = 0 := by
    rw [← hw]
    linear_combination (pcU a z) * c2 - (pcV a z) * c1
  exact (mul_eq_zero.mp this).resolve_right hs

/-- DLMF 12.5.1, real form: `U(a,x) = e^{-x^2/4} / Gamma(1/2+a) * int_0^infty t^{a-1/2} e^{-t^2/2 - x t} dt` for `a > -1/2`. -/
theorem pcU_eq_laplace {a : ℝ} (ha : -1 / 2 < a) (x : ℝ) :
    pcU a x = Real.exp (-x ^ 2 / 4) * lapI (a - 1 / 2) x / Real.Gamma (1 / 2 + a) := by
  have hc : -1 < a - 1 / 2 := by linarith
  have hG : 0 < Real.Gamma (1 / 2 + a) := Real.Gamma_pos_of_pos (by linarith)
  set G := Real.Gamma (1 / 2 + a) with hGd
  set W : ℝ → ℝ := fun z => Real.exp (-z ^ 2 / 4) * lapI (a - 1 / 2) z / G with hW
  set W' : ℝ → ℝ := fun z => Real.exp (-z ^ 2 / 4) * (-lapI (a - 1 / 2 + 1) z - z / 2 * lapI (a - 1 / 2) z) / G with hW'
  have hE : ∀ z : ℝ, HasDerivAt (fun z : ℝ => Real.exp (-z ^ 2 / 4)) (Real.exp (-z ^ 2 / 4) * (-z / 2)) z := by
    intro z
    have : HasDerivAt (fun z : ℝ => -z ^ 2 / 4) (-z / 2) z := by
      convert ((hasDerivAt_pow 2 z).neg.div_const 4) using 1
      simp; ring
    exact this.exp
  have hd1 : ∀ z, HasDerivAt W (W' z) z := fun z => by
    have := (((hE z).mul (hasDerivAt_lapI hc z)).div_const G)
    refine this.congr_deriv ?_
    simp only [hW']; ring
  have hd2 : ∀ z, HasDerivAt W' ((z ^ 2 / 4 + a) * W z) z := fun z => by
    have hc1 : -1 < a - 1 / 2 + 1 := by linarith
    have i1 := hasDerivAt_lapI hc z
    have i2 := hasDerivAt_lapI hc1 z
    have inner : HasDerivAt (fun z => -lapI (a - 1 / 2 + 1) z - z / 2 * lapI (a - 1 / 2) z)
        (-(-lapI (a - 1 / 2 + 1 + 1) z) - (1 / 2 * lapI (a - 1 / 2) z + z / 2 * (-lapI (a - 1 / 2 + 1) z))) z :=
      i2.neg.sub (((hasDerivAt_id z).div_const 2).mul i1 |>.congr_deriv (by simp))
    have := (((hE z).mul inner).div_const G)
    refine this.congr_deriv ?_
    have hib := lapI_ibp hc z
    rw [show a - 1 / 2 + 2 = a - 1 / 2 + 1 + 1 by ring] at hib
    simp only [hW]
    generalize lapI (a - 1 / 2 + 1 + 1) z = L2 at *
    generalize lapI (a - 1 / 2 + 1) z = L1 at *
    generalize lapI (a - 1 / 2) z = L0 at *
    field_simp
    linear_combination 16 * hib
  -- initial values
  have hdup := Real.Gamma_mul_Gamma_add_half (a / 2 + 1 / 4)
  rw [show 2 * (a / 2 + 1 / 4) = 1 / 2 + a by ring, show a / 2 + 1 / 4 + 1 / 2 = 3 / 4 + a / 2 by ring,
    show 1 - (1 / 2 + a) = 1 - 2 * (a / 2 + 1 / 4) by ring] at hdup
  have hG1 : 0 < Real.Gamma (a / 2 + 1 / 4) := Real.Gamma_pos_of_pos (by linarith)
  have hG3 : 0 < Real.Gamma (3 / 4 + a / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hsπ : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  set T : ℝ := (2 : ℝ) ^ (-(a / 2 + 1 / 4)) with hT
  have hTp : 0 < T := Real.rpow_pos_of_pos (by norm_num) _
  have hTi : (2 : ℝ) ^ (a / 2 + 1 / 4) = T⁻¹ := by rw [hT, Real.rpow_neg (by norm_num), inv_inv]
  have hT2 : (2 : ℝ) ^ (1 - 2 * (a / 2 + 1 / 4)) = 2 * T ^ 2 := by
    rw [hT, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    rw [show (1 - 2 * (a / 2 + 1 / 4) : ℝ) = 1 + (-(a / 2 + 1 / 4)) * ((2 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_add (by norm_num), Real.rpow_one]
  have hs2 : Real.sqrt 2 = (2 : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow 2
  rw [hT2] at hdup
  have W0 : W 0 = pcU a 0 := by
    simp only [hW]
    rw [lapI_zero hc, pcU_zero, show (a - 1 / 2 + 1) / 2 = a / 2 + 1 / 4 by ring]
    simp only [zero_pow two_ne_zero, neg_zero, zero_div, Real.exp_zero, one_mul]
    rw [hTi, ← hT]
    rw [← hGd] at hdup
    generalize Real.Gamma (a / 2 + 1 / 4) = g1 at *
    generalize Real.Gamma (3 / 4 + a / 2) = g3 at *
    field_simp
    nlinarith [hdup]
  have W0' : W' 0 = pcUD a 0 := by
    simp only [hW']
    rw [lapI_zero (c := a - 1 / 2 + 1) (by linarith), pcUD_zero]
    have e1 : (a - 1 / 2 + 1 + 1) / 2 = 3 / 4 + a / 2 := by ring
    have p : (2 : ℝ) ^ ((a - 1 / 2 + 1 + 1) / 2) = T⁻¹ * Real.sqrt 2 := by
      rw [e1, show 3 / 4 + a / 2 = (a / 2 + 1 / 4) + 1 / 2 by ring, Real.rpow_add (by norm_num), hTi, hs2]
    have q : (2 : ℝ) ^ (-(a / 2 - 1 / 4)) = T * Real.sqrt 2 := by
      rw [show -(a / 2 - 1 / 4) = -(a / 2 + 1 / 4) + 1 / 2 by ring, Real.rpow_add (by norm_num), hs2]
    rw [p, q, e1, show 1 / 4 + a / 2 = a / 2 + 1 / 4 by ring]
    simp only [zero_pow two_ne_zero, neg_zero, zero_div, Real.exp_zero, one_mul, zero_mul, sub_zero]
    rw [← hGd] at hdup
    generalize Real.Gamma (a / 2 + 1 / 4) = g1 at *
    generalize Real.Gamma (3 / 4 + a / 2) = g3 at *
    have hs2p : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    field_simp
    nlinarith [hdup]
  have hunique := weber_unique (a := a) (f := fun z => W z - pcU a z) (f' := fun z => W' z - pcUD a z)
    (fun z => (hd1 z).sub (hasDerivAt_pcU a z))
    (fun z => ((hd2 z).sub (hasDerivAt_pcUD a z)).congr_deriv (by ring))
    (by simp [W0]) (by simp [W0']) x
  have : W x = pcU a x := by linarith
  rw [← this]

/-! ### Positivity and decay -/

theorem lapI_pos {c : ℝ} (hc : -1 < c) (z : ℝ) : 0 < lapI c z := by
  unfold lapI
  have hint := integrableOn_lapIntegrand hc z
  rw [setIntegral_pos_iff_support_of_nonneg_ae]
  · have : Function.support (fun t : ℝ => t ^ c * Real.exp (-t ^ 2 / 2 - z * t)) ∩ Ioi 0 = Ioi 0 := by
      ext t
      simp only [mem_inter_iff, Function.mem_support, mem_Ioi, and_iff_right_iff_imp]
      intro ht
      exact (mul_pos (Real.rpow_pos_of_pos ht _) (Real.exp_pos _)).ne'
    rw [this]
    simp
  · exact ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
      have : 0 < t := ht
      positivity
  · exact hint

/-- `U(a, x) > 0` for `a > -1/2` and all real `x` (DLMF 12.5.1). -/
theorem pcU_pos_of_gt {a : ℝ} (ha : -1 / 2 < a) (x : ℝ) : 0 < pcU a x := by
  rw [pcU_eq_laplace ha]
  have := lapI_pos (show -1 < a - 1 / 2 by linarith) x
  have hG : 0 < Real.Gamma (1 / 2 + a) := Real.Gamma_pos_of_pos (by linarith)
  positivity

theorem lapI_le_zero {c : ℝ} (hc : -1 < c) {z : ℝ} (hz : 0 ≤ z) : lapI c z ≤ lapI c 0 := by
  unfold lapI
  refine setIntegral_mono_on (integrableOn_lapIntegrand hc z) (integrableOn_lapIntegrand hc 0) measurableSet_Ioi ?_
  intro t ht
  have ht0 : 0 < t := ht
  simp only [zero_mul, sub_zero]
  gcongr
  nlinarith

theorem pcU_decay_base {a : ℝ} (ha : -1 / 2 < a) :
    ∃ C : ℝ, ∀ x : ℝ, 0 ≤ x → |pcU a x| ≤ C * (1 + x) ^ 0 * Real.exp (-x ^ 2 / 4) := by
  have hG : 0 < Real.Gamma (1 / 2 + a) := Real.Gamma_pos_of_pos (by linarith)
  refine ⟨lapI (a - 1 / 2) 0 / Real.Gamma (1 / 2 + a), fun x hx => ?_⟩
  rw [abs_of_pos (pcU_pos_of_gt ha x), pcU_eq_laplace ha, pow_zero, mul_one]
  have := lapI_le_zero (show -1 < a - 1 / 2 by linarith) hx
  rw [div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ hG.le
  nlinarith [Real.exp_pos (-x ^ 2 / 4)]

/-- The shift `U(a) = x U(a+1) + (a + 3/2) U(a+2)` (DLMF 12.8.1 at `a + 1`). -/
theorem pcU_three_term (a x : ℝ) : pcU a x = x * pcU (a + 1) x + (a + 3 / 2) * pcU (a + 2) x := by
  have h1 := pc_shift_U_dn (a + 1) x
  have h2 := pc_shift_U_up (a + 1) x
  rw [show a + 1 - 1 = a by ring] at h1
  rw [show a + 1 + 1 = a + 2 by ring] at h2
  linear_combination h1 - h2

theorem pcU_decay_bound (n : ℕ) : ∀ a : ℝ, -1 / 2 - n < a →
    ∃ C : ℝ, ∀ x : ℝ, 0 ≤ x → |pcU a x| ≤ C * (1 + x) ^ n * Real.exp (-x ^ 2 / 4) := by
  induction n with
  | zero =>
    intro a ha
    exact pcU_decay_base (by simpa using ha)
  | succ n ih =>
    intro a ha
    have h1 : -1 / 2 - (n : ℝ) < a + 1 := by push_cast at ha; linarith
    have h2 : -1 / 2 - (n : ℝ) < a + 2 := by push_cast at ha; linarith
    obtain ⟨C1, hC1⟩ := ih (a + 1) h1
    obtain ⟨C2, hC2⟩ := ih (a + 2) h2
    refine ⟨|C1| + |a + 3 / 2| * |C2|, fun x hx => ?_⟩
    have hE := Real.exp_pos (-x ^ 2 / 4)
    have hx1 : 1 ≤ 1 + x := by linarith
    have hp : 0 ≤ (1 + x) ^ n := by positivity
    have hp1 : (1 + x) ^ n ≤ (1 + x) ^ (n + 1) := pow_le_pow_right₀ hx1 (Nat.le_succ n)
    rw [pcU_three_term a x]
    calc |x * pcU (a + 1) x + (a + 3 / 2) * pcU (a + 2) x|
        ≤ |x * pcU (a + 1) x| + |(a + 3 / 2) * pcU (a + 2) x| := abs_add_le _ _
      _ = x * |pcU (a + 1) x| + |a + 3 / 2| * |pcU (a + 2) x| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hx]
      _ ≤ x * (C1 * (1 + x) ^ n * Real.exp (-x ^ 2 / 4)) + |a + 3 / 2| * (C2 * (1 + x) ^ n * Real.exp (-x ^ 2 / 4)) := by
          gcongr
          · exact hC1 x hx
          · exact hC2 x hx
      _ ≤ (|C1| + |a + 3 / 2| * |C2|) * (1 + x) ^ (n + 1) * Real.exp (-x ^ 2 / 4) := by
          have e1 : x * (C1 * (1 + x) ^ n * Real.exp (-x ^ 2 / 4)) ≤ |C1| * (1 + x) ^ (n + 1) * Real.exp (-x ^ 2 / 4) := by
            have : x * (1 + x) ^ n ≤ (1 + x) ^ (n + 1) := by rw [pow_succ]; nlinarith
            have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this (abs_nonneg C1)) hE.le
            calc x * (C1 * (1 + x) ^ n * Real.exp (-x ^ 2 / 4)) = (C1 * (x * (1 + x) ^ n)) * Real.exp (-x ^ 2 / 4) := by ring
              _ ≤ (|C1| * (x * (1 + x) ^ n)) * Real.exp (-x ^ 2 / 4) := by gcongr; exact le_abs_self _
              _ ≤ _ := by nlinarith [h]
          have e2 : |a + 3 / 2| * (C2 * (1 + x) ^ n * Real.exp (-x ^ 2 / 4)) ≤
              |a + 3 / 2| * |C2| * (1 + x) ^ (n + 1) * Real.exp (-x ^ 2 / 4) := by
            have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp1 (mul_nonneg (abs_nonneg (a + 3 / 2)) (abs_nonneg C2))) hE.le
            calc |a + 3 / 2| * (C2 * (1 + x) ^ n * Real.exp (-x ^ 2 / 4))
                = (|a + 3 / 2| * C2) * (1 + x) ^ n * Real.exp (-x ^ 2 / 4) := by ring
              _ ≤ (|a + 3 / 2| * |C2|) * (1 + x) ^ n * Real.exp (-x ^ 2 / 4) := by
                  gcongr; exact le_abs_self _
              _ ≤ _ := by nlinarith [h]
          nlinarith [e1, e2]

/-- `U(a, x) -> 0` as `x -> +infinity` for every real `a`. -/
theorem tendsto_pcU (a : ℝ) : Tendsto (pcU a) atTop (𝓝 0) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (-1 / 2 - a)
  obtain ⟨C, hC⟩ := pcU_decay_bound n a (by linarith)
  have hb : Tendsto (fun x : ℝ => |C| * 2 ^ n * (x ^ (n : ℝ) * Real.exp (-(1 / 4) * x))) atTop (𝓝 0) := by
    have := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n : ℝ) (1 / 4) (by norm_num)).const_mul (|C| * 2 ^ n)
    rwa [mul_zero] at this
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun x => abs_nonneg _) ?_ hb
  filter_upwards [eventually_ge_atTop 1] with x hx
  have hx0 : 0 ≤ x := by linarith
  refine (hC x hx0).trans ?_
  have h1 : (1 + x) ^ n ≤ 2 ^ n * x ^ (n : ℝ) := by
    rw [Real.rpow_natCast, ← mul_pow]
    exact pow_le_pow_left₀ (by linarith) (by linarith) n
  have h2 : Real.exp (-x ^ 2 / 4) ≤ Real.exp (-(1 / 4) * x) := Real.exp_le_exp.mpr (by nlinarith)
  calc C * (1 + x) ^ n * Real.exp (-x ^ 2 / 4) ≤ |C| * (1 + x) ^ n * Real.exp (-x ^ 2 / 4) := by
        gcongr; exact le_abs_self _
    _ ≤ |C| * (2 ^ n * x ^ (n : ℝ)) * Real.exp (-(1 / 4) * x) := by gcongr
    _ = _ := by ring

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.pcU_eq_laplace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pcU_eq_laplace

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.tendsto_pcU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tendsto_pcU

end FormalResearch.JacobiEigenvectors.Charts
