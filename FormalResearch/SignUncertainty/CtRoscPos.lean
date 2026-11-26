module

public import Mathlib
public import FormalResearch.SignUncertainty.CtRoscMass

/-!
# `ct:dyadic` (4), `(ct:rosc)`: the positive lobe `∫_0^R w_R f_c` (piece `T5` of `CtRoscBook`)

`constant_terms_lower.tex`, `ct:dyadic` (4): "the lobe piece `0 ≤ 1 - W₆(u) ≤ 2(u/R)^{12}` integrates against `|Ψ̃(φ_c(u))| ≤ C e^{-c₀ u^{3/2}}` to `O(R^{-12})`".  Here the
pointwise decay is replaced by the mass bounds already in Lean: the total mass `∫|Re Ψ̃| ≤ 1 + 2 A r_∞` on `(0, u₁)` against the weight `2(u₁/R)^{12}`, and the deep-lobe
mass `∫_{x ≥ φ(u₁)} |Re Ψ̃| ≤ 8(e^{-5 (kφ(u₁))^{3/2}} + e^{-c/25}) + A r_∞` (`psi_abs_tail`) against the weight `≤ 1` on `(u₁, R)`.

All proved.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

/-- **The positive lobe** (`0 < u₁ ≤ R ≤ R_max`, `k φ(u₁) ≥ 1`):
`|∫_{(0,R)} w_R(u) f_c(u) du| ≤ 2(u₁/R)^{12}(1 + 2A r_∞) + 8(e^{-5(kφ(u₁))^{3/2}} + e^{-c/25}) + (φ(R) - φ(u₁)) r_∞`. -/
lemma pos_lobe_le {ε c C ρ M R u₁ : ℝ} {f : ℝ → ℝ} (X : CtRoscCtx ε c C ρ M f) (hR0 : 0 < R)
    (hRm : R ≤ ctRmax ctChartC1 c) (hu0 : 0 < u₁) (hu1 : u₁ ≤ R) (hk : 1 ≤ langerLobeK * ctPhiR ε c u₁) :
    |∫ u in Ioo 0 R, taperW R u * ctFr ε c f u| ≤
      2 * (u₁ / R) ^ 12 * (1 + 2 * langerRadius c * hankelRinf c) +
        (8 * (Real.exp (-5 * (langerLobeK * ctPhiR ε c u₁) ^ (3 / 2 : ℝ)) + Real.exp (-(1 / 25) * c)) +
          (ctPhiR ε c R - ctPhiR ε c u₁) * hankelRinf c) := by
  have hc0 := X.c_pos
  have hRmpos := X.H.Rm_pos
  have hT : Continuous (taperW R) := by unfold taperW taperX; fun_prop
  have hTb : ∀ u, |taperW R u| ≤ 1 := fun u => by
    rw [abs_of_nonneg (taperW_nonneg hR0 u)]; exact taperW_le_one hR0 u
  have hI : IntegrableOn (ctFr ε c f) (Ioo 0 R) := X.integrableOn_ctFr (by linarith) hRm
  have hint : IntegrableOn (fun u => taperW R u * ctFr ε c f u) (Ioo 0 R) :=
    hI.bdd_mul (c := 1) hT.aestronglyMeasurable.restrict (Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs]; exact hTb u)
  have hU : Ioc 0 u₁ ∪ Ioc u₁ R = Ioc 0 R := Ioc_union_Ioc_eq_Ioc hu0.le hu1
  have hTI : IntegrableOn (fun u => taperW R u * ctFr ε c f u) (Ioc 0 R) := by
    have := hint
    rwa [IntegrableOn, Measure.restrict_congr_set Ioo_ae_eq_Ioc] at this
  have hsplit : ∫ u in Ioo 0 R, taperW R u * ctFr ε c f u =
      (∫ u in Ioo 0 u₁, taperW R u * ctFr ε c f u) + ∫ u in Ioo u₁ R, taperW R u * ctFr ε c f u := by
    rw [← integral_Ioc_eq_integral_Ioo, ← hU,
      setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
        (hTI.mono_set (by rw [← hU]; exact subset_union_left)) (hTI.mono_set (by rw [← hU]; exact subset_union_right)),
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  -- near part: weight `≤ 2 (u₁/R)^12`
  have hnear : |∫ u in Ioo 0 u₁, taperW R u * ctFr ε c f u| ≤
      2 * (u₁ / R) ^ 12 * (1 + 2 * langerRadius c * hankelRinf c) := by
    refine (abs_integral_le_integral_abs).trans ?_
    have hI1 : IntegrableOn (ctFr ε c f) (Ioo 0 u₁) := X.integrableOn_ctFr (by linarith) (by linarith)
    have hmass := X.ctFr_abs_le (a := 0) (b := u₁) (by linarith) (by linarith) hu0.le
    calc ∫ u in Ioo 0 u₁, |taperW R u * ctFr ε c f u|
        ≤ ∫ u in Ioo 0 u₁, 2 * (u₁ / R) ^ 12 * |ctFr ε c f u| :=
          integral_mono_of_nonneg (Eventually.of_forall fun u => abs_nonneg _)
            (hI1.abs.const_mul _) (ae_restrict_of_forall_mem measurableSet_Ioo fun u hu => by
              beta_reduce
              rw [abs_mul, abs_of_nonneg (taperW_nonneg hR0 u)]
              refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
              refine (taperW_le_pow hR0 hu.1.le).trans ?_
              have h0 : 0 ≤ u / R := div_nonneg hu.1.le hR0.le
              exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 (div_le_div_of_nonneg_right hu.2.le hR0.le) 12)
                (by norm_num))
      _ = 2 * (u₁ / R) ^ 12 * ∫ u in Ioo 0 u₁, |ctFr ε c f u| := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hmass (by positivity)
  -- far part: weight `≤ 1`, deep lobe
  have hfar : |∫ u in Ioo u₁ R, taperW R u * ctFr ε c f u| ≤
      8 * (Real.exp (-5 * (langerLobeK * ctPhiR ε c u₁) ^ (3 / 2 : ℝ)) + Real.exp (-(1 / 25) * c)) +
        (ctPhiR ε c R - ctPhiR ε c u₁) * hankelRinf c := by
    refine (abs_integral_le_integral_abs).trans ?_
    have hI2 : IntegrableOn (ctFr ε c f) (Ioo u₁ R) := X.integrableOn_ctFr (by linarith) hRm
    have h1 : ∫ u in Ioo u₁ R, |taperW R u * ctFr ε c f u| ≤ ∫ u in Ioo u₁ R, |ctFr ε c f u| :=
      integral_mono_of_nonneg (Eventually.of_forall fun u => abs_nonneg _) hI2.abs
        (ae_restrict_of_forall_mem measurableSet_Ioo fun u hu => by
          beta_reduce
          rw [abs_mul]
          exact mul_le_of_le_one_left (abs_nonneg _) (hTb u))
    refine h1.trans ?_
    rw [X.ctFr_abs_subst (by linarith) hRm hu1]
    have hmono : ctPhiR ε c u₁ ≤ ctPhiR ε c R :=
      X.H.ctPhiR_strictMonoOn.monotoneOn ⟨by linarith, by linarith⟩ ⟨by linarith, hRm⟩ hu1
    have hx0 : 0 ≤ ctPhiR ε c u₁ := by
      by_contra h
      push Not at h
      have := mul_neg_of_pos_of_neg langerLobeK_pos h
      linarith
    have hxA : ctPhiR ε c R ≤ langerRadius c :=
      (abs_le.1 (X.H.abs_ctPhiR_lt (by rw [abs_of_pos hR0]; exact hRm)).le).2
    have := psi_abs_tail (by linarith [X.H.hc]) X.hf X.hε X.hM hx0 hmono hxA hk
    rw [intervalIntegral.integral_of_le hmono, integral_Ioc_eq_integral_Ioo] at this
    exact this
  rw [hsplit]
  exact (abs_add_le _ _).trans (add_le_add hnear hfar)

/-- info: 'FormalResearch.SignUncertainty.pos_lobe_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pos_lobe_le

end FormalResearch.SignUncertainty
