/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctDJetJC
public import FormalResearch.SignUncertainty.FctHomotopyJets

/-!
# The amplitude `J` and its coefficient functions (F2a, `(fct:dJ-jets)`)

`Jfun V H τ2`: the amplitude of the paper, `J = (1 + 2 Y V_Y / V) (V / V(·,0))^{1/2} H(τ2 · Y V²)` on the scaled chart, where
`H = (1 + G)^{1/2}`, `G(z) = z n'(z) / n(z)` and `τ2 = τ₁²` (`(fct:comp-cfu)`, the formula for `J` before `(fct:dJ-jets)`).
`Jca, Jcb, Jcc`: the coefficients of `∂_v J = a ∂_v V + b Y ∂_Y ∂_v V + c ∂_v V(·,0)` (`Jv_eq`), and `J_coef_jc`: their
stage-bounded `C^{15}` bounds on `Ω × Yint`.

Class: proved, no hypotheses beyond those stated.
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace FormalResearch.SignUncertainty
section DJetCoef
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The amplitude `J = (1 + 2 Y V_Y / V) (V / V(·,0))^{1/2} H(τ2 Y V²)` of the scaled chart. -/
noncomputable def Jfun (V : P × ℝ → ℝ) (H : ℝ → ℝ) (τ2 : ℝ) (q : P × ℝ) : ℝ :=
  (1 + 2 * (q.2 * fderiv ℝ V q (0, 1)) * (V q)⁻¹) * (V q * (V (q.1, 0))⁻¹) ^ (1 / 2 : ℝ) *
    H (τ2 * (q.2 * V q ^ 2))

/-- The coefficient of `∂_v V` in `∂_v J`. -/
noncomputable def Jca (V : P × ℝ → ℝ) (H : ℝ → ℝ) (τ2 : ℝ) (q : P × ℝ) : ℝ :=
  (V q * (V (q.1, 0))⁻¹) ^ (1 / 2 : ℝ) * H (τ2 * (q.2 * V q ^ 2)) *
      (-(2 * (q.2 * fderiv ℝ V q (0, 1)) * (V q)⁻¹ ^ 2) +
        (1 + 2 * (q.2 * fderiv ℝ V q (0, 1)) * (V q)⁻¹) * (V q)⁻¹ * (1 / 2)) +
    (1 + 2 * (q.2 * fderiv ℝ V q (0, 1)) * (V q)⁻¹) * (V q * (V (q.1, 0))⁻¹) ^ (1 / 2 : ℝ) *
      deriv H (τ2 * (q.2 * V q ^ 2)) * (2 * τ2 * q.2 * V q)

/-- The coefficient of `Y ∂_Y ∂_v V` in `∂_v J`. -/
noncomputable def Jcb (V : P × ℝ → ℝ) (H : ℝ → ℝ) (τ2 : ℝ) (q : P × ℝ) : ℝ :=
  2 * (V q * (V (q.1, 0))⁻¹) ^ (1 / 2 : ℝ) * H (τ2 * (q.2 * V q ^ 2)) * (V q)⁻¹

/-- The coefficient of `∂_v V(·,0)` in `∂_v J`. -/
noncomputable def Jcc (V : P × ℝ → ℝ) (H : ℝ → ℝ) (τ2 : ℝ) (q : P × ℝ) : ℝ :=
  -((1 + 2 * (q.2 * fderiv ℝ V q (0, 1)) * (V q)⁻¹) * (V q * (V (q.1, 0))⁻¹) ^ (1 / 2 : ℝ) *
    H (τ2 * (q.2 * V q ^ 2)) * (V (q.1, 0))⁻¹ * (1 / 2))

lemma zero_mem_Yint : (0 : ℝ) ∈ Yint := ⟨by norm_num, by norm_num⟩

/-- The projection `(p, Y) ↦ (p, 0)` as a continuous linear map of norm `≤ 1`. -/
noncomputable def projP (P : Type*) [NormedAddCommGroup P] [NormedSpace ℝ P] : (P × ℝ) →L[ℝ] (P × ℝ) :=
  (ContinuousLinearMap.inl ℝ P ℝ).comp (ContinuousLinearMap.fst ℝ P ℝ)

lemma projP_apply (q : P × ℝ) : projP P q = (q.1, 0) := by simp [projP]

lemma projP_norm : ‖projP P‖ ≤ 1 := by
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have h1 := ContinuousLinearMap.norm_inl_le_one ℝ P ℝ
  have h2 := norm_fst_le_one P ℝ
  nlinarith [norm_nonneg (ContinuousLinearMap.inl ℝ P ℝ), norm_nonneg (ContinuousLinearMap.fst ℝ P ℝ)]

lemma ratio_mem {x y : ℝ} (hx : 9 / 10 ≤ x ∧ x ≤ 6 / 5) (hy : 9 / 10 ≤ y ∧ y ≤ 6 / 5) :
    x * y⁻¹ ∈ Ioo (1 / 2 : ℝ) 2 := by
  have hy0 : 0 < y := by linarith [hy.1]
  rw [← div_eq_mul_inv]
  constructor
  · rw [lt_div_iff₀ hy0]; linarith [hx.1, hy.2]
  · rw [div_lt_iff₀ hy0]; linarith [hx.2, hy.1]

lemma inv_mem {x : ℝ} (hx : 9 / 10 ≤ x ∧ x ≤ 6 / 5) : x ∈ Ioo (1 / 2 : ℝ) 2 := by
  constructor <;> linarith [hx.1, hx.2]

variable {Ω : Set P} {β : ℝ} {V : P × ℝ → ℝ} {H : ℝ → ℝ} {T : Set ℝ} {τ2 : ℝ}

/-- The coefficient functions `a, b, c` of `∂_v J` are stage-bounded `C^{15}` functions on `Ω × Yint`. -/
lemma J_coef_jc (hΩ : IsOpen Ω) (hβ : 8 ≤ β) (hV : JCΦ 16 (Ω ×ˢ Yint) V β 0)
    (hVb : ∀ q ∈ Ω ×ˢ Yint, 9 / 10 ≤ V q ∧ V q ≤ 6 / 5) (hT : IsOpen T) (hH : JCΦ 16 T H β 0) (hτ : |τ2| ≤ 1)
    (hHT : ∀ q ∈ Ω ×ˢ Yint, τ2 * (q.2 * V q ^ 2) ∈ T) :
    JCΦ 15 (Ω ×ˢ Yint) (Jca V H τ2) β 9 ∧ JCΦ 15 (Ω ×ˢ Yint) (Jcb V H τ2) β 9 ∧
      JCΦ 15 (Ω ×ˢ Yint) (Jcc V H τ2) β 9 ∧ JCΦ 15 (Ω ×ˢ Yint) (Jfun V H τ2) β 9 := by
  have hβ0 : 0 ≤ β := by linarith
  have hβ1 : 1 ≤ β := by linarith
  have hO : IsOpen (Ω ×ˢ Yint) := hΩ.prod isOpen_Ioo
  have hOd : UniqueDiffOn ℝ (Ω ×ˢ Yint) := hO.uniqueDiffOn
  have hc : ∀ (x : ℝ) (m : ℕ), |x| ≤ 2 → JCΦ 15 (Ω ×ˢ Yint) (fun _ : P × ℝ => x) β m := fun x m hx =>
    JCΦ.const hOd (hx.trans (by have := Φb_iter_ge m β; linarith))
  have hV15 : JCΦ 15 (Ω ×ˢ Yint) V β 0 := hV.mono_order (by norm_num)
  have hs : JCΦ 15 (Ω ×ˢ Yint) (fun q : P × ℝ => q.2) β 0 :=
    JCΦ.snd hOd hβ1 (fun q hq => by
      have := hq.2; rw [abs_le]; constructor <;> linarith [this.1, this.2]) 0
  have hdV : JCΦ 15 (Ω ×ˢ Yint) (fun q => fderiv ℝ V q (0, 1)) β 0 := JCΦ.deriv_snd (j := 15) hO hV
  have hW : JCΦ 15 (Ω ×ˢ Yint) (fun q => q.2 * fderiv ℝ V q (0, 1)) β 1 :=
    JCΦ.mul hOd hβ0 (by norm_num) hs hdV (by norm_num)
  have hVi : JCΦ 15 (Ω ×ˢ Yint) (fun q => (V q)⁻¹) β 2 := by
    have := JCΦ.rpow_comp hOd hβ0 (k := 15) (by norm_num) (r := -1) (m' := 1 / 2) (M := 2) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [max_eq_left]; linarith) (by norm_num [max_eq_left]; linarith) hV15
      (fun q hq => inv_mem (hVb q hq)) (m := 2) (by norm_num)
    exact this.congr fun q _ => by simp [Real.rpow_neg_one]
  have hV0 : JCΦ 15 (Ω ×ˢ Yint) (fun q => V (q.1, 0)) β 1 := by
    have := JCΦ.comp_clm hOd hOd hβ0 (by norm_num) (projP P) projP_norm (g := V) (a := 0) hV15
      (fun q hq => by rw [projP_apply]; exact ⟨hq.1, zero_mem_Yint⟩) (m := 1) (by norm_num)
    exact this.congr fun q _ => by simp [projP_apply]
  have hV0i : JCΦ 15 (Ω ×ˢ Yint) (fun q => (V (q.1, 0))⁻¹) β 2 := by
    have := JCΦ.rpow_comp hOd hβ0 (k := 15) (by norm_num) (r := -1) (m' := 1 / 2) (M := 2) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [max_eq_left]; linarith) (by norm_num [max_eq_left]; linarith) hV0
      (fun q hq => inv_mem (hVb (q.1, 0) ⟨hq.1, zero_mem_Yint⟩)) (m := 2) (by norm_num)
    exact this.congr fun q _ => by simp [Real.rpow_neg_one]
  have hRt : JCΦ 15 (Ω ×ˢ Yint) (fun q => V q * (V (q.1, 0))⁻¹) β 3 :=
    JCΦ.mul hOd hβ0 (by norm_num) hV15 hV0i (by norm_num)
  have hQ : JCΦ 15 (Ω ×ˢ Yint) (fun q => (V q * (V (q.1, 0))⁻¹) ^ (1 / 2 : ℝ)) β 4 :=
    JCΦ.rpow_comp hOd hβ0 (k := 15) (by norm_num) (r := 1 / 2) (m' := 1 / 2) (M := 2) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [max_eq_left]; linarith) (by norm_num [max_eq_left]; linarith) hRt
      (fun q hq => ratio_mem (hVb q hq) (hVb (q.1, 0) ⟨hq.1, zero_mem_Yint⟩)) (m := 4) (by norm_num)
  have hV2 : JCΦ 15 (Ω ×ˢ Yint) (fun q => V q ^ 2) β 1 :=
    (JCΦ.mul hOd hβ0 (by norm_num) hV15 hV15 (by norm_num)).congr fun q _ => by ring
  have hsV2 : JCΦ 15 (Ω ×ˢ Yint) (fun q => q.2 * V q ^ 2) β 2 :=
    JCΦ.mul hOd hβ0 (by norm_num) hs hV2 (by norm_num)
  have hτc : JCΦ 15 (Ω ×ˢ Yint) (fun _ : P × ℝ => τ2) β 0 := hc τ2 0 (hτ.trans (by norm_num))
  have hZ : JCΦ 15 (Ω ×ˢ Yint) (fun q => τ2 * (q.2 * V q ^ 2)) β 3 :=
    JCΦ.mul hOd hβ0 (by norm_num) hτc hsV2 (by norm_num)
  have hH15 : JCΦ 15 T H β 0 := hH.mono_order (by norm_num)
  have hH' : JCΦ 15 T (deriv H) β 0 := by
    have := (hH : JC 16 T H _).succ_fderiv hT |>.clm_apply_const hT.uniqueDiffOn (1 : ℝ)
    have h1 : ‖(1 : ℝ)‖ = 1 := by simp
    rw [h1, one_mul] at this
    exact this
  have hR : JCΦ 15 (Ω ×ˢ Yint) (fun q => H (τ2 * (q.2 * V q ^ 2))) β 4 :=
    JCΦ.comp1 hOd hT.uniqueDiffOn hβ0 (by norm_num) hH15 hZ hHT (by norm_num)
  have hR' : JCΦ 15 (Ω ×ˢ Yint) (fun q => deriv H (τ2 * (q.2 * V q ^ 2))) β 4 :=
    JCΦ.comp1 hOd hT.uniqueDiffOn hβ0 (by norm_num) hH' hZ hHT (by norm_num)
  have h2W : JCΦ 15 (Ω ×ˢ Yint) (fun q => 2 * (q.2 * fderiv ℝ V q (0, 1))) β 2 :=
    JCΦ.mul hOd hβ0 (by norm_num) (hc 2 0 (by norm_num)) hW (by norm_num)
  have h2WVi : JCΦ 15 (Ω ×ˢ Yint) (fun q => 2 * (q.2 * fderiv ℝ V q (0, 1)) * (V q)⁻¹) β 3 :=
    JCΦ.mul hOd hβ0 (by norm_num) h2W hVi (by norm_num)
  have hP : JCΦ 15 (Ω ×ˢ Yint) (fun q => 1 + 2 * (q.2 * fderiv ℝ V q (0, 1)) * (V q)⁻¹) β 4 :=
    JCΦ.add hOd (hc 1 0 (by norm_num)) h2WVi (by norm_num)
  have hVi2 : JCΦ 15 (Ω ×ˢ Yint) (fun q => (V q)⁻¹ ^ 2) β 3 :=
    (JCΦ.mul hOd hβ0 (by norm_num) hVi hVi (by norm_num)).congr fun q _ => by ring
  have hT1 : JCΦ 15 (Ω ×ˢ Yint) (fun q => 2 * (q.2 * fderiv ℝ V q (0, 1)) * (V q)⁻¹ ^ 2) β 4 :=
    JCΦ.mul hOd hβ0 (by norm_num) h2W hVi2 (by norm_num)
  have hPVi : JCΦ 15 (Ω ×ˢ Yint) (fun q => (1 + 2 * (q.2 * fderiv ℝ V q (0, 1)) * (V q)⁻¹) * (V q)⁻¹ * (1 / 2)) β 6 :=
    JCΦ.mul hOd hβ0 (by norm_num) (JCΦ.mul hOd hβ0 (by norm_num) hP hVi (by norm_num : max 4 2 + 1 ≤ 5)) (hc (1 / 2) 0 (by norm_num))
      (by norm_num : max 5 0 + 1 ≤ 6)
  have hinner : JCΦ 15 (Ω ×ˢ Yint) (fun q => -(2 * (q.2 * fderiv ℝ V q (0, 1)) * (V q)⁻¹ ^ 2) +
      (1 + 2 * (q.2 * fderiv ℝ V q (0, 1)) * (V q)⁻¹) * (V q)⁻¹ * (1 / 2)) β 7 :=
    JCΦ.add hOd (JC.neg hOd hT1) hPVi (by norm_num)
  have hQR : JCΦ 15 (Ω ×ˢ Yint) (fun q => (V q * (V (q.1, 0))⁻¹) ^ (1 / 2 : ℝ) * H (τ2 * (q.2 * V q ^ 2))) β 5 :=
    JCΦ.mul hOd hβ0 (by norm_num) hQ hR (by norm_num)
  have ha1 := JCΦ.mul hOd hβ0 (by norm_num) hQR hinner (by norm_num : max 5 7 + 1 ≤ 8)
  have hPQ : JCΦ 15 (Ω ×ˢ Yint) (fun q => (1 + 2 * (q.2 * fderiv ℝ V q (0, 1)) * (V q)⁻¹) *
      (V q * (V (q.1, 0))⁻¹) ^ (1 / 2 : ℝ)) β 5 := JCΦ.mul hOd hβ0 (by norm_num) hP hQ (by norm_num)
  have hPQR' := JCΦ.mul hOd hβ0 (by norm_num) hPQ hR' (by norm_num : max 5 4 + 1 ≤ 6)
  have hτs : JCΦ 15 (Ω ×ˢ Yint) (fun q => 2 * τ2 * q.2 * V q) β 2 :=
    JCΦ.mul hOd hβ0 (by norm_num) (JCΦ.mul hOd hβ0 (by norm_num) (hc (2 * τ2) 0 (by
      rw [abs_mul]; norm_num; linarith [hτ])) hs (by norm_num : max 0 0 + 1 ≤ 1)) hV15 (by norm_num : max 1 0 + 1 ≤ 2)
  have ha2 := JCΦ.mul hOd hβ0 (by norm_num) hPQR' hτs (by norm_num : max 6 2 + 1 ≤ 7)
  have hJ := JCΦ.mul hOd hβ0 (by norm_num) hPQ hR (by norm_num : max 5 4 + 1 ≤ 6)
  refine ⟨(JCΦ.add hOd ha1 ha2 (by norm_num : max 8 7 + 1 ≤ 9)).congr fun q _ => rfl, ?_, ?_,
    (hJ.mono_m (by norm_num : 6 ≤ 9)).congr fun q _ => rfl⟩
  · have h2Q := JCΦ.mul hOd hβ0 (by norm_num) (hc 2 0 (by norm_num)) hQ (by norm_num : max 0 4 + 1 ≤ 5)
    have h2QR := JCΦ.mul hOd hβ0 (by norm_num) h2Q hR (by norm_num : max 5 4 + 1 ≤ 6)
    exact (JCΦ.mul hOd hβ0 (by norm_num) h2QR hVi (by norm_num : max 6 2 + 1 ≤ 7)).mono_m (by norm_num : 7 ≤ 9)
      |>.congr fun q _ => rfl
  · have hPQR := JCΦ.mul hOd hβ0 (by norm_num) hPQ hR (by norm_num : max 5 4 + 1 ≤ 6)
    have h7 := JCΦ.mul hOd hβ0 (by norm_num) hPQR hV0i (by norm_num : max 6 2 + 1 ≤ 7)
    have h8 := JCΦ.mul hOd hβ0 (by norm_num) h7 (hc (1 / 2) 0 (by norm_num)) (by norm_num : max 7 0 + 1 ≤ 8)
    have h8n : JCΦ 15 (Ω ×ˢ Yint) _ β 8 := JC.neg hOd h8
    exact (h8n.mono_m (by norm_num : 8 ≤ 9)).congr fun q _ => rfl

/-- info: 'FormalResearch.SignUncertainty.J_coef_jc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms J_coef_jc

end DJetCoef
end FormalResearch.SignUncertainty
