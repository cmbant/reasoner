/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctHomotopy
public import FormalResearch.SignUncertainty.FctWeighted
public import FormalResearch.SignUncertainty.FctJCBound

/-!
# Divided-difference representation of the homotopy ODE and its weighted jets (F2a, `fct:comp-cfu`)

From the pointwise homotopy ODE (`ode_pointwise`): `∂_v V = e U' Σ_{k<5} Y^{4-k} A^k G(A) + e U' Y⁵ ∫₀¹ G_Y(Y + σ(A-Y)) dσ`
with `G = V^{11} θ(·, Y V²)`, `U' = V + 2Y ∂_Y V` (`E_eq`), the stage-bounded `C^{15}` bounds of the ingredients (`E_build`), and
the one-variable bounds `|∂_Y^n ∂_v V| ≤ C |e| max(Y, A)^{max(0,4-n)}` (`E_jets`), the weights of `(fct:V-diff-jets)`.

Class: proved, no hypotheses beyond those stated.
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace FormalResearch.SignUncertainty

section Bridge
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The open interval of the `Y` variable of the chart. -/
noncomputable abbrev Yint : Set ℝ := Ioo (-(1 / 5) : ℝ) (36 / 10)

/-- The divided-difference integral `∫₀¹ G_Y(p, Y + σ(A - Y)) dσ`. -/
noncomputable def divInt (G : P × ℝ → ℝ) (A : P → ℝ) (q : P × ℝ) : ℝ :=
  ∫ σ in Icc (0 : ℝ) 1, fderiv ℝ G (q.1, q.2 + σ * (A q.1 - q.2)) (0, 1)

lemma divInt_mul {Ω : Set P} (hΩ : IsOpen Ω) {G : P × ℝ → ℝ} {A : P → ℝ} (hG : ContDiffOn ℝ 1 G (Ω ×ˢ Yint))
    (hAY : ∀ p ∈ Ω, A p ∈ Yint) {q : P × ℝ} (hq : q ∈ Ω ×ˢ Yint) :
    (A q.1 - q.2) * divInt G A q = G (q.1, A q.1) - G q := by
  have hO : IsOpen (Ω ×ˢ Yint) := hΩ.prod isOpen_Ioo
  have hmem : ∀ σ ∈ Icc (0 : ℝ) 1, (q.1, q.2 + σ * (A q.1 - q.2)) ∈ Ω ×ˢ Yint := fun σ hσ =>
    ⟨hq.1, by
      have := (convex_Ioo (-(1 / 5) : ℝ) (36 / 10)).add_smul_sub_mem hq.2 (hAY _ hq.1) hσ
      simpa [smul_eq_mul] using this⟩
  have hder : ∀ σ ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun σ : ℝ => G (q.1, q.2 + σ * (A q.1 - q.2)))
      ((A q.1 - q.2) * fderiv ℝ G (q.1, q.2 + σ * (A q.1 - q.2)) (0, 1)) σ := by
    intro σ hσ
    rw [uIcc_of_le zero_le_one] at hσ
    have h1 := hasDerivAt_line (F := G) (y := q.1) (t := q.2 + σ * (A q.1 - q.2))
      ((hG.differentiableOn one_ne_zero).differentiableAt (hO.mem_nhds (hmem σ hσ)))
    have h2 : HasDerivAt (fun σ : ℝ => q.2 + σ * (A q.1 - q.2)) (A q.1 - q.2) σ := by
      simpa using ((hasDerivAt_id σ).mul_const (A q.1 - q.2)).const_add q.2
    have h3 := h1.comp σ h2
    rw [mul_comm] at h3
    exact h3
  have hcont : ContinuousOn (fun σ : ℝ => fderiv ℝ G (q.1, q.2 + σ * (A q.1 - q.2)) (0, 1)) (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]
    have h1 : ContinuousOn (fun x => fderiv ℝ G x (0, 1)) (Ω ×ˢ Yint) :=
      (hG.continuousOn_fderiv_of_isOpen hO le_rfl).clm_apply continuousOn_const
    exact h1.comp (by fun_prop) (fun σ hσ => hmem σ hσ)
  have hint : IntervalIntegrable (fun σ : ℝ => (A q.1 - q.2) * fderiv ℝ G (q.1, q.2 + σ * (A q.1 - q.2)) (0, 1))
      volume 0 1 := (continuousOn_const.mul hcont).intervalIntegrable
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint
  simp only [divInt]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  rw [intervalIntegral.integral_const_mul] at hftc
  rw [hftc]
  have e1 : q.2 + 1 * (A q.1 - q.2) = A q.1 := by ring
  have e0 : q.2 + 0 * (A q.1 - q.2) = q.2 := by ring
  rw [e1, e0]

lemma E_eq {Ω : Set P} (hΩ : IsOpen Ω) {G Ev U : P × ℝ → ℝ} {A' : P → ℝ} {e : ℝ}
    (hG : ContDiffOn ℝ 1 G (Ω ×ˢ Yint)) (hAY : ∀ p ∈ Ω, A' p ∈ Yint)
    (hEv : ContinuousOn Ev (Ω ×ˢ Yint)) (hU : ContinuousOn U (Ω ×ˢ Yint))
    (hI : ContinuousOn (divInt G A') (Ω ×ˢ Yint))
    (hode : ∀ q ∈ Ω ×ˢ Yint, (A' q.1 - q.2) * Ev q =
      e * U q * (A' q.1 ^ 5 * G (q.1, A' q.1) - q.2 ^ 5 * G q)) :
    ∀ q ∈ Ω ×ˢ Yint, Ev q = e * (U q * ((∑ k ∈ Finset.range 5, q.2 ^ (4 - k) * A' q.1 ^ k) * G (q.1, A' q.1) +
      q.2 ^ 5 * divInt G A' q)) := by
  have hO : IsOpen (Ω ×ˢ Yint) := hΩ.prod isOpen_Ioo
  have hne : ∀ q ∈ Ω ×ˢ Yint, A' q.1 ≠ q.2 → Ev q = e * (U q * ((∑ k ∈ Finset.range 5, q.2 ^ (4 - k) * A' q.1 ^ k) *
      G (q.1, A' q.1) + q.2 ^ 5 * divInt G A' q)) := by
    intro q hq hAq
    have h1 := hode q hq
    have h2 := divInt_mul hΩ hG hAY hq
    have h3 : A' q.1 ^ 5 - q.2 ^ 5 = (A' q.1 - q.2) * ∑ k ∈ Finset.range 5, q.2 ^ (4 - k) * A' q.1 ^ k := by
      have := geom_sum₂_mul (A' q.1) q.2 5
      rw [← this, mul_comm]
      congr 1
      refine Finset.sum_congr rfl fun k _ => by ring
    have hsub : A' q.1 - q.2 ≠ 0 := sub_ne_zero.mpr hAq
    apply mul_left_cancel₀ hsub
    rw [h1]
    have : A' q.1 ^ 5 * G (q.1, A' q.1) - q.2 ^ 5 * G q =
        (A' q.1 ^ 5 - q.2 ^ 5) * G (q.1, A' q.1) + q.2 ^ 5 * (G (q.1, A' q.1) - G q) := by ring
    rw [this, h3, ← h2]
    ring
  intro q hq
  by_cases hAq : A' q.1 = q.2
  swap
  · exact hne q hq hAq
  -- continuity at `Y = A`
  set S : Set ℝ := {s | (q.1, s) ∈ Ω ×ˢ Yint} with hS
  have hSo : IsOpen S := hO.preimage (Continuous.prodMk_right q.1)
  have hAS : A' q.1 ∈ S := ⟨hq.1, hAY _ hq.1⟩
  have hqS : q.2 ∈ S := hq.2 |> fun h => ⟨hq.1, h⟩
  set h : ℝ → ℝ := fun s => Ev (q.1, s) - e * (U (q.1, s) * ((∑ k ∈ Finset.range 5, s ^ (4 - k) * A' q.1 ^ k) *
      G (q.1, A' q.1) + s ^ 5 * divInt G A' (q.1, s))) with hh
  have hcont : ContinuousAt h q.2 := by
    have hm : ∀ {F : P × ℝ → ℝ}, ContinuousOn F (Ω ×ˢ Yint) → ContinuousAt (fun s => F (q.1, s)) q.2 := by
      intro F hF
      exact (hF.continuousAt (hO.mem_nhds ⟨hq.1, hq.2⟩)).comp (f := fun s : ℝ => (q.1, s)) (x := q.2)
        (continuous_const.prodMk continuous_id).continuousAt
    refine (hm hEv).sub (continuousAt_const.mul ((hm hU).mul ?_))
    exact ((by fun_prop : Continuous fun s : ℝ => ∑ k ∈ Finset.range 5, s ^ (4 - k) * A' q.1 ^ k).continuousAt.mul
      continuousAt_const).add ((continuousAt_id.pow 5).mul (hm hI))
  have hz : ∀ᶠ s in 𝓝[≠] q.2, h s = 0 := by
    have : ∀ᶠ s in 𝓝 q.2, s ∈ S := hSo.mem_nhds hqS
    filter_upwards [nhdsWithin_le_nhds this, self_mem_nhdsWithin] with s hs hsne
    have := hne (q.1, s) hs (by rw [hAq]; exact fun h => hsne h.symm)
    simp only [hh, this]; ring
  have h0 : h q.2 = 0 := by
    have t1 : Tendsto h (𝓝[≠] q.2) (𝓝 (h q.2)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
    have t2 : Tendsto h (𝓝[≠] q.2) (𝓝 0) := tendsto_const_nhds.congr' (hz.mono fun s hs => hs.symm)
    exact tendsto_nhds_unique t1 t2
  simp only [hh] at h0
  have : (q.1, q.2) = q := rfl
  rw [this] at h0
  linarith

/-- One-variable derivatives in the last coordinate of a `JC` function. -/
lemma dY_bound {O : Set (P × ℝ)} (hO : IsOpen O) {k : ℕ} {f : P × ℝ → ℝ} {b : ℝ} (hb : 0 ≤ b)
    (h : JC k O f b) {p : P} {Y : ℝ} (hpY : (p, Y) ∈ O) :
    ContDiffAt ℝ k (fun s : ℝ => f (p, s)) Y ∧
      ∀ j ≤ k, |iteratedDeriv j (fun s : ℝ => f (p, s)) Y| ≤ k.factorial * b := by
  set S : Set ℝ := {s | (p, s) ∈ O} with hS
  have hSo : IsOpen S := hO.preimage (Continuous.prodMk_right p)
  have hYS : Y ∈ S := hpY
  have hSd : UniqueDiffOn ℝ S := hSo.uniqueDiffOn
  have hc : JC k S (fun s : ℝ => f (p, s)) (k.factorial * b * (max 1 (max 0 1)) ^ k) :=
    JC.comp_pair (k := k) hSd hO.uniqueDiffOn (g := f) (u := fun _ : ℝ => p)
      (w := fun s : ℝ => s) (C := b) (b1 := 0) (b2 := 1) hb h contDiffOn_const contDiffOn_id
      (fun i hi _ s hs => by
        rw [iteratedFDerivWithin_const_of_ne (by omega)]; simp)
      (fun i hi _ s hs => norm_iteratedFDerivWithin_id_le hSd hi hs) (fun s hs => hs)
  have hmax : max (1 : ℝ) (max 0 1) = 1 := by norm_num
  rw [hmax, one_pow, mul_one] at hc
  refine ⟨hc.1.contDiffAt (hSo.mem_nhds hYS), fun j hj => ?_⟩
  have e1 := iteratedDerivWithin_of_isOpen hSo (n := j) (f := fun s : ℝ => f (p, s)) hYS
  rw [← e1, iteratedDerivWithin_eq_iteratedFDerivWithin]
  calc _ ≤ ‖iteratedFDerivWithin ℝ j (fun s : ℝ => f (p, s)) S Y‖ * ∏ _i : Fin j, ‖(1 : ℝ)‖ := by
        simpa using (iteratedFDerivWithin ℝ j (fun s : ℝ => f (p, s)) S Y).le_opNorm (fun _ => (1 : ℝ))
    _ ≤ k.factorial * b := by
        simp only [norm_one, Finset.prod_const_one, mul_one]
        exact hc.2 j hj Y hYS

/-- Stage-bounded building blocks of the divided-difference representation of `∂_v V`. -/
lemma E_build {Ω : Set P} (hΩ : IsOpen Ω) {β : ℝ} (hβ : 4 ≤ β) {V θ : P × ℝ → ℝ} {A : P → ℝ}
    (hV : JCΦ 16 (Ω ×ˢ Yint) V β 0) (hA : JCΦ 16 Ω A β 0) (hθ : JCΦ 16 (Ω ×ˢ Ioo (-1 : ℝ) 6) θ β 0)
    (hAY : ∀ p ∈ Ω, A p ∈ Yint) (hz : ∀ q ∈ Ω ×ˢ Yint, q.2 * V q ^ 2 ∈ Ioo (-1 : ℝ) 6) :
    JCΦ 16 (Ω ×ˢ Yint) (fun q => V q ^ 11 * θ (q.1, q.2 * V q ^ 2)) β 6 ∧
    JCΦ 16 Ω (fun p => V (p, A p) ^ 11 * θ (p, A p * V (p, A p) ^ 2)) β 7 ∧
    JCΦ 15 (Ω ×ˢ Yint) (divInt (fun q => V q ^ 11 * θ (q.1, q.2 * V q ^ 2)) A) β 7 ∧
    JCΦ 15 (Ω ×ˢ Yint) (fun q => V q + 2 * q.2 * fderiv ℝ V q (0, 1)) β 3 := by
  have hβ0 : 0 ≤ β := by linarith
  have hβ1 : 1 ≤ β := by linarith
  have hO : IsOpen (Ω ×ˢ Yint) := hΩ.prod isOpen_Ioo
  have hOd : UniqueDiffOn ℝ (Ω ×ˢ Yint) := hO.uniqueDiffOn
  have hΩd : UniqueDiffOn ℝ Ω := hΩ.uniqueDiffOn
  have hW : IsOpen (Ω ×ˢ Ioo (-1 : ℝ) 6) := hΩ.prod isOpen_Ioo
  have hs0 : JCΦ 16 (Ω ×ˢ Yint) (fun q : P × ℝ => q.2) β 0 :=
    JCΦ.snd hOd hβ1 (fun q hq => by
      have := hq.2; rw [abs_le]; constructor <;> linarith [this.1, this.2]) 0
  have hv2 : JCΦ 16 (Ω ×ˢ Yint) (fun q => V q ^ 2) β 1 :=
    (JCΦ.mul hOd hβ0 (by norm_num) hV hV (by norm_num)).congr fun q _ => by ring
  have hv4 : JCΦ 16 (Ω ×ˢ Yint) (fun q => V q ^ 4) β 2 :=
    (JCΦ.mul hOd hβ0 (by norm_num) hv2 hv2 (by norm_num)).congr fun q _ => by ring
  have hv8 : JCΦ 16 (Ω ×ˢ Yint) (fun q => V q ^ 8) β 3 :=
    (JCΦ.mul hOd hβ0 (by norm_num) hv4 hv4 (by norm_num)).congr fun q _ => by ring
  have hv10 : JCΦ 16 (Ω ×ˢ Yint) (fun q => V q ^ 10) β 4 :=
    (JCΦ.mul hOd hβ0 (by norm_num) hv8 hv2 (by norm_num)).congr fun q _ => by ring
  have hv11 : JCΦ 16 (Ω ×ˢ Yint) (fun q => V q ^ 11) β 5 :=
    (JCΦ.mul hOd hβ0 (by norm_num) hv10 hV (by norm_num)).congr fun q _ => by ring
  have hw : JCΦ 16 (Ω ×ˢ Yint) (fun q => q.2 * V q ^ 2) β 2 :=
    JCΦ.mul hOd hβ0 (by norm_num) hs0 hv2 (by norm_num)
  have hL : ‖ContinuousLinearMap.fst ℝ P ℝ‖ ≤ 1 := norm_fst_le_one P ℝ
  have hθc : JCΦ 16 (Ω ×ˢ Yint) (fun q => θ (q.1, q.2 * V q ^ 2)) β 3 :=
    (JCΦ.comp_pair hOd (hW.uniqueDiffOn : UniqueDiffOn ℝ (Ω ×ˢ Ioo (-1 : ℝ) 6)) hβ0 (by norm_num) (g := θ) (u := fun q => ContinuousLinearMap.fst ℝ P ℝ q)
      (w := fun q => q.2 * V q ^ 2) (a1 := 0) (a2 := 0) (a3 := 2) hθ
      (ContinuousLinearMap.fst ℝ P ℝ).contDiff.contDiffOn hw.1
      (fun i hi _ y hy => (norm_iteratedFDerivWithin_clm_le hOd (ContinuousLinearMap.fst ℝ P ℝ) hi hy).trans
        (hL.trans hβ1))
      (fun i _ hi y hy => hw.2 i hi y hy) (fun q hq => ⟨hq.1, hz q hq⟩) (by norm_num)).congr fun q _ => rfl
  have hG : JCΦ 16 (Ω ×ˢ Yint) (fun q => V q ^ 11 * θ (q.1, q.2 * V q ^ 2)) β 6 :=
    JCΦ.mul hOd hβ0 (by norm_num) hv11 hθc (by norm_num)
  have hGa : JCΦ 16 Ω (fun p => V (p, A p) ^ 11 * θ (p, A p * V (p, A p) ^ 2)) β 7 :=
    JCΦ.comp_pair hΩd hOd hβ0 (by norm_num) (g := fun q : P × ℝ => V q ^ 11 * θ (q.1, q.2 * V q ^ 2))
      (u := fun p => p) (w := A) (a1 := 6) (a2 := 0) (a3 := 0) hG contDiffOn_id hA.1
      (fun i hi _ y hy => (norm_iteratedFDerivWithin_id_le hΩd hi hy).trans hβ1)
      (fun i _ hi y hy => hA.2 i hi y hy) (fun p hp => ⟨hp, hAY p hp⟩) (by norm_num)
  have hG' : JCΦ 15 (Ω ×ˢ Yint) (fun q => fderiv ℝ (fun q => V q ^ 11 * θ (q.1, q.2 * V q ^ 2)) q (0, 1)) β 6 :=
    JCΦ.deriv_snd (j := 15) hO hG
  refine ⟨hG, hGa, ?_, ?_⟩
  · have hU3d : UniqueDiffOn ℝ ((Ω ×ˢ Yint) ×ˢ Icc (0 : ℝ) 1) := hOd.prod (uniqueDiffOn_Icc zero_lt_one)
    have hG'15 : JCΦ 15 (Ω ×ˢ Yint) (fun x : P × ℝ => fderiv ℝ (fun q => V q ^ 11 * θ (q.1, q.2 * V q ^ 2)) x (0, 1)) β 6 := hG'
    have hσ : JCΦ 15 ((Ω ×ˢ Yint) ×ˢ Icc (0 : ℝ) 1) (fun x : (P × ℝ) × ℝ => x.2) β 0 :=
      JCΦ.snd hU3d hβ1 (fun x hx => by
        have := hx.2; rw [abs_le]; constructor <;> linarith [this.1, this.2]) 0
    have hs15 : JCΦ 15 (Ω ×ˢ Yint) (fun q : P × ℝ => q.2) β 0 := hs0.mono_order (by norm_num)
    have hA15 : JCΦ 15 Ω A β 0 := hA.mono_order (by norm_num)
    have hLn : ‖ContinuousLinearMap.fst ℝ (P × ℝ) ℝ‖ ≤ 1 := norm_fst_le_one _ _
    set L1 : ((P × ℝ) × ℝ) →L[ℝ] P := (ContinuousLinearMap.fst ℝ P ℝ).comp (ContinuousLinearMap.fst ℝ (P × ℝ) ℝ)
      with hL1
    have hL1n : ‖L1‖ ≤ 1 :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
        have := norm_fst_le_one P ℝ
        have := norm_fst_le_one (P × ℝ) ℝ
        nlinarith [norm_nonneg (ContinuousLinearMap.fst ℝ P ℝ), norm_nonneg (ContinuousLinearMap.fst ℝ (P × ℝ) ℝ)])
    have hz3 : JCΦ 15 ((Ω ×ˢ Yint) ×ˢ Icc (0 : ℝ) 1) (fun x : (P × ℝ) × ℝ => x.1.2) β 1 :=
      (JCΦ.comp_clm hU3d hOd hβ0 (by norm_num) (ContinuousLinearMap.fst ℝ (P × ℝ) ℝ) hLn hs15
        (fun x hx => hx.1) (by norm_num)).congr fun x _ => rfl
    have hA3 : JCΦ 15 ((Ω ×ˢ Yint) ×ˢ Icc (0 : ℝ) 1) (fun x : (P × ℝ) × ℝ => A (L1 x)) β 1 :=
      JCΦ.comp_clm hU3d hΩd hβ0 (by norm_num) L1 hL1n hA15 (fun x hx => hx.1.1) (by norm_num)
    have hdf := JCΦ.sub hU3d hA3 hz3 (by norm_num : max 1 1 + 1 ≤ 2)
    have hml := JCΦ.mul hU3d hβ0 (by norm_num) hσ hdf (by norm_num : max 0 2 + 1 ≤ 3)
    have hwx := JCΦ.add hU3d hz3 hml (by norm_num : max 1 3 + 1 ≤ 4)
    have hcomp : JCΦ 15 ((Ω ×ˢ Yint) ×ˢ Icc (0 : ℝ) 1) (fun x : (P × ℝ) × ℝ =>
        fderiv ℝ (fun q => V q ^ 11 * θ (q.1, q.2 * V q ^ 2))
          (L1 x, x.1.2 + x.2 * (A (L1 x) - x.1.2)) (0, 1)) β 7 :=
      JCΦ.comp_pair hU3d hOd hβ0 (by norm_num) (g := fun x : P × ℝ => fderiv ℝ (fun q => V q ^ 11 * θ (q.1, q.2 * V q ^ 2)) x (0, 1))
        (u := fun x : (P × ℝ) × ℝ => L1 x) (w := fun x : (P × ℝ) × ℝ => x.1.2 + x.2 * (A (L1 x) - x.1.2))
        (a1 := 6) (a2 := 0) (a3 := 4) hG'15 L1.contDiff.contDiffOn hwx.1
        (fun i hi _ y hy => (norm_iteratedFDerivWithin_clm_le hU3d L1 hi hy).trans (hL1n.trans hβ1))
        (fun i _ hi y hy => hwx.2 i hi y hy) (fun x hx => by
          have hp : L1 x ∈ Ω := hx.1.1
          have := (convex_Ioo (-(1 / 5) : ℝ) (36 / 10)).add_smul_sub_mem hx.1.2 (hAY _ hp) hx.2
          exact ⟨hp, by simpa [smul_eq_mul] using this⟩) (by norm_num)
    exact (JCΦ.integral01 hO (f := fun (q : P × ℝ) (σ : ℝ) =>
      fderiv ℝ (fun q => V q ^ 11 * θ (q.1, q.2 * V q ^ 2)) (q.1, q.2 + σ * (A q.1 - q.2)) (0, 1))
      (hcomp.congr fun x _ => rfl)).congr fun q _ => rfl
  · have hV15 : JCΦ 15 (Ω ×ˢ Yint) V β 0 := hV.mono_order (by norm_num)
    have hs15 : JCΦ 15 (Ω ×ˢ Yint) (fun q : P × ℝ => q.2) β 0 := hs0.mono_order (by norm_num)
    have hdV : JCΦ 15 (Ω ×ˢ Yint) (fun q => fderiv ℝ V q (0, 1)) β 0 := JCΦ.deriv_snd (j := 15) hO hV
    have hc2 : JCΦ 15 (Ω ×ˢ Yint) (fun _ : P × ℝ => (2 : ℝ)) β 0 :=
      JCΦ.const hOd (by rw [abs_of_pos (by norm_num)]; simpa using (by linarith : (2:ℝ) ≤ β))
    have h2s := JCΦ.mul hOd hβ0 (by norm_num) hc2 hs15 (by norm_num : max 0 0 + 1 ≤ 1)
    have h2sd := JCΦ.mul hOd hβ0 (by norm_num) h2s hdV (by norm_num : max 1 0 + 1 ≤ 2)
    exact JCΦ.add hOd hV15 h2sd (by norm_num)

/-- Weighted one-variable jets of `∂_v V`: `|∂_Y^n ∂_v V| ≤ C |e| max(Y,A)^{max(0,4-n)}`. -/
theorem E_jets {Ω : Set P} (hΩ : IsOpen Ω) {β : ℝ} (hβ : 4 ≤ β) {V θ : P × ℝ → ℝ} {A : P → ℝ} (v : P) (e : ℝ)
    (hV : JCΦ 16 (Ω ×ˢ Yint) V β 0) (hA : JCΦ 16 Ω A β 0) (hθ : JCΦ 16 (Ω ×ˢ Ioo (-1 : ℝ) 6) θ β 0)
    (hAY : ∀ p ∈ Ω, A p ∈ Yint) (hz : ∀ q ∈ Ω ×ˢ Yint, q.2 * V q ^ 2 ∈ Ioo (-1 : ℝ) 6)
    (hode : ∀ q ∈ Ω ×ˢ Yint, (A q.1 - q.2) * fderiv ℝ V q (v, 0) =
      e * (V q + 2 * q.2 * fderiv ℝ V q (0, 1)) *
        (A q.1 ^ 5 * V (q.1, A q.1) ^ 11 * θ (q.1, A q.1 * V (q.1, A q.1) ^ 2) -
          q.2 ^ 5 * V q ^ 11 * θ (q.1, q.2 * V q ^ 2)))
    {p : P} (hp : p ∈ Ω) {Y : ℝ} (hY : Y ∈ Yint) (hY0 : 0 ≤ Y) (hA0 : 0 ≤ A p) {n : ℕ} (hn : n ≤ 15) :
    |iteratedDeriv n (fun s : ℝ => fderiv ℝ V (p, s) (v, 0)) Y| ≤
      |e| * ((n + 1) * 2 ^ n * 1000000 * ((Nat.factorial 15 : ℝ) * Φb^[8] β) * max Y (A p) ^ (4 - n)) := by
  have hβ0 : 0 ≤ β := by linarith
  have hO : IsOpen (Ω ×ˢ Yint) := hΩ.prod isOpen_Ioo
  have hOd : UniqueDiffOn ℝ (Ω ×ˢ Yint) := hO.uniqueDiffOn
  obtain ⟨hG, hGa, hIG, hU⟩ := E_build hΩ hβ hV hA hθ hAY hz
  set G : P × ℝ → ℝ := fun q => V q ^ 11 * θ (q.1, q.2 * V q ^ 2) with hGdef
  set Ga : P → ℝ := fun p => G (p, A p) with hGadef
  set U : P × ℝ → ℝ := fun q => V q + 2 * q.2 * fderiv ℝ V q (0, 1) with hUdef
  have hG1 : ContDiffOn ℝ 1 G (Ω ×ˢ Yint) := (hG : JC 16 _ G _).1.of_le (by norm_num)
  have hEv : JC 15 (Ω ×ˢ Yint) (fun y => fderiv ℝ V y (v, 0)) _ :=
    (JC.succ_fderiv hO (hV : JC 16 _ V _)).clm_apply_const hOd (v, 0)
  have hEq := E_eq hΩ (G := G) (A' := A) (Ev := fun y => fderiv ℝ V y (v, 0)) (U := U) (e := e)
    hG1 hAY hEv.1.continuousOn (hU : JC 15 _ U _).1.continuousOn
    (hIG : JC 15 _ (divInt G A) _).1.continuousOn (fun q hq => by rw [hode q hq]; simp only [hGdef, hUdef]; ring)
  have hpO : (p, Y) ∈ Ω ×ˢ Yint := ⟨hp, hY⟩
  have hGa0 : |Ga p| ≤ Φb^[7] β := JB.apply_le (hGa : JC 16 Ω _ _).2 hp
  have hc7 : JCΦ 15 (Ω ×ˢ Yint) (fun _ : P × ℝ => Ga p) β 7 := JCΦ.const hOd hGa0
  have hg0 : JCΦ 15 (Ω ×ˢ Yint) (fun q => U q * Ga p) β 8 := JCΦ.mul hOd hβ0 (by norm_num) hU hc7 (by norm_num)
  have hg1 : JCΦ 15 (Ω ×ˢ Yint) (fun q => U q * divInt G A q) β 8 := JCΦ.mul hOd hβ0 (by norm_num) hU hIG (by norm_num)
  have hb8 : 0 ≤ Φb^[8] β := Φb_iter_nonneg hβ0 8
  obtain ⟨hcd0, hb0⟩ := dY_bound hO hb8 (hg0 : JC 15 _ _ _) hpO
  obtain ⟨hcd1, hb1⟩ := dY_bound hO hb8 (hg1 : JC 15 _ _ _) hpO
  have hSo : IsOpen {s : ℝ | (p, s) ∈ Ω ×ˢ Yint} := hO.preimage (Continuous.prodMk_right p)
  have hS : ∀ᶠ s in 𝓝 Y, (p, s) ∈ Ω ×ˢ Yint := hSo.mem_nhds hpO
  have hfun : (fun s : ℝ => fderiv ℝ V (p, s) (v, 0)) =ᶠ[𝓝 Y] fun s => e * ((∑ k ∈ Finset.range 5, A p ^ k *
      (s ^ (4 - k) * (U (p, s) * Ga p))) + s ^ 5 * (U (p, s) * divInt G A (p, s))) := by
    filter_upwards [hS] with s hs
    rw [hEq (p, s) hs]
    simp only
    congr 1
    rw [mul_add, Finset.sum_mul, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun k _ => by ring
    · ring
  rw [hfun.iteratedDeriv_eq n, iteratedDeriv_const_mul_field]
  have hmain := weighted_E1D (n := n) (g0 := fun s => U (p, s) * Ga p) (g1 := fun s => U (p, s) * divInt G A (p, s))
    (Y := Y) (A := A p) (β := (Nat.factorial 15 : ℝ) * Φb^[8] β) hY0 hA0 (by have := hY.2; linarith) (by have := hAY p hp; linarith [this.2])
    (hcd0.of_le (by exact_mod_cast hn)) (hcd1.of_le (by exact_mod_cast hn)) (fun k hk => hb0 k (hk.trans hn))
    (fun k hk => hb1 k (hk.trans hn))
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left hmain (abs_nonneg e)

/-- info: 'FormalResearch.SignUncertainty.dY_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dY_bound

/-- info: 'FormalResearch.SignUncertainty.divInt_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms divInt_mul

/-- info: 'FormalResearch.SignUncertainty.E_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms E_eq

/-- info: 'FormalResearch.SignUncertainty.E_build' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms E_build

/-- info: 'FormalResearch.SignUncertainty.E_jets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms E_jets

end Bridge
end FormalResearch.SignUncertainty
