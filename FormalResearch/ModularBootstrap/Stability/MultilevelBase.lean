module

public import FormalResearch.ModularBootstrap.Stability.HbStability
public import Mathlib.LinearAlgebra.Lagrange

/-!
# Multilevel Stability Base & Common-Shift Inequality (`se:terminal-stability`, `se:common-shift`)

Source: `CFT/modular_bootstrap/paper/soft_edge_two_level_stability.tex`, Theorem `se:terminal-stability`
and equation \eqref{se:common-shift}, for every polynomial Hermite–Biehler pair `(P, Q)`
(`AiryPQHB P Q`, `Q ≠ 0`).

Here `S = hbTopZeros hHB hQ` is the set of the `m = at47_m P Q` largest zeros of `N = P Ai + Q Ai'`,
`t_m = hbMinZero hHB hQ`, and `G_N = hbExtremal hHB hQ`.

* `AiryG.densityHyp_of_max_zero`: `DensityHyp` with `δ = max (∫ Re f) 0 + τ(R)` (allowing negative integrals).
* `hbNodeCoeff`: `b_t = D(t) / (‖G_N‖₁ ∏_{s ∈ S \ {t}} (s - t))`.
* `hbExtremal_deriv_node_mul`, `hb_deriv_node_re`, `hb_dslope_integral_re`: `-ω_t G_N'(t) / ‖G_N‖₁ = b_t`
  and `-∫ dslope G_N t = D(t) / ∏_{s ∈ S \ {t}} (s - t)` for every `t ∈ S`.
* `hb_sub_below_gap`, `hb_nodes_min_gap`, `hb_quotient_of_subset`: zero-gap below `t_m` and `AiryG` quotients.
* `hbCommonShift_sum_pos`, `hbCommonShift_lt_one`: `∑_{t ∈ S} b_t > 0` and
  `∑_{t ∈ S \ {t_m}} (-b_t / b_{t_m}) < 1` (\eqref{se:common-shift}).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set Polynomial
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.Stability

open FormalResearch.Special FormalResearch.ModularBootstrap.Blowup
  FormalResearch.ModularBootstrap.ConcreteBootstrap FormalResearch.SignUncertainty

/-! ### Part 1: `DensityHyp` allowing negative `∫ Re f` -/

/-- Density hypotheses for any norm-one `f ∈ 𝒢` satisfying `f ≥ 0` on `(-∞, uT]`, using
`δ = max (∫ Re f) 0 + τ(R)` so `∫ Re f` may have either sign. -/
lemma AiryG.densityHyp_of_max_zero {f : ℂ → ℂ} (hf : AiryG f)
    (hn : ∫ x : ℝ, ‖f (x : ℂ)‖ = 1) {R uT : ℝ} (hR : 1 ≤ R)
    (hRu : -R ≤ uT) (hnn : ∀ x : ℝ, x ≤ uT → 0 ≤ (f (x : ℂ)).re) :
    DensityHyp (4 * π)⁻¹ R 0 (max (∫ x : ℝ, (f (x : ℂ)).re) 0 + tailBound (4 * π)⁻¹ R) f uT := by
  have hR0 : 0 ≤ R := by linarith
  have hτ := hf.tail_Ioi hn hR
  have hint_g : Integrable (fun x : ℝ => (f (x : ℂ)).re) := hf.integrable_re
  have hint_n : Integrable (fun x : ℝ => ‖f (x : ℂ)‖) := hf.integrable_norm
  have hsplit : ∀ (φ : ℝ → ℝ), Integrable φ → ∀ a : ℝ,
      (∫ x in Iic R, φ x) - (∫ x in Iic a, φ x) = ∫ x in a..R, φ x := fun φ hφ a =>
    intervalIntegral.integral_Iic_sub_Iic hφ.integrableOn hφ.integrableOn
  have htot : ∀ (φ : ℝ → ℝ), Integrable φ → (∫ x in Iic R, φ x) + (∫ x in Ioi R, φ x) = ∫ x, φ x :=
    fun φ hφ => intervalIntegral.integral_Iic_add_Ioi hφ.integrableOn hφ.integrableOn
  refine
    { analytic := fun z _ => hf.diff.analyticAt z
      real := fun x _ => hf.real x
      env := ?_
      nonneg := fun x _ hx => hnn x hx
      l1 := ?_
      neg := ?_
      top := ?_ }
  · intro u _ hu
    have h1 := hf.env_sharp hu
    have hre := re_cpow_half_pos_of_cut hu
    have hu_ne : u ≠ 0 := fun h0 => hu (by simp [h0])
    have hu_norm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
    have hB := hf.norm_Iic_le hn
    have he := airyEnv_pos u
    have hq : 0 ≤ ‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹ :=
      mul_nonneg (Real.rpow_nonneg hu_norm_pos.le _) (inv_nonneg.mpr hre.le)
    calc ‖f u‖ ≤ (4 * π)⁻¹ * (∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖) * airyEnv u *
          ‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹ := h1
      _ = (4 * π)⁻¹ * (∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖) * airyEnv u *
          (‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹) := by ring
      _ ≤ (4 * π)⁻¹ * 1 * airyEnv u * (‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹) := by
          gcongr
      _ = _ := by simp [mul_assoc]
  · rw [intervalIntegral.integral_of_le (by linarith)]
    rw [← hn]
    exact setIntegral_le_integral hint_n (Eventually.of_forall fun x => norm_nonneg _)
  · set φ : ℝ → ℝ := fun x => max 0 (-(f (x : ℂ)).re) with hφ
    have hφ_int : Integrable φ :=
      hint_g.neg_part.congr (Eventually.of_forall fun x => max_comm _ _)
    have hφ_eq : ∀ x : ℝ, φ x = (‖f (x : ℂ)‖ - (f (x : ℂ)).re) / 2 := by
      intro x
      rw [hf.norm_real x]
      rcases le_total 0 (f (x : ℂ)).re with h | h
      · rw [hφ]; simp only; rw [max_eq_left (by linarith), abs_of_nonneg h]; ring
      · rw [hφ]; simp only; rw [max_eq_right (by linarith), abs_of_nonpos h]; ring
    have hφ_val : ∫ x : ℝ, φ x = (1 - ∫ x : ℝ, (f (x : ℂ)).re) / 2 := by
      simp_rw [hφ_eq]
      rw [integral_div, integral_sub hint_n hint_g, hn]
    have hφ_left : ∫ x in Iic (-R), φ x = 0 := by
      refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
      have := hnn x (le_trans (mem_Iic.mp hx) (by linarith))
      rw [hφ]; exact max_eq_left (by linarith)
    have hφ_right : ∫ x in Ioi R, φ x ≤ tailBound (4 * π)⁻¹ R := by
      refine le_trans (setIntegral_mono hφ_int.integrableOn hint_n.integrableOn fun x => ?_) hτ
      rw [hφ]
      refine max_le (norm_nonneg _) ?_
      exact (neg_le_abs _).trans (by rw [hf.norm_real x])
    have h1 := hsplit φ hφ_int (-R)
    have h2 := htot φ hφ_int
    rw [hφ_left, sub_zero] at h1
    have hmax1 : ∫ x : ℝ, (f (x : ℂ)).re ≤ max (∫ x : ℝ, (f (x : ℂ)).re) 0 := le_max_left _ _
    have hmax0 : 0 ≤ max (∫ x : ℝ, (f (x : ℂ)).re) 0 := le_max_right _ _
    linarith only [hφ_val, hφ_right, h1, h2, hmax1, hmax0]
  · intro R' hR' hR'u
    set g : ℝ → ℝ := fun x => (f (x : ℂ)).re with hg
    have h1 := hsplit g hint_g (-R')
    have h2 := htot g hint_g
    have hleft : 0 ≤ ∫ x in Iic (-R'), g x :=
      setIntegral_nonneg measurableSet_Iic fun x hx => hnn x (le_trans (mem_Iic.mp hx) hR'u)
    have hright : -(∫ x in Ioi R, g x) ≤ tailBound (4 * π)⁻¹ R := by
      rw [← integral_neg]
      refine le_trans (setIntegral_mono hint_g.neg.integrableOn hint_n.integrableOn fun x => ?_) hτ
      rw [hg]
      exact (neg_le_abs _).trans (by rw [hf.norm_real x])
    have hmax1 : ∫ x : ℝ, (f (x : ℂ)).re ≤ max (∫ x : ℝ, (f (x : ℂ)).re) 0 := le_max_left _ _
    linarith only [h1, h2, hleft, hright, hmax1]

/-! ### Part 2: Nodal properties, `hbNodeCoeff`, and subset quotients -/

section HBMultilevel

variable {P Q : ℝ[X]} (hHB : AiryPQHB P Q) (hQ : Q ≠ 0)

/-- The slope coefficient `b_t = D(t) / (‖G_N‖₁ ∏_{s ∈ S \ {t}} (s - t))` at `t ∈ S`. -/
noncomputable def hbNodeCoeff (t : ℝ) : ℝ :=
  airyPQDr P Q t /
    (profileMass (hbExtremal hHB hQ) * ∏ s ∈ (hbTopZeros hHB hQ).erase t, (s - t))

private lemma hb_deriv_im_zero' {h : ℂ → ℂ} (hd : Differentiable ℂ h)
    (hreal : ∀ x : ℝ, (h (x : ℂ)).im = 0) (x : ℝ) : (deriv h (x : ℂ)).im = 0 := by
  have hdG : HasDerivAt (fun t : ℝ => h (t : ℂ)) (deriv h (x : ℂ)) x := by
    simpa only [mul_one] using (hd (x : ℂ)).hasDerivAt.comp_ofReal
  have hdim : HasDerivAt (fun t : ℝ => (h (t : ℂ)).im) (deriv h (x : ℂ)).im x :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hdG
  have hconst : (fun t : ℝ => (h (t : ℂ)).im) = fun _ => (0 : ℝ) := funext hreal
  rw [hconst] at hdim
  exact hdim.unique (hasDerivAt_const _ _)

/-- For every `t ∈ S = hbTopZeros hHB hQ`,
`G_N'(t) ∏_{s ∈ S \ {t}} (s - t) = -N'(t)²`. -/
lemma hbExtremal_deriv_node_mul {t : ℝ} (ht : t ∈ hbTopZeros hHB hQ) :
    deriv (hbExtremal hHB hQ) (t : ℂ) *
        ∏ s ∈ (hbTopZeros hHB hQ).erase t, ((s : ℂ) - (t : ℂ)) =
      -(deriv (airyPQN P Q) (t : ℂ) ^ 2) := by
  classical
  set S := hbTopZeros hHB hQ
  set S' := S.erase t
  set G := hbExtremal hHB hQ
  set N := airyPQN P Q
  have hs := hbTopZeros_spec hHB hQ
  have hG := hbExtremal_spec hHB hQ
  have hG_t : G (t : ℂ) = 0 := hG.2.2.2.2.2.2.1 t ht
  have hN_t : N (t : ℂ) = 0 := hs.2.1 t ht
  have hD1d : Differentiable ℂ (dslope G (t : ℂ)) :=
    EntireDiv.differentiable_dslope_entire hG.1 _
  have hD2d : Differentiable ℂ (dslope N (t : ℂ)) :=
    EntireDiv.differentiable_dslope_entire (differentiable_airyPQN P Q) _
  have hG_fac : ∀ z : ℂ, G z = (z - (t : ℂ)) * dslope G (t : ℂ) z := fun z => by
    have := sub_smul_dslope G (t : ℂ) z
    rw [smul_eq_mul, hG_t, sub_zero] at this
    exact this.symm
  have hN_fac : ∀ z : ℂ, N z = (z - (t : ℂ)) * dslope N (t : ℂ) z := fun z => by
    have := sub_smul_dslope N (t : ℂ) z
    rw [smul_eq_mul, hN_t, sub_zero] at this
    exact this.symm
  have hpr_fac : ∀ z : ℂ, at47_pr S z = (z - (t : ℂ)) * at47_pr S' z := fun z => by
    unfold at47_pr
    exact (Finset.mul_prod_erase S (fun s => z - (s : ℂ)) ht).symm
  have hcancel : ∀ z : ℂ, z ≠ (t : ℂ) →
      dslope G (t : ℂ) z * at47_pr S' z =
        (((-1 : ℝ) ^ S.card : ℝ) : ℂ) * dslope N (t : ℂ) z ^ 2 := by
    intro z hz
    have hne : (z - (t : ℂ)) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hz)
    have h1 : G z * at47_pr S z = (((-1 : ℝ) ^ S.card : ℝ) : ℂ) * N z ^ 2 := hG.2.1 z
    rw [hG_fac z, hN_fac z, hpr_fac z] at h1
    have h2 : (z - (t : ℂ)) ^ 2 * (dslope G (t : ℂ) z * at47_pr S' z) =
        (z - (t : ℂ)) ^ 2 * ((((-1 : ℝ) ^ S.card : ℝ) : ℂ) * dslope N (t : ℂ) z ^ 2) := by
      calc (z - (t : ℂ)) ^ 2 * (dslope G (t : ℂ) z * at47_pr S' z)
          = (z - (t : ℂ)) * dslope G (t : ℂ) z * ((z - (t : ℂ)) * at47_pr S' z) := by ring
        _ = (((-1 : ℝ) ^ S.card : ℝ) : ℂ) * ((z - (t : ℂ)) * dslope N (t : ℂ) z) ^ 2 := h1
        _ = _ := by ring
    exact mul_left_cancel₀ hne h2
  have hdense : Dense ({(t : ℂ)}ᶜ : Set ℂ) :=
    (Set.finite_singleton (t : ℂ)).countable.dense_compl ℂ
  have hcont_l : Continuous (fun z : ℂ => dslope G (t : ℂ) z * at47_pr S' z) :=
    hD1d.continuous.mul (at47_pr_differentiable S').continuous
  have hcont_r : Continuous (fun z : ℂ =>
      (((-1 : ℝ) ^ S.card : ℝ) : ℂ) * dslope N (t : ℂ) z ^ 2) :=
    continuous_const.mul (hD2d.continuous.pow 2)
  have hext := Continuous.ext_on hdense hcont_l hcont_r hcancel
  have htm_eq := congrFun hext (t : ℂ)
  rw [dslope_same, dslope_same] at htm_eq
  have hcard : S.card = S'.card + 1 := (Finset.card_erase_add_one ht).symm
  have hsign : (-1 : ℝ) ^ S.card = -((-1 : ℝ) ^ S'.card) := by
    rw [hcard, pow_succ]; ring
  have hpr_flip : at47_pr S' (t : ℂ) =
      (((-1 : ℝ) ^ S'.card : ℝ) : ℂ) * ∏ s ∈ S', ((s : ℂ) - (t : ℂ)) := by
    unfold at47_pr
    have : ((-1 : ℂ) ^ S'.card) * ∏ s ∈ S', ((s : ℂ) - (t : ℂ)) =
        ∏ s ∈ S', ((t : ℂ) - (s : ℂ)) := by
      rw [← Finset.prod_const (b := (-1 : ℂ)) (s := S'), ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun s _ => by ring
    push_cast
    exact this.symm
  rw [hpr_flip, hsign] at htm_eq
  have hε0 : ((-1 : ℂ) ^ S'.card) ≠ 0 := pow_ne_zero _ (by norm_num)
  push_cast at htm_eq
  have htm_eq' : ((-1 : ℂ) ^ S'.card) *
      (deriv G (t : ℂ) * ∏ s ∈ S', ((s : ℂ) - (t : ℂ))) =
      ((-1 : ℂ) ^ S'.card) * (-(deriv N (t : ℂ) ^ 2)) := by
    calc ((-1 : ℂ) ^ S'.card) * (deriv G (t : ℂ) * ∏ s ∈ S', ((s : ℂ) - (t : ℂ)))
        = deriv G (t : ℂ) * ((-1 : ℂ) ^ S'.card * ∏ s ∈ S', ((s : ℂ) - (t : ℂ))) := by ring
      _ = (-((-1 : ℂ) ^ S'.card)) * deriv N (t : ℂ) ^ 2 := htm_eq
      _ = _ := by ring
  exact mul_left_cancel₀ hε0 htm_eq'

lemma hb_deriv_node_re {t : ℝ} (ht : t ∈ hbTopZeros hHB hQ) :
    (deriv (hbExtremal hHB hQ) (t : ℂ)).re *
        ∏ s ∈ (hbTopZeros hHB hQ).erase t, (s - t) =
      -((airyPQN' P Q (t : ℂ)).re ^ 2) := by
  classical
  set S := hbTopZeros hHB hQ
  set S' := S.erase t
  have hmul := hbExtremal_deriv_node_mul hHB hQ ht
  have hN' : deriv (airyPQN P Q) (t : ℂ) = (((airyPQN' P Q (t : ℂ)).re : ℝ) : ℂ) := by
    rw [deriv_airyPQN, airyPQN'_ofReal, Complex.ofReal_re]
  have hprod : (∏ s ∈ S', ((s : ℂ) - (t : ℂ))) = ((∏ s ∈ S', (s - t) : ℝ) : ℂ) := by
    push_cast; rfl
  have hG_real : (deriv (hbExtremal hHB hQ) (t : ℂ)).im = 0 :=
    hb_deriv_im_zero' (hbExtremal_spec hHB hQ).1 (hbExtremal_spec hHB hQ).2.2.2.2.1 t
  have hG_cast : deriv (hbExtremal hHB hQ) (t : ℂ) =
      (((deriv (hbExtremal hHB hQ) (t : ℂ)).re : ℝ) : ℂ) :=
    Complex.ext rfl hG_real
  rw [hN', hprod, hG_cast] at hmul
  exact_mod_cast hmul

lemma hb_prod_erase_ne_zero (t : ℝ) :
    ∏ s ∈ (hbTopZeros hHB hQ).erase t, (s - t) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun s hs => ?_
  exact sub_ne_zero.mpr (Finset.mem_erase.mp hs).1

lemma hbNodeCoeff_eq_weight_deriv {t : ℝ} (ht : t ∈ hbTopZeros hHB hQ) :
    hbNodeCoeff hHB hQ t =
      -(airyPQDr P Q t / (airyPQN' P Q (t : ℂ)).re ^ 2) *
        (deriv (hbExtremal hHB hQ) (t : ℂ)).re / profileMass (hbExtremal hHB hQ) := by
  have hs := hbTopZeros_spec hHB hQ
  obtain ⟨_, hN'⟩ := airyPQ_zero_weight_pos hHB hQ (hs.2.1 t ht)
  have hN're : (airyPQN' P Q (t : ℂ)).re ≠ 0 := by
    intro h0; apply hN'; rw [airyPQN'_ofReal, Complex.ofReal_re] at h0; rw [airyPQN'_ofReal, h0]; simp
  have hprod_ne := hb_prod_erase_ne_zero hHB hQ t
  have hL_ne : profileMass (hbExtremal hHB hQ) ≠ 0 :=
    (hbExtremalProfile (HermiteBiehlerData.ofQNeZero hHB hQ)).mass_pos.ne'
  have hre := hb_deriv_node_re hHB hQ ht
  have h_eq : (deriv (hbExtremal hHB hQ) (t : ℂ)).re =
      -((airyPQN' P Q (t : ℂ)).re ^ 2) / ∏ s ∈ (hbTopZeros hHB hQ).erase t, (s - t) :=
    eq_div_of_mul_eq hprod_ne hre
  unfold hbNodeCoeff
  rw [h_eq]
  field_simp [hN're, hprod_ne, hL_ne]

lemma hbNodeCoeff_tm_pos : 0 < hbNodeCoeff hHB hQ (hbMinZero hHB hQ) := by
  have hs := hbTopZeros_spec hHB hQ
  obtain ⟨hD, _⟩ := airyPQ_zero_weight_pos hHB hQ (hs.2.1 _ hs.2.2.2.1)
  have hL := (hbExtremalProfile (HermiteBiehlerData.ofQNeZero hHB hQ)).mass_pos
  have hprod := hb_prod_erase_pos hHB hQ
  unfold hbNodeCoeff
  exact div_pos hD (mul_pos hL hprod)

/-- Every zero of `N` outside `S = hbTopZeros hHB hQ` stays bounded away below `t_m`. -/
lemma hb_sub_below_gap :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, airyPQN P Q (x : ℂ) = 0 → x ∉ hbTopZeros hHB hQ →
      x ≤ hbMinZero hHB hQ - δ := by
  classical
  set S := hbTopZeros hHB hQ
  set tm := hbMinZero hHB hQ
  have hs := hbTopZeros_spec hHB hQ
  have hfin_C := airyPQ_zeros_finite hHB (|tm| + 1)
  have hfin_R : {x : ℝ | airyPQN P Q (x : ℂ) = 0 ∧ x ∈ Icc (tm - 1) tm}.Finite := by
    refine (hfin_C.preimage Complex.ofReal_injective.injOn).subset fun x hx => ?_
    refine ⟨hx.1, ?_⟩
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [neg_abs_le tm, hx.2.1], by linarith [le_abs_self tm, hx.2.2]⟩
  let Z : Finset ℝ := hfin_R.toFinset \ S
  by_cases hne : Z.Nonempty
  · let xmax := Z.max' hne
    have hmem : xmax ∈ Z := Finset.max'_mem _ hne
    have hxZ := Finset.mem_sdiff.mp hmem
    have hxR := hfin_R.mem_toFinset.mp hxZ.1
    have hlt : xmax < tm := hs.2.2.1 xmax hxR.1 hxZ.2 tm hs.2.2.2.1
    refine ⟨min 1 (tm - xmax), lt_min one_pos (sub_pos.mpr hlt), fun x hx hxS => ?_⟩
    by_cases hx1 : x < tm - 1
    · have : min 1 (tm - xmax) ≤ 1 := min_le_left _ _
      linarith
    · have hxle : x < tm := hs.2.2.1 x hx hxS tm hs.2.2.2.1
      have hxin : x ∈ Z := Finset.mem_sdiff.mpr ⟨hfin_R.mem_toFinset.mpr ⟨hx, ⟨by linarith, hxle.le⟩⟩, hxS⟩
      have hle_max : x ≤ xmax := Finset.le_max' Z x hxin
      have : min 1 (tm - xmax) ≤ tm - xmax := min_le_right _ _
      linarith
  · refine ⟨1, one_pos, fun x hx hxS => ?_⟩
    by_contra hgt
    push Not at hgt
    have hxle : x < tm := hs.2.2.1 x hx hxS tm hs.2.2.2.1
    have hxin : x ∈ Z := Finset.mem_sdiff.mpr ⟨hfin_R.mem_toFinset.mpr ⟨hx, ⟨by linarith, hxle.le⟩⟩, hxS⟩
    exact hne ⟨x, hxin⟩

/-- Minimum pairwise gap among distinct nodes of `S = hbTopZeros hHB hQ` (or `1` if `|S| = 1`). -/
lemma hb_nodes_min_gap :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ hbTopZeros hHB hQ, ∀ t ∈ hbTopZeros hHB hQ, s ≠ t → δ ≤ |s - t| := by
  classical
  set S := hbTopZeros hHB hQ
  let P_off : Finset (ℝ × ℝ) := (S ×ˢ S).filter fun p => p.1 ≠ p.2
  by_cases hne : P_off.Nonempty
  · refine ⟨P_off.inf' hne fun p => |p.1 - p.2|, ?_, fun s hs t ht hst => ?_⟩
    · rw [Finset.lt_inf'_iff]
      intro p hp
      exact abs_sub_pos.mpr (Finset.mem_filter.mp hp).2
    · exact Finset.inf'_le (fun p : ℝ × ℝ => |p.1 - p.2|) (Finset.mem_filter.mpr ⟨Finset.mk_mem_product hs ht, hst⟩)
  · refine ⟨1, one_pos, fun s hs t ht hst => ?_⟩
    exact absurd ⟨(s, t), Finset.mem_filter.mpr ⟨Finset.mk_mem_product hs ht, hst⟩⟩ hne

/-- Any subset quotient `G_N(u) / ∏_{t ∈ A} (u - t)` (`A ⊆ S`) lies in `AiryG`. -/
lemma hb_quotient_of_subset (A : Finset ℝ) (hA : A ⊆ hbTopZeros hHB hQ) :
    ∃ ψ : ℂ → ℂ, AiryG ψ ∧ ∀ u : ℂ, hbExtremal hHB hQ u = ψ u * ∏ t ∈ A, (u - (t : ℂ)) := by
  set G := hbExtremal hHB hQ
  have hG := hbExtremal_spec hHB hQ
  obtain ⟨C, ν, hC, hb⟩ := hG.2.2.2.1
  obtain ⟨ψ, hψd, hψeq, C', hC', hb'⟩ :=
    at47_div_finset A hG.1 (fun t ht => hG.2.2.2.2.2.2.1 t (hA ht)) hC hb
  have hψreal : ∀ x : ℝ, (ψ (x : ℂ)).im = 0 := by
    have hcont_im : Continuous (fun x : ℝ => (ψ (x : ℂ)).im) :=
      Complex.continuous_im.comp (hψd.continuous.comp continuous_ofReal)
    have hzero_on : ∀ x : ℝ, x ∉ (A : Set ℝ) → (ψ (x : ℂ)).im = 0 := by
      intro x hx
      have heq := hψeq (x : ℂ)
      have hpr_ne : (∏ t ∈ A, ((x : ℂ) - (t : ℂ))) ≠ 0 := by
        refine Finset.prod_ne_zero_iff.mpr fun t ht => ?_
        exact sub_ne_zero.mpr fun h => hx (Complex.ofReal_injective h ▸ ht)
      have hprod_cast : (∏ t ∈ A, ((x : ℂ) - (t : ℂ))) = ((∏ t ∈ A, (x - t) : ℝ) : ℂ) := by
        push_cast; rfl
      have hG_cast : G (x : ℂ) = (((G (x : ℂ)).re : ℝ) : ℂ) :=
        Complex.ext rfl (hG.2.2.2.2.1 x)
      have hψ_val : ψ (x : ℂ) = G (x : ℂ) / ∏ t ∈ A, ((x : ℂ) - (t : ℂ)) :=
        eq_div_of_mul_eq hpr_ne heq.symm
      rw [hψ_val, hG_cast, hprod_cast, ← Complex.ofReal_div, Complex.ofReal_im]
    have hdense : Dense ((A : Set ℝ)ᶜ) := A.finite_toSet.countable.dense_compl ℝ
    exact fun x => congrFun (Continuous.ext_on hdense hcont_im continuous_zero hzero_on) x
  have hψint : Integrable (fun x : ℝ => ψ (x : ℂ)) := by
    let tm := hbMinZero hHB hQ
    let S := hbTopZeros hHB hQ
    have htm_mem : tm ∈ S := (hbTopZeros_spec hHB hQ).2.2.2.1
    let R : ℝ := S.sup' ⟨tm, htm_mem⟩ (fun t => |t|) + 1
    have h_out : IntegrableOn (fun x : ℝ => ψ (x : ℂ)) (Icc (-R) R)ᶜ := by
      have hG_out : Integrable (fun x : ℝ => G (x : ℂ)) (volume.restrict (Icc (-R) R)ᶜ) :=
        hG.2.2.1.integrableOn
      refine hG_out.mono ?_ ?_
      · exact (hψd.continuous.comp continuous_ofReal).aestronglyMeasurable.restrict
      · filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with x hx
        have hRx : R ≤ |x| := by
          by_contra hlt; push Not at hlt
          exact hx (abs_le.mp hlt.le)
        have h1_le : 1 ≤ ‖∏ t ∈ A, ((x : ℂ) - (t : ℂ))‖ := by
          rw [norm_prod]
          have h_each : ∀ t ∈ A, 1 ≤ ‖(x : ℂ) - (t : ℂ)‖ := fun t ht => by
            have hle_R : |t| ≤ S.sup' ⟨tm, htm_mem⟩ (fun s => |s|) :=
              Finset.le_sup' (fun s => |s|) (hA ht)
            rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
            have := abs_sub_abs_le_abs_sub x t
            linarith
          have hprod_ge : ∀ T : Finset ℝ, (∀ t ∈ T, (1 : ℝ) ≤ ‖(x : ℂ) - (t : ℂ)‖) →
              1 ≤ ∏ t ∈ T, ‖(x : ℂ) - (t : ℂ)‖ := fun T => by
            induction T using Finset.induction_on with
            | empty => intro _; simp
            | @insert a s ha ih =>
              intro h
              rw [Finset.prod_insert ha]
              exact one_le_mul_of_one_le_of_one_le
                (h a (Finset.mem_insert_self _ _))
                (ih fun t ht => h t (Finset.mem_insert_of_mem ht))
          exact hprod_ge A h_each
        have hnorm := congrArg norm (hψeq (x : ℂ))
        rw [norm_mul] at hnorm
        have hle : ‖ψ (x : ℂ)‖ ≤ ‖ψ (x : ℂ)‖ * ‖∏ t ∈ A, ((x : ℂ) - (t : ℂ))‖ :=
          le_mul_of_one_le_right (norm_nonneg _) h1_le
        dsimp only [G]
        linarith only [hnorm, hle]
    have h_in : IntegrableOn (fun x : ℝ => ψ (x : ℂ)) (Icc (-R) R) :=
      (hψd.continuous.comp continuous_ofReal).continuousOn.integrableOn_Icc
    have hun := h_in.union h_out
    rwa [Set.union_compl_self, integrableOn_univ] at hun
  exact ⟨ψ, ⟨hψd, hψint, ⟨C', ν, hC', hb'⟩, hψreal⟩, hψeq⟩

/-- Quadrature formula for `-dslope G_N t` at any `t ∈ S = hbTopZeros hHB hQ`:
`-(∫ x : ℝ, (dslope G_N t (x : ℂ)).re) = D(t) / ∏_{s ∈ S \ {t}} (s - t) = ‖G_N‖₁ * b_t`. -/
lemma hb_dslope_integral_re {t : ℝ} (ht : t ∈ hbTopZeros hHB hQ) :
    -(∫ x : ℝ, (dslope (hbExtremal hHB hQ) (t : ℂ) (x : ℂ)).re) =
      profileMass (hbExtremal hHB hQ) * hbNodeCoeff hHB hQ t := by
  classical
  set S := hbTopZeros hHB hQ
  set G := hbExtremal hHB hQ
  have hs := hbTopZeros_spec hHB hQ
  have hG := hbExtremal_spec hHB hQ
  have hGt : G (t : ℂ) = 0 := hG.2.2.2.2.2.2.1 t ht
  obtain ⟨ψ, hψG, hψeq⟩ := hb_quotient_of_subset hHB hQ {t} (Finset.singleton_subset_iff.mpr ht)
  have hψ_dslope : ∀ z : ℂ, ψ z = dslope G (t : ℂ) z := by
    intro z
    by_cases hz : z = (t : ℂ)
    · have hcont := Continuous.ext_on ((Set.finite_singleton (t : ℂ)).countable.dense_compl ℂ)
        hψG.diff.continuous (EntireDiv.differentiable_dslope_entire hG.1 (t : ℂ)).continuous
        fun w (hw : w ≠ (t : ℂ)) => by
          have h1 : hbExtremal hHB hQ w = ψ w * (w - (t : ℂ)) := by
            simpa [Finset.prod_singleton] using hψeq w
          have h2 : (w - (t : ℂ)) * dslope G (t : ℂ) w = hbExtremal hHB hQ w := by
            have := sub_smul_dslope G (t : ℂ) w
            rw [smul_eq_mul, hGt, sub_zero] at this
            exact this
          have h3 : ψ w * (w - (t : ℂ)) = dslope G (t : ℂ) w * (w - (t : ℂ)) := by
            rw [← h1, ← h2, mul_comm]
          exact mul_right_cancel₀ (sub_ne_zero.mpr hw) h3
      exact congrFun hcont z
    · have h1 : hbExtremal hHB hQ z = ψ z * (z - (t : ℂ)) := by
        simpa [Finset.prod_singleton] using hψeq z
      have h2 : (z - (t : ℂ)) * dslope G (t : ℂ) z = hbExtremal hHB hQ z := by
        have := sub_smul_dslope G (t : ℂ) z
        rw [smul_eq_mul, hGt, sub_zero] at this
        exact this
      have h3 : ψ z * (z - (t : ℂ)) = dslope G (t : ℂ) z * (z - (t : ℂ)) := by
        rw [← h1, ← h2, mul_comm]
      exact mul_right_cancel₀ (sub_ne_zero.mpr hz) h3
  obtain ⟨C', ν', hC', hb'⟩ := hψG.growth
  have hsum := airyPQ_hasSum_unc hHB hQ hψG.diff hψG.integrable hC' hb'
  let a_term : {z : ℂ // airyPQN P Q z = 0} → ℂ := fun z =>
    ψ z.1 * (airyPQD P Q z.1 / airyPQN' P Q z.1 ^ 2)
  let zt : {z : ℂ // airyPQN P Q z = 0} := ⟨(t : ℂ), hs.2.1 t ht⟩
  have hsingle : HasSum a_term (a_term zt) := by
    refine hasSum_single zt fun z hz => ?_
    have hzeq : z.1 ≠ (t : ℂ) := fun h => hz (Subtype.ext h)
    have hGz : hbExtremal hHB hQ z.1 = 0 := by
      have h1 := hG.2.1 z.1
      rw [z.2, zero_pow two_ne_zero, mul_zero] at h1
      by_cases hpr : at47_pr S z.1 = 0
      · obtain ⟨s, hs_mem, hzs⟩ := Finset.prod_eq_zero_iff.mp (by simpa [at47_pr] using hpr)
        have : z.1 = (s : ℂ) := sub_eq_zero.mp hzs
        rw [this]; exact hG.2.2.2.2.2.2.1 s hs_mem
      · exact (mul_eq_zero.mp h1).resolve_right hpr
    have hψz : ψ z.1 = 0 := by
      have h1 := hψeq z.1
      rw [Finset.prod_singleton, hGz] at h1
      exact (mul_eq_zero.mp h1.symm).resolve_right (sub_ne_zero.mpr hzeq)
    simp [a_term, hψz]
  have hval := hsum.unique hsingle
  have hre := congrArg Complex.re hval
  rw [← hψG.re_integral] at hre
  have hψt : ψ (t : ℂ) = deriv G (t : ℂ) := by
    rw [hψ_dslope, dslope_same]
  have hψt_real : (deriv G (t : ℂ)).im = 0 :=
    hb_deriv_im_zero' hG.1 hG.2.2.2.2.1 t
  have hψt_cast : ψ (t : ℂ) = (((deriv G (t : ℂ)).re : ℝ) : ℂ) := by
    rw [hψt]; exact Complex.ext rfl hψt_real
  have hD_cast : airyPQD P Q (t : ℂ) = ((airyPQDr P Q t : ℝ) : ℂ) := airyPQD_ofReal P Q t
  have hN'_cast : airyPQN' P Q (t : ℂ) = (((airyPQN' P Q (t : ℂ)).re : ℝ) : ℂ) := by
    rw [airyPQN'_ofReal, Complex.ofReal_re]
  have h_re_val : (a_term zt).re =
      (deriv G (t : ℂ)).re * (airyPQDr P Q t / (airyPQN' P Q (t : ℂ)).re ^ 2) := by
    dsimp [a_term, zt]
    conv_lhs => rw [hψt_cast, hD_cast, hN'_cast]
    have he : (((deriv G (t : ℂ)).re : ℝ) : ℂ) *
        (((airyPQDr P Q t : ℝ) : ℂ) / (((airyPQN' P Q (t : ℂ)).re : ℝ) : ℂ) ^ 2) =
        (((deriv G (t : ℂ)).re * (airyPQDr P Q t / (airyPQN' P Q (t : ℂ)).re ^ 2) : ℝ) : ℂ) := by
      push_cast; rfl
    rw [he, Complex.ofReal_re]
  rw [h_re_val] at hre
  have h_eq_dslope : ∫ x : ℝ, (dslope G (t : ℂ) (x : ℂ)).re = ∫ x : ℝ, (ψ (x : ℂ)).re := by
    congr 1; ext x; rw [hψ_dslope]
  rw [h_eq_dslope, hre, hbNodeCoeff_eq_weight_deriv hHB hQ ht]
  have hL_ne : profileMass G ≠ 0 :=
    (hbExtremalProfile (HermiteBiehlerData.ofQNeZero hHB hQ)).mass_pos.ne'
  dsimp only [G] at hL_ne ⊢
  field_simp [hL_ne]

/-! ### Part 3: The common-shift inequality (`se:common-shift`) -/

/-- The polynomial `D(u) = P(u)(P(u) + Q'(u)) - Q(u)(P'(u) + u Q(u))` whose evaluation on `ℝ`
is `airyPQDr P Q`. -/
noncomputable def airyPQDPoly (P Q : ℝ[X]) : ℝ[X] :=
  P * (P + derivative Q) - Q * (derivative P + X * Q)

lemma airyPQDPoly_eval (P Q : ℝ[X]) (x : ℝ) : (airyPQDPoly P Q).eval x = airyPQDr P Q x := by
  unfold airyPQDPoly airyPQDr
  simp [eval_sub, eval_mul, eval_add, eval_X]

lemma airyPQDPoly_natDegree_and_coeff (P Q : ℝ[X]) (hQ : Q ≠ 0) :
    (airyPQDPoly P Q).natDegree < at47_m P Q ∧
      0 < (-1 : ℝ) ^ (at47_m P Q - 1) * (airyPQDPoly P Q).coeff (at47_m P Q - 1) := by
  set m := at47_m P Q
  have hm_ge : 2 ≤ m := by
    have := at47_m_ge_Q P Q; omega
  have hPQ : airyPQDPoly P Q = P ^ 2 + P * derivative Q - Q * derivative P - X * Q ^ 2 := by
    unfold airyPQDPoly; ring
  have hP_or_Q : m = 2 * P.natDegree + 1 ∨ m = 2 * Q.natDegree + 2 := by
    unfold m at47_m; exact max_choice _ _
  have hPdQ : (P * derivative Q).natDegree < m - 1 := by
    by_cases hdQ : derivative Q = 0
    · simp [hdQ]; omega
    · have h1 := natDegree_mul_le (p := P) (q := derivative Q)
      by_cases hQd0 : Q.natDegree = 0
      · rw [eq_C_of_natDegree_eq_zero hQd0, derivative_C] at hdQ; exact absurd rfl hdQ
      · have h2 := natDegree_derivative_lt hQd0
        rcases hP_or_Q with hm | hm
        · have hge := at47_m_ge_Q P Q
          change 2 * Q.natDegree + 2 ≤ m at hge
          omega
        · have hge := at47_m_ge_P P Q
          change 2 * P.natDegree + 1 ≤ m at hge
          omega
  have hQdP : (Q * derivative P).natDegree < m - 1 := by
    by_cases hdP : derivative P = 0
    · simp [hdP]; omega
    · have h1 := natDegree_mul_le (p := Q) (q := derivative P)
      by_cases hPd0 : P.natDegree = 0
      · rw [eq_C_of_natDegree_eq_zero hPd0, derivative_C] at hdP; exact absurd rfl hdP
      · have h2 := natDegree_derivative_lt hPd0
        rcases hP_or_Q with hm | hm
        · have hge := at47_m_ge_Q P Q
          change 2 * Q.natDegree + 2 ≤ m at hge
          omega
        · have hge := at47_m_ge_P P Q
          change 2 * P.natDegree + 1 ≤ m at hge
          omega
  rcases hP_or_Q with hm | hm
  · have hP0 : P ≠ 0 := by
      intro h0
      have h2 := at47_m_ge_Q P Q
      rw [h0, natDegree_zero] at hm
      omega
    have hm1 : m - 1 = 2 * P.natDegree := by omega
    have hQ_lt : 2 * Q.natDegree + 2 < 2 * P.natDegree + 1 := by
      have h2 := at47_m_ge_Q P Q
      change 2 * Q.natDegree + 2 ≤ m at h2
      omega
    have hP2_deg : (P ^ 2).natDegree = m - 1 := by
      have hne : (P.leadingCoeff ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 (leadingCoeff_ne_zero.mpr hP0)
      rw [natDegree_pow' hne, hm1]
    have hXQ2_deg : (X * Q ^ 2).natDegree < m - 1 := by
      have h1 := natDegree_mul_le (p := X) (q := Q ^ 2)
      have h2 := natDegree_pow_le (p := Q) (n := 2)
      simp only [natDegree_X] at h1
      omega
    have hdeg : (airyPQDPoly P Q).natDegree ≤ m - 1 := by
      rw [hPQ]
      refine (natDegree_sub_le _ _).trans (max_le ((natDegree_sub_le _ _).trans (max_le
        ((natDegree_add_le _ _).trans (max_le hP2_deg.le hPdQ.le)) hQdP.le)) hXQ2_deg.le)
    have hcoeff : (airyPQDPoly P Q).coeff (m - 1) = P.leadingCoeff ^ 2 := by
      rw [hPQ, coeff_sub, coeff_sub, coeff_add, coeff_eq_zero_of_natDegree_lt hPdQ,
        coeff_eq_zero_of_natDegree_lt hQdP, coeff_eq_zero_of_natDegree_lt hXQ2_deg,
        add_zero, sub_zero, sub_zero, ← hP2_deg, coeff_natDegree, leadingCoeff_pow]
    refine ⟨by omega, ?_⟩
    have heven : (-1 : ℝ) ^ (m - 1) = 1 := by
      rw [hm1, pow_mul, neg_one_sq, one_pow]
    rw [hcoeff, heven, one_mul]
    exact sq_pos_of_ne_zero (leadingCoeff_ne_zero.mpr hP0)
  · have hm1 : m - 1 = 2 * Q.natDegree + 1 := by omega
    have hP_le : 2 * P.natDegree + 1 < 2 * Q.natDegree + 2 := by
      have h2 := at47_m_ge_P P Q
      change 2 * P.natDegree + 1 ≤ m at h2
      omega
    have hP2_deg : (P ^ 2).natDegree < m - 1 := by
      have h2 := natDegree_pow_le (p := P) (n := 2)
      omega
    have hXQ2_deg : (X * Q ^ 2).natDegree = m - 1 := by
      have hQ2_ne : Q ^ 2 ≠ 0 := pow_ne_zero 2 hQ
      rw [natDegree_mul X_ne_zero hQ2_ne, natDegree_X,
        natDegree_pow' (pow_ne_zero 2 (leadingCoeff_ne_zero.mpr hQ)), hm1]
      ring
    have hXQ2_lc : (X * Q ^ 2).coeff (m - 1) = Q.leadingCoeff ^ 2 := by
      rw [← hXQ2_deg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_X, one_mul, leadingCoeff_pow]
    have hdeg : (airyPQDPoly P Q).natDegree ≤ m - 1 := by
      rw [hPQ]
      refine (natDegree_sub_le _ _).trans (max_le ((natDegree_sub_le _ _).trans (max_le
        ((natDegree_add_le _ _).trans (max_le hP2_deg.le hPdQ.le)) hQdP.le)) hXQ2_deg.le)
    have hcoeff : (airyPQDPoly P Q).coeff (m - 1) = -(Q.leadingCoeff ^ 2) := by
      rw [hPQ, coeff_sub, coeff_sub, coeff_add, coeff_eq_zero_of_natDegree_lt hP2_deg,
        coeff_eq_zero_of_natDegree_lt hPdQ, coeff_eq_zero_of_natDegree_lt hQdP,
        hXQ2_lc]
      ring
    refine ⟨by omega, ?_⟩
    have hodd : (-1 : ℝ) ^ (m - 1) = -1 := by
      rw [hm1, pow_succ, pow_mul, neg_one_sq, one_pow, one_mul]
    rw [hcoeff, hodd]
    have hq_pos : 0 < Q.leadingCoeff ^ 2 := sq_pos_of_ne_zero (leadingCoeff_ne_zero.mpr hQ)
    linarith

lemma lagrange_coeff_sum {S : Finset ℝ} (_hne : S.Nonempty) {D : ℝ[X]} (hdeg : D.natDegree < S.card) :
    ∑ t ∈ S, D.eval t / ∏ s ∈ S.erase t, (t - s) = D.coeff (S.card - 1) := by
  classical
  have hdeg' : D.degree < (S.card : ℕ) := by
    by_cases hD : D = 0
    · simp [hD]
    · rwa [degree_eq_natDegree hD, Nat.cast_lt]
  have hint := Lagrange.eq_interpolate (Set.injOn_id (S : Set ℝ)) hdeg' (f := D)
  have hsum : D = ∑ t ∈ S, C (D.eval t / ∏ s ∈ S.erase t, (t - s)) *
      ∏ s ∈ S.erase t, (X - C s) := by
    calc D = Lagrange.interpolate S id (fun x => D.eval (id x)) := hint
      _ = ∑ t ∈ S, C (D.eval t / ∏ s ∈ S.erase t, (t - s)) * ∏ s ∈ S.erase t, (X - C s) := by
          rw [Lagrange.interpolate_eq_sum]; rfl
  have hcoeff := congrArg (fun p : ℝ[X] => p.coeff (S.card - 1)) hsum
  have hsum_coeff : ∀ (T : Finset ℝ) (g : ℝ → ℝ[X]),
      (∑ t ∈ T, g t).coeff (S.card - 1) = ∑ t ∈ T, (g t).coeff (S.card - 1) := by
    intro T g
    induction T using Finset.induction_on with
    | empty => simp
    | @insert a s ha _ => simp [Finset.sum_insert ha]
  rw [hsum_coeff] at hcoeff
  have hterm : ∀ t ∈ S,
      (C (D.eval t / ∏ s ∈ S.erase t, (t - s)) * ∏ s ∈ S.erase t, (X - C s)).coeff (S.card - 1) =
        D.eval t / ∏ s ∈ S.erase t, (t - s) := by
    intro t ht
    set Q_t : ℝ[X] := ∏ s ∈ S.erase t, (X - C s)
    have hmon : Q_t.Monic := monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _
    have hdeg_Q : Q_t.natDegree = S.card - 1 := by
      rw [natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _]
      simp [Finset.card_erase_of_mem ht]
    rw [coeff_C_mul, ← hdeg_Q, hmon.coeff_natDegree, mul_one]
  calc ∑ t ∈ S, D.eval t / ∏ s ∈ S.erase t, (t - s)
      = ∑ t ∈ S, (C (D.eval t / ∏ s ∈ S.erase t, (t - s)) *
          ∏ s ∈ S.erase t, (X - C s)).coeff (S.card - 1) := by
        refine Finset.sum_congr rfl fun t ht => (hterm t ht).symm
    _ = D.coeff (S.card - 1) := hcoeff.symm

/-- **Common-shift inequality (`se:common-shift`)**:
`∑_{t ∈ S} b_t = (-1)^{m-1} [u^{m-1}] D / ‖G_N‖₁ > 0`. -/
theorem hbCommonShift_sum_pos : 0 < ∑ t ∈ hbTopZeros hHB hQ, hbNodeCoeff hHB hQ t := by
  classical
  set S := hbTopZeros hHB hQ
  set tm := hbMinZero hHB hQ
  have hs := hbTopZeros_spec hHB hQ
  have hS_ne : S.Nonempty := ⟨tm, hs.2.2.2.1⟩
  obtain ⟨hdeg_lt, hcoeff_pos⟩ := airyPQDPoly_natDegree_and_coeff P Q hQ
  have hdeg_S : (airyPQDPoly P Q).natDegree < S.card := by rwa [hs.1]
  have hlag := lagrange_coeff_sum hS_ne hdeg_S
  have hflip : ∀ t ∈ S,
      airyPQDr P Q t / ∏ s ∈ S.erase t, (s - t) =
        (-1 : ℝ) ^ (S.card - 1) * ((airyPQDPoly P Q).eval t / ∏ s ∈ S.erase t, (t - s)) := by
    intro t ht
    have hprod : ∏ s ∈ S.erase t, (s - t) = (-1 : ℝ) ^ (S.card - 1) * ∏ s ∈ S.erase t, (t - s) := by
      have hc : (S.erase t).card = S.card - 1 := Finset.card_erase_of_mem ht
      rw [← hc, ← Finset.prod_const (b := (-1 : ℝ)) (s := S.erase t), ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun s _ => by ring
    have hp_ne : ∏ s ∈ S.erase t, (t - s) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun s hs => sub_ne_zero.mpr (Finset.mem_erase.mp hs).1.symm
    have hsq : (-1 : ℝ) ^ (S.card - 1) * (-1 : ℝ) ^ (S.card - 1) = 1 := by rw [← mul_pow]; simp
    calc airyPQDr P Q t / ∏ s ∈ S.erase t, (s - t)
        = (airyPQDPoly P Q).eval t / ((-1 : ℝ) ^ (S.card - 1) * ∏ s ∈ S.erase t, (t - s)) := by
            rw [← airyPQDPoly_eval, hprod]
      _ = ((-1 : ℝ) ^ (S.card - 1) * (-1 : ℝ) ^ (S.card - 1)) * (airyPQDPoly P Q).eval t /
            ((-1 : ℝ) ^ (S.card - 1) * ∏ s ∈ S.erase t, (t - s)) := by rw [hsq, one_mul]
      _ = (-1 : ℝ) ^ (S.card - 1) * ((airyPQDPoly P Q).eval t / ∏ s ∈ S.erase t, (t - s)) := by
            have hne : (-1 : ℝ) ^ (S.card - 1) ≠ 0 := pow_ne_zero _ (by norm_num)
            field_simp [hne, hp_ne]
  have hsum_eq : ∑ t ∈ S, hbNodeCoeff hHB hQ t =
      ((-1 : ℝ) ^ (S.card - 1) * (airyPQDPoly P Q).coeff (S.card - 1)) /
        profileMass (hbExtremal hHB hQ) := by
    have h_term : ∀ t ∈ S, hbNodeCoeff hHB hQ t =
        (profileMass (hbExtremal hHB hQ))⁻¹ *
          ((-1 : ℝ) ^ (S.card - 1) * ((airyPQDPoly P Q).eval t / ∏ s ∈ S.erase t, (t - s))) := by
      intro t ht
      unfold hbNodeCoeff
      dsimp only [S] at hflip
      rw [div_mul_eq_div_div, div_right_comm, hflip t ht]
      ring
    rw [Finset.sum_congr rfl h_term, ← Finset.mul_sum, ← Finset.mul_sum, hlag]
    ring
  rw [hsum_eq]
  rw [← hs.1] at hcoeff_pos
  exact div_pos hcoeff_pos (hbExtremalProfile (HermiteBiehlerData.ofQNeZero hHB hQ)).mass_pos

/-- **Strict common-shift inequality (`se:common-shift`)**:
`∑_{t ∈ S \ {t_m}} (-b_t / b_{t_m}) = 1 - (∑_{t ∈ S} b_t) / b_{t_m} < 1`. -/
theorem hbCommonShift_lt_one :
    ∑ t ∈ (hbTopZeros hHB hQ).erase (hbMinZero hHB hQ),
        (-(hbNodeCoeff hHB hQ t) / hbNodeCoeff hHB hQ (hbMinZero hHB hQ)) =
      1 - (∑ t ∈ hbTopZeros hHB hQ, hbNodeCoeff hHB hQ t) / hbNodeCoeff hHB hQ (hbMinZero hHB hQ) ∧
    ∑ t ∈ (hbTopZeros hHB hQ).erase (hbMinZero hHB hQ),
        (-(hbNodeCoeff hHB hQ t) / hbNodeCoeff hHB hQ (hbMinZero hHB hQ)) < 1 := by
  set S := hbTopZeros hHB hQ
  set tm := hbMinZero hHB hQ
  have htm_mem : tm ∈ S := (hbTopZeros_spec hHB hQ).2.2.2.1
  have hbm_pos : 0 < hbNodeCoeff hHB hQ tm := hbNodeCoeff_tm_pos hHB hQ
  have hsum_pos : 0 < ∑ t ∈ S, hbNodeCoeff hHB hQ t := hbCommonShift_sum_pos hHB hQ
  have heq : ∑ t ∈ S.erase tm, (-(hbNodeCoeff hHB hQ t) / hbNodeCoeff hHB hQ tm) =
      1 - (∑ t ∈ S, hbNodeCoeff hHB hQ t) / hbNodeCoeff hHB hQ tm := by
    have hsp := Finset.add_sum_erase S (hbNodeCoeff hHB hQ) htm_mem
    have hdiv : ∀ t ∈ S.erase tm,
        -(hbNodeCoeff hHB hQ t) / hbNodeCoeff hHB hQ tm =
          -(hbNodeCoeff hHB hQ t) * (hbNodeCoeff hHB hQ tm)⁻¹ := fun _ _ => div_eq_mul_inv _ _
    rw [Finset.sum_congr rfl hdiv, ← Finset.sum_mul, Finset.sum_neg_distrib]
    have heq' : ∑ t ∈ S.erase tm, hbNodeCoeff hHB hQ t =
        (∑ t ∈ S, hbNodeCoeff hHB hQ t) - hbNodeCoeff hHB hQ tm := by linarith
    rw [heq']
    field_simp [hbm_pos.ne']
    ring
  refine ⟨heq, ?_⟩
  rw [heq]
  have : 0 < (∑ t ∈ S, hbNodeCoeff hHB hQ t) / hbNodeCoeff hHB hQ tm := div_pos hsum_pos hbm_pos
  linarith

end HBMultilevel

/-- info: 'FormalResearch.ModularBootstrap.Stability.hb_dslope_integral_re' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Stability.hb_dslope_integral_re

/-- info: 'FormalResearch.ModularBootstrap.Stability.hbCommonShift_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Stability.hbCommonShift_lt_one

end FormalResearch.ModularBootstrap.Stability
