module

public import FormalResearch.ModularBootstrap.Stability.TerminalStability
public import FormalResearch.ModularBootstrap.Stability.AiryStability
public import FormalResearch.ModularBootstrap.Blowup.HbNormLimit

/-!
# Concrete Hermite–Biehler instance of Theorem `se:terminal-stability`

Source: `CFT/modular_bootstrap/paper/soft_edge_two_level_stability.tex`, Theorem `se:terminal-stability`
(fixed terminal-node case, equations \eqref{se:terminal-slope} and \eqref{se:multilevel-slope} at
`h = (0, …, 0, δ)`).

For any real polynomial Hermite–Biehler pair `(P, Q)` (`AiryPQHB P Q`, `Q ≠ 0`), let
`S = hbTopZeros hHB hQ` be the `m = at47_m P Q` largest zeros of `N = P Ai + Q Ai'`,
`t_m = hbMinZero hHB hQ = min S`, and `G_N = hbExtremal hHB hQ`.

* `hbTerminalData`: packages `TerminalData` using `airyPQ_hasSum_unc`, weight
  `ω_m = D(t_m)/N'(t_m)²`, and slope `γ = -G_N'(t_m) = N'(t_m)² / ∏_{t ∈ S \ {t_m}} (t - t_m)`.
* `hb_wγ`: `ω_m γ = D(t_m) / ∏_{t ∈ S \ {t_m}} (t - t_m)`.
* `hb_stability`: `I_N(δ) > 0` for all `δ > 0` and
  `I_N(δ)/δ → D(t_m) / (‖G_N‖₁ ∏_{t ∈ S \ {t_m}} (t - t_m))` as `δ ↓ 0`.

Note: the general multilevel variation `I(h) = ∑ b_i h_i + o(|h|)` and the local Hermite–Biehler
boundary `Z_m(y)` are not formalised here.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set Polynomial
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.Stability

open FormalResearch.Special FormalResearch.ModularBootstrap.Blowup
  FormalResearch.SignUncertainty

section HBInstance

variable {P Q : ℝ[X]} (hHB : AiryPQHB P Q) (hQ : Q ≠ 0)

/-- Derivative of `G_N` at the terminal zero `t_m`:
`G_N'(t_m) ∏_{t ∈ S \ {t_m}} (t - t_m) = -N'(t_m)²`. -/
lemma hbExtremal_deriv_tm_mul :
    deriv (hbExtremal hHB hQ) (hbMinZero hHB hQ : ℂ) *
        ∏ t ∈ (hbTopZeros hHB hQ).erase (hbMinZero hHB hQ),
          ((t : ℂ) - (hbMinZero hHB hQ : ℂ)) =
      -(deriv (airyPQN P Q) (hbMinZero hHB hQ : ℂ) ^ 2) := by
  classical
  set S := hbTopZeros hHB hQ
  set tm := hbMinZero hHB hQ
  set S' := S.erase tm
  set G := hbExtremal hHB hQ
  set N := airyPQN P Q
  have hs := hbTopZeros_spec hHB hQ
  have hG := hbExtremal_spec hHB hQ
  have htm_mem : tm ∈ S := hs.2.2.2.1
  have hG_tm : G (tm : ℂ) = 0 := hG.2.2.2.2.2.2.1 tm htm_mem
  have hN_tm : N (tm : ℂ) = 0 := hs.2.1 tm htm_mem
  have hGd : Differentiable ℂ G := hG.1
  have hNd : Differentiable ℂ N := differentiable_airyPQN P Q
  have hD1d : Differentiable ℂ (dslope G (tm : ℂ)) :=
    EntireDiv.differentiable_dslope_entire hGd _
  have hD2d : Differentiable ℂ (dslope N (tm : ℂ)) :=
    EntireDiv.differentiable_dslope_entire hNd _
  have hG_fac : ∀ z : ℂ, G z = (z - (tm : ℂ)) * dslope G (tm : ℂ) z := fun z => by
    have := sub_smul_dslope G (tm : ℂ) z
    rw [smul_eq_mul, hG_tm, sub_zero] at this
    exact this.symm
  have hN_fac : ∀ z : ℂ, N z = (z - (tm : ℂ)) * dslope N (tm : ℂ) z := fun z => by
    have := sub_smul_dslope N (tm : ℂ) z
    rw [smul_eq_mul, hN_tm, sub_zero] at this
    exact this.symm
  have hpr_fac : ∀ z : ℂ, at47_pr S z = (z - (tm : ℂ)) * at47_pr S' z := fun z => by
    unfold at47_pr
    exact (Finset.mul_prod_erase S (fun t => z - (t : ℂ)) htm_mem).symm
  have hcancel : ∀ z : ℂ, z ≠ (tm : ℂ) →
      dslope G (tm : ℂ) z * at47_pr S' z =
        (((-1 : ℝ) ^ S.card : ℝ) : ℂ) * dslope N (tm : ℂ) z ^ 2 := by
    intro z hz
    have hne : (z - (tm : ℂ)) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hz)
    have h1 : G z * at47_pr S z = (((-1 : ℝ) ^ S.card : ℝ) : ℂ) * N z ^ 2 := hG.2.1 z
    rw [hG_fac z, hN_fac z, hpr_fac z] at h1
    have h2 : (z - (tm : ℂ)) ^ 2 * (dslope G (tm : ℂ) z * at47_pr S' z) =
        (z - (tm : ℂ)) ^ 2 * ((((-1 : ℝ) ^ S.card : ℝ) : ℂ) * dslope N (tm : ℂ) z ^ 2) := by
      calc (z - (tm : ℂ)) ^ 2 * (dslope G (tm : ℂ) z * at47_pr S' z)
          = (z - (tm : ℂ)) * dslope G (tm : ℂ) z * ((z - (tm : ℂ)) * at47_pr S' z) := by ring
        _ = (((-1 : ℝ) ^ S.card : ℝ) : ℂ) * ((z - (tm : ℂ)) * dslope N (tm : ℂ) z) ^ 2 := h1
        _ = _ := by ring
    exact mul_left_cancel₀ hne h2
  have hdense : Dense ({(tm : ℂ)}ᶜ : Set ℂ) :=
    (Set.finite_singleton (tm : ℂ)).countable.dense_compl ℂ
  have hcont_l : Continuous (fun z : ℂ => dslope G (tm : ℂ) z * at47_pr S' z) :=
    hD1d.continuous.mul (at47_pr_differentiable S').continuous
  have hcont_r : Continuous (fun z : ℂ =>
      (((-1 : ℝ) ^ S.card : ℝ) : ℂ) * dslope N (tm : ℂ) z ^ 2) :=
    continuous_const.mul (hD2d.continuous.pow 2)
  have hext := Continuous.ext_on hdense hcont_l hcont_r (fun z hz => hcancel z hz)
  have htm_eq := congrFun hext (tm : ℂ)
  rw [dslope_same, dslope_same] at htm_eq
  have hcard : S.card = S'.card + 1 := (Finset.card_erase_add_one htm_mem).symm
  have hsign : (-1 : ℝ) ^ S.card = -((-1 : ℝ) ^ S'.card) := by
    rw [hcard, pow_succ]; ring
  have hpr_flip : at47_pr S' (tm : ℂ) =
      (((-1 : ℝ) ^ S'.card : ℝ) : ℂ) * ∏ t ∈ S', ((t : ℂ) - (tm : ℂ)) := by
    unfold at47_pr
    have : ((-1 : ℂ) ^ S'.card) * ∏ t ∈ S', ((t : ℂ) - (tm : ℂ)) =
        ∏ t ∈ S', ((tm : ℂ) - (t : ℂ)) := by
      rw [← Finset.prod_const (b := (-1 : ℂ)) (s := S'), ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun t _ => by ring
    push_cast
    exact this.symm
  rw [hpr_flip, hsign] at htm_eq
  have hε0 : ((-1 : ℂ) ^ S'.card) ≠ 0 := pow_ne_zero _ (by norm_num)
  push_cast at htm_eq
  have htm_eq' : ((-1 : ℂ) ^ S'.card) *
      (deriv G (tm : ℂ) * ∏ t ∈ S', ((t : ℂ) - (tm : ℂ))) =
      ((-1 : ℂ) ^ S'.card) * (-(deriv N (tm : ℂ) ^ 2)) := by
    calc ((-1 : ℂ) ^ S'.card) * (deriv G (tm : ℂ) * ∏ t ∈ S', ((t : ℂ) - (tm : ℂ)))
        = deriv G (tm : ℂ) * ((-1 : ℂ) ^ S'.card * ∏ t ∈ S', ((t : ℂ) - (tm : ℂ))) := by ring
      _ = (-((-1 : ℂ) ^ S'.card)) * deriv N (tm : ℂ) ^ 2 := htm_eq
      _ = _ := by ring
  exact mul_left_cancel₀ hε0 htm_eq'

private lemma hb_deriv_im_zero {h : ℂ → ℂ} (hd : Differentiable ℂ h)
    (hreal : ∀ x : ℝ, (h (x : ℂ)).im = 0) (x : ℝ) : (deriv h (x : ℂ)).im = 0 := by
  have hdG : HasDerivAt (fun t : ℝ => h (t : ℂ)) (deriv h (x : ℂ)) x := by
    simpa only [mul_one] using (hd (x : ℂ)).hasDerivAt.comp_ofReal
  have hdim : HasDerivAt (fun t : ℝ => (h (t : ℂ)).im) (deriv h (x : ℂ)).im x :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hdG
  have hconst : (fun t : ℝ => (h (t : ℂ)).im) = fun _ => (0 : ℝ) := funext hreal
  rw [hconst] at hdim
  exact hdim.unique (hasDerivAt_const _ _)

lemma hb_prod_erase_pos :
    0 < ∏ t ∈ (hbTopZeros hHB hQ).erase (hbMinZero hHB hQ), (t - hbMinZero hHB hQ) := by
  have hs := hbTopZeros_spec hHB hQ
  refine Finset.prod_pos fun t ht => ?_
  rcases Finset.mem_erase.mp ht with ⟨hne, hmem⟩
  exact sub_pos.mpr (lt_of_le_of_ne (hs.2.2.2.2 t hmem) (Ne.symm hne))

lemma hb_deriv_tm_re :
    (deriv (hbExtremal hHB hQ) (hbMinZero hHB hQ : ℂ)).re =
      -((airyPQN' P Q (hbMinZero hHB hQ : ℂ)).re ^ 2 /
        ∏ t ∈ (hbTopZeros hHB hQ).erase (hbMinZero hHB hQ), (t - hbMinZero hHB hQ)) := by
  set S := hbTopZeros hHB hQ
  set tm := hbMinZero hHB hQ
  set S' := S.erase tm
  have hmul := hbExtremal_deriv_tm_mul hHB hQ
  have hN' : deriv (airyPQN P Q) (tm : ℂ) = (((airyPQN' P Q (tm : ℂ)).re : ℝ) : ℂ) := by
    rw [deriv_airyPQN, airyPQN'_ofReal, Complex.ofReal_re]
  have hprod : (∏ t ∈ S', ((t : ℂ) - (tm : ℂ))) =
      ((∏ t ∈ S', (t - tm) : ℝ) : ℂ) := by
    push_cast; rfl
  have hG_real : (deriv (hbExtremal hHB hQ) (tm : ℂ)).im = 0 :=
    hb_deriv_im_zero (hbExtremal_spec hHB hQ).1 (hbExtremal_spec hHB hQ).2.2.2.2.1 tm
  have hG_cast : deriv (hbExtremal hHB hQ) (tm : ℂ) =
      (((deriv (hbExtremal hHB hQ) (tm : ℂ)).re : ℝ) : ℂ) :=
    Complex.ext rfl hG_real
  rw [hN', hprod, hG_cast] at hmul
  have hreal : (deriv (hbExtremal hHB hQ) (tm : ℂ)).re * ∏ t ∈ S', (t - tm) =
      -(airyPQN' P Q (tm : ℂ)).re ^ 2 := by
    exact_mod_cast hmul
  have hpos := hb_prod_erase_pos hHB hQ
  have hpos' : ∏ t ∈ S', (t - tm) ≠ 0 := hpos.ne'
  field_simp [hpos']
  linarith

/-- Quadrature positivity for `(P, Q)` (`AiryPQHB P Q`, `Q ≠ 0`) via `airyPQ_hasSum_unc`. -/
theorem hb_quad {f : ℂ → ℂ} (hf : AiryG f)
    (hpos : ∀ x : ℝ, x ≤ hbMinZero hHB hQ → 0 ≤ (f (x : ℂ)).re)
    (hnodes : ∀ i : HbNodes (HermiteBiehlerData.ofQNeZero hHB hQ), 0 ≤ (f (i.1 : ℂ)).re) :
    0 ≤ ∫ x : ℝ, (f (x : ℂ)).re ∧
      (airyPQDr P Q (hbMinZero hHB hQ) / (airyPQN' P Q (hbMinZero hHB hQ : ℂ)).re ^ 2) *
        (f (hbMinZero hHB hQ : ℂ)).re ≤ ∫ x : ℝ, (f (x : ℂ)).re := by
  set S := hbTopZeros hHB hQ
  set tm := hbMinZero hHB hQ
  have hs := hbTopZeros_spec hHB hQ
  obtain ⟨C, ν, hC, hb⟩ := hf.growth
  have hsum := airyPQ_hasSum_unc hHB hQ hf.diff hf.integrable hC hb
  have hre := Complex.reCLM.hasSum hsum
  have hw_eq : ∀ z : {z : ℂ // airyPQN P Q z = 0},
      Complex.reCLM (f z.1 * (airyPQD P Q z.1 / airyPQN' P Q z.1 ^ 2)) =
        (f (z.1.re : ℂ)).re * (airyPQDr P Q z.1.re / (airyPQN' P Q (z.1.re : ℂ)).re ^ 2) := by
    intro z
    have hzeq := airyPQ_zero_eq_ofReal hHB z.2
    have hfz : f z.1 = (((f (z.1.re : ℂ)).re : ℝ) : ℂ) := by
      conv_lhs => rw [hzeq]
      exact Complex.ext rfl (hf.real z.1.re)
    have hDz : airyPQD P Q z.1 = ((airyPQDr P Q z.1.re : ℝ) : ℂ) := by
      conv_lhs => rw [hzeq]
      exact airyPQD_ofReal P Q z.1.re
    have hN'z : airyPQN' P Q z.1 = (((airyPQN' P Q (z.1.re : ℂ)).re : ℝ) : ℂ) := by
      conv_lhs => rw [hzeq]
      rw [airyPQN'_ofReal, Complex.ofReal_re]
    rw [Complex.reCLM_apply, hfz, hDz, hN'z]
    have e : (((f (z.1.re : ℂ)).re : ℝ) : ℂ) *
        (((airyPQDr P Q z.1.re : ℝ) : ℂ) / (((airyPQN' P Q (z.1.re : ℂ)).re : ℝ) : ℂ) ^ 2) =
        (((f (z.1.re : ℂ)).re * (airyPQDr P Q z.1.re / (airyPQN' P Q (z.1.re : ℂ)).re ^ 2) : ℝ) : ℂ) := by
      push_cast; rfl
    rw [e, Complex.ofReal_re]
  simp_rw [hw_eq] at hre
  rw [Complex.reCLM_apply, ← hf.re_integral] at hre
  have hw_pos : ∀ z : {z : ℂ // airyPQN P Q z = 0},
      0 < airyPQDr P Q z.1.re / (airyPQN' P Q (z.1.re : ℂ)).re ^ 2 := by
    intro z
    have hzeq := airyPQ_zero_eq_ofReal hHB z.2
    have hz0 : airyPQN P Q (z.1.re : ℂ) = 0 := by rw [← hzeq]; exact z.2
    obtain ⟨hD, hN'⟩ := airyPQ_zero_weight_pos hHB hQ hz0
    have hN're : (airyPQN' P Q (z.1.re : ℂ)).re ≠ 0 := by
      intro h0
      apply hN'
      rw [airyPQN'_ofReal, Complex.ofReal_re] at h0
      rw [airyPQN'_ofReal, h0]; simp
    exact div_pos hD (sq_pos_of_ne_zero hN're)
  have hnn : ∀ z : {z : ℂ // airyPQN P Q z = 0},
      0 ≤ (f (z.1.re : ℂ)).re * (airyPQDr P Q z.1.re / (airyPQN' P Q (z.1.re : ℂ)).re ^ 2) := by
    intro z
    have hzeq := airyPQ_zero_eq_ofReal hHB z.2
    have hz0 : airyPQN P Q (z.1.re : ℂ) = 0 := by rw [← hzeq]; exact z.2
    have hfnn : 0 ≤ (f (z.1.re : ℂ)).re := by
      by_cases hmem : z.1.re ∈ S
      · by_cases htm_eq : z.1.re = tm
        · rw [htm_eq]; exact hpos tm le_rfl
        · exact hnodes ⟨z.1.re, hmem, htm_eq⟩
      · exact hpos z.1.re (hs.2.2.1 z.1.re hz0 hmem tm hs.2.2.2.1).le
    exact mul_nonneg hfnn (hw_pos z).le
  refine ⟨hre.nonneg hnn, ?_⟩
  let ztm : {z : ℂ // airyPQN P Q z = 0} := ⟨(tm : ℂ), hs.2.1 tm hs.2.2.2.1⟩
  have hle := le_hasSum hre ztm (fun j _ => hnn j)
  simpa [ztm, mul_comm] using hle

/-- The concrete `TerminalData` for a Hermite–Biehler pair `(P, Q)` (`AiryPQHB P Q`, `Q ≠ 0`). -/
noncomputable def hbTerminalData :
    TerminalData (HbNodes (HermiteBiehlerData.ofQNeZero hHB hQ)) where
  G := hbExtremal hHB hQ
  zT := hbMinZero hHB hQ
  nodes := fun i => i.1
  w := airyPQDr P Q (hbMinZero hHB hQ) / (airyPQN' P Q (hbMinZero hHB hQ : ℂ)).re ^ 2
  γ := (airyPQN' P Q (hbMinZero hHB hQ : ℂ)).re ^ 2 /
    ∏ t ∈ (hbTopZeros hHB hQ).erase (hbMinZero hHB hQ), (t - hbMinZero hHB hQ)
  hG := hbExtremalProfile (HermiteBiehlerData.ofQNeZero hHB hQ)
  hGgrowth := (hbExtremal_spec hHB hQ).2.2.2.1
  hP := hbEqualityPrinciple (HermiteBiehlerData.ofQNeZero hHB hQ)
  hw := by
    have hs := hbTopZeros_spec hHB hQ
    obtain ⟨hD, hN'⟩ := airyPQ_zero_weight_pos hHB hQ (hs.2.1 _ hs.2.2.2.1)
    have hN're : (airyPQN' P Q (hbMinZero hHB hQ : ℂ)).re ≠ 0 := by
      intro h0
      apply hN'
      rw [airyPQN'_ofReal, Complex.ofReal_re] at h0
      rw [airyPQN'_ofReal, h0]; simp
    exact div_pos hD (sq_pos_of_ne_zero hN're)
  hγ := by
    have hs := hbTopZeros_spec hHB hQ
    obtain ⟨_, hN'⟩ := airyPQ_zero_weight_pos hHB hQ (hs.2.1 _ hs.2.2.2.1)
    have hN're : (airyPQN' P Q (hbMinZero hHB hQ : ℂ)).re ≠ 0 := by
      intro h0
      apply hN'
      rw [airyPQN'_ofReal, Complex.ofReal_re] at h0
      rw [airyPQN'_ofReal, h0]; simp
    exact div_pos (sq_pos_of_ne_zero hN're) (hb_prod_erase_pos hHB hQ)
  hderiv := hb_deriv_tm_re hHB hQ
  quad := fun f hf hpos hnodes => hb_quad hHB hQ hf hpos hnodes

/-- The terminal-node infimum `I_N(δ)` for `(P, Q)`. -/
noncomputable def hbI (δ : ℝ) : ℝ := termI (hbTerminalData hHB hQ) δ

/-- `ω_m γ = D(t_m) / ∏_{t ∈ S \ {t_m}} (t - t_m)`. -/
lemma hb_wγ :
    (hbTerminalData hHB hQ).w * (hbTerminalData hHB hQ).γ =
      airyPQDr P Q (hbMinZero hHB hQ) /
        ∏ t ∈ (hbTopZeros hHB hQ).erase (hbMinZero hHB hQ), (t - hbMinZero hHB hQ) := by
  show (airyPQDr P Q (hbMinZero hHB hQ) / (airyPQN' P Q (hbMinZero hHB hQ : ℂ)).re ^ 2) *
      ((airyPQN' P Q (hbMinZero hHB hQ : ℂ)).re ^ 2 /
        ∏ t ∈ (hbTopZeros hHB hQ).erase (hbMinZero hHB hQ), (t - hbMinZero hHB hQ)) = _
  have hs := hbTopZeros_spec hHB hQ
  obtain ⟨_, hN'⟩ := airyPQ_zero_weight_pos hHB hQ (hs.2.1 _ hs.2.2.2.1)
  have hN're : (airyPQN' P Q (hbMinZero hHB hQ : ℂ)).re ≠ 0 := by
    intro h0
    apply hN'
    rw [airyPQN'_ofReal, Complex.ofReal_re] at h0
    rw [airyPQN'_ofReal, h0]; simp
  have hpos := hb_prod_erase_pos hHB hQ
  field_simp

private lemma hbExtremal_nonpos_right :
    ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ x : ℝ, hbMinZero hHB hQ < x → x < hbMinZero hHB hQ + δ₁ →
      (hbExtremal hHB hQ (x : ℂ)).re ≤ 0 := by
  classical
  set S := hbTopZeros hHB hQ
  set tm := hbMinZero hHB hQ
  set S' := S.erase tm
  set G := hbExtremal hHB hQ
  have hs := hbTopZeros_spec hHB hQ
  have hG := hbExtremal_spec hHB hQ
  have htm_mem : tm ∈ S := hs.2.2.2.1
  have hδ₁ : ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ t ∈ S', tm + δ₁ ≤ t := by
    by_cases hne : S'.Nonempty
    · set δ₁ := S'.inf' hne (fun t => t - tm)
      have hpos : 0 < δ₁ := by
        rw [Finset.lt_inf'_iff]
        intro t ht
        rcases Finset.mem_erase.mp ht with ⟨hneq, hmem⟩
        exact sub_pos.mpr (lt_of_le_of_ne (hs.2.2.2.2 t hmem) (Ne.symm hneq))
      refine ⟨δ₁, hpos, fun t ht => ?_⟩
      have hle : δ₁ ≤ t - tm := Finset.inf'_le (fun s => s - tm) ht
      linarith
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      exact ⟨1, one_pos, fun t ht => by rw [hne] at ht; simp at ht⟩
  obtain ⟨δ₁, hδ₁_pos, hδ₁_le⟩ := hδ₁
  refine ⟨δ₁, hδ₁_pos, fun x hx_lo hx_hi => ?_⟩
  have hxS : x ∉ S := by
    intro hmem
    rcases eq_or_ne x tm with rfl | hne
    · exact lt_irrefl _ hx_lo
    · have hmem' : x ∈ S' := Finset.mem_erase.mpr ⟨hne, hmem⟩
      linarith [hδ₁_le x hmem']
  have h1 := hG.2.1 (x : ℂ)
  rw [at47_pr_ofReal, airyPQN_ofReal] at h1
  have hG_cast : hbExtremal hHB hQ (x : ℂ) = (((G (x : ℂ)).re : ℝ) : ℂ) :=
    Complex.ext rfl (hG.2.2.2.2.1 x)
  rw [hG_cast] at h1
  have hreal : (G (x : ℂ)).re * ∏ t ∈ S, (x - t) =
      (-1 : ℝ) ^ S.card * (P.eval x * airyAi x + Q.eval x * airyAi' x) ^ 2 := by
    exact_mod_cast h1
  have hcard : S.card = S'.card + 1 := (Finset.card_erase_add_one htm_mem).symm
  have hprod_S : ∏ t ∈ S, (x - t) = (x - tm) * ∏ t ∈ S', (x - t) :=
    (Finset.mul_prod_erase S (fun t => x - t) htm_mem).symm
  have hsign_prod : (-1 : ℝ) ^ S.card * ∏ t ∈ S, (x - t) =
      -( (x - tm) * ∏ t ∈ S', (t - x) ) := by
    rw [hcard, pow_succ, hprod_S]
    have hflip : (-1 : ℝ) ^ S'.card * ∏ t ∈ S', (x - t) = ∏ t ∈ S', (t - x) := by
      rw [← Finset.prod_const (b := (-1 : ℝ)) (s := S'), ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun t _ => by ring
    calc ((-1 : ℝ) ^ S'.card * (-1 : ℝ)) * ((x - tm) * ∏ t ∈ S', (x - t))
        = -((x - tm) * ((-1 : ℝ) ^ S'.card * ∏ t ∈ S', (x - t))) := by ring
      _ = -((x - tm) * ∏ t ∈ S', (t - x)) := by rw [hflip]
  have hpos_den : 0 < (x - tm) * ∏ t ∈ S', (t - x) := by
    refine mul_pos (sub_pos.mpr hx_lo) (Finset.prod_pos fun t ht => ?_)
    linarith [hδ₁_le t ht]
  have heq_mul : (G (x : ℂ)).re * ((x - tm) * ∏ t ∈ S', (t - x)) =
      -(P.eval x * airyAi x + Q.eval x * airyAi' x) ^ 2 := by
    have hsq := congrArg (fun r : ℝ => (-1 : ℝ) ^ S.card * r) hreal
    have hinv : (-1 : ℝ) ^ S.card * (-1 : ℝ) ^ S.card = 1 := by rw [← mul_pow]; simp
    have hlhs : (-1 : ℝ) ^ S.card * ((G (x : ℂ)).re * ∏ t ∈ S, (x - t)) =
        (G (x : ℂ)).re * ((-1 : ℝ) ^ S.card * ∏ t ∈ S, (x - t)) := by ring
    have hrhs : (-1 : ℝ) ^ S.card * ((-1 : ℝ) ^ S.card * (P.eval x * airyAi x + Q.eval x * airyAi' x) ^ 2) =
        (P.eval x * airyAi x + Q.eval x * airyAi' x) ^ 2 := by
      rw [← mul_assoc, hinv, one_mul]
    rw [hlhs, hsign_prod, hrhs] at hsq
    linarith
  have hnonpos_mul : (G (x : ℂ)).re * ((x - tm) * ∏ t ∈ S', (t - x)) ≤ 0 := by
    rw [heq_mul]; exact neg_nonpos.mpr (sq_nonneg _)
  exact nonpos_of_mul_nonpos_left hnonpos_mul hpos_den

/-- **Theorem `se:terminal-stability` (fixed terminal-node case) for any polynomial Hermite–Biehler
pair `(P, Q)` (`AiryPQHB P Q`, `Q ≠ 0`).**
`I_N(δ) > 0` for all `δ > 0`, and
`I_N(δ)/δ → D(t_m) / (‖G_N‖₁ ∏_{t ∈ S \ {t_m}} (t - t_m))` as `δ ↓ 0`. -/
theorem hb_stability :
    (∀ δ : ℝ, 0 < δ → 0 < hbI hHB hQ δ) ∧
      Tendsto (fun δ : ℝ => hbI hHB hQ δ / δ) (𝓝[>] 0)
        (𝓝 (airyPQDr P Q (hbMinZero hHB hQ) /
          (profileMass (hbExtremal hHB hQ) *
            ∏ t ∈ (hbTopZeros hHB hQ).erase (hbMinZero hHB hQ), (t - hbMinZero hHB hQ)))) := by
  classical
  set T := hbTerminalData hHB hQ
  set S := hbTopZeros hHB hQ
  set tm := hbMinZero hHB hQ
  set G := hbExtremal hHB hQ
  have hs := hbTopZeros_spec hHB hQ
  have hG := hbExtremal_spec hHB hQ
  have htm_mem : tm ∈ S := hs.2.2.2.1
  have hG_tm : G (tm : ℂ) = 0 := hG.2.2.2.2.2.2.1 tm htm_mem
  obtain ⟨C, ν, hC, hb⟩ := hG.2.2.2.1
  obtain ⟨ψ, hψd, heq, C', hC', hb'⟩ := at47_div_point hG.1 tm hG_tm hC hb
  have hψ_tm : ψ (tm : ℂ) = deriv G (tm : ℂ) := by
    have hGf : G = fun u => ψ u * (u - (tm : ℂ)) := funext heq
    have hd : HasDerivAt (fun u => ψ u * (u - (tm : ℂ)))
        (deriv ψ (tm : ℂ) * ((tm : ℂ) - (tm : ℂ)) + ψ (tm : ℂ) * 1) (tm : ℂ) :=
      (hψd (tm : ℂ)).hasDerivAt.mul ((hasDerivAt_id _).sub_const _)
    rw [hGf, hd.deriv]; ring
  have hψreal : ∀ x : ℝ, (ψ (x : ℂ)).im = 0 := by
    intro x
    by_cases hx : x = tm
    · rw [hx, hψ_tm]
      exact hb_deriv_im_zero hG.1 hG.2.2.2.2.1 tm
    · have h := congrArg Complex.im (heq (x : ℂ))
      rw [hG.2.2.2.2.1 x, Complex.mul_im] at h
      have hxr : ((x : ℂ) - (tm : ℂ)).re = x - tm := by simp
      have hxi : ((x : ℂ) - (tm : ℂ)).im = 0 := by simp
      rw [hxr, hxi] at h
      have hne : x - tm ≠ 0 := sub_ne_zero.mpr hx
      have : (ψ (x : ℂ)).im * (x - tm) = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_right hne
  have hGre : ∀ x : ℝ, (G (x : ℂ)).re = (ψ (x : ℂ)).re * (x - tm) := fun x => by
    have h := congrArg Complex.re (heq (x : ℂ))
    rw [Complex.mul_re, hψreal x] at h
    simpa using h
  -- Integrability of `ψ`: on `|x| ≥ |tm| + 1`, `‖ψ(x)‖ ≤ ‖G(x)‖`; on compact `[-|tm|-1, |tm|+1]`, continuous.
  have hψ_int : Integrable (fun x : ℝ => ψ (x : ℂ)) := by
    set B : ℝ := |tm| + 1
    have hB : 0 < B := by positivity
    have hcont : Continuous (fun x : ℝ => ψ (x : ℂ)) := hψd.continuous.comp continuous_ofReal
    have hneg : IntegrableOn (fun x : ℝ => ψ (x : ℂ)) (Iio (-B)) := by
      refine (hG.2.2.1.norm.integrableOn (s := Iio (-B))).mono' hcont.aestronglyMeasurable.restrict ?_
      filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
      have hxlt : x < -(|tm| + 1) := hx
      have hden : 1 ≤ ‖(x : ℂ) - (tm : ℂ)‖ := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        linarith [neg_abs_le tm, le_abs_self (tm - x),
          show |x - tm| = |tm - x| from abs_sub_comm x tm]
      have e := congrArg norm (heq (x : ℂ))
      rw [norm_mul] at e
      calc ‖ψ (x : ℂ)‖ = ‖ψ (x : ℂ)‖ * 1 := (mul_one _).symm
        _ ≤ ‖ψ (x : ℂ)‖ * ‖(x : ℂ) - (tm : ℂ)‖ := mul_le_mul_of_nonneg_left hden (norm_nonneg _)
        _ = ‖G (x : ℂ)‖ := e.symm
    have hpos : IntegrableOn (fun x : ℝ => ψ (x : ℂ)) (Ioi B) := by
      refine (hG.2.2.1.norm.integrableOn (s := Ioi B)).mono' hcont.aestronglyMeasurable.restrict ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hxgt : |tm| + 1 < x := hx
      have hden : 1 ≤ ‖(x : ℂ) - (tm : ℂ)‖ := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        linarith [le_abs_self tm, le_abs_self (x - tm)]
      have e := congrArg norm (heq (x : ℂ))
      rw [norm_mul] at e
      calc ‖ψ (x : ℂ)‖ = ‖ψ (x : ℂ)‖ * 1 := (mul_one _).symm
        _ ≤ ‖ψ (x : ℂ)‖ * ‖(x : ℂ) - (tm : ℂ)‖ := mul_le_mul_of_nonneg_left hden (norm_nonneg _)
        _ = ‖G (x : ℂ)‖ := e.symm
    have hmid : IntegrableOn (fun x : ℝ => ψ (x : ℂ)) (Icc (-B) B) := hcont.continuousOn.integrableOn_Icc
    have huniv : (univ : Set ℝ) = Iio (-B) ∪ Icc (-B) B ∪ Ioi B := by
      ext x; simp only [mem_univ, mem_union, mem_Iio, mem_Icc, mem_Ioi, true_iff]
      by_cases h1 : x < -B
      · exact Or.inl (Or.inl h1)
      · by_cases h2 : x ≤ B
        · exact Or.inl (Or.inr ⟨by linarith, h2⟩)
        · exact Or.inr (by linarith)
    rw [← integrableOn_univ, huniv]
    exact (hneg.union hmid).union hpos
  have hψG : AiryG ψ := ⟨hψd, hψ_int, ⟨C', ν, hC', hb'⟩, hψreal⟩
  have hψ_at_zeros : ∀ z : ℂ, airyPQN P Q z = 0 → z ≠ (tm : ℂ) → ψ z = 0 := by
    intro z hz hne
    have hzr := airyPQ_zero_eq_ofReal hHB hz
    have hGz : G z = 0 := by
      by_cases hzS : z.re ∈ S
      · rw [hzr]; exact hG.2.2.2.2.2.2.1 z.re hzS
      · have h1 := hG.2.1 z
        rw [hz, zero_pow two_ne_zero, mul_zero] at h1
        have hpr : at47_pr S z ≠ 0 := by
          rw [hzr]; exact at47_pr_ne_zero hzS
        exact (mul_eq_zero.mp h1).resolve_right hpr
    have h2 : G z = ψ z * (z - (tm : ℂ)) := heq z
    rw [hGz] at h2
    exact (mul_eq_zero.mp h2.symm).resolve_right (sub_ne_zero.mpr hne)
  have hint_ψ : ∫ x : ℝ, (ψ (x : ℂ)).re = T.w * (ψ (tm : ℂ)).re := by
    have hsum := airyPQ_hasSum_unc hHB hQ hψd hψ_int hC' hb'
    let b : {z : ℂ // airyPQN P Q z = 0} := ⟨(tm : ℂ), hs.2.1 tm htm_mem⟩
    have hsingle : HasSum (fun z : {z : ℂ // airyPQN P Q z = 0} =>
        ψ z.1 * (airyPQD P Q z.1 / airyPQN' P Q z.1 ^ 2))
        (ψ b.1 * (airyPQD P Q b.1 / airyPQN' P Q b.1 ^ 2)) := by
      refine hasSum_single b fun z hz => ?_
      have hne : z.1 ≠ (tm : ℂ) := fun h => hz (Subtype.ext h)
      rw [hψ_at_zeros z.1 z.2 hne, zero_mul]
    have hval := hsum.unique hsingle
    have hre := congrArg Complex.re hval
    rw [← hψG.re_integral] at hre
    have hψ_cast : ψ (tm : ℂ) = (((ψ (tm : ℂ)).re : ℝ) : ℂ) := Complex.ext rfl (hψreal tm)
    have hD_cast : airyPQD P Q (tm : ℂ) = ((airyPQDr P Q tm : ℝ) : ℂ) := airyPQD_ofReal P Q tm
    have hN'_cast : airyPQN' P Q (tm : ℂ) = (((airyPQN' P Q (tm : ℂ)).re : ℝ) : ℂ) := by
      rw [airyPQN'_ofReal, Complex.ofReal_re]
    dsimp only [b] at hre
    rw [hψ_cast, hD_cast, hN'_cast] at hre
    have he : (((ψ (tm : ℂ)).re : ℝ) : ℂ) *
        (((airyPQDr P Q tm : ℝ) : ℂ) / (((airyPQN' P Q (tm : ℂ)).re : ℝ) : ℂ) ^ 2) =
        (((ψ (tm : ℂ)).re * (airyPQDr P Q tm / (airyPQN' P Q (tm : ℂ)).re ^ 2) : ℝ) : ℂ) := by
      push_cast; rfl
    rw [he, Complex.ofReal_re] at hre
    rw [hre]
    dsimp only [T, hbTerminalData]
    ring
  set W : ℂ → ℂ := fun u => (((-1 : ℝ)) : ℂ) * ψ u with hW
  have hWG : AiryG W := hψG.smul (-1)
  have hψ_tm_re : (ψ (tm : ℂ)).re = -T.γ := by
    rw [hψ_tm]; exact T.hderiv
  have hWint : ∫ x : ℝ, (W (x : ℂ)).re = T.w * T.γ := by
    have : ∀ x : ℝ, (W (x : ℂ)).re = -(ψ (x : ℂ)).re := fun x => by simp [hW]
    simp_rw [this]
    rw [integral_neg, hint_ψ, hψ_tm_re]
    ring
  obtain ⟨δ₁, hδ₁, hG_nonpos⟩ := hbExtremal_nonpos_right hHB hQ
  have hγ := T.hγ
  have hnn : ∀ δ : ℝ, 0 < δ → δ < δ₁ → ∀ x : ℝ, x ≤ tm + δ →
      0 ≤ (T.G (x : ℂ) + (δ : ℂ) * W (x : ℂ)).re := by
    intro δ hδ hδlt x hx
    have hre : (T.G (x : ℂ) + (δ : ℂ) * W (x : ℂ)).re =
        (G (x : ℂ)).re - δ * (ψ (x : ℂ)).re := by
      show (G (x : ℂ) + (δ : ℂ) * ((((-1 : ℝ)) : ℂ) * ψ (x : ℂ))).re = _
      simp [Complex.add_re, Complex.mul_re, hψreal x]
      ring
    rw [hre]
    rcases lt_trichotomy x tm with hlt | heq_tm | hgt
    · have hG0 : 0 ≤ (G (x : ℂ)).re := hG.2.2.2.2.2.1 x hlt.le
      have hψ' : (ψ (x : ℂ)).re = (G (x : ℂ)).re / (x - tm) := by
        rw [hGre x]; field_simp [(sub_neg.mpr hlt).ne]
      rw [hψ']
      have hneg : x - tm < 0 := by linarith
      have : (G (x : ℂ)).re - δ * ((G (x : ℂ)).re / (x - tm)) =
          (G (x : ℂ)).re * (1 + δ / (tm - x)) := by
        field_simp [hneg.ne, (sub_pos.mpr hlt).ne']
        ring
      rw [this]
      exact mul_nonneg hG0 (by have : 0 < δ / (tm - x) := div_pos hδ (by linarith); linarith)
    · rw [heq_tm, hG_tm, Complex.zero_re, hψ_tm_re]
      nlinarith [mul_pos hδ hγ]
    · have hG0 : (G (x : ℂ)).re ≤ 0 := hG_nonpos x hgt (by linarith)
      have hψ' : (ψ (x : ℂ)).re = (G (x : ℂ)).re / (x - tm) := by
        rw [hGre x]; field_simp [(sub_pos.mpr hgt).ne']
      rw [hψ']
      have hpos : 0 < x - tm := by linarith
      have : (G (x : ℂ)).re - δ * ((G (x : ℂ)).re / (x - tm)) =
          (G (x : ℂ)).re * (1 - δ / (x - tm)) := by
        field_simp
      rw [this]
      have h1 : 1 ≤ δ / (x - tm) := by rw [le_div_iff₀ hpos]; linarith
      exact mul_nonneg_of_nonpos_of_nonpos hG0 (by linarith)
  have hnode : ∀ δ : ℝ, 0 < δ → δ < δ₁ →
      ∀ i : HbNodes (HermiteBiehlerData.ofQNeZero hHB hQ),
        0 ≤ (T.G (T.nodes i : ℂ) + (δ : ℂ) * W (T.nodes i : ℂ)).re := by
    intro δ hδ hδlt i
    have hi_zero : G (i.1 : ℂ) = 0 := hG.2.2.2.2.2.2.1 i.1 i.2.1
    have hψ_zero : ψ (i.1 : ℂ) = 0 :=
      hψ_at_zeros (i.1 : ℂ) (hs.2.1 i.1 i.2.1) (fun h => i.2.2 (Complex.ofReal_injective h))
    show 0 ≤ (G (i.1 : ℂ) + (δ : ℂ) * ((((-1 : ℝ)) : ℂ) * ψ (i.1 : ℂ))).re
    rw [hi_zero, hψ_zero]
    simp
  have hne : ∀ δ : ℝ, 0 < δ → (termSet T δ).Nonempty := by
    intro δ hδ
    set smax := S.sup' ⟨tm, htm_mem⟩ id
    set c : ℝ := max (max smax (tm + δ)) (airyZero 1 + 1) with hc
    have hp : 0 < c - airyZero 1 := by
      have := le_max_right (max smax (tm + δ)) (airyZero 1 + 1); linarith
    have hsmax : smax ≤ c := (le_max_left smax (tm + δ)).trans (le_max_left _ _)
    have htmc : tm + δ ≤ c := (le_max_right smax (tm + δ)).trans (le_max_left _ _)
    refine ⟨_, airyTrial (c - airyZero 1), airyTrial_G _, airyTrial_ne _ hp, fun i => ?_,
      fun x hx => airyTrial_re_nonneg (by have hx' : x ≤ tm + δ := hx; linarith), rfl⟩
    have hi_le : i.1 ≤ smax := Finset.le_sup' id i.2.1
    exact airyTrial_re_nonneg (x := i.1) (by linarith)
  obtain ⟨hpos, hlim⟩ := terminal_stability T hne W hWG hWint hδ₁ hnn hnode
  refine ⟨hpos, ?_⟩
  have hnorm : T.w * T.γ / profileMass T.G =
      airyPQDr P Q tm / (profileMass G * ∏ t ∈ S.erase tm, (t - tm)) := by
    rw [hb_wγ hHB hQ]
    show (airyPQDr P Q tm / ∏ t ∈ S.erase tm, (t - tm)) / profileMass G = _
    rw [div_div, mul_comm (∏ t ∈ S.erase tm, (t - tm)) (profileMass G)]
  rw [← hnorm]
  exact hlim

/-- info: 'FormalResearch.ModularBootstrap.Stability.hb_stability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hb_stability

end HBInstance

end FormalResearch.ModularBootstrap.Stability
