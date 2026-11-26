module

public import Mathlib
public import FormalResearch.SignUncertainty.CtRoscDefect
public import FormalResearch.SignUncertainty.CtRoscUpper
public import FormalResearch.SignUncertainty.CtRoscChart
public import FormalResearch.SignUncertainty.CtRoscEta
public import FormalResearch.SignUncertainty.CtDyadicCombined
public import FormalResearch.SignUncertainty.CtChartPsiAnalytic
public import FormalResearch.SignUncertainty.CtDyadicPsiWindow

/-!
# `ct:dyadic` (4), `(ct:rosc)`: the Airy-side half-disc estimate at a good radius

Core estimate for `CtCombinedPieces.rosc`: with `W₆(u) = (1-(u/R)^{12})²` and `F = f_c = ctFcC ctChartC1 ε c f` (holomorphic and conjugation-symmetric on a
disc of radius `> R_max`, `ctFcC_holo`), the half-disc defect formula `airy_halfdisc_rosc` and the pure-Airy comparison `AiryRplusComparison`
bound `ctRoscAiry` (the Airy-side quantity `Σ_{n≤N} H(a_n)/Ai'(a_n)² - ∫_{-R}^R H + 2∫_0^R Re H(-v) sin(4/3 v^{3/2}) dv`, `H = W₆ F`) by `K η(R)`.
Proved, given the named input `AiryRplusComparison`.
-/

@[expose] public section

open Complex MeasureTheory Metric Set Filter Topology intervalIntegral
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.Special FormalResearch.HalfDiscCauchy

/-- **Named input `AiryRplusComparison`** (pure Airy asymptotics, `ap:thmD`, DLMF 9.7.5/9.7.9): at good radii the reflection function
`R₊ = (Bi - iAi)/Ai` of the upper semicircle is `2 e^{(4/3)u^{3/2}}` up to relative error `O(R^{-3/2})`:
`‖W₆(w)‖ ‖R₊(w) - 2E(w)‖ ≤ C R^{-3/2} ‖E(w)‖` on `w = Re^{iθ}`, `θ ∈ [0, π]`, with `W₆(w) = (1-(w/R)^{12})²`.  Numerically `C ≈ 1.67`
(scratch check `R ∈ [10, 400]`, good radii). -/
def AiryRplusComparison : Prop :=
  ∃ C R₀ : ℝ, 0 ≤ C ∧ ∀ R : ℝ, R₀ ≤ R → ctGoodRadius R → ∀ θ ∈ Icc (0 : ℝ) π,
    ‖(1 - (circleMap 0 R θ / (R : ℂ)) ^ 12) ^ 2‖ * ‖airyRplus (circleMap 0 R θ) - 2 * airyUpE (circleMap 0 R θ)‖ ≤
      C * R ^ (-(3 / 2 : ℝ)) * ‖airyUpE (circleMap 0 R θ)‖

/-- The taper `W₆(u) = (1 - (u/R)^{12})²` on `ℂ`. -/
noncomputable def ctW6 (R : ℝ) (u : ℂ) : ℂ := (1 - (u / (R : ℂ)) ^ 12) ^ 2

/-- The Airy-side quantity of `(ct:rosc)`. -/
noncomputable def ctRoscAiry (R ε c : ℝ) (f : ℝ → ℝ) (N : ℕ) : ℂ :=
  ((∑ n ∈ Finset.Icc 1 N, (ctW6 R (airyZero n : ℂ) * ctFcC ctChartC1 ε c f (airyZero n : ℂ)) /
        (deriv airyAiC (airyZero n : ℂ)) ^ 2) -
      ∫ x in (-R)..R, (ctW6 R (x : ℂ) * ctFcC ctChartC1 ε c f (x : ℂ))) +
    2 * ((∫ v in (0 : ℝ)..R,
      (ctW6 R (-(v : ℂ)) * ctFcC ctChartC1 ε c f (-(v : ℂ))).re * Real.sin (4 / 3 * v ^ (3 / 2 : ℝ)) : ℝ) : ℂ)

lemma ctW6_diff (R : ℝ) : Differentiable ℂ (ctW6 R) := by
  unfold ctW6; fun_prop

lemma ctW6_conj (R : ℝ) (z : ℂ) : ctW6 R ((starRingEnd ℂ) z) = (starRingEnd ℂ) (ctW6 R z) := by
  simp [ctW6, map_pow, map_sub, map_div₀, Complex.conj_ofReal]


lemma ctRmax_mono {c₁ c₁' c : ℝ} (hc : 0 ≤ c) (h : 0 ≤ c₁) (hle : c₁ ≤ c₁') : ctRmax c₁ c ≤ ctRmax c₁' c := by
  unfold ctRmax
  have : c₁ ^ 2 ≤ c₁' ^ 2 := pow_le_pow_left₀ h hle 2
  have h2 : 0 ≤ c ^ (2 / 3 : ℝ) := Real.rpow_nonneg hc _
  nlinarith [mul_le_mul_of_nonneg_right this h2]

/-- **The Airy-side bound** (`(ct:rosc)`, error term): at a good radius `R ∈ [c₁²c^{2/3}, 4c₁²c^{2/3}]`, `‖ctRoscAiry‖ ≤ K η(R)` given the pointwise
comparison on the upper semicircle. -/
lemma ctRoscAiry_le {c₁ ε c C₁ C₂ ρW MW K R : ℝ} {f : ℝ → ℝ} {N : ℕ} (hc₁ : 0 < c₁) (hle : c₁ ≤ ctChartC1)
    (hb : CtChartBody c₁ ε c C₁) (hb' : CtChartBody ctChartC1 ε c C₂) (hW : PsiWin ε ρW MW)
    (hν : 8 * c₁ ^ 2 ≤ ρW / 2) (hMc : MW < 2 * c₁ ^ 2 * c) (hc : 3e6 ≤ c) (hcC : C₂ * c ^ (-(1 / 3 : ℝ)) < 1)
    (hf : IsHankelEigenfn c ε f) (hR0 : 0 < R) (hR : R ≤ 4 * c₁ ^ 2 * c ^ (2 / 3 : ℝ))
    (hD : CftCircleData airyAiC (fun n => (airyZero n : ℂ)) (Finset.Icc 1 N) R)
    (hcmp : ∀ θ ∈ Icc (0 : ℝ) π, ‖ctW6 R (circleMap 0 R θ)‖ *
      ‖airyRplus (circleMap 0 R θ) - 2 * airyUpE (circleMap 0 R θ)‖ ≤ K * ‖airyUpE (circleMap 0 R θ)‖) :
    ‖ctRoscAiry R ε c f N‖ ≤ K * ctEta c₁ ε c f R := by
  have hc0 : 0 < c := by linarith
  have hγ : 0 < ctChartC1 := ctChartC1_pos
  obtain ⟨ρ, hρ, hFd, -, hFc⟩ := ctFcC_holo hγ ctChartC1_le hb' hc hcC hf
  have hRm : ctRmax c₁ c ≤ ctRmax ctChartC1 c := ctRmax_mono hc0.le hc₁.le hle
  have hRρ : R < ρ := lt_of_le_of_lt (hR.trans (le_of_eq rfl)) (lt_of_le_of_lt hRm hρ)
  have hmain := airy_halfdisc_rosc hD hRρ (ctW6_diff R).differentiableOn hFd
    (fun z hz => by rw [ctW6_conj, hFc z hz, ← map_mul]) hcmp
  have hK0 : 0 ≤ K := by
    have h0 := hcmp 0 ⟨le_rfl, Real.pi_pos.le⟩
    have : 0 ≤ ‖airyUpE (circleMap 0 R 0)‖ := norm_nonneg _
    have hp : 0 < ‖airyUpE (circleMap 0 R 0)‖ := by
      rw [norm_airyUpE (by simp [circleMap])]; exact inv_pos.2 (airyEnv_pos _)
    by_contra hneg
    replace hneg := not_le.1 hneg
    nlinarith [mul_nonneg (norm_nonneg (ctW6 R (circleMap 0 R 0))) (norm_nonneg (airyRplus (circleMap 0 R 0) - 2 * airyUpE (circleMap 0 R 0))), mul_neg_of_neg_of_pos hneg hp]
  -- agreement of the charts on the circle and the η comparison
  obtain ⟨ρ1, hρ1, hag⟩ := ctPhiC_agree hc0 hc₁ hle hb hb' hW hν hMc
  have hRρ1 : ∀ u : ℂ, ‖u‖ = R → u ∈ ball (0 : ℂ) ρ1 := fun u hu => by
    rw [mem_ball_zero_iff, hu]; exact lt_of_le_of_lt hR hρ1
  have hFeq : ∀ u : ℂ, ‖u‖ = R → ctFcC c₁ ε c f u = ctFcC ctChartC1 ε c f u := fun u hu => by
    unfold ctFcC
    rw [hag (hRρ1 u hu), (hag.deriv isOpen_ball) (hRρ1 u hu)]
  have hsph : ∀ θ : ℝ, circleMap 0 R θ ∈ sphere (0 : ℂ) R := fun θ => by simp [abs_of_pos hR0]
  have hnorm : ∀ θ : ℝ, ‖circleMap 0 R θ‖ = R := fun θ => by rw [norm_circleMap_zero, abs_of_pos hR0]
  have hlang : R < c ^ (2 / 3 : ℝ) * langerKappa * 4.94e-4 := by
    have h1 := hankelBand_radius_ge_one hc
    have h2 : R ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) := by
      have h3 : 4 * c₁ ^ 2 ≤ (1 / 100 : ℝ) ^ 2 := by
        have := ctChartC1_le
        nlinarith [hle, hc₁]
      have h4 : 0 ≤ c ^ (2 / 3 : ℝ) := Real.rpow_nonneg hc0.le _
      nlinarith
    have h5 : langerRadius c = c ^ (2 / 3 : ℝ) * langerKappa * 4.94e-4 := rfl
    linarith
  have hΨc : ContinuousOn (hankelPsi c f) (sphere 0 R) := by
    have := (analyticOnNhd_hankelPsi hc0 hf).continuousOn
    exact this.mono (fun u hu => by
      rw [mem_closedBall_zero_iff]; rw [mem_sphere_zero_iff_norm] at hu; linarith)
  have hGc : ContinuousOn (ctFcC ctChartC1 ε c f) (sphere 0 R) :=
    hFd.continuousOn.mono (fun u hu => by
      rw [mem_ball_zero_iff]; rw [mem_sphere_zero_iff_norm] at hu; linarith)
  have hge := ctEta_ge_half hR0 hΨc hGc
  have hηeq : ctEta c₁ ε c f R = ∫ θ in (0 : ℝ)..(2 * π),
      R * (‖hankelPsi c f (circleMap 0 R θ)‖ + ‖ctFcC ctChartC1 ε c f (circleMap 0 R θ)‖) /
        airyEnv (circleMap 0 R θ) := by
    unfold ctEta
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    show _ = _
    rw [hFeq _ (hnorm θ)]
  rw [hηeq]
  refine hmain.trans ?_
  have : R * K * (∫ θ in (0 : ℝ)..π, ‖ctFcC ctChartC1 ε c f (circleMap 0 R θ)‖ * ‖airyUpE (circleMap 0 R θ)‖) =
      K * ∫ θ in (0 : ℝ)..π, R * ‖ctFcC ctChartC1 ε c f (circleMap 0 R θ)‖ * ‖airyUpE (circleMap 0 R θ)‖ := by
    have e : (∫ θ in (0 : ℝ)..π, R * ‖ctFcC ctChartC1 ε c f (circleMap 0 R θ)‖ * ‖airyUpE (circleMap 0 R θ)‖) =
        R * ∫ θ in (0 : ℝ)..π, ‖ctFcC ctChartC1 ε c f (circleMap 0 R θ)‖ * ‖airyUpE (circleMap 0 R θ)‖ := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr (fun θ _ => ?_)
      show R * ‖_‖ * ‖_‖ = R * (‖_‖ * ‖_‖)
      ring
    rw [e]; ring
  rw [this]
  exact mul_le_mul_of_nonneg_left hge hK0


/-- **The Hankel bookkeeping `CtRoscBook`** (`(ct:rosc)`; `constant_terms_lower.tex`, `ct:dyadic` (4), mass identity, lobe and transport):
at a good radius `R ∈ [c₁²c^{2/3}, 4c₁²c^{2/3}]` with `a_1, …, a_N` the Airy zeros inside `|u| < R`, the concrete quantity
`budget + M_all + 2(s₁ - s₂)` equals the Airy-side quantity `ctRoscAiry` up to `O(c^{-4/3})`.  Its content: the budget `tsum` is the finite sum over the
nodes `a_n` (`T1`); `∫_{-R}^R W₆ f_c = ∫ g - ∫_{-R}^0 w_R g - ∫_0^R q g` with `∫_ℝ h dL = ε f(0)` the mass identity (`T2`, `T3`); the taper integral is
transported to the Langer variable (`T4`, `ct_trans_transport`), the remaining pieces are `O(R^{-6}) TV + e^{-c R^{1/2}}` (`T5`), and `s₂^{lit} - s₂^{L}`
is the `O(R^{-12})` edge strip (`T6`).  **Proved** for every `0 < c₁ ≤ ctChartC1` (`ct_rosc_book`, `CtRoscBookProof`, with the bound `10 c^{-4/3}`). -/
def CtRoscBook (c₁ : ℝ) : Prop :=
  ∃ C c₀ : ℝ, ∀ c : ℝ, c₀ ≤ c → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
    ∀ (T : ℝ) (f : ℝ → ℝ), IsHankelFeasible c ε T f → hankelMass c f = 1 →
      T < c * hankelXi c (FormalResearch.Special.airyZero 1) → 0 < ctGap ε c T →
      ∀ R : ℝ, R ∈ Icc (c₁ ^ 2 * c ^ (2 / 3 : ℝ)) (4 * c₁ ^ 2 * c ^ (2 / 3 : ℝ)) → ctGoodRadius R →
        ∀ N : ℕ, (∀ n : ℕ, 1 ≤ n → (n ≤ N ↔ -airyZero n < R)) →
          ‖((ctBudget R ε c f + ctMall R ε c f + 2 * (ctOscS1 R ε c f - ctOscS2 R ε c f) : ℝ) : ℂ) -
              ctRoscAiry R ε c f N‖ ≤ C * c ^ (-(4 / 3) : ℝ)

lemma ctChartComplex_of_le {c₁ : ℝ} (h0 : 0 < c₁) (hle : c₁ ≤ ctChartC1) : CtChartComplex c₁ :=
  (Classical.choose_spec ct_chart_complex).2 c₁ h0 (hle.trans (min_le_left _ _))


lemma le_rpow_two_thirds {t c : ℝ} (ht : 0 ≤ t) (hc : t ^ (3 / 2 : ℝ) ≤ c) : t ≤ c ^ (2 / 3 : ℝ) := by
  have := Real.rpow_le_rpow (Real.rpow_nonneg ht _) hc (by norm_num : (0 : ℝ) ≤ 2 / 3)
  rwa [← Real.rpow_mul ht, show (3 / 2 : ℝ) * (2 / 3) = 1 by norm_num, Real.rpow_one] at this

lemma rpow_neg_three_halves {c₁ c : ℝ} (hc₁ : 0 < c₁) (hc : 0 < c) :
    (c₁ ^ 2 * c ^ (2 / 3 : ℝ)) ^ (-(3 / 2) : ℝ) = (c₁ ^ 3)⁻¹ * c⁻¹ := by
  rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hc.le _), ← Real.rpow_mul hc.le,
    show (2 / 3 : ℝ) * (-(3 / 2)) = -1 by norm_num, Real.rpow_neg_one,
    show (c₁ ^ 2) = c₁ ^ (2 : ℝ) by norm_cast, ← Real.rpow_mul hc₁.le,
    show (2 : ℝ) * (-(3 / 2)) = -(3 : ℕ) by norm_num, Real.rpow_neg hc₁.le, Real.rpow_natCast]

lemma ctGoodRadius_ne_zero {R : ℝ} (hR : 0 < R) (hg : ctGoodRadius R) (u : ℂ) (hu : ‖u‖ = R) : airyAiC u ≠ 0 := by
  intro h0
  have := hg u hu
  rw [h0, norm_zero, zero_pow two_ne_zero] at this
  have hp : 0 < 1 / (25 * π) * (1 + R) ^ (-(1 / 2) : ℝ) * airyEnv u := by
    have := airyEnv_pos u
    have h1 : 0 < (1 + R) ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos (by linarith) _
    positivity
  exact absurd this (not_le.2 hp)

lemma rosc_arith {q d a Cb B x cn lg : ℝ} (hq : |q| ≤ d + a) (hd : d ≤ Cb * cn) (ha : a ≤ B * x) (hcn : 0 ≤ cn)
    (hlg : 1 ≤ lg) (hB : 0 ≤ B) (hx : 0 ≤ x) : |q| ≤ (|Cb| + B) * (x + cn * lg) := by
  have h1 : Cb * cn ≤ |Cb| * (cn * lg) := by
    calc Cb * cn ≤ |Cb| * cn := mul_le_mul_of_nonneg_right (le_abs_self Cb) hcn
      _ ≤ |Cb| * (cn * lg) := mul_le_mul_of_nonneg_left (by nlinarith) (abs_nonneg Cb)
  have h2 : B * x ≤ B * (x + cn * lg) := mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg hcn (by linarith : (0:ℝ) ≤ lg)]) hB
  nlinarith [abs_nonneg Cb]

/-- **`CtCombinedPieces.rosc`** (`(ct:rosc)`, `ct:dyadic` (4)), from the named input `AiryRplusComparison` (pure Airy) and `CtRoscBook`
(Hankel bookkeeping, proved: `ct_rosc_book`): for small `c₁`, `|budget + M_all + 2(s₁ - s₂)| ≤ C(c⁻¹ η_R + c^{-4/3} log c)` at good radii.  The Airy part is the half-disc
defect formula `airy_halfdisc_rosc` with `W₆ f_c`, `K = C R^{-3/2} ≤ C c₁^{-3} c⁻¹`.  Proved given the Airy input `hA` and the hypothesis `CtRoscBook c₁` (itself proved, `ct_rosc_book`). -/
theorem ct_combined_rosc (hA : AiryRplusComparison) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ γ → CtRoscBook c₁ →
      CtDyadicBound c₁ fun R ε c f => ctBudget R ε c f + ctMall R ε c f + 2 * (ctOscS1 R ε c f - ctOscS2 R ε c f) := by
  obtain ⟨ρ₁, M₁, hρ₁, hM₁, hw₁⟩ := ctPsi_window (ε := 1) (Or.inl rfl)
  obtain ⟨ρ₂, M₂, hρ₂, hM₂, hw₂⟩ := ctPsi_window (ε := -1) (Or.inr rfl)
  obtain ⟨Ccmp, R₀, hCcmp, hcmp⟩ := hA
  refine ⟨min ctChartC1 (min (ρ₁ / 16) (ρ₂ / 16)), lt_min ctChartC1_pos (lt_min (by positivity) (by positivity)), ?_⟩
  intro c₁ hc₁ hγ hBook
  have hle : c₁ ≤ ctChartC1 := hγ.trans (min_le_left _ _)
  have hρ1 : c₁ ≤ ρ₁ / 16 := hγ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hρ2 : c₁ ≤ ρ₂ / 16 := hγ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hc₁1 : c₁ ≤ 1 := hle.trans (ctChartC1_le.trans (by norm_num))
  have hc₁2 : c₁ ^ 2 ≤ c₁ := by nlinarith
  obtain ⟨C₁, c₀₁, hC₁, H₁⟩ := ctChartComplex_of_le hc₁ hle
  obtain ⟨C₂, c₀₂, hC₂, H₂⟩ := ctChartComplex_ctChartC1
  obtain ⟨Cb, c₀b, Hb⟩ := hBook
  set t : ℝ := max R₀ 1 / c₁ ^ 2 with ht
  have hc12 : 0 < c₁ ^ 2 := by positivity
  have ht0 : 0 ≤ t := by positivity
  set X : ℝ := max (max (max c₀₁ c₀₂) (max c₀b 3e6)) (max (max (t ^ (3 / 2 : ℝ)) ((M₁ + M₂ + 1) / c₁ ^ 2))
    ((|C₂| + 1) ^ 3)) with hX
  refine ⟨|Cb| + Ccmp * (c₁ ^ 3)⁻¹, X, ?_⟩
  intro c hcX ε hε T f hfeas hmass hT hgap R hR hgood
  have hc3 : 3e6 ≤ c := ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _))).trans hcX
  have hc0 : 0 < c := by linarith
  have hc01 : c₀₁ ≤ c := (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans hcX
  have hc02 : c₀₂ ≤ c := (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans hcX
  have hc0b : c₀b ≤ c := (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _)).trans hcX
  have hct : t ^ (3 / 2 : ℝ) ≤ c := (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_right _ _)).trans hcX
  have hcM : (M₁ + M₂ + 1) / c₁ ^ 2 ≤ c := (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_right _ _)).trans hcX
  have hcC : (|C₂| + 1) ^ 3 ≤ c := ((le_max_right _ _).trans (le_max_right _ _)).trans hcX
  have hRt := le_rpow_two_thirds ht0 hct
  have hmax : max R₀ 1 ≤ c₁ ^ 2 * c ^ (2 / 3 : ℝ) := by
    have := mul_le_mul_of_nonneg_left hRt hc12.le
    rwa [ht, mul_div_cancel₀ _ hc12.ne'] at this
  have hR0' : R₀ ≤ c₁ ^ 2 * c ^ (2 / 3 : ℝ) := (le_max_left _ _).trans hmax
  have hRpos : 0 < c₁ ^ 2 * c ^ (2 / 3 : ℝ) := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hmax)
  have hRlo : c₁ ^ 2 * c ^ (2 / 3 : ℝ) ≤ R := hR.1
  have hRhi : R ≤ 4 * c₁ ^ 2 * c ^ (2 / 3 : ℝ) := hR.2
  have hR0 : 0 < R := lt_of_lt_of_le hRpos hRlo
  obtain ⟨N, hN, hD⟩ := airy_circleData hR0 (ctGoodRadius_ne_zero hR0 hgood)
  have hMc : M₁ < 2 * c₁ ^ 2 * c ∧ M₂ < 2 * c₁ ^ 2 * c := by
    have h1 : M₁ + M₂ + 1 ≤ c₁ ^ 2 * c := by
      rw [div_le_iff₀ hc12] at hcM; linarith
    constructor <;> nlinarith [mul_pos hc12 hc0]
  have hcC' : C₂ * c ^ (-(1 / 3 : ℝ)) < 1 := by
    have h1 : |C₂| + 1 ≤ c ^ (1 / 3 : ℝ) := by
      have := Real.rpow_le_rpow (by positivity) hcC (by norm_num : (0 : ℝ) ≤ 1 / 3)
      rwa [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
        show ((3 : ℕ) : ℝ) * (1 / 3) = 1 by norm_num, Real.rpow_one] at this
    have h2 : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
    rw [Real.rpow_neg hc0.le, ← div_eq_mul_inv, div_lt_one h2]
    linarith [le_abs_self C₂]
  have hKnn : 0 ≤ Ccmp * R ^ (-(3 / 2) : ℝ) := mul_nonneg hCcmp (Real.rpow_nonneg hR0.le _)
  have hair : ‖ctRoscAiry R ε c f N‖ ≤ Ccmp * R ^ (-(3 / 2) : ℝ) * ctEta c₁ ε c f R := by
    have hcmpR : ∀ θ ∈ Icc (0 : ℝ) π, ‖ctW6 R (circleMap 0 R θ)‖ *
        ‖airyRplus (circleMap 0 R θ) - 2 * airyUpE (circleMap 0 R θ)‖ ≤
          Ccmp * R ^ (-(3 / 2) : ℝ) * ‖airyUpE (circleMap 0 R θ)‖ := fun θ hθ =>
      hcmp R (hR0'.trans hRlo) hgood θ hθ
    rcases hε with rfl | rfl
    · exact ctRoscAiry_le hc₁ hle (H₁ 1 (Or.inl rfl) c hc01) (H₂ 1 (Or.inl rfl) c hc02) ⟨hρ₁, hM₁, hw₁⟩
        (by linarith) hMc.1 hc3 hcC' hfeas.toIsHankelEigenfn hR0 hRhi hD hcmpR
    · exact ctRoscAiry_le hc₁ hle (H₁ (-1) (Or.inr rfl) c hc01) (H₂ (-1) (Or.inr rfl) c hc02) ⟨hρ₂, hM₂, hw₂⟩
        (by linarith) hMc.2 hc3 hcC' hfeas.toIsHankelEigenfn hR0 hRhi hD hcmpR
  have hbk := Hb c hc0b ε hε T f hfeas hmass hT hgap R hR hgood N hN
  have hKle : R ^ (-(3 / 2) : ℝ) ≤ (c₁ ^ 3)⁻¹ * c⁻¹ := by
    rw [← rpow_neg_three_halves hc₁ hc0]
    exact Real.rpow_le_rpow_of_nonpos hRpos hRlo (by norm_num)
  have hη := ctEta_nonneg c₁ ε c f hR0.le
  have hcneg : 0 ≤ c ^ (-(4 / 3) : ℝ) := Real.rpow_nonneg hc0.le _
  have hlog : 1 ≤ Real.log c := by
    rw [Real.le_log_iff_exp_le hc0]
    have := Real.exp_one_lt_d9
    linarith
  set Q : ℝ := ctBudget R ε c f + ctMall R ε c f + 2 * (ctOscS1 R ε c f - ctOscS2 R ε c f) with hQ
  have h1 : |Q| ≤ ‖(Q : ℂ) - ctRoscAiry R ε c f N‖ + ‖ctRoscAiry R ε c f N‖ := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real]
    calc ‖(Q : ℂ)‖ = ‖((Q : ℂ) - ctRoscAiry R ε c f N) + ctRoscAiry R ε c f N‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  have h2 : Ccmp * R ^ (-(3 / 2) : ℝ) * ctEta c₁ ε c f R ≤ Ccmp * (c₁ ^ 3)⁻¹ * (c⁻¹ * ctEta c₁ ε c f R) := by
    have := mul_le_mul_of_nonneg_left hKle hCcmp
    calc _ ≤ Ccmp * ((c₁ ^ 3)⁻¹ * c⁻¹) * ctEta c₁ ε c f R := mul_le_mul_of_nonneg_right this hη
      _ = _ := by ring
  have hpos1 : 0 ≤ Ccmp * (c₁ ^ 3)⁻¹ := mul_nonneg hCcmp (by positivity)
  have hcη : 0 ≤ c⁻¹ * ctEta c₁ ε c f R := mul_nonneg (inv_nonneg.2 hc0.le) hη
  exact rosc_arith h1 hbk (hair.trans h2) hcneg hlog hpos1 hcη

/-- info: 'FormalResearch.SignUncertainty.ct_combined_rosc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_combined_rosc

/-- info: 'FormalResearch.SignUncertainty.ctRoscAiry_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ctRoscAiry_le

end FormalResearch.SignUncertainty
