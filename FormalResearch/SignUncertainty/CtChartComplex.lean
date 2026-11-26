module

public import Mathlib
public import FormalResearch.SignUncertainty.CtDyadicEta
public import FormalResearch.SignUncertainty.CtDyadicUhat
public import FormalResearch.SignUncertainty.CtDyadicPsiWindow
public import FormalResearch.SignUncertainty.CtChartInverse

/-!
# `ct:cfu`: the complex chart `φ_c = û⁻¹` from the analyticity of `ψ_ε` across `a = 0`

`constant_terms_lower.tex`, `ct:phic-exp`, Lemma `ct:cfu` (analytic continuation of `ψ_ε` to a fixed disc `|a| ≤ a₀`) and the
definition `φ_c := û⁻¹` on `|u| ≤ R_max = 4c₁²c^{2/3}`.

* `CtPsiAnalytic ε` (the one **named input**, not proved here): the Lean `ctPsi ε` (`ψ_ε = θ_ε(τ₀(a))/√(-a)`, `a < 0`) is the
  restriction to `(-ρ, 0)` of a function `Ψ` holomorphic on a disc `|a| < ρ`, with `Ψ(ā) = conj Ψ(a)`.  This is `ct:cfu` Step 2
  (`ψ_ε(a) := h_ε(-a, a)` is real-analytic on `|a| ≤ a₀`); in Lean `ctPsi_window`/`cfu_psi_langer` give only `C^∞` at `0`.
* `ct_chart_complex_of_analytic`: **proved** from `CtPsiAnalytic (1)` and `CtPsiAnalytic (-1)`: for `c₁ ≤ c₁₀`, the complex chart
  `φ_c` exists on a disc of radius `> R_max` (`CtChartComplex c₁`), via the holomorphic inverse of `a ↦ a + c⁻¹ Ψ(a)`
  (`ct_inv_chart`) and the identity theorem (`ctChartExt_unique`).
-/

@[expose] public section

open Complex Metric Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

/-- **Analyticity of `ψ_ε` across `a = 0`** (`ct:cfu` Step 2, `ct:psi-def`; named input, not proved): the Lean `ctPsi ε` is the
restriction to `(-ρ, 0)` of a function holomorphic on `ball 0 ρ` that is real-symmetric (`Ψ(ā) = conj Ψ(a)`, i.e. real on the
real axis). -/
def CtPsiAnalytic (ε : ℝ) : Prop :=
  ∃ (ρ : ℝ) (Ψ : ℂ → ℂ), 0 < ρ ∧ DifferentiableOn ℂ Ψ (ball 0 ρ) ∧
    (∀ z ∈ ball (0 : ℂ) ρ, Ψ (starRingEnd ℂ z) = starRingEnd ℂ (Ψ z)) ∧
    ∀ a : ℝ, -ρ < a → a < 0 → Ψ (a : ℂ) = (ctPsi ε a : ℂ)

/-- The four clauses of `CtChartComplex` at one `(ε, c)`. -/
def CtChartBody (c₁ ε c C : ℝ) : Prop :=
  (∃ F, IsCtChartExt c₁ ε c F) ∧
    (∀ x : ℝ, -ctRmax c₁ c ≤ x → x ≤ 0 → x ∈ ctPhiDom ε c) ∧
    (∀ x : ℝ, |x| ≤ ctRmax c₁ c → (ctPhiC c₁ ε c (x : ℂ)).im = 0) ∧
    (∀ u : ℂ, ‖u‖ ≤ ctRmax c₁ c →
      ‖ctPhiC c₁ ε c u - u‖ ≤ C * c ^ (-(1 / 3 : ℝ)) ∧ ‖deriv (ctPhiC c₁ ε c) u - 1‖ ≤ C * c ^ (-1 : ℝ))

lemma ctChartComplex_iff (c₁ : ℝ) :
    CtChartComplex c₁ ↔ ∃ C c₀ : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → ∀ c : ℝ, c₀ ≤ c → CtChartBody c₁ ε c C :=
  Iff.rfl

/-- `ctPhi` inverts `û` on `ctPhiDom` (`û` is injective there). -/
lemma ctPhi_ctUhat (ε : ℝ) {c : ℝ} (hc : 0 < c) {w : ℝ} (hw : w ∈ ctPhiDom ε c) : ctPhi ε c (ctUhat ε c w) = w :=
  (ctUhat_injOn_dom ε hc).leftInvOn_invFunOn hw

lemma ctRmax_pos {c₁ c : ℝ} (hc₁ : 0 < c₁) (hc : 0 < c) : 0 < ctRmax c₁ c := by
  unfold ctRmax; positivity

/-- `μ R_max = 4 · 2^{2/3} c₁² ≤ 8 c₁²`. -/
lemma ctMu_mul_ctRmax {c₁ c : ℝ} (hc : 0 < c) : ctMu c * ctRmax c₁ c = 4 * (2 : ℝ) ^ ((2 : ℝ) / 3) * c₁ ^ 2 := by
  unfold ctMu ctRmax
  have : c ^ (-(2 / 3) : ℝ) * c ^ (2 / 3 : ℝ) = 1 := by
    rw [← Real.rpow_add hc]; norm_num
  calc (2 : ℝ) ^ ((2 : ℝ) / 3) * c ^ (-(2 / 3) : ℝ) * (4 * c₁ ^ 2 * c ^ (2 / 3 : ℝ))
      = 4 * (2 : ℝ) ^ ((2 : ℝ) / 3) * c₁ ^ 2 * (c ^ (-(2 / 3) : ℝ) * c ^ (2 / 3 : ℝ)) := by ring
    _ = _ := by rw [this, mul_one]

lemma ctMu_mul_ctRmax_le {c₁ c : ℝ} (hc : 0 < c) : ctMu c * ctRmax c₁ c ≤ 8 * c₁ ^ 2 := by
  rw [ctMu_mul_ctRmax hc]
  have h2 : (2 : ℝ) ^ ((2 : ℝ) / 3) ≤ 2 := by
    calc (2 : ℝ) ^ ((2 : ℝ) / 3) ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  nlinarith [sq_nonneg c₁]

lemma ctLam_le_rpow_neg {c : ℝ} (hc : 0 < c) : ctLam c ≤ c ^ (-(1 / 3 : ℝ)) := by
  unfold ctLam
  have h1 : (2 : ℝ) ^ (-(2 / 3) : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have h2 : 0 < c ^ (-(1 / 3 : ℝ)) := Real.rpow_pos_of_pos hc _
  nlinarith

/-! ### Uniqueness of the continuation -/

/-- Two holomorphic continuations of the chart agree on a disc of radius `> R_max` (identity theorem: both invert `û` on the
interval `û([-R_max, 0))`). -/
lemma ctChartExt_unique {c₁ ε c : ℝ} (hc : 0 < c) (hc₁ : 0 < c₁)
    (hdom : ∀ x : ℝ, -ctRmax c₁ c ≤ x → x ≤ 0 → x ∈ ctPhiDom ε c)
    (hcont : ContinuousAt (ctUhat ε c) (-(ctRmax c₁ c) / 2))
    (hz0 : |ctUhat ε c (-(ctRmax c₁ c) / 2)| < ctRmax c₁ c)
    {F₁ F₂ : ℂ → ℂ} (h₁ : IsCtChartExt c₁ ε c F₁) (h₂ : IsCtChartExt c₁ ε c F₂) :
    ∃ ρ : ℝ, ctRmax c₁ c < ρ ∧ EqOn F₁ F₂ (ball 0 ρ) := by
  obtain ⟨⟨ρ₁, hρ₁, hd₁⟩, hag₁⟩ := h₁
  obtain ⟨⟨ρ₂, hρ₂, hd₂⟩, hag₂⟩ := h₂
  have hR := ctRmax_pos hc₁ hc
  set R := ctRmax c₁ c with hRdef
  set w₀ : ℝ := -R / 2 with hw₀
  refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, ?_⟩
  have hU : ball (0 : ℂ) (min ρ₁ ρ₂) ⊆ ball 0 ρ₁ := ball_subset_ball (min_le_left _ _)
  have hU2 : ball (0 : ℂ) (min ρ₁ ρ₂) ⊆ ball 0 ρ₂ := ball_subset_ball (min_le_right _ _)
  have han₁ : AnalyticOnNhd ℂ F₁ (ball 0 (min ρ₁ ρ₂)) := (hd₁.mono hU).analyticOnNhd isOpen_ball
  have han₂ : AnalyticOnNhd ℂ F₂ (ball 0 (min ρ₁ ρ₂)) := (hd₂.mono hU2).analyticOnNhd isOpen_ball
  set z₀ : ℂ := ((ctUhat ε c w₀ : ℝ) : ℂ) with hz₀
  have hz0mem : z₀ ∈ ball (0 : ℂ) (min ρ₁ ρ₂) := by
    rw [mem_ball_zero_iff, hz₀, Complex.norm_real, Real.norm_eq_abs]
    exact lt_min (hz0.trans hρ₁) (hz0.trans hρ₂)
  refine han₁.eqOn_of_preconnected_of_frequently_eq han₂ (convex_ball _ _).isPreconnected hz0mem ?_
  have hw₀mem : w₀ ∈ Ioo (-R) 0 := ⟨by rw [hw₀]; linarith, by rw [hw₀]; linarith⟩
  have hev : ∀ᶠ w in 𝓝[≠] w₀, w ∈ Ioo (-R) 0 :=
    mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds hw₀mem.1 hw₀mem.2)
  have hcont' : ContinuousAt (fun w : ℝ => ((ctUhat ε c w : ℝ) : ℂ)) w₀ :=
    Complex.continuous_ofReal.continuousAt.comp hcont
  have htend : Tendsto (fun w : ℝ => ((ctUhat ε c w : ℝ) : ℂ)) (𝓝[≠] w₀) (𝓝[≠] z₀) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hcont'.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [hev, self_mem_nhdsWithin] with w hw hne
    intro h
    have h' : ctUhat ε c w = ctUhat ε c w₀ := Complex.ofReal_injective h
    exact hne (ctUhat_injOn_dom ε hc (hdom w hw.1.le hw.2.le) (hdom w₀ hw₀mem.1.le hw₀mem.2.le) h')
  have hagr : ∀ᶠ w in 𝓝[≠] w₀, F₁ ((ctUhat ε c w : ℝ) : ℂ) = F₂ ((ctUhat ε c w : ℝ) : ℂ) := by
    filter_upwards [hev] with w hw
    have hwd := hdom w hw.1.le hw.2.le
    have habs : |w| ≤ R := by rw [abs_of_neg hw.2]; linarith [hw.1]
    rw [hag₁ w hwd hw.2 habs, hag₂ w hwd hw.2 habs]
  by_contra hcon
  have h1 := Filter.not_frequently.mp hcon
  have h2 := htend.eventually h1
  obtain ⟨w, hw1, hw2⟩ := (hagr.and h2).exists
  exact hw2 hw1

/-! ### Construction of the chart from `Ψ` -/

section Construct

variable {ε c₁ c : ℝ} {Ψ : ℂ → ℂ} {ρΨ r M ρW MW : ℝ}

/-- The core of `ct_chart_complex_of_analytic`, for one `(ε, c)`: the data `Ψ` (holomorphic, real-symmetric, equal to `ctPsi ε`
on `(-ρΨ, 0)`, bounded with its derivative by `M` on `closedBall 0 r`, `r < ρΨ`) and the window `PsiWin ε ρW MW`, with the
quantitative conditions `2M ≤ c`, `4M ≤ r c`, `2 MW ≤ c`, `M < 2 c₁² c`, `8 c₁² ≤ r/8`, `8 c₁² ≤ ρW/2`, give `CtChartBody c₁ ε c (2M)`. -/
theorem ctChartBody_of_data (hc₁ : 0 < c₁) (hc : 0 < c) (hΨd : DifferentiableOn ℂ Ψ (ball 0 ρΨ)) (hr : r < ρΨ)
    (hr0 : 0 < r) (hM : ∀ z ∈ closedBall (0 : ℂ) r, ‖Ψ z‖ ≤ M ∧ ‖deriv Ψ z‖ ≤ M)
    (hconj : ∀ z ∈ ball (0 : ℂ) ρΨ, Ψ (starRingEnd ℂ z) = starRingEnd ℂ (Ψ z))
    (hagree : ∀ a : ℝ, -ρΨ < a → a < 0 → Ψ (a : ℂ) = (ctPsi ε a : ℂ))
    (hW : PsiWin ε ρW MW) (h2M : 2 * M ≤ c) (h4M : 4 * M ≤ r * c) (hcW : 2 * MW ≤ c) (hMc : M < 2 * c₁ ^ 2 * c)
    (hν1 : 8 * c₁ ^ 2 ≤ r / 8) (hν2 : 8 * c₁ ^ 2 ≤ ρW / 2) : CtChartBody c₁ ε c (2 * M) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (mem_closedBall_self hr0.le)).1
  have hμ := ctMu_pos hc
  set μ := ctMu c with hμdef
  set κ : ℝ := c⁻¹ with hκdef
  have hκ0 : 0 ≤ κ := (inv_pos.2 hc).le
  have hκM : κ * M ≤ 1 / 2 := by
    rw [hκdef, inv_mul_le_iff₀ hc]; linarith
  have hκMr : κ * M ≤ r / 4 := by
    rw [hκdef, inv_mul_le_iff₀ hc]; linarith
  obtain ⟨G, hGsp, hGun, hGd⟩ := ct_inv_chart hΨd hr hr0 hM hκ0 hκM (by linarith)
  have hRpos := ctRmax_pos hc₁ hc
  set R := ctRmax c₁ c with hRdef
  have hνle : μ * R ≤ r / 8 := (ctMu_mul_ctRmax_le hc).trans hν1
  have hνW : μ * R ≤ ρW / 2 := (ctMu_mul_ctRmax_le hc).trans hν2
  -- the chart
  set F : ℂ → ℂ := fun u => G ((μ : ℂ) * u) / (μ : ℂ) with hF
  have hμC : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ.ne'
  set ρu : ℝ := r / (2 * μ) with hρu
  have hRρ : R < ρu := by
    rw [hρu, lt_div_iff₀ (by positivity)]
    nlinarith
  have hmem : ∀ u : ℂ, u ∈ ball (0 : ℂ) ρu → (μ : ℂ) * u ∈ ball (0 : ℂ) (r / 2) := by
    intro u hu
    rw [mem_ball_zero_iff] at hu ⊢
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hμ.le]
    rw [hρu, lt_div_iff₀ (by positivity)] at hu
    nlinarith
  have hFd : ∀ u ∈ ball (0 : ℂ) ρu, HasDerivAt F (1 / (1 + (κ : ℂ) * deriv Ψ (G ((μ : ℂ) * u)))) u := by
    intro u hu
    have h1 := hGd _ (hmem u hu)
    have h2 : HasDerivAt (fun u : ℂ => (μ : ℂ) * u) (μ : ℂ) u := by
      simpa using (hasDerivAt_id u).const_mul (μ : ℂ)
    have h3 := (h1.comp u h2).div_const (μ : ℂ)
    have e : 1 / (1 + (κ : ℂ) * deriv Ψ (G ((μ : ℂ) * u))) * (μ : ℂ) / (μ : ℂ) =
        1 / (1 + (κ : ℂ) * deriv Ψ (G ((μ : ℂ) * u))) := by
      field_simp
    rw [← e]
    exact h3
  have hFdiff : DifferentiableOn ℂ F (ball 0 ρu) := fun u hu => (hFd u hu).differentiableAt.differentiableWithinAt
  -- `û` on the real window
  have hdom : ∀ x : ℝ, -R ≤ x → x ≤ 0 → x ∈ ctPhiDom ε c := by
    intro x hx1 hx2
    refine ⟨hx2, ρW, MW, hW, hcW, ?_⟩
    have := mul_le_mul_of_nonneg_left hx1 hμ.le
    have : -(μ * R) ≤ μ * x := by linarith
    linarith [hW.1]
  -- `ctPsi` bound along the window from `Ψ`
  have hpsiΨ : ∀ a : ℝ, -(r / 8) ≤ a → a < 0 → ((ctPsi ε a : ℝ) : ℂ) = Ψ (a : ℂ) ∧ |ctPsi ε a| ≤ M := by
    intro a ha1 ha2
    have hρa : -ρΨ < a := by linarith
    have e := hagree a hρa ha2
    refine ⟨e.symm, ?_⟩
    have hm := (hM (a : ℂ) (by rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_neg ha2]; linarith)).1
    rw [e] at hm
    simpa using hm
  -- agreement on the real window
  have hag : ∀ w : ℝ, w ∈ ctPhiDom ε c → w < 0 → |w| ≤ R → F ((ctUhat ε c w : ℝ) : ℂ) = (w : ℂ) := by
    intro w _ hw0 hwR
    have hwa : μ * w < 0 := mul_neg_of_pos_of_neg hμ hw0
    have hwa' : -(r / 8) ≤ μ * w := by
      have : |w| = -w := abs_of_neg hw0
      have := mul_le_mul_of_nonneg_left hwR hμ.le
      nlinarith
    obtain ⟨hpe, hpb⟩ := hpsiΨ (μ * w) hwa' hwa
    set a₀ : ℂ := ((μ * w : ℝ) : ℂ) with ha₀
    have ha₀cl : a₀ ∈ closedBall (0 : ℂ) r := by
      rw [mem_closedBall_zero_iff, ha₀, Complex.norm_real, Real.norm_eq_abs, abs_of_neg hwa]; linarith
    have hb : (μ : ℂ) * ((ctUhat ε c w : ℝ) : ℂ) = a₀ + (κ : ℂ) * Ψ a₀ := by
      rw [ha₀, ← hpe, ctUhat_eq]
      have hlm := ctLam_mul_ctMu hc
      have : (κ : ℂ) = ((ctLam c * μ : ℝ) : ℂ) := by rw [hlm]
      rw [this]
      push_cast
      ring
    have hbn : (μ : ℂ) * ((ctUhat ε c w : ℝ) : ℂ) ∈ ball (0 : ℂ) (r / 2) := by
      rw [hb, mem_ball_zero_iff]
      calc ‖a₀ + (κ : ℂ) * Ψ a₀‖ ≤ ‖a₀‖ + ‖(κ : ℂ) * Ψ a₀‖ := norm_add_le _ _
        _ ≤ r / 8 + κ * M := by
            have h1 : ‖a₀‖ ≤ r / 8 := by
              rw [ha₀, Complex.norm_real, Real.norm_eq_abs, abs_of_neg hwa]; linarith
            have h2 : ‖(κ : ℂ) * Ψ a₀‖ ≤ κ * M := by
              rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hκ0]
              have := (hM a₀ ha₀cl).1
              exact mul_le_mul_of_nonneg_left this hκ0
            linarith
        _ < r / 2 := by linarith
    have := hGun _ hbn a₀ ha₀cl hb.symm
    simp only [hF]
    rw [← this, ha₀]
    push_cast
    field_simp
  have hext : IsCtChartExt c₁ ε c F := ⟨⟨ρu, hRρ, hFdiff⟩, hag⟩
  -- the derivative and displacement bounds on `‖u‖ ≤ R`
  have hbnd : ∀ u : ℂ, ‖u‖ ≤ R →
      ‖F u - u‖ ≤ 2 * M * c ^ (-(1 / 3 : ℝ)) ∧ ‖deriv F u - 1‖ ≤ 2 * M * c ^ (-1 : ℝ) := by
    intro u hu
    have huρ : u ∈ ball (0 : ℂ) ρu := by rw [mem_ball_zero_iff]; exact lt_of_le_of_lt hu hRρ
    obtain ⟨hGcl, hGeq⟩ := hGsp _ (hmem u huρ)
    constructor
    · have e : F u - u = -((κ : ℂ) * Ψ (G ((μ : ℂ) * u))) / (μ : ℂ) := by
        simp only [hF]
        field_simp
        linear_combination hGeq
      rw [e, norm_div, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hκ0, Complex.norm_real,
        Real.norm_of_nonneg hμ.le, div_le_iff₀ hμ]
      have h1 := (hM _ hGcl).1
      have hl : κ = ctLam c * μ := by rw [ctLam_mul_ctMu hc]
      have hlc := ctLam_le_rpow_neg hc
      have hcpos : 0 < c ^ (-(1 / 3 : ℝ)) := Real.rpow_pos_of_pos hc _
      calc κ * ‖Ψ (G ((μ : ℂ) * u))‖ ≤ κ * M := mul_le_mul_of_nonneg_left h1 hκ0
        _ = ctLam c * M * μ := by rw [hl]; ring
        _ ≤ 2 * M * c ^ (-(1 / 3 : ℝ)) * μ := by
            apply mul_le_mul_of_nonneg_right _ hμ.le
            nlinarith [mul_le_mul_of_nonneg_right hlc hM0]
    · rw [(hFd u huρ).deriv]
      have hq : ‖(κ : ℂ) * deriv Ψ (G ((μ : ℂ) * u))‖ ≤ κ * M := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hκ0]
        exact mul_le_mul_of_nonneg_left (hM _ hGcl).2 hκ0
      set q : ℂ := (κ : ℂ) * deriv Ψ (G ((μ : ℂ) * u)) with hq'
      have hden : 1 / 2 ≤ ‖1 + q‖ := by
        have := norm_sub_norm_le (1 : ℂ) (-q)
        rw [sub_neg_eq_add, norm_neg, norm_one] at this
        linarith
      have hpos : 0 < ‖1 + q‖ := by linarith
      have hne : (1 + q) ≠ 0 := norm_pos_iff.mp hpos
      have e : 1 / (1 + q) - 1 = -q / (1 + q) := by field_simp; ring
      rw [e, norm_div, norm_neg, div_le_iff₀ hpos]
      have hcm : c ^ (-1 : ℝ) = κ := by rw [Real.rpow_neg_one]
      rw [hcm]
      nlinarith [mul_le_mul_of_nonneg_left hden (mul_nonneg hM0 hκ0)]
  -- identification of `ctPhiC` with `F`
  have hcont : ContinuousAt (ctUhat ε c) (-R / 2) := by
    have hw0 : -R / 2 < 0 := by linarith
    have hwρ : -ρW < μ * (-R / 2) := by
      have : μ * (-R / 2) = -(μ * R) / 2 := by ring
      rw [this]; linarith [hW.1]
    exact (ctUhat_hasDerivAt hW hc hw0 hwρ).continuousAt
  have hz0 : |ctUhat ε c (-R / 2)| < R := by
    have hw0 : -R / 2 < 0 := by linarith
    have hwρ : -ρW < μ * (-R / 2) := by
      have : μ * (-R / 2) = -(μ * R) / 2 := by ring
      rw [this]; linarith [hW.1]
    have h1 := abs_ctUhat_sub_le hW hc hw0 hwρ
    have hwa : μ * (-R / 2) < 0 := by nlinarith
    have hwa' : -(r / 8) ≤ μ * (-R / 2) := by
      have : μ * (-R / 2) = -(μ * R) / 2 := by ring
      rw [this]; linarith
    obtain ⟨-, hpb⟩ := hpsiΨ _ hwa' hwa
    have h2 : |ctUhat ε c (-R / 2) - (-R / 2)| ≤ ctLam c * M := by
      rw [ctUhat_eq]
      have : -R / 2 + ctLam c * ctPsi ε (μ * (-R / 2)) - -R / 2 = ctLam c * ctPsi ε (μ * (-R / 2)) := by ring
      rw [this, abs_mul, abs_of_pos (ctLam_pos hc)]
      exact mul_le_mul_of_nonneg_left hpb (ctLam_pos hc).le
    have h3 : ctLam c * M < R / 2 := by
      have hlc := ctLam_le_rpow_neg hc
      have : ctLam c * M ≤ c ^ (-(1 / 3 : ℝ)) * M := mul_le_mul_of_nonneg_right hlc hM0
      have hcc : c ^ (-(1 / 3 : ℝ)) * c ^ (1 : ℝ) = c ^ (2 / 3 : ℝ) := by
        rw [← Real.rpow_add hc]; norm_num
      have hpos : 0 < c ^ (-(1 / 3 : ℝ)) := Real.rpow_pos_of_pos hc _
      have e1 : R / 2 = 2 * c₁ ^ 2 * c ^ (2 / 3 : ℝ) := by rw [hRdef]; unfold ctRmax; ring
      rw [e1, ← hcc, Real.rpow_one]
      nlinarith [mul_lt_mul_of_pos_left hMc hpos]
    have := abs_le.mp h2
    rw [abs_lt]
    constructor <;> nlinarith [this.1, this.2]
  have hFeq : ∃ ρ : ℝ, R < ρ ∧ EqOn F (ctPhiC c₁ ε c) (ball 0 ρ) :=
    ctChartExt_unique hc hc₁ hdom hcont hz0 hext (ctPhiC_spec ⟨F, hext⟩)
  obtain ⟨ρe, hρe, hEq⟩ := hFeq
  have hlocal : ∀ u : ℂ, ‖u‖ ≤ R → ctPhiC c₁ ε c =ᶠ[𝓝 u] F := by
    intro u hu
    have hmem' : u ∈ ball (0 : ℂ) ρe := by rw [mem_ball_zero_iff]; exact lt_of_le_of_lt hu hρe
    filter_upwards [isOpen_ball.mem_nhds hmem'] with z hz using (hEq hz).symm
  refine ⟨⟨F, hext⟩, hdom, ?_, ?_⟩
  · -- reality
    intro x hx
    have hxρ : (x : ℂ) ∈ ball (0 : ℂ) ρu := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact lt_of_le_of_lt hx hRρ
    have hb := hmem _ hxρ
    have hbc : starRingEnd ℂ ((μ : ℂ) * (x : ℂ)) = (μ : ℂ) * (x : ℂ) := by simp
    have hGc : G ((μ : ℂ) * (x : ℂ)) = starRingEnd ℂ (G ((μ : ℂ) * (x : ℂ))) := by
      obtain ⟨hGcl, hGeq⟩ := hGsp _ hb
      have hcl' : starRingEnd ℂ (G ((μ : ℂ) * (x : ℂ))) ∈ closedBall (0 : ℂ) r := by
        rw [mem_closedBall_zero_iff, Complex.norm_conj]; simpa using hGcl
      have hGρ : G ((μ : ℂ) * (x : ℂ)) ∈ ball (0 : ℂ) ρΨ :=
        closedBall_subset_ball hr hGcl
      have heq : starRingEnd ℂ (G ((μ : ℂ) * (x : ℂ))) +
          (κ : ℂ) * Ψ (starRingEnd ℂ (G ((μ : ℂ) * (x : ℂ)))) = (μ : ℂ) * (x : ℂ) := by
        rw [hconj _ hGρ]
        have := congrArg (starRingEnd ℂ) hGeq
        rw [map_add, map_mul, Complex.conj_ofReal, hbc] at this
        exact this
      exact (hGun _ hb _ hcl' heq).symm
    have hxF : F (x : ℂ) = G ((μ : ℂ) * (x : ℂ)) / (μ : ℂ) := rfl
    have hu : ctPhiC c₁ ε c (x : ℂ) = F (x : ℂ) := (hlocal (x : ℂ) (by simpa using hx)).self_of_nhds
    rw [hu, hxF]
    have him : (G ((μ : ℂ) * (x : ℂ))).im = 0 := by
      have := congrArg Complex.im hGc
      rw [Complex.conj_im] at this
      linarith
    rw [Complex.div_ofReal_im, him]; simp
  · intro u hu
    have hb := hbnd u hu
    have e1 : ctPhiC c₁ ε c u = F u := (hlocal u hu).self_of_nhds
    have e2 : deriv (ctPhiC c₁ ε c) u = deriv F u := (hlocal u hu).deriv_eq
    rw [e1, e2]
    exact hb

end Construct

/-- `CtChartBody` is monotone in the constant `C`. -/
lemma CtChartBody.mono {c₁ ε c C C' : ℝ} (hc : 0 < c) (h : CtChartBody c₁ ε c C) (hCC : C ≤ C') :
    CtChartBody c₁ ε c C' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, h3, fun u hu => ?_⟩
  obtain ⟨a, b⟩ := h4 u hu
  have p1 : 0 < c ^ (-(1 / 3 : ℝ)) := Real.rpow_pos_of_pos hc _
  have p2 : 0 < c ^ (-1 : ℝ) := Real.rpow_pos_of_pos hc _
  exact ⟨a.trans (mul_le_mul_of_nonneg_right hCC p1.le), b.trans (mul_le_mul_of_nonneg_right hCC p2.le)⟩

/-- The chart for one sign `ε`, from `CtPsiAnalytic ε`: there are `m, C, K` such that for `8c₁² ≤ m` and `c ≥ K(1 + c₁⁻²)`
the four clauses of `CtChartComplex` hold with the constant `C`. -/
theorem ct_chart_of_psiAnalytic {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (hψ : CtPsiAnalytic ε) :
    ∃ m C K : ℝ, 0 < m ∧ 0 ≤ C ∧ 1 ≤ K ∧ ∀ c₁ : ℝ, 0 < c₁ → 8 * c₁ ^ 2 ≤ m → ∀ c : ℝ, K * (1 + (c₁⁻¹) ^ 2) ≤ c →
      CtChartBody c₁ ε c C := by
  obtain ⟨ρΨ, Ψ, hρ, hd, hconj, hag⟩ := hψ
  set r := ρΨ / 2 with hrdef
  have hr0 : 0 < r := by positivity
  have hr : r < ρΨ := by rw [hrdef]; linarith
  have hsub : closedBall (0 : ℂ) r ⊆ ball 0 ρΨ := closedBall_subset_ball hr
  obtain ⟨M1, hM1⟩ := (isCompact_closedBall (0 : ℂ) r).exists_bound_of_continuousOn (hd.continuousOn.mono hsub)
  have hdc : ContinuousOn (deriv Ψ) (ball 0 ρΨ) := ((hd.analyticOnNhd isOpen_ball).deriv).continuousOn
  obtain ⟨M2, hM2⟩ := (isCompact_closedBall (0 : ℂ) r).exists_bound_of_continuousOn (hdc.mono hsub)
  set M : ℝ := max 0 (max M1 M2) with hMdef
  have hM0 : 0 ≤ M := le_max_left _ _
  have hM : ∀ z ∈ closedBall (0 : ℂ) r, ‖Ψ z‖ ≤ M ∧ ‖deriv Ψ z‖ ≤ M := fun z hz =>
    ⟨(hM1 z hz).trans ((le_max_left _ _).trans (le_max_right _ _)), (hM2 z hz).trans ((le_max_right _ _).trans (le_max_right _ _))⟩
  obtain ⟨ρW, MW, hρW, hMW, hwin⟩ := ctPsi_window hε
  have hW : PsiWin ε ρW MW := ⟨hρW, hMW, hwin⟩
  refine ⟨min (r / 8) (ρW / 2), 2 * M, max 1 (max (2 * M) (max (4 * M / r) (max (2 * MW) (M + 1)))), by positivity,
    by positivity, le_max_left _ _, ?_⟩
  intro c₁ hc₁ hm c hc
  set K := max 1 (max (2 * M) (max (4 * M / r) (max (2 * MW) (M + 1)))) with hK
  have hK1 : 1 ≤ K := le_max_left _ _
  have hinv : 0 ≤ (c₁⁻¹) ^ 2 := sq_nonneg _
  have hcK : K ≤ c := by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ K) hinv]
  have hcpos : 0 < c := by linarith
  have h2M : 2 * M ≤ c := (le_max_left _ _).trans ((le_max_right _ _).trans hcK)
  have h4M : 4 * M ≤ r * c := by
    have : 4 * M / r ≤ c :=
      ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hcK)))
    rw [div_le_iff₀ hr0] at this; linarith
  have hcW : 2 * MW ≤ c :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hcK))))
  have hMc : M < 2 * c₁ ^ 2 * c := by
    have h1 : M + 1 ≤ K :=
      ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
    have h2 : K * (c₁⁻¹) ^ 2 ≤ c := by nlinarith
    have h3 : (M + 1) * (c₁⁻¹) ^ 2 ≤ c := (mul_le_mul_of_nonneg_right h1 hinv).trans h2
    have h4 : (c₁⁻¹) ^ 2 * c₁ ^ 2 = 1 := by field_simp
    have h5 : M + 1 ≤ c₁ ^ 2 * c := by
      have := mul_le_mul_of_nonneg_left h3 (sq_nonneg c₁)
      calc M + 1 = c₁ ^ 2 * ((M + 1) * (c₁⁻¹) ^ 2) := by
            have : c₁ ^ 2 * ((M + 1) * (c₁⁻¹) ^ 2) = (M + 1) * ((c₁⁻¹) ^ 2 * c₁ ^ 2) := by ring
            rw [this, h4, mul_one]
        _ ≤ c₁ ^ 2 * c := this
    nlinarith
  have hν1 : 8 * c₁ ^ 2 ≤ r / 8 := hm.trans (min_le_left _ _)
  have hν2 : 8 * c₁ ^ 2 ≤ ρW / 2 := hm.trans (min_le_right _ _)
  exact ctChartBody_of_data hc₁ hcpos hd hr hr0 hM hconj hag hW h2M h4M hcW hMc hν1 hν2

/-- **`CtChartComplex c₁` from the analyticity of `ψ_ε`** (`ct:cfu`, `ct:phic-exp`): if `ψ_{+1}` and `ψ_{-1}` extend holomorphically
across `a = 0` (`CtPsiAnalytic`), there is `c₁₀ > 0` such that `CtChartComplex c₁` holds for every `0 < c₁ ≤ c₁₀`: the complex chart
`φ_c = û⁻¹` exists on a disc of radius `> R_max = 4c₁²c^{2/3}`, is real on the real axis, and satisfies `|φ_c(u) - u| ≤ C c^{-1/3}`,
`|φ_c'(u) - 1| ≤ C c^{-1}` for `|u| ≤ R_max`, `c ≥ c₀(c₁)`. -/
theorem ct_chart_complex_of_analytic (h₁ : CtPsiAnalytic 1) (h₂ : CtPsiAnalytic (-1)) :
    ∃ c₁₀ : ℝ, 0 < c₁₀ ∧ ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ c₁₀ → CtChartComplex c₁ := by
  obtain ⟨m₁, C₁, K₁, hm₁, hC₁, hK₁, H₁⟩ := ct_chart_of_psiAnalytic (Or.inl rfl) h₁
  obtain ⟨m₂, C₂, K₂, hm₂, hC₂, hK₂, H₂⟩ := ct_chart_of_psiAnalytic (Or.inr rfl) h₂
  refine ⟨Real.sqrt (min m₁ m₂ / 8), Real.sqrt_pos.mpr (by positivity), fun c₁ hc₁ hle => ?_⟩
  have hsq : c₁ ^ 2 ≤ min m₁ m₂ / 8 := (Real.le_sqrt' hc₁).mp hle
  have hm : 8 * c₁ ^ 2 ≤ min m₁ m₂ := by linarith
  have hm₁' : 8 * c₁ ^ 2 ≤ m₁ := hm.trans (min_le_left _ _)
  have hm₂' : 8 * c₁ ^ 2 ≤ m₂ := hm.trans (min_le_right _ _)
  refine ⟨max C₁ C₂, max K₁ K₂ * (1 + (c₁⁻¹) ^ 2), le_max_of_le_left hC₁, ?_⟩
  intro ε hε c hc
  have hinv : 0 ≤ (c₁⁻¹) ^ 2 := sq_nonneg _
  have hKc : 1 ≤ max K₁ K₂ * (1 + (c₁⁻¹) ^ 2) := by
    have : 1 ≤ max K₁ K₂ := hK₁.trans (le_max_left _ _)
    nlinarith
  have hcpos : 0 < c := by linarith
  rcases hε with rfl | rfl
  · refine (H₁ c₁ hc₁ hm₁' c ?_).mono hcpos (le_max_left _ _)
    exact (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)).trans hc
  · refine (H₂ c₁ hc₁ hm₂' c ?_).mono hcpos (le_max_right _ _)
    exact (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)).trans hc

/-- info: 'FormalResearch.SignUncertainty.ct_chart_complex_of_analytic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_chart_complex_of_analytic

end FormalResearch.SignUncertainty
