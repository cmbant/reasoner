module

public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroBumpPositivity
public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroWindow

/-!
# The window limit of `Ψ_g` for the bumped two-zero comb at every weight (`ut:T2`, "Window and vacuum normalisation")

Source: `upper_transfer.tex`, Theorem T2 (`ut:T2`) at fixed `(w, Q)`.  The test is `g_w = ½(h₂^{(p)} - 𝓗_w h₂^{(p)})`
(`twoZeroBumpG`), `h₂^{(p)} = sech² T_{χ(p)} B₁^{(p)}`.  With `u = -κσ`, `x = ξ_* + λσ`, `t = c x²/3`:

* `twoZeroBump_hat_window_bound` (Lemma `SD_G`, order `p`): `|𝓗_w h₂^{(p)}(t)| V(t) (dt/dσ) ≤ K c'` for `x ≥ ξ_*/2`
  (the far Cardy bound `cardyFarBoundP_prob` replaces the weight-one `cardyFarBound_prob`);
* `twoZeroBump_window_limit` (`eq:ut:T2-local` at weight `w`): `F_{2,c}^{-1} Ψ_g → C₂ W₂`, uniformly on `u ∈ [-R, R]`,
  on a compact family and in the cut `N' ≥ n + 2`: the bump multiplies the comb profile on the real axis by
  `R_bump ∈ [1, 1 + C/c']` for `x ≤ ξ_* + r_p` (`re_profile_bump`), so the limit is that of the unbumped comb;
* `twoZeroBump_window_field`: the `window` field of `TwoZeroTransferData` with `g = twoZeroBumpG prob`.

All results are proved unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Upper.Window FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.Upper.Design FormalResearch.ModularBootstrap.Upper.Membership
  FormalResearch.ModularBootstrap.Upper.Hankel FormalResearch.ModularBootstrap.Upper.Rigidity
  FormalResearch.ModularBootstrap.Upper.Positivity FormalResearch.ModularBootstrap.Upper.Assembly
  FormalResearch.ModularBootstrap.Upper.Window.Cardy FormalResearch.ModularBootstrap.Upper.Bump
open TwoZeroDesign

/-- The test `g_w = ½(h₂^{(p)} - 𝓗_w h₂^{(p)})` for an arbitrary bump `bd` and cut `N'`. -/
noncomputable def twoZeroBumpGN (prob : FixedWeightProblem) (bd : BumpData) {n : ℕ} (d : TwoZeroDesign n) (c : ℝ)
    (N' : ℕ) : ℝ → ℝ :=
  pairOdd (combProfile c (d.bumpComb bd c N')) (hankelTransform prob.w (combProfile c (d.bumpComb bd c N')))

lemma twoZeroBumpG_eq (prob : FixedWeightProblem) {n : ℕ} (d : TwoZeroDesign n) (c : ℝ) :
    twoZeroBumpG prob d c = twoZeroBumpGN prob (probBump prob) d c (bumpCut (probBump prob) (n + 2) c) := rfl

/-- `F_{2,c} = FK^{(2)}_c · πλ/(2√2)` with the measure normalisation of Lemma `W` (no hypothesis on the weight). -/
lemma twoZeroF_eq_windowMeasureNormK_w (prob : FixedWeightProblem) {c : ℝ} (hc : 0 < c) :
    twoZeroF prob c = windowMeasureNormK prob 2 c * (π * lambdaComb c / (2 * √2)) := by
  rw [windowMeasureNormK_eq_FKc prob 2 hc]; rfl

/-! ### Lemma `SD_G` at order `p` against the far Cardy bound -/

/-- **Lemma `SD_G` against the far Cardy bound for the bumped two-zero comb, every weight**:
`|𝓗_w h₂^{(p)}(t)| V(t) (2 c x/3) ≤ K c'` for `x ≥ ξ_*/2`, uniformly on a compact family and in the cut. -/
theorem twoZeroBump_hat_window_bound (prob : FixedWeightProblem) (bd : BumpData) {n : ℕ}
    {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ c in atTop, ∀ d ∈ 𝒦, ∀ N' : ℕ, n + 2 ≤ N' → ∀ x : ℝ, xiStar / 2 ≤ x →
      |hankelTransform prob.w (combProfile c (d.bumpComb bd c N')) (c * x ^ 2 / 3) *
        prob.cardyV (c / 12) (c * x ^ 2 / 3) * (2 * c * x / 3)| ≤ K * c := by
  obtain ⟨KG, hKG, hglobal⟩ := twoZeroBump_globalP bd (prob.w - 1) hK hA
  obtain ⟨C, c₀, hC, hfar⟩ := cardyFarBoundP_prob prob (x₀ := xiStar / 2) (half_pos xiStar_pos)
  have hξ := xiStar_pos
  refine ⟨KG * C * (1 + 2 / xiStar) ^ (prob.w - 1), by positivity, ?_⟩
  filter_upwards [hglobal, twoZeroBump_k7W prob bd hK hA, twoZeroBump_innerCombHyp bd hK hA,
    eventually_ge_atTop c₀, eventually_ge_atTop (3 / (2 * π * xiStar)),
    eventually_gt_atTop (0 : ℝ)] with c hp hk7 hin hc₀ hc3 hcpos d hd N' hNN' x hx
  have hxpos : 0 < x := lt_of_lt_of_le (half_pos hξ) hx
  obtain ⟨C₀, hC0, hd1, hd2, -⟩ := hk7 d hd N' hNN'
  have ht0 : 0 < c * x ^ 2 / 3 := by positivity
  have hone : 1 ≤ 4 * π * c * x / 3 := by
    have h1 : 3 / (2 * π * xiStar) * (2 * π * xiStar) = 3 := by field_simp
    have h2 : 3 ≤ c * (2 * π * xiStar) := by
      have := mul_le_mul_of_nonneg_right hc3 (by positivity : 0 ≤ 2 * π * xiStar)
      linarith
    have h4 : 2 * π * xiStar ≤ 4 * π * x := by
      nlinarith only [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hx)]
    have h3 : c * (2 * π * xiStar) ≤ c * (4 * π * x) := mul_le_mul_of_nonneg_left h4 hcpos.le
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
    linarith only [h2, h3]
  have hht := hp d hd N' hNN' x hxpos hone
  have e2 := (hin d hd N' hNN').edgeHankelP_eq (prob.w - 1) hcpos hd1 ht0
  rw [Nat.sub_add_cancel prob.hw] at e2
  have e3 : edgeHankelP (prob.w - 1) c (fun b => sechSqProfile b * d.bumpComb bd c N' b) (c * x ^ 2 / 3) =
      ((hankelTransform prob.w (combProfile c (d.bumpComb bd c N')) (c * x ^ 2 / 3) : ℝ) : ℂ) := e2
  rw [e3, Complex.norm_real, Real.norm_eq_abs] at hht
  obtain ⟨hV0, hVb⟩ := hfar c hc₀ x hx
  rw [besselL_eq_edgeL] at hVb
  set p := prob.w - 1 with hp'
  set A' : ℝ := |hankelTransform prob.w (combProfile c (d.bumpComb bd c N')) (c * x ^ 2 / 3)| with hA'
  set V : ℝ := prob.cardyV (c / 12) (c * x ^ 2 / 3) with hV
  have hA0' : 0 ≤ A' := abs_nonneg _
  have hx3 : 0 ≤ 2 * c * x / 3 := by positivity
  rw [abs_mul, abs_mul, abs_of_nonneg hV0, abs_of_nonneg hx3, ← hA']
  have h1 : A' * V * (2 * c * x / 3) =
      (Real.exp (c * edgeL x) * A') * (V * Real.exp (-(c * edgeL x)) * (2 / 3 * c * x)) := by
    rw [Real.exp_neg]
    have := Real.exp_pos (c * edgeL x)
    field_simp
  rw [h1]
  have h2 : (Real.exp (c * edgeL x) * A') * (V * Real.exp (-(c * edgeL x)) * (2 / 3 * c * x)) ≤
      (KG * √(c / x) * (1 / x) ^ p) * (C * √c * √x * (1 + x) ^ p) :=
    mul_le_mul hht hVb (by
      have := Real.exp_pos (-(c * edgeL x))
      positivity) (by positivity)
  have e1 : √(c / x) * √x = √c := by
    rw [← Real.sqrt_mul (by positivity), div_mul_cancel₀ _ hxpos.ne']
  have e1' : √c * √c = c := Real.mul_self_sqrt hcpos.le
  have h3 : (KG * √(c / x) * (1 / x) ^ p) * (C * √c * √x * (1 + x) ^ p) =
      KG * C * c * ((1 / x) * (1 + x)) ^ p := by
    calc (KG * √(c / x) * (1 / x) ^ p) * (C * √c * √x * (1 + x) ^ p)
        = KG * C * ((√(c / x) * √x) * √c) * ((1 / x) ^ p * (1 + x) ^ p) := by ring
      _ = KG * C * c * ((1 / x) * (1 + x)) ^ p := by rw [e1, e1', mul_pow]
  have h4 : ((1 / x) * (1 + x)) ^ p ≤ (1 + 2 / xiStar) ^ p := by
    refine pow_le_pow_left₀ (by positivity) ?_ p
    have h5 : 1 / x ≤ 2 / xiStar := by
      have := one_div_le_one_div_of_le (half_pos hξ) hx
      rwa [one_div_div] at this
    have h6 : (1 / x) * (1 + x) = 1 / x + 1 := by field_simp
    rw [h6]
    linarith
  calc (Real.exp (c * edgeL x) * A') * (V * Real.exp (-(c * edgeL x)) * (2 / 3 * c * x))
      ≤ (KG * √(c / x) * (1 / x) ^ p) * (C * √c * √x * (1 + x) ^ p) := h2
    _ = KG * C * c * ((1 / x) * (1 + x)) ^ p := h3
    _ ≤ KG * C * c * (1 + 2 / xiStar) ^ p :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = KG * C * (1 + 2 / xiStar) ^ p * c := by ring

/-! ### The window limit -/

/-- The bump multiplies the comb factor: `|T - q s| ≤ a q |s|`, `1 ≤ R ≤ 1 + δ` give `|R T - q s| ≤ (a + 2δ) q |s|`. -/
lemma bumped_P_bound {R T q s a δ : ℝ} (hq : 0 < q) (hR1 : 1 ≤ R) (hRδ : R ≤ 1 + δ) (ha1 : a ≤ 1)
    (hT : |T - q * s| ≤ a * q * |s|) : |R * T - q * s| ≤ (a + 2 * δ) * q * |s| := by
  have hqs : 0 ≤ q * |s| := by positivity
  have hT' : |T| ≤ 2 * (q * |s|) := by
    have h1 : |T| ≤ |q * s| + |T - q * s| := by
      calc |T| = |q * s + (T - q * s)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    rw [abs_mul, abs_of_pos hq] at h1
    nlinarith only [h1, hT, ha1, hqs]
  have e : R * T - q * s = (R - 1) * T + (T - q * s) := by ring
  have hR0 : 0 ≤ R - 1 := by linarith
  have hδ : 0 ≤ δ := by linarith
  rw [e]
  calc |(R - 1) * T + (T - q * s)| ≤ |(R - 1) * T| + |T - q * s| := abs_add_le _ _
    _ = (R - 1) * |T| + |T - q * s| := by rw [abs_mul, abs_of_nonneg hR0]
    _ ≤ δ * (2 * (q * |s|)) + a * q * |s| := by
        refine add_le_add (mul_le_mul (by linarith) hT' (abs_nonneg _) hδ) hT
    _ = (a + 2 * δ) * q * |s| := by ring

/-- **The window limit of `Ψ_g` for the bumped two-zero comb, every weight** (`ut:T2`, `eq:ut:T2-local` including the
`ĥ` part): for every bump `bd`, compact family `𝒦` of admissible designs, `R ≥ 0`, `ε > 0`: for `c` large,
`|F_{2,c}^{-1} Ψ_{g}(u) - C₂ W₂(u)| ≤ ε` for all `d ∈ 𝒦`, cuts `N' ≥ n + 2` and `u ∈ [-R, R]`, with
`g = twoZeroBumpGN prob bd d c N'`. -/
theorem twoZeroBump_window_limit (prob : FixedWeightProblem) (bd : BumpData) {n : ℕ}
    {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) {R : ℝ} (hR : 0 ≤ R)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ c in atTop, ∀ d ∈ 𝒦, ∀ N' : ℕ, n + 2 ≤ N' → ∀ u ∈ Icc (-R) R,
      |(twoZeroF prob c)⁻¹ * psiAiry prob c (twoZeroBumpGN prob bd d c N') u - twoZeroC₂ * d.Wr u| ≤ ε := by
  have hκ := kappaAiry_pos
  have hξ := xiStar_pos
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = R / kappaAiry := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hSdef]; positivity
  obtain ⟨S₁, hS₁0, hS₁⟩ := hK.exists_sigmaP_bound
  obtain ⟨CT, hCT0, hTev⟩ := twoZeroT_window_bound (S + S₁) (by positivity)
  obtain ⟨B₀, hB₀, hBb⟩ := CompactCombFamily.tildeW_bound (toModifiedFamily hK hA) hS0
  obtain ⟨K, hK0, hKev⟩ := twoZeroBump_hat_window_bound prob bd hK hA
  obtain ⟨Cp, C', hbump⟩ := re_profile_bump (n := n) bd
  obtain ⟨n1, hn1⟩ := (phiWKB_succ_tendsto.eventually_ge_atTop S).exists
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = 2 * kappaAiry * ε / 3 := ⟨_, rfl⟩
  have he0 : 0 < e := by rw [he]; positivity
  obtain ⟨ε₁, hε₁⟩ : ∃ ε₁ : ℝ, ε₁ = e / (2 * (S + S₁) + 1) := ⟨_, rfl⟩
  have hε₁0 : 0 < ε₁ := by rw [hε₁]; positivity
  obtain ⟨C₀, hC₀, hWm⟩ := lemma_W_measure prob (toModifiedFamily hK hA) hS0 n1 ε₁ hε₁0
  obtain ⟨M', hM'⟩ : ∃ M' : ℝ, M' = CT * (2 * √2 / π) := ⟨_, rfl⟩
  have hM'0 : 0 ≤ M' := by rw [hM']; positivity
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = min 1 (e / ((S + S₁) * B₀ + 1)) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; exact lt_min one_pos (by positivity)
  obtain ⟨C'', hC''⟩ : ∃ C'' : ℝ, C'' = max C' 0 := ⟨_, rfl⟩
  have hC''0 : 0 ≤ C'' := by rw [hC'']; exact le_max_right _ _
  have hFc := twoZeroFConst_pos prob
  filter_upwards [hKev, hbump, hTev, eventually_ge_atTop C₀, lambda_mul_le M' (half_pos hδ0),
    lambda_mul_le S (half_pos hξ), lambda_mul_le S bd.r_pos,
    eventually_gt_atTop (0 : ℝ),
    eventually_ge_atTop (4 * C'' / δ),
    Real.tendsto_sqrt_atTop.eventually_ge_atTop (K / (twoZeroFConst prob * e)),
    tendsto_lambdaComb_atTop.eventually_le_const (zero_lt_one : (0 : ℝ) < 1)]
    with c hKc hbc hTc hc₀ hlM hlS hlr hc0 hcδ hsq hl1' d hd N' hN' u hu
  have hlam := lambdaComb_pos' hc0
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = -u / kappaAiry := ⟨_, rfl⟩
  have hσκ : σ * kappaAiry = -u := by rw [hσ]; field_simp
  have hσS : |σ| ≤ S := by
    rw [hSdef] at *
    rw [abs_le]
    constructor
    · by_contra h
      push Not at h
      have h' := mul_lt_mul_of_pos_right h hκ
      have : R / kappaAiry * kappaAiry = R := by field_simp
      nlinarith [hu.2]
    · by_contra h
      push Not at h
      have h' := mul_lt_mul_of_pos_right h hκ
      have : R / kappaAiry * kappaAiry = R := by field_simp
      nlinarith [hu.1]
  have hσI : σ ∈ Icc (-S) (phiWKB (n1 + 1)) := ⟨(abs_le.1 hσS).1, (abs_le.1 hσS).2.trans hn1⟩
  have hσI' : σ ∈ Icc (-S) S := ⟨(abs_le.1 hσS).1, (abs_le.1 hσS).2⟩
  have hx : xiStar / 2 ≤ xiStar + lambdaComb c * σ := by
    have := mul_le_mul_of_nonneg_left (abs_le.1 hσS).1 hlam.le
    nlinarith
  have hx0 : 0 ≤ xiStar + lambdaComb c * σ := by linarith
  have hxr : xiStar + lambdaComb c * σ ≤ xiStar + bd.r := by
    have := mul_le_mul_of_nonneg_left (abs_le.1 hσS).2 hlam.le
    linarith
  have hWu : -kappaAiry * σ = u := by rw [hσ]; field_simp
  have hFKpos : 0 < windowMeasureNormK prob 2 c := by
    rw [windowMeasureNormK_eq_FKc prob 2 hc0]
    exact FKc_pos (qProb_pos prob) 2 hc0
  have hq₀pos : 0 < π * lambdaComb c / (2 * √2) := by positivity
  have hF : twoZeroF prob c = windowMeasureNormK prob 2 c * (π * lambdaComb c / (2 * √2)) :=
    twoZeroF_eq_windowMeasureNormK_w prob hc0
  -- comb part from Lemma W
  have hB := hWm hc₀ d.toModified (toModifiedFamily_mem hK hA hd) σ hσI
  simp only [] at hB
  have hWtb := hBb d.toModified (toModifiedFamily_mem hK hA hd) σ hσI'
  -- the factor T
  have hsb : |σ - d.sigmaP| ≤ S + S₁ :=
    (abs_sub _ _).trans (add_le_add hσS (hS₁ d hd))
  have hPb : |tFac (d.chiP c) (xiStar + lambdaComb c * σ) - π * lambdaComb c / (2 * √2) * (σ - d.sigmaP)| ≤
      (M' * lambdaComb c) * (π * lambdaComb c / (2 * √2)) * |σ - d.sigmaP| := by
    have h := hTc σ d.p (hσS.trans (by linarith)) (by
      have := hS₁ d hd
      unfold sigmaP at this
      rw [neg_div, abs_neg] at this
      linarith)
    have e1 : ((xiStar + lambdaComb c * (-d.p / kappaAiry) : ℝ) : ℂ) = ((d.chiP c : ℝ) : ℂ) := rfl
    rw [e1, tFac_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
    have e2 : (-d.p / kappaAiry) = d.sigmaP := rfl
    rw [e2] at h
    have : CT * lambdaComb c ^ 2 * |σ - d.sigmaP| =
        (M' * lambdaComb c) * (π * lambdaComb c / (2 * √2)) * |σ - d.sigmaP| := by
      rw [hM']
      have : √2 ≠ 0 := by positivity
      field_simp
    rw [← this]
    exact h
  have hl1 : M' * lambdaComb c ≤ δ / 2 := by rw [mul_comm]; exact hlM
  have ha0 : 0 ≤ M' * lambdaComb c := by positivity
  have ha1 : M' * lambdaComb c ≤ 1 := by
    have : δ ≤ 1 := by rw [hδ]; exact min_le_left _ _
    linarith
  -- the bump factor
  obtain ⟨Rb, hR1, -, hRn, hre⟩ := hbc d N' hN' _ hx0
  have hRb : Rb ≤ 1 + C'' / c := by
    have := hRn hxr
    have h2 : C' / c ≤ C'' / c := div_le_div_of_nonneg_right (by rw [hC'']; exact le_max_left _ _) hc0.le
    linarith
  have hδc : 2 * (C'' / c) ≤ δ / 2 := by
    have h1 : 4 * C'' / δ ≤ c := hcδ
    have h2 := (div_le_iff₀ hδ0).mp h1
    have : C'' / c ≤ δ / 4 := by
      rw [div_le_iff₀ hc0]; linarith
    linarith
  have hPb' := bumped_P_bound hq₀pos hR1 hRb ha1 hPb
  have ha' : M' * lambdaComb c + 2 * (C'' / c) ≤ δ := by linarith
  have ha0' : 0 ≤ M' * lambdaComb c + 2 * (C'' / c) := by positivity
  have ha1' : M' * lambdaComb c + 2 * (C'' / c) ≤ 1 :=
    ha'.trans (by rw [hδ]; exact min_le_left _ _)
  -- the transform part
  have hHh := hKc d hd N' hN' _ hx
  have hHh' : |hankelTransform prob.w (combProfile c (d.bumpComb bd c N'))
        (c * (xiStar + lambdaComb c * σ) ^ 2 / 3) *
      prob.cardyV (c / 12) (c * (xiStar + lambdaComb c * σ) ^ 2 / 3) *
        ((2 * c * (xiStar + lambdaComb c * σ) / 3) * lambdaComb c)| ≤
      e * (windowMeasureNormK prob 2 c * (π * lambdaComb c / (2 * √2))) := by
    rw [← hF, twoZeroF_eq_const_mul prob hc0]
    have hc32 : c ^ (3 / 2 : ℝ) = c * √c := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hc0, Real.rpow_one, ← Real.sqrt_eq_rpow]
    rw [hc32]
    have hsq' : K ≤ e * twoZeroFConst prob * √c := by
      have := (div_le_iff₀ (mul_pos hFc he0)).1 hsq
      linarith
    have e1 : ∀ h' V' x' : ℝ, h' * V' * ((2 * c * x' / 3) * lambdaComb c) =
        (h' * V' * (2 * c * x' / 3)) * lambdaComb c := fun _ _ _ => by ring
    rw [e1, abs_mul, abs_of_pos hlam]
    calc _ ≤ (K * c) * 1 := mul_le_mul hHh hl1' hlam.le (by positivity)
      _ = K * c := mul_one _
      _ ≤ (e * twoZeroFConst prob * √c) * c := by gcongr
      _ = e * (twoZeroFConst prob * (c * √c)) := by ring
  -- identification of the limit
  have hID := tildeW_toModified_Wr d σ
  have hC : twoZeroC₂ * d.Wr u = (1 / (2 * kappaAiry)) *
      ((σ - d.sigmaP) * tildeW 2 d.toModified.sigmaFLim d.toModified.allSigmaLim d.toModified.allEpsLim σ) := by
    rw [← hWu]
    have e1 : (σ - d.sigmaP) * tildeW 2 d.toModified.sigmaFLim d.toModified.allSigmaLim
        d.toModified.allEpsLim σ = CStar * kappaAiry ^ 2 * d.Wr (-kappaAiry * σ) := by
      have : tildeW 2 d.toModified.sigmaFLim d.toModified.allSigmaLim d.toModified.allEpsLim σ *
          (σ - d.sigmaP) = CStar * kappaAiry ^ 2 * d.Wr (-kappaAiry * σ) := hID
      linarith
    rw [e1]
    unfold twoZeroC₂
    field_simp
  have hprof : combProfile c (d.bumpComb bd c N') (c * (xiStar + lambdaComb c * σ) ^ 2 / 3) =
      Rb * (tFac (d.chiP c) (xiStar + lambdaComb c * σ) *
        modifiedH0 2 (n + 2) d.toModified c (xiStar + lambdaComb c * σ)) := by
    rw [← twoZero_combProfile_eq d hc0 hx0]
    unfold combProfile combH0
    rw [xOf_comp hc0 hx0]
    exact hre
  have hpsi : psiAiry prob c (twoZeroBumpGN prob bd d c N') u =
      (((Rb * tFac (d.chiP c) (xiStar + lambdaComb c * σ)) *
            modifiedH0 2 (n + 2) d.toModified c (xiStar + lambdaComb c * σ) -
          hankelTransform prob.w (combProfile c (d.bumpComb bd c N'))
            (c * (xiStar + lambdaComb c * σ) ^ 2 / 3)) / 2) *
        prob.cardyV (c / 12) (c * (xiStar + lambdaComb c * σ) ^ 2 / 3) *
        (((2 * c * (xiStar + lambdaComb c * σ) / 3) * lambdaComb c) / kappaAiry) := by
    unfold twoZeroBumpGN
    rw [psiAiry_pairOdd_eq prob hc0 _ _ (u := u) (by rw [← hσ]; exact hx0), ← hσ, hprof]
    ring
  rw [hpsi, hC, hF]
  have h1 : 2 * (S + S₁) * ε₁ ≤ e := by
    rw [hε₁]; exact eps_split (by positivity) he0
  have h2 : (M' * lambdaComb c + 2 * (C'' / c)) * (S + S₁) * B₀ ≤ e :=
    small_mul ha0' (by positivity) hB₀.le (ha'.trans (by rw [hδ]; exact min_le_right _ _))
  exact window_error_bound hκ hFKpos hq₀pos he hB hWtb hsb hPb' ha0' ha1' h1 h2 hHh'

/-- The `window` field of `TwoZeroTransferData` for `F = twoZeroF prob`, `g = twoZeroBumpG prob`, `C₂ = twoZeroC₂`
(same quantifiers and form as the field). -/
theorem twoZeroBump_window_field (prob : FixedWeightProblem) {n : ℕ}
    {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∀ R : ℝ, 0 ≤ R → ∀ ε : ℝ, 0 < ε → ∀ᶠ c : ℝ in atTop, ∀ d ∈ 𝒦, ∀ u ∈ Icc (-R) R,
      |(twoZeroF prob c)⁻¹ * psiAiry prob c (twoZeroBumpG prob d c) u - twoZeroC₂ * d.Wr u| ≤ ε := by
  intro R hR ε hε
  filter_upwards [twoZeroBump_window_limit prob (probBump prob) hK hA hR hε,
    eventually_gt_atTop (0 : ℝ)] with c h hc d hd u hu
  exact h d hd _ (le_bumpCut (probBump prob) (n + 2) c) u hu

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZeroBump_window_field' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZeroBump_window_field


/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZeroBump_hat_window_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZeroBump_hat_window_bound

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZeroBump_window_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZeroBump_window_limit

end FormalResearch.ModularBootstrap.TwoLevel
