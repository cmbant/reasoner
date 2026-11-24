module

public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroWindowNorm
public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroCombK7
public import FormalResearch.ModularBootstrap.Upper.Assembly.PsiBounds

/-!
# The window limit of `Ψ_g` for the two-zero comb (`upper_transfer.tex`, Theorem T2 `ut:T2`, "Window and vacuum normalisation")

The functional of `ut:T2` is `g_c = ½(h₂ - ĥ₂)` with `h₂ = sech²(πb/2) T_{χ(p)} B₁` (`TwoZeroDesign.twoZeroComb`),
`twoZeroG d c = pairOdd (combProfile c B₂) (hankelTransform 1 (combProfile c B₂))`.  With `u = -κσ`, `x = ξ_* + λσ`,
`t = c x²/3`, `Ψ_g(u) = g(t) V(t) J`, `J = (dt/dσ)/κ`:

* `psiAiry_pairOdd_eq`: `Ψ_g(u) = ½ (h(t) - ĥ(t)) V(t) (dt/dσ)/κ` (any `h`, `ĥ`);
* `twoZero_combProfile_eq`: `h₂(t) = T_{χ(p)}(x) · h₀^{(2)}(x)` with `h₀^{(2)} = modifiedH0 2 (n+2) (toModified d)`;
* `twoZero_hat_window_bound` (Lemma `SD_G`): `|ĥ₂(t)| V(t) (dt/dσ) ≤ K c'` for `x ≥ ξ_*/2`, uniformly on a compact family;
* `twoZero_window_limit` (`eq:ut:T2-local` with the `ĥ` part): `F_{2,c}^{-1} Ψ_g → C₂ W₂` uniformly on
  `u ∈ [-R, R]` and on a compact family of admissible designs, `C₂ = C_* κ / 2`, `F_{2,c} = twoZeroF`.
  The comb part is Lemma `W` at `f = 2` (`lemma_W_measure`, uniform on the family) with `ut:ID`
  (`tildeW_toModified_Wr`) and the window form of the factor `T_{χ(p)}` (`twoZeroT_window_bound`); the `ĥ` part is
  `O(c'/F_{2,c}) = O(c'^{-1/2})`.

All results are proved unconditionally (for `prob.w = 1`).
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
  FormalResearch.ModularBootstrap.Upper.Window.Cardy
open TwoZeroDesign

/-- The functional `g_c = ½(h₂ - ĥ₂)` of `ut:T2` (`h₂ = sech² · T_{χ(p)} B₁`). -/
noncomputable def twoZeroG {n : ℕ} (d : TwoZeroDesign n) (c : ℝ) : ℝ → ℝ :=
  pairOdd (combProfile c (d.twoZeroComb c)) (hankelTransform 1 (combProfile c (d.twoZeroComb c)))

/-- `C₂ = C_*^{(2)}/(2κ) = C_* κ/2` (`ut:T2`). -/
noncomputable def twoZeroC₂ : ℝ := CStar * kappaAiry / 2

lemma twoZeroC₂_pos : 0 < twoZeroC₂ := by
  have := CStar_pos
  have := kappaAiry_pos
  unfold twoZeroC₂; positivity

/-! ### Pointwise forms -/

/-- `Ψ_g(u) = ½ (h(t) - ĥ(t)) V(t) (dt/dσ)/κ` at `t = c x²/3`, `x = ξ_* + λσ`, `σ = -u/κ`. -/
lemma psiAiry_pairOdd_eq (prob : FixedWeightProblem) {c : ℝ} (hc : 0 < c) (h ĥ : ℝ → ℝ) {u : ℝ}
    (hx : 0 ≤ xiStar + lambdaComb c * (-u / kappaAiry)) :
    psiAiry prob c (pairOdd h ĥ) u =
      ((h (c * (xiStar + lambdaComb c * (-u / kappaAiry)) ^ 2 / 3) -
          ĥ (c * (xiStar + lambdaComb c * (-u / kappaAiry)) ^ 2 / 3)) / 2) *
        prob.cardyV (c / 12) (c * (xiStar + lambdaComb c * (-u / kappaAiry)) ^ 2 / 3) *
        (((2 * c * (xiStar + lambdaComb c * (-u / kappaAiry)) / 3) * lambdaComb c) / kappaAiry) := by
  unfold psiAiry pairOdd
  rw [tAiry_eq hc hx, jAiry_eq hc hx]

/-- `h₂(c x²/3) = T_{χ(p)}(x) · h₀^{(2)}(x)` for `x ≥ 0`. -/
lemma twoZero_combProfile_eq {n : ℕ} (d : TwoZeroDesign n) {c x : ℝ} (hc : 0 < c) (hx : 0 ≤ x) :
    combProfile c (d.twoZeroComb c) (c * x ^ 2 / 3) =
      tFac (d.chiP c) x * modifiedH0 2 (n + 2) d.toModified c x := by
  unfold combProfile combH0 modifiedH0
  rw [xOf_comp hc hx]
  unfold twoZeroComb
  rw [d.comb_eq_modifiedCombB, Upper.Membership.sechSqProfile_ofReal, tFac_eq, ← mul_assoc, ← Complex.ofReal_mul,
    Complex.re_ofReal_mul]
  ring

/-! ### Lemma `SD_G` for `h₂` -/

/-- **Lemma `SD_G` against the far Cardy bound for `h₂`**: `|ĥ₂(t)| V(t) (2 c x/3) ≤ K c'` for `x ≥ ξ_*/2`,
uniformly on a compact family of admissible designs. -/
theorem twoZero_hat_window_bound (prob : FixedWeightProblem) (hw : prob.w = 1) {n : ℕ}
    {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ c in atTop, ∀ d ∈ 𝒦, ∀ x : ℝ, xiStar / 2 ≤ x →
      |hankelTransform 1 (combProfile c (d.twoZeroComb c)) (c * x ^ 2 / 3) *
        prob.cardyV (c / 12) (c * x ^ 2 / 3) * (2 * c * x / 3)| ≤ K * c := by
  obtain ⟨K, hK0, hKe⟩ := edge_global_bound
  obtain ⟨C, c₀, hC, hfar⟩ := cardyFarBound_prob prob hw (x₀ := xiStar / 2) (half_pos xiStar_pos)
  refine ⟨K * C, by positivity, ?_⟩
  filter_upwards [twoZeroComb_innerCombHyp hK hA, twoZeroComb_k7_membership_vacuum hw hK hA,
    eventually_ge_atTop c₀, eventually_gt_atTop (0 : ℝ)] with c hI hK7 hc₀ hcpos d hd x hx
  have hxpos : 0 < x := lt_of_lt_of_le (half_pos xiStar_pos) hx
  obtain ⟨C₀, hC0, hd1, -⟩ := hK7 d hd
  have ht0 : 0 < c * x ^ 2 / 3 := by positivity
  have hsd := hKe (combH0 (d.twoZeroComb c)) π 8 1 Real.pi_pos (hI d hd).edgeHankelHyp zero_le_one
    (hI d hd).edgeSechBound c x hcpos hxpos
  rw [(hI d hd).edgeHankel_eq hcpos hd1 ht0, Complex.norm_real, Real.norm_eq_abs] at hsd
  obtain ⟨hV0, hVb⟩ := hfar c hc₀ x hx
  rw [besselL_eq_edgeL] at hVb
  set A : ℝ := |hankelTransform 1 (combProfile c (d.twoZeroComb c)) (c * x ^ 2 / 3)| with hA'
  set V : ℝ := prob.cardyV (c / 12) (c * x ^ 2 / 3) with hV
  have hA0 : 0 ≤ A := abs_nonneg _
  have hx3 : 0 ≤ 2 * c * x / 3 := by positivity
  rw [abs_mul, abs_mul, abs_of_nonneg hV0, abs_of_nonneg hx3, ← hA']
  have h1 : A * V * (2 * c * x / 3) =
      (Real.exp (c * edgeL x) * A) * (V * Real.exp (-(c * edgeL x)) * (2 / 3 * c * x)) := by
    rw [Real.exp_neg]
    have := Real.exp_pos (c * edgeL x)
    field_simp
  rw [h1]
  have h2 : (Real.exp (c * edgeL x) * A) * (V * Real.exp (-(c * edgeL x)) * (2 / 3 * c * x)) ≤
      (K * 1 * √(c / x)) * (C * √c * √x) :=
    mul_le_mul hsd hVb (by
      have := Real.exp_pos (-(c * edgeL x))
      positivity) (by positivity)
  have h3 : (K * 1 * √(c / x)) * (C * √c * √x) = K * C * c := by
    have e1 : √(c / x) * √x = √c := by
      rw [← Real.sqrt_mul (by positivity), div_mul_cancel₀ _ hxpos.ne']
    have e2 : √c * √c = c := Real.mul_self_sqrt hcpos.le
    calc (K * 1 * √(c / x)) * (C * √c * √x) = K * C * ((√(c / x) * √x) * √c) := by ring
      _ = K * C * c := by rw [e1, e2]
  linarith

/-! ### The window limit -/

/-- The algebra of the comb part: `P/q₀ ≈ s`, `B ≈ W̃` give `(P/q₀) B ≈ s W̃`. -/
lemma window_product_estimate {P q₀ s W B a S B₀ ε₁ : ℝ} (hq₀ : 0 < q₀) (hP : |P - q₀ * s| ≤ a * q₀ * |s|)
    (hs : |s| ≤ S) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hW : |W| ≤ B₀) (hB : |B - W| ≤ ε₁) :
    |P / q₀ * B - s * W| ≤ 2 * S * ε₁ + a * S * B₀ := by
  have hS0 : 0 ≤ S := (abs_nonneg _).trans hs
  have hε₁ : 0 ≤ ε₁ := (abs_nonneg _).trans hB
  have h1 : |P / q₀ - s| ≤ a * |s| := by
    have : P / q₀ - s = (P - q₀ * s) / q₀ := by field_simp
    rw [this, abs_div, abs_of_pos hq₀, div_le_iff₀ hq₀]
    linarith
  have h2 : |P / q₀| ≤ 2 * S := by
    have : |P / q₀| ≤ |s| + |P / q₀ - s| := by
      calc |P / q₀| = |s + (P / q₀ - s)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    nlinarith [abs_nonneg s]
  have e : P / q₀ * B - s * W = (P / q₀) * (B - W) + (P / q₀ - s) * W := by ring
  rw [e]
  calc |(P / q₀) * (B - W) + (P / q₀ - s) * W| ≤ |(P / q₀) * (B - W)| + |(P / q₀ - s) * W| := abs_add_le _ _
    _ = |P / q₀| * |B - W| + |P / q₀ - s| * |W| := by rw [abs_mul, abs_mul]
    _ ≤ 2 * S * ε₁ + a * S * B₀ := by
        refine add_le_add (mul_le_mul h2 hB (abs_nonneg _) (by positivity)) ?_
        calc |P / q₀ - s| * |W| ≤ (a * S) * B₀ :=
              mul_le_mul ((h1.trans (mul_le_mul_of_nonneg_left hs ha0))) hW (abs_nonneg _) (by positivity)
          _ = a * S * B₀ := rfl

lemma eps_split {T e : ℝ} (hT : 0 ≤ T) (he : 0 < e) : 2 * T * (e / (2 * T + 1)) ≤ e := by
  rw [show 2 * T * (e / (2 * T + 1)) = e * (2 * T / (2 * T + 1)) by ring]
  have : 2 * T / (2 * T + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  nlinarith

lemma small_mul {a T B e : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T) (hB : 0 ≤ B)
    (h : a ≤ e / (T * B + 1)) : a * T * B ≤ e := by
  have h2 : a * (T * B + 1) ≤ e := by rwa [le_div_iff₀ (by positivity)] at h
  nlinarith [mul_nonneg ha (mul_nonneg hT hB)]

/-- The real-variable core of the window limit: the error of `F⁻¹ Ψ` against `(1/(2κ)) s W̃`, with
`F = FK q₀`, `Ψ = ½ (P h₀ - ĥ) V (dt/dσ)/κ`. -/
lemma window_error_bound {κ FK q₀ P mH V Dt ĥ s Wt a S B₀ ε₁ e ε : ℝ} (hκ : 0 < κ) (hFK : 0 < FK)
    (hq₀ : 0 < q₀) (he : e = 2 * κ * ε / 3) (hB : |mH * V * Dt / FK - Wt| ≤ ε₁) (hW : |Wt| ≤ B₀)
    (hs : |s| ≤ S) (hP : |P - q₀ * s| ≤ a * q₀ * |s|) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (h1 : 2 * S * ε₁ ≤ e)
    (h2 : a * S * B₀ ≤ e) (h3 : |ĥ * V * Dt| ≤ e * (FK * q₀)) :
    |(FK * q₀)⁻¹ * (((P * mH - ĥ) / 2) * V * (Dt / κ)) - (1 / (2 * κ)) * (s * Wt)| ≤ ε := by
  have hexpr : (FK * q₀)⁻¹ * (((P * mH - ĥ) / 2) * V * (Dt / κ)) - (1 / (2 * κ)) * (s * Wt) =
      (1 / (2 * κ)) * ((P / q₀ * (mH * V * Dt / FK) - s * Wt) - (ĥ * V * Dt) / (FK * q₀)) := by
    field_simp
    ring
  rw [hexpr, abs_mul, abs_of_pos (by positivity : 0 < 1 / (2 * κ))]
  have hcomb := window_product_estimate hq₀ hP hs ha0 ha1 hW hB
  have hT3 : |(ĥ * V * Dt) / (FK * q₀)| ≤ e := by
    rw [abs_div, abs_of_pos (mul_pos hFK hq₀), div_le_iff₀ (mul_pos hFK hq₀)]
    exact h3
  have hsum : |(P / q₀ * (mH * V * Dt / FK) - s * Wt) - (ĥ * V * Dt) / (FK * q₀)| ≤ 3 * e := by
    calc _ ≤ |P / q₀ * (mH * V * Dt / FK) - s * Wt| + |(ĥ * V * Dt) / (FK * q₀)| := abs_sub _ _
      _ ≤ 3 * e := by linarith
  calc 1 / (2 * κ) * _ ≤ 1 / (2 * κ) * (3 * e) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = ε := by rw [he]; field_simp

/-- **The window limit of `Ψ_g` for the two-zero comb** (`ut:T2`, `eq:ut:T2-local` including the `ĥ` part): for
`prob.w = 1`, every compact family `𝒦` of admissible designs, `R ≥ 0`, `ε > 0`: for `c` large,
`|F_{2,c}^{-1} Ψ_{g_c}(u) - C₂ W₂(u)| ≤ ε` for all `d ∈ 𝒦`, `u ∈ [-R, R]`, with `g_c = twoZeroG d c`,
`F_{2,c} = twoZeroF prob c`, `C₂ = C_* κ/2`. -/
theorem twoZero_window_limit (prob : FixedWeightProblem) (hw : prob.w = 1) {n : ℕ}
    {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) {R : ℝ} (hR : 0 ≤ R)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ c in atTop, ∀ d ∈ 𝒦, ∀ u ∈ Icc (-R) R,
      |(twoZeroF prob c)⁻¹ * psiAiry prob c (twoZeroG d c) u - twoZeroC₂ * d.Wr u| ≤ ε := by
  have hκ := kappaAiry_pos
  have hξ := xiStar_pos
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = R / kappaAiry := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hSdef]; positivity
  have hSκ : S * kappaAiry = R := by rw [hSdef]; field_simp
  obtain ⟨S₁, hS₁0, hS₁⟩ := hK.exists_sigmaP_bound
  obtain ⟨CT, hCT0, hTev⟩ := twoZeroT_window_bound (S + S₁) (by positivity)
  obtain ⟨B₀, hB₀, hBb⟩ := CompactCombFamily.tildeW_bound (toModifiedFamily hK hA) hS0
  obtain ⟨K, hK0, hKev⟩ := twoZero_hat_window_bound prob hw hK hA
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
  have hFc := twoZeroFConst_pos prob
  filter_upwards [hKev, hTev, eventually_ge_atTop C₀, lambda_mul_le M' hδ0, lambda_mul_le S (half_pos hξ),
    eventually_gt_atTop (0 : ℝ),
    Real.tendsto_sqrt_atTop.eventually_ge_atTop (K / (twoZeroFConst prob * e)),
    tendsto_lambdaComb_atTop.eventually_le_const (zero_lt_one : (0 : ℝ) < 1)]
    with c hKc hTc hc₀ hlM hlS hc0 hsq hl1' d hd u hu
  have hlam := lambdaComb_pos' hc0
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = -u / kappaAiry := ⟨_, rfl⟩
  have hσκ : σ * kappaAiry = -u := by rw [hσ]; field_simp
  have hσS : |σ| ≤ S := by
    rw [abs_le]
    constructor
    · by_contra h
      push Not at h
      nlinarith [mul_lt_mul_of_pos_right h hκ, hu.2]
    · by_contra h
      push Not at h
      nlinarith [mul_lt_mul_of_pos_right h hκ, hu.1]
  have hσI : σ ∈ Icc (-S) (phiWKB (n1 + 1)) := ⟨(abs_le.1 hσS).1, (abs_le.1 hσS).2.trans hn1⟩
  have hσI' : σ ∈ Icc (-S) S := ⟨(abs_le.1 hσS).1, (abs_le.1 hσS).2⟩
  have hx : xiStar / 2 ≤ xiStar + lambdaComb c * σ := by
    have := mul_le_mul_of_nonneg_left (abs_le.1 hσS).1 hlam.le
    nlinarith
  have hx0 : 0 ≤ xiStar + lambdaComb c * σ := by linarith
  have hWu : -kappaAiry * σ = u := by rw [hσ]; field_simp
  have hFKpos : 0 < windowMeasureNormK prob 2 c := by
    rw [windowMeasureNormK_eq_FKc prob 2 hc0]
    exact FKc_pos (qProb_pos prob) 2 hc0
  have hq₀pos : 0 < π * lambdaComb c / (2 * √2) := by positivity
  have hF : twoZeroF prob c = windowMeasureNormK prob 2 c * (π * lambdaComb c / (2 * √2)) :=
    twoZeroF_eq_windowMeasureNormK prob hw hc0
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
  have hl1 : M' * lambdaComb c ≤ δ := by rw [mul_comm]; exact hlM
  have ha0 : 0 ≤ M' * lambdaComb c := by positivity
  have ha1 : M' * lambdaComb c ≤ 1 := hl1.trans (by rw [hδ]; exact min_le_left _ _)
  -- the transform part
  have hHh := hKc d hd _ hx
  have hHh' : |hankelTransform 1 (combProfile c (d.twoZeroComb c)) (c * (xiStar + lambdaComb c * σ) ^ 2 / 3) *
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
  have hpsi : psiAiry prob c (twoZeroG d c) u =
      ((tFac (d.chiP c) (xiStar + lambdaComb c * σ) *
            modifiedH0 2 (n + 2) d.toModified c (xiStar + lambdaComb c * σ) -
          hankelTransform 1 (combProfile c (d.twoZeroComb c)) (c * (xiStar + lambdaComb c * σ) ^ 2 / 3)) / 2) *
        prob.cardyV (c / 12) (c * (xiStar + lambdaComb c * σ) ^ 2 / 3) *
        (((2 * c * (xiStar + lambdaComb c * σ) / 3) * lambdaComb c) / kappaAiry) := by
    unfold twoZeroG
    rw [psiAiry_pairOdd_eq prob hc0 _ _ (u := u) (by rw [← hσ]; exact hx0), ← hσ,
      twoZero_combProfile_eq d hc0 hx0]
  rw [hpsi, hC, hF]
  have h1 : 2 * (S + S₁) * ε₁ ≤ e := by
    rw [hε₁]; exact eps_split (by positivity) he0
  have h2 : (M' * lambdaComb c) * (S + S₁) * B₀ ≤ e :=
    small_mul ha0 (by positivity) hB₀.le (hl1.trans (by rw [hδ]; exact min_le_right _ _))
  exact window_error_bound hκ hFKpos hq₀pos he hB hWtb hsb hPb ha0 ha1 h1 h2 hHh'

/-- The `window` field of `TwoZeroTransferData` for `F = twoZeroF prob`, `g = twoZeroG`, `C₂ = twoZeroC₂`
(same quantifiers and form as the field; `psiAiry` is `Upper.Rigidity.psiAiry`). -/
theorem twoZero_window_field (prob : FixedWeightProblem) (hw : prob.w = 1) {n : ℕ}
    {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∀ R : ℝ, 0 ≤ R → ∀ ε : ℝ, 0 < ε → ∀ᶠ c : ℝ in atTop, ∀ d ∈ 𝒦, ∀ u ∈ Icc (-R) R,
      |(twoZeroF prob c)⁻¹ * psiAiry prob c (twoZeroG d c) u - twoZeroC₂ * d.Wr u| ≤ ε :=
  fun _ hR _ hε => twoZero_window_limit prob hw hK hA hR hε

/-- The `F_asymp` field of `TwoZeroTransferData` for `F = twoZeroF prob`, any threshold `c₀ > 0`. -/
theorem twoZeroF_asymp_field (prob : FixedWeightProblem) {c₀ : ℝ} (hc₀ : 0 < c₀) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ c : ℝ, c₀ ≤ c →
      A * c ^ ((3 : ℝ) / 2) ≤ twoZeroF prob c ∧ twoZeroF prob c ≤ B * c ^ ((3 : ℝ) / 2) := by
  obtain ⟨A, B, hA, hB, h⟩ := twoZeroF_asymp prob
  exact ⟨A, B, hA, hB, fun c hc => h c (hc₀.trans_le hc)⟩

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZero_hat_window_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZero_hat_window_bound

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZero_window_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZero_window_limit

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZero_window_field' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZero_window_field

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZeroF_asymp_field' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZeroF_asymp_field

end FormalResearch.ModularBootstrap.TwoLevel
