module

public import FormalResearch.ModularBootstrap.Mixtures.VacWindow
public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroTransferW

/-!
# `pmix:vac` for `(f, r) = (2, 1)`: the window part (`ut:T2` for a common source)

`positive_mixtures.tex`, Proposition PM.9 (`pmix:vac`) at `(f, r) = (2, 1)` (`γ = 5/2`, `n_eff = 5/4`, the two-simple-zero designs of
`ut:T2`, the family `𝓕_2` of `ut:ideal`).  The bumped two-zero comb `h₂^{(p)}` and the test `twoZeroBumpG` depend on the problem only through
the weight, so they are taken at the trivial product `triv`, exactly as for `f = 1` (`VacWindow`).

* `twoZeroFSrc`: the normalisation `F^{mix}_{2,c} = FKc (𝔮_mix) 2 c · πλ/(2√2) = A(ξ_*) F_{2,c}^{(w,1)}`;
* `twoZero_Wr_bound`: `C_* κ² |W_2(u)|` is bounded uniformly on a compact family of designs and `u ∈ [-R, R]`;
* `twoZeroBump_window_comb_src`: the comb window `|(F^{mix})^{-1} h₂^{(p)} V_s (dt/dσ) - C_* κ² W_2(-κσ)| ≤ ε`;
* **`twoZeroBump_window_limit_src`** (first limit of `pmix:fixed-transfer`): `|(F^{mix}_{2,c})^{-1} Ψ^{mix}_g(u) - C₂ W_2(u)| ≤ ε` on `[-R, R]`,
  uniformly on the compact family `𝒦` and in the cut.

All results are proved unconditionally.
-/

@[expose] public section

namespace FormalResearch.ModularBootstrap.Mixtures

open Real Filter Topology Set MeasureTheory
open scoped Real
open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.FixedWeight FormalResearch.ModularBootstrap.Upper.Window.Cardy
  FormalResearch.ModularBootstrap.Upper.Comb FormalResearch.ModularBootstrap.Upper.Rigidity
  FormalResearch.ModularBootstrap.Upper.Window FormalResearch.ModularBootstrap.Upper.Positivity
  FormalResearch.ModularBootstrap.Upper.Assembly FormalResearch.ModularBootstrap.Upper.Bump
  FormalResearch.ModularBootstrap.Upper.Design FormalResearch.ModularBootstrap.Upper.Membership
  FormalResearch.ModularBootstrap.TwoLevel FormalResearch.Special
open TwoZeroDesign

/-- `F^{mix}_{2,c} = FKc (𝔮_mix) 2 c · πλ/(2√2)`. -/
noncomputable def twoZeroFSrc (src : ShiftSource) (c : ℝ) : ℝ :=
  FKc src.qMix 2 c * (π * lambdaComb c / (2 * √2))

lemma twoZeroFSrc_eq (src : ShiftSource) (c : ℝ) :
    twoZeroFSrc src c = src.ampl xiStar * twoZeroF src.triv c := by
  unfold twoZeroFSrc twoZeroF
  rw [src.qMix_eq, FKc_scale, FKc_scale (qProb src.triv)]
  ring

lemma twoZeroFSrc_pos (C : CommonSource) {c : ℝ} (hc : 0 < c) : 0 < twoZeroFSrc C.src c := by
  rw [twoZeroFSrc_eq]
  exact mul_pos (C.ampl_pos xiStar_pos) (twoZeroF_pos _ hc)

/-- **Uniform bound of the window function**: `|C_* κ² W_2(u)| ≤ M` for `d ∈ 𝒦`, `|u| ≤ R`. -/
lemma twoZero_Wr_bound {n : ℕ} {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm)
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ d ∈ 𝒦, ∀ u ∈ Icc (-R) R, |CStar * kappaAiry ^ 2 * d.Wr u| ≤ M := by
  have hκ := kappaAiry_pos
  have hS : 0 ≤ R / kappaAiry := by positivity
  obtain ⟨S₁, hS₁0, hS₁⟩ := hK.exists_sigmaP_bound
  obtain ⟨B₀, hB₀, hBb⟩ := CompactCombFamily.tildeW_bound (toModifiedFamily hK hA) hS
  refine ⟨B₀ * (R / kappaAiry + S₁), by positivity, fun d hd u hu => ?_⟩
  have hσ : -u / kappaAiry ∈ Icc (-(R / kappaAiry)) (R / kappaAiry) := by
    constructor
    · have e : -(R / kappaAiry) = -R / kappaAiry := by ring
      rw [e]
      exact div_le_div_of_nonneg_right (by linarith [hu.2]) hκ.le
    · exact div_le_div_of_nonneg_right (by linarith [hu.1]) hκ.le
  have hID := tildeW_toModified_Wr d (-u / kappaAiry)
  have hu' : -kappaAiry * (-u / kappaAiry) = u := by field_simp
  rw [hu'] at hID
  rw [← hID, abs_mul]
  have h1 := hBb d.toModified (toModifiedFamily_mem hK hA hd) (-u / kappaAiry) hσ
  have h2 : |(-u / kappaAiry) - (-d.p / kappaAiry)| ≤ R / kappaAiry + S₁ := by
    have hs := hS₁ d hd
    have e : (-d.p / kappaAiry) = d.sigmaP := rfl
    rw [e]
    refine (abs_sub _ _).trans (add_le_add ?_ hs)
    rw [abs_le]
    exact ⟨hσ.1, hσ.2⟩
  exact mul_le_mul h1 h2 (abs_nonneg _) hB₀.le

/-- **The comb window for the source, `(f, r) = (2, 1)`** (`twoZeroBump_window_comb` at `triv`, transferred by `cmp_window`). -/
theorem twoZeroBump_window_comb_src (C : CommonSource) (bd : BumpData) {n : ℕ}
    {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) {S : ℝ} (hS : 0 ≤ S)
    (n1 : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ c in atTop, ∀ d ∈ 𝒦, ∀ N' : ℕ, n + 2 ≤ N' → ∀ σ ∈ Icc (-S) (phiWKB (n1 + 1)),
      |(twoZeroFSrc C.src c)⁻¹ * (combProfile c (d.bumpComb bd c N') (c * (xiStar + lambdaComb c * σ) ^ 2 / 3) *
          C.src.cardyV (c / 12) (c * (xiStar + lambdaComb c * σ) ^ 2 / 3) *
          ((2 * c * (xiStar + lambdaComb c * σ) / 3) * lambdaComb c)) -
        CStar * kappaAiry ^ 2 * d.Wr (-kappaAiry * σ)| ≤ ε := by
  have hκ := kappaAiry_pos
  have hAs := C.ampl_pos xiStar_pos
  set As : ℝ := C.src.ampl xiStar with hAsdef
  have hΦ0 : 0 ≤ phiWKB (n1 + 1) := phiWKB_nonneg (by omega)
  set S' : ℝ := max S (phiWKB (n1 + 1)) with hS'
  have hS'0 : 0 ≤ S' := le_max_of_le_left hS
  obtain ⟨M₀, hM₀0, hM₀⟩ := twoZero_Wr_bound hK hA (R := kappaAiry * S') (by positivity)
  set M : ℝ := M₀ with hM
  have hMe : 0 < M + ε / 2 := by positivity
  set δ : ℝ := As * (ε / 2) / (M + ε / 2) with hδdef
  have hδ : 0 < δ := by positivity
  have hδM : δ / As * (M + ε / 2) ≤ ε / 2 := by
    have : δ / As = (ε / 2) / (M + ε / 2) := by rw [hδdef]; field_simp
    rw [this, div_mul_cancel₀ _ hMe.ne']
  filter_upwards [twoZeroBump_window_comb C.src.triv bd hK hA hS n1 (half_pos hε),
    cmp_window C S' hδ, eventually_gt_atTop (0 : ℝ), lambda_mul_le S (half_pos xiStar_pos)]
    with c h1 hcmp hc0 hlS d hd N' hN' σ hσ
  have hσ' : σ ∈ Icc (-S') S' :=
    ⟨by linarith [hσ.1, le_max_left S (phiWKB (n1 + 1))], by linarith [hσ.2, le_max_right S (phiWKB (n1 + 1))]⟩
  obtain ⟨hVt, hVs⟩ := hcmp σ hσ'
  have hP := h1 d hd N' hN' σ hσ
  have hlam := lambdaComb_pos' hc0
  have hx : 0 ≤ xiStar + lambdaComb c * σ := by
    have h1 := mul_le_mul_of_nonneg_left hσ.1 hlam.le
    have h2 : lambdaComb c * (-S) = -(lambdaComb c * S) := mul_neg _ _
    linarith [xiStar_pos, hlS]
  have hFt := twoZeroF_pos C.src.triv hc0
  have hD : 0 ≤ (2 * c * (xiStar + lambdaComb c * σ) / 3) * lambdaComb c := by positivity
  set h : ℝ := combProfile c (d.bumpComb bd c N') (c * (xiStar + lambdaComb c * σ) ^ 2 / 3)
  set Vs := C.src.cardyV (c / 12) (c * (xiStar + lambdaComb c * σ) ^ 2 / 3)
  set Vt := C.src.triv.cardyV (c / 12) (c * (xiStar + lambdaComb c * σ) ^ 2 / 3)
  set D : ℝ := (2 * c * (xiStar + lambdaComb c * σ) / 3) * lambdaComb c
  set Ft : ℝ := twoZeroF C.src.triv c
  set w0 : ℝ := CStar * kappaAiry ^ 2 * d.Wr (-kappaAiry * σ)
  have hw0 : |w0| ≤ M := by
    refine hM₀ d hd (-kappaAiry * σ) ⟨?_, ?_⟩
    · have := hσ'.2; nlinarith only [this, hκ]
    · have := hσ'.1; nlinarith only [this, hκ]
  have hP' : |Ft⁻¹ * (h * Vt * D) - w0| ≤ ε / 2 := hP
  have hQ := ratio_aux (A := As) (Vs := Vs) (Vt := Vt) (k := Ft⁻¹ * D) (y := h) (δ := δ) hAs hVt
    (mul_nonneg (inv_nonneg.2 hFt.le) hD) hVs
  have hPe : Ft⁻¹ * D * h * Vt = Ft⁻¹ * (h * Vt * D) := by ring
  have hPabs : |Ft⁻¹ * D * h * Vt| ≤ M + ε / 2 := by
    rw [hPe]
    have := abs_sub_abs_le_abs_sub (Ft⁻¹ * (h * Vt * D)) w0
    linarith
  have hQP : |Ft⁻¹ * D / As * h * Vs - Ft⁻¹ * D * h * Vt| ≤ ε / 2 := by
    refine hQ.trans ?_
    calc δ / As * |Ft⁻¹ * D * h * Vt| ≤ δ / As * (M + ε / 2) :=
          mul_le_mul_of_nonneg_left hPabs (div_nonneg hδ.le hAs.le)
      _ ≤ ε / 2 := hδM
  have hFs : twoZeroFSrc C.src c = As * Ft := twoZeroFSrc_eq C.src c
  have e : (twoZeroFSrc C.src c)⁻¹ * (h * Vs * D) = Ft⁻¹ * D / As * h * Vs := by
    rw [hFs]; field_simp
  rw [e]
  calc |Ft⁻¹ * D / As * h * Vs - w0|
      = |(Ft⁻¹ * D / As * h * Vs - Ft⁻¹ * D * h * Vt) + (Ft⁻¹ * (h * Vt * D) - w0)| := by
        rw [← hPe]; ring_nf
    _ ≤ |Ft⁻¹ * D / As * h * Vs - Ft⁻¹ * D * h * Vt| + |Ft⁻¹ * (h * Vt * D) - w0| := abs_add_le _ _
    _ ≤ ε := by linarith

/-- **`pmix:fixed-transfer`, first limit, `(f, r) = (2, 1)`** (`twoZeroBump_window_limit` at `triv`, transferred by `cmp_window`):
for `R ≥ 0`, `ε > 0` and large `c`, `|(F^{mix}_{2,c})^{-1} Ψ^{mix}_g(u) - C₂ W₂(u)| ≤ ε` on `[-R, R]`, uniformly for `d ∈ 𝒦` and every cut. -/
theorem twoZeroBump_window_limit_src (C : CommonSource) (bd : BumpData) {n : ℕ}
    {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) {R : ℝ} (hR : 0 ≤ R)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ c in atTop, ∀ d ∈ 𝒦, ∀ N' : ℕ, n + 2 ≤ N' → ∀ u ∈ Icc (-R) R,
      |(twoZeroFSrc C.src c)⁻¹ * psiAirySrc C.src c (twoZeroBumpGN C.src.triv bd d c N') u -
        twoZeroC₂ * d.Wr u| ≤ ε := by
  have hAs := C.ampl_pos xiStar_pos
  have hκ := kappaAiry_pos
  set As : ℝ := C.src.ampl xiStar with hAsdef
  obtain ⟨M₀, hM₀0, hM₀⟩ := twoZero_Wr_bound hK hA hR
  set M : ℝ := M₀ / (2 * kappaAiry) with hM
  have hM0 : 0 ≤ M := by positivity
  have hMe : 0 < M + ε / 2 := by positivity
  set δ : ℝ := As * (ε / 2) / (M + ε / 2) with hδdef
  have hδ : 0 < δ := by positivity
  have hδM : δ / As * (M + ε / 2) ≤ ε / 2 := by
    have : δ / As = (ε / 2) / (M + ε / 2) := by rw [hδdef]; field_simp
    rw [this, div_mul_cancel₀ _ hMe.ne']
  filter_upwards [twoZeroBump_window_limit C.src.triv bd hK hA hR (half_pos hε),
    cmp_window C (R / kappaAiry) hδ, eventually_gt_atTop (0 : ℝ),
    lambda_mul_le (R / kappaAiry) (half_pos xiStar_pos)] with c h1 hcmp hc0 hlS d hd N' hN' u hu
  have hlam := lambdaComb_pos' hc0
  have hσ : -u / kappaAiry ∈ Icc (-(R / kappaAiry)) (R / kappaAiry) := by
    constructor
    · have e : -(R / kappaAiry) = -R / kappaAiry := by ring
      rw [e]
      exact div_le_div_of_nonneg_right (by linarith [hu.2]) hκ.le
    · exact div_le_div_of_nonneg_right (by linarith [hu.1]) hκ.le
  have hx : 0 ≤ xiStar + lambdaComb c * (-u / kappaAiry) := by
    have h1 := mul_le_mul_of_nonneg_left hσ.1 hlam.le
    have h2 : lambdaComb c * (-(R / kappaAiry)) = -(lambdaComb c * (R / kappaAiry)) := mul_neg _ _
    linarith [xiStar_pos]
  have hx' : xiStar / 2 ≤ xiStar + lambdaComb c * (-u / kappaAiry) := by
    have h1 := mul_le_mul_of_nonneg_left hσ.1 hlam.le
    have h2 : lambdaComb c * (-(R / kappaAiry)) = -(lambdaComb c * (R / kappaAiry)) := mul_neg _ _
    linarith [xiStar_pos]
  have ht := tAiry_eq hc0 hx
  obtain ⟨hVt, hVs⟩ := hcmp _ hσ
  have hVs' : |C.src.cardyV (c / 12) (tAiry c u) -
      As * C.src.triv.cardyV (c / 12) (tAiry c u)| ≤ δ * C.src.triv.cardyV (c / 12) (tAiry c u) := by
    rw [ht]; exact hVs
  have hVt' : 0 < C.src.triv.cardyV (c / 12) (tAiry c u) := by rw [ht]; exact hVt
  have htpos : 0 < tAiry c u := by
    rw [ht]; have : 0 < xiStar + lambdaComb c * (-u / kappaAiry) := by linarith [xiStar_pos]
    positivity
  have hJ := jAiry_pos hc0 htpos
  have hFt := twoZeroF_pos C.src.triv hc0
  have hP := h1 d hd N' hN' u hu
  set t := tAiry c u with htdef
  set g := twoZeroBumpGN C.src.triv bd d c N'
  set Vs := C.src.cardyV (c / 12) t
  set Vt := C.src.triv.cardyV (c / 12) t
  set J := jAiry c t
  set Ft : ℝ := twoZeroF C.src.triv c
  set k : ℝ := Ft⁻¹ * J with hk
  have hk0 : 0 ≤ k := mul_nonneg (inv_nonneg.2 hFt.le) hJ.le
  have hQ := ratio_aux (A := As) (Vs := Vs) (Vt := Vt) (k := k) (y := g t) (δ := δ) hAs hVt' hk0 hVs'
  have e1 : Ft⁻¹ * psiAiry C.src.triv c g u = k * g t * Vt := by
    unfold psiAiry; rw [hk]; ring
  have e2 : (twoZeroFSrc C.src c)⁻¹ * psiAirySrc C.src c g u = k / As * g t * Vs := by
    have hs : twoZeroFSrc C.src c = As * Ft := twoZeroFSrc_eq C.src c
    unfold psiAirySrc; rw [hs, hk]
    show (As * Ft)⁻¹ * (g t * Vs * J) = Ft⁻¹ * J / As * g t * Vs
    field_simp
  rw [e1] at hP
  rw [e2]
  have hW : |twoZeroC₂ * d.Wr u| ≤ M := by
    have h2 := hM₀ d hd u hu
    have e : twoZeroC₂ * d.Wr u = (CStar * kappaAiry ^ 2 * d.Wr u) / (2 * kappaAiry) := by
      unfold twoZeroC₂; field_simp
    rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * kappaAiry), hM]
    exact div_le_div_of_nonneg_right h2 (by positivity)
  have hPabs : |k * g t * Vt| ≤ M + ε / 2 := by
    have := abs_sub_abs_le_abs_sub (k * g t * Vt) (twoZeroC₂ * d.Wr u)
    linarith
  calc |k / As * g t * Vs - twoZeroC₂ * d.Wr u|
      = |(k / As * g t * Vs - k * g t * Vt) + (k * g t * Vt - twoZeroC₂ * d.Wr u)| := by ring_nf
    _ ≤ |k / As * g t * Vs - k * g t * Vt| + |k * g t * Vt - twoZeroC₂ * d.Wr u| := abs_add_le _ _
    _ ≤ ε / 2 + ε / 2 := by
        refine add_le_add ?_ hP
        refine hQ.trans ?_
        calc δ / As * |k * g t * Vt| ≤ δ / As * (M + ε / 2) :=
              mul_le_mul_of_nonneg_left hPabs (div_nonneg hδ.le hAs.le)
          _ ≤ ε / 2 := hδM
    _ = ε := by ring

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.twoZeroBump_window_comb_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZeroBump_window_comb_src

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.twoZeroBump_window_limit_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZeroBump_window_limit_src

end FormalResearch.ModularBootstrap.Mixtures
