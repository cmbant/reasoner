module

public import FormalResearch.ModularBootstrap.Mixtures.VacCompare

/-!
# `pmix:vac`, window part: the first limit of `pmix:fixed-transfer` for `f = 1`

`positive_mixtures.tex`, Proposition PM.9 (`pmix:vac`), "(F^{mix})^{-1} Ψ^{mix}_{g_w} → C W locally uniformly", `(f, r) = (1, 0)`.

For a `CommonSource` `C`, the bumped `f = 1` designs of W-P5 (the comb `bumpSigComb d c' N N' η σs` and the test `bumpG`) depend on the
problem only through the weight `w`, so they are taken at the trivial product `C.src.triv` (`Q ≡ 1`).  By the comparison
`cmp_window` (`V_s = A(ξ_*) V_t (1 + O(c'^{-2/3}))` on compact windows) the two window limits of W-P5 at `triv` transfer to `V_s` with the
normalisation `FK^{mix} = A(ξ_*) FK^{(w,1)}`:

* `ratio_aux`: the elementary comparison `|(k/A) y V_s - k y V_t| ≤ (δ/A) |k y V_t|` from `|V_s - A V_t| ≤ δ V_t`;
* `bump_part1_src`: the comb part, `|h^{(p)} V_s (dt/dσ)/FK^{mix} - C_* κ W(-κσ)| ≤ ε'` (uniform in the cut `N'`);
* **`bump_psi_uniform_src`** (`pmix:fixed-transfer`, first limit): `|(2/(C_* FK^{mix})) Ψ^{mix}_{g_w}(u) - W(u)| ≤ ε` on `[-R, R]`.

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
  FormalResearch.Special

/-- The comparison step: if `|V_s - A V_t| ≤ δ V_t` (`A, V_t > 0`) and `k ≥ 0`, then
`|(k/A) y V_s - k y V_t| ≤ (δ/A) |k y V_t|`. -/
lemma ratio_aux {A Vs Vt k y δ : ℝ} (hA : 0 < A) (hVt : 0 < Vt) (hk : 0 ≤ k)
    (h : |Vs - A * Vt| ≤ δ * Vt) :
    |k / A * y * Vs - k * y * Vt| ≤ δ / A * |k * y * Vt| := by
  have e : k / A * y * Vs - k * y * Vt = k / A * y * (Vs - A * Vt) := by
    field_simp
  rw [e, abs_mul, abs_mul, abs_of_nonneg (div_nonneg hk hA.le)]
  have h1 : |y| * |Vs - A * Vt| ≤ |y| * (δ * Vt) := mul_le_mul_of_nonneg_left h (abs_nonneg _)
  have h2 : |k * y * Vt| = k * |y| * Vt := by
    rw [abs_mul, abs_mul, abs_of_nonneg hk, abs_of_pos hVt]
  rw [h2]
  calc k / A * |y| * |Vs - A * Vt| = k / A * (|y| * |Vs - A * Vt|) := by ring
    _ ≤ k / A * (|y| * (δ * Vt)) :=
        mul_le_mul_of_nonneg_left h1 (div_nonneg hk hA.le)
    _ = δ / A * (k * |y| * Vt) := by ring

/-- **The comb window for the source** (`bump_part1` at `triv`, transferred by `cmp_window`), uniform in the cut `N'`. -/
theorem bump_part1_src (C : CommonSource) (d : BumpData) (N : ℕ) (hN : 1 ≤ N) {η : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) (σs : ℕ → ℝ) {S : ℝ} (hS : 0 ≤ S) (n1 : ℕ) {ε' : ℝ} (hε' : 0 < ε') :
    ∀ᶠ c in atTop, ∀ N' : ℕ, N ≤ N' → ∀ σ ∈ Icc (-S) (phiWKB (n1 + 1)),
      |combProfile c (bumpSigComb d c N N' η σs) (c * (xiStar + lambdaComb c * σ) ^ 2 / 3) *
          C.src.cardyV (c / 12) (c * (xiStar + lambdaComb c * σ) ^ 2 / 3) *
          ((2 * c * (xiStar + lambdaComb c * σ) / 3) * lambdaComb c) / FKc C.src.qMix 1 c -
        CStar * kappaAiry * sigWinW N η σs (-kappaAiry * σ)| ≤ ε' := by
  have hAs := C.ampl_pos xiStar_pos
  set As : ℝ := C.src.ampl xiStar with hAsdef
  have hcw : Continuous fun σ : ℝ => CStar * kappaAiry * sigWinW N η σs (-kappaAiry * σ) := by
    unfold sigWinW
    exact continuous_const.mul ((continuous_sigWindowRe hN η σs).comp (by fun_prop))
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc (a := -S) (b := phiWKB (n1 + 1))).exists_bound_of_continuousOn
    hcw.continuousOn
  set M : ℝ := max M₀ 0 with hM
  have hΦ0 : 0 ≤ phiWKB (n1 + 1) := phiWKB_nonneg (by omega)
  have hMe : 0 < M + ε' / 2 := by positivity
  set δ : ℝ := As * (ε' / 2) / (M + ε' / 2) with hδdef
  have hδ : 0 < δ := by positivity
  have hδM : δ / As * (M + ε' / 2) ≤ ε' / 2 := by
    have : δ / As = (ε' / 2) / (M + ε' / 2) := by rw [hδdef]; field_simp
    rw [this, div_mul_cancel₀ _ hMe.ne']
  filter_upwards [bump_part1 C.src.triv d N hN hη0 hη1 σs hS n1 (half_pos hε'),
    cmp_window C (max S (phiWKB (n1 + 1))) hδ, eventually_gt_atTop (0 : ℝ),
    lambda_mul_le S (half_pos xiStar_pos)] with c h1 hcmp hc0 hlS N' hNN' σ hσ
  have hσ' : σ ∈ Icc (-(max S (phiWKB (n1 + 1)))) (max S (phiWKB (n1 + 1))) :=
    ⟨by linarith [hσ.1, le_max_left S (phiWKB (n1 + 1))], by linarith [hσ.2, le_max_right S (phiWKB (n1 + 1))]⟩
  obtain ⟨hVt, hVs⟩ := hcmp σ hσ'
  have hP := h1 N' hNN' σ hσ
  have hlam := lambdaComb_pos' hc0
  have hx : 0 ≤ xiStar + lambdaComb c * σ := by
    have h1 := mul_le_mul_of_nonneg_left hσ.1 hlam.le
    have h2 : lambdaComb c * (-S) = -(lambdaComb c * S) := mul_neg _ _
    linarith [xiStar_pos, hlS]
  have hFKt := FKc_pos (qProb_pos C.src.triv) 1 hc0
  have hD : 0 ≤ (2 * c * (xiStar + lambdaComb c * σ) / 3) * lambdaComb c := by positivity
  set h : ℝ := combProfile c (bumpSigComb d c N N' η σs) (c * (xiStar + lambdaComb c * σ) ^ 2 / 3)
  set Vs := C.src.cardyV (c / 12) (c * (xiStar + lambdaComb c * σ) ^ 2 / 3)
  set Vt := C.src.triv.cardyV (c / 12) (c * (xiStar + lambdaComb c * σ) ^ 2 / 3)
  set D : ℝ := (2 * c * (xiStar + lambdaComb c * σ) / 3) * lambdaComb c
  set FKt : ℝ := FKc (qProb C.src.triv) 1 c
  set w0 : ℝ := CStar * kappaAiry * sigWinW N η σs (-kappaAiry * σ)
  have hw0 : |w0| ≤ M := by
    have := hM₀ σ ⟨hσ.1, hσ.2⟩
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  have hP' : |h * Vt * D / FKt - w0| ≤ ε' / 2 := hP
  have hQ := ratio_aux (A := As) (Vs := Vs) (Vt := Vt) (k := D / FKt) (y := h) (δ := δ) hAs hVt
    (div_nonneg hD hFKt.le) hVs
  have hPabs : |D / FKt * h * Vt| ≤ M + ε' / 2 := by
    have e : D / FKt * h * Vt = h * Vt * D / FKt := by ring
    rw [e]
    have := abs_sub_abs_le_abs_sub (h * Vt * D / FKt) w0
    linarith
  have hQP : |D / FKt / As * h * Vs - D / FKt * h * Vt| ≤ ε' / 2 := by
    refine hQ.trans ?_
    have e2 : |D / FKt * h * Vt| = |D / FKt * h * Vt| := rfl
    calc δ / As * |D / FKt * h * Vt| ≤ δ / As * (M + ε' / 2) :=
          mul_le_mul_of_nonneg_left hPabs (div_nonneg hδ.le hAs.le)
      _ ≤ ε' / 2 := hδM
  have hFKs : FKc C.src.qMix 1 c = As * FKt := FKc_qMix C.src c
  have e : h * Vs * D / FKc C.src.qMix 1 c = D / FKt / As * h * Vs := by
    rw [hFKs]; field_simp
  rw [e]
  have e3 : D / FKt * h * Vt = h * Vt * D / FKt := by ring
  calc |D / FKt / As * h * Vs - w0|
      = |(D / FKt / As * h * Vs - D / FKt * h * Vt) + (h * Vt * D / FKt - w0)| := by rw [← e3]; ring_nf
    _ ≤ |D / FKt / As * h * Vs - D / FKt * h * Vt| + |h * Vt * D / FKt - w0| := abs_add_le _ _
    _ ≤ ε' := by linarith

/-- **`pmix:fixed-transfer`, first limit, `(f, r) = (1, 0)`** (`bump_psi_uniform` at `triv`, transferred by `cmp_window`): for every
`R ≥ 0`, `ε > 0` and large `c`, `|(2/(C_* FK^{mix}_c)) Ψ^{mix}_{g_w}(u) - W(u)| ≤ ε` on `[-R, R]`, with `g_w = bumpG triv d N η σs c`
and the Airy window `W = sigWinW N η σs` of the `f = 1` modification (first site anywhere, the family `𝓕_1`). -/
theorem bump_psi_uniform_src (C : CommonSource) (d : BumpData) (N : ℕ) (hN : 1 ≤ N) {η : ℝ}
    (hη0 : 0 < η) (hη1 : η ≤ 1 / 4) (σs : ℕ → ℝ) {R : ℝ} (hR : 0 ≤ R) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ c in atTop, ∀ u ∈ Icc (-R) R,
      |psiScaleSrc C.src c * psiAirySrc C.src c (bumpG C.src.triv d N η σs c) u - sigWinW N η σs u| ≤ ε := by
  have hAs := C.ampl_pos xiStar_pos
  have hκ := kappaAiry_pos
  set As : ℝ := C.src.ampl xiStar with hAsdef
  have hcw : Continuous (sigWinW N η σs) := by
    unfold sigWinW
    exact continuous_sigWindowRe hN η σs
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn hcw.continuousOn
  set M : ℝ := max M₀ 0 with hM
  have hMe : 0 < M + ε / 2 := by positivity
  set δ : ℝ := As * (ε / 2) / (M + ε / 2) with hδdef
  have hδ : 0 < δ := by positivity
  have hδM : δ / As * (M + ε / 2) ≤ ε / 2 := by
    have : δ / As = (ε / 2) / (M + ε / 2) := by rw [hδdef]; field_simp
    rw [this, div_mul_cancel₀ _ hMe.ne']
  have hS0 : 0 ≤ R / kappaAiry := by positivity
  filter_upwards [bump_psi_uniform C.src.triv d N hN hη0 hη1 σs hR (half_pos hε),
    cmp_window C (R / kappaAiry) hδ, eventually_gt_atTop (0 : ℝ),
    lambda_mul_le (R / kappaAiry) (half_pos xiStar_pos)] with c h1 hcmp hc0 hlS u hu
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
  have hFKt := FKc_pos (qProb_pos C.src.triv) 1 hc0
  have hP := h1 u hu
  set t := tAiry c u with htdef
  set g := bumpG C.src.triv d N η σs c
  set Vs := C.src.cardyV (c / 12) t
  set Vt := C.src.triv.cardyV (c / 12) t
  set J := jAiry c t
  set k : ℝ := psiScale C.src.triv c * J with hk
  have hk0 : 0 ≤ k := mul_nonneg (psiScale_pos C.src.triv hc0).le hJ.le
  have hQ := ratio_aux (A := As) (Vs := Vs) (Vt := Vt) (k := k) (y := g t) (δ := δ) hAs hVt' hk0 hVs'
  have e1 : psiScale C.src.triv c * psiAiry C.src.triv c g u = k * g t * Vt := by
    unfold psiAiry; rw [hk]; ring
  have e2 : psiScaleSrc C.src c * psiAirySrc C.src c g u = k / As * g t * Vs := by
    have hs : psiScaleSrc C.src c = psiScale C.src.triv c / As := by
      unfold psiScaleSrc psiScale
      rw [FKc_qMix, ← hAsdef]
      have := CStar_pos
      field_simp
    unfold psiAirySrc; rw [hs, hk]; ring
  rw [e1] at hP
  rw [e2]
  have hW : |sigWinW N η σs u| ≤ M := by
    have := hM₀ u hu
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  have hPabs : |k * g t * Vt| ≤ M + ε / 2 := by
    have := abs_sub_abs_le_abs_sub (k * g t * Vt) (sigWinW N η σs u)
    linarith
  calc |k / As * g t * Vs - sigWinW N η σs u|
      = |(k / As * g t * Vs - k * g t * Vt) + (k * g t * Vt - sigWinW N η σs u)| := by ring_nf
    _ ≤ |k / As * g t * Vs - k * g t * Vt| + |k * g t * Vt - sigWinW N η σs u| := abs_add_le _ _
    _ ≤ ε / 2 + ε / 2 := by
        refine add_le_add ?_ hP
        refine hQ.trans ?_
        calc δ / As * |k * g t * Vt| ≤ δ / As * (M + ε / 2) :=
              mul_le_mul_of_nonneg_left hPabs (div_nonneg hδ.le hAs.le)
          _ ≤ ε / 2 := hδM
    _ = ε := by ring

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.bump_part1_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bump_part1_src

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.bump_psi_uniform_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bump_psi_uniform_src

end FormalResearch.ModularBootstrap.Mixtures
