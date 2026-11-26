module

public import FormalResearch.ModularBootstrap.Upper.Positivity.VacuumBumped
public import FormalResearch.ModularBootstrap.Upper.Assembly.FarFirstSite
public import FormalResearch.ModularBootstrap.FixedWeightBand.BootstrapWInterface

/-!
# Property (P), `Σ₀` and `Σ` at every weight: the bumped designs (`sr:P`, `sr:Sigma0`, `sr:Sigma`, `wone:clark`(a))

Source: `CFT/modular_bootstrap/paper/spectral_rigidity.tex` (Property `sr:P`, (P1)-(P4); Theorems `sr:Sigma0`, `sr:Sigma`),
`upper_transfer.tex` (`ut:T`, `ut:Vac`, `ut:III`, `fw:s1`; Proposition W1.5(a), `wone:clark`).

`Assembly/DesignWindow.lean` proves Property (P) for the designs `D(N, η_*, d)` of a **weight-one** problem
(`designPropertyP_prob`: unbumped combs, `hankelTransform 1`).  This file proves it at **every weight** `w = prob.w` for the
bumped designs, by the same chain with the bump of `rpParams (prob.w - 1)` and the transform `hankelTransform prob.w`
(`g_w = ½(h₀^{(p)} - 𝓗_w h₀^{(p)})`, `bumpG`):

* `bumpCut`, `bumpBc`, `bumpG`: a cut above the block `[ξ_* + 2 r_p, X_p]` for every `c`, the bumped comb and the test;
* `bumpG_good` (P1: test class and decay, from `bumpSig_k7W`), `bumpG_pos` (P2: `g_w > 0` for `t ≥ t_f + 1`, from
  `proposition_III`), `bump_part1` (Lemma `W` + `ID` with `R_bump ∈ [1, 1 + C/c]`), `bump_hat_window_bound` (Lemma `SD_G` at
  order `p = w - 1` against the far Cardy bound of order `p`, `phase_packageP` and `cardyFarBoundP_prob`), `bump_psi_uniform`
  (P3: the window limit of `Ψ_g`), `bump_psi_limsup` (P4: from `proposition_V_i_bumped`);
* `bumpEventual`, `combDesignData_designW`: the comb data `(P1)`-`(P4)`; **`designPropertyP_probW`** (`sr:P`, `designClass`)
  and **`displacedPropertyP_probW`** (`displacedClassX`) for every crossing sequence of every `prob : FixedWeightProblem`;
* **`sigmaZero_unconditional_probW`** (`sr:Sigma0`) and **`sigma_unconditional_probW`** (`sr:Sigma`): for the extremal
  measures `ν_*(c_j)` of every `(w, Q)`, with the threshold lower bound `fixedWeightLowerBoundInput_of_problem`, the same
  window families as at weight one (`designTailBounds`, `displacedFamily`, `farFamily`), and no further hypothesis.

Scope (as at weight one, `PLAN.md` section 5): the extremal measures of `(H_w)` problems; the `f = 1` designs with the
far-first-site omitted family replacing the paper's `f ≥ 2` Step 6; positive `η_*`.  The `w = 1` declarations are the cases
`prob.w = 1` (with a bump present, which is harmless: it is the identity statement `R_bump ≥ 1`).

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Assembly

open FormalResearch.Special FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.Upper.Rigidity FormalResearch.ModularBootstrap.Upper.Comb
  FormalResearch.ModularBootstrap.Upper.Design FormalResearch.ModularBootstrap.Upper.Window
  FormalResearch.ModularBootstrap.Upper.Window.Cardy FormalResearch.ModularBootstrap.Upper.Membership
  FormalResearch.ModularBootstrap.Upper.Positivity FormalResearch.ModularBootstrap.Upper.Bump
  FormalResearch.ModularBootstrap.Upper.Ramped FormalResearch.ModularBootstrap.Upper.Hankel
  FormalResearch.ModularBootstrap.Upper.Holes

open Classical in
/-- A cut `N' ≥ N` above the whole block `[ξ_* + 2 r_p, X_p]` for every `c > 0` (arbitrary, `N` if `c ≤ 0`). -/
noncomputable def bumpCut (d : BumpData) (N : ℕ) (c : ℝ) : ℕ :=
  if h : 0 < c then max N (Classical.choose (exists_cut d h)) else N

lemma le_bumpCut (d : BumpData) (N : ℕ) (c : ℝ) : N ≤ bumpCut d N c := by
  unfold bumpCut
  split_ifs
  · exact le_max_left _ _
  · exact le_rfl

lemma bumpCut_spec (d : BumpData) (N : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ k : ℕ, 1 ≤ k → chiQuantile c (k : ℝ) ≤ d.X → k ≤ bumpCut d N c := by
  intro k hk hkX
  unfold bumpCut
  simp only [hc, ↓reduceDIte]
  exact (Classical.choose_spec (exists_cut d hc) k hk hkX).trans (le_max_right _ _)

/-- The bumped comb `B_D^{(p)}` of the `f = 1` finite modification with offsets `σs` at `c`, with the cut `bumpCut`. -/
noncomputable def bumpBc (d : BumpData) (N : ℕ) (η : ℝ) (σs : ℕ → ℝ) (c : ℝ) : ℂ → ℂ :=
  bumpSigComb d c N (bumpCut d N c) η σs

/-- `g_w = ½ (h₀^{(p)} - ĥ₀^{(p)})` (`pairOdd`) of the bumped modification at `c`, `ĥ₀ = hankelTransform prob.w h₀`. -/
noncomputable def bumpG (prob : FixedWeightProblem) (d : BumpData) (N : ℕ) (η : ℝ) (σs : ℕ → ℝ)
    (c : ℝ) : ℝ → ℝ :=
  pairOdd (combProfile c (bumpBc d N η σs c)) (hankelTransform prob.w (combProfile c (bumpBc d N η σs c)))

/-- Membership in the test class and the exponential decay of `g_w` for the bumped designs (P1). -/
theorem bumpG_good (prob : FixedWeightProblem) (d : BumpData) (N : ℕ) (hN : 1 ≤ N) {η : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) (σs : ℕ → ℝ) :
    ∀ᶠ c in atTop, 0 < c ∧ TestClass prob (c / 12) (bumpG prob d N η σs c) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
        |bumpG prob d N η σs c t| ≤ C * Real.exp (-4 * π * √(c / 12 * t) - π * √(3 * t / c)) := by
  filter_upwards [bumpSig_k7W prob d N hN hη0 hη1 σs, eventually_gt_atTop (0 : ℝ)] with c hk hc
  obtain ⟨C, hC, hd1, hd2, hT, -⟩ := hk (bumpCut d N c) (le_bumpCut d N c)
  refine ⟨hc, hT, C, hC, fun t ht => ?_⟩
  have h := (hd1.pairOdd hd2) t ht
  unfold decayEnv at h
  rw [decay_exponent_eq hc ht] at h
  have e : -(4 * π * √(c / 12 * t)) - π * xOf c t = -4 * π * √(c / 12 * t) - π * √(3 * t / c) := by
    unfold xOf; ring
  rw [e] at h
  exact h

/-- **(P2) positivity of `g_w` for the bumped designs, every weight** (`ut:III`, Proposition III): for `η_* ∈ (0, 1/4]` and
`c` large, `g_w(t) > 0` for every `t ≥ t_f + 1`, with the bump of `rpParams (prob.w - 1)` and a cut above its block. -/
theorem bumpG_pos (prob : FixedWeightProblem) (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 4)
    (σs : ℕ → ℝ) :
    ∀ᶠ c in atTop, ∀ t : ℝ, sigTf σs c + 1 ≤ t →
      0 < bumpG prob (rpParams (prob.w - 1)).bumpData N η σs c t := by
  filter_upwards [proposition_III prob N hN hη0 hη1 σs,
    bumpSig_k7W prob (rpParams (prob.w - 1)).bumpData N hN hη0.le hη1 σs,
    bumpSig_phaseHyp (rpParams (prob.w - 1)).bumpData N hN hη0.le hη1 σs,
    designComb_innerCombHyp_of_admissible 1 le_rfl (η₀ := 1 / 4) (by norm_num) (by norm_num),
    eventually_gt_atTop (0 : ℝ)] with c hIII hk7 hph hin hc t ht
  set d := (rpParams (prob.w - 1)).bumpData with hd
  obtain ⟨hfN, hA, -⟩ := hph (bumpCut d N c) (le_bumpCut d N c)
  have hI : InnerCombHyp c (bumpBc d N η σs c) := hin (bumpCut d N c) _ _ hfN hA
  obtain ⟨C, hC0, hd1, hd2, -⟩ := hk7 (bumpCut d N c) (le_bumpCut d N c)
  have htf : 0 ≤ sigTf σs c := by unfold sigTf; positivity
  have ht0 : 0 < t := by linarith
  have hx0 : 0 ≤ xOf c t := xOf_nonneg c t
  have hxt : c * xOf c t ^ 2 / 3 = t := by
    unfold xOf
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  have hpos := hIII (bumpCut d N c) (le_bumpCut d N c) (bumpCut_spec d N hc) (xOf c t) hx0
    (by rw [hxt]; exact ht)
  have hh : designProfile c 1 (bumpCut d N c) (1 / 4) (bumpSigma c N σs)
      (bumpEps d c N (1 / 4) (designWidth1 c η)) ((xOf c t : ℝ) : ℂ) =
      ((combProfile c (bumpBc d N η σs c) t : ℝ) : ℂ) := by
    have := hI.combProfile_eq (s := t) ht0
    rw [← combH0_designComb]
    exact this
  have e2 := hI.edgeHankelP_eq (prob.w - 1) hc hd1 ht0
  rw [Nat.sub_add_cancel prob.hw] at e2
  unfold twoGW at hpos
  rw [hxt, hh] at hpos
  have e3 : edgeHankelP (prob.w - 1) c (designProfile c 1 (bumpCut d N c) (1 / 4) (bumpSigma c N σs)
      (bumpEps d c N (1 / 4) (designWidth1 c η))) t =
      ((hankelTransform prob.w (combProfile c (bumpBc d N η σs c)) t : ℝ) : ℂ) := by
    rw [← combH0_designComb]
    exact e2
  rw [e3] at hpos
  simp only [Complex.sub_re, Complex.ofReal_re] at hpos
  unfold bumpG pairOdd
  linarith


/-! ### Window convergence of `Ψ_g` for the bumped designs (P3) and the vacuum bound (P4) -/

lemma bumpSigGVac_eq (prob : FixedWeightProblem) (d : BumpData) (N : ℕ) (η : ℝ) (σs : ℕ → ℝ) (c : ℝ) :
    bumpSigGVac prob d N (bumpCut d N c) η σs c = prob.gVac (c / 12) (bumpG prob d N η σs c) := rfl

/-- `sig_part1` at every weight: the hypothesis `prob.w = 1` of `sig_part1` is unused. -/
theorem sig_part1_w (prob : FixedWeightProblem) (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 ≤ η)
    (hη1 : η ≤ 1 / 4) (σs : ℕ → ℝ) {S : ℝ} (hS : 0 ≤ S) (n1 : ℕ) {ε' : ℝ} (hε' : 0 < ε') :
    ∀ᶠ c in atTop, ∀ σ ∈ Icc (-S) (phiWKB (n1 + 1)),
      |combProfile c (sigBc N η σs c) (c * (xiStar + lambdaComb c * σ) ^ 2 / 3) *
          prob.cardyV (c / 12) (c * (xiStar + lambdaComb c * σ) ^ 2 / 3) *
          ((2 * c * (xiStar + lambdaComb c * σ) / 3) * lambdaComb c) / FKc (qProb prob) 1 c -
        CStar * kappaAiry * sigWinW N η σs (-kappaAiry * σ)| ≤ ε' := by
  obtain ⟨C₀, hC₀, hW⟩ := lemma_W_measure prob
    (sigModFamily N hN hη0 hη1 σs) hS n1 ε' hε'
  filter_upwards [eventually_ge_atTop C₀, sigProfile_re_eq_modifiedH0 N hη0 hη1 σs,
    eventually_gt_atTop (0 : ℝ), lambda_mul_le S xiStar_pos] with c hc hE2 hcpos hlam σ hσ
  have hx : 0 ≤ xiStar + lambdaComb c * σ := by
    have h1 := hσ.1
    have := mul_le_mul_of_nonneg_left h1 (Cardy.lambdaComb_pos' hcpos).le
    nlinarith
  have h := hW hc (sigMod N η σs) (sigModFamily_mem N hN hη0 hη1 σs) σ hσ
  simp only [] at h
  rw [windowMeasureNormK_eq prob hcpos, tildeW_sigMod N hN η σs σ] at h
  unfold sigBc sigWinW
  rw [combProfile_sig_ofReal hx hcpos, hE2]
  exact h

/-- **Lemma `W` + Lemma `ID` for the bumped designs at every weight, two-sided** (`fw:e3.3`): the bump multiplies the
window integrand by `R_bump ∈ [1, 1 + C/c]` on `x ≤ ξ_* + r_p`, so the window limit is unchanged. -/
theorem bump_part1 (prob : FixedWeightProblem) (d : BumpData) (N : ℕ) (hN : 1 ≤ N) {η : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) (σs : ℕ → ℝ) {S : ℝ} (hS : 0 ≤ S) (n1 : ℕ) {ε' : ℝ} (hε' : 0 < ε') :
    ∀ᶠ c in atTop, ∀ N' : ℕ, N ≤ N' → ∀ σ ∈ Icc (-S) (phiWKB (n1 + 1)),
      |combProfile c (bumpSigComb d c N N' η σs) (c * (xiStar + lambdaComb c * σ) ^ 2 / 3) *
          prob.cardyV (c / 12) (c * (xiStar + lambdaComb c * σ) ^ 2 / 3) *
          ((2 * c * (xiStar + lambdaComb c * σ) / 3) * lambdaComb c) / FKc (qProb prob) 1 c -
        CStar * kappaAiry * sigWinW N η σs (-kappaAiry * σ)| ≤ ε' := by
  have hcw : Continuous fun σ : ℝ => CStar * kappaAiry * sigWinW N η σs (-kappaAiry * σ) := by
    unfold sigWinW
    exact continuous_const.mul ((continuous_sigWindowRe hN η σs).comp (by fun_prop))
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc (a := -S) (b := phiWKB (n1 + 1))).exists_bound_of_continuousOn
    hcw.continuousOn
  have hMb : 0 ≤ max M₀ 0 + ε' / 2 := by positivity
  have hcore : ∀ (R q w0 δ : ℝ), 1 ≤ R → R ≤ 1 + δ → 0 ≤ δ → |q - w0| ≤ ε' / 2 → |w0| ≤ max M₀ 0 →
      δ * (max M₀ 0 + ε' / 2) ≤ ε' / 2 → |R * q - w0| ≤ ε' := by
    intro R q w0 δ hR1 hRδ hδ hq hw hδM
    have hq' : |q| ≤ max M₀ 0 + ε' / 2 := by
      have := abs_sub_abs_le_abs_sub q w0
      linarith
    have hRq : |(R - 1) * q| ≤ δ * (max M₀ 0 + ε' / 2) := by
      rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ R - 1)]
      exact mul_le_mul (by linarith) hq' (abs_nonneg _) hδ
    have e : R * q - w0 = (R - 1) * q + (q - w0) := by ring
    rw [e]
    calc |(R - 1) * q + (q - w0)| ≤ |(R - 1) * q| + |q - w0| := abs_add_le _ _
      _ ≤ ε' := by linarith
  filter_upwards [sig_part1_w prob N hN hη0 hη1 σs hS n1 (half_pos hε'),
    bump_lemma d (η₀ := 1 / 4) (by norm_num) le_rfl, eventually_gt_atTop (0 : ℝ),
    lambda_mul_le S (half_pos xiStar_pos), lambda_mul_le (phiWKB (n1 + 1)) d.r_pos,
    eventually_ge_atTop (2 * bumpC' d (1 / 4) * (max M₀ 0 + ε' / 2) / ε' + 1),
    combProfile_bumped_eq d] with c hp1 hbl hcpos hlS hlΦ hcbig hval N' hNN' σ hσ
  have hlpos := Cardy.lambdaComb_pos' hcpos
  have hx : 0 ≤ xiStar + lambdaComb c * σ := by
    have h1 := mul_le_mul_of_nonneg_left hσ.1 hlpos.le
    have h2 : lambdaComb c * (-S) = -(lambdaComb c * S) := mul_neg _ _
    linarith [xiStar_pos]
  have hxr : xiStar + lambdaComb c * σ ≤ xiStar + d.r := by
    have h1 := mul_le_mul_of_nonneg_left hσ.2 hlpos.le
    linarith
  obtain ⟨-, -, hR1, -, hRn⟩ := hbl 1 N N' σs (designWidth1 c η) (xiStar + lambdaComb c * σ) hN hNN' hx
  have hδ : bumpC' d (1 / 4) / c * (max M₀ 0 + ε' / 2) ≤ ε' / 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hcpos]
    have h1 : 2 * bumpC' d (1 / 4) * (max M₀ 0 + ε' / 2) / ε' ≤ c := by linarith
    have h2 := (div_le_iff₀ hε').mp h1
    nlinarith only [h2]
  have hw0 : |CStar * kappaAiry * sigWinW N η σs (-kappaAiry * σ)| ≤ max M₀ 0 := by
    have := hM₀ σ hσ
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  have hq := hp1 σ hσ
  have hvt := hval N N' σs (designWidth1 c η) hN hNN' (c * (xiStar + lambdaComb c * σ) ^ 2 / 3)
  rw [xOf_comp hcpos hx] at hvt
  have hbc : combProfile c (bumpSigComb d c N N' η σs) (c * (xiStar + lambdaComb c * σ) ^ 2 / 3) =
      bumpFactor d c (1 / 4) N N' (xiStar + lambdaComb c * σ) *
        combProfile c (sigBc N η σs c) (c * (xiStar + lambdaComb c * σ) ^ 2 / 3) := hvt
  rw [hbc]
  have e : bumpFactor d c (1 / 4) N N' (xiStar + lambdaComb c * σ) *
        combProfile c (sigBc N η σs c) (c * (xiStar + lambdaComb c * σ) ^ 2 / 3) *
        prob.cardyV (c / 12) (c * (xiStar + lambdaComb c * σ) ^ 2 / 3) *
        ((2 * c * (xiStar + lambdaComb c * σ) / 3) * lambdaComb c) / FKc (qProb prob) 1 c =
      bumpFactor d c (1 / 4) N N' (xiStar + lambdaComb c * σ) *
        (combProfile c (sigBc N η σs c) (c * (xiStar + lambdaComb c * σ) ^ 2 / 3) *
          prob.cardyV (c / 12) (c * (xiStar + lambdaComb c * σ) ^ 2 / 3) *
          ((2 * c * (xiStar + lambdaComb c * σ) / 3) * lambdaComb c) / FKc (qProb prob) 1 c) := by
    ring
  rw [e]
  exact hcore _ _ _ _ hR1 (hRn hxr) (div_nonneg (bumpC'_nonneg d _) hcpos.le) hq hw0 hδ

/-- **Lemma `SD_G` against the far Cardy bound for the bumped designs, every weight** (`fw:e1.3`, `rem:cardy`):
`|ĥ₀^{(p)}(t)| V(t) (2 c x/3) ≤ K c` for `x ≥ ξ_*/2` (`ĥ₀ = hankelTransform prob.w h₀`), uniformly in the cut. -/
theorem bump_hat_window_bound (prob : FixedWeightProblem) (d : BumpData) (N : ℕ) (hN : 1 ≤ N) {η : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) (σs : ℕ → ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ c in atTop, ∀ N' : ℕ, N ≤ N' → ∀ x : ℝ, xiStar / 2 ≤ x →
      |hankelTransform prob.w (combProfile c (bumpSigComb d c N N' η σs)) (c * x ^ 2 / 3) *
        prob.cardyV (c / 12) (c * x ^ 2 / 3) * (2 * c * x / 3)| ≤ K * c := by
  obtain ⟨K0, A, Cε, C1, KG, hK0, hA0, hCε, hC1, hKG, hpkg⟩ := phase_packageP (prob.w - 1) 1 le_rfl
    (η₀ := 1 / 4) (by norm_num) le_rfl (P := 2) (by norm_num) (θ := 1 / 2) (by norm_num) (by norm_num)
  obtain ⟨C, c₀, hC, hfar⟩ := cardyFarBoundP_prob prob (x₀ := xiStar / 2) (half_pos xiStar_pos)
  have hξ := xiStar_pos
  refine ⟨KG * C * (1 + 2 / xiStar) ^ (prob.w - 1), by positivity, ?_⟩
  filter_upwards [hpkg, bumpSig_phaseHyp d N hN hη0 hη1 σs, bumpSig_k7W prob d N hN hη0 hη1 σs,
    designComb_innerCombHyp_of_admissible 1 le_rfl (η₀ := 1 / 4) (by norm_num) (by norm_num),
    eventually_ge_atTop c₀, eventually_ge_atTop (3 / (2 * π * xiStar)),
    eventually_gt_atTop (0 : ℝ)] with c hp hph hk7 hin hc₀ hc3 hcpos N' hNN' x hx
  have hxpos : 0 < x := lt_of_lt_of_le (half_pos hξ) hx
  have hglob := (hp N' _ _ (hph N' hNN')).2.2.2
  obtain ⟨hfN, hA, -⟩ := hph N' hNN'
  have hI : InnerCombHyp c (bumpSigComb d c N N' η σs) := hin N' _ _ hfN hA
  obtain ⟨C₀, hC0, hd1, hd2, -⟩ := hk7 N' hNN'
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
  have hht := hglob x hxpos hone
  have e2 := hI.edgeHankelP_eq (prob.w - 1) hcpos hd1 ht0
  rw [Nat.sub_add_cancel prob.hw] at e2
  have e3 : edgeHankelP (prob.w - 1) c (designProfile c 1 N' (1 / 4) (bumpSigma c N σs)
      (bumpEps d c N (1 / 4) (designWidth1 c η))) (c * x ^ 2 / 3) =
      ((hankelTransform prob.w (combProfile c (bumpSigComb d c N N' η σs)) (c * x ^ 2 / 3) : ℝ) : ℂ) := by
    rw [← combH0_designComb]
    exact e2
  rw [e3, Complex.norm_real, Real.norm_eq_abs] at hht
  obtain ⟨hV0, hVb⟩ := hfar c hc₀ x hx
  rw [besselL_eq_edgeL] at hVb
  set p := prob.w - 1 with hp'
  set A' : ℝ := |hankelTransform prob.w (combProfile c (bumpSigComb d c N N' η σs)) (c * x ^ 2 / 3)| with hA'
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

/-- Pointwise form of `Ψ_c` for the bumped design: `(2/(C_* FK)) g_w V J = (1/(C_* κ FK)) (h₀ - ĥ₀) V (dt/dσ)` at `u = -κσ`. -/
lemma psi_eq_bump (prob : FixedWeightProblem) {c : ℝ} (hc : 0 < c) (d : BumpData) (N : ℕ) (η : ℝ)
    (σs : ℕ → ℝ) (u σ : ℝ) (hσ : σ = -u / kappaAiry) (hx : 0 ≤ xiStar + lambdaComb c * σ) :
    psiScale prob c * psiAiry prob c (bumpG prob d N η σs c) u =
      (1 / (CStar * kappaAiry * FKc (qProb prob) 1 c)) *
        ((combProfile c (bumpBc d N η σs c) (c * (xiStar + lambdaComb c * σ) ^ 2 / 3) -
          hankelTransform prob.w (combProfile c (bumpBc d N η σs c))
            (c * (xiStar + lambdaComb c * σ) ^ 2 / 3)) *
          prob.cardyV (c / 12) (c * (xiStar + lambdaComb c * σ) ^ 2 / 3) *
          ((2 * c * (xiStar + lambdaComb c * σ) / 3) * lambdaComb c)) := by
  have hκ := kappaAiry_pos
  have hCs := CStar_pos
  have hFK := FKc_pos (qProb_pos prob) 1 hc
  subst hσ
  unfold psiScale psiAiry bumpG pairOdd
  rw [tAiry_eq hc hx, jAiry_eq hc hx]
  field_simp

/-- **(P3): the window limit of `Ψ_g` for the bumped designs, every weight.** -/
theorem bump_psi_uniform (prob : FixedWeightProblem) (d : BumpData) (N : ℕ) (hN : 1 ≤ N) {η : ℝ}
    (hη0 : 0 < η) (hη1 : η ≤ 1 / 4) (σs : ℕ → ℝ) {R : ℝ} (hR : 0 ≤ R) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ c in atTop, ∀ u ∈ Icc (-R) R,
      |psiScale prob c * psiAiry prob c (bumpG prob d N η σs c) u - sigWinW N η σs u| ≤ ε := by
  have hκ := kappaAiry_pos
  have hCs := CStar_pos
  have hP : 0 < CStar * kappaAiry := mul_pos hCs hκ
  set S : ℝ := R / kappaAiry with hS
  have hS0 : 0 ≤ S := by positivity
  have hSκ : S * kappaAiry = R := by rw [hS]; field_simp
  obtain ⟨n1, hn1⟩ := (phiWKB_succ_tendsto.eventually_ge_atTop S).exists
  obtain ⟨K, hK0, hKev⟩ := bump_hat_window_bound prob d N hN hη0.le hη1 σs
  set ε' : ℝ := ε * (CStar * kappaAiry) / 2 with hε'
  have hε'0 : 0 < ε' := by positivity
  set δ₂ : ℝ := ε * (CStar * kappaAiry) / (2 * (K + 1)) with hδ₂
  have hδ₂0 : 0 < δ₂ := by positivity
  have hlsq : ∀ᶠ c : ℝ in atTop, lambdaComb c * c ^ (1 / 2 : ℝ) ≤ δ₂ :=
    lambdaComb_mul_sqrt_tendsto.eventually_le_const hδ₂0
  filter_upwards [bump_part1 prob d N hN hη0.le hη1 σs hS0 n1 hε'0, hKev, hlsq,
    lambda_mul_le S (half_pos xiStar_pos), FKc_ge_mul_sqrt_of_pos (qProb_pos prob) 1,
    eventually_gt_atTop (1 : ℝ)] with c h1 hK hl hlS hFK hc1 u hu
  have hc0 : 0 < c := lt_trans one_pos hc1
  have hlam := Cardy.lambdaComb_pos' hc0
  have hFKpos := FKc_pos (qProb_pos prob) 1 hc0
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = -u / kappaAiry := ⟨_, rfl⟩
  have hσκ : σ * kappaAiry = -u := by rw [hσ]; field_simp
  have hlo : -S ≤ σ := by
    by_contra h
    push Not at h
    nlinarith [mul_lt_mul_of_pos_right h hκ, hu.2]
  have hhi : σ ≤ S := by
    by_contra h
    push Not at h
    nlinarith [mul_lt_mul_of_pos_right h hκ, hu.1]
  have hσS : σ ∈ Icc (-S) (phiWKB (n1 + 1)) := ⟨hlo, hhi.trans hn1⟩
  have hx : xiStar / 2 ≤ xiStar + lambdaComb c * σ := by
    have := mul_le_mul_of_nonneg_left hlo hlam.le
    nlinarith
  have hx0 : 0 ≤ xiStar + lambdaComb c * σ := le_trans (by have := xiStar_pos; positivity) hx
  have hWu : -kappaAiry * σ = u := by rw [hσ]; field_simp
  have hp1 := h1 (bumpCut d N c) (le_bumpCut d N c) σ hσS
  rw [hWu] at hp1
  have hp2 := hK (bumpCut d N c) (le_bumpCut d N c) _ hx
  rw [psi_eq_bump prob hc0 d N η σs u σ hσ hx0]
  change |(1 / (CStar * kappaAiry * FKc (qProb prob) 1 c)) *
      ((combProfile c (bumpSigComb d c N (bumpCut d N c) η σs) (c * (xiStar + lambdaComb c * σ) ^ 2 / 3) -
        hankelTransform prob.w (combProfile c (bumpSigComb d c N (bumpCut d N c) η σs))
          (c * (xiStar + lambdaComb c * σ) ^ 2 / 3)) *
        prob.cardyV (c / 12) (c * (xiStar + lambdaComb c * σ) ^ 2 / 3) *
        ((2 * c * (xiStar + lambdaComb c * σ) / 3) * lambdaComb c)) - sigWinW N η σs u| ≤ ε
  set x : ℝ := xiStar + lambdaComb c * σ with hxdef
  set t : ℝ := c * x ^ 2 / 3 with htdef
  set h : ℝ := combProfile c (bumpSigComb d c N (bumpCut d N c) η σs) t with hhdef
  set ĥ : ℝ := hankelTransform prob.w (combProfile c (bumpSigComb d c N (bumpCut d N c) η σs)) t with hĥdef
  set V : ℝ := prob.cardyV (c / 12) t with hVdef
  set Dt : ℝ := (2 * c * x / 3) * lambdaComb c with hDt
  set P : ℝ := CStar * kappaAiry with hPdef
  set FK : ℝ := FKc (qProb prob) 1 c with hFKdef
  set Wu : ℝ := sigWinW N η σs u with hWudef
  have hB : |ĥ * V * Dt| ≤ ε / 2 * (P * FK) := by
    have e1 : ĥ * V * Dt = (ĥ * V * (2 * c * x / 3)) * lambdaComb c := by rw [hDt]; ring
    rw [e1, abs_mul, abs_of_pos hlam]
    have hc2 : c = √c * √c := (Real.mul_self_sqrt hc0.le).symm
    have hsq : lambdaComb c * √c ≤ δ₂ := by rw [Real.sqrt_eq_rpow]; exact hl
    have hsqp : 0 < √c := Real.sqrt_pos.mpr hc0
    have hFK' : √c ≤ FK := by simpa using hFK
    calc |ĥ * V * (2 * c * x / 3)| * lambdaComb c ≤ (K * c) * lambdaComb c :=
          mul_le_mul_of_nonneg_right hp2 hlam.le
      _ = K * (lambdaComb c * √c) * √c := by
          linear_combination (K * lambdaComb c) * hc2
      _ ≤ K * δ₂ * FK := by
          gcongr
      _ ≤ ε / 2 * (P * FK) := by
          have : K * δ₂ = ε * P / 2 * (K / (K + 1)) := by
            rw [hδ₂, hPdef]; field_simp
          rw [this]
          have hk1 : K / (K + 1) ≤ 1 := by
            rw [div_le_one (by linarith)]; linarith
          have hεP : 0 ≤ ε * P / 2 := by positivity
          calc ε * P / 2 * (K / (K + 1)) * FK ≤ ε * P / 2 * 1 * FK := by gcongr
            _ = ε / 2 * (P * FK) := by ring
  have hdecomp : 1 / (P * FK) * ((h - ĥ) * V * Dt) - Wu =
      (1 / P) * (h * V * Dt / FK - P * Wu) - (ĥ * V * Dt) / (P * FK) := by
    field_simp
    ring
  rw [hdecomp]
  have hA : |(1 / P) * (h * V * Dt / FK - P * Wu)| ≤ ε / 2 := by
    rw [abs_mul, abs_of_pos (one_div_pos.mpr hP)]
    calc 1 / P * |h * V * Dt / FK - P * Wu| ≤ 1 / P * ε' := by gcongr
      _ = ε / 2 := by rw [hε']; field_simp
  have hBB : |(ĥ * V * Dt) / (P * FK)| ≤ ε / 2 := by
    rw [abs_div, abs_of_pos (mul_pos hP hFKpos), div_le_iff₀ (mul_pos hP hFKpos)]
    exact hB
  calc |(1 / P) * (h * V * Dt / FK - P * Wu) - (ĥ * V * Dt) / (P * FK)|
      ≤ |(1 / P) * (h * V * Dt / FK - P * Wu)| + |(ĥ * V * Dt) / (P * FK)| := abs_sub _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add hA hBB
    _ = ε := by ring

/-- **(P4): the vacuum bound** `∫ Ψ_c du ≤ V + ε` for the bumped designs, every weight (`V = windowIntegralSig`). -/
theorem bump_psi_limsup (prob : FixedWeightProblem) (d : BumpData) (N : ℕ) (hN : 1 ≤ N) {η : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) (σs : ℕ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ c in atTop,
      ∫ u, psiScale prob c * psiAiry prob c (bumpG prob d N η σs c) u ≤ windowIntegralSig N η σs + ε := by
  have hCs := CStar_pos
  filter_upwards [proposition_V_i_bumped prob d N hN hη0 hη1 σs (ε := ε * CStar) (by positivity),
    eventually_gt_atTop (0 : ℝ)] with c hV hc0
  have hV' := hV (bumpCut d N c) (le_bumpCut d N c)
  have hFK := FKc_pos (qProb_pos prob) 1 hc0
  rw [integral_const_mul, integral_psiAiry_eq_neg_gVac prob hc0]
  have e : psiScale prob c * (-prob.gVac (c / 12) (bumpG prob d N η σs c) / (2 * π)) =
      (2 * bumpSigPsiIntegral prob d N (bumpCut d N c) η σs c / FKc (qProb prob) 1 c) / CStar := by
    unfold psiScale bumpSigPsiIntegral
    rw [bumpSigGVac_eq prob]
    field_simp
  rw [e, div_le_iff₀ hCs]
  have : windowIntegralSig N η σs * CStar + ε * CStar = CStar * windowIntegralSig N η σs + ε * CStar := by ring
  linarith


/-! ### Property (P) at every weight -/

/-- The eventual comb data of any window `D` whose window function is the Airy window `sigWinW N η σs` of the `f = 1`
finite modification with offsets `σs` and whose first site is `u_f = -κ σ_1`, **at every weight**: the test is the
bumped design `g_w = ½(h₀^{(p)} - 𝓗_w h₀^{(p)})` (`bumpG`) with the bump of `rpParams (prob.w - 1)`
(`sigEventual` is the unbumped weight-one case). -/
noncomputable def bumpEventual (prob : FixedWeightProblem) (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη : 0 < η)
    (hη1 : η ≤ 1 / 4) (σs : ℕ → ℝ) (D : Window) (hW : D.W = sigWinW N η σs)
    (hF : D.uF = -(kappaAiry * σs 1)) : EventualCombData prob D where
  g := bumpG prob (rpParams (prob.w - 1)).bumpData N η σs
  scale := psiScale prob
  tf := sigTf σs
  good := by
    filter_upwards [bumpG_good prob (rpParams (prob.w - 1)).bumpData N hN hη.le hη1 σs,
      bumpG_pos prob N hN hη hη1 σs] with c hgood hpos
    obtain ⟨hc, hT, hdec⟩ := hgood
    refine ⟨hc, psiScale_pos prob hc, hT, hdec, ?_, fun t ht => (hpos t ht).le⟩
    unfold sigTf; positivity
  theta := by rw [hF]; exact uAiry_sigTf σs
  window := fun R hR ε hε => by
    rw [hW]; exact bump_psi_uniform prob _ N hN hη hη1 σs hR hε
  limsup := fun ε hε => by
    have hV : D.V = windowIntegralSig N η σs := by
      unfold Window.V windowIntegralSig; rw [hW]; rfl
    rw [hV]; exact bump_psi_limsup prob _ N hN hη.le hη1 σs hε

/-- **`(P1)`-`(P4)` for the designs at every weight**: `CombDesignData S (designWin N hη d)` for every crossing sequence
`S` of every fixed-weight problem. -/
noncomputable def combDesignData_designW (prob : FixedWeightProblem) (S : CrossingSequence prob) (N : ℕ)
    (hN : 1 ≤ N) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 4) (d : ℝ) : CombDesignData S (designWin N hη d) :=
  (bumpEventual prob N hN hη hη1 (designSigma1 d) (designWin N hη d) (designWin_W_eq_sig N hη d)
    (designWin_uF_eq_sig N hη d)).toComb S

/-- **Property `sr:P` for the designs of every fixed-weight problem, at every weight** (`sr:P`, `ut:Vac`, `ut:III`,
`wone:clark`(a) design side): every window `D(N, η_*, d)` of `designClass` carries a design test for the spectral
measures `μ_S` of every crossing sequence `S` of `prob`, with the bump of `rpParams (prob.w - 1)` for `w > 1`.  For
`prob.w = 1` it is `designPropertyP_prob`. -/
theorem designPropertyP_probW (prob : FixedWeightProblem) (S : CrossingSequence prob) :
    DesignPropertyP S.μS designClass := by
  refine designPropertyP_of_comb S fun D hD => ?_
  obtain ⟨N, η, d, hη, hN, hη1, rfl⟩ := hD
  exact ⟨combDesignData_designW prob S N hN hη hη1 d⟩

/-- **Property `sr:P` for the displaced and far-first-site designs at every weight.** -/
theorem displacedPropertyP_probW (prob : FixedWeightProblem) (S : CrossingSequence prob) :
    DesignPropertyP S.μS displacedClassX := by
  refine designPropertyP_of_comb S fun D hD => ?_
  obtain ⟨N, η, e, d, hη, hH, hN, hη1, he, rfl⟩ := hD
  refine ⟨(bumpEventual prob N hN hη hη1 (dispSigma d e) _ ?_ ?_).toComb S⟩
  · funext u
    rw [profWin_W]
    show (profW (dispSite N e) (designWidthU N η) d (u : ℂ)).re = (sigWindowW N η (dispSigma d e) (u : ℂ)).re
    rw [sigWindowW_dispSite N η d e he]
  · rw [profWin_uF, dispSigma_one]

/-! ### `Σ₀` and `Σ` at every weight (wiring) -/

/-- **`Σ₀` at every weight** for every crossing sequence with `T_V(c_j) ≤ τ_j`, given the threshold lower bound `hLo`
and the window algebra `SameSiteFamily designClass`. -/
theorem sigmaZero_of_threshold_probW (prob : FixedWeightProblem)
    (hLo : FormalResearch.ModularBootstrap.FixedWeight.FixedWeightLowerBoundInput prob)
    (S : CrossingSequence prob) (hτ : ∀ j, prob.T_V (S.c j) ≤ S.τ j) (F : SameSiteFamily designClass) :
    SigmaZeroConclusion S.c S.τ S.μS :=
  theorem_sigma_zero_crossing S (gapCondition_of_lowerBound hLo S.tendsto_c hτ)
    (designPropertyP_probW prob S) F

/-- **`Σ₀` at every weight for the extremal measures, unconditionally**
(`sr:Sigma0`; `wone:clark`(c) first part): for every `c`-sequence tending to infinity (above a threshold) there is an
extremal crossing sequence (gap exactly `T_V(c_j)`) whose limit measure satisfies the conclusion of `Σ₀`.  The
threshold lower bound is `fixedWeightLowerBoundInput_of_problem` (every `(w, Q)`). -/
theorem sigmaZero_unconditional_probW (prob : FixedWeightProblem) :
    ∃ c₀ : ℝ, ∀ cSeq : ℕ → ℝ, Tendsto cSeq atTop atTop → (∀ j, c₀ ≤ cSeq j) →
      ∃ S : CrossingSequence prob, S.c = cSeq ∧
        (∀ j, S.τ j = prob.T_V (cSeq j)) ∧
        (∀ j, ∀ ε : ℝ, 0 < ε → 0 < (S.meas j).ν (Set.Iio (S.τ j + ε))) ∧
        SigmaZeroConclusion S.c S.τ S.μS := by
  have hLo := FormalResearch.ModularBootstrap.FixedWeightBand.fixedWeightLowerBoundInput_of_problem prob
  obtain ⟨c₀, h⟩ := exists_optimalCrossingSequence prob hLo
  refine ⟨c₀, fun cSeq hc hge => ?_⟩
  obtain ⟨S, hS, hτ, hchg, -⟩ := h cSeq hc hge
  exact ⟨S, hS, hτ, hchg,
    sigmaZero_of_threshold_probW prob hLo S (fun j => by rw [hS, hτ j])
      (sameSiteFamily_designClass designTailBounds).some⟩

/-- **`Σ` at every weight** for every crossing sequence with `T_V(c_j) ≤ τ_j`, given the threshold lower bound `hLo`;
`𝒟x` is a class of further designs with Property `sr:P`, and the window algebra on `designClass ∪ 𝒟x` is assumed
(`sigma_of_threshold_prob` at weight one). -/
theorem sigma_of_threshold_probW (prob : FixedWeightProblem)
    (hLo : FormalResearch.ModularBootstrap.FixedWeight.FixedWeightLowerBoundInput prob)
    (S : CrossingSequence prob) (hτ : ∀ j, prob.T_V (S.c j) ≤ S.τ j) {𝒟x : Set Window}
    (hPx : DesignPropertyP S.μS 𝒟x) (F : SameSiteFamily designClass)
    (Dis : DisplacedFamily (designClass ∪ 𝒟x)) (Om : OmittedFamily (designClass ∪ 𝒟x)) :
    SigmaConclusion S.μS :=
  theorem_sigma_crossing S (gapCondition_of_lowerBound hLo S.tendsto_c hτ)
    (designPropertyP_union (designPropertyP_probW prob S) hPx)
    (SameSiteFamily.mono Set.subset_union_left F) Dis Om

/-- **`Σ` at every weight for the extremal measures, unconditionally** (`sr:Sigma`; `wone:clark`(c) first part): the
far-first-site omitted family replaces the paper's `f ≥ 2` Step 6, as at weight one
(`sigma_unconditional_prob`). -/
theorem sigma_unconditional_probW (prob : FixedWeightProblem) :
    ∃ c₀ : ℝ, ∀ cSeq : ℕ → ℝ, Tendsto cSeq atTop atTop → (∀ j, c₀ ≤ cSeq j) →
      ∃ S : CrossingSequence prob, S.c = cSeq ∧
        (∀ j, S.τ j = prob.T_V (cSeq j)) ∧
        (∀ j, ∀ ε : ℝ, 0 < ε → 0 < (S.meas j).ν (Set.Iio (S.τ j + ε))) ∧
        SigmaConclusion S.μS := by
  have hLo := FormalResearch.ModularBootstrap.FixedWeightBand.fixedWeightLowerBoundInput_of_problem prob
  obtain ⟨c₀, h⟩ := exists_optimalCrossingSequence prob hLo
  refine ⟨c₀, fun cSeq hc hge => ?_⟩
  obtain ⟨S, hS, hτ, hchg, -⟩ := h cSeq hc hge
  exact ⟨S, hS, hτ, hchg,
    sigma_of_threshold_probW prob hLo S (fun j => by rw [hS, hτ j]) (displacedPropertyP_probW prob S)
      (sameSiteFamily_designClass designTailBounds).some
      (DisplacedFamily.mono (displacedClass_subset.trans Set.subset_union_right) displacedFamily)
      farFamily⟩

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.bumpG_good' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bumpG_good

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.bumpG_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bumpG_pos

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.bump_part1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bump_part1

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.bump_hat_window_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bump_hat_window_bound

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.bump_psi_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bump_psi_uniform

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.bump_psi_limsup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bump_psi_limsup

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.designPropertyP_probW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms designPropertyP_probW

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.displacedPropertyP_probW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms displacedPropertyP_probW

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.sigmaZero_unconditional_probW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sigmaZero_unconditional_probW

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.sigma_of_threshold_probW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sigma_of_threshold_probW

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.sigma_unconditional_probW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sigma_unconditional_probW

end FormalResearch.ModularBootstrap.Upper.Assembly
