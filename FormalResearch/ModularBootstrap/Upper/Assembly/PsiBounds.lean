module

public import FormalResearch.ModularBootstrap.Upper.Assembly.Chart

/-!
# The two window estimates for `Ψ_g`: the comb part (Lemma `W`) and the transform part (Lemma `SD_G`)

Source: `CFT/modular_bootstrap/paper/spectral_rigidity.tex` ((P3), the window limit of `Ψ_g`),
`upper_transfer.tex` (`ut:W`, `ut:ID`, `ut:G`; `edge_transform_sd.tex`, `esd:global`).

For the design `D(N, η_*, d)`, `t = c x²/3`, `x = ξ_* + λσ`, `dt/dσ = (2 c x/3) λ`, `FK_c = FKc 1 1 c`:

* `design_part1`: `h₀(t) V(t) (dt/dσ) / FK_c → C_* κ Re W(-κσ)`, uniformly for `σ ∈ [-S, Φ_{N₁+1}]`
  (Lemma `W` with Lemma `ID`; two-sided form of `design_window_pointwise`);
* `hat_window_bound`: `|ĥ₀(t)| V(t) (2 c x/3) ≤ K c` for all `x ≥ ξ_*/2` (Lemma `SD_G`,
  `e^{c L} |ĥ₀| ≤ K √(c/x)`, against the far Cardy bound `V e^{-c L} (2 c x/3) ≤ C √c √x`).

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Assembly

open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.Upper.Hankel FormalResearch.ModularBootstrap.Upper.Comb
  FormalResearch.ModularBootstrap.Upper.Design FormalResearch.ModularBootstrap.Upper.Window
  FormalResearch.ModularBootstrap.Upper.Window.Cardy FormalResearch.ModularBootstrap.Upper.Holes
  FormalResearch.ModularBootstrap.Upper.Membership FormalResearch.ModularBootstrap.Upper.Positivity

/-- The real window `W(u) = Re W(u)` of the modification with offsets `σs`. -/
noncomputable def sigWinW (N : ℕ) (η : ℝ) (σs : ℕ → ℝ) (u : ℝ) : ℝ := (sigWindowW N η σs (u : ℂ)).re

/-- The real window `W_D(u) = Re W(u)` of the design `D(N, η_*, d)`. -/
noncomputable def designWinW (N : ℕ) (η d : ℝ) (u : ℝ) : ℝ := (designWindowW N η d (u : ℂ)).re

lemma designWinW_eq_sig (N : ℕ) (η d : ℝ) : designWinW N η d = sigWinW N η (designSigma1 d) := by
  funext u
  unfold designWinW sigWinW
  rw [designWindowW_eq_sig]

/-- **Lemma `W` + Lemma `ID` for the finite modifications with arbitrary offsets, two-sided**: see
`design_part1`, the case `σs = designSigma1 d`. -/
theorem sig_part1 (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) (σs : ℕ → ℝ)
    {S : ℝ} (hS : 0 ≤ S) (n1 : ℕ) {ε' : ℝ} (hε' : 0 < ε') :
    ∀ᶠ c in atTop, ∀ σ ∈ Icc (-S) (phiWKB (n1 + 1)),
      |combProfile c (sigBc N η σs c) (c * (xiStar + lambdaComb c * σ) ^ 2 / 3) *
          virasoroProblem.cardyV (c / 12) (c * (xiStar + lambdaComb c * σ) ^ 2 / 3) *
          ((2 * c * (xiStar + lambdaComb c * σ) / 3) * lambdaComb c) / FKc 1 1 c -
        CStar * kappaAiry * sigWinW N η σs (-kappaAiry * σ)| ≤ ε' := by
  obtain ⟨C₀, hC₀, hW⟩ := lemma_W_measure virasoroProblem
    (sigModFamily N hN hη0 hη1 σs) hS n1 ε' hε'
  filter_upwards [eventually_ge_atTop C₀, sigProfile_re_eq_modifiedH0 N hη0 hη1 σs,
    eventually_gt_atTop (0 : ℝ), lambda_mul_le S xiStar_pos] with c hc hE2 hcpos hlam σ hσ
  have hx : 0 ≤ xiStar + lambdaComb c * σ := by
    have h1 := hσ.1
    have := mul_le_mul_of_nonneg_left h1 (lambdaComb_pos' hcpos).le
    nlinarith
  have h := hW hc (sigMod N η σs) (sigModFamily_mem N hN hη0 hη1 σs) σ hσ
  simp only [] at h
  rw [windowMeasureNormK_virasoro hcpos, tildeW_sigMod N hN η σs σ] at h
  unfold sigBc sigWinW
  rw [combProfile_sig_ofReal hx hcpos, hE2]
  exact h

/-- **Lemma `W` + Lemma `ID` for the designs, two-sided.** -/
theorem design_part1 (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) (d : ℝ)
    {S : ℝ} (hS : 0 ≤ S) (n1 : ℕ) {ε' : ℝ} (hε' : 0 < ε') :
    ∀ᶠ c in atTop, ∀ σ ∈ Icc (-S) (phiWKB (n1 + 1)),
      |combProfile c (designBc N η d c) (c * (xiStar + lambdaComb c * σ) ^ 2 / 3) *
          virasoroProblem.cardyV (c / 12) (c * (xiStar + lambdaComb c * σ) ^ 2 / 3) *
          ((2 * c * (xiStar + lambdaComb c * σ) / 3) * lambdaComb c) / FKc 1 1 c -
        CStar * kappaAiry * designWinW N η d (-kappaAiry * σ)| ≤ ε' :=
  by
  simpa only [designWinW_eq_sig, designBc] using sig_part1 N hN hη0 hη1 (designSigma1 d) hS n1 hε'

lemma besselL_eq_edgeL (x : ℝ) : Bessel.besselL x = edgeL x := rfl

/-- **Lemma `SD_G` against the far Cardy bound**, arbitrary offsets `σs`: see `hat_window_bound`. -/
theorem sig_hat_window_bound (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) (σs : ℕ → ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ c in atTop, ∀ x : ℝ, xiStar / 2 ≤ x →
      |hankelTransform 1 (combProfile c (sigBc N η σs c)) (c * x ^ 2 / 3) *
        virasoroProblem.cardyV (c / 12) (c * x ^ 2 / 3) * (2 * c * x / 3)| ≤ K * c := by
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ k, 1 ≤ k → k ≤ N → |σs k| ≤ M :=
    ⟨∑ k ∈ Finset.Icc 1 N, |σs k|, fun k hk hkN =>
      Finset.single_le_sum (f := fun j => |σs j|) (fun _ _ => abs_nonneg _)
        (Finset.mem_Icc.mpr ⟨hk, hkN⟩)⟩
  obtain ⟨Cg, hCg, hW⟩ := designWidth1_family N hη0 hη1
  obtain ⟨K, hK0, hK⟩ := designProfile_global_bound 1 N le_rfl hN M Cg
    (η₀ := 1 / 4) (by norm_num) le_rfl
  obtain ⟨C, c₀, hC, hfar⟩ := cardyFarBound_virasoro (x₀ := xiStar / 2) (half_pos xiStar_pos)
  refine ⟨K * C, by positivity, ?_⟩
  filter_upwards [hK, hW, sigGood_eventually N hN hη0 hη1 σs, eventually_ge_atTop c₀,
    eventually_gt_atTop (0 : ℝ)] with c hKc hWc hgood hc₀ hcpos x hx
  have hxpos : 0 < x := lt_of_lt_of_le (half_pos xiStar_pos) hx
  obtain ⟨-, hInner, C₀, hC0, hd1, hd2, -⟩ := hgood
  have ht0 : 0 < c * x ^ 2 / 3 := by positivity
  have hedge := hInner.edgeHankel_eq hcpos hd1 ht0
  have hht := hKc (σs) (designWidth1 c η) (fun k hk hkN => hM k hk hkN)
    (fun k hk hkN => hWc k hk hkN) x hxpos
  have e : designProfile c 1 N (1 / 4) (σs) (designWidth1 c η) =
      combH0 (sigBc N η σs c) := rfl
  rw [e, hedge, Complex.norm_real, Real.norm_eq_abs] at hht
  obtain ⟨hV0, hVb⟩ := hfar c hc₀ x hx
  rw [besselL_eq_edgeL] at hVb
  set A : ℝ := |hankelTransform 1 (combProfile c (sigBc N η σs c)) (c * x ^ 2 / 3)| with hA
  set V : ℝ := virasoroProblem.cardyV (c / 12) (c * x ^ 2 / 3) with hV
  have hA0 : 0 ≤ A := abs_nonneg _
  have hx3 : 0 ≤ 2 * c * x / 3 := by positivity
  rw [abs_mul, abs_mul, abs_of_nonneg hV0, abs_of_nonneg hx3, ← hA]
  have h1 : A * V * (2 * c * x / 3) =
      (Real.exp (c * edgeL x) * A) * (V * Real.exp (-(c * edgeL x)) * (2 / 3 * c * x)) := by
    rw [Real.exp_neg]
    have := Real.exp_pos (c * edgeL x)
    field_simp
  rw [h1]
  have h2 : (Real.exp (c * edgeL x) * A) * (V * Real.exp (-(c * edgeL x)) * (2 / 3 * c * x)) ≤
      (K * √(c / x)) * (C * √c * √x) :=
    mul_le_mul hht hVb (by
      have := Real.exp_pos (-(c * edgeL x))
      positivity) (by positivity)
  have h3 : (K * √(c / x)) * (C * √c * √x) = K * C * c := by
    have e1 : √(c / x) * √x = √c := by
      rw [← Real.sqrt_mul (by positivity), div_mul_cancel₀ _ hxpos.ne']
    have e2 : √c * √c = c := Real.mul_self_sqrt hcpos.le
    calc (K * √(c / x)) * (C * √c * √x) = K * C * ((√(c / x) * √x) * √c) := by ring
      _ = K * C * c := by rw [e1, e2]
  linarith

/-- **Lemma `SD_G` against the far Cardy bound**: `|ĥ₀(t)| V(t) (2 c x/3) ≤ K c` for `x ≥ ξ_*/2`. -/
theorem hat_window_bound (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) (d : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ c in atTop, ∀ x : ℝ, xiStar / 2 ≤ x →
      |hankelTransform 1 (combProfile c (designBc N η d c)) (c * x ^ 2 / 3) *
        virasoroProblem.cardyV (c / 12) (c * x ^ 2 / 3) * (2 * c * x / 3)| ≤ K * c :=
  sig_hat_window_bound N hN hη0 hη1 (designSigma1 d)

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.sig_part1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sig_part1

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.design_part1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms design_part1

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.hat_window_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hat_window_bound

end FormalResearch.ModularBootstrap.Upper.Assembly
