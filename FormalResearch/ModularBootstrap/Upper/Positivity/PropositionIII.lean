module

public import FormalResearch.ModularBootstrap.Upper.Positivity.PropositionIIIRegionII
public import FormalResearch.ModularBootstrap.Crossing.Setup

/-!
# Proposition III: positivity of `g_w` at fixed `(w, Q)` for the bumped fixed designs (`ut:III`)

Source: `CFT/modular_bootstrap/paper/upper_transfer.tex`, Proposition III (`ut:III`) and its proof (Region I, near-tip
Region II, macroscopic Region II), with `fw:e1.3`, `fw:e1.6`, `fw:e2.2`, `fw:e2.3`, `fw:e3.1`, `fw:e3.5`.

For a fixed-weight problem `prob` put `p = prob.w - 1`, `P = rpParams p` (`r_p`, `X_p`, `η_big(p)`, `fw:e2.2`, `fw:e2.3`,
parameter selection) and `d = P.bumpData`.  `twoGW p c' f N η₀ σ ε x = 2 g_w(c' x²/3)` is the order-`p` test
(`h₀(x) - (𝓗_{p+1} h₀)(t)`, real part), `t = c' x²/3`.  The bumped design of a base finite modification
`(f, N₀, σ, ε)` with a cut `N ≥ N₀` above the block `[ξ_* + 2 r_p, X_p]` is
`designComb c' f N (1/4) (bumpSigma c' N₀ σ) (bumpEps d c' N₀ (1/4) ε)` (`Upper.Bump`).

* `bumped_regionI_pos` (Region I): the bump only raises `h₀` on the real axis (`R_bump ≥ 1`, `fw:e3.3`), so a lower bound
  `A √c' < h₀ e^{c'L}` of the base design is inherited by the bumped design, and the order-`p` global bound
  `fw:e1.3` (`twoGW_pos_of_lower`, `RegionOne`) closes it.
* `proposition_III_sig`, `proposition_III_sig_t`, `proposition_III_design`, `proposition_III_design_t`: the `f = 1`
  designs at fixed sites `σs` (arbitrary sites, `σs = designSigma1 d` for the designs `D(N, η_*, d)`), width
  `designWidth1 c' η_*`, all of `x ≥ χ'_1 + C λ c'^{-1/2}`, i.e. all `t ≥ t_f + 1`.  Region I(a), I(b) are the lower bounds
  `proposition_I_a_sig_lower`, `proposition_I_b_sig_lower` of the base design; Region II is `bumped_regionII_pos`
  (any `f ≥ 1`, compact family).
* `proposition_III`, `proposition_III_regionII`: the statements for a `FixedWeightProblem` (`p = prob.w - 1`,
  `P = rpParams p`).
* `proposition_I_sigW`: Region I at weight `w` for the unbumped designs (the bump is absent there in the paper).
* `twoGW_prob_one`: at `w = 1` the order-`p` test is the original `twoG`, and `proposition_I_design_t` with
  `proposition_II_design` are the unbumped statements at `w = 1` (the bump is not needed there).
* `exists_cut_ge`, `proposition_III_nonvacuous`: cuts above the block exist, so the hypotheses are satisfiable.

Region I at `f ≥ 2` is not part of `RegionOne` at any weight (it is the `f = 1` Lemma R window); the compact-family
statement of this file is Region II.

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Positivity

open FormalResearch.ModularBootstrap.Upper.Comb FormalResearch.ModularBootstrap.Upper.Hankel
  FormalResearch.ModularBootstrap.Upper.Saddle FormalResearch.ModularBootstrap.Upper.Design
  FormalResearch.ModularBootstrap.Upper.Holes FormalResearch.ModularBootstrap.Upper.Bump
  FormalResearch.ModularBootstrap.Crossing

/-! ### 1. Region I for the bumped designs -/

/-- **Region I for the bumped designs** (`ut:III`, Region I; `fw:e1.3`, `fw:e3.3`).  For fixed `p`, `P : RpParams p` and
`f ≥ 1` there is `A ≥ 0` such that for `c'` large, every admissible base data `(f, N₀, σ, ε)`, every cut `N ≥ N₀` and every
`x ≥ ξ_*/2` with `A √c' < h₀(x) e^{c' L(x)}` for the base design, `2 g_w(c' x²/3) > 0` for the bumped design. -/
theorem bumped_regionI_pos (p : ℕ) (P : RpParams p) (f : ℕ) (hf : 1 ≤ f) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ c' in atTop, ∀ (N₀ N : ℕ) (σ ε : ℕ → ℝ), f ≤ N₀ → N₀ ≤ N →
      DesignAdmissible c' f N₀ (1 / 4) σ ε → ∀ x : ℝ, xiStar / 2 ≤ x →
      A * √c' < (designProfile c' f N₀ (1 / 4) σ ε (x : ℂ)).re * Real.exp (c' * edgeL x) →
      0 < twoGW p c' f N (1 / 4) (bumpSigma c' N₀ σ) (bumpEps P.bumpData c' N₀ (1 / 4) ε) x := by
  obtain ⟨A, hA0, hA⟩ := twoGW_pos_of_lower p f (η₀ := 1 / 4) (by norm_num) le_rfl
  refine ⟨A, hA0, ?_⟩
  filter_upwards [hA, bumped_admissible P.bumpData f hf (η₀ := 1 / 4) (by norm_num) le_rfl,
    bumped_value P.bumpData (η₀ := 1 / 4) (by norm_num) le_rfl,
    bumpFactor_one_le P.bumpData (η₀ := 1 / 4) (by norm_num) le_rfl]
    with c' hAc hbad hv hR1 N₀ N σ ε hfN₀ hN hadm x hx hlow
  obtain ⟨hb, hbump⟩ := hv f N₀ N σ ε x hfN₀ hN
  set Rb := bumpFactor P.bumpData c' (1 / 4) N₀ N x with hRb
  set cr := combReal c' f N₀ (1 / 4) σ ε x with hcr
  set s : ℝ := 1 / Real.cosh (π * x / 2) ^ 2 with hs
  have hspos : 0 < s := by positivity
  have hprof0 : (designProfile c' f N₀ (1 / 4) σ ε (x : ℂ)).re = s * cr := by
    rw [designProfile_ofReal hb, Complex.ofReal_re]
  have hbc : designComb c' f N (1 / 4) (bumpSigma c' N₀ σ) (bumpEps P.bumpData c' N₀ (1 / 4) ε)
      (x : ℂ) = ((Rb * cr : ℝ) : ℂ) := by
    have h := hbump
    unfold bumpedComb at h
    exact h
  have hprof1 : (designProfile c' f N (1 / 4) (bumpSigma c' N₀ σ) (bumpEps P.bumpData c' N₀ (1 / 4) ε)
      (x : ℂ)).re = s * (Rb * cr) := by
    rw [designProfile_ofReal hbc, Complex.ofReal_re]
  have hE : 0 < Real.exp (c' * edgeL x) := Real.exp_pos _
  have hApos : 0 ≤ A * √c' := mul_nonneg hA0 (Real.sqrt_nonneg _)
  have hpos0 : 0 < (designProfile c' f N₀ (1 / 4) σ ε (x : ℂ)).re * Real.exp (c' * edgeL x) :=
    lt_of_le_of_lt hApos hlow
  have hre0 : 0 < (designProfile c' f N₀ (1 / 4) σ ε (x : ℂ)).re := pos_of_mul_pos_left hpos0 hE.le
  have hcrpos : 0 < cr := by
    rw [hprof0] at hre0
    exact pos_of_mul_pos_right hre0 hspos.le
  have hmono : s * cr ≤ s * (Rb * cr) := by
    refine mul_le_mul_of_nonneg_left ?_ hspos.le
    have := hR1 N₀ N x
    nlinarith
  have hlow' : A * √c' < (designProfile c' f N (1 / 4) (bumpSigma c' N₀ σ)
      (bumpEps P.bumpData c' N₀ (1 / 4) ε) (x : ℂ)).re * Real.exp (c' * edgeL x) := by
    refine lt_of_lt_of_le hlow (mul_le_mul_of_nonneg_right ?_ hE.le)
    rw [hprof0, hprof1]
    exact hmono
  exact hAc N _ _ (hbad N₀ N σ ε hfN₀ hN hadm) x hx hlow'

/-- **Region I at weight `w = p + 1`, unbumped** (`ut:III`, Region I, `fw:e1.3`): for the `f = 1` finite modifications at
fixed sites `σs`, with the order-`p` transform, `x ∈ [χ'_1 + C λ c'^{-1/2}, ξ_I]` gives `2 g_w > 0` (the bump is not
needed there; `proposition_I_a_sig`, `proposition_I_b_sig` are the case `p = 0`). -/
theorem proposition_I_sigW (p : ℕ) (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 4)
    (σs : ℕ → ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ c' in atTop, ∀ x : ℝ,
      designSite c' σs 1 + C * lambdaComb c' * c' ^ (-(1 / 2 : ℝ)) ≤ x →
      x ≤ xiStar + c' ^ (-(2 / 5 : ℝ)) →
      0 < twoGW p c' 1 N (1 / 4) σs (designWidth1 c' η) x := by
  obtain ⟨A, hA0, hA⟩ := twoGW_pos_of_lower p 1 (η₀ := 1 / 4) (by norm_num) le_rfl
  obtain ⟨Sg0, hSg0, hb⟩ := proposition_I_b_sig_lower N hN hη0 hη1 σs
  obtain ⟨C, hC, ha⟩ := proposition_I_a_sig_lower N hN hη0 hη1 σs Sg0 A hA0
  refine ⟨C, hC, ?_⟩
  filter_upwards [hA, hb A, ha, designWidth1_admissible N hN hη0.le hη1 σs, eventually_gt_atTop (0 : ℝ)]
    with c' hAc hbc hac hadm hcpos x hx hxI
  have hsc : 0 < √c' := Real.sqrt_pos.mpr hcpos
  by_cases h1 : x ≤ xiStar + lambdaComb c' * Sg0
  · obtain ⟨hxh, hQ⟩ := hac x hx h1
    exact hAc N σs (designWidth1 c' η) hadm x hxh (lt_of_lt_of_le (by nlinarith) hQ)
  · push Not at h1
    obtain ⟨hxh, hQ⟩ := hbc x h1.le hxI
    exact hAc N σs (designWidth1 c' η) hadm x hxh hQ

/-! ### 2. The designs at fixed sites -/

/-- **Proposition III for the `f = 1` finite modifications at fixed sites `σs`** (`ut:III`; arbitrary sites, widths
`η_* ℓ_k`): there is `C > 0` such that for `c'` large, every cut `N' ≥ N` above the block and every
`x ≥ χ'_1 + C λ c'^{-1/2}` (`χ'_1 = designSite c' σs 1`), `2 g_w(c' x²/3) > 0` for the bumped design.  Region I(a), I(b)
are `proposition_I_a_sig_lower`, `proposition_I_b_sig_lower` with `bumped_regionI_pos`; Region II is
`bumped_regionII_pos`. -/
theorem proposition_III_sig (p : ℕ) (P : RpParams p) (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 < η)
    (hη1 : η ≤ 1 / 4) (σs : ℕ → ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ c' in atTop, ∀ N' : ℕ, N ≤ N' →
      (∀ k : ℕ, 1 ≤ k → chiQuantile c' (k : ℝ) ≤ P.X → k ≤ N') →
      ∀ x : ℝ, designSite c' σs 1 + C * lambdaComb c' * c' ^ (-(1 / 2 : ℝ)) ≤ x →
        0 < twoGW p c' 1 N' (1 / 4) (bumpSigma c' N σs)
          (bumpEps P.bumpData c' N (1 / 4) (designWidth1 c' η)) x := by
  obtain ⟨A, hA0, hA⟩ := bumped_regionI_pos p P 1 le_rfl
  obtain ⟨Sg0, hSg0, hb⟩ := proposition_I_b_sig_lower N hN hη0 hη1 σs
  obtain ⟨C, hC, ha⟩ := proposition_I_a_sig_lower N hN hη0 hη1 σs Sg0 A hA0
  obtain ⟨Cg, hCg, hfam⟩ := designWidth1_family N hη0.le hη1
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ k, 1 ≤ k → k ≤ N → |σs k| ≤ M :=
    ⟨∑ k ∈ Finset.Icc 1 N, |σs k|, fun k hk hkN =>
      Finset.single_le_sum (f := fun j => |σs j|) (fun _ _ => abs_nonneg _)
        (Finset.mem_Icc.mpr ⟨hk, hkN⟩)⟩
  refine ⟨C, hC, ?_⟩
  filter_upwards [hA, hb A, ha, designWidth1_admissible N hN hη0.le hη1 σs,
    bumped_regionII_pos p P 1 N le_rfl hN M Cg, hfam, eventually_gt_atTop (0 : ℝ)]
    with c' hAc hbc hac hadm hII hfamc hcpos N' hNN' hcut x hx
  have hsc : 0 < √c' := Real.sqrt_pos.mpr hcpos
  by_cases h1 : x ≤ xiStar + lambdaComb c' * Sg0
  · obtain ⟨hxh, hQ⟩ := hac x hx h1
    exact hAc N N' σs (designWidth1 c' η) hN hNN' hadm x hxh
      (lt_of_lt_of_le (by nlinarith) hQ)
  · push Not at h1
    by_cases h2 : x ≤ xiStar + c' ^ (-(2 / 5 : ℝ))
    · obtain ⟨hxh, hQ⟩ := hbc x h1.le h2
      exact hAc N N' σs (designWidth1 c' η) hN hNN' hadm x hxh hQ
    · push Not at h2
      exact hII N' σs (designWidth1 c' η) hNN' hcut (fun k hk hkN => hM k hk hkN)
        (fun k hk hkN => hfamc k hk hkN) x h2.le

/-- **Proposition III, form `t ≥ t_f + 1`** for the `f = 1` finite modifications at fixed sites `σs`: for `c'` large,
every cut `N' ≥ N` above the block and all `t = c' x²/3 ≥ t_f + 1`, `t_f = c' χ'_1²/3`, `2 g_w(t) > 0`. -/
theorem proposition_III_sig_t (p : ℕ) (P : RpParams p) (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 < η)
    (hη1 : η ≤ 1 / 4) (σs : ℕ → ℝ) :
    ∀ᶠ c' in atTop, ∀ N' : ℕ, N ≤ N' →
      (∀ k : ℕ, 1 ≤ k → chiQuantile c' (k : ℝ) ≤ P.X → k ≤ N') →
      ∀ x : ℝ, 0 ≤ x → c' * designSite c' σs 1 ^ 2 / 3 + 1 ≤ c' * x ^ 2 / 3 →
        0 < twoGW p c' 1 N' (1 / 4) (bumpSigma c' N σs)
          (bumpEps P.bumpData c' N (1 / 4) (designWidth1 c' η)) x := by
  obtain ⟨C, hC, hI⟩ := proposition_III_sig p P N hN hη0 hη1 σs
  filter_upwards [hI, tForm_gap σs C] with c' hIc htg N' hNN' hcut x hx0 hx
  exact hIc N' hNN' hcut x (htg x hx0 hx)

/-- **Proposition III for the designs `D(N, η_*, d)`** (`σs = designSigma1 d`): the gap form. -/
theorem proposition_III_design (p : ℕ) (P : RpParams p) (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 < η)
    (hη1 : η ≤ 1 / 4) (d : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ c' in atTop, ∀ N' : ℕ, N ≤ N' →
      (∀ k : ℕ, 1 ≤ k → chiQuantile c' (k : ℝ) ≤ P.X → k ≤ N') →
      ∀ x : ℝ, designSite c' (designSigma1 d) 1 + C * lambdaComb c' * c' ^ (-(1 / 2 : ℝ)) ≤ x →
        0 < twoGW p c' 1 N' (1 / 4) (bumpSigma c' N (designSigma1 d))
          (bumpEps P.bumpData c' N (1 / 4) (designWidth1 c' η)) x :=
  proposition_III_sig p P N hN hη0 hη1 (designSigma1 d)

/-- **Proposition III for the designs `D(N, η_*, d)`, form `t ≥ t_f + 1`.** -/
theorem proposition_III_design_t (p : ℕ) (P : RpParams p) (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 < η)
    (hη1 : η ≤ 1 / 4) (d : ℝ) :
    ∀ᶠ c' in atTop, ∀ N' : ℕ, N ≤ N' →
      (∀ k : ℕ, 1 ≤ k → chiQuantile c' (k : ℝ) ≤ P.X → k ≤ N') →
      ∀ x : ℝ, 0 ≤ x → c' * designSite c' (designSigma1 d) 1 ^ 2 / 3 + 1 ≤ c' * x ^ 2 / 3 →
        0 < twoGW p c' 1 N' (1 / 4) (bumpSigma c' N (designSigma1 d))
          (bumpEps P.bumpData c' N (1 / 4) (designWidth1 c' η)) x :=
  proposition_III_sig_t p P N hN hη0 hη1 (designSigma1 d)

/-! ### 3. The statements for a fixed-weight problem -/

/-- At `w = 1` the order-`p` test of weight `prob.w` is the original `twoG`. -/
theorem twoGW_prob_one (prob : FixedWeightProblem) (hw : prob.w = 1) (c' : ℝ) (f N : ℕ) (η₀ : ℝ)
    (σ ε : ℕ → ℝ) (x : ℝ) : twoGW (prob.w - 1) c' f N η₀ σ ε x = twoG c' f N η₀ σ ε x := by
  rw [hw]
  exact twoGW_zero c' f N η₀ σ ε x

/-- **Proposition III** (`ut:III`) for a fixed-weight problem `prob` (`(H_w)`, any `prob.w`): with the bump of
`rpParams (prob.w - 1)`, for `c'` large `g_w = ½(h₀ - 𝓗_w h₀) > 0` on `t ≥ t_f + 1` for the bumped `f = 1` designs at fixed
sites `σs` (width `η_* ℓ_k`, any cut `N' ≥ N` above the block). -/
theorem proposition_III (prob : FixedWeightProblem) (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 < η)
    (hη1 : η ≤ 1 / 4) (σs : ℕ → ℝ) :
    ∀ᶠ c' in atTop, ∀ N' : ℕ, N ≤ N' →
      (∀ k : ℕ, 1 ≤ k → chiQuantile c' (k : ℝ) ≤ (rpParams (prob.w - 1)).X → k ≤ N') →
      ∀ x : ℝ, 0 ≤ x → c' * designSite c' σs 1 ^ 2 / 3 + 1 ≤ c' * x ^ 2 / 3 →
        0 < twoGW (prob.w - 1) c' 1 N' (1 / 4) (bumpSigma c' N σs)
          (bumpEps (rpParams (prob.w - 1)).bumpData c' N (1 / 4) (designWidth1 c' η)) x :=
  proposition_III_sig_t (prob.w - 1) (rpParams (prob.w - 1)) N hN hη0 hη1 σs

/-- **Proposition III, Region II, compact family** (`ut:III`, any `f ≥ 1`): for `c'` large, every member of the compact
family of finite modifications (`|σ_k| ≤ M`, `0 ≤ ε_k ≤ E λ`), every cut `N ≥ N₀` above the block and every `x ≥ ξ_I`,
`Lev^{(f)}(x)/20 ≤ 2 g_w(c' x²/3)` for the bumped design, `p = prob.w - 1`. -/
theorem proposition_III_regionII (prob : FixedWeightProblem) (f N₀ : ℕ) (hf : 1 ≤ f) (hfN₀ : f ≤ N₀)
    (M E : ℝ) :
    ∀ᶠ c' in atTop, ∀ (N : ℕ) (σ ε : ℕ → ℝ), N₀ ≤ N →
      (∀ k : ℕ, 1 ≤ k → chiQuantile c' (k : ℝ) ≤ (rpParams (prob.w - 1)).X → k ≤ N) →
      (∀ k, f ≤ k → k ≤ N₀ → |σ k| ≤ M) →
      (∀ k, f < k → k ≤ N₀ → 0 ≤ ε k ∧ ε k ≤ E * lambdaComb c') →
      ∀ x : ℝ, xiStar + c' ^ (-(2 / 5 : ℝ)) ≤ x →
        1 / 20 * levComb c' f x ≤
          twoGW (prob.w - 1) c' f N (1 / 4) (bumpSigma c' N₀ σ)
            (bumpEps (rpParams (prob.w - 1)).bumpData c' N₀ (1 / 4) ε) x :=
  bumped_regionII (prob.w - 1) (rpParams (prob.w - 1)) f N₀ hf hfN₀ M E

/-! ### 4. Non-vacuity -/

/-- A cut `N' ≥ N` above the block exists for every `c' > 0`. -/
theorem exists_cut_ge {p : ℕ} (P : RpParams p) {c' : ℝ} (hc' : 0 < c') (N : ℕ) :
    ∃ N' : ℕ, N ≤ N' ∧ ∀ k : ℕ, 1 ≤ k → chiQuantile c' (k : ℝ) ≤ P.X → k ≤ N' := by
  obtain ⟨n, hn⟩ := exists_cut P.bumpData hc'
  exact ⟨max N n, le_max_left _ _, fun k hk hkX => (hn k hk hkX).trans (le_max_right _ _)⟩

/-- **Non-vacuity of Proposition III**: for `c'` large the hypotheses of `proposition_III` are satisfiable (a cut above the
block exists), so the conclusion is a positivity statement about actual bumped designs. -/
theorem proposition_III_nonvacuous (prob : FixedWeightProblem) (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 < η)
    (hη1 : η ≤ 1 / 4) (σs : ℕ → ℝ) :
    ∀ᶠ c' in atTop, ∃ N' : ℕ, N ≤ N' ∧
      (∀ k : ℕ, 1 ≤ k → chiQuantile c' (k : ℝ) ≤ (rpParams (prob.w - 1)).X → k ≤ N') ∧
      ∀ x : ℝ, 0 ≤ x → c' * designSite c' σs 1 ^ 2 / 3 + 1 ≤ c' * x ^ 2 / 3 →
        0 < twoGW (prob.w - 1) c' 1 N' (1 / 4) (bumpSigma c' N σs)
          (bumpEps (rpParams (prob.w - 1)).bumpData c' N (1 / 4) (designWidth1 c' η)) x := by
  filter_upwards [proposition_III prob N hN hη0 hη1 σs, eventually_gt_atTop (0 : ℝ)] with c' h hc'
  obtain ⟨N', hNN', hcut⟩ := exists_cut_ge (rpParams (prob.w - 1)) hc' N
  exact ⟨N', hNN', hcut, h N' hNN' hcut⟩

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.bumped_regionI_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bumped_regionI_pos

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.proposition_I_sigW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms proposition_I_sigW

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.proposition_III_sig' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms proposition_III_sig

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.proposition_III_sig_t' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms proposition_III_sig_t

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.proposition_III_design_t' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms proposition_III_design_t

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.proposition_III' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms proposition_III

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.proposition_III_regionII' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms proposition_III_regionII

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.proposition_III_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms proposition_III_nonvacuous

end FormalResearch.ModularBootstrap.Upper.Positivity
