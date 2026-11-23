module

public import FormalResearch.ModularBootstrap.Upper.Assembly.PsiWindow
public import FormalResearch.ModularBootstrap.Upper.Assembly.ProfWinDef
public import FormalResearch.ModularBootstrap.Upper.Rigidity.Wiring
public import FormalResearch.ModularBootstrap.Upper.Window.AiryProdPositive

/-!
# Property `sr:P` for the Virasoro designs: `DesignPropertyP S.μS designClass`

Source: `CFT/modular_bootstrap/paper/spectral_rigidity.tex` (Property `sr:P`, (P1)-(P4)),
`upper_transfer.tex` (`ut:V`, `ut:R`, `ut:III`, `ut:Vac`).

* `designWin N hη d`: the abstract `Window` (`Upper.Rigidity.Window`) of the design `D(N, η_*, d)`:
  `W = Re W_D` (`designWinW`), `u_f = a_1 - d`, `W ≥ 0` on `u ≤ u_f` (sign structure of the Airy
  product, `airyWindowProd_re_pos`, needs `η_* > 0`), and the Airy quadrature `∫ W = Σ W(a_n)/Ai'(a_n)²`
  (`lemma_V_hasSum`).
* `designClass`: the class `𝒟` of the windows `D(N, η_*, d)` with `N ≥ 1`, `0 < η_* ≤ 1/4`, `d ∈ ℝ`.
  **Restrictions of the class**: `f = 1` (no omitted sites), the only displaced site is the first one,
  `η_* > 0` (Lemma `R`, Proposition `I`), `η_* ≤ 1/4` (`η₀ = 1/4`), `N` fixed along the sequence
  (the explicit `N`-dependence of `ut:P`(a) is not covered).
* `combDesignData_of_eventually`: comb data `(P1)`-`(P4)` from statements `∀ᶠ c in atTop` about a
  family of functionals `g_c`, for every `CrossingSequence` (the finitely many bad `c_j` are replaced by
  `g_j = 0`).
* `combDesignData_design`: `CombDesignData S (designWin N hη d)` for every Virasoro crossing sequence.
* **`designPropertyP_virasoro`**: `DesignPropertyP S.μS designClass` for every `S : CrossingSequence
  virasoroProblem`, proved from the Lean ingredients (`design1_k7_membership_vacuum`,
  `proposition_I_design_t`, `lemma_W_measure`, `lemma_ID`, `proposition_V_i`, `designG_nonneg`).

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Assembly

open FormalResearch.Special FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.Upper.Rigidity FormalResearch.ModularBootstrap.Upper.Window
  FormalResearch.ModularBootstrap.Upper.Positivity FormalResearch.ModularBootstrap.Upper.Design

/-! ### The window `D(N, η_*, d)` as an abstract `Window` -/

lemma designWidthU_ne_zero (N : ℕ) {η : ℝ} (hη : 0 < η) {k : ℕ} (hk : 1 < k) :
    designWidthU N η k ≠ 0 := by
  unfold designWidthU
  have := gapWKB_pos (by omega : 1 ≤ k)
  have h : (if k ≤ N then η else (1 / 4 : ℝ)) ≠ 0 := by
    split_ifs
    · exact hη.ne'
    · norm_num
  exact mul_ne_zero h this.ne'

lemma designWinW_nonneg_of_le (N : ℕ) {η : ℝ} (hη : 0 < η) (d : ℝ) {u : ℝ}
    (hu : u ≤ airyZero 1 - d) : 0 ≤ designWinW N η d u :=
  profWre_nonneg_of_le (designSiteU N) (designWidthU N η) (design_tail_hypothesis N η) d
    (fun _ hk => designWidthU_ne_zero N hη hk) hu

lemma continuous_designWinW (N : ℕ) (η d : ℝ) : Continuous (designWinW N η d) :=
  continuous_profWre (designSiteU N) (designWidthU N η) (design_tail_hypothesis N η) d

lemma integrable_designWinW (N : ℕ) (η d : ℝ) : Integrable (designWinW N η d) :=
  integrable_profWre (designSiteU N) (designWidthU N η) (design_tail_hypothesis N η) d

lemma designWinW_hasSum (N : ℕ) (η d : ℝ) :
    HasSum (fun i : ℕ => designWinW N η d (airyNode i) * airyNodeWeight i)
      (∫ u, designWinW N η d u) :=
  profWre_hasSum (designSiteU N) (designWidthU N η) (design_tail_hypothesis N η) d

/-- The abstract window `W_D` of the design `D(N, η_*, d)`, `η_* > 0`: the profile window `profWin` of the
profile `(designSiteU N, designWidthU N η)`. -/
noncomputable def designWin (N : ℕ) {η : ℝ} (hη : 0 < η) (d : ℝ) : Window :=
  profWin (designSiteU N) (designWidthU N η) (design_tail_hypothesis N η)
    (fun _ hk => designWidthU_ne_zero N hη hk) d

lemma designWin_V (N : ℕ) {η : ℝ} (hη : 0 < η) (d : ℝ) :
    (designWin N hη d).V = windowIntegralVD N η d := rfl

/-- The class `𝒟` of the Virasoro designs `D(N, η_*, d)`: `N ≥ 1`, `0 < η_* ≤ 1/4`, `d ∈ ℝ`. -/
def designClass : Set Window :=
  {D | ∃ (N : ℕ) (η d : ℝ) (hη : 0 < η), 1 ≤ N ∧ η ≤ 1 / 4 ∧ D = designWin N hη d}

lemma designWin_mem {N : ℕ} {η : ℝ} (hη : 0 < η) (hN : 1 ≤ N) (hη1 : η ≤ 1 / 4) (d : ℝ) :
    designWin N hη d ∈ designClass := ⟨N, η, d, hη, hN, hη1, rfl⟩

/-! ### Comb data from statements for large `c` -/

/-- The statements about `g_c` for large `c` that make up `CombDesignData`. -/
structure EventualCombData (D : Window) where
  g : ℝ → ℝ → ℝ
  scale : ℝ → ℝ
  tf : ℝ → ℝ
  good : ∀ᶠ c in atTop, 0 < c ∧ 0 < scale c ∧ TestClass virasoroProblem (c / 12) (g c) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
      |g c t| ≤ C * Real.exp (-4 * π * √(c / 12 * t) - π * √(3 * t / c))) ∧
    0 ≤ tf c + 1 ∧ ∀ t : ℝ, tf c + 1 ≤ t → 0 ≤ g c t
  theta : Tendsto (fun c => uAiry c (tf c + 1)) atTop (𝓝 D.uF)
  window : ∀ R : ℝ, 0 ≤ R → ∀ ε : ℝ, 0 < ε → ∀ᶠ c in atTop, ∀ u ∈ Icc (-R) R,
    |scale c * psiAiry virasoroProblem c (g c) u - D.W u| ≤ ε
  limsup : ∀ ε : ℝ, 0 < ε → ∀ᶠ c in atTop,
    ∫ u, scale c * psiAiry virasoroProblem c (g c) u ≤ D.V + ε

open Classical in
/-- `(P1)`-`(P4)` for the crossing sequence `S` from the statements for large `c`: the finitely many
`j` with `c_j` outside the good set get `g_j = 0`. -/
noncomputable def EventualCombData.toComb {D : Window} (E : EventualCombData D)
    (S : CrossingSequence virasoroProblem) : CombDesignData S D := by
  let good : ℝ → Prop := fun c => 0 < c ∧ 0 < E.scale c ∧ TestClass virasoroProblem (c / 12) (E.g c) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
      |E.g c t| ≤ C * Real.exp (-4 * π * √(c / 12 * t) - π * √(3 * t / c))) ∧
    0 ≤ E.tf c + 1 ∧ ∀ t : ℝ, E.tf c + 1 ≤ t → 0 ≤ E.g c t
  have hev : ∀ᶠ j in atTop, good (S.c j) := S.tendsto_c.eventually E.good
  exact {
    g := fun j => if good (S.c j) then E.g (S.c j) else fun _ => 0
    scale := fun j => if good (S.c j) then E.scale (S.c j) else 1
    tf := fun j => if good (S.c j) then E.tf (S.c j) else 0
    scale_pos := fun j => by
      by_cases h : good (S.c j)
      · simp only [h, ite_true]; exact h.2.1
      · simp [h]
    testClass := fun j => by
      by_cases h : good (S.c j)
      · simp only [h, ite_true]; exact h.2.2.1
      · simp only [h, ite_false]
        simpa using (thermalDiff_mem_TestClass virasoroProblem (S.shift_le j)
          (by norm_num : (0 : ℝ) < 1 / 2)).smul 0
    decay := fun j => by
      by_cases h : good (S.c j)
      · simp only [h, ite_true]; exact h.2.2.2.1
      · simp only [h, ite_false]; exact ⟨0, le_rfl, fun t _ => by simp⟩
    tf_nonneg := fun j => by
      by_cases h : good (S.c j)
      · simp only [h, ite_true]; exact h.2.2.2.2.1
      · simp [h]
    g_nonneg := fun j t ht => by
      by_cases h : good (S.c j)
      · simp only [h, ite_true] at ht ⊢; exact h.2.2.2.2.2 t ht
      · simp [h]
    theta_tendsto := by
      refine ((E.theta.comp S.tendsto_c)).congr' ?_
      filter_upwards [hev] with j hj
      simp [hj]
    window_limit := by
      rw [Metric.tendstoLocallyUniformly_iff]
      intro ε hε x
      refine ⟨Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith), ?_⟩
      have h1 := E.window (|x| + 1) (by positivity) (ε / 2) (half_pos hε)
      have h2 := S.tendsto_c.eventually h1
      filter_upwards [hev, h2] with j hj h2j y hy
      have hy' : y ∈ Icc (-(|x| + 1)) (|x| + 1) :=
        ⟨by linarith [hy.1, neg_abs_le x], by linarith [hy.2, le_abs_self x]⟩
      have := h2j y hy'
      simp only [hj, ite_true]
      rw [Real.dist_eq, abs_sub_comm]
      linarith
    limsup_le := fun ε hε => by
      have h1 := S.tendsto_c.eventually (E.limsup ε hε)
      filter_upwards [hev, h1] with j hj h1j
      simp only [hj, ite_true]
      exact h1j }


/-- The eventual comb data of any window `D` whose window function is the Airy window `sigWinW N η σs` of
the `f = 1` finite modification with offsets `σs` (first site `σs 1`, sites `2..N` arbitrary, so displaced
sites and a first site anywhere on the real line are allowed) and whose first site is `u_f = -κ σ_1`. -/
noncomputable def sigEventual (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 4)
    (σs : ℕ → ℝ) (D : Window) (hW : D.W = sigWinW N η σs)
    (hF : D.uF = -(kappaAiry * σs 1)) : EventualCombData D where
  g := sigG N η σs
  scale := psiScale
  tf := sigTf σs
  good := by
    filter_upwards [sigGood_eventually N hN hη.le hη1 σs, sigG_nonneg N hN hη hη1 σs]
      with c hgood hpos
    refine ⟨hpos.1, psiScale_pos hpos.1, hgood.testClass, hgood.decay, ?_,
      fun t ht => (hpos.2 t ht).le⟩
    have := hpos.1
    unfold sigTf; positivity
  theta := by rw [hF]; exact uAiry_sigTf σs
  window := fun R hR ε hε => by
    rw [hW]; exact sig_psi_uniform N hN hη hη1 σs hR hε
  limsup := fun ε hε => by
    have hV : D.V = windowIntegralSig N η σs := by
      unfold Window.V windowIntegralSig; rw [hW]; rfl
    rw [hV]; exact sig_psi_limsup N hN hη.le hη1 σs hε

lemma designWin_W_eq_sig (N : ℕ) {η : ℝ} (hη : 0 < η) (d : ℝ) :
    (designWin N hη d).W = sigWinW N η (designSigma1 d) := by
  rw [← designWinW_eq_sig]; rfl

lemma designWin_uF_eq_sig (N : ℕ) {η : ℝ} (hη : 0 < η) (d : ℝ) :
    (designWin N hη d).uF = -(kappaAiry * designSigma1 d 1) := by
  have hκ := kappaAiry_pos
  have hσ1def : kappaAiry * designSigma1 d 1 = |airyZero 1| + d := by
    rw [designSigma1_one]; field_simp
  rw [hσ1def, abs_of_neg (airyZero_neg 1)]
  show airyZero 1 - d = _
  ring

/-- The eventual comb data of the design `D(N, η_*, d)`. -/
noncomputable def designEventual (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 4)
    (d : ℝ) : EventualCombData (designWin N hη d) :=
  sigEventual N hN hη hη1 (designSigma1 d) (designWin N hη d) (designWin_W_eq_sig N hη d)
    (designWin_uF_eq_sig N hη d)

/-- **`(P1)`-`(P4)` for the designs**: `CombDesignData S (designWin N hη d)` for every Virasoro
crossing sequence `S`. -/
noncomputable def combDesignData_design (S : CrossingSequence virasoroProblem) (N : ℕ) (hN : 1 ≤ N)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 4) (d : ℝ) : CombDesignData S (designWin N hη d) :=
  (designEventual N hN hη hη1 d).toComb S

/-- **Property `sr:P` for the Virasoro designs**: every window `D(N, η_*, d)` of `designClass` carries a
design test for the spectral measures `μ_S` of every Virasoro crossing sequence. -/
theorem designPropertyP_virasoro (S : CrossingSequence virasoroProblem) :
    DesignPropertyP S.μS designClass := by
  refine designPropertyP_of_comb S fun D hD => ?_
  obtain ⟨N, η, d, hη, hN, hη1, rfl⟩ := hD
  exact ⟨combDesignData_design S N hN hη hη1 d⟩

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.designWinW_hasSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms designWinW_hasSum

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.designPropertyP_virasoro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms designPropertyP_virasoro

end FormalResearch.ModularBootstrap.Upper.Assembly
