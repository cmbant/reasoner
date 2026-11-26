module

public import FormalResearch.ModularBootstrap.Blowup.SlackFeasible
public import FormalResearch.ModularBootstrap.Blowup.ClarkNormLimit
public import FormalResearch.ModularBootstrap.Blowup.HbNormLimit

/-!
# `bl:norm` for fixed-weight problems at `m₀ = 1, 2` (Langer variable)

Source: `CFT/modular_bootstrap/paper/blowup_limit.tex`, Lemma BL-N (`bl:norm`), `m₀ = 1` (Airy) and
`m₀ = 2` (Clark).  The transported densities `Ψ_n = psiTilde prob c'_n g_n` of tests `g_n` with
normalised vacuum slack `η_n → 0` (`IsSlackFeasible`) satisfy the standing assumptions
`DensitySeq` (`exists_densitySeq`, from `densityHyp_of_slack`), as soon as `c'_n → ∞` and the
thresholds are bounded in the Langer variable: `T_n ≤ Δ_{c'_n}(-K)` for one `K ≥ 0` (the paper's
"`s(T_j)` bounded above"). The abstract layer (`AiryNormLimit`, `ClarkNormLimit`) then gives

* (a) `limsup u_T(n) ≤ a₁` (resp. `z₂(α)`, resp. `t_m` for a general Hermite–Biehler datum), `u_T = chartUT c'_n T_n`;
* (b) if `u_T(n) → a₁` (only `liminf` is used): `Ψ_n → Ai²/((a₁-u)‖·‖₁)` (resp. `g_α/‖g_α‖₁`) locally
  uniformly on `ℂ` and in `L¹(ℝ)`, and the truncated total mass `∫ Re Ψ_n → 0`.

For Clark the prescribed node enters through the data: points `ũ_n → z₁(α)` with
`g_n(Δ_{c'_n}(ũ_n)) ≥ 0`.

The statements are in the transported (`u`-)variable of the Langer chart; the conversion to the
`s`-variable `Φ_j(s) = …` of the paper (with `(T - ξ̄ c')/c'^{1/3}` bookkeeping) is not formalised here.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.Blowup

open FormalResearch.ModularBootstrap Crossing PoissonJensen WeightAxioms TipFront ConcreteBootstrap
  FixedWeightTip FormalResearch.Special FormalResearch.SignUncertainty

/-- The chart radius `A_{c'}² → ∞`. -/
lemma tendsto_chartAC_sq {r_1 : ℝ} (hr1 : 0 < r_1) :
    Tendsto (fun c' : ℝ => chartAC r_1 c' ^ 2) atTop atTop :=
  ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).const_mul_atTop
    (mul_pos two_pos (pow_pos (chartBV_pos hr1) 2))).congr'
      (by filter_upwards [eventually_ge_atTop (0 : ℝ)] with c' hc'; rw [chartAC_sq r_1 c' hc'])

/-- `K ≤ A²` and `T ≤ Δ(-K)` give the interior condition `T < Δ(-A²)` when `K < A²`. -/
lemma interior_of_le_neg {r_1 c' T K : ℝ} (hr1 : 0 < r_1) (hc' : 0 < c') (hK : 0 ≤ K)
    (hKA : K < chartAC r_1 c' ^ 2) (hT : T ≤ virasoroDeltaChart c' (-K)) :
    T < virasoroDeltaChart c' (-(chartAC r_1 c' ^ 2)) := by
  have hanti := virasoroDeltaChart_strictAnti hc'
  have hA2 := chartAC_sq_le_virasoroAC_sq hr1 hc'.le
  have hlt := hanti (a := -(chartAC r_1 c' ^ 2)) (b := -K)
    ⟨by linarith, by linarith [sq_nonneg (chartAC r_1 c')]⟩
    ⟨by linarith, by linarith⟩ (by linarith)
  exact hT.trans_lt hlt

/-- The chart image of a threshold `T ≤ Δ(-K)` satisfies `-K ≤ u_T`. -/
lemma neg_le_chartUT {r_1 c' T K : ℝ} (hr1 : 0 < r_1) (hc' : 0 < c') (hK : 0 ≤ K)
    (hKA : K < chartAC r_1 c' ^ 2) (hlo : virasoroDeltaChart c' (chartAC r_1 c' ^ 2) ≤ T)
    (hT : T ≤ virasoroDeltaChart c' (-K)) : -K ≤ chartUT c' T := by
  have hint := interior_of_le_neg hr1 hc' hK hKA hT
  obtain ⟨hmem, heq⟩ := chartUT_mem_Icc_of_between' hr1 hc' hlo hint.le
  have hanti := virasoroDeltaChart_strictAnti hc'
  have hA2 := chartAC_sq_le_virasoroAC_sq hr1 hc'.le
  by_contra hlt
  push Not at hlt
  have := hanti (a := chartUT c' T) (b := -K)
    ⟨by linarith [hmem.1], by linarith [hmem.2]⟩ ⟨by linarith, by linarith⟩ hlt
  rw [heq] at this
  linarith

/-- The far-lobe mass is nonnegative. -/
lemma deltaLobe_nonneg' {prob : FixedWeightProblem} (D : UniformPropositionPData prob) {c' : ℝ}
    {g : ℝ → ℝ} (hc' : D.c₀ ≤ c') (hM : 0 < prob.cardyNorm (c' / 12) g) :
    0 ≤ deltaLobe prob D.r_1 c' g := by
  have hc'_pos : 0 < c' := D.hc₀_pos.trans_le hc'
  have hΔ_pos : 0 < virasoroDeltaChart c' (chartAC D.r_1 c' ^ 2) :=
    virasoroDeltaChart_pos hc'_pos
      (chart_real_abs_le_virasoro D.hr1_pos hc'_pos (by rw [abs_of_nonneg (sq_nonneg _)]))
  unfold deltaLobe
  exact mul_nonneg (inv_nonneg.mpr hM.le) (intervalIntegral.integral_nonneg hΔ_pos.le
    fun t ht => mul_nonneg (abs_nonneg _) (D.cardyV_nonneg hc' ht.1))

lemma tendsto_max_atTop (N : ℕ) : Tendsto (fun n : ℕ => max n N) atTop atTop :=
  tendsto_atTop_mono (fun n => le_max_left n N) tendsto_id

lemma eventually_unmax {P : ℕ → Prop} (N : ℕ) (h : ∀ᶠ n in atTop, P (max n N)) :
    ∀ᶠ n in atTop, P n := by
  obtain ⟨M, hM⟩ := eventually_atTop.1 h
  refine eventually_atTop.2 ⟨max M N, fun n hn => ?_⟩
  have := hM n (le_trans (le_max_left _ _) hn)
  rwa [max_eq_left (le_trans (le_max_right _ _) hn)] at this

lemma tendsto_unmax {α : Type*} [TopologicalSpace α] {f : ℕ → α} {a : α} (N : ℕ)
    (h : Tendsto (fun n => f (max n N)) atTop (𝓝 a)) : Tendsto f atTop (𝓝 a) := by
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [max_eq_left hn]

/-- **The standing assumptions of `bl:norm` hold for slack-feasible tests with bounded threshold.**

For tests `g_n` with vacuum slack `η_n → 0` at `c'_n → ∞`, with `T_n ≤ Δ_{c'_n}(-K)` (bounded
`s(T_n)`), the transported densities, re-indexed along `max n N` (they agree with the original ones
for `n ≥ N`), form a `DensitySeq` with `R_n = A_{c'_n}²`, `ς_n = generalSigma`, `δ_n = δ_lobe + η_n`,
the thresholds are bounded below by `-K`, and the sign of `g_n(Δ u)` is that of `Re Ψ_n(u)` on the
disc. -/
theorem exists_densitySeq {prob : FixedWeightProblem} (D : UniformPropositionPData prob)
    {c' T η : ℕ → ℝ} {g : ℕ → ℝ → ℝ} {Q : ℕ → Prop} (hQ : ∀ᶠ n in atTop, Q n)
    (hc' : Tendsto c' atTop atTop) (hη : Tendsto η atTop (𝓝 0))
    (hη0 : ∀ᶠ n in atTop, 0 ≤ η n)
    (hsf : ∀ᶠ n in atTop, IsSlackFeasible prob (c' n / 12) (T n) (η n) (g n))
    (hK : ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop, T n ≤ virasoroDeltaChart (c' n) (-K)) :
    ∃ (C₀ : ℝ) (N : ℕ),
      DensitySeq C₀ (fun n => chartAC D.r_1 (c' (max n N)) ^ 2)
        (fun n => generalSigma D.p_e (c' (max n N)))
        (fun n => deltaLobe prob D.r_1 (c' (max n N)) (g (max n N)) + η (max n N))
        (fun n => psiTilde prob (c' (max n N)) (g (max n N)))
        (fun n => chartUT (c' (max n N)) (T (max n N))) ∧
      (∃ x₀ : ℝ, ∀ n, x₀ ≤ chartUT (c' (max n N)) (T (max n N))) ∧
      (∀ n (u : ℝ), |u| ≤ chartAC D.r_1 (c' (max n N)) ^ 2 →
        (0 ≤ g (max n N) (virasoroDeltaChart (c' (max n N)) u) ↔
          0 ≤ (psiTilde prob (c' (max n N)) (g (max n N)) (u : ℂ)).re)) ∧
      ∀ n, Q (max n N) := by
  obtain ⟨c_S, C₀, C_gap, κ_gap, hcS, hC₀, hCg, hκ, key⟩ := densityHyp_of_slack D
  obtain ⟨K, hK0, hKev⟩ := hK
  have hc₀pos := D.hc₀_pos
  have hη4 : ∀ᶠ n in atTop, η n ≤ 1 / 4 := hη.eventually (eventually_le_nhds (by norm_num))
  have hall : ∀ᶠ n in atTop, (c_S ≤ c' n ∧ 0 ≤ η n ∧ η n ≤ 1 / 4 ∧
      IsSlackFeasible prob (c' n / 12) (T n) (η n) (g n) ∧ T n ≤ virasoroDeltaChart (c' n) (-K) ∧
      K < chartAC D.r_1 (c' n) ^ 2) ∧ Q n :=
    ((hc'.eventually (eventually_ge_atTop c_S)).and <| hη0.and <| hη4.and <| hsf.and <| hKev.and <|
      ((tendsto_chartAC_sq D.hr1_pos).comp hc').eventually (eventually_gt_atTop K)).and hQ
  obtain ⟨N, hN⟩ := eventually_atTop.1 hall
  have hmax := tendsto_max_atTop N
  have hpt : ∀ n, c_S ≤ c' (max n N) ∧ 0 ≤ η (max n N) ∧ η (max n N) ≤ 1 / 4 ∧
      IsSlackFeasible prob (c' (max n N) / 12) (T (max n N)) (η (max n N)) (g (max n N)) ∧
      T (max n N) ≤ virasoroDeltaChart (c' (max n N)) (-K) ∧
      K < chartAC D.r_1 (c' (max n N)) ^ 2 := fun n => (hN _ (le_max_right n N)).1
  have hc'pos : ∀ n, 0 < c' (max n N) := fun n => hc₀pos.trans_le (hcS.trans (hpt n).1)
  have hint : ∀ n, T (max n N) < virasoroDeltaChart (c' (max n N))
      (-(chartAC D.r_1 (c' (max n N)) ^ 2)) := fun n =>
    interior_of_le_neg D.hr1_pos (hc'pos n) hK0 (hpt n).2.2.2.2.2 (hpt n).2.2.2.2.1
  have hkey := fun n => key (hpt n).1 (hpt n).2.1 (hpt n).2.2.1 (hpt n).2.2.2.1 (hint n)
  have hc'm : Tendsto (fun n => c' (max n N)) atTop atTop := hc'.comp hmax
  refine ⟨C₀, N, ⟨hC₀, (tendsto_chartAC_sq D.hr1_pos).comp hc'm, ?_, ?_, ?_, fun n => (hkey n).2.1⟩,
    ⟨-K, fun n => ?_⟩, fun n => (hkey n).2.2.2, fun n => (hN _ (le_max_right n N)).2⟩
  · filter_upwards [hc'm.eventually (eventually_ge_atTop (1 : ℝ))] with n hn
    exact generalSigma_nonneg D.hp_e_nn hn
  · exact (generalSigma_tendsto_zero D.p_e).comp hc'm
  · have h1 : Tendsto (fun n => -κ_gap * c' (max n N)) atTop atBot :=
      hc'm.const_mul_atTop_of_neg (by linarith)
    have h2 : Tendsto (fun n => C_gap * Real.exp (-κ_gap * c' (max n N))) atTop (𝓝 0) := by
      simpa only [mul_zero, Function.comp] using (Real.tendsto_exp_atBot.comp h1).const_mul C_gap
    have h3 : Tendsto (fun n => deltaLobe prob D.r_1 (c' (max n N)) (g (max n N))) atTop (𝓝 0) :=
      squeeze_zero (fun n => deltaLobe_nonneg' D (hcS.trans (hpt n).1)
        (hpt n).2.2.2.1.2.1) (fun n => (hkey n).1) h2
    simpa using h3.add (hη.comp hmax)
  · exact neg_le_chartUT D.hr1_pos (hc'pos n) hK0 (hpt n).2.2.2.2.2 (hkey n).2.2.1.le
      (hpt n).2.2.2.2.1

lemma tendstoUniformlyOn_unmax {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {s : Set ℂ} (N : ℕ)
    (h : TendstoUniformlyOn (fun n => F (max n N)) f atTop s) : TendstoUniformlyOn F f atTop s := by
  refine h.congr ?_
  filter_upwards [eventually_ge_atTop N] with n hn x _
  simp only [max_eq_left hn]

/-- **`bl:norm`, `m₀ = 1` (Airy), for fixed-weight problems.**  Tests `g_n` with vacuum slack
`η_n → 0` at `c'_n → ∞` and `T_n ≤ Δ_{c'_n}(-K)` (the paper's "`s(T_n)` bounded above").
(a) `limsup u_T(n) ≤ a₁`, where `u_T(n) = chartUT c'_n T_n`.
(b) if `liminf u_T(n) ≥ a₁`: `u_T(n) → a₁`, and the transported densities `psiTilde prob c'_n g_n`
converge to `Ai²/((a₁ - u)‖·‖₁)` locally uniformly on `ℂ` and in `L¹(ℝ)` (extended by `0` outside
`[-A_n², A_n²]`), and `∫_{-A_n²}^{A_n²} Re Ψ_n → 0`. -/
theorem airy_blnorm {prob : FixedWeightProblem} (D : UniformPropositionPData prob)
    {c' T η : ℕ → ℝ} {g : ℕ → ℝ → ℝ}
    (hc' : Tendsto c' atTop atTop) (hη : Tendsto η atTop (𝓝 0))
    (hη0 : ∀ᶠ n in atTop, 0 ≤ η n)
    (hsf : ∀ᶠ n in atTop, IsSlackFeasible prob (c' n / 12) (T n) (η n) (g n))
    (hK : ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop, T n ≤ virasoroDeltaChart (c' n) (-K)) :
    (∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, chartUT (c' n) (T n) ≤ airyZero 1 + ε) ∧
    ((∀ x < airyZero 1, ∀ᶠ n in atTop, x ≤ chartUT (c' n) (T n)) →
      Tendsto (fun n => chartUT (c' n) (T n)) atTop (𝓝 (airyZero 1)) ∧
      (∀ m : ℕ, TendstoUniformlyOn (fun n => psiTilde prob (c' n) (g n)) airyProfile atTop
        (closedBall (0 : ℂ) ((m : ℝ) + 1))) ∧
      Tendsto (fun n => ∫ x : ℝ, ‖(Icc (-(chartAC D.r_1 (c' n) ^ 2)) (chartAC D.r_1 (c' n) ^ 2)).indicator
        (fun x : ℝ => psiTilde prob (c' n) (g n) (x : ℂ)) x - airyProfile (x : ℂ)‖) atTop (𝓝 0) ∧
      Tendsto (fun n => ∫ x in (-(chartAC D.r_1 (c' n) ^ 2))..(chartAC D.r_1 (c' n) ^ 2),
        (psiTilde prob (c' n) (g n) (x : ℂ)).re) atTop (𝓝 0)) := by
  obtain ⟨C₀, N, S, hbd, -, -⟩ := exists_densitySeq D (Q := fun _ => True)
    (Eventually.of_forall fun _ => trivial) hc' hη hη0 hsf hK
  have hmax := tendsto_max_atTop N
  refine ⟨fun ε hε => eventually_unmax N (airy_threshold_le S hbd ε hε), fun huT => ?_⟩
  have huT' : ∀ x < airyZero 1, ∀ᶠ n in atTop,
      x ≤ chartUT (c' (max n N)) (T (max n N)) := fun x hx => hmax.eventually (huT x hx)
  exact ⟨tendsto_unmax N (airy_threshold_tendsto S hbd huT'),
    fun m => tendstoUniformlyOn_unmax N (airy_norm_limit S hbd huT' m),
    tendsto_unmax N (airy_norm_limit_l1 S hbd huT'),
    tendsto_unmax N (airy_norm_limit_integral S hbd huT')⟩

/-- **`bl:norm`, `m₀ = 2` (Clark), for fixed-weight problems.**  As `airy_blnorm`, with the prescribed
node: points `ũ_n → z₁(α)` with `g_n(Δ_{c'_n}(ũ_n)) ≥ 0` (eventually), and `sin α ≠ 0`.  The limit
profile is `g_α/‖g_α‖₁` and the terminal node is `z₂(α)`. -/
theorem clark_blnorm {prob : FixedWeightProblem} (D : UniformPropositionPData prob) {α : ℝ}
    (hα : Real.sin α ≠ 0)
    {c' T η : ℕ → ℝ} {g : ℕ → ℝ → ℝ}
    (hc' : Tendsto c' atTop atTop) (hη : Tendsto η atTop (𝓝 0))
    (hη0 : ∀ᶠ n in atTop, 0 ≤ η n)
    (hsf : ∀ᶠ n in atTop, IsSlackFeasible prob (c' n / 12) (T n) (η n) (g n))
    (hK : ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop, T n ≤ virasoroDeltaChart (c' n) (-K))
    (hnode : ∃ ũ : ℕ → ℝ, Tendsto ũ atTop (𝓝 (clarkNode α 1)) ∧
      ∀ᶠ n in atTop, 0 ≤ g n (virasoroDeltaChart (c' n) (ũ n))) :
    (∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, chartUT (c' n) (T n) ≤ clarkNode α 2 + ε) ∧
    ((∀ x < clarkNode α 2, ∀ᶠ n in atTop, x ≤ chartUT (c' n) (T n)) →
      Tendsto (fun n => chartUT (c' n) (T n)) atTop (𝓝 (clarkNode α 2)) ∧
      (∀ m : ℕ, TendstoUniformlyOn (fun n => psiTilde prob (c' n) (g n)) (clarkProfile α) atTop
        (closedBall (0 : ℂ) ((m : ℝ) + 1))) ∧
      Tendsto (fun n => ∫ x : ℝ, ‖(Icc (-(chartAC D.r_1 (c' n) ^ 2)) (chartAC D.r_1 (c' n) ^ 2)).indicator
        (fun x : ℝ => psiTilde prob (c' n) (g n) (x : ℂ)) x - clarkProfile α (x : ℂ)‖) atTop (𝓝 0) ∧
      Tendsto (fun n => ∫ x in (-(chartAC D.r_1 (c' n) ^ 2))..(chartAC D.r_1 (c' n) ^ 2),
        (psiTilde prob (c' n) (g n) (x : ℂ)).re) atTop (𝓝 0)) := by
  obtain ⟨ũ, hũ, hũg⟩ := hnode
  have hũR : ∀ᶠ n in atTop, |ũ n| ≤ chartAC D.r_1 (c' n) ^ 2 := by
    have hb : ∀ᶠ n in atTop, |ũ n| ≤ |clarkNode α 1| + 1 := by
      have := hũ.abs.eventually (eventually_le_nhds (show |clarkNode α 1| < |clarkNode α 1| + 1 by
        linarith))
      exact this
    filter_upwards [hb, ((tendsto_chartAC_sq D.hr1_pos).comp hc').eventually
      (eventually_ge_atTop (|clarkNode α 1| + 1))] with n h1 h2 using h1.trans h2
  obtain ⟨C₀, N, S, hbd, hsign, hQ⟩ := exists_densitySeq D
    (Q := fun n => |ũ n| ≤ chartAC D.r_1 (c' n) ^ 2 ∧ 0 ≤ g n (virasoroDeltaChart (c' n) (ũ n)))
    (hũR.and hũg) hc' hη hη0 hsf hK
  have hmax := tendsto_max_atTop N
  have hn : ClarkNodeData α (fun n => psiTilde prob (c' (max n N)) (g (max n N))) :=
    ⟨fun n => ũ (max n N), hũ.comp hmax, fun n => (hsign n _ (hQ n).1).1 (hQ n).2⟩
  refine ⟨fun ε hε => eventually_unmax N (clark_threshold_le hα S hbd hn ε hε), fun huT => ?_⟩
  have huT' : ∀ x < clarkNode α 2, ∀ᶠ n in atTop,
      x ≤ chartUT (c' (max n N)) (T (max n N)) := fun x hx => hmax.eventually (huT x hx)
  exact ⟨tendsto_unmax N (clark_threshold_tendsto hα S hbd hn huT'),
    fun m => tendstoUniformlyOn_unmax N (clark_norm_limit hα S hbd hn huT' m),
    tendsto_unmax N (clark_norm_limit_l1 hα S hbd hn huT'),
    tendsto_unmax N (clark_norm_limit_integral hα S hbd hn huT')⟩

/-- info: 'FormalResearch.ModularBootstrap.Blowup.airy_blnorm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airy_blnorm

/-- info: 'FormalResearch.ModularBootstrap.Blowup.clark_blnorm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms clark_blnorm

/-- **`bl:norm`, general `m₀`, for fixed-weight problems.**  As `clark_blnorm`, for a Hermite–Biehler
datum `D'` with prescribed nodes `S \ {t_m}`: for every node `t_i` points `ũ_{n,i} → t_i` with
`g_n(Δ_{c'_n}(ũ_{n,i})) ≥ 0` (eventually). -/
theorem hb_blnorm {prob : FixedWeightProblem} (D : UniformPropositionPData prob)
    (H : HermiteBiehlerData)
    {c' T η : ℕ → ℝ} {g : ℕ → ℝ → ℝ}
    (hc' : Tendsto c' atTop atTop) (hη : Tendsto η atTop (𝓝 0))
    (hη0 : ∀ᶠ n in atTop, 0 ≤ η n)
    (hsf : ∀ᶠ n in atTop, IsSlackFeasible prob (c' n / 12) (T n) (η n) (g n))
    (hK : ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop, T n ≤ virasoroDeltaChart (c' n) (-K))
    (hnode : ∀ i : HbNodes H, ∃ ũ : ℕ → ℝ, Tendsto ũ atTop (𝓝 i.1) ∧
      ∀ᶠ n in atTop, 0 ≤ g n (virasoroDeltaChart (c' n) (ũ n))) :
    (∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, chartUT (c' n) (T n) ≤ H.tm + ε) ∧
    ((∀ x < H.tm, ∀ᶠ n in atTop, x ≤ chartUT (c' n) (T n)) →
      Tendsto (fun n => chartUT (c' n) (T n)) atTop (𝓝 H.tm) ∧
      (∀ m : ℕ, TendstoUniformlyOn (fun n => psiTilde prob (c' n) (g n)) (normProfile H.G) atTop
        (closedBall (0 : ℂ) ((m : ℝ) + 1))) ∧
      Tendsto (fun n => ∫ x : ℝ, ‖(Icc (-(chartAC D.r_1 (c' n) ^ 2)) (chartAC D.r_1 (c' n) ^ 2)).indicator
        (fun x : ℝ => psiTilde prob (c' n) (g n) (x : ℂ)) x - normProfile H.G (x : ℂ)‖) atTop
        (𝓝 0) ∧
      Tendsto (fun n => ∫ x in (-(chartAC D.r_1 (c' n) ^ 2))..(chartAC D.r_1 (c' n) ^ 2),
        (psiTilde prob (c' n) (g n) (x : ℂ)).re) atTop (𝓝 0)) := by
  have : Finite (HbNodes H) :=
    Finite.of_injective (fun t : HbNodes H => (⟨t.1, t.2.1⟩ : H.S))
      (fun a b (h : (⟨a.1, a.2.1⟩ : H.S) = ⟨b.1, b.2.1⟩) =>
        Subtype.ext (Subtype.mk.inj h))
  choose ũ hũ hũg using hnode
  have hũR : ∀ᶠ n in atTop, ∀ i, |ũ i n| ≤ chartAC D.r_1 (c' n) ^ 2 := by
    rw [Filter.eventually_all]
    intro i
    have hb : ∀ᶠ n in atTop, |ũ i n| ≤ |i.1| + 1 :=
      (hũ i).abs.eventually (eventually_le_nhds (show |i.1| < |i.1| + 1 by linarith))
    filter_upwards [hb, ((tendsto_chartAC_sq D.hr1_pos).comp hc').eventually
      (eventually_ge_atTop (|i.1| + 1))] with n h1 h2 using h1.trans h2
  have hũg' : ∀ᶠ n in atTop, ∀ i, 0 ≤ g n (virasoroDeltaChart (c' n) (ũ i n)) :=
    Filter.eventually_all.2 hũg
  obtain ⟨C₀, N, S, hbd, hsign, hQ⟩ := exists_densitySeq D
    (Q := fun n => (∀ i, |ũ i n| ≤ chartAC D.r_1 (c' n) ^ 2) ∧
      ∀ i, 0 ≤ g n (virasoroDeltaChart (c' n) (ũ i n)))
    (hũR.and hũg') hc' hη hη0 hsf hK
  have hmax := tendsto_max_atTop N
  have hn : ∀ i : HbNodes H, ∃ ũ' : ℕ → ℝ, Tendsto ũ' atTop (𝓝 i.1) ∧
      ∀ n, 0 ≤ (psiTilde prob (c' (max n N)) (g (max n N)) (ũ' n : ℂ)).re :=
    fun i => ⟨fun n => ũ i (max n N), (hũ i).comp hmax,
      fun n => (hsign n _ ((hQ n).1 i)).1 ((hQ n).2 i)⟩
  refine ⟨fun ε hε => eventually_unmax N (hb_threshold_le H S hbd hn ε hε), fun huT => ?_⟩
  have huT' : ∀ x < H.tm, ∀ᶠ n in atTop,
      x ≤ chartUT (c' (max n N)) (T (max n N)) := fun x hx => hmax.eventually (huT x hx)
  exact ⟨tendsto_unmax N (hb_threshold_tendsto H S hbd huT' hn),
    fun m => tendstoUniformlyOn_unmax N (hb_norm_limit H S hbd huT' hn m),
    tendsto_unmax N (hb_norm_limit_l1 H S hbd huT' hn),
    tendsto_unmax N (hb_norm_limit_integral H S hbd huT' hn)⟩

/-- info: 'FormalResearch.ModularBootstrap.Blowup.hb_blnorm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hb_blnorm

end FormalResearch.ModularBootstrap.Blowup
