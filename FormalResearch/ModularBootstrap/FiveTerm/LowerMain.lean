module

public import FormalResearch.ModularBootstrap.FiveTerm.LowerMainDefs
public import FormalResearch.ModularBootstrap.FiveTerm.LowerPhaseSharp
public import FormalResearch.ModularBootstrap.FiveTerm.LowerLangerBridge
public import FormalResearch.ModularBootstrap.FiveTerm.LowerChartMain
public import FormalResearch.ModularBootstrap.FiveTerm.LowerSign
public import FormalResearch.ModularBootstrap.FiveTerm.LowerCorL
public import FormalResearch.ModularBootstrap.ConcreteBootstrap.QuadratureBounds
public import FormalResearch.ModularBootstrap.Contour.VirasoroScaleChoice

/-!
# Skeleton of `cts:lower-main`: the sharp log-free lower bound from its open lemmas (FIVE-L, Theorem C9)

Source: `CFT/modular_bootstrap/paper/constant_term_slit_strip.tex`, Theorem C9 (`cts:lower-main`) and its
one-pass log-free proof, with Lemma C6 (`cts:cauchy-dual`), Lemma C7 (`cts:rosc-uncond`), Lemma C7b (`ctl:pass2`),
Lemma C8 (`cts:boas`), Proposition C1 (`cts:langer`).

* `LowerMainInputs prob c0 γ0` (a structure) holds the remaining **open TeX lemmas as used in the proof of C9**,
  as fields over concrete objects (`lowerF`, `lowerH`, `lowerPNodes`, `lowerEta`, `lowerBand`, `lowerSc`, ...): the
  shifted Airy chart `φ_c` (`LowerChart`, `cts:cauchy-dual`(1)), the combined dual identity (`LowerCombined`,
  `cts:rosc-uncond`(4)), and Boas positivity (`LowerBoas`, `cts:boas`).  `ctl:freeze` is used inside `cts:boas`, and
  `K_edge^ε` and `cts:dual-id` are consumed inside `cts:rosc-uncond`(4) and `cts:boas`.
* Already proved facts are **not** fields: `LowerPrelim prob` packages `rem:corL`(b) and the sign/range facts of
  `lemmaQ_part3` (at Virasoro: `lowerPrelim_virasoro` in `LowerMainVirasoro`), `LowerLangerPhase` is discharged by
  `lowerLangerPhase_holds`, `LowerPass2` is discharged at Virasoro by `lowerPass2_of_chart` (`LowerPass2Main`), and
  `LowerEdgeHankel`, `LowerBoasResidue`, `LowerDyadic`, `LowerCorL`, `LowerSign` are used by the field discharges.
* `nodes_lower` (private): the first Airy node alone gives `P_R(H) ≥ κ(ũ_T - φ_c(a_1))/(2 Ai'(a_1)²)`.
* `lowerPhase_of_inputs` (**the skeleton**): `LowerMainInputs prob c0 γ0` and `c0 < 0` give `C ≥ 0` with
  `LowerPhaseStatementSharp prob c0 γ0 C` (log-free `cts:lower-main` phase bound).  It includes the `ũ ↔ τ` bridge
  (`lowerUstar_phase`: the chart point `u_*` with phase `τ_* - K c^{-2}` is
  `a_1 - (c_0/c_*) c^{-1/3} - γ_0 a_1 c^{-1} + β K c^{-4/3}`).

The Virasoro corollary (`spinless_lower_of_inputs`, first display of `cts:lower-main`) is in `LowerMainVirasoro`.
Proved modulo the named structure `LowerMainInputs`; the constants are existential.  Non-vacuity of the fields is not
checked here: a field is a statement about the stated objects and must be true for the real chart.
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set Complex Metric intervalIntegral
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.Special FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.Crossing FormalResearch.ModularBootstrap.ConcreteBootstrap
open FormalResearch.ModularBootstrap.FixedWeightTip FormalResearch.ModularBootstrap.Contour

noncomputable section

/-! ### Objects of the proof of `cts:lower-main` (shared definitions live in `LowerMainDefs`) -/

/-! ### The open lemmas, as fields -/

open Classical in
/-- **`cts:rosc-uncond` (4)**, the combined dual identity at every good radius on the band
`T ≤ Δ(-virasoroAThr)`:
`|P_R(H) + g_vac/2π + ∫_{v_0}^∞ w̃_R Ψ̃(-v')[1 + 2 s_c] dv'| ≤ C (c⁻¹ η_R + c^{-4/3})`. -/
def LowerCombined (prob : FixedWeightProblem) (Gout : ℂ → ℂ) (c1 : ℝ) (phi : ℝ → ℂ → ℂ)
    (uhat : ℝ → ℝ → ℝ) : Prop :=
  ∃ cc C : ℝ, ∀ c : ℝ, cc ≤ c → ∀ (T : ℝ) (g : ℝ → ℝ), prob.IsWeaklyFeasible (c / 12) T g →
    LowerViolator phi c T → T ≤ virasoroDeltaChart c (-virasoroAThr) →
    ∀ (N : ℕ) (R : ℝ), LowerGoodCircle N R → LowerRadiusRange c1 c R →
      |lowerPNodes N (lowerH prob phi c g R) + prob.gVac (c / 12) g / (2 * π) +
          lowerBand prob Gout phi uhat c R g| ≤
        C * (c ^ (-1 : ℝ) * lowerEta prob phi c g R + c ^ (-(4 / 3 : ℝ)))

/-- **`ctl:pass2` (`cts:rosc-uncond` (1))**: unconditional good Airy circle `R ∈ [c_1² c^{2/3}, 4 c_1² c^{2/3}]`
with `η(R) ≤ C c^{-1/3}` on the band `T ≤ Δ(-virasoroAThr)`. -/
def LowerPass2 (prob : FixedWeightProblem) (c1 : ℝ) (phi : ℝ → ℂ → ℂ) : Prop :=
  ∃ cc C : ℝ, ∀ c : ℝ, cc ≤ c → ∀ (T : ℝ) (g : ℝ → ℝ),
    prob.IsWeaklyFeasible (c / 12) T g → LowerViolator phi c T →
    T ≤ virasoroDeltaChart c (-virasoroAThr) →
    ∃ (N : ℕ) (R : ℝ), LowerGoodCircle N R ∧ LowerRadiusRange c1 c R ∧
      lowerEta prob phi c g R ≤ C * c ^ (-(1 / 3 : ℝ))

/-- **`cts:boas`** (local strip Boas positivity): the band integral is `≥ -C c^{-4/3}`
at every good radius on the band `T ≤ Δ(-virasoroAThr)`. -/
def LowerBoas (prob : FixedWeightProblem) (Gout : ℂ → ℂ) (c1 : ℝ) (phi : ℝ → ℂ → ℂ)
    (uhat : ℝ → ℝ → ℝ) : Prop :=
  ∃ cc C : ℝ, ∀ c : ℝ, cc ≤ c → ∀ (T : ℝ) (g : ℝ → ℝ), prob.IsWeaklyFeasible (c / 12) T g →
    LowerViolator phi c T → T ≤ virasoroDeltaChart c (-virasoroAThr) →
    ∀ (N : ℕ) (R : ℝ), LowerGoodCircle N R → LowerRadiusRange c1 c R →
      -(C * c ^ (-(4 / 3 : ℝ))) ≤ lowerBand prob Gout phi uhat c R g

/-- **The remaining open input of `cts:lower-main`.** `cts:langer` (`LowerLangerPhase`), `ctl:pass2` (`LowerPass2`),
`cts:cauchy-dual` (1) / `cts:phic-exp` (`LowerChart`), and `cts:boas` (`LowerBoas` at `virasoroPhi`, `virasoroUhat`, `virasoroC1`)
are now discharged unconditionally; the remaining field is `cts:rosc-uncond` (4) (`LowerCombined`). -/
structure LowerMainInputs (prob : FixedWeightProblem) where
  combined : LowerCombined prob Gout virasoroC1 virasoroPhi virasoroUhat

/-- The chart point of the reference phase minus `K c^{-2}`:
`u_* = a_1 - (c_0/c_*) c^{-1/3} - γ_0 a_1 c^{-1} + β K c^{-4/3}`. -/
def lowerUstar (c0 γ0 K c : ℝ) : ℝ :=
  airyZero 1 - c0 / cStar * c ^ (-(1 / 3 : ℝ)) - γ0 * airyZero 1 * c ^ (-1 : ℝ) +
    betaTip * K * c ^ (-(4 / 3 : ℝ))

private lemma rpow_third_pows {c : ℝ} (hc : 0 < c) :
    c ^ (-(2 / 3 : ℝ)) = (c ^ (-(1 / 3 : ℝ))) ^ 2 ∧ c ^ (-1 : ℝ) = (c ^ (-(1 / 3 : ℝ))) ^ 3 ∧
    c ^ (-(4 / 3 : ℝ)) = (c ^ (-(1 / 3 : ℝ))) ^ 4 ∧ c ^ (-2 : ℝ) = (c ^ (-(1 / 3 : ℝ))) ^ 6 ∧
    c ^ (-(5 / 3 : ℝ)) = (c ^ (-(1 / 3 : ℝ))) ^ 5 ∧ c ^ (2 / 3 : ℝ) = ((c ^ (-(1 / 3 : ℝ))) ^ 2)⁻¹ := by
  have key : ∀ (k : ℕ) (e : ℝ), e = -(1 / 3 : ℝ) * k → c ^ e = (c ^ (-(1 / 3 : ℝ))) ^ k := by
    intro k e he
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le, he]
  refine ⟨key 2 (-(2 / 3)) (by norm_num), key 3 (-1) (by norm_num), key 4 (-(4 / 3)) (by norm_num),
    key 6 (-2) (by norm_num), key 5 (-(5 / 3)) (by norm_num), ?_⟩
  rw [← key 2 (-(2 / 3)) (by norm_num), ← Real.rpow_neg hc.le]; norm_num

/-- The phase of the chart point `u_*` is `τ_*(c) - K c^{-2}` (exact algebra). -/
lemma lowerUstar_phase (c0 γ0 K : ℝ) {c : ℝ} (hc : 0 < c) :
    -lowerUstar c0 γ0 K c / (betaTip * c ^ (2 / 3 : ℝ)) =
      tauStar c0 γ0 c - K * c ^ (-2 : ℝ) := by
  obtain ⟨h2, h3, h4, h6, h5, h23⟩ := rpow_third_pows hc
  have hp : 0 < c ^ (-(1 / 3 : ℝ)) := Real.rpow_pos_of_pos hc _
  have hβ := betaTip_pos
  have hξ := xiStar_pos
  have ha : airyZero 1 < 0 := airyZero_neg 1
  have hcs : cStar = 2 * xiStar / (3 * betaTip) := rfl
  unfold lowerUstar tauStar sLanger
  rw [h2, h3, h4, h6, h5, h23, hcs, abs_of_neg ha]
  set p := c ^ (-(1 / 3 : ℝ))
  field_simp
  ring

/-- `u_* = a_1 + c^{-1/3} b(c)` with `b(c) → -c_0/c_*`. -/
private lemma ustar_eq_bracket (c0 γ0 K : ℝ) {c : ℝ} (hc : 0 < c) :
    lowerUstar c0 γ0 K c = airyZero 1 + c ^ (-(1 / 3 : ℝ)) *
      (-c0 / cStar - γ0 * airyZero 1 * c ^ (-(2 / 3) : ℝ) + betaTip * K * c ^ (-1 : ℝ)) := by
  obtain ⟨h2, h3, h4, -, -, -⟩ := rpow_third_pows hc
  unfold lowerUstar
  rw [h2, h3, h4] at *
  ring

/-- For `c_0 < 0` and `c` large, `a_1 < u_* < 0` and `u_* ≥ -(|a_1| + 1)`; `u_* → a_1`. -/
lemma lowerUstar_eventually {c0 : ℝ} (hc0 : c0 < 0) (γ0 K : ℝ) :
    ∀ᶠ c : ℝ in atTop, airyZero 1 < lowerUstar c0 γ0 K c ∧ lowerUstar c0 γ0 K c < 0 ∧
      -(|airyZero 1| + 1) ≤ lowerUstar c0 γ0 K c := by
  have hcs := cStar_pos
  have ha := airyZero_neg 1
  have hb : Tendsto (fun c : ℝ => -c0 / cStar - γ0 * airyZero 1 * c ^ (-(2 / 3) : ℝ) +
      betaTip * K * c ^ (-1 : ℝ)) atTop (𝓝 (-c0 / cStar - γ0 * airyZero 1 * 0 +
        betaTip * K * 0)) := by
    refine (tendsto_const_nhds.sub ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).const_mul
      _)).add ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1)).const_mul _)
  have hlim : -c0 / cStar - γ0 * airyZero 1 * 0 + betaTip * K * 0 = -c0 / cStar := by ring
  rw [hlim] at hb
  have hpos : 0 < -c0 / cStar := div_pos (by linarith) hcs
  have hcm : Tendsto (fun c : ℝ => c ^ (-(1 / 3) : ℝ)) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  have hprod := hcm.mul hb
  rw [zero_mul] at hprod
  filter_upwards [hb.eventually (lt_mem_nhds (half_lt_self hpos)),
    hprod.eventually (gt_mem_nhds (show (0 : ℝ) < -airyZero 1 / 2 by linarith)),
    eventually_gt_atTop (0 : ℝ)] with c hb1 hp2 hc
  rw [ustar_eq_bracket c0 γ0 K hc]
  have hp : 0 < c ^ (-(1 / 3 : ℝ)) := Real.rpow_pos_of_pos hc _
  have hb0 : 0 < (-c0 / cStar - γ0 * airyZero 1 * c ^ (-(2 / 3) : ℝ) +
      betaTip * K * c ^ (-1 : ℝ)) := by linarith
  refine ⟨by nlinarith [mul_pos hp hb0], by linarith, ?_⟩
  rw [abs_of_neg ha]
  nlinarith [mul_pos hp hb0]

/-- **Already-proved facts about `Ψ̃` at a violating test** (not fields): for `c ≥ c_P` and every weakly feasible `g`
with `T < Δ(a_1)`: `a_1 < ũ_T`, `ũ_T` lies in the Langer disc with `Δ(ũ_T) = T`; `Ψ̃` is real and `≥ 0` on the real
axis below `ũ_T`; and the slope bound `Re Ψ̃(a_1 + θ x̃) ≥ 2κ(1-θ) x̃` of `rem:corL`(b).
At Virasoro they are `corL_virasoro`, `lemmaQ_part3` (`lowerPrelim_virasoro`). -/
def LowerPrelim (prob : FixedWeightProblem) : Prop :=
  ∃ cP κ : ℝ, 0 < κ ∧ ∀ c : ℝ, cP ≤ c → ∀ (T : ℝ) (g : ℝ → ℝ), prob.IsWeaklyFeasible (c / 12) T g →
    T < virasoroDeltaChart c (airyZero 1) →
      (airyZero 1 < virasoroUT c T ∧
        virasoroUT c T ∈ Icc (-(virasoroAC c ^ 2)) (virasoroAC c ^ 2) ∧
        virasoroDeltaChart c (virasoroUT c T) = T) ∧
      (∀ x : ℝ, |x| ≤ virasoroAC c ^ 2 → (psiTilde prob c g (x : ℂ)).im = 0) ∧
      (∀ x : ℝ, |x| ≤ virasoroAC c ^ 2 → x ≤ virasoroUT c T → 0 ≤ (psiTilde prob c g (x : ℂ)).re) ∧
      (∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → 2 * κ * (1 - θ) * (virasoroUT c T - airyZero 1) ≤
        (psiTilde prob c g ((airyZero 1 + θ * (virasoroUT c T - airyZero 1) : ℝ) : ℂ)).re)

private lemma nodes_ge (prob : FixedWeightProblem) (phi : ℝ → ℂ → ℂ) (c : ℝ) (g : ℝ → ℝ) (R : ℝ)
    {N : ℕ} (hN : 1 ≤ N) {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ n : ℕ, 2 ≤ n → n ≤ N → 0 ≤ (lowerF prob phi c g (airyZero n : ℂ)).re)
    (hf1 : L ≤ (lowerF prob phi c g (airyZero 1 : ℂ)).re) (hW : 1 / 2 ≤ lowerW6 R (airyZero 1)) :
    (1 / 2) * L / airyAi' (airyZero 1) ^ 2 ≤ lowerPNodes N (lowerH prob phi c g R) := by
  have hAi : 0 < airyAi' (airyZero 1) ^ 2 := by
    have := airyAi'_first_pos; positivity
  unfold lowerPNodes
  have h1 : (1 / 2) * L / airyAi' (airyZero 1) ^ 2 ≤
      lowerH prob phi c g R (airyZero 1) / airyAi' (airyZero 1) ^ 2 := by
    apply div_le_div_of_nonneg_right _ hAi.le
    unfold lowerH
    nlinarith [mul_le_mul hW hf1 hL (by linarith : (0 : ℝ) ≤ lowerW6 R (airyZero 1))]
  refine h1.trans ?_
  refine Finset.single_le_sum (f := fun n => lowerH prob phi c g R (airyZero n) / airyAi' (airyZero n) ^ 2)
    (fun n hn => ?_) (Finset.mem_Icc.2 ⟨le_rfl, hN⟩)
  obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.1 hn
  apply div_nonneg _ (sq_nonneg _)
  unfold lowerH
  have hW6 : 0 ≤ lowerW6 R (airyZero n) := sq_nonneg _
  by_cases h1n : n = 1
  · subst h1n
    exact mul_nonneg hW6 (hL.trans hf1)
  · exact mul_nonneg hW6 (hf n (by omega) hnN)

/-- Node lower bound for a violating test: the first node alone gives
`P_R(H) ≥ κ (ũ_T - φ_c(a_1)) / (2 Ai'(a_1)²)`. -/
private lemma nodes_lower (prob : FixedWeightProblem) (phi : ℝ → ℂ → ℂ) (c1 c : ℝ) (g : ℝ → ℝ)
    (T κ : ℝ) {N : ℕ} {R : ℝ}
    (hκ : 0 < κ)
    (hρ : ∃ ρ : ℝ, lowerRmax c1 c < ρ ∧ DifferentiableOn ℂ (phi c) (ball 0 ρ))
    (him : ∀ x : ℝ, |x| ≤ lowerRmax c1 c → (phi c (x : ℂ)).im = 0)
    (hclose : ∀ u : ℂ, ‖u‖ ≤ lowerRmax c1 c → ‖phi c u - u‖ ≤ 1 ∧ ‖deriv (phi c) u - 1‖ ≤ 1 / 2)
    (hA : lowerRmax c1 c + 1 ≤ virasoroAC c ^ 2)
    (hq1 : airyZero 1 < virasoroUT c T)
    (hq0 : ∀ x : ℝ, |x| ≤ virasoroAC c ^ 2 → (psiTilde prob c g (x : ℂ)).im = 0)
    (hq3 : ∀ x : ℝ, |x| ≤ virasoroAC c ^ 2 → x ≤ virasoroUT c T → 0 ≤ (psiTilde prob c g (x : ℂ)).re)
    (hq4 : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → 2 * κ * (1 - θ) * (virasoroUT c T - airyZero 1) ≤
        (psiTilde prob c g ((airyZero 1 + θ * (virasoroUT c T - airyZero 1) : ℝ) : ℂ)).re)
    (hviol : (phi c (airyZero 1 : ℂ)).re < virasoroUT c T)
    (hge : airyZero 1 ≤ (phi c (airyZero 1 : ℂ)).re)
    (hgood : ∀ n : ℕ, 1 ≤ n → (n ≤ N ↔ |airyZero n| < R)) (hR : R ≤ lowerRmax c1 c)
    (hRa : 2 * |airyZero 1| ≤ R) :
    (1 / 2) * (κ * (virasoroUT c T - (phi c (airyZero 1 : ℂ)).re)) / airyAi' (airyZero 1) ^ 2 ≤
      lowerPNodes N (lowerH prob phi c g R) := by
  obtain ⟨ρ, hρR, hdiff⟩ := hρ
  set Rm := lowerRmax c1 c with hRm
  have ha1 : airyZero 1 < 0 := airyZero_neg 1
  have hRm0 : 0 ≤ Rm := by linarith [abs_nonneg (airyZero 1)]
  have hN : 1 ≤ N := by
    rw [hgood 1 le_rfl]
    rw [abs_of_neg ha1]
    have := abs_of_neg ha1
    linarith [abs_nonneg (airyZero 1)]
  set uT := virasoroUT c T with huT
  set φR : ℝ → ℝ := fun x => (phi c (x : ℂ)).re with hφR
  have hdiffAt : ∀ x : ℝ, |x| ≤ Rm → DifferentiableAt ℂ (phi c) (x : ℂ) := by
    intro x hx
    refine hdiff.differentiableAt (isOpen_ball.mem_nhds ?_)
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; linarith
  have hderiv : ∀ x : ℝ, |x| ≤ Rm → HasDerivAt φR (deriv (phi c) (x : ℂ)).re x := fun x hx =>
    (hdiffAt x hx).hasDerivAt.real_of_complex
  have hnorm : ∀ x : ℝ, |x| ≤ Rm → ‖(x : ℂ)‖ ≤ Rm := fun x hx => by
    rwa [Complex.norm_real, Real.norm_eq_abs]
  have hder_re : ∀ x : ℝ, |x| ≤ Rm → 1 / 2 ≤ (deriv (phi c) (x : ℂ)).re := by
    intro x hx
    have h := (hclose (x : ℂ) (hnorm x hx)).2
    have h2 := (abs_le.1 ((Complex.abs_re_le_norm _).trans h)).1
    simp only [Complex.sub_re, Complex.one_re] at h2
    linarith
  have hmono : StrictMonoOn φR (Icc (-Rm) Rm) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _) ?_ ?_
    · intro x hx
      exact (hderiv x (abs_le.2 hx)).continuousAt.continuousWithinAt
    · intro x hx
      have hx' : x ∈ Icc (-Rm) Rm := interior_subset hx
      rw [(hderiv x (abs_le.2 hx')).deriv]
      linarith [hder_re x (abs_le.2 hx')]
  have hphi : ∀ x : ℝ, |x| ≤ Rm → phi c (x : ℂ) = ((φR x : ℝ) : ℂ) := fun x hx =>
    Complex.ext (by simp [φR]) (by simp [him x hx])
  have hφA : ∀ x : ℝ, |x| ≤ Rm → |φR x| ≤ virasoroAC c ^ 2 := by
    intro x hx
    have h1 := (hclose (x : ℂ) (hnorm x hx)).1
    have h2 : |φR x - x| ≤ 1 := by
      have := (Complex.abs_re_le_norm (phi c (x : ℂ) - x)).trans h1
      simpa [φR] using this
    have h3 : |φR x| ≤ |x| + 1 := by
      calc |φR x| = |(φR x - x) + x| := by ring_nf
        _ ≤ |φR x - x| + |x| := abs_add_le _ _
        _ ≤ |x| + 1 := by linarith
    linarith
  have hFre : ∀ x : ℝ, |x| ≤ Rm →
      (lowerF prob phi c g (x : ℂ)).re =
        (psiTilde prob c g ((φR x : ℝ) : ℂ)).re * (deriv (phi c) (x : ℂ)).re := by
    intro x hx
    unfold lowerF
    rw [hphi x hx, Complex.mul_re, hq0 _ (hφA x hx), zero_mul, sub_zero]
  have han : ∀ n : ℕ, 1 ≤ n → n ≤ N → |airyZero n| ≤ Rm := fun n hn hnN =>
    ((hgood n hn).1 hnN).le.trans hR
  have hma : ∀ n : ℕ, 1 ≤ n → n ≤ N → airyZero n ∈ Icc (-Rm) Rm := fun n hn hnN =>
    abs_le.1 (han n hn hnN)
  have ha1m : airyZero 1 ∈ Icc (-Rm) Rm := hma 1 le_rfl hN
  have hfn : ∀ n : ℕ, 2 ≤ n → n ≤ N → 0 ≤ (lowerF prob phi c g (airyZero n : ℂ)).re := by
    intro n hn hnN
    have hxn := han n (by omega) hnN
    rw [hFre _ hxn]
    have hle : φR (airyZero n) ≤ φR (airyZero 1) :=
      (hmono.monotoneOn (hma n (by omega) hnN) ha1m
        (airyZero_lt_of_lt le_rfl (by omega : 1 < n)).le)
    have hle2 : φR (airyZero n) ≤ uT := by
      have : φR (airyZero 1) = (phi c (airyZero 1 : ℂ)).re := rfl
      linarith
    exact mul_nonneg (hq3 _ (hφA _ hxn) hle2) (by linarith [hder_re _ hxn])
  -- first node
  have hx1 := han 1 le_rfl hN
  have hslope := hq4 ((φR (airyZero 1) - airyZero 1) / (uT - airyZero 1))
    (div_nonneg (by simpa [φR] using sub_nonneg.2 hge) (by linarith))
    ((div_le_one (by linarith)).2 (by simp only [φR]; linarith))
  have hxu : uT - airyZero 1 ≠ 0 := by linarith
  have hid : airyZero 1 + (φR (airyZero 1) - airyZero 1) / (uT - airyZero 1) * (uT - airyZero 1) =
      φR (airyZero 1) := by field_simp; ring
  rw [hid] at hslope
  have hcoef : 2 * κ * (1 - (φR (airyZero 1) - airyZero 1) / (uT - airyZero 1)) * (uT - airyZero 1) =
      2 * κ * (uT - φR (airyZero 1)) := by field_simp; ring
  rw [hcoef] at hslope
  have hf1 : κ * (uT - φR (airyZero 1)) ≤ (lowerF prob phi c g (airyZero 1 : ℂ)).re := by
    rw [hFre _ hx1]
    have hd := hder_re _ hx1
    have hpos : 0 ≤ 2 * κ * (uT - φR (airyZero 1)) := by
      have : φR (airyZero 1) < uT := hviol
      positivity
    nlinarith
  have hL : 0 ≤ κ * (uT - φR (airyZero 1)) := by
    have : φR (airyZero 1) < uT := hviol
    positivity
  have hW : 1 / 2 ≤ lowerW6 R (airyZero 1) := by
    unfold lowerW6
    have hR0 : 0 < R := by
      have := abs_pos.2 ha1.ne
      linarith
    have ht : (airyZero 1 / R) ^ 12 ≤ 1 / 4096 := by
      have h1 : |airyZero 1 / R| ≤ 1 / 2 := by
        rw [abs_div, abs_of_pos hR0, div_le_iff₀ hR0]; linarith
      have h2 : (airyZero 1 / R) ^ 12 ≤ (1 / 2) ^ 12 := by
        rw [← (by decide : Even 12).pow_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) h1 12
      linarith [h2, (by norm_num : ((1 : ℝ) / 2) ^ 12 = 1 / 4096)]
    have h0 : 0 ≤ (airyZero 1 / R) ^ 12 := by positivity
    nlinarith
  exact nodes_ge prob phi c g R hN hL hfn hf1 hW

private lemma rpow_neg_one_mul {c : ℝ} (hc : 0 < c) :
    c ^ (-1 : ℝ) * c ^ (-(1 / 3 : ℝ)) = c ^ (-(4 / 3 : ℝ)) := by
  rw [← Real.rpow_add hc]; norm_num

/-- **One-pass upper bound on the node sum in `cts:lower-main`.**  For every violating test there is a good radius with
`P_R(H) + g_vac/2π ≤ C_0 c^{-4/3}`, `C_0` independent of the test and of `K`. -/
private lemma lower_pass_bound {prob : FixedWeightProblem}
    (h : LowerMainInputs prob) (hpass : LowerPass2 prob virasoroC1 virasoroPhi)
    (hboas : LowerBoas prob Gout virasoroC1 virasoroPhi virasoroUhat) :
    ∃ cc C₀ : ℝ, ∀ c : ℝ, cc ≤ c → ∀ (T : ℝ) (g : ℝ → ℝ), prob.IsWeaklyFeasible (c / 12) T g →
      LowerViolator virasoroPhi c T → T ≤ virasoroDeltaChart c (-virasoroAThr) →
      ∃ (N : ℕ) (R : ℝ), LowerGoodCircle N R ∧ LowerRadiusRange virasoroC1 c R ∧
        lowerPNodes N (lowerH prob virasoroPhi c g R) + prob.gVac (c / 12) g / (2 * π) ≤
          C₀ * c ^ (-(4 / 3 : ℝ)) := by
  obtain ⟨cc4, C4, h4⟩ := h.combined
  obtain ⟨cc2, Cp, hp2⟩ := hpass
  obtain ⟨cc8, C8, h8⟩ := hboas
  set C4' := max C4 0 with hC4'
  set Cp' := max Cp 0 with hCp'
  set C8' := max C8 0 with hC8'
  have hC40 : 0 ≤ C4' := le_max_right _ _
  refine ⟨max (max cc4 cc2) (max cc8 1), C4' * (Cp' + 1) + C8', ?_⟩
  intro c hc T g hg hviol hT_hi
  have hc1 : 1 ≤ c := (le_max_right _ _).trans ((le_max_right _ _).trans hc)
  have hc0 : 0 < c := by linarith
  have hcc4 : cc4 ≤ c := (le_max_left _ _).trans ((le_max_left _ _).trans hc)
  have hcc2 : cc2 ≤ c := (le_max_right _ _).trans ((le_max_left _ _).trans hc)
  have hcc8 : cc8 ≤ c := (le_max_left _ _).trans ((le_max_right _ _).trans hc)
  have hm1 : 0 ≤ c ^ (-1 : ℝ) := Real.rpow_nonneg hc0.le _
  have hd0 : 0 ≤ c ^ (-(4 / 3 : ℝ)) := Real.rpow_nonneg hc0.le _
  obtain ⟨N, R, hgood, hrange, hη⟩ := hp2 c hcc2 T g hg hviol hT_hi
  have hR0 : 0 ≤ R := by
    have : 0 ≤ lowerRmin virasoroC1 c := by unfold lowerRmin; positivity
    linarith [hrange.1]
  refine ⟨N, R, hgood, hrange, ?_⟩
  have hP2 := h4 c hcc4 T g hg hviol hT_hi N R hgood hrange
  have hB2 := h8 c hcc8 T g hg hviol hT_hi N R hgood hrange
  have habs2 := (abs_le.1 hP2).2
  have hη0 : 0 ≤ lowerEta prob virasoroPhi c g R :=
    intervalIntegral.integral_nonneg (by positivity) (fun θ _ =>
      div_nonneg (mul_nonneg hR0 (add_nonneg (norm_nonneg _) (norm_nonneg _))) (airyEnv_pos _).le)
  have hE0 := mul_nonneg hm1 hη0
  have hηb : c ^ (-1 : ℝ) * lowerEta prob virasoroPhi c g R ≤ Cp' * c ^ (-(4 / 3 : ℝ)) := by
    calc c ^ (-1 : ℝ) * lowerEta prob virasoroPhi c g R
        ≤ c ^ (-1 : ℝ) * (Cp * c ^ (-(1 / 3 : ℝ))) := mul_le_mul_of_nonneg_left hη hm1
      _ = Cp * (c ^ (-1 : ℝ) * c ^ (-(1 / 3 : ℝ))) := by ring
      _ = Cp * c ^ (-(4 / 3 : ℝ)) := by rw [rpow_neg_one_mul hc0]
      _ ≤ Cp' * c ^ (-(4 / 3 : ℝ)) := mul_le_mul_of_nonneg_right (le_max_left _ _) hd0
  have hS : C4 * (c ^ (-1 : ℝ) * lowerEta prob virasoroPhi c g R + c ^ (-(4 / 3 : ℝ))) ≤
      C4' * ((Cp' + 1) * c ^ (-(4 / 3 : ℝ))) := by
    have hS0 : 0 ≤ c ^ (-1 : ℝ) * lowerEta prob virasoroPhi c g R + c ^ (-(4 / 3 : ℝ)) := by linarith
    calc _ ≤ C4' * (c ^ (-1 : ℝ) * lowerEta prob virasoroPhi c g R + c ^ (-(4 / 3 : ℝ))) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hS0
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hC40
  have hC8b : C8 * c ^ (-(4 / 3 : ℝ)) ≤ C8' * c ^ (-(4 / 3 : ℝ)) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hd0
  nlinarith [hS, hC8b, hB2, habs2]

private lemma ge_bracket_eventually {c0 : ℝ} (hc0 : c0 < 0) (γ0 Cφ : ℝ) :
    ∀ᶠ c : ℝ in atTop, 0 < -c0 / cStar - γ0 * airyZero 1 * c ^ (-(2 / 3) : ℝ) - Cφ * c ^ (-1 : ℝ) := by
  have hcs := cStar_pos
  have hb : Tendsto (fun c : ℝ => -c0 / cStar - γ0 * airyZero 1 * c ^ (-(2 / 3) : ℝ) -
      Cφ * c ^ (-1 : ℝ)) atTop (𝓝 (-c0 / cStar - γ0 * airyZero 1 * 0 - Cφ * 0)) :=
    (tendsto_const_nhds.sub ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).const_mul _)).sub
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1)).const_mul _)
  have hlim : -c0 / cStar - γ0 * airyZero 1 * 0 - Cφ * 0 = -c0 / cStar := by ring
  rw [hlim] at hb
  exact hb.eventually (lt_mem_nhds (div_pos (by linarith) hcs))

private lemma lowerPhase_claim_delta_le {prob : FixedWeightProblem} {C₀ K κ L₀ Cφ c T u A2 : ℝ}
    {g : ℝ → ℝ}
    (hκ : 0 < κ) (hc0 : 0 < c)
    (hL₀ : L₀ = κ / (2 * airyAi' (airyZero 1) ^ 2)) (hL₀pos : 0 < L₀)
    (hβK : betaTip * K = max C₀ 0 / L₀ + Cφ + betaTip)
    (hu : u = lowerUstar c0Star gamma0 K c) (hu1 : airyZero 1 < u) (hu3 : -(|airyZero 1| + 1) ≤ u)
    (hbr : 0 < -c0Star / cStar - gamma0 * airyZero 1 * c ^ (-(2 / 3) : ℝ) - Cφ * c ^ (-1 : ℝ))
    (hφ1 : Cφ * c ^ (-(1 / 3 : ℝ)) ≤ 1) (hφ2 : Cφ * c ^ (-1 : ℝ) ≤ 1 / 2)
    (hA2 : A2 = virasoroAC c ^ 2) (hRA : lowerRmax virasoroC1 c + 1 ≤ A2)
    (hRa : 2 * |airyZero 1| ≤ virasoroC1 ^ 2 * c ^ (2 / 3 : ℝ))
    (hAmem : ∀ x : ℝ, -(|airyZero 1| + 1) ≤ x → x ≤ 0 → x ∈ Icc (-A2) A2)
    (hsA : StrictAntiOn (virasoroDeltaChart c) (Icc (-A2) A2))
    (hu_mem : u ∈ Icc (-A2) A2) (ha1_mem : airyZero 1 ∈ Icc (-A2) A2)
    (hg : prob.IsWeaklyFeasible (c / 12) T g)
    (hprel_c : ∀ T g, prob.IsWeaklyFeasible (c / 12) T g → T < virasoroDeltaChart c (airyZero 1) →
      (airyZero 1 < virasoroUT c T ∧
        virasoroUT c T ∈ Icc (-(virasoroAC c ^ 2)) (virasoroAC c ^ 2) ∧
        virasoroDeltaChart c (virasoroUT c T) = T) ∧
      (∀ x : ℝ, |x| ≤ virasoroAC c ^ 2 → (psiTilde prob c g (x : ℂ)).im = 0) ∧
      (∀ x : ℝ, |x| ≤ virasoroAC c ^ 2 → x ≤ virasoroUT c T → 0 ≤ (psiTilde prob c g (x : ℂ)).re) ∧
      (∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → 2 * κ * (1 - θ) * (virasoroUT c T - airyZero 1) ≤
        (psiTilde prob c g ((airyZero 1 + θ * (virasoroUT c T - airyZero 1) : ℝ) : ℂ)).re))
    (hch_c : (∃ ρ : ℝ, lowerRmax virasoroC1 c < ρ ∧ DifferentiableOn ℂ (virasoroPhi c) (ball 0 ρ)) ∧
      (∀ x : ℝ, |x| ≤ lowerRmax virasoroC1 c → (virasoroPhi c (x : ℂ)).im = 0) ∧
      (∀ w : ℂ, ‖w‖ ≤ lowerRmax virasoroC1 c →
        ‖virasoroPhi c w - w‖ ≤ Cφ * c ^ (-(1 / 3 : ℝ)) ∧ ‖deriv (virasoroPhi c) w - 1‖ ≤ Cφ * c ^ (-1 : ℝ)) ∧
      (∀ x : ℝ, |x| ≤ lowerRmax virasoroC1 c → virasoroUhat c (virasoroPhi c (x : ℂ)).re = x) ∧
      |(virasoroPhi c (airyZero 1 : ℂ)).re -
          (airyZero 1 - c0Star / cStar * c ^ (-(1 / 3 : ℝ)) - gamma0 * airyZero 1 * c ^ (-1 : ℝ))| ≤
        Cφ * c ^ (-(4 / 3 : ℝ)))
    (hpass_c : ∀ T g, prob.IsWeaklyFeasible (c / 12) T g → LowerViolator virasoroPhi c T →
      T ≤ virasoroDeltaChart c (-virasoroAThr) →
      ∃ N R, LowerGoodCircle N R ∧ LowerRadiusRange virasoroC1 c R ∧
        lowerPNodes N (lowerH prob virasoroPhi c g R) + prob.gVac (c / 12) g / (2 * π) ≤
          C₀ * c ^ (-(4 / 3 : ℝ))) :
    virasoroDeltaChart c u ≤ T := by
  by_contra hT
  have hT' : T < virasoroDeltaChart c u := not_le.1 hT
  have hTa : T < virasoroDeltaChart c (airyZero 1) := hT'.trans (hsA ha1_mem hu_mem hu1)
  obtain ⟨⟨hq1, hq2, hq2'⟩, hq0, hq3, hq4⟩ := hprel_c T g hg hTa
  set uT := virasoroUT c T with huT
  have hlt : u < uT := by
    by_contra hle
    have := hsA.antitoneOn (hA2 ▸ hq2) hu_mem (not_lt.1 hle)
    linarith
  obtain ⟨⟨ρ, hρ, hdiff⟩, him, hcl, -, hexp⟩ := hch_c
  have hclose : ∀ w : ℂ, ‖w‖ ≤ lowerRmax virasoroC1 c → ‖virasoroPhi c w - w‖ ≤ 1 ∧ ‖deriv (virasoroPhi c) w - 1‖ ≤ 1 / 2 :=
    fun w hw => ⟨(hcl w hw).1.trans hφ1, (hcl w hw).2.trans hφ2⟩
  obtain ⟨hp2, hp3, hp4, -, -, -⟩ := rpow_third_pows hc0
  have hp : 0 < c ^ (-(1 / 3 : ℝ)) := Real.rpow_pos_of_pos hc0 _
  have hcs := cStar_pos
  have hexp' := abs_le.1 hexp
  have hge : airyZero 1 ≤ (virasoroPhi c (airyZero 1 : ℂ)).re := by
    set p := c ^ (-(1 / 3 : ℝ)) with hpdef
    rw [hp2, hp3] at hbr
    rw [hp4, hp3] at hexp'
    have : 0 < p * (-c0Star / cStar - gamma0 * airyZero 1 * p ^ 2 - Cφ * p ^ 3) := mul_pos hp hbr
    have h2 : p * (-c0Star / cStar - gamma0 * airyZero 1 * p ^ 2 - Cφ * p ^ 3) =
        -(c0Star / cStar * p) - gamma0 * airyZero 1 * p ^ 3 - Cφ * p ^ 4 := by ring
    linarith [hexp'.1]
  have hdpos : 0 < c ^ (-(4 / 3 : ℝ)) := Real.rpow_pos_of_pos hc0 _
  have hdiffu : (max C₀ 0 / L₀ + betaTip) * c ^ (-(4 / 3 : ℝ)) ≤
      u - (virasoroPhi c (airyZero 1 : ℂ)).re := by
    have hu' : u = (airyZero 1 - c0Star / cStar * c ^ (-(1 / 3 : ℝ)) - gamma0 * airyZero 1 * c ^ (-1 : ℝ)) +
        betaTip * K * c ^ (-(4 / 3 : ℝ)) := by
      rw [hu]; unfold lowerUstar; ring
    have h2 : betaTip * K * c ^ (-(4 / 3 : ℝ)) =
        (max C₀ 0 / L₀ + Cφ + betaTip) * c ^ (-(4 / 3 : ℝ)) := by
      rw [← hβK]
    linarith [hexp'.2, h2, hu']
  have hviol : LowerViolator virasoroPhi c T := by
    unfold LowerViolator
    have : 0 < (max C₀ 0 / L₀ + betaTip) * c ^ (-(4 / 3 : ℝ)) := by
      have : 0 ≤ max C₀ 0 / L₀ := div_nonneg (le_max_right _ _) hL₀pos.le
      have := betaTip_pos
      positivity
    linarith
  have hthr_mem : -virasoroAThr ∈ Icc (-A2) A2 := by
    unfold virasoroAThr
    exact hAmem (-(|airyZero 1| + 1)) le_rfl (by linarith [abs_nonneg (airyZero 1)])
  have hT_hi : T ≤ virasoroDeltaChart c (-virasoroAThr) := by
    have hle : virasoroDeltaChart c u ≤ virasoroDeltaChart c (-virasoroAThr) :=
      hsA.antitoneOn hthr_mem hu_mem hu3
    linarith
  obtain ⟨N, R, hgood, hrange, hPb⟩ := hpass_c T g hg hviol hT_hi
  have hlow := nodes_lower prob virasoroPhi virasoroC1 c g T κ hκ ⟨ρ, hρ, hdiff⟩ him hclose (hA2 ▸ hRA) hq1 hq0 hq3 hq4
    hviol hge hgood.2 hrange.2 (by
      have := hrange.1; unfold lowerRmin at this; linarith)
  have hgv : 0 ≤ prob.gVac (c / 12) g / (2 * π) :=
    div_nonneg hg.2.2.1 (by positivity)
  have hLeq : (1 / 2) * (κ * (uT - (virasoroPhi c (airyZero 1 : ℂ)).re)) / airyAi' (airyZero 1) ^ 2 =
      L₀ * (uT - (virasoroPhi c (airyZero 1 : ℂ)).re) := by
    rw [hL₀]; field_simp
  rw [hLeq] at hlow
  have hfin : L₀ * ((max C₀ 0 / L₀ + betaTip) * c ^ (-(4 / 3 : ℝ))) ≤
      C₀ * c ^ (-(4 / 3 : ℝ)) := by
    have : L₀ * (u - (virasoroPhi c (airyZero 1 : ℂ)).re) ≤ L₀ * (uT - (virasoroPhi c (airyZero 1 : ℂ)).re) :=
      mul_le_mul_of_nonneg_left (by linarith) hL₀pos.le
    have h3 := mul_le_mul_of_nonneg_left hdiffu hL₀pos.le
    linarith
  have : L₀ * ((max C₀ 0 / L₀ + betaTip) * c ^ (-(4 / 3 : ℝ))) =
      (max C₀ 0 + L₀ * betaTip) * c ^ (-(4 / 3 : ℝ)) := by
    field_simp
  rw [this] at hfin
  have h4 : (max C₀ 0 + L₀ * betaTip) * c ^ (-(4 / 3 : ℝ)) ≤
      C₀ * c ^ (-(4 / 3 : ℝ)) := by linarith
  have h5 := le_of_mul_le_mul_right h4 hdpos
  have hLβ : 0 < L₀ * betaTip := mul_pos hL₀pos betaTip_pos
  linarith only [h5, hLβ, le_max_left C₀ 0]

/-- **`cts:lower-main` from its inputs** (`LowerMainInputs`, the remaining open TeX lemmas, and `LowerPrelim`):
there is `C ≥ 0` with `LowerPhaseStatementSharp prob c0Star gamma0 C`, i.e. every weakly
feasible test has first-site phase at least `τ_*(c) - C c^{-2}`.  Proof: `ctl:pass2` + `cts:rosc-uncond`(4) + `cts:boas`
(`lower_pass_bound`), the first node (`nodes_lower`), the unconditional shifted chart (`virasoroChart_holds`),
and the Langer identification (`LowerLangerPhase`) at `u_* = lowerUstar`. -/
theorem lowerPhase_of_inputs {prob : FixedWeightProblem}
    (hP : LowerPrelim prob) (h : LowerMainInputs prob)
    (hpass : LowerPass2 prob virasoroC1 virasoroPhi)
    (hboas : LowerBoas prob Gout virasoroC1 virasoroPhi virasoroUhat) :
    ∃ C : ℝ, 0 ≤ C ∧ LowerPhaseStatementSharp prob c0Star gamma0 C := by
  have hc0 : c0Star < 0 := c0Star_neg
  obtain ⟨ccp, C₀, hpass⟩ := lower_pass_bound h hpass hboas
  obtain ⟨cP, κ, hκ, hprel⟩ := hP
  obtain ⟨cc_ch, Cφ, hCφ, hch⟩ := virasoroChart_holds
  obtain ⟨cb, hlang⟩ := lowerLangerPhase_holds
  have hAi : 0 < airyAi' (airyZero 1) ^ 2 := by have := airyAi'_first_pos; positivity
  have hβ := betaTip_pos
  set L₀ : ℝ := κ / (2 * airyAi' (airyZero 1) ^ 2) with hL₀
  have hL₀pos : 0 < L₀ := by positivity
  set K : ℝ := (max C₀ 0 / L₀ + Cφ) / betaTip + 1 with hK
  have hK0 : 0 ≤ K := by
    have : 0 ≤ max C₀ 0 / L₀ := div_nonneg (le_max_right _ _) hL₀pos.le
    positivity
  refine ⟨K, hK0, ?_⟩
  have hβK : betaTip * K = max C₀ 0 / L₀ + Cφ + betaTip := by
    rw [hK]; field_simp
  have ha1 : airyZero 1 < 0 := airyZero_neg 1
  have hBV := virasoroBV_pos
  have hc1_bv : 10 * virasoroC1 ≤ virasoroBV := virasoroC1_small.trans virasoroBVChoice_le
  have hdiff2 : 0 < 2 * virasoroBV ^ 2 - 4 * virasoroC1 ^ 2 := by
    have hc1_pos := virasoroC1_pos
    nlinarith only [sq_nonneg virasoroC1, sq_nonneg virasoroBV, hc1_pos, hc1_bv, hBV]
  have hc23 : Tendsto (fun c : ℝ => c ^ (2 / 3 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hcm3 : Tendsto (fun c : ℝ => c ^ (-(1 / 3) : ℝ)) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  have hcm1 : Tendsto (fun c : ℝ => c ^ (-1 : ℝ)) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  have hev : ∀ᶠ c : ℝ in atTop, (airyZero 1 < lowerUstar c0Star gamma0 K c ∧ lowerUstar c0Star gamma0 K c < 0 ∧
        -(|airyZero 1| + 1) ≤ lowerUstar c0Star gamma0 K c) ∧
      0 < -c0Star / cStar - gamma0 * airyZero 1 * c ^ (-(2 / 3) : ℝ) - Cφ * c ^ (-1 : ℝ) ∧
      Cφ * c ^ (-(1 / 3 : ℝ)) ≤ 1 ∧ Cφ * c ^ (-1 : ℝ) ≤ 1 / 2 ∧
      1 ≤ (2 * virasoroBV ^ 2 - 4 * virasoroC1 ^ 2) * c ^ (2 / 3 : ℝ) ∧
      2 * |airyZero 1| ≤ virasoroC1 ^ 2 * c ^ (2 / 3 : ℝ) ∧
      max (max (max cc_ch cP) (max cb ccp)) 3 ≤ c := by
    have h1 := lowerUstar_eventually hc0 gamma0 K
    have h2 := ge_bracket_eventually hc0 gamma0 Cφ
    have h3 : ∀ᶠ c : ℝ in atTop, Cφ * c ^ (-(1 / 3 : ℝ)) ≤ 1 :=
      (by simpa using hcm3.const_mul Cφ : Tendsto (fun c : ℝ => Cφ * c ^ (-(1 / 3) : ℝ)) atTop (𝓝 0)).eventually
        (Iic_mem_nhds zero_lt_one)
    have h4 : ∀ᶠ c : ℝ in atTop, Cφ * c ^ (-1 : ℝ) ≤ 1 / 2 :=
      (by simpa using hcm1.const_mul Cφ : Tendsto (fun c : ℝ => Cφ * c ^ (-1 : ℝ)) atTop (𝓝 0)).eventually
        (Iic_mem_nhds (by norm_num))
    have h5 := (hc23.const_mul_atTop hdiff2).eventually_ge_atTop 1
    have h6 := (hc23.const_mul_atTop (by have := virasoroC1_pos; positivity : 0 < virasoroC1 ^ 2)).eventually_ge_atTop
      (2 * |airyZero 1|)
    have h7 := eventually_ge_atTop (max (max (max cc_ch cP) (max cb ccp)) 3)
    filter_upwards [h1, h2, h3, h4, h5, h6, h7] with c a b c' d e f g
    exact ⟨a, b, c', d, e, f, g⟩
  obtain ⟨c₂, hc₂⟩ := eventually_atTop.1 hev
  refine ⟨c₂, fun c hc T g hg => ?_⟩
  obtain ⟨⟨hu1, hu2, hu3⟩, hbr, hφ1, hφ2, hA1, hRa, hcmax⟩ := hc₂ c hc
  have hc3 : 3 ≤ c := (le_max_right _ _).trans hcmax
  have hc0 : 0 < c := by linarith
  have hcch : cc_ch ≤ c := ((le_max_left _ _).trans (le_max_left _ _)).trans
    ((le_max_left _ _).trans hcmax)
  have hcP : cP ≤ c := ((le_max_right _ _).trans (le_max_left _ _)).trans
    ((le_max_left _ _).trans hcmax)
  have hcb : cb ≤ c := ((le_max_left _ _).trans (le_max_right _ _)).trans
    ((le_max_left _ _).trans hcmax)
  have hccp : ccp ≤ c := ((le_max_right _ _).trans (le_max_right _ _)).trans
    ((le_max_left _ _).trans hcmax)
  set u := lowerUstar c0Star gamma0 K c with hu
  set A2 := virasoroAC c ^ 2 with hA2
  have hA2eq : A2 = 2 * virasoroBV ^ 2 * c ^ (2 / 3 : ℝ) := virasoroAC_sq c hc0.le
  have hc23pos : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
  have hRmax : lowerRmax virasoroC1 c = 4 * virasoroC1 ^ 2 * c ^ (2 / 3 : ℝ) := rfl
  have hRmin : lowerRmin virasoroC1 c = virasoroC1 ^ 2 * c ^ (2 / 3 : ℝ) := rfl
  have hRA : lowerRmax virasoroC1 c + 1 ≤ A2 := by rw [hA2eq, hRmax]; nlinarith
  have hRmax_ge : 2 * |airyZero 1| ≤ lowerRmax virasoroC1 c := by
    rw [hRmax]; nlinarith [sq_nonneg virasoroC1, mul_nonneg (sq_nonneg virasoroC1) hc23pos.le]
  have habs_a : |airyZero 1| = -airyZero 1 := abs_of_neg ha1
  have hAmem : ∀ x : ℝ, -(|airyZero 1| + 1) ≤ x → x ≤ 0 → x ∈ Icc (-A2) A2 := by
    intro x hx1 hx2
    refine ⟨by linarith [habs_a], by linarith⟩
  have hsA : StrictAntiOn (virasoroDeltaChart c) (Icc (-A2) A2) := virasoroDeltaChart_strictAnti hc0
  have hu_mem : u ∈ Icc (-A2) A2 := hAmem u hu3 hu2.le
  have ha1_mem : airyZero 1 ∈ Icc (-A2) A2 := hAmem _ (by linarith) ha1.le
  have h0_mem : (0 : ℝ) ∈ Icc (-A2) A2 := hAmem 0 (by linarith [abs_nonneg (airyZero 1)]) le_rfl
  -- the claim `Δ(u_*) ≤ T`
  have hclaim : virasoroDeltaChart c u ≤ T :=
    lowerPhase_claim_delta_le hκ hc0 hL₀ hL₀pos hβK hu hu1 hu3 hbr hφ1 hφ2
      hA2 hRA hRa hAmem hsA hu_mem ha1_mem hg (hprel c hcP) (hch c hcch) (hpass c hccp)
  -- conclusion
  have hΔ0 : virasoroDeltaChart c 0 < virasoroDeltaChart c u := hsA hu_mem h0_mem hu2
  rw [virasoroDeltaChart_zero] at hΔ0
  have hxiBar : xiBar = xiStar ^ 2 / 3 := rfl
  have hξ := xiStar_pos
  have hΔpos : 0 < virasoroDeltaChart c u := by
    have : 0 < xiBar * c := by rw [hxiBar]; positivity
    linarith
  have hΔnn : 0 ≤ 3 * virasoroDeltaChart c u / c := div_nonneg (by linarith) hc0.le
  refine ⟨√(3 * virasoroDeltaChart c u / c), ?_, ?_, ?_⟩
  · rw [Real.lt_sqrt hξ.le, lt_div_iff₀ hc0]
    rw [hxiBar] at hΔ0
    linarith
  · have h1 := hlang c hcb u hu3 hu2
    have h2 : -u / (betaTip * c ^ (2 / 3 : ℝ)) = tauStar c0Star gamma0 c - K * c ^ (-2 : ℝ) :=
      lowerUstar_phase c0Star gamma0 K hc0
    exact (h1.trans h2).ge
  · rw [Real.sq_sqrt hΔnn]
    have : c / 3 * (3 * virasoroDeltaChart c u / c) = virasoroDeltaChart c u := by field_simp
    linarith

end

end FormalResearch.ModularBootstrap.FiveTerm

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.lowerPhase_of_inputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.lowerPhase_of_inputs

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.lowerUstar_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.lowerUstar_phase
