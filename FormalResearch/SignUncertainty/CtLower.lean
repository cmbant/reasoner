module

public import FormalResearch.SignUncertainty.CtLowerDefs
public import FormalResearch.SignUncertainty.CtLowerChartGap
public import FormalResearch.SignUncertainty.CtKappaNeg
public import FormalResearch.SignUncertainty.Radii
public import FormalResearch.SignUncertainty.CtOuter
public import FormalResearch.SignUncertainty.CtCfuData
public import FormalResearch.SignUncertainty.HankelTransportInt
public import FormalResearch.SignUncertainty.RadialRigidity
public import FormalResearch.SignUncertainty.HankelEdgePhase
public import FormalResearch.SignUncertainty.HankelThresholds

/-!
# `thm:ct-lower`: the five-term lower bound, assembled from named inputs (F1 skeleton)

`constant_terms_lower.tex`, "Proof of the lower bound in `thm:ct-lower`(i)" (`eq:ct-lower`, left half).  For real `c ≥ c₀`
and `ε = ±1`, every feasible threshold `T` of the Hankel problem satisfies
`Δ₅^ε(c) - C c⁻¹ log c ≤ T`, where
`Δ₅^ε(c) = c/π² + A c^{1/3} + κ_ε + c₁^{Langer} c^{-1/3} + d₂^{*,ε} c^{-2/3}`,
`κ_ε = θ₁^ε/π²`, `c₁^{Langer} = 9π²A²/25`, `d₂^{*,ε} = A(θ₁^ε + 12θ₃^ε/π²)`.

**Status: conditional on `CtLowerInputs`** (`pass1`, `pass2`, `node_lower`; the inversion step `chart_gap` is proved:
`ctChartGap` in `CtLowerChartGap`, with `κ_ε < 0` from `CtKappaNeg`).  The proof in the paper is by contradiction at the first Airy node: a
feasible `f` at `T ≤ Δ₅ - K c⁻¹ log c` has `ũ₁ - φ_c(a₁) ≥ (Kβ₁/2) c^{-4/3} log c` (Langer chart inversion), and the
dual identity at two good radii (`ct:dyadic` (2), (4) with `ct:boas`) bounds the budget `P_R(H) + g_vac/2π` above by
`C₀ c^{-4/3} log c` with `C₀` independent of `K`, while the effective `C¹` stability at the first node
(`gt:7.7p` (b), (d)) bounds it below by a positive multiple of `ũ₁ - φ_c(a₁)` minus an exponentially small term.  This file
proves the last step (the choice of `K` and the contradiction) from the fields of `CtLowerInputs` and `ctChartGap`.  The TeX
objects are defined concretely in `CtLowerDefs` (`ctGap`, `ctBudget`; see their docstrings): `ũ(T/c)` is the inverse of the
Lean Langer chart `hankelXi`, `φ_c` the inverse of `û` built from the CFU phase `ψ_ε = θ_ε(τ₀(a))/√(-a)`, `Ψ̃` is
`hankelPsi`, and `P_R`, `g_vac` are as in `ap:thmD` and `ct:gvac-def`.  Instantiating the structure means proving the
statements about these definitions (see `PLAN.md`, the `ct:dyadic` row).  The only parts of the definitions that are
junk outside the regime of the TeX are noted in their docstrings (`invFunOn` returns an arbitrary point where `û` is not
bijective); the fields are only used inside that regime.  No result of this file is unconditional.
-/

@[expose] public section

open scoped Real
open Filter Topology

namespace FormalResearch.SignUncertainty

/-- **`thm:ct-lower` (`eq:ct-lower`, left half), the statement:** non-effective `c₀, C` such that for real `c ≥ c₀` and
`ε = ±1`, every feasible threshold is at least `Δ₅^ε(c) - C c⁻¹ log c` (equivalently, `Δ₅^ε(c) - C c⁻¹ log c ≤ T_c^ε`
when a feasible threshold exists). -/
def CtLowerStatement : Prop :=
  ∃ c₀ C : ℝ, ∀ c : ℝ, c₀ ≤ c → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → ∀ (T : ℝ) (f : ℝ → ℝ),
    IsHankelFeasible c ε T f → ctDelta5 ε c - C * (c⁻¹ * Real.log c) ≤ T

/-- **The TeX results of `constant_terms_lower.tex` not yet in Lean, as the fields the contradiction argument uses**
(the chart inversion `chart_gap`, `ct:langer-inv` with `ct:five-term-node`, is the proved `ctChartGap`).

All statements are about a feasible `f` with `M[f] = 1` (`hankelMass c f = 1`) and the concrete objects `ctGap`,
`ctBudget`.  `c₁ > 0` is the constant of `ct:cfu`; the good radii are the radii `R ∈ [c₁²c^{2/3}, 4c₁²c^{2/3}]` (the
window `ctWindow`).

* `pass1`: `ct:dyadic` (2) (first good radius `R₁`, `η(R₁) ≤ C`), (4) and `ct:boas`, for `ũ₁ > φ_c(a₁)`.
* `pass2`: `ct:dyadic` (2) (second good radius `R`, `η(R) ≤ C c^{-1/3} log c`), (4) without the `𝟙_{E_un}` term and
  `ct:boas`, given the Pass-1 bound; the constant `C₀` does not depend on `K`.
* `node_lower`: `gt:7.7p` (b) and (d) (effective uniform `C¹` stability at `α = 0`, `f_*(u) = Ai(u)²/(a₁-u)`), `g_vac ≥ 0`
  (`ε f(0) ≤ 0`) and the sign of the `n ≥ 2` nodes: at every radius of the window the budget is at least `κ` times the gap
  up to an exponentially small term. -/
structure CtLowerInputs where
  c₁ : ℝ
  hc₁ : 0 < c₁
  C1 : ℝ
  pass1 : ∃ c₀ : ℝ, ∀ c : ℝ, c₀ ≤ c → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
    ∀ (T : ℝ) (f : ℝ → ℝ), IsHankelFeasible c ε T f → hankelMass c f = 1 → 0 < ctGap ε c T →
      ∃ R₁ : ℝ, R₁ ∈ Set.Icc (c₁ ^ 2 * c ^ (2 / 3 : ℝ)) (4 * c₁ ^ 2 * c ^ (2 / 3 : ℝ)) ∧
        ctBudget R₁ ε c f ≤ C1 * c⁻¹
  pass2 : ∃ C₀ c₀ : ℝ, ∀ c : ℝ, c₀ ≤ c → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
    ∀ (T : ℝ) (f : ℝ → ℝ), IsHankelFeasible c ε T f → hankelMass c f = 1 → 0 < ctGap ε c T →
      (∃ R₁ : ℝ, R₁ ∈ Set.Icc (c₁ ^ 2 * c ^ (2 / 3 : ℝ)) (4 * c₁ ^ 2 * c ^ (2 / 3 : ℝ)) ∧
        ctBudget R₁ ε c f ≤ C1 * c⁻¹) →
      ∃ R : ℝ, R ∈ Set.Icc (c₁ ^ 2 * c ^ (2 / 3 : ℝ)) (4 * c₁ ^ 2 * c ^ (2 / 3 : ℝ)) ∧
        ctBudget R ε c f ≤ C₀ * (c ^ (-(4 / 3) : ℝ) * Real.log c)
  node_lower : ∃ κ κ' C' c₀ : ℝ, 0 < κ ∧ 0 < κ' ∧ ∀ c : ℝ, c₀ ≤ c → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
    ∀ (T : ℝ) (f : ℝ → ℝ), IsHankelFeasible c ε T f → hankelMass c f = 1 → 0 < ctGap ε c T →
      ∀ R : ℝ, R ∈ Set.Icc (c₁ ^ 2 * c ^ (2 / 3 : ℝ)) (4 * c₁ ^ 2 * c ^ (2 / 3 : ℝ)) →
        κ * ctGap ε c T ≤ ctBudget R ε c f + C' * Real.exp (-κ' * c)

/-- **`thm:ct-lower`, left half of `eq:ct-lower`, from `CtLowerInputs`** (the contradiction of the proof: with
`K = 2(max(C₀,0)+1)/(κβ₁)` the budget is at least `(max(C₀,0)+1) c^{-4/3}log c - C' e^{-κ'c}` and at most
`C₀ c^{-4/3}log c`, impossible for large `c`). -/
theorem ct_lower (I : CtLowerInputs) : CtLowerStatement := by
  obtain ⟨C₀, c₂, h2⟩ := I.pass2
  obtain ⟨c₁, h1⟩ := I.pass1
  obtain ⟨κ, κ', C', c₃, hκ, hκ', h3⟩ := I.node_lower
  set M : ℝ := max C₀ 0 + 1 with hM
  have hM0 : 0 < M := by positivity
  have hβ := hankelBeta1_pos
  set K : ℝ := 2 * M / (κ * hankelBeta1) with hK
  have hKpos : 0 < K := by positivity
  obtain ⟨c₀, hc₀⟩ := ctChartGap (fun _ hε => ctKappa_neg hε) K hKpos
  -- the exponential is eventually below `c^{-4/3}`
  have ht := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (4 / 3 : ℝ) κ' hκ'
  have hev : ∀ᶠ c : ℝ in atTop, c ^ (4 / 3 : ℝ) * Real.exp (-κ' * c) < 1 / (|C'| + 1) :=
    ht.eventually (gt_mem_nhds (by positivity))
  obtain ⟨c₄, hc₄⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max c₀ (max c₁ (max c₂ (max c₃ (max c₄ 3)))), K, ?_⟩
  intro c hc ε hε T f₀ hf₀
  simp only [max_le_iff] at hc
  obtain ⟨hc₀', hc₁', hc₂', hc₃', hc₄', hc3⟩ := hc
  have hcpos : 0 < c := by linarith
  -- normalise to `M[f] = 1`
  obtain ⟨f, hf, hmass⟩ := hankel_feasible_normalize hcpos hf₀
  by_contra hlt
  rw [not_le] at hlt
  have hgapK := hc₀ c hc₀' ε hε T f hf hmass hlt.le
  have hlog1 : 1 ≤ Real.log c := by
    have : Real.exp 1 ≤ 3 := by
      have := Real.exp_one_lt_d9; linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log c := Real.log_le_log (Real.exp_pos 1) (by linarith)
  set X : ℝ := c ^ (-(4 / 3) : ℝ) * Real.log c with hX
  have hcp : 0 < c ^ (-(4 / 3) : ℝ) := Real.rpow_pos_of_pos hcpos _
  have hXge : c ^ (-(4 / 3) : ℝ) ≤ X := by
    rw [hX]; nlinarith
  have hXpos : 0 < X := lt_of_lt_of_le hcp hXge
  set g : ℝ := ctGap ε c T with hg
  have hKX : 0 < K * hankelBeta1 / 2 * X := by positivity
  have hgpos : 0 < g := lt_of_lt_of_le hKX hgapK
  obtain ⟨R₁, hR₁, hp1⟩ := h1 c hc₁' ε hε T f hf hmass hgpos
  obtain ⟨R, hR, hp2⟩ := h2 c hc₂' ε hε T f hf hmass hgpos ⟨R₁, hR₁, hp1⟩
  have hn := h3 c hc₃' ε hε T f hf hmass hgpos R hR
  have hκK : κ * (K * hankelBeta1 / 2) = M := by
    rw [hK]; field_simp
  have hMX : M * X ≤ κ * g := by
    have := mul_le_mul_of_nonneg_left hgapK hκ.le
    calc M * X = κ * (K * hankelBeta1 / 2) * X := by rw [hκK]
      _ = κ * (K * hankelBeta1 / 2 * X) := by ring
      _ ≤ κ * g := this
  have hCM : C₀ + 1 ≤ M := by
    have := le_max_left C₀ 0
    rw [hM]; linarith
  have hXle : X ≤ C' * Real.exp (-κ' * c) := by
    have h5 : M * X ≤ C₀ * X + C' * Real.exp (-κ' * c) := by
      have : κ * g ≤ ctBudget R ε c f + C' * Real.exp (-κ' * c) := hn
      have h6 : ctBudget R ε c f ≤ C₀ * X := hp2
      linarith
    nlinarith
  -- but `C' e^{-κ'c} < c^{-4/3}`
  have hmul : c ^ (-(4 / 3) : ℝ) * c ^ (4 / 3 : ℝ) = 1 := by
    rw [← Real.rpow_add hcpos]; norm_num
  have hpp : 0 < c ^ (4 / 3 : ℝ) := Real.rpow_pos_of_pos hcpos _
  have hex := hc₄ c hc₄'
  have hC1 : 0 < |C'| + 1 := by positivity
  have hlt2 : |C'| * Real.exp (-κ' * c) * c ^ (4 / 3 : ℝ) < 1 := by
    have hE := Real.exp_pos (-κ' * c)
    have h7 : c ^ (4 / 3 : ℝ) * Real.exp (-κ' * c) * (|C'| + 1) < 1 := by
      rw [lt_div_iff₀ hC1] at hex; exact hex
    nlinarith [abs_nonneg C', mul_pos hpp hE]
  have hlt3 : |C'| * Real.exp (-κ' * c) < c ^ (-(4 / 3) : ℝ) := by
    by_contra hcon
    rw [not_lt] at hcon
    have := mul_le_mul_of_nonneg_right hcon hpp.le
    rw [hmul] at this
    linarith
  have := le_abs_self C'
  have hE := Real.exp_pos (-κ' * c)
  nlinarith [mul_le_mul_of_nonneg_right this hE.le]

/-- Corollary in the paper's form: `Δ₅^ε(c) - C c⁻¹ log c ≤ T_c^ε` once a feasible threshold exists for the given
`c` (for large `c` this is `HbThresholdsUpper`, `u1co:O9p`). -/
theorem ct_lower_hankelT (h : CtLowerStatement) :
    ∃ c₀ C : ℝ, ∀ c : ℝ, c₀ ≤ c → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
      (∃ T f, IsHankelFeasible c ε T f) →
        ctDelta5 ε c - C * (c⁻¹ * Real.log c) ≤ hankelT ε c := by
  obtain ⟨c₀, C, hC⟩ := h
  refine ⟨c₀, C, fun c hc ε hε hne => ?_⟩
  exact le_csInf (by obtain ⟨T, f, hf⟩ := hne; exact ⟨T, f, hf⟩)
    fun T ⟨f, hf⟩ => hC c hc ε hε T f hf

/-- info: 'FormalResearch.SignUncertainty.ct_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.ct_lower

/-- info: 'FormalResearch.SignUncertainty.ct_lower_hankelT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.ct_lower_hankelT

end FormalResearch.SignUncertainty
