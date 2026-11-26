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
public import FormalResearch.SignUncertainty.CtBandTop
public import FormalResearch.SignUncertainty.CtNodeLower

/-!
# `thm:ct-lower`: the five-term lower bound, assembled from named inputs (F1 skeleton)

`constant_terms_lower.tex`, "Proof of the lower bound in `thm:ct-lower`(i)" (`eq:ct-lower`, left half).  For real `c ≥ c₀`
and `ε = ±1`, every feasible threshold `T` of the Hankel problem satisfies
`Δ₅^ε(c) - C c⁻¹ log c ≤ T`, where
`Δ₅^ε(c) = c/π² + A c^{1/3} + κ_ε + c₁^{Langer} c^{-1/3} + d₂^{*,ε} c^{-2/3}`,
`κ_ε = θ₁^ε/π²`, `c₁^{Langer} = 9π²A²/25`, `d₂^{*,ε} = A(θ₁^ε + 12θ₃^ε/π²)`.

**Status: conditional on `CtLowerInputs`** (`dyadic` = `ct:dyadic` (4), `boas` = `ct:boas`; `ct:dyadic` (2) and the node lower bound are proved; the inversion step `chart_gap` is proved:
`ctChartGap` in `CtLowerChartGap`, with `κ_ε < 0` from `CtKappaNeg`).  The proof in the paper is by contradiction at the first Airy node: a
feasible `f` at `T ≤ Δ₅ - K c⁻¹ log c` has `ũ₁ - φ_c(a₁) ≥ (Kβ₁/2) c^{-4/3} log c` (Langer chart inversion), and the
dual identity at one good radius (`ct:dyadic` (2), (4) with `ct:boas`) bounds the budget `P_R(H) + g_vac/2π` above by
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

/-- **`ct:boas`** (`ct:boas-ineq`) in the concrete setting, for the window of `c₁`: at every good radius `R ∈ [c₁²c^{2/3}, 4c₁²c^{2/3}]`
(hypotheses of `ct:dyadic`: feasible `f`, `M[f] = 1`, violator `T < cξ(a₁)`, `ũ₁ > φ_c(a₁)`), the Boas integral with the taper `w̃_R`
is `≥ -C c^{-4/3} log c`.  Block assembly in `CtBoasAssembly` (`boas_ineq_assembled`); the fields of `BoasInputs` are only partly
discharged (see `PLAN.md`). -/
def CtBoasStatement (c₁ : ℝ) : Prop :=
  ∃ C c₀ : ℝ, ∀ c : ℝ, c₀ ≤ c → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
    ∀ (T : ℝ) (f : ℝ → ℝ), IsHankelFeasible c ε T f → hankelMass c f = 1 →
      T < c * hankelXi c (FormalResearch.Special.airyZero 1) → 0 < ctGap ε c T →
      ∀ R : ℝ, R ∈ Set.Icc (c₁ ^ 2 * c ^ (2 / 3 : ℝ)) (4 * c₁ ^ 2 * c ^ (2 / 3 : ℝ)) → ctGoodRadius R →
        -(C * (c ^ (-(4 / 3) : ℝ) * Real.log c)) ≤
          ∫ L in Set.Ici (ctLv0 c), ctTaper ε c R L * (hankelHL c f L * boasKernel (boasX c ε) L)

/-- **The pass** of the proof of `thm:ct-lower` (`ct:dyadic` (2), (4) with `ct:boas`), for the window of `c₁`: for `ũ₁ > φ_c(a₁)`
there is a radius `R` in the window with budget `P_R(H) + g_vac/2π ≤ C₀ c^{-4/3} log c`, `C₀` independent of `K`. -/
def CtPassStatement (c₁ : ℝ) : Prop :=
  ∃ C₀ c₀ : ℝ, ∀ c : ℝ, c₀ ≤ c → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
    ∀ (T : ℝ) (f : ℝ → ℝ), IsHankelFeasible c ε T f → hankelMass c f = 1 →
      T < c * hankelXi c (FormalResearch.Special.airyZero 1) → 0 < ctGap ε c T →
      ∃ R : ℝ, R ∈ Set.Icc (c₁ ^ 2 * c ^ (2 / 3 : ℝ)) (4 * c₁ ^ 2 * c ^ (2 / 3 : ℝ)) ∧
        ctBudget R ε c f ≤ C₀ * (c ^ (-(4 / 3) : ℝ) * Real.log c)

/-- **`ct:dyadic` (4) and `ct:boas`, `ct:dyadic` (2) → the pass.**  `ct:dyadic` (2) is the proved `ct_dyadic_radius_proved` (small `c₁`);
`(ct:combined)` gives `|budget + B| ≤ C(c⁻¹η + c^{-4/3}log c)` with `η ≤ C c^{-1/3}`, and `ct:boas` gives `B ≥ -O(c^{-4/3}log c)`. -/
theorem ct_pass {c₁ : ℝ} (hr : CtDyadicRadiusStatement c₁) (hd : CtDyadicInputs c₁) (hb : CtBoasStatement c₁) :
    CtPassStatement c₁ := by
  obtain ⟨Cr, cr, hr⟩ := hr
  obtain ⟨Cd, cd, hd⟩ := hd.combined
  obtain ⟨Cb, cb, hb⟩ := hb
  refine ⟨|Cb| + |Cd| * (|Cr| + 1), max cr (max cd (max cb 3)), ?_⟩
  intro c hc ε hε T f hf hm hT hg
  simp only [max_le_iff] at hc
  obtain ⟨hc1, hc2, hc3, hc4⟩ := hc
  have hcpos : 0 < c := by linarith
  obtain ⟨R, hR, hgood, hη⟩ := hr c hc1 ε hε T f hf hm hT hg
  refine ⟨R, hR, ?_⟩
  have h1 := hd c hc2 ε hε T f hf hm hT hg R hR hgood
  have h2 := hb c hc3 ε hε T f hf hm hT hg R hR hgood
  have hlog1 : 1 ≤ Real.log c := by
    have : Real.exp 1 ≤ 3 := by
      have := Real.exp_one_lt_d9; linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log c := Real.log_le_log (Real.exp_pos 1) (by linarith)
  have hcp : 0 < c ^ (-(4 / 3) : ℝ) := Real.rpow_pos_of_pos hcpos _
  set X : ℝ := c ^ (-(4 / 3) : ℝ) * Real.log c with hX
  have hXge : c ^ (-(4 / 3) : ℝ) ≤ X := by rw [hX]; nlinarith
  have hηnn : 0 ≤ ctEta c₁ ε c f R :=
    ctEta_nonneg c₁ ε c f (le_trans (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hcpos.le _)) hR.1)
  have hq : c⁻¹ * c ^ (-(1 / 3) : ℝ) = c ^ (-(4 / 3) : ℝ) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hcpos]; norm_num
  have hrp : 0 < c ^ (-(1 / 3) : ℝ) := Real.rpow_pos_of_pos hcpos _
  have ha1 : c⁻¹ * ctEta c₁ ε c f R ≤ |Cr| * X := by
    have e1 : c⁻¹ * ctEta c₁ ε c f R ≤ c⁻¹ * (|Cr| * c ^ (-(1 / 3) : ℝ)) :=
      mul_le_mul_of_nonneg_left (hη.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hrp.le))
        (inv_nonneg.2 hcpos.le)
    have e2 : c⁻¹ * (|Cr| * c ^ (-(1 / 3) : ℝ)) = |Cr| * c ^ (-(4 / 3) : ℝ) := by rw [← hq]; ring
    have e3 : |Cr| * c ^ (-(4 / 3) : ℝ) ≤ |Cr| * X := mul_le_mul_of_nonneg_left hXge (abs_nonneg _)
    linarith
  have ha0 : 0 ≤ c⁻¹ * ctEta c₁ ε c f R + X :=
    add_nonneg (mul_nonneg (inv_nonneg.2 hcpos.le) hηnn) (by linarith)
  have hX0 : 0 ≤ X := by linarith
  have h3 : |ctBudget R ε c f + ∫ L in Set.Ici (ctLv0 c), ctTaper ε c R L * (hankelHL c f L * boasKernel (boasX c ε) L)| ≤
      |Cd| * ((|Cr| + 1) * X) := by
    refine h1.trans ?_
    calc Cd * (c⁻¹ * ctEta c₁ ε c f R + X) ≤ |Cd| * (c⁻¹ * ctEta c₁ ε c f R + X) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) ha0
      _ ≤ |Cd| * ((|Cr| + 1) * X) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  have h4 : -(|Cb| * X) ≤ ∫ L in Set.Ici (ctLv0 c), ctTaper ε c R L * (hankelHL c f L * boasKernel (boasX c ε) L) := by
    have : Cb * X ≤ |Cb| * X := mul_le_mul_of_nonneg_right (le_abs_self _) hX0
    linarith
  have h5 := (abs_le.1 h3).2
  calc ctBudget R ε c f ≤ |Cd| * ((|Cr| + 1) * X) + |Cb| * X := by linarith
    _ = (|Cb| + |Cd| * (|Cr| + 1)) * X := by ring
    _ = (|Cb| + |Cd| * (|Cr| + 1)) * (c ^ (-(4 / 3) : ℝ) * Real.log c) := by rw [hX]

/-- **`thm:ct-lower`, left half of `eq:ct-lower`, from the pass and the node lower bound at one window** (the contradiction of the proof: with
`K = 2(max(C₀,0)+1)/(κβ₁)` the budget is at least `(max(C₀,0)+1) c^{-4/3}log c - C' e^{-κ'c}` and at most
`C₀ c^{-4/3}log c`, impossible for large `c`). -/
theorem ct_lower_of_pass_node {c₁ : ℝ} (hP : CtPassStatement c₁) (hN : CtNodeLowerStatement c₁) :
    CtLowerStatement := by
  obtain ⟨C₀, c₂, h2⟩ := hP
  obtain ⟨κ, κ', C', c₃, hκ, hκ', h3⟩ := hN
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
  refine ⟨max c₀ (max c₂ (max c₃ (max c₄ 3))), K, ?_⟩
  intro c hc ε hε T f₀ hf₀
  simp only [max_le_iff] at hc
  obtain ⟨hc₀', hc₂', hc₃', hc₄', hc3⟩ := hc
  have hcpos : 0 < c := by linarith
  -- normalise to `M[f] = 1`
  obtain ⟨f, hf, hmass⟩ := hankel_feasible_normalize hcpos hf₀
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨hguard, hgapK⟩ := hc₀ c hc₀' ε hε T f hf hmass hlt.le
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
  obtain ⟨R, hR, hp2⟩ := h2 c hc₂' ε hε T f hf hmass hguard hgpos
  have hn := h3 c hc₃' ε hε T f hf hmass hguard hgpos R hR
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

/-- **The TeX results of `constant_terms_lower.tex` not yet in Lean** (`ct:dyadic` (2) and the chart inversion are proved:
`ct_dyadic_radius_proved`, `ctChartGap`).  Each field holds for every small window constant `c₁ > 0` (the constant of `ct:cfu`; the
windows are `[c₁²c^{2/3}, 4c₁²c^{2/3}]`), about a feasible `f` with `M[f] = 1`, the violator `T < cξ(a₁)` and `ũ₁ > φ_c(a₁)`:

* `dyadic`: `ct:dyadic` (4), `(ct:combined)` (`CtDyadicInputs`).
* `boas`: `ct:boas`, `ct:boas-ineq` (`CtBoasStatement`).

The node lower bound (`gt:7.7p` (b), (d), `g_vac ≥ 0`, the sign of the `n ≥ 2` nodes) is the proved `ct_node_lower` (`CtNodeLower`). -/
structure CtLowerInputs : Prop where
  dyadic : ∃ c₁₀ : ℝ, 0 < c₁₀ ∧ ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ c₁₀ → CtDyadicInputs c₁
  boas : ∃ c₁₀ : ℝ, 0 < c₁₀ ∧ ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ c₁₀ → CtBoasStatement c₁

/-- **`thm:ct-lower` from `CtLowerInputs`**: take `c₁` below the three thresholds and the radius threshold of `ct_dyadic_radius_proved`. -/
theorem ct_lower (I : CtLowerInputs) : CtLowerStatement := by
  obtain ⟨a₁, ha₁, hd⟩ := I.dyadic
  obtain ⟨a₂, ha₂, hb⟩ := I.boas
  obtain ⟨a₃, ha₃, hn⟩ := ct_node_lower
  obtain ⟨a₄, ha₄, hr⟩ := ct_dyadic_radius_proved
  set c₁ : ℝ := min a₁ (min a₂ (min a₃ a₄)) with hc₁
  have hpos : 0 < c₁ := lt_min ha₁ (lt_min ha₂ (lt_min ha₃ ha₄))
  have l1 : c₁ ≤ a₁ := min_le_left _ _
  have l2 : c₁ ≤ a₂ := (min_le_right _ _).trans (min_le_left _ _)
  have l3 : c₁ ≤ a₃ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have l4 : c₁ ≤ a₄ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  exact ct_lower_of_pass_node (ct_pass (hr c₁ hpos l4) (hd c₁ hpos l1) (hb c₁ hpos l2)) (hn c₁ hpos l3)

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

/-- info: 'FormalResearch.SignUncertainty.ct_pass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.ct_pass

/-- info: 'FormalResearch.SignUncertainty.ct_lower_of_pass_node' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.ct_lower_of_pass_node

/-- info: 'FormalResearch.SignUncertainty.ct_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.ct_lower

/-- info: 'FormalResearch.SignUncertainty.ct_lower_hankelT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.ct_lower_hankelT

end FormalResearch.SignUncertainty
