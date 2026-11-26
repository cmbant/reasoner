module

public import FormalResearch.ModularBootstrap.FiveTerm.UpperAssembly
public import FormalResearch.ModularBootstrap.FiveTerm.UpperTipMatch
public import FormalResearch.ModularBootstrap.Upper.Membership.RadialFourier
public import FormalResearch.ModularBootstrap.Upper.Membership.HankelTransform
public import FormalResearch.ModularBootstrap.Upper.Membership.DecayIntegrability

/-!
# The skeleton of the sharp upper bound: `UpperMainInputs` (FIVE-U)

Source: `CFT/modular_bootstrap/paper/constant_term_slit_strip.tex`, Lemmas C10-C14
(`cts:smooth-env`, `cts:tip-shared`, `cts:upper-design`, `cts:regionII-floor`, `cts:shifted-langer`,
`cts:upper-vac`) and `five_term_roadmap.tex` (`app:gp-assembly`).

`UpperMainInputs src W K G g₁ γ₀` is the list of the open TeX lemmas behind the sharp upper bound, one
field per TeX statement, over an abstract comb `h₀(c', d, b) = ℰ_δ B_D` (a function of the charge `c'`, the
first-site shift `d` and the strip variable `b`).  The test is the one of `K7`/`FW-M`,
`g = ½ (u - 𝓗_w u)` with the real radial profile `u(t) = Re h₀(√(3t/c'))` (`upperTest`, using the
Hankel transform `hankelTransform src.w` of the source), so that `g` is not a free datum.

Fields (the constants `K_δ, C_V, C_1', C_τ` are independent of the shift range `D`; only the threshold
depends on `D`; `δ = K_δ c'^{-1} log c'`):

* `c11_membership` (Lemma C11 `cts:upper-design` (3), with K7): `g ∈ Ā`;
* `c11_first_site` (Lemma C11 (1) site relation `τ̂(χ'_1) = λ(|a_1|+d)/κ_comb`, with the quadratic
  `Ψ_δ` expansion of Lemma C10 (3), giving `eq:gp-first-site`): `ξ_* < χ'_1` and
  `τ(χ'_1) = (|a_1|+d)/β c'^{-2/3} - 3 c_1(δ)/(8√2) c'^{-1} - |a_1| γ_0/β c'^{-5/3} + O(c'^{-2})`;
* `c12_regionII` (Lemma C12 `cts:regionII-floor` (2)): `g ≥ 0` for `x ≥ x_split`;
* `c13_regionI` (Lemma C13 `cts:shifted-langer` (3)): `g ≥ 0` for
  `t ∈ [t(χ'_1) + C_1' c'^{-1} log c', t(x_split)]`;
* `c14_vacuum` (Lemma C14 `cts:upper-vac`, `eq:Vc-exp`): `V^tot/F_c = -d + (c'^{-1/3}/c_*) 𝖡[F_δ] + O(c'^{-4/3} log c')`.

Not fields: Lemmas C10 (1) (`UpperSmoothEnv`), `pm:tip-match` (`UpperTipMatch`), `cts:tip-shared` (b1), (b2), (d)
(`UpperPairDrift`, `UpperPairGamma`, `UpperTipSharedD`) and the algebraic half of C10 (3) (`UpperDetuning`) are proved
and used directly by the proofs of the fields.  The open sub-inputs of the fields are the concrete statements
`AiryLinearMoment` (`cts:tip-shared` (a)) and `AiryPrimitiveDecay` (`cts:tip-shared` (c)) below, and
`cts:smooth-env` (2) (strip factorisation; needs `cts:cauchy-dual` Step 2 of FIVE-L).

**Proved here:** `sharpUpperFamily_of_inputs` (the fields give `SharpUpperFamily`, the interface of
`sharp_upper_of_family`), `sharp_upper_of_inputs` (any shift source) and `spinless_upper_of_inputs`
(the Virasoro corollary through `spinless_upper_of_family`).  These are conditional on `UpperMainInputs`.
-/

@[expose] public section

open Real Filter Topology Set Complex MeasureTheory

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.Special FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Mixtures
  FormalResearch.ModularBootstrap.Upper.Membership

/-- The real radial profile `u(t) = Re h(√(3t/c'))` of a comb `h` (the `combProfile` of `K7` with a general
profile `h`). -/
noncomputable def envProfile (c : ℝ) (h : ℂ → ℂ) (t : ℝ) : ℝ := (h ((Upper.Membership.xOf c t : ℝ) : ℂ)).re

/-- The test `g = ½ (u - 𝓗_w u)` of the comb `h`, for the source `src` (`FW-M`, `K7`). -/
noncomputable def upperTest (src : ShiftSource) (h : ℂ → ℂ) (c : ℝ) : ℝ → ℝ :=
  pairOdd (envProfile c h) (hankelTransform src.w (envProfile c h))

/-- `cts:tip-shared` (a) (Airy linear moment, `cts:airy-sum-zero`):
`2 ∑_{k ≤ K} |a_k|/κ_comb - 2 ∫_{1/4}^{K+1/2} (a - 1/4)^{2/3} da = O(K^{-1/3})`.  Open (needs the Hadamard sum rule
`airyAi_sq_series_real` together with a three-term asymptotic of `Ai'/Ai`). -/
def AiryLinearMoment : Prop :=
  ∃ C : ℝ, ∀ K : ℕ, 1 ≤ K →
    |2 * ∑ k ∈ Finset.Icc 1 K, |airyZero k| / kappaComb -
        2 * ∫ a in (1 / 4 : ℝ)..(K + 1 / 2 : ℝ), (a - 1 / 4) ^ (2 / 3 : ℝ)| ≤ C * (K : ℝ) ^ (-(1 / 3) : ℝ)

/-- The Airy primitive `B(t) = ∫_{-∞}^t Ai - 1_{t>0}` of `cts:tip-shared` (c), written through the absolutely
convergent tail `∫_t^∞ Ai` and `∫_ℝ Ai = 1`. -/
noncomputable def airyPrimB (t : ℝ) : ℝ := (if 0 < t then 0 else 1) - ∫ s in Ioi t, airyAi s

/-- The second primitive `C(t) = t B(t) - Ai'(t)` of `cts:tip-shared` (c). -/
noncomputable def airyPrimC (t : ℝ) : ℝ := t * airyPrimB t - airyAi' t

/-- `cts:tip-shared` (c) decay: `B(t) = O(|t|^{-3/4})`, `C(t) = O(|t|^{-5/4})` as `t → -∞`.  Open (DLMF 9.7.5, 9.7.9-10). -/
def AiryPrimitiveDecay : Prop :=
  ∃ C : ℝ, ∀ t : ℝ, t ≤ -1 →
    |airyPrimB t| ≤ C * |t| ^ (-(3 / 4) : ℝ) ∧ |airyPrimC t| ≤ C * |t| ^ (-(5 / 4) : ℝ)

/-- **The open TeX lemmas behind the sharp upper bound** (see the module docstring), over the abstract comb
`h₀(c', d, ·)`. -/
structure UpperMainInputs (src : ShiftSource) (W : ℝ → ℝ) (K : ℝ → ℂ) (G : ℂ → ℂ) (g1 γ0 : ℝ) where
  Kδ : ℝ
  CV : ℝ
  C1 : ℝ
  Cτ : ℝ
  hKδ : 0 < Kδ
  hCV : 0 ≤ CV
  hC1 : 0 ≤ C1
  hCτ : 0 ≤ Cτ
  /-- the comb `h₀(c', d, b) = ℰ_δ B_D` -/
  h0 : ℝ → ℝ → ℂ → ℂ
  /-- the first site `χ'_1(c', d)` -/
  x1 : ℝ → ℝ → ℝ
  /-- the macroscopic split point `x_split(c', d)` -/
  xs : ℝ → ℝ → ℝ
  /-- the normalisation `F K_c^{(1)} C_*` of the vacuum pairing -/
  Fc : ℝ → ℝ
  /-- Lemma C11 `cts:upper-design` (3) with K7: membership `g ∈ Ā`. -/
  c11_membership : ∀ D : ℝ, 0 < D → ∃ cmin : ℝ, ∀ c : ℝ, cmin ≤ c →
    ∀ d : ℝ, |d| ≤ D * c ^ (-(4 / 3) : ℝ) * Real.log c →
      TestClass src (c / 12) (upperTest src (h0 c d) c)
  /-- Lemma C11 (1) and C10 (3): the first-site phase, `eq:gp-first-site`. -/
  c11_first_site : ∀ D : ℝ, 0 < D → ∃ cmin : ℝ, ∀ c : ℝ, cmin ≤ c →
    ∀ d : ℝ, |d| ≤ D * c ^ (-(4 / 3) : ℝ) * Real.log c →
      xiStar < x1 c d ∧
      |tauPhase (x1 c d) - ((|airyZero 1| + d) / betaTip * c ^ (-(2 / 3) : ℝ) -
          3 * (-g1 - (Kδ * c ^ (-1 : ℝ) * Real.log c) / 2) / (8 * √2) * c ^ (-1 : ℝ) -
          |airyZero 1| / betaTip * γ0 * c ^ (-(5 / 3) : ℝ))| ≤ Cτ * c ^ (-2 : ℝ)
  /-- Lemma C12 `cts:regionII-floor` (2): `g ≥ 0` on `x ≥ x_split` (`t = c' x²/3`). -/
  c12_regionII : ∀ D : ℝ, 0 < D → ∃ cmin : ℝ, ∀ c : ℝ, cmin ≤ c →
    ∀ d : ℝ, |d| ≤ D * c ^ (-(4 / 3) : ℝ) * Real.log c →
      ∀ t : ℝ, c / 3 * xs c d ^ 2 ≤ t → 0 ≤ upperTest src (h0 c d) c t
  /-- Lemma C13 `cts:shifted-langer` (3): `g ≥ 0` on `[t(χ'_1) + C_1' c'^{-1} log c', t(x_split)]`. -/
  c13_regionI : ∀ D : ℝ, 0 < D → ∃ cmin : ℝ, ∀ c : ℝ, cmin ≤ c →
    ∀ d : ℝ, |d| ≤ D * c ^ (-(4 / 3) : ℝ) * Real.log c →
      ∀ t : ℝ, c / 3 * x1 c d ^ 2 + C1 * c ^ (-1 : ℝ) * Real.log c ≤ t → t ≤ c / 3 * xs c d ^ 2 →
        0 ≤ upperTest src (h0 c d) c t
  /-- Lemma C14 `cts:upper-vac` (`eq:Vc-exp`): the vacuum expansion, `F K_c^{(1)} C_* > 0`. -/
  c14_vacuum : ∀ D : ℝ, 0 < D → ∃ cmin : ℝ, ∀ c : ℝ, cmin ≤ c → 0 < Fc c ∧
    ∀ d : ℝ, |d| ≤ D * c ^ (-(4 / 3) : ℝ) * Real.log c →
      |(-(src.gVac (c / 12) (upperTest src (h0 c d) c)) / π) / Fc c + d -
          c ^ (-(1 / 3) : ℝ) / cStar * combB W K (fDelta G (Kδ * c ^ (-1 : ℝ) * Real.log c))| ≤
        CV * c ^ (-(4 / 3) : ℝ) * Real.log c

/-- The fields of `UpperMainInputs` give the test family `SharpUpperFamily`. -/
theorem sharpUpperFamily_of_inputs {src : ShiftSource} {W : ℝ → ℝ} {K : ℝ → ℂ} {G : ℂ → ℂ} {g1 γ0 : ℝ}
    (I : UpperMainInputs src W K G g1 γ0) : SharpUpperFamily src W K G g1 γ0 := by
  refine ⟨I.Kδ, I.CV, I.C1, I.Cτ, fun c d => upperTest src (I.h0 c d) c, I.x1, I.Fc,
    I.hKδ, I.hCV, I.hC1, I.hCτ, ?_⟩
  intro D hD
  obtain ⟨m1, h1⟩ := I.c11_membership D hD
  obtain ⟨m2, h2⟩ := I.c11_first_site D hD
  obtain ⟨m3, h3⟩ := I.c12_regionII D hD
  obtain ⟨m4, h4⟩ := I.c13_regionI D hD
  obtain ⟨m5, h5⟩ := I.c14_vacuum D hD
  refine ⟨max m1 (max m2 (max m3 (max m4 m5))), fun c hc => ?_⟩
  have hc1 : m1 ≤ c := (le_max_left _ _).trans hc
  have hc2 : m2 ≤ c := ((le_max_left _ _).trans (le_max_right _ _)).trans hc
  have hc3 : m3 ≤ c := (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hc
  have hc4 : m4 ≤ c := ((((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans
    (le_max_right _ _)).trans hc
  have hc5 : m5 ≤ c := ((((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans
    (le_max_right _ _)).trans hc
  obtain ⟨hFc, hv⟩ := h5 c hc5
  refine ⟨hFc, fun d hd => ?_⟩
  refine ⟨h1 c hc1 d hd, hv d hd, (h2 c hc2 d hd).1, (h2 c hc2 d hd).2, fun t ht => ?_⟩
  by_cases hts : t ≤ c / 3 * I.xs c d ^ 2
  · exact h4 c hc4 d hd t ht hts
  · exact h3 c hc3 d hd t (not_le.mp hts).le

/-- The sharp upper bound for any shift source, conditional on `UpperMainInputs`. -/
theorem sharp_upper_of_inputs {src : ShiftSource} {W : ℝ → ℝ} {K : ℝ → ℂ} {G : ℂ → ℂ} {g1 γ0 : ℝ}
    (hG : OuterDatum W K g1 G) (I : UpperMainInputs src W K G g1 γ0) :
    ∃ Cp c₀ : ℝ, ∀ c : ℝ, c₀ ≤ c → src.Delta_best c ≤
      c / lambdaV + Aopt * c ^ (1 / 3 : ℝ) + c0StarOf g1 + c1Langer * c ^ (-(1 / 3) : ℝ) +
        d2Of (c0StarOf g1) γ0 * c ^ (-(2 / 3) : ℝ) + Cp * c ^ (-1 : ℝ) * Real.log c :=
  sharp_upper_of_family hG (sharpUpperFamily_of_inputs I)

open FormalResearch.ModularBootstrap.Crossing in
/-- **The Virasoro corollary**: the upper half of `thm:spinless-expansion`, conditional on `UpperMainInputs`. -/
theorem spinless_upper_of_inputs
    (I : UpperMainInputs (ShiftSource.ofProblem virasoroProblem) Wslit Kedge Gout g1Vir gamma0) :
    ∃ Cp c₀ : ℝ, ∀ c : ℝ, c₀ ≤ c → virasoroProblem.Delta_best c ≤
      c / lambdaV + Aopt * c ^ (1 / 3 : ℝ) + c0Star + c1Langer * c ^ (-(1 / 3) : ℝ) +
        d2Star * c ^ (-(2 / 3) : ℝ) + Cp * c ^ (-1 : ℝ) * Real.log c :=
  spinless_upper_of_family (sharpUpperFamily_of_inputs I)

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.sharpUpperFamily_of_inputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sharpUpperFamily_of_inputs

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.spinless_upper_of_inputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms spinless_upper_of_inputs

end FormalResearch.ModularBootstrap.FiveTerm
