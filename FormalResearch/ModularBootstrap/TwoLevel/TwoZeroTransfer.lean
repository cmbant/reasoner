module

public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroTransferWindow
public import FormalResearch.ModularBootstrap.Upper.Assembly.DesignWindow
public import FormalResearch.ModularBootstrap.Upper.Assembly.Chart

/-!
# The two-simple-zero transfer, Theorem T2 (`upper_transfer.tex`, `ut:T2`), as a named hypothesis

`ut:T2` (the finite-`c` transfer `(P_{2s})` of `virasoro_two_level.tex`) is **not formalised**: its proof is the
`f = 2` reference comb times the strip inner functions `T_{χ(p)}` (Regions I and II, window limit, vacuum limsup).
This module states it exactly as a named `Prop`, `TwoSimpleZeroTransfer prob`, and proves what is needed to use it:

* `TwoZeroTransferData prob 𝒦`: the conclusion of `ut:T2` for a compact family `𝒦` of admissible designs
  (`TwoZeroDesign.Adm`, `IsCompactFamily`).  Fourier-odd `g_{c,𝔇} ∈ Ā_w` is `TestClass prob (c/12) _`
  (`c = c'` is the effective central charge), the comb decay of (P1) of Property `sr:P`, positivity of `g` for
  `t ≥ t(q) + 1` (`tAiry c q`), the window limit `F_c^{-1} Ψ_g → C₂ W₂` locally uniformly in `u` and uniformly on
  `𝒦`, the vacuum `limsup F_c^{-1} ∫ Ψ_g ≤ C₂ ∫ W₂` uniformly on `𝒦`, `F_c ≍ c^{3/2}`, and
  `g_vac ≥ c_𝒦 c^{3/2}` when `∫ W₂ ≤ -δ` uniformly on `𝒦`, and `Ψ_g` integrable (so the integrals above are genuine).
* `TwoSimpleZeroTransfer prob`: for every `n ≥ 1` (`N = n + 2 ≥ 3`) and every compact family of admissible designs.
* `TwoZeroTransferData.toEventual`, `designPropertyP_twoZero`: for a single design, `ut:T2` gives the abstract
  design test (`Upper.Rigidity.DesignTest`) for the spectral measures `μ_S` of every crossing sequence `S` of `prob`,
  for the window `twoZeroWin d` (first kept site `u_f = q`; `Ψ_j ≥ 0` on `u ≤ u(t(q) + 1) → q`).
* Non-vacuity: `twoZeroDesign_adm_nonempty` (admissible designs exist), `isCompactFamily_singleton`,
  `twoZeroDesignTest_nonvacuous`: in the model `μ_j = μ_A` (Airy quadrature measure) every window of
  `twoZeroClass` carries a design test, so the interface that `ut:T2` is converted to is satisfiable; the
  statement `TwoSimpleZeroTransfer prob` itself is the content of the later package that proves `ut:T2`.

The vacuum clause and the uniformity are stated as in the TeX.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Upper.Rigidity FormalResearch.ModularBootstrap.Upper.Assembly
open FormalResearch.ModularBootstrap.Upper.Window FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.Upper.Design

/-! ### The position of the threshold `t(q) + 1` -/

/-- `u(t(q) + 1) → q`: the threshold `t(q) + 1` of `ut:T2` sits at `u = q + O(c^{-1/3})`. -/
theorem tendsto_uAiry_tAiry_add_one (q : ℝ) :
    Tendsto (fun c : ℝ => uAiry c (tAiry c q + 1)) atTop (𝓝 q) := by
  have hκ := kappaAiry_pos
  have hxi := xiStar_pos
  set σs : ℕ → ℝ := fun _ => -q / kappaAiry with hσs
  have h0 : Tendsto (fun c : ℝ => xiStar + lambdaComb c * (-q / kappaAiry)) atTop
      (𝓝 (xiStar + 0 * (-q / kappaAiry))) :=
    (tendsto_lambdaComb_atTop.mul_const _).const_add _
  have hev : ∀ᶠ c : ℝ in atTop, 0 ≤ xiStar + lambdaComb c * (-q / kappaAiry) := by
    refine (h0.eventually (lt_mem_nhds (by simpa using hxi))).mono fun c hc => hc.le
  have hlim := uAiry_sigTf σs
  have hval : -(kappaAiry * σs 1) = q := by
    simp only [hσs]; field_simp
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [hev, eventually_gt_atTop (0 : ℝ)] with c hc hc0
  have : sigTf σs c = tAiry c q := by
    rw [tAiry_eq hc0 hc]
    simp only [sigTf, designSite, hσs]
  rw [this]

/-! ### Theorem T2 as a named hypothesis -/

/-- The conclusion of `ut:T2` (`upper_transfer.tex`) for a family `𝒦` of two-simple-zero designs: the
functionals `g_{c,𝔇}`, the normalisations `F_c ≍ c^{3/2}`, `C₂ > 0`, positivity for `t ≥ t(q) + 1`, the window
limit, the integrability of `Ψ_g` (eventually, uniformly on `𝒦`; needed for the integral in `limsup_le`
to be genuine Bochner integrals rather than the value `0` of a non-integrable function), the vacuum limsup (uniform
on `𝒦`), and the vacuum bound.  See the module docstring. -/
structure TwoZeroTransferData (prob : FixedWeightProblem) {n : ℕ} (𝒦 : Set (TwoZeroDesign n)) where
  c₀ : ℝ
  C₂ : ℝ
  F : ℝ → ℝ
  g : TwoZeroDesign n → ℝ → ℝ → ℝ
  c₀_pos : 0 < c₀
  C₂_pos : 0 < C₂
  F_asymp : ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ c : ℝ, c₀ ≤ c →
    A * c ^ ((3 : ℝ) / 2) ≤ F c ∧ F c ≤ B * c ^ ((3 : ℝ) / 2)
  testClass : ∀ c : ℝ, c₀ ≤ c → ∀ d ∈ 𝒦, TestClass prob (c / 12) (g d c)
  decay : ∀ c : ℝ, c₀ ≤ c → ∀ d ∈ 𝒦, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
    |g d c t| ≤ C * Real.exp (-4 * π * Real.sqrt (c / 12 * t) - π * Real.sqrt (3 * t / c))
  pos : ∀ c : ℝ, c₀ ≤ c → ∀ d ∈ 𝒦, ∀ t : ℝ, tAiry c d.q + 1 ≤ t → 0 < g d c t
  window : ∀ R : ℝ, 0 ≤ R → ∀ ε : ℝ, 0 < ε → ∀ᶠ c : ℝ in atTop, ∀ d ∈ 𝒦, ∀ u ∈ Icc (-R) R,
    |(F c)⁻¹ * psiAiry prob c (g d c) u - C₂ * d.Wr u| ≤ ε
  integrable : ∀ᶠ c : ℝ in atTop, ∀ d ∈ 𝒦, Integrable (psiAiry prob c (g d c))
  limsup_le : ∀ ε : ℝ, 0 < ε → ∀ᶠ c : ℝ in atTop, ∀ d ∈ 𝒦,
    (F c)⁻¹ * (∫ u, psiAiry prob c (g d c) u) ≤ C₂ * (∫ u, d.Wr u) + ε
  vac : (∃ δ : ℝ, 0 < δ ∧ ∀ d ∈ 𝒦, ∫ u, d.Wr u ≤ -δ) → ∃ κ : ℝ, 0 < κ ∧
    ∀ c : ℝ, c₀ ≤ c → ∀ d ∈ 𝒦, κ * c ^ ((3 : ℝ) / 2) ≤ prob.gVac (c / 12) (g d c)

/-- **Hypothesis (not formalised): Theorem T2** (`upper_transfer.tex`, `ut:T2`, the two-simple-zero transfer
`(P_{2s})`).  For every `N = n + 2 ≥ 3` and every compact family of designs with zeros `p > q`, `q < 0`, on-band
modified pairs with distinct sites and positive widths (reference pairs `η₀ = 1/4` elsewhere), the data of
`TwoZeroTransferData` exist, at the fixed weight `prob`.  Discharged by the package that proves `ut:T2`. -/
def TwoSimpleZeroTransfer (prob : FixedWeightProblem) : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ 𝒦 : Set (TwoZeroDesign n), TwoZeroDesign.IsCompactFamily 𝒦 →
    (∀ d ∈ 𝒦, d.Adm) → Nonempty (TwoZeroTransferData prob 𝒦)

/-! ### From T2 to the design test for `μ_S` -/

/-- The class of the two-simple-zero windows (`n ≥ 1`, admissible `d`). -/
def twoZeroClass : Set Window :=
  {D | ∃ (n : ℕ) (_ : 1 ≤ n) (d : TwoZeroDesign n) (hd : d.Adm), D = twoZeroWin d hd}

lemma twoZeroWin_mem {n : ℕ} (hn : 1 ≤ n) (d : TwoZeroDesign n) (hd : d.Adm) :
    twoZeroWin d hd ∈ twoZeroClass := ⟨n, hn, d, hd, rfl⟩

lemma isCompactFamily_singleton {n : ℕ} (d : TwoZeroDesign n) :
    TwoZeroDesign.IsCompactFamily ({d} : Set (TwoZeroDesign n)) := by
  unfold TwoZeroDesign.IsCompactFamily
  rw [Set.image_singleton]; exact isCompact_singleton

namespace TwoZeroTransferData

variable {prob : FixedWeightProblem} {n : ℕ} {d : TwoZeroDesign n}

lemma F_pos (X : TwoZeroTransferData prob {d}) {c : ℝ} (hc : X.c₀ ≤ c) : 0 < X.F c := by
  obtain ⟨A, B, hA, hB, h⟩ := X.F_asymp
  have hc0 : 0 < c := lt_of_lt_of_le X.c₀_pos hc
  exact lt_of_lt_of_le (by positivity) (h c hc).1

/-- For a single design, `ut:T2` is the eventual comb data of `twoZeroWin d`, with scale
`(C₂ F_c)^{-1}` and `t_f := t(q)`. -/
noncomputable def toEventual (X : TwoZeroTransferData prob {d}) (hd : d.Adm) :
    EventualCombData prob (twoZeroWin d hd) where
  g := X.g d
  scale := fun c => (X.C₂ * X.F c)⁻¹
  tf := fun c => tAiry c d.q
  good := by
    filter_upwards [eventually_ge_atTop X.c₀] with c hc
    have hc0 : 0 < c := lt_of_lt_of_le X.c₀_pos hc
    have hF := X.F_pos hc
    refine ⟨hc0, inv_pos.2 (mul_pos X.C₂_pos hF), X.testClass c hc d rfl, X.decay c hc d rfl, ?_,
      fun t ht => (X.pos c hc d rfl t ht).le⟩
    have := tAiry_nonneg hc0 d.q
    linarith
  theta := by simpa using tendsto_uAiry_tAiry_add_one d.q
  window := fun R hR ε hε => by
    have h := X.window R hR (ε * X.C₂) (mul_pos hε X.C₂_pos)
    filter_upwards [h, eventually_ge_atTop X.c₀] with c hc hc₀ u hu
    have hF := X.F_pos hc₀
    have := hc d rfl u hu
    simp only [twoZeroWin_W]
    have e : (X.C₂ * X.F c)⁻¹ * psiAiry prob c (X.g d c) u - d.Wr u =
        ((X.F c)⁻¹ * psiAiry prob c (X.g d c) u - X.C₂ * d.Wr u) / X.C₂ := by
      field_simp [X.C₂_pos.ne']
    rw [e, abs_div, abs_of_pos X.C₂_pos, div_le_iff₀ X.C₂_pos]
    linarith
  limsup := fun ε hε => by
    have h := X.limsup_le (ε * X.C₂) (mul_pos hε X.C₂_pos)
    filter_upwards [h] with c hc
    have := hc d rfl
    have hV : (twoZeroWin d hd).V = ∫ u, d.Wr u := rfl
    show ∫ u, (X.C₂ * X.F c)⁻¹ * psiAiry prob c (X.g d c) u ≤ (twoZeroWin d hd).V + ε
    rw [hV, integral_const_mul]
    have e : (X.C₂ * X.F c)⁻¹ * (∫ u, psiAiry prob c (X.g d c) u) =
        ((X.F c)⁻¹ * (∫ u, psiAiry prob c (X.g d c) u)) / X.C₂ := by
      field_simp
    rw [e, div_le_iff₀ X.C₂_pos]
    have h2 : (X.C₂ * (∫ u, d.Wr u) + ε * X.C₂) = ((∫ u, d.Wr u) + ε) * X.C₂ := by ring
    exact this.trans h2.le

end TwoZeroTransferData

/-- **`ut:T2` gives Property `sr:P` for the two-simple-zero windows**: every window of `twoZeroClass` carries a
design test for the spectral measures of every crossing sequence of `prob`. -/
theorem designPropertyP_twoZero {prob : FixedWeightProblem} (hT : TwoSimpleZeroTransfer prob)
    (S : CrossingSequence prob) : DesignPropertyP S.μS twoZeroClass := by
  refine designPropertyP_of_comb S fun D hD => ?_
  obtain ⟨n, hn, d, hd, rfl⟩ := hD
  obtain ⟨X⟩ := hT n hn {d} (isCompactFamily_singleton d) (fun d' h => by rw [mem_singleton_iff.1 h]; exact hd)
  exact ⟨(X.toEventual hd).toComb S⟩

/-! ### Non-vacuity -/

/-- Admissible designs exist (`n = 1`). -/
theorem twoZeroDesign_adm_nonempty : ∃ d : TwoZeroDesign 1, d.Adm :=
  ⟨⟨0, -1, fun _ => -2, fun _ => 1⟩, by
    refine ⟨by norm_num, by norm_num, fun _ => by norm_num, ?_, fun _ => by norm_num⟩
    intro i j _; exact Subsingleton.elim i j⟩

/-- Non-vacuity of the interface that `ut:T2` is converted to: in the model `μ_j = μ_A` (the Airy quadrature
measure, `Ψ_j = W`) every window of `twoZeroClass` carries a design test.  This uses that `twoZeroWin d` is a
genuine `Window` (continuous, integrable, `W_2 ≥ 0` on `u ≤ q`, Airy quadrature). -/
theorem twoZeroDesignTest_nonvacuous : DesignPropertyP (fun _ => airyMeasure) twoZeroClass :=
  designPropertyP_nonvacuous twoZeroClass

/-- The window `W_2` of an admissible design is positive below `q`, negative between `q` and `p`, positive
above `p`: the sign pattern that makes `∫ W_2 < 0` possible. -/
theorem twoZeroWindow_signs {n : ℕ} (d : TwoZeroDesign n) (hd : d.Adm) :
    (∀ u, u < d.q → 0 < d.Wr u) ∧ (∀ u, d.q < u → u < d.p → d.Wr u < 0) ∧
      (∀ u, d.p < u → 0 < d.Wr u) :=
  ⟨fun _ h => d.Wr_pos_of_lt hd h, fun _ h1 h2 => d.Wr_neg_of_mem hd h1 h2,
    fun _ h => d.Wr_pos_of_gt hd h⟩

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.tendsto_uAiry_tAiry_add_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tendsto_uAiry_tAiry_add_one

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.designPropertyP_twoZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms designPropertyP_twoZero

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZeroDesignTest_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZeroDesignTest_nonvacuous

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZeroDesign_adm_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZeroDesign_adm_nonempty

end FormalResearch.ModularBootstrap.TwoLevel
