module

public import FormalResearch.ModularBootstrap.Upper.Positivity.Vacuum
public import FormalResearch.ModularBootstrap.Upper.Positivity.RegionOneAssembly

/-!
# The comb functional `g_𝔇` of the Virasoro designs and its membership/positivity data

Source: `CFT/modular_bootstrap/paper/upper_transfer.tex` (`ut:P`, `ut:III`) and
`CFT/modular_bootstrap/paper/spectral_rigidity.tex` (Property `sr:P`, (P1), (P2)).

For the design `D(N, η_*, d)` (`f = 1`, `w = 1`, `Q = (1 - q)²`) at the central charge parameter `c`
(the `c'` of the comb modules):

* `designBc N η d c`: the comb `B_D` (`designComb c 1 N (1/4) (designSigma1 d) (designWidth1 c η)`);
* `designG N η d c`: `g = ½ (h₀ - ĥ₀)` (`pairOdd`), with `h₀ = combProfile`, `ĥ₀ = hankelTransform 1 h₀`;
* `designTf d c`: `t_f = c χ'_1² / 3`, with `χ'_1 = ξ_* + λ σ_1` the first (shifted) site.

Results, all for `c` large (`∀ᶠ c in atTop`) and unconditional:

* `designGood`: the conclusion of Lemma `K7` (`K7Conclusion`) together with `InnerCombHyp`;
* `designG_testClass`: `g ∈ Ā` (`TestClass virasoroProblem (c/12) g`) (P1);
* `designG_decay`: `|g(t)| ≤ C e^{-4π√(c t/12) - π√(3t/c)}` (P1);
* `designG_nonneg`: `g(t) ≥ 0` for `t ≥ t_f + 1`, for `η_* ∈ (0, 1/4]` (P2, from Proposition I and II);
* `designG_gVac_pos`: `V_D < 0` implies `g_vac > 0` (Proposition V (ii)).

**Restriction of the design class.**  Positivity (`designG_nonneg`) uses Proposition I, whose
Lemma R needs `η_* > 0`; membership and the vacuum bound hold for `η_* ≥ 0`.  All designs of this
module have `f = 1` (the first kept site is `a_1 - d`, no omitted sites) and no displaced site.
-/

@[expose] public section

open Real Filter Topology Set MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Assembly

open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.Upper.Hankel FormalResearch.ModularBootstrap.Upper.Comb
  FormalResearch.ModularBootstrap.Upper.Design FormalResearch.ModularBootstrap.Upper.Window
  FormalResearch.ModularBootstrap.Upper.Holes FormalResearch.ModularBootstrap.Upper.Membership
  FormalResearch.ModularBootstrap.Upper.Positivity

/-- The comb `B_D` of the design `D(N, η_*, d)` at `c`. -/
noncomputable def designBc (N : ℕ) (η d c : ℝ) : ℂ → ℂ :=
  designComb c 1 N (1 / 4) (designSigma1 d) (designWidth1 c η)

/-- `g = ½ (h₀ - ĥ₀)` of the design `D(N, η_*, d)` at `c`. -/
noncomputable def designG (N : ℕ) (η d c : ℝ) : ℝ → ℝ :=
  pairOdd (combProfile c (designBc N η d c))
    (hankelTransform 1 (combProfile c (designBc N η d c)))

/-- `t_f = c χ'_1² / 3`, `χ'_1 = ξ_* + λ σ_1` the first site of the design. -/
noncomputable def designTf (d c : ℝ) : ℝ := c * designSite c (designSigma1 d) 1 ^ 2 / 3

lemma designGVac_eq (N : ℕ) (η d c : ℝ) :
    designGVac N η d c = virasoroProblem.gVac (c / 12) (designG N η d c) := rfl

/-- The conclusion of Lemma `K7` and `InnerCombHyp` for the design comb. -/
def DesignGood (N : ℕ) (η d c : ℝ) : Prop :=
  0 < c ∧ InnerCombHyp c (designBc N η d c) ∧ K7Conclusion virasoroProblem c (designBc N η d c)

lemma designGood_eventually (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) (d : ℝ) :
    ∀ᶠ c in atTop, DesignGood N η d c := by
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ k, 1 ≤ k → k ≤ N → |designSigma1 d k| ≤ M :=
    ⟨∑ k ∈ Finset.Icc 1 N, |designSigma1 d k|, fun k hk hkN =>
      Finset.single_le_sum (f := fun j => |designSigma1 d j|) (fun _ _ => abs_nonneg _)
        (Finset.mem_Icc.mpr ⟨hk, hkN⟩)⟩
  obtain ⟨Cg, hCg, h_ev⟩ := siteGap_eventually_le
  filter_upwards [design1_k7_membership_vacuum (prob := virasoroProblem) rfl N hN hη0 hη1 d M hM,
    designComb_innerCombHyp 1 N le_rfl hN M Cg (by norm_num : (0 : ℝ) ≤ 1 / 4) le_rfl, h_ev,
    eventually_gt_atTop (0 : ℝ)] with c hK7 hInner ⟨hgap_k, hgap_1_bd, hcd1_bd, _⟩ hpos
  refine ⟨hpos, hInner (designSigma1 d) (designWidth1 c η) (fun k hk hkN => hM k hk hkN)
    (fun k hk hkN => ⟨mul_nonneg hη0 (siteGap_nonneg hpos (by omega)), ?_⟩), hK7⟩
  have hgk := (hgap_k k (by omega)).trans (hgap_1_bd.trans hcd1_bd)
  unfold designWidth1
  calc η * siteGap c k ≤ 1 * (Cg * lambdaComb c) :=
        mul_le_mul (hη1.trans (by norm_num)) hgk (siteGap_nonneg hpos (by omega)) (by norm_num)
    _ = Cg * lambdaComb c := one_mul _

lemma DesignGood.testClass {N : ℕ} {η d c : ℝ} (h : DesignGood N η d c) :
    TestClass virasoroProblem (c / 12) (designG N η d c) := by
  obtain ⟨-, -, C, -, -, -, hT, -⟩ := h
  exact hT

/-- `c · (2π x / 3) = 4π √((c/12) t)` for `x = √(3t/c)`. -/
lemma decay_exponent_eq {c t : ℝ} (hc : 0 < c) (ht : 0 ≤ t) :
    c * (2 * π * xOf c t / 3) = 4 * π * √(c / 12 * t) := by
  have hx : 0 ≤ xOf c t := Real.sqrt_nonneg _
  have h : c / 12 * t = (c / 6 * xOf c t) ^ 2 := by
    rw [mul_pow, show xOf c t ^ 2 = 3 * t / c by unfold xOf; exact Real.sq_sqrt (by positivity)]
    field_simp
    ring
  rw [h, Real.sqrt_sq (by positivity)]
  ring

lemma DesignGood.decay {N : ℕ} {η d c : ℝ} (h : DesignGood N η d c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
      |designG N η d c t| ≤ C * Real.exp (-4 * π * √(c / 12 * t) - π * √(3 * t / c)) := by
  obtain ⟨hc, -, C, hC, hd1, hd2, -⟩ := h
  refine ⟨C, hC, fun t ht => ?_⟩
  have := (hd1.pairOdd hd2) t ht
  unfold decayEnv at this
  rw [decay_exponent_eq hc ht] at this
  have e : -(4 * π * √(c / 12 * t)) - π * xOf c t = -4 * π * √(c / 12 * t) - π * √(3 * t / c) := by
    unfold xOf; ring
  rw [e] at this
  exact this

/-- **(P2) positivity of `g`**: for `η_* ∈ (0, 1/4]` and large `c`, `g(t) ≥ 0` (indeed `> 0`) for every
`t ≥ t_f + 1` (`ut:III` at `w = 1`: Proposition I and Proposition II). -/
theorem designG_nonneg (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 4) (d : ℝ) :
    ∀ᶠ c in atTop, 0 < c ∧ ∀ t : ℝ, designTf d c + 1 ≤ t → 0 < designG N η d c t := by
  filter_upwards [designGood_eventually N hN hη0.le hη1 d, proposition_I_design_t N hN hη0 hη1 d]
    with c hgood hI
  obtain ⟨hc, hInner, C, hC, hd1, hd2, -⟩ := hgood
  refine ⟨hc, fun t ht => ?_⟩
  have htf : 0 ≤ designTf d c := by unfold designTf; positivity
  have ht0 : 0 < t := by linarith
  set x : ℝ := xOf c t with hxdef
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hxt : c * x ^ 2 / 3 = t := by
    rw [hxdef]; unfold xOf
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  have hpos := hI x hx0 (by rw [hxt]; exact ht)
  unfold twoG at hpos
  have hedge := hInner.edgeHankel_eq hc hd1 ht0
  have hh : designProfile c 1 N (1 / 4) (designSigma1 d) (designWidth1 c η) (x : ℂ) =
      ((combProfile c (designBc N η d c) t : ℝ) : ℂ) := by
    have := hInner.combProfile_eq (s := t) ht0
    unfold designBc at this ⊢
    rw [← combH0_designComb]
    convert this using 3
    rfl
  rw [hxt] at hpos
  rw [hh] at hpos
  have e2 : edgeHankel c (designProfile c 1 N (1 / 4) (designSigma1 d) (designWidth1 c η)) t =
      ((hankelTransform 1 (combProfile c (designBc N η d c)) t : ℝ) : ℂ) := by
    rw [← combH0_designComb]; exact hedge
  rw [e2] at hpos
  simp only [Complex.sub_re, Complex.ofReal_re] at hpos
  unfold designG pairOdd
  linarith

/-- **Proposition V (ii) for `g`**: if `V_D < 0`, then `g_vac > 0` for large `c`. -/
theorem designG_gVac_pos (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) (d : ℝ)
    (hV : windowIntegralVD N η d < 0) :
    ∀ᶠ c in atTop, 0 < virasoroProblem.gVac (c / 12) (designG N η d c) := by
  filter_upwards [proposition_V_ii N hN hη0 hη1 d hV] with c hc
  exact hc.1

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.designGood_eventually' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms designGood_eventually

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.DesignGood.testClass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DesignGood.testClass

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.DesignGood.decay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DesignGood.decay

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.designG_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms designG_nonneg

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.designG_gVac_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms designG_gVac_pos

end FormalResearch.ModularBootstrap.Upper.Assembly
