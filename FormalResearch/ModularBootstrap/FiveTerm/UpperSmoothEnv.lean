module

public import FormalResearch.ModularBootstrap.FiveTerm.CombRegularisation
public import FormalResearch.ModularBootstrap.FiveTerm.VirasoroG3Main

/-!
# The smoothed minimiser `F_δ = m_δ F_*` and its band functional (FIVE-U; `cts:smooth-env` (1))

Source: `CFT/modular_bootstrap/paper/constant_term_slit_strip.tex`, Lemma C10 (`cts:smooth-env`), item (1),
with eq. `cts:Fdelta`, `cts:Jpf`, `cts:Jpf-lim`.

For an outer-function datum `OuterDatum W K g₁ G` (generic in `(W, K, g₁, G)`; the Virasoro instance is
`gout_outerDatum`) and `δ ∈ (0,1)` (the paper's `δ < δ₀ < 1/4`; the proof does not need the smallness):

* `fDelta G δ = m_δ · (1+z²)/G` (`cts:Fdelta`) lies in `H_adm(Ω)` with `F_δ'(0) = -g₁ - δ/2`
  (`c_1(δ)` of the paper), is zero-free on `closure Ω ∖ {i,-i,1}`, has `F_δ(0) = 1` and is real-symmetric;
* `0 ≤ 𝒥[F_δ] - c_0^* ≤ 25 α_C δ²` (`cts:Jpf-lim`, first half; the constant is absolute);
* the band part `𝖡[F] = 𝒥[F] + α_tip F'(0)` (`cts:Jpf`) satisfies `𝖡[F_*] = 0` and
  `|𝖡[F_δ] + (α_tip/2) δ| ≤ 25 α_C δ²` (`cts:Jpf-lim`, second half);
* the `J`-value in terms of the band part: `𝒥[F_δ] = 𝖡[F_δ] - α_tip c_1(δ)` (the identity behind the
  assembly `eq:gp-upper-final`).

The Virasoro instance `smooth_env_one_virasoro` states the same with `c_0^* = c0Star` and `c_1(δ) = -g1Vir - δ/2`.
Not here: items (2)-(3) of `cts:smooth-env` (strip factorisation of `ℰ_δ`, the potential `ΔΦ_δ`, the
detuning `D_δ`), see `FIVEU_DESIGN.md`.

All results are proved unconditionally.
-/

@[expose] public section

open Complex Set Filter Topology MeasureTheory Metric
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

/-- The smoothed minimiser `F_δ = m_δ F_*` (`cts:Fdelta`, `F_δ = (1+z²) m_δ / G_outer`). -/
noncomputable def fDelta (G : ℂ → ℂ) (δ : ℝ) (z : ℂ) : ℂ := mEps δ z * fStar G z

/-- The band part `𝖡[F] = 𝒥[F] + α_tip F'(0)` of the comb functional (`cts:Jpf`). -/
noncomputable def combB (W : ℝ → ℝ) (K : ℝ → ℂ) (F : ℂ → ℂ) : ℝ :=
  combJ W K F + alphaTip * (slope0 F).re

section

variable {G : ℂ → ℂ} {g1 δ : ℝ} {W : ℝ → ℝ} {K : ℝ → ℂ}

lemma fStar_ne_zero (hG : OuterDatum W K g1 G) {z : ℂ} (hz : z ∈ closure halfDisc \ singPts) :
    fStar G z ≠ 0 := by
  unfold fStar
  have h1 : z ≠ Complex.I := fun h => hz.2 (by rw [mem_singPts_iff]; exact Or.inl h)
  have h2 : z ≠ -Complex.I := fun h => hz.2 (by rw [mem_singPts_iff]; exact Or.inr (Or.inl h))
  exact div_ne_zero (one_add_sq_ne_zero h1 h2) (hG.ne_zero z hz)

lemma mEps_ne_zero (δ : ℝ) (z : ℂ) : mEps δ z ≠ 0 := Complex.exp_ne_zero _

lemma HAdm.apply_zero {F : ℂ → ℂ} {c1 : ℝ} (hF : HAdm F c1) : F 0 = 1 := by
  obtain ⟨C, r, hr, hj⟩ := hF.jet
  have h0 : (0 : ℂ) ∈ closure halfDisc := mem_closure_halfDisc (by simp) (by simp)
  have := hj 0 h0 (by simpa using hr)
  simp only [mul_zero, sub_zero, norm_zero] at this
  have h2 : ‖F 0 - 1‖ ≤ 0 := by simpa using this
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h2)

/-- **`cts:smooth-env` (1)**: class membership, normalisation, zero-freeness and jet of `F_δ`. -/
theorem fDelta_hAdm (hG : OuterDatum W K g1 G) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    HAdm (fDelta G δ) (-g1 - δ / 2) :=
  (comb_regularisation hG hδ0 hδ1).1

theorem fDelta_zero (hG : OuterDatum W K g1 G) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    fDelta G δ 0 = 1 :=
  (fDelta_hAdm hG hδ0 hδ1).apply_zero

theorem fDelta_ne_zero (hG : OuterDatum W K g1 G) {z : ℂ} (hz : z ∈ closure halfDisc \ singPts) :
    fDelta G δ z ≠ 0 :=
  mul_ne_zero (mEps_ne_zero δ z) (fStar_ne_zero hG hz)

theorem fDelta_conj (hG : OuterDatum W K g1 G) (hδ0 : 0 < δ) (hδ1 : δ < 1) {z : ℂ}
    (hz : z ∈ halfDisc) :
    fDelta G δ (starRingEnd ℂ z) = starRingEnd ℂ (fDelta G δ z) :=
  (fDelta_hAdm hG hδ0 hδ1).conj z hz

theorem slope0_fDelta (hG : OuterDatum W K g1 G) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    slope0 (fDelta G δ) = ((-g1 - δ / 2 : ℝ) : ℂ) :=
  (fDelta_hAdm hG hδ0 hδ1).slope0_eq

/-- **`cts:Jpf-lim`, first half**: `0 ≤ 𝒥[F_δ] - c_0^* ≤ 25 α_C δ²`. -/
theorem combJ_fDelta_bounds (hG : OuterDatum W K g1 G) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    0 ≤ combJ W K (fDelta G δ) - c0StarOf g1 ∧
      combJ W K (fDelta G δ) - c0StarOf g1 ≤ 25 * alphaC * δ ^ 2 := by
  obtain ⟨-, h1, h2⟩ := comb_regularisation hG hδ0 hδ1
  unfold c0StarOf
  exact ⟨sub_nonneg.mpr h1, by unfold fDelta; linarith⟩

/-- `𝖡[F_*] = 0` (`cts:Jpf-lim` proof, `ctu:J-quad`). -/
theorem combB_fStar (hG : OuterDatum W K g1 G) : combB W K (fStar G) = 0 := by
  unfold combB
  rw [(fStar_hAdm hG).slope0_eq, comb_attained hG]
  simp

/-- The band functional of `F_δ` in terms of `𝒥`: `𝖡[F_δ] = 𝒥[F_δ] + α_tip F_δ'(0)`, with `F_δ'(0) = -g₁ - δ/2`. -/
theorem combB_fDelta_eq (hG : OuterDatum W K g1 G) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    combB W K (fDelta G δ) = combJ W K (fDelta G δ) - alphaTip * (g1 + δ / 2) := by
  unfold combB
  rw [slope0_fDelta hG hδ0 hδ1]
  simp only [Complex.ofReal_re]
  ring

/-- **`cts:Jpf-lim`, second half**: `|𝖡[F_δ] + (α_tip/2) δ| ≤ 25 α_C δ²`
(so `𝖡[F_δ] = -(α_tip/2) δ + O(δ²)`). -/
theorem combB_fDelta_bounds (hG : OuterDatum W K g1 G) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    |combB W K (fDelta G δ) + alphaTip / 2 * δ| ≤ 25 * alphaC * δ ^ 2 := by
  obtain ⟨h1, h2⟩ := combJ_fDelta_bounds hG hδ0 hδ1
  rw [combB_fDelta_eq hG hδ0 hδ1]
  unfold c0StarOf at h1 h2
  rw [abs_le]
  constructor <;> nlinarith only [h1, h2]

/-- The `𝒥`-value in terms of the band part and the tip slope `c_1(δ) = F_δ'(0)`:
`𝒥[F_δ] = 𝖡[F_δ] - α_tip c_1(δ)` (the combination entering `eq:gp-upper-final`). -/
theorem combJ_fDelta_eq_B (hG : OuterDatum W K g1 G) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    combJ W K (fDelta G δ) = combB W K (fDelta G δ) - alphaTip * (-g1 - δ / 2) := by
  rw [combB_fDelta_eq hG hδ0 hδ1]; ring

end

/-- **`cts:smooth-env` (1), Virasoro instance** (`W = Wslit`, `K = Kedge`, `G = Gout`): `F_δ ∈ H_adm` with
`c_1(δ) = -g₁ - δ/2`, `g₁ = g1Vir`, zero-free, `F_δ(0) = 1`, `0 ≤ 𝒥[F_δ] - c_0^* ≤ 25 α_C δ²` with the closed
form `c_0^* = c0Star`, and `|𝖡[F_δ] + (α_tip/2) δ| ≤ 25 α_C δ²`. -/
theorem smooth_env_one_virasoro {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    HAdm (fDelta Gout δ) (-g1Vir - δ / 2) ∧
    (∀ z ∈ closure halfDisc \ singPts, fDelta Gout δ z ≠ 0) ∧
    fDelta Gout δ 0 = 1 ∧
    (0 ≤ combJ Wslit Kedge (fDelta Gout δ) - c0Star ∧
      combJ Wslit Kedge (fDelta Gout δ) - c0Star ≤ 25 * alphaC * δ ^ 2) ∧
    |combB Wslit Kedge (fDelta Gout δ) + alphaTip / 2 * δ| ≤ 25 * alphaC * δ ^ 2 := by
  have hG := gout_outerDatum_g1Out
  have e1 := g1Out_eq_g1Vir
  have e0 : c0Star = c0StarOf g1Out := by rw [c0Star_eq_c0StarOf, e1]
  rw [← e1]
  refine ⟨fDelta_hAdm hG hδ0 hδ1, fun z hz => fDelta_ne_zero hG hz, fDelta_zero hG hδ0 hδ1, ?_,
    combB_fDelta_bounds hG hδ0 hδ1⟩
  rw [e0]
  exact combJ_fDelta_bounds hG hδ0 hδ1

end FormalResearch.ModularBootstrap.FiveTerm

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.combB_fDelta_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.combB_fDelta_bounds

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.smooth_env_one_virasoro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.smooth_env_one_virasoro
