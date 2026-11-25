module

public import FormalResearch.SignUncertainty.CeLiftPhysical
public import FormalResearch.SignUncertainty.HbUpperM1
public import FormalResearch.SignUncertainty.MiddleBandPositivityDual

/-!
# The physical sign of `thm:ce-hb-lift` (M6): helpers and the source-family input

Coefficients of the dual-side seed `D_η = airySeedU2 (1 + γ₂δ) (b₀ + η) (-γ₂δ)` (`δ = Kε`, `b₀ = γ₁δ - γ₂δ - (δ - ∫ S_c)`), the
admissible tuning predicate `CeTune`, and its existence (`ceTune_exists`) from `ceLift_tune`.

`CeSourceFamily S` is the **hypothesis structure** under which `ceLift_physical` (in `CeLiftSignMain`) holds: it collects the consequences of Lemma `O.12`
(`ceo:conv`) that the lift uses.  It is not discharged in this file; it is instantiated for `convSource` in `ConvSourceFamily.lean`. `CeHankelPair` and the headline `ce_hb_lift_m1`
remain open.  Field by field (TeX item behind it; see `ConvSourceFamily.lean` for the proofs of the weak forms used here):
* `hasU2`: `hasU2_convSource` (proved, `O.12(1)`, `(3)`);
* `mass`: `O.12(1)`-`(2)`: `γ ε ≤ ∫ S_c = ∫ w_c ≤ (γ + θ C_p √λ) ε` for every `c` (from `‖w_h‖₁ ≤ C_p √h`; `convSource_mass` gives the asymptotic form for `ε ≤ 1/√λ`);
* `tail`: `ConvTailData` at the spline width `β₁ K ε / 2`, order `m = 4`: `I_main[S_c]` from `O.12(7)` (far transfer; the range `L ≤ L_F` from `middle_transfer_gt1`),
  `I_dual[S_c]` from `GT.2b` with `A = C ε^{9/2}` (`O.12(5)`); the structure asks only for fixed-`c` decay as `ξ → ∞` (constants depending on `K`, `c`), which is weaker than
  the uniform TeX statements;
* `edge`: `‖W_{S_c}(c^{1/3})‖ ≤ C c^{-5/6}`, implied with room by `O.12(6)`, `|W_{S_c}(w)| ≤ C ε (1 + Re w)^{-11/2}`, at `w = ε⁻¹` (which gives `C ε^{13/2}`);
* `dual`: `O6DualEst` for the reflected seed `-S_c`: `(e3)` from `O.12(5)` and `GT.2b`, and the window bound `O(ξ⁻¹ ε^{7/2})` by absolute reflected integration (`ce_hb_lift.tex`).
`ceSourceFamily_nonvacuous` (module `CeSourceFamilyWitness`) shows that the structure is satisfiable.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

/-- `δ = K ε ≤ 1/2` for `8 K³ ≤ c`. -/
lemma ce_delta_half {K c : ℝ} (hK : 1 ≤ K) (hc : 0 < c) (hc8 : 8 * K ^ 3 ≤ c) : K * liftEps c ≤ 1 / 2 := by
  have hε : 0 < liftEps c := liftEps_pos hc
  have hcube : liftEps c ^ 3 * c = 1 := liftEps_cube_mul hc
  have hKe3 : (K * liftEps c) ^ 3 * c = K ^ 3 := by
    calc (K * liftEps c) ^ 3 * c = K ^ 3 * (liftEps c ^ 3 * c) := by ring
      _ = K ^ 3 := by rw [hcube, mul_one]
  by_contra hcon
  push_neg at hcon
  have h2 : (1 / 2 : ℝ) ^ 3 < (K * liftEps c) ^ 3 := pow_lt_pow_left₀ hcon (by norm_num) (by norm_num)
  have h3 := mul_lt_mul_of_pos_right h2 hc
  rw [hKe3] at h3
  norm_num at h3
  linarith

/-- `δ = K ε ≤ δ₁` for `(K/δ₁)³ ≤ c`. -/
lemma ce_delta_le {K c δ₁ : ℝ} (hK : 0 < K) (hδ₁ : 0 < δ₁) (hc : 0 < c) (hcδ : (K / δ₁) ^ 3 ≤ c) :
    K * liftEps c ≤ δ₁ := by
  have hε : 0 < liftEps c := liftEps_pos hc
  have hcube : liftEps c ^ 3 * c = 1 := liftEps_cube_mul hc
  have hKe3 : (K * liftEps c) ^ 3 * c = K ^ 3 := by
    calc (K * liftEps c) ^ 3 * c = K ^ 3 * (liftEps c ^ 3 * c) := by ring
      _ = K ^ 3 := by rw [hcube, mul_one]
  have h2 : K ^ 3 ≤ δ₁ ^ 3 * c := by
    have := hcδ
    rw [div_pow, div_le_iff₀ (by positivity)] at this
    linarith
  have h3 : (K * liftEps c) ^ 3 ≤ δ₁ ^ 3 := by
    by_contra hcon
    push_neg at hcon
    have := mul_lt_mul_of_pos_right hcon hc
    rw [hKe3] at this
    linarith
  exact le_of_pow_le_pow_left₀ (by norm_num) hδ₁.le h3

lemma hasU2_integrable_real {X : ℝ → ℝ} (h : HasU2 X) : Integrable X := by
  simpa using (h.integrable 0 (by simp)).re

/-- The `u`-independent coefficient `b₀` of the dual-side seed (mass of the seed equal to the mass of `S_c`). -/
noncomputable def ceDb0 (γ₁ γ₂ : ℝ) (S : ℝ → ℝ → ℝ) (K c : ℝ) : ℝ :=
  γ₁ * (K * liftEps c) - γ₂ * (K * liftEps c) - (K * liftEps c - ∫ u : ℝ, S c u)

/-- The tuning predicate: `η` is at most `K ε`, obeys the bound of `ceLift_tune`, and makes `f₋(0) = 0`. -/
def CeTune (γ₁ γ₂ : ℝ) (S : ℝ → ℝ → ℝ) (K c η : ℝ) : Prop :=
  |η| ≤ K * liftEps c ∧
  |η| ≤ 2 / ceK * (‖liftSymbol (airySeedU2 (1 + γ₂ * (K * liftEps c)) (ceDb0 γ₁ γ₂ S K c) (-(γ₂ * (K * liftEps c))))
        (ceBeta1 * K * liftEps c / 2) 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ)‖ +
      ‖liftSymbol (S c) (ceBeta1 * K * liftEps c / 2) 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ)‖) ∧
  liftSymbol (fun u => airySeedU2 (1 + γ₂ * (K * liftEps c)) (ceDb0 γ₁ γ₂ S K c + η) (-(γ₂ * (K * liftEps c))) u +
      (-1) * S c u) (ceBeta1 * K * liftEps c / 2) 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ) -
    liftSymbol (fun u => airySeedU2 (1 + γ₂ * (K * liftEps c)) (ceDb0 γ₁ γ₂ S K c + η) (-(γ₂ * (K * liftEps c))) u +
      (-1) * S c u) (ceBeta1 * K * liftEps c / 2) 4 0 = 0

/-- Existence of the tuning `η` when the edge values are small. -/
theorem ceTune_exists (γ₁ γ₂ : ℝ) (S : ℝ → ℝ → ℝ) {K c : ℝ} (hK : 0 < K) (hc : 0 < c) (hS : HasU2 (S c))
    (hmass : ∫ u : ℝ, airySeedU2 (1 + γ₂ * (K * liftEps c)) (ceDb0 γ₁ γ₂ S K c) (-(γ₂ * (K * liftEps c))) u =
      ∫ u : ℝ, S c u)
    (hgx : |(liftSymbol (ceG1 (airyZero 1)) (ceBeta1 * K * liftEps c / 2) 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ)).re| ≤ ceK / 2)
    (hsmall : 2 / ceK * (‖liftSymbol (airySeedU2 (1 + γ₂ * (K * liftEps c)) (ceDb0 γ₁ γ₂ S K c)
        (-(γ₂ * (K * liftEps c)))) (ceBeta1 * K * liftEps c / 2) 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ)‖ +
      ‖liftSymbol (S c) (ceBeta1 * K * liftEps c / 2) 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ)‖) ≤ K * liftEps c) :
    ∃ η : ℝ, CeTune γ₁ γ₂ S K c η := by
  obtain ⟨η, hη, he⟩ := ceLift_tune hS (1 + γ₂ * (K * liftEps c)) (ceDb0 γ₁ γ₂ S K c) (-(γ₂ * (K * liftEps c))) 4
    (x := c ^ (1 / 3 : ℝ)) (Real.rpow_nonneg hc.le _) hmass hgx
  exact ⟨η, hη.trans hsmall, hη, he⟩


/-- **The input on the source family `S_c`** for the physical sign of `thm:ce-hb-lift` (the consequences of Lemma `O.12`, `ceo:conv`,
that the lift uses): class `HasU2`; mass `≍ ε`; the one-sided tail data (`ConvTailData`); the edge bound `|W_{S_c}(c^{1/3})| ≲ c^{-5/6}`
at the spline width `β₁ K ε / 2`; and the reflected estimates `O6DualEst` for `-S_c`.  This structure is the hypothesis
under which `ceLift_physical` holds; it is instantiated for the convolution source in `ConvSourceFamily.lean` (`ceSourceFamily_convSource`,
`ceSourceFamily_convSource_paper`; the `edge` and `dual` fields there are the weak forms stated here, not the sharp `O.12(5)`, `O.12(6)`). -/
structure CeSourceFamily (S : ℝ → ℝ → ℝ) : Prop where
  hasU2 : ∀ {c : ℝ}, 2000 ≤ c → HasU2 (S c)
  mass : ∃ m₀ M₀ : ℝ, 0 < m₀ ∧ 0 < M₀ ∧ ∀ {c : ℝ}, 2000 ≤ c →
    m₀ * liftEps c ≤ ∫ u : ℝ, S c u ∧ ∫ u : ℝ, S c u ≤ M₀ * liftEps c
  tail : ∀ {K c : ℝ}, 1 ≤ K → 2000 ≤ c → 8 * K ^ 3 ≤ c → ConvTailData (S c) (ceBeta1 * K * liftEps c / 2) 4 c
  edge : ∀ K : ℝ, 1 ≤ K → ∃ C : ℝ, 0 ≤ C ∧ ∀ {c : ℝ}, 2000 ≤ c → 8 * K ^ 3 ≤ c →
    ‖liftSymbol (S c) (ceBeta1 * K * liftEps c / 2) 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ)‖ ≤ C * c ^ (-(5 / 6 : ℝ))
  dual : O6DualEst 4 (fun _ c u => -S c u)

lemma airySeedU2_zero_one_zero : airySeedU2 0 1 0 = ceG1 (airyZero 1) := by
  funext u; simp [airySeedU2]

/-- info: 'FormalResearch.SignUncertainty.ceTune_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ceTune_exists

end FormalResearch.SignUncertainty
