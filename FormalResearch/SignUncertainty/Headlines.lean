module

public import FormalResearch.SignUncertainty.Radii
public import FormalResearch.SignUncertainty.RadialCompactnessProof
public import FormalResearch.SignUncertainty.OneProfileEnvelope
public import FormalResearch.SignUncertainty.EuclidRadialProjection
public import FormalResearch.SignUncertainty.ShellGapHankel
public import FormalResearch.SignUncertainty.ShellGapExtract
public import FormalResearch.SignUncertainty.HeadlineDefs
public import FormalResearch.SignUncertainty.HankelThresholds
public import FormalResearch.SignUncertainty.CEShellReduction
public import FormalResearch.SignUncertainty.CeCanonicalDefs
public import FormalResearch.SignUncertainty.HbZeroEnum
public import FormalResearch.SignUncertainty.ShellGapOrigin
public import FormalResearch.SignUncertainty.ShellGapEndpoint
public import FormalResearch.SignUncertainty.ShellGapOriginFloor
public import FormalResearch.SignUncertainty.CeCanonicalSide
public import FormalResearch.SignUncertainty.HbMultilevelDefs
public import FormalResearch.SignUncertainty.AiryNodeSquare
public import FormalResearch.SignUncertainty.AiryActiveHeight
public import FormalResearch.SignUncertainty.CeTerminalDeflation
public import FormalResearch.SignUncertainty.AiryNodeSign
public import FormalResearch.SignUncertainty.AiryRationalDensity
public import FormalResearch.SignUncertainty.CeHbLift
public import FormalResearch.SignUncertainty.CeShellReductionProved

/-!
# Paper I headline theorems from one input structure each (M0 skeleton)

Source: `CFT/sign_uncertainty/paper/sign_uncertainty_core.tex`, introduction:
`thm:intro-radii`, `thm:intro-hb`, `thm:intro-gap`. (The old `thm:intro-separation` was deleted from the paper; its
conditional proof is kept, not as a headline, in `SignSeparationLimsup.lean`.)

Each headline is stated on the concrete objects of `Radii.lean` (Euclidean `A_sign^±(d)`, `r_CE(d)`,
the prescribed-shell class, the Bessel-kernel Hankel thresholds) with the paper's constants, and is
proved from an input structure whose fields are, one-to-one, the TeX theorems the paper's proof cites
(field names are the TeX labels where the paper has one: `hb_thresholds_lower/upper`, `shell_reduction`,
`ce_hb_lift`, ...; `gt:7.9`, the Euclidean radii as Hankel thresholds, is the theorem
`hankel_euclid_dictionary` and no longer a field; `hb_thresholds_lower` (`HankelThresholds.lean`) and
`shell_reduction_m1` (`shell_reduction_m1_proved`, `CEShellReduction.lean`) are theorems and no longer fields,
and `shell_reduction_airy : ShellReduction ShellHBData.airy` is proved).
**A field is an open theorem about the concrete objects**; progress is the number of open fields, and a
field is discharged only by proving it (then it is dropped from the structure). The input structures
deliberately have no `*_nonvacuous` witness: each field is an open theorem of the paper, so a witness
would be the theorem itself (deliberate deviation from the usual non-vacuity requirement); where a field's
satisfiability is in doubt the docstring says so. The three headlines are stated as in the paper.

Headlines and their inputs (open fields in bold):

* `thm_intro_radii` (`thm:intro-radii`, `gt:7.9`, `gt:7.12`, `gt:7.12a`), from `RadiiInputs`:
  `hb_thresholds_upper` (`thm:hb-thresholds` upper half at `(P,Q) = (1,0)`, i.e. `u1co:O9p`; proved as
  `hbThresholdsUpper` in `HbUpperM1.lean`, which imports this file, so it is a field here only for import order);
  `ce_hb_lift_m1` is proved via `ce_hb_lift_proved ShellHBData.airy` (`CeHbLift.lean`), making `thm_intro_radii_ce`
  unconditional. Proved here from these and from `hb_thresholds_lower`, `shell_reduction_m1_proved`: the gluing
  `ce_radius_airy_order_of_bounds`, the origin option `constrained_threshold_eq_unconstrained`, the density expansion
  `ce_volume_expansion`.
* `thm_intro_hb` (`thm:intro-hb` = `u1cl:multilevel` = `thm:hb-thresholds`, all Hermite–Biehler levels), from
  `HbMultilevelInputs D` (`HbMultilevelDefs.lean`): **`lower`** (lower half; `fto1:thm`, `fto1:mellin`, `gt:7.7p`,
  `u1cl:rep`, TE.0'; proved for `(P,Q) = (1,0)` as `hbMultilevelLower_airy`), **`construction`** (`u1co:O9p`, all-level
  seeds), **`attainment`** (`gt:7.9a`, `lem:finite-hankel-compactness`), **`exact_origin`** (`gt:7.9b`).
* `thm_ce_canonical_iff` (`thm:intro-gap` = `thm:ce-canonical-iff`, parts (1)-(4), with (i)-(iv); the zero enumeration `t` exists and is unique: `HbZeroEnum.lean`), unconditional (`CeCanonicalInputs D t` has no open fields;
  `shell_reduction` (`thm:ce-shell-reduction`) is proved as `shellReduction_proved` in `CeShellReductionProved.lean`);
  `ce_hb_lift` (`thm:ce-hb-lift`, weak positivity) is proved as `ce_hb_lift_proved` (`CeHbLift.lean`) and no longer a field,
  and `shifted_lift` (`thm:ce-shifted-lift`) is proved as `ce_shifted_lift_proved` (`CeShiftedLift.lean`) and no longer
  a field, giving unconditional `ce_airy_transfer_upper` (`thm:ce-airy-transfer`(1) upper bound,
  `AiryRationalDensity.lean`). The extraction and
  constraint system `eq:ce-laplace-constraint` of `thm:ce-shell-gap` (Hankel form `HankelShellGapLimit`) is the
  theorem `hankelShellGapLimit_proved` (`ShellGapExtract.lean`) and no longer a field; `thm:airy-square-attained` (1), (3) is the theorem `airySquareAttained` (`CeCanonicalDefs.lean`, from
  `AirySquareSimple.lean`) and no longer a field, nor are `lem:airy-square-bound` (`Λ_m > a_m`: `airyLambdaSection_hb_gt_airyZero`, `AirySquareBound.lean`),
  `lem:airy-node-square` (`λ > τ_N > t_{m+e}`: `airy_node_square`, `AiryNodeSquare.lean`), `lem:airy-active-height`
  (`airy_active_height`, `AiryActiveHeight.lean`), `thm:airy-node-sign` (`airy_node_sign`, `airy_node_sum`,
  `AiryNodeSign.lean`), or `lem:ce-terminal-deflation` (`terminal_cardinal_integral`, `ce_terminal_deflation_full`, `CeTerminalDeflation.lean`); the `v = t_m` endpoint clause
  `ShellGapEndpoint D` is the theorem `shellGapEndpoint_proved` (`ShellGapEndpoint.lean`) and no longer a field, and
  `thm_ce_shell_gap` is proved; `one_profile_envelope` (`gt:3.1` envelope used in `prop:ce-one-profile`) is a theorem
  (`OneProfileEnvelope.lean`). Proved here: `one_profile_feasible_iff`, `one_profile_maximizer_exists`,
  `one_profile_threshold_le_and_endpoint_iff` (`prop:ce-one-profile`, `uLP_eq_tm_iff`), `even_m_laplace_sign`,
  the chain `Λ_M ≤ λ < u_sh ≤ u_LP` from the witness of `thm:airy-square-attained` and `D.uniqueness`
  (`lem:hb-uniqueness`), and the cycle (i) ⇔ (ii) ⇔ (iii) ⇔ (iv).

Conventions. `c = d/2`, `A = |a₁|/β₁` (`airyOrderCoeff`), `airyOrderModel d = d/(2π²) + A (d/2)^{1/3}`.
Radii whose defining set is empty are `+∞` in the paper; the statements below that involve the
prescribed-shell radius quantify over the members of `ceShellRadiusSet`. For the Euclidean radii and
`hankelT` the real `sInf` is used; for `d ≥ 2` the defining sets are nonempty (this is part of the
field `hb_thresholds_upper` (the theorem `hbThresholdsUpper`) for the Hankel side, and the Euclidean sets are then nonempty by
`signWitness_of_hankelFeasible`), so the junk value `sInf ∅ = 0` never matters for a true statement.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real ENNReal Polynomial FourierTransform RealInnerProductSpace

namespace FormalResearch.SignUncertainty

open FormalResearch.Special
open FormalResearch.CohnElkies

/-! ### Elementary bookkeeping -/

/-- A bound valid for `d ≥ d₁` extends to all `d` with a larger constant. -/
lemma exists_abs_bound_nat {f : ℕ → ℝ} {d₁ : ℕ} {B : ℝ} (h : ∀ d : ℕ, d₁ ≤ d → |f d| ≤ B) :
    ∃ C : ℝ, ∀ d : ℕ, |f d| ≤ C := by
  refine ⟨|B| + ∑ d ∈ Finset.range d₁, |f d|, fun d => ?_⟩
  have hs : 0 ≤ ∑ d ∈ Finset.range d₁, |f d| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  by_cases hd : d₁ ≤ d
  · linarith [h d hd, le_abs_self B]
  · have : |f d| ≤ ∑ d ∈ Finset.range d₁, |f d| :=
      Finset.single_le_sum (f := fun d => |f d|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.mpr (not_le.mp hd))
    linarith [abs_nonneg B]

/-- The one-level threshold lies within `C` of the Airy-order model, from the two halves. -/
lemma hankelT_sub_model_le {c ε C₁ C₂ : ℝ} (hlow : ∀ T f, IsHankelFeasible c ε T f →
      c / π ^ 2 + airyOrderCoeff * c ^ (1 / 3 : ℝ) - C₁ ≤ T)
    (hup : ∃ T f, IsHankelFeasible c ε T f ∧ T ≤ c / π ^ 2 + airyOrderCoeff * c ^ (1 / 3 : ℝ) + C₂) :
    |hankelT ε c - (c / π ^ 2 + airyOrderCoeff * c ^ (1 / 3 : ℝ))| ≤ max C₁ C₂ := by
  obtain ⟨T₀, f₀, hf₀, hT₀⟩ := hup
  have hbdd : BddBelow {T : ℝ | ∃ f, IsHankelFeasible c ε T f} :=
    ⟨c / π ^ 2 + airyOrderCoeff * c ^ (1 / 3 : ℝ) - C₁, fun T ⟨f, hf⟩ => hlow T f hf⟩
  have h1 : hankelT ε c ≤ T₀ := csInf_le hbdd ⟨f₀, hf₀⟩
  have h2 : c / π ^ 2 + airyOrderCoeff * c ^ (1 / 3 : ℝ) - C₁ ≤ hankelT ε c :=
    le_csInf ⟨T₀, f₀, hf₀⟩ fun T ⟨f, hf⟩ => hlow T f hf
  rw [abs_le]
  constructor <;> linarith [le_max_left C₁ C₂, le_max_right C₁ C₂]

/-- `airyOrderModel d` is the model `c/π² + A c^{1/3}` at `c = d/2`. -/
lemma airyOrderModel_eq (d : ℕ) :
    airyOrderModel d = ((d : ℝ) / 2) / π ^ 2 + airyOrderCoeff * ((d : ℝ) / 2) ^ (1 / 3 : ℝ) := by
  unfold airyOrderModel; ring

/-! ### Statements of the TeX theorems used as inputs -/

/-- `prop:ce-one-profile`, attainment step (uniform envelope from the proof of `gt:3.1`): normalised
one-profile witnesses at thresholds above a feasible `u₀` obey a common bound
`C (1 + |z|)^ν e(z)`. -/
def OneProfileEnvelope (D : ShellHBData) : Prop :=
  ∀ u₀ : ℝ, OneProfileFeasible D u₀ → ∃ C ν : ℝ, 0 ≤ C ∧ ∀ u : ℝ, u₀ ≤ u →
    ∀ H : ℂ → ℂ, OneProfileFeasibleWitness D u H → (∫ x : ℝ, ‖H (x : ℂ)‖) = 1 →
      ∀ z : ℂ, ‖H z‖ ≤ C * (1 + ‖z‖) ^ ν * airyEnv z

/-- `prop:ce-one-profile`, attainment step: proved (`one_profile_envelope_aux`, `OneProfileEnvelope.lean`). -/
theorem one_profile_envelope (D : ShellHBData) : OneProfileEnvelope D := one_profile_envelope_aux D

/-! ### Input structures -/

/-- The concrete Bessel kernel `hankelPhi c` is a `HankelKernelData c` for `c ≥ 1`: proved
(`hankelKernelData`, `HankelBesselData.lean`; no input needed). -/
theorem bessel_kernel_data (c : ℝ) (hc : 1 ≤ c) :
    ∃ K : HankelKernelData c, K.φ = hankelPhi c :=
  ⟨hankelKernelData (by linarith), rfl⟩

/-- `thm:hb-thresholds` at one level: the lower half `HbThresholdsLower` is the theorem `hb_thresholds_lower`
(`HankelThresholds.lean`); the upper half `HbThresholdsUpper` is the theorem `hbThresholdsUpper` (`HbUpperM1.lean`).
It stays a field here only because `HbUpperM1` imports this file; supply it with `⟨hbThresholdsUpper⟩`. -/
structure OneLevelThresholds : Prop where
  hb_thresholds_upper : HbThresholdsUpper

/-- Inputs of `thm:intro-radii` (`ce_hb_lift_m1` is proved in `CeHbLift.lean` as
`ce_hb_lift_proved ShellHBData.airy` and no longer a field). -/
structure RadiiInputs : Prop extends OneLevelThresholds where

/-- `gt:7.5`, first claim, one level, `ε = -1`: `liminf c^{-1/3}(T_c - c/π²) ≥ A`
(from `radial_compactness` via `radial_rigidity_liminf_ereal`). -/
theorem radial_rigidity_lower :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ c : ℝ in atTop, ∀ (T : ℝ) (f : ℝ → ℝ),
      IsHankelFeasible c (-1) T f → c / π ^ 2 + (airyOrderCoeff - ε) * c ^ (1 / 3 : ℝ) ≤ T :=
  radial_rigidity_lower_of_compactness radial_compactness

/-! ### Headline A and B: `thm:intro-radii` -/

section Radii

variable (I : RadiiInputs)
include I

/-- For all large `d`, the Euclidean radii satisfy `A_sign^±(d)²/2 = T^{±,0}_{d/2}` with `T^{-,0} =
T^{-}` (the exact origin option, `gt:7.9b`) and `T^±_c` within `O(1)` of `c/π² + A c^{1/3}`. -/
private lemma sign_radii_tail :
    ∃ (C : ℝ) (d₁ : ℕ), 2 ≤ d₁ ∧ ∀ d : ℕ, d₁ ≤ d →
      |aSignPos d ^ 2 / 2 - airyOrderModel d| ≤ C ∧ |aSignNeg d ^ 2 / 2 - airyOrderModel d| ≤ C := by
  obtain ⟨C₁, c₁, hlow⟩ := hb_thresholds_lower
  obtain ⟨C₂, c₂, hup⟩ := I.hb_thresholds_upper
  -- threshold for the exact origin option: `c/π² + A c^{1/3} - C₁ > c/(4π)`
  have hπ : 0 < 1 / π ^ 2 - 1 / (4 * π) := by
    have : 1 / (4 * π) < 1 / π ^ 2 := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith [Real.pi_gt_three, Real.pi_lt_four]
    linarith
  obtain ⟨c₃, hc₃⟩ : ∃ c₃ : ℝ, ∀ c : ℝ, c₃ ≤ c → C₁ < c * (1 / π ^ 2 - 1 / (4 * π)) := by
    refine ⟨(|C₁| + 1) / (1 / π ^ 2 - 1 / (4 * π)), fun c hc => ?_⟩
    rw [div_le_iff₀ hπ] at hc
    linarith [le_abs_self C₁]
  set c₄ : ℝ := max (max c₁ c₂) (max c₃ 1) with hc₄
  have hc₄1 : c₁ ≤ c₄ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hc₄2 : c₂ ≤ c₄ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hc₄3 : c₃ ≤ c₄ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hc₄4 : 1 ≤ c₄ := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨max C₁ C₂, ⌈2 * c₄⌉₊ + 2, by omega, fun d hd => ?_⟩
  have hc : c₄ ≤ (d : ℝ) / 2 := by
    have : (2 * c₄ : ℝ) ≤ ⌈2 * c₄⌉₊ := Nat.le_ceil _
    have : ((⌈2 * c₄⌉₊ + 2 : ℕ) : ℝ) ≤ d := by exact_mod_cast hd
    push_cast at this
    linarith
  set c : ℝ := (d : ℝ) / 2 with hc_def
  have hd2 : 2 ≤ d := by omega
  have hc0 : 0 < c := by linarith
  obtain ⟨hp, hn⟩ := hankel_euclid_dictionary d hd2
  have hnonneg : ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → ∃ T f, IsHankelFeasible c ε T f :=
    fun ε hε => by obtain ⟨T, f, hf, _⟩ := hup c (by linarith) ε hε; exact ⟨T, f, hf⟩
  have hb : ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
      |hankelT ε c - airyOrderModel d| ≤ max C₁ C₂ := fun ε hε => by
    rw [airyOrderModel_eq]
    exact hankelT_sub_model_le (fun T f hf => hlow c (by linarith) ε hε T f hf)
      (hup c (by linarith) ε hε)
  have hT0 : hankelT0 c = hankelT (-1) c := by
    refine hankelT0_eq_hankelT hc0 (bessel_kernel_data c (by linarith))
      (laguerre_odd_mode (by linarith)) (hnonneg (-1) (Or.inr rfl)) ?_
    have hmodel : 0 ≤ airyOrderCoeff * c ^ (1 / 3 : ℝ) :=
      mul_nonneg airyOrderCoeff_pos.le (Real.rpow_nonneg hc0.le _)
    have hlo : c / π ^ 2 + airyOrderCoeff * c ^ (1 / 3 : ℝ) - C₁ ≤ hankelT (-1) c :=
      le_csInf (hnonneg (-1) (Or.inr rfl)) fun T ⟨f, hf⟩ => hlow c (by linarith) (-1) (Or.inr rfl) T f hf
    have h3 := hc₃ c (by linarith)
    have e1 : c / π ^ 2 = c * (1 / π ^ 2) := by ring
    have e2 : c / (4 * π) = c * (1 / (4 * π)) := by ring
    rw [mul_sub] at h3
    linarith
  refine ⟨?_, ?_⟩
  · rw [hp]; exact hb 1 (Or.inl rfl)
  · rw [hn, hT0]; exact hb (-1) (Or.inr rfl)

end Radii

/-- The Laplace hypothesis of `thm:ce-hb-lift` holds at `m = 1`, `N = Ai` (`shellLaplaceF_m1_pos`). -/
lemma airy_laplace_negG_pos {y : ℝ} (hy : 0 < y) :
    0 < airyLaplace (fun u => -(ShellHBData.airy.G (u : ℂ)).re) y := by
  rw [airyLaplace_negG_eq]
  have hm1 : ShellHBData.airy.S.card = 1 :=
    ShellHBData.airy.m_eq.elim (fun h => h.2) (fun h => False.elim (h.1 rfl))
  exact mul_pos (Real.exp_pos _) (shellLaplaceF_m1_pos ShellHBData.airy hm1 hy)

lemma airy_S_card : ShellHBData.airy.S.card = 1 :=
  ShellHBData.airy.m_eq.elim (fun h => h.2) (fun h => False.elim (h.1 rfl))

section Radii2

variable (I : RadiiInputs)
include I

/-- **Headline A (`gt:7.9`, `thm:intro-radii`, both signs).** For every integer `d ≥ 2`,
`A_sign^±(d)²/2 = d/(2π²) + A (d/2)^{1/3} + O(1)` with `A = |a₁|/β₁`.

Proved from `RadiiInputs`; see the module docstring for the open field used
(`hb_thresholds_upper`; the lower half is the theorem `hb_thresholds_lower`). The second asymptotic form of `gt:7.9` (`A_sign(d)/√d`) is not restated. -/
theorem thm_intro_radii_sign :
    (∃ C : ℝ, ∀ d : ℕ, 2 ≤ d → |aSignPos d ^ 2 / 2 - airyOrderModel d| ≤ C) ∧
    (∃ C : ℝ, ∀ d : ℕ, 2 ≤ d → |aSignNeg d ^ 2 / 2 - airyOrderModel d| ≤ C) := by
  obtain ⟨C, d₁, -, h⟩ := sign_radii_tail I
  exact ⟨(exists_abs_bound_nat (f := fun d => aSignPos d ^ 2 / 2 - airyOrderModel d)
      (fun d hd => (h d hd).1)).imp fun C hC d _ => hC d,
    (exists_abs_bound_nat (f := fun d => aSignNeg d ^ 2 / 2 - airyOrderModel d)
      (fun d hd => (h d hd).2)).imp fun C hC d _ => hC d⟩

end Radii2

/-- **Headline B (`gt:7.12`, `gt:7.12a`, `thm:intro-radii`, Cohn–Elkies radius).** (In the paper `r_CE(d)`
is the Schwartz infimum; it equals `optimalL1CERadius d` by `ce_schwartz_radius_eq_L1_radius`.) For every integer
`d ≥ 2`, `r_CE(d)²/2 = d/(2π²) + A (d/2)^{1/3} + O(1)`, and the ball of radius `r_CE(d)/2` has volume
`(πd)^{-1/2} (e/(2π))^{d/2} exp(π² A (d/2)^{1/3} + O(1))`, in both the multiplicative
and the logarithmic form (`eq:intro-density`; the constant `-log π / 2` is absorbed in the `O(1)`).

Unconditional (proved from `ce_hb_lift_proved ShellHBData.airy` and `shell_reduction_m1_proved` by the gluing
`ce_radius_airy_order_of_bounds` and the Stirling expansion `ce_volume_expansion`). -/
theorem thm_intro_radii_ce :
    (∃ C : ℝ, ∀ d : ℕ, 2 ≤ d → |optimalL1CERadius d ^ 2 / 2 - airyOrderModel d| ≤ C) ∧
    (∃ c₁ c₂ : ℝ, 0 < c₁ ∧ ∀ d : ℕ, 2 ≤ d →
      c₁ * ((π * (d : ℝ)) ^ (-(1 / 2 : ℝ)) * (Real.exp 1 / (2 * π)) ^ ((d : ℝ) / 2) *
          Real.exp (π ^ 2 * airyOrderCoeff * ((d : ℝ) / 2) ^ (1 / 3 : ℝ))) ≤
        (volume : Measure (Euc d)).real (Metric.ball 0 (optimalL1CERadius d / 2)) ∧
      (volume : Measure (Euc d)).real (Metric.ball 0 (optimalL1CERadius d / 2)) ≤
        c₂ * ((π * (d : ℝ)) ^ (-(1 / 2 : ℝ)) * (Real.exp 1 / (2 * π)) ^ ((d : ℝ) / 2) *
          Real.exp (π ^ 2 * airyOrderCoeff * ((d : ℝ) / 2) ^ (1 / 3 : ℝ)))) ∧
    (∃ C' : ℝ, ∀ d : ℕ, 2 ≤ d →
      |Real.log ((volume : Measure (Euc d)).real (Metric.ball 0 (optimalL1CERadius d / 2))) -
        (((d : ℝ) / 2) * Real.log (Real.exp 1 / (2 * π)) +
          π ^ 2 * airyOrderCoeff * ((d : ℝ) / 2) ^ (1 / 3 : ℝ) - (1 / 2 : ℝ) * Real.log (d : ℝ))| ≤ C') := by
  obtain ⟨C_lo, d_lo, hlo0⟩ := shell_reduction_m1_proved
  -- the upper half from `ce_hb_lift_proved` at `D = airy`, no shells, `R_off = 0`
  obtain ⟨K₀, d_hi, hhi0⟩ := ce_hb_lift_proved ShellHBData.airy (fun y hy => (airy_laplace_negG_pos hy).le) 0 le_rfl
  have hA : -(ShellHBData.airy.tm / hankelBeta1) = airyOrderCoeff := by
    unfold airyOrderCoeff
    rw [abs_of_neg (airyZero_neg 1)]
    show -(airyZero 1 / hankelBeta1) = -airyZero 1 / hankelBeta1
    ring
  set d₀ : ℕ := max (max d_lo d_hi) 2 with hd₀
  have hd₀2 : 2 ≤ d₀ := le_max_right _ _
  have hlo : ∀ d : ℕ, d₀ ≤ d →
      (d : ℝ) / (2 * π ^ 2) + airyOrderCoeff * ((d : ℝ) / 2) ^ (1 / 3 : ℝ) - C_lo ≤
        optimalL1CERadius d ^ 2 / 2 := fun d hd => by
    have := hlo0 d (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hd)
    unfold airyOrderModel at this
    exact this
  have hhi : ∀ d : ℕ, d₀ ≤ d → ∃ r h, IsContinuousL1CEAdmissible d r h ∧
      r ^ 2 / 2 ≤ (d : ℝ) / (2 * π ^ 2) + airyOrderCoeff * ((d : ℝ) / 2) ^ (1 / 3 : ℝ) + K₀ := by
    intro d hd
    obtain ⟨R, ⟨h, hh⟩, hR⟩ := hhi0 d (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hd)
      (fun _ _ => 0) (fun _ _ => by simp)
    refine ⟨R, h, hh.toIsContinuousL1CEAdmissible, ?_⟩
    rw [← hA]
    linarith
  obtain ⟨-, ⟨C, hC⟩, -, -⟩ := ce_radius_airy_order_of_bounds hd₀2 airyOrderCoeff C_lo K₀ hlo hhi
  have hr_pos : ∀ d : ℕ, 2 ≤ d → 0 < optimalL1CERadius d := fun d hd =>
    (optimalCERadius_pos_and_bound_ge (by omega : 1 ≤ d)).2.1
  obtain ⟨hmult, hlog⟩ := ce_volume_expansion airyOrderCoeff hr_pos ⟨C, hC⟩
  exact ⟨⟨C, fun d hd => by unfold airyOrderModel; exact hC d hd⟩, hmult, hlog⟩

/-- **`thm:intro-radii`** (`gt:7.9`, `gt:7.12`, `gt:7.12a`): the three radii at Airy order, and the
volume/density expansion of the Cohn–Elkies ball (`eq:intro-density`). -/
theorem thm_intro_radii (I : RadiiInputs) :
    ((∃ C : ℝ, ∀ d : ℕ, 2 ≤ d → |aSignPos d ^ 2 / 2 - airyOrderModel d| ≤ C) ∧
      (∃ C : ℝ, ∀ d : ℕ, 2 ≤ d → |aSignNeg d ^ 2 / 2 - airyOrderModel d| ≤ C)) ∧

      (∃ C : ℝ, ∀ d : ℕ, 2 ≤ d → |optimalL1CERadius d ^ 2 / 2 - airyOrderModel d| ≤ C) ∧
      (∃ c₁ c₂ : ℝ, 0 < c₁ ∧ ∀ d : ℕ, 2 ≤ d →
        c₁ * ((π * (d : ℝ)) ^ (-(1 / 2 : ℝ)) * (Real.exp 1 / (2 * π)) ^ ((d : ℝ) / 2) *
            Real.exp (π ^ 2 * airyOrderCoeff * ((d : ℝ) / 2) ^ (1 / 3 : ℝ))) ≤
          (volume : Measure (Euc d)).real (Metric.ball 0 (optimalL1CERadius d / 2)) ∧
        (volume : Measure (Euc d)).real (Metric.ball 0 (optimalL1CERadius d / 2)) ≤
          c₂ * ((π * (d : ℝ)) ^ (-(1 / 2 : ℝ)) * (Real.exp 1 / (2 * π)) ^ ((d : ℝ) / 2) *
            Real.exp (π ^ 2 * airyOrderCoeff * ((d : ℝ) / 2) ^ (1 / 3 : ℝ)))) ∧
      (∃ C' : ℝ, ∀ d : ℕ, 2 ≤ d →
        |Real.log ((volume : Measure (Euc d)).real (Metric.ball 0 (optimalL1CERadius d / 2))) -
          (((d : ℝ) / 2) * Real.log (Real.exp 1 / (2 * π)) +
            π ^ 2 * airyOrderCoeff * ((d : ℝ) / 2) ^ (1 / 3 : ℝ) - (1 / 2 : ℝ) * Real.log (d : ℝ))| ≤ C') :=
  ⟨thm_intro_radii_sign I, thm_intro_radii_ce⟩

/-! ### Headline `thm:intro-hb` (`u1cl:multilevel`) -/


/-- elementary: for large `c`, `c/π² - a c^{1/3} - b > 0`. -/
lemma exists_pos_level (a b : ℝ) : ∃ c₀ : ℝ, 1 ≤ c₀ ∧ ∀ c : ℝ, c₀ ≤ c → 0 < c / π ^ 2 - a * c ^ (1 / 3 : ℝ) - b := by
  set X : ℝ := π ^ 2 * (|a| + |b| + 1) + 1 with hX
  have hπ : 0 < π ^ 2 := by positivity
  have hX1 : 1 ≤ X := by
    have : 0 ≤ π ^ 2 * (|a| + |b| + 1) := by positivity
    linarith
  refine ⟨X ^ 3, one_le_pow₀ hX1, fun c hc => ?_⟩
  have hc0 : 0 ≤ c := le_trans (by positivity) hc
  set x : ℝ := c ^ (1 / 3 : ℝ) with hx
  have hxc : x ^ 3 = c := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hc0]; norm_num
  have hxX : X ≤ x := by
    by_contra h
    push Not at h
    have : x ^ 3 < X ^ 3 := by
      have hx0 : 0 ≤ x := Real.rpow_nonneg hc0 _
      exact pow_lt_pow_left₀ h hx0 (by norm_num)
    linarith
  have hx1 : 1 ≤ x := le_trans hX1 hxX
  have h1 : π ^ 2 * (|a| + |b| + 1) ≤ x := by linarith
  have h2 : (|a| + |b| + 1) ≤ x / π ^ 2 := by
    rw [le_div_iff₀ hπ]; linarith
  rw [← hxc]
  have e : x ^ 3 / π ^ 2 = x ^ 2 * (x / π ^ 2) := by ring
  rw [e]
  have h3 : x ^ 2 * (|a| + |b| + 1) ≤ x ^ 2 * (x / π ^ 2) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have h4 : x ≤ x ^ 2 := by nlinarith
  have h5 : a * x ≤ |a| * x := mul_le_mul_of_nonneg_right (le_abs_self a) (by linarith)
  have h6 : |a| * x ≤ |a| * x ^ 2 := mul_le_mul_of_nonneg_left h4 (abs_nonneg a)
  have h7 : b ≤ |b| * x ^ 2 := by
    have : |b| ≤ |b| * x ^ 2 := by nlinarith [abs_nonneg b]
    linarith [le_abs_self b]
  nlinarith [abs_nonneg a, abs_nonneg b, sq_nonneg x]


/-- The prescribed sites are positive for large `c`, uniformly over the offsets. -/
lemma hankelSites_pos (D : ShellHBData) (R_off : ℝ) :
    ∃ c₀ : ℝ, 1 ≤ c₀ ∧ ∀ c : ℝ, c₀ ≤ c → ∀ r : ℝ → ℝ → ℝ, (∀ t c', |r t c'| ≤ R_off) →
      ∀ s ∈ hankelSites D r c, 0 < s := by
  obtain ⟨c₀, h1, h⟩ := exists_pos_level (∑ t ∈ D.S, |t| / hankelBeta1) R_off
  refine ⟨c₀, h1, fun c hc r hr s hs => ?_⟩
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
  have htS : t ∈ D.S := (Finset.mem_erase.mp ht).2
  have hc0 : 0 ≤ c := by linarith
  have hle : |t| / hankelBeta1 ≤ ∑ t ∈ D.S, |t| / hankelBeta1 :=
    Finset.single_le_sum (f := fun t => |t| / hankelBeta1)
      (fun _ _ => div_nonneg (abs_nonneg _) hankelBeta1_pos.le) htS
  have hpow : 0 ≤ c ^ (1 / 3 : ℝ) := Real.rpow_nonneg hc0 _
  have h2 : t / hankelBeta1 ≤ |t| / hankelBeta1 :=
    div_le_div_of_nonneg_right (le_abs_self t) hankelBeta1_pos.le
  have h3 := h c hc
  have h4 : (t / hankelBeta1) * c ^ (1 / 3 : ℝ) ≤ (∑ t ∈ D.S, |t| / hankelBeta1) * c ^ (1 / 3 : ℝ) :=
    mul_le_mul_of_nonneg_right (h2.trans hle) hpow
  have h5 := (abs_le.mp (hr t c)).1
  unfold hankelLevel
  linarith

/-- **`thm:intro-hb`** (= `u1cl:multilevel`, Theorem L.2, = `thm:hb-thresholds`). Fix Hermite–Biehler data
`(P, Q)` (the configuration `D`, `m = D.S.card`, sites `t_1, …, t_{m-1}` = `D.S` minus `D.tm`) and `R_off ≥ 0`. For
either Fourier eigenvalue `ε`, real `c` large and prescribed levels `T_{j,c} = c/π² - (t_j/β₁) c^{1/3} + r_{j,c}`,
`|r_{j,c}| ≤ R_off`, the infimum `T^{opt,ε}_{m,c}` over feasible `f ∈ 𝒜_c^ε` with `f(T_{j,c}) ≥ 0` equals
`c/π² - (t_m/β₁) c^{1/3} + O(1)`; the infimum is attained (also by an `f` with `f(0) = 0`) and unchanged by the extra
condition `f(0) = 0`; the constants `C`, `c₀` are uniform in the offsets. Conditional on `HbMultilevelInputs D`
(open results, see `HbMultilevelDefs.lean`); not stated: the O-constant's dependence on `(P, Q)` (it is on `D`). -/
theorem thm_intro_hb (D : ShellHBData) (I : HbMultilevelInputs D) :
    ∀ R_off : ℝ, 0 ≤ R_off → ∃ C c₀ : ℝ, ∀ c : ℝ, c₀ ≤ c → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
      ∀ r : ℝ → ℝ → ℝ, (∀ t c', |r t c'| ≤ R_off) →
        |hankelTOpt D r ε c - hbModel D c| ≤ C ∧
        (∃ f : ℝ → ℝ, IsHankelPrescribed D r c ε (hankelTOpt D r ε c) f) ∧
        (∃ f : ℝ → ℝ, IsHankelPrescribed D r c ε (hankelTOpt D r ε c) f ∧ f 0 = 0) ∧
        hankelTOpt0 D r ε c = hankelTOpt D r ε c := by
  intro R_off hR
  obtain ⟨C₁, c₁, hlow⟩ := I.lower R_off hR
  obtain ⟨K, c₂, hKpos, hc₂, hcon⟩ := I.construction 4 le_rfl R_off hR
  obtain ⟨c₃, hc₃, hpos⟩ := hankelSites_pos D R_off
  have htm : D.tm < 0 := lt_of_le_of_lt D.tm_le_airyZero_one (airyZero_neg 1)
  refine ⟨max C₁ K, max (max c₁ c₂) (max c₃ 1), fun c hc ε hε r hr => ?_⟩
  have hc₁' : c₁ ≤ c := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hc
  have hc₂' : c₂ ≤ c := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hc
  have hc₃' : c₃ ≤ c := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hc
  have hc1 : 1 ≤ c := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hc
  -- the construction gives an element of the feasible class
  obtain ⟨f₀, hf₀eig, hf₀0, hf₀sites, hf₀tail⟩ := hcon c hc₂' ε hε
  set Tup : ℝ := c / π ^ 2 + (|D.tm| / hankelBeta1) * c ^ (1 / 3 : ℝ) + K with hTup
  have hTup' : Tup = hbModel D c + K := by
    unfold hbModel
    rw [hTup, abs_of_neg htm]; ring
  have hfeas₀ : IsHankelFeasible c ε Tup f₀ :=
    { toIsHankelEigenfn := hf₀eig
      nonzero := ⟨0, Set.mem_Ici.mpr le_rfl, fun h => by rw [h, mul_zero] at hf₀0; exact lt_irrefl _ hf₀0⟩
      origin_sign := hf₀0.le
      tail_nonneg := fun Δ hΔ => (hf₀tail Δ hΔ).le }
  have hpres₀ : IsHankelPrescribed D r c ε Tup f₀ :=
    { toIsHankelFeasible := hfeas₀
      sites_nonneg := fun s hs => by
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
        have htS := Finset.mem_erase.mp ht
        refine (hf₀sites t htS.2 htS.1 _ ?_).le
        have : hankelLevel t c (r t c) - hankelLevel t c 0 = r t c := by unfold hankelLevel; ring
        rw [this]; exact hr t c }
  -- attainment
  have hsitespos : ∀ s ∈ hankelSites D r c, 0 < s := hpos c hc₃' r hr
  obtain ⟨Tm, fm, hmin⟩ := I.attainment c (by linarith) ε hε (hankelSites D r c) hsitespos
    ⟨Tup, f₀, hfeas₀, hpres₀.sites_nonneg⟩
  have hmem : ∀ T f, IsHankelPrescribed D r c ε T f ↔
      IsHankelFeasible c ε T f ∧ ∀ s ∈ hankelSites D r c, 0 ≤ f s :=
    fun T f => ⟨fun h => ⟨h.toIsHankelFeasible, h.sites_nonneg⟩, fun h => ⟨h.1, h.2⟩⟩
  have hpresm : IsHankelPrescribed D r c ε Tm fm := (hmem _ _).2 ⟨hmin.feasible, hmin.sites_nonneg⟩
  have hleast : IsLeast {T : ℝ | ∃ f, IsHankelPrescribed D r c ε T f} Tm :=
    ⟨⟨fm, hpresm⟩, fun T ⟨f, hf⟩ => hmin.least T f hf.toIsHankelFeasible hf.sites_nonneg⟩
  have hinf : hankelTOpt D r ε c = Tm := hleast.csInf_eq
  have hf0 : fm 0 = 0 := I.exact_origin c (by linarith) ε hε _ hsitespos Tm fm hmin
  have hleast0 : IsLeast {T : ℝ | ∃ f, IsHankelPrescribed D r c ε T f ∧ f 0 = 0} Tm :=
    ⟨⟨fm, hpresm, hf0⟩, fun T ⟨f, hf, _⟩ => hleast.2 ⟨f, hf⟩⟩
  have hbound1 := hlow c hc₁' ε hε r hr Tm fm hpresm
  have hbound2 : Tm ≤ Tup := hleast.2 ⟨f₀, hpres₀⟩
  rw [hinf]
  refine ⟨?_, ⟨fm, hpresm⟩, ⟨fm, hpresm, hf0⟩, hleast0.csInf_eq⟩
  rw [abs_le]
  constructor <;> linarith [le_max_left C₁ K, le_max_right C₁ K]


/-- `hbModel` for the Airy configuration is the one-level model `c/π² + A c^{1/3}`. -/
lemma hbModel_airy (c : ℝ) :
    hbModel ShellHBData.airy c = c / π ^ 2 + airyOrderCoeff * c ^ (1 / 3 : ℝ) := by
  unfold hbModel airyOrderCoeff
  rw [abs_of_neg (airyZero_neg 1)]
  show c / π ^ 2 - (airyZero 1 / hankelBeta1) * c ^ (1 / 3 : ℝ) = _
  ring

/-- The lower half of `u1cl:multilevel` at `(P, Q) = (1, 0)`: the field `lower` of `HbMultilevelInputs` holds for
the Airy configuration (from `hb_thresholds_lower`; the prescribed sites are empty there). -/
theorem hbMultilevelLower_airy : HbMultilevelLower ShellHBData.airy := by
  intro R_off _
  obtain ⟨C, c₀, h⟩ := hb_thresholds_lower
  refine ⟨C, c₀, fun c hc ε hε r _ T f hf => ?_⟩
  rw [hbModel_airy]
  exact h c hc ε hε T f hf.toIsHankelFeasible


/-! ### Headline `thm:intro-gap` (`thm:ce-canonical-iff`) -/


/-- `u_LP ≤ t_m`. -/
lemma uLP_le_tm (D : ShellHBData) : uLP D ≤ (D.tm : EReal) :=
  iSup₂_le fun u hu => EReal.coe_le_coe_iff.2 ((one_profile_threshold_le_and_endpoint_iff D).1 u hu)

/-- Attainment of `u_LP` when the weak problem is feasible. -/
lemma uLP_attained (D : ShellHBData) (h : ∃ u : ℝ, OneProfileFeasible D u) :
    ∃ b : ℝ, uLP D = (b : EReal) ∧ OneProfileFeasible D b := by
  obtain ⟨u₀, hu₀⟩ := h
  obtain ⟨C, ν, hC, hbound⟩ := one_profile_envelope_aux D u₀ hu₀
  obtain ⟨u_s, hu_s⟩ := one_profile_maximizer_exists D
    { u₀ := u₀, u₀_feasible := hu₀, C₀ := C, ν₀ := ν, hC₀ := hC,
      uniform_env := fun {u H} hu hH hn z => hbound u hu H hH hn z }
  refine ⟨u_s, le_antisymm (iSup₂_le fun u hu => EReal.coe_le_coe_iff.2 (hu_s.2 hu)) ?_, hu_s.1⟩
  exact le_iSup₂ (f := fun (u : ℝ) (_ : OneProfileFeasible D u) => (u : EReal)) u_s hu_s.1

/-- The weak witness `-G_N` at the cutoff `t_m` under `ℒ_y(-G_N) ≥ 0`. -/
lemma negG_witness (D : ShellHBData)
    (hL_nn : ∀ y : ℝ, 0 < y → 0 ≤ airyLaplace (fun u => -(D.G (u : ℂ)).re) y) :
    OneProfileFeasibleWitness D D.tm (fun z => -D.G z) := by
  refine ⟨D.G_inAiryClass.neg, ?_, ?_, ?_, ?_⟩
  · by_contra h0
    push Not at h0
    have hl : ∫ x : ℝ, ‖D.G (x : ℂ)‖ = 0 := by
      have : (fun x : ℝ => ‖D.G (x : ℂ)‖) = 0 := funext fun x => by
        simpa [neg_eq_zero] using h0 (x : ℂ)
      simp [this]
    linarith [D.G_l1_pos]
  · intro t ht _
    rw [Complex.neg_re, D.G_eq_zero_on_S t ht, Complex.zero_re, neg_zero]
  · intro u hu
    rw [Complex.neg_re]
    exact neg_nonpos.mpr (D.G_nonneg_left u hu)
  · intro y hy
    rcases hy.eq_or_lt with rfl | hypos
    · have hre : ∫ x : ℝ, (D.G (x : ℂ)).re = (∫ x : ℝ, D.G (x : ℂ)).re := integral_re D.G_int
      simp_rw [zero_mul, Real.exp_zero, mul_one, Complex.neg_re, integral_neg, hre,
        D.G_integral_zero, Complex.zero_re, neg_zero, le_rfl]
    · have hyL := hL_nn y hypos
      unfold airyLaplace at hyL
      have hint_nn : 0 ≤ ∫ u : ℝ, -(D.G (u : ℂ)).re * Real.exp (y * u) :=
        nonneg_of_mul_nonneg_right hyL (Real.exp_pos _)
      have heq : (fun u : ℝ => (-D.G (u : ℂ)).re * Real.exp (y * u)) =
          fun (u : ℝ) => -(D.G (u : ℂ)).re * Real.exp (y * u) := by
        ext u; rw [Complex.neg_re]
      rw [heq]; exact hint_nn

/-- `u_LP = t_m` iff `ℒ_y(-G_N) ≥ 0` for all `y > 0` (`prop:ce-one-profile`). -/
lemma uLP_eq_tm_iff (D : ShellHBData) :
    uLP D = (D.tm : EReal) ↔ ∀ y : ℝ, 0 < y → 0 ≤ airyLaplace (fun u => -(D.G (u : ℂ)).re) y := by
  constructor
  · intro h
    have hex : ∃ u : ℝ, OneProfileFeasible D u := by
      by_contra hno
      push Not at hno
      have : uLP D = ⊥ := by simp [uLP, hno]
      rw [this] at h
      exact EReal.bot_ne_coe _ h
    obtain ⟨b, hb, hfeas⟩ := uLP_attained D hex
    rw [hb] at h
    have : b = D.tm := EReal.coe_injective h
    subst this
    exact ((one_profile_threshold_le_and_endpoint_iff D).2.1 hfeas)
  · intro hL
    refine le_antisymm (uLP_le_tm D) ?_
    exact le_iSup₂ (f := fun (u : ℝ) (_ : OneProfileFeasible D u) => (u : EReal)) D.tm
      ((one_profile_threshold_le_and_endpoint_iff D).2.2 hL |> fun h => h)

/-- Strict-site witnesses are weak witnesses: `u_sh ≤ u_LP`. -/
lemma uSh_le_uLP (D : ShellHBData) : uSh D ≤ uLP D :=
  iSup₂_le fun u hu => by
    obtain ⟨H, hH, _⟩ := hu
    exact le_iSup₂ (f := fun (u : ℝ) (_ : OneProfileFeasible D u) => (u : EReal)) u ⟨H, hH⟩

/-- With no prescribed sites (`m = 1`), `u_sh = u_LP`. -/
lemma uSh_eq_uLP_of_card_one (D : ShellHBData) (h : D.S.card = 1) : uSh D = uLP D := by
  refine le_antisymm (uSh_le_uLP D) (iSup₂_le fun u hu => ?_)
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
  have hS : ∀ t ∈ D.S, t = D.tm := fun t ht => by
    have h1 : t = a := by rw [ha] at ht; exact Finset.mem_singleton.mp ht
    have h2 : D.tm = a := by
      have := D.tm_mem; rw [ha] at this; exact Finset.mem_singleton.mp this
    rw [h1, h2]
  obtain ⟨H, hH⟩ := hu
  exact le_iSup₂ (f := fun (u : ℝ) (_ : OneProfileStrictFeasible D u) => (u : EReal)) u
    ⟨H, hH, fun t ht htm => (htm (hS t ht)).elim⟩


lemma shellSites_card (D : ShellHBData) : (shellSites D).card = D.S.card - 1 :=
  Finset.card_erase_of_mem D.tm_mem

/-- The chain `Λ_M ≤ λ < u_sh ≤ u_LP` of `thm:ce-canonical-iff` (1), for `m ≥ 2`. -/
lemma lambda_chain (D : ShellHBData) (hm : 2 ≤ D.S.card) :
    (∀ M : ℕ, D.S.card ≤ M → airyLambdaM (shellSites D) M ≤ airyLambdaOf (shellSites D)) ∧
    ((airyLambdaOf (shellSites D) : ℝ) : EReal) ≤ uLP D ∧
    ((airyLambdaOf (shellSites D) : ℝ) : EReal) < uSh D := by
  have hcard := shellSites_card D
  refine ⟨fun M hM => ?_, ?_⟩
  · exact airyLambdaSection_le_airyLambda (airySites (shellSites D)) (by omega)
  obtain ⟨q, hqd, hqreal, hqne, hqs, hwit, hint0, hLpos⟩ := (airySquareAttained D).witness
  set lam : ℝ := airyLambdaOf (shellSites D) with hlam
  have hle : (lam : EReal) ≤ uLP D :=
    le_iSup₂ (f := fun (u : ℝ) (_ : OneProfileFeasible D u) => (u : EReal)) lam ⟨_, hwit⟩
  refine ⟨hle, ?_⟩
  have hlt : lam < D.tm := by
    have h1 : lam ≤ D.tm := EReal.coe_le_coe_iff.1 (hle.trans (uLP_le_tm D))
    refine lt_of_le_of_ne h1 fun heq => ?_
    obtain ⟨hHd, hHi, hHb, hHreal⟩ := hwit.1
    obtain ⟨C, ν, hC, hb⟩ := hHb
    set H : ℂ → ℂ := fun z => (z - (lam : ℂ)) * q z ^ 2 with hH
    have hint : 0 ≤ (∫ x : ℝ, H (x : ℂ)).re := by
      have hre : ∫ x : ℝ, (H (x : ℂ)).re = (∫ x : ℝ, H (x : ℂ)).re := integral_re hHi
      rw [← hre]; exact le_of_eq hint0.symm
    obtain ⟨b, _, _, hnz⟩ := D.uniqueness hHd hHi hC hb hHreal hint hwit.2.2.1
      (fun x hx => hwit.2.2.2.1 x (heq ▸ hx))
    obtain ⟨_, _, hder⟩ := hnz hwit.2.1
    obtain ⟨s, hs⟩ : (shellSites D).Nonempty := Finset.card_pos.mp (by omega)
    have hsS : s ∈ D.S := (Finset.mem_erase.mp hs).2
    have hdq : HasDerivAt (fun z : ℂ => (z - (lam : ℂ)) * q z ^ 2) 0 (s : ℂ) := by
      have h1 : HasDerivAt (fun z : ℂ => z - (lam : ℂ)) 1 (s : ℂ) := (hasDerivAt_id _).sub_const _
      have h2 := (hqd (s : ℂ)).hasDerivAt.pow 2
      refine (h1.mul h2).congr_deriv ?_
      simp [hqs s hs]
    exact hder s hsS hdq.deriv
  exact (airy_active_height D).strictify lam hlt _ hwit hLpos


lemma shell_mem_pos {D : ShellHBData} {r : ℝ → ℕ → ℝ} {d : ℕ} {R : ℝ} (hR : R ∈ ceShellRadiusSet D r d) :
    0 < R := by
  obtain ⟨h, hh⟩ := hR
  exact hh.toIsContinuousL1CEAdmissible.toIsCohnElkiesAdmissible.r_pos

lemma shellNormRadius_ge_iff {d : ℕ} (hd : 1 ≤ d) (s R : ℝ) :
    s ≤ shellNormRadius d R ↔ (d : ℝ) / (2 * π ^ 2) + s * ((d : ℝ) / 2) ^ (1 / 3 : ℝ) ≤ R ^ 2 / 2 := by
  have hq : 0 < ((d : ℝ) / 2) ^ (1 / 3 : ℝ) :=
    Real.rpow_pos_of_pos (by have : (1 : ℝ) ≤ d := by exact_mod_cast hd
                             linarith) _
  unfold shellNormRadius
  rw [le_div_iff₀ hq]
  constructor <;> intro h <;> linarith

lemma sinf_sq_ge {S : Set ℝ} (hne : S.Nonempty) (hpos : ∀ R ∈ S, 0 < R) {B : ℝ}
    (h : ∀ R ∈ S, B ≤ R ^ 2 / 2) : B ≤ (sInf S) ^ 2 / 2 := by
  have h0 : 0 ≤ sInf S := le_csInf hne fun R hR => (hpos R hR).le
  rcases le_or_gt B 0 with hB | hB
  · nlinarith [sq_nonneg (sInf S)]
  · have : √(2 * B) ≤ sInf S := le_csInf hne fun R hR =>
      Real.sqrt_le_iff.mpr ⟨(hpos R hR).le, by linarith [h R hR]⟩
    have := (Real.sqrt_le_iff.mp this).2
    linarith

lemma sinf_sq_le {S : Set ℝ} (hpos : ∀ R ∈ S, 0 < R) {R : ℝ} (hR : R ∈ S) :
    (sInf S) ^ 2 / 2 ≤ R ^ 2 / 2 := by
  have h0 : 0 ≤ sInf S := le_csInf ⟨R, hR⟩ fun R hR => (hpos R hR).le
  have h1 : sInf S ≤ R := csInf_le ⟨0, fun R hR => (hpos R hR).le⟩ hR
  nlinarith

/-- Lower half of `thm:ce-shell-gap`: for offsets `o(c^{1/3})` and `s` with `u_LP < -β₁ s`, eventually every
admissible radius has `ρ ≥ s`. (The extraction `hankelShellGapLimit_proved` and the proved one-profile reduction.) -/
lemma shell_gap_lower (D : ShellHBData) {r : ℝ → ℕ → ℝ} (hr : ShellOffsetsSmall r) {s : ℝ}
    (hs : uLP D < ((-(hankelBeta1 * s) : ℝ) : EReal)) :
    ∀ᶠ d : ℕ in atTop, ∀ R ∈ ceShellRadiusSet D r d, s ≤ shellNormRadius d R := by
  have hinf : ¬ OneProfileFeasible D (-(hankelBeta1 * s)) := fun hf =>
    absurd (le_iSup₂ (f := fun (u : ℝ) (_ : OneProfileFeasible D u) => (u : EReal))
      (-(hankelBeta1 * s)) hf) (not_le.2 hs)
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  have hfreq : ∃ᶠ d : ℕ in atTop, (∃ R ∈ ceShellRadiusSet D r d, shellNormRadius d R < s) ∧ 1 ≤ d := by
    refine (hcon.mono fun d hd => ?_).and_eventually (eventually_ge_atTop 1)
    push Not at hd
    exact hd
  obtain ⟨φ, hφ, hφP⟩ := Filter.extraction_of_frequently_atTop hfreq
  choose R hRmem hRlt using fun k => (hφP k).1
  refine hinf ((one_profile_feasible_iff D _).1
    ((shellGapLimit_of_hankel (hankelShellGapLimit_proved D)) r hr (-(hankelBeta1 * s)) φ hφ.tendsto_atTop
      (fun _ => 0) tendsto_const_nhds R hRmem fun k => ?_))
  have hd1 : (1 : ℝ) ≤ (φ k : ℝ) := by exact_mod_cast (hφP k).2
  have hq : 0 < ((φ k : ℝ) / 2) ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have h1 := hRlt k
  unfold shellNormRadius at h1
  rw [div_lt_iff₀ hq] at h1
  have hβ := hankelBeta1_pos
  have : -(hankelBeta1 * s) / hankelBeta1 = -s := by field_simp
  rw [this]
  linarith


/-- **`thm:ce-shell-gap`** (Corollary H.14d), the strict-gap part (`eq:strict-gap`): if `ℒ_y(-G_N) < 0` for some `y > 0`
(this holds for every even `m`, see `thm_ce_shell_gap_even`) and the offsets are `o(c^{1/3})`, then
`liminf ρ_d ≥ -u_LP/β₁` (for every real `s` with `-β₁ s > u_LP`, eventually every admissible radius has `ρ ≥ s`) and
`u_LP < t_m`. Proved from the extraction `hankelShellGapLimit_proved` and the one-profile reduction. The remaining
clauses of the paper's statement (the cutoff bound `v ≤ t_m`, the `v = t_m` endpoint clause, and the origin floor
`eq:ce-origin-floor` of `cor:ce-projection-mass`) are unconditional theorems about Hankel profiles; they are collected
with this statement in `thm_ce_shell_gap_full`. -/
theorem thm_ce_shell_gap {D : ShellHBData}
    (hlap : ∃ y : ℝ, 0 < y ∧ airyLaplace (fun u => -(D.G (u : ℂ)).re) y < 0)
    {r : ℝ → ℕ → ℝ} (hr : ShellOffsetsSmall r) :
    (∀ s : ℝ, uLP D < ((-(hankelBeta1 * s) : ℝ) : EReal) →
      ∀ᶠ d : ℕ in atTop, ∀ R ∈ ceShellRadiusSet D r d, s ≤ shellNormRadius d R) ∧
    uLP D < (D.tm : EReal) := by
  refine ⟨fun s hs => shell_gap_lower D hr hs, lt_of_le_of_ne (uLP_le_tm D) fun he => ?_⟩
  obtain ⟨y, hy, hneg⟩ := hlap
  exact absurd ((uLP_eq_tm_iff D).1 he y hy) (not_le.mpr hneg)

/-- `thm:ce-shell-gap`: the cutoff bound `v ≤ t_m` ("one has `v ≤ t_m`"). Under the hypotheses of
`HankelShellGapLimit` at the cutoff `u_* = v` (offsets `o(c^{1/3})`, Hankel Cohn–Elkies profiles with
`h_k ≤ 0` at the prescribed shells and thresholds `T_k ≤ c/π² - (v/β₁)c^{1/3} + o(c^{1/3})`), `v ≤ t_m`. -/
def HankelCutoffLeTm (D : ShellHBData) : Prop :=
  ∀ r : ℝ → ℕ → ℝ, ShellOffsetsSmall r →
    ∀ (v : ℝ) (dk : ℕ → ℕ), Tendsto dk atTop atTop → (∀ k, 2 ≤ dk k) →
      ∀ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) →
        ∀ (G : ℕ → ℝ → ℝ) (T : ℕ → ℝ), (∀ k, HankelShellProfile ((dk k : ℝ) / 2) (T k) (G k)) →
          (∀ k, ∀ t ∈ D.S, t ≠ D.tm → 0 ≤ shellSite t (r t) (dk k) →
            G k (shellSite t (r t) (dk k)) ≤ 0) →
          (∀ k, T k ≤ (dk k : ℝ) / (2 * π ^ 2) - (v / hankelBeta1) * ((dk k : ℝ) / 2) ^ (1 / 3 : ℝ)
            + ε k * ((dk k : ℝ) / 2) ^ (1 / 3 : ℝ)) →
          v ≤ D.tm

theorem hankelCutoffLeTm_proved (D : ShellHBData) : HankelCutoffLeTm D := by
  intro r hr v dk hdk h2 ε hε G T hP hshell hT
  have h1 := (one_profile_feasible_iff D v).1 (hankelShellGapLimit_proved D r hr v dk hdk h2 ε hε G T hP hshell hT)
  have h3 : (v : EReal) ≤ uLP D :=
    le_iSup₂ (f := fun (u : ℝ) (_ : OneProfileFeasible D u) => (u : EReal)) v h1
  exact EReal.coe_le_coe_iff.1 (h3.trans (uLP_le_tm D))

/-- **`thm:ce-shell-gap`** (Corollary H.14d), the formal statement as far as proved: the strict-gap clause
`eq:strict-gap` of `thm_ce_shell_gap` (under the Laplace hypothesis `ℒ_y(-G_N) < 0`, automatic for even `m`), the cutoff
bound `v ≤ t_m` (`HankelCutoffLeTm`), the `v = t_m` endpoint clause (`ShellGapEndpoint`:
`Ψ_h/M[h] → -G_N/‖G_N‖₁`, `Ψ_ĥ/M[h] → 0`, `Ψ_f/M[f] → G_N/‖G_N‖₁`, `M[ĥ]/M[f] → 0`, `ℒ_y(-G_N) ≥ 0`), and the origin
floor `eq:ce-origin-floor` of `cor:ce-projection-mass` (`HankelOriginFloor`, together with the extraction of
`eq:ce-laplace-constraint`). The last three are unconditional. -/
theorem thm_ce_shell_gap_full {D : ShellHBData}
    (hlap : ∃ y : ℝ, 0 < y ∧ airyLaplace (fun u => -(D.G (u : ℂ)).re) y < 0)
    {r : ℝ → ℕ → ℝ} (hr : ShellOffsetsSmall r) :
    ((∀ s : ℝ, uLP D < ((-(hankelBeta1 * s) : ℝ) : EReal) →
      ∀ᶠ d : ℕ in atTop, ∀ R ∈ ceShellRadiusSet D r d, s ≤ shellNormRadius d R) ∧
      uLP D < (D.tm : EReal)) ∧
    HankelCutoffLeTm D ∧ ShellGapEndpoint D ∧ HankelOriginFloor D :=
  ⟨thm_ce_shell_gap hlap hr, hankelCutoffLeTm_proved D, shellGapEndpoint_proved D, hankelOriginFloor_proved D⟩

/-- `thm:ce-shell-gap` for even `m = D.S.card`: the Laplace hypothesis holds (`even_m_laplace_sign`). -/
theorem thm_ce_shell_gap_even {D : ShellHBData} (heven : Even D.S.card) {r : ℝ → ℕ → ℝ}
    (hr : ShellOffsetsSmall r) :
    (∀ s : ℝ, uLP D < ((-(hankelBeta1 * s) : ℝ) : EReal) →
      ∀ᶠ d : ℕ in atTop, ∀ R ∈ ceShellRadiusSet D r d, s ≤ shellNormRadius d R) ∧
    uLP D < (D.tm : EReal) :=
  thm_ce_shell_gap (by obtain ⟨y, hy, h⟩ := even_m_laplace_sign D heven; exact ⟨y, hy, h⟩) hr

lemma ceShellRho_of_nonempty {D : ShellHBData} {r : ℝ → ℕ → ℝ} {d : ℕ}
    (h : (ceShellRadiusSet D r d).Nonempty) :
    ceShellRho D r d = ((shellNormRadius d (sInf (ceShellRadiusSet D r d)) : ℝ) : EReal) := by
  unfold ceShellRho; simp [h]

lemma le_ceShellRho {D : ShellHBData} {r : ℝ → ℕ → ℝ} {d : ℕ} (hd : 1 ≤ d) {s : ℝ}
    (hall : ∀ R ∈ ceShellRadiusSet D r d, s ≤ shellNormRadius d R) : ((s : ℝ) : EReal) ≤ ceShellRho D r d := by
  by_cases hne : (ceShellRadiusSet D r d).Nonempty
  · rw [ceShellRho_of_nonempty hne, EReal.coe_le_coe_iff, shellNormRadius_ge_iff hd]
    exact sinf_sq_ge hne (fun R hR => shell_mem_pos hR) fun R hR => (shellNormRadius_ge_iff hd s R).1 (hall R hR)
  · unfold ceShellRho; simp [hne]

lemma shellNormRadius_sInf_le {D : ShellHBData} {r : ℝ → ℕ → ℝ} {d : ℕ} (hd : 1 ≤ d) {w : ℝ}
    (h : ∃ R ∈ ceShellRadiusSet D r d, R ^ 2 / 2 ≤ (d : ℝ) / (2 * π ^ 2) + w * ((d : ℝ) / 2) ^ (1 / 3 : ℝ)) :
    shellNormRadius d (sInf (ceShellRadiusSet D r d)) ≤ w := by
  obtain ⟨R, hR, hle⟩ := h
  have hq : 0 < ((d : ℝ) / 2) ^ (1 / 3 : ℝ) :=
    Real.rpow_pos_of_pos (by have : (1 : ℝ) ≤ d := by exact_mod_cast hd
                             linarith) _
  unfold shellNormRadius
  rw [div_le_iff₀ hq]
  have := sinf_sq_le (fun R hR => shell_mem_pos hR) hR
  linarith

lemma ceShellRho_tendsto {D : ShellHBData} {r : ℝ → ℕ → ℝ} {τ : ℝ}
    (hne : ∀ᶠ d : ℕ in atTop, (ceShellRadiusSet D r d).Nonempty)
    (hlow : ∀ s : ℝ, s < τ → ∀ᶠ d : ℕ in atTop, ∀ R ∈ ceShellRadiusSet D r d, s ≤ shellNormRadius d R)
    (hup : ∀ w : ℝ, τ < w → ∀ᶠ d : ℕ in atTop, ∃ R ∈ ceShellRadiusSet D r d,
      R ^ 2 / 2 ≤ (d : ℝ) / (2 * π ^ 2) + w * ((d : ℝ) / 2) ^ (1 / 3 : ℝ)) :
    Tendsto (ceShellRho D r) atTop (𝓝 (τ : EReal)) := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · obtain ⟨x, hax, hxτ⟩ := EReal.lt_iff_exists_real_btwn.1 ha
    filter_upwards [hlow x (EReal.coe_lt_coe_iff.1 hxτ), eventually_ge_atTop 1] with d hd h1
    exact hax.trans_le (le_ceShellRho h1 hd)
  · obtain ⟨w, hτw, hwb⟩ := EReal.lt_iff_exists_real_btwn.1 hb
    filter_upwards [hne, hup w (EReal.coe_lt_coe_iff.1 hτw), eventually_ge_atTop 1] with d hn hu h1
    rw [ceShellRho_of_nonempty hn]
    exact lt_of_le_of_lt (EReal.coe_le_coe_iff.2 (shellNormRadius_sInf_le h1 hu)) hwb

/-- `u_sh = t_m` in the canonical case, from `lem:airy-active-height` (3) and `lem:ce-terminal-deflation`. -/
lemma uSh_eq_tm_of_canonical (D : ShellHBData)
    (hi : ∀ y : ℝ, 0 < y → 0 ≤ airyLaplace (fun u => -(D.G (u : ℂ)).re) y) : uSh D = (D.tm : EReal) := by
  have hb := (uLP_eq_tm_iff D).2 hi
  obtain ⟨-, -, -, hpos⟩ := terminal_cardinal_integral D
  refine (airy_active_height D).quotient_mass D.tm hb _ (negG_witness D hi) ?_
  have : (∫ u : ℝ, (((fun z => -D.G z) (u : ℂ)).re) / (u - D.tm)) =
      ∫ u : ℝ, (-(D.G (u : ℂ)).re) / (u - D.tm) := by simp
  rw [this]; exact hpos.le


lemma qpow_pos (d : ℕ) (hd : 1 ≤ d) : 0 < ((d : ℝ) / 2) ^ (1 / 3 : ℝ) :=
  Real.rpow_pos_of_pos (by have : (1 : ℝ) ≤ d := by exact_mod_cast hd
                           linarith) _

lemma qpow_tendsto : Tendsto (fun d : ℕ => ((d : ℝ) / 2) ^ (1 / 3 : ℝ)) atTop atTop :=
  (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
    ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_div_const (by norm_num : (0 : ℝ) < 2))

lemma shell_i_to_ii (D : ShellHBData) :
    LaplaceNonneg D → ShellBoundedRemainder D := by
  intro hi R_off hR r hr
  obtain ⟨C₁, d₁, h₁⟩ := shellReduction_proved D R_off hR
  obtain ⟨K₀, d₂, h₂⟩ := ce_hb_lift_proved D hi R_off hR
  refine ⟨max C₁ K₀, max d₁ d₂, fun d hd => ?_⟩
  obtain ⟨R, hRm, hRle⟩ := h₂ d (le_trans (le_max_right _ _) hd) r hr
  have hne : (ceShellRadiusSet D r d).Nonempty := ⟨R, hRm⟩
  refine ⟨hne, ?_⟩
  have hlo := sinf_sq_ge hne (fun R hR => shell_mem_pos hR)
    (fun R hR => h₁ d (le_trans (le_max_left _ _) hd) r hr R hR)
  have hup := sinf_sq_le (fun R hR => shell_mem_pos hR) hRm
  rw [abs_le]
  constructor <;> linarith [le_max_left C₁ K₀, le_max_right C₁ K₀]

lemma ceShellRho_tendsto_of_bound {D : ShellHBData} {r : ℝ → ℕ → ℝ} {C : ℝ} {d₀ : ℕ}
    (h : ∀ d : ℕ, d₀ ≤ d → (ceShellRadiusSet D r d).Nonempty ∧
      |(sInf (ceShellRadiusSet D r d)) ^ 2 / 2 -
        ((d : ℝ) / (2 * π ^ 2) - (D.tm / hankelBeta1) * ((d : ℝ) / 2) ^ (1 / 3 : ℝ))| ≤ C) :
    Tendsto (ceShellRho D r) atTop (𝓝 ((-(D.tm / hankelBeta1) : ℝ) : EReal)) := by
  set τ : ℝ := -(D.tm / hankelBeta1) with hτ
  have hC : 0 ≤ C := by
    have := (h (max d₀ 1) (le_max_left _ _)).2
    exact le_trans (abs_nonneg _) this
  have hlim : Tendsto (fun d : ℕ => C / ((d : ℝ) / 2) ^ (1 / 3 : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop qpow_tendsto
  have hg1 : Tendsto (fun d : ℕ => τ - C / ((d : ℝ) / 2) ^ (1 / 3 : ℝ)) atTop (𝓝 τ) := by
    simpa using (tendsto_const_nhds (x := τ)).sub hlim
  have hg2 : Tendsto (fun d : ℕ => τ + C / ((d : ℝ) / 2) ^ (1 / 3 : ℝ)) atTop (𝓝 τ) := by
    simpa using (tendsto_const_nhds (x := τ)).add hlim
  have hreal : Tendsto (fun d : ℕ => shellNormRadius d (sInf (ceShellRadiusSet D r d))) atTop (𝓝 τ) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hg1 hg2 ?_ ?_
    · filter_upwards [eventually_ge_atTop (max d₀ 1)] with d hd
      have hq := qpow_pos d (le_trans (le_max_right _ _) hd)
      have hb := (abs_le.1 (h d (le_trans (le_max_left _ _) hd)).2).1
      unfold shellNormRadius
      rw [le_div_iff₀ hq, sub_mul, div_mul_cancel₀ _ hq.ne', hτ]
      nlinarith [hq]
    · filter_upwards [eventually_ge_atTop (max d₀ 1)] with d hd
      have hq := qpow_pos d (le_trans (le_max_right _ _) hd)
      have hb := (abs_le.1 (h d (le_trans (le_max_left _ _) hd)).2).2
      unfold shellNormRadius
      rw [div_le_iff₀ hq, add_mul, div_mul_cancel₀ _ hq.ne', hτ]
      nlinarith [hq]
  have hco := (EReal.tendsto_coe.2 hreal)
  refine hco.congr' ?_
  filter_upwards [eventually_ge_atTop d₀] with d hd
  rw [ceShellRho_of_nonempty (h d hd).1]

lemma shell_ii_to_iii_liminf {D : ShellHBData} (h : ShellBoundedRemainder D) : ShellLiminf D := by
  refine ⟨fun _ _ => 0, fun s => by simp, ?_⟩
  obtain ⟨C, d₀, hC⟩ := h 0 le_rfl (fun _ _ => 0) (fun _ _ => by simp)
  exact (ceShellRho_tendsto_of_bound hC).liminf_eq

lemma shell_iii_to_iv {D : ShellHBData} (h : ShellLimit D) : ShellLiminf D :=
  ⟨fun _ _ => 0, fun s => by simp,
    (h _ (fun s => by simp)).liminf_eq⟩

lemma shell_iv_to_i (D : ShellHBData) (h : ShellLiminf D) : LaplaceNonneg D := by
  by_contra hi
  have hlt : uLP D < (D.tm : EReal) :=
    lt_of_le_of_ne (uLP_le_tm D) fun he => hi ((uLP_eq_tm_iff D).1 he)
  obtain ⟨w, hw1, hw2⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
  have hw2' : w < D.tm := EReal.coe_lt_coe_iff.1 hw2
  obtain ⟨r, hr, hliminf⟩ := h
  set s : ℝ := -w / hankelBeta1 with hs
  have hβ := hankelBeta1_pos
  have hnegβ : -(hankelBeta1 * s) = w := by rw [hs]; field_simp
  have hlow := shell_gap_lower D hr (s := s) (by rw [hnegβ]; exact hw1)
  have hev : ∀ᶠ d : ℕ in atTop, ((s : ℝ) : EReal) ≤ ceShellRho D r d := by
    filter_upwards [hlow, eventually_ge_atTop 1] with d hd h1
    exact le_ceShellRho h1 hd
  have hle : ((s : ℝ) : EReal) ≤ liminf (ceShellRho D r) atTop := le_liminf_of_le (by isBoundedDefault) hev
  rw [hliminf, EReal.coe_le_coe_iff] at hle
  have : -(D.tm / hankelBeta1) < s := by
    rw [hs, neg_div, neg_lt_neg_iff]
    exact div_lt_div_of_pos_right hw2' hβ
  linarith


lemma shell_i_to_iii (D : ShellHBData) (hi : LaplaceNonneg D) :
    ShellLimit D := by
  intro r hr
  have hβ := hankelBeta1_pos
  have hLP := (uLP_eq_tm_iff D).2 hi
  have hSh := uSh_eq_tm_of_canonical D hi
  set τ : ℝ := -(D.tm / hankelBeta1) with hτ
  have hup : ∀ w : ℝ, τ < w → ∀ᶠ d : ℕ in atTop, ∃ R ∈ ceShellRadiusSet D r d,
      R ^ 2 / 2 ≤ (d : ℝ) / (2 * π ^ 2) + w * ((d : ℝ) / 2) ^ (1 / 3 : ℝ) := by
    intro w hw
    have hw' : -(hankelBeta1 * w) < D.tm := by
      have : hankelBeta1 * τ < hankelBeta1 * w := mul_lt_mul_of_pos_left hw hβ
      have e : hankelBeta1 * τ = -D.tm := by rw [hτ]; field_simp
      linarith
    set v : ℝ := (-(hankelBeta1 * w) + D.tm) / 2 with hv
    have hvlt : v < D.tm := by rw [hv]; linarith
    have hvgt : -(hankelBeta1 * w) < v := by rw [hv]; linarith
    have hup := ce_airy_transfer_upper D v (by rw [hSh]; exact EReal.coe_lt_coe_iff.2 hvlt) r hr
    filter_upwards [hup, eventually_ge_atTop 1] with d hd h1
    obtain ⟨R, hR, hle⟩ := hd
    refine ⟨R, hR, le_trans hle ?_⟩
    have hq := qpow_pos d h1
    have h3 : -w ≤ v / hankelBeta1 := by rw [le_div_iff₀ hβ]; linarith
    have h4 : -(v / hankelBeta1) ≤ w := by linarith
    linarith [mul_le_mul_of_nonneg_right h4 hq.le]
  refine ceShellRho_tendsto ?_ ?_ hup
  · filter_upwards [hup (τ + 1) (by linarith)] with d ⟨R, hR, _⟩ using ⟨R, hR⟩
  · intro s hs
    have : uLP D < ((-(hankelBeta1 * s) : ℝ) : EReal) := by
      rw [hLP]
      refine EReal.coe_lt_coe_iff.2 ?_
      have : hankelBeta1 * s < hankelBeta1 * τ := mul_lt_mul_of_pos_left hs hβ
      have e : hankelBeta1 * τ = -D.tm := by rw [hτ]; field_simp
      linarith
    exact shell_gap_lower D hr this


lemma uSh_eq_of_node_bound {D : ShellHBData} {t : ℕ → ℝ} (ht : IsHbZeroEnum D.P D.Q t)
    (h : ((hbNode t (D.S.card + 2) : ℝ) : EReal) ≤ uLP D) : uSh D = uLP D := by
  have hbot : uLP D ≠ ⊥ := fun h0 => by
    rw [h0] at h; exact absurd (le_bot_iff.1 h) (EReal.coe_ne_bot _)
  have htop : uLP D ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) (uLP_le_tm D)
  obtain ⟨b, hb⟩ : ∃ b : ℝ, uLP D = (b : EReal) := ⟨(uLP D).toReal, (EReal.coe_toReal htop hbot).symm⟩
  have hbtm : b ≤ D.tm := EReal.coe_le_coe_iff.1 (hb ▸ uLP_le_tm D)
  rw [hb]
  rcases hbtm.lt_or_eq with hlt | heq
  · exact (airy_node_sign D ht).2 b hb (by rw [hb] at h; exact EReal.coe_le_coe_iff.1 h) hlt
  · subst heq
    exact uSh_eq_tm_of_canonical D ((uLP_eq_tm_iff D).1 (hb.trans rfl))

/-- **`thm:intro-gap`** (= `thm:ce-canonical-iff`, `ce_canonical_iff.tex`), parts (1)-(3), for strict
Hermite–Biehler data `D` (`m = D.S.card`, sites `shellSites D`) with the zero enumeration `t` (`t j = t_{j+1}`).

(1) `u_LP ≤ t_m`, with equality iff `ℒ_y(-G_N) ≥ 0` for all `y > 0`; for `m ≥ 2`,
`Λ_M ≤ λ < u_sh ≤ u_LP` (`M ≥ m`), `Λ_m > a_m`, `λ > τ_N > t_{m+e}`; if `u_LP < t_m` there is a common positive
height at which every optimizer has a Laplace zero of even order (`L = L' = 0`) and the deflation obstruction
`eq:airy-deflation-obstruction` holds. (2) `u_sh = u_LP` under the integral criterion (a) or the node-sign criterion
(b), whenever `u_LP ≥ t_{m+2}`, and for every configuration with `m ≤ 5`. (3) the equivalence of (i)
`ℒ_y(-G_N) ≥ 0` for all `y > 0` (`LaplaceNonneg`), (ii) the bounded remainder `eq:ce-canonical-iff`
(`ShellBoundedRemainder`), (iii) `lim ρ_d = -t_m/β₁` for offsets `o(c^{1/3})` (`ShellLimit`) and (iv) `liminf ρ_d =
-t_m/β₁` for some such shells (`ShellLiminf`); (i) forces `m` odd.

Unconditional (`CeCanonicalInputs D t` has no remaining open fields). Differences from the
paper's text: `d` is an integer here
(`ρ_d` is `+∞` for an empty shell class); in (ii) the offsets are fixed per statement, and the quotient integrals in
(1) and (2)(a) are required to exist; the hypothesis `IsHbZeroEnum` on `t` is
satisfiable for every `D` (`exists_isHbZeroEnum`, unique by `IsHbZeroEnum.unique`; `hbZeroEnum D` is that `t`). (4) the
remaining clauses of `thm:ce-shell-gap` (Hankel form; the origin floor `eq:ce-origin-floor` is `HankelOriginFloor`, in
`thm_ce_shell_gap_full`): the origin mass identity `0 < h(0) = M[ĥ] ≤ M[h]` for Hankel
Cohn–Elkies profiles (proved, `hankelShellProfile_origin_mass`) and the `v = t_m` endpoint clause
(`ShellGapEndpoint D`: `Ψ_h/M[h] → -G_N/‖G_N‖₁`, `Ψ_ĥ/M[h] → 0`, `Ψ_f/M[f] → G_N/‖G_N‖₁`, `M[ĥ]/M[f] → 0`, with
`f = ĥ - h`, and `ℒ_y(-G_N) ≥ 0`; proved, `shellGapEndpoint_proved`). The failure of (i) forcing a strict
Airy-order gap (`thm:ce-shell-gap`, `eq:strict-gap`) is `thm_ce_shell_gap`. (5) the side clauses of the statement:
`eq:hb-node-bound` (for `m ≥ 2` the node weights `ω_n`, `n ∈ T_0`, are positive and `τ_N < t_m`; proved,
`hbNodeWeight_pos`, `hbTauN_lt_tm`, `CeCanonicalSide.lean`), the bound of `thm:ce-laplace-zeros` (the positive zeros of
`F_N = ∫ (-G_N) e^{yu} du`, counted with multiplicity, number at most `m - 1`; proved, `laplace_zero_multiplicity_le`;
its parenthetical "even multiplicity" and the same statement for `ℒ_y(-G_N) = e^{-y³/12} F_N` are not restated) and the
cumulative node-sum criterion of `thm:airy-node-sign` (proved, `airy_node_sum`, `AiryNodeSign.lean`). -/
theorem thm_ce_canonical_iff (D : ShellHBData) (t : ℕ → ℝ) (ht : IsHbZeroEnum D.P D.Q t) :
    -- (1) thresholds
    (uLP D ≤ (D.tm : EReal) ∧
      (uLP D = (D.tm : EReal) ↔ ∀ y : ℝ, 0 < y → 0 ≤ airyLaplace (fun u => -(D.G (u : ℂ)).re) y) ∧
      (2 ≤ D.S.card →
        (∀ M : ℕ, D.S.card ≤ M → airyLambdaM (shellSites D) M ≤ airyLambdaOf (shellSites D)) ∧
        ((airyLambdaOf (shellSites D) : ℝ) : EReal) < uSh D ∧ uSh D ≤ uLP D ∧
        airyZero D.S.card < airyLambdaM (shellSites D) D.S.card ∧
        hbTauN D t < airyLambdaOf (shellSites D) ∧ hbNode t (D.S.card + D.S.card / 2) < hbTauN D t) ∧
      (uLP D < (D.tm : EReal) →
        (∃ y : ℝ, 0 < y ∧ ∀ b : ℝ, uLP D = (b : EReal) → ∀ H : ℂ → ℂ, OneProfileFeasibleWitness D b H →
          AnalyticAt ℝ (laplaceL (fun u => (H (u : ℂ)).re)) y ∧
          Even (analyticOrderNatAt (laplaceL (fun u => (H (u : ℂ)).re)) y) ∧
          laplaceL (fun u => (H (u : ℂ)).re) y = 0 ∧
          deriv (laplaceL (fun u => (H (u : ℂ)).re)) y = 0) ∧
        (∀ b : ℝ, uLP D = (b : EReal) → ∀ H : ℂ → ℂ, OneProfileFeasibleWitness D b H →
          ∀ z : ℝ, b < z → (H (z : ℂ)).re = 0 → (z ∉ shellSites D ∨ (deriv H (z : ℂ)).re ≤ 0) →
            ∫ u : ℝ, (H (u : ℂ)).re / (u - z) < 0))) ∧
    -- (2) weak equals strict
    ((∀ b : ℝ, uLP D = (b : EReal) → b < D.tm → ∀ H : ℂ → ℂ, OneProfileFeasibleWitness D b H →
        ((MeasureTheory.Integrable (fun u : ℝ => (H (u : ℂ)).re / (u - b)) ∧
            0 ≤ ∫ u : ℝ, (H (u : ℂ)).re / (u - b)) ∨
          ¬ ∃ t₁ t₂ t₃ : ℝ, t₁ < t₂ ∧ t₂ < t₃ ∧ b < t₁ ∧ t₃ ≤ D.tm ∧ at47_Nf D.P D.Q t₁ = 0 ∧
            at47_Nf D.P D.Q t₂ = 0 ∧ at47_Nf D.P D.Q t₃ = 0 ∧ 0 < (H (t₁ : ℂ)).re ∧
            (H (t₂ : ℂ)).re < 0 ∧ 0 < (H (t₃ : ℂ)).re) → uSh D = (b : EReal)) ∧
      (((hbNode t (D.S.card + 2) : ℝ) : EReal) ≤ uLP D → uSh D = uLP D) ∧
      (D.S.card ≤ 5 → uSh D = uLP D)) ∧
    -- (3) the canonical coefficient
    ((LaplaceNonneg D → Odd D.S.card) ∧
      (LaplaceNonneg D ↔ ShellBoundedRemainder D) ∧
      (LaplaceNonneg D ↔ ShellLimit D) ∧
      (LaplaceNonneg D ↔ ShellLiminf D)) ∧
    -- (4) `thm:ce-shell-gap`: the origin mass identity and the `v = t_m` endpoint clause
    ((∀ n : ℕ, 1 ≤ n → ∀ (T : ℝ) (G : ℝ → ℝ), HankelShellProfile (((n : ℝ) + 1) / 2) T G →
        0 < G 0 ∧
        hankelMass (((n : ℝ) + 1) / 2) (besselHankelTransform (((n : ℝ) + 1) / 2) G) = G 0 ∧
        G 0 ≤ hankelMass (((n : ℝ) + 1) / 2) G) ∧
      ShellGapEndpoint D) ∧
    -- (5) side clauses: `eq:hb-node-bound` (`ω_n > 0`, `τ_N < t_m`), the zero bound of `thm:ce-laplace-zeros`
    -- for `F_N = ∫ (-G_N) e^{yu}`, and the cumulative node-sum criterion of `thm:airy-node-sign`
    ((2 ≤ D.S.card →
        (∀ n ∈ Finset.Icc D.S.card (D.S.card + D.S.card / 2),
          0 < hbNodeWeight D.P D.Q t (Finset.Icc D.S.card (D.S.card + D.S.card / 2)) n) ∧
        hbTauN D t < D.tm) ∧
      (∀ Z : Finset ℝ, (∀ z ∈ Z, 0 < z) → ∀ mult : ℝ → ℕ,
        (∀ z ∈ Z, ∀ k < mult z, iteratedDeriv k (shellLaplaceF D) z = 0) →
          ∑ z ∈ Z, mult z ≤ D.S.card - 1) ∧
      (∀ b : ℝ, uLP D = (b : EReal) → b < D.tm → ∀ H : ℂ → ℂ, OneProfileFeasibleWitness D b H →
        (∃ c : ℝ, b ≤ c ∧ c < D.tm ∧ (H (c : ℂ)).re = 0 ∧
          (∀ n : ℕ, t n < c → (H (t n : ℂ)).re ≤ 0) ∧
          ((∃ n : ℕ, t n = c) → 0 ≤ (deriv H (c : ℂ)).re) ∧
          (∀ x : ℝ, c < x → ∀ F : Finset ℕ, (∀ n : ℕ, n ∈ F ↔ (c < t n ∧ t n ≤ x)) →
            0 ≤ ∑ n ∈ F, airyPQDr D.P D.Q (t n) * (H (t n : ℂ)).re /
              ((airyPQN' D.P D.Q (t n : ℂ)).re) ^ 2)) →
        uSh D = (b : EReal))) := by
  refine ⟨⟨uLP_le_tm D, uLP_eq_tm_iff D, fun hm => ?_, fun hlt => ⟨?_, ?_⟩⟩, ⟨?_, ?_, ?_⟩, ?_,
    ⟨fun n hn T G hG => hankelShellProfile_origin_mass hn hG, shellGapEndpoint_proved D⟩,
    fun hm => ⟨fun n hn => hbNodeWeight_pos D ht hm hn, hbTauN_lt_tm D ht hm⟩,
    fun Z hZ mult hmult => laplace_zero_multiplicity_le D Z hZ mult hmult, airy_node_sum D ht⟩
  · obtain ⟨hΛ, -, hlt⟩ := lambda_chain D hm
    obtain ⟨hτ1, hτ2⟩ := airy_node_square D ht hm
    exact ⟨hΛ, hlt, uSh_le_uLP D, airyLambdaSection_hb_gt_airyZero D hm, hτ1, hτ2⟩
  · obtain ⟨y, hy, h⟩ := (airy_active_height D).laplace_zero hlt
    exact ⟨y, hy, h⟩
  · exact fun b hb H hH z hz hz0 hs => (airy_active_height D).deflation hlt b hb H hH z hz hz0 hs
  · intro b hb hbt H hH hc
    rcases hc with ⟨-, hnn⟩ | hno
    · exact (airy_active_height D).quotient_mass b hb H hH hnn
    · exact (airy_node_sign D ht).1 b hb hbt H hH hno
  · exact fun h => uSh_eq_of_node_bound ht h
  · intro h5
    by_cases h1 : D.S.card = 1
    · exact uSh_eq_uLP_of_card_one D h1
    · have hpos : 0 < D.S.card := Finset.card_pos.mpr D.S_nonempty
      have hm : 2 ≤ D.S.card := by omega
      obtain ⟨-, hle, -⟩ := lambda_chain D hm
      obtain ⟨hτ1, hτ2⟩ := airy_node_square D ht hm
      refine uSh_eq_of_node_bound ht ?_
      have hanti : hbNode t (D.S.card + 2) ≤ hbNode t (D.S.card + D.S.card / 2) := by
        unfold hbNode
        exact ht.1.antitone (by omega)
      refine le_trans (EReal.coe_le_coe_iff.2 (hanti.trans (hτ2.trans hτ1).le)) hle
  · refine ⟨fun hi => ?_, ⟨shell_i_to_ii D, fun h => shell_iv_to_i D (shell_ii_to_iii_liminf h)⟩,
      ⟨shell_i_to_iii D, fun h => shell_iv_to_i D (shell_iii_to_iv h)⟩,
      ⟨fun hi => shell_iii_to_iv (shell_i_to_iii D hi), shell_iv_to_i D⟩⟩
    by_contra hnodd
    obtain ⟨y, hy, hneg⟩ := even_m_laplace_sign D (Nat.not_odd_iff_even.mp hnodd)
    exact absurd (hi y hy) (not_le.mpr hneg)


/-! ### Axiom checks -/

/-- info: 'FormalResearch.SignUncertainty.thm_intro_radii_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms thm_intro_radii_sign

/-- info: 'FormalResearch.SignUncertainty.thm_intro_radii_ce' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms thm_intro_radii_ce

/-- info: 'FormalResearch.SignUncertainty.thm_intro_radii' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms thm_intro_radii

/-- info: 'FormalResearch.SignUncertainty.thm_intro_hb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms thm_intro_hb

/-- info: 'FormalResearch.SignUncertainty.thm_ce_canonical_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms thm_ce_canonical_iff

/-- info: 'FormalResearch.SignUncertainty.thm_ce_shell_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms thm_ce_shell_gap

/-- info: 'FormalResearch.SignUncertainty.thm_ce_shell_gap_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms thm_ce_shell_gap_full

/-- info: 'FormalResearch.SignUncertainty.hankelCutoffLeTm_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelCutoffLeTm_proved

/-- info: 'FormalResearch.SignUncertainty.thm_ce_shell_gap_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms thm_ce_shell_gap_even

/-- info: 'FormalResearch.SignUncertainty.hbMultilevelLower_airy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hbMultilevelLower_airy

/-- info: 'FormalResearch.SignUncertainty.SignSeparationPackage.Tneg_asymp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignSeparationPackage.Tneg_asymp

/-- info: 'FormalResearch.SignUncertainty.hankelT0_eq_hankelT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelT0_eq_hankelT

/-- info: 'FormalResearch.SignUncertainty.laguerre_odd_mode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms laguerre_odd_mode

end FormalResearch.SignUncertainty
