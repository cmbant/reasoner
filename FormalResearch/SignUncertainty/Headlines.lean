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

/-!
# Paper I headline theorems from one input structure each (M0 skeleton)

Source: `CFT/sign_uncertainty/paper/sign_uncertainty_core.tex`, introduction:
`thm:intro-radii`, `thm:intro-gap`. (The old `thm:intro-separation` was deleted from the paper; its
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
would be the theorem itself (deliberate deviation from the usual non-vacuity requirement). Scope:
`thm:intro-hb` (all Hermite–Biehler levels) has no Lean headline yet (milestone M8).

Headlines and their inputs (open fields in bold):

* `thm_intro_radii` (`thm:intro-radii`, `gt:7.9`, `gt:7.12`, `gt:7.12a`), from `RadiiInputs`:
  `hb_thresholds_upper` (`thm:hb-thresholds` upper half at `(P,Q) = (1,0)`, i.e. `u1co:O9p`; proved as
  `hbThresholdsUpper` in `HbUpperM1.lean`, which imports this file, so it is a field here only for import order),
  **`ce_hb_lift_m1`** (`thm:ce-hb-lift`, `m₀ = 1`; its Laplace hypothesis is proved here from
  `shellLaplaceF_m1_pos`). Proved here from these and from `hb_thresholds_lower`, `shell_reduction_m1_proved`: the gluing `ce_radius_airy_order_of_bounds`, the
  origin option `constrained_threshold_eq_unconstrained`, the density expansion `ce_volume_expansion`.
* `thm_intro_gap_i/ii/iii` (`thm:intro-gap`), from `ShellGapInputs D`:
  **`shell_reduction`** (`thm:ce-shell-reduction`), **`ce_hb_lift`** (`thm:ce-hb-lift`). The extraction and
  constraint system `eq:ce-laplace-constraint` of `thm:ce-shell-gap` (Hankel form `HankelShellGapLimit`) is the
  theorem `hankelShellGapLimit_proved` (`ShellGapExtract.lean`) and no longer a field.
  `one_profile_envelope` (`gt:3.1` envelope used in `prop:ce-one-profile`) is a theorem
  (`OneProfileEnvelope.lean`). Proved here from these: `one_profile_feasible_iff`, `one_profile_maximizer_exists`,
  `one_profile_threshold_le_and_endpoint_iff` (`prop:ce-one-profile`), `even_m_laplace_sign`.

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

/-- `thm:hb-thresholds` at `(P, Q) = (1, 0)`, upper half (`u1co:O9p`, Theorem O.9', the one-level
construction): for large `c` and either eigenvalue there is a feasible `f` at a threshold at most
`c/π² + A c^{1/3} + C`. -/
def HbThresholdsUpper : Prop :=
  ∃ C c₀ : ℝ, ∀ c : ℝ, c₀ ≤ c → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
    ∃ (T : ℝ) (f : ℝ → ℝ), IsHankelFeasible c ε T f ∧
      T ≤ c / π ^ 2 + airyOrderCoeff * c ^ (1 / 3 : ℝ) + C

/-- `ce_hb_lift` (`thm:ce-hb-lift`, Cohn–Elkies lift under strict Laplace positivity), for the
Hermite–Biehler configuration `D` (`m = D.S.card`): if `m` is odd and `ℒ_y(-G_N) > 0` for all `y > 0`,
then for every `R_off ≥ 0` there are `K₀` and `d₀` such that in every dimension `d ≥ d₀` and for all
offsets `|r_{j,c}| ≤ R_off` there is a radial normalised continuous integrable Cohn–Elkies pair with
`h ≤ 0` at the shells and for `|x|²/2 ≥ c/π² - (t_m/β₁) c^{1/3} + K₀`. -/
def CeHbLift (D : ShellHBData) : Prop :=
  Odd D.S.card → (∀ y : ℝ, 0 < y → 0 < airyLaplace (fun u => -(D.G (u : ℂ)).re) y) →
    ∀ R_off : ℝ, 0 ≤ R_off → ∃ (K₀ : ℝ) (d₀ : ℕ), ∀ d : ℕ, d₀ ≤ d →
      ∀ r : ℝ → ℕ → ℝ, (∀ t d', |r t d'| ≤ R_off) →
        ∃ (R : ℝ), R ∈ ceShellRadiusSet D r d ∧
          R ^ 2 / 2 ≤ (d : ℝ) / (2 * π ^ 2) - (D.tm / hankelBeta1) * ((d : ℝ) / 2) ^ (1 / 3 : ℝ) + K₀

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

/-- Inputs of `thm:intro-radii`. -/
structure RadiiInputs : Prop extends OneLevelThresholds where
  /-- `thm:ce-hb-lift` with `m₀ = 1`, `N = Ai` (the paper's route II, `ce_radius.tex`). -/
  ce_hb_lift_m1 : CeHbLift ShellHBData.airy

/-- `gt:7.5`, first claim, one level, `ε = -1`: `liminf c^{-1/3}(T_c - c/π²) ≥ A`
(from `radial_compactness` via `radial_rigidity_liminf_ereal`). -/
theorem radial_rigidity_lower :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ c : ℝ in atTop, ∀ (T : ℝ) (f : ℝ → ℝ),
      IsHankelFeasible c (-1) T f → c / π ^ 2 + (airyOrderCoeff - ε) * c ^ (1 / 3 : ℝ) ≤ T :=
  radial_rigidity_lower_of_compactness radial_compactness

/-- Inputs of `thm:intro-gap` for the Hermite–Biehler configuration `D`. -/
structure ShellGapInputs (D : ShellHBData) : Prop where
  shell_reduction : ShellReduction D
  ce_hb_lift : CeHbLift D

/-- `thm:ce-shell-gap` for radial Cohn-Elkies pairs on `ℝ^d`: a theorem
(`hankelShellGapLimit_proved`, then `shellGapLimit_of_hankel`). -/
theorem ShellGapInputs.shell_gap_limit {D : ShellHBData} (_I : ShellGapInputs D) : ShellGapLimit D :=
  shellGapLimit_of_hankel (hankelShellGapLimit_proved D)


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

/-- **Headline B (`gt:7.12`, `gt:7.12a`, `thm:intro-radii`, Cohn–Elkies radius).** (In the paper `r_CE(d)`
is the Schwartz infimum; it equals `optimalL1CERadius d` by `ce_schwartz_radius_eq_L1_radius`.) For every integer
`d ≥ 2`, `r_CE(d)²/2 = d/(2π²) + A (d/2)^{1/3} + O(1)`, and the ball of radius `r_CE(d)/2` has volume
`(πd)^{-1/2} (e/(2π))^{d/2} exp(π² A (d/2)^{1/3} + O(1))`, in both the multiplicative
and the logarithmic form (`eq:intro-density`; the constant `-log π / 2` is absorbed in the `O(1)`).

Proved from `RadiiInputs` (`ce_hb_lift_m1`) and `shell_reduction_m1_proved` by the gluing
`ce_radius_airy_order_of_bounds` and the Stirling expansion `ce_volume_expansion`. -/
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
  -- the upper half from `ce_hb_lift_m1` at `D = airy`, no shells, `R_off = 0`
  obtain ⟨K₀, d_hi, hhi0⟩ := I.ce_hb_lift_m1 (by rw [airy_S_card]; exact odd_one)
    (fun y hy => airy_laplace_negG_pos hy) 0 le_rfl
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

end Radii2

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
  ⟨thm_intro_radii_sign I, thm_intro_radii_ce I⟩

/-! ### Headline C′: `thm:intro-gap` -/

section ShellGap

variable {D : ShellHBData} (I : ShellGapInputs D)
include I

/-- **`thm:intro-gap` (i)** (`thm:ce-shell-reduction`): for bounded shell offsets,
`(R_d^{CE})²/2 ≥ d/(2π²) - (t_m/β₁)(d/2)^{1/3} - O(1)`, uniformly over the offsets (every member of
`ceShellRadiusSet D r d` satisfies the bound, i.e. so does its infimum). The paper's proof is
the reduction itself, so this is the field `shell_reduction`. -/
theorem thm_intro_gap_i : ShellReduction D := I.shell_reduction

/-- **`thm:intro-gap` (ii)** (`thm:ce-shell-gap` with `prop:ce-one-profile`): if `ℒ_y(-G_N) < 0` for some
`y > 0` (this holds for every even `m`, see `thm_intro_gap_ii_even`) and the offsets are `o(c^{1/3})`,
then

* `liminf_{d→∞} ((R_d^{CE})²/2 - d/(2π²))/(d/2)^{1/3} ≥ -u_LP/β₁`: for every real `s` with
  `-β₁ s > u_LP` (equivalently `s < -u_LP/β₁`, with `u_LP = -∞` allowed) eventually every admissible
  radius has `shellNormRadius d R ≥ s`; and
* `u_LP < t_m`, i.e. `-u_LP/β₁ > -t_m/β₁`.

Proved from `shell_gap_limit` (extraction), the theorem `one_profile_envelope` (attainment) and the proved
one-profile reduction (`one_profile_feasible_iff`, `one_profile_maximizer_exists`,
`one_profile_threshold_le_and_endpoint_iff`). -/
theorem thm_intro_gap_ii
    (hlap : ∃ y : ℝ, 0 < y ∧ airyLaplace (fun u => -(D.G (u : ℂ)).re) y < 0)
    (r : ℝ → ℕ → ℝ)
    (hr : ∀ t : ℝ, Tendsto (fun d : ℕ => r t d / ((d : ℝ) / 2) ^ (1 / 3 : ℝ)) atTop (𝓝 0)) :
    (∀ s : ℝ, uLP D < ((-(hankelBeta1 * s) : ℝ) : EReal) →
      ∀ᶠ d : ℕ in atTop, ∀ R ∈ ceShellRadiusSet D r d, s ≤ shellNormRadius d R) ∧
    uLP D < (D.tm : EReal) := by
  refine ⟨fun s hs => ?_, ?_⟩
  · have hinf : ¬ OneProfileFeasible D (-(hankelBeta1 * s)) := fun hf =>
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
      (I.shell_gap_limit r hr (-(hankelBeta1 * s)) φ hφ.tendsto_atTop (fun _ => 0) tendsto_const_nhds
        R hRmem fun k => ?_))
    have hd1 : (1 : ℝ) ≤ (φ k : ℝ) := by exact_mod_cast (hφP k).2
    have hq : 0 < ((φ k : ℝ) / 2) ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
    have h1 := hRlt k
    unfold shellNormRadius at h1
    rw [div_lt_iff₀ hq] at h1
    have hβ := hankelBeta1_pos
    have : -(hankelBeta1 * s) / hankelBeta1 = -s := by field_simp
    rw [this]
    linarith
  · by_cases hfeas : ∃ u : ℝ, OneProfileFeasible D u
    · obtain ⟨u₀, hu₀⟩ := hfeas
      obtain ⟨C, ν, hC, hbound⟩ := one_profile_envelope D u₀ hu₀
      obtain ⟨u_s, hu_s⟩ := one_profile_maximizer_exists D
        { u₀ := u₀, u₀_feasible := hu₀, C₀ := C, ν₀ := ν, hC₀ := hC,
          uniform_env := fun {u H} hu hH hn z => hbound u hu H hH hn z }
      have hle := (one_profile_threshold_le_and_endpoint_iff D).1 u_s hu_s.1
      have hne : u_s ≠ D.tm := by
        intro heq
        obtain ⟨y, hy, hneg⟩ := hlap
        have := ((one_profile_threshold_le_and_endpoint_iff D).2).1 (heq ▸ hu_s.1) y hy
        linarith
      have hlt : u_s < D.tm := lt_of_le_of_ne hle hne
      refine lt_of_le_of_lt (iSup₂_le fun u hu => ?_) (EReal.coe_lt_coe_iff.2 hlt)
      exact EReal.coe_le_coe_iff.2 (hu_s.2 hu)
    · refine lt_of_le_of_lt (iSup₂_le fun u hu => (hfeas ⟨u, hu⟩).elim) (EReal.bot_lt_coe _)

/-- **`thm:intro-gap` (ii), even `m`**: the Laplace hypothesis of (ii) holds for every even
`m = D.S.card` (`even_m_laplace_sign`, no numerical estimates). -/
theorem thm_intro_gap_ii_even (heven : Even D.S.card) (r : ℝ → ℕ → ℝ)
    (hr : ∀ t : ℝ, Tendsto (fun d : ℕ => r t d / ((d : ℝ) / 2) ^ (1 / 3 : ℝ)) atTop (𝓝 0)) :
    (∀ s : ℝ, uLP D < ((-(hankelBeta1 * s) : ℝ) : EReal) →
      ∀ᶠ d : ℕ in atTop, ∀ R ∈ ceShellRadiusSet D r d, s ≤ shellNormRadius d R) ∧
    uLP D < (D.tm : EReal) :=
  thm_intro_gap_ii I (by obtain ⟨y, hy, h⟩ := even_m_laplace_sign D heven; exact ⟨y, hy, h⟩) r hr

/-- **`thm:intro-gap` (iii)**: if `m` is odd and `ℒ_y(-G_N) > 0` for every `y > 0`, then for bounded
offsets `(R_d^{CE})²/2 = d/(2π²) - (t_m/β₁)(d/2)^{1/3} + O(1)`: every admissible radius is above the
model minus `C` (`thm:ce-shell-reduction`) and some admissible radius is below the model plus `C`
(`thm:ce-hb-lift`). The case `m = 1`, `N = Ai` is the Cohn–Elkies half of `thm_intro_radii`. -/
theorem thm_intro_gap_iii (hodd : Odd D.S.card)
    (hpos : ∀ y : ℝ, 0 < y → 0 < airyLaplace (fun u => -(D.G (u : ℂ)).re) y)
    (R_off : ℝ) (hR : 0 ≤ R_off) :
    ∃ (C : ℝ) (d₀ : ℕ), ∀ d : ℕ, d₀ ≤ d → ∀ r : ℝ → ℕ → ℝ, (∀ t d', |r t d'| ≤ R_off) →
      (∀ R ∈ ceShellRadiusSet D r d,
        (d : ℝ) / (2 * π ^ 2) - (D.tm / hankelBeta1) * ((d : ℝ) / 2) ^ (1 / 3 : ℝ) - C ≤ R ^ 2 / 2) ∧
      ∃ R ∈ ceShellRadiusSet D r d,
        R ^ 2 / 2 ≤ (d : ℝ) / (2 * π ^ 2) - (D.tm / hankelBeta1) * ((d : ℝ) / 2) ^ (1 / 3 : ℝ) + C := by
  obtain ⟨C₁, d₁, h₁⟩ := I.shell_reduction R_off hR
  obtain ⟨K₀, d₂, h₂⟩ := I.ce_hb_lift hodd hpos R_off hR
  refine ⟨max C₁ K₀, max d₁ d₂, fun d hd r hr => ⟨fun R hRm => ?_, ?_⟩⟩
  · linarith [h₁ d (le_trans (le_max_left _ _) hd) r hr R hRm, le_max_left C₁ K₀]
  · obtain ⟨R, hRm, hRle⟩ := h₂ d (le_trans (le_max_right _ _) hd) r hr
    exact ⟨R, hRm, by linarith [le_max_right C₁ K₀]⟩

end ShellGap

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

/-- info: 'FormalResearch.SignUncertainty.thm_intro_gap_i' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms thm_intro_gap_i

/-- info: 'FormalResearch.SignUncertainty.thm_intro_gap_ii' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms thm_intro_gap_ii

/-- info: 'FormalResearch.SignUncertainty.thm_intro_gap_ii_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms thm_intro_gap_ii_even

/-- info: 'FormalResearch.SignUncertainty.thm_intro_gap_iii' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms thm_intro_gap_iii

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
