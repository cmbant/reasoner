module

public import FormalResearch.SignUncertainty.Radii

/-!
# Paper I headline theorems from one input structure each (M0 skeleton)

Source: `CFT/sign_uncertainty/paper/sign_uncertainty_core.tex`, introduction:
`thm:intro-radii`, `thm:intro-separation`, `thm:intro-gap`.

Each headline is stated on the concrete objects of `Radii.lean` (Euclidean `A_sign^±(d)`, `r_CE(d)`,
the prescribed-shell class, the Bessel-kernel Hankel thresholds) with the paper's constants, and is
proved from an input structure whose fields are, one-to-one, the TeX theorems the paper's proof cites
(field name = TeX label). **A field is an open theorem about the concrete objects**; progress is the
number of open fields, and a field is discharged only by proving it (then it is dropped from the
structure). Nothing here is a hypothesis-satisfiability exercise: the fields are not witnessed.

Headlines and their inputs (open fields in bold):

* `thm_intro_radii` (`thm:intro-radii`, `gt:7.9`, `gt:7.12`, `gt:7.12a`), from `RadiiInputs`:
  **`hankel_antideriv_facts`** (Weber limit and boundedness for the Bessel kernel; proved for
  `c = 5/2`, `HankelBessel.lean`), **`hankel_euclid_dictionary`** (`gt:7.9`: radial averaging,
  Bochner, BCK/CG reduction, all integer `d ≥ 2`), **`hb_thresholds_lower`**, **`hb_thresholds_upper`**
  (`thm:hb-thresholds` at `(P,Q) = (1,0)`, i.e. `u1cl:multilevel` and `u1co:O9p`),
  **`shell_reduction_m1`** (`thm:ce-shell-reduction`, `m = 1`, with `O(d)` averaging),
  **`ce_hb_lift_m1`** (`thm:ce-hb-lift`, `m₀ = 1`; its Laplace hypothesis is proved here from
  `shellLaplaceF_m1_pos`). Proved here from these: the gluing `ce_radius_airy_order_of_bounds`, the
  origin option `constrained_threshold_eq_unconstrained`, the density expansion `ce_volume_expansion`.
* `thm_intro_separation` (`thm:intro-separation`, `gt:7.9c`), from `SeparationInputs`:
  **`hankel_antideriv_facts`**, **`radial_rigidity_lower`** (`gt:7.5`, one level, `ε = -1`),
  **`hb_thresholds_upper`** (`u1co:O9p`, one level), **`radial_profile_c1`** (`gt:7.5` profile
  identification together with the `C¹` clause of `lem:radial-compactness`). Proved here from these:
  the Hardy–Mellin intertwiner argument (`sign_separation_eventually_le`, via
  `SignSeparationPackage.langer_approx` built from the `C¹` field). The Euclidean statement (2)
  additionally uses `EuclidDictionary` (`hankel_euclid_dictionary`; `laguerre_odd_mode` is proved).
* `thm_intro_gap_i/ii/iii` (`thm:intro-gap`), from `ShellGapInputs D`:
  **`shell_reduction`** (`thm:ce-shell-reduction`), **`shell_gap_limit`** (`thm:ce-shell-gap`,
  extraction and constraint system `eq:ce-laplace-constraint`), **`one_profile_envelope`**
  (`gt:3.1` envelope used in `prop:ce-one-profile`), **`ce_hb_lift`** (`thm:ce-hb-lift`). Proved here
  from these: `one_profile_feasible_iff`, `one_profile_maximizer_exists`,
  `one_profile_threshold_le_and_endpoint_iff` (`prop:ce-one-profile`), `even_m_laplace_sign`.

Conventions. `c = d/2`, `A = |a₁|/β₁` (`airyOrderCoeff`), `airyOrderModel d = d/(2π²) + A (d/2)^{1/3}`.
Radii whose defining set is empty are `+∞` in the paper; the statements below that involve the
prescribed-shell radius quantify over the members of `ceShellRadiusSet`. For the Euclidean radii and
`hankelT` the real `sInf` is used; for `d ≥ 2` the defining sets are nonempty (this is part of the
open fields: `hb_thresholds_upper` for the Hankel side, `hankel_euclid_dictionary` for the Euclidean
side), so the junk value `sInf ∅ = 0` never matters for a true statement.
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

/-- `thm:hb-thresholds` at `(P, Q) = (1, 0)`, lower half (`u1cl:multilevel`, Theorem L.2): every
feasible threshold, for either eigenvalue, is at least `c/π² + A c^{1/3} - C` once `c` is large. -/
def HbThresholdsLower : Prop :=
  ∃ C c₀ : ℝ, ∀ c : ℝ, c₀ ≤ c → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → ∀ (T : ℝ) (f : ℝ → ℝ),
    IsHankelFeasible c ε T f → c / π ^ 2 + airyOrderCoeff * c ^ (1 / 3 : ℝ) - C ≤ T

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

/-- `thm:ce-shell-reduction` (Theorem HB--CE.L) for `D`, bounded offsets: every admissible radius
satisfies `R²/2 ≥ d/(2π²) - (t_m/β₁)(d/2)^{1/3} - O(1)`, uniformly over the allowed offsets. -/
def ShellReduction (D : ShellHBData) : Prop :=
  ∀ R_off : ℝ, 0 ≤ R_off → ∃ (C : ℝ) (d₀ : ℕ), ∀ d : ℕ, d₀ ≤ d →
    ∀ r : ℝ → ℕ → ℝ, (∀ t d', |r t d'| ≤ R_off) →
      ∀ R ∈ ceShellRadiusSet D r d,
        (d : ℝ) / (2 * π ^ 2) - (D.tm / hankelBeta1) * ((d : ℝ) / 2) ^ (1 / 3 : ℝ) - C ≤ R ^ 2 / 2

/-- `thm:ce-shell-gap` (Theorem H.14), extraction and constraint system `eq:ce-laplace-constraint`:
along any sequence of dimensions `d_k → ∞` and admissible pairs (shell offsets `o(c^{1/3})`) whose
thresholds satisfy `R_k²/2 ≤ d_k/(2π²) - (u_*/β₁) c_k^{1/3} + o(c_k^{1/3})` for a fixed real `u_*`,
the window profiles of `p_k = (ĥ+h)/2`, `q_k = (ĥ-h)/2`, normalised by `M[2q_k]`, have limits
`P_∞, Q_∞ ∈ 𝒢` satisfying the two-profile system at `u_*` (`TwoProfileFeasible D u_*`). -/
def ShellGapLimit (D : ShellHBData) : Prop :=
  ∀ r : ℝ → ℕ → ℝ, (∀ t : ℝ, Tendsto (fun d : ℕ => r t d / ((d : ℝ) / 2) ^ (1 / 3 : ℝ)) atTop (𝓝 0)) →
    ∀ (u_star : ℝ) (dk : ℕ → ℕ), Tendsto dk atTop atTop →
      ∀ (ε : ℕ → ℝ), Tendsto ε atTop (𝓝 0) →
        ∀ (R : ℕ → ℝ), (∀ k, R k ∈ ceShellRadiusSet D r (dk k)) →
          (∀ k, R k ^ 2 / 2 ≤ (dk k : ℝ) / (2 * π ^ 2) - (u_star / hankelBeta1) * ((dk k : ℝ) / 2) ^ (1 / 3 : ℝ)
            + ε k * ((dk k : ℝ) / 2) ^ (1 / 3 : ℝ)) →
          TwoProfileFeasible D u_star

/-- `prop:ce-one-profile`, attainment step (uniform envelope from the proof of `gt:3.1`): normalised
one-profile witnesses at thresholds above a feasible `u₀` obey a common bound
`C (1 + |z|)^ν e(z)`. -/
def OneProfileEnvelope (D : ShellHBData) : Prop :=
  ∀ u₀ : ℝ, OneProfileFeasible D u₀ → ∃ C ν : ℝ, 0 ≤ C ∧ ∀ u : ℝ, u₀ ≤ u →
    ∀ H : ℂ → ℂ, OneProfileFeasibleWitness D u H → (∫ x : ℝ, ‖H (x : ℂ)‖) = 1 →
      ∀ z : ℂ, ‖H z‖ ≤ C * (1 + ‖z‖) ^ ν * airyEnv z

/-! ### Input structures -/

/-- `hankel_antideriv_facts`: for `c ≥ 1` the two analytic facts about `φ_c = hankelPhi c` of
`HankelBessel.lean` (boundedness and Weber limit `(2π)^c/Γ(c) ∫_0^X w^{c/2-1} φ_c → 1`,
DLMF 10.22.43). Everything else making `hankelPhi c` a `HankelKernelData` (`φ(0) = 1`, continuity,
`|φ| ≤ 1`) is proved (`hankelKernelData`). Being discharged by a parallel agent. -/
structure HankelKernelFacts : Prop where
  hankel_antideriv_facts : ∀ c : ℝ, 1 ≤ c → HankelAntiderivFacts c

/-- With `HankelAntiderivFacts c` the concrete Bessel kernel is a `HankelKernelData c`
(`hankelKernelData`, with `φ_zero`, `φ_cont`, `φ_bound` proved). -/
theorem HankelKernelFacts.bessel_kernel_data (I : HankelKernelFacts) (c : ℝ) (hc : 1 ≤ c) :
    ∃ K : HankelKernelData c, K.φ = hankelPhi c :=
  ⟨hankelKernelData (by linarith) (I.hankel_antideriv_facts c hc), rfl⟩

/-- The Euclidean/Hankel layer. (`gt:7.9b`, the odd Laguerre mode is a `(-1)`-eigenfunction, is proved:
`laguerre_odd_mode`.)
`hankel_euclid_dictionary` (`gt:7.9`, proof): for every integer `d ≥ 2`,
`A_sign^+(d)²/2 = T_{d/2}^{+1}` and `A_sign^-(d)²/2 = T_{d/2}^{-1}` with the origin condition `f(0) = 0`
(radial averaging over `O(d)`, the radial Fourier transform in every dimension including odd `d`, and
the compact-support uncertainty argument that the average is nonzero). -/
structure EuclidDictionary : Prop where
  hankel_euclid_dictionary : ∀ d : ℕ, 2 ≤ d →
    aSignPos d ^ 2 / 2 = hankelT 1 ((d : ℝ) / 2) ∧ aSignNeg d ^ 2 / 2 = hankelT0 ((d : ℝ) / 2)

/-- `thm:hb-thresholds` at one level, both halves (`HbThresholdsLower`, `HbThresholdsUpper`). -/
structure OneLevelThresholds : Prop where
  hb_thresholds_lower : HbThresholdsLower
  hb_thresholds_upper : HbThresholdsUpper

/-- Inputs of `thm:intro-radii`. -/
structure RadiiInputs : Prop extends HankelKernelFacts, EuclidDictionary, OneLevelThresholds where
  /-- `thm:ce-shell-reduction` at `m = 1` for `r_CE(d)` (after `O(d)` averaging): the negative Fourier
  projection `ĥ - h` is a sign-uncertainty competitor; `r_CE(d)²/2 ≥ d/(2π²) + A (d/2)^{1/3} - O(1)`. -/
  shell_reduction_m1 : ∃ (C : ℝ) (d₀ : ℕ), ∀ d : ℕ, d₀ ≤ d →
    airyOrderModel d - C ≤ optimalL1CERadius d ^ 2 / 2
  /-- `thm:ce-hb-lift` with `m₀ = 1`, `N = Ai` (the paper's route II, `ce_radius.tex`). -/
  ce_hb_lift_m1 : CeHbLift ShellHBData.airy

/-- Inputs of `thm:intro-separation` (`gt:7.9c`), Hankel side. -/
structure SeparationInputs : Prop extends HankelKernelFacts where
  /-- `gt:7.5`, first claim, one level, `ε = -1`: `liminf c^{-1/3}(T_c - c/π²) ≥ A`. -/
  radial_rigidity_lower : ∀ ε : ℝ, 0 < ε → ∀ᶠ c : ℝ in atTop, ∀ (T : ℝ) (f : ℝ → ℝ),
    IsHankelFeasible c (-1) T f → c / π ^ 2 + (airyOrderCoeff - ε) * c ^ (1 / 3 : ℝ) ≤ T
  /-- `u1co:O9p` at one level. -/
  hb_thresholds_upper : HbThresholdsUpper
  /-- `gt:7.5` (identification of the limit) with `lem:radial-compactness` (`C¹` clause): the window
  profile `Ψ_{f,c}/M[f]` of a near-optimal `(-1)`-feasible `f` is `C¹` and converges to
  `G_Ai/‖G_Ai‖₁` together with its first derivative, locally uniformly. -/
  radial_profile_c1 : ∀ R η : ℝ, 0 < η → ∀ᶠ c : ℝ in atTop, ∀ (T : ℝ) (f : ℝ → ℝ),
    IsHankelFeasible c (-1) T f → hankelT (-1) c ≤ T → T ≤ hankelT (-1) c + 1 / c →
      ContDiffOn ℝ 1 (fun u => hankelWindowProfile c f u / hankelMass c f) (Ioo (-R) R) ∧
      ∀ u ∈ Ioo (-R) R,
        |hankelWindowProfile c f u / hankelMass c f - HermiteBiehlerData.airy.normG u| ≤ η ∧
        |deriv (fun v => hankelWindowProfile c f v / hankelMass c f) u -
          deriv HermiteBiehlerData.airy.normG u| ≤ η

/-- Inputs of `thm:intro-gap` for the Hermite–Biehler configuration `D`. -/
structure ShellGapInputs (D : ShellHBData) : Prop where
  shell_reduction : ShellReduction D
  shell_gap_limit : ShellGapLimit D
  one_profile_envelope : OneProfileEnvelope D
  ce_hb_lift : CeHbLift D


/-! ### Headline A and B: `thm:intro-radii` -/

section Radii

variable (I : RadiiInputs)
include I

/-- For all large `d`, the Euclidean radii satisfy `A_sign^±(d)²/2 = T^{±,0}_{d/2}` with `T^{-,0} =
T^{-}` (the exact origin option, `gt:7.9b`) and `T^±_c` within `O(1)` of `c/π² + A c^{1/3}`. -/
private lemma sign_radii_tail :
    ∃ (C : ℝ) (d₁ : ℕ), 2 ≤ d₁ ∧ ∀ d : ℕ, d₁ ≤ d →
      |aSignPos d ^ 2 / 2 - airyOrderModel d| ≤ C ∧ |aSignNeg d ^ 2 / 2 - airyOrderModel d| ≤ C := by
  obtain ⟨C₁, c₁, hlow⟩ := I.hb_thresholds_lower
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
  obtain ⟨hp, hn⟩ := I.hankel_euclid_dictionary d hd2
  have hnonneg : ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → ∃ T f, IsHankelFeasible c ε T f :=
    fun ε hε => by obtain ⟨T, f, hf, _⟩ := hup c (by linarith) ε hε; exact ⟨T, f, hf⟩
  have hb : ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
      |hankelT ε c - airyOrderModel d| ≤ max C₁ C₂ := fun ε hε => by
    rw [airyOrderModel_eq]
    exact hankelT_sub_model_le (fun T f hf => hlow c (by linarith) ε hε T f hf)
      (hup c (by linarith) ε hε)
  have hT0 : hankelT0 c = hankelT (-1) c := by
    refine hankelT0_eq_hankelT hc0 (I.bessel_kernel_data c (by linarith))
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

Proved from `RadiiInputs`; see the module docstring for the open fields used
(`hankel_antideriv_facts`, `hankel_euclid_dictionary`, `hb_thresholds_lower`,
`hb_thresholds_upper`). The second asymptotic form of `gt:7.9` (`A_sign(d)/√d`) is not restated. -/
theorem thm_intro_radii_sign :
    (∃ C : ℝ, ∀ d : ℕ, 2 ≤ d → |aSignPos d ^ 2 / 2 - airyOrderModel d| ≤ C) ∧
    (∃ C : ℝ, ∀ d : ℕ, 2 ≤ d → |aSignNeg d ^ 2 / 2 - airyOrderModel d| ≤ C) := by
  obtain ⟨C, d₁, -, h⟩ := sign_radii_tail I
  exact ⟨(exists_abs_bound_nat (f := fun d => aSignPos d ^ 2 / 2 - airyOrderModel d)
      (fun d hd => (h d hd).1)).imp fun C hC d _ => hC d,
    (exists_abs_bound_nat (f := fun d => aSignNeg d ^ 2 / 2 - airyOrderModel d)
      (fun d hd => (h d hd).2)).imp fun C hC d _ => hC d⟩

/-- **Headline B (`gt:7.12`, `gt:7.12a`, `thm:intro-radii`, Cohn–Elkies radius).** For every integer
`d ≥ 2`, `r_CE(d)²/2 = d/(2π²) + A (d/2)^{1/3} + O(1)`, and the ball of radius `r_CE(d)/2` has volume
`(πd)^{-1/2} (e/(2π))^{d/2} exp(π² A (d/2)^{1/3} + O(1))`, in both the multiplicative
and the logarithmic form (`eq:intro-density`; the constant `-log π / 2` is absorbed in the `O(1)`).

Proved from `RadiiInputs` (`shell_reduction_m1`, `ce_hb_lift_m1`) by the gluing
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
  obtain ⟨C_lo, d_lo, hlo0⟩ := I.shell_reduction_m1
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

/-! ### Headline S: `thm:intro-separation` -/

section Separation

variable (I : SeparationInputs)
include I

/-- Feasible thresholds exist for large `c` (`hb_thresholds_upper`) and are bounded below. -/
private lemma neg_nonempty_ev : ∃ c_u : ℝ, ∀ c : ℝ, c_u ≤ c → ∃ T f, IsHankelFeasible c (-1) T f := by
  obtain ⟨C, c_u, h⟩ := I.hb_thresholds_upper
  exact ⟨c_u, fun c hc => by obtain ⟨T, f, hf, -⟩ := h c hc (-1) (Or.inr rfl); exact ⟨T, f, hf⟩⟩

/-- `(T_c^{-1} - c/π²)/c^{1/3} → A` from `radial_rigidity_lower` and `hb_thresholds_upper`. -/
private lemma hankelT_neg_airy_order :
    Tendsto (fun c : ℝ => (hankelT (-1) c - c / π ^ 2) / c ^ (1 / 3 : ℝ)) atTop
      (𝓝 airyOrderCoeff) := by
  obtain ⟨C₂, c_u, hup⟩ := I.hb_thresholds_upper
  have hA := airyOrderCoeff_pos
  have hnn : ∀ᶠ c : ℝ in atTop, ∀ (T : ℝ) (f : ℝ → ℝ), IsHankelFeasible c (-1) T f →
      c / π ^ 2 + (airyOrderCoeff - airyOrderCoeff) * c ^ (1 / 3 : ℝ) ≤ T :=
    I.radial_rigidity_lower airyOrderCoeff hA
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · -- lower side
    set ε : ℝ := (airyOrderCoeff - a) / 2 with hε
    have hεpos : 0 < ε := by rw [hε]; linarith
    filter_upwards [I.radial_rigidity_lower ε hεpos, eventually_ge_atTop c_u,
      eventually_gt_atTop (0 : ℝ)] with c hc hcu hc0
    obtain ⟨T₀, f₀, hf₀, -⟩ := hup c hcu (-1) (Or.inr rfl)
    have hge : c / π ^ 2 + (airyOrderCoeff - ε) * c ^ (1 / 3 : ℝ) ≤ hankelT (-1) c :=
      le_csInf ⟨T₀, f₀, hf₀⟩ fun T ⟨f, hf⟩ => hc T f hf
    have hq : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
    rw [lt_div_iff₀ hq]
    nlinarith [hge]
  · -- upper side
    have hq0 : Tendsto (fun c : ℝ => C₂ * c ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).const_mul C₂
    have hb' : 0 < b - airyOrderCoeff := by linarith
    filter_upwards [hq0.eventually (gt_mem_nhds hb'), hnn, eventually_ge_atTop c_u,
      eventually_gt_atTop (0 : ℝ)] with c hqc hnc hcu hc0
    obtain ⟨T₀, f₀, hf₀, hT₀⟩ := hup c hcu (-1) (Or.inr rfl)
    have hbdd : BddBelow {T : ℝ | ∃ f, IsHankelFeasible c (-1) T f} :=
      ⟨c / π ^ 2 + (airyOrderCoeff - airyOrderCoeff) * c ^ (1 / 3 : ℝ),
        fun T ⟨f, hf⟩ => hnc T f hf⟩
    have hle : hankelT (-1) c ≤ T₀ := csInf_le hbdd ⟨f₀, hf₀⟩
    have hq : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
    rw [div_lt_iff₀ hq]
    have hinv : c ^ (-(1 / 3 : ℝ)) * c ^ (1 / 3 : ℝ) = 1 := by
      rw [← Real.rpow_add hc0]; norm_num
    have h1 := mul_lt_mul_of_pos_right hqc hq
    rw [mul_assoc, hinv, mul_one] at h1
    nlinarith [h1, hle, hT₀]

/-- The package of `SignSeparationPackage` built from `SeparationInputs`, with its thresholds. -/
private lemma exists_package : ∃ P : SignSeparationPackage, ∀ c : ℝ, P.c₀ ≤ c →
    P.Tpos c = hankelT 1 c ∧ P.Tneg c = hankelT (-1) c := by
  classical
  obtain ⟨c_u, hc_u⟩ := neg_nonempty_ev I
  have hc1 : ∀ c : ℝ, max 1 c_u ≤ c → 1 ≤ c := fun c hc => le_trans (le_max_left _ _) hc
  have hK : ∀ c : ℝ, ∀ hc : max 1 c_u ≤ c,
      (Classical.choose (I.bessel_kernel_data c (hc1 c hc))).φ = hankelPhi c :=
    fun c hc => Classical.choose_spec (I.bessel_kernel_data c (hc1 c hc))
  let P : SignSeparationPackage :=
    { c₀ := max 1 c_u
      hc₀ := lt_of_lt_of_le one_pos (le_max_left _ _)
      K := fun c hc => Classical.choose (I.bessel_kernel_data c (hc1 c hc))
      neg_feasible := fun c hc => by
        obtain ⟨T, f, hf⟩ := hc_u c (le_trans (le_max_right _ _) hc)
        exact ⟨T, f, ((Classical.choose (I.bessel_kernel_data c (hc1 c hc))).isFeasible_iff
          (hK c hc) (-1) T f).2 hf⟩
      Tneg_airy_order := by
        refine (hankelT_neg_airy_order I).congr' ?_
        filter_upwards [eventually_ge_atTop (max 1 c_u)] with c hc
        simp only [dif_pos hc, (Classical.choose (I.bessel_kernel_data c (hc1 c hc))).threshold_eq
          (hK c hc)]
      c1_profile := fun R η hη => by
        filter_upwards [I.radial_profile_c1 R η hη] with c hcev hc T f hf hT1 hT2
        have hKc := hK c hc
        rw [(Classical.choose (I.bessel_kernel_data c (hc1 c hc))).isFeasible_iff hKc] at hf
        simp only [(Classical.choose (I.bessel_kernel_data c (hc1 c hc))).threshold_eq hKc] at hT1 hT2
        exact hcev T f hf hT1 hT2 }
  refine ⟨P, fun c hc => ?_⟩
  have hKc := hK c hc
  constructor
  · show (if hc' : max 1 c_u ≤ c then hankelThreshold c
        (Classical.choose (I.bessel_kernel_data c (hc1 c hc'))) 1 else 0) = _
    rw [dif_pos hc, (Classical.choose (I.bessel_kernel_data c (hc1 c hc))).threshold_eq hKc]
  · show (if hc' : max 1 c_u ≤ c then hankelThreshold c
        (Classical.choose (I.bessel_kernel_data c (hc1 c hc'))) (-1) else 0) = _
    rw [dif_pos hc, (Classical.choose (I.bessel_kernel_data c (hc1 c hc))).threshold_eq hKc]

/-- Theorem 7.9c(1) in quantitative form: `T_c^{+1} - T_c^{-1} ≤ -2/π² + ε₀` eventually. -/
private lemma separation_eventually (ε₀ : ℝ) (hε₀ : 0 < ε₀) :
    ∀ᶠ c : ℝ in atTop, hankelT 1 c - hankelT (-1) c ≤ -(2 / π ^ 2) + ε₀ := by
  obtain ⟨P, hP⟩ := exists_package I
  filter_upwards [sign_separation_eventually_le P ε₀ hε₀, eventually_ge_atTop P.c₀] with c hc hc₀
  rw [← (hP c hc₀).1, ← (hP c hc₀).2]
  exact hc

/-- **Headline S, Hankel form (`gt:7.9c(1)`, `thm:intro-separation`, first line):**
`limsup_{c→∞} (T_c^{+1} - T_c^{-1}) ≤ -2/π²` (limsup in `EReal`, so no coboundedness is assumed).

Proved from `SeparationInputs`: `hankel_antideriv_facts`, `radial_rigidity_lower`, `hb_thresholds_upper`,
`radial_profile_c1`, with the Hardy–Mellin intertwiner argument of `sign_separation_eventually_le`. -/
theorem thm_intro_separation_hankel :
    Filter.limsup (fun c : ℝ => ((hankelT 1 c - hankelT (-1) c : ℝ) : EReal)) atTop ≤
      ((-(2 / π ^ 2) : ℝ) : EReal) := by
  rw [Filter.limsup_le_iff]
  intro y hy
  obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.1 hy
  have hr : -(2 / π ^ 2) < r := EReal.coe_lt_coe_iff.1 hr1
  filter_upwards [separation_eventually I ((r + 2 / π ^ 2) / 2) (by linarith)] with c hc
  refine lt_trans (EReal.coe_lt_coe_iff.2 ?_) hr2
  linarith

end Separation

section SeparationEuclid

variable (I : SeparationInputs) (E : EuclidDictionary)
include I E

/-- For large `c`, the exact origin option does not change `T_c^{-1}` (`gt:7.9b`). -/
private lemma neg_T0_eq_ev : ∀ᶠ c : ℝ in atTop, hankelT0 c = hankelT (-1) c := by
  obtain ⟨c_u, hc_u⟩ := neg_nonempty_ev I
  filter_upwards [I.radial_rigidity_lower airyOrderCoeff airyOrderCoeff_pos,
    eventually_ge_atTop (max 1 c_u), eventually_gt_atTop (0 : ℝ)] with c hc hcu hc0
  have hc1 : 1 ≤ c := le_trans (le_max_left _ _) hcu
  have hne := hc_u c (le_trans (le_max_right _ _) hcu)
  refine hankelT0_eq_hankelT hc0 (I.bessel_kernel_data c hc1) (laguerre_odd_mode (by linarith)) hne ?_
  have hge : c / π ^ 2 + (airyOrderCoeff - airyOrderCoeff) * c ^ (1 / 3 : ℝ) ≤ hankelT (-1) c :=
    le_csInf hne fun T ⟨f, hf⟩ => hc T f hf
  have h4 : 1 / (4 * π) < 1 / π ^ 2 := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [Real.pi_gt_three, Real.pi_lt_four]
  have := mul_lt_mul_of_pos_left h4 hc0
  have e1 : c / π ^ 2 = c * (1 / π ^ 2) := by ring
  have e2 : c / (4 * π) = c * (1 / (4 * π)) := by ring
  rw [sub_self, zero_mul, add_zero] at hge
  linarith

/-- **Headline S, Euclidean form (`gt:7.9c(2)`, `thm:intro-separation`, second line):**
`limsup_{d→∞} ½(A_sign^+(d)² - A_sign^-(d)²) ≤ -2/π²` (integer `d`, limsup in `EReal`).

From `thm_intro_separation_hankel`'s inputs and `EuclidDictionary`
(`hankel_euclid_dictionary`): `A_sign^+(d)²/2 = T_{d/2}^{+1}` and `A_sign^-(d)²/2 = T_{d/2}^{-1,0} =
T_{d/2}^{-1}` for large `d`. -/
theorem thm_intro_separation_radii :
    Filter.limsup (fun d : ℕ => (((aSignPos d ^ 2 - aSignNeg d ^ 2) / 2 : ℝ) : EReal)) atTop ≤
      ((-(2 / π ^ 2) : ℝ) : EReal) := by
  have hc_tend : Tendsto (fun d : ℕ => (d : ℝ) / 2) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num : (0 : ℝ) < 2)
  rw [Filter.limsup_le_iff]
  intro y hy
  obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.1 hy
  have hr : -(2 / π ^ 2) < r := EReal.coe_lt_coe_iff.1 hr1
  filter_upwards [hc_tend.eventually (separation_eventually I ((r + 2 / π ^ 2) / 2) (by linarith)),
    hc_tend.eventually (neg_T0_eq_ev I E), eventually_ge_atTop 2] with d hd hT0 hd2
  refine lt_trans (EReal.coe_lt_coe_iff.2 ?_) hr2
  obtain ⟨hp, hn⟩ := E.hankel_euclid_dictionary d hd2
  have : (aSignPos d ^ 2 - aSignNeg d ^ 2) / 2 =
      hankelT 1 ((d : ℝ) / 2) - hankelT (-1) ((d : ℝ) / 2) := by
    rw [← hT0, ← hn, ← hp]; ring
  rw [this]
  linarith

end SeparationEuclid

/-- **`thm:intro-separation`** (`gt:7.9c`): both lines of `eq:intro-separation`. -/
theorem thm_intro_separation (I : SeparationInputs) (E : EuclidDictionary) :
    Filter.limsup (fun c : ℝ => ((hankelT 1 c - hankelT (-1) c : ℝ) : EReal)) atTop ≤
        ((-(2 / π ^ 2) : ℝ) : EReal) ∧
    Filter.limsup (fun d : ℕ => (((aSignPos d ^ 2 - aSignNeg d ^ 2) / 2 : ℝ) : EReal)) atTop ≤
        ((-(2 / π ^ 2) : ℝ) : EReal) :=
  ⟨thm_intro_separation_hankel I, thm_intro_separation_radii I E⟩

/-- **`thm:intro-radii`** (`gt:7.9`, `gt:7.12`, `gt:7.12a`): the three radii at Airy order, with the
density expansion. -/
theorem thm_intro_radii (I : RadiiInputs) :
    ((∃ C : ℝ, ∀ d : ℕ, 2 ≤ d → |aSignPos d ^ 2 / 2 - airyOrderModel d| ≤ C) ∧
      (∃ C : ℝ, ∀ d : ℕ, 2 ≤ d → |aSignNeg d ^ 2 / 2 - airyOrderModel d| ≤ C)) ∧
    (∃ C : ℝ, ∀ d : ℕ, 2 ≤ d → |optimalL1CERadius d ^ 2 / 2 - airyOrderModel d| ≤ C) :=
  ⟨thm_intro_radii_sign I, (thm_intro_radii_ce I).1⟩

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

Proved from `shell_gap_limit` (extraction), `one_profile_envelope` (attainment) and the proved
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
      obtain ⟨C, ν, hC, hbound⟩ := I.one_profile_envelope u₀ hu₀
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

/-- info: 'FormalResearch.SignUncertainty.thm_intro_separation_hankel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms thm_intro_separation_hankel

/-- info: 'FormalResearch.SignUncertainty.thm_intro_separation_radii' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms thm_intro_separation_radii

/-- info: 'FormalResearch.SignUncertainty.thm_intro_separation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms thm_intro_separation

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

/-- info: 'FormalResearch.SignUncertainty.SignSeparationPackage.langer_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignSeparationPackage.langer_approx

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
