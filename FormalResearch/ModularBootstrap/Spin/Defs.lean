module

public import FormalResearch.ModularBootstrap.Constants
public import FormalResearch.ModularBootstrap.Crossing.Setup
public import FormalResearch.ModularBootstrap.Bessel.Defs
public import FormalResearch.ModularBootstrap.LP.Cayley
public import FormalResearch.ModularBootstrap.Duality.DualMajorant
public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-!
# Continuous-spin modular bootstrap: definitions and basic properties

Concrete definitions for the continuous-spin Virasoro modular bootstrap on the Liouville cone
(`CFT/modular_bootstrap/paper/spinning_foundations.tex`, `spinning_calibration.tex`,
`spinning_dual.tex`, `spinning_s4.tex`).

## Conventions and reuse
- The spinless Virasoro problem is `Crossing.virasoroProblem` (`w = 1`, `Q(q) = (1 - q)²`), with
  gap parameter `virasoroProblem.T_V (c - 1)` and optimal dimension gap
  `virasoroProblem.Delta_best (c - 1)`.
- Charge parameters: `n = c - 1`, `a = n / 12`. Most objects are parameterised directly by `a`
  (matching `Crossing.TestClass`, `Crossing.FixedWeightProblem.cardyV`, etc.).
- Two-dimensional tests `Φ : ℝ × ℝ → ℝ` live in `(r_L, r_R)` coordinates (`t_L = r_L² / 2`,
  `t_R = r_R² / 2`). Their 2D Fourier transform is taken via the lift `spinToEuc Φ` to
  `EuclideanSpace ℝ (Fin 2)` using Mathlib's `𝓕`, which matches `Crossing.radialLift 1`
  pointwise on radial functions (`spinToEuc_radialLift`).
- Laguerre functions `L_m^{(-1/2)}(4π t) e^{-2π t}` reuse `LP.lagPsi (1 / 2) m t`.
- Dual majorants reuse `Duality.hMaj`.
- Modified Bessel functions reuse `Bessel.besselI`, and Chebyshev polynomials reuse
  `Polynomial.Chebyshev.T`.

## Proved basic lemmas
- `spinV1_nonneg`, `spinWc_nonneg`, `spinM2_nonneg`
- `spinToEuc_radialLift`: exact match with `Crossing.radialLift 1`
- `spin_half_mass`: `spinnotes:half`, the half-mass lower bound for weakly feasible tests
- `spinM2_eq_spinWc`, `spinPhiVac_eq_spinWc`: rescaled `x_L, x_R` coordinate identities
- `spinWc_factorization`, `spinWc_le_exp`, `spinWc_exp_mono`: exact Cardy factorisation and
  monotonicity of `w_c(x) e^{-π n x / 3}`
- `spinThrInf_mono_cone`, `spinThrInf_mono_class`: monotonicity of primal infima (the first two
  inequalities of `spinnotes:S1`(c))
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real FourierTransform RealInnerProductSpace

namespace FormalResearch.ModularBootstrap.Spin

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Bessel
open FormalResearch.ModularBootstrap.LP
open FormalResearch.ModularBootstrap.Duality

/-! ### Section 1: Symmetry, coordinates, and radial embedding -/

/-- `D_4` invariance of a function on `ℝ × ℝ`: even in each coordinate and swap-symmetric. -/
def IsD4Invariant (Φ : ℝ × ℝ → ℝ) : Prop :=
  (∀ rL rR : ℝ, Φ (-rL, rR) = Φ (rL, rR)) ∧
  (∀ rL rR : ℝ, Φ (rL, -rR) = Φ (rL, rR)) ∧
  (∀ rL rR : ℝ, Φ (rR, rL) = Φ (rL, rR))

/-- Lift of `Φ : ℝ × ℝ → ℝ` to `EuclideanSpace ℝ (Fin 2) → ℂ` for Mathlib's 2D Fourier transform
`𝓕`, matching the kernel `e^{-2π i (r_L x_L + r_R x_R)}` of `spinning_foundations.tex`. -/
def spinToEuc (Φ : ℝ × ℝ → ℝ) (x : EuclideanSpace ℝ (Fin 2)) : ℂ :=
  ((Φ (x 0, x 1) : ℝ) : ℂ)

/-- Radial lift of a spinless test `g : ℝ → ℝ` to `ℝ × ℝ` via `t = (r_L² + r_R²) / 2`. -/
noncomputable def spinRadialLift (g : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  g ((p.1 ^ 2 + p.2 ^ 2) / 2)

/-- Evaluation of a `D_4`-invariant test `Φ` in spectral `(t_L, t_R)` coordinates (`t_u = r_u² / 2`)
on the quadrant `t_L, t_R ≥ 0`. -/
noncomputable def spinEvalT (Φ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  Φ (Real.sqrt (2 * p.1), Real.sqrt (2 * p.2))

lemma spinRadialLift_d4 (g : ℝ → ℝ) : IsD4Invariant (spinRadialLift g) := by
  refine ⟨fun rL rR => ?_, fun rL rR => ?_, fun rL rR => ?_⟩ <;>
    simp only [spinRadialLift, neg_sq, add_comm]

lemma spinToEuc_radialLift (g : ℝ → ℝ) :
    spinToEuc (spinRadialLift g) = radialLift 1 g := by
  ext x
  simp only [spinToEuc, spinRadialLift, radialLift]
  congr 2
  have hnorm : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  rw [hnorm]

lemma spinEvalT_radialLift (g : ℝ → ℝ) {p : ℝ × ℝ} (hp1 : 0 ≤ p.1) (hp2 : 0 ≤ p.2) :
    spinEvalT (spinRadialLift g) p = g (p.1 + p.2) := by
  simp only [spinEvalT, spinRadialLift]
  rw [Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]
  congr 1; ring

/-! ### Section 2: Chiral Cardy weight, norms, and admissible test classes -/

/-- One-dimensional chiral Cardy weight
`V_1(r) = cosh(2π √a r) - cosh(2π √(a - 2) r)`. -/
noncomputable def spinV1 (a r : ℝ) : ℝ :=
  Real.cosh (2 * π * Real.sqrt a * r) - Real.cosh (2 * π * Real.sqrt (a - 2) * r)

lemma spinV1_even (a r : ℝ) : spinV1 a (-r) = spinV1 a r := by
  simp [spinV1, Real.cosh_neg]

lemma spinV1_nonneg {a : ℝ} (_ha : 2 ≤ a) (r : ℝ) : 0 ≤ spinV1 a r := by
  unfold spinV1
  have h1 : Real.sqrt (a - 2) ≤ Real.sqrt a := Real.sqrt_le_sqrt (by linarith)
  have h2 : |2 * π * Real.sqrt (a - 2) * r| ≤ |2 * π * Real.sqrt a * r| := by
    simp only [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ)),
      abs_of_nonneg Real.pi_pos.le, abs_of_nonneg (Real.sqrt_nonneg _)]
    gcongr
  rw [sub_nonneg]
  exact Real.cosh_le_cosh.mpr h2

/-- Weighted `L^1` Cardy norm `M_2[Φ] = ∬_{ℝ²} |Φ(r_L, r_R)| V_1(r_L) V_1(r_R) dr_L dr_R`. -/
noncomputable def spinM2 (a : ℝ) (Φ : ℝ × ℝ → ℝ) : ℝ :=
  ∫ p : ℝ × ℝ, |Φ p| * spinV1 a p.1 * spinV1 a p.2

/-- Vacuum pairing `Φ_vac = -∬_{ℝ²} Φ(r_L, r_R) V_1(r_L) V_1(r_R) dr_L dr_R`. -/
noncomputable def spinPhiVac (a : ℝ) (Φ : ℝ × ℝ → ℝ) : ℝ :=
  -(∫ p : ℝ × ℝ, Φ p * spinV1 a p.1 * spinV1 a p.2)

/-- Stronger exponential norm
`J[Φ] = ∬_{ℝ²} |Φ(r_L, r_R)| cosh(2π √a r_L) cosh(2π √a r_R) dr_L dr_R`. -/
noncomputable def spinJ (a : ℝ) (Φ : ℝ × ℝ → ℝ) : ℝ :=
  ∫ p : ℝ × ℝ, |Φ p| * Real.cosh (2 * π * Real.sqrt a * p.1) *
    Real.cosh (2 * π * Real.sqrt a * p.2)

lemma spinM2_nonneg {a : ℝ} (ha : 2 ≤ a) (Φ : ℝ × ℝ → ℝ) : 0 ≤ spinM2 a Φ :=
  integral_nonneg fun p =>
    mul_nonneg (mul_nonneg (abs_nonneg _) (spinV1_nonneg ha p.1)) (spinV1_nonneg ha p.2)

/-- Full continuous-spin test class `\overline{\mathcal A}_{\rm spin}` at shift `a`:
continuous, integrable, `D_4`-invariant, real Fourier-odd (`\hat Φ = -Φ`) with `M_2[Φ] < ∞`. -/
structure SpinTestClass (a : ℝ) (Φ : ℝ × ℝ → ℝ) : Prop where
  cont : Continuous Φ
  int : Integrable Φ
  d4_inv : IsD4Invariant Φ
  fourier_odd : 𝓕 (spinToEuc Φ) = -(spinToEuc Φ)
  int_M2 : Integrable (fun p : ℝ × ℝ => |Φ p| * spinV1 a p.1 * spinV1 a p.2)

/-- The `J`-finite subclass `\overline{\mathcal A}_{\rm spin}^J = {Φ ∈ \overline{\mathcal A}_{\rm spin} : J[Φ] < ∞}`. -/
structure SpinTestClassJ (a : ℝ) (Φ : ℝ × ℝ → ℝ) : Prop where
  base : SpinTestClass a Φ
  int_J : Integrable (fun p : ℝ × ℝ => |Φ p| * Real.cosh (2 * π * Real.sqrt a * p.1) *
    Real.cosh (2 * π * Real.sqrt a * p.2))

/-- Swap-symmetrised odd two-variable Laguerre basis function in `(r_L, r_R)` coordinates:
`½ (ψ_m(r_L²/2) ψ_n(r_R²/2) + ψ_m(r_R²/2) ψ_n(r_L²/2))` where `ψ_k = LP.lagPsi (1/2) k`. -/
noncomputable def spinOddLaguerreBasis (m n : ℕ) (p : ℝ × ℝ) : ℝ :=
  (1 / 2 : ℝ) * (lagPsi (1 / 2) m (p.1 ^ 2 / 2) * lagPsi (1 / 2) n (p.2 ^ 2 / 2) +
    lagPsi (1 / 2) m (p.2 ^ 2 / 2) * lagPsi (1 / 2) n (p.1 ^ 2 / 2))

/-- Certified subclass `\mathcal B` (`spinning_dual.tex`): the real linear span of swap-symmetric
odd two-variable Laguerre basis functions (`m + n` odd) and radial lifts `spinRadialLift (hMaj a β₀)`
of the dual majorants (`0 < β₀ ≤ 1 / 2`). -/
def SpinCertifiedClass (a : ℝ) (Φ : ℝ × ℝ → ℝ) : Prop :=
  Φ ∈ Submodule.span ℝ
    ({f : ℝ × ℝ → ℝ | ∃ m n : ℕ, Odd (m + n) ∧ f = spinOddLaguerreBasis m n} ∪
     {f : ℝ × ℝ → ℝ | ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ 1 / 2 ∧ f = spinRadialLift (hMaj a β₀)})

lemma SpinTestClass.int_vac {a : ℝ} (ha : 2 ≤ a) {Φ : ℝ × ℝ → ℝ} (hΦ : SpinTestClass a Φ) :
    Integrable (fun p : ℝ × ℝ => Φ p * spinV1 a p.1 * spinV1 a p.2) := by
  refine hΦ.int_M2.mono' ?_ (Eventually.of_forall fun p => ?_)
  · have hV1 : Continuous (spinV1 a) := by unfold spinV1; fun_prop
    exact ((hΦ.cont.mul (hV1.comp continuous_fst)).mul (hV1.comp continuous_snd)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (spinV1_nonneg ha p.1), abs_of_nonneg (spinV1_nonneg ha p.2)]

lemma SpinTestClass.int_neg_part {a : ℝ} (ha : 2 ≤ a) {Φ : ℝ × ℝ → ℝ} (hΦ : SpinTestClass a Φ) :
    Integrable (fun p : ℝ × ℝ => max (-Φ p) 0 * spinV1 a p.1 * spinV1 a p.2) := by
  refine hΦ.int_M2.mono' ?_ (Eventually.of_forall fun p => ?_)
  · have hV1 : Continuous (spinV1 a) := by unfold spinV1; fun_prop
    have hneg : Continuous (fun p : ℝ × ℝ => max (-Φ p) 0) :=
      (hΦ.cont.neg).max continuous_const
    exact ((hneg.mul (hV1.comp continuous_fst)).mul (hV1.comp continuous_snd)).aestronglyMeasurable
  · have hnn : 0 ≤ max (-Φ p) 0 := le_max_right _ _
    have hle : max (-Φ p) 0 ≤ |Φ p| := max_le (neg_le_abs _) (abs_nonneg _)
    rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg hnn (spinV1_nonneg ha p.1))
      (spinV1_nonneg ha p.2))]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hle (spinV1_nonneg ha p.1)) (spinV1_nonneg ha p.2)

/-- **`spinnotes:half`**: if `Φ ∈ \overline{\mathcal A}_{\rm spin}` has `Φ_vac ≥ 0` (at `a ≥ 2`),
then `∬_{ℝ²} Φ_- V_1 ⊗ V_1 ≥ ½ M_2[Φ]`. -/
theorem spin_half_mass {a : ℝ} (ha : 2 ≤ a) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass a Φ) (hvac : 0 ≤ spinPhiVac a Φ) :
    (1 / 2 : ℝ) * spinM2 a Φ ≤
      ∫ p : ℝ × ℝ, max (-Φ p) 0 * spinV1 a p.1 * spinV1 a p.2 := by
  have hpt : ∀ p : ℝ × ℝ,
      |Φ p| * spinV1 a p.1 * spinV1 a p.2 - Φ p * spinV1 a p.1 * spinV1 a p.2 =
        2 * (max (-Φ p) 0 * spinV1 a p.1 * spinV1 a p.2) := by
    intro p
    have habs : |Φ p| - Φ p = 2 * max (-Φ p) 0 := by
      rcases le_total 0 (Φ p) with h | h
      · rw [abs_of_nonneg h, max_eq_right (by linarith)]; ring
      · rw [abs_of_nonpos h, max_eq_left (by linarith)]; ring
    calc |Φ p| * spinV1 a p.1 * spinV1 a p.2 - Φ p * spinV1 a p.1 * spinV1 a p.2
        = (|Φ p| - Φ p) * spinV1 a p.1 * spinV1 a p.2 := by ring
      _ = 2 * (max (-Φ p) 0 * spinV1 a p.1 * spinV1 a p.2) := by rw [habs]; ring
  have hint_sub :
      (∫ p : ℝ × ℝ, |Φ p| * spinV1 a p.1 * spinV1 a p.2) -
        (∫ p : ℝ × ℝ, Φ p * spinV1 a p.1 * spinV1 a p.2) =
      2 * ∫ p : ℝ × ℝ, max (-Φ p) 0 * spinV1 a p.1 * spinV1 a p.2 := by
    rw [← integral_sub hΦ.int_M2 (hΦ.int_vac ha), ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall hpt)
  unfold spinM2 spinPhiVac at *
  linarith

/-! ### Section 3: Spectral cones, feasibility, and primal infima -/

/-- Continuous-spin Liouville cone `\Omega_L(T) = {(t_L, t_R) : t_L, t_R ≥ 0, t_L + t_R ≥ T}`. -/
def liouvilleCone (T : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ T ≤ p.1 + p.2}

/-- Integer-spin subset `\Omega_{\mathbb Z}(T) = \Omega_L(T) ∩ {t_L - t_R ∈ ℤ}`. -/
def integerSpinCone (T : ℝ) : Set (ℝ × ℝ) :=
  {p | p ∈ liouvilleCone T ∧ ∃ j : ℤ, p.1 - p.2 = j}

/-- Wider spectral cone `{(t_L, t_R) : t_L, t_R ≥ -η a, t_L + t_R ≥ T}` (`s4:S4`). -/
def widerCone (a η T : ℝ) : Set (ℝ × ℝ) :=
  {p | -(η * a) ≤ p.1 ∧ -(η * a) ≤ p.2 ∧ T ≤ p.1 + p.2}

lemma integerSpinCone_subset_liouvilleCone (T : ℝ) :
    integerSpinCone T ⊆ liouvilleCone T := fun _ h => h.1

lemma liouvilleCone_subset_widerCone {a η : ℝ} (ha : 0 ≤ a) (hη : 0 ≤ η) (T : ℝ) :
    liouvilleCone T ⊆ widerCone a η T := fun _ ⟨h1, h2, h3⟩ =>
  ⟨by nlinarith, by nlinarith, h3⟩

/-- Strict feasibility of `Φ ∈ C` on `Ω(T)` at shift `a`: `Φ_vac > 0` and `Φ ≥ 0` on `Ω(T)`. -/
def SpinIsFeasible (C : (ℝ × ℝ → ℝ) → Prop) (Ω : ℝ → Set (ℝ × ℝ))
    (a T : ℝ) (Φ : ℝ × ℝ → ℝ) : Prop :=
  C Φ ∧ 0 < spinPhiVac a Φ ∧ ∀ p ∈ Ω T, 0 ≤ spinEvalT Φ p

/-- Weak feasibility of `Φ ∈ \overline{\mathcal A}_{\rm spin}` on `\Omega_L(T)`:
`M_2[Φ] > 0`, `Φ_vac ≥ 0`, and `Φ ≥ 0` on `\Omega_L(T)`. -/
def SpinIsWeaklyFeasible (a T : ℝ) (Φ : ℝ × ℝ → ℝ) : Prop :=
  SpinTestClass a Φ ∧ 0 < spinM2 a Φ ∧ 0 ≤ spinPhiVac a Φ ∧
    ∀ p ∈ liouvilleCone T, 0 ≤ spinEvalT Φ p

/-- Slack feasibility of `Φ ∈ \overline{\mathcal A}_{\rm spin}` on `\Omega_L(T)` (`s4:S4`):
`M_2[Φ] > 0`, `Φ_vac ≥ -n^{-1} M_2[Φ]` (with `n = 12 a`), and `Φ ≥ 0` on `\Omega_L(T)`. -/
def SpinIsSlackFeasible (a T : ℝ) (Φ : ℝ × ℝ → ℝ) : Prop :=
  SpinTestClass a Φ ∧ 0 < spinM2 a Φ ∧ -(12 * a)⁻¹ * spinM2 a Φ ≤ spinPhiVac a Φ ∧
    ∀ p ∈ liouvilleCone T, 0 ≤ spinEvalT Φ p

lemma SpinIsFeasible.isWeaklyFeasible {a T : ℝ} (ha : 2 ≤ a) {Φ : ℝ × ℝ → ℝ}
    (h : SpinIsFeasible (SpinTestClass a) liouvilleCone a T Φ) :
    SpinIsWeaklyFeasible a T Φ := by
  refine ⟨h.1, ?_, h.2.1.le, h.2.2⟩
  by_contra hle
  push Not at hle
  have hm0 : spinM2 a Φ = 0 := le_antisymm hle (spinM2_nonneg ha Φ)
  have hhalf := spin_half_mass ha h.1 h.2.1.le
  have hle_M2 : ∫ p : ℝ × ℝ, max (-Φ p) 0 * spinV1 a p.1 * spinV1 a p.2 ≤ spinM2 a Φ := by
    refine integral_mono (h.1.int_neg_part ha) h.1.int_M2 fun p => ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (max_le (neg_le_abs _) (abs_nonneg _)) (spinV1_nonneg ha p.1))
      (spinV1_nonneg ha p.2)
  have hneg0 : ∫ p : ℝ × ℝ, max (-Φ p) 0 * spinV1 a p.1 * spinV1 a p.2 = 0 := by linarith
  have hvac_le : spinPhiVac a Φ ≤ spinM2 a Φ := by
    unfold spinPhiVac spinM2
    rw [← integral_neg]
    refine integral_mono (h.1.int_vac ha).neg h.1.int_M2 fun p => ?_
    have : -(Φ p * spinV1 a p.1 * spinV1 a p.2) = (-Φ p) * spinV1 a p.1 * spinV1 a p.2 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (neg_le_abs _) (spinV1_nonneg ha p.1)) (spinV1_nonneg ha p.2)
  linarith [h.2.1]

/-- Strict primal infimum `T(C; Ω) = inf {T > 0 : ∃ Φ ∈ C, Φ ≥ 0 on Ω(T), Φ_vac > 0}`. -/
noncomputable def spinThrInf (C : (ℝ × ℝ → ℝ) → Prop) (Ω : ℝ → Set (ℝ × ℝ)) (a : ℝ) : ℝ :=
  sInf {T : ℝ | 0 < T ∧ ∃ Φ, SpinIsFeasible C Ω a T Φ}

/-- Optimal continuous-spin Liouville gap `\Delta_L(c) = a + T(\overline{\mathcal A}_{\rm spin}; \Omega_L)`. -/
noncomputable def spinDeltaL (c : ℝ) : ℝ :=
  (c - 1) / 12 + spinThrInf (SpinTestClass ((c - 1) / 12)) liouvilleCone ((c - 1) / 12)

/-- Optimal `J`-finite continuous-spin gap `\Delta_{\rm spin}(c) = a + T(\overline{\mathcal A}_{\rm spin}^J; \Omega_L)`. -/
noncomputable def spinDeltaSpin (c : ℝ) : ℝ :=
  (c - 1) / 12 + spinThrInf (SpinTestClassJ ((c - 1) / 12)) liouvilleCone ((c - 1) / 12)

/-- Optimal integer-spin gap `\Delta_{\rm best}^{\overline{\mathcal A}_{\rm spin}}(\Omega_{\mathbb Z})`. -/
noncomputable def spinDeltaInt (c : ℝ) : ℝ :=
  (c - 1) / 12 + spinThrInf (SpinTestClass ((c - 1) / 12)) integerSpinCone ((c - 1) / 12)

lemma spinThrInf_mono_cone {C : (ℝ × ℝ → ℝ) → Prop} {Ω₁ Ω₂ : ℝ → Set (ℝ × ℝ)} {a : ℝ}
    (hsub : ∀ T, Ω₁ T ⊆ Ω₂ T)
    (hne : {T : ℝ | 0 < T ∧ ∃ Φ, SpinIsFeasible C Ω₂ a T Φ}.Nonempty) :
    spinThrInf C Ω₁ a ≤ spinThrInf C Ω₂ a := by
  unfold spinThrInf
  refine csInf_le_csInf ⟨0, fun T hT => hT.1.le⟩ hne ?_
  rintro T ⟨hT, Φ, hC, hvac, hpos⟩
  exact ⟨hT, Φ, hC, hvac, fun p hp => hpos p (hsub T hp)⟩

lemma spinThrInf_mono_class {C₁ C₂ : (ℝ × ℝ → ℝ) → Prop} {Ω : ℝ → Set (ℝ × ℝ)} {a : ℝ}
    (hsub : ∀ Φ, C₂ Φ → C₁ Φ)
    (hne : {T : ℝ | 0 < T ∧ ∃ Φ, SpinIsFeasible C₂ Ω a T Φ}.Nonempty) :
    spinThrInf C₁ Ω a ≤ spinThrInf C₂ Ω a := by
  unfold spinThrInf
  refine csInf_le_csInf ⟨0, fun T hT => hT.1.le⟩ hne ?_
  rintro T ⟨hT, Φ, hC, hvac, hpos⟩
  exact ⟨hT, Φ, hsub Φ hC, hvac, hpos⟩

/-- First inequality of `spinnotes:S1`(c): `\Delta_{\rm int} ≤ \Delta_L`, whenever a strictly
feasible test exists on `\Omega_L`. -/
theorem spinDeltaInt_le_spinDeltaL (c : ℝ)
    (hne : {T : ℝ | 0 < T ∧ ∃ Φ,
      SpinIsFeasible (SpinTestClass ((c - 1) / 12)) liouvilleCone ((c - 1) / 12) T Φ}.Nonempty) :
    spinDeltaInt c ≤ spinDeltaL c := by
  unfold spinDeltaInt spinDeltaL
  linarith [spinThrInf_mono_cone integerSpinCone_subset_liouvilleCone hne]

/-- Second inequality of `spinnotes:S1`(c): `\Delta_L ≤ \Delta_{\rm spin}`, whenever a strictly
feasible `J`-finite test exists on `\Omega_L`. -/
theorem spinDeltaL_le_spinDeltaSpin (c : ℝ)
    (hne : {T : ℝ | 0 < T ∧ ∃ Φ,
      SpinIsFeasible (SpinTestClassJ ((c - 1) / 12)) liouvilleCone ((c - 1) / 12) T Φ}.Nonempty) :
    spinDeltaL c ≤ spinDeltaSpin c := by
  unfold spinDeltaL spinDeltaSpin
  linarith [spinThrInf_mono_class (fun _ h => h.base) hne]

/-! ### Section 4: Two-variable crossing measures (`sd:eSD1`) and Cardy harmonics (`S1`(b)) -/

/-- Chiral vacuum factor `q(β) = e^{π a β} (1 - e^{-2π β})`. -/
noncomputable def spinVacuumQ (a β : ℝ) : ℝ :=
  Real.exp (π * a * β) * (1 - Real.exp (-2 * π * β))

/-- Two-variable vacuum factor `v(β_L, β_R) = q(β_L) q(β_R)`. -/
noncomputable def spinVacuumV (a βL βR : ℝ) : ℝ :=
  spinVacuumQ a βL * spinVacuumQ a βR

/-- Two-variable thermal crossing kernel
`X_{β_L, β_R}(t_L, t_R) = e^{-2π(β_L t_L + β_R t_R)} - (β_L β_R)^{-1/2} e^{-2π(t_L/β_L + t_R/β_R)}`. -/
noncomputable def spinThermalX (βL βR tL tR : ℝ) : ℝ :=
  Real.exp (-2 * π * (βL * tL + βR * tR)) -
    (βL * βR) ^ (-(1 / 2 : ℝ)) * Real.exp (-2 * π * (tL / βL + tR / βR))

/-- Vacuum value `X_{β_L, β_R, vac} = v(β_L, β_R) - (β_L β_R)^{-1/2} v(β_L^{-1}, β_R^{-1})`. -/
noncomputable def spinThermalXVac (a βL βR : ℝ) : ℝ :=
  spinVacuumV a βL βR - (βL * βR) ^ (-(1 / 2 : ℝ)) * spinVacuumV a βL⁻¹ βR⁻¹

/-- Positive two-variable crossing measure on `[0, ∞)²` satisfying `(sd:eSD1)`. -/
structure SpinCrossingMeasure (a : ℝ) where
  ν : Measure (ℝ × ℝ)
  supp_quad : ν ({p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2}ᶜ) = 0
  finite_laplace : ∀ {β : ℝ}, 0 < β →
    Integrable (fun p : ℝ × ℝ => Real.exp (-2 * π * β * (p.1 + p.2))) ν
  crossing : ∀ {βL βR : ℝ}, 0 < βL → 0 < βR →
    ∫ p : ℝ × ℝ, spinThermalX βL βR p.1 p.2 ∂ν = -spinThermalXVac a βL βR

/-- Maximal crossing-measure gap `\tau_{\max}(Ω)` on a cone `Ω`. -/
noncomputable def spinTauMax (a : ℝ) (Ω : ℝ → Set (ℝ × ℝ)) : ℝ :=
  sSup {τ : ℝ | 0 < τ ∧ ∃ meas : SpinCrossingMeasure a, meas.ν (Ω τ)ᶜ = 0}

/-- `D_4` angular harmonics `V_{2,\ell}(t) = ∫_0^{2π} cos(4\ell ψ) V_1(r_L) V_1(r_R) dψ`
around the zero-spin diagonal `(r_L, r_R) = √(2t)(cos(π/4 + ψ), sin(π/4 + ψ))`. -/
noncomputable def spinV2Harmonic (a : ℝ) (ℓ : ℕ) (t : ℝ) : ℝ :=
  ∫ ψ in (0 : ℝ)..(2 * π),
    Real.cos (4 * (ℓ : ℝ) * ψ) *
      spinV1 a (Real.sqrt (2 * t) * Real.cos (π / 4 + ψ)) *
      spinV1 a (Real.sqrt (2 * t) * Real.sin (π / 4 + ψ))

/-! ### Section 5: Rescaled coordinates, difference operators, and projections (`S22`–`S24`, `C1`, `C3`) -/

/-- Contraction factor `\gamma_a = \sqrt{1 - 2/a}`. -/
noncomputable def spinGamma (a : ℝ) : ℝ := Real.sqrt (1 - 2 / a)

/-- Outward dilation factor `\lambda = \gamma_a^{-1}`. -/
noncomputable def spinLambda (a : ℝ) : ℝ := (spinGamma a)⁻¹

/-- Rescaled test `\mathcal G(x_L, x_R) = Φ(2√a x_L, 2√a x_R)`. -/
noncomputable def spinG (a : ℝ) (Φ : ℝ × ℝ → ℝ) (xL xR : ℝ) : ℝ :=
  Φ (2 * Real.sqrt a * xL, 2 * Real.sqrt a * xR)

/-- Complex Fourier continuation of `\mathcal G` via Fourier oddness `\hat Φ = -Φ`:
`\mathcal G(b_L, b_R) = -∬ Φ(r_L, r_R) cos(4π√a r_L b_L) cos(4π√a r_R b_R) dr_L dr_R`. -/
noncomputable def spinGC (a : ℝ) (Φ : ℝ × ℝ → ℝ) (bL bR : ℂ) : ℂ :=
  -(∫ p : ℝ × ℝ, (Φ p : ℂ) *
    Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * bL) *
    Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * bR))

/-- Rescaled chiral Cardy weight `w_c(x) = 2√a V_1(2√a x)`. -/
noncomputable def spinWc (a x : ℝ) : ℝ :=
  2 * Real.sqrt a * spinV1 a (2 * Real.sqrt a * x)

/-- Open horizontal strip `\mathcal S_θ = {b ∈ ℂ : |Im b| < θ}`. -/
def spinStrip (θ : ℝ) : Set ℂ := {b : ℂ | |b.im| < θ}

/-- Real inward double difference `\mathcal D_a \mathcal G = (I - T_L)(I - T_R) \mathcal G`. -/
noncomputable def spinDa (a : ℝ) (Φ : ℝ × ℝ → ℝ) (xL xR : ℝ) : ℝ :=
  spinG a Φ xL xR - spinG a Φ (spinGamma a * xL) xR -
    spinG a Φ xL (spinGamma a * xR) + spinG a Φ (spinGamma a * xL) (spinGamma a * xR)

/-- Complex Fourier representation of `\mathcal D_a \mathcal G` on `\mathcal S_{1/2}²`. -/
noncomputable def spinDaC (a : ℝ) (Φ : ℝ × ℝ → ℝ) (bL bR : ℂ) : ℂ :=
  -(∫ p : ℝ × ℝ, (Φ p : ℂ) *
    (Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * bL) -
      Complex.cos (4 * π * (Real.sqrt (a - 2) : ℂ) * (p.1 : ℂ) * bL)) *
    (Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * bR) -
      Complex.cos (4 * π * (Real.sqrt (a - 2) : ℂ) * (p.2 : ℂ) * bR)))

/-- Real outward double difference `\Delta_a \mathcal G(x_L, x_R) = \mathcal D_a \mathcal G(\lambda x_L, \lambda x_R)`. -/
noncomputable def spinDeltaA (a : ℝ) (Φ : ℝ × ℝ → ℝ) (xL xR : ℝ) : ℝ :=
  spinDa a Φ (spinLambda a * xL) (spinLambda a * xR)

/-- Complex outward double difference `\Delta_a \mathcal G(b_L, b_R) = \mathcal D_a \mathcal G(\lambda b_L, \lambda b_R)`. -/
noncomputable def spinDeltaAC (a : ℝ) (Φ : ℝ × ℝ → ℝ) (bL bR : ℂ) : ℂ :=
  spinDaC a Φ ((spinLambda a : ℂ) * bL) ((spinLambda a : ℂ) * bR)

/-- Linear growth rate `L(x) = 2π|x| / 3`. -/
noncomputable def spinL (x : ℝ) : ℝ := 2 * π * |x| / 3

/-- Shifted fold tip `b_* = \gamma_a \xi_*`. -/
noncomputable def spinBStar (a : ℝ) : ℝ := spinGamma a * xiStar

/-- Transverse Gaussian width `\sigma_0 = 1 / 20`. -/
noncomputable def spinSigma0 : ℝ := 1 / 20

/-- Uncalibrated longitudinal projection kernel `h_b(d)` (`spinnotes:S23`). -/
noncomputable def spinHb (b : ℂ) (d : ℝ) : ℂ :=
  ((1 + xiStar ^ 2 : ℝ) : ℂ) / (1 + b ^ 2) *
    (Complex.tanh ((b + (d : ℂ)) / 2) ^ 2 * Complex.tanh ((b - (d : ℂ)) / 2) ^ 2) /
    ((Real.tanh (xiStar / 2) ^ 4 : ℝ) : ℂ) *
    Complex.exp (-(((d ^ 2 / spinSigma0 ^ 2 : ℝ) : ℂ)))

/-- Uncalibrated longitudinal scalar projection `G_{\rm eff}(b)` (`spinnotes:S23`). -/
noncomputable def spinGeff (a : ℝ) (Φ : ℝ × ℝ → ℝ) (b : ℂ) : ℂ :=
  ((1 / (Real.sqrt π * spinSigma0) : ℝ) : ℂ) *
    ∫ d : ℝ, spinHb b d * spinGC a Φ (b + (d : ℂ)) (b - (d : ℂ))

/-- Sub-bistrip weighted `L^1` integral `I_\theta[Φ]` (`spinnotes:S24`). -/
noncomputable def spinITheta (a θ : ℝ) (Φ : ℝ × ℝ → ℝ) : ℝ :=
  ∫ p : ℝ × ℝ, |Φ p| * Real.cosh (4 * π * Real.sqrt a * θ * p.1) *
    Real.cosh (4 * π * Real.sqrt a * θ * p.2)

/-! ### Section 6: Calibration objects (`scal:C1`) -/

/-- Limiting Cardy factor `F(x) = 1 - e^{-4π x}`. -/
noncomputable def spinCalF (x : ℝ) : ℝ := 1 - Real.exp (-4 * π * x)

/-- Limiting ratio `\phi(x) = \tanh^2(x/2) / F(x)`. -/
noncomputable def spinCalPhi (x : ℝ) : ℝ := Real.tanh (x / 2) ^ 2 / spinCalF x

/-- Edge calibration slope `\alpha_1` (`spinning_calibration.tex`). -/
noncomputable def spinAlpha1 : ℝ :=
  -(2 * xiStar) / (1 + xiStar ^ 2) + 4 / Real.sinh xiStar -
    8 * π / (Real.exp (4 * π * xiStar) - 1)

/-- Calibrated transverse kernel `h_b^{\rm cal}(d)` (`scal:eC1`). -/
noncomputable def spinHbCal (b : ℂ) (d : ℝ) : ℂ :=
  spinHb b d * Complex.exp
    (-((spinAlpha1 : ℂ) * (b ^ 2 - ((xiStar ^ 2 : ℝ) : ℂ)) / (2 * (xiStar : ℂ))) -
      (b ^ 2 - ((xiStar ^ 2 : ℝ) : ℂ)) ^ 2)

/-- Calibrated scalar projection `G_{\rm cal}(b)` (`scal:eC1`). -/
noncomputable def spinGcal (a : ℝ) (Φ : ℝ × ℝ → ℝ) (b : ℂ) : ℂ :=
  ((4 * spinCalF xiStar ^ 2 : ℝ) : ℂ) *
    ∫ d : ℝ, spinHbCal b d * spinGC a Φ (b + (d : ℂ)) (b - (d : ℂ))

/-- Finite-`c` Cardy factor `F_c(x) = (1 - e^{-π n(1+γ_a)x/3})(1 - e^{-π n(1-γ_a)x/3})`
with `n = 12 a`. -/
noncomputable def spinCalFc (a x : ℝ) : ℝ :=
  (1 - Real.exp (-π * (12 * a) * (1 + spinGamma a) * x / 3)) *
    (1 - Real.exp (-π * (12 * a) * (1 - spinGamma a) * x / 3))

/-- Finite-`c` ratio `\phi_c(x) = \tanh^2(x/2) / F_c(x)`, extended by `0` at `x = 0`. -/
noncomputable def spinCalPhic (a x : ℝ) : ℝ :=
  if x = 0 then 0 else Real.tanh (x / 2) ^ 2 / spinCalFc a x

/-- First (principal) term of the symmetrised adjoint ratio `R_c(ξ, d)` on `ξ ≥ |d|`. -/
noncomputable def spinRc1 (a ξ d : ℝ) : ℝ :=
  (1 + xiStar ^ 2) / (1 + ξ ^ 2) *
    (spinCalPhic a (ξ + d) * spinCalPhic a (ξ - d) / spinCalPhi xiStar ^ 2) *
    Real.exp (-d ^ 2 / spinSigma0 ^ 2 - spinAlpha1 * (ξ ^ 2 - xiStar ^ 2) / (2 * xiStar) -
      (ξ ^ 2 - xiStar ^ 2) ^ 2)

/-- Second (`ξ ↔ d` symmetrised) term of `R_c(ξ, d)` on `ξ ≥ |d|`. -/
noncomputable def spinRc2 (a ξ d : ℝ) : ℝ :=
  Real.exp (-(12 * a) * (2 * π / 3) * (ξ - |d|)) *
    ((1 + xiStar ^ 2) / (1 + d ^ 2)) *
    (spinCalPhic a (ξ + d) * spinCalPhic a (ξ - d) / spinCalPhi xiStar ^ 2) *
    Real.exp (-ξ ^ 2 / spinSigma0 ^ 2 - spinAlpha1 * (d ^ 2 - xiStar ^ 2) / (2 * xiStar) -
      (d ^ 2 - xiStar ^ 2) ^ 2)

/-- Exact symmetrised adjoint ratio `R_c(ξ, d) = R_{1,c}(ξ, d) + R_{2,c}(ξ, d)` (`scal:C1`). -/
noncomputable def spinRc (a ξ d : ℝ) : ℝ := spinRc1 a ξ d + spinRc2 a ξ d

/-! ### Section 7: Elementary properties of `spinGamma`, `spinLambda`, `spinWc`, and coordinate changes -/

lemma spinGamma_pos {a : ℝ} (ha : 2 < a) : 0 < spinGamma a := by
  unfold spinGamma
  refine Real.sqrt_pos.mpr ?_
  have : 2 / a < 1 := (div_lt_one (by linarith)).mpr ha
  linarith

lemma spinGamma_lt_one {a : ℝ} (ha : 2 < a) : spinGamma a < 1 := by
  unfold spinGamma
  have hpos : 0 < 2 / a := div_pos two_pos (by linarith)
  exact (Real.sqrt_lt' one_pos).mpr (by linarith)

lemma spinGamma_sq {a : ℝ} (ha : 2 ≤ a) : spinGamma a ^ 2 = 1 - 2 / a := by
  unfold spinGamma
  refine Real.sq_sqrt ?_
  have : 2 / a ≤ 1 := (div_le_one (by linarith)).mpr ha
  linarith

lemma spinLambda_gt_one {a : ℝ} (ha : 2 < a) : 1 < spinLambda a := by
  unfold spinLambda
  exact one_lt_inv₀ (spinGamma_pos ha) |>.mpr (spinGamma_lt_one ha)

lemma spinWc_nonneg {a : ℝ} (ha : 2 ≤ a) (x : ℝ) : 0 ≤ spinWc a x :=
  mul_nonneg (by positivity) (spinV1_nonneg ha _)

lemma spinWc_even (a x : ℝ) : spinWc a (-x) = spinWc a x := by
  unfold spinWc
  rw [mul_neg, spinV1_even]

/-- Exact factorisation of `w_c(x)` (`spinning_calibration.tex`):
`w_c(x) = √a e^{2π a |x|} (1 - e^{-4π a (1 + γ_a) |x|}) (1 - e^{-4π a (1 - γ_a) |x|})`
(equivalently `√a e^{n k |x| / 2} F_c(|x|)` with `n = 12 a`, `k = 2π / 3`). -/
lemma spinWc_factorization {a : ℝ} (ha : 2 ≤ a) (x : ℝ) :
    spinWc a x = Real.sqrt a * Real.exp (4 * π * a * |x|) * spinCalFc a |x| := by
  have ha0 : 0 < a := by linarith
  have hsq_a : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha0.le
  have hsq_a2 : Real.sqrt (a - 2) = Real.sqrt a * spinGamma a := by
    unfold spinGamma
    rw [← Real.sqrt_mul ha0.le]
    congr 1
    field_simp [ha0.ne']
  have habs : spinWc a x = spinWc a |x| := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx, spinWc_even]
  rw [habs]
  unfold spinWc spinV1 spinCalFc
  have h1 : 2 * π * Real.sqrt a * (2 * Real.sqrt a * |x|) = 4 * π * a * |x| := by
    calc 2 * π * Real.sqrt a * (2 * Real.sqrt a * |x|)
        = 4 * π * (Real.sqrt a * Real.sqrt a) * |x| := by ring
      _ = 4 * π * a * |x| := by rw [hsq_a]
  have h2 : 2 * π * Real.sqrt (a - 2) * (2 * Real.sqrt a * |x|) =
      4 * π * a * spinGamma a * |x| := by
    rw [hsq_a2]
    calc 2 * π * (Real.sqrt a * spinGamma a) * (2 * Real.sqrt a * |x|)
        = 4 * π * (Real.sqrt a * Real.sqrt a) * spinGamma a * |x| := by ring
      _ = 4 * π * a * spinGamma a * |x| := by rw [hsq_a]
  rw [h1, h2, Real.cosh_eq, Real.cosh_eq]
  set u := 4 * π * a * |x|
  set g := spinGamma a
  have hexp1 : -π * (12 * a) * (1 + g) * |x| / 3 = -(u + g * u) := by
    dsimp [u]; ring
  have hexp2 : -π * (12 * a) * (1 - g) * |x| / 3 = -(u - g * u) := by
    dsimp [u]; ring
  rw [hexp1, hexp2]
  have he1 : Real.exp u * Real.exp (-(u + g * u)) = Real.exp (-(g * u)) := by
    rw [← Real.exp_add]; congr 1; ring
  have he2 : Real.exp u * Real.exp (-(u - g * u)) = Real.exp (g * u) := by
    rw [← Real.exp_add]; congr 1; ring
  have he3 : Real.exp u * Real.exp (-(u + g * u)) * Real.exp (-(u - g * u)) = Real.exp (-u) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hgu : 4 * π * a * g * |x| = g * u := by dsimp [u]; ring
  rw [hgu]
  calc 2 * Real.sqrt a * ((Real.exp u + Real.exp (-u)) / 2 - (Real.exp (g * u) + Real.exp (-(g * u))) / 2)
      = Real.sqrt a * (Real.exp u + Real.exp (-u) - Real.exp (g * u) - Real.exp (-(g * u))) := by ring
    _ = Real.sqrt a * (Real.exp u * ((1 - Real.exp (-(u + g * u))) * (1 - Real.exp (-(u - g * u))))) := by
        congr 1
        linear_combination -he3 + he2 + he1
    _ = Real.sqrt a * Real.exp u * ((1 - Real.exp (-(u + g * u))) * (1 - Real.exp (-(u - g * u)))) := by
        ring

lemma spinCalFc_le_one {a x : ℝ} (ha : 2 ≤ a) (hx : 0 ≤ x) : spinCalFc a x ≤ 1 := by
  unfold spinCalFc
  have hg0 : 0 ≤ spinGamma a := Real.sqrt_nonneg _
  have hg1 : spinGamma a ≤ 1 := by
    unfold spinGamma
    have h2a : 0 ≤ 2 / a := div_nonneg two_pos.le (by linarith)
    exact Real.sqrt_le_one.mpr (by linarith)
  have h1p : 0 ≤ π * (12 * a) * (1 + spinGamma a) * x / 3 := by positivity
  have h2p : 0 ≤ π * (12 * a) * (1 - spinGamma a) * x / 3 := by
    have : 0 ≤ 1 - spinGamma a := by linarith
    positivity
  have h1 : 0 ≤ 1 - Real.exp (-π * (12 * a) * (1 + spinGamma a) * x / 3) := by
    rw [sub_nonneg]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have h2 : 1 - Real.exp (-π * (12 * a) * (1 + spinGamma a) * x / 3) ≤ 1 := by
    linarith [Real.exp_pos (-π * (12 * a) * (1 + spinGamma a) * x / 3)]
  have h3 : 0 ≤ 1 - Real.exp (-π * (12 * a) * (1 - spinGamma a) * x / 3) := by
    rw [sub_nonneg]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have h4 : 1 - Real.exp (-π * (12 * a) * (1 - spinGamma a) * x / 3) ≤ 1 := by
    linarith [Real.exp_pos (-π * (12 * a) * (1 - spinGamma a) * x / 3)]
  nlinarith

/-- Pointwise upper bound `w_c(x) ≤ √a e^{4π a |x|}` (`a ≥ 2`). -/
lemma spinWc_le_exp {a : ℝ} (ha : 2 ≤ a) (x : ℝ) :
    spinWc a x ≤ Real.sqrt a * Real.exp (4 * π * a * |x|) := by
  rw [spinWc_factorization ha]
  have h := spinCalFc_le_one ha (abs_nonneg x)
  have hnn : 0 ≤ Real.sqrt a * Real.exp (4 * π * a * |x|) := by positivity
  nlinarith

/-- Quadrant weight bound: for `x_L, x_R ≥ 0` and `a ≥ 2`,
`w_c(x_L) w_c(x_R) ≤ a e^{12 a L((x_L + x_R)/2)}`. -/
lemma spinWc_mul_le_exp {a xL xR : ℝ} (ha : 2 ≤ a) (hxL : 0 ≤ xL) (hxR : 0 ≤ xR) :
    spinWc a xL * spinWc a xR ≤ a * Real.exp (12 * a * spinL ((xL + xR) / 2)) := by
  have hL := spinWc_le_exp ha xL
  have hR := spinWc_le_exp ha xR
  have hmul : spinWc a xL * spinWc a xR ≤
      (Real.sqrt a * Real.exp (4 * π * a * |xL|)) *
        (Real.sqrt a * Real.exp (4 * π * a * |xR|)) :=
    mul_le_mul hL hR (spinWc_nonneg ha xR) (by positivity)
  have hsq : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt (by linarith)
  have hexp : 12 * a * spinL ((xL + xR) / 2) = 4 * π * a * |xL| + 4 * π * a * |xR| := by
    unfold spinL
    rw [abs_of_nonneg hxL, abs_of_nonneg hxR, abs_of_nonneg (by linarith)]
    ring
  calc spinWc a xL * spinWc a xR
      ≤ (Real.sqrt a * Real.exp (4 * π * a * |xL|)) *
          (Real.sqrt a * Real.exp (4 * π * a * |xR|)) := hmul
    _ = (Real.sqrt a * Real.sqrt a) * Real.exp (4 * π * a * |xL| + 4 * π * a * |xR|) := by
        rw [Real.exp_add]; ring
    _ = a * Real.exp (12 * a * spinL ((xL + xR) / 2)) := by rw [hsq, hexp]

/-- Monotonicity of `w_c(x) e^{-4π a x}` on `[0, ∞)` (equivalently `w_c(x) e^{-π n x / 3}` with
`n = 12 a`): for `0 ≤ x ≤ y`, `w_c(x) ≤ e^{-4π a (y - x)} w_c(y)`. -/
lemma spinWc_exp_mono {a x y : ℝ} (ha : 2 ≤ a) (hx : 0 ≤ x) (hxy : x ≤ y) :
    spinWc a x ≤ Real.exp (-(4 * π * a * (y - x))) * spinWc a y := by
  have hy : 0 ≤ y := hx.trans hxy
  rw [spinWc_factorization ha x, spinWc_factorization ha y, abs_of_nonneg hx, abs_of_nonneg hy]
  have hg0 : 0 ≤ spinGamma a := Real.sqrt_nonneg _
  have hg1 : spinGamma a ≤ 1 := by
    unfold spinGamma
    have h2a : 0 ≤ 2 / a := div_nonneg two_pos.le (by linarith)
    exact Real.sqrt_le_one.mpr (by linarith)
  have hFc : spinCalFc a x ≤ spinCalFc a y := by
    unfold spinCalFc
    have hc1 : 0 ≤ π * (12 * a) * (1 + spinGamma a) / 3 := by positivity
    have hc2 : 0 ≤ π * (12 * a) * (1 - spinGamma a) / 3 := by
      have : 0 ≤ 1 - spinGamma a := by linarith
      positivity
    have h1a : 0 ≤ 1 - Real.exp (-π * (12 * a) * (1 + spinGamma a) * x / 3) := by
      rw [sub_nonneg]
      have : -π * (12 * a) * (1 + spinGamma a) * x / 3 =
          -(π * (12 * a) * (1 + spinGamma a) / 3 * x) := by ring
      rw [this]
      exact Real.exp_le_one_iff.mpr (by nlinarith)
    have h2a : 0 ≤ 1 - Real.exp (-π * (12 * a) * (1 - spinGamma a) * x / 3) := by
      rw [sub_nonneg]
      have : -π * (12 * a) * (1 - spinGamma a) * x / 3 =
          -(π * (12 * a) * (1 - spinGamma a) / 3 * x) := by ring
      rw [this]
      exact Real.exp_le_one_iff.mpr (by nlinarith)
    have h1 : 1 - Real.exp (-π * (12 * a) * (1 + spinGamma a) * x / 3) ≤
        1 - Real.exp (-π * (12 * a) * (1 + spinGamma a) * y / 3) := by
      have he : -π * (12 * a) * (1 + spinGamma a) * y / 3 ≤
          -π * (12 * a) * (1 + spinGamma a) * x / 3 := by
        have hmul : π * (12 * a) * (1 + spinGamma a) / 3 * x ≤
            π * (12 * a) * (1 + spinGamma a) / 3 * y := mul_le_mul_of_nonneg_left hxy hc1
        linarith
      linarith [Real.exp_le_exp.mpr he]
    have h2 : 1 - Real.exp (-π * (12 * a) * (1 - spinGamma a) * x / 3) ≤
        1 - Real.exp (-π * (12 * a) * (1 - spinGamma a) * y / 3) := by
      have he : -π * (12 * a) * (1 - spinGamma a) * y / 3 ≤
          -π * (12 * a) * (1 - spinGamma a) * x / 3 := by
        have hmul : π * (12 * a) * (1 - spinGamma a) / 3 * x ≤
            π * (12 * a) * (1 - spinGamma a) / 3 * y := mul_le_mul_of_nonneg_left hxy hc2
        linarith
      linarith [Real.exp_le_exp.mpr he]
    exact mul_le_mul h1 h2 h2a (h1a.trans h1)
  have hexp : Real.exp (-(4 * π * a * (y - x))) * Real.exp (4 * π * a * y) =
      Real.exp (4 * π * a * x) := by
    rw [← Real.exp_add]; congr 1; ring
  calc Real.sqrt a * Real.exp (4 * π * a * x) * spinCalFc a x
      ≤ Real.sqrt a * Real.exp (4 * π * a * x) * spinCalFc a y :=
        mul_le_mul_of_nonneg_left hFc (by positivity)
    _ = Real.exp (-(4 * π * a * (y - x))) * (Real.sqrt a * Real.exp (4 * π * a * y) * spinCalFc a y) := by
        rw [← hexp]; ring

/-- Scaling change of variables on `ℝ × ℝ` for `c₁, c₂ > 0`. -/
lemma integral_prod_scale {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (f : ℝ × ℝ → ℝ) :
    ∫ p : ℝ × ℝ, f p = (c₁ * c₂) * ∫ p : ℝ × ℝ, f (c₁ * p.1, c₂ * p.2) := by
  let e : ℝ × ℝ ≃ᵐ ℝ × ℝ :=
    (MeasurableEquiv.mulLeft₀ c₁ hc₁.ne').prodCongr (MeasurableEquiv.mulLeft₀ c₂ hc₂.ne')
  have hmp : Measure.map e (volume : Measure (ℝ × ℝ)) =
      ENNReal.ofReal (c₁⁻¹ * c₂⁻¹) • (volume : Measure (ℝ × ℝ)) := by
    have he : (e : ℝ × ℝ → ℝ × ℝ) = Prod.map (c₁ * ·) (c₂ * ·) := rfl
    rw [he, Measure.volume_eq_prod,
      ← Measure.map_prod_map _ _ (measurable_const_mul c₁) (measurable_const_mul c₂),
      Real.map_volume_mul_left hc₁.ne', Real.map_volume_mul_left hc₂.ne',
      Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
      abs_of_pos (inv_pos.mpr hc₁), abs_of_pos (inv_pos.mpr hc₂),
      ENNReal.ofReal_mul (inv_pos.mpr hc₁).le]
  have heq : ∫ p : ℝ × ℝ, f (c₁ * p.1, c₂ * p.2) =
      ∫ p : ℝ × ℝ, f p ∂(Measure.map e volume) :=
    (integral_map_equiv e f).symm
  rw [heq, hmp, integral_smul_measure, ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
  field_simp [hc₁.ne', hc₂.ne']

/-- Change of variables `r = 2√a x` on `ℝ × ℝ`: `M_2[Φ] = ∬ |\mathcal G| w_c ⊗ w_c`. -/
lemma spinM2_eq_spinWc {a : ℝ} (ha : 0 < a) (Φ : ℝ × ℝ → ℝ) :
    spinM2 a Φ = ∫ p : ℝ × ℝ, |spinG a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2 := by
  unfold spinM2 spinG spinWc
  let c : ℝ := 2 * Real.sqrt a
  have hc : 0 < c := by positivity
  rw [integral_prod_scale hc hc (fun p => |Φ p| * spinV1 a p.1 * spinV1 a p.2), ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  dsimp [c]; ring

/-- Change of variables `r = 2√a x` on `ℝ × ℝ`: `Φ_vac = -∬ \mathcal G w_c ⊗ w_c`. -/
lemma spinPhiVac_eq_spinWc {a : ℝ} (ha : 0 < a) (Φ : ℝ × ℝ → ℝ) :
    spinPhiVac a Φ = -(∫ p : ℝ × ℝ, spinG a Φ p.1 p.2 * spinWc a p.1 * spinWc a p.2) := by
  unfold spinPhiVac spinG spinWc
  congr 1
  let c : ℝ := 2 * Real.sqrt a
  have hc : 0 < c := by positivity
  rw [integral_prod_scale hc hc (fun p => Φ p * spinV1 a p.1 * spinV1 a p.2), ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  dsimp [c]; ring

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Spin.spin_half_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spin_half_mass

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinDeltaInt_le_spinDeltaL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinDeltaInt_le_spinDeltaL

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinDeltaL_le_spinDeltaSpin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinDeltaL_le_spinDeltaSpin

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinWc_factorization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinWc_factorization

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinWc_exp_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinWc_exp_mono

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinM2_eq_spinWc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinM2_eq_spinWc

end FormalResearch.ModularBootstrap.Spin
