module

public import FormalResearch.ModularBootstrap.Crossing.SumRule
public import FormalResearch.ModularBootstrap.FixedWeight.DualMajorant

/-!
# Atomic shift sources (the setting of `pmix:rebase`, `pmix:weight`, `pmix:crossing`)

Setting of `positive_mixtures.tex`, Section `pmix:s-weight` (PM-0), and of the common source class
`(H_{w,λ})` of `dual_spectrum.tex` (`ds:source-floor`), for a finite signed measure of shifts.

* `ShiftSource`: weight `w ≥ 1` and the finite signed measure `λ = ∑_j coef_j δ_{shift_j}`, `shift_j ≥ 0`.
  Its Cardy weight is `V_a(t) = ∑_j coef_j K^{(w)}_{a - shift_j}(t)` (`ShiftSource.cardyV`), the amplitude is
  `A(b) = ∑_j coef_j e^{-4π shift_j b}`, the source is `v_a(β) = ∑_j coef_j e^{2π (a - shift_j) β}`.
* The fixed-weight setting `FixedWeightProblem` is the special case with atoms = subsets of the null shifts
  and coefficients `(-1)^{|s|}` (`ShiftSource.ofProblem`, with `cardyV = cardyV` by `rfl`); the test class
  `TestClass`, `g_vac`, feasibility and the thresholds `T_V`, `T_weak`, `T_P` are re-defined for a source and
  agree with the old ones on `ofProblem` (`rfl`).
* `MixtureData` is the paper's `(H_{w,mix})`: components `(d_i, r_i, Q_i)`; `toSource` flattens it, and the
  flattened Cardy weight is `V_mix = ∑_i d_i V_{Q_i}(a - r_i, ·)` (`MixtureData.toSource_cardyV`).
* `MixtureData.rebase` is `pmix:rebase` (a): the rebased data have the same Cardy weight at `a - r_min`, hence
  the same test class, `g_vac`, feasibility and thresholds (`rebase_cardyV`, `rebase_testClass_iff`,
  `rebase_T_V`, ...), and the same source function (`rebase_srcFun`).

The atomic case is the paper's full mixture case; a general Borel `λ` (continuum of shifts) is not covered.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real FourierTransform

namespace FormalResearch.ModularBootstrap.Mixtures

open FormalResearch.ModularBootstrap.Crossing

/-! ### Section 1: the source -/

/-- A finite signed measure of shifts at integer weight `w ≥ 1`: `λ = ∑_j coef_j δ_{shift_j}`. -/
structure ShiftSource where
  w : ℕ
  hw : 1 ≤ w
  ι : Type
  [fintype : Fintype ι]
  coef : ι → ℝ
  shift : ι → ℝ
  hshift : ∀ j, 0 ≤ shift j

attribute [instance] ShiftSource.fintype

namespace ShiftSource

variable (src : ShiftSource)

/-- Cardy weight `V(t) = ∑_j coef_j K^{(w)}_{a - shift_j}(t)`. -/
noncomputable def cardyV (a t : ℝ) : ℝ :=
  ∑ j, src.coef j * kernelK src.w (a - src.shift j) t

/-- Cardy density `ρ(t) = 2π V(t)`. -/
noncomputable def cardyDensity (a t : ℝ) : ℝ := 2 * π * src.cardyV a t

/-- `V(t) / t^{w-1}`, extended smoothly to `t ∈ ℝ`. -/
noncomputable def cardyVReduced (a t : ℝ) : ℝ :=
  ∑ j, src.coef j * kernelKReduced src.w (a - src.shift j) t

/-- Cartesian Cardy density of the source (normalisation of `FixedWeightProblem.rhoDensity`). -/
noncomputable def rhoDensity (a t : ℝ) : ℝ :=
  ((src.w - 1).factorial : ℝ) / (2 * π) ^ src.w * (2 * π * src.cardyVReduced a t)

/-- Total variation `‖λ‖_TV = ∑_j |coef_j|`. -/
noncomputable def tv : ℝ := ∑ j, |src.coef j|

/-- All shifts are at most the charge `a` (`a ≥ S_λ`). -/
def ShiftLE (a : ℝ) : Prop := ∀ j, src.shift j ≤ a

/-- The source function `v_a(β) = ∑_j coef_j e^{2π (a - shift_j) β}` (`v_n` of `pmix:vn`). -/
noncomputable def srcFun (a β : ℝ) : ℝ :=
  ∑ j, src.coef j * Real.exp (2 * π * (a - src.shift j) * β)

/-- The amplitude `A(x) = ∑_j coef_j e^{-4π shift_j x}` on the real line. -/
noncomputable def ampl (x : ℝ) : ℝ :=
  ∑ j, src.coef j * Real.exp (-4 * π * src.shift j * x)

/-- The amplitude `A(b)` on `ℂ` (an entire function). -/
noncomputable def amplC (b : ℂ) : ℂ :=
  ∑ j, (src.coef j : ℂ) * Complex.exp (-4 * (π : ℂ) * (src.shift j : ℂ) * b)

lemma cardyV_eq_pow_mul_reduced (a t : ℝ) :
    src.cardyV a t = t ^ (src.w - 1) * src.cardyVReduced a t := by
  unfold cardyV cardyVReduced
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [kernelK_eq_pow_mul_reduced]
  ring

lemma continuous_cardyV (a : ℝ) : Continuous (src.cardyV a) := by
  unfold cardyV
  exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_kernelK src.w _)

lemma continuous_cardyVReduced (a : ℝ) : Continuous (src.cardyVReduced a) := by
  unfold cardyVReduced
  exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_kernelKReduced src.w _)

lemma continuous_rhoDensity (a : ℝ) : Continuous (src.rhoDensity a) := by
  unfold rhoDensity
  exact continuous_const.mul (continuous_const.mul (src.continuous_cardyVReduced a))

lemma tv_nonneg : 0 ≤ src.tv := Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma amplC_entire : Differentiable ℂ src.amplC := by
  unfold amplC
  refine Differentiable.fun_sum fun j _ => ?_
  fun_prop

lemma amplC_ofReal (x : ℝ) : src.amplC (x : ℂ) = (src.ampl x : ℂ) := by
  unfold amplC ampl
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 2

lemma abs_ampl_le {x : ℝ} (hx : 0 ≤ x) : |src.ampl x| ≤ src.tv := by
  unfold ampl tv
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have hexp : Real.exp (-4 * π * src.shift j * x) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have := src.hshift j
    nlinarith [Real.pi_pos, mul_nonneg this hx]
  calc |src.coef j| * Real.exp (-4 * π * src.shift j * x) ≤ |src.coef j| * 1 :=
        mul_le_mul_of_nonneg_left hexp (abs_nonneg _)
    _ = |src.coef j| := mul_one _

/-- **Upper bound by the Bessel kernel**: `|V_a(t)| ≤ ‖λ‖_TV K_a(t)` when `a ≥ S_λ`, `t ≥ 0`. -/
lemma abs_cardyV_le {a : ℝ} (ha : src.ShiftLE a) {t : ℝ} (ht : 0 ≤ t) :
    |src.cardyV a t| ≤ src.tv * kernelK src.w a t := by
  unfold cardyV tv
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  have h0 : 0 ≤ a - src.shift j := sub_nonneg.mpr (ha j)
  have hmono : kernelK src.w (a - src.shift j) t ≤ kernelK src.w a t :=
    kernelK_mono_alpha h0 (by linarith [src.hshift j]) ht
  rw [abs_mul, abs_of_nonneg (kernelK_nonneg h0 ht)]
  exact mul_le_mul_of_nonneg_left hmono (abs_nonneg _)

lemma cardyV_le {a : ℝ} (ha : src.ShiftLE a) {t : ℝ} (ht : 0 ≤ t) :
    src.cardyV a t ≤ src.tv * kernelK src.w a t :=
  (le_abs_self _).trans (src.abs_cardyV_le ha ht)

/-- **Laplace identity** (`pmix:weight` (a)): `2π ∫₀^∞ V e^{-2πβt} dt = β^{-w} v_a(1/β)`. -/
theorem cardyV_laplace (a : ℝ) {β : ℝ} (hβ : 0 < β) :
    IntegrableOn (fun t => src.cardyV a t * Real.exp (-2 * π * β * t)) (Ioi 0) ∧
      2 * π * ∫ t in Ioi 0, src.cardyV a t * Real.exp (-2 * π * β * t) =
        β ^ (-(src.w : ℝ)) * src.srcFun a β⁻¹ := by
  have hk := fun j => kernelK_laplace src.hw (a - src.shift j) hβ
  have hsum : (fun t => src.cardyV a t * Real.exp (-2 * π * β * t)) =
      fun t => ∑ j, src.coef j * (kernelK src.w (a - src.shift j) t *
        Real.exp (-2 * π * β * t)) := by
    ext t
    unfold cardyV
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hint : IntegrableOn (fun t => src.cardyV a t * Real.exp (-2 * π * β * t)) (Ioi 0) := by
    rw [hsum]
    exact integrable_finsetSum _ fun j _ => (hk j).1.const_mul _
  refine ⟨hint, ?_⟩
  rw [hsum, integral_finsetSum _ fun j _ => (hk j).1.const_mul _, Finset.mul_sum]
  unfold srcFun
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, ← mul_assoc, mul_comm (2 * π), mul_assoc, (hk j).2]
  have : 2 * π * (a - src.shift j) / β = 2 * π * (a - src.shift j) * β⁻¹ := by
    rw [div_eq_mul_inv]
  rw [this]
  ring

end ShiftSource

/-! ### Section 2: test class, vacuum pairing, feasibility and thresholds -/

/-- The Hankel-odd test class `\overline{\mathcal A}_{w, src}` at vacuum shift `a`. -/
structure TestClass (src : ShiftSource) (a : ℝ) (g : ℝ → ℝ) : Prop where
  cont : ContinuousOn g (Ici 0)
  int_lift : Integrable (radialLift src.w g)
  fourier_odd : 𝓕 (radialLift src.w g) = -(radialLift src.w g)
  int_cardy : IntegrableOn (fun t => |g t| * src.cardyV a t) (Ioi 0)

namespace ShiftSource

variable (src : ShiftSource)

/-- Cardy norm `M[g] = ∫₀^∞ |g| V dt`. -/
noncomputable def cardyNorm (a : ℝ) (g : ℝ → ℝ) : ℝ :=
  ∫ t in Ioi 0, |g t| * src.cardyV a t

/-- Vacuum pairing `g_vac = -2π ∫₀^∞ g V dt = -∫ g ρ dt`. -/
noncomputable def gVac (a : ℝ) (g : ℝ → ℝ) : ℝ :=
  -2 * π * ∫ t in Ioi 0, g t * src.cardyV a t

/-- Strict feasibility: `g_vac > 0` and `g ≥ 0` on `[T, ∞)`. -/
def IsFeasible (a T : ℝ) (g : ℝ → ℝ) : Prop :=
  TestClass src a g ∧ 0 < src.gVac a g ∧ ∀ t ≥ T, 0 ≤ g t

/-- Weak feasibility: `g ≢ 0`, `g_vac ≥ 0` and `g ≥ 0` on `[T, ∞)`. -/
def IsWeaklyFeasible (a T : ℝ) (g : ℝ → ℝ) : Prop :=
  TestClass src a g ∧ (∃ t ≥ 0, g t ≠ 0) ∧ 0 ≤ src.gVac a g ∧ ∀ t ≥ T, 0 ≤ g t

/-- Strict threshold `T(c̃) = inf {T > 0 : ∃ g ∈ \overline{\mathcal A}, g_vac > 0, g|_{[T,∞)} ≥ 0}`
(`T_mix` of `positive_mixtures.tex`, `T_V` of `dual_spectrum.tex`). -/
noncomputable def T_V (cTilde : ℝ) : ℝ :=
  sInf {T : ℝ | 0 < T ∧ ∃ g, src.IsFeasible (cTilde / 12) T g}

/-- Weak threshold `T_weak(c̃)` (`T_{weak,mix}`). -/
noncomputable def T_weak (cTilde : ℝ) : ℝ :=
  sInf {T : ℝ | 0 < T ∧ ∃ g, src.IsWeaklyFeasible (cTilde / 12) T g}

/-- Finite-order odd-Laguerre threshold `T_{mix,P}(c̃)`: strict threshold over
`span {ψ_{2j-1}}_{j=1}^P`, `ψ_k = L_k^{(w-1)}(4π t) e^{-2π t}`. -/
noncomputable def T_P (P : ℕ) (cTilde : ℝ) : ℝ :=
  sInf {T : ℝ | 0 < T ∧ ∃ g, src.IsFeasible (cTilde / 12) T g ∧
    ∃ c : Fin P → ℝ, ∀ t, g t = ∑ j : Fin P, c j * FixedWeight.genLaguerrePsi src.w (2 * (j : ℕ) + 1) t}

/-- Optimal primary dimension gap `Δ(c̃) = c̃/12 + T_V(c̃)`. -/
noncomputable def Delta_best (cTilde : ℝ) : ℝ := cTilde / 12 + src.T_V cTilde

end ShiftSource

/-! ### Section 3: the bridge with the fixed-weight setting -/

/-- A fixed-weight problem as a shift source: atoms are the subsets `s` of the null shifts, with
coefficient `(-1)^{|s|}` and shift `∑_{l ∈ s} μ_l`. -/
noncomputable def ShiftSource.ofProblem (prob : FixedWeightProblem) : ShiftSource where
  w := prob.w
  hw := prob.hw
  ι := Finset (Fin prob.m)
  coef s := (-1 : ℝ) ^ s.card
  shift s := prob.shiftSum s
  hshift s := prob.shiftSum_nonneg s

section Bridge

variable (prob : FixedWeightProblem)

@[simp] lemma ofProblem_w : (ShiftSource.ofProblem prob).w = prob.w := rfl

@[simp] lemma ofProblem_cardyV (a t : ℝ) :
    (ShiftSource.ofProblem prob).cardyV a t = prob.cardyV a t := rfl

@[simp] lemma ofProblem_cardyDensity (a t : ℝ) :
    (ShiftSource.ofProblem prob).cardyDensity a t = prob.cardyDensity a t := rfl

@[simp] lemma ofProblem_cardyVReduced (a t : ℝ) :
    (ShiftSource.ofProblem prob).cardyVReduced a t = prob.cardyVReduced a t := rfl

@[simp] lemma ofProblem_rhoDensity (a t : ℝ) :
    (ShiftSource.ofProblem prob).rhoDensity a t = prob.rhoDensity a t := rfl

lemma ofProblem_testClass_iff {a : ℝ} {g : ℝ → ℝ} :
    TestClass (ShiftSource.ofProblem prob) a g ↔ Crossing.TestClass prob a g :=
  ⟨fun h => ⟨h.cont, h.int_lift, h.fourier_odd, h.int_cardy⟩,
    fun h => ⟨h.cont, h.int_lift, h.fourier_odd, h.int_cardy⟩⟩

@[simp] lemma ofProblem_cardyNorm (a : ℝ) (g : ℝ → ℝ) :
    (ShiftSource.ofProblem prob).cardyNorm a g = prob.cardyNorm a g := rfl

@[simp] lemma ofProblem_gVac (a : ℝ) (g : ℝ → ℝ) :
    (ShiftSource.ofProblem prob).gVac a g = prob.gVac a g := rfl

lemma ofProblem_isFeasible_iff {a T : ℝ} {g : ℝ → ℝ} :
    (ShiftSource.ofProblem prob).IsFeasible a T g ↔ prob.IsFeasible a T g := by
  unfold ShiftSource.IsFeasible FixedWeightProblem.IsFeasible
  rw [ofProblem_testClass_iff]
  rfl

lemma ofProblem_isWeaklyFeasible_iff {a T : ℝ} {g : ℝ → ℝ} :
    (ShiftSource.ofProblem prob).IsWeaklyFeasible a T g ↔ prob.IsWeaklyFeasible a T g := by
  unfold ShiftSource.IsWeaklyFeasible FixedWeightProblem.IsWeaklyFeasible
  rw [ofProblem_testClass_iff]
  rfl

lemma ofProblem_T_V (cTilde : ℝ) :
    (ShiftSource.ofProblem prob).T_V cTilde = prob.T_V cTilde := by
  unfold ShiftSource.T_V FixedWeightProblem.T_V
  simp only [ofProblem_isFeasible_iff]

lemma ofProblem_T_weak (cTilde : ℝ) :
    (ShiftSource.ofProblem prob).T_weak cTilde = prob.T_weak cTilde := by
  unfold ShiftSource.T_weak FixedWeightProblem.T_weak
  simp only [ofProblem_isWeaklyFeasible_iff]

lemma ofProblem_Delta_best (cTilde : ℝ) :
    (ShiftSource.ofProblem prob).Delta_best cTilde = prob.Delta_best cTilde := by
  unfold ShiftSource.Delta_best FixedWeightProblem.Delta_best
  rw [ofProblem_T_V]

lemma ofProblem_shiftLE_iff {a : ℝ} :
    (ShiftSource.ofProblem prob).ShiftLE a ↔ prob.totalShift ≤ a := by
  constructor
  · intro h
    have h1 := h Finset.univ
    have : prob.shiftSum Finset.univ = prob.totalShift := rfl
    simpa [ShiftSource.ofProblem, this] using h1
  · intro h s
    exact (prob.shiftSum_le_totalShift s).trans h

lemma ofProblem_ampl (x : ℝ) :
    (ShiftSource.ofProblem prob).ampl x = prob.nullPoly (Real.exp (-4 * π * x)) := by
  unfold ShiftSource.ampl
  rw [prob.nullPoly_eq_sum (Real.exp_pos _).le]
  refine Finset.sum_congr rfl fun s _ => ?_
  show (-1 : ℝ) ^ s.card * Real.exp (-4 * π * prob.shiftSum s * x) = _
  congr 1
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  congr 1; ring

end Bridge

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.ShiftSource.cardyV_laplace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ShiftSource.cardyV_laplace

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.ofProblem_T_V' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ofProblem_T_V

end FormalResearch.ModularBootstrap.Mixtures
