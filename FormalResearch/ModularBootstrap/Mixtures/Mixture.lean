module

public import FormalResearch.ModularBootstrap.Mixtures.Source

/-!
# Mixtures `(H_{w,mix})` and rebasing (`pmix:rebase` (a))

Setting `(H_{w,mix})` of `positive_mixtures.tex`: integer weight `w ≥ 1`, `s ≥ 1` components with positive
coefficients `d_i`, shifts `r_i ≥ 0` and fixed products `Q_i(q) = ∏_ℓ (1 - q^{μ_{i,ℓ}})` (data `(m_i, μ_i)`; `MixtureData.Q i` is the
`FixedWeightProblem` of weight `w` they define).  `MixtureData.toSource` flattens the mixture into the atomic source with atoms
`(i, S)`, `S ⊆ {1..m_i}`, coefficient `d_i (-1)^{|S|}` and shift `r_i + ∑_{ℓ ∈ S} μ_{i,ℓ}`.

* `toSource_cardyV`: `V_mix(t) = ∑_i d_i V_{Q_i}(a - r_i, t)` (the paper's `V_mix = ∑_i d_i V_i`, `V_i` the
  single-component Cardy weight at parameter `n_i = n - 12 r_i`).
* `toSource_ampl`: `A(x) = ∑_i d_i e^{-4π r_i x} Q_i(e^{-4π x})` (`pmix:Amix`).
* `toSource_srcFun`: `v_n(β) = ∑_i d_i e^{2π(a - r_i)β} Q_i(e^{-2πβ})` (`pmix:vn`).
* `pmix:rebase` (a), `Lemma PM.1`: `rebase` has `r'_i = r_i - r_min`; at `a' = a - r_min` it has the same
  Cardy weight (`rebase_cardyV`), source function (`rebase_srcFun`), test class, norm and vacuum pairing
  (`rebase_testClass_iff`, `rebase_cardyNorm`, `rebase_gVac`), feasibility and thresholds `T_V, T_weak, T_P`
  (`rebase_isFeasible_iff`, `rebase_T_V`, ...; `c̃' = c̃ - 12 r_min`), and `min r' = 0` (`rebase_exists_zero`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Mixtures

open FormalResearch.ModularBootstrap.Crossing

/-- Setting `(H_{w,mix})`: positive coefficients `d_i`, shifts `r_i ≥ 0` and fixed products `Q_i`, given by their
number of factors `m_i` and exponents `μ_{i,ℓ} > 0`. -/
structure MixtureData where
  w : ℕ
  hw : 1 ≤ w
  s : ℕ
  hs : 1 ≤ s
  d : Fin s → ℝ
  hd : ∀ i, 0 < d i
  r : Fin s → ℝ
  hr : ∀ i, 0 ≤ r i
  m : Fin s → ℕ
  μ : ∀ i, Fin (m i) → ℝ
  hμ : ∀ i l, 0 < μ i l

namespace MixtureData

variable (M : MixtureData)

/-- The `i`-th component product `Q_i(q) = ∏_{ℓ} (1 - q^{μ_{i,ℓ}})` as a fixed-weight problem of weight `w`. -/
def Q (i : Fin M.s) : FixedWeightProblem where
  w := M.w
  hw := M.hw
  m := M.m i
  μ := M.μ i
  hμ := M.hμ i

@[simp] lemma Q_w (i : Fin M.s) : (M.Q i).w = M.w := rfl

/-- Flattening of a mixture into an atomic shift source (atoms `(i, S)`). -/
noncomputable def toSource : ShiftSource where
  w := M.w
  hw := M.hw
  ι := Σ i : Fin M.s, Finset (Fin (M.Q i).m)
  coef x := M.d x.1 * (-1 : ℝ) ^ x.2.card
  shift x := M.r x.1 + (M.Q x.1).shiftSum x.2
  hshift _ := add_nonneg (M.hr _) ((M.Q _).shiftSum_nonneg _)

/-- Sums over the atoms split as `∑_i ∑_S`. -/
lemma sum_toSource {β : Type*} [AddCommMonoid β] (f : M.toSource.ι → β) :
    ∑ x, f x = ∑ i, ∑ S : Finset (Fin (M.Q i).m), f ⟨i, S⟩ :=
  Fintype.sum_sigma _

/-- **`V_mix = ∑_i d_i V_i`** (`pmix:Vmix`): the flattened Cardy weight is the sum of the single-component
Cardy weights at the shifted charges `a - r_i`. -/
theorem toSource_cardyV (a t : ℝ) :
    M.toSource.cardyV a t = ∑ i, M.d i * (M.Q i).cardyV (a - M.r i) t := by
  unfold ShiftSource.cardyV
  rw [M.sum_toSource]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold FixedWeightProblem.cardyV
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  show M.d i * (-1 : ℝ) ^ S.card * kernelK M.w (a - (M.r i + (M.Q i).shiftSum S)) t =
    M.d i * ((-1 : ℝ) ^ S.card * kernelK M.w (a - M.r i - (M.Q i).shiftSum S) t)
  rw [sub_add_eq_sub_sub]
  ring

/-- **`A(x) = ∑_i d_i e^{-4π r_i x} Q_i(e^{-4π x})`** (`pmix:Amix`). -/
theorem toSource_ampl (x : ℝ) :
    M.toSource.ampl x =
      ∑ i, M.d i * Real.exp (-4 * π * M.r i * x) * (M.Q i).nullPoly (Real.exp (-4 * π * x)) := by
  unfold ShiftSource.ampl
  rw [M.sum_toSource]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← ofProblem_ampl (M.Q i) x, mul_assoc, ShiftSource.ampl, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  show M.d i * (-1 : ℝ) ^ S.card * Real.exp (-4 * π * (M.r i + (M.Q i).shiftSum S) * x) =
    M.d i * (Real.exp (-4 * π * M.r i * x) * ((-1 : ℝ) ^ S.card *
      Real.exp (-4 * π * (M.Q i).shiftSum S * x)))
  have : Real.exp (-4 * π * (M.r i + (M.Q i).shiftSum S) * x) =
      Real.exp (-4 * π * M.r i * x) * Real.exp (-4 * π * (M.Q i).shiftSum S * x) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [this]
  ring

/-- **`v_n(β) = ∑_i d_i e^{2π(a - r_i)β} Q_i(e^{-2πβ})`** (`pmix:vn`). -/
theorem toSource_srcFun (a β : ℝ) :
    M.toSource.srcFun a β =
      ∑ i, M.d i * Real.exp (2 * π * (a - M.r i) * β) *
        (M.Q i).nullPoly (Real.exp (-2 * π * β)) := by
  unfold ShiftSource.srcFun
  rw [M.sum_toSource]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_assoc, (M.Q i).nullPoly_eq_sum (Real.exp_pos _).le, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  show M.d i * (-1 : ℝ) ^ S.card * Real.exp (2 * π * (a - (M.r i + (M.Q i).shiftSum S)) * β) =
    M.d i * (Real.exp (2 * π * (a - M.r i) * β) * ((-1 : ℝ) ^ S.card *
      Real.exp (-2 * π * β) ^ (M.Q i).shiftSum S))
  have hrpow : Real.exp (-2 * π * β) ^ (M.Q i).shiftSum S =
      Real.exp (-2 * π * β * (M.Q i).shiftSum S) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  have : Real.exp (2 * π * (a - (M.r i + (M.Q i).shiftSum S)) * β) =
      Real.exp (2 * π * (a - M.r i) * β) * Real.exp (-2 * π * β * (M.Q i).shiftSum S) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hrpow, this]
  ring

/-! ### Rebasing to `min_i r_i = 0` (`pmix:rebase` (a)) -/

/-- `r_min = min_i r_i`. -/
noncomputable def rmin : ℝ :=
  Finset.univ.inf' ⟨⟨0, M.hs⟩, Finset.mem_univ _⟩ M.r

lemma rmin_le (i : Fin M.s) : M.rmin ≤ M.r i :=
  Finset.inf'_le _ (Finset.mem_univ i)

lemma exists_rmin : ∃ i, M.r i = M.rmin := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' (⟨⟨0, M.hs⟩, Finset.mem_univ _⟩ :
    (Finset.univ : Finset (Fin M.s)).Nonempty) M.r
  exact ⟨i, hi.symm⟩

lemma rmin_nonneg : 0 ≤ M.rmin := by
  obtain ⟨i, hi⟩ := M.exists_rmin
  rw [← hi]; exact M.hr i

/-- The rebased mixture `r'_i = r_i - r_min`. -/
noncomputable def rebase : MixtureData :=
  { M with
    r := fun i => M.r i - M.rmin
    hr := fun i => sub_nonneg.mpr (M.rmin_le i) }

@[simp] lemma rebase_w : M.rebase.w = M.w := rfl

@[simp] lemma rebase_toSource_w : M.rebase.toSource.w = M.toSource.w := rfl

/-- `min_i r'_i = 0` and `r'_i ≥ 0`. -/
lemma rebase_exists_zero : ∃ i, M.rebase.r i = 0 := by
  obtain ⟨i, hi⟩ := M.exists_rmin
  exact ⟨i, by simp [rebase, hi]⟩

/-- **`pmix:rebase` (a)**: the Cardy weight is unchanged as a function of `t`: the rebased mixture at
`a' = a - r_min` has the weight `V_mix` of the original at `a`. -/
theorem rebase_cardyV (a t : ℝ) :
    M.rebase.toSource.cardyV (a - M.rmin) t = M.toSource.cardyV a t := by
  unfold ShiftSource.cardyV
  refine Finset.sum_congr rfl fun x _ => ?_
  show M.d x.1 * (-1 : ℝ) ^ x.2.card *
      kernelK M.w (a - M.rmin - (M.r x.1 - M.rmin + (M.Q x.1).shiftSum x.2)) t =
    M.d x.1 * (-1 : ℝ) ^ x.2.card * kernelK M.w (a - (M.r x.1 + (M.Q x.1).shiftSum x.2)) t
  congr 2
  ring

/-- **`pmix:rebase` (a)**: the source `v_n` is identical, `v_n(β) = v'_{n'}(β)` (`a' = a - r_min`). -/
theorem rebase_srcFun (a β : ℝ) :
    M.rebase.toSource.srcFun (a - M.rmin) β = M.toSource.srcFun a β := by
  unfold ShiftSource.srcFun
  refine Finset.sum_congr rfl fun x _ => ?_
  show M.d x.1 * (-1 : ℝ) ^ x.2.card *
      Real.exp (2 * π * (a - M.rmin - (M.r x.1 - M.rmin + (M.Q x.1).shiftSum x.2)) * β) =
    M.d x.1 * (-1 : ℝ) ^ x.2.card *
      Real.exp (2 * π * (a - (M.r x.1 + (M.Q x.1).shiftSum x.2)) * β)
  congr 3
  ring

/-- **`pmix:rebase` (a)**: the Cardy density is unchanged. -/
theorem rebase_cardyDensity (a t : ℝ) :
    M.rebase.toSource.cardyDensity (a - M.rmin) t = M.toSource.cardyDensity a t := by
  unfold ShiftSource.cardyDensity
  rw [rebase_cardyV]

/-- **`pmix:rebase` (a)**: the test class `\overline{\mathcal A}_{w,mix}` is unchanged. -/
theorem rebase_testClass_iff {a : ℝ} {g : ℝ → ℝ} :
    TestClass M.rebase.toSource (a - M.rmin) g ↔ TestClass M.toSource a g := by
  constructor
  · intro h
    refine ⟨h.cont, h.int_lift, h.fourier_odd, ?_⟩
    simpa only [rebase_cardyV] using h.int_cardy
  · intro h
    refine ⟨h.cont, h.int_lift, h.fourier_odd, ?_⟩
    simpa only [rebase_cardyV] using h.int_cardy

/-- **`pmix:rebase` (a)**: the norm `M_mix[g]` is unchanged. -/
theorem rebase_cardyNorm (a : ℝ) (g : ℝ → ℝ) :
    M.rebase.toSource.cardyNorm (a - M.rmin) g = M.toSource.cardyNorm a g := by
  unfold ShiftSource.cardyNorm
  simp only [rebase_cardyV]

/-- **`pmix:rebase` (a)**: the vacuum pairing `g_{vac,mix}` is unchanged. -/
theorem rebase_gVac (a : ℝ) (g : ℝ → ℝ) :
    M.rebase.toSource.gVac (a - M.rmin) g = M.toSource.gVac a g := by
  unfold ShiftSource.gVac
  simp only [rebase_cardyV]

theorem rebase_isFeasible_iff {a T : ℝ} {g : ℝ → ℝ} :
    M.rebase.toSource.IsFeasible (a - M.rmin) T g ↔ M.toSource.IsFeasible a T g := by
  unfold ShiftSource.IsFeasible
  rw [rebase_testClass_iff, rebase_gVac]

theorem rebase_isWeaklyFeasible_iff {a T : ℝ} {g : ℝ → ℝ} :
    M.rebase.toSource.IsWeaklyFeasible (a - M.rmin) T g ↔ M.toSource.IsWeaklyFeasible a T g := by
  unfold ShiftSource.IsWeaklyFeasible
  rw [rebase_testClass_iff, rebase_gVac]

lemma rebase_charge (cTilde : ℝ) : (cTilde - 12 * M.rmin) / 12 = cTilde / 12 - M.rmin := by ring

/-- **`pmix:rebase` (a)**: `T_mix` is unchanged (`c̃' = c̃ - 12 r_min`, i.e. `n' = n - 12 r_min`). -/
theorem rebase_T_V (cTilde : ℝ) :
    M.rebase.toSource.T_V (cTilde - 12 * M.rmin) = M.toSource.T_V cTilde := by
  unfold ShiftSource.T_V
  simp only [rebase_charge, rebase_isFeasible_iff]

/-- **`pmix:rebase` (a)**: `T_{weak,mix}` is unchanged. -/
theorem rebase_T_weak (cTilde : ℝ) :
    M.rebase.toSource.T_weak (cTilde - 12 * M.rmin) = M.toSource.T_weak cTilde := by
  unfold ShiftSource.T_weak
  simp only [rebase_charge, rebase_isWeaklyFeasible_iff]

/-- **`pmix:rebase` (a)**: the finite-order thresholds `T_{mix,P}` are unchanged. -/
theorem rebase_T_P (P : ℕ) (cTilde : ℝ) :
    M.rebase.toSource.T_P P (cTilde - 12 * M.rmin) = M.toSource.T_P P cTilde := by
  unfold ShiftSource.T_P
  simp only [rebase_charge, rebase_isFeasible_iff]
  rfl

theorem rebase_Delta_best (cTilde : ℝ) :
    M.rebase.toSource.Delta_best (cTilde - 12 * M.rmin) =
      M.toSource.Delta_best cTilde - M.rmin := by
  unfold ShiftSource.Delta_best
  rw [rebase_T_V]
  ring

/-- **`pmix:rebase` (a)** (Lemma PM.1 (a)), packaged: rebasing `n' = n - 12 r_min`, `r'_i = r_i - r_min`
leaves the source function `v_n`, the Cardy weight (hence density, norm, `g_vac`, test class) and the thresholds
`T_mix`, `T_{weak,mix}`, `T_{mix,P}` unchanged as functions of `t` and `n`. -/
theorem pmix_rebase_a :
    (∀ a β : ℝ, M.rebase.toSource.srcFun (a - M.rmin) β = M.toSource.srcFun a β) ∧
    (∀ a t : ℝ, M.rebase.toSource.cardyV (a - M.rmin) t = M.toSource.cardyV a t) ∧
    (∀ (a : ℝ) (g : ℝ → ℝ), (TestClass M.rebase.toSource (a - M.rmin) g ↔ TestClass M.toSource a g) ∧
      M.rebase.toSource.cardyNorm (a - M.rmin) g = M.toSource.cardyNorm a g ∧
      M.rebase.toSource.gVac (a - M.rmin) g = M.toSource.gVac a g) ∧
    (∀ cTilde : ℝ, M.rebase.toSource.T_V (cTilde - 12 * M.rmin) = M.toSource.T_V cTilde ∧
      M.rebase.toSource.T_weak (cTilde - 12 * M.rmin) = M.toSource.T_weak cTilde ∧
      ∀ P : ℕ, M.rebase.toSource.T_P P (cTilde - 12 * M.rmin) = M.toSource.T_P P cTilde) :=
  ⟨M.rebase_srcFun, M.rebase_cardyV,
    fun a g => ⟨M.rebase_testClass_iff, M.rebase_cardyNorm a g, M.rebase_gVac a g⟩,
    fun cTilde => ⟨M.rebase_T_V cTilde, M.rebase_T_weak cTilde, fun P => M.rebase_T_P P cTilde⟩⟩

end MixtureData

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.MixtureData.pmix_rebase_a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MixtureData.pmix_rebase_a

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.MixtureData.toSource_cardyV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MixtureData.toSource_cardyV

end FormalResearch.ModularBootstrap.Mixtures
