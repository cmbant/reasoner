module

public import FormalResearch.ModularBootstrap.Mixtures.CommonSource
public import FormalResearch.ModularBootstrap.FixedWeight.MomentProblem
public import FormalResearch.ModularBootstrap.Duality.ConstrainedFeasible
public import FormalResearch.ModularBootstrap.Upper.Membership.RadialFourier

/-!
# Source dual setup, `DualSetupCore`, and Lemma M (`ds:M`) for `CommonSource` (PM-4)

Builds the DU-G input (`SourceDualSetupCore`, abstracting `FixedWeight.DualSetupCore`) and proves
`dual_spectrum.tex`, Lemma M (`ds:M`) and constrained finiteness (`T_F < ∞`) for any atomic source
with the comparison floor (`CommonSource` / `FloorData.At`), including rebased positive mixtures
(`MixtureData`, `positive_mixtures.tex` §`pmix:s-duality`).

* `SourceDualSetupCore src cTilde β₀ T₀`: standing fixed-charge hypotheses for an atomic source:
  `c̃ > 0`, `a = c̃/12`, `src.ShiftLE a`, `0 ≤ V` and `V ≤ ‖λ‖_TV K_a`, `β₀ ∈ (0, 1/2]`,
  `t₀^*(w, β₀) ≤ T₀ > 0`, and `g_vac(Ξ_β) < 0` on `(0, β₀]` (true on `(0, 1)` for positive
  mixtures and on small `(0, β₁]` for every `CommonSource` by `d_λ V_{Q_0} ≤ V ≤ ‖λ‖_TV K_a`).
* `SourceDualSetupCore.exists_of_floor` / `exists_of_common` / `of_mixture` / `of_fixedWeight`:
  constructs `SourceDualSetupCore` from `FloorData.At`, `CommonSource`, `MixtureData`, or
  `FixedWeight.DualSetupCore`.
* `lemma_M_src`, `commonSource_lemma_M`: full Lemma M (`ds:M`) for any `SourceDualSetupCore` /
  `CommonSource` (`h ∈ \overline{\mathcal A}`, `h_vac = -C₀ < 0`, `w_* ≤ h` on `[T₀, ∞)`,
  `e^{-2πβt} ≤ C_β w_*`, `ψ_k / w_* → 0`, `Ξ_β / w_* → 0`).
* `exists_feasible_src_of_compact`, `T_V_lt_top_src`: finiteness `T_F < ∞` and `0 ≤ T_V < ∞` for
  every compact `F ⊂ (0, ∞)` and any `FloorData.At (c̃/12)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real FourierTransform

namespace FormalResearch.ModularBootstrap.Mixtures

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Duality
open FormalResearch.ModularBootstrap.FixedWeight

/-! ### Test-class algebra and `IsFeasibleOn` for `ShiftSource` -/

/-- Feasibility of `g ∈ \overline{\mathcal A}` on an arbitrary set `X`: `g_vac > 0` and `g ≥ 0` on `X`. -/
def ShiftSource.IsFeasibleOn (src : ShiftSource) (a : ℝ) (X : Set ℝ) (g : ℝ → ℝ) : Prop :=
  TestClass src a g ∧ 0 < src.gVac a g ∧ ∀ t ∈ X, 0 ≤ g t

lemma isFeasibleOn_Ici_iff_src (src : ShiftSource) (a T : ℝ) (g : ℝ → ℝ) :
    src.IsFeasibleOn a (Ici T) g ↔ src.IsFeasible a T g := by
  unfold ShiftSource.IsFeasibleOn ShiftSource.IsFeasible
  simp only [mem_Ici, ge_iff_le]

lemma testClass_zero_src (src : ShiftSource) (a : ℝ) : TestClass src a (fun _ => 0) where
  cont := continuousOn_const
  int_lift := by
    have hz : radialLift src.w (fun _ : ℝ => (0 : ℝ)) = 0 := by ext x; simp [radialLift]
    rw [hz]
    exact integrable_zero _ _ _
  fourier_odd := by
    have hz : radialLift src.w (fun _ : ℝ => (0 : ℝ)) = 0 := by ext x; simp [radialLift]
    rw [hz]; ext x; rw [Real.fourier_eq]; simp
  int_cardy := by
    have hz : (fun t => |(0 : ℝ)| * src.cardyV a t) = 0 := by ext t; simp
    rw [hz]; exact integrableOn_zero

lemma testClass_add_src {src : ShiftSource} {a : ℝ} {g₁ g₂ : ℝ → ℝ}
    (h₁ : TestClass src a g₁) (h₂ : TestClass src a g₂) :
    TestClass src a (fun t => g₁ t + g₂ t) where
  cont := h₁.cont.add h₂.cont
  int_lift := by
    have heq : radialLift src.w (fun t => g₁ t + g₂ t) =
        fun x => radialLift src.w g₁ x + radialLift src.w g₂ x := by
      ext x; simp [radialLift]
    rw [heq]
    exact h₁.int_lift.add h₂.int_lift
  fourier_odd := by
    have heq : radialLift src.w (fun t => g₁ t + g₂ t) =
        fun x => radialLift src.w g₁ x - ((-1 : ℂ) • radialLift src.w g₂) x := by
      ext x; simp [radialLift]
    rw [heq]
    have hsub := FormalResearch.ModularBootstrap.Upper.Membership.fourier_sub_fn h₁.int_lift
      (h₂.int_lift.smul (-1 : ℂ))
    rw [hsub, show (-1 : ℂ) • radialLift src.w g₂ = fun x => (-1 : ℂ) • radialLift src.w g₂ x from rfl,
      FormalResearch.ModularBootstrap.Upper.Membership.fourier_smul_fn',
      h₁.fourier_odd, h₂.fourier_odd]
    ext x; simp; ring
  int_cardy := by
    have hV_m : AEStronglyMeasurable (fun t => |g₁ t + g₂ t| * src.cardyV a t)
        (volume.restrict (Ioi 0)) :=
      (((h₁.cont.add h₂.cont).abs.mono Ioi_subset_Ici_self).mul
        (src.continuous_cardyV a).continuousOn).aestronglyMeasurable measurableSet_Ioi
    refine (h₁.int_cardy.norm.add h₂.int_cardy.norm).mono' hV_m ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _
    simp only [Real.norm_eq_abs, abs_mul, abs_abs]
    calc |g₁ t + g₂ t| * |src.cardyV a t| ≤ (|g₁ t| + |g₂ t|) * |src.cardyV a t| :=
          mul_le_mul_of_nonneg_right (abs_add_le _ _) (abs_nonneg _)
      _ = |g₁ t| * |src.cardyV a t| + |g₂ t| * |src.cardyV a t| := by ring

lemma testClass_smul_src {src : ShiftSource} {a : ℝ} (c : ℝ) {g : ℝ → ℝ}
    (hg : TestClass src a g) : TestClass src a (fun t => c * g t) where
  cont := continuousOn_const.mul hg.cont
  int_lift := by
    have heq : radialLift src.w (fun t => c * g t) = fun x => (c : ℂ) • radialLift src.w g x := by
      ext x; simp [radialLift, smul_eq_mul]
    rw [heq]
    exact hg.int_lift.smul (c : ℂ)
  fourier_odd := by
    have heq : radialLift src.w (fun t => c * g t) = fun x => (c : ℂ) • radialLift src.w g x := by
      ext x; simp [radialLift, smul_eq_mul]
    rw [heq, FormalResearch.ModularBootstrap.Upper.Membership.fourier_smul_fn', hg.fourier_odd]
    ext x; simp
  int_cardy := by
    have heq : (fun t => |c * g t| * src.cardyV a t) = fun t => |c| * (|g t| * src.cardyV a t) := by
      ext t; rw [abs_mul]; ring
    rw [heq]
    exact hg.int_cardy.const_mul _

lemma testClass_sum_src {src : ShiftSource} {a : ℝ} {ι : Type*} (s : Finset ι)
    (l : ι → ℝ) (g : ι → ℝ → ℝ) (hg : ∀ i ∈ s, TestClass src a (g i)) :
    TestClass src a (fun t => ∑ i ∈ s, l i * g i t) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using testClass_zero_src src a
  | @insert i s hi ih =>
    have hg_i : TestClass src a (g i) := hg i (Finset.mem_insert_self i s)
    have hg_s : ∀ j ∈ s, TestClass src a (g j) := fun j hj => hg j (Finset.mem_insert_of_mem hj)
    have heq : (fun t => ∑ j ∈ insert i s, l j * g j t) =
        fun t => l i * g i t + ∑ j ∈ s, l j * g j t := by
      ext t; rw [Finset.sum_insert hi]
    rw [heq]
    exact testClass_add_src (testClass_smul_src (l i) hg_i) (ih hg_s)

lemma integrableOn_mul_cardyV_of_testClass {src : ShiftSource} {a : ℝ} {g : ℝ → ℝ}
    (hg : TestClass src a g) :
    IntegrableOn (fun t => g t * src.cardyV a t) (Ioi 0) := by
  refine hg.int_cardy.norm.mono' ?_ ?_
  · exact ((hg.cont.mono Ioi_subset_Ici_self).mul
      (src.continuous_cardyV a).continuousOn).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_abs]

lemma gVac_add_src {src : ShiftSource} {a : ℝ} {g₁ g₂ : ℝ → ℝ}
    (h₁ : TestClass src a g₁) (h₂ : TestClass src a g₂) :
    src.gVac a (fun t => g₁ t + g₂ t) = src.gVac a g₁ + src.gVac a g₂ := by
  unfold ShiftSource.gVac
  have heq : (fun t => (g₁ t + g₂ t) * src.cardyV a t) =
      fun t => g₁ t * src.cardyV a t + g₂ t * src.cardyV a t := by ext t; ring
  rw [heq, integral_add (integrableOn_mul_cardyV_of_testClass h₁)
    (integrableOn_mul_cardyV_of_testClass h₂)]
  ring

lemma gVac_smul_src {src : ShiftSource} {a : ℝ} (c : ℝ) {g : ℝ → ℝ} :
    src.gVac a (fun t => c * g t) = c * src.gVac a g := by
  unfold ShiftSource.gVac
  have heq : (fun t => c * g t * src.cardyV a t) = fun t => c * (g t * src.cardyV a t) := by
    ext t; ring
  rw [heq, integral_const_mul]
  ring

lemma gVac_sum_src {src : ShiftSource} {a : ℝ} {ι : Type*} (s : Finset ι)
    (l : ι → ℝ) (g : ι → ℝ → ℝ) (hg : ∀ i ∈ s, TestClass src a (g i)) :
    src.gVac a (fun t => ∑ i ∈ s, l i * g i t) = ∑ i ∈ s, l i * src.gVac a (g i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [ShiftSource.gVac]
  | @insert i s hi ih =>
    have hg_i : TestClass src a (g i) := hg i (Finset.mem_insert_self i s)
    have hg_s : ∀ j ∈ s, TestClass src a (g j) := fun j hj => hg j (Finset.mem_insert_of_mem hj)
    have heq : (fun t => ∑ j ∈ insert i s, l j * g j t) =
        fun t => l i * g i t + ∑ j ∈ s, l j * g j t := by
      ext t; rw [Finset.sum_insert hi]
    rw [heq, Finset.sum_insert hi, gVac_add_src (testClass_smul_src (l i) hg_i)
      (testClass_sum_src s l g hg_s), gVac_smul_src (l i), ih hg_s]

lemma gVac_thermalDiff_src_eq (src : ShiftSource) (a : ℝ) {β : ℝ} (hβ : 0 < β) :
    src.gVac a (thermalDiff src.w β) =
      src.srcFun a β - β ^ (-(src.w : ℝ)) * src.srcFun a β⁻¹ := by
  unfold ShiftSource.gVac
  have h1 := src.cardyV_laplace a hβ
  have h2 := src.cardyV_laplace a (inv_pos.mpr hβ)
  have heq : (fun t => thermalDiff src.w β t * src.cardyV a t) =
      fun t => src.cardyV a t * Real.exp (-2 * π * β * t) -
        β ^ (-(src.w : ℝ)) * (src.cardyV a t * Real.exp (-2 * π * β⁻¹ * t)) := by
    ext t; unfold thermalDiff
    rw [show -2 * π * t / β = -2 * π * β⁻¹ * t by ring]
    ring
  rw [heq, integral_sub h1.1 (h2.1.const_mul _), integral_const_mul]
  have hi2 : 2 * π * ∫ t in Ioi 0, src.cardyV a t * Real.exp (-2 * π * β⁻¹ * t) =
      β ^ (src.w : ℝ) * src.srcFun a β := by
    rw [h2.2, inv_inv, Real.inv_rpow hβ.le, Real.rpow_neg hβ.le, inv_inv]
  have hmul : -2 * π *
      ((∫ t in Ioi 0, src.cardyV a t * Real.exp (-2 * π * β * t)) -
        β ^ (-(src.w : ℝ)) * ∫ t in Ioi 0, src.cardyV a t * Real.exp (-2 * π * β⁻¹ * t)) =
      -(2 * π * ∫ t in Ioi 0, src.cardyV a t * Real.exp (-2 * π * β * t)) +
        β ^ (-(src.w : ℝ)) *
          (2 * π * ∫ t in Ioi 0, src.cardyV a t * Real.exp (-2 * π * β⁻¹ * t)) := by ring
  rw [hmul, h1.2, hi2]
  have hpow : β ^ (-(src.w : ℝ)) * β ^ (src.w : ℝ) = 1 := by
    rw [← Real.rpow_add hβ, neg_add_cancel, Real.rpow_zero]
  calc -(β ^ (-(src.w : ℝ)) * src.srcFun a β⁻¹) + β ^ (-(src.w : ℝ)) * (β ^ (src.w : ℝ) * src.srcFun a β)
      = -(β ^ (-(src.w : ℝ)) * src.srcFun a β⁻¹) + (β ^ (-(src.w : ℝ)) * β ^ (src.w : ℝ)) * src.srcFun a β := by ring
    _ = src.srcFun a β - β ^ (-(src.w : ℝ)) * src.srcFun a β⁻¹ := by rw [hpow, one_mul]; ring

/-- Crossing right-hand side `a_β = ∫₀^∞ Ξ_β^{(w)}(t) ρ_C(t) dt` for a `ShiftSource`. -/
noncomputable def crossingRHSS (src : ShiftSource) (a β : ℝ) : ℝ :=
  ∫ t in Ioi 0, thermalDiff src.w β t * src.cardyDensity a t

lemma gVac_thermalDiff_src_eq_neg (src : ShiftSource) (a β : ℝ) :
    src.gVac a (thermalDiff src.w β) = -crossingRHSS src a β := by
  unfold ShiftSource.gVac crossingRHSS ShiftSource.cardyDensity
  have heq : (fun t => thermalDiff src.w β t * (2 * π * src.cardyV a t)) =
      fun t => (2 * π) * (thermalDiff src.w β t * src.cardyV a t) := by ext t; ring
  rw [heq, integral_const_mul]; ring

/-! ### `SourceDualSetupCore` and constructions from `FloorData`, `CommonSource`, `MixtureData` -/

/-- Standing dual hypotheses (`ds:M`, `ds:E`, `ds:LP` input) for an atomic shift source:
the DU-G `DualSetupCore` generalised from `FixedWeightProblem` to `ShiftSource`. -/
structure SourceDualSetupCore (src : ShiftSource) (cTilde β₀ T₀ : ℝ) : Prop where
  hc_pos : 0 < cTilde
  hshift : src.ShiftLE (cTilde / 12)
  hnonneg : ∀ {t : ℝ}, 0 ≤ t → 0 ≤ src.cardyV (cTilde / 12) t
  hupper : ∀ {t : ℝ}, 0 ≤ t → src.cardyV (cTilde / 12) t ≤ src.tv * kernelK src.w (cTilde / 12) t
  hβ₀ : 0 < β₀
  hβ₀2 : β₀ ≤ 1 / 2
  hT₀ : t0Star src.w β₀ ≤ T₀
  hT₀pos : 0 < T₀
  hvac_neg : ∀ {β : ℝ}, 0 < β → β ≤ β₀ → src.gVac (cTilde / 12) (thermalDiff src.w β) < 0

lemma SourceDualSetupCore.ha_pos {src : ShiftSource} {cTilde β₀ T₀ : ℝ}
    (S : SourceDualSetupCore src cTilde β₀ T₀) : 0 < cTilde / 12 := by linarith [S.hc_pos]

/-- Convert a fixed-weight `FixedWeight.DualSetupCore` into `SourceDualSetupCore`. -/
lemma SourceDualSetupCore.of_fixedWeight {prob : FixedWeightProblem} {cTilde β₀ T₀ : ℝ}
    (S : FixedWeight.DualSetupCore prob cTilde β₀ T₀) :
    SourceDualSetupCore (ShiftSource.ofProblem prob) cTilde β₀ T₀ where
  hc_pos := S.hc_pos
  hshift := (ofProblem_shiftLE_iff prob).2 S.ha
  hnonneg ht := prob.cardyV_nonneg S.ha ht
  hupper ht := by
    have hV := (ofProblem_shiftLE_iff prob).2 S.ha
    rw [ofProblem_cardyV]
    exact (ShiftSource.ofProblem prob).cardyV_le hV ht
  hβ₀ := S.hβ₀
  hβ₀2 := S.hβ₀2
  hT₀ := S.hT₀
  hT₀pos := S.hT₀pos
  hvac_neg {β} hβ hβle := by
    rw [ofProblem_gVac]
    exact gVac_thermalDiff_neg prob S.ha_pos hβ (lt_of_le_of_lt hβle (by linarith [S.hβ₀2]))

/-- Lower bound for `-g_vac(Ξ_γ)` under a floor `F.At a`:
`d_λ Q_0(e^{-2π}) γ^{-w} e^{2πa/γ} - ‖λ‖_TV e^{2πa} ≤ -src.gVac a (Ξ_γ)` for `0 < γ ≤ 1`. -/
lemma neg_gVac_thermalDiff_src_ge {src : ShiftSource} {F : FloorData src} {a γ : ℝ}
    (h : F.At a) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    F.d * F.prob.nullPoly (Real.exp (-2 * π)) *
        (γ ^ (-(src.w : ℝ)) * Real.exp (2 * π * a / γ)) -
      src.tv * Real.exp (2 * π * a) ≤
    -src.gVac a (thermalDiff src.w γ) := by
  have h1 := src.cardyV_laplace a hγ
  have h2 := F.prob.cardyV_laplace a hγ
  have hfl_int : F.d * (2 * π * ∫ t in Ioi 0, F.prob.cardyV a t * Real.exp (-2 * π * γ * t)) ≤
      2 * π * ∫ t in Ioi 0, src.cardyV a t * Real.exp (-2 * π * γ * t) := by
    have heq1 : F.d * (2 * π * ∫ t in Ioi 0, F.prob.cardyV a t * Real.exp (-2 * π * γ * t)) =
        2 * π * ∫ t in Ioi 0, (F.d * F.prob.cardyV a t) * Real.exp (-2 * π * γ * t) := by
      calc F.d * (2 * π * ∫ t in Ioi 0, F.prob.cardyV a t * Real.exp (-2 * π * γ * t))
          = 2 * π * (F.d * ∫ t in Ioi 0, F.prob.cardyV a t * Real.exp (-2 * π * γ * t)) := by ring
        _ = 2 * π * ∫ t in Ioi 0, F.d * (F.prob.cardyV a t * Real.exp (-2 * π * γ * t)) := by
            rw [← integral_const_mul]
        _ = 2 * π * ∫ t in Ioi 0, (F.d * F.prob.cardyV a t) * Real.exp (-2 * π * γ * t) := by
            refine congrArg (fun x : ℝ => 2 * π * x)
              (setIntegral_congr_fun measurableSet_Ioi fun (t : ℝ) _ => by ring)
    rw [heq1]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hint2 : IntegrableOn (fun t => F.d * F.prob.cardyV a t * Real.exp (-2 * π * γ * t)) (Ioi 0) :=
      (h2.1.const_mul F.d).congr (Filter.Eventually.of_forall fun t => by ring)
    exact setIntegral_mono_on hint2 h1.1 measurableSet_Ioi fun t ht =>
      mul_le_mul_of_nonneg_right (h.lower ht) (Real.exp_pos _).le
  rw [h2.2, h1.2] at hfl_int
  have hlow_term : F.d * F.prob.nullPoly (Real.exp (-2 * π)) *
      (γ ^ (-(src.w : ℝ)) * Real.exp (2 * π * a / γ)) ≤
      γ ^ (-(src.w : ℝ)) * src.srcFun a γ⁻¹ := by
    have hq2 : Real.exp (-2 * π / γ) ≤ Real.exp (-2 * π) := by
      refine Real.exp_le_exp.2 ?_; rw [div_le_iff₀ hγ]; nlinarith [Real.pi_pos]
    have hq3 : Real.exp (-2 * π) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos])
    have hQ : F.prob.nullPoly (Real.exp (-2 * π)) ≤ F.prob.nullPoly (Real.exp (-2 * π / γ)) :=
      nullPoly_antitone_on_Icc F.prob (Real.exp_pos _).le hq2 hq3
    have hmul : F.d * (γ ^ (-(src.w : ℝ)) * Real.exp (2 * π * a / γ) *
        F.prob.nullPoly (Real.exp (-2 * π))) ≤
        F.d * (γ ^ (-(src.w : ℝ)) * Real.exp (2 * π * a / γ) *
          F.prob.nullPoly (Real.exp (-2 * π / γ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hQ (by positivity)) F.hd.le
    have hw_eq : (F.prob.w : ℝ) = (src.w : ℝ) := by simp
    have hdiv : 2 * π * a / γ = 2 * π * a * γ⁻¹ := by rw [div_eq_mul_inv]
    rw [hw_eq, hdiv] at hfl_int
    calc F.d * F.prob.nullPoly (Real.exp (-2 * π)) *
          (γ ^ (-(src.w : ℝ)) * Real.exp (2 * π * a / γ))
        = F.d * (γ ^ (-(src.w : ℝ)) * Real.exp (2 * π * a / γ) *
            F.prob.nullPoly (Real.exp (-2 * π))) := by ring
      _ ≤ F.d * (γ ^ (-(src.w : ℝ)) * Real.exp (2 * π * a / γ) *
            F.prob.nullPoly (Real.exp (-2 * π / γ))) := hmul
      _ ≤ γ ^ (-(src.w : ℝ)) * src.srcFun a γ⁻¹ := by rw [hdiv]; exact hfl_int
  have hup_term : src.srcFun a γ ≤ src.tv * Real.exp (2 * π * a) := by
    unfold ShiftSource.srcFun ShiftSource.tv
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    have hexp : Real.exp (2 * π * (a - src.shift j) * γ) ≤ Real.exp (2 * π * a) := by
      refine Real.exp_le_exp.mpr ?_
      have hs := mul_nonneg (src.hshift j) hγ.le
      have h1' : 2 * π * (a - src.shift j) * γ ≤ 2 * π * a * γ := by nlinarith [Real.pi_pos]
      have h2' : 2 * π * a * γ ≤ 2 * π * a * 1 :=
        mul_le_mul_of_nonneg_left hγ1 (mul_nonneg (by positivity) h.pos.le)
      linarith
    calc src.coef j * Real.exp (2 * π * (a - src.shift j) * γ)
        ≤ |src.coef j| * Real.exp (2 * π * (a - src.shift j) * γ) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le
      _ ≤ |src.coef j| * Real.exp (2 * π * a) :=
          mul_le_mul_of_nonneg_left hexp (abs_nonneg _)
  rw [gVac_thermalDiff_src_eq src a hγ]
  linarith

/-- Small-`β` vacuum negativity for any floor charge (`ds:M` / `dual_spectrum.tex`):
if `F.At a`, there exists `β₁ ∈ (0, 1/2]` such that `g_vac(Ξ_β) < 0` for all `0 < β ≤ β₁`. -/
lemma exists_beta1_gVac_neg {src : ShiftSource} {F : FloorData src} {a : ℝ} (h : F.At a) :
    ∃ β₁ : ℝ, 0 < β₁ ∧ β₁ ≤ 1 / 2 ∧
      ∀ {β : ℝ}, 0 < β → β ≤ β₁ → src.gVac a (thermalDiff src.w β) < 0 := by
  have ha0 : 0 < a := h.pos
  have hq0_pos : 0 < F.prob.nullPoly (Real.exp (-2 * π)) :=
    F.prob.nullPoly_pos (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos]))
  set c_low : ℝ := F.d * F.prob.nullPoly (Real.exp (-2 * π)) with hc_low
  have hcl_pos : 0 < c_low := mul_pos F.hd hq0_pos
  set L : ℝ := max 0 (Real.log ((src.tv + 1) / c_low)) + 1 with hL
  have hL_pos : 0 < L := by positivity
  set β₁ : ℝ := min (1 / 2) ((2 * π * a) / (2 * π * a + L)) with hβ₁def
  have hden_pos : 0 < 2 * π * a + L := by positivity
  have hβ₁_pos : 0 < β₁ := lt_min (by norm_num) (div_pos (by positivity) hden_pos)
  have hβ₁_half : β₁ ≤ 1 / 2 := min_le_left _ _
  refine ⟨β₁, hβ₁_pos, hβ₁_half, fun {β} hβ hβle => ?_⟩
  have hβ1 : β ≤ 1 := by linarith
  have hlow := neg_gVac_thermalDiff_src_ge h hβ hβ1
  have hβ_bound : β ≤ (2 * π * a) / (2 * π * a + L) := hβle.trans (min_le_right _ _)
  have hmul : β * (2 * π * a + L) ≤ 2 * π * a := (le_div_iff₀ hden_pos).mp hβ_bound
  have hexp_arg : 2 * π * a + L ≤ 2 * π * a / β := by
    rw [le_div_iff₀ hβ]; linarith
  have hbw : 1 ≤ β ^ (-(src.w : ℝ)) := by
    rw [Real.rpow_neg hβ.le, one_le_inv₀ (Real.rpow_pos_of_pos hβ _)]
    exact Real.rpow_le_one hβ.le hβ1 (Nat.cast_nonneg _)
  have hexp_ge : Real.exp (2 * π * a) * ((src.tv + 1) / c_low) < Real.exp (2 * π * a / β) := by
    have hlog : Real.log ((src.tv + 1) / c_low) < L := by
      have := le_max_right 0 (Real.log ((src.tv + 1) / c_low))
      linarith
    have hEL : (src.tv + 1) / c_low < Real.exp L := by
      calc (src.tv + 1) / c_low = Real.exp (Real.log ((src.tv + 1) / c_low)) :=
            (Real.exp_log (div_pos (by linarith [src.tv_nonneg]) hcl_pos)).symm
        _ < Real.exp L := Real.exp_lt_exp.mpr hlog
    calc Real.exp (2 * π * a) * ((src.tv + 1) / c_low)
        < Real.exp (2 * π * a) * Real.exp L := mul_lt_mul_of_pos_left hEL (Real.exp_pos _)
      _ = Real.exp (2 * π * a + L) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (2 * π * a / β) := Real.exp_le_exp.mpr hexp_arg
  have hprod_ge : src.tv * Real.exp (2 * π * a) <
      c_low * (β ^ (-(src.w : ℝ)) * Real.exp (2 * π * a / β)) := by
    have htv_lt : src.tv * Real.exp (2 * π * a) < (src.tv + 1) * Real.exp (2 * π * a) := by
      nlinarith [Real.exp_pos (2 * π * a)]
    have heq_low : (src.tv + 1) * Real.exp (2 * π * a) =
        c_low * (Real.exp (2 * π * a) * ((src.tv + 1) / c_low)) := by
      field_simp [hcl_pos.ne']
    have hrpow_mul : Real.exp (2 * π * a / β) ≤ β ^ (-(src.w : ℝ)) * Real.exp (2 * π * a / β) :=
      le_mul_of_one_le_left (Real.exp_pos _).le hbw
    calc src.tv * Real.exp (2 * π * a)
        < c_low * (Real.exp (2 * π * a) * ((src.tv + 1) / c_low)) := heq_low ▸ htv_lt
      _ < c_low * Real.exp (2 * π * a / β) := mul_lt_mul_of_pos_left hexp_ge hcl_pos
      _ ≤ c_low * (β ^ (-(src.w : ℝ)) * Real.exp (2 * π * a / β)) :=
          mul_le_mul_of_nonneg_left hrpow_mul hcl_pos.le
  linarith

/-- Build `SourceDualSetupCore` for any `F.At (cTilde / 12)` and `T₀ > 0`. -/
lemma SourceDualSetupCore.exists_of_floor {src : ShiftSource} {F : FloorData src} {cTilde T₀ : ℝ}
    (h : F.At (cTilde / 12)) (hT₀pos : 0 < T₀) :
    ∃ β₀ : ℝ, SourceDualSetupCore src cTilde β₀ T₀ := by
  obtain ⟨β₁, hβ₁pos, hβ₁2, hβ₁neg⟩ := exists_beta1_gVac_neg h
  obtain ⟨β₂, hβ₂pos, hβ₂2, hβ₂T⟩ := exists_beta0 src.w hT₀pos
  refine ⟨min β₁ β₂, ⟨by linarith [h.pos], h.shift, fun ht => h.nonneg_V ht,
    fun ht => src.cardyV_le h.shift ht, lt_min hβ₁pos hβ₂pos, (min_le_left _ _).trans hβ₁2, ?_,
    hT₀pos, fun hβ hβle => hβ₁neg hβ (hβle.trans (min_le_left _ _))⟩⟩
  calc t0Star src.w (min β₁ β₂) = t0 src.w (min β₁ β₂) :=
        t0Star_eq_t0 (lt_min hβ₁pos hβ₂pos) (lt_of_le_of_lt ((min_le_left _ _).trans hβ₁2) (by norm_num))
    _ ≤ t0 src.w β₂ := t0_mono src.w (lt_min hβ₁pos hβ₂pos) (min_le_right _ _)
        (lt_of_le_of_lt hβ₂2 (by norm_num))
    _ = t0Star src.w β₂ := (t0Star_eq_t0 hβ₂pos (lt_of_le_of_lt hβ₂2 (by norm_num))).symm
    _ ≤ T₀ := hβ₂T

/-- Build `SourceDualSetupCore` for a `CommonSource` at any charge `cTilde ≥ 12 C.a₀` and `T₀ > 0`. -/
lemma SourceDualSetupCore.exists_of_common (C : CommonSource) {cTilde T₀ : ℝ}
    (hc : 12 * C.a₀ ≤ cTilde) (hT₀pos : 0 < T₀) :
    ∃ β₀ : ℝ, SourceDualSetupCore C.src cTilde β₀ T₀ :=
  SourceDualSetupCore.exists_of_floor (C.at_ (by linarith)) hT₀pos

/-- A rebased positive mixture with `c̃ > 0`, `c̃ ≥ 12 S_max` satisfies `SourceDualSetupCore`
for **every** `β₀ ∈ (0, 1/2]` with `t₀^*(w, β₀) ≤ T₀` (because every component has `g_vac(Ξ_β) < 0`
for all `β ∈ (0, 1)`). -/
lemma SourceDualSetupCore.of_mixture (M : MixtureData) {cTilde β₀ T₀ : ℝ}
    (hc_pos : 0 < cTilde) (hS : 12 * M.Smax ≤ cTilde)
    (hβ₀ : 0 < β₀) (hβ₀2 : β₀ ≤ 1 / 2) (hT₀ : t0Star M.w β₀ ≤ T₀) (hT₀pos : 0 < T₀) :
    SourceDualSetupCore M.toSource cTilde β₀ T₀ where
  hc_pos := hc_pos
  hshift := M.shiftLE_of_Smax (by linarith)
  hnonneg {t} ht := by
    rw [M.toSource_cardyV (cTilde / 12) t]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (M.hd i).le
      ((M.Q i).cardyV_nonneg (by linarith [M.le_Smax i]) ht)
  hupper {t} ht := M.toSource.cardyV_le (M.shiftLE_of_Smax (by linarith)) ht
  hβ₀ := hβ₀
  hβ₀2 := hβ₀2
  hT₀ := hT₀
  hT₀pos := hT₀pos
  hvac_neg {β} hβ hβle := by
    have hβ1 : β < 1 := lt_of_le_of_lt (hβle.trans hβ₀2) (by norm_num)
    have ha0 : 0 < cTilde / 12 := by linarith
    have hlap := M.toSource.cardyV_laplace (cTilde / 12) hβ
    rw [gVac_thermalDiff_src_eq M.toSource (cTilde / 12) hβ]
    have hcomp : ∀ i : Fin M.s,
        Real.exp (2 * π * (cTilde / 12 - M.r i) * β) * (M.Q i).nullPoly (Real.exp (-2 * π * β)) <
          β ^ (-(M.w : ℝ)) * Real.exp (2 * π * (cTilde / 12 - M.r i) / β) *
            (M.Q i).nullPoly (Real.exp (-2 * π / β)) := fun i => by
      have ha_nn : 0 ≤ cTilde / 12 - M.r i := by linarith [M.le_Smax i, (M.Q i).totalShift_nonneg]
      have hq1_pos : 0 < Real.exp (-2 * π * β) := Real.exp_pos _
      have hq1_lt : Real.exp (-2 * π * β) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
      have hq2_pos : 0 < Real.exp (-2 * π / β) := Real.exp_pos _
      have hβ_inv : β < β⁻¹ := lt_trans hβ1 ((one_lt_inv₀ hβ).mpr hβ1)
      have hq2_le_q1 : Real.exp (-2 * π / β) ≤ Real.exp (-2 * π * β) := by
        refine Real.exp_le_exp.mpr ?_
        rw [show -2 * π / β = -2 * π * β⁻¹ by ring]
        nlinarith [Real.pi_pos]
      have hQ1_pos : 0 < (M.Q i).nullPoly (Real.exp (-2 * π * β)) :=
        (M.Q i).nullPoly_pos hq1_pos.le hq1_lt
      have hQ1_le_Q2 : (M.Q i).nullPoly (Real.exp (-2 * π * β)) ≤
          (M.Q i).nullPoly (Real.exp (-2 * π / β)) :=
        nullPoly_antitone_on_Icc (M.Q i) hq2_pos.le hq2_le_q1 hq1_lt.le
      have hbw_gt1 : 1 < β ^ (-(M.w : ℝ)) := by
        rw [Real.rpow_neg hβ.le, one_lt_inv₀ (Real.rpow_pos_of_pos hβ _)]
        exact Real.rpow_lt_one hβ.le hβ1 (by exact_mod_cast M.hw)
      have hexp_le : Real.exp (2 * π * (cTilde / 12 - M.r i) * β) ≤
          Real.exp (2 * π * (cTilde / 12 - M.r i) / β) := by
        refine Real.exp_le_exp.mpr ?_
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left hβ_inv.le (mul_nonneg (by positivity) ha_nn)
      calc Real.exp (2 * π * (cTilde / 12 - M.r i) * β) *
            (M.Q i).nullPoly (Real.exp (-2 * π * β))
          < β ^ (-(M.w : ℝ)) * Real.exp (2 * π * (cTilde / 12 - M.r i) * β) *
              (M.Q i).nullPoly (Real.exp (-2 * π * β)) := by
            have hpos := mul_pos (Real.exp_pos (2 * π * (cTilde / 12 - M.r i) * β)) hQ1_pos
            calc _ = 1 * (Real.exp (2 * π * (cTilde / 12 - M.r i) * β) *
                    (M.Q i).nullPoly (Real.exp (-2 * π * β))) := (one_mul _).symm
              _ < β ^ (-(M.w : ℝ)) * (Real.exp (2 * π * (cTilde / 12 - M.r i) * β) *
                    (M.Q i).nullPoly (Real.exp (-2 * π * β))) :=
                    mul_lt_mul_of_pos_right hbw_gt1 hpos
              _ = _ := by ring
        _ ≤ β ^ (-(M.w : ℝ)) * Real.exp (2 * π * (cTilde / 12 - M.r i) / β) *
              (M.Q i).nullPoly (Real.exp (-2 * π * β)) := by
            gcongr
        _ ≤ β ^ (-(M.w : ℝ)) * Real.exp (2 * π * (cTilde / 12 - M.r i) / β) *
              (M.Q i).nullPoly (Real.exp (-2 * π / β)) := by
            gcongr
    have hsf : ∀ x, 0 < x → M.toSource.srcFun (cTilde / 12) x =
        ∑ i : Fin M.s, M.d i * Real.exp (2 * π * (cTilde / 12 - M.r i) * x) *
          (M.Q i).nullPoly (Real.exp (-2 * π * x)) := fun x hx => by
      simpa [mul_assoc] using M.toSource_srcFun (cTilde / 12) x
    rw [hsf β hβ, hsf β⁻¹ (inv_pos.mpr hβ)]
    have hlt_sum : ∑ i : Fin M.s, M.d i * Real.exp (2 * π * (cTilde / 12 - M.r i) * β) *
          (M.Q i).nullPoly (Real.exp (-2 * π * β)) <
        ∑ i : Fin M.s, M.d i * (β ^ (-(M.w : ℝ)) * Real.exp (2 * π * (cTilde / 12 - M.r i) / β) *
          (M.Q i).nullPoly (Real.exp (-2 * π / β))) := by
      refine Finset.sum_lt_sum (fun i _ => ?_) ⟨⟨0, M.hs⟩, Finset.mem_univ _, ?_⟩
      · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hcomp i).le (M.hd i).le
      · simpa only [mul_assoc] using mul_lt_mul_of_pos_left (hcomp ⟨0, M.hs⟩) (M.hd _)
    have hrhs_eq : β ^ (-(M.w : ℝ)) * ∑ i : Fin M.s, M.d i *
          Real.exp (2 * π * (cTilde / 12 - M.r i) * β⁻¹) *
          (M.Q i).nullPoly (Real.exp (-2 * π * β⁻¹)) =
        ∑ i : Fin M.s, M.d i * (β ^ (-(M.w : ℝ)) * Real.exp (2 * π * (cTilde / 12 - M.r i) / β) *
          (M.Q i).nullPoly (Real.exp (-2 * π / β))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show 2 * π * (cTilde / 12 - M.r i) * β⁻¹ = 2 * π * (cTilde / 12 - M.r i) / β by ring,
        show -2 * π * β⁻¹ = -2 * π / β by ring]
      ring
    rw [show (M.toSource.w : ℝ) = M.w from rfl]
    linarith

/-! ### Lemma M (`ds:M`) for `SourceDualSetupCore` -/

private lemma trivial_cardyV_eq (w : ℕ) (hw : 1 ≤ w) (a t : ℝ) :
    (trivialProductProblem w hw).cardyV a t = kernelK w a t := by
  rw [FixedWeightProblem.cardyV]
  have hsub : Subsingleton (Finset (Fin (trivialProductProblem w hw).m)) :=
    ⟨fun s₁ s₂ => by ext i; exact Fin.elim0 (Fin.cast (by rfl) i)⟩
  rw [Fintype.sum_subsingleton _ ∅]
  have hcard : (∅ : Finset (Fin (trivialProductProblem w hw).m)).card = 0 := Finset.card_empty
  have hsum : (trivialProductProblem w hw).shiftSum
      (∅ : Finset (Fin (trivialProductProblem w hw).m)) = 0 := by
    simp [FixedWeightProblem.shiftSum]
  rw [hcard, hsum]
  simp [trivialProductProblem]

lemma thermalDiff_mem_TestClass_src {src : ShiftSource} {a : ℝ} (ha0 : 0 < a)
    (hnonneg : ∀ {t : ℝ}, 0 ≤ t → 0 ≤ src.cardyV a t)
    (hupper : ∀ {t : ℝ}, 0 ≤ t → src.cardyV a t ≤ src.tv * kernelK src.w a t)
    {β : ℝ} (hβ : 0 < β) :
    TestClass src a (thermalDiff src.w β) := by
  let prob0 := trivialProductProblem src.w src.hw
  have hK : Crossing.TestClass prob0 a (thermalDiff prob0.w β) :=
    thermalDiff_mem_TestClass prob0 (by simp [prob0, trivialProductProblem_totalShift, ha0.le]) hβ
  refine ⟨hK.cont, hK.int_lift, hK.fourier_odd, ?_⟩
  have hV_m : AEStronglyMeasurable (fun t => |thermalDiff src.w β t| * src.cardyV a t)
      (volume.restrict (Ioi 0)) :=
    (((hK.cont.abs.mono Ioi_subset_Ici_self).mul
      (src.continuous_cardyV a).continuousOn)).aestronglyMeasurable measurableSet_Ioi
  refine (hK.int_cardy.const_mul src.tv).mono' hV_m ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 ≤ t := (mem_Ioi.mp ht).le
  have hVn := hnonneg ht0
  rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) hVn)]
  have hKV : prob0.cardyV a t = kernelK src.w a t := trivial_cardyV_eq src.w src.hw a t
  have hw0 : prob0.w = src.w := rfl
  calc |thermalDiff src.w β t| * src.cardyV a t
      ≤ |thermalDiff src.w β t| * (src.tv * kernelK src.w a t) :=
        mul_le_mul_of_nonneg_left (hupper ht0) (abs_nonneg _)
    _ = src.tv * (|thermalDiff prob0.w β t| * prob0.cardyV a t) := by
        rw [hKV, hw0]; ring

lemma hMaj_mem_TestClass_src {src : ShiftSource} {a β₀ : ℝ} (ha0 : 0 < a)
    (hnonneg : ∀ {t : ℝ}, 0 ≤ t → 0 ≤ src.cardyV a t)
    (hupper : ∀ {t : ℝ}, 0 ≤ t → src.cardyV a t ≤ src.tv * kernelK src.w a t) :
    TestClass src a (FixedWeight.hMaj src.w a β₀) := by
  let prob0 := trivialProductProblem src.w src.hw
  have hM : Crossing.TestClass prob0 a (FixedWeight.hMaj prob0.w a β₀) :=
    hMaj_mem_TestClass prob0 (by simp [prob0, trivialProductProblem_totalShift, ha0.le]) ha0
  refine ⟨hM.cont, hM.int_lift, hM.fourier_odd, ?_⟩
  have hV_m : AEStronglyMeasurable (fun t => |FixedWeight.hMaj src.w a β₀ t| * src.cardyV a t)
      (volume.restrict (Ioi 0)) :=
    (((hM.cont.abs.mono Ioi_subset_Ici_self).mul
      (src.continuous_cardyV a).continuousOn)).aestronglyMeasurable measurableSet_Ioi
  refine (hM.int_cardy.const_mul src.tv).mono' hV_m ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 ≤ t := (mem_Ioi.mp ht).le
  have hVn := hnonneg ht0
  rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) hVn)]
  have hKV : prob0.cardyV a t = kernelK src.w a t := trivial_cardyV_eq src.w src.hw a t
  have hw0 : prob0.w = src.w := rfl
  calc |FixedWeight.hMaj src.w a β₀ t| * src.cardyV a t
      ≤ |FixedWeight.hMaj src.w a β₀ t| * (src.tv * kernelK src.w a t) :=
        mul_le_mul_of_nonneg_left (hupper ht0) (abs_nonneg _)
    _ = src.tv * (|FixedWeight.hMaj prob0.w a β₀ t| * prob0.cardyV a t) := by
        rw [hKV, hw0]; ring

/-- `C₀ := -g_vac(h) = 2 ∫₀^{β₀} (-g_vac(Ξ_β)) ϑ(dβ)` for a `ShiftSource`. -/
noncomputable def dualC0S (src : ShiftSource) (a β₀ : ℝ) : ℝ :=
  -src.gVac a (FixedWeight.hMaj src.w a β₀)

private lemma integrable_prod_V_src {src : ShiftSource} {a β₀ : ℝ} (ha0 : 0 < a)
    (hnonneg : ∀ {t : ℝ}, 0 ≤ t → 0 ≤ src.cardyV a t)
    (hupper : ∀ {t : ℝ}, 0 ≤ t → src.cardyV a t ≤ src.tv * kernelK src.w a t) :
    Integrable (fun p : ℝ × ℝ =>
        thermalDiff src.w p.2 p.1 * src.cardyV a p.1 * thetaW a p.2)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioc 0 β₀))) := by
  let prob0 := trivialProductProblem src.w src.hw
  have hP0 := integrable_prod_V prob0 (β₀ := β₀)
    (by simp [prob0, trivialProductProblem_totalShift, ha0.le]) ha0
  have hFm : Measurable (fun p : ℝ × ℝ =>
      thermalDiff src.w p.2 p.1 * src.cardyV a p.1 * thetaW a p.2) := by
    have := measurable_thetaW a
    have hV := (src.continuous_cardyV a).measurable
    unfold thermalDiff; fun_prop
  refine (hP0.norm.const_mul src.tv).mono' hFm.aestronglyMeasurable ?_
  have hKV : ∀ t, prob0.cardyV a t = kernelK src.w a t := fun t => trivial_cardyV_eq src.w src.hw a t
  have hw0 : prob0.w = src.w := rfl
  have hae : ∀ᵐ p : ℝ × ℝ ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioc 0 β₀))),
      p.1 ∈ Ioi (0 : ℝ) ∧ p.2 ∈ Ioc (0 : ℝ) β₀ := by
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioc)
  filter_upwards [hae] with p hp
  have ht0 : 0 ≤ p.1 := (mem_Ioi.mp hp.1).le
  have hVn := hnonneg ht0
  have hK0 : 0 ≤ kernelK src.w a p.1 := kernelK_nonneg ha0.le ht0
  have hup := hupper ht0
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hVn, abs_of_pos (thetaW_pos a p.2),
    Real.norm_eq_abs, abs_mul, abs_mul, hKV p.1, hw0, abs_of_nonneg hK0, abs_of_pos (thetaW_pos a p.2)]
  calc |thermalDiff src.w p.2 p.1| * src.cardyV a p.1 * thetaW a p.2
      ≤ |thermalDiff src.w p.2 p.1| * (src.tv * kernelK src.w a p.1) * thetaW a p.2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hup (abs_nonneg _))
          (thetaW_pos a p.2).le
    _ = src.tv * (|thermalDiff src.w p.2 p.1| * kernelK src.w a p.1 * thetaW a p.2) := by ring

lemma dualC0S_eq_integral {src : ShiftSource} {a β₀ : ℝ} (ha0 : 0 < a)
    (hnonneg : ∀ {t : ℝ}, 0 ≤ t → 0 ≤ src.cardyV a t)
    (hupper : ∀ {t : ℝ}, 0 ≤ t → src.cardyV a t ≤ src.tv * kernelK src.w a t) :
    dualC0S src a β₀ =
      2 * ∫ β in Ioc 0 β₀, (-src.gVac a (thermalDiff src.w β)) * thetaW a β := by
  have hP := integrable_prod_V_src (β₀ := β₀) ha0 hnonneg hupper
  have hswap := integral_integral_swap (μ := volume.restrict (Ioi 0))
    (ν := volume.restrict (Ioc 0 β₀))
    (f := fun t β => thermalDiff src.w β t * src.cardyV a t * thetaW a β) hP
  have hvac : src.gVac a (FixedWeight.hMaj src.w a β₀) =
      2 * ∫ β in Ioc 0 β₀, src.gVac a (thermalDiff src.w β) * thetaW a β := by
    unfold ShiftSource.gVac FixedWeight.hMaj
    have e1 : ∀ t : ℝ, 2 * (∫ β in Ioc 0 β₀, thermalDiff src.w β t * thetaW a β) *
        src.cardyV a t =
        2 * ∫ β in Ioc 0 β₀, thermalDiff src.w β t * src.cardyV a t * thetaW a β := fun t => by
      rw [mul_assoc, ← integral_mul_const]
      congr 1; exact integral_congr_ae (Eventually.of_forall fun β => by ring)
    have e2 : ∀ β : ℝ, ∫ t in Ioi 0, thermalDiff src.w β t * src.cardyV a t * thetaW a β =
        (∫ t in Ioi 0, thermalDiff src.w β t * src.cardyV a t) * thetaW a β := fun β =>
      integral_mul_const _ _
    simp_rw [e1]
    rw [integral_const_mul, hswap]
    simp_rw [e2]
    rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun β => ?_)
    ring
  unfold dualC0S
  rw [hvac, ← mul_neg, ← integral_neg]
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun β => by ring)

lemma dualC0S_pos {src : ShiftSource} {cTilde β₀ T₀ : ℝ}
    (S : SourceDualSetupCore src cTilde β₀ T₀) :
    0 < dualC0S src (cTilde / 12) β₀ := by
  rw [dualC0S_eq_integral S.ha_pos S.hnonneg S.hupper]
  refine mul_pos two_pos ?_
  have hint : IntegrableOn
      (fun β => (-src.gVac (cTilde / 12) (thermalDiff src.w β)) * thetaW (cTilde / 12) β)
      (Ioc 0 β₀) := by
    have hP := integrable_prod_V_src (β₀ := β₀) S.ha_pos S.hnonneg S.hupper
    have hi := hP.integral_prod_right
    have heq : (fun β => (-src.gVac (cTilde / 12) (thermalDiff src.w β)) * thetaW (cTilde / 12) β) =
        fun β => (2 * π) * ∫ t in Ioi 0,
          thermalDiff src.w β t * src.cardyV (cTilde / 12) t * thetaW (cTilde / 12) β := by
      ext β
      unfold ShiftSource.gVac
      rw [integral_mul_const]
      ring
    rw [heq]
    exact hi.const_mul (2 * π)
  rw [setIntegral_pos_iff_support_of_nonneg_ae]
  · have hsupp : Function.support
        (fun β => (-src.gVac (cTilde / 12) (thermalDiff src.w β)) * thetaW (cTilde / 12) β) ∩
        Ioc 0 β₀ = Ioc 0 β₀ := by
      ext β
      simp only [mem_inter_iff, Function.mem_support, ne_eq, and_iff_right_iff_imp]
      intro hβ
      exact (mul_pos (neg_pos.mpr (S.hvac_neg hβ.1 hβ.2)) (thetaW_pos (cTilde / 12) β)).ne'
    rw [hsupp]; simp [S.hβ₀]
  · rw [EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
    exact Eventually.of_forall fun β hβ =>
      (mul_pos (neg_pos.mpr (S.hvac_neg hβ.1 hβ.2)) (thetaW_pos (cTilde / 12) β)).le
  · exact hint

/-- **Lemma M (`dual_spectrum.tex`, `ds:M`)** for any atomic source satisfying
`SourceDualSetupCore` (e.g. a `CommonSource` or rebased `MixtureData`). -/
theorem lemma_M_src {src : ShiftSource} {cTilde β₀ T₀ : ℝ}
    (S : SourceDualSetupCore src cTilde β₀ T₀) :
    TestClass src (cTilde / 12) (hMaj src.w (cTilde / 12) β₀) ∧
      src.gVac (cTilde / 12) (hMaj src.w (cTilde / 12) β₀) = -dualC0S src (cTilde / 12) β₀ ∧
      0 < dualC0S src (cTilde / 12) β₀ ∧
      (∀ t, T₀ ≤ t → wStar (cTilde / 12) β₀ t ≤ hMaj src.w (cTilde / 12) β₀ t) ∧
      (∀ β : ℝ, 0 < β → ∃ C : ℝ, 0 < C ∧
        ∀ t, 0 ≤ t → Real.exp (-2 * π * β * t) ≤ C * wStar (cTilde / 12) β₀ t) ∧
      (∀ k : ℕ, Tendsto (fun t => genLaguerrePsi src.w k t / wStar (cTilde / 12) β₀ t)
        atTop (𝓝 0)) ∧
      (∀ β : ℝ, 0 < β →
        Tendsto (fun t => thermalDiff src.w β t / wStar (cTilde / 12) β₀ t) atTop (𝓝 0)) := by
  have ha0 := S.ha_pos
  have hβ₀1 : β₀ < 1 := lt_of_le_of_lt S.hβ₀2 (by norm_num)
  exact ⟨hMaj_mem_TestClass_src ha0 S.hnonneg S.hupper, by simp [dualC0S],
    dualC0S_pos S,
    fun t ht => wStar_le_hMaj src.hw ha0 S.hβ₀ hβ₀1 S.hT₀ ht,
    fun β hβ => exp_le_const_wStar ha0.le S.hβ₀ hβ,
    fun k => tendsto_genLaguerrePsi_div_wStar src.w k ha0.le S.hβ₀,
    fun β hβ => tendsto_thermalDiff_div_wStar ha0.le S.hβ₀ hβ⟩

/-- **Lemma M (`ds:M`) for a `CommonSource`**: at every `c̃ ≥ 12 C.a₀` and `T₀ > 0`, there is
`β₀ ∈ (0, 1/2]` giving `SourceDualSetupCore` and all conclusions of `ds:M`. -/
theorem commonSource_lemma_M (C : CommonSource) {cTilde T₀ : ℝ}
    (hc : 12 * C.a₀ ≤ cTilde) (hT₀pos : 0 < T₀) :
    ∃ β₀ : ℝ, SourceDualSetupCore C.src cTilde β₀ T₀ ∧
      TestClass C.src (cTilde / 12) (hMaj C.src.w (cTilde / 12) β₀) ∧
      C.src.gVac (cTilde / 12) (hMaj C.src.w (cTilde / 12) β₀) =
        -dualC0S C.src (cTilde / 12) β₀ ∧
      0 < dualC0S C.src (cTilde / 12) β₀ ∧
      (∀ t, T₀ ≤ t → wStar (cTilde / 12) β₀ t ≤ hMaj C.src.w (cTilde / 12) β₀ t) ∧
      (∀ β : ℝ, 0 < β → ∃ C₀ : ℝ, 0 < C₀ ∧
        ∀ t, 0 ≤ t → Real.exp (-2 * π * β * t) ≤ C₀ * wStar (cTilde / 12) β₀ t) ∧
      (∀ k : ℕ, Tendsto (fun t => genLaguerrePsi C.src.w k t / wStar (cTilde / 12) β₀ t)
        atTop (𝓝 0)) ∧
      (∀ β : ℝ, 0 < β →
        Tendsto (fun t => thermalDiff C.src.w β t / wStar (cTilde / 12) β₀ t) atTop (𝓝 0)) := by
  obtain ⟨β₀, S⟩ := SourceDualSetupCore.exists_of_common C hc hT₀pos
  exact ⟨β₀, S, lemma_M_src S⟩

/-! ### Constrained finiteness (`T_F < ∞` and `T_V < ∞`) from `FloorData.At` -/

/-- Explicit feasible thermal test `A Ξ_{β₁} - Ξ_{β₂}` for any `SourceDualSetupCore`, showing
`0 ≤ T_V < ∞`. -/
theorem T_V_lt_top_of_core {src : ShiftSource} {cTilde β₀ T₀ : ℝ}
    (S : SourceDualSetupCore src cTilde β₀ T₀) :
    0 ≤ src.T_V cTilde ∧
      ∃ T : ℝ, 0 < T ∧ (∃ g, src.IsFeasible (cTilde / 12) T g) ∧ src.T_V cTilde ≤ T := by
  let a : ℝ := cTilde / 12
  have ha0 : 0 < a := S.ha_pos
  let β₁ : ℝ := β₀ / 2
  let β₂ : ℝ := β₀
  have hβ₁ : 0 < β₁ := half_pos S.hβ₀
  have hβ₁₂ : β₁ < β₂ := half_lt_self S.hβ₀
  have hβ₂ : β₂ < 1 := lt_of_le_of_lt S.hβ₀2 (by norm_num)
  have hv1 : src.gVac a (thermalDiff src.w β₁) < 0 := S.hvac_neg hβ₁ (by linarith [S.hβ₀])
  have hv2 : src.gVac a (thermalDiff src.w β₂) < 0 := S.hvac_neg S.hβ₀ le_rfl
  let A : ℝ := (-src.gVac a (thermalDiff src.w β₂)) / (2 * (-src.gVac a (thermalDiff src.w β₁)))
  have hA_pos : 0 < A := div_pos (by linarith) (by linarith)
  let g : ℝ → ℝ := fun t => A * thermalDiff src.w β₁ t - thermalDiff src.w β₂ t
  have hg_eq : g = fun t => A * thermalDiff src.w β₁ t + (-1) * thermalDiff src.w β₂ t := by
    ext t; ring
  have ht1 : TestClass src a (thermalDiff src.w β₁) :=
    thermalDiff_mem_TestClass_src ha0 S.hnonneg S.hupper hβ₁
  have ht2 : TestClass src a (thermalDiff src.w β₂) :=
    thermalDiff_mem_TestClass_src ha0 S.hnonneg S.hupper S.hβ₀
  have hg_mem : TestClass src a g := by
    rw [hg_eq]
    exact testClass_add_src (testClass_smul_src A ht1) (testClass_smul_src (-1) ht2)
  have hg_vac : 0 < src.gVac a g := by
    rw [hg_eq, gVac_add_src (testClass_smul_src A ht1) (testClass_smul_src (-1) ht2),
      gVac_smul_src A, gVac_smul_src (-1)]
    have hA_mul : A * (-src.gVac a (thermalDiff src.w β₁)) =
        (-src.gVac a (thermalDiff src.w β₂)) / 2 := by
      dsimp [A]; field_simp [hv1.ne]
    linarith
  let c₁ : ℝ := 2 * π * (β₂ - β₁)
  let c₂ : ℝ := 2 * π * (1 / β₁ - β₁)
  have hc₁_pos : 0 < c₁ := by dsimp [c₁]; nlinarith [Real.pi_pos]
  have hc₂_pos : 0 < c₂ := by
    dsimp [c₂]
    have h1 : β₁ < 1 := hβ₁₂.trans hβ₂
    have h2 : 1 < 1 / β₁ := one_lt_one_div hβ₁ h1
    nlinarith [Real.pi_pos]
  let T₁ : ℝ := Real.log (2 / A) / c₁
  let T₂ : ℝ := Real.log (2 * β₁ ^ (-(src.w : ℝ))) / c₂
  let T : ℝ := max 1 (max T₁ T₂)
  have hT_pos : 0 < T := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hg_tail : ∀ t ≥ T, 0 ≤ g t := fun t ht => by
    have hpt1 : T₁ ≤ t := (le_max_left _ _ |>.trans (le_max_right _ _)).trans ht
    have hpt2 : T₂ ≤ t := (le_max_right _ _ |>.trans (le_max_right _ _)).trans ht
    have hexp1 : Real.exp (-2 * π * β₂ * t) ≤ (A / 2) * Real.exp (-2 * π * β₁ * t) := by
      have hlog : Real.log (2 / A) ≤ c₁ * t := by
        have := (div_le_iff₀ hc₁_pos).mp hpt1; linarith
      have hle : 2 / A ≤ Real.exp (c₁ * t) := by
        have := Real.exp_le_exp.mpr hlog; rwa [Real.exp_log (by positivity)] at this
      have hle' : Real.exp (-(c₁ * t)) ≤ A / 2 := by
        rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity)]; simpa [inv_div] using hle
      have eadd : -2 * π * β₂ * t = -2 * π * β₁ * t + -(c₁ * t) := by dsimp [c₁]; ring
      rw [eadd, Real.exp_add]
      calc Real.exp (-2 * π * β₁ * t) * Real.exp (-(c₁ * t))
          ≤ Real.exp (-2 * π * β₁ * t) * (A / 2) := mul_le_mul_of_nonneg_left hle' (Real.exp_pos _).le
        _ = (A / 2) * Real.exp (-2 * π * β₁ * t) := mul_comm _ _
    have hexp2 : β₁ ^ (-(src.w : ℝ)) * Real.exp (-2 * π * t / β₁) ≤
        (1 / 2) * Real.exp (-2 * π * β₁ * t) := by
      have hbw_pos : 0 < β₁ ^ (-(src.w : ℝ)) := Real.rpow_pos_of_pos hβ₁ _
      have hlog : Real.log (2 * β₁ ^ (-(src.w : ℝ))) ≤ c₂ * t := by
        have := (div_le_iff₀ hc₂_pos).mp hpt2; linarith
      have hle : 2 * β₁ ^ (-(src.w : ℝ)) ≤ Real.exp (c₂ * t) := by
        have := Real.exp_le_exp.mpr hlog; rwa [Real.exp_log (by positivity)] at this
      have hle' : β₁ ^ (-(src.w : ℝ)) * Real.exp (-(c₂ * t)) ≤ 1 / 2 := by
        rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]; linarith
      have eadd : -2 * π * t / β₁ = -2 * π * β₁ * t + -(c₂ * t) := by
        dsimp [c₂]; field_simp [hβ₁.ne']; ring
      rw [eadd, Real.exp_add]
      calc β₁ ^ (-(src.w : ℝ)) * (Real.exp (-2 * π * β₁ * t) * Real.exp (-(c₂ * t)))
          = (β₁ ^ (-(src.w : ℝ)) * Real.exp (-(c₂ * t))) * Real.exp (-2 * π * β₁ * t) := by ring
        _ ≤ (1 / 2) * Real.exp (-2 * π * β₁ * t) := mul_le_mul_of_nonneg_right hle' (Real.exp_pos _).le
    have hterm_nn : 0 ≤ β₂ ^ (-(src.w : ℝ)) * Real.exp (-2 * π * t / β₂) :=
      mul_nonneg (Real.rpow_nonneg S.hβ₀.le _) (Real.exp_pos _).le
    dsimp [g]; unfold thermalDiff; nlinarith
  have hg : src.IsFeasible a T g := ⟨hg_mem, hg_vac, hg_tail⟩
  have hne : {T' : ℝ | 0 < T' ∧ ∃ g', src.IsFeasible a T' g'}.Nonempty := ⟨T, hT_pos, g, hg⟩
  exact ⟨by unfold ShiftSource.T_V; exact le_csInf hne fun T' hT' => hT'.1.le,
    T, hT_pos, ⟨g, hg⟩, by unfold ShiftSource.T_V; exact csInf_le ⟨0, fun T' hT' => hT'.1.le⟩ ⟨hT_pos, g, hg⟩⟩

/-- **Constrained finiteness `T_F < ∞`** (`ds:E`(b)): for every compact `F ⊂ (0, ∞)` (possibly empty)
and any `F.At (c̃ / 12)` together with `SourceDualSetupCore`, there are `τ > 0` and
`g ∈ \overline{\mathcal A}` with `g_vac > 0` and `g ≥ 0` on `F ∪ [τ, ∞)`. -/
theorem exists_feasible_src_of_compact {src : ShiftSource} {Fl : FloorData src} {cTilde β₀ T₀ : ℝ}
    (hAt : Fl.At (cTilde / 12)) (S : SourceDualSetupCore src cTilde β₀ T₀)
    {F : Set ℝ} (hFc : IsCompact F) (hF : F ⊆ Ioi 0) :
    ∃ τ : ℝ, 0 < τ ∧ ∃ g, src.IsFeasibleOn (cTilde / 12) (F ∪ Ici τ) g := by
  rcases F.eq_empty_or_nonempty with rfl | hne
  · obtain ⟨-, T, hT, ⟨g, hg⟩, -⟩ := T_V_lt_top_of_core S
    exact ⟨T, hT, g, by rw [empty_union, isFeasibleOn_Ici_iff_src]; exact hg⟩
  set a : ℝ := cTilde / 12 with ha_def
  have ha0 : 0 < a := S.ha_pos
  obtain ⟨m, hmF, hmin⟩ := hFc.exists_isMinOn hne continuous_id.continuousOn
  obtain ⟨R, hRF, hmax⟩ := hFc.exists_isMaxOn hne continuous_id.continuousOn
  have hm : 0 < m := hF hmF
  have hmt : ∀ t ∈ F, m ≤ t := fun t ht => isMinOn_iff.1 hmin t ht
  have htR : ∀ t ∈ F, t ≤ R := fun t ht => isMaxOn_iff.1 hmax t ht
  obtain ⟨b', hb'0, hb'2, hb'm⟩ := exists_beta0 src.w hm
  let b : ℝ := min b' β₀
  have hb0 : 0 < b := lt_min hb'0 S.hβ₀
  have hbβ₀ : b ≤ β₀ := min_le_right _ _
  have hb1 : b < 1 := lt_of_le_of_lt (hbβ₀.trans S.hβ₀2) (by norm_num)
  have ht0b : t0 src.w b ≤ m := by
    calc t0 src.w b ≤ t0 src.w b' := t0_mono src.w hb0 (min_le_left _ _)
          (lt_of_le_of_lt hb'2 (by norm_num))
      _ = t0Star src.w b' := (t0Star_eq_t0 hb'0 (lt_of_le_of_lt hb'2 (by norm_num))).symm
      _ ≤ m := hb'm
  set δ : ℝ := (1 / 2) * Real.exp (-2 * π * b * R) with hδdef
  have hδ : 0 < δ := by positivity
  have hΞb : ∀ t ∈ F, δ ≤ thermalDiff src.w b t := fun t ht => by
    have h1 := two_thermalDiff_ge hb0 hb1 (ht0b.trans (hmt t ht))
    have h2 : Real.exp (-2 * π * b * R) ≤ Real.exp (-2 * π * b * t) := by
      refine Real.exp_le_exp.2 ?_
      have := mul_nonneg (by positivity : 0 ≤ 2 * π * b) (sub_nonneg.mpr (htR t ht))
      linarith
    linarith
  set vb := src.gVac a (thermalDiff src.w b) with hvbdef
  have hvb : vb < 0 := S.hvac_neg hb0 hbβ₀
  have hvb' : 0 < -vb := neg_pos.2 hvb
  set K : ℝ := 2 * (-vb) / δ with hKdef
  have hK : 0 < K := div_pos (by linarith) hδ
  set q₀ := Fl.d * Fl.prob.nullPoly (Real.exp (-2 * π)) with hq₀def
  have hq₀ : 0 < q₀ := mul_pos Fl.hd (Fl.prob.nullPoly_pos (Real.exp_pos _).le
    (Real.exp_lt_one_iff.2 (by nlinarith [Real.pi_pos])))
  have hev1 : ∀ᶠ γ in 𝓝[>] (0 : ℝ), γ ∈ Ioo (0 : ℝ) b := Ioo_mem_nhdsGT hb0
  have hev2 : ∀ᶠ γ in 𝓝[>] (0 : ℝ), (2 * K + src.tv * Real.exp (2 * π * a)) / q₀ ≤
      Real.exp (2 * π * a * γ⁻¹) := by
    have h1 : Tendsto (fun γ : ℝ => 2 * π * a * γ⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
      tendsto_inv_nhdsGT_zero.const_mul_atTop (by positivity)
    exact (Real.tendsto_exp_atTop.comp h1).eventually_ge_atTop _
  obtain ⟨γ, ⟨hγ0, hγb⟩, hγ2⟩ := (hev1.and hev2).exists
  have hγ1 : γ < 1 := hγb.trans hb1
  have hγβ₀ : γ ≤ β₀ := hγb.le.trans hbβ₀
  set vγ := src.gVac a (thermalDiff src.w γ) with hvγdef
  have hvγ : vγ < 0 := S.hvac_neg hγ0 hγβ₀
  set P : ℝ := γ ^ (-(src.w : ℝ)) with hPdef
  have hP : 1 ≤ P := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hγ0 hγ1.le (by simp)
  have hvγK : K * (1 + P) ≤ -vγ := by
    have hlow := neg_gVac_thermalDiff_src_ge hAt hγ0 hγ1.le
    rw [div_eq_mul_inv] at hlow
    have hX : 2 * K + src.tv * Real.exp (2 * π * a) ≤ q₀ * Real.exp (2 * π * a * γ⁻¹) := by
      rw [div_le_iff₀ hq₀] at hγ2
      linarith [mul_comm q₀ (Real.exp (2 * π * a * γ⁻¹))]
    have hX' : 0 ≤ q₀ * Real.exp (2 * π * a * γ⁻¹) - K := by
      have := Real.exp_pos (2 * π * a)
      have := src.tv_nonneg
      nlinarith
    have h3 : q₀ * Real.exp (2 * π * a * γ⁻¹) - K ≤
        P * (q₀ * Real.exp (2 * π * a * γ⁻¹) - K) := le_mul_of_one_le_left hX' hP
    simp only [← hPdef, ← hq₀def] at hlow
    linarith only [hlow, h3, hX]
  set c : ℝ := 2 * (-vb) / (-vγ) with hcdef
  have hc : 0 < c := div_pos (by linarith) (by linarith)
  have hcvγ : c * (-vγ) = 2 * (-vb) := by rw [hcdef, div_mul_cancel₀ _ (neg_pos.2 hvγ).ne']
  have hcP : c * (1 + P) ≤ δ := by
    rw [hcdef, div_mul_eq_mul_div, div_le_iff₀ (neg_pos.2 hvγ)]
    have hKδ : K * δ = 2 * (-vb) := by rw [hKdef, div_mul_cancel₀ _ hδ.ne']
    rw [← hKδ]
    linarith only [mul_le_mul_of_nonneg_left hvγK hδ.le]
  set d : ℝ := γ / 2 with hddef
  have hd0 : 0 < d := by positivity
  have hdγ : d < γ := by linarith
  have hdβ₀ : d ≤ β₀ := hdγ.le.trans hγβ₀
  set vd := src.gVac a (thermalDiff src.w d) with hvddef
  have hvd : vd < 0 := S.hvac_neg hd0 hdβ₀
  set lam : ℝ := (-vb) / (2 * (-vd)) with hlamdef
  have hlam : 0 < lam := div_pos hvb' (by linarith)
  have hvdne : vd ≠ 0 := hvd.ne
  have hlamvd : lam * vd = -((-vb) / 2) := by rw [hlamdef]; field_simp
  obtain ⟨τ₁, hτ₁⟩ := tail_nonneg src.w hd0 hdγ hγb hb1 hc hlam
  set g : ℝ → ℝ := fun t => (thermalDiff src.w b t + (-c) * thermalDiff src.w γ t) +
    lam * thermalDiff src.w d t with hgdef
  have hTb : TestClass src a (thermalDiff src.w b) :=
    thermalDiff_mem_TestClass_src ha0 S.hnonneg S.hupper hb0
  have hTγ : TestClass src a (thermalDiff src.w γ) :=
    thermalDiff_mem_TestClass_src ha0 S.hnonneg S.hupper hγ0
  have hTd : TestClass src a (thermalDiff src.w d) :=
    thermalDiff_mem_TestClass_src ha0 S.hnonneg S.hupper hd0
  have hg : TestClass src a g :=
    testClass_add_src (testClass_add_src hTb (testClass_smul_src (-c) hTγ))
      (testClass_smul_src lam hTd)
  have hgvac : src.gVac a g = (-vb) / 2 := by
    have h1 := gVac_add_src hTb (testClass_smul_src (-c) hTγ)
    have h2 := gVac_add_src (testClass_add_src hTb (testClass_smul_src (-c) hTγ))
      (testClass_smul_src lam hTd)
    rw [gVac_smul_src (-c)] at h1
    rw [h1, gVac_smul_src lam] at h2
    show src.gVac a (fun t => (thermalDiff src.w b t + (-c) * thermalDiff src.w γ t) +
      lam * thermalDiff src.w d t) = _
    rw [h2]
    have : -c * vγ = 2 * (-vb) := by linarith only [hcvγ]
    rw [this]; linarith only [hlamvd]
  have hd_le : t0 src.w d ≤ m :=
    (t0_mono src.w hd0 (hdγ.le.trans hγb.le) hb1).trans ht0b
  refine ⟨max τ₁ 1, lt_of_lt_of_le one_pos (le_max_right _ _), g, hg, ?_, ?_⟩
  · rw [hgvac]; linarith
  · rintro t (ht | ht)
    · have htm := hmt t ht
      have htpos : 0 < t := hm.trans_le htm
      have h1 := hΞb t ht
      have h2 := abs_thermalDiff_le_one_add (w := src.w) hγ0 htpos.le
      have h3 : 0 ≤ thermalDiff src.w d t := by
        have := two_thermalDiff_ge hd0 (hdγ.trans hγ1) (hd_le.trans htm)
        have := Real.exp_pos (-2 * π * d * t); linarith
      have h4 : c * thermalDiff src.w γ t ≤ c * (1 + P) :=
        mul_le_mul_of_nonneg_left ((le_abs_self _).trans h2) hc.le
      show 0 ≤ (thermalDiff src.w b t + (-c) * thermalDiff src.w γ t) + lam * thermalDiff src.w d t
      linarith only [h1, h4, hcP, mul_nonneg hlam.le h3]
    · have := hτ₁ t ((le_max_left τ₁ 1).trans ht)
      show 0 ≤ (thermalDiff src.w b t + (-c) * thermalDiff src.w γ t) + lam * thermalDiff src.w d t
      linarith

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.SourceDualSetupCore.exists_of_common' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SourceDualSetupCore.exists_of_common

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.commonSource_lemma_M' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms commonSource_lemma_M

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.exists_feasible_src_of_compact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_feasible_src_of_compact

end FormalResearch.ModularBootstrap.Mixtures
