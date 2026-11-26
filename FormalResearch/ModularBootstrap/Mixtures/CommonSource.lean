module

public import FormalResearch.ModularBootstrap.Mixtures.Mixture
public import FormalResearch.ModularBootstrap.WeightAxioms.Axioms

/-!
# The common source class and `pmix:weight` (a) (`positive_mixtures.tex`, Lemma PM.2 (a))

The standing class `(H_{w,λ})` of `dual_spectrum.tex` (`ds:source-floor`), for an atomic signed measure `λ`:
a comparison product `Q_0` (`FloorData`: `m` factors `μ_ℓ > 0`, floor constant `d_λ > 0`) such that at the charge `a`
(`FloorData.At`, with `a > 0`, `a ≥ S_λ`, `a ≥ S_0`)
`V_a(t) ≥ d_λ V_{w,Q_0}(a, t)` for all `t > 0`.  `CommonSource` is the class "for all sufficiently large `n = 12 a`"
(`a ≥ a₀`).  A rebased positive mixture is an instance (`MixtureData.floorAt`, `MixtureData.commonSource`), with
`Q_0 = Q_{i_0}`, `d_λ = d_{i_0}` for any unshifted component `i_0` (`r_{i_0} = 0`).

`pmix:weight` (a), proved at every fixed charge with the floor (`pmix_weight_a`):
* Laplace identity `2π ∫ V e^{-2πβt} dt = β^{-w} v(1/β)` (`ShiftSource.cardyV_laplace`);
* sandwich `d_λ V_{w,Q_0} ≤ V ≤ C_up K_a`, `C_up = ‖λ‖_TV` (`C_up = D_tot` for a positive mixture, by
  `MixtureData.toSource_tv`);
* `V > 0` on `(0,∞)`, `V ≥ c_0 t^{m+w-1}`, `V/t^{w-1}` continuous (extends to `0`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Mixtures

open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.WeightAxioms

/-! ### Floor data -/

/-- Comparison product `Q_0` and floor constant of the common source class. -/
structure FloorData (src : ShiftSource) where
  m : ℕ
  μ : Fin m → ℝ
  hμ : ∀ l, 0 < μ l
  d : ℝ
  hd : 0 < d

namespace FloorData

variable {src : ShiftSource} (F : FloorData src)

/-- The comparison product `Q_0` as a fixed-weight problem at the weight of the source. -/
def prob : FixedWeightProblem where
  w := src.w
  hw := src.hw
  m := F.m
  μ := F.μ
  hμ := F.hμ

@[simp] lemma prob_w : F.prob.w = src.w := rfl

@[simp] lemma prob_m : F.prob.m = F.m := rfl

/-- The comparison floor of `ds:source-floor` at the charge `a`: `a > 0`, `a ≥ S_λ`, `a ≥ S_0` and
`V_a ≥ d_λ V_{w,Q_0}(a)` on `(0, ∞)`. -/
structure At (a : ℝ) : Prop where
  pos : 0 < a
  shift : src.ShiftLE a
  prob_shift : F.prob.totalShift ≤ a
  floor : ∀ t : ℝ, 0 < t → F.d * F.prob.cardyV a t ≤ src.cardyV a t

end FloorData

/-- The common source class `(H_{w,λ})` for all sufficiently large charge `a ≥ a₀`. -/
structure CommonSource where
  src : ShiftSource
  F : FloorData src
  a₀ : ℝ
  at_ : ∀ {a : ℝ}, a₀ ≤ a → F.At a

/-! ### `pmix:weight` (a) at a fixed charge -/

namespace FloorData.At

variable {src : ShiftSource} {F : FloorData src} {a : ℝ}

/-- Lower half of the sandwich `(pmix:Vsandwich)`. -/
lemma lower (h : F.At a) {t : ℝ} (ht : 0 < t) : F.d * F.prob.cardyV a t ≤ src.cardyV a t :=
  h.floor t ht

/-- `V > 0` on `(0, ∞)`. -/
lemma pos_V (h : F.At a) {t : ℝ} (ht : 0 < t) : 0 < src.cardyV a t :=
  lt_of_lt_of_le (mul_pos F.hd (F.prob.cardyV_pos h.prob_shift ht)) (h.lower ht)

/-- Upper half of the sandwich: `V ≤ ‖λ‖_TV K_a`. -/
lemma upper (h : F.At a) {t : ℝ} (ht : 0 ≤ t) : src.cardyV a t ≤ src.tv * kernelK src.w a t :=
  src.cardyV_le h.shift ht

/-- `V ≥ 0` on `[0, ∞)` (continuity at `0`). -/
lemma nonneg_V (h : F.At a) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ src.cardyV a t := by
  rcases ht.eq_or_lt with rfl | htp
  · have htend : Tendsto (src.cardyV a) (𝓝[>] 0) (𝓝 (src.cardyV a 0)) :=
      (src.continuous_cardyV a).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto htend ?_
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact (h.pos_V hu).le
  · exact (h.pos_V htp).le

/-- `‖λ‖_TV > 0`. -/
lemma tv_pos (h : F.At a) : 0 < src.tv := by
  have h1 := h.pos_V (zero_lt_one : (0 : ℝ) < 1)
  have h2 := h.upper (zero_le_one' ℝ)
  have hK : 0 ≤ kernelK src.w a 1 := kernelK_nonneg h.pos.le zero_le_one
  by_contra hcon
  have : src.tv = 0 := le_antisymm (not_lt.mp hcon) src.tv_nonneg
  rw [this, zero_mul] at h2
  linarith

/-- **Power-law floor**: `V(t) ≥ c₀ t^{m+w-1}` on `(0, ∞)` (`c₀ = d_λ c_{w,Q_0}`), independent of the charge
among all `a ≥ S_0` for which the floor holds. -/
lemma pow_floor (F : FloorData src) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ {a : ℝ}, F.At a → ∀ {t : ℝ}, 0 < t →
      c₀ * t ^ ((F.m + src.w - 1 : ℕ) : ℝ) ≤ src.cardyV a t := by
  obtain ⟨c_low, hc_low, hfl⟩ := cardyV_small_t_floor F.prob
  refine ⟨F.d * c_low, mul_pos F.hd hc_low, fun {a} h {t} ht => ?_⟩
  have h1 := hfl (a := a) h.prob_shift ht
  have h2 := h.lower ht
  have : F.d * (c_low * t ^ ((F.prob.m + F.prob.w - 1 : ℕ) : ℝ)) ≤ F.d * F.prob.cardyV a t :=
    mul_le_mul_of_nonneg_left h1 F.hd.le
  simp only [prob_m, prob_w] at this
  linarith

end FloorData.At

/-- **`pmix:weight` (a)** (Lemma PM.2 (a)): at a fixed charge with the floor,
(1) the Laplace identity `2π ∫ V e^{-2πβt} dt = β^{-w} v_a(1/β)`;
(2) the sandwich `d_λ V_{w,Q_0}(t) ≤ V(t) ≤ ‖λ‖_TV K_a(t)` on `t > 0`, in particular `V > 0` there;
(3) `V(t) ≥ c₀ t^{m+w-1}`;
(4) `V(t) = t^{w-1} V_red(t)` with `V_red` continuous on `ℝ` (extension to `0` by the convergent power series). -/
theorem pmix_weight_a {src : ShiftSource} (F : FloorData src) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ {a : ℝ}, F.At a →
      (∀ {β : ℝ}, 0 < β →
        IntegrableOn (fun t => src.cardyV a t * Real.exp (-2 * π * β * t)) (Ioi 0) ∧
        2 * π * ∫ t in Ioi 0, src.cardyV a t * Real.exp (-2 * π * β * t) =
          β ^ (-(src.w : ℝ)) * src.srcFun a β⁻¹) ∧
      (∀ {t : ℝ}, 0 < t →
        F.d * F.prob.cardyV a t ≤ src.cardyV a t ∧
          src.cardyV a t ≤ src.tv * kernelK src.w a t ∧ 0 < src.cardyV a t) ∧
      (∀ {t : ℝ}, 0 < t → c₀ * t ^ ((F.m + src.w - 1 : ℕ) : ℝ) ≤ src.cardyV a t) ∧
      (Continuous (src.cardyVReduced a) ∧ ∀ t : ℝ, src.cardyV a t = t ^ (src.w - 1) * src.cardyVReduced a t) := by
  obtain ⟨c₀, hc₀, hfl⟩ := FloorData.At.pow_floor F
  refine ⟨c₀, hc₀, fun {a} h => ⟨fun {β} hβ => src.cardyV_laplace a hβ, fun {t} ht => ⟨h.lower ht,
    h.upper ht.le, h.pos_V ht⟩, fun {t} ht => hfl h ht, src.continuous_cardyVReduced a,
    src.cardyV_eq_pow_mul_reduced a⟩⟩

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.pmix_weight_a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pmix_weight_a

/-! ### Mixtures are common sources -/

namespace MixtureData

variable (M : MixtureData)

/-- `S_max = max_i (r_i + S_i)`, `S_i = ∑_ℓ μ_{i,ℓ}`. -/
noncomputable def Smax : ℝ :=
  Finset.univ.sup' ⟨⟨0, M.hs⟩, Finset.mem_univ _⟩ fun i => M.r i + (M.Q i).totalShift

lemma le_Smax (i : Fin M.s) : M.r i + (M.Q i).totalShift ≤ M.Smax :=
  Finset.le_sup' (fun i => M.r i + (M.Q i).totalShift) (Finset.mem_univ i)

lemma Smax_nonneg : 0 ≤ M.Smax :=
  (add_nonneg (M.hr ⟨0, M.hs⟩) (M.Q ⟨0, M.hs⟩).totalShift_nonneg).trans (M.le_Smax ⟨0, M.hs⟩)

/-- `‖λ‖_TV = D_tot C`-type bound: for a positive mixture the total variation of the flattened measure is
`C_mix = ∑_i d_i ∑_u |c_{i,u}| = ∑_i d_i 2^{m_i}`. -/
theorem toSource_tv : M.toSource.tv = ∑ i, M.d i * 2 ^ (M.m i) := by
  unfold ShiftSource.tv
  rw [M.sum_toSource]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : ∀ S : Finset (Fin (M.Q i).m), |M.toSource.coef ⟨i, S⟩| = M.d i := fun S => by
    show |M.d i * (-1 : ℝ) ^ S.card| = M.d i
    rw [abs_mul, abs_of_pos (M.hd i), abs_pow, abs_neg, abs_one, one_pow, mul_one]
  simp_rw [this]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin, nsmul_eq_mul]
  show (2 ^ (M.Q i).m : ℕ) * M.d i = M.d i * 2 ^ M.m i
  push_cast
  rw [mul_comm]
  rfl

/-- Every shift of the flattened mixture is at most `S_max`. -/
lemma shiftLE_of_Smax {a : ℝ} (ha : M.Smax ≤ a) : M.toSource.ShiftLE a := by
  rintro ⟨i, S⟩
  show M.r i + (M.Q i).shiftSum S ≤ a
  linarith [M.le_Smax i, (M.Q i).shiftSum_le_totalShift S]

/-- Floor data of an unshifted component `i₀` (`r_{i₀} = 0`): `Q_0 = Q_{i₀}`, `d_λ = d_{i₀}`. -/
def floorData (i₀ : Fin M.s) : FloorData M.toSource where
  m := M.m i₀
  μ := M.μ i₀
  hμ := M.hμ i₀
  d := M.d i₀
  hd := M.hd i₀

/-- **A mixture satisfies the floor** (`ds:source-floor`) at every charge `a > 0`, `a ≥ S_max`, with
`Q_0 = Q_{i₀}`, `d_λ = d_{i₀}`, for any component with `r_{i₀} = 0` (e.g. after rebasing). -/
theorem floorAt {i₀ : Fin M.s} (hi₀ : M.r i₀ = 0) {a : ℝ} (ha : 0 < a) (hS : M.Smax ≤ a) :
    (M.floorData i₀).At a where
  pos := ha
  shift := M.shiftLE_of_Smax hS
  prob_shift := by
    have := M.le_Smax i₀
    rw [hi₀, zero_add] at this
    exact this.trans hS
  floor t ht := by
    rw [M.toSource_cardyV a t]
    have hnn : ∀ i, 0 ≤ M.d i * (M.Q i).cardyV (a - M.r i) t := fun i => by
      refine mul_nonneg (M.hd i).le ((M.Q i).cardyV_nonneg ?_ ht.le)
      linarith [M.le_Smax i]
    have hsingle : M.d i₀ * (M.Q i₀).cardyV (a - M.r i₀) t ≤
        ∑ i, M.d i * (M.Q i).cardyV (a - M.r i) t :=
      Finset.single_le_sum (f := fun i => M.d i * (M.Q i).cardyV (a - M.r i) t)
        (fun i _ => hnn i) (Finset.mem_univ i₀)
    rw [hi₀, sub_zero] at hsingle
    exact hsingle

/-- A rebased mixture, for all charges `a ≥ max S_max 1`, is a common source. -/
noncomputable def commonSource {i₀ : Fin M.s} (hi₀ : M.r i₀ = 0) : CommonSource where
  src := M.toSource
  F := M.floorData i₀
  a₀ := max M.Smax 1
  at_ ha := M.floorAt hi₀ (lt_of_lt_of_le one_pos ((le_max_right _ _).trans ha))
    ((le_max_left _ _).trans ha)

end MixtureData

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.MixtureData.floorAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MixtureData.floorAt

end FormalResearch.ModularBootstrap.Mixtures
