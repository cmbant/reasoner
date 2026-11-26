module

public import FormalResearch.ModularBootstrap.FixedWeight.CrossingMeasure
public import FormalResearch.ModularBootstrap.FixedWeight.DualMajorant
public import FormalResearch.ModularBootstrap.FixedWeight.MomentProblem

/-!
# The tests `span{Ξ_β, h}` and exact crossing pairing (`ds:M`(a), `ds:E`(a) (i)⇒(ii))

`dual_spectrum.tex`, Theorem E(a): for a crossing measure `ν` the pairing
`∫ g dν = -g_vac` is *exact* for every `g ∈ span{Ξ_β, h}`, without a terminal ray.  The inputs are

* `abs_hMaj_le` (the decay `|h(t)| ≤ C e^{-4π√(2at)}` of `ds:M`(a), which the Lean `lemma_M` of
  `FixedWeight/DualMajorant` does not record), proved by the AM–GM inequality
  `2πβt + 4πa/β ≥ 4π√(2at)` and the Peano-type bound `β^{-w} e^{-c/β} ≤ (w/c)^w`;
* the absorption of a polynomial factor, `exp_neg_mul_sqrt_le`;
* the crossing equation (Z2) itself for each `Ξ_β` (with integrability from (Z1)).

`spanTest` is the paper's test `Σ_β l_β Ξ_β + μ h`, `NoSpanFeasible` its condition (ii) of `ds:E`(a)
(no such test nonnegative on `X` has `g_vac > 0`), and `crossing_pairing_span` is the exact pairing.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.ModularBootstrap.FixedWeight

open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Duality

/-! ### AM-GM and the decay of `h` -/

lemma amgm_beta {β t a : ℝ} (hβ : 0 < β) (ht : 0 ≤ t) (ha : 0 ≤ a) :
    4 * π * Real.sqrt (2 * a * t) ≤ 2 * π * β * t + 4 * π * a / β := by
  set s := Real.sqrt t with hs
  set A := Real.sqrt (2 * a) with hA
  have hs2 : s ^ 2 = t := Real.sq_sqrt ht
  have hA2 : A ^ 2 = 2 * a := Real.sq_sqrt (by linarith)
  have hsq : Real.sqrt (2 * a * t) = A * s := by rw [Real.sqrt_mul (by linarith)]
  rw [hsq]
  have key : (4 * π * (A * s)) * β ≤ (2 * π * β * t + 4 * π * a / β) * β := by
    have e : (2 * π * β * t + 4 * π * a / β) * β = 2 * π * β ^ 2 * t + 4 * π * a := by
      field_simp
    rw [e]
    have h0 : 4 * π * (A * s) * β ≤ 2 * π * β ^ 2 * s ^ 2 + 2 * π * A ^ 2 := by
      nlinarith [mul_nonneg Real.pi_pos.le (sq_nonneg (β * s - A))]
    rw [hs2, hA2] at h0
    linarith
  exact le_of_mul_le_mul_right key hβ

lemma amgm_two {t a : ℝ} (ht : 0 ≤ t) (ha : 0 ≤ a) :
    4 * π * Real.sqrt (2 * a * t) ≤ 2 * π * t + 4 * π * a := by
  have := amgm_beta (β := 1) one_pos ht ha
  simpa using this

/-- **Decay of the dual majorant** (`ds:M`(a)): `|h(t)| ≤ C e^{-4π√(2at)}` for `t ≥ 0`, with an
explicit constant. -/
lemma abs_hMaj_le {w : ℕ} (hw : 1 ≤ w) {a β₀ : ℝ} (ha : 0 < a) (hβ₀ : 0 < β₀) (hβ₀2 : β₀ ≤ 1 / 2)
    {t : ℝ} (ht : 0 ≤ t) :
    |hMaj w a β₀ t| ≤ 2 * β₀ * (Real.exp (8 * π * a) * (1 + ((w : ℝ) / (2 * π * a)) ^ w)) *
      Real.exp (-4 * π * Real.sqrt (2 * a * t)) := by
  set B : ℝ := Real.exp (8 * π * a) * (1 + ((w : ℝ) / (2 * π * a)) ^ w) *
    Real.exp (-4 * π * Real.sqrt (2 * a * t)) with hB
  have hpt : ∀ β ∈ Ioc (0 : ℝ) β₀, ‖thermalDiff w β t * thetaW a β‖ ≤ B := by
    intro β hβ
    have hβ0 : 0 < β := hβ.1
    have hβ2 : β ≤ 1 / 2 := hβ.2.trans hβ₀2
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (thetaW_pos a β)]
    have hθ := thetaW_eq a β
    have htri := abs_thermalDiff_le (w := w) hβ0 t
    -- part 1
    have h1 : Real.exp (-2 * π * β * t) * thetaW a β ≤
        Real.exp (8 * π * a) * Real.exp (-4 * π * Real.sqrt (2 * a * t)) := by
      rw [hθ]
      have : Real.exp (-2 * π * β * t) * (Real.exp (8 * π * a) * Real.exp (-(4 * π * a) / β)) =
          Real.exp (8 * π * a) * Real.exp (-2 * π * β * t - 4 * π * a / β) := by
        rw [show -2 * π * β * t - 4 * π * a / β = -2 * π * β * t + (-(4 * π * a) / β) by ring,
          Real.exp_add]; ring
      rw [this]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
      have := amgm_beta hβ0 ht ha.le
      linarith
    -- part 2
    have h2 : β ^ (-(w : ℝ)) * Real.exp (-2 * π * t / β) * thetaW a β ≤
        Real.exp (8 * π * a) * (((w : ℝ) / (2 * π * a)) ^ w) *
          Real.exp (-4 * π * Real.sqrt (2 * a * t)) := by
      set c : ℝ := π * t + 2 * π * a with hc
      have hcpos : 0 < c := by positivity
      have hc2 : 2 * π * a ≤ c := by nlinarith [Real.pi_pos]
      have hp := rpow_neg_mul_exp_neg_div_le hw hcpos hβ0
      have hp2 : ((w : ℝ) / c) ^ w ≤ ((w : ℝ) / (2 * π * a)) ^ w := by
        refine pow_le_pow_left₀ (by positivity) ?_ w
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) hc2
      have he : Real.exp (-c / β) ≤ Real.exp (-2 * c) := by
        refine Real.exp_le_exp.2 ?_
        have : 2 ≤ 1 / β := by rw [le_div_iff₀ hβ0]; linarith
        have e : -c / β = -(c * (1 / β)) := by ring
        rw [e]; nlinarith
      have he2 : Real.exp (-2 * c) ≤ Real.exp (-4 * π * Real.sqrt (2 * a * t)) := by
        refine Real.exp_le_exp.2 ?_
        have := amgm_two ht ha.le
        rw [hc]; nlinarith
      have hsplit : β ^ (-(w : ℝ)) * Real.exp (-2 * π * t / β) * thetaW a β =
          Real.exp (8 * π * a) * ((β ^ (-(w : ℝ)) * Real.exp (-c / β)) * Real.exp (-c / β)) := by
        rw [hθ]
        have : Real.exp (-2 * π * t / β) * Real.exp (-(4 * π * a) / β) =
            Real.exp (-c / β) * Real.exp (-c / β) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 1; rw [hc]; field_simp; ring
        calc β ^ (-(w : ℝ)) * Real.exp (-2 * π * t / β) *
              (Real.exp (8 * π * a) * Real.exp (-(4 * π * a) / β))
            = Real.exp (8 * π * a) * (β ^ (-(w : ℝ)) *
                (Real.exp (-2 * π * t / β) * Real.exp (-(4 * π * a) / β))) := by ring
          _ = _ := by rw [this]; ring
      rw [hsplit]
      have : (β ^ (-(w : ℝ)) * Real.exp (-c / β)) * Real.exp (-c / β) ≤
          (((w : ℝ) / (2 * π * a)) ^ w) * Real.exp (-4 * π * Real.sqrt (2 * a * t)) :=
        mul_le_mul (hp.trans hp2) (he.trans he2) (Real.exp_pos _).le (by positivity)
      calc Real.exp (8 * π * a) * ((β ^ (-(w : ℝ)) * Real.exp (-c / β)) * Real.exp (-c / β))
          ≤ Real.exp (8 * π * a) * ((((w : ℝ) / (2 * π * a)) ^ w) *
              Real.exp (-4 * π * Real.sqrt (2 * a * t))) :=
            mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
        _ = _ := by ring
    calc |thermalDiff w β t| * thetaW a β
        ≤ (Real.exp (-2 * π * β * t) + β ^ (-(w : ℝ)) * Real.exp (-2 * π * t / β)) * thetaW a β :=
          mul_le_mul_of_nonneg_right htri (thetaW_pos a β).le
      _ = Real.exp (-2 * π * β * t) * thetaW a β +
          β ^ (-(w : ℝ)) * Real.exp (-2 * π * t / β) * thetaW a β := by ring
      _ ≤ _ := by rw [hB]; nlinarith [h1, h2]
  have hvol : volume.real (Ioc (0 : ℝ) β₀) = β₀ := by
    simp [Measure.real, Real.volume_Ioc, hβ₀.le]
  have hint := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0 : ℝ) β₀)
    (f := fun β => thermalDiff w β t * thetaW a β) (by simp) hpt
  rw [hvol] at hint
  unfold hMaj
  rw [abs_mul, abs_two, ← Real.norm_eq_abs]
  calc 2 * ‖∫ β in Ioc 0 β₀, thermalDiff w β t * thetaW a β‖ ≤ 2 * (B * β₀) :=
        mul_le_mul_of_nonneg_left hint (by norm_num)
    _ = _ := by rw [hB]; ring

/-- Polynomial absorption: `e^{-d √t} ≤ (k!/d^k) e^d (1+t)^{-k/2}`, `d > 0`, `t ≥ 0`. -/
lemma exp_neg_mul_sqrt_le {d : ℝ} (hd : 0 < d) (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-(d * Real.sqrt t)) ≤
      ((k.factorial : ℝ) / d ^ k * Real.exp d) * (1 + t) ^ (-((k : ℝ) / 2)) := by
  have h1t : 1 + t ≤ (1 + Real.sqrt t) ^ 2 := by
    have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht
    nlinarith [Real.sqrt_nonneg t]
  have hpow_le : (1 + t) ^ ((k : ℝ) / 2) ≤ (1 + Real.sqrt t) ^ k := by
    calc (1 + t) ^ ((k : ℝ) / 2) ≤ ((1 + Real.sqrt t) ^ 2) ^ ((k : ℝ) / 2) :=
          Real.rpow_le_rpow (by positivity) h1t (by positivity)
      _ = (1 + Real.sqrt t) ^ (((2 : ℕ) : ℝ) * ((k : ℝ) / 2)) := by
          rw [← Real.rpow_natCast (1 + Real.sqrt t) 2, ← Real.rpow_mul (by positivity)]
      _ = (1 + Real.sqrt t) ^ (k : ℝ) := by
          rw [show ((2 : ℕ) : ℝ) * ((k : ℝ) / 2) = (k : ℝ) by push_cast; ring]
      _ = (1 + Real.sqrt t) ^ k := Real.rpow_natCast _ k
  have hexp_ser : (d * (1 + Real.sqrt t)) ^ k / (k.factorial : ℝ) ≤
      Real.exp (d * (1 + Real.sqrt t)) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    exact (Real.summable_pow_div_factorial _).le_tsum k fun j _ => by positivity
  have hbound1 : (1 + Real.sqrt t) ^ k * Real.exp (-(d * Real.sqrt t)) ≤
      (k.factorial : ℝ) / d ^ k * Real.exp d := by
    have hmul : (1 + Real.sqrt t) ^ k ≤
        (k.factorial : ℝ) / d ^ k * Real.exp (d * (1 + Real.sqrt t)) := by
      rw [mul_pow] at hexp_ser
      have hk_pos : (0 : ℝ) < (k.factorial : ℝ) := by positivity
      have hd_pow_pos : 0 < d ^ k := by positivity
      calc (1 + Real.sqrt t) ^ k
          = ((k.factorial : ℝ) / d ^ k) * (d ^ k * (1 + Real.sqrt t) ^ k / (k.factorial : ℝ)) := by
            field_simp
        _ ≤ ((k.factorial : ℝ) / d ^ k) * Real.exp (d * (1 + Real.sqrt t)) :=
            mul_le_mul_of_nonneg_left hexp_ser (by positivity)
    calc (1 + Real.sqrt t) ^ k * Real.exp (-(d * Real.sqrt t))
        ≤ ((k.factorial : ℝ) / d ^ k * Real.exp (d * (1 + Real.sqrt t))) *
            Real.exp (-(d * Real.sqrt t)) :=
          mul_le_mul_of_nonneg_right hmul (Real.exp_pos _).le
      _ = (k.factorial : ℝ) / d ^ k * Real.exp d := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  have hbound2 : (1 + t) ^ ((k : ℝ) / 2) * Real.exp (-(d * Real.sqrt t)) ≤
      (k.factorial : ℝ) / d ^ k * Real.exp d :=
    (mul_le_mul_of_nonneg_right hpow_le (Real.exp_pos _).le).trans hbound1
  have h1t_pos : 0 < (1 + t) ^ ((k : ℝ) / 2) := Real.rpow_pos_of_pos (by linarith) _
  rw [Real.rpow_neg (by linarith), ← div_eq_mul_inv, le_div_iff₀ h1t_pos]
  linarith [hbound2]

/-- The decay of `h` in the form of the sum-rule hypothesis (`q = (w+2)/2 > (w+1)/2`). -/
lemma hMaj_decay {w : ℕ} (hw : 1 ≤ w) {a β₀ : ℝ} (ha : 0 < a) (hβ₀ : 0 < β₀) (hβ₀2 : β₀ ≤ 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
      |hMaj w a β₀ t| ≤ C * (1 + t) ^ (-(((w + 2 : ℕ) : ℝ) / 2)) *
        Real.exp (-4 * π * Real.sqrt (a * t)) := by
  set k : ℕ := w + 2 with hk
  set d : ℝ := 4 * π * (Real.sqrt 2 - 1) * Real.sqrt a with hd
  have hs2 : 1 < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hdpos : 0 < d := by
    have : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
    have : 0 < Real.sqrt 2 - 1 := by linarith
    positivity
  set C₁ : ℝ := 2 * β₀ * (Real.exp (8 * π * a) * (1 + ((w : ℝ) / (2 * π * a)) ^ w)) with hC₁
  refine ⟨C₁ * ((k.factorial : ℝ) / d ^ k * Real.exp d), by positivity, fun t ht => ?_⟩
  have h1 := abs_hMaj_le hw ha hβ₀ hβ₀2 ht
  have hsq : Real.sqrt (2 * a * t) = Real.sqrt 2 * Real.sqrt a * Real.sqrt t := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num)]
  have hsq' : Real.sqrt (a * t) = Real.sqrt a * Real.sqrt t := Real.sqrt_mul ha.le t
  have hexp : Real.exp (-4 * π * Real.sqrt (2 * a * t)) =
      Real.exp (-(d * Real.sqrt t)) * Real.exp (-4 * π * Real.sqrt (a * t)) := by
    rw [← Real.exp_add, hsq, hsq', hd]; congr 1; ring
  have h2 := exp_neg_mul_sqrt_le hdpos k ht
  calc |hMaj w a β₀ t| ≤ C₁ * Real.exp (-4 * π * Real.sqrt (2 * a * t)) := h1
    _ = C₁ * Real.exp (-(d * Real.sqrt t)) * Real.exp (-4 * π * Real.sqrt (a * t)) := by
        rw [hexp]; ring
    _ ≤ C₁ * (((k.factorial : ℝ) / d ^ k * Real.exp d) * (1 + t) ^ (-((k : ℝ) / 2))) *
          Real.exp (-4 * π * Real.sqrt (a * t)) := by
        gcongr
    _ = _ := by ring_nf

/-! ### The tests `Σ l_β Ξ_β + μ h` and the exact pairing -/

/-- The test `Σ_{β ∈ B} l_β Ξ_β + μ h` of `ds:E`(a) (`h` the dual majorant of `ds:M`). -/
noncomputable def spanTest (w : ℕ) (a β₀ : ℝ) (B : Finset ℝ) (l : ℝ → ℝ) (μ : ℝ) (t : ℝ) : ℝ :=
  ∑ β ∈ B, l β * thermalDiff w β t + μ * hMaj w a β₀ t

lemma spanTest_mem (prob : FixedWeightProblem) {a β₀ : ℝ} (ha : prob.totalShift ≤ a) (ha0 : 0 < a)
    {B : Finset ℝ} (hB : ∀ β ∈ B, 0 < β) (l : ℝ → ℝ) (μ : ℝ) :
    TestClass prob a (spanTest prob.w a β₀ B l μ) :=
  (Duality.testClass_sum (a := a) B l (fun β => thermalDiff prob.w β)
    (fun β hβ => thermalDiff_mem_TestClass prob ha (hB β hβ))).add
    ((hMaj_mem_TestClass prob (β₀ := β₀) ha ha0).smul μ)

/-- `g_vac` of a span test: `-(Σ l_β a_β + μ C₀)`. -/
lemma gVac_spanTest (prob : FixedWeightProblem) {a β₀ : ℝ} (ha : prob.totalShift ≤ a) (ha0 : 0 < a)
    {B : Finset ℝ} (hB : ∀ β ∈ B, 0 < β) (l : ℝ → ℝ) (μ : ℝ) :
    prob.gVac a (spanTest prob.w a β₀ B l μ) =
      -(∑ β ∈ B, l β * crossingRHS prob a β + μ * dualC0 prob a β₀) := by
  have hXi : ∀ β ∈ B, TestClass prob a (thermalDiff prob.w β) := fun β hβ =>
    thermalDiff_mem_TestClass prob ha (hB β hβ)
  have hsum := Duality.testClass_sum (a := a) B l (fun β => thermalDiff prob.w β) hXi
  have hhM := hMaj_mem_TestClass prob (β₀ := β₀) ha ha0
  have := prob.gVac_add hsum (hhM.smul μ)
  rw [prob.gVac_smul μ hhM, Duality.gVac_sum B l _ hXi] at this
  unfold spanTest
  rw [this, hMaj_vac prob ha ha0]
  have hsn : ∑ β ∈ B, l β * prob.gVac a (thermalDiff prob.w β) =
      -∑ β ∈ B, l β * crossingRHS prob a β := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun β _ => by rw [gVac_thermalDiff_eq_neg]; ring
  rw [hsn]; ring

/-- A crossing measure is finite on compact sets (a consequence of (Z1)). -/
theorem _root_.FormalResearch.ModularBootstrap.Crossing.AdmissibleCrossingMeasure.isFiniteMeasureOnCompacts {prob : FixedWeightProblem} {a : ℝ}
    (meas : AdmissibleCrossingMeasure prob a) : IsFiniteMeasureOnCompacts meas.ν := by
  refine ⟨fun K hK => ?_⟩
  obtain ⟨R, hR⟩ := hK.bddAbove
  have hsub : K ⊆ Iio 0 ∪ Icc 0 (max R 0) := by
    intro x hx
    by_cases hx0 : x < 0
    · exact Or.inl hx0
    · exact Or.inr ⟨not_lt.1 hx0, (hR hx).trans (le_max_left _ _)⟩
  refine lt_of_le_of_lt (measure_mono hsub) (lt_of_le_of_lt (measure_union_le _ _) ?_)
  rw [meas.supp_nonneg, zero_add]
  have hint := (meas.finite_laplace one_pos).mono_set
    (Icc_subset_Ici_self : Icc (0 : ℝ) (max R 0) ⊆ Ici 0)
  set ε : ℝ := Real.exp (-2 * π * 1 * max R 0) with hε
  have hεpos : 0 < ε := Real.exp_pos _
  have h1 := hint.measure_norm_ge_lt_top hεpos
  have hset : Icc 0 (max R 0) ⊆ {x | ε ≤ ‖Real.exp (-2 * π * 1 * x)‖} := by
    intro x hx
    simp only [mem_ofPred_eq, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.2 ?_
    nlinarith [Real.pi_pos, hx.2]
  calc meas.ν (Icc 0 (max R 0)) = (meas.ν.restrict (Icc 0 (max R 0))) (Icc 0 (max R 0)) :=
        (Measure.restrict_apply_self _ _).symm
    _ ≤ _ := measure_mono hset
    _ < ⊤ := h1

/-- The integrability and crossing value of `Ξ_β` against a crossing measure. -/
lemma _root_.FormalResearch.ModularBootstrap.Crossing.AdmissibleCrossingMeasure.integrableOn_thermalDiff {prob : FixedWeightProblem} {a : ℝ}
    (meas : AdmissibleCrossingMeasure prob a) {β : ℝ} (hβ : 0 < β) :
    IntegrableOn (thermalDiff prob.w β) (Ici 0) meas.ν := by
  have h1 := meas.finite_laplace hβ
  have h2 := meas.finite_laplace (inv_pos.2 hβ)
  have hdom : IntegrableOn (fun t => Real.exp (-2 * π * β * t) +
      β ^ (-(prob.w : ℝ)) * Real.exp (-2 * π * β⁻¹ * t)) (Ici 0) meas.ν := h1.add (h2.const_mul _)
  refine hdom.mono' (by unfold thermalDiff; fun_prop : Continuous (thermalDiff prob.w β)).aestronglyMeasurable ?_
  refine Eventually.of_forall fun t => ?_
  have := abs_thermalDiff_le (w := prob.w) hβ t
  rw [Real.norm_eq_abs]
  have e : -2 * π * t / β = -2 * π * β⁻¹ * t := by ring
  rw [e] at this
  exact this

/-- **Exact crossing pairing for the span tests** (`ds:E`(a), (i)⇒(ii)): for every crossing
measure `ν` and every `g = Σ l_β Ξ_β + μ h`, `g ∈ L¹(ν)` and `∫ g dν = -g_vac = Σ l_β a_β + μ C₀`
(`gVac_spanTest`), with no terminal-ray assumption. -/
theorem crossing_pairing_span (prob : FixedWeightProblem) {cTilde β₀ : ℝ} (hc_pos : 0 < cTilde)
    (hc : 12 * prob.totalShift ≤ cTilde) (hβ₀ : 0 < β₀) (hβ₀2 : β₀ ≤ 1 / 2)
    (meas : AdmissibleCrossingMeasure prob (cTilde / 12)) {B : Finset ℝ} (hB : ∀ β ∈ B, 0 < β)
    (l : ℝ → ℝ) (μ : ℝ) :
    IntegrableOn (spanTest prob.w (cTilde / 12) β₀ B l μ) (Ici 0) meas.ν ∧
      ∫ t in Ici 0, spanTest prob.w (cTilde / 12) β₀ B l μ t ∂meas.ν =
        ∑ β ∈ B, l β * crossingRHS prob (cTilde / 12) β + μ * dualC0 prob (cTilde / 12) β₀ := by
  have ha : prob.totalShift ≤ cTilde / 12 := by linarith
  have ha0 : 0 < cTilde / 12 := by linarith
  -- the majorant
  obtain ⟨C, hC, hdec⟩ := hMaj_decay prob.hw ha0 hβ₀ hβ₀2
  have hq : (prob.w + 1 : ℝ) / 2 < (((prob.w + 2 : ℕ) : ℝ) / 2) := by push_cast; linarith
  obtain ⟨hhint, hhval⟩ := Duality.proposition_P1 prob ha ha0 meas
    (hMaj_mem_TestClass prob (β₀ := β₀) ha ha0) hq hC hdec
  have hΞint : ∀ β ∈ B, IntegrableOn (fun t => l β * thermalDiff prob.w β t) (Ici 0) meas.ν :=
    fun β hβ => (meas.integrableOn_thermalDiff (hB β hβ)).const_mul _
  have hsumint : IntegrableOn (fun t => ∑ β ∈ B, l β * thermalDiff prob.w β t) (Ici 0) meas.ν :=
    integrable_finsetSum _ hΞint
  refine ⟨hsumint.add (hhint.const_mul μ), ?_⟩
  unfold spanTest
  rw [integral_add hsumint (hhint.const_mul μ), integral_finsetSum _ hΞint, integral_const_mul]
  have hΞ : ∀ β ∈ B, ∫ t in Ici 0, l β * thermalDiff prob.w β t ∂meas.ν =
      l β * crossingRHS prob (cTilde / 12) β := by
    intro β hβ
    rw [integral_const_mul]
    exact congrArg _ (meas.crossing (hB β hβ))
  rw [Finset.sum_congr rfl hΞ]
  have h2 : ∫ t in Ici 0, hMaj prob.w (cTilde / 12) β₀ t ∂meas.ν = dualC0 prob (cTilde / 12) β₀ := by
    have := hMaj_vac prob (β₀ := β₀) ha ha0
    linarith
  rw [h2]

end FormalResearch.ModularBootstrap.FixedWeight
