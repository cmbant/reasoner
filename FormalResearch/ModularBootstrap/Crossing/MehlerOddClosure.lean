module

public import FormalResearch.ModularBootstrap.Crossing.SumRule
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.MeasureTheory.VectorMeasure.IntegrationByParts
public import Mathlib.MeasureTheory.VectorMeasure.WithDensity
public import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# Density of Thermal Differences in the Radial Fourier-Odd `L²` Subspace

Proves that every radial `L¹` function `radialLift w g` with `ContinuousOn g (Ici 0)` and
`𝓕 (radialLift w g) = -(radialLift w g)` lies in the `L²(ℝ^{2w})` closure of finite real
linear combinations of thermal differences `radialLiftReal w (thermalDiff w β)` (`β > 0`).

The proof avoids Hermite/Laguerre orthonormal completeness:
1. Pull back to the radial pushforward measure `μ = Measure.map (fun x => ‖x‖² / 2) volume`.
2. Show `span {exp(-2πβ·) | β > 0}` is dense in `L²(μ)` via Stone–Weierstrass on `[0, 1]`
   and `VectorMeasure.ext_of_Icc` for the Laplace transform at `β = 1 + k`.
3. Push forward into `L²(ℝ^{2w})` and apply the continuous projection `h ↦ (h - 𝓕 h) / 2`,
   using `𝓕(exp(-πβ‖·‖²)) = β^{-w} exp(-π‖·‖²/β)`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real FourierTransform RealInnerProductSpace ENNReal ComplexInnerProductSpace SchwartzMap

namespace FormalResearch.ModularBootstrap.Crossing

section RadialMeasure

/-- Radial coordinate map `x ↦ ‖x‖² / 2` from `RadialSpace w` to `[0, ∞)`. -/
noncomputable def radialQuadMap (w : ℕ) (x : RadialSpace w) : ℝ := ‖x‖ ^ 2 / 2

lemma continuous_radialQuadMap (w : ℕ) : Continuous (radialQuadMap w) :=
  (continuous_norm.pow 2).div_const 2

lemma measurable_radialQuadMap (w : ℕ) : Measurable (radialQuadMap w) :=
  (continuous_radialQuadMap w).measurable

/-- Pushforward of Lebesgue measure on `ℝ^{2w}` along `x ↦ ‖x‖² / 2`. -/
noncomputable def radialMeasure (w : ℕ) : Measure ℝ :=
  Measure.map (radialQuadMap w) volume

lemma measurePreserving_radialQuadMap (w : ℕ) :
    MeasurePreserving (radialQuadMap w) volume (radialMeasure w) :=
  ⟨measurable_radialQuadMap w, rfl⟩

lemma radialMeasure_Iio_zero (w : ℕ) : radialMeasure w (Iio 0) = 0 := by
  unfold radialMeasure
  rw [Measure.map_apply (measurable_radialQuadMap w) measurableSet_Iio]
  have hempty : radialQuadMap w ⁻¹' Iio 0 = ∅ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_empty_iff_false, iff_false, not_lt]
    unfold radialQuadMap
    positivity
  rw [hempty, measure_empty]

lemma ae_nonneg_radialMeasure (w : ℕ) : ∀ᵐ t ∂(radialMeasure w), 0 ≤ t := by
  rw [ae_iff]
  have heq : {t : ℝ | ¬ (0 ≤ t)} = Iio 0 := by ext t; simp
  rw [heq]
  exact radialMeasure_Iio_zero w

instance instSigmaFiniteRadialMeasure (w : ℕ) : SigmaFinite (radialMeasure w) := by
  refine ⟨⟨{
    set := fun n : ℕ => Iic (n : ℝ)
    set_mem := fun _ => trivial
    finite := fun n => by
      unfold radialMeasure
      rw [Measure.map_apply (measurable_radialQuadMap w) measurableSet_Iic]
      have hsub : radialQuadMap w ⁻¹' Iic (n : ℝ) ⊆
          Metric.closedBall (0 : RadialSpace w) (Real.sqrt (2 * (n : ℝ))) := by
        intro x hx
        rw [Metric.mem_closedBall, dist_zero_right]
        have hx' : ‖x‖ ^ 2 ≤ 2 * (n : ℝ) := by
          unfold radialQuadMap at hx
          linarith [Set.mem_Iic.mp hx]
        calc ‖x‖ = Real.sqrt (‖x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg x)).symm
          _ ≤ Real.sqrt (2 * (n : ℝ)) := Real.sqrt_le_sqrt hx'
      exact lt_of_le_of_lt (measure_mono hsub) measure_closedBall_lt_top
    spanning := by
      ext t
      simp only [Set.mem_iUnion, Set.mem_Iic, Set.mem_univ, iff_true]
      exact exists_nat_ge t }⟩⟩

/-- Isometric embedding of `L²(radialMeasure w)` into `L²(RadialSpace w)` by precomposition with
`x ↦ ‖x‖² / 2`. -/
noncomputable def radialLiftLp (w : ℕ) :
    Lp ℂ 2 (radialMeasure w) →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure (RadialSpace w)) where
  toFun := Lp.compMeasurePreserving (radialQuadMap w) (measurePreserving_radialQuadMap w)
  map_add' f g :=
    (Lp.compMeasurePreserving (radialQuadMap w) (measurePreserving_radialQuadMap w)).map_add f g
  map_smul' c f := by
    ext1
    have h1 := Lp.coeFn_compMeasurePreserving (c • f) (measurePreserving_radialQuadMap w)
    have h2 := Lp.coeFn_compMeasurePreserving f (measurePreserving_radialQuadMap w)
    have hsm1 : c • f =ᵐ[radialMeasure w] fun t => c • f t := Lp.coeFn_smul c f
    have hsm1' : (fun x => (c • f) (radialQuadMap w x)) =ᵐ[volume]
        fun x => c • f (radialQuadMap w x) :=
      (measurePreserving_radialQuadMap w).quasiMeasurePreserving.ae hsm1
    have hsm2 : (c • Lp.compMeasurePreserving (radialQuadMap w)
        (measurePreserving_radialQuadMap w) f) =ᵐ[volume]
        fun x => c • (Lp.compMeasurePreserving (radialQuadMap w)
          (measurePreserving_radialQuadMap w) f x) := Lp.coeFn_smul c _
    filter_upwards [h1, hsm1', h2, hsm2] with x hx1 hx_sm hx2 hx_sm2
    simp only [RingHom.id_apply]
    rw [hx1, Function.comp_apply, hx_sm, hx_sm2, hx2, Function.comp_apply]
  norm_map' f := Lp.norm_compMeasurePreserving f (measurePreserving_radialQuadMap w)

end RadialMeasure

section LaplaceDensity

/-- Exponential basis function `t ↦ exp(-2πβt)` in `ℂ` on `[0, ∞)`. -/
noncomputable def expRadial (β t : ℝ) : ℂ :=
  ((Real.exp (-2 * π * β * t) : ℝ) : ℂ)

lemma continuous_expRadial (β : ℝ) : Continuous (expRadial β) := by
  unfold expRadial
  fun_prop

lemma memLp_expRadial_vol (w : ℕ) {β : ℝ} (hβ : 0 < β) :
    MemLp (fun x : RadialSpace w => expRadial β (radialQuadMap w x)) 2 volume := by
  have heq : (fun x : RadialSpace w => expRadial β (radialQuadMap w x)) =
      fun x => ((Real.exp (-π * β * ‖x‖ ^ 2) : ℝ) : ℂ) := by
    ext x
    unfold expRadial radialQuadMap
    congr 2; ring
  rw [heq]
  have hcont : Continuous (fun x : RadialSpace w => ((Real.exp (-π * β * ‖x‖ ^ 2) : ℝ) : ℂ)) := by
    fun_prop
  refine memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable |>.mpr ?_
  have hsq : (fun x : RadialSpace w => ‖((Real.exp (-π * β * ‖x‖ ^ 2) : ℝ) : ℂ)‖ ^ 2) =
      fun x => Real.exp (-π * (2 * β) * ‖x‖ ^ 2) := by
    ext x
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_nat_mul]
    congr 1; push_cast; ring
  rw [hsq]
  exact (integral_exp_neg_pi_mul_norm_sq w (mul_pos two_pos hβ)).1

lemma memLp_expRadial (w : ℕ) {β : ℝ} (hβ : 0 < β) :
    MemLp (expRadial β) 2 (radialMeasure w) :=
  (memLp_map_measure_iff (continuous_expRadial β).aestronglyMeasurable
    (continuous_radialQuadMap w).aemeasurable).mpr (memLp_expRadial_vol w hβ)

/-- Continuous map `t ↦ clamp_{[0,1]}(exp(-2πt))` agreeing with `exp(-2πt)` on `[0, ∞)`. -/
private noncomputable def expClamp (t : ℝ) : Icc (0 : ℝ) 1 :=
  ⟨max 0 (min 1 (Real.exp (-2 * π * t))), le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

private lemma continuous_expClamp : Continuous expClamp := by
  refine Continuous.subtype_mk ?_ _
  exact continuous_const.max (continuous_const.min (by fun_prop))

private lemma expClamp_eq_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    (expClamp t : ℝ) = Real.exp (-2 * π * t) := by
  have h0 : 0 ≤ Real.exp (-2 * π * t) := (Real.exp_pos _).le
  have h1 : Real.exp (-2 * π * t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
  change max 0 (min 1 (Real.exp (-2 * π * t))) = Real.exp (-2 * π * t)
  rw [min_eq_right h1, max_eq_right h0]

private lemma integral_continuous_mul_eq_zero_of_exp_orth (w : ℕ) {h : ℝ → ℂ}
    (hh_int : Integrable h (radialMeasure w))
    (hh_orth : ∀ k : ℕ, ∫ t, (Real.exp (-2 * π * t)) ^ k • h t ∂(radialMeasure w) = 0)
    (ψ : C(Icc (0 : ℝ) 1, ℝ)) :
    ∫ t, ψ (expClamp t) • h t ∂(radialMeasure w) = 0 := by
  have hpoly : ∀ P : Polynomial ℝ,
      ∫ t, P.eval (expClamp t : ℝ) • h t ∂(radialMeasure w) = 0 := by
    intro P
    have heq : (fun t => P.eval (expClamp t : ℝ) • h t) =ᵐ[radialMeasure w]
        fun t => ∑ k ∈ Finset.range (P.natDegree + 1),
          P.coeff k • ((Real.exp (-2 * π * t)) ^ k • h t) := by
      filter_upwards [ae_nonneg_radialMeasure w] with t ht
      rw [expClamp_eq_of_nonneg ht, Polynomial.eval_eq_sum_range, Finset.sum_smul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_smul, mul_comm]
    rw [integral_congr_ae heq]
    have hterm_int : ∀ k : ℕ,
        Integrable (fun t => P.coeff k • ((Real.exp (-2 * π * t)) ^ k • h t)) (radialMeasure w) := by
      intro k
      refine Integrable.smul (P.coeff k) ?_
      have hmeas_k : AEStronglyMeasurable (fun t : ℝ => (Real.exp (-2 * π * t)) ^ k • h t)
          (radialMeasure w) :=
        ((by fun_prop : Continuous fun t : ℝ => Real.exp (-2 * π * t) ^ k).aestronglyMeasurable).smul
          hh_int.1
      refine hh_int.norm.mono' hmeas_k ?_
      filter_upwards [ae_nonneg_radialMeasure w] with t ht
      have hle : Real.exp (-2 * π * t) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
      have hpow_le : |Real.exp (-2 * π * t) ^ k| ≤ 1 := by
        rw [abs_of_nonneg (pow_nonneg (Real.exp_pos _).le k)]
        exact pow_le_one₀ (Real.exp_pos _).le hle
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) hpow_le
    rw [integral_finsetSum _ fun k _ => hterm_int k]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [integral_smul, hh_orth k, smul_zero]
  have hnorm_le : ∀ ε : ℝ, 0 < ε →
      ‖∫ t, ψ (expClamp t) • h t ∂(radialMeasure w)‖ ≤ ε * ∫ t, ‖h t‖ ∂(radialMeasure w) := by
    intro ε hε
    have hmem := continuousMap_mem_polynomialFunctions_closure 0 1 ψ
    obtain ⟨p, hp_mem, hp_dist⟩ := Metric.mem_closure_iff.mp hmem ε hε
    change p ∈ (polynomialFunctions (Icc (0 : ℝ) 1) : Set _) at hp_mem
    rw [polynomialFunctions_coe] at hp_mem
    obtain ⟨P, rfl⟩ := hp_mem
    have hsub_eq : ∫ t, ψ (expClamp t) • h t ∂(radialMeasure w) =
        ∫ t, (ψ (expClamp t) - P.eval (expClamp t : ℝ)) • h t ∂(radialMeasure w) := by
      have hint_ψ : Integrable (fun t => ψ (expClamp t) • h t) (radialMeasure w) := by
        refine (hh_int.norm.const_mul ‖ψ‖).mono'
          (AEStronglyMeasurable.smul (ψ.continuous.comp continuous_expClamp).aestronglyMeasurable hh_int.1) ?_
        filter_upwards with t
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (ContinuousMap.norm_coe_le_norm ψ (expClamp t)) (norm_nonneg _)
      have hint_P : Integrable (fun t => P.eval (expClamp t : ℝ) • h t) (radialMeasure w) := by
        let q : C(Icc (0 : ℝ) 1, ℝ) := Polynomial.toContinuousMapOnAlgHom (Icc (0 : ℝ) 1) P
        have hbd : ∀ s : Icc (0 : ℝ) 1, |P.eval (s : ℝ)| ≤ ‖q‖ := fun s => by
          simpa [q, Real.norm_eq_abs] using ContinuousMap.norm_coe_le_norm q s
        refine (hh_int.norm.const_mul ‖q‖).mono'
          (AEStronglyMeasurable.smul
            ((P.continuous.comp continuous_subtype_val).comp continuous_expClamp).aestronglyMeasurable
            hh_int.1) ?_
        filter_upwards with t
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hbd (expClamp t)) (norm_nonneg _)
      have heq : (fun t => (ψ (expClamp t) - P.eval (expClamp t : ℝ)) • h t) =
          fun t => ψ (expClamp t) • h t - P.eval (expClamp t : ℝ) • h t := by
        ext t; rw [sub_smul]
      rw [heq, integral_sub hint_ψ hint_P, hpoly P, sub_zero]
    rw [hsub_eq]
    have hint_sub : Integrable (fun t => (ψ (expClamp t) - P.eval (expClamp t : ℝ)) • h t)
        (radialMeasure w) := by
      refine (hh_int.norm.const_mul ε).mono'
        (AEStronglyMeasurable.smul
          ((ψ.continuous.comp continuous_expClamp).sub
            ((P.continuous.comp continuous_subtype_val).comp continuous_expClamp)).aestronglyMeasurable
          hh_int.1) ?_
      filter_upwards with t
      rw [norm_smul, Real.norm_eq_abs]
      have hd : |ψ (expClamp t) - P.eval (expClamp t : ℝ)| < ε := by
        have h1 : dist ((Polynomial.toContinuousMapOnAlgHom (Icc (0 : ℝ) 1) P) (expClamp t))
            (ψ (expClamp t)) ≤
            dist (Polynomial.toContinuousMapOnAlgHom (Icc (0 : ℝ) 1) P) ψ :=
          ContinuousMap.dist_apply_le_dist _
        rw [Real.dist_eq, abs_sub_comm] at h1
        exact lt_of_le_of_lt h1 (by rwa [dist_comm] at hp_dist)
      exact mul_le_mul_of_nonneg_right hd.le (norm_nonneg _)
    have hpt : ∀ t, ‖(ψ (expClamp t) - P.eval (expClamp t : ℝ)) • h t‖ ≤ ε * ‖h t‖ := fun t => by
      rw [norm_smul, Real.norm_eq_abs]
      have hd : |ψ (expClamp t) - P.eval (expClamp t : ℝ)| < ε := by
        have h1 : dist ((Polynomial.toContinuousMapOnAlgHom (Icc (0 : ℝ) 1) P) (expClamp t))
            (ψ (expClamp t)) ≤
            dist (Polynomial.toContinuousMapOnAlgHom (Icc (0 : ℝ) 1) P) ψ :=
          ContinuousMap.dist_apply_le_dist _
        rw [Real.dist_eq, abs_sub_comm] at h1
        exact lt_of_le_of_lt h1 (by rwa [dist_comm] at hp_dist)
      exact mul_le_mul_of_nonneg_right hd.le (norm_nonneg _)
    calc ‖∫ t, (ψ (expClamp t) - P.eval (expClamp t : ℝ)) • h t ∂(radialMeasure w)‖
        ≤ ∫ t, ‖(ψ (expClamp t) - P.eval (expClamp t : ℝ)) • h t‖ ∂(radialMeasure w) :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ t, ε * ‖h t‖ ∂(radialMeasure w) :=
          integral_mono hint_sub.norm (hh_int.norm.const_mul ε) hpt
      _ = ε * ∫ t, ‖h t‖ ∂(radialMeasure w) := integral_const_mul _ _
  have hnorm0 : ‖∫ t, ψ (expClamp t) • h t ∂(radialMeasure w)‖ ≤ 0 := by
    let J := ‖∫ t, ψ (expClamp t) • h t ∂(radialMeasure w)‖
    change J ≤ 0
    by_contra hpos
    push Not at hpos
    let I := ∫ t, ‖h t‖ ∂(radialMeasure w)
    have hI_nn : 0 ≤ I := integral_nonneg fun _ => norm_nonneg _
    let ε := J / (2 * (I + 1))
    have hε : 0 < ε := div_pos hpos (by linarith)
    have hle : J ≤ ε * I := hnorm_le ε hε
    have hlt : ε * I < J := by
      dsimp [ε]
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith
    exact lt_irrefl _ (lt_of_le_of_lt hle hlt)
  exact norm_le_zero_iff.mp hnorm0

private lemma ae_eq_zero_of_forall_exp_integral_eq_zero (w : ℕ) {h : ℝ → ℂ}
    (hh_int : Integrable h (radialMeasure w))
    (hh_orth : ∀ k : ℕ, ∫ t, (Real.exp (-2 * π * t)) ^ k • h t ∂(radialMeasure w) = 0) :
    h =ᵐ[radialMeasure w] 0 := by
  have hIcc_nonneg : ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      ∫ t in Icc a b, h t ∂(radialMeasure w) = 0 := by
    intro a b ha hab
    let r₁ : ℝ := Real.exp (-2 * π * b)
    let r₂ : ℝ := Real.exp (-2 * π * a)
    have hr₁₂ : r₁ ≤ r₂ := Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    let K : Set ℝ := Icc r₁ r₂
    have hK_ne : K.Nonempty := ⟨r₁, le_rfl, hr₁₂⟩
    have hK_closed : IsClosed K := isClosed_Icc
    let ψ : ℕ → C(Icc (0 : ℝ) 1, ℝ) := fun n =>
      ⟨fun s => max 0 (1 - (n : ℝ) * Metric.infDist (s : ℝ) K),
        continuous_const.max (continuous_const.sub
          (continuous_const.mul (Metric.continuous_infDist_pt K |>.comp continuous_subtype_val)))⟩
    have hlim : ∀ᵐ t ∂(radialMeasure w),
        Tendsto (fun n : ℕ => ψ n (expClamp t) • h t) atTop
          (𝓝 ((Icc a b).indicator h t)) := by
      filter_upwards [ae_nonneg_radialMeasure w] with t ht
      have hmem_iff : (expClamp t : ℝ) ∈ K ↔ t ∈ Icc a b := by
        rw [expClamp_eq_of_nonneg ht]
        simp only [K, Set.mem_Icc, r₁, r₂, Real.exp_le_exp]
        have h2pi : 0 < 2 * π := by positivity
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨by nlinarith, by nlinarith⟩
        · rintro ⟨h1, h2⟩
          exact ⟨by nlinarith, by nlinarith⟩
      by_cases ht_mem : t ∈ Icc a b
      · have hs_mem : (expClamp t : ℝ) ∈ K := hmem_iff.mpr ht_mem
        have hinf : Metric.infDist (expClamp t : ℝ) K = 0 :=
          (hK_closed.mem_iff_infDist_zero hK_ne).mp hs_mem
        rw [Set.indicator_of_mem ht_mem]
        have hconst : (fun n : ℕ => ψ n (expClamp t) • h t) = fun _ => h t := by
          ext n
          dsimp [ψ]
          rw [hinf, mul_zero, sub_zero, max_eq_right zero_le_one]
          simp only [Complex.ofReal_one, one_mul]
        rw [hconst]
        exact tendsto_const_nhds
      · have hs_nmem : (expClamp t : ℝ) ∉ K := fun hc => ht_mem (hmem_iff.mp hc)
        have hinf_pos : 0 < Metric.infDist (expClamp t : ℝ) K := by
          rcases lt_or_eq_of_le (Metric.infDist_nonneg (x := (expClamp t : ℝ)) (s := K)) with h | h
          · exact h
          · exact absurd ((hK_closed.mem_iff_infDist_zero hK_ne).mpr h.symm) hs_nmem
        rw [Set.indicator_of_notMem ht_mem]
        obtain ⟨N, hN⟩ := exists_nat_gt (1 / Metric.infDist (expClamp t : ℝ) K)
        refine tendsto_atTop_of_eventually_const (i₀ := N) fun n hn => ?_
        have hn_gt : 1 < (n : ℝ) * Metric.infDist (expClamp t : ℝ) K := by
          have h1 : 1 / Metric.infDist (expClamp t : ℝ) K < (n : ℝ) :=
            lt_of_lt_of_le hN (Nat.cast_le.mpr hn)
          rwa [div_lt_iff₀ hinf_pos] at h1
        dsimp [ψ]
        rw [max_eq_left (by linarith)]
        simp only [Complex.ofReal_zero, zero_mul]
    have hbound : ∀ n : ℕ, ∀ᵐ t ∂(radialMeasure w), ‖ψ n (expClamp t) • h t‖ ≤ ‖h t‖ := by
      intro n
      filter_upwards with t
      rw [norm_smul, Real.norm_eq_abs]
      have h0 : 0 ≤ ψ n (expClamp t) := le_max_left _ _
      have h1 : ψ n (expClamp t) ≤ 1 := by
        refine max_le zero_le_one ?_
        have := mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
          (Metric.infDist_nonneg (x := (expClamp t : ℝ)) (s := K))
        linarith
      rw [abs_of_nonneg h0]
      exact mul_le_of_le_one_left (norm_nonneg _) h1
    have htend := tendsto_integral_of_dominated_convergence (fun t => ‖h t‖)
      (fun n => AEStronglyMeasurable.smul
        ((ψ n).continuous.comp continuous_expClamp).aestronglyMeasurable hh_int.1)
      hh_int.norm hbound hlim
    have hzero : (fun n : ℕ => ∫ t, (⇑(ψ n) ∘ expClamp • h) t ∂(radialMeasure w)) = fun _ => 0 := by
      ext n
      simpa [Function.comp_def] using
        integral_continuous_mul_eq_zero_of_exp_orth w hh_int hh_orth (ψ n)
    rw [hzero] at htend
    have heq0 := tendsto_nhds_unique htend tendsto_const_nhds
    rwa [integral_indicator measurableSet_Icc] at heq0
  have hIcc_all : ∀ a b : ℝ, a ≤ b → ∫ t in Icc a b, h t ∂(radialMeasure w) = 0 := by
    intro a b hab
    rcases le_or_gt 0 a with ha | ha
    · exact hIcc_nonneg a b ha hab
    · rcases lt_or_ge b 0 with hb | hb
      · have hzero : radialMeasure w (Icc a b) = 0 :=
          measure_mono_null (fun t ht => Set.mem_Iio.mpr (lt_of_le_of_lt ht.2 hb))
            (radialMeasure_Iio_zero w)
        rw [← Measure.restrict_eq_zero] at hzero
        rw [hzero, integral_zero_measure]
      have heq : (radialMeasure w).restrict (Icc a b) = (radialMeasure w).restrict (Icc 0 b) := by
        refine Measure.restrict_congr_set ?_
        rw [Filter.eventuallyEqSet_iff]
        filter_upwards [ae_nonneg_radialMeasure w] with t ht
        simp only [Set.mem_Icc, eq_iff_iff]
        exact ⟨fun ⟨_, htb⟩ => ⟨ht, htb⟩, fun ⟨_, htb⟩ => ⟨ha.le.trans ht, htb⟩⟩
      rw [heq]
      exact hIcc_nonneg 0 b le_rfl hb
  have hvm : (radialMeasure w).withDensityᵥ h = 0 := by
    refine VectorMeasure.ext_of_Icc _ _ fun a b hab => ?_
    rw [withDensityᵥ_apply hh_int measurableSet_Icc, FunLike.coe_zero, Pi.zero_apply,
      hIcc_all a b hab]
  refine ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite
    (fun _ _ _ => hh_int.integrableOn) fun s hs _ => ?_
  have hs_eq := congrArg (fun v : VectorMeasure ℝ ℂ => v s) hvm
  rw [withDensityᵥ_apply hh_int hs, FunLike.coe_zero, Pi.zero_apply] at hs_eq
  exact hs_eq

/-- The complex span of `{exp(-2πβ·) | β > 0}` is dense in `L²(radialMeasure w)`. -/
theorem expRadialSpan_topologicalClosure_eq_top (w : ℕ) :
    (Submodule.span ℂ { u : Lp ℂ 2 (radialMeasure w) |
      ∃ β > 0, ∃ h : MemLp (expRadial β) 2 (radialMeasure w),
        u = h.toLp (expRadial β) }).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff, eq_bot_iff]
  intro u hu
  rw [Submodule.mem_bot]
  have hu_orth : ∀ β : ℝ, 0 < β →
      ∫ t, expRadial β t * u t ∂(radialMeasure w) = 0 := by
    intro β hβ
    have hmem := memLp_expRadial w hβ
    have hinner := hu (hmem.toLp (expRadial β)) (Submodule.subset_span ⟨β, hβ, hmem, rfl⟩)
    rw [L2.inner_def] at hinner
    have heq : (fun t => @inner ℂ _ _ ((hmem.toLp (expRadial β) : ℝ → ℂ) t) ((u : ℝ → ℂ) t)) =ᵐ[radialMeasure w]
        fun t => expRadial β t * u t := by
      filter_upwards [hmem.coeFn_toLp] with t ht
      rw [ht, RCLike.inner_apply]
      dsimp [expRadial]
      rw [Complex.conj_ofReal, mul_comm]
    rw [integral_congr_ae heq] at hinner
    exact hinner
  let h : ℝ → ℂ := fun t => Real.exp (-2 * π * t) • (u : ℝ → ℂ) t
  have hh_int : Integrable h (radialMeasure w) := by
    have h1 := memLp_expRadial w one_pos
    have h2 : MemLp (u : ℝ → ℂ) 2 (radialMeasure w) := Lp.memLp u
    have hmul := h1.integrable_mul h2
    refine hmul.congr (ae_of_all _ fun t => ?_)
    simp only [h, expRadial, mul_one, Complex.real_smul, Pi.mul_apply]
  have hh_orth : ∀ k : ℕ, ∫ t, (Real.exp (-2 * π * t)) ^ k • h t ∂(radialMeasure w) = 0 := by
    intro k
    have hk_eq : (fun t => (Real.exp (-2 * π * t)) ^ k • h t) =
        fun t => expRadial ((k : ℝ) + 1) t * u t := by
      ext t
      simp only [h, expRadial, Complex.real_smul]
      rw [← Real.exp_nat_mul, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
      congr 3; ring
    rw [hk_eq]
    exact hu_orth ((k : ℝ) + 1) (by positivity)
  have hae := ae_eq_zero_of_forall_exp_integral_eq_zero w hh_int hh_orth
  have hu_ae : (u : ℝ → ℂ) =ᵐ[radialMeasure w] 0 := by
    filter_upwards [hae] with t ht
    simp only [h, Complex.real_smul, Pi.zero_apply, mul_eq_zero] at ht
    rcases ht with hexp | hu0
    · exact absurd (Complex.ofReal_eq_zero.mp hexp) (Real.exp_pos _).ne'
    · exact hu0
  ext1
  exact hu_ae.trans (Lp.coeFn_zero ℂ 2 (radialMeasure w)).symm

end LaplaceDensity

section FourierClosure

/-- Compatibility between the `L¹` pointwise Fourier transform `𝓕 f` and the `L²` Fourier
transform `𝓕 (hf2.toLp f)` when `f ∈ L¹ ∩ L²` and `𝓕 f ∈ L²`. -/
lemma toLp_fourier_eq_of_integrable {w : ℕ} {f : RadialSpace w → ℂ}
    (hf1 : Integrable f) (hf2 : MemLp f 2 volume) (hFf2 : MemLp (𝓕 f) 2 volume) :
    𝓕 (hf2.toLp f) = hFf2.toLp (𝓕 f) := by
  have hdense : DenseRange (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure (RadialSpace w))) :=
    SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top
  refine eq_of_sub_eq_zero ?_
  rw [← @inner_self_eq_zero ℂ]
  let d := 𝓕 (hf2.toLp f) - hFf2.toLp (𝓕 f)
  have hinner_ψ : ∀ ψ : 𝓢(RadialSpace w, ℂ), @inner ℂ _ _ d (ψ.toLp 2 volume) = 0 := by
    intro ψ
    rw [inner_sub_left]
    have h1 : @inner ℂ _ _ (𝓕 (hf2.toLp f)) (ψ.toLp 2 volume) =
        @inner ℂ _ _ (hf2.toLp f) ((𝓕⁻ ψ).toLp 2 volume) := by
      have hinv := (Lp.inner_fourier_eq (hf2.toLp f) (𝓕⁻ (ψ.toLp 2 volume))).symm
      have hpair : 𝓕 (𝓕⁻ (ψ.toLp 2 volume)) = ψ.toLp 2 volume :=
        (Lp.fourierTransformₗᵢ (RadialSpace w) ℂ).apply_symm_apply _
      rw [hpair, SchwartzMap.toLp_fourierInv_eq] at hinv
      exact hinv.symm
    have h2 : @inner ℂ _ _ (hf2.toLp f) ((𝓕⁻ ψ).toLp 2 volume) =
        ∫ x : RadialSpace w, (innerSL ℂ (f x)) (𝓕⁻ (ψ : RadialSpace w → ℂ) x) := by
      rw [L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hf2.coeFn_toLp, (𝓕⁻ ψ).coeFn_toLp 2 volume] with x hx1 hx2
      rw [hx1, hx2, innerSL_apply_apply, SchwartzMap.fourierInv_coe]
    have h3 : ∫ x : RadialSpace w, (innerSL ℂ (f x)) (𝓕⁻ (ψ : RadialSpace w → ℂ) x) =
        ∫ ξ : RadialSpace w, (innerSL ℂ (𝓕 f ξ)) (ψ ξ) := by
      have hsesq := VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip
        (L := innerₗ (RadialSpace w)) (innerSL ℂ) Real.continuous_fourierChar
        continuous_inner hf1 (ψ.integrable (μ := volume))
      have hLflip : -(innerₗ (RadialSpace w)).flip = -(innerₗ (RadialSpace w)) := by
        ext x y; simp
      rw [hLflip] at hsesq
      exact hsesq.symm
    have h4 : ∫ ξ : RadialSpace w, (innerSL ℂ (𝓕 f ξ)) (ψ ξ) =
        @inner ℂ _ _ (hFf2.toLp (𝓕 f)) (ψ.toLp 2 volume) := by
      rw [L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hFf2.coeFn_toLp, ψ.coeFn_toLp 2 volume] with ξ hξ1 hξ2
      rw [hξ1, hξ2, innerSL_apply_apply]
    rw [h1, h2, h3, h4, sub_self]
  have hcont : Continuous (fun y : Lp ℂ 2 (volume : Measure (RadialSpace w)) => @inner ℂ _ _ d y) :=
    continuous_const.inner continuous_id
  have hzero_all : ∀ y : Lp ℂ 2 (volume : Measure (RadialSpace w)), @inner ℂ _ _ d y = 0 :=
    fun y => hdense.induction_on y (isClosed_eq hcont continuous_const) hinner_ψ
  exact hzero_all d

lemma memLp_radialLift_of_fourier_odd {w : ℕ} {g : ℝ → ℝ}
    (hg_int : Integrable (radialLift w g)) (hg_odd : 𝓕 (radialLift w g) = -(radialLift w g)) :
    MemLp (radialLift w g) 2 volume := by
  obtain ⟨_, hbd⟩ := radialLift_bounded_continuous_of_fourier_odd hg_int hg_odd
  let B : ℝ := ∫ y : RadialSpace w, ‖radialLift w g y‖
  have hB_nn : 0 ≤ B := integral_nonneg fun _ => norm_nonneg _
  refine memLp_two_iff_integrable_sq_norm hg_int.1 |>.mpr ?_
  refine (hg_int.norm.const_mul B).mono' (hg_int.1.norm.pow 2) ?_
  filter_upwards with x
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have hx : ‖radialLift w g x‖ ≤ B := by
    dsimp [B]
    simpa [radialLift_eq_ofReal] using hbd x
  calc ‖radialLift w g x‖ ^ 2 = ‖radialLift w g x‖ * ‖radialLift w g x‖ := sq _
    _ ≤ B * ‖radialLift w g x‖ := mul_le_mul_of_nonneg_right hx (norm_nonneg _)

lemma memLp_g_radialMeasure_of_fourier_odd {w : ℕ} {g : ℝ → ℝ}
    (hg_cont : ContinuousOn g (Ici 0)) (hg_int : Integrable (radialLift w g))
    (hg_odd : 𝓕 (radialLift w g) = -(radialLift w g)) :
    MemLp (fun t => (g t : ℂ)) 2 (radialMeasure w) := by
  have hvol := memLp_radialLift_of_fourier_odd hg_int hg_odd
  have hmeas : AEStronglyMeasurable (fun t => (g t : ℂ)) (radialMeasure w) := by
    have hcont_ici : ContinuousOn (fun t => (g t : ℂ)) (Ici 0) :=
      Complex.continuous_ofReal.comp_continuousOn hg_cont
    have hae_meas : AEStronglyMeasurable (fun t => (g t : ℂ))
        ((radialMeasure w).restrict (Ici 0)) :=
      hcont_ici.aestronglyMeasurable measurableSet_Ici
    have hrestrict : (radialMeasure w).restrict (Ici 0) = radialMeasure w := by
      refine Measure.restrict_eq_self_of_ae_mem ?_
      rw [ae_iff]
      have heq : {t : ℝ | t ∉ Ici 0} = Iio 0 := by ext t; simp
      rw [heq]
      exact radialMeasure_Iio_zero w
    rwa [hrestrict] at hae_meas
  exact (memLp_map_measure_iff hmeas (continuous_radialQuadMap w).aemeasurable).mpr hvol

lemma memLp_thermalDiff_vol (w : ℕ) {β : ℝ} (hβ : 0 < β) :
    MemLp (radialLift w (thermalDiff w β)) 2 volume := by
  have h1 := memLp_expRadial_vol w hβ
  have h2 := memLp_expRadial_vol w (inv_pos.mpr hβ)
  let c : ℂ := ((β ^ (-(w : ℝ)) : ℝ) : ℂ)
  have heq : radialLift w (thermalDiff w β) =
      fun x : RadialSpace w => expRadial β (radialQuadMap w x) -
        c • expRadial β⁻¹ (radialQuadMap w x) := by
    ext x
    simp only [c, radialLift, thermalDiff, expRadial, radialQuadMap, div_eq_mul_inv, smul_eq_mul,
      Complex.ofReal_sub, Complex.ofReal_mul]
    congr 2; ring_nf
  rw [heq]
  exact h1.sub (h2.const_smul c)

lemma fourier_expRadial_vol_L2 (w : ℕ) {β : ℝ} (hβ : 0 < β)
    (hmem : MemLp (fun x : RadialSpace w => expRadial β (radialQuadMap w x)) 2 volume) :
    𝓕 (hmem.toLp _) = ((β ^ (-(w : ℝ)) : ℝ) : ℂ) •
      (memLp_expRadial_vol w (inv_pos.mpr hβ)).toLp _ := by
  have hb : 0 < ((π * β : ℝ) : ℂ).re := by simp [Real.pi_pos, hβ]
  have h1 : Integrable (fun x : RadialSpace w => expRadial β (radialQuadMap w x)) := by
    have heq : (fun x : RadialSpace w => expRadial β (radialQuadMap w x)) =
        fun x : RadialSpace w => Complex.exp (-((π * β : ℝ) : ℂ) * (‖x‖ : ℂ) ^ 2) := by
      ext x; unfold expRadial radialQuadMap; rw [Complex.ofReal_exp]; congr 1; push_cast; ring
    rw [heq]
    simpa using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add hb 0 (0 : RadialSpace w)
  have hfour_pt : 𝓕 (fun x : RadialSpace w => expRadial β (radialQuadMap w x)) =
      fun x : RadialSpace w => ((β ^ (-(w : ℝ)) : ℝ) : ℂ) •
        expRadial β⁻¹ (radialQuadMap w x) := by
    ext ξ
    have heq : (fun x : RadialSpace w => expRadial β (radialQuadMap w x)) =
        fun x : RadialSpace w => Complex.exp (-((π * β : ℝ) : ℂ) * (‖x‖ : ℂ) ^ 2) := by
      ext x; unfold expRadial radialQuadMap; rw [Complex.ofReal_exp]; congr 1; push_cast; ring
    rw [heq, fourier_gaussian_innerProductSpace hb ξ]
    have hdim : (Module.finrank ℝ (RadialSpace w) / 2 : ℂ) = (w : ℂ) := by
      rw [finrank_euclideanSpace_fin]; push_cast; ring
    have hpi : ((π : ℝ) : ℂ) / ((π * β : ℝ) : ℂ) = ((β⁻¹ : ℝ) : ℂ) := by
      have hp : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
      have hbc : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ.ne'
      push_cast; field_simp
    rw [hdim, hpi, show (w : ℂ) = ((w : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_cpow (by positivity : 0 ≤ β⁻¹), Real.inv_rpow hβ.le,
      ← Real.rpow_neg hβ.le]
    simp only [smul_eq_mul, expRadial, radialQuadMap]
    rw [Complex.ofReal_exp]
    congr 2; push_cast
    have hpi_ne : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
    have hb_ne : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ.ne'
    field_simp
  let c : ℂ := ((β ^ (-(w : ℝ)) : ℝ) : ℂ)
  have hFf2 : MemLp (𝓕 (fun x : RadialSpace w => expRadial β (radialQuadMap w x))) 2 volume := by
    rw [hfour_pt]
    exact (memLp_expRadial_vol w (inv_pos.mpr hβ)).const_smul c
  rw [toLp_fourier_eq_of_integrable h1 hmem hFf2]
  ext1
  have h_a := hFf2.coeFn_toLp
  have h_b := Lp.coeFn_smul c ((memLp_expRadial_vol w (inv_pos.mpr hβ)).toLp _)
  have h_c := (memLp_expRadial_vol w (inv_pos.mpr hβ)).coeFn_toLp
  filter_upwards [h_a, h_b, h_c] with x hxa hxb hxc
  rw [hxa, hxb, Pi.smul_apply, hxc, hfour_pt]

/-- Every Fourier-odd radial `L¹` function `radialLift w g` lies in the `L²(ℝ^{2w})`
topological closure of the complex span of `thermalDiff w β` (`β > 0`). -/
theorem radialLift_mem_thermalDiffSpan_closure (w : ℕ) {g : ℝ → ℝ}
    (hg_cont : ContinuousOn g (Ici 0)) (hg_int : Integrable (radialLift w g))
    (hg_odd : 𝓕 (radialLift w g) = -(radialLift w g)) :
    (memLp_radialLift_of_fourier_odd hg_int hg_odd).toLp (radialLift w g) ∈
      (Submodule.span ℂ { u : Lp ℂ 2 (volume : Measure (RadialSpace w)) |
        ∃ β > 0, ∃ h : MemLp (radialLift w (thermalDiff w β)) 2 volume,
          u = h.toLp (radialLift w (thermalDiff w β)) }).topologicalClosure := by
  let S_rad : Submodule ℂ (Lp ℂ 2 (volume : Measure (RadialSpace w))) :=
    Submodule.span ℂ { u | ∃ β > 0, ∃ h : MemLp (fun x => expRadial β (radialQuadMap w x)) 2 volume,
      u = h.toLp _ }
  let S_odd : Submodule ℂ (Lp ℂ 2 (volume : Measure (RadialSpace w))) :=
    Submodule.span ℂ { u | ∃ β > 0, ∃ h : MemLp (radialLift w (thermalDiff w β)) 2 volume,
      u = h.toLp _ }
  let fLp : Lp ℂ 2 (volume : Measure (RadialSpace w)) :=
    (memLp_radialLift_of_fourier_odd hg_int hg_odd).toLp (radialLift w g)
  have hfLp_in_rad : fLp ∈ S_rad.topologicalClosure := by
    let gLp : Lp ℂ 2 (radialMeasure w) :=
      (memLp_g_radialMeasure_of_fourier_odd hg_cont hg_int hg_odd).toLp (fun t => (g t : ℂ))
    have hJg : radialLiftLp w gLp = fLp := by
      ext1
      have h1 := Lp.coeFn_compMeasurePreserving gLp (measurePreserving_radialQuadMap w)
      have h2 := (memLp_g_radialMeasure_of_fourier_odd hg_cont hg_int hg_odd).coeFn_toLp
      have h2' := (measurePreserving_radialQuadMap w).quasiMeasurePreserving.ae h2
      have h3 := (memLp_radialLift_of_fourier_odd hg_int hg_odd).coeFn_toLp
      filter_upwards [h1, h2', h3] with x hx1 hx2 hx3
      have hx1' : ((radialLiftLp w gLp : Lp ℂ 2 (volume : Measure (RadialSpace w))) :
          RadialSpace w → ℂ) x = (gLp : ℝ → ℂ) (radialQuadMap w x) := hx1
      rw [hx1', hx2, hx3]
      rfl
    have hgLp_mem := expRadialSpan_topologicalClosure_eq_top w
    have hgLp_cl : gLp ∈ (Submodule.span ℂ { u : Lp ℂ 2 (radialMeasure w) |
        ∃ β > 0, ∃ h : MemLp (expRadial β) 2 (radialMeasure w), u = h.toLp _ }).topologicalClosure := by
      rw [hgLp_mem]; trivial
    have hmap : ∀ u ∈ Submodule.span ℂ { u : Lp ℂ 2 (radialMeasure w) |
        ∃ β > 0, ∃ h : MemLp (expRadial β) 2 (radialMeasure w), u = h.toLp _ },
        radialLiftLp w u ∈ S_rad := by
      intro u hu
      refine Submodule.span_induction ?_ (by simp) (fun _ _ _ _ hx hy => by
          rw [map_add]; exact S_rad.add_mem hx hy)
        (fun c _ _ hx => by rw [map_smul]; exact S_rad.smul_mem c hx) hu
      rintro _ ⟨β, hβ, hmem, rfl⟩
      refine Submodule.subset_span ⟨β, hβ, memLp_expRadial_vol w hβ, ?_⟩
      ext1
      have h1 := Lp.coeFn_compMeasurePreserving (hmem.toLp (expRadial β))
        (measurePreserving_radialQuadMap w)
      have h2 := (measurePreserving_radialQuadMap w).quasiMeasurePreserving.ae hmem.coeFn_toLp
      have h3 := (memLp_expRadial_vol w hβ).coeFn_toLp
      filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
      have hx1' : ((radialLiftLp w (hmem.toLp (expRadial β)) :
          Lp ℂ 2 (volume : Measure (RadialSpace w))) : RadialSpace w → ℂ) x =
          (hmem.toLp (expRadial β) : ℝ → ℂ) (radialQuadMap w x) := hx1
      rw [hx1', hx2, hx3]
    rw [← hJg]
    have hgLp_cl' : (gLp : Lp ℂ 2 (radialMeasure w)) ∈ closure (Submodule.span ℂ { u : Lp ℂ 2 (radialMeasure w) |
        ∃ β > 0, ∃ h : MemLp (expRadial β) 2 (radialMeasure w), u = h.toLp _ } : Set _) :=
      hgLp_cl
    change radialLiftLp w gLp ∈ closure (S_rad : Set _)
    exact closure_mono (by rintro _ ⟨u, hu, rfl⟩; exact hmap u hu)
      (image_closure_subset_closure_image (radialLiftLp w).continuous ⟨gLp, hgLp_cl', rfl⟩)
  let T : Lp ℂ 2 (volume : Measure (RadialSpace w)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (RadialSpace w)) :=
    (1 / 2 : ℂ) • (ContinuousLinearMap.id ℂ _ -
      (Lp.fourierTransformₗᵢ (RadialSpace w) ℂ).toContinuousLinearEquiv.toContinuousLinearMap)
  have hT_map : ∀ u ∈ S_rad, T u ∈ S_odd := by
    intro u hu
    refine Submodule.span_induction ?_ (by simp) (fun _ _ _ _ hx hy => by
        rw [map_add]; exact S_odd.add_mem hx hy)
      (fun c _ _ hx => by rw [map_smul]; exact S_odd.smul_mem c hx) hu
    rintro _ ⟨β, hβ, hmem, rfl⟩
    have hfour_exp := fourier_expRadial_vol_L2 w hβ hmem
    refine S_odd.smul_mem (1 / 2 : ℂ) (Submodule.subset_span ⟨β, hβ, memLp_thermalDiff_vol w hβ, ?_⟩)
    dsimp [T]
    change hmem.toLp _ - 𝓕 (hmem.toLp _) = (memLp_thermalDiff_vol w hβ).toLp _
    rw [hfour_exp]
    ext1
    let c : ℂ := ((β ^ (-(w : ℝ)) : ℝ) : ℂ)
    have h1 := Lp.coeFn_sub (hmem.toLp _) (c • (memLp_expRadial_vol w (inv_pos.mpr hβ)).toLp _)
    have h2 := Lp.coeFn_smul c ((memLp_expRadial_vol w (inv_pos.mpr hβ)).toLp _)
    have h3 := hmem.coeFn_toLp
    have h4 := (memLp_expRadial_vol w (inv_pos.mpr hβ)).coeFn_toLp
    have h5 := (memLp_thermalDiff_vol w hβ).coeFn_toLp
    filter_upwards [h1, h2, h3, h4, h5] with x hx1 hx2 hx3 hx4 hx5
    change _ = ((memLp_thermalDiff_vol w hβ).toLp _ : RadialSpace w → ℂ) x
    rw [hx1, Pi.sub_apply, hx2, Pi.smul_apply, hx3, hx4, hx5]
    simp only [c, radialLift, thermalDiff, expRadial, radialQuadMap, div_eq_mul_inv, smul_eq_mul,
      Complex.ofReal_sub, Complex.ofReal_mul]
    congr 2; ring_nf
  have hT_f : T fLp = fLp := by
    have hFf : 𝓕 fLp = -fLp := by
      change 𝓕 ((memLp_radialLift_of_fourier_odd hg_int hg_odd).toLp (radialLift w g)) = _
      have hFf2 : MemLp (𝓕 (radialLift w g)) 2 volume := by
        rw [hg_odd]; exact (memLp_radialLift_of_fourier_odd hg_int hg_odd).neg
      rw [toLp_fourier_eq_of_integrable hg_int (memLp_radialLift_of_fourier_odd hg_int hg_odd) hFf2]
      ext1
      have h1 := hFf2.coeFn_toLp
      have h2 := Lp.coeFn_neg fLp
      have h3 := (memLp_radialLift_of_fourier_odd hg_int hg_odd).coeFn_toLp
      filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
      rw [hx1, hx2, Pi.neg_apply]
      change 𝓕 (radialLift w g) x = -(fLp : RadialSpace w → ℂ) x
      rw [hg_odd, Pi.neg_apply]
      exact congrArg Neg.neg hx3.symm
    have hT_eq : T fLp = (1 / 2 : ℂ) • (fLp - 𝓕 fLp) := rfl
    rw [hT_eq, hFf, sub_neg_eq_add, ← two_smul ℂ fLp, smul_smul]
    norm_num
  have hres : T fLp ∈ S_odd.topologicalClosure := by
    change T fLp ∈ closure (S_odd : Set _)
    have hfLp_in_rad' : fLp ∈ closure (S_rad : Set _) := hfLp_in_rad
    exact closure_mono (by rintro _ ⟨u, hu, rfl⟩; exact hT_map u hu)
      (image_closure_subset_closure_image T.continuous ⟨fLp, hfLp_in_rad', rfl⟩)
  rwa [hT_f] at hres

private lemma coeFn_finsetSum_Lp {ι : Type*} (s : Finset ι)
    (f : ι → Lp ℂ 2 (volume : Measure (RadialSpace w))) :
    ((∑ i ∈ s, f i : Lp ℂ 2 (volume : Measure (RadialSpace w))) : RadialSpace w → ℂ) =ᵐ[volume]
      fun x => ∑ i ∈ s, (f i : RadialSpace w → ℂ) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa [Pi.zero_def] using Lp.coeFn_zero ℂ 2 (volume : Measure (RadialSpace w))
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (f a) (∑ i ∈ s, f i), ih] with x hx1 hx2
    rw [hx1, Pi.add_apply, hx2, Finset.sum_insert ha]

private lemma lp_sub_norm_sq_eq_integral {w : ℕ}
    (u v : Lp ℂ 2 (volume : Measure (RadialSpace w))) :
    ‖u - v‖ ^ 2 = ∫ x : RadialSpace w, ‖(u : RadialSpace w → ℂ) x - (v : RadialSpace w → ℂ) x‖ ^ 2 := by
  have hsub := Lp.coeFn_sub u v
  have heq_int : (∫ x : RadialSpace w, ‖(u : RadialSpace w → ℂ) x - (v : RadialSpace w → ℂ) x‖ ^ 2) =
      ∫ x : RadialSpace w, ‖((u - v : Lp ℂ 2 (volume : Measure (RadialSpace w))) :
        RadialSpace w → ℂ) x‖ ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [hsub] with x hx
    rw [hx, Pi.sub_apply]
  rw [heq_int]
  have hinner : ‖u - v‖ ^ 2 = (@inner ℂ _ _ (u - v) (u - v)).re := by
    change ‖u - v‖ ^ 2 = RCLike.re (@inner ℂ _ _ (u - v) (u - v))
    rw [inner_self_eq_norm_sq (𝕜 := ℂ)]
  have hint_in : Integrable (fun x : RadialSpace w =>
      @inner ℂ _ _ (((u - v : Lp ℂ 2 (volume : Measure (RadialSpace w))) : RadialSpace w → ℂ) x)
        (((u - v : Lp ℂ 2 (volume : Measure (RadialSpace w))) : RadialSpace w → ℂ) x)) :=
    L2.integrable_inner (u - v) (u - v)
  have hinner2 : (@inner ℂ _ _ (u - v) (u - v)).re =
      ∫ x : RadialSpace w, ‖((u - v : Lp ℂ 2 (volume : Measure (RadialSpace w))) :
        RadialSpace w → ℂ) x‖ ^ 2 := by
    rw [L2.inner_def, ← Complex.reCLM_apply, ← Complex.reCLM.integral_comp_comm hint_in]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    change RCLike.re (@inner ℂ _ _ _ _) = _
    rw [inner_self_eq_norm_sq (𝕜 := ℂ)]
  rw [hinner, hinner2]

private lemma integrable_sq_diff_thermal {w N : ℕ} (c β : Fin N → ℝ) (hβ : ∀ i, 0 < β i)
    {g : ℝ → ℝ} (hg_int : Integrable (radialLift w g))
    (hg_odd : 𝓕 (radialLift w g) = -(radialLift w g)) :
    Integrable (fun x : RadialSpace w =>
      (∑ i : Fin N, c i * radialLiftReal w (thermalDiff w (β i)) x -
        radialLiftReal w g x) ^ 2) := by
  have h1 : MemLp (fun x : RadialSpace w =>
      ∑ i : Fin N, (c i : ℂ) * radialLift w (thermalDiff w (β i)) x) 2 volume :=
    memLp_finsetSum _ fun i _ => (memLp_thermalDiff_vol w (hβ i)).const_mul (c i : ℂ)
  have h2 := memLp_radialLift_of_fourier_odd hg_int hg_odd
  have hsub := h1.sub h2
  have heq : ((fun x : RadialSpace w =>
        ∑ i : Fin N, (c i : ℂ) * radialLift w (thermalDiff w (β i)) x) - radialLift w g) =
      fun x : RadialSpace w =>
        ((∑ i : Fin N, c i * radialLiftReal w (thermalDiff w (β i)) x -
          radialLiftReal w g x : ℝ) : ℂ) := by
    ext x
    simp only [Pi.sub_apply, radialLift_eq_ofReal, Complex.ofReal_sub, Complex.ofReal_sum,
      Complex.ofReal_mul]
  rw [heq] at hsub
  have hmeas : AEStronglyMeasurable (fun x : RadialSpace w =>
      ((∑ i : Fin N, c i * radialLiftReal w (thermalDiff w (β i)) x -
        radialLiftReal w g x : ℝ) : ℂ)) volume := by
    have h1m : AEStronglyMeasurable (fun x : RadialSpace w =>
        ∑ i : Fin N, (c i : ℂ) * radialLift w (thermalDiff w (β i)) x) volume :=
      (by unfold radialLift thermalDiff; fun_prop : Continuous _).aestronglyMeasurable
    rw [← heq]
    exact h1m.sub hg_int.1
  have hint_sq := (memLp_two_iff_integrable_sq_norm hmeas).mp hsub
  refine hint_sq.congr (ae_of_all _ fun x => ?_)
  dsimp only
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- Real `L²` approximation of `radialLiftReal w g` by finite real linear combinations of
`radialLiftReal w (thermalDiff w β)` (`β > 0`). -/
theorem exists_thermalDiff_approx_L2 (w : ℕ) {g : ℝ → ℝ}
    (hg_cont : ContinuousOn g (Ici 0)) (hg_int : Integrable (radialLift w g))
    (hg_odd : 𝓕 (radialLift w g) = -(radialLift w g)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (N : ℕ) (c β : Fin N → ℝ), (∀ i, 0 < β i) ∧
      Integrable (fun x : RadialSpace w =>
        (∑ i : Fin N, c i * radialLiftReal w (thermalDiff w (β i)) x -
          radialLiftReal w g x) ^ 2) ∧
      ∫ x : RadialSpace w,
        (∑ i : Fin N, c i * radialLiftReal w (thermalDiff w (β i)) x -
          radialLiftReal w g x) ^ 2 ≤ δ ^ 2 := by
  have hmem := radialLift_mem_thermalDiffSpan_closure w hg_cont hg_int hg_odd
  change (memLp_radialLift_of_fourier_odd hg_int hg_odd).toLp (radialLift w g) ∈
    ((Submodule.span ℂ { u : Lp ℂ 2 (volume : Measure (RadialSpace w)) |
      ∃ β > 0, ∃ h : MemLp (radialLift w (thermalDiff w β)) 2 volume,
        u = h.toLp (radialLift w (thermalDiff w β)) }).topologicalClosure : Set _) at hmem
  rw [Submodule.topologicalClosure_coe, Metric.mem_closure_iff] at hmem
  obtain ⟨u, hu_span, hu_dist⟩ := hmem δ hδ
  rw [SetLike.mem_coe, Submodule.mem_span_set] at hu_span
  obtain ⟨cF, hcF_supp, hu_sum⟩ := hu_span
  let e : cF.support ≃ Fin cF.support.card := Finset.equivFin cF.support
  have hβ_ex : ∀ j : Fin cF.support.card,
      ∃ β : ℝ, 0 < β ∧ ∃ h : MemLp (radialLift w (thermalDiff w β)) 2 volume,
        (e.symm j : Lp ℂ 2 (volume : Measure (RadialSpace w))) =
          h.toLp (radialLift w (thermalDiff w β)) := fun j =>
    hcF_supp (Finset.coe_mem (e.symm j))
  choose β hβ_pos hmem_β h_eq_β using hβ_ex
  let cC : Fin cF.support.card → ℂ := fun j =>
    cF (e.symm j : Lp ℂ 2 (volume : Measure (RadialSpace w)))
  let c : Fin cF.support.card → ℝ := fun j => (cC j).re
  have hint_diff := integrable_sq_diff_thermal c β hβ_pos hg_int hg_odd
  refine ⟨cF.support.card, c, β, hβ_pos, hint_diff, ?_⟩
  let fLp := (memLp_radialLift_of_fourier_odd hg_int hg_odd).toLp (radialLift w g)
  have hnorm_lt : ‖u - fLp‖ < δ := by rwa [← dist_eq_norm, dist_comm]
  have hnorm_sq : ∫ x : RadialSpace w, ‖(u : RadialSpace w → ℂ) x - (fLp : RadialSpace w → ℂ) x‖ ^ 2 ≤ δ ^ 2 := by
    rw [← lp_sub_norm_sq_eq_integral u fLp]
    exact pow_le_pow_left₀ (norm_nonneg _) hnorm_lt.le 2
  have hu_ae : (u : RadialSpace w → ℂ) =ᵐ[volume] fun x =>
      ∑ i : Fin cF.support.card, cC i * radialLift w (thermalDiff w (β i)) x := by
    have hu_eq : u = ∑ i : Fin cF.support.card,
        cC i • (hmem_β i).toLp (radialLift w (thermalDiff w (β i))) := by
      rw [← hu_sum, Finsupp.sum, ← Finset.sum_coe_sort cF.support, ← Equiv.sum_comp e.symm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← h_eq_β i]
    have hsum_ae : (∑ i : Fin cF.support.card,
        cC i • (hmem_β i).toLp (radialLift w (thermalDiff w (β i))) :
          Lp ℂ 2 (volume : Measure (RadialSpace w))) =ᵐ[volume]
        fun x => ∑ i : Fin cF.support.card, cC i * radialLift w (thermalDiff w (β i)) x := by
      have hs := coeFn_finsetSum_Lp (Finset.univ : Finset (Fin cF.support.card))
        (fun i => cC i • (hmem_β i).toLp (radialLift w (thermalDiff w (β i))))
      have hsm : ∀ i : Fin cF.support.card,
          (cC i • (hmem_β i).toLp (radialLift w (thermalDiff w (β i))) :
            Lp ℂ 2 (volume : Measure (RadialSpace w))) =ᵐ[volume]
          fun x => cC i * radialLift w (thermalDiff w (β i)) x := fun i => by
        filter_upwards [Lp.coeFn_smul (cC i) ((hmem_β i).toLp (radialLift w (thermalDiff w (β i)))),
          (hmem_β i).coeFn_toLp] with x hx1 hx2
        rw [hx1, Pi.smul_apply, hx2, smul_eq_mul]
      have hall := ae_all_iff.mpr hsm
      filter_upwards [hs, hall] with x hxs hxa
      rw [hxs]
      exact Finset.sum_congr rfl fun i _ => hxa i
    rwa [hu_eq]
  have hpt_le : (fun x : RadialSpace w =>
      (∑ i : Fin cF.support.card, c i * radialLiftReal w (thermalDiff w (β i)) x -
        radialLiftReal w g x) ^ 2) ≤ᵐ[volume]
      fun x : RadialSpace w => ‖(u : RadialSpace w → ℂ) x - (fLp : RadialSpace w → ℂ) x‖ ^ 2 := by
    filter_upwards [hu_ae, (memLp_radialLift_of_fourier_odd hg_int hg_odd).coeFn_toLp]
      with x hxu hxf
    rw [hxu, hxf]
    have hre : (∑ i : Fin cF.support.card, c i * radialLiftReal w (thermalDiff w (β i)) x -
        radialLiftReal w g x) =
        ((∑ i : Fin cF.support.card, cC i * radialLift w (thermalDiff w (β i)) x) -
          radialLift w g x).re := by
      simp only [c, Complex.sub_re, Complex.re_sum, Complex.mul_re, radialLift_eq_ofReal,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rw [hre]
    have hre_le : |((∑ i : Fin cF.support.card, cC i * radialLift w (thermalDiff w (β i)) x) -
          radialLift w g x).re| ≤
        ‖(∑ i : Fin cF.support.card, cC i * radialLift w (thermalDiff w (β i)) x) -
          radialLift w g x‖ :=
      Complex.abs_re_le_norm _
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hre_le 2
  have hint_rhs : Integrable (fun x : RadialSpace w =>
      ‖(u : RadialSpace w → ℂ) x - (fLp : RadialSpace w → ℂ) x‖ ^ 2) := by
    have hmem_sub : MemLp (fun x : RadialSpace w => (u : RadialSpace w → ℂ) x -
        (fLp : RadialSpace w → ℂ) x) 2 volume := (Lp.memLp u).sub (Lp.memLp fLp)
    have hmeas_sub : AEStronglyMeasurable (fun x : RadialSpace w => (u : RadialSpace w → ℂ) x -
        (fLp : RadialSpace w → ℂ) x) volume :=
      (Lp.aestronglyMeasurable u).sub (Lp.aestronglyMeasurable fLp)
    exact (memLp_two_iff_integrable_sq_norm hmeas_sub).mp hmem_sub
  exact (integral_mono_ae hint_diff hint_rhs hpt_le).trans hnorm_sq

end FourierClosure

section AxiomChecks

/-- info: 'FormalResearch.ModularBootstrap.Crossing.expRadialSpan_topologicalClosure_eq_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Crossing.expRadialSpan_topologicalClosure_eq_top

/-- info: 'FormalResearch.ModularBootstrap.Crossing.radialLift_mem_thermalDiffSpan_closure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Crossing.radialLift_mem_thermalDiffSpan_closure

/-- info: 'FormalResearch.ModularBootstrap.Crossing.exists_thermalDiff_approx_L2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Crossing.exists_thermalDiff_approx_L2

end AxiomChecks

end FormalResearch.ModularBootstrap.Crossing
