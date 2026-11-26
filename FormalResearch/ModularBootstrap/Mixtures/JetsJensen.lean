module

public import FormalResearch.ModularBootstrap.Mixtures.Jets

/-!
# `pmix:jets`: the Jensen comparison (`pmix:jensen`, analytic core)

`positive_mixtures.tex`, Proposition PM.13, second half: for a rebased positive mixture
`A = ∑ d_i A_i`, `A_i(x) = e^{-4π r_i x} Q_i(e^{-4πx})`, `p_i = d_i A_i(ξ_*)/A(ξ_*)` (`∑ p_i = 1`) and
`f(t) = log(∑ p_i e^{f_i(t)}) ≥ ∑ p_i f_i(t)`, `f_i(t) = log(A_i(x(t))/A_i(ξ_*))`:

* `sum_mul_le_log_sum_exp`, `log_sum_exp_eq_iff`: the finite Jensen inequality for `log ∑ p_i e^{f_i}` and its equality case
  (strict convexity of `exp`);
* `jensen_integral`: the integrated form `∑ p_i ∫ f_i w ≤ ∫ log(∑ p_i e^{f_i}) w` for a positive weight `w`, with equality iff all
  `f_i` coincide on `(0, ∞)` (continuity and `w > 0`);
* `xChart_surj`: `x : [0,∞) → [ξ_*, ∞)` is onto (explicit inverse `t = √(sinh⁴(πx) - 1)`);
* `pmix_jensen`: the statement for `MixtureData` with `w(t) = 1/t²` (`∫ f/t²` is the integrated-by-parts `I₁`), equality iff the
  normalised component amplitudes `A_i/A_i(ξ_*)` coincide on `[ξ_*, ∞)`.

Not here: the identification of `∫ f/t²` (via `I₁(A) = ∫ ℓ`) with the exact boundary minimum `j(w, A)`, see `Jets.lean`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Mixtures

open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing

section Finite

variable {ι : Type*} [Fintype ι]

lemma nonempty_of_sum_eq_one {p : ι → ℝ} (hs : ∑ i, p i = 1) : Nonempty ι := by
  by_contra h
  rw [not_nonempty_iff] at h
  simp at hs

/-- Finite Jensen: `∑ p_i f_i ≤ log ∑ p_i e^{f_i}`. -/
lemma sum_mul_le_log_sum_exp {p : ι → ℝ} (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1) (f : ι → ℝ) :
    ∑ i, p i * f i ≤ Real.log (∑ i, p i * Real.exp (f i)) := by
  have := nonempty_of_sum_eq_one hs
  have hpos : 0 < ∑ i, p i * Real.exp (f i) :=
    Finset.sum_pos (fun i _ => mul_pos (hp i) (Real.exp_pos _)) Finset.univ_nonempty
  rw [Real.le_log_iff_exp_le hpos]
  have := convexOn_exp.map_sum_le (t := Finset.univ) (w := p) (p := f) (fun i _ => (hp i).le) hs
    (fun _ _ => Set.mem_univ _)
  simpa [smul_eq_mul] using this

/-- Equality case of the finite Jensen inequality: all `f_i` coincide. -/
lemma log_sum_exp_eq_iff {p : ι → ℝ} (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1) (f : ι → ℝ) :
    Real.log (∑ i, p i * Real.exp (f i)) = ∑ i, p i * f i ↔ ∀ i j, f i = f j := by
  have := nonempty_of_sum_eq_one hs
  have hpos : 0 < ∑ i, p i * Real.exp (f i) :=
    Finset.sum_pos (fun i _ => mul_pos (hp i) (Real.exp_pos _)) Finset.univ_nonempty
  constructor
  · intro h
    have h1 : ∑ i, p i * Real.exp (f i) = Real.exp (∑ i, p i * f i) := by
      rw [← h, Real.exp_log hpos]
    have h2 := (strictConvexOn_exp.map_sum_eq_iff (t := Finset.univ) (w := p) (p := f)
      (fun i _ => hp i) hs (fun _ _ => Set.mem_univ _)).1 (by simpa [smul_eq_mul] using h1.symm)
    intro i j
    rw [h2 i (Finset.mem_univ _), h2 j (Finset.mem_univ _)]
  · intro h
    obtain ⟨i₀⟩ := this
    have hc : ∀ i, f i = f i₀ := fun i => h i i₀
    have e1 : ∑ i, p i * f i = f i₀ := by
      simp_rw [hc, ← Finset.sum_mul, hs, one_mul]
    have e2 : ∑ i, p i * Real.exp (f i) = Real.exp (f i₀) := by
      simp_rw [hc, ← Finset.sum_mul, hs, one_mul]
    rw [e1, e2, Real.log_exp]

end Finite

section Integral

variable {ι : Type*} [Fintype ι]

/-- **Integrated Jensen** against a positive weight, with its equality case. -/
theorem jensen_integral {p : ι → ℝ} (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1) {f : ι → ℝ → ℝ}
    (hfc : ∀ i, ContinuousOn (f i) (Ioi 0)) {wt : ℝ → ℝ} (hwt : ∀ t, 0 < t → 0 < wt t)
    (hwc : ContinuousOn wt (Ioi 0))
    (hint : ∀ i, IntegrableOn (fun t => f i t * wt t) (Ioi 0))
    (hintlog : IntegrableOn (fun t => Real.log (∑ i, p i * Real.exp (f i t)) * wt t) (Ioi 0)) :
    ∑ i, p i * ∫ t in Ioi 0, f i t * wt t ≤
        ∫ t in Ioi 0, Real.log (∑ i, p i * Real.exp (f i t)) * wt t ∧
      (∑ i, p i * ∫ t in Ioi 0, f i t * wt t =
          ∫ t in Ioi 0, Real.log (∑ i, p i * Real.exp (f i t)) * wt t ↔
        ∀ i j, ∀ t ∈ Ioi (0 : ℝ), f i t = f j t) := by
  have := nonempty_of_sum_eq_one hs
  set L : ℝ → ℝ := fun t => Real.log (∑ i, p i * Real.exp (f i t)) with hL
  set G : ℝ → ℝ := fun t => ∑ i, p i * f i t with hG
  have hGint : IntegrableOn (fun t => G t * wt t) (Ioi 0) := by
    have : (fun t => G t * wt t) = fun t => ∑ i, p i * (f i t * wt t) := by
      ext t; simp only [hG, Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [this]
    exact integrable_finsetSum _ fun i _ => (hint i).const_mul _
  have hGeq : ∑ i, p i * ∫ t in Ioi 0, f i t * wt t = ∫ t in Ioi 0, G t * wt t := by
    have : (fun t => G t * wt t) = fun t => ∑ i, p i * (f i t * wt t) := by
      ext t; simp only [hG, Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, integral_finsetSum _ fun i _ => (hint i).const_mul _]
    exact Finset.sum_congr rfl fun i _ => (integral_const_mul _ _).symm
  have hpt : ∀ t ∈ Ioi (0 : ℝ), G t * wt t ≤ L t * wt t := fun t ht =>
    mul_le_mul_of_nonneg_right (sum_mul_le_log_sum_exp hp hs fun i => f i t) (hwt t ht).le
  have hmono : ∫ t in Ioi 0, G t * wt t ≤ ∫ t in Ioi 0, L t * wt t :=
    setIntegral_mono_on hGint hintlog measurableSet_Ioi hpt
  rw [hGeq]
  refine ⟨hmono, ⟨fun heq => ?_, fun hall => ?_⟩⟩
  · -- equality of the integrals forces pointwise equality
    have hd_int : IntegrableOn (fun t => (L t - G t) * wt t) (Ioi 0) := by
      have : (fun t => (L t - G t) * wt t) = fun t => L t * wt t - G t * wt t := by
        ext t; ring
      rw [this]; exact hintlog.sub hGint
    have hd0 : ∫ t in Ioi 0, (L t - G t) * wt t = 0 := by
      have : (fun t => (L t - G t) * wt t) = fun t => L t * wt t - G t * wt t := by
        ext t; ring
      rw [this, integral_sub hintlog hGint, heq, sub_self]
    have hdnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun t => (L t - G t) * wt t := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have := hpt t ht
      show (0 : ℝ) ≤ (L t - G t) * wt t
      rw [sub_mul]
      linarith
    have hae := (setIntegral_eq_zero_iff_of_nonneg_ae hdnn hd_int).1 hd0
    have hcontL : ContinuousOn L (Ioi 0) := by
      refine ContinuousOn.log ?_ fun t _ => ?_
      · exact continuousOn_finsetSum _ fun i _ =>
          continuousOn_const.mul (Real.continuous_exp.comp_continuousOn (hfc i))
      · exact (Finset.sum_pos (fun i _ => mul_pos (hp i) (Real.exp_pos _))
          Finset.univ_nonempty).ne'
    have hcontG : ContinuousOn G (Ioi 0) :=
      continuousOn_finsetSum _ fun i _ => continuousOn_const.mul (hfc i)
    have hcontd : ContinuousOn (fun t => (L t - G t) * wt t) (Ioi 0) :=
      (hcontL.sub hcontG).mul hwc
    have heqOn := Measure.eqOn_open_of_ae_eq hae isOpen_Ioi hcontd continuousOn_const
    intro i j t ht
    have h0 : (L t - G t) * wt t = 0 := heqOn ht
    have h1 : L t - G t = 0 := by
      rcases mul_eq_zero.1 h0 with h | h
      · exact h
      · exact absurd h (hwt t ht).ne'
    exact (log_sum_exp_eq_iff hp hs fun i => f i t).1 (by simp only [hL, hG] at h1; linarith) i j
  · refine le_antisymm hmono ?_
    refine (setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_).ge
    have := (log_sum_exp_eq_iff hp hs fun i => f i t).2 fun i j => hall i j t ht
    show G t * wt t = Real.log (∑ i, p i * Real.exp (f i t)) * wt t
    rw [this]

end Integral

/-! ### The chart is onto `[ξ_*, ∞)` -/

lemma sinh_pi_mul_ge_one {x : ℝ} (hx : xiStar ≤ x) : 1 ≤ Real.sinh (π * x) := by
  have h1 : Real.arsinh 1 ≤ π * x := by
    have := mul_le_mul_of_nonneg_left hx Real.pi_pos.le
    have e : π * xiStar = Real.arsinh 1 := by unfold xiStar; field_simp
    linarith
  have := Real.sinh_le_sinh.2 h1
  rwa [Real.sinh_arsinh] at this

/-- Every `x ≥ ξ_*` is `x(t)` for some `t ≥ 0` (`t = √(sinh⁴(πx) - 1)`). -/
lemma xChart_surj {x : ℝ} (hx : xiStar ≤ x) : ∃ t : ℝ, 0 ≤ t ∧ xChart t = x := by
  have hs := sinh_pi_mul_ge_one hx
  set s : ℝ := Real.sinh (π * x) with hs_def
  have hs4 : 1 ≤ s ^ 4 := one_le_pow₀ hs
  refine ⟨Real.sqrt (s ^ 4 - 1), Real.sqrt_nonneg _, ?_⟩
  have hq : qChart (Real.sqrt (s ^ 4 - 1)) = s ^ 2 := by
    unfold qChart
    rw [Real.sq_sqrt (by linarith), show 1 + (s ^ 4 - 1) = (s ^ 2) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  unfold xChart
  rw [hq, Real.sqrt_sq (by linarith), hs_def, Real.arsinh_sinh]
  field_simp

/-! ### The Jensen comparison for a mixture -/

namespace MixtureData

variable (M : MixtureData)

/-- The component amplitude `A_i(x) = e^{-4π r_i x} Q_i(e^{-4πx})`. -/
noncomputable def compAmp (i : Fin M.s) (x : ℝ) : ℝ :=
  Real.exp (-4 * π * M.r i * x) * (M.Q i).nullPoly (Real.exp (-4 * π * x))

lemma compAmp_pos (i : Fin M.s) {x : ℝ} (hx : 0 < x) : 0 < M.compAmp i x := by
  unfold compAmp
  refine mul_pos (Real.exp_pos _) ((M.Q i).nullPoly_pos (Real.exp_pos _).le ?_)
  exact Real.exp_lt_one_iff.2 (by nlinarith [Real.pi_pos])

lemma continuous_compAmp (i : Fin M.s) : Continuous (M.compAmp i) := by
  unfold compAmp
  refine (Real.continuous_exp.comp (by fun_prop)).mul ?_
  have hc : Continuous (M.Q i).nullPoly := by
    unfold FixedWeightProblem.nullPoly
    exact continuous_finsetProd _ fun l _ =>
      continuous_const.sub (Real.continuous_rpow_const ((M.Q i).hμ l).le)
  exact hc.comp (Real.continuous_exp.comp (by fun_prop))

lemma ampl_eq_sum (x : ℝ) : M.toSource.ampl x = ∑ i, M.d i * M.compAmp i x := by
  rw [M.toSource_ampl]
  exact Finset.sum_congr rfl fun i _ => by unfold compAmp; ring

lemma ampl_xi_pos : 0 < M.toSource.ampl xiStar := by
  rw [M.ampl_eq_sum]
  exact Finset.sum_pos (fun i _ => mul_pos (M.hd i) (M.compAmp_pos i xiStar_pos))
    ⟨⟨0, M.hs⟩, Finset.mem_univ _⟩

/-- The Jensen weights `p_i = d_i A_i(ξ_*) / A(ξ_*)`. -/
noncomputable def jensenWeight (i : Fin M.s) : ℝ := M.d i * M.compAmp i xiStar / M.toSource.ampl xiStar

lemma jensenWeight_pos (i : Fin M.s) : 0 < M.jensenWeight i :=
  div_pos (mul_pos (M.hd i) (M.compAmp_pos i xiStar_pos)) M.ampl_xi_pos

lemma sum_jensenWeight : ∑ i, M.jensenWeight i = 1 := by
  unfold jensenWeight
  rw [← Finset.sum_div, ← M.ampl_eq_sum]
  exact div_self M.ampl_xi_pos.ne'

end MixtureData

/-- `F_A(t) = log (A(x(t)) / A(ξ_*))` (`f` of `pmix:f-ell`). -/
noncomputable def logAmp (A : ℝ → ℝ) (t : ℝ) : ℝ := Real.log (A (xChart t) / A xiStar)

lemma continuous_xChart : Continuous xChart :=
  continuous_iff_continuousAt.2 fun t => (xChart_hasDerivAt t).continuousAt

namespace MixtureData

variable (M : MixtureData)

lemma exp_logAmp_comp (i : Fin M.s) (t : ℝ) :
    Real.exp (logAmp (M.compAmp i) t) = M.compAmp i (xChart t) / M.compAmp i xiStar := by
  unfold logAmp
  exact Real.exp_log (div_pos (M.compAmp_pos i (xiStar_pos.trans_le (xiStar_le_xChart t)))
    (M.compAmp_pos i xiStar_pos))

/-- `f = log ∑ p_i e^{f_i}`. -/
lemma logAmp_mixture (t : ℝ) :
    logAmp M.toSource.ampl t =
      Real.log (∑ i, M.jensenWeight i * Real.exp (logAmp (M.compAmp i) t)) := by
  have hsum : ∑ i, M.jensenWeight i * Real.exp (logAmp (M.compAmp i) t) =
      M.toSource.ampl (xChart t) / M.toSource.ampl xiStar := by
    simp_rw [M.exp_logAmp_comp]
    rw [M.ampl_eq_sum (xChart t), Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h := (M.compAmp_pos i xiStar_pos).ne'
    unfold jensenWeight
    field_simp
  rw [hsum]
  rfl

lemma continuousOn_logAmp_comp (i : Fin M.s) : ContinuousOn (logAmp (M.compAmp i)) (Ioi 0) := by
  unfold logAmp
  refine ContinuousOn.log ?_ fun t _ => ?_
  · exact (((M.continuous_compAmp i).comp continuous_xChart).div_const _).continuousOn
  · exact (div_pos (M.compAmp_pos i (xiStar_pos.trans_le (xiStar_le_xChart t)))
      (M.compAmp_pos i xiStar_pos)).ne'

/-- **`pmix:jets`, the Jensen comparison** (`pmix:jensen`, analytic core).  With the Jensen weights `p_i`,
`∑ p_i ∫₀^∞ F_i/t² dt ≤ ∫₀^∞ F_A/t² dt` (`F_i = log(A_i(x(t))/A_i(ξ_*))`, `F_A = log(A(x(t))/A(ξ_*))`; `∫ F/t²` is the
integrated-by-parts form of `I₁`), with equality iff the normalised component amplitudes `A_i/A_i(ξ_*)` coincide on
`[ξ_*, ∞)`.  The integrability of the integrands is hypothesised (`F = O(t²)` at `0`, growth `O(1 + log t)` at `∞`
in the paper). -/
theorem pmix_jensen
    (hint : ∀ i, IntegrableOn (fun t => logAmp (M.compAmp i) t / t ^ 2) (Ioi 0))
    (hintA : IntegrableOn (fun t => logAmp M.toSource.ampl t / t ^ 2) (Ioi 0)) :
    ∑ i, M.jensenWeight i * ∫ t in Ioi 0, logAmp (M.compAmp i) t / t ^ 2 ≤
        ∫ t in Ioi 0, logAmp M.toSource.ampl t / t ^ 2 ∧
      (∑ i, M.jensenWeight i * ∫ t in Ioi 0, logAmp (M.compAmp i) t / t ^ 2 =
          ∫ t in Ioi 0, logAmp M.toSource.ampl t / t ^ 2 ↔
        ∀ i j, ∀ x : ℝ, xiStar ≤ x →
          M.compAmp i x / M.compAmp i xiStar = M.compAmp j x / M.compAmp j xiStar) := by
  have hdiv : ∀ g : ℝ → ℝ, (fun t => g t * (1 / t ^ 2)) = fun t => g t / t ^ 2 := fun g => by
    ext t; ring
  have hwt : ∀ t : ℝ, 0 < t → 0 < 1 / t ^ 2 := fun t ht => by positivity
  have hwc : ContinuousOn (fun t : ℝ => 1 / t ^ 2) (Ioi 0) :=
    continuousOn_const.div (continuousOn_id.pow 2) fun t ht => by
      have : 0 < t := ht
      positivity
  have hint' : ∀ i, IntegrableOn (fun t => logAmp (M.compAmp i) t * (1 / t ^ 2)) (Ioi 0) := fun i => by
    rw [hdiv]; exact hint i
  have hintlog : IntegrableOn (fun t => Real.log (∑ i, M.jensenWeight i *
      Real.exp (logAmp (M.compAmp i) t)) * (1 / t ^ 2)) (Ioi 0) := by
    have : (fun t => Real.log (∑ i, M.jensenWeight i * Real.exp (logAmp (M.compAmp i) t)) *
        (1 / t ^ 2)) = fun t => logAmp M.toSource.ampl t / t ^ 2 := by
      ext t; rw [← M.logAmp_mixture t]; ring
    rw [this]; exact hintA
  obtain ⟨hle, hiff⟩ := jensen_integral (fun i => M.jensenWeight_pos i) M.sum_jensenWeight
    (fun i => M.continuousOn_logAmp_comp i) hwt hwc hint' hintlog
  have hrhs : (fun t => Real.log (∑ i, M.jensenWeight i * Real.exp (logAmp (M.compAmp i) t)) *
      (1 / t ^ 2)) = fun t => logAmp M.toSource.ampl t / t ^ 2 := by
    ext t; rw [← M.logAmp_mixture t]; ring
  have e1 : ∀ i, (∫ t in Ioi (0 : ℝ), logAmp (M.compAmp i) t * (1 / t ^ 2)) =
      ∫ t in Ioi (0 : ℝ), logAmp (M.compAmp i) t / t ^ 2 := fun i =>
    setIntegral_congr_fun measurableSet_Ioi fun t _ => by ring
  have e2 : (∫ t in Ioi (0 : ℝ), Real.log (∑ i, M.jensenWeight i *
      Real.exp (logAmp (M.compAmp i) t)) * (1 / t ^ 2)) =
      ∫ t in Ioi (0 : ℝ), logAmp M.toSource.ampl t / t ^ 2 :=
    setIntegral_congr_fun measurableSet_Ioi fun t _ => by rw [← M.logAmp_mixture t]; ring
  simp only [e1, e2] at hle hiff
  refine ⟨hle, hiff.trans ⟨fun h i j x hx => ?_, fun h i j t ht => ?_⟩⟩
  · obtain ⟨t, ht0, htx⟩ := xChart_surj hx
    rcases ht0.eq_or_lt with rfl | htp
    · rw [xChart_zero] at htx
      rw [← htx, div_self (M.compAmp_pos i xiStar_pos).ne', div_self (M.compAmp_pos j xiStar_pos).ne']
    · have := h i j t htp
      unfold logAmp at this
      have hi := div_pos (M.compAmp_pos i (xiStar_pos.trans_le (xiStar_le_xChart t)))
        (M.compAmp_pos i xiStar_pos)
      have hj := div_pos (M.compAmp_pos j (xiStar_pos.trans_le (xiStar_le_xChart t)))
        (M.compAmp_pos j xiStar_pos)
      have := Real.log_injOn_pos hi hj this
      rwa [htx] at this
  · unfold logAmp
    rw [h i j (xChart t) (xiStar_le_xChart t)]

end MixtureData

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.MixtureData.pmix_jensen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MixtureData.pmix_jensen

end FormalResearch.ModularBootstrap.Mixtures
