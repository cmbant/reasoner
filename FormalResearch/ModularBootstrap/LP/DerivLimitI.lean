module

public import FormalResearch.ModularBootstrap.LP.Reference
public import FormalResearch.ModularBootstrap.Duality.CrossingMeasure

/-!
# The infinite-order derivative limit, part (i) (`ds:LP`(i)), direction (b) ⇒ (a)

`CFT/modular_bootstrap/paper/dual_spectrum.tex`, Theorem LP (`ds:LP`), (i).  A *finite odd-Laguerre
test* on `X` is `g = e^{-2πt} p` with `p ∈ O_N = span{P_k : k odd ≤ N}`, `g ≥ 0` on `X` and
`g_vac > 0` (`OddFeasible`).  If a crossing measure `ν` is carried by `X` then there is none
(`not_oddFeasible_of_crossingMeasure`, for every `X`): this is `ds:cay` (`ds_cay_iff`) applied to `ν`
and to `e^{2πt} μ_C = ρ_C dt`, and `∫ g dν = -g_vac`.
-/

@[expose] public section

open MeasureTheory Set Real Filter Topology
open scoped ENNReal
open FormalResearch.ModularBootstrap.Crossing

namespace FormalResearch.ModularBootstrap.LP

/-- A finite odd-Laguerre test on `X`: `p ∈ O_N`, `g = e^{-2πt} p ≥ 0` on `X`, `g_vac > 0`. -/
def OddFeasible (prob : FixedWeightProblem) (a : ℝ) (N : ℕ) (X : Set ℝ) (p : ℝ → ℝ) : Prop :=
  p ∈ oddSpan (prob.w : ℝ) N ∧ (∀ t ∈ X, 0 ≤ Real.exp (-2 * π * t) * p t) ∧
    0 < prob.gVac a (fun t => Real.exp (-2 * π * t) * p t)

lemma OddFeasible.p_nonneg {prob : FixedWeightProblem} {a : ℝ} {N : ℕ} {X : Set ℝ} {p : ℝ → ℝ}
    (h : OddFeasible prob a N X p) {t : ℝ} (ht : t ∈ X) : 0 ≤ p t := by
  have := h.2.1 t ht
  exact nonneg_of_mul_nonneg_right this (Real.exp_pos _)

lemma OddFeasible.mono_N {prob : FixedWeightProblem} {a : ℝ} {M N : ℕ} (hMN : M ≤ N) {X : Set ℝ}
    {p : ℝ → ℝ} (h : OddFeasible prob a M X p) : OddFeasible prob a N X p :=
  ⟨oddSpan_mono _ hMN h.1, h.2.1, h.2.2⟩

lemma OddFeasible.mono_X {prob : FixedWeightProblem} {a : ℝ} {N : ℕ} {X Y : Set ℝ} (hYX : Y ⊆ X)
    {p : ℝ → ℝ} (h : OddFeasible prob a N X p) : OddFeasible prob a N Y p :=
  ⟨h.1, fun t ht => h.2.1 t (hYX ht), h.2.2⟩

section BA

variable {prob : FixedWeightProblem} {a : ℝ}

lemma exp_mul_lagP_eq (w : ℝ) (k : ℕ) (t : ℝ) :
    Real.exp (-2 * π * t) * lagP w k t =
      ((-1) ^ k * (k.factorial : ℝ) / (4 * π) ^ k) * lagPsi w k t := by
  rw [lagP_eq]; unfold lagPsi; ring

/-- `ν`-integrability of the crossing measure's Laplace transforms in the form needed for `ds:cay`. -/
lemma crossing_lapFin (meas : AdmissibleCrossingMeasure prob a) {β : ℝ} (hβ : 0 < β) :
    Integrable (fun t => Real.exp (-2 * π * β * t)) meas.ν := by
  have := meas.finite_laplace hβ
  rwa [IntegrableOn, Duality.restrict_Ici_eq_self meas] at this

/-- **`ds:LP`(i), (b) ⇒ (a)**: a crossing measure carried by `X` excludes every finite odd-Laguerre
test on `X` (for every `X`). -/
theorem not_oddFeasible_of_crossingMeasure (ha : prob.totalShift ≤ a)
    (meas : AdmissibleCrossingMeasure prob a) {X : Set ℝ} (hX : meas.ν Xᶜ = 0) (N : ℕ)
    (p : ℝ → ℝ) : ¬ OddFeasible prob a N X p := by
  rintro ⟨hp, hnn, hvac⟩
  have hw : 0 < (prob.w : ℝ) := by exact_mod_cast prob.hw
  set θ : ℝ := 1 / 2 with hθ
  have hθ0 : 0 < θ := by norm_num [hθ]
  have hθ1 : θ < 1 := by norm_num [hθ]
  have hs0 := sTheta_pos hθ0 hθ1
  set ν := meas.ν with hν
  set νC := expTilt (refMeas prob a) with hνC
  have hint : Integrable (fun t => Real.exp (-2 * π * sTheta θ * t)) ν := crossing_lapFin meas hs0
  have hs1 : sTheta θ < 1 := by
    unfold sTheta; rw [hθ]; norm_num
  have hint' : Integrable (fun t => Real.exp (-2 * π * sTheta θ * t)) νC := by
    rw [hνC, integrable_expTilt_iff]
    have := integrable_exp_ref ha (c := 2 * π * (1 - sTheta θ)) (by nlinarith [Real.pi_pos])
    refine this.congr (Eventually.of_forall fun t => ?_)
    simp only
    rw [← Real.exp_add]; congr 1; ring
  have hcross : ∀ β, sTheta θ < β → β < 1 / sTheta θ →
      ∫ t, xiW (prob.w : ℝ) β t ∂ν = ∫ t, xiW (prob.w : ℝ) β t ∂νC := by
    intro β h1 h2
    have hβ0 : 0 < β := hs0.trans h1
    have h := meas.crossing hβ0
    rw [Duality.restrict_Ici_eq_self meas] at h
    rw [hνC, integral_xiW_expTilt_ref' ha β]
    exact h
  have hmom := (ds_cay_iff hw hθ0 hθ1 meas.supp_nonneg (by rw [hνC]; exact expTilt_apply_eq_zero refMeas_Iio)
    hint hint').1 hcross
  -- the test as a combination of the `ψ_k`
  have hmain : ∀ q ∈ oddSpan (prob.w : ℝ) N,
      Integrable (fun t => Real.exp (-2 * π * t) * q t) ν ∧
      Integrable (fun t => Real.exp (-2 * π * t) * q t) νC ∧
      ∫ t, Real.exp (-2 * π * t) * q t ∂ν = ∫ t, Real.exp (-2 * π * t) * q t ∂νC := by
    intro q hq
    refine Submodule.span_induction (p := fun q _ =>
      Integrable (fun t => Real.exp (-2 * π * t) * q t) ν ∧
      Integrable (fun t => Real.exp (-2 * π * t) * q t) νC ∧
      ∫ t, Real.exp (-2 * π * t) * q t ∂ν = ∫ t, Real.exp (-2 * π * t) * q t ∂νC) ?_ ?_ ?_ ?_ hq
    · rintro f ⟨k, hk, -, rfl⟩
      have h1 := (ds_cay_series hw hθ0 hθ1 meas.supp_nonneg hint (ϖ := 0) (β := 1)
        (by simpa using hθ0) (by norm_num)).1 k
      have h2 := (ds_cay_series hw hθ0 hθ1 (by rw [hνC]; exact expTilt_apply_eq_zero refMeas_Iio)
        hint' (ϖ := 0) (β := 1) (by simpa using hθ0) (by norm_num)).1 k
      have e : (fun t => Real.exp (-2 * π * t) * lagP (prob.w : ℝ) k t) =
          fun t => ((-1) ^ k * (k.factorial : ℝ) / (4 * π) ^ k) * lagPsi (prob.w : ℝ) k t :=
        funext fun t => exp_mul_lagP_eq _ k t
      rw [e]
      refine ⟨h1.const_mul _, h2.const_mul _, ?_⟩
      rw [integral_const_mul, integral_const_mul, hmom k hk]
    · simp
    · rintro f g _ _ ⟨hf1, hf2, hf3⟩ ⟨hg1, hg2, hg3⟩
      simp only [Pi.add_apply, mul_add]
      exact ⟨hf1.add hg1, hf2.add hg2, by rw [integral_add hf1 hg1, integral_add hf2 hg2, hf3, hg3]⟩
    · rintro c f _ ⟨hf1, hf2, hf3⟩
      simp only [Pi.smul_apply, smul_eq_mul]
      have e : ∀ t, Real.exp (-2 * π * t) * (c * f t) = c * (Real.exp (-2 * π * t) * f t) :=
        fun t => by ring
      simp_rw [e]
      exact ⟨hf1.const_mul c, hf2.const_mul c, by rw [integral_const_mul, integral_const_mul, hf3]⟩
  obtain ⟨-, -, heq⟩ := hmain p hp
  -- `∫ g dν_C = ∫ p dμ_C = -g_vac`
  have hνCint : ∫ t, Real.exp (-2 * π * t) * p t ∂νC = ∫ t, p t ∂refMeas prob a := by
    rw [hνC, integral_expTilt]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only
    rw [← mul_assoc, ← Real.exp_add]; ring_nf; simp
  have hge : 0 ≤ ∫ t, Real.exp (-2 * π * t) * p t ∂ν := by
    refine integral_nonneg_of_ae ?_
    have : ∀ᵐ t ∂ν, t ∉ Xᶜ := measure_eq_zero_iff_ae_notMem.1 hX
    filter_upwards [this] with t ht
    exact hnn t (by simpa using ht)
  rw [heq, hνCint] at hge
  have := gVac_expPoly ha p
  linarith

end BA

end FormalResearch.ModularBootstrap.LP
