module

public import FormalResearch.CohnElkies.MellinAiryToolkit
public import FormalResearch.CohnElkies.AirySeedFloors

/-!
# The edge dispersion `m(τ) = log((πτ/2)/tanh(πτ/2))` for the Hankel strip data (M5-S5)

`hankelEdgeM τ = ceEll (π τ / 2)` is the dispersion `m` of `(MS2)` in `teb:mellin` for the Hankel strip
(`mat:T4`(f)): `m(0) = 0`, `m` is continuous and strictly increasing on `[0, ∞)`, unbounded
(`hankelEdgeM_exists_root`), with derivative `m' = -Φ''` and

* `hankelEdgeM_step`: `(3/16) min(τ², 1) ≤ m(τ) - m(τ/2)` (`(M1)`, from `m1_bound`);
* `hankelEdgeM_slope`: `(1/2) τ / (1 + τ³) ≤ m'(τ)` (`(M2)`, from `m2_bounds`);
* `hankelEdgeM_sq_le`: `τ² ≤ (16/3) m(τ)` whenever `m(τ) < 3/16`;
* `hankelEdgePhi_odd`, `hankelEdgePhi_hasDerivAt`: `Φ(τ; L) = edgePhi L τ` is odd in `τ` with
  `∂_τ Φ = L - m(τ)`.
-/

@[expose] public section

open Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-- The dispersion `m(τ) = ceEll (π τ / 2)`. -/
noncomputable def hankelEdgeM (τ : ℝ) : ℝ := ceEll (π * τ / 2)

/-- Its derivative `m'(τ) = -Φ''(τ)`. -/
noncomputable def hankelEdgeM' (τ : ℝ) : ℝ := -edgePhiDeriv2 τ

lemma hankelEdgeM_zero : hankelEdgeM 0 = 0 := by simp [hankelEdgeM, ceEll]

lemma hankelEdgeM_pos {τ : ℝ} (hτ : 0 < τ) : 0 < hankelEdgeM τ := by
  have hx : 0 < π * τ / 2 := by positivity
  have h1 := tanh_lt_id hx
  have h2 := tanh_pos_of_pos hx
  unfold hankelEdgeM ceEll
  exact Real.log_pos ((one_lt_div h2).mpr h1)

lemma hankelEdgeM_nonneg {τ : ℝ} (hτ : 0 ≤ τ) : 0 ≤ hankelEdgeM τ := by
  rcases hτ.eq_or_lt with h | h
  · rw [← h, hankelEdgeM_zero]
  · exact (hankelEdgeM_pos h).le

lemma hankelEdgeM_hasDerivAt {τ : ℝ} (hτ : 0 < τ) : HasDerivAt hankelEdgeM (hankelEdgeM' τ) τ :=
  (m2_bounds hτ).1

lemma hankelEdgeM_continuousOn : ContinuousOn hankelEdgeM (Ici 0) := by
  intro τ hτ
  rcases (mem_Ici.mp hτ).eq_or_lt with h | h
  · rw [← h, ← continuousWithinAt_Ioi_iff_Ici]
    have h0 : Tendsto ceEll (𝓝[>] (0 : ℝ)) (𝓝 0) := ceEll_tendsto_zero
    have hlin : Tendsto (fun s : ℝ => π * s / 2) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have : Continuous (fun s : ℝ => π * s / 2) := by fun_prop
        simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        have : (0 : ℝ) < s := hs
        show (0 : ℝ) < π * s / 2
        positivity
    have h1 := h0.comp hlin
    unfold ContinuousWithinAt
    rw [hankelEdgeM_zero]
    exact h1
  · exact (hankelEdgeM_hasDerivAt h).continuousAt.continuousWithinAt

lemma hankelEdgeM_strictMonoOn : StrictMonoOn hankelEdgeM (Ici 0) := by
  intro a ha b hb hab
  rcases (mem_Ici.mp ha).eq_or_lt with h | h
  · rw [← h, hankelEdgeM_zero]
    exact hankelEdgeM_pos (by rw [← h] at hab; exact hab)
  · have hx : π * a / 2 ∈ Ioi (0 : ℝ) := by
      have : 0 < π * a / 2 := by positivity
      exact this
    have hy : π * b / 2 ∈ Ioi (0 : ℝ) := by
      have : 0 < π * b / 2 := by have : 0 < b := h.trans hab; positivity
      exact this
    exact ceEll_strictMonoOn hx hy (by nlinarith [Real.pi_pos])

lemma hankelEdgeM_step {τ : ℝ} (hτ : 0 < τ) :
    (3 / 16) * min (τ ^ 2) 1 ≤ hankelEdgeM τ - hankelEdgeM (τ / 2) := by
  have h := m1_bound hτ
  have h2 : (3 / 16) * min (τ ^ 2) 1 ≤ 3 / 8 * τ ^ 2 / (1 + τ ^ 2) := by
    have hpos : 0 < 1 + τ ^ 2 := by positivity
    rw [le_div_iff₀ hpos]
    rcases le_total (τ ^ 2) 1 with h1 | h1
    · rw [min_eq_left h1]; nlinarith [sq_nonneg τ, sq_nonneg (τ ^ 2)]
    · rw [min_eq_right h1]; nlinarith [sq_nonneg τ]
  exact h2.trans h

lemma hankelEdgeM_slope {τ : ℝ} (hτ : 0 < τ) :
    (1 / 2) * τ / (1 + τ ^ 3) ≤ hankelEdgeM' τ := by
  have h := (m2_bounds hτ).2.1
  have key : 1 / 2 * (1 + τ ^ 2) ≤ 1 + τ ^ 3 := by
    rcases le_total τ 1 with h1 | h1
    · nlinarith [pow_pos hτ 3, sq_nonneg τ]
    · nlinarith [pow_pos hτ 3, sq_nonneg τ]
  have h3 : (1 / 2) * τ / (1 + τ ^ 3) ≤ τ / (1 + τ ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left key hτ.le]
  exact h3.trans h

lemma hankelEdgeM_sq_le {τ μ : ℝ} (hτ : 0 ≤ τ) (hm : hankelEdgeM τ = μ) (hμ : μ < 3 / 16) :
    τ ^ 2 ≤ 16 / 3 * μ := by
  rcases hτ.eq_or_lt with h | h
  · rw [← h] at hm ⊢
    rw [hankelEdgeM_zero] at hm
    rw [← hm]; norm_num
  · have h1 := hankelEdgeM_step h
    have h2 := hankelEdgeM_nonneg (show 0 ≤ τ / 2 by positivity)
    have hpos : 0 < 1 + τ ^ 2 := by positivity
    have h3 := m1_bound h
    have h4 : 3 / 8 * τ ^ 2 ≤ μ * (1 + τ ^ 2) := by
      have : 3 / 8 * τ ^ 2 / (1 + τ ^ 2) ≤ μ := by
        have : hankelEdgeM (τ / 2) = ceEll (π * (τ / 2) / 2) := rfl
        unfold hankelEdgeM at hm h2
        linarith
      rwa [div_le_iff₀ hpos] at this
    have hτ2 : τ ^ 2 < 1 := by
      by_contra hcon
      push Not at hcon
      nlinarith [sq_nonneg τ]
    nlinarith [sq_nonneg τ]

lemma hankelEdgeM_exists_root {μ : ℝ} (hμ : 0 ≤ μ) : ∃ τ : ℝ, 0 ≤ τ ∧ hankelEdgeM τ = μ := by
  set N : ℝ := 2 * Real.exp μ / π with hN
  have hN0 : 0 < N := by positivity
  have hx : π * N / 2 = Real.exp μ := by rw [hN]; field_simp
  have hmN : μ ≤ hankelEdgeM N := by
    unfold hankelEdgeM ceEll
    rw [hx]
    have hpos : 0 < Real.exp μ := Real.exp_pos μ
    have ht0 := tanh_pos_of_pos hpos
    have ht1 : Real.tanh (Real.exp μ) ≤ 1 := (Real.tanh_lt_one _).le
    have : Real.exp μ ≤ Real.exp μ / Real.tanh (Real.exp μ) := by
      rw [le_div_iff₀ ht0]; nlinarith
    calc μ = Real.log (Real.exp μ) := (Real.log_exp μ).symm
      _ ≤ _ := Real.log_le_log hpos this
  have hcont : ContinuousOn hankelEdgeM (Icc 0 N) := hankelEdgeM_continuousOn.mono Icc_subset_Ici_self
  have := intermediate_value_Icc hN0.le hcont
  obtain ⟨τ, hτ, hτm⟩ := this ⟨by rw [hankelEdgeM_zero]; exact hμ, hmN⟩
  exact ⟨τ, hτ.1, hτm⟩

lemma hankelEdgePhi_odd (L τ : ℝ) : edgePhi L (-τ) = -edgePhi L τ := by
  unfold edgePhi
  have heven : ∀ u : ℝ, Real.log (Real.tanh (π * -u / 2) / (π * -u / 2)) =
      Real.log (Real.tanh (π * u / 2) / (π * u / 2)) := by
    intro u
    rw [show π * -u / 2 = -(π * u / 2) by ring, Real.tanh_neg, neg_div_neg_eq]
  have h1 := intervalIntegral.integral_comp_neg (a := 0) (b := τ)
    (fun u : ℝ => Real.log (Real.tanh (π * u / 2) / (π * u / 2)))
  simp only [heven, neg_zero] at h1
  have h2 : ∫ u in (0 : ℝ)..-τ, Real.log (Real.tanh (π * u / 2) / (π * u / 2)) =
      -∫ u in (-τ)..0, Real.log (Real.tanh (π * u / 2) / (π * u / 2)) :=
    intervalIntegral.integral_symm (-τ) 0
  rw [h2, ← h1]
  ring

lemma hankelEdgePhi_hasDerivAt (L : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt (edgePhi L) (L - hankelEdgeM τ) τ := by
  refine (hasDerivAt_edgePhi L τ).congr_deriv ?_
  unfold edgePhiDeriv
  rw [if_neg hτ.ne', abs_of_pos hτ]
  unfold hankelEdgeM ceEll
  rw [show π * τ / 2 / Real.tanh (π * τ / 2) = (Real.tanh (π * τ / 2) / (π * τ / 2))⁻¹ by rw [inv_div],
    Real.log_inv]
  ring

/-- info: 'FormalResearch.SignUncertainty.hankelEdgeM_continuousOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelEdgeM_continuousOn

/-- info: 'FormalResearch.SignUncertainty.hankelEdgeM_strictMonoOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelEdgeM_strictMonoOn

/-- info: 'FormalResearch.SignUncertainty.hankelEdgeM_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelEdgeM_step

/-- info: 'FormalResearch.SignUncertainty.hankelEdgeM_slope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelEdgeM_slope

/-- info: 'FormalResearch.SignUncertainty.hankelEdgeM_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelEdgeM_sq_le

/-- info: 'FormalResearch.SignUncertainty.hankelEdgeM_exists_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelEdgeM_exists_root

/-- info: 'FormalResearch.SignUncertainty.hankelEdgePhi_odd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelEdgePhi_odd

/-- info: 'FormalResearch.SignUncertainty.hankelEdgePhi_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelEdgePhi_hasDerivAt

end FormalResearch.SignUncertainty
