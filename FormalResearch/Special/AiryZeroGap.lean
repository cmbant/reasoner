module

public import FormalResearch.Special.AiryNodes
public import FormalResearch.Special.SturmAiryComparison

/-!
# Spacing of the zeros of `Ai` and a rate bound for its Prüfer angle

Two elementary Sturm-theoretic inputs for the counting of the zeros in `[-5, 0]` (`AiryFirstZeros`):

* `airy_prufer_rate`: if `-M ≤ a ≤ b` with `M ≥ 1`, every Prüfer angle `θ` of `(Ai, Ai')` satisfies
  `θ b - θ a ≤ M (b - a)` (since `θ' = cos²θ + (-x) sin²θ ≤ max(1, -x)`);
* `airy_zero_gap`: **two distinct zeros `x < x' ≤ 0` of `Ai` with `x ≥ -Y` are at distance `≥ π/√Y`.**
  Proof: the zeros are at Prüfer levels `kπ < k'π`; the level `(k+1)π` is reached at some `x₁ ∈ (x, x']`, where
  `x, x₁` are consecutive zeros; Sturm comparison (`IsSol.exists_zero_Icc_of_comparison`) with
  `y'' = -Y y`, whose solution `sin(√Y (· - c))` has no zero in `[x, x₁]` if `x₁ - x < π/√Y` and `c` is chosen just
  below `x`.

Both are proved (no numerical input).
-/

@[expose] public section

open Set

namespace FormalResearch.Special

open SturmAiry

/-- **Rate bound for the Prüfer angle of `Ai`**: `θ' ≤ max(1, -x)`, so `θ b - θ a ≤ M (b - a)` for
`-M ≤ a ≤ b`, `M ≥ 1`. -/
theorem airy_prufer_rate {θ : ℝ → ℝ} (hθ : IsPruferLift (fun x => x) airyAi airyAi' θ) {M a b : ℝ}
    (hM : 1 ≤ M) (ha : -M ≤ a) (hab : a ≤ b) : θ b - θ a ≤ M * (b - a) := by
  have hg : ∀ x, HasDerivAt (fun x => M * x - θ x)
      (M - (Real.cos (θ x) ^ 2 - x * Real.sin (θ x) ^ 2)) x := fun x =>
    ((hasDerivAt_id x).const_mul M).sub (hθ.hasDerivAt x) |>.congr_deriv (by simp)
  have hmono : MonotoneOn (fun x => M * x - θ x) (Icc a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc a b)
      (fun x _ => (hg x).continuousAt.continuousWithinAt)
      (fun x _ => (hg x).differentiableAt.differentiableWithinAt) ?_
    intro x hx
    rw [interior_Icc] at hx
    rw [(hg x).deriv]
    have hx1 : -M ≤ x := by linarith [hx.1]
    nlinarith [Real.sin_sq_add_cos_sq (θ x), mul_nonneg (by linarith : 0 ≤ M + x) (sq_nonneg (Real.sin (θ x))),
      sq_nonneg (Real.sin (θ x)), sq_nonneg (Real.cos (θ x))]
  have := hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  dsimp only at this
  linarith

/-- `sin(ω(x - c))` solves `y'' = -ω² y`. -/
lemma airyGap_isSol_sin {ω : ℝ} (c : ℝ) :
    IsSol (fun _ => -ω ^ 2) (fun x => Real.sin (ω * (x - c))) (fun x => ω * Real.cos (ω * (x - c))) where
  hasDerivAt x := by
    have h : HasDerivAt (fun x => ω * (x - c)) ω x := by
      simpa using ((hasDerivAt_id x).sub_const c).const_mul ω
    simpa [mul_comm] using h.sin
  hasDerivAt' x := by
    have h : HasDerivAt (fun x => ω * (x - c)) ω x := by
      simpa using ((hasDerivAt_id x).sub_const c).const_mul ω
    have := (h.cos).const_mul ω
    refine this.congr_deriv ?_
    ring

/-- Consecutive zeros `x < x₁` of a solution `s` of `s'' = x s` (positive on the open interval between them)
with `-Y ≤ x` are at least `π/√Y` apart. -/
lemma airyGap_consecutive {s s' : ℝ → ℝ} (hs : IsSol (fun x => x) s s') {Y x x₁ : ℝ} (hY : 0 < Y)
    (hx : -Y ≤ x) (hxx₁ : x < x₁) (hx₁ : s x = 0) (hx₁' : s x₁ = 0)
    (hsign : ∀ t ∈ Ioo x x₁, 0 < s t) : Real.pi / √Y ≤ x₁ - x := by
  by_contra hlt
  push Not at hlt
  have hω : 0 < √Y := Real.sqrt_pos.mpr hY
  have hω2 : √Y ^ 2 = Y := Real.sq_sqrt hY.le
  set ω := √Y
  set δ := (Real.pi / ω - (x₁ - x)) / 2 with hδ
  have hδ0 : 0 < δ := by
    have : (x₁ - x) < Real.pi / ω := hlt
    rw [hδ]; linarith
  have hsol := airyGap_isSol_sin (ω := ω) (x - δ)
  obtain ⟨c, hc, hc0⟩ := IsSol.exists_zero_Icc_of_comparison (p := fun x => x) continuous_id hsol
    hs hxx₁ (fun t ht => by simp only [hω2]; linarith [ht.1]) hx₁ hx₁' hsign
  have h1 : 0 < ω * (c - (x - δ)) := mul_pos hω (by linarith [hc.1])
  have h2 : ω * (c - (x - δ)) < Real.pi := by
    have : ω * (c - (x - δ)) ≤ ω * (x₁ - (x - δ)) := mul_le_mul_of_nonneg_left (by linarith [hc.2]) hω.le
    have e : ω * (x₁ - (x - δ)) = ω * (x₁ - x) + ω * δ := by ring
    have e2 : ω * δ = (Real.pi - ω * (x₁ - x)) / 2 := by rw [hδ]; field_simp
    have hd : ω * (x₁ - x) < Real.pi := by
      rw [lt_div_iff₀ hω] at hlt; linarith
    linarith
  have := Real.sin_pos_of_pos_of_lt_pi h1 h2
  linarith

/-- **Spacing of the zeros of `Ai`.**  If `x < x' ≤ 0` are zeros of `Ai` and `-Y ≤ x` (`Y > 0`), then
`x' - x ≥ π/√Y`. -/
theorem airy_zero_gap {Y x x' : ℝ} (hY : 0 < Y) (hx : -Y ≤ x) (hxx' : x < x') (hx'0 : x' ≤ 0)
    (h : airyAi x = 0) (h' : airyAi x' = 0) : Real.pi / √Y ≤ x' - x := by
  obtain ⟨θ, hθ, -, -, hmono⟩ := airy_exists_prufer
  obtain ⟨k, hk⟩ := (airy_zero_iff_level hθ x).1 h
  obtain ⟨k', hk'⟩ := (airy_zero_iff_level hθ x').1 h'
  have hxle : x ∈ Iic (0 : ℝ) := by simp; linarith
  have hx'le : x' ∈ Iic (0 : ℝ) := hx'0
  have hlt : θ x < θ x' := hmono hxle hx'le hxx'
  have hkk : k < k' := by
    have : (k : ℝ) * Real.pi < k' * Real.pi := by rw [← hk, ← hk']; exact hlt
    have := lt_of_mul_lt_mul_right this Real.pi_pos.le
    exact_mod_cast this
  have hlev : ((k + 1 : ℤ) : ℝ) * Real.pi ∈ Icc (θ x) (θ x') := by
    constructor
    · rw [hk]; push_cast; nlinarith [Real.pi_pos]
    · rw [hk']
      have : ((k + 1 : ℤ) : ℝ) ≤ k' := by exact_mod_cast hkk
      exact mul_le_mul_of_nonneg_right this Real.pi_pos.le
  obtain ⟨x₁, hx₁, hθx₁⟩ := intermediate_value_Icc hxx'.le hθ.continuous.continuousOn hlev
  have hx₁gt : x < x₁ := by
    refine lt_of_le_of_ne hx₁.1 (fun heq => ?_)
    rw [← heq, hk] at hθx₁; push_cast at hθx₁; nlinarith [Real.pi_pos]
  have hx₁z : airyAi x₁ = 0 := (airy_zero_iff_level hθ x₁).2 ⟨k + 1, hθx₁⟩
  -- sign on the open interval
  have hsign : ∀ t ∈ Ioo x x₁, θ t ∈ Ioo ((k : ℝ) * Real.pi) ((k + 1 : ℤ) * Real.pi) := by
    intro t ht
    have h1 : θ x < θ t := hmono hxle (show t ∈ Iic (0 : ℝ) from by simp; linarith [ht.2, hx₁.2]) ht.1
    have h2 : θ t < θ x₁ := hmono (show t ∈ Iic (0 : ℝ) from by simp; linarith [ht.2, hx₁.2])
      (show x₁ ∈ Iic (0 : ℝ) from by simp; linarith [hx₁.2]) ht.2
    rw [hk] at h1; rw [hθx₁] at h2
    exact ⟨h1, h2⟩
  obtain ⟨r, hr, hy, -⟩ := hθ.exists_r
  have hsinsign : ∀ t ∈ Ioo x x₁, 0 < (-1 : ℝ) ^ k * airyAi t := by
    intro t ht
    obtain ⟨a1, a2⟩ := hsign t ht
    rw [hy t]
    have hs : 0 < (-1 : ℝ) ^ k * Real.sin (θ t) := by
      have e : θ t = (θ t - k * Real.pi) + k * Real.pi := by ring
      have hpos : 0 < Real.sin (θ t - k * Real.pi) := by
        apply Real.sin_pos_of_pos_of_lt_pi
        · linarith
        · push_cast at a2; linarith
      have : Real.sin (θ t) = (-1 : ℝ) ^ k * Real.sin (θ t - k * Real.pi) := by
        conv_lhs => rw [e]
        rw [Real.sin_add_int_mul_pi]
      rw [this, ← mul_assoc, ← mul_zpow, show (-1 : ℝ) * -1 = 1 by norm_num, one_zpow, one_mul]
      exact hpos
    calc (0 : ℝ) < r t * ((-1 : ℝ) ^ k * Real.sin (θ t)) := mul_pos (hr t) hs
      _ = _ := by ring
  have hmain : Real.pi / √Y ≤ x₁ - x := by
    rcases Int.even_or_odd k with he | ho
    · have hp : (-1 : ℝ) ^ k = 1 := he.neg_one_zpow
      exact airyGap_consecutive isSol_airyAi hY hx hx₁gt h hx₁z (fun t ht => by
        have := hsinsign t ht; rwa [hp, one_mul] at this)
    · have hp : (-1 : ℝ) ^ k = -1 := ho.neg_one_zpow
      exact airyGap_consecutive isSol_airyAi.neg hY hx hx₁gt (by simp [h]) (by simp [hx₁z])
        (fun t ht => by have := hsinsign t ht; rw [hp] at this; simpa using this)
  linarith [hx₁.2]

/-- info: 'FormalResearch.Special.airy_zero_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy_zero_gap

/-- info: 'FormalResearch.Special.airy_prufer_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy_prufer_rate

end FormalResearch.Special
