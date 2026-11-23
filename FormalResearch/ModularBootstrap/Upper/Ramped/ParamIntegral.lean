module

public import FormalResearch.Special.LangerHadamard

/-!
# Smooth parametric integrals `q ↦ ∫₀¹ w(t) K(c + a(t)(q - c)) dt`

A reparametrised form of the Hadamard integral of `FormalResearch.Special.LangerHadamard`
(there `a(t) = t`): with a continuous profile `a : [0,1] → [0,1]` and a continuous weight `w`, the map
`hadIntA a w K c` is `C^m` on a ball `B(c, ρ)` whenever `K` is `C^m` on it.  With `a(t) = t^2` this
gives the smoothness of the Langer integrals `∫₀¹ F(u t²) dt` and `∫₀¹ 2 t² H(r t²) dt`
(`remainder.tex`, Proposition 1.2(1)).

* `hadIntA`, `continuousOn_hadIntA`, `hasDerivAt_hadIntA`, `contDiffOn_hadIntA`.
-/

@[expose] public section

open Filter Topology Set MeasureTheory Metric
open FormalResearch.Special

namespace FormalResearch.ModularBootstrap.Upper.Ramped

/-- The reparametrised Hadamard integral `q ↦ ∫₀¹ w(t) K(c + a(t)(q - c)) dt`. -/
noncomputable def hadIntA (a w K : ℝ → ℝ) (c q : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, w t * K (c + a t * (q - c))

section
variable {a w K : ℝ → ℝ} {c ρ q : ℝ}

lemma hadIntA_mem_ball (ha01 : ∀ t ∈ Icc (0 : ℝ) 1, a t ∈ Icc (0 : ℝ) 1) (hq : q ∈ ball c ρ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : c + a t * (q - c) ∈ ball c ρ :=
  hadInt_mem_ball hq (ha01 t ht)

lemma hadIntA_cont_t (ha : Continuous a) (ha01 : ∀ t ∈ Icc (0 : ℝ) 1, a t ∈ Icc (0 : ℝ) 1)
    (hw : Continuous w) (hK : ContinuousOn K (ball c ρ)) (hq : q ∈ ball c ρ) :
    ContinuousOn (fun t => w t * K (c + a t * (q - c))) (Icc 0 1) := by
  refine hw.continuousOn.mul ?_
  exact hK.comp (by fun_prop) fun t ht => hadIntA_mem_ball ha01 hq ht

lemma hadIntA_bound (ha01 : ∀ t ∈ Icc (0 : ℝ) 1, a t ∈ Icc (0 : ℝ) 1) {r : ℝ} (hr : r < ρ)
    (hK : ContinuousOn K (ball c ρ)) (hw : Continuous w) :
    ∃ B : ℝ, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ closedBall c r,
      ‖w t * K (c + a t * (x - c))‖ ≤ B := by
  obtain ⟨B1, hB1⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hw.continuousOn
  obtain ⟨B2, hB2⟩ := hadInt_integrand_bound hr hK (fun _ => 1) continuous_const
  refine ⟨B1 * B2, fun t ht x hx => ?_⟩
  have h2 := hB2 (a t) (ha01 t ht) x hx
  simp only [one_mul] at h2
  rw [norm_mul]
  exact mul_le_mul (hB1 t ht) h2 (norm_nonneg _) ((norm_nonneg _).trans (hB1 t ht))

lemma continuousOn_hadIntA (ha : Continuous a) (ha01 : ∀ t ∈ Icc (0 : ℝ) 1, a t ∈ Icc (0 : ℝ) 1)
    (hw : Continuous w) (hK : ContinuousOn K (ball c ρ)) :
    ContinuousOn (hadIntA a w K c) (ball c ρ) := by
  intro q hq
  apply ContinuousAt.continuousWithinAt
  obtain ⟨r, hqr, hrρ⟩ : ∃ r, dist q c < r ∧ r < ρ := exists_between (mem_ball.1 hq)
  obtain ⟨B, hB⟩ := hadIntA_bound ha01 hrρ hK hw
  have hs : ball c r ∈ 𝓝 q := isOpen_ball.mem_nhds (mem_ball.2 hqr)
  refine intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => B) ?_ ?_ ?_ ?_
  · filter_upwards [hs] with x hx
    exact ((hadIntA_cont_t ha ha01 hw hK (ball_subset_ball hrρ.le hx)).mono
      (by simpa using Ioc_subset_Icc_self)).aestronglyMeasurable measurableSet_Ioc
  · filter_upwards [hs] with x hx
    refine Eventually.of_forall fun t ht => hB t (Ioc_subset_Icc_self (by simpa using ht)) x
      (ball_subset_closedBall hx)
  · exact intervalIntegrable_const
  · refine Eventually.of_forall fun t ht => ?_
    have ht' : t ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self (by simpa using ht)
    refine ContinuousAt.mul continuousAt_const ?_
    have hKc : ContinuousAt K (c + a t * (q - c)) :=
      hK.continuousAt (isOpen_ball.mem_nhds (hadIntA_mem_ball ha01 hq ht'))
    exact hKc.comp (f := fun x => c + a t * (x - c)) (by fun_prop)

lemma hasDerivAt_hadIntA (ha : Continuous a) (ha01 : ∀ t ∈ Icc (0 : ℝ) 1, a t ∈ Icc (0 : ℝ) 1)
    (hw : Continuous w) (hK : ContDiffOn ℝ 1 K (ball c ρ)) (hq : q ∈ ball c ρ) :
    HasDerivAt (hadIntA a w K c) (hadIntA a (fun t => a t * w t) (deriv K) c q) q := by
  have hKc : ContinuousOn K (ball c ρ) := hK.continuousOn
  have hK' : ContinuousOn (deriv K) (ball c ρ) :=
    hK.continuousOn_deriv_of_isOpen isOpen_ball le_rfl
  have hwt : Continuous (fun t => a t * w t) := ha.mul hw
  obtain ⟨r, hqr, hrρ⟩ : ∃ r, dist q c < r ∧ r < ρ := exists_between (mem_ball.1 hq)
  obtain ⟨B, hB⟩ := hadIntA_bound ha01 hrρ hK' hwt
  have hs : ball c r ∈ 𝓝 q := isOpen_ball.mem_nhds (mem_ball.2 hqr)
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := 0) (b := 1)
    (F := fun x t => w t * K (c + a t * (x - c)))
    (F' := fun x t => (a t * w t) * deriv K (c + a t * (x - c))) (x₀ := q) (s := ball c r)
    (bound := fun _ => B) hs ?_ ?_ ?_ ?_ intervalIntegrable_const ?_
  · exact key.2
  · filter_upwards [hs] with x hx
    exact ((hadIntA_cont_t ha ha01 hw hKc (ball_subset_ball hrρ.le hx)).mono
      (by simpa using Ioc_subset_Icc_self)).aestronglyMeasurable measurableSet_Ioc
  · exact (hadIntA_cont_t ha ha01 hw hKc hq).intervalIntegrable_of_Icc zero_le_one
  · exact ((hadIntA_cont_t ha ha01 hwt hK' hq).mono
      (by simpa using Ioc_subset_Icc_self)).aestronglyMeasurable measurableSet_Ioc
  · refine Eventually.of_forall fun t ht x hx => hB t (Ioc_subset_Icc_self (by simpa using ht)) x
      (ball_subset_closedBall hx)
  · refine Eventually.of_forall fun t ht x hx => ?_
    have ht' : t ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self (by simpa using ht)
    have hxρ : x ∈ ball c ρ := ball_subset_ball hrρ.le hx
    have hKd : DifferentiableAt ℝ K (c + a t * (x - c)) :=
      (hK.differentiableOn one_ne_zero).differentiableAt
        (isOpen_ball.mem_nhds (hadIntA_mem_ball ha01 hxρ ht'))
    have h1 : HasDerivAt (fun x : ℝ => c + a t * (x - c)) (a t) x := by
      simpa using (((hasDerivAt_id x).sub_const c).const_mul (a t)).const_add c
    have := (hKd.hasDerivAt.comp x h1).const_mul (w t)
    convert this using 1
    simp only [Function.comp_apply]
    ring

/-- `hadIntA a w K c` is `C^m` on `B(c, ρ)` whenever `K` is. -/
lemma contDiffOn_hadIntA (ha : Continuous a) (ha01 : ∀ t ∈ Icc (0 : ℝ) 1, a t ∈ Icc (0 : ℝ) 1)
    (m : ℕ) : ∀ (w K : ℝ → ℝ), Continuous w →
    ContDiffOn ℝ m K (ball c ρ) → ContDiffOn ℝ m (hadIntA a w K c) (ball c ρ) := by
  induction m with
  | zero =>
    intro w K hw hK
    rw [Nat.cast_zero, contDiffOn_zero] at hK ⊢
    exact continuousOn_hadIntA ha ha01 hw hK
  | succ m ih =>
    intro w K hw hK
    have hK1 : ContDiffOn ℝ 1 K (ball c ρ) :=
      hK.of_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m))
    have hdK : ContDiffOn ℝ m (deriv K) (ball c ρ) :=
      hK.deriv_of_isOpen isOpen_ball (by simp)
    have hwt : Continuous (fun t => a t * w t) := ha.mul hw
    rw [Nat.cast_succ, contDiffOn_succ_iff_deriv_of_isOpen isOpen_ball]
    refine ⟨fun q hq => (hasDerivAt_hadIntA ha ha01 hw hK1 hq).differentiableAt.differentiableWithinAt,
      by simp, ?_⟩
    exact (ih _ _ hwt hdK).congr fun q hq => (hasDerivAt_hadIntA ha ha01 hw hK1 hq).deriv

end

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.contDiffOn_hadIntA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms contDiffOn_hadIntA

end FormalResearch.ModularBootstrap.Upper.Ramped
