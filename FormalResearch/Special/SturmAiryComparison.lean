module

public import FormalResearch.Special.SturmAiryZeros

/-!
# Sturm comparison and the zeros of `y'' = x y` on the two half-lines

Continuation of `FormalResearch/Special/SturmAiryZeros.lean` (real solutions of `y'' = q y` on `ℝ`).

* `IsSol.exists_zero_Icc_of_comparison` (**Sturm comparison**): if `s'' = p s` has consecutive zeros
  `a < b` (`s > 0` on `(a, b)`) and `q ≤ p` on `[a, b]`, then every solution of `y'' = q y` has a zero in
  the closed interval `[a, b]`.  So the equation with the larger potential has fewer zeros.  Only
  `p` has to be continuous; the zero may sit at an endpoint (`y = s`, `q = p`).
* `IsSol.exists_zero_Icc_of_le_neg_one`: with `p = -1`, `s = sin(· - a)`: if `q ≤ -1` on
  `[a, a + π]`, every solution has a zero in `[a, a + π]`.
* `IsSol.infinite_zeros_of_le_neg_one` and `IsSol.infinite_zeros_Iic_zero`: for `q x = x` (the Airy
  equation) every solution has infinitely many zeros in `(-∞, 0]` (more precisely, in
  `(-∞, -1]`; the zero solution has every point as a zero; for a nontrivial one the zeros are
  discrete by `IsSol.finite_zeros_Icc`).
* `IsSol.eq_zero_of_two_zeros_of_pos`, `IsSol.zeros_Ici_zero_subsingleton`: if `q > 0` on `(x₁, x₂)`
  and `y x₁ = y x₂ = 0` then `y ≡ 0`; for `q x = x` a nontrivial solution has **at most one zero in
  `[0, ∞)`** (via `(y y')' = y'² + q y² ≥ 0`).

Not formalised: a quantitative count of zeros on `[-T, 0]` from comparison alone (the sharp
count `⌊θ(b)/π⌋ - ⌊θ(a)/π⌋` is in `AiryPruferZeros`), comparison with a strict inequality giving
a zero in the open interval.
-/

@[expose] public section

open Set Filter Topology

namespace FormalResearch.Special.SturmAiry

variable {q p y y' s s' : ℝ → ℝ}

/-- If `f(a) = 0` and `f > 0` on `(a, b)`, then `f'(a) ≥ 0`. -/
theorem nonneg_deriv_of_pos_right {f : ℝ → ℝ} {d a b : ℝ} (hd : HasDerivAt f d a) (hab : a < b)
    (ha : f a = 0) (hpos : ∀ x ∈ Ioo a b, 0 < f x) : 0 ≤ d := by
  by_contra hneg
  push Not at hneg
  have hs := (hasDerivAt_iff_tendsto_slope.1 hd).mono_left (nhdsGT_le_nhdsNE a)
  have h1 : ∀ᶠ x in 𝓝[>] a, slope f a x < 0 := hs.eventually (Iio_mem_nhds hneg)
  have h2 : ∀ᶠ x in 𝓝[>] a, x ∈ Ioo a b := Ioo_mem_nhdsGT hab
  obtain ⟨x, hx1, hx2⟩ := (h1.and h2).exists
  have h3 := hpos x hx2
  rw [slope_def_field, ha] at hx1
  have : 0 < (f x - 0) / (x - a) := div_pos (by linarith) (by linarith [hx2.1])
  linarith

/-- If `f(b) = 0` and `f > 0` on `(a, b)`, then `f'(b) ≤ 0`. -/
theorem nonpos_deriv_of_pos_left {f : ℝ → ℝ} {d a b : ℝ} (hd : HasDerivAt f d b) (hab : a < b)
    (hb : f b = 0) (hpos : ∀ x ∈ Ioo a b, 0 < f x) : d ≤ 0 := by
  have hd' : HasDerivAt f d (-(-b)) := by simpa using hd
  have hg : HasDerivAt (fun x => f (-x)) ((-1 : ℝ) • d) (-b) := hd'.scomp (-b) (hasDerivAt_neg (-b))
  have := nonneg_deriv_of_pos_right hg (a := -b) (b := -a) (by linarith) (by simpa using hb)
    (fun x hx => hpos (-x) ⟨by linarith [hx.2], by linarith [hx.1]⟩)
  simp only [neg_smul, one_smul] at this
  linarith

/-- A continuous function without zeros on `[a, b]` has constant sign there. -/
theorem sign_const_of_ne_zero {f : ℝ → ℝ} (hc : Continuous f) {a b : ℝ} (hab : a ≤ b)
    (h : ∀ x ∈ Icc a b, f x ≠ 0) :
    (∀ x ∈ Icc a b, 0 < f x) ∨ ∀ x ∈ Icc a b, f x < 0 := by
  have hax : a ∈ Icc a b := ⟨le_rfl, hab⟩
  rcases lt_or_gt_of_ne (h a hax) with ha | ha
  · right
    intro x hx
    by_contra hneg
    push Not at hneg
    obtain ⟨c, hc1, hc2⟩ := intermediate_value_Icc hx.1 hc.continuousOn ⟨ha.le, hneg⟩
    exact h c ⟨hc1.1, hc1.2.trans hx.2⟩ hc2
  · left
    intro x hx
    by_contra hneg
    push Not at hneg
    obtain ⟨c, hc1, hc2⟩ := intermediate_value_Icc' hx.1 hc.continuousOn ⟨hneg, ha.le⟩
    exact h c ⟨hc1.1, hc1.2.trans hx.2⟩ hc2

namespace IsSol

private theorem false_of_pos (hp : Continuous p) (hy : IsSol q y y') (hs : IsSol p s s') {a b : ℝ}
    (hab : a < b) (hqp : ∀ x ∈ Icc a b, q x ≤ p x) (hsa : s a = 0) (hsb : s b = 0)
    (hspos : ∀ x ∈ Ioo a b, 0 < s x) (hypos : ∀ x ∈ Icc a b, 0 < y x) : False := by
  have hV : ∀ x, HasDerivAt (fun x => y x * s' x - y' x * s x) ((p x - q x) * (y x * s x)) x := by
    intro x
    have := ((hy.hasDerivAt x).mul (hs.hasDerivAt' x)).sub
      ((hy.hasDerivAt' x).mul (hs.hasDerivAt x))
    exact this.congr_deriv (by ring)
  have hmono : MonotoneOn (fun x => y x * s' x - y' x * s x) (Icc a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc a b)
      (fun x _ => (hV x).continuousAt.continuousWithinAt)
      (fun x _ => (hV x).differentiableAt.differentiableWithinAt) ?_
    intro x hx
    rw [interior_Icc] at hx
    rw [(hV x).deriv]
    have h1 := hspos x hx
    have h2 := hypos x (Ioo_subset_Icc_self hx)
    have h3 := hqp x (Ioo_subset_Icc_self hx)
    exact mul_nonneg (by linarith) (by positivity)
  have hs0 : ∃ x, s x ≠ 0 := ⟨(a + b) / 2, (hspos _ ⟨by linarith, by linarith⟩).ne'⟩
  have hsa' : 0 < s' a :=
    lt_of_le_of_ne (nonneg_deriv_of_pos_right (hs.hasDerivAt a) hab hsa hspos)
      (Ne.symm (hs.deriv_ne_zero_of_zero hp hs0 hsa))
  have hsb' : s' b < 0 :=
    lt_of_le_of_ne (nonpos_deriv_of_pos_left (hs.hasDerivAt b) hab hsb hspos)
      (hs.deriv_ne_zero_of_zero hp hs0 hsb)
  have h := hmono ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab.le
  simp only [hsa, hsb, mul_zero, sub_zero] at h
  have := mul_pos (hypos a ⟨le_rfl, hab.le⟩) hsa'
  have := mul_neg_of_pos_of_neg (hypos b ⟨hab.le, le_rfl⟩) hsb'
  linarith

/-- **Sturm comparison theorem.**  Let `s'' = p s` have consecutive zeros `a < b` (`s > 0` on
`(a, b)`, `p` continuous) and let `q ≤ p` on `[a, b]`.  Then every solution `y` of `y'' = q y` has a
zero in `[a, b]`: the equation with the smaller potential oscillates at least as fast. -/
theorem exists_zero_Icc_of_comparison (hp : Continuous p) (hy : IsSol q y y')
    (hs : IsSol p s s') {a b : ℝ} (hab : a < b) (hqp : ∀ x ∈ Icc a b, q x ≤ p x) (hsa : s a = 0)
    (hsb : s b = 0) (hspos : ∀ x ∈ Ioo a b, 0 < s x) : ∃ c ∈ Icc a b, y c = 0 := by
  by_contra hcon
  push Not at hcon
  rcases sign_const_of_ne_zero hy.continuous hab.le hcon with h | h
  · exact false_of_pos hp hy hs hab hqp hsa hsb hspos h
  · exact false_of_pos hp hy.neg hs hab hqp hsa hsb hspos (fun x hx => by simpa using h x hx)

/-- `sin (· - a)` solves `y'' = -y`. -/
theorem isSol_sin_sub (a : ℝ) :
    IsSol (fun _ => (-1 : ℝ)) (fun x => Real.sin (x - a)) (fun x => Real.cos (x - a)) where
  hasDerivAt x := by
    simpa using ((hasDerivAt_id x).sub_const a).sin
  hasDerivAt' x := by
    simpa using (((hasDerivAt_id x).sub_const a).cos).congr_deriv (by simp)

/-- If `q ≤ -1` on an interval `[a, a + π]`, every solution of `y'' = q y` has a zero there. -/
theorem exists_zero_Icc_of_le_neg_one (hy : IsSol q y y') {a : ℝ}
    (hq : ∀ x ∈ Icc a (a + Real.pi), q x ≤ -1) : ∃ c ∈ Icc a (a + Real.pi), y c = 0 :=
  exists_zero_Icc_of_comparison (p := fun _ => (-1 : ℝ)) continuous_const hy (isSol_sin_sub a)
    (by linarith [Real.pi_pos]) hq (by simp) (by simp) (fun x hx =>
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2]))

/-- **Infinitely many zeros on the oscillatory side.**  If `q ≤ -1` on `(-∞, T]`, every solution of
`y'' = q y` has infinitely many zeros in `(-∞, T]`. -/
theorem infinite_zeros_of_le_neg_one (hy : IsSol q y y') {T : ℝ} (hq : ∀ x ≤ T, q x ≤ -1) :
    {x | x ≤ T ∧ y x = 0}.Infinite := by
  refine Set.infinite_of_forall_exists_lt fun m => ?_
  set a := min m T - 2 * Real.pi with ha
  obtain ⟨c, hc, hy0⟩ := exists_zero_Icc_of_le_neg_one hy (a := a) (fun x hx => hq x (by
    have := min_le_right m T
    linarith [hx.2, Real.pi_pos]))
  refine ⟨c, ⟨?_, hy0⟩, ?_⟩
  · have := min_le_right m T
    linarith [hc.2, Real.pi_pos]
  · have := min_le_left m T
    linarith [hc.2, Real.pi_pos]

/-- **For `y'' = x y`, infinitely many zeros on `(-∞, 0]`.**  Every solution (the zero solution
trivially; a nontrivial one has a discrete, unbounded-below zero set). -/
theorem infinite_zeros_Iic_zero (hy : IsSol (fun x => x) y y') :
    {x | x ≤ 0 ∧ y x = 0}.Infinite :=
  (infinite_zeros_of_le_neg_one (T := -1) hy (fun x hx => hx)).mono
    (fun x hx => ⟨hx.1.trans (by norm_num), hx.2⟩)

/-! ### The positive side: `q > 0` forces at most one zero -/

/-- If `q > 0` on `(x₁, x₂)` and `y x₁ = y x₂ = 0`, then `y ≡ 0` (`q` continuous): the function
`y y'` is nondecreasing, vanishes at both ends, so `y'² + q y² = (y y')' = 0` inside. -/
theorem eq_zero_of_two_zeros_of_pos (hq : Continuous q) (h : IsSol q y y') {x₁ x₂ : ℝ}
    (h12 : x₁ < x₂) (hpos : ∀ x ∈ Ioo x₁ x₂, 0 < q x) (h1 : y x₁ = 0) (h2 : y x₂ = 0) (x : ℝ) :
    y x = 0 := by
  have hP : ∀ x, HasDerivAt (fun x => y x * y' x) (y' x ^ 2 + q x * y x ^ 2) x := fun x =>
    ((h.hasDerivAt x).mul (h.hasDerivAt' x)).congr_deriv (by ring)
  have hmono : MonotoneOn (fun x => y x * y' x) (Icc x₁ x₂) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc x₁ x₂)
      (fun x _ => (hP x).continuousAt.continuousWithinAt)
      (fun x _ => (hP x).differentiableAt.differentiableWithinAt) ?_
    intro x hx
    rw [interior_Icc] at hx
    rw [(hP x).deriv]
    have := hpos x hx
    positivity
  have hzero : ∀ x ∈ Icc x₁ x₂, y x * y' x = 0 := by
    intro x hx
    have a1 := hmono ⟨le_rfl, h12.le⟩ hx hx.1
    have a2 := hmono hx ⟨h12.le, le_rfl⟩ hx.2
    simp only [h1, h2, zero_mul] at a1 a2
    exact le_antisymm a2 a1
  set m := (x₁ + x₂) / 2 with hm
  have hmI : m ∈ Ioo x₁ x₂ := ⟨by linarith, by linarith⟩
  have hev : (fun x => y x * y' x) =ᶠ[𝓝 m] fun _ => (0 : ℝ) := by
    filter_upwards [Ioo_mem_nhds hmI.1 hmI.2] with z hz using hzero z (Ioo_subset_Icc_self hz)
  have hd0 := (hasDerivAt_const m (0 : ℝ)).congr_of_eventuallyEq hev
  have := (hP m).unique hd0
  have hqm := hpos m hmI
  have h3 : q m * y m ^ 2 = 0 := by
    nlinarith [sq_nonneg (y' m), mul_nonneg hqm.le (sq_nonneg (y m))]
  have hy0 : y m = 0 := pow_eq_zero_iff two_ne_zero |>.1 ((mul_eq_zero.1 h3).resolve_left hqm.ne')
  have hy0' : y' m = 0 := by
    have h4 : y' m ^ 2 = 0 := by rw [h3] at this; linarith
    exact pow_eq_zero_iff two_ne_zero |>.1 h4
  exact (eq_zero_of_zero_data hq h hy0 hy0' x).1

/-- **At most one zero on `[0, ∞)`** for a nontrivial solution of the Airy equation `y'' = x y`. -/
theorem zeros_Ici_zero_subsingleton (h : IsSol (fun x => x) y y') (hy : ∃ x, y x ≠ 0) :
    {x | 0 ≤ x ∧ y x = 0}.Subsingleton := by
  intro a ha b hb
  by_contra hne
  rcases lt_or_gt_of_ne hne with hab | hab
  · obtain ⟨x, hx⟩ := hy
    exact hx (eq_zero_of_two_zeros_of_pos continuous_id h hab
      (fun z hz => by simp only [id]; linarith [hz.1, ha.1]) ha.2 hb.2 x)
  · obtain ⟨x, hx⟩ := hy
    exact hx (eq_zero_of_two_zeros_of_pos continuous_id h hab
      (fun z hz => by simp only [id]; linarith [hz.1, hb.1]) hb.2 ha.2 x)

end IsSol

/-- info: 'FormalResearch.Special.SturmAiry.IsSol.exists_zero_Icc_of_comparison' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.SturmAiry.IsSol.exists_zero_Icc_of_comparison

/-- info: 'FormalResearch.Special.SturmAiry.IsSol.exists_zero_Icc_of_le_neg_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.SturmAiry.IsSol.exists_zero_Icc_of_le_neg_one

/-- info: 'FormalResearch.Special.SturmAiry.IsSol.infinite_zeros_of_le_neg_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.SturmAiry.IsSol.infinite_zeros_of_le_neg_one

/-- info: 'FormalResearch.Special.SturmAiry.IsSol.infinite_zeros_Iic_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.SturmAiry.IsSol.infinite_zeros_Iic_zero

/-- info: 'FormalResearch.Special.SturmAiry.IsSol.eq_zero_of_two_zeros_of_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.SturmAiry.IsSol.eq_zero_of_two_zeros_of_pos

/-- info: 'FormalResearch.Special.SturmAiry.IsSol.zeros_Ici_zero_subsingleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.SturmAiry.IsSol.zeros_Ici_zero_subsingleton

end FormalResearch.Special.SturmAiry
