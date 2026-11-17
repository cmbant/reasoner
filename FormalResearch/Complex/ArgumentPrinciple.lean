module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Algebra.BigOperators.Finprod

/-!
# The argument principle on a circle

Generic complex analysis (no application content).  **Proved.**

Statement formalised (the argument principle for a disc, e.g. Ahlfors, *Complex Analysis*, §5.2; Conway,
*Functions of One Complex Variable*, V.3.4 with a circle as contour): let `f` be holomorphic on the open disc
`ball c R` and let `0 < r < R` (so `f` is holomorphic on a neighbourhood of the closed disc `closedBall c r`).  If `f`
has no zero on the circle `sphere c r`, then
`(2πi)⁻¹ ∮_{|z - c| = r} f'(z) / f(z) dz` is the number of zeros of `f` in `ball c r`, counted with
multiplicity (`analyticOrderNatAt`):

* `ArgPrinciple.zeroCount f c r`: the number of zeros of `f` in `ball c r` with multiplicity,
  `∑ᶠ z ∈ ball c r, analyticOrderNatAt f z`;
* `ArgPrinciple.zeros_finite`: if `f` is holomorphic on `ball c R` and not identically zero there then it has finitely
  many zeros in `closedBall c r` (`r < R`), so `zeroCount` is the honest count;
* `ArgPrinciple.circleIntegral_logDeriv`: the argument principle (headline).

Proof: induction on the number of zeros.  With no zero in `closedBall c r` the integrand is holomorphic on the disc and
Cauchy's theorem gives `0`; with a zero `a`, `f = (· - a) * dslope f a`, the order drops by one and the integrand splits
as `1 / (z - a) + g' / g`, whose first part integrates to `2πi` (`circleIntegral.integral_sub_inv_of_mem_ball`).

**Not formalised.** General contours and winding numbers, poles (the meromorphic argument principle `N - P`), and
the version on a general Jordan domain.  Mathlib has none of the argument principle, Rouché's theorem, Hurwitz's theorem
(only `TendstoLocallyUniformlyOn.differentiableOn` and `logDeriv_tendsto`), as of the pinned revision.
-/

@[expose] public section

open Complex Filter Topology Metric Set
open scoped Real

namespace FormalResearch.ArgPrinciple

/-- The number of zeros of `f` in the open disc `ball c r`, counted with multiplicity
(a finsum: it is the true count when `f` is holomorphic and not identically zero, see `zeros_finite`). -/
noncomputable def zeroCount (f : ℂ → ℂ) (c : ℂ) (r : ℝ) : ℕ :=
  ∑ᶠ z ∈ ball c r, analyticOrderNatAt f z

variable {f g : ℂ → ℂ} {c : ℂ} {r R : ℝ}

/-- A function holomorphic on a disc and non-zero at one point of it has finite analytic order everywhere on the disc. -/
lemma order_ne_top (hf : DifferentiableOn ℂ f (ball c R)) {w : ℂ} (hw : w ∈ ball c R) (hfw : f w ≠ 0)
    {z : ℂ} (hz : z ∈ ball c R) : analyticOrderAt f z ≠ ⊤ := by
  have han : AnalyticOnNhd ℂ f (ball c R) := hf.analyticOnNhd isOpen_ball
  refine han.analyticOrderAt_ne_top_of_isPreconnected (convex_ball c R).isPreconnected hw hz ?_
  rw [(han w hw).analyticOrderAt_eq_zero.mpr hfw]
  simp

/-- On the disc, the order of a non-trivial holomorphic function is non-zero exactly at its zeros. -/
lemma orderNat_ne_zero_iff (hf : DifferentiableOn ℂ f (ball c R)) {w : ℂ} (hw : w ∈ ball c R) (hfw : f w ≠ 0)
    {z : ℂ} (hz : z ∈ ball c R) : analyticOrderNatAt f z ≠ 0 ↔ f z = 0 := by
  have han : AnalyticOnNhd ℂ f (ball c R) := hf.analyticOnNhd isOpen_ball
  have hfin := order_ne_top hf hw hfw hz
  constructor
  · exact apply_eq_zero_of_analyticOrderNatAt_ne_zero
  · intro h0 h
    have h1 : analyticOrderAt f z = 0 := by
      unfold analyticOrderNatAt at h
      exact (ENat.toNat_eq_zero.mp h).resolve_right hfin
    rcases analyticOrderAt_eq_zero.mp h1 with h2 | h2
    · exact h2 (han z hz)
    · exact h2 h0

/-- A function holomorphic on `ball c R` and not identically zero has only finitely many zeros in each closed disc
`closedBall c r`, `r < R`. -/
theorem zeros_finite (hf : DifferentiableOn ℂ f (ball c R)) {w : ℂ} (hw : w ∈ ball c R) (hfw : f w ≠ 0)
    (hrR : r < R) : {z ∈ closedBall c r | f z = 0}.Finite := by
  by_contra hinf
  obtain ⟨x, hxK, hx⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinf (isCompact_closedBall c r)
    (fun z hz => hz.1)
  have hxR : x ∈ ball c R := lt_of_le_of_lt (mem_closedBall.mp hxK) hrR
  have han : AnalyticOnNhd ℂ f (ball c R) := hf.analyticOnNhd isOpen_ball
  have hfreq : ∃ᶠ z in 𝓝[≠] x, f z = 0 := by
    rw [accPt_iff_frequently_nhdsNE] at hx
    exact hx.mono fun z hz => hz.2
  have := han.eqOn_zero_of_preconnected_of_frequently_eq_zero (convex_ball c R).isPreconnected hxR hfreq hw
  exact hfw this


/-- Cauchy: the logarithmic derivative of a holomorphic function with no zero in `closedBall c r` has zero circle
integral. -/
lemma circleIntegral_logDeriv_of_no_zero (hr : 0 < r) (hrR : r < R) (hf : DifferentiableOn ℂ f (ball c R))
    (hne : ∀ z ∈ closedBall c r, f z ≠ 0) : (∮ z in C(c, r), deriv f z / f z) = 0 := by
  have hsub : closedBall c r ⊆ ball c R := closedBall_subset_ball hrR
  have han : AnalyticOnNhd ℂ f (ball c R) := hf.analyticOnNhd isOpen_ball
  have hd' : AnalyticOnNhd ℂ (deriv f) (ball c R) := han.deriv
  refine circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le Set.countable_empty ?_ ?_
  · exact (hd'.continuousOn.mono hsub).div (han.continuousOn.mono hsub) hne
  · intro z hz
    have hzR : z ∈ ball c R := hsub (ball_subset_closedBall hz.1)
    exact ((hd' z hzR).differentiableAt).div (han z hzR).differentiableAt (hne z (ball_subset_closedBall hz.1))

/-- If `f ≠ 0` on the circle, it is non-zero at some point of the disc `ball c R`. -/
lemma exists_nonzero_of_sphere (hr : 0 < r) (hrR : r < R) (hne : ∀ z ∈ sphere c r, f z ≠ 0) :
    c + r ∈ ball c R ∧ f (c + r) ≠ 0 := by
  have h1 : c + (r : ℂ) ∈ sphere c r := by simp [abs_of_pos hr]
  exact ⟨by simpa [mem_ball, abs_of_pos hr] using hrR, hne _ h1⟩

/-- The multiplicity-weighted count is a finsum over a finite set. -/
lemma support_orderNat_finite (hf : DifferentiableOn ℂ f (ball c R)) {w : ℂ} (hw : w ∈ ball c R) (hfw : f w ≠ 0)
    (hrR : r < R) : (ball c r ∩ Function.support fun z => analyticOrderNatAt f z).Finite := by
  refine (zeros_finite hf hw hfw hrR).subset fun z hz => ⟨ball_subset_closedBall hz.1, ?_⟩
  exact (orderNat_ne_zero_iff hf hw hfw ((ball_subset_ball hrR.le) hz.1)).mp hz.2

/-- **Argument principle on a circle.**  `f` holomorphic on `ball c R`, `0 < r < R`, `f ≠ 0` on `sphere c r`:
`∮_{|z-c|=r} f'/f = 2πi · (number of zeros of f in ball c r, with multiplicity)`. -/
theorem circleIntegral_logDeriv (hr : 0 < r) (hrR : r < R) (hf : DifferentiableOn ℂ f (ball c R))
    (hne : ∀ z ∈ sphere c r, f z ≠ 0) :
    (∮ z in C(c, r), deriv f z / f z) = 2 * π * I * (zeroCount f c r : ℂ) := by
  induction hN : zeroCount f c r generalizing f with
  | zero =>
    obtain ⟨hw, hfw⟩ := exists_nonzero_of_sphere hr hrR hne
    have hfin := support_orderNat_finite hf hw hfw hrR
    have hall : ∀ z ∈ ball c r, analyticOrderNatAt f z = 0 := by
      intro z hz
      by_contra hz0
      have hmem : z ∈ ball c r ∩ Function.support fun z => analyticOrderNatAt f z := ⟨hz, hz0⟩
      have h1 : zeroCount f c r = ∑ z ∈ hfin.toFinset, analyticOrderNatAt f z := by
        unfold zeroCount
        rw [← finsum_mem_inter_support, finsum_mem_eq_finite_toFinset_sum _ hfin]
      have h2 : analyticOrderNatAt f z ≤ ∑ z ∈ hfin.toFinset, analyticOrderNatAt f z :=
        Finset.single_le_sum (f := fun z => analyticOrderNatAt f z) (fun _ _ => Nat.zero_le _)
          (hfin.mem_toFinset.mpr hmem)
      have := Nat.pos_of_ne_zero hz0
      omega
    have hnz : ∀ z ∈ closedBall c r, f z ≠ 0 := by
      intro z hz
      rcases (mem_closedBall.mp hz).lt_or_eq with h | h
      · intro h0
        have hzR : z ∈ ball c R := ball_subset_ball hrR.le (mem_ball.mpr h)
        exact ((orderNat_ne_zero_iff hf hw hfw hzR).mpr h0) (hall z (mem_ball.mpr h))
      · exact hne z (mem_sphere.mpr h)
    rw [circleIntegral_logDeriv_of_no_zero hr hrR hf hnz]
    simp
  | succ N ih =>
    obtain ⟨hw, hfw⟩ := exists_nonzero_of_sphere hr hrR hne
    obtain ⟨a, ha, hfa⟩ : ∃ a ∈ ball c r, analyticOrderNatAt f a ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have : zeroCount f c r = 0 := finsum_mem_eq_zero_of_forall_eq_zero hcon
      omega
    have haR : a ∈ ball c R := ball_subset_ball hrR.le ha
    have hfa0 : f a = 0 := (orderNat_ne_zero_iff hf hw hfw haR).mp hfa
    set g := dslope f a with hgdef
    have hg : DifferentiableOn ℂ g (ball c R) :=
      (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds haR)).2 hf
    have hfg : ∀ z, f z = (z - a) * g z := fun z => by
      have := sub_smul_dslope f a z
      rw [smul_eq_mul, hfa0, sub_zero] at this
      exact this.symm
    have hfeq : f = (fun z => z - a) * g := funext hfg
    have hza : ∀ z ∈ sphere c r, z ≠ a := by
      intro z hz hza
      have h1 : dist z c = r := mem_sphere.mp hz
      have h2 : dist a c < r := mem_ball.mp ha
      rw [hza] at h1
      linarith
    have hgne : ∀ z ∈ sphere c r, g z ≠ 0 := by
      intro z hz h0
      exact hne z hz (by rw [hfg, h0, mul_zero])
    obtain ⟨-, hgw⟩ : c + r ∈ ball c R ∧ g (c + r) ≠ 0 := exists_nonzero_of_sphere hr hrR hgne
    have hanf : AnalyticOnNhd ℂ f (ball c R) := hf.analyticOnNhd isOpen_ball
    have hang : AnalyticOnNhd ℂ g (ball c R) := hg.analyticOnNhd isOpen_ball
    have hord : ∀ z ∈ ball c R,
        analyticOrderNatAt f z = analyticOrderNatAt g z + (if z = a then 1 else 0) := by
      intro z hz
      have h1 : analyticOrderAt (fun z : ℂ => z - a) z ≠ ⊤ := by
        by_cases hza : z = a
        · subst hza; simp
        · simp [hza]
      have h2 := order_ne_top hg hw hgw hz
      have h3 : AnalyticAt ℂ (fun z : ℂ => z - a) z := by fun_prop
      rw [hfeq, analyticOrderNatAt_mul h3 (hang z hz) h1 h2]
      by_cases hza : z = a
      · subst hza; simp [analyticOrderNatAt, add_comm]
      · simp [hza, analyticOrderNatAt]
    have hfinG := support_orderNat_finite hg hw hgw hrR
    have hfinI : (ball c r ∩ Function.support fun z => if z = a then (1 : ℕ) else 0).Finite :=
      (Set.finite_singleton a).subset fun z hz => by
        by_contra h
        exact hz.2 (by simp [Set.mem_singleton_iff.not.mp h] ) 
    have hone : ∑ᶠ z ∈ ball c r, (if z = a then (1 : ℕ) else 0) = 1 := by
      have : ball c r ∩ Function.support (fun z => if z = a then (1:ℕ) else 0) = {a} := by
        ext z; by_cases h : z = a <;> simp [h, ha]
      rw [← finsum_mem_inter_support, this, finsum_mem_singleton]; simp
    have hcount : zeroCount f c r = zeroCount g c r + 1 := by
      unfold zeroCount
      rw [finsum_mem_congr rfl (fun z hz => hord z (ball_subset_ball hrR.le hz)),
        finsum_mem_add_distrib' hfinG hfinI, hone]
    have hN' : zeroCount g c r = N := by omega
    have ihg := ih hg hgne hN'
    have hcont1 : ContinuousOn (fun z => (z - a)⁻¹) (sphere c r) :=
      ContinuousOn.inv₀ (by fun_prop) fun z hz => sub_ne_zero.mpr (hza z hz)
    have hsub : sphere c r ⊆ ball c R := (sphere_subset_closedBall).trans (closedBall_subset_ball hrR)
    have hcont2 : ContinuousOn (fun z => deriv g z / g z) (sphere c r) :=
       (hang.deriv.continuousOn.mono hsub).div (hang.continuousOn.mono hsub) hgne
    have hcongr : (∮ z in C(c, r), deriv f z / f z) =
        ∮ z in C(c, r), ((z - a)⁻¹ + deriv g z / g z) := by
      refine circleIntegral.integral_congr hr.le fun z hz => ?_
      have hzR := hsub hz
      have hdg : HasDerivAt g (deriv g z) z := (hg.differentiableAt (isOpen_ball.mem_nhds hzR)).hasDerivAt
      have hdf : deriv f z = g z + (z - a) * deriv g z := by
        have := (((hasDerivAt_id z).sub_const a).mul hdg)
        rw [hfeq]
        simpa using this.deriv
      have hz1 : z - a ≠ 0 := sub_ne_zero.mpr (hza z hz)
      have hz2 := hgne z hz
      simp only [hdf, hfg z]
      field_simp
    rw [hcongr, circleIntegral.integral_add (hcont1.circleIntegrable hr.le) (hcont2.circleIntegrable hr.le),
      circleIntegral.integral_sub_inv_of_mem_ball ha, ihg]
    push_cast
    ring

/-- info: 'FormalResearch.ArgPrinciple.zeros_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ArgPrinciple.zeros_finite

/-- info: 'FormalResearch.ArgPrinciple.circleIntegral_logDeriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ArgPrinciple.circleIntegral_logDeriv

end FormalResearch.ArgPrinciple
