module

public import FormalResearch.Complex.Rouche
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Noshiro-Warschawski injectivity and a root-count perturbation lemma (`lem:7.7b` support)

Two generic complex-analysis facts used in the proofs of Lemma 7.7b (i)-(iii) (`langer_transport.tex`, l.12-40).

* `injOn_of_re_deriv_pos` (Noshiro-Warschawski on a convex set): if `f` is complex differentiable on a convex set
  `s` with `0 < Re f'` there, then `f` is injective on `s`.  **Proved.**  Proof: for `a ≠ b` in `s`, the real function
  `t ↦ Re (conj (a - b) * f (b + t (a - b)))` on `[0,1]` has derivative `|a - b|² Re f'(·) > 0`, so it is strictly
  monotone and cannot take equal values at `t = 0` and `t = 1` when `f a = f b`.  This uses the mean value theorem
  only; no continuity of `f'` and no integral is needed.  Restates Noshiro (1934) / Warschawski (1935) in the
  convex, one-line-derivative form; no Mathlib lemma of this form was found.
* `exists_unique_root_of_perturb`: a holomorphic `h` with `|h z - z| ≤ δ` on the circle `|z| = r` takes each value
  `w` with `‖w‖ + δ < r` exactly once in the open disc `ball 0 r`, under the extra hypothesis `0 < Re h'` on
  `closedBall 0 r` (the application has `|h' - 1| ≤ 1.2e-3`).  **Proved.**

Hypothesis changes from the brief, stated precisely:
* `h` is assumed holomorphic on the open disc `ball 0 R` for some `R > r`, not only on `closedBall 0 r`.  Rouché's
  theorem (`FormalResearch.ArgPrinciple.rouche`, which needs a neighbourhood of the closed disc) gives existence; the
  closed-disc hypothesis alone does not supply a neighbourhood.
* `hpos` is assumed on `closedBall 0 r` as in the brief; only its restriction to `ball 0 r` is used.
* Existence comes from Rouché (`FormalResearch.ArgPrinciple.rouche` with `g = id`), not from the open mapping theorem.
  Uniqueness comes from Noshiro, so it uses `hpos`; the brief's alternative route is not needed.

Negative regression (`not_injOn_sq`): `z ↦ z²` is not injective on `ball 0 1` (`(1/2)² = (-1/2)²`), so the hypothesis
`0 < Re f'` in `injOn_of_re_deriv_pos` cannot be dropped.  Here `f' = 2z` has negative real part on the left half-disc.
-/

@[expose] public section

open Complex Filter Topology Metric Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.ArgPrinciple

/-- **Noshiro-Warschawski on a convex set.** If `f` has derivative `f'` on a convex set `s` and `Re f' > 0` there,
then `f` is injective on `s`. -/
theorem injOn_of_re_deriv_pos {s : Set ℂ} (hs : Convex ℝ s) {f f' : ℂ → ℂ}
    (hf : ∀ z ∈ s, HasDerivAt f (f' z) z) (hpos : ∀ z ∈ s, 0 < (f' z).re) : Set.InjOn f s := by
  intro a ha b hb hab
  by_contra hne
  have hd : a - b ≠ 0 := sub_ne_zero.mpr hne
  have hγ : ∀ t ∈ Set.Icc (0:ℝ) 1, b + t • (a - b) ∈ s := fun t ht => hs.add_smul_sub_mem hb ha ht
  -- derivative of `t ↦ f (b + t (a - b))`
  have hg : ∀ t ∈ Set.Icc (0:ℝ) 1,
      HasDerivAt (fun t : ℝ => f (b + t • (a - b))) ((a - b) * f' (b + t • (a - b))) t := by
    intro t ht
    have hlin : HasDerivAt (fun t : ℝ => b + t • (a - b)) (a - b) t := by
      have := ((hasDerivAt_id t).smul_const (a - b)).const_add b
      simpa using this
    have := (hf _ (hγ t ht)).scomp t hlin
    simpa [smul_eq_mul, Function.comp_def] using this
  -- `|a - b|² Re f'` after multiplying by `conj (a - b)`
  have key : ∀ w : ℂ, ((starRingEnd ℂ) (a - b) * ((a - b) * w)).re = Complex.normSq (a - b) * w.re := by
    intro w
    rw [← mul_assoc, ← Complex.normSq_eq_conj_mul_self, Complex.re_ofReal_mul]
  have hH : ∀ t ∈ Set.Icc (0:ℝ) 1,
      HasDerivAt (fun t : ℝ => ((starRingEnd ℂ) (a - b) * f (b + t • (a - b))).re)
        (Complex.normSq (a - b) * (f' (b + t • (a - b))).re) t := by
    intro t ht
    have h1 := (hg t ht).const_mul ((starRingEnd ℂ) (a - b))
    have h2 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h1
    rw [← key]
    exact h2
  have hcont : ContinuousOn (fun t : ℝ => ((starRingEnd ℂ) (a - b) * f (b + t • (a - b))).re)
      (Set.Icc 0 1) := fun t ht => (hH t ht).continuousAt.continuousWithinAt
  have hmono : StrictMonoOn (fun t : ℝ => ((starRingEnd ℂ) (a - b) * f (b + t • (a - b))).re)
      (Set.Icc 0 1) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 1) hcont fun t ht => ?_
    rw [interior_Icc] at ht
    rw [(hH t (Set.Ioo_subset_Icc_self ht)).deriv]
    exact mul_pos (Complex.normSq_pos.mpr hd) (hpos _ (hγ t (Set.Ioo_subset_Icc_self ht)))
  have h01 := hmono (a := 0) (b := 1) (by norm_num) (by norm_num) zero_lt_one
  have e0 : b + (0:ℝ) • (a - b) = b := by simp
  have e1 : b + (1:ℝ) • (a - b) = a := by rw [one_smul]; abel
  dsimp only at h01
  rw [e0, e1, hab] at h01
  exact lt_irrefl _ h01

/-- **Perturbation lemma (root count on a disc).** Let `h` be holomorphic on `ball 0 R`, `r < R`, with
`‖h z - z‖ ≤ δ` on the circle `‖z‖ = r`, and `‖w‖ + δ < r`.  If `0 < Re h'` on `closedBall 0 r`, then the equation
`h z = w` has exactly one solution in the open disc `ball 0 r`.  Existence is Rouché's theorem with `g = id`. -/
theorem exists_unique_root_of_perturb {r R : ℝ} (hr : 0 < r) (hrR : r < R) {h : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h (Metric.ball 0 R))
    (δ : ℝ) (hδ : ∀ z : ℂ, ‖z‖ = r → ‖h z - z‖ ≤ δ) {w : ℂ} (hw : ‖w‖ + δ < r)
    (hpos : ∀ z ∈ Metric.closedBall (0:ℂ) r, 0 < (deriv h z).re) :
    ∃! z, z ∈ Metric.ball (0:ℂ) r ∧ h z = w := by
  -- Rouché: `h - w` and `id` have the same zero count in `ball 0 r`
  have hF : DifferentiableOn ℂ (fun z => h z - w) (Metric.ball 0 R) := hh.sub_const w
  have hG : DifferentiableOn ℂ (id : ℂ → ℂ) (Metric.ball 0 R) := differentiableOn_id
  have hineq : ∀ z ∈ Metric.sphere (0:ℂ) r, ‖(h z - w) - z‖ < ‖z‖ := by
    intro z hz
    have hn : ‖z‖ = r := by simpa using hz
    have e : h z - w - z = (h z - z) - w := by ring
    rw [e, hn]
    calc ‖(h z - z) - w‖ ≤ ‖h z - z‖ + ‖w‖ := norm_sub_le _ _
      _ ≤ δ + ‖w‖ := by linarith [hδ z hn]
      _ < r := by linarith
  have hcount : zeroCount (fun z => h z - w) 0 r = zeroCount id 0 r :=
    FormalResearch.ArgPrinciple.rouche hr hrR hF hG hineq
  -- the identity has a zero in the disc, so its zero count is positive
  have hwR : (r : ℂ) ∈ Metric.ball (0:ℂ) R := by
    rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]; exact hrR
  have hfw : (id : ℂ → ℂ) (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hfin := support_orderNat_finite hG hwR hfw hrR
  have h0id : analyticOrderNatAt (id : ℂ → ℂ) 0 = 1 := by
    simp [analyticOrderNatAt]
  have hne0 : zeroCount id 0 r ≠ 0 := by
    have h1 : zeroCount id 0 r = ∑ z ∈ hfin.toFinset, analyticOrderNatAt (id : ℂ → ℂ) z := by
      unfold zeroCount
      rw [← finsum_mem_inter_support, finsum_mem_eq_finite_toFinset_sum _ hfin]
    have hmem : (0:ℂ) ∈ Metric.ball 0 r ∩ Function.support fun z => analyticOrderNatAt (id : ℂ → ℂ) z :=
      ⟨mem_ball_self hr, by rw [Function.mem_support, h0id]; exact one_ne_zero⟩
    have h2 : analyticOrderNatAt (id : ℂ → ℂ) 0 ≤ ∑ z ∈ hfin.toFinset, analyticOrderNatAt (id : ℂ → ℂ) z :=
      Finset.single_le_sum (f := fun z => analyticOrderNatAt (id : ℂ → ℂ) z) (fun _ _ => Nat.zero_le _)
        (hfin.mem_toFinset.mpr hmem)
    rw [h0id] at h2
    rw [h1]
    omega
  -- existence: a zero of `h - w` in the disc
  have hex : ∃ z ∈ Metric.ball (0:ℂ) r, h z - w = 0 := by
    by_contra hno
    have hzero : ∀ z ∈ Metric.ball (0:ℂ) r, analyticOrderNatAt (fun z => h z - w) z = 0 := by
      intro z hz
      have hA : AnalyticAt ℂ (fun z => h z - w) z :=
        hF.analyticAt (isOpen_ball.mem_nhds (ball_subset_ball hrR.le hz))
      have hne : h z - w ≠ 0 := fun h0 => hno ⟨z, hz, h0⟩
      have hord : analyticOrderAt (fun z => h z - w) z = 0 := hA.analyticOrderAt_eq_zero.mpr hne
      simp [analyticOrderNatAt, hord]
    have h0 : zeroCount (fun z => h z - w) 0 r = 0 := finsum_mem_eq_zero_of_forall_eq_zero hzero
    rw [hcount] at h0
    exact hne0 h0
  obtain ⟨z0, hz0, hz0e⟩ := hex
  have hz0' : h z0 = w := sub_eq_zero.mp hz0e
  -- uniqueness: injectivity of `h` on the disc (Noshiro)
  have hdiff : ∀ z ∈ Metric.ball (0:ℂ) r, HasDerivAt h (deriv h z) z := fun z hz =>
    ((hh.differentiableAt (isOpen_ball.mem_nhds (ball_subset_ball hrR.le hz)))).hasDerivAt
  have hinj : Set.InjOn h (Metric.ball (0:ℂ) r) :=
    injOn_of_re_deriv_pos (convex_ball 0 r) hdiff fun z hz => hpos z (ball_subset_closedBall hz)
  exact ⟨z0, ⟨hz0, hz0'⟩, fun y hy => hinj hy.1 hz0 (hy.2.trans hz0'.symm)⟩

/-- Negative regression: `z ↦ z²` is not injective on `ball 0 1`, since `(1/2)² = (-1/2)²`.  So the hypothesis
`0 < Re f'` of `injOn_of_re_deriv_pos` cannot be dropped (here `f' = 2z` changes sign on the disc). -/
theorem not_injOn_sq : ¬ Set.InjOn (fun z : ℂ => z ^ 2) (Metric.ball (0:ℂ) 1) := by
  intro hinj
  have h1 : (1 / 2 : ℂ) ∈ Metric.ball (0:ℂ) 1 := by
    rw [mem_ball, dist_zero_right, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
    norm_num
  have h2 : (-1 / 2 : ℂ) ∈ Metric.ball (0:ℂ) 1 := by
    rw [mem_ball, dist_zero_right, show (-1 / 2 : ℂ) = ((-1 / 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by norm_num)]
    norm_num
  have := hinj h1 h2 (by norm_num)
  norm_num at this

/-- info: 'FormalResearch.SignUncertainty.injOn_of_re_deriv_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.injOn_of_re_deriv_pos

/-- info: 'FormalResearch.SignUncertainty.exists_unique_root_of_perturb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.exists_unique_root_of_perturb

end FormalResearch.SignUncertainty
