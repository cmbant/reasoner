module

public import FormalResearch.SignUncertainty.FctMomentCore
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Topology.Order.IntermediateValue

/-!
# `fct:moment-solver`: finite moment correction on a fixed scaled interval (F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma `fct:moment-solver` (lines 128–165).

For any fixed `N ≥ 1`, there is a threshold `τ₀ > 0` and an explicit linear operator
`momentSolver N τ₁ : (ℝ → ℝ) → (ℝ → ℝ)` (defined for `0 < τ₁ ≤ τ₀`) such that for any real even
smooth target `f` on `[-3τ₁, 3τ₁]` with `f(0) = 0` and `|f^{(r)}(t)| ≤ C_f r * M * τ₁^{2-r}`,
the output `v = momentSolver N τ₁ f` is real, even, `C^∞`, supported in `(-10τ₁, 10τ₁)`,
agrees with `f` on `[-2τ₁, 2τ₁]`, has zero moments `ℳ_k[v] = 0` (`0 ≤ k < N`) and hence
vanishing odd phase derivatives `ϑ_D^{(2k+1)}(0) = 0` (`0 ≤ k < N`), satisfies
`|v^{(r)}(t)| ≤ C_v r * M * τ₁^{2-r}`, `‖v‖₁ ≤ C_L1 * M * τ₁^3`, and its boundary phase satisfies
`|ϑ_D^{(r)}(t)| ≤ C_th r * M * τ₁^{2-r} * min 1 ((|t|/τ₁)^{max(0, 2N+1-r)})` for `|t| ≤ 12τ₁`.

Class: proved, no hypotheses. Kernel-dependence guards at the end.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real BigOperators Matrix

namespace FormalResearch.SignUncertainty.FctMoment

/-! ### Fixed even cutoff `η_cut` and bumps `φ_j` -/

/-- Underlying smooth bump on `ℝ` equal to `1` on `[-2, 2]` and supported in `(-5/2, 5/2)`. -/
noncomputable def etaBump : ContDiffBump (0 : ℝ) :=
  ⟨2, 5 / 2, by norm_num, by norm_num⟩

/-- Fixed even smooth cutoff `η_cut` equal to `1` on `[-2, 2]` and supported in `(-5/2, 5/2) ⊂ (-3, 3)`. -/
noncomputable def etaCut (x : ℝ) : ℝ := (etaBump x + etaBump (-x)) / 2

lemma etaCut_even (x : ℝ) : etaCut (-x) = etaCut x := by
  unfold etaCut; rw [neg_neg]; ring

lemma contDiff_etaCut : ContDiff ℝ (⊤ : ℕ∞) etaCut := by
  unfold etaCut
  exact (etaBump.contDiff.add (etaBump.contDiff.comp contDiff_neg)).div_const 2

lemma etaCut_eq_one {x : ℝ} (hx : |x| ≤ 2) : etaCut x = 1 := by
  unfold etaCut
  have h1 : x ∈ Metric.closedBall (0 : ℝ) etaBump.rIn := by
    simpa [etaBump, Real.norm_eq_abs] using hx
  have h2 : -x ∈ Metric.closedBall (0 : ℝ) etaBump.rIn := by
    simpa [etaBump, Real.norm_eq_abs] using hx
  rw [etaBump.one_of_mem_closedBall h1, etaBump.one_of_mem_closedBall h2]
  norm_num

lemma etaCut_eq_zero {x : ℝ} (hx : 5 / 2 ≤ |x|) : etaCut x = 0 := by
  unfold etaCut
  have h1 : x ∉ Function.support etaBump := by
    rw [etaBump.support_eq]
    simp only [etaBump, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, not_lt]
    exact hx
  have h2 : -x ∉ Function.support etaBump := by
    rw [etaBump.support_eq]
    simp only [etaBump, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_neg, not_lt]
    exact hx
  rw [Function.notMem_support.mp h1, Function.notMem_support.mp h2]
  norm_num

lemma hasCompactSupport_etaCut : HasCompactSupport etaCut := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -(5 / 2 : ℝ)) (b := 5 / 2)) ?_
  intro x hx
  by_contra hnot
  have hge : 5 / 2 ≤ |x| := by
    rw [mem_Icc] at hnot
    push Not at hnot
    rcases le_or_gt (-(5 / 2 : ℝ)) x with h | h
    · rw [abs_of_nonneg (by linarith [hnot h])]; linarith [hnot h]
    · rw [abs_of_neg (by linarith)]; linarith
  exact hx (etaCut_eq_zero hge)

/-- Center of the `j`-th bump interval in `(3, 8)`. -/
noncomputable def bumpCenter (N : ℕ) (j : Fin N) : ℝ :=
  3 + 5 * ((j.1 : ℝ) + 1 / 2) / (N : ℝ)

/-- Radius of the `j`-th bump in `(3, 8)`. -/
noncomputable def bumpRadius (N : ℕ) : ℝ := 5 / (4 * (N : ℝ))

lemma bumpRadius_pos {N : ℕ} (hN : 0 < N) : 0 < bumpRadius N := by
  unfold bumpRadius
  have : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  positivity

/-- Raw smooth bump centered at `bumpCenter N j` with outer radius `bumpRadius N`. -/
noncomputable def rawBump (N : ℕ) (j : Fin N) : ContDiffBump (bumpCenter N j) :=
  ⟨bumpRadius N / 2, bumpRadius N,
    half_pos (bumpRadius_pos (Nat.pos_of_ne_zero (Fin.pos j).ne')),
    half_lt_self (bumpRadius_pos (Nat.pos_of_ne_zero (Fin.pos j).ne'))⟩

lemma rawBump_interval_bounds (N : ℕ) (j : Fin N) :
    3 + 5 * (j.1 : ℝ) / (N : ℝ) < bumpCenter N j - bumpRadius N ∧
    bumpCenter N j + bumpRadius N < 3 + 5 * ((j.1 : ℝ) + 1) / (N : ℝ) := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Fin.pos j).ne')
  unfold bumpCenter bumpRadius
  constructor <;> field_simp <;> linarith

lemma rawBump_support_subset (N : ℕ) (j : Fin N) :
    Function.support (rawBump N j) ⊆ Ioo (3 + 5 * (j.1 : ℝ) / (N : ℝ)) (3 + 5 * ((j.1 : ℝ) + 1) / (N : ℝ)) := by
  intro u hu
  have hmem : u ∈ Metric.ball (bumpCenter N j) (bumpRadius N) := by
    change u ∈ Metric.ball (bumpCenter N j) (rawBump N j).rOut
    rwa [← (rawBump N j).support_eq]
  rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hmem
  have hb := rawBump_interval_bounds N j
  exact ⟨by linarith [hmem.1, hb.1], by linarith [hmem.2, hb.2]⟩

lemma rawBump_support_subset_3_8 (N : ℕ) (j : Fin N) :
    Function.support (rawBump N j) ⊆ Ioo (3 : ℝ) 8 := by
  intro u hu
  have h := rawBump_support_subset N j hu
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Fin.pos j).ne')
  have hj0 : (0 : ℝ) ≤ j.1 := Nat.cast_nonneg _
  have hj1 : ((j.1 : ℝ) + 1) / (N : ℝ) ≤ 1 := by
    rw [div_le_one hN]
    exact_mod_cast j.isLt
  have h5 : 5 * ((j.1 : ℝ) + 1) / (N : ℝ) ≤ 5 := by
    rw [mul_div_assoc]; linarith
  exact ⟨by linarith [h.1, show (0 : ℝ) ≤ 5 * (j.1 : ℝ) / (N : ℝ) by positivity],
    by linarith [h.2, h5]⟩

lemma rawBump_integral_pos (N : ℕ) (j : Fin N) :
    0 < ∫ u in Ioi (0 : ℝ), (rawBump N j) u := by
  set c := bumpCenter N j
  set r := bumpRadius N
  have hr : 0 < r := bumpRadius_pos (Nat.pos_of_ne_zero (Fin.pos j).ne')
  have hb := rawBump_interval_bounds N j
  have hsub : Icc (c - r / 2) (c + r / 2) ⊆ Ioi (0 : ℝ) := by
    intro u hu
    have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Fin.pos j).ne')
    have : (0 : ℝ) ≤ 5 * (j.1 : ℝ) / (N : ℝ) := by positivity
    change 0 < u
    linarith [hu.1, hb.1, hr]
  have hint : IntegrableOn (rawBump N j) (Ioi (0 : ℝ)) :=
    ((rawBump N j).continuous.integrable_of_hasCompactSupport (rawBump N j).hasCompactSupport).integrableOn
  have hle : ∫ u in Icc (c - r / 2) (c + r / 2), (rawBump N j) u ≤
      ∫ u in Ioi (0 : ℝ), (rawBump N j) u :=
    setIntegral_mono_set hint (Filter.Eventually.of_forall fun u => (rawBump N j).nonneg)
      (Filter.Eventually.of_forall hsub)
  have hval : ∫ u in Icc (c - r / 2) (c + r / 2), (rawBump N j) u = r := by
    have hcongr : EqOn (rawBump N j) (fun _ => (1 : ℝ)) (Icc (c - r / 2) (c + r / 2)) := by
      intro u hu
      refine (rawBump N j).one_of_mem_closedBall ?_
      change u ∈ Metric.closedBall c (r / 2)
      rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
      exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
    rw [setIntegral_congr_fun measurableSet_Icc hcongr, setIntegral_const, smul_eq_mul, mul_one,
      Measure.real_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
    ring
  linarith

/-- Even normalized smooth bump `φ_j` supported in `(-8, -3) ∪ (3, 8)` with `∫_0^∞ φ_j = 1`. -/
noncomputable def bumpPhi (N : ℕ) (j : Fin N) (u : ℝ) : ℝ :=
  ((rawBump N j) u + (rawBump N j) (-u)) / ∫ s in Ioi (0 : ℝ), (rawBump N j) s

lemma bumpPhi_even (N : ℕ) (j : Fin N) (u : ℝ) : bumpPhi N j (-u) = bumpPhi N j u := by
  unfold bumpPhi; rw [neg_neg]; ring

lemma contDiff_bumpPhi (N : ℕ) (j : Fin N) : ContDiff ℝ (⊤ : ℕ∞) (bumpPhi N j) := by
  unfold bumpPhi
  exact ((rawBump N j).contDiff.add ((rawBump N j).contDiff.comp contDiff_neg)).div_const _

lemma bumpPhi_nonneg (N : ℕ) (j : Fin N) (u : ℝ) : 0 ≤ bumpPhi N j u :=
  div_nonneg (add_nonneg (rawBump N j).nonneg (rawBump N j).nonneg) (rawBump_integral_pos N j).le

lemma bumpPhi_eq_of_nonneg (N : ℕ) (j : Fin N) {u : ℝ} (hu : 0 ≤ u) :
    bumpPhi N j u = (rawBump N j) u / ∫ s in Ioi (0 : ℝ), (rawBump N j) s := by
  unfold bumpPhi
  have hneg : (rawBump N j) (-u) = 0 := by
    by_contra hne
    have h3 := (rawBump_support_subset_3_8 N j hne).1
    linarith
  rw [hneg, add_zero]

lemma bumpPhi_zero_of_le_three (N : ℕ) (j : Fin N) {u : ℝ} (hu0 : 0 ≤ u) (hu3 : u ≤ 3) :
    bumpPhi N j u = 0 := by
  rw [bumpPhi_eq_of_nonneg N j hu0]
  have hz : (rawBump N j) u = 0 := by
    by_contra hne
    linarith [(rawBump_support_subset_3_8 N j hne).1]
  rw [hz, zero_div]

lemma bumpPhi_zero_of_abs_ge_eight (N : ℕ) (j : Fin N) {u : ℝ} (hu : 8 ≤ |u|) :
    bumpPhi N j u = 0 := by
  unfold bumpPhi
  have hz1 : (rawBump N j) u = 0 := by
    by_contra hne
    have h := rawBump_support_subset_3_8 N j hne
    have : |u| < 8 := abs_lt.mpr ⟨by linarith [h.1], h.2⟩
    linarith
  have hz2 : (rawBump N j) (-u) = 0 := by
    by_contra hne
    have h := rawBump_support_subset_3_8 N j hne
    have : |-u| < 8 := abs_lt.mpr ⟨by linarith [h.1], h.2⟩
    rw [abs_neg] at this; linarith
  rw [hz1, hz2, add_zero, zero_div]

lemma hasCompactSupport_bumpPhi (N : ℕ) (j : Fin N) : HasCompactSupport (bumpPhi N j) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (-8 : ℝ)) (b := 8)) ?_
  intro u hu
  by_contra hnot
  have hge : 8 ≤ |u| := by
    rw [mem_Icc] at hnot; push Not at hnot
    rcases le_or_gt (-8 : ℝ) u with h | h
    · rw [abs_of_nonneg (by linarith [hnot h])]; linarith [hnot h]
    · rw [abs_of_neg (by linarith)]; linarith
  exact hu (bumpPhi_zero_of_abs_ge_eight N j hge)

lemma bumpPhi_integral_Ioi (N : ℕ) (j : Fin N) :
    ∫ u in Ioi (0 : ℝ), bumpPhi N j u = 1 := by
  have hcongr : EqOn (bumpPhi N j)
      (fun u => (rawBump N j) u / ∫ s in Ioi (0 : ℝ), (rawBump N j) s) (Ioi 0) :=
    fun u hu => bumpPhi_eq_of_nonneg N j (mem_Ioi.mp hu).le
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_div,
    div_self (rawBump_integral_pos N j).ne']

/-! ### Moment matrices `Ã(τ₁)` and `Ã(0)` and invertibility -/

/-- Normalized moment matrix `Ã_{kj}(τ₁)` of `fct:moment-solver`. -/
noncomputable def momentMatrix (N : ℕ) (τ₁ : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun k j =>
    (π ^ 2 * τ₁ ^ (1 + 2 * k.1) / ((2 * k.1 + 1).factorial : ℝ)) *
      fctMoment k.1 (fun t => bumpPhi N j (t / τ₁))

/-- Limiting moment matrix `Ã_{kj}(0) = ∫_0^∞ φ_j(u) u^{-2-2k} du`. -/
noncomputable def momentMatrix0 (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun k j =>
    ∫ u in Ioi (0 : ℝ), bumpPhi N j u / u ^ (2 + 2 * k.1)

/-- `det Ã(0) ≠ 0` by polynomial root counting on the `N` disjoint bump intervals. -/
lemma momentMatrix0_det_ne_zero (N : ℕ) : (momentMatrix0 N).det ≠ 0 := by
  intro hdet
  have hdetT : (momentMatrix0 N)ᵀ.det = 0 := by rw [Matrix.det_transpose]; exact hdet
  obtain ⟨b, hb_ne, hb_mul⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdetT
  -- Define `P(u) = ∑_k b_k / u^{2+2k}`
  let P : ℝ → ℝ := fun u => ∑ k : Fin N, b k / u ^ (2 + 2 * k.1)
  have hP_cont : ContinuousOn P (Ioi 0) := by
    have hsum : ∀ (s : Finset (Fin N)), ContinuousOn (fun u => ∑ k ∈ s, b k / u ^ (2 + 2 * k.1)) (Ioi 0) := by
      intro s
      induction s using Finset.cons_induction with
      | empty => simpa using continuousOn_const
      | cons k s hks ih =>
        simp_rw [Finset.sum_cons]
        exact (continuousOn_const.div (continuousOn_id.pow _) fun u hu => pow_ne_zero _ (mem_Ioi.mp hu).ne').add ih
    exact hsum Finset.univ
  -- For each `j`, `∫_{u>0} φ_j(u) P(u) du = 0`
  have hint_zero : ∀ j : Fin N, ∫ u in Ioi (0 : ℝ), bumpPhi N j u * P u = 0 := by
    intro j
    have hrow : ∑ k : Fin N, momentMatrix0 N k j * b k = 0 := by
      have := congrFun hb_mul j
      simpa [Matrix.mulVec, dotProduct, Matrix.transpose_apply] using this
    have hint_k : ∀ k : Fin N, IntegrableOn (fun u : ℝ => bumpPhi N j u * (b k / u ^ (2 + 2 * k.1))) (Ioi 0) := by
      intro k
      have hsupp : HasCompactSupport (fun u : ℝ => if u ∈ Ioi (0 : ℝ) then bumpPhi N j u * (b k / u ^ (2 + 2 * k.1)) else 0) := by
        refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (0 : ℝ)) (b := 8)) ?_
        intro u hu
        simp only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at hu
        have hu0 : 0 < u := hu.1
        have hphi : bumpPhi N j u ≠ 0 := left_ne_zero_of_mul hu.2
        have hlt8 : u < 8 := by
          by_contra hge
          exact hphi (bumpPhi_zero_of_abs_ge_eight N j (by rw [abs_of_pos hu0]; linarith))
        exact ⟨hu0.le, hlt8.le⟩
      have hcont : ContinuousOn (fun u : ℝ => bumpPhi N j u * (b k / u ^ (2 + 2 * k.1))) (Icc (3 : ℝ) 8) :=
        ((contDiff_bumpPhi N j).continuous.continuousOn).mul
          (continuousOn_const.div (continuousOn_id.pow _) fun u hu => pow_ne_zero _ (by linarith [hu.1]))
      have hi38 : IntegrableOn (fun u : ℝ => bumpPhi N j u * (b k / u ^ (2 + 2 * k.1))) (Icc (3 : ℝ) 8) :=
        hcont.integrableOn_Icc
      refine IntegrableOn.mono_set (t := Icc (3 : ℝ) 8 ∪ (Ioi 0 \ Icc 3 8)) ?_ (fun u hu => by
        by_cases h : u ∈ Icc (3 : ℝ) 8 <;> [exact Or.inl h; exact Or.inr ⟨hu, h⟩])
      refine hi38.union (IntegrableOn.congr_fun (integrableOn_zero) (fun u hu => ?_)
        (measurableSet_Ioi.diff measurableSet_Icc))
      have hu0 : 0 < u := hu.1
      have hnot : u ∉ Icc (3 : ℝ) 8 := hu.2
      rw [mem_Icc] at hnot; push Not at hnot
      rcases le_or_gt u 3 with h3 | h3
      · rw [bumpPhi_zero_of_le_three N j hu0.le h3, zero_mul]
      · rw [bumpPhi_zero_of_abs_ge_eight N j (by rw [abs_of_pos hu0]; linarith [hnot h3.le]), zero_mul]
    have hsum : (fun u : ℝ => bumpPhi N j u * P u) =
        fun u => ∑ k : Fin N, bumpPhi N j u * (b k / u ^ (2 + 2 * k.1)) := by
      ext u; simp only [P, Finset.mul_sum]
    have hint_sum : ∀ (s : Finset (Fin N)),
        IntegrableOn (fun u : ℝ => ∑ k ∈ s, bumpPhi N j u * (b k / u ^ (2 + 2 * k.1))) (Ioi 0) ∧
        ∫ u in Ioi (0 : ℝ), ∑ k ∈ s, bumpPhi N j u * (b k / u ^ (2 + 2 * k.1)) =
          ∑ k ∈ s, ∫ u in Ioi (0 : ℝ), bumpPhi N j u * (b k / u ^ (2 + 2 * k.1)) := by
      intro s
      induction s using Finset.cons_induction with
      | empty => exact ⟨by simp, by simp⟩
      | cons k s hks ih =>
        simp_rw [Finset.sum_cons]
        exact ⟨(hint_k k).add ih.1, by rw [integral_add (hint_k k) ih.1, ih.2]⟩
    rw [hsum, (hint_sum Finset.univ).2]
    have hterm : ∀ k : Fin N, ∫ u in Ioi (0 : ℝ), bumpPhi N j u * (b k / u ^ (2 + 2 * k.1)) =
        momentMatrix0 N k j * b k := by
      intro k
      unfold momentMatrix0
      simp only [Matrix.of_apply]
      rw [← integral_mul_const]
      refine setIntegral_congr_fun measurableSet_Ioi fun u _ => by ring
    simp_rw [hterm]
    exact hrow
  -- On each bump interval `[c_j - r_N, c_j + r_N]`, `P` must have a zero `u_j`
  have hexists_root : ∀ j : Fin N,
      ∃ u ∈ Icc (bumpCenter N j - bumpRadius N) (bumpCenter N j + bumpRadius N), P u = 0 := by
    intro j
    set c := bumpCenter N j
    set r := bumpRadius N
    have hr : 0 < r := bumpRadius_pos (Nat.pos_of_ne_zero (Fin.pos j).ne')
    have hb := rawBump_interval_bounds N j
    have hsub : Icc (c - r) (c + r) ⊆ Ioi (0 : ℝ) := by
      intro u hu
      have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Fin.pos j).ne')
      have : (0 : ℝ) ≤ 5 * (j.1 : ℝ) / (N : ℝ) := by positivity
      change 0 < u
      linarith [hu.1, hb.1]
    have hraw_zero_outside : ∀ u, u ∉ Icc (c - r) (c + r) → (rawBump N j) u = 0 := by
      intro u hu
      refine Function.notMem_support.mp ?_
      rw [(rawBump N j).support_eq]
      intro hball
      apply hu
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hball
      change -r < u - c ∧ u - c < r at hball
      exact ⟨by linarith [hball.1], by linarith [hball.2]⟩
    have hnot_pos : ¬ (∀ u ∈ Icc (c - r) (c + r), 0 < P u) := by
      intro hpos
      have hmin_exists := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr (by linarith : c - r ≤ c + r))
        (hP_cont.mono hsub)
      obtain ⟨u₀, hu₀, hmin⟩ := hmin_exists
      have hm_pos : 0 < P u₀ := hpos u₀ hu₀
      have hge : ∀ u ∈ Ioi (0 : ℝ), P u₀ * bumpPhi N j u ≤ bumpPhi N j u * P u := by
        intro u hu
        by_cases hmem : u ∈ Icc (c - r) (c + r)
        · have hpu : P u₀ ≤ P u := hmin hmem
          nlinarith [bumpPhi_nonneg N j u]
        · rw [bumpPhi_eq_of_nonneg N j (mem_Ioi.mp hu).le, hraw_zero_outside u hmem, zero_div, mul_zero, zero_mul]
      have hint_phi : IntegrableOn (bumpPhi N j) (Ioi (0 : ℝ)) :=
        ((contDiff_bumpPhi N j).continuous.integrable_of_hasCompactSupport (hasCompactSupport_bumpPhi N j)).integrableOn
      have hint_prod : IntegrableOn (fun u => bumpPhi N j u * P u) (Ioi (0 : ℝ)) := by
        have hcont : ContinuousOn (fun u => bumpPhi N j u * P u) (Icc (c - r) (c + r)) :=
          (contDiff_bumpPhi N j).continuous.continuousOn.mul (hP_cont.mono hsub)
        refine IntegrableOn.mono_set (t := Icc (c - r) (c + r) ∪ (Ioi 0 \ Icc (c - r) (c + r)))
          (hcont.integrableOn_Icc.union (IntegrableOn.congr_fun integrableOn_zero (fun u hu => ?_)
            (measurableSet_Ioi.diff measurableSet_Icc)))
          (fun u hu => by by_cases h : u ∈ Icc (c - r) (c + r) <;> [exact Or.inl h; exact Or.inr ⟨hu, h⟩])
        rw [bumpPhi_eq_of_nonneg N j (mem_Ioi.mp hu.1).le, hraw_zero_outside u hu.2, zero_div, zero_mul]
      have hle := setIntegral_mono_on (hint_phi.const_mul (P u₀)) hint_prod measurableSet_Ioi hge
      rw [integral_const_mul, bumpPhi_integral_Ioi, mul_one, hint_zero j] at hle
      linarith
    have hnot_neg : ¬ (∀ u ∈ Icc (c - r) (c + r), P u < 0) := by
      intro hneg
      have hmax_exists := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr (by linarith : c - r ≤ c + r))
        (hP_cont.mono hsub)
      obtain ⟨u₀, hu₀, hmax⟩ := hmax_exists
      have hm_neg : P u₀ < 0 := hneg u₀ hu₀
      have hle_pt : ∀ u ∈ Ioi (0 : ℝ), bumpPhi N j u * P u ≤ P u₀ * bumpPhi N j u := by
        intro u hu
        by_cases hmem : u ∈ Icc (c - r) (c + r)
        · have hpu : P u ≤ P u₀ := hmax hmem
          nlinarith [bumpPhi_nonneg N j u]
        · rw [bumpPhi_eq_of_nonneg N j (mem_Ioi.mp hu).le, hraw_zero_outside u hmem, zero_div, mul_zero, zero_mul]
      have hint_phi : IntegrableOn (bumpPhi N j) (Ioi (0 : ℝ)) :=
        ((contDiff_bumpPhi N j).continuous.integrable_of_hasCompactSupport (hasCompactSupport_bumpPhi N j)).integrableOn
      have hint_prod : IntegrableOn (fun u => bumpPhi N j u * P u) (Ioi (0 : ℝ)) := by
        have hcont : ContinuousOn (fun u => bumpPhi N j u * P u) (Icc (c - r) (c + r)) :=
          (contDiff_bumpPhi N j).continuous.continuousOn.mul (hP_cont.mono hsub)
        refine IntegrableOn.mono_set (t := Icc (c - r) (c + r) ∪ (Ioi 0 \ Icc (c - r) (c + r)))
          (hcont.integrableOn_Icc.union (IntegrableOn.congr_fun integrableOn_zero (fun u hu => ?_)
            (measurableSet_Ioi.diff measurableSet_Icc)))
          (fun u hu => by by_cases h : u ∈ Icc (c - r) (c + r) <;> [exact Or.inl h; exact Or.inr ⟨hu, h⟩])
        rw [bumpPhi_eq_of_nonneg N j (mem_Ioi.mp hu.1).le, hraw_zero_outside u hu.2, zero_div, zero_mul]
      have hle := setIntegral_mono_on hint_prod (hint_phi.const_mul (P u₀)) measurableSet_Ioi hle_pt
      rw [integral_const_mul, bumpPhi_integral_Ioi, mul_one, hint_zero j] at hle
      linarith
    push Not at hnot_pos hnot_neg
    obtain ⟨x, hx, hPx⟩ := hnot_pos
    obtain ⟨y, hy, hPy⟩ := hnot_neg
    have hmem0 : (0 : ℝ) ∈ Icc (P x) (P y) := ⟨hPx, hPy⟩
    have hsub_xy : uIcc x y ⊆ Icc (c - r) (c + r) := Set.uIcc_subset_Icc hx hy
    obtain ⟨u, hu, hPu⟩ := intermediate_value_uIcc (hP_cont.mono (hsub_xy.trans hsub))
      (Icc_subset_uIcc hmem0)
    exact ⟨u, hsub_xy hu, hPu⟩
  choose u hu_mem hu_zero using hexists_root
  -- The `N` points `u_j^2` are strictly increasing, hence distinct roots of `Q` of degree `< N`
  have hu_pos : ∀ j : Fin N, 0 < u j := fun j => by
    have hb := rawBump_interval_bounds N j
    have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Fin.pos j).ne')
    have : (0 : ℝ) ≤ 5 * (j.1 : ℝ) / (N : ℝ) := by positivity
    linarith [(hu_mem j).1, hb.1]
  have hu_strict : StrictMono u := by
    intro j₁ j₂ hj
    have hb1 := rawBump_interval_bounds N j₁
    have hb2 := rawBump_interval_bounds N j₂
    have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Fin.pos j₁).ne')
    have hle : ((j₁.1 : ℝ) + 1) ≤ (j₂.1 : ℝ) := by exact_mod_cast hj
    have hdiv : 5 * ((j₁.1 : ℝ) + 1) / (N : ℝ) ≤ 5 * (j₂.1 : ℝ) / (N : ℝ) := by gcongr
    linarith [(hu_mem j₁).2, hb1.2, hb2.1, (hu_mem j₂).1]
  have hu_sq_inj : Function.Injective (fun j : Fin N => (u j) ^ 2) := by
    intro j₁ j₂ hsq
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := hu_strict h
      nlinarith [hu_pos j₁, hu_pos j₂]
    · have := hu_strict h
      nlinarith [hu_pos j₁, hu_pos j₂]
  -- Polynomial `Q(X) = ∑_{k : Fin N} b_k X^{N - 1 - k}`
  let Q : Polynomial ℝ := ∑ k : Fin N, Polynomial.C (b k) * Polynomial.X ^ (N - 1 - k.1)
  have hQ_eval : ∀ j : Fin N, Q.eval ((u j) ^ 2) = 0 := by
    intro j
    have hup : u j ≠ 0 := (hu_pos j).ne'
    have hmul : (u j) ^ (2 * N) * P (u j) = Q.eval ((u j) ^ 2) := by
      have heval_sum : Q.eval ((u j) ^ 2) =
          ∑ k : Fin N, b k * ((u j) ^ 2) ^ (N - 1 - k.1) := by
        show Polynomial.evalRingHom ((u j) ^ 2) Q = _
        simp only [Q, map_sum, map_mul, map_pow, Polynomial.coe_evalRingHom,
          Polynomial.eval_C, Polynomial.eval_X]
      rw [heval_sum]
      simp only [P, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← pow_mul, mul_div_assoc', mul_comm ((u j) ^ (2 * N)), mul_div_assoc]
      congr 1
      have hexp : 2 * N = 2 * (N - 1 - k.1) + (2 + 2 * k.1) := by omega
      rw [hexp, pow_add, mul_div_cancel_right₀ _ (pow_ne_zero _ hup)]
    rw [← hmul, hu_zero j, mul_zero]
  have hQ_zero : Q = 0 := by
    by_contra hQne
    have hdeg : Q.natDegree < N := by
      have hle : Q.natDegree ≤ N - 1 := by
        refine (Polynomial.natDegree_sum_le _ _).trans ?_
        rw [Finset.fold_max_le]
        refine ⟨Nat.zero_le _, fun k _ => ?_⟩
        exact (Polynomial.natDegree_C_mul_X_pow_le (b k) (N - 1 - k.1)).trans (by omega)
      have hNpos : 0 < N := by
        by_contra h0
        have : N = 0 := Nat.eq_zero_of_not_pos h0
        subst this
        exact hQne (by simp [Q])
      omega
    have hsub_roots : Finset.image (fun j : Fin N => (u j) ^ 2) Finset.univ ⊆ Q.roots.toFinset := by
      intro x hx
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hQne, Polynomial.IsRoot.def]
      exact hQ_eval j
    have hcard : N ≤ Q.roots.toFinset.card := by
      calc N = (Finset.univ : Finset (Fin N)).card := (Fintype.card_fin N).symm
        _ = (Finset.image (fun j : Fin N => (u j) ^ 2) Finset.univ).card :=
            (Finset.card_image_of_injective _ hu_sq_inj).symm
        _ ≤ Q.roots.toFinset.card := Finset.card_le_card hsub_roots
    have hle_deg : Q.roots.toFinset.card ≤ Q.natDegree :=
      (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' Q)
    omega
  apply hb_ne
  ext k
  have hcoeff : Q.coeff (N - 1 - k.1) = b k := by
    have hsum_c : Q.coeff (N - 1 - k.1) =
        ∑ m : Fin N, (Polynomial.C (b m) * Polynomial.X ^ (N - 1 - m.1)).coeff (N - 1 - k.1) := by
      show Polynomial.lcoeff ℝ (N - 1 - k.1) Q = _
      simp only [Q, map_sum]; rfl
    rw [hsum_c, Finset.sum_eq_single k]
    · simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    · intro m _ hmk
      have hne : N - 1 - k.1 ≠ N - 1 - m.1 := by
        intro heq; apply hmk; ext; omega
      simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hne]
    · intro hk; exact absurd (Finset.mem_univ k) hk
  rw [← hcoeff, hQ_zero, Polynomial.coeff_zero]
  rfl

/-- `Ã_{kj}(τ₁) → Ã_{kj}(0)` as `τ₁ ↓ 0` (explicitly `O(τ₁²)` on `0 < τ₁ ≤ 1/16`). -/
lemma momentMatrix_close (N : ℕ) (k j : Fin N) :
    ∃ C ≥ 0, ∀ τ₁ ∈ Ioc (0 : ℝ) (1 / 16),
      |momentMatrix N τ₁ k j - momentMatrix0 N k j| ≤ C * τ₁ ^ 2 := by
  obtain ⟨B, hB, hBbd⟩ := exists_bound_fctWeightRem k.1
  refine ⟨π ^ 2 * B / ((2 * k.1 + 1).factorial : ℝ), by positivity, fun τ₁ hτ₁ => ?_⟩
  have hτ0 : 0 < τ₁ := hτ₁.1
  have hτ16 : τ₁ ≤ 1 / 16 := hτ₁.2
  -- Use `fctMoment_eq_integral_weight` for `v(t) = bumpPhi N j (t / τ₁)`
  have hv_cd : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => bumpPhi N j (t / τ₁)) :=
    (contDiff_bumpPhi N j).comp (contDiff_id.div_const τ₁)
  have hv_supp : HasCompactSupport (fun t : ℝ => bumpPhi N j (t / τ₁)) := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -8 * τ₁) (b := 8 * τ₁)) ?_
    intro t ht
    by_contra hnot
    have hge : 8 ≤ |t / τ₁| := by
      rw [abs_div, abs_of_pos hτ0, le_div_iff₀ hτ0]
      rw [mem_Icc] at hnot; push Not at hnot
      rcases le_or_gt (-8 * τ₁) t with h | h
      · rw [abs_of_nonneg (by linarith [hnot h])]; linarith [hnot h]
      · rw [abs_of_neg (by linarith)]; linarith
    exact ht (bumpPhi_zero_of_abs_ge_eight N j hge)
  have hv_van : ∀ t ∈ Ioo (0 : ℝ) (3 * τ₁), bumpPhi N j (t / τ₁) = 0 := by
    intro t ht
    exact bumpPhi_zero_of_le_three N j (div_nonneg ht.1.le hτ0.le) ((div_le_iff₀ hτ0).mpr ht.2.le)
  have hmom := fctMoment_eq_integral_weight hv_cd hv_supp (by positivity : 0 < 3 * τ₁) hv_van k.1
  -- Change variables `t = τ₁ * u` on `Ioi 0`
  have hcov : ∫ t in Ioi (0 : ℝ), bumpPhi N j (t / τ₁) * iteratedDeriv (2 * k.1) fctWeight t =
      τ₁ * ∫ u in Ioi (0 : ℝ), bumpPhi N j u * iteratedDeriv (2 * k.1) fctWeight (τ₁ * u) := by
    have h1 := integral_comp_mul_left_Ioi
      (fun t => bumpPhi N j (t / τ₁) * iteratedDeriv (2 * k.1) fctWeight t) (0 : ℝ) hτ0
    simp only [mul_zero, smul_eq_mul] at h1
    have h2 : ∫ u in Ioi (0 : ℝ), bumpPhi N j (τ₁ * u / τ₁) * iteratedDeriv (2 * k.1) fctWeight (τ₁ * u) =
        ∫ u in Ioi (0 : ℝ), bumpPhi N j u * iteratedDeriv (2 * k.1) fctWeight (τ₁ * u) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
      rw [mul_div_cancel_left₀ _ hτ0.ne']
    rw [h2] at h1
    have hne : τ₁ ≠ 0 := hτ0.ne'
    calc ∫ t in Ioi (0 : ℝ), bumpPhi N j (t / τ₁) * iteratedDeriv (2 * k.1) fctWeight t
        = τ₁ * (τ₁⁻¹ * ∫ t in Ioi (0 : ℝ), bumpPhi N j (t / τ₁) * iteratedDeriv (2 * k.1) fctWeight t) := by
          field_simp
      _ = τ₁ * ∫ u in Ioi (0 : ℝ), bumpPhi N j u * iteratedDeriv (2 * k.1) fctWeight (τ₁ * u) := by
          rw [← h1]
  unfold momentMatrix momentMatrix0
  simp only [Matrix.of_apply]
  rw [hmom, hcov]
  set c_k : ℝ := π ^ 2 * τ₁ ^ (2 + 2 * k.1) / ((2 * k.1 + 1).factorial : ℝ)
  have hck : (π ^ 2 * τ₁ ^ (1 + 2 * k.1) / ((2 * k.1 + 1).factorial : ℝ)) *
      (τ₁ * ∫ u in Ioi (0 : ℝ), bumpPhi N j u * iteratedDeriv (2 * k.1) fctWeight (τ₁ * u)) =
      ∫ u in Ioi (0 : ℝ), c_k * (bumpPhi N j u * iteratedDeriv (2 * k.1) fctWeight (τ₁ * u)) := by
    rw [integral_const_mul]
    have hpow : τ₁ ^ (1 + 2 * k.1) * τ₁ = τ₁ ^ (2 + 2 * k.1) := by
      rw [← pow_succ]; congr 1; omega
    simp only [c_k]
    rw [← mul_assoc]
    congr 1
    calc π ^ 2 * τ₁ ^ (1 + 2 * k.1) / ↑(2 * k.1 + 1).factorial * τ₁
        = π ^ 2 * (τ₁ ^ (1 + 2 * k.1) * τ₁) / ↑(2 * k.1 + 1).factorial := by ring
      _ = π ^ 2 * τ₁ ^ (2 + 2 * k.1) / ↑(2 * k.1 + 1).factorial := by rw [hpow]
  rw [hck]
  -- Pointwise difference on `Ioi 0`
  have hdiff_eq : EqOn (fun u : ℝ => c_k * (bumpPhi N j u * iteratedDeriv (2 * k.1) fctWeight (τ₁ * u)) -
      bumpPhi N j u / u ^ (2 + 2 * k.1))
      (fun u : ℝ => c_k * bumpPhi N j u * iteratedDeriv (2 * k.1) fctWeightRem (τ₁ * u)) (Ioi 0) := by
    intro u hu
    dsimp only
    by_cases h38 : u ∈ Ioo (3 : ℝ) 8
    · have htu0 : 0 < τ₁ * u := mul_pos hτ0 (by linarith [h38.1])
      have htu1 : τ₁ * u < 1 := by nlinarith [h38.2, hτ16]
      rw [iteratedDeriv_fctWeight_decomp k.1 htu0 htu1]
      have hfac : ((2 * k.1 + 1).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      have hpi : π ≠ 0 := Real.pi_ne_zero
      have htu_pow : (τ₁ * u) ^ (2 + 2 * k.1) = τ₁ ^ (2 + 2 * k.1) * u ^ (2 + 2 * k.1) := mul_pow _ _ _
      simp only [c_k]
      rw [htu_pow]
      have hu_ne : u ^ (2 + 2 * k.1) ≠ 0 := pow_ne_zero _ (by linarith [h38.1])
      have hτ_ne : τ₁ ^ (2 + 2 * k.1) ≠ 0 := pow_ne_zero _ hτ0.ne'
      field_simp; ring
    · have hphi0 : bumpPhi N j u = 0 := by
        rw [mem_Ioo] at h38; push Not at h38
        rcases le_or_gt u 3 with h3 | h3
        · exact bumpPhi_zero_of_le_three N j (mem_Ioi.mp hu).le h3
        · exact bumpPhi_zero_of_abs_ge_eight N j (by rw [abs_of_pos (mem_Ioi.mp hu)]; exact h38 h3)
      simp [hphi0]
  have hint_sub : IntegrableOn (fun u : ℝ => c_k * (bumpPhi N j u * iteratedDeriv (2 * k.1) fctWeight (τ₁ * u))) (Ioi 0) ∧
      IntegrableOn (fun u : ℝ => bumpPhi N j u / u ^ (2 + 2 * k.1)) (Ioi 0) := by
    have hcont1 : ContinuousOn (fun u : ℝ => c_k * (bumpPhi N j u * iteratedDeriv (2 * k.1) fctWeight (τ₁ * u))) (Icc (3 : ℝ) 8) := by
      have hw_cd : ∀ n : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (iteratedDeriv n fctWeight) (Ioi 0) := by
        intro n
        have hw0 : ContDiffOn ℝ (⊤ : ℕ∞) fctWeight (Ioi 0) := by
          unfold fctWeight
          have hcosh : ContDiffOn ℝ (⊤ : ℕ∞) (fun t => Real.cosh (π * t)) (Ioi 0) := by
            have heq : Real.cosh = fun t => (Real.exp t + Real.exp (-t)) / 2 := funext Real.cosh_eq
            rw [heq]
            exact (((Real.contDiff_exp.of_le le_top).add
              ((Real.contDiff_exp.of_le le_top).comp contDiff_neg)).div_const 2).comp_contDiffOn
              (contDiffOn_const.mul contDiffOn_id)
          exact hcosh.div ((contDiff_sinh_real.comp_contDiffOn (contDiffOn_const.mul contDiffOn_id)).pow 2)
            fun t ht => pow_ne_zero 2 (sinh_pi_ne_zero (mem_Ioi.mp ht).ne')
        induction n with
        | zero => simpa using hw0
        | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv_of_isOpen isOpen_Ioi (by simp)
      refine continuousOn_const.mul ((contDiff_bumpPhi N j).continuous.continuousOn.mul ?_)
      exact (hw_cd (2 * k.1)).continuousOn.comp (continuousOn_const.mul continuousOn_id)
        fun u hu => mul_pos hτ0 (by linarith [hu.1])
    have hcont2 : ContinuousOn (fun u : ℝ => bumpPhi N j u / u ^ (2 + 2 * k.1)) (Icc (3 : ℝ) 8) :=
      (contDiff_bumpPhi N j).continuous.continuousOn.div (continuousOn_id.pow _)
        fun u hu => pow_ne_zero _ (by linarith [hu.1])
    have hvan_out : ∀ u ∈ Ioi (0 : ℝ) \ Icc (3 : ℝ) 8, bumpPhi N j u = 0 := by
      intro u hu
      have hnot := hu.2; rw [mem_Icc] at hnot; push Not at hnot
      rcases le_or_gt u 3 with h3 | h3
      · exact bumpPhi_zero_of_le_three N j (mem_Ioi.mp hu.1).le h3
      · exact bumpPhi_zero_of_abs_ge_eight N j (by rw [abs_of_pos (mem_Ioi.mp hu.1)]; linarith [hnot h3.le])
    constructor
    · refine IntegrableOn.mono_set (t := Icc (3 : ℝ) 8 ∪ (Ioi 0 \ Icc 3 8))
        (hcont1.integrableOn_Icc.union (IntegrableOn.congr_fun integrableOn_zero
          (fun u hu => by simp [hvan_out u hu]) (measurableSet_Ioi.diff measurableSet_Icc)))
        (fun u hu => by by_cases h : u ∈ Icc (3 : ℝ) 8 <;> [exact Or.inl h; exact Or.inr ⟨hu, h⟩])
    · refine IntegrableOn.mono_set (t := Icc (3 : ℝ) 8 ∪ (Ioi 0 \ Icc 3 8))
        (hcont2.integrableOn_Icc.union (IntegrableOn.congr_fun integrableOn_zero
          (fun u hu => by simp [hvan_out u hu]) (measurableSet_Ioi.diff measurableSet_Icc)))
        (fun u hu => by by_cases h : u ∈ Icc (3 : ℝ) 8 <;> [exact Or.inl h; exact Or.inr ⟨hu, h⟩])
  rw [← integral_sub hint_sub.1 hint_sub.2, setIntegral_congr_fun measurableSet_Ioi hdiff_eq]
  have hck_nn : 0 ≤ c_k := by positivity
  have hpt : ∀ u ∈ Ioi (0 : ℝ),
      ‖c_k * bumpPhi N j u * iteratedDeriv (2 * k.1) fctWeightRem (τ₁ * u)‖ ≤
        (c_k * B) * bumpPhi N j u := by
    intro u hu
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hck_nn, abs_of_nonneg (bumpPhi_nonneg N j u)]
    by_cases h38 : u ∈ Ioo (3 : ℝ) 8
    · have hmem : τ₁ * u ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) :=
        ⟨by nlinarith [h38.1, hτ0], by nlinarith [h38.2, hτ16]⟩
      have hbd_rem := hBbd (τ₁ * u) hmem
      calc c_k * bumpPhi N j u * |iteratedDeriv (2 * k.1) fctWeightRem (τ₁ * u)|
          ≤ c_k * bumpPhi N j u * B :=
            mul_le_mul_of_nonneg_left hbd_rem (mul_nonneg hck_nn (bumpPhi_nonneg N j u))
        _ = c_k * B * bumpPhi N j u := by ring
    · have hphi0 : bumpPhi N j u = 0 := by
        rw [mem_Ioo] at h38; push Not at h38
        rcases le_or_gt u 3 with h3 | h3
        · exact bumpPhi_zero_of_le_three N j (mem_Ioi.mp hu).le h3
        · exact bumpPhi_zero_of_abs_ge_eight N j (by rw [abs_of_pos (mem_Ioi.mp hu)]; exact h38 h3)
      simp [hphi0]
  have hint_phi : IntegrableOn (bumpPhi N j) (Ioi (0 : ℝ)) :=
    ((contDiff_bumpPhi N j).continuous.integrable_of_hasCompactSupport (hasCompactSupport_bumpPhi N j)).integrableOn
  have hnorm : |∫ u in Ioi (0 : ℝ), c_k * bumpPhi N j u * iteratedDeriv (2 * k.1) fctWeightRem (τ₁ * u)| ≤
      ∫ u in Ioi (0 : ℝ), (c_k * B) * bumpPhi N j u := by
    rw [← Real.norm_eq_abs]
    exact norm_integral_le_of_norm_le (hint_phi.const_mul (c_k * B))
      (ae_restrict_of_forall_mem measurableSet_Ioi hpt)
  rw [integral_const_mul, bumpPhi_integral_Ioi, mul_one] at hnorm
  have htau_le : τ₁ ^ (2 + 2 * k.1) ≤ τ₁ ^ 2 := by
    rw [pow_add]
    have hle1 : τ₁ ^ (2 * k.1) ≤ 1 := pow_le_one₀ hτ0.le (by linarith)
    nlinarith [sq_nonneg τ₁]
  calc |∫ u in Ioi (0 : ℝ), c_k * bumpPhi N j u * iteratedDeriv (2 * k.1) fctWeightRem (τ₁ * u)|
      ≤ c_k * B := hnorm
    _ = (π ^ 2 * B / ((2 * k.1 + 1).factorial : ℝ)) * τ₁ ^ (2 + 2 * k.1) := by simp only [c_k]; ring
    _ ≤ (π ^ 2 * B / ((2 * k.1 + 1).factorial : ℝ)) * τ₁ ^ 2 := by
        exact mul_le_mul_of_nonneg_left htau_le (by positivity)

/-- Uniform invertibility and inverse bound for `momentMatrix N τ₁` for sufficiently small `τ₁ > 0`. -/
lemma momentMatrix_inv_bound (N : ℕ) :
    ∃ τ₀ > 0, τ₀ ≤ 1 / 16 ∧ ∃ C_inv ≥ 0, ∀ τ₁ ∈ Ioc (0 : ℝ) τ₀,
      IsUnit (momentMatrix N τ₁).det ∧
      ∀ k j : Fin N, |(momentMatrix N τ₁)⁻¹ k j| ≤ C_inv := by
  have htend : Tendsto (fun τ₁ => momentMatrix N τ₁) (𝓝[>] (0 : ℝ)) (𝓝 (momentMatrix0 N)) := by
    refine tendsto_pi_nhds.mpr fun k => tendsto_pi_nhds.mpr fun j => ?_
    obtain ⟨C, hC, hbd⟩ := momentMatrix_close N k j
    refine Metric.tendsto_nhds.mpr fun ε hε => ?_
    have hmem : Ioc (0 : ℝ) (min (1 / 16) (Real.sqrt (ε / (C + 1)))) ∈ 𝓝[>] (0 : ℝ) := by
      have hpos : 0 < min (1 / 16 : ℝ) (Real.sqrt (ε / (C + 1))) :=
        lt_min (by norm_num) (Real.sqrt_pos.mpr (by positivity))
      exact Ioc_mem_nhdsGT hpos
    filter_upwards [hmem] with τ₁ hτ₁
    rw [Real.dist_eq]
    have h1 : τ₁ ∈ Ioc (0 : ℝ) (1 / 16) := ⟨hτ₁.1, hτ₁.2.trans (min_le_left _ _)⟩
    have h2 : τ₁ ≤ Real.sqrt (ε / (C + 1)) := hτ₁.2.trans (min_le_right _ _)
    have hsq : τ₁ ^ 2 ≤ ε / (C + 1) := by
      calc τ₁ ^ 2 ≤ (Real.sqrt (ε / (C + 1))) ^ 2 := pow_le_pow_left₀ hτ₁.1.le h2 2
        _ = ε / (C + 1) := Real.sq_sqrt (by positivity)
    have hlt : C * τ₁ ^ 2 < ε := by
      calc C * τ₁ ^ 2 ≤ C * (ε / (C + 1)) := mul_le_mul_of_nonneg_left hsq hC
        _ < (C + 1) * (ε / (C + 1)) := by
            exact mul_lt_mul_of_pos_right (by linarith) (by positivity)
        _ = ε := mul_div_cancel₀ ε (by linarith)
    exact (hbd τ₁ h1).trans_lt hlt
  have hdet0 : (momentMatrix0 N).det ≠ 0 := momentMatrix0_det_ne_zero N
  -- Continuity of `A ↦ A.det` and `A ↦ (A.det)⁻¹ • A.adjugate` at `momentMatrix0 N`
  have hdet_tend : Tendsto (fun τ₁ => (momentMatrix N τ₁).det) (𝓝[>] (0 : ℝ)) (𝓝 (momentMatrix0 N).det) :=
    (continuous_id.matrix_det.tendsto _).comp htend
  have hinv_tend : Tendsto (fun τ₁ => (momentMatrix N τ₁)⁻¹) (𝓝[>] (0 : ℝ)) (𝓝 (momentMatrix0 N)⁻¹) := by
    have hformula : ∀ A : Matrix (Fin N) (Fin N) ℝ, A⁻¹ = Ring.inverse A.det • A.adjugate :=
      fun A => Matrix.inv_def A
    simp_rw [hformula]
    have hadj_tend : Tendsto (fun τ₁ => (momentMatrix N τ₁).adjugate) (𝓝[>] (0 : ℝ))
        (𝓝 (momentMatrix0 N).adjugate) :=
      (continuous_id.matrix_adjugate.tendsto _).comp htend
    have hdet_inv : Tendsto (fun τ₁ => Ring.inverse (momentMatrix N τ₁).det) (𝓝[>] (0 : ℝ))
        (𝓝 (Ring.inverse (momentMatrix0 N).det)) := by
      simp_rw [Ring.inverse_eq_inv']
      exact (continuousAt_inv₀ hdet0).tendsto.comp hdet_tend
    exact hdet_inv.smul hadj_tend
  -- Extract `τ₀ ∈ (0, 1/16]` where `det ≠ 0` and `|A⁻¹ k j| ≤ |A₀⁻¹ k j| + 1`
  have hev_det : ∀ᶠ τ₁ in 𝓝[>] (0 : ℝ), (momentMatrix N τ₁).det ≠ 0 :=
    hdet_tend.eventually (isOpen_ne.mem_nhds hdet0)
  have hev_inv : ∀ᶠ τ₁ in 𝓝[>] (0 : ℝ),
      ∀ k j : Fin N, |(momentMatrix N τ₁)⁻¹ k j - (momentMatrix0 N)⁻¹ k j| < 1 := by
    rw [Filter.eventually_all]
    intro k
    rw [Filter.eventually_all]
    intro j
    have hkj : Tendsto (fun τ₁ => (momentMatrix N τ₁)⁻¹ k j) (𝓝[>] (0 : ℝ)) (𝓝 ((momentMatrix0 N)⁻¹ k j)) :=
      tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hinv_tend k) j
    exact Metric.tendsto_nhds.mp hkj 1 one_pos
  have hev := hev_det.and hev_inv
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, hδ_spec⟩ := hev
  set τ₀ : ℝ := min (1 / 16) (δ / 2)
  have hτ₀_pos : 0 < τ₀ := lt_min (by norm_num) (half_pos hδ)
  have hτ₀_le : τ₀ ≤ 1 / 16 := min_le_left _ _
  set C_inv : ℝ := ∑ k : Fin N, ∑ j : Fin N, (|(momentMatrix0 N)⁻¹ k j| + 1)
  refine ⟨τ₀, hτ₀_pos, hτ₀_le, C_inv, Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun j _ => by positivity,
    fun τ₁ hτ₁ => ?_⟩
  have hdist : dist τ₁ 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hτ₁.1]
    have : τ₁ ≤ δ / 2 := hτ₁.2.trans (min_le_right _ _)
    linarith
  obtain ⟨hdet_ne, hclose⟩ := hδ_spec hdist hτ₁.1
  refine ⟨isUnit_iff_ne_zero.mpr hdet_ne, fun k j => ?_⟩
  have h1 : |(momentMatrix N τ₁)⁻¹ k j| ≤ |(momentMatrix0 N)⁻¹ k j| + 1 := by
    have := hclose k j
    have htri := abs_sub_abs_le_abs_sub ((momentMatrix N τ₁)⁻¹ k j) ((momentMatrix0 N)⁻¹ k j)
    linarith
  have h2 : |(momentMatrix0 N)⁻¹ k j| + 1 ≤ ∑ j' : Fin N, (|(momentMatrix0 N)⁻¹ k j'| + 1) :=
    Finset.single_le_sum (f := fun j' : Fin N => |(momentMatrix0 N)⁻¹ k j'| + 1)
      (fun j' _ => by positivity) (Finset.mem_univ j)
  have h3 : ∑ j' : Fin N, (|(momentMatrix0 N)⁻¹ k j'| + 1) ≤ C_inv :=
    Finset.single_le_sum (f := fun k' : Fin N => ∑ j' : Fin N, (|(momentMatrix0 N)⁻¹ k' j'| + 1))
      (fun k' _ => Finset.sum_nonneg fun j' _ => by positivity) (Finset.mem_univ k)
  linarith

/-! ### The linear moment solver `momentSolver` and headline theorem `fct_moment_solver` -/

/-- Cut-off target `f̃(t) = η_cut(t/τ₁) f(t)`. -/
noncomputable def tildeF (τ₁ : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  etaCut (t / τ₁) * f t

/-- Correction coefficients `c_j(f)` solving `∑_j Ã_{kj}(τ₁) c_j = -τ₁⁻² (π² τ₁^{1+2k}/(2k+1)!) ℳ_k[f̃]`. -/
noncomputable def solverCoeff (N : ℕ) (τ₁ : ℝ) (f : ℝ → ℝ) : Fin N → ℝ :=
  -((momentMatrix N τ₁)⁻¹.mulVec fun k =>
    τ₁⁻¹ ^ 2 * (π ^ 2 * τ₁ ^ (1 + 2 * k.1) / ((2 * k.1 + 1).factorial : ℝ)) *
      fctMoment k.1 (tildeF τ₁ f))

/-- Linear moment solver `v(t) = f̃(t) + τ₁² ∑_j c_j φ_j(t/τ₁)` of Lemma `fct:moment-solver`. -/
noncomputable def momentSolver (N : ℕ) (τ₁ : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  tildeF τ₁ f t + τ₁ ^ 2 * ∑ j : Fin N, solverCoeff N τ₁ f j * bumpPhi N j (t / τ₁)

/-- `tildeF τ₁ f` is smooth on `ℝ` whenever `f` is smooth on `(-3τ₁, 3τ₁)`. -/
lemma contDiff_tildeF {τ₁ : ℝ} (hτ₁ : 0 < τ₁) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Ioo (-3 * τ₁) (3 * τ₁))) :
    ContDiff ℝ (⊤ : ℕ∞) (tildeF τ₁ f) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : |t| < 3 * τ₁
  · have hmem : t ∈ Ioo (-3 * τ₁) (3 * τ₁) := ⟨by linarith [(abs_lt.mp ht).1], (abs_lt.mp ht).2⟩
    have hf_at : ContDiffAt ℝ (⊤ : ℕ∞) f t := hf.contDiffAt (isOpen_Ioo.mem_nhds hmem)
    have heta_at : ContDiffAt ℝ (⊤ : ℕ∞) (fun s => etaCut (s / τ₁)) t :=
      (contDiff_etaCut.comp (contDiff_id.div_const τ₁)).contDiffAt
    exact heta_at.mul hf_at
  · have hgt : 5 / 2 * τ₁ < |t| := by
      have : 3 * τ₁ ≤ |t| := not_lt.mp ht
      linarith
    have hopen : IsOpen {s : ℝ | 5 / 2 * τ₁ < |s|} := isOpen_lt continuous_const continuous_abs
    have hev : tildeF τ₁ f =ᶠ[𝓝 t] 0 :=
      Filter.eventually_of_mem (hopen.mem_nhds hgt) fun s hs => by
        unfold tildeF
        have hge : 5 / 2 ≤ |s / τ₁| := by
          rw [abs_div, abs_of_pos hτ₁, le_div_iff₀ hτ₁]
          exact le_of_lt hs
        rw [etaCut_eq_zero hge, zero_mul]; rfl
    exact contDiffAt_const.congr_of_eventuallyEq hev

lemma hasCompactSupport_tildeF {τ₁ : ℝ} (hτ₁ : 0 < τ₁) (f : ℝ → ℝ) :
    HasCompactSupport (tildeF τ₁ f) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc (a := -(5 / 2 * τ₁)) (b := 5 / 2 * τ₁)) ?_
  intro t ht
  by_contra hnot
  have hge : 5 / 2 ≤ |t / τ₁| := by
    rw [abs_div, abs_of_pos hτ₁, le_div_iff₀ hτ₁]
    rw [mem_Icc] at hnot; push Not at hnot
    rcases le_or_gt (-(5 / 2 * τ₁)) t with h | h
    · rw [abs_of_nonneg (by linarith [hnot h])]; linarith [hnot h]
    · rw [abs_of_neg (by linarith)]; linarith
  exact ht (by unfold tildeF; rw [etaCut_eq_zero hge, zero_mul])

lemma tildeF_even {τ₁ : ℝ} (hτ₁ : 0 < τ₁) {f : ℝ → ℝ}
    (heven : ∀ t ∈ Icc (-3 * τ₁) (3 * τ₁), f (-t) = f t) (t : ℝ) :
    tildeF τ₁ f (-t) = tildeF τ₁ f t := by
  unfold tildeF
  rw [neg_div, etaCut_even]
  by_cases ht : |t| ≤ 3 * τ₁
  · rw [heven t ⟨by linarith [(abs_le.mp ht).1], (abs_le.mp ht).2⟩]
  · have hge : 5 / 2 ≤ |t / τ₁| := by
      rw [abs_div, abs_of_pos hτ₁, le_div_iff₀ hτ₁]
      linarith [not_le.mp ht]
    rw [etaCut_eq_zero hge, zero_mul, zero_mul]

/-- Scaling of iterated derivatives: `(g(·/τ₁))^{(r)}(t) = τ₁^{-r} g^{(r)}(t/τ₁)`. -/
lemma iteratedDeriv_comp_div {g : ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (τ₁ : ℝ) (r : ℕ) (t : ℝ) :
    iteratedDeriv r (fun s => g (s / τ₁)) t = (τ₁⁻¹) ^ r * iteratedDeriv r g (t / τ₁) := by
  have heq : (fun s => g (s / τ₁)) = fun s => g (τ₁⁻¹ * s) := by ext s; rw [div_eq_inv_mul]
  rw [heq, iteratedDeriv_comp_const_mul (hg.of_le (WithTop.coe_le_coe.mpr le_top)), div_eq_inv_mul]

/-- Leibniz bound for `tildeF τ₁ f`. -/
lemma abs_iteratedDeriv_tildeF_le (C_f : ℕ → ℝ) (hC_f : ∀ r, 0 ≤ C_f r) (r : ℕ) :
    ∃ C_t ≥ 0, ∀ {τ₁ M : ℝ} {f : ℝ → ℝ}, 0 < τ₁ → 0 ≤ M →
      ContDiffOn ℝ (⊤ : ℕ∞) f (Ioo (-3 * τ₁) (3 * τ₁)) →
      (∀ j t, |t| ≤ 3 * τ₁ → |iteratedDeriv j f t| ≤ C_f j * M * τ₁ ^ ((2 : ℤ) - j)) →
      ∀ t, |iteratedDeriv r (tildeF τ₁ f) t| ≤ C_t * M * τ₁ ^ ((2 : ℤ) - r) := by
  have hex : ∀ i : ℕ, ∃ E ≥ 0, ∀ x, |iteratedDeriv i etaCut x| ≤ E :=
    fun i => exists_bound_iteratedDeriv_of_compact contDiff_etaCut hasCompactSupport_etaCut i
  choose E hE_nn hE_bd using hex
  set C_t : ℝ := ∑ i ∈ Finset.range (r + 1), (Nat.choose r i : ℝ) * E i * C_f (r - i)
  refine ⟨C_t, Finset.sum_nonneg fun i _ => by have := hE_nn i; have := hC_f (r - i); positivity,
    fun {τ₁ M f} hτ₁ hM hf hbd t => ?_⟩
  by_cases ht : |t| < 3 * τ₁
  · have hmem : t ∈ Ioo (-3 * τ₁) (3 * τ₁) := ⟨by linarith [(abs_lt.mp ht).1], (abs_lt.mp ht).2⟩
    have hf_at : ContDiffAt ℝ (r : WithTop ℕ∞) f t :=
      (hf.contDiffAt (isOpen_Ioo.mem_nhds hmem)).of_le (WithTop.coe_le_coe.mpr le_top)
    have heta_at : ContDiffAt ℝ (r : WithTop ℕ∞) (fun s => etaCut (s / τ₁)) t :=
      ((contDiff_etaCut.comp (contDiff_id.div_const τ₁)).contDiffAt).of_le
        (WithTop.coe_le_coe.mpr le_top)
    have hleib := iteratedDeriv_mul heta_at hf_at
    change |iteratedDeriv r ((fun s => etaCut (s / τ₁)) * f) t| ≤ _
    rw [hleib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [show C_t * M * τ₁ ^ ((2 : ℤ) - ↑r) =
        ∑ i ∈ Finset.range (r + 1), ((Nat.choose r i : ℝ) * E i * C_f (r - i)) * M * τ₁ ^ ((2 : ℤ) - ↑r) by
      simp only [C_t, Finset.sum_mul]]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi_le : i ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [iteratedDeriv_comp_div contDiff_etaCut, abs_mul, abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _),
      abs_pow, abs_inv, abs_of_pos hτ₁]
    have hpow : (τ₁⁻¹) ^ i * τ₁ ^ ((2 : ℤ) - ↑(r - i)) = τ₁ ^ ((2 : ℤ) - ↑r) := by
      rw [inv_pow, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ hτ₁.ne']
      congr 1; omega
    calc (Nat.choose r i : ℝ) * ((τ₁⁻¹) ^ i * |iteratedDeriv i etaCut (t / τ₁)|) * |iteratedDeriv (r - i) f t|
        ≤ (Nat.choose r i : ℝ) * ((τ₁⁻¹) ^ i * E i) * (C_f (r - i) * M * τ₁ ^ ((2 : ℤ) - ↑(r - i))) := by
          have h1 : 0 ≤ (Nat.choose r i : ℝ) := Nat.cast_nonneg _
          have h2 : 0 ≤ (τ₁⁻¹) ^ i := by positivity
          have h3 : 0 ≤ E i := hE_nn i
          have h4 : 0 ≤ C_f (r - i) * M * τ₁ ^ ((2 : ℤ) - ↑(r - i)) :=
            mul_nonneg (mul_nonneg (hC_f _) hM) (zpow_pos hτ₁ _).le
          exact mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hE_bd i _) h2) h1)
            (hbd (r - i) t ht.le) (abs_nonneg _) (by positivity)
      _ = ((Nat.choose r i : ℝ) * E i * C_f (r - i)) * M * ((τ₁⁻¹) ^ i * τ₁ ^ ((2 : ℤ) - ↑(r - i))) := by ring
      _ = ((Nat.choose r i : ℝ) * E i * C_f (r - i)) * M * τ₁ ^ ((2 : ℤ) - ↑r) := by rw [hpow]
  · -- Outside `(-3τ₁, 3τ₁)`, `tildeF τ₁ f` vanishes identically in a neighborhood
    have hgt : 5 / 2 * τ₁ < |t| := by linarith [not_lt.mp ht]
    have hopen : IsOpen {s : ℝ | 5 / 2 * τ₁ < |s|} := isOpen_lt continuous_const continuous_abs
    have hev : tildeF τ₁ f =ᶠ[𝓝 t] 0 :=
      Filter.eventually_of_mem (hopen.mem_nhds hgt) fun s hs => by
        unfold tildeF
        have hge : 5 / 2 ≤ |s / τ₁| := by
          rw [abs_div, abs_of_pos hτ₁, le_div_iff₀ hτ₁]; exact le_of_lt hs
        rw [etaCut_eq_zero hge, zero_mul]; rfl
    have hz : iteratedDeriv r (tildeF τ₁ f) t = 0 := by simpa using (hev.iteratedDeriv r).eq_of_nhds
    rw [hz, abs_zero]
    exact mul_nonneg (mul_nonneg (Finset.sum_nonneg fun i _ => by
      have := hE_nn i; have := hC_f (r - i); positivity) hM) (zpow_pos hτ₁ _).le

/-- Linearity of `momentSolver N τ₁` in `f`. -/
lemma momentSolver_linear (N : ℕ) {τ₁ : ℝ} (hτ₁ : 0 < τ₁) {f₁ f₂ : ℝ → ℝ}
    (hf₁ : ContDiffOn ℝ (⊤ : ℕ∞) f₁ (Ioo (-3 * τ₁) (3 * τ₁)))
    (he₁ : ∀ t ∈ Icc (-3 * τ₁) (3 * τ₁), f₁ (-t) = f₁ t)
    (hf₂ : ContDiffOn ℝ (⊤ : ℕ∞) f₂ (Ioo (-3 * τ₁) (3 * τ₁)))
    (he₂ : ∀ t ∈ Icc (-3 * τ₁) (3 * τ₁), f₂ (-t) = f₂ t)
    (a b : ℝ) (t : ℝ) :
    momentSolver N τ₁ (fun s => a * f₁ s + b * f₂ s) t =
      a * momentSolver N τ₁ f₁ t + b * momentSolver N τ₁ f₂ t := by
  have htf : tildeF τ₁ (fun s => a * f₁ s + b * f₂ s) =
      fun s => a * tildeF τ₁ f₁ s + b * tildeF τ₁ f₂ s := by
    ext s; unfold tildeF; ring
  have hmom : ∀ k : Fin N, fctMoment k.1 (tildeF τ₁ (fun s => a * f₁ s + b * f₂ s)) =
      a * fctMoment k.1 (tildeF τ₁ f₁) + b * fctMoment k.1 (tildeF τ₁ f₂) := fun k => by
    rw [htf]
    exact fctMoment_linear (contDiff_tildeF hτ₁ hf₁) (hasCompactSupport_tildeF hτ₁ f₁)
      (tildeF_even hτ₁ he₁) (contDiff_tildeF hτ₁ hf₂) (hasCompactSupport_tildeF hτ₁ f₂)
      (tildeF_even hτ₁ he₂) a b k.1
  have hcoeff : ∀ j : Fin N, solverCoeff N τ₁ (fun s => a * f₁ s + b * f₂ s) j =
      a * solverCoeff N τ₁ f₁ j + b * solverCoeff N τ₁ f₂ j := by
    intro j
    unfold solverCoeff
    simp only [Pi.neg_apply, Matrix.mulVec, dotProduct]
    simp_rw [hmom]
    have : ∑ k : Fin N, (momentMatrix N τ₁)⁻¹ j k *
        (τ₁⁻¹ ^ 2 * (π ^ 2 * τ₁ ^ (1 + 2 * k.1) / ↑(2 * k.1 + 1).factorial) *
          (a * fctMoment k.1 (tildeF τ₁ f₁) + b * fctMoment k.1 (tildeF τ₁ f₂))) =
        a * ∑ k : Fin N, (momentMatrix N τ₁)⁻¹ j k *
          (τ₁⁻¹ ^ 2 * (π ^ 2 * τ₁ ^ (1 + 2 * k.1) / ↑(2 * k.1 + 1).factorial) * fctMoment k.1 (tildeF τ₁ f₁)) +
        b * ∑ k : Fin N, (momentMatrix N τ₁)⁻¹ j k *
          (τ₁⁻¹ ^ 2 * (π ^ 2 * τ₁ ^ (1 + 2 * k.1) / ↑(2 * k.1 + 1).factorial) * fctMoment k.1 (tildeF τ₁ f₂)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => by ring
    rw [this]; ring
  unfold momentSolver
  rw [htf]
  simp_rw [hcoeff]
  have hsum : ∑ j : Fin N, (a * solverCoeff N τ₁ f₁ j + b * solverCoeff N τ₁ f₂ j) * bumpPhi N j (t / τ₁) =
      a * ∑ j : Fin N, solverCoeff N τ₁ f₁ j * bumpPhi N j (t / τ₁) +
      b * ∑ j : Fin N, solverCoeff N τ₁ f₂ j * bumpPhi N j (t / τ₁) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [hsum]; ring

/-- **Lemma `fct:moment-solver`** (`constant_terms_five.tex`, lines 128–165):
Finite moment correction on a fixed scaled interval.

For any fixed `N ≥ 1`, there exists `τ₀ > 0` such that for all `τ₁ ∈ (0, τ₀]` the explicit
linear operator `momentSolver N τ₁` satisfies:
- linearity on smooth even targets on `[-3τ₁, 3τ₁]`;
- for any derivative-bound profile `C_f : ℕ → ℝ` (nonnegative), there exist constants
  `C_v : ℕ → ℝ`, `C_L1 : ℝ`, `C_th : ℕ → ℝ` (independent of `τ₁`, `M`, `f`) such that for every
  `M ≥ 0` and every real even smooth `f` on `[-3τ₁, 3τ₁]` with `f 0 = 0` and
  `|f^{(r)}(t)| ≤ C_f r * M * τ₁^{2-r}` (`|t| ≤ 3τ₁`), `v := momentSolver N τ₁ f` is real, even,
  `C^∞`, supported in `(-10τ₁, 10τ₁)`, equals `f` on `[-2τ₁, 2τ₁]`, has `ℳ_k[v] = 0` and
  `ϑ_D^{(2k+1)}(0) = 0` for `0 ≤ k < N`, satisfies `|v^{(r)}(t)| ≤ C_v r * M * τ₁^{2-r}`,
  `∫ |v| ≤ C_L1 * M * τ₁^3`, and
  `|ϑ_D^{(r)}(t)| ≤ C_th r * M * τ₁^{2-r} * min 1 ((|t|/τ₁)^{max(0, 2N+1-r)})` for `|t| ≤ 12τ₁`. -/
theorem fct_moment_solver (N : ℕ) (_hN : 1 ≤ N) :
    ∃ τ₀ > 0, ∀ (C_f : ℕ → ℝ), (∀ r, 0 ≤ C_f r) →
      ∃ (C_v : ℕ → ℝ) (C_L1 : ℝ) (C_th : ℕ → ℝ),
        (∀ r, 0 ≤ C_v r) ∧ 0 ≤ C_L1 ∧ (∀ r, 0 ≤ C_th r) ∧
        ∀ {τ₁ M : ℝ} {f : ℝ → ℝ},
          τ₁ ∈ Ioc (0 : ℝ) τ₀ → 0 ≤ M →
          ContDiffOn ℝ (⊤ : ℕ∞) f (Ioo (-3 * τ₁) (3 * τ₁)) →
          (∀ t ∈ Icc (-3 * τ₁) (3 * τ₁), f (-t) = f t) →
          f 0 = 0 →
          (∀ r t, |t| ≤ 3 * τ₁ → |iteratedDeriv r f t| ≤ C_f r * M * τ₁ ^ ((2 : ℤ) - r)) →
          let v := momentSolver N τ₁ f
          ContDiff ℝ (⊤ : ℕ∞) v ∧
          (∀ t, v (-t) = v t) ∧
          v 0 = 0 ∧
          Function.support v ⊆ Ioo (-10 * τ₁) (10 * τ₁) ∧
          (∀ t, |t| ≤ 2 * τ₁ → v t = f t) ∧
          (∀ k < N, fctMoment k v = 0) ∧
          (∀ k < N, iteratedDeriv (2 * k + 1) (fctThetaD v) 0 = 0) ∧
          (∀ r t, |iteratedDeriv r v t| ≤ C_v r * M * τ₁ ^ ((2 : ℤ) - r)) ∧
          (∫ t : ℝ, |v t| ≤ C_L1 * M * τ₁ ^ 3) ∧
          (∀ r t, |t| ≤ 12 * τ₁ →
            |iteratedDeriv r (fctThetaD v) t| ≤
              C_th r * M * τ₁ ^ ((2 : ℤ) - r) * min 1 ((|t| / τ₁) ^ (2 * N + 1 - r))) := by
  obtain ⟨τ₀, hτ₀_pos, hτ₀_16, C_inv, hC_inv_nn, hinv⟩ := momentMatrix_inv_bound N
  refine ⟨τ₀, hτ₀_pos, fun C_f hC_f => ?_⟩
  -- Derivative bounds for `tildeF` and `bumpPhi`
  choose C_t hC_t_nn hC_t_bd using fun r => abs_iteratedDeriv_tildeF_le C_f hC_f r
  choose B_phi hB_phi_nn hB_phi_bd using fun (j : Fin N) (r : ℕ) =>
    exists_bound_iteratedDeriv_of_compact (contDiff_bumpPhi N j) (hasCompactSupport_bumpPhi N j) r
  -- Coefficient bound `C_c`
  set C_c : ℝ := C_inv * ∑ k : Fin N, (3 / ((2 * k.1 + 1).factorial : ℝ)) * C_t (2 * k.1 + 2)
  have hC_c_nn : 0 ≤ C_c := mul_nonneg hC_inv_nn
    (Finset.sum_nonneg fun k _ => mul_nonneg (by positivity) (hC_t_nn _))
  set C_v : ℕ → ℝ := fun r => C_t r + C_c * ∑ j : Fin N, B_phi j r
  have hC_v_nn : ∀ r, 0 ≤ C_v r := fun r =>
    add_nonneg (hC_t_nn r) (mul_nonneg hC_c_nn (Finset.sum_nonneg fun j _ => hB_phi_nn j r))
  set C_L1 : ℝ := 20 * C_v 0
  set C_th : ℕ → ℝ := fun r => (46 / π) * max (C_v (r + 1)) (C_v (2 * N + 2))
  refine ⟨C_v, C_L1, C_th, hC_v_nn, mul_nonneg (by norm_num) (hC_v_nn 0),
    fun r => mul_nonneg (by positivity) (le_trans (hC_v_nn (r + 1)) (le_max_left _ _)),
    fun {τ₁ M f} hτ₁ hM hf heven hf0 hfbd => ?_⟩
  have hτ0 : 0 < τ₁ := hτ₁.1
  obtain ⟨hdet_unit, hinv_bd⟩ := hinv τ₁ hτ₁
  have htf_cd : ContDiff ℝ (⊤ : ℕ∞) (tildeF τ₁ f) := contDiff_tildeF hτ0 hf
  have htf_supp : HasCompactSupport (tildeF τ₁ f) := hasCompactSupport_tildeF hτ0 f
  have htf_even : ∀ t, tildeF τ₁ f (-t) = tildeF τ₁ f t := tildeF_even hτ0 heven
  -- 1. Smoothness
  have hv_cd : ContDiff ℝ (⊤ : ℕ∞) (momentSolver N τ₁ f) := by
    unfold momentSolver
    refine htf_cd.add (contDiff_const.mul ?_)
    exact ContDiff.sum fun j _ =>
      contDiff_const.mul ((contDiff_bumpPhi N j).comp (contDiff_id.div_const τ₁))
  -- 2. Evenness
  have hv_even : ∀ t, momentSolver N τ₁ f (-t) = momentSolver N τ₁ f t := by
    intro t; unfold momentSolver
    rw [htf_even t]
    congr 2; refine Finset.sum_congr rfl fun j _ => ?_
    rw [neg_div, bumpPhi_even]
  -- 3. Agreement on `[-2τ₁, 2τ₁]` and `v 0 = 0`
  have hv_eq_f : ∀ t, |t| ≤ 2 * τ₁ → momentSolver N τ₁ f t = f t := by
    intro t ht
    unfold momentSolver tildeF
    have hdiv2 : |t / τ₁| ≤ 2 := by rw [abs_div, abs_of_pos hτ0, div_le_iff₀ hτ0]; exact ht
    rw [etaCut_eq_one hdiv2, one_mul]
    have hsum0 : ∑ j : Fin N, solverCoeff N τ₁ f j * bumpPhi N j (t / τ₁) = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      have hphi0 : bumpPhi N j (t / τ₁) = 0 := by
        rcases le_or_gt 0 (t / τ₁) with h | h
        · exact bumpPhi_zero_of_le_three N j h (by linarith [abs_of_nonneg h ▸ hdiv2])
        · rw [← bumpPhi_even]
          exact bumpPhi_zero_of_le_three N j (by linarith) (by linarith [abs_of_neg h ▸ hdiv2])
      rw [hphi0, mul_zero]
    rw [hsum0, mul_zero, add_zero]
  have hv0 : momentSolver N τ₁ f 0 = 0 := by
    rw [hv_eq_f 0 (by simp; linarith), hf0]
  -- 4. Support in `(-10τ₁, 10τ₁)`
  have hv_supp : Function.support (momentSolver N τ₁ f) ⊆ Ioo (-10 * τ₁) (10 * τ₁) := by
    intro t ht
    by_contra hnot
    have hge8 : 8 ≤ |t / τ₁| := by
      rw [abs_div, abs_of_pos hτ0, le_div_iff₀ hτ0]
      rw [mem_Ioo] at hnot; push Not at hnot
      rcases lt_or_ge (-10 * τ₁) t with h | h
      · rw [abs_of_nonneg (by linarith [hnot h])]; linarith [hnot h]
      · rw [abs_of_neg (by linarith)]; linarith
    apply ht
    unfold momentSolver tildeF
    rw [etaCut_eq_zero (by linarith), zero_mul, zero_add]
    have hsum0 : ∑ j : Fin N, solverCoeff N τ₁ f j * bumpPhi N j (t / τ₁) = 0 :=
      Finset.sum_eq_zero fun j _ => by rw [bumpPhi_zero_of_abs_ge_eight N j hge8, mul_zero]
    rw [hsum0, mul_zero]
  have hv_comp : HasCompactSupport (momentSolver N τ₁ f) :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc (hv_supp.trans Ioo_subset_Icc_self)
  -- 5. Zero moments `ℳ_k[v] = 0` for `k < N`
  have hv_mom : ∀ k < N, fctMoment k (momentSolver N τ₁ f) = 0 := by
    intro k hk
    let k' : Fin N := ⟨k, hk⟩
    -- Linearity of `fctMoment` over finite sum
    have hlin_sum : ∀ (s : Finset (Fin N)) (c : Fin N → ℝ),
        fctMoment k (fun t => ∑ j ∈ s, c j * bumpPhi N j (t / τ₁)) =
          ∑ j ∈ s, c j * fctMoment k (fun t => bumpPhi N j (t / τ₁)) := by
      intro s c
      induction s using Finset.cons_induction with
      | empty =>
        simp only [Finset.sum_empty]
        unfold fctMoment
        have : iteratedDeriv (2 * k + 1) (fun _ : ℝ => (0 : ℝ)) = 0 := by
          ext t; simp
        rw [this]; simp
      | cons j s hjs ih =>
        have hcd_j : ContDiff ℝ (⊤ : ℕ∞) (fun t => bumpPhi N j (t / τ₁)) :=
          (contDiff_bumpPhi N j).comp (contDiff_id.div_const τ₁)
        have hsupp_j : HasCompactSupport (fun t => bumpPhi N j (t / τ₁)) :=
          HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -8 * τ₁) (b := 8 * τ₁))
            fun t ht => by
              by_contra hnot; apply ht
              refine bumpPhi_zero_of_abs_ge_eight N j ?_
              rw [abs_div, abs_of_pos hτ0, le_div_iff₀ hτ0]
              rw [mem_Icc] at hnot; push Not at hnot
              rcases le_or_gt (-8 * τ₁) t with h | h
              · rw [abs_of_nonneg (by linarith [hnot h])]; linarith [hnot h]
              · rw [abs_of_neg (by linarith)]; linarith
        have he_j : ∀ t, bumpPhi N j (-t / τ₁) = bumpPhi N j (t / τ₁) :=
          fun t => by rw [neg_div, bumpPhi_even]
        have hcd_s : ContDiff ℝ (⊤ : ℕ∞) (fun t => ∑ i ∈ s, c i * bumpPhi N i (t / τ₁)) :=
          ContDiff.sum fun i _ => contDiff_const.mul ((contDiff_bumpPhi N i).comp (contDiff_id.div_const τ₁))
        have hsupp_s : HasCompactSupport (fun t => ∑ i ∈ s, c i * bumpPhi N i (t / τ₁)) :=
          HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -8 * τ₁) (b := 8 * τ₁))
            fun t ht => by
              by_contra hnot; apply ht
              refine Finset.sum_eq_zero fun i _ => ?_
              have hge : 8 ≤ |t / τ₁| := by
                rw [abs_div, abs_of_pos hτ0, le_div_iff₀ hτ0]
                rw [mem_Icc] at hnot; push Not at hnot
                rcases le_or_gt (-8 * τ₁) t with h | h
                · rw [abs_of_nonneg (by linarith [hnot h])]; linarith [hnot h]
                · rw [abs_of_neg (by linarith)]; linarith
              rw [bumpPhi_zero_of_abs_ge_eight N i hge, mul_zero]
        have he_s : ∀ t, (∑ i ∈ s, c i * bumpPhi N i (-t / τ₁)) = ∑ i ∈ s, c i * bumpPhi N i (t / τ₁) :=
          fun t => Finset.sum_congr rfl fun i _ => by rw [neg_div, bumpPhi_even]
        simp_rw [Finset.sum_cons]
        have hlin := fctMoment_linear hcd_j hsupp_j he_j hcd_s hsupp_s he_s (c j) 1 k
        simp only [one_mul] at hlin
        rw [hlin, ih]
    have hcd_sum : ContDiff ℝ (⊤ : ℕ∞) (fun t => ∑ j : Fin N, solverCoeff N τ₁ f j * bumpPhi N j (t / τ₁)) :=
      ContDiff.sum fun j _ => contDiff_const.mul ((contDiff_bumpPhi N j).comp (contDiff_id.div_const τ₁))
    have hsupp_sum : HasCompactSupport (fun t => ∑ j : Fin N, solverCoeff N τ₁ f j * bumpPhi N j (t / τ₁)) :=
      HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -8 * τ₁) (b := 8 * τ₁))
        fun t ht => by
          by_contra hnot; apply ht
          refine Finset.sum_eq_zero fun i _ => ?_
          have hge : 8 ≤ |t / τ₁| := by
            rw [abs_div, abs_of_pos hτ0, le_div_iff₀ hτ0]
            rw [mem_Icc] at hnot; push Not at hnot
            rcases le_or_gt (-8 * τ₁) t with h | h
            · rw [abs_of_nonneg (by linarith [hnot h])]; linarith [hnot h]
            · rw [abs_of_neg (by linarith)]; linarith
          rw [bumpPhi_zero_of_abs_ge_eight N i hge, mul_zero]
    have he_sum : ∀ t, (∑ j : Fin N, solverCoeff N τ₁ f j * bumpPhi N j (-t / τ₁)) =
        ∑ j : Fin N, solverCoeff N τ₁ f j * bumpPhi N j (t / τ₁) :=
      fun t => Finset.sum_congr rfl fun j _ => by rw [neg_div, bumpPhi_even]
    have hmom_v : fctMoment k (momentSolver N τ₁ f) =
        fctMoment k (tildeF τ₁ f) + τ₁ ^ 2 * ∑ j : Fin N, solverCoeff N τ₁ f j *
          fctMoment k (fun t => bumpPhi N j (t / τ₁)) := by
      unfold momentSolver
      have := fctMoment_linear htf_cd htf_supp htf_even hcd_sum hsupp_sum he_sum 1 (τ₁ ^ 2) k
      simp only [one_mul] at this
      rw [this, hlin_sum]
    rw [hmom_v]
    -- Multiply by `scale_k = π² τ₁^{1+2k} / (2k+1)! > 0`
    set scale_k : ℝ := π ^ 2 * τ₁ ^ (1 + 2 * k) / ((2 * k + 1).factorial : ℝ)
    have hscale_pos : 0 < scale_k := by positivity
    suffices h0 : scale_k * (fctMoment k (tildeF τ₁ f) + τ₁ ^ 2 * ∑ j : Fin N,
        solverCoeff N τ₁ f j * fctMoment k (fun t => bumpPhi N j (t / τ₁))) = 0 from
      (mul_eq_zero.mp h0).resolve_left hscale_pos.ne'
    have hmat : scale_k * ∑ j : Fin N, solverCoeff N τ₁ f j * fctMoment k (fun t => bumpPhi N j (t / τ₁)) =
        ((momentMatrix N τ₁).mulVec (solverCoeff N τ₁ f)) k' := by
      simp only [Matrix.mulVec, dotProduct, momentMatrix, Matrix.of_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [scale_k, k']; ring
    have hmul_inv : (momentMatrix N τ₁).mulVec (solverCoeff N τ₁ f) =
        -(fun m : Fin N => τ₁⁻¹ ^ 2 * (π ^ 2 * τ₁ ^ (1 + 2 * m.1) / ((2 * m.1 + 1).factorial : ℝ)) *
          fctMoment m.1 (tildeF τ₁ f)) := by
      unfold solverCoeff
      rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet_unit, Matrix.one_mulVec]
    have hrow := congrFun hmul_inv k'
    simp only [Pi.neg_apply] at hrow
    calc scale_k * (fctMoment k (tildeF τ₁ f) + τ₁ ^ 2 * ∑ j : Fin N,
            solverCoeff N τ₁ f j * fctMoment k (fun t => bumpPhi N j (t / τ₁)))
        = scale_k * fctMoment k (tildeF τ₁ f) + τ₁ ^ 2 * ((momentMatrix N τ₁).mulVec (solverCoeff N τ₁ f) k') := by
          rw [mul_add, ← mul_assoc, mul_comm scale_k (τ₁ ^ 2), mul_assoc, hmat]
      _ = scale_k * fctMoment k (tildeF τ₁ f) + τ₁ ^ 2 * (-(τ₁⁻¹ ^ 2 * scale_k * fctMoment k (tildeF τ₁ f))) := by
          rw [hrow]
      _ = 0 := by
          have hτne : τ₁ ≠ 0 := hτ0.ne'
          field_simp; ring
  -- 6. Vanishing odd phase derivatives at 0
  have hv_th0 : ∀ k < N, iteratedDeriv (2 * k + 1) (fctThetaD (momentSolver N τ₁ f)) 0 = 0 := by
    intro k hk
    rw [iteratedDeriv_odd_fctThetaD_zero hv_cd hv_comp hv_even k, hv_mom k hk, mul_zero]
  -- 7. Coefficient bound `|solverCoeff N τ₁ f j| ≤ C_c * M`
  have hmom_tf_bd : ∀ k : Fin N,
      |τ₁⁻¹ ^ 2 * (π ^ 2 * τ₁ ^ (1 + 2 * k.1) / ((2 * k.1 + 1).factorial : ℝ)) *
        fctMoment k.1 (tildeF τ₁ f)| ≤ (3 / ((2 * k.1 + 1).factorial : ℝ)) * C_t (2 * k.1 + 2) * M := by
    intro k
    -- Bound `|fctMoment k (tildeF τ₁ f)|` via MVT + `abs_mul_inv_sinh_le`
    set g := iteratedDeriv (2 * k.1 + 1) (tildeF τ₁ f)
    have hg0 : g 0 = 0 := iteratedDeriv_odd_zero htf_even k.1
    have hg_zero : ∀ t, 3 * τ₁ ≤ t → g t = 0 := by
      intro t ht
      have hgt : 5 / 2 * τ₁ < t := by linarith
      have hev : tildeF τ₁ f =ᶠ[𝓝 t] 0 :=
        Filter.eventually_of_mem (Ioi_mem_nhds hgt) fun s hs => by
          unfold tildeF
          have hge : 5 / 2 ≤ |s / τ₁| := by
            rw [abs_div, abs_of_pos hτ0, le_div_iff₀ hτ0, abs_of_pos (by linarith [mem_Ioi.mp hs])]
            exact le_of_lt (mem_Ioi.mp hs)
          rw [etaCut_eq_zero hge, zero_mul]; rfl
      simpa [g] using (hev.iteratedDeriv (2 * k.1 + 1)).eq_of_nhds
    have hIoc_eq : ∫ t in Ioi (0 : ℝ), g t / Real.sinh (π * t) =
        ∫ t in Icc (0 : ℝ) (3 * τ₁), g t / Real.sinh (π * t) := by
      have hsub : Ioc (0 : ℝ) (3 * τ₁) ⊆ Ioi (0 : ℝ) := fun t ht => ht.1
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
      refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Ioi.nullMeasurableSet hsub
        (Filter.Eventually.of_forall fun t ht => ?_)
      have hgt : 3 * τ₁ < t := by
        by_contra hle; exact ht.2 ⟨ht.1, not_lt.mp hle⟩
      rw [hg_zero t hgt.le, zero_div]
    set B_g : ℝ := C_t (2 * k.1 + 2) * M * τ₁ ^ ((2 : ℤ) - ↑(2 * k.1 + 2))
    have hBg_nn : 0 ≤ B_g := mul_nonneg (mul_nonneg (hC_t_nn _) hM) (zpow_pos hτ0 _).le
    have hpt : ∀ t ∈ Icc (0 : ℝ) (3 * τ₁), ‖g t / Real.sinh (π * t)‖ ≤ B_g / π := by
      intro t _
      rw [Real.norm_eq_abs]
      have hgt_le : |g t| ≤ B_g * |t| := by
        have hlip := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
          (f := g) (f' := deriv g) (s := univ) (C := B_g)
          (fun x _ => ((contDiff_iteratedDeriv_infty htf_cd (2 * k.1 + 1)).differentiable (by simp) x).hasDerivAt.hasDerivWithinAt)
          (fun x _ => by
            rw [Real.norm_eq_abs]
            show |deriv (iteratedDeriv (2 * k.1 + 1) (tildeF τ₁ f)) x| ≤ B_g
            rw [← iteratedDeriv_succ]
            exact hC_t_bd (2 * k.1 + 2) hτ0 hM hf hfbd x)
          convex_univ (mem_univ 0) (mem_univ t)
        simpa [hg0, Real.norm_eq_abs] using hlip
      by_cases ht0 : t = 0
      · simp only [ht0, hg0, zero_div, abs_zero]; positivity
      · rw [abs_div]
        calc |g t| / |Real.sinh (π * t)|
            ≤ (B_g * |t|) / |Real.sinh (π * t)| := div_le_div_of_nonneg_right hgt_le (abs_nonneg _)
          _ = B_g * |t / Real.sinh (π * t)| := by rw [abs_div, mul_div_assoc]
          _ ≤ B_g * (1 / π) := mul_le_mul_of_nonneg_left (abs_mul_inv_sinh_le t) hBg_nn
          _ = B_g / π := by ring
    have hnorm := MeasureTheory.norm_setIntegral_le_of_norm_le_const (μ := volume) (hs := measure_Icc_lt_top) hpt
    rw [Real.norm_eq_abs, Measure.real_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith), sub_zero] at hnorm
    have hmom_le : |fctMoment k.1 (tildeF τ₁ f)| ≤ (3 / π ^ 2) * B_g * τ₁ := by
      unfold fctMoment
      rw [hIoc_eq, abs_mul, abs_of_pos (by positivity : 0 < 1 / π)]
      calc (1 / π) * |∫ t in Icc (0 : ℝ) (3 * τ₁), g t / Real.sinh (π * t)|
          ≤ (1 / π) * ((B_g / π) * (3 * τ₁)) := mul_le_mul_of_nonneg_left hnorm (by positivity)
        _ = (3 / π ^ 2) * B_g * τ₁ := by ring
    rw [abs_mul, abs_of_pos (by positivity : 0 < τ₁⁻¹ ^ 2 * (π ^ 2 * τ₁ ^ (1 + 2 * k.1) / ((2 * k.1 + 1).factorial : ℝ)))]
    have hpow_cancel : τ₁⁻¹ ^ 2 * τ₁ ^ (1 + 2 * k.1) * (τ₁ ^ ((2 : ℤ) - ↑(2 * k.1 + 2)) * τ₁) = 1 := by
      have hexp : (2 : ℤ) - ↑(2 * k.1 + 2) = -↑(2 * k.1) := by omega
      rw [hexp, zpow_neg, zpow_natCast, pow_add, pow_one]
      have hτne : τ₁ ≠ 0 := hτ0.ne'
      field_simp
    calc τ₁⁻¹ ^ 2 * (π ^ 2 * τ₁ ^ (1 + 2 * k.1) / ((2 * k.1 + 1).factorial : ℝ)) * |fctMoment k.1 (tildeF τ₁ f)|
        ≤ τ₁⁻¹ ^ 2 * (π ^ 2 * τ₁ ^ (1 + 2 * k.1) / ((2 * k.1 + 1).factorial : ℝ)) * ((3 / π ^ 2) * B_g * τ₁) :=
          mul_le_mul_of_nonneg_left hmom_le (by positivity)
      _ = (3 / ((2 * k.1 + 1).factorial : ℝ)) * C_t (2 * k.1 + 2) * M *
          (τ₁⁻¹ ^ 2 * τ₁ ^ (1 + 2 * k.1) * (τ₁ ^ ((2 : ℤ) - ↑(2 * k.1 + 2)) * τ₁)) := by
          have hpi : π ≠ 0 := Real.pi_ne_zero
          simp only [B_g]; field_simp
      _ = (3 / ((2 * k.1 + 1).factorial : ℝ)) * C_t (2 * k.1 + 2) * M := by rw [hpow_cancel, mul_one]
  have hcoeff_bd : ∀ j : Fin N, |solverCoeff N τ₁ f j| ≤ C_c * M := by
    intro j
    unfold solverCoeff
    simp only [Pi.neg_apply, abs_neg, Matrix.mulVec, dotProduct]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [show C_c * M = ∑ k : Fin N, C_inv * ((3 / ((2 * k.1 + 1).factorial : ℝ)) * C_t (2 * k.1 + 2) * M) by
      simp only [C_c, Finset.mul_sum, Finset.sum_mul]; refine Finset.sum_congr rfl fun k _ => by ring]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [abs_mul]
    exact mul_le_mul (hinv_bd j k) (hmom_tf_bd k) (abs_nonneg _) hC_inv_nn
  -- 8. Derivative bounds on `v`
  have hv_deriv_bd : ∀ r t, |iteratedDeriv r (momentSolver N τ₁ f) t| ≤ C_v r * M * τ₁ ^ ((2 : ℤ) - r) := by
    intro r t
    unfold momentSolver
    have hcd1 : ContDiffAt ℝ (r : WithTop ℕ∞) (tildeF τ₁ f) t :=
      htf_cd.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
    have hcd2 : ContDiffAt ℝ (r : WithTop ℕ∞) (fun s => τ₁ ^ 2 * ∑ j : Fin N, solverCoeff N τ₁ f j * bumpPhi N j (s / τ₁)) t :=
      (contDiff_const.mul (ContDiff.sum fun j _ =>
        contDiff_const.mul ((contDiff_bumpPhi N j).comp (contDiff_id.div_const τ₁)))).contDiffAt.of_le
        (WithTop.coe_le_coe.mpr le_top)
    rw [show (fun s => tildeF τ₁ f s + τ₁ ^ 2 * ∑ j : Fin N, solverCoeff N τ₁ f j * bumpPhi N j (s / τ₁)) =
        tildeF τ₁ f + (fun s => τ₁ ^ 2 * ∑ j : Fin N, solverCoeff N τ₁ f j * bumpPhi N j (s / τ₁)) from rfl,
      iteratedDeriv_add hcd1 hcd2, iteratedDeriv_const_mul_field]
    have hsum_deriv : iteratedDeriv r (fun s => ∑ j : Fin N, solverCoeff N τ₁ f j * bumpPhi N j (s / τ₁)) t =
        ∑ j : Fin N, solverCoeff N τ₁ f j * ((τ₁⁻¹) ^ r * iteratedDeriv r (bumpPhi N j) (t / τ₁)) := by
      have h1 := iteratedDeriv_sum (I := (Finset.univ : Finset (Fin N)))
        (f := fun j s => solverCoeff N τ₁ f j * bumpPhi N j (s / τ₁)) (n := r) (x := t)
        fun j _ => (contDiff_const.mul ((contDiff_bumpPhi N j).comp (contDiff_id.div_const τ₁))).contDiffAt.of_le
          (WithTop.coe_le_coe.mpr le_top)
      rw [show (fun s => ∑ j : Fin N, solverCoeff N τ₁ f j * bumpPhi N j (s / τ₁)) =
          ∑ j : Fin N, fun s => solverCoeff N τ₁ f j * bumpPhi N j (s / τ₁) by ext s; simp, h1]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [iteratedDeriv_const_mul_field, iteratedDeriv_comp_div (contDiff_bumpPhi N j)]
    rw [hsum_deriv]
    refine (abs_add_le _ _).trans ?_
    have h1 := hC_t_bd r hτ0 hM hf hfbd t
    have hpow : τ₁ ^ 2 * (τ₁⁻¹) ^ r = τ₁ ^ ((2 : ℤ) - ↑r) := by
      rw [inv_pow, ← zpow_natCast τ₁ 2, ← zpow_natCast τ₁ r, ← zpow_neg, ← zpow_add₀ hτ0.ne']
      congr 1
    have h2 : |τ₁ ^ 2 * ∑ j : Fin N, solverCoeff N τ₁ f j * ((τ₁⁻¹) ^ r * iteratedDeriv r (bumpPhi N j) (t / τ₁))| ≤
        (C_c * ∑ j : Fin N, B_phi j r) * M * τ₁ ^ ((2 : ℤ) - ↑r) := by
      rw [abs_mul, abs_of_pos (by positivity : 0 < τ₁ ^ 2)]
      refine (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (sq_nonneg τ₁)).trans ?_
      have hterm : ∀ j : Fin N,
          |solverCoeff N τ₁ f j * ((τ₁⁻¹) ^ r * iteratedDeriv r (bumpPhi N j) (t / τ₁))| ≤
            C_c * M * (τ₁⁻¹) ^ r * B_phi j r := fun j => by
        rw [abs_mul, abs_mul, abs_pow, abs_inv, abs_of_pos hτ0]
        calc |solverCoeff N τ₁ f j| * ((τ₁⁻¹) ^ r * |iteratedDeriv r (bumpPhi N j) (t / τ₁)|)
            ≤ (C_c * M) * ((τ₁⁻¹) ^ r * B_phi j r) :=
              mul_le_mul (hcoeff_bd j) (mul_le_mul_of_nonneg_left (hB_phi_bd j r _) (by positivity))
                (by positivity) (mul_nonneg hC_c_nn hM)
          _ = C_c * M * (τ₁⁻¹) ^ r * B_phi j r := by ring
      calc τ₁ ^ 2 * ∑ j : Fin N, |solverCoeff N τ₁ f j * ((τ₁⁻¹) ^ r * iteratedDeriv r (bumpPhi N j) (t / τ₁))|
          ≤ τ₁ ^ 2 * ∑ j : Fin N, C_c * M * (τ₁⁻¹) ^ r * B_phi j r :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hterm j) (sq_nonneg τ₁)
        _ = (C_c * ∑ j : Fin N, B_phi j r) * M * (τ₁ ^ 2 * (τ₁⁻¹) ^ r) := by
            rw [← Finset.mul_sum]; ring
        _ = (C_c * ∑ j : Fin N, B_phi j r) * M * τ₁ ^ ((2 : ℤ) - ↑r) := by rw [hpow]
    calc |iteratedDeriv r (tildeF τ₁ f) t| +
          |τ₁ ^ 2 * ∑ j : Fin N, solverCoeff N τ₁ f j * ((τ₁⁻¹) ^ r * iteratedDeriv r (bumpPhi N j) (t / τ₁))|
        ≤ C_t r * M * τ₁ ^ ((2 : ℤ) - ↑r) + (C_c * ∑ j : Fin N, B_phi j r) * M * τ₁ ^ ((2 : ℤ) - ↑r) :=
          add_le_add h1 h2
      _ = C_v r * M * τ₁ ^ ((2 : ℤ) - ↑r) := by simp only [C_v]; ring
  -- 9. L¹ norm bound `∫ |v| ≤ 20 C_v 0 M τ₁^3`
  have hv_L1 : ∫ t : ℝ, |momentSolver N τ₁ f t| ≤ C_L1 * M * τ₁ ^ 3 := by
    have hsplit : ∫ t : ℝ, |momentSolver N τ₁ f t| =
        ∫ t in Icc (-10 * τ₁) (10 * τ₁), |momentSolver N τ₁ f t| := by
      rw [← setIntegral_univ]
      refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero MeasurableSet.univ.nullMeasurableSet (subset_univ _)
        (Filter.Eventually.of_forall fun t ht => ?_)
      have h0 : momentSolver N τ₁ f t = 0 := by
        by_contra hne
        exact ht.2 (Ioo_subset_Icc_self (hv_supp hne))
      simp [h0]
    rw [hsplit]
    have hpt : ∀ t ∈ Icc (-10 * τ₁) (10 * τ₁), ‖|momentSolver N τ₁ f t|‖ ≤ C_v 0 * M * τ₁ ^ 2 := by
      intro t _
      rw [Real.norm_eq_abs, abs_abs]
      simpa using hv_deriv_bd 0 t
    have hnorm := MeasureTheory.norm_setIntegral_le_of_norm_le_const (μ := volume) (hs := measure_Icc_lt_top) hpt
    rw [Real.norm_eq_abs, Measure.real_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith),
      abs_of_nonneg (setIntegral_nonneg measurableSet_Icc fun t _ => abs_nonneg _)] at hnorm
    calc ∫ t in Icc (-10 * τ₁) (10 * τ₁), |momentSolver N τ₁ f t|
        ≤ C_v 0 * M * τ₁ ^ 2 * (10 * τ₁ - -10 * τ₁) := hnorm
      _ = C_L1 * M * τ₁ ^ 3 := by simp only [C_L1]; ring
  -- 10. Quantitative phase bound from `FctMomentCore.abs_iteratedDeriv_fctThetaD_le`
  have hv_th_bd : ∀ r t, |t| ≤ 12 * τ₁ →
      |iteratedDeriv r (fctThetaD (momentSolver N τ₁ f)) t| ≤
        C_th r * M * τ₁ ^ ((2 : ℤ) - r) * min 1 ((|t| / τ₁) ^ (2 * N + 1 - r)) :=
    fun r t ht => abs_iteratedDeriv_fctThetaD_le hv_cd hv_even hv_supp hτ0 hM hv_mom hv_deriv_bd r t ht
  exact ⟨hv_cd, hv_even, hv0, hv_supp, hv_eq_f, hv_mom, hv_th0, hv_deriv_bd, hv_L1, hv_th_bd⟩

/-- info: 'FormalResearch.SignUncertainty.FctMoment.fct_moment_solver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.FctMoment.fct_moment_solver

end FormalResearch.SignUncertainty.FctMoment

