module

public import FormalResearch.CohnElkies.PieceCPhase

/-!
# Regularity of `φ = χ₁ H_c` (the amplitude of the branch term)

Source: `CFT/sign_uncertainty/paper/u1c_estimate_proofs.tex`, Piece C item 3: `H_c(v) = g(v) e^{icR(εv)}` is smooth with
`|H_c| + |H_c'| + |H_c''| ≤ C` on `[-1, 1]`. Here: `pcH` is `C²` (`contDiff_pcH`; `edgeR` is `C³`), so for a `C²` cutoff `χ₁` supported in `[-1,1]`,
`φ = χ₁ H_c` is `C²` with compact support in `[-1,1]` and hence has finite bounds `M` (`exists_bounds_chi_pcH`), exactly the
hypotheses `hφ`, `b0`-`b2` of `pieceC_main_term`. The bound `M` obtained here depends on `(c, δ₀, m)`; its uniformity
(`C` independent of `c ≥ 2`, `δ₀ ∈ (0,4]`) is not proved here.

Status: proved, unconditional (qualitative).
-/

@[expose] public section

open MeasureTheory Set
open scoped Real

namespace FormalResearch.CohnElkies

lemma contDiffAt_cpow_neg_half {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    ContDiffAt ℂ 2 (fun w : ℂ => w ^ (-(1 / 2 : ℂ))) z := by
  have h := ((Complex.contDiffAt_log (n := 2) hz).mul (contDiffAt_const (c := (-(1 / 2 : ℂ))))).cexp
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_ne.mem_nhds (Complex.slitPlane_ne_zero hz)] with w hw
  exact Complex.cpow_def_of_ne_zero hw _

theorem contDiff_pcH (δ₀ : ℝ) (m : ℕ) {c : ℝ} (hc : 0 < c) : ContDiff ℝ 2 (pcH δ₀ m c) := by
  have hε := liftEps_pos hc
  have hz : ContDiff ℝ 2 (fun v : ℝ => (((liftEps c * v : ℝ) : ℂ) * Complex.I)) :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)).mul contDiff_const
  have hcpow : ContDiff ℝ 2 (fun v : ℝ => (1 - (((liftEps c * v : ℝ) : ℂ) * Complex.I)) ^ (-(1 / 2 : ℂ))) := by
    refine contDiff_iff_contDiffAt.mpr fun v => ?_
    have hmem : (1 - (((liftEps c * v : ℝ) : ℂ) * Complex.I)) ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl (by simp))
    exact ((contDiffAt_cpow_neg_half hmem).restrict_scalars ℝ).comp v (contDiff_const.sub hz).contDiffAt
  have hbin : ContDiff ℝ 2 (fun v : ℝ => FormalResearch.Asymptotics.binetDiff c (((liftEps c * v : ℝ) : ℂ) * Complex.I)) := by
    unfold FormalResearch.Asymptotics.binetDiff
    have hb : ContDiffOn ℂ 2 FormalResearch.Asymptotics.binetRem {w : ℂ | 0 < w.re} :=
      FormalResearch.Asymptotics.binetRem_differentiableOn.contDiffOn (isOpen_lt continuous_const Complex.continuous_re)
    have hb' := hb.restrict_scalars ℝ
    exact (hb'.comp_contDiff (contDiff_const.mul (contDiff_const.sub hz)) (fun v => by simp [hc])).sub contDiff_const
  have hmult : ContDiff ℝ 2 (fun v : ℝ => liftMultiplier δ₀ m ((v : ℂ) * Complex.I)) := by
    unfold liftMultiplier
    have : ContDiff ℂ 2 bsplineE1 := contDiff_bsplineE1.of_le (by norm_cast)
    exact ((this.restrict_scalars ℝ).comp (contDiff_const.mul ((Complex.ofRealCLM.contDiff).mul contDiff_const))).pow m
  have hR : ContDiff ℝ 2 (fun v : ℝ => Complex.exp (Complex.I * ((c * edgeR (liftEps c * v) : ℝ) : ℂ))) := by
    refine Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul ?_)))
    exact (edgeR_contDiff.of_le (by norm_num)).comp (contDiff_const.mul contDiff_id)
  unfold pcH pcAmp
  exact ((hcpow.mul (Complex.contDiff_exp.comp hbin)).mul hmult).mul hR


/-- Finite bounds for `φ = χ₁ H_c` and its first two derivatives (qualitative; `M` depends on `c, δ₀, m`). -/
theorem exists_bounds_chi_pcH (δ₀ : ℝ) (m : ℕ) {c : ℝ} (hc : 0 < c) {χ₁ : ℝ → ℝ} (hχ : ContDiff ℝ 2 χ₁)
    (hsupp : ∀ v : ℝ, 1 < |v| → χ₁ v = 0) :
    ContDiff ℝ 2 (fun v : ℝ => (χ₁ v : ℂ) * pcH δ₀ m c v) ∧ ∃ M : ℝ,
      (∀ v, ‖(χ₁ v : ℂ) * pcH δ₀ m c v‖ ≤ M) ∧ (∀ v, ‖deriv (fun v : ℝ => (χ₁ v : ℂ) * pcH δ₀ m c v) v‖ ≤ M) ∧
      (∀ v, ‖deriv (deriv (fun v : ℝ => (χ₁ v : ℂ) * pcH δ₀ m c v)) v‖ ≤ M) := by
  set φ : ℝ → ℂ := fun v => (χ₁ v : ℂ) * pcH δ₀ m c v with hφ
  have hφc : ContDiff ℝ 2 φ := (Complex.ofRealCLM.contDiff.comp hχ).mul (contDiff_pcH δ₀ m hc)
  refine ⟨hφc, ?_⟩
  have hz : ∀ v : ℝ, 1 < |v| → φ v = 0 := fun v hv => by simp [hφ, hsupp v hv]
  have hcs : HasCompactSupport φ := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1)) fun v hv => hz v ?_
    by_contra h
    exact hv ⟨(abs_le.mp (not_lt.mp h)).1, (abs_le.mp (not_lt.mp h)).2⟩
  have hcs1 : HasCompactSupport (deriv φ) := hcs.deriv
  have hcs2 : HasCompactSupport (deriv (deriv φ)) := hcs1.deriv
  have c1 : Continuous (deriv φ) := (hφc.iterate_deriv' 1 1).continuous.congr (by intro v; simp)
  have c2 : Continuous (deriv (deriv φ)) := (hφc.iterate_deriv' 0 2).continuous.congr (by intro v; simp)
  obtain ⟨M0, h0⟩ := hcs.exists_bound_of_continuous hφc.continuous
  obtain ⟨M1, h1⟩ := hcs1.exists_bound_of_continuous c1
  obtain ⟨M2, h2⟩ := hcs2.exists_bound_of_continuous c2
  exact ⟨max M0 (max M1 M2), fun v => (h0 v).trans (le_max_left _ _),
    fun v => (h1 v).trans ((le_max_left _ _).trans (le_max_right _ _)),
    fun v => (h2 v).trans ((le_max_right _ _).trans (le_max_right _ _))⟩

/-- info: 'FormalResearch.CohnElkies.contDiffAt_cpow_neg_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.contDiffAt_cpow_neg_half
/-- info: 'FormalResearch.CohnElkies.contDiff_pcH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.contDiff_pcH
/-- info: 'FormalResearch.CohnElkies.exists_bounds_chi_pcH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.exists_bounds_chi_pcH

end FormalResearch.CohnElkies
