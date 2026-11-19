module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Charts.ParabolicCylinder
public import FormalResearch.JacobiEigenvectors.Charts.PCExact

/-!
# Paper J, Layer 4 (phase B1): smoothness of the actual `pcU, pcV`

Proved for the actual functions (`pcU a z = Re U(a, z)`, `pcV a z = Re V(a, z)`):

* `contDiff_pcU`, `contDiff_pcV`: for every real `a`, `z ↦ U(a, z)` and `z ↦ V(a, z)` are smooth (`ContDiff ℝ ⊤`, i.e. analytic), from
  the entire dependence on `z` of the vendored lean-DLMF closure (`parabolicCylinderU_entire`, `parabolicCylinderV_entire`);
* `continuous_pcU`, `continuous_pcV`: joint continuity in `(a, z)`.  Proof: Kummer's series `M(a, c, z) = ∑ (a)_n / ((c)_n n!) z^n`, `c ∈ {1/2, 3/2}`, is
  locally uniformly dominated by `((1 + 2R) R)^n / n!` (`kummer_term_le`, from `|(a)_n| ≤ (R)_n` and `(c)_n >= (1/2)_n`, `(R + j) <= (1 + 2R)(1/2 + j)`),
  so it is jointly continuous (`continuous_kummerM_joint`); `U` and `V` are Kummer series times continuous `2^{·}` and reciprocal-Gamma factors.

Not proved: joint smoothness `ContDiff ℝ ⊤` of `(a, z) ↦ U(a, z)`.  The vendored closure has entire dependence on `z` and (once its `Regularized` closure is
vendored) on `a` *separately*; Mathlib has no Osgood or Hartogs theorem.  What the Layer-2/3 consumers use is exactly the slice smoothness and the joint continuity above
(`PCSmoothFacts`).
-/

@[expose] public section
noncomputable section
namespace FormalResearch.JacobiEigenvectors.Charts
open DLMF.Confluent DLMF.Hypergeometric
open scoped Nat

lemma norm_pochhammer_le (a : ℂ) (R : ℝ) (ha : ‖a‖ ≤ R) (n : ℕ) :
    ‖pochhammer a n‖ ≤ ∏ j ∈ Finset.range n, (R + j) := by
  induction n with
  | zero => simp [pochhammer_zero]
  | succ n ih =>
    rw [pochhammer_succ, norm_mul, Finset.prod_range_succ]
    refine mul_le_mul ih ?_ (norm_nonneg _) (Finset.prod_nonneg fun j _ => ?_)
    · calc ‖a + n‖ ≤ ‖a‖ + ‖(n : ℂ)‖ := norm_add_le _ _
        _ ≤ R + n := by simp; linarith
    · have : 0 ≤ ‖a‖ := norm_nonneg _
      have : (0:ℝ) ≤ j := Nat.cast_nonneg j
      linarith

lemma pochhammer_real_ge (c : ℝ) (hc : 1 / 2 ≤ c) (n : ℕ) :
    ∏ j ∈ Finset.range n, (1 / 2 + (j : ℝ)) ≤ ‖pochhammer (c : ℂ) n‖ := by
  induction n with
  | zero => simp [pochhammer_zero]
  | succ n ih =>
    rw [pochhammer_succ, norm_mul, Finset.prod_range_succ]
    have h1 : ‖(c : ℂ) + n‖ = c + n := by
      rw [show (c : ℂ) + n = ((c + n : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
    rw [h1]
    refine mul_le_mul ih (by linarith) (by positivity) (norm_nonneg _)

lemma kummer_term_le (c : ℝ) (hc : 1 / 2 ≤ c) (R : ℝ) (hR : 0 ≤ R) (a z : ℂ) (ha : ‖a‖ ≤ R) (hz : ‖z‖ ≤ R) (n : ℕ) :
    ‖pochhammer a n / (pochhammer (c : ℂ) n * n !) * z ^ n‖ ≤ ((1 + 2 * R) * R) ^ n / n ! := by
  have hP := norm_pochhammer_le a R ha n
  have hQ := pochhammer_real_ge c hc n
  have hprod : ∏ j ∈ Finset.range n, (R + (j : ℝ)) ≤ (1 + 2 * R) ^ n * ∏ j ∈ Finset.range n, (1 / 2 + (j : ℝ)) := by
    have e : (1 + 2 * R) ^ n = ∏ j ∈ Finset.range n, (1 + 2 * R) := by simp
    rw [e, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod₀
    · intro j _; positivity
    · intro j _
      have : (0:ℝ) ≤ j := Nat.cast_nonneg j
      nlinarith
  have hQpos : 0 < ∏ j ∈ Finset.range n, (1 / 2 + (j : ℝ)) :=
    Finset.prod_pos fun j _ => by positivity
  have hf : (0:ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
  rw [norm_mul, norm_div, norm_mul, norm_pow]
  have hfn : ‖((n ! : ℕ) : ℂ)‖ = (n ! : ℝ) := by simp
  rw [hfn]
  have hz' : ‖z‖ ^ n ≤ R ^ n := pow_le_pow_left₀ (norm_nonneg _) hz n
  have hden : ((1 + 2 * R) ^ n * ∏ j ∈ Finset.range n, (1 / 2 + (j : ℝ))) * (n ! : ℝ) ≥ 0 := by positivity
  calc ‖pochhammer a n‖ / (‖pochhammer (c : ℂ) n‖ * (n ! : ℝ)) * ‖z‖ ^ n
      ≤ ((1 + 2 * R) ^ n * ∏ j ∈ Finset.range n, (1 / 2 + (j : ℝ))) / (( ∏ j ∈ Finset.range n, (1 / 2 + (j : ℝ))) * (n ! : ℝ)) * R ^ n := by
        gcongr
        exact hP.trans hprod
    _ = ((1 + 2 * R) * R) ^ n / n ! := by
        rw [mul_pow]; field_simp

/-- Joint continuity of Kummer's `M(a, c, z)` in `(a, z)` for a fixed real `c >= 1/2`. -/
lemma continuous_kummerM_joint (c : ℝ) (hc : 1 / 2 ≤ c) :
    Continuous (fun p : ℂ × ℂ => kummerM p.1 (c : ℂ) p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  set R : ℝ := ‖p.1‖ + ‖p.2‖ + 1 with hR
  have hR0 : 0 ≤ R := by positivity
  set s : Set (ℂ × ℂ) := {q | ‖q.1‖ < R ∧ ‖q.2‖ < R} with hs
  have hopen : IsOpen s :=
    (isOpen_lt (continuous_norm.comp continuous_fst) continuous_const).inter
      (isOpen_lt (continuous_norm.comp continuous_snd) continuous_const)
  have hps : p ∈ s := ⟨by simp only [hR]; linarith [norm_nonneg p.2], by simp only [hR]; linarith [norm_nonneg p.1]⟩
  have hon : ContinuousOn (fun q : ℂ × ℂ => kummerM q.1 (c : ℂ) q.2) s := by
    unfold kummerM
    refine continuousOn_tsum (u := fun n => ((1 + 2 * R) * R) ^ n / n !) (fun n => ?_)
      (Real.summable_pow_div_factorial _) (fun n q hq => kummer_term_le c hc R hR0 q.1 q.2 hq.1.le hq.2.le n)
    refine Continuous.continuousOn ?_
    have h1 : Continuous (fun a : ℂ => pochhammer a n) := by
      unfold pochhammer; exact Polynomial.continuous _
    exact ((h1.comp continuous_fst).div_const _).mul ((continuous_snd).pow n)
  exact hon.continuousAt (hopen.mem_nhds hps)

lemma continuous_cpow_two : Continuous (fun w : ℂ => (2 : ℂ) ^ w) :=
  Continuous.const_cpow continuous_id (Or.inl two_ne_zero)

lemma continuous_inv_Gamma : Continuous (fun w : ℂ => (Complex.Gamma w)⁻¹) :=
  Complex.differentiable_one_div_Gamma.continuous

lemma continuous_kummer_half (c : ℝ) (hc : 1 / 2 ≤ c) (α : ℂ) :
    Continuous (fun p : ℂ × ℂ => kummerM (p.1 / 2 + α) (c : ℂ) (p.2 ^ 2 / 2)) :=
  (continuous_kummerM_joint c hc).comp (show Continuous (fun p : ℂ × ℂ => (p.1 / 2 + α, p.2 ^ 2 / 2)) by fun_prop)

lemma continuous_even_joint : Continuous (fun p : ℂ × ℂ => parabolicCylinderEven p.1 p.2) := by
  have h := continuous_kummer_half (1 / 2) le_rfl (1 / 4)
  have e : ((1 / 2 : ℝ) : ℂ) = 1 / 2 := by push_cast; ring
  simp only [e] at h
  exact (show Continuous (fun p : ℂ × ℂ => Complex.exp (-p.2 ^ 2 / 4)) by fun_prop).mul h

lemma continuous_odd_joint : Continuous (fun p : ℂ × ℂ => parabolicCylinderOdd p.1 p.2) := by
  have h := continuous_kummer_half (3 / 2) (by norm_num) (3 / 4)
  have e : ((3 / 2 : ℝ) : ℂ) = 3 / 2 := by push_cast; ring
  simp only [e] at h
  exact ((continuous_snd).mul (show Continuous (fun p : ℂ × ℂ => Complex.exp (-p.2 ^ 2 / 4)) by fun_prop)).mul h

lemma continuous_U_joint : Continuous (fun p : ℂ × ℂ => parabolicCylinderU p.1 p.2) := by
  unfold parabolicCylinderU
  have hG1 : Continuous (fun p : ℂ × ℂ => (Complex.Gamma (3 / 4 + p.1 / 2))⁻¹) :=
    continuous_inv_Gamma.comp (by fun_prop)
  have hG2 : Continuous (fun p : ℂ × ℂ => (Complex.Gamma (1 / 4 + p.1 / 2))⁻¹) :=
    continuous_inv_Gamma.comp (by fun_prop)
  have hp1 : Continuous (fun p : ℂ × ℂ => (2 : ℂ) ^ (-(p.1 / 2 + 1 / 4))) :=
    continuous_cpow_two.comp (by fun_prop)
  have hp2 : Continuous (fun p : ℂ × ℂ => (2 : ℂ) ^ (-(p.1 / 2 - 1 / 4))) :=
    continuous_cpow_two.comp (by fun_prop)
  exact (((continuous_const.mul hp1).mul hG1).mul continuous_even_joint).sub
    (((continuous_const.mul hp2).mul hG2).mul continuous_odd_joint)

lemma continuous_V_joint : Continuous (fun p : ℂ × ℂ => parabolicCylinderV p.1 p.2) := by
  unfold parabolicCylinderV parabolicCylinderVZero parabolicCylinderVDerivZero
  have hA : Continuous (fun p : ℂ × ℂ => (Complex.Gamma (3 / 4 - p.1 / 2))⁻¹) :=
    continuous_inv_Gamma.comp (by fun_prop)
  have hB : Continuous (fun p : ℂ × ℂ => (Complex.Gamma (1 / 4 + p.1 / 2))⁻¹) :=
    continuous_inv_Gamma.comp (by fun_prop)
  have hC : Continuous (fun p : ℂ × ℂ => (Complex.Gamma (1 / 4 - p.1 / 2))⁻¹) :=
    continuous_inv_Gamma.comp (by fun_prop)
  have hD : Continuous (fun p : ℂ × ℂ => (Complex.Gamma (3 / 4 + p.1 / 2))⁻¹) :=
    continuous_inv_Gamma.comp (by fun_prop)
  have hp1 : Continuous (fun p : ℂ × ℂ => (2 : ℂ) ^ (p.1 / 2 + 1 / 4)) :=
    continuous_cpow_two.comp (by fun_prop)
  have hp2 : Continuous (fun p : ℂ × ℂ => (2 : ℂ) ^ (p.1 / 2 + 3 / 4)) :=
    continuous_cpow_two.comp (by fun_prop)
  exact (((continuous_const.mul hp1).mul (hA.pow 2)).mul hB |>.mul continuous_even_joint).add
    (((continuous_const.mul hp2).mul (hC.pow 2)).mul hD |>.mul continuous_odd_joint)

lemma continuous_ofReal_pair : Continuous (fun p : ℝ × ℝ => ((p.1 : ℂ), (p.2 : ℂ))) :=
  (Complex.continuous_ofReal.comp continuous_fst).prodMk (Complex.continuous_ofReal.comp continuous_snd)

/-- Joint continuity of the real restrictions. -/
theorem continuous_pcU : Continuous (fun p : ℝ × ℝ => pcU p.1 p.2) := by
  have h : Continuous (fun p : ℝ × ℝ => parabolicCylinderU (p.1 : ℂ) (p.2 : ℂ)) := by
    have := continuous_U_joint.comp continuous_ofReal_pair
    exact this
  exact Complex.continuous_re.comp h

theorem continuous_pcV : Continuous (fun p : ℝ × ℝ => pcV p.1 p.2) := by
  have h : Continuous (fun p : ℝ × ℝ => parabolicCylinderV (p.1 : ℂ) (p.2 : ℂ)) := by
    have := continuous_V_joint.comp continuous_ofReal_pair
    exact this
  exact Complex.continuous_re.comp h


/-- `U(a, ·)` is smooth (indeed analytic) on `ℝ`, for every real `a`. -/
theorem contDiff_pcU (a : ℝ) : ContDiff ℝ ⊤ (pcU a) := by
  have h : ContDiff ℂ ⊤ (parabolicCylinderU (a : ℂ)) := (parabolicCylinderU_entire (a : ℂ)).contDiff
  exact Complex.reCLM.contDiff.comp ((h.restrict_scalars ℝ).comp Complex.ofRealCLM.contDiff)

theorem contDiff_pcV (a : ℝ) : ContDiff ℝ ⊤ (pcV a) := by
  have h : ContDiff ℂ ⊤ (parabolicCylinderV (a : ℂ)) := (parabolicCylinderV_entire (a : ℂ)).contDiff
  exact Complex.reCLM.contDiff.comp ((h.restrict_scalars ℝ).comp Complex.ofRealCLM.contDiff)


/-- **The regularity part of `ParabolicCylinderFacts` holds for the actual functions**. -/
theorem pcSmoothFacts : PCSmoothFacts pcU pcV where
  slice_U := contDiff_pcU
  slice_V := contDiff_pcV
  cont_U := continuous_pcU
  cont_V := continuous_pcV

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.continuous_kummerM_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms continuous_kummerM_joint

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.continuous_pcU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms continuous_pcU

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.continuous_pcV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms continuous_pcV

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.contDiff_pcU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms contDiff_pcU

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.contDiff_pcV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms contDiff_pcV

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.pcSmoothFacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pcSmoothFacts

end FormalResearch.JacobiEigenvectors.Charts
