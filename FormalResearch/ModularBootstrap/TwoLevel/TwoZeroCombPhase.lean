module

public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroCombT
public import FormalResearch.ModularBootstrap.Upper.Design.CombTransformAbs
public import FormalResearch.ModularBootstrap.Upper.Design.CombTransform
public import FormalResearch.ModularBootstrap.Upper.Membership.SaddleTail
public import FormalResearch.ModularBootstrap.Upper.Membership.CombDecay

/-!
# Multiplying a comb by a real strip factor `T_ζ` (`upper_transfer.tex`, `ut:T2`, "Phase and membership")

For a comb `B` with phase `log B = c'Φ₀ + Φ₁` on `𝒩` and a real site `ζ ≥ 0`, the comb `T_ζ B` has phase
`Φ₁ + (iπ + φ_ζ)`, since `T_ζ = e^{iπ + φ_ζ}` (`K1(d)`, `blaschkeT_eq_exp`): the TeX's
`Φ₁ = 2πi - (5/2)φ̄ + ⋯ + (φ_{χ(p)} - φ̄) + Δ₁` is `designPhi1 + iπ + φ_{χ(p)}` (`twoZeroPhi1`).  The derivative bound
for `iπ + φ_ζ` is uniform in `ζ ≥ 0` (`K1(d)`), so no closeness of `ζ` to `ξ_*` is needed for membership.

* `tPhase ζ b = iπ + φ_ζ(b)`; `iteratedDeriv_tPhase_le`: `‖∂_b^i (iπ + φ_ζ)‖ ≤ M_T` on `𝒩`, `i ≤ 2`, uniformly in `ζ ≥ 0`;
* `InnerCombHyp.mul_blaschkeT`: hypotheses (i), (iii) of `K7` (`InnerCombHyp`) are stable under `B ↦ T_ζ B`;
* `CombPhaseData.mul_blaschkeT`: hypothesis (ii) (`CombPhaseData`) of `K7` for `T_ζ B`, with `Φ₁ + tPhase ζ`;
* `PhaseComb.mul_blaschkeT`: the same for the abstract `PhaseComb` of `Design.CombTransformAbs` (Lemmas `SD_V`, `Φ`);
* `designComb_phaseComb_of_decomp`: the finite modifications `designComb` carry a `PhaseComb`.

All results are proved unconditionally.
-/

@[expose] public section

open Complex Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Design

open FormalResearch.ModularBootstrap.Upper.Comb FormalResearch.ModularBootstrap.Upper.Saddle

/-- The finite modifications `designComb` carry a `PhaseComb` with `Φ₁ = designPhi1` (`ut:Phi`; the abstract
interface of `designProfile_sdvHypotheses_of_decomp`). -/
theorem designComb_phaseComb_of_decomp (f : ℕ) (hf : 1 ≤ f) {η₀ : ℝ} (hη₀0 : 0 ≤ η₀)
    (hη₀1 : η₀ ≤ 1 / 4) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ c' in atTop, ∀ (N : ℕ) (σ ε : ℕ → ℝ) (B : ℝ),
      DesignAdmissible c' f N η₀ σ ε → DesignPhiDecomp c' f N η₀ σ ε B →
      PhaseComb c' (A + B) (designComb c' f N η₀ σ ε) (designPhi1 c' f N η₀ σ ε) := by
  obtain ⟨A, hA0, hBev⟩ := designPhi1_bounds_of_decomp f hf hη₀0 hη₀1
  refine ⟨A, hA0, ?_⟩
  filter_upwards [hBev, combTail_K1a_unif hη₀0 hη₀1] with c' hBd hTd N σ ε B hA hDec
  obtain ⟨hT1, hT2, hT3, hT4⟩ := hTd N
  obtain ⟨hK1, -, -⟩ := designComb_K1a hA hT1 hT2 hT3
  obtain ⟨hΦ1, hder⟩ := hBd N σ ε B hA hDec
  refine ⟨fun _ hb => hK1 hb, fun _ hb => exp_designPhi1_eq hDec hb, hΦ1, hder,
    fun b hb => re_designPhi1_edge hDec hb, fun b hb => ?_⟩
  exact designComb_neg_conj c' f N η₀ σ ε b (hT4 (by rw [hb]; norm_num))

end FormalResearch.ModularBootstrap.Upper.Design

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.ModularBootstrap.Upper.Comb FormalResearch.ModularBootstrap.Upper.Saddle
  FormalResearch.ModularBootstrap.Upper.Design FormalResearch.ModularBootstrap.Upper.Membership

/-! ### 1. The phase `iπ + φ_ζ` of `T_ζ` -/

/-- `iπ + φ_ζ(b)`, the logarithm of `T_ζ(b)` on `𝒩` (`T_ζ = exp (iπ + φ_ζ)`). -/
noncomputable def tPhase (ζ : ℂ) (b : ℂ) : ℂ := (π : ℂ) * Complex.I + phiZeta ζ b

lemma differentiableOn_tPhase {ζ : ℝ} (hζ : -1 / 4 < ζ) : DifferentiableOn ℂ (tPhase (ζ : ℂ)) combNOpen :=
  fun _ hb => ((hasDerivAt_phiZeta_b hb (ofReal_mem_combZOpen' hζ)).differentiableAt.const_add
    ((π : ℂ) * Complex.I)).differentiableWithinAt

lemma analyticOnNhd_tPhase {ζ : ℝ} (hζ : -1 / 4 < ζ) : AnalyticOnNhd ℂ (tPhase (ζ : ℂ)) combNOpen :=
  (differentiableOn_tPhase hζ).analyticOnNhd isOpen_combNOpen

/-- **Uniform bound for the phase of `T_ζ`** (`K1(d)`): `‖∂_b^i (iπ + φ_ζ)‖ ≤ π + C_φ` on `𝒩`, `i ≤ 2`,
for every real `ζ ≥ 0`. -/
theorem iteratedDeriv_tPhase_le :
    ∃ Cφ : ℝ, 0 ≤ Cφ ∧ ∀ (i : ℕ), i ≤ 2 → ∀ {ζ : ℝ} {b : ℂ}, 0 ≤ ζ → b ∈ combN →
      ‖iteratedDeriv i (tPhase (ζ : ℂ)) b‖ ≤ π + Cφ := by
  obtain ⟨C, hC, -, hbd⟩ := combPhiDeriv_bound
  refine ⟨C, hC.le, fun i hi ζ b hζ hb => ?_⟩
  have hbo : b ∈ combNOpen := combN_subset_combNOpen hb
  have hbm : b ∈ combNMid := combN_subset_combNMid hb
  have hz : (ζ : ℂ) ∈ combZ := ofReal_mem_combZ' hζ
  have hzo : (ζ : ℂ) ∈ combZOpen := ofReal_mem_combZOpen' (by linarith)
  have hcd : ‖combPhiDeriv i 0 (ζ : ℂ) b‖ ≤ C := by
    calc ‖combPhiDeriv i 0 (ζ : ℂ) b‖ ≤ C * min 1 (Real.exp (-π * ((ζ : ℂ).re - |b.re|))) :=
          hbd i 0 (by omega) hbm hz
      _ ≤ C * 1 := by gcongr; exact min_le_left _ _
      _ = C := mul_one C
  have e1 := iteratedDeriv_combPhiDeriv_b i 0 hbo hzo
  have e3 : (fun b' => combPhiDeriv 0 0 (ζ : ℂ) b') = fun b' => phiZeta (ζ : ℂ) b' := by
    funext b'; exact combPhiDeriv_zero _ _
  rw [e3] at e1
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · simp only [iteratedDeriv_zero] at e1 ⊢
    have h0 : ‖tPhase (ζ : ℂ) b‖ ≤ π + ‖phiZeta (ζ : ℂ) b‖ := by
      unfold tPhase
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
    rw [e1] at h0
    linarith
  · have : iteratedDeriv i (tPhase (ζ : ℂ)) b = iteratedDeriv i (fun b' => phiZeta (ζ : ℂ) b') b :=
      iteratedDeriv_const_add (f := fun b' => phiZeta (ζ : ℂ) b') hipos ((π : ℂ) * Complex.I)
    rw [this, e1]
    linarith [Real.pi_pos]

/-- `iteratedDeriv` of a sum `Φ₁ + tPhase ζ` (`Φ₁` analytic at `b`, `i ≤ 2`). -/
lemma iteratedDeriv_add_tPhase {Φ₁ : ℂ → ℂ} {ζ : ℝ} (hζ : -1 / 4 < ζ) {b : ℂ} (hb : b ∈ combN)
    (hΦ : AnalyticAt ℂ Φ₁ b) (i : ℕ) :
    iteratedDeriv i (fun w => Φ₁ w + tPhase (ζ : ℂ) w) b =
      iteratedDeriv i Φ₁ b + iteratedDeriv i (tPhase (ζ : ℂ)) b :=
  iteratedDeriv_fun_add (hΦ.contDiffAt.of_le (by exact_mod_cast le_top))
    (((analyticOnNhd_tPhase hζ) b (combN_subset_combNOpen hb)).contDiffAt.of_le
      (by exact_mod_cast le_top))

lemma norm_iteratedDeriv_add_tPhase_le {Φ₁ : ℂ → ℂ} {M ζ : ℝ} {Cφ : ℝ} (hζ : 0 ≤ ζ) {b : ℂ}
    (hb : b ∈ combN) (hΦ : AnalyticAt ℂ Φ₁ b) {i : ℕ} (hi : i ≤ 2)
    (hM : ‖iteratedDeriv i Φ₁ b‖ ≤ M)
    (hT : ∀ (i : ℕ), i ≤ 2 → ‖iteratedDeriv i (tPhase (ζ : ℂ)) b‖ ≤ π + Cφ) :
    ‖iteratedDeriv i (fun w => Φ₁ w + tPhase (ζ : ℂ) w) b‖ ≤ M + (π + Cφ) := by
  rw [iteratedDeriv_add_tPhase (by linarith) hb hΦ i]
  exact (norm_add_le _ _).trans (add_le_add hM (hT i hi))

/-! ### 2. Stability of the `K7` hypotheses under `B ↦ T_ζ B` -/

/-- Hypotheses (i), (iii) of Lemma `K7` are stable under multiplication by `T_ζ`, `ζ` real. -/
theorem _root_.FormalResearch.ModularBootstrap.Upper.Membership.InnerCombHyp.mul_blaschkeT {c' : ℝ} {B : ℂ → ℂ} (h : InnerCombHyp c' B) (ζ : ℝ) :
    InnerCombHyp c' (fun b => blaschkeT (ζ : ℂ) b * B b) := by
  have hdiff : DifferentiableOn ℂ (blaschkeT (ζ : ℂ)) {b : ℂ | |b.im| < 7 / 8} := fun b hb => by
    have hb' : |b.im| < 7 / 8 := hb
    have : |b.im| + |(ζ : ℂ).im| < 1 := by
      rw [Complex.ofReal_im, abs_zero, add_zero]; linarith
    exact (differentiableAt_blaschkeT this).differentiableWithinAt
  refine ⟨fun r => ?_, fun r => ?_, hdiff.mul h.holo, fun b hb => ?_, fun v => ?_, ?_⟩
  · simp only [blaschkeT_neg_b, h.even r]
  · have h1 : (blaschkeT (ζ : ℂ) (r : ℂ)).im = 0 := by
      rw [tFac_eq]; exact Complex.ofReal_im _
    simp [Complex.mul_im, h1, h.real r]
  · rw [norm_mul]
    exact (mul_le_mul (norm_blaschkeT_real_le_one ζ hb) (h.bound b hb) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  · rw [norm_mul, norm_blaschkeT_real_eq_one ζ (by simp), h.unit_edge v, one_mul]
  · obtain ⟨C, hC⟩ := h.tail
    refine ⟨C, fun x hx => ?_⟩
    rw [norm_mul]
    have h1 : ‖blaschkeT (ζ : ℂ) (x : ℂ)‖ ≤ 1 := norm_blaschkeT_real_le_one ζ (by simp)
    calc ‖blaschkeT (ζ : ℂ) (x : ℂ)‖ * ‖B (x : ℂ)‖ * Real.exp (c' * (2 * π * x / 3))
        ≤ 1 * ‖B (x : ℂ)‖ * Real.exp (c' * (2 * π * x / 3)) := by
          gcongr
      _ ≤ C := by rw [one_mul]; exact hC x hx

/-- Hypothesis (ii) of Lemma `K7` for `T_ζ B`: phase `Φ₁ + (iπ + φ_ζ)`, `ζ ≥ 0` real. -/
theorem _root_.FormalResearch.ModularBootstrap.Upper.Membership.CombPhaseData.mul_blaschkeT :
    ∃ Cφ : ℝ, 0 ≤ Cφ ∧ ∀ {c' M : ℝ} {B Φ₁ : ℂ → ℂ}, CombPhaseData c' M B Φ₁ → ∀ {ζ : ℝ}, 0 ≤ ζ →
      CombPhaseData c' (M + (π + Cφ)) (fun b => blaschkeT (ζ : ℂ) b * B b)
        (fun b => Φ₁ b + tPhase (ζ : ℂ) b) := by
  obtain ⟨Cφ, hCφ, hT⟩ := iteratedDeriv_tPhase_le
  refine ⟨Cφ, hCφ, fun {c' M B Φ₁} h {ζ} hζ => ?_⟩
  have hζ' : -1 / 4 < ζ := by linarith
  refine ⟨?_, fun b hb => ?_, fun v => ?_, fun i hi b hb => ?_⟩
  · intro b hb
    exact (h.holo b hb).add ((analyticOnNhd_tPhase hζ') b (combN_subset_combNOpen hb))
  · have hbN : b ∈ combN := hb
    have hT : blaschkeT (ζ : ℂ) b = Complex.exp (tPhase (ζ : ℂ) b) :=
      blaschkeT_eq_exp hbN (ofReal_mem_combZ' hζ)
    calc blaschkeT (ζ : ℂ) b * B b
        = Complex.exp (tPhase (ζ : ℂ) b) * Complex.exp ((c' : ℂ) * edgePhi0Blaschke b + Φ₁ b) := by
          rw [h.eq b hb, ← hT]
      _ = Complex.exp ((c' : ℂ) * edgePhi0Blaschke b + (Φ₁ b + tPhase (ζ : ℂ) b)) := by
          rw [← Complex.exp_add]; ring_nf
  · have hb : ((v : ℂ) + Complex.I / 2).im = 1 / 2 := by simp
    have h1 := h.re_edge v
    have h2 : (tPhase (ζ : ℂ) ((v : ℂ) + Complex.I / 2)).re = 0 := by
      unfold tPhase
      have := phiZeta_re_eq_zero_of_im_half hζ hb
      simpa [Complex.add_re, Complex.mul_re] using this
    simp only [Complex.add_re, h1, h2, add_zero]
  · exact norm_iteratedDeriv_add_tPhase_le hζ hb (h.holo b hb : AnalyticAt ℂ Φ₁ b) hi (h.bound i hi b hb)
      (fun j hj => hT j hj hζ hb)

/-- The abstract `PhaseComb` of `Design.CombTransformAbs` is stable under `B ↦ T_ζ B`, `Φ₁ ↦ Φ₁ + iπ + φ_ζ`
(`ζ ≥ 0` real; `M_φ ↦ M_φ + π + C_φ`). -/
theorem _root_.FormalResearch.ModularBootstrap.Upper.Design.PhaseComb.mul_blaschkeT :
    ∃ Cφ : ℝ, 0 ≤ Cφ ∧ ∀ {c' M : ℝ} {B Φ₁ : ℂ → ℂ}, PhaseComb c' M B Φ₁ → ∀ {ζ : ℝ}, 0 ≤ ζ →
      PhaseComb c' (M + (π + Cφ)) (fun b => blaschkeT (ζ : ℂ) b * B b)
        (fun b => Φ₁ b + tPhase (ζ : ℂ) b) := by
  obtain ⟨Cφ, hCφ, hT⟩ := iteratedDeriv_tPhase_le
  refine ⟨Cφ, hCφ, fun {c' M B Φ₁} h {ζ} hζ => ?_⟩
  have hζ' : -1 / 4 < ζ := by linarith
  have d1 : ∀ (F : ℂ → ℂ) (b : ℂ), deriv F b = iteratedDeriv 1 F b := fun F b => by
    rw [iteratedDeriv_one]
  have d2 : ∀ (F : ℂ → ℂ) (b : ℂ), deriv (deriv F) b = iteratedDeriv 2 F b := fun F b => by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hdiff : DifferentiableOn ℂ (fun b => Φ₁ b + tPhase (ζ : ℂ) b) combNMid :=
    h.diff.add ((differentiableOn_tPhase hζ').mono combNMid_subset_combNOpen)
  have han : ∀ b ∈ combN, AnalyticAt ℂ Φ₁ b := fun b hb =>
    (h.diff.analyticOnNhd isOpen_combNMid) b (combN_subset_combNMid hb)
  have hit : ∀ b ∈ combN, ∀ i : ℕ, 1 ≤ i → i ≤ 2 →
      ‖iteratedDeriv i (fun w => Φ₁ w + tPhase (ζ : ℂ) w) b‖ ≤ M + (π + Cφ) := fun b hb i hi1 hi2 => by
    refine norm_iteratedDeriv_add_tPhase_le hζ hb (han b hb) hi2 ?_ (fun j hj => hT j hj hζ hb)
    interval_cases i
    · rw [← d1]; exact (h.deriv_bound b hb).1
    · rw [← d2]; exact (h.deriv_bound b hb).2
  refine ⟨fun b hb => ?_, fun b hb => ?_, hdiff, fun b hb => ⟨?_, ?_⟩, fun b hb => ?_, fun b hb => ?_⟩
  · rw [norm_mul]
    exact (mul_le_mul (norm_blaschkeT_real_le_one ζ hb) (h.bound b hb) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  · have hT : blaschkeT (ζ : ℂ) b = Complex.exp (tPhase (ζ : ℂ) b) :=
      blaschkeT_eq_exp hb (ofReal_mem_combZ' hζ)
    calc Complex.exp ((c' : ℂ) * edgePhi0Blaschke b + (Φ₁ b + tPhase (ζ : ℂ) b))
        = Complex.exp ((c' : ℂ) * edgePhi0Blaschke b + Φ₁ b) * Complex.exp (tPhase (ζ : ℂ) b) := by
          rw [← Complex.exp_add]; ring_nf
      _ = blaschkeT (ζ : ℂ) b * B b := by
          rw [h.eq b hb, ← hT, mul_comm]
  · rw [d1]; exact hit b hb 1 le_rfl (by norm_num)
  · rw [d2]; exact hit b hb 2 (by norm_num) le_rfl
  · have hbim : b.im = 1 / 2 := hb
    have h1 := h.re_edge b hbim
    have h2 : (tPhase (ζ : ℂ) b).re = 0 := by
      unfold tPhase
      have := phiZeta_re_eq_zero_of_im_half hζ hbim
      simpa [Complex.add_re, Complex.mul_re] using this
    simp only [Complex.add_re, h1, h2, add_zero]
  · have hbim : b.im = 1 / 2 := hb
    rw [map_mul, ← h.symm_edge b hbim, blaschkeT_ofReal_neg_conj]

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Upper.Design.designComb_phaseComb_of_decomp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Design.designComb_phaseComb_of_decomp

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.iteratedDeriv_tPhase_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.TwoLevel.iteratedDeriv_tPhase_le

/-- info: 'FormalResearch.ModularBootstrap.Upper.Membership.InnerCombHyp.mul_blaschkeT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Membership.InnerCombHyp.mul_blaschkeT

/-- info: 'FormalResearch.ModularBootstrap.Upper.Membership.CombPhaseData.mul_blaschkeT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Membership.CombPhaseData.mul_blaschkeT

/-- info: 'FormalResearch.ModularBootstrap.Upper.Design.PhaseComb.mul_blaschkeT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Design.PhaseComb.mul_blaschkeT

end FormalResearch.ModularBootstrap.TwoLevel
