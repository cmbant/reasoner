/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctClaimG

/-!
# Claim G, perturbative form (F2a, `fct:comp-cfu`)

For `E(y,t) = m₀ t + N(y,t)` with `N` small in `C^k` jointly in `(y,t)`: the root `w(y)` is unique, `C^k`, and
`‖w‖_{C^k} ≤ C(k,m₀) ‖N‖_{C^k}` (`claim_G_pert`).  This is the form needed for the perturbative implicit functions of
the scalar cubic chart (the critical point `B`, the inverse `Z` of `Y = z D²`); it needs no divided differences.
Same proof as `claim_G`.

Class: proved, no hypotheses beyond those stated.
-/

@[expose] public section

open Set Filter Topology
open scoped ContDiff

namespace FormalResearch.SignUncertainty

section ClaimGPert
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

lemma JB.fderiv_apply_le {U : Set (Y × ℝ)} (hU : IsOpen U) {k : ℕ} (hk : 1 ≤ k) {N : Y × ℝ → ℝ} {ε : ℝ}
    (h : JB k U N ε) {p : Y × ℝ} (hp : p ∈ U) : |fderiv ℝ N p (0, 1)| ≤ ε := by
  have h1 := ((h.mono_order hk).succ_fderivWithin (j := 0) hU.uniqueDiffOn) 0 le_rfl p hp
  have h2 : ‖iteratedFDerivWithin ℝ 0 (fderivWithin ℝ N U) U p‖ = ‖fderiv ℝ N p‖ := by
    simp [iteratedFDerivWithin_zero_eq_comp, fderivWithin_of_isOpen hU hp]
  rw [h2] at h1
  have h3 : ‖fderiv ℝ N p (0, 1)‖ ≤ ‖fderiv ℝ N p‖ * ‖((0 : Y), (1 : ℝ))‖ := (fderiv ℝ N p).le_opNorm _
  have hn : ‖((0 : Y), (1 : ℝ))‖ = 1 := by simp [Prod.norm_def]
  rw [hn, mul_one] at h3
  have h4 : |fderiv ℝ N p (0, 1)| ≤ ‖fderiv ℝ N p‖ := by simpa using h3
  exact h4.trans h1


lemma hasDerivAt_pert_line {m0 : ℝ} {N : Y × ℝ → ℝ} {y : Y} {t : ℝ} (hN : DifferentiableAt ℝ N (y, t)) :
    HasDerivAt (fun s => m0 * s + N (y, s)) (m0 + fderiv ℝ N (y, t) (0, 1)) t := by
  have h2 : HasDerivAt (fun s : ℝ => m0 * s) m0 t := by simpa using (hasDerivAt_id t).const_mul m0
  exact h2.add (hasDerivAt_line hN)

lemma claimGP_root {O : Set Y} {k : ℕ} (hk : 1 ≤ k) (hO : IsOpen O) {w0 m0 ε : ℝ} (hm0 : 0 < m0) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ m0 / 2) (hεw : ε < m0 / 2 * w0) {N : Y × ℝ → ℝ} (hN : ContDiffOn ℝ k N (O ×ˢ Ioo (-w0) w0))
    (hNb : JB k (O ×ˢ Ioo (-w0) w0) N ε) :
    ∀ y ∈ O, ∃ t ∈ Ioo (-w0) w0, m0 * t + N (y, t) = 0 ∧ |t| ≤ ε / (m0 / 2) ∧
      ∀ s ∈ Ioo (-w0) w0, m0 * s + N (y, s) = 0 → s = t := by
  intro y hy
  have hk0 : (k : ℕ∞ω) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hU : IsOpen (O ×ˢ Ioo (-w0) w0) := hO.prod isOpen_Ioo
  refine exists_unique_root (h := fun s => m0 * s + N (y, s)) (h' := fun t => m0 + fderiv ℝ N (y, t) (0, 1))
    (half_pos hm0) hε0 hεw
    (fun t ht => hasDerivAt_pert_line ((diffAt_of_mem hO hN hy ht).differentiableAt hk0)) ?_ ?_
  · intro t ht
    have := JB.fderiv_apply_le hU hk hNb (p := (y, t)) ⟨hy, ht⟩
    have := (abs_le.mp this).1
    linarith
  · have hw0 : 0 < w0 := by
      by_contra h
      nlinarith
    have := hNb.apply_le (y := (y, 0)) ⟨hy, ⟨by linarith, hw0⟩⟩
    simpa using this

lemma claimGP_smooth [CompleteSpace Y] {O : Set Y} {k : ℕ} (hk : 1 ≤ k) (hO : IsOpen O) {w0 m0 ε : ℝ}
    (hm0 : 0 < m0) (hε1 : ε ≤ m0 / 2) {N : Y × ℝ → ℝ} (hN : ContDiffOn ℝ k N (O ×ˢ Ioo (-w0) w0))
    (hNb : JB k (O ×ˢ Ioo (-w0) w0) N ε) {w : Y → ℝ}
    (hw : ∀ y ∈ O, w y ∈ Ioo (-w0) w0 ∧ m0 * w y + N (y, w y) = 0 ∧
      ∀ s ∈ Ioo (-w0) w0, m0 * s + N (y, s) = 0 → s = w y) :
    ContDiffOn ℝ k w O := by
  intro y0 hy0
  refine ContDiffAt.contDiffWithinAt ?_
  obtain ⟨ht0, hz0, -⟩ := hw y0 hy0
  set t0 := w y0 with ht0def
  have hU : IsOpen (O ×ˢ Ioo (-w0) w0) := hO.prod isOpen_Ioo
  set Ef : Y × ℝ → ℝ := fun p => m0 * p.2 + N p with hEf
  have hNat : ContDiffAt ℝ k N (y0, t0) := diffAt_of_mem hO hN hy0 ht0
  have cdf : ContDiffAt ℝ k Ef (y0, t0) := (contDiffAt_snd.const_smul m0 |>.congr_of_eventuallyEq
    (Eventually.of_forall fun p => by simp)).add hNat
  have hk0 : (k : ℕ∞ω) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hder : fderiv ℝ Ef (y0, t0) (0, 1) = m0 + fderiv ℝ N (y0, t0) (0, 1) := by
    have h1 : HasDerivAt (fun s : ℝ => (y0, s)) ((0 : Y), (1 : ℝ)) t0 :=
      (hasDerivAt_const t0 y0).prodMk (hasDerivAt_id t0)
    have h2 := (cdf.differentiableAt hk0).hasFDerivAt.comp_hasDerivAt t0 h1
    exact h2.unique (hasDerivAt_pert_line (hNat.differentiableAt hk0))
  have hc : 0 < m0 + fderiv ℝ N (y0, t0) (0, 1) := by
    have := (abs_le.mp (JB.fderiv_apply_le hU hk hNb (p := (y0, t0)) ⟨hy0, ht0⟩)).1
    linarith
  have hL : ∀ x : ℝ, (fderiv ℝ Ef (y0, t0) ∘L ContinuousLinearMap.inr ℝ Y ℝ) x =
      (m0 + fderiv ℝ N (y0, t0) (0, 1)) * x := by
    intro x
    have : ((0 : Y), x) = x • ((0 : Y), (1 : ℝ)) := by simp
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.inr_apply]
    rw [this, map_smul, hder, smul_eq_mul, mul_comm]
  have if₂ : (fderiv ℝ Ef (y0, t0) ∘L ContinuousLinearMap.inr ℝ Y ℝ).IsInvertible := by
    refine ContinuousLinearMap.IsInvertible.of_inverse
      (g := (m0 + fderiv ℝ N (y0, t0) (0, 1))⁻¹ • ContinuousLinearMap.id ℝ ℝ) ?_ ?_
    · ext
      simp [hL, hc.ne']
    · ext
      simp [hL, hc.ne']
  set ψ := cdf.implicitFunction hk0 if₂ with hψ
  have hψd : ContDiffAt ℝ k ψ y0 := cdf.contDiffAt_implicitFunction hk0 if₂
  have hψ0 : ψ y0 = t0 := cdf.implicitFunction_apply_self hk0 if₂
  have e1 := cdf.eventually_apply_implicitFunction hk0 if₂
  have e2 : ∀ᶠ y in 𝓝 y0, ψ y ∈ Ioo (-w0) w0 :=
    hψd.continuousAt.eventually_mem (isOpen_Ioo.mem_nhds (by rw [hψ0]; exact ht0))
  have e3 : ∀ᶠ y in 𝓝 y0, y ∈ O := hO.mem_nhds hy0
  have hEu : Ef (y0, t0) = 0 := hz0
  have : w =ᶠ[𝓝 y0] ψ := by
    filter_upwards [e1, e2, e3] with y h1 h2 h3
    obtain ⟨-, -, hu⟩ := hw y h3
    exact (hu _ h2 (h1.trans hEu)).symm
  exact hψd.congr_of_eventuallyEq this

lemma claimGP_deriv {O : Set Y} {k : ℕ} (hk : 1 ≤ k) (hO : IsOpen O) {w0 m0 ε : ℝ} (hm0 : 0 < m0)
    (hε1 : ε ≤ m0 / 2) {N : Y × ℝ → ℝ} (hN : ContDiffOn ℝ k N (O ×ˢ Ioo (-w0) w0))
    (hNb : JB k (O ×ˢ Ioo (-w0) w0) N ε) {w : Y → ℝ} (hwd : ContDiffOn ℝ k w O)
    (hw : ∀ y ∈ O, w y ∈ Ioo (-w0) w0 ∧ m0 * w y + N (y, w y) = 0) {y : Y} (hy : y ∈ O) :
    fderiv ℝ w y = -(m0 + fderiv ℝ N (y, w y) (0, 1))⁻¹ •
      (fderiv ℝ N (y, w y)).comp (ContinuousLinearMap.inl ℝ Y ℝ) := by
  have hk0 : (k : ℕ∞ω) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hU : IsOpen (O ×ˢ Ioo (-w0) w0) := hO.prod isOpen_Ioo
  have hc : 0 < m0 + fderiv ℝ N (y, w y) (0, 1) := by
    have := (abs_le.mp (JB.fderiv_apply_le hU hk hNb (p := (y, w y)) ⟨hy, (hw y hy).1⟩)).1
    linarith
  have hw' : HasFDerivAt w (fderiv ℝ w y) y :=
    ((hwd.contDiffAt (hO.mem_nhds hy)).differentiableAt hk0).hasFDerivAt
  have hΦ : HasFDerivAt (fun y => (y, w y)) ((ContinuousLinearMap.id ℝ Y).prod (fderiv ℝ w y)) y :=
    (hasFDerivAt_id y).prodMk hw'
  have hN1 : HasFDerivAt N (fderiv ℝ N (y, w y)) (y, w y) :=
    ((diffAt_of_mem hO hN hy (hw y hy).1).differentiableAt hk0).hasFDerivAt
  have hN' := hN1.comp y hΦ
  have hg := (hw'.const_mul m0).add hN'
  have hz : HasFDerivAt (fun y => m0 * w y + N (y, w y)) (0 : Y →L[ℝ] ℝ) y := by
    refine (hasFDerivAt_const (0 : ℝ) y).congr_of_eventuallyEq ?_
    filter_upwards [hO.mem_nhds hy] with z hz using (hw z hz).2
  have h0 := hg.unique hz
  ext v
  have h1 := congrArg (fun L : Y →L[ℝ] ℝ => L v) h0
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, zero_apply] at h1
  have h2 : fderiv ℝ N (y, w y) (v, fderiv ℝ w y v) =
      fderiv ℝ N (y, w y) (v, 0) + fderiv ℝ w y v * fderiv ℝ N (y, w y) (0, 1) := by
    have : (v, fderiv ℝ w y v) = (v, (0 : ℝ)) + fderiv ℝ w y v • ((0 : Y), (1 : ℝ)) := by
      ext <;> simp
    rw [this, map_add, map_smul, smul_eq_mul]
  rw [h2] at h1
  simp only [smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul, neg_mul, ContinuousLinearMap.inl_apply]
  field_simp
  linear_combination h1

/-- Constant bounding `(m₀ + ∂_tN)⁻¹` in `JB k'`. -/
noncomputable def claimGPKu (k' : ℕ) (m0 : ℝ) : ℝ :=
  k'.factorial * (k'.factorial * (max 1 (m0 / 2)⁻¹) ^ (k' + 1)) * (max 1 (3 * m0 / 2)) ^ k'

lemma claimGP_aux (k' : ℕ) {O : Set Y} (hO : IsOpen O) {w0 m0 ε : ℝ} (hm0 : 0 < m0) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ m0 / 2) {N : Y × ℝ → ℝ} (hN : ContDiffOn ℝ (k' + 1) N (O ×ˢ Ioo (-w0) w0))
    (hNb : JB (k' + 1) (O ×ˢ Ioo (-w0) w0) N ε) :
    ContDiffOn ℝ k' (fun p => (m0 + fderiv ℝ N p (0, 1))⁻¹) (O ×ˢ Ioo (-w0) w0) ∧
    JB k' (O ×ˢ Ioo (-w0) w0) (fun p => (m0 + fderiv ℝ N p (0, 1))⁻¹) (claimGPKu k' m0) ∧
    ContDiffOn ℝ k' (fun p => (fderiv ℝ N p).comp (ContinuousLinearMap.inl ℝ Y ℝ)) (O ×ˢ Ioo (-w0) w0) ∧
    JB k' (O ×ˢ Ioo (-w0) w0) (fun p => (fderiv ℝ N p).comp (ContinuousLinearMap.inl ℝ Y ℝ)) ε := by
  set U := O ×ˢ Ioo (-w0) w0 with hUdef
  have hU : IsOpen U := hO.prod isOpen_Ioo
  have hUd : UniqueDiffOn ℝ U := hU.uniqueDiffOn
  have hFd : ContDiffOn ℝ k' (fderiv ℝ N) U := hN.fderiv_of_isOpen hU (le_refl _)
  have hFdb : JB k' U (fderiv ℝ N) ε :=
    (hNb.succ_fderivWithin hUd).congr fun p hp => fderivWithin_of_isOpen hU hp
  have hn : ‖((0 : Y), (1 : ℝ))‖ = 1 := by simp [Prod.norm_def]
  have hg : JB k' U (fun p => fderiv ℝ N p (0, 1)) (1 * ε) := by
    have := JB.clm_apply_const hUd hFd ((0 : Y), (1 : ℝ)) hFdb
    rwa [hn] at this
  have hgc : ContDiffOn ℝ k' (fun p => fderiv ℝ N p (0, 1)) U := hFd.clm_apply contDiffOn_const
  have hac : ContDiffOn ℝ k' (fun p => m0 + fderiv ℝ N p (0, 1)) U := contDiffOn_const.add hgc
  have ha : JB k' U (fun p => m0 + fderiv ℝ N p (0, 1)) (3 * m0 / 2) := by
    have := JB.add hUd (contDiffOn_const (c := m0)) hgc (JB.const hUd m0) hg
    refine this.mono ?_
    rw [Real.norm_eq_abs, abs_of_pos hm0]
    linarith
  have hmin : ∀ p ∈ U, m0 / 2 ≤ m0 + fderiv ℝ N p (0, 1) := fun p hp => by
    have := (abs_le.mp (JB.fderiv_apply_le hU (by omega : 1 ≤ k' + 1) hNb hp)).1
    linarith
  have hinv := JB.inv hUd (half_pos hm0) hac hmin ha
  have hGc : ContDiffOn ℝ k' (fun p => (fderiv ℝ N p).comp (ContinuousLinearMap.inl ℝ Y ℝ)) U :=
    (ContinuousLinearMap.precomp ℝ (ContinuousLinearMap.inl ℝ Y ℝ) :
      ((Y × ℝ) →L[ℝ] ℝ) →L[ℝ] (Y →L[ℝ] ℝ)).contDiff.comp_contDiffOn hFd
  exact ⟨hac.inv fun p hp => (lt_of_lt_of_le (half_pos hm0) (hmin p hp)).ne', hinv, hGc,
    JB.comp_inl hUd hε0 hFd hFdb⟩

/-- One step of the derivative-order induction for `claim_G_pert`. -/
noncomputable def claimGPStep (k' j : ℕ) (m0 c : ℝ) : ℝ :=
  max (2 / m0) (2 ^ j * (j.factorial * claimGPKu k' m0 * (max 1 (max 1 c)) ^ j) *
    (j.factorial * (max 1 (max 1 c)) ^ j))

noncomputable def claimGPSeq (k' : ℕ) (m0 : ℝ) : ℕ → ℝ
  | 0 => 2 / m0
  | j + 1 => claimGPStep k' j m0 (claimGPSeq k' m0 j)

lemma claimGPSeq_nonneg (k' : ℕ) {m0 : ℝ} (hm0 : 0 < m0) (j : ℕ) : 0 ≤ claimGPSeq k' m0 j := by
  cases j with
  | zero => show (0:ℝ) ≤ 2 / m0; positivity
  | succ j => exact (show (0:ℝ) ≤ 2 / m0 by positivity).trans (le_max_left _ _)

lemma claimGP_step {k' j : ℕ} (hj : j ≤ k') {O : Set Y} (hO : IsOpen O) {w0 m0 ε c : ℝ} (hm0 : 0 < m0)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ m0 / 2) (hε2 : ε ≤ 1) (hc : 0 ≤ c) {N : Y × ℝ → ℝ}
    (hN : ContDiffOn ℝ (k' + 1) N (O ×ˢ Ioo (-w0) w0)) (hNb : JB (k' + 1) (O ×ˢ Ioo (-w0) w0) N ε)
    {w : Y → ℝ} (hwd : ContDiffOn ℝ (k' + 1) w O)
    (hw : ∀ y ∈ O, w y ∈ Ioo (-w0) w0 ∧ m0 * w y + N (y, w y) = 0) (hw0 : ∀ y ∈ O, |w y| ≤ 2 * ε / m0)
    (ih : JB j O w (c * ε)) :
    JB (j + 1) O w (claimGPStep k' j m0 c * ε) := by
  obtain ⟨huc, hub, hGc, hGb⟩ := claimGP_aux k' hO hm0 hε0 hε1 hN hNb
  set U := O ×ˢ Ioo (-w0) w0 with hUdef
  have hU : IsOpen U := hO.prod isOpen_Ioo
  have hUd : UniqueDiffOn ℝ U := hU.uniqueDiffOn
  have hOd : UniqueDiffOn ℝ O := hO.uniqueDiffOn
  have hjk : (j : ℕ∞ω) ≤ k' := by exact_mod_cast hj
  have hwj : ContDiffOn ℝ j w O := hwd.of_le (by exact_mod_cast (by omega : j ≤ k' + 1))
  have hΦc : ContDiffOn ℝ j (fun y => (y, w y)) O := contDiffOn_id.prodMk hwj
  have hΦU : MapsTo (fun y => (y, w y)) O U := fun y hy => ⟨hy, (hw y hy).1⟩
  have hΦb : ∀ i, 1 ≤ i → i ≤ j → ∀ y ∈ O, ‖iteratedFDerivWithin ℝ i (fun y => (y, w y)) O y‖ ≤ max 1 c := by
    intro i hi1 hij y hy
    refine (norm_iteratedFDerivWithin_graph_le hOd hwj (b := c * ε) (fun i _ hi y hy => ih i hi y hy) i hi1 hij y hy).trans
      (max_le_max le_rfl ?_)
    exact mul_le_of_le_one_right hc hε2
  have hKu0 : 0 ≤ claimGPKu k' m0 := by unfold claimGPKu; positivity
  have huΦ := JB.comp hOd hUd (g := fun p => (m0 + fderiv ℝ N p (0, 1))⁻¹) (huc.of_le hjk) hΦc hΦU hKu0
    (fun y hy i hi => hub i (hi.trans hj) _ (hΦU hy)) hΦb
  have hGΦ := JB.comp hOd hUd (g := fun p => (fderiv ℝ N p).comp (ContinuousLinearMap.inl ℝ Y ℝ))
    (hGc.of_le hjk) hΦc hΦU hε0 (fun y hy i hi => hGb i (hi.trans hj) _ (hΦU hy)) hΦb
  have hCu0 : 0 ≤ (j.factorial : ℝ) * claimGPKu k' m0 * (max 1 (max 1 c)) ^ j := by
    have := hKu0; positivity
  have hCg0 : 0 ≤ (j.factorial : ℝ) * ε * (max 1 (max 1 c)) ^ j := by positivity
  have hGΦc : ContDiffOn ℝ j ((fun p : Y × ℝ => (fderiv ℝ N p).comp (ContinuousLinearMap.inl ℝ Y ℝ)) ∘
      fun y => (y, w y)) O := (hGc.of_le hjk).comp hΦc hΦU
  have huΦc : ContDiffOn ℝ j ((fun p : Y × ℝ => (m0 + fderiv ℝ N p (0, 1))⁻¹) ∘ fun y => (y, w y)) O :=
    (huc.of_le hjk).comp hΦc hΦU
  have hprod := JB.smul_mul hOd hCu0 hCg0 huΦc hGΦc huΦ hGΦ
  have hneg := JB.neg hOd hprod
  have hk1 : (1 : ℕ) ≤ k' + 1 := by omega
  have hk1' : ContDiffOn ℝ ((k' + 1 : ℕ) : ℕ∞ω) N U := by exact_mod_cast hN
  have hfin := hneg.congr (g := fderivWithin ℝ w O) fun y hy => by
    rw [fderivWithin_of_isOpen hO hy,
      claimGP_deriv hk1 hO hm0 hε1 hk1' (by exact_mod_cast hNb) (by exact_mod_cast hwd) hw hy, neg_smul]
    rfl
  have hmain := JB.of_fderivWithin hOd (fun y hy => by simpa [Real.norm_eq_abs] using hw0 y hy) hfin
  refine hmain.mono (max_le ?_ ?_)
  · calc 2 * ε / m0 = 2 / m0 * ε := by ring
      _ ≤ claimGPStep k' j m0 c * ε := mul_le_mul_of_nonneg_right (le_max_left _ _) hε0
  · calc _ = (2 ^ j * ((j.factorial : ℝ) * claimGPKu k' m0 * (max 1 (max 1 c)) ^ j) *
          ((j.factorial : ℝ) * (max 1 (max 1 c)) ^ j)) * ε := by ring
      _ ≤ claimGPStep k' j m0 c * ε := mul_le_mul_of_nonneg_right (le_max_right _ _) hε0

/-- **Claim G, perturbative form.** `E(y,t) = m₀ t + N(y,t)` with `‖N‖_{C^k} ≤ ε ≤ min(1, m₀/2)` jointly in `(y,t)` on
`O × (-w₀,w₀)`, `ε < (m₀/2) w₀`: the root `w(y)` exists, is unique in `(-w₀,w₀)`, is `C^k` and `‖w‖_{C^k} ≤ C(k,m₀) ε`.
Class: proved. -/
theorem claim_G_pert [CompleteSpace Y] {k : ℕ} (hk : 1 ≤ k) {m0 : ℝ} (hm0 : 0 < m0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {O : Set Y}, IsOpen O → ∀ {w0 ε : ℝ}, 0 ≤ ε → ε ≤ m0 / 2 → ε ≤ 1 →
    ε < m0 / 2 * w0 → ∀ {N : Y × ℝ → ℝ}, ContDiffOn ℝ k N (O ×ˢ Ioo (-w0) w0) →
      JB k (O ×ˢ Ioo (-w0) w0) N ε →
      ∃ w : Y → ℝ, ContDiffOn ℝ k w O ∧ JB k O w (C * ε) ∧
        ∀ y ∈ O, w y ∈ Ioo (-w0) w0 ∧ m0 * w y + N (y, w y) = 0 ∧
          ∀ s ∈ Ioo (-w0) w0, m0 * s + N (y, s) = 0 → s = w y := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  refine ⟨claimGPSeq k' m0 (k' + 1), claimGPSeq_nonneg k' hm0 _, ?_⟩
  intro O hO w0 ε hε0 hε1 hε2 hεw N hN hNb
  have hN' : ContDiffOn ℝ (k' + 1) N (O ×ˢ Ioo (-w0) w0) := by exact_mod_cast hN
  have hroot := claimGP_root (by omega) hO hm0 hε0 hε1 hεw hN hNb
  have hex : ∀ y, ∃ t, y ∈ O → (t ∈ Ioo (-w0) w0 ∧ m0 * t + N (y, t) = 0 ∧ |t| ≤ ε / (m0 / 2) ∧
      ∀ s ∈ Ioo (-w0) w0, m0 * s + N (y, s) = 0 → s = t) := by
    intro y
    by_cases hy : y ∈ O
    · obtain ⟨t, h1, h2, h3, h4⟩ := hroot y hy
      exact ⟨t, fun _ => ⟨h1, h2, h3, h4⟩⟩
    · exact ⟨0, fun h => absurd h hy⟩
  choose w hw using hex
  have hwspec : ∀ y ∈ O, w y ∈ Ioo (-w0) w0 ∧ m0 * w y + N (y, w y) = 0 ∧
      ∀ s ∈ Ioo (-w0) w0, m0 * s + N (y, s) = 0 → s = w y :=
    fun y hy => ⟨(hw y hy).1, (hw y hy).2.1, (hw y hy).2.2.2⟩
  have hwd : ContDiffOn ℝ (k' + 1 : ℕ) w O := claimGP_smooth (by omega) hO hm0 hε1 hN hNb hwspec
  have hwd' : ContDiffOn ℝ (k' + 1) w O := by exact_mod_cast hwd
  have hw0 : ∀ y ∈ O, |w y| ≤ 2 * ε / m0 := fun y hy => by
    have := (hw y hy).2.2.1
    have e : ε / (m0 / 2) = 2 * ε / m0 := by field_simp
    rwa [e] at this
  have key : ∀ j, j ≤ k' + 1 → JB j O w (claimGPSeq k' m0 j * ε) := by
    intro j
    induction j with
    | zero =>
      intro _ i hi y hy
      have hi0 : i = 0 := by omega
      subst hi0
      have : ‖iteratedFDerivWithin ℝ 0 w O y‖ = |w y| := by simp [iteratedFDerivWithin_zero_eq_comp]
      rw [this]
      calc |w y| ≤ 2 * ε / m0 := hw0 y hy
        _ = claimGPSeq k' m0 0 * ε := by simp [claimGPSeq]; ring
    | succ j ih =>
      intro hj
      exact claimGP_step (by omega) hO hm0 hε0 hε1 hε2 (claimGPSeq_nonneg k' hm0 j) hN' hNb hwd'
        (fun y hy => ⟨(hw y hy).1, (hw y hy).2.1⟩) hw0 (ih (by omega))
  exact ⟨w, hwd, key (k' + 1) le_rfl, hwspec⟩

end ClaimGPert

/-- info: 'FormalResearch.SignUncertainty.JB.fderiv_apply_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms JB.fderiv_apply_le

/-- info: 'FormalResearch.SignUncertainty.claimGP_smooth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms claimGP_smooth

/-- info: 'FormalResearch.SignUncertainty.claimGP_deriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms claimGP_deriv

/-- info: 'FormalResearch.SignUncertainty.claimGP_aux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms claimGP_aux

/-- info: 'FormalResearch.SignUncertainty.claimGP_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms claimGP_step

/-- info: 'FormalResearch.SignUncertainty.claim_G_pert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms claim_G_pert

end FormalResearch.SignUncertainty
