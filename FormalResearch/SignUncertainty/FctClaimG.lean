/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctJet
public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Claim G: quantitative `C^k` implicit function bound (F2a, `fct:comp-cfu`)

Paper Lemma `fct:comp-cfu`, Claim G.  For `E(y,t) = E₀(y) + t F(y,t)` on an open parameter set `O` with
`‖E₀‖_{C^k} ≤ ε ≤ 1`, `‖F‖_{C^k} ≤ K`, `∂_tE ≥ m > 0` on `O × (-w₀,w₀)`, `w₀ ≤ 1`, `ε < m w₀`: the root
`w(y) ∈ (-w₀,w₀)` exists, is unique, is `C^k` on `O`, and `‖w‖_{C^k} ≤ C(k,m,K) ε` (`claim_G`).

The `C^k` norm is `JB k` of `FctJet` (iterated Fréchet derivatives, operator norms, comparable to the paper's sup of
partial derivatives up to a factor depending on `k` and the dimension).  Differences from the paper's statement:
`O` is open instead of a box (the paper's box is handled by applying the lemma on an open neighbourhood), the root is
unique in the open interval `(-w₀,w₀)`, and the sign `∂_tE ≥ m` is fixed (the case `∂_tE ≤ -m` is the same statement for
`-E₀, -F`).  The smoothness is Mathlib's `ContDiffAt.implicitFunction`; the bound is the induction on the derivative order
for `Dw = -(∂_tE)⁻¹ (DE₀ + w ∂_yF)` (a `JB` closure computation).

Class: proved, no hypotheses beyond those stated.
-/

@[expose] public section

open Set Filter Topology
open scoped ContDiff

namespace FormalResearch.SignUncertainty


lemma exists_unique_root {h h' : ℝ → ℝ} {w0 m ε : ℝ} (hm : 0 < m) (hε0 : 0 ≤ ε) (hεm : ε < m * w0)
    (hd : ∀ t ∈ Ioo (-w0) w0, HasDerivAt h (h' t) t) (hge : ∀ t ∈ Ioo (-w0) w0, m ≤ h' t)
    (h0 : |h 0| ≤ ε) :
    ∃ t ∈ Ioo (-w0) w0, h t = 0 ∧ |t| ≤ ε / m ∧ ∀ s ∈ Ioo (-w0) w0, h s = 0 → s = t := by
  have hw0 : 0 < w0 := by
    by_contra hc
    rw [not_lt] at hc
    nlinarith
  have hmono : ∀ x ∈ Ioo (-w0) w0, ∀ y ∈ Ioo (-w0) w0, x ≤ y → m * (y - x) ≤ h y - h x := by
    have hcont : ContinuousOn h (Ioo (-w0) w0) := fun t ht => (hd t ht).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ h (interior (Ioo (-w0) w0)) := by
      rw [interior_Ioo]; exact fun t ht => (hd t ht).differentiableAt.differentiableWithinAt
    refine Convex.mul_sub_le_image_sub_of_le_deriv (convex_Ioo _ _) hcont hdiff ?_
    intro x hx
    rw [interior_Ioo] at hx
    rw [(hd x hx).deriv]; exact hge x hx
  have ht : ε / m < w0 := by rw [div_lt_iff₀ hm]; linarith
  have ht0 : 0 ≤ ε / m := div_nonneg hε0 hm.le
  have hin : ∀ t ∈ Icc (-(ε / m)) (ε / m), t ∈ Ioo (-w0) w0 := fun t htt =>
    ⟨by linarith [htt.1], by linarith [htt.2]⟩
  have h1 : 0 ≤ h (ε / m) := by
    have := hmono 0 ⟨by linarith, hw0⟩ (ε / m) (hin _ ⟨by linarith, le_rfl⟩) ht0
    have e : m * (ε / m - 0) = ε := by field_simp; ring
    have := (abs_le.mp h0).1
    linarith
  have h2 : h (-(ε / m)) ≤ 0 := by
    have := hmono (-(ε / m)) (hin _ ⟨le_rfl, by linarith⟩) 0 ⟨by linarith, hw0⟩ (by linarith)
    have e : m * (0 - -(ε / m)) = ε := by field_simp; ring
    have := (abs_le.mp h0).2
    linarith
  have hc : ContinuousOn h (Icc (-(ε / m)) (ε / m)) := fun t htt =>
    (hd t (hin t htt)).continuousAt.continuousWithinAt
  obtain ⟨t, htI, hth⟩ := intermediate_value_Icc (by linarith) hc ⟨h2, h1⟩
  have huniq : ∀ s ∈ Ioo (-w0) w0, h s = 0 → s = t := by
    intro s hs hsz
    have ht' := hin t htI
    rcases lt_trichotomy s t with hl | he | hg
    · have := hmono s hs t ht' hl.le
      nlinarith
    · exact he
    · have := hmono t ht' s hs hg.le
      nlinarith
  exact ⟨t, hin t htI, hth, abs_le.mpr ⟨by linarith [htI.1], htI.2⟩, huniq⟩

section ClaimG

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- `∂_t(E₀(y) + t F(y,t))` as a function of `(y,t)`. -/
noncomputable def aF (F : Y × ℝ → ℝ) (p : Y × ℝ) : ℝ := F p + p.2 * fderiv ℝ F p (0, 1)

lemma hasDerivAt_line {F : Y × ℝ → ℝ} {y : Y} {t : ℝ} (hF : DifferentiableAt ℝ F (y, t)) :
    HasDerivAt (fun s => F (y, s)) (fderiv ℝ F (y, t) (0, 1)) t := by
  have h1 : HasDerivAt (fun s : ℝ => (y, s)) ((0 : Y), (1 : ℝ)) t :=
    (hasDerivAt_const t y).prodMk (hasDerivAt_id t)
  exact hF.hasFDerivAt.comp_hasDerivAt t h1

lemma hasDerivAt_E_line {E0 : Y → ℝ} {F : Y × ℝ → ℝ} {y : Y} {t : ℝ} (hF : DifferentiableAt ℝ F (y, t)) :
    HasDerivAt (fun s => E0 y + s * F (y, s)) (aF F (y, t)) t := by
  have h2 := (hasDerivAt_id t).mul (hasDerivAt_line hF)
  have := h2.const_add (E0 y)
  simpa [aF] using this

lemma JB.apply_le {U : Set Y} {k : ℕ} {f : Y → ℝ} {b : ℝ} (h : JB k U f b) {y : Y} (hy : y ∈ U) : |f y| ≤ b := by
  have := h 0 (Nat.zero_le _) y hy
  simpa [iteratedFDerivWithin_zero_eq_comp] using this

lemma diffAt_of_mem {k : ℕ} {O : Set Y} (hO : IsOpen O) {w0 : ℝ} {F : Y × ℝ → ℝ}
    (hF : ContDiffOn ℝ k F (O ×ˢ Ioo (-w0) w0)) {y : Y} (hy : y ∈ O) {t : ℝ} (ht : t ∈ Ioo (-w0) w0) :
    ContDiffAt ℝ k F (y, t) :=
  hF.contDiffAt ((hO.prod isOpen_Ioo).mem_nhds ⟨hy, ht⟩)

lemma claimG_root {O : Set Y} {k : ℕ} (hk : 1 ≤ k) (hO : IsOpen O) {w0 m ε : ℝ} (hm : 0 < m) (hε0 : 0 ≤ ε)
    (hεm : ε < m * w0) {E0 : Y → ℝ} {F : Y × ℝ → ℝ} (hF : ContDiffOn ℝ k F (O ×ˢ Ioo (-w0) w0))
    (hE0 : ∀ y ∈ O, |E0 y| ≤ ε) (hdE : ∀ y ∈ O, ∀ t ∈ Ioo (-w0) w0, m ≤ aF F (y, t)) :
    ∀ y ∈ O, ∃ t ∈ Ioo (-w0) w0, E0 y + t * F (y, t) = 0 ∧ |t| ≤ ε / m ∧
      ∀ s ∈ Ioo (-w0) w0, E0 y + s * F (y, s) = 0 → s = t := by
  intro y hy
  have hk0 : (k : ℕ∞ω) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  refine exists_unique_root (h := fun s => E0 y + s * F (y, s)) (h' := fun t => aF F (y, t)) hm hε0 hεm
    (fun t ht => hasDerivAt_E_line ((diffAt_of_mem hO hF hy ht).differentiableAt hk0))
    (fun t ht => hdE y hy t ht) ?_
  simpa using hE0 y hy

lemma claimG_smooth [CompleteSpace Y] {O : Set Y} {k : ℕ} (hk : 1 ≤ k) (hO : IsOpen O) {w0 m : ℝ} (hm : 0 < m)
    {E0 : Y → ℝ} {F : Y × ℝ → ℝ} (hE0 : ContDiffOn ℝ k E0 O) (hF : ContDiffOn ℝ k F (O ×ˢ Ioo (-w0) w0))
    (hdE : ∀ y ∈ O, ∀ t ∈ Ioo (-w0) w0, m ≤ aF F (y, t)) {w : Y → ℝ}
    (hw : ∀ y ∈ O, w y ∈ Ioo (-w0) w0 ∧ E0 y + w y * F (y, w y) = 0 ∧
      ∀ s ∈ Ioo (-w0) w0, E0 y + s * F (y, s) = 0 → s = w y) :
    ContDiffOn ℝ k w O := by
  intro y0 hy0
  refine ContDiffAt.contDiffWithinAt ?_
  obtain ⟨ht0, hz0, -⟩ := hw y0 hy0
  set t0 := w y0 with ht0def
  set Ef : Y × ℝ → ℝ := fun p => E0 p.1 + p.2 * F p with hEf
  have hFat : ContDiffAt ℝ k F (y0, t0) := diffAt_of_mem hO hF hy0 ht0
  have cdf : ContDiffAt ℝ k Ef (y0, t0) := by
    have h1 : ContDiffAt ℝ k (fun p : Y × ℝ => E0 p.1) (y0, t0) :=
      (hE0.contDiffAt (hO.mem_nhds hy0)).comp (y0, t0) contDiffAt_fst
    exact h1.add (contDiffAt_snd.mul hFat)
  have hk0 : (k : ℕ∞ω) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hder : fderiv ℝ Ef (y0, t0) (0, 1) = aF F (y0, t0) := by
    have h1 : HasDerivAt (fun s : ℝ => (y0, s)) ((0 : Y), (1 : ℝ)) t0 :=
      (hasDerivAt_const t0 y0).prodMk (hasDerivAt_id t0)
    have h2 := (cdf.differentiableAt hk0).hasFDerivAt.comp_hasDerivAt t0 h1
    exact h2.unique (hasDerivAt_E_line (E0 := E0) (hFat.differentiableAt hk0))
  have hc : 0 < aF F (y0, t0) := lt_of_lt_of_le hm (hdE y0 hy0 t0 ht0)
  have hL : ∀ x : ℝ, (fderiv ℝ Ef (y0, t0) ∘L ContinuousLinearMap.inr ℝ Y ℝ) x = aF F (y0, t0) * x := by
    intro x
    have : ((0 : Y), x) = x • ((0 : Y), (1 : ℝ)) := by simp
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.inr_apply]
    rw [this, map_smul, hder, smul_eq_mul, mul_comm]
  have if₂ : (fderiv ℝ Ef (y0, t0) ∘L ContinuousLinearMap.inr ℝ Y ℝ).IsInvertible := by
    refine ContinuousLinearMap.IsInvertible.of_inverse (g := (aF F (y0, t0))⁻¹ • ContinuousLinearMap.id ℝ ℝ) ?_ ?_
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

lemma claimG_deriv {O : Set Y} {k : ℕ} (hk : 1 ≤ k) (hO : IsOpen O) {w0 m : ℝ} (hm : 0 < m)
    {E0 : Y → ℝ} {F : Y × ℝ → ℝ} (hE0 : ContDiffOn ℝ k E0 O) (hF : ContDiffOn ℝ k F (O ×ˢ Ioo (-w0) w0))
    (hdE : ∀ y ∈ O, ∀ t ∈ Ioo (-w0) w0, m ≤ aF F (y, t)) {w : Y → ℝ} (hwd : ContDiffOn ℝ k w O)
    (hw : ∀ y ∈ O, w y ∈ Ioo (-w0) w0 ∧ E0 y + w y * F (y, w y) = 0) {y : Y} (hy : y ∈ O) :
    fderiv ℝ w y = -(aF F (y, w y))⁻¹ •
      (fderiv ℝ E0 y + w y • (fderiv ℝ F (y, w y)).comp (ContinuousLinearMap.inl ℝ Y ℝ)) := by
  have hk0 : (k : ℕ∞ω) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hat := hdE y hy (w y) (hw y hy).1
  have hc : 0 < aF F (y, w y) := lt_of_lt_of_le hm hat
  have hE' : HasFDerivAt E0 (fderiv ℝ E0 y) y :=
    ((hE0.contDiffAt (hO.mem_nhds hy)).differentiableAt hk0).hasFDerivAt
  have hw' : HasFDerivAt w (fderiv ℝ w y) y :=
    ((hwd.contDiffAt (hO.mem_nhds hy)).differentiableAt hk0).hasFDerivAt
  have hΦ : HasFDerivAt (fun y => (y, w y)) ((ContinuousLinearMap.id ℝ Y).prod (fderiv ℝ w y)) y :=
    (hasFDerivAt_id y).prodMk hw'
  have hF1 : HasFDerivAt F (fderiv ℝ F (y, w y)) (y, w y) :=
    ((diffAt_of_mem hO hF hy (hw y hy).1).differentiableAt hk0).hasFDerivAt
  have hF' := hF1.comp y hΦ
  have hg := hE'.add (hw'.mul hF')
  have hz : HasFDerivAt (fun y => E0 y + w y * F (y, w y)) (0 : Y →L[ℝ] ℝ) y := by
    refine (hasFDerivAt_const (0 : ℝ) y).congr_of_eventuallyEq ?_
    filter_upwards [hO.mem_nhds hy] with z hz using (hw z hz).2
  have h0 := hg.unique hz
  ext v
  have h1 := congrArg (fun L : Y →L[ℝ] ℝ => L v) h0
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply, smul_eq_mul, zero_apply] at h1
  simp only [Function.comp_apply] at h1
  simp only [smul_apply, add_apply, ContinuousLinearMap.comp_apply, smul_eq_mul, neg_mul,
    ContinuousLinearMap.inl_apply]
  unfold aF at hc ⊢
  field_simp
  have h2 : fderiv ℝ F (y, w y) (v, fderiv ℝ w y v) =
      fderiv ℝ F (y, w y) (v, 0) + fderiv ℝ w y v * fderiv ℝ F (y, w y) (0, 1) := by
    have : (v, fderiv ℝ w y v) = (v, (0 : ℝ)) + fderiv ℝ w y v • ((0 : Y), (1 : ℝ)) := by
      ext <;> simp
    rw [this, map_add, map_smul, smul_eq_mul]
  rw [h2] at h1
  linear_combination h1

/-- Constant bounding `∂_t E` in `JB k'`. -/
noncomputable def claimGKa (k' : ℕ) (K : ℝ) : ℝ := K + 2 ^ k' * 1 * K

/-- Constant bounding `(∂_t E)⁻¹` in `JB k'`. -/
noncomputable def claimGKu (k' : ℕ) (m K : ℝ) : ℝ :=
  k'.factorial * (k'.factorial * (max 1 m⁻¹) ^ (k' + 1)) * (max 1 (claimGKa k' K)) ^ k'

lemma claimG_aux (k' : ℕ) {O : Set Y} (hO : IsOpen O) {w0 m K : ℝ} (hw1 : w0 ≤ 1) (hm : 0 < m) (hK : 0 ≤ K)
    {F : Y × ℝ → ℝ} (hF : ContDiffOn ℝ (k' + 1) F (O ×ˢ Ioo (-w0) w0))
    (hFb : JB (k' + 1) (O ×ˢ Ioo (-w0) w0) F K)
    (hdE : ∀ y ∈ O, ∀ t ∈ Ioo (-w0) w0, m ≤ aF F (y, t)) :
    ContDiffOn ℝ k' (fun p => (aF F p)⁻¹) (O ×ˢ Ioo (-w0) w0) ∧
    JB k' (O ×ˢ Ioo (-w0) w0) (fun p => (aF F p)⁻¹) (claimGKu k' m K) ∧
    ContDiffOn ℝ k' (fun p => (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ Y ℝ)) (O ×ˢ Ioo (-w0) w0) ∧
    JB k' (O ×ˢ Ioo (-w0) w0) (fun p => (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ Y ℝ)) K := by
  set U := O ×ˢ Ioo (-w0) w0 with hUdef
  have hU : IsOpen U := hO.prod isOpen_Ioo
  have hUd : UniqueDiffOn ℝ U := hU.uniqueDiffOn
  have hFd : ContDiffOn ℝ k' (fderiv ℝ F) U := hF.fderiv_of_isOpen hU (le_refl _)
  have hFdb : JB k' U (fderiv ℝ F) K :=
    (hFb.succ_fderivWithin hUd).congr fun p hp => fderivWithin_of_isOpen hU hp
  have hn : ‖((0 : Y), (1 : ℝ))‖ = 1 := by simp [Prod.norm_def]
  have hg : JB k' U (fun p => fderiv ℝ F p (0, 1)) (1 * K) := by
    have := JB.clm_apply_const hUd hFd ((0 : Y), (1 : ℝ)) hFdb
    rwa [hn] at this
  have hgc : ContDiffOn ℝ k' (fun p => fderiv ℝ F p (0, 1)) U := hFd.clm_apply contDiffOn_const
  have hs : JB k' U (fun p : Y × ℝ => p.2) 1 := JB.snd hUd fun p hp => (abs_lt.mpr ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩).le
  have hsc : ContDiffOn ℝ k' (fun p : Y × ℝ => p.2) U := contDiffOn_snd
  have hprod := JB.smul_mul hUd zero_le_one (mul_nonneg zero_le_one hK) hsc hgc hs hg
  have ha : JB k' U (aF F) (claimGKa k' K) := by
    have := JB.add hUd (hF.of_le (by exact_mod_cast Nat.le_succ k')) (hsc.mul hgc) (hFb.mono_order (Nat.le_succ k'))
      (by simpa [smul_eq_mul] using hprod : JB k' U (fun p : Y × ℝ => p.2 * fderiv ℝ F p (0, 1)) _)
    exact this.mono (le_of_eq (by unfold claimGKa; ring))
  have hac : ContDiffOn ℝ k' (aF F) U := (hF.of_le (by exact_mod_cast Nat.le_succ k')).add (hsc.mul hgc)
  have hmin : ∀ p ∈ U, m ≤ aF F p := fun p hp => hdE p.1 hp.1 p.2 hp.2
  have hinv := JB.inv hUd hm hac hmin ha
  have hGc : ContDiffOn ℝ k' (fun p => (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ Y ℝ)) U :=
    (ContinuousLinearMap.precomp ℝ (ContinuousLinearMap.inl ℝ Y ℝ) :
      ((Y × ℝ) →L[ℝ] ℝ) →L[ℝ] (Y →L[ℝ] ℝ)).contDiff.comp_contDiffOn hFd
  exact ⟨hac.inv fun p hp => (lt_of_lt_of_le hm (hmin p hp)).ne', hinv, hGc, JB.comp_inl hUd hK hFd hFdb⟩

/-- One step of the derivative-order induction: the constant for `JB (j+1) w` from the one for `JB j w`. -/
noncomputable def claimGStep (k' j : ℕ) (m K c : ℝ) : ℝ :=
  max (1 / m) (2 ^ j * (j.factorial * claimGKu k' m K * (max 1 (max 1 c)) ^ j) *
    (1 + 2 ^ j * c * (j.factorial * K * (max 1 (max 1 c)) ^ j)))

/-- The constants of the induction. -/
noncomputable def claimGSeq (k' : ℕ) (m K : ℝ) : ℕ → ℝ
  | 0 => 1 / m
  | j + 1 => claimGStep k' j m K (claimGSeq k' m K j)

lemma claimGSeq_nonneg (k' : ℕ) {m : ℝ} (K : ℝ) (hm : 0 < m) (j : ℕ) : 0 ≤ claimGSeq k' m K j := by
  cases j with
  | zero => simp [claimGSeq, hm.le]
  | succ j => exact (show (0:ℝ) ≤ 1 / m by positivity).trans (le_max_left _ _)

lemma claimG_step {k' j : ℕ} (hj : j ≤ k') {O : Set Y} (hO : IsOpen O) {w0 m K ε c : ℝ} (hw1 : w0 ≤ 1)
    (hm : 0 < m) (hK : 0 ≤ K) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hc : 0 ≤ c) {E0 : Y → ℝ} {F : Y × ℝ → ℝ} {w : Y → ℝ}
    (hE0 : ContDiffOn ℝ (k' + 1) E0 O) (hE0b : JB (k' + 1) O E0 ε)
    (hF : ContDiffOn ℝ (k' + 1) F (O ×ˢ Ioo (-w0) w0)) (hFb : JB (k' + 1) (O ×ˢ Ioo (-w0) w0) F K)
    (hdE : ∀ y ∈ O, ∀ t ∈ Ioo (-w0) w0, m ≤ aF F (y, t)) (hwd : ContDiffOn ℝ (k' + 1) w O)
    (hw : ∀ y ∈ O, w y ∈ Ioo (-w0) w0 ∧ E0 y + w y * F (y, w y) = 0) (hw0 : ∀ y ∈ O, |w y| ≤ ε / m)
    (ih : JB j O w (c * ε)) [CompleteSpace Y] :
    JB (j + 1) O w (claimGStep k' j m K c * ε) := by
  obtain ⟨huc, hub, hGc, hGb⟩ := claimG_aux k' hO hw1 hm hK hF hFb hdE
  set U := O ×ˢ Ioo (-w0) w0 with hUdef
  have hU : IsOpen U := hO.prod isOpen_Ioo
  have hUd : UniqueDiffOn ℝ U := hU.uniqueDiffOn
  have hOd : UniqueDiffOn ℝ O := hO.uniqueDiffOn
  have hk1 : (1 : ℕ) ≤ k' + 1 := by omega
  have hj' : (j : ℕ∞ω) ≤ ((k' + 1 : ℕ) : ℕ∞ω) := by exact_mod_cast (by omega : j ≤ k' + 1)
  have hjk : (j : ℕ∞ω) ≤ k' := by exact_mod_cast hj
  have hwj : ContDiffOn ℝ j w O := hwd.of_le (by exact_mod_cast (by omega : j ≤ k' + 1))
  have hΦc : ContDiffOn ℝ j (fun y => (y, w y)) O := contDiffOn_id.prodMk hwj
  have hΦU : MapsTo (fun y => (y, w y)) O U := fun y hy => ⟨hy, (hw y hy).1⟩
  have hΦb : ∀ i, 1 ≤ i → i ≤ j → ∀ y ∈ O, ‖iteratedFDerivWithin ℝ i (fun y => (y, w y)) O y‖ ≤ max 1 c := by
    intro i hi1 hij y hy
    refine (norm_iteratedFDerivWithin_graph_le hOd hwj (b := c * ε) (fun i _ hi y hy => ih i hi y hy) i hi1 hij y hy).trans
      (max_le_max le_rfl (mul_le_of_le_one_right hc hε1))
  have hKu0 : 0 ≤ claimGKu k' m K := by unfold claimGKu; positivity
  have huΦ := JB.comp hOd hUd (g := fun p => (aF F p)⁻¹) (huc.of_le hjk) hΦc hΦU hKu0
    (fun y hy i hi => hub i (hi.trans hj) _ (hΦU hy)) hΦb
  have hGΦ := JB.comp hOd hUd (g := fun p => (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ Y ℝ))
    (hGc.of_le hjk) hΦc hΦU hK (fun y hy i hi => hGb i (hi.trans hj) _ (hΦU hy)) hΦb
  have hCu0 : 0 ≤ (j.factorial : ℝ) * claimGKu k' m K * (max 1 (max 1 c)) ^ j := by
    have := hKu0; positivity
  have hCg0 : 0 ≤ (j.factorial : ℝ) * K * (max 1 (max 1 c)) ^ j := by positivity
  have hGΦc : ContDiffOn ℝ j ((fun p : Y × ℝ => (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ Y ℝ)) ∘
      fun y => (y, w y)) O := (hGc.of_le hjk).comp hΦc hΦU
  have huΦc : ContDiffOn ℝ j ((fun p : Y × ℝ => (aF F p)⁻¹) ∘ fun y => (y, w y)) O :=
    (huc.of_le hjk).comp hΦc hΦU
  have hcε : 0 ≤ c * ε := mul_nonneg hc hε0
  have hwG := JB.smul_mul hOd hcε hCg0 hwj hGΦc ih hGΦ
  have hwGc := hwj.smul hGΦc
  have hDE0c : ContDiffOn ℝ j (fun y => fderiv ℝ E0 y) O :=
    hE0.fderiv_of_isOpen hO (by exact_mod_cast (by omega : j + 1 ≤ k' + 1))
  have hDE0b : JB j O (fun y => fderiv ℝ E0 y) ε :=
    ((hE0b.mono_order (by omega : j + 1 ≤ k' + 1)).succ_fderivWithin hOd).congr fun y hy =>
      fderivWithin_of_isOpen hO hy
  have hsum := JB.add hOd hDE0c hwGc hDE0b hwG
  have hsumc := hDE0c.add hwGc
  have hbsum : 0 ≤ ε + 2 ^ j * (c * ε) * ((j.factorial : ℝ) * K * (max 1 (max 1 c)) ^ j) := by positivity
  have hprod := JB.smul_mul hOd hCu0 hbsum huΦc hsumc huΦ hsum
  have hneg := JB.neg hOd hprod
  have hk1' : ContDiffOn ℝ ((k' + 1 : ℕ) : ℕ∞ω) E0 O := by exact_mod_cast hE0
  have hF1' : ContDiffOn ℝ ((k' + 1 : ℕ) : ℕ∞ω) F U := by exact_mod_cast hF
  have hfin := hneg.congr (g := fderivWithin ℝ w O) fun y hy => by
    rw [fderivWithin_of_isOpen hO hy,
      claimG_deriv hk1 hO hm hk1' hF1' hdE (by exact_mod_cast hwd) hw hy]
    rw [neg_smul]
    rfl
  have hmain := JB.of_fderivWithin hOd (fun y hy => by simpa [Real.norm_eq_abs] using hw0 y hy) hfin
  refine hmain.mono (max_le ?_ ?_)
  · calc ε / m = 1 / m * ε := by ring
      _ ≤ claimGStep k' j m K c * ε := mul_le_mul_of_nonneg_right (le_max_left _ _) hε0
  · calc _ = (2 ^ j * ((j.factorial : ℝ) * claimGKu k' m K * (max 1 (max 1 c)) ^ j) *
          (1 + 2 ^ j * c * ((j.factorial : ℝ) * K * (max 1 (max 1 c)) ^ j))) * ε := by ring
      _ ≤ claimGStep k' j m K c * ε := mul_le_mul_of_nonneg_right (le_max_right _ _) hε0

/-- **Claim G** (`fct:comp-cfu`): quantitative `C^k` implicit-function bound for `E(y,t) = E₀(y) + t F(y,t)`.
On an open parameter set `O ⊂ Y`, with `‖E₀‖_{C^k} ≤ ε ≤ 1`, `‖F‖_{C^k} ≤ K`, `∂_tE = F + t ∂_tF ≥ m > 0` on
`O × (-w₀, w₀)`, `w₀ ≤ 1` and `ε < m w₀`, the equation `E = 0` has a unique root `w(y) ∈ (-w₀,w₀)`, `w ∈ C^k(O)` and
`‖w‖_{C^k} ≤ C(k,m,K) ε` (the constant is independent of `O`, `w₀`, `ε`, `E₀`, `F`).  The negative case
`∂_tE ≤ -m` is this statement applied to `-E₀, -F`.  Class: proved. -/
theorem claim_G [CompleteSpace Y] {k : ℕ} (hk : 1 ≤ k) {m K : ℝ} (hm : 0 < m) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {O : Set Y}, IsOpen O → ∀ {w0 ε : ℝ}, 0 < w0 → w0 ≤ 1 → 0 ≤ ε → ε ≤ 1 → ε < m * w0 →
    ∀ {E0 : Y → ℝ} {F : Y × ℝ → ℝ}, ContDiffOn ℝ k E0 O → JB k O E0 ε →
      ContDiffOn ℝ k F (O ×ˢ Ioo (-w0) w0) → JB k (O ×ˢ Ioo (-w0) w0) F K →
      (∀ y ∈ O, ∀ t ∈ Ioo (-w0) w0, m ≤ F (y, t) + t * fderiv ℝ F (y, t) (0, 1)) →
      ∃ w : Y → ℝ, ContDiffOn ℝ k w O ∧ JB k O w (C * ε) ∧
        ∀ y ∈ O, w y ∈ Ioo (-w0) w0 ∧ E0 y + w y * F (y, w y) = 0 ∧
          ∀ s ∈ Ioo (-w0) w0, E0 y + s * F (y, s) = 0 → s = w y := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  refine ⟨claimGSeq k' m K (k' + 1), claimGSeq_nonneg k' K hm _, ?_⟩
  intro O hO w0 ε hw0 hw1 hε0 hε1 hεm E0 F hE0 hE0b hF hFb hdE
  have hdE' : ∀ y ∈ O, ∀ t ∈ Ioo (-w0) w0, m ≤ aF F (y, t) := hdE
  have hF' : ContDiffOn ℝ (k' + 1) F (O ×ˢ Ioo (-w0) w0) := by exact_mod_cast hF
  have hE0' : ContDiffOn ℝ (k' + 1) E0 O := by exact_mod_cast hE0
  have hroot := claimG_root (by omega) hO hm hε0 hεm hF (fun y hy => hE0b.apply_le hy) hdE'
  have hex : ∀ y, ∃ t, y ∈ O → (t ∈ Ioo (-w0) w0 ∧ E0 y + t * F (y, t) = 0 ∧ |t| ≤ ε / m ∧
      ∀ s ∈ Ioo (-w0) w0, E0 y + s * F (y, s) = 0 → s = t) := by
    intro y
    by_cases hy : y ∈ O
    · obtain ⟨t, h1, h2, h3, h4⟩ := hroot y hy
      exact ⟨t, fun _ => ⟨h1, h2, h3, h4⟩⟩
    · exact ⟨0, fun h => absurd h hy⟩
  choose w hw using hex
  have hwspec : ∀ y ∈ O, w y ∈ Ioo (-w0) w0 ∧ E0 y + w y * F (y, w y) = 0 ∧
      ∀ s ∈ Ioo (-w0) w0, E0 y + s * F (y, s) = 0 → s = w y :=
    fun y hy => ⟨(hw y hy).1, (hw y hy).2.1, (hw y hy).2.2.2⟩
  have hwd : ContDiffOn ℝ (k' + 1 : ℕ) w O := claimG_smooth (by omega) hO hm hE0 hF hdE' hwspec
  have hwd' : ContDiffOn ℝ (k' + 1) w O := by exact_mod_cast hwd
  have hw0 : ∀ y ∈ O, |w y| ≤ ε / m := fun y hy => (hw y hy).2.2.1
  have key : ∀ j, j ≤ k' + 1 → JB j O w (claimGSeq k' m K j * ε) := by
    intro j
    induction j with
    | zero =>
      intro _ i hi y hy
      have hi0 : i = 0 := by omega
      subst hi0
      have : ‖iteratedFDerivWithin ℝ 0 w O y‖ = |w y| := by simp [iteratedFDerivWithin_zero_eq_comp]
      rw [this]
      calc |w y| ≤ ε / m := hw0 y hy
        _ = claimGSeq k' m K 0 * ε := by simp [claimGSeq]; ring
    | succ j ih =>
      intro hj
      exact claimG_step (by omega) hO hw1 hm hK hε0 hε1 (claimGSeq_nonneg k' K hm j) hE0' hE0b hF' hFb hdE' hwd'
        (fun y hy => ⟨(hw y hy).1, (hw y hy).2.1⟩) hw0 (ih (by omega))
  exact ⟨w, hwd, key (k' + 1) le_rfl, hwspec⟩

end ClaimG

/-- info: 'FormalResearch.SignUncertainty.exists_unique_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_unique_root

/-- info: 'FormalResearch.SignUncertainty.claimG_smooth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms claimG_smooth

/-- info: 'FormalResearch.SignUncertainty.claimG_deriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms claimG_deriv

/-- info: 'FormalResearch.SignUncertainty.claimG_aux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms claimG_aux

/-- info: 'FormalResearch.SignUncertainty.claimG_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms claimG_step

/-- info: 'FormalResearch.SignUncertainty.claim_G' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms claim_G

end FormalResearch.SignUncertainty
