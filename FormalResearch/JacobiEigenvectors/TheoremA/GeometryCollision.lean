module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.GeometryStatements

/-!
# Paper J, Layer 2 (L2.G4 (b)): the collision energies, lem:tha-geom (b)

Proves `GeomCollision` of `TheoremA/GeometryStatements.lean` (frozen; not edited).  The left-end statement is proved
once for a principal pair `(G, B)` indexed by a compact `K` (`left_concl_of_data`), and applied to `F` and to
`mirrorFamily F`, whose principal symbols are `s |-> G(L - s)`.  Only `G_0 >= g_* > 0`, `C^1` regularity on `[0, L]` and
joint continuity of the symbols and their first derivatives on `K x [0, L]` are used.

Fixed `mu`, put `E = E_0`, `F_m = 2 sqrt E + (B - B(0))`, `H_m = 2 sqrt E - (B - B(0))`.  For `X = B(0) + delta`,
`T(.;X) = (F_m - delta)(H_m + delta)` on `[0, L]`.  Near `0`, `F_m` and `H_m` are strictly increasing, because
`E' >= c_1 > 0` while `sqrt E` is small; so for `delta > 0` the only zero is the root of `F_m = delta`, and for
`delta < 0` the root of `H_m = -delta`.  All constants are uniform in `mu in K` by compactness.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA.Collision

open Set Filter Topology FormalResearch.JacobiEigenvectors.Setting

/-! ### Pointwise algebra at a collision energy -/

/-- `F_m = 2 sqrt(E_0) + (B - B(0))`. -/
def Fm (L : ℝ) (G B : ℝ → ℝ) (u : ℝ) : ℝ := 2 * Real.sqrt (E0 L G u) + (B u - B 0)

/-- `H_m = 2 sqrt(E_0) - (B - B(0))`. -/
def Hm (L : ℝ) (G B : ℝ → ℝ) (u : ℝ) : ℝ := 2 * Real.sqrt (E0 L G u) - (B u - B 0)

/-- The derivative of `E_0` written with `G` and `G'`. -/
def Dfn (L : ℝ) (G : ℝ → ℝ) (u : ℝ) : ℝ :=
  (L - 2 * u) * G u + u * (L - u) * derivWithin G (Icc 0 L) u

lemma E0_nonneg' {L : ℝ} {G : ℝ → ℝ} {u : ℝ} (hu : u ∈ Icc 0 L) (hG : 0 ≤ G u) : 0 ≤ E0 L G u := by
  unfold E0
  exact mul_nonneg (mul_nonneg hu.1 (by linarith [hu.2])) hG

lemma tfun_factor {L : ℝ} {G B : ℝ → ℝ} {u : ℝ} (hu : u ∈ Icc 0 L) (hG : 0 ≤ G u) (δ : ℝ) :
    Tfun L G B (B 0 + δ) u = (Fm L G B u - δ) * (Hm L G B u + δ) := by
  have hs : Real.sqrt (E0 L G u) ^ 2 = E0 L G u := Real.sq_sqrt (E0_nonneg' hu hG)
  unfold Tfun Fm Hm
  linear_combination (-4 : ℝ) * hs

lemma Fm_zero (L : ℝ) (G B : ℝ → ℝ) : Fm L G B 0 = 0 := by
  unfold Fm E0; simp

lemma Hm_zero (L : ℝ) (G B : ℝ → ℝ) : Hm L G B 0 = 0 := by
  unfold Hm E0; simp

lemma continuousOn_E0 {L : ℝ} {G : ℝ → ℝ} (hG : ContinuousOn G (Icc 0 L)) :
    ContinuousOn (fun u => E0 L G u) (Icc 0 L) := by
  unfold E0
  exact (continuousOn_id.mul (continuousOn_const.sub continuousOn_id)).mul hG

lemma continuousOn_Fm {L : ℝ} {G B : ℝ → ℝ} (hG : ContinuousOn G (Icc 0 L)) (hB : ContinuousOn B (Icc 0 L)) :
    ContinuousOn (Fm L G B) (Icc 0 L) := by
  unfold Fm
  exact (continuousOn_const.mul (continuousOn_E0 hG).sqrt).add (hB.sub continuousOn_const)

lemma continuousOn_Hm {L : ℝ} {G B : ℝ → ℝ} (hG : ContinuousOn G (Icc 0 L)) (hB : ContinuousOn B (Icc 0 L)) :
    ContinuousOn (Hm L G B) (Icc 0 L) := by
  unfold Hm
  exact (continuousOn_const.mul (continuousOn_E0 hG).sqrt).sub (hB.sub continuousOn_const)

/-! ### Derivatives at interior points -/

lemma hasDerivAt_E0' {L : ℝ} {G : ℝ → ℝ} {x : ℝ} (hG : DifferentiableAt ℝ G x) :
    HasDerivAt (fun u => E0 L G u) ((L - 2 * x) * G x + x * (L - x) * deriv G x) x := by
  have hsub : HasDerivAt (fun u : ℝ => L - u) (0 - 1) x := (hasDerivAt_const x L).sub (hasDerivAt_id' x)
  have h1 : HasDerivAt (fun u : ℝ => u * (L - u)) (1 * (L - x) + x * (0 - 1)) x :=
    (hasDerivAt_id' x).mul hsub
  have h2 := h1.mul hG.hasDerivAt
  unfold E0
  convert h2 using 1
  ring

lemma hasDerivAt_Fm {L : ℝ} {G B : ℝ → ℝ} {x : ℝ} (hx : x ∈ Ioo 0 L) (hGpos : 0 < G x)
    (hG : DifferentiableAt ℝ G x) (hB : DifferentiableAt ℝ B x) :
    HasDerivAt (Fm L G B)
      (((L - 2 * x) * G x + x * (L - x) * deriv G x) / Real.sqrt (E0 L G x) + deriv B x) x := by
  have hE : 0 < E0 L G x := by
    unfold E0; exact mul_pos (mul_pos hx.1 (by linarith [hx.2])) hGpos
  have h := (((hasDerivAt_E0' hG).sqrt hE.ne').const_mul 2).add (hB.hasDerivAt.sub_const (B 0))
  unfold Fm
  convert h using 1
  ring

lemma hasDerivAt_Hm {L : ℝ} {G B : ℝ → ℝ} {x : ℝ} (hx : x ∈ Ioo 0 L) (hGpos : 0 < G x)
    (hG : DifferentiableAt ℝ G x) (hB : DifferentiableAt ℝ B x) :
    HasDerivAt (Hm L G B)
      (((L - 2 * x) * G x + x * (L - x) * deriv G x) / Real.sqrt (E0 L G x) - deriv B x) x := by
  have hE : 0 < E0 L G x := by
    unfold E0; exact mul_pos (mul_pos hx.1 (by linarith [hx.2])) hGpos
  have h := (((hasDerivAt_E0' hG).sqrt hE.ne').const_mul 2).sub (hB.hasDerivAt.sub_const (B 0))
  unfold Hm
  convert h using 1
  ring

/-! ### Monotonicity of `F_m` and `H_m` near `0` -/

lemma strictMonoOn_Fm_Hm {L g Mg Mb c1 U0 : ℝ} {G B : ℝ → ℝ} (hg : 0 < g) (hUL : U0 < L) (hU0 : 0 < U0)
    (hG : ∀ u ∈ Icc 0 L, g ≤ G u) (hGub : ∀ u ∈ Icc 0 L, G u ≤ Mg)
    (hGd : DifferentiableOn ℝ G (Icc 0 L)) (hBd : DifferentiableOn ℝ B (Icc 0 L))
    (hBb : ∀ u ∈ Icc 0 L, |derivWithin B (Icc 0 L) u| ≤ Mb) (hMb : 0 ≤ Mb)
    (hD : ∀ u ∈ Ioo 0 U0, c1 ≤ (L - 2 * u) * G u + u * (L - u) * derivWithin G (Icc 0 L) u)
    (hc : 0 < c1) (hsmall : (Mb + 1) ^ 2 * (L * Mg * U0) < c1 ^ 2) :
    StrictMonoOn (Fm L G B) (Icc 0 U0) ∧ StrictMonoOn (Hm L G B) (Icc 0 U0) := by
  have hL : 0 < L := lt_trans hU0 hUL
  have hxL : ∀ x ∈ Ioo 0 U0, x ∈ Icc 0 L := fun x hx => ⟨hx.1.le, (hx.2.trans hUL).le⟩
  have hGpos : ∀ x ∈ Ioo 0 U0, 0 < G x := fun x hx => lt_of_lt_of_le hg (hG x (hxL x hx))
  have hdiff : ∀ x ∈ Ioo 0 L, DifferentiableAt ℝ G x := fun x hx =>
    hGd.differentiableAt (Icc_mem_nhds hx.1 hx.2)
  have hdiffB : ∀ x ∈ Ioo 0 L, DifferentiableAt ℝ B x := fun x hx =>
    hBd.differentiableAt (Icc_mem_nhds hx.1 hx.2)
  have hdG : ∀ x ∈ Ioo 0 L, deriv G x = derivWithin G (Icc 0 L) x := fun x hx =>
    (derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)).symm
  have hdB : ∀ x ∈ Ioo 0 L, deriv B x = derivWithin B (Icc 0 L) x := fun x hx =>
    (derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)).symm
  have hEpos : ∀ x ∈ Ioo 0 U0, 0 < E0 L G x := by
    intro x hx
    unfold E0
    exact mul_pos (mul_pos hx.1 (by linarith [hx.2, hUL])) (hGpos x hx)
  -- the square-root estimate: `(Mb + 1) sqrt E < c1` on `(0, U0)`
  have hsq : ∀ x ∈ Ioo 0 U0, (Mb + 1) * Real.sqrt (E0 L G x) < c1 := by
    intro x hx
    have hx0 : 0 < x := hx.1
    have hG0 : 0 ≤ G x := (hGpos x hx).le
    have hA : E0 L G x ≤ L * Mg * U0 := by
      show x * (L - x) * G x ≤ L * Mg * U0
      have h1 : x * (L - x) ≤ L * x := by nlinarith
      have h2 : x * (L - x) * G x ≤ L * x * G x := mul_le_mul_of_nonneg_right h1 hG0
      have h3 : L * x * G x ≤ L * x * Mg :=
        mul_le_mul_of_nonneg_left (hGub x (hxL x hx)) (mul_pos hL hx0).le
      have hMg0 : 0 ≤ Mg := le_trans hG0 (hGub x (hxL x hx))
      have h4 : L * x * Mg ≤ L * Mg * U0 := by
        have := mul_le_mul_of_nonneg_left hx.2.le (mul_nonneg hL.le hMg0)
        linarith [show L * x * Mg = L * Mg * x by ring]
      linarith
    have hs2 : Real.sqrt (E0 L G x) ^ 2 = E0 L G x := Real.sq_sqrt (hEpos x hx).le
    have hs0 : 0 ≤ Real.sqrt (E0 L G x) := Real.sqrt_nonneg _
    have hsq2 : ((Mb + 1) * Real.sqrt (E0 L G x)) ^ 2 < c1 ^ 2 := by
      have e : ((Mb + 1) * Real.sqrt (E0 L G x)) ^ 2 = (Mb + 1) ^ 2 * E0 L G x := by
        rw [mul_pow, hs2]
      have h5 : (Mb + 1) ^ 2 * E0 L G x ≤ (Mb + 1) ^ 2 * (L * Mg * U0) :=
        mul_le_mul_of_nonneg_left hA (sq_nonneg _)
      rw [e]
      linarith
    have hnn : 0 ≤ (Mb + 1) * Real.sqrt (E0 L G x) := mul_nonneg (by linarith) hs0
    nlinarith
  -- the derivative of `F_m` and `H_m` is positive on `(0, U0)`
  have hkey : ∀ x ∈ Ioo 0 U0, Mb + 1 < ((L - 2 * x) * G x + x * (L - x) * derivWithin G (Icc 0 L) x) /
      Real.sqrt (E0 L G x) := by
    intro x hx
    have hs : 0 < Real.sqrt (E0 L G x) := Real.sqrt_pos.2 (hEpos x hx)
    rw [lt_div_iff₀ hs]
    have h1 := hD x hx
    have h2 := hsq x hx
    linarith
  have hderF : ∀ x ∈ Ioo 0 U0, 0 < deriv (Fm L G B) x ∧ 0 < deriv (Hm L G B) x := by
    intro x hx
    have hx' : x ∈ Ioo 0 L := ⟨hx.1, hx.2.trans hUL⟩
    have hF := hasDerivAt_Fm hx' (hGpos x hx) (hdiff x hx') (hdiffB x hx')
    have hH := hasDerivAt_Hm hx' (hGpos x hx) (hdiff x hx') (hdiffB x hx')
    rw [hF.deriv, hH.deriv, hdG x hx', hdB x hx']
    have k := hkey x hx
    have hb := abs_le.1 (hBb x (hxL x hx))
    constructor <;> linarith [hb.1, hb.2]
  have hcontF : ContinuousOn (Fm L G B) (Icc 0 U0) :=
    (continuousOn_Fm hGd.continuousOn hBd.continuousOn).mono (Icc_subset_Icc le_rfl hUL.le)
  have hcontH : ContinuousOn (Hm L G B) (Icc 0 U0) :=
    (continuousOn_Hm hGd.continuousOn hBd.continuousOn).mono (Icc_subset_Icc le_rfl hUL.le)
  refine ⟨strictMonoOn_of_deriv_pos (convex_Icc 0 U0) hcontF ?_,
    strictMonoOn_of_deriv_pos (convex_Icc 0 U0) hcontH ?_⟩
  · intro x hx
    rw [interior_Icc] at hx
    exact (hderF x hx).1
  · intro x hx
    rw [interior_Icc] at hx
    exact (hderF x hx).2

/-! ### Principal pairs over a compact set -/

section Uniform

variable {Par : Type*} [TopologicalSpace Par]

/-- What the collision analysis uses about a pair `(G, B)` of principal symbols indexed by `K`. -/
structure CollData (L g : ℝ) (K : Set Par) (G B : Par → ℝ → ℝ) : Prop where
  lb : ∀ μ ∈ K, ∀ u ∈ Icc 0 L, g ≤ G μ u
  diffG : ∀ μ ∈ K, DifferentiableOn ℝ (G μ) (Icc 0 L)
  diffB : ∀ μ ∈ K, DifferentiableOn ℝ (B μ) (Icc 0 L)
  contG : ContinuousOn (fun p : Par × ℝ => G p.1 p.2) (K ×ˢ Icc 0 L)
  contB : ContinuousOn (fun p : Par × ℝ => B p.1 p.2) (K ×ˢ Icc 0 L)
  derG : ContinuousOn (fun p : Par × ℝ => derivWithin (G p.1) (Icc 0 L) p.2) (K ×ˢ Icc 0 L)
  derB : ContinuousOn (fun p : Par × ℝ => derivWithin (B p.1) (Icc 0 L) p.2) (K ×ˢ Icc 0 L)

lemma collData_empty {L g : ℝ} {K : Set Par} (hK : K = ∅) (G B : Par → ℝ → ℝ) : CollData L g K G B := by
  subst hK
  exact ⟨fun μ hμ => by simp at hμ, fun μ hμ => by simp at hμ, fun μ hμ => by simp at hμ,
    by simp, by simp, by simp, by simp⟩

/-- The derivative of `G(L - .)` is `-G'(L - .)`. -/
lemma derivWithin_mirror {L : ℝ} {G : ℝ → ℝ} (hL : 0 < L) (hGd : DifferentiableOn ℝ G (Icc 0 L)) {u : ℝ}
    (hu : u ∈ Icc 0 L) :
    derivWithin (fun v => G (L - v)) (Icc 0 L) u = -derivWithin G (Icc 0 L) (L - u) := by
  have hmem : L - u ∈ Icc 0 L := ⟨by linarith [hu.2], by linarith [hu.1]⟩
  have hG' : HasDerivWithinAt G (derivWithin G (Icc 0 L) (L - u)) (Icc 0 L) (L - u) :=
    (hGd (L - u) hmem).hasDerivWithinAt
  have hlin : HasDerivWithinAt (fun v : ℝ => L - v) (-1) (Icc 0 L) u :=
    ((hasDerivAt_id' u).const_sub L).hasDerivWithinAt
  have hc := hG'.comp u hlin
    (fun v hv => show L - v ∈ Icc 0 L from ⟨by linarith [hv.2], by linarith [hv.1]⟩)
  have h : derivWithin (fun v => G (L - v)) (Icc 0 L) u = derivWithin G (Icc 0 L) (L - u) * (-1) :=
    hc.derivWithin ((uniqueDiffOn_Icc hL) u hu)
  rw [h]
  ring

lemma collData_mirror {L g : ℝ} {K : Set Par} {G B : Par → ℝ → ℝ} (hL : 0 < L) (hd : CollData L g K G B) :
    CollData L g K (fun μ u => G μ (L - u)) (fun μ u => B μ (L - u)) := by
  have hmap : ∀ u ∈ Icc (0 : ℝ) L, L - u ∈ Icc (0 : ℝ) L := fun u hu =>
    ⟨by linarith [hu.2], by linarith [hu.1]⟩
  have haff : DifferentiableOn ℝ (fun u : ℝ => L - u) (Icc 0 L) :=
    (differentiableOn_const L).sub differentiableOn_id
  have hcontMap : ContinuousOn (fun p : Par × ℝ => (p.1, L - p.2)) (K ×ˢ Icc 0 L) :=
    (Continuous.prodMk continuous_fst (continuous_const.sub continuous_snd)).continuousOn
  have hmapK : MapsTo (fun p : Par × ℝ => (p.1, L - p.2)) (K ×ˢ Icc 0 L) (K ×ˢ Icc 0 L) :=
    fun p hp => ⟨hp.1, hmap p.2 hp.2⟩
  refine ⟨fun μ hμ u hu => hd.lb μ hμ (L - u) (hmap u hu),
    fun μ hμ => (hd.diffG μ hμ).comp haff (fun u hu => hmap u hu),
    fun μ hμ => (hd.diffB μ hμ).comp haff (fun u hu => hmap u hu), ?_, ?_, ?_, ?_⟩
  · exact hd.contG.comp hcontMap hmapK
  · exact hd.contB.comp hcontMap hmapK
  · have hc : ContinuousOn (fun p : Par × ℝ => -derivWithin (G p.1) (Icc 0 L) (L - p.2)) (K ×ˢ Icc 0 L) :=
      (hd.derG.comp hcontMap hmapK).neg
    refine hc.congr (fun p hp => ?_)
    exact derivWithin_mirror hL (hd.diffG p.1 hp.1) hp.2
  · have hc : ContinuousOn (fun p : Par × ℝ => -derivWithin (B p.1) (Icc 0 L) (L - p.2)) (K ×ˢ Icc 0 L) :=
      (hd.derB.comp hcontMap hmapK).neg
    refine hc.congr (fun p hp => ?_)
    exact derivWithin_mirror hL (hd.diffB p.1 hp.1) hp.2

/-! ### The left-end statement -/

theorem left_concl_of_data {L g : ℝ} {K : Set Par} {G B : Par → ℝ → ℝ} (hL : 0 < L) (hg : 0 < g)
    (hK : IsCompact K) (hd : CollData L g K G B) :
    ∃ U0 δ1 pmin : ℝ, 0 < U0 ∧ U0 < L ∧ 0 < δ1 ∧ 0 < pmin ∧ ∀ μ ∈ K,
      (∀ u ∈ Icc 0 U0, pmin ≤ Real.sqrt ((L - u) * G μ u)) ∧
      Tfun L (G μ) (B μ) (B μ 0) 0 = 0 ∧
      derivWithin (Tfun L (G μ) (B μ) (B μ 0)) (Icc 0 L) 0 = 4 * L * G μ 0 ∧
      0 < 4 * L * G μ 0 ∧
      (∀ u ∈ Ioc 0 U0, 0 < Tfun L (G μ) (B μ) (B μ 0) u) ∧
      ∀ X : ℝ, X ≠ B μ 0 → |X - B μ 0| ≤ δ1 →
        ∃ us ∈ Ioo 0 U0, Tfun L (G μ) (B μ) X us = 0 ∧
          (∀ u ∈ Ico 0 us, Tfun L (G μ) (B μ) X u < 0) ∧
          (∀ u ∈ Ioc us U0, 0 < Tfun L (G μ) (B μ) X u) := by
  rcases K.eq_empty_or_nonempty with hKe | hne
  · refine ⟨L / 2, 1, 1, by linarith, by linarith, one_pos, one_pos, fun μ hμ => ?_⟩
    rw [hKe] at hμ
    simp at hμ
  -- uniform bounds on `G` and `B'` over `K x [0, L]`
  have hKI : IsCompact (K ×ˢ Icc (0 : ℝ) L) := hK.prod isCompact_Icc
  obtain ⟨C1, hC1⟩ := hKI.exists_bound_of_continuousOn hd.contG
  obtain ⟨C2, hC2⟩ := hKI.exists_bound_of_continuousOn hd.derB
  obtain ⟨Mg, hMgdef⟩ : ∃ M : ℝ, M = |C1| + g := ⟨_, rfl⟩
  obtain ⟨Mb, hMbdef⟩ : ∃ M : ℝ, M = |C2| := ⟨_, rfl⟩
  have hMgpos : 0 < Mg := by rw [hMgdef]; linarith [abs_nonneg C1]
  have hMbnn : 0 ≤ Mb := by rw [hMbdef]; exact abs_nonneg C2
  have hGubM : ∀ μ ∈ K, ∀ u ∈ Icc 0 L, G μ u ≤ Mg := by
    intro μ hμ u hu
    have h := hC1 (μ, u) ⟨hμ, hu⟩
    have h' : |G μ u| ≤ C1 := by simpa [Real.norm_eq_abs] using h
    rw [hMgdef]
    linarith [le_abs_self (G μ u), le_abs_self C1]
  have hBbM : ∀ μ ∈ K, ∀ u ∈ Icc 0 L, |derivWithin (B μ) (Icc 0 L) u| ≤ Mb := by
    intro μ hμ u hu
    have h := hC2 (μ, u) ⟨hμ, hu⟩
    have h' : |derivWithin (B μ) (Icc 0 L) u| ≤ C2 := by simpa [Real.norm_eq_abs] using h
    rw [hMbdef]
    exact h'.trans (le_abs_self C2)
  -- uniform lower bound for `E_0'` near `0` (tube lemma over `K`)
  obtain ⟨c1, hc1⟩ : ∃ c : ℝ, c = L * g / 2 := ⟨_, rfl⟩
  have hc1pos : 0 < c1 := by rw [hc1]; exact div_pos (mul_pos hL hg) two_pos
  have hDc : ContinuousOn (fun p : Par × ℝ => Dfn L (G p.1) p.2) (K ×ˢ Icc 0 L) := by
    unfold Dfn
    apply ContinuousOn.add
    · exact ((continuous_const.sub (continuous_const.mul continuous_snd)).continuousOn).mul hd.contG
    · exact ((continuous_snd.mul (continuous_const.sub continuous_snd)).continuousOn).mul hd.derG
  have hloc : ∀ μ ∈ K, ∀ᶠ z in 𝓝 ((0 : ℝ), μ),
      (z.2 ∈ K → z.1 ∈ Icc 0 L → c1 < Dfn L (G z.2) z.1) := by
    intro μ hμ
    have hsw : ContinuousOn (fun z : ℝ × Par => Dfn L (G z.2) z.1) (Icc 0 L ×ˢ K) :=
      hDc.comp (continuous_snd.prodMk continuous_fst).continuousOn (fun z hz => ⟨hz.2, hz.1⟩)
    have hmem : ((0 : ℝ), μ) ∈ Icc 0 L ×ˢ K := ⟨⟨le_rfl, hL.le⟩, hμ⟩
    have hlt : c1 < Dfn L (G μ) 0 := by
      have e : Dfn L (G μ) 0 = L * G μ 0 := by unfold Dfn; ring
      rw [e, hc1]
      nlinarith [hd.lb μ hμ 0 ⟨le_rfl, hL.le⟩]
    have hT : ∀ᶠ z in 𝓝[Icc 0 L ×ˢ K] ((0 : ℝ), μ), c1 < Dfn L (G z.2) z.1 :=
      Filter.Tendsto.eventually (hsw.continuousWithinAt hmem) (lt_mem_nhds hlt)
    filter_upwards [eventually_nhdsWithin_iff.1 hT] with z hz h2 h1
    exact hz ⟨h1, h2⟩
  have htube : ∀ᶠ u in 𝓝 (0 : ℝ), ∀ μ ∈ K, μ ∈ K → u ∈ Icc 0 L → c1 < Dfn L (G μ) u := by
    refine hK.eventually_forall_of_forall_eventually
      (P := fun u μ => μ ∈ K → u ∈ Icc 0 L → c1 < Dfn L (G μ) u) (fun μ hμ => ?_)
    filter_upwards [hloc μ hμ] with z hz
    exact hz
  obtain ⟨ρ, hρ, hρP⟩ := Metric.eventually_nhds_iff.1 htube
  have hρ' : ∀ μ ∈ K, ∀ u ∈ Icc 0 L, |u| < ρ → c1 < Dfn L (G μ) u := fun μ hμ u hu hab =>
    hρP (by rw [Real.dist_eq, sub_zero]; exact hab) μ hμ hμ hu
  -- the choice of `U_0`
  obtain ⟨Z, hZ⟩ : ∃ Z : ℝ, Z = (Mb + 1) ^ 2 * (L * Mg) + 1 := ⟨_, rfl⟩
  have hZpos : 0 < Z := by
    rw [hZ]
    have : 0 ≤ (Mb + 1) ^ 2 * (L * Mg) := mul_nonneg (sq_nonneg _) (mul_nonneg hL.le hMgpos.le)
    linarith
  obtain ⟨U0, hU0⟩ : ∃ U0 : ℝ, U0 = min (min (ρ / 2) (L / 2)) (c1 ^ 2 / Z) := ⟨_, rfl⟩
  have hU0pos : 0 < U0 := by
    rw [hU0]
    exact lt_min (lt_min (half_pos hρ) (half_pos hL)) (div_pos (pow_pos hc1pos 2) hZpos)
  have hU0ρ : U0 ≤ ρ / 2 := by
    rw [hU0]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hU0L : U0 ≤ L / 2 := by
    rw [hU0]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hU0Z : U0 * Z ≤ c1 ^ 2 := by
    have h : U0 ≤ c1 ^ 2 / Z := by rw [hU0]; exact min_le_right _ _
    exact (le_div_iff₀ hZpos).1 h
  have hsmall : (Mb + 1) ^ 2 * (L * Mg * U0) < c1 ^ 2 := by
    have e : (Mb + 1) ^ 2 * (L * Mg * U0) = U0 * Z - U0 := by rw [hZ]; ring
    linarith
  have hUL : U0 < L := by linarith
  -- monotonicity of `F_m`, `H_m` on `[0, U_0]`, for every `mu in K`
  have hmono : ∀ μ ∈ K, StrictMonoOn (Fm L (G μ) (B μ)) (Icc 0 U0) ∧
      StrictMonoOn (Hm L (G μ) (B μ)) (Icc 0 U0) := by
    intro μ hμ
    refine strictMonoOn_Fm_Hm hg hUL hU0pos (hd.lb μ hμ) (hGubM μ hμ) (hd.diffG μ hμ) (hd.diffB μ hμ)
      (hBbM μ hμ) hMbnn ?_ hc1pos hsmall
    intro u hu
    have hu' : u ∈ Icc 0 L := ⟨hu.1.le, hu.2.trans hUL |>.le⟩
    exact (hρ' μ hμ u hu' (by rw [abs_of_pos hu.1]; linarith [hu.2, hU0ρ])).le
  have hU0I : U0 ∈ Icc 0 L := ⟨hU0pos.le, hUL.le⟩
  have hU0I' : U0 ∈ Icc 0 U0 := ⟨hU0pos.le, le_rfl⟩
  have h0I' : (0 : ℝ) ∈ Icc 0 U0 := ⟨le_rfl, hU0pos.le⟩
  have hφpos : ∀ μ ∈ K, 0 < min (Fm L (G μ) (B μ) U0) (Hm L (G μ) (B μ) U0) := by
    intro μ hμ
    have h1 := (hmono μ hμ).1 h0I' hU0I' hU0pos
    have h2 := (hmono μ hμ).2 h0I' hU0I' hU0pos
    rw [Fm_zero] at h1
    rw [Hm_zero] at h2
    exact lt_min h1 h2
  -- continuity in `mu` of `F_m(U_0)`, `H_m(U_0)`
  have hf : Continuous (fun μ : Par => (μ, U0)) := continuous_id.prodMk continuous_const
  have hf0 : Continuous (fun μ : Par => (μ, (0 : ℝ))) := continuous_id.prodMk continuous_const
  have hGU : ContinuousOn (fun μ => G μ U0) K :=
    hd.contG.comp hf.continuousOn (fun μ hμ => ⟨hμ, hU0I⟩)
  have hBU : ContinuousOn (fun μ => B μ U0) K :=
    hd.contB.comp hf.continuousOn (fun μ hμ => ⟨hμ, hU0I⟩)
  have hB0 : ContinuousOn (fun μ => B μ 0) K :=
    hd.contB.comp hf0.continuousOn (fun μ hμ => ⟨hμ, ⟨le_rfl, hL.le⟩⟩)
  have hc2 : ContinuousOn (fun _ : Par => (2 : ℝ)) K := continuousOn_const
  have hE : ContinuousOn (fun μ => U0 * (L - U0) * G μ U0) K := continuousOn_const.mul hGU
  have hFc : ContinuousOn (fun μ => Fm L (G μ) (B μ) U0) K :=
    (hc2.mul hE.sqrt).add (hBU.sub hB0)
  have hHc : ContinuousOn (fun μ => Hm L (G μ) (B μ) U0) K :=
    (hc2.mul hE.sqrt).sub (hBU.sub hB0)
  obtain ⟨μ0, hμ0K, hμ0min⟩ := hK.exists_isMinOn hne (hFc.inf hHc)
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = min (Fm L (G μ0) (B μ0) U0) (Hm L (G μ0) (B μ0) U0) := ⟨_, rfl⟩
  have hmpos : 0 < m := by rw [hm]; exact hφpos μ0 hμ0K
  have hmle : ∀ μ ∈ K, m ≤ min (Fm L (G μ) (B μ) U0) (Hm L (G μ) (B μ) U0) := fun μ hμ => by
    rw [hm]; exact isMinOn_iff.1 hμ0min μ hμ
  have hmF : ∀ μ ∈ K, m ≤ Fm L (G μ) (B μ) U0 := fun μ hμ => le_trans (hmle μ hμ) (min_le_left _ _)
  have hmH : ∀ μ ∈ K, m ≤ Hm L (G μ) (B μ) U0 := fun μ hμ => le_trans (hmle μ hμ) (min_le_right _ _)
  refine ⟨U0, m / 2, Real.sqrt (L * g / 2), hU0pos, hUL, half_pos hmpos,
    Real.sqrt_pos.2 (div_pos (mul_pos hL hg) two_pos), fun μ hμ => ?_⟩
  have hGg : ∀ u ∈ Icc 0 L, g ≤ G μ u := hd.lb μ hμ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the lower bound of `P_0`
    intro u hu
    apply Real.sqrt_le_sqrt
    have h1 : L / 2 ≤ L - u := by linarith [hu.2, hU0L]
    have h2 := hGg u ⟨hu.1, by linarith [hu.2, hUL]⟩
    have h3 := mul_le_mul h1 h2 hg.le (by linarith [hu.2, hUL])
    linarith [show L * g / 2 = L / 2 * g by ring]
  · unfold Tfun E0
    simp
  · -- the one-sided derivative of `T` at the collision energy
    have hG0 : HasDerivWithinAt (G μ) (derivWithin (G μ) (Icc 0 L) 0) (Icc 0 L) 0 :=
      ((hd.diffG μ hμ) 0 ⟨le_rfl, hL.le⟩).hasDerivWithinAt
    have hB0' : HasDerivWithinAt (B μ) (derivWithin (B μ) (Icc 0 L) 0) (Icc 0 L) 0 :=
      ((hd.diffB μ hμ) 0 ⟨le_rfl, hL.le⟩).hasDerivWithinAt
    have hsub : HasDerivAt (fun u : ℝ => L - u) (0 - 1) 0 := (hasDerivAt_const 0 L).sub (hasDerivAt_id' 0)
    have hlin : HasDerivAt (fun u : ℝ => u * (L - u)) (1 * (L - 0) + 0 * (0 - 1)) 0 :=
      (hasDerivAt_id' 0).mul hsub
    have hE' : HasDerivWithinAt (fun u => E0 L (G μ) u)
        ((1 * (L - 0) + 0 * (0 - 1)) * G μ 0 + (0 * (L - 0)) * derivWithin (G μ) (Icc 0 L) 0)
        (Icc 0 L) 0 :=
      hlin.hasDerivWithinAt.mul hG0
    have hT : HasDerivWithinAt (Tfun L (G μ) (B μ) (B μ 0)) (4 * L * G μ 0) (Icc 0 L) 0 := by
      have h := (hE'.const_mul 4).sub ((hB0'.const_sub (B μ 0)).pow 2)
      have hfun : Tfun L (G μ) (B μ) (B μ 0) = fun u => 4 * E0 L (G μ) u - (B μ 0 - B μ u) ^ 2 := rfl
      rw [hfun]
      convert h using 1
      simp
      ring
    exact hT.derivWithin ((uniqueDiffOn_Icc hL) 0 ⟨le_rfl, hL.le⟩)
  · have := hGg 0 ⟨le_rfl, hL.le⟩
    exact mul_pos (by linarith) (lt_of_lt_of_le hg (hGg 0 ⟨le_rfl, hL.le⟩))
  · -- positivity of `T(.; B(0))` on `(0, U_0]`
    intro u hu
    have hu' : u ∈ Icc 0 L := ⟨hu.1.le, hu.2.trans hUL.le⟩
    have hu'' : u ∈ Icc 0 U0 := ⟨hu.1.le, hu.2⟩
    have hfac := tfun_factor (B := B μ) hu' (le_trans hg.le (hGg u hu')) 0
    simp only [add_zero, sub_zero] at hfac
    rw [hfac]
    have h1 := (hmono μ hμ).1 h0I' hu'' hu.1
    have h2 := (hmono μ hμ).2 h0I' hu'' hu.1
    rw [Fm_zero] at h1
    rw [Hm_zero] at h2
    exact mul_pos h1 h2
  · -- the root for `X != B(0)` with `|X - B(0)| <= delta_1`
    intro X hXne hXδ
    have hδ : |X - B μ 0| ≤ m / 2 := hXδ
    have key : ∀ u ∈ Icc 0 L, Tfun L (G μ) (B μ) X u =
        (Fm L (G μ) (B μ) u - (X - B μ 0)) * (Hm L (G μ) (B μ) u + (X - B μ 0)) := by
      intro u hu
      have h := tfun_factor (B := B μ) hu (le_trans hg.le (hGg u hu)) (X - B μ 0)
      rw [show B μ 0 + (X - B μ 0) = X by ring] at h
      exact h
    have hFc' : ContinuousOn (Fm L (G μ) (B μ)) (Icc 0 U0) :=
      (continuousOn_Fm (hd.diffG μ hμ).continuousOn (hd.diffB μ hμ).continuousOn).mono
        (Icc_subset_Icc le_rfl hUL.le)
    have hHc' : ContinuousOn (Hm L (G μ) (B μ)) (Icc 0 U0) :=
      (continuousOn_Hm (hd.diffG μ hμ).continuousOn (hd.diffB μ hμ).continuousOn).mono
        (Icc_subset_Icc le_rfl hUL.le)
    have hF0 : Fm L (G μ) (B μ) 0 = 0 := Fm_zero _ _ _
    have hH0 : Hm L (G μ) (B μ) 0 = 0 := Hm_zero _ _ _
    have hFU := hmF μ hμ
    have hHU := hmH μ hμ
    have hsub : Icc (0 : ℝ) U0 ⊆ Icc 0 L := Icc_subset_Icc le_rfl hUL.le
    rcases lt_trichotomy (X - B μ 0) 0 with hneg | hzero | hpos
    · -- `delta < 0`: the root of `H_m = -delta`
      have hδ' : -(X - B μ 0) ≤ m / 2 := by rw [abs_of_neg hneg] at hδ; exact hδ
      have hmem : -(X - B μ 0) ∈ Icc (Hm L (G μ) (B μ) 0) (Hm L (G μ) (B μ) U0) :=
        ⟨by rw [hH0]; linarith, by linarith⟩
      obtain ⟨us, hus, hHus⟩ := intermediate_value_Icc hU0pos.le hHc' hmem
      have hus0 : 0 < us := lt_of_le_of_ne hus.1 (fun h => by
        rw [← h, hH0] at hHus; linarith)
      have husU : us < U0 := lt_of_le_of_ne hus.2 (fun h => by
        rw [h] at hHus; linarith)
      have hsum : Hm L (G μ) (B μ) us + (X - B μ 0) = 0 := by rw [hHus]; ring
      refine ⟨us, ⟨hus0, husU⟩, ?_, ?_, ?_⟩
      · rw [key us (hsub hus), hsum, mul_zero]
      · intro u hu
        have huU : u ∈ Icc 0 U0 := ⟨hu.1, hu.2.le.trans husU.le⟩
        have huI : u ∈ Icc 0 L := ⟨huU.1, huU.2.trans hUL.le⟩
        have h1 : Hm L (G μ) (B μ) u < Hm L (G μ) (B μ) us := (hmono μ hμ).2 huU hus hu.2
        have h2 := (hmono μ hμ).1.monotoneOn h0I' huU hu.1
        rw [Fm_zero] at h2
        rw [key u huI]
        exact mul_neg_of_pos_of_neg (by linarith) (by linarith)
      · intro u hu
        have huU : u ∈ Icc 0 U0 := ⟨hus.1.trans hu.1.le, hu.2⟩
        have huI : u ∈ Icc 0 L := ⟨huU.1, huU.2.trans hUL.le⟩
        have h1 : Hm L (G μ) (B μ) us < Hm L (G μ) (B μ) u := (hmono μ hμ).2 hus huU hu.1
        have h2 := (hmono μ hμ).1.monotoneOn h0I' huU (hus.1.trans hu.1.le)
        rw [Fm_zero] at h2
        rw [key u huI]
        exact mul_pos (by linarith) (by linarith)
    · exact absurd (sub_eq_zero.1 hzero) hXne
    · -- `delta > 0`: the root of `F_m = delta`
      have hδ' : X - B μ 0 ≤ m / 2 := by rw [abs_of_pos hpos] at hδ; exact hδ
      have hmem : X - B μ 0 ∈ Icc (Fm L (G μ) (B μ) 0) (Fm L (G μ) (B μ) U0) :=
        ⟨by rw [hF0]; exact hpos.le, by linarith⟩
      obtain ⟨us, hus, hFus⟩ := intermediate_value_Icc hU0pos.le hFc' hmem
      have hus0 : 0 < us := lt_of_le_of_ne hus.1 (fun h => by
        rw [← h, hF0] at hFus; linarith)
      have husU : us < U0 := lt_of_le_of_ne hus.2 (fun h => by
        rw [h] at hFus; linarith)
      have hdiff0 : Fm L (G μ) (B μ) us - (X - B μ 0) = 0 := by rw [hFus]; ring
      refine ⟨us, ⟨hus0, husU⟩, ?_, ?_, ?_⟩
      · rw [key us (hsub hus), hdiff0, zero_mul]
      · intro u hu
        have huU : u ∈ Icc 0 U0 := ⟨hu.1, hu.2.le.trans husU.le⟩
        have huI : u ∈ Icc 0 L := ⟨huU.1, huU.2.trans hUL.le⟩
        have h1 : Fm L (G μ) (B μ) u < Fm L (G μ) (B μ) us := (hmono μ hμ).1 huU hus hu.2
        have h2 := (hmono μ hμ).2.monotoneOn h0I' huU hu.1
        rw [Hm_zero] at h2
        rw [key u huI]
        exact mul_neg_of_neg_of_pos (by linarith) (by linarith)
      · intro u hu
        have huU : u ∈ Icc 0 U0 := ⟨hus.1.trans hu.1.le, hu.2⟩
        have huI : u ∈ Icc 0 L := ⟨huU.1, huU.2.trans hUL.le⟩
        have h1 : Fm L (G μ) (B μ) us < Fm L (G μ) (B μ) u := (hmono μ hμ).1 hus huU hu.1
        have h2 := (hmono μ hμ).2.monotoneOn h0I' huU (hus.1.trans hu.1.le)
        rw [Hm_zero] at h2
        rw [key u huI]
        exact mul_pos (by linarith) (by linarith)

end Uniform

/-! ### The collision statement -/

theorem geomCollision {Par : Type*} [TopologicalSpace Par] (F : SymbolFamily Par) (K : Set Par) :
    GeomCollision F K := by
  unfold GeomCollision
  intro hK hH hR
  obtain ⟨g, hg⟩ := hH
  rcases K.eq_empty_or_nonempty with hKe | ⟨μ0, hμ0⟩
  · have hd : CollData F.L 1 K (F.G 0) (F.B 0) := collData_empty hKe _ _
    constructor
    · unfold GeomCollisionLeftConcl
      exact left_concl_of_data F.L_pos one_pos hK hd
    · unfold GeomCollisionLeftConcl
      exact left_concl_of_data F.L_pos one_pos hK (collData_mirror F.L_pos hd)
  · have hgpos : 0 < g := (hg μ0 hμ0).gstar_pos
    have hd : CollData F.L g K (F.G 0) (F.B 0) :=
      { lb := fun μ hμ u hu => (hg μ hμ).G0_lb u hu
        diffG := fun μ hμ => (hR.1.1 μ hμ).differentiableOn (by norm_num)
        diffB := fun μ hμ => (hR.2.1 μ hμ).differentiableOn (by norm_num)
        contG := by simpa using hR.1.2 0 (Nat.zero_le _)
        contB := by simpa using hR.2.2 0 (Nat.zero_le _)
        derG := by simpa [iteratedDerivWithin_one] using hR.1.2 1 (by norm_num)
        derB := by simpa [iteratedDerivWithin_one] using hR.2.2 1 (by norm_num) }
    constructor
    · unfold GeomCollisionLeftConcl
      exact left_concl_of_data F.L_pos hgpos hK hd
    · unfold GeomCollisionLeftConcl
      exact left_concl_of_data F.L_pos hgpos hK (collData_mirror F.L_pos hd)

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.Collision.geomCollision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.Collision.geomCollision

end FormalResearch.JacobiEigenvectors.TheoremA.Collision
