module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.Geometry

/-!
# Paper J, Layer 2 (L2.G4 (d)): the second derivative of `f_+` as a function of the jets

Auxiliary facts for `GeomSoft`.  For a principal pair `(G, B)` with `G >= g > 0` of class `C^2` on `[0, L]`:

* `fPlus_contDiffOn_r`: `f_+` is `C^r` on `(0, L)` if `G, B` are `C^r` on `[0, L]`;
* `deriv_deriv_fPlus_eq`: on `(0, L)`, `f_+'' = f2 L G B` with `f2` an explicit expression in `G, G', G'', B', B''` (division free
  except by `sqrt E_0`, which is positive in `(0, L)`);
* `continuousOn_f2`: `(mu, u) |-> f2 L (G mu) (B mu) u` is continuous on `K x [a, b]`, `0 < a <= b < L`, when the jets
  `G, G', G'', B', B''` are jointly continuous on `K x [0, L]` (this is the `PrincipalReg` hypothesis).

Differences from the paper: none.  Not formalised: nothing.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA.SoftSymbol

open Set Filter Topology FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.TheoremA.HypMorse

variable {L g : ℝ} {G B : ℝ → ℝ}

lemma fPlus_contDiffOn_r (hG : ∀ u ∈ Icc 0 L, g ≤ G u) (hg : 0 < g) {r : ℕ}
    (hGr : ContDiffOn ℝ (r : WithTop ℕ∞) G (Icc 0 L)) (hBr : ContDiffOn ℝ (r : WithTop ℕ∞) B (Icc 0 L)) :
    ContDiffOn ℝ (r : WithTop ℕ∞) (fPlus L G B) (Ioo 0 L) := by
  have hE : ContDiffOn ℝ (r : WithTop ℕ∞) (E0 L G) (Icc 0 L) := by
    unfold E0
    exact (contDiffOn_id.mul (contDiffOn_const.sub contDiffOn_id)).mul hGr
  have hsq : ContDiffOn ℝ (r : WithTop ℕ∞) (fun u => Real.sqrt (E0 L G u)) (Ioo 0 L) := by
    intro u hu
    have hE' : ContDiffAt ℝ (r : WithTop ℕ∞) (E0 L G) u :=
      hE.contDiffAt (Filter.mem_of_superset (isOpen_Ioo.mem_nhds hu) Ioo_subset_Icc_self)
    exact (ContDiffAt.sqrt hE' (ne_of_gt (E0_pos hG hg hu))).contDiffWithinAt
  have hB' : ContDiffOn ℝ (r : WithTop ℕ∞) B (Ioo 0 L) := hBr.mono Ioo_subset_Icc_self
  have : fPlus L G B = fun u => B u + 2 * Real.sqrt (E0 L G u) := rfl
  rw [this]
  exact hB'.add (contDiffOn_const.mul hsq)

/-- `f_+''` written with the jets. -/
def f2 (L : ℝ) (G B : ℝ → ℝ) (u : ℝ) : ℝ :=
  (hder L G B u * Real.sqrt (E0 L G u) - hf L G B u * (Epf L G u / (2 * Real.sqrt (E0 L G u)))) /
    (Real.sqrt (E0 L G u)) ^ 2

lemma deriv_deriv_fPlus_eq (hG : ContDiffOn ℝ 2 G (Icc 0 L)) (hB : ContDiffOn ℝ 2 B (Icc 0 L))
    (hGpos : ∀ v ∈ Ioo 0 L, 0 < G v) {u : ℝ} (hu : u ∈ Ioo 0 L) :
    deriv (deriv (fPlus L G B)) u = f2 L G B u := by
  have hfp : ∀ v ∈ Ioo 0 L, deriv (fPlus L G B) v = hf L G B v / Real.sqrt (E0 L G v) :=
    fun v hv => (hasDerivAt_fPlus' hG hB hv (E0_pos_Ioo hGpos hv)).deriv
  have hsq : ∀ v ∈ Ioo 0 L, Real.sqrt (E0 L G v) ≠ 0 :=
    fun v hv => (Real.sqrt_pos.2 (E0_pos_Ioo hGpos hv)).ne'
  have hEv : deriv (fPlus L G B) =ᶠ[𝓝 u] fun v => hf L G B v / Real.sqrt (E0 L G v) :=
    Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hu) hfp
  have hquot : HasDerivAt (fun v => hf L G B v / Real.sqrt (E0 L G v))
      ((hder L G B u * Real.sqrt (E0 L G u) - hf L G B u *
        (Epf L G u / (2 * Real.sqrt (E0 L G u)))) / (Real.sqrt (E0 L G u)) ^ 2) u :=
    (hasDerivAt_hf hG hB hu (E0_pos_Ioo hGpos hu)).div
      (hasDerivAt_sqrtE0 hG hu (E0_pos_Ioo hGpos hu)) (hsq u hu)
  rw [hEv.deriv_eq, hquot.deriv]
  rfl

lemma continuousOn_f2 {Par : Type*} [TopologicalSpace Par] {K : Set Par} {Gp Bp : Par → ℝ → ℝ} {a b g : ℝ}
    (ha : 0 < a) (hb : b < L) (hg : 0 < g) (hGg : ∀ μ ∈ K, ∀ u ∈ Icc 0 L, g ≤ Gp μ u)
    (j0 : ContinuousOn (fun p : Par × ℝ => Gp p.1 p.2) (K ×ˢ Icc 0 L))
    (j1 : ContinuousOn (fun p : Par × ℝ => d1 L (Gp p.1) p.2) (K ×ˢ Icc 0 L))
    (j2 : ContinuousOn (fun p : Par × ℝ => d2 L (Gp p.1) p.2) (K ×ˢ Icc 0 L))
    (k1 : ContinuousOn (fun p : Par × ℝ => d1 L (Bp p.1) p.2) (K ×ˢ Icc 0 L))
    (k2 : ContinuousOn (fun p : Par × ℝ => d2 L (Bp p.1) p.2) (K ×ˢ Icc 0 L)) :
    ContinuousOn (fun p : Par × ℝ => f2 L (Gp p.1) (Bp p.1) p.2) (K ×ˢ Icc a b) := by
  have hsub : K ×ˢ Icc a b ⊆ K ×ˢ Icc 0 L :=
    prod_mono subset_rfl (Icc_subset_Icc ha.le hb.le)
  have c0 := j0.mono hsub
  have c1 := j1.mono hsub
  have c2 := j2.mono hsub
  have e1 := k1.mono hsub
  have e2 := k2.mono hsub
  have cu : ContinuousOn (fun p : Par × ℝ => p.2) (K ×ˢ Icc a b) := continuous_snd.continuousOn
  have cE : ContinuousOn (fun p : Par × ℝ => E0 L (Gp p.1) p.2) (K ×ˢ Icc a b) := by
    unfold E0
    exact (cu.mul (continuousOn_const.sub cu)).mul c0
  have cS : ContinuousOn (fun p : Par × ℝ => Real.sqrt (E0 L (Gp p.1) p.2)) (K ×ˢ Icc a b) :=
    Real.continuous_sqrt.comp_continuousOn cE
  have hSne : ∀ p ∈ K ×ˢ Icc a b, Real.sqrt (E0 L (Gp p.1) p.2) ≠ 0 := by
    intro p hp
    have hu : p.2 ∈ Ioo 0 L := ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩
    have hGpos : ∀ v ∈ Icc 0 L, g ≤ Gp p.1 v := hGg p.1 hp.1
    exact (Real.sqrt_pos.2 (E0_pos hGpos hg hu)).ne'
  have cEpf : ContinuousOn (fun p : Par × ℝ => Epf L (Gp p.1) p.2) (K ×ˢ Icc a b) := by
    unfold Epf
    exact ((continuousOn_const.sub (continuousOn_const.mul cu)).mul c0).add ((cu.mul (continuousOn_const.sub cu)).mul c1)
  have cEpp : ContinuousOn (fun p : Par × ℝ => Epp L (Gp p.1) p.2) (K ×ˢ Icc a b) := by
    unfold Epp
    exact ((continuousOn_const.mul c0).add
      (((continuousOn_const.mul (continuousOn_const.sub (continuousOn_const.mul cu))).mul c1))).add
      ((cu.mul (continuousOn_const.sub cu)).mul c2)
  have chf : ContinuousOn (fun p : Par × ℝ => hf L (Gp p.1) (Bp p.1) p.2) (K ×ˢ Icc a b) := by
    unfold hf
    exact (e1.mul cS).add cEpf
  have chder : ContinuousOn (fun p : Par × ℝ => hder L (Gp p.1) (Bp p.1) p.2) (K ×ˢ Icc a b) := by
    unfold hder
    refine ((e2.mul cS).add (e1.mul (cEpf.div (continuousOn_const.mul cS)
      (fun p hp => mul_ne_zero two_ne_zero (hSne p hp))))).add cEpp
  unfold f2
  refine ((chder.mul cS).sub (chf.mul (cEpf.div (continuousOn_const.mul cS)
    (fun p hp => mul_ne_zero two_ne_zero (hSne p hp))))).div (cS.pow 2) (fun p hp => pow_ne_zero 2 (hSne p hp))

end FormalResearch.JacobiEigenvectors.TheoremA.SoftSymbol
