module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.ActionDerivative

/-!
# Paper J, Layer 2: the `t`-derivative of the frozen action, `eq:cp-dt` (L2.E, Step 1 of cor:eigen, part 4)

Source: Paper J `thmA.tex`, proof of `cor:eigen`, Step 1: `d_t S_0^{(t)}(X)|_{t=0} = int_{u_-}^{u_+} (B_1 + Q_0 G_1/(2 G_0)) T^{-1/2} du`, `Q_0 = X - B_0`.  Frozen statement: `CorEigenS1` (first two conjuncts).

## Proved here

* `chiCut`: a smooth cutoff of the identity (`chi t = t` for `|t| <= t_0/2`, `|chi t| <= t_0`), so that `G_0 + chi(t) G_1 >= g_*/2` for all `t`.
* `arg_eq`: for `G_0, G_t = G_0 + t G_1 > 0`, `(X - B_t)/(2 sqrt(a G_t)) = (X + t rho - B_0)/(2 sqrt(a G_0))` with `rho = -((X - B_0) G_1/(G_t (1 + w)) + B_1 w)`, `w = sqrt(G_0/G_t)`: the action of the frozen symbols is the action of `(G_0, B_0)` at an energy shifted by `t rho`.
* `rhoDt`, `rhoDt_contDiffOn`: the weight `rho` is `C^1` jointly in `(u, t)` on `[0, L] x R` (with the cutoff).
* **`actionS0_dt_sym`**: `d/dt int_0^L arccos((X - (B_0 + t B_1))/(2 sqrt(E_0[G_0 + t G_1]))) du |_{t=0} = int_0^L (B_1 + (X - B_0) G_1/(2 G_0)) T^{-1/2} du`, from `ActionDeriv.hasDerivAt_shiftAction_C1` (`rho_0 = -(B_1 + (X - B_0) G_1/(2 G_0))`).
* `dm1_data`, `actionS0_frozen_eq`: `(D_1)` gives `G_0, B_0 in C^2`, `G_1, B_1 in C^1`; `actionS0 (frozenFamily F 0) (mu, t)` is the action of `G_0 + t G_1`, `B_0 + t B_1`.
* **`actionS0_frozen_hasDerivAt`**: for `mu in K`, `X` in the open band: `HasDerivAt (t |-> actionS0 (frozenFamily F 0) (mu, t) X) (int_{u_-}^{u_+} (B_1 + (X - B_0) G_1/(2 G_0)) T^{-1/2} du) 0`, with the integrand interval integrable.
  These are the first two conjuncts of `CorEigenS1` with `S_1` replaced by the integral.

## Differences from the paper

As in `ActionDerivative.lean`: no turning-point differentiation.  The substitution `X -> X + t rho_t(u)` is exact (an algebraic identity of the two `arccos` arguments), so the `t`-derivative is the shift derivative of `ActionDerivativeShift.lean`.

## Not formalised

The identification `S_1 = d_t S_0^{(t)}` for the `S` of the frozen statement (third conjunct of `CorEigenS1`): see `CorEigenGapM.lean`.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Set Filter Topology MeasureTheory FormalResearch.JacobiEigenvectors.Setting

/-- A smooth cutoff of the identity: `chi t = t` for `|t| <= t0/2` and `|chi t| <= t0` everywhere. -/
def chiCut (t0 t : ℝ) : ℝ := t * Real.smoothTransition (2 - (t / (t0 / 2)) ^ 2)

lemma chiCut_contDiff (t0 : ℝ) : ContDiff ℝ 1 (chiCut t0) := by
  unfold chiCut
  exact contDiff_id.mul (Real.smoothTransition.contDiff.comp (contDiff_const.sub ((contDiff_id.div_const _).pow 2)))

lemma chiCut_eq {t0 t : ℝ} (ht0 : 0 < t0) (ht : |t| ≤ t0 / 2) : chiCut t0 t = t := by
  unfold chiCut
  have h1 : (t / (t0 / 2)) ^ 2 ≤ 1 := by
    have : |t / (t0 / 2)| ≤ 1 := by
      rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < t0 / 2), div_le_one (by positivity)]
      exact ht
    nlinarith [sq_abs (t / (t0 / 2)), abs_nonneg (t / (t0 / 2))]
  rw [Real.smoothTransition.one_of_one_le (by linarith), mul_one]

lemma chiCut_abs_le {t0 : ℝ} (ht0 : 0 < t0) (t : ℝ) : |chiCut t0 t| ≤ t0 := by
  unfold chiCut
  rcases lt_or_ge |t| t0 with h | h
  · rw [abs_mul, abs_of_nonneg (Real.smoothTransition.nonneg _)]
    have := Real.smoothTransition.le_one (2 - (t / (t0 / 2)) ^ 2)
    calc |t| * Real.smoothTransition (2 - (t / (t0 / 2)) ^ 2) ≤ |t| * 1 :=
          mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ ≤ t0 := by linarith
  · have h2 : (t / (t0 / 2)) ^ 2 ≥ 4 := by
      have : |t / (t0 / 2)| ≥ 2 := by
        rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < t0 / 2), ge_iff_le, le_div_iff₀ (by positivity)]
        linarith
      nlinarith [sq_abs (t / (t0 / 2)), abs_nonneg (t / (t0 / 2))]
    rw [Real.smoothTransition.zero_of_nonpos (by linarith), mul_zero, abs_zero]
    exact ht0.le


lemma arg_eq {a G0 G1 B0 B1 X t : ℝ} (hG0 : 0 < G0) (hGt : 0 < G0 + t * G1) (ha : 0 < a) :
    (X - (B0 + t * B1)) / (2 * Real.sqrt (a * (G0 + t * G1))) =
      (X + t * (-((X - B0) * G1 / ((G0 + t * G1) * (1 + Real.sqrt (G0 / (G0 + t * G1)))) +
          B1 * Real.sqrt (G0 / (G0 + t * G1)))) - B0) / (2 * Real.sqrt (a * G0)) := by
  set Gt := G0 + t * G1 with hGtdef
  set w := Real.sqrt (G0 / Gt) with hw
  have hwpos : 0 < w := Real.sqrt_pos.2 (div_pos hG0 hGt)
  have hw2 : w ^ 2 = G0 / Gt := Real.sq_sqrt (div_pos hG0 hGt).le
  have hG0eq : G0 = Gt * w ^ 2 := by rw [hw2]; field_simp
  have hq : 0 < Real.sqrt (a * Gt) := Real.sqrt_pos.2 (mul_pos ha hGt)
  have hqw : Real.sqrt (a * Gt) * w = Real.sqrt (a * G0) := by
    rw [← Real.sqrt_sq hwpos.le, ← Real.sqrt_mul (mul_pos ha hGt).le, hG0eq]
    congr 1
    ring
  have hkey : t * (-((X - B0) * G1 / (Gt * (1 + w)) + B1 * w)) = (X - B0) * (w - 1) - t * B1 * w := by
    have h1 : t * G1 = Gt - G0 := by rw [hGtdef]; ring
    have h2 : 0 < 1 + w := by linarith
    field_simp
    rw [hG0eq] at h1
    linear_combination (-(X - B0)) * h1
  rw [← hqw, hkey]
  field_simp
  ring


/-- The frozen principal symbol `G_0 + chi(t) G_1` (the cutoff `chi` makes it positive for all `t`). -/
def GtauF (G0 G1 : ℝ → ℝ) (t0 u t : ℝ) : ℝ := G0 u + chiCut t0 t * G1 u

/-- The shift of the energy induced by `t`: `S_0^{(t)}(X) = int arccos((X + t rho_t(u) - B_0(u))/(2 sqrt E_0(u))) du`, `rho_0 = -(B_1 + (X - B_0) G_1/(2 G_0))`. -/
def rhoDt (X : ℝ) (G0 G1 B0 B1 : ℝ → ℝ) (t0 u t : ℝ) : ℝ :=
  -((X - B0 u) * G1 u / (GtauF G0 G1 t0 u t * (1 + Real.sqrt (G0 u / GtauF G0 G1 t0 u t))) +
    B1 u * Real.sqrt (G0 u / GtauF G0 G1 t0 u t))

lemma rhoDt_contDiffOn {L X t0 : ℝ} {G0 G1 B0 B1 : ℝ → ℝ} (hG0 : ContDiffOn ℝ 1 G0 (Icc 0 L))
    (hG1 : ContDiffOn ℝ 1 G1 (Icc 0 L)) (hB0 : ContDiffOn ℝ 1 B0 (Icc 0 L)) (hB1 : ContDiffOn ℝ 1 B1 (Icc 0 L))
    (hGpos : ∀ u ∈ Icc 0 L, 0 < G0 u) (hGt : ∀ u ∈ Icc 0 L, ∀ t, 0 < GtauF G0 G1 t0 u t) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => rhoDt X G0 G1 B0 B1 t0 p.1 p.2) (Icc 0 L ×ˢ univ) := by
  have cu : ∀ g : ℝ → ℝ, ContDiffOn ℝ 1 g (Icc 0 L) →
      ContDiffOn ℝ 1 (fun p : ℝ × ℝ => g p.1) (Icc 0 L ×ˢ univ) :=
    fun g hg => hg.comp contDiff_fst.contDiffOn (fun p hp => hp.1)
  have hχ : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => chiCut t0 p.2) (Icc 0 L ×ˢ univ) :=
    ((chiCut_contDiff t0).comp contDiff_snd).contDiffOn
  have hGt' : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => GtauF G0 G1 t0 p.1 p.2) (Icc 0 L ×ˢ univ) :=
    (cu G0 hG0).add (hχ.mul (cu G1 hG1))
  have hq : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => G0 p.1 / GtauF G0 G1 t0 p.1 p.2) (Icc 0 L ×ˢ univ) :=
    (cu G0 hG0).div hGt' (fun p hp => (hGt p.1 hp.1 p.2).ne')
  have hw : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => Real.sqrt (G0 p.1 / GtauF G0 G1 t0 p.1 p.2)) (Icc 0 L ×ˢ univ) :=
    hq.sqrt (fun p hp => (div_pos (hGpos p.1 hp.1) (hGt p.1 hp.1 p.2)).ne')
  have hw1 : ∀ p ∈ Icc 0 L ×ˢ (univ : Set ℝ), 0 < Real.sqrt (G0 p.1 / GtauF G0 G1 t0 p.1 p.2) :=
    fun p hp => Real.sqrt_pos.2 (div_pos (hGpos p.1 hp.1) (hGt p.1 hp.1 p.2))
  unfold rhoDt
  refine ContDiffOn.neg (ContDiffOn.add ?_ ((cu B1 hB1).mul hw))
  refine (((contDiffOn_const.sub (cu B0 hB0)).mul (cu G1 hG1))).div (hGt'.mul (contDiffOn_const.add hw)) ?_
  intro p hp
  have := hGt p.1 hp.1 p.2
  have := hw1 p hp
  positivity

section Sym

variable {L g : ℝ} {G0 G1 B0 B1 : ℝ → ℝ}

/-- **`eq:cp-dt`** for principal symbols: the `t`-derivative at `t = 0` of the action of `G_0 + t G_1`, `B_0 + t B_1` at the energy `X` of the open band is
`int_0^L (B_1 + (X - B_0) G_1/(2 G_0)) T(u; X)^{-1/2} du` (`T^{-1/2} := 0` where `T <= 0`). -/
theorem actionS0_dt_sym (hL : 0 < L) (hyp : Hyp L G0 B0 g) (hG2 : ContDiffOn ℝ 2 G0 (Icc 0 L))
    (hB2 : ContDiffOn ℝ 2 B0 (Icc 0 L)) (hG1 : ContDiffOn ℝ 1 G1 (Icc 0 L)) (hB1 : ContDiffOn ℝ 1 B1 (Icc 0 L))
    {X : ℝ} (hX1 : Xsm L G0 B0 < X) (hX2 : X < Xsp L G0 B0) :
    HasDerivAt (fun t : ℝ => ∫ u in (0 : ℝ)..L, Real.arccos ((X - (B0 u + t * B1 u)) /
        (2 * Real.sqrt (E0 L (fun v => G0 v + t * G1 v) u))))
      (∫ u in (0 : ℝ)..L, (B1 u + (X - B0 u) * G1 u / (2 * G0 u)) / Real.sqrt (Tfun L G0 B0 X u)) 0 := by
  have hGpos : ∀ u ∈ Icc 0 L, 0 < G0 u := fun u hu => lt_of_lt_of_le hyp.gstar_pos (hyp.G0_lb u hu)
  -- the size of the freezing parameter
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := L)).exists_bound_of_continuousOn hG1.continuousOn
  set M' := |M| + 1 with hM'
  have hM'pos : 0 < M' := by positivity
  set t0 := g / (2 * M') with ht0
  have ht0pos : 0 < t0 := by have := hyp.gstar_pos; positivity
  have hGt : ∀ u ∈ Icc 0 L, ∀ t, 0 < GtauF G0 G1 t0 u t := by
    intro u hu t
    have h1 := chiCut_abs_le ht0pos t
    have h2 : ‖G1 u‖ ≤ M' := le_trans (hM u hu) (by rw [hM']; linarith [le_abs_self M])
    have h3 : |chiCut t0 t * G1 u| ≤ g / 2 := by
      rw [abs_mul]
      calc |chiCut t0 t| * |G1 u| ≤ t0 * M' :=
            mul_le_mul h1 (by simpa [Real.norm_eq_abs] using h2) (abs_nonneg _) ht0pos.le
        _ = g / 2 := by rw [ht0]; field_simp
    have h4 := (abs_le.1 h3).1
    have h5 := hyp.G0_lb u hu
    unfold GtauF
    linarith [hyp.gstar_pos]
  have hρ : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => rhoDt X G0 G1 B0 B1 t0 p.1 p.2) (Icc 0 L ×ˢ univ) :=
    rhoDt_contDiffOn (hG2.of_le (by norm_num)) hG1 (hB2.of_le (by norm_num)) hB1 hGpos hGt
  obtain ⟨-, -, hE0, hEL, hEpos⟩ := E0_data hL hyp hG2
  obtain ⟨a0, b0, ha0, hab, hb0, -, -, hza, hzb, hneg, hpos, hda, hdb⟩ := base_data hL hyp hG2 hB2 hX1 hX2
  have hdE : ∀ u ∈ Icc 0 L, derivWithin (E0 L G0) (Icc 0 L) u = E1G L G0 u := fun u hu =>
    (hasDerivWithinAt_E0 (hG2.differentiableOn (by norm_num)) hu).derivWithin (uniqueDiffOn_Icc hL u hu)
  have h := ActionDeriv.hasDerivAt_shiftAction_C1 hL ((HypMorse.contDiffOn_E0 hG2).of_le (by norm_num))
    (hB2.of_le (by norm_num)) hE0 hEL hEpos hρ ha0 hab hb0 hza hzb hneg hpos
    (by rw [hdE a0 ⟨ha0, by linarith⟩]; exact hda) (by rw [hdE b0 ⟨by linarith, hb0⟩]; exact hdb)
  have hchi0 : chiCut t0 0 = 0 := by
    have := chiCut_eq ht0pos (t := 0) (by simp; positivity)
    simpa using this
  have hev : (fun t : ℝ => ∫ u in (0 : ℝ)..L, Real.arccos ((X + t * rhoDt X G0 G1 B0 B1 t0 u t - B0 u) /
        (2 * Real.sqrt (E0 L G0 u)))) =ᶠ[𝓝 0]
      (fun t : ℝ => ∫ u in (0 : ℝ)..L, Real.arccos ((X - (B0 u + t * B1 u)) /
        (2 * Real.sqrt (E0 L (fun v => G0 v + t * G1 v) u)))) := by
    filter_upwards [Ioo_mem_nhds (by linarith : -(t0 / 2) < 0) (by linarith : (0 : ℝ) < t0 / 2)] with t ht
    have hchi : chiCut t0 t = t := chiCut_eq ht0pos (abs_le.2 ⟨ht.1.le, ht.2.le⟩)
    refine intervalIntegral.integral_congr (fun u hu => ?_)
    rw [uIcc_of_le hL.le] at hu
    show Real.arccos _ = Real.arccos _
    by_cases hend : u = 0 ∨ u = L
    · have e1 : E0 L G0 u = 0 := by rcases hend with rfl | rfl <;> simp [E0]
      have e2 : E0 L (fun v => G0 v + t * G1 v) u = 0 := by rcases hend with rfl | rfl <;> simp [E0]
      rw [e1, e2]
      simp
    · have hin : u ∈ Ioo 0 L := by
        push Not at hend
        exact ⟨lt_of_le_of_ne hu.1 (Ne.symm hend.1), lt_of_le_of_ne hu.2 hend.2⟩
      have hGt' : 0 < G0 u + t * G1 u := by
        have := hGt u hu t
        simpa only [GtauF, hchi] using this
      have ha : 0 < u * (L - u) := mul_pos hin.1 (by linarith [hin.2])
      have := arg_eq (X := X) (B0 := B0 u) (B1 := B1 u) (G1 := G1 u) (t := t) (hGpos u hu) hGt' ha
      have hE : E0 L G0 u = u * (L - u) * G0 u := rfl
      have hE' : E0 L (fun v => G0 v + t * G1 v) u = u * (L - u) * (G0 u + t * G1 u) := rfl
      rw [hE, hE']
      simp only [rhoDt, GtauF, hchi]
      exact congrArg Real.arccos this.symm
  have h' := h.congr_of_eventuallyEq hev.symm
  have hval : -∫ u in (0 : ℝ)..L, rhoDt X G0 G1 B0 B1 t0 u 0 / Real.sqrt (4 * E0 L G0 u - (X - B0 u) ^ 2) =
      ∫ u in (0 : ℝ)..L, (B1 u + (X - B0 u) * G1 u / (2 * G0 u)) / Real.sqrt (Tfun L G0 B0 X u) := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr (fun u hu => ?_)
    rw [uIcc_of_le hL.le] at hu
    have hG := (hGpos u hu).ne'
    have hρ0 : rhoDt X G0 G1 B0 B1 t0 u 0 = -(B1 u + (X - B0 u) * G1 u / (2 * G0 u)) := by
      simp only [rhoDt, GtauF, hchi0, zero_mul, add_zero, div_self hG, Real.sqrt_one]
      field_simp
      ring
    show -(rhoDt X G0 G1 B0 B1 t0 u 0 / Real.sqrt (4 * E0 L G0 u - (X - B0 u) ^ 2)) = _
    rw [hρ0, neg_div, neg_neg]
    rfl
  rw [← hval]
  exact h'

end Sym

section Family

variable {Par : Type*} [TopologicalSpace Par]

/-- The data of `eq:cp-S0p`/`eq:cp-dt` from `(H1)--(H3)` and `(D_1)`: `G_0, B_0 in C^2`, `G_1, B_1 in C^1` on `[0, L]`. -/
lemma dm1_data (F : SymbolFamily Par) (K : Set Par) (hH : HypOn F K) (hD : DM F K 1) {μ : Par} (hμ : μ ∈ K) :
    ∃ g : ℝ, Hyp F.L (F.G 0 μ) (F.B 0 μ) g ∧ ContDiffOn ℝ 2 (F.G 0 μ) (Icc 0 F.L) ∧ ContDiffOn ℝ 2 (F.B 0 μ) (Icc 0 F.L) ∧
      ContDiffOn ℝ 1 (F.G 1 μ) (Icc 0 F.L) ∧ ContDiffOn ℝ 1 (F.B 1 μ) (Icc 0 F.L) := by
  obtain ⟨g, hg⟩ := hH
  have h0 := hD.reg 0 (Nat.zero_le _)
  have h1 := hD.reg 1 le_rfl
  have e0 : (regBudget 1 - 10 * (0 / 2) : ℕ) = 23 := by unfold regBudget; norm_num
  have e1 : (regBudget 1 - 10 * (1 / 2) : ℕ) = 23 := by unfold regBudget; norm_num
  rw [e0] at h0
  rw [e1] at h1
  refine ⟨g, hg μ hμ, (h0.1.1 μ hμ).of_le (by norm_cast), (h0.2.1 μ hμ).of_le (by norm_cast),
    (h1.1.1 μ hμ).of_le (by norm_cast), (h1.2.1 μ hμ).of_le (by norm_cast)⟩

omit [TopologicalSpace Par] in
/-- `S_0^{(t)} = actionS0 (frozenFamily F 0) (mu, t)` is the action of the principal symbols `G_0 + t G_1`, `B_0 + t B_1`. -/
lemma actionS0_frozen_eq (F : SymbolFamily Par) (μ : Par) (t X : ℝ) :
    actionS0 (frozenFamily F 0) (μ, t) X = ∫ u in (0 : ℝ)..F.L, Real.arccos ((X - (F.B 0 μ u + t * F.B 1 μ u)) /
      (2 * Real.sqrt (E0 F.L (fun v => F.G 0 μ v + t * F.G 1 μ v) u))) := by
  unfold actionS0
  simp [frozenFamily]

/-- **`eq:cp-dt`** (the `t`-derivative of the frozen action): for `mu in K`, `X` in the open band, `d/dt S_0^{(t)}(X)|_{t=0} = int_{u_-}^{u_+} (B_1 + (X - B_0) G_1/(2 G_0)) T^{-1/2} du`,
absolutely convergent also at the collision energies. -/
theorem actionS0_frozen_hasDerivAt (F : SymbolFamily Par) (K : Set Par) (hH : HypOn F K) (hD : DM F K 1) {μ : Par} (hμ : μ ∈ K)
    {X : ℝ} (hX : X ∈ Ioo (F.bandLo μ) (F.bandHi μ)) :
    HasDerivAt (fun t : ℝ => actionS0 (frozenFamily F 0) (μ, t) X)
      (∫ u in (F.uMinus μ X)..(F.uPlus μ X), (F.B 1 μ u + (X - F.B 0 μ u) * F.G 1 μ u / (2 * F.G 0 μ u)) /
        Real.sqrt (Tfun F.L (F.G 0 μ) (F.B 0 μ) X u)) 0 ∧
    IntervalIntegrable (fun u => (F.B 1 μ u + (X - F.B 0 μ u) * F.G 1 μ u / (2 * F.G 0 μ u)) /
        Real.sqrt (Tfun F.L (F.G 0 μ) (F.B 0 μ) X u)) volume (F.uMinus μ X) (F.uPlus μ X) := by
  obtain ⟨g, hyp, hG2, hB2, hG1, hB1⟩ := dm1_data F K hH hD hμ
  have hq : ContinuousOn (fun u => F.B 1 μ u + (X - F.B 0 μ u) * F.G 1 μ u / (2 * F.G 0 μ u)) (Icc 0 F.L) := by
    refine hB1.continuousOn.add ((((continuousOn_const.sub hB2.continuousOn).mul hG1.continuousOn)).div
      (continuousOn_const.mul hG2.continuousOn) (fun u hu => ?_))
    have := lt_of_lt_of_le hyp.gstar_pos (hyp.G0_lb u hu)
    positivity
  have hint := (intervalIntegrable_inv_sqrtT F.L_pos hyp hG2 hB2 hX.1 hX.2 hq).2
  refine ⟨?_, hint⟩
  have h1 := actionS0_dt_sym F.L_pos hyp hG2 hB2 hG1 hB1 hX.1 hX.2
  have h2 := integral_zero_L_eq F.L_pos hyp hG2 hB2 hX.1 hX.2
    (fun u => F.B 1 μ u + (X - F.B 0 μ u) * F.G 1 μ u / (2 * F.G 0 μ u))
  rw [uMinus_eq_uMinusS, uPlus_eq_uPlusS, ← h2]
  simp only [actionS0_frozen_eq]
  exact h1

end Family

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.arg_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.arg_eq

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.rhoDt_contDiffOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.rhoDt_contDiffOn

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.actionS0_dt_sym' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.actionS0_dt_sym

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.dm1_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.dm1_data

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.actionS0_frozen_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.actionS0_frozen_hasDerivAt

end FormalResearch.JacobiEigenvectors.TheoremA
