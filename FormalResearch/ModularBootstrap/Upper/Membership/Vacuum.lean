module

public import FormalResearch.ModularBootstrap.Upper.Membership.HankelFormula
public import FormalResearch.ModularBootstrap.Upper.Membership.PairContinuation
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.ReImTopology

/-!
# Membership in `Ā` and the vacuum identity, abstract form (`fw:FWM`, `cmb:K7`)

Abstract statement of Lemma `FW-M` (`fw:FWM` items 1-3, `upper_transfer.tex`), which at `w = 1` is
Lemma `K7` (`cmb:K7`, `comb_estimates.tex`, "Membership" and "Vacuum").  Data:

* a Fourier pair `(h, ĥ)` of real radial profiles (`RadialFourierPair w h ĥ`: continuous, integrable
  radial lifts on `ℝ^{2w}`, `𝓕 (radialLift w h) = radialLift w ĥ`), where `ĥ = 𝓗_w h` is the
  order-`(w-1)` Hankel transform in the normalisation of `Crossing.TestClass`;
* kernel integrability `∫₀^∞ |h| K_{c'/12}^{(w)} < ∞`, same for `ĥ` (the consequence of the decay
  `|h| + |ĥ| ≤ C e^{-c' L - πx}` that the proof uses; see `DecayIntegrability`);
* the comb `H0 = h₀(b)` as a function on the strip: continuous on `|Im b| ≤ 1/2`, holomorphic on
  `|Im b| < 1/2`, equal to `h(c' b²/3)` for real `b` (`StripContinuation`).

Conclusions (`fwM_membership_vacuum`), for `g = ½ (h - ĥ)` (`pairOdd`), `a = c'/12 ≥ S`:

1. `g ∈ Ā` (`TestClass prob a g`);
2. `2π ∫₀^∞ ĥ K_α^{(w)} dt = h₀(b_α)` for `0 ≤ α ≤ a`, `b_α = i (3α/c')^{1/2}`
   (analytic Hankel continuation of `ĥ`, identity theorem on the strip);
3. `g_vac = ½ ∑_s (-1)^{|s|} h₀(b_{a - r_s}) - π ∫₀^∞ h V dt`, i.e. the paper's
   `½ ∑_r c_r h(-a + r) - π ∫ h V` with `h(-α) := h₀(b_α)` (the values `b = i y`).

The normalisation of `Crossing.gVac` (`-2π ∫ g V`) and `Crossing.cardyV` (`V = ∑_s (-1)^{|s|} K_{a-r_s}`)
matches the paper's `g_vac = -2π ∫ g V dt`, `V_{w,Q} = ∑ c_r K_{a-r}` with `c_r` the coefficients of
`Q`; no mismatch.

Everything is proved unconditionally from the hypotheses stated.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Membership

open FormalResearch.ModularBootstrap.Crossing FormalResearch.ModularBootstrap.WeightAxioms

/-! ### Identity theorem on the strip -/

/-- The open strip `|Im b| < 1/2`. -/
def openStrip : Set ℂ := {b : ℂ | |b.im| < 1 / 2}

/-- The closed strip `|Im b| ≤ 1/2`. -/
def closedStrip : Set ℂ := {b : ℂ | |b.im| ≤ 1 / 2}

lemma openStrip_eq : openStrip = Complex.im ⁻¹' Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
  ext b; simp [openStrip, abs_lt]

lemma isOpen_openStrip : IsOpen openStrip := by
  rw [openStrip_eq]; exact isOpen_Ioo.preimage Complex.continuous_im

lemma isPreconnected_openStrip : IsPreconnected openStrip := by
  have : Convex ℝ openStrip := by
    rw [openStrip_eq]; exact (convex_Ioo _ _).linear_preimage Complex.imLm
  exact this.isPreconnected

lemma closedStrip_subset_closure_openStrip : closedStrip ⊆ closure openStrip := by
  rw [openStrip_eq, Complex.closure_preimage_im, closure_Ioo (by norm_num)]
  intro b hb
  change |b.im| ≤ 1 / 2 at hb
  exact ⟨by linarith [(abs_le.mp hb).1], (abs_le.mp hb).2⟩

/-- Two functions continuous on the closed strip, holomorphic on the open strip and equal on `ℝ`
are equal on the closed strip (identity theorem + continuity). -/
theorem eqOn_closedStrip_of_real {f g : ℂ → ℂ}
    (hfc : ContinuousOn f closedStrip) (hgc : ContinuousOn g closedStrip)
    (hfd : DifferentiableOn ℂ f openStrip) (hgd : DifferentiableOn ℂ g openStrip)
    (hreal : ∀ b : ℝ, f (b : ℂ) = g (b : ℂ)) : EqOn f g closedStrip := by
  have h0 : (0 : ℂ) ∈ openStrip := by simp [openStrip]
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), f z = g z := by
    have hten : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · exact (Complex.continuous_ofReal.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with x hx
        simpa using hx
    exact hten.frequently (Filter.Eventually.of_forall (fun x : ℝ => hreal x)).frequently
  have heq := (hfd.analyticOnNhd isOpen_openStrip).eqOn_of_preconnected_of_frequently_eq
    (hgd.analyticOnNhd isOpen_openStrip) isPreconnected_openStrip h0 hfreq
  exact heq.of_subset_closure hfc hgc
    (fun b (hb : |b.im| < 1 / 2) => (hb.le : |b.im| ≤ 1 / 2))
    closedStrip_subset_closure_openStrip

/-! ### Kernel integrability and the Cardy weight -/

/-- `∫₀^∞ |ψ| K_a^{(w)} dt < ∞`: the integrability the vacuum step uses. -/
def KernelIntegrable (w : ℕ) (a : ℝ) (ψ : ℝ → ℝ) : Prop :=
  IntegrableOn (fun t : ℝ => |ψ t| * kernelK w a t) (Ioi 0)

lemma KernelIntegrable.shift {w : ℕ} {a α : ℝ} {ψ : ℝ → ℝ} (hψ : ContinuousOn ψ (Ici 0))
    (hk : KernelIntegrable w a ψ) (hα0 : 0 ≤ α) (hα : α ≤ a) :
    IntegrableOn (fun t : ℝ => ψ t * kernelK w α t) (Ioi 0) := by
  refine hk.mono' ?_ ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_))
  · exact ((hψ.mono Ioi_subset_Ici_self).mul (continuous_kernelK w α).continuousOn
      ).aestronglyMeasurable measurableSet_Ioi
  · have ht0 : 0 ≤ t := (mem_Ioi.mp ht).le
    rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (kernelK_nonneg hα0 ht0)]
    exact mul_le_mul_of_nonneg_left (kernelK_mono_alpha hα0 hα ht0) (abs_nonneg _)

lemma KernelIntegrable.cardy {prob : FixedWeightProblem} {a : ℝ} (ha : prob.totalShift ≤ a)
    {ψ : ℝ → ℝ} (hψ : ContinuousOn ψ (Ici 0)) (hk : KernelIntegrable prob.w a ψ) :
    IntegrableOn (fun t : ℝ => |ψ t| * prob.cardyV a t) (Ioi 0) := by
  refine hk.mono' ?_ ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_))
  · exact ((hψ.abs.mono Ioi_subset_Ici_self).mul (continuous_cardyV prob a).continuousOn
      ).aestronglyMeasurable measurableSet_Ioi
  · have ht0 : 0 ≤ t := (mem_Ioi.mp ht).le
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (prob.cardyV_nonneg ha ht0))]
    exact mul_le_mul_of_nonneg_left (cardyV_le_kernelK prob ha ht0) (abs_nonneg _)

lemma integrableOn_mul_cardyV {prob : FixedWeightProblem} {a : ℝ} (ha : prob.totalShift ≤ a)
    {ψ : ℝ → ℝ} (hψ : ContinuousOn ψ (Ici 0)) (hk : KernelIntegrable prob.w a ψ) :
    IntegrableOn (fun t : ℝ => ψ t * prob.cardyV a t) (Ioi 0) := by
  refine (hk.cardy ha hψ).mono' ?_
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_))
  · exact ((hψ.mono Ioi_subset_Ici_self).mul (continuous_cardyV prob a).continuousOn
      ).aestronglyMeasurable measurableSet_Ioi
  · rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (prob.cardyV_nonneg ha (mem_Ioi.mp ht).le)]

/-! ### Vacuum points and the continuation of the transform -/

/-- The vacuum point `b_α = i (3α/c')^{1/2}` (`cmb:K7`); `c' b_α² / 3 = -α`, and `b_a = i/2`
for `a = c'/12`. -/
noncomputable def bAlpha (c' α : ℝ) : ℂ := Complex.I * ((Real.sqrt (3 * α / c') : ℝ) : ℂ)

lemma kernelArg_bAlpha {c' α : ℝ} (hc' : 0 < c') (hα : 0 ≤ α) :
    -(c' : ℂ) * bAlpha c' α ^ 2 / 3 = (α : ℂ) := by
  unfold bAlpha
  have hsq : ((Real.sqrt (3 * α / c') : ℝ) : ℂ) ^ 2 = ((3 * α / c' : ℝ) : ℂ) := by
    exact_mod_cast Real.sq_sqrt (by positivity)
  have hc0 : (c' : ℂ) ≠ 0 := by exact_mod_cast hc'.ne'
  rw [mul_pow, Complex.I_sq, hsq]
  push_cast
  field_simp

lemma bAlpha_mem_closedStrip {c' α : ℝ} (hc' : 0 < c') (hα : α ≤ c' / 12) :
    bAlpha c' α ∈ closedStrip := by
  show |(bAlpha c' α).im| ≤ 1 / 2
  have him : (bAlpha c' α).im = Real.sqrt (3 * α / c') := by simp [bAlpha]
  rw [him, abs_of_nonneg (Real.sqrt_nonneg _)]
  calc Real.sqrt (3 * α / c') ≤ Real.sqrt (1 / 4) := by
        refine Real.sqrt_le_sqrt ?_
        rw [div_le_iff₀ hc']; linarith
    _ = 1 / 2 := by
        rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)

/-- The comb `h₀(b)` on the strip (`cmb:K7`, `fw:FWM`): continuous on `|Im b| ≤ 1/2`,
holomorphic on `|Im b| < 1/2`, and `h₀(b) = h(c' b²/3)` for real `b`. -/
structure StripContinuation (c' : ℝ) (h : ℝ → ℝ) (H0 : ℂ → ℂ) : Prop where
  cont : ContinuousOn H0 closedStrip
  holo : DifferentiableOn ℂ H0 openStrip
  real : ∀ b : ℝ, H0 (b : ℂ) = (h (c' * b ^ 2 / 3) : ℂ)

/-- Analytic Hankel continuation (`fw:FWM` item 3): `h₀ = -hankelContinuationW w c' ĥ` on the
closed strip. -/
theorem StripContinuation.eq_continuation {w : ℕ} (hw : 1 ≤ w) {c' : ℝ} (hc' : 0 < c')
    {h ĥ : ℝ → ℝ} {H0 : ℂ → ℂ} (hp : RadialFourierPair w h ĥ)
    (hk' : KernelIntegrable w (c' / 12) ĥ) (hS : StripContinuation c' h H0) :
    EqOn H0 (fun b => -(hankelContinuationW w c' ĥ b)) closedStrip := by
  refine eqOn_closedStrip_of_real hS.cont ?_ hS.holo ?_ (fun b => ?_)
  · exact (continuousOn_hankelContinuationW_of_integrable hw hc' hp.cont' hk').neg
  · exact (differentiableOn_hankelContinuationW_of_integrable hw hc' hp.cont' hk').neg
  · rw [hS.real b, hankelContinuationW_of_pair hw hc' hp.symm b, neg_neg]

/-- **Vacuum kernel identity**: for `0 ≤ α ≤ c'/12`, `2π ∫₀^∞ ĥ K_α^{(w)} dt = h₀(b_α)`. -/
theorem StripContinuation.vacuum_kernel {w : ℕ} (hw : 1 ≤ w) {c' : ℝ} (hc' : 0 < c')
    {h ĥ : ℝ → ℝ} {H0 : ℂ → ℂ} (hp : RadialFourierPair w h ĥ)
    (hk' : KernelIntegrable w (c' / 12) ĥ) (hS : StripContinuation c' h H0)
    {α : ℝ} (hα0 : 0 ≤ α) (hα : α ≤ c' / 12) :
    ((2 * π * ∫ t in Ioi (0 : ℝ), ĥ t * kernelK w α t : ℝ) : ℂ) = H0 (bAlpha c' α) := by
  rw [hS.eq_continuation hw hc' hp hk' (bAlpha_mem_closedStrip hc' hα)]
  beta_reduce
  unfold hankelContinuationW
  rw [kernelArg_bAlpha hc' hα0]
  have hint : ∀ t ∈ Ioi (0 : ℝ), (ĥ t : ℂ) * kernelKC w (α : ℂ) (t : ℂ) =
      ((ĥ t * kernelK w α t : ℝ) : ℂ) := fun t _ => by
    rw [kernelKC_ofReal w hw α t]; push_cast; ring
  rw [setIntegral_congr_fun measurableSet_Ioi hint, integral_complex_ofReal]
  push_cast; ring

/-! ### The abstract membership and vacuum theorem -/

/-- **Lemma `FW-M` (items 1-3) and Lemma `K7` (`w = 1`), abstract form.**
Let `(h, ĥ)` be a Fourier pair of real radial profiles at weight `w = prob.w`, `a = c'/12 ≥ S`,
with `∫ |h| K_a < ∞`, `∫ |ĥ| K_a < ∞`, and `H0 = h₀` a strip-continuous comb with
`h₀(b) = h(c' b²/3)` on `ℝ`.  Then for `g = ½ (h - ĥ)`:
`g ∈ Ā` and `g_vac = ½ ∑_s (-1)^{|s|} h₀(b_{a - r_s}) - π ∫₀^∞ h V dt`
(the paper's `½ ∑_r c_r h(-a + r) - π ∫ h V`, with `h(-α) := h₀(b_α)`). -/
theorem fwM_membership_vacuum {prob : FixedWeightProblem} {c' : ℝ} (hc' : 0 < c')
    (hS : prob.totalShift ≤ c' / 12) {h ĥ : ℝ → ℝ} {H0 : ℂ → ℂ}
    (hp : RadialFourierPair prob.w h ĥ)
    (hk : KernelIntegrable prob.w (c' / 12) h) (hk' : KernelIntegrable prob.w (c' / 12) ĥ)
    (hH : StripContinuation c' h H0) :
    TestClass prob (c' / 12) (pairOdd h ĥ) ∧
      ((prob.gVac (c' / 12) (pairOdd h ĥ) : ℝ) : ℂ) =
        (1 / 2 : ℂ) * ∑ s : Finset (Fin prob.m), (-1 : ℂ) ^ s.card *
            H0 (bAlpha c' (c' / 12 - prob.shiftSum s)) -
          (π : ℂ) * ((∫ t in Ioi (0 : ℝ), h t * prob.cardyV (c' / 12) t : ℝ) : ℂ) := by
  have hw := prob.hw
  refine ⟨pairOdd_testClass hp (hk.cardy hS hp.cont) (hk'.cardy hS hp.cont')
    (fun t ht => prob.cardyV_nonneg hS ht), ?_⟩
  set a : ℝ := c' / 12 with ha
  have hVh := integrableOn_mul_cardyV hS hp.cont hk
  have hVh' := integrableOn_mul_cardyV hS hp.cont' hk'
  have hshift : ∀ s : Finset (Fin prob.m), 0 ≤ a - prob.shiftSum s ∧ a - prob.shiftSum s ≤ a :=
    fun s => ⟨by linarith [prob.shiftSum_le_totalShift s], by linarith [prob.shiftSum_nonneg s]⟩
  -- the integral of `ĥ V` splits over the shifts
  have hsplit : ∫ t in Ioi (0 : ℝ), ĥ t * prob.cardyV a t =
      ∑ s : Finset (Fin prob.m), (-1 : ℝ) ^ s.card *
        ∫ t in Ioi (0 : ℝ), ĥ t * kernelK prob.w (a - prob.shiftSum s) t := by
    have hfun : ∀ t, ĥ t * prob.cardyV a t = ∑ s : Finset (Fin prob.m), (-1 : ℝ) ^ s.card *
        (ĥ t * kernelK prob.w (a - prob.shiftSum s) t) := fun t => by
      unfold FixedWeightProblem.cardyV
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => by ring
    simp_rw [hfun]
    rw [integral_finsetSum _ (fun s _ =>
      ((hk'.shift hp.cont' (hshift s).1 (hshift s).2).const_mul ((-1 : ℝ) ^ s.card)))]
    exact Finset.sum_congr rfl fun s _ => integral_const_mul _ _
  have hvac : ∀ s : Finset (Fin prob.m),
      ((2 * π * ∫ t in Ioi (0 : ℝ), ĥ t * kernelK prob.w (a - prob.shiftSum s) t : ℝ) : ℂ) =
        H0 (bAlpha c' (a - prob.shiftSum s)) := fun s =>
    hH.vacuum_kernel hw hc' hp hk' (hshift s).1 (by have := (hshift s).2; rw [ha] at this; exact this)
  have hg : ∫ t in Ioi (0 : ℝ), pairOdd h ĥ t * prob.cardyV a t =
      ((∫ t in Ioi (0 : ℝ), h t * prob.cardyV a t) -
        (∫ t in Ioi (0 : ℝ), ĥ t * prob.cardyV a t)) / 2 := by
    have heq : ∀ t, pairOdd h ĥ t * prob.cardyV a t =
        (h t * prob.cardyV a t - ĥ t * prob.cardyV a t) / 2 := fun t => by
      simp only [pairOdd]; ring
    simp_rw [heq]
    rw [integral_div, integral_sub hVh hVh']
  have hreal : prob.gVac a (pairOdd h ĥ) =
      -π * (∫ t in Ioi (0 : ℝ), h t * prob.cardyV a t) +
        π * ∑ s : Finset (Fin prob.m), (-1 : ℝ) ^ s.card *
          (∫ t in Ioi (0 : ℝ), ĥ t * kernelK prob.w (a - prob.shiftSum s) t) := by
    unfold FixedWeightProblem.gVac
    rw [hg, hsplit]; ring
  rw [hreal]
  push_cast
  have hsum : (π : ℂ) * ∑ s : Finset (Fin prob.m), (-1 : ℂ) ^ s.card *
        ((∫ t in Ioi (0 : ℝ), ĥ t * kernelK prob.w (a - prob.shiftSum s) t : ℝ) : ℂ) =
      (1 / 2 : ℂ) * ∑ s : Finset (Fin prob.m), (-1 : ℂ) ^ s.card *
        H0 (bAlpha c' (a - prob.shiftSum s)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← hvac s]
    push_cast
    ring
  rw [← hsum]
  ring

/-- info: 'FormalResearch.ModularBootstrap.Upper.Membership.fwM_membership_vacuum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fwM_membership_vacuum

end FormalResearch.ModularBootstrap.Upper.Membership
