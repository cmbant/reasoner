module

public import FormalResearch.ModularBootstrap.Mixtures.CrossingA
public import FormalResearch.ModularBootstrap.Upper.Membership.FWM

/-!
# `pmix:crossing` (b): comb membership and the vacuum identity for an atomic source

`positive_mixtures.tex`, Lemma PM.3 (b).  Let `(h₀, ĥ₀)` be a comb and its Hankel transform in the abstract form of
`Upper.Membership.fwM_of_decay` (continuous profiles, Fourier pair on `ℝ^{2w}`, the decay
`|h₀|, |ĥ₀| ≤ C e^{-n' L(x) - πx}`, strip continuation `H₀` with `H₀(b) = h₀(n' b²/3)` on `ℝ`), at the parameter
`n' = c'`, `a = c'/12`, and put `g_w = ½ (h₀ - ĥ₀)` (`pairOdd`).  For an atomic source at a charge with the floor:

* `g_w ∈ \overline{\mathcal A}_{w, src}` and `g_w` has the decay of the envelope;
* the vacuum identity `pmix:comb-vac`:
  `g_vac = ½ ∑_j coef_j H₀(b_{a - shift_j}) - π ∫₀^∞ h₀ V dt`, where `H₀(b_α) = "h₀(-α)"`
  (the paper's `½ ∫ h₀(-a'+r) dλ(r)`), as an identity in `ℂ` (both sides are real);
* the comb term is bounded by `‖λ‖_TV = C_vac` when `|h₀(-α)| ≤ 2` at the source shifts.

The proof is the proof of `fwM_membership_vacuum` for the signed combination of kernels
`V = ∑_j coef_j K_{a - shift_j}`, plus the comparison `|V| ≤ ‖λ‖_TV K_a` for the test-class integrability.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real FourierTransform

namespace FormalResearch.ModularBootstrap.Mixtures

open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.FixedWeight FormalResearch.ModularBootstrap.Upper.Membership

namespace FloorData.At

variable {src : ShiftSource} {F : FloorData src} {a : ℝ}

/-- A test function of `Q ≡ 1` (weight `V = K_a`) is a source test function. -/
lemma testClass_of_trivial (h : F.At a) {g : ℝ → ℝ}
    (hg : Crossing.TestClass (trivialProductProblem src.w src.hw) a g) : TestClass src a g := by
  refine ⟨hg.cont, hg.int_lift, hg.fourier_odd, ?_⟩
  have hKint : IntegrableOn (fun t => |g t| * kernelK src.w a t) (Ioi 0) :=
    hg.int_cardy.congr_fun (fun t _ => by simp only [trivial_cardyV]) measurableSet_Ioi
  have hc : ContinuousOn (fun t => |g t| * src.cardyV a t) (Ioi 0) :=
    ((hg.cont.abs.mono Ioi_subset_Ici_self).mul (src.continuous_cardyV _).continuousOn)
  refine (hKint.const_mul src.tv).mono' (hc.aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  have ht0 : 0 < t := ht
  rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (h.pos_V ht0).le)]
  calc |g t| * src.cardyV a t ≤ |g t| * (src.tv * kernelK src.w a t) :=
        mul_le_mul_of_nonneg_left (h.upper ht0.le) (abs_nonneg _)
    _ = src.tv * (|g t| * kernelK src.w a t) := by ring

end FloorData.At

/-- **`pmix:crossing` (b)** (Lemma PM.3 (b)): comb membership, decay and the vacuum identity `pmix:comb-vac`
for an atomic source at the charge `a = c'/12` with the floor (the hypotheses on `(h₀, ĥ₀)` are those of
`fwM_of_decay`). -/
theorem pmix_crossing_b {src : ShiftSource} {F : FloorData src} {c' C : ℝ} (hc' : 0 < c')
    (hA : F.At (c' / 12)) {h ĥ : ℝ → ℝ} {H0 : ℂ → ℂ}
    (hcont : ContinuousOn h (Ici 0)) (hcont' : ContinuousOn ĥ (Ici 0))
    (hd : DecayBound c' C h) (hd' : DecayBound c' C ĥ)
    (hF : 𝓕 (radialLift src.w h) = radialLift src.w ĥ)
    (hH : StripContinuation c' h H0) :
    TestClass src (c' / 12) (pairOdd h ĥ) ∧ DecayBound c' C (pairOdd h ĥ) ∧
      ((src.gVac (c' / 12) (pairOdd h ĥ) : ℝ) : ℂ) =
        (1 / 2 : ℂ) * ∑ j, (src.coef j : ℂ) * H0 (bAlpha c' (c' / 12 - src.shift j)) -
          (π : ℂ) * ((∫ t in Ioi (0 : ℝ), h t * src.cardyV (c' / 12) t : ℝ) : ℂ) := by
  have hw := src.hw
  obtain ⟨hmem, hdec, -⟩ := fwM_of_decay (prob := trivialProductProblem src.w src.hw) hc'
    (by rw [trivialProductProblem_totalShift]; positivity) hcont hcont' hd hd' hF hH
  refine ⟨hA.testClass_of_trivial hmem, hdec, ?_⟩
  set a : ℝ := c' / 12 with ha
  have hp : RadialFourierPair src.w h ĥ :=
    ⟨hcont, hcont', radialLift_integrable_of_decay hw hc' hcont hd,
      radialLift_integrable_of_decay hw hc' hcont' hd', hF⟩
  have hk : KernelIntegrable src.w a h := kernelIntegrable_of_decay hw hc' hcont hd
  have hk' : KernelIntegrable src.w a ĥ := kernelIntegrable_of_decay hw hc' hcont' hd'
  have hshift : ∀ j, 0 ≤ a - src.shift j ∧ a - src.shift j ≤ a :=
    fun j => ⟨by linarith [hA.shift j], by linarith [src.hshift j]⟩
  -- splitting `∫ ψ V` over the atoms
  have hsplit : ∀ {ψ : ℝ → ℝ}, ContinuousOn ψ (Ici 0) → KernelIntegrable src.w a ψ →
      IntegrableOn (fun t => ψ t * src.cardyV a t) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), ψ t * src.cardyV a t =
        ∑ j, src.coef j * ∫ t in Ioi (0 : ℝ), ψ t * kernelK src.w (a - src.shift j) t := by
    intro ψ hψ hkψ
    have hfun : ∀ t, ψ t * src.cardyV a t =
        ∑ j, src.coef j * (ψ t * kernelK src.w (a - src.shift j) t) := fun t => by
      unfold ShiftSource.cardyV
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hint : ∀ j ∈ Finset.univ, IntegrableOn
        (fun t => src.coef j * (ψ t * kernelK src.w (a - src.shift j) t)) (Ioi 0) := fun j _ =>
      (hkψ.shift hψ (hshift j).1 (hshift j).2).const_mul _
    simp_rw [hfun]
    refine ⟨integrable_finsetSum _ hint, ?_⟩
    rw [integral_finsetSum _ hint]
    exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
  obtain ⟨hVh, -⟩ := hsplit hcont hk
  obtain ⟨hVh', hsplit'⟩ := hsplit hcont' hk'
  have hvac : ∀ j,
      ((2 * π * ∫ t in Ioi (0 : ℝ), ĥ t * kernelK src.w (a - src.shift j) t : ℝ) : ℂ) =
        H0 (bAlpha c' (a - src.shift j)) := fun j =>
    hH.vacuum_kernel hw hc' hp hk' (hshift j).1 (by have := (hshift j).2; rw [ha] at this; exact this)
  have hg : ∫ t in Ioi (0 : ℝ), pairOdd h ĥ t * src.cardyV a t =
      ((∫ t in Ioi (0 : ℝ), h t * src.cardyV a t) -
        (∫ t in Ioi (0 : ℝ), ĥ t * src.cardyV a t)) / 2 := by
    have heq : ∀ t, pairOdd h ĥ t * src.cardyV a t =
        (h t * src.cardyV a t - ĥ t * src.cardyV a t) / 2 := fun t => by
      simp only [pairOdd]; ring
    simp_rw [heq]
    rw [integral_div, integral_sub hVh hVh']
  have hreal : src.gVac a (pairOdd h ĥ) =
      -π * (∫ t in Ioi (0 : ℝ), h t * src.cardyV a t) +
        π * ∑ j, src.coef j *
          (∫ t in Ioi (0 : ℝ), ĥ t * kernelK src.w (a - src.shift j) t) := by
    unfold ShiftSource.gVac
    rw [hg, hsplit']; ring
  rw [hreal]
  push_cast
  have hsum : (π : ℂ) * ∑ j, (src.coef j : ℂ) *
        ((∫ t in Ioi (0 : ℝ), ĥ t * kernelK src.w (a - src.shift j) t : ℝ) : ℂ) =
      (1 / 2 : ℂ) * ∑ j, (src.coef j : ℂ) * H0 (bAlpha c' (a - src.shift j)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hvac j]
    push_cast
    ring
  rw [← hsum]
  ring

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.pmix_crossing_b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pmix_crossing_b

/-- **The comb term of `pmix:comb-vac` is bounded by `C_vac = ‖λ‖_TV`** as soon as `|h₀(-α)| ≤ 2` at the source
shifts (`‖H₀(b_{a - shift_j})‖ ≤ 2`). -/
theorem comb_term_le {src : ShiftSource} {c' : ℝ} {H0 : ℂ → ℂ}
    (hb : ∀ j, ‖H0 (bAlpha c' (c' / 12 - src.shift j))‖ ≤ 2) :
    ‖(1 / 2 : ℂ) * ∑ j, (src.coef j : ℂ) * H0 (bAlpha c' (c' / 12 - src.shift j))‖ ≤ src.tv := by
  rw [norm_mul]
  have hsum : ‖∑ j, (src.coef j : ℂ) * H0 (bAlpha c' (c' / 12 - src.shift j))‖ ≤
      ∑ j, |src.coef j| * 2 := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hb j) (abs_nonneg _)
  rw [← Finset.sum_mul] at hsum
  calc ‖(1 / 2 : ℂ)‖ * _ ≤ (1 / 2) * ((∑ j, |src.coef j|) * 2) := by
        rw [norm_div, norm_one, Complex.norm_ofNat]
        exact mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = src.tv := by unfold ShiftSource.tv; ring

/-- **The comb term for a mixture** (`pmix:comb-vac`, last clause): for the flattened mixture the comb term is
`½ ∑_i d_i ∑_S (-1)^{|S|} H₀(b_{a - r_i - shiftSum S})`, the paper's `½ ∑_{i,u} d_i c_{i,u} h₀(-a' + r'_i + u)`. -/
theorem MixtureData.comb_term_eq (M : MixtureData) (c' : ℝ) (H0 : ℂ → ℂ) :
    ∑ x, (M.toSource.coef x : ℂ) * H0 (bAlpha c' (c' / 12 - M.toSource.shift x)) =
      ∑ i, (M.d i : ℂ) * ∑ S : Finset (Fin (M.Q i).m),
        (-1 : ℂ) ^ S.card * H0 (bAlpha c' (c' / 12 - M.r i - (M.Q i).shiftSum S)) := by
  rw [M.sum_toSource]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  show ((M.d i * (-1 : ℝ) ^ S.card : ℝ) : ℂ) * H0 (bAlpha c' (c' / 12 - (M.r i + (M.Q i).shiftSum S))) = _
  rw [sub_add_eq_sub_sub]
  push_cast
  ring

end FormalResearch.ModularBootstrap.Mixtures
