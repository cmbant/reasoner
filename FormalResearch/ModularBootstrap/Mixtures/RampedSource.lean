module

public import FormalResearch.ModularBootstrap.Mixtures.SmoothVacuum
public import FormalResearch.ModularBootstrap.Mixtures.WeightAxioms
public import FormalResearch.ModularBootstrap.Mixtures.CrossingB

/-!
# The smooth weight of a common source, and `K7` for a source (inputs of `pmix:o1`, upper half)

`positive_mixtures.tex`, Lemma PM.7 (`pmix:o1`), upper bound: "by `pmix:weight`(b) and `rem:cardy`, `V_mix` satisfies
hypotheses (i)-(ii) of `pmix:smooth` with `q_mix(x) = (2x)^{w-1} A(x)/(1 - e^{-4πx})²` and `K_2 = w - 1`; by
`pmix:crossing`(b) and `pmix:ramped`, `g_w ∈ \overline{\mathcal A}_{w,mix}` ...".

* `exists_smoothWeight` : for a `CommonSource` there is a `SmoothWeight` with `V c' = src.cardyV (c'/12)`, `A = src.ampl`
  (the amplitude `A(x) = ∑ coef_j e^{-4π shift_j x}` of `pmix:Amix`), built from the real asymptote `ShiftSource.real_asymp`
  (`pmix:weight`(b)), the sandwich `0 ≤ V ≤ ‖λ‖_TV K_a` (`pmix:weight`(a)), the positivity `A ≥ d_λ Q_0 > 0`
  (`ampl_lower`) and the far-band bound of the trivial product `Q ≡ 1` (`cardyFarBoundP_prob`) times `‖λ‖_TV`;
* `k7_src` : `pmix:crossing`(b) for a comb whose decay is known: membership of `g_w = ½ (h₀ - ĥ₀)` in the source test class,
  the vacuum identity `pmix:comb-vac`, and the bound `|comb term| ≤ C_vac = ‖λ‖_TV` for combs with `|h₀(-α)| ≤ 2` at the
  source shifts (`InnerCombHyp`).

All results are proved unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real FourierTransform

namespace FormalResearch.ModularBootstrap.Mixtures

open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.FixedWeight FormalResearch.ModularBootstrap.Upper.Window
  FormalResearch.ModularBootstrap.Upper.Window.Cardy FormalResearch.ModularBootstrap.Upper.Ramped
  FormalResearch.ModularBootstrap.Upper.Comb FormalResearch.ModularBootstrap.Upper.Membership
  FormalResearch.ModularBootstrap.WeightAxioms FormalResearch.ModularBootstrap.Upper.Hankel FormalResearch.Special

/-! ### The amplitude of a source -/

/-- `x ↦ A(x) = ∑_j coef_j e^{-4π shift_j x}` is Lipschitz on `[0, ∞)`. -/
lemma ShiftSource.abs_ampl_sub_le (src : ShiftSource) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |src.ampl x - src.ampl y| ≤ (∑ j, |src.coef j| * (4 * π * src.shift j)) * |x - y| := by
  unfold ShiftSource.ampl
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  have hs := src.hshift j
  have hu : 0 ≤ 4 * π * src.shift j * x := by positivity
  have hv : 0 ≤ 4 * π * src.shift j * y := by positivity
  have h1 := abs_exp_neg_sub_le hu hv
  have e1 : Real.exp (-4 * π * src.shift j * x) = Real.exp (-(4 * π * src.shift j * x)) := by
    congr 1; ring
  have e2 : Real.exp (-4 * π * src.shift j * y) = Real.exp (-(4 * π * src.shift j * y)) := by
    congr 1; ring
  rw [← mul_sub, abs_mul, e1, e2]
  have h2 : |4 * π * src.shift j * x - 4 * π * src.shift j * y| = 4 * π * src.shift j * |x - y| := by
    rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
  rw [h2] at h1
  calc |src.coef j| * |Real.exp (-(4 * π * src.shift j * x)) - Real.exp (-(4 * π * src.shift j * y))|
      ≤ |src.coef j| * (4 * π * src.shift j * |x - y|) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = _ := by ring

/-- The amplitude of a common source is positive on `(0, ∞)`: `A(x) ≥ d_λ Q_0(e^{-4πx}) > 0`. -/
lemma CommonSource.ampl_pos (C : CommonSource) {x : ℝ} (hx : 0 < x) : 0 < C.src.ampl x := by
  have hq0 : 0 < Real.exp (-4 * π * x) := Real.exp_pos _
  have hq1 : Real.exp (-4 * π * x) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  exact lt_of_lt_of_le (mul_pos C.F.hd (C.F.prob.nullPoly_pos hq0.le hq1)) (ampl_lower C.F C.at_ hx)

/-! ### The smooth weight -/

/-- **A common source gives a `SmoothWeight`** (hypotheses (i)-(ii) of `pmix:smooth` for `V_mix`): see the module
docstring.  `V c' = src.cardyV (c'/12)` and `A = src.ampl`. -/
theorem exists_smoothWeight (C : CommonSource) :
    ∃ W : SmoothWeight C.src.w C.src.hw,
      (∀ c' t : ℝ, W.V c' t = C.src.cardyV (c' / 12) t) ∧ (∀ x : ℝ, W.A x = C.src.ampl x) := by
  have hξ := xiStar_pos
  have hA0 := C.at_ (le_refl C.a₀)
  have ha₀ : 0 < C.a₀ := hA0.pos
  obtain ⟨Cx, hCx, hreal⟩ := C.src.real_asymp (S := C.a₀) hA0.shift (x₀ := xiStar / 2) (half_pos hξ)
  obtain ⟨CF, cF, hCF, hFb⟩ := cardyFarBoundP_prob (trivialProductProblem C.src.w C.src.hw)
    (x₀ := xiStar + 1 / 2) (by linarith)
  have hat : ∀ {c' : ℝ}, max (max 1 (24 * C.a₀)) cF ≤ c' → C.F.At (c' / 12) := by
    intro c' hc'
    have h1 : 24 * C.a₀ ≤ c' := (le_max_right 1 (24 * C.a₀)).trans ((le_max_left _ _).trans hc')
    exact C.at_ (by linarith)
  have htv : 0 < C.src.tv := (C.at_ (le_refl C.a₀)).tv_pos
  refine ⟨{ V := fun c' t => C.src.cardyV (c' / 12) t
            A := C.src.ampl
            c₀ := max (max 1 (24 * C.a₀)) cF
            K := Cx
            hK := hCx
            L := ∑ j, |C.src.coef j| * (4 * π * C.src.shift j)
            hL := Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _)
              (by have := C.src.hshift j; positivity)
            Cd := C.src.tv
            hCd := C.src.tv_nonneg
            nonneg := fun {c' t} hc ht => (hat hc).nonneg_V ht
            cont := fun {c'} _ => C.src.continuous_cardyV (c' / 12)
            dom := fun {c' t} hc ht => (hat hc).upper ht
            asymp := fun {c' x} hc hx => hreal ((le_max_left _ _).trans hc) hx.1
            A_pos := C.ampl_pos hξ
            A_nonneg := fun x hx => (C.ampl_pos (by linarith [hx.1])).le
            A_lip := fun x hx => C.src.abs_ampl_sub_le (by linarith [hx.1]) hξ.le
            far := ⟨C.src.tv * CF, max (max 1 (24 * C.a₀)) cF, mul_pos htv hCF,
              fun c' hc x hx => ?_⟩ }, fun _ _ => rfl, fun _ => rfl⟩
  have hc'0 : 0 < c' := lt_of_lt_of_le one_pos ((le_max_left 1 (24 * C.a₀)).trans
    ((le_max_left _ _).trans hc))
  have hx0 : 0 < x := by linarith
  obtain ⟨hv0, hvb⟩ := hFb c' ((le_max_right _ _).trans hc) x hx
  have hVn : 0 ≤ C.src.cardyV (c' / 12) (c' * x ^ 2 / 3) := (hat hc).nonneg_V (by positivity)
  refine ⟨hVn, ?_⟩
  have hup := (hat hc).upper (t := c' * x ^ 2 / 3) (by positivity)
  have hE : 0 ≤ Real.exp (-(c' * Bessel.besselL x)) * (2 / 3 * c' * x) := by positivity
  have hKt : kernelK C.src.w (c' / 12) (c' * x ^ 2 / 3) =
      (trivialProductProblem C.src.w C.src.hw).cardyV (c' / 12) (c' * x ^ 2 / 3) := by
    rw [trivial_cardyV]
  calc C.src.cardyV (c' / 12) (c' * x ^ 2 / 3) * Real.exp (-(c' * Bessel.besselL x)) * (2 / 3 * c' * x)
      = C.src.cardyV (c' / 12) (c' * x ^ 2 / 3) * (Real.exp (-(c' * Bessel.besselL x)) * (2 / 3 * c' * x)) := by
        ring
    _ ≤ (C.src.tv * kernelK C.src.w (c' / 12) (c' * x ^ 2 / 3)) *
          (Real.exp (-(c' * Bessel.besselL x)) * (2 / 3 * c' * x)) :=
        mul_le_mul_of_nonneg_right hup hE
    _ = C.src.tv * ((trivialProductProblem C.src.w C.src.hw).cardyV (c' / 12) (c' * x ^ 2 / 3) *
          Real.exp (-(c' * Bessel.besselL x)) * (2 / 3 * c' * x)) := by rw [hKt]; ring
    _ ≤ C.src.tv * (CF * √c' * √x * (1 + x) ^ (C.src.w - 1)) :=
        mul_le_mul_of_nonneg_left hvb htv.le
    _ = _ := by ring

/-! ### `pmix:crossing` (b) for a comb: membership, vacuum identity, comb term -/

/-- **`pmix:crossing` (b) for a comb of the ramped family** (`pmix:comb-vac`): at a charge `a = c'/12` with the floor,
for an inner comb `B` (`InnerCombHyp`) whose weight-`w` `K7` conclusion holds for the trivial product `Q ≡ 1` (the decay
of `h₀`, `ĥ₀` is source free), the function `g_w = ½ (h₀ - ĥ₀)` is in the source test class, its vacuum pairing is
`g_vac = ½ ∑_j coef_j H₀(b_{a - shift_j}) - π ∫₀^∞ h₀ V dt`, and the comb term is bounded by `C_vac = ‖λ‖_TV`. -/
theorem k7_src {src : ShiftSource} {F : FloorData src} {c' : ℝ} {B : ℂ → ℂ} (hc' : 0 < c')
    (hA : F.At (c' / 12)) (hB : InnerCombHyp c' B)
    (hK : K7ConclusionW (trivialProductProblem src.w src.hw) c' B) :
    TestClass src (c' / 12)
        (pairOdd (combProfile c' B) (hankelTransform src.w (combProfile c' B))) ∧
      ((src.gVac (c' / 12)
          (pairOdd (combProfile c' B) (hankelTransform src.w (combProfile c' B))) : ℝ) : ℂ) =
        (1 / 2 : ℂ) * ∑ j, (src.coef j : ℂ) * combH0 B (bAlpha c' (c' / 12 - src.shift j)) -
          (π : ℂ) * ((∫ t in Ioi (0 : ℝ), combProfile c' B t * src.cardyV (c' / 12) t : ℝ) : ℂ) ∧
      ‖(1 / 2 : ℂ) * ∑ j, (src.coef j : ℂ) * combH0 B (bAlpha c' (c' / 12 - src.shift j))‖ ≤ src.tv := by
  obtain ⟨C, hC0, hd, hd', -, -, -⟩ := hK
  have hw := src.hw
  have hF : 𝓕 (radialLift src.w (combProfile c' B)) =
      radialLift src.w (hankelTransform src.w (combProfile c' B)) :=
    fourier_radialLift_eq_hankelTransform hw _
  have hcont' : ContinuousOn (hankelTransform src.w (combProfile c' B)) (Ici 0) :=
    continuousOn_hankelTransform hw (hB.integrable_liftW hw hc' hd)
  have hcont : ContinuousOn (combProfile c' B) (Ici 0) := hB.continuousOn_combProfile hc'
  obtain ⟨hmem, -, hvac⟩ := pmix_crossing_b hc' hA hcont hcont' hd hd' hF (hB.stripContinuation hc')
  refine ⟨hmem, hvac, comb_term_le (fun j => ?_)⟩
  set α := c' / 12 - src.shift j with hα
  have hα1 : α ≤ c' / 12 := by linarith [src.hshift j]
  have hmem' := bAlpha_mem_closedStrip hc' hα1
  have hbim : |(bAlpha c' α).im| ≤ 1 / 2 := hmem'
  have hy0 : 0 ≤ Real.sqrt (3 * α / c') := Real.sqrt_nonneg _
  have hy1 : Real.sqrt (3 * α / c') ≤ 1 / 2 := by
    have := hbim
    simpa [bAlpha, abs_of_nonneg hy0] using this
  unfold combH0
  rw [norm_mul]
  have e1 : bAlpha c' α = Complex.I * ((Real.sqrt (3 * α / c') : ℝ) : ℂ) := rfl
  calc ‖sechSqProfile (bAlpha c' α)‖ * ‖B (bAlpha c' α)‖ ≤ 2 * 1 := by
        rw [e1]
        exact mul_le_mul (norm_sechSqProfile_imag_le hy0 hy1) (hB.bound _ (by rw [← e1]; exact hbim))
          (norm_nonneg _) (by norm_num)
    _ = 2 := by norm_num

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.exists_smoothWeight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_smoothWeight

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.k7_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms k7_src

end FormalResearch.ModularBootstrap.Mixtures
