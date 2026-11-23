module

public import FormalResearch.ModularBootstrap.Upper.Window.TailBand
public import FormalResearch.ModularBootstrap.Upper.Window.TailIntegrals

/-!
# Lemma `T` (tail of the fixed designs), `ut:T`

Source: `CFT/modular_bootstrap/paper/upper_transfer.tex`, §5, Lemma `T` (`ut:T`).  For the finite
modifications `B_D^{(f)} = designComb c' f N η₀ σ ε` of the index-`f` reference comb in the compact family
`|σ_k| ≤ M`, `0 ≤ ε'_k ≤ E λ` of `lemma_P_b` (`ut:P`(b); in particular `D(N, η_*, d)` at `f = 1`), with
`h₀ = sech²(πb/2) B_D` (`combProfile`), the Cardy weight `V` and `r₀ > 0` (`r₀ = 3/10` in the paper):
there are `N₂`, `C_T`, `C_far`, independent of `N₁` and `c'`, such that for every `N₁ ≥ max(4f, N₂)` and all
large `c'`, uniformly over the family,

* `∫_{χ_{N₁+1} ≤ x ≤ ξ_* + r₀} |h₀| V dt ≤ FK_c^{(f)} C_T N₁^{-(2/3)(2f - 3/2)}` (intermediate band),
* `∫_{x ≥ ξ_* + r₀} |h₀| V dt ≤ C_far √c'` (far band),

where `t = c'x²/3` (the band is `[c'χ_{N₁+1}²/3, c'(ξ_*+r₀)²/3]` in `t`), `FK_c^{(f)} = FKc 1 f c'`
(`Window.Cardy`).  The proof is that of the paper: `|B_D| ≤ 2|B_ref|` for `N₁ ≥ N₂`
(`designComb_norm_le_exp_ref`), `K6`(a) + `K4` + `K0`(c) (`refComb_band_bound`, `refComb_far_bound`),
Lemma `A_V` in window form (`CardyWindowBound`), and the substitution `t = c'x²/3`.

* `lemma_T_of_cardy`: the statement for an abstract Cardy weight `V` satisfying the named properties
  `CardyWindowBound V 1 r₀` and `CardyFarBound V (ξ_* + r₀)`;
* `lemma_T`: Virasoro (`w = 1`, `Q = (1-q)²`): `V = virasoroProblem.cardyV (c'/12)`, no hypotheses beyond
  those of the paper.  The general `(w, Q)` statement additionally needs the bump `h₀^{(p)}` and the Peano
  bound `fw:e3.6` (`CardyFarBound` with its factor `(1+x)^{m+p}`), which are not formalised.
* `lemma_T_sig1`: the `f = 1` finite modifications with arbitrary offsets `σ` (`η₀ = 1/4`);
  `lemma_T_design1`: the designs `D(N, η_*, d)`, the case `σ = designSigma1 d`.

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Window.Tail

open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Upper.Comb
  FormalResearch.ModularBootstrap.Upper.Holes FormalResearch.ModularBootstrap.Upper.Design
  FormalResearch.ModularBootstrap.Upper.Membership FormalResearch.ModularBootstrap.Upper.Window.Cardy

/-! ### Pointwise bounds on `|h₀|` -/

/-- `|h₀(t)| ≤ sech²(πx/2) |B(x)|` at `t = c'x²/3`. -/
lemma abs_combProfile_le_sech {c' x : ℝ} (B : ℂ → ℂ) (hc' : 0 < c') (hx : 0 ≤ x) :
    |combProfile c' B (c' * x ^ 2 / 3)| ≤ 1 / cosh (π * x / 2) ^ 2 * ‖B (x : ℂ)‖ := by
  unfold combProfile
  rw [xOf_comp hc' hx]
  refine (Complex.abs_re_le_norm _).trans ?_
  unfold combH0
  rw [norm_mul, sechSqProfile_ofReal, Complex.norm_real, Real.norm_of_nonneg (by positivity)]

/-- `|h₀(t)| ≤ 4 e^{-πx} |B(x)|` at `t = c'x²/3`. -/
lemma abs_combProfile_le_exp {c' x : ℝ} (B : ℂ → ℂ) (hc' : 0 < c') (hx : 0 ≤ x) :
    |combProfile c' B (c' * x ^ 2 / 3)| ≤ 4 * exp (-π * x) * ‖B (x : ℂ)‖ := by
  unfold combProfile
  rw [xOf_comp hc' hx]
  refine (Complex.abs_re_le_norm _).trans ?_
  unfold combH0
  rw [norm_mul]
  have := norm_sechSqProfile_ofReal_le x
  rw [abs_of_nonneg hx] at this
  exact mul_le_mul_of_nonneg_right this (norm_nonneg _)

/-- Pointwise integrand bound on the window: if `|B(x)| e^{c'L} ≤ Cb` and the window bound of `V` holds
with constant `Cw`, then `(2/3) c' x |h₀| V ≤ Cb Cw/λ`. -/
lemma integrand_window_le {c' x Cb Cw : ℝ} {B : ℂ → ℂ} {v : ℝ} (hc' : 0 < c') (hx : 0 < x)
    (hv0 : 0 ≤ v) (hB : ‖B (x : ℂ)‖ * exp (c' * Bessel.besselL x) ≤ Cb)
    (hw : v * exp (-(c' * Bessel.besselL x)) * (1 / cosh (π * x / 2) ^ 2) *
      (2 / 3 * c' * x * lambdaComb c') ≤ Cw) :
    (2 * c' * x / 3) * (|combProfile c' B (c' * x ^ 2 / 3)| * v) ≤ Cb * (Cw / lambdaComb c') := by
  have hlam := Cardy.lambdaComb_pos' hc'
  have hcp := abs_combProfile_le_sech B hc' hx.le
  have hs2 : 0 < 1 / cosh (π * x / 2) ^ 2 := by positivity
  have hB0 : 0 ≤ ‖B (x : ℂ)‖ * exp (c' * Bessel.besselL x) := by positivity
  have hw' : v * exp (-(c' * Bessel.besselL x)) * (1 / cosh (π * x / 2) ^ 2) *
      (2 / 3 * c' * x) ≤ Cw / lambdaComb c' := by
    rw [le_div_iff₀ hlam]; linarith
  have hexp : exp (c' * Bessel.besselL x) * exp (-(c' * Bessel.besselL x)) = 1 := by
    rw [← exp_add]; simp
  calc (2 * c' * x / 3) * (|combProfile c' B (c' * x ^ 2 / 3)| * v)
      ≤ (2 * c' * x / 3) * ((1 / cosh (π * x / 2) ^ 2 * ‖B (x : ℂ)‖) * v) := by
        gcongr
    _ = (‖B (x : ℂ)‖ * exp (c' * Bessel.besselL x)) *
          (v * exp (-(c' * Bessel.besselL x)) * (1 / cosh (π * x / 2) ^ 2) *
            (2 / 3 * c' * x)) := by
        linear_combination ((2 * c' * x / 3) * (1 / cosh (π * x / 2) ^ 2 * ‖B (x : ℂ)‖ * v)) *
          (-hexp)
    _ ≤ Cb * (Cw / lambdaComb c') := by
        exact mul_le_mul hB hw' (by positivity) (hB0.trans hB)

/-- Pointwise integrand bound on the far band: `|B(x)| e^{c'L} ≤ Cb` and `V e^{-c'L} dt ≤ Cf √c' √x dx`
give `(2/3) c' x |h₀| V ≤ 4 Cb Cf √c' · (√x e^{-πx})`. -/
lemma integrand_far_le {c' x Cb Cf : ℝ} {B : ℂ → ℂ} {v : ℝ} (hc' : 0 < c') (hx : 0 < x)
    (hv0 : 0 ≤ v) (hB : ‖B (x : ℂ)‖ * exp (c' * Bessel.besselL x) ≤ Cb)
    (hw : v * exp (-(c' * Bessel.besselL x)) * (2 / 3 * c' * x) ≤ Cf * √c' * √x) :
    (2 * c' * x / 3) * (|combProfile c' B (c' * x ^ 2 / 3)| * v) ≤
      4 * Cb * Cf * √c' * (x ^ (1 / 2 : ℝ) * exp (-π * x)) := by
  have hcp := abs_combProfile_le_exp B hc' hx.le
  have hB0 : 0 ≤ ‖B (x : ℂ)‖ * exp (c' * Bessel.besselL x) := by positivity
  have hexp : exp (c' * Bessel.besselL x) * exp (-(c' * Bessel.besselL x)) = 1 := by
    rw [← exp_add]; simp
  have hsq : √x = x ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow x
  calc (2 * c' * x / 3) * (|combProfile c' B (c' * x ^ 2 / 3)| * v)
      ≤ (2 * c' * x / 3) * ((4 * exp (-π * x) * ‖B (x : ℂ)‖) * v) := by gcongr
    _ = 4 * exp (-π * x) * ((‖B (x : ℂ)‖ * exp (c' * Bessel.besselL x)) *
          (v * exp (-(c' * Bessel.besselL x)) * (2 / 3 * c' * x))) := by
        linear_combination ((2 * c' * x / 3) * (4 * exp (-π * x) * ‖B (x : ℂ)‖ * v)) * (-hexp)
    _ ≤ 4 * exp (-π * x) * (Cb * (Cf * √c' * √x)) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul hB hw (by positivity) (hB0.trans hB))
          (by positivity)
    _ = 4 * Cb * Cf * √c' * (x ^ (1 / 2 : ℝ) * exp (-π * x)) := by rw [← hsq]; ring

lemma exists_N₂ (Θ : ℝ) : ∃ N₂ : ℕ, ∀ N₁ : ℕ, N₂ ≤ N₁ → Θ ≤ phiQuantile ((N₁ + 1 : ℕ) : ℝ) := by
  obtain ⟨N₂, hN₂⟩ := exists_nat_ge (max Θ 0 ^ (3 / 2 : ℝ))
  refine ⟨N₂, fun N₁ hN₁ => ?_⟩
  have hN : (N₂ : ℝ) ≤ N₁ := by exact_mod_cast hN₁
  have hΘ0 : 0 ≤ max Θ 0 := le_max_right _ _
  unfold phiQuantile
  have h1 : max Θ 0 ^ (3 / 2 : ℝ) ≤ (((N₁ + 1 : ℕ) : ℝ) - 1 / 4) := by
    push_cast; linarith
  have h2 := Real.rpow_le_rpow (Real.rpow_nonneg hΘ0 _) h1 (by norm_num : (0 : ℝ) ≤ 2 / 3)
  rw [← Real.rpow_mul hΘ0, show (3 / 2 : ℝ) * (2 / 3) = 1 by norm_num, Real.rpow_one] at h2
  exact (le_max_left Θ 0).trans h2

/-! ### Geometry of the band for fixed `c'` -/

/-- With `κ = (1 + C₁)^{-2/3}`, `κ Φ_{N₁+1} ≥ max(4s, K/log 2)` and `r_{N₁+1} ≤ 1`:
`κ λ N₁^{2/3} ≤ χ_{N₁+1} - ξ_*`, and every `x ≥ χ_{N₁+1}` satisfies `x ≥ ξ_* + 4sλ` and
`K λ/(x - ξ_*) ≤ log 2` (so that `e^{Kλ/(x-ξ_*)} ≤ 2`). -/
lemma band_geometry {c' K s : ℝ} {N₁ : ℕ} (hc' : 0 < c') (hK0 : 0 ≤ K) (hs : 0 < s) (hN1 : 1 ≤ N₁)
    (hr1 : siteRadius c' ((N₁ + 1 : ℕ) : ℝ) ≤ 1)
    (hΦ : max (4 * s) (K / Real.log 2) ≤
      (1 + c1K0) ^ (-(2 / 3 : ℝ)) * phiQuantile ((N₁ + 1 : ℕ) : ℝ)) :
    (1 + c1K0) ^ (-(2 / 3 : ℝ)) * lambdaComb c' * (N₁ : ℝ) ^ (2 / 3 : ℝ) ≤
        chiQuantile c' ((N₁ + 1 : ℕ) : ℝ) - xiStar ∧
      ∀ x : ℝ, chiQuantile c' ((N₁ + 1 : ℕ) : ℝ) ≤ x →
        xiStar + 4 * s * lambdaComb c' ≤ x ∧ K * (lambdaComb c' / (x - xiStar)) ≤ Real.log 2 := by
  have hlam := Cardy.lambdaComb_pos' hc'
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hN1r : (1 : ℝ) ≤ N₁ := by exact_mod_cast hN1
  have hN14s : (1 / 4 : ℝ) < ((N₁ + 1 : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ ((N₁ + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ N₁ + 1)
    linarith
  have hrlow := (siteRadius_le_one_bounds hc' hN14s hr1).1
  unfold siteRadius at hrlow
  have hκ : 0 < (1 + c1K0) ^ (-(2 / 3 : ℝ)) := Real.rpow_pos_of_pos (by linarith [c1K0_pos]) _
  have hΦN : (N₁ : ℝ) ^ (2 / 3 : ℝ) ≤ phiQuantile ((N₁ + 1 : ℕ) : ℝ) := by
    unfold phiQuantile
    apply Real.rpow_le_rpow (by linarith) _ (by norm_num)
    push_cast; linarith
  have hu₀ : (1 + c1K0) ^ (-(2 / 3 : ℝ)) * lambdaComb c' * (N₁ : ℝ) ^ (2 / 3 : ℝ) ≤
      chiQuantile c' ((N₁ + 1 : ℕ) : ℝ) - xiStar := by
    refine le_trans ?_ hrlow
    rw [show (1 + c1K0) ^ (-(2 / 3 : ℝ)) * lambdaComb c' * (N₁ : ℝ) ^ (2 / 3 : ℝ) =
      (1 + c1K0) ^ (-(2 / 3 : ℝ)) * (lambdaComb c' * (N₁ : ℝ) ^ (2 / 3 : ℝ)) by ring]
    gcongr
  refine ⟨hu₀, fun x hx => ?_⟩
  have h4 : 4 * s ≤ (1 + c1K0) ^ (-(2 / 3 : ℝ)) * phiQuantile ((N₁ + 1 : ℕ) : ℝ) :=
    (le_max_left _ _).trans hΦ
  have hκΦ : 0 < (1 + c1K0) ^ (-(2 / 3 : ℝ)) * phiQuantile ((N₁ + 1 : ℕ) : ℝ) := by
    have : 0 < 4 * s := by positivity
    linarith
  have hxξ : (1 + c1K0) ^ (-(2 / 3 : ℝ)) * (lambdaComb c' * phiQuantile ((N₁ + 1 : ℕ) : ℝ)) ≤
      x - xiStar := by linarith
  refine ⟨?_, ?_⟩
  · have h2 := mul_le_mul_of_nonneg_right h4 hlam.le
    nlinarith
  · have hxξ0 : 0 < x - xiStar :=
      lt_of_lt_of_le (by nlinarith [mul_pos hlam hκΦ]) hxξ
    have e1 : lambdaComb c' / (x - xiStar) ≤
        1 / ((1 + c1K0) ^ (-(2 / 3 : ℝ)) * phiQuantile ((N₁ + 1 : ℕ) : ℝ)) := by
      rw [div_le_div_iff₀ hxξ0 hκΦ]
      nlinarith
    have e2 : K ≤ Real.log 2 * ((1 + c1K0) ^ (-(2 / 3 : ℝ)) * phiQuantile ((N₁ + 1 : ℕ) : ℝ)) := by
      have := (le_max_right (4 * s) (K / Real.log 2)).trans hΦ
      rw [div_le_iff₀ hlog2] at this
      linarith
    calc K * (lambdaComb c' / (x - xiStar))
        ≤ K * (1 / ((1 + c1K0) ^ (-(2 / 3 : ℝ)) * phiQuantile ((N₁ + 1 : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_left e1 hK0
      _ = K / ((1 + c1K0) ^ (-(2 / 3 : ℝ)) * phiQuantile ((N₁ + 1 : ℕ) : ℝ)) := by ring
      _ ≤ Real.log 2 := by rw [div_le_iff₀ hκΦ]; linarith

/-- `‖B_D‖ ≤ 2 ‖B_ref‖` from `‖B_D‖ ≤ e^{y} ‖B_ref‖` and `y ≤ log 2`. -/
lemma norm_le_two_of_exp {a b y : ℝ} (hb : 0 ≤ b) (h : a ≤ Real.exp y * b) (hy : y ≤ Real.log 2) :
    a ≤ 2 * b := by
  have : Real.exp y ≤ 2 := by
    calc Real.exp y ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr hy
      _ = 2 := Real.exp_log (by norm_num)
  nlinarith

/-- Pointwise bound of the integrand on the intermediate band, in terms of `(x - ξ_*)^{-p}`. -/
lemma band_pointwise {c' x CR CA W D p lam rn : ℝ} {B : ℂ → ℂ} {v : ℝ} (hc' : 0 < c')
    (hx : 0 < x) (hxξ : 0 < x - xiStar) (hlam : lam = lambdaComb c') (hv0 : 0 ≤ v)
    (hw : v * exp (-(c' * Bessel.besselL x)) * (1 / cosh (π * x / 2) ^ 2) *
      (2 / 3 * c' * x * lambdaComb c') ≤ CA * W)
    (hBn : ‖B (x : ℂ)‖ ≤ 2 * rn)
    (hR : rn * exp (c' * Bessel.besselL x) ≤ CR * (D / (π * (x - xiStar))) ^ p) (hD : 0 ≤ D) :
    (2 * c' * x / 3) * (|combProfile c' B (c' * x ^ 2 / 3)| * v) ≤
      2 * CR * CA * (D / π) ^ p * W / lam * (x - xiStar) ^ (-p) := by
  have hB : ‖B (x : ℂ)‖ * exp (c' * Bessel.besselL x) ≤ 2 * (CR * (D / (π * (x - xiStar))) ^ p) := by
    calc ‖B (x : ℂ)‖ * exp (c' * Bessel.besselL x) ≤ (2 * rn) * exp (c' * Bessel.besselL x) :=
          mul_le_mul_of_nonneg_right hBn (exp_pos _).le
      _ = 2 * (rn * exp (c' * Bessel.besselL x)) := by ring
      _ ≤ 2 * (CR * (D / (π * (x - xiStar))) ^ p) := by gcongr
  have hint := integrand_window_le (B := B) hc' hx hv0 hB hw
  refine hint.trans (le_of_eq ?_)
  have hA : (D / (π * (x - xiStar))) ^ p = (D / π) ^ p * (x - xiStar) ^ (-p) := by
    have hpi := Real.pi_pos
    rw [show D / (π * (x - xiStar)) = (D / π) * (x - xiStar)⁻¹ by field_simp,
      Real.mul_rpow (by positivity) (inv_nonneg.mpr hxξ.le), Real.inv_rpow hxξ.le,
      ← Real.rpow_neg hxξ.le]
  rw [hA, ← hlam]
  ring

/-- The integral over the intermediate band, from the pointwise bound in the variable `x`. -/
lemma band_integral_le {c' a x1 p Kc : ℝ} {B : ℂ → ℂ} {V : ℝ → ℝ → ℝ} (hc' : 0 < c')
    (hξa : xiStar < a) (hab : a ≤ x1) (hp : 1 < p) (hKc0 : 0 ≤ Kc)
    (hfin : ∀ x ∈ Icc a x1, 0 < x ∧ 0 ≤ V c' (c' * x ^ 2 / 3) ∧
      (2 * c' * x / 3) * (|combProfile c' B (c' * x ^ 2 / 3)| * V c' (c' * x ^ 2 / 3)) ≤
        Kc * (x - xiStar) ^ (-p)) :
    (∫ t in Icc (c' * a ^ 2 / 3) (c' * x1 ^ 2 / 3), |combProfile c' B t| * V c' t) ≤
      Kc * ((a - xiStar) ^ (1 - p) / (p - 1)) := by
  rw [integral_Icc_comp_sq hc' (xiStar_pos.trans hξa) hab
    (fun t => |combProfile c' B t| * V c' t)]
  have hcont : ContinuousOn (fun x : ℝ => Kc * (x - xiStar) ^ (-p)) (Icc a x1) := by
    refine continuousOn_const.mul ?_
    refine ContinuousOn.rpow_const (continuousOn_id.sub continuousOn_const) fun x hx => ?_
    left
    have : 0 < x - xiStar := by linarith [hx.1]
    exact this.ne'
  calc ∫ x in Icc a x1, (2 * c' * x / 3) *
        (|combProfile c' B (c' * x ^ 2 / 3)| * V c' (c' * x ^ 2 / 3))
      ≤ ∫ x in Icc a x1, Kc * (x - xiStar) ^ (-p) := by
        refine integral_mono_of_nonneg ?_ hcont.integrableOn_Icc ?_
        · refine (ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall fun x hx => ?_)
          obtain ⟨hxp, hv0, -⟩ := hfin x hx
          positivity
        · exact (ae_restrict_iff' measurableSet_Icc).mpr
            (Eventually.of_forall fun x hx => (hfin x hx).2.2)
    _ = Kc * ∫ x in Icc a x1, (x - xiStar) ^ (-p) := integral_const_mul _ _
    _ ≤ Kc * ((a - xiStar) ^ (1 - p) / (p - 1)) :=
        mul_le_mul_of_nonneg_left (integral_Icc_rpow_neg_le hp hξa hab) hKc0

/-- The integral over the far band, from the pointwise bound in the variable `x`. -/
lemma far_integral_le {c' x1 Cc : ℝ} {B : ℂ → ℂ} {V : ℝ → ℝ → ℝ} (hc' : 0 < c') (hx1 : 0 < x1)
    (hCc : 0 ≤ Cc)
    (hfin : ∀ x ∈ Ici x1, 0 < x ∧ 0 ≤ V c' (c' * x ^ 2 / 3) ∧
      (2 * c' * x / 3) * (|combProfile c' B (c' * x ^ 2 / 3)| * V c' (c' * x ^ 2 / 3)) ≤
        Cc * (x ^ (1 / 2 : ℝ) * exp (-π * x))) :
    (∫ t in Ici (c' * x1 ^ 2 / 3), |combProfile c' B t| * V c' t) ≤ Cc * farConst := by
  rw [integral_Ici_comp_sq hc' hx1 (fun t => |combProfile c' B t| * V c' t)]
  calc ∫ x in Ici x1, (2 * c' * x / 3) *
        (|combProfile c' B (c' * x ^ 2 / 3)| * V c' (c' * x ^ 2 / 3))
      ≤ ∫ x in Ici x1, Cc * (x ^ (1 / 2 : ℝ) * exp (-π * x)) := by
        refine integral_mono_of_nonneg ?_ ((integrableOn_Ici_sqrt_exp hx1).const_mul _) ?_
        · refine (ae_restrict_iff' measurableSet_Ici).mpr (Eventually.of_forall fun x hx => ?_)
          obtain ⟨hxp, hv0, -⟩ := hfin x hx
          positivity
        · exact (ae_restrict_iff' measurableSet_Ici).mpr
            (Eventually.of_forall fun x hx => (hfin x hx).2.2)
    _ = Cc * ∫ x in Ici x1, x ^ (1 / 2 : ℝ) * exp (-π * x) := integral_const_mul _ _
    _ ≤ Cc * farConst := mul_le_mul_of_nonneg_left (integral_Ici_sqrt_exp_le hx1) hCc

/-- **Lemma `T`, intermediate band** (`ut:T`) for an abstract Cardy weight satisfying `CardyWindowBound`. -/
theorem lemma_T_band_of_cardy {V : ℝ → ℝ → ℝ} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hW : CardyWindowBound V 1 r₀)
    (f N : ℕ) (hf : 1 ≤ f) (hfN : f ≤ N) (M E : ℝ) {η₀ : ℝ} (h0 : 0 ≤ η₀) (h1 : η₀ ≤ 1 / 4) :
    ∃ N₂ : ℕ, ∃ C_T : ℝ, 0 ≤ C_T ∧ ∀ N₁ : ℕ, max (4 * f) N₂ ≤ N₁ →
      ∀ᶠ c' in atTop, ∀ σ ε : ℕ → ℝ, (∀ k, f ≤ k → k ≤ N → |σ k| ≤ M) →
        (∀ k, f < k → k ≤ N → 0 ≤ ε k ∧ ε k ≤ E * lambdaComb c') →
        (∫ t in Icc (c' * chiQuantile c' ((N₁ + 1 : ℕ) : ℝ) ^ 2 / 3) (c' * (xiStar + r₀) ^ 2 / 3),
            |combProfile c' (designComb c' f N η₀ σ ε) t| * V c' t) ≤
          FKc 1 f c' * C_T * (N₁ : ℝ) ^ (-((2 / 3 : ℝ) * (2 * (f : ℝ) - 3 / 2))) := by
  obtain ⟨CA, cA, hCA, hWb⟩ := hW
  obtain ⟨CR, hCR, hRb⟩ := refComb_band_bound (f := f) hf (r₀ := r₀) h0 h1
  obtain ⟨K, hK0, hDev⟩ := designComb_norm_le_exp_ref f N hf hfN M E h0 h1
  obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = max (phiQuantile ((N : ℝ) + 2)) M := ⟨_, rfl⟩
  have hs : 0 < s := by
    rw [hs_def]; exact lt_of_lt_of_le (phiQuantile_succ_succ_pos N) (le_max_left _ _)
  rw [← hs_def] at hDev
  have hκ : 0 < (1 + c1K0) ^ (-(2 / 3 : ℝ)) := Real.rpow_pos_of_pos (by linarith [c1K0_pos]) _
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨N₂, hN₂⟩ := exists_N₂ (max (4 * s) (K / Real.log 2) / (1 + c1K0) ^ (-(2 / 3 : ℝ)))
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast hf
  obtain ⟨p, hp_def⟩ : ∃ p : ℝ, p = 2 * ((f : ℝ) - 1 / 4) := ⟨_, rfl⟩
  have hp : 1 < p := by rw [hp_def]; linarith
  have hπ := Real.pi_pos
  have hs2 : 0 < √2 := Real.sqrt_pos.mpr (by norm_num)
  obtain ⟨D, hD_def⟩ : ∃ D : ℝ, D = 4 * √2 * cosh (π * r₀ / 2) := ⟨_, rfl⟩
  have hD : 0 < D := by rw [hD_def]; have := Real.cosh_pos (π * r₀ / 2); positivity
  obtain ⟨C_T, hCT_def⟩ : ∃ C_T : ℝ,
      C_T = 2 * CR * CA * (D / (2 * √2)) ^ p * ((1 + c1K0) ^ (-(2 / 3 : ℝ))) ^ (1 - p) / (p - 1) :=
    ⟨_, rfl⟩
  have hCT0 : 0 ≤ C_T := by
    have : 0 < p - 1 := by linarith
    rw [hCT_def]; positivity
  refine ⟨N₂, C_T, hCT0, fun N₁ hN₁ => ?_⟩
  have h4f : 4 * f ≤ N₁ := (le_max_left _ _).trans hN₁
  have hΘ := hN₂ N₁ ((le_max_right _ _).trans hN₁)
  have hN1 : 1 ≤ N₁ := by omega
  have hN1pos : (0 : ℝ) < N₁ := by exact_mod_cast hN1
  have hN14s : (1 / 4 : ℝ) < ((N₁ + 1 : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ ((N₁ + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ N₁ + 1)
    linarith
  have hΦ : max (4 * s) (K / Real.log 2) ≤
      (1 + c1K0) ^ (-(2 / 3 : ℝ)) * phiQuantile ((N₁ + 1 : ℕ) : ℝ) := by
    rw [div_le_iff₀ hκ] at hΘ; linarith
  filter_upwards [hRb N₁ h4f, hDev, eventually_ge_atTop cA,
    eventually_siteRadius_le_one (((N₁ + 1 : ℕ) : ℝ)), eventually_gt_atTop (0 : ℝ)]
    with c' hRb' hDev' hcA hr1 hc'
  intro σ ε hσ hε
  have hlam := Cardy.lambdaComb_pos' hc'
  have hξ := xiStar_pos
  have hgeo := band_geometry hc' hK0 hs hN1 (hr1 hN14s.le) hΦ
  have hξa : xiStar < chiQuantile c' ((N₁ + 1 : ℕ) : ℝ) := xiStar_lt_chiQuantile hc' hN14s
  have hW0 : 0 < FVc 1 c' := FVc_pos one_pos hc'
  by_cases hab : chiQuantile c' ((N₁ + 1 : ℕ) : ℝ) ≤ xiStar + r₀
  · have hKc0 : 0 ≤ 2 * CR * CA * (D / π) ^ p * FVc 1 c' / lambdaComb c' := by positivity
    have hfin : ∀ x ∈ Icc (chiQuantile c' ((N₁ + 1 : ℕ) : ℝ)) (xiStar + r₀), 0 < x ∧
        0 ≤ V c' (c' * x ^ 2 / 3) ∧
        (2 * c' * x / 3) * (|combProfile c' (designComb c' f N η₀ σ ε) (c' * x ^ 2 / 3)| *
          V c' (c' * x ^ 2 / 3)) ≤
          2 * CR * CA * (D / π) ^ p * FVc 1 c' / lambdaComb c' * (x - xiStar) ^ (-p) := by
      intro x hx
      have hxpos : 0 < x := by linarith [hx.1]
      have hxξ0 : 0 < x - xiStar := by linarith [hx.1]
      obtain ⟨hv0, hw⟩ := hWb c' hcA x (by linarith [hx.1]) hx.2
      obtain ⟨h4s, hlog⟩ := hgeo.2 x hx.1
      have hBn := norm_le_two_of_exp (norm_nonneg _) (hDev' σ ε hσ hε x h4s) hlog
      have hRx := hRb' x hx.1 hx.2
      rw [← hp_def, ← hD_def] at hRx
      exact ⟨hxpos, hv0, band_pointwise hc' hxpos hxξ0 rfl hv0 hw hBn hRx hD.le⟩
    refine (band_integral_le hc' hξa hab hp hKc0 hfin).trans ?_
    have halg := band_final_algebra (p := p) (lam := lambdaComb c')
      (κ := (1 + c1K0) ^ (-(2 / 3 : ℝ))) (W := FVc 1 c') (CR := CR) (CA := CA) (D := D)
      (N1 := (N₁ : ℝ)) (u0 := chiQuantile c' ((N₁ + 1 : ℕ) : ℝ) - xiStar) hp hlam hκ hN1pos
      hW0.le hCR.le hCA.le hD hgeo.1
    have hexp : (2 / 3 : ℝ) * (1 - p) = -((2 / 3 : ℝ) * (2 * (f : ℝ) - 3 / 2)) := by
      rw [hp_def]; ring
    rw [hexp] at halg
    refine halg.trans (le_of_eq ?_)
    unfold FKc
    rw [← hp_def, hCT_def]
  · have hx1 : (c' * (xiStar + r₀) ^ 2 / 3) < c' * chiQuantile c' ((N₁ + 1 : ℕ) : ℝ) ^ 2 / 3 := by
      have h1 : xiStar + r₀ < chiQuantile c' ((N₁ + 1 : ℕ) : ℝ) := not_le.mp hab
      have h0' : 0 < xiStar + r₀ := by linarith
      have : (xiStar + r₀) ^ 2 < chiQuantile c' ((N₁ + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
      have := mul_lt_mul_of_pos_left this hc'
      linarith
    rw [Set.Icc_eq_empty (not_le.mpr hx1), Measure.restrict_empty, integral_zero_measure]
    have := FKc_pos (q := 1) one_pos f hc'
    positivity

/-- **Lemma `T`, far band** (`ut:T`) for an abstract Cardy weight satisfying `CardyFarBound`. -/
theorem lemma_T_far_of_cardy {V : ℝ → ℝ → ℝ} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hF : CardyFarBound V (xiStar + r₀))
    (f N : ℕ) (hf : 1 ≤ f) (hfN : f ≤ N) (M E : ℝ) {η₀ : ℝ} (h0 : 0 ≤ η₀) (h1 : η₀ ≤ 1 / 4) :
    ∃ C_far : ℝ, 0 ≤ C_far ∧ ∀ᶠ c' in atTop, ∀ σ ε : ℕ → ℝ,
      (∀ k, f ≤ k → k ≤ N → |σ k| ≤ M) →
      (∀ k, f < k → k ≤ N → 0 ≤ ε k ∧ ε k ≤ E * lambdaComb c') →
        (∫ t in Ici (c' * (xiStar + r₀) ^ 2 / 3),
            |combProfile c' (designComb c' f N η₀ σ ε) t| * V c' t) ≤ C_far * √c' := by
  obtain ⟨CF, cF, hCF, hFb⟩ := hF
  obtain ⟨Cr, hCr, hrfar⟩ := refComb_far_bound hf h0 h1 hr₀
  obtain ⟨K, hK0, hDev⟩ := designComb_norm_le_exp_ref f N hf hfN M E h0 h1
  obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = max (phiQuantile ((N : ℝ) + 2)) M := ⟨_, rfl⟩
  have hs : 0 < s := by
    rw [hs_def]; exact lt_of_lt_of_le (phiQuantile_succ_succ_pos N) (le_max_left _ _)
  rw [← hs_def] at hDev
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hξ := xiStar_pos
  have hx0 : 0 < xiStar + r₀ := by linarith
  refine ⟨4 * (2 * Cr) * CF * farConst, ?_, ?_⟩
  · have := farConst_nonneg
    positivity
  have hlam_ev : ∀ᶠ c' in atTop, lambdaComb c' ≤ r₀ / (4 * s) ∧
      K * lambdaComb c' ≤ r₀ * Real.log 2 := by
    have e1 := tendsto_lambdaComb_atTop.eventually
      (eventually_le_nhds (show (0 : ℝ) < r₀ / (4 * s) by positivity))
    have h2 := tendsto_lambdaComb_atTop.const_mul K
    rw [mul_zero] at h2
    exact e1.and (h2.eventually (eventually_le_nhds (show (0 : ℝ) < r₀ * Real.log 2 by positivity)))
  filter_upwards [hDev, eventually_ge_atTop cF, eventually_gt_atTop (0 : ℝ), hlam_ev, hrfar]
    with c' hDev' hcF hc' hlam hrfar'
  intro σ ε hσ hε
  have hlampos := Cardy.lambdaComb_pos' hc'
  have hfin : ∀ x ∈ Ici (xiStar + r₀), 0 < x ∧ 0 ≤ V c' (c' * x ^ 2 / 3) ∧
      (2 * c' * x / 3) * (|combProfile c' (designComb c' f N η₀ σ ε) (c' * x ^ 2 / 3)| *
        V c' (c' * x ^ 2 / 3)) ≤
        4 * (2 * Cr) * CF * √c' * (x ^ (1 / 2 : ℝ) * exp (-π * x)) := by
    intro x hx
    have hx' : xiStar + r₀ ≤ x := hx
    have hxpos : 0 < x := by linarith
    have hxξ : r₀ ≤ x - xiStar := by linarith
    have hxξ0 : 0 < x - xiStar := by linarith
    obtain ⟨hv0, hw⟩ := hFb c' hcF x hx'
    refine ⟨hxpos, hv0, ?_⟩
    have h4s : xiStar + 4 * s * lambdaComb c' ≤ x := by
      have : 4 * s * lambdaComb c' ≤ r₀ := by
        have := hlam.1
        rw [le_div_iff₀ (by positivity)] at this
        linarith
      linarith
    have hlog : K * (lambdaComb c' / (x - xiStar)) ≤ Real.log 2 := by
      calc K * (lambdaComb c' / (x - xiStar)) = (K * lambdaComb c') / (x - xiStar) := by ring
        _ ≤ (r₀ * Real.log 2) / (x - xiStar) := div_le_div_of_nonneg_right hlam.2 hxξ0.le
        _ ≤ (r₀ * Real.log 2) / r₀ :=
            div_le_div_of_nonneg_left (by positivity) hr₀ hxξ
        _ = Real.log 2 := by field_simp
    have hBn := norm_le_two_of_exp (norm_nonneg _) (hDev' σ ε hσ hε x h4s) hlog
    have hB : ‖designComb c' f N η₀ σ ε (x : ℂ)‖ * exp (c' * Bessel.besselL x) ≤ 2 * Cr :=
      calc ‖designComb c' f N η₀ σ ε (x : ℂ)‖ * exp (c' * Bessel.besselL x)
          ≤ (2 * ‖refComb c' f η₀ (x : ℂ)‖) * exp (c' * Bessel.besselL x) :=
            mul_le_mul_of_nonneg_right hBn (exp_pos _).le
        _ = 2 * (‖refComb c' f η₀ (x : ℂ)‖ * exp (c' * Bessel.besselL x)) := by ring
        _ ≤ 2 * Cr := by have := hrfar' x hx'; linarith
    exact integrand_far_le (B := designComb c' f N η₀ σ ε) hc' hxpos hv0 hB hw
  have := far_integral_le (B := designComb c' f N η₀ σ ε) (V := V) hc' hx0
    (by positivity : (0 : ℝ) ≤ 4 * (2 * Cr) * CF * √c') hfin
  refine this.trans (le_of_eq ?_)
  ring

/-- **Lemma `T`** (`ut:T`) for an abstract Cardy weight `V` with the window and far-band bounds of
Lemma `A_V` (`CardyWindowBound`, `CardyFarBound`).  Quantifiers as in the paper: for the compact family
`|σ_k| ≤ M`, `0 ≤ ε'_k ≤ E λ`, there are `N₂, C_T, C_far`, independent of `N₁` and `c'`, such that for every
`N₁ ≥ max(4f, N₂)` and `c ≥ c₀(𝒦, N₁)`, uniformly on the family, the intermediate band
`[c'χ_{N₁+1}²/3, c'(ξ_*+r₀)²/3]` (in `t`) carries `∫ |h₀| V dt ≤ FK_c^{(f)} C_T N₁^{-(2/3)(2f-3/2)}`
and the far band `t ≥ c'(ξ_*+r₀)²/3` carries `∫ |h₀| V dt ≤ C_far √c'`. -/
theorem lemma_T_of_cardy {V : ℝ → ℝ → ℝ} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hW : CardyWindowBound V 1 r₀) (hF : CardyFarBound V (xiStar + r₀))
    (f N : ℕ) (hf : 1 ≤ f) (hfN : f ≤ N) (M E : ℝ) {η₀ : ℝ} (h0 : 0 ≤ η₀) (h1 : η₀ ≤ 1 / 4) :
    ∃ N₂ : ℕ, ∃ C_T C_far : ℝ, 0 ≤ C_T ∧ 0 ≤ C_far ∧ ∀ N₁ : ℕ, max (4 * f) N₂ ≤ N₁ →
      ∀ᶠ c' in atTop, ∀ σ ε : ℕ → ℝ, (∀ k, f ≤ k → k ≤ N → |σ k| ≤ M) →
        (∀ k, f < k → k ≤ N → 0 ≤ ε k ∧ ε k ≤ E * lambdaComb c') →
        (∫ t in Icc (c' * chiQuantile c' ((N₁ + 1 : ℕ) : ℝ) ^ 2 / 3) (c' * (xiStar + r₀) ^ 2 / 3),
            |combProfile c' (designComb c' f N η₀ σ ε) t| * V c' t) ≤
          FKc 1 f c' * C_T * (N₁ : ℝ) ^ (-((2 / 3 : ℝ) * (2 * (f : ℝ) - 3 / 2))) ∧
        (∫ t in Ici (c' * (xiStar + r₀) ^ 2 / 3),
            |combProfile c' (designComb c' f N η₀ σ ε) t| * V c' t) ≤ C_far * √c' := by
  obtain ⟨N₂, C_T, hCT, hband⟩ := lemma_T_band_of_cardy hr₀ hW f N hf hfN M E h0 h1
  obtain ⟨C_far, hCf, hfar⟩ := lemma_T_far_of_cardy hr₀ hF f N hf hfN M E h0 h1
  refine ⟨N₂, C_T, C_far, hCT, hCf, fun N₁ hN₁ => ?_⟩
  filter_upwards [hband N₁ hN₁, hfar] with c' hb hf' σ ε hσ hε
  exact ⟨hb σ ε hσ hε, hf' σ ε hσ hε⟩

/-- **Lemma `T`** (`ut:T`), Virasoro (`w = 1`, `Q = (1-q)²`, `q = 1`): the Cardy weight is
`V = virasoroProblem.cardyV (c'/12)`, `h₀ = sech²(πb/2) B_D^{(f)}` (`combProfile`), `r₀ > 0`
(`r₀ = 3/10` in the paper).  For the compact family `|σ_k| ≤ M`, `0 ≤ ε'_k ≤ E λ` of finite
modifications `B_D^{(f)} = designComb c' f N η₀ σ ε` of `B_ref^{(f)}` (`ut:P`(b)), there are `N₂`, `C_T`,
`C_far` independent of `N₁` and `c'` such that for every `N₁ ≥ max(4f, N₂)` and all large `c'`, uniformly
on the family,
`∫_{χ_{N₁+1} ≤ x ≤ ξ_*+r₀} |h₀| V dt ≤ FK_c^{(f)} C_T N₁^{-(2/3)(2f-3/2)}` and
`∫_{x ≥ ξ_*+r₀} |h₀| V dt ≤ C_far √c'` (`t = c'x²/3`; `FK_c^{(f)} = FKc 1 f c'`). -/
theorem lemma_T {r₀ : ℝ} (hr₀ : 0 < r₀)
    (f N : ℕ) (hf : 1 ≤ f) (hfN : f ≤ N) (M E : ℝ) {η₀ : ℝ} (h0 : 0 ≤ η₀) (h1 : η₀ ≤ 1 / 4) :
    ∃ N₂ : ℕ, ∃ C_T C_far : ℝ, 0 ≤ C_T ∧ 0 ≤ C_far ∧ ∀ N₁ : ℕ, max (4 * f) N₂ ≤ N₁ →
      ∀ᶠ c' in atTop, ∀ σ ε : ℕ → ℝ, (∀ k, f ≤ k → k ≤ N → |σ k| ≤ M) →
        (∀ k, f < k → k ≤ N → 0 ≤ ε k ∧ ε k ≤ E * lambdaComb c') →
        (∫ t in Icc (c' * chiQuantile c' ((N₁ + 1 : ℕ) : ℝ) ^ 2 / 3) (c' * (xiStar + r₀) ^ 2 / 3),
            |combProfile c' (designComb c' f N η₀ σ ε) t| *
              Crossing.virasoroProblem.cardyV (c' / 12) t) ≤
          FKc 1 f c' * C_T * (N₁ : ℝ) ^ (-((2 / 3 : ℝ) * (2 * (f : ℝ) - 3 / 2))) ∧
        (∫ t in Ici (c' * (xiStar + r₀) ^ 2 / 3),
            |combProfile c' (designComb c' f N η₀ σ ε) t| *
              Crossing.virasoroProblem.cardyV (c' / 12) t) ≤ C_far * √c' :=
  lemma_T_of_cardy (V := fun c' t => Crossing.virasoroProblem.cardyV (c' / 12) t) hr₀
    (cardyWindowBound_virasoro hr₀) (cardyFarBound_virasoro (by linarith [xiStar_pos])) f N hf hfN
    M E h0 h1

/-- **Lemma `T` for the `f = 1` finite modifications at fixed sites** (`η₀ = 1/4`, arbitrary offsets `σ`,
`ε = designWidth1 c' η_*`, `M` a bound for the offsets `σ_1, …, σ_N`; the exponent is `-1/3`).
`lemma_T_design1` is the case `σ = designSigma1 d`. -/
theorem lemma_T_sig1 {r₀ : ℝ} (hr₀ : 0 < r₀) (N : ℕ) (hN : 1 ≤ N) {etaStar : ℝ} (hη0 : 0 ≤ etaStar)
    (hη1 : etaStar ≤ 1 / 4) (σ : ℕ → ℝ) (M : ℝ) (hM : ∀ k, 1 ≤ k → k ≤ N → |σ k| ≤ M) :
    ∃ N₂ : ℕ, ∃ C_T C_far : ℝ, 0 ≤ C_T ∧ 0 ≤ C_far ∧ ∀ N₁ : ℕ, max 4 N₂ ≤ N₁ →
      ∀ᶠ c' in atTop,
        (∫ t in Icc (c' * chiQuantile c' ((N₁ + 1 : ℕ) : ℝ) ^ 2 / 3) (c' * (xiStar + r₀) ^ 2 / 3),
            |combProfile c' (designComb c' 1 N (1 / 4) σ (designWidth1 c' etaStar)) t| *
              Crossing.virasoroProblem.cardyV (c' / 12) t) ≤
          FKc 1 1 c' * C_T * (N₁ : ℝ) ^ (-(1 / 3 : ℝ)) ∧
        (∫ t in Ici (c' * (xiStar + r₀) ^ 2 / 3),
            |combProfile c' (designComb c' 1 N (1 / 4) σ (designWidth1 c' etaStar)) t| *
              Crossing.virasoroProblem.cardyV (c' / 12) t) ≤ C_far * √c' := by
  obtain ⟨Cg, hCg, h_ev⟩ := siteGap_eventually_le
  obtain ⟨N₂, C_T, C_far, hCT, hCf, h⟩ := lemma_T hr₀ 1 N le_rfl hN M Cg
    (by norm_num : (0 : ℝ) ≤ 1 / 4) le_rfl
  refine ⟨N₂, C_T, C_far, hCT, hCf, fun N₁ hN₁ => ?_⟩
  have hexp : -((2 / 3 : ℝ) * (2 * ((1 : ℕ) : ℝ) - 3 / 2)) = -(1 / 3 : ℝ) := by norm_num
  filter_upwards [h N₁ (by simpa using hN₁), h_ev, eventually_gt_atTop (0 : ℝ)]
    with c' hc' ⟨hgap_k, hgap_1_bd, hcd1_bd, _⟩ hpos
  have key := hc' σ (designWidth1 c' etaStar) (fun k hk hkN => hM k hk hkN)
    (fun k hk hkN => ⟨mul_nonneg hη0 (siteGap_nonneg hpos (by omega)), by
      have hgk := (hgap_k k (by omega)).trans (hgap_1_bd.trans hcd1_bd)
      unfold designWidth1
      calc etaStar * siteGap c' k ≤ 1 * (Cg * lambdaComb c') :=
            mul_le_mul (hη1.trans (by norm_num)) hgk (siteGap_nonneg hpos (by omega)) (by norm_num)
        _ = Cg * lambdaComb c' := one_mul _⟩)
  rw [hexp] at key
  exact key

/-- **Lemma `T` for the designs `D(N, η_*, d)`** (`f = 1`, `η₀ = 1/4`, `σ = designSigma1 d`,
`ε = designWidth1 c' η_*`, `M` a bound for the offsets `σ_1, …, σ_N`; the exponent is `-1/3`). -/
theorem lemma_T_design1 {r₀ : ℝ} (hr₀ : 0 < r₀) (N : ℕ) (hN : 1 ≤ N) {etaStar : ℝ} (hη0 : 0 ≤ etaStar)
    (hη1 : etaStar ≤ 1 / 4) (d M : ℝ) (hM : ∀ k, 1 ≤ k → k ≤ N → |designSigma1 d k| ≤ M) :
    ∃ N₂ : ℕ, ∃ C_T C_far : ℝ, 0 ≤ C_T ∧ 0 ≤ C_far ∧ ∀ N₁ : ℕ, max 4 N₂ ≤ N₁ →
      ∀ᶠ c' in atTop,
        (∫ t in Icc (c' * chiQuantile c' ((N₁ + 1 : ℕ) : ℝ) ^ 2 / 3) (c' * (xiStar + r₀) ^ 2 / 3),
            |combProfile c' (designComb c' 1 N (1 / 4) (designSigma1 d) (designWidth1 c' etaStar)) t| *
              Crossing.virasoroProblem.cardyV (c' / 12) t) ≤
          FKc 1 1 c' * C_T * (N₁ : ℝ) ^ (-(1 / 3 : ℝ)) ∧
        (∫ t in Ici (c' * (xiStar + r₀) ^ 2 / 3),
            |combProfile c' (designComb c' 1 N (1 / 4) (designSigma1 d) (designWidth1 c' etaStar)) t| *
              Crossing.virasoroProblem.cardyV (c' / 12) t) ≤ C_far * √c' :=
  lemma_T_sig1 hr₀ N hN hη0 hη1 (designSigma1 d) M hM

/-- **Non-vacuity of the hypotheses of `lemma_T`**: the window and far-band properties hold for the
Virasoro Cardy kernel, and the compact family of finite modifications is nonempty (it contains the zero
modification `σ = 0`, `ε = 0`, for every `c' > 0`). -/
theorem lemma_T_hypotheses_nonvacuous {r₀ : ℝ} (hr₀ : 0 < r₀) (f N : ℕ) {M E : ℝ} (hM : 0 ≤ M)
    (hE : 0 ≤ E) {c' : ℝ} (hc' : 0 < c') :
    CardyWindowBound (fun c' t => Crossing.virasoroProblem.cardyV (c' / 12) t) 1 r₀ ∧
      CardyFarBound (fun c' t => Crossing.virasoroProblem.cardyV (c' / 12) t) (xiStar + r₀) ∧
      ∃ σ ε : ℕ → ℝ, (∀ k, f ≤ k → k ≤ N → |σ k| ≤ M) ∧
        (∀ k, f < k → k ≤ N → 0 ≤ ε k ∧ ε k ≤ E * lambdaComb c') :=
  ⟨cardyWindowBound_virasoro hr₀, cardyFarBound_virasoro (by linarith [xiStar_pos]),
    design_family_nonempty f N hM hE hc'⟩

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.Tail.lemma_T_hypotheses_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_T_hypotheses_nonvacuous

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.Tail.lemma_T_band_of_cardy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_T_band_of_cardy

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.Tail.lemma_T_far_of_cardy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_T_far_of_cardy

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.Tail.lemma_T_of_cardy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_T_of_cardy

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.Tail.lemma_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_T

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.Tail.lemma_T_sig1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_T_sig1

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.Tail.lemma_T_design1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_T_design1

end FormalResearch.ModularBootstrap.Upper.Window.Tail
