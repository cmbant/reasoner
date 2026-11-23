module

public import FormalResearch.SignUncertainty.ShellGapLaplace
public import FormalResearch.SignUncertainty.MellinStrip

/-!
# The Mellin reflection gives `∫ h ρ₀ W ≥ 0` (proof of `thm:ce-shell-gap`, Laplace constraint)

For `p ∈ 𝒜_c^{+1}`, `q ∈ 𝒜_c^{-1}` with `p + q ≥ 0` (that is, `ĥ ≥ 0`) and `h = p - q`, the weighted
integral `∫ h ρ₀ W` is nonnegative for `y > 0` and `c` large:

* `integral_laplaceWeight_eq`: `∫ f ρ₀ W = e^{-c Re ℋ(ζ)} K(c-x) ∫ f Δ^{c-x-1}`, `x = cζ_c`, `K(s) = (2π)^s/Γ(s)`
  (the Gamma form of the weight);
* `mellinK_reflect`: the Mellin reflection `K(c-x) M_f(c-x) = ε K(x) M_f(x)` on the Weber range
  (`mellinStrip_reflection_of_re_lt`);
* `weighted_nonneg`: `∫ (p-q) ρ₀ W = e^{-cℋ} K(x) ∫ (p+q) Δ^{x-1} ≥ 0`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-- `K(s) = (2π)^s / Γ(s)`. -/
noncomputable def mellinK (s : ℝ) : ℝ := (2 * Real.pi) ^ s / Real.Gamma s

lemma mellinK_pos {s : ℝ} (hs : 0 < s) : 0 < mellinK s := by
  unfold mellinK
  have := Real.Gamma_pos_of_pos hs
  positivity

lemma mellinStrip_real (f : ℝ → ℝ) {s : ℝ} (hs : 0 < s) :
    mellinStrip f (s : ℂ) =
      ((mellinK s * ∫ Δ in Ioi (0 : ℝ), f Δ * Δ ^ (s - 1) : ℝ) : ℂ) := by
  have h2π : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hint : mellinRaw f (s : ℂ) = ((∫ Δ in Ioi (0 : ℝ), f Δ * Δ ^ (s - 1) : ℝ) : ℂ) := by
    unfold mellinRaw
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun Δ hΔ => ?_
    rw [show ((s : ℂ) - 1) = ((s - 1 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (le_of_lt hΔ)]
    push_cast; ring
  have e1 : (((2 * Real.pi : ℝ) ^ s : ℝ) : ℂ) = ((2 * Real.pi : ℝ) : ℂ) ^ (s : ℂ) :=
    Complex.ofReal_cpow h2π s
  have e2 : ((Real.Gamma s : ℝ) : ℂ) = Complex.Gamma (s : ℂ) := (Complex.Gamma_ofReal s).symm
  have e3 : ((mellinK s : ℝ) : ℂ) = (((2 * Real.pi : ℝ) ^ s : ℝ) : ℂ) / ((Real.Gamma s : ℝ) : ℂ) := by
    unfold mellinK; exact Complex.ofReal_div _ _
  unfold mellinStrip
  rw [hint, Complex.ofReal_mul (mellinK s), e3, e1, e2]

lemma mellinK_reflect {c ε : ℝ} (hc : 3 / 2 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < c / 2 - 1 / 4) :
    mellinK (c - x) * ∫ Δ in Ioi (0 : ℝ), f Δ * Δ ^ (c - x - 1) =
      ε * (mellinK x * ∫ Δ in Ioi (0 : ℝ), f Δ * Δ ^ (x - 1)) := by
  have h := mellinStrip_reflection_of_re_lt hc hf (z := (x : ℂ)) (by simpa using hx0)
    (by simpa using hx1)
  rw [show (c : ℂ) - (x : ℂ) = ((c - x : ℝ) : ℂ) by push_cast; ring,
    mellinStrip_real f (by linarith : 0 < c - x), mellinStrip_real f hx0] at h
  have h' : ((mellinK (c - x) * ∫ Δ in Ioi (0 : ℝ), f Δ * Δ ^ (c - x - 1) : ℝ) : ℂ) =
      ((ε * (mellinK x * ∫ Δ in Ioi (0 : ℝ), f Δ * Δ ^ (x - 1)) : ℝ) : ℂ) := by
    rw [h]; push_cast; ring
  exact_mod_cast h'

lemma integral_laplaceWeight_eq {c y : ℝ} (hc : 0 < c) (hy : 0 ≤ y) (hζ : laplaceZeta c y < 1)
    (f : ℝ → ℝ) :
    ∫ Δ in Ioi (0 : ℝ), f Δ * hankelRho0 c Δ * laplaceWeight c y Δ =
      Real.exp (-c * (stripH (laplaceZeta c y : ℂ)).re) *
        (mellinK (c - c * laplaceZeta c y) *
          ∫ Δ in Ioi (0 : ℝ), f Δ * Δ ^ (c - c * laplaceZeta c y - 1)) := by
  set x : ℝ := c * laplaceZeta c y with hx
  set E : ℝ := Real.exp (-c * (stripH (laplaceZeta c y : ℂ)).re) with hE
  have hx0 : 0 ≤ x := mul_nonneg hc.le (laplaceZeta_nonneg hc hy)
  have hcx : 0 < c - x := by
    have : x < c := by rw [hx]; nlinarith
    linarith
  rw [← integral_const_mul, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun Δ hΔ => ?_
  have hΔ0 : 0 < Δ := hΔ
  have gf := laplaceWeight_gamma_form hc hy hζ hΔ0
  have hc1 : c * (1 - laplaceZeta c y) = c - x := by rw [hx]; ring
  rw [hc1] at gf
  rw [gf]
  have hGc : 0 < Real.Gamma c := Real.Gamma_pos_of_pos hc
  have hGx : 0 < Real.Gamma (c - x) := Real.Gamma_pos_of_pos hcx
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  have h1 : (2 * Real.pi) ^ (c - x) = (2 * Real.pi) ^ c * (2 * Real.pi) ^ (-x) := by
    rw [← Real.rpow_add h2π]; ring_nf
  have h2 : Δ ^ (c - x - 1) = Δ ^ (c - 1) * Δ ^ (-x) := by
    rw [← Real.rpow_add hΔ0]; ring_nf
  unfold hankelRho0 mellinK
  rw [h1, h2]
  field_simp
  rw [hE, hx]
  ring_nf

theorem weighted_nonneg {c y : ℝ} (hc : 56 ≤ c) (hy : 0 < y) (hζ : laplaceZeta c y ≤ 1 / 4)
    {p q : ℝ → ℝ} (hp : IsHankelEigenfn c 1 p) (hq : IsHankelEigenfn c (-1) q)
    (hpq : ∀ Δ : ℝ, 0 ≤ Δ → 0 ≤ p Δ + q Δ) :
    0 ≤ ∫ Δ in Ioi (0 : ℝ), (p Δ - q Δ) * hankelRho0 c Δ * laplaceWeight c y Δ := by
  have hc0 : 0 < c := by linarith
  have hy0 : 0 ≤ y := hy.le
  have hζ1 : laplaceZeta c y < 1 := by linarith
  set x : ℝ := c * laplaceZeta c y with hx
  have hζpos : 0 < laplaceZeta c y := by
    unfold laplaceZeta
    exact mul_pos (div_pos hy laplaceCs_pos) (radialEps_pos hc0)
  have hx0 : 0 < x := mul_pos hc0 hζpos
  have hx1 : x < c / 2 - 1 / 4 := by
    have := mul_le_mul_of_nonneg_left hζ hc0.le
    rw [hx]; nlinarith
  have hxc : x ≤ c := by linarith
  set E : ℝ := Real.exp (-c * (stripH (laplaceZeta c y : ℂ)).re) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hpi : IntegrableOn (fun Δ => p Δ * hankelRho0 c Δ * laplaceWeight c y Δ) (Ioi 0) :=
    (integrableOn_weighted hc hy0 hζ hp (Or.inl rfl)).congr_fun (fun Δ _ => by ring)
      measurableSet_Ioi
  have hqi : IntegrableOn (fun Δ => q Δ * hankelRho0 c Δ * laplaceWeight c y Δ) (Ioi 0) :=
    (integrableOn_weighted hc hy0 hζ hq (Or.inr rfl)).congr_fun (fun Δ _ => by ring)
      measurableSet_Ioi
  have hsplit : ∫ Δ in Ioi (0 : ℝ), (p Δ - q Δ) * hankelRho0 c Δ * laplaceWeight c y Δ =
      (∫ Δ in Ioi (0 : ℝ), p Δ * hankelRho0 c Δ * laplaceWeight c y Δ) -
        ∫ Δ in Ioi (0 : ℝ), q Δ * hankelRho0 c Δ * laplaceWeight c y Δ := by
    rw [← integral_sub hpi hqi]
    refine integral_congr_ae (Eventually.of_forall fun Δ => ?_)
    simp only; ring
  rw [hsplit, integral_laplaceWeight_eq hc0 hy0 hζ1 p, integral_laplaceWeight_eq hc0 hy0 hζ1 q]
  rw [← hx]
  have r1 := mellinK_reflect (by linarith : 3 / 2 < c) hp hx0 hx1
  have r2 := mellinK_reflect (by linarith : 3 / 2 < c) hq hx0 hx1
  -- integrability of the unweighted Mellin integrands
  have hint : ∀ {ε : ℝ} {f : ℝ → ℝ}, IsHankelEigenfn c ε f →
      IntegrableOn (fun Δ => f Δ * Δ ^ (x - 1)) (Ioi 0) := by
    intro ε f hf
    have h := integrableOn_abs_mul_rpow_eigen hc0 hf hx0 hxc
    refine Integrable.mono' h ?_ ?_
    · exact (((hf.cont.mono Ioi_subset_Ici_self).mul
        (ContinuousOn.rpow_const continuousOn_id fun w hw => Or.inl (ne_of_gt hw))).aestronglyMeasurable
        measurableSet_Ioi)
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun Δ hΔ => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (le_of_lt hΔ) _)]
  have hsum : (∫ Δ in Ioi (0 : ℝ), p Δ * Δ ^ (x - 1)) + ∫ Δ in Ioi (0 : ℝ), q Δ * Δ ^ (x - 1) =
      ∫ Δ in Ioi (0 : ℝ), (p Δ + q Δ) * Δ ^ (x - 1) := by
    rw [← integral_add (hint hp) (hint hq)]
    refine integral_congr_ae (Eventually.of_forall fun Δ => ?_)
    simp only; ring
  have hnn : 0 ≤ ∫ Δ in Ioi (0 : ℝ), (p Δ + q Δ) * Δ ^ (x - 1) :=
    setIntegral_nonneg measurableSet_Ioi fun Δ hΔ =>
      mul_nonneg (hpq Δ (le_of_lt hΔ)) (Real.rpow_nonneg (le_of_lt hΔ) _)
  have hK := mellinK_pos hx0
  calc 0 ≤ E * (mellinK x * ((∫ Δ in Ioi (0 : ℝ), p Δ * Δ ^ (x - 1)) +
          ∫ Δ in Ioi (0 : ℝ), q Δ * Δ ^ (x - 1))) := by
        rw [hsum]; positivity
    _ = _ := by
        rw [show c - x - 1 = c - x - 1 from rfl] at *
        have r1' : mellinK (c - x) * ∫ Δ in Ioi (0 : ℝ), p Δ * Δ ^ (c - x - 1) =
            mellinK x * ∫ Δ in Ioi (0 : ℝ), p Δ * Δ ^ (x - 1) := by
          rw [r1]; ring
        have r2' : mellinK (c - x) * ∫ Δ in Ioi (0 : ℝ), q Δ * Δ ^ (c - x - 1) =
            -(mellinK x * ∫ Δ in Ioi (0 : ℝ), q Δ * Δ ^ (x - 1)) := by
          rw [r2]; ring
        rw [r1', r2']; ring

end FormalResearch.SignUncertainty
