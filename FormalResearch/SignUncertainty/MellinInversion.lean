module

public import FormalResearch.SignUncertainty.MellinDecay
public import FormalResearch.SignUncertainty.MellinMajorant
public import Mathlib.Analysis.Complex.Hadamard
public import Mathlib.Analysis.MellinInversion

/-!
# Mellin inversion for `f ∈ 𝒜_c^ε` (`lem:radial-compactness`, Step 1)

For `c > 3/2`, `ε = ±1`, `f ∈ 𝒜_c^ε`, `0 < σ` and `σ + 1 < c`, the vertical line `Re z = σ` carries an integrable
raw Mellin transform and, for every `Δ > 0`,
`f(Δ) = (1/2π) ∫ Δ^{-(σ+iy)} mellinRaw f (σ+iy) dy` (`mellin_inversion_f`).

Proof: Hadamard's three-lines theorem (Mathlib) for `G_t(z) = mellinRaw f (z + it) e^{z²}` on `x₁ ≤ Re z ≤ c`,
with the edge bounds `|mellinRaw| ≤ J` at `Re z = c` and `(1+|y|)^{-(c-2x₁)}` at `Re z = x₁`
(`MellinDecay`), gives `|mellinRaw f (σ+it)| ≲ (1+|t|)^{-(c-2x₁)(c-σ)/(c-x₁)}`, which is integrable once
`σ + 1 < c` and `x₁` is small; then Mathlib's `mellinInv_mellin_eq` applies.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex.HadamardThreeLines
open scoped Real

namespace FormalResearch.SignUncertainty

/-- Power-law decay of `mellinRaw f` on `Re z = x`, `x₁ ≤ x ≤ c`, by three lines. -/
theorem exists_norm_mellinRaw_interp {c ε : ℝ} (hc : 3 / 2 < c) {f : ℝ → ℝ}
    (hf : IsHankelEigenfn c ε f) (hε : ε = 1 ∨ ε = -1) {x1 : ℝ} (hx1 : 0 < x1)
    (hx1c : 2 * x1 < c) {x : ℝ} (hx : x1 ≤ x) (hxc : x ≤ c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖mellinRaw f ((x : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        C * (1 + |t|) ^ (-((c - 2 * x1) * ((c - x) / (c - x1)))) := by
  have hc0 : 0 < c := by linarith
  obtain ⟨CL, hCL0, hCL⟩ := exists_norm_mellinRaw_left hc hf hε hx1 hx1c
  obtain ⟨J, hJ0, hJ⟩ := exists_norm_mellinRaw_le hc0 hf hx1 (by linarith)
  set a : ℝ := c - 2 * x1 with ha
  have ha0 : 0 < a := by linarith
  have hx1c' : x1 < c := by linarith
  set Cg : ℝ := CL * Real.exp (x1 ^ 2) * Real.exp (a ^ 2 / 4) with hCg
  have hCg0 : 0 ≤ Cg := by positivity
  set Cr : ℝ := J * Real.exp (c ^ 2) with hCr
  have hCr0 : 0 ≤ Cr := by positivity
  set s : ℝ := (x - x1) / (c - x1) with hs
  have hcx1 : 0 < c - x1 := by linarith
  have hs1 : 1 - s = (c - x) / (c - x1) := by rw [hs]; field_simp; ring
  have hs0 : 0 ≤ 1 - s := by rw [hs1]; exact div_nonneg (by linarith) hcx1.le
  refine ⟨Real.exp (-(x ^ 2)) * Cg ^ (1 - s) * Cr ^ s, by positivity, fun t => ?_⟩
  set G : ℂ → ℂ := fun z => mellinRaw f (z + (t : ℂ) * Complex.I) * Complex.exp (z ^ 2) with hG
  have hnormexp : ∀ z : ℂ, ‖Complex.exp (z ^ 2)‖ = Real.exp (z.re ^ 2 - z.im ^ 2) := by
    intro z; rw [Complex.norm_exp]; congr 1; simp [sq]
  have hshift_re : ∀ z : ℂ, (z + (t : ℂ) * Complex.I).re = z.re := by intro z; simp
  -- bounded above on the closed strip
  have hB : BddAbove ((norm ∘ G) '' verticalClosedStrip x1 c) := by
    refine ⟨J * Real.exp (c ^ 2), ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have hz' : x1 ≤ z.re ∧ z.re ≤ c := hz
    simp only [Function.comp, hG, norm_mul, hnormexp]
    have h1 := hJ (z + (t : ℂ) * Complex.I) (by rw [hshift_re]; exact hz'.1)
      (by rw [hshift_re]; exact hz'.2)
    have h2 : Real.exp (z.re ^ 2 - z.im ^ 2) ≤ Real.exp (c ^ 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg z.im, hz'.1, hz'.2]
    exact mul_le_mul h1 h2 (Real.exp_pos _).le hJ0
  -- differentiable / continuous
  have hd : DiffContOnCl ℂ G (verticalStrip x1 c) := by
    constructor
    · intro z hz
      have hz' : x1 < z.re ∧ z.re < c := hz
      have hmem : z + (t : ℂ) * Complex.I ∈ {w : ℂ | 0 < w.re ∧ w.re < c} := by
        simp only [Set.mem_ofPred_eq, hshift_re]; exact ⟨by linarith [hz'.1], hz'.2⟩
      have h1 : DifferentiableWithinAt ℂ (mellinRaw f) {w : ℂ | 0 < w.re ∧ w.re < c}
          (z + (t : ℂ) * Complex.I) := differentiableOn_mellinRaw hc0 hf _ hmem
      have hopen : {w : ℂ | 0 < w.re ∧ w.re < c} ∈ 𝓝 (z + (t : ℂ) * Complex.I) := by
        refine IsOpen.mem_nhds ?_ hmem
        exact (isOpen_lt continuous_const Complex.continuous_re).inter
          (isOpen_lt Complex.continuous_re continuous_const)
      have h2 : DifferentiableAt ℂ (mellinRaw f) (z + (t : ℂ) * Complex.I) :=
        h1.differentiableAt hopen
      have hsh : DifferentiableAt ℂ (fun w : ℂ => w + (t : ℂ) * Complex.I) z :=
        differentiableAt_id.add_const _
      have h3 : DifferentiableAt ℂ (fun w : ℂ => mellinRaw f (w + (t : ℂ) * Complex.I)) z :=
        DifferentiableAt.comp (g := mellinRaw f) z h2 hsh
      exact (h3.mul (differentiableAt_id.pow 2).cexp).differentiableWithinAt
    · have hS : closure (verticalStrip x1 c) ⊆ verticalClosedStrip x1 c := by
        refine closure_minimal ?_ ?_
        · intro z hz; exact ⟨hz.1.le, hz.2.le⟩
        · have : verticalClosedStrip x1 c = Complex.re ⁻¹' Icc x1 c := rfl
          rw [this]; exact isClosed_Icc.preimage Complex.continuous_re
      refine ContinuousOn.mono ?_ hS
      have h1 : ContinuousOn (fun z : ℂ => mellinRaw f (z + (t : ℂ) * Complex.I))
          (verticalClosedStrip x1 c) := by
        refine (continuousOn_mellinRaw hc0 hf).comp (by fun_prop) ?_
        intro z hz
        have hz' : x1 ≤ z.re ∧ z.re ≤ c := hz
        show 0 < (z + (t : ℂ) * Complex.I).re ∧ (z + (t : ℂ) * Complex.I).re ≤ c
        rw [hshift_re]; exact ⟨by linarith [hz'.1], hz'.2⟩
      exact h1.mul (by fun_prop)
  -- edges
  have hLeft : ∀ z ∈ Complex.re ⁻¹' {x1}, ‖G z‖ ≤ Cg * (1 + |t|) ^ (-a) := by
    intro z hz
    have hzre : z.re = x1 := hz
    have hzeq : z = (x1 : ℂ) + (z.im : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [hzre]
    simp only [hG, norm_mul, hnormexp, hzre]
    have hmell := hCL (z.im + t)
    have e : z + (t : ℂ) * Complex.I = (x1 : ℂ) + ((z.im + t : ℝ) : ℂ) * Complex.I := by
      rw [hzeq]; push_cast; simp; ring
    rw [e]
    set y := z.im with hy
    have hw : 1 + |t| ≤ (1 + |y + t|) * (1 + |y|) := by
      have : |t| ≤ |y + t| + |y| := by
        have := abs_sub (y + t) y; simp at this; linarith [abs_sub_comm (y + t) y]
      nlinarith [abs_nonneg y, abs_nonneg (y + t), abs_nonneg t]
    have hu : 0 < 1 + |y + t| := by positivity
    have hv : 0 < 1 + |y| := by positivity
    have hwp : 0 < 1 + |t| := by positivity
    have h1 : (1 + |y + t|) ^ (-a) ≤ (1 + |y|) ^ a * (1 + |t|) ^ (-a) := by
      have h2 : (1 + |t|) ^ a ≤ ((1 + |y + t|) * (1 + |y|)) ^ a :=
        Real.rpow_le_rpow hwp.le hw ha0.le
      rw [Real.mul_rpow hu.le hv.le] at h2
      have h3 : (1 + |y + t|) ^ (-a) = ((1 + |y + t|) ^ a)⁻¹ := Real.rpow_neg hu.le a
      have h4 : (1 + |t|) ^ (-a) = ((1 + |t|) ^ a)⁻¹ := Real.rpow_neg hwp.le a
      have hupos : 0 < (1 + |y + t|) ^ a := Real.rpow_pos_of_pos hu a
      have hwpos : 0 < (1 + |t|) ^ a := Real.rpow_pos_of_pos hwp a
      have hvpos : 0 < (1 + |y|) ^ a := Real.rpow_pos_of_pos hv a
      rw [h3, h4, inv_eq_one_div, inv_eq_one_div, div_le_iff₀ hupos]
      rw [mul_one_div, div_mul_eq_mul_div, le_div_iff₀ hwpos]
      nlinarith
    have h5 : (1 + |y|) ^ a * Real.exp (-(y ^ 2)) ≤ Real.exp (a ^ 2 / 4) := by
      have h6 : (1 + |y|) ^ a ≤ Real.exp (|y| * a) := by
        calc (1 + |y|) ^ a ≤ (Real.exp |y|) ^ a :=
              Real.rpow_le_rpow hv.le (by linarith [Real.add_one_le_exp |y|]) ha0.le
          _ = Real.exp (|y| * a) := by rw [← Real.exp_mul]
      calc (1 + |y|) ^ a * Real.exp (-(y ^ 2)) ≤ Real.exp (|y| * a) * Real.exp (-(y ^ 2)) := by
            gcongr
        _ = Real.exp (|y| * a - y ^ 2) := by rw [← Real.exp_add]; ring_nf
        _ ≤ Real.exp (a ^ 2 / 4) := by
            apply Real.exp_le_exp.mpr
            have : y ^ 2 = |y| ^ 2 := (sq_abs y).symm
            nlinarith [sq_nonneg (|y| - a / 2)]
    have hexpe : Real.exp (x1 ^ 2 - y ^ 2) = Real.exp (x1 ^ 2) * Real.exp (-(y ^ 2)) := by
      rw [← Real.exp_add]; ring_nf
    rw [hexpe]
    calc ‖mellinRaw f ((x1 : ℂ) + ((y + t : ℝ) : ℂ) * Complex.I)‖ *
          (Real.exp (x1 ^ 2) * Real.exp (-(y ^ 2)))
        ≤ (CL * (1 + |y + t|) ^ (-a)) * (Real.exp (x1 ^ 2) * Real.exp (-(y ^ 2))) := by
          gcongr
      _ ≤ (CL * ((1 + |y|) ^ a * (1 + |t|) ^ (-a))) * (Real.exp (x1 ^ 2) * Real.exp (-(y ^ 2))) := by
          gcongr
      _ = (CL * Real.exp (x1 ^ 2)) * ((1 + |y|) ^ a * Real.exp (-(y ^ 2))) * (1 + |t|) ^ (-a) := by
          ring
      _ ≤ (CL * Real.exp (x1 ^ 2)) * Real.exp (a ^ 2 / 4) * (1 + |t|) ^ (-a) := by gcongr
      _ = Cg * (1 + |t|) ^ (-a) := by rw [hCg]
  have hRight : ∀ z ∈ Complex.re ⁻¹' {c}, ‖G z‖ ≤ Cr := by
    intro z hz
    have hzre : z.re = c := hz
    simp only [hG, norm_mul, hnormexp, hzre]
    have h1 := hJ (z + (t : ℂ) * Complex.I) (by rw [hshift_re, hzre]; linarith)
      (by rw [hshift_re, hzre])
    have h2 : Real.exp (c ^ 2 - z.im ^ 2) ≤ Real.exp (c ^ 2) :=
      Real.exp_le_exp.mpr (by nlinarith [sq_nonneg z.im])
    exact mul_le_mul h1 h2 (Real.exp_pos _).le hJ0
  have hxmem : (x : ℂ) ∈ verticalClosedStrip x1 c := by
    show x1 ≤ (x : ℂ).re ∧ (x : ℂ).re ≤ c
    simpa using ⟨hx, hxc⟩
  have hthree := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip' hx1c'
    hxmem hd hB hLeft hRight
  simp only [Complex.ofReal_re] at hthree
  have hGx : ‖G (x : ℂ)‖ = ‖mellinRaw f ((x : ℂ) + (t : ℂ) * Complex.I)‖ * Real.exp (x ^ 2) := by
    simp only [hG, norm_mul, hnormexp]; simp
  rw [hGx] at hthree
  rw [← hs] at hthree
  have hCgt : 0 ≤ Cg := hCg0
  have hpowt : 0 < 1 + |t| := by positivity
  have hsplit : (Cg * (1 + |t|) ^ (-a)) ^ (1 - s) = Cg ^ (1 - s) * (1 + |t|) ^ (-a * (1 - s)) := by
    rw [Real.mul_rpow hCgt (Real.rpow_nonneg hpowt.le _), ← Real.rpow_mul hpowt.le]
  rw [hsplit] at hthree
  have hexpn : 0 < Real.exp (x ^ 2) := Real.exp_pos _
  have hfin : ‖mellinRaw f ((x : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      (Cg ^ (1 - s) * (1 + |t|) ^ (-a * (1 - s)) * Cr ^ s) / Real.exp (x ^ 2) := by
    rw [le_div_iff₀ hexpn]; exact hthree
  have hexp' : -((c - 2 * x1) * ((c - x) / (c - x1))) = -a * (1 - s) := by rw [hs1, ha]; ring
  rw [hexp']
  calc _ ≤ _ := hfin
    _ = Real.exp (-(x ^ 2)) * Cg ^ (1 - s) * Cr ^ s * (1 + |t|) ^ (-a * (1 - s)) := by
      rw [div_eq_mul_inv, ← Real.exp_neg]; ring

/-- A small `x₁` for the three-lines argument. -/
lemma exists_x1 {c σ : ℝ} (hσ0 : 0 < σ) (hσ : σ + 1 < c) :
    ∃ x1 : ℝ, 0 < x1 ∧ x1 ≤ σ ∧ 2 * x1 < c ∧ 1 < (c - 2 * x1) * ((c - σ) / (c - x1)) := by
  set d : ℝ := c - σ with hd
  have hd1 : 1 < d := by rw [hd]; linarith
  have hc0 : 0 < c := by linarith
  set m : ℝ := c * (d - 1) / (2 * (2 * d - 1)) with hm
  have hm0 : 0 < m := by rw [hm]; apply div_pos (mul_pos hc0 (by linarith)); linarith
  have h2d : 2 * d - 1 ≠ 0 := by intro h; linarith
  have h2d' : d * 2 - 1 ≠ 0 := by intro h; linarith
  have hmm : m * (2 * d - 1) = c * (d - 1) / 2 := by rw [hm]; field_simp
  refine ⟨min (σ / 2) m, lt_min (by linarith) hm0, (min_le_left _ _).trans (by linarith), ?_, ?_⟩
  · have h1 : min (σ / 2) m ≤ m := min_le_right _ _
    have h2 : m * (2 * d - 1) < c * (d - 1) := by rw [hmm]; nlinarith [mul_pos hc0 (by linarith : (0 : ℝ) < d - 1)]
    nlinarith [mul_pos hc0 (by linarith : (0 : ℝ) < d - 1)]
  · set x1 := min (σ / 2) m with hx1
    have h1 : x1 ≤ m := min_le_right _ _
    have hx10 : 0 < x1 := lt_min (by linarith) hm0
    have hx1c : x1 < c := by nlinarith [min_le_left (σ / 2) m]
    have hcx1 : 0 < c - x1 := by linarith
    rw [← mul_div_assoc, lt_div_iff₀ hcx1]
    have h3 : x1 * (2 * d - 1) ≤ m * (2 * d - 1) := mul_le_mul_of_nonneg_right h1 (by linarith)
    nlinarith [mul_pos hc0 (by linarith : (0 : ℝ) < d - 1)]

lemma mellin_eq_mellinRaw (f : ℝ → ℝ) (s : ℂ) :
    mellin (fun t : ℝ => (f t : ℂ)) s = mellinRaw f s := by
  simp [mellin, mellinRaw, smul_eq_mul, mul_comm]

/-- Integrability of the raw Mellin transform along `Re z = σ`, `0 < σ`, `σ + 1 < c`. -/
theorem integrable_mellinRaw_line {c ε : ℝ} (hc : 3 / 2 < c) {f : ℝ → ℝ}
    (hf : IsHankelEigenfn c ε f) (hε : ε = 1 ∨ ε = -1) {σ : ℝ} (hσ0 : 0 < σ) (hσ : σ + 1 < c) :
    Integrable (fun y : ℝ => mellinRaw f ((σ : ℂ) + (y : ℂ) * Complex.I)) := by
  have hc0 : 0 < c := by linarith
  obtain ⟨x1, hx10, hx1σ, hx1c, hb⟩ := exists_x1 hσ0 hσ
  obtain ⟨C, hC0, hC⟩ := exists_norm_mellinRaw_interp hc hf hε hx10 hx1c hx1σ (by linarith : σ ≤ c)
  have hcont : Continuous (fun y : ℝ => mellinRaw f ((σ : ℂ) + (y : ℂ) * Complex.I)) := by
    have h := continuousOn_mellinRaw hc0 hf
    exact h.comp_continuous (by fun_prop : Continuous fun y : ℝ => (σ : ℂ) + (y : ℂ) * Complex.I)
      (fun y => by
        show 0 < ((σ : ℂ) + (y : ℂ) * Complex.I).re ∧ ((σ : ℂ) + (y : ℂ) * Complex.I).re ≤ c
        simp; exact ⟨hσ0, by linarith⟩)
  have hint : Integrable (fun y : ℝ => (1 + ‖y‖) ^ (-((c - 2 * x1) * ((c - σ) / (c - x1))))) :=
    integrable_one_add_norm (by simpa using hb)
  refine Integrable.mono' (hint.const_mul C) hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  simpa [Real.norm_eq_abs] using hC y

/-- **Mellin inversion for `f ∈ 𝒜_c^ε`**: for `0 < σ`, `σ + 1 < c` and `Δ > 0`,
`f(Δ) = (1/2π) ∫ Δ^{-(σ+iy)} mellinRaw f (σ+iy) dy`. -/
theorem mellin_inversion_f {c ε : ℝ} (hc : 3 / 2 < c) {f : ℝ → ℝ}
    (hf : IsHankelEigenfn c ε f) (hε : ε = 1 ∨ ε = -1) {σ : ℝ} (hσ0 : 0 < σ) (hσ : σ + 1 < c)
    {Δ : ℝ} (hΔ : 0 < Δ) :
    (f Δ : ℂ) = (1 / (2 * Real.pi) : ℂ) * ∫ y : ℝ,
      (Δ : ℂ) ^ (-((σ : ℂ) + (y : ℂ) * Complex.I)) * mellinRaw f ((σ : ℂ) + (y : ℂ) * Complex.I) := by
  have hc0 : 0 < c := by linarith
  have hconv : MellinConvergent (fun t : ℝ => (f t : ℂ)) (σ : ℂ) := by
    have := integrableOn_mellin_integrand hc0 hf (z := (σ : ℂ)) (by simpa using hσ0)
      (by simp; linarith)
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp [smul_eq_mul, mul_comm]
  have hvert : Complex.VerticalIntegrable (mellin (fun t : ℝ => (f t : ℂ))) σ := by
    have := integrable_mellinRaw_line hc hf hε hσ0 hσ
    unfold Complex.VerticalIntegrable
    simpa [mellin_eq_mellinRaw] using this
  have hcts : ContinuousAt (fun t : ℝ => (f t : ℂ)) Δ :=
    Complex.continuous_ofReal.continuousAt.comp (hf.cont.continuousAt (Ici_mem_nhds hΔ))
  have := mellinInv_mellin_eq σ (fun t : ℝ => (f t : ℂ)) hΔ hconv hvert hcts
  unfold mellinInv at this
  simp only [mellin_eq_mellinRaw, smul_eq_mul] at this
  rw [← this]
  simp

/-- info: 'FormalResearch.SignUncertainty.exists_norm_mellinRaw_interp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_norm_mellinRaw_interp

/-- info: 'FormalResearch.SignUncertainty.integrable_mellinRaw_line' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integrable_mellinRaw_line

/-- info: 'FormalResearch.SignUncertainty.mellin_inversion_f' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mellin_inversion_f

end FormalResearch.SignUncertainty
