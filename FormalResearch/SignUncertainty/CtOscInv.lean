module

public import FormalResearch.SignUncertainty.CtOscD2
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.Algebra.Order.Group
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Inverse of the Morse coordinate

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu` Step 4, Piece 1 ("Its inverse has uniformly bounded
derivatives through order three").  **Proved.**

An increasing chart `s` on `(-1,1)` with `m₀ ≤ s' ≤ Ks`, `s(0) = 0`, has a global inverse `tinv` on `(-m₀, m₀)`, with
`tinv' = 1/s'(tinv)`; it is `D2` with explicit constants.
-/

@[expose] public section

open Set Filter Topology

namespace FormalResearch.SignUncertainty.CtOsc

/-- An increasing chart on `(-1,1)`: `s' = sd ≥ m₀ > 0`, `sd` is `D2`, `s 0 = 0`. -/
structure Chart (s sd sd1 sd2 : ℝ → ℝ) (Ks m0 : ℝ) : Prop where
  D : D2 (Ioo (-1 : ℝ) 1) sd sd1 sd2 Ks
  hs : ∀ y ∈ Ioo (-1 : ℝ) 1, HasDerivAt s (sd y) y
  m0pos : 0 < m0
  lo : ∀ y ∈ Ioo (-1 : ℝ) 1, m0 ≤ sd y
  s0 : s 0 = 0

section
variable {s sd sd1 sd2 : ℝ → ℝ} {Ks m0 : ℝ}

lemma monoOn_of_hasDerivAt {g g' : ℝ → ℝ} (hg : ∀ y ∈ Ioo (-1 : ℝ) 1, HasDerivAt g (g' y) y)
    (hnn : ∀ y ∈ Ioo (-1 : ℝ) 1, 0 ≤ g' y) : MonotoneOn g (Ioo (-1 : ℝ) 1) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ioo _ _) (fun y hy => (hg y hy).continuousAt.continuousWithinAt) ?_ ?_
  · rw [interior_Ioo]; exact fun y hy => (hg y hy).differentiableAt.differentiableWithinAt
  · rw [interior_Ioo]; intro y hy; rw [(hg y hy).deriv]; exact hnn y hy

lemma Chart.strictMonoOn (h : Chart s sd sd1 sd2 Ks m0) : StrictMonoOn s (Ioo (-1 : ℝ) 1) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioo _ _) (fun y hy => (h.hs y hy).continuousAt.continuousWithinAt) ?_
  rw [interior_Ioo]; intro y hy; rw [(h.hs y hy).deriv]; exact lt_of_lt_of_le h.m0pos (h.lo y hy)

lemma Chart.cont_s (h : Chart s sd sd1 sd2 Ks m0) : ContinuousOn s (Ioo (-1 : ℝ) 1) :=
  fun y hy => (h.hs y hy).continuousAt.continuousWithinAt

lemma Chart.ge_pos (h : Chart s sd sd1 sd2 Ks m0) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) (h0 : 0 ≤ t) :
    m0 * t ≤ s t := by
  have hm : MonotoneOn (fun y => s y - m0 * y) (Ioo (-1 : ℝ) 1) :=
    monoOn_of_hasDerivAt (g' := fun y => sd y - m0)
      (fun y hy => by simpa using (h.hs y hy).fun_sub ((hasDerivAt_id y).const_mul m0))
      (fun y hy => sub_nonneg.2 (h.lo y hy))
  have := hm (by norm_num : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1) ht h0
  simp only [h.s0, mul_zero, sub_zero] at this
  linarith

lemma Chart.le_neg (h : Chart s sd sd1 sd2 Ks m0) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) (h0 : t ≤ 0) :
    s t ≤ m0 * t := by
  have hm : MonotoneOn (fun y => s y - m0 * y) (Ioo (-1 : ℝ) 1) :=
    monoOn_of_hasDerivAt (g' := fun y => sd y - m0)
      (fun y hy => by simpa using (h.hs y hy).fun_sub ((hasDerivAt_id y).const_mul m0))
      (fun y hy => sub_nonneg.2 (h.lo y hy))
  have := hm ht (by norm_num : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1) h0
  simp only [h.s0, mul_zero, sub_zero] at this
  linarith

lemma Chart.abs_s_le (h : Chart s sd sd1 sd2 Ks m0) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) : |s t| ≤ Ks * |t| := by
  have hm : MonotoneOn (fun y => Ks * y - s y) (Ioo (-1 : ℝ) 1) :=
    monoOn_of_hasDerivAt (g' := fun y => Ks - sd y)
      (fun y hy => by simpa using ((hasDerivAt_id y).const_mul Ks).fun_sub (h.hs y hy))
      (fun y hy => sub_nonneg.2 (le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using h.D.b0 y hy)))
  have hK := h.D.K0
  have h0 : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by norm_num
  rcases le_total 0 t with h1 | h1
  · have a1 := hm h0 ht h1
    simp only [h.s0, mul_zero, sub_zero] at a1
    have a2 := h.ge_pos ht h1
    rw [abs_of_nonneg h1, abs_of_nonneg (by nlinarith [h.m0pos])]
    linarith
  · have a1 := hm ht h0 h1
    simp only [h.s0, mul_zero, sub_zero] at a1
    have a2 := h.le_neg ht h1
    rw [abs_of_nonpos h1, abs_of_nonpos (by nlinarith [h.m0pos])]
    linarith

lemma Chart.surj (h : Chart s sd sd1 sd2 Ks m0) {X : ℝ} (hX : X ∈ Ioo (-m0) m0) :
    ∃ t ∈ Ioo (-1 : ℝ) 1, s t = X := by
  have hm := h.m0pos
  have hXa : |X| < m0 := abs_lt.mpr hX
  set τ : ℝ := (1 + |X| / m0) / 2 with hτ
  have h1 : |X| / m0 < 1 := (div_lt_one hm).mpr hXa
  have h2 : 0 ≤ |X| / m0 := by positivity
  have hτ1 : τ < 1 := by rw [hτ]; linarith
  have hτ0 : |X| / m0 < τ := by rw [hτ]; linarith
  have hτp : 0 < τ := lt_of_le_of_lt h2 hτ0
  have hmτ : |X| < m0 * τ := by
    have := (div_lt_iff₀ hm).mp hτ0
    linarith
  have hτI : τ ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, hτ1⟩
  have hnτI : -τ ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have a1 := h.ge_pos hτI hτp.le
  have a2 := h.le_neg hnτI (by linarith)
  have hsub : Icc (-τ) τ ⊆ Ioo (-1 : ℝ) 1 := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have := intermediate_value_Icc (by linarith : -τ ≤ τ) (h.cont_s.mono hsub)
    (show X ∈ Icc (s (-τ)) (s τ) from ⟨by nlinarith [neg_abs_le X, abs_nonneg X], by nlinarith [le_abs_self X]⟩)
  obtain ⟨t, ht, hst⟩ := this
  exact ⟨t, hsub ht, hst⟩

lemma Chart.exists_inv (h : Chart s sd sd1 sd2 Ks m0) :
    ∃ tinv : ℝ → ℝ, (∀ X ∈ Ioo (-m0) m0, tinv X ∈ Ioo (-1 : ℝ) 1 ∧ s (tinv X) = X) ∧
      (∀ t ∈ Ioo (-1 : ℝ) 1, s t ∈ Ioo (-m0) m0 → tinv (s t) = t) ∧
      ∀ X ∈ Ioo (-m0) m0, HasDerivAt tinv (sd (tinv X))⁻¹ X := by
  classical
  have hsurj := fun X (hX : X ∈ Ioo (-m0) m0) => h.surj hX
  have hspec : ∀ X (hX : X ∈ Ioo (-m0) m0),
      (hsurj X hX).choose ∈ Ioo (-1 : ℝ) 1 ∧ s (hsurj X hX).choose = X := fun X hX =>
    (hsurj X hX).choose_spec
  have hrep : ∀ X (hX : X ∈ Ioo (-m0) m0), (fun X => if hX : X ∈ Ioo (-m0) m0 then (hsurj X hX).choose else 0) X =
      (hsurj X hX).choose := fun X hX => by simp only [dif_pos hX]
  set tinv : ℝ → ℝ := fun X => if hX : X ∈ Ioo (-m0) m0 then (hsurj X hX).choose else 0 with htinv
  have h1 : ∀ X ∈ Ioo (-m0) m0, tinv X ∈ Ioo (-1 : ℝ) 1 ∧ s (tinv X) = X := fun X hX => by
    rw [hrep X hX]; exact hspec X hX
  have h2 : ∀ t ∈ Ioo (-1 : ℝ) 1, s t ∈ Ioo (-m0) m0 → tinv (s t) = t := fun t ht hst => by
    obtain ⟨hI, hs⟩ := h1 _ hst
    exact h.strictMonoOn.injOn hI ht hs
  refine ⟨tinv, h1, h2, fun X hX => ?_⟩
  obtain ⟨ht0, hs0⟩ := h1 X hX
  set t0 := tinv X with ht0def
  have hnhd : Ioo (-1 : ℝ) 1 ∈ 𝓝 t0 := Ioo_mem_nhds ht0.1 ht0.2
  have hstrict : HasStrictDerivAt s (sd t0) t0 :=
    hasStrictDerivAt_of_hasDerivAt_of_continuousAt (by filter_upwards [hnhd] with y hy using h.hs y hy)
      (h.D.cont0.continuousAt hnhd)
  have hJ : Ioo (-m0) m0 ∈ 𝓝 (s t0) := by rw [hs0]; exact Ioo_mem_nhds hX.1 hX.2
  have hg : ∀ᶠ x in 𝓝 t0, tinv (s x) = x := by
    filter_upwards [hnhd, (h.hs t0 ht0).continuousAt.preimage_mem_nhds hJ] with x hx hxJ using h2 x hx hxJ
  have hne : sd t0 ≠ 0 := ne_of_gt (lt_of_lt_of_le h.m0pos (h.lo t0 ht0))
  have := (hstrict.to_local_left_inverse hne hg).hasDerivAt
  rw [hs0] at this
  exact this

end

end FormalResearch.SignUncertainty.CtOsc
