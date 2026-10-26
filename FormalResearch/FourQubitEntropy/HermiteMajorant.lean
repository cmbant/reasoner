import Mathlib

/-!
# A Hermite-interpolation positivity lemma

Let `φ` be a function on `[0,∞)` with a chain of three derivatives `φ ⟶ φ₁ ⟶ φ₂ ⟶ φ₃` on `(0,∞)`
(`φ₃` is the third derivative), with `φ₃` strictly increasing (that is, `φ⁗ > 0`), and with
double zeros at two nodes `0 < p < r` (`φ p = φ' p = φ r = φ' r = 0`). Then `φ > 0` on
`[0,∞) ∖ {p, r}`, and `φ₃` vanishes somewhere (so `φ'''` changes sign).

This is the Hermite remainder argument "`f⁗ < 0 ⟹ f ≤` its cubic Hermite interpolant" in a form
that needs no divided-difference formalism: only Rolle's theorem and monotonicity.
-/

namespace FormalResearch.FourQubitEntropy

namespace HM

/-- Strict increase from a positive derivative on the interior. -/
theorem strictMono_of_pos {g g' : ℝ → ℝ} {a b : ℝ} (hc : ContinuousOn g (Set.Icc a b))
    (hd : ∀ x ∈ Set.Ioo a b, HasDerivAt g (g' x) x) (hp : ∀ x ∈ Set.Ioo a b, 0 < g' x) :
    StrictMonoOn g (Set.Icc a b) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc a b) hc
  intro x hx
  rw [interior_Icc] at hx
  rw [(hd x hx).deriv]; exact hp x hx

/-- Strict decrease from a negative derivative on the interior. -/
theorem strictAnti_of_neg {g g' : ℝ → ℝ} {a b : ℝ} (hc : ContinuousOn g (Set.Icc a b))
    (hd : ∀ x ∈ Set.Ioo a b, HasDerivAt g (g' x) x) (hp : ∀ x ∈ Set.Ioo a b, g' x < 0) :
    StrictAntiOn g (Set.Icc a b) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc a b) hc
  intro x hx
  rw [interior_Icc] at hx
  rw [(hd x hx).deriv]; exact hp x hx

end HM

open HM in
/-- **Hermite positivity.** See the module docstring. -/
theorem hermite_positivity {φ φ₁ φ₂ φ₃ : ℝ → ℝ} {p r : ℝ} (hp : 0 < p) (hpr : p < r)
    (hc : ContinuousOn φ (Set.Ici 0))
    (d0 : ∀ x, 0 < x → HasDerivAt φ (φ₁ x) x)
    (d1 : ∀ x, 0 < x → HasDerivAt φ₁ (φ₂ x) x)
    (d2 : ∀ x, 0 < x → HasDerivAt φ₂ (φ₃ x) x)
    (h4 : StrictMonoOn φ₃ (Set.Ioi 0))
    (z0p : φ p = 0) (z1p : φ₁ p = 0) (z0r : φ r = 0) (z1r : φ₁ r = 0) :
    (∀ x, 0 ≤ x → x ≠ p → x ≠ r → 0 < φ x) ∧ ∃ u, 0 < u ∧ φ₃ u = 0 := by
  have hr : 0 < r := hp.trans hpr
  -- continuity of the derivatives on `(0,∞)`
  have c0 : ∀ a b : ℝ, 0 < a → ContinuousOn φ (Set.Icc a b) := fun a b ha x hx =>
    (d0 x (ha.trans_le hx.1)).continuousAt.continuousWithinAt
  have c1 : ∀ a b : ℝ, 0 < a → ContinuousOn φ₁ (Set.Icc a b) := fun a b ha x hx =>
    (d1 x (ha.trans_le hx.1)).continuousAt.continuousWithinAt
  have c2 : ∀ a b : ℝ, 0 < a → ContinuousOn φ₂ (Set.Icc a b) := fun a b ha x hx =>
    (d2 x (ha.trans_le hx.1)).continuousAt.continuousWithinAt
  -- Rolle
  obtain ⟨s, hs, hs0⟩ := exists_hasDerivAt_eq_zero hpr (c0 p r hp)
    (z0p.trans z0r.symm) (fun x hx => d0 x (hp.trans hx.1))
  obtain ⟨t₁, ht₁, ht₁0⟩ := exists_hasDerivAt_eq_zero hs.1 (c1 p s hp)
    (z1p.trans hs0.symm) (fun x hx => d1 x (hp.trans hx.1))
  obtain ⟨t₂, ht₂, ht₂0⟩ := exists_hasDerivAt_eq_zero hs.2 (c1 s r (hp.trans hs.1))
    (hs0.trans z1r.symm) (fun x hx => d1 x ((hp.trans hs.1).trans hx.1))
  have ht12 : t₁ < t₂ := ht₁.2.trans ht₂.1
  have ht₁pos : 0 < t₁ := hp.trans ht₁.1
  obtain ⟨u, hu, hu0⟩ := exists_hasDerivAt_eq_zero ht12 (c2 t₁ t₂ ht₁pos)
    (ht₁0.trans ht₂0.symm) (fun x hx => d2 x (ht₁pos.trans hx.1))
  have hupos : 0 < u := ht₁pos.trans hu.1
  refine ⟨?_, u, hupos, hu0⟩
  -- sign of φ₃ around `u`
  have neg3 : ∀ x, 0 < x → x < u → φ₃ x < 0 := fun x hx hxu => by
    have := h4 hx hupos hxu; rwa [hu0] at this
  have pos3 : ∀ x, u < x → 0 < φ₃ x := fun x hx => by
    have := h4 hupos (hupos.trans hx) hx; rwa [hu0] at this
  -- signs of φ₂
  have S1 : ∀ x, 0 < x → x < t₁ → 0 < φ₂ x := by
    intro x hx hxt
    have hxu : x < u := hxt.trans hu.1
    have hm : StrictAntiOn φ₂ (Set.Icc x u) :=
      strictAnti_of_neg (c2 x u hx) (fun y hy => d2 y (hx.trans hy.1))
        (fun y hy => neg3 y (hx.trans hy.1) hy.2)
    have := hm ⟨le_refl x, hxu.le⟩ ⟨hxt.le, hu.1.le⟩ hxt
    rwa [ht₁0] at this
  have S2 : ∀ x, t₁ < x → x < t₂ → φ₂ x < 0 := by
    intro x hx1 hx2
    rcases le_total x u with hxu | hxu
    · have hm : StrictAntiOn φ₂ (Set.Icc t₁ u) :=
        strictAnti_of_neg (c2 t₁ u ht₁pos) (fun y hy => d2 y (ht₁pos.trans hy.1))
          (fun y hy => neg3 y (ht₁pos.trans hy.1) hy.2)
      have := hm ⟨le_refl _, hu.1.le⟩ ⟨hx1.le, hxu⟩ hx1
      rwa [ht₁0] at this
    · have hm : StrictMonoOn φ₂ (Set.Icc u t₂) :=
        strictMono_of_pos (c2 u t₂ hupos) (fun y hy => d2 y (hupos.trans hy.1))
          (fun y hy => pos3 y hy.1)
      have := hm ⟨hxu, hx2.le⟩ ⟨hu.2.le, le_refl _⟩ hx2
      rwa [ht₂0] at this
  have S3 : ∀ x, t₂ < x → 0 < φ₂ x := by
    intro x hx
    have hm : StrictMonoOn φ₂ (Set.Icc u x) :=
      strictMono_of_pos (c2 u x hupos) (fun y hy => d2 y (hupos.trans hy.1))
        (fun y hy => pos3 y hy.1)
    have := hm ⟨hu.2.le, hx.le⟩ ⟨hu.2.le.trans hx.le, le_refl _⟩ hx
    rwa [ht₂0] at this
  -- signs of φ₁
  have F1 : ∀ x, 0 < x → x < p → φ₁ x < 0 := by
    intro x hx hxp
    have hm : StrictMonoOn φ₁ (Set.Icc x p) :=
      strictMono_of_pos (c1 x p hx) (fun y hy => d1 y (hx.trans hy.1))
        (fun y hy => S1 y (hx.trans hy.1) (hy.2.trans ht₁.1))
    have := hm ⟨le_refl _, hxp.le⟩ ⟨hxp.le, le_refl _⟩ hxp
    rwa [z1p] at this
  have F2 : ∀ x, p < x → x < s → 0 < φ₁ x := by
    intro x hx1 hx2
    rcases le_total x t₁ with hxt | hxt
    · have hm : StrictMonoOn φ₁ (Set.Icc p x) :=
        strictMono_of_pos (c1 p x hp) (fun y hy => d1 y (hp.trans hy.1))
          (fun y hy => S1 y (hp.trans hy.1) (hy.2.trans_le hxt))
      have := hm ⟨le_refl _, hx1.le⟩ ⟨hx1.le, le_refl _⟩ hx1
      rwa [z1p] at this
    · have hm : StrictAntiOn φ₁ (Set.Icc t₁ s) :=
        strictAnti_of_neg (c1 t₁ s ht₁pos) (fun y hy => d1 y (ht₁pos.trans hy.1))
          (fun y hy => S2 y hy.1 (hy.2.trans ht₂.1))
      have := hm ⟨hxt, hx2.le⟩ ⟨ht₁.2.le, le_refl _⟩ hx2
      rwa [hs0] at this
  have F3 : ∀ x, s < x → x < r → φ₁ x < 0 := by
    intro x hx1 hx2
    rcases le_total x t₂ with hxt | hxt
    · have hm : StrictAntiOn φ₁ (Set.Icc s x) :=
        strictAnti_of_neg (c1 s x (hp.trans hs.1)) (fun y hy => d1 y ((hp.trans hs.1).trans hy.1))
          (fun y hy => S2 y (ht₁.2.trans hy.1) (hy.2.trans_le hxt))
      have := hm ⟨le_refl _, hx1.le⟩ ⟨hx1.le, le_refl _⟩ hx1
      rwa [hs0] at this
    · have hm : StrictMonoOn φ₁ (Set.Icc x r) :=
        strictMono_of_pos (c1 x r (hp.trans (hs.1.trans hx1))) (fun y hy => d1 y
            ((hp.trans (hs.1.trans hx1)).trans hy.1))
          (fun y hy => S3 y (lt_of_le_of_lt hxt hy.1))
      have := hm ⟨le_refl _, hx2.le⟩ ⟨hx2.le, le_refl _⟩ hx2
      rwa [z1r] at this
  have F4 : ∀ x, r < x → 0 < φ₁ x := by
    intro x hx
    have hm : StrictMonoOn φ₁ (Set.Icc r x) :=
      strictMono_of_pos (c1 r x hr) (fun y hy => d1 y (hr.trans hy.1))
        (fun y hy => S3 y (ht₂.2.trans hy.1))
    have := hm ⟨le_refl _, hx.le⟩ ⟨hx.le, le_refl _⟩ hx
    rwa [z1r] at this
  -- the function itself
  have G1 : ∀ x, 0 ≤ x → x < p → 0 < φ x := by
    intro x hx hxp
    have hm : StrictAntiOn φ (Set.Icc x p) :=
      strictAnti_of_neg (hc.mono fun y hy => le_trans hx hy.1)
        (fun y hy => d0 y (lt_of_le_of_lt hx hy.1))
        (fun y hy => F1 y (lt_of_le_of_lt hx hy.1) hy.2)
    have := hm ⟨le_refl _, hxp.le⟩ ⟨hxp.le, le_refl _⟩ hxp
    rwa [z0p] at this
  have G2 : ∀ x, p < x → x ≤ s → 0 < φ x := by
    intro x hx1 hx2
    have hm : StrictMonoOn φ (Set.Icc p x) :=
      strictMono_of_pos (c0 p x hp) (fun y hy => d0 y (hp.trans hy.1))
        (fun y hy => F2 y hy.1 (hy.2.trans_le hx2))
    have := hm ⟨le_refl _, hx1.le⟩ ⟨hx1.le, le_refl _⟩ hx1
    rwa [z0p] at this
  have G3 : ∀ x, s < x → x < r → 0 < φ x := by
    intro x hx1 hx2
    have hxp : 0 < x := hp.trans (hs.1.trans hx1)
    have hm : StrictAntiOn φ (Set.Icc x r) :=
      strictAnti_of_neg (c0 x r hxp) (fun y hy => d0 y (hxp.trans hy.1))
        (fun y hy => F3 y (hx1.trans hy.1) hy.2)
    have := hm ⟨le_refl _, hx2.le⟩ ⟨hx2.le, le_refl _⟩ hx2
    rwa [z0r] at this
  have G4 : ∀ x, r < x → 0 < φ x := by
    intro x hx
    have hm : StrictMonoOn φ (Set.Icc r x) :=
      strictMono_of_pos (c0 r x hr) (fun y hy => d0 y (hr.trans hy.1))
        (fun y hy => F4 y hy.1)
    have := hm ⟨le_refl _, hx.le⟩ ⟨hx.le, le_refl _⟩ hx
    rwa [z0r] at this
  intro x hx hxp hxr
  rcases lt_or_gt_of_ne hxp with h1 | h1
  · exact G1 x hx h1
  rcases le_or_gt x s with h2 | h2
  · exact G2 x h1 h2
  rcases lt_or_gt_of_ne hxr with h3 | h3
  · exact G3 x h2 h3
  · exact G4 x h3

/-- info: 'FormalResearch.FourQubitEntropy.hermite_positivity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hermite_positivity

end FormalResearch.FourQubitEntropy
