module

public import Mathlib

/-!
# Hermite-interpolation sign lemmas (real-variable, by Rolle)

Used by Paper E, `lem:fqe-large-head-dual` (`renyi_large_head_dual.tex`).

* `hermite3_nonpos`: if `R` has `R(A) = R(m) = R'(m) = 0` and `R''' ≤ 0`, then `R ≤ 0` on `[A, B]`.
  (The quadratic Hermite interpolant at one single node and one double node is an upper bound when
  the third derivative is nonpositive.)
* `hermite4_nonneg`: if `R(l) = R'(l) = R(u) = R'(u) = 0` and `R'''' ≥ 0`, then `R ≥ 0` on `[A, B]`
  (the cubic Hermite interpolant at two double nodes is a lower bound when the fourth derivative is
  nonnegative).

Both are proved by Rolle's theorem and monotonicity of the successive derivatives; no remainder
formula is used.
-/

@[expose] public section


namespace FormalResearch.FourQubitEntropy.RenyiFull

open Set

/-- Monotonicity from the derivative sign, continuity on the closed and derivative on the open interval. -/
theorem le_of_deriv_nonneg_Icc {f f' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn f (Icc a b)) (hd : ∀ z ∈ Ioo a b, HasDerivAt f (f' z) z)
    (hs : ∀ z ∈ Ioo a b, 0 ≤ f' z) : f a ≤ f b := by
  have hm : MonotoneOn f (Icc a b) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b) hc (f' := f')
    · intro x hx
      rw [interior_Icc] at hx
      exact (hd x hx).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact hs x hx
  exact hm ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab

theorem ge_of_deriv_nonpos_Icc {f f' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn f (Icc a b)) (hd : ∀ z ∈ Ioo a b, HasDerivAt f (f' z) z)
    (hs : ∀ z ∈ Ioo a b, f' z ≤ 0) : f b ≤ f a := by
  have hm : AntitoneOn f (Icc a b) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b) hc (f' := f')
    · intro x hx
      rw [interior_Icc] at hx
      exact (hd x hx).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact hs x hx
  exact hm ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab

/-- Variant when the derivative exists on the whole closed interval. -/
theorem le_of_deriv_nonneg_hd {f f' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hd : ∀ z ∈ Icc a b, HasDerivAt f (f' z) z)
    (hs : ∀ z ∈ Ioo a b, 0 ≤ f' z) : f a ≤ f b :=
  le_of_deriv_nonneg_Icc hab (fun z hz => (hd z hz).continuousAt.continuousWithinAt)
    (fun z hz => hd z (Ioo_subset_Icc_self hz)) hs

theorem ge_of_deriv_nonpos_hd {f f' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hd : ∀ z ∈ Icc a b, HasDerivAt f (f' z) z)
    (hs : ∀ z ∈ Ioo a b, f' z ≤ 0) : f b ≤ f a :=
  ge_of_deriv_nonpos_Icc hab (fun z hz => (hd z hz).continuousAt.continuousWithinAt)
    (fun z hz => hd z (Ioo_subset_Icc_self hz)) hs

/-- Monotone step with the plumbing of sub-intervals absorbed. -/
theorem mono_step {f f' : ℝ → ℝ} {A B a b : ℝ} (hd : ∀ z ∈ Icc A B, HasDerivAt f (f' z) z)
    (hA : A ≤ a) (hb : b ≤ B) (hab : a ≤ b) (hs : ∀ z ∈ Icc a b, 0 ≤ f' z) : f a ≤ f b :=
  le_of_deriv_nonneg_hd hab (fun z hz => hd z ⟨hA.trans hz.1, hz.2.trans hb⟩)
    (fun z hz => hs z (Ioo_subset_Icc_self hz))

theorem anti_step {f f' : ℝ → ℝ} {A B a b : ℝ} (hd : ∀ z ∈ Icc A B, HasDerivAt f (f' z) z)
    (hA : A ≤ a) (hb : b ≤ B) (hab : a ≤ b) (hs : ∀ z ∈ Icc a b, f' z ≤ 0) : f b ≤ f a :=
  ge_of_deriv_nonpos_hd hab (fun z hz => hd z ⟨hA.trans hz.1, hz.2.trans hb⟩)
    (fun z hz => hs z (Ioo_subset_Icc_self hz))

/-- **Quadratic Hermite upper bound.** `R(A) = R(m) = R'(m) = 0`, `R''' ≤ 0` on `[A,B]` gives `R ≤ 0`. -/
theorem hermite3_nonpos {A B m : ℝ} (hAm : A < m) (hmB : m ≤ B) {R R1 R2 R3 : ℝ → ℝ}
    (d0 : ∀ z ∈ Icc A B, HasDerivAt R (R1 z) z) (d1 : ∀ z ∈ Icc A B, HasDerivAt R1 (R2 z) z)
    (d2 : ∀ z ∈ Icc A B, HasDerivAt R2 (R3 z) z) (h3 : ∀ z ∈ Icc A B, R3 z ≤ 0)
    (hA0 : R A = 0) (hm0 : R m = 0) (hm1 : R1 m = 0) : ∀ z ∈ Icc A B, R z ≤ 0 := by
  have cont0 : ∀ {a b : ℝ}, A ≤ a → b ≤ B → ContinuousOn R (Icc a b) := fun ha hb z hz =>
    (d0 z ⟨ha.trans hz.1, hz.2.trans hb⟩).continuousAt.continuousWithinAt
  have cont1 : ∀ {a b : ℝ}, A ≤ a → b ≤ B → ContinuousOn R1 (Icc a b) := fun ha hb z hz =>
    (d1 z ⟨ha.trans hz.1, hz.2.trans hb⟩).continuousAt.continuousWithinAt
  obtain ⟨ξ, hξ, hξ0⟩ := exists_hasDerivAt_eq_zero hAm (cont0 le_rfl hmB) (hA0.trans hm0.symm)
    (fun z hz => d0 z ⟨hz.1.le, hz.2.le.trans hmB⟩)
  have hξA : A < ξ := hξ.1
  have hξm : ξ < m := hξ.2
  obtain ⟨η, hη, hη0⟩ := exists_hasDerivAt_eq_zero hξm (cont1 hξA.le hmB) (hξ0.trans hm1.symm)
    (fun z hz => d1 z ⟨hξA.le.trans hz.1.le, hz.2.le.trans hmB⟩)
  have hηξ : ξ < η := hη.1
  have hηm : η < m := hη.2
  have s2a : ∀ z ∈ Icc A η, 0 ≤ R2 z := by
    intro z hz
    have := anti_step d2 hz.1 (hηm.le.trans hmB) hz.2 (fun w hw => h3 w ⟨hz.1.trans hw.1, hw.2.trans (hηm.le.trans hmB)⟩)
    linarith
  have s2b : ∀ z ∈ Icc η B, R2 z ≤ 0 := by
    intro z hz
    have := anti_step d2 (hξA.le.trans hηξ.le) hz.2 hz.1 (fun w hw => h3 w ⟨(hξA.le.trans hηξ.le).trans hw.1, hw.2.trans hz.2⟩)
    linarith
  have s1a : ∀ z ∈ Icc A ξ, R1 z ≤ 0 := by
    intro z hz
    have := mono_step d1 hz.1 (hξm.le.trans hmB) hz.2 (fun w hw => s2a w ⟨hz.1.trans hw.1, hw.2.trans hηξ.le⟩)
    linarith
  have s1b : ∀ z ∈ Icc ξ m, 0 ≤ R1 z := by
    intro z hz
    rcases le_total z η with h | h
    · have := mono_step d1 hξA.le (hz.2.trans hmB) hz.1
        (fun w hw => s2a w ⟨hξA.le.trans hw.1, hw.2.trans h⟩)
      linarith
    · have := anti_step d1 (hξA.le.trans (hηξ.le.trans h)) hmB hz.2
        (fun w hw => s2b w ⟨h.trans hw.1, hw.2.trans hmB⟩)
      linarith
  have s1c : ∀ z ∈ Icc m B, R1 z ≤ 0 := by
    intro z hz
    have := anti_step d1 (hAm.le) hz.2 hz.1
      (fun w hw => s2b w ⟨hηm.le.trans hw.1, hw.2.trans hz.2⟩)
    linarith
  intro z hz
  rcases le_total z ξ with h1 | h1
  · have := anti_step d0 le_rfl (h1.trans (hξm.le.trans hmB)) hz.1
      (fun w hw => s1a w ⟨hw.1, hw.2.trans h1⟩)
    linarith
  rcases le_total z m with h2 | h2
  · have := mono_step d0 (hξA.le.trans h1) hmB h2
      (fun w hw => s1b w ⟨h1.trans hw.1, hw.2⟩)
    linarith
  · have := anti_step d0 hAm.le hz.2 h2 (fun w hw => s1c w ⟨hw.1, hw.2.trans hz.2⟩)
    linarith

/-- **Cubic Hermite lower bound.**  `R(l) = R'(l) = R(u) = R'(u) = 0`, `R'''' ≥ 0` on `(A,B)`
(with `R, R'` continuous on `[A,B]`) gives `R ≥ 0` on `[A,B]`. -/
theorem hermite4_nonneg {A B l u : ℝ} (hAl : A ≤ l) (hlu : l < u) (huB : u ≤ B)
    {R R1 R2 R3 R4 : ℝ → ℝ}
    (c0 : ContinuousOn R (Icc A B)) (c1 : ContinuousOn R1 (Icc A B))
    (d0 : ∀ z ∈ Ioo A B, HasDerivAt R (R1 z) z) (d1 : ∀ z ∈ Ioo A B, HasDerivAt R1 (R2 z) z)
    (d2 : ∀ z ∈ Ioo A B, HasDerivAt R2 (R3 z) z) (d3 : ∀ z ∈ Ioo A B, HasDerivAt R3 (R4 z) z)
    (h4 : ∀ z ∈ Ioo A B, 0 ≤ R4 z)
    (hl0 : R l = 0) (hu0 : R u = 0) (hl1 : R1 l = 0) (hu1 : R1 u = 0) : ∀ z ∈ Icc A B, 0 ≤ R z := by
  -- steps on `Ioo`-derivative functions
  have mo : ∀ {f f' : ℝ → ℝ} {a b : ℝ}, ContinuousOn f (Icc A B) → (∀ z ∈ Ioo A B, HasDerivAt f (f' z) z) →
      A ≤ a → b ≤ B → a ≤ b → (∀ z ∈ Ioo a b, 0 ≤ f' z) → f a ≤ f b := by
    intro f f' a b hc hd hA hb hab hs
    exact le_of_deriv_nonneg_Icc hab (hc.mono (Icc_subset_Icc hA hb))
      (fun z hz => hd z ⟨hA.trans_lt hz.1, hz.2.trans_le hb⟩) hs
  have an : ∀ {f f' : ℝ → ℝ} {a b : ℝ}, ContinuousOn f (Icc A B) → (∀ z ∈ Ioo A B, HasDerivAt f (f' z) z) →
      A ≤ a → b ≤ B → a ≤ b → (∀ z ∈ Ioo a b, f' z ≤ 0) → f b ≤ f a := by
    intro f f' a b hc hd hA hb hab hs
    exact ge_of_deriv_nonpos_Icc hab (hc.mono (Icc_subset_Icc hA hb))
      (fun z hz => hd z ⟨hA.trans_lt hz.1, hz.2.trans_le hb⟩) hs
  have cont : ∀ {f f' : ℝ → ℝ}, (∀ z ∈ Ioo A B, HasDerivAt f (f' z) z) → ∀ {a b : ℝ}, A < a → b < B →
      ContinuousOn f (Icc a b) := fun hd a b ha hb z hz =>
    (hd z ⟨ha.trans_le hz.1, hz.2.trans_lt hb⟩).continuousAt.continuousWithinAt
  have mo2 : ∀ {f f' : ℝ → ℝ}, (∀ z ∈ Ioo A B, HasDerivAt f (f' z) z) → ∀ {a b : ℝ}, A < a → b < B →
      a ≤ b → (∀ z ∈ Ioo a b, 0 ≤ f' z) → f a ≤ f b := by
    intro f f' hd a b ha hb hab hs
    exact le_of_deriv_nonneg_Icc hab (cont hd ha hb)
      (fun z hz => hd z ⟨ha.trans hz.1, hz.2.trans hb⟩) hs
  have an2 : ∀ {f f' : ℝ → ℝ}, (∀ z ∈ Ioo A B, HasDerivAt f (f' z) z) → ∀ {a b : ℝ}, A < a → b < B →
      a ≤ b → (∀ z ∈ Ioo a b, f' z ≤ 0) → f b ≤ f a := by
    intro f f' hd a b ha hb hab hs
    exact ge_of_deriv_nonpos_Icc hab (cont hd ha hb)
      (fun z hz => hd z ⟨ha.trans hz.1, hz.2.trans hb⟩) hs
  -- Rolle points
  obtain ⟨ξ, hξ, hξ0⟩ := exists_hasDerivAt_eq_zero hlu (c0.mono (Icc_subset_Icc hAl huB)) (hl0.trans hu0.symm)
    (fun z hz => d0 z ⟨hAl.trans_lt hz.1, hz.2.trans_le huB⟩)
  have hlξ : l < ξ := hξ.1
  have hξu : ξ < u := hξ.2
  obtain ⟨η1, hη1, hη10⟩ := exists_hasDerivAt_eq_zero hlξ (c1.mono (Icc_subset_Icc hAl (hξu.le.trans huB)))
    (hl1.trans hξ0.symm) (fun z hz => d1 z ⟨hAl.trans_lt hz.1, hz.2.trans (hξu.trans_le huB)⟩)
  obtain ⟨η2, hη2, hη20⟩ := exists_hasDerivAt_eq_zero hξu (c1.mono (Icc_subset_Icc (hAl.trans (hlξ.le)) huB))
    (hξ0.trans hu1.symm) (fun z hz => d1 z ⟨(hAl.trans_lt (hlξ.trans hz.1)), hz.2.trans_le huB⟩)
  have h1ξ : η1 < ξ := hη1.2
  have hξ2 : ξ < η2 := hη2.1
  have hAη1 : A < η1 := hAl.trans_lt hη1.1
  have hη2B : η2 < B := hη2.2.trans_le huB
  obtain ⟨ζ, hζ, hζ0⟩ := exists_hasDerivAt_eq_zero (h1ξ.trans hξ2)
    (cont d2 hAη1 hη2B) (hη10.trans hη20.symm)
    (fun z hz => d2 z ⟨hAη1.trans hz.1, hz.2.trans hη2B⟩)
  have hηζ : η1 < ζ := hζ.1
  have hζη : ζ < η2 := hζ.2
  have hζB : ζ < B := hζη.trans hη2B
  have hAζ : A < ζ := hAη1.trans hηζ
  -- sign of R3
  have s3a : ∀ z, A < z → z ≤ ζ → R3 z ≤ 0 := by
    intro z hz hzζ
    have := mo2 d3 hz hζB hzζ (fun w hw => h4 w ⟨hz.trans hw.1, hw.2.trans hζB⟩)
    linarith
  have s3b : ∀ z, ζ ≤ z → z < B → 0 ≤ R3 z := by
    intro z hz hzB
    have := mo2 d3 hAζ hzB hz (fun w hw => h4 w ⟨hAζ.trans hw.1, hw.2.trans hzB⟩)
    linarith
  -- sign of R2
  have s2a : ∀ z, A < z → z ≤ η1 → 0 ≤ R2 z := by
    intro z hz hzη
    have := an2 d2 hz (by linarith) hzη
      (fun w hw => s3a w (by linarith [hw.1]) (by linarith [hw.2]))
    linarith
  have s2b : ∀ z, η1 ≤ z → z ≤ η2 → R2 z ≤ 0 := by
    intro z hz hz2
    rcases le_total z ζ with h | h
    · have := an2 d2 hAη1 (by linarith) hz
        (fun w hw => s3a w (by linarith [hw.1]) (by linarith [hw.2]))
      linarith
    · have := mo2 d2 (by linarith : A < z) hη2B hz2
        (fun w hw => s3b w (by linarith [hw.1]) (by linarith [hw.2]))
      linarith
  have s2c : ∀ z, η2 ≤ z → z < B → 0 ≤ R2 z := by
    intro z hz hzB
    have := mo2 d2 (by linarith) hzB hz
      (fun w hw => s3b w (by linarith [hw.1]) (by linarith [hw.2]))
    linarith
  -- sign of R1
  have s1a : ∀ z ∈ Icc A l, R1 z ≤ 0 := by
    intro z hz
    have := mo c1 d1 hz.1 (by linarith) hz.2
      (fun w hw => s2a w (by linarith [hw.1, hz.1]) (by linarith [hw.2, hη1.1]))
    linarith
  have s1b : ∀ z ∈ Icc l ξ, 0 ≤ R1 z := by
    intro z hz
    rcases le_total z η1 with h | h
    · have := mo c1 d1 hAl (by linarith) hz.1
        (fun w hw => s2a w (by linarith [hw.1]) (by linarith [hw.2]))
      linarith
    · have := an c1 d1 (by linarith) (by linarith) hz.2
        (fun w hw => s2b w (by linarith [hw.1]) (by linarith [hw.2]))
      linarith
  have s1c : ∀ z ∈ Icc ξ u, R1 z ≤ 0 := by
    intro z hz
    rcases le_total z η2 with h | h
    · have := an c1 d1 (by linarith) (by linarith) hz.1
        (fun w hw => s2b w (by linarith [hw.1]) (by linarith [hw.2]))
      linarith
    · have := mo c1 d1 (by linarith) huB hz.2
        (fun w hw => s2c w (by linarith [hw.1, hz.1, hξ2]) (by linarith [hw.2, huB]))
      linarith
  have s1d : ∀ z ∈ Icc u B, 0 ≤ R1 z := by
    intro z hz
    have := mo c1 d1 (by linarith) hz.2 hz.1
      (fun w hw => s2c w (by linarith [hw.1, hη2.2]) (by linarith [hw.2, hz.2]))
    linarith
  -- conclusion
  intro z hz
  rcases le_total z l with h1 | h1
  · have := an c0 d0 hz.1 (by linarith) h1
      (fun w hw => s1a w ⟨by linarith [hw.1, hz.1], by linarith [hw.2]⟩ |> fun x => by linarith [x])
    linarith
  rcases le_total z ξ with h2 | h2
  · have := mo c0 d0 hAl (by linarith [hz.2, hξu, huB]) h1
      (fun w hw => s1b w ⟨by linarith [hw.1], by linarith [hw.2]⟩)
    linarith
  rcases le_total z u with h3 | h3
  · have := an c0 d0 (by linarith [hz.1]) huB h3
      (fun w hw => s1c w ⟨by linarith [hw.1], by linarith [hw.2]⟩)
    linarith
  · have := mo c0 d0 (by linarith) hz.2 h3
      (fun w hw => s1d w ⟨by linarith [hw.1], by linarith [hw.2, hz.2]⟩)
    linarith

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.hermite3_nonpos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hermite3_nonpos

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.hermite4_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hermite4_nonneg

end FormalResearch.FourQubitEntropy.RenyiFull
