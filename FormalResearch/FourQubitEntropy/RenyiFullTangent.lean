module

public import Mathlib

/-!
# The convex-then-concave tangent argument (`lem:fqe-hs-polynomial`)

An abstract version of the paper's curvature argument.  Let `Φ` be continuous on `[a₀, a₁]` with
`Φ' = E·P` (`P > 0`) and `E' = K·(J - L)` (`K > 0`) on the open interval, `J` continuous and strictly
decreasing, and let `x*` be an interior point with `E(x*) = 0` and `Φ(a₀) < Φ(x*)`.  Then `Φ(x) < Φ(x*)`
for every `x ∈ [a₀, a₁]`, `x ≠ x*`.

(`J > L` first and then `J < L`: `E` is first increasing then decreasing, so `Φ' = EP` changes sign at
most twice; since `Φ(a₀) < Φ(x*)`, `Φ` is first quasi-convex, then unimodal with maximum at `x*`.)
-/

@[expose] public section


namespace FormalResearch.FourQubitEntropy.RenyiFull

open Set

variable {Φ E P K J : ℝ → ℝ} {L a0 a1 xs : ℝ}

/-- Strict monotonicity from a positive derivative on an open interval. -/
theorem strictMonoOn_of_hasDerivAt_pos {f f' : ℝ → ℝ} {a b : ℝ}
    (hc : ContinuousOn f (Icc a b)) (hd : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hp : ∀ x ∈ Ioo a b, 0 < f' x) : StrictMonoOn f (Icc a b) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc a b) hc ?_
  intro x hx
  rw [interior_Icc] at hx
  rw [(hd x hx).deriv]
  exact hp x hx

theorem strictAntiOn_of_hasDerivAt_neg {f f' : ℝ → ℝ} {a b : ℝ}
    (hc : ContinuousOn f (Icc a b)) (hd : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hp : ∀ x ∈ Ioo a b, f' x < 0) : StrictAntiOn f (Icc a b) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc a b) hc ?_
  intro x hx
  rw [interior_Icc] at hx
  rw [(hd x hx).deriv]
  exact hp x hx

theorem tangent_argument
    (hΦc : ContinuousOn Φ (Icc a0 a1)) (hEc : ContinuousOn E (Icc a0 a1))
    (hΦd : ∀ x ∈ Ioo a0 a1, HasDerivAt Φ (E x * P x) x) (hP : ∀ x ∈ Ioo a0 a1, 0 < P x)
    (hEd : ∀ x ∈ Ioo a0 a1, HasDerivAt E (K x * (J x - L)) x) (hK : ∀ x ∈ Ioo a0 a1, 0 < K x)
    (hJ : StrictAntiOn J (Icc a0 a1)) (hJc : ContinuousOn J (Icc a0 a1))
    (hxs : xs ∈ Ioo a0 a1) (hE0 : E xs = 0) (hΦ1 : Φ a0 < Φ xs) :
    ∀ x ∈ Icc a0 a1, x ≠ xs → Φ x < Φ xs := by
  have hxs0 : a0 < xs := hxs.1
  have hxs1 : xs < a1 := hxs.2
  -- sub-interval helpers
  have sub : ∀ {c d : ℝ}, a0 ≤ c → d ≤ a1 → Ioo c d ⊆ Ioo a0 a1 := fun {c d} hc hd x hx =>
    ⟨lt_of_le_of_lt hc hx.1, lt_of_lt_of_le hx.2 hd⟩
  have subc : ∀ {c d : ℝ}, a0 ≤ c → d ≤ a1 → Icc c d ⊆ Icc a0 a1 := fun {c d} hc hd x hx =>
    ⟨hc.trans hx.1, hx.2.trans hd⟩
  -- Step 1: J xs < L
  have step1 : J xs < L := by
    by_contra hge
    push Not at hge
    have hEmono : StrictMonoOn E (Icc a0 xs) := by
      refine strictMonoOn_of_hasDerivAt_pos (hEc.mono (subc le_rfl hxs1.le))
        (fun x hx => hEd x (sub le_rfl hxs1.le hx)) (fun x hx => ?_)
      have hx' := sub le_rfl hxs1.le hx
      have : J xs < J x := hJ ⟨hx'.1.le, hx'.2.le⟩ ⟨hxs0.le, hxs1.le⟩ hx.2
      exact mul_pos (hK x hx') (by linarith)
    have hEneg : ∀ x ∈ Ioo a0 xs, E x < 0 := fun x hx => by
      have := hEmono ⟨hx.1.le, hx.2.le⟩ ⟨hxs0.le, le_rfl⟩ hx.2
      linarith
    have hΦanti : StrictAntiOn Φ (Icc a0 xs) := by
      refine strictAntiOn_of_hasDerivAt_neg (hΦc.mono (subc le_rfl hxs1.le))
        (fun x hx => hΦd x (sub le_rfl hxs1.le hx)) (fun x hx => ?_)
      exact mul_neg_of_neg_of_pos (hEneg x hx) (hP x (sub le_rfl hxs1.le hx))
    have := hΦanti ⟨le_rfl, hxs0.le⟩ ⟨hxs0.le, le_rfl⟩ hxs0
    linarith
  -- Step 2: a switching point y0
  obtain ⟨y0, hy0a, hy0x, hy0J, hy0left⟩ : ∃ y0, a0 ≤ y0 ∧ y0 < xs ∧ J y0 ≤ L ∧
      ∀ x, a0 ≤ x → x < y0 → L < J x := by
    by_cases h1 : J a0 ≤ L
    · exact ⟨a0, le_rfl, hxs0, h1, fun x hx hx' => by linarith⟩
    · push Not at h1
      have hcont : ContinuousOn J (Icc a0 xs) := hJc.mono (subc le_rfl hxs1.le)
      obtain ⟨y0, hy0, hy0e⟩ := intermediate_value_Icc' hxs0.le hcont ⟨step1.le, h1.le⟩
      have hy0lt : y0 < xs := lt_of_le_of_ne hy0.2 (by
        rintro rfl; linarith)
      refine ⟨y0, hy0.1, hy0lt, hy0e.le, fun x hx hx' => ?_⟩
      have : J y0 < J x := hJ ⟨hx, (hx'.le.trans hy0lt.le).trans hxs1.le⟩
        ⟨hy0.1, hy0lt.le.trans hxs1.le⟩ hx'
      linarith
  have hy0a1 : y0 < a1 := hy0x.trans hxs1
  -- Step 3: E decreasing on [y0, a1], Φ unimodal on [y0, a1]
  have hEanti : StrictAntiOn E (Icc y0 a1) := by
    refine strictAntiOn_of_hasDerivAt_neg (hEc.mono (subc hy0a le_rfl))
      (fun x hx => hEd x (sub hy0a le_rfl hx)) (fun x hx => ?_)
    have hx' := sub hy0a le_rfl hx
    have : J x < J y0 := hJ ⟨hy0a, hy0a1.le⟩ ⟨hx'.1.le, hx'.2.le⟩ hx.1
    exact mul_neg_of_pos_of_neg (hK x hx') (by linarith)
  have hEpos : ∀ x ∈ Ico y0 xs, 0 < E x := fun x hx => by
    have := hEanti ⟨hx.1, hx.2.le.trans hxs1.le⟩ ⟨hy0x.le, hxs1.le⟩ hx.2
    linarith
  have hEneg2 : ∀ x ∈ Ioc xs a1, E x < 0 := fun x hx => by
    have := hEanti ⟨hy0x.le, hxs1.le⟩ ⟨hx.1.le.trans' hy0x.le, hx.2⟩ hx.1
    linarith
  have hΦ_up : StrictMonoOn Φ (Icc y0 xs) := by
    refine strictMonoOn_of_hasDerivAt_pos (hΦc.mono (subc hy0a hxs1.le))
      (fun x hx => hΦd x (sub hy0a hxs1.le hx)) (fun x hx => ?_)
    exact mul_pos (hEpos x ⟨hx.1.le, hx.2⟩) (hP x (sub hy0a hxs1.le hx))
  have hΦ_down : StrictAntiOn Φ (Icc xs a1) := by
    refine strictAntiOn_of_hasDerivAt_neg (hΦc.mono (subc hxs0.le le_rfl))
      (fun x hx => hΦd x (sub hxs0.le le_rfl hx)) (fun x hx => ?_)
    exact mul_neg_of_neg_of_pos (hEneg2 x ⟨hx.1, hx.2.le⟩) (hP x (sub hxs0.le le_rfl hx))
  have hΦy0 : Φ y0 < Φ xs := hΦ_up ⟨le_rfl, hy0x.le⟩ ⟨hy0x.le, le_rfl⟩ hy0x
  -- Step 4: the left part [a0, y0)
  have hleft : ∀ x ∈ Icc a0 y0, Φ x < Φ xs := by
    intro x hx
    rcases hx.1.eq_or_lt with hxa | hxa
    · rw [← hxa]; exact hΦ1
    rcases hx.2.eq_or_lt with hxy | hxy
    · rw [hxy]; exact hΦy0
    -- E is strictly increasing on [a0, y0]
    have hEmono : StrictMonoOn E (Icc a0 y0) := by
      refine strictMonoOn_of_hasDerivAt_pos (hEc.mono (subc le_rfl hy0a1.le))
        (fun z hz => hEd z (sub le_rfl hy0a1.le hz)) (fun z hz => ?_)
      have hz' := sub le_rfl hy0a1.le hz
      have := hy0left z hz.1.le hz.2
      exact mul_pos (hK z hz') (by linarith)
    by_cases hEx : 0 ≤ E x
    · -- E > 0 on (x, y0): Φ increasing on [x, y0]
      have hup : StrictMonoOn Φ (Icc x y0) := by
        refine strictMonoOn_of_hasDerivAt_pos (hΦc.mono (subc hx.1 hy0a1.le))
          (fun z hz => hΦd z (sub hx.1 hy0a1.le hz)) (fun z hz => ?_)
        have : E x < E z := hEmono ⟨hx.1, hx.2⟩ ⟨hx.1.trans hz.1.le, hz.2.le⟩ hz.1
        exact mul_pos (by linarith) (hP z (sub hx.1 hy0a1.le hz))
      have := hup ⟨le_rfl, hxy.le⟩ ⟨hxy.le, le_rfl⟩ hxy
      linarith
    · push Not at hEx
      -- E < 0 on (a0, x): Φ decreasing on [a0, x]
      have hdown : StrictAntiOn Φ (Icc a0 x) := by
        refine strictAntiOn_of_hasDerivAt_neg (hΦc.mono (subc le_rfl (hxy.le.trans hy0a1.le)))
          (fun z hz => hΦd z (sub le_rfl (hxy.le.trans hy0a1.le) hz)) (fun z hz => ?_)
        have : E z < E x := hEmono ⟨hz.1.le, hz.2.le.trans hxy.le⟩ ⟨hx.1, hx.2⟩ hz.2
        exact mul_neg_of_neg_of_pos (by linarith) (hP z (sub le_rfl (hxy.le.trans hy0a1.le) hz))
      have := hdown ⟨le_rfl, hxa.le⟩ ⟨hxa.le, le_rfl⟩ hxa
      linarith
  -- assemble
  intro x hx hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rcases le_or_gt x y0 with h | h
    · exact hleft x ⟨hx.1, h⟩
    · exact hΦ_up ⟨h.le, hlt.le⟩ ⟨hy0x.le, le_rfl⟩ hlt
  · exact hΦ_down ⟨le_rfl, hgt.le.trans hx.2⟩ ⟨hgt.le, hx.2⟩ hgt

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.tangent_argument' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tangent_argument

end FormalResearch.FourQubitEntropy.RenyiFull
