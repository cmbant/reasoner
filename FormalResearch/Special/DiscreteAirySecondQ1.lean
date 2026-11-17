module

public import FormalResearch.Special.DiscreteAirySecondTransport
public import FormalResearch.Special.DiscreteAirySecondAssembly

/-!
# Second-order Airy parametrix, part 15: existence of `q₁` (Q1)

The `q₁`-residual equation `a2Res = 0` of `DiscreteAirySecondAssembly` is, after the closed-form identity
`d/dq [E₁(ζ, ζ')] = 2 lkds1` (`a2_hasDerivAt_E1`; it uses the Ch ODEs of order `0` and `1`), the singular transport equation
`2 W q₁' + W' q₁ = a2Src` with `W = A E₁(ζ,ζ') = A ζ ζ' Sh(ζζ'²)` (`a2Res_eq`), which has the **regular solution**
of `DiscreteAirySecondTransport`.  Here `W(c) = 0`, `ω = dslope W c > 0` (from `ζ' > 0`, `A > 0` and the amplitude relation
`g² A ζ' Sh = 1`, which gives `Ch' > 0`; and `ω(c) = A(c) ζ'(c)²`) and `a2Src ∈ C⁴`.

`airy2_q1_exists`: for `ζ ∈ C⁷`, `A, g ∈ C⁶`, `A₂, c₂ ∈ C⁴` on a ball `B(c, ρ)` around the turn (`ζ(c) = 0`, `ζ' > 0`, `A > 0`,
`hrel`) there is `q₁ ∈ C³(B)` with `a2Res ζ A A₂ g q₁ c₂ = 0` on `B`.  **Claim class: proved.**  This discharges the `q₁`-input of
`airy2_dai_full` near a simple turn (on a ball, not on all of `U`).
-/

@[expose] public section

open Set Metric

namespace FormalResearch.Special

/-- `d/dq E₁(ζ(q), ζ'(q)) = 2 lkds1` (uses the Ch ODEs at orders `0` and `1`). -/
lemma a2_hasDerivAt_E1 {ζ : ℝ → ℝ} {q : ℝ} (hz : HasDerivAt ζ (deriv ζ q) q)
    (hs : HasDerivAt (deriv ζ) (deriv (deriv ζ) q) q) :
    HasDerivAt (fun x => apuE1 (ζ x) (deriv ζ x))
      (2 * lkds1 (ζ q) (deriv ζ q) (deriv (deriv ζ) q)) q := by
  have hw : HasDerivAt (fun x => ζ x * deriv ζ x ^ 2) _ q := hz.mul (hs.pow 2)
  have hc : HasDerivAt (fun x => apuc 1 (ζ x * deriv ζ x ^ 2)) _ q :=
    (apuc_hasDerivAt 1 (ζ q * deriv ζ q ^ 2)).comp q hw
  have h1 : HasDerivAt (fun x => 2 * ζ x * deriv ζ x * apuc 1 (ζ x * deriv ζ x ^ 2)) _ q :=
    ((hz.const_mul 2).mul hs).mul hc
  unfold apuE1
  simp only [Pi.mul_apply, Nat.cast_ofNat, Nat.add_one_sub_one] at h1
  refine (h1.congr_deriv ?_)
  have o0 := apu2_ode 0 (ζ q * deriv ζ q ^ 2)
  have o1 := apu2_ode 1 (ζ q * deriv ζ q ^ 2)
  unfold lkds1 apuE apuO1
  simp only [Nat.reduceAdd, Nat.cast_zero, Nat.cast_one, mul_zero, mul_one] at *
  linear_combination (-(ζ q * deriv (deriv ζ) q)) * o0 - (deriv ζ q ^ 2) * o1

/-- The source term of the transport equation (`c₂ g - 2 [h²]𝔄[g, 0]`, with `p` omitted). -/
noncomputable def a2Src (ζ A A2 g c2 : ℝ → ℝ) (q : ℝ) : ℝ :=
  c2 q * g q - 2 * (a2G0 A g q * lkcs2 (ζ q) (deriv ζ q) (deriv (deriv ζ) q) (deriv (deriv (deriv ζ)) q) +
    a2G1 A g q * lkcs1 (ζ q) (deriv ζ q) (deriv (deriv ζ) q) +
    a2G2 A A2 g (fun _ => 0) q * apuE (ζ q) (deriv ζ q))

/-- The singular coefficient `W = A E₁(ζ, ζ') = A ζ ζ' Sh(ζ ζ'²)`. -/
noncomputable def a2W (ζ A : ℝ → ℝ) (q : ℝ) : ℝ := A q * apuE1 (ζ q) (deriv ζ q)
/-- Its derivative (closed form). -/
noncomputable def a2W' (ζ A : ℝ → ℝ) (q : ℝ) : ℝ :=
  deriv A q * apuE1 (ζ q) (deriv ζ q) + A q * (2 * lkds1 (ζ q) (deriv ζ q) (deriv (deriv ζ) q))

lemma a2_hasDerivAt_W {ζ A : ℝ → ℝ} {q : ℝ} (hA : HasDerivAt A (deriv A q) q)
    (hz : HasDerivAt ζ (deriv ζ q) q) (hs : HasDerivAt (deriv ζ) (deriv (deriv ζ) q) q) :
    HasDerivAt (a2W ζ A) (a2W' ζ A q) q :=
  hA.mul (a2_hasDerivAt_E1 hz hs)

/-- **The residual equation is the transport equation** `2 W q₁' + W' q₁ = a2Src`. -/
lemma a2Res_eq (ζ A A2 g q1 c2 : ℝ → ℝ) (q : ℝ) :
    a2Res ζ A A2 g q1 c2 q =
      2 * a2W ζ A q * deriv q1 q + a2W' ζ A q * q1 q - a2Src ζ A A2 g c2 q := by
  unfold a2Res a2Src a2W a2W' lkA2 a2H0 a2H1
  ring

/-- Iterated derivatives of a `C⁷` function inside a ball. -/
lemma a2_cd_derivs {c ρ : ℝ} {f : ℝ → ℝ} (hf : ContDiffOn ℝ 7 f (ball c ρ)) :
    ContDiffOn ℝ 6 (deriv f) (ball c ρ) ∧ ContDiffOn ℝ 5 (deriv (deriv f)) (ball c ρ) ∧
      ContDiffOn ℝ 4 (deriv (deriv (deriv f))) (ball c ρ) := by
  have h1 : ContDiffOn ℝ 6 (deriv f) (ball c ρ) := hf.deriv_of_isOpen isOpen_ball (by norm_num)
  have h2 : ContDiffOn ℝ 5 (deriv (deriv f)) (ball c ρ) := h1.deriv_of_isOpen isOpen_ball (by norm_num)
  exact ⟨h1, h2, h2.deriv_of_isOpen isOpen_ball (by norm_num)⟩

/-- **Smoothness of the source.** -/
lemma a2_cd_src {c ρ : ℝ} {ζ A A2 g c2 : ℝ → ℝ} (hζ : ContDiffOn ℝ 7 ζ (ball c ρ))
    (hA : ContDiffOn ℝ 6 A (ball c ρ)) (hA2 : ContDiffOn ℝ 4 A2 (ball c ρ)) (hg : ContDiffOn ℝ 6 g (ball c ρ))
    (hc2 : ContDiffOn ℝ 4 c2 (ball c ρ)) : ContDiffOn ℝ 4 (a2Src ζ A A2 g c2) (ball c ρ) := by
  obtain ⟨z1, z2, z3⟩ := a2_cd_derivs hζ
  have z0 : ContDiffOn ℝ 4 ζ (ball c ρ) := hζ.of_le (by norm_num)
  have z1' : ContDiffOn ℝ 4 (deriv ζ) (ball c ρ) := z1.of_le (by norm_num)
  have z2' : ContDiffOn ℝ 4 (deriv (deriv ζ)) (ball c ρ) := z2.of_le (by norm_num)
  have a1 : ContDiffOn ℝ 5 (deriv A) (ball c ρ) := hA.deriv_of_isOpen isOpen_ball (by norm_num)
  have a2 : ContDiffOn ℝ 4 (deriv (deriv A)) (ball c ρ) := a1.deriv_of_isOpen isOpen_ball (by norm_num)
  have g1 : ContDiffOn ℝ 5 (deriv g) (ball c ρ) := hg.deriv_of_isOpen isOpen_ball (by norm_num)
  have g2 : ContDiffOn ℝ 4 (deriv (deriv g)) (ball c ρ) := g1.deriv_of_isOpen isOpen_ball (by norm_num)
  have a0 : ContDiffOn ℝ 4 A (ball c ρ) := hA.of_le (by norm_num)
  have a1' : ContDiffOn ℝ 4 (deriv A) (ball c ρ) := a1.of_le (by norm_num)
  have g0 : ContDiffOn ℝ 4 g (ball c ρ) := hg.of_le (by norm_num)
  have g1' : ContDiffOn ℝ 4 (deriv g) (ball c ρ) := g1.of_le (by norm_num)
  have hcn : ∀ n : ℕ, ContDiff ℝ 4 (apuc n) := fun n => (apuc_contDiff n).of_le (by norm_num)
  have e : a2Src ζ A A2 g c2 = fun q => c2 q * g q - 2 * ((A q * g q) *
      (apuE1 (ζ q) (deriv ζ q) * (deriv (deriv (deriv ζ)) q / 6) +
        ζ q * apuE (ζ q) (deriv ζ q) * (deriv (deriv ζ) q / 2) ^ 2 / 2 +
        apuO1 (ζ q) (deriv ζ q) * (deriv (deriv ζ) q / 2) + apuC2 (ζ q) (deriv ζ q)) +
      (deriv A q * g q / 2 + A q * deriv g q) *
        (apuE1 (ζ q) (deriv ζ q) * (deriv (deriv ζ) q / 2) + apuO (ζ q) (deriv ζ q)) +
      (deriv (deriv A) q * g q / 8 + deriv A q * deriv g q / 2 + A q * (deriv (deriv g) q / 2) +
        A2 q * g q + A q * 0) * apuE (ζ q) (deriv ζ q)) := by
    funext q
    simp only [a2Src, lkcs1, lkcs2, a2G0, a2G1, a2G2]
  rw [e]
  unfold apuE apuE1 apuO apuO1 apuC2
  fun_prop

/-- `apuc 2 0 = 1/12`. -/
lemma a2_apuc_two_zero : apuc 2 0 = 1 / 12 := by
  have h := apu2_ode 1 0
  rw [apuc_one_at] at h
  norm_num at h
  linarith

/-- `ω(c) = A(c) ζ'(c)²`: the derivative of `W` at a zero of `ζ`. -/
lemma a2W'_at {ζ A : ℝ → ℝ} {c : ℝ} (hc : ζ c = 0) :
    a2W' ζ A c = A c * deriv ζ c ^ 2 := by
  unfold a2W' lkds1 apuO1 apuE1
  rw [hc]
  have h2 := a2_apuc_two_zero
  have h1 := apuc_one_at
  simp only [mul_zero, zero_mul, zero_add, add_zero]
  rw [h1, h2]
  ring

/-- **Positivity of `ω = dslope W c`** on a ball around a simple turn. -/
lemma a2_omega_pos {c ρ : ℝ} {ζ A g : ℝ → ℝ} (hζ : ContDiffOn ℝ 7 ζ (ball c ρ))
    (hA : ContDiffOn ℝ 6 A (ball c ρ)) (hc : ζ c = 0) (hρ : 0 < ρ)
    (hz' : ∀ q ∈ ball c ρ, 0 < deriv ζ q) (hApos : ∀ q ∈ ball c ρ, 0 < A q)
    (hrel : ∀ q ∈ ball c ρ,
      g q ^ 2 * A q * deriv ζ q * (2 * deriv langerCosh (ζ q * deriv ζ q ^ 2)) = 1) :
    ∀ q ∈ ball c ρ, 0 < dslope (a2W ζ A) c q := by
  intro q hq
  have hdiffA : ∀ x ∈ ball c ρ, HasDerivAt A (deriv A x) x := fun x hx =>
    ((hA.differentiableOn (by norm_num)).differentiableAt (isOpen_ball.mem_nhds hx)).hasDerivAt
  have hdiffz : ∀ x ∈ ball c ρ, HasDerivAt ζ (deriv ζ x) x := fun x hx =>
    ((hζ.differentiableOn (by norm_num)).differentiableAt (isOpen_ball.mem_nhds hx)).hasDerivAt
  obtain ⟨z1, -, -⟩ := a2_cd_derivs hζ
  have hdiffs : ∀ x ∈ ball c ρ, HasDerivAt (deriv ζ) (deriv (deriv ζ) x) x := fun x hx =>
    ((z1.differentiableOn (by norm_num)).differentiableAt (isOpen_ball.mem_nhds hx)).hasDerivAt
  have hcd : HasDerivAt (a2W ζ A) (a2W' ζ A c) c :=
    a2_hasDerivAt_W (hdiffA c (mem_ball_self hρ)) (hdiffz c (mem_ball_self hρ)) (hdiffs c (mem_ball_self hρ))
  have hW0 : a2W ζ A c = 0 := by simp [a2W, apuE1, hc]
  -- the derivative of Ch is positive along the curve
  have hCh : ∀ x ∈ ball c ρ, 0 < apuc 1 (ζ x * deriv ζ x ^ 2) := by
    intro x hx
    have h := hrel x hx
    have e : apuc 1 (ζ x * deriv ζ x ^ 2) = deriv langerCosh (ζ x * deriv ζ x ^ 2) := apuc_succ 0 _
    rw [e]
    by_contra hneg
    have hP : 0 ≤ g x ^ 2 * A x * deriv ζ x := by
      have := hApos x hx; have := hz' x hx; positivity
    nlinarith [mul_nonneg hP (by linarith : 0 ≤ -(2 * deriv langerCosh (ζ x * deriv ζ x ^ 2)))]
  by_cases hqc : q = c
  · subst hqc
    rw [dslope_same, hcd.deriv, a2W'_at hc]
    have := hApos q hq; have := hz' q hq; positivity
  · rw [dslope_of_ne _ hqc, slope_def_field, hW0, sub_zero]
    have hmono : StrictMonoOn ζ (ball c ρ) :=
      strictMonoOn_of_deriv_pos (convex_ball c ρ)
        (fun x hx => (hdiffz x hx).continuousAt.continuousWithinAt)
        (fun x hx => by rw [isOpen_ball.interior_eq] at hx; exact hz' x hx)
    have hAq := hApos q hq
    have hzq := hz' q hq
    have hch := hCh q hq
    unfold a2W apuE1
    rcases lt_or_gt_of_ne hqc with hlt | hgt
    · have hneg : ζ q < 0 := by rw [← hc]; exact hmono hq (mem_ball_self hρ) hlt
      have : 0 < A q * (2 * ζ q * deriv ζ q * apuc 1 (ζ q * deriv ζ q ^ 2)) / (q - c) := by
        apply div_pos_of_neg_of_neg
        · have : 0 < A q * (2 * (-ζ q) * deriv ζ q * apuc 1 (ζ q * deriv ζ q ^ 2)) := by
            have : 0 < -ζ q := by linarith
            positivity
          linarith
        · linarith
      exact this
    · have hpos : 0 < ζ q := by rw [← hc]; exact hmono (mem_ball_self hρ) hq hgt
      apply div_pos
      · positivity
      · linarith

lemma a2_cd_W {c ρ : ℝ} {ζ A : ℝ → ℝ} (hζ : ContDiffOn ℝ 7 ζ (ball c ρ))
    (hA : ContDiffOn ℝ 6 A (ball c ρ)) : ContDiffOn ℝ 5 (a2W ζ A) (ball c ρ) := by
  obtain ⟨z1, -, -⟩ := a2_cd_derivs hζ
  have hcn : ∀ n : ℕ, ContDiff ℝ 5 (apuc n) := fun n => (apuc_contDiff n).of_le (by norm_num)
  have z0 : ContDiffOn ℝ 5 ζ (ball c ρ) := hζ.of_le (by norm_num)
  have z1' : ContDiffOn ℝ 5 (deriv ζ) (ball c ρ) := z1.of_le (by norm_num)
  have a0 : ContDiffOn ℝ 5 A (ball c ρ) := hA.of_le (by norm_num)
  unfold a2W apuE1
  fun_prop

/-- **Existence of `q₁` (Q1).**  On a ball around a simple turn, with the first-order amplitude relation, the singular
transport equation `a2Res = 0` has a `C³` solution `q₁`. -/
theorem airy2_q1_exists {c ρ : ℝ} {ζ A A2 g c2 : ℝ → ℝ} (hρ : 0 < ρ)
    (hζ : ContDiffOn ℝ 7 ζ (ball c ρ)) (hA : ContDiffOn ℝ 6 A (ball c ρ))
    (hA2 : ContDiffOn ℝ 4 A2 (ball c ρ)) (hg : ContDiffOn ℝ 6 g (ball c ρ))
    (hc2 : ContDiffOn ℝ 4 c2 (ball c ρ)) (hc : ζ c = 0)
    (hz' : ∀ q ∈ ball c ρ, 0 < deriv ζ q) (hApos : ∀ q ∈ ball c ρ, 0 < A q)
    (hrel : ∀ q ∈ ball c ρ,
      g q ^ 2 * A q * deriv ζ q * (2 * deriv langerCosh (ζ q * deriv ζ q ^ 2)) = 1) :
    ∃ q1 : ℝ → ℝ, ContDiffOn ℝ 3 q1 (ball c ρ) ∧
      ∀ q ∈ ball c ρ, a2Res ζ A A2 g q1 c2 q = 0 := by
  have hW0 : a2W ζ A c = 0 := by simp [a2W, apuE1, hc]
  obtain ⟨q1, hq1, hq1e⟩ := transport_regular_solution (c := c) (ρ := ρ) 3 (by norm_num)
    (W := a2W ζ A) (f := a2Src ζ A A2 g c2) (a2_cd_W hζ hA) (a2_cd_src hζ hA hA2 hg hc2) hW0
    (a2_omega_pos hζ hA hc hρ hz' hApos hrel)
  refine ⟨q1, hq1, fun q hq => ?_⟩
  have hdiffA : HasDerivAt A (deriv A q) q :=
    ((hA.differentiableOn (by norm_num)).differentiableAt (isOpen_ball.mem_nhds hq)).hasDerivAt
  have hdiffz : HasDerivAt ζ (deriv ζ q) q :=
    ((hζ.differentiableOn (by norm_num)).differentiableAt (isOpen_ball.mem_nhds hq)).hasDerivAt
  obtain ⟨z1, -, -⟩ := a2_cd_derivs hζ
  have hdiffs : HasDerivAt (deriv ζ) (deriv (deriv ζ) q) q :=
    ((z1.differentiableOn (by norm_num)).differentiableAt (isOpen_ball.mem_nhds hq)).hasDerivAt
  have hd := (a2_hasDerivAt_W hdiffA hdiffz hdiffs).deriv
  have := hq1e q hq
  rw [hd] at this
  rw [a2Res_eq]
  linarith

/-- info: 'FormalResearch.Special.airy2_q1_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy2_q1_exists

end FormalResearch.Special
