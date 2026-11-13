module

public import Mathlib

/-!
# Uniqueness of the affine centering (Weyl P2, `prop:unique`): the exact algebraic core

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, section *The midpoint is uniquely forced*.

The proposition compares the canonical centered lengths `A = a + (n+1)/2`, `B = b + (m+1)/2`,
`C = c + 1/2` with trial lengths `A' = a+u`, `B' = b+v`, `C' = c+w`; with
`Δ_A = n+1-2u`, `Δ_B = m+1-2v`, `Δ_C = 1-2w` one has `A = A' + Δ_A/2`, etc.  Under the dilation
`A' = Λα`, `B' = Λβ`, `C' = Λγ` the angle `x = cosA(A,B,C)` equals (degree-`0` homogeneity)
`cosShape(α + ε Δ_A/2, β + ε Δ_B/2, γ + ε Δ_C/2)` with `ε = 1/Λ`.  The `Λ⁻¹`-term of the exact
recurrence is `(2f+1) λ_f X₁`, where `X₁` is the `ε`-derivative of this expression at `ε = 0`.

What is formalised (all exact, no asymptotics):

* `cosShape_trial`: the homogeneity identity above;
* `hasDerivAt_trial`: `X₁ = driftX1` (`eq:6juniquenongeneric`), i.e. the first-order Taylor
  coefficient of the angle in `ε = 1/Λ`;
* `driftX1_eq_zero_iff`, `unique_affine_core`: if `X₁` vanishes on a nonempty open set of shapes
  (with `α, β > 0`) then `Δ_A = Δ_B = Δ_C = 0` (the polynomial identity of the proof), and conversely;
* `prop_unique_algebra`: in terms of `u, v, w`: `X₁ = 0` on an open set iff
  `u = (n+1)/2`, `v = (m+1)/2`, `w = 1/2`.

Not formalised (analysis in `Λ`): the expansions `E(k)/(4A'B'R_k) = 1 + s/Λ + O(Λ⁻²)` and the
statement that the admitted `f`-independent normalisations remove everything but `X₁`; these are
the part of the proof of `prop:unique` that is asymptotic and is not an exact finite statement.
-/

@[expose] public section

namespace FormalResearch.Racah.SixJ

/-- The law-of-cosines angle of a shape `(α, β, γ)`. -/
noncomputable def cosShape (α β γ : ℝ) : ℝ := (α ^ 2 + β ^ 2 - γ ^ 2) / (2 * α * β)

/-- `A = A' + Δ_A/2` etc. with `A' = Λα`: the canonical angle is the angle of the shifted shape
(`cosA` is homogeneous of degree `0`). -/
theorem cosShape_trial (Λ α β γ ΔA ΔB ΔC : ℝ) (hΛ : Λ ≠ 0) :
    ((Λ * α + ΔA / 2) ^ 2 + (Λ * β + ΔB / 2) ^ 2 - (Λ * γ + ΔC / 2) ^ 2) /
        (2 * (Λ * α + ΔA / 2) * (Λ * β + ΔB / 2)) =
      cosShape (α + (1 / Λ) * (ΔA / 2)) (β + (1 / Λ) * (ΔB / 2)) (γ + (1 / Λ) * (ΔC / 2)) := by
  unfold cosShape
  have e1 : α + 1 / Λ * (ΔA / 2) = (Λ * α + ΔA / 2) / Λ := by field_simp
  have e2 : β + 1 / Λ * (ΔB / 2) = (Λ * β + ΔB / 2) / Λ := by field_simp
  have e3 : γ + 1 / Λ * (ΔC / 2) = (Λ * γ + ΔC / 2) / Λ := by field_simp
  rw [e1, e2, e3]
  generalize Λ * α + ΔA / 2 = A
  generalize Λ * β + ΔB / 2 = B
  generalize Λ * γ + ΔC / 2 = C
  by_cases hA : A = 0
  · simp [hA]
  by_cases hB : B = 0
  · simp [hB]
  field_simp

/-- The first-order drift `X₁` of the law-of-cosines point (`eq:6juniquenongeneric`). -/
noncomputable def driftX1 (ΔA ΔB ΔC α β γ : ℝ) : ℝ :=
  ΔA * (α ^ 2 - β ^ 2 + γ ^ 2) / (4 * α ^ 2 * β) +
    ΔB * (β ^ 2 - α ^ 2 + γ ^ 2) / (4 * α * β ^ 2) - ΔC * γ / (2 * α * β)

/-- `X₁` is the `ε`-derivative at `ε = 0` (`ε = 1/Λ`) of the angle of the shifted shape: the
`Λ⁻¹` coefficient in `x = x' + X₁/Λ + O(Λ⁻²)` (`eq:6jtrialangle`). -/
theorem hasDerivAt_trial (ΔA ΔB ΔC α β γ : ℝ) (hα : α ≠ 0) (hβ : β ≠ 0) :
    HasDerivAt (fun ε : ℝ => cosShape (α + ε * (ΔA / 2)) (β + ε * (ΔB / 2)) (γ + ε * (ΔC / 2)))
      (driftX1 ΔA ΔB ΔC α β γ) 0 := by
  have hA : HasDerivAt (fun ε : ℝ => α + ε * (ΔA / 2)) (ΔA / 2) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (ΔA / 2)).const_add α
  have hB : HasDerivAt (fun ε : ℝ => β + ε * (ΔB / 2)) (ΔB / 2) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (ΔB / 2)).const_add β
  have hC : HasDerivAt (fun ε : ℝ => γ + ε * (ΔC / 2)) (ΔC / 2) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (ΔC / 2)).const_add γ
  have hN := ((hA.pow 2).add (hB.pow 2)).sub (hC.pow 2)
  have hD := ((hA.const_mul 2).mul hB)
  have hD0 : (fun ε : ℝ => 2 * (α + ε * (ΔA / 2)) * (β + ε * (ΔB / 2))) 0 ≠ 0 := by
    simp only [zero_mul, add_zero]
    exact mul_ne_zero (mul_ne_zero two_ne_zero hα) hβ
  have h := hN.div hD hD0
  unfold cosShape
  refine h.congr_deriv ?_
  unfold driftX1
  simp only [Pi.add_apply, Pi.pow_apply, Pi.sub_apply, Pi.mul_apply, zero_mul, add_zero]
  field_simp
  ring

/-- The polynomial identity of the proof: `X₁ = 0` iff
`Δ_A β(α²-β²+γ²) + Δ_B α(β²-α²+γ²) - 2Δ_C αβγ = 0` (for `α, β ≠ 0`). -/
theorem driftX1_eq_zero_iff (ΔA ΔB ΔC α β γ : ℝ) (hα : α ≠ 0) (hβ : β ≠ 0) :
    driftX1 ΔA ΔB ΔC α β γ = 0 ↔
      ΔA * β * (α ^ 2 - β ^ 2 + γ ^ 2) + ΔB * α * (β ^ 2 - α ^ 2 + γ ^ 2) -
        2 * ΔC * α * β * γ = 0 := by
  have e : driftX1 ΔA ΔB ΔC α β γ =
      (ΔA * β * (α ^ 2 - β ^ 2 + γ ^ 2) + ΔB * α * (β ^ 2 - α ^ 2 + γ ^ 2) -
        2 * ΔC * α * β * γ) / (4 * α ^ 2 * β ^ 2) := by
    unfold driftX1
    field_simp
    ring
  rw [e, div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact h
    · exfalso
      have : (4 : ℝ) * α ^ 2 * β ^ 2 ≠ 0 := by positivity
      exact this h
  · intro h; exact Or.inl h

/-- A quadratic `p + qγ + rγ²` vanishing at `γ₀ - δ, γ₀, γ₀ + δ` (`δ ≠ 0`) has `q = r = 0`
when expressed through the coefficients at `γ₀`; used with the explicit coefficients below. -/
private lemma quad_zero (P : ℝ → ℝ) (r q p γ₀ δ : ℝ) (hδ : δ ≠ 0)
    (hP : ∀ γ, P γ = p + q * γ + r * γ ^ 2)
    (h0 : P γ₀ = 0) (h1 : P (γ₀ + δ) = 0) (h2 : P (γ₀ - δ) = 0) : r = 0 ∧ q + 2 * r * γ₀ = 0 := by
  rw [hP] at h0 h1 h2
  have hr : r * δ ^ 2 = 0 := by nlinarith
  have hδ2 : δ ^ 2 ≠ 0 := pow_ne_zero 2 hδ
  have hr0 : r = 0 := by
    rcases mul_eq_zero.mp hr with h | h
    · exact h
    · exact absurd h hδ2
  subst hr0
  refine ⟨rfl, ?_⟩
  have : q * δ = 0 := by nlinarith
  rcases mul_eq_zero.mp this with h | h
  · simpa using h
  · exact absurd h hδ

/-- **`prop:unique`, exact core.**  If `X₁` vanishes on a nonempty open set of shapes
`(α, β, γ)` with `α, β > 0` (the strict-triangle shapes), then `Δ_A = Δ_B = Δ_C = 0`. -/
theorem unique_affine_core (ΔA ΔB ΔC : ℝ) (U : Set (ℝ × ℝ × ℝ)) (hU : IsOpen U) (hne : U.Nonempty)
    (hpos : ∀ p ∈ U, 0 < p.1 ∧ 0 < p.2.1)
    (hX : ∀ p ∈ U, driftX1 ΔA ΔB ΔC p.1 p.2.1 p.2.2 = 0) :
    ΔA = 0 ∧ ΔB = 0 ∧ ΔC = 0 := by
  obtain ⟨⟨α₀, β₀, γ₀⟩, hp0⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU _ hp0
  -- the polynomial identity on the ball
  have hPoly : ∀ α β γ : ℝ, (α, β, γ) ∈ U →
      ΔA * β * (α ^ 2 - β ^ 2 + γ ^ 2) + ΔB * α * (β ^ 2 - α ^ 2 + γ ^ 2) -
        2 * ΔC * α * β * γ = 0 := by
    intro α β γ hm
    have := hpos _ hm
    exact (driftX1_eq_zero_iff ΔA ΔB ΔC α β γ this.1.ne' this.2.ne').mp (hX _ hm)
  have hmem : ∀ α β γ : ℝ, |α - α₀| < ε → |β - β₀| < ε → |γ - γ₀| < ε → (α, β, γ) ∈ U := by
    intro α β γ h1 h2 h3
    apply hball
    rw [Metric.mem_ball, Prod.dist_eq, Prod.dist_eq]
    simp only [Real.dist_eq]
    refine max_lt h1 (max_lt h2 h3)
  have hδ : ε / 3 ≠ 0 := by positivity
  -- for each `(α, β)` near `(α₀, β₀)`: both quadratic coefficients vanish
  have hcoef : ∀ α β : ℝ, |α - α₀| < ε → |β - β₀| < ε →
      (ΔA * β + ΔB * α = 0) ∧ (-2 * ΔC * α * β + 2 * (ΔA * β + ΔB * α) * γ₀ = 0) := by
    intro α β h1 h2
    have hs : ∀ t : ℝ, |t| < ε → ΔA * β * (α ^ 2 - β ^ 2 + (γ₀ + t) ^ 2) +
        ΔB * α * (β ^ 2 - α ^ 2 + (γ₀ + t) ^ 2) - 2 * ΔC * α * β * (γ₀ + t) = 0 := by
      intro t ht
      apply hPoly
      apply hmem α β _ h1 h2
      simpa using ht
    have e0 := hs 0 (by simpa using hε)
    have e1 := hs (ε / 3) (by rw [abs_of_pos (by positivity)]; linarith)
    have e2 := hs (-(ε / 3)) (by rw [abs_neg, abs_of_pos (by positivity)]; linarith)
    have := quad_zero (fun γ => ΔA * β * (α ^ 2 - β ^ 2 + γ ^ 2) + ΔB * α * (β ^ 2 - α ^ 2 + γ ^ 2) -
        2 * ΔC * α * β * γ) (ΔA * β + ΔB * α) (-2 * ΔC * α * β)
      (ΔA * β * (α ^ 2 - β ^ 2) + ΔB * α * (β ^ 2 - α ^ 2)) γ₀ (ε / 3) hδ
      (fun γ => by ring) (by simpa using e0) (by simpa using e1) (by simpa [sub_eq_add_neg] using e2)
    exact ⟨this.1, by linarith [this.2]⟩
  obtain ⟨c0, c0'⟩ := hcoef α₀ β₀ (by simpa using hε) (by simpa using hε)
  obtain ⟨c1, -⟩ := hcoef (α₀ + ε / 2) β₀ (by rw [add_sub_cancel_left, abs_of_pos (by positivity)]; linarith)
    (by simpa using hε)
  obtain ⟨c2, -⟩ := hcoef α₀ (β₀ + ε / 2) (by simpa using hε)
    (by rw [add_sub_cancel_left, abs_of_pos (by positivity)]; linarith)
  have hα0 := (hpos _ hp0).1
  have hβ0 := (hpos _ hp0).2
  have hB0 : ΔB = 0 := by
    have : ΔB * (ε / 2) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exfalso; have : ε / 2 ≠ 0 := by positivity
      exact this h
  have hA0 : ΔA = 0 := by
    have : ΔA * (ε / 2) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exfalso; have : ε / 2 ≠ 0 := by positivity
      exact this h
  refine ⟨hA0, hB0, ?_⟩
  rw [hA0, hB0] at c0'
  have : ΔC * (α₀ * β₀) = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · exact h
  · exfalso; have : α₀ * β₀ ≠ 0 := by positivity
    exact this h

/-- **`prop:unique`** (uniqueness of the affine centering, exact algebraic content).  With
`Δ_A = n+1-2u`, `Δ_B = m+1-2v`, `Δ_C = 1-2w`: the first-order drift `X₁` of the trial angle
vanishes on a nonempty open set of strict-triangle shapes if and only if
`u = (n+1)/2`, `v = (m+1)/2`, `w = 1/2`. -/
theorem prop_unique_algebra (m n u v w : ℝ) (U : Set (ℝ × ℝ × ℝ)) (hU : IsOpen U) (hne : U.Nonempty)
    (hpos : ∀ p ∈ U, 0 < p.1 ∧ 0 < p.2.1) :
    (∀ p ∈ U, driftX1 (n + 1 - 2 * u) (m + 1 - 2 * v) (1 - 2 * w) p.1 p.2.1 p.2.2 = 0) ↔
      (u = (n + 1) / 2 ∧ v = (m + 1) / 2 ∧ w = 1 / 2) := by
  constructor
  · intro h
    obtain ⟨hA, hB, hC⟩ := unique_affine_core _ _ _ U hU hne hpos h
    refine ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨rfl, rfl, rfl⟩ p _
    unfold driftX1
    ring_nf

/-- info: 'FormalResearch.Racah.SixJ.prop_unique_algebra' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prop_unique_algebra

/-- info: 'FormalResearch.Racah.SixJ.hasDerivAt_trial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_trial

end FormalResearch.Racah.SixJ
