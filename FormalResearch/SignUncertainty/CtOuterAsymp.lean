module

public import FormalResearch.SignUncertainty.CtOuterPhi0
public import FormalResearch.SignUncertainty.CtOuterTheta

/-!
# Large-`τ` behaviour of `θ_-`

**Proved.**  `θ_-(τ) + π/2 = φ(τ) + F_{ũ₁}(τ)` for `τ ≥ 5`, where `φ(τ) = ∫ ũ₀(t)/sinh(π(t-τ)) dt` has
`|φ^{(n)}(τ)| ≤ K_n e^{-πτ}` and `F_{ũ₁}` is `C^∞` with `|F_{ũ₁}^{(n)}(τ)| ≤ C_n (1+τ)² e^{-πτ}` for `τ ≥ 1`.
Hence `|θ_-(τ) + π/2| ≤ C (1+τ)² e^{-πτ}` and `|θ_-^{(n)}(τ)| ≤ C_n (1+τ)² e^{-π|τ|}` for `|τ| ≥ 1`, `n ≥ 1`.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty.CtOuter

/-- `(1+x) e^{-πx} ≤ 1`. -/
lemma q_le_one {x : ℝ} (hx : 0 ≤ x) : (1 + x) * Real.exp (-π * x) ≤ 1 := by
  have h1 : 1 + x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have h2 : Real.exp x * Real.exp (-π * x) ≤ 1 := by
    rw [← Real.exp_add]; apply Real.exp_le_one_iff.mpr; nlinarith only [Real.pi_gt_three, hx]
  calc (1 + x) * Real.exp (-π * x) ≤ Real.exp x * Real.exp (-π * x) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ ≤ 1 := h2

lemma utl1_bdd (n : ℕ) : ∃ B : ℝ, ∀ t : ℝ, |iteratedDeriv n utl1 t| ≤ B := by
  obtain ⟨A, hA⟩ := utl1_deriv_bound n
  refine ⟨|A|, fun t => (hA t).trans ?_⟩
  have h0 := q_le_one (abs_nonneg t)
  have h1 : 0 ≤ (1 + |t|) * Real.exp (-π * |t|) := by positivity
  calc A * ((1 + |t|) * Real.exp (-π * |t|)) ≤ |A| * ((1 + |t|) * Real.exp (-π * |t|)) :=
        mul_le_mul_of_nonneg_right (le_abs_self A) h1
    _ ≤ |A| * 1 := mul_le_mul_of_nonneg_left h0 (abs_nonneg A)
    _ = |A| := mul_one _

lemma hasDerivAt_iter_utl1 (m : ℕ) (t : ℝ) :
    HasDerivAt (iteratedDeriv m utl1) (iteratedDeriv (m + 1) utl1 t) t := by
  have := (contDiff_utl1.differentiable_iteratedDeriv m (by exact_mod_cast WithTop.coe_lt_top _)) t
  have h := this.hasDerivAt
  rwa [← iteratedDeriv_succ] at h

/-- `G = F_{ũ₁}`. -/
noncomputable def GF : ℝ → ℝ := bdryF utl1

lemma iteratedDeriv_GF (n : ℕ) : iteratedDeriv n GF = bdryF (iteratedDeriv n utl1) :=
  iteratedDeriv_bdryF contDiff_utl1 utl1_bdd n

lemma contDiff_GF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) GF := by
  have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) GF :=
    contDiff_of_differentiable_iteratedDeriv (n := ⊤) (fun m _ => by
      rw [iteratedDeriv_GF]
      intro τ
      obtain ⟨B0, hB0⟩ := utl1_bdd m
      obtain ⟨B1, hB1⟩ := utl1_bdd (m + 1)
      obtain ⟨B2, hB2⟩ := utl1_bdd (m + 2)
      exact (hasDerivAt_bdryF (hasDerivAt_iter_utl1 m) (hasDerivAt_iter_utl1 (m + 1)) hB0 hB1 hB2 τ).differentiableAt)
  exact h

/-- `|F_{ũ₁}^{(n)}(τ)| ≤ C (1+τ)² e^{-πτ}` for `τ ≥ 1`. -/
theorem GF_deriv_bound (n : ℕ) :
    ∃ C : ℝ, ∀ τ : ℝ, 1 ≤ τ → |iteratedDeriv n GF τ| ≤ C * ((1 + τ) ^ 2 * Real.exp (-π * τ)) := by
  obtain ⟨C0, hC0⟩ := bdryF_decay
  obtain ⟨A0, hA0⟩ := utl1_deriv_bound n
  obtain ⟨A1, hA1⟩ := utl1_deriv_bound (n + 1)
  refine ⟨C0 * (|A0| + |A1|), fun τ hτ => ?_⟩
  rw [iteratedDeriv_GF]
  have hq : ∀ t : ℝ, 0 ≤ (1 + |t|) * Real.exp (-π * |t|) := fun t => by positivity
  have h := hC0 (b := iteratedDeriv n utl1) (b' := iteratedDeriv (n + 1) utl1) (A := |A0| + |A1|)
    (hasDerivAt_iter_utl1 n)
    (fun t => (hA0 t).trans (mul_le_mul_of_nonneg_right (by linarith [le_abs_self A0, abs_nonneg A1]) (hq t)))
    (fun t => (hA1 t).trans (mul_le_mul_of_nonneg_right (by linarith [le_abs_self A1, abs_nonneg A0]) (hq t))) τ hτ
  exact h.trans (le_of_eq (by ring))

/-- **`θ_-(τ) + π/2 = φ(τ) + F_{ũ₁}(τ)` for `τ ≥ 5`.** -/
lemma theta_neg_split {τ : ℝ} (hτ : 5 ≤ τ) :
    outerTheta (-1) τ = phi0 utl0 τ + GF τ - π / 2 := by
  have hτ0 : 0 < τ := by linarith
  rw [outerTheta_neg_eq_utl hτ0]
  have e : utl = fun t => utl0 t + utl1 t := funext fun t => (utl0_add_utl1 t).symm
  obtain ⟨M0, hM0⟩ := abs_utl0_le
  obtain ⟨M1, hM1⟩ := abs_utl1_le
  obtain ⟨L, hL⟩ := uR_lipschitz τ
  obtain ⟨L', hL'⟩ := wpl_lipschitz hτ0
  have hLu : ∀ t : ℝ, |t - τ| ≤ 1 → |utl t - utl τ| ≤ (L + L') * |t - τ| := by
    intro t ht
    have h1 := hL t ht
    have h2 := hL' t (ht.trans (by linarith))
    unfold utl
    calc |uR t + wpl t - (uR τ + wpl τ)| = |(uR t - uR τ) + (wpl t - wpl τ)| := by ring_nf
      _ ≤ |uR t - uR τ| + |wpl t - wpl τ| := abs_add_le _ _
      _ ≤ L * |t - τ| + L' * |t - τ| := add_le_add h1 h2
      _ = _ := by ring
  have h := bdryF_add (a := utl0) (b := utl1) (τ := τ) (δ := 1) one_pos measurable_utl0 measurable_utl1 hM0 hM1
    (La := 0) (Lb := L + L')
    (fun t ht => by
      have h1 : 2 ≤ |t| := by
        have := (abs_le.mp ht).1
        rw [abs_of_pos (by linarith : (0 : ℝ) < t)]; linarith
      have h2 : 2 ≤ |τ| := by rw [abs_of_pos hτ0]; linarith
      rw [utl0_eq_zero h1, utl0_eq_zero h2]; simp)
    (fun t ht => by
      have h1 : 2 ≤ |t| := by
        have := (abs_le.mp ht).1
        rw [abs_of_pos (by linarith : (0 : ℝ) < t)]; linarith
      have h2 : 2 ≤ |τ| := by rw [abs_of_pos hτ0]; linarith
      rw [utl1_eq h1, utl1_eq h2]; exact hLu t ht)
  have h' : bdryF utl τ = bdryF utl0 τ + bdryF utl1 τ := by
    rw [e]; exact h
  rw [h', bdryF_eq_phi0 (a := utl0) (fun t ht => utl0_eq_zero (by linarith)) (by linarith)]
  rfl

/-- **Asymptotics of `θ_-`.** -/
theorem theta_neg_asymp : ∃ C : ℝ, ∀ τ : ℝ, 6 ≤ τ →
    |outerTheta (-1) τ + π / 2| ≤ C * ((1 + τ) ^ 2 * Real.exp (-π * τ)) := by
  obtain ⟨K, hK⟩ := phi0_deriv_bound measurable_utl0 integrable_utl0 (fun t ht => utl0_eq_zero (by linarith)) 0
  obtain ⟨C, hC⟩ := GF_deriv_bound 0
  refine ⟨|K| + |C|, fun τ hτ => ?_⟩
  have h1 := hK τ (by linarith)
  have h2 := hC τ (by linarith)
  simp only [iteratedDeriv_zero] at h1 h2
  rw [theta_neg_split (by linarith)]
  have e1 : Real.exp (-π * τ) ≤ (1 + τ) ^ 2 * Real.exp (-π * τ) := by
    have : (1 : ℝ) ≤ (1 + τ) ^ 2 := by nlinarith only [hτ]
    nlinarith only [this, Real.exp_pos (-π * τ)]
  have hX : 0 ≤ (1 + τ) ^ 2 * Real.exp (-π * τ) := by positivity
  calc |phi0 utl0 τ + GF τ - π / 2 + π / 2| = |phi0 utl0 τ + GF τ| := by ring_nf
    _ ≤ |phi0 utl0 τ| + |GF τ| := abs_add_le _ _
    _ ≤ K * Real.exp (-π * τ) + C * ((1 + τ) ^ 2 * Real.exp (-π * τ)) := add_le_add h1 h2
    _ ≤ |K| * ((1 + τ) ^ 2 * Real.exp (-π * τ)) + |C| * ((1 + τ) ^ 2 * Real.exp (-π * τ)) := by
        apply add_le_add
        · calc K * Real.exp (-π * τ) ≤ |K| * Real.exp (-π * τ) :=
              mul_le_mul_of_nonneg_right (le_abs_self K) (Real.exp_pos _).le
            _ ≤ |K| * ((1 + τ) ^ 2 * Real.exp (-π * τ)) := mul_le_mul_of_nonneg_left e1 (abs_nonneg K)
        · exact mul_le_mul_of_nonneg_right (le_abs_self C) hX
    _ = _ := by ring

/-- info: 'FormalResearch.SignUncertainty.CtOuter.theta_neg_asymp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms theta_neg_asymp

end FormalResearch.SignUncertainty.CtOuter
