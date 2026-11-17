module

public import FormalResearch.Special.AiryCftSignUncertainty

/-!
# Theorem B at `u₁ = a₁`: all samples vanish (first half of the equality case)

CFT `AIRY_POISSON.md` §4, Theorem B′, Proof 2, step 4.  Let `f` be in the class of `AiryCftSignUncertainty` (entire, `L¹(ℝ)`,
`‖f(u)‖ ≤ C(1+|u|)^ν e(u)`, real on `ℝ`), `f ≥ 0` on `(-∞, a₁]` and `∫ f ≤ 0`.  Then (**proved**, `airy_sign_equality_samples`)

`∫ f = 0` and `f(a_n) = 0` for every `n ≥ 1`.

Proof (the note's step 4, with the unconditional translated quadrature `airy_shift_hasSum` in place of Theorem D): for `0 < ε < a₁ - a₂`
the real series `Σ_n f(a_n + ε)/Ai'(a_n)²` has sum `J = ∫ f ≤ 0`, and its terms with `n ≥ 2` are `≥ 0` (`a_n + ε ≤ a₂ + ε < a₁`), so
`t₁(ε) + t_m(ε) ≤ J` for every `m ≥ 2`; letting `ε → 0⁺` (continuity of `f`) and using `f(a_n) ≥ 0` gives `0 ≤ t₁(0) ≤ J ≤ 0` and
`t_m(0) ≤ J - t₁(0) ≤ 0`, so all samples vanish.

This is the generic half of the equality case.  **Not formalised:** the conclusion `f = c Ai²/(u - a₁)`, `c < 0`: with these vanishing samples
`f` has double zeros at `a_n` (`n ≥ 2`, since `f ≥ 0` around them), so `f/Ai²` has at most a simple pole at `a₁`; its polynomial growth on good circles
(lower bound `|Ai| ≥ c (1+|u|)^{-1/4} e^{1/2}` there, and the `𝒢_{1/2}` pointwise bound), Liouville, and `Ai² P ∈ L¹ ⇒ P = 0` are not formalised.
The converse (the extremal `-Ai²/(u - a₁)` satisfies all hypotheses with `∫ = 0`) is `airyExtremal_attains`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

/-- **Equality case, samples.**  Under the hypotheses of Theorem B with `u₁ = a₁` (`f ≥ 0` on `(-∞, a₁]`, `∫ f ≤ 0`), `∫ f = 0` and every
sample `f(a_n)` vanishes. -/
theorem airy_sign_equality_samples {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hfi : Integrable (fun x : ℝ => f (x : ℂ)))
    {C ν : ℝ} (hC : 0 ≤ C) (hb : ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u)
    (hreal : ∀ x : ℝ, (f (x : ℂ)).im = 0) (hpos : ∀ x : ℝ, x ≤ airyZero 1 → 0 ≤ (f (x : ℂ)).re)
    (hint : (∫ x : ℝ, (f (x : ℂ)).re) ≤ 0) :
    (∫ x : ℝ, (f (x : ℂ)).re) = 0 ∧ ∀ n : ℕ, 1 ≤ n → f (airyZero n : ℂ) = 0 := by
  set J : ℝ := ∫ x : ℝ, (f (x : ℂ)).re with hJ
  -- `t ε k = Re f(a_{k+1} + ε)/Ai'(a_{k+1})²`
  set t : ℝ → ℕ → ℝ := fun ε k => (f (((airyZero (k + 1) + ε : ℝ)) : ℂ)).re / (airyAi' (airyZero (k + 1))) ^ 2 with ht
  have hδ : 0 < airyZero 1 - airyZero 2 := by
    have := airyZero_strictAnti (n := 1) le_rfl; linarith
  -- positivity of the terms with `k ≥ 1`
  have hpos' : ∀ ε : ℝ, 0 ≤ ε → ε < airyZero 1 - airyZero 2 → ∀ k : ℕ, 1 ≤ k → 0 ≤ t ε k := by
    intro ε hε0 hε k hk
    refine div_nonneg (hpos _ ?_) (sq_nonneg _)
    have h1 : airyZero (k + 1) ≤ airyZero 2 := airyZero_le_of_le (by norm_num) (by omega)
    linarith
  -- `t ε 0 + t ε m ≤ J` and `t ε 0 ≤ J`
  have hmain : ∀ ε : ℝ, 0 < ε → ε < airyZero 1 - airyZero 2 → ∀ T : Finset ℕ, (∀ k ∈ T, 1 ≤ k) →
      ∑ k ∈ insert 0 T, t ε k ≤ J := by
    intro ε hε0 hε T hT
    refine sum_le_hasSum (insert 0 T) (fun k hk => ?_) (airy_shift_hasSum hf hfi hC hb hreal hε0.le)
    have : k ≠ 0 := fun h => hk (by simp [h])
    exact hpos' ε hε0.le hε k (by omega)
  -- continuity in `ε`
  have hcont : ∀ k : ℕ, Continuous (fun ε : ℝ => t ε k) := by
    intro k
    have : Continuous (fun ε : ℝ => (f (((airyZero (k + 1) + ε : ℝ)) : ℂ)).re) :=
      Complex.continuous_re.comp (hf.continuous.comp (Complex.continuous_ofReal.comp (continuous_const.add continuous_id)))
    exact this.div_const _
  have hlim : ∀ T : Finset ℕ, (∀ k ∈ T, 1 ≤ k) → ∑ k ∈ insert 0 T, t 0 k ≤ J := by
    intro T hT
    have hc : Continuous (fun ε : ℝ => ∑ k ∈ insert 0 T, t ε k) := continuous_finsetSum _ fun k _ => hcont k
    have h1 : Tendsto (fun ε : ℝ => ∑ k ∈ insert 0 T, t ε k) (𝓝[>] 0) (𝓝 (∑ k ∈ insert 0 T, t 0 k)) :=
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    refine le_of_tendsto h1 ?_
    filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
    exact hmain ε hε.1 hε.2 T hT
  have ht0 : ∀ k : ℕ, 0 ≤ t 0 k := fun k => by
    refine div_nonneg (hpos _ ?_) (sq_nonneg _)
    have h1 : airyZero (k + 1) ≤ airyZero 1 := airyZero_le_of_le le_rfl (by omega)
    simpa using h1
  have hJ0 : t 0 0 ≤ J := by simpa using hlim ∅ (by simp)
  have hJz : J = 0 := le_antisymm hint ((ht0 0).trans hJ0)
  have hall : ∀ m : ℕ, 1 ≤ m → t 0 m = 0 := by
    intro m hm
    have h := hlim {m} (by simpa using hm)
    rw [Finset.sum_insert (by simp; omega), Finset.sum_singleton] at h
    have := ht0 0
    have := ht0 m
    linarith
  have hfirst : t 0 0 = 0 := by linarith [ht0 0]
  refine ⟨hJz, fun n hn => ?_⟩
  have hk : t 0 (n - 1) = 0 := by
    rcases Nat.eq_zero_or_pos (n - 1) with h0 | hp
    · rw [h0]; exact hfirst
    · exact hall (n - 1) hp
  simp only [ht, add_zero] at hk
  have e : n - 1 + 1 = n := by omega
  rw [e] at hk
  have hre0 : (f (airyZero n : ℂ)).re = 0 := by
    rcases div_eq_zero_iff.1 hk with h | h
    · exact h
    · exfalso
      have hz : airyAi (airyZero n) = 0 := airyAi_airyZero n
      have := airyKer_pos' (airyZero n)
      rw [hz] at this
      have h2 : airyAi' (airyZero n) ^ 2 - airyZero n * (0 : ℝ) ^ 2 = airyAi' (airyZero n) ^ 2 := by ring
      rw [h2] at this
      exact this.ne' h
  rw [airy_real_cast hreal, hre0]; simp

/-- info: 'FormalResearch.Special.airy_sign_equality_samples' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy_sign_equality_samples

end FormalResearch.Special
