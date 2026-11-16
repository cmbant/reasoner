module

public import FormalResearch.Special.DiscreteAirySecondPair
public import FormalResearch.Special.AiryParametrixJets

/-!
# Second-order Airy parametrix, part 7: uniform jets of the data on a compact set

Uniform (in `q ∈ J` compact) bounds and Taylor remainders for `C⁴`, `C³`, `C¹` functions, and their translation into the
jet calculus `Ex3` over an arbitrary parameter type with `q : α → ℝ`, `hh : α → ℝ`:

* `sj_jet4`: `C⁴` (used for `ζ`): `|ζ(q+s) - (ζ + ζ' s + ζ'' s²/2 + ζ''' s³/6)| ≤ B₄ |s|⁴`;
* `Ex3.of_q3`: for `f ∈ C³`, `f(q + c·hh)` is `Ex3 [f, c f', c² f''/2]`;
* `SOB.lip1`: for `f ∈ C¹`, `hh² (f(q + c·hh) - f(q)) ∈ SOB 3`.

**Claim class: proved.**
-/

@[expose] public section

open Set

namespace FormalResearch.Special

/-- Fourth-order jet of a `C⁴` function on a compact `J ⊆ U`. -/
theorem sj_jet4 {f : ℝ → ℝ} {U J : Set ℝ} (hU : IsOpen U) (hf : ContDiffOn ℝ 4 f U)
    (hJ : IsCompact J) (hJU : J ⊆ U) :
    ∃ M0 M1 M2 M3 M4 δ : ℝ, 0 ≤ M0 ∧ 0 ≤ M1 ∧ 0 ≤ M2 ∧ 0 ≤ M3 ∧ 0 ≤ M4 ∧ 0 < δ ∧ ∀ q ∈ J,
      |f q| ≤ M0 ∧ |deriv f q| ≤ M1 ∧ |deriv (deriv f) q| ≤ M2 ∧ |deriv (deriv (deriv f)) q| ≤ M3 ∧
      ∀ s : ℝ, |s| ≤ δ → |f (q + s) - (f q + deriv f q * s + deriv (deriv f) q * s ^ 2 / 2 +
        deriv (deriv (deriv f)) q * s ^ 3 / 6)| ≤ M4 * |s| ^ 4 := by
  obtain ⟨δ, hδ, hcth⟩ := hJ.exists_cthickening_subset_open hU hJU
  obtain ⟨B, hB0, hB⟩ := apx_taylor_J (n := 4) hU hf hJ hcth
  obtain ⟨M0, hM0, h0⟩ := apx_bound_iterate hU hf hJ hJU 0 (by norm_num)
  obtain ⟨M1, hM1, h1⟩ := apx_bound_iterate hU hf hJ hJU 1 (by norm_num)
  obtain ⟨M2, hM2, h2⟩ := apx_bound_iterate hU hf hJ hJU 2 (by norm_num)
  obtain ⟨M3, hM3, h3⟩ := apx_bound_iterate hU hf hJ hJU 3 (by norm_num)
  have it2 : ∀ x, deriv^[2] f x = deriv (deriv f) x := by
    intro x; simp [Function.iterate_succ_apply']
  have it3 : ∀ x, deriv^[3] f x = deriv (deriv (deriv f)) x := by
    intro x; simp [Function.iterate_succ_apply']
  refine ⟨M0, M1, M2, M3, B, δ, hM0, hM1, hM2, hM3, hB0, hδ, fun q hq => ⟨by simpa using h0 q hq,
    by simpa using h1 q hq, by simpa [it2] using h2 q hq, by simpa [it3] using h3 q hq, fun s hs => ?_⟩⟩
  have := hB q hq s hs
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Function.iterate_zero, id_eq,
    Function.iterate_one, it2, it3, Nat.factorial, pow_zero, pow_one] at this
  convert this using 3; norm_num

/-- First-order jet of a `C¹` function on a compact `J ⊆ U`. -/
theorem sj_jet1 {f : ℝ → ℝ} {U J : Set ℝ} (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    (hJ : IsCompact J) (hJU : J ⊆ U) :
    ∃ M0 M1 δ : ℝ, 0 ≤ M0 ∧ 0 ≤ M1 ∧ 0 < δ ∧ ∀ q ∈ J, |f q| ≤ M0 ∧
      ∀ s : ℝ, |s| ≤ δ → |f (q + s) - f q| ≤ M1 * |s| := by
  obtain ⟨δ, hδ, hcth⟩ := hJ.exists_cthickening_subset_open hU hJU
  obtain ⟨B, hB0, hB⟩ := apx_taylor_J (n := 1) hU hf hJ hcth
  obtain ⟨M0, hM0, h0⟩ := apx_bound_iterate hU hf hJ hJU 0 (by norm_num)
  refine ⟨M0, B, δ, hM0, hB0, hδ, fun q hq => ⟨by simpa using h0 q hq, fun s hs => ?_⟩⟩
  have := hB q hq s hs
  simpa using this

section Calc

variable {α : Type*} {D : α → Prop} {hh q : α → ℝ}

/-- **`C³` function at the shifted point as a third-order jet.** -/
theorem Ex3.of_q3 {f : ℝ → ℝ} {U J : Set ℝ} (hU : IsOpen U) (hf : ContDiffOn ℝ 3 f U)
    (hJ : IsCompact J) (hJU : J ⊆ U) (c : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ {α : Type} (D : α → Prop) (hh q : α → ℝ), (∀ a, D a → q a ∈ J) →
      (∀ a, D a → |c| * |hh a| ≤ δ) →
      Ex3 D hh (fun a => f (q a + c * hh a)) (fun a => f (q a)) (fun a => c * deriv f (q a))
        (fun a => c ^ 2 * deriv (deriv f) (q a) / 2) := by
  obtain ⟨M0, M1, M2, M3, δ, hM0, hM1, hM2, hM3, hδ, hj⟩ := apx_jet3 hU hf hJ hJU
  refine ⟨δ, hδ, fun {α} D hh q hq hc => ?_⟩
  have hb : ∀ a, D a → |f (q a + c * hh a) - (f (q a) + deriv f (q a) * (c * hh a) +
      deriv (deriv f) (q a) * (c * hh a) ^ 2 / 2)| ≤ M3 * |c * hh a| ^ 3 := fun a ha => by
    refine (hj (q a) (hq a ha)).2.2.2 (c * hh a) ?_ 
    rw [abs_mul]; exact hc a ha
  refine ⟨⟨M3 * |c| ^ 3, by positivity, fun a ha => ?_⟩, ?_, ?_, ?_⟩
  · have := hb a ha
    rw [abs_mul] at this
    have e : f (q a + c * hh a) - (f (q a) + hh a * (c * deriv f (q a)) +
        hh a ^ 2 * (c ^ 2 * deriv (deriv f) (q a) / 2)) = f (q a + c * hh a) - (f (q a) + deriv f (q a) * (c * hh a) +
            deriv (deriv f) (q a) * (c * hh a) ^ 2 / 2) := by ring
    show |f (q a + c * hh a) - (f (q a) + hh a * (c * deriv f (q a)) +
        hh a ^ 2 * (c ^ 2 * deriv (deriv f) (q a) / 2))| ≤ _
    rw [e]
    calc _ ≤ M3 * (|c| * |hh a|) ^ 3 := this
      _ = _ := by ring
  · exact SOB.bdd (M := M0) fun a ha => (hj (q a) (hq a ha)).1
  · exact SOB.bdd (M := |c| * M1) fun a ha => by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hj (q a) (hq a ha)).2.1 (abs_nonneg _)
  · exact SOB.bdd (M := c ^ 2 * M2 / 2) fun a ha => by
      have := (hj (q a) (hq a ha)).2.2.1
      rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg c), abs_two]
      have h2 : c ^ 2 * |deriv (deriv f) (q a)| ≤ c ^ 2 * M2 := mul_le_mul_of_nonneg_left this (sq_nonneg c)
      linarith

/-- **`hh² (f(q + c hh) - f(q)) = O(hh³)` for a `C¹` function.** -/
theorem SOB.lip1 {f : ℝ → ℝ} {U J : Set ℝ} (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    (hJ : IsCompact J) (hJU : J ⊆ U) (c : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ {α : Type} (D : α → Prop) (hh q : α → ℝ), (∀ a, D a → q a ∈ J) →
      (∀ a, D a → |c| * |hh a| ≤ δ) →
      SOB D hh 3 (fun a => hh a ^ 2 * (f (q a + c * hh a) - f (q a))) ∧ SOB D hh 0 (fun a => f (q a)) := by
  obtain ⟨M0, M1, δ, hM0, hM1, hδ, hj⟩ := sj_jet1 hU hf hJ hJU
  refine ⟨δ, hδ, fun {α} D hh q hq hc => ⟨⟨M1 * |c|, by positivity, fun a ha => ?_⟩,
    SOB.bdd (M := M0) fun a ha => (hj (q a) (hq a ha)).1⟩⟩
  have := (hj (q a) (hq a ha)).2 (c * hh a) (by rw [abs_mul]; exact hc a ha)
  rw [abs_mul] at this
  show |hh a ^ 2 * (f (q a + c * hh a) - f (q a))| ≤ _
  rw [abs_mul, abs_pow]
  calc |hh a| ^ 2 * |f (q a + c * hh a) - f (q a)| ≤ |hh a| ^ 2 * (M1 * (|c| * |hh a|)) :=
        mul_le_mul_of_nonneg_left this (sq_nonneg _)
    _ = _ := by ring

end Calc

end FormalResearch.Special
