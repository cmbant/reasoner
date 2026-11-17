module

public import FormalResearch.Special.AiryCftQSample

/-!
# Theorem Q (4) for `Ai`, unconditional `HasSum`

With the sampling bound of Theorem Q (3) (`airyQ_sampling`, `AiryCftQSample`) the series `Σ_n f(a_n)/Ai'(a_n)²` converges absolutely
for every entire `f` with `‖f(u)‖ ≤ C (1+|u|)^ν e(u)` (**any real `ν`**, complex-valued `f`) and `f ∈ L¹(ℝ)`, so the `Summable` hypothesis of
`airyQ_hasSum` is dropped: `airyQ_hasSum_unc : HasSum (fun n => f(a_{n+1})/Ai'(a_{n+1})²) (∫_ℝ f)`.  (The range `ν ∈ [-1, 1/2]` of the note
is covered because `f ∈ L¹(ℝ)` is the only integrability input; Theorem Q (2) shows that every `f` in the class automatically has `ν ≤ 1/2`,
which is not needed here.)  **Proved.**
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

/-- **Theorem Q (4), unconditional.**  For `f` entire, `‖f(u)‖ ≤ C (1+|u|)^ν e(u)` (any real `ν`) and `f ∈ L¹(ℝ)`:
`∫_ℝ f = Σ_{n ≥ 1} f(a_n)/Ai'(a_n)²`, absolutely convergent. -/
theorem airyQ_hasSum_unc {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hfi : Integrable (fun x : ℝ => f (x : ℂ)))
    {C ν : ℝ} (hC : 0 ≤ C) (hb : ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u) :
    HasSum (fun n : ℕ => f (airyZero (n + 1) : ℂ) / (deriv airyAiC (airyZero (n + 1) : ℂ)) ^ 2)
      (∫ x : ℝ, f (x : ℂ)) := by
  obtain ⟨K, -, hK⟩ := airyQ_sampling
  obtain ⟨hs, -⟩ := hK hf hfi hC hb
  exact airyQ_hasSum hf hfi hC hb hs.of_norm

/-- info: 'FormalResearch.Special.airyQ_hasSum_unc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyQ_hasSum_unc

end FormalResearch.Special
