import FormalResearch.FourQubitEntropy.GOProbe.Final

/-!
# GO certificate: smoke test of the checker on a one-block toy certificate

One variable `x₀`, the constraint matrix `M = [[1]]`, one block with `p₀ = x₀`, `A = [[1]]`, `Δ = [[1]]`,
`grid = 1`, `s² = 2`, `cd = 1`: the weight is `H + Δ = 1 + 1 = 2`, the compact test `1 < 2·1` passes,
`U = 2 x₀²` and the single coordinate map is the identity, so `lit = 2 x₀²`.  Kernel-checked
(`decide +kernel`, no `native_decide`), and fed to `go_sound`.
-/

namespace FormalResearch.FourQubitEntropy.GOProbe

def smokeCons : List (List (List SP)) := [[[[(0, 1)]]]]

def smokeAct : List Nat × List Int := (List.range 19, List.replicate 19 1)

def smokeBlock : GBlock := ⟨0, [[(0, 1, 1)]], [[1]], [[1]], [[]]⟩

/-- `2 x₀²` (the key of `x₀²` is `2`). -/
def smokeLit : SP := [(2, 2)]

theorem smoke_check : check smokeCons [smokeAct] smokeLit 1 2 1 [smokeBlock] = true := by
  decide +kernel

/-- The toy certificate is sound: `2 x₀² ≥ 0` whenever the constant constraint `1` is PSD (always). -/
theorem smoke_sound (x : ℕ → ℝ)
    (h : ∀ g ∈ [smokeAct], ∀ c < smokeCons.length, Psd (act g x) (smokeCons.getD c [])) :
    0 ≤ ev x smokeLit :=
  go_sound smoke_check x h

end FormalResearch.FourQubitEntropy.GOProbe
