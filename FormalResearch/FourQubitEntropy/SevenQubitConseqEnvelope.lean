module

public import FormalResearch.FourQubitEntropy.EntropyPurityEnvelope

/-!
# `lem:seven-fixed-purity-envelope`: the entropy envelope at fixed eight-level purity

For `1/8 ≤ p ≤ 1` put `t(p) = (1 + √(7(8p-1)))/8` and
`g₈(p) = -t ln t - 7 · ((1-t)/7) ln ((1-t)/7)` (entropy in nats; the paper's `g₈` is this over `ln 2`).
Every probability vector `λ` on eight points with `∑ λ² = p` has `∑ -λ ln λ ≤ g₈(p)`.

This is the `d = 8` instance of the all-dimension envelope `EntropyPurity.entropy_le_gEnv`
(`EntropyPurityEnvelope.lean`, which also proves the equality case `entropy_eq_gEnv_iff`):
`g8 = gEnv 8` (`g8_eq_gEnv`).
-/

@[expose] public section


open Real Finset

namespace FormalResearch.FourQubitEntropy.SevenQubitConseq

/-- Entropy (nats) of the spike spectrum `(a, b, …, b)`, `b = (1-a)/7`. -/
noncomputable def Gsp (a : ℝ) : ℝ := negMulLog a + 7 * negMulLog ((1 - a) / 7)

/-- The spike weight `t(p)`. -/
noncomputable def tOf (p : ℝ) : ℝ := (1 + Real.sqrt (7 * (8 * p - 1))) / 8

/-- The envelope `g₈(p)` (nats). -/
noncomputable def g8 (p : ℝ) : ℝ := Gsp (tOf p)

theorem Gsp_eq_spikeEnt (a : ℝ) : Gsp a = EntropyPurity.spikeEnt 8 a := by
  unfold Gsp EntropyPurity.spikeEnt; norm_num

theorem g8_eq_gEnv (p : ℝ) : g8 p = EntropyPurity.gEnv 8 p := by
  unfold g8 tOf EntropyPurity.gEnv EntropyPurity.spikeWt
  rw [Gsp_eq_spikeEnt]; norm_num

theorem sum_sq_ge {ι : Type*} [Fintype ι] (hcard : Fintype.card ι = 8) (lam : ι → ℝ)
    (h1 : ∑ i, lam i = 1) : 1 / 8 ≤ ∑ i, lam i ^ 2 := by
  have := EntropyPurity.sum_sq_ge_inv hcard (by norm_num) lam h1
  norm_num at this ⊢; exact this

theorem sum_sq_le {ι : Type*} [Fintype ι] (lam : ι → ℝ) (h0 : ∀ i, 0 ≤ lam i)
    (h1 : ∑ i, lam i = 1) : ∑ i, lam i ^ 2 ≤ 1 :=
  EntropyPurity.sum_sq_le_one lam h0 h1

/-- **`lem:seven-fixed-purity-envelope` (entropy bound).**  For every probability vector `λ` on an
eight-point set with `∑ λ² = p`: `∑ -λ ln λ ≤ g₈(p)`. -/
theorem entropy_le_g8 {ι : Type*} [Fintype ι] (hcard : Fintype.card ι = 8) (lam : ι → ℝ)
    (h0 : ∀ i, 0 ≤ lam i) (h1 : ∑ i, lam i = 1) :
    ∑ i, negMulLog (lam i) ≤ g8 (∑ i, lam i ^ 2) := by
  have := EntropyPurity.entropy_le_gEnv (d := 8) (by norm_num) hcard lam h0 h1
  rw [g8_eq_gEnv]; exact_mod_cast this

end FormalResearch.FourQubitEntropy.SevenQubitConseq
