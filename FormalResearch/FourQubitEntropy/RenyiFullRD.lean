import FormalResearch.FourQubitEntropy.RenyiFullLowTilt
import FormalResearch.FourQubitEntropy.RenyiFullProps

/-!
# `lem:fqe-rational-dual`: the assembly from the two chart bounds

Paper E, `sup_renyi.tex` `lem:fqe-rational-dual`, whose proof is now the analytic assembly
low-tilt reduction + `lem:fqe-small-head-dual` + `lem:fqe-large-head-dual`.

* `SmallHeadDual`: every ordered `(a,b,c,c)` with `a ≤ 1/2` has `Λ_θ ≤ 8023/4800` (band `L`, `q_s`).
* `LargeHeadDual`: every ordered `(a,b,c,c)` with `1/2 ≤ a ≤ 4/5` has `Λ_θ < 2507333/1500000`.
* `rationalDual_of_heads`: `RationalDual` follows (`lam_reduce_abcc` at `q = q_s`, `β = 3/20`, and
  the purity cap `p ≤ 49/75 ⇒ a ≤ 4/5`).
-/

namespace FormalResearch.FourQubitEntropy.RenyiFull

open FormalResearch.FourQubitEntropy

/-- **`lem:fqe-small-head-dual`**: on the ordered chart `(a,b,c,c)` with `a ≤ 1/2`,
`Λ_θ ≤ 8023/4800 < 5/3 + 1837/375000 - 10⁻⁵` (`θ = (397/100, 3/20, 159/100)`, `q = q_s`). -/
def SmallHeadDual : Prop :=
  ∀ a b c : ℝ, 0 ≤ c → c ≤ b → b ≤ a → a ≤ 1 / 2 → a + b + 2 * c = 1 →
    Lam qS aL bL gL ![a, b, c, c] ≤ 8023 / 4800

/-- **`lem:fqe-large-head-dual`**: on the ordered chart `(a,b,c,c)` with `1/2 ≤ a ≤ 4/5`,
`Λ_θ < T = 2507333/1500000`. -/
def LargeHeadDual : Prop :=
  ∀ a b c : ℝ, 0 ≤ c → c ≤ b → b ≤ a → 1 / 2 ≤ a → a ≤ 4 / 5 → a + b + 2 * c = 1 →
    Lam qS aL bL gL ![a, b, c, c] < 2507333 / 1500000

theorem WL_sub_eps : WL - 1 / 100000 = 2507333 / 1500000 := by
  unfold WL ell aL bL gL
  norm_num [min_def]

theorem SmallHead_le_WL : (8023 / 4800 : ℝ) ≤ WL - 1 / 100000 := by
  rw [WL_sub_eps]; norm_num

theorem purity_cap_head {a b c : ℝ} (hc : 0 ≤ c) (hcb : c ≤ b) (hs : a + b + 2 * c = 1)
    (hp : pur ![a, b, c, c] ≤ 49 / 75) : a ≤ 4 / 5 := by
  rw [pur_abcc] at hp
  by_contra h
  push Not at h
  -- b + 2c = 1 - a, and b^2 + 2c^2 ≥ (1-a)^2/3 by Cauchy-Schwarz
  have h1 : b ^ 2 + 2 * c ^ 2 ≥ (1 - a) ^ 2 / 3 := by
    have : b + 2 * c = 1 - a := by linarith
    nlinarith [sq_nonneg (b - c)]
  nlinarith [sq_nonneg (a - 4 / 5)]

/-- **`lem:fqe-rational-dual`** from the two chart bounds. -/
theorem rationalDual_of_heads (hS : SmallHeadDual) (hLg : LargeHeadDual) : RationalDual := by
  intro l hl hp
  obtain ⟨ν, hν, ⟨a, b, c, hc, hcb, hba, hνe⟩, hpν, hle⟩ :=
    lam_reduce_abcc (q := qS) (β := bL) aL gL (by unfold qS; norm_num) (by unfold qS; norm_num)
      (by unfold bL; norm_num) (by unfold bL; norm_num) hl
  refine hle.trans ?_
  have hs : a + b + 2 * c = 1 := by
    have := hν.2
    rw [hνe] at this
    simp [Fin.sum_univ_four] at this
    linarith
  rw [hνe]
  rw [hνe] at hpν
  rw [WL_sub_eps]
  rcases le_total a (1 / 2) with h | h
  · exact (hS a b c hc hcb hba h hs).trans (by norm_num)
  · exact (hLg a b c hc hcb hba h (purity_cap_head hc hcb hs (hpν.trans_le hp)) hs).le

end FormalResearch.FourQubitEntropy.RenyiFull
