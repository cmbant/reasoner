module

public import FormalResearch.FourQubitEntropy.RenyiFullSHLarge

/-!
# Small-head dual: assembly of the large tail and of `lem:fqe-small-head-dual`

`sh_large_tail`: `Λ_θ ≤ Λ_θ(c₂) = 8023/4800` on `((1-u+δ)/2, (1-u-δ)/2, u/2, u/2)`, `1/4 ≤ u ≤ 1/2`,
`0 ≤ δ ≤ min(u, 1-2u)`.  `smallHeadDual : SmallHeadDual` combines it with `sh_small_tail`.
-/

@[expose] public section


namespace FormalResearch.FourQubitEntropy.RenyiFull

theorem Lam_c2_sub_Lam_L {l : Fin 4 → ℝ} :
    Lam qS aL bL gL c2 - Lam qS aL bL gL l =
      (2 - renyiSpec qS l) - (aL + 8 * bL - gL / 2) * (pur l - 1 / 4) +
        12 * bL * (cub l - 1 / 16 - 3 / 4 * (pur l - 1 / 4)) + gL * (pur l - 1 / 4) ^ 2 := by
  have h1 : qS ≠ 1 := by unfold qS; norm_num
  rw [Lam_c2 (by unfold qS; norm_num) h1]
  unfold Lam
  ring

theorem Lam_c2_value : Lam qS aL bL gL c2 = 8023 / 4800 := by
  rw [Lam_c2 (by unfold qS; norm_num) (by unfold qS; norm_num)]
  unfold aL bL gL; norm_num

theorem sh_large_tail {u δ : ℝ} (hu1 : 1 / 4 ≤ u) (hu2 : u ≤ 1 / 2) (hδ0 : 0 ≤ δ) (hδu : δ ≤ u)
    (hδ2 : δ ≤ 1 - 2 * u) :
    Lam qS aL bL gL ![(1 - u + δ) / 2, (1 - u - δ) / 2, u / 2, u / 2] ≤ 8023 / 4800 := by
  set l : Fin 4 → ℝ := ![(1 - u + δ) / 2, (1 - u - δ) / 2, u / 2, u / 2] with hl
  have hprob : IsProb4 l := by
    constructor
    · intro i; fin_cases i <;> simp [hl] <;> linarith
    · simp [hl, Fin.sum_univ_four]; ring
  have hx : pur l - 1 / 4 = (1 / 2 - u) ^ 2 + δ ^ 2 / 2 := by rw [hl, pur_sh]; ring
  have hy : cub l - 1 / 16 - 3 / 4 * (pur l - 1 / 4) = 3 / 4 * (1 / 2 - u) * δ ^ 2 := by
    rw [hl, cub_sh, pur_sh]; ring
  have hxle : (1 / 2 - u) ^ 2 + δ ^ 2 / 2 ≤ 3 / 32 := by nlinarith
  rcases (show 0 ≤ (1 / 2 - u) ^ 2 + δ ^ 2 / 2 by positivity).eq_or_lt with h0 | hpos
  · -- uniform
    have hu : u = 1 / 2 := by nlinarith [sq_nonneg (1 / 2 - u), sq_nonneg δ]
    have hδ : δ = 0 := by nlinarith [sq_nonneg (1 / 2 - u), sq_nonneg δ]
    have : l = c2 := by
      rw [hl, hu, hδ]; unfold c2; ext i; fin_cases i <;> simp <;> norm_num
    rw [this, Lam_c2_value]
  · have hx0 : 0 < pur l - 1 / 4 := by rw [hx]; exact hpos
    have hy0 : 0 ≤ cub l - 1 / 16 - 3 / 4 * (pur l - 1 / 4) := by
      rw [hy]; have : 0 ≤ 1 / 2 - u := by linarith
      positivity
    have hy1 : cub l - 1 / 16 - 3 / 4 * (pur l - 1 / 4) ≤ 9 / 50 * (pur l - 1 / 4) := by
      rw [hy, hx]
      nlinarith [mul_nonneg hδ0 hδ0, mul_nonneg (sub_nonneg.2 hδ2) (sub_nonneg.2 hu2),
        mul_nonneg (sub_nonneg.2 hδu) (sub_nonneg.2 hu2), mul_nonneg hδ0 (sub_nonneg.2 hu2),
        mul_nonneg (mul_nonneg hδ0 hδ0) (sub_nonneg.2 hu2)]
    have hE := sh_large_entropy hprob hx0 (by rw [hx]; exact hxle) hy0 hy1
    have hid := Lam_c2_sub_Lam_L (l := l)
    set x := pur l - 1 / 4 with hxd
    set y := cub l - 1 / 16 - 3 / 4 * x with hyd
    have hxy : x * (y / x) = y := by field_simp
    have : 0 ≤ Lam qS aL bL gL c2 - Lam qS aL bL gL l := by
      rw [hid]
      unfold aL bL gL
      nlinarith [hE, hxy]
    rw [Lam_c2_value] at this
    linarith

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.sh_large_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sh_large_tail

end FormalResearch.FourQubitEntropy.RenyiFull
