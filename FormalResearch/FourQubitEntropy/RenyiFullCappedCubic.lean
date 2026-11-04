module

public import FormalResearch.FourQubitEntropy.RenyiFullCCMoment
public import FormalResearch.FourQubitEntropy.RenyiFullCCPairs
public import FormalResearch.FourQubitEntropy.RenyiFullDetChart
public import FormalResearch.FourQubitEntropy.RenyiFullProps

/-!
# `lem:fqe-capped-cubic` (CG): proved

Paper E, `lem:fqe-capped-cubic` (`renyi_capped_cubic.tex`).  `CappedCubic` (`RenyiFullProps.lean`) is proved here,
without hypothesis, in the following steps (`q = q_s = 1587/1000`, `x = p - 1/4`):

1. `p ≤ 21/50` (`x ≤ 17/100`): the moment argument `cc_moment` (`RenyiFullCCMoment.lean`: Taylor through degree five,
   `ln N` concave in `x`, the curvature and endpoint cells of `gen_cc_cells.py`);
2. `21/50 < p ≤ 47/100`: `det_reduction` to the two ordered charts `S`, `B`; Jensen grouping and the weight estimates
   (`entS_cc`, `entB_cc`, CG3, `RenyiFullCCPairs.lean`); and the two binary quartic bounds
   `bin_quartic1`, `bin_quartic2` (`RenyiFullCCBinary.lean`), consequences of the binary quartic lemma
   (`RenyiFullBQBinary.lean`: `A_q` increasing at `q_s`), combined in `cc_final_ineq`.
-/

@[expose] public section


namespace FormalResearch.FourQubitEntropy.RenyiFull

open FormalResearch.FourQubitEntropy

/-- The last step of the pair charts: `h(u) ≤ 4u(1-u) - (11/10) d (1/4 - d)` with `d = u - u² - v/2`. -/
theorem cc_final_ineq {u v : ℝ} (hu1 : 3 / 100 ≤ u) (hu2 : u ≤ 4 / 15) (hv0 : 0 ≤ v)
    (hd1 : 3 / 100 ≤ u - u ^ 2 - v / 2) (hd2 : u - u ^ 2 - v / 2 ≤ 2 / 25) :
    binH qBQ u ≤ 4 * u * (1 - u) - 11 / 10 * ((u - u ^ 2 - v / 2) * (1 / 4 - (u - u ^ 2 - v / 2))) := by
  set d := u - u ^ 2 - v / 2 with hd
  have hd0 : d ≤ u * (1 - u) := by rw [hd]; nlinarith
  rcases le_total u (1 / 12) with h | h
  · have hq := bin_quartic1 hu1 (by linarith)
    have hd0' : u * (1 - u) ≤ 11 / 144 := by nlinarith
    have e : (1 - 2 * u) ^ 2 = 1 - 4 * (u * (1 - u)) := by ring
    rw [e] at hq
    have key : d * (1 - 4 * d) ≤ u * (1 - u) * (1 - 4 * (u * (1 - u))) := by
      have : 0 ≤ (u * (1 - u) - d) * (1 - 4 * (u * (1 - u) + d)) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith
    nlinarith
  · have hq := bin_quartic2 h (by linarith)
    have e : (1 - 2 * u) ^ 2 = 1 - 4 * (u * (1 - u)) := by ring
    rw [e] at hq
    have hlo : 11 / 144 ≤ u * (1 - u) := by nlinarith
    have hhi : u * (1 - u) ≤ 44 / 225 := by nlinarith
    have hf : 399 / 10000 ≤ u * (1 - u) * (1 - 4 * (u * (1 - u))) := by
      nlinarith [mul_nonneg (show 0 ≤ u * (1 - u) - 11 / 144 by linarith)
        (show 0 ≤ 44 / 225 - u * (1 - u) by linarith)]
    have hdd : d * (1 / 4 - d) ≤ 17 / 100 * (2 / 25) := by
      nlinarith [mul_nonneg (show 0 ≤ 2 / 25 - d by linarith) (show 0 ≤ d by linarith)]
    nlinarith

/-- The target of `CappedCubic`, as a function of `(p, t)`. -/
noncomputable def ccTarget (p t : ℝ) : ℝ :=
  10 / 3 - 6 * p + 8 / 3 * t - 11 / 10 * (p - 1 / 4) * (1 / 2 - p)

/-- Pair chart `S`. -/
theorem cc_pairS {u δ : ℝ} (hu0 : 0 ≤ u) (hδ0 : 0 ≤ δ) (hδ2 : δ ≤ 1 - 2 * u)
    (hp1 : 21 / 50 ≤ slp u (δ ^ 2)) (hp2 : slp u (δ ^ 2) ≤ 47 / 100) :
    renyiSpec qS (muS u δ) ≤ ccTarget (slp u (δ ^ 2)) (slt (1 - u) u (δ ^ 2)) := by
  unfold slp at hp1 hp2
  have hv : δ ^ 2 ≤ (1 - 2 * u) ^ 2 := by nlinarith
  have hu12 : u ≤ 1 / 2 := by nlinarith
  have hu3 : 3 / 100 ≤ u := by nlinarith [sq_nonneg δ]
  have hu4 : u ≤ 4 / 15 := by
    by_contra hcon
    push Not at hcon
    nlinarith [mul_nonneg (show 0 ≤ u - 4 / 15 by linarith) (show 0 ≤ 1 / 2 - u by linarith)]
  have hv2 : δ ^ 2 ≤ 2 / 3 * (1 - u) ^ 2 := by
    nlinarith [sq_nonneg (u - 4 / 15), mul_nonneg (show 0 ≤ 4 / 15 - u by linarith) (show 0 ≤ u by linarith)]
  have hE := entS_cc hu3 hu4 hδ0 hv2
  have hF := cc_final_ineq (u := u) (v := δ ^ 2) hu3 hu4 (sq_nonneg δ) (by nlinarith) (by nlinarith)
  have hE' : renyiSpec qS (muS u δ) ≤ 1 + binH qBQ u - (1 + 2 * u) * δ ^ 2 := hE
  unfold ccTarget slp slt
  nlinarith [hE', hF]

/-- Pair chart `B`. -/
theorem cc_pairB {u δ : ℝ} (hδ0 : 0 ≤ δ) (hδu : δ ≤ u) (hu2 : 2 * u ≤ 1)
    (hp1 : 21 / 50 ≤ slp u (δ ^ 2)) (hp2 : slp u (δ ^ 2) ≤ 47 / 100) :
    renyiSpec qS (muB u δ) ≤ ccTarget (slp u (δ ^ 2)) (slt u u (δ ^ 2)) := by
  unfold slp at hp1 hp2
  have hu0 : 0 ≤ u := by linarith
  have hv : δ ^ 2 ≤ u ^ 2 := by nlinarith
  have hu3 : 3 / 100 ≤ u := by nlinarith [sq_nonneg δ]
  have hu4 : u ≤ 3 / 32 := by
    by_contra hcon
    push Not at hcon
    nlinarith [mul_nonneg (show 0 ≤ u - 3 / 32 by linarith) (show 0 ≤ 1 / 2 - u by linarith)]
  have hE := entB_cc hu3 hu4 hδ0 hδu
  have hF := cc_final_ineq (u := u) (v := δ ^ 2) hu3 (by linarith) (sq_nonneg δ) (by nlinarith) (by nlinarith)
  have hE' : renyiSpec qS (muB u δ) ≤ 1 + binH qBQ u - (3 - 2 * u) * δ ^ 2 := hE
  unfold ccTarget slp slt
  nlinarith [hE', hF]

/-- **`lem:fqe-capped-cubic` (CG), proved.** -/
theorem cappedCubic : CappedCubic := by
  intro l hl hp
  have hq := pur_ge_quarter hl
  have htarget : 10 / 3 - 6 * pur l + 8 / 3 * cub l - 11 / 10 * (pur l - 1 / 4) * (1 / 2 - pur l) =
      ccTarget (pur l) (cub l) := rfl
  rw [htarget]
  have h1 : (1 : ℝ) < qS := qS_gt_one
  have h2 : qS < 2 := qS_lt_two
  rcases hq.eq_or_lt with h | h
  · -- uniform spectrum
    have hu := pur_eq_quarter hl h.symm
    have hl2 : l = c2 := by funext i; rw [hu i]; unfold c2; fin_cases i <;> simp
    subst hl2
    rw [renyiSpec_c2 (by linarith) h1.ne', pur_c2, cub_c2]
    unfold ccTarget; norm_num
  · by_cases hx : pur l ≤ 21 / 50
    · -- moment case
      have hm := cc_moment hl (by linarith) (by linarith)
      unfold ccTarget
      nlinarith [hm]
    · -- pair charts
      push Not at hx
      obtain ⟨μ, hμ, hpμ, htμ, hHμ⟩ := det_reduction qS h1 h2 l hl
      have hmain : renyiSpec qS μ ≤ ccTarget (pur μ) (cub μ) := by
        obtain ⟨⟨hnn, hsum⟩, a, b, c, hc0, hcb, hba, hform⟩ := hμ
        simp only [Fin.sum_univ_four] at hsum
        rcases hform with rfl | rfl
        · have hsum' : a + b + c + c = 1 := by simpa using hsum
          have hμ' : (![a, b, c, c] : Fin 4 → ℝ) = muS (2 * c) (a - b) := by
            funext i; fin_cases i <;> simp [muS] <;> linarith
          rw [hμ'] at hpμ htμ ⊢
          rw [pur_muS] at hpμ ⊢
          rw [cub_muS] at htμ ⊢
          have hp1 : 21 / 50 ≤ slp (2 * c) ((a - b) ^ 2) := by linarith [hpμ]
          have hp2 : slp (2 * c) ((a - b) ^ 2) ≤ 47 / 100 := by linarith [hpμ]
          exact cc_pairS (by linarith) (by linarith) (by linarith) hp1 hp2
        · have hsum' : a + a + b + c = 1 := by simpa using hsum
          have hμ' : (![a, a, b, c] : Fin 4 → ℝ) = muB (1 - 2 * a) (b - c) := by
            funext i; fin_cases i <;> simp [muB] <;> linarith
          rw [hμ'] at hpμ htμ ⊢
          rw [pur_muB] at hpμ ⊢
          rw [cub_muB] at htμ ⊢
          have hp1 : 21 / 50 ≤ slp (1 - 2 * a) ((b - c) ^ 2) := by linarith [hpμ]
          have hp2 : slp (1 - 2 * a) ((b - c) ^ 2) ≤ 47 / 100 := by linarith [hpμ]
          exact cc_pairB (by linarith) (by linarith) (by linarith) hp1 hp2
      rw [hpμ, htμ] at hmain
      exact hHμ.trans hmain

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.cappedCubic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cappedCubic

end FormalResearch.FourQubitEntropy.RenyiFull
