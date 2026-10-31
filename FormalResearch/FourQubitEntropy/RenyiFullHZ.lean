import FormalResearch.FourQubitEntropy.RenyiFullProps

/-!
# The HS zone `F < 3/20` of `thm:fqe-renyi-classical` (case (2))

Paper E: the outer dual of `lem:fqe-hs-polynomial` and the case (HZ) of the proof of
`thm:fqe-renyi-classical`.

* `u_gt`, `kU_gt`: `3^{3/5} > 19/10` and `k > 7/3` (the paper has `k > 480/203`).
* `ell_hz_ge`: for `0 ≤ ε ≤ 1/9` and `0 ≤ F ≤ 3/20`,
  `ℓ_{(α,β,γ)}(ε,F) ≥ (149/324) ε + F (1/12 - 5F/9) ≥ 0`.
* `caseHZ`: assuming `HsSupporting`, a triple of the relaxation with `F < 3/20`, `20ε + 2F < 1`
  satisfies `E_{8/5} ≤ h_{8/5}`, with equality only when all three spectra are HS.
-/

namespace FormalResearch.FourQubitEntropy.RenyiFull

open FormalResearch.FourQubitEntropy

theorem u_gt : (19 / 10 : ℝ) < (3 : ℝ) ^ (3 / 5 : ℝ) := by
  have h5 : ((3 : ℝ) ^ (3 / 5 : ℝ)) ^ (5 : ℕ) = 27 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  by_contra hle
  push Not at hle
  have hpos : 0 ≤ (3 : ℝ) ^ (3 / 5 : ℝ) := by positivity
  have := pow_le_pow_left₀ hpos hle 5
  rw [h5] at this
  norm_num at this

theorem kU_gt : 7 / 3 < kU := by
  have hL0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL1 : Real.log 2 < 7 / 10 := by
    have := Real.log_two_lt_d9
    linarith
  set u := (3 : ℝ) ^ (3 / 5 : ℝ) with hu
  have hu1 := u_gt
  have hfrac : 9 / 29 ≤ (u - 1) / (u + 1) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  have hc : 16 / (3 * (7 / 10)) < 16 / (3 * Real.log 2) := by
    apply div_lt_div_of_pos_left (by norm_num) (by positivity) (by linarith)
  unfold kU
  rw [← hu]
  calc (7 / 3 : ℝ) < 16 / (3 * (7 / 10)) * (9 / 29) := by norm_num
    _ ≤ 16 / (3 * Real.log 2) * (9 / 29) := by
        apply mul_le_mul_of_nonneg_right hc.le (by norm_num)
    _ ≤ 16 / (3 * Real.log 2) * ((u - 1) / (u + 1)) := by
        apply mul_le_mul_of_nonneg_left hfrac (by positivity)

theorem aU_gt : 7 / 2 + 65 / 36 < aU := by
  have := kU_gt
  unfold aU
  linarith

/-- The outer dual of the HS zone: `ℓ ≥ 0` on `[0,1/9] × [0,3/20]`. -/
theorem ell_hz_ge {ε F : ℝ} (he0 : 0 ≤ ε) (he1 : ε ≤ 1 / 9) (hF0 : 0 ≤ F) (hF1 : F ≤ 3 / 20) :
    149 / 324 * ε + F * (1 / 12 - 5 / 9 * F) ≤ ell aU bU gU ε F := by
  have ha := aU_gt
  unfold ell bU gU
  nlinarith [mul_nonneg he0 (sub_nonneg.2 he1)]

theorem ell_hz_nonneg {ε F : ℝ} (he0 : 0 ≤ ε) (he1 : ε ≤ 1 / 9) (hF0 : 0 ≤ F) (hF1 : F ≤ 3 / 20) :
    0 ≤ ell aU bU gU ε F := by
  have := ell_hz_ge he0 he1 hF0 hF1
  have h1 : 0 ≤ 149 / 324 * ε := by positivity
  have h2 : 0 ≤ F * (1 / 12 - 5 / 9 * F) := mul_nonneg hF0 (by linarith)
  linarith

/-- Each cut purity of a triple with `P = 1 + ε`, `ε < 1/20`, is at most `9/16`. -/
theorem pur_le_of_triple {l₂ l₃ l₄ : Fin 4 → ℝ} (h₂ : IsProb4 l₂) (h₃ : IsProb4 l₃)
    (h₄ : IsProb4 l₄) {c : ℝ} (hc : Pm l₂ l₃ l₄ - 1 ≤ c) :
    pur l₂ ≤ 1 / 2 + c ∧ pur l₃ ≤ 1 / 2 + c ∧ pur l₄ ≤ 1 / 2 + c := by
  have q2 : 1 / 4 ≤ pur l₂ := pur_ge_quarter h₂
  have q3 : 1 / 4 ≤ pur l₃ := pur_ge_quarter h₃
  have q4 : 1 / 4 ≤ pur l₄ := pur_ge_quarter h₄
  unfold Pm at hc
  refine ⟨by linarith, by linarith, by linarith⟩


theorem qU_gt_one : 1 < qU := by unfold qU; norm_num
theorem qS_gt_one : 1 < qS := by unfold qS; norm_num

/-- **Case (2) of `thm:fqe-renyi-classical` (HZ).** From `HsSupporting`: a triple of the relaxation
with `F < 3/20` and `20ε + 2F < 1` has `E_{8/5} ≤ h_{8/5}`, with equality only for three HS spectra. -/
theorem caseHZ (hHZ : HsSupporting) {l₂ l₃ l₄ : Fin 4 → ℝ} (R : RelaxTriple l₂ l₃ l₄)
    (hF : Fm l₂ l₃ l₄ < 3 / 20) (hE : 20 * (Pm l₂ l₃ l₄ - 1) + 2 * Fm l₂ l₃ l₄ < 1) :
    Em qU l₂ l₃ l₄ ≤ hsq qU ∧ (Em qU l₂ l₃ l₄ = hsq qU → IsHsTriple l₂ l₃ l₄) := by
  have hF0 := R.F_ge
  have hP0 := R.P_ge
  have hε1 : Pm l₂ l₃ l₄ - 1 ≤ 1 / 20 := by linarith
  obtain ⟨q2, q3, q4⟩ := pur_le_of_triple R.prob₂ R.prob₃ R.prob₄ hε1
  have b2 : pur l₂ ≤ 9 / 16 := by linarith
  have b3 : pur l₃ ≤ 9 / 16 := by linarith
  have b4 : pur l₄ ≤ 9 / 16 := by linarith
  obtain ⟨s2, e2⟩ := hHZ l₂ R.prob₂ b2
  obtain ⟨s3, e3⟩ := hHZ l₃ R.prob₃ b3
  obtain ⟨s4, e4⟩ := hHZ l₄ R.prob₄ b4
  have hd := dual_bound R.QK qU aU bU gU (by unfold gU; norm_num)
  have hl := ell_hz_nonneg (ε := Pm l₂ l₃ l₄ - 1) (F := Fm l₂ l₃ l₄) (by linarith) (by linarith)
    hF0 hF.le
  have hEm : Em qU l₂ l₃ l₄ = (renyiSpec qU l₂ + renyiSpec qU l₃ + renyiSpec qU l₄) / 3 := rfl
  have hh : hsq qU = renyiSpec qU hsSpec := rfl
  refine ⟨by linarith, fun heq => ?_⟩
  -- equality forces each per-cut inequality to be an equality
  have t2 : Lam qU aU bU gU l₂ = renyiSpec qU hsSpec := by linarith
  have t3 : Lam qU aU bU gU l₃ = renyiSpec qU hsSpec := by linarith
  have t4 : Lam qU aU bU gU l₄ = renyiSpec qU hsSpec := by linarith
  exact ⟨e2 t2, e3 t3, e4 t4⟩

end FormalResearch.FourQubitEntropy.RenyiFull
