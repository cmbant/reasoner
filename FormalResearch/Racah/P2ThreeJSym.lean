module

public import FormalResearch.Racah.P2ThreeJSeed

/-!
# Symmetries of the Regge-midpoint kernel and the spin-`1/2` chambers (Weyl P2)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `eq:3jseed` ff., `rem:spinhalf`.

* `Phi3j_neg_M`: the simultaneous sign symmetry (`threeJ_neg`) in the paper's variables:
  `Φ_L^{-M,σ}(-x) = (-1)^{L-σ} Φ_L^{M,σ}(x)` (`μ ↦ -μ`, i.e. `x ↦ -x`; `j_±` unchanged).  The sign is
  `N`- and `μ`-independent, because `j_++m_+ ∈ ℤ`.
* `Phi3j_half_pp`, `Phi3j_half_pm`, `Phi3j_half_mp`, `Phi3j_half_mm`: `rem:spinhalf` for all
  four chambers `M, σ ∈ {±1/2}`, exactly:
  `Φ_{1/2}^{M,σ}(x;h) = d^{1/2}_{Mσ}(arccos x)/√(1-h²/4)` where the half-angle values are written as
  `d_{++} = d_{--} = √((1+x)/2)`, `d_{+-} = -√((1-x)/2)`, `d_{-+} = √((1-x)/2)` (these are
  `cos(θ/2)`, `-sin(θ/2)`, `sin(θ/2)`, `cos(θ/2)` at `x = cos θ`); the identification with
  `d^{1/2}_{Mσ}(θ)` itself is not formalised (Mathlib has no Wigner `d`).
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner

/-- **Simultaneous sign symmetry in the midpoint variables**:
`Φ_L^{-M,σ}(-x) = (-1)^{L-σ} Φ_L^{M,σ}(x)`, in the form `μ ↦ -μ`.  Hypotheses: `2L`,
`2j_+ = N-1+σ`, `L-σ`, `j_++m_+` are integers (the paper's standing integrality). -/
theorem Phi3j_neg_M (L M σ N μ : ℚ) (hL : ∃ n : ℤ, 2 * L = n)
    (ht : ∃ n : ℤ, N - 1 + σ = n) (hk : ∃ n : ℤ, L - σ = n)
    (hc : ∃ n : ℤ, jPlus N σ + mPlus M μ = n) :
    Phi3j L (-M) σ N (-μ) = sgn (L - σ) * Phi3j L M σ N μ := by
  obtain ⟨l, hl⟩ := hL
  obtain ⟨t, ht⟩ := ht
  obtain ⟨k, hk⟩ := hk
  obtain ⟨c, hc⟩ := hc
  have e1 : mMinus (-M) (-μ) = -(mMinus M μ) := by unfold mMinus; ring
  have e2 : mPlus (-M) (-μ) = -(mPlus M μ) := by unfold mPlus; ring
  unfold Phi3j
  rw [e1, e2, threeJ_neg]
  have s1 : 2 * L + jPlus N σ + -(mPlus M μ) = (((l + t - c : ℤ)) : ℚ) := by
    unfold jPlus mPlus at *; push_cast; linarith
  have s2 : L + jMinus N σ + jPlus N σ = (((k + t : ℤ)) : ℚ) := by
    unfold jMinus jPlus; push_cast; linarith
  have s3 : 2 * L + jPlus N σ + mPlus M μ = (((l + c : ℤ)) : ℚ) := by
    unfold jPlus mPlus at *; push_cast; linarith
  have s4 : L - σ = ((k : ℤ) : ℚ) := by exact_mod_cast hk
  rw [s1, s2, s3, s4, sgn_intCast, sgn_intCast, sgn_intCast, sgn_intCast]
  have : (-1 : ℝ) ^ (l + t - c) * (-1 : ℝ) ^ (k + t) =
      (-1 : ℝ) ^ k * (-1 : ℝ) ^ (l + c) := by
    rw [← zpow_add₀ (by norm_num), ← zpow_add₀ (by norm_num),
      show l + t - c + (k + t) = (k + (l + c)) + 2 * (t - c) by ring,
      neg_one_zpow_add_two_mul]
  linear_combination (Real.sqrt (N : ℝ) *
    threeJ L (jMinus N σ) (jPlus N σ) M (mMinus M μ) (mPlus M μ)) * this

lemma Cprod_two_one (h : ℝ) : Cprod (1 + 0 + 1) 1 h = 1 - h ^ 2 / 4 := by
  rw [show 1 + 0 + 1 = 0 + 2 by rfl, Cprod_succ_succ, Cprod_zero]
  push_cast; ring

lemma sgn_zero' : sgn (0 : ℚ) = 1 := by
  have := sgn_intCast 0
  simpa using this

lemma sgn_one' : sgn (1 : ℚ) = -1 := by
  have := sgn_intCast 1
  simpa using this

lemma half_hyp_pm (N μ : ℚ) (a c : ℕ) (ha : jMinus N (1 / 2) + mMinus (1 / 2) μ = a)
    (hc : jPlus N (1 / 2) + mPlus (1 / 2) μ = c) :
    (∃ n : ℤ, N - 1 + 1 / 2 = n) := by
  refine ⟨(a : ℤ) + c + 1, ?_⟩
  unfold jMinus jPlus mMinus mPlus at *
  push_cast; linarith

/-- `rem:spinhalf`, chamber `M = σ = 1/2`: `Φ = √((1+x)/2)/√(1-h²/4)`, `x = 2μ/N`, `h = 1/N`. -/
theorem Phi3j_half_pp (N μ : ℚ) (a c : ℕ) (ha : jMinus N (1 / 2) + mMinus (1 / 2) μ = a)
    (hc : jPlus N (1 / 2) + mPlus (1 / 2) μ = c) :
    Phi3j (1 / 2) (1 / 2) (1 / 2) N μ =
      Real.sqrt ((1 + 2 * (μ : ℝ) / N) / 2) / Real.sqrt (1 - (1 / (N : ℝ)) ^ 2 / 4) := by
  have := Phi3j_seed (1 / 2) (1 / 2) N μ 1 0 a c (by norm_num) (by norm_num) ha hc
  rw [this, Cprod_two_one, Cprod_zero, Cprod_one, show (1 / 2 : ℚ) - 1 / 2 = 0 by norm_num,
    sgn_zero']
  simp

/-- `rem:spinhalf`, chamber `M = 1/2, σ = -1/2`: `Φ = -√((1-x)/2)/√(1-h²/4)`. -/
theorem Phi3j_half_pm (N μ : ℚ) (a c : ℕ) (ha : jMinus N (-1 / 2) + mMinus (1 / 2) μ = a)
    (hc : jPlus N (-1 / 2) + mPlus (1 / 2) μ = c) :
    Phi3j (1 / 2) (1 / 2) (-1 / 2) N μ =
      -(Real.sqrt ((1 - 2 * (μ : ℝ) / N) / 2) / Real.sqrt (1 - (1 / (N : ℝ)) ^ 2 / 4)) := by
  have := Phi3j_seed (1 / 2) (-1 / 2) N μ 0 1 a c (by norm_num) (by norm_num) ha hc
  rw [this, show 0 + 1 + 1 = 1 + 0 + 1 by rfl, Cprod_two_one, Cprod_zero, Cprod_one,
    show (1 / 2 : ℚ) - -1 / 2 = 1 by norm_num, sgn_one']
  simp
  ring

/-- `rem:spinhalf`, chamber `M = -1/2, σ = 1/2` (from `M = 1/2` by the sign symmetry):
`Φ = √((1-x)/2)/√(1-h²/4)`.  The lattice hypotheses are `j_--m_-` and `j_+-m_+` in `ℕ`. -/
theorem Phi3j_half_mp (N μ : ℚ) (a c : ℕ) (hb : jMinus N (1 / 2) - mMinus (-1 / 2) μ = a)
    (hd : jPlus N (1 / 2) - mPlus (-1 / 2) μ = c) :
    Phi3j (1 / 2) (-1 / 2) (1 / 2) N μ =
      Real.sqrt ((1 - 2 * (μ : ℝ) / N) / 2) / Real.sqrt (1 - (1 / (N : ℝ)) ^ 2 / 4) := by
  have ha : jMinus N (1 / 2) + mMinus (1 / 2) (-μ) = a := by
    unfold jMinus mMinus at *; linarith
  have hc : jPlus N (1 / 2) + mPlus (1 / 2) (-μ) = c := by
    unfold jPlus mPlus at *; linarith
  have h1 := half_hyp_pm N (-μ) a c ha hc
  have hneg := Phi3j_neg_M (1 / 2) (1 / 2) (1 / 2) N (-μ) ⟨1, by norm_num⟩
    (by obtain ⟨n, hn⟩ := h1; exact ⟨n, by linarith⟩) ⟨0, by norm_num⟩
    ⟨c, by rw [hc]; simp⟩
  rw [show (-(1 / 2 : ℚ)) = -1 / 2 by norm_num, neg_neg] at hneg
  rw [hneg, Phi3j_half_pp N (-μ) a c ha hc, show (1 / 2 : ℚ) - 1 / 2 = 0 by norm_num, sgn_zero']
  push_cast
  rw [show (1 + 2 * -(μ : ℝ) / N) = 1 - 2 * μ / N by ring]
  ring

/-- `rem:spinhalf`, chamber `M = σ = -1/2`: `Φ = √((1+x)/2)/√(1-h²/4)`. -/
theorem Phi3j_half_mm (N μ : ℚ) (a c : ℕ) (hb : jMinus N (-1 / 2) - mMinus (-1 / 2) μ = a)
    (hd : jPlus N (-1 / 2) - mPlus (-1 / 2) μ = c) :
    Phi3j (1 / 2) (-1 / 2) (-1 / 2) N μ =
      Real.sqrt ((1 + 2 * (μ : ℝ) / N) / 2) / Real.sqrt (1 - (1 / (N : ℝ)) ^ 2 / 4) := by
  have ha : jMinus N (-1 / 2) + mMinus (1 / 2) (-μ) = a := by
    unfold jMinus mMinus at *; linarith
  have hc : jPlus N (-1 / 2) + mPlus (1 / 2) (-μ) = c := by
    unfold jPlus mPlus at *; linarith
  have h1 : ∃ n : ℤ, N - 1 + -1 / 2 = n := by
    refine ⟨(a : ℤ) + c + 1 - 1, ?_⟩
    unfold jMinus jPlus mMinus mPlus at *
    push_cast; linarith
  have hneg := Phi3j_neg_M (1 / 2) (1 / 2) (-1 / 2) N (-μ) ⟨1, by norm_num⟩
    (by obtain ⟨n, hn⟩ := h1; exact ⟨n, by linarith⟩) ⟨1, by norm_num⟩
    ⟨c, by rw [hc]; simp⟩
  rw [show (-(1 / 2 : ℚ)) = -1 / 2 by norm_num, neg_neg] at hneg
  rw [hneg, Phi3j_half_pm N (-μ) a c ha hc, show (1 / 2 : ℚ) - -1 / 2 = 1 by norm_num, sgn_one']
  push_cast
  rw [show (1 - 2 * -(μ : ℝ) / N) = 1 + 2 * μ / N by ring]
  ring

/-- info: 'FormalResearch.Racah.Phi3j_neg_M' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi3j_neg_M

/-- info: 'FormalResearch.Racah.Phi3j_half_pp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi3j_half_pp

/-- info: 'FormalResearch.Racah.Phi3j_half_pm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi3j_half_pm

/-- info: 'FormalResearch.Racah.Phi3j_half_mp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi3j_half_mp

/-- info: 'FormalResearch.Racah.Phi3j_half_mm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi3j_half_mm

end FormalResearch.Racah
