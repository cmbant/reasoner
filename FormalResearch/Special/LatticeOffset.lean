module

public import FormalResearch.Special.LatticeVar

/-!
# `prop:offsetcore` (i), the finite deduction from `lem:latticesum` (iii)

Source: `Weyl/free_fermion/paper/parts/constants.tex`, `prop:offsetcore`.  Given the offset statement
`lem:latticesum` (iii) as an explicit hypothesis (`hIII`, `hIIIfrac`: the quantity
`S = ∑_r [ν(2πx_r) - 1_{x_r<0}]` is within `E₃` of `{t₀} - ½` (for `t₀ ∉ ℤ`) and its offset
`S - t₀ + ½` is within `E₃` of `ℤ`), the finite sum `𝔱 = ∑ λ_r + k₀ + ∑ μ_s` of the proposition satisfies
`|𝔱 - (k₀ + K₊ + r₀ + {t₀} - ½)| ≤ n ε_λ + 2 ε_μ + E₃` and
`dist(t₀ - 𝔱 - ½, ℤ) ≤ n ε_λ + 2 ε_μ + E₃`.

This is the finite deduction only.  `lem:latticesum` (iii) for the Gamma phase (`latticesum_gamma_iii`) and `prop:offsetcore`
(i), (ii) without hypotheses on (iii) are in `LatticeOffsetGamma` (`offsetcore_gamma`).
-/

@[expose] public section

namespace FormalResearch.Special.Lattice

open Set

lemma abs_sub_indicator_le {m : ℝ} (h0 : 0 ≤ m) (h1 : m ≤ 1) :
    |m - (if 1 / 2 < m then 1 else 0)| ≤ 2 * (m * (1 - m)) := by
  split_ifs with h
  · rw [abs_of_nonpos (by linarith)]; nlinarith
  · rw [abs_of_nonneg (by linarith)]; nlinarith

/-- **`prop:offsetcore` (i)**, the finite deduction from `lem:latticesum` (iii) taken as the hypotheses `hIII`, `hIIIfrac`.
The unconditional statement for the Gamma phase is `offsetcore_gamma` (`LatticeOffsetGamma`), which feeds this theorem
with `latticesum_gamma_iii`. -/
theorem offsetcore_i_of_iii {ι : Type*} (S : Finset ℝ) (M : Finset ι) (lam : ℝ → ℝ) (mu : ι → ℝ)
    (k0 : ℤ) (t0 tt epl epm E3 : ℝ)
    (hlam : ∀ x ∈ S, |lam x - nuR (2 * Real.pi * x)| ≤ epl)
    (hmu : ∀ s ∈ M, 0 ≤ mu s ∧ mu s ≤ 1) (hμsum : ∑ s ∈ M, mu s * (1 - mu s) ≤ epm)
    (htt : tt = ∑ x ∈ S, lam x + k0 + ∑ s ∈ M, mu s)
    (hIII : ∃ m : ℤ, |(∑ x ∈ S, (nuR (2 * Real.pi * x) - if x < 0 then (1 : ℝ) else 0)) - t0 + 1 / 2 - m| ≤ E3)
    (hIIIfrac : Int.fract t0 ≠ 0 →
      |(∑ x ∈ S, (nuR (2 * Real.pi * x) - if x < 0 then (1 : ℝ) else 0)) - (Int.fract t0 - 1 / 2)| ≤ E3) :
    (Int.fract t0 ≠ 0 →
      |tt - (k0 + ((M.filter fun s => 1 / 2 < mu s).card : ℝ) +
        ((S.filter fun x => x < 0).card : ℝ) + (Int.fract t0 - 1 / 2))| ≤
          S.card * epl + 2 * epm + E3) ∧
    ∃ m : ℤ, |t0 - tt - 1 / 2 - m| ≤ S.card * epl + 2 * epm + E3 := by
  classical
  set Sd : ℝ := ∑ x ∈ S, (nuR (2 * Real.pi * x) - if x < 0 then (1 : ℝ) else 0) with hSd
  set r0 : ℝ := ((S.filter fun x => x < 0).card : ℝ) with hr0
  set Kp : ℝ := ((M.filter fun s => 1 / 2 < mu s).card : ℝ) with hKp
  have hr0e : ∑ x ∈ S, (if x < 0 then (1 : ℝ) else 0) = r0 := by
    rw [hr0, Finset.card_filter]; push_cast; rfl
  have hKe : ∑ s ∈ M, (if 1 / 2 < mu s then (1 : ℝ) else 0) = Kp := by
    rw [hKp, Finset.card_filter]; push_cast; rfl
  have hSd' : Sd = ∑ x ∈ S, nuR (2 * Real.pi * x) - r0 := by
    rw [hSd, Finset.sum_sub_distrib, hr0e]
  -- error of the finite part
  have herr1 : |∑ x ∈ S, lam x - ∑ x ∈ S, nuR (2 * Real.pi * x)| ≤ S.card * epl := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ x ∈ S, |lam x - nuR (2 * Real.pi * x)| ≤ ∑ _x ∈ S, epl := Finset.sum_le_sum hlam
      _ = S.card * epl := by simp
  have herr2 : |∑ s ∈ M, mu s - Kp| ≤ 2 * epm := by
    rw [← hKe, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ s ∈ M, |mu s - (if 1 / 2 < mu s then (1 : ℝ) else 0)|
        ≤ ∑ s ∈ M, 2 * (mu s * (1 - mu s)) :=
          Finset.sum_le_sum fun s hs => abs_sub_indicator_le (hmu s hs).1 (hmu s hs).2
      _ = 2 * ∑ s ∈ M, mu s * (1 - mu s) := by rw [Finset.mul_sum]
      _ ≤ 2 * epm := by linarith
  -- 𝔱 = k0 + Kp + r0 + Sd + err
  set err : ℝ := tt - (k0 + Kp + r0 + Sd) with herr
  have herrb : |err| ≤ S.card * epl + 2 * epm := by
    have e : err = (∑ x ∈ S, lam x - ∑ x ∈ S, nuR (2 * Real.pi * x)) + (∑ s ∈ M, mu s - Kp) := by
      rw [herr, htt, hSd']; ring
    rw [e]
    exact (abs_add_le _ _).trans (add_le_add herr1 herr2)
  constructor
  · intro hf
    have h3 := hIIIfrac hf
    have e : tt - (k0 + Kp + r0 + (Int.fract t0 - 1 / 2)) = err + (Sd - (Int.fract t0 - 1 / 2)) := by
      rw [herr]; ring
    rw [e]
    exact (abs_add_le _ _).trans (by linarith)
  · obtain ⟨m, hm⟩ := hIII
    refine ⟨-(m + k0 + ((M.filter fun s => 1 / 2 < mu s).card : ℤ) +
      ((S.filter fun x => x < 0).card : ℤ)), ?_⟩
    have e : t0 - tt - 1 / 2 - ((-(m + k0 + ((M.filter fun s => 1 / 2 < mu s).card : ℤ) +
        ((S.filter fun x => x < 0).card : ℤ)) : ℤ) : ℝ) =
        -(Sd - t0 + 1 / 2 - m) - err := by
      push_cast
      rw [herr]
      simp only [hKp, hr0]
      ring
    rw [e]
    refine (abs_sub _ _).trans ?_
    rw [abs_neg]
    linarith

/-- info: 'FormalResearch.Special.Lattice.offsetcore_i_of_iii' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms offsetcore_i_of_iii

end FormalResearch.Special.Lattice
