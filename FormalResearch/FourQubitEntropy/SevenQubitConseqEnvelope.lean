import FormalResearch.FourQubitEntropy.SevenQubitConseqMajorant

/-!
# `lem:seven-fixed-purity-envelope`: the entropy envelope at fixed eight-level purity

For `1/8 ≤ p ≤ 1` put `t(p) = (1 + √(7(8p-1)))/8` and
`g₈(p) = -t ln t - 7 · ((1-t)/7) ln ((1-t)/7)` (entropy in nats; the paper's `g₈` is this over `ln 2`).
Every probability vector `λ` on eight points with `∑ λ² = p` has `∑ -λ ln λ ≤ g₈(p)`.

Proof (a Lagrange-free route): `λ_max ≤ t(p)` by Cauchy–Schwarz; the Hermite quadratic majorant of
`-x ln x` with double contact at `b = (1-t)/7` and contact at `t` is valid on `[0,t]`
(`SevenQubitConseqMajorant.majorant`), and its sum over `λ` depends only on `∑ λ` and `∑ λ²`.
-/

open Real Finset

namespace FormalResearch.FourQubitEntropy.SevenQubitConseq

/-- Entropy (nats) of the spike spectrum `(a, b, …, b)`, `b = (1-a)/7`. -/
noncomputable def Gsp (a : ℝ) : ℝ := negMulLog a + 7 * negMulLog ((1 - a) / 7)

/-- The spike weight `t(p)`. -/
noncomputable def tOf (p : ℝ) : ℝ := (1 + Real.sqrt (7 * (8 * p - 1))) / 8

/-- The envelope `g₈(p)` (nats). -/
noncomputable def g8 (p : ℝ) : ℝ := Gsp (tOf p)

theorem hc_mul {a b : ℝ} : hc a b * (a - b) ^ 2 = rem b a := by
  unfold hc
  rcases eq_or_ne a b with h | h
  · subst h; simp [rem_at]
  · have : (a - b) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.2 h)
    field_simp

/-- Quadratic majorant of the spike data: `Gsp a` is the value of the sum of the majorant. -/
theorem envelope_aux {ι : Type*} [Fintype ι] (hcard : Fintype.card ι = 8) (lam : ι → ℝ)
    (h0 : ∀ i, 0 ≤ lam i) (h1 : ∑ i, lam i = 1) {a : ℝ} (ha1 : 1 / 8 ≤ a) (ha2 : a < 1)
    (hp : ∑ i, lam i ^ 2 = (8 * a ^ 2 - 2 * a + 1) / 7) :
    ∑ i, negMulLog (lam i) ≤ Gsp a := by
  set b : ℝ := (1 - a) / 7 with hbdef
  have hb : 0 < b := by rw [hbdef]; linarith
  have hba : b ≤ a := by rw [hbdef]; linarith
  -- every eigenvalue is at most a
  have hle : ∀ j, lam j ≤ a := by
    classical
    intro j
    have hcs := sq_sum_le_card_mul_sum_sq (s := univ.erase j) (f := lam)
    have hc7 : ((univ.erase j).card : ℝ) = 7 := by
      rw [Finset.card_erase_of_mem (mem_univ j), Finset.card_univ, hcard]; norm_num
    rw [hc7] at hcs
    have e1 : ∑ i ∈ univ.erase j, lam i = 1 - lam j := by
      have := Finset.add_sum_erase univ lam (mem_univ j)
      linarith
    have e2 : ∑ i ∈ univ.erase j, lam i ^ 2 = (8 * a ^ 2 - 2 * a + 1) / 7 - lam j ^ 2 := by
      have := Finset.add_sum_erase univ (fun i => lam i ^ 2) (mem_univ j)
      linarith
    rw [e1, e2] at hcs
    by_contra hlt
    rw [not_le] at hlt
    nlinarith [h0 j]
  set c := hc a b with hcdef
  set α : ℝ := negMulLog b + (-log b - 1) * (-b) + c * b ^ 2 with hα
  set β : ℝ := (-log b - 1) - 2 * c * b with hβ
  set Q : ℝ → ℝ := fun x => α + β * x + c * x ^ 2 with hQ
  have hQe : ∀ x, tang b x + c * (x - b) ^ 2 = Q x := by
    intro x; simp only [tang, hQ, hα, hβ]; ring
  have hmaj : ∀ i, negMulLog (lam i) ≤ Q (lam i) := fun i => by
    rw [← hQe]; exact majorant hb hba (h0 i) (hle i)
  have hQa : negMulLog a = Q a := by
    have := hc_mul (a := a) (b := b)
    have e : rem b a = negMulLog a - tang b a := rfl
    rw [← hQe]; rw [← hcdef] at this; linarith
  have hQb : negMulLog b = Q b := by
    rw [← hQe]; simp [tang]
  calc ∑ i, negMulLog (lam i) ≤ ∑ i, Q (lam i) := Finset.sum_le_sum fun i _ => hmaj i
    _ = 8 * α + β * 1 + c * ((8 * a ^ 2 - 2 * a + 1) / 7) := by
      simp only [hQ]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h1, hp]
      simp [Finset.sum_const, Finset.card_univ, hcard]
    _ = Q a + 7 * Q b := by
      simp only [hQ, hbdef]
      field_simp
      ring
    _ = Gsp a := by rw [← hQa, ← hQb]; rfl

theorem sum_sq_ge {ι : Type*} [Fintype ι] (hcard : Fintype.card ι = 8) (lam : ι → ℝ)
    (h1 : ∑ i, lam i = 1) : 1 / 8 ≤ ∑ i, lam i ^ 2 := by
  have : 0 ≤ ∑ i, (lam i - 1 / 8) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have e : ∑ i, (lam i - 1 / 8) ^ 2 = ∑ i, lam i ^ 2 - 1 / 4 + 1 / 8 := by
    have : ∀ i, (lam i - 1 / 8) ^ 2 = lam i ^ 2 - (1 / 4) * lam i + 1 / 64 := fun i => by ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, h1,
      Finset.sum_const, Finset.card_univ, hcard]
    norm_num
  linarith

theorem sum_sq_le {ι : Type*} [Fintype ι] (lam : ι → ℝ) (h0 : ∀ i, 0 ≤ lam i)
    (h1 : ∑ i, lam i = 1) : ∑ i, lam i ^ 2 ≤ 1 := by
  have hle : ∀ i, lam i ≤ 1 := fun i => by
    rw [← h1]
    exact Finset.single_le_sum (f := lam) (fun j _ => h0 j) (mem_univ i)
  calc ∑ i, lam i ^ 2 ≤ ∑ i, lam i := Finset.sum_le_sum fun i _ => by
        nlinarith [h0 i, hle i]
    _ = 1 := h1

/-- **`lem:seven-fixed-purity-envelope` (entropy bound).**  For every probability vector `λ` on an
eight-point set with `∑ λ² = p`: `∑ -λ ln λ ≤ g₈(p)`. -/
theorem entropy_le_g8 {ι : Type*} [Fintype ι] (hcard : Fintype.card ι = 8) (lam : ι → ℝ)
    (h0 : ∀ i, 0 ≤ lam i) (h1 : ∑ i, lam i = 1) :
    ∑ i, negMulLog (lam i) ≤ g8 (∑ i, lam i ^ 2) := by
  set p := ∑ i, lam i ^ 2 with hpdef
  have hp1 : 1 / 8 ≤ p := sum_sq_ge hcard lam h1
  have hp2 : p ≤ 1 := sum_sq_le lam h0 h1
  set s := Real.sqrt (7 * (8 * p - 1)) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 7 * (8 * p - 1) := Real.sq_sqrt (by linarith)
  have hs7 : s ≤ 7 := by nlinarith
  unfold g8 tOf
  rw [← hs]
  rcases lt_or_ge s 7 with hlt | hge
  · apply envelope_aux hcard lam h0 h1 (a := (1 + s) / 8) (by linarith) (by linarith)
    have : p = (8 * ((1 + s) / 8) ^ 2 - 2 * ((1 + s) / 8) + 1) / 7 := by nlinarith
    show p = _
    exact this
  · -- p = 1: a point mass
    have hs7' : s = 7 := le_antisymm hs7 hge
    have hp : p = 1 := by rw [hs7'] at hs2; linarith
    have hle : ∀ i, lam i ≤ 1 := fun i => by
      rw [← h1]; exact Finset.single_le_sum (f := lam) (fun j _ => h0 j) (mem_univ i)
    have hz : ∀ i, lam i ^ 2 = lam i := by
      have hsum : ∑ i, (lam i - lam i ^ 2) = 0 := by
        rw [Finset.sum_sub_distrib, h1]; linarith
      have hnn : ∀ i ∈ (univ : Finset ι), 0 ≤ lam i - lam i ^ 2 := fun i _ => by
        nlinarith [h0 i, hle i]
      have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum
      intro i; have := this i (mem_univ i); linarith
    have hv : ∀ i, negMulLog (lam i) = 0 := by
      intro i
      have : lam i = 0 ∨ lam i = 1 := by
        have h := hz i
        have : lam i * (lam i - 1) = 0 := by nlinarith
        rcases mul_eq_zero.1 this with h | h
        · exact Or.inl h
        · exact Or.inr (by linarith)
      rcases this with h | h <;> simp [h]
    simp only [hv, Finset.sum_const_zero]
    rw [hs7']
    norm_num [Gsp]

end FormalResearch.FourQubitEntropy.SevenQubitConseq
