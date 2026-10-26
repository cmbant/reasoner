import FormalResearch.FourQubitEntropy.RenyiSpec
import FormalResearch.FourQubitEntropy.Tsallis

/-!
# Rényi envelope on a rank-two cut

If one of the three balanced cuts of a unit four-qubit vector has Schmidt rank at most two, with
nonzero eigenvalues `a, 1-a`, then for every `q > 0` (including the von Neumann case `q = 1`)
`E_q(ψ) ≤ 4/3 + H_q(a, 1-a)/3 ≤ 5/3`, with equality in the first bound iff the other two cuts are
maximally mixed.

Paper: `prop:fqe-renyi-rank-two` (renyi_above_one.tex). The proof is the paper's: each of the other
two cuts has entropy at most `log₂ 4 = 2`, and a binary vector has entropy at most `1`.
-/

open scoped ComplexConjugate Matrix ComplexOrder

namespace FormalResearch.FourQubitEntropy

open Real

/-- A probability vector indexed by the pairs of qubit values (a cut spectrum). -/
def IsProb (l : Fin 2 × Fin 2 → ℝ) : Prop := (∀ i, 0 ≤ l i) ∧ ∑ i, l i = 1

theorem isProb_cut {R : Mat4} (hR : R.IsHermitian) (hp : R.PosSemidef)
    (htr : (Matrix.trace R).re = 1) : IsProb hR.eigenvalues :=
  ⟨hp.eigenvalues_nonneg, by rw [sum_eigenvalues_eq_trace, htr]⟩

theorem card_pair : Fintype.card (Fin 2 × Fin 2) = 4 := by simp

/-- The Rényi-`q` entropy of the binary vector `(a, 1-a)`, `log₂(a^q + (1-a)^q)/(1-q)`. -/
noncomputable def renyiBin (q a : ℝ) : ℝ := renyiSpec q ![a, 1 - a]

theorem renyiBin_eq (q a : ℝ) :
    renyiBin q a = Real.logb 2 (a ^ q + (1 - a) ^ q) / (1 - q) := by
  simp [renyiBin, renyiSpec, Fin.sum_univ_two]

/-- The von Neumann entropy in bits of a probability vector. -/
noncomputable def entSpec {ι : Type*} [Fintype ι] (l : ι → ℝ) : ℝ :=
  (∑ i, Real.negMulLog (l i)) / Real.log 2

/-- The binary entropy in bits. -/
noncomputable def entBin (a : ℝ) : ℝ := entSpec ![a, 1 - a]

theorem entBin_eq (a : ℝ) : entBin a = (Real.negMulLog a + Real.negMulLog (1 - a)) / Real.log 2 := by
  simp [entBin, entSpec, Fin.sum_univ_two]

theorem vnEntropy_eq_entSpec {R : Mat4} (hR : R.IsHermitian) :
    vnEntropy hR = entSpec hR.eigenvalues := rfl

section Entropy

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Shannon entropy is at most `log n`, with equality iff uniform. -/
theorem sum_negMulLog_le {l : ι → ℝ} (hl : ∀ i, 0 ≤ l i) (hs : ∑ i, l i = 1) :
    (∑ i, Real.negMulLog (l i) ≤ Real.log (Fintype.card ι)) ∧
    (∑ i, Real.negMulLog (l i) = Real.log (Fintype.card ι) ↔ ∀ i, l i = 1 / (Fintype.card ι : ℝ)) := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  set n : ℝ := (Fintype.card ι : ℝ) with hn_def
  have hw : ∀ i ∈ (Finset.univ : Finset ι), 0 < 1 / n := fun i _ => by positivity
  have hw1 : ∑ _i : ι, 1 / n = 1 := by simp [hn_def]
  have hmean : ∑ i, (1 / n) • l i = 1 / n := by
    simp only [smul_eq_mul, ← Finset.mul_sum, hs, mul_one]
  have hmem : ∀ i ∈ (Finset.univ : Finset ι), l i ∈ Set.Ici (0 : ℝ) := fun i _ => hl i
  have hsum : ∑ i, (1 / n) • Real.negMulLog (l i) = (1 / n) * ∑ i, Real.negMulLog (l i) := by
    simp only [smul_eq_mul, ← Finset.mul_sum]
  have hc := Real.strictConcaveOn_negMulLog
  have hle := hc.concaveOn.le_map_sum (t := Finset.univ) (w := fun _ => 1 / n) (p := l)
    (fun i _ => (hw i (Finset.mem_univ i)).le) hw1 hmem
  have hiff := hc.map_sum_eq_iff (t := Finset.univ) (w := fun _ => 1 / n) (p := l) hw hw1 hmem
  simp only [hmean, hsum] at hle hiff
  have hval : Real.negMulLog (1 / n) = (1 / n) * Real.log n := by
    rw [Real.negMulLog, one_div, Real.log_inv]; ring
  rw [hval] at hle hiff
  have key : ∀ S : ℝ, (1 / n) * S = (1 / n) * Real.log n ↔ S = Real.log n := fun S => by
    constructor
    · intro h; exact mul_left_cancel₀ (by positivity) h
    · intro h; rw [h]
  refine ⟨?_, ?_⟩
  · have := mul_le_mul_of_nonneg_left hle hn.le
    have e : n * ((1 / n) * ∑ i, Real.negMulLog (l i)) = ∑ i, Real.negMulLog (l i) := by field_simp
    have e' : n * ((1 / n) * Real.log n) = Real.log n := by field_simp
    linarith
  · constructor
    · intro h
      have h2 : (1 / n) * Real.log n = (1 / n) * ∑ i, Real.negMulLog (l i) := by
        rw [key (∑ i, Real.negMulLog (l i)) |>.2 h]
      intro i; exact hiff.1 h2 i (Finset.mem_univ i)
    · intro h
      have h2 := hiff.2 (fun j _ => h j)
      exact (key _).1 h2.symm

theorem entSpec_le_logb_card {l : ι → ℝ} (hl : ∀ i, 0 ≤ l i) (hs : ∑ i, l i = 1) :
    entSpec l ≤ Real.logb 2 (Fintype.card ι) := by
  unfold entSpec Real.logb
  exact div_le_div_of_nonneg_right (sum_negMulLog_le hl hs).1 (Real.log_pos (by norm_num)).le

theorem entSpec_eq_iff {l : ι → ℝ} (hl : ∀ i, 0 ≤ l i) (hs : ∑ i, l i = 1) :
    entSpec l = Real.logb 2 (Fintype.card ι) ↔ ∀ i, l i = 1 / (Fintype.card ι : ℝ) := by
  rw [← (sum_negMulLog_le hl hs).2]
  unfold entSpec Real.logb
  have l2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact ⟨fun h => by rwa [div_left_inj' l2.ne'] at h, fun h => by rw [h]⟩

end Entropy

/-! ### Rank-two spectra -/

/-- The spectrum `l` is `(a, 1-a, 0, 0)` up to ordering. -/
def RankTwoSpec (l : Fin 2 × Fin 2 → ℝ) (a : ℝ) : Prop :=
  ∃ i k, i ≠ k ∧ l i = a ∧ l k = 1 - a ∧ ∀ j, j ≠ i → j ≠ k → l j = 0

theorem RankTwoSpec.sum_rpow {l : Fin 2 × Fin 2 → ℝ} {a : ℝ} (h : RankTwoSpec l a) {q : ℝ}
    (hq : 0 < q) : ∑ j, l j ^ q = a ^ q + (1 - a) ^ q := by
  obtain ⟨i, k, hik, hi, hk, h0⟩ := h
  rw [Finset.sum_eq_add_of_mem i k (Finset.mem_univ _) (Finset.mem_univ _) hik, hi, hk]
  intro j _ ⟨h1, h2⟩
  rw [h0 j h1 h2, Real.zero_rpow hq.ne']

theorem RankTwoSpec.sum_negMulLog {l : Fin 2 × Fin 2 → ℝ} {a : ℝ} (h : RankTwoSpec l a) :
    ∑ j, Real.negMulLog (l j) = Real.negMulLog a + Real.negMulLog (1 - a) := by
  obtain ⟨i, k, hik, hi, hk, h0⟩ := h
  rw [Finset.sum_eq_add_of_mem i k (Finset.mem_univ _) (Finset.mem_univ _) hik, hi, hk]
  intro j _ ⟨h1, h2⟩
  rw [h0 j h1 h2]; simp

theorem logb_two_four : Real.logb 2 (4 : ℝ) = 2 := by
  rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, Real.logb_rpow (by norm_num) (by norm_num)]

theorem card_pair_real : (Fintype.card (Fin 2 × Fin 2) : ℝ) = 4 := by simp

theorem renyiSpec_le_two {q : ℝ} (hq0 : 0 < q) (hq1 : q ≠ 1) {l : Fin 2 × Fin 2 → ℝ} (hl : IsProb l) :
    renyiSpec q l ≤ 2 := by
  have := renyiSpec_le_logb_card hq0 hq1 hl.1 hl.2
  rwa [card_pair_real, logb_two_four] at this

theorem renyiSpec_eq_two_iff {q : ℝ} (hq0 : 0 < q) (hq1 : q ≠ 1) {l : Fin 2 × Fin 2 → ℝ}
    (hl : IsProb l) : renyiSpec q l = 2 ↔ ∀ i, l i = 1 / 4 := by
  have := renyiSpec_eq_iff hq0 hq1 hl.1 hl.2
  rwa [card_pair_real, logb_two_four] at this

theorem entSpec_le_two {l : Fin 2 × Fin 2 → ℝ} (hl : IsProb l) : entSpec l ≤ 2 := by
  have := entSpec_le_logb_card hl.1 hl.2
  rwa [card_pair_real, logb_two_four] at this

theorem entSpec_eq_two_iff {l : Fin 2 × Fin 2 → ℝ} (hl : IsProb l) :
    entSpec l = 2 ↔ ∀ i, l i = 1 / 4 := by
  have := entSpec_eq_iff hl.1 hl.2
  rwa [card_pair_real, logb_two_four] at this

theorem renyiBin_le_one {q : ℝ} (hq0 : 0 < q) (hq1 : q ≠ 1) {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1) :
    renyiBin q a ≤ 1 := by
  unfold renyiBin
  have := renyiSpec_le_logb_card hq0 hq1 (l := ![a, 1 - a]) (by
    intro i; fin_cases i <;> simp <;> linarith) (by simp [Fin.sum_univ_two])
  simpa using this

theorem entBin_le_one {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1) : entBin a ≤ 1 := by
  unfold entBin
  have := entSpec_le_logb_card (l := ![a, 1 - a]) (by
    intro i; fin_cases i <;> simp <;> linarith) (by simp [Fin.sum_univ_two])
  simpa using this

/-- **Rank-two cut, spectrum level** (`q ≠ 1`). -/
theorem renyi_rank_two_core {q a : ℝ} (hq0 : 0 < q) (hq1 : q ≠ 1) {l₁ l₂ l₃ : Fin 2 × Fin 2 → ℝ}
    (h₂ : IsProb l₂) (h₃ : IsProb l₃) (h₁ : RankTwoSpec l₁ a) :
    (renyiSpec q l₁ + renyiSpec q l₂ + renyiSpec q l₃) / 3 ≤ 4 / 3 + renyiBin q a / 3 ∧
    ((renyiSpec q l₁ + renyiSpec q l₂ + renyiSpec q l₃) / 3 = 4 / 3 + renyiBin q a / 3 ↔
      (∀ i, l₂ i = 1 / 4) ∧ ∀ i, l₃ i = 1 / 4) := by
  have e1 : renyiSpec q l₁ = renyiBin q a := by
    rw [renyiBin_eq]; unfold renyiSpec; rw [h₁.sum_rpow hq0]
  have b2 := renyiSpec_le_two hq0 hq1 h₂
  have b3 := renyiSpec_le_two hq0 hq1 h₃
  have i2 := renyiSpec_eq_two_iff hq0 hq1 h₂
  have i3 := renyiSpec_eq_two_iff hq0 hq1 h₃
  rw [e1]
  refine ⟨by linarith, ⟨fun h => ⟨i2.1 (by linarith), i3.1 (by linarith)⟩, fun ⟨u2, u3⟩ => ?_⟩⟩
  rw [i2.2 u2, i3.2 u3]; ring

/-- **Rank-two cut, spectrum level** (`q = 1`, von Neumann). -/
theorem entropy_rank_two_core {a : ℝ} {l₁ l₂ l₃ : Fin 2 × Fin 2 → ℝ}
    (h₂ : IsProb l₂) (h₃ : IsProb l₃) (h₁ : RankTwoSpec l₁ a) :
    (entSpec l₁ + entSpec l₂ + entSpec l₃) / 3 ≤ 4 / 3 + entBin a / 3 ∧
    ((entSpec l₁ + entSpec l₂ + entSpec l₃) / 3 = 4 / 3 + entBin a / 3 ↔
      (∀ i, l₂ i = 1 / 4) ∧ ∀ i, l₃ i = 1 / 4) := by
  have e1 : entSpec l₁ = entBin a := by
    rw [entBin_eq]; unfold entSpec; rw [h₁.sum_negMulLog]
  have b2 := entSpec_le_two h₂
  have b3 := entSpec_le_two h₃
  have i2 := entSpec_eq_two_iff h₂
  have i3 := entSpec_eq_two_iff h₃
  rw [e1]
  refine ⟨by linarith, ⟨fun h => ⟨i2.1 (by linarith), i3.1 (by linarith)⟩, fun ⟨u2, u3⟩ => ?_⟩⟩
  rw [i2.2 u2, i3.2 u3]; ring

/-! ### The theorem for the three cuts -/

theorem isProb12 {ψ : Psi} (hψ : normSqPsi ψ = 1) : IsProb (red12_herm ψ).eigenvalues :=
  isProb_cut _ (red12_psd ψ) (by rw [trace_red12, hψ]; simp)

theorem isProb13 {ψ : Psi} (hψ : normSqPsi ψ = 1) : IsProb (red13_herm ψ).eigenvalues :=
  isProb_cut _ (red13_psd ψ) (by rw [trace_red13, hψ]; simp)

theorem isProb14 {ψ : Psi} (hψ : normSqPsi ψ = 1) : IsProb (red14_herm ψ).eigenvalues :=
  isProb_cut _ (red14_psd ψ) (by rw [trace_red14, hψ]; simp)

/-- **Rényi envelope on a rank-two cut** (`prop:fqe-renyi-rank-two`), cut `12|34`, order
`q > 0`, `q ≠ 1`: if the cut spectrum is `(a, 1-a, 0, 0)` with `1/2 ≤ a ≤ 1`, then
`E_q(ψ) ≤ 4/3 + H_q(a,1-a)/3 ≤ 5/3`, with equality in the first bound iff the other two
balanced cut spectra are both `(1/4)⁴`. -/
theorem renyi_rank_two_12 {q a : ℝ} (hq0 : 0 < q) (hq1 : q ≠ 1) (ha : 1 / 2 ≤ a) (ha1 : a ≤ 1)
    {ψ : Psi} (hψ : normSqPsi ψ = 1) (h : RankTwoSpec (red12_herm ψ).eigenvalues a) :
    (meanRenyi q ψ ≤ 4 / 3 + renyiBin q a / 3 ∧ 4 / 3 + renyiBin q a / 3 ≤ 5 / 3) ∧
    (meanRenyi q ψ = 4 / 3 + renyiBin q a / 3 ↔
      (∀ i, (red13_herm ψ).eigenvalues i = 1 / 4) ∧ ∀ i, (red14_herm ψ).eigenvalues i = 1 / 4) := by
  obtain ⟨c1, c2⟩ := renyi_rank_two_core hq0 hq1 (isProb13 hψ) (isProb14 hψ) h
  have hb := renyiBin_le_one hq0 hq1 (by linarith) ha1
  exact ⟨⟨c1, by linarith⟩, c2⟩

/-- `prop:fqe-renyi-rank-two`, cut `13|24` (see `renyi_rank_two_12`). -/
theorem renyi_rank_two_13 {q a : ℝ} (hq0 : 0 < q) (hq1 : q ≠ 1) (ha : 1 / 2 ≤ a) (ha1 : a ≤ 1)
    {ψ : Psi} (hψ : normSqPsi ψ = 1) (h : RankTwoSpec (red13_herm ψ).eigenvalues a) :
    (meanRenyi q ψ ≤ 4 / 3 + renyiBin q a / 3 ∧ 4 / 3 + renyiBin q a / 3 ≤ 5 / 3) ∧
    (meanRenyi q ψ = 4 / 3 + renyiBin q a / 3 ↔
      (∀ i, (red12_herm ψ).eigenvalues i = 1 / 4) ∧ ∀ i, (red14_herm ψ).eigenvalues i = 1 / 4) := by
  obtain ⟨c1, c2⟩ := renyi_rank_two_core hq0 hq1 (isProb12 hψ) (isProb14 hψ) h
  have hb := renyiBin_le_one hq0 hq1 (by linarith) ha1
  have e : meanRenyi q ψ = (renyiSpec q (red13_herm ψ).eigenvalues + renyiSpec q (red12_herm ψ).eigenvalues
      + renyiSpec q (red14_herm ψ).eigenvalues) / 3 := by
    simp only [meanRenyi, renyiCut_eq_renyiSpec]; ring
  rw [e]
  exact ⟨⟨c1, by linarith⟩, c2⟩

/-- `prop:fqe-renyi-rank-two`, cut `14|23` (see `renyi_rank_two_12`). -/
theorem renyi_rank_two_14 {q a : ℝ} (hq0 : 0 < q) (hq1 : q ≠ 1) (ha : 1 / 2 ≤ a) (ha1 : a ≤ 1)
    {ψ : Psi} (hψ : normSqPsi ψ = 1) (h : RankTwoSpec (red14_herm ψ).eigenvalues a) :
    (meanRenyi q ψ ≤ 4 / 3 + renyiBin q a / 3 ∧ 4 / 3 + renyiBin q a / 3 ≤ 5 / 3) ∧
    (meanRenyi q ψ = 4 / 3 + renyiBin q a / 3 ↔
      (∀ i, (red12_herm ψ).eigenvalues i = 1 / 4) ∧ ∀ i, (red13_herm ψ).eigenvalues i = 1 / 4) := by
  obtain ⟨c1, c2⟩ := renyi_rank_two_core hq0 hq1 (isProb12 hψ) (isProb13 hψ) h
  have hb := renyiBin_le_one hq0 hq1 (by linarith) ha1
  have e : meanRenyi q ψ = (renyiSpec q (red14_herm ψ).eigenvalues + renyiSpec q (red12_herm ψ).eigenvalues
      + renyiSpec q (red13_herm ψ).eigenvalues) / 3 := by
    simp only [meanRenyi, renyiCut_eq_renyiSpec]; ring
  rw [e]
  exact ⟨⟨c1, by linarith⟩, c2⟩

/-- The von Neumann case `q = 1` of `prop:fqe-renyi-rank-two`, cut `12|34`: the same statement with
`meanEntropy` and the binary entropy `entBin a`. -/
theorem entropy_rank_two_12 {a : ℝ} (ha : 1 / 2 ≤ a) (ha1 : a ≤ 1)
    {ψ : Psi} (hψ : normSqPsi ψ = 1) (h : RankTwoSpec (red12_herm ψ).eigenvalues a) :
    (meanEntropy ψ ≤ 4 / 3 + entBin a / 3 ∧ 4 / 3 + entBin a / 3 ≤ 5 / 3) ∧
    (meanEntropy ψ = 4 / 3 + entBin a / 3 ↔
      (∀ i, (red13_herm ψ).eigenvalues i = 1 / 4) ∧ ∀ i, (red14_herm ψ).eigenvalues i = 1 / 4) := by
  obtain ⟨c1, c2⟩ := entropy_rank_two_core (isProb13 hψ) (isProb14 hψ) h
  have hb := entBin_le_one (by linarith) ha1
  exact ⟨⟨c1, by linarith⟩, c2⟩

/-- `prop:fqe-renyi-rank-two`, `q = 1`, cut `13|24`. -/
theorem entropy_rank_two_13 {a : ℝ} (ha : 1 / 2 ≤ a) (ha1 : a ≤ 1)
    {ψ : Psi} (hψ : normSqPsi ψ = 1) (h : RankTwoSpec (red13_herm ψ).eigenvalues a) :
    (meanEntropy ψ ≤ 4 / 3 + entBin a / 3 ∧ 4 / 3 + entBin a / 3 ≤ 5 / 3) ∧
    (meanEntropy ψ = 4 / 3 + entBin a / 3 ↔
      (∀ i, (red12_herm ψ).eigenvalues i = 1 / 4) ∧ ∀ i, (red14_herm ψ).eigenvalues i = 1 / 4) := by
  obtain ⟨c1, c2⟩ := entropy_rank_two_core (isProb12 hψ) (isProb14 hψ) h
  have hb := entBin_le_one (by linarith) ha1
  have e : meanEntropy ψ = (entSpec (red13_herm ψ).eigenvalues + entSpec (red12_herm ψ).eigenvalues
      + entSpec (red14_herm ψ).eigenvalues) / 3 := by
    unfold meanEntropy vnEntropy entSpec; ring
  rw [e]
  exact ⟨⟨c1, by linarith⟩, c2⟩

/-- `prop:fqe-renyi-rank-two`, `q = 1`, cut `14|23`. -/
theorem entropy_rank_two_14 {a : ℝ} (ha : 1 / 2 ≤ a) (ha1 : a ≤ 1)
    {ψ : Psi} (hψ : normSqPsi ψ = 1) (h : RankTwoSpec (red14_herm ψ).eigenvalues a) :
    (meanEntropy ψ ≤ 4 / 3 + entBin a / 3 ∧ 4 / 3 + entBin a / 3 ≤ 5 / 3) ∧
    (meanEntropy ψ = 4 / 3 + entBin a / 3 ↔
      (∀ i, (red12_herm ψ).eigenvalues i = 1 / 4) ∧ ∀ i, (red13_herm ψ).eigenvalues i = 1 / 4) := by
  obtain ⟨c1, c2⟩ := entropy_rank_two_core (isProb12 hψ) (isProb13 hψ) h
  have hb := entBin_le_one (by linarith) ha1
  have e : meanEntropy ψ = (entSpec (red14_herm ψ).eigenvalues + entSpec (red12_herm ψ).eigenvalues
      + entSpec (red13_herm ψ).eigenvalues) / 3 := by
    unfold meanEntropy vnEntropy entSpec; ring
  rw [e]
  exact ⟨⟨c1, by linarith⟩, c2⟩

/-- info: 'FormalResearch.FourQubitEntropy.renyi_rank_two_12' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms renyi_rank_two_12

/-- info: 'FormalResearch.FourQubitEntropy.renyi_rank_two_13' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms renyi_rank_two_13

/-- info: 'FormalResearch.FourQubitEntropy.renyi_rank_two_14' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms renyi_rank_two_14

/-- info: 'FormalResearch.FourQubitEntropy.entropy_rank_two_12' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms entropy_rank_two_12

/-- info: 'FormalResearch.FourQubitEntropy.entropy_rank_two_13' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms entropy_rank_two_13

/-- info: 'FormalResearch.FourQubitEntropy.entropy_rank_two_14' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms entropy_rank_two_14

end FormalResearch.FourQubitEntropy
