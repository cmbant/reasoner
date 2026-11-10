module

public import FormalResearch.FourQubitEntropy.SevenQubitRainsFaces
public import FormalResearch.FourQubitEntropy.PurityLPCert
public import FormalResearch.NQubit.Shadow.Stabilizer

/-!
# States attaining the Rains bound at `n = 7, 13, 19, 20` (`prop:rains-faces`)

`QI/multiqubit_entanglement/seven_qubit_entanglement/shadow_equality_geometry.tex`, `prop:rains-faces`.

For `n ∈ {7, 13, 19, 20}` let `L_n = 1/8, 25/1408, 93/38896, 1193/739024` be the Rains LP value.  Proved here for every
unit `n`-qubit vector `ψ` (a pure state, not only stabilizer states):

* the Rains lower bound `L_n ≤ π_{⌊n/2⌋}(ψ)` for these `n` (`rains_bound_7`, …), by exact dual certificates
  (`lp_bound`);
* if `π_{⌊n/2⌋}(ψ) = L_n` then `ψ` has the **unique** Pauli weight distribution `A = tgt_n` and shadow distribution
  `S = sh_n` of `SevenQubitRainsFaces` (`rains_equality_profile_7`, …).  The dual certificates are strictly
  complementary on the listed zero weights and zero shadow coefficients (`lp_equality_zero`: `Σ_j w_j A_j +
  Σ_i y_i S_i = π - L`, all terms non-negative), which puts `A` on the face `FaceR n zA zS`, and the face has a
  unique point (integer left inverse of `n+1` independent rows);
* for `n = 7, 13` the unique profile has a non-integer shadow coefficient (`S_1 = 7/4`, `S_3 = 39/4`), so **no stabilizer
  state attains the Rains bound** (`stabilizer_ne_rains_7`, `stabilizer_ne_rains_13`; integrality of `S_i` is
  `IsStabilizerState.shadowCoeff_nat`).

Not covered: existence of any state with these profiles (the paper asserts none), and the `n = 20` Type I additive
`F₄` code reading.
-/

@[expose] public section


open scoped BigOperators
open Finset

namespace FormalResearch.FourQubitEntropy.SevenQubitRainsEquality

open FormalResearch.FourQubitEntropy.SevenQubitRains
open FormalResearch.NQubit FormalResearch.NQubit.Pauli FormalResearch.NQubit.Shadow
  FormalResearch.NQubit.Reduced FormalResearch.NQubit.TimeReversal
open FormalResearch.FourQubitEntropy.PurityLP

/-! ### The face over `ℝ` and its unique point -/

/-- `Face` for a real weight distribution. -/
def FaceR (n : ℕ) (zA zS : List ℕ) (A : ℕ → ℝ) : Prop :=
  A 0 = 1 ∧ (∀ j ∈ zA, A j = 0) ∧
  (∀ s < (n + 1) / 2, ∑ j ∈ range (n + 1), ((aCoef n s j - aCoef n (n - s) j : ℚ) : ℝ) * A j = 0) ∧
  (∀ i ∈ zS, ∑ j ∈ range (n + 1), (shadowCoef n i j : ℝ) * A j = 0)

theorem sum_PR (n s : ℕ) (hs : s ≤ n) (A : ℕ → ℝ) :
    ∑ j ∈ range (n + 1), ((aCoef n s j - aCoef n (n - s) j : ℚ) : ℝ) * A j =
      (∑ j ∈ range (n + 1), (pNum n s j : ℝ) * A j) / (2 ^ n * Nat.choose n s) := by
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  have := congrArg (fun q : ℚ => (q : ℝ)) (coefP_eq n s j hs)
  push_cast at this
  push_cast
  rw [this, div_mul_eq_mul_div]

theorem sum_SR (n i : ℕ) (A : ℕ → ℝ) :
    ∑ j ∈ range (n + 1), (shadowCoef n i j : ℝ) * A j =
      (∑ j ∈ range (n + 1), (shadowNum n i j : ℝ) * A j) / 2 ^ n := by
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [shadowCoef]; push_cast; rw [div_mul_eq_mul_div]

theorem unique_of_cert_R (n : ℕ) (spec : ℕ → ℕ × ℕ) (L : ℕ → ℕ → ℤ) (dd : ℤ)
    (hLM : ∀ j < n + 1, ∀ i < n + 1,
      ∑ k ∈ range (n + 1), L j k * rowI n (spec k).1 (spec k).2 i = if j = i then dd else 0)
    (A : ℕ → ℝ) (rhs : ℕ → ℤ)
    (hrow : ∀ k < n + 1,
      ∑ i ∈ range (n + 1), (rowI n (spec k).1 (spec k).2 i : ℝ) * A i = (rhs k : ℝ)) :
    ∀ j < n + 1, (dd : ℝ) * A j = ((∑ k ∈ range (n + 1), L j k * rhs k : ℤ) : ℝ) := by
  intro j hj
  push_cast
  symm
  calc (∑ k ∈ range (n + 1), (L j k : ℝ) * (rhs k : ℝ))
      = ∑ k ∈ range (n + 1), (L j k : ℝ) *
          ∑ i ∈ range (n + 1), (rowI n (spec k).1 (spec k).2 i : ℝ) * A i := by
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [hrow k (Finset.mem_range.1 hk)]
    _ = ∑ i ∈ range (n + 1),
          (∑ k ∈ range (n + 1), (L j k : ℝ) * (rowI n (spec k).1 (spec k).2 i : ℝ)) * A i := by
        simp_rw [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
        ring
    _ = ∑ i ∈ range (n + 1), (if j = i then (dd : ℝ) else 0) * A i := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have := hLM j hj i (Finset.mem_range.1 hi)
        have h2 : (∑ k ∈ range (n + 1), (L j k : ℝ) * (rowI n (spec k).1 (spec k).2 i : ℝ)) =
            if j = i then (dd : ℝ) else 0 := by
          have := congrArg (fun z : ℤ => (z : ℝ)) this
          simpa [apply_ite] using this
        rw [h2]
    _ = (dd : ℝ) * A j := by
        simp [ite_mul, Finset.sum_ite_eq, Finset.mem_range, hj]

theorem faceR_rows (n : ℕ) (zA zS : List ℕ) (A : ℕ → ℝ) (h : FaceR n zA zS A)
    (spec : ℕ → ℕ × ℕ)
    (hspec : ∀ k < n + 1, spec k = (0, 0) ∨
      ((spec k).1 = 0 ∧ (spec k).2 ∈ zA ∧ 0 < (spec k).2 ∧ (spec k).2 ≤ n) ∨
      ((spec k).1 = 1 ∧ (spec k).2 < (n + 1) / 2) ∨
      ((spec k).1 = 2 ∧ (spec k).2 ∈ zS ∧ (spec k).2 ≤ n)) :
    ∀ k < n + 1, ∑ i ∈ range (n + 1), (rowI n (spec k).1 (spec k).2 i : ℝ) * A i =
      ((if (spec k).1 = 0 ∧ (spec k).2 = 0 then 1 else 0 : ℤ) : ℝ) := by
  obtain ⟨h0, hz, hp, hs⟩ := h
  intro k hk
  rcases hspec k hk with hk0 | ⟨ht, hm, hpos, hle⟩ | ⟨ht, hlt⟩ | ⟨ht, hm, hle⟩
  · rw [hk0]
    simp [rowI, h0]
  · have hne : (spec k).2 ≠ 0 := by omega
    simp [rowI, ht, hne, Finset.mem_range, Nat.lt_succ_of_le hle, hz _ hm]
  · have h1 : (spec k).1 ≠ 0 := by omega
    have hs' : (spec k).2 ≤ n := by omega
    have := hp (spec k).2 hlt
    rw [sum_PR n _ hs'] at this
    have hD : (2 : ℝ) ^ n * Nat.choose n (spec k).2 ≠ 0 := by
      have : (0 : ℝ) < Nat.choose n (spec k).2 := by exact_mod_cast Nat.choose_pos hs'
      positivity
    simpa [rowI, h1, ht, hD] using this
  · have h1 : (spec k).1 ≠ 0 := by omega
    have h2 : (spec k).1 ≠ 1 := by omega
    have := hs _ hm
    rw [sum_SR] at this
    simpa [rowI, h1, h2] using this

/-- Generic uniqueness of the real face point, from the same integer data as the rational version. -/
theorem faceR_unique_of_data (n : ℕ) (zA zS : List ℕ) (spec : List (ℕ × ℕ)) (Lt : List (List ℤ))
    (dd : ℤ) (tl : List ℤ) (A : ℕ → ℝ) (h : FaceR n zA zS A)
    (hspec : ∀ k < n + 1, (spec.getD k (0, 0)) = (0, 0) ∨
      ((spec.getD k (0, 0)).1 = 0 ∧ (spec.getD k (0, 0)).2 ∈ zA ∧ 0 < (spec.getD k (0, 0)).2 ∧
        (spec.getD k (0, 0)).2 ≤ n) ∨
      ((spec.getD k (0, 0)).1 = 1 ∧ (spec.getD k (0, 0)).2 < (n + 1) / 2) ∨
      ((spec.getD k (0, 0)).1 = 2 ∧ (spec.getD k (0, 0)).2 ∈ zS ∧ (spec.getD k (0, 0)).2 ≤ n))
    (hLM : ∀ j < n + 1, ∀ i < n + 1,
      ∑ k ∈ range (n + 1), (Lt.getD j []).getD k 0 * rowI n (spec.getD k (0, 0)).1
        (spec.getD k (0, 0)).2 i = if j = i then dd else 0)
    (hcol : ∀ j < n + 1, ∑ k ∈ range (n + 1), (Lt.getD j []).getD k 0 *
      (if (spec.getD k (0, 0)).1 = 0 ∧ (spec.getD k (0, 0)).2 = 0 then 1 else 0 : ℤ) =
      dd * tl.getD j 0)
    (hd : dd ≠ 0) : ∀ j ≤ n, A j = ((tl.getD j 0 : ℤ) : ℝ) := by
  have hrows := faceR_rows n zA zS A h (fun k => spec.getD k (0, 0)) hspec
  have hc := unique_of_cert_R n (fun k => spec.getD k (0, 0)) (fun j k => (Lt.getD j []).getD k 0)
    dd hLM A _ hrows
  intro j hj
  have e := hc j (by omega)
  rw [hcol j (by omega)] at e
  have hd' : (dd : ℝ) ≠ 0 := by exact_mod_cast hd
  apply mul_left_cancel₀ hd'
  rw [e]; push_cast; ring

/-! ### Equality in the LP step -/

/-- The LP slack identity: `π_{⌊n/2⌋} - L = Σ_j w_j A_j + Σ_i y_i S_i`. -/
theorem lp_slack (n : ℕ) (L : ℚ) (es ys : List (ℕ × ℚ)) (h : lpCheck n L es ys = true)
    (ψ : Ψ n) (hψ : nsq ψ = 1) :
    meanPurity ψ (n / 2) - L = ∑ j ∈ range (n + 1), (wCoef n L es ys j : ℝ) * weightEnum ψ j +
      (ys.map fun p => (p.2 : ℝ) * shadowCoeff ψ p.1).sum := by
  simp only [lpCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range] at h
  obtain ⟨⟨hes, _⟩, _⟩ := h
  set A' : ℕ → ℝ := fun j => weightEnum ψ j with hA'
  have hk : n / 2 ≤ n := Nat.div_le_self n 2
  have hlin : ∀ s, s ≤ n → lin n A' (aQ n s) = meanPurity ψ s := fun s hs =>
    (meanPurity_eq_lin ψ hs).symm
  have hw := lin_wCoef n A' L es ys
  have hes0 : (es.map fun p => (p.2 : ℝ) * (lin n A' (aQ n p.1) - lin n A' (aQ n (n - p.1)))).sum
      = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    have hp1 := hes p hp
    rw [hlin p.1 hp1, hlin (n - p.1) (Nat.sub_le _ _), meanPurity_compl ψ hp1]
    ring
  have hys : (ys.map fun p => (p.2 : ℝ) * lin n A' (shQ n p.1)).sum =
      (ys.map fun p => (p.2 : ℝ) * shadowCoeff ψ p.1).sum := by
    congr 1
    refine List.map_congr_left fun p _ => ?_
    rw [shadowCoeff_eq_lin]; rfl
  have hA0 : A' 0 = 1 := weightEnum_zero_of_unit ψ hψ
  rw [hes0, hlin (n / 2) hk, hys, hA0] at hw
  have hl : lin n A' (wCoef n L es ys) = ∑ j ∈ range (n + 1), (wCoef n L es ys j : ℝ) * weightEnum ψ j :=
    rfl
  rw [hl] at hw
  linarith

/-- **Complementary slackness.** If `π_{⌊n/2⌋}(ψ) = L` for a passing certificate, then `A_j = 0` wherever the
residual `w_j` is positive and `S_i = 0` wherever the multiplier `y_i` is positive. -/
theorem lp_equality_zero (n : ℕ) (L : ℚ) (es ys : List (ℕ × ℚ)) (h : lpCheck n L es ys = true)
    (ψ : Ψ n) (hψ : nsq ψ = 1) (heq : meanPurity ψ (n / 2) = L) :
    (∀ j ≤ n, 0 < wCoef n L es ys j → weightEnum ψ j = 0) ∧
    (∀ p ∈ ys, 0 < p.2 → shadowCoeff ψ p.1 = 0) := by
  have hs := lp_slack n L es ys h ψ hψ
  rw [heq, sub_self] at hs
  simp only [lpCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range] at h
  obtain ⟨⟨_, hys⟩, hw⟩ := h
  have hT : ∀ j ∈ range (n + 1), 0 ≤ (wCoef n L es ys j : ℝ) * weightEnum ψ j := fun j hj =>
    mul_nonneg (by exact_mod_cast hw j (Finset.mem_range.mp hj)) (weightEnum_nonneg ψ j)
  have hU : ∀ x ∈ ys.map (fun p => (p.2 : ℝ) * shadowCoeff ψ p.1), 0 ≤ x := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact mul_nonneg (by exact_mod_cast hys p hp) (shadow_nonneg ψ p.1)
  have hT0 := Finset.sum_nonneg hT
  have hU0 := List.sum_nonneg hU
  constructor
  · intro j hj hpos
    have hsum : ∑ j ∈ range (n + 1), (wCoef n L es ys j : ℝ) * weightEnum ψ j = 0 := by linarith
    have := (Finset.sum_eq_zero_iff_of_nonneg hT).mp hsum j (Finset.mem_range.mpr (by omega))
    have hp' : (0 : ℝ) < wCoef n L es ys j := by exact_mod_cast hpos
    exact (mul_eq_zero.mp this).resolve_left hp'.ne'
  · intro p hp hpos
    have hsum : (ys.map fun p => (p.2 : ℝ) * shadowCoeff ψ p.1).sum = 0 := by linarith
    have hle := List.single_le_sum hU _ (List.mem_map.mpr ⟨p, hp, rfl⟩)
    have h0 : (p.2 : ℝ) * shadowCoeff ψ p.1 = 0 := by
      have := hU _ (List.mem_map.mpr ⟨p, hp, rfl⟩)
      linarith
    have hp' : (0 : ℝ) < p.2 := by exact_mod_cast hpos
    exact (mul_eq_zero.mp h0).resolve_left hp'.ne'

/-! ### From the dual certificate to the unique profile -/

theorem aQ_eq (n s j : ℕ) (hs : s ≤ n) : aQ n s j = aCoef n s j := by
  unfold aQ aCoef; simp [hs]

theorem shQ_eq (n i j : ℕ) (hi : i ≤ n) : shQ n i j = shadowCoef n i j := by
  unfold shQ shadowCoef shadowNum
  push_cast
  rw [one_div, inv_mul_eq_div]
  congr 1
  rw [← Finset.sum_filter]
  have hf : (range (n + 1)).filter (fun u => u ≤ i) = range (i + 1) := by
    ext u; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [hf]
  refine Finset.sum_congr rfl fun u hu => ?_
  have hu' : u ≤ i := by simp only [Finset.mem_range] at hu; omega
  by_cases hc : i - u ≤ j
  · have hpar : ((j - (i - u)) % 2 = 0) ↔ Even (j + i + u) := by rw [Nat.even_iff]; omega
    by_cases h2 : (j - (i - u)) % 2 = 0
    · simp only [h2, ↓reduceIte, Even.neg_one_pow (hpar.mp h2)]
    · have hodd : Odd (j + i + u) := by
        rw [← Nat.not_even_iff_odd]; exact fun he => h2 (hpar.mpr he)
      simp only [h2, ↓reduceIte, Odd.neg_one_pow hodd]
  · rw [Nat.choose_eq_zero_of_lt (n := j) (k := i - u) (by omega)]; simp

/-- **A pure state attaining the Rains bound lies on the face.** -/
theorem faceR_of_equality (n : ℕ) (L : ℚ) (es ys : List (ℕ × ℚ)) (zA zS : List ℕ)
    (hcert : lpCheck n L es ys = true)
    (hzA : ∀ j ∈ zA, j ≤ n ∧ 0 < wCoef n L es ys j)
    (hzS : ∀ i ∈ zS, i ≤ n ∧ ∃ p ∈ ys, p.1 = i ∧ 0 < p.2)
    (ψ : Ψ n) (hψ : nsq ψ = 1) (heq : meanPurity ψ (n / 2) = L) :
    FaceR n zA zS (fun j => weightEnum ψ j) := by
  obtain ⟨hA, hS⟩ := lp_equality_zero n L es ys hcert ψ hψ heq
  refine ⟨weightEnum_zero_of_unit ψ hψ, fun j hj => hA j (hzA j hj).1 (hzA j hj).2, ?_, ?_⟩
  · intro s hs
    have hs1 : s ≤ n := by omega
    have hs2 : n - s ≤ n := Nat.sub_le _ _
    have e1 := meanPurity_eq_lin ψ hs1
    have e2 := meanPurity_eq_lin ψ hs2
    have e3 := meanPurity_compl ψ hs1
    have : ∑ j ∈ range (n + 1), ((aCoef n s j - aCoef n (n - s) j : ℚ) : ℝ) * weightEnum ψ j =
        meanPurity ψ s - meanPurity ψ (n - s) := by
      rw [e1, e2, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [aQ_eq n s j hs1, aQ_eq n (n - s) j hs2]; push_cast; ring
    rw [this, e3]; ring
  · intro i hi
    obtain ⟨hin, p, hp, hp1, hp2⟩ := hzS i hi
    have h0 := hS p hp hp2
    rw [hp1] at h0
    rw [shadowCoeff_eq_lin] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [shQ_eq n i j hin]

/-- Generic form: a certificate with strict complementarity, together with the integer uniqueness data of
the face, pins the Pauli weight distribution of every pure state at the bound. -/
theorem rains_equality_profile (n : ℕ) (L : ℚ) (es ys : List (ℕ × ℚ)) (zA zS : List ℕ)
    (spec : List (ℕ × ℕ)) (Lt : List (List ℤ)) (dd : ℤ) (tl : List ℤ)
    (hcert : lpCheck n L es ys = true)
    (hzA : ∀ j ∈ zA, j ≤ n ∧ 0 < wCoef n L es ys j)
    (hzS : ∀ i ∈ zS, i ≤ n ∧ ∃ p ∈ ys, p.1 = i ∧ 0 < p.2)
    (hspec : ∀ k < n + 1, (spec.getD k (0, 0)) = (0, 0) ∨
      ((spec.getD k (0, 0)).1 = 0 ∧ (spec.getD k (0, 0)).2 ∈ zA ∧ 0 < (spec.getD k (0, 0)).2 ∧
        (spec.getD k (0, 0)).2 ≤ n) ∨
      ((spec.getD k (0, 0)).1 = 1 ∧ (spec.getD k (0, 0)).2 < (n + 1) / 2) ∨
      ((spec.getD k (0, 0)).1 = 2 ∧ (spec.getD k (0, 0)).2 ∈ zS ∧ (spec.getD k (0, 0)).2 ≤ n))
    (hLM : ∀ j < n + 1, ∀ i < n + 1,
      ∑ k ∈ range (n + 1), (Lt.getD j []).getD k 0 * rowI n (spec.getD k (0, 0)).1
        (spec.getD k (0, 0)).2 i = if j = i then dd else 0)
    (hcol : ∀ j < n + 1, ∑ k ∈ range (n + 1), (Lt.getD j []).getD k 0 *
      (if (spec.getD k (0, 0)).1 = 0 ∧ (spec.getD k (0, 0)).2 = 0 then 1 else 0 : ℤ) =
      dd * tl.getD j 0)
    (hd : dd ≠ 0) (ψ : Ψ n) (hψ : nsq ψ = 1) (heq : meanPurity ψ (n / 2) = L) :
    ∀ j ≤ n, weightEnum ψ j = ((tl.getD j 0 : ℤ) : ℝ) :=
  faceR_unique_of_data n zA zS spec Lt dd tl _
    (faceR_of_equality n L es ys zA zS hcert hzA hzS ψ hψ heq) hspec hLM hcol hd

/-! ### Certificates (exact duals, strictly complementary) -/

def es7 : List (ℕ × ℚ) := [(0, (-11/140 : ℚ)), (1, (1/4 : ℚ)), (2, (-3/20 : ℚ)), (3, (-1/4 : ℚ))]
def ys7 : List (ℕ × ℚ) := [(0, (1/280 : ℚ)), (2, (1/280 : ℚ))]

def es13 : List (ℕ × ℚ) := [(0, (-6035/54912 : ℚ)), (1, (-7/384 : ℚ)), (2, (237/704 : ℚ)), (3, (-205/192 : ℚ)), (4, (-95/384 : ℚ)), (5, (153/128 : ℚ)), (6, (109/32 : ℚ))]
def ys13 : List (ℕ × ℚ) := [(0, (1/18304 : ℚ)), (1, (1/3432 : ℚ)), (2, (1/18304 : ℚ)), (6, (1/18304 : ℚ)), (10, (1/18304 : ℚ))]

def es19 : List (ℕ × ℚ) := [(0, (-628183/5912192 : ℚ)), (1, (-1005/18304 : ℚ)), (2, (9135/28288 : ℚ)), (3, (-27675/18304 : ℚ)), (4, (17859/4576 : ℚ)), (5, (-801/352 : ℚ)), (6, (-4935/4576 : ℚ)), (7, (-4755/352 : ℚ)), (8, (11745/704 : ℚ)), (9, (1267/64 : ℚ))]
def ys19 : List (ℕ × ℚ) := [(0, (5/5912192 : ℚ)), (1, (23/739024 : ℚ)), (2, (5/5912192 : ℚ)), (3, (3/739024 : ℚ)), (4, (5/5912192 : ℚ)), (8, (5/5912192 : ℚ)), (12, (5/5912192 : ℚ)), (16, (5/5912192 : ℚ))]

def es20 : List (ℕ × ℚ) := [(0, (54/4199 : ℚ)), (1, (-700/4199 : ℚ)), (2, (4725/4862 : ℚ)), (3, (-8100/2431 : ℚ)), (4, (1050/143 : ℚ)), (5, (-1512/143 : ℚ)), (6, (1350/143 : ℚ)), (7, (-600/143 : ℚ)), (8, (0 : ℚ)), (9, (0 : ℚ))]
def ys20 : List (ℕ × ℚ) := [(0, (103/1478048 : ℚ)), (2, (23/1478048 : ℚ)), (4, (3/1478048 : ℚ))]

theorem shadow_of_profile (n i : ℕ) (hi : i ≤ n) (ψ : Ψ n) (tl : List ℤ)
    (hA : ∀ j ≤ n, weightEnum ψ j = ((tl.getD j 0 : ℤ) : ℝ)) :
    shadowCoeff ψ i = ((∑ j ∈ range (n + 1), shadowCoef n i j * ((tl.getD j 0 : ℤ) : ℚ) : ℚ) : ℝ) := by
  rw [shadowCoeff_eq_lin]
  push_cast
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [hA j (by simp only [Finset.mem_range] at hj; omega), shQ_eq n i j hi]


theorem cert7 : lpCheck 7 (1/8 : ℚ) es7 ys7 = true := by decide +kernel

/-- The Rains bound `π_{⌊7/2⌋} ≥ 1/8` for every unit `7`-qubit vector. -/
theorem rains_bound_7 (ψ : Ψ 7) (hψ : nsq ψ = 1) :
    ((1/8 : ℚ) : ℝ) ≤ meanPurity ψ (7 / 2) := lp_bound 7 _ es7 ys7 cert7 ψ hψ

/-- **`prop:rains-faces`, `n = 7`**: a unit vector attaining the Rains bound has the unique Pauli weight
distribution `tgt7`. -/
theorem rains_equality_profile_7 (ψ : Ψ 7) (hψ : nsq ψ = 1)
    (heq : meanPurity ψ (7 / 2) = ((1/8 : ℚ) : ℝ)) :
    ∀ j ≤ 7, weightEnum ψ j = ((tgtL7.getD j 0 : ℤ) : ℝ) :=
  rains_equality_profile 7 (1/8 : ℚ) es7 ys7 zA7 zS7 spec7 Ltab7 dd7 tgtL7 cert7
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by unfold dd7; norm_num) ψ hψ heq

/-- ... and the unique shadow distribution `sh7`. -/
theorem rains_equality_shadow_7 (ψ : Ψ 7) (hψ : nsq ψ = 1)
    (heq : meanPurity ψ (7 / 2) = ((1/8 : ℚ) : ℝ)) (i : ℕ) (hi : i ≤ 7) :
    shadowCoeff ψ i = ((sh7 i : ℚ) : ℝ) := by
  rw [shadow_of_profile 7 i hi ψ tgtL7 (rains_equality_profile_7 ψ hψ heq)]
  congr 1
  exact face7_shadow i hi

theorem cert13 : lpCheck 13 (25/1408 : ℚ) es13 ys13 = true := by decide +kernel

/-- The Rains bound `π_{⌊13/2⌋} ≥ 25/1408` for every unit `13`-qubit vector. -/
theorem rains_bound_13 (ψ : Ψ 13) (hψ : nsq ψ = 1) :
    ((25/1408 : ℚ) : ℝ) ≤ meanPurity ψ (13 / 2) := lp_bound 13 _ es13 ys13 cert13 ψ hψ

/-- **`prop:rains-faces`, `n = 13`**: a unit vector attaining the Rains bound has the unique Pauli weight
distribution `tgt13`. -/
theorem rains_equality_profile_13 (ψ : Ψ 13) (hψ : nsq ψ = 1)
    (heq : meanPurity ψ (13 / 2) = ((25/1408 : ℚ) : ℝ)) :
    ∀ j ≤ 13, weightEnum ψ j = ((tgtL13.getD j 0 : ℤ) : ℝ) :=
  rains_equality_profile 13 (25/1408 : ℚ) es13 ys13 zA13 zS13 spec13 Ltab13 dd13 tgtL13 cert13
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by unfold dd13; norm_num) ψ hψ heq

/-- ... and the unique shadow distribution `sh13`. -/
theorem rains_equality_shadow_13 (ψ : Ψ 13) (hψ : nsq ψ = 1)
    (heq : meanPurity ψ (13 / 2) = ((25/1408 : ℚ) : ℝ)) (i : ℕ) (hi : i ≤ 13) :
    shadowCoeff ψ i = ((sh13 i : ℚ) : ℝ) := by
  rw [shadow_of_profile 13 i hi ψ tgtL13 (rains_equality_profile_13 ψ hψ heq)]
  congr 1
  exact face13_shadow i hi

theorem cert19 : lpCheck 19 (93/38896 : ℚ) es19 ys19 = true := by decide +kernel

/-- The Rains bound `π_{⌊19/2⌋} ≥ 93/38896` for every unit `19`-qubit vector. -/
theorem rains_bound_19 (ψ : Ψ 19) (hψ : nsq ψ = 1) :
    ((93/38896 : ℚ) : ℝ) ≤ meanPurity ψ (19 / 2) := lp_bound 19 _ es19 ys19 cert19 ψ hψ

/-- **`prop:rains-faces`, `n = 19`**: a unit vector attaining the Rains bound has the unique Pauli weight
distribution `tgt19`. -/
theorem rains_equality_profile_19 (ψ : Ψ 19) (hψ : nsq ψ = 1)
    (heq : meanPurity ψ (19 / 2) = ((93/38896 : ℚ) : ℝ)) :
    ∀ j ≤ 19, weightEnum ψ j = ((tgtL19.getD j 0 : ℤ) : ℝ) :=
  rains_equality_profile 19 (93/38896 : ℚ) es19 ys19 zA19 zS19 spec19 Ltab19 dd19 tgtL19 cert19
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by unfold dd19; norm_num) ψ hψ heq

/-- ... and the unique shadow distribution `sh19`. -/
theorem rains_equality_shadow_19 (ψ : Ψ 19) (hψ : nsq ψ = 1)
    (heq : meanPurity ψ (19 / 2) = ((93/38896 : ℚ) : ℝ)) (i : ℕ) (hi : i ≤ 19) :
    shadowCoeff ψ i = ((sh19 i : ℚ) : ℝ) := by
  rw [shadow_of_profile 19 i hi ψ tgtL19 (rains_equality_profile_19 ψ hψ heq)]
  congr 1
  exact face19_shadow i hi

theorem cert20 : lpCheck 20 (1193/739024 : ℚ) es20 ys20 = true := by decide +kernel

/-- The Rains bound `π_{⌊20/2⌋} ≥ 1193/739024` for every unit `20`-qubit vector. -/
theorem rains_bound_20 (ψ : Ψ 20) (hψ : nsq ψ = 1) :
    ((1193/739024 : ℚ) : ℝ) ≤ meanPurity ψ (20 / 2) := lp_bound 20 _ es20 ys20 cert20 ψ hψ

/-- **`prop:rains-faces`, `n = 20`**: a unit vector attaining the Rains bound has the unique Pauli weight
distribution `tgt20`. -/
theorem rains_equality_profile_20 (ψ : Ψ 20) (hψ : nsq ψ = 1)
    (heq : meanPurity ψ (20 / 2) = ((1193/739024 : ℚ) : ℝ)) :
    ∀ j ≤ 20, weightEnum ψ j = ((tgtL20.getD j 0 : ℤ) : ℝ) :=
  rains_equality_profile 20 (1193/739024 : ℚ) es20 ys20 zA20 zS20 spec20 Ltab20 dd20 tgtL20 cert20
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by unfold dd20; norm_num) ψ hψ heq

/-- ... and the unique shadow distribution `sh20`. -/
theorem rains_equality_shadow_20 (ψ : Ψ 20) (hψ : nsq ψ = 1)
    (heq : meanPurity ψ (20 / 2) = ((1193/739024 : ℚ) : ℝ)) (i : ℕ) (hi : i ≤ 20) :
    shadowCoeff ψ i = ((sh20 i : ℚ) : ℝ) := by
  rw [shadow_of_profile 20 i hi ψ tgtL20 (rains_equality_profile_20 ψ hψ heq)]
  congr 1
  exact face20_shadow i hi

/-- **No stabilizer state attains the Rains bound at `n = 7`** (`S_1 = 7/4` is not an integer). -/
theorem stabilizer_ne_rains_7 (ψ : Ψ 7) (h : IsStabilizerState ψ) :
    meanPurity ψ (7 / 2) ≠ ((1/8 : ℚ) : ℝ) := by
  intro heq
  obtain ⟨m, hm⟩ := h.shadowCoeff_nat 1
  have := rains_equality_shadow_7 ψ h.1 heq 1 (by norm_num)
  rw [hm, sh7_one] at this
  push_cast at this
  have h4 : ((4 : ℝ) * m) = 7 := by linarith
  have h5 : 4 * m = 7 := by exact_mod_cast h4
  omega

/-- **No stabilizer state attains the Rains bound at `n = 13`** (`S_3 = 39/4` is not an integer). -/
theorem stabilizer_ne_rains_13 (ψ : Ψ 13) (h : IsStabilizerState ψ) :
    meanPurity ψ (13 / 2) ≠ ((25/1408 : ℚ) : ℝ) := by
  intro heq
  obtain ⟨m, hm⟩ := h.shadowCoeff_nat 3
  have := rains_equality_shadow_13 ψ h.1 heq 3 (by norm_num)
  rw [hm, sh13_three] at this
  push_cast at this
  have h4 : ((4 : ℝ) * m) = 39 := by linarith
  have h5 : 4 * m = 39 := by exact_mod_cast h4
  omega

/-- info: 'FormalResearch.FourQubitEntropy.SevenQubitRainsEquality.rains_bound_7' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rains_bound_7

/-- info: 'FormalResearch.FourQubitEntropy.SevenQubitRainsEquality.rains_bound_13' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rains_bound_13

/-- info: 'FormalResearch.FourQubitEntropy.SevenQubitRainsEquality.rains_bound_19' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rains_bound_19

/-- info: 'FormalResearch.FourQubitEntropy.SevenQubitRainsEquality.rains_bound_20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rains_bound_20

/-- info: 'FormalResearch.FourQubitEntropy.SevenQubitRainsEquality.rains_equality_profile_7' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rains_equality_profile_7

/-- info: 'FormalResearch.FourQubitEntropy.SevenQubitRainsEquality.rains_equality_profile_13' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rains_equality_profile_13

/-- info: 'FormalResearch.FourQubitEntropy.SevenQubitRainsEquality.rains_equality_profile_19' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rains_equality_profile_19

/-- info: 'FormalResearch.FourQubitEntropy.SevenQubitRainsEquality.rains_equality_shadow_20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rains_equality_shadow_20

/-- info: 'FormalResearch.FourQubitEntropy.SevenQubitRainsEquality.stabilizer_ne_rains_7' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stabilizer_ne_rains_7

/-- info: 'FormalResearch.FourQubitEntropy.SevenQubitRainsEquality.stabilizer_ne_rains_13' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stabilizer_ne_rains_13

end FormalResearch.FourQubitEntropy.SevenQubitRainsEquality
