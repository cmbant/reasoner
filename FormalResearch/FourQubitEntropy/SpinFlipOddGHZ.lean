import FormalResearch.FourQubitEntropy.SpinFlipOddSector

/-!
# The GHZ state has vanishing odd-weight Pauli weights below full weight

Source: `ResearchNotes/QI/seven_qubit_entanglement/spinflip_tradeoff.tex` (QIprojects PR #200), last paragraph
of the proof of `thm:odd-spinflip-tradeoff`: for `GHZ_n = (|0⟩^{⊗n} + |1⟩^{⊗n})/√2` a Pauli word with an `X` or
`Y` on some but not all sites has zero expectation, and a `Z`-word of weight `j < n` has nonzero
expectation only if `j` is even; hence `A_j(GHZ_n) = 0` for odd `j < n`.

* `ghz n`, `nsq_ghz`: the state and its norm (`n ≥ 1`);
* `pexp_ghz_eq_zero`: `⟨P_a⟩ = 0` for every word of odd weight `< n` (`n ≥ 1`);
* `A_ghz_odd`: `A_j(GHZ_n) = 0` for odd `j < n`.

Claim class: **proved**.
-/

open scoped ComplexConjugate BigOperators
open FormalResearch.FrameFree.NQubit

namespace FormalResearch.FourQubitEntropy.SpinFlip

variable {n : ℕ}

/-- The all-zeros configuration. -/
def z0 (n : ℕ) : Cfg n := fun _ => 0
/-- The all-ones configuration. -/
def z1 (n : ℕ) : Cfg n := fun _ => 1

theorem z0_ne_z1 (hn : 1 ≤ n) : z0 n ≠ z1 n := by
  intro h
  have := congrFun h ⟨0, hn⟩
  simp [z0, z1] at this

/-- `GHZ_n = (|0…0⟩ + |1…1⟩)/√2`. -/
noncomputable def ghz (n : ℕ) : Ψ n :=
  fun x => if x = z0 n ∨ x = z1 n then (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) else 0

theorem sum_ghz (hn : 1 ≤ n) (F : Cfg n → ℂ) :
    ∑ x, ghz n x * F x = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (F (z0 n) + F (z1 n)) := by
  rw [Finset.sum_eq_add (z0 n) (z1 n) (z0_ne_z1 hn)]
  · simp [ghz]; ring
  · intro x _ hx
    simp [ghz, hx.1, hx.2]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro h; exact absurd (Finset.mem_univ _) h

theorem conj_ghz (x : Cfg n) : conj (ghz n x) = ghz n x := by
  unfold ghz; split_ifs <;> simp

theorem nsq_ghz (hn : 1 ≤ n) : nsq (ghz n) = 1 := by
  unfold nsq
  rw [Finset.sum_eq_add (z0 n) (z1 n) (z0_ne_z1 hn)]
  · simp [ghz, Complex.normSq_ofReal]
    norm_num
  · intro x _ hx
    simp [ghz, hx.1, hx.2]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro h; exact absurd (Finset.mem_univ _) h

theorem pexp_ghz (hn : 1 ≤ n) (a : Fin n → Fin 4) :
    pexp (ghz n) a = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) *
      ((∏ i, pauliSU (a i) 0 0) + (∏ i, pauliSU (a i) 0 1) + (∏ i, pauliSU (a i) 1 0)
        + (∏ i, pauliSU (a i) 1 1)) := by
  rw [pexp_unfold]
  simp_rw [conj_ghz]
  rw [sum_ghz hn]
  have hin : ∀ x : Cfg n, ∑ y, (∏ i, pauliSU (a i) (x i) (y i)) * ghz n y
      = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * ((∏ i, pauliSU (a i) (x i) (z0 n i))
          + (∏ i, pauliSU (a i) (x i) (z1 n i))) := by
    intro x
    have := sum_ghz hn (fun y => ∏ i, pauliSU (a i) (x i) (y i))
    calc ∑ y, (∏ i, pauliSU (a i) (x i) (y i)) * ghz n y
        = ∑ y, ghz n y * ∏ i, pauliSU (a i) (x i) (y i) :=
          Finset.sum_congr rfl fun y _ => mul_comm _ _
      _ = _ := this
  rw [hin (z0 n), hin (z1 n)]
  simp only [z0, z1]
  ring

theorem pU00 (b : Fin 4) :
    pauliSU b 0 0 = if b = 0 then 1 else if b = 3 then -Complex.I else 0 := by
  fin_cases b <;> simp [pauliSU]

theorem pU11 (b : Fin 4) :
    pauliSU b 1 1 = if b = 0 then 1 else if b = 3 then Complex.I else 0 := by
  fin_cases b <;> simp [pauliSU]

theorem pU01 (b : Fin 4) :
    pauliSU b 0 1 = if b = 1 then -Complex.I else if b = 2 then -1 else 0 := by
  fin_cases b <;> simp [pauliSU]

theorem pU10 (b : Fin 4) :
    pauliSU b 1 0 = if b = 1 then -Complex.I else if b = 2 then 1 else 0 := by
  fin_cases b <;> simp [pauliSU]

theorem exists_id_of_wt_lt (a : Fin n → Fin 4) (h : wt a < n) : ∃ i, a i = 0 := by
  by_contra hne
  push Not at hne
  have : wt a = n := by
    unfold wt
    rw [Finset.filter_true_of_mem (fun i _ => hne i)]
    simp
  omega

/-- **A Pauli word of odd weight `< n` has zero GHZ expectation.** -/
theorem pexp_ghz_eq_zero (hn : 1 ≤ n) (a : Fin n → Fin 4) (hodd : Odd (wt a)) (hlt : wt a < n) :
    pexp (ghz n) a = 0 := by
  rw [pexp_ghz hn]
  obtain ⟨i0, hi0⟩ := exists_id_of_wt_lt a hlt
  have h01 : ∏ i, pauliSU (a i) 0 1 = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i0) (by rw [pU01, hi0]; simp)
  have h10 : ∏ i, pauliSU (a i) 1 0 = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i0) (by rw [pU10, hi0]; simp)
  rw [h01, h10]
  by_cases hxy : ∃ i, a i = 1 ∨ a i = 2
  · obtain ⟨i1, hi1⟩ := hxy
    have h00 : ∏ i, pauliSU (a i) 0 0 = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i1) (by rcases hi1 with h | h <;> rw [pU00, h] <;> simp)
    have h11 : ∏ i, pauliSU (a i) 1 1 = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i1) (by rcases hi1 with h | h <;> rw [pU11, h] <;> simp)
    rw [h00, h11]; simp
  · push Not at hxy
    have hz : ∀ i, a i = 0 ∨ a i = 3 := by
      intro i
      have h1 := (hxy i).1
      have h2 := (hxy i).2
      revert h1 h2
      generalize a i = b
      revert b; decide
    have h00 : ∏ i, pauliSU (a i) 0 0 = (-Complex.I) ^ wt a := by
      calc ∏ i, pauliSU (a i) 0 0 = ∏ i, (if a i = 0 then (1 : ℂ) else -Complex.I) :=
            Finset.prod_congr rfl fun i _ => by
              rw [pU00]; rcases hz i with h | h <;> simp [h]
        _ = _ := by
            unfold wt; rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
    have h11 : ∏ i, pauliSU (a i) 1 1 = Complex.I ^ wt a := by
      calc ∏ i, pauliSU (a i) 1 1 = ∏ i, (if a i = 0 then (1 : ℂ) else Complex.I) :=
            Finset.prod_congr rfl fun i _ => by
              rw [pU11]; rcases hz i with h | h <;> simp [h]
        _ = _ := by
            unfold wt; rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
    rw [h00, h11, hodd.neg_pow]; ring

/-- **`A_j(GHZ_n) = 0` for odd `j < n`.** -/
theorem A_ghz_odd (hn : 1 ≤ n) {j : ℕ} (hj : Odd j) (hjn : j < n) : A (ghz n) j = 0 := by
  unfold A
  refine Finset.sum_eq_zero fun a ha => ?_
  have h := (Finset.mem_filter.mp ha).2
  unfold pw
  rw [pexp_ghz_eq_zero hn a (h ▸ hj) (h ▸ hjn)]
  simp

end FormalResearch.FourQubitEntropy.SpinFlip
