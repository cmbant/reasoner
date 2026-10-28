import FormalResearch.FourQubitEntropy.SevenQubitHammingGlue
import FormalResearch.FourQubitEntropy.SpinFlipOmega

/-!
# Seven qubits: the `11/49` bound on Hamming-ball states (`cor:seven-hamming-ball-shadow`)

Source: `ResearchNotes/QI/seven_qubit_entanglement/hamming_ball_schmidt.tex`,
`cor:seven-hamming-ball-shadow`.

**Proved here (complex states, all axioms standard).**
`ball_purity_11_49`: for `ψ : Ψ 7` with `nsq ψ = 1` supported on Hamming weight `≤ 2`,
`11/49 + (58 W₀ + 28 W₁)/245 ≤ Pur ψ 3 / 35`, where `W_j` is the `|ψ|²`-mass on weight `j`;
`ball_purity_11_49_bound` is the bound `11/49 ≤ Pur ψ 3 / 35`.

**Route (differs from the paper).** The paper uses the Rains shadow identity. That identity is *not*
formalized here. Instead:
* `signed_weighted_A_ball_zero`: for a state supported on weight `≤ r` with `2 r < n - 1`,
  `Σ_j (-1)^j (n - j) A_j = 0` (a single-site signed Pauli completeness kernel,
  `kernel_supp_signed`, `signed_wsupp_eq`, `signed_wsupp_ball_zero`);
* together with `A_0 = 1`, `Σ A_j = 2^7`, `Σ (-1)^j A_j = 0` (Kramers, `n` odd) and the complementarity
  `Pur_r = Pur_{7-r}`, this gives `A_3 = 7 + A_1 + A_2` and `Pur₃ = (35 + 15 A_1 + 5 A_2 + A_3)/8`;
* `A_1 ≥ Z²/7`, `A_2 ≥ K²/21` from the `Z`-type words (`pw_zword`, `sq_zsum_le_A`, Cauchy-Schwarz) with
  the character sums `sum_chi1_seven`, `sum_chi2_seven` (checked by `decide +kernel` on the `128`
  configurations); for ball states `Z = 7W₀ + 5W₁ + 3W₂`, `K = 21W₀ + 9W₁ + W₂`.

**Not proved here.** The equality characterization of the corollary, and any statement for
other `(n, r)`.
-/

open scoped ComplexConjugate BigOperators
open FormalResearch.FrameFree.NQubit

open FormalResearch.FourQubitEntropy.SevenQubitIco.HammingGlue (wf)

theorem chi1_seven : ∀ x : Fin 7 → Fin 2,
    (∑ S ∈ (Finset.univ : Finset (Fin 7)).powersetCard 1, ∏ j ∈ S, (if x j = 0 then (1 : ℤ) else -1))
      = 7 - 2 * (wf x : ℤ) := by
  decide +kernel

theorem chi2_seven : ∀ x : Fin 7 → Fin 2,
    2 * (∑ S ∈ (Finset.univ : Finset (Fin 7)).powersetCard 2, ∏ j ∈ S, (if x j = 0 then (1 : ℤ) else -1))
      = (7 - 2 * (wf x : ℤ)) ^ 2 - 7 := by
  decide +kernel


namespace FormalResearch.FourQubitEntropy.SpinFlip

variable {n : ℕ}

/-- Signed completeness kernel on words supported in `S`. -/
theorem kernel_supp_signed (S : Finset (Fin n)) (x y x' y' : Cfg n) :
    ∑ a ∈ wsupp S, (∏ i, (if a i = 0 then (1 : ℂ) else -1)) *
        ((∏ i, pauliSU (a i) (x i) (y i)) * conj (∏ i, pauliSU (a i) (x' i) (y' i)))
      = ∏ i, (if i ∈ S then 2 * (eps (x i) (y' i) * eps (y i) (x' i))
          else (if x i = y i ∧ x' i = y' i then (1 : ℂ) else 0)) := by
  simp_rw [map_prod, ← Finset.prod_mul_distrib]
  unfold wsupp
  rw [← Finset.prod_univ_sum (fun i => if i ∈ S then (Finset.univ : Finset (Fin 4)) else {0})
    (fun i b => (if b = 0 then (1 : ℂ) else -1) *
      (pauliSU b (x i) (y i) * conj (pauliSU b (x' i) (y' i))))]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : i ∈ S
  · simp only [hi, ite_true]
    exact pauliSU_signed _ _ _ _
  · simp only [hi, ite_false, Finset.sum_singleton]
    by_cases h1 : x i = y i <;> by_cases h2 : x' i = y' i <;>
      simp [pauliSU, h1, h2]


/-- The per-site factor of the signed kernel. -/
noncomputable def gK (S : Finset (Fin n)) (x y x' y' : Cfg n) (i : Fin n) : ℂ :=
  if i ∈ S then 2 * (eps (x i) (y' i) * eps (y i) (x' i))
    else (if x i = y i ∧ x' i = y' i then (1 : ℂ) else 0)

/-- **Signed Pauli sum on a site set, as a four-fold configuration sum.** -/
theorem signed_wsupp_eq (ψ : Ψ n) (S : Finset (Fin n)) :
    ((∑ a ∈ wsupp S, (-1 : ℝ) ^ wt a * pw ψ a : ℝ) : ℂ) =
      ∑ x, ∑ y, ∑ x', ∑ y', (conj (ψ x) * ψ y * (ψ x' * conj (ψ y'))) *
        ∏ i, gK S x y x' y' i := by
  push_cast
  simp_rw [← signprod_eq, pw_cast]
  exact wavg_aux (wsupp S) (fun (a : Fin n → Fin 4) (x y : Cfg n) => ∏ i, pauliSU (a i) (x i) (y i))
    (fun a => ∏ i, (if a i = 0 then (1 : ℂ) else -1))
    (fun x y x' y' => ∏ i, gK S x y x' y' i)
    (fun x y x' y' => kernel_supp_signed S x y x' y') ψ ψ



theorem card_le_wf_add (S : Finset (Fin n)) (x y : Cfg n) (h : ∀ i ∈ S, x i ≠ y i) :
    S.card ≤ wf x + wf y := by
  unfold wf
  calc S.card ≤ ((Finset.univ.filter fun i => x i ≠ 0) ∪ (Finset.univ.filter fun i => y i ≠ 0)).card := by
        apply Finset.card_le_card
        intro i hi
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        have := h i hi
        omega
    _ ≤ _ := Finset.card_union_le _ _

/-- **Vanishing of the signed Pauli sum for ball-supported vectors.** If `ψ` is supported on strings of
weight `≤ r` and `2r < |S|`, then `Σ_{supp a ⊆ S} (-1)^{wt a} ⟨P_a⟩² = 0`. (Each term of the kernel
expansion contains `ψ x · conj ψ y'` with `x_i ≠ y'_i` on all of `S`, forcing `wt x + wt y' ≥ |S|`.) -/
theorem signed_wsupp_ball_zero (ψ : Ψ n) (r : ℕ) (hsupp : ∀ x, r < wf x → ψ x = 0)
    (S : Finset (Fin n)) (hS : 2 * r < S.card) :
    ∑ a ∈ wsupp S, (-1 : ℝ) ^ wt a * pw ψ a = 0 := by
  apply Complex.ofReal_injective
  rw [signed_wsupp_eq]
  push_cast
  refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ =>
    Finset.sum_eq_zero fun x' _ => Finset.sum_eq_zero fun y' _ => ?_
  by_cases hx : r < wf x
  · simp [hsupp x hx]
  by_cases hy : r < wf y'
  · simp [hsupp y' hy]
  have : ∏ i, gK S x y x' y' i = 0 := by
    by_contra hne
    have hall : ∀ i, gK S x y x' y' i ≠ 0 := fun i => by
      intro h0; exact hne (Finset.prod_eq_zero (Finset.mem_univ i) h0)
    have hne' : ∀ i ∈ S, x i ≠ y' i := by
      intro i hi h
      have := hall i
      simp only [gK, hi, ite_true] at this
      apply this
      have e : ∀ a : Fin 2, eps a a = 0 := by intro a; fin_cases a <;> simp [eps]
      rw [h, e]; simp
    have := card_le_wf_add S x y' hne'
    omega
  rw [this, mul_zero]


theorem wsupp_erase (i : Fin n) (a : Fin n → Fin 4) :
    a ∈ wsupp (Finset.univ.erase i) ↔ a i = 0 := by
  rw [mem_wsupp]
  constructor
  · intro h; exact h i (by simp)
  · intro h j hj
    have : j = i := by simpa using hj
    rw [this]; exact h

theorem card_zero_sites (a : Fin n → Fin 4) :
    (Finset.univ.filter fun i => a i = 0).card = n - wt a := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun i => a i = 0)
  rw [Finset.card_univ, Fintype.card_fin] at h
  unfold wt
  simp only [ne_eq]
  omega

/-- `Σ_i Σ_{supp a ∌ i} f(a) = Σ_a (n - wt a) f(a)`. -/
theorem sum_erase_sites (f : (Fin n → Fin 4) → ℝ) :
    ∑ i : Fin n, ∑ a ∈ wsupp (Finset.univ.erase i), f a =
      ∑ a : Fin n → Fin 4, ((n : ℝ) - wt a) * f a := by
  have h1 : ∀ i : Fin n, ∑ a ∈ wsupp (Finset.univ.erase i), f a =
      ∑ a : Fin n → Fin 4, if a i = 0 then f a else 0 := by
    intro i
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext a; simp [wsupp_erase]
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, card_zero_sites]
  have : wt a ≤ n := wt_le a
  rw [Nat.cast_sub this]

/-- **Vanishing of the shadow-type weight sum** `Σ_j (-1)^j (n - j) A_j` for vectors supported on strings of
weight `≤ r` with `2r < n - 1`. (This is `32 S_1` of the paper at `n = 7, r = 2`, with `τ_7 = 0`.) -/
theorem signed_weighted_A_ball_zero (ψ : Ψ n) (r : ℕ) (hsupp : ∀ x, r < wf x → ψ x = 0)
    (hr : 2 * r < n - 1) :
    ∑ j ∈ Finset.range (n + 1), (-1 : ℝ) ^ j * ((n : ℝ) - j) * A ψ j = 0 := by
  have h := sum_erase_sites (n := n) (fun a => (-1 : ℝ) ^ wt a * pw ψ a)
  have h0 : ∀ i : Fin n, ∑ a ∈ wsupp (Finset.univ.erase i), (-1 : ℝ) ^ wt a * pw ψ a = 0 := by
    intro i
    refine signed_wsupp_ball_zero ψ r hsupp _ ?_
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    omega
  simp only [h0, Finset.sum_const_zero] at h
  have h2 := sum_A_eq ψ (fun j => (-1 : ℝ) ^ j * ((n : ℝ) - j))
  calc _ = ∑ a : Fin n → Fin 4, ((n : ℝ) - wt a) * ((-1 : ℝ) ^ wt a * pw ψ a) := by
        rw [h2]; exact Finset.sum_congr rfl fun a _ => by ring
    _ = 0 := h.symm


/-- The `Z`-type Pauli word with `σ_z` (as `-iσ_z`) exactly on `S`. -/
def zword (S : Finset (Fin n)) : Fin n → Fin 4 := fun j => if j ∈ S then 3 else 0

theorem wt_zword (S : Finset (Fin n)) : wt (zword S) = S.card := by
  unfold wt zword
  congr 1
  ext j
  by_cases h : j ∈ S <;> simp [h]

theorem zword_injective : Function.Injective (zword : Finset (Fin n) → Fin n → Fin 4) := by
  intro S T h
  ext j
  have := congrFun h j
  by_cases hS : j ∈ S <;> by_cases hT : j ∈ T <;> simp_all [zword]

/-- The sign character `χ_S(x) = ∏_{j∈S} (-1)^{x_j}`. -/
def zchi (S : Finset (Fin n)) (x : Cfg n) : ℝ := ∏ j ∈ S, (if x j = 0 then (1 : ℝ) else -1)

theorem pauliSU_three_diag (a : Fin 2) :
    pauliSU 3 a a = (-Complex.I) * (if a = 0 then (1 : ℂ) else -1) := by
  fin_cases a <;> simp [pauliSU]

theorem pauliSU_three_off (a b : Fin 2) (h : a ≠ b) : pauliSU 3 a b = 0 := by
  fin_cases a <;> fin_cases b <;> simp_all [pauliSU]

theorem pauliSU_zero_off (a b : Fin 2) (h : a ≠ b) : pauliSU 0 a b = 0 := by
  fin_cases a <;> fin_cases b <;> simp_all [pauliSU]

theorem Mat_zword (S : Finset (Fin n)) (x y : Cfg n) :
    (∏ j, pauliSU (zword S j) (x j) (y j)) =
      if x = y then ((-Complex.I) ^ S.card * (zchi S x : ℂ)) else 0 := by
  by_cases hxy : x = y
  · subst hxy
    simp only [ite_true]
    have h1 : ∀ j, pauliSU (zword S j) (x j) (x j) =
        if j ∈ S then (-Complex.I) * (if x j = 0 then (1 : ℂ) else -1) else 1 := by
      intro j
      by_cases hj : j ∈ S
      · simp only [zword, hj, ite_true]
        exact pauliSU_three_diag _
      · simp [zword, hj, pauliSU]
    simp_rw [h1]
    rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_mul_distrib, Finset.prod_const, zchi]
    push_cast
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    split_ifs <;> simp
  · rw [ite_eq_right_iff.mpr (fun h => absurd h hxy)]
    obtain ⟨j, hj⟩ : ∃ j, x j ≠ y j := by
      by_contra h; push Not at h; exact hxy (funext h)
    refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
    by_cases hjS : j ∈ S
    · simp only [zword, hjS, ite_true]
      exact pauliSU_three_off _ _ hj
    · simp only [zword, hjS, ite_false]
      exact pauliSU_zero_off _ _ hj

theorem pexp_zword (ψ : Ψ n) (S : Finset (Fin n)) :
    pexp ψ (zword S) = (-Complex.I) ^ S.card *
      ((∑ x, Complex.normSq (ψ x) * zchi S x : ℝ) : ℂ) := by
  rw [pexp_unfold]
  have e : ∀ x y : Cfg n, (∏ i, pauliSU (zword S i) (x i) (y i)) =
      if x = y then ((-Complex.I) ^ S.card * (zchi S x : ℂ)) else 0 := fun x y => Mat_zword S x y
  simp only [e]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Complex.normSq_eq_conj_mul_self]
  ring

/-- `⟨P_{zword S}⟩² = (Σ_x |ψ_x|² χ_S(x))²`. -/
theorem pw_zword (ψ : Ψ n) (S : Finset (Fin n)) :
    pw ψ (zword S) = (∑ x, Complex.normSq (ψ x) * zchi S x) ^ 2 := by
  unfold pw
  rw [pexp_zword, map_mul, map_pow, Complex.normSq_ofReal]
  have : Complex.normSq (-Complex.I) = 1 := by simp [Complex.normSq_apply]
  rw [this]; simp [sq]


theorem A_ge_zwords (ψ : Ψ n) (k : ℕ) :
    ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, pw ψ (zword S) ≤ A ψ k := by
  unfold A
  rw [← Finset.sum_image (f := fun a => pw ψ a) (g := zword) (fun S _ T _ h => zword_injective h)]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro a ha
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp ha
    simp [wt_zword, (Finset.mem_powersetCard.mp hS).2]
  · intro a _ _; exact pw_nonneg ψ a

/-- Cauchy-Schwarz over the `Z`-type words of weight `k`:
`(Σ_{|S|=k} Σ_x |ψ_x|² χ_S(x))² ≤ C(n,k) A_k`. -/
theorem sq_zsum_le_A (ψ : Ψ n) (k : ℕ) :
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        ∑ x, Complex.normSq (ψ x) * zchi S x) ^ 2 ≤ (n.choose k : ℝ) * A ψ k := by
  have h1 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n)).powersetCard k)
    (f := fun S => ∑ x, Complex.normSq (ψ x) * zchi S x)
  rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] at h1
  have h2 := A_ge_zwords ψ k
  simp_rw [pw_zword] at h2
  have h3 : (0 : ℝ) ≤ n.choose k := by positivity
  calc _ ≤ _ := h1
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 h3

/-- The sum over `S` of the characters, rewritten through the string weight (`n = 7`). -/
theorem sum_chi1_seven (x : Cfg 7) :
    (∑ S ∈ (Finset.univ : Finset (Fin 7)).powersetCard 1, zchi S x) = 7 - 2 * (wf x : ℝ) := by
  have h := chi1_seven x
  have : (((∑ S ∈ (Finset.univ : Finset (Fin 7)).powersetCard 1,
      ∏ j ∈ S, (if x j = 0 then (1 : ℤ) else -1) : ℤ)) : ℝ) = ((7 - 2 * (wf x : ℤ) : ℤ) : ℝ) := by
    rw [h]
  push_cast at this
  unfold zchi
  exact this

theorem sum_chi2_seven (x : Cfg 7) :
    2 * (∑ S ∈ (Finset.univ : Finset (Fin 7)).powersetCard 2, zchi S x) =
      (7 - 2 * (wf x : ℝ)) ^ 2 - 7 := by
  have h := chi2_seven x
  have : ((2 * (∑ S ∈ (Finset.univ : Finset (Fin 7)).powersetCard 2,
      ∏ j ∈ S, (if x j = 0 then (1 : ℤ) else -1)) : ℤ) : ℝ) =
        (((7 - 2 * (wf x : ℤ)) ^ 2 - 7 : ℤ) : ℝ) := by
    rw [h]
  push_cast at this
  unfold zchi
  exact this



/-- The mass of `|ψ|²` on strings of Hamming weight `j`. -/
noncomputable def Wmass (ψ : Ψ n) (j : ℕ) : ℝ :=
  ∑ x : Cfg n, if wf x = j then Complex.normSq (ψ x) else 0

theorem Wmass_nonneg (ψ : Ψ n) (j : ℕ) : 0 ≤ Wmass ψ j :=
  Finset.sum_nonneg fun x _ => by split_ifs <;> simp [Complex.normSq_nonneg]

/-- For `ψ` supported on weights `≤ 2`, a weight function integrates against `|ψ|²` through the
three masses `W₀, W₁, W₂`. -/
theorem sum_normSq_weight (ψ : Ψ n) (hsupp : ∀ x, 2 < wf x → ψ x = 0) (g : ℕ → ℝ) :
    ∑ x : Cfg n, Complex.normSq (ψ x) * g (wf x) =
      g 0 * Wmass ψ 0 + g 1 * Wmass ψ 1 + g 2 * Wmass ψ 2 := by
  unfold Wmass
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : 2 < wf x
  · simp [hsupp x h]
  · have : wf x = 0 ∨ wf x = 1 ∨ wf x = 2 := by omega
    rcases this with h0 | h0 | h0 <;> simp [h0] <;> ring


/-- **Seven qubits, ball states: `Pur₃/35 ≥ 11/49 + (58 W₀ + 28 W₁)/245`.**
For a unit vector supported on strings of Hamming weight `≤ 2` (the Hamming ball of radius 2), the mean
three-qubit purity is at least `11/49`, with the explicit excess above in the masses `W₀, W₁` on weights
`0, 1`. -/
theorem ball_purity_11_49 (ψ : Ψ 7) (hn : nsq ψ = 1) (hsupp : ∀ x, 2 < wf x → ψ x = 0) :
    11 / 49 + 58 / 245 * Wmass ψ 0 + 28 / 245 * Wmass ψ 1 ≤ Pur ψ 3 / 35 := by
  have hW : Wmass ψ 0 + Wmass ψ 1 + Wmass ψ 2 = 1 := by
    have h := sum_normSq_weight ψ hsupp (fun _ => 1)
    simp only [mul_one, one_mul] at h
    rw [← h]; exact hn
  have hW0 := Wmass_nonneg ψ 0
  have hW1 := Wmass_nonneg ψ 1
  have hW2 := Wmass_nonneg ψ 2
  -- the Z- and K-type sums
  have hZ : ∑ S ∈ (Finset.univ : Finset (Fin 7)).powersetCard 1,
      ∑ x, Complex.normSq (ψ x) * zchi S x = 7 * Wmass ψ 0 + 5 * Wmass ψ 1 + 3 * Wmass ψ 2 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, sum_chi1_seven]
    rw [sum_normSq_weight ψ hsupp (fun j => 7 - 2 * (j : ℝ))]
    norm_num
  have hK : ∑ S ∈ (Finset.univ : Finset (Fin 7)).powersetCard 2,
      ∑ x, Complex.normSq (ψ x) * zchi S x = 21 * Wmass ψ 0 + 9 * Wmass ψ 1 + Wmass ψ 2 := by
    rw [Finset.sum_comm]
    have e : ∀ x : Cfg 7, (∑ S ∈ (Finset.univ : Finset (Fin 7)).powersetCard 2, zchi S x)
        = ((7 - 2 * (wf x : ℝ)) ^ 2 - 7) / 2 := fun x => by
      have := sum_chi2_seven x; linarith
    simp_rw [← Finset.mul_sum, e]
    rw [sum_normSq_weight ψ hsupp (fun j => ((7 - 2 * (j : ℝ)) ^ 2 - 7) / 2)]
    norm_num
  have h1 := sq_zsum_le_A ψ 1
  have h2 := sq_zsum_le_A ψ 2
  rw [hZ] at h1
  rw [hK] at h2
  have c1 : (Nat.choose 7 1 : ℝ) = 7 := by norm_num [Nat.choose]
  have c2 : (Nat.choose 7 2 : ℝ) = 21 := by norm_num [Nat.choose]
  rw [c1] at h1
  rw [c2] at h2
  -- linear relations among the `A_j` and the purities
  have hV := signed_weighted_A_ball_zero ψ 2 (fun x hx => hsupp x hx) (by norm_num)
  have hA0 := A_zero ψ
  have hS := sum_A ψ
  have hT := sum_signed_A ψ
  have hτ := tau_eq_zero_of_odd (by decide : Odd 7) ψ
  rw [hτ] at hT
  rw [hn] at hA0 hS
  have p1 := Pur_eq ψ 1
  have p2 := Pur_eq ψ 2
  have p3 := Pur_eq ψ 3
  have p4 := Pur_eq ψ 4
  have p5 := Pur_eq ψ 5
  have p6 := Pur_eq ψ 6
  have q1 := Pur_compl ψ 1 (by norm_num)
  have q2 := Pur_compl ψ 2 (by norm_num)
  have q3 := Pur_compl ψ 3 (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hV hS hT p1 p2 p3 p4 p5 p6
  norm_num [Nat.choose] at hV hS hT p1 p2 p3 p4 p5 p6 q1 q2 q3 hA0
  nlinarith [mul_nonneg hW0 hW0, mul_nonneg hW0 hW1, mul_nonneg hW1 hW1]

/-- Corollary: `Pur₃ ≥ 35 · 11/49 = 55/7` for ball states (`cor:seven-hamming-ball-shadow`, the bound
`11/49` on the mean three-qubit purity). -/
theorem ball_purity_11_49_bound (ψ : Ψ 7) (hn : nsq ψ = 1) (hsupp : ∀ x, 2 < wf x → ψ x = 0) :
    11 / 49 ≤ Pur ψ 3 / 35 := by
  have := ball_purity_11_49 ψ hn hsupp
  have h0 := Wmass_nonneg ψ 0
  have h1 := Wmass_nonneg ψ 1
  linarith

end FormalResearch.FourQubitEntropy.SpinFlip
