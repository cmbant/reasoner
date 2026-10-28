import FormalResearch.FourQubitEntropy.SpinFlipPurity

open scoped ComplexConjugate BigOperators Matrix
open FormalResearch.FrameFree.NQubit

namespace FormalResearch.FourQubitEntropy.SpinFlip

theorem conj_ip {n : ℕ} (ψ φ : Ψ n) : conj (ip ψ φ) = ip φ ψ := by
  unfold ip; simp [map_sum, mul_comm]

/-- Adjoint of a local operator inside the inner product. -/
theorem ip_rot_adj {n : ℕ} (u : Fin n → Op1) (ψ φ : Ψ n) :
    ip (rot u ψ) φ = ip ψ (rot (fun i => (u i)ᴴ) φ) := by
  unfold ip rot
  simp only [map_sum, map_mul, map_prod, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  have : ∏ i, conj (u i (x i) (y i)) = ∏ i, (u i)ᴴ (y i) (x i) := by
    simp [Matrix.conjTranspose_apply]
  rw [this]; ring

theorem rot_smul_fam {n : ℕ} (c : Fin n → ℂ) (u : Fin n → Op1) (ψ : Ψ n) :
    rot (fun i => c i • u i) ψ = (∏ i, c i) • rot u ψ := by
  funext x
  simp only [rot, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, Finset.prod_mul_distrib,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

theorem pauliSU_adj (a : Fin 4) :
    (pauliSU a)ᴴ = (if a = 0 then (1 : ℂ) else -1) • pauliSU a := by
  fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauliSU, Matrix.conjTranspose_apply]

theorem conj_pexp {n : ℕ} (ψ : Ψ n) (a : Fin n → Fin 4) :
    conj (pexp ψ a) = (-1 : ℂ) ^ wt a * pexp ψ a := by
  unfold pexp
  rw [conj_ip, ip_rot_adj]
  have : (fun i => (pauliSU (a i))ᴴ) = fun i => (if a i = 0 then (1 : ℂ) else -1) • pauliSU (a i) := by
    funext i; exact pauliSU_adj _
  rw [this, rot_smul_fam, signprod_eq]
  simp [ip, Finset.mul_sum, mul_left_comm]

theorem pexp_Θ {n : ℕ} (ψ : Ψ n) (a : Fin n → Fin 4) : pexp (Θ ψ) a = conj (pexp ψ a) := by
  unfold pexp
  rw [← Θ_rot _ (fun i => pauliSU_su2 _), ip_Θ_Θ]


/-! ### The branch states `Ω_z` -/

theorem sum_cfg_succ {m : ℕ} (F : Cfg (m + 1) → ℂ) :
    ∑ x, F x = ∑ c : Fin 2, ∑ x' : Cfg m, F (Fin.cons c x') := by
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (m + 1) => Fin 2)) F, Fintype.sum_prod_type]
  rfl

theorem sum_word_succ {m : ℕ} {R : Type*} [AddCommMonoid R] (F : (Fin (m + 1) → Fin 4) → R) :
    ∑ a, F a = ∑ c : Fin 4, ∑ a' : Fin m → Fin 4, F (Fin.cons c a') := by
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (m + 1) => Fin 4)) F, Fintype.sum_prod_type]
  rfl

/-- Two branches on the distinguished qubit `0`. -/
def branch {m : ℕ} (f g : Ψ m) : Ψ (m + 1) := fun x => if x 0 = 0 then f (Fin.tail x) else g (Fin.tail x)

theorem branch_cons {m : ℕ} (f g : Ψ m) (c : Fin 2) (x' : Cfg m) :
    branch f g (Fin.cons c x') = if c = 0 then f x' else g x' := by
  simp [branch]

/-- `|Ω_z⟩ = (|0⟩ z + |1⟩ Θ_m z)/√2`. -/
noncomputable def omega {m : ℕ} (z : Ψ m) : Ψ (m + 1) :=
  (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • branch z (Θ z)

theorem pexp_branch {m : ℕ} (f g : Ψ m) (a' : Fin m → Fin 4) :
    pexp (branch f g) (Fin.cons 0 a') = pexp f a' + pexp g a' := by
  have h1 : (pauliSU 0 : Op1) = 1 := rfl
  unfold pexp ip rot
  simp only [sum_cfg_succ, Fin.sum_univ_two, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
    branch_cons, h1]
  simp [Matrix.one_apply]

theorem pexp_smul {n : ℕ} (c : ℂ) (ψ : Ψ n) (a : Fin n → Fin 4) :
    pexp (c • ψ) a = (conj c * c) * pexp ψ a := by
  unfold pexp ip rot
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

theorem pexp_omega {m : ℕ} (z : Ψ m) (a' : Fin m → Fin 4) :
    pexp (omega z) (Fin.cons 0 a') = (1 / 2 : ℂ) * (pexp z a' + conj (pexp z a')) := by
  unfold omega
  rw [pexp_smul, pexp_branch, pexp_Θ]
  have : conj (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = 1 / 2 := by
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul]
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    rw [show ((Real.sqrt 2)⁻¹ : ℝ) * (Real.sqrt 2)⁻¹ = 1 / 2 by
      rw [← mul_inv, h2]; norm_num]
    push_cast; ring
  simpa using congrArg (· * (pexp z a' + conj (pexp z a'))) this

/-- The Pauli weights of `Ω_z` on words that are the identity on the distinguished qubit:
only even weights survive, and they equal those of `z`. -/
theorem pw_omega {m : ℕ} (z : Ψ m) (a' : Fin m → Fin 4) :
    pw (omega z) (Fin.cons 0 a') = if Even (wt a') then pw z a' else 0 := by
  unfold pw
  rw [pexp_omega, conj_pexp]
  rcases Nat.even_or_odd (wt a') with h | h
  · simp only [h, ↓reduceIte, h.neg_one_pow]
    have : (1 / 2 : ℂ) * (pexp z a' + 1 * pexp z a') = pexp z a' := by ring
    rw [this]
  · have hn : ¬ Even (wt a') := Nat.not_even_iff_odd.mpr h
    simp only [hn, ↓reduceIte, h.neg_one_pow]
    simp


theorem wt_cons {m : ℕ} (c : Fin 4) (a' : Fin m → Fin 4) :
    wt (Fin.cons c a' : Fin (m + 1) → Fin 4) = (if c ≠ 0 then 1 else 0) + wt a' := by
  have h : ∀ {k : ℕ} (b : Fin k → Fin 4), wt b = ∑ i, if b i ≠ 0 then 1 else 0 := by
    intro k b; unfold wt; rw [Finset.card_filter]
  rw [h, h, Fin.sum_univ_succ]
  simp

/-- The Pauli weight enumerator of `Ω_z` on the original qubits (`eq:parity-Q`, coefficient form). -/
theorem B_omega {m : ℕ} (z : Ψ m) (j : ℕ) :
    B (omega z) 0 j = if Even j then A z j else 0 := by
  have hset : (wsupp (Finset.univ.erase (0 : Fin (m + 1)))).filter (fun a => wt a = j)
      = Finset.univ.filter (fun a : Fin (m + 1) → Fin 4 => a 0 = 0 ∧ wt a = j) := by
    ext a
    rw [Finset.mem_filter, Finset.mem_filter, mem_wsupp]
    have key : ∀ i : Fin (m + 1), i ∉ Finset.univ.erase (0 : Fin (m + 1)) ↔ i = 0 := by
      intro i; simp
    simp only [key, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1 0 rfl, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun i hi => by subst hi; exact h1, h2⟩
  unfold B
  rw [hset, Finset.sum_filter, sum_word_succ]
  simp only [Fin.sum_univ_four, Fin.cons_zero]
  have h1 : ((1 : Fin 4) = 0) = False := by decide
  have h2 : ((2 : Fin 4) = 0) = False := by decide
  have h3 : ((3 : Fin 4) = 0) = False := by decide
  simp only [h1, h2, h3, false_and, ite_false, Finset.sum_const_zero, add_zero, true_and,
    wt_cons, pw_omega]
  have key : ∀ x : Fin m → Fin 4, (if (if (0 : Fin 4) ≠ 0 then 1 else 0) + wt x = j then
      (if Even (wt x) then pw z x else 0) else 0)
      = if Even j then (if wt x = j then pw z x else 0) else 0 := by
    intro x
    by_cases h : wt x = j <;> simp [h]
  simp only [key]
  unfold A
  rw [Finset.sum_filter]
  split_ifs <;> simp


/-- `A_0 = ‖ψ‖⁴`. -/
theorem A_zero {n : ℕ} (ψ : Ψ n) : A ψ 0 = nsq ψ * nsq ψ := by
  have hset : (Finset.univ.filter fun a : Fin n → Fin 4 => wt a = 0) = {fun _ => 0} := by
    ext a
    simp [wt, Finset.card_eq_zero, Finset.filter_eq_empty_iff, funext_iff]
  unfold A
  rw [hset, Finset.sum_singleton]
  unfold pw pexp
  have : (fun i => pauliSU (((fun _ => 0 : Fin n → Fin 4)) i)) = fun _ => (1 : Op1) := rfl
  rw [this, rot_one, ip_self, Complex.normSq_ofReal]

/-- `eq:parity-Q`, coefficient form: the purity enumerator of subsets of the original qubits. -/
theorem purOmega {m : ℕ} (z : Ψ m) (r : ℕ) :
    (2 : ℝ) ^ r * PurU (omega z) (Finset.univ.erase 0) r =
      ∑ j ∈ Finset.range (m + 1),
        (if j ≤ r then (if Even j then (Nat.choose (m - j) (r - j) : ℝ) else 0) else 0) * A z j := by
  rw [two_pow_mul_Q, Finset.sum_range_succ]
  have hlast : (if m + 1 ≤ r then (Nat.choose (m + 1 - 1 - (m + 1)) (r - (m + 1)) : ℝ) else 0)
      * B (omega z) 0 (m + 1) = 0 := by
    rw [B_omega]
    have : A z (m + 1) = 0 := A_eq_zero_of_gt z (Nat.lt_succ_self m)
    by_cases h : Even (m + 1) <;> simp [h, this]
  rw [hlast, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [B_omega]
  by_cases hj : j ≤ r <;> by_cases he : Even j <;> simp [hj, he]

theorem balanced_m3 (z : Ψ 3) (hz : nsq z = 1) :
    Pur (omega z) 2 / 6 = 1 / 2 := by
  rw [Pur_split (omega z) 0 2 (by norm_num)]
  have hQk := purOmega z 2
  have hQn := purOmega z 2
  have hsum := sum_A z
  have hsgn := sum_signed_A z
  have hA0 := A_zero z
  have hE1 := Pur_eq z 1
  have hE2 := Pur_eq z 2
  have hC1 := Pur_compl z 1 (by norm_num)
  rw [hz] at hsum hA0
  norm_num [Finset.sum_range_succ, Nat.choose] at hQk hQn hsum hsgn hA0 hE1 hE2 hC1 ⊢
  linear_combination (1/2) * hA0 + (1/6) * hE1 + (-1/12) * hE2 + (-1/3) * hC1 + (1/24) * hQk + (1/24) * hQn

theorem balanced_m4 (z : Ψ 4) (hz : nsq z = 1) :
    Pur (omega z) 2 / 10 = 3 / 10 + (A z 1 + 4 * tau z) / 20 := by
  rw [Pur_split (omega z) 0 2 (by norm_num)]
  have hQk := purOmega z 2
  have hQn := purOmega z 3
  have hsum := sum_A z
  have hsgn := sum_signed_A z
  have hA0 := A_zero z
  have hE1 := Pur_eq z 1
  have hE2 := Pur_eq z 2
  have hE3 := Pur_eq z 3
  have hC1 := Pur_compl z 1 (by norm_num)
  rw [hz] at hsum hA0
  norm_num [Finset.sum_range_succ, Nat.choose] at hQk hQn hsum hsgn hA0 hE1 hE2 hE3 hC1 ⊢
  linear_combination (1/2) * hA0 + (-1/80) * hsum + (1/80) * hsgn + (1/10) * hE1 + (-1/40) * hE3 + (-1/5) * hC1 + (1/40) * hQk + (1/80) * hQn

theorem balanced_m5 (z : Ψ 5) (hz : nsq z = 1) :
    Pur (omega z) 3 / 20 = 1 / 8 + 3 * A z 2 / 80 := by
  rw [Pur_split (omega z) 0 3 (by norm_num)]
  have hQk := purOmega z 3
  have hQn := purOmega z 3
  have hsum := sum_A z
  have hsgn := sum_signed_A z
  have hA0 := A_zero z
  have hE1 := Pur_eq z 1
  have hE2 := Pur_eq z 2
  have hE3 := Pur_eq z 3
  have hE4 := Pur_eq z 4
  have hC1 := Pur_compl z 1 (by norm_num)
  have hC2 := Pur_compl z 2 (by norm_num)
  rw [hz] at hsum hA0
  norm_num [Finset.sum_range_succ, Nat.choose] at hQk hQn hsum hsgn hA0 hE1 hE2 hE3 hE4 hC1 hC2 ⊢
  linear_combination (1/8) * hA0 + (1/160) * hQk + (1/160) * hQn

theorem balanced_m6 (z : Ψ 6) (hz : nsq z = 1) :
    Pur (omega z) 3 / 35 = 19 / 140 + (A z 1 + 3 * A z 2 + 6 * tau z) / 140 := by
  rw [Pur_split (omega z) 0 3 (by norm_num)]
  have hQk := purOmega z 3
  have hQn := purOmega z 4
  have hsum := sum_A z
  have hsgn := sum_signed_A z
  have hA0 := A_zero z
  have hE1 := Pur_eq z 1
  have hE2 := Pur_eq z 2
  have hE3 := Pur_eq z 3
  have hE4 := Pur_eq z 4
  have hE5 := Pur_eq z 5
  have hC1 := Pur_compl z 1 (by norm_num)
  have hC2 := Pur_compl z 2 (by norm_num)
  rw [hz] at hsum hA0
  norm_num [Finset.sum_range_succ, Nat.choose] at hQk hQn hsum hsgn hA0 hE1 hE2 hE3 hE4 hE5 hC1 hC2 ⊢
  linear_combination (5/28) * hA0 + (-3/4480) * hsum + (3/4480) * hsgn + (3/140) * hE1 + (-1/280) * hE2 + (1/1120) * hE4 + (-3/2240) * hE5 + (-3/70) * hC1 + (1/70) * hC2 + (1/280) * hQk + (1/560) * hQn


/-! ### Normalisation and the symmetry `Θ Ω_z = -Ω_z` for odd `m` -/

theorem ip_branch {m : ℕ} (f g f' g' : Ψ m) :
    ip (branch f g) (branch f' g') = ip f f' + ip g g' := by
  unfold ip
  simp only [sum_cfg_succ, Fin.sum_univ_two, branch_cons]
  simp

theorem ip_smul_smul {n : ℕ} (c : ℂ) (ψ φ : Ψ n) : ip (c • ψ) (c • φ) = (conj c * c) * ip ψ φ := by
  unfold ip
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

theorem coef_sq : conj (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = 1 / 2 := by
  rw [Complex.conj_ofReal, ← Complex.ofReal_mul]
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [show ((Real.sqrt 2)⁻¹ : ℝ) * (Real.sqrt 2)⁻¹ = 1 / 2 by rw [← mul_inv, h2]; norm_num]
  push_cast; ring

/-- `‖Ω_z‖ = ‖z‖`. -/
theorem nsq_omega {m : ℕ} (z : Ψ m) : nsq (omega z) = nsq z := by
  have h : (nsq (omega z) : ℂ) = (nsq z : ℂ) := by
    rw [← ip_self, ← ip_self]
    unfold omega
    rw [ip_smul_smul, ip_branch, ip_self, ip_self, nsq_Θ, coef_sq]
    ring
  exact_mod_cast h

theorem Θ_branch {m : ℕ} (f g : Ψ m) : Θ (branch f g) = branch (Θ g) (-(Θ f)) := by
  have key : ∀ (c : Fin 2) (x' : Cfg m), Θ (branch f g) (Fin.cons c x')
      = branch (Θ g) (-(Θ f)) (Fin.cons c x') := by
    intro c x'
    rw [branch_cons]
    unfold Θ
    simp only [sum_cfg_succ, Fin.sum_univ_two, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
      branch_cons]
    fin_cases c <;> simp [eps]
  funext x
  have := key (x 0) (Fin.tail x)
  simpa [Fin.cons_self_tail] using this

theorem Θ_smul {n : ℕ} (c : ℂ) (ψ : Ψ n) : Θ (c • ψ) = conj c • Θ ψ := by
  funext x
  simp only [Θ, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

/-- For odd `m`, `Θ_{m+1} Ω_z = -Ω_z` (`J_{m+1}Ω_z = -Ω_z`). -/
theorem Θ_omega_odd {m : ℕ} (hm : Odd m) (z : Ψ m) : Θ (omega z) = -omega z := by
  unfold omega
  rw [Θ_smul, Θ_branch, Θ_Θ, hm.neg_one_pow, Complex.conj_ofReal]
  funext x
  simp [branch]
  split_ifs <;> simp

/-- For odd `m` and any `z`, `τ_{m+1}(Ω_z) = ‖z‖⁴`: the intrinsic characterisation `τ = 1`
(forward direction of `thm:parity-purification`). -/
theorem tau_omega_odd {m : ℕ} (hm : Odd m) (z : Ψ m) : tau (omega z) = nsq z * nsq z := by
  unfold tau
  rw [Θ_omega_odd hm]
  have : ip (omega z) (-omega z) = -(nsq (omega z) : ℂ) := by
    unfold ip; simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
    rw [← ip_self]; rfl
  rw [this, Complex.normSq_neg, Complex.normSq_ofReal, nsq_omega]

/-- `eq:parity-P` at coefficient level: the size-`k` purity sum of `Ω_z` is the sum of the
enumerator coefficients of `Q_z` at `k` and at `m + 1 - k`. -/
theorem Pur_omega {m : ℕ} (z : Ψ m) (k : ℕ) (hk : k ≤ m + 1) :
    Pur (omega z) k =
      (∑ j ∈ Finset.range (m + 1),
        (if j ≤ k then (if Even j then (Nat.choose (m - j) (k - j) : ℝ) else 0) else 0) * A z j) / 2 ^ k
      + (∑ j ∈ Finset.range (m + 1),
        (if j ≤ m + 1 - k then (if Even j then (Nat.choose (m - j) (m + 1 - k - j) : ℝ) else 0) else 0)
          * A z j) / 2 ^ (m + 1 - k) := by
  rw [Pur_split (omega z) 0 k hk, ← purOmega, ← purOmega]
  field_simp

/-- **Seven-qubit spin-flip gap** (`eq:seven-spinflip-gap`): for a normalised six-qubit `z`,
`Ω_z` is a unit seven-qubit state and its balanced-cut purity (average over the 35 three-qubit
subsets) is `19/140 + (A₁ + 3A₂ + 6τ₆)/140 ≥ 19/140`. -/
theorem seven_spinflip_gap (z : Ψ 6) (hz : nsq z = 1) :
    nsq (omega z) = 1 ∧
    Pur (omega z) 3 / 35 = 19 / 140 + (A z 1 + 3 * A z 2 + 6 * tau z) / 140 ∧
    19 / 140 ≤ Pur (omega z) 3 / 35 := by
  refine ⟨by rw [nsq_omega, hz], balanced_m6 z hz, ?_⟩
  rw [balanced_m6 z hz]
  have h1 := A_nonneg z 1
  have h2 := A_nonneg z 2
  have h3 := tau_nonneg z
  linarith

/-- Equality case of the seven-qubit gap: `z` is two-uniform (`A₁ = A₂ = 0`) with `τ₆(z) = 0`. -/
theorem seven_spinflip_gap_eq_iff (z : Ψ 6) (hz : nsq z = 1) :
    Pur (omega z) 3 / 35 = 19 / 140 ↔ A z 1 = 0 ∧ A z 2 = 0 ∧ tau z = 0 := by
  rw [balanced_m6 z hz]
  have h1 := A_nonneg z 1
  have h2 := A_nonneg z 2
  have h3 := tau_nonneg z
  constructor
  · intro h
    refine ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨a, b, c⟩
    rw [a, b, c]; norm_num

end FormalResearch.FourQubitEntropy.SpinFlip
