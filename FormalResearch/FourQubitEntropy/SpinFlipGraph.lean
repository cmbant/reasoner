import FormalResearch.FourQubitEntropy.SpinFlipOmega

/-!
# Time-reversal overlap of graph states (`thm:parity-graph`, the `τ`-criterion)

Source: `ResearchNotes/QI/seven_qubit_entanglement/spinflip_graph_parity.tex`, `thm:parity-graph`
(QIprojects PR #200).

`G` is a simple graph on `n` vertices given by a symmetric loop-free Boolean adjacency function `Γ`.  The
(unnormalised) graph state is `|G⟩ = Σ_x (-1)^{Σ_{i<j} Γ_{ij} x_i x_j} |x⟩`.

* `Θ_gs`: `Θ|G⟩ = (-1)^{|E|} · Σ_x (-1)^{Σ_i (1 + deg_i) x_i} (-1)^{Σ_{i<j}Γ_{ij}x_i x_j}|x⟩`
  (`J_n|G⟩` is `Z^{1 + Γ 1}|G⟩` up to the phase `(-1)^{|E|}`);
* `tau_gs`: `τ_n(G) = |⟨G,ΘG⟩|² = ‖G‖⁴` if every vertex has odd degree and `0` otherwise; hence, normalised,
  `τ_n(G) ∈ {0,1}` and `τ_n(G) = 1` iff all degrees are odd (the all-odd-degree criterion of the theorem).

* `extG Γ` is the extension graph `H` (new vertex `0` attached to the old vertices of even degree, i.e. along
  `d = 1 + Γ1`); `omega_gs`: `Ω_G(x₀,x') = 2^{-1/2} (-1)^{|E| x₀} H(x₀,x')`, i.e. `Ω_G = H` up to the phase
  `Z^{|E|}` on the added qubit; `deg2_extG_succ`: every old vertex of `H` has odd degree;
  `deg2_extG_zero`: the new vertex has degree parity `m`.

The converse (deleting the distinguished vertex of any such graph recovers `G`: the extension is a bijection),
the counting statement `2^{C(m,2)}` and the identification of `τ_n = 1` with `Σ_{j odd} A_j = 0` for the graph
state (a combination of `tau_gs_eq_iff` with `SpinFlipPauli.tau_eq_one_iff_odd_vanish`) are *not* formalised
as separate theorems.  Claim class: **proved**.
-/

open scoped ComplexConjugate BigOperators
open FormalResearch.FrameFree.NQubit

namespace FormalResearch.FourQubitEntropy.SpinFlip

variable {n : ℕ}

/-- The sign character `ZMod 2 → ±1`. -/
def chi (a : ZMod 2) : ℂ := (![1, -1] : Fin 2 → ℂ) a

theorem chi_add (a b : ZMod 2) : chi (a + b) = chi a * chi b := by
  fin_cases a <;> fin_cases b <;> simp [chi] <;> rfl

/-- The mod-2 value of a bit. -/
def zx (a : Fin 2) : ZMod 2 := (a.val : ZMod 2)

/-- Bitwise complement. -/
def flipc (x : Cfg n) : Cfg n := fun i => 1 - x i

theorem zx_flip (a : Fin 2) : zx (1 - a) = 1 + zx a := by
  fin_cases a <;> decide

/-- Quadratic form of the graph, `Σ_{i<j} Γ_{ij} x_i x_j` in `ZMod 2`. -/
def qf (Γ : Fin n → Fin n → Bool) (x : Cfg n) : ZMod 2 :=
  ∑ i, ∑ j, if i < j ∧ Γ i j = true then zx (x i) * zx (x j) else 0

/-- Number of edges mod 2. -/
def nedge (Γ : Fin n → Fin n → Bool) : ZMod 2 :=
  ∑ i, ∑ j, if i < j ∧ Γ i j = true then 1 else 0

/-- Degree of vertex `i` mod 2. -/
def deg2 (Γ : Fin n → Fin n → Bool) (i : Fin n) : ZMod 2 := ∑ j, if Γ i j = true then 1 else 0

/-- The (unnormalised) graph state. -/
def gs (Γ : Fin n → Fin n → Bool) : Ψ n := fun x => chi (qf Γ x)

theorem chi_zero : chi 0 = 1 := rfl
theorem chi_one : chi 1 = -1 := rfl

theorem chi_mul_self (a : ZMod 2) : chi a * chi a = 1 := by
  rw [← chi_add]
  have : a + a = 0 := by fin_cases a <;> decide
  rw [this, chi_zero]

theorem conj_chi (a : ZMod 2) : conj (chi a) = chi a := by
  fin_cases a <;> simp [chi]

theorem chi_sum {ι : Type*} (s : Finset ι) (a : ι → ZMod 2) :
    chi (∑ i ∈ s, a i) = ∏ i ∈ s, chi (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [chi_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, chi_add, ih]

theorem eps_flip (a : Fin 2) : eps a (1 - a) = chi (zx a) := by
  fin_cases a <;> simp [eps, chi, zx]

theorem eps_same (a : Fin 2) : eps a a = 0 := by
  fin_cases a <;> simp [eps]

/-- `Θψ(x) = (-1)^{|x|} conj ψ(x̄)`. -/
theorem Θ_cfg (ψ : Ψ n) (x : Cfg n) :
    Θ ψ x = chi (∑ i, zx (x i)) * conj (ψ (flipc x)) := by
  classical
  unfold Θ
  have hprod : ∀ y : Cfg n, (∏ i, eps (x i) (y i)) =
      if y = flipc x then chi (∑ i, zx (x i)) else 0 := by
    intro y
    by_cases hy : y = flipc x
    · subst hy
      simp only [ite_true, chi_sum]
      exact Finset.prod_congr rfl fun i _ => eps_flip (x i)
    · simp only [hy, ite_false]
      obtain ⟨i, hi⟩ : ∃ i, y i ≠ flipc x i := by
        by_contra hcon
        exact hy (funext fun i => by_contra fun h => hcon ⟨i, h⟩)
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      have : y i = x i := by
        simp only [flipc] at hi
        revert hi; generalize y i = b; generalize x i = a
        fin_cases a <;> fin_cases b <;> simp
      rw [this]; exact eps_same _
  simp only [hprod, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- Double counting `Σ_{i<j, Γ_{ij}} (x_i + x_j) = Σ_i deg_i x_i`. -/
theorem double_count (Γ : Fin n → Fin n → Bool) (hsym : ∀ i j, Γ i j = Γ j i)
    (hirr : ∀ i, Γ i i = false) (a : Fin n → ZMod 2) :
    (∑ i, ∑ j, if i < j ∧ Γ i j = true then a i + a j else 0)
      = ∑ i, deg2 Γ i * a i := by
  have h1 : ∀ i j, (if i < j ∧ Γ i j = true then a i + a j else 0)
      = (if i < j ∧ Γ i j = true then a i else 0) + (if i < j ∧ Γ i j = true then a j else 0) := by
    intro i j; split_ifs <;> simp
  simp_rw [h1, Finset.sum_add_distrib]
  have h2 : (∑ i, ∑ j, if i < j ∧ Γ i j = true then a j else 0)
      = ∑ i, ∑ j, if j < i ∧ Γ i j = true then a i else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hsym j i]
  rw [h2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold deg2
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hij : i = j
  · subst hij; simp [hirr]
  · rcases lt_or_gt_of_ne hij with h | h
    · simp [h, not_lt.mpr h.le]
    · simp [h, not_lt.mpr h.le]

theorem qf_flip (Γ : Fin n → Fin n → Bool) (hsym : ∀ i j, Γ i j = Γ j i)
    (hirr : ∀ i, Γ i i = false) (x : Cfg n) :
    qf Γ (flipc x) = nedge Γ + ∑ i, deg2 Γ i * zx (x i) + qf Γ x := by
  have h1 : ∀ i j, (if i < j ∧ Γ i j = true then zx (flipc x i) * zx (flipc x j) else 0)
      = (if i < j ∧ Γ i j = true then (1 : ZMod 2) else 0)
        + (if i < j ∧ Γ i j = true then zx (x i) + zx (x j) else 0)
        + (if i < j ∧ Γ i j = true then zx (x i) * zx (x j) else 0) := by
    intro i j
    by_cases h : i < j ∧ Γ i j = true
    · simp only [h, and_self, ite_true, flipc, zx_flip]; ring
    · simp [h]
  unfold qf
  simp_rw [h1, Finset.sum_add_distrib]
  rw [double_count Γ hsym hirr (fun i => zx (x i))]
  rfl

/-- `J_n |G⟩ = (-1)^{|E|} Z^{1 + Γ1} |G⟩`, pointwise. -/
theorem Θ_gs (Γ : Fin n → Fin n → Bool) (hsym : ∀ i j, Γ i j = Γ j i) (hirr : ∀ i, Γ i i = false)
    (x : Cfg n) :
    Θ (gs Γ) x = chi (nedge Γ) * chi (∑ i, (1 + deg2 Γ i) * zx (x i)) * gs Γ x := by
  rw [Θ_cfg]
  unfold gs
  rw [conj_chi, qf_flip Γ hsym hirr, ← chi_add, ← chi_add, ← chi_add]
  congr 1
  simp only [add_mul, one_mul, Finset.sum_add_distrib]
  ring

theorem sum_chi_lin (c : Fin n → ZMod 2) :
    ∑ x : Cfg n, chi (∑ i, c i * zx (x i)) = ∏ i, (1 + chi (c i)) := by
  have h : ∀ x : Cfg n, chi (∑ i, c i * zx (x i)) = ∏ i, chi (c i * zx (x i)) := fun x => chi_sum _ _
  simp_rw [h]
  rw [sum_prod_pi (fun i b => chi (c i * zx b))]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [Fin.sum_univ_two, zx, chi_zero]

theorem ip_gs_Θ (Γ : Fin n → Fin n → Bool) (hsym : ∀ i j, Γ i j = Γ j i) (hirr : ∀ i, Γ i i = false) :
    ip (gs Γ) (Θ (gs Γ)) = chi (nedge Γ) * ∏ i, (1 + chi (1 + deg2 Γ i)) := by
  unfold ip
  have h : ∀ x : Cfg n, conj (gs Γ x) * Θ (gs Γ) x
      = chi (nedge Γ) * chi (∑ i, (1 + deg2 Γ i) * zx (x i)) := by
    intro x
    rw [Θ_gs Γ hsym hirr]
    unfold gs
    rw [conj_chi]
    have := chi_mul_self (qf Γ x)
    linear_combination (chi (nedge Γ) * chi (∑ i, (1 + deg2 Γ i) * zx (x i))) * this
  simp_rw [h]
  rw [← Finset.mul_sum, sum_chi_lin]

theorem deg2_eq (Γ : Fin n → Fin n → Bool) (i : Fin n) :
    deg2 Γ i = ((Finset.univ.filter fun j => Γ i j = true).card : ZMod 2) := by
  unfold deg2
  rw [Finset.card_filter]
  push_cast
  rfl

theorem chi_normSq (a : ZMod 2) : Complex.normSq (chi a) = 1 := by
  fin_cases a <;> simp [chi]

theorem nsq_gs (Γ : Fin n → Fin n → Bool) : nsq (gs Γ) = 2 ^ n := by
  unfold nsq gs
  simp [chi_normSq]

/-- **`τ_n` of a graph state**: `τ = ‖G‖⁴` if all degrees are odd, and `τ = 0` otherwise. -/
theorem tau_gs (Γ : Fin n → Fin n → Bool) (hsym : ∀ i j, Γ i j = Γ j i)
    (hirr : ∀ i, Γ i i = false) :
    tau (gs Γ) = if (∀ i, Odd (Finset.univ.filter fun j => Γ i j = true).card)
      then nsq (gs Γ) * nsq (gs Γ) else 0 := by
  unfold tau
  rw [ip_gs_Θ Γ hsym hirr, Complex.normSq_mul, chi_normSq, one_mul, nsq_gs]
  have hfac : ∀ i, (1 + chi (1 + deg2 Γ i)) =
      if Odd (Finset.univ.filter fun j => Γ i j = true).card then (2 : ℂ) else 0 := by
    intro i
    have hodd : Odd (Finset.univ.filter fun j => Γ i j = true).card ↔ deg2 Γ i = 1 := by
      rw [deg2_eq, ZMod.natCast_eq_one_iff_odd]
    by_cases h : deg2 Γ i = 1
    · have h1 : (1 + deg2 Γ i) = 0 := by rw [h]; decide
      simp only [hodd.mpr h, ite_true, h1, chi_zero]; norm_num
    · have h1 : (1 + deg2 Γ i) = 1 := by
        have : deg2 Γ i = 0 := by
          revert h; generalize deg2 Γ i = a
          fin_cases a <;> first | (intro _; rfl) | (intro h; exact absurd rfl h)
        rw [this]; simp
      have hn : ¬ Odd (Finset.univ.filter fun j => Γ i j = true).card := fun ho => h (hodd.mp ho)
      simp only [hn, ite_false, h1, chi_one]; norm_num
  simp only [hfac]
  by_cases hall : ∀ i, Odd (Finset.univ.filter fun j => Γ i j = true).card
  · simp only [hall, ite_true]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have h4 : Complex.normSq (2 : ℂ) = 4 := by simp [Complex.normSq_apply]; norm_num
    rw [map_pow, h4, ← mul_pow]
    norm_num
  · simp only [hall, ite_false]
    obtain ⟨i, hi⟩ : ∃ i, ¬ Odd (Finset.univ.filter fun j => Γ i j = true).card := by
      by_contra hcon
      exact hall fun i => by_contra fun h => hcon ⟨i, h⟩
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp only [hi, ite_false])]
    simp

/-! ### The spin-flip extension `Γ ↦ Γ_H` -/

/-- The extension graph `H`: a new vertex `0`, adjacent to the old vertex `j` iff `d_j = 1 + deg_j = 1`
(i.e. iff `deg_j` is even); old vertices are `j.succ`. -/
def extG {m : ℕ} (Γ : Fin m → Fin m → Bool) : Fin (m + 1) → Fin (m + 1) → Bool :=
  fun i j => Fin.cases (motive := fun _ => Bool)
    (Fin.cases (motive := fun _ => Bool) false (fun j' => decide (deg2 Γ j' = 0)) j)
    (fun i' => Fin.cases (motive := fun _ => Bool) (decide (deg2 Γ i' = 0)) (fun j' => Γ i' j') j) i

theorem extG_00 {m : ℕ} (Γ : Fin m → Fin m → Bool) : extG Γ 0 0 = false := by simp [extG]
theorem extG_0s {m : ℕ} (Γ : Fin m → Fin m → Bool) (j : Fin m) :
    extG Γ 0 j.succ = decide (deg2 Γ j = 0) := by simp [extG]
theorem extG_s0 {m : ℕ} (Γ : Fin m → Fin m → Bool) (i : Fin m) :
    extG Γ i.succ 0 = decide (deg2 Γ i = 0) := by simp [extG]
theorem extG_ss {m : ℕ} (Γ : Fin m → Fin m → Bool) (i j : Fin m) :
    extG Γ i.succ j.succ = Γ i j := by simp [extG]

theorem extG_symm {m : ℕ} (Γ : Fin m → Fin m → Bool) (hsym : ∀ i j, Γ i j = Γ j i) (i j : Fin (m + 1)) :
    extG Γ i j = extG Γ j i := by
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
  · rfl
  · rw [extG_0s, extG_s0]
  · rw [extG_0s, extG_s0]
  · rw [extG_ss, extG_ss, hsym]

theorem extG_irrefl {m : ℕ} (Γ : Fin m → Fin m → Bool) (hirr : ∀ i, Γ i i = false) (i : Fin (m + 1)) :
    extG Γ i i = false := by
  refine Fin.cases ?_ (fun i' => ?_) i
  · exact extG_00 Γ
  · rw [extG_ss, hirr]

theorem qf_extG {m : ℕ} (Γ : Fin m → Fin m → Bool) (x0 : Fin 2) (x' : Cfg m) :
    qf (extG Γ) (Fin.cons x0 x' : Cfg (m + 1)) =
      qf Γ x' + zx x0 * ∑ j, (1 + deg2 Γ j) * zx (x' j) := by
  have hd2 : ∀ j, (if deg2 Γ j = 0 then zx x0 * zx (x' j) else 0)
      = zx x0 * ((1 + deg2 Γ j) * zx (x' j)) := by
    intro j
    by_cases h : deg2 Γ j = 0
    · simp only [h, ite_true]; simp
    · have h1 : deg2 Γ j = 1 := by
        revert h; generalize deg2 Γ j = a
        fin_cases a <;> first | (intro h; exact absurd rfl h) | (intro _; rfl)
      have h11 : (1 + 1 : ZMod 2) = 0 := by decide
      simp only [h, ite_false, h1, h11]; simp
  have key : (∑ j, if deg2 Γ j = 0 then zx x0 * zx (x' j) else 0)
      = zx x0 * ∑ j, (1 + deg2 Γ j) * zx (x' j) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => hd2 j
  unfold qf
  simp only [Fin.sum_univ_succ, extG_00, extG_0s, extG_s0, extG_ss, Fin.cons_zero, Fin.cons_succ,
    Fin.succ_lt_succ_iff, Fin.succ_pos, not_lt_zero]
  simp only [lt_irrefl, false_and, ite_false, Finset.sum_const_zero, zero_add, decide_eq_true_eq,
    and_true, Fin.succ_ne_zero, Fin.pos_iff_ne_zero]
  simp only [true_and]
  rw [key, add_comm]

/-- **`Ω_G = H` up to a phase on the added qubit** (`thm:parity-graph`): on `|x₀, x'⟩`,
`Ω_G(x₀,x') = 2^{-1/2} (-1)^{|E| x₀} H(x₀,x')`, where `H = gs (extG Γ)`. -/
theorem omega_gs {m : ℕ} (Γ : Fin m → Fin m → Bool) (hsym : ∀ i j, Γ i j = Γ j i)
    (hirr : ∀ i, Γ i i = false) (x0 : Fin 2) (x' : Cfg m) :
    omega (gs Γ) (Fin.cons x0 x' : Cfg (m + 1)) =
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * chi (nedge Γ * zx x0) * gs (extG Γ) (Fin.cons x0 x') := by
  have hext : gs (extG Γ) (Fin.cons x0 x' : Cfg (m + 1)) =
      chi (qf Γ x' + zx x0 * ∑ j, (1 + deg2 Γ j) * zx (x' j)) := by
    unfold gs; rw [qf_extG]
  rw [hext]
  unfold omega
  simp only [Pi.smul_apply, smul_eq_mul, branch_cons]
  fin_cases x0
  · simp [zx, chi_zero, gs]
  · have h1 : zx ((1 : Fin 2)) = 1 := by decide
    simp only [Fin.isValue, Fin.mk_one, one_ne_zero, ite_false, h1, mul_one, one_mul]
    rw [Θ_gs Γ hsym hirr, chi_add]
    simp only [gs]
    ring

/-- The vertex-degree parities in `H`: every old vertex has odd degree. -/
theorem deg2_extG_succ {m : ℕ} (Γ : Fin m → Fin m → Bool) (i : Fin m) :
    deg2 (extG Γ) i.succ = 1 := by
  unfold deg2
  simp only [Fin.sum_univ_succ, extG_s0, extG_ss]
  have : (if decide (deg2 Γ i = 0) = true then (1 : ZMod 2) else 0) = 1 + deg2 Γ i := by
    generalize deg2 Γ i = a
    fin_cases a <;> decide
  rw [this]
  change 1 + deg2 Γ i + deg2 Γ i = 1
  generalize deg2 Γ i = a
  fin_cases a <;> decide

theorem sum_deg2 {m : ℕ} (Γ : Fin m → Fin m → Bool) (hsym : ∀ i j, Γ i j = Γ j i)
    (hirr : ∀ i, Γ i i = false) : ∑ i, deg2 Γ i = 0 := by
  have h := double_count Γ hsym hirr (fun _ => (1 : ZMod 2))
  have h2 : ∀ i j, (if i < j ∧ Γ i j = true then (1 : ZMod 2) + 1 else 0)
      = (if i < j ∧ Γ i j = true then (1 : ZMod 2) else 0)
        + (if i < j ∧ Γ i j = true then (1 : ZMod 2) else 0) := by
    intro i j; split_ifs <;> simp
  simp only [h2, Finset.sum_add_distrib] at h
  have h11 : ∀ a : ZMod 2, a + a = 0 := by intro a; fin_cases a <;> decide
  have e : (∑ i, ∑ j, if i < j ∧ Γ i j = true then (1 : ZMod 2) else 0) = nedge Γ := rfl
  rw [e, h11] at h
  simpa using h.symm

/-- The new vertex of `H` has degree parity `m` (`1ᵀ d = m + 1ᵀ Γ 1 ≡ m`). -/
theorem deg2_extG_zero {m : ℕ} (Γ : Fin m → Fin m → Bool) (hsym : ∀ i j, Γ i j = Γ j i)
    (hirr : ∀ i, Γ i i = false) : deg2 (extG Γ) 0 = (m : ZMod 2) := by
  unfold deg2
  simp only [Fin.sum_univ_succ, extG_00, extG_0s]
  have hd : ∀ j, (if decide (deg2 Γ j = 0) = true then (1 : ZMod 2) else 0) = 1 + deg2 Γ j := by
    intro j
    generalize deg2 Γ j = a
    fin_cases a <;> decide
  simp only [hd, Finset.sum_add_distrib, sum_deg2 Γ hsym hirr]
  simp

/-- `τ_n(G) = 1` (normalised) iff every vertex has odd degree. -/
theorem tau_gs_eq_iff (Γ : Fin n → Fin n → Bool) (hsym : ∀ i j, Γ i j = Γ j i)
    (hirr : ∀ i, Γ i i = false) :
    tau (gs Γ) = nsq (gs Γ) * nsq (gs Γ) ↔ ∀ i, Odd (Finset.univ.filter fun j => Γ i j = true).card := by
  have hpos : 0 < nsq (gs Γ) * nsq (gs Γ) := by rw [nsq_gs]; positivity
  rw [tau_gs Γ hsym hirr]
  by_cases h : ∀ i, Odd (Finset.univ.filter fun j => Γ i j = true).card
  · simp [h]
  · simp only [h, ite_false, iff_false]
    exact fun h0 => absurd h0.symm (ne_of_gt hpos)

end FormalResearch.FourQubitEntropy.SpinFlip
