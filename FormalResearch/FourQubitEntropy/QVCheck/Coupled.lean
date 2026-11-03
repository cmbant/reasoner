module

public import QVCheckImpl.Impl5
public import FormalResearch.FourQubitEntropy.QVCheck.Coupling
public import FormalResearch.FourQubitEntropy.QVCheck.Intertwiner

/-!
# The coupled contraction (K3, K4)

For a sector `p = (A, B)` and a pair of letters, the contraction `⟨W, (⊗_q Q_q) V⟩` is reshaped into the pair form `S4`,
and `S4` is transformed by the coupling matrices `T`, `Tinv` into the sparse family `Ŵ_u`, `V̂_u`.  The result is
`pair_identity`, the semantics of `ctPair`/`ctil` for one pair of letters in a sector.
-/

@[expose] public section


open Finset FormalResearch.FourQubitEntropy FormalResearch.FourQubitEntropy.QVBlock
open scoped Matrix

namespace QVCheck

/-!
## Reshaping a four-qubit contraction into the pair form `S4`

For a sector `p` with radices `m q`, `DA = m 0 * m 1`, `DB = m 2 * m 3`:
`∑_{x,y} w(flat x) (⊗_q Q_q)(x,y) v(flat y) = S4 W P V R`, where `W_{ij} = w(i DB + j)`, `V_{kl} = v(k DB + l)`,
`P_{ik} = Q_0(i/m1, k/m1) Q_1(i%m1, k%m1)`, `R_{jl} = Q_2(j/m3, l/m3) Q_3(j%m3, l%m3)`.
-/

/-- a function `ℕ × ℕ → ℤ` as a matrix -/
def nm (D1 D2 : ℕ) (f : ℕ → ℕ → ℤ) : Matrix (Fin D1) (Fin D2) ℤ := Matrix.of fun i j => f i.val j.val

/-- entry of a matrix at natural indices (zero outside) -/
def qe {m : ℕ} (Q : Matrix (Fin m) (Fin m) ℤ) (a b : ℕ) : ℤ := if h : a < m ∧ b < m then Q ⟨a, h.1⟩ ⟨b, h.2⟩ else 0

theorem S4_nat (DA DB : ℕ) (f g h r : ℕ → ℕ → ℤ) :
    S4 (nm DA DB f) (nm DA DA g) (nm DA DB h) (nm DB DB r) =
      ∑ i ∈ range DA, ∑ j ∈ range DB, ∑ k ∈ range DA, ∑ l ∈ range DB, f i j * g i k * h k l * r j l := by
  unfold S4
  simp only [nm, Matrix.of_apply]
  rw [← Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ range DB, ∑ k ∈ range DA, ∑ l ∈ range DB, f i j * g i k * h k l * r j l)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun j => ∑ k ∈ range DA, ∑ l ∈ range DB, f i j * g i k * h k l * r j l)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun k => ∑ l ∈ range DB, f i j * g i k * h k l * r j l)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun l => f i j * g i k * h k l * r j l)]

theorem sum_range_mul_eq (g : ℕ → ℤ) (m n : ℕ) :
    ∑ i ∈ range (m * n), g i = ∑ a ∈ range m, ∑ b ∈ range n, g (a * n + b) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

theorem sum_ix4 (m : Fin 4 → ℕ) (g : (∀ q : Fin 4, Fin (m q)) → ℤ) :
    ∑ x : (∀ q : Fin 4, Fin (m q)), g x =
      ∑ a ∈ range (m 0), ∑ b ∈ range (m 1), ∑ c ∈ range (m 2), ∑ d ∈ range (m 3),
        (if h : a < m 0 ∧ b < m 1 ∧ c < m 2 ∧ d < m 3 then
          g ((ixEquiv m).symm (⟨a, h.1⟩, ⟨b, h.2.1⟩, ⟨c, h.2.2.1⟩, ⟨d, h.2.2.2⟩)) else 0) := by
  rw [← (ixEquiv m).symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  simp only [Finset.sum_range]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun d _ => ?_
  rw [dite_eq_left ⟨a.2, b.2, c.2, d.2⟩]

theorem flatIx_eq (m : Fin 4 → ℕ) (x : ∀ q : Fin 4, Fin (m q)) :
    flatIx m x = ((x 0).val * m 1 + (x 1).val) * (m 2 * m 3) + ((x 2).val * m 3 + (x 3).val) := by
  unfold flatIx flat4; ring

theorem div_mod_aux (a b n : ℕ) (hb : b < n) : (a * n + b) / n = a ∧ (a * n + b) % n = b := by
  have hn : 0 < n := by omega
  constructor
  · rw [Nat.mul_comm, Nat.mul_add_div hn, Nat.div_eq_of_lt hb]; simp
  · rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hb]

theorem contr_eq_S4 (m : Fin 4 → ℕ) (Q : ∀ q, Matrix (Fin (m q)) (Fin (m q)) ℤ) (wv vv : ℕ → ℤ) :
    ∑ x : (∀ q : Fin 4, Fin (m q)), ∑ y : (∀ q : Fin 4, Fin (m q)),
        wv (flatIx m x) * kronPi Q x y * vv (flatIx m y) =
      S4 (nm (m 0 * m 1) (m 2 * m 3) fun i j => wv (i * (m 2 * m 3) + j))
        (nm (m 0 * m 1) (m 0 * m 1) fun i k => qe (Q 0) (i / m 1) (k / m 1) * qe (Q 1) (i % m 1) (k % m 1))
        (nm (m 0 * m 1) (m 2 * m 3) fun k l => vv (k * (m 2 * m 3) + l))
        (nm (m 2 * m 3) (m 2 * m 3) fun j l => qe (Q 2) (j / m 3) (l / m 3) * qe (Q 3) (j % m 3) (l % m 3)) := by
  rw [S4_nat]
  simp only [sum_range_mul_eq _ (m 0) (m 1), sum_range_mul_eq _ (m 2) (m 3)]
  simp only [sum_ix4 m]
  refine Finset.sum_congr rfl fun a0 h0 => Finset.sum_congr rfl fun a1 h1 =>
    Finset.sum_congr rfl fun a2 h2 => Finset.sum_congr rfl fun a3 h3 => ?_
  have h0' := Finset.mem_range.1 h0; have h1' := Finset.mem_range.1 h1
  have h2' := Finset.mem_range.1 h2; have h3' := Finset.mem_range.1 h3
  rw [dite_eq_left ⟨h0', h1', h2', h3'⟩]
  refine Finset.sum_congr rfl fun b0 hb0 => Finset.sum_congr rfl fun b1 hb1 =>
    Finset.sum_congr rfl fun b2 hb2 => Finset.sum_congr rfl fun b3 hb3 => ?_
  have hb0' := Finset.mem_range.1 hb0; have hb1' := Finset.mem_range.1 hb1
  have hb2' := Finset.mem_range.1 hb2; have hb3' := Finset.mem_range.1 hb3
  rw [dite_eq_left ⟨hb0', hb1', hb2', hb3'⟩]
  obtain ⟨d0, e0⟩ := div_mod_aux a0 a1 (m 1) h1'
  obtain ⟨d1, e1⟩ := div_mod_aux b0 b1 (m 1) hb1'
  obtain ⟨d2, e2⟩ := div_mod_aux a2 a3 (m 3) h3'
  obtain ⟨d3, e3⟩ := div_mod_aux b2 b3 (m 3) hb3'
  rw [d0, e0, d1, e1, d2, e2, d3, e3]
  have hq : ∀ (q : Fin 4) (a b : ℕ) (ha : a < m q) (hb : b < m q), qe (Q q) a b = Q q ⟨a, ha⟩ ⟨b, hb⟩ := by
    intro q a b ha hb; unfold qe; rw [dite_eq_left ⟨ha, hb⟩]
  rw [hq 0 a0 b0 h0' hb0', hq 1 a1 b1 h1' hb1', hq 2 a2 b2 h2' hb2', hq 3 a3 b3 h3' hb3']
  have hk : kronPi Q ((ixEquiv m).symm (⟨a0, h0'⟩, ⟨a1, h1'⟩, ⟨a2, h2'⟩, ⟨a3, h3'⟩))
      ((ixEquiv m).symm (⟨b0, hb0'⟩, ⟨b1, hb1'⟩, ⟨b2, hb2'⟩, ⟨b3, hb3'⟩)) =
      Q 0 ⟨a0, h0'⟩ ⟨b0, hb0'⟩ * Q 1 ⟨a1, h1'⟩ ⟨b1, hb1'⟩ * Q 2 ⟨a2, h2'⟩ ⟨b2, hb2'⟩ * Q 3 ⟨a3, h3'⟩ ⟨b3, hb3'⟩ := by
    rw [kronPi_apply, Fin.prod_univ_four]; rfl
  rw [hk, flatIx_eq, flatIx_eq]
  show wv ((a0 * m 1 + a1) * (m 2 * m 3) + (a2 * m 3 + a3)) * _ * vv ((b0 * m 1 + b1) * (m 2 * m 3) + (b2 * m 3 + b3)) = _
  ring

/-!
## The coupled contraction of one pair of letters (K4 core)
-/

theorem nm_hat (DA DB d : ℕ) (iA jB : ℕ → ℕ) (hi : ∀ x < d, iA x < DA) (hj : ∀ x < d, jB x < DB) (c : ℕ → ℤ) :
    nm DA DB (fun i j => ∑ x ∈ range d, if i = iA x ∧ j = jB x then c x else 0) =
      ∑ x : Fin d, c x.val • (Matrix.single (⟨iA x.val, hi x.val x.2⟩ : Fin DA) (⟨jB x.val, hj x.val x.2⟩ : Fin DB) (1 : ℤ)) := by
  refine Matrix.ext fun i j => ?_
  simp only [nm, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
  rw [← Fin.sum_univ_eq_sum_range (fun x => if i.val = iA x ∧ j.val = jB x then c x else 0) d]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : i.val = iA x.val ∧ j.val = jB x.val
  · have h' : (⟨iA x.val, hi x.val x.2⟩ : Fin DA) = i ∧ (⟨jB x.val, hj x.val x.2⟩ : Fin DB) = j :=
      ⟨Fin.ext h.1.symm, Fin.ext h.2.symm⟩
    rw [ite_eq_left h, ite_eq_left h', mul_one]
  · have h' : ¬((⟨iA x.val, hi x.val x.2⟩ : Fin DA) = i ∧ (⟨jB x.val, hj x.val x.2⟩ : Fin DB) = j) :=
      fun hh => h ⟨(congrArg Fin.val hh.1).symm, (congrArg Fin.val hh.2).symm⟩
    rw [ite_eq_right h, ite_eq_right h', mul_zero]

theorem S4_hat (DA DB d d' : ℕ) (iA jB kA lB : ℕ → ℕ) (hi : ∀ x < d, iA x < DA) (hj : ∀ x < d, jB x < DB)
    (hk : ∀ y < d', kA y < DA) (hl : ∀ y < d', lB y < DB) (c c' : ℕ → ℤ)
    (P : Matrix (Fin DA) (Fin DA) ℤ) (R' : Matrix (Fin DB) (Fin DB) ℤ) :
    S4 (nm DA DB fun i j => ∑ x ∈ range d, if i = iA x ∧ j = jB x then c x else 0) P
      (nm DA DB fun k l => ∑ y ∈ range d', if k = kA y ∧ l = lB y then c' y else 0) R' =
      ∑ x ∈ range d, ∑ y ∈ range d', c x * c' y * qe P (iA x) (kA y) * qe R' (jB x) (lB y) := by
  rw [nm_hat DA DB d iA jB hi hj c, nm_hat DA DB d' kA lB hk hl c']
  rw [S4_sum_left]
  rw [← Fin.sum_univ_eq_sum_range (fun x => ∑ y ∈ range d', c x * c' y * qe P (iA x) (kA y) * qe R' (jB x) (lB y)) d]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [S4_smul_left, S4_sum_right]
  rw [← Fin.sum_univ_eq_sum_range (fun y => c x.val * c' y * qe P (iA x.val) (kA y) * qe R' (jB x.val) (lB y)) d',
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [S4_smul_right, S4_single]
  have e1 : qe P (iA x.val) (kA y.val) = P ⟨iA x.val, hi x.val x.2⟩ ⟨kA y.val, hk y.val y.2⟩ := by
    unfold qe; rw [dite_eq_left ⟨hi x.val x.2, hk y.val y.2⟩]
  have e2 : qe R' (jB x.val) (lB y.val) = R' ⟨jB x.val, hj x.val x.2⟩ ⟨lB y.val, hl y.val y.2⟩ := by
    unfold qe; rw [dite_eq_left ⟨hj x.val x.2, hl y.val y.2⟩]
  rw [e1, e2]; ring

/-!
## Entries of the tables `Π[l] = T (Q0 ⊗ Q1) Tinv` (`tableLetter`)
-/

/-- the `D × D` Kronecker matrix `Q0 ⊗ Q1` of a letter, at natural indices -/
def pairKron (ai sp0 sp1 pj : ℕ) (l : Letter) (e e' : ℕ) : ℤ :=
  psiAt ai sp0 (pj / 4) l.1 l.2.1 (e / mult (pj % 4)) (e' / mult (pj % 4)) *
    psiAt ai sp1 (pj % 4) l.2.2.1 l.2.2.2 (e % mult (pj % 4)) (e' % mult (pj % 4))

theorem tlQ0_apply (ai sp0 pj : ℕ) (l : Letter) (a b : ℕ) (ha : a < mult (pj / 4)) (hb : b < mult (pj / 4)) :
    gt (tlQ0 ai sp0 pj l) (a * mult (pj / 4) + b) = psiAt ai sp0 (pj / 4) l.1 l.2.1 a b := by
  unfold tlQ0
  have hlt : a * mult (pj / 4) + b < mult (pj / 4) * mult (pj / 4) := by nlinarith
  rw [gt_tab, ite_eq_left hlt]
  obtain ⟨e1, e2⟩ := div_mod_aux a b (mult (pj / 4)) hb
  rw [e1, e2]

theorem tlQ1_apply (ai sp1 pj : ℕ) (l : Letter) (a b : ℕ) (ha : a < mult (pj % 4)) (hb : b < mult (pj % 4)) :
    gt (tlQ1 ai sp1 pj l) (a * mult (pj % 4) + b) = psiAt ai sp1 (pj % 4) l.2.2.1 l.2.2.2 a b := by
  unfold tlQ1
  have hlt : a * mult (pj % 4) + b < mult (pj % 4) * mult (pj % 4) := by nlinarith
  rw [gt_tab, ite_eq_left hlt]
  obtain ⟨e1, e2⟩ := div_mod_aux a b (mult (pj % 4)) hb
  rw [e1, e2]

theorem tlS_apply (ai sp1 pj : ℕ) (l : Letter) (k0 i1 c : ℕ) (hk0 : k0 < mult (pj / 4)) (hi1 : i1 < mult (pj % 4))
    (hc : c < mult (pj / 4) * mult (pj % 4)) :
    gt (tlS ai sp1 pj l) ((k0 * mult (pj % 4) + i1) * (mult (pj / 4) * mult (pj % 4)) + c) =
      ∑ k1 ∈ range (mult (pj % 4)), psiAt ai sp1 (pj % 4) l.2.2.1 l.2.2.2 i1 k1 * tiAt pj (k0 * mult (pj % 4) + k1) c := by
  unfold tlS
  dsimp only
  have hlt : (k0 * mult (pj % 4) + i1) * (mult (pj / 4) * mult (pj % 4)) + c <
      mult (pj / 4) * mult (pj % 4) * (mult (pj / 4) * mult (pj % 4)) := by
    have : k0 * mult (pj % 4) + i1 < mult (pj / 4) * mult (pj % 4) := by nlinarith
    nlinarith
  rw [gt_tab, ite_eq_left hlt, sumTo_eq]
  obtain ⟨d1, d2⟩ := div_mod_aux (k0 * mult (pj % 4) + i1) c (mult (pj / 4) * mult (pj % 4)) hc
  obtain ⟨f1, f2⟩ := div_mod_aux k0 i1 (mult (pj % 4)) hi1
  simp only [d1, d2, f1, f2]
  refine Finset.sum_congr rfl fun k1 hk1 => ?_
  have hk1' := Finset.mem_range.1 hk1
  rw [tlQ1_apply ai sp1 pj l i1 k1 hi1 hk1']

theorem tlM1_apply (ai sp0 sp1 pj : ℕ) (l : Letter) (k c : ℕ) (hk : k < mult (pj / 4) * mult (pj % 4))
    (hc : c < mult (pj / 4) * mult (pj % 4)) :
    gt (tlM1 ai sp0 sp1 pj l) (k * (mult (pj / 4) * mult (pj % 4)) + c) =
      ∑ k0 ∈ range (mult (pj / 4)), psiAt ai sp0 (pj / 4) l.1 l.2.1 (k / mult (pj % 4)) k0 *
        ∑ k1 ∈ range (mult (pj % 4)), psiAt ai sp1 (pj % 4) l.2.2.1 l.2.2.2 (k % mult (pj % 4)) k1 *
          tiAt pj (k0 * mult (pj % 4) + k1) c := by
  unfold tlM1
  dsimp only
  have hlt : k * (mult (pj / 4) * mult (pj % 4)) + c < mult (pj / 4) * mult (pj % 4) * (mult (pj / 4) * mult (pj % 4)) := by
    nlinarith
  rw [gt_tab, ite_eq_left hlt, sumTo_eq]
  obtain ⟨d1, d2⟩ := div_mod_aux k c (mult (pj / 4) * mult (pj % 4)) hc
  simp only [d1, d2]
  have hm1 : 0 < mult (pj % 4) := by
    rcases Nat.eq_zero_or_pos (mult (pj % 4)) with h | h
    · rw [h] at hk; omega
    · exact h
  have hk1 : k % mult (pj % 4) < mult (pj % 4) := Nat.mod_lt _ hm1
  have hk2 : k / mult (pj % 4) < mult (pj / 4) := Nat.div_lt_of_lt_mul (by nlinarith)
  refine Finset.sum_congr rfl fun k0 hk0 => ?_
  have hk0' := Finset.mem_range.1 hk0
  rw [tlQ0_apply ai sp0 pj l _ k0 hk2 hk0', tlS_apply ai sp1 pj l k0 _ c hk0' hk1 hc]

theorem tableLetter_apply (ai sp0 sp1 pj : ℕ) (l : Letter) (row col : ℕ) (hr : row < mult (pj / 4) * mult (pj % 4))
    (hc : col < mult (pj / 4) * mult (pj % 4)) :
    gt (tableLetter ai sp0 sp1 pj l) (row * (mult (pj / 4) * mult (pj % 4)) + col) =
      ∑ e ∈ range (mult (pj / 4) * mult (pj % 4)), ∑ e' ∈ range (mult (pj / 4) * mult (pj % 4)),
        tAt pj row e * pairKron ai sp0 sp1 pj l e e' * tiAt pj e' col := by
  unfold tableLetter
  dsimp only
  have hlt : row * (mult (pj / 4) * mult (pj % 4)) + col < mult (pj / 4) * mult (pj % 4) * (mult (pj / 4) * mult (pj % 4)) := by
    nlinarith
  rw [gt_tab, ite_eq_left hlt, sumTo_eq]
  obtain ⟨d1, d2⟩ := div_mod_aux row col (mult (pj / 4) * mult (pj % 4)) hc
  simp only [d1, d2]
  refine Finset.sum_congr rfl fun e he => ?_
  have he' := Finset.mem_range.1 he
  rw [tlM1_apply ai sp0 sp1 pj l e col he' hc]
  rw [sum_range_mul_eq _ (mult (pj / 4)) (mult (pj % 4))]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k0 hk0 => ?_
  refine Finset.sum_congr rfl fun k1 hk1 => ?_
  have hk1' := Finset.mem_range.1 hk1
  unfold pairKron
  obtain ⟨q1, q2⟩ := div_mod_aux k0 k1 (mult (pj % 4)) hk1'
  rw [q1, q2]
  ring

/-!
## Matrix identities for the coupled data (K3, K4)
-/

theorem mul_nm (D1 D2 D3 : ℕ) (f g : ℕ → ℕ → ℤ) :
    nm D1 D2 f * nm D2 D3 g = nm D1 D3 (fun i k => ∑ e ∈ range D2, f i e * g e k) := by
  refine Matrix.ext fun i k => ?_
  simp only [nm, Matrix.mul_apply, Matrix.of_apply]
  rw [← Fin.sum_univ_eq_sum_range (fun e => f i e * g e k) D2]

theorem transpose_nm (D1 D2 : ℕ) (f : ℕ → ℕ → ℤ) : (nm D1 D2 f)ᵀ = nm D2 D1 (fun a b => f b a) := by
  refine Matrix.ext fun i k => ?_
  simp [nm]

theorem nm_apply (D1 D2 : ℕ) (f : ℕ → ℕ → ℤ) (i : Fin D1) (j : Fin D2) : nm D1 D2 f i j = f i.val j.val := rfl

theorem nm_congr (D1 D2 : ℕ) (f g : ℕ → ℕ → ℤ) (h : ∀ i < D1, ∀ j < D2, f i j = g i j) : nm D1 D2 f = nm D1 D2 g := by
  refine Matrix.ext fun i j => ?_
  exact h i.val i.2 j.val j.2

/-- `T_A P T_inv` as an `nm` matrix -/
theorem tri_nm (DA : ℕ) (t g ti : ℕ → ℕ → ℤ) :
    nm DA DA t * nm DA DA g * nm DA DA ti =
      nm DA DA (fun i k => ∑ e ∈ range DA, ∑ e' ∈ range DA, t i e * g e e' * ti e' k) := by
  rw [mul_nm, mul_nm]
  refine nm_congr _ _ _ _ fun i _ k _ => ?_
  simp only [Finset.sum_mul]
  exact Finset.sum_comm

theorem checkT_spec (h : checkT () = true) (pj : ℕ) (hpj : pj < 16) :
    delta pj ≠ 0 ∧ ∀ i j : ℕ, i < pairDim pj → j < pairDim pj →
      ∑ k ∈ range (pairDim pj), tiAt pj i k * tAt pj k j = if i = j then delta pj else 0 := by
  unfold checkT at h
  have h1 := (allTo_iff _ _).1 h pj (by rw [hide_eq]; exact hpj)
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h1
  refine ⟨h1.1, fun i j hi hj => ?_⟩
  have h2 := (allTo_iff _ _).1 h1.2 i hi
  have h3 := (allTo_iff _ _).1 h2 j hj
  simp only [Bool.and_eq_true, beq_iff_eq, sumTo_eq] at h3
  rw [h3.2]

theorem coupledW_entry (code b i j : ℕ) (hi : i < pairDim (pA code)) (hj : j < pairDim (pB code)) :
    gt (coupledW code b) (i * pairDim (pB code) + j) =
      ∑ l ∈ range (pairDim (pB code)), (∑ k ∈ range (pairDim (pA code)),
        tiAt (pA code) k i * wAt code b (k * pairDim (pB code) + l)) * tiAt (pB code) l j := by
  unfold coupledW
  have hlt : i * pairDim (pB code) + j < pairDim (pA code) * pairDim (pB code) := by nlinarith
  rw [gt_tab, ite_eq_left hlt, sumTo_eq]
  obtain ⟨d1, d2⟩ := div_mod_aux i j (pairDim (pB code)) hj
  simp only [d1, d2]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' := Finset.mem_range.1 hl
  have hlt' : i * pairDim (pB code) + l < pairDim (pA code) * pairDim (pB code) := by nlinarith
  obtain ⟨e1, e2⟩ := div_mod_aux i l (pairDim (pB code)) hl'
  rw [gt_tab, ite_eq_left hlt', sumTo_eq]
  simp only [e1, e2]

theorem coupledV_entry (code b i j : ℕ) (hi : i < pairDim (pA code)) (hj : j < pairDim (pB code)) :
    gt (coupledV code b) (i * pairDim (pB code) + j) =
      ∑ l ∈ range (pairDim (pB code)), (∑ k ∈ range (pairDim (pA code)),
        tAt (pA code) i k * vAt code b (k * pairDim (pB code) + l)) * tAt (pB code) j l := by
  unfold coupledV
  have hlt : i * pairDim (pB code) + j < pairDim (pA code) * pairDim (pB code) := by nlinarith
  rw [gt_tab, ite_eq_left hlt, sumTo_eq]
  obtain ⟨d1, d2⟩ := div_mod_aux i j (pairDim (pB code)) hj
  simp only [d1, d2]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' := Finset.mem_range.1 hl
  have hlt' : i * pairDim (pB code) + l < pairDim (pA code) * pairDim (pB code) := by nlinarith
  obtain ⟨e1, e2⟩ := div_mod_aux i l (pairDim (pB code)) hl'
  rw [gt_tab, ite_eq_left hlt', sumTo_eq]
  simp only [e1, e2]

/-!
## The generic coupled identity for one pair of letters (K4)
-/

theorem coupled_generic (DA DB n : ℕ) (tA tiA tB tiB w v P R : ℕ → ℕ → ℤ) (dA dB Lc : ℤ)
    (Om Xi : ℕ → ℤ) (dU : ℕ → ℕ) (iA jB : ℕ → ℕ → ℕ) (wcf vcf : ℕ → ℕ → ℤ)
    (hA2 : ∀ i < DA, ∀ j < DA, ∑ k ∈ range DA, tiA i k * tA k j = if i = j then dA else 0)
    (hB2 : ∀ i < DB, ∀ j < DB, ∑ k ∈ range DB, tiB i k * tB k j = if i = j then dB else 0)
    (hbd : ∀ u < n, ∀ x < dU u, iA u x < DA ∧ jB u x < DB)
    (hW : ∀ i < DA, ∀ j < DB, Lc * (∑ l ∈ range DB, (∑ k ∈ range DA, tiA k i * w k l) * tiB l j) =
      ∑ u ∈ range n, Om u * ∑ x ∈ range (dU u), if i = iA u x ∧ j = jB u x then wcf u x else 0)
    (hV : ∀ i < DA, ∀ j < DB, Lc * (∑ l ∈ range DB, (∑ k ∈ range DA, tA i k * v k l) * tB j l) =
      ∑ u ∈ range n, Xi u * ∑ x ∈ range (dU u), if i = iA u x ∧ j = jB u x then vcf u x else 0) :
    dA ^ 2 * dB ^ 2 * Lc ^ 2 * S4 (nm DA DB w) (nm DA DA P) (nm DA DB v) (nm DB DB R) =
      ∑ u ∈ range n, ∑ u' ∈ range n, Om u * Xi u' * ∑ x ∈ range (dU u), ∑ y ∈ range (dU u'),
        wcf u x * vcf u' y *
          (∑ e ∈ range DA, ∑ e' ∈ range DA, tA (iA u x) e * P e e' * tiA e' (iA u' y)) *
          (∑ e ∈ range DB, ∑ e' ∈ range DB, tB (jB u x) e * R e e' * tiB e' (jB u' y)) := by
  have hA2m : nm DA DA tiA * nm DA DA tA = dA • (1 : Matrix (Fin DA) (Fin DA) ℤ) := by
    rw [mul_nm]
    refine Matrix.ext fun i j => ?_
    rw [nm_apply, hA2 i.val i.2 j.val j.2]
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij; simp
    · have : i.val ≠ j.val := fun e => hij (Fin.ext e)
      simp [hij, this]
  have hB2m : nm DB DB tiB * nm DB DB tB = dB • (1 : Matrix (Fin DB) (Fin DB) ℤ) := by
    rw [mul_nm]
    refine Matrix.ext fun i j => ?_
    rw [nm_apply, hB2 i.val i.2 j.val j.2]
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij; simp
    · have : i.val ≠ j.val := fun e => hij (Fin.ext e)
      simp [hij, this]
  have h1 := S4_coupled (nm DA DB w) (nm DA DA P) (nm DA DB v) (nm DB DB R) (nm DA DA tA) (nm DA DA tiA)
    (nm DB DB tB) (nm DB DB tiB) dA dB hA2m hB2m
  have eP : nm DA DA tA * nm DA DA P * nm DA DA tiA =
      nm DA DA (fun i k => ∑ e ∈ range DA, ∑ e' ∈ range DA, tA i e * P e e' * tiA e' k) := tri_nm DA tA P tiA
  have eR : nm DB DB tB * nm DB DB R * nm DB DB tiB =
      nm DB DB (fun i k => ∑ e ∈ range DB, ∑ e' ∈ range DB, tB i e * R e e' * tiB e' k) := tri_nm DB tB R tiB
  have eW : (nm DA DA tiA)ᵀ * nm DA DB w * nm DB DB tiB =
      nm DA DB (fun i j => ∑ l ∈ range DB, (∑ k ∈ range DA, tiA k i * w k l) * tiB l j) := by
    rw [transpose_nm, mul_nm, mul_nm]
  have eV : nm DA DA tA * nm DA DB v * (nm DB DB tB)ᵀ =
      nm DA DB (fun i j => ∑ l ∈ range DB, (∑ k ∈ range DA, tA i k * v k l) * tB j l) := by
    rw [transpose_nm, mul_nm, mul_nm]
  rw [eP, eR, eW, eV] at h1
  set Wc : ℕ → ℕ → ℤ := fun i j => ∑ l ∈ range DB, (∑ k ∈ range DA, tiA k i * w k l) * tiB l j with hWc
  set Vc : ℕ → ℕ → ℤ := fun i j => ∑ l ∈ range DB, (∑ k ∈ range DA, tA i k * v k l) * tB j l with hVc
  set Pt : ℕ → ℕ → ℤ := fun i k => ∑ e ∈ range DA, ∑ e' ∈ range DA, tA i e * P e e' * tiA e' k with hPt
  set Rt : ℕ → ℕ → ℤ := fun i k => ∑ e ∈ range DB, ∑ e' ∈ range DB, tB i e * R e e' * tiB e' k with hRt
  have hWm : Lc • nm DA DB Wc = ∑ u ∈ range n, Om u • nm DA DB (fun i j =>
      ∑ x ∈ range (dU u), if i = iA u x ∧ j = jB u x then wcf u x else 0) := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.smul_apply, nm_apply, Matrix.sum_apply, smul_eq_mul]
    exact hW i.val i.2 j.val j.2
  have hVm : Lc • nm DA DB Vc = ∑ u ∈ range n, Xi u • nm DA DB (fun i j =>
      ∑ x ∈ range (dU u), if i = iA u x ∧ j = jB u x then vcf u x else 0) := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.smul_apply, nm_apply, Matrix.sum_apply, smul_eq_mul]
    exact hV i.val i.2 j.val j.2
  have key : Lc ^ 2 * S4 (nm DA DB Wc) (nm DA DA Pt) (nm DA DB Vc) (nm DB DB Rt) =
      S4 (Lc • nm DA DB Wc) (nm DA DA Pt) (Lc • nm DA DB Vc) (nm DB DB Rt) := by
    rw [S4_smul_left, S4_smul_right]; ring
  have qe_nm : ∀ (D : ℕ) (f : ℕ → ℕ → ℤ) (i k : ℕ), i < D → k < D → qe (nm D D f) i k = f i k := by
    intro D f i k hi hk; unfold qe; rw [dite_eq_left ⟨hi, hk⟩]; rfl
  calc dA ^ 2 * dB ^ 2 * Lc ^ 2 * S4 (nm DA DB w) (nm DA DA P) (nm DA DB v) (nm DB DB R)
      = Lc ^ 2 * (dA ^ 2 * dB ^ 2 * S4 (nm DA DB w) (nm DA DA P) (nm DA DB v) (nm DB DB R)) := by ring
    _ = Lc ^ 2 * S4 (nm DA DB Wc) (nm DA DA Pt) (nm DA DB Vc) (nm DB DB Rt) := by rw [h1]
    _ = S4 (Lc • nm DA DB Wc) (nm DA DA Pt) (Lc • nm DA DB Vc) (nm DB DB Rt) := key
    _ = _ := by
      rw [hWm, hVm, S4_sum_left]
      refine Finset.sum_congr rfl fun u hu => ?_
      rw [S4_smul_left, S4_sum_right, Finset.mul_sum]
      refine Finset.sum_congr rfl fun u' hu' => ?_
      rw [S4_smul_right]
      have hu1 := Finset.mem_range.1 hu
      have hu2 := Finset.mem_range.1 hu'
      rw [S4_hat DA DB (dU u) (dU u') (iA u) (jB u) (iA u') (jB u')
        (fun x hx => (hbd u hu1 x hx).1) (fun x hx => (hbd u hu1 x hx).2)
        (fun x hx => (hbd u' hu2 x hx).1) (fun x hx => (hbd u' hu2 x hx).2) (wcf u) (vcf u')]
      rw [mul_assoc]
      refine congrArg (fun z => Om u * (Xi u' * z)) ?_
      refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
      have hx' := Finset.mem_range.1 hx
      have hy' := Finset.mem_range.1 hy
      rw [qe_nm DA Pt _ _ (hbd u hu1 x hx').1 (hbd u' hu2 y hy').1,
        qe_nm DB Rt _ _ (hbd u hu1 x hx').2 (hbd u' hu2 y hy').2]

/-!
## Specifications extracted from the structural checks (K3, `checkU`) and the sector arithmetic
-/

theorem pA_pcode (p : Fin 4 → Spin) : pA (pcode p) = (p 0).val * 4 + (p 1).val := by
  have h0 : spinDigit (pcode p) 0 = (p 0).val := spinDigit_pcode p 0
  have h1 : spinDigit (pcode p) 1 = (p 1).val := spinDigit_pcode p 1
  unfold pA pairIdx; rw [h0, h1]

theorem pB_pcode (p : Fin 4 → Spin) : pB (pcode p) = (p 2).val * 4 + (p 3).val := by
  have h0 : spinDigit (pcode p) 2 = (p 2).val := spinDigit_pcode p 2
  have h1 : spinDigit (pcode p) 3 = (p 3).val := spinDigit_pcode p 3
  unfold pB pairIdx; rw [h0, h1]

theorem pA_div (p : Fin 4 → Spin) : pA (pcode p) / 4 = (p 0).val := by
  rw [pA_pcode]; have := (p 1).2; omega

theorem pA_mod (p : Fin 4 → Spin) : pA (pcode p) % 4 = (p 1).val := by
  rw [pA_pcode]; have := (p 1).2; omega

theorem pB_div (p : Fin 4 → Spin) : pB (pcode p) / 4 = (p 2).val := by
  rw [pB_pcode]; have := (p 3).2; omega

theorem pB_mod (p : Fin 4 → Spin) : pB (pcode p) % 4 = (p 3).val := by
  rw [pB_pcode]; have := (p 3).2; omega

theorem pA_lt (p : Fin 4 → Spin) : pA (pcode p) < 16 := by rw [pA_pcode]; have := (p 0).2; have := (p 1).2; omega
theorem pB_lt (p : Fin 4 → Spin) : pB (pcode p) < 16 := by rw [pB_pcode]; have := (p 2).2; have := (p 3).2; omega

theorem pairDim_pA (p : Fin 4 → Spin) : pairDim (pA (pcode p)) = radix p 0 * radix p 1 := by
  unfold pairDim; rw [pA_div, pA_mod]; rfl

theorem pairDim_pB (p : Fin 4 → Spin) : pairDim (pB (pcode p)) = radix p 2 * radix p 3 := by
  unfold pairDim; rw [pB_div, pB_mod]; rfl

theorem checkU_spec (h : checkU () = true) (code : ℕ) (hc : code < 256) (k : ℕ) (hk : k < (uInfo code).size) :
    let e := (uInfo code).getD k default
    e.s < e.gA ∧ e.t < e.gB ∧ ∀ x < e.d, e.oA + x * e.gA + e.s < pairDim (pA code) ∧ e.oB + x * e.gB + e.t < pairDim (pB code) := by
  unfold checkU at h
  have h1 := (allTo_iff _ _).1 h code (by rw [hide_eq]; exact hc)
  have h2 := (allTo_iff _ _).1 h1 k hk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
  refine ⟨h2.1.1, h2.1.2, fun x hx => ?_⟩
  have := (allTo_iff _ _).1 h2.2 x hx
  simpa using this

theorem hatEntry_eq (isW : Bool) (code u i j : ℕ) :
    hatEntry isW code u i j =
      ∑ x ∈ range ((uInfo code).getD u default).d,
        if i = ((uInfo code).getD u default).oA + x * ((uInfo code).getD u default).gA + ((uInfo code).getD u default).s ∧
           j = ((uInfo code).getD u default).oB + x * ((uInfo code).getD u default).gB + ((uInfo code).getD u default).t
        then (if isW then wc ((uInfo code).getD u default).lab x else vc ((uInfo code).getD u default).lab x) else 0 := by
  unfold hatEntry
  rw [sumTo_eq]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : i = ((uInfo code).getD u default).oA + x * ((uInfo code).getD u default).gA + ((uInfo code).getD u default).s ∧
           j = ((uInfo code).getD u default).oB + x * ((uInfo code).getD u default).gB + ((uInfo code).getD u default).t
  · rw [ite_eq_left h]; rw [ite_eq_left]; simp [h.1, h.2]
  · rw [ite_eq_right h, ite_eq_right]; simpa using h

theorem checkStructure_spec (h : checkStructure () = true) (code : ℕ) (hc : code < 256) (b : ℕ) (hb : b < nn code) :
    (uInfo code).size = nn code ∧
    (∀ i < pairDim (pA code), ∀ j < pairDim (pB code),
      DataStr.lc * gt (coupledW code b) (i * pairDim (pB code) + j) =
        ∑ u ∈ range (nn code), gt omArr (nnOff code + b * nn code + u) * hatEntry true code u i j) ∧
    (∀ i < pairDim (pA code), ∀ j < pairDim (pB code),
      DataStr.lc * gt (coupledV code b) (i * pairDim (pB code) + j) =
        ∑ u ∈ range (nn code), gt xiArr (nnOff code + b * nn code + u) * hatEntry false code u i j) := by
  unfold checkStructure at h
  have h1 := (allTo_iff _ _).1 h code (by rw [hide_eq]; exact hc)
  have h2 := (allTo_iff _ _).1 h1 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h2
  have hsz : (uInfo code).size = nn code := h2.1
  refine ⟨hsz, fun i hi j hj => ?_, fun i hi j hj => ?_⟩
  · have h3 := (allTo_iff _ _).1 h2.2 (i * pairDim (pB code) + j) (by nlinarith)
    simp only [Bool.and_eq_true, beq_iff_eq] at h3
    have e1 := h3.1
    obtain ⟨d1, d2⟩ := div_mod_aux i j (pairDim (pB code)) hj
    simp only [d1, d2] at e1
    rw [e1]
    unfold reconEntry
    rw [sumTo_eq, hsz]
    refine Finset.sum_congr rfl fun u hu => ?_
    unfold slice
    rw [gt_tab, ite_eq_left (Finset.mem_range.1 hu)]
  · have h3 := (allTo_iff _ _).1 h2.2 (i * pairDim (pB code) + j) (by nlinarith)
    simp only [Bool.and_eq_true, beq_iff_eq] at h3
    have e1 := h3.2
    obtain ⟨d1, d2⟩ := div_mod_aux i j (pairDim (pB code)) hj
    simp only [d1, d2] at e1
    rw [e1]
    unfold reconEntry
    rw [sumTo_eq, hsz]
    refine Finset.sum_congr rfl fun u hu => ?_
    unfold slice
    rw [gt_tab, ite_eq_left (Finset.mem_range.1 hu)]

/-!
## The coupled identity for one pair of letters in a sector `p`
-/

theorem qe_psiMat (a : ℕ) (jx j' : Spin) (mu mup x y : ℕ) (hx : x < multF j') (hy : y < multF j') :
    qe (psiMat a jx j' mu mup) x y = psiAt (a - 3) jx.val j'.val mu mup x y := by
  unfold qe; rw [dite_eq_left ⟨hx, hy⟩]; rfl

theorem pairKron_A (p : Fin 4 → Spin) (a : ℕ) (sp : Fin 4 → Spin) (mu mu' : Fin 4 → ℕ) (e e' : ℕ)
    (he : e < radix p 0 * radix p 1) (he' : e' < radix p 0 * radix p 1) :
    pairKron (a - 3) (sp 0).val (sp 1).val (pA (pcode p)) (mu 0, mu' 0, mu 1, mu' 1) e e' =
      qe (psiMat a (sp 0) (p 0) (mu 0) (mu' 0)) (e / radix p 1) (e' / radix p 1) *
        qe (psiMat a (sp 1) (p 1) (mu 1) (mu' 1)) (e % radix p 1) (e' % radix p 1) := by
  unfold pairKron
  rw [pA_div, pA_mod]
  have h1 : e / radix p 1 < radix p 0 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact he)
  have h2 : e' / radix p 1 < radix p 0 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact he')
  have hpos : 0 < radix p 1 := by
    rcases Nat.eq_zero_or_pos (radix p 1) with h | h
    · rw [h] at he; omega
    · exact h
  have h3 : e % radix p 1 < radix p 1 := Nat.mod_lt _ hpos
  have h4 : e' % radix p 1 < radix p 1 := Nat.mod_lt _ hpos
  rw [qe_psiMat _ _ _ _ _ _ _ h1 h2, qe_psiMat _ _ _ _ _ _ _ h3 h4]
  rfl

theorem pairKron_B (p : Fin 4 → Spin) (a : ℕ) (sp : Fin 4 → Spin) (mu mu' : Fin 4 → ℕ) (e e' : ℕ)
    (he : e < radix p 2 * radix p 3) (he' : e' < radix p 2 * radix p 3) :
    pairKron (a - 3) (sp 2).val (sp 3).val (pB (pcode p)) (mu 2, mu' 2, mu 3, mu' 3) e e' =
      qe (psiMat a (sp 2) (p 2) (mu 2) (mu' 2)) (e / radix p 3) (e' / radix p 3) *
        qe (psiMat a (sp 3) (p 3) (mu 3) (mu' 3)) (e % radix p 3) (e' % radix p 3) := by
  unfold pairKron
  rw [pB_div, pB_mod]
  have h1 : e / radix p 3 < radix p 2 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact he)
  have h2 : e' / radix p 3 < radix p 2 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact he')
  have hpos : 0 < radix p 3 := by
    rcases Nat.eq_zero_or_pos (radix p 3) with h | h
    · rw [h] at he; omega
    · exact h
  have h3 : e % radix p 3 < radix p 3 := Nat.mod_lt _ hpos
  have h4 : e' % radix p 3 < radix p 3 := Nat.mod_lt _ hpos
  rw [qe_psiMat _ _ _ _ _ _ _ h1 h2, qe_psiMat _ _ _ _ _ _ _ h3 h4]
  rfl

theorem pair_identity (hT : checkT () = true) (hU : checkU () = true) (hS : checkStructure () = true)
    (p : Fin 4 → Spin) (a : ℕ) (sp : Fin 4 → Spin) (mu mu' : Fin 4 → ℕ) (A B : Fin (nnF p)) :
    delta (pA (pcode p)) ^ 2 * delta (pB (pcode p)) ^ 2 * DataStr.lc ^ 2 *
      (∑ x : (∀ q, Fin (multF (p q))), ∑ y : (∀ q, Fin (multF (p q))),
        Wmat p x A * kronPi (fun r => psiMat a (sp r) (p r) (mu r) (mu' r)) x y * Vmat p y B) =
    ∑ u ∈ range (nn (pcode p)), ∑ u' ∈ range (nn (pcode p)),
      gt omArr (nnOff (pcode p) + A.val * nn (pcode p) + u) * gt xiArr (nnOff (pcode p) + B.val * nn (pcode p) + u') *
        ctPair (pcode p)
          (tableLetter (a - 3) (sp 0).val (sp 1).val (pA (pcode p)) (mu 0, mu' 0, mu 1, mu' 1))
          (tableLetter (a - 3) (sp 2).val (sp 3).val (pB (pcode p)) (mu 2, mu' 2, mu 3, mu' 3))
          ((uInfo (pcode p)).getD u default) ((uInfo (pcode p)).getD u' default) := by
  have hcl : pcode p < 256 := pcode_lt p
  have hAn : A.val < nn (pcode p) := A.2
  have hBn : B.val < nn (pcode p) := B.2
  obtain ⟨hsz, hWs, -⟩ := checkStructure_spec hS (pcode p) hcl A.val hAn
  obtain ⟨-, -, hVs⟩ := checkStructure_spec hS (pcode p) hcl B.val hBn
  obtain ⟨hdA, hTA⟩ := checkT_spec hT (pA (pcode p)) (pA_lt p)
  obtain ⟨hdB, hTB⟩ := checkT_spec hT (pB (pcode p)) (pB_lt p)
  have hDA : pairDim (pA (pcode p)) = radix p 0 * radix p 1 := pairDim_pA p
  have hDB : pairDim (pB (pcode p)) = radix p 2 * radix p 3 := pairDim_pB p
  have e0 : (∑ x : (∀ q, Fin (multF (p q))), ∑ y : (∀ q, Fin (multF (p q))),
        Wmat p x A * kronPi (fun r => psiMat a (sp r) (p r) (mu r) (mu' r)) x y * Vmat p y B) =
      ∑ x : (∀ q, Fin (multF (p q))), ∑ y : (∀ q, Fin (multF (p q))),
        (fun f => wAt (pcode p) A.val f) (flatIx (radix p) x) * kronPi (fun r => psiMat a (sp r) (p r) (mu r) (mu' r)) x y *
          (fun f => vAt (pcode p) B.val f) (flatIx (radix p) y) := rfl
  rw [e0, contr_eq_S4 (radix p) (fun r => psiMat a (sp r) (p r) (mu r) (mu' r))]
  have hA2 : ∀ i < radix p 0 * radix p 1, ∀ j < radix p 0 * radix p 1,
      ∑ k ∈ range (radix p 0 * radix p 1), tiAt (pA (pcode p)) i k * tAt (pA (pcode p)) k j =
        if i = j then delta (pA (pcode p)) else 0 := by
    intro i hi j hj
    rw [← hDA] at hi hj ⊢
    exact hTA i j hi hj
  have hB2 : ∀ i < radix p 2 * radix p 3, ∀ j < radix p 2 * radix p 3,
      ∑ k ∈ range (radix p 2 * radix p 3), tiAt (pB (pcode p)) i k * tAt (pB (pcode p)) k j =
        if i = j then delta (pB (pcode p)) else 0 := by
    intro i hi j hj
    rw [← hDB] at hi hj ⊢
    exact hTB i j hi hj
  have hbd : ∀ u < nn (pcode p), ∀ x < ((uInfo (pcode p)).getD u default).d,
      ((uInfo (pcode p)).getD u default).oA + x * ((uInfo (pcode p)).getD u default).gA + ((uInfo (pcode p)).getD u default).s
        < radix p 0 * radix p 1 ∧
      ((uInfo (pcode p)).getD u default).oB + x * ((uInfo (pcode p)).getD u default).gB + ((uInfo (pcode p)).getD u default).t
        < radix p 2 * radix p 3 := by
    intro u hu x hx
    have := (checkU_spec hU (pcode p) hcl u (by rw [hsz]; exact hu)).2.2 x hx
    rw [hDA, hDB] at this
    exact this
  have hW : ∀ i < radix p 0 * radix p 1, ∀ j < radix p 2 * radix p 3,
      DataStr.lc * (∑ l ∈ range (radix p 2 * radix p 3), (∑ k ∈ range (radix p 0 * radix p 1),
        tiAt (pA (pcode p)) k i * wAt (pcode p) A.val (k * (radix p 2 * radix p 3) + l)) * tiAt (pB (pcode p)) l j) =
      ∑ u ∈ range (nn (pcode p)), gt omArr (nnOff (pcode p) + A.val * nn (pcode p) + u) *
        ∑ x ∈ range ((uInfo (pcode p)).getD u default).d,
          if i = ((uInfo (pcode p)).getD u default).oA + x * ((uInfo (pcode p)).getD u default).gA +
              ((uInfo (pcode p)).getD u default).s ∧
            j = ((uInfo (pcode p)).getD u default).oB + x * ((uInfo (pcode p)).getD u default).gB +
              ((uInfo (pcode p)).getD u default).t
          then wc ((uInfo (pcode p)).getD u default).lab x else 0 := by
    intro i hi j hj
    have h1 := hWs i (by rw [hDA]; exact hi) j (by rw [hDB]; exact hj)
    rw [coupledW_entry (pcode p) A.val i j (by rw [hDA]; exact hi) (by rw [hDB]; exact hj)] at h1
    simp only [hDA, hDB, hatEntry_eq] at h1
    simpa using h1
  have hV : ∀ i < radix p 0 * radix p 1, ∀ j < radix p 2 * radix p 3,
      DataStr.lc * (∑ l ∈ range (radix p 2 * radix p 3), (∑ k ∈ range (radix p 0 * radix p 1),
        tAt (pA (pcode p)) i k * vAt (pcode p) B.val (k * (radix p 2 * radix p 3) + l)) * tAt (pB (pcode p)) j l) =
      ∑ u ∈ range (nn (pcode p)), gt xiArr (nnOff (pcode p) + B.val * nn (pcode p) + u) *
        ∑ x ∈ range ((uInfo (pcode p)).getD u default).d,
          if i = ((uInfo (pcode p)).getD u default).oA + x * ((uInfo (pcode p)).getD u default).gA +
              ((uInfo (pcode p)).getD u default).s ∧
            j = ((uInfo (pcode p)).getD u default).oB + x * ((uInfo (pcode p)).getD u default).gB +
              ((uInfo (pcode p)).getD u default).t
          then vc ((uInfo (pcode p)).getD u default).lab x else 0 := by
    intro i hi j hj
    have h1 := hVs i (by rw [hDA]; exact hi) j (by rw [hDB]; exact hj)
    rw [coupledV_entry (pcode p) B.val i j (by rw [hDA]; exact hi) (by rw [hDB]; exact hj)] at h1
    simp only [hDA, hDB, hatEntry_eq] at h1
    simpa using h1
  have key := coupled_generic (radix p 0 * radix p 1) (radix p 2 * radix p 3) (nn (pcode p))
    (tAt (pA (pcode p))) (tiAt (pA (pcode p))) (tAt (pB (pcode p))) (tiAt (pB (pcode p)))
    (fun i j => wAt (pcode p) A.val (i * (radix p 2 * radix p 3) + j))
    (fun i j => vAt (pcode p) B.val (i * (radix p 2 * radix p 3) + j))
    (fun i k => qe (psiMat a (sp 0) (p 0) (mu 0) (mu' 0)) (i / radix p 1) (k / radix p 1) *
      qe (psiMat a (sp 1) (p 1) (mu 1) (mu' 1)) (i % radix p 1) (k % radix p 1))
    (fun j l => qe (psiMat a (sp 2) (p 2) (mu 2) (mu' 2)) (j / radix p 3) (l / radix p 3) *
      qe (psiMat a (sp 3) (p 3) (mu 3) (mu' 3)) (j % radix p 3) (l % radix p 3))
    (delta (pA (pcode p))) (delta (pB (pcode p))) DataStr.lc
    (fun u => gt omArr (nnOff (pcode p) + A.val * nn (pcode p) + u))
    (fun u => gt xiArr (nnOff (pcode p) + B.val * nn (pcode p) + u))
    (fun u => ((uInfo (pcode p)).getD u default).d)
    (fun u x => ((uInfo (pcode p)).getD u default).oA + x * ((uInfo (pcode p)).getD u default).gA +
      ((uInfo (pcode p)).getD u default).s)
    (fun u x => ((uInfo (pcode p)).getD u default).oB + x * ((uInfo (pcode p)).getD u default).gB +
      ((uInfo (pcode p)).getD u default).t)
    (fun u x => wc ((uInfo (pcode p)).getD u default).lab x) (fun u x => vc ((uInfo (pcode p)).getD u default).lab x)
    hA2 hB2 hbd hW hV
  refine Eq.trans key ?_
  refine Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun u' hu' => ?_
  refine congrArg (fun z => gt omArr (nnOff (pcode p) + A.val * nn (pcode p) + u) *
    gt xiArr (nnOff (pcode p) + B.val * nn (pcode p) + u') * z) ?_
  have hu1 := Finset.mem_range.1 hu
  have hu2 := Finset.mem_range.1 hu'
  unfold ctPair
  simp only [sumTo_eq]
  refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
  have hx' := Finset.mem_range.1 hx
  have hy' := Finset.mem_range.1 hy
  obtain ⟨b1, b2⟩ := hbd u hu1 x hx'
  obtain ⟨b3, b4⟩ := hbd u' hu2 y hy'
  have t1 := tableLetter_apply (a - 3) (sp 0).val (sp 1).val (pA (pcode p)) (mu 0, mu' 0, mu 1, mu' 1) _ _
    (by rw [← pairDim]; rw [hDA]; exact b1) (by rw [← pairDim]; rw [hDA]; exact b3)
  have t2 := tableLetter_apply (a - 3) (sp 2).val (sp 3).val (pB (pcode p)) (mu 2, mu' 2, mu 3, mu' 3) _ _
    (by rw [← pairDim]; rw [hDB]; exact b2) (by rw [← pairDim]; rw [hDB]; exact b4)
  change gt _ (_ * pairDim (pA (pcode p)) + _) = _ at t1
  change gt _ (_ * pairDim (pB (pcode p)) + _) = _ at t2
  rw [t1, t2]
  have hrA : mult (pA (pcode p) / 4) * mult (pA (pcode p) % 4) = radix p 0 * radix p 1 := hDA
  have hrB : mult (pB (pcode p) / 4) * mult (pB (pcode p) % 4) = radix p 2 * radix p 3 := hDB
  rw [hrA, hrB]
  have hSA : ∀ row col : ℕ, (∑ e ∈ range (radix p 0 * radix p 1), ∑ e' ∈ range (radix p 0 * radix p 1),
      tAt (pA (pcode p)) row e * (qe (psiMat a (sp 0) (p 0) (mu 0) (mu' 0)) (e / radix p 1) (e' / radix p 1) *
        qe (psiMat a (sp 1) (p 1) (mu 1) (mu' 1)) (e % radix p 1) (e' % radix p 1)) * tiAt (pA (pcode p)) e' col) =
      ∑ e ∈ range (radix p 0 * radix p 1), ∑ e' ∈ range (radix p 0 * radix p 1),
        tAt (pA (pcode p)) row e * pairKron (a - 3) (sp 0).val (sp 1).val (pA (pcode p)) (mu 0, mu' 0, mu 1, mu' 1) e e' *
          tiAt (pA (pcode p)) e' col := by
    intro row col
    refine Finset.sum_congr rfl fun e he => Finset.sum_congr rfl fun e' he' => ?_
    rw [pairKron_A p a sp mu mu' e e' (Finset.mem_range.1 he) (Finset.mem_range.1 he')]
  have hSB : ∀ row col : ℕ, (∑ e ∈ range (radix p 2 * radix p 3), ∑ e' ∈ range (radix p 2 * radix p 3),
      tAt (pB (pcode p)) row e * (qe (psiMat a (sp 2) (p 2) (mu 2) (mu' 2)) (e / radix p 3) (e' / radix p 3) *
        qe (psiMat a (sp 3) (p 3) (mu 3) (mu' 3)) (e % radix p 3) (e' % radix p 3)) * tiAt (pB (pcode p)) e' col) =
      ∑ e ∈ range (radix p 2 * radix p 3), ∑ e' ∈ range (radix p 2 * radix p 3),
        tAt (pB (pcode p)) row e * pairKron (a - 3) (sp 2).val (sp 3).val (pB (pcode p)) (mu 2, mu' 2, mu 3, mu' 3) e e' *
          tiAt (pB (pcode p)) e' col := by
    intro row col
    refine Finset.sum_congr rfl fun e he => Finset.sum_congr rfl fun e' he' => ?_
    rw [pairKron_B p a sp mu mu' e e' (Finset.mem_range.1 he) (Finset.mem_range.1 he')]
  rw [hSA, hSB]

end QVCheck
