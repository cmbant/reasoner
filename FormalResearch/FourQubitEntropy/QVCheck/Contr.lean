import FormalResearch.FourQubitEntropy.QVCheck.Chars
import FormalResearch.FourQubitEntropy.QVCheck.Coupling
import FormalResearch.FourQubitEntropy.QVCheck.PsiBlock

/-!
# Reshaping a four-qubit contraction into the pair form `S4`

For a sector `p` with radices `m q`, `DA = m 0 * m 1`, `DB = m 2 * m 3`:
`∑_{x,y} w(flat x) (⊗_q Q_q)(x,y) v(flat y) = S4 W P V R`, where `W_{ij} = w(i DB + j)`, `V_{kl} = v(k DB + l)`,
`P_{ik} = Q_0(i/m1, k/m1) Q_1(i%m1, k%m1)`, `R_{jl} = Q_2(j/m3, l/m3) Q_3(j%m3, l%m3)`.
-/

open Finset
open scoped Matrix
open FormalResearch.FourQubitEntropy FormalResearch.FourQubitEntropy.QVBlock

namespace QVCheck

/-- a function `ℕ × ℕ → ℤ` as a matrix -/
def nm (D1 D2 : ℕ) (f : ℕ → ℕ → ℤ) : Matrix (Fin D1) (Fin D2) ℤ := Matrix.of fun i j => f i.val j.val

/-- entry of a matrix at natural indices (zero outside) -/
def qe {m : ℕ} (Q : Matrix (Fin m) (Fin m) ℤ) (a b : ℕ) : ℤ := if h : a < m ∧ b < m then Q ⟨a, h.1⟩ ⟨b, h.2⟩ else 0

theorem qe_fin {m : ℕ} (Q : Matrix (Fin m) (Fin m) ℤ) (a b : Fin m) : qe Q a.val b.val = Q a b := by
  unfold qe; rw [dif_pos ⟨a.2, b.2⟩]

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
  rw [dif_pos ⟨a.2, b.2, c.2, d.2⟩]


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
  rw [dif_pos ⟨h0', h1', h2', h3'⟩]
  refine Finset.sum_congr rfl fun b0 hb0 => Finset.sum_congr rfl fun b1 hb1 =>
    Finset.sum_congr rfl fun b2 hb2 => Finset.sum_congr rfl fun b3 hb3 => ?_
  have hb0' := Finset.mem_range.1 hb0; have hb1' := Finset.mem_range.1 hb1
  have hb2' := Finset.mem_range.1 hb2; have hb3' := Finset.mem_range.1 hb3
  rw [dif_pos ⟨hb0', hb1', hb2', hb3'⟩]
  obtain ⟨d0, e0⟩ := div_mod_aux a0 a1 (m 1) h1'
  obtain ⟨d1, e1⟩ := div_mod_aux b0 b1 (m 1) hb1'
  obtain ⟨d2, e2⟩ := div_mod_aux a2 a3 (m 3) h3'
  obtain ⟨d3, e3⟩ := div_mod_aux b2 b3 (m 3) hb3'
  rw [d0, e0, d1, e1, d2, e2, d3, e3]
  have hq : ∀ (q : Fin 4) (a b : ℕ) (ha : a < m q) (hb : b < m q), qe (Q q) a b = Q q ⟨a, ha⟩ ⟨b, hb⟩ := by
    intro q a b ha hb; unfold qe; rw [dif_pos ⟨ha, hb⟩]
  rw [hq 0 a0 b0 h0' hb0', hq 1 a1 b1 h1' hb1', hq 2 a2 b2 h2' hb2', hq 3 a3 b3 h3' hb3']
  have hk : kronPi Q ((ixEquiv m).symm (⟨a0, h0'⟩, ⟨a1, h1'⟩, ⟨a2, h2'⟩, ⟨a3, h3'⟩))
      ((ixEquiv m).symm (⟨b0, hb0'⟩, ⟨b1, hb1'⟩, ⟨b2, hb2'⟩, ⟨b3, hb3'⟩)) =
      Q 0 ⟨a0, h0'⟩ ⟨b0, hb0'⟩ * Q 1 ⟨a1, h1'⟩ ⟨b1, hb1'⟩ * Q 2 ⟨a2, h2'⟩ ⟨b2, hb2'⟩ * Q 3 ⟨a3, h3'⟩ ⟨b3, hb3'⟩ := by
    rw [kronPi_apply, Fin.prod_univ_four]; rfl
  rw [hk, flatIx_eq, flatIx_eq]
  show wv ((a0 * m 1 + a1) * (m 2 * m 3) + (a2 * m 3 + a3)) * _ * vv ((b0 * m 1 + b1) * (m 2 * m 3) + (b2 * m 3 + b3)) = _
  ring

end QVCheck
