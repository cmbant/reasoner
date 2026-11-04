module

public import Mathlib
public import QVCheckImpl.Basic
public import QVCheckImpl.Impl2
public import FormalResearch.FourQubitEntropy.QVBlock.Kron

/-!
# Array semantics of the checker primitives

`QVCheckImpl` is Mathlib-free executable code over flat `Array Int`s.  This module gives its primitives their meaning:

* the loop combinators `sumTo`, `allTo`, `tab` are finite sums, bounded universal quantifiers and tabulations;
* the mode products `modeProd`, composed along the four qubit axes (`kron4`), compute the Kronecker action `⊗_q M_q` on
  flat tensors (`kron4_eq_sum`).
-/

@[expose] public section


open Finset

namespace QVCheck

/-!
## Loop combinators (`QVCheckImpl.Basic`)

* `sumTo n f = ∑ i < n, f i`, `allTo n p = true ↔ ∀ i < n, p i = true`,
* `(tab n f).getD i 0 = if i < n then f i else 0`, `(tab n f).size = n`.
-/

theorem hide_eq (u : Unit) (n : Nat) : hide u n = n := rfl

theorem sumAux_eq (f : Nat → Int) (n : Nat) (acc : Int) :
    sumAux f n acc = acc + ∑ i ∈ range n, f i := by
  induction n generalizing acc with
  | zero => simp [sumAux]
  | succ k ih => rw [sumAux, ih, Finset.sum_range_succ]; ring

theorem sumTo_eq (n : Nat) (f : Nat → Int) : sumTo n f = ∑ i ∈ range n, f i := by
  simp [sumTo, sumAux_eq]

theorem allAux_iff (p : Nat → Bool) (n : Nat) : allAux p n = true ↔ ∀ i < n, p i = true := by
  induction n with
  | zero => simp [allAux]
  | succ k ih =>
    rw [allAux, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
      · exact h2 i h
      · subst h; exact h1
    · intro h; exact ⟨h k (Nat.lt_succ_self k), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

theorem allTo_iff (n : Nat) (p : Nat → Bool) : allTo n p = true ↔ ∀ i < n, p i = true :=
  allAux_iff p n

theorem tabAux_eq (f : Nat → Int) (n : Nat) :
    ∀ (k : Nat), k ≤ n → ∀ (acc : Array Int),
      tabAux f n k acc = acc ++ ((List.range' (n - k) k).map f).toArray := by
  intro k
  induction k with
  | zero => intro _ acc; simp [tabAux]
  | succ k ih =>
    intro hk acc
    rw [tabAux, ih (by omega)]
    have h1 : n - (k + 1) + 1 = n - k := by omega
    have h2 : n - (k + 1) = n - 1 - k := by omega
    rw [List.range'_succ, h1, h2]
    simp

theorem tab_toList (n : Nat) (f : Nat → Int) : tab n f = ((List.range n).map f).toArray := by
  unfold tab
  rw [tabAux_eq f n n le_rfl]
  simp [List.range_eq_range']

theorem tab_size (n : Nat) (f : Nat → Int) : (tab n f).size = n := by
  rw [tab_toList]; simp

theorem tab_getD (n : Nat) (f : Nat → Int) (i : Nat) :
    (tab n f).getD i 0 = if i < n then f i else 0 := by
  rw [tab_toList]
  by_cases h : i < n
  · simp [h, Array.getD]
  · simp [h, Array.getD]

theorem gt_tab (n : Nat) (f : Nat → Int) (i : Nat) : gt (tab n f) i = if i < n then f i else 0 :=
  tab_getD n f i

/-!
## Mode products on flat tensors (K2, K6 and the table stage)

`modeProd M m s tr X` applies the `m × m` matrix `M` (or its transpose) to the axis of radix `m` and stride `s` of the flat
array `X`.  We prove `modeProd_apply` (the entry formula in the three-level decomposition `idx = (a m + r) s + b`) and, for four
axes with radices `m q` and the mixed-radix flattening `flat`, that applying the four mode products is `⊗_q M_q`
(`kron4_entry`, `kron4_eq_sum`).
-/

theorem modeProd_apply (M : Array Int) (m s : Nat) (tr : Bool) (X : Array Int) (a r b : Nat)
    (hr : r < m) (hb : b < s) (hl : (a * m + r) * s + b < X.size) :
    (modeProd M m s tr X).getD ((a * m + r) * s + b) 0 =
      ∑ k ∈ range m, (if tr then gt M (k * m + r) else gt M (r * m + k)) * gt X ((a * m + k) * s + b) := by
  have hs : 0 < s := by omega
  have hm : 0 < m := by omega
  unfold modeProd
  rw [tab_getD, ite_eq_left (by simpa using hl), sumTo_eq]
  have h1 : ((a * m + r) * s + b) / s % m = r := by
    have : ((a * m + r) * s + b) / s = a * m + r := by
      rw [Nat.mul_comm (a * m + r) s]
      rw [Nat.mul_add_div hs, Nat.div_eq_of_lt hb]; simp
    rw [this, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
  have h2 : ((a * m + r) * s + b) % s = b := by
    rw [Nat.mul_comm (a * m + r) s, Nat.mul_add_mod, Nat.mod_eq_of_lt hb]
  have h3 : ((a * m + r) * s + b) / (s * m) = a := by
    have : (a * m + r) * s + b = (s * m) * a + (r * s + b) := by ring
    rw [this, Nat.mul_add_div (Nat.mul_pos hs hm)]
    have : (r * s + b) / (s * m) = 0 := by
      apply Nat.div_eq_of_lt
      have : r * s + b < (r + 1) * s := by nlinarith
      have : (r + 1) * s ≤ m * s := Nat.mul_le_mul_right s hr
      nlinarith
    simp [this]
  simp only [h1, h2, h3]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 2
  ring


/-! ### Four axes -/

/-- mixed-radix flattening of a four-digit index -/
def flat4 (m1 m2 m3 a b c d : Nat) : Nat := ((a * m1 + b) * m2 + c) * m3 + d

theorem flat4_lt {m0 m1 m2 m3 a b c d : Nat} (ha : a < m0) (hb : b < m1) (hc : c < m2) (hd : d < m3) :
    flat4 m1 m2 m3 a b c d < m0 * m1 * m2 * m3 := by
  unfold flat4
  have h1 : a * m1 + b < m0 * m1 := by
    calc a * m1 + b < a * m1 + m1 := by omega
      _ = (a + 1) * m1 := by ring
      _ ≤ m0 * m1 := Nat.mul_le_mul_right m1 ha
  have h2 : (a * m1 + b) * m2 + c < m0 * m1 * m2 := by
    calc (a * m1 + b) * m2 + c < (a * m1 + b) * m2 + m2 := by omega
      _ = (a * m1 + b + 1) * m2 := by ring
      _ ≤ m0 * m1 * m2 := Nat.mul_le_mul_right m2 h1
  calc ((a * m1 + b) * m2 + c) * m3 + d < ((a * m1 + b) * m2 + c) * m3 + m3 := by omega
    _ = ((a * m1 + b) * m2 + c + 1) * m3 := by ring
    _ ≤ m0 * m1 * m2 * m3 := Nat.mul_le_mul_right m3 h2

section four
variable (M0 M1 M2 M3 : Array Int) (m0 m1 m2 m3 : Nat) (tr : Bool) (X : Array Int)

/-- the matrix entry used by `modeProd` -/
def mEnt (tr : Bool) (M : Array Int) (m r k : Nat) : Int := if tr then gt M (k * m + r) else gt M (r * m + k)

/-- the four mode products applied in the order `0, 1, 2, 3` (as `kronGen` does) -/
def kron4 (X : Array Int) : Array Int :=
  modeProd M3 m3 1 tr (modeProd M2 m2 m3 tr (modeProd M1 m1 (m2 * m3) tr (modeProd M0 m0 (m1 * m2 * m3) tr X)))

theorem modeProd_size (M : Array Int) (m s : Nat) (tr : Bool) (X : Array Int) :
    (modeProd M m s tr X).size = X.size := by
  unfold modeProd; rw [tab_size]

theorem mode_entry_gen (M : Array Int) (m s : Nat) (tr : Bool) (X : Array Int) (a r b : Nat)
    (hr : r < m) (hb : b < s) (idx : Nat) (hidx : idx = (a * m + r) * s + b) (hl : idx < X.size)
    (f : Nat → Nat) (hf : ∀ k, (a * m + k) * s + b = f k) :
    (modeProd M m s tr X).getD idx 0 = ∑ k ∈ range m, mEnt tr M m r k * gt X (f k) := by
  subst hidx
  rw [modeProd_apply M m s tr X a r b hr hb hl]
  exact Finset.sum_congr rfl fun k _ => by rw [hf k]; rfl

theorem kron4_entry (hX : X.size = m0 * m1 * m2 * m3) {a b c d : Nat} (ha : a < m0) (hb : b < m1) (hc : c < m2)
    (hd : d < m3) :
    (kron4 M0 M1 M2 M3 m0 m1 m2 m3 tr X).getD (flat4 m1 m2 m3 a b c d) 0 =
      ∑ k3 ∈ range m3, mEnt tr M3 m3 d k3 * ∑ k2 ∈ range m2, mEnt tr M2 m2 c k2 *
        ∑ k1 ∈ range m1, mEnt tr M1 m1 b k1 * ∑ k0 ∈ range m0, mEnt tr M0 m0 a k0 *
          gt X (flat4 m1 m2 m3 k0 k1 k2 k3) := by
  have hlt : ∀ a b c d, a < m0 → b < m1 → c < m2 → d < m3 → flat4 m1 m2 m3 a b c d < X.size := by
    intro a b c d ha hb hc hd; rw [hX]; exact flat4_lt ha hb hc hd
  set A1 := modeProd M0 m0 (m1 * m2 * m3) tr X with hA1
  set A2 := modeProd M1 m1 (m2 * m3) tr A1 with hA2
  set A3 := modeProd M2 m2 m3 tr A2 with hA3
  have s1 : A1.size = X.size := modeProd_size _ _ _ _ _
  have s2 : A2.size = X.size := by rw [hA2, modeProd_size, s1]
  have s3 : A3.size = X.size := by rw [hA3, modeProd_size, s2]
  have p1 : 0 < m1 := by omega
  have e1 : ∀ a b c d, a < m0 → b < m1 → c < m2 → d < m3 →
      A1.getD (flat4 m1 m2 m3 a b c d) 0 = ∑ k ∈ range m0, mEnt tr M0 m0 a k * gt X (flat4 m1 m2 m3 k b c d) := by
    intro a b c d ha hb hc hd
    refine mode_entry_gen M0 m0 (m1 * m2 * m3) tr X 0 a ((b * m2 + c) * m3 + d) ha ?_ _ ?_ (hlt a b c d ha hb hc hd) _ ?_
    · have := flat4_lt (m0 := 1) (m1 := m1) (m2 := m2) (m3 := m3) (a := 0) (b := b) (c := c) (d := d) (by omega) hb hc hd
      unfold flat4 at this; nlinarith
    · unfold flat4; ring
    · intro k; unfold flat4; ring
  have e2 : ∀ a b c d, a < m0 → b < m1 → c < m2 → d < m3 →
      A2.getD (flat4 m1 m2 m3 a b c d) 0 = ∑ k ∈ range m1, mEnt tr M1 m1 b k * A1.getD (flat4 m1 m2 m3 a k c d) 0 := by
    intro a b c d ha hb hc hd
    have := mode_entry_gen M1 m1 (m2 * m3) tr A1 a b (c * m3 + d) hb (by
      have := flat4_lt (m0 := 1) (m1 := m1) (m2 := m2) (m3 := m3) (a := 0) (b := 0) (c := c) (d := d) (by omega) p1 hc hd
      unfold flat4 at this; nlinarith) (flat4 m1 m2 m3 a b c d) (by unfold flat4; ring) (by rw [s1]; exact hlt a b c d ha hb hc hd)
      (fun k => flat4 m1 m2 m3 a k c d) (by intro k; unfold flat4; ring)
    rw [hA2]; rw [this]
    exact Finset.sum_congr rfl fun k _ => rfl
  have e3 : ∀ a b c d, a < m0 → b < m1 → c < m2 → d < m3 →
      A3.getD (flat4 m1 m2 m3 a b c d) 0 = ∑ k ∈ range m2, mEnt tr M2 m2 c k * A2.getD (flat4 m1 m2 m3 a b k d) 0 := by
    intro a b c d ha hb hc hd
    have := mode_entry_gen M2 m2 m3 tr A2 (a * m1 + b) c d hc hd (flat4 m1 m2 m3 a b c d) (by unfold flat4; ring)
      (by rw [s2]; exact hlt a b c d ha hb hc hd) (fun k => flat4 m1 m2 m3 a b k d) (by intro k; unfold flat4; ring)
    rw [hA3, this]
    exact Finset.sum_congr rfl fun k _ => rfl
  have e4 : ∀ a b c d, a < m0 → b < m1 → c < m2 → d < m3 →
      (kron4 M0 M1 M2 M3 m0 m1 m2 m3 tr X).getD (flat4 m1 m2 m3 a b c d) 0 =
        ∑ k ∈ range m3, mEnt tr M3 m3 d k * A3.getD (flat4 m1 m2 m3 a b c k) 0 := by
    intro a b c d ha hb hc hd
    have := mode_entry_gen M3 m3 1 tr A3 ((a * m1 + b) * m2 + c) d 0 hd (by omega) (flat4 m1 m2 m3 a b c d) (by unfold flat4; ring)
      (by rw [s3]; exact hlt a b c d ha hb hc hd) (fun k => flat4 m1 m2 m3 a b c k) (by intro k; unfold flat4; ring)
    unfold kron4
    rw [this]
    exact Finset.sum_congr rfl fun k _ => rfl
  rw [e4 a b c d ha hb hc hd]
  refine Finset.sum_congr rfl fun k3 hk3 => ?_
  have hk3' := Finset.mem_range.1 hk3
  congr 1
  rw [e3 a b c k3 ha hb hc hk3']
  refine Finset.sum_congr rfl fun k2 hk2 => ?_
  have hk2' := Finset.mem_range.1 hk2
  congr 1
  rw [e2 a b k2 k3 ha hb hk2' hk3']
  refine Finset.sum_congr rfl fun k1 hk1 => ?_
  have hk1' := Finset.mem_range.1 hk1
  congr 1
  rw [e1 a k1 k2 k3 ha hk1' hk2' hk3']

end four


/-! ### Kronecker product on `∀ q : Fin 4, Fin (m q)` -/

/-- the product type of four digits, identified with `∀ q : Fin 4, Fin (m q)` -/
def ixEquiv (m : Fin 4 → ℕ) :
    (∀ q : Fin 4, Fin (m q)) ≃ Fin (m 0) × Fin (m 1) × Fin (m 2) × Fin (m 3) where
  toFun x := (x 0, x 1, x 2, x 3)
  invFun t := fun q => match q with
    | ⟨0, _⟩ => t.1
    | ⟨1, _⟩ => t.2.1
    | ⟨2, _⟩ => t.2.2.1
    | ⟨3, _⟩ => t.2.2.2
  left_inv x := by
    funext q
    fin_cases q <;> rfl
  right_inv t := rfl

/-- the flat index of a four-digit index -/
def flatIx (m : Fin 4 → ℕ) (x : ∀ q : Fin 4, Fin (m q)) : ℕ :=
  flat4 (m 1) (m 2) (m 3) (x 0) (x 1) (x 2) (x 3)

theorem flatIx_lt (m : Fin 4 → ℕ) (x : ∀ q : Fin 4, Fin (m q)) : flatIx m x < m 0 * m 1 * m 2 * m 3 :=
  flat4_lt (x 0).2 (x 1).2 (x 2).2 (x 3).2

/-- `kron4` computes `(⊗_q M_q) X` in flat coordinates. -/
theorem kron4_eq_sum (m : Fin 4 → ℕ) (Ms : Fin 4 → Array Int) (tr : Bool) (X : Array Int)
    (hX : X.size = m 0 * m 1 * m 2 * m 3) (x : ∀ q : Fin 4, Fin (m q)) :
    (kron4 (Ms 0) (Ms 1) (Ms 2) (Ms 3) (m 0) (m 1) (m 2) (m 3) tr X).getD (flatIx m x) 0 =
      ∑ y : (∀ q : Fin 4, Fin (m q)), (∏ q, mEnt tr (Ms q) (m q) (x q) (y q)) * gt X (flatIx m y) := by
  rw [flatIx, kron4_entry _ _ _ _ _ _ _ _ _ _ hX (x 0).2 (x 1).2 (x 2).2 (x 3).2]
  rw [← (ixEquiv m).symm.sum_comp]
  simp only [Fintype.sum_prod_type, Fin.prod_univ_four]
  have key : ∀ (f : ℕ → ℕ → ℕ → ℕ → ℤ),
      ∑ k3 ∈ range (m 3), ∑ k2 ∈ range (m 2), ∑ k1 ∈ range (m 1), ∑ k0 ∈ range (m 0), f k0 k1 k2 k3 =
      ∑ k0 ∈ range (m 0), ∑ k1 ∈ range (m 1), ∑ k2 ∈ range (m 2), ∑ k3 ∈ range (m 3), f k0 k1 k2 k3 := by
    intro f
    calc _ = ∑ k3 ∈ range (m 3), ∑ k2 ∈ range (m 2), ∑ k0 ∈ range (m 0), ∑ k1 ∈ range (m 1), f k0 k1 k2 k3 :=
          Finset.sum_congr rfl fun k3 _ => Finset.sum_congr rfl fun k2 _ => Finset.sum_comm
      _ = ∑ k3 ∈ range (m 3), ∑ k0 ∈ range (m 0), ∑ k2 ∈ range (m 2), ∑ k1 ∈ range (m 1), f k0 k1 k2 k3 :=
          Finset.sum_congr rfl fun k3 _ => Finset.sum_comm
      _ = ∑ k0 ∈ range (m 0), ∑ k3 ∈ range (m 3), ∑ k2 ∈ range (m 2), ∑ k1 ∈ range (m 1), f k0 k1 k2 k3 :=
          Finset.sum_comm
      _ = ∑ k0 ∈ range (m 0), ∑ k3 ∈ range (m 3), ∑ k1 ∈ range (m 1), ∑ k2 ∈ range (m 2), f k0 k1 k2 k3 :=
          Finset.sum_congr rfl fun k0 _ => Finset.sum_congr rfl fun k3 _ => Finset.sum_comm
      _ = ∑ k0 ∈ range (m 0), ∑ k1 ∈ range (m 1), ∑ k3 ∈ range (m 3), ∑ k2 ∈ range (m 2), f k0 k1 k2 k3 :=
          Finset.sum_congr rfl fun k0 _ => Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun k0 _ => Finset.sum_congr rfl fun k1 _ => Finset.sum_comm
  simp only [Finset.mul_sum]
  rw [key (fun k0 k1 k2 k3 => mEnt tr (Ms 3) (m 3) (↑(x 3)) k3 * (mEnt tr (Ms 2) (m 2) (↑(x 2)) k2 *
    (mEnt tr (Ms 1) (m 1) (↑(x 1)) k1 * (mEnt tr (Ms 0) (m 0) (↑(x 0)) k0 * gt X (flat4 (m 1) (m 2) (m 3) k0 k1 k2 k3)))))]
  have conv : ∀ (g : ℕ → ℕ → ℕ → ℕ → ℤ),
      ∑ a : Fin (m 0), ∑ b : Fin (m 1), ∑ c : Fin (m 2), ∑ d : Fin (m 3), g a b c d =
      ∑ k0 ∈ range (m 0), ∑ k1 ∈ range (m 1), ∑ k2 ∈ range (m 2), ∑ k3 ∈ range (m 3), g k0 k1 k2 k3 := by
    intro g
    simp only [Finset.sum_range]
  refine (conv _).symm.trans ?_
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun d _ => ?_
  have e0 : (((ixEquiv m).symm (a, b, c, d) 0 : Fin (m 0)) : ℕ) = a := rfl
  have e1 : (((ixEquiv m).symm (a, b, c, d) 1 : Fin (m 1)) : ℕ) = b := rfl
  have e2 : (((ixEquiv m).symm (a, b, c, d) 2 : Fin (m 2)) : ℕ) = c := rfl
  have e3 : (((ixEquiv m).symm (a, b, c, d) 3 : Fin (m 3)) : ℕ) = d := rfl
  have e4 : flatIx m ((ixEquiv m).symm (a, b, c, d)) = flat4 (m 1) (m 2) (m 3) a b c d := rfl
  rw [e0, e1, e2, e3, e4]
  ring

end QVCheck
