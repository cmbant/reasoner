module

public import Mathlib
public import FormalResearch.FourQubitEntropy.GOProbe.PolySound

/-!
# GO glue: graded rational polynomials and matrices of them (computable, with soundness)

`PQ d` is a rational polynomial of total degree `≤ d` in the 19 slice coordinates: a denominator `den > 0`
and a sparse integer polynomial `p` (packed keys, `GOProbe/Poly.lean`) with `Dg d p`; its value at `x : ℕ → ℝ` is
`ev x p / den` (`PQ.val`).  The operations `add`, `mul`, `smul`, `sumF` are ordinary computable list
functions (so a `native_decide` can run them) and `PQ.val` is a ring homomorphism for them (`val_add`,
`val_mul`, ...), which is what lets the slice-side real expressions of `PaperEGoSlice` be transcribed and
compared with the generated certificate data by a decidable equality of sorted sparse polynomials.
Matrices are `Fin m → Fin n → PQ d` (`pmul`, `padd`, ...), related to real matrices by `Rel`.
Claim class: proved.
-/

@[expose] public section


open Finset
open scoped Matrix

namespace FormalResearch.FourQubitEntropy.GOProbe

structure PQ (d : ℕ) where
  den : ℕ
  p : SP
  hden : 0 < den
  hp : Dg d p

namespace PQ

noncomputable def val (x : ℕ → ℝ) {d : ℕ} (a : PQ d) : ℝ := ev x a.p / a.den

def zero {d : ℕ} : PQ d := ⟨1, [], Nat.one_pos, Dg_nil d⟩

instance {d : ℕ} : Inhabited (PQ d) := ⟨zero⟩

theorem dsum_zero : dsum 0 = 0 := by decide

theorem evK_zero (x : ℕ → ℝ) : evK x 0 = 1 := by
  unfold evK
  exact Finset.prod_eq_one fun i _ => by simp [dig]

theorem dsum_pow (i : ℕ) (hi : i < 19) : dsum (256 ^ i) = 1 := by
  rw [dsum_eq]
  have h1 : (256 : ℕ) ^ i = 1 * 256 ^ i := (one_mul _).symm
  have : ∀ j, dig j (256 ^ i) = if j = i then 1 else 0 := fun j => by
    rw [h1]; exact dig_shift 1 i j (by norm_num)
  simp [this, Finset.sum_ite_eq', hi]

theorem evK_pow (x : ℕ → ℝ) (i : ℕ) (hi : i < 19) : evK x (256 ^ i) = x i := by
  have h1 : (256 : ℕ) ^ i = 1 * 256 ^ i := (one_mul _).symm
  have : ∀ j, dig j (256 ^ i) = if j = i then 1 else 0 := fun j => by
    rw [h1]; exact dig_shift 1 i j (by norm_num)
  unfold evK
  simp [this, Finset.prod_ite_eq', hi]

/-- The coordinate `x_i`. -/
def var (i : ℕ) (hi : i < 19) : PQ 1 :=
  ⟨1, [(256 ^ i, 1)], Nat.one_pos, by
    intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    exact (dsum_pow i hi).le⟩

/-- The rational constant `q`. -/
def ofRat {d : ℕ} (q : ℚ) : PQ d :=
  ⟨q.den, if q.num = 0 then [] else [(0, q.num)], q.den_pos, by
    intro t ht
    split_ifs at ht with h
    · simp at ht
    · simp only [List.mem_singleton] at ht
      subst ht
      rw [dsum_zero]; exact Nat.zero_le _⟩

def lift {d d' : ℕ} (h : d ≤ d') (a : PQ d) : PQ d' := ⟨a.den, a.p, a.hden, Dg_mono h a.hp⟩

/-- Multiplication by the rational constant `q`. -/
def smul {d : ℕ} (q : ℚ) (a : PQ d) : PQ d :=
  ⟨q.den * a.den, scaleSP q.num a.p, Nat.mul_pos q.den_pos a.hden, Dg_scaleSP _ a.hp⟩

def add {d : ℕ} (a b : PQ d) : PQ d :=
  ⟨Nat.lcm a.den b.den,
    addSP (scaleSP ((Nat.lcm a.den b.den / a.den : ℕ) : ℤ) a.p)
      (scaleSP ((Nat.lcm a.den b.den / b.den : ℕ) : ℤ) b.p),
    Nat.lcm_pos a.hden b.hden,
    Dg_addSP (Dg_scaleSP _ a.hp) (Dg_scaleSP _ b.hp)⟩

def neg {d : ℕ} (a : PQ d) : PQ d := smul (-1) a

def sub {d : ℕ} (a b : PQ d) : PQ d := add a (neg b)

def mul {d1 d2 : ℕ} (a : PQ d1) (b : PQ d2) (h : d1 + d2 ≤ 255 := by norm_num) : PQ (d1 + d2) :=
  ⟨a.den * b.den, mulSP a.p b.p, Nat.mul_pos a.hden b.hden, Dg_mulSP a.hp b.hp h⟩

def sumF {d n : ℕ} (f : Fin n → PQ d) : PQ d := (List.ofFn f).foldr add zero

/-! ### Values -/

@[simp] theorem val_zero (x : ℕ → ℝ) {d : ℕ} : (zero : PQ d).val x = 0 := by simp [val, zero]

theorem val_var (x : ℕ → ℝ) (i : ℕ) (hi : i < 19) : (var i hi).val x = x i := by
  simp [val, var, ev_cons, evK_pow x i hi]

theorem val_ofRat (x : ℕ → ℝ) {d : ℕ} (q : ℚ) : (ofRat q : PQ d).val x = (q : ℝ) := by
  unfold val ofRat
  by_cases h : q.num = 0
  · simp only [h, ite_true, ev_nil]
    have : q = 0 := Rat.zero_of_num_zero h
    simp [this]
  · simp only [h, ite_false, ev_cons, ev_nil, evK_zero]
    have hq : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by
      exact_mod_cast (Rat.num_div_den q).symm
    rw [hq]; simp

theorem val_lift (x : ℕ → ℝ) {d d' : ℕ} (h : d ≤ d') (a : PQ d) : (lift h a).val x = a.val x := rfl

theorem val_smul (x : ℕ → ℝ) {d : ℕ} (q : ℚ) (a : PQ d) : (smul q a).val x = (q : ℝ) * a.val x := by
  have hd : (a.den : ℝ) ≠ 0 := by exact_mod_cast a.hden.ne'
  have hq : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_pos.ne'
  have h : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by exact_mod_cast (Rat.num_div_den q).symm
  unfold val smul
  simp only [ev_scaleSP]
  rw [h]; push_cast; field_simp

theorem val_add (x : ℕ → ℝ) {d : ℕ} (a b : PQ d) : (add a b).val x = a.val x + b.val x := by
  have h1 : ((Nat.lcm a.den b.den / a.den : ℕ) : ℝ) * a.den = (Nat.lcm a.den b.den : ℕ) := by
    exact_mod_cast Nat.div_mul_cancel (Nat.dvd_lcm_left a.den b.den)
  have h2 : ((Nat.lcm a.den b.den / b.den : ℕ) : ℝ) * b.den = (Nat.lcm a.den b.den : ℕ) := by
    exact_mod_cast Nat.div_mul_cancel (Nat.dvd_lcm_right a.den b.den)
  have hL : (Nat.lcm a.den b.den : ℝ) ≠ 0 := by exact_mod_cast (Nat.lcm_pos a.hden b.hden).ne'
  have ha : (a.den : ℝ) ≠ 0 := by exact_mod_cast a.hden.ne'
  have hb : (b.den : ℝ) ≠ 0 := by exact_mod_cast b.hden.ne'
  have e1 : ((Nat.lcm a.den b.den / a.den : ℕ) : ℝ) = (Nat.lcm a.den b.den : ℕ) / a.den := by
    rw [eq_div_iff ha]; exact h1
  have e2 : ((Nat.lcm a.den b.den / b.den : ℕ) : ℝ) = (Nat.lcm a.den b.den : ℕ) / b.den := by
    rw [eq_div_iff hb]; exact h2
  unfold val add
  simp only [ev_addSP, ev_scaleSP, Int.cast_natCast]
  rw [e1, e2]
  field_simp

theorem val_neg (x : ℕ → ℝ) {d : ℕ} (a : PQ d) : (neg a).val x = -a.val x := by
  unfold neg; rw [val_smul]; simp

theorem val_sub (x : ℕ → ℝ) {d : ℕ} (a b : PQ d) : (sub a b).val x = a.val x - b.val x := by
  unfold sub; rw [val_add, val_neg]; ring

theorem val_mul (x : ℕ → ℝ) {d1 d2 : ℕ} (a : PQ d1) (b : PQ d2) (h : d1 + d2 ≤ 255) :
    (mul a b h).val x = a.val x * b.val x := by
  have ha : (a.den : ℝ) ≠ 0 := by exact_mod_cast a.hden.ne'
  have hb : (b.den : ℝ) ≠ 0 := by exact_mod_cast b.hden.ne'
  unfold val mul
  rw [ev_mulSP x a.hp b.hp h]
  push_cast
  field_simp

theorem val_sumF (x : ℕ → ℝ) {d : ℕ} : ∀ {n : ℕ} (f : Fin n → PQ d),
    (sumF f).val x = ∑ i, (f i).val x
  | 0, f => by simp [sumF]
  | n + 1, f => by
    unfold sumF at *
    rw [List.ofFn_succ, List.foldr_cons, val_add, Fin.sum_univ_succ]
    have := val_sumF x (fun i : Fin n => f i.succ)
    unfold sumF at this
    rw [this]

/-! ### Matrices -/

abbrev PM (d m n : ℕ) := Fin m → Fin n → PQ d

/-- `A` evaluates entrywise to the real matrix `M`. -/
def Rel (x : ℕ → ℝ) {d m n : ℕ} (A : PM d m n) (M : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ i j, (A i j).val x = M i j

def pmul {d1 d2 m k n : ℕ} (A : PM d1 m k) (B : PM d2 k n) (h : d1 + d2 ≤ 255 := by norm_num) :
    PM (d1 + d2) m n := fun i j => sumF fun l => mul (A i l) (B l j) h

def padd {d m n : ℕ} (A B : PM d m n) : PM d m n := fun i j => add (A i j) (B i j)
def psub {d m n : ℕ} (A B : PM d m n) : PM d m n := fun i j => sub (A i j) (B i j)
def psmul {d m n : ℕ} (q : ℚ) (A : PM d m n) : PM d m n := fun i j => smul q (A i j)
def ptrans {d m n : ℕ} (A : PM d m n) : PM d n m := fun i j => A j i

/-- The trace of a square matrix. -/
def ptr {d n : ℕ} (A : PM d n n) : PQ d := sumF fun i => A i i

/-- Squared Frobenius norm. -/
def pfn {d m n : ℕ} (A : PM d m n) (h : d + d ≤ 255 := by norm_num) : PQ (d + d) :=
  sumF fun i => sumF fun j => mul (A i j) (A i j) h

/-- Materialise the entries (computed once, shared by later uses). -/
def tab {d m n : ℕ} (A : PM d m n) : PM d m n :=
  let t : List (List (PQ d)) := List.ofFn fun i => List.ofFn fun j => A i j
  fun i j => (t.getD i []).getD j zero

theorem tab_apply {d m n : ℕ} (A : PM d m n) (i : Fin m) (j : Fin n) : tab A i j = A i j := by
  unfold tab
  simp [List.getD_eq_getElem?_getD]

theorem Rel.tab {x : ℕ → ℝ} {d m n : ℕ} {A : PM d m n} {M : Matrix (Fin m) (Fin n) ℝ} (h : Rel x A M) :
    Rel x (tab A) M := fun i j => by rw [tab_apply]; exact h i j

theorem Rel.mul {x : ℕ → ℝ} {d1 d2 m k n : ℕ} {A : PM d1 m k} {B : PM d2 k n}
    {M : Matrix (Fin m) (Fin k) ℝ} {N : Matrix (Fin k) (Fin n) ℝ} (hA : Rel x A M) (hB : Rel x B N)
    (h : d1 + d2 ≤ 255 := by norm_num) : Rel x (pmul A B h) (M * N) := fun i j => by
  simp only [pmul, val_sumF, val_mul, Matrix.mul_apply, hA _ _, hB _ _]

theorem Rel.add {x : ℕ → ℝ} {d m n : ℕ} {A B : PM d m n} {M N : Matrix (Fin m) (Fin n) ℝ}
    (hA : Rel x A M) (hB : Rel x B N) : Rel x (padd A B) (M + N) := fun i j => by
  simp only [padd, val_add, Matrix.add_apply, hA _ _, hB _ _]

theorem Rel.sub {x : ℕ → ℝ} {d m n : ℕ} {A B : PM d m n} {M N : Matrix (Fin m) (Fin n) ℝ}
    (hA : Rel x A M) (hB : Rel x B N) : Rel x (psub A B) (M - N) := fun i j => by
  simp only [psub, val_sub, Matrix.sub_apply, hA _ _, hB _ _]

theorem Rel.smul {x : ℕ → ℝ} {d m n : ℕ} {A : PM d m n} {M : Matrix (Fin m) (Fin n) ℝ} (q : ℚ)
    (hA : Rel x A M) : Rel x (psmul q A) ((q : ℝ) • M) := fun i j => by
  simp only [psmul, val_smul, Matrix.smul_apply, hA _ _, smul_eq_mul]

theorem Rel.trans {x : ℕ → ℝ} {d m n : ℕ} {A : PM d m n} {M : Matrix (Fin m) (Fin n) ℝ}
    (hA : Rel x A M) : Rel x (ptrans A) Mᵀ := fun i j => by
  simp only [ptrans, Matrix.transpose_apply, hA _ _]

/-- Scalar times matrix. -/
def pscal {d1 d2 m n : ℕ} (s : PQ d1) (A : PM d2 m n) (h : d1 + d2 ≤ 255 := by norm_num) :
    PM (d1 + d2) m n := fun i j => mul s (A i j) h

theorem Rel.scal {x : ℕ → ℝ} {d1 d2 m n : ℕ} {s : PQ d1} {A : PM d2 m n}
    {M : Matrix (Fin m) (Fin n) ℝ} (hA : Rel x A M) (h : d1 + d2 ≤ 255 := by norm_num) :
    Rel x (pscal s A h) (s.val x • M) := fun i j => by
  simp only [pscal, val_mul, Matrix.smul_apply, hA _ _, smul_eq_mul]

theorem val_ptr {x : ℕ → ℝ} {d n : ℕ} {A : PM d n n} {M : Matrix (Fin n) (Fin n) ℝ} (hA : Rel x A M) :
    (ptr A).val x = Matrix.trace M := by
  simp only [ptr, val_sumF, Matrix.trace, Matrix.diag_apply, hA _ _]

theorem val_pfn {x : ℕ → ℝ} {d m n : ℕ} {A : PM d m n} {M : Matrix (Fin m) (Fin n) ℝ} (hA : Rel x A M)
    (h : d + d ≤ 255) : (pfn A h).val x = ∑ i, ∑ j, M i j ^ 2 := by
  simp only [pfn, val_sumF, val_mul, hA _ _, sq]

end PQ

end FormalResearch.FourQubitEntropy.GOProbe
