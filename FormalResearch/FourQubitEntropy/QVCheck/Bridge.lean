import FormalResearch.FourQubitEntropy.QVCert.Reduction
import FormalResearch.FourQubitEntropy.QVCheck.Placement
import FormalResearch.FourQubitEntropy.QVCheck.Sector
import FormalResearch.FourQubitEntropy.QVFrame.Assembly
import FormalResearch.FourQubitEntropy.QVFrame.Defect

/-!
# Bridge to the `QVCert` blocks

The checker handles `BlockD`/`RhsTerm` arrays; this module identifies them with the blocks `QVCert.blk k` and the
right-hand-side permutations of `QVFrame.Defect` (`blocksQ`, `rhsTermsQ`, `wordOf`), and assembles the families
`Xk`, `Xhk` of the block calculus (`Xsum`: `∑ κ ⊗_q Xk κ q = K`).
-/

open Finset FormalResearch.FourQubitEntropy FormalResearch.FourQubitEntropy.QVBlock FormalResearch.FourQubitEntropy.QVFrame
open scoped Matrix

namespace QVCheck

/-!
## The blocks `QVCert.blk k` as checker data
-/

/-- the spin index `n / 2` as an element of `Spin = Fin 4` -/
def spOfNat (n : ℕ) : Spin := ⟨(n / 2) % 4, Nat.mod_lt _ (by norm_num)⟩

/-- the spins of a checker block -/
def spf (b : BlockD) : Fin 4 → Spin := fun r => spOfNat (b.2.1.getD r.val 0)

/-- a `QVCert` block as checker data -/
def toBlockD (b : QVCert.Block) : BlockD := (b.a, (List.finRange 4).map b.spins, b.weights, b.vecs)

/-- the blocks handed to the checker -/
def blocksQ : List BlockD := (List.finRange 14).map fun k => toBlockD (QVCert.blk k)

theorem blk_spins_le : ∀ k : Fin 14, ∀ r : Fin 4, (QVCert.blk k).spins r ≤ 6 ∧ (QVCert.blk k).spins r % 2 = 0 := by
  decide +kernel

theorem blk_vecs_length : ∀ k : Fin 14, (QVCert.blk k).vecs.length = (QVCert.blk k).weights.length := by
  decide +kernel

theorem mult_bridge (j : Spin) : QVCert.mult (2 * j.val) = multF j := by
  obtain ⟨j, hj⟩ := j
  interval_cases j <;> rfl

theorem blkSp_toBlockD (b : QVCert.Block) (r : Fin 4) :
    (blkSp (toBlockD b)).getD r.val 0 = b.spins r / 2 := by
  unfold blkSp toBlockD
  simp [Array.getD, List.getElem_map, List.getElem_finRange]

theorem spf_toBlockD (b : QVCert.Block) (hb : ∀ r : Fin 4, b.spins r ≤ 6) (r : Fin 4) :
    (spf (toBlockD b) r).val = b.spins r / 2 := by
  unfold spf spOfNat toBlockD
  simp only
  have : ((List.finRange 4).map b.spins).getD r.val 0 = b.spins r := by
    simp [List.getD_eq_getElem?_getD]
  rw [this]
  have := hb r
  omega

theorem two_mul_spf (b : QVCert.Block) (hb : ∀ r : Fin 4, b.spins r ≤ 6 ∧ b.spins r % 2 = 0) (r : Fin 4) :
    2 * (spf (toBlockD b) r).val = b.spins r := by
  rw [spf_toBlockD b (fun r => (hb r).1) r]
  have := hb r
  omega

/-- the digit function of the checker is that of `QVCert` -/
theorem muDig_eq (spA : Array ℕ) (p' : Fin 4 → ℕ) (hs : ∀ r : Fin 4, mult (spA.getD r.val 0) = QVCert.mult (p' r))
    (c : ℕ) (r : Fin 4) : muDig spA c r.val = QVCert.muDigit p' c r := by
  have h0 : mult (spA[0]?.getD 0) = QVCert.mult (p' 0) := by simpa [Array.getD_eq_getD_getElem?] using hs 0
  have h1 : mult (spA[1]?.getD 0) = QVCert.mult (p' 1) := by simpa [Array.getD_eq_getD_getElem?] using hs 1
  have h2 : mult (spA[2]?.getD 0) = QVCert.mult (p' 2) := by simpa [Array.getD_eq_getD_getElem?] using hs 2
  have h3 : mult (spA[3]?.getD 0) = QVCert.mult (p' 3) := by simpa [Array.getD_eq_getD_getElem?] using hs 3
  have e0 : (Finset.univ.filter (fun l : Fin 4 => (0 : Fin 4) < l)) = {1, 2, 3} := by decide
  have e1 : (Finset.univ.filter (fun l : Fin 4 => (1 : Fin 4) < l)) = {2, 3} := by decide
  have e2 : (Finset.univ.filter (fun l : Fin 4 => (2 : Fin 4) < l)) = {3} := by decide
  have e3 : (Finset.univ.filter (fun l : Fin 4 => (3 : Fin 4) < l)) = ∅ := by decide
  unfold QVCert.muDigit muDig
  fin_cases r
  · simp only [Fin.zero_eta, e0]
    simp [List.range, List.range.loop, h0, h1, h2, h3, Nat.mul_assoc]
  · simp only [Fin.mk_one, e1]
    simp [List.range, List.range.loop, h1, h2, h3]
  · simp only [Fin.reduceFinMk, e2]
    simp [List.range, List.range.loop, h2, h3]
  · simp only [Fin.reduceFinMk, e3]
    simp [List.range, List.range.loop, h3]

/-!
## Words for the right-hand side permutations
-/

def bubbleStep (st : List ℕ × List (Fin 5)) (i : Fin 5) : List ℕ × List (Fin 5) :=
  if st.1.getD (i.val + 1) 0 < st.1.getD i.val 0 then
    ((st.1.set i.val (st.1.getD (i.val + 1) 0)).set (i.val + 1) (st.1.getD i.val 0), i :: st.2)
  else st

def bubblePass (st : List ℕ × List (Fin 5)) : List ℕ × List (Fin 5) := (List.finRange 5).foldl bubbleStep st

/-- a word in the adjacent transpositions for the permutation with image list `l` (bubble sort) -/
def bubbleWord (l : List ℕ) : List (Fin 5) := ((List.range 6).foldl (fun st _ => bubblePass st) (l, [])).2

def wordOf (π : Equiv.Perm (Fin 6)) : List (Fin 5) := bubbleWord ((List.finRange 6).map fun t => (π t).val)

theorem wordOf_spec : ∀ i : RhsIdx, ∀ q : Fin 4, ((wordOf (rhsPerm i q)).map gens).prod = rhsPerm i q := by
  decide +kernel

def rhsIdxList : List RhsIdx :=
  (List.finRange 7).flatMap fun a => (List.finRange 3).flatMap fun b => (List.finRange 3).map fun c => (a, b, c)

/-- the right-hand-side term of an index: coefficient and one word per qubit -/
def rhsTermOf (i : RhsIdx) : RhsTerm :=
  (rhsCoef i, ((List.finRange 4).map fun q => (wordOf (rhsPerm i q)).map Fin.val).toArray)

/-- the terms handed to the checker -/
def rhsTermsQ : Array RhsTerm := (rhsIdxList.map rhsTermOf).toArray

theorem sum_flatMap_map {α β : Type*} (L : List α) (g : α → List β) (h : β → ℤ) :
    ((L.flatMap g).map h).sum = (L.map fun a => ((g a).map h).sum).sum := by
  induction L with
  | nil => simp
  | cons a t ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

theorem sum_rhsIdxList (h : RhsIdx → ℤ) : (rhsIdxList.map h).sum = ∑ i : RhsIdx, h i := by
  rw [Fintype.sum_prod_type, Fin.sum_univ_def]
  unfold rhsIdxList
  rw [sum_flatMap_map]
  refine congrArg List.sum (List.map_congr_left fun a _ => ?_)
  rw [Fintype.sum_prod_type, Fin.sum_univ_def, sum_flatMap_map]
  refine congrArg List.sum (List.map_congr_left fun b _ => ?_)
  rw [Fin.sum_univ_def, List.map_map]
  rfl

theorem slotPermZ_apply (π : Equiv.Perm (Fin 6)) (a c : Wd 6) :
    (slotPerm ℤ π : Matrix (Wd 6) (Wd 6) ℤ) a c = if a = slotAct π c then 1 else 0 := rfl

theorem slotPermZ_mul (π τ : Equiv.Perm (Fin 6)) :
    (slotPerm ℤ (π * τ) : Matrix (Wd 6) (Wd 6) ℤ) = (slotPerm ℤ π * slotPerm ℤ τ : Matrix (Wd 6) (Wd 6) ℤ) := by
  ext a c
  simp only [slotPermZ_apply, Matrix.mul_apply]
  rw [Finset.sum_eq_single (slotAct τ c)]
  · have : slotAct (π * τ) c = slotAct π (slotAct τ c) := rfl
    simp [this]
  · intro b _ hb
    simp [hb]
  · simp

theorem slotPermZ_one : (slotPerm ℤ (1 : Equiv.Perm (Fin 6)) : Matrix (Wd 6) (Wd 6) ℤ) = 1 := by
  ext a c
  have h : slotAct (1 : Equiv.Perm (Fin 6)) c = c := rfl
  simp [slotPermZ_apply, h, Matrix.one_apply]

theorem blk_word (hS : checkSlots () = true) (l : List (Fin 5)) :
    Cmat * (slotPerm ℤ ((l.map gens).prod) : Matrix (Wd 6) (Wd 6) ℤ) =
      blk dimF ((l.map fun i => (fun j => rho0 i j : ∀ j : Spin, Matrix (Fin (multF j)) (Fin (multF j)) ℤ)).prod) * Cmat := by
  induction l with
  | nil =>
    simp only [List.map_nil, List.prod_nil]
    rw [slotPermZ_one, blk_one, Matrix.mul_one, Matrix.one_mul]
  | cons i t ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [slotPermZ_mul, ← Matrix.mul_assoc, hrho0_of_check hS i, Matrix.mul_assoc, ih, ← Matrix.mul_assoc,
      ← blk_mul]

theorem blk_word_apply (l : List (Fin 5)) (j : Spin) :
    ((l.map fun i => (fun j => rho0 i j : ∀ j : Spin, Matrix (Fin (multF j)) (Fin (multF j)) ℤ)).prod) j =
      (l.map fun i => rho0 i j).prod := by
  rw [Pi.list_prod_apply, List.map_map]
  rfl

theorem rhsKron_term (p : Fin 4 → Spin) (i : RhsIdx) :
    rhsKron p (rhsTermOf i) = kronPi (fun q => ((wordOf (rhsPerm i q)).map fun n => rho0 n (p q)).prod) := by
  unfold rhsKron
  refine congrArg kronPi (funext fun q => ?_)
  have : (rhsTermOf i).2.getD q.val [] = (wordOf (rhsPerm i q)).map Fin.val := by
    unfold rhsTermOf
    simp [Array.getD]
  rw [this, ofMat_repProd]

theorem rhs_sum (p : Fin 4 → Spin) (A B : ℕ) :
    ∑ ti ∈ range rhsTermsQ.size, (rhsTermsQ.getD ti default).1 * bilN p (rhsKron p (rhsTermsQ.getD ti default)) A B =
      ∑ i : RhsIdx, rhsCoef i * bilN p (kronPi (fun q => ((wordOf (rhsPerm i q)).map fun n => rho0 n (p q)).prod)) A B := by
  unfold rhsTermsQ
  rw [arr_sum rhsIdxList rhsTermOf (fun t => t.1 * bilN p (rhsKron p t) A B) default, sum_rhsIdxList]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [rhsKron_term]
  rfl

/-!
## Assembly of the checker semantics with the block calculus
-/

abbrev Bk (k : Fin 14) : QVCert.Block := QVCert.blk k

/-- absorb a coefficient into qubit `0` -/
def absorb {α : Type*} [SMul ℤ α] (c : ℤ) (f : Fin 4 → α) : Fin 4 → α := fun q => if q = 0 then c • f q else f q

theorem kronPi_absorb {m n : Fin 4 → Type*} [∀ q, Fintype (m q)] [∀ q, Fintype (n q)] (c : ℤ)
    (M : ∀ q, Matrix (m q) (n q) ℤ) :
    kronPi (fun q => if q = 0 then c • M q else M q) = c • kronPi M := by
  ext a b
  simp only [kronPi_apply, Matrix.smul_apply, smul_eq_mul, Fin.prod_univ_four]
  simp
  ring

theorem blk_smulZ (c : ℤ) (X : ∀ j : Spin, Matrix (Fin (multF j)) (Fin (multF j)) ℤ) :
    blk dimF (fun j => c • X j) = c • blk dimF X := by
  ext ⟨j, k, μ⟩ ⟨j', k', μ'⟩
  by_cases h : j = j'
  · subst h
    simp only [blk_same, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  · simp [blk_ne dimF _ h]

theorem blk_a_mem : ∀ k : Fin 14, (Bk k).a ∈ ({3, 4} : Finset ℕ) := by decide +kernel

/-- the spins of a block as elements of `Spin` -/
def spB (k : Fin 14) : Fin 4 → Spin := spf (toBlockD (Bk k))

theorem two_mul_spB (k : Fin 14) (q : Fin 4) : 2 * (spB k q).val = (Bk k).spins q :=
  two_mul_spf _ (blk_spins_le k) q

theorem mult_spB (k : Fin 14) (q : Fin 4) : QVCert.mult ((Bk k).spins q) = multF (spB k q) := by
  rw [← two_mul_spB, mult_bridge]

abbrev vlen (k : Fin 14) (i : ℕ) : ℕ := ((Bk k).vecs.getD i []).length

/-- the certificate part of the index set: block, covariant, qubit permutation, entries of the multiplicity vector -/
abbrev CertIdx : Type :=
  Σ k : Fin 14, Σ i : Fin (Bk k).weights.length, Equiv.Perm (Fin 4) × Fin (vlen k i.val) × Fin (vlen k i.val)

abbrev KIdx : Type := RhsIdx ⊕ CertIdx

def ent (k : Fin 14) (i : ℕ) (s : Fin (vlen k i)) : ℕ × ℤ := ((Bk k).vecs.getD i []).get s

def ccf (k : Fin 14) (i : ℕ) (s s' : Fin (vlen k i)) : ℤ := (Bk k).q i * ((ent k i s).2 * (ent k i s').2)

/-- the per-qubit factor of a certificate term (frame-6 operator) -/
def Tm (k : Fin 14) (i : ℕ) (σ : Equiv.Perm (Fin 4)) (s s' : Fin (vlen k i)) (q : Fin 4) : Matrix (Wd 6) (Wd 6) ℤ :=
  tau (Bk k).a (Eop ((Bk k).spins (σ.symm q)) (QVCert.muDigit (Bk k).spins (ent k i s).1 (σ.symm q))
    (QVCert.muDigit (Bk k).spins (ent k i s').1 (σ.symm q)))

/-- its block data -/
def Th (k : Fin 14) (i : ℕ) (σ : Equiv.Perm (Fin 4)) (s s' : Fin (vlen k i)) (q : Fin 4) (j : Spin) :
    Matrix (Fin (multF j)) (Fin (multF j)) ℤ :=
  psiMat (Bk k).a (spB k (σ.symm q)) j (QVCert.muDigit (Bk k).spins (ent k i s).1 (σ.symm q))
    (QVCert.muDigit (Bk k).spins (ent k i s').1 (σ.symm q))

def Xk : KIdx → Fin 4 → Matrix (Wd 6) (Wd 6) ℤ
  | .inl i => absorb (2 * QVCert.certD * rhsCoef i) fun q => (slotPerm ℤ (rhsPerm i q) : Matrix (Wd 6) (Wd 6) ℤ)
  | .inr ⟨k, i, σ, s, s'⟩ => absorb (-ccf k i.val s s') fun q => Tm k i.val σ s s' q

def Xhk : KIdx → Fin 4 → ∀ j : Spin, Matrix (Fin (multF j)) (Fin (multF j)) ℤ
  | .inl i => absorb (2 * QVCert.certD * rhsCoef i) fun q j => ((wordOf (rhsPerm i q)).map fun n => rho0 n j).prod
  | .inr ⟨k, i, σ, s, s'⟩ => absorb (-ccf k i.val s s') fun q j => Th k i.val σ s s' q j

theorem hX_absorb (c : ℤ) (M : Fin 4 → Matrix (Wd 6) (Wd 6) ℤ)
    (Mh : Fin 4 → ∀ j : Spin, Matrix (Fin (multF j)) (Fin (multF j)) ℤ)
    (h : ∀ q, Cmat * M q = blk dimF (Mh q) * Cmat) (q : Fin 4) :
    Cmat * absorb c M q = blk dimF (absorb c Mh q) * Cmat := by
  unfold absorb
  by_cases hq : q = 0
  · simp only [hq, ite_true]
    rw [Matrix.mul_smul, h, ← Matrix.smul_mul]
    congr 1
    exact (blk_smulZ c (Mh 0)).symm
  · simp only [hq, ite_false]
    exact h q

theorem muDigit_lt (k : Fin 14) (c : ℕ) (r : Fin 4) : QVCert.muDigit (Bk k).spins c r < multF (spB k r) := by
  rw [← mult_spB]
  unfold QVCert.muDigit
  exact Nat.mod_lt _ (by rw [mult_spB]; exact multF_pos _)

theorem Xk_inl (i : RhsIdx) : Xk (.inl i) =
    absorb (2 * QVCert.certD * rhsCoef i) fun q => (slotPerm ℤ (rhsPerm i q) : Matrix (Wd 6) (Wd 6) ℤ) := rfl

theorem Xhk_inl (i : RhsIdx) : Xhk (.inl i) =
    absorb (2 * QVCert.certD * rhsCoef i) fun q j => ((wordOf (rhsPerm i q)).map fun n => rho0 n j).prod := rfl

theorem Xk_inr (k : Fin 14) (i : Fin (Bk k).weights.length) (σ : Equiv.Perm (Fin 4)) (s s' : Fin (vlen k i.val)) :
    Xk (.inr ⟨k, i, σ, s, s'⟩) = absorb (-ccf k i.val s s') fun q => Tm k i.val σ s s' q := rfl

theorem Xhk_inr (k : Fin 14) (i : Fin (Bk k).weights.length) (σ : Equiv.Perm (Fin 4)) (s s' : Fin (vlen k i.val)) :
    Xhk (.inr ⟨k, i, σ, s, s'⟩) = absorb (-ccf k i.val s s') fun q j => Th k i.val σ s s' q j := rfl

theorem hX_rhs (hS : checkSlots () = true) (i : RhsIdx) (q : Fin 4) :
    Cmat * (slotPerm ℤ (rhsPerm i q) : Matrix (Wd 6) (Wd 6) ℤ) =
      blk dimF (fun j => ((wordOf (rhsPerm i q)).map fun n => rho0 n j).prod) * Cmat := by
  have h := blk_word hS (wordOf (rhsPerm i q))
  rw [wordOf_spec i q] at h
  have e : (fun j : Spin => ((wordOf (rhsPerm i q)).map fun n => rho0 n j).prod) =
      ((wordOf (rhsPerm i q)).map fun n => (fun j : Spin => rho0 n j : ∀ j : Spin, Matrix (Fin (multF j)) (Fin (multF j)) ℤ)).prod :=
    funext fun j => (blk_word_apply (wordOf (rhsPerm i q)) j).symm
  rw [h, e]

theorem hX_cert (hP : checkPsi () = true) (k : Fin 14) (i : ℕ) (σ : Equiv.Perm (Fin 4)) (s s' : Fin (vlen k i))
    (q : Fin 4) : Cmat * Tm k i σ s s' q = blk dimF (fun j => Th k i σ s s' q j) * Cmat := by
  unfold Tm
  rw [← two_mul_spB k (σ.symm q)]
  exact hPsi_of_check hP _ (blk_a_mem k) (spB k (σ.symm q)) _ _ (muDigit_lt k _ _) (muDigit_lt k _ _)

theorem hXk (hS : checkSlots () = true) (hP : checkPsi () = true) (κ : KIdx) (q : Fin 4) :
    Cmat * Xk κ q = blk dimF (Xhk κ q) * Cmat := by
  rcases κ with i | ⟨k, i, σ, s, s'⟩
  · rw [Xk_inl, Xhk_inl]
    exact hX_absorb _ _ _ (hX_rhs hS i) q
  · rw [Xk_inr, Xhk_inr]
    exact hX_absorb _ _ _ (hX_cert hP k i.val σ s s') q

theorem lsum_eq_fin (v : List (ℕ × ℤ)) (f : ℕ × ℤ → Matrix (Cfg 6) (Cfg 6) ℤ) :
    lsum v f = ∑ s : Fin v.length, f (v.get s) := by
  unfold lsum
  rw [← Fin.sum_univ_fun_getElem]
  rfl

theorem cert_ki (k : Fin 14) (i : ℕ) :
    ∑ σ : Equiv.Perm (Fin 4), ∑ s : Fin (vlen k i), ∑ s' : Fin (vlen k i),
        (-ccf k i s s') • kronPi (fun q => Tm k i σ s s' q) =
      -((Bk k).q i • tauGram (Bk k).a (Bk k).spins ((Bk k).vecs.getD i [])) := by
  unfold tauGram
  rw [Finset.smul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [lsum_eq_fin, Finset.smul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [lsum_eq_fin, Finset.smul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun s' _ => ?_
  unfold ccf Tm ent
  rw [smul_smul, neg_smul]

theorem Xsum : ∑ κ : KIdx, kronPi (Xk κ) =
    Kfam (fun k : Fin 14 => Bk k) (fun k => (Bk k).weights.length) (fun k i => (Bk k).q i) QVCert.certD := by
  unfold Kfam certFam rhsOp
  rw [Fintype.sum_sum_type]
  have h1 : ∑ i : RhsIdx, kronPi (Xk (.inl i)) =
      (2 * QVCert.certD) • ∑ i : RhsIdx, rhsCoef i •
        kronPi (fun q => (slotPerm ℤ (rhsPerm i q) : Matrix (Wd 6) (Wd 6) ℤ)) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Xk_inl]
    unfold absorb
    rw [kronPi_absorb (m := fun _ => Wd 6) (n := fun _ => Wd 6) (2 * QVCert.certD * rhsCoef i)
      (fun q => (slotPerm ℤ (rhsPerm i q) : Matrix (Wd 6) (Wd 6) ℤ)), smul_smul]
  have h2 : ∑ c : CertIdx, kronPi (Xk (.inr c)) =
      -∑ k : Fin 14, ∑ i ∈ range (Bk k).weights.length, (Bk k).q i • tauGram (Bk k).a (Bk k).spins ((Bk k).vecs.getD i []) := by
    rw [Fintype.sum_sigma, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Fintype.sum_sigma, Finset.sum_range, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← cert_ki k i.val, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => ?_
    rw [Xk_inr]
    unfold absorb
    rw [kronPi_absorb (m := fun _ => Wd 6) (n := fun _ => Wd 6) (-ccf k i.val s s')
      (fun q => Tm k i.val σ s s' q)]
  rw [h1, h2, sub_eq_add_neg]

end QVCheck
