module

public import FormalResearch.FourQubitEntropy.QVCheck.Terms

/-!
# Placements (K5)

The 24 permutations `π` of the four qubits act on the sector bases (`checkPlacements`); `place_transfer` expresses the
placed bilinear form `bilPl` through the checker's `SW`, `SV` tables, and `bilN_kron_placed` its value on Kronecker
products.
-/

@[expose] public section


open Finset FormalResearch.FourQubitEntropy FormalResearch.FourQubitEntropy.QVBlock
open scoped Matrix

namespace QVCheck

/-!
## The 24 qubit permutations
-/

/-- the `pii`-th permutation of the checker as a function on `Fin 4` -/
def permSigma (pii : ℕ) : Fin 4 → Fin 4 := fun q => ⟨(perms4.getD pii #[]).getD q.val 0 % 4, Nat.mod_lt _ (by norm_num)⟩

theorem permSigma_bij : ∀ pii : Fin 24, Function.Bijective (permSigma pii.val) := by decide +kernel

theorem permSigma_inj : ∀ a b : Fin 24, permSigma a.val = permSigma b.val → a = b := by decide +kernel

theorem perms4_entry : ∀ pii : Fin 24, ∀ q : Fin 4,
    (perms4.getD pii.val #[]).getD q.val 0 < 4 ∧ (perms4.getD pii.val #[]).size = 4 := by decide +kernel

/-- the permutation of `Fin 4` -/
noncomputable def sg (pii : Fin 24) : Equiv.Perm (Fin 4) := Equiv.ofBijective (permSigma pii.val) (permSigma_bij pii)

theorem sg_apply (pii : Fin 24) (q : Fin 4) : (sg pii) q = permSigma pii.val q := rfl

theorem sg_inj : Function.Injective sg := by
  intro a b h
  apply permSigma_inj
  funext q
  exact congrArg (fun σ : Equiv.Perm (Fin 4) => σ q) h

theorem sg_bij : Function.Bijective sg := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨sg_inj, ?_⟩
  simp [Fintype.card_perm]; rfl

theorem sum_perm4 (F : Equiv.Perm (Fin 4) → ℤ) : ∑ σ : Equiv.Perm (Fin 4), F σ = ∑ pii : Fin 24, F (sg pii) := by
  exact (Fintype.sum_bijective sg sg_bij (fun pii => F (sg pii)) F (fun _ => rfl)).symm


/-- strides of the mixed-radix flattening -/
def strideM (m : Fin 4 → ℕ) : Fin 4 → ℕ := ![m 1 * m 2 * m 3, m 2 * m 3, m 3, 1]

theorem stride_pcode (p : Fin 4 → Spin) (q : Fin 4) : stride (pcode p) q.val = strideM (radix p) q := by
  obtain ⟨h0, h1, h2, h3⟩ := stride_eq (pcode p)
  have d0 : spinDigit (pcode p) 1 = (p 1).val := spinDigit_pcode p 1
  have d1 : spinDigit (pcode p) 2 = (p 2).val := spinDigit_pcode p 2
  have d2 : spinDigit (pcode p) 3 = (p 3).val := spinDigit_pcode p 3
  fin_cases q
  · simp only [strideM]; show stride (pcode p) 0 = _
    rw [h0, d0, d1, d2]; rfl
  · simp only [strideM]; show stride (pcode p) 1 = _
    rw [h1, d1, d2]; rfl
  · simp only [strideM]; show stride (pcode p) 2 = _
    rw [h2, d2]; rfl
  · simp only [strideM]; show stride (pcode p) 3 = _
    rw [h3]; rfl

theorem digit_lem (a r b m s : ℕ) (hr : r < m) (hb : b < s) : ((a * m + r) * s + b) / s % m = r := by
  have hs : 0 < s := by omega
  have : ((a * m + r) * s + b) / s = a * m + r := by
    rw [Nat.mul_comm (a * m + r) s, Nat.mul_add_div hs, Nat.div_eq_of_lt hb]; simp
  rw [this, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]

theorem flatIx_digit (m : Fin 4 → ℕ) (x : ∀ q : Fin 4, Fin (m q)) (q : Fin 4) :
    flatIx m x / strideM m q % m q = (x q).val := by
  have b0 := (x 0).2; have b1 := (x 1).2; have b2 := (x 2).2; have b3 := (x 3).2
  have hB0 : ((x 1).val * m 2 + (x 2).val) * m 3 + (x 3).val < m 1 * m 2 * m 3 := by
    have := flat4_lt (m0 := 1) (m1 := m 1) (m2 := m 2) (m3 := m 3) (a := 0) (b := (x 1).val) (c := (x 2).val)
      (d := (x 3).val) (by omega) b1 b2 b3
    unfold flat4 at this; simpa using this
  have hB1 : (x 2).val * m 3 + (x 3).val < m 2 * m 3 := by
    have := flat4_lt (m0 := 1) (m1 := 1) (m2 := m 2) (m3 := m 3) (a := 0) (b := 0) (c := (x 2).val)
      (d := (x 3).val) (by omega) (by have := (x 1).2; omega) b2 b3
    unfold flat4 at this; simpa using this
  rw [flatIx_eq]
  fin_cases q
  · simp only [strideM]
    show _ / (m 1 * m 2 * m 3) % m 0 = (x 0).val
    rw [show ((x 0).val * m 1 + (x 1).val) * (m 2 * m 3) + ((x 2).val * m 3 + (x 3).val) =
      (0 * m 0 + (x 0).val) * (m 1 * m 2 * m 3) + (((x 1).val * m 2 + (x 2).val) * m 3 + (x 3).val) by ring]
    exact digit_lem 0 (x 0).val _ (m 0) (m 1 * m 2 * m 3) b0 hB0
  · simp only [strideM]
    show _ / (m 2 * m 3) % m 1 = (x 1).val
    rw [show ((x 0).val * m 1 + (x 1).val) * (m 2 * m 3) + ((x 2).val * m 3 + (x 3).val) =
      ((x 0).val * m 1 + (x 1).val) * (m 2 * m 3) + ((x 2).val * m 3 + (x 3).val) from rfl]
    exact digit_lem (x 0).val (x 1).val _ (m 1) (m 2 * m 3) b1 hB1
  · simp only [strideM]
    show _ / m 3 % m 2 = (x 2).val
    rw [show ((x 0).val * m 1 + (x 1).val) * (m 2 * m 3) + ((x 2).val * m 3 + (x 3).val) =
      (((x 0).val * m 1 + (x 1).val) * m 2 + (x 2).val) * m 3 + (x 3).val by ring]
    exact digit_lem ((x 0).val * m 1 + (x 1).val) (x 2).val (x 3).val (m 2) (m 3) b2 b3
  · simp only [strideM]
    show _ / 1 % m 3 = (x 3).val
    rw [Nat.div_one]
    have : ((x 0).val * m 1 + (x 1).val) * (m 2 * m 3) + ((x 2).val * m 3 + (x 3).val) =
        ((((x 0).val * m 1 + (x 1).val) * m 2 + (x 2).val)) * m 3 + (x 3).val := by ring
    rw [this, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt b3]


theorem flatIx_sum (m : Fin 4 → ℕ) (x : ∀ q : Fin 4, Fin (m q)) :
    flatIx m x = ∑ q : Fin 4, (x q).val * strideM m q := by
  rw [flatIx_eq, Fin.sum_univ_four]
  simp only [strideM]
  simp
  ring

theorem placed_eq (p : Fin 4 → Spin) (pii : Fin 24) :
    placedCode (pcode p) (perms4.getD pii.val #[]) = pcode (fun r => p (sg pii r)) := by
  have e : ∀ q : Fin 4, spinDigit (pcode p) ((perms4.getD pii.val #[]).getD q.val 0) = (p (sg pii q)).val := by
    intro q
    have h1 := (perms4_entry pii q).1
    have : (perms4.getD pii.val #[]).getD q.val 0 = ((sg pii) q).val := by
      rw [sg_apply]; unfold permSigma; simp only; exact (Nat.mod_eq_of_lt h1).symm
    rw [this, spinDigit_pcode p (sg pii q)]
  have e0 : spinDigit (pcode p) ((perms4.getD pii.val #[]).getD 0 0) = (p (sg pii 0)).val := e 0
  have e1 : spinDigit (pcode p) ((perms4.getD pii.val #[]).getD 1 0) = (p (sg pii 1)).val := e 1
  have e2 : spinDigit (pcode p) ((perms4.getD pii.val #[]).getD 2 0) = (p (sg pii 2)).val := e 2
  have e3 : spinDigit (pcode p) ((perms4.getD pii.val #[]).getD 3 0) = (p (sg pii 3)).val := e 3
  unfold placedCode
  rw [e0, e1, e2, e3]
  rfl


theorem foldl_range4 (g : ℕ → ℕ) : (List.range 4).foldl (fun acc q => acc + g q) 0 = g 0 + g 1 + g 2 + g 3 := by
  have hr : List.range 4 = [0, 1, 2, 3] := rfl
  rw [hr]; simp [List.foldl]

theorem flat_perm (p : Fin 4 → Spin) (pii : Fin 24) (x : ∀ r : Fin 4, Fin (multF (p (sg pii r)))) :
    flatIx (radix p) (Equiv.piCongrLeft (fun q => Fin (multF (p q))) (sg pii) x) =
      permFlatIdx (pcode p) (perms4.getD pii.val #[]) (flatIx (radix (fun r => p (sg pii r))) x) := by
  unfold permFlatIdx
  rw [placed_eq p pii, foldl_range4]
  rw [flatIx_sum, ← Equiv.sum_comp (sg pii)]
  have hsum : ∀ g : ℕ → ℕ, g 0 + g 1 + g 2 + g 3 = ∑ q : Fin 4, g q.val := by
    intro g; rw [Fin.sum_univ_four]; rfl
  have key : ∀ q : Fin 4,
      (flatIx (radix (fun r => p (sg pii r))) x / stride (pcode (fun r => p (sg pii r))) q.val %
        mult (spinDigit (pcode (fun r => p (sg pii r))) q.val)) *
        stride (pcode p) ((perms4.getD pii.val #[]).getD q.val 0) =
      ((Equiv.piCongrLeft (fun q => Fin (multF (p q))) (sg pii) x) (sg pii q)).val * strideM (radix p) (sg pii q) := by
    intro q
    have hd := flatIx_digit (radix (fun r => p (sg pii r))) x q
    rw [stride_pcode, spinDigit_pcode]
    have hm : mult ((p (sg pii q)).val) = radix (fun r => p (sg pii r)) q := rfl
    rw [hm, hd]
    have h1 := (perms4_entry pii q).1
    have : (perms4.getD pii.val #[]).getD q.val 0 = ((sg pii) q).val := by
      rw [sg_apply]; unfold permSigma; simp only; exact (Nat.mod_eq_of_lt h1).symm
    rw [this, stride_pcode, Equiv.piCongrLeft_apply_apply]
  refine (Finset.sum_congr rfl fun q _ => (key q).symm).trans ?_
  exact (hsum (fun q => flatIx (radix (fun r => p (sg pii r))) x / stride (pcode (fun r => p (sg pii r))) q %
    mult (spinDigit (pcode (fun r => p (sg pii r))) q) * stride (pcode p) ((perms4.getD pii.val #[]).getD q 0))).symm

/-!
## The placement transfer (K5)
-/

theorem checkPlacements_spec (h : checkPlacements () = true) (p : Fin 4 → Spin) (pii : Fin 24)
    (hn : 0 < nn (pcode p)) :
    nn (pcode (fun r => p (sg pii r))) = nn (pcode p) ∧ pden (pcode p) pii.val ≠ 0 ∧
    ∀ a < nn (pcode p), ∀ f < sdim (pcode (fun r => p (sg pii r))),
      pden (pcode p) pii.val * vAt (pcode p) a (permFlatIdx (pcode p) (perms4.getD pii.val #[]) f) =
        ∑ a' ∈ range (nn (pcode p)), pSV (pcode p) pii.val a a' * vAt (pcode (fun r => p (sg pii r))) a' f ∧
      pden (pcode p) pii.val * wAt (pcode p) a (permFlatIdx (pcode p) (perms4.getD pii.val #[]) f) =
        ∑ a' ∈ range (nn (pcode p)), pSW (pcode p) pii.val a a' * wAt (pcode (fun r => p (sg pii r))) a' f := by
  unfold checkPlacements at h
  have h1 := (allTo_iff _ _).1 h (pcode p) (by rw [hide_eq]; exact pcode_lt p)
  have h2 := (allTo_iff _ _).1 h1 pii.val pii.2
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, bne_iff_ne, ne_eq] at h2
  rcases h2 with h2 | ⟨⟨hnn, hd⟩, hall⟩
  · omega
  rw [← placed_eq p pii]
  refine ⟨hnn, hd, fun a ha f hf => ?_⟩
  have h3 := (allTo_iff _ _).1 hall a ha
  have h4 := (allTo_iff _ _).1 h3 f (by simpa [placed_eq] using hf)
  simp only [Bool.and_eq_true, beq_iff_eq, sumTo_eq] at h4
  exact h4

/-- `bil` with natural-number basis indices -/
def bilN (p : Fin 4 → Spin) (M : Matrix (∀ q, Fin (multF (p q))) (∀ q, Fin (multF (p q))) ℤ) (A B : ℕ) : ℤ :=
  ∑ x : (∀ q, Fin (multF (p q))), ∑ y : (∀ q, Fin (multF (p q))),
    wAt (pcode p) A (flatIx (radix p) x) * M x y * vAt (pcode p) B (flatIx (radix p) y)

/-- the placed bilinear form: `W_A ∘ e`, `V_B ∘ e` on the sector `p ∘ σ` -/
def bilPl (p : Fin 4 → Spin) (σ : Equiv.Perm (Fin 4))
    (G : Matrix (∀ r, Fin (multF (p (σ r)))) (∀ r, Fin (multF (p (σ r)))) ℤ) (A B : ℕ) : ℤ :=
  ∑ x : (∀ r, Fin (multF (p (σ r)))), ∑ y : (∀ r, Fin (multF (p (σ r)))),
    wAt (pcode p) A (flatIx (radix p) (Equiv.piCongrLeft (fun q => Fin (multF (p q))) σ x)) * G x y *
      vAt (pcode p) B (flatIx (radix p) (Equiv.piCongrLeft (fun q => Fin (multF (p q))) σ y))

theorem expand_sums (S S' : Finset ℕ) (f : ℕ → ℤ) (g : ℤ) (h : ℕ → ℤ) :
    (∑ a ∈ S, f a) * g * (∑ b ∈ S', h b) = ∑ a ∈ S, ∑ b ∈ S', f a * g * h b := by
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]

theorem sum4_swap {α β γ δ : Type*} (s1 : Finset α) (s2 : Finset β) (s3 : Finset γ) (s4 : Finset δ)
    (f : α → β → γ → δ → ℤ) :
    ∑ x ∈ s1, ∑ y ∈ s2, ∑ a ∈ s3, ∑ b ∈ s4, f x y a b = ∑ a ∈ s3, ∑ b ∈ s4, ∑ x ∈ s1, ∑ y ∈ s2, f x y a b := by
  calc _ = ∑ x ∈ s1, ∑ a ∈ s3, ∑ y ∈ s2, ∑ b ∈ s4, f x y a b :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ a ∈ s3, ∑ x ∈ s1, ∑ y ∈ s2, ∑ b ∈ s4, f x y a b := Finset.sum_comm
    _ = ∑ a ∈ s3, ∑ x ∈ s1, ∑ b ∈ s4, ∑ y ∈ s2, f x y a b :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun a _ => Finset.sum_comm

theorem place_transfer (hP : checkPlacements () = true) (p : Fin 4 → Spin) (pii : Fin 24) (hn : 0 < nn (pcode p))
    (G : Matrix (∀ r, Fin (multF (p (sg pii r)))) (∀ r, Fin (multF (p (sg pii r)))) ℤ) (A B : ℕ)
    (hA : A < nn (pcode p)) (hB : B < nn (pcode p)) :
    pden (pcode p) pii.val ^ 2 * bilPl p (sg pii) G A B =
      ∑ A' ∈ range (nn (pcode p)), ∑ B' ∈ range (nn (pcode p)),
        pSW (pcode p) pii.val A A' * pSV (pcode p) pii.val B B' * bilN (fun r => p (sg pii r)) G A' B' := by
  obtain ⟨hnn, hd, hspec⟩ := checkPlacements_spec hP p pii hn
  have hW : ∀ x : (∀ r, Fin (multF (p (sg pii r)))),
      pden (pcode p) pii.val * wAt (pcode p) A (flatIx (radix p) (Equiv.piCongrLeft (fun q => Fin (multF (p q))) (sg pii) x)) =
        ∑ A' ∈ range (nn (pcode p)), pSW (pcode p) pii.val A A' *
          wAt (pcode (fun r => p (sg pii r))) A' (flatIx (radix (fun r => p (sg pii r))) x) := by
    intro x
    rw [flat_perm]
    exact (hspec A hA _ (by rw [sdim_pcode]; exact flatIx_lt _ x)).2
  have hV : ∀ x : (∀ r, Fin (multF (p (sg pii r)))),
      pden (pcode p) pii.val * vAt (pcode p) B (flatIx (radix p) (Equiv.piCongrLeft (fun q => Fin (multF (p q))) (sg pii) x)) =
        ∑ B' ∈ range (nn (pcode p)), pSV (pcode p) pii.val B B' *
          vAt (pcode (fun r => p (sg pii r))) B' (flatIx (radix (fun r => p (sg pii r))) x) := by
    intro x
    rw [flat_perm]
    exact (hspec B hB _ (by rw [sdim_pcode]; exact flatIx_lt _ x)).1
  unfold bilPl bilN
  have step : ∀ x y : (∀ r, Fin (multF (p (sg pii r)))),
      pden (pcode p) pii.val ^ 2 * (wAt (pcode p) A (flatIx (radix p) (Equiv.piCongrLeft (fun q => Fin (multF (p q))) (sg pii) x)) *
        G x y * vAt (pcode p) B (flatIx (radix p) (Equiv.piCongrLeft (fun q => Fin (multF (p q))) (sg pii) y))) =
      (∑ A' ∈ range (nn (pcode p)), pSW (pcode p) pii.val A A' *
          wAt (pcode (fun r => p (sg pii r))) A' (flatIx (radix (fun r => p (sg pii r))) x)) * G x y *
        (∑ B' ∈ range (nn (pcode p)), pSV (pcode p) pii.val B B' *
          vAt (pcode (fun r => p (sg pii r))) B' (flatIx (radix (fun r => p (sg pii r))) y)) := by
    intro x y
    rw [← hW x, ← hV y]; ring
  have hlhs : pden (pcode p) pii.val ^ 2 * ∑ x : (∀ r, Fin (multF (p (sg pii r)))), ∑ y : (∀ r, Fin (multF (p (sg pii r)))),
      wAt (pcode p) A (flatIx (radix p) (Equiv.piCongrLeft (fun q => Fin (multF (p q))) (sg pii) x)) * G x y *
        vAt (pcode p) B (flatIx (radix p) (Equiv.piCongrLeft (fun q => Fin (multF (p q))) (sg pii) y)) =
      ∑ x : (∀ r, Fin (multF (p (sg pii r)))), ∑ y : (∀ r, Fin (multF (p (sg pii r)))),
        ∑ A' ∈ range (nn (pcode p)), ∑ B' ∈ range (nn (pcode p)),
          pSW (pcode p) pii.val A A' * pSV (pcode p) pii.val B B' *
            (wAt (pcode (fun r => p (sg pii r))) A' (flatIx (radix (fun r => p (sg pii r))) x) * G x y *
              vAt (pcode (fun r => p (sg pii r))) B' (flatIx (radix (fun r => p (sg pii r))) y)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [step x y, expand_sums]
    refine Finset.sum_congr rfl fun A' _ => Finset.sum_congr rfl fun B' _ => ?_
    ring
  rw [hlhs, sum4_swap]
  refine Finset.sum_congr rfl fun A' _ => Finset.sum_congr rfl fun B' _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]

/-!
## Placed bilinear forms of Kronecker products
-/

/-- A Kronecker product in the sector `p` is the placed form of the permuted product in the sector `p ∘ σ`. -/
theorem bilN_kron_placed (p : Fin 4 → Spin) (σ : Equiv.Perm (Fin 4))
    (M : ∀ q, Matrix (Fin (multF (p q))) (Fin (multF (p q))) ℤ) (A B : ℕ) :
    bilN p (kronPi M) A B = bilPl p σ (kronPi (fun r => M (σ r))) A B := by
  unfold bilN bilPl
  let e := Equiv.piCongrLeft (fun q => Fin (multF (p q))) σ
  have hk : ∀ x y : (∀ r, Fin (multF (p (σ r)))), kronPi (fun r => M (σ r)) x y = kronPi M (e x) (e y) := by
    intro x y
    rw [kronPi_apply, kronPi_apply]
    rw [← Equiv.prod_comp σ (fun q => M q ((e x) q) ((e y) q))]
    refine Finset.prod_congr rfl fun r _ => ?_
    simp only [e, Equiv.piCongrLeft_apply_apply]
  rw [← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [hk]

theorem bilN_add (p : Fin 4 → Spin) (M N : Matrix (∀ q, Fin (multF (p q))) (∀ q, Fin (multF (p q))) ℤ) (A B : ℕ) :
    bilN p (M + N) A B = bilN p M A B + bilN p N A B := by
  unfold bilN
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Matrix.add_apply]; ring

theorem bilN_smul (p : Fin 4 → Spin) (c : ℤ) (M : Matrix (∀ q, Fin (multF (p q))) (∀ q, Fin (multF (p q))) ℤ) (A B : ℕ) :
    bilN p (c • M) A B = c * bilN p M A B := by
  unfold bilN
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Matrix.smul_apply, smul_eq_mul]; ring

theorem bilN_zero (p : Fin 4 → Spin) (A B : ℕ) :
    bilN p (0 : Matrix (∀ q, Fin (multF (p q))) (∀ q, Fin (multF (p q))) ℤ) A B = 0 := by
  unfold bilN; simp

theorem bilN_list_sum {α : Type*} (p : Fin 4 → Spin) (L : List α)
    (f : α → Matrix (∀ q, Fin (multF (p q))) (∀ q, Fin (multF (p q))) ℤ) (A B : ℕ) :
    bilN p (L.map f).sum A B = (L.map fun x => bilN p (f x) A B).sum := by
  induction L with
  | nil => simpa using bilN_zero p A B
  | cons a t ih => simp only [List.map_cons, List.sum_cons, bilN_add, ih]

theorem bilN_finset_sum {ι : Type*} (p : Fin 4 → Spin) (s : Finset ι)
    (f : ι → Matrix (∀ q, Fin (multF (p q))) (∀ q, Fin (multF (p q))) ℤ) (A B : ℕ) :
    bilN p (∑ i ∈ s, f i) A B = ∑ i ∈ s, bilN p (f i) A B := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using bilN_zero p A B
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, bilN_add, ih]

theorem bilPl_add (p : Fin 4 → Spin) (σ : Equiv.Perm (Fin 4))
    (M N : Matrix (∀ r, Fin (multF (p (σ r)))) (∀ r, Fin (multF (p (σ r)))) ℤ) (A B : ℕ) :
    bilPl p σ (M + N) A B = bilPl p σ M A B + bilPl p σ N A B := by
  unfold bilPl
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Matrix.add_apply]; ring

theorem bilPl_smul (p : Fin 4 → Spin) (σ : Equiv.Perm (Fin 4)) (c : ℤ)
    (M : Matrix (∀ r, Fin (multF (p (σ r)))) (∀ r, Fin (multF (p (σ r)))) ℤ) (A B : ℕ) :
    bilPl p σ (c • M) A B = c * bilPl p σ M A B := by
  unfold bilPl
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Matrix.smul_apply, smul_eq_mul]; ring

theorem bilPl_zero (p : Fin 4 → Spin) (σ : Equiv.Perm (Fin 4)) (A B : ℕ) :
    bilPl p σ (0 : Matrix (∀ r, Fin (multF (p (σ r)))) (∀ r, Fin (multF (p (σ r)))) ℤ) A B = 0 := by
  unfold bilPl; simp

theorem bilPl_list_sum {α : Type*} (p : Fin 4 → Spin) (σ : Equiv.Perm (Fin 4)) (L : List α)
    (f : α → Matrix (∀ r, Fin (multF (p (σ r)))) (∀ r, Fin (multF (p (σ r)))) ℤ) (A B : ℕ) :
    bilPl p σ (L.map f).sum A B = (L.map fun x => bilPl p σ (f x) A B).sum := by
  induction L with
  | nil => simpa using bilPl_zero p σ A B
  | cons a t ih => simp only [List.map_cons, List.sum_cons, bilPl_add, ih]

end QVCheck
