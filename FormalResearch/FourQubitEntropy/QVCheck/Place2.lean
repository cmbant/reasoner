import FormalResearch.FourQubitEntropy.QVCheck.Place

/-!
# The placement transfer (K5)
-/

open Finset
open scoped Matrix
open FormalResearch.FourQubitEntropy FormalResearch.FourQubitEntropy.QVBlock

namespace QVCheck

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

theorem bil_eq_bilN (p : Fin 4 → Spin) (M : Matrix (∀ q, Fin (multF (p q))) (∀ q, Fin (multF (p q))) ℤ) (A B : Fin (nnF p)) :
    bil p M A B = bilN p M A.val B.val := rfl

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

end QVCheck
