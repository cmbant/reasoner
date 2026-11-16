module

public import FormalResearch.Special.DiscreteAirySecondLink

/-!
# Second-order Airy parametrix, part 5: the two links combined (odd orders cancel)

`PairData` = two links `L₊` (at `t`, `h = t³`) and `L₋` (at `-t`, `-h`) with the **same jets** `z₀..z₃, G₀..G₂, H₀, H₁`.

* `pair_A`: `ℒ_A(t) + ℒ_A(-t) - Z = O(|h|³)` provided the central term `Z = Z₀ + h² Z₂ + O(h³)` has
  `Z₀ = 2 lkA0` and `Z₂ = 2 lkA2` (the **eikonal** and the **transport equation for `q₁`**; the odd coefficient `lkA1` cancels exactly);
* `pair_S`: `ℒ_S(t) - ℒ_S(-t) - Z_c = O(|h|³)` provided `Z_c = h Q₀ + O(h³)` with `Q₀ = 2 lkS1` (the `h²` coefficient `lkS2`
  cancels exactly; `lkS1 = 0` after the **transport identity** of the amplitude).

**Claim class: proved.**
-/

@[expose] public section

open Set

namespace FormalResearch.Special

section Pair

variable {α : Type*} {D : α → Prop} {hh t z0 z1 z2 z3 G0 G1 G2 H0 H1 : α → ℝ} {Z0 S B : ℝ}

lemma SOB.neg_hh {n : ℕ} {f : α → ℝ} (h : SOB D hh n f) : SOB D (fun a => -hh a) n f := by
  obtain ⟨K, hK, hb⟩ := h
  exact ⟨K, hK, fun a ha => by simpa [abs_neg] using hb a ha⟩

lemma SOB.of_neg_hh {n : ℕ} {f : α → ℝ} (h : SOB D (fun a => -hh a) n f) : SOB D hh n f := by
  obtain ⟨K, hK, hb⟩ := h
  exact ⟨K, hK, fun a ha => by simpa [abs_neg] using hb a ha⟩

/-- **Even combination** (`𝔄`). -/
theorem pair_A {e₁ γ₁ η₁ e₂ γ₂ η₂ : α → ℝ} {Zc Zc0 Zc2 : α → ℝ}
    (L₁ : LinkData D hh t z0 z1 z2 z3 e₁ G0 G1 G2 γ₁ H0 H1 η₁ Z0 S B)
    (L₂ : LinkData D (fun a => -hh a) (fun a => -t a) z0 z1 z2 z3 e₂ G0 G1 G2 γ₂ H0 H1 η₂ Z0 S B)
    (hZ : SOB D hh 3 (fun a => Zc a - (Zc0 a + hh a ^ 2 * Zc2 a)))
    (hZ0 : ∀ a, D a → Zc0 a = 2 * lkA0 (z0 a) (z1 a) (G0 a))
    (hZ2 : ∀ a, D a → Zc2 a = 2 * lkA2 (z0 a) (z1 a) (z2 a) (z3 a) (G0 a) (G1 a) (G2 a) (H0 a) (H1 a)) :
    SOB D hh 3 (fun a =>
      (lkG hh G0 G1 G2 γ₁ a * apuCs (z0 a) (t a) (z1 a + lkδ hh z2 z3 e₁ a) +
        hh a * lkH hh H0 H1 η₁ a * apuCs1 (z0 a) (t a) (z1 a + lkδ hh z2 z3 e₁ a)) +
      (lkG (fun a => -hh a) G0 G1 G2 γ₂ a * apuCs (z0 a) (-t a) (z1 a + lkδ (fun a => -hh a) z2 z3 e₂ a) +
        (-hh a) * lkH (fun a => -hh a) H0 H1 η₂ a * apuCs1 (z0 a) (-t a) (z1 a + lkδ (fun a => -hh a) z2 z3 e₂ a))
      - Zc a) := by
  have h1 := L₁.exA.1
  have h2 := (L₂.exA.1).of_neg_hh
  have := (h1.add h2).sub hZ
  refine this.congr fun a ha => ?_
  simp only [hZ0 a ha, hZ2 a ha]
  ring

/-- **Odd combination** (`𝔅`). -/
theorem pair_S {e₁ γ₁ η₁ e₂ γ₂ η₂ : α → ℝ} {Zc : α → ℝ}
    (L₁ : LinkData D hh t z0 z1 z2 z3 e₁ G0 G1 G2 γ₁ H0 H1 η₁ Z0 S B)
    (L₂ : LinkData D (fun a => -hh a) (fun a => -t a) z0 z1 z2 z3 e₂ G0 G1 G2 γ₂ H0 H1 η₂ Z0 S B)
    (hZ : SOB D hh 3 (fun a => Zc a - hh a * (2 * lkS1 (z0 a) (z1 a) (z2 a) (G0 a) (G1 a) (H0 a)))) :
    SOB D hh 3 (fun a =>
      (lkG hh G0 G1 G2 γ₁ a * apuSs (z0 a) (t a) (z1 a + lkδ hh z2 z3 e₁ a) +
        hh a * lkH hh H0 H1 η₁ a * apuSs1 (z0 a) (t a) (z1 a + lkδ hh z2 z3 e₁ a)) -
      (lkG (fun a => -hh a) G0 G1 G2 γ₂ a * apuSs (z0 a) (-t a) (z1 a + lkδ (fun a => -hh a) z2 z3 e₂ a) +
        (-hh a) * lkH (fun a => -hh a) H0 H1 η₂ a * apuSs1 (z0 a) (-t a) (z1 a + lkδ (fun a => -hh a) z2 z3 e₂ a))
      - Zc a) := by
  have h1 := L₁.exS.1
  have h2 := (L₂.exS.1).of_neg_hh
  have := (h1.sub h2).sub hZ
  refine this.congr fun a ha => ?_
  ring

end Pair

end FormalResearch.Special
