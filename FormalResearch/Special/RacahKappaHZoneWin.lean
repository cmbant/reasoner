module

public import FormalResearch.Special.RacahKappaHZoneAbs
public import FormalResearch.Special.RacahKappaZoneWin

/-!
# Index selection and the zone mass, shifted lattice (half-integer Racah chains)

Twin of `RacahKappaZoneWin` for the Airy window `RkWinAtH` on `q_k = (k+1)δ³`; declarations carry the suffix `H`.

**Claim class: proved.**
-/

@[expose] public section

open Finset FormalResearch.Racah.P3 FormalResearch.DiscreteAiry
open scoped Real

namespace FormalResearch.Special
lemma rk_idxH {δ c d : ℝ} (hδ : 0 < δ) :
    ∃ kc jz : ℤ, c ≤ ((kc : ℝ) + 1) * δ ^ 3 ∧ ((kc : ℝ) - 1 / 2) * δ ^ 3 < c ∧
      d < ((jz : ℝ) + 1) * δ ^ 3 ∧ ((jz : ℝ) - 1 / 2) * δ ^ 3 ≤ d := by
  have hh : 0 < δ ^ 3 := by positivity
  refine ⟨⌈(c - δ ^ 3) / δ ^ 3⌉, ⌊(d - δ ^ 3) / δ ^ 3⌋ + 1, ?_, ?_, ?_, ?_⟩
  · have := Int.le_ceil ((c - δ ^ 3) / δ ^ 3)
    rw [div_le_iff₀ hh] at this
    linarith
  · have := Int.ceil_lt_add_one ((c - δ ^ 3) / δ ^ 3)
    have h2 : (⌈(c - δ ^ 3) / δ ^ 3⌉ : ℝ) - 1 < (c - δ ^ 3) / δ ^ 3 := by linarith
    rw [lt_div_iff₀ hh] at h2
    linarith
  · have := Int.lt_floor_add_one ((d - δ ^ 3) / δ ^ 3)
    rw [div_lt_iff₀ hh] at this
    push_cast
    linarith
  · have := Int.floor_le ((d - δ ^ 3) / δ ^ 3)
    rw [le_div_iff₀ hh] at this
    push_cast
    linarith

/-- The zone mass from a window. -/
lemma rk_zone_winH {P Q τ x qs : ℝ} {Y : ℤ → ℝ} {r C Cmu ξ0 gmin gmax c1 c2 δ cs Rmax η : ℝ} {J m N jz : ℤ} {κ μ : ℝ}
    (hW : RkWinAtH P Q τ x qs Y (cs / δ ^ 3) r C Cmu ξ0 gmin gmax c1 c2 δ J m N κ μ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hc1 : 0 < c1) (hc12 : c1 ≤ c2) (hgmax : 0 ≤ gmax) (hC : 0 ≤ C) (hCmu : 0 ≤ Cmu) (hcs : 0 ≤ cs)
    (hξ0 : 0 < ξ0) (hRmax : 0 ≤ Rmax) (hr : 0 < r) (hη : 0 < η) (hηr : η ≤ r / 2) (hη1 : η ≤ 1)
    (hs1 : δ ≤ ξ0 / 14) (hs2 : δ ≤ 1 * ξ0 ^ 3 / (48 * ((450 * gmax + C) * Cmu * cs + 1))) (hs3 : δ ^ 3 ≤ η / 2)
    (hs4 : δ ^ 2 ≤ c1 * η / (2 * (1 + c2))) (hs5 : δ ≤ c1 * r / 8) (hs6 : c2 * δ ≤ 1)
    (hjz1 : qs - η < ((jz : ℝ) + 1) * δ ^ 3) (hjz2 : ((jz : ℝ) + 1) * δ ^ 3 ≤ qs - η + δ ^ 3)
    (hmono : ∀ k' k : ℤ, qs + δ ^ 3 ≤ ((k' : ℝ) + 1) * δ ^ 3 → k' ≤ k → Y k ^ 2 ≤ Y k' ^ 2)
    (hsupp : ∀ k : ℤ, Rmax < ((k : ℝ) + 1) * δ ^ 3 → Y k = 0) :
    ∃ END : ℤ, jz ≤ END ∧ (∀ k : ℤ, END ≤ k → Y k = 0) ∧
      ∑ k ∈ Finset.Ico jz END, Y k ^ 2 ≤
        2 * gmax ^ 2 * (2 * κ ^ 2 + 2 * 1 ^ 2) * ((√(2 * c2 * η) / Real.pi + 2 * c2 * (2 * c2 * η)) / (c1 * δ ^ 2)) +
          rkzK3 c1 gmax C 4 (Rmax + 2) * (2 * κ ^ 2 + 2 * 1 ^ 2) / δ := by
  obtain ⟨hJ1, hJN, hJm, hmN, hwin, h1, h2, h3, h4, h5, h6, hg, hXm, hgl, hgap, hX0m, hXN, hμ, hpt⟩ := hW
  have hμ' : |μ| ≤ Cmu * (cs / δ ^ 3) * Real.exp (-ξ0 / δ ^ 3) / δ := hμ
  refine rk_zone_absH (Y := Y) (X := turnX (hrU P Q τ x) qs (δ ^ 3) δ)
    (g := fun k => langerAmp (hrU P Q τ x) (hrA1 P Q) qs (dalQ (δ ^ 3) δ k)) (J := J) (m := m) (N := N) (jz := jz) (δ := δ) (qs := qs)
    (r := r) (η := η) (C := C) (Cmu := Cmu) (ξ0 := ξ0) (gmin := gmin) (gmax := gmax) (c1 := c1) (c2 := c2) (κ := κ) (μ := μ) (cs := cs)
    (Rmax := Rmax) (κm := 1) hδ hδ1 hc1 hc12 hgmax hC hCmu hcs hξ0 one_pos hRmax hr hη hηr hη1 hs1 hs2 hs3 hs4 hs5 hs6 hJ1 hJN hJm hmN
    h2 h3 h4 hjz1 hjz2 hgap (fun k hk => hXm k hk) hX0m hXN hg ?_ hμ' hmono hsupp
  intro k hk
  have := hpt k hk
  simpa [daoPhi, daoPsi] using this



end FormalResearch.Special
