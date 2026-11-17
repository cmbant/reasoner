module

public import FormalResearch.Special.RacahKappaSharp
public import FormalResearch.Special.BulkKappaWin
public import FormalResearch.Special.BulkKappaWinH

/-!
# The sharp amplitude `κ² δ → 2` for every Airy window (abstract form, either lattice)

`bk_sharp_absG`: the abstract sharp theorem `rk_kappa_sharp_abs` / `rk_kappa_sharp_absH` (`RacahKappaSharp`, `RacahKappaHSharp`) in the *window-first* form of `BulkKappaWin`: the constants of the Airy window and the band-mass
statement `Hband` (for every window of those constants) are inputs, and the conclusion is `|κ² δ - 2| ≤ τ'` for **every** window `RkWinAtG` of a member of the family at `h ≤ ε₁(τ')`.  It is generic in the lattice
offset `θ` (`q_k = (k + θ) δ³`: `θ = 1/2` integer chains, `θ = 1` half-integer chains) and in the rows predicate.  `bk_sharp_abs`, `bk_sharp_absH` instantiate it with `bk_win`, `bk_winH`: they
export in one statement the constants, the window existence (`h ≤ δ_A³`), the sharp amplitude of every window, and the Liouville-Green bulk form of every window with the *same* `κ, μ`.

The proof is that of `rk_kappa_sharp_abs` (same mass accounting: band mass, left mass `≤ uM`, zone and tail via `rk_chain_step`).  The hypotheses on the family are those of `rk_kappa_sharp_abs`.

**Claim class: proved.**
-/

@[expose] public section

open Finset FormalResearch.Racah.P3 FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- **The sharp constant for every window, lattice-generic abstract form** (see the module docstring). -/
theorem bk_sharp_absG {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (τ x qs : ℝ) (hqs : 0 < qs) (hτ : τ ^ 2 = 1)
    (hκ : 0 < 1 - τ * x) (hα : 0 < 1 - P * qs ^ 2) (hβ : 0 < 1 - Q * qs ^ 2) (hturn : Phi P Q τ x (qs ^ 2) = 0)
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (q₀ : ℝ → ℝ) (Rows : ℝ → (ℤ → ℝ) → Prop) (Rmax : ℝ) (hRmax : 0 ≤ Rmax)
    (r Cmu ξ0 gmax gmin c1 c2 CA : ℝ) (hr : 0 < r) (hrq4 : r ≤ qs / 4) (hCA : 0 < CA) (hCmu : 0 < Cmu) (hξ0 : 0 < ξ0) (hgmax : 0 < gmax)
    (hc1 : 0 < c1) (hc12 : c1 ≤ c2)
    (Hband : ∀ c0 : ℝ, 0 < c0 → c0 < qs / 2 → ∀ η : ℝ, 0 < η → η ≤ r / 2 → ∀ c : ℝ, c0 < c → c < qs - r → ∃ δ0 θ0 : ℝ, 0 < δ0 ∧ 0 ≤ θ0 ∧
      ∀ (δ : ℝ) (Y : ℤ → ℝ) (Ymax : ℝ), 0 < δ → δ ≤ δ0 → Rows (δ ^ 3) Y → (∀ k : ℤ, qs + δ ^ 3 ≤ ((k : ℝ) + θ) * δ ^ 3 → |Y k| ≤ Ymax) →
        ∀ (J m N : ℤ) (κ μ : ℝ), RkWinAtG θ (q₀ δ) P Q τ x qs Y Ymax r CA Cmu ξ0 gmin gmax c1 c2 δ J m N κ μ →
          BkBandAt θ P Q x qs c η δ θ0 Y κ μ)
    (Fam : ℝ → (ℤ → ℝ) → ℝ → Prop)
    (hrows : ∀ h Y M, Fam h Y M → Rows h Y)
    (hmass : ∀ h Y M, Fam h Y M → 0 < h → M * h * Real.sqrt (rkS P Q x) = 1)
    (hYle : ∀ h Y M, Fam h Y M → ∀ k : ℤ, Y k ^ 2 ≤ M)
    (hsupp : ∀ h Y M, Fam h Y M → ∀ k : ℤ, Rmax < ((k : ℝ) + θ) * h → Y k = 0)
    (hMeq : ∀ h Y M, Fam h Y M → ∀ END : ℤ, (∀ k : ℤ, END ≤ k → Y k = 0) → ∑ k ∈ Finset.Ico 0 END, Y k ^ 2 = M)
    (hmono : ∀ h Y M, Fam h Y M → ∀ k' k : ℤ, qs + h ≤ ((k' : ℝ) + θ) * h → k' ≤ k → Y k ^ 2 ≤ Y k' ^ 2)
    (hLeft : ∀ ε : ℝ, 0 < ε → ∃ cL hL : ℝ, 0 < cL ∧ 0 < hL ∧ ∀ h Y M, Fam h Y M → 0 < h → h ≤ hL →
      ∀ kc : ℤ, ((kc : ℝ) + θ - 1) * h ≤ cL → ∑ k ∈ Finset.Ico 0 kc, Y k ^ 2 ≤ ε * M) :
    ∀ τ' : ℝ, 0 < τ' → ∃ ε1 : ℝ, 0 < ε1 ∧ ∀ (h : ℝ) (Y : ℤ → ℝ) (M : ℝ), Fam h Y M → 0 < h → h ≤ ε1 →
      ∀ (δ : ℝ) (J m N : ℤ) (κ μ : ℝ), 0 < δ → δ ^ 3 = h →
        RkWinAtG θ (q₀ δ) P Q τ x qs Y ((1 / Real.sqrt (rkS P Q x) + 1) / δ ^ 3) r CA Cmu ξ0 gmin gmax c1 c2 δ J m N κ μ →
          |κ ^ 2 * δ - 2| ≤ τ' := by
  have hs := rk_turn_id hP hQ hτ hα hβ hturn
  have hx2 := rk_abs_x_lt hP hQ hτ hqs hα hβ hκ hturn
  have hspos : 0 < rkS P Q x := by
    have h1 : 0 < 1 - x ^ 2 := by linarith
    rw [hs] at h1
    by_contra hneg
    push Not at hneg
    nlinarith [sq_nonneg qs]
  have hsq : 0 < Real.sqrt (rkS P Q x) := Real.sqrt_pos.2 hspos
  have hc2 : 0 < c2 := hc1.trans_le hc12
  set sq : ℝ := Real.sqrt (rkS P Q x) with hsqdef
  set cs : ℝ := 1 / sq + 1 with hcsdef
  have hcs0 : 0 ≤ cs := by positivity
  intro τ' hτ'
  set u : ℝ := min (τ' / 40) (1 / 6) with hudef
  have hu : 0 < u := lt_min (by positivity) (by norm_num)
  have hu40 : 40 * u ≤ τ' := by have := min_le_left (τ' / 40) (1 / 6); linarith
  have hu6 : u ≤ 1 / 6 := min_le_right _ _
  obtain ⟨cL, hL, hcL, hhL, HL⟩ := hLeft u hu
  set c : ℝ := min cL (min (u * qs) (qs / 2)) with hcdef
  have hcpos : 0 < c := lt_min hcL (lt_min (by positivity) (by positivity))
  have hc_cL : c ≤ cL := min_le_left _ _
  have hcu : c / qs ≤ u := by
    rw [div_le_iff₀ hqs]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hcq2 : c ≤ qs / 2 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨η, hη, hηr, hη1, hηu, hA0⟩ := rk_choose_eta hc1 hc2 hgmax.le hsq hu hqs hr
  have hc0 : 0 < c / 2 := by positivity
  obtain ⟨δ0, θ0, hδ0, hθ00, HB⟩ := Hband (c / 2) hc0 (by linarith) η hη hηr c (by linarith) (by linarith)
  set K3 : ℝ := rkzK3 c1 gmax CA 4 (Rmax + 2) with hK3def
  set A0v : ℝ := 2 * gmax ^ 2 * (√(2 * c2 * η) / Real.pi + 2 * c2 * (2 * c2 * η)) / c1 with hA0vdef
  have hK30 : 0 ≤ K3 := rkzK3_nonneg hc1 (by norm_num) (by linarith)
  have hA0v0 : 0 ≤ A0v := by rw [hA0vdef]; positivity
  obtain ⟨δm, hδm, Hδ⟩ := rk_delta_exists (b1 := δ0) (b2 := 1) (b3 := hL) (b4 := (ξ0 / 14)) (b5 := (1 * ξ0 ^ 3 / (48 * ((450 * gmax + CA) * Cmu * cs + 1)))) (b6 := (η / 2)) (b7 := (c1 * η / (2 * (1 + c2)))) (b8 := (c1 * r / 8)) (b9 := (1 / c2)) (b10 := (1 * ξ0 ^ 3 / (48 * (Cmu * cs + 1)))) (b11 := (u / (θ0 + 1))) (b12 := (u / (8 * sq * K3 + 1))) (b13 := (u / (2 * sq * (A0v + K3) + 1))) (b14 := (8 * u)) hδ0 one_pos hhL (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
  refine ⟨δm ^ 3, by positivity, ?_⟩
  intro h Y M hF hh hhδ δ J m N κ μ hδ hδ3 hWin
  subst hδ3
  have hδle : δ ≤ δm := by
    by_contra hcon
    push Not at hcon
    have : δm ^ 3 < δ ^ 3 := by gcongr
    linarith
  obtain ⟨d0, d1, dL, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14⟩ := Hδ δ hδle
  have hM := hmass _ Y M hF hh
  have hδ3le : δ ^ 3 ≤ δ := by
    have h1 : δ ^ 2 ≤ 1 := pow_le_one₀ hδ.le d1
    calc δ ^ 3 = δ * δ ^ 2 := by ring
      _ ≤ δ * 1 := mul_le_mul_of_nonneg_left h1 hδ.le
      _ = δ := mul_one _
  have hbd : ∀ k : ℤ, qs + δ ^ 3 ≤ ((k : ℝ) + θ) * δ ^ 3 → |Y k| ≤ cs / δ ^ 3 := fun k _ =>
    rk_tail_bd hδ d1 hsq hM (hYle _ Y M hF k)
  obtain ⟨kc, jz, hkc1, hkc2, hjz1, hjz2⟩ := rk_idx (θ := θ) (c := c) (d := qs - η) hδ
  obtain ⟨hBlo, hBhi⟩ := HB δ Y (cs / δ ^ 3) hδ d0 (hrows _ Y M hF) hbd J m N κ μ hWin kc jz M hkc1 (by linarith) hjz1 (by linarith) hM
  have hLeftB : ∑ k ∈ Finset.Ico 0 kc, Y k ^ 2 ≤ u * M :=
    HL _ Y M hF hh (hδ3le.trans dL) kc (by linarith)
  have hcη : c + δ ^ 3 < qs - η := by
    have : η ≤ qs / 8 := by linarith
    have : δ ^ 3 ≤ η / 2 := hδ3le.trans d6
    linarith
  have hδ2 : δ ^ 2 ≤ δ := by
    calc δ ^ 2 = δ * δ := by ring
      _ ≤ δ * 1 := mul_le_mul_of_nonneg_left d1 hδ.le
      _ = δ := mul_one _
  have hc2δ : c2 * δ ≤ 1 := by
    calc c2 * δ ≤ c2 * (1 / c2) := mul_le_mul_of_nonneg_left d9 hc2.le
      _ = 1 := by field_simp
  have hθδ : θ0 * δ ^ 3 ≤ u := by
    have h1 : θ0 * δ ^ 3 ≤ θ0 * δ := mul_le_mul_of_nonneg_left hδ3le hθ00
    have h2 := (le_div_iff₀ (by positivity : (0 : ℝ) < θ0 + 1)).1 d11
    linarith only [h1, h2, hδ]
  have hK3δ : 4 * sq * (K3 * δ) ≤ u / 2 := by
    have h2 := (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * sq * K3 + 1)).1 d12
    linarith only [h2, hδ]
  have hξδ : 2 * sq * δ * (A0v + K3 * δ) ≤ u := by
    have h1 : δ * (A0v + K3 * δ) ≤ δ * (A0v + K3) := by
      apply mul_le_mul_of_nonneg_left _ hδ.le
      have : K3 * δ ≤ K3 * 1 := mul_le_mul_of_nonneg_left d1 hK30
      linarith only [this]
    have h2 := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * sq * (A0v + K3) + 1)).1 d13
    have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * sq)
    linarith only [h2, h3, hδ]
  have hfin := rk_chain_step (P := P) (Q := Q) (τ := τ) (x := x) (qs := qs) (Y := Y) (r := r) (C := CA) (Cmu := Cmu) (ξ0 := ξ0)
    (gmin := gmin) (gmax := gmax) (c1 := c1) (c2 := c2) (δ := δ) (cs := cs) (Rmax := Rmax) (η := η) (c := c) (M := M) (sq := sq) (u := u)
    (θ0 := θ0) hWin hθ0 hθ1 hδ d1 hc1 hc12 hgmax.le hCA.le hCmu.le hcs0 hξ0 hRmax hr hη hηr hη1 hsq hqs d4 d5 (hδ3le.trans d6)
    (hδ2.trans d7) d8 hc2δ d10 hkc1 hkc2 hcpos hcη hjz1 hjz2 hM (hmono _ Y M hF) (hsupp _ Y M hF) (hMeq _ Y M hF) hLeftB hBlo hBhi
    hu hu6 hθ00 hcu hηu hθδ hA0 hK3δ hξδ d14
  linarith

/-- info: 'FormalResearch.Special.bk_sharp_absG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.bk_sharp_absG

end FormalResearch.Special
