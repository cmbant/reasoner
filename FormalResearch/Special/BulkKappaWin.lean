module

public import FormalResearch.Special.BulkKappaDef

/-!
# Window-first bulk and band theorem, integer lattice

`bk_win`: for the closed-form Hahn / centred Racah rows `jac (hrAk P Q a b h) (hrCk P Q τ x a b h) Y = 0` there are constants `r, C_μ, ξ₀, g_max, g_min, c₁, c₂, C_A, δ_A` such that

1. (**existence**) every solution `Y` of the rows at a scale `δ ≤ δ_A` with `|Y| ≤ Y_max` beyond `q_*` has an Airy window `RkWinAt` of those constants;
2. (**bulk**) for every bulk window `[c, q_* - η]` (`c₀ < c < q_* - r`, `0 < η ≤ r/2`) there are `δ₀, C` such that **every** window `RkWinAt` of those constants of a solution at `δ ≤ δ₀` satisfies the
   Liouville-Green bulk form `BkBulkAt` with the *window's* `κ, μ`;
3. (**band**) the same for the band mass `BkBandAt` in units of the Gauss weight.

This is `rk_bulk` / `rk_bulk_band` (`RacahKappaBulk`, `RacahKappaBandD`) with the quantifiers on the window reordered (same proofs): the window is no longer an existential witness inside the statement, so
statements about `κ` (`bk_sharp_abs`, `BulkKappaAbs`) and the bulk form can be applied to the *same* `κ, μ`.

**Claim class: proved.**
-/

@[expose] public section

open Finset Set FormalResearch.Racah.P3 FormalResearch.DiscreteAiry
open scoped Real

namespace FormalResearch.Special

/-- **Window, bulk form and band mass of every window, integer lattice** (see the module docstring). -/
theorem bk_win {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (a b τ x qs : ℝ) (hqs : 0 < qs) (hτ : τ ^ 2 = 1)
    (hκ : 0 < 1 - τ * x) (hα : 0 < 1 - P * qs ^ 2) (hβ : 0 < 1 - Q * qs ^ 2) (hturn : Phi P Q τ x (qs ^ 2) = 0)
    (hosc0 : ∀ q : ℝ, 0 < q → q < qs → |hrU P Q τ x q| < 1) :
    ∃ (r Cmu ξ0 gmax gmin c1 c2 CA δA : ℝ), 0 < r ∧ r ≤ qs / 4 ∧ 0 < CA ∧ 0 < Cmu ∧ 0 < ξ0 ∧ 0 < gmax ∧ 0 < gmin ∧
      gmin ≤ gmax ∧ 0 < c1 ∧ c1 ≤ c2 ∧ 0 < δA ∧
      (∀ (δ : ℝ) (Y : ℤ → ℝ) (Ymax : ℝ), 0 < δ → δ ≤ δA →
        (∀ k : ℤ, 1 ≤ k → jac (hrAk P Q a b (δ ^ 3)) (hrCk P Q τ x a b (δ ^ 3)) Y k = 0) →
        (∀ k : ℤ, qs + δ ^ 3 ≤ ((k : ℝ) + 1 / 2) * δ ^ 3 → |Y k| ≤ Ymax) →
        ∃ (J m N : ℤ) (κ μ : ℝ), RkWinAt P Q τ x qs Y Ymax r CA Cmu ξ0 gmin gmax c1 c2 δ J m N κ μ) ∧
      (∀ c0 : ℝ, 0 < c0 → c0 < qs / 2 → ∀ η : ℝ, 0 < η → η ≤ r / 2 → ∀ c : ℝ, c0 < c → c < qs - r → ∃ δ0 C : ℝ, 0 < δ0 ∧ 0 < C ∧
        ∀ (δ : ℝ) (Y : ℤ → ℝ) (Ymax : ℝ), 0 < δ → δ ≤ δ0 →
          (∀ k : ℤ, 1 ≤ k → jac (hrAk P Q a b (δ ^ 3)) (hrCk P Q τ x a b (δ ^ 3)) Y k = 0) →
          (∀ k : ℤ, qs + δ ^ 3 ≤ ((k : ℝ) + 1 / 2) * δ ^ 3 → |Y k| ≤ Ymax) →
          ∀ (J m N : ℤ) (κ μ : ℝ), RkWinAt P Q τ x qs Y Ymax r CA Cmu ξ0 gmin gmax c1 c2 δ J m N κ μ →
            BkBulkAt (δ ^ 3 / 2) P Q τ x qs c0 c η δ C Y κ μ) ∧
      (∀ c0 : ℝ, 0 < c0 → c0 < qs / 2 → ∀ η : ℝ, 0 < η → η ≤ r / 2 → ∀ c : ℝ, c0 < c → c < qs - r → ∃ δ0 θ0 : ℝ, 0 < δ0 ∧ 0 ≤ θ0 ∧
        ∀ (δ : ℝ) (Y : ℤ → ℝ) (Ymax : ℝ), 0 < δ → δ ≤ δ0 →
          (∀ k : ℤ, 1 ≤ k → jac (hrAk P Q a b (δ ^ 3)) (hrCk P Q τ x a b (δ ^ 3)) Y k = 0) →
          (∀ k : ℤ, qs + δ ^ 3 ≤ ((k : ℝ) + 1 / 2) * δ ^ 3 → |Y k| ≤ Ymax) →
          ∀ (J m N : ℤ) (κ μ : ℝ), RkWinAt P Q τ x qs Y Ymax r CA Cmu ξ0 gmin gmax c1 c2 δ J m N κ μ →
            BkBandAt (1 / 2) P Q x qs c η δ θ0 Y κ μ) := by
  have hs := rk_turn_id hP hQ hτ hα hβ hturn
  have hx2 := rk_abs_x_lt hP hQ hτ hqs hα hβ hκ hturn
  have hspos : 0 < rkS P Q x := by
    have h1 : 0 < 1 - x ^ 2 := by linarith
    rw [hs] at h1
    by_contra hneg
    push Not at hneg
    nlinarith [sq_nonneg qs]
  have hsq : 0 < Real.sqrt (rkS P Q x) := Real.sqrt_pos.2 hspos
  obtain ⟨ρ, hρ, hch⟩ := dlgh_chart (P := P) (Q := Q) τ x qs hqs hκ hα hβ hturn
  obtain ⟨r, δA, CA, Cmu, ξ0, gmax, gmin0, c1, c2, hr, hrρ, hrq4, hδA, hδA1, hCA, hCmu, hξ0, hgmax, hgmin0, hgg, hc1, hc12, HA⟩ :=
    rk_compose hP hQ a b τ x qs hqs hτ hκ hα hβ hturn (ρ := min (ρ / 2) (qs / 4))
      (lt_min (by positivity) (by linarith))
  have hrρ1 : r ≤ ρ / 2 := hrρ.trans (min_le_left _ _)
  have hrρ2 : r ≤ qs / 4 := hrρ.trans (min_le_right _ _)
  -- the bulk form of every window
  have Hbulk : ∀ c0 : ℝ, 0 < c0 → c0 < qs / 2 → ∀ η : ℝ, 0 < η → η ≤ r / 2 → ∀ c : ℝ, c0 < c → c < qs - r → ∃ δ0 C : ℝ, 0 < δ0 ∧ 0 < C ∧
        ∀ (δ : ℝ) (Y : ℤ → ℝ) (Ymax : ℝ), 0 < δ → δ ≤ δ0 →
          (∀ k : ℤ, 1 ≤ k → jac (hrAk P Q a b (δ ^ 3)) (hrCk P Q τ x a b (δ ^ 3)) Y k = 0) →
          (∀ k : ℤ, qs + δ ^ 3 ≤ ((k : ℝ) + 1 / 2) * δ ^ 3 → |Y k| ≤ Ymax) →
          ∀ (J m N : ℤ) (κ μ : ℝ), RkWinAt P Q τ x qs Y Ymax r CA Cmu ξ0 gmin0 gmax c1 c2 δ J m N κ μ →
            BkBulkAt (δ ^ 3 / 2) P Q τ x qs c0 c η δ C Y κ μ := by
    intro c0 hc0 hc0q η hη hηr c hc0c hcr
    have hosc : ∀ q ∈ Set.Ico c0 qs, |hrU P Q τ x q| < 1 := fun q hq => hosc0 q (hc0.trans_le hq.1) hq.2
    have hc : 0 < c := hc0.trans hc0c
    have hc1pos : 0 < (c0 + c) / 2 := by linarith
    have hcd : c < qs - η := by linarith
    have hdd0 : qs - η < qs - η / 2 := by linarith
    have hfacP : ∀ q : ℝ, 0 < q → q ≤ qs → 0 < 1 - P * q ^ 2 := fun q h1 h2 => dlgh_fac hP hα h1 h2
    have hfacQ : ∀ q : ℝ, 0 < q → q ≤ qs → 0 < 1 - Q * q ^ 2 := fun q h1 h2 => dlgh_fac hQ hβ h1 h2
    have hreg : ∀ q ∈ Set.Icc c0 (qs - η / 2), 0 < 1 - P * q ^ 2 ∧ 0 < 1 - Q * q ^ 2 ∧ |hrU P Q τ x q| < 1 :=
      fun q hq => ⟨hfacP q (by linarith [hq.1]) (by linarith [hq.2]), hfacQ q (by linarith [hq.1]) (by linarith [hq.2]),
        hosc q ⟨hq.1, by linarith [hq.2]⟩⟩
    obtain ⟨δ1, Cb, hδ1, hCb, HM⟩ := dlg_airy_match_hahn hP hQ a b τ x hτ hc0 hc0c hcd hdd0 hreg
    have hch_d := hch (qs - r / 2) (by linarith) (by linarith)
    have hΦpos : 0 < ∫ s in (qs - r / 2)..qs, Real.arccos (hrU P Q τ x s) := by
      rw [← hch_d.2.1]; exact mul_pos (by norm_num) (Real.rpow_pos_of_pos (neg_pos.2 hch_d.1) _)
    set Φ : ℝ := ∫ s in (qs - r / 2)..qs, Real.arccos (hrU P Q τ x s) with hΦ
    have hgmin : 0 < (((3 / 2) * Φ) ^ (2 / 3 : ℝ)) ^ (1 / 4 : ℝ) * 1 :=
      mul_pos (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos (by positivity) _) _) one_pos
    set gmin : ℝ := (((3 / 2) * Φ) ^ (2 / 3 : ℝ)) ^ (1 / 4 : ℝ) * 1 with hgmin_def
    have hKc : 0 ≤ 1 / (12 * Φ) + CA / gmin := by positivity
    refine ⟨min δ1 (min 1 (r / 4)), Cb * (2 + (1 / (12 * Φ) + CA / gmin)),
      lt_min hδ1 (lt_min one_pos (by positivity)), by positivity, ?_⟩
    intro δ Y Ymax hδ hδ0 hrows hbd J m N κ μ hWin
    have hδ1' : δ ≤ δ1 := hδ0.trans (min_le_left _ _)
    have hδone : δ ≤ 1 := hδ0.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hδr : δ ≤ r / 4 := hδ0.trans ((min_le_right _ _).trans (min_le_right _ _))
    have h3δ : δ ^ 3 ≤ δ := by
      have h1 : δ ^ 2 ≤ 1 := pow_le_one₀ hδ.le hδone
      calc δ ^ 3 = δ * δ ^ 2 := by ring
        _ ≤ δ * 1 := mul_le_mul_of_nonneg_left h1 hδ.le
        _ = δ := mul_one _
    have hδ3r : δ ^ 3 ≤ r / 4 := h3δ.trans hδr
    have hWin' := hWin
    obtain ⟨hJ1, hJN, hJm, hmN, hwin, h1, h2, h3, h4, h5, h6, hg, hXm, hgl, hgap, hX0m, hXN, hμ2, hpt⟩ := hWin
    have e2 : ∀ k : ℤ, dalQ (δ ^ 3 / 2) δ k = ((k : ℝ) + 1 / 2) * δ ^ 3 := fun k => by unfold dalQ; ring
    have hqJ := dlgh_qJ (qs := qs) (r := r) (δ := δ) (J := J) hδ h1 h2 hδ3r
    have site := dlgh_site_all (P := P) (Q := Q) hP hQ τ x qs hα hβ (c0 := c0) (c := c) (r := r) (ρ := ρ) (δ := δ) (J := J)
      (N := N) (κ := κ) (μ := μ) (Y := Y) (CA := CA) hch hosc hrρ1 hc0c hcr hδ hqJ hΦpos hCA hpt hJN hr hc0
    have hlat := dlgh_lattice (c := c) (d := qs - η) hδ
    have hqJ' : ∀ k : ℤ, J ≤ k → k ≤ J + 1 → c ≤ dlgQ (δ ^ 3 / 2) (δ ^ 3) k ∧ dlgQ (δ ^ 3 / 2) (δ ^ 3) k ≤ qs - η :=
      fun k hk1 hk2 => ⟨by have h := hqJ k hk1 hk2; show c ≤ dalQ (δ ^ 3 / 2) δ k; linarith [h.1],
        by have h := hqJ k hk1 hk2; show dalQ (δ ^ 3 / 2) δ k ≤ qs - η; linarith [h.2]⟩
    have hJw := (hlat J).1 (hqJ' J le_rfl (by omega))
    have hJw1 := (hlat (J + 1)).1 (hqJ' (J + 1) (by omega) le_rfl)
    have hJ0 : 0 ≤ ⌈(c - δ ^ 3 / 2) / δ ^ 3⌉ := by
      by_contra hneg
      push Not at hneg
      have hmem := (hlat ⌈(c - δ ^ 3 / 2) / δ ^ 3⌉).2 ⟨le_rfl, by omega⟩
      have h1' : ((⌈(c - δ ^ 3 / 2) / δ ^ 3⌉ : ℤ) : ℝ) ≤ -1 := by exact_mod_cast (by omega : ⌈(c - δ ^ 3 / 2) / δ ^ 3⌉ ≤ -1)
      have := hmem.1
      unfold dlgQ at this
      have h3p : 0 < δ ^ 3 := by positivity
      have h4 := mul_le_mul_of_nonneg_right h1' h3p.le
      linarith only [this, h4, h3p, hc]
    intro k hk1 hk2
    have hmem := (hlat k).1 ⟨hk1, hk2⟩
    have hres := HM δ Y ⌈(c - δ ^ 3 / 2) / δ ^ 3⌉ (⌊(qs - η - δ ^ 3 / 2) / δ ^ 3⌋ - 1) J κ μ
      (∫ s in (c0 + c) / 2..qs, Real.arccos (hrU P Q τ x s)) Φ gmin CA hΦpos hgmin hCA.le hδ
      hδ1' hJw.1 (by omega)
      (fun j hj => by
        rw [Finset.mem_Icc] at hj
        exact (hlat j).2 ⟨hj.1, by omega⟩)
      (fun j hj => hrows j (by rw [Finset.mem_Icc] at hj; omega))
      (site J le_rfl (by omega)) (site (J + 1) (by omega) le_rfl)
    exact hres k (by rw [Finset.mem_Icc]; omega)
  refine ⟨r, Cmu, ξ0, gmax, gmin0, c1, c2, CA, δA, hr, hrq4, hCA, hCmu, hξ0, hgmax, hgmin0, hgg, hc1, hc12, hδA, ?_, Hbulk, ?_⟩
  · -- existence of the window
    intro δ Y Ymax hδ hδA' hrows hbd
    obtain ⟨δ', hδ', hδ'A, hδ'3, J, m, N, κ, μ, hWin⟩ := HA (δ ^ 3) Y Ymax (by positivity) (pow_le_pow_left₀ hδ.le hδA' 3) hrows hbd
    have hδeq : δ = δ' := (pow_left_inj₀ hδ.le hδ'.le (by norm_num)).1 hδ'3.symm
    subst hδeq
    exact ⟨J, m, N, κ, μ, hWin⟩
  · -- the band mass of every window
    intro c0 hc0 hc0q η hη hηr c hc0c hcr
    obtain ⟨δ0', C, hδ0', hC, HH⟩ := Hbulk c0 hc0 hc0q η hη hηr c hc0c hcr
    have hcη : c < qs - η := by linarith
    obtain ⟨lo, hi, Mm, D⟩ := rk_bulk_D hP hQ τ x qs hα hβ hosc0 hc0 hc0c hη hcη
    have hc : 0 < c := hc0.trans hc0c
    set Cb0 : ℝ := (hi ^ 5 + 2 * qs * Mm * (hi ^ 4 + hi ^ 8)) / 2 with hCb0
    set E : ℝ := C * √Real.pi with hE
    have hπ := Real.pi_pos
    have hE0 : 0 ≤ E := by positivity
    have hhi0 : 0 ≤ hi := by
      have h1 := D.Ab ((c0 + c) / 2 + (qs - η / 2 - (c0 + c) / 2) / 2) ⟨by
        have : (c0 + c) / 2 < qs - η / 2 := by linarith
        linarith, by
        have : (c0 + c) / 2 < qs - η / 2 := by linarith
        linarith⟩
      linarith [h1.1, h1.2, D.lo_pos]
    have hCb0n : 0 ≤ Cb0 := by have := D.M_nonneg; rw [hCb0]; positivity
    refine ⟨min δ0' (min 1 (min (η / 4) (c / 2))), 8 * E * (1 + E) + 2 * Cb0 * Real.sqrt (rkS P Q x) / Real.pi,
      lt_min hδ0' (lt_min one_pos (lt_min (by linarith) (by linarith))), by positivity, ?_⟩
    intro δ Y Ymax hδ hδ0 hrows hbd J m N κ μ hW
    have hδ' : δ ≤ δ0' := hδ0.trans (min_le_left _ _)
    have hδ1 : δ ≤ 1 := hδ0.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hδη : δ ≤ η / 4 := hδ0.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have hδc' : δ ≤ c / 2 := hδ0.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    have hδc : 2 * δ ≤ c := by linarith
    have h3δ : δ ^ 3 ≤ δ := by
      have h1 : δ ^ 2 ≤ 1 := pow_le_one₀ hδ.le hδ1
      calc δ ^ 3 = δ * δ ^ 2 := by ring
        _ ≤ δ * 1 := mul_le_mul_of_nonneg_left h1 hδ.le
        _ = δ := mul_one _
    have hbulk := HH δ Y Ymax hδ hδ' hrows hbd J m N κ μ hW
    intro kc jz M hkc1 hkc2 hjz1 hjz2 hM
    exact rk_band_assemble (θl := 1 / 2) (q₀ := δ ^ 3 / 2) (by norm_num) (by norm_num) hP hQ τ x qs hqs hτ hα hβ hs hspos hsq hc0 hc0c hη hcη hc hπ hE0 hδ hδ1 hδη hδc (by ring)
      (by
        have : η < qs - η - c := by linarith
        linarith) h3δ D hhi0 hbulk kc jz M hkc1 (by linarith) hjz1 (by linarith) hM

/-- info: 'FormalResearch.Special.bk_win' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.bk_win

end FormalResearch.Special
