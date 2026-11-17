module

public import FormalResearch.Special.RacahKappaCompose

/-!
# Bulk Liouville-Green form with the same `κ, μ` as the Airy window (Hahn / centred Racah)

`dlg_hahn_airy` (`DiscreteLgHahnMatch`) proves the bulk form `Y_k = h^{1/6}π^{-1/2} w_k(κ cos χ_k + μ sin χ_k) + O(h^{7/6}(|κ|+|μ|) w_k)` on `[c, q_* - r/2]` but hides `κ, μ`, which are the
Airy coefficients of the matching window, and takes the Airy chart radius from `dlgh_airy_compose` (not tunable).  `rk_bulk` is the same proof run on `rk_compose`: it exports the window `RkWinAt` (positions,
chart data, pointwise Airy matching) *with the same `κ, μ`* as the bulk form, and lets the radius be capped by any `r_cap > 0`.  Both facts are what the sharp-constant mass accounting needs
(the band is measured with the bulk form, the turning zone with the Airy form).

**Claim class: proved** (same proof as `dlg_hahn_airy`).
-/

@[expose] public section

open Finset Set FormalResearch.Racah.P3 FormalResearch.DiscreteAiry
open scoped Real

namespace FormalResearch.Special

/-- **Airy window and bulk Liouville-Green form with the same `κ, μ`** (see the module docstring).  The conclusion of `dlg_hahn_airy`, with a free cap `rcap` on the Airy radius, the
chart data of `rk_compose`, and the Airy coefficients `κ, μ` of the window `RkWinAt` being those of the bulk form. -/
theorem rk_bulk {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (a b τ x qs : ℝ) (hqs : 0 < qs) (hτ : τ ^ 2 = 1)
    (hκ : 0 < 1 - τ * x) (hα : 0 < 1 - P * qs ^ 2) (hβ : 0 < 1 - Q * qs ^ 2) (hturn : Phi P Q τ x (qs ^ 2) = 0)
    {c0 : ℝ} (hc0 : 0 < c0) (hc0q : c0 < qs) (hosc : ∀ q ∈ Set.Ico c0 qs, |hrU P Q τ x q| < 1) {rcap : ℝ} (hrcap : 0 < rcap) :
    ∃ (r Cmu ξ0 gmax gmin c1 c2 CA : ℝ), 0 < r ∧ r ≤ rcap ∧ r ≤ qs / 4 ∧ 0 < CA ∧ 0 < Cmu ∧ 0 < ξ0 ∧ 0 < gmax ∧ 0 < gmin ∧ gmin ≤ gmax ∧
      0 < c1 ∧ c1 ≤ c2 ∧
      ∀ c : ℝ, c0 < c → c < qs - r → ∃ δ0 C : ℝ, 0 < δ0 ∧ 0 < C ∧
        ∀ (δ : ℝ) (Y : ℤ → ℝ) (Ymax : ℝ), 0 < δ → δ ≤ δ0 →
          (∀ k : ℤ, 1 ≤ k → jac (hrAk P Q a b (δ ^ 3)) (hrCk P Q τ x a b (δ ^ 3)) Y k = 0) → (∀ k, |Y k| ≤ Ymax) →
          ∃ (J m N : ℤ) (κ μ : ℝ), RkWinAt P Q τ x qs Y Ymax r CA Cmu ξ0 gmin gmax c1 c2 δ J m N κ μ ∧
            ∀ k : ℤ, c ≤ dlgQ (δ ^ 3 / 2) (δ ^ 3) k → dlgQ (δ ^ 3 / 2) (δ ^ 3) k ≤ qs - r / 2 →
              |Y k - (δ ^ 3) ^ (1 / 6 : ℝ) * (1 / √π) * dlgsW (hrA1 P Q) (hrU P Q τ x) (dlgQ (δ ^ 3 / 2) (δ ^ 3) k) *
                  (κ * Real.cos (dlgP (dlgsPhase (hrU P Q τ x) ((c0 + c) / 2)) (δ ^ 3 / 2) (δ ^ 3) k -
                      (∫ s in (c0 + c) / 2..qs, Real.arccos (hrU P Q τ x s)) / δ ^ 3 + π / 4) +
                    μ * Real.sin (dlgP (dlgsPhase (hrU P Q τ x) ((c0 + c) / 2)) (δ ^ 3 / 2) (δ ^ 3) k -
                      (∫ s in (c0 + c) / 2..qs, Real.arccos (hrU P Q τ x s)) / δ ^ 3 + π / 4))| ≤
                C * ((|κ| + |μ|) * ((δ ^ 3) ^ (1 / 6 : ℝ) * δ ^ 3)) *
                  dlgsW (hrA1 P Q) (hrU P Q τ x) (dlgQ (δ ^ 3 / 2) (δ ^ 3) k) := by
  obtain ⟨ρ, hρ, hch⟩ := dlgh_chart (P := P) (Q := Q) τ x qs hqs hκ hα hβ hturn
  obtain ⟨r, δA, CA, Cmu, ξ0, gmax, gmin0, c1, c2, hr, hrρ, hrq4, hδA, hδA1, hCA, hCmu, hξ0, hgmax, hgmin0, hgg, hc1, hc12, HA⟩ :=
    rk_compose hP hQ a b τ x qs hqs hτ hκ hα hβ hturn (ρ := min (min (ρ / 2) (qs - c0)) rcap)
      (lt_min (lt_min (by positivity) (by linarith)) hrcap)
  have hrρ1 : r ≤ ρ / 2 := hrρ.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hrρ2 : r ≤ qs - c0 := hrρ.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hrρ3 : r ≤ rcap := hrρ.trans (min_le_right _ _)
  refine ⟨r, Cmu, ξ0, gmax, gmin0, c1, c2, CA, hr, hrρ3, hrq4, hCA, hCmu, hξ0, hgmax, hgmin0, hgg, hc1, hc12, ?_⟩
  intro c hc0c hcr
  have hc : 0 < c := hc0.trans hc0c
  have hc1pos : 0 < (c0 + c) / 2 := by linarith
  have hcd : c < qs - r / 2 := by linarith
  have hdd0 : qs - r / 2 < qs - r / 4 := by linarith
  have hfacP : ∀ q : ℝ, 0 < q → q ≤ qs → 0 < 1 - P * q ^ 2 := fun q h1 h2 => dlgh_fac hP hα h1 h2
  have hfacQ : ∀ q : ℝ, 0 < q → q ≤ qs → 0 < 1 - Q * q ^ 2 := fun q h1 h2 => dlgh_fac hQ hβ h1 h2
  have hreg : ∀ q ∈ Set.Icc c0 (qs - r / 4), 0 < 1 - P * q ^ 2 ∧ 0 < 1 - Q * q ^ 2 ∧ |hrU P Q τ x q| < 1 :=
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
  refine ⟨min (min δA δ1) (min 1 (r / 4)), Cb * (2 + (1 / (12 * Φ) + CA / gmin)),
    lt_min (lt_min hδA hδ1) (lt_min one_pos (by positivity)), by positivity, ?_⟩
  intro δ Y Ymax hδ hδ0 hrows hbd
  have hδA' : δ ≤ δA := hδ0.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδ1' : δ ≤ δ1 := hδ0.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδone : δ ≤ 1 := hδ0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδr : δ ≤ r / 4 := hδ0.trans ((min_le_right _ _).trans (min_le_right _ _))
  have h3δ : δ ^ 3 ≤ δ := by
    have h1 : δ ^ 2 ≤ 1 := pow_le_one₀ hδ.le hδone
    calc δ ^ 3 = δ * δ ^ 2 := by ring
      _ ≤ δ * 1 := mul_le_mul_of_nonneg_left h1 hδ.le
      _ = δ := mul_one _
  have hδ3r : δ ^ 3 ≤ r / 4 := h3δ.trans hδr
  have hhA := HA (δ ^ 3) Y Ymax (by positivity) (pow_le_pow_left₀ hδ.le hδA' 3) hrows hbd
  obtain ⟨δ', hδ', hδ'A, hδ'3, J, m, N, κ, μ, hWin⟩ := hhA
  have hWin' := hWin
  obtain ⟨hJ1, hJN, hJm, hmN, hwin, h1, h2, h3, h4, h5, h6, hg, hXm, hgl, hgap, hX0m, hXN, hμ2, hpt⟩ := hWin
  have hδeq : δ = δ' := (pow_left_inj₀ hδ.le hδ'.le (by norm_num)).1 hδ'3.symm
  subst hδeq
  have e2 : ∀ k : ℤ, dalQ (δ ^ 3 / 2) δ k = ((k : ℝ) + 1 / 2) * δ ^ 3 := fun k => by unfold dalQ; ring
  have hqJ := dlgh_qJ (qs := qs) (r := r) (δ := δ) (J := J) hδ h1 h2 hδ3r
  have site := dlgh_site_all (P := P) (Q := Q) hP hQ τ x qs hα hβ (c0 := c0) (c := c) (r := r) (ρ := ρ) (δ := δ) (J := J)
    (N := N) (κ := κ) (μ := μ) (Y := Y) (CA := CA) hch hosc hrρ1 hc0c hcr hδ hqJ hΦpos hCA hpt hJN hr hc0
  -- the bulk window of all lattice sites in `[c, qs - r/2]`
  have hlat := dlgh_lattice (c := c) (d := qs - r / 2) hδ
  have hqJ' : ∀ k : ℤ, J ≤ k → k ≤ J + 1 → c ≤ dlgQ (δ ^ 3 / 2) (δ ^ 3) k ∧ dlgQ (δ ^ 3 / 2) (δ ^ 3) k ≤ qs - r / 2 :=
    fun k hk1 hk2 => ⟨by have h := hqJ k hk1 hk2; show c ≤ dalQ (δ ^ 3 / 2) δ k; linarith [h.1], (hqJ k hk1 hk2).2⟩
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
  refine ⟨J, m, N, κ, μ, hWin', fun k hk1 hk2 => ?_⟩
  have hmem := (hlat k).1 ⟨hk1, hk2⟩
  have hres := HM δ Y ⌈(c - δ ^ 3 / 2) / δ ^ 3⌉ (⌊(qs - r / 2 - δ ^ 3 / 2) / δ ^ 3⌋ - 1) J κ μ
    (∫ s in (c0 + c) / 2..qs, Real.arccos (hrU P Q τ x s)) Φ gmin CA hΦpos hgmin hCA.le hδ
    (hδ0.trans ((min_le_left _ _).trans (min_le_right _ _))) hJw.1 (by omega)
    (fun j hj => by
      rw [Finset.mem_Icc] at hj
      exact (hlat j).2 ⟨hj.1, by omega⟩)
    (fun j hj => hrows j (by rw [Finset.mem_Icc] at hj; omega))
    (site J le_rfl (by omega)) (site (J + 1) (by omega) le_rfl)
  have := hres k (by rw [Finset.mem_Icc]; omega)
  exact this

/-- info: 'FormalResearch.Special.rk_bulk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.rk_bulk

end FormalResearch.Special
