module

public import FormalResearch.Special.BulkWindowRk
public import FormalResearch.Special.BulkIndexHahn

/-!
# Bulk window, part 6: the node count of the Airy window of the physical `3j` chain

Instance of `BwnSetup.count` (`BulkWindowRk`) for the integer `3j` chain (`τ = +1`, `0 < x < 1`): the window data and the constants come from
`hahn_chain_kappa_sharp_win` (`κ² δ → 2`, `|μ| ≤ C_μ Y_max e^{-ξ₀/δ³}/δ`), the chart identity from `dlgh_chart`, and all smallness conditions
(`bwn_small`: `E = (1350 + 4C/g_min) δ³ ≪ δ`, `μ/κ ≤ δ³`) hold for `δ³ = 1/N` small.

* `bwn_phase_pos`, `bwn_phase_ge`: `Φ(b₀) > 0`, `Φ(q) ≥ Φ(b₀)` for `q ≤ b₀` (`Φ/δ³ ≥ 16/3` at every site with `q ≤ b₀`, `N` large).
* **`bwn_hahn_window`**: there is `ρ > 0` (depending on `(M, σ, x)` only, `ρ ≤ q_*/2`) such that for every `b₀ ∈ [0, q_*)` there is `ε > 0` with: at every lattice
  node with `h = 1/N ≤ ε` there is a turning site `K + i_w` (`q ∈ [q_*, q_* + h)`, `K = max |M| |σ|`) such that at every site `K + i` with
  `q ∈ [q_* - ρ, b₀]` and `|cos θ_i| > 1/10` (`θ_i = Φ(q_{K+i})/h - π/4`, `bixTheta`) one has `i < i_w` and the number of nodes of `bixU M σ N x` in the bonds
  `i, …, i_w - 1` is exactly `⌊Φ(q_{K+i})/(π h) + 1/4⌋`.

**Claim class: proved** (composition of proved results; axiom guard pinned).  **Not formalised:** `τ = -1`, the half-integer lattice (the same proof with the corresponding window theorems; the integer Racah `6j` chain, `τ = ±1`, is `RacahWindow`); constants uniform in `x` or `(M, σ)`; the junction with the bulk count and the right-end count
(`BulkWindowIndex`).
-/

@[expose] public section

open Finset Set FormalResearch.Racah FormalResearch.Racah.P3 FormalResearch.Wigner FormalResearch.DiscreteAiry
open scoped Real

namespace FormalResearch.Special


/-- `Φ(b₀) > 0` for `0 ≤ b₀ < q_*`, and `Φ(q) ≥ Φ(b₀)` for `0 ≤ q ≤ b₀`. -/
lemma bwn_phase_pos {x b0 : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hb0 : 0 ≤ b0) (hb : b0 < √(1 - x ^ 2)) :
    0 < bkPhase 1 0 1 x (√(1 - x ^ 2)) b0 := by
  set qs := √(1 - x ^ 2) with hqs
  set b' := (b0 + qs) / 2 with hb'
  have hb'1 : b0 < b' := by rw [hb']; linarith
  have hb'2 : b' < qs := by rw [hb']; linarith
  have h1 := (bix_phase_step (x := x) (b := b') (q := b0) (q' := b') hx0 hx1 hb'2 hb0 hb'1.le le_rfl).1
  have h2 := (bwn_phase_bounds hx0 hx1 (hb0.trans hb'1.le) hb'2.le).1
  have hδ : 0 < Real.arccos (x / √(1 - b' ^ 2)) :=
    Real.arccos_pos.2 (bix_lt_one (hb0.trans hb'1.le) hb'2)
  have : 0 < Real.arccos (x / √(1 - b' ^ 2)) * (b' - b0) := mul_pos hδ (by linarith)
  linarith

lemma bwn_phase_ge {x b0 q : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hq : 0 ≤ q) (hqb : q ≤ b0) (hb : b0 < √(1 - x ^ 2)) :
    bkPhase 1 0 1 x (√(1 - x ^ 2)) b0 ≤ bkPhase 1 0 1 x (√(1 - x ^ 2)) q := by
  have h1 := (bix_phase_step (x := x) (b := b0) (q := q) (q' := b0) hx0 hx1 hb hq hqb le_rfl).1
  have hδ : 0 ≤ Real.arccos (x / √(1 - b0 ^ 2)) := Real.arccos_nonneg _
  have : 0 ≤ Real.arccos (x / √(1 - b0 ^ 2)) * (b0 - q) := mul_nonneg hδ (by linarith)
  linarith

/-- Smallness of `δ`: the numerical conditions of `BwnSetup` hold for all small `δ`. -/
lemma bwn_small {C gmin c1 cpos Cmu ξ0 : ℝ} (hC : 0 < C) (hgmin : 0 < gmin) (hc1 : 0 < c1) (hcpos : 0 < cpos)
    (hCmu : 0 < Cmu) (hξ0 : 0 < ξ0) :
    ∃ δs : ℝ, 0 < δs ∧ δs ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δs →
      bwnE C gmin δ < cpos ∧ 8 * bwnE C gmin δ ≤ bwn_c0 * (c1 * δ) ∧ bwnE C gmin δ ^ 2 / δ ^ 2 ≤ bwn_c0 ^ 2 / 2 ∧
      bwnE C gmin δ < δ / 25 ∧ 2 * Cmu * Real.exp (-ξ0 / δ ^ 3) ≤ δ ^ 7 := by
  have hc0 := bwn_c0_pos
  set C1 : ℝ := 1350 + 4 * C / gmin with hC1
  have hC1p : 0 < C1 := by rw [hC1]; positivity
  obtain ⟨δe, hδe, hδe1, hexp⟩ := bwn_exp_small (C := 2 * Cmu) (ξ0 := ξ0) (by positivity) hξ0 7 (by norm_num)
  refine ⟨min δe (min (cpos / (2 * C1)) (min (bwn_c0 * c1 / (8 * C1)) (min (bwn_c0 ^ 2 / (2 * C1 ^ 2)) (1 / (50 * C1))))),
    lt_min hδe (lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity) (by positivity)))),
    (min_le_left _ _).trans hδe1, ?_⟩
  intro δ hδ hδs
  have h1 : δ ≤ δe := hδs.trans (min_le_left _ _)
  have h2 : δ ≤ cpos / (2 * C1) := hδs.trans ((min_le_right _ _).trans (min_le_left _ _))
  have h3 : δ ≤ bwn_c0 * c1 / (8 * C1) := hδs.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have h4 : δ ≤ bwn_c0 ^ 2 / (2 * C1 ^ 2) :=
    hδs.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have h5 : δ ≤ 1 / (50 * C1) :=
    hδs.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hδ1 : δ ≤ 1 := h1.trans hδe1
  have hδ2 : δ ^ 2 ≤ δ := by nlinarith
  have hδ3 : δ ^ 3 ≤ δ := by nlinarith [pow_pos hδ 2]
  have hδ4 : δ ^ 4 ≤ δ := by nlinarith [pow_pos hδ 2, pow_pos hδ 3]
  have hE : bwnE C gmin δ = C1 * δ ^ 3 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hE]
    rw [le_div_iff₀ (by positivity)] at h2
    nlinarith
  · rw [hE]
    rw [le_div_iff₀ (by positivity)] at h3
    have a1 : 8 * (C1 * δ ^ 3) ≤ 8 * C1 * δ * δ := by
      have := mul_le_mul_of_nonneg_left hδ2 (by positivity : (0 : ℝ) ≤ 8 * C1 * δ)
      nlinarith
    have a2 := mul_le_mul_of_nonneg_right h3 hδ.le
    nlinarith
  · rw [hE]
    have : (C1 * δ ^ 3) ^ 2 / δ ^ 2 = C1 ^ 2 * δ ^ 4 := by field_simp
    rw [this]
    rw [le_div_iff₀ (by positivity)] at h4
    nlinarith
  · rw [hE]
    rw [le_div_iff₀ (by positivity)] at h5
    nlinarith
  · exact hexp δ hδ h1


/-- The exponentially small `μ` is `≤ δ³ |κ|`. -/
lemma bwn_mu_bound {Cmu ξ0 δ μ κ : ℝ} (hδ : 0 < δ) (hκabs : 1 ≤ |κ|)
    (hμW : |μ| ≤ Cmu * (2 / δ ^ 3) * Real.exp (-ξ0 / δ ^ 3) / δ)
    (hexp : 2 * Cmu * Real.exp (-ξ0 / δ ^ 3) ≤ δ ^ 7) : |μ| ≤ δ ^ 3 * |κ| := by
  have h1 : |μ| ≤ δ ^ 3 := by
    refine hμW.trans ?_
    have e : Cmu * (2 / δ ^ 3) * Real.exp (-ξ0 / δ ^ 3) / δ = (2 * Cmu * Real.exp (-ξ0 / δ ^ 3)) / δ ^ 4 := by
      field_simp
    rw [e, div_le_iff₀ (by positivity)]
    have : δ ^ 3 * δ ^ 4 = δ ^ 7 := by ring
    rw [this]; exact hexp
  have hδ3 : 0 < δ ^ 3 := by positivity
  calc |μ| ≤ δ ^ 3 := h1
    _ = δ ^ 3 * 1 := by ring
    _ ≤ δ ^ 3 * |κ| := mul_le_mul_of_nonneg_left hκabs hδ3.le

/-- If `(K+1) δ³ ≤ q_*/2` and the turning site has `q ≥ q_*`, then `K < m_w`. -/
lemma bwn_K_lt {K mw : ℤ} {δ qs : ℝ} (hδ : 0 < δ) (hqs : 0 < qs)
    (hqK : ((K : ℝ) + 1) * δ ^ 3 ≤ qs / 2) (hqm1 : qs ≤ bwnQ δ mw) : K < mw := by
  have hδ3p : 0 < δ ^ 3 := by positivity
  have h1 : bwnQ δ K < qs := by
    unfold bwnQ
    have : ((K : ℝ) + 1 / 2) * δ ^ 3 ≤ ((K : ℝ) + 1) * δ ^ 3 := by nlinarith
    linarith
  have h2 : bwnQ δ K < bwnQ δ mw := lt_of_lt_of_le h1 hqm1
  by_contra hc
  push Not at hc
  have := bwnQ_mono hδ hc
  linarith

/-- `δ³ ≤ q_*/(2(K+1))` gives `(K+1) δ³ ≤ q_*/2`. -/
lemma bwn_K_bound {K : ℝ} {δ3 qs : ℝ} (hK : 0 ≤ K) (h : δ3 ≤ qs / (2 * (K + 1))) : (K + 1) * δ3 ≤ qs / 2 := by
  have hp : 0 < K + 1 := by linarith
  have := mul_le_mul_of_nonneg_left h hp.le
  have e : (K + 1) * (qs / (2 * (K + 1))) = qs / 2 := by field_simp
  linarith

/-- Three facts read off an Airy window. -/
lemma bwn_window_facts {x : ℝ} {Y : ℤ → ℝ} {Ymax r C Cmu ξ0 gmin gmax c1 c2 δ κ μ : ℝ} {J mw N' : ℤ}
    (hW : RkWinAt 1 0 1 x (√(1 - x ^ 2)) Y Ymax r C Cmu ξ0 gmin gmax c1 c2 δ J mw N' κ μ) :
    √(1 - x ^ 2) ≤ bwnQ δ mw ∧ bwnQ δ mw < √(1 - x ^ 2) + δ ^ 3 ∧
      |μ| ≤ Cmu * Ymax * Real.exp (-ξ0 / δ ^ 3) / δ := by
  unfold RkWinAt RkWinAtG at hW
  obtain ⟨hJ1, hJN, hJm, hmN, hr, hqJ1, hqJ2, hqm1, hqm2, hqN1, hqN2, hgmax', hXle, hgmin', hstep, hXm, hXN, hμW, hY⟩ := hW
  exact ⟨hqm1, hqm2, hμW⟩

/-- Assembly of `BwnSetup` from a window. -/
lemma bwn_setup_of_window {x : ℝ} {Y : ℤ → ℝ} {Ymax r C Cmu ξ0 gmin gmax c1 c2 δ κ μ ρ ρ0 cpos : ℝ} {J mw N' K : ℤ} {i : ℕ}
    (hW : RkWinAt 1 0 1 x (√(1 - x ^ 2)) Y Ymax r C Cmu ξ0 gmin gmax c1 c2 δ J mw N' κ μ)
    (hx0 : 0 < x) (hx1 : x < 1) (hgmin : 0 < gmin) (hC : 0 < C) (hc1 : 0 < c1) (hc12 : c1 ≤ c2) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hκ : 1 ≤ κ ^ 2 * δ) (hμ : |μ| ≤ δ ^ 3 * |κ|) (hρ : 0 < ρ) (hρr : ρ ≤ r) (hρ0 : ρ < ρ0) (hρ4 : ρ ≤ 1 / 4)
    (hρc : 200 * c2 ^ 3 * ρ ≤ 1)
    (hchart : ∀ q : ℝ, √(1 - x ^ 2) - ρ0 < q → q < √(1 - x ^ 2) →
      langerZeta (hrU 1 0 1 x) (√(1 - x ^ 2)) q < 0 ∧
      2 / 3 * (-langerZeta (hrU 1 0 1 x) (√(1 - x ^ 2)) q) ^ (3 / 2 : ℝ) = bkPhase 1 0 1 x (√(1 - x ^ 2)) q)
    (hcpos : ∀ X ∈ Set.Icc (-1 : ℝ) (1 / 4), cpos ≤ airyAi X)
    (hE1 : bwnE C gmin δ < cpos) (hE2 : 8 * bwnE C gmin δ ≤ bwn_c0 * (c1 * δ))
    (hE3 : bwnE C gmin δ ^ 2 / δ ^ 2 ≤ bwn_c0 ^ 2 / 2) (hE4 : bwnE C gmin δ < δ / 25)
    (hq0 : √(1 - x ^ 2) - ρ ≤ bwnQ δ (K + i)) (hq1 : bwnQ δ (K + i) < √(1 - x ^ 2))
    (hbig : 16 / 3 ≤ bkPhase 1 0 1 x (√(1 - x ^ 2)) (bwnQ δ (K + i)) / δ ^ 3)
    (hcos : 1 / 10 < |Real.cos (bkPhase 1 0 1 x (√(1 - x ^ 2)) (bwnQ δ (K + i)) / δ ^ 3 - π / 4)|) :
    BwnSetup x Y r C gmin c1 c2 δ κ μ ρ ρ0 cpos J mw N' K i := by
  unfold RkWinAt RkWinAtG at hW
  obtain ⟨hJ1, hJN, hJm, hmN, hr, hqJ1, hqJ2, hqm1, hqm2, hqN1, hqN2, hgmax', hXle, hgmin', hstep, hXm, hXN, hμW, hY⟩ := hW
  exact ⟨hx0, hx1, hgmin, hC, hc1, hc12, hδ, hδ1, hκ, hμ, hρ, hρr, hρ0, hρ4, hρc, hchart, hcpos, hE1, hE2, hE3, hE4,
    hJ1, hJm, hmN, hqJ2, hqm1, hqm2, fun k hk => hXle k hk, fun k hk => hgmin' k hk, fun k hk => hstep k hk, hXm,
    fun k hk => hY k hk, hq0, hq1, hbig, hcos⟩

/-- **The node count of the Airy window of the physical `3j` chain** (`τ = +1`, integer lattice).  There is `ρ > 0` (depending on
`(M, σ, x)` only) such that for every `b₀ ∈ [0, q_*)` there is `ε > 0` with: at every lattice node with `1/N ≤ ε` there is a turning site
`K + i_w` (`q ∈ [q_*, q_* + 1/N)`, `K = max |M| |σ|`) such that at every site `K + i` with `q ∈ [q_* - ρ, b₀]` and `|cos θ_i| > 1/10`
the nodes of the chain in the bonds `i, …, i_w - 1` number exactly `⌊Φ(q_{K+i})/(π h) + 1/4⌋`. -/
theorem bwn_hahn_window (M σ : ℤ) (x : ℚ) (hx0 : 0 < x) (hx1 : x < 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ √(1 - (x : ℝ) ^ 2) / 2 ∧ ∀ b0 : ℝ, 0 ≤ b0 → b0 < √(1 - (x : ℝ) ^ 2) → ∃ ε : ℝ, 0 < ε ∧
      ∀ (N : ℤ) (n : ℕ), max |M| |σ| < N ∧ (n : ℤ) < N - max |M| |σ| ∧ xLat (M : ℚ) (σ : ℚ) (N : ℚ) n = x →
        1 / (N : ℝ) ≤ ε → ∃ iw : ℕ, √(1 - (x : ℝ) ^ 2) ≤ bixQ N (max |M| |σ| + (iw : ℤ)) ∧
          bixQ N (max |M| |σ| + (iw : ℤ)) < √(1 - (x : ℝ) ^ 2) + 1 / (N : ℝ) ∧
          ∀ i : ℕ, √(1 - (x : ℝ) ^ 2) - ρ ≤ bixQ N (max |M| |σ| + (i : ℤ)) → bixQ N (max |M| |σ| + (i : ℤ)) ≤ b0 →
            1 / 10 < |Real.cos (bixTheta (x : ℝ) N (max |M| |σ| + (i : ℤ)))| →
            i < iw ∧ ((∑ j ∈ Ico i iw, bix_c (bixU M σ N x) j : ℕ) : ℤ) =
              ⌊bkPhase 1 0 1 (x : ℝ) (√(1 - (x : ℝ) ^ 2)) (bixQ N (max |M| |σ| + (i : ℤ))) / (π * (1 / (N : ℝ))) + 1 / 4⌋ := by
  have hx0' : (0 : ℝ) < x := by exact_mod_cast hx0
  have hx1' : (x : ℝ) < 1 := by exact_mod_cast hx1
  have hxabs : |(x : ℝ)| < 1 := abs_lt.2 ⟨by linarith, hx1'⟩
  obtain ⟨r, Cmu, ξ0, gmax, gmin, c1, c2, CA, hr0, hrq, hCA, hCmu, hξ0, hgmax, hgmin, hgg, hc1, hc12, H⟩ :=
    hahn_chain_kappa_sharp_win M σ x hx0 hx1
  obtain ⟨hqs, hτ, hκ, hα, hβ, hturn⟩ := bkh_geom (τ := 1) (x := (x : ℝ)) (Or.inl ⟨rfl, hx0'⟩) hxabs
  obtain ⟨ρ0, hρ0, hch⟩ := dlgh_chart (P := 1) (Q := 0) 1 (x : ℝ) (√(1 - (x : ℝ) ^ 2)) hqs hκ hα hβ hturn
  set qs : ℝ := √(1 - (x : ℝ) ^ 2) with hqsdef
  obtain ⟨cpos, hcposp, hcpos⟩ := bwn_pos_const
  obtain ⟨δs, hδs0, hδs1, hsmall⟩ := bwn_small hCA hgmin hc1 hcposp hCmu hξ0
  obtain ⟨ε1, hε1, H1⟩ := H 1 one_pos
  have hc2p : 0 < c2 := lt_of_lt_of_le hc1 hc12
  set ρ : ℝ := min (min r (ρ0 / 2)) (min (min (1 / 4) (1 / (200 * c2 ^ 3))) (qs / 2)) with hρdef
  have hρp : 0 < ρ := lt_min (lt_min hr0 (by linarith)) (lt_min (lt_min (by norm_num) (by positivity)) (by linarith))
  have hρr : ρ ≤ r := (min_le_left _ _).trans (min_le_left _ _)
  have hρρ0 : ρ < ρ0 := lt_of_le_of_lt ((min_le_left _ _).trans (min_le_right _ _)) (by linarith)
  have hρ4 : ρ ≤ 1 / 4 := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hρc : 200 * c2 ^ 3 * ρ ≤ 1 := by
    have : ρ ≤ 1 / (200 * c2 ^ 3) := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
    rw [le_div_iff₀ (by positivity)] at this; linarith
  have hρq : ρ ≤ qs / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ρ, hρp, hρq, ?_⟩
  intro b0 hb00 hb0q
  have hΦ0 := bwn_phase_pos hx0' hx1' hb00 hb0q
  set Φ0 := bkPhase 1 0 1 (x : ℝ) qs b0 with hΦ0def
  set K : ℤ := max |M| |σ| with hK
  have hK0 : 0 ≤ K := le_trans (abs_nonneg M) (le_max_left _ _)
  refine ⟨min ε1 (min (δs ^ 3) (min (3 * Φ0 / 16) (qs / (2 * ((K : ℝ) + 1))))), lt_min hε1 (lt_min (by positivity) (lt_min (by positivity) (by
    have : (0 : ℝ) < (K : ℝ) + 1 := by have : (0 : ℝ) ≤ K := by exact_mod_cast hK0
                                       linarith
    positivity))), ?_⟩
  intro N n hnode hNε
  have hNε1 : 1 / (N : ℝ) ≤ ε1 := hNε.trans (min_le_left _ _)
  have hNεδ : 1 / (N : ℝ) ≤ δs ^ 3 := hNε.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hNεΦ : 1 / (N : ℝ) ≤ 3 * Φ0 / 16 := hNε.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hNεK : 1 / (N : ℝ) ≤ qs / (2 * ((K : ℝ) + 1)) :=
    hNε.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨δ, hδ, hδ3, J, mw, N', κ, μ, hW, hκs⟩ := H1 N n hnode hNε1
  have hδ3' : δ ^ 3 = 1 / (N : ℝ) := hδ3
  have hδs' : δ ≤ δs := by
    refine le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) hδs0.le ?_
    rw [hδ3']; exact hNεδ
  have hδ1 : δ ≤ 1 := hδs'.trans hδs1
  obtain ⟨hE1, hE2, hE3, hE4, hexp⟩ := hsmall δ hδ hδs'
  have hκ1 : 1 ≤ κ ^ 2 * δ := by have := (abs_le.1 hκs).1; linarith
  have hκabs : 1 ≤ |κ| := by
    have : 1 ≤ κ ^ 2 := by nlinarith [sq_nonneg κ]
    exact (one_le_sq_iff_one_le_abs κ).1 this
  have hδ3p : 0 < δ ^ 3 := by positivity
  obtain ⟨hqm1, hqm2, hμW⟩ := bwn_window_facts hW
  have hμ : |μ| ≤ δ ^ 3 * |κ| := by
    exact bwn_mu_bound hδ hκabs hμW hexp
  have hKmw : K < mw := by
    have hK1 : ((K : ℝ) + 1) * δ ^ 3 ≤ qs / 2 := bwn_K_bound (by exact_mod_cast hK0) (hδ3'.le.trans hNεK)
    exact bwn_K_lt hδ hqs hK1 hqm1
  have hbQ : ∀ k : ℤ, bixQ N k = bwnQ δ k := by intro k; unfold bixQ bwnQ; rw [hδ3']
  have hqm : qs ≤ bwnQ δ mw ∧ bwnQ δ mw < qs + δ ^ 3 := ⟨hqm1, hqm2⟩
  refine ⟨(mw - K).toNat, ?_, ?_, ?_⟩
  · have : K + ((mw - K).toNat : ℤ) = mw := by omega
    rw [this, hbQ]; exact hqm.1
  · have : K + ((mw - K).toNat : ℤ) = mw := by omega
    rw [this, hbQ, ← hδ3']; exact hqm.2
  · intro i hq0 hq1 hcos
    rw [hbQ] at hq0 hq1
    have hq1' : bwnQ δ (K + i) < qs := lt_of_le_of_lt hq1 hb0q
    have hqpos : 0 ≤ bwnQ δ (K + i) := by
      unfold bwnQ
      have : (0 : ℝ) ≤ ((K + i : ℤ) : ℝ) := by
        have : (0 : ℤ) ≤ K + i := by omega
        exact_mod_cast this
      positivity
    have hΦge := bwn_phase_ge hx0' hx1' hqpos hq1 hb0q
    have hbig : 16 / 3 ≤ bkPhase 1 0 1 (x : ℝ) qs (bwnQ δ (K + i)) / δ ^ 3 := by
      rw [le_div_iff₀ hδ3p]
      have : δ ^ 3 ≤ 3 * Φ0 / 16 := hδ3'.le.trans hNεΦ
      linarith
    have hcos' : 1 / 10 < |Real.cos (bkPhase 1 0 1 (x : ℝ) qs (bwnQ δ (K + i)) / δ ^ 3 - π / 4)| := by
      unfold bixTheta at hcos
      rw [hbQ, ← hδ3'] at hcos
      exact hcos
    have P := bwn_setup_of_window (K := K) (i := i) (ρ := ρ) (ρ0 := ρ0) (cpos := cpos) hW hx0' hx1' hgmin hCA hc1 hc12 hδ hδ1 hκ1 hμ
      hρp hρr hρρ0 hρ4 hρc (fun q h1 h2 => by
        obtain ⟨a1, a2, -⟩ := hch q h1 h2
        exact ⟨a1, a2⟩) hcpos hE1 hE2 hE3 hE4 hq0 hq1' hbig hcos'
    obtain ⟨hlt, hcount⟩ := P.count
    refine ⟨by omega, ?_⟩
    have e1 : bixU M σ N x = fun j : ℕ => hahn3jY M σ N x (K + j) := rfl
    rw [e1, hcount, hbQ, ← hδ3']


/-- info: 'FormalResearch.Special.bwn_hahn_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.bwn_hahn_window

end FormalResearch.Special
