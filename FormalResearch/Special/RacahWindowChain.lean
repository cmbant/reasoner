module

public import FormalResearch.Special.RacahWindowSetup
public import FormalResearch.Special.BulkKappaRacahInst
public import FormalResearch.Special.BulkWindowHahn

/-!
# Racah window, part 3: the node count of the Airy window of the physical `6j` chain (integer data, `τ = ±1`)

Instance of `RwnSetup.count` (`RacahWindowSetup`) for the integer `6j` chain of shape `(α, β, x)`, `P = 1/(4α²)`, `Q = 1/(4β²)`, `q_* = racahQs α β x`, lattice `q_k = (k + 1/2) h`, `h = δ³` (`rwQ`; the
abstract `rwn_window_of_out` is for any `θ ∈ [0, 1]`), first site `K = max |m| |n|`, and the chain `Y_k = u_k Ŷ_k` with the sign twist `u` (`u ≡ 1` for `τ = +1`, `u_k = (-1)^k` for `τ = -1`, the twisted
chain; `rwY`).  The data `RwData` collect the hypotheses of `bk_racah_int` (`BulkKappaRacah`).  The window data and the constants come from `bk_racah_int` (`BkOut`: window of every family member and
`|κ²δ - 2| ≤ τ'` for every window), the chart identity from `dlgh_chart`, the geometry from `RwGeo` (`RacahWindowGeom`), and the smallness conditions from `bwn_small`, `bwn_mu_bound` (`BulkWindowHahn`).

* **`rwn_racah_window`**: there is `ρ > 0` (depending on `(α, β, x, m, n)` only, `ρ ≤ q_*/2`) such that for every `b₀ ∈ [0, q_*)` there is `ε > 0` with: for every finite Racah system with
  `A h = α`, `B h = β`, `cos = x`, `h ≤ ε`, there is a turning site `K + i_w` (`q ∈ [q_*, q_* + h)`) such that at every site `K + j` with `q ∈ [q_* - ρ, b₀]` and `|cos θ_j| > 1/10`
  (`θ_j = Φ(q_{K+j})/h - π/4`, `rwTheta`) one has `j < i_w` and the number of nodes of `s ↦ Y_{K+s}` in the bonds `j, …, i_w - 1` is exactly `⌊Φ(q_{K+j})/(π h) + 1/4⌋`.

**Claim class: proved** (composition of proved results; axiom guard pinned).  **Not formalised:** the half-integer lattice (the same proof with `bk_racah_half`); uniformity of `(ρ, ε)` in
`(α, β, x, m, n)`; the right end and the bulk (`RacahWindowIndex`).
-/

@[expose] public section

open Finset Set FormalResearch.Racah FormalResearch.Racah.SixJ FormalResearch.Racah.P3 FormalResearch.Wigner FormalResearch.DiscreteAiry
open scoped Real

namespace FormalResearch.Special

/-- The lattice site `q_k = (k + θ) h` (`θ = 1/2`: integer `6j` data; `θ = 1`: half-integer data). -/
noncomputable def rwQ (θ h : ℝ) (k : ℤ) : ℝ := ((k : ℝ) + θ) * h

/-- The Bohr-Sommerfeld phase `θ_k = Φ(q_k)/h - π/4`. -/
noncomputable def rwTheta (P Q τ x qs θ h : ℝ) (k : ℤ) : ℝ := bkPhase P Q τ x qs (rwQ θ h k) / h - π / 4

lemma rwQ_eq (θ δ : ℝ) (k : ℤ) : rwQ θ (δ ^ 3) k = rwnQ θ δ k := rfl

lemma rwQ_succ (θ h : ℝ) (k : ℤ) : rwQ θ h (k + 1) = rwQ θ h k + h := by unfold rwQ; push_cast; ring

lemma rwQ_mono {θ h : ℝ} (hh : 0 < h) {k k' : ℤ} (hk : k ≤ k') : rwQ θ h k ≤ rwQ θ h k' := by
  unfold rwQ
  have : (k : ℝ) ≤ k' := by exact_mod_cast hk
  nlinarith

/-- Assembly of `RwnSetup` from a window. -/
lemma rwn_setup_of_window {P Q τ x qs θ : ℝ} {Y : ℤ → ℝ} {Ymax r C Cmu ξ0 gmin gmax c1 c2 δ κ μ ρ ρ0 cpos : ℝ} {J mw N' K : ℤ} {i : ℕ}
    (hW : RkWinAtG θ (θ * δ ^ 3) P Q τ x qs Y Ymax r C Cmu ξ0 gmin gmax c1 c2 δ J mw N' κ μ) (hθ : 0 ≤ θ)
    (hqs : 0 < qs) (hphase : ∀ q : ℝ, qs - ρ0 < q → q < qs → bkPhase P Q τ x qs q ≤ π / 2 * (qs - q))
    (hgmin : 0 < gmin) (hC : 0 < C) (hc1 : 0 < c1) (hc12 : c1 ≤ c2) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hκ : 1 ≤ κ ^ 2 * δ) (hμ : |μ| ≤ δ ^ 3 * |κ|) (hρ : 0 < ρ) (hρr : ρ ≤ r) (hρ0 : ρ < ρ0) (hρ4 : ρ ≤ 1 / 4)
    (hρc : 200 * c2 ^ 3 * ρ ≤ 1)
    (hchart : ∀ q : ℝ, qs - ρ0 < q → q < qs →
      langerZeta (hrU P Q τ x) qs q < 0 ∧
      2 / 3 * (-langerZeta (hrU P Q τ x) qs q) ^ (3 / 2 : ℝ) = bkPhase P Q τ x qs q)
    (hcpos : ∀ X ∈ Set.Icc (-1 : ℝ) (1 / 4), cpos ≤ airyAi X)
    (hE1 : bwnE C gmin δ < cpos) (hE2 : 8 * bwnE C gmin δ ≤ bwn_c0 * (c1 * δ))
    (hE3 : bwnE C gmin δ ^ 2 / δ ^ 2 ≤ bwn_c0 ^ 2 / 2) (hE4 : bwnE C gmin δ < δ / 25)
    (hq0 : qs - ρ ≤ rwnQ θ δ (K + i)) (hq1 : rwnQ θ δ (K + i) < qs)
    (hbig : 16 / 3 ≤ bkPhase P Q τ x qs (rwnQ θ δ (K + i)) / δ ^ 3)
    (hcos : 1 / 10 < |Real.cos (bkPhase P Q τ x qs (rwnQ θ δ (K + i)) / δ ^ 3 - π / 4)|) :
    RwnSetup P Q τ x qs θ Y r C gmin c1 c2 δ κ μ ρ ρ0 cpos J mw N' K i := by
  unfold RkWinAtG at hW
  obtain ⟨hJ1, hJN, hJm, hmN, hr, hqJ1, hqJ2, hqm1, hqm2, hqN1, hqN2, hgmax', hXle, hgmin', hstep, hXm, hXN, hμW, hY⟩ := hW
  exact ⟨hqs, hθ, hphase, hgmin, hC, hc1, hc12, hδ, hδ1, hκ, hμ, hρ, hρr, hρ0, hρ4, hρc, hchart, hcpos, hE1, hE2, hE3, hE4,
    hJ1, hJm, hmN, hqJ2, hqm1, hqm2, fun k hk => hXle k hk, fun k hk => hgmin' k hk, fun k hk => hstep k hk, hXm,
    fun k hk => hY k hk, hq0, hq1, hbig, hcos⟩

/-- The part of `rwn_window_of_out` after the constants are fixed: the count of an Airy window of `RkWinAtG` form at the sites of `[q_* - ρ, b₀]`. -/
lemma rwn_core {P Q τ x qs θ r C Cmu ξ0 gmin gmax c1 c2 δ κ μ ρ ρ0 cpos b0 Ymax : ℝ} {Y : ℤ → ℝ} {J mw N' K : ℤ}
    (hqs : 0 < qs) (G : RwGeo P Q τ x qs) (hθ : 0 ≤ θ) (hK : 0 ≤ K)
    (hW : RkWinAtG θ (θ * δ ^ 3) P Q τ x qs Y Ymax r C Cmu ξ0 gmin gmax c1 c2 δ J mw N' κ μ)
    (hphase : ∀ q : ℝ, qs - ρ0 < q → q < qs → bkPhase P Q τ x qs q ≤ π / 2 * (qs - q))
    (hgmin : 0 < gmin) (hC : 0 < C) (hc1 : 0 < c1) (hc12 : c1 ≤ c2) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hκ : 1 ≤ κ ^ 2 * δ) (hμ : |μ| ≤ δ ^ 3 * |κ|) (hρ : 0 < ρ) (hρr : ρ ≤ r) (hρ0 : ρ < ρ0) (hρ4 : ρ ≤ 1 / 4)
    (hρc : 200 * c2 ^ 3 * ρ ≤ 1)
    (hchart : ∀ q : ℝ, qs - ρ0 < q → q < qs →
      langerZeta (hrU P Q τ x) qs q < 0 ∧
      2 / 3 * (-langerZeta (hrU P Q τ x) qs q) ^ (3 / 2 : ℝ) = bkPhase P Q τ x qs q)
    (hcpos : ∀ X ∈ Set.Icc (-1 : ℝ) (1 / 4), cpos ≤ airyAi X)
    (hE1 : bwnE C gmin δ < cpos) (hE2 : 8 * bwnE C gmin δ ≤ bwn_c0 * (c1 * δ))
    (hE3 : bwnE C gmin δ ^ 2 / δ ^ 2 ≤ bwn_c0 ^ 2 / 2) (hE4 : bwnE C gmin δ < δ / 25)
    (hb0q : b0 < qs) (hqm1 : qs ≤ rwnQ θ δ mw) (hqm2 : rwnQ θ δ mw < qs + δ ^ 3) (hKmw : K < mw)
    (hΦ : 16 / 3 * δ ^ 3 ≤ bkPhase P Q τ x qs b0) :
    ∃ iw : ℕ, qs ≤ rwQ θ (δ ^ 3) (K + (iw : ℤ)) ∧ rwQ θ (δ ^ 3) (K + (iw : ℤ)) < qs + δ ^ 3 ∧
      ∀ j : ℕ, qs - ρ ≤ rwQ θ (δ ^ 3) (K + (j : ℤ)) → rwQ θ (δ ^ 3) (K + (j : ℤ)) ≤ b0 →
        1 / 10 < |Real.cos (rwTheta P Q τ x qs θ (δ ^ 3) (K + (j : ℤ)))| →
        j < iw ∧ ((∑ t ∈ Ico j iw, bix_c (fun s : ℕ => Y (K + (s : ℤ))) t : ℕ) : ℤ) =
          ⌊bkPhase P Q τ x qs (rwQ θ (δ ^ 3) (K + (j : ℤ))) / (π * δ ^ 3) + 1 / 4⌋ := by
  have hδ3p : 0 < δ ^ 3 := by positivity
  refine ⟨(mw - K).toNat, ?_, ?_, ?_⟩
  · have : K + ((mw - K).toNat : ℤ) = mw := by omega
    rw [this, rwQ_eq]; exact hqm1
  · have : K + ((mw - K).toNat : ℤ) = mw := by omega
    rw [this, rwQ_eq]; exact hqm2
  · intro i hq0 hq1 hcos
    rw [rwQ_eq] at hq0 hq1
    have hq1' : rwnQ θ δ (K + i) < qs := lt_of_le_of_lt hq1 hb0q
    have hqpos : 0 ≤ rwnQ θ δ (K + i) := by
      unfold rwnQ
      have : (0 : ℝ) ≤ ((K + i : ℤ) : ℝ) := by
        have : (0 : ℤ) ≤ K + i := by omega
        exact_mod_cast this
      positivity
    have hΦge := G.phase_ge hqpos hq1 hb0q
    have hbig : 16 / 3 ≤ bkPhase P Q τ x qs (rwnQ θ δ (K + i)) / δ ^ 3 := by
      rw [le_div_iff₀ hδ3p]
      linarith
    have hcos' : 1 / 10 < |Real.cos (bkPhase P Q τ x qs (rwnQ θ δ (K + i)) / δ ^ 3 - π / 4)| := by
      unfold rwTheta at hcos
      rw [rwQ_eq] at hcos
      exact hcos
    have S := rwn_setup_of_window (K := K) (i := i) (ρ := ρ) (ρ0 := ρ0) (cpos := cpos) hW hθ hqs hphase hgmin hC hc1 hc12 hδ hδ1 hκ hμ
      hρ hρr hρ0 hρ4 hρc hchart hcpos hE1 hE2 hE3 hE4 hq0 hq1' hbig hcos'
    obtain ⟨hlt, hcount⟩ := S.count
    refine ⟨by omega, ?_⟩
    rw [hcount, rwQ_eq]

/-- The chart radius: `Langer`'s chart is valid and `Φ ≤ (π/2)(q_* - q)` on `(q_* - ρ₀, q_*)`. -/
lemma rwn_chart_data {P Q τ x qs : ℝ} (G : RwGeo P Q τ x qs) :
    ∃ ρ0 : ℝ, 0 < ρ0 ∧
      (∀ q : ℝ, qs - ρ0 < q → q < qs → langerZeta (hrU P Q τ x) qs q < 0 ∧
        2 / 3 * (-langerZeta (hrU P Q τ x) qs q) ^ (3 / 2 : ℝ) = bkPhase P Q τ x qs q) ∧
      (∀ q : ℝ, qs - ρ0 < q → q < qs → bkPhase P Q τ x qs q ≤ π / 2 * (qs - q)) := by
  have hκ : 0 < 1 - τ * x := by
    rcases G.tau_cases with h | h <;> rw [h] <;> linarith [G.hx.1, G.hx.2]
  obtain ⟨ρ0c, hρ0c, hch⟩ := dlgh_chart (P := P) (Q := Q) τ x qs G.hqs hκ G.hα G.hβ G.hturn
  obtain ⟨ρu, hρu, hρuq, hphu⟩ := G.near_turn
  refine ⟨min ρ0c ρu, lt_min hρ0c hρu, ?_, ?_⟩
  · intro q h1 h2
    have : qs - ρ0c < q := by
      have : min ρ0c ρu ≤ ρ0c := min_le_left _ _
      linarith
    obtain ⟨a1, a2, -⟩ := hch q this h2
    exact ⟨a1, a2⟩
  · intro q h1 h2
    have : min ρ0c ρu ≤ ρu := min_le_right _ _
    exact hphu q (by linarith) h2.le

/-- The overlap radius `ρ`. -/
lemma rwn_rho {r c2 ρ0 qs : ℝ} (hr0 : 0 < r) (hc2 : 0 < c2) (hρ0 : 0 < ρ0) (hqs : 0 < qs) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ r ∧ ρ < ρ0 ∧ ρ ≤ 1 / 4 ∧ 200 * c2 ^ 3 * ρ ≤ 1 ∧ ρ ≤ qs / 2 := by
  refine ⟨min (min r (ρ0 / 2)) (min (min (1 / 4) (1 / (200 * c2 ^ 3))) (qs / 2)),
    lt_min (lt_min hr0 (by linarith)) (lt_min (lt_min (by norm_num) (by positivity)) (by linarith)),
    (min_le_left _ _).trans (min_le_left _ _),
    lt_of_le_of_lt ((min_le_left _ _).trans (min_le_right _ _)) (by linarith),
    (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)), ?_, (min_le_right _ _).trans (min_le_right _ _)⟩
  have : min (min r (ρ0 / 2)) (min (min (1 / 4) (1 / (200 * c2 ^ 3))) (qs / 2)) ≤ 1 / (200 * c2 ^ 3) :=
    (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  rw [le_div_iff₀ (by positivity)] at this; linarith

/-- The exponentially small `μ`, with the amplitude constant `cs`. -/
lemma rwn_mu {Cmu ξ0 cs δ μ κ : ℝ} (hδ : 0 < δ) (hκabs : 1 ≤ |κ|)
    (hμW : |μ| ≤ Cmu * (cs / δ ^ 3) * Real.exp (-ξ0 / δ ^ 3) / δ)
    (hexp : 2 * (cs * Cmu / 2) * Real.exp (-ξ0 / δ ^ 3) ≤ δ ^ 7) : |μ| ≤ δ ^ 3 * |κ| := by
  refine bwn_mu_bound (Cmu := cs * Cmu / 2) (ξ0 := ξ0) hδ hκabs ?_ hexp
  have e : cs * Cmu / 2 * (2 / δ ^ 3) * Real.exp (-ξ0 / δ ^ 3) / δ = Cmu * (cs / δ ^ 3) * Real.exp (-ξ0 / δ ^ 3) / δ := by
    field_simp
  rw [e]; exact hμW

/-- **The node count of the Airy window of a family of chains with a `BkOut` window** (`τ = ±1`).  Given the window data `Hout` of a family `Fam`
(`BkOut`, e.g. the `6j` chains of `bk_racah_int`), there is `ρ > 0` (depending on the data only, `ρ ≤ q_*/2`) such that for every `b₀ ∈ [0, q_*)`, every first site `K ≥ 0`
there is `ε > 0` with: for every member with `h ≤ ε` there is a turning site `K + i_w` (`q ∈ [q_*, q_* + h)`) such that at every site `K + j` with `q ∈ [q_* - ρ, b₀]` and
`|cos θ_j| > 1/10` one has `j < i_w` and the nodes of `s ↦ Y_{K+s}` in the bonds `j, …, i_w - 1` number exactly `⌊Φ(q_{K+j})/(π h) + 1/4⌋`. -/
theorem rwn_window_of_out {P Q τ x qs θ : ℝ} {q₀ : ℝ → ℝ} (hq₀ : ∀ δ, q₀ δ = θ * δ ^ 3) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (G : RwGeo P Q τ x qs)
    {Fam : ℝ → (ℤ → ℝ) → ℝ → Prop} {r Cmu ξ0 gmax gmin c1 c2 CA δA : ℝ}
    (hr0 : 0 < r) (hCA : 0 < CA) (hCmu : 0 < Cmu) (hξ0 : 0 < ξ0) (hgmin : 0 < gmin) (hc1 : 0 < c1) (hc12 : c1 ≤ c2) (hδA : 0 < δA)
    (Hout : BkOut θ q₀ P Q τ x qs Fam r Cmu ξ0 gmax gmin c1 c2 CA δA) (K : ℤ) (hK : 0 ≤ K) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ qs / 2 ∧ ∀ b0 : ℝ, 0 ≤ b0 → b0 < qs → ∃ ε : ℝ, 0 < ε ∧
      ∀ (h : ℝ) (Y : ℤ → ℝ) (M : ℝ), Fam h Y M → 0 < h → h ≤ ε →
        ∃ iw : ℕ, qs ≤ rwQ θ h (K + (iw : ℤ)) ∧ rwQ θ h (K + (iw : ℤ)) < qs + h ∧
          ∀ j : ℕ, qs - ρ ≤ rwQ θ h (K + (j : ℤ)) → rwQ θ h (K + (j : ℤ)) ≤ b0 →
            1 / 10 < |Real.cos (rwTheta P Q τ x qs θ h (K + (j : ℤ)))| →
            j < iw ∧ ((∑ t ∈ Ico j iw, bix_c (fun s : ℕ => Y (K + (s : ℤ))) t : ℕ) : ℤ) =
              ⌊bkPhase P Q τ x qs (rwQ θ h (K + (j : ℤ))) / (π * h) + 1 / 4⌋ := by
  have hqs := G.hqs
  obtain ⟨ρ0, hρ0p, hchart, hphase⟩ := rwn_chart_data G
  obtain ⟨cpos, hcposp, hcpos⟩ := bwn_pos_const
  have hcsp : 0 < 1 / √(rkS P Q x) + 1 := by positivity
  obtain ⟨δs, hδs0, hδs1, hsmall⟩ := bwn_small hCA hgmin hc1 hcposp
    (by positivity : 0 < (1 / √(rkS P Q x) + 1) * Cmu / 2) hξ0
  obtain ⟨ε1, hε1, H1⟩ := Hout.2.1 1 one_pos
  have hc2p : 0 < c2 := lt_of_lt_of_le hc1 hc12
  obtain ⟨ρ, hρp, hρr, hρρ0, hρ4, hρc, hρq⟩ := rwn_rho hr0 hc2p hρ0p hqs
  refine ⟨ρ, hρp, hρq, ?_⟩
  intro b0 hb00 hb0q
  have hΦ0 := G.phase_pos hb00 hb0q
  have hKp : (0 : ℝ) < (K : ℝ) + 1 := by
    have : (0 : ℝ) ≤ K := by exact_mod_cast hK
    linarith
  refine ⟨min ε1 (min (δA ^ 3) (min (δs ^ 3) (min (3 * bkPhase P Q τ x qs b0 / 16) (qs / (2 * ((K : ℝ) + 1)))))),
    lt_min hε1 (lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity) (by positivity)))), ?_⟩
  intro h Y M hfam hh hhε
  have hhε1 : h ≤ ε1 := hhε.trans (min_le_left _ _)
  have hhA : h ≤ δA ^ 3 := hhε.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hhδ : h ≤ δs ^ 3 := hhε.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hhΦ : h ≤ 3 * bkPhase P Q τ x qs b0 / 16 :=
    hhε.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hhK : h ≤ qs / (2 * ((K : ℝ) + 1)) :=
    hhε.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  obtain ⟨δ, hδ, hδ3, J, mw, N', κ, μ, hW⟩ := Hout.1 h Y M hfam hh hhA
  have hκs := H1 h Y M hfam hh hhε1 δ J mw N' κ μ hδ hδ3 hW
  rw [hq₀ δ] at hW
  subst hδ3
  have hδs' : δ ≤ δs := le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) hδs0.le hhδ
  have hδ1 : δ ≤ 1 := hδs'.trans hδs1
  obtain ⟨hE1, hE2, hE3, hE4, hexp⟩ := hsmall δ hδ hδs'
  have hκ1 : 1 ≤ κ ^ 2 * δ := by have := (abs_le.1 hκs).1; linarith
  have hκabs : 1 ≤ |κ| := by
    have : 1 ≤ κ ^ 2 := by nlinarith [sq_nonneg κ]
    exact (one_le_sq_iff_one_le_abs κ).1 this
  have hδ3p : 0 < δ ^ 3 := by positivity
  have hfacts : qs ≤ rwnQ θ δ mw ∧ rwnQ θ δ mw < qs + δ ^ 3 ∧
      |μ| ≤ Cmu * ((1 / √(rkS P Q x) + 1) / δ ^ 3) * Real.exp (-ξ0 / δ ^ 3) / δ := by
    unfold RkWinAtG at hW
    obtain ⟨hJ1, hJN, hJm, hmN, hr, hqJ1, hqJ2, hqm1, hqm2, hqN1, hqN2, hgmax', hXle, hgmin', hstep, hXm, hXN, hμW, hY⟩ := hW
    exact ⟨hqm1, hqm2, hμW⟩
  obtain ⟨hqm1, hqm2, hμW⟩ := hfacts
  have hμ : |μ| ≤ δ ^ 3 * |κ| := rwn_mu hδ hκabs hμW hexp
  have hKmw : K < mw := by
    have hK1 : ((K : ℝ) + 1) * δ ^ 3 ≤ qs / 2 := by
      have := mul_le_mul_of_nonneg_left hhK hKp.le
      have e : ((K : ℝ) + 1) * (qs / (2 * ((K : ℝ) + 1))) = qs / 2 := by field_simp
      linarith
    have h1 : rwnQ θ δ K < qs := by
      unfold rwnQ
      have : ((K : ℝ) + θ) * δ ^ 3 ≤ ((K : ℝ) + 1) * δ ^ 3 := by nlinarith
      linarith
    by_contra hc
    push Not at hc
    have := rwnQ_mono θ hδ hc
    exact absurd (hqm1.trans this) (not_le.2 h1)
  refine rwn_core hqs G hθ hK hW hphase hgmin hCA hc1 hc12 hδ hδ1 hκ1 hμ hρp hρr hρρ0 hρ4 hρc hchart hcpos hE1 hE2 hE3 hE4
    hb0q hqm1 hqm2 hKmw ?_
  exact le_trans (mul_le_mul_of_nonneg_left hhΦ (by norm_num : (0 : ℝ) ≤ 16 / 3)) (le_of_eq (by ring))

/-- The (twisted) natural-gauge `6j` chain `Y_k = u_k Ŷ_k`. -/
noncomputable def rwY (u : ℤ → ℝ) (a b c m n : ℤ) (k : ℤ) : ℝ := u k * racah6jY a b c m n k

/-- The hypotheses of `bk_racah_int` for the integer `6j` chain of shape `(α, β, x)` with sign twist `u`, collected: `τ = ±1`, the turn `q_*`, the rows of the twisted chain. -/
structure RwData (α β x τ qs : ℝ) (m n : ℤ) (u : ℤ → ℝ) : Prop where
  hα : 0 < α
  hβ : 0 < β
  hqs : 0 < qs
  hτ : τ ^ 2 = 1
  hx1 : -1 < x
  hx2 : x < 1
  hκ : 0 < 1 - τ * x
  hαq : 0 < 1 - 1 / (4 * α ^ 2) * qs ^ 2
  hβq : 0 < 1 - 1 / (4 * β ^ 2) * qs ^ 2
  hturn : Phi (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) τ x (qs ^ 2) = 0
  hu : ∀ k, u k ^ 2 = 1
  hrows : ∀ (a b c : ℤ) (D' : ℕ), RacahSystem (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) D' → ∀ i : Fin (D' + 1),
      (c : ℚ) = cPt (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) i → ∀ h : ℝ, 0 < h → wA (a : ℚ) (n : ℚ) * h = α →
      wB (b : ℚ) (m : ℚ) * h = β → cosA (wA (a : ℚ) (n : ℚ)) (wB (b : ℚ) (m : ℚ)) (wC (c : ℚ)) = x →
      ∀ k : ℤ, 1 ≤ k → jac (hrAk (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) (m : ℝ) (n : ℝ) h)
        (hrCk (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) τ x (m : ℝ) (n : ℝ) h) (fun j => u j * racah6jY a b c m n j) k = 0

namespace RwData

variable {α β x τ qs : ℝ} {m n : ℤ} {u : ℤ → ℝ}

lemma geo (D : RwData α β x τ qs m n u) : RwGeo (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) τ x qs :=
  ⟨by have := D.hα; positivity, by have := D.hβ; positivity, D.hτ, D.hqs, D.hαq, D.hβq, D.hturn, ⟨D.hx1, D.hx2⟩⟩

/-- Data of the untwisted chain, `τ = +1`. -/
lemma pos (hα : 0 < α) (hβ : 0 < β) (hx1 : -1 < x) (hx2 : x < 1) (hprod : (α - β * x) * (β - α * x) < 0) (m n : ℤ) :
    RwData α β x 1 (racahQs α β x) m n (fun _ => 1) := by
  obtain ⟨hqs, hκ, hαq, hβq, hturn⟩ := racah_turn_geom_pos hα hβ hx1 hx2 hprod
  exact ⟨hα, hβ, hqs, by norm_num, hx1, hx2, hκ, hαq, hβq, hturn, fun _ => by norm_num, bkr_rows_int_pos hα hβ m n⟩

/-- Data of the twisted chain `(-1)^k Ŷ_k`, `τ = -1`. -/
lemma neg (hα : 0 < α) (hβ : 0 < β) (hx1 : -1 < x) (hx2 : x < 1) (hprod : 0 < (α - β * x) * (β - α * x)) (m n : ℤ) :
    RwData α β x (-1) (racahQs α β x) m n (fun j => (-1 : ℝ) ^ j) := by
  obtain ⟨hqs, hκ, hαq, hβq, hturn⟩ := racah_turn_geom_neg hα hβ hx1 hx2 hprod
  exact ⟨hα, hβ, hqs, by norm_num, hx1, hx2, hκ, hαq, hβq, hturn, bkh_neg_sq, bkr_rows_int_neg hα hβ m n⟩

end RwData

/-- **The node count of the Airy window of the physical integer `6j` chain** (`τ = ±1`): see the module docstring. -/
theorem rwn_racah_window {α β x τ qs : ℝ} {m n : ℤ} {u : ℤ → ℝ} (D : RwData α β x τ qs m n u) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ qs / 2 ∧ ∀ b0 : ℝ, 0 ≤ b0 → b0 < qs → ∃ ε : ℝ, 0 < ε ∧
      ∀ (a b c : ℤ) (D' : ℕ), RacahSystem (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) D' → ∀ i : Fin (D' + 1),
        (c : ℚ) = cPt (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) i → ∀ h : ℝ, 0 < h → h ≤ ε →
        wA (a : ℚ) (n : ℚ) * h = α → wB (b : ℚ) (m : ℚ) * h = β →
        cosA (wA (a : ℚ) (n : ℚ)) (wB (b : ℚ) (m : ℚ)) (wC (c : ℚ)) = x →
        ∃ iw : ℕ, qs ≤ rwQ (1 / 2) h (max |m| |n| + (iw : ℤ)) ∧ rwQ (1 / 2) h (max |m| |n| + (iw : ℤ)) < qs + h ∧
          ∀ j : ℕ, qs - ρ ≤ rwQ (1 / 2) h (max |m| |n| + (j : ℤ)) → rwQ (1 / 2) h (max |m| |n| + (j : ℤ)) ≤ b0 →
            1 / 10 < |Real.cos (rwTheta (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) τ x qs (1 / 2) h (max |m| |n| + (j : ℤ)))| →
            j < iw ∧ ((∑ t ∈ Ico j iw, bix_c (fun s : ℕ => rwY u a b c m n (max |m| |n| + (s : ℤ))) t : ℕ) : ℤ) =
              ⌊bkPhase (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) τ x qs (rwQ (1 / 2) h (max |m| |n| + (j : ℤ))) / (π * h) + 1 / 4⌋ := by
  have G := D.geo
  obtain ⟨r, Cmu, ξ0, gmax, gmin, c1, c2, CA, δA, hm, hr0, hrq, hCA, hCmu, hξ0, hgmax, hgmin, hgg, hc1, hc12, hδA, hmpos, Hout⟩ :=
    bk_racah_int α β x τ qs m n D.hα D.hβ D.hqs D.hτ D.hκ D.hαq D.hβq D.hturn u D.hu D.hrows
  have hK : 0 ≤ max |m| |n| := le_trans (abs_nonneg m) (le_max_left _ _)
  obtain ⟨ρ, hρ, hρq, H⟩ := rwn_window_of_out (θ := 1 / 2) (q₀ := fun δ => δ ^ 3 / 2) (fun δ => by ring) (by norm_num) (by norm_num)
    G hr0 hCA hCmu hξ0 hgmin hc1 hc12 hδA Hout (max |m| |n|) hK
  refine ⟨ρ, hρ, hρq, fun b0 hb0 hb0q => ?_⟩
  obtain ⟨ε, hε, Hε⟩ := H b0 hb0 hb0q
  refine ⟨min ε hm, lt_min hε hmpos, ?_⟩
  intro a b c D' hsys i hc h hh hεh hAh hBh hx
  have hfam : rkFam α β x m n u hm h (fun j => u j * racah6jY a b c m n j)
      (4 * wA (a : ℚ) (n : ℚ) * wB (b : ℚ) (m : ℚ) / (2 * wC (c : ℚ))) :=
    ⟨hh, hεh.trans (min_le_right _ _), a, b, c, D', hsys, i, hc, hAh, hBh, hx, rfl, rfl⟩
  exact Hε h _ _ hfam hh (hεh.trans (min_le_left _ _))

/-- info: 'FormalResearch.Special.rwn_window_of_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.rwn_window_of_out

/-- info: 'FormalResearch.Special.rwn_racah_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.rwn_racah_window

end FormalResearch.Special
