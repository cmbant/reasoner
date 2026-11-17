module

public import FormalResearch.Special.RacahKappaZoneWin
public import FormalResearch.Special.RacahKappaBandD
public import FormalResearch.Special.RacahKappaFinalAlg
public import FormalResearch.Special.RacahKappaChoose

/-!
# One chain at one scale: the mass accounting

`rk_chain_step`: given the Airy window `RkWinAtG θ q₀` of a chain (`θ = 1/2`: `RkWinAt`, integer chains; `θ = 1`: `RkWinAtH`, half-integer chains) `Y` (with the exponentially small `μ`), the band mass bounds in units of the Gauss weight, the left mass `≤ uM`, a monotone tail, a bounded support and the identity
`M = Σ_{k ≥ 0} Y_k²`, one has `|κ²δ - 2| ≤ 40 u`.

**Claim class: proved.**
-/

@[expose] public section

open Finset FormalResearch.Racah.P3 FormalResearch.DiscreteAiry

namespace FormalResearch.Special

lemma rkzK3_nonneg {c1 G C Rc Rt : ℝ} (hc1 : 0 < c1) (hRc : 0 ≤ Rc) (hRt : 0 ≤ Rt) : 0 ≤ rkzK3 c1 G C Rc Rt := by
  unfold rkzK3; positivity

/-- `|μ| ≤ δ³` from the exponential bound. -/
lemma rk_mu_le {δ ξ0 Cmu cs μ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hξ : 0 < ξ0) (hCmu : 0 ≤ Cmu) (hcs : 0 ≤ cs) (h1 : δ ≤ ξ0 / 14)
    (h2 : δ ≤ 1 * ξ0 ^ 3 / (48 * (Cmu * cs + 1)))
    (hμ : |μ| ≤ Cmu * (cs / δ ^ 3) * Real.exp (-ξ0 / δ ^ 3) / δ) : |μ| ≤ δ ^ 3 := by
  have hB : 0 ≤ Cmu * cs := by positivity
  have hsm := kk_mu_small hδ hδ1 hξ hB h1 h2
  have h3 : 1 ≤ Real.exp (7 / δ ^ 2) := Real.one_le_exp (by positivity)
  have h4 : Cmu * (cs / δ ^ 3) * Real.exp (-ξ0 / δ ^ 3) / δ = Cmu * cs * (1 / δ ^ 3) * (Real.exp (-ξ0 / δ ^ 3) / δ) := by ring
  rw [h4] at hμ
  have h5 : 0 ≤ Cmu * cs * (1 / δ ^ 3) * (Real.exp (-ξ0 / δ ^ 3) / δ) := by positivity
  have h6 : Cmu * cs * (1 / δ ^ 3) * (Real.exp (-ξ0 / δ ^ 3) / δ) ≤
      Cmu * cs * (1 / δ ^ 3) * (Real.exp (-ξ0 / δ ^ 3) / δ) * Real.exp (7 / δ ^ 2) := by
    nlinarith
  linarith

/-- The mass split `M = L + B + Z`. -/
lemma rk_mass_split {Y : ℤ → ℝ} {kc jz END : ℤ} {M : ℝ} (h0 : 0 ≤ kc) (h1 : kc ≤ jz) (h2 : jz ≤ END)
    (hM : ∑ k ∈ Finset.Ico 0 END, Y k ^ 2 = M) :
    M = ∑ k ∈ Finset.Ico 0 kc, Y k ^ 2 + ∑ k ∈ Finset.Ico kc jz, Y k ^ 2 + ∑ k ∈ Finset.Ico jz END, Y k ^ 2 := by
  rw [← hM, kk_ico_split (fun k => Y k ^ 2) (b := jz) (by omega) h2, kk_ico_split (fun k => Y k ^ 2) (a := 0) (b := kc) h0 h1]

/-- `0 ≤ kc ≤ jz` (lattice `q_k = (k + θ) δ³`, `0 < θ ≤ 1`). -/
lemma rk_kc_facts {δ3 c qs η θ : ℝ} {kc jz : ℤ} (hθ1 : θ ≤ 1) (hδ3 : 0 < δ3) (hkc1 : c ≤ ((kc : ℝ) + θ) * δ3)
    (hkc2 : ((kc : ℝ) + θ - 1) * δ3 < c) (hcpos : 0 < c) (hcη : c + δ3 < qs - η) (hjz1 : qs - η < ((jz : ℝ) + θ) * δ3) :
    0 ≤ kc ∧ kc ≤ jz := by
  constructor
  · by_contra hneg
    have h1 : (kc : ℝ) ≤ -1 := by exact_mod_cast (by omega : kc ≤ -1)
    have : ((kc : ℝ) + θ) * δ3 ≤ 0 := by nlinarith only [h1, hδ3, hθ1]
    linarith only [this, hkc1, hcpos]
  · by_contra hneg
    have h1 : (jz : ℝ) + 1 ≤ kc := by exact_mod_cast (by omega : jz + 1 ≤ kc)
    have h3 : ((jz : ℝ) + θ + 1) * δ3 ≤ ((kc : ℝ) + θ) * δ3 := by nlinarith only [h1, hδ3]
    have h2 : ((kc : ℝ) + θ) * δ3 = ((kc : ℝ) + θ - 1) * δ3 + δ3 := by ring
    have h4 : ((jz : ℝ) + θ) * δ3 + δ3 = ((jz : ℝ) + θ + 1) * δ3 := by ring
    linarith only [h3, h2, h4, hkc2, hjz1, hcη, hδ3]

/-- **One chain at one scale.** -/
lemma rk_chain_step {P Q τ x qs : ℝ} {Y : ℤ → ℝ} {r C Cmu ξ0 gmin gmax c1 c2 δ cs Rmax η c M sq u θ0 θ q₀ : ℝ} {J m N kc jz : ℤ} {κ μ : ℝ}
    (hW : RkWinAtG θ q₀ P Q τ x qs Y (cs / δ ^ 3) r C Cmu ξ0 gmin gmax c1 c2 δ J m N κ μ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hc1 : 0 < c1) (hc12 : c1 ≤ c2) (hgmax : 0 ≤ gmax) (hC : 0 ≤ C) (hCmu : 0 ≤ Cmu) (hcs : 0 ≤ cs)
    (hξ0 : 0 < ξ0) (hRmax : 0 ≤ Rmax) (hr : 0 < r) (hη : 0 < η) (hηr : η ≤ r / 2) (hη1 : η ≤ 1) (hsq : 0 < sq) (hqs : 0 < qs)
    (hs1 : δ ≤ ξ0 / 14) (hs2 : δ ≤ 1 * ξ0 ^ 3 / (48 * ((450 * gmax + C) * Cmu * cs + 1))) (hs3 : δ ^ 3 ≤ η / 2)
    (hs4 : δ ^ 2 ≤ c1 * η / (2 * (1 + c2))) (hs5 : δ ≤ c1 * r / 8) (hs6 : c2 * δ ≤ 1)
    (hs7 : δ ≤ 1 * ξ0 ^ 3 / (48 * (Cmu * cs + 1)))
    (hkc1 : c ≤ ((kc : ℝ) + θ) * δ ^ 3) (hkc2 : ((kc : ℝ) + θ - 1) * δ ^ 3 < c) (hcpos : 0 < c) (hcη : c + δ ^ 3 < qs - η)
    (hjz1 : qs - η < ((jz : ℝ) + θ) * δ ^ 3) (hjz2 : ((jz : ℝ) + θ - 1) * δ ^ 3 ≤ qs - η)
    (hM : M * δ ^ 3 * sq = 1)
    (hmono : ∀ k' k : ℤ, qs + δ ^ 3 ≤ ((k' : ℝ) + θ) * δ ^ 3 → k' ≤ k → Y k ^ 2 ≤ Y k' ^ 2)
    (hsupp : ∀ k : ℤ, Rmax < ((k : ℝ) + θ) * δ ^ 3 → Y k = 0)
    (hMeq : ∀ END : ℤ, (∀ k : ℤ, END ≤ k → Y k = 0) → ∑ k ∈ Finset.Ico 0 END, Y k ^ 2 = M)
    (hL : ∑ k ∈ Finset.Ico 0 kc, Y k ^ 2 ≤ u * M)
    (hBlo : (κ ^ 2 + μ ^ 2) * δ / 2 * M * (1 - (c / qs + 2 * √(η / qs)) - θ0 * δ ^ 3) ≤ ∑ k ∈ Finset.Ico kc jz, Y k ^ 2)
    (hBhi : ∑ k ∈ Finset.Ico kc jz, Y k ^ 2 ≤ (κ ^ 2 + μ ^ 2) * δ / 2 * M * (1 + θ0 * δ ^ 3))
    (hu : 0 < u) (hu6 : u ≤ 1 / 6) (hθ0 : 0 ≤ θ0) (hcu : c / qs ≤ u) (hηu : 2 * √(η / qs) ≤ u) (hθu : θ0 * δ ^ 3 ≤ u)
    (hA0 : 4 * sq * (2 * gmax ^ 2 * (√(2 * c2 * η) / Real.pi + 2 * c2 * (2 * c2 * η)) / c1) ≤ u / 2)
    (hK3 : 4 * sq * (rkzK3 c1 gmax C 4 (Rmax + 2) * δ) ≤ u / 2)
    (hξu : 2 * sq * δ * (2 * gmax ^ 2 * (√(2 * c2 * η) / Real.pi + 2 * c2 * (2 * c2 * η)) / c1 + rkzK3 c1 gmax C 4 (Rmax + 2) * δ) ≤ u)
    (hδu : δ ≤ 8 * u) : |κ ^ 2 * δ - 2| ≤ 40 * u := by
  have hδ3 : 0 < δ ^ 3 := by positivity
  have hM0 : 0 < M := by
    have : M = 1 / (δ ^ 3 * sq) := by
      have : δ ^ 3 * sq ≠ 0 := by positivity
      field_simp; linarith
    rw [this]; positivity
  have hW' := hW
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hμ, _⟩ := hW'
  have hμ3 : |μ| ≤ δ ^ 3 := rk_mu_le hδ hδ1 hξ0 hCmu hcs hs1 hs7 hμ
  have hjz2' : ((jz : ℝ) + θ) * δ ^ 3 ≤ qs - η + δ ^ 3 := by
    have h2 : ((jz : ℝ) + θ) * δ ^ 3 = ((jz : ℝ) + θ - 1) * δ ^ 3 + δ ^ 3 := by ring
    linarith only [hjz2, h2]
  have hz := rk_zone_win hW hθ hδ hδ1 hc1 hc12 hgmax hC hCmu hcs hξ0 hRmax hr hη hηr hη1 hs1 hs2 hs3 hs4 hs5 hs6 hjz1 hjz2' hmono hsupp
  obtain ⟨END, hEND, hEND0, hZ⟩ := hz
  obtain ⟨hkc0, hkcjz⟩ := rk_kc_facts hθ1 hδ3 hkc1 hkc2 hcpos hcη hjz1
  have hsplit := rk_mass_split (Y := Y) hkc0 hkcjz hEND (hMeq END hEND0)
  have hL0 : 0 ≤ ∑ k ∈ Finset.Ico 0 kc, Y k ^ 2 := Finset.sum_nonneg (fun k _ => sq_nonneg _)
  have hZ0 : 0 ≤ ∑ k ∈ Finset.Ico jz END, Y k ^ 2 := Finset.sum_nonneg (fun k _ => sq_nonneg _)
  set A0 : ℝ := 2 * gmax ^ 2 * (√(2 * c2 * η) / Real.pi + 2 * c2 * (2 * c2 * η)) / c1 with hA0def
  set K3 : ℝ := rkzK3 c1 gmax C 4 (Rmax + 2) with hK3def
  have hc2 : 0 < c2 := hc1.trans_le hc12
  have hA00 : 0 ≤ A0 := by rw [hA0def]; positivity
  have hK30 : 0 ≤ K3 := rkzK3_nonneg hc1 (by norm_num) (by linarith)
  have hZ' : ∑ k ∈ Finset.Ico jz END, Y k ^ 2 ≤ A0 * (2 * κ ^ 2 + 2) / δ ^ 2 + K3 * (2 * κ ^ 2 + 2) / δ := by
    refine hZ.trans (le_of_eq ?_)
    rw [hA0def]
    field_simp
  exact rk_final_alg (κ := κ) (μ := μ) (δ := δ) (M := M) (sq := sq) (L := ∑ k ∈ Finset.Ico 0 kc, Y k ^ 2)
    (B := ∑ k ∈ Finset.Ico kc jz, Y k ^ 2) (Z := ∑ k ∈ Finset.Ico jz END, Y k ^ 2) (aB := c / qs + 2 * √(η / qs)) (θ := θ0 * δ ^ 3)
    (ε := u) (A0 := A0) (K3 := K3) (u := u) hδ hδ1 hsq hM hL0 hL hZ0 hsplit hBlo hBhi hZ' hμ3 hA00 hK30
    (by positivity) (by positivity) hu.le hu6 (by linarith) (by linarith) (by linarith) hθu le_rfl hδu

end FormalResearch.Special
