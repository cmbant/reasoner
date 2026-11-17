module

public import FormalResearch.Special.RacahKappaHBulk
public import FormalResearch.Special.RacahKappaBandD

/-!
# The band with the chain data, shifted lattice (half-integer Racah chains)

`rk_bulk_bandH`: twin of `rk_bulk_band` (`RacahKappaBandD`) for the closed forms `hrAkH`, `hrCkH` on the lattice `q_k = (k+1) δ³` (so `q_{k-1} = k δ³`).  The band assembly
`rk_band_assemble`, the lattice geometry `rk_band_geom` and the band mass `rk_band_mass` are the lattice-generic lemmas of `RacahKappaBandD`, `RacahKappaBandMass`, used with `θ = 1`.

**Claim class: proved.**
-/

@[expose] public section

open Finset Set FormalResearch.Racah.P3 FormalResearch.DiscreteAiry
open scoped Real

namespace FormalResearch.Special

/-- **Window and band mass in units of the Gauss weight.**  The conclusion of `rk_bulkH` for the Airy window `RkWinAtH`, together with, for every band `kc ≤ k < jz`
(`q_{kc-1} < c ≤ q_{kc}`, `q_{jz-1} ≤ q_* - η < q_{jz}`) and every `M` with `M δ³ √s = 1`, `s = rkS P Q x`:
`T M (1 - a_B - θ₀ δ³) ≤ Σ_{kc ≤ k < jz} Y_k² ≤ T M (1 + θ₀ δ³)`, `T = (κ² + μ²) δ/2`, `a_B = c/q_* + 2√(η/q_*)`. -/
theorem rk_bulk_bandH {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (a b τ x qs : ℝ) (hqs : 0 < qs) (hτ : τ ^ 2 = 1)
    (hκ : 0 < 1 - τ * x) (hα : 0 < 1 - P * qs ^ 2) (hβ : 0 < 1 - Q * qs ^ 2) (hturn : Phi P Q τ x (qs ^ 2) = 0)
    (hosc0 : ∀ q : ℝ, 0 < q → q < qs → |hrU P Q τ x q| < 1) :
    ∃ (r Cmu ξ0 gmax gmin c1 c2 CA : ℝ), 0 < r ∧ r ≤ qs / 4 ∧ 0 < CA ∧ 0 < Cmu ∧ 0 < ξ0 ∧ 0 < gmax ∧ 0 < gmin ∧ gmin ≤ gmax ∧
      0 < c1 ∧ c1 ≤ c2 ∧
      ∀ c0 : ℝ, 0 < c0 → c0 < qs / 2 → ∀ η : ℝ, 0 < η → η ≤ r / 2 → ∀ c : ℝ, c0 < c → c < qs - r → ∃ δ0 θ0 : ℝ, 0 < δ0 ∧ 0 ≤ θ0 ∧
        ∀ (δ : ℝ) (Y : ℤ → ℝ) (Ymax : ℝ), 0 < δ → δ ≤ δ0 →
          (∀ k : ℤ, 1 ≤ k → jac (hrAkH P Q a b (δ ^ 3)) (hrCkH P Q τ x a b (δ ^ 3)) Y k = 0) →
          (∀ k : ℤ, qs + δ ^ 3 ≤ ((k : ℝ) + 1) * δ ^ 3 → |Y k| ≤ Ymax) →
          ∃ (J m N : ℤ) (κ μ : ℝ), RkWinAtH P Q τ x qs Y Ymax r CA Cmu ξ0 gmin gmax c1 c2 δ J m N κ μ ∧
            ∀ (kc jz : ℤ) (M : ℝ), c ≤ ((kc : ℝ) + 1) * δ ^ 3 → (kc : ℝ) * δ ^ 3 < c →
              qs - η < ((jz : ℝ) + 1) * δ ^ 3 → (jz : ℝ) * δ ^ 3 ≤ qs - η →
              M * δ ^ 3 * Real.sqrt (rkS P Q x) = 1 →
                (κ ^ 2 + μ ^ 2) * δ / 2 * M * (1 - (c / qs + 2 * √(η / qs)) - θ0 * δ ^ 3) ≤ ∑ k ∈ Finset.Ico kc jz, Y k ^ 2 ∧
                ∑ k ∈ Finset.Ico kc jz, Y k ^ 2 ≤ (κ ^ 2 + μ ^ 2) * δ / 2 * M * (1 + θ0 * δ ^ 3) := by
  have hs := rk_turn_id hP hQ hτ hα hβ hturn
  have hx2 := rk_abs_x_lt hP hQ hτ hqs hα hβ hκ hturn
  have hspos : 0 < rkS P Q x := by
    have h1 : 0 < 1 - x ^ 2 := by linarith
    rw [hs] at h1
    by_contra hneg
    push Not at hneg
    nlinarith [sq_nonneg qs]
  have hsq : 0 < Real.sqrt (rkS P Q x) := Real.sqrt_pos.2 hspos
  obtain ⟨r, Cmu, ξ0, gmax, gmin, c1, c2, CA, hr, hrq4, hCA, hCmu, hξ0, hgmax, hgmin, hgg, hc1, hc12, H⟩ :=
    rk_bulkH hP hQ a b τ x qs hqs hτ hκ hα hβ hturn hosc0
  refine ⟨r, Cmu, ξ0, gmax, gmin, c1, c2, CA, hr, hrq4, hCA, hCmu, hξ0, hgmax, hgmin, hgg, hc1, hc12, ?_⟩
  intro c0 hc0 hc0q η hη hηr c hc0c hcr
  obtain ⟨δ0', C, hδ0', hC, HH⟩ := H c0 hc0 hc0q η hη hηr c hc0c hcr
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
  intro δ Y Ymax hδ hδ0 hrows hbd
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
  obtain ⟨J, m, N, κ, μ, hW, hbulk⟩ := HH δ Y Ymax hδ hδ' hrows hbd
  refine ⟨J, m, N, κ, μ, hW, ?_⟩
  intro kc jz M hkc1 hkc2 hjz1 hjz2 hM
  exact rk_band_assemble (θl := 1) (q₀ := δ ^ 3) (by norm_num) (by norm_num) hP hQ τ x qs hqs hτ hα hβ hs hspos hsq hc0 hc0c hη hcη hc hπ hE0 hδ hδ1 hδη hδc (by ring)
    (by
      have : η < qs - η - c := by linarith
      linarith) h3δ D hhi0 hbulk kc jz M hkc1 (by linarith) hjz1 (by linarith) hM


/-- info: 'FormalResearch.Special.rk_bulk_bandH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.rk_bulk_bandH

end FormalResearch.Special
