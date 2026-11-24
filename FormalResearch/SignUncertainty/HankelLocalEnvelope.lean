module

public import FormalResearch.SignUncertainty.HankelLocalDensity
public import FormalResearch.SignUncertainty.HankelLangerRoot

/-!
# The envelope `(e71)` of the local density (`gt:7.7c` (c))

At the saddle `ζ_+ = u^{1/2}` of `ℓ = -g(ζ_+)` (so `ℓ = log(π² ξ)` for the point `ξ` of the Langer chart): by
`hankel_local_density_bound`, `phase_at_saddle` and `re_mMap_bounds`,
`‖∫_{|τ|≤1/3} J(σ_* + iτ) dτ‖ ≤ 200 c^{-1/3} (Re √ũ)^{-1/2} |e^{-(4/3) ũ^{3/2}}|`
(`hankel_local_density_envelope`), with `√ũ = c^{1/3} μ 𝗆(ζ_+)`.
-/

@[expose] public section

open Complex Set Filter Topology MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty

lemma norm_gSer_small {ζ : ℂ} (hζ : ‖ζ‖ ≤ 0.035) : ‖gSer etaC ζ‖ ≤ 1 / 200 := by
  have hu : ‖ζ ^ 2‖ ≤ 0.035 ^ 2 := by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hζ 2
  have h1 : ‖ζ ^ 2‖ < 1 := lt_of_le_of_lt hu (by norm_num)
  have hb : ∀ j, 1 ≤ j → |etaC j / ((j : ℝ) + 1)| ≤ 1 := fun j _ => abs_eta_div_le langerEta_etaC j
  have h2 := norm_psW_sub_le (a := fun j => etaC j / ((j : ℝ) + 1)) (B := 1) hb h1
  have h0 : (etaC 0 / (((0 : ℕ) : ℝ) + 1)) = π ^ 2 / 12 := by simp [etaC_zero]
  have h3 : ‖psW (fun j => etaC j / ((j : ℝ) + 1)) (ζ ^ 2)‖ ≤
      π ^ 2 / 12 + 1 * ‖ζ ^ 2‖ / (1 - ‖ζ ^ 2‖) := by
    have := norm_le_insert' (psW (fun j => etaC j / ((j : ℝ) + 1)) (ζ ^ 2))
      ((etaC 0 / (((0 : ℕ) : ℝ) + 1) : ℝ) : ℂ)
    rw [h0] at this h2
    have h4 : ‖((π ^ 2 / 12 : ℝ) : ℂ)‖ = π ^ 2 / 12 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  rw [one_mul] at h3
  unfold gSer
  rw [norm_mul, norm_pow]
  have hm : ‖ζ ^ 2‖ / (1 - ‖ζ ^ 2‖) ≤ 0.035 ^ 2 / (1 - 0.035 ^ 2) := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; nlinarith [norm_nonneg (ζ ^ 2)]
  have hpi2 : π ^ 2 / 12 ≤ 1 := by
    have : π ^ 2 < 3.15 ^ 2 := pow_lt_pow_left₀ Real.pi_lt_d2 Real.pi_pos.le (by norm_num)
    linarith
  have hζ0 := norm_nonneg ζ
  have hq : ‖ζ‖ ^ 2 ≤ 0.035 ^ 2 := pow_le_pow_left₀ hζ0 hζ 2
  have hps : ‖psW (fun j => etaC j / ((j : ℝ) + 1)) (ζ ^ 2)‖ ≤ 1 + 0.035 ^ 2 / (1 - 0.035 ^ 2) := by
    linarith
  calc ‖ζ‖ ^ 2 * ‖psW (fun j => etaC j / ((j : ℝ) + 1)) (ζ ^ 2)‖
      ≤ 0.035 ^ 2 * (1 + 0.035 ^ 2 / (1 - 0.035 ^ 2)) := by gcongr
    _ ≤ 1 / 200 := by norm_num

lemma langerMu_lt : langerMu < 3 / 4 := by
  have h3 : langerMu ^ 3 < (3 / 4) ^ 3 := by
    rw [langerMu_cube]
    have : π ^ 2 < 3.15 ^ 2 := pow_lt_pow_left₀ Real.pi_lt_d2 Real.pi_pos.le (by norm_num)
    nlinarith
  exact lt_of_pow_lt_pow_left₀ 3 (by norm_num) h3

/-- **Envelope `(e71)` for the local integral** at `ℓ = -g(ζ₊)`, `ζ₊ = u^{1/2}`, `u` off the cut with `‖u‖ ≤ 0.035²`
(absolute constant `200`). -/
theorem hankel_local_density_envelope {c ε : ℝ} (hc : 2 ≤ c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1) {u : ℂ} (hu : u ∈ slitPlane)
    (hun : ‖u‖ ≤ 0.035 ^ 2) :
    ‖∫ τ in (-(1 / 3 : ℝ))..(1 / 3),
        hankelJ c f (-(gSer etaC (saddleRoot u))) (((1 / 10 : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
      200 * (c ^ (1 / 3 : ℝ))⁻¹ * (Real.sqrt ((langerUtilde etaC c u) ^ (1 / 2 : ℂ)).re)⁻¹ *
        ‖Complex.exp (-(4 / 3 : ℂ) * (langerUtilde etaC c u) ^ (3 / 2 : ℂ))‖ := by
  have hc0 : 0 < c := by linarith
  set ζ := saddleRoot u with hζ
  have hζn : ‖ζ‖ ≤ 0.035 := norm_saddleRoot_le hun
  have hre : 0 < ζ.re := re_saddleRoot_pos hu
  have hζeq : (ζ.re : ℂ) + (ζ.im : ℂ) * Complex.I = ζ := by apply Complex.ext <;> simp
  have hσ : ζ.re ≤ 0.035 := (Complex.re_le_norm ζ).trans hζn
  have hτ0 : |ζ.im| ≤ 0.035 := (Complex.abs_im_le_norm ζ).trans hζn
  have hl : (-(gSer etaC ζ)).re ≤ 1 / 200 := by
    have h1 := Complex.re_le_norm (-(gSer etaC ζ))
    rw [norm_neg] at h1
    exact h1.trans (norm_gSer_small hζn)
  have hcrit : gSer etaC ((ζ.re : ℂ) + (ζ.im : ℂ) * Complex.I) + (-(gSer etaC ζ)) = 0 := by
    rw [hζeq]; ring
  have hb := hankel_local_density_bound hc hf hε hM (-(gSer etaC ζ)) hl hre hσ hτ0 hcrit
  rw [hζeq] at hb
  -- the phase at the saddle
  have hph : (c : ℂ) * hankelLocPhi (-(gSer etaC ζ)) ζ = -(4 / 3 : ℂ) * (langerUtilde etaC c u) ^ (3 / 2 : ℂ) := by
    rw [← phase_at_saddle langerEta_etaC hc0 hu hun]
    unfold hankelLocPhi; ring
  have hexp : Real.exp (c * (hankelLocPhi (-(gSer etaC ζ)) ζ).re) =
      ‖Complex.exp (-(4 / 3 : ℂ) * (langerUtilde etaC c u) ^ (3 / 2 : ℂ))‖ := by
    rw [← hph, Complex.norm_exp]; congr 1; simp [Complex.mul_re]
  rw [hexp] at hb
  -- `Re √ũ ≤ c^{1/3} (1 + 9e-4) μ σ`
  set k : ℝ := c ^ (1 / 3 : ℝ) with hk
  have hk0 : 0 < k := Real.rpow_pos_of_pos hc0 _
  have hk3 : k ^ 3 = c := by
    rw [hk, ← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
  have hm := re_mMap_bounds langerEta_etaC (σ := ζ.re) (τ := ζ.im) hre.le (by rw [hζeq]; exact hζn)
  rw [hζeq] at hm
  have hR : ((langerUtilde etaC c u) ^ (1 / 2 : ℂ)).re = k * langerMu * (mMap etaC ζ).re := by
    rw [langerUtilde_sqrt langerEta_etaC hc0 hu hun, Complex.re_ofReal_mul]
  have hR0 : 0 < ((langerUtilde etaC c u) ^ (1 / 2 : ℂ)).re := by
    rw [hR]; exact mul_pos (mul_pos hk0 langerMu_pos) (by nlinarith [hm.1])
  have hRle : ((langerUtilde etaC c u) ^ (1 / 2 : ℂ)).re ≤ k * ζ.re := by
    rw [hR]
    have hμ := langerMu_lt
    have hmu := langerMu_pos
    have : langerMu * (mMap etaC ζ).re ≤ ζ.re := by nlinarith [hm.2]
    nlinarith
  set R := ((langerUtilde etaC c u) ^ (1 / 2 : ℂ)).re with hRdef
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.2 hR0
  have hX : k * Real.sqrt R ≤ Real.sqrt (c * ζ.re) := by
    refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
    rw [mul_pow, Real.sq_sqrt hR0.le, ← hk3]
    have : k ^ 2 * R ≤ k ^ 2 * (k * ζ.re) := by gcongr
    nlinarith
  have hinv : (Real.sqrt (c * ζ.re))⁻¹ ≤ k⁻¹ * (Real.sqrt R)⁻¹ := by
    rw [← mul_inv]; exact inv_anti₀ (by positivity) hX
  calc _ ≤ 200 * (Real.sqrt (c * ζ.re))⁻¹ * ‖Complex.exp (-(4 / 3 : ℂ) * (langerUtilde etaC c u) ^ (3 / 2 : ℂ))‖ := hb
    _ ≤ 200 * (k⁻¹ * (Real.sqrt R)⁻¹) * ‖Complex.exp (-(4 / 3 : ℂ) * (langerUtilde etaC c u) ^ (3 / 2 : ℂ))‖ := by gcongr
    _ = _ := by ring

/-- info: 'FormalResearch.SignUncertainty.hankel_local_density_envelope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel_local_density_envelope

end FormalResearch.SignUncertainty
