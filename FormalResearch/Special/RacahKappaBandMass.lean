module

public import FormalResearch.Special.RacahKappaBand
public import FormalResearch.Special.RacahKappaConst
public import FormalResearch.Special.DiscreteAiryKappaSharpGeom

/-!
# The band mass in units of the Gauss weight

For an LG datum with `w² = kpP/√s` on the lattice sites of a band `kc ≤ k < kc + N'`, the band mass `B = Σ Y²` satisfies, with the Gauss weight `M = 1/(√s h)` and `T = (κ² + μ²)δ/2`,

`T M (1 - a - θ) ≤ B ≤ T M (1 + θ)`,  `θ = 8E(1+E)h + 2 C_b √s h/π`,  `a = q_{kc-1}/q_* + √(1 - (q_{kc+N'-1}/q_*)²)`

(`rk_band_mass`; `rkb_band` for the oscillation, `ksg_sv` for the Riemann sum of the profile).

**Claim class: proved.**
-/

@[expose] public section

open Finset FormalResearch.DiscreteAiry

namespace FormalResearch.Special

lemma rk_band_mass {A θ w Θ : ℝ → ℝ} {U : Set ℝ} {lo hi Mm : ℝ} (D : DlgData A θ w Θ U lo hi Mm)
    {h δ ρ E κ μ φ0 qs sq M : ℝ} {kc : ℤ} {Y : ℤ → ℝ} (m : ℕ) (hh : 0 < h) (hh1 : h ≤ 1) (hδ0 : 0 < δ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ^ 2 = δ / Real.pi) (hE : 0 ≤ E) (hsq : 0 < sq) (hM : M * h * sq = 1) (hqs : 0 < qs) (hk0 : 1 ≤ kc)
    (hNh : ((m : ℝ) + 1) * h ≤ qs) (hend : kpU h (kc + (m : ℤ) + 1) < qs)
    (hq : ∀ i : ℕ, i ≤ m + 1 → dlgQ (h / 2) h (kc + (i : ℤ)) ∈ U)
    (hrep : ∀ i : ℕ, i < m + 1 → |Y (kc + (i : ℤ)) - ρ * w (dlgQ (h / 2) h (kc + (i : ℤ))) *
        (κ * Real.cos (Θ (dlgQ (h / 2) h (kc + (i : ℤ))) / h + φ0) + μ * Real.sin (Θ (dlgQ (h / 2) h (kc + (i : ℤ))) / h + φ0))| ≤
      E * ((|κ| + |μ|) * (ρ * h)) * w (dlgQ (h / 2) h (kc + (i : ℤ))))
    (hw2 : ∀ i : ℕ, i < m + 1 → w (dlgQ (h / 2) h (kc + (i : ℤ))) ^ 2 = kpP qs h (kc + (i : ℤ)) / sq) :
    (κ ^ 2 + μ ^ 2) * δ / 2 * M * (1 - (kpU h (kc - 1) / qs + √(1 - (kpU h (kc + (m : ℤ)) / qs) ^ 2)) -
        (8 * E * (1 + E) * h + 2 * ((hi ^ 5 + 2 * qs * Mm * (hi ^ 4 + hi ^ 8)) / 2) * sq * h / Real.pi)) ≤
      ∑ i ∈ range (m + 1), Y (kc + (i : ℤ)) ^ 2 ∧
    ∑ i ∈ range (m + 1), Y (kc + (i : ℤ)) ^ 2 ≤
      (κ ^ 2 + μ ^ 2) * δ / 2 * M * (1 + (8 * E * (1 + E) * h + 2 * ((hi ^ 5 + 2 * qs * Mm * (hi ^ 4 + hi ^ 8)) / 2) * sq * h / Real.pi)) := by
  have hπ := Real.pi_pos
  have hband := rkb_band D (q0 := h / 2) (a := kc) (Y := Y) (ρ := ρ) (E := E) (κ := κ) (μ := μ) (φ0 := φ0) (m + 1) hh hh1 hρ0 hE hq hrep
  obtain ⟨hsv_hi, hsv_lo⟩ := ksg_sv (qs := qs) (h := h) (k0 := kc) m hqs hh hk0 hend
  set B : ℝ := ∑ i ∈ range (m + 1), Y (kc + (i : ℤ)) ^ 2 with hB
  set W : ℝ := ∑ i ∈ range (m + 1), w (dlgQ (h / 2) h (kc + (i : ℤ))) ^ 2 with hW
  set sv : ℝ := ∑ i ∈ range (m + 1), kpP qs h (kc + (i : ℤ)) / 2 with hsv
  set a : ℝ := kpU h (kc - 1) / qs + √(1 - (kpU h (kc + (m : ℤ)) / qs) ^ 2) with ha
  have hWsv : W = 2 * sv / sq := by
    rw [hW, hsv, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hw2 i (Finset.mem_range.1 hi)]; ring
  have hMeq : M = 1 / (h * sq) := by
    have : h * sq ≠ 0 := by positivity
    field_simp; linarith
  have hWhi : W ≤ Real.pi * M := by
    rw [hWsv, hMeq]
    have : 2 * sv / sq ≤ 2 * (Real.pi / 2 * (1 / h)) / sq := div_le_div_of_nonneg_right (by linarith) hsq.le
    refine this.trans (le_of_eq ?_)
    field_simp
  have hWlo : Real.pi * M * (1 - a) ≤ W := by
    rw [hWsv, hMeq]
    have : 2 * (Real.pi / 2 * (1 / h) * (1 - a)) / sq ≤ 2 * sv / sq := div_le_div_of_nonneg_right (by linarith) hsq.le
    refine le_trans (le_of_eq ?_) this
    field_simp
  set Cb0 : ℝ := (hi ^ 5 + 2 * qs * Mm * (hi ^ 4 + hi ^ 8)) / 2 with hCb0
  have hlo := D.lo_pos
  have hhi : 0 ≤ hi := by
    have h1 := D.Ab _ (hq 0 (by omega))
    linarith [h1.1, h1.2]
  have hMm := D.M_nonneg
  have hNh' : ((m + 1 : ℕ) : ℝ) * h ≤ qs := by push_cast; exact hNh
  have hCb : ((hi ^ 5 + 2 * ((m + 1 : ℕ) : ℝ) * h * Mm * (hi ^ 4 + hi ^ 8)) / 2) ≤ Cb0 := by
    rw [hCb0]
    have h1 : ((m + 1 : ℕ) : ℝ) * h * (Mm * (hi ^ 4 + hi ^ 8)) ≤ qs * (Mm * (hi ^ 4 + hi ^ 8)) :=
      mul_le_mul_of_nonneg_right hNh' (by positivity)
    nlinarith
  clear_value Cb0
  set R2 : ℝ := κ ^ 2 + μ ^ 2 with hR2
  have hR20 : 0 ≤ R2 := by positivity
  have hXr : 0 ≤ ρ ^ 2 * R2 := by positivity
  have hXe : ρ ^ 2 * R2 = 2 * (R2 * δ / 2) / Real.pi := by rw [hρ]; field_simp
  obtain ⟨hb1, hb2⟩ := abs_le.1 hband
  have hCbn : 0 ≤ Cb0 := by rw [hCb0]; positivity
  have hM0 : 0 < M := by rw [hMeq]; positivity
  have hEh : 0 ≤ 4 * E * (1 + E) * h := by positivity
  set Tt : ℝ := R2 * δ / 2 with hTt
  have hT0 : 0 ≤ Tt := by positivity
  have hXT : ρ ^ 2 * R2 * Real.pi = 2 * Tt := by rw [hXe]; field_simp
  have hMsq : M * sq * h = 1 := by rw [← hM]; ring
  constructor
  · -- lower bound
    have h1 : ρ ^ 2 * R2 / 2 * W - ρ ^ 2 * R2 * (4 * E * (1 + E) * h * W + ((hi ^ 5 + 2 * ((m + 1 : ℕ) : ℝ) * h * Mm * (hi ^ 4 + hi ^ 8)) / 2)) ≤ B := by
      linarith
    have h2 : ρ ^ 2 * R2 * (4 * E * (1 + E) * h * W + ((hi ^ 5 + 2 * ((m + 1 : ℕ) : ℝ) * h * Mm * (hi ^ 4 + hi ^ 8)) / 2)) ≤
        ρ ^ 2 * R2 * (4 * E * (1 + E) * h * (Real.pi * M) + Cb0) := by
      apply mul_le_mul_of_nonneg_left _ hXr
      have := mul_le_mul_of_nonneg_left hWhi hEh
      linarith
    have h3 : ρ ^ 2 * R2 / 2 * (Real.pi * M * (1 - a)) ≤ ρ ^ 2 * R2 / 2 * W :=
      mul_le_mul_of_nonneg_left hWlo (by positivity)
    have key : Tt * M * (1 - a - (8 * E * (1 + E) * h + 2 * Cb0 * sq * h / Real.pi)) =
        ρ ^ 2 * R2 / 2 * (Real.pi * M * (1 - a)) - ρ ^ 2 * R2 * (4 * E * (1 + E) * h * (Real.pi * M) + Cb0) := by
      have e1 : Tt = ρ ^ 2 * R2 * Real.pi / 2 := by linarith
      rw [e1]
      field_simp
      linear_combination (-(ρ ^ 2 * R2 * Cb0 * 2)) * hMsq
    linarith
  · have h1 : B ≤ ρ ^ 2 * R2 / 2 * W + ρ ^ 2 * R2 * (4 * E * (1 + E) * h * W + ((hi ^ 5 + 2 * ((m + 1 : ℕ) : ℝ) * h * Mm * (hi ^ 4 + hi ^ 8)) / 2)) := by
      linarith
    have h2 : ρ ^ 2 * R2 * (4 * E * (1 + E) * h * W + ((hi ^ 5 + 2 * ((m + 1 : ℕ) : ℝ) * h * Mm * (hi ^ 4 + hi ^ 8)) / 2)) ≤
        ρ ^ 2 * R2 * (4 * E * (1 + E) * h * (Real.pi * M) + Cb0) := by
      apply mul_le_mul_of_nonneg_left _ hXr
      have := mul_le_mul_of_nonneg_left hWhi hEh
      linarith
    have h3 : ρ ^ 2 * R2 / 2 * W ≤ ρ ^ 2 * R2 / 2 * (Real.pi * M) :=
      mul_le_mul_of_nonneg_left hWhi (by positivity)
    have key : Tt * M * (1 + (8 * E * (1 + E) * h + 2 * Cb0 * sq * h / Real.pi)) =
        ρ ^ 2 * R2 / 2 * (Real.pi * M) + ρ ^ 2 * R2 * (4 * E * (1 + E) * h * (Real.pi * M) + Cb0) := by
      have e1 : Tt = ρ ^ 2 * R2 * Real.pi / 2 := by linarith
      rw [e1]
      field_simp
      linear_combination (ρ ^ 2 * R2 * Cb0 * 2) * hMsq
    linarith

/-- info: 'FormalResearch.Special.rk_band_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.rk_band_mass

end FormalResearch.Special
