module

public import FormalResearch.Special.RacahKappaBulk
public import FormalResearch.Special.RacahKappaBandMass
public import FormalResearch.Special.DiscreteAiryKappaOrderLow

/-!
# The LG datum on the band, and the band mass from the bulk form

`rk_bulk_D`: the bulk LG datum `(A, θ, w, Θ)` of the centred Racah / Hahn closed form on `(c', q_* - η/2)`, `c' = (c₀ + c)/2`.
`rk_band_site`: the band sums `Σ_{kc ≤ k < jz} Y_k²` in units of the Gauss weight, from the bulk form of `rk_bulk` (same `κ, μ` as the Airy window).

**Claim class: proved.**
-/

@[expose] public section

open Finset Set FormalResearch.Racah.P3 FormalResearch.DiscreteAiry
open scoped Real

namespace FormalResearch.Special

lemma rk_bulk_D {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (τ x qs : ℝ) (hα : 0 < 1 - P * qs ^ 2) (hβ : 0 < 1 - Q * qs ^ 2)
    (hosc0 : ∀ q : ℝ, 0 < q → q < qs → |hrU P Q τ x q| < 1) {c0 c η : ℝ} (hc0 : 0 < c0) (hc0c : c0 < c) (hη : 0 < η)
    (hcη : c < qs - η) :
    ∃ lo hi Mm : ℝ, DlgData (hrA1 P Q) (dlgsTheta (hrU P Q τ x)) (dlgsW (hrA1 P Q) (hrU P Q τ x))
      (dlgsPhase (hrU P Q τ x) ((c0 + c) / 2)) (Set.Ioo ((c0 + c) / 2) (qs - η / 2)) lo hi Mm := by
  have hfacP : ∀ q : ℝ, 0 < q → q ≤ qs → 0 < 1 - P * q ^ 2 := fun q h1 h2 => dlgh_fac hP hα h1 h2
  have hfacQ : ∀ q : ℝ, 0 < q → q ≤ qs → 0 < 1 - Q * q ^ 2 := fun q h1 h2 => dlgh_fac hQ hβ h1 h2
  have hreg' : ∀ q ∈ Ioo c0 (qs - η / 4), 0 < (1 - P * q ^ 2) * (1 - Q * q ^ 2) := fun q hq =>
    mul_pos (hfacP q (by linarith [hq.1]) (by linarith [hq.2])) (hfacQ q (by linarith [hq.1]) (by linarith [hq.2]))
  have hA : ContDiffOn ℝ 2 (hrA1 P Q) (Ioo c0 (qs - η / 4)) := fun q hq =>
    (hrA_contDiffAt 2 (hreg' q hq)).contDiffWithinAt
  have hu := dlgh_u_diff (P := P) (Q := Q) τ x hreg'
  have hsub : Icc ((c0 + c) / 2) (qs - η / 2) ⊆ Ioo c0 (qs - η / 4) := fun q hq => ⟨by linarith [hq.1], by linarith [hq.2]⟩
  obtain ⟨lo, hi, Mm, D, -⟩ := dlg_smooth_data (isOpen_Ioo (a := c0) (b := qs - η / 4))
    (c := (c0 + c) / 2) (d := qs - η / 2) (by linarith) hsub hA hu
    (fun q hq => hrA_pos (hreg' q hq)) (fun q hq => hosc0 q (by linarith [hq.1]) (by linarith [hq.2]))
  exact ⟨lo, hi, Mm, D⟩

/-- `(δ³)^{1/6}² = δ`. -/
lemma rk_rpow_sq {δ : ℝ} (hδ : 0 < δ) : ((δ ^ 3) ^ (1 / 6 : ℝ)) ^ 2 = δ := by
  have h3 : 0 ≤ δ ^ 3 := by positivity
  rw [← Real.rpow_natCast, ← Real.rpow_mul h3]
  have : (δ ^ 3) ^ ((1 / 6 : ℝ) * ((2 : ℕ) : ℝ)) = δ := by
    have e : (1 / 6 : ℝ) * ((2 : ℕ) : ℝ) = 1 / 3 := by norm_num
    rw [e, ← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
    norm_num
  exact this

/-- The profile sum bounds: `a ≤ c/q_* + 2√(η/q_*)` for the band `q_{kc - 1} < c`, `qs - η - h < q_{jz-1} ≤ qs`. -/
lemma rk_a_bound {qs h c η q1 q2 : ℝ} (hqs : 0 < qs) (hh : 0 < h) (hhη : h ≤ η) (hq1 : q1 < c) (hq2 : qs - η - h < q2)
    (hq2' : q2 ≤ qs) (hq20 : 0 ≤ q2) :
    q1 / qs + √(1 - (q2 / qs) ^ 2) ≤ c / qs + 2 * √(η / qs) := by
  have h1 : q1 / qs ≤ c / qs := div_le_div_of_nonneg_right hq1.le hqs.le
  have hy1 : q2 / qs ≤ 1 := by rw [div_le_one hqs]; exact hq2'
  have hy0 : 0 ≤ q2 / qs := by positivity
  have hη : 0 < η := lt_of_lt_of_le hh hhη
  have h2 : 1 - (q2 / qs) ^ 2 ≤ 4 * η / qs := by
    have : 1 - (q2 / qs) ^ 2 = (1 - q2 / qs) * (1 + q2 / qs) := by ring
    rw [this]
    have e1 : 1 - q2 / qs ≤ 2 * η / qs := by
      rw [show 1 - q2 / qs = (qs - q2) / qs by field_simp]
      exact div_le_div_of_nonneg_right (by linarith) hqs.le
    calc (1 - q2 / qs) * (1 + q2 / qs) ≤ (2 * η / qs) * 2 :=
          mul_le_mul e1 (by linarith) (by linarith) (by positivity)
      _ = 4 * η / qs := by ring
  have h3 : √(1 - (q2 / qs) ^ 2) ≤ 2 * √(η / qs) := by
    calc √(1 - (q2 / qs) ^ 2) ≤ √(4 * η / qs) := Real.sqrt_le_sqrt h2
      _ = 2 * √(η / qs) := by
        have : 4 * η / qs = 2 ^ 2 * (η / qs) := by ring
        rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  linarith

/-- Lattice geometry of a band `kc ≤ k < jz` at scale `h = δ³`, lattice `q_k = (k + θ) δ³` (`0 < θ ≤ 1`). -/
lemma rk_band_geom {δ qs c η θ : ℝ} {kc jz : ℤ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hqs : 0 < qs) (hc : 0 < c) (hδη : δ ≤ η / 4)
    (hδc : 2 * δ ≤ c) (hbig : 4 * δ ≤ qs - η - c) (hη : 0 < η)
    (hkc1 : c ≤ ((kc : ℝ) + θ) * δ ^ 3) (hkc2 : ((kc : ℝ) + θ - 1) * δ ^ 3 < c)
    (hjz1 : qs - η < ((jz : ℝ) + θ) * δ ^ 3) (hjz2 : ((jz : ℝ) + θ - 1) * δ ^ 3 ≤ qs - η) :
    ∃ m : ℕ, jz = kc + (m : ℤ) + 1 ∧ 1 ≤ kc ∧
      (∀ i : ℕ, i ≤ m + 1 → c ≤ (((kc + (i : ℤ) : ℤ) : ℝ) + θ) * δ ^ 3 ∧
        (((kc + (i : ℤ) : ℤ) : ℝ) + θ) * δ ^ 3 < qs - η / 2) ∧
      (∀ i : ℕ, i < m + 1 → (((kc + (i : ℤ) : ℤ) : ℝ) + θ) * δ ^ 3 ≤ qs - η) ∧
      ((m : ℝ) + 1) * δ ^ 3 ≤ qs ∧ ((jz : ℝ) + θ) * δ ^ 3 < qs ∧
      qs - η - δ ^ 3 < ((jz : ℝ) + θ - 1) * δ ^ 3 ∧ 0 ≤ ((jz : ℝ) + θ - 1) * δ ^ 3 := by
  have hh : 0 < δ ^ 3 := by positivity
  have h3δ : δ ^ 3 ≤ δ := by
    have h1 : δ ^ 2 ≤ 1 := pow_le_one₀ hδ.le hδ1
    calc δ ^ 3 = δ * δ ^ 2 := by ring
      _ ≤ δ * 1 := mul_le_mul_of_nonneg_left h1 hδ.le
      _ = δ := mul_one _
  have hqm : ∀ k k' : ℤ, k ≤ k' → ((k : ℝ) + θ) * δ ^ 3 ≤ ((k' : ℝ) + θ) * δ ^ 3 := fun k k' hkk => by
    have : (k : ℝ) ≤ k' := by exact_mod_cast hkk
    exact mul_le_mul_of_nonneg_right (by linarith) hh.le
  have hkcjz : kc + 1 < jz := by
    by_contra hcon
    push Not at hcon
    have h1 : ((jz : ℝ) - 1) ≤ (kc : ℝ) := by
      have : jz - 1 ≤ kc := by omega
      exact_mod_cast this
    have h2 := mul_le_mul_of_nonneg_right h1 hh.le
    linarith only [h2, hkc1, hjz1, hbig, hδη, hη, hh, h3δ, hkc2]
  obtain ⟨m, hm⟩ : ∃ m : ℕ, jz = kc + (m : ℤ) + 1 := ⟨(jz - kc - 1).toNat, by
    have := Int.toNat_of_nonneg (show 0 ≤ jz - kc - 1 by omega); omega⟩
  have hjzR : ((jz : ℝ)) = (kc : ℝ) + (m : ℝ) + 1 := by rw [hm]; push_cast; ring
  have hk1 : 1 ≤ kc := by
    by_contra hcon
    have h0 : kc ≤ 0 := by omega
    have h1 := hqm kc 0 h0
    simp only [Int.cast_zero] at h1
    have hθδ : θ * δ ^ 3 ≤ δ ^ 3 := by nlinarith only [hθ1, hh]
    linarith only [h1, hkc1, hδc, h3δ, hh, hc, hδ, hθδ]
  have hkpos : (1 : ℝ) ≤ kc := by exact_mod_cast hk1
  have hjz' : ((jz : ℝ) + θ) * δ ^ 3 = ((jz : ℝ) + θ - 1) * δ ^ 3 + δ ^ 3 := by ring
  refine ⟨m, hm, hk1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    constructor
    · have := hqm kc (kc + (i : ℤ)) (by omega)
      linarith only [this, hkc1]
    · have h1 := hqm (kc + (i : ℤ)) jz (by omega)
      linarith only [h1, hjz', hjz2, hδη, h3δ, hη]
  · intro i hi
    have h1 := hqm (kc + (i : ℤ)) (jz - 1) (by omega)
    have h2 : ((jz : ℝ) + θ - 1) * δ ^ 3 = (((jz - 1 : ℤ) : ℝ) + θ) * δ ^ 3 := by push_cast; ring
    linarith only [h1, h2, hjz2]
  · have : ((m : ℝ) + 1) * δ ^ 3 = ((jz : ℝ) + θ) * δ ^ 3 - ((kc : ℝ) + θ) * δ ^ 3 := by rw [hjzR]; ring
    rw [this]
    have : 0 < ((kc : ℝ) + θ) * δ ^ 3 := mul_pos (by linarith) hh
    linarith only [this, hjz', hjz2, hδη, h3δ, hη]
  · linarith only [hjz', hjz2, hδη, h3δ, hη]
  · linarith only [hjz1, hjz', hh]
  · have : (1 : ℝ) ≤ jz := by
      have : (1 : ℤ) ≤ jz := by omega
      exact_mod_cast this
    exact mul_nonneg (by linarith) hh.le

/-- The band assembly (bulk form on the band, the datum `D`, the profile sum), on the lattice `q_k = q₀ + kδ³ = (k + θ_l) δ³`
(`q₀ = θ_l δ³`; `θ_l = 1/2` integer chains, `θ_l = 1` half-integer chains). -/
lemma rk_band_assemble {θl q₀ : ℝ} (hθl : 0 < θl) (hθl1 : θl ≤ 1) {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (τ x qs : ℝ) (hqs : 0 < qs) (hτ : τ ^ 2 = 1) (hα : 0 < 1 - P * qs ^ 2)
    (hβ : 0 < 1 - Q * qs ^ 2) (hs : 1 - x ^ 2 = rkS P Q x * qs ^ 2) (hspos : 0 < rkS P Q x) (hsq : 0 < Real.sqrt (rkS P Q x))
    {c0 c η C δ lo hi Mm : ℝ} {Y : ℤ → ℝ} {κ μ : ℝ} (hc0 : 0 < c0) (hc0c : c0 < c) (hη : 0 < η) (hcη : c < qs - η) (hc : 0 < c)
    (hπ : 0 < Real.pi) (hE0 : 0 ≤ C * √Real.pi) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδη : δ ≤ η / 4) (hδc : 2 * δ ≤ c) (hq₀ : q₀ = θl * δ ^ 3)
    (hbig : 4 * δ ≤ qs - η - c) (h3δ : δ ^ 3 ≤ δ)
    (D : DlgData (hrA1 P Q) (dlgsTheta (hrU P Q τ x)) (dlgsW (hrA1 P Q) (hrU P Q τ x))
      (dlgsPhase (hrU P Q τ x) ((c0 + c) / 2)) (Set.Ioo ((c0 + c) / 2) (qs - η / 2)) lo hi Mm)
    (hhi0 : 0 ≤ hi)
    (hbulk : ∀ k : ℤ, c ≤ dlgQ q₀ (δ ^ 3) k → dlgQ q₀ (δ ^ 3) k ≤ qs - η →
              |Y k - (δ ^ 3) ^ (1 / 6 : ℝ) * (1 / √Real.pi) * dlgsW (hrA1 P Q) (hrU P Q τ x) (dlgQ q₀ (δ ^ 3) k) *
                  (κ * Real.cos (dlgP (dlgsPhase (hrU P Q τ x) ((c0 + c) / 2)) q₀ (δ ^ 3) k -
                      (∫ s in (c0 + c) / 2..qs, Real.arccos (hrU P Q τ x s)) / δ ^ 3 + Real.pi / 4) +
                    μ * Real.sin (dlgP (dlgsPhase (hrU P Q τ x) ((c0 + c) / 2)) q₀ (δ ^ 3) k -
                      (∫ s in (c0 + c) / 2..qs, Real.arccos (hrU P Q τ x s)) / δ ^ 3 + Real.pi / 4))| ≤
                C * ((|κ| + |μ|) * ((δ ^ 3) ^ (1 / 6 : ℝ) * δ ^ 3)) *
                  dlgsW (hrA1 P Q) (hrU P Q τ x) (dlgQ q₀ (δ ^ 3) k))
    (kc jz : ℤ) (M : ℝ) (hkc1 : c ≤ ((kc : ℝ) + θl) * δ ^ 3) (hkc2 : ((kc : ℝ) + θl - 1) * δ ^ 3 < c)
    (hjz1 : qs - η < ((jz : ℝ) + θl) * δ ^ 3) (hjz2 : ((jz : ℝ) + θl - 1) * δ ^ 3 ≤ qs - η)
    (hM : M * δ ^ 3 * Real.sqrt (rkS P Q x) = 1) :
    (κ ^ 2 + μ ^ 2) * δ / 2 * M * (1 - (c / qs + 2 * √(η / qs)) -
        (8 * (C * √Real.pi) * (1 + C * √Real.pi) + 2 * ((hi ^ 5 + 2 * qs * Mm * (hi ^ 4 + hi ^ 8)) / 2) * Real.sqrt (rkS P Q x) / Real.pi) * δ ^ 3) ≤
      ∑ k ∈ Finset.Ico kc jz, Y k ^ 2 ∧
    ∑ k ∈ Finset.Ico kc jz, Y k ^ 2 ≤ (κ ^ 2 + μ ^ 2) * δ / 2 * M *
      (1 + (8 * (C * √Real.pi) * (1 + C * √Real.pi) + 2 * ((hi ^ 5 + 2 * qs * Mm * (hi ^ 4 + hi ^ 8)) / 2) * Real.sqrt (rkS P Q x) / Real.pi) * δ ^ 3) := by
  obtain ⟨m, hm, hk1, hbandR, hbandU2, hjzNh, hjzqs, hjzlo, hjzpos⟩ := rk_band_geom hθl hθl1 (δ := δ) (qs := qs) (c := c) (η := η) (kc := kc) (jz := jz) hδ hδ1 hqs hc hδη hδc hbig hη hkc1 hkc2 hjz1 hjz2
  obtain ⟨hbandR1, hbandR2⟩ : (∀ i : ℕ, i ≤ m + 1 → c ≤ (((kc + (i : ℤ) : ℤ) : ℝ) + θl) * δ ^ 3) ∧
      (∀ i : ℕ, i ≤ m + 1 → (((kc + (i : ℤ) : ℤ) : ℝ) + θl) * δ ^ 3 < qs - η / 2) :=
    ⟨fun i hi => (hbandR i hi).1, fun i hi => (hbandR i hi).2⟩
  have hh : 0 < δ ^ 3 := by positivity
  have hh1 : δ ^ 3 ≤ 1 := pow_le_one₀ hδ.le hδ1
  have hqe : ∀ k : ℤ, dlgQ q₀ (δ ^ 3) k = ((k : ℝ) + θl) * δ ^ 3 := fun k => by unfold dlgQ; rw [hq₀]; ring
  have hqk : ∀ k : ℤ, kpUg θl (δ ^ 3) k = ((k : ℝ) + θl) * δ ^ 3 := fun k => rfl
  have hsumeq : ∑ k ∈ Finset.Ico kc jz, Y k ^ 2 = ∑ i ∈ range (m + 1), Y (kc + (i : ℤ)) ^ 2 := by
    rw [kk_ico_range (fun k => Y k ^ 2) (by omega : kc ≤ jz)]
    have : (jz - kc).toNat = m + 1 := by omega
    rw [this]
  rw [hsumeq]
  set I : ℝ := ∫ s in (c0 + c) / 2..qs, Real.arccos (hrU P Q τ x s) with hI
  set Θ : ℝ → ℝ := dlgsPhase (hrU P Q τ x) ((c0 + c) / 2) with hΘ
  have hρ0 : 0 ≤ (δ ^ 3) ^ (1 / 6 : ℝ) * (1 / √Real.pi) := by positivity
  have hρ2 : ((δ ^ 3) ^ (1 / 6 : ℝ) * (1 / √Real.pi)) ^ 2 = δ / Real.pi := by
    rw [mul_pow, rk_rpow_sq hδ, div_pow, one_pow, Real.sq_sqrt hπ.le]; ring
  have hbandU : ∀ i : ℕ, i ≤ m + 1 → dlgQ q₀ (δ ^ 3) (kc + (i : ℤ)) ∈ Set.Ioo ((c0 + c) / 2) (qs - η / 2) := by
    intro i hi
    rw [hqe]
    exact ⟨by linarith only [hbandR1 i hi, hc0c], hbandR2 i hi⟩
  have hrep : ∀ i : ℕ, i < m + 1 → |Y (kc + (i : ℤ)) - ((δ ^ 3) ^ (1 / 6 : ℝ) * (1 / √Real.pi)) * dlgsW (hrA1 P Q) (hrU P Q τ x) (dlgQ q₀ (δ ^ 3) (kc + (i : ℤ))) *
      (κ * Real.cos (Θ (dlgQ q₀ (δ ^ 3) (kc + (i : ℤ))) / δ ^ 3 + (-I / δ ^ 3 + Real.pi / 4)) +
        μ * Real.sin (Θ (dlgQ q₀ (δ ^ 3) (kc + (i : ℤ))) / δ ^ 3 + (-I / δ ^ 3 + Real.pi / 4)))| ≤
      (C * √Real.pi) * ((|κ| + |μ|) * (((δ ^ 3) ^ (1 / 6 : ℝ) * (1 / √Real.pi)) * δ ^ 3)) *
        dlgsW (hrA1 P Q) (hrU P Q τ x) (dlgQ q₀ (δ ^ 3) (kc + (i : ℤ))) := by
    intro i hi
    have hlo : c ≤ dlgQ q₀ (δ ^ 3) (kc + (i : ℤ)) := by rw [hqe]; exact hbandR1 i (by omega)
    have hup : dlgQ q₀ (δ ^ 3) (kc + (i : ℤ)) ≤ qs - η := by rw [hqe]; exact hbandU2 i hi
    have hb := hbulk (kc + (i : ℤ)) hlo hup
    have e1 : dlgP Θ q₀ (δ ^ 3) (kc + (i : ℤ)) - I / δ ^ 3 + Real.pi / 4 = Θ (dlgQ q₀ (δ ^ 3) (kc + (i : ℤ))) / δ ^ 3 + (-I / δ ^ 3 + Real.pi / 4) := by
      unfold dlgP; ring
    rw [e1] at hb
    refine hb.trans (le_of_eq ?_)
    have hπs : √Real.pi ≠ 0 := (Real.sqrt_pos.2 hπ).ne'
    field_simp
  have hw2 : ∀ i : ℕ, i < m + 1 → dlgsW (hrA1 P Q) (hrU P Q τ x) (dlgQ q₀ (δ ^ 3) (kc + (i : ℤ))) ^ 2 =
      kpPg θl qs (δ ^ 3) (kc + (i : ℤ)) / Real.sqrt (rkS P Q x) := by
    intro i hi
    have hq1 : dlgQ q₀ (δ ^ 3) (kc + (i : ℤ)) = kpUg θl (δ ^ 3) (kc + (i : ℤ)) := by rw [hqe, hqk]
    rw [hq1]
    have hlo : c ≤ kpUg θl (δ ^ 3) (kc + (i : ℤ)) := by rw [hqk]; exact hbandR1 i (by omega)
    have hup : kpUg θl (δ ^ 3) (kc + (i : ℤ)) < qs := by
      rw [hqk]; linarith only [hbandU2 i hi, hη]
    have hq0 : 0 < kpUg θl (δ ^ 3) (kc + (i : ℤ)) := lt_of_lt_of_le hc hlo
    have hint : 0 < (1 - P * kpUg θl (δ ^ 3) (kc + (i : ℤ)) ^ 2) * (1 - Q * kpUg θl (δ ^ 3) (kc + (i : ℤ)) ^ 2) :=
      mul_pos (dlgh_fac hP hα hq0 hup.le) (dlgh_fac hQ hβ hq0 hup.le)
    exact rk_w_sq_kpPg hP hQ hτ hs hq0.le hup hint hspos
  have hend : kpUg θl (δ ^ 3) (kc + (m : ℤ) + 1) < qs := by
    rw [← hm, hqk]; exact hjzqs
  have hNh : ((m : ℝ) + 1) * δ ^ 3 ≤ qs := hjzNh
  obtain ⟨hlow, hup⟩ := rk_band_mass D hθl (q0 := q₀) (Y := Y) (h := δ ^ 3) (δ := δ) (E := C * √Real.pi) (κ := κ) (μ := μ)
    (φ0 := -I / δ ^ 3 + Real.pi / 4) (qs := qs) (sq := Real.sqrt (rkS P Q x)) (M := M) (kc := kc) m hh hh1 hδ hρ0 hρ2 hE0 hsq hM hqs hk1 hNh hend
    hbandU hrep hw2
  have ha : kpUg θl (δ ^ 3) (kc - 1) / qs + √(1 - (kpUg θl (δ ^ 3) (kc + (m : ℤ)) / qs) ^ 2) ≤ c / qs + 2 * √(η / qs) := by
    have hjm : kc + (m : ℤ) = jz - 1 := by omega
    rw [hjm]
    have hq1 : kpUg θl (δ ^ 3) (jz - 1) = ((jz : ℝ) + θl - 1) * δ ^ 3 := by
      rw [hqk]; push_cast; ring
    have hq2 : kpUg θl (δ ^ 3) (kc - 1) = ((kc : ℝ) + θl - 1) * δ ^ 3 := by
      rw [hqk]; push_cast; ring
    refine rk_a_bound hqs hh (by linarith only [hδη, h3δ, hη]) ?_ ?_ ?_ ?_
    · rw [hq2]; exact hkc2
    · rw [hq1]; exact hjzlo
    · rw [hq1]; linarith only [hjz2, hη]
    · rw [hq1]; exact hjzpos
  have hT0 : 0 ≤ (κ ^ 2 + μ ^ 2) * δ / 2 * M := by
    have hM0 : 0 ≤ M := by
      have : M = 1 / (δ ^ 3 * Real.sqrt (rkS P Q x)) := by
        field_simp; linarith
      rw [this]; positivity
    positivity
  have hθ : 8 * (C * √Real.pi) * (1 + C * √Real.pi) * δ ^ 3 + 2 * ((hi ^ 5 + 2 * qs * Mm * (hi ^ 4 + hi ^ 8)) / 2) * Real.sqrt (rkS P Q x) * δ ^ 3 / Real.pi =
      (8 * (C * √Real.pi) * (1 + C * √Real.pi) + 2 * ((hi ^ 5 + 2 * qs * Mm * (hi ^ 4 + hi ^ 8)) / 2) * Real.sqrt (rkS P Q x) / Real.pi) * δ ^ 3 := by ring
  rw [hθ] at hlow hup
  constructor
  · refine le_trans ?_ hlow
    apply mul_le_mul_of_nonneg_left _ hT0
    linarith only [ha]
  · exact hup

/-- **Window and band mass in units of the Gauss weight.**  The conclusion of `rk_bulk` for the Airy window `RkWinAt`, together with, for every band `kc ≤ k < jz`
(`q_{kc-1} < c ≤ q_{kc}`, `q_{jz-1} ≤ q_* - η < q_{jz}`) and every `M` with `M δ³ √s = 1`, `s = rkS P Q x`:
`T M (1 - a_B - θ₀ δ³) ≤ Σ_{kc ≤ k < jz} Y_k² ≤ T M (1 + θ₀ δ³)`, `T = (κ² + μ²) δ/2`, `a_B = c/q_* + 2√(η/q_*)`. -/
theorem rk_bulk_band {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (a b τ x qs : ℝ) (hqs : 0 < qs) (hτ : τ ^ 2 = 1)
    (hκ : 0 < 1 - τ * x) (hα : 0 < 1 - P * qs ^ 2) (hβ : 0 < 1 - Q * qs ^ 2) (hturn : Phi P Q τ x (qs ^ 2) = 0)
    (hosc0 : ∀ q : ℝ, 0 < q → q < qs → |hrU P Q τ x q| < 1) :
    ∃ (r Cmu ξ0 gmax gmin c1 c2 CA : ℝ), 0 < r ∧ r ≤ qs / 4 ∧ 0 < CA ∧ 0 < Cmu ∧ 0 < ξ0 ∧ 0 < gmax ∧ 0 < gmin ∧ gmin ≤ gmax ∧
      0 < c1 ∧ c1 ≤ c2 ∧
      ∀ c0 : ℝ, 0 < c0 → c0 < qs / 2 → ∀ η : ℝ, 0 < η → η ≤ r / 2 → ∀ c : ℝ, c0 < c → c < qs - r → ∃ δ0 θ0 : ℝ, 0 < δ0 ∧ 0 ≤ θ0 ∧
        ∀ (δ : ℝ) (Y : ℤ → ℝ) (Ymax : ℝ), 0 < δ → δ ≤ δ0 →
          (∀ k : ℤ, 1 ≤ k → jac (hrAk P Q a b (δ ^ 3)) (hrCk P Q τ x a b (δ ^ 3)) Y k = 0) →
          (∀ k : ℤ, qs + δ ^ 3 ≤ ((k : ℝ) + 1 / 2) * δ ^ 3 → |Y k| ≤ Ymax) →
          ∃ (J m N : ℤ) (κ μ : ℝ), RkWinAt P Q τ x qs Y Ymax r CA Cmu ξ0 gmin gmax c1 c2 δ J m N κ μ ∧
            ∀ (kc jz : ℤ) (M : ℝ), c ≤ ((kc : ℝ) + 1 / 2) * δ ^ 3 → ((kc : ℝ) - 1 / 2) * δ ^ 3 < c →
              qs - η < ((jz : ℝ) + 1 / 2) * δ ^ 3 → ((jz : ℝ) - 1 / 2) * δ ^ 3 ≤ qs - η →
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
    rk_bulk hP hQ a b τ x qs hqs hτ hκ hα hβ hturn hosc0
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
  exact rk_band_assemble (θl := 1 / 2) (q₀ := δ ^ 3 / 2) (by norm_num) (by norm_num) hP hQ τ x qs hqs hτ hα hβ hs hspos hsq hc0 hc0c hη hcη hc hπ hE0 hδ hδ1 hδη hδc (by ring)
    (by
      have : η < qs - η - c := by linarith
      linarith) h3δ D hhi0 hbulk kc jz M hkc1 (by linarith) hjz1 (by linarith) hM

/-- info: 'FormalResearch.Special.rk_bulk_band' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.rk_bulk_band

end FormalResearch.Special
