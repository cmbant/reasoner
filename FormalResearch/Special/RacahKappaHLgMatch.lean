module

public import FormalResearch.Special.DiscreteLgHahnMatch
public import FormalResearch.Special.RacahKappaHLgHahn

/-!
# Half-integer Racah chains: lattice and Airy-site facts on the shifted lattice

Twins of `dlgh_lattice`, `dlgh_qJ`, `dlgh_site_all` (`DiscreteLgHahnMatch`) for the lattice `q_k = (k + 1) δ³`; declarations carry the suffix `H`.

**Claim class: proved.**
-/

@[expose] public section

open Finset FormalResearch.Racah.P3 FormalResearch.DiscreteAiry
open scoped Real

namespace FormalResearch.Special
/-- **The Airy datum at one lattice site** (`DlgAiryAt`) from the Langer chart facts at that site and the D2A pointwise Airy shape. -/
theorem dlgh_airyatH {P Q τ x qs : ℝ} {Y : ℤ → ℝ} {κ μ Ts Φmin lo C δ : ℝ} {k : ℤ} {Θ : ℝ → ℝ}
    (hδ : 0 < δ) (hlo : 0 < lo) (hΦ : 0 < Φmin) (hC : 0 ≤ C)
    (hA : 0 < hrA1 P Q (dalQ (δ ^ 3) δ k)) (hu : |hrU P Q τ x (dalQ (δ ^ 3) δ k)| < 1)
    (hneg : langerZeta (hrU P Q τ x) qs (dalQ (δ ^ 3) δ k) < 0)
    (hphase : 2 / 3 * (-langerZeta (hrU P Q τ x) qs (dalQ (δ ^ 3) δ k)) ^ (3 / 2 : ℝ) = Ts - Θ (dalQ (δ ^ 3) δ k))
    (hg4 : (langerAmp (hrU P Q τ x) (hrA1 P Q) qs (dalQ (δ ^ 3) δ k)) ^ 4 =
      4 * |langerZeta (hrU P Q τ x) qs (dalQ (δ ^ 3) δ k)| /
        |4 * hrA1 P Q (dalQ (δ ^ 3) δ k) ^ 2 * (1 - hrU P Q τ x (dalQ (δ ^ 3) δ k) ^ 2)|)
    (hg0 : 0 < langerAmp (hrU P Q τ x) (hrA1 P Q) qs (dalQ (δ ^ 3) δ k))
    (hΦle : Φmin ≤ Ts - Θ (dalQ (δ ^ 3) δ k))
    (hwlo : lo ≤ dlgsW (hrA1 P Q) (hrU P Q τ x) (dalQ (δ ^ 3) δ k))
    (hAiry : |Y k - (κ * daoPhi (fun k => langerAmp (hrU P Q τ x) (hrA1 P Q) qs (dalQ (δ ^ 3) δ k))
          (turnX (hrU P Q τ x) qs (δ ^ 3) δ) k +
        μ * daoPsi (fun k => langerAmp (hrU P Q τ x) (hrA1 P Q) qs (dalQ (δ ^ 3) δ k))
          (turnX (hrU P Q τ x) qs (δ ^ 3) δ) k)| ≤
      C * δ ^ 3 * (|κ| * airyWt (turnX (hrU P Q τ x) qs (δ ^ 3) δ k) +
        |μ| * airyBiWt (turnX (hrU P Q τ x) qs (δ ^ 3) δ k))) :
    DlgAiryAt κ μ Y (dlgsW (hrA1 P Q) (hrU P Q τ x)) Θ (δ ^ 3) (δ ^ 3) Ts Φmin
      ((((3 / 2) * Φmin) ^ (2 / 3 : ℝ)) ^ (1 / 4 : ℝ) * lo) C k := by
  set q : ℝ := dalQ (δ ^ 3) δ k with hq
  set ζ : ℝ := langerZeta (hrU P Q τ x) qs q with hζ
  set g : ℝ := langerAmp (hrU P Q τ x) (hrA1 P Q) qs q with hgdef
  set W : ℝ := dlgsW (hrA1 P Q) (hrU P Q τ x) q with hWdef
  have hh : 0 < δ ^ 3 := by positivity
  have hZ : 0 < -ζ := neg_pos.2 hneg
  have hW : 0 < W := hlo.trans_le hwlo
  have h4 : g ^ 4 = -ζ * W ^ 4 := by
    have := dlgh_g4 (A0 := hrA1 P Q q) (u0 := hrU P Q τ x q) (Z := -ζ) (g := g) hA hu hZ (by rw [hg4, neg_neg])
    exact this
  obtain ⟨hgeq, hyp, hM2, hM3⟩ := dlgh_site_arith hg0 hW hZ hh h4
  have hDpos : Φmin ≤ 2 / 3 * (-ζ) ^ (3 / 2 : ℝ) := by rw [hphase]; exact hΦle
  have hXk : turnX (hrU P Q τ x) qs (δ ^ 3) δ k = (δ ^ 3) ^ (-(2 / 3) : ℝ) * ζ := rfl
  set y : ℝ := (δ ^ 3) ^ (-(2 / 3) : ℝ) * (-ζ) with hy
  have hXy : turnX (hrU P Q τ x) qs (δ ^ 3) δ k = -y := by
    rw [hXk, hy]; ring
  have hyw : y ^ (-(1 / 4) : ℝ) ≥ 0 := (Real.rpow_pos_of_pos hyp _).le
  have hq' : dlgQ (δ ^ 3) (δ ^ 3) k = q := rfl
  refine ⟨g, y, hyp, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hq']; exact hM2
  · have : (2 / 3 * (-ζ) ^ (3 / 2 : ℝ)) / δ ^ 3 = Ts / δ ^ 3 - dlgP Θ (δ ^ 3) (δ ^ 3) k := by
      rw [hphase, sub_div]; rfl
    rw [hM3, this]
  · have : δ ^ 3 * dlgP Θ (δ ^ 3) (δ ^ 3) k = Θ q := by
      unfold dlgP; rw [mul_div_cancel₀ _ hh.ne']; rfl
    rw [this]; exact hΦle
  · -- g ≥ gmin
    have hZmin : ((3 / 2) * Φmin) ^ (2 / 3 : ℝ) ≤ -ζ := by
      have h1 : (3 / 2) * Φmin ≤ (-ζ) ^ (3 / 2 : ℝ) := by linarith
      have h2 := Real.rpow_le_rpow (by positivity) h1 (by norm_num : (0 : ℝ) ≤ 2 / 3)
      rwa [← Real.rpow_mul hZ.le, show (3 / 2 : ℝ) * (2 / 3) = 1 by norm_num, Real.rpow_one] at h2
    rw [hgeq]
    exact mul_le_mul (Real.rpow_le_rpow (by positivity) hZmin (by norm_num)) hwlo hlo.le (Real.rpow_nonneg hZ.le _)
  · -- Airy shape
    have hAi : airyAi (turnX (hrU P Q τ x) qs (δ ^ 3) δ k) = airyAi (-y) := by rw [hXy]
    have hBi : airyBi (turnX (hrU P Q τ x) qs (δ ^ 3) δ k) = airyBi (-y) := by rw [hXy]
    have hwt : airyWt (turnX (hrU P Q τ x) qs (δ ^ 3) δ k) ≤ y ^ (-(1 / 4) : ℝ) ∧
        airyBiWt (turnX (hrU P Q τ x) qs (δ ^ 3) δ k) ≤ y ^ (-(1 / 4) : ℝ) := by
      rw [hXy]
      have hxi : airyXi (-y) = 0 := by
        unfold airyXi
        rw [max_eq_right (by linarith), Real.zero_rpow (by norm_num)]; ring
      have hab : |-y| = y := by rw [abs_neg, abs_of_pos hyp]
      have hrp : (2 + y) ^ (-(1 / 4) : ℝ) ≤ y ^ (-(1 / 4) : ℝ) :=
        Real.rpow_le_rpow_of_nonpos hyp (by linarith) (by norm_num)
      unfold airyWt airyBiWt
      rw [hxi, hab]
      simp only [neg_zero, Real.exp_zero, mul_one]
      exact ⟨hrp, hrp⟩
    have hC' : C * δ ^ 3 * (|κ| * airyWt (turnX (hrU P Q τ x) qs (δ ^ 3) δ k) +
        |μ| * airyBiWt (turnX (hrU P Q τ x) qs (δ ^ 3) δ k)) ≤ C * (δ ^ 3) * ((|κ| + |μ|) * y ^ (-(1 / 4) : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [mul_le_mul_of_nonneg_left hwt.1 (abs_nonneg κ), mul_le_mul_of_nonneg_left hwt.2 (abs_nonneg μ)]
    have := hAiry
    unfold daoPhi daoPsi at this
    rw [hAi, hBi] at this
    exact this.trans hC'

lemma dlgh_latticeH {δ c d : ℝ} (hδ : 0 < δ) (k : ℤ) :
    (c ≤ dlgQ (δ ^ 3) (δ ^ 3) k ∧ dlgQ (δ ^ 3) (δ ^ 3) k ≤ d) ↔
      (⌈(c - δ ^ 3) / δ ^ 3⌉ ≤ k ∧ k ≤ ⌊(d - δ ^ 3) / δ ^ 3⌋) := by
  have hh : 0 < δ ^ 3 := by positivity
  rw [Int.ceil_le, Int.le_floor, div_le_iff₀ hh, le_div_iff₀ hh]
  unfold dlgQ
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith


lemma dlgh_qJH {qs r δ : ℝ} {J : ℤ} (hδ : 0 < δ) (h1 : qs - r ≤ ((J : ℝ) + 1) * δ ^ 3)
    (h2 : ((J : ℝ) + 1) * δ ^ 3 < qs - r + δ ^ 3) (h3 : δ ^ 3 ≤ r / 4) :
    ∀ k : ℤ, J ≤ k → k ≤ J + 1 → qs - r ≤ dalQ (δ ^ 3) δ k ∧ dalQ (δ ^ 3) δ k ≤ qs - r / 2 := by
  intro k hk1 hk2
  have e2 : dalQ (δ ^ 3) δ k = ((k : ℝ) + 1) * δ ^ 3 := by unfold dalQ; ring
  rw [e2]
  have h3p : 0 < δ ^ 3 := by positivity
  rcases (by omega : k = J ∨ k = J + 1) with rfl | rfl
  · constructor <;> linarith
  · push_cast
    have : (((J : ℝ) + 1) + 1) * δ ^ 3 = ((J : ℝ) + 1) * δ ^ 3 + δ ^ 3 := by ring
    rw [this]
    constructor <;> linarith

/-- The Airy datum `DlgAiryAt` at the two sites `J, J + 1` of the Airy window (assembly of `dlgh_chart`, the phase split and `dlgh_airyatH`). -/
lemma dlgh_site_allH {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (τ x qs : ℝ) (hα : 0 < 1 - P * qs ^ 2) (hβ : 0 < 1 - Q * qs ^ 2)
    {c0 c r ρ δ : ℝ} {J N : ℤ} {κ μ : ℝ} {Y : ℤ → ℝ} {CA : ℝ}
    (hch : ∀ q : ℝ, qs - ρ < q → q < qs →
      langerZeta (hrU P Q τ x) qs q < 0 ∧
      2 / 3 * (-langerZeta (hrU P Q τ x) qs q) ^ (3 / 2 : ℝ) = ∫ s in q..qs, Real.arccos (hrU P Q τ x s) ∧
      (langerAmp (hrU P Q τ x) (hrA1 P Q) qs q) ^ 4 =
        4 * |langerZeta (hrU P Q τ x) qs q| / |4 * hrA1 P Q q ^ 2 * (1 - hrU P Q τ x q ^ 2)| ∧
      0 < langerAmp (hrU P Q τ x) (hrA1 P Q) qs q)
    (hosc : ∀ q ∈ Set.Ico c0 qs, |hrU P Q τ x q| < 1) (hrρ1 : r ≤ ρ / 2) (hc0c : c0 < c) (hcr : c < qs - r)
    (hδ : 0 < δ)
    (hqJ : ∀ k : ℤ, J ≤ k → k ≤ J + 1 → qs - r ≤ dalQ (δ ^ 3) δ k ∧ dalQ (δ ^ 3) δ k ≤ qs - r / 2)
    (hΦpos : 0 < ∫ s in (qs - r / 2)..qs, Real.arccos (hrU P Q τ x s)) (hCA : 0 < CA)
    (hpt : ∀ k ∈ Finset.Icc J (N + 1),
      |Y k - (κ * daoPhi (fun k => langerAmp (hrU P Q τ x) (hrA1 P Q) qs (dalQ (δ ^ 3) δ k))
            (turnX (hrU P Q τ x) qs (δ ^ 3) δ) k +
          μ * daoPsi (fun k => langerAmp (hrU P Q τ x) (hrA1 P Q) qs (dalQ (δ ^ 3) δ k))
            (turnX (hrU P Q τ x) qs (δ ^ 3) δ) k)| ≤
        CA * δ ^ 3 * (|κ| * airyWt (turnX (hrU P Q τ x) qs (δ ^ 3) δ k) +
          |μ| * airyBiWt (turnX (hrU P Q τ x) qs (δ ^ 3) δ k))) (hJN : J < N) (hr : 0 < r) (hc0 : 0 < c0) :
    ∀ k : ℤ, J ≤ k → k ≤ J + 1 →
      DlgAiryAt κ μ Y (dlgsW (hrA1 P Q) (hrU P Q τ x)) (dlgsPhase (hrU P Q τ x) ((c0 + c) / 2)) (δ ^ 3) (δ ^ 3)
        (∫ s in (c0 + c) / 2..qs, Real.arccos (hrU P Q τ x s))
        (∫ s in (qs - r / 2)..qs, Real.arccos (hrU P Q τ x s))
        ((((3 / 2) * (∫ s in (qs - r / 2)..qs, Real.arccos (hrU P Q τ x s))) ^ (2 / 3 : ℝ)) ^ (1 / 4 : ℝ) * 1) CA k := by
  intro k hk1 hk2
  have hc : 0 < c := hc0.trans hc0c
  have hc1pos : 0 < (c0 + c) / 2 := by linarith
  have hfacP : ∀ q : ℝ, 0 < q → q ≤ qs → 0 < 1 - P * q ^ 2 := fun q h1 h2 => dlgh_fac hP hα h1 h2
  have hfacQ : ∀ q : ℝ, 0 < q → q ≤ qs → 0 < 1 - Q * q ^ 2 := fun q h1 h2 => dlgh_fac hQ hβ h1 h2
  obtain ⟨hq1, hq2⟩ := hqJ k hk1 hk2
  have hqc : c < dalQ (δ ^ 3) δ k := by linarith
  have hq0 : 0 < dalQ (δ ^ 3) δ k := hc.trans hqc
  have hqs' : dalQ (δ ^ 3) δ k < qs := by linarith
  have hcq1 : (c0 + c) / 2 ≤ dalQ (δ ^ 3) δ k := by linarith
  obtain ⟨hneg, hI, hg4, hg0⟩ := hch (dalQ (δ ^ 3) δ k) (by linarith) hqs'
  have hsplit := dlgh_split hP hQ τ x qs ((c0 + c) / 2) (dalQ (δ ^ 3) δ k) hc1pos hα hβ hcq1 hqs'.le
  have hΦle := dlgh_tail_ge hP hQ τ x qs ((c0 + c) / 2) (dalQ (δ ^ 3) δ k) (qs - r / 2) hc1pos hα hβ hcq1 hq2
    (by linarith)
  have hu1 : |hrU P Q τ x (dalQ (δ ^ 3) δ k)| < 1 := hosc _ ⟨by linarith, hqs'⟩
  exact dlgh_airyatH (P := P) (Q := Q) (τ := τ) (x := x) (qs := qs) (Y := Y) (κ := κ) (μ := μ) hδ one_pos hΦpos hCA.le
    (hrA_pos (mul_pos (hfacP _ hq0 hqs'.le) (hfacQ _ hq0 hqs'.le))) hu1 hneg (hI.trans hsplit.symm) hg4 hg0
    (by rw [hsplit]; exact hΦle)
    (dlgh_w_ge_one hP hQ (hfacP _ hq0 hqs'.le) (hfacQ _ hq0 hqs'.le) τ x hu1)
    (hpt k (by rw [Finset.mem_Icc]; omega))


end FormalResearch.Special
