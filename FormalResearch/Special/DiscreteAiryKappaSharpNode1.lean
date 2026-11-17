module

public import FormalResearch.Special.DiscreteAiryKappaSharpMatch
public import FormalResearch.Special.DiscreteAiryKappaBand3j

/-!
# Sharp `κ`: the node-level match at the band end (plan K1, sharp constant, step 10)

* `ksf_X`, `ksf_g`: the chart sequences of `KkData` (`turnX`, `langerAmp ∘ dalQ`) are `ζ(q_k)/δ²` and `g(q_k)` at `q_k = kpU (δ³) k`;
* `ksf_sq`: `|√I - T| ≤ T E`, `E ≤ 1`, `I ≥ 0`, `T ≥ 0` give `(1-E)² T² ≤ I ≤ (1+E)² T²`;
* `ksf_match`: **the Ermakov amplitude of the actual chain at the band end `b` is `κ²δ/π (1 + O(E))`**, `E = ksfE`, with `ηr = r_b² - 1` bounded by `3β/b²`.

**Claim class: proved.**
-/

@[expose] public section

open Finset Set Real FormalResearch.Racah FormalResearch.Racah.P3 FormalResearch.Wigner

namespace FormalResearch.Special

/-- `(δ³)^{-2/3} = 1/δ²`. -/
lemma ksf_rpow {δ : ℝ} (hδ : 0 < δ) : (δ ^ 3) ^ (-(2 / 3 : ℝ)) = 1 / δ ^ 2 := by
  have h1 : (δ ^ 3 : ℝ) = δ ^ (3 : ℝ) := by norm_cast
  rw [h1, ← Real.rpow_mul hδ.le]
  have h2 : (3 : ℝ) * (-(2 / 3)) = -(2 : ℝ) := by norm_num
  rw [h2, Real.rpow_neg hδ.le, one_div]
  norm_cast

/-- The lattice variable of the chart: `X_k = ζ(q_k)/δ²`. -/
lemma ksf_X (x δ : ℝ) (hδ : 0 < δ) (k : ℤ) :
    turnX (hrU 1 0 1 x) (√(1 - x ^ 2)) (δ ^ 3 / 2) δ k = kshZ x (kpU (δ ^ 3) k) / δ ^ 2 := by
  unfold turnX dalX kshZ
  rw [ksf_rpow hδ]
  have : dalQ (δ ^ 3 / 2) δ k = kpU (δ ^ 3) k := by unfold dalQ kpU; ring
  rw [this]
  ring

/-- The Langer amplitude along the lattice: `g_k = g(q_k)`. -/
lemma ksf_g (x δ : ℝ) (k : ℤ) :
    langerAmp (hrU 1 0 1 x) (hrA1 1 0) (√(1 - x ^ 2)) (dalQ (δ ^ 3 / 2) δ k) = kshG x (kpU (δ ^ 3) k) := by
  unfold kshG
  have : dalQ (δ ^ 3 / 2) δ k = kpU (δ ^ 3) k := by unfold dalQ kpU; ring
  rw [this]

/-- From `|√I - T| ≤ T E` to the two-sided bound on `I`. -/
lemma ksf_sq {I T E : ℝ} (hI : 0 ≤ I) (hT : 0 ≤ T) (hE : E ≤ 1) (h : abs (√I - T) ≤ T * E) :
    (1 - E) ^ 2 * T ^ 2 ≤ I ∧ I ≤ (1 + E) ^ 2 * T ^ 2 := by
  have hs0 : 0 ≤ √I := Real.sqrt_nonneg I
  have hs2 : √I ^ 2 = I := Real.sq_sqrt hI
  obtain ⟨h1, h2⟩ := abs_le.1 h
  have hlow : T * (1 - E) ≤ √I := by linarith
  have hup : √I ≤ T * (1 + E) := by linarith
  constructor
  · have h0 : 0 ≤ T * (1 - E) := mul_nonneg hT (by linarith)
    have := pow_le_pow_left₀ h0 hlow 2
    rw [hs2] at this
    nlinarith [this]
  · have := pow_le_pow_left₀ hs0 hup 2
    rw [hs2] at this
    nlinarith [this]

/-- The error of the bond match (with `|η_r| ≤ ηb`). -/
noncomputable def ksfE (x A δ ηb Cr Ye : ℝ) : ℝ :=
  6 * ((3 * δ ^ 3 / (A * x ^ 2) + 2 * (δ ^ 3 + ηb) / x ^ 4) / x) / A ^ 2 + 4 * (2 * (Cr * (δ ^ 2 * √δ) + Ye / 8)) / A

lemma ksfE_mono {x A δ ηr ηb Cr Ye : ℝ} (hx : 0 < x) (hA : 0 < A) (h : |ηr| ≤ ηb) :
    6 * ((3 * δ ^ 3 / (A * x ^ 2) + 2 * (δ ^ 3 + |ηr|) / x ^ 4) / x) / A ^ 2 + 4 * (2 * (Cr * (δ ^ 2 * √δ) + Ye / 8)) / A ≤
      ksfE x A δ ηb Cr Ye := by
  unfold ksfE
  have h1 : 2 * (δ ^ 3 + |ηr|) / x ^ 4 ≤ 2 * (δ ^ 3 + ηb) / x ^ 4 :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  have h2 : (3 * δ ^ 3 / (A * x ^ 2) + 2 * (δ ^ 3 + |ηr|) / x ^ 4) / x ≤ (3 * δ ^ 3 / (A * x ^ 2) + 2 * (δ ^ 3 + ηb) / x ^ 4) / x :=
    div_le_div_of_nonneg_right (by linarith) hx.le
  have h3 : 6 * ((3 * δ ^ 3 / (A * x ^ 2) + 2 * (δ ^ 3 + |ηr|) / x ^ 4) / x) / A ^ 2 ≤
      6 * ((3 * δ ^ 3 / (A * x ^ 2) + 2 * (δ ^ 3 + ηb) / x ^ 4) / x) / A ^ 2 :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  linarith

/-- **The Ermakov amplitude at the band end** (`ksh_bond_match` for the actual chain, with `η_r = r_b² - 1`, `|η_r| ≤ 3β/b²`):
`(1-E)² κ²δ/π ≤ I_b(Ŷ) ≤ (1+E)² κ²δ/π`, `E = ksfE x A δ (3β/b²) C_r Y_e ≤ 1`. -/
theorem ksf_match {M σ N b : ℤ} {x : ℚ} {rs c1s c2s δ κ Cr Ye A : ℝ} (hx0 : 0 < (x : ℝ)) (hx1 : (x : ℝ) < 1)
    (C : KshChart (x : ℝ) rs c1s c2s) (hδ : 0 < δ) (hb : 1 ≤ b) (hβb : kl_beta (M : ℝ) (σ : ℝ) < (b : ℝ) ^ 2)
    (hbh : ((b : ℝ) * δ ^ 3) ^ 2 < 1)
    (hq1 : √(1 - (x : ℝ) ^ 2) - rs ≤ kpU (δ ^ 3) (b - 1)) (hqb : kpU (δ ^ 3) b < √(1 - (x : ℝ) ^ 2))
    (hA0 : 0 < A) (hA1 : A ≤ 1) (hAm : A ^ 2 ≤ √(1 - (x : ℝ) ^ 2) ^ 2 - kpU (δ ^ 3) (b - 1) ^ 2)
    (hA0' : A ^ 2 ≤ √(1 - (x : ℝ) ^ 2) ^ 2 - kpU (δ ^ 3) b ^ 2)
    (hηb : 3 * kl_beta (M : ℝ) (σ : ℝ) / (b : ℝ) ^ 2 ≤ (x : ℝ) ^ 2) (hηb2 : 3 * kl_beta (M : ℝ) (σ : ℝ) / (b : ℝ) ^ 2 ≤ 1 / 2)
    (hgb : 0 < kshG (x : ℝ) (kpU (δ ^ 3) b)) (hgb1 : 0 < kshG (x : ℝ) (kpU (δ ^ 3) (b - 1))) (hCr : 0 ≤ Cr)
    (hrb : |hahn3jY M σ N x b - κ * (kshG (x : ℝ) (kpU (δ ^ 3) b) * airyAi (kshZ (x : ℝ) (kpU (δ ^ 3) b) / δ ^ 2))| ≤ Cr * δ ^ 3 * |κ|)
    (hrb1 : |hahn3jY M σ N x (b - 1) -
      κ * (kshG (x : ℝ) (kpU (δ ^ 3) (b - 1)) * airyAi (kshZ (x : ℝ) (kpU (δ ^ 3) (b - 1)) / δ ^ 2))| ≤ Cr * δ ^ 3 * |κ|)
    (hyb : (-(kshZ (x : ℝ) (kpU (δ ^ 3) b) / δ ^ 2)) ^ (-(3 / 2) : ℝ) ≤ Ye)
    (hyb1 : (-(kshZ (x : ℝ) (kpU (δ ^ 3) (b - 1)) / δ ^ 2)) ^ (-(3 / 2) : ℝ) ≤ Ye)
    (hE : ksfE (x : ℝ) A δ (3 * kl_beta (M : ℝ) (σ : ℝ) / (b : ℝ) ^ 2) Cr Ye ≤ 1) :
    (1 - ksfE (x : ℝ) A δ (3 * kl_beta (M : ℝ) (σ : ℝ) / (b : ℝ) ^ 2) Cr Ye) ^ 2 * (κ ^ 2 * δ / Real.pi) ≤
        kermI (hrAk 1 0 (M : ℝ) (σ : ℝ) (δ ^ 3)) (kpP (√(1 - (x : ℝ) ^ 2)) (δ ^ 3)) (hahn3jY M σ N x) b ∧
      kermI (hrAk 1 0 (M : ℝ) (σ : ℝ) (δ ^ 3)) (kpP (√(1 - (x : ℝ) ^ 2)) (δ ^ 3)) (hahn3jY M σ N x) b ≤
        (1 + ksfE (x : ℝ) A δ (3 * kl_beta (M : ℝ) (σ : ℝ) / (b : ℝ) ^ 2) Cr Ye) ^ 2 * (κ ^ 2 * δ / Real.pi) := by
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
  obtain ⟨hapos, ha, -, -⟩ := kb_coef (M : ℝ) (σ : ℝ) (x : ℝ) (δ ^ 3) hb hβb hbh
  obtain ⟨hηr, -⟩ := kb_eta_bound (M := (M : ℝ)) (σ := (σ : ℝ)) hb' hβb
  have h1 := ksh_bond_match (x := (x : ℝ)) (r := rs) (c1 := c1s) (c2 := c2s) (δ := δ) (κ := κ) (Cr := Cr) (Ye := Ye) (A := A)
    (ηr := rr (M : ℝ) (σ : ℝ) (b : ℝ) ^ 2 - 1) (Y := hahn3jY M σ N x) (a := hrAk 1 0 (M : ℝ) (σ : ℝ) (δ ^ 3)) (k := b) hx0 hx1 C hδ hb hq1 hqb hA0 hA1
    hAm hA0' hapos ha (hηr.trans hηb) (hηr.trans hηb2) hgb hgb1 hCr hrb hrb1 hyb hyb1
  have h2 := ksfE_mono (x := (x : ℝ)) (A := A) (δ := δ) (ηr := rr (M : ℝ) (σ : ℝ) (b : ℝ) ^ 2 - 1)
    (ηb := 3 * kl_beta (M : ℝ) (σ : ℝ) / (b : ℝ) ^ 2) (Cr := Cr) (Ye := Ye) hx0 hA0 hηr
  have hT0 : 0 ≤ |κ * √(δ / π)| := abs_nonneg _
  have h3 : abs (√(kermI (hrAk 1 0 (M : ℝ) (σ : ℝ) (δ ^ 3)) (kpP (√(1 - (x : ℝ) ^ 2)) (δ ^ 3)) (hahn3jY M σ N x) b) - |κ * √(δ / π)|) ≤
      |κ * √(δ / π)| * ksfE (x : ℝ) A δ (3 * kl_beta (M : ℝ) (σ : ℝ) / (b : ℝ) ^ 2) Cr Ye :=
    h1.trans (mul_le_mul_of_nonneg_left h2 hT0)
  have hqs : 0 < √(1 - (x : ℝ) ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have hrad := kp_rad_ge (a := hrAk 1 0 (M : ℝ) (σ : ℝ) (δ ^ 3)) (x := (x : ℝ)) (qs := √(1 - (x : ℝ) ^ 2)) (h := δ ^ 3) (A := A)
    (η := rr (M : ℝ) (σ : ℝ) (b : ℝ) ^ 2 - 1) (Real.sq_sqrt (by nlinarith)) hb (by positivity) hA0 hAm hA0' ha (hηr.trans hηb)
  have hI0 := kermI_nonneg (a := hrAk 1 0 (M : ℝ) (σ : ℝ) (δ ^ 3)) (Y := hahn3jY M σ N x) (kpP_pos hA0 hA0') (kpP_pos hA0 hAm) hrad
  have h4 := ksf_sq hI0 hT0 hE h3
  have hT2 : |κ * √(δ / π)| ^ 2 = κ ^ 2 * δ / Real.pi := by
    rw [sq_abs, mul_pow, Real.sq_sqrt (by positivity)]; ring
  rw [hT2] at h4
  exact h4

/-- info: 'FormalResearch.Special.ksf_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.ksf_match

end FormalResearch.Special
