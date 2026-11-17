module

public import FormalResearch.Special.DiscreteAiryKappaSharpChart
public import FormalResearch.Special.DiscreteAiryKappaSharpRho

/-!
# Sharp `κ`: the Airy matching of the Ermakov form at a bond (plan K1, sharp constant, step 4)

At a bond `(k, k-1)` of the oscillatory region (`q_{k-1} ≥ q_* - r`, `q_k < q_*`, `α ≥ A`) the chain is `Ŷ_j = κ g_j Ai(X_j) + r_j`
(`|r_j| ≤ C_r δ³ |κ|`, from the Airy matching of the order-sharp theorem), `X_j = ζ(q_j)/δ²`.  With the large-argument asymptotics
`Ai(-y) = π^{-1/2} y^{-1/4} cos(ξ - π/4) + ε`, `|ε| ≤ y^{-7/4}/8`, `ξ = (2/3) y^{3/2}`, and the chart identity `g y^{-1/4} = √(δ P)`
(`KshChart.amp_sq`, `P = 2/α`), `Ŷ_j = t √P_j cos θ_j + e_j` with `t = κ √(δ/π)`, `θ_j = ξ_j - π/4`, `|e_j| ≤ η |t| √P_j`,
`η = 2 (C_r δ²√δ + Y_e/8)` where `y_j^{-3/2} ≤ Y_e` (`ksh_site_eq`).  Since the phase difference has `cos(θ_{k-1} - θ_k) = x/√(1-η̃²)`
(`KshChart.phase`) and `|s/√W - x/√(1-η̃²)| ≤ ρ` (`ksh_site_rho`), `ksh_I_close` gives
`|√I_k(Ŷ) - |κ|√(δ/π)| ≤ |κ|√(δ/π) (4Wρ + √(2W)(η + η))` (`ksh_bond_match`): **the Ermakov amplitude is `I = κ²δ/π (1 + o(1))`**.

**Claim class: proved.**
-/

@[expose] public section

open Set Real FormalResearch.Racah.P3

namespace FormalResearch.Special

/-- Pure real form of the per-site error: `M = g y⁴`, `|Y - κ g Ai| ≤ C_r δ³|κ|`, `|Ai - y⁴ c/√π| ≤ y⁴ y₃₂/8`, `y₃₂ ≤ Y_e`, `M² ≥ 2δ` give
`|Y - κ M c/√π| ≤ 2 (C_r δ²√δ + Y_e/8) · |κ| M/√π`. -/
lemma ksh_err_site {Y κ g y4 y32 Ai c δ Cr Ye : ℝ} (hδ : 0 < δ) (hg : 0 < g) (hy4 : 0 < y4) (hy32 : 0 ≤ y32) (hYe : y32 ≤ Ye)
    (hCr : 0 ≤ Cr) (hM : 2 * δ ≤ (g * y4) ^ 2) (hr : |Y - κ * (g * Ai)| ≤ Cr * δ ^ 3 * |κ|)
    (hAi : |Ai - 1 / √π * y4 * c| ≤ 1 / 8 * (y4 * y32)) :
    |Y - κ * (g * y4 * c / √π)| ≤ 2 * (Cr * (δ ^ 2 * √δ) + Ye / 8) * (|κ| * (g * y4) / √π) := by
  have hπ : 0 < √π := Real.sqrt_pos.2 Real.pi_pos
  have hπ2 : √π ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    have := Real.pi_lt_four
    nlinarith
  have hsδ : 0 < √δ := Real.sqrt_pos.2 hδ
  have hsδ2 := Real.sq_sqrt hδ.le
  set M := g * y4 with hMdef
  have hM0 : 0 < M := by positivity
  have hMs : √δ ≤ M := by
    have : δ ≤ M ^ 2 := by linarith
    calc √δ ≤ √(M ^ 2) := Real.sqrt_le_sqrt this
      _ = M := Real.sqrt_sq hM0.le
  have e1 : Y - κ * (M * c / √π) = (Y - κ * (g * Ai)) + κ * g * (Ai - 1 / √π * y4 * c) := by
    rw [hMdef]; ring
  have b1 : |κ * g * (Ai - 1 / √π * y4 * c)| ≤ |κ| * (M * y32 / 8) := by
    rw [abs_mul, abs_mul, abs_of_pos hg]
    have : g * |Ai - 1 / √π * y4 * c| ≤ g * (1 / 8 * (y4 * y32)) := mul_le_mul_of_nonneg_left hAi hg.le
    calc |κ| * g * |Ai - 1 / √π * y4 * c| = |κ| * (g * |Ai - 1 / √π * y4 * c|) := by ring
      _ ≤ |κ| * (g * (1 / 8 * (y4 * y32))) := mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ = |κ| * (M * y32 / 8) := by rw [hMdef]; ring
  have b2 : |Y - κ * (M * c / √π)| ≤ Cr * δ ^ 3 * |κ| + |κ| * (M * y32 / 8) := by
    rw [e1]
    exact (abs_add_le _ _).trans (add_le_add hr b1)
  refine b2.trans ?_
  -- compare
  have hδ3 : δ ^ 3 ≤ δ ^ 2 * √δ * M := by
    have : δ ^ 3 = δ ^ 2 * √δ * √δ := by
      have : δ = √δ ^ 2 := hsδ2.symm
      calc δ ^ 3 = δ ^ 2 * δ := by ring
        _ = δ ^ 2 * (√δ * √δ) := by rw [← sq, hsδ2]
        _ = _ := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hMs (by positivity)
  have c1 : Cr * δ ^ 3 ≤ Cr * (δ ^ 2 * √δ) * M := by
    calc Cr * δ ^ 3 ≤ Cr * (δ ^ 2 * √δ * M) := mul_le_mul_of_nonneg_left hδ3 hCr
      _ = _ := by ring
  have c2 : M * y32 / 8 ≤ M * (Ye / 8) := by
    have : M * y32 ≤ M * Ye := mul_le_mul_of_nonneg_left hYe hM0.le
    linarith
  have hkey : Cr * δ ^ 3 + M * y32 / 8 ≤ (Cr * (δ ^ 2 * √δ) + Ye / 8) * M := by nlinarith [c1, c2]
  have hpos : 0 ≤ Cr * (δ ^ 2 * √δ) + Ye / 8 := by
    have : 0 ≤ Ye := le_trans hy32 hYe
    positivity
  calc Cr * δ ^ 3 * |κ| + |κ| * (M * y32 / 8) = |κ| * (Cr * δ ^ 3 + M * y32 / 8) := by ring
    _ ≤ |κ| * ((Cr * (δ ^ 2 * √δ) + Ye / 8) * M) := mul_le_mul_of_nonneg_left hkey (abs_nonneg _)
    _ ≤ |κ| * ((Cr * (δ ^ 2 * √δ) + Ye / 8) * M) * (2 / √π) := by
        have h2 : 1 ≤ 2 / √π := by rw [le_div_iff₀ hπ]; linarith
        have h0 : 0 ≤ |κ| * ((Cr * (δ ^ 2 * √δ) + Ye / 8) * M) := by positivity
        nlinarith
    _ = _ := by ring

/-- **The chain at a lattice site as a cosine of the Airy phase**: `Ŷ_j = t √P_j cos θ_j + e_j`, `t = κ√(δ/π)`, `θ_j = (2/3) y_j^{3/2} - π/4`,
`y_j = -ζ(q_j)/δ²`, with `|e_j| ≤ 2(C_r δ²√δ + Y_e/8) |t| √P_j` (`y_j^{-3/2} ≤ Y_e`). -/
lemma ksh_site_eq {x r c1 c2 δ κ Cr Ye : ℝ} {Y : ℤ → ℝ} {j : ℤ} (hx0 : 0 < x) (hx1 : x < 1) (C : KshChart x r c1 c2)
    (hδ : 0 < δ) (hq : kpU (δ ^ 3) j ∈ Icc (√(1 - x ^ 2) - r) (√(1 - x ^ 2))) (hqq : kpU (δ ^ 3) j < √(1 - x ^ 2))
    (hg : 0 < kshG x (kpU (δ ^ 3) j)) (hCr : 0 ≤ Cr)
    (hrest : |Y j - κ * (kshG x (kpU (δ ^ 3) j) * airyAi (kshZ x (kpU (δ ^ 3) j) / δ ^ 2))| ≤ Cr * δ ^ 3 * |κ|)
    (hy32 : (-(kshZ x (kpU (δ ^ 3) j) / δ ^ 2)) ^ (-(3 / 2) : ℝ) ≤ Ye) :
    ∃ e : ℝ, Y j = κ * √(δ / π) * √(kpP (√(1 - x ^ 2)) (δ ^ 3) j) *
        Real.cos (2 / 3 * (-(kshZ x (kpU (δ ^ 3) j) / δ ^ 2)) ^ (3 / 2 : ℝ) - π / 4) + e ∧
      |e| ≤ 2 * (Cr * (δ ^ 2 * √δ) + Ye / 8) * (|κ * √(δ / π)| * √(kpP (√(1 - x ^ 2)) (δ ^ 3) j)) := by
  set q := kpU (δ ^ 3) j with hqdef
  set qs := √(1 - x ^ 2) with hqsdef
  have hq2 : qs ^ 2 = 1 - x ^ 2 := Real.sq_sqrt (by nlinarith)
  have hqs : 0 < qs := Real.sqrt_pos.2 (by nlinarith)
  have hqs1 : qs < 1 := by nlinarith
  have hq0 : 0 < q := by linarith [C.hrq, hq.1]
  have hzneg : kshZ x q < 0 := by
    have := (C.zeta_bounds hq).2
    nlinarith [C.hc1]
  have hy : 0 < -(kshZ x q / δ ^ 2) := by
    have : kshZ x q / δ ^ 2 < 0 := div_neg_of_neg_of_pos hzneg (by positivity)
    linarith
  set y := -(kshZ x q / δ ^ 2) with hydef
  have hα2 : 0 < qs ^ 2 - q ^ 2 := by nlinarith
  have hα : 0 < √(qs ^ 2 - q ^ 2) := Real.sqrt_pos.2 hα2
  have hα1 : √(qs ^ 2 - q ^ 2) ≤ 1 := by
    rw [Real.sqrt_le_one]; nlinarith
  have hP : kpP qs (δ ^ 3) j = 2 / √(qs ^ 2 - q ^ 2) := by
    unfold kpP kpα; rfl
  have hP0 : 2 ≤ kpP qs (δ ^ 3) j := by
    rw [hP, le_div_iff₀ hα]; linarith
  have hy4 : 0 < y ^ (-(1 / 4) : ℝ) := Real.rpow_pos_of_pos hy _
  have hy32' : 0 ≤ y ^ (-(3 / 2) : ℝ) := (Real.rpow_pos_of_pos hy _).le
  have hamp := C.amp_sq hx0 hx1 hδ hq hqq
  -- amplitude: (g y4)² = δ P
  have hM2 : (kshG x q * y ^ (-(1 / 4) : ℝ)) ^ 2 = δ * kpP qs (δ ^ 3) j := by
    rw [mul_pow, hamp, hP]; ring
  have hM : 2 * δ ≤ (kshG x q * y ^ (-(1 / 4) : ℝ)) ^ 2 := by
    rw [hM2]; nlinarith
  have hAi0 := airyAi_neg_asymptotic hy
  have hX : kshZ x q / δ ^ 2 = -y := by rw [hydef]; ring
  have hAi : |airyAi (kshZ x q / δ ^ 2) - 1 / √π * y ^ (-(1 / 4) : ℝ) * Real.cos (2 / 3 * y ^ (3 / 2 : ℝ) - π / 4)| ≤
      1 / 8 * (y ^ (-(1 / 4) : ℝ) * y ^ (-(3 / 2) : ℝ)) := by
    rw [hX]
    have e : y ^ (-(7 / 4) : ℝ) = y ^ (-(1 / 4) : ℝ) * y ^ (-(3 / 2) : ℝ) := by
      rw [← Real.rpow_add hy]; norm_num
    rw [← e]; exact hAi0
  have hmain := ksh_err_site (Y := Y j) (κ := κ) (g := kshG x q) (y4 := y ^ (-(1 / 4) : ℝ)) (y32 := y ^ (-(3 / 2) : ℝ))
    (Ai := airyAi (kshZ x q / δ ^ 2)) (c := Real.cos (2 / 3 * y ^ (3 / 2 : ℝ) - π / 4)) (δ := δ) (Cr := Cr) (Ye := Ye)
    hδ hg hy4 hy32' hy32 hCr hM hrest hAi
  -- rewrite the amplitude
  have hMs : kshG x q * y ^ (-(1 / 4) : ℝ) = √δ * √(kpP qs (δ ^ 3) j) := by
    rw [← Real.sqrt_mul hδ.le, ← hM2, Real.sqrt_sq (by positivity)]
  have hπ : 0 < √π := Real.sqrt_pos.2 Real.pi_pos
  have hsd : √(δ / π) = √δ / √π := Real.sqrt_div hδ.le _
  refine ⟨Y j - κ * √(δ / π) * √(kpP qs (δ ^ 3) j) * Real.cos (2 / 3 * y ^ (3 / 2 : ℝ) - π / 4), by ring, ?_⟩
  have e1 : κ * √(δ / π) * √(kpP qs (δ ^ 3) j) * Real.cos (2 / 3 * y ^ (3 / 2 : ℝ) - π / 4) =
      κ * (kshG x q * y ^ (-(1 / 4) : ℝ) * Real.cos (2 / 3 * y ^ (3 / 2 : ℝ) - π / 4) / √π) := by
    rw [hMs, hsd]; field_simp
  have e2 : |κ * √(δ / π)| * √(kpP qs (δ ^ 3) j) = |κ| * (kshG x q * y ^ (-(1 / 4) : ℝ)) / √π := by
    rw [hMs, hsd, abs_mul, abs_of_pos (by positivity : 0 < √δ / √π)]; field_simp
  rw [e1, e2]
  exact hmain

/-- `W = a² P_k P_{k-1} ≤ 3/(2A²)` on the band. -/
lemma ksh_W_le {a : ℤ → ℝ} {k : ℤ} {qs h A ηr : ℝ} (hA0 : 0 < A) (hAm : A ^ 2 ≤ qs ^ 2 - kpU h (k - 1) ^ 2)
    (hA0' : A ^ 2 ≤ qs ^ 2 - kpU h k ^ 2) (ha : a k ^ 2 = (1 + ηr) * ((1 - ((k : ℝ) * h) ^ 2) / 4)) (hηr2 : |ηr| ≤ 1 / 2) :
    a k ^ 2 * kpP qs h k * kpP qs h (k - 1) ≤ 3 / (2 * A ^ 2) := by
  have hPk : 0 < kpP qs h k := kpP_pos hA0 hA0'
  have hPk1 : 0 < kpP qs h (k - 1) := kpP_pos hA0 hAm
  have hPk2 : kpP qs h k ≤ 2 / A := kpP_le hA0 hA0'
  have hPk12 : kpP qs h (k - 1) ≤ 2 / A := kpP_le hA0 hAm
  have hm1 : (1 - ((k : ℝ) * h) ^ 2) / 4 ≤ 1 / 4 := by nlinarith [sq_nonneg ((k : ℝ) * h)]
  have h1 : 0 < 1 + ηr := by have := (abs_le.1 hηr2).1; linarith
  have hm0 : 0 ≤ (1 - ((k : ℝ) * h) ^ 2) / 4 := by
    have : 0 ≤ a k ^ 2 := sq_nonneg _
    rw [ha] at this
    exact nonneg_of_mul_nonneg_right this h1
  have ha2 : a k ^ 2 ≤ 3 / 8 := by
    rw [ha]
    have h2 : 1 + ηr ≤ 3 / 2 := by have := (abs_le.1 hηr2).2; linarith
    nlinarith [mul_le_mul h2 hm1 hm0 (by norm_num : (0 : ℝ) ≤ 3 / 2)]
  have h3 := mul_le_mul ha2 hPk2 hPk.le (by norm_num)
  have h4 := mul_le_mul h3 hPk12 hPk1.le (by positivity)
  calc a k ^ 2 * kpP qs h k * kpP qs h (k - 1) ≤ 3 / 8 * (2 / A) * (2 / A) := h4
    _ = 3 / (2 * A ^ 2) := by field_simp; ring

/-- The error factor: `W ≤ 3/(2A²)` gives `4Wρ + √(2W)(η + η) ≤ 6ρ/A² + 4η/A`. -/
lemma ksh_E_le {W A ρ η1 : ℝ} (hA0 : 0 < A) (hWle : W ≤ 3 / (2 * A ^ 2)) (hρ0 : 0 ≤ ρ) (hη10 : 0 ≤ η1) :
    4 * W * ρ + √(2 * W) * (η1 + η1) ≤ 6 * ρ / A ^ 2 + 4 * η1 / A := by
  have hsq : √(2 * W) ≤ 2 / A := by
    rw [Real.sqrt_le_left (by positivity)]
    have : 2 * W ≤ 3 / A ^ 2 := by
      rw [show 3 / A ^ 2 = 2 * (3 / (2 * A ^ 2)) by field_simp]; linarith
    calc 2 * W ≤ 3 / A ^ 2 := this
      _ ≤ (2 / A) ^ 2 := by rw [div_pow]; exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
  have b1 : 4 * W * ρ ≤ 6 * ρ / A ^ 2 := by
    have := mul_le_mul_of_nonneg_right hWle hρ0
    calc 4 * W * ρ = 4 * (W * ρ) := by ring
      _ ≤ 4 * (3 / (2 * A ^ 2) * ρ) := by linarith
      _ = 6 * ρ / A ^ 2 := by field_simp; ring
  have b2 : √(2 * W) * (η1 + η1) ≤ 4 * η1 / A := by
    calc √(2 * W) * (η1 + η1) ≤ 2 / A * (η1 + η1) := mul_le_mul_of_nonneg_right hsq (by linarith)
      _ = 4 * η1 / A := by ring
  linarith

/-- **The Ermakov amplitude at a bond equals `κ²δ/π`, to first order**: at the bond `(k, k-1)` of the band (`α ≥ A`, window of the chart,
`a_k² = (1 + η_r)(1 - (kδ³)²)/4`, the Airy matching `|Ŷ_j - κ g_j Ai(X_j)| ≤ C_r δ³ |κ|` and `y_j^{-3/2} ≤ Y_e`, `g_j > 0`):
`|√I_k(Ŷ) - |κ|√(δ/π)| ≤ |κ|√(δ/π) (6ρ/A² + 4η/A)`, `ρ = (3δ³/(A x²) + 2(δ³ + |η_r|)/x⁴)/x`, `η = 2(C_r δ²√δ + Y_e/8)`. -/
theorem ksh_bond_match {x r c1 c2 δ κ Cr Ye A ηr : ℝ} {Y a : ℤ → ℝ} {k : ℤ} (hx0 : 0 < x) (hx1 : x < 1)
    (C : KshChart x r c1 c2) (hδ : 0 < δ) (hk : 1 ≤ k) (hq1 : √(1 - x ^ 2) - r ≤ kpU (δ ^ 3) (k - 1))
    (hqk : kpU (δ ^ 3) k < √(1 - x ^ 2)) (hA0 : 0 < A) (hA1 : A ≤ 1)
    (hAm : A ^ 2 ≤ √(1 - x ^ 2) ^ 2 - kpU (δ ^ 3) (k - 1) ^ 2) (hA0' : A ^ 2 ≤ √(1 - x ^ 2) ^ 2 - kpU (δ ^ 3) k ^ 2)
    (hapos : 0 < a k) (ha : a k ^ 2 = (1 + ηr) * ((1 - ((k : ℝ) * δ ^ 3) ^ 2) / 4)) (hηr : |ηr| ≤ x ^ 2) (hηr2 : |ηr| ≤ 1 / 2)
    (hgk : 0 < kshG x (kpU (δ ^ 3) k)) (hgk1 : 0 < kshG x (kpU (δ ^ 3) (k - 1))) (hCr : 0 ≤ Cr)
    (hrk : |Y k - κ * (kshG x (kpU (δ ^ 3) k) * airyAi (kshZ x (kpU (δ ^ 3) k) / δ ^ 2))| ≤ Cr * δ ^ 3 * |κ|)
    (hrk1 : |Y (k - 1) - κ * (kshG x (kpU (δ ^ 3) (k - 1)) * airyAi (kshZ x (kpU (δ ^ 3) (k - 1)) / δ ^ 2))| ≤ Cr * δ ^ 3 * |κ|)
    (hyk : (-(kshZ x (kpU (δ ^ 3) k) / δ ^ 2)) ^ (-(3 / 2) : ℝ) ≤ Ye)
    (hyk1 : (-(kshZ x (kpU (δ ^ 3) (k - 1)) / δ ^ 2)) ^ (-(3 / 2) : ℝ) ≤ Ye) :
    abs (√(kermI a (kpP (√(1 - x ^ 2)) (δ ^ 3)) Y k) - |κ * √(δ / π)|) ≤
      |κ * √(δ / π)| * (6 * ((3 * δ ^ 3 / (A * x ^ 2) + 2 * (δ ^ 3 + |ηr|) / x ^ 4) / x) / A ^ 2 +
        4 * (2 * (Cr * (δ ^ 2 * √δ) + Ye / 8)) / A) := by
  set qs := √(1 - x ^ 2) with hqsdef
  have hq2 : qs ^ 2 = 1 - x ^ 2 := Real.sq_sqrt (by nlinarith)
  have hqs : 0 < qs := Real.sqrt_pos.2 (by nlinarith)
  have hh : 0 < δ ^ 3 := by positivity
  have hkk : kpU (δ ^ 3) k - δ ^ 3 = kpU (δ ^ 3) (k - 1) := kpU_pred _ k
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hq0 : 0 < kpU (δ ^ 3) (k - 1) := by
    have : (0 : ℝ) < ((k - 1 : ℤ) : ℝ) + 1 / 2 := by push_cast; linarith
    unfold kpU; exact mul_pos this hh
  have hwk : kpU (δ ^ 3) k ∈ Icc (qs - r) qs := ⟨by linarith [hkk, hh], hqk.le⟩
  have hwk1 : kpU (δ ^ 3) (k - 1) ∈ Icc (qs - r) qs := ⟨hq1, by linarith [hkk, hh]⟩
  set η1 : ℝ := 2 * (Cr * (δ ^ 2 * √δ) + Ye / 8) with hη1def
  have hYe0 : 0 ≤ Ye := le_trans (Real.rpow_pos_of_pos (by
    have hz := (C.zeta_bounds hwk).2
    have : kshZ x (kpU (δ ^ 3) k) < 0 := by nlinarith [C.hc1]
    have : kshZ x (kpU (δ ^ 3) k) / δ ^ 2 < 0 := div_neg_of_neg_of_pos this (by positivity)
    linarith) _).le hyk
  have hη10 : 0 ≤ η1 := by rw [hη1def]; positivity
  obtain ⟨ek, hek, hbk⟩ := ksh_site_eq (Y := Y) (j := k) (κ := κ) hx0 hx1 C hδ hwk hqk hgk hCr hrk hyk
  obtain ⟨ek1, hek1, hbk1⟩ := ksh_site_eq (Y := Y) (j := k - 1) (κ := κ) hx0 hx1 C hδ hwk1 (by linarith [hkk, hh]) hgk1 hCr hrk1 hyk1
  obtain ⟨η, hη, hcosd⟩ := C.phase hx0 hx1 hδ hq1 (by linarith [hkk]) hqk
  set θ := 2 / 3 * (-(kshZ x (kpU (δ ^ 3) k) / δ ^ 2)) ^ (3 / 2 : ℝ) - π / 4 with hθ
  set d := 2 / 3 * (-(kshZ x (kpU (δ ^ 3) (k - 1)) / δ ^ 2)) ^ (3 / 2 : ℝ) -
    2 / 3 * (-(kshZ x (kpU (δ ^ 3) k) / δ ^ 2)) ^ (3 / 2 : ℝ) with hd
  have hθ1 : 2 / 3 * (-(kshZ x (kpU (δ ^ 3) (k - 1)) / δ ^ 2)) ^ (3 / 2 : ℝ) - π / 4 = θ + d := by rw [hθ, hd]; ring
  rw [hθ1] at hek1
  have hcos := ksh_cos_id θ d
  rw [hcosd] at hcos
  -- the Ermakov data
  have hrad := kp_rad_ge (a := a) (x := x) (qs := qs) (h := δ ^ 3) (A := A) (η := ηr) hq2 hk hh hA0 hAm hA0' ha hηr
  have hPk : 0 < kpP qs (δ ^ 3) k := kpP_pos hA0 hA0'
  have hPk1 : 0 < kpP qs (δ ^ 3) (k - 1) := kpP_pos hA0 hAm
  have hρ := ksh_site_rho (a := a) (x := x) (qs := qs) (h := δ ^ 3) (A := A) (η := η) (ηr := ηr) (k := k) hx0 hq2 hqs hh hk hA0 hA1
    hAm hA0' ha hηr hηr2 (by rw [← kpU_pred]; linarith [hη.1, hkk]) (by linarith [hη.2])
  have hu : |x / √(1 - η ^ 2)| ≤ 1 := by rw [← hcosd]; exact Real.abs_cos_le_one _
  have hI := ksh_I_close (a := a) (P := kpP qs (δ ^ 3)) (Y := Y) (k := k) (t := κ * √(δ / π)) (u := x / √(1 - η ^ 2))
    (c1 := Real.cos θ) (c0 := Real.cos (θ + d)) (e1 := ek) (e0 := ek1) (η1 := η1) (η0 := η1)
    (ρ := (3 * δ ^ 3 / (A * x ^ 2) + 2 * (δ ^ 3 + |ηr|) / x ^ 4) / x) hapos hPk hPk1 hrad hek hek1 hcos
    (Real.abs_cos_le_one _) (Real.abs_cos_le_one _) hu hbk hbk1 hη10 hη10 hρ
  refine hI.trans ?_
  have hWle := ksh_W_le (a := a) (k := k) (qs := qs) (h := δ ^ 3) (A := A) (ηr := ηr) hA0 hAm hA0' ha hηr2
  have hρ0 : 0 ≤ (3 * δ ^ 3 / (A * x ^ 2) + 2 * (δ ^ 3 + |ηr|) / x ^ 4) / x := by positivity
  have t0 : 0 ≤ |κ * √(δ / π)| := abs_nonneg _
  apply mul_le_mul_of_nonneg_left _ t0
  exact ksh_E_le hA0 hWle hρ0 hη10

/-- info: 'FormalResearch.Special.ksh_site_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.ksh_site_eq

/-- info: 'FormalResearch.Special.ksh_bond_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.ksh_bond_match

end FormalResearch.Special
