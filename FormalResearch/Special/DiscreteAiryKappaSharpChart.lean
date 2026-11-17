module

public import FormalResearch.Special.DiscreteAiryKappaChart2
public import FormalResearch.Special.AiryAsymReal

/-!
# Sharp `κ`: the Langer chart of the Hahn chain with its amplitude identity (plan K1, sharp constant, step 3)

The chart `ζ = langerZeta u q_*`, `g = langerAmp u A q_*` of `u = x/√(1-q²)`, `A = ½√(1-q²)` (the Hahn data `P = 1, Q = 0`) satisfies on a window
`[q_* - r, q_* + r]` (`ksh_chart`): `ζ' ∈ [c₁, c₂]`, `ζ(q_*) = 0`, `g² A ζ' Sh(ζζ'²) = 1`, `Ch(ζζ'²) = u`.

* `ksh_g2`: **`g(q)² = 2 √(-ζ(q)) / α(q)`**, `α = √(q_*² - q²)`, for `q < q_*` in the window (from `Ch² - 1 = w Sh²`, `Ch = u`, `u² - 1 = -α²/(1-q²)`).
  Consequence: `g y^{-1/4} = √(δ P)` for `y = -ζ/δ²`, `P = 2/α`: the Airy amplitude is the Ermakov profile amplitude (`ksh_amp_sq`).
* `ksh_phase`: for `q₁ < q₀ < q_*` in the window with `q₀ - q₁ = δ³`, the Airy phases `ξ_j = (2/3)(-ζ(q_j)/δ²)^{3/2}` satisfy
  `cos(ξ₁ - ξ₀) = x/√(1 - η²)` for some `η ∈ (q₁, q₀)` (mean value theorem for `(2/3)(-ζ)^{3/2}`, whose derivative is `-√(-ζ) ζ'`,
  and `Ch(w) = cos√(-w)` for `w = ζζ'² ≤ 0`).

**Claim class: proved.**
-/

@[expose] public section

open Set Filter Topology FormalResearch.Racah.P3

namespace FormalResearch.Special

/-- `u = x/√(1-q²)` for the Hahn data. -/
lemma ksh_hrU (x q : ℝ) : hrU 1 0 1 x q = x / √(1 - q ^ 2) := by
  unfold hrU etilde
  simp

/-- `A = ½√(1-q²)` for the Hahn data. -/
lemma ksh_hrA (q : ℝ) : hrA1 1 0 q = 1 / 2 * √(1 - q ^ 2) := by
  unfold hrA1 etilde
  simp

/-- The Langer coordinate `ζ` of the Hahn data `(P, Q, τ) = (1, 0, 1)` at the turn `q_* = √(1 - x²)`. -/
noncomputable def kshZ (x : ℝ) : ℝ → ℝ := langerZeta (hrU 1 0 1 x) (√(1 - x ^ 2))

/-- The Langer amplitude `g` of the Hahn data. -/
noncomputable def kshG (x : ℝ) : ℝ → ℝ := langerAmp (hrU 1 0 1 x) (hrA1 1 0) (√(1 - x ^ 2))

/-- The window data of the Hahn chart: `ζ' ∈ [c₁, c₂]`, `ζ(q_*) = 0`, the amplitude relation and the eikonal relation on `[q_* - r, q_* + r]`. -/
structure KshChart (x r c1 c2 : ℝ) : Prop where
  hr : 0 < r
  hrq : r ≤ √(1 - x ^ 2) / 4
  hc1 : 0 < c1
  hc12 : c1 ≤ c2
  z0 : kshZ x (√(1 - x ^ 2)) = 0
  der : ∀ q ∈ Icc (√(1 - x ^ 2) - r) (√(1 - x ^ 2) + r),
    HasDerivAt (kshZ x) (deriv (kshZ x) q) q ∧ c1 ≤ deriv (kshZ x) q ∧ deriv (kshZ x) q ≤ c2
  rel : ∀ q ∈ Icc (√(1 - x ^ 2) - r) (√(1 - x ^ 2) + r),
    kshG x q ^ 2 * hrA1 1 0 q * deriv (kshZ x) q * (2 * deriv langerCosh (kshZ x q * deriv (kshZ x) q ^ 2)) = 1
  eik : ∀ q ∈ Icc (√(1 - x ^ 2) - r) (√(1 - x ^ 2) + r), langerCosh (kshZ x q * deriv (kshZ x) q ^ 2) = hrU 1 0 1 x q

/-- **The window data of the Hahn chart.** -/
theorem ksh_chart (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) : ∃ r c1 c2 : ℝ, KshChart x r c1 c2 := by
  have hq2 : √(1 - x ^ 2) ^ 2 = 1 - x ^ 2 := Real.sq_sqrt (by nlinarith)
  have hqs : 0 < √(1 - x ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have hint : 0 < (1 - 1 * √(1 - x ^ 2) ^ 2) * (1 - 0 * √(1 - x ^ 2) ^ 2) := by
    rw [hq2]; nlinarith
  have hturn : Phi 1 0 1 x (√(1 - x ^ 2) ^ 2) = 0 := by
    unfold Phi etilde
    rw [hq2]
    have : (1 - 1 * (1 - x ^ 2)) * (1 - 0 * (1 - x ^ 2)) = x ^ 2 := by ring
    rw [this, Real.sqrt_sq hx0.le]
    simp
  obtain ⟨r, c1, c2, gmin, gmax, Amin, Amax, LA, Lg, Lu, U, T, hrr0, hU, hsub, hζ, hAU, hgU, hrel, heik⟩ :=
    dal_turn_data (hrU_contDiffAt 1 x 3 hint) (hrU_turn hint hturn)
      (hrU_deriv_pos hqs (by linarith) (by rw [hq2]; nlinarith) (by simp) hturn) (hrA_contDiffAt 2 hint) (hrA_pos hint)
      (show 0 < √(1 - x ^ 2) / 4 by positivity)
  exact ⟨r, c1, c2, ⟨T.r_pos, hrr0, T.c1_pos, T.c1_le, T.zeta0, fun q hq => T.der q hq,
    fun q hq => hrel q (hsub hq), fun q hq => heik q (hsub hq)⟩⟩

/-- **Linear control of `ζ` near the turn**: from `c₁ ≤ ζ' ≤ c₂` on `[c-r, c+r]` and `ζ(c) = 0`, for `q ∈ [c-r, c]`:
`-c₂(c - q) ≤ ζ(q) ≤ -c₁(c - q)`. -/
lemma ksh_zeta_bounds {ζ : ℝ → ℝ} {c r c1 c2 : ℝ} (hz0 : ζ c = 0)
    (hder : ∀ q ∈ Icc (c - r) (c + r), HasDerivAt ζ (deriv ζ q) q ∧ c1 ≤ deriv ζ q ∧ deriv ζ q ≤ c2)
    (hr : 0 < r) {q : ℝ} (hq : q ∈ Icc (c - r) c) :
    -c2 * (c - q) ≤ ζ q ∧ ζ q ≤ -c1 * (c - q) := by
  have hD : Convex ℝ (Icc (c - r) (c + r)) := convex_Icc _ _
  have hint : interior (Icc (c - r) (c + r)) = Ioo (c - r) (c + r) := interior_Icc
  have hcont : ContinuousOn ζ (Icc (c - r) (c + r)) := fun y hy => (hder y hy).1.continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ ζ (interior (Icc (c - r) (c + r))) := by
    rw [hint]
    exact fun y hy => (hder y (Ioo_subset_Icc_self hy)).1.differentiableAt.differentiableWithinAt
  have hqD : q ∈ Icc (c - r) (c + r) := ⟨hq.1, by linarith [hq.2]⟩
  have hcD : c ∈ Icc (c - r) (c + r) := ⟨by linarith, by linarith⟩
  have h1 := Convex.mul_sub_le_image_sub_of_le_deriv hD hcont hdiff (C := c1)
    (fun y hy => by rw [hint] at hy; exact (hder y (Ioo_subset_Icc_self hy)).2.1) q hqD c hcD hq.2
  have h2 := Convex.image_sub_le_mul_sub_of_deriv_le hD hcont hdiff (C := c2)
    (fun y hy => by rw [hint] at hy; exact (hder y (Ioo_subset_Icc_self hy)).2.2) q hqD c hcD hq.2
  rw [hz0] at h1 h2
  constructor <;> nlinarith

/-- Algebra of the amplitude identity: `g² A ζ' Sh = 1`, `A = s/2`, `u = x/s`, `u² - 1 = z d² Sh²` (`z = ζ`, `d = ζ'`), `α² = s² - x²`,
`z < 0` give `g² = 2√(-z)/α`. -/
lemma ksh_g2_alg {g A d Sh z x α s : ℝ} (hs : 0 < s) (hA : A = s / 2) (hrel : g ^ 2 * A * d * Sh = 1)
    (hid : (x / s) ^ 2 - 1 = z * d ^ 2 * Sh ^ 2) (hα : 0 < α) (hα2 : α ^ 2 = s ^ 2 - x ^ 2) (hz : z < 0) :
    g ^ 2 = 2 * √(-z) / α := by
  have h1 : g ^ 2 * (d * Sh) * s = 2 := by rw [hA] at hrel; linarith
  have h2 : (d * Sh) ^ 2 * (z * s ^ 2) = -α ^ 2 := by
    have : (x / s) ^ 2 - 1 = (x ^ 2 - s ^ 2) / s ^ 2 := by field_simp
    rw [this] at hid
    have h3 : x ^ 2 - s ^ 2 = z * d ^ 2 * Sh ^ 2 * s ^ 2 := by
      have := hid; field_simp at this; linarith
    nlinarith [h3, hα2]
  have h4 : (g ^ 2) ^ 2 = 4 * (-z) / α ^ 2 := by
    have : (g ^ 2 * (d * Sh) * s) ^ 2 = 4 := by rw [h1]; norm_num
    have hα0 : α ^ 2 ≠ 0 := by positivity
    have key : (g ^ 2) ^ 2 * α ^ 2 = 4 * (-z) := by
      calc (g ^ 2) ^ 2 * α ^ 2 = -(g ^ 4 * ((d * Sh) ^ 2 * (z * s ^ 2))) := by rw [h2]; ring
        _ = -z * (g ^ 2 * (d * Sh) * s) ^ 2 := by ring
        _ = 4 * (-z) := by rw [this]; ring
    rw [eq_div_iff hα0]; exact key
  have h5 : (2 * √(-z) / α) ^ 2 = 4 * (-z) / α ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by linarith)]; norm_num
  have h6 : g ^ 2 = 2 * √(-z) / α := by
    have := (sq_eq_sq₀ (sq_nonneg g) (by positivity : (0 : ℝ) ≤ 2 * √(-z) / α)).1 (h4.trans h5.symm)
    exact this
  exact h6

/-- On `[q_* - r, q_*)`: `-c₂(q_* - q) ≤ ζ ≤ -c₁(q_* - q) < 0`. -/
lemma KshChart.zeta_bounds {x r c1 c2 : ℝ} (C : KshChart x r c1 c2) {q : ℝ} (hq : q ∈ Icc (√(1 - x ^ 2) - r) (√(1 - x ^ 2))) :
    -c2 * (√(1 - x ^ 2) - q) ≤ kshZ x q ∧ kshZ x q ≤ -c1 * (√(1 - x ^ 2) - q) :=
  ksh_zeta_bounds C.z0 C.der C.hr hq

/-- **The amplitude identity of the Hahn chart**: `g(q)² = 2√(-ζ(q))/α(q)`, `α = √(q_*² - q²)`, for `q ∈ [q_* - r, q_*)`. -/
theorem KshChart.g2 {x r c1 c2 : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (C : KshChart x r c1 c2) {q : ℝ}
    (hq : q ∈ Icc (√(1 - x ^ 2) - r) (√(1 - x ^ 2))) (hqq : q < √(1 - x ^ 2)) :
    kshG x q ^ 2 = 2 * √(-kshZ x q) / √(√(1 - x ^ 2) ^ 2 - q ^ 2) := by
  have hq2 : √(1 - x ^ 2) ^ 2 = 1 - x ^ 2 := Real.sq_sqrt (by nlinarith)
  have hqs : 0 < √(1 - x ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have hqs1 : √(1 - x ^ 2) < 1 := by nlinarith
  have hqwin : q ∈ Icc (√(1 - x ^ 2) - r) (√(1 - x ^ 2) + r) := ⟨hq.1, by linarith [C.hr]⟩
  have hq0 : 0 < q := by linarith [C.hrq, hq.1]
  have hq1 : q ^ 2 < 1 := by nlinarith
  have hs : 0 < √(1 - q ^ 2) := Real.sqrt_pos.2 (by linarith)
  have hss : √(1 - q ^ 2) ^ 2 = 1 - q ^ 2 := Real.sq_sqrt (by linarith)
  have hzneg : kshZ x q < 0 := by
    have := (C.zeta_bounds hq).2
    nlinarith [C.hc1]
  have hα2 : 0 < √(1 - x ^ 2) ^ 2 - q ^ 2 := by nlinarith
  have hα : 0 < √(√(1 - x ^ 2) ^ 2 - q ^ 2) := Real.sqrt_pos.2 hα2
  have hαs : √(√(1 - x ^ 2) ^ 2 - q ^ 2) ^ 2 = √(1 - q ^ 2) ^ 2 - x ^ 2 := by
    rw [Real.sq_sqrt hα2.le, hss, hq2]; ring
  have hrel := C.rel q hqwin
  have heik := C.eik q hqwin
  rw [ksh_hrA] at hrel
  have hid := langerCosh_sq_sub_one (kshZ x q * deriv (kshZ x) q ^ 2)
  rw [heik, ksh_hrU] at hid
  have hSh : langerSinhc (kshZ x q * deriv (kshZ x) q ^ 2) = 2 * deriv langerCosh (kshZ x q * deriv (kshZ x) q ^ 2) := by
    unfold langerSinhc; rfl
  rw [hSh] at hid
  exact ksh_g2_alg (g := kshG x q) (A := 1 / 2 * √(1 - q ^ 2)) (d := deriv (kshZ x) q)
    (Sh := 2 * deriv langerCosh (kshZ x q * deriv (kshZ x) q ^ 2))
    hs (by ring) hrel hid hα hαs hzneg

/-- `(2/3) y^{3/2}` for `y = -ζ/δ²` is `(2/3)(-ζ)^{3/2}/δ³`. -/
lemma ksh_xi_eq {z δ : ℝ} (hδ : 0 < δ) (hz : z ≤ 0) :
    2 / 3 * (-(z / δ ^ 2)) ^ (3 / 2 : ℝ) = 2 / 3 * (-z) ^ (3 / 2 : ℝ) / δ ^ 3 := by
  have h1 : -(z / δ ^ 2) = (-z) / δ ^ 2 := by ring
  rw [h1, Real.div_rpow (by linarith) (by positivity)]
  have h2 : (δ ^ 2) ^ (3 / 2 : ℝ) = δ ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
    norm_num
  rw [h2]; ring

/-- **The Airy phase difference of the Hahn chart**: for `q₀ = q₁ + δ³ < q_*` in the window there is `η ∈ (q₁, q₀)` with
`cos(ξ(q₁) - ξ(q₀)) = x/√(1 - η²)`, `ξ(q) = (2/3)(-ζ(q)/δ²)^{3/2}`. -/
theorem KshChart.phase {x r c1 c2 δ : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (C : KshChart x r c1 c2) (hδ : 0 < δ) {q1 q0 : ℝ}
    (hq1 : √(1 - x ^ 2) - r ≤ q1) (h10 : q1 + δ ^ 3 = q0) (hq0 : q0 < √(1 - x ^ 2)) :
    ∃ η ∈ Ioo q1 q0, Real.cos (2 / 3 * (-(kshZ x q1 / δ ^ 2)) ^ (3 / 2 : ℝ) - 2 / 3 * (-(kshZ x q0 / δ ^ 2)) ^ (3 / 2 : ℝ)) =
      x / √(1 - η ^ 2) := by
  have hqs : 0 < √(1 - x ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have hd3 : 0 < δ ^ 3 := by positivity
  have hq10 : q1 < q0 := by linarith
  have hwin : ∀ q ∈ Icc q1 q0, q ∈ Icc (√(1 - x ^ 2) - r) (√(1 - x ^ 2) + r) := fun q hq => ⟨by linarith [hq.1], by linarith [hq.2, C.hr]⟩
  have hneg : ∀ q ∈ Icc q1 q0, kshZ x q < 0 := fun q hq => by
    have hqq : q ∈ Icc (√(1 - x ^ 2) - r) (√(1 - x ^ 2)) := ⟨by linarith [hq.1], by linarith [hq.2]⟩
    have := (C.zeta_bounds hqq).2
    have : 0 < √(1 - x ^ 2) - q := by
      rcases hq.2.lt_or_eq with h | h
      · linarith
      · linarith
    nlinarith [C.hc1]
  -- the primitive Ψ
  set Ψ : ℝ → ℝ := fun q => 2 / 3 * (-kshZ x q) ^ (3 / 2 : ℝ) with hΨ
  have hΨd : ∀ q ∈ Ioo q1 q0, HasDerivAt Ψ (-(√(-kshZ x q) * deriv (kshZ x) q)) q := by
    intro q hq
    have hqI : q ∈ Icc q1 q0 := Ioo_subset_Icc_self hq
    have hd := (C.der q (hwin q hqI)).1
    have hne : (-kshZ x q) ≠ 0 := by have := hneg q hqI; linarith
    have h1 := (hd.neg).rpow_const (p := (3 / 2 : ℝ)) (Or.inl hne)
    have h2 := h1.const_mul (2 / 3)
    convert h2 using 1
    have hpos : 0 < -kshZ x q := by have := hneg q hqI; linarith
    have : (-kshZ x q) ^ ((3 / 2 : ℝ) - 1) = √(-kshZ x q) := by
      rw [Real.sqrt_eq_rpow]; norm_num
    simp only [Pi.neg_apply]
    rw [this]; ring
  have hΨc : ContinuousOn Ψ (Icc q1 q0) := by
    intro q hq
    have hd := (C.der q (hwin q hq)).1
    have hne : (-kshZ x q) ≠ 0 := by have := hneg q hq; linarith
    exact (((hd.neg).rpow_const (p := (3 / 2 : ℝ)) (Or.inl hne)).const_mul (2 / 3)).continuousAt.continuousWithinAt
  obtain ⟨η, hη, hηeq⟩ := exists_hasDerivAt_eq_slope Ψ (fun q => -(√(-kshZ x q) * deriv (kshZ x) q)) hq10 hΨc hΨd
  have hηI : η ∈ Icc q1 q0 := Ioo_subset_Icc_self hη
  refine ⟨η, hη, ?_⟩
  -- the phase difference equals √(-ζ(η)) ζ'(η)
  set t := √(-kshZ x η) * deriv (kshZ x) η with ht
  have hdη := C.der η (hwin η hηI)
  have hzη := hneg η hηI
  have ht0 : 0 ≤ t := mul_nonneg (Real.sqrt_nonneg _) (by linarith [hdη.2.1, C.hc1])
  have hkey : Ψ q1 - Ψ q0 = t * δ ^ 3 := by
    have h3 : -t = (Ψ q0 - Ψ q1) / (q0 - q1) := hηeq
    have h4 : q0 - q1 = δ ^ 3 := by linarith
    rw [h4] at h3
    field_simp at h3
    linarith
  have hxi : 2 / 3 * (-(kshZ x q1 / δ ^ 2)) ^ (3 / 2 : ℝ) - 2 / 3 * (-(kshZ x q0 / δ ^ 2)) ^ (3 / 2 : ℝ) = t := by
    rw [ksh_xi_eq hδ (hneg q1 ⟨le_rfl, hq10.le⟩).le, ksh_xi_eq hδ (hneg q0 ⟨hq10.le, le_rfl⟩).le]
    have : 2 / 3 * (-kshZ x q1) ^ (3 / 2 : ℝ) / δ ^ 3 - 2 / 3 * (-kshZ x q0) ^ (3 / 2 : ℝ) / δ ^ 3 = (Ψ q1 - Ψ q0) / δ ^ 3 := by
      simp only [hΨ]; ring
    rw [this, hkey]; field_simp
  rw [hxi]
  -- cos t = Ch(w) = u(η)
  have hw : kshZ x η * deriv (kshZ x) η ^ 2 ≤ 0 := by
    have : 0 ≤ deriv (kshZ x) η ^ 2 := sq_nonneg _
    nlinarith
  have hsq : √(-(kshZ x η * deriv (kshZ x) η ^ 2)) = t := by
    have : -(kshZ x η * deriv (kshZ x) η ^ 2) = t ^ 2 := by
      rw [ht, mul_pow, Real.sq_sqrt (by linarith)]; ring
    rw [this, Real.sqrt_sq ht0]
  have := C.eik η (hwin η hηI)
  rw [langerCosh_nonpos hw, hsq, ksh_hrU] at this
  exact this

/-- **The Airy amplitude is the Ermakov amplitude**: with `y = -ζ(q)/δ²`, `g(q)² (y^{-1/4})² = 2δ/α(q)` (`= δ P`, `P = 2/α`). -/
theorem KshChart.amp_sq {x r c1 c2 δ : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (C : KshChart x r c1 c2) (hδ : 0 < δ) {q : ℝ}
    (hq : q ∈ Icc (√(1 - x ^ 2) - r) (√(1 - x ^ 2))) (hqq : q < √(1 - x ^ 2)) :
    kshG x q ^ 2 * ((-(kshZ x q / δ ^ 2)) ^ (-(1 / 4) : ℝ)) ^ 2 = 2 * δ / √(√(1 - x ^ 2) ^ 2 - q ^ 2) := by
  have hq2 : √(1 - x ^ 2) ^ 2 = 1 - x ^ 2 := Real.sq_sqrt (by nlinarith)
  have hqs : 0 < √(1 - x ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have hqs1 : √(1 - x ^ 2) < 1 := by nlinarith
  have hq0 : 0 < q := by linarith [C.hrq, hq.1]
  have hzneg : kshZ x q < 0 := by
    have := (C.zeta_bounds hq).2
    nlinarith [C.hc1]
  have hα2 : 0 < √(1 - x ^ 2) ^ 2 - q ^ 2 := by nlinarith
  have hα : 0 < √(√(1 - x ^ 2) ^ 2 - q ^ 2) := Real.sqrt_pos.2 hα2
  have hy : 0 < -(kshZ x q / δ ^ 2) := by
    have : kshZ x q / δ ^ 2 < 0 := div_neg_of_neg_of_pos hzneg (by positivity)
    linarith
  have h1 : ((-(kshZ x q / δ ^ 2)) ^ (-(1 / 4) : ℝ)) ^ 2 = 1 / √(-(kshZ x q / δ ^ 2)) := by
    have e : 1 / (-(kshZ x q / δ ^ 2)) ^ (1 / 2 : ℝ) = (-(kshZ x q / δ ^ 2)) ^ (-(1 / 2) : ℝ) := by
      rw [Real.rpow_neg hy.le, one_div]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy.le, Real.sqrt_eq_rpow, e]
    norm_num
  have h2 : √(-(kshZ x q / δ ^ 2)) = √(-kshZ x q) / δ := by
    have : -(kshZ x q / δ ^ 2) = (-kshZ x q) / δ ^ 2 := by ring
    rw [this, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hδ.le]
  have hsz : 0 < √(-kshZ x q) := Real.sqrt_pos.2 (by linarith)
  rw [h1, h2, C.g2 hx0 hx1 hq hqq]
  field_simp

/-- info: 'FormalResearch.Special.ksh_chart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.ksh_chart

/-- info: 'FormalResearch.Special.KshChart.g2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.KshChart.g2

/-- info: 'FormalResearch.Special.KshChart.phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.KshChart.phase

/-- info: 'FormalResearch.Special.KshChart.amp_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.KshChart.amp_sq

end FormalResearch.Special
