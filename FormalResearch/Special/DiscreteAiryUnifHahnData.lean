module

public import FormalResearch.Special.DiscreteAiryUnifTheorem
public import FormalResearch.Special.DiscreteAiryPhysHahn

/-!
# Uniform discrete-to-Airy for Hahn: the datum class is uniform over `x ∈ [x₀, x₁]`

For the closed-form Hahn data `A = hrA1 1 0 = ½ √(1-q²)`, `u = hrU 1 0 τ x = τ x / √(1-q²)` (`τ² = 1`) with
`y = τ x ∈ [x₀, x₁] ⊂ (0, 1)` and `c = √(1-x²)`, the datum class `DunDatum` of `DiscreteAiryUnifMain` holds on `ball c ρ`
with constants `(ρ, Ku, m, a₋, a₊, KA)` depending only on `(x₀, x₁)`.

The derivative bounds are those of the two fixed functions `q ↦ (√(1-q²))⁻¹`, `q ↦ √(1-q²)` on the compact `[0, (1+c_max)/2] ⊂ (-1, 1)`,
`u = y · (√(1-q²))⁻¹` carrying the factor `|y| ≤ 1`: no compactness in the parameter `x` is used (only in the variable `q`).

**Claim class: proved.**
-/

@[expose] public section

open Set Metric FormalResearch.Racah.P3 FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- `q ↦ √(1-q²)`. -/
noncomputable def hdS (q : ℝ) : ℝ := Real.sqrt (1 - q ^ 2)

/-- `q ↦ (√(1-q²))⁻¹`. -/
noncomputable def hdR (q : ℝ) : ℝ := (Real.sqrt (1 - q ^ 2))⁻¹

lemma hrU_one_zero (τ x : ℝ) : hrU 1 0 τ x = fun q => (τ * x) * hdR q := by
  funext q
  simp [hrU, etilde, hdR, div_eq_mul_inv]

lemma hrA1_one_zero : hrA1 1 0 = fun q => (1 / 2 : ℝ) * hdS q := by
  funext q
  simp [hrA1, etilde, hdS]

lemma hdS_cd : ContDiffOn ℝ 3 hdS (Ioo (-1) 1) := by
  unfold hdS
  refine ContDiffOn.sqrt (by fun_prop) (fun q hq => ?_)
  have h1 := hq.1
  have h2 := hq.2
  exact (by nlinarith : (0 : ℝ) < 1 - q ^ 2).ne'

lemma hdR_cd : ContDiffOn ℝ 3 hdR (Ioo (-1) 1) := by
  unfold hdR
  refine ContDiffOn.inv (hdS_cd) (fun q hq => ?_)
  have h1 := hq.1
  have h2 := hq.2
  exact (Real.sqrt_pos.2 (by nlinarith : (0 : ℝ) < 1 - q ^ 2)).ne'

/-- Bounds of the first three derivatives of a fixed `C³` function on a compact subset of an open set. -/
lemma dun_fam_bound {f : ℝ → ℝ} {U S : Set ℝ} (hU : IsOpen U) (hf : ContDiffOn ℝ 3 f U) (hS : IsCompact S)
    (hSU : S ⊆ U) : ∃ K : ℝ, 0 ≤ K ∧ ∀ q ∈ S,
      |deriv f q| ≤ K ∧ |deriv (deriv f) q| ≤ K ∧ |deriv (deriv (deriv f)) q| ≤ K := by
  have h1 : ContDiffOn ℝ 2 (deriv f) U := hf.deriv_of_isOpen hU (by norm_num)
  have h2 : ContDiffOn ℝ 1 (deriv (deriv f)) U := h1.deriv_of_isOpen hU (by norm_num)
  have h3 : ContDiffOn ℝ 0 (deriv (deriv (deriv f))) U := h2.deriv_of_isOpen hU (by norm_num)
  obtain ⟨K1, hK1⟩ := hS.exists_bound_of_continuousOn (h1.continuousOn.mono hSU)
  obtain ⟨K2, hK2⟩ := hS.exists_bound_of_continuousOn (h2.continuousOn.mono hSU)
  obtain ⟨K3, hK3⟩ := hS.exists_bound_of_continuousOn (h3.continuousOn.mono hSU)
  refine ⟨max 0 (max K1 (max K2 K3)), le_max_left _ _, fun q hq => ?_⟩
  have a1 := hK1 q hq
  have a2 := hK2 q hq
  have a3 := hK3 q hq
  rw [Real.norm_eq_abs] at a1 a2 a3
  refine ⟨a1.trans ?_, a2.trans ?_, a3.trans ?_⟩
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  · exact (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))

/-- The first three derivatives of `y · f` on an open set where `f` is `C³`. -/
lemma dun_mul_derivs {f : ℝ → ℝ} {B : Set ℝ} (hB : IsOpen B) (hf : ContDiffOn ℝ 3 f B) (y : ℝ) :
    ∀ z ∈ B, deriv (fun q => y * f q) z = y * deriv f z ∧
      deriv (deriv (fun q => y * f q)) z = y * deriv (deriv f) z ∧
      deriv (deriv (deriv (fun q => y * f q))) z = y * deriv (deriv (deriv f)) z := by
  have hd0 : ∀ z ∈ B, DifferentiableAt ℝ f z := fun z hz =>
    (hf.differentiableOn (by norm_num)).differentiableAt (hB.mem_nhds hz)
  have h1 : ContDiffOn ℝ 2 (deriv f) B := hf.deriv_of_isOpen hB (by norm_num)
  have hd1 : ∀ z ∈ B, DifferentiableAt ℝ (deriv f) z := fun z hz =>
    (h1.differentiableOn (by norm_num)).differentiableAt (hB.mem_nhds hz)
  have h2 : ContDiffOn ℝ 1 (deriv (deriv f)) B := h1.deriv_of_isOpen hB (by norm_num)
  have hd2 : ∀ z ∈ B, DifferentiableAt ℝ (deriv (deriv f)) z := fun z hz =>
    (h2.differentiableOn (by norm_num)).differentiableAt (hB.mem_nhds hz)
  have e1 : ∀ z ∈ B, deriv (fun q => y * f q) z = y * deriv f z := fun z hz => deriv_const_mul y (hd0 z hz)
  have e1' : ∀ z ∈ B, deriv (fun q => y * f q) =ᶠ[nhds z] fun q => y * deriv f q := fun z hz =>
    Filter.eventually_of_mem (hB.mem_nhds hz) (fun w hw => e1 w hw)
  have e2 : ∀ z ∈ B, deriv (deriv (fun q => y * f q)) z = y * deriv (deriv f) z := fun z hz => by
    rw [(e1' z hz).deriv_eq]; exact deriv_const_mul y (hd1 z hz)
  have e2' : ∀ z ∈ B, deriv (deriv (fun q => y * f q)) =ᶠ[nhds z] fun q => y * deriv (deriv f) q :=
    fun z hz => Filter.eventually_of_mem (hB.mem_nhds hz) (fun w hw => e2 w hw)
  intro z hz
  refine ⟨e1 z hz, e2 z hz, ?_⟩
  rw [(e2' z hz).deriv_eq]; exact deriv_const_mul y (hd2 z hz)

/-- The datum `(y · hdR, ½ hdS)` at `c` with `c² = 1 - y²` on a ball inside `[0, q_hi]`, from fixed-function derivative bounds. -/
lemma hahn_datum_core {y c ρ qhi K1 K2 m : ℝ} (hyp : 0 < y) (hyl : y < 1) (hc2 : c ^ 2 = 1 - y ^ 2) (hcp : 0 < c)
    (hmc : m ≤ c) (hK2n : 0 ≤ K2) (hρp : 0 < ρ) (hqhi : qhi < 1) (hballS : ball c ρ ⊆ Icc (0 : ℝ) qhi)
    (hK1 : ∀ q ∈ Icc (0 : ℝ) qhi, |deriv hdR q| ≤ K1 ∧ |deriv (deriv hdR) q| ≤ K1 ∧
      |deriv (deriv (deriv hdR)) q| ≤ K1)
    (hK2 : ∀ q ∈ Icc (0 : ℝ) qhi, |deriv hdS q| ≤ K2 ∧ |deriv (deriv hdS) q| ≤ K2 ∧
      |deriv (deriv (deriv hdS)) q| ≤ K2) :
    DunDatum (fun q => y * hdR q) (fun q => (1 / 2 : ℝ) * hdS q) c ρ (K1 + 1) m (Real.sqrt (1 - qhi ^ 2) / 2) (1 / 2) K2 := by
  have hSU : Icc (0 : ℝ) qhi ⊆ Ioo (-1) 1 := fun q hq => ⟨by linarith [hq.1], lt_of_le_of_lt hq.2 hqhi⟩
  have hballU : ball c ρ ⊆ Ioo (-1 : ℝ) 1 := hballS.trans hSU
  have hDR := dun_mul_derivs (isOpen_ball (x := c) (ε := ρ)) (hdR_cd.mono hballU) y
  have hDS := dun_mul_derivs (isOpen_ball (x := c) (ε := ρ)) (hdS_cd.mono hballU) (1 / 2 : ℝ)
  have hs : Real.sqrt (1 - c ^ 2) = y := by
    rw [hc2, sub_sub_cancel, Real.sqrt_sq hyp.le]
  have hyabs : |y| ≤ 1 := by rw [abs_of_pos hyp]; exact hyl.le
  refine
    { u3 := contDiffOn_const.mul (hdR_cd.mono hballU)
      u0 := ?_
      um := ?_
      ub := fun z hz => ?_
      A2 := (contDiffOn_const.mul (hdS_cd.mono hballU)).of_le (by norm_num)
      Ab := fun z hz => ?_
      Aj := fun z hz => ?_ }
  · simp only [hdR, hs]
    field_simp
  · have hder : HasDerivAt hdR (c / y / y ^ 2) c := by
      have h1 : HasDerivAt (fun q : ℝ => 1 - q ^ 2) (-(2 * c)) c := by
        simpa using ((hasDerivAt_pow 2 c).const_sub 1)
      have h2 := h1.sqrt (by rw [hc2]; nlinarith only [hyp, hyl] : (1 - c ^ 2) ≠ 0)
      have h3 := h2.inv (by rw [hs]; exact hyp.ne' : Real.sqrt (1 - c ^ 2) ≠ 0)
      have : hdR = fun q => (Real.sqrt (1 - q ^ 2))⁻¹ := rfl
      rw [this]
      convert h3 using 1
      rw [hs]; field_simp
    have hdc : deriv (fun q => y * hdR q) c = c / y ^ 2 := by
      rw [(dun_mul_derivs isOpen_ball (hdR_cd.mono hballU) y c (mem_ball_self hρp)).1, hder.deriv]
      field_simp
    rw [hdc, le_div_iff₀ (by positivity)]
    nlinarith only [mul_pos hcp hyp, sq_nonneg y, hyl, hyp, hmc, hcp]
  · obtain ⟨e1, e2, e3⟩ := hDR z hz
    obtain ⟨b1, b2, b3⟩ := hK1 z (hballS hz)
    rw [e1, e2, e3, abs_mul, abs_mul, abs_mul]
    have hn : 0 ≤ |y| := abs_nonneg _
    refine ⟨?_, ?_, ?_⟩
    · nlinarith only [abs_nonneg (deriv hdR z), hn, hyabs, b1]
    · nlinarith only [abs_nonneg (deriv (deriv hdR) z), hn, hyabs, b2]
    · nlinarith only [abs_nonneg (deriv (deriv (deriv hdR)) z), hn, hyabs, b3]
  · have hzS := hballS hz
    have hq2 : z ^ 2 ≤ qhi ^ 2 := by nlinarith only [hzS.1, hzS.2]
    have hlo : Real.sqrt (1 - qhi ^ 2) ≤ hdS z := Real.sqrt_le_sqrt (by linarith)
    have hhi : hdS z ≤ 1 := Real.sqrt_le_one.2 (by nlinarith only [sq_nonneg z])
    show Real.sqrt (1 - qhi ^ 2) / 2 ≤ (1 / 2 : ℝ) * hdS z ∧ (1 / 2 : ℝ) * hdS z ≤ 1 / 2
    constructor <;> linarith
  · obtain ⟨e1, e2, e3⟩ := hDS z hz
    obtain ⟨b1, b2, b3⟩ := hK2 z (hballS hz)
    rw [e1, e2]
    rw [abs_mul, abs_mul]
    simp only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    constructor <;> linarith

/-- **The Hahn datum class is uniform over the shape `y = τ x ∈ [x₀, x₁] ⊂ (0,1)`.** -/
lemma hahn_datum_unif {x0 x1 : ℝ} (hx0 : 0 < x0) (hx01 : x0 ≤ x1) (hx1 : x1 < 1) :
    ∃ ρ Ku m aLo aHi KA : ℝ, 0 < ρ ∧ 0 < Ku ∧ 0 < m ∧ 0 < aLo ∧ aLo ≤ aHi ∧ 0 ≤ KA ∧
      ∀ τ x : ℝ, τ ^ 2 = 1 → τ * x ∈ Icc x0 x1 →
        ρ ≤ Real.sqrt (1 - x ^ 2) / 4 ∧
        (∀ q ∈ Icc (Real.sqrt (1 - x ^ 2) - ρ) (Real.sqrt (1 - x ^ 2) + ρ),
          0 < 1 - 1 * q ^ 2 ∧ 0 < 1 - 0 * q ^ 2) ∧
        DunDatum (hrU 1 0 τ x) (hrA1 1 0) (Real.sqrt (1 - x ^ 2)) ρ Ku m aLo aHi KA := by
  have hx0' : x0 ^ 2 < 1 := by nlinarith
  have hx1' : x1 ^ 2 < 1 := by nlinarith
  obtain ⟨cmin, hcmin⟩ : ∃ cmin, cmin = Real.sqrt (1 - x1 ^ 2) := ⟨_, rfl⟩
  obtain ⟨cmax, hcmax⟩ : ∃ cmax, cmax = Real.sqrt (1 - x0 ^ 2) := ⟨_, rfl⟩
  have hcminp : 0 < cmin := by rw [hcmin]; exact Real.sqrt_pos.2 (by linarith)
  have hcmaxlt : cmax < 1 := by
    rw [hcmax]
    exact (Real.sqrt_lt' one_pos).2 (by nlinarith only [hx0, hx0'])
  obtain ⟨qhi, hqhi⟩ : ∃ qhi, qhi = (1 + cmax) / 2 := ⟨_, rfl⟩
  have hcmaxp : 0 < cmax := by rw [hcmax]; exact Real.sqrt_pos.2 (by linarith)
  have hqhi1 : qhi < 1 := by rw [hqhi]; linarith
  have hqhi0 : 0 < qhi := by rw [hqhi]; linarith
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = min (cmin / 4) ((1 - cmax) / 2) := ⟨_, rfl⟩
  have hρp : 0 < ρ := by rw [hρ]; exact lt_min (by positivity) (by linarith)
  have hρ1 : ρ ≤ cmin / 4 := by rw [hρ]; exact min_le_left _ _
  have hρ2 : ρ ≤ (1 - cmax) / 2 := by rw [hρ]; exact min_le_right _ _
  have hSc : IsCompact (Icc (0 : ℝ) qhi) := isCompact_Icc
  have hSU : Icc (0 : ℝ) qhi ⊆ Ioo (-1) 1 := fun q hq => ⟨by linarith [hq.1], lt_of_le_of_lt hq.2 hqhi1⟩
  obtain ⟨K1, hK1n, hK1⟩ := dun_fam_bound isOpen_Ioo hdR_cd hSc hSU
  obtain ⟨K2, hK2n, hK2⟩ := dun_fam_bound isOpen_Ioo hdS_cd hSc hSU
  have hs0p : 0 < Real.sqrt (1 - qhi ^ 2) := Real.sqrt_pos.2 (by nlinarith only [hqhi0, hqhi1])
  have hs01 : Real.sqrt (1 - qhi ^ 2) ≤ 1 := Real.sqrt_le_one.2 (by nlinarith only [sq_nonneg qhi])
  refine ⟨ρ, K1 + 1, cmin, Real.sqrt (1 - qhi ^ 2) / 2, 1 / 2, K2, hρp, by linarith, hcminp, by positivity,
    by linarith, hK2n, ?_⟩
  intro τ x hτ hy
  have hx2 : x ^ 2 = (τ * x) ^ 2 := by rw [mul_pow, hτ, one_mul]
  obtain ⟨y, hyd⟩ : ∃ y, y = τ * x := ⟨_, rfl⟩
  rw [← hyd] at hy hx2
  have hyp : 0 < y := lt_of_lt_of_le hx0 hy.1
  have hyl1 : y < 1 := lt_of_le_of_lt hy.2 hx1
  obtain ⟨c, hc⟩ : ∃ c, c = Real.sqrt (1 - x ^ 2) := ⟨_, rfl⟩
  rw [← hc]
  have hc2 : c ^ 2 = 1 - y ^ 2 := by
    rw [hc, Real.sq_sqrt (by rw [hx2]; nlinarith only [hyp, hyl1]), hx2]
  have hccmin : cmin ≤ c := by
    rw [hcmin, hc]; exact Real.sqrt_le_sqrt (by rw [hx2]; nlinarith only [hy.2, hyp, hx0])
  have hccmax : c ≤ cmax := by
    rw [hcmax, hc]; exact Real.sqrt_le_sqrt (by rw [hx2]; nlinarith only [hy.1, hx0])
  have hcp : 0 < c := lt_of_lt_of_le hcminp hccmin
  have hballS : ball c ρ ⊆ Icc (0 : ℝ) qhi := fun q hq => by
    rw [mem_ball, Real.dist_eq, abs_lt] at hq
    constructor <;> linarith [hq.1, hq.2]
  refine ⟨by linarith, fun q hq => ?_, ?_⟩
  · have h1 : 0 < q := by linarith [hq.1]
    have h2 : q < 1 := by linarith [hq.2]
    constructor
    · nlinarith only [h1, h2]
    · norm_num
  rw [hrU_one_zero, hrA1_one_zero, ← hyd]
  exact hahn_datum_core hyp hyl1 hc2 hcp hccmin hK2n hρp hqhi1 hballS hK1 hK2

/-- info: 'FormalResearch.Special.hahn_datum_unif' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hahn_datum_unif

end FormalResearch.Special
