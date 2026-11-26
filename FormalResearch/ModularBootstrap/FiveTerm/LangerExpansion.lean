module

public import FormalResearch.ModularBootstrap.FiveTerm.Constants
public import FormalResearch.ModularBootstrap.FiveTerm.Langer

/-!
# The Virasoro Langer node and the `c'` versus `c` convention shift (`cts:langer`(2), (3))

Source: `CFT/modular_bootstrap/paper/constant_term_slit_strip.tex`, Proposition C1 (`cts:langer`).

With `c' = c - 1`, `N = cumulN` and `κ_L = (2/(3π)) |a_1|^{3/2}`:

* `xLanger c` is the unique solution `x_L(c) > ξ_*` of `c' N(x_L) = κ_L` (`xLanger_spec`), and
  `deltaLanger c = c'/12 + (c'/3) x_L(c)²`;
* `langer_node_expansion` (`cts:langer-exp`): `Δ_Langer(c) = c'/Λ_V + A_opt c'^{1/3}
  + c_1^Langer c'^{-1/3} + O(c'^{-1})` as `c' → ∞`;
* `langer_convention_shift` (`cts:langer`(3)): for every sequence `Δ(c)`,
  `R_c = R_{c'} - 1/Λ_V - (A_opt/3) c^{-2/3} + O(c^{-5/3})`, where
  `R_{c'} = Δ - c'/Λ_V - A_opt c'^{1/3}` and `R_c = Δ - c/Λ_V - A_opt c^{1/3}`.

The `O(·)` terms are explicit (`|·| ≤ C ·`, for `c ≥ c_0`).
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.Special FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Upper.Comb

/-! ### 1. The Langer node `x_L(c)` -/

/-- `κ_L = (2/(3π)) |a_1|^{3/2}`, the right-hand side of `c' N(x_L) = κ_L`. -/
noncomputable def langerRhs : ℝ := 2 / (3 * π) * |airyZero 1| ^ (3 / 2 : ℝ)

lemma langerRhs_pos : 0 < langerRhs := by
  unfold langerRhs
  have := abs_pos.mpr (airyZero_neg 1).ne
  have := Real.pi_pos
  positivity

/-- The Langer node `x_L(c)`: the solution of `c' N(x_L) = κ_L`, `c' = c - 1`
(`chiQuantile` at level `1/4 + κ_L`). -/
noncomputable def xLanger (c : ℝ) : ℝ := chiQuantile (c - 1) (1 / 4 + langerRhs)

/-- `Δ_Langer(c) = c'/12 + (c'/3) x_L(c)²`. -/
noncomputable def deltaLanger (c : ℝ) : ℝ := (c - 1) / 12 + (c - 1) / 3 * xLanger c ^ 2

/-- `x_L(c) > ξ_*` is the unique solution of `c' N(x_L) = κ_L` (`cts:langer`, definition). -/
theorem xLanger_spec {c : ℝ} (hc : 1 < c) :
    xiStar < xLanger c ∧ (c - 1) * cumulN (xLanger c) = langerRhs ∧
      ∀ y, xiStar < y → (c - 1) * cumulN y = langerRhs → y = xLanger c := by
  have hc' : 0 < c - 1 := by linarith
  have ha : 1 / 4 ≤ 1 / 4 + langerRhs := by linarith [langerRhs_pos]
  obtain ⟨h1, h2⟩ := chiQuantile_spec hc' ha
  have h2' : (c - 1) * cumulN (xLanger c) = langerRhs := by
    unfold xLanger; rw [h2]; ring
  refine ⟨?_, h2', fun y hy hy2 => ?_⟩
  · refine lt_of_le_of_ne h1 fun h => ?_
    have : cumulN (xLanger c) = 0 := by rw [← h]; exact cumulN_xiStar
    rw [this, mul_zero] at h2'
    exact langerRhs_pos.ne h2'
  · apply cumulN_strictMonoOn.injOn (Set.mem_Ici.mpr hy.le) (Set.mem_Ici.mpr h1)
    exact mul_left_cancel₀ hc'.ne' (hy2.trans h2'.symm)

/-- `x_L(c) → ξ_*`: for every `r₀ > 0`, `x_L(c) < ξ_* + r₀` for large `c`. -/
lemma xLanger_lt_of_large {r₀ : ℝ} (hr₀ : 0 < r₀) :
    ∃ c₀ : ℝ, 1 < c₀ ∧ ∀ c ≥ c₀, xLanger c < xiStar + r₀ := by
  have hN0 : 0 < cumulN (xiStar + r₀) := by
    rw [← cumulN_xiStar]
    exact cumulN_strictMonoOn (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr (by linarith))
      (by linarith)
  refine ⟨langerRhs / cumulN (xiStar + r₀) + 2, by have := div_pos langerRhs_pos hN0; linarith,
    fun c hc => ?_⟩
  have hc1 : 1 < c := by have := div_pos langerRhs_pos hN0; linarith
  obtain ⟨hx, hN, -⟩ := xLanger_spec hc1
  by_contra h
  rw [not_lt] at h
  have hmono : cumulN (xiStar + r₀) ≤ cumulN (xLanger c) :=
    cumulN_strictMonoOn.monotoneOn (Set.mem_Ici.mpr (by linarith)) (Set.mem_Ici.mpr hx.le) h
  have : langerRhs < (c - 1) * cumulN (xiStar + r₀) := by
    have h1 : langerRhs / cumulN (xiStar + r₀) + 1 ≤ c - 1 := by linarith
    have h2 : langerRhs / cumulN (xiStar + r₀) * cumulN (xiStar + r₀) = langerRhs := by
      field_simp
    nlinarith only [h1, h2, hN0]
  nlinarith only [this, hmono, hN, hc1, hN0]

/-! ### 2. Inversion of the Langer coordinate -/

/-- Inversion: if `ε = τ(ξ_*+r)` satisfies `|ε - r - ηr²| ≤ 2r³` for small `r > 0`, then
`|r - (ε - ηε²)| ≤ 24 ε³`, `r ≤ 2ε`, `ε ≤ 2r` and `|r² - ε²| ≤ 2ε³`. -/
lemma inversion_aux {r ε η : ℝ} (hr : 0 < r) (hr0 : r ≤ 1 / 30) (hη0 : 0 ≤ η) (hη1 : η ≤ 4 / 50)
    (h : |ε - r - η * r ^ 2| ≤ 2 * r ^ 3) :
    r ≤ 2 * ε ∧ ε ≤ 2 * r ∧ |r - (ε - η * ε ^ 2)| ≤ 24 * ε ^ 3 ∧ |r ^ 2 - ε ^ 2| ≤ 2 * ε ^ 3 := by
  obtain ⟨h1, h2⟩ := abs_le.mp h
  have hr2 : r ^ 2 ≤ r / 30 := by nlinarith only [hr, hr0]
  have hr3 : r ^ 3 ≤ r / 900 := by nlinarith only [hr, hr0, hr2]
  have hηr : η * r ^ 2 ≤ η * (r / 30) := mul_le_mul_of_nonneg_left hr2 hη0
  have hηr' : 0 ≤ η * r ^ 2 := by positivity
  have hε1 : r ≤ 2 * ε := by nlinarith only [h1, hr3, hηr', hr]
  have hε2 : ε ≤ 2 * r := by nlinarith only [h2, hr3, hηr, hr, hη1]
  have hε0 : 0 < ε := by linarith
  -- |r - ε| ≤ η r² + 2 r³
  have hd : |r - ε| ≤ η * r ^ 2 + 2 * r ^ 3 := by
    rw [abs_le]; constructor <;> nlinarith only [h1, h2, hηr']
  have hd2 : |r - ε| ≤ 3 / 5 * ε ^ 2 := by
    have : η * r ^ 2 + 2 * r ^ 3 ≤ 3 / 5 * ε ^ 2 := by
      have h3 : r ^ 3 ≤ r ^ 2 / 30 := by nlinarith only [hr, hr0, sq_nonneg r]
      have h4 : r ^ 2 ≤ 4 * ε ^ 2 := by nlinarith only [hε1, hr]
      nlinarith only [h3, h4, hη1, hη0, sq_nonneg r, mul_nonneg hη0 (sq_nonneg r)]
    exact hd.trans this
  refine ⟨hε1, hε2, ?_, ?_⟩
  · -- r - (ε - η ε²) = -η (r² - ε²) + θ
    have hsq : |r ^ 2 - ε ^ 2| ≤ 2 * ε ^ 3 := by
      have : r ^ 2 - ε ^ 2 = (r - ε) * (r + ε) := by ring
      rw [this, abs_mul, abs_of_pos (by linarith : 0 < r + ε)]
      calc |r - ε| * (r + ε) ≤ (3 / 5 * ε ^ 2) * (3 * ε) :=
            mul_le_mul hd2 (by linarith) (by linarith) (by positivity)
        _ ≤ 2 * ε ^ 3 := by nlinarith only [pow_pos hε0 3]
    have hθ : |(r - ε + η * r ^ 2)| ≤ 2 * r ^ 3 := by
      rw [abs_le]; constructor <;> nlinarith only [h1, h2]
    have key : r - (ε - η * ε ^ 2) = (r - ε + η * r ^ 2) - η * (r ^ 2 - ε ^ 2) := by ring
    rw [key]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_of_nonneg hη0]
    have h5 : r ^ 3 ≤ 8 * ε ^ 3 := by
      have := pow_le_pow_left₀ hr.le hε1 3
      nlinarith only [this]
    nlinarith only [hθ, hsq, h5, hη1, hη0, pow_pos hε0 3, mul_le_mul_of_nonneg_left hsq hη0]
  · have : r ^ 2 - ε ^ 2 = (r - ε) * (r + ε) := by ring
    rw [this, abs_mul, abs_of_pos (by linarith : 0 < r + ε)]
    calc |r - ε| * (r + ε) ≤ (3 / 5 * ε ^ 2) * (3 * ε) :=
          mul_le_mul hd2 (by linarith) (by linarith) (by positivity)
      _ ≤ 2 * ε ^ 3 := by nlinarith only [pow_pos hε0 3]

/-! ### 3. The expansion of the Langer node (`cts:langer-exp`) -/

/-- `s_1 = |a_1|/β`. -/
noncomputable def sLanger : ℝ := |airyZero 1| / betaTip

lemma sLanger_pos : 0 < sLanger := div_pos (abs_pos.mpr (airyZero_neg 1).ne) betaTip_pos

lemma betaTip_eq_rpow : betaTip = (3 * π / 2 * kTip) ^ (2 / 3 : ℝ) := by
  unfold betaTip KTip
  congr 1; ring

/-- `τ(x_L(c)) = (|a_1|/β) c'^{-2/3}`. -/
lemma tau_xLanger {c : ℝ} (hc : 1 < c) :
    (cumulN (xLanger c) / kTip) ^ (2 / 3 : ℝ) = sLanger * (c - 1) ^ (-(2 / 3) : ℝ) := by
  have hc' : 0 < c - 1 := by linarith
  obtain ⟨-, hN, -⟩ := xLanger_spec hc
  have hk := kTip_pos
  have hpi := Real.pi_pos
  have ha : 0 < |airyZero 1| := abs_pos.mpr (airyZero_neg 1).ne
  have hN' : cumulN (xLanger c) = langerRhs / (c - 1) := by
    rw [eq_div_iff hc'.ne', mul_comm]; exact hN
  have h1 : cumulN (xLanger c) / kTip =
      |airyZero 1| ^ (3 / 2 : ℝ) * ((3 * π / 2 * kTip)⁻¹ * (c - 1)⁻¹) := by
    rw [hN']; unfold langerRhs; field_simp
  have hb0 : 0 < 3 * π / 2 * kTip := by positivity
  rw [h1, Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul ha.le, Real.inv_rpow hb0.le, Real.inv_rpow hc'.le, ← betaTip_eq_rpow,
    Real.rpow_neg hc'.le]
  norm_num
  unfold sLanger
  ring

lemma eta_bounds : 0 ≤ π / (30 * √2) ∧ π / (30 * √2) ≤ 4 / 50 := by
  have hu : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hu0 : 0 < √2 := Real.sqrt_pos.mpr (by norm_num)
  have hu2 : 7 / 5 ≤ √2 := by nlinarith only [hu, hu0]
  have hpi := Real.pi_lt_d2
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (by positivity)]
  nlinarith only [hpi, hu2]

lemma xiStar_le_third : xiStar ≤ 1 / 3 := by
  unfold xiStar
  rw [div_le_iff₀ Real.pi_pos]
  have := arsinh_one_lt_one
  nlinarith only [this, Real.pi_gt_three]

/-- **`cts:langer`(2)**, the expansion (`cts:langer-exp`) of the exact Virasoro Langer node:
there are `C, c₀` with, for all `c ≥ c₀` (`c' = c - 1`),
`|Δ_Langer(c) - (c'/Λ_V + A_opt c'^{1/3} + c_1^Langer c'^{-1/3})| ≤ C / c'`. -/
theorem langer_node_expansion :
    ∃ C c₀ : ℝ, 1 < c₀ ∧ ∀ c ≥ c₀,
      |deltaLanger c - ((c - 1) / lambdaV + Aopt * (c - 1) ^ (1 / 3 : ℝ) +
        c1Langer * (c - 1) ^ (-(1 / 3) : ℝ))| ≤ C / (c - 1) := by
  have hpi := Real.pi_pos
  obtain ⟨c₀, hc₀, hc₀'⟩ := xLanger_lt_of_large (r₀ := 1 / (10 * π)) (by positivity)
  refine ⟨6 * sLanger ^ 3, c₀, hc₀, fun c hc => ?_⟩
  have hc1 : 1 < c := lt_of_lt_of_le hc₀ hc
  have hc' : 0 < c - 1 := by linarith
  obtain ⟨hxi, -, -⟩ := xLanger_spec hc1
  set x := xLanger c with hx
  set r := x - xiStar with hr
  have hr0 : 0 < r := sub_pos.mpr hxi
  have hr1 : π * r ≤ 1 / 10 := by
    have : r < 1 / (10 * π) := by have := hc₀' c hc; linarith
    rw [lt_div_iff₀ (by positivity)] at this
    nlinarith only [this]
  have hr30 : r ≤ 1 / 30 := by nlinarith only [hr1, Real.pi_gt_three, hr0]
  have hxr : xiStar + r = x := by rw [hr]; ring
  set ε : ℝ := sLanger * (c - 1) ^ (-(2 / 3) : ℝ) with hε
  have hτ := tau_tip_expansion hr0 hr1
  rw [hxr, hx, tau_xLanger hc1, ← hε] at hτ
  obtain ⟨η0, η1⟩ := eta_bounds
  obtain ⟨-, hε2, hinv, hsq⟩ := inversion_aux hr0 hr30 η0 η1 hτ
  have hε0 : 0 < ε := by
    have := sLanger_pos
    have := Real.rpow_pos_of_pos hc' (-(2 / 3) : ℝ)
    positivity
  -- the rpow identities
  set c' := c - 1 with hc'def
  have mr : ∀ a : ℝ, c' * c' ^ a = c' ^ (1 + a) := fun a => by
    rw [Real.rpow_add hc', Real.rpow_one]
  have p2 : (c' ^ (-(2 / 3) : ℝ)) ^ 2 = c' ^ (-(4 / 3) : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc'.le]; norm_num
  have p3 : (c' ^ (-(2 / 3) : ℝ)) ^ 3 = c' ^ (-(2) : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc'.le]; norm_num
  have e1 : c' * ε = sLanger * c' ^ (1 / 3 : ℝ) := by
    rw [hε, show c' * (sLanger * c' ^ (-(2 / 3) : ℝ)) = sLanger * (c' * c' ^ (-(2 / 3) : ℝ)) by ring,
      mr]
    norm_num
  have e2 : c' * ε ^ 2 = sLanger ^ 2 * c' ^ (-(1 / 3) : ℝ) := by
    rw [hε, mul_pow, p2, show c' * (sLanger ^ 2 * c' ^ (-(4 / 3) : ℝ)) =
      sLanger ^ 2 * (c' * c' ^ (-(4 / 3) : ℝ)) by ring, mr]
    norm_num
  have e3 : c' * ε ^ 3 = sLanger ^ 3 / c' := by
    rw [hε, mul_pow, p3, show c' * (sLanger ^ 3 * c' ^ (-(2) : ℝ)) =
      sLanger ^ 3 * (c' * c' ^ (-(2) : ℝ)) by ring, mr]
    norm_num
    rw [Real.rpow_neg_one]; ring
  have hlam : c' / lambdaV = c' * (1 / 12 + xiStar ^ 2 / 3) := by
    have h := xiBar_eq_inv_lambdaV_sub
    unfold xiBar at h
    rw [div_eq_mul_one_div, h]; ring
  have hA : Aopt = 2 * xiStar / 3 * sLanger := by
    rw [Aopt_eq_mul_abs_airyZero_div_betaTip]; unfold sLanger; ring
  have hc1eq : c1Langer = (1 / 3 - 2 * xiStar / 3 * (π / (30 * √2))) * sLanger ^ 2 := by
    unfold c1Langer sLanger
    have hu0 : 0 < √2 := Real.sqrt_pos.mpr (by norm_num)
    field_simp
    ring
  have hΔ : deltaLanger c - ((c - 1) / lambdaV + Aopt * (c - 1) ^ (1 / 3 : ℝ) +
      c1Langer * (c - 1) ^ (-(1 / 3) : ℝ)) =
      2 * xiStar / 3 * (c' * (r - (ε - π / (30 * √2) * ε ^ 2))) + c' / 3 * (r ^ 2 - ε ^ 2) := by
    have hd : deltaLanger c = c' / 12 + c' / 3 * (xiStar + r) ^ 2 := by
      unfold deltaLanger; rw [hxr]
    rw [hd, hlam, hA, hc1eq]
    have e1' := e1; have e2' := e2
    have : 2 * xiStar / 3 * sLanger * c' ^ (1 / 3 : ℝ) = 2 * xiStar / 3 * (c' * ε) := by rw [e1]; ring
    have h2 : (1 / 3 - 2 * xiStar / 3 * (π / (30 * √2))) * sLanger ^ 2 * c' ^ (-(1 / 3) : ℝ) =
        (1 / 3 - 2 * xiStar / 3 * (π / (30 * √2))) * (c' * ε ^ 2) := by rw [e2]; ring
    rw [show (c - 1) = c' from rfl, this, h2]
    ring
  rw [hΔ]
  have hb1 : |c' * (r - (ε - π / (30 * √2) * ε ^ 2))| ≤ c' * (24 * ε ^ 3) := by
    rw [abs_mul, abs_of_pos hc']
    exact mul_le_mul_of_nonneg_left hinv hc'.le
  have hb2 : |c' / 3 * (r ^ 2 - ε ^ 2)| ≤ c' / 3 * (2 * ε ^ 3) := by
    rw [abs_mul, abs_of_pos (by positivity)]
    exact mul_le_mul_of_nonneg_left hsq (by positivity)
  have hξ := xiStar_le_third
  have hξ0 := xiStar_pos
  refine (abs_add_le _ _).trans ?_
  have hb1' : |2 * xiStar / 3 * (c' * (r - (ε - π / (30 * √2) * ε ^ 2)))| ≤
      2 * xiStar / 3 * (c' * (24 * ε ^ 3)) := by
    rw [abs_mul, abs_of_pos (by positivity)]
    exact mul_le_mul_of_nonneg_left hb1 (by positivity)
  have hfin : 2 * xiStar / 3 * (c' * (24 * ε ^ 3)) + c' / 3 * (2 * ε ^ 3) ≤ 6 * (c' * ε ^ 3) := by
    have : 0 ≤ c' * ε ^ 3 := by positivity
    nlinarith only [hξ, hξ0, this]
  rw [e3] at hfin
  calc _ ≤ 2 * xiStar / 3 * (c' * (24 * ε ^ 3)) + c' / 3 * (2 * ε ^ 3) := add_le_add hb1' hb2
    _ ≤ 6 * (sLanger ^ 3 / c') := hfin
    _ = 6 * sLanger ^ 3 / c' := by ring

/-! ### 4. The convention shift `c'` versus `c` (`cts:langer`(3)) -/

lemma one_sub_rpow_third_bounds {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1 / 2) :
    1 - t / 3 - t ^ 2 ≤ (1 - t) ^ (1 / 3 : ℝ) ∧ (1 - t) ^ (1 / 3 : ℝ) ≤ 1 - t / 3 := by
  have hpos : 0 < 1 - t := by linarith
  set y : ℝ := (1 - t) ^ (1 / 3 : ℝ) with hy
  have hy0 : 0 < y := Real.rpow_pos_of_pos hpos _
  have hy3 : y ^ 3 = 1 - t := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hpos.le]; norm_num
  constructor
  · by_contra h
    rw [not_le] at h
    have hL : 0 ≤ 1 - t / 3 - t ^ 2 := by nlinarith only [h0, h1]
    have := pow_lt_pow_left₀ h hy0.le (by norm_num : (3 : ℕ) ≠ 0)
    rw [hy3] at this
    nlinarith only [this, h0, h1, mul_nonneg h0 (sq_nonneg t), pow_nonneg h0 4, pow_nonneg h0 5,
      pow_nonneg h0 6, sq_nonneg t]
  · by_contra h
    rw [not_le] at h
    have hM : 0 ≤ 1 - t / 3 := by linarith
    have := pow_lt_pow_left₀ h hM (by norm_num : (3 : ℕ) ≠ 0)
    rw [hy3] at this
    nlinarith only [this, h0, h1, mul_nonneg h0 (sq_nonneg t), sq_nonneg t]

/-- **`cts:langer`(3)**, the convention shift. For every `Δ : ℝ → ℝ` and `c ≥ 2`, with
`R_{c'} = Δ(c) - c'/Λ_V - A_opt c'^{1/3}` and `R_c = Δ(c) - c/Λ_V - A_opt c^{1/3}`,
`|R_c - (R_{c'} - 1/Λ_V - (A_opt/3) c^{-2/3})| ≤ A_opt c^{-5/3}`; and
`1/Λ_V = 1/12 + arsinh² 1/(3π²)` (`inv_lambdaV_eq`). -/
theorem langer_convention_shift (Δ : ℝ → ℝ) {c : ℝ} (hc : 2 ≤ c) :
    |(Δ c - c / lambdaV - Aopt * c ^ (1 / 3 : ℝ)) -
        ((Δ c - (c - 1) / lambdaV - Aopt * (c - 1) ^ (1 / 3 : ℝ)) - 1 / lambdaV -
          Aopt / 3 * c ^ (-(2 / 3) : ℝ))| ≤ Aopt * c ^ (-(5 / 3) : ℝ) := by
  have hc0 : 0 < c := by linarith
  have hA := Aopt_pos
  set t : ℝ := 1 / c with ht
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 / 2 := by rw [ht, div_le_div_iff₀ hc0 (by norm_num)]; linarith
  obtain ⟨b1, b2⟩ := one_sub_rpow_third_bounds ht0 ht1
  have hmul : (c - 1) ^ (1 / 3 : ℝ) = c ^ (1 / 3 : ℝ) * (1 - t) ^ (1 / 3 : ℝ) := by
    rw [← Real.mul_rpow hc0.le (by linarith)]
    congr 1; rw [ht]; field_simp
  have hc13 : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
  have ht1' : t = c ^ (-1 : ℝ) := by rw [ht, Real.rpow_neg_one]; field_simp
  have ht2' : t ^ 2 = c ^ (-2 : ℝ) := by
    rw [ht, div_pow, one_pow, Real.rpow_neg hc0.le, Real.rpow_two, one_div]
  have e1 : c ^ (1 / 3 : ℝ) * t = c ^ (-(2 / 3) : ℝ) := by
    rw [ht1', ← Real.rpow_add hc0]; norm_num
  have e2 : c ^ (1 / 3 : ℝ) * t ^ 2 = c ^ (-(5 / 3) : ℝ) := by
    rw [ht2', ← Real.rpow_add hc0]; norm_num
  have key : (Δ c - c / lambdaV - Aopt * c ^ (1 / 3 : ℝ)) -
        ((Δ c - (c - 1) / lambdaV - Aopt * (c - 1) ^ (1 / 3 : ℝ)) - 1 / lambdaV -
          Aopt / 3 * c ^ (-(2 / 3) : ℝ)) =
      Aopt * (c ^ (1 / 3 : ℝ) * ((1 - t) ^ (1 / 3 : ℝ) - (1 - t / 3))) := by
    rw [hmul]
    have : c ^ (-(2 / 3) : ℝ) = c ^ (1 / 3 : ℝ) * t := e1.symm
    rw [this]
    ring
  rw [key, abs_mul, abs_of_pos hA]
  have : |c ^ (1 / 3 : ℝ) * ((1 - t) ^ (1 / 3 : ℝ) - (1 - t / 3))| ≤ c ^ (-(5 / 3) : ℝ) := by
    rw [abs_mul, abs_of_pos hc13, abs_of_nonpos (by linarith)]
    rw [← e2]
    nlinarith only [b1, hc13, mul_le_mul_of_nonneg_left (by linarith : -( (1 - t) ^ (1 / 3 : ℝ) - (1 - t / 3)) ≤ t ^ 2) hc13.le]
  exact mul_le_mul_of_nonneg_left this hA.le

end FormalResearch.ModularBootstrap.FiveTerm

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.xLanger_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.xLanger_spec

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.langer_node_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.langer_node_expansion

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.langer_convention_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.langer_convention_shift
