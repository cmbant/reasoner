import FormalResearch.FourQubitEntropy.SevenQubitIcoStationarity

/-!
# The decimal value of the entropy maximum on the icosahedral family, and two logarithmic constants

`thm:fqe-seven-entropy` and `prop:entropy-seven-stationarity` quote
`E₃(ψ_{x_*}) = 2.965356029477675899…` bits. This file proves the enclosure
`2.965356029477 < E₃(ψ_{x_*}) < 2.965356029478` (bits), where `E3` is the mean three-qubit entropy in nats
of `SevenQubitIcoEntropy`, divided by `log 2`.

Method (all exact rational arithmetic, no floating point): a general enclosure of `log r` from the
`arctanh` series `log r = 2 Σ z^{2k+1}/(2k+1)`, `z = (r-1)/(r+1)`, with the geometric tail bound
(`log_atanh_bounds`); enclosures of `ln 2`, `ln(3/2)` and of three logarithms of rationals near `1`; the
value `E3 b` at the rational point `b = 698288/10⁷` just above `x_*` (`star_enclosure` gives
`698287/10⁷ < x_* < b`), `E3 b ≤ E3 x_*` since `x_*` is the maximiser, and by the mean value theorem and
the monotonicity of `E3d` the upper bound `E3 x_* ≤ E3 b + (4/35)(R b/L b - 1)(b - a)`, with
`log y ≤ y - 1` and the closed equation of `SevenQubitIcoStationarity`.

Also: `joint_coeff_enclosure`: `4.5786 < 6 ln 2/(15/2 - 6 ln 3) < 4.5787`, the constant
`≈ 4.57862` of `W₁ + τ ≤ 6 ln 2/(15/2 - 6 ln 3) δ` in the section "Spectral corollaries and stability" of
`four_qubit_entropy.tex` (`entropy_stability_joint` is the inequality).

Not proved: the digits beyond the twelfth.
-/

namespace FormalResearch.FourQubitEntropy.SevenQubitIco

namespace StarValue

open Real Set Stationarity

/-- Partial sum of the `arctanh` series of `log r` with `z = (r-1)/(r+1)`. -/
noncomputable def atanhPartial (z : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, 2 * (1 / (2 * (k : ℝ) + 1)) * z ^ (2 * k + 1)

theorem log_atanh_bounds {r : ℝ} (hr : 1 ≤ r) (N : ℕ) :
    atanhPartial ((r - 1) / (r + 1)) N ≤ log r ∧
    log r ≤ atanhPartial ((r - 1) / (r + 1)) N +
      2 * ((r - 1) / (r + 1)) ^ (2 * N + 1) / ((2 * (N : ℝ) + 1) * (1 - ((r - 1) / (r + 1)) ^ 2)) := by
  set z : ℝ := (r - 1) / (r + 1) with hz
  have hr0 : 0 < r + 1 := by linarith
  have hz0 : 0 ≤ z := div_nonneg (by linarith) hr0.le
  have hz1 : z < 1 := by rw [hz, div_lt_one hr0]; linarith
  have habs : |z| < 1 := by rw [abs_of_nonneg hz0]; exact hz1
  have hS := Real.hasSum_log_sub_log_of_abs_lt_one habs
  have hlog : log (1 + z) - log (1 - z) = log r := by
    have h1 : 0 < 1 + z := by linarith
    have h2 : 0 < 1 - z := by linarith
    rw [← Real.log_div h1.ne' h2.ne']
    congr 1
    rw [hz]
    field_simp
    ring
  rw [hlog] at hS
  set f : ℕ → ℝ := fun k => 2 * (1 / (2 * (k : ℝ) + 1)) * z ^ (2 * k + 1) with hf
  have hfnn : ∀ k, 0 ≤ f k := fun k => by simp only [hf]; positivity
  constructor
  · exact sum_le_hasSum (Finset.range N) (fun i _ => hfnn i) hS
  · have hT := (hasSum_nat_add_iff' N).mpr hS
    have hz2 : z ^ 2 < 1 := by nlinarith
    have hg : HasSum (fun k : ℕ => (2 * z ^ (2 * N + 1) / (2 * (N : ℝ) + 1)) * (z ^ 2) ^ k)
        ((2 * z ^ (2 * N + 1) / (2 * (N : ℝ) + 1)) * (1 - z ^ 2)⁻¹) :=
      (hasSum_geometric_of_lt_one (by positivity) hz2).mul_left _
    have hle : ∀ k : ℕ, f (k + N) ≤ (2 * z ^ (2 * N + 1) / (2 * (N : ℝ) + 1)) * (z ^ 2) ^ k := by
      intro k
      simp only [hf]
      have e : z ^ (2 * (k + N) + 1) = z ^ (2 * N + 1) * (z ^ 2) ^ k := by
        rw [← pow_mul, ← pow_add]; congr 1; ring
      rw [e]
      have hd : 1 / (2 * ((k + N : ℕ) : ℝ) + 1) ≤ 1 / (2 * (N : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        push_cast; have : (0:ℝ) ≤ k := Nat.cast_nonneg k; linarith
      have hp : 0 ≤ z ^ (2 * N + 1) * (z ^ 2) ^ k := by positivity
      calc 2 * (1 / (2 * ((k + N : ℕ) : ℝ) + 1)) * (z ^ (2 * N + 1) * (z ^ 2) ^ k)
          ≤ 2 * (1 / (2 * (N : ℝ) + 1)) * (z ^ (2 * N + 1) * (z ^ 2) ^ k) := by gcongr
        _ = _ := by ring
    have := hasSum_le hle hT hg
    have e2 : (2 * z ^ (2 * N + 1) / (2 * (N : ℝ) + 1)) * (1 - z ^ 2)⁻¹
        = 2 * z ^ (2 * N + 1) / ((2 * (N : ℝ) + 1) * (1 - z ^ 2)) := by
      field_simp
    rw [e2] at this
    unfold atanhPartial
    linarith


theorem log_enc {r : ℝ} (hr : 1 ≤ r) (N : ℕ) (lo hi : ℝ)
    (hlo : lo ≤ atanhPartial ((r - 1) / (r + 1)) N)
    (hhi : atanhPartial ((r - 1) / (r + 1)) N +
      2 * ((r - 1) / (r + 1)) ^ (2 * N + 1) / ((2 * (N : ℝ) + 1) * (1 - ((r - 1) / (r + 1)) ^ 2)) ≤ hi) :
    lo ≤ log r ∧ log r ≤ hi := by
  obtain ⟨h1, h2⟩ := log_atanh_bounds hr N
  exact ⟨le_trans hlo h1, le_trans h2 hhi⟩

theorem log2_enc : (6931471805599453094172 / 10000000000000000000000 : ℝ) ≤ log (2) ∧ log (2) ≤ (6931471805599453094173 / 10000000000000000000000 : ℝ) :=
  log_enc (by norm_num) 22 _ _ (by unfold atanhPartial; norm_num [Finset.sum_range_succ])
    (by unfold atanhPartial; norm_num [Finset.sum_range_succ])

theorem log32_enc : (4054651081081643819776 / 10000000000000000000000 : ℝ) ≤ log (3 / 2) ∧ log (3 / 2) ≤ (4054651081081643819781 / 10000000000000000000000 : ℝ) :=
  log_enc (by norm_num) 14 _ _ (by unfold atanhPartial; norm_num [Finset.sum_range_succ])
    (by unfold atanhPartial; norm_num [Finset.sum_range_succ])

theorem LA_enc : (858863082986425997134 / 10000000000000000000000 : ℝ) ≤ log (390625 / 358476) ∧ log (390625 / 358476) ≤ (858863082986425997135 / 10000000000000000000000 : ℝ) :=
  log_enc (by norm_num) 14 _ _ (by unfold atanhPartial; norm_num [Finset.sum_range_succ])
    (by unfold atanhPartial; norm_num [Finset.sum_range_succ])

theorem LB_enc : (2206639356065903749434 / 10000000000000000000000 : ℝ) ≤ log (487072 / 390625) ∧ log (487072 / 390625) ≤ (2206639356065903749435 / 10000000000000000000000 : ℝ) :=
  log_enc (by norm_num) 14 _ _ (by unfold atanhPartial; norm_num [Finset.sum_range_succ])
    (by unfold atanhPartial; norm_num [Finset.sum_range_succ])

theorem LC_enc : (2381873438477599997894 / 10000000000000000000000 : ℝ) ≤ log (390625 / 307834) ∧ log (390625 / 307834) ≤ (2381873438477599997895 / 10000000000000000000000 : ℝ) :=
  log_enc (by norm_num) 14 _ _ (by unfold atanhPartial; norm_num [Finset.sum_range_succ])
    (by unfold atanhPartial; norm_num [Finset.sum_range_succ])

/-! ### The value of `E3` at the rational point `b = 698288/10⁷` -/

theorem log_t1 : log (89619 / 781250 : ℝ) = -3 * log 2 - log (390625 / 358476) := by
  have : (89619 / 781250 : ℝ) = (2 ^ 3 * (390625 / 358476))⁻¹ := by norm_num
  rw [this, Real.log_inv, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  push_cast; ring

theorem log_t2 : log (60884 / 390625 : ℝ) = -3 * log 2 + log (487072 / 390625) := by
  have : (60884 / 390625 : ℝ) = (2 ^ 3)⁻¹ * (487072 / 390625) := by norm_num
  rw [this, Real.log_mul (by norm_num) (by norm_num), Real.log_inv, Real.log_pow]
  push_cast; ring

theorem log_t3 : log (89619 / 390625 : ℝ) = -2 * log 2 - log (390625 / 358476) := by
  have : (89619 / 390625 : ℝ) = 2 * (89619 / 781250) := by norm_num
  rw [this, Real.log_mul (by norm_num) (by norm_num), log_t1]
  ring

theorem log_t4 : log (153917 / 1562500 : ℝ) = -3 * log 2 - log (390625 / 307834) := by
  have : (153917 / 1562500 : ℝ) = (2 ^ 3 * (390625 / 307834))⁻¹ := by norm_num
  rw [this, Real.log_inv, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  push_cast; ring

theorem E3_b_eq : E3 (698288 / 10000000) =
    (-(195 * (89619 / 781250)) * (-3 * log 2 - log (390625 / 358476))
     - 40 * (60884 / 390625) * (-3 * log 2 + log (487072 / 390625))
     - 15 * (89619 / 390625) * (-2 * log 2 - log (390625 / 358476))
     - 30 * (153917 / 1562500) * (-3 * log 2 - log (390625 / 307834))) / 35 := by
  have e1 : 4 * u (698288 / 10000000) = 89619 / 781250 := by unfold u; norm_num
  have e2 : 3 * u (698288 / 10000000) + 698288 / 10000000 = 60884 / 390625 := by unfold u; norm_num
  have e3 : 8 * u (698288 / 10000000) = 89619 / 390625 := by unfold u; norm_num
  have e4 : u (698288 / 10000000) + 698288 / 10000000 = 153917 / 1562500 := by unfold u; norm_num
  unfold E3
  rw [e1, e2, e3, e4]
  simp only [Real.negMulLog_def]
  rw [log_t1, log_t2, log_t3, log_t4]
  ring

/-- **The decimal value.** The mean three-qubit entropy of `ψ_{x_*}` is
`2.9653560294776 < E₃ < 2.9653560294777` bits (the paper quotes `2.965356029477675899…`). -/
theorem star_value : ∃ c : ℝ, (∀ y ∈ Icc (0 : ℝ) (1 / 2), y ≠ c → E3 y < E3 c) ∧
    2 ^ 32 * (1 - 2 * c) ^ 15 = 3 ^ 8 * (1 + 8 * c) ^ 8 * (1 + 28 * c) ^ 7 ∧
    (29653560294776 / 10000000000000 : ℝ) < E3 c / log 2 ∧
    E3 c / log 2 < 29653560294777 / 10000000000000 := by
  obtain ⟨c, hmax, hac, hcb⟩ := star_enclosure
  obtain ⟨c', hmax', h32, hc1, heq, -⟩ := star_equation
  -- the two maximisers coincide
  have hcc : c = c' := by
    by_contra hne
    have h1 := hmax c' ⟨by linarith, by linarith⟩ (Ne.symm hne)
    have h2 := hmax' c ⟨by linarith, by linarith⟩ hne
    linarith
  subst hcc
  have hc0 : 0 < c := by linarith
  have hc2 : c < 1 / 2 := by linarith
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = 698288 / 10000000 := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 698287 / 10000000 := ⟨_, rfl⟩
  rw [← hb] at hcb
  rw [← ha] at hac
  have hEb : E3 b = (-(195 * (89619 / 781250)) * (-3 * log 2 - log (390625 / 358476))
     - 40 * (60884 / 390625) * (-3 * log 2 + log (487072 / 390625))
     - 15 * (89619 / 390625) * (-2 * log 2 - log (390625 / 358476))
     - 30 * (153917 / 1562500) * (-3 * log 2 - log (390625 / 307834))) / 35 := by
    rw [hb]; exact E3_b_eq
  have hbi : b < 1 / 2 := by rw [hb]; norm_num
  have hb0 : 0 ≤ b := by rw [hb]; norm_num
  have hl2pos : 0 < log 2 := Real.log_pos (by norm_num)
  obtain ⟨h2l, h2h⟩ := log2_enc
  obtain ⟨hAl, hAh⟩ := LA_enc
  obtain ⟨hBl, hBh⟩ := LB_enc
  obtain ⟨hCl, hCh⟩ := LC_enc
  refine ⟨c, hmax, heq, ?_, ?_⟩
  · -- lower bound: `E3 b < E3 c`
    rw [lt_div_iff₀ hl2pos]
    have hlow : E3 b < E3 c :=
      hmax b ⟨hb0, by linarith⟩ (by intro h; rw [h] at hcb; exact lt_irrefl _ hcb)
    rw [hEb] at hlow
    nlinarith
  · -- upper bound by the mean value theorem
    rw [div_lt_iff₀ hl2pos]
    have hmvt := exists_hasDerivAt_eq_slope E3 E3d hcb continuous_E3.continuousOn
      (fun x hx => hasDerivAt_E3 (by linarith [hx.1]) (by linarith [hx.2, hbi]))
    obtain ⟨ξ, hξ, hξd⟩ := hmvt
    have hanti : E3d b ≤ E3d ξ :=
      E3d_strictAntiOn.antitoneOn ⟨by linarith [hξ.1], by linarith [hξ.2, hbi]⟩ ⟨hb0, hbi⟩ hξ.2.le
    have hbc : 0 < b - c := by linarith
    have hslope : E3d b * (b - c) ≤ E3 b - E3 c := by
      rw [hξd, le_div_iff₀ hbc] at hanti
      linarith
    -- `-E3d b ≤ (4/35)(R/L - 1)`
    have hLR := E3d_eq_log_ratio hb0 hbi
    have hLpos := L_pos hbi
    have hRpos := R_pos hb0
    have hlogle : log (R b / L b) ≤ R b / L b - 1 := Real.log_le_sub_one_of_pos (div_pos hRpos hLpos)
    have hlogneg : log (L b / R b) = - log (R b / L b) := by
      rw [← Real.log_inv, inv_div]
    have hEd : -E3d b ≤ 4 / 35 * (R b / L b - 1) := by
      rw [hLR, hlogneg]; linarith
    have hwnn : 0 ≤ 4 / 35 * (R b / L b - 1) := by
      unfold L R; rw [hb]; norm_num
    have hnum : 4 / 35 * (R b / L b - 1) * (b - a) < 1 / 10 ^ 14 := by
      unfold L R; rw [hb, ha]; norm_num
    have hbc2 : b - c ≤ b - a := by linarith
    have h1 : -E3d b * (b - c) ≤ 4 / 35 * (R b / L b - 1) * (b - c) :=
      mul_le_mul_of_nonneg_right hEd hbc.le
    have h2 : 4 / 35 * (R b / L b - 1) * (b - c) ≤ 4 / 35 * (R b / L b - 1) * (b - a) :=
      mul_le_mul_of_nonneg_left hbc2 hwnn
    have hup : E3 c ≤ E3 b + 1 / 10 ^ 14 := by linarith
    rw [hEb] at hup
    nlinarith


/-- **The SC-2 lower witness, discharged for the maximiser.** The family maximum `E_* = E3 x_*` satisfies
`E_* > (59307/20000) ln 2`, i.e. `E₃(ψ_{x_*}) > 2.96535` bits. This is the hypothesis `hwit` of
`competitor_purity_band` / `eigenCap_497` in `SevenQubitCompetitorBand` / `SevenQubitEigenCap497` with
`Estar := E3 x_*` (the paper's `E_*`), so it need not be assumed once `Estar` is taken to be the family
maximum. -/
theorem sc2_witness : ∃ c : ℝ, (∀ y ∈ Icc (0 : ℝ) (1 / 2), y ≠ c → E3 y < E3 c) ∧
    (59307 / 20000 : ℝ) * log 2 < E3 c := by
  obtain ⟨c, hmax, -, h1, -⟩ := star_value
  refine ⟨c, hmax, ?_⟩
  have h2 : (0 : ℝ) < log 2 := Real.log_pos (by norm_num)
  have h3 : (59307 / 20000 : ℝ) < E3 c / log 2 := lt_trans (by norm_num) h1
  have := (lt_div_iff₀ h2).mp h3
  linarith

/-- `ln 3 = ln 2 + ln (3/2)` with enclosures. -/
theorem log3_enclosure : (10986122886681 / 10000000000000 : ℝ) < log 3 ∧
    log 3 < 10986122886682 / 10000000000000 := by
  have h : log 3 = log 2 + log (3 / 2) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  obtain ⟨h2l, h2h⟩ := log2_enc
  obtain ⟨h3l, h3h⟩ := log32_enc
  rw [h]
  constructor <;> linarith

/-- The constant of the joint stability estimate `W₁ + τ ≤ (6 ln 2/(15/2 - 6 ln 3)) δ`
(`entropy_stability_joint`): `4.5786 < 6 ln 2/(15/2 - 6 ln 3) < 4.5787`. -/
theorem joint_coeff_enclosure :
    (45786 / 10000 : ℝ) < 6 * log 2 / (15 / 2 - 6 * log 3) ∧
    6 * log 2 / (15 / 2 - 6 * log 3) < 45787 / 10000 := by
  obtain ⟨h3l, h3h⟩ := log3_enclosure
  obtain ⟨h2l, h2h⟩ := log2_enc
  have hD : 0 < 15 / 2 - 6 * log 3 := by linarith
  constructor
  · rw [lt_div_iff₀ hD]; linarith
  · rw [div_lt_iff₀ hD]; linarith

end StarValue

end FormalResearch.FourQubitEntropy.SevenQubitIco
