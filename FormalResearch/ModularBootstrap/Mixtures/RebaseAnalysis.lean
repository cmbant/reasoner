module

public import FormalResearch.ModularBootstrap.Upper.Rigidity.Dictionary

/-!
# `pmix:rebase` (b), (c): the asymptotics of the rebased chart (`positive_mixtures.tex`, Lemma PM.1)

Pure real analysis in the large parameter `n` (the effective central charge `c̃`), `n' = n - 12 r`.

* `rebase_b` (b): `ξ̄ n' - c_* z (n')^{1/3} = ξ̄ n - c_* z n^{1/3} - 12 ξ̄ r + O(n^{-2/3})` for every fixed `z`;
  `rebase_b_offset`: a bounded offset `|x - (ξ̄ n - c_* z n^{1/3})| ≤ R_off` stays bounded,
  `|x - (ξ̄ n' - c_* z n'^{1/3})| ≤ R_off + 12 ξ̄ r + 1` for large `n`.
* `rebase_c_u` (c): on every window `|u_{n'}(t)| ≤ R`, `u_n(t) - u_{n'}(t) = 6 β r ξ_* n^{-1/3} + O_R(n^{-1})`,
  uniformly in `t > 0` (`u_n = uAiry n`, `β = betaTip`, `ξ_* = xiStar`).
* `rebase_c_J` (c): `J_n(t) / J_{n'}(t) = 1 + O(n^{-1})` (here exactly `(n'/n)^{1/6}`, so `|J_n/J_{n'} - 1| ≤ 12 r / n`
  for every `t > 0`; no window is needed).

Method: with `m = n^{1/6}`, `m' = (n')^{1/6}` every quantity is polynomial: `n^{2/3} = m^4`, `n^{1/3} = m^2`,
`√n = m^3`, `m^6 - m'^6 = 12 r`, so the estimates are elementary identities in `δ = m - m'`.
-/

@[expose] public section

open Filter Topology
open scoped Real

namespace FormalResearch.ModularBootstrap.Mixtures

open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Upper.Rigidity

/-! ### The sixth-root substitution -/

section SixthRoot

variable {n : ℝ}

private lemma sixth_pow (hn : 0 < n) : (n ^ ((1 : ℝ) / 6)) ^ 6 = n := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]; norm_num

private lemma rpow_two_thirds_eq (hn : 0 < n) : n ^ ((2 : ℝ) / 3) = (n ^ ((1 : ℝ) / 6)) ^ 4 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]; norm_num

private lemma rpow_third_eq (hn : 0 < n) : n ^ ((1 : ℝ) / 3) = (n ^ ((1 : ℝ) / 6)) ^ 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]; norm_num

private lemma sqrt_of_sixth {m : ℝ} (hm : 0 < m) (h : m ^ 6 = n) : √n = m ^ 3 := by
  rw [← h, show m ^ 6 = (m ^ 3) ^ 2 by ring]
  exact Real.sqrt_sq (by positivity)

private lemma sqrt_eq_cube (hn : 0 < n) : √n = (n ^ ((1 : ℝ) / 6)) ^ 3 :=
  sqrt_of_sixth (Real.rpow_pos_of_pos hn _) (sixth_pow hn)

/-- `uAiry n t` in the variable `m = n^{1/6}`: `-β (σ m - ξ_* m^4)`, `σ = √(3t)`. -/
private lemma uAiry_eq_m (hn : 0 < n) {t : ℝ} (ht : 0 ≤ t) :
    uAiry n t = -betaTip * (√(3 * t) * (n ^ ((1 : ℝ) / 6)) - xiStar * (n ^ ((1 : ℝ) / 6)) ^ 4) := by
  have hm : 0 < n ^ ((1 : ℝ) / 6) := Real.rpow_pos_of_pos hn _
  unfold uAiry
  rw [Real.sqrt_div (by linarith) n, sqrt_eq_cube hn, rpow_two_thirds_eq hn]
  field_simp

/-- `jAiry n t` in the variable `m`: `2 σ / (3 β m)`. -/
private lemma jAiry_eq_m (hn : 0 < n) {t : ℝ} (ht : 0 ≤ t) :
    jAiry n t = 2 * √(3 * t) / (3 * betaTip * (n ^ ((1 : ℝ) / 6))) := by
  have hm : 0 < n ^ ((1 : ℝ) / 6) := Real.rpow_pos_of_pos hn _
  have hb := betaTip_pos
  unfold jAiry
  rw [Real.sqrt_div (by linarith) n, sqrt_eq_cube hn, rpow_third_eq hn]
  field_simp

end SixthRoot

/-! ### The algebraic core -/

/-- Core estimate: with `δ = m - m'`, `D = m^6 - m'^6`, and `|u'| ≤ R` for `u' = -β(σ m' - ξ m'^4)`,
`u - u' = β ξ D / (2 m^2) + O(1/m^6)` for `u = -β(σ m - ξ m^4)`. -/
private lemma core_u_bound {m m' σ ξ β R : ℝ} (hm1 : 1 ≤ m) (hm'0 : 0 < m') (hmm' : m' ≤ m)
    (hhalf : m / 2 ≤ m') (hξ : 0 < ξ) (hβ : 0 < β)
    (hR : |-β * (σ * m' - ξ * m' ^ 4)| ≤ R) :
    |(-β * (σ * m - ξ * m ^ 4)) - (-β * (σ * m' - ξ * m' ^ 4)) - β * ξ * (m ^ 6 - m' ^ 6) / (2 * m ^ 2)| ≤
      (9 / 2 * β * ξ * (m ^ 6 - m' ^ 6) ^ 2 + 2 * (m ^ 6 - m' ^ 6) * R) / m ^ 6 := by
  have hm0 : 0 < m := by linarith
  set δ : ℝ := m - m' with hδ
  have hδ0 : 0 ≤ δ := sub_nonneg.mpr hmm'
  set D : ℝ := m ^ 6 - m' ^ 6 with hD
  set S : ℝ := m ^ 5 + m ^ 4 * m' + m ^ 3 * m' ^ 2 + m ^ 2 * m' ^ 3 + m * m' ^ 4 + m' ^ 5 with hS
  set T : ℝ := m ^ 3 + m * m' ^ 2 + m ^ 2 * m' with hT
  set P : ℝ := (m ^ 4 + m ^ 3 * m' + m ^ 2 * m' ^ 2 + m * m' ^ 3 + m' ^ 4) +
    m * m' * (m ^ 2 + m * m' + m' ^ 2) + m ^ 2 * m' ^ 2 with hP
  have hDS : D = δ * S := by rw [hD, hδ, hS]; ring
  have hS1 : m ^ 5 ≤ S := by
    rw [hS]; nlinarith only [pow_pos hm0 4, pow_pos hm'0 5, mul_pos (pow_pos hm0 4) hm'0,
      mul_pos (pow_pos hm0 3) (pow_pos hm'0 2), mul_pos (pow_pos hm0 2) (pow_pos hm'0 3),
      mul_pos hm0 (pow_pos hm'0 4)]
  have hD0 : 0 ≤ D := by rw [hDS]; exact mul_nonneg hδ0 (by linarith [pow_pos hm0 5])
  have hδD : δ * m ^ 5 ≤ D := by
    rw [hDS]; exact mul_le_mul_of_nonneg_left hS1 hδ0
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  have hPle : P ≤ 9 * m ^ 4 := by
    have h1 : m' ≤ m := hmm'
    have hm'm : ∀ k : ℕ, m' ^ k ≤ m ^ k := fun k => pow_le_pow_left₀ hm'0.le h1 k
    have a1 : m ^ 3 * m' ≤ m ^ 4 := by nlinarith only [pow_pos hm0 3, h1]
    have a2 : m ^ 2 * m' ^ 2 ≤ m ^ 4 := by
      have := hm'm 2; nlinarith only [pow_pos hm0 2, this]
    have a3 : m * m' ^ 3 ≤ m ^ 4 := by
      have := hm'm 3; nlinarith only [hm0, this]
    have a4 : m' ^ 4 ≤ m ^ 4 := hm'm 4
    have b1 : m * m' * m ^ 2 ≤ m ^ 4 := by nlinarith only [pow_pos hm0 3, h1]
    have b2 : m * m' * (m * m') ≤ m ^ 4 := by
      have := hm'm 2; nlinarith only [pow_pos hm0 2, this]
    have b3 : m * m' * m' ^ 2 ≤ m ^ 4 := by
      have := hm'm 3; nlinarith only [hm0, this]
    have b4 : m ^ 2 * m' ^ 2 ≤ m ^ 4 := a2
    rw [hP]; nlinarith only [a1, a2, a3, a4, b1, b2, b3, b4]
  -- the identity `2 m² δ T - D = δ² P`
  have hid1 : 2 * m ^ 2 * δ * T - D = δ ^ 2 * P := by
    rw [hD, hδ, hT, hP]; ring
  -- `u - u' = β δ (ξ T - (σ - ξ m'^3))`
  have hid2 : (-β * (σ * m - ξ * m ^ 4)) - (-β * (σ * m' - ξ * m' ^ 4)) =
      β * δ * (ξ * T - (σ - ξ * m' ^ 3)) := by
    rw [hδ, hT]; ring
  set Y : ℝ := δ * T - D / (2 * m ^ 2) with hY
  have hY_eq : Y = δ ^ 2 * P / (2 * m ^ 2) := by
    rw [hY]; field_simp; linarith [hid1]
  have hY0 : 0 ≤ Y := by rw [hY_eq]; positivity
  have hYle : Y ≤ 9 / 2 * δ ^ 2 * m ^ 2 := by
    rw [hY_eq, div_le_iff₀ (by positivity)]
    nlinarith only [mul_le_mul_of_nonneg_left hPle (sq_nonneg δ), pow_pos hm0 2, sq_nonneg δ,
      hPle, mul_nonneg (sq_nonneg δ) (pow_pos hm0 2).le]
  set Z : ℝ := σ - ξ * m' ^ 3 with hZ
  have hX : (-β * (σ * m - ξ * m ^ 4)) - (-β * (σ * m' - ξ * m' ^ 4)) -
      β * ξ * D / (2 * m ^ 2) = β * ξ * Y - β * δ * Z := by
    rw [hid2, hY]; field_simp; ring
  have hZb : β * m' * |Z| ≤ R := by
    have : -β * (σ * m' - ξ * m' ^ 4) = -(β * m' * Z) := by rw [hZ]; ring
    rw [this, abs_neg, abs_mul, abs_mul, abs_of_pos hβ, abs_of_pos hm'0] at hR
    exact hR
  rw [hX, le_div_iff₀ (by positivity)]
  have hm6 : 0 < m ^ 6 := pow_pos hm0 6
  -- first term
  have t1 : β * ξ * Y * m ^ 6 ≤ β * ξ * (9 / 2 * D ^ 2) := by
    have h1 : Y * m ^ 6 ≤ 9 / 2 * (δ * m ^ 5) ^ 2 := by
      have : (δ * m ^ 5) ^ 2 = δ ^ 2 * m ^ 10 := by ring
      rw [this]
      have hm8 : m ^ 8 ≤ m ^ 10 := pow_le_pow_right₀ hm1 (by norm_num)
      calc Y * m ^ 6 ≤ 9 / 2 * δ ^ 2 * m ^ 2 * m ^ 6 :=
            mul_le_mul_of_nonneg_right hYle hm6.le
        _ = 9 / 2 * δ ^ 2 * m ^ 8 := by ring
        _ ≤ 9 / 2 * δ ^ 2 * m ^ 10 := by
            apply mul_le_mul_of_nonneg_left hm8; positivity
        _ = 9 / 2 * (δ ^ 2 * m ^ 10) := by ring
    have h2 : (δ * m ^ 5) ^ 2 ≤ D ^ 2 :=
      pow_le_pow_left₀ (by positivity) hδD 2
    have hβξ : 0 ≤ β * ξ := by positivity
    calc β * ξ * Y * m ^ 6 = β * ξ * (Y * m ^ 6) := by ring
      _ ≤ β * ξ * (9 / 2 * (δ * m ^ 5) ^ 2) := mul_le_mul_of_nonneg_left h1 hβξ
      _ ≤ β * ξ * (9 / 2 * D ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ hβξ
          linarith
  -- second term
  have t2 : |β * δ * Z| * m ^ 6 ≤ 2 * D * R := by
    have hmm2 : m ≤ 2 * m' := by linarith
    have hZ' : β * m * |Z| ≤ 2 * R := by
      have : β * m * |Z| ≤ β * (2 * m') * |Z| := by
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        exact mul_le_mul_of_nonneg_left hmm2 hβ.le
      nlinarith only [this, hZb]
    have habs : |β * δ * Z| = δ * (β * |Z|) := by
      rw [abs_mul, abs_mul, abs_of_pos hβ, abs_of_nonneg hδ0]; ring
    rw [habs]
    calc δ * (β * |Z|) * m ^ 6 = (δ * m ^ 5) * (β * m * |Z|) := by ring
      _ ≤ D * (2 * R) := by
          apply mul_le_mul hδD hZ' (by positivity) hD0
      _ = 2 * D * R := by ring
  calc |β * ξ * Y - β * δ * Z| * m ^ 6 ≤ (|β * ξ * Y| + |β * δ * Z|) * m ^ 6 :=
        mul_le_mul_of_nonneg_right (abs_sub _ _) hm6.le
    _ = β * ξ * Y * m ^ 6 + |β * δ * Z| * m ^ 6 := by
        rw [abs_of_nonneg (by positivity : 0 ≤ β * ξ * Y)]; ring
    _ ≤ β * ξ * (9 / 2 * D ^ 2) + 2 * D * R := add_le_add t1 t2
    _ = 9 / 2 * β * ξ * D ^ 2 + 2 * D * R := by ring

/-! ### (c): the chart `u_n` and the Jacobian `J_n` -/

/-- **`pmix:rebase` (c), the chart.** On every window `|u_{n'}(t)| ≤ R` (`n' = n - 12 r`),
`u_n(t) - u_{n'}(t) = 6 β r ξ_* / n^{1/3} + O_R(n^{-1})`, uniformly in `t > 0`. -/
theorem rebase_c_u (R : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    ∃ C n₀ : ℝ, 0 < C ∧ 1 ≤ n₀ ∧ ∀ n : ℝ, n₀ ≤ n → ∀ t : ℝ, 0 < t →
      |uAiry (n - 12 * r) t| ≤ R →
        |uAiry n t - uAiry (n - 12 * r) t - 6 * betaTip * r * xiStar / n ^ ((1 : ℝ) / 3)| ≤ C / n := by
  have hβ := betaTip_pos
  have hξ := xiStar_pos
  refine ⟨9 / 2 * betaTip * xiStar * (12 * r) ^ 2 + 2 * (12 * r) * |R| + 1, max 1 (24 * r), by positivity,
    le_max_left _ _, fun n hn t ht hR => ?_⟩
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hn24 : 24 * r ≤ n := (le_max_right _ _).trans hn
  have hn0 : 0 < n := by linarith
  have hn' : 0 < n - 12 * r := by linarith
  set m : ℝ := n ^ ((1 : ℝ) / 6) with hm
  set m' : ℝ := (n - 12 * r) ^ ((1 : ℝ) / 6) with hm'
  have hm0 : 0 < m := Real.rpow_pos_of_pos hn0 _
  have hm'0 : 0 < m' := Real.rpow_pos_of_pos hn' _
  have hm6 : m ^ 6 = n := sixth_pow hn0
  have hm'6 : m' ^ 6 = n - 12 * r := sixth_pow hn'
  have hm1 : 1 ≤ m := Real.one_le_rpow hn1 (by norm_num)
  have hmm' : m' ≤ m := by
    apply Real.rpow_le_rpow hn'.le (by linarith) (by norm_num)
  have hhalf : m / 2 ≤ m' := by
    by_contra hcon
    push Not at hcon
    have h1 : m' ^ 6 < (m / 2) ^ 6 := pow_lt_pow_left₀ hcon hm'0.le (by norm_num)
    have h2 : (m / 2) ^ 6 = m ^ 6 / 64 := by ring
    rw [hm'6, h2, hm6] at h1
    linarith
  have hD : m ^ 6 - m' ^ 6 = 12 * r := by rw [hm6, hm'6]; ring
  have hu := uAiry_eq_m hn0 ht.le
  have hu' := uAiry_eq_m hn' ht.le
  rw [hu'] at hR
  have hcore := core_u_bound (σ := √(3 * t)) (ξ := xiStar) (β := betaTip) (R := |R|) hm1 hm'0 hmm' hhalf
    hξ hβ (hR.trans (le_abs_self R))
  rw [hD] at hcore
  rw [hu, hu']
  have hrep : 6 * betaTip * r * xiStar / n ^ ((1 : ℝ) / 3) =
      betaTip * xiStar * (12 * r) / (2 * m ^ 2) := by
    rw [rpow_third_eq hn0]; field_simp; ring
  rw [hrep]
  refine hcore.trans ?_
  rw [hm6]
  apply div_le_div_of_nonneg_right _ hn0.le
  linarith

/-- **`pmix:rebase` (c), the Jacobian.** `J_n(t) / J_{n'}(t) = (n'/n)^{1/6}`; hence
`|J_n(t)/J_{n'}(t) - 1| ≤ 12 r / n` for every `t > 0` (`n ≥ 24 r`, `n ≥ 1`). -/
theorem rebase_c_J {r : ℝ} (hr : 0 ≤ r) {n : ℝ} (hn1 : 1 ≤ n) (hn24 : 24 * r ≤ n)
    {t : ℝ} (ht : 0 < t) :
    |jAiry n t / jAiry (n - 12 * r) t - 1| ≤ 12 * r / n := by
  have hβ := betaTip_pos
  have hn0 : 0 < n := by linarith
  have hn' : 0 < n - 12 * r := by linarith
  set m : ℝ := n ^ ((1 : ℝ) / 6) with hm
  set m' : ℝ := (n - 12 * r) ^ ((1 : ℝ) / 6) with hm'
  have hm0 : 0 < m := Real.rpow_pos_of_pos hn0 _
  have hm'0 : 0 < m' := Real.rpow_pos_of_pos hn' _
  have hm6 : m ^ 6 = n := sixth_pow hn0
  have hm'6 : m' ^ 6 = n - 12 * r := sixth_pow hn'
  have hmm' : m' ≤ m := Real.rpow_le_rpow hn'.le (by linarith) (by norm_num)
  have hσ : 0 < √(3 * t) := Real.sqrt_pos.mpr (by linarith)
  rw [jAiry_eq_m hn0 ht.le, jAiry_eq_m hn' ht.le]
  have hratio : 2 * √(3 * t) / (3 * betaTip * m) / (2 * √(3 * t) / (3 * betaTip * m')) = m' / m := by
    field_simp
  rw [hratio]
  have hle : m' / m ≤ 1 := (div_le_one hm0).mpr hmm'
  rw [abs_sub_comm, abs_of_nonneg (by linarith)]
  have hδ : (m - m') * m ^ 5 ≤ 12 * r := by
    have hDS : m ^ 6 - m' ^ 6 = (m - m') *
        (m ^ 5 + m ^ 4 * m' + m ^ 3 * m' ^ 2 + m ^ 2 * m' ^ 3 + m * m' ^ 4 + m' ^ 5) := by ring
    have hS1 : m ^ 5 ≤ m ^ 5 + m ^ 4 * m' + m ^ 3 * m' ^ 2 + m ^ 2 * m' ^ 3 + m * m' ^ 4 + m' ^ 5 := by
      nlinarith only [pow_pos hm0 4, pow_pos hm'0 5, mul_pos (pow_pos hm0 4) hm'0,
        mul_pos (pow_pos hm0 3) (pow_pos hm'0 2), mul_pos (pow_pos hm0 2) (pow_pos hm'0 3),
        mul_pos hm0 (pow_pos hm'0 4)]
    have : (m - m') * m ^ 5 ≤ m ^ 6 - m' ^ 6 := by
      rw [hDS]; exact mul_le_mul_of_nonneg_left hS1 (sub_nonneg.mpr hmm')
    rw [hm6, hm'6] at this; linarith
  have : 1 - m' / m = (m - m') / m := by field_simp
  rw [this, div_le_div_iff₀ hm0 hn0]
  rw [← hm6]
  nlinarith only [hδ, hm0, pow_pos hm0 5]

/-! ### (b): thresholds in the rebased parameter -/

section PartB

/-- `0 ≤ n^{1/3} - (n - D)^{1/3} ≤ D / (n-D)^{2/3}` (mean value for the cube root, elementary form). -/
private lemma cube_root_sub_le {n D : ℝ} (hD : 0 ≤ D) (hnD : D < n) :
    0 ≤ n ^ ((1 : ℝ) / 3) - (n - D) ^ ((1 : ℝ) / 3) ∧
      n ^ ((1 : ℝ) / 3) - (n - D) ^ ((1 : ℝ) / 3) ≤ D / (n - D) ^ ((2 : ℝ) / 3) := by
  have hn' : 0 < n - D := by linarith
  have hn0 : 0 < n := by linarith
  set p : ℝ := n ^ ((1 : ℝ) / 3) with hp
  set q : ℝ := (n - D) ^ ((1 : ℝ) / 3) with hq
  have hp0 : 0 < p := Real.rpow_pos_of_pos hn0 _
  have hq0 : 0 < q := Real.rpow_pos_of_pos hn' _
  have hp3 : p ^ 3 = n := by rw [hp, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; norm_num
  have hq3 : q ^ 3 = n - D := by rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul hn'.le]; norm_num
  have hq2 : q ^ 2 = (n - D) ^ ((2 : ℝ) / 3) := by
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul hn'.le]; norm_num
  have hqp : q ≤ p := by
    by_contra h
    push Not at h
    have := pow_lt_pow_left₀ h hp0.le (by norm_num : 3 ≠ 0)
    rw [hp3, hq3] at this
    linarith
  refine ⟨by linarith, ?_⟩
  rw [← hq2, le_div_iff₀ (by positivity)]
  have hdiff : (p - q) * (p ^ 2 + p * q + q ^ 2) = D := by
    have : p ^ 3 - q ^ 3 = D := by rw [hp3, hq3]; ring
    nlinarith only [this]
  have : (p - q) * q ^ 2 ≤ (p - q) * (p ^ 2 + p * q + q ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hqp)
    nlinarith only [sq_nonneg p, mul_pos hp0 hq0]
  linarith

/-- **`pmix:rebase` (b)** (`Lemma PM.1`): for every fixed `z`, as `n → ∞`,
`ξ̄ n' - c_* z (n')^{1/3} = ξ̄ n - c_* z n^{1/3} - 12 ξ̄ r + O(n^{-2/3})` with `n' = n - 12 r`. -/
theorem rebase_b (z : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    ∃ C n₀ : ℝ, 0 < C ∧ 1 ≤ n₀ ∧ ∀ n : ℝ, n₀ ≤ n →
      |(xiBar * (n - 12 * r) - cStar * z * (n - 12 * r) ^ ((1 : ℝ) / 3)) -
          (xiBar * n - cStar * z * n ^ ((1 : ℝ) / 3) - 12 * xiBar * r)| ≤ C * n ^ (-((2 : ℝ) / 3)) := by
  refine ⟨|cStar * z| * 12 * r * 2 + 1, max 1 (24 * r), by positivity, le_max_left _ _, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hn24 : 24 * r ≤ n := (le_max_right _ _).trans hn
  have hn0 : 0 < n := by linarith
  have hD : 12 * r < n := by linarith
  obtain ⟨h0, h1⟩ := cube_root_sub_le (n := n) (D := 12 * r) (by linarith) hD
  have heq : (xiBar * (n - 12 * r) - cStar * z * (n - 12 * r) ^ ((1 : ℝ) / 3)) -
      (xiBar * n - cStar * z * n ^ ((1 : ℝ) / 3) - 12 * xiBar * r) =
      cStar * z * (n ^ ((1 : ℝ) / 3) - (n - 12 * r) ^ ((1 : ℝ) / 3)) := by ring
  rw [heq, abs_mul]
  -- `(n - 12 r)^{2/3} ≥ (n/2)^{2/3} ≥ n^{2/3}/2`
  have hhalf : n / 2 ≤ n - 12 * r := by linarith
  have hr23 : n ^ ((2 : ℝ) / 3) / 2 ≤ (n - 12 * r) ^ ((2 : ℝ) / 3) := by
    have hmono : (n / 2) ^ ((2 : ℝ) / 3) ≤ (n - 12 * r) ^ ((2 : ℝ) / 3) :=
      Real.rpow_le_rpow (by linarith) hhalf (by norm_num)
    have hsplit : (n / 2) ^ ((2 : ℝ) / 3) = n ^ ((2 : ℝ) / 3) / 2 ^ ((2 : ℝ) / 3) := by
      rw [Real.div_rpow hn0.le (by norm_num)]
    have h2 : (2 : ℝ) ^ ((2 : ℝ) / 3) ≤ 2 := by
      calc (2 : ℝ) ^ ((2 : ℝ) / 3) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    have hpos : 0 < n ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hn0 _
    have : n ^ ((2 : ℝ) / 3) / 2 ≤ n ^ ((2 : ℝ) / 3) / 2 ^ ((2 : ℝ) / 3) :=
      div_le_div_of_nonneg_left hpos.le (by positivity) h2
    linarith
  have hpos23 : 0 < n ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hn0 _
  have hbound : n ^ ((1 : ℝ) / 3) - (n - 12 * r) ^ ((1 : ℝ) / 3) ≤ 24 * r * n ^ (-((2 : ℝ) / 3)) := by
    refine h1.trans ?_
    have hh : 0 < n ^ ((2 : ℝ) / 3) / 2 := by positivity
    calc 12 * r / (n - 12 * r) ^ ((2 : ℝ) / 3) ≤ 12 * r / (n ^ ((2 : ℝ) / 3) / 2) :=
          div_le_div_of_nonneg_left (by linarith) hh hr23
      _ = 24 * r * n ^ (-((2 : ℝ) / 3)) := by
          rw [Real.rpow_neg hn0.le]; field_simp; ring
  rw [abs_of_nonneg h0]
  calc |cStar * z| * (n ^ ((1 : ℝ) / 3) - (n - 12 * r) ^ ((1 : ℝ) / 3))
      ≤ |cStar * z| * (24 * r * n ^ (-((2 : ℝ) / 3))) :=
        mul_le_mul_of_nonneg_left hbound (abs_nonneg _)
    _ ≤ (|cStar * z| * 12 * r * 2 + 1) * n ^ (-((2 : ℝ) / 3)) := by
        have : 0 < n ^ (-((2 : ℝ) / 3)) := Real.rpow_pos_of_pos hn0 _
        nlinarith only [this, abs_nonneg (cStar * z)]

/-- **`pmix:rebase` (b)**, offsets: a bounded offset from the site `ξ̄ n - c_* z n^{1/3}` is a bounded offset
from `ξ̄ n' - c_* z (n')^{1/3}`, `R'_off = R_off + 12 ξ̄ r + 1`, for all large `n`. -/
theorem rebase_b_offset (z R : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    ∃ n₀ : ℝ, ∀ n : ℝ, n₀ ≤ n → ∀ x : ℝ,
      |x - (xiBar * n - cStar * z * n ^ ((1 : ℝ) / 3))| ≤ R →
        |x - (xiBar * (n - 12 * r) - cStar * z * (n - 12 * r) ^ ((1 : ℝ) / 3))| ≤
          R + 12 * xiBar * r + 1 := by
  obtain ⟨C, n₁, hC, hn₁, hb⟩ := rebase_b z hr
  have hlim : Tendsto (fun n : ℝ => C * n ^ (-((2 : ℝ) / 3))) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).const_mul C
    simpa using this
  obtain ⟨n₂, hn₂⟩ := (hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).exists_forall_of_atTop
  refine ⟨max n₁ n₂, fun n hn x hx => ?_⟩
  have h1 := hb n ((le_max_left _ _).trans hn)
  have h2 := hn₂ n ((le_max_right _ _).trans hn)
  have hxi : 0 ≤ xiBar := by unfold xiBar; have := xiStar_pos; positivity
  have : x - (xiBar * (n - 12 * r) - cStar * z * (n - 12 * r) ^ ((1 : ℝ) / 3)) =
      (x - (xiBar * n - cStar * z * n ^ ((1 : ℝ) / 3))) + 12 * xiBar * r -
        ((xiBar * (n - 12 * r) - cStar * z * (n - 12 * r) ^ ((1 : ℝ) / 3)) -
          (xiBar * n - cStar * z * n ^ ((1 : ℝ) / 3) - 12 * xiBar * r)) := by ring
  rw [this]
  calc _ ≤ |(x - (xiBar * n - cStar * z * n ^ ((1 : ℝ) / 3))) + 12 * xiBar * r| +
        |(xiBar * (n - 12 * r) - cStar * z * (n - 12 * r) ^ ((1 : ℝ) / 3)) -
          (xiBar * n - cStar * z * n ^ ((1 : ℝ) / 3) - 12 * xiBar * r)| := abs_sub _ _
    _ ≤ (|x - (xiBar * n - cStar * z * n ^ ((1 : ℝ) / 3))| + |12 * xiBar * r|) + 1 := by
        gcongr
        · exact abs_add_le _ _
        · linarith
    _ ≤ R + 12 * xiBar * r + 1 := by
        rw [abs_of_nonneg (by positivity : 0 ≤ 12 * xiBar * r)]
        linarith

end PartB

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.rebase_b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rebase_b

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.rebase_b_offset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rebase_b_offset

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.rebase_c_u' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rebase_c_u

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.rebase_c_J' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rebase_c_J

/-! ### (c): the reverse window and the inverse Jacobian ratio -/

/-- **Reverse window transfer.** If `|u_n(t)| ≤ R` then `|u_{n'}(t)| ≤ R + 1` for all large `n` (`n' = n - 12 r`):
`u_{n'} = (m'/m) u_n - β ξ_* m' (m^3 - m'^3)` and `m' (m^3 - m'^3) ≤ 12 r / m^2`. -/
theorem rebase_window_rev (R : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    ∃ n₀ : ℝ, 1 ≤ n₀ ∧ ∀ n : ℝ, n₀ ≤ n → ∀ t : ℝ, 0 < t →
      |uAiry n t| ≤ R → |uAiry (n - 12 * r) t| ≤ R + 1 := by
  have hβ := betaTip_pos
  have hξ := xiStar_pos
  set K : ℝ := 12 * betaTip * xiStar * r + 1 with hK
  have hK1 : 1 ≤ K := by
    have : 0 ≤ 12 * betaTip * xiStar * r := by positivity
    rw [hK]; linarith
  refine ⟨max (max 1 (24 * r)) (K ^ 3), (le_max_left _ _).trans (le_max_left _ _), fun n hn t ht hR => ?_⟩
  have hn1 : 1 ≤ n := (le_max_left _ _).trans ((le_max_left _ _).trans hn)
  have hn24 : 24 * r ≤ n := (le_max_right _ _).trans ((le_max_left _ _).trans hn)
  have hnK : K ^ 3 ≤ n := (le_max_right _ _).trans hn
  have hn0 : 0 < n := by linarith
  have hn' : 0 < n - 12 * r := by linarith
  set m : ℝ := n ^ ((1 : ℝ) / 6) with hm
  set m' : ℝ := (n - 12 * r) ^ ((1 : ℝ) / 6) with hm'
  have hm0 : 0 < m := Real.rpow_pos_of_pos hn0 _
  have hm'0 : 0 < m' := Real.rpow_pos_of_pos hn' _
  have hm6 : m ^ 6 = n := sixth_pow hn0
  have hm'6 : m' ^ 6 = n - 12 * r := sixth_pow hn'
  have hmm' : m' ≤ m := Real.rpow_le_rpow hn'.le (by linarith) (by norm_num)
  have hD : m ^ 6 - m' ^ 6 = 12 * r := by rw [hm6, hm'6]; ring
  have hm2K : K ≤ m ^ 2 := by
    refine le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) (by positivity) ?_
    rw [← pow_mul, show 2 * 3 = 6 by norm_num, hm6]
    exact hnK
  have hu := uAiry_eq_m hn0 ht.le
  have hu' := uAiry_eq_m hn' ht.le
  have hrel : uAiry (n - 12 * r) t =
      (m' / m) * uAiry n t - betaTip * xiStar * (m' * (m ^ 3 - m' ^ 3)) := by
    rw [hu', hu]; field_simp; ring
  have h3 : m' ^ 3 ≤ m ^ 3 := pow_le_pow_left₀ hm'0.le hmm' 3
  have hE0 : 0 ≤ m' * (m ^ 3 - m' ^ 3) := mul_nonneg hm'0.le (sub_nonneg.2 h3)
  have hEm : (m' * (m ^ 3 - m' ^ 3)) * m ^ 2 ≤ 12 * r := by
    calc (m' * (m ^ 3 - m' ^ 3)) * m ^ 2 = (m' * m ^ 2) * (m ^ 3 - m' ^ 3) := by ring
      _ ≤ m ^ 3 * (m ^ 3 - m' ^ 3) := by
          refine mul_le_mul_of_nonneg_right ?_ (sub_nonneg.2 h3)
          calc m' * m ^ 2 ≤ m * m ^ 2 := mul_le_mul_of_nonneg_right hmm' (sq_nonneg m)
            _ = m ^ 3 := by ring
      _ ≤ (m ^ 3 + m' ^ 3) * (m ^ 3 - m' ^ 3) := by
          refine mul_le_mul_of_nonneg_right ?_ (sub_nonneg.2 h3)
          linarith [pow_pos hm'0 3]
      _ = m ^ 6 - m' ^ 6 := by ring
      _ = 12 * r := hD
  have hratio : m' / m ≤ 1 := (div_le_one hm0).mpr hmm'
  have hratio0 : 0 ≤ m' / m := by positivity
  have hE : betaTip * xiStar * (m' * (m ^ 3 - m' ^ 3)) ≤ 1 := by
    have hm2 : 0 < m ^ 2 := by positivity
    have h1 : m' * (m ^ 3 - m' ^ 3) ≤ 12 * r / m ^ 2 := by
      rw [le_div_iff₀ hm2]; exact hEm
    calc betaTip * xiStar * (m' * (m ^ 3 - m' ^ 3)) ≤ betaTip * xiStar * (12 * r / m ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (12 * betaTip * xiStar * r) / m ^ 2 := by ring
      _ ≤ 1 := by
          rw [div_le_one hm2]; linarith
  rw [hrel]
  calc |(m' / m) * uAiry n t - betaTip * xiStar * (m' * (m ^ 3 - m' ^ 3))|
      ≤ |(m' / m) * uAiry n t| + |betaTip * xiStar * (m' * (m ^ 3 - m' ^ 3))| := abs_sub _ _
    _ ≤ R + 1 := by
        rw [abs_mul, abs_of_nonneg hratio0, abs_of_nonneg (by positivity :
          0 ≤ betaTip * xiStar * (m' * (m ^ 3 - m' ^ 3)))]
        have : (m' / m) * |uAiry n t| ≤ |uAiry n t| := by
          calc (m' / m) * |uAiry n t| ≤ 1 * |uAiry n t| :=
                mul_le_mul_of_nonneg_right hratio (abs_nonneg _)
            _ = |uAiry n t| := one_mul _
        linarith

/-- `J_{n'}(t) / J_n(t) = (m/m')`, so `|J_{n'}/J_n - 1| ≤ 24 r / n` for `n ≥ 24 r`, `n ≥ 1`. -/
theorem rebase_c_J_inv {r : ℝ} (hr : 0 ≤ r) {n : ℝ} (hn1 : 1 ≤ n) (hn24 : 24 * r ≤ n)
    {t : ℝ} (ht : 0 < t) :
    |jAiry (n - 12 * r) t / jAiry n t - 1| ≤ 24 * r / n := by
  have hβ := betaTip_pos
  have hn0 : 0 < n := by linarith
  have hn' : 0 < n - 12 * r := by linarith
  have hJ := rebase_c_J hr hn1 hn24 ht
  have hJpos : ∀ c : ℝ, 0 < c → 0 < jAiry c t := fun c hc => by
    unfold jAiry
    have : 0 < √(3 * t / c) := Real.sqrt_pos.mpr (by positivity)
    have := Real.rpow_pos_of_pos hc ((1 : ℝ) / 3)
    positivity
  set ρ : ℝ := jAiry n t / jAiry (n - 12 * r) t with hρ
  have hρ0 : 0 < ρ := div_pos (hJpos n hn0) (hJpos _ hn')
  have hsmall : 12 * r / n ≤ 1 / 2 := by
    rw [div_le_iff₀ hn0]; linarith
  have hρhalf : 1 / 2 ≤ ρ := by
    have := (abs_le.1 hJ).1
    linarith
  have hinv : jAiry (n - 12 * r) t / jAiry n t = ρ⁻¹ := by
    rw [hρ, inv_div]
  rw [hinv]
  have h1 : |ρ⁻¹ - 1| = |1 - ρ| / ρ := by
    rw [show ρ⁻¹ - 1 = (1 - ρ) / ρ by field_simp, abs_div, abs_of_pos hρ0]
  rw [h1, div_le_iff₀ hρ0, abs_sub_comm]
  calc |ρ - 1| ≤ 12 * r / n := hJ
    _ ≤ 24 * r / n * ρ := by
        have : 12 * r / n = 24 * r / n * (1 / 2) := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_left hρhalf (by positivity)

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.rebase_window_rev' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rebase_window_rev

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.rebase_c_J_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rebase_c_J_inv

end FormalResearch.ModularBootstrap.Mixtures
