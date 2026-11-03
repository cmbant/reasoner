module

public import FormalResearch.FourQubitEntropy.RenyiFullDefs
public import FormalResearch.FourQubitEntropy.RenyiFullHsProof

/-!
# Critical-locus variance profile `prop:fqe-critical-variance`: the real-algebra core

Paper E, `renyi_compatibility.tex`, `prop:fqe-critical-variance` (RF), and its use in the equality
classification of `thm:fqe-quadratic-variance` (`quadratic_variance_certificate.tex`).

At `P = 1` the three cut spectra of a pure four-qubit state are `(1 + ε_k · g^c)/4`, `k = 1..4`
(`ε_k` the four sign vectors of product `-1`), with `g^c` signed cyclic rearrangements of the products
`m_i n_j` of two unit vectors `m, n ∈ ℝ³` (`QVEqualityBridge.lean` derives this from the critical
normal form).  This file is the real algebra on `(m, n)`, with no quantum content:

* `rp_bound`: `27 e₃(A) ≤ g(√X)` (`eq:fqe-triple-product`, from the cubic discriminant identity);
* `transfer_id`: the product transfer `eq:fqe-product-transfer-remainder`;
* `core_ineq`: `27 κ ≤ g(s)`, `κ = m₁m₂m₃n₁n₂n₃`, `s = (XY)^{1/4}`;
* `core_triple`: for the triple `(spc0, spc1, spc2) m n`: `P = 1`, `24 V = s⁴`, `F = (1 - 27κ)/2`, so
  `F ≥ (3/2)s² - s³` (RF);
* `core_equality`: `F² = 6 V` forces `s ∈ {0, 1}` and the spectra are an HS triple (`s = 0`) or a
  cluster triple (`s = 1`).

Everything here is proved (no hypotheses, no `native_decide`).
-/

@[expose] public section


namespace FormalResearch.FourQubitEntropy.QVEquality

open FormalResearch.FourQubitEntropy FormalResearch.FourQubitEntropy.RenyiFull

/-! ### The scalar inequalities -/

/-- `g(t) = (1 - t)² (1 + 2t)`, so that `h(X) = g(√X)` of `eq:fqe-triple-product`. -/
def gfun (t : ℝ) : ℝ := (1 - t) ^ 2 * (1 + 2 * t)

theorem gfun_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ gfun t := by unfold gfun; positivity

/-- `eq:fqe-triple-product`: for a nonnegative triple of sum one with `X = 1 - 3 e₂`, `27 e₃ ≤ g(√X)`
(the cubic discriminant identity `4X³ - (27e₃ - 1 + 3X)² = 27 ∏(A_i - A_j)²`). -/
theorem rp_bound {a b c r : ℝ} (hs : a + b + c = 1)
    (hr : 0 ≤ r) (hX : r ^ 2 = 1 - 3 * (a * b + a * c + b * c)) :
    27 * (a * b * c) ≤ gfun r := by
  have hc' : c = 1 - a - b := by linarith
  have disc : 4 * (r ^ 2) ^ 3 - (27 * (a * b * c) - 1 + 3 * r ^ 2) ^ 2
      = 27 * ((a - b) * (b - c) * (a - c)) ^ 2 := by
    rw [hX, hc']; ring
  have key : (27 * (a * b * c) - 1 + 3 * r ^ 2) ^ 2 ≤ (2 * r ^ 3) ^ 2 := by
    nlinarith [sq_nonneg ((a - b) * (b - c) * (a - c))]
  have := abs_le_of_sq_le_sq key (by positivity)
  have h2 := le_abs_self (27 * (a * b * c) - 1 + 3 * r ^ 2)
  unfold gfun; nlinarith

/-- `eq:fqe-product-transfer-remainder`: `g(ξζ)² - g(ξ²) g(ζ²) = d {w [6q(q+2) + 2d] + d (1+2q)²}`. -/
theorem transfer_id (ξ ζ : ℝ) :
    gfun (ξ * ζ) ^ 2 - gfun (ξ ^ 2) * gfun (ζ ^ 2) =
      (ξ - ζ) ^ 2 * ((1 - ξ ^ 2) * (1 - ζ ^ 2) * (6 * (ξ * ζ) * (ξ * ζ + 2) + 2 * (ξ - ζ) ^ 2)
        + (ξ - ζ) ^ 2 * (1 + 2 * (ξ * ζ)) ^ 2) := by
  unfold gfun; ring

theorem transfer_le {ξ ζ : ℝ} (hξ : 0 ≤ ξ) (hξ1 : ξ ≤ 1) (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) :
    gfun (ξ ^ 2) * gfun (ζ ^ 2) ≤ gfun (ξ * ζ) ^ 2 := by
  have h := transfer_id ξ ζ
  have hw : 0 ≤ (1 - ξ ^ 2) * (1 - ζ ^ 2) :=
    mul_nonneg (by nlinarith) (by nlinarith)
  have : 0 ≤ (ξ - ζ) ^ 2 * ((1 - ξ ^ 2) * (1 - ζ ^ 2) * (6 * (ξ * ζ) * (ξ * ζ + 2) + 2 * (ξ - ζ) ^ 2)
        + (ξ - ζ) ^ 2 * (1 + 2 * (ξ * ζ)) ^ 2) := by
    have hq : 0 ≤ ξ * ζ := mul_nonneg hξ hζ
    positivity
  linarith

/-- `X = 1 - 3 e₂(A)` lies in `[0, 1]` for a nonnegative triple of sum one. -/
theorem X_bounds {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hs : a + b + c = 1) :
    0 ≤ 1 - 3 * (a * b + a * c + b * c) ∧ 1 - 3 * (a * b + a * c + b * c) ≤ 1 := by
  constructor
  · nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
  · nlinarith [mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc]

/-- **The core inequality** `27 κ ≤ g(ξζ)` with `κ² = e₃(A) e₃(B)`, `ξ⁴ = X`, `ζ⁴ = Y`. -/
theorem core_ineq {A0 A1 A2 B0 B1 B2 κ ξ ζ : ℝ}
    (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2) (hAs : A0 + A1 + A2 = 1)
    (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2) (hBs : B0 + B1 + B2 = 1)
    (hκ : κ ^ 2 = A0 * A1 * A2 * (B0 * B1 * B2))
    (hξ : 0 ≤ ξ) (hξ4 : ξ ^ 4 = 1 - 3 * (A0 * A1 + A0 * A2 + A1 * A2))
    (hζ : 0 ≤ ζ) (hζ4 : ζ ^ 4 = 1 - 3 * (B0 * B1 + B0 * B2 + B1 * B2)) :
    27 * κ ≤ gfun (ξ * ζ) := by
  have hXb := X_bounds hA0 hA1 hA2 hAs
  have hYb := X_bounds hB0 hB1 hB2 hBs
  have hξ1 : ξ ≤ 1 := by
    by_contra h; push Not at h
    have : 1 < ξ ^ 4 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) h.le 4, one_lt_pow₀ h (by norm_num : (4:ℕ) ≠ 0)]
    linarith [hXb.2]
  have hζ1 : ζ ≤ 1 := by
    by_contra h; push Not at h
    have : 1 < ζ ^ 4 := by nlinarith [one_lt_pow₀ h (by norm_num : (4:ℕ) ≠ 0)]
    linarith [hYb.2]
  have h1 := rp_bound (r := ξ ^ 2) hAs (by positivity) (by rw [← hξ4]; ring)
  have h2 := rp_bound (r := ζ ^ 2) hBs (by positivity) (by rw [← hζ4]; ring)
  have e3A : 0 ≤ A0 * A1 * A2 := by positivity
  have e3B : 0 ≤ B0 * B1 * B2 := by positivity
  have hgξ := gfun_nonneg (sq_nonneg ξ)
  have hgζ := gfun_nonneg (sq_nonneg ζ)
  have hq : 0 ≤ ξ * ζ := mul_nonneg hξ hζ
  have hg := gfun_nonneg hq
  have hT := transfer_le hξ hξ1 hζ hζ1
  have hprod : (27 * κ) ^ 2 ≤ gfun (ξ * ζ) ^ 2 := by
    have : (27 * κ) ^ 2 = (27 * (A0 * A1 * A2)) * (27 * (B0 * B1 * B2)) := by
      rw [mul_pow, hκ]; ring
    rw [this]
    calc (27 * (A0 * A1 * A2)) * (27 * (B0 * B1 * B2))
        ≤ gfun (ξ ^ 2) * gfun (ζ ^ 2) :=
          mul_le_mul h1 h2 (by positivity) hgξ
      _ ≤ _ := hT
  have := abs_le_of_sq_le_sq hprod hg
  exact (le_abs_self _).trans this

/-! ### The spectra `(1 + ε · g)/4` -/

/-- The spectrum `(1 + ε_k · g)/4` for the four sign vectors `ε_k` of product `-1`,
`ε = (+,+,-), (+,-,+), (-,+,+), (-,-,-)`. -/
noncomputable def specG (a b c : ℝ) : Fin 4 → ℝ :=
  ![(1 + a + b - c) / 4, (1 + a - b + c) / 4, (1 - a + b + c) / 4, (1 - a - b - c) / 4]

theorem specG_sum (a b c : ℝ) : ∑ i, specG a b c i = 1 := by
  simp [specG, Fin.sum_univ_four]; ring

theorem pur_specG (a b c : ℝ) : pur (specG a b c) = (1 + a ^ 2 + b ^ 2 + c ^ 2) / 4 := by
  simp [pur, specG, Fin.sum_univ_four]; ring

theorem cub_specG (a b c : ℝ) :
    cub (specG a b c) = (1 + 3 * (a ^ 2 + b ^ 2 + c ^ 2) - 6 * (a * b * c)) / 16 := by
  simp [cub, specG, Fin.sum_univ_four]; ring

/-- The three cut spectra attached to unit vectors `m, n ∈ ℝ³` (`g^c_a = ± m_{a+c} n_a`). -/
noncomputable def spc0 (m n : Fin 3 → ℝ) : Fin 4 → ℝ := specG (m 0 * n 0) (m 1 * n 1) (-(m 2 * n 2))
noncomputable def spc1 (m n : Fin 3 → ℝ) : Fin 4 → ℝ := specG (-(m 2 * n 1)) (m 0 * n 2) (m 1 * n 0)
noncomputable def spc2 (m n : Fin 3 → ℝ) : Fin 4 → ℝ := specG (m 1 * n 2) (m 2 * n 0) (-(m 0 * n 1))

/-- `κ = m₀m₁m₂n₀n₁n₂`. -/
noncomputable def kap (m n : Fin 3 → ℝ) : ℝ := m 0 * m 1 * m 2 * (n 0 * n 1 * n 2)

theorem sum_u (A0 A1 A2 B0 B1 B2 : ℝ) (hA : A0 + A1 + A2 = 1) (hB : B0 + B1 + B2 = 1) :
    (A0 * B0 + A1 * B1 + A2 * B2) + (A2 * B1 + A0 * B2 + A1 * B0) + (A1 * B2 + A2 * B0 + A0 * B1) = 1 := by
  have : (A0 + A1 + A2) * (B0 + B1 + B2) = 1 := by rw [hA, hB]; ring
  linarith

theorem sum_u_sq (A0 A1 A2 B0 B1 B2 : ℝ) (hA : A0 + A1 + A2 = 1) (hB : B0 + B1 + B2 = 1) :
    (A0 * B0 + A1 * B1 + A2 * B2) ^ 2 + (A2 * B1 + A0 * B2 + A1 * B0) ^ 2
        + (A1 * B2 + A2 * B0 + A0 * B1) ^ 2 =
      (1 + 2 * ((1 - 3 * (A0 * A1 + A0 * A2 + A1 * A2)) * (1 - 3 * (B0 * B1 + B0 * B2 + B1 * B2)))) / 3 := by
  have h2 : A2 = 1 - A0 - A1 := by linarith
  have h3 : B2 = 1 - B0 - B1 := by linarith
  subst h2; subst h3; ring

section Triple

variable (m n : Fin 3 → ℝ)

theorem Pm_core (hm : m 0 ^ 2 + m 1 ^ 2 + m 2 ^ 2 = 1) (hn : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1) :
    RenyiFull.Pm (spc0 m n) (spc1 m n) (spc2 m n) = 1 := by
  unfold RenyiFull.Pm spc0 spc1 spc2
  rw [pur_specG, pur_specG, pur_specG]
  have := sum_u (m 0 ^ 2) (m 1 ^ 2) (m 2 ^ 2) (n 0 ^ 2) (n 1 ^ 2) (n 2 ^ 2) hm hn
  nlinarith [this]

theorem Fm_core (hm : m 0 ^ 2 + m 1 ^ 2 + m 2 ^ 2 = 1) (hn : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1) :
    RenyiFull.Fm (spc0 m n) (spc1 m n) (spc2 m n) = (1 - 27 * kap m n) / 2 := by
  have hP := Pm_core m n hm hn
  unfold RenyiFull.Fm RenyiFull.Tm
  rw [hP]
  unfold spc0 spc1 spc2 kap
  rw [cub_specG, cub_specG, cub_specG]
  have := sum_u (m 0 ^ 2) (m 1 ^ 2) (m 2 ^ 2) (n 0 ^ 2) (n 1 ^ 2) (n 2 ^ 2) hm hn
  nlinarith [this]

theorem Vm_core (hm : m 0 ^ 2 + m 1 ^ 2 + m 2 ^ 2 = 1) (hn : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1) :
    24 * RenyiFull.Vm (spc0 m n) (spc1 m n) (spc2 m n) =
      (1 - 3 * (m 0 ^ 2 * m 1 ^ 2 + m 0 ^ 2 * m 2 ^ 2 + m 1 ^ 2 * m 2 ^ 2)) *
        (1 - 3 * (n 0 ^ 2 * n 1 ^ 2 + n 0 ^ 2 * n 2 ^ 2 + n 1 ^ 2 * n 2 ^ 2)) := by
  have hP := Pm_core m n hm hn
  unfold RenyiFull.Vm
  rw [hP]
  unfold spc0 spc1 spc2
  rw [pur_specG, pur_specG, pur_specG]
  have h1 := sum_u (m 0 ^ 2) (m 1 ^ 2) (m 2 ^ 2) (n 0 ^ 2) (n 1 ^ 2) (n 2 ^ 2) hm hn
  have h2 := sum_u_sq (m 0 ^ 2) (m 1 ^ 2) (m 2 ^ 2) (n 0 ^ 2) (n 1 ^ 2) (n 2 ^ 2) hm hn
  nlinarith [h1, h2]

end Triple

section Triple2

variable (m n : Fin 3 → ℝ)

theorem kap_sq (m n : Fin 3 → ℝ) :
    kap m n ^ 2 = (m 0 ^ 2 * m 1 ^ 2 * m 2 ^ 2) * (n 0 ^ 2 * n 1 ^ 2 * n 2 ^ 2) := by
  unfold kap; ring

/-- Existence of the fourth roots `ξ, ζ ∈ [0,1]` of `X, Y`. -/
theorem exists_xi (hm : m 0 ^ 2 + m 1 ^ 2 + m 2 ^ 2 = 1) :
    ∃ ξ : ℝ, 0 ≤ ξ ∧ ξ ≤ 1 ∧
      ξ ^ 4 = 1 - 3 * (m 0 ^ 2 * m 1 ^ 2 + m 0 ^ 2 * m 2 ^ 2 + m 1 ^ 2 * m 2 ^ 2) := by
  have hb := X_bounds (sq_nonneg (m 0)) (sq_nonneg (m 1)) (sq_nonneg (m 2)) hm
  refine ⟨Real.sqrt (Real.sqrt (1 - 3 * (m 0 ^ 2 * m 1 ^ 2 + m 0 ^ 2 * m 2 ^ 2 + m 1 ^ 2 * m 2 ^ 2))),
    Real.sqrt_nonneg _, ?_, ?_⟩
  · rw [Real.sqrt_le_one]; rw [Real.sqrt_le_one]; exact hb.2
  · rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt hb.1]

/-- **`prop:fqe-critical-variance` for the core triple** (RF): `P = 1`, `24 V = s⁴`, `s = ξ ζ ∈ [0,1]`,
`F = (1 - 27κ)/2 ≥ (3/2)s² - s³`. -/
theorem core_triple (hm : m 0 ^ 2 + m 1 ^ 2 + m 2 ^ 2 = 1) (hn : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1) :
    ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ RenyiFull.Pm (spc0 m n) (spc1 m n) (spc2 m n) = 1 ∧
      24 * RenyiFull.Vm (spc0 m n) (spc1 m n) (spc2 m n) = s ^ 4 ∧
      RenyiFull.Fm (spc0 m n) (spc1 m n) (spc2 m n) = (1 - 27 * kap m n) / 2 ∧
      3 / 2 * s ^ 2 - s ^ 3 ≤ RenyiFull.Fm (spc0 m n) (spc1 m n) (spc2 m n) := by
  obtain ⟨ξ, hξ, hξ1, hξ4⟩ := exists_xi m hm
  obtain ⟨ζ, hζ, hζ1, hζ4⟩ := exists_xi n hn
  have hci := core_ineq (κ := kap m n) (sq_nonneg (m 0)) (sq_nonneg (m 1)) (sq_nonneg (m 2)) hm
    (sq_nonneg (n 0)) (sq_nonneg (n 1)) (sq_nonneg (n 2)) hn (kap_sq m n) hξ hξ4 hζ hζ4
  have hF := Fm_core m n hm hn
  refine ⟨ξ * ζ, mul_nonneg hξ hζ, by nlinarith, Pm_core m n hm hn, ?_, hF, ?_⟩
  · rw [Vm_core m n hm hn, ← hξ4, ← hζ4]; ring
  · rw [hF]; unfold gfun at hci; nlinarith

end Triple2

/-! ### Endpoint spectra -/

theorem specG_zero : UniformFour (specG 0 0 0) := by
  intro i; fin_cases i <;> simp [specG]

theorem specG_hs {a b c : ℝ} (ha : a ^ 2 = 1 / 9) (hb : b ^ 2 = 1 / 9) (hc : c ^ 2 = 1 / 9)
    (habc : a * b * c = -(1 / 27)) : IsHsPerm (specG a b c) := by
  have e : ∀ x : ℝ, x ^ 2 = 1 / 9 → x = 1 / 3 ∨ x = -(1 / 3) := fun x hx => by
    have : x ^ 2 = (1 / 3) ^ 2 := by rw [hx]; norm_num
    exact sq_eq_sq_iff_eq_or_eq_neg.mp this
  rcases e a ha with rfl | rfl <;> rcases e b hb with rfl | rfl <;> rcases e c hc with rfl | rfl
  · exfalso; norm_num at habc
  · exact isHsPerm_of_pattern 0 (by simp [specG]; norm_num)
      (fun j hj => by fin_cases j <;> simp [specG] at hj ⊢ <;> norm_num)
  · exact isHsPerm_of_pattern 1 (by simp [specG]; norm_num)
      (fun j hj => by fin_cases j <;> simp [specG] at hj ⊢ <;> norm_num)
  · exfalso; norm_num at habc
  · exact isHsPerm_of_pattern 2 (by simp [specG]; norm_num)
      (fun j hj => by fin_cases j <;> simp [specG] at hj ⊢ <;> norm_num)
  · exfalso; norm_num at habc
  · exfalso; norm_num at habc
  · exact isHsPerm_of_pattern 3 (by simp [specG]; norm_num)
      (fun j hj => by fin_cases j <;> simp [specG] at hj ⊢ <;> norm_num)

/-- A spectrum `specG a b c` whose coordinate squares are `0` or `1` and sum to at most `1` is uniform-four
(`u = 0`) or uniform-two (`u = 1`). -/
theorem specG_unit {a b c : ℝ} (ha : a ^ 2 = 0 ∨ a ^ 2 = 1) (hb : b ^ 2 = 0 ∨ b ^ 2 = 1)
    (hc : c ^ 2 = 0 ∨ c ^ 2 = 1) (hle : a ^ 2 + b ^ 2 + c ^ 2 ≤ 1) :
    (a ^ 2 + b ^ 2 + c ^ 2 = 0 ∧ UniformFour (specG a b c)) ∨
      (a ^ 2 + b ^ 2 + c ^ 2 = 1 ∧ UniformTwo (specG a b c)) := by
  have z : ∀ x : ℝ, x ^ 2 = 0 → x = 0 := fun x hx => pow_eq_zero_iff (two_ne_zero) |>.mp hx
  have o : ∀ x : ℝ, x ^ 2 = 1 → x = 1 ∨ x = -1 := fun x hx => by
    have : x ^ 2 = 1 ^ 2 := by rw [hx]; norm_num
    exact sq_eq_sq_iff_eq_or_eq_neg.mp this
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc
  · left
    refine ⟨by rw [ha, hb, hc]; norm_num, ?_⟩
    rw [z a ha, z b hb, z c hc]; exact specG_zero
  · right
    refine ⟨by rw [ha, hb, hc]; norm_num, ?_⟩
    rw [z a ha, z b hb]
    rcases o c hc with rfl | rfl
    · exact ⟨1, 2, by decide, by simp [specG]; norm_num, by simp [specG]; norm_num,
        fun k hk1 hk2 => by fin_cases k <;> simp [specG] at hk1 hk2 ⊢⟩
    · exact ⟨0, 3, by decide, by simp [specG]; norm_num, by simp [specG]; norm_num,
        fun k hk1 hk2 => by fin_cases k <;> simp [specG] at hk1 hk2 ⊢⟩
  · right
    refine ⟨by rw [ha, hb, hc]; norm_num, ?_⟩
    rw [z a ha, z c hc]
    rcases o b hb with rfl | rfl
    · exact ⟨0, 2, by decide, by simp [specG]; norm_num, by simp [specG]; norm_num,
        fun k hk1 hk2 => by fin_cases k <;> simp [specG] at hk1 hk2 ⊢⟩
    · exact ⟨1, 3, by decide, by simp [specG]; norm_num, by simp [specG]; norm_num,
        fun k hk1 hk2 => by fin_cases k <;> simp [specG] at hk1 hk2 ⊢⟩
  · exfalso; rw [ha, hb, hc] at hle; norm_num at hle
  · right
    refine ⟨by rw [ha, hb, hc]; norm_num, ?_⟩
    rw [z b hb, z c hc]
    rcases o a ha with rfl | rfl
    · exact ⟨0, 1, by decide, by simp [specG]; norm_num, by simp [specG]; norm_num,
        fun k hk1 hk2 => by fin_cases k <;> simp [specG] at hk1 hk2 ⊢⟩
    · exact ⟨2, 3, by decide, by simp [specG]; norm_num, by simp [specG]; norm_num,
        fun k hk1 hk2 => by fin_cases k <;> simp [specG] at hk1 hk2 ⊢⟩
  · exfalso; rw [ha, hb, hc] at hle; norm_num at hle
  · exfalso; rw [ha, hb, hc] at hle; norm_num at hle
  · exfalso; rw [ha, hb, hc] at hle; norm_num at hle

/-! ### Equality at `P = 1`: `s ∈ {0, 1}` and the HS / cluster triples -/

/-- `r = √X` for a nonnegative triple of sum one: `r ∈ [0, 1]`, `r² = 1 - 3 e₂`. -/
theorem exists_root {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hs : a + b + c = 1) :
    ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧ r ^ 2 = 1 - 3 * (a * b + a * c + b * c) := by
  have h := X_bounds ha hb hc hs
  exact ⟨Real.sqrt _, Real.sqrt_nonneg _, by rw [Real.sqrt_le_one]; exact h.2, Real.sq_sqrt h.1⟩

theorem e3_le {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hs : a + b + c = 1) :
    27 * (a * b * c) ≤ 1 := by
  obtain ⟨r, hr, hr1, hr4⟩ := exists_root ha hb hc hs
  have := rp_bound hs hr hr4
  unfold gfun at this
  nlinarith [mul_nonneg (sq_nonneg r) (sub_nonneg.2 hr1)]

theorem amgm_eq {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hs : a + b + c = 1)
    (h : 1 ≤ 27 * (a * b * c)) : a = 1 / 3 ∧ b = 1 / 3 ∧ c = 1 / 3 := by
  obtain ⟨r, hr, hr1, hr4⟩ := exists_root ha hb hc hs
  have h1 := rp_bound hs hr hr4
  unfold gfun at h1
  have h2 : r ^ 2 * (3 - 2 * r) ≤ 0 := by nlinarith
  have h3 : r ^ 2 = 0 := by
    by_contra hne
    have : 0 < r ^ 2 := lt_of_le_of_ne (sq_nonneg r) (Ne.symm hne)
    nlinarith
  have h4 : (a - b) ^ 2 + (a - c) ^ 2 + (b - c) ^ 2 = 0 := by nlinarith
  have e1 : a - b = 0 := by nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
  have e2 : a - c = 0 := by nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
  refine ⟨?_, ?_, ?_⟩ <;> linarith

theorem sq01_mul {x y : ℝ} (hx : x ^ 2 = 0 ∨ x ^ 2 = 1) (hy : y ^ 2 = 0 ∨ y ^ 2 = 1) :
    (x * y) ^ 2 = 0 ∨ (x * y) ^ 2 = 1 := by
  rw [mul_pow]; rcases hx with h | h <;> rcases hy with h' | h' <;> simp [h, h']

theorem sq01_neg {x : ℝ} (hx : x ^ 2 = 0 ∨ x ^ 2 = 1) : (-x) ^ 2 = 0 ∨ (-x) ^ 2 = 1 := by
  rw [neg_sq]; exact hx

/-- A nonnegative triple of sum one with `e₂ = 0` is a coordinate vector: each entry is `0` or `1`. -/
theorem coord_of_e2 {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hs : a + b + c = 1)
    (h : 1 - 3 * (a * b + a * c + b * c) = 1) :
    (a = 0 ∨ a = 1) ∧ (b = 0 ∨ b = 1) ∧ (c = 0 ∨ c = 1) := by
  have hab : a * b = 0 := by nlinarith [mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc]
  have hac : a * c = 0 := by nlinarith [mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc]
  have hbc : b * c = 0 := by nlinarith [mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc]
  have h1 : a * (a - 1) = 0 := by
    have : a - 1 = -(b + c) := by linarith
    rw [this]; nlinarith
  have h2 : b * (b - 1) = 0 := by
    have : b - 1 = -(a + c) := by linarith
    rw [this]; nlinarith
  have h3 : c * (c - 1) = 0 := by
    have : c - 1 = -(a + b) := by linarith
    rw [this]; nlinarith
  refine ⟨?_, ?_, ?_⟩
  · rcases mul_eq_zero.mp h1 with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  · rcases mul_eq_zero.mp h2 with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  · rcases mul_eq_zero.mp h3 with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)

theorem ge_one_of_prod {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hx1 : x ≤ 1) (hy1 : y ≤ 1)
    (h : x * y = 1) : 1 ≤ x ∧ 1 ≤ y := by
  constructor <;> nlinarith

theorem one_of_prod_one {x y : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1)
    (h : x * y = 1) : x = 1 ∧ y = 1 := by
  constructor <;> nlinarith

/-- **Equality `F² = 6V` at `P = 1` for the core triple** (`s ∈ {0, 1}`): an HS triple or a cluster triple. -/
theorem core_equality (m n : Fin 3 → ℝ) (hm : m 0 ^ 2 + m 1 ^ 2 + m 2 ^ 2 = 1)
    (hn : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1)
    (hEq : RenyiFull.Fm (spc0 m n) (spc1 m n) (spc2 m n) ^ 2 =
      6 * RenyiFull.Vm (spc0 m n) (spc1 m n) (spc2 m n)) :
    IsHsTriple (spc0 m n) (spc1 m n) (spc2 m n) ∨ IsClusterTriple (spc0 m n) (spc1 m n) (spc2 m n) := by
  obtain ⟨s, hs0, hs1, -, hV, hF, hRF⟩ := core_triple m n hm hn
  have hVm := Vm_core m n hm hn
  have hXb := X_bounds (sq_nonneg (m 0)) (sq_nonneg (m 1)) (sq_nonneg (m 2)) hm
  have hYb := X_bounds (sq_nonneg (n 0)) (sq_nonneg (n 1)) (sq_nonneg (n 2)) hn
  set X := 1 - 3 * (m 0 ^ 2 * m 1 ^ 2 + m 0 ^ 2 * m 2 ^ 2 + m 1 ^ 2 * m 2 ^ 2) with hXdef
  set Y := 1 - 3 * (n 0 ^ 2 * n 1 ^ 2 + n 0 ^ 2 * n 2 ^ 2 + n 1 ^ 2 * n 2 ^ 2) with hYdef
  set F := RenyiFull.Fm (spc0 m n) (spc1 m n) (spc2 m n) with hFdef
  have hF0 : 0 ≤ F := by nlinarith [mul_nonneg (sq_nonneg s) (sub_nonneg.2 hs1), sq_nonneg s]
  have hF2 : F = s ^ 2 / 2 := by
    have h4 : (F - s ^ 2 / 2) * (F + s ^ 2 / 2) = 0 := by nlinarith
    rcases mul_eq_zero.mp h4 with h | h
    · linarith
    · nlinarith [sq_nonneg s]
  have hkey : s = 0 ∨ s = 1 := by
    have : s ^ 2 * (1 - s) = 0 := by
      have h1 : 0 ≤ s ^ 2 * (1 - s) := mul_nonneg (sq_nonneg s) (by linarith)
      nlinarith
    rcases mul_eq_zero.mp this with h | h
    · left; exact pow_eq_zero_iff (two_ne_zero) |>.mp h
    · right; linarith
  rcases hkey with rfl | rfl
  · -- s = 0: HS
    left
    have hk : kap m n = 1 / 27 := by
      have : (1 - 27 * kap m n) / 2 = 0 := by rw [← hF, hF2]; ring
      linarith
    have eA := e3_le (sq_nonneg (m 0)) (sq_nonneg (m 1)) (sq_nonneg (m 2)) hm
    have eB := e3_le (sq_nonneg (n 0)) (sq_nonneg (n 1)) (sq_nonneg (n 2)) hn
    obtain ⟨gA, gB⟩ := ge_one_of_prod (by positivity) (by positivity) eA eB (by
      have : (27 * (m 0 ^ 2 * m 1 ^ 2 * m 2 ^ 2)) * (27 * (n 0 ^ 2 * n 1 ^ 2 * n 2 ^ 2))
          = 729 * kap m n ^ 2 := by rw [kap_sq]; ring
      rw [this, hk]; norm_num)
    obtain ⟨a0, a1, a2⟩ := amgm_eq (sq_nonneg (m 0)) (sq_nonneg (m 1)) (sq_nonneg (m 2)) hm gA
    obtain ⟨b0, b1, b2⟩ := amgm_eq (sq_nonneg (n 0)) (sq_nonneg (n 1)) (sq_nonneg (n 2)) hn gB
    have kk : ∀ p : ℝ, p = kap m n → p = 1 / 27 := fun p hp => by rw [hp, hk]
    refine ⟨?_, ?_, ?_⟩
    · exact specG_hs (by rw [mul_pow, a0, b0]; norm_num) (by rw [mul_pow, a1, b1]; norm_num)
        (by rw [neg_sq, mul_pow, a2, b2]; norm_num)
        (by
          have : m 0 * n 0 * (m 1 * n 1) * -(m 2 * n 2) = -kap m n := by unfold kap; ring
          rw [this, hk])
    · exact specG_hs (by rw [neg_sq, mul_pow, a2, b1]; norm_num) (by rw [mul_pow, a0, b2]; norm_num)
        (by rw [mul_pow, a1, b0]; norm_num)
        (by
          have : -(m 2 * n 1) * (m 0 * n 2) * (m 1 * n 0) = -kap m n := by unfold kap; ring
          rw [this, hk])
    · exact specG_hs (by rw [mul_pow, a1, b2]; norm_num) (by rw [mul_pow, a2, b0]; norm_num)
        (by rw [neg_sq, mul_pow, a0, b1]; norm_num)
        (by
          have : m 1 * n 2 * (m 2 * n 0) * -(m 0 * n 1) = -kap m n := by unfold kap; ring
          rw [this, hk])
  · -- s = 1: cluster
    right
    have hXY : X * Y = 1 := by rw [← hVm, hV]; norm_num
    obtain ⟨hX1, hY1⟩ := one_of_prod_one hXb.1 hXb.2 hYb.1 hYb.2 hXY
    obtain ⟨a0, a1, a2⟩ := coord_of_e2 (sq_nonneg (m 0)) (sq_nonneg (m 1)) (sq_nonneg (m 2)) hm hX1
    obtain ⟨b0, b1, b2⟩ := coord_of_e2 (sq_nonneg (n 0)) (sq_nonneg (n 1)) (sq_nonneg (n 2)) hn hY1
    have hsum := sum_u (m 0 ^ 2) (m 1 ^ 2) (m 2 ^ 2) (n 0 ^ 2) (n 1 ^ 2) (n 2 ^ 2) hm hn
    have hu : (m 0 * n 0) ^ 2 + (m 1 * n 1) ^ 2 + (-(m 2 * n 2)) ^ 2 +
        ((-(m 2 * n 1)) ^ 2 + (m 0 * n 2) ^ 2 + (m 1 * n 0) ^ 2) +
        ((m 1 * n 2) ^ 2 + (m 2 * n 0) ^ 2 + (-(m 0 * n 1)) ^ 2) = 1 := by
      linear_combination hsum
    have c0 := specG_unit (sq01_mul a0 b0) (sq01_mul a1 b1) (sq01_neg (sq01_mul a2 b2))
      (by linarith [hu, sq_nonneg (-(m 2 * n 1)), sq_nonneg (m 0 * n 2), sq_nonneg (m 1 * n 0),
        sq_nonneg (m 1 * n 2), sq_nonneg (m 2 * n 0), sq_nonneg (-(m 0 * n 1))])
    have c1 := specG_unit (sq01_neg (sq01_mul a2 b1)) (sq01_mul a0 b2) (sq01_mul a1 b0)
      (by linarith [hu, sq_nonneg (m 0 * n 0), sq_nonneg (m 1 * n 1), sq_nonneg (-(m 2 * n 2)),
        sq_nonneg (m 1 * n 2), sq_nonneg (m 2 * n 0), sq_nonneg (-(m 0 * n 1))])
    have c2 := specG_unit (sq01_mul a1 b2) (sq01_mul a2 b0) (sq01_neg (sq01_mul a0 b1))
      (by linarith [hu, sq_nonneg (m 0 * n 0), sq_nonneg (m 1 * n 1), sq_nonneg (-(m 2 * n 2)),
        sq_nonneg (-(m 2 * n 1)), sq_nonneg (m 0 * n 2), sq_nonneg (m 1 * n 0)])
    unfold spc0 spc1 spc2
    rcases c0 with ⟨h0, f0⟩ | ⟨h0, t0⟩ <;> rcases c1 with ⟨h1, f1⟩ | ⟨h1, t1⟩ <;>
      rcases c2 with ⟨h2, f2⟩ | ⟨h2, t2⟩
    · exfalso; linarith
    · exact Or.inr (Or.inr ⟨f0, f1, t2⟩)
    · exact Or.inr (Or.inl ⟨f0, t1, f2⟩)
    · exfalso; linarith
    · exact Or.inl ⟨t0, f1, f2⟩
    · exfalso; linarith
    · exfalso; linarith
    · exfalso; linarith

end FormalResearch.FourQubitEntropy.QVEquality
