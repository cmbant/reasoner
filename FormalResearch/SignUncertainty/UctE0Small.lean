module

public import FormalResearch.SignUncertainty.UctE0Remainder

/-!
# Pointwise bounds for `E₀ = kernelAmp c - 1` and its first two derivatives (F2a, `uct:bump-weighted` far band)

`E0_small_bounds`: there are `C, q` such that for `0 < h ≤ 1/8`, `c = h⁻²`, `v = τ/h`, the function `E₀ = bumpE0 c` is `C²` and, for all real `τ`,
`|E₀| ≤ C |τ| (1+|v|)^q`, `|E₀'| ≤ C (1+|v|)^q`, `|E₀''| ≤ C c (1+|v|)^q`.

Route: `E₀ = ε + a₁ τ + G_h(τ/h)` (`E0_poly_remainder`, `P` without constant term).  `|G_h(v)| ≤ N h|v|(1+|v|)^{D+1}`, `|h⁻¹ G_h'(v)| ≤ N (1+|v|)^{D+1}` (as `d₀ ≥ 1`
for every monomial), `|P| ≤ N(1+|v|)^D`.  `a₁ = E₀'(0)` is bounded by evaluating `E₀(h)`, `|E₀(h)| ≤ C h` (`E0_wexp`, `N = 1`).  The bound on `E₀` is the mean value theorem from `E₀(0) = 0`.

Class: proved, no hypotheses.
-/

@[expose] public section

open Set Filter Topology
open FormalResearch.Asymptotics

namespace FormalResearch.SignUncertainty

lemma WPolyW.one_le {P : P2} (hP : WPolyW P) (h0 : MvPolynomial.constantCoeff P = 0) {d : Fin 2 →₀ ℕ}
    (hd : d ∈ P.support) : 1 ≤ d 0 := by
  by_contra hcon
  have hd0 : d 0 = 0 := by omega
  have hne : P.coeff d ≠ 0 := by simpa using hd
  have h1 : d 1 ≤ 0 := by have := hP d hne; omega
  have hz : d = 0 := by
    ext i
    fin_cases i
    · simpa using hd0
    · simp; omega
  rw [hz] at hne
  exact hne (by simpa [MvPolynomial.constantCoeff_eq] using h0)

lemma norm_gP0_fine (P : P2) (hP1 : ∀ d ∈ P.support, 1 ≤ d 0) {h : ℝ} (h0 : 0 < h) (h1 : h ≤ 1) (v : ℝ) :
    ‖gP0 P h v‖ ≤ cnorm P * (h * |v|) * (1 + |v|) ^ (P.support.sup (fun d => d 1) + 1) := by
  unfold gP0 cnorm
  rw [Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d hd => ?_)
  have hD : d 1 ≤ P.support.sup (fun d => d 1) := Finset.le_sup (f := fun d => d 1) hd
  have hd1 := hP1 d hd
  refine (norm_div_nat_le _ (by omega)).trans ?_
  simp only [norm_mul, norm_div, norm_pow, Complex.norm_real, Complex.norm_natCast, Real.norm_eq_abs, abs_of_pos h0]
  have hn1 : (1 : ℝ) ≤ ((d 1 + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ d 1 + 1)
  have hhp : h ^ (d 0) ≤ h := by
    calc h ^ (d 0) ≤ h ^ 1 := pow_le_pow_of_le_one h0.le h1 hd1
      _ = h := pow_one h
  have hv : |v| ^ (d 1 + 2) ≤ |v| * (1 + |v|) ^ (P.support.sup (fun d => d 1) + 1) := by
    calc |v| ^ (d 1 + 2) = |v| * |v| ^ (d 1 + 1) := by ring
      _ ≤ |v| * (1 + |v|) ^ (d 1 + 1) := by gcongr; linarith [abs_nonneg v]
      _ ≤ |v| * (1 + |v|) ^ (P.support.sup (fun d => d 1) + 1) := by
          gcongr
          linarith [abs_nonneg v]
  have hc0 := norm_nonneg (P.coeff d)
  calc ‖P.coeff d‖ * h ^ (d 0) / (((d 1 + 1 : ℕ)) : ℝ) * |v| ^ (d 1 + 2)
      ≤ ‖P.coeff d‖ * h ^ (d 0) * |v| ^ (d 1 + 2) := by
        gcongr
        exact div_le_self (by positivity) hn1
    _ ≤ ‖P.coeff d‖ * h * (|v| * (1 + |v|) ^ (P.support.sup (fun d => d 1) + 1)) := by
        gcongr
    _ = _ := by ring

lemma norm_gP1_fine (P : P2) (hP1 : ∀ d ∈ P.support, 1 ≤ d 0) {h : ℝ} (h0 : 0 < h) (h1 : h ≤ 1) (v : ℝ) :
    ‖((h⁻¹ : ℝ) : ℂ) * gP1 P h v‖ ≤ cnorm P * (1 + |v|) ^ (P.support.sup (fun d => d 1) + 1) := by
  unfold gP1 cnorm
  rw [Finset.mul_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d hd => ?_)
  have hD : d 1 ≤ P.support.sup (fun d => d 1) := Finset.le_sup (f := fun d => d 1) hd
  have hd1 := hP1 d hd
  simp only [norm_mul, norm_div, norm_pow, Complex.norm_real, Complex.norm_natCast, Real.norm_eq_abs, abs_of_pos h0,
    abs_inv]
  have hn1 : (1 : ℝ) ≤ ((d 1 + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ d 1 + 1)
  have hhp : h⁻¹ * h ^ (d 0) ≤ 1 := by
    obtain ⟨k, hk⟩ : ∃ k, d 0 = k + 1 := ⟨d 0 - 1, by omega⟩
    rw [hk, pow_succ]
    have : h⁻¹ * (h ^ k * h) = h ^ k := by field_simp
    rw [this]; exact pow_le_one₀ h0.le h1
  have hv : |v| ^ (d 1 + 1) ≤ (1 + |v|) ^ (P.support.sup (fun d => d 1) + 1) := by
    calc |v| ^ (d 1 + 1) ≤ (1 + |v|) ^ (d 1 + 1) := by gcongr; linarith
      _ ≤ (1 + |v|) ^ (P.support.sup (fun d => d 1) + 1) := by
          gcongr
          linarith [abs_nonneg v]
  have hc0 := norm_nonneg (P.coeff d)
  calc h⁻¹ * (‖P.coeff d‖ * h ^ (d 0) * |v| ^ (d 1 + 1) / (((d 1 + 1 : ℕ)) : ℝ))
      ≤ h⁻¹ * (‖P.coeff d‖ * h ^ (d 0) * |v| ^ (d 1 + 1)) := by
        gcongr
        exact div_le_self (by positivity) hn1
    _ = ‖P.coeff d‖ * (h⁻¹ * h ^ (d 0)) * |v| ^ (d 1 + 1) := by ring
    _ ≤ ‖P.coeff d‖ * 1 * (1 + |v|) ^ (P.support.sup (fun d => d 1) + 1) := by
        gcongr
    _ = _ := by ring

theorem E0_small_bounds : ∃ (C : ℝ) (q : ℕ), 0 ≤ C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 / 8 →
    ContDiff ℝ 2 (bumpE0 ((h ^ 2)⁻¹)) ∧ ∀ τ : ℝ,
      ‖bumpE0 ((h ^ 2)⁻¹) τ‖ ≤ C * |τ| * (1 + |τ / h|) ^ q ∧
      ‖deriv (bumpE0 ((h ^ 2)⁻¹)) τ‖ ≤ C * (1 + |τ / h|) ^ q ∧
      ‖deriv (deriv (bumpE0 ((h ^ 2)⁻¹))) τ‖ ≤ C * (h ^ 2)⁻¹ * (1 + |τ / h|) ^ q := by
  obtain ⟨P, Cε, p, hP, hP0, hCε, hrem⟩ := E0_poly_remainder
  obtain ⟨Cg, hCg0, hCg⟩ := WExpW.norm_le_x (k0 := 1) le_rfl (le_refl 1)
    ((E0_wexp (N := 1) (by norm_num) (by norm_num)).toW)
  have hP1 : ∀ d ∈ P.support, 1 ≤ d 0 := fun d hd => hP.one_le hP0 hd
  set N : ℝ := cnorm P with hN
  have hN0 : 0 ≤ N := cnorm_nonneg P
  set D : ℕ := P.support.sup (fun d => d 1) with hD
  set A1 : ℝ := 8 * Cg + Cε * 2 ^ p + N * 2 ^ (D + 1) with hA1
  have hA10 : 0 ≤ A1 := by positivity
  refine ⟨Cε + A1 + N, p + D + 1, by positivity, fun h hh hh8 => ?_⟩
  have hh1 : h ≤ 1 := by linarith
  have hc : 2 ≤ (h ^ 2)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) (by positivity)]; nlinarith
  set c : ℝ := (h ^ 2)⁻¹ with hcdef
  set E : ℝ → ℂ := bumpE0 c with hEdef
  obtain ⟨hεC2, hε⟩ := hrem h hh (by linarith)
  set a1 : ℂ := deriv E 0 with ha1def
  have hEd : ∀ τ : ℝ, deriv E τ = deriv (E0r P h) τ + (a1 + ((h⁻¹ : ℝ) : ℂ) * gP1 P h (τ / h)) := by
    intro τ
    have h1 := deriv_E0r (P := P) hh hc τ
    simp only [← hEdef, ← hcdef, ← ha1def] at h1
    have h2 : deriv E τ = deriv (kernelAmp c) τ := congrFun (deriv_bumpE0 c) τ
    rw [h2]
    linear_combination (-1 : ℂ) * h1
  have hEdd : ∀ τ : ℝ, deriv (deriv E) τ = deriv (deriv (E0r P h)) τ + ((h⁻¹ : ℝ) : ℂ) ^ 2 * wev h (τ / h) P := by
    intro τ
    have h1 := deriv_deriv_E0r (P := P) hh hc τ
    simp only [← hcdef] at h1
    have h2 : deriv (deriv E) τ = deriv (deriv (kernelAmp c)) τ := congrFun (congrArg deriv (deriv_bumpE0 c)) τ
    rw [h2]
    linear_combination (-1 : ℂ) * h1
  have hEexp : ∀ τ : ℝ, E τ = E0r P h τ + (a1 * (τ : ℂ) + gP0 P h (τ / h)) := by
    intro τ; unfold E0r; ring
  -- bound on a₁
  have hEh : ‖E h‖ ≤ Cg * (h * 8) := by
    have hr : WReg 1 h 1 := ⟨hh, by norm_num; linarith⟩
    have := hCg h 1 hr
    simp only [wx, abs_one] at this
    have e : E h = kernelAmp ((h ^ 2)⁻¹) (h * 1) - 1 := by simp [hEdef, hcdef, bumpE0]
    rw [e]
    refine this.trans (le_of_eq ?_)
    ring
  have ha1b : ‖a1‖ ≤ A1 := by
    have h1 := hEexp h
    have e : a1 * (h : ℂ) = E h - E0r P h h - gP0 P h (h / h) := by rw [h1]; ring
    have hdiv : h / h = 1 := div_self hh.ne'
    have hg := norm_gP0_fine P hP1 hh hh1 (h / h)
    rw [hdiv] at hg
    simp only [abs_one, mul_one] at hg
    have hε0 := (hε h).1
    rw [hdiv] at hε0
    simp only [abs_one] at hε0
    have hn : ‖a1‖ * h ≤ ‖E h‖ + ‖E0r P h h‖ + ‖gP0 P h 1‖ := by
      have := congrArg norm e
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hh.le] at this
      rw [this]
      refine (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) ?_)
      rw [hdiv]
    have hεh : ‖E0r P h h‖ ≤ Cε * 2 ^ p * h := by
      refine hε0.trans ?_
      have : (1 + 1 : ℝ) = 2 := by norm_num
      rw [this]
      have h4 : h ^ 4 ≤ h := by
        calc h ^ 4 ≤ h ^ 1 := pow_le_pow_of_le_one hh.le hh1 (by norm_num)
          _ = h := pow_one h
      calc Cε * h ^ 4 * 2 ^ p ≤ Cε * h * 2 ^ p := by gcongr
        _ = _ := by ring
    have hgh : ‖gP0 P h 1‖ ≤ N * 2 ^ (D + 1) * h := by
      refine hg.trans ?_
      have : (1 + 1 : ℝ) = 2 := by norm_num
      rw [this]; apply le_of_eq; ring
    have : ‖a1‖ * h ≤ A1 * h := by
      calc ‖a1‖ * h ≤ Cg * (h * 8) + Cε * 2 ^ p * h + N * 2 ^ (D + 1) * h := by linarith
        _ = A1 * h := by rw [hA1]; ring
    exact le_of_mul_le_mul_right this hh
  -- bounds
  have hX1 : ∀ τ : ℝ, 1 ≤ 1 + |τ / h| := fun τ => by linarith [abs_nonneg (τ / h)]
  have hXp : ∀ (τ : ℝ) (k : ℕ), k ≤ p + D + 1 → (1 + |τ / h|) ^ k ≤ (1 + |τ / h|) ^ (p + D + 1) :=
    fun τ k hk => pow_le_pow_right₀ (hX1 τ) hk
  have hD1 : ∀ τ : ℝ, ‖deriv E τ‖ ≤ (Cε + A1 + N) * (1 + |τ / h|) ^ (p + D + 1) := by
    intro τ
    rw [hEd τ]
    have b1 := (hε τ).2.1
    have b2 : ‖((h⁻¹ : ℝ) : ℂ) * gP1 P h (τ / h)‖ ≤ N * (1 + |τ / h|) ^ (D + 1) := norm_gP1_fine P hP1 hh hh1 (τ / h)
    have h3 : h ^ 3 ≤ 1 := pow_le_one₀ hh.le hh1
    have hX := hX1 τ
    have hXq : (1 + |τ / h|) ^ p ≤ (1 + |τ / h|) ^ (p + D + 1) := hXp τ p (by omega)
    have hXq2 : (1 + |τ / h|) ^ (D + 1) ≤ (1 + |τ / h|) ^ (p + D + 1) := hXp τ (D + 1) (by omega)
    have hXq0 : 1 ≤ (1 + |τ / h|) ^ (p + D + 1) := one_le_pow₀ hX
    calc ‖deriv (E0r P h) τ + (a1 + ((h⁻¹ : ℝ) : ℂ) * gP1 P h (τ / h))‖
        ≤ ‖deriv (E0r P h) τ‖ + (‖a1‖ + ‖((h⁻¹ : ℝ) : ℂ) * gP1 P h (τ / h)‖) :=
          (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
      _ ≤ Cε * h ^ 3 * (1 + |τ / h|) ^ p + (A1 + N * (1 + |τ / h|) ^ (D + 1)) := add_le_add b1 (add_le_add ha1b b2)
      _ ≤ Cε * (1 + |τ / h|) ^ (p + D + 1) + (A1 * (1 + |τ / h|) ^ (p + D + 1) + N * (1 + |τ / h|) ^ (p + D + 1)) := by
          have e1 : Cε * h ^ 3 * (1 + |τ / h|) ^ p ≤ Cε * (1 + |τ / h|) ^ (p + D + 1) := by
            calc Cε * h ^ 3 * (1 + |τ / h|) ^ p ≤ Cε * 1 * (1 + |τ / h|) ^ p := by gcongr
              _ ≤ Cε * (1 + |τ / h|) ^ (p + D + 1) := by rw [mul_one]; gcongr
          have e2 : A1 ≤ A1 * (1 + |τ / h|) ^ (p + D + 1) := le_mul_of_one_le_right hA10 hXq0
          have e3 : N * (1 + |τ / h|) ^ (D + 1) ≤ N * (1 + |τ / h|) ^ (p + D + 1) := by gcongr
          linarith
      _ = _ := by ring
  have hD2 : ∀ τ : ℝ, ‖deriv (deriv E) τ‖ ≤ (Cε + A1 + N) * c * (1 + |τ / h|) ^ (p + D + 1) := by
    intro τ
    rw [hEdd τ]
    have b1 := (hε τ).2.2
    have b2 : ‖wev h (τ / h) P‖ ≤ N * (1 + |τ / h|) ^ D := norm_wev_le_crude P hh hh1 (τ / h)
    have hc2 : ‖((h⁻¹ : ℝ) : ℂ) ^ 2‖ = c := by
      rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hh.le), hcdef, inv_pow]
    have hX := hX1 τ
    have hXq : (1 + |τ / h|) ^ p ≤ (1 + |τ / h|) ^ (p + D + 1) := hXp τ p (by omega)
    have hXq2 : (1 + |τ / h|) ^ D ≤ (1 + |τ / h|) ^ (p + D + 1) := hXp τ D (by omega)
    have hXq0 : 1 ≤ (1 + |τ / h|) ^ (p + D + 1) := one_le_pow₀ hX
    have hh2c : h ^ 2 ≤ c := by nlinarith
    have hc0 : 0 ≤ c := by linarith
    calc ‖deriv (deriv (E0r P h)) τ + ((h⁻¹ : ℝ) : ℂ) ^ 2 * wev h (τ / h) P‖
        ≤ ‖deriv (deriv (E0r P h)) τ‖ + c * ‖wev h (τ / h) P‖ := by
          refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
          rw [norm_mul, hc2]
      _ ≤ Cε * h ^ 2 * (1 + |τ / h|) ^ p + c * (N * (1 + |τ / h|) ^ D) := add_le_add b1 (mul_le_mul_of_nonneg_left b2 hc0)
      _ ≤ Cε * c * (1 + |τ / h|) ^ (p + D + 1) + c * (N * (1 + |τ / h|) ^ (p + D + 1)) := by
          have e1 : Cε * h ^ 2 * (1 + |τ / h|) ^ p ≤ Cε * c * (1 + |τ / h|) ^ (p + D + 1) := by
            calc Cε * h ^ 2 * (1 + |τ / h|) ^ p ≤ Cε * c * (1 + |τ / h|) ^ p := by gcongr
              _ ≤ _ := by gcongr
          have e3 : c * (N * (1 + |τ / h|) ^ D) ≤ c * (N * (1 + |τ / h|) ^ (p + D + 1)) := by gcongr
          linarith
      _ ≤ _ := by
          have : 0 ≤ c * (1 + |τ / h|) ^ (p + D + 1) := by positivity
          nlinarith [mul_nonneg hA10 this]
  have hE0 : E 0 = 0 := bumpE0_zero c
  refine ⟨contDiff_bumpE0 hc, fun τ => ⟨?_, hD1 τ, hD2 τ⟩⟩
  have hdiff : ∀ t ∈ Set.uIcc (0 : ℝ) τ, DifferentiableAt ℝ E t := fun t _ =>
    ((contDiff_bumpE0 hc).differentiable (by norm_num)) t
  have hbd : ∀ t ∈ Set.uIcc (0 : ℝ) τ, ‖deriv E t‖ ≤ (Cε + A1 + N) * (1 + |τ / h|) ^ (p + D + 1) := by
    intro t ht
    refine (hD1 t).trans ?_
    have hts : |t| ≤ |τ| := by
      rcases Set.mem_uIcc.mp ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [abs_of_nonneg h1, abs_of_nonneg (h1.trans h2)]; exact h2
      · rw [abs_of_nonpos h2, abs_of_nonpos (h1.trans h2)]; linarith
    have : |t / h| ≤ |τ / h| := by
      rw [abs_div, abs_div, abs_of_pos hh]; exact div_le_div_of_nonneg_right hts hh.le
    gcongr
  have := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbd (convex_uIcc 0 τ) Set.left_mem_uIcc Set.right_mem_uIcc
  rw [hE0, sub_zero, sub_zero, Real.norm_eq_abs] at this
  calc ‖E τ‖ ≤ (Cε + A1 + N) * (1 + |τ / h|) ^ (p + D + 1) * |τ| := this
    _ = _ := by ring

/-- info: 'FormalResearch.SignUncertainty.E0_small_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms E0_small_bounds

end FormalResearch.SignUncertainty
