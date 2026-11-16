module

public import FormalResearch.Racah.P2AnalyticHeadline6j
public import FormalResearch.Racah.P2AnalyticHeadline
public import FormalResearch.Racah.P2AnalyticTaylor

/-!
# The Flude `Λ⁻¹` defect (Weyl P2, `sec:6jFludedefect`, `eq:Fludedefect`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, subsection *Why the usual Edmonds--Flude variables
retain a `Λ⁻¹` defect* (`eq:Fludenorm`, `eq:Fludeangle`, `eq:deltaF`, `eq:Fludedefect`).

Flude's normalisation `Ψ_f = (-1)^ξ √(ω_aω_b) W_f`, `ω_a = 2A+f`, `ω_b = 2B+f` and angle
`x_F = cosA (A+n/2) (B+m/2) C` are compared with the Weyl-midpoint kernel `Φ_f` and angle
`x = cosA A B C`.  `sec_6jFludedefect` proves, uniformly on the cone `𝒯_δ`,

`Ψ_f - d^f_{nm}(arccos x_F) = Λ⁻¹ [r_F d^f_{nm}(arccos x) - δ_F d'(x)] + O(H⁻²)`

with the paper's `r_F` and `δ_F`.  The input is `thm_6jeven` at `R = 1` (`Φ_f = d + O(H⁻²)`); the rest is
exact algebra (`Psi6_eq_mul_Phi6`, `cosA_shift_identity`, `sqrt_one_add_mul_bound`) and a uniform
second-order Taylor bound for `d` on compact subintervals of `(-1,1)` (`taylor_two_uniform`, from
`taylor_uniform_of_analytic`).  Every constant is explicit in `flude_core`.

Not formalised: the claim that the defect `r_F d - δ_F d'` is generically non-zero (the word "generic"
in the paper), and the phrase "for the same family" beyond the stated uniform cone.
-/

@[expose] public section

namespace FormalResearch.Racah

open Set Filter Topology FormalResearch.Wigner FormalResearch.Racah.SixJ

/-- First-order Taylor bound of a function analytic on `(-1,1)`, uniform on `[-1+η, 1-η]`. -/
theorem taylor_two_uniform (D : ℝ → ℝ) (hD : AnalyticOnNhd ℝ D (Ioo (-1 : ℝ) 1)) {η : ℝ}
    (hη : 0 < η) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ M : ℝ, ∀ x ∈ Icc (-1 + η) (1 - η), ∀ t : ℝ, |t| ≤ ρ →
      |D (x + t) - D x - deriv D x * t| ≤ M * t ^ 2 := by
  set U : Set (ℝ × ℝ) := {p | p.1 + p.2 ∈ Ioo (-1 : ℝ) 1} with hU
  have hUo : IsOpen U := isOpen_Ioo.preimage (continuous_fst.add continuous_snd)
  have hG : AnalyticOnNhd ℝ (fun p : ℝ × ℝ => D (p.1 + p.2)) U := by
    intro p hp
    have h1 : AnalyticAt ℝ (fun q : ℝ × ℝ => q.1 + q.2) p :=
      (analyticAt_fst).add (analyticAt_snd)
    exact (hD _ hp).comp_of_eq h1 rfl
  have hK : IsCompact (Icc (-1 + η) (1 - η)) := isCompact_Icc
  have hKU : Icc (-1 + η) (1 - η) ×ˢ ({0} : Set ℝ) ⊆ U := by
    rintro ⟨z, t⟩ ⟨hz, ht⟩
    have : t = 0 := ht
    subst this
    simp only [hU, Set.mem_ofPred_eq, add_zero]
    exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
  obtain ⟨ρ, hρ, C, h⟩ := taylor_uniform_of_analytic hUo hG hK hKU 2
  refine ⟨ρ, hρ, C, fun x hx t ht => ?_⟩
  have := h x hx t ht
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add, taylorCoeff,
    iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one, pow_zero, mul_one,
    iteratedDeriv_one, Nat.factorial_one, pow_one, add_zero] at this
  have hd : deriv (fun s : ℝ => D (x + s)) 0 = deriv D x := by
    rw [deriv_comp_const_add]; simp
  rw [hd] at this
  simpa [sq_abs, mul_comm, sub_sub] using this

/-- `√((1+a)(1+b)) = 1 + (a+b)/2 + O((a-b)²)` for `a, b ≥ 0`. -/
theorem sqrt_one_add_mul_bound {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.sqrt ((1 + a) * (1 + b)) - 1 - (a + b) / 2| ≤ (a - b) ^ 2 / 8 := by
  set g := Real.sqrt ((1 + a) * (1 + b)) with hg
  have hg2 : g ^ 2 = (1 + a) * (1 + b) := Real.sq_sqrt (by positivity)
  have hg1 : 1 ≤ g := by
    rw [hg]; apply Real.le_sqrt_of_sq_le; nlinarith [mul_nonneg ha hb]
  have key : (1 + (a + b) / 2) ^ 2 - g ^ 2 = (a - b) ^ 2 / 4 := by rw [hg2]; ring
  have hden : 2 ≤ (1 + (a + b) / 2) + g := by linarith
  have hnonneg : 0 ≤ (1 + (a + b) / 2) - g := by
    nlinarith [sq_nonneg (a - b)]
  have h2 : ((1 + (a + b) / 2) - g) * ((1 + (a + b) / 2) + g) = (a - b) ^ 2 / 4 := by
    rw [← key]; ring
  rw [abs_sub_comm, abs_of_nonneg (by linarith)]
  nlinarith [sq_nonneg (a - b)]

/-- The exact first-order identity for the Flude angle: with `x = cosA A B C`,
`U = pA + qB - x(qA + pB)`, `V = (p²+q²)/2 - xpq`,
`cosA (A+p) (B+q) C - x - U/(AB) = V/(A'B') - U (qA + pB + pq)/(AB A'B')`, `A' = A+p`, `B' = B+q`. -/
theorem cosA_shift_identity (A B C p q : ℝ) (hA : A ≠ 0) (hB : B ≠ 0) (hA' : A + p ≠ 0)
    (hB' : B + q ≠ 0) :
    cosA (A + p) (B + q) C - cosA A B C -
        (p * A + q * B - cosA A B C * (q * A + p * B)) / (A * B) =
      ((p ^ 2 + q ^ 2) / 2 - cosA A B C * p * q) / ((A + p) * (B + q)) -
        (p * A + q * B - cosA A B C * (q * A + p * B)) * (q * A + p * B + p * q) /
          (A * B * ((A + p) * (B + q))) := by
  unfold cosA
  field_simp
  ring

private theorem abs_div_le_of {N D n0 d0 : ℝ} (hN : |N| ≤ n0) (hD : d0 ≤ D) (hd0 : 0 < d0) :
    |N / D| ≤ n0 / d0 := by
  rw [abs_div, abs_of_pos (lt_of_lt_of_le hd0 hD)]
  exact div_le_div₀ ((abs_nonneg N).trans hN) hN hd0 hD

/-- The first-order shift of the angle and its remainder (the algebraic half of
`eq:Fludedefect`): on `δH ≤ A, B ≤ H`, `|x| ≤ 1`, `H ≥ 1`, `H ≥ 2|p|/δ`, `H ≥ 2|q|/δ`, the angle
`cosA (A+p) (B+q) C` equals `x + T + e` with `T = U/(AB)`, `|T| ≤ u₀/(δ² H)` and `|e| ≤ K₁/H²`,
`u₀ = 2(|p|+|q|)`, `K₁ = 4v₀/δ² + 4u₀w₀/δ⁴`, `v₀ = p²+q²`, `w₀ = |p|+|q|+|p||q|`. -/
theorem cosA_shift_bounds (A B C p q H δ : ℝ) (hδ : 0 < δ) (hH : 1 ≤ H) (hAH : A ≤ H) (hBH : B ≤ H)
    (hAδ : δ * H ≤ A) (hBδ : δ * H ≤ B) (hx : |cosA A B C| ≤ 1) (hp : 2 * |p| ≤ δ * H)
    (hq : 2 * |q| ≤ δ * H) :
    |(p * A + q * B - cosA A B C * (q * A + p * B)) / (A * B)| ≤
        2 * (|p| + |q|) / (δ ^ 2 * H) ∧
      |cosA (A + p) (B + q) C - cosA A B C -
          (p * A + q * B - cosA A B C * (q * A + p * B)) / (A * B)| ≤
        (4 * (p ^ 2 + q ^ 2) / δ ^ 2 +
            4 * (2 * (|p| + |q|)) * (|p| + |q| + |p| * |q|) / δ ^ 4) / H ^ 2 := by
  have hH0 : 0 < H := by linarith
  have hA0 : 0 < A := lt_of_lt_of_le (by positivity) hAδ
  have hB0 : 0 < B := lt_of_lt_of_le (by positivity) hBδ
  have hA' : δ * H / 2 ≤ A + p := by
    have := neg_abs_le p; linarith
  have hB' : δ * H / 2 ≤ B + q := by
    have := neg_abs_le q; linarith
  have hA'0 : 0 < A + p := lt_of_lt_of_le (by positivity) hA'
  have hB'0 : 0 < B + q := lt_of_lt_of_le (by positivity) hB'
  set x := cosA A B C with hxdef
  have hU : |p * A + q * B - x * (q * A + p * B)| ≤ 2 * (|p| + |q|) * H := by
    have e1 : |p * A| ≤ |p| * H := by
      rw [abs_mul, abs_of_pos hA0]; exact mul_le_mul_of_nonneg_left hAH (abs_nonneg p)
    have e2 : |q * B| ≤ |q| * H := by
      rw [abs_mul, abs_of_pos hB0]; exact mul_le_mul_of_nonneg_left hBH (abs_nonneg q)
    have e3 : |x * (q * A + p * B)| ≤ (|q| + |p|) * H := by
      rw [abs_mul]
      have : |q * A + p * B| ≤ (|q| + |p|) * H := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_pos hA0, abs_of_pos hB0]
        nlinarith [mul_le_mul_of_nonneg_left hAH (abs_nonneg q),
          mul_le_mul_of_nonneg_left hBH (abs_nonneg p)]
      calc |x| * |q * A + p * B| ≤ 1 * ((|q| + |p|) * H) :=
            mul_le_mul hx this (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    calc _ ≤ |p * A| + |q * B| + |x * (q * A + p * B)| := by
          refine (abs_sub _ _).trans ?_
          gcongr; exact abs_add_le _ _
      _ ≤ _ := by nlinarith
  have hAB : δ ^ 2 * H ^ 2 ≤ A * B := by
    have := mul_le_mul hAδ hBδ (by positivity) hA0.le
    nlinarith
  have hA'B' : (δ * H / 2) ^ 2 ≤ (A + p) * (B + q) := by
    have := mul_le_mul hA' hB' (by positivity) hA'0.le
    nlinarith
  refine ⟨?_, ?_⟩
  · have := abs_div_le_of hU hAB (by positivity)
    calc _ ≤ 2 * (|p| + |q|) * H / (δ ^ 2 * H ^ 2) := this
      _ = _ := by field_simp
  · rw [cosA_shift_identity A B C p q hA0.ne' hB0.ne' hA'0.ne' hB'0.ne']
    set V := (p ^ 2 + q ^ 2) / 2 - x * p * q with hV
    have hVb : |V| ≤ p ^ 2 + q ^ 2 := by
      have : |x * p * q| ≤ |p| * |q| := by
        rw [abs_mul, abs_mul]
        calc |x| * |p| * |q| ≤ 1 * |p| * |q| := by gcongr
          _ = _ := by ring
      have h2 : |p| * |q| ≤ (p ^ 2 + q ^ 2) / 2 := by
        nlinarith [sq_nonneg (|p| - |q|), sq_abs p, sq_abs q]
      refine (abs_sub _ _).trans ?_
      rw [abs_of_nonneg (by positivity)]
      linarith
    have hW : |q * A + p * B + p * q| ≤ (|p| + |q| + |p| * |q|) * H := by
      have e1 : |q * A + p * B| ≤ (|q| + |p|) * H := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_pos hA0, abs_of_pos hB0]
        nlinarith [mul_le_mul_of_nonneg_left hAH (abs_nonneg q),
          mul_le_mul_of_nonneg_left hBH (abs_nonneg p)]
      have e2 : |p * q| = |p| * |q| := abs_mul _ _
      have e3 : |p| * |q| ≤ |p| * |q| * H := by nlinarith [mul_nonneg (abs_nonneg p) (abs_nonneg q)]
      refine (abs_add_le _ _).trans ?_
      nlinarith
    have t1 : |V / ((A + p) * (B + q))| ≤ (p ^ 2 + q ^ 2) / (δ * H / 2) ^ 2 :=
      abs_div_le_of hVb hA'B' (by positivity)
    have t2 : |(p * A + q * B - x * (q * A + p * B)) * (q * A + p * B + p * q) /
        (A * B * ((A + p) * (B + q)))| ≤
        (2 * (|p| + |q|) * H) * ((|p| + |q| + |p| * |q|) * H) / (δ ^ 2 * H ^ 2 * (δ * H / 2) ^ 2) := by
      refine abs_div_le_of ?_ ?_ (by positivity)
      · rw [abs_mul]
        exact mul_le_mul hU hW (abs_nonneg _) (by positivity)
      · exact mul_le_mul hAB hA'B' (by positivity) (by positivity)
    refine (abs_sub _ _).trans ?_
    have e1 : (p ^ 2 + q ^ 2) / (δ * H / 2) ^ 2 = 4 * (p ^ 2 + q ^ 2) / δ ^ 2 / H ^ 2 := by
      field_simp; ring
    have e2 : (2 * (|p| + |q|) * H) * ((|p| + |q| + |p| * |q|) * H) /
        (δ ^ 2 * H ^ 2 * (δ * H / 2) ^ 2) =
        4 * (2 * (|p| + |q|)) * (|p| + |q| + |p| * |q|) / δ ^ 4 / H ^ 2 := by
      field_simp; ring
    rw [e1] at t1; rw [e2] at t2
    calc _ ≤ _ + _ := add_le_add t1 t2
      _ = _ := by ring

/-- `x ↦ d^f_{nm}(arccos x)` is real analytic on `(-1,1)` for admissible `f, m, n`
(`f ± m`, `f ± n` natural numbers). -/
theorem analyticOnNhd_wignerSmallDx_hlab (f m n : ℚ)
    (hlab : IsNat (f + m) ∧ IsNat (f - m) ∧ IsNat (f + n) ∧ IsNat (f - n)) :
    AnalyticOnNhd ℝ (wignerSmallDx f n m) (Set.Ioo (-1 : ℝ) 1) := by
  obtain ⟨⟨a1, h1⟩, ⟨a2, h2⟩, ⟨a3, h3⟩, ⟨a4, h4⟩⟩ := hlab
  have hα : |n - m| = ((((a2 : ℤ) - a4).natAbs : ℕ) : ℚ) := by
    rw [Nat.cast_natAbs]; push_cast
    congr 1; linarith
  have hβ : |n + m| = ((((a3 : ℤ) - a2).natAbs : ℕ) : ℚ) := by
    rw [Nat.cast_natAbs]; push_cast
    congr 1; linarith
  have hk : ∃ k : ℕ, f = max |n| |m| + k := by
    rcases le_total |m| |n| with h | h
    · rw [max_eq_left h]
      rcases abs_cases n with ⟨hn, _⟩ | ⟨hn, _⟩
      · exact ⟨a4, by rw [hn]; linarith⟩
      · exact ⟨a3, by rw [hn]; linarith⟩
    · rw [max_eq_right h]
      rcases abs_cases m with ⟨hn, _⟩ | ⟨hn, _⟩
      · exact ⟨a2, by rw [hn]; linarith⟩
      · exact ⟨a1, by rw [hn]; linarith⟩
  obtain ⟨k, hk⟩ := hk
  exact analyticOnNhd_wignerSmallDx_of_labels n m f k hk _ _ hα hβ

/-- The error budget of `eq:Fludedefect` (pure algebra). -/
theorem flude_assembly {ρ Φ d0 d1 dF t T r M0 R0 a1 a2 a3 a4 : ℝ} (h1 : |ρ - 1 - r| ≤ a1)
    (hd0 : |d0| ≤ M0) (hρ : |ρ| ≤ R0) (hΦ : |Φ - d0| ≤ a2) (hF : |dF - d0 - d1 * t| ≤ a3)
    (hd1 : |d1| ≤ M0) (ht : |t - T| ≤ a4) :
    |ρ * Φ - dF - (r * d0 - T * d1)| ≤ a1 * M0 + R0 * a2 + a3 + M0 * a4 := by
  have e : ρ * Φ - dF - (r * d0 - T * d1) =
      (ρ - 1 - r) * d0 + ρ * (Φ - d0) - (dF - d0 - d1 * t) - d1 * (t - T) := by ring
  rw [e]
  have b1 : |(ρ - 1 - r) * d0| ≤ a1 * M0 := by
    rw [abs_mul]; exact mul_le_mul h1 hd0 (abs_nonneg _) ((abs_nonneg _).trans h1)
  have b2 : |ρ * (Φ - d0)| ≤ R0 * a2 := by
    rw [abs_mul]; exact mul_le_mul hρ hΦ (abs_nonneg _) ((abs_nonneg _).trans hρ)
  have b4 : |d1 * (t - T)| ≤ M0 * a4 := by
    rw [abs_mul]; exact mul_le_mul hd1 ht (abs_nonneg _) ((abs_nonneg _).trans hd1)
  calc _ ≤ |(ρ - 1 - r) * d0 + ρ * (Φ - d0) - (dF - d0 - d1 * t)| + |d1 * (t - T)| := abs_sub _ _
    _ ≤ |(ρ - 1 - r) * d0 + ρ * (Φ - d0)| + |dF - d0 - d1 * t| + |d1 * (t - T)| := by
        gcongr; exact abs_sub _ _
    _ ≤ (|(ρ - 1 - r) * d0| + |ρ * (Φ - d0)|) + |dF - d0 - d1 * t| + |d1 * (t - T)| := by
        gcongr; exact abs_add_le _ _
    _ ≤ _ := by linarith

/-- On the cone `T_δ` the centred cosine stays a fixed distance from `±1`. -/
theorem cone_cos_bounds {A B C H δ : ℝ} (hδ : 0 < δ) (hH : 0 < H) (hA : δ * H ≤ A) (hB : δ * H ≤ B)
    (h1 : δ * H ≤ A + B - C) (h2 : δ * H ≤ A + C - B) (h3 : δ * H ≤ B + C - A) (hAH : A ≤ H)
    (hBH : B ≤ H) (hHS : H ≤ A + B + C) :
    δ ^ 2 / 2 ≤ 1 - cosA A B C ∧ δ / 2 ≤ 1 + cosA A B C := by
  have hA0 : 0 < A := lt_of_lt_of_le (by positivity) hA
  have hB0 : 0 < B := lt_of_lt_of_le (by positivity) hB
  have hAB : 0 < 2 * A * B := by positivity
  have hABle : 2 * A * B ≤ 2 * H ^ 2 := by nlinarith [mul_le_mul hAH hBH hB0.le hH.le]
  have e1 : 1 - cosA A B C = ((B + C - A) * (A + C - B)) / (2 * A * B) := by
    unfold cosA; field_simp; ring
  have e2 : 1 + cosA A B C = ((A + B - C) * (A + B + C)) / (2 * A * B) := by
    unfold cosA; field_simp; ring
  constructor
  · rw [e1, le_div_iff₀ hAB]
    have p3 : 0 ≤ B + C - A := le_trans (by positivity) h3
    have p2 : 0 ≤ A + C - B := le_trans (by positivity) h2
    have := mul_le_mul h3 h2 (by positivity) p3
    nlinarith [mul_le_mul_of_nonneg_left hABle (by positivity : (0 : ℝ) ≤ δ ^ 2 / 2)]
  · rw [e2, le_div_iff₀ hAB]
    have p1 : 0 ≤ A + B - C := le_trans (by positivity) h1
    have := mul_le_mul h1 hHS hH.le p1
    nlinarith [mul_le_mul_of_nonneg_left hABle (by positivity : (0 : ℝ) ≤ δ / 2),
      mul_pos hδ hH, mul_pos (mul_pos hδ hH) hH, mul_pos hδ hH]

/-- The normalisation ratio `√((1+a)(1+b))`, `a = f/(2A)`, `b = f/(2B)`, equals `1 + r + O(H⁻²)`
with `r = (f/4)(A⁻¹+B⁻¹)` and is bounded, on `δH ≤ A, B`, `H ≥ 1`. -/
theorem flude_norm_bounds {A B H δ f : ℝ} (hδ : 0 < δ) (hf : 0 ≤ f) (hH1 : 1 ≤ H)
    (hAδ : δ * H ≤ A) (hBδ : δ * H ≤ B) :
    |Real.sqrt ((1 + f / (2 * A)) * (1 + f / (2 * B))) - 1 - f / 4 * (1 / A + 1 / B)| ≤
        f ^ 2 / (32 * δ ^ 2) / H ^ 2 ∧
      |Real.sqrt ((1 + f / (2 * A)) * (1 + f / (2 * B)))| ≤
        1 + f / (2 * δ) + f ^ 2 / (32 * δ ^ 2) := by
  have hH0 : 0 < H := by linarith
  have hA0 : 0 < A := lt_of_lt_of_le (by positivity) hAδ
  have hB0 : 0 < B := lt_of_lt_of_le (by positivity) hBδ
  set a : ℝ := f / (2 * A) with ha
  set b : ℝ := f / (2 * B) with hb
  set cc : ℝ := f / (2 * δ * H) with hcc
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  have hac : a ≤ cc := by
    rw [ha, hcc]
    exact div_le_div_of_nonneg_left hf (by positivity) (by linarith)
  have hbc : b ≤ cc := by
    rw [hb, hcc]
    exact div_le_div_of_nonneg_left hf (by positivity) (by linarith)
  have hcc0 : 0 ≤ cc := by positivity
  have hsq := sqrt_one_add_mul_bound ha0 hb0
  have hab2 : (a - b) ^ 2 ≤ cc ^ 2 := by
    have : |a - b| ≤ cc := by rw [abs_le]; constructor <;> linarith
    calc (a - b) ^ 2 = |a - b| ^ 2 := (sq_abs _).symm
      _ ≤ cc ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
  have hrr : f / 4 * (1 / A + 1 / B) = (a + b) / 2 := by rw [ha, hb]; field_simp; ring
  have hcc2 : cc ^ 2 / 8 = f ^ 2 / (32 * δ ^ 2) / H ^ 2 := by rw [hcc]; field_simp; ring
  refine ⟨?_, ?_⟩
  · rw [hrr]
    refine hsq.trans ?_
    rw [← hcc2]; linarith
  · have hccle : cc ≤ f / (2 * δ) := by
      have h2δ : (0 : ℝ) < 2 * δ := by positivity
      have h3 : 2 * δ ≤ 2 * δ * H := by
        have := mul_le_mul_of_nonneg_left hH1 h2δ.le
        linarith
      rw [hcc]
      exact div_le_div_of_nonneg_left hf h2δ h3
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    have h := (abs_le.mp hsq).2
    have hc2 : cc ^ 2 / 8 ≤ f ^ 2 / (32 * δ ^ 2) := by
      rw [hcc2]
      exact div_le_self (by positivity) (one_le_pow₀ hH1)
    have : (a - b) ^ 2 / 8 ≤ cc ^ 2 / 8 := by linarith
    linarith

/-- Total shift bound: `x_F - x = T + e`, `|t| ≤ c₁/H`, `|t - T| ≤ K₁/H²`, with
`T = ½[(m/A + n/B) - x(n/A + m/B)]`. -/
theorem flude_shift_total (A B C H δ n m : ℝ) (hδ : 0 < δ) (hH : 1 ≤ H) (hAH : A ≤ H) (hBH : B ≤ H)
    (hAδ : δ * H ≤ A) (hBδ : δ * H ≤ B) (hx : |cosA A B C| ≤ 1) (hnm : |n| + |m| ≤ δ * H) :
    |cosA (A + n / 2) (B + m / 2) C - cosA A B C -
        1 / 2 * ((m / A + n / B) - cosA A B C * (n / A + m / B))| ≤
        (4 * ((n / 2) ^ 2 + (m / 2) ^ 2) / δ ^ 2 +
          4 * (2 * (|n / 2| + |m / 2|)) * (|n / 2| + |m / 2| + |n / 2| * |m / 2|) / δ ^ 4) / H ^ 2 ∧
    |cosA (A + n / 2) (B + m / 2) C - cosA A B C| ≤
      (2 * (|n / 2| + |m / 2|) / δ ^ 2 +
        (4 * ((n / 2) ^ 2 + (m / 2) ^ 2) / δ ^ 2 +
          4 * (2 * (|n / 2| + |m / 2|)) * (|n / 2| + |m / 2| + |n / 2| * |m / 2|) / δ ^ 4)) / H := by
  have hH0 : 0 < H := by linarith
  have hA0 : 0 < A := lt_of_lt_of_le (by positivity) hAδ
  have hB0 : 0 < B := lt_of_lt_of_le (by positivity) hBδ
  have hp2 : 2 * |n / 2| ≤ δ * H := by
    rw [abs_div, abs_two]; linarith [abs_nonneg m]
  have hq2 : 2 * |m / 2| ≤ δ * H := by
    rw [abs_div, abs_two]; linarith [abs_nonneg n]
  obtain ⟨hT, he⟩ := cosA_shift_bounds A B C (n / 2) (m / 2) H δ hδ hH hAH hBH hAδ hBδ hx hp2 hq2
  have hTform : (n / 2 * A + m / 2 * B - cosA A B C * (m / 2 * A + n / 2 * B)) / (A * B) =
      1 / 2 * ((m / A + n / B) - cosA A B C * (n / A + m / B)) := by
    field_simp; ring
  rw [hTform] at hT he
  refine ⟨he, ?_⟩
  set T : ℝ := 1 / 2 * ((m / A + n / B) - cosA A B C * (n / A + m / B)) with hTdef
  set t : ℝ := cosA (A + n / 2) (B + m / 2) C - cosA A B C with htdef
  set u0 : ℝ := 2 * (|n / 2| + |m / 2|) with hu0
  set K1 : ℝ := 4 * ((n / 2) ^ 2 + (m / 2) ^ 2) / δ ^ 2 +
    4 * (2 * (|n / 2| + |m / 2|)) * (|n / 2| + |m / 2| + |n / 2| * |m / 2|) / δ ^ 4 with hK1
  have hK1n : 0 ≤ K1 := by positivity
  have : |t| ≤ |T| + |t - T| := by
    calc |t| = |T + (t - T)| := by rw [add_sub_cancel]
      _ ≤ _ := abs_add_le _ _
  have h1' : |T| ≤ u0 / δ ^ 2 / H := by
    calc |T| ≤ u0 / (δ ^ 2 * H) := hT
      _ = _ := by field_simp
  have h2' : K1 / H ^ 2 ≤ K1 / H :=
    div_le_div_of_nonneg_left hK1n hH0 (le_self_pow₀ hH two_ne_zero)
  calc |t| ≤ _ := this
    _ ≤ u0 / δ ^ 2 / H + K1 / H := add_le_add h1' (he.trans h2')
    _ = _ := by ring

/-- The analytic core of `eq:Fludedefect`: for any `D` analytic on `(-1,1)`, any `f ≥ 0` and `n, m`,
and any `Φ` with `Φ = D(x) + O(H^{-2})` on the cone `T_δ` (`x = cosA A B C`), the rescaled and
shifted quantity `√((1+f/(2A))(1+f/(2B))) Φ - D(x_F)` equals `r D(x) - T D'(x) + O(H^{-2})`,
`r = (f/4)(A⁻¹+B⁻¹)`, `T = ½[(m/A + n/B) - x(n/A + m/B)]`, `x_F = cosA (A+n/2) (B+m/2) C`. -/
theorem flude_core (D : ℝ → ℝ) (hD : AnalyticOnNhd ℝ D (Ioo (-1 : ℝ) 1)) {δ : ℝ} (hδ : 0 < δ)
    (f n m C1 : ℝ) (hf : 0 ≤ f) :
    ∃ C H₀ : ℝ, ∀ A B C' H Φ : ℝ, H₀ ≤ H → δ * H ≤ A → δ * H ≤ B → δ * H ≤ A + B - C' →
      δ * H ≤ A + C' - B → δ * H ≤ B + C' - A → A ≤ H → B ≤ H → H ≤ A + B + C' →
      |Φ - D (cosA A B C')| ≤ C1 / H ^ 2 →
      |Real.sqrt ((1 + f / (2 * A)) * (1 + f / (2 * B))) * Φ - D (cosA (A + n / 2) (B + m / 2) C') -
          ((f / 4 * (1 / A + 1 / B)) * D (cosA A B C') -
            (1 / 2 * ((m / A + n / B) - cosA A B C' * (n / A + m / B))) *
              deriv D (cosA A B C'))| ≤ C / H ^ 2 := by
  set η : ℝ := δ ^ 2 / 4 with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨ρ, hρ, M, hM⟩ := taylor_two_uniform D hD hη0
  have hK : IsCompact (Icc (-1 + η) (1 - η)) := isCompact_Icc
  have hKsub : Icc (-1 + η) (1 - η) ⊆ Ioo (-1 : ℝ) 1 := fun z hz =>
    ⟨by linarith [hz.1], by linarith [hz.2]⟩
  obtain ⟨M1, hM1⟩ := hK.exists_bound_of_continuousOn (hD.continuousOn.mono hKsub)
  obtain ⟨M2, hM2⟩ := hK.exists_bound_of_continuousOn ((hD.deriv).continuousOn.mono hKsub)
  set M0 : ℝ := max M1 M2 with hM0
  set K1 : ℝ := 4 * ((n / 2) ^ 2 + (m / 2) ^ 2) / δ ^ 2 +
    4 * (2 * (|n / 2| + |m / 2|)) * (|n / 2| + |m / 2| + |n / 2| * |m / 2|) / δ ^ 4 with hK1
  set c1 : ℝ := 2 * (|n / 2| + |m / 2|) / δ ^ 2 + K1 with hc1
  have hc1n : 0 ≤ c1 := by positivity
  have hK1n : 0 ≤ K1 := by positivity
  set R0 : ℝ := 1 + f / (2 * δ) + f ^ 2 / (32 * δ ^ 2) with hR0
  refine ⟨f ^ 2 / (32 * δ ^ 2) * M0 + R0 * C1 + |M| * c1 ^ 2 + M0 * K1,
    max (max 1 ((|n| + |m|) / δ)) (c1 / ρ), ?_⟩
  intro A B C' H Φ hH hAδ hBδ h1 h2 h3 hAH hBH hHS hΦ
  have hH1 : 1 ≤ H := (le_max_left _ _).trans ((le_max_left _ _).trans hH)
  have hH0 : 0 < H := by linarith
  have hHn : (|n| + |m|) / δ ≤ H := ((le_max_right _ _).trans (le_max_left _ _)).trans hH
  have hHρ : c1 / ρ ≤ H := (le_max_right _ _).trans hH
  obtain ⟨hx1, hx2⟩ := cone_cos_bounds hδ hH0 hAδ hBδ h1 h2 h3 hAH hBH hHS
  have hδ1 : δ ≤ 1 := by
    have : δ * H ≤ H := hAδ.trans hAH
    nlinarith
  have e1 : δ ^ 2 / 4 ≤ δ / 2 := by nlinarith
  have e2 : δ ^ 2 / 4 ≤ δ ^ 2 / 2 := by nlinarith [sq_nonneg δ]
  have hxK : cosA A B C' ∈ Icc (-1 + η) (1 - η) := ⟨by linarith, by linarith⟩
  have hxabs : |cosA A B C'| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [sq_nonneg δ]
  have hd0 : |D (cosA A B C')| ≤ M0 := by
    have := hM1 _ hxK; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)
  have hd1 : |deriv D (cosA A B C')| ≤ M0 := by
    have := hM2 _ hxK; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_right _ _)
  have hnm : |n| + |m| ≤ δ * H := by
    have := (div_le_iff₀ hδ).mp hHn; linarith
  obtain ⟨ht, htb⟩ := flude_shift_total A B C' H δ n m hδ hH1 hAH hBH hAδ hBδ hxabs hnm
  obtain ⟨hg1, hg2⟩ := flude_norm_bounds hδ hf hH1 hAδ hBδ
  have htρ : |cosA (A + n / 2) (B + m / 2) C' - cosA A B C'| ≤ ρ := by
    refine htb.trans ?_
    rw [div_le_iff₀ hH0]
    have := (div_le_iff₀ hρ).mp hHρ
    linarith [mul_comm H ρ]
  have hF : |D (cosA A B C' + (cosA (A + n / 2) (B + m / 2) C' - cosA A B C')) - D (cosA A B C') -
      deriv D (cosA A B C') * (cosA (A + n / 2) (B + m / 2) C' - cosA A B C')| ≤
      |M| * (c1 / H) ^ 2 := by
    refine (hM _ hxK _ htρ).trans ?_
    calc M * _ ^ 2 ≤ |M| * _ ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self M) (sq_nonneg _)
      _ = |M| * |cosA (A + n / 2) (B + m / 2) C' - cosA A B C'| ^ 2 := by rw [sq_abs]
      _ ≤ |M| * (c1 / H) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) htb 2) (abs_nonneg M)
  have key := flude_assembly hg1 hd0 hg2 hΦ hF hd1 ht
  rw [add_sub_cancel] at key
  refine key.trans (le_of_eq ?_)
  simp only [hc1, hK1, hR0, hM0]
  field_simp

/-- Flude's normalised kernel `Ψ_f = (-1)^ξ √(ω_aω_b) W_f`, `ω_a = 2a+n+f+1 = 2A+f`,
`ω_b = 2B+f` (`eq:Fludenorm`), `ξ = a+b+c+f+n`. -/
noncomputable def Psi6 (a b c f m n : ℚ) : ℝ :=
  sgn (a + b + c + f + n) * Real.sqrt ((2 * wA a n + f) * (2 * wB b m + f)) * W6 a b c f m n

/-- Flude's angle `x_F = cos φ_F = ((A+n/2)² + (B+m/2)² - C²)/(2(A+n/2)(B+m/2))`
(`eq:Fludeangle`). -/
noncomputable def xFlude (a b c m n : ℚ) : ℝ :=
  cosA (wA a n + (n : ℝ) / 2) (wB b m + (m : ℝ) / 2) (wC c)

/-- `Ψ_f = √((2A+f)(2B+f))/(2√(AB)) · Φ_f`. -/
theorem Psi6_eq_mul_Phi6 (a b c f m n : ℚ) (hf : 0 ≤ f) (hA : 0 < wA a n) (hB : 0 < wB b m) :
    Psi6 a b c f m n =
      Real.sqrt ((1 + (f : ℝ) / (2 * wA a n)) * (1 + (f : ℝ) / (2 * wB b m))) * Phi6 a b c f m n := by
  unfold Psi6 Phi6
  have hAB : 0 < wA a n * wB b m := mul_pos hA hB
  have h1 : (2 * wA a n + (f : ℝ)) * (2 * wB b m + (f : ℝ)) =
      (2 * Real.sqrt (wA a n * wB b m)) ^ 2 *
        ((1 + (f : ℝ) / (2 * wA a n)) * (1 + (f : ℝ) / (2 * wB b m))) := by
    rw [mul_pow, Real.sq_sqrt hAB.le]
    field_simp
  have hnn : 0 ≤ (1 + (f : ℝ) / (2 * wA a n)) * (1 + (f : ℝ) / (2 * wB b m)) := by
    have : (0 : ℝ) ≤ f := by exact_mod_cast hf
    positivity
  rw [h1, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  ring

/-- **`sec:6jFludedefect`, `eq:Fludedefect`.**  Fix admissible `f, m, n` and `δ > 0`.  With
`A = wA a n`, `B = wB b m`, `C = wC c`, `Λ = A+B+C`, `α = A/Λ`, `β = B/Λ`, `x = cosA A B C`,
`d = d^f_{nm}(arccos ·)` (`wignerSmallDx f n m`), Flude's `Ψ_f` (`Psi6`) and angle `x_F` (`xFlude`),

`Ψ_f - d(x_F) = Λ⁻¹ [ r_F d(x) - δ_F d'(x) ] + O(H^{-2})`,

`r_F = (f/4)(α⁻¹+β⁻¹)` (`eq:Fludedefect` with `r_F` of the display before it) and
`δ_F = ½[(m/α + n/β) - x(n/α + m/β)]` (`eq:deltaF`), uniformly over the physical triples with
`H = max(A,B,C) ≥ H₀` in `𝒯_δ` (`δ H ≤ min(A,B,C,A+B-C,A+C-B,B+C-A)`).  Since `H ≤ Λ ≤ 3H` on `𝒯_δ`
the remainder is `O(Λ⁻²)` as in the paper.  Derived, as in the paper, from `thm_6jeven`
(`Phi6_even_expansion_cone` with `R = 1`, `G_{f,0} = d`), the exact `Ψ_f = √((2A+f)(2B+f))/(2√(AB)) Φ_f`
(`Psi6_eq_mul_Phi6`), an exact algebraic identity for `x_F - x` (`cosA_shift_identity`) and a
uniform Taylor bound for `d` (`taylor_two_uniform`, real analyticity of `d` on `(-1,1)`:
`analyticOnNhd_wignerSmallDx_hlab`); the first-order coefficients are exactly those of the paper
(`flude_core`).  This statement is exactly that the conventional variables have a generic
`Λ⁻¹` defect `r_F d - δ_F d'` (its non-vanishing is not part of the statement). -/
theorem sec_6jFludedefect (f m n : ℚ)
    (hlab : IsNat (f + m) ∧ IsNat (f - m) ∧ IsNat (f + n) ∧ IsNat (f - n)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C H₀ : ℝ, ∀ a b c : ℚ, IsTri f (b + m) b → IsTri f a (a + n) → IsTri c a b →
      IsTri c (b + m) (a + n) → ∀ A B C' : ℝ, A = wA a n → B = wB b m → C' = wC c →
      H₀ ≤ Hscale A B C' → δ * Hscale A B C' ≤ Tmin A B C' →
      |Psi6 a b c f m n - wignerSmallDx f n m (xFlude a b c m n) -
          (1 / (A + B + C')) *
            ((f / 4 * (1 / (A / (A + B + C')) + 1 / (B / (A + B + C')))) *
                wignerSmallDx f n m (cosA A B C') -
              (1 / 2 * ((m / (A / (A + B + C')) + n / (B / (A + B + C'))) -
                  cosA A B C' * (n / (A / (A + B + C')) + m / (B / (A + B + C'))))) *
                deriv (wignerSmallDx f n m) (cosA A B C'))| ≤
        C / Hscale A B C' ^ 2 := by
  have hf0 : (0 : ℚ) ≤ f := by
    obtain ⟨⟨p1, h1⟩, ⟨p2, h2⟩, -, -⟩ := hlab
    have : (0 : ℚ) ≤ (p1 : ℚ) + p2 := by positivity
    linarith
  have hD := analyticOnNhd_wignerSmallDx_hlab f m n hlab
  obtain ⟨C1, H1, hΦ⟩ := Phi6_even_expansion_cone f m n hδ 1
  obtain ⟨C2, H2, hcore⟩ := flude_core (wignerSmallDx f n m) hD hδ (f : ℝ) (n : ℝ) (m : ℝ) C1
    (by exact_mod_cast hf0)
  refine ⟨C2, max (max H1 H2) 1, ?_⟩
  intro a b c t1 t2 t3 t4 A B C' hA hB hC hH hT
  subst hA hB hC
  set H := Hscale (wA a n) (wB b m) (wC c) with hHdef
  have hH1 : 1 ≤ H := (le_max_right _ _).trans hH
  have hH0 : 0 < H := by linarith
  have hHH1 : H1 ≤ H := ((le_max_left _ _).trans (le_max_left _ _)).trans hH
  have hHH2 : H2 ≤ H := ((le_max_right _ _).trans (le_max_left _ _)).trans hH
  have hT' := hT
  simp only [Tmin, le_min_iff] at hT'
  obtain ⟨hAδ, hBδ, hCδ, h1, h2, h3⟩ := hT'
  have hAH : wA a n ≤ H := by
    rw [hHdef]; unfold Hscale; exact le_max_left _ _
  have hBH : wB b m ≤ H := by
    rw [hHdef]; unfold Hscale; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hA0 : 0 < wA a n := lt_of_lt_of_le (by positivity) hAδ
  have hB0 : 0 < wB b m := lt_of_lt_of_le (by positivity) hBδ
  have hC0 : 0 < wC c := lt_of_lt_of_le (by positivity) hCδ
  have hHS : H ≤ wA a n + wB b m + wC c := by
    rw [hHdef]; unfold Hscale
    exact max_le (by linarith) (max_le (by linarith) (by linarith))
  obtain ⟨hx1, hx2⟩ := cone_cos_bounds hδ hH0 hAδ hBδ h1 h2 h3 hAH hBH hHS
  have hδ1 : δ ≤ 1 := by
    have : δ * H ≤ H := hAδ.trans hAH
    nlinarith
  have hxI : cosA (wA a n) (wB b m) (wC c) ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> nlinarith [sq_nonneg δ]
  -- `Φ_f = d + O(H⁻²)`
  have hΦ' := hΦ a b c t1 t2 t3 t4 hHH1 hT
  have hG0 : G6even f m n 0 (wA a n) (wB b m) (wC c) = wignerSmallDx f n m (cosA (wA a n) (wB b m) (wC c)) := by
    rw [G6even_zero_eq_dZero6 f m n hlab hA0 hB0 (by linarith)]
    exact dZero6_eq_wignerD f m n hlab.1 hlab.2.1 hlab.2.2.1 hlab.2.2.2 hxI
  simp only [Finset.sum_range_one, hG0, mul_one] at hΦ'
  have hc := hcore (wA a n) (wB b m) (wC c) H (Phi6 a b c f m n) hHH2 hAδ hBδ h1 h2 h3 hAH hBH hHS
    (by simpa using hΦ')
  rw [Psi6_eq_mul_Phi6 a b c f m n hf0 hA0 hB0]
  have hΛ : 0 < wA a n + wB b m + wC c := by linarith
  have e1 : 1 / (wA a n / (wA a n + wB b m + wC c)) = (wA a n + wB b m + wC c) / wA a n := by
    field_simp
  have e2 : 1 / (wB b m / (wA a n + wB b m + wC c)) = (wA a n + wB b m + wC c) / wB b m := by
    field_simp
  have key : (1 / (wA a n + wB b m + wC c)) *
        ((f / 4 * (1 / (wA a n / (wA a n + wB b m + wC c)) + 1 / (wB b m / (wA a n + wB b m + wC c)))) *
            wignerSmallDx f n m (cosA (wA a n) (wB b m) (wC c)) -
          (1 / 2 * (((m : ℝ) / (wA a n / (wA a n + wB b m + wC c)) +
                (n : ℝ) / (wB b m / (wA a n + wB b m + wC c))) -
              cosA (wA a n) (wB b m) (wC c) *
                ((n : ℝ) / (wA a n / (wA a n + wB b m + wC c)) +
                  (m : ℝ) / (wB b m / (wA a n + wB b m + wC c))))) *
            deriv (wignerSmallDx f n m) (cosA (wA a n) (wB b m) (wC c))) =
      ((f : ℝ) / 4 * (1 / wA a n + 1 / wB b m)) *
          wignerSmallDx f n m (cosA (wA a n) (wB b m) (wC c)) -
        (1 / 2 * (((m : ℝ) / wA a n + (n : ℝ) / wB b m) -
            cosA (wA a n) (wB b m) (wC c) * ((n : ℝ) / wA a n + (m : ℝ) / wB b m))) *
          deriv (wignerSmallDx f n m) (cosA (wA a n) (wB b m) (wC c)) := by
    field_simp
  rw [key]
  exact hc

end FormalResearch.Racah

/-- info: 'FormalResearch.Racah.sec_6jFludedefect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.sec_6jFludedefect

/-- info: 'FormalResearch.Racah.flude_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.flude_core
