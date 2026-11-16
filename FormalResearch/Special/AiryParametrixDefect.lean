module

public import FormalResearch.Special.AiryParametrixPointwise
public import FormalResearch.Special.AiryParametrixJets

/-!
# The Airy parametrix defect lemma (window form)

**Setting.**  `A, ζ, g : ℝ → ℝ` and an open `U ⊇ J` (`J` compact), with `A, g ∈ C²(U)`, `ζ ∈ C³(U)` and the
*closed-form amplitude relation*
`g² · A · ζ' · Sh(ζ ζ'²) = 1` on `U`, where `Sh(w) = 2 Ch'(w) = ∑ wⁿ/(2n+1)!` (`langerSinhc`) and
`Ch = langerCosh` (`= cosh √w`).  The row operator is
`(Lψ)(q) = A(q+h/2) ψ(q+h) + A(q-h/2) ψ(q-h) - c(q) ψ(q)` with the *canonical-turn diagonal*
`c(q) = 2 A(q) Ch(ζ(q) ζ'(q)²)` (for `ζ ζ'² = Φ(u-1)` of `LangerPhi`: `c = 2 A u`, the eikonal
`cosh √(ζζ'²) = u`), and the parametrix is `ψ(q) = g(q) Ai(h^{-2/3} ζ(q))`.  A lattice `q_k = q₀ + kh` with
`a_k = A(q_k - h/2)`, `c_k = c(q_k)` gives `jac a c ψ k = (Lψ)(q_k)`.

**Closed-form amplitude.**  `g² A ζ' Sh(ζζ'²) = 1` is exactly `g = (4|ζ|/|D̄|)^{1/4}`,
`D̄ = 4A² - c² = -4A² sinh²η` of W1 est:279 / P3 A:1152 (`sinh²√F = F · Sh(F)²`, `u² - 1 = sinh²`), and
equivalently `(V g²)' = 0`-transport integrated: `V = A S₀(ζ') = A ζ' Sh(ζζ'²)`, `V g² = 1`.

**Main result** (`airyParametrix_defect`).  For every compact `J ⊆ U` there are `K, h₀ > 0` such that for
`h ∈ (0, h₀]`, `q ∈ J`, with `X = h^{-2/3} ζ(q)`,
`|(Lψ)(q)| ≤ K h² (1+|X|)³ airyWt(X)`.

* *Window.* `h² (1+|X|)³` is `O(h^{2 - 3ε})` for `|X| ≤ h^{-ε}` and is **not** small on the whole turn
  neighbourhood (`X ~ h^{-2/3}`): the truncation error of `Ch` (the fifth-order Taylor remainder of the
  exact shift functions) is `ζ³`, i.e. `h² X³`.  The true defect there is `O(h²) ψ` (mpmath sanity run, not
  committed), which needs the `h`-expansion of the shift functions at *fixed* `ζ`
  (the paper's `C(s;ζ,h)`, `S(s;ζ,h)`); this is done in `AiryParametrixUniform*`
  (`airyParametrix_defect_uniform`: `≤ K h² airyWt X` for all real `X`), of which the present window form is
  a weaker corollary (`(1+|X|)³ ≥ 1`).
* *Stages.*  The `h^{5/3}` defect follows from the `h²` statement since `h² ≤ h^{5/3}` for `h ≤ 1`;
  the proof gives the `h²` statement directly because the parity cancellation of the odd orders is purely
  algebraic in the variables `(ζ, s, h)` (`AiryParametrixSkeleton`).
* *Weight.* All `X ∈ ℝ` (oscillatory side included): `airyWt ≍ M/E` of Olver on `x ≤ 0` and `≍ Ai` on
  `x ≥ -1` (`apx_airy_global`).
* *Hypotheses.*  The closed-form relation `g² A ζ' Sh(ζζ'²) = 1` on `U` gives only `g, A, ζ', Sh ≠ 0` and
  `A ζ' Sh > 0`; `A > 0` is needed by the consumer for the lattice recurrence;
  `c` is the displayed formula.  Constants `K, h₀` are existential and depend on `J, U, A, ζ, g`.

Not formalised here: the `h²` coefficient `ϖ`.  The relation `g² A ζ' Sh(F) = 1` and `Ch(F) = u` for M3's
coordinate `ζ = langerZeta u c` and amplitude `g = langerAmp u A c` (with `Sh(F) = sinh√F/√F`) is derived in
`AiryParametrixLanger` (`langer_hrel`), which also gives the combined window-form defect; the uniform
`O(h²)ψ` bound on the whole turn neighbourhood is `AiryParametrixUniform*`.
-/

@[expose] public section

open Set

namespace FormalResearch.Special

lemma apx_rpow {h : ℝ} (hh : 0 < h) :
    ∃ t : ℝ, 0 < t ∧ t ^ 3 = h ∧ h ^ (-(2 / 3 : ℝ)) = (t ^ 2)⁻¹ := by
  refine ⟨h ^ (1 / 3 : ℝ), Real.rpow_pos_of_pos hh _, ?_, ?_⟩
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hh.le]; norm_num
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hh.le, Real.rpow_neg hh.le]; norm_num

lemma apx_prod {a a1 ra b b1 rb h σ A0 A1 ρA g0 g1 ρg : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1)
    (hσ : σ = 1 ∨ σ = -1) (ha : |a| ≤ A0) (ha1 : |a1| ≤ A1) (hra : |ra| ≤ ρA * h ^ 2)
    (hb : |b| ≤ g0) (hb1 : |b1| ≤ g1) (hrb : |rb| ≤ ρg * h ^ 2) :
    |(a + σ * (h / 2) * a1 + ra) * (b + σ * h * b1 + rb) - (a * b + σ * h * (a1 * b / 2 + a * b1))| ≤
      (A1 * g1 / 2 + (A0 + A1) * ρg + ρA * (g0 + g1 + ρg)) * h ^ 2 := by
  have hσ2 : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hσ1 : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hA0 : 0 ≤ A0 := (abs_nonneg _).trans ha
  have hA1 : 0 ≤ A1 := (abs_nonneg _).trans ha1
  have hg0 : 0 ≤ g0 := (abs_nonneg _).trans hb
  have hg1 : 0 ≤ g1 := (abs_nonneg _).trans hb1
  have hρA : 0 ≤ ρA := by
    by_contra hneg
    have := mul_neg_of_neg_of_pos (not_le.1 hneg) (pow_pos hh0 2)
    linarith [(abs_nonneg ra).trans hra]
  have hρg : 0 ≤ ρg := by
    by_contra hneg
    have := mul_neg_of_neg_of_pos (not_le.1 hneg) (pow_pos hh0 2)
    linarith [(abs_nonneg rb).trans hrb]
  have key : (a + σ * (h / 2) * a1 + ra) * (b + σ * h * b1 + rb) -
        (a * b + σ * h * (a1 * b / 2 + a * b1)) =
      h ^ 2 * a1 * b1 / 2 + (a + σ * (h / 2) * a1) * rb + ra * (b + σ * h * b1 + rb) := by
    have : σ ^ 2 * h ^ 2 * a1 * b1 / 2 = h ^ 2 * a1 * b1 / 2 := by rw [hσ2]; ring
    linear_combination (h ^ 2 * a1 * b1 / 2) * hσ2
  rw [key]
  have hh2 : h ^ 2 ≤ 1 := pow_le_one₀ hh0.le hh1
  have e1 : |h ^ 2 * a1 * b1 / 2| ≤ (A1 * g1 / 2) * h ^ 2 := by
    rw [abs_div, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ h ^ 2), abs_two]
    have := mul_le_mul ha1 hb1 (abs_nonneg _) hA1
    nlinarith [sq_nonneg h]
  have e2 : |(a + σ * (h / 2) * a1) * rb| ≤ (A0 + A1) * ρg * h ^ 2 := by
    rw [abs_mul]
    have h1 : |a + σ * (h / 2) * a1| ≤ A0 + A1 := by
      calc |a + σ * (h / 2) * a1| ≤ |a| + |σ * (h / 2) * a1| := abs_add_le _ _
        _ ≤ A0 + A1 := by
            rw [abs_mul, abs_mul, hσ1, abs_div, abs_of_pos hh0]
            have : h / |(2:ℝ)| * |a1| ≤ A1 := by
              rw [abs_two]; nlinarith [abs_nonneg a1]
            linarith
    calc |a + σ * (h / 2) * a1| * |rb| ≤ (A0 + A1) * (ρg * h ^ 2) :=
          mul_le_mul h1 hrb (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have e3 : |ra * (b + σ * h * b1 + rb)| ≤ ρA * (g0 + g1 + ρg) * h ^ 2 := by
    rw [abs_mul]
    have h1 : |b + σ * h * b1 + rb| ≤ g0 + g1 + ρg := by
      calc |b + σ * h * b1 + rb| ≤ |b| + |σ * h * b1| + |rb| := by
            calc _ ≤ |b + σ * h * b1| + |rb| := abs_add_le _ _
              _ ≤ _ := by linarith [abs_add_le b (σ * h * b1)]
        _ ≤ g0 + g1 + ρg := by
            rw [abs_mul, abs_mul, hσ1, abs_of_pos hh0]
            have : 1 * h * |b1| ≤ g1 := by nlinarith [abs_nonneg b1]
            nlinarith [hrb, mul_le_mul_of_nonneg_left hh2 hρg]
    calc |ra| * |b + σ * h * b1 + rb| ≤ (ρA * h ^ 2) * (g0 + g1 + ρg) :=
          mul_le_mul hra h1 (abs_nonneg _) (by positivity)
      _ = _ := by ring
  calc _ ≤ |h ^ 2 * a1 * b1 / 2| + |(a + σ * (h / 2) * a1) * rb| + |ra * (b + σ * h * b1 + rb)| :=
        abs_add_three _ _ _
    _ ≤ _ := by nlinarith [e1, e2, e3]

/-- `|D| ≤ M h³ → |D/h| ≤ M h²`. -/
lemma apx_div_h {D h M : ℝ} (hh : 0 < h) (hD : |D| ≤ M * h ^ 3) : |D / h| ≤ M * h ^ 2 := by
  rw [abs_div, abs_of_pos hh, div_le_iff₀ hh]
  calc |D| ≤ M * h ^ 3 := hD
    _ = M * h ^ 2 * h := by ring

/-- `|σ z₁ + h z₂/2 + e| ≤ Z₁ + Z₂/2 + Z₃` for `σ = ±1`, `h ≤ 1`, `|e| ≤ Z₃ h²`. -/
lemma apx_sp_bound {σ z1 z2 e h Z1 Z2 Z3 : ℝ} (hσ : |σ| = 1) (hh0 : 0 < h) (hh1 : h ≤ 1)
    (hz1 : |z1| ≤ Z1) (hz2 : |z2| ≤ Z2) (he : |e| ≤ Z3 * h ^ 2) (hZ3 : 0 ≤ Z3) :
    |σ * z1 + h * z2 / 2 + e| ≤ Z1 + Z2 / 2 + Z3 := by
  have h1 : |σ * z1| ≤ Z1 := by rw [abs_mul, hσ, one_mul]; exact hz1
  have h2 : |h * z2 / 2| ≤ Z2 / 2 := by
    rw [abs_div, abs_mul, abs_of_pos hh0, abs_two]
    have := mul_le_mul hh1 hz2 (abs_nonneg _) zero_le_one
    linarith
  have h3 : |e| ≤ Z3 := by
    have := mul_le_mul_of_nonneg_left (pow_le_one₀ hh0.le hh1 (n := 2)) hZ3
    linarith
  calc |σ * z1 + h * z2 / 2 + e| ≤ |σ * z1 + h * z2 / 2| + |e| := abs_add_le _ _
    _ ≤ |σ * z1| + |h * z2 / 2| + |e| := by linarith [abs_add_le (σ * z1) (h * z2 / 2)]
    _ ≤ _ := by linarith

/-- The bounds on `G₀ = a b`, `G₁ = a₁ b/2 + a b₁`, `z₂`. -/
lemma apx_Gjet_bound {a a1 b b1 A0 A1 g0 g1 : ℝ} (ha : |a| ≤ A0) (ha1 : |a1| ≤ A1) (hb : |b| ≤ g0)
    (hb1 : |b1| ≤ g1) :
    |a * b| ≤ A0 * g0 ∧ |a1 * b / 2 + a * b1| ≤ A1 * g0 / 2 + A0 * g1 := by
  have hA0 : 0 ≤ A0 := (abs_nonneg _).trans ha
  have hA1 : 0 ≤ A1 := (abs_nonneg _).trans ha1
  constructor
  · rw [abs_mul]; exact mul_le_mul ha hb (abs_nonneg _) hA0
  · calc |a1 * b / 2 + a * b1| ≤ |a1 * b / 2| + |a * b1| := abs_add_le _ _
      _ ≤ _ := by
          rw [abs_div, abs_mul, abs_mul, abs_two]
          have h1 := mul_le_mul ha1 hb (abs_nonneg _) hA1
          have h2 := mul_le_mul ha hb1 (abs_nonneg _) hA0
          linarith

/-- **Real-variable core of the defect lemma.**  All the Taylor data enter as hypotheses on reals. -/
theorem apx_defect_core (Z0 Z1 Z2 Z3 A0 A1 A2 g0 g1 g2 : ℝ) (hZ0 : 0 ≤ Z0) (hZ1 : 0 ≤ Z1)
    (hZ2 : 0 ≤ Z2) (hZ3 : 0 ≤ Z3) (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2) (hg0 : 0 ≤ g0)
    (hg1 : 0 ≤ g1) (hg2 : 0 ≤ g2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (t zp zm Ap Am gP gM z0 z1 z2 a a1 b b1 : ℝ), 0 < t → t ≤ 1 →
      t * (Z1 + Z2 / 2 + Z3) ≤ 1 →
      |z0| ≤ Z0 → |z1| ≤ Z1 → |z2| ≤ Z2 → |a| ≤ A0 → |a1| ≤ A1 → |b| ≤ g0 → |b1| ≤ g1 →
      |zp - (z0 + z1 * t ^ 3 + z2 * (t ^ 3) ^ 2 / 2)| ≤ Z3 * (t ^ 3) ^ 3 →
      |zm - (z0 + z1 * -t ^ 3 + z2 * (-t ^ 3) ^ 2 / 2)| ≤ Z3 * (t ^ 3) ^ 3 →
      |Ap - (a + a1 * (t ^ 3 / 2))| ≤ A2 * (t ^ 3 / 2) ^ 2 →
      |Am - (a + a1 * -(t ^ 3 / 2))| ≤ A2 * (t ^ 3 / 2) ^ 2 →
      |gP - (b + b1 * t ^ 3)| ≤ g2 * (t ^ 3) ^ 2 →
      |gM - (b + b1 * -t ^ 3)| ≤ g2 * (t ^ 3) ^ 2 →
      2 * (a1 * b / 2 + a * b1) * z1 * (2 * deriv langerCosh (z0 * z1 ^ 2)) +
        (a * b) * z2 * (2 * deriv langerCosh (z0 * z1 ^ 2) +
          2 * (z0 * z1 ^ 2) * (2 * deriv (deriv langerCosh) (z0 * z1 ^ 2))) +
        (a * b) * z1 ^ 4 * (2 * deriv (deriv langerCosh) (z0 * z1 ^ 2)) = 0 →
      |Ap * (gP * airyAi (zp / t ^ 2)) + Am * (gM * airyAi (zm / t ^ 2)) -
          2 * a * langerCosh (z0 * z1 ^ 2) * (b * airyAi (z0 / t ^ 2))| ≤
        K * (t ^ 3) ^ 2 * (1 + |z0 / t ^ 2|) ^ 3 * airyWt (z0 / t ^ 2) := by
  set S : ℝ := Z1 + Z2 / 2 + Z3 with hS
  have hS0 : 0 ≤ S := by positivity
  set B : ℝ := Z2 + A0 * g0 + (A1 * g0 / 2 + A0 * g1) with hB
  have hB0 : 0 ≤ B := by positivity
  set Γ : ℝ := A1 * g1 / 2 + (A0 + A1) * g2 + (A2 / 4) * (g0 + g1 + g2) with hΓ
  have hΓ0 : 0 ≤ Γ := by positivity
  obtain ⟨K, hK0, hpt⟩ := apx_pointwise Z0 S B Z3 Γ hZ0 hS0 hB0 hZ3 hΓ0
  refine ⟨K, hK0, ?_⟩
  intro t zp zm Ap Am gP gM z0 z1 z2 a a1 b b1 ht0 ht1 htS hz0 hz1 hz2 ha ha1 hb hb1 hzp hzm hAp hAm
    hgp hgm hTR
  have hh0 : 0 < t ^ 3 := by positivity
  have hh1 : t ^ 3 ≤ 1 := pow_le_one₀ ht0.le ht1
  -- the increments of `ζ`
  have hep_b : |(zp - z0) / t ^ 3 - (z1 + t ^ 3 * z2 / 2)| ≤ Z3 * (t ^ 3) ^ 2 := by
    have e : (zp - z0) / t ^ 3 - (z1 + t ^ 3 * z2 / 2) =
        (zp - (z0 + z1 * t ^ 3 + z2 * (t ^ 3) ^ 2 / 2)) / t ^ 3 := by
      field_simp; ring
    rw [e]; exact apx_div_h hh0 hzp
  have hem_b : |(zm - z0) / t ^ 3 - (-z1 + t ^ 3 * z2 / 2)| ≤ Z3 * (t ^ 3) ^ 2 := by
    have e : (zm - z0) / t ^ 3 - (-z1 + t ^ 3 * z2 / 2) =
        (zm - (z0 + z1 * -t ^ 3 + z2 * (-t ^ 3) ^ 2 / 2)) / t ^ 3 := by
      field_simp; ring
    rw [e]; exact apx_div_h hh0 hzm
  -- the increments of `G`
  have hGp := apx_prod (a := a) (a1 := a1) (b := b) (b1 := b1)
    (ra := Ap - (a + a1 * (t ^ 3 / 2))) (rb := gP - (b + b1 * t ^ 3))
    (h := t ^ 3) (σ := 1) (A0 := A0) (A1 := A1) (ρA := A2 / 4) (g0 := g0) (g1 := g1) (ρg := g2)
    hh0 hh1 (Or.inl rfl) ha ha1 (by
      calc _ ≤ A2 * (t ^ 3 / 2) ^ 2 := hAp
        _ = A2 / 4 * (t ^ 3) ^ 2 := by ring) hb hb1 hgp
  have hGm := apx_prod (a := a) (a1 := a1) (b := b) (b1 := b1)
    (ra := Am - (a + a1 * -(t ^ 3 / 2))) (rb := gM - (b + b1 * -t ^ 3))
    (h := t ^ 3) (σ := -1) (A0 := A0) (A1 := A1) (ρA := A2 / 4) (g0 := g0) (g1 := g1) (ρg := g2)
    hh0 hh1 (Or.inr rfl) ha ha1 (by
      calc _ ≤ A2 * (t ^ 3 / 2) ^ 2 := hAm
        _ = A2 / 4 * (t ^ 3) ^ 2 := by ring) hb hb1 hgm
  have hgp_b : |Ap * gP - (a * b + t ^ 3 * (a1 * b / 2 + a * b1))| ≤ Γ * (t ^ 3) ^ 2 := by
    have e : Ap * gP - (a * b + t ^ 3 * (a1 * b / 2 + a * b1)) =
        (a + 1 * (t ^ 3 / 2) * a1 + (Ap - (a + a1 * (t ^ 3 / 2)))) *
          (b + 1 * t ^ 3 * b1 + (gP - (b + b1 * t ^ 3))) -
          (a * b + 1 * t ^ 3 * (a1 * b / 2 + a * b1)) := by ring
    rw [e]; exact hGp
  have hgm_b : |Am * gM - (a * b - t ^ 3 * (a1 * b / 2 + a * b1))| ≤ Γ * (t ^ 3) ^ 2 := by
    have e : Am * gM - (a * b - t ^ 3 * (a1 * b / 2 + a * b1)) =
        (a + -1 * (t ^ 3 / 2) * a1 + (Am - (a + a1 * -(t ^ 3 / 2)))) *
          (b + -1 * t ^ 3 * b1 + (gM - (b + b1 * -t ^ 3))) -
          (a * b + -1 * t ^ 3 * (a1 * b / 2 + a * b1)) := by ring
    rw [e]; exact hGm
  have hsp := apx_sp_bound (σ := 1) (by norm_num) hh0 hh1 hz1 hz2 hep_b hZ3
  have hsm := apx_sp_bound (σ := -1) (by norm_num) hh0 hh1 hz1 hz2 hem_b hZ3
  obtain ⟨hG0, hG1⟩ := apx_Gjet_bound ha ha1 hb hb1
  have hz1S : |z1| ≤ S := by rw [hS]; linarith
  have p1 : 0 ≤ A0 * g0 := mul_nonneg hA0 hg0
  have p2 : 0 ≤ A1 * g0 / 2 + A0 * g1 := by positivity
  have hz2B : |z2| ≤ B := by rw [hB]; linarith
  have hG0B : |a * b| ≤ B := by rw [hB]; linarith
  have hG1B : |a1 * b / 2 + a * b1| ≤ B := by rw [hB]; linarith
  have hmain := hpt t z0 z1 z2 (a * b) (a1 * b / 2 + a * b1) _ _ (Ap * gP - (a * b + t ^ 3 * (a1 * b / 2 + a * b1)))
    (Am * gM - (a * b - t ^ 3 * (a1 * b / 2 + a * b1))) ht0 ht1 htS hz0 hz1S hz2B hG0B hG1B hep_b hem_b
    hgp_b hgm_b (by simpa using hsp) (by simpa using hsm) hTR
  have e1 : a * b + t ^ 3 * (a1 * b / 2 + a * b1) +
      (Ap * gP - (a * b + t ^ 3 * (a1 * b / 2 + a * b1))) = Ap * gP := by ring
  have e2 : a * b - t ^ 3 * (a1 * b / 2 + a * b1) +
      (Am * gM - (a * b - t ^ 3 * (a1 * b / 2 + a * b1))) = Am * gM := by ring
  have e3 : z1 + t ^ 3 * z2 / 2 + ((zp - z0) / t ^ 3 - (z1 + t ^ 3 * z2 / 2)) = (zp - z0) / t ^ 3 := by ring
  have e4 : -z1 + t ^ 3 * z2 / 2 + ((zm - z0) / t ^ 3 - (-z1 + t ^ 3 * z2 / 2)) = (zm - z0) / t ^ 3 := by ring
  rw [e1, e2, e3, e4] at hmain
  have e5 : z0 / t ^ 2 + t * ((zp - z0) / t ^ 3) = zp / t ^ 2 := by field_simp; ring
  have e6 : z0 / t ^ 2 + t * ((zm - z0) / t ^ 3) = zm / t ^ 2 := by field_simp; ring
  rw [e5, e6] at hmain
  convert hmain using 2
  ring

/-- **The Airy parametrix defect lemma (window form).**  See the module docstring. -/
theorem airyParametrix_defect {U J : Set ℝ} {ζ A g : ℝ → ℝ} (hU : IsOpen U) (hJ : IsCompact J)
    (hJU : J ⊆ U) (hζ : ContDiffOn ℝ 3 ζ U) (hA : ContDiffOn ℝ 2 A U) (hg : ContDiffOn ℝ 2 g U)
    (hrel : ∀ q ∈ U, g q ^ 2 * A q * deriv ζ q * (2 * deriv langerCosh (ζ q * deriv ζ q ^ 2)) = 1) :
    ∃ K h0 : ℝ, 0 < K ∧ 0 < h0 ∧ ∀ h : ℝ, 0 < h → h ≤ h0 → ∀ q ∈ J,
      |A (q + h / 2) * (g (q + h) * airyAi (h ^ (-(2 / 3 : ℝ)) * ζ (q + h))) +
          A (q - h / 2) * (g (q - h) * airyAi (h ^ (-(2 / 3 : ℝ)) * ζ (q - h))) -
          2 * A q * langerCosh (ζ q * deriv ζ q ^ 2) * (g q * airyAi (h ^ (-(2 / 3 : ℝ)) * ζ q))| ≤
        K * h ^ 2 * (1 + |h ^ (-(2 / 3 : ℝ)) * ζ q|) ^ 3 * airyWt (h ^ (-(2 / 3 : ℝ)) * ζ q) := by
  obtain ⟨Z0, Z1, Z2, Z3, δζ, hZ0, hZ1, hZ2, hZ3, hδζ, hζj⟩ := apx_jet3 hU hζ hJ hJU
  obtain ⟨A0, A1, A2, δA, hA0, hA1, hA2, hδA, hAj⟩ := apx_jet2 hU hA hJ hJU
  obtain ⟨g0, g1, g2, δg, hg0, hg1, hg2, hδg, hgj⟩ := apx_jet2 hU hg hJ hJU
  obtain ⟨K, hK0, hcore⟩ := apx_defect_core Z0 Z1 Z2 Z3 A0 A1 A2 g0 g1 g2 hZ0 hZ1 hZ2 hZ3 hA0 hA1 hA2
    hg0 hg1 hg2
  set S : ℝ := Z1 + Z2 / 2 + Z3 with hS
  have hS0 : 0 ≤ S := by positivity
  set c0 : ℝ := 1 / (S + 1) with hc0
  have hc0pos : 0 < c0 := by positivity
  refine ⟨K + 1, min (min δζ (min (2 * δA) δg)) (min 1 (c0 ^ 3)), by linarith, ?_, ?_⟩
  · exact lt_min (lt_min hδζ (lt_min (by linarith) hδg)) (lt_min one_pos (by positivity))
  intro h hh0 hh0' q hq
  have hhδζ : h ≤ δζ := hh0'.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hhδA : h / 2 ≤ δA := by
    have := hh0'.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    linarith
  have hhδg : h ≤ δg := hh0'.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hh1 : h ≤ 1 := hh0'.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hhc : h ≤ c0 ^ 3 := hh0'.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨t, ht0, ht3, hpow⟩ := apx_rpow hh0
  subst ht3
  have ht1 : t ≤ 1 := by
    by_contra hlt
    have : 1 < t ^ 3 := one_lt_pow₀ (not_le.1 hlt) (by norm_num)
    linarith
  have htc : t ≤ c0 := by
    by_contra hlt
    have : c0 ^ 3 < t ^ 3 := pow_lt_pow_left₀ (not_le.1 hlt) hc0pos.le (by norm_num)
    linarith
  have htS : t * S ≤ 1 := by
    calc t * S ≤ c0 * S := mul_le_mul_of_nonneg_right htc hS0
      _ ≤ 1 := by rw [hc0, one_div, inv_mul_le_iff₀ (by positivity)]; linarith
  obtain ⟨hζ0, hζ1, hζ2, hζT⟩ := hζj q hq
  obtain ⟨hA0q, hA1q, hAT⟩ := hAj q hq
  obtain ⟨hg0q, hg1q, hgT⟩ := hgj q hq
  have hζp := hζT (t ^ 3) (by rw [abs_of_pos hh0]; exact hhδζ)
  have hζm := hζT (-(t ^ 3)) (by rw [abs_neg, abs_of_pos hh0]; exact hhδζ)
  rw [abs_of_pos hh0] at hζp
  rw [abs_neg, abs_of_pos hh0, ← sub_eq_add_neg] at hζm
  have hAp := hAT (t ^ 3 / 2) (by rw [abs_of_pos (by positivity)]; exact hhδA)
  have hAm := hAT (-(t ^ 3 / 2)) (by rw [abs_neg, abs_of_pos (by positivity)]; exact hhδA)
  have hgp := hgT (t ^ 3) (by rw [abs_of_pos hh0]; exact hhδg)
  have hgm := hgT (-(t ^ 3)) (by rw [abs_neg, abs_of_pos hh0]; exact hhδg)
  rw [neg_sq] at hAm hgm
  rw [← sub_eq_add_neg] at hgm hAm
  have hTR := apx_transport hU hζ hA hg hrel (hJU hq)
  have hmain := hcore t (ζ (q + t ^ 3)) (ζ (q - t ^ 3)) (A (q + t ^ 3 / 2)) (A (q - t ^ 3 / 2))
    (g (q + t ^ 3)) (g (q - t ^ 3)) (ζ q) (deriv ζ q) (deriv (deriv ζ) q) (A q) (deriv A q) (g q)
    (deriv g q) ht0 ht1 htS hζ0 hζ1 hζ2 hA0q hA1q hg0q hg1q hζp hζm hAp hAm hgp hgm hTR
  rw [hpow]
  simp only [inv_mul_eq_div]
  have hX : 0 ≤ (t ^ 3) ^ 2 * (1 + |ζ q / t ^ 2|) ^ 3 * airyWt (ζ q / t ^ 2) := by
    have := airyWt_pos (ζ q / t ^ 2)
    positivity
  calc _ ≤ K * (t ^ 3) ^ 2 * (1 + |ζ q / t ^ 2|) ^ 3 * airyWt (ζ q / t ^ 2) := hmain
    _ ≤ _ := by nlinarith [hX]

/-- info: 'FormalResearch.Special.airyParametrix_defect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyParametrix_defect

/-- info: 'FormalResearch.Special.apx_defect_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.apx_defect_core

end FormalResearch.Special
