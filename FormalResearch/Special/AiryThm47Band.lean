module

public import FormalResearch.Special.AiryThm47Block

/-!
# Non-integrability on the band (Theorem 4.7, `SOFT_EDGE_THEOREMS.md`)

`at47_not_integrable_poly_mul`: for `P`, `Q ≠ 0` real polynomials, `ts` a finite set of reals with `m = at47_m P Q` elements
and `p` a complex polynomial of degree `≥ 1`, the function `p(x) N(x)² / ∏_{t ∈ ts}(x - t)` is not integrable on `ℝ`.
Proof: `N² ≳ ` block mass `R^{e+1}√R` on `[-2R,-R]` (`at47_block_integral`, integration by parts and the Airy kernel
`K(-s,-s) ≍ √s`), `|p(x)| ≳ |x|^d`, `|∏| ≲ R^m`, `m = e + 2`; so each dyadic block carries mass `≳ R^{d-1}√R ≥ c`.
All proved; the hypothesis `ts.card = at47_m P Q` is not tied to zeros of `N` (the statement is a pure growth statement).
-/

@[expose] public section

open Polynomial MeasureTheory Filter Topology
open scoped Real

namespace FormalResearch.Special

/-- A nonnegative integrable function cannot have mass `≥ c > 0` on every dyadic block `[-2R,-R]`, `R ≥ R0`. -/
lemma at47_blocks_not_integrable {h : ℝ → ℝ} (hint : Integrable h) (hnn : ∀ x, 0 ≤ h x) {c R0 : ℝ}
    (hc : 0 < c) (hR0 : 0 < R0) (hblock : ∀ R : ℝ, R0 ≤ R → c ≤ ∫ x in (-(2 * R))..(-R), h x) : False := by
  have hF : ∀ k : ℕ, (k : ℝ) * c ≤ ∫ x in (-(R0 * 2 ^ k))..(-R0), h x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hk : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      have hRk : R0 ≤ R0 * 2 ^ k := by nlinarith
      have e : -(R0 * 2 ^ (k + 1)) = -(2 * (R0 * 2 ^ k)) := by ring
      have hb := hblock (R0 * 2 ^ k) hRk
      have hsplit : ∫ x in (-(R0 * 2 ^ (k + 1)))..(-R0), h x =
          (∫ x in (-(R0 * 2 ^ (k + 1)))..(-(R0 * 2 ^ k)), h x) + ∫ x in (-(R0 * 2 ^ k))..(-R0), h x := by
        rw [intervalIntegral.integral_add_adjacent_intervals] <;> exact hint.intervalIntegrable
      rw [hsplit, e]
      push_cast
      linarith
  have hbound : ∀ k : ℕ, ∫ x in (-(R0 * 2 ^ k))..(-R0), h x ≤ ∫ x, h x := by
    intro k
    have hk : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have hle : -(R0 * 2 ^ k) ≤ -R0 := by nlinarith
    rw [intervalIntegral.integral_of_le hle]
    exact setIntegral_le_integral hint (Filter.Eventually.of_forall hnn)
  obtain ⟨k, hk⟩ := exists_nat_gt ((∫ x, h x) / c)
  have h1 := (hF k).trans (hbound k)
  rw [div_lt_iff₀ hc] at hk
  linarith

/-- **Theorem 4.7, non-integrability step (U1).**  If `ts` has `m = at47_m P Q` elements (`Q ≠ 0`) and `p` is a complex
polynomial of degree `≥ 1`, then `x ↦ p(x) N(x)² / ∏_{t ∈ ts}(x - t)` is not integrable on `ℝ`. -/
theorem at47_not_integrable_poly_mul (P Q : ℝ[X]) (hQ : Q ≠ 0) (ts : Finset ℝ) (hcard : ts.card = at47_m P Q)
    (p : ℂ[X]) (hp : 1 ≤ p.natDegree) :
    ¬ Integrable (fun x : ℝ => p.eval (x : ℂ) * ((at47_Nf P Q x : ℝ) : ℂ) ^ 2 / ∏ t ∈ ts, ((x : ℂ) - (t : ℂ))) := by
  intro hint
  have hp0 : p ≠ 0 := by rintro rfl; simp at hp
  obtain ⟨c1, S1, hc1, hS1, hpl⟩ := at47_cpoly_lower hp0
  obtain ⟨c, R1, hc, hR1, hblock⟩ := at47_block_integral P Q hQ
  have hm : ts.card = at47_e P Q + 2 := hcard.trans (at47_m_eq P Q)
  obtain ⟨d', hd'⟩ : ∃ d', p.natDegree = d' + 1 := ⟨p.natDegree - 1, by omega⟩
  set T : ℝ := ∑ t ∈ ts, |t| with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun _ _ => abs_nonneg _
  let h : ℝ → ℝ := fun x => ‖p.eval (x : ℂ)‖ * at47_Nf P Q x ^ 2 / ‖∏ t ∈ ts, ((x : ℂ) - (t : ℂ))‖
  have hh : h = fun x : ℝ => ‖p.eval (x : ℂ) * ((at47_Nf P Q x : ℝ) : ℂ) ^ 2 / ∏ t ∈ ts, ((x : ℂ) - (t : ℂ))‖ := by
    funext (x : ℝ)
    simp only [h, norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hint' : Integrable h := by rw [hh]; exact hint.norm
  have hnn : ∀ x, 0 ≤ h x := fun x => by simp only [h]; positivity
  refine at47_blocks_not_integrable hint' hnn (c := c1 * c / 3 ^ ts.card)
    (R0 := max (max R1 S1) (T + 1)) (by positivity) (lt_of_lt_of_le (by linarith) (le_max_right _ _)) ?_
  intro R hR
  have hRR1 : R1 ≤ R := ((le_max_left _ _).trans (le_max_left _ _)).trans hR
  have hRS1 : S1 ≤ R := ((le_max_right _ _).trans (le_max_left _ _)).trans hR
  have hRT : T + 1 ≤ R := (le_max_right _ _).trans hR
  have hR1' : 1 ≤ R := by linarith
  have hR0 : 0 < R := by linarith
  have hab : -(2 * R) ≤ -R := by linarith
  set K : ℝ := c1 * R ^ p.natDegree / (3 * R) ^ ts.card with hK
  have hKpos : 0 < K := by positivity
  have hpt : ∀ x ∈ Set.Icc (-(2 * R)) (-R), K * at47_Nf P Q x ^ 2 ≤ h x := by
    intro x hx
    have hxR : R ≤ -x := by linarith [hx.2]
    have hx2 : -x ≤ 2 * R := by linarith [hx.1]
    have hxn : ‖(x : ℂ)‖ = -x := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    have hpl' : c1 * R ^ p.natDegree ≤ ‖p.eval (x : ℂ)‖ := by
      have := hpl (x : ℂ) (by rw [hxn]; linarith)
      rw [hxn] at this
      refine le_trans ?_ this
      gcongr
    have hprod : ‖∏ t ∈ ts, ((x : ℂ) - (t : ℂ))‖ ≤ (3 * R) ^ ts.card := by
      rw [norm_prod]
      calc ∏ t ∈ ts, ‖(x : ℂ) - (t : ℂ)‖ ≤ ∏ t ∈ ts, (3 * R) := by
            gcongr with t ht
            have h1 : |t| ≤ T := Finset.single_le_sum (f := fun t => |t|) (fun _ _ => abs_nonneg _) ht
            have : ‖(x : ℂ) - (t : ℂ)‖ ≤ ‖(x : ℂ)‖ + ‖(t : ℂ)‖ := norm_sub_le _ _
            rw [hxn, Complex.norm_real, Real.norm_eq_abs] at this
            linarith
        _ = (3 * R) ^ ts.card := by simp
    have hprodpos : 0 < ‖∏ t ∈ ts, ((x : ℂ) - (t : ℂ))‖ := by
      rw [norm_pos_iff, Finset.prod_ne_zero_iff]
      intro t ht h0
      have h1 : |t| ≤ T := Finset.single_le_sum (f := fun t => |t|) (fun _ _ => abs_nonneg _) ht
      have h2 : (x : ℂ) = t := sub_eq_zero.mp h0
      have h3 : x = t := by exact_mod_cast h2
      have : |t| = -x := by rw [← h3, abs_of_nonpos (by linarith)]
      linarith
    simp only [h]
    rw [hK]
    have hN := sq_nonneg (at47_Nf P Q x)
    calc c1 * R ^ p.natDegree / (3 * R) ^ ts.card * at47_Nf P Q x ^ 2
        = (c1 * R ^ p.natDegree * at47_Nf P Q x ^ 2) / (3 * R) ^ ts.card := by ring
      _ ≤ (‖p.eval (x : ℂ)‖ * at47_Nf P Q x ^ 2) / ‖∏ t ∈ ts, ((x : ℂ) - (t : ℂ))‖ := by
          apply div_le_div₀ (by positivity) _ hprodpos hprod
          gcongr
  have hcontN : ContinuousOn (fun x => K * at47_Nf P Q x ^ 2) (Set.Icc (-(2 * R)) (-R)) := by
    unfold at47_Nf
    have := continuous_airyAi; have := continuous_airyAi'
    have hP := Polynomial.continuous P (R := ℝ)
    have hQc := Polynomial.continuous Q (R := ℝ)
    fun_prop
  have hI1 : IntervalIntegrable (fun x => K * at47_Nf P Q x ^ 2) volume (-(2 * R)) (-R) :=
    hcontN.intervalIntegrable_of_Icc hab
  have hmono := intervalIntegral.integral_mono_on hab hI1 hint'.intervalIntegrable hpt
  have hN := hblock R hRR1
  have hcN : ∫ x in (-(2 * R))..(-R), K * at47_Nf P Q x ^ 2 = K * ∫ x in (-(2 * R))..(-R), at47_Nf P Q x ^ 2 :=
    intervalIntegral.integral_const_mul _ _
  rw [hcN] at hmono
  refine le_trans ?_ hmono
  have hq : c1 * c / 3 ^ ts.card ≤ K * (c * (R ^ (at47_e P Q + 1) * √R)) := by
    have e1 : K * (c * (R ^ (at47_e P Q + 1) * √R)) = (c1 * c / 3 ^ ts.card) * (R ^ d' * √R) := by
      rw [hK, hd', hm]
      field_simp
      ring
    rw [e1]
    have h1 : 1 ≤ R ^ d' := one_le_pow₀ hR1'
    have h2 : 1 ≤ √R := by rw [Real.one_le_sqrt]; exact hR1'
    have : 1 ≤ R ^ d' * √R := by nlinarith
    have hpos : 0 < c1 * c / 3 ^ ts.card := by positivity
    nlinarith
  exact hq.trans (mul_le_mul_of_nonneg_left hN hKpos.le)

/-- info: 'FormalResearch.Special.at47_not_integrable_poly_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.at47_not_integrable_poly_mul

end FormalResearch.Special
