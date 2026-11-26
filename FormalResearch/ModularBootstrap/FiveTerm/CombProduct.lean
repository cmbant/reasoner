module

public import FormalResearch.ModularBootstrap.FiveTerm.CombClass

/-!
# `F ∈ H_adm` times an outer-function datum lies in the Cauchy class (FIVE-0; `ctu:common-functional` (1))

Source: Lemma ctu.2a (`constant_term_universality.tex`), "by these properties and (i)-(ii) of the class
`H_adm(Ω)`, `H = F G` satisfies `H(z̄) = conj H(z)`, `H = 1 + (F'(0)+g_1) z + O(|z|²)` at `0`, `H` is bounded near
`1`, and `|H| = O(|1+z²|^{a_∞-1} (log)^{...})` at `±i`".

`HAdm.mul_datum`: `F ∈ HAdm F c₁` and `OuterDatum W K g₁ G` give `CauchyClass (F·G) (c₁ + g₁)`, with the growth
exponent `ε = 1/4` (`|H| |1+z²|^{3/4}` bounded): near `±i`, `|F G| ≤ C |1+z²|^{a - 5/4}` with `a > 1/2`, so the
product with `|1+z²|^{3/4}` is `O(|1+z²|^{a-1/2})`; near `1`, `|F| |z-1|^{1/2}` and `|G| |z-1|^{-1/2}` are
bounded; elsewhere by continuity on a compact set (`bounded_of_local`).  All proved unconditionally.
-/

@[expose] public section

open Complex Set Filter Topology MeasureTheory Metric
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

section

variable {F G : ℂ → ℂ} {c1 g1 : ℝ} {W : ℝ → ℝ} {K : ℝ → ℂ}

lemma norm_closure_halfDisc_le {z : ℂ} (hz : z ∈ closure halfDisc) : ‖z‖ ≤ 1 := by
  have : closure halfDisc ⊆ closedBall (0 : ℂ) 1 := by
    refine closure_minimal ?_ isClosed_closedBall
    intro w hw; rw [mem_closedBall, dist_zero_right]; exact hw.1.le
  have := this hz
  rwa [mem_closedBall, dist_zero_right] at this

lemma norm_one_add_sq_le_two {z : ℂ} (hz : z ∈ closure halfDisc) : ‖1 + z ^ 2‖ ≤ 2 := by
  have h := norm_closure_halfDisc_le hz
  calc ‖1 + z ^ 2‖ ≤ ‖(1 : ℂ)‖ + ‖z ^ 2‖ := norm_add_le _ _
    _ = 1 + ‖z‖ ^ 2 := by rw [norm_one, norm_pow]
    _ ≤ 2 := by nlinarith only [h, norm_nonneg z]

lemma one_add_sq_ne_zero {z : ℂ} (h1 : z ≠ Complex.I) (h2 : z ≠ -Complex.I) : 1 + z ^ 2 ≠ 0 := by
  intro h
  have : (z - Complex.I) * (z + Complex.I) = 0 := by
    have hI := Complex.I_sq
    linear_combination h + (-1 : ℂ) * hI
  rcases mul_eq_zero.mp this with h | h
  · exact h1 (sub_eq_zero.mp h)
  · exact h2 (eq_neg_of_add_eq_zero_left h)

/-- Jet of a product. -/
lemma jet_mul (hF : ∃ C r : ℝ, 0 < r ∧ ∀ z ∈ closure halfDisc, ‖z‖ < r → ‖F z - 1 - c1 * z‖ ≤ C * ‖z‖ ^ 2)
    (hG : ∃ C r : ℝ, 0 < r ∧ ∀ z ∈ closure halfDisc, ‖z‖ < r → ‖G z - 1 - g1 * z‖ ≤ C * ‖z‖ ^ 2) :
    ∃ C r : ℝ, 0 < r ∧ ∀ z ∈ closure halfDisc, ‖z‖ < r →
      ‖F z * G z - 1 - ((c1 + g1 : ℝ) : ℂ) * z‖ ≤ C * ‖z‖ ^ 2 := by
  obtain ⟨CF, rF, hrF, hFj⟩ := hF
  obtain ⟨CG, rG, hrG, hGj⟩ := hG
  refine ⟨|c1 * g1| + |CF| * (1 + |g1| + |CG|) + |CG| * (1 + |c1|), min (min rF rG) 1,
    by positivity, fun z hz hzr => ?_⟩
  have hzF : ‖z‖ < rF := lt_of_lt_of_le hzr (le_trans (min_le_left _ _) (min_le_left _ _))
  have hzG : ‖z‖ < rG := lt_of_lt_of_le hzr (le_trans (min_le_left _ _) (min_le_right _ _))
  have hz1 : ‖z‖ < 1 := lt_of_lt_of_le hzr (min_le_right _ _)
  have eF := hFj z hz hzF
  have eG := hGj z hz hzG
  set a := ‖z‖ with ha
  have ha0 : 0 ≤ a := norm_nonneg z
  set eFv := F z - 1 - c1 * z with heF
  set eGv := G z - 1 - g1 * z with heG
  have hid : F z * G z - 1 - ((c1 + g1 : ℝ) : ℂ) * z =
      (c1 * g1 : ℝ) * z ^ 2 + eFv * G z + eGv * (1 + (c1 : ℂ) * z) := by
    rw [heF, heG]; push_cast; ring
  have hGn : ‖G z‖ ≤ 1 + |g1| + |CG| := by
    have : G z = 1 + g1 * z + eGv := by rw [heG]; ring
    rw [this]
    calc ‖(1 : ℂ) + g1 * z + eGv‖ ≤ ‖(1 : ℂ) + g1 * z‖ + ‖eGv‖ := norm_add_le _ _
      _ ≤ (‖(1 : ℂ)‖ + ‖(g1 : ℂ) * z‖) + ‖eGv‖ := by gcongr; exact norm_add_le _ _
      _ = (1 + |g1| * a) + ‖eGv‖ := by rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ (1 + |g1| * a) + |CG| * a ^ 2 := by
          gcongr; exact le_trans eG (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg a))
      _ ≤ 1 + |g1| + |CG| := by
          have haa : a ^ 2 ≤ 1 := by nlinarith only [hz1, ha0]
          nlinarith only [mul_le_mul_of_nonneg_left hz1.le (abs_nonneg g1), abs_nonneg CG, abs_nonneg g1,
            mul_le_mul_of_nonneg_left haa (abs_nonneg CG)]
  have h1c : ‖(1 : ℂ) + (c1 : ℂ) * z‖ ≤ 1 + |c1| := by
    calc ‖(1 : ℂ) + (c1 : ℂ) * z‖ ≤ ‖(1 : ℂ)‖ + ‖(c1 : ℂ) * z‖ := norm_add_le _ _
      _ = 1 + |c1| * a := by rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ 1 + |c1| := by nlinarith only [mul_le_mul_of_nonneg_left hz1.le (abs_nonneg c1)]
  rw [hid]
  calc ‖((c1 * g1 : ℝ) : ℂ) * z ^ 2 + eFv * G z + eGv * (1 + (c1 : ℂ) * z)‖
      ≤ ‖((c1 * g1 : ℝ) : ℂ) * z ^ 2‖ + ‖eFv * G z‖ + ‖eGv * (1 + (c1 : ℂ) * z)‖ := by
        refine le_trans (norm_add_le _ _) ?_
        gcongr; exact norm_add_le _ _
    _ ≤ |c1 * g1| * a ^ 2 + (|CF| * a ^ 2) * (1 + |g1| + |CG|) + (|CG| * a ^ 2) * (1 + |c1|) := by
        gcongr
        · rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
        · rw [norm_mul]
          exact mul_le_mul (le_trans eF (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg a))) hGn
            (norm_nonneg _) (by positivity)
        · rw [norm_mul]
          exact mul_le_mul (le_trans eG (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg a))) h1c
            (norm_nonneg _) (by positivity)
    _ = (|c1 * g1| + |CF| * (1 + |g1| + |CG|) + |CG| * (1 + |c1|)) * a ^ 2 := by ring

lemma continuousOn_one_add_sq_rpow (q : ℝ) (hq : 0 ≤ q) :
    Continuous fun z : ℂ => ‖1 + z ^ 2‖ ^ q := by
  have : Continuous fun z : ℂ => ‖1 + z ^ 2‖ := by fun_prop
  exact this.rpow_const (fun _ => Or.inr hq)

lemma prod_bound_at_I {m1 m2 t C1 C2 a : ℝ} (ht : 0 < t) (ht2 : t ≤ 2) (ha : 1 / 2 < a)
    (h1 : m1 ≤ C1 * t ^ a) (h2 : m2 ≤ C2 * t ^ (-(5 / 4 : ℝ))) (hm2 : 0 ≤ m2) :
    m1 * m2 * t ^ (1 - (1 / 4 : ℝ)) ≤ |C1| * |C2| * (2 : ℝ) ^ (a - 1 / 2) := by
  have hta : 0 ≤ t ^ a := Real.rpow_nonneg ht.le _
  have htb : 0 ≤ t ^ (-(5 / 4 : ℝ)) := Real.rpow_nonneg ht.le _
  have e1 : m1 ≤ |C1| * t ^ a := le_trans h1 (mul_le_mul_of_nonneg_right (le_abs_self _) hta)
  have e2 : m2 ≤ |C2| * t ^ (-(5 / 4 : ℝ)) :=
    le_trans h2 (mul_le_mul_of_nonneg_right (le_abs_self _) htb)
  have e3 : t ^ a * t ^ (-(5 / 4 : ℝ)) * t ^ (1 - (1 / 4 : ℝ)) = t ^ (a - 1 / 2) := by
    rw [← Real.rpow_add ht, ← Real.rpow_add ht]; congr 1; ring
  have e4 : t ^ (a - 1 / 2) ≤ (2 : ℝ) ^ (a - 1 / 2) :=
    Real.rpow_le_rpow ht.le ht2 (by linarith)
  have hq : 0 ≤ t ^ (1 - (1 / 4 : ℝ)) := Real.rpow_nonneg ht.le _
  calc m1 * m2 * t ^ (1 - (1 / 4 : ℝ)) ≤ (|C1| * t ^ a) * (|C2| * t ^ (-(5 / 4 : ℝ))) * t ^ (1 - (1 / 4 : ℝ)) := by
        gcongr
    _ = |C1| * |C2| * (t ^ a * t ^ (-(5 / 4 : ℝ)) * t ^ (1 - (1 / 4 : ℝ))) := by ring
    _ = |C1| * |C2| * t ^ (a - 1 / 2) := by rw [e3]
    _ ≤ |C1| * |C2| * (2 : ℝ) ^ (a - 1 / 2) := by gcongr

lemma prod_bound_at_one {m1 m2 s C1 C2 : ℝ} (hs : 0 < s) (h1 : m1 * s ^ (1 / 2 : ℝ) ≤ C1)
    (h2 : m2 ≤ C2 * s ^ (1 / 2 : ℝ)) (hm1 : 0 ≤ m1) : m1 * m2 ≤ |C2| * |C1| := by
  have hsq : 0 ≤ s ^ (1 / 2 : ℝ) := Real.rpow_nonneg hs.le _
  have e2 : m2 ≤ |C2| * s ^ (1 / 2 : ℝ) := le_trans h2 (mul_le_mul_of_nonneg_right (le_abs_self _) hsq)
  calc m1 * m2 ≤ m1 * (|C2| * s ^ (1 / 2 : ℝ)) := mul_le_mul_of_nonneg_left e2 hm1
    _ = |C2| * (m1 * s ^ (1 / 2 : ℝ)) := by ring
    _ ≤ |C2| * |C1| := mul_le_mul_of_nonneg_left (le_trans h1 (le_abs_self _)) (abs_nonneg _)

/-- Growth of the product `F G` with exponent `ε = 1/4`. -/
lemma growth_mul (hF : HAdm F c1) (hG : OuterDatum W K g1 G) :
    ∃ C : ℝ, ∀ z ∈ closure halfDisc, z ≠ Complex.I → z ≠ -Complex.I → z ≠ 1 →
      ‖F z * G z‖ * ‖1 + z ^ 2‖ ^ (1 - (1 / 4 : ℝ)) ≤ C := by
  obtain ⟨CF1, rF1, hrF1, hF1⟩ := hF.near_one
  obtain ⟨CG1, cG1, rG1, hcG1, hrG1, hG1⟩ := hG.near_one
  obtain ⟨CF2, rF2, a, hrF2, ha, hF2⟩ := hF.near_I
  obtain ⟨CG2, cG2, rG2, hcG2, hrG2, hG2⟩ := hG.near_I
  set r1 := min rF1 rG1 with hr1
  set r2 := min rF2 rG2 with hr2
  have hr1p : 0 < r1 := lt_min hrF1 hrG1
  have hr2p : 0 < r2 := lt_min hrF2 hrG2
  set f : ℂ → ℝ := fun z => ‖F z * G z‖ * ‖1 + z ^ 2‖ ^ (1 - (1 / 4 : ℝ)) with hf
  have hfc : ContinuousOn f (closure halfDisc \ singPts) := by
    have h1 : ContinuousOn (fun z => ‖F z * G z‖) (closure halfDisc \ singPts) :=
      (hF.cont.mul hG.cont).norm
    exact h1.mul (continuousOn_one_add_sq_rpow _ (by norm_num)).continuousOn
  have hnearI : ∀ z ∈ closure halfDisc \ singPts, (‖z - Complex.I‖ < r2 ∨ ‖z + Complex.I‖ < r2) →
      f z ≤ |CF2| * |CG2| * (2 : ℝ) ^ (a - 1 / 2) := by
    intro z hz hnr
    have hS := hz.2
    rw [mem_singPts_iff] at hS
    push Not at hS
    obtain ⟨hzI, hzmI, hz1⟩ := hS
    have ht : 0 < ‖1 + z ^ 2‖ := norm_pos_iff.2 (one_add_sq_ne_zero hzI hzmI)
    have hnF : ‖z - Complex.I‖ < rF2 ∨ ‖z + Complex.I‖ < rF2 :=
      hnr.imp (fun h => lt_of_lt_of_le h (min_le_left _ _)) (fun h => lt_of_lt_of_le h (min_le_left _ _))
    have hnG : ‖z - Complex.I‖ < rG2 ∨ ‖z + Complex.I‖ < rG2 :=
      hnr.imp (fun h => lt_of_lt_of_le h (min_le_right _ _)) (fun h => lt_of_lt_of_le h (min_le_right _ _))
    have hFz := hF2 z hz.1 hzI hzmI hnF
    have hGz := (hG2 z hz.1 hzI hzmI hnG).2
    simp only [hf, norm_mul]
    exact prod_bound_at_I ht (norm_one_add_sq_le_two hz.1) ha hFz hGz (norm_nonneg _)
  have hnear1 : ∀ z ∈ closure halfDisc \ singPts, ‖z - 1‖ < r1 → f z ≤ |CG1| * |CF1| * 2 := by
    intro z hz hnr
    have hS := hz.2
    rw [mem_singPts_iff] at hS
    push Not at hS
    obtain ⟨hzI, hzmI, hz1⟩ := hS
    have hs : 0 < ‖z - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hz1)
    have hFz := hF1 z hz.1 hz1 (lt_of_lt_of_le hnr (min_le_left _ _))
    have hGz := (hG1 z hz.1 hz1 (lt_of_lt_of_le hnr (min_le_right _ _))).2
    have hp := prod_bound_at_one hs hFz hGz (norm_nonneg _)
    have h2 : ‖1 + z ^ 2‖ ^ (1 - (1 / 4 : ℝ)) ≤ 2 := by
      have h := norm_one_add_sq_le_two hz.1
      calc ‖1 + z ^ 2‖ ^ (1 - (1 / 4 : ℝ)) ≤ (2 : ℝ) ^ (1 - (1 / 4 : ℝ)) :=
            Real.rpow_le_rpow (norm_nonneg _) h (by norm_num)
        _ ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    simp only [hf, norm_mul]
    calc ‖F z‖ * ‖G z‖ * ‖1 + z ^ 2‖ ^ (1 - (1 / 4 : ℝ)) ≤ (|CG1| * |CF1|) * 2 :=
          mul_le_mul hp h2 (Real.rpow_nonneg (norm_nonneg _) _) (by positivity)
      _ = _ := rfl
  obtain ⟨M, hM⟩ := bounded_of_local (r := min r1 r2) hfc (lt_min hr1p hr2p)
    (M := max (|CG1| * |CF1| * 2) (|CF2| * |CG2| * (2 : ℝ) ^ (a - 1 / 2))) (by
      intro z hz hnear
      rcases hnear with h | h | h
      · refine le_trans (hnearI z hz (Or.inl ?_)) (le_max_right _ _)
        rw [← dist_eq_norm]; exact lt_of_lt_of_le h (le_trans (min_le_right _ _) le_rfl)
      · refine le_trans (hnearI z hz (Or.inr ?_)) (le_max_right _ _)
        rw [show z + Complex.I = z - (-Complex.I) by ring, ← dist_eq_norm]
        exact lt_of_lt_of_le h (le_trans (min_le_right _ _) le_rfl)
      · refine le_trans (hnear1 z hz ?_) (le_max_left _ _)
        rw [← dist_eq_norm]; exact lt_of_lt_of_le h (le_trans (min_le_left _ _) le_rfl))
  refine ⟨M, fun z hz hzI hzmI hz1 => hM z ⟨hz, ?_⟩⟩
  rw [mem_singPts_iff]
  tauto

/-- **`H = F G` lies in the Cauchy class** with `h₁ = F'(0) + g₁`. -/
theorem HAdm.mul_datum (hF : HAdm F c1) (hG : OuterDatum W K g1 G) :
    CauchyClass (fun z => F z * G z) (c1 + g1) where
  diff := hF.diff.mul hG.diff
  cont := hF.cont.mul hG.cont
  conj z hz := by simp only [hF.conj z hz, hG.conj z hz, map_mul]
  jet := jet_mul hF.jet hG.jet
  growth := by
    obtain ⟨C, hC⟩ := growth_mul hF hG
    exact ⟨C, 1 / 4, by norm_num, by norm_num, hC⟩

end

end FormalResearch.ModularBootstrap.FiveTerm

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.HAdm.mul_datum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.HAdm.mul_datum
