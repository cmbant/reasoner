module

public import FormalResearch.ModularBootstrap.Upper.Positivity.RegionOne

/-!
# Proposition I, assembly: `g > 0` on `t ≥ t_f + 1` at weight `1` (`ut:I`)

Source: `CFT/modular_bootstrap/paper/upper_transfer.tex`, Proposition I (`ut:I`) and the sentence
"Region I and II overlap, so `g > 0` on `t ≥ t_f + 1` at `w = 1`".  For the designs `D(N, η_*, d)`
(`f = 1`, `η_* ∈ (0, 1/4]`) and `c'` large:

* `proposition_I_sig`, `proposition_I_sig_t`: the same for the finite modifications with arbitrary offsets
  `σs` (sites `2..N` displaced, first site arbitrary); `proposition_I_design`, `proposition_I_design_t` are the
  case `σs = designSigma1 d`.
* `proposition_I_design`: there is `C > 0` such that `2 g(c' x²/3) > 0` for every
  `x ≥ χ'_1 + C λ c'^{-1/2}` (`χ'_1 = designSite c' (designSigma1 d) 1`): Region I (a), (b) and Region II
  (`proposition_II_design`, `levComb_pos`);
* `proposition_I_design_t`: `2 g(t) > 0` for `t = c' x²/3 ≥ t_f + 1`, `t_f = c' χ'_1²/3`, `x ≥ 0`.

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Positivity

open FormalResearch.ModularBootstrap.Upper.Comb FormalResearch.ModularBootstrap.Upper.Hankel
  FormalResearch.ModularBootstrap.Upper.Saddle FormalResearch.ModularBootstrap.Upper.Design
  FormalResearch.ModularBootstrap.Upper.Holes FormalResearch.ModularBootstrap.Upper.Window

/-- `λ c'^{1/2} → 0`. -/
lemma lambdaComb_mul_sqrt_tendsto : Tendsto (fun c' : ℝ => lambdaComb c' * c' ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
  have h : Tendsto (fun c' : ℝ => kTip ^ (-(2 / 3 : ℝ)) * c' ^ (-(1 / 6 : ℝ))) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 6)).const_mul (kTip ^ (-(2 / 3 : ℝ)))
    simpa using this
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with c' hc'
  unfold lambdaComb
  rw [Real.mul_rpow kTip_pos.le hc'.le, mul_assoc, ← Real.rpow_add hc']
  norm_num

lemma sqrt_gap_lower {c' x χ B : ℝ} (hc' : 0 < c') (_hχ : 0 < χ) (hχB : χ ≤ B) (hx : χ ≤ x)
    (hxB : x ≤ χ + 1) (hB : 1 ≤ B) (h : c' * χ ^ 2 + 3 ≤ c' * x ^ 2) :
    3 / (c' * (2 * B + 1)) ≤ x - χ := by
  have h1 : 3 / c' ≤ x ^ 2 - χ ^ 2 := by
    rw [div_le_iff₀ hc']; nlinarith
  have h2 : x ^ 2 - χ ^ 2 = (x - χ) * (x + χ) := by ring
  have h3 : x + χ ≤ 2 * B + 1 := by linarith
  have h4 : 3 / c' ≤ (x - χ) * (2 * B + 1) :=
    h1.trans (h2 ▸ mul_le_mul_of_nonneg_left h3 (by linarith))
  rw [div_le_iff₀ (by positivity)]
  rw [div_le_iff₀ hc'] at h4
  nlinarith

/-- **Proposition I, Region I ∪ Region II** (`ut:I`, `ut:II`) for the `f = 1` finite modifications at
fixed sites `σs` (first site `σs 1`, sites `2..N` arbitrary): see `proposition_I_design`, the case
`σs = designSigma1 d`. -/
theorem proposition_I_sig (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 4) (σs : ℕ → ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ c' in atTop, ∀ x : ℝ,
      designSite c' (σs) 1 + C * lambdaComb c' * c' ^ (-(1 / 2 : ℝ)) ≤ x →
      0 < twoG c' 1 N (1 / 4) (σs) (designWidth1 c' η) x := by
  obtain ⟨Sg0, hSg0, hb⟩ := proposition_I_b_sig N hN hη0 hη1 σs
  obtain ⟨C, hC, ha⟩ := proposition_I_a_sig N hN hη0 hη1 σs Sg0
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ k, 1 ≤ k → k ≤ N → |σs k| ≤ M :=
    ⟨∑ k ∈ Finset.Icc 1 N, |σs k|, fun k hk hkN =>
      Finset.single_le_sum (f := fun j => |σs j|) (fun _ _ => abs_nonneg _)
        (Finset.mem_Icc.mpr ⟨hk, hkN⟩)⟩
  refine ⟨C, hC, ?_⟩
  filter_upwards [ha, hb, proposition_II_sig N hN hη0.le hη1 σs M hM,
    eventually_gt_atTop (0 : ℝ)] with c' hac hbc hIIc hcpos x hx
  by_cases h1 : x ≤ xiStar + lambdaComb c' * Sg0
  · exact hac x hx h1
  · push Not at h1
    by_cases h2 : x ≤ xiStar + c' ^ (-(2 / 5 : ℝ))
    · exact hbc x h1.le h2
    · push Not at h2
      have h := hIIc x h2.le
      have hlev := levComb_pos c' 1 x
      have : 0 < twoG c' 1 N (1 / 4) (σs) (designWidth1 c' η) x / levComb c' 1 x :=
        lt_of_lt_of_le (by norm_num) h
      exact (div_pos_iff_of_pos_right hlev).mp this

/-- **Proposition I, Region I ∪ Region II** (`ut:I`, `ut:II`): for the designs `D(N, η_*, d)`, there is
`C > 0` such that for large `c'` and every `x ≥ χ'_1 + C λ c'^{-1/2}`, `2 g(c' x²/3) > 0`. -/
theorem proposition_I_design (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 4) (d : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ c' in atTop, ∀ x : ℝ,
      designSite c' (designSigma1 d) 1 + C * lambdaComb c' * c' ^ (-(1 / 2 : ℝ)) ≤ x →
      0 < twoG c' 1 N (1 / 4) (designSigma1 d) (designWidth1 c' η) x :=
  proposition_I_sig N hN hη0 hη1 (designSigma1 d)

/-- **Proposition I, form `t ≥ t_f + 1`** (`ut:I`) for the `f = 1` finite modifications at fixed sites `σs`:
see `proposition_I_design_t`, the case `σs = designSigma1 d`. -/
theorem proposition_I_sig_t (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 4) (σs : ℕ → ℝ) :
    ∀ᶠ c' in atTop, ∀ x : ℝ, 0 ≤ x →
      c' * designSite c' (σs) 1 ^ 2 / 3 + 1 ≤ c' * x ^ 2 / 3 →
      0 < twoG c' 1 N (1 / 4) (σs) (designWidth1 c' η) x := by
  obtain ⟨C, hC, hI⟩ := proposition_I_sig N hN hη0 hη1 σs
  have hs1 : Tendsto (fun c' : ℝ => lambdaComb c' * |σs 1|) atTop (𝓝 0) := by
    simpa using tendsto_lambdaComb_atTop.mul_const |σs 1|
  have hxi := xiStar_pos
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = xiStar + 1 + 1 := ⟨_, rfl⟩
  have hB1 : 1 ≤ B := by rw [hB]; linarith
  have hlim := lambdaComb_mul_sqrt_tendsto.const_mul (C * (2 * B + 1))
  rw [mul_zero] at hlim
  filter_upwards [hI, hs1.eventually_le_const (by norm_num : (0 : ℝ) < 1),
    hs1.eventually_le_const (half_pos hxi),
    hlim.eventually_le_const (by norm_num : (0 : ℝ) < 3),
    eventually_gt_atTop (1 : ℝ)] with c' hIc hs1c hs2c hlc hc1 x hx0 hx
  have hcpos : 0 < c' := by linarith
  have hlam : 0 < lambdaComb c' := Real.rpow_pos_of_pos (mul_pos kTip_pos hcpos) _
  have hσ : |σs 1| ≥ σs 1 := le_abs_self _
  have hσ' : -|σs 1| ≤ σs 1 := neg_abs_le _
  have hχ : designSite c' (σs) 1 = xiStar + lambdaComb c' * σs 1 := rfl
  have hl1 : lambdaComb c' * σs 1 ≤ lambdaComb c' * |σs 1| :=
    mul_le_mul_of_nonneg_left hσ hlam.le
  have hl2 : -(lambdaComb c' * |σs 1|) ≤ lambdaComb c' * σs 1 := by
    have := mul_le_mul_of_nonneg_left hσ' hlam.le
    linarith
  have hχpos : 0 < designSite c' (σs) 1 := by rw [hχ]; linarith
  have hχB : designSite c' (σs) 1 ≤ B := by rw [hχ, hB]; linarith
  refine hIc x ?_
  set χ := designSite c' (σs) 1 with hχdef
  have hxsq : c' * χ ^ 2 + 3 ≤ c' * x ^ 2 := by linarith
  have hχx : χ ≤ x := by
    by_contra hlt
    push Not at hlt
    have h1 : x ^ 2 < χ ^ 2 := by nlinarith
    nlinarith [mul_lt_mul_of_pos_left h1 hcpos]
  have hcm : 0 < c' ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hcpos _
  have he : c' ^ (-(1 / 2 : ℝ)) * c' = c' ^ (1 / 2 : ℝ) := by
    have h1 : c' = c' ^ (1 : ℝ) := (Real.rpow_one c').symm
    calc c' ^ (-(1 / 2 : ℝ)) * c' = c' ^ (-(1 / 2 : ℝ)) * c' ^ (1 : ℝ) := by rw [← h1]
      _ = c' ^ (1 / 2 : ℝ) := by rw [← Real.rpow_add hcpos]; norm_num
  have hB3 : 0 < c' * (2 * B + 1) := by positivity
  have hfinal : C * lambdaComb c' * c' ^ (-(1 / 2 : ℝ)) ≤ 3 / (c' * (2 * B + 1)) := by
    rw [le_div_iff₀ hB3]
    have : C * lambdaComb c' * c' ^ (-(1 / 2 : ℝ)) * (c' * (2 * B + 1)) =
        C * (2 * B + 1) * (lambdaComb c' * c' ^ (1 / 2 : ℝ)) := by rw [← he]; ring
    rw [this]; exact hlc
  by_cases hx1 : x ≤ χ + 1
  · exact hfinal.trans (sqrt_gap_lower hcpos hχpos hχB hχx hx1 hB1 hxsq) |> fun h => by linarith
  · push Not at hx1
    have : 3 / (c' * (2 * B + 1)) ≤ 1 := by
      rw [div_le_one hB3]; nlinarith
    linarith

/-- **Proposition I, form `t ≥ t_f + 1`** (`ut:I`): for the designs `D(N, η_*, d)` and large `c'`,
`2 g(t) > 0` for all `t = c' x²/3` (`x ≥ 0`) with `t ≥ t_f + 1`, `t_f = c' χ'_1²/3`. -/
theorem proposition_I_design_t (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 4) (d : ℝ) :
    ∀ᶠ c' in atTop, ∀ x : ℝ, 0 ≤ x →
      c' * designSite c' (designSigma1 d) 1 ^ 2 / 3 + 1 ≤ c' * x ^ 2 / 3 →
      0 < twoG c' 1 N (1 / 4) (designSigma1 d) (designWidth1 c' η) x :=
  proposition_I_sig_t N hN hη0 hη1 (designSigma1 d)

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.proposition_I_sig' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms proposition_I_sig

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.proposition_I_sig_t' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms proposition_I_sig_t

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.proposition_I_design' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms proposition_I_design

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.proposition_I_design_t' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms proposition_I_design_t

end FormalResearch.ModularBootstrap.Upper.Positivity
