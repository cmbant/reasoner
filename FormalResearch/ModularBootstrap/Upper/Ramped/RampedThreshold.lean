module

public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedDesign

/-!
# The threshold `t_*` of the ramped comb (`rem:thmU`, Step 5, last line)

Source: `CFT/notes/n2_ramped_comb.tex`, Lemma U* (`rem:thmU`), end of the proof, and the order-of-constants
paragraph.

* `rampedTstar P c' = c' χ'_1² / 3`, the left end of the positivity range of `g` (the first zero of `B_{D_*}`
  in the `t = c' x²/3` variable);
* `rampedThreshold`: `t_* = ξ̄ c' + A_opt c'^{1/3} + (A_opt/|a_1|) M_0 + O(c'^{-1/3})` with an absolute `O`,
  from `langerTauInv_expansion`, `d = M_0 c'^{-1/3}` and `A_opt = c_* |a_1|`, `c_* = 2ξ_*/(3 κ k_tip^{2/3})`;
* `rampedD_le`: `d ≤ min(1, (a_1 - a_2)/8)` for `c'` large (the threshold depends on `M_0` only).

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real BigOperators

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.ModularBootstrap Upper.Comb Upper.Design FormalResearch.Special
  FormalResearch.ModularBootstrap.Upper.Window

/-- The threshold `t_* = c' χ'_1² / 3` of the ramped comb. -/
noncomputable def rampedTstar (P : RampedParams) (c' : ℝ) : ℝ :=
  c' * designSite c' (rampedSigma (rampedD P c') c') 1 ^ 2 / 3

lemma c_mul_lambdaComb {c' : ℝ} (hc' : 0 < c') :
    c' * lambdaComb c' = kTip ^ (-(2 / 3 : ℝ)) * c' ^ (1 / 3 : ℝ) := by
  unfold lambdaComb
  rw [Real.mul_rpow kTip_pos.le hc'.le]
  have : c' * c' ^ (-(2 / 3 : ℝ)) = c' ^ (1 / 3 : ℝ) := by
    calc c' * c' ^ (-(2 / 3 : ℝ)) = c' ^ (1 : ℝ) * c' ^ (-(2 / 3 : ℝ)) := by rw [Real.rpow_one]
      _ = c' ^ (1 / 3 : ℝ) := by rw [← Real.rpow_add hc']; norm_num
  rw [mul_left_comm, this]

lemma c_mul_lambdaComb_sq {c' : ℝ} (hc' : 0 < c') :
    c' * lambdaComb c' ^ 2 = kTip ^ (-(4 / 3 : ℝ)) * c' ^ (-(1 / 3 : ℝ)) := by
  have h := c_mul_lambdaComb hc'
  have hl : lambdaComb c' = kTip ^ (-(2 / 3 : ℝ)) * c' ^ (-(2 / 3 : ℝ)) := by
    unfold lambdaComb; rw [Real.mul_rpow kTip_pos.le hc'.le]
  rw [hl, mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast (c' ^ (-(2 / 3 : ℝ))),
    ← Real.rpow_mul kTip_pos.le, ← Real.rpow_mul hc'.le]
  have : c' * c' ^ ((-(2 / 3 : ℝ)) * ((2 : ℕ) : ℝ)) = c' ^ (-(1 / 3 : ℝ)) := by
    calc c' * c' ^ ((-(2 / 3 : ℝ)) * ((2 : ℕ) : ℝ)) = c' ^ (1 : ℝ) * c' ^ ((-(2 / 3 : ℝ)) * ((2 : ℕ) : ℝ)) := by
          rw [Real.rpow_one]
      _ = c' ^ (-(1 / 3 : ℝ)) := by rw [← Real.rpow_add hc']; norm_num
  rw [mul_left_comm, this]
  norm_num

lemma cStar_eq : cStar = 2 * xiStar / (3 * kappaAiry) * kTip ^ (-(2 / 3 : ℝ)) := by
  have hk := kTip_pos
  have hκ := kappaAiry_pos
  have hβ : betaTip = kappaAiry * kTip ^ (2 / 3 : ℝ) := by
    unfold betaTip KTip kappaAiry
    rw [← Real.mul_rpow (by positivity) hk.le]
    congr 1; ring
  have h2 : 0 < kTip ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hk _
  unfold cStar
  rw [hβ, Real.rpow_neg hk.le]
  field_simp


/-- The remainder of `u² = (ξ + s - e)²` after the linear term: `|u² - ξ² - 2ξs| ≤ (2ξB + (1+B)²) s²`
for `0 ≤ e ≤ B s²`, `0 ≤ s ≤ 1`. -/
lemma threshold_remainder {B ξ s e u : ℝ} (hB : 0 ≤ B) (hξ : 0 < ξ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (he0 : 0 ≤ e) (he1 : e ≤ B * s ^ 2) (hu : u = ξ + s - e) :
    |u ^ 2 - ξ ^ 2 - 2 * ξ * s| ≤ (2 * ξ * B + (1 + B) ^ 2) * s ^ 2 := by
  have e1 : u ^ 2 - ξ ^ 2 - 2 * ξ * s = -2 * ξ * e + (s - e) ^ 2 := by rw [hu]; ring
  have hBs : 0 ≤ B * s := mul_nonneg hB hs0
  have h2 : e ≤ B * s := he1.trans (by
    have := mul_le_mul_of_nonneg_left hs1 hBs
    nlinarith)
  have h3 : |s - e| ≤ (1 + B) * s := by
    rw [abs_le]; constructor <;> linarith
  have h4 : (s - e) ^ 2 ≤ (1 + B) ^ 2 * s ^ 2 := by
    rw [← sq_abs, show (1 + B) ^ 2 * s ^ 2 = ((1 + B) * s) ^ 2 by ring]
    exact pow_le_pow_left₀ (abs_nonneg _) h3 2
  have hxe : ξ * e ≤ ξ * (B * s ^ 2) := mul_le_mul_of_nonneg_left he1 hξ.le
  have hxe0 : 0 ≤ ξ * e := mul_nonneg hξ.le he0
  have hq : 0 ≤ ξ * (B * s ^ 2) := by positivity
  have hq2 : 0 ≤ (1 + B) ^ 2 * s ^ 2 := by positivity
  rw [e1, abs_le]
  constructor <;> nlinarith [sq_nonneg (s - e)]

lemma rampedNode_one (d c' : ℝ) : rampedNode d c' 1 = (|airyZero 1| + d) / kappaAiry := by
  unfold rampedNode sNodeAiry
  simp only [ite_true]
  ring

/-- **The threshold** (`rem:thmU`, end of Step 5): `t_* = c' χ'_1²/3 = ξ̄ c' + A_opt c'^{1/3} +
(A_opt/|a_1|) M_0 + O(c'^{-1/3})`, with an absolute `O` and `d = M_0 c'^{-1/3}`. -/
theorem rampedThreshold : ∃ C : ℝ, 0 < C ∧ ∀ P : RampedParams, ∀ᶠ c' : ℝ in atTop,
    |rampedTstar P c' - (xiBar * c' + Aopt * c' ^ (1 / 3 : ℝ) + Aopt / |airyZero 1| * P.M0)| ≤
      C * c' ^ (-(1 / 3 : ℝ)) := by
  have hk := kTip_pos
  have hκ := kappaAiry_pos
  have hxs := xiStar_pos
  have ha1 : 0 < |airyZero 1| := abs_pos.2 (airyZero_neg 1).ne
  have hB : 0 ≤ 2 * c1K0 / 3 := by have := c1K0_pos; positivity
  have hk43 : 0 < kTip ^ (-(4 / 3 : ℝ)) := Real.rpow_pos_of_pos hk _
  refine ⟨(2 * xiStar * (2 * c1K0 / 3) + (1 + 2 * c1K0 / 3) ^ 2) * ((|airyZero 1| + 1) / kappaAiry) ^ 2 *
    kTip ^ (-(4 / 3 : ℝ)) / 3 + 1, by positivity, fun P => ?_⟩
  have hlam : ∀ᶠ c' : ℝ in atTop, lambdaComb c' * ((|airyZero 1| + 1) / kappaAiry) ≤ 1 := by
    have ht := tendsto_lambdaComb_atTop.mul_const ((|airyZero 1| + 1) / kappaAiry)
    simp only [zero_mul] at ht
    exact ht.eventually_le_const zero_lt_one
  have hdl : ∀ᶠ c' : ℝ in atTop, rampedD P c' ≤ 1 := by
    have ht := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).const_mul P.M0
    simp only [mul_zero] at ht
    exact ht.eventually_le_const zero_lt_one
  filter_upwards [eventually_gt_atTop 0, hlam, hdl] with c' hc' hlc hdc
  have hl := lambdaComb_pos' hc'
  obtain ⟨d, hd⟩ : ∃ d, d = rampedD P c' := ⟨_, rfl⟩
  have hd0 : 0 ≤ d := by rw [hd]; unfold rampedD; have := P.M0_pos; positivity
  rw [← hd] at hdc
  obtain ⟨s, hs⟩ : ∃ s, s = lambdaComb c' * ((|airyZero 1| + d) / kappaAiry) := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := by rw [hs]; positivity
  have hs1 : s ≤ lambdaComb c' * ((|airyZero 1| + 1) / kappaAiry) := by
    rw [hs]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (by linarith) hκ.le) hl.le
  have hsle : s ≤ 1 := hs1.trans hlc
  have hsite : designSite c' (rampedSigma d c') 1 = langerTauInv s := by
    rw [designSite_rampedSigma hc', rampedNode_one, hs]
  obtain ⟨he0, he1⟩ := langerTauInv_expansion hs0
  obtain ⟨u, hu⟩ : ∃ u, u = langerTauInv s := ⟨_, rfl⟩
  rw [← hu] at he0 he1
  obtain ⟨e, he⟩ : ∃ e, e = xiStar + s - u := ⟨_, rfl⟩
  rw [← he] at he0 he1
  have hmain : 2 * xiStar / 3 * c' * s = cStar * c' ^ (1 / 3 : ℝ) * (|airyZero 1| + d) := by
    rw [cStar_eq]
    have e1 : 2 * xiStar / 3 * c' * s =
        2 * xiStar / 3 * (c' * lambdaComb c') * ((|airyZero 1| + d) / kappaAiry) := by rw [hs]; ring
    rw [e1, c_mul_lambdaComb hc']
    field_simp
  have hdM : d * c' ^ (1 / 3 : ℝ) = P.M0 := by
    rw [hd]; unfold rampedD
    rw [mul_assoc, ← Real.rpow_add hc']; norm_num
  have hA : Aopt = cStar * |airyZero 1| := rfl
  have hA' : Aopt / |airyZero 1| = cStar := by rw [hA]; field_simp
  have hu_eq : u = xiStar + s - e := by linarith
  have hR := threshold_remainder hB hxs hs0 hsle he0 he1 hu_eq
  have hs2 : s ^ 2 ≤ lambdaComb c' ^ 2 * ((|airyZero 1| + 1) / kappaAiry) ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hs0 hs1 2
  have hcl : c' * lambdaComb c' ^ 2 = kTip ^ (-(4 / 3 : ℝ)) * c' ^ (-(1 / 3 : ℝ)) := c_mul_lambdaComb_sq hc'
  have h5 : cStar * |airyZero 1| * c' ^ (1 / 3 : ℝ) + cStar * P.M0 = 2 * xiStar / 3 * c' * s := by
    rw [hmain, ← hdM]; ring
  have key : rampedTstar P c' - (xiBar * c' + Aopt * c' ^ (1 / 3 : ℝ) + Aopt / |airyZero 1| * P.M0) =
      c' * (u ^ 2 - xiStar ^ 2 - 2 * xiStar * s) / 3 := by
    unfold rampedTstar
    rw [← hd, hsite, ← hu, hA', hA, xiBar]
    linear_combination (-1 : ℝ) * h5
  have hp : 0 < c' ^ (-(1 / 3 : ℝ)) := Real.rpow_pos_of_pos hc' _
  have hK : 0 ≤ 2 * xiStar * (2 * c1K0 / 3) + (1 + 2 * c1K0 / 3) ^ 2 := by positivity
  rw [key, abs_div, abs_mul, abs_of_pos hc', abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  calc c' * |u ^ 2 - xiStar ^ 2 - 2 * xiStar * s| / 3
      ≤ c' * ((2 * xiStar * (2 * c1K0 / 3) + (1 + 2 * c1K0 / 3) ^ 2) *
          (lambdaComb c' ^ 2 * ((|airyZero 1| + 1) / kappaAiry) ^ 2)) / 3 := by
        gcongr
        exact hR.trans (mul_le_mul_of_nonneg_left hs2 hK)
    _ = (2 * xiStar * (2 * c1K0 / 3) + (1 + 2 * c1K0 / 3) ^ 2) * ((|airyZero 1| + 1) / kappaAiry) ^ 2 *
          (c' * lambdaComb c' ^ 2) / 3 := by ring
    _ = (2 * xiStar * (2 * c1K0 / 3) + (1 + 2 * c1K0 / 3) ^ 2) * ((|airyZero 1| + 1) / kappaAiry) ^ 2 *
          (kTip ^ (-(4 / 3 : ℝ)) * c' ^ (-(1 / 3 : ℝ))) / 3 := by rw [hcl]
    _ ≤ _ := by nlinarith

/-- `d ≤ min(1, (a_1 - a_2)/8)` for `c'` large (`rem:thmU`, order of constants; the threshold depends on `M_0`). -/
theorem rampedD_le (P : RampedParams) :
    ∀ᶠ c' : ℝ in atTop, rampedD P c' ≤ min 1 ((airyZero 1 - airyZero 2) / 8) := by
  have hgap : 0 < (airyZero 1 - airyZero 2) / 8 := by
    have := airyZero_strictAnti (n := 1) le_rfl
    have h2 : airyZero 2 < airyZero 1 := this
    linarith
  have ht := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).const_mul P.M0
  simp only [mul_zero] at ht
  exact ht.eventually_le_const (lt_min zero_lt_one hgap)

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.rampedThreshold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rampedThreshold

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.rampedD_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rampedD_le

end FormalResearch.ModularBootstrap.Upper.Ramped
