module

public import FormalResearch.ModularBootstrap.Upper.Assembly.BumpedDesignWindow
public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedRegionTwoNear

/-!
# The macroscopic bump sits above the ramp (`fw:Ustar`, step (1a), `n2_ramped_comb.tex`)

Source: `CFT/notes/n2_ramped_comb.tex`, Lemma `U*(w)` (`fw:Ustar`), the parameter order (a)-(e) and Step (1a): the
ramp occupies `χ_k - ξ_* ≲ r_1(C_mid) = k_tip^{-2/3} (4 C_mid)^{-8/5}` while the bump block starts at `ξ_* + 2 r_p`; for
`C_mid` large (chosen *after* the bump data `r_p`, `X_p`, `η_big`) no index of the block is `≤ n_cap + 6`, so the bumped
comb is the reference raise `R_bump` of the ramped comb.

* `nCap_le_of_Cmid`: `n_cap ≤ ⌈c' (16 C_mid²)^{-6/5}⌉` (the paper's `n_cap ≤ c'(4 C_mid)^{-12/5} + 1`);
* `rampedBlockAbove` (Step (1a)): for every bump `bd` there is `C_sep` such that for every `P : RampedParams` with
  `C_sep ≤ P.C_mid` and `c'` large, `bd.BlockAbove c' (n_cap + 6)`;
* `rampedBumpCut`: the cut above the block and above the ramp cut `n_cap + 6`.

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.ModularBootstrap Upper.Comb Upper.Bump Upper.Assembly

/-- **`n_cap ≤ ⌈c' (16 C_mid²)^{-6/5}⌉`**: `η_k² ≥ C_mid² (k/c')^{5/6}`, which is `≥ 1/16` at that index. -/
lemma nCap_le_of_Cmid (P : RampedParams) {c' : ℝ} (hc' : 0 < c') :
    nCap P c' ≤ ⌈c' * (16 * P.Cmid ^ 2) ^ (-(6 / 5 : ℝ))⌉₊ := by
  have hC : 0 < 16 * P.Cmid ^ 2 := by have := P.one_le_Cmid; positivity
  have hs : 0 < (16 * P.Cmid ^ 2) ^ (-(6 / 5 : ℝ)) := Real.rpow_pos_of_pos hC _
  refine Nat.sInf_le ?_
  show 1 / 16 ≤ etaArg P c' ⌈c' * (16 * P.Cmid ^ 2) ^ (-(6 / 5 : ℝ))⌉₊
  refine le_trans ?_ (etaArg_ge_second P hc' _)
  have hk : c' * (16 * P.Cmid ^ 2) ^ (-(6 / 5 : ℝ)) ≤ (⌈c' * (16 * P.Cmid ^ 2) ^ (-(6 / 5 : ℝ))⌉₊ : ℝ) :=
    Nat.le_ceil _
  have h1 : (16 * P.Cmid ^ 2) ^ (-(6 / 5 : ℝ)) ≤ (⌈c' * (16 * P.Cmid ^ 2) ^ (-(6 / 5 : ℝ))⌉₊ : ℝ) / c' := by
    rw [le_div_iff₀ hc']; linarith
  have h2 : (1 / (16 * P.Cmid ^ 2)) ≤ (((⌈c' * (16 * P.Cmid ^ 2) ^ (-(6 / 5 : ℝ))⌉₊ : ℝ) / c') ^ (5 / 6 : ℝ)) := by
    have := Real.rpow_le_rpow hs.le h1 (by norm_num : (0 : ℝ) ≤ 5 / 6)
    rw [← Real.rpow_mul hC.le] at this
    have e : (-(6 / 5 : ℝ)) * (5 / 6) = -1 := by norm_num
    rw [e, Real.rpow_neg_one] at this
    rwa [one_div]
  have hCm : 0 < P.Cmid ^ 2 := by have := P.one_le_Cmid; positivity
  have hne : P.Cmid ≠ 0 := ne_of_gt (by linarith [P.one_le_Cmid])
  calc (1 / 16 : ℝ) = P.Cmid ^ 2 * (1 / (16 * P.Cmid ^ 2)) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 hCm.le

/-- `∃ C₁, ∀ C ≥ C₁, (16 C²)^{-6/5} ≤ δ` for `δ > 0`. -/
lemma exists_Cmid_small {δ : ℝ} (hδ : 0 < δ) : ∃ C₁ : ℝ, ∀ C : ℝ, C₁ ≤ C → (16 * C ^ 2) ^ (-(6 / 5 : ℝ)) ≤ δ := by
  have h16 : Tendsto (fun C : ℝ => 16 * C ^ 2) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num) (tendsto_pow_atTop (by norm_num))
  have h := (tendsto_rpow_neg_atTop (show (0 : ℝ) < 6 / 5 by norm_num)).comp h16
  obtain ⟨C₁, hC₁⟩ := eventually_atTop.1 (h.eventually_le_const hδ)
  exact ⟨C₁, fun C hC => hC₁ C hC⟩

/-- **Step (1a): the block lies above the ramp.**  For every bump `bd` there is `C_sep` such that for every ramped
parameter set with `C_mid ≥ C_sep` and `c'` large, no index `k ≤ n_cap + 6` lies in the block
`ξ_* + 2 r_p ≤ χ_k ≤ X_p` of `bd`. -/
theorem rampedBlockAbove (bd : BumpData) :
    ∃ Csep : ℝ, ∀ P : RampedParams, Csep ≤ P.Cmid →
      ∀ᶠ c' : ℝ in atTop, bd.BlockAbove c' (nCap P c' + 6) := by
  have hk := kTip_pos
  have hr := bd.r_pos
  set ρ : ℝ := bd.r ^ (3 / 2 : ℝ) with hρ
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos hr _
  obtain ⟨C₁, hC₁⟩ := exists_Cmid_small (δ := kTip * ρ / 2) (by positivity)
  refine ⟨max C₁ 1, fun P hP => ?_⟩
  have hPC : C₁ ≤ P.Cmid := (le_max_left _ _).trans hP
  have hs := hC₁ P.Cmid hPC
  filter_upwards [eventually_ge_atTop (14 / (kTip * ρ)), eventually_gt_atTop (0 : ℝ)] with c' hc'14 hc'0
  intro k hk6 hblock
  -- `χ_{n_cap+6} < ξ_* + r_p`
  have hcap := nCap_le_of_Cmid P hc'0
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ c' * (16 * P.Cmid ^ 2) ^ (-(6 / 5 : ℝ)) by
    have : 0 ≤ (16 * P.Cmid ^ 2) ^ (-(6 / 5 : ℝ)) := Real.rpow_nonneg (by positivity) _
    positivity)
  have hncap : (nCap P c' : ℝ) ≤ c' * (16 * P.Cmid ^ 2) ^ (-(6 / 5 : ℝ)) + 1 := by
    have : (nCap P c' : ℝ) ≤ (⌈c' * (16 * P.Cmid ^ 2) ^ (-(6 / 5 : ℝ))⌉₊ : ℝ) := by exact_mod_cast hcap
    linarith
  have hN : ((nCap P c' + 6 : ℕ) : ℝ) ≤ kTip * ρ * c' := by
    have h1 : c' * (16 * P.Cmid ^ 2) ^ (-(6 / 5 : ℝ)) ≤ c' * (kTip * ρ / 2) :=
      mul_le_mul_of_nonneg_left hs hc'0.le
    have h2 : 14 ≤ kTip * ρ * c' := by
      have := (div_le_iff₀ (by positivity : 0 < kTip * ρ)).1 hc'14
      linarith
    push_cast
    nlinarith only [hncap, h1, h2]
  have hsq : (1 / 4 : ℝ) ≤ ((nCap P c' + 6 : ℕ) : ℝ) := by
    have : (0 : ℝ) ≤ (nCap P c' : ℝ) := Nat.cast_nonneg _
    push_cast; linarith
  have hb := (siteRadius_bounds hc'0 hsq).2
  have hphi := lambda_mul_phi_le hc'0 hsq
  have hrad : chiQuantile c' ((nCap P c' + 6 : ℕ) : ℝ) - xiStar ≤ bd.r := by
    have h3 : (((nCap P c' + 6 : ℕ) : ℝ) / (kTip * c')) ≤ ρ := by
      rw [div_le_iff₀ (by positivity)]; linarith
    have h4 : (((nCap P c' + 6 : ℕ) : ℝ) / (kTip * c')) ^ (2 / 3 : ℝ) ≤ ρ ^ (2 / 3 : ℝ) :=
      Real.rpow_le_rpow (by positivity) h3 (by norm_num)
    have h5 : ρ ^ (2 / 3 : ℝ) = bd.r := by
      rw [hρ, ← Real.rpow_mul hr.le]; norm_num
    unfold siteRadius at hb
    linarith
  have hlo := hblock.1
  unfold BumpData.lo at hlo
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · have : chiQuantile c' ((0 : ℕ) : ℝ) = xiStar := by
      unfold chiQuantile
      have hn : ¬ (0 < c' ∧ 1 / 4 ≤ ((0 : ℕ) : ℝ)) := fun h => by
        have := h.2
        norm_num at this
      simp only [hn, dite_false]
    rw [this] at hlo
    linarith
  · have hmono := chi_mono_nat hc'0 hk1 hk6
    linarith

/-- The cut of the bumped ramped comb: above the block of `bd` and above the ramp cut `n_cap + 6`. -/
noncomputable def rampedBumpCut (bd : BumpData) (P : RampedParams) (c' : ℝ) : ℕ :=
  bumpCut bd (nCap P c' + 6) c'

lemma le_rampedBumpCut (bd : BumpData) (P : RampedParams) (c' : ℝ) : nCap P c' + 6 ≤ rampedBumpCut bd P c' :=
  le_bumpCut bd _ c'

lemma rampedBumpCut_spec (bd : BumpData) (P : RampedParams) {c' : ℝ} (hc' : 0 < c') :
    ∀ k : ℕ, 1 ≤ k → chiQuantile c' (k : ℝ) ≤ bd.X → k ≤ rampedBumpCut bd P c' :=
  bumpCut_spec bd _ hc'

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.rampedBlockAbove' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rampedBlockAbove

end FormalResearch.ModularBootstrap.Upper.Ramped
