module

public import FormalResearch.ModularBootstrap.Duality.Primal.PositiveThreshold
public import FormalResearch.ModularBootstrap.Duality.ReserveSeparation

/-!
# Primal attainment and discreteness (Theorem E', `ds:primal`, `dual_spectrum.tex`)

For a compact `F ⊂ (0, ∞)` and `X_τ = F ∪ [τ, ∞)`, at a charge where `FixedChargeStrip` holds
(every `c̃ ≥ c₀(w, Q)`, `fixedChargeStrip_of_large`):

* `primal_extremal_of_sequence`: every normalised strictly feasible minimising sequence has a
  subsequence converging locally uniformly and in `M` to a weak extremal `g_*` (`M[g_*] = 1`,
  `g_{*,vac} = 0`, `g_* ≥ 0` on `X_{T_F}`) whose zero set is locally finite (strip holomorphy);
* `theorem_primal`: (a) existence of `g_*`; (b) every crossing measure on `X_{T_F}` is carried by
  `{g_* = 0}`; (c) every such measure is carried by a locally finite set and has `ν({T_F}) > 0`;
  (d) if `g_* > 0` on a compact `E ⊂ (0, ∞)` then `T_{F ∪ E} = T_F` and every crossing measure on
  `F ∪ E ∪ [T_F, ∞)` gives `E` zero mass.
-/

@[expose] public section

open MeasureTheory Filter Topology Set Complex
open scoped Real

namespace FormalResearch.ModularBootstrap.FixedWeight

open Crossing WeightAxioms FormalResearch.ModularBootstrap.Duality

variable {prob : FixedWeightProblem} {cTilde : ℝ}

/-- **Weak extremal from a normalised minimising sequence** (`ds:primal`(a)). -/
theorem primal_extremal_of_sequence (S : FixedChargeStrip prob cTilde) {F : Set ℝ}
    (hFc : IsCompact F) (hF : F ⊆ Ioi 0) {τ : ℕ → ℝ} {g : ℕ → ℝ → ℝ}
    (hfeas : ∀ k, prob.IsFeasibleOn (cTilde / 12) (F ∪ Ici (τ k)) (g k))
    (hτ : Tendsto τ atTop (𝓝 (constrainedThreshold prob cTilde F)))
    (hM : ∀ k, prob.cardyNorm (cTilde / 12) (g k) = 1) :
    ∃ (φ : ℕ → ℕ) (gs : ℝ → ℝ), StrictMono φ ∧ TestClass prob (cTilde / 12) gs ∧
      prob.cardyNorm (cTilde / 12) gs = 1 ∧ prob.gVac (cTilde / 12) gs = 0 ∧
      (∀ t ∈ F ∪ Ici (constrainedThreshold prob cTilde F), 0 ≤ gs t) ∧
      (∀ R : ℝ, TendstoUniformlyOn (fun k => g (φ k)) gs atTop (Icc 0 R)) ∧
      Tendsto (fun k => ∫ t in Ioi (0 : ℝ), |g (φ k) t - gs t| * prob.cardyV (cTilde / 12) t)
        atTop (𝓝 0) ∧
      (∀ R : ℝ, {t ∈ Icc (0 : ℝ) R | gs t = 0}.Finite) ∧ (∃ t : ℝ, 0 ≤ t ∧ gs t ≠ 0) ∧
      (∃ G : ℂ → ℂ, DifferentiableOn ℂ G openStrip ∧
        ∀ t : ℝ, 0 ≤ t → G (stripCoord cTilde t : ℂ) = (gs t : ℂ)) := by
  classical
  set a : ℝ := cTilde / 12 with ha_def
  set TF : ℝ := constrainedThreshold prob cTilde F with hTF
  have hTV := T_V_pos_of_strip S
  obtain ⟨⟨hle, hne⟩, ⟨⟨hTFpos, meas, hν⟩, -⟩, -, -⟩ :=
    theorem_E_b_compact prob S.hc_pos S.hc hFc hF hTV
  have hTF0 : 0 < TF := lt_of_lt_of_le hTV hle
  have hsh : prob.totalShift ≤ a := by linarith [S.hc]
  have ha0 : 0 < a := by linarith [S.hc_pos]
  -- discard finitely many terms
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hτ.eventually (gt_mem_nhds (show TF < TF + 1 by linarith)))
  set g' : ℕ → ℝ → ℝ := fun k => g (k + N) with hg'
  have hg'f : ∀ k, prob.IsFeasibleOn a (F ∪ Ici (τ (k + N))) (g' k) := fun k => hfeas (k + N)
  have hτ' : ∀ k, τ (k + N) ≤ TF + 1 := fun k => (hN (k + N) (by omega)).le
  have hneg : ∀ k, ∀ t ≥ TF + 1, 0 ≤ g' k t := fun k t ht =>
    (hg'f k).2.2 t (Or.inr (le_trans (hτ' k) ht))
  have hv : ∀ k, ∫ t in Ioi (0 : ℝ), g' k t * prob.cardyV a t ≤ 0 := fun k => by
    have h1 := (hg'f k).2.1
    have : prob.gVac a (g' k) = -2 * π * ∫ t in Ioi (0 : ℝ), g' k t * prob.cardyV a t := rfl
    nlinarith [Real.pi_pos]
  obtain ⟨φ, gs, hφ, htc, hnn, hunif, hMle, hvac0, hne0, hzero, hG, himp⟩ :=
    exists_primal_limit S (fun k => (hg'f k).1) (fun k => hM (k + N)) hv (R₀ := TF + 1)
      (by linarith) hneg
  have hgs_cont : ContinuousOn gs (Ici 0) := htc.cont
  have hpt : ∀ t : ℝ, 0 ≤ t → Tendsto (fun k => g' (φ k) t) atTop (𝓝 (gs t)) := fun t ht =>
    (hunif t).tendsto_at ⟨ht, le_rfl⟩
  -- `g_* ≥ 0` on `X_{T_F}`
  have hφN : Tendsto (fun k => φ k + N) atTop atTop :=
    tendsto_atTop_add_const_right atTop N hφ.tendsto_atTop
  have hτφ : Tendsto (fun k => τ (φ k + N)) atTop (𝓝 TF) := hτ.comp hφN
  have hnn_F : ∀ t ∈ F, 0 ≤ gs t := fun t ht =>
    ge_of_tendsto (hpt t (le_of_lt (hF ht)))
      (Eventually.of_forall fun k => (hg'f (φ k)).2.2 t (Or.inl ht))
  have hnn_gt : ∀ t, TF < t → 0 ≤ gs t := fun t ht =>
    ge_of_tendsto (hpt t (by linarith))
      ((hτφ.eventually (gt_mem_nhds ht)).mono fun k hk =>
        (hg'f (φ k)).2.2 t (Or.inr (le_of_lt hk)))
  have hnn_TF : 0 ≤ gs TF := by
    have hcont : ContinuousAt gs TF := by
      refine (hgs_cont.continuousAt (Ici_mem_nhds hTF0))
    exact ge_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds : Tendsto gs (𝓝[>] TF) _)
      (eventually_nhdsWithin_of_forall fun t ht => hnn_gt t ht)
  have hnn_X : ∀ t ∈ F ∪ Ici TF, 0 ≤ gs t := fun t ht => by
    rcases ht with ht | ht
    · exact hnn_F t ht
    · rcases (mem_Ici.1 ht).eq_or_lt with h | h
      · rw [← h]; exact hnn_TF
      · exact hnn_gt t h
  -- `g_{*,vac} ≤ 0` by pairing with a crossing measure on `X_{T_F}`
  have hvac_le : prob.gVac a gs ≤ 0 := by
    obtain ⟨hint, hle1⟩ := lemma_fwX_one_sided_unconditional prob hsh ha0 meas htc (T := TF)
      (fun t ht => hnn_X t (Or.inr ht))
    have hae : ∀ᵐ t ∂meas.ν, 0 ≤ gs t := by
      have : ∀ᵐ y ∂meas.ν, y ∉ (F ∪ Ici TF)ᶜ := measure_eq_zero_iff_ae_notMem.1 hν
      filter_upwards [this] with y hy using hnn_X y (by simpa using hy)
    rw [Duality.restrict_Ici_eq_self meas] at hle1
    have h0 : 0 ≤ ∫ t, gs t ∂meas.ν := integral_nonneg_of_ae hae
    linarith
  have hvac_eq : prob.gVac a gs = 0 := le_antisymm hvac_le hvac0
  obtain ⟨hM1, hconv⟩ := himp hvac_le
  refine ⟨fun k => φ k + N, gs, ?_, htc, hM1, hvac_eq, hnn_X, ?_, ?_, hzero, hne0, hG⟩
  · exact hφ.add_const N
  · exact hunif
  · exact hconv

end FormalResearch.ModularBootstrap.FixedWeight
