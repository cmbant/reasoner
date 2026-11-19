module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.Order.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# `L¹` control of squares of `L²` functions under cardinal truncation (CEQ22, GT.0)

Source: `CFT/notes/ce_o1_global_transfer.tex`, the GT.0 paragraph ("for such a seed, if `H_{c,N} → H_c` in `L²`,
then `‖H_{c,N}² − H_c²‖₁ ≤ (‖H_{c,N}‖₂ + ‖H_c‖₂) ‖H_{c,N} − H_c‖₂ → 0`"); queue row CEQ22 of
`CFT/modular_bootstrap/notes/CE_MISSING_QUEUE.md`.

**Statements proved** (both for `𝕜 = ℝ` or `𝕜 = ℂ`, i.e. any `RCLike 𝕜`, on `ℝ` with Lebesgue measure):

* `eLpNorm_sq_sub_sq_le`: `‖H_N² − H²‖₁ ≤ (‖H_N‖₂ + ‖H‖₂) ‖H_N − H‖₂` (exact, with `eLpNorm` norms).
* `tendsto_eLpNorm_sq_sub_sq`: if `‖H_i − H‖₂ → 0` along a filter, then `‖H_i² − H²‖₁ → 0`.

**Proof.** `H_N² − H² = (H_N − H)(H_N + H)` and `‖H_N + H‖ ≤ ‖H_N‖ + ‖H‖` pointwise; then Hölder with exponents
`(2, 2, 1)` on the product of norms, and Minkowski for `‖H_N‖ + ‖H‖`. The corollary bounds `‖H_i‖₂ ≤ ‖H_i − H‖₂ + ‖H‖₂`
and squeezes.

**Not covered.** The truncation limit itself (the cardinal Paley–Wiener convergence `H_{c,N} → H_c` in GT.0 and the
`H^∞` estimate that follows) is not formalised; only the `L¹` inequality and its limit form used there.
-/

@[expose] public section

namespace FormalResearch.CohnElkies

open MeasureTheory Filter Topology
open scoped ENNReal

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Pointwise factorisation: `‖a² − b²‖ = ‖a − b‖ ‖a + b‖ ≤ ‖a − b‖ (‖a‖ + ‖b‖)`. -/
lemma norm_sq_sub_sq_le (a b : 𝕜) : ‖a ^ 2 - b ^ 2‖ ≤ ‖a - b‖ * (‖a‖ + ‖b‖) := by
  have e : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
  rw [e, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_add_le a b) (norm_nonneg _)

/-- **CEQ22 (GT.0), inequality form.** For `L²` functions `H_N, H` on `ℝ`,
`‖H_N² − H²‖₁ ≤ (‖H_N‖₂ + ‖H‖₂) ‖H_N − H‖₂`. -/
theorem eLpNorm_sq_sub_sq_le (HN H : ℝ → 𝕜) (hHN : MemLp HN 2 volume) (hH : MemLp H 2 volume) :
    eLpNorm (fun x => HN x ^ 2 - H x ^ 2) 1 volume ≤
      (eLpNorm HN 2 volume + eLpNorm H 2 volume) * eLpNorm (fun x => HN x - H x) 2 volume := by
  have hmeas_sq : AEStronglyMeasurable (fun x => HN x ^ 2 - H x ^ 2) volume :=
    (hHN.aestronglyMeasurable.pow 2).sub (hH.aestronglyMeasurable.pow 2)
  have hd : AEStronglyMeasurable (fun x => ‖HN x - H x‖) volume :=
    (hHN.aestronglyMeasurable.sub hH.aestronglyMeasurable).norm
  have hs : AEStronglyMeasurable (fun x => ‖HN x‖ + ‖H x‖) volume :=
    hHN.aestronglyMeasurable.norm.add hH.aestronglyMeasurable.norm
  -- (a) pointwise domination by a product of real norms
  have step1 : eLpNorm (fun x => HN x ^ 2 - H x ^ 2) 1 volume ≤
      eLpNorm (fun x => ‖HN x - H x‖ * (‖HN x‖ + ‖H x‖)) 1 volume :=
    eLpNorm_mono_real hmeas_sq fun x => norm_sq_sub_sq_le (HN x) (H x)
  -- (b) Hölder with exponents (2, 2, 1) on the product of norms
  have step2 : eLpNorm (fun x => ‖HN x - H x‖ * (‖HN x‖ + ‖H x‖)) 1 volume ≤
      eLpNorm (fun x => ‖HN x - H x‖) 2 volume * eLpNorm (fun x => ‖HN x‖ + ‖H x‖) 2 volume := by
    have hcont : Continuous (fun p : ℝ × ℝ => p.1 * p.2) := continuous_fst.mul continuous_snd
    have hpt : ∀ᵐ x ∂(volume : Measure ℝ),
        ‖(fun a b : ℝ => a * b) (‖HN x - H x‖) (‖HN x‖ + ‖H x‖)‖ ≤
          ((1 : NNReal) : ℝ) * ‖‖HN x - H x‖‖ * ‖‖HN x‖ + ‖H x‖‖ := by
      refine ae_of_all _ fun x => ?_
      have h1 : 0 ≤ ‖HN x - H x‖ := norm_nonneg _
      have h2 : 0 ≤ ‖HN x‖ + ‖H x‖ := by positivity
      simp only [NNReal.coe_one, one_mul, norm_mul, Real.norm_of_nonneg h1,
        Real.norm_of_nonneg h2, le_refl]
    have := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm (p := 2) (q := 2) (r := 1)
      (fun a b : ℝ => a * b) 1 hcont hd hs hpt
    simpa using this
  -- (c) Minkowski for the sum of norms, and `‖·‖` does not change the `L²` norm
  have step3 : eLpNorm (fun x => ‖HN x‖ + ‖H x‖) 2 volume ≤
      eLpNorm HN 2 volume + eLpNorm H 2 volume := by
    have h : eLpNorm (fun x => ‖HN x‖ + ‖H x‖) 2 volume
        ≤ eLpNorm (fun x => ‖HN x‖) 2 volume + eLpNorm (fun x => ‖H x‖) 2 volume :=
      eLpNorm_add_le (by norm_num)
    rwa [eLpNorm_norm HN hHN.aestronglyMeasurable, eLpNorm_norm H hH.aestronglyMeasurable] at h
  have hdiff : eLpNorm (fun x => ‖HN x - H x‖) 2 volume = eLpNorm (fun x => HN x - H x) 2 volume :=
    eLpNorm_norm _ (hHN.aestronglyMeasurable.sub hH.aestronglyMeasurable)
  calc eLpNorm (fun x => HN x ^ 2 - H x ^ 2) 1 volume
      ≤ eLpNorm (fun x => ‖HN x - H x‖ * (‖HN x‖ + ‖H x‖)) 1 volume := step1
    _ ≤ eLpNorm (fun x => ‖HN x - H x‖) 2 volume * eLpNorm (fun x => ‖HN x‖ + ‖H x‖) 2 volume :=
        step2
    _ ≤ eLpNorm (fun x => HN x - H x) 2 volume * (eLpNorm HN 2 volume + eLpNorm H 2 volume) := by
        rw [hdiff]
        exact mul_le_mul' le_rfl step3
    _ = (eLpNorm HN 2 volume + eLpNorm H 2 volume) * eLpNorm (fun x => HN x - H x) 2 volume :=
        mul_comm _ _

/-- **CEQ22 (GT.0), limit form.** If `H_i → H` in `L²` along a filter (`‖H_i − H‖₂ → 0`), then
`H_i² → H²` in `L¹` (`‖H_i² − H²‖₁ → 0`). The `H_i` and `H` are `L²` functions on `ℝ`. -/
theorem tendsto_eLpNorm_sq_sub_sq {ι : Type*} {l : Filter ι} (HN : ι → ℝ → 𝕜) (H : ℝ → 𝕜)
    (hHN : ∀ i, MemLp (HN i) 2 volume) (hH : MemLp H 2 volume)
    (hconv : Tendsto (fun i => eLpNorm (fun x => HN i x - H x) 2 volume) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm (fun x => HN i x ^ 2 - H x ^ 2) 1 volume) l (𝓝 0) := by
  set K : ℝ≥0∞ := eLpNorm H 2 volume with hK
  have hKtop : K ≠ ⊤ := hH.eLpNorm_lt_top.ne
  set δ : ι → ℝ≥0∞ := fun i => eLpNorm (fun x => HN i x - H x) 2 volume with hδdef
  -- triangle inequality: `‖H_i‖₂ ≤ ‖H_i − H‖₂ + ‖H‖₂`
  have htri : ∀ i, eLpNorm (HN i) 2 volume ≤ δ i + K := by
    intro i
    have h : eLpNorm (fun x => HN i x - H x + H x) 2 volume
        ≤ eLpNorm (fun x => HN i x - H x) 2 volume + eLpNorm H 2 volume :=
      eLpNorm_add_le (by norm_num)
    have e : (fun x => HN i x - H x + H x) = HN i := funext fun x => sub_add_cancel _ _
    rw [e] at h
    exact h
  -- the pointwise bound on the `L¹` norm
  have hbound : ∀ i, eLpNorm (fun x => HN i x ^ 2 - H x ^ 2) 1 volume ≤ ((δ i + K) + K) * δ i := by
    intro i
    have h := eLpNorm_sq_sub_sq_le (HN i) H (hHN i) hH
    exact h.trans (mul_le_mul' (add_le_add (htri i) le_rfl) le_rfl)
  -- the upper bound tends to zero
  have hδt : Tendsto δ l (𝓝 0) := hconv
  have hA : Tendsto (fun i => (δ i + K) + K) l (𝓝 ((0 + K) + K)) :=
    (hδt.add tendsto_const_nhds).add tendsto_const_nhds
  have hKK : (0 + K) + K ≠ ⊤ := by
    rw [zero_add]
    exact ENNReal.add_ne_top.2 ⟨hKtop, hKtop⟩
  have hup : Tendsto (fun i => ((δ i + K) + K) * δ i) l (𝓝 (((0 + K) + K) * 0)) :=
    ENNReal.Tendsto.mul hA (Or.inr ENNReal.zero_ne_top) hδt (Or.inr hKK)
  rw [mul_zero] at hup
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun _ => zero_le) hbound

/-- info: 'FormalResearch.CohnElkies.eLpNorm_sq_sub_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eLpNorm_sq_sub_sq_le

/-- info: 'FormalResearch.CohnElkies.tendsto_eLpNorm_sq_sub_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tendsto_eLpNorm_sq_sub_sq

end FormalResearch.CohnElkies
