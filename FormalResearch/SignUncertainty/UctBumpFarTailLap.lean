module

public import FormalResearch.SignUncertainty.UctBumpFarSplit
public import FormalResearch.SignUncertainty.UctBumpEdge

/-!
# Uniform bounds for the Laplace transforms of the smooth tail (F2a, `uct:bump-weighted` far band)

For `B` a `BumpProfile 1 1 M α β K` (support in `[1, ∞)`, `|B^{(k)}| ≤ K_k M x^{-β-k}`, `β ≥ 3/2`), the damped transforms `bumpLapW B m s = ∫ e^{-sx} x^m B` (`m ≤ 2`, `Re s > 0`) obey, with constants depending
only on `K, m, N`:

* `tailLapW_decay`: `‖bumpLapW B m s‖ ≤ K^{(m)}_N M ‖s‖^{-N}` for every `N ≥ 3`;
* `tailLapW_small`: `‖bumpLapW B m s‖ ≤ A_m M ‖s‖^{1/2-m}` for `m = 1, 2`, `‖s‖ ≤ 1`;
* `tailLapW_zero`: `‖bumpLapW B 0 s‖ ≤ 2 |K_0| M`.

These are the proofs of `tail_bound`/`head_bound`/`bumpLapW_bound` of `UctBumpEdge` with explicit constants (`tail_bound_D`, `bumpLapW_bound_of_tail`) and `mulPow_bound` for the derivatives of `x^m B`.

Class: proved, no hypotheses.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

namespace BumpProfile

variable {M α β : ℝ} {K : ℕ → ℝ} {B : ℝ → ℝ}

lemma iteratedDeriv_zero_le_one (h : BumpProfile 1 1 M α β K B) (k : ℕ) {x : ℝ} (hx : x ≤ 1) : iteratedDeriv k B x = 0 :=
  zero_of_zero_left (h.contDiff_iteratedDeriv k).continuous (a := 1)
    (fun y hy => h.zero_of_lt k (by simpa using hy)) hx

lemma zero_le_one (h : BumpProfile 1 1 M α β K B) {x : ℝ} (hx : x ≤ 1) : B x = 0 := by
  simpa using h.iteratedDeriv_zero_le_one 0 hx

/-- `∫ ‖B‖ ≤ 2 |K₀| M` for the tail profile. -/
lemma integral_norm_le (h : BumpProfile 1 1 M α β K B) (hM : 0 ≤ M) (hβ : 3 / 2 ≤ β) :
    ∫ x : ℝ, ‖B x‖ ≤ 2 * |K 0| * M := by
  have hβ1 : 1 < β := by linarith
  have hBi : Integrable B := h.integrable_self (by norm_num) hβ1
  have hint : IntegrableOn (fun x : ℝ => x ^ (-β)) (Ioi 1) := integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  have h1 : ∫ x : ℝ, ‖B x‖ = ∫ x in Ioi (1 : ℝ), ‖B x‖ := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    rw [h.zero_le_one (not_lt.mp hx), norm_zero]
  rw [h1]
  have h2 : ∫ x in Ioi (1 : ℝ), ‖B x‖ ≤ ∫ x in Ioi (1 : ℝ), |K 0| * M * x ^ (-β) := by
    refine setIntegral_mono_on hBi.norm.integrableOn (hint.const_mul _) measurableSet_Ioi fun x hx => ?_
    have hx1 : (1 : ℝ) < x := hx
    have hf := h.far 0 x hx1.le
    simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero] at hf
    rw [Real.norm_eq_abs]
    refine hf.trans ?_
    have : K 0 * M ≤ |K 0| * M := mul_le_mul_of_nonneg_right (le_abs_self _) hM
    exact mul_le_mul_of_nonneg_right this (Real.rpow_nonneg (by linarith) _)
  refine h2.trans ?_
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) one_pos]
  have : -((1 : ℝ) ^ (-β + 1)) / (-β + 1) = 1 / (β - 1) := by
    rw [Real.one_rpow]
    have : (β - 1) ≠ 0 := by linarith
    have : (-β + 1) ≠ 0 := by linarith
    field_simp
    ring
  rw [this]
  have hK : 0 ≤ |K 0| * M := by positivity
  have : 1 / (β - 1) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  nlinarith

lemma tailLapW_zero (h : BumpProfile 1 1 M α β K B) (hM : 0 ≤ M) (hβ : 3 / 2 ≤ β) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖bumpLapW B 0 s‖ ≤ 2 * |K 0| * M := by
  refine le_trans ?_ (h.integral_norm_le hM hβ)
  unfold bumpLapW
  have hBi : Integrable B := h.integrable_self (by norm_num) (by linarith)
  refine norm_integral_le_of_norm_le hBi.norm (ae_of_all _ fun x => ?_)
  rcases lt_or_ge x 1 with hx | hx
  · rw [h.zero_le_one hx.le]; simp
  · simp only [pow_zero, one_mul]
    rw [norm_mul, bump_norm_exp_neg_mul, Complex.norm_real]
    have : Real.exp (-(s.re * x)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    calc Real.exp (-(s.re * x)) * ‖B x‖ ≤ 1 * ‖B x‖ := by gcongr
      _ = _ := one_mul _

lemma tailLapW_decay (h : BumpProfile 1 1 M α β K B) (hM : 0 ≤ M) (hβ : 3 / 2 ≤ β) (m N : ℕ) (hm : m ≤ 2) (hN : 3 ≤ N)
    {s : ℂ} (hs : 0 < s.re) :
    ‖bumpLapW B m s‖ ≤ mulPowK K m N * M * (‖s‖⁻¹) ^ N := by
  set u : ℝ → ℝ := fun y => y ^ m * B y with hu
  have hup := h.mulPow one_pos one_pos hM m
  have hm2 : (m : ℝ) ≤ 2 := by exact_mod_cast hm
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hz : ∀ k : ℕ, iteratedDeriv k u 1 = 0 := fun k => hup.iteratedDeriv_zero_le_one k le_rfl
  have heq : bumpLapW B m s = ∫ x in Ioi (1 : ℝ), Complex.exp (-s * (x : ℂ)) * (u x : ℂ) := by
    unfold bumpLapW
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    have := hup.zero_le_one (not_lt.mp hx)
    simp only [hu] at this ⊢
    rw [this]; simp
  have hb : ∀ k : ℕ, k ≤ N → ∃ A p : ℝ, ∀ x ≥ (1 : ℝ), |iteratedDeriv k u x| ≤ A * x ^ p :=
    fun k _ => ⟨mulPowK K m k * M, -(β - m) - k, fun x hx => hup.far k x hx⟩
  have hint : IntegrableOn (fun x : ℝ => x ^ (-(β - m) - (N : ℝ))) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  have hI : IntegrableOn (iteratedDeriv N u) (Ioi 1) := by
    refine (hint.const_mul (mulPowK K m N * M)).mono' ?_ ?_
    · exact ((hup.contDiff_iteratedDeriv N).continuous.aestronglyMeasurable).restrict
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [Real.norm_eq_abs]; exact hup.far N x (le_of_lt hx)
  rw [heq]
  refine (tail_iter (le_refl (1 : ℝ)) hs N u hup.smooth hb hI).trans ?_
  have hsum : ∑ k ∈ Finset.range N, (‖s‖⁻¹) ^ (k + 1) * |iteratedDeriv k u 1| = 0 :=
    Finset.sum_eq_zero fun k _ => by rw [hz k]; simp
  rw [hsum, zero_add]
  have h2 : ∫ x in Ioi (1 : ℝ), |iteratedDeriv N u x| ≤ mulPowK K m N * M := by
    refine (setIntegral_mono_on hI.norm (hint.const_mul (mulPowK K m N * M)) measurableSet_Ioi fun x hx => ?_).trans ?_
    · rw [Real.norm_eq_abs]; exact hup.far N x (le_of_lt hx)
    · rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) one_pos, Real.one_rpow]
      have hK : 0 ≤ mulPowK K m N * M := by have := mulPowK_nonneg K m N; positivity
      have : -(1 : ℝ) / (-(β - m) - (N : ℝ) + 1) ≤ 1 := by
        rw [div_le_iff_of_neg (by linarith)]; linarith
      nlinarith
  calc (‖s‖⁻¹) ^ N * ∫ x in Ioi (1 : ℝ), |iteratedDeriv N u x| ≤ (‖s‖⁻¹) ^ N * (mulPowK K m N * M) := by
        gcongr
    _ = _ := by ring

lemma tailLapW_small (h : BumpProfile 1 1 M α β K B) (hM : 0 ≤ M) (hβ : 3 / 2 ≤ β) (m : ℕ) (hm1 : 1 ≤ m) {s : ℂ}
    (hs : 0 < s.re) (hs1 : ‖s‖ ≤ 1) :
    ‖bumpLapW B m s‖ ≤ (4 * |K 0| + ∑ k ∈ Finset.range (m + 1), mulPowK K m k + mulPowK K m (m + 1)) * M *
      (‖s‖⁻¹) ^ ((m : ℝ) - 1 / 2) := by
  set D : ℕ → ℝ := fun k => mulPowK K m k * M with hDdef
  have hD0 : ∀ k, 0 ≤ D k := fun k => by have := mulPowK_nonneg K m k; simp only [hDdef]; positivity
  have hD : ∀ k : ℕ, ∀ x : ℝ, 1 ≤ x → |iteratedDeriv k (fun y : ℝ => y ^ m * B y) x| ≤ D k * x ^ ((m : ℝ) - β - k) := by
    intro k x hx
    have := mulPow_bound h.smooth hM (by linarith : (0 : ℝ) < x) m k (fun j _ => h.far j x hx)
    simp only [hDdef]
    rwa [show -(β - (m : ℝ)) - (k : ℝ) = (m : ℝ) - β - k by ring] at this
  have hCt := tail_bound_D h.smooth hβ m D hD0 hD
  have key := h.bumpLapW_bound_of_tail (by norm_num) (by norm_num) hβ hM m hm1 hCt s hs hs1
  refine key.trans ?_
  have hR : 0 ≤ (‖s‖⁻¹) ^ ((m : ℝ) - 1 / 2) := Real.rpow_nonneg (by positivity) _
  have hI := h.integral_norm_le hM hβ
  have hβ1 : 1 / β ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hDm : D (m + 1) / β ≤ D (m + 1) := by
    calc D (m + 1) / β = D (m + 1) * (1 / β) := by ring
      _ ≤ D (m + 1) * 1 := by gcongr; exact hD0 _
      _ = _ := mul_one _
  have hsum : ∑ k ∈ Finset.range (m + 1), D k = (∑ k ∈ Finset.range (m + 1), mulPowK K m k) * M := by
    simp only [hDdef]; rw [Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ hR
  have e1 : 2 * |K 0| * M + 2 * |K 0| * M = 4 * |K 0| * M := by ring
  calc (∫ x : ℝ, ‖B x‖) + 2 * |K 0| * M + ((∑ k ∈ Finset.range (m + 1), D k) + D (m + 1) / β)
      ≤ 2 * |K 0| * M + 2 * |K 0| * M + ((∑ k ∈ Finset.range (m + 1), D k) + D (m + 1)) := by
        gcongr
    _ = _ := by rw [e1, hsum]; simp only [hDdef]; ring

end BumpProfile

/-- The constant of `tailLapW_small`. -/
noncomputable def tailA (K : ℕ → ℝ) (m : ℕ) : ℝ :=
  4 * |K 0| + ∑ k ∈ Finset.range (m + 1), mulPowK K m k + mulPowK K m (m + 1)

lemma tailA_nonneg (K : ℕ → ℝ) (m : ℕ) : 0 ≤ tailA K m := by
  unfold tailA
  have := Finset.sum_nonneg fun k (_ : k ∈ Finset.range (m + 1)) => mulPowK_nonneg K m k
  have := mulPowK_nonneg K m (m + 1)
  positivity

namespace BumpProfile

variable {M α β : ℝ} {K : ℕ → ℝ} {B : ℝ → ℝ}

/-- Pointwise bounds in terms of any `u ≤ ‖s‖`. -/
lemma tailPhi_pt (h : BumpProfile 1 1 M α β K B) (hM : 0 ≤ M) (hβ : 3 / 2 ≤ β) {s : ℂ} (hs : 0 < s.re) {u : ℝ}
    (hu : 0 < u) (hsu : u ≤ ‖s‖) (m N : ℕ) (hm : m ≤ 2) (hN : 3 ≤ N) :
    ‖bumpLapW B m s‖ ≤ M * mulPowK K m N * (u⁻¹) ^ N ∧
      (1 ≤ m → u ≤ 1 → ‖bumpLapW B m s‖ ≤ M * (tailA K m + mulPowK K m N) * (u⁻¹) ^ ((m : ℝ) - 1 / 2)) := by
  have hsn : 0 < ‖s‖ := lt_of_lt_of_le hu hsu
  have hinv : ‖s‖⁻¹ ≤ u⁻¹ := inv_anti₀ hu hsu
  have hD := h.tailLapW_decay hM hβ m N hm hN hs
  have hDK := mulPowK_nonneg K m N
  have hA := tailA_nonneg K m
  have hd1 : ‖bumpLapW B m s‖ ≤ M * mulPowK K m N * (u⁻¹) ^ N := by
    refine hD.trans ?_
    calc mulPowK K m N * M * (‖s‖⁻¹) ^ N ≤ mulPowK K m N * M * (u⁻¹) ^ N := by gcongr
      _ = _ := by ring
  refine ⟨hd1, fun hm1 hu1 => ?_⟩
  have hexp : 0 ≤ (m : ℝ) - 1 / 2 := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    linarith
  by_cases hs1 : ‖s‖ ≤ 1
  · have := h.tailLapW_small hM hβ m hm1 hs hs1
    refine this.trans ?_
    have h2 : (‖s‖⁻¹) ^ ((m : ℝ) - 1 / 2) ≤ (u⁻¹) ^ ((m : ℝ) - 1 / 2) := Real.rpow_le_rpow (by positivity) hinv hexp
    calc tailA K m * M * (‖s‖⁻¹) ^ ((m : ℝ) - 1 / 2) ≤ tailA K m * M * (u⁻¹) ^ ((m : ℝ) - 1 / 2) := by gcongr
      _ ≤ M * (tailA K m + mulPowK K m N) * (u⁻¹) ^ ((m : ℝ) - 1 / 2) := by
          have : 0 ≤ (u⁻¹) ^ ((m : ℝ) - 1 / 2) := Real.rpow_nonneg (by positivity) _
          nlinarith [mul_nonneg hM hDK, mul_nonneg (mul_nonneg hM hDK) this]
  · have hs1' : 1 < ‖s‖ := not_le.mp hs1
    have hi1 : ‖s‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hs1'.le
    have h3 : (‖s‖⁻¹) ^ N ≤ 1 := pow_le_one₀ (by positivity) hi1
    have h4 : 1 ≤ (u⁻¹) ^ ((m : ℝ) - 1 / 2) := Real.one_le_rpow (one_le_inv₀ hu |>.mpr hu1) hexp
    refine hD.trans ?_
    calc mulPowK K m N * M * (‖s‖⁻¹) ^ N ≤ mulPowK K m N * M * 1 := by gcongr
      _ ≤ mulPowK K m N * M * (u⁻¹) ^ ((m : ℝ) - 1 / 2) := by gcongr
      _ ≤ M * (tailA K m + mulPowK K m N) * (u⁻¹) ^ ((m : ℝ) - 1 / 2) := by
          have : 0 ≤ (u⁻¹) ^ ((m : ℝ) - 1 / 2) := Real.rpow_nonneg (by positivity) _
          nlinarith [mul_nonneg hM hA, mul_nonneg (mul_nonneg hM hA) this]

end BumpProfile

/-- info: 'FormalResearch.SignUncertainty.BumpProfile.tailLapW_decay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BumpProfile.tailLapW_decay

/-- info: 'FormalResearch.SignUncertainty.BumpProfile.tailLapW_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BumpProfile.tailLapW_small

/-- info: 'FormalResearch.SignUncertainty.BumpProfile.tailLapW_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BumpProfile.tailLapW_zero

/-- info: 'FormalResearch.SignUncertainty.BumpProfile.tailPhi_pt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BumpProfile.tailPhi_pt

end FormalResearch.SignUncertainty
