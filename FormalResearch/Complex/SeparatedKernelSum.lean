module

public import Mathlib

/-!
# A uniform bound for Cauchy-kernel sums over a separated sequence

Generic real analysis, no Airy content.  **Proved.**  Let `S` be a finite set of indices, `c : ι → ℝ` positive and `d : ι → ℕ`
injective on `S` (a "label"), with

* growth `κ (d i + 1)² ≤ c_i⁶`,
* separation `s (|d i - d j| - 1) ≤ |c_i - c_j| · max(c_i, c_j)²` for `i ≠ j` in `S` (the zeros `√(-a_n)` of `Ai` have `c_n³ ≍ n`, so
  `|c_n - c_m| ≳ |n - m| / max(c_n,c_m)²`; for the zeros of `P Ai + Q Ai'`, which interlace those of `Ai`, the labels are the gap
  indices and the separation holds up to the shift `-1`),

and put `r_i = 1/(4 c_i²)`.  Then (`separated_kernel_sum`) there is `K` (depending on `s, κ` only) with
`Σ_{i∈S} r_i² / ((t - c_i)² + r_i²) ≤ K` for every real `t` and every finite `S`.

Proof: let `m ∈ S` minimise `|t - c_i|`; for `i ≠ m` one has `|c_i - c_m| ≤ 2|t - c_i|`.  At most two `i` have `|d i - d m| = 1` (term `≤ 1`);
for the rest `s(|d i - d m| - 1) ≥ (s/2)|d i - d m|`, and if `c_m ≤ 2 c_i` the separation gives
`r_i²/(t-c_i)² ≤ 16/(s²(d i - d m)²)`, while if `c_m > 2 c_i` then `|t - c_i| ≥ c_i/2` and the term is `≤ 1/(4 c_i⁶) ≤ 1/(4κ(d i+1)²)`;
both are summable (the first over `ℤ`, by injectivity of `d`).  The `m`-th term is `≤ 1`.
-/

@[expose] public section

open Finset

namespace FormalResearch.Hardy

/-- The two pointwise bounds for a single kernel term. -/
lemma kernel_term_le {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    (1 / (4 * c ^ 2)) ^ 2 / (d ^ 2 + (1 / (4 * c ^ 2)) ^ 2) ≤ 1 / (16 * c ^ 4 * d ^ 2) := by
  have hr : (1 / (4 * c ^ 2)) ^ 2 = 1 / (16 * c ^ 4) := by
    field_simp; ring
  rw [hr]
  have h1 : 1 / (16 * c ^ 4) / (d ^ 2 + 1 / (16 * c ^ 4)) ≤ 1 / (16 * c ^ 4) / d ^ 2 := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    linarith [show 0 < 1 / (16 * c ^ 4) by positivity]
  refine h1.trans (le_of_eq ?_)
  field_simp

lemma kernel_caseA {c d σ : ℝ} (hc : 0 < c) (hd : 0 < d) (hσ : 0 < σ) (h : σ ≤ 8 * c ^ 2 * d) :
    1 / (16 * c ^ 4 * d ^ 2) ≤ 4 / σ ^ 2 := by
  have hsq : σ ^ 2 ≤ 64 * c ^ 4 * d ^ 2 := by
    have := pow_le_pow_left₀ hσ.le h 2
    nlinarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

lemma kernel_caseB {c d κ e : ℝ} (hc : 0 < c) (hκ : 0 < κ) (he : 0 < e) (hd : c / 2 ≤ d)
    (h6 : κ * e ≤ c ^ 6) : 1 / (16 * c ^ 4 * d ^ 2) ≤ 1 / (4 * κ) * (1 / e) := by
  have hsq : (c / 2) ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ (by positivity) hd 2
  have h1 : 1 / (16 * c ^ 4 * d ^ 2) ≤ 1 / (4 * c ^ 6) := by
    apply one_div_le_one_div_of_le (by positivity)
    have : 4 * c ^ 6 = 16 * c ^ 4 * (c / 2) ^ 2 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hsq (by positivity)
  refine h1.trans ?_
  rw [div_mul_div_comm, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

lemma kernel_term_le_one {r d : ℝ} (hr : 0 < r) : r ^ 2 / (d ^ 2 + r ^ 2) ≤ 1 := by
  rw [div_le_one (by positivity)]
  nlinarith [sq_nonneg d]

/-- **Uniform bound for the kernel sum over a separated family.** -/
theorem separated_kernel_sum {ι : Type*} {c : ι → ℝ} {d : ι → ℕ} {s κ : ℝ} (hs : 0 < s) (hκ : 0 < κ) :
    ∃ K : ℝ, ∀ (S : Finset ι), (∀ i ∈ S, 0 < c i) → (∀ i ∈ S, κ * ((d i : ℝ) + 1) ^ 2 ≤ c i ^ 6) →
      (Set.InjOn d S) →
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → s * (|(d i : ℝ) - d j| - 1) ≤ |c i - c j| * (max (c i) (c j)) ^ 2) →
      ∀ t : ℝ, ∑ i ∈ S, (1 / (4 * c i ^ 2)) ^ 2 / ((t - c i) ^ 2 + (1 / (4 * c i ^ 2)) ^ 2) ≤ K := by
  classical
  set Z : ℝ := ∑' k : ℤ, 1 / (k : ℝ) ^ 2 with hZ
  have hZs : Summable (fun k : ℤ => 1 / (k : ℝ) ^ 2) := Real.summable_one_div_int_pow.mpr (by norm_num)
  set W : ℝ := ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2 with hW
  have hWs : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    simpa using this
  have hZ0 : 0 ≤ Z := tsum_nonneg fun k => by positivity
  have hW0 : 0 ≤ W := tsum_nonneg fun k => by positivity
  refine ⟨3 + 16 / s ^ 2 * Z + 1 / (4 * κ) * W, fun S h1 h2 hinj h3 t => ?_⟩
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.sum_empty]
    positivity
  -- the nearest index
  obtain ⟨m, hmS, hmin⟩ := S.exists_min_image (fun i => |t - c i|) hne
  set φ : ι → ℤ := fun i => (d i : ℤ) - d m with hφ
  have hφinj : Set.InjOn φ S := fun a ha b hb h => hinj ha hb (by
    have : (d a : ℤ) = d b := by simpa [hφ] using h
    exact_mod_cast this)
  -- the per-term bound
  have hterm : ∀ i ∈ S, (1 / (4 * c i ^ 2)) ^ 2 / ((t - c i) ^ 2 + (1 / (4 * c i ^ 2)) ^ 2) ≤
      (if i = m then 1 else 0) + (if (φ i) ^ 2 = 1 then 1 else 0) +
        16 / s ^ 2 * (1 / ((φ i : ℤ) : ℝ) ^ 2) + 1 / (4 * κ) * (1 / ((d i : ℝ) + 1) ^ 2) := by
    intro i hi
    have hcn := h1 i hi
    have hr0 : 0 < 1 / (4 * c i ^ 2) := by positivity
    have hn0 : 0 ≤ (if i = m then (1 : ℝ) else 0) := by split_ifs <;> norm_num
    have hn1 : 0 ≤ (if (φ i) ^ 2 = 1 then (1 : ℝ) else 0) := by split_ifs <;> norm_num
    have hnonneg1 : 0 ≤ 16 / s ^ 2 * (1 / ((φ i : ℤ) : ℝ) ^ 2) := by positivity
    have hnonneg2 : 0 ≤ 1 / (4 * κ) * (1 / ((d i : ℝ) + 1) ^ 2) := by positivity
    have hle1 := kernel_term_le_one (d := t - c i) hr0
    by_cases him : i = m
    · subst him
      simp only [ite_true]
      linarith
    · simp only [him, ite_false, zero_add]
      by_cases hone : (φ i) ^ 2 = 1
      · simp only [hone, ite_true]
        linarith
      · simp only [hone, ite_false]
        have hφne : φ i ≠ 0 := fun h0 => him (hφinj hi hmS (by simpa [hφ] using h0))
        have hφ2 : 2 ≤ |(φ i : ℝ)| := by
          have h2' : 1 < |φ i| := by
            rcases lt_trichotomy (|φ i|) 1 with h | h | h
            · have : |φ i| ≤ 0 := by
                have := abs_nonneg (φ i); omega
              exact absurd (abs_nonpos_iff.mp this) hφne
            · exfalso; apply hone
              have : φ i = 1 ∨ φ i = -1 := abs_eq (by norm_num) |>.mp h
              rcases this with h | h <;> simp [h]
            · exact h
          have : (2 : ℤ) ≤ |φ i| := h2'
          exact_mod_cast this
        have hmin' : |t - c m| ≤ |t - c i| := hmin i hi
        have he : |c i - c m| ≤ 2 * |t - c i| := by
          have : c i - c m = (t - c m) - (t - c i) := by ring
          rw [this]
          calc |(t - c m) - (t - c i)| ≤ |t - c m| + |t - c i| := abs_sub _ _
            _ ≤ _ := by linarith
        have hsep := h3 i hi m hmS him
        have hdd : |(d i : ℝ) - d m| = |(φ i : ℝ)| := by simp [hφ]
        rw [hdd] at hsep
        have hsep' : (s / 2) * |(φ i : ℝ)| ≤ |c i - c m| * (max (c i) (c m)) ^ 2 := by
          nlinarith [mul_pos hs (by linarith : (0 : ℝ) < |(φ i : ℝ)|)]
        have hmax : 0 < (max (c i) (c m)) ^ 2 := by positivity
        have hφpos : 0 < |(φ i : ℝ)| := by linarith
        have he0 : 0 < |c i - c m| := by
          by_contra h
          have : |c i - c m| = 0 := le_antisymm (not_lt.mp h) (abs_nonneg _)
          rw [this, zero_mul] at hsep'
          nlinarith [mul_pos (by positivity : 0 < s / 2) hφpos]
        have hd : 0 < |t - c i| := by linarith
        have hk := kernel_term_le hcn (d := |t - c i|) hd
        rw [← sq_abs (t - c i)]
        refine hk.trans ?_
        by_cases hcase : c m ≤ 2 * c i
        · -- case A
          have hmx : max (c i) (c m) ≤ 2 * c i := max_le (by linarith) hcase
          have hmx2 : (max (c i) (c m)) ^ 2 ≤ 4 * c i ^ 2 := by nlinarith [le_max_left (c i) (c m)]
          have hA : (s / 2) * |(φ i : ℝ)| ≤ |c i - c m| * (4 * c i ^ 2) :=
            hsep'.trans (mul_le_mul_of_nonneg_left hmx2 (abs_nonneg _))
          have hd2 : (s / 2) * |(φ i : ℝ)| ≤ 8 * c i ^ 2 * |t - c i| := by nlinarith [sq_nonneg (c i)]
          have hj : ((φ i : ℤ) : ℝ) ^ 2 = |(φ i : ℝ)| ^ 2 := by simp
          rw [hj]
          have hx : 0 < (s / 2) * |(φ i : ℝ)| := by positivity
          have h5 := kernel_caseA hcn hd hx hd2
          have e5 : 4 / ((s / 2) * |(φ i : ℝ)|) ^ 2 = 16 / s ^ 2 * (1 / |(φ i : ℝ)| ^ 2) := by
            field_simp; ring
          rw [e5] at h5
          linarith
        · -- case B
          push Not at hcase
          have hd3 : c i / 2 ≤ |t - c i| := by
            have : c i < |c i - c m| := by
              rw [abs_sub_comm]; rw [abs_of_pos (by linarith)]; linarith
            linarith
          have := kernel_caseB hcn hκ (by positivity : (0 : ℝ) < ((d i : ℝ) + 1) ^ 2) hd3 (h2 i hi)
          linarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have e1 : ∑ i ∈ S, (if i = m then (1 : ℝ) else 0) ≤ 1 := by
    rw [Finset.sum_ite_eq' S m (fun _ => (1 : ℝ))]
    split_ifs
    norm_num
  have e1' : ∑ i ∈ S, (if (φ i) ^ 2 = 1 then (1 : ℝ) else 0) ≤ 2 := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hcard : (S.filter (fun i => (φ i) ^ 2 = 1)).card ≤ ({1, -1} : Finset ℤ).card :=
      Finset.card_le_card_of_injOn φ (fun i hi => by
        have := (Finset.mem_filter.mp hi).2
        have h' : φ i = 1 ∨ φ i = -1 := by
          have : (φ i - 1) * (φ i + 1) = 0 := by linear_combination this
          rcases mul_eq_zero.mp this with h | h
          · left; linarith
          · right; linarith
        simpa using h') (fun a ha b hb h => hφinj (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 h)
    have : ({1, -1} : Finset ℤ).card = 2 := by decide
    exact_mod_cast (hcard.trans this.le)
  have e2 : ∑ i ∈ S, 1 / ((φ i : ℤ) : ℝ) ^ 2 ≤ Z := by
    have : ∑ i ∈ S, 1 / ((φ i : ℤ) : ℝ) ^ 2 = ∑ k ∈ S.image φ, 1 / (k : ℝ) ^ 2 := by
      rw [Finset.sum_image hφinj]
    rw [this]
    exact hZs.sum_le_tsum _ (fun k _ => by positivity)
  have e3 : ∑ i ∈ S, 1 / ((d i : ℝ) + 1) ^ 2 ≤ W := by
    have : ∑ i ∈ S, 1 / ((d i : ℝ) + 1) ^ 2 = ∑ n ∈ S.image d, 1 / ((n : ℝ) + 1) ^ 2 := by
      rw [Finset.sum_image hinj]
    rw [this]
    exact hWs.sum_le_tsum _ (fun k _ => by positivity)
  have hs2 : 0 ≤ 16 / s ^ 2 := by positivity
  have hk4 : 0 ≤ 1 / (4 * κ) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left e2 hs2, mul_le_mul_of_nonneg_left e3 hk4]

/-- info: 'FormalResearch.Hardy.separated_kernel_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Hardy.separated_kernel_sum

end FormalResearch.Hardy
