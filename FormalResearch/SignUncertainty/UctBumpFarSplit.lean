module

public import FormalResearch.SignUncertainty.UctBumpSymbol

/-!
# Splitting a bump profile into a compactly supported part and a tail (F2a, `uct:bump-weighted` far band)

With the smooth cutoff `φ(x) = smoothTransition (x - 1)` (`0` on `x ≤ 1`, `1` on `x ≥ 2`) a `BumpProfile b δ M α β K B` splits as `B = B_n + B_t`,
`B_t = φ B` and `B_n = B - φ B`:

* `B_t` is a `BumpProfile 1 1 M α β K''` (support `[1, ∞)`), with `K''` depending only on `K`;
* `B_n` is a `BumpProfile b δ M α (7/2) K'` supported in `(-∞, 2]` (`B_n = 0` on `x ≥ 2`);
* `x^j B` of a `BumpProfile b δ M α β K` is a `BumpProfile b δ M (α - j) (β - j) K^{(j)}` (`BumpProfile.mulPow`).

Class: proved, no hypotheses.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

/-- The cutoff `φ`: `0` for `x ≤ 1`, `1` for `x ≥ 2`. -/
noncomputable def cutφ (x : ℝ) : ℝ := Real.smoothTransition (x - 1)

lemma contDiff_cutφ : ContDiff ℝ (⊤ : ℕ∞) cutφ :=
  Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)

lemma cutφ_of_le {x : ℝ} (hx : x ≤ 1) : cutφ x = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)

lemma cutφ_of_ge {x : ℝ} (hx : 2 ≤ x) : cutφ x = 1 := Real.smoothTransition.one_of_one_le (by linarith)

lemma cutφ_nonneg (x : ℝ) : 0 ≤ cutφ x := Real.smoothTransition.nonneg _

lemma cutφ_le_one (x : ℝ) : cutφ x ≤ 1 := Real.smoothTransition.le_one _

lemma contDiff_iteratedDeriv_top {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv j f) := by
  rw [iteratedDeriv_eq_iterate]; exact hf.iterate_deriv j

lemma zero_of_zero_left {g : ℝ → ℝ} (hg : Continuous g) {a : ℝ} (h : ∀ x < a, g x = 0) {x : ℝ} (hx : x ≤ a) :
    g x = 0 := by
  have hcl : IsClosed {y : ℝ | g y = 0} := isClosed_eq hg continuous_const
  have hsub : Iio a ⊆ {y : ℝ | g y = 0} := fun y hy => h y hy
  have := closure_minimal hsub hcl
  rw [closure_Iio] at this
  exact this hx

lemma zero_of_zero_right {g : ℝ → ℝ} (hg : Continuous g) {a : ℝ} (h : ∀ x > a, g x = 0) {x : ℝ} (hx : a ≤ x) :
    g x = 0 := by
  have hcl : IsClosed {y : ℝ | g y = 0} := isClosed_eq hg continuous_const
  have hsub : Ioi a ⊆ {y : ℝ | g y = 0} := fun y hy => h y hy
  have := closure_minimal hsub hcl
  rw [closure_Ioi] at this
  exact this hx

lemma iteratedDeriv_eq_zero_of_lt {f : ℝ → ℝ} {a : ℝ} (hs : ∀ x < a, f x = 0) (j : ℕ) {x : ℝ} (hx : x < a) :
    iteratedDeriv j f x = 0 := by
  have hev : f =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds hx] with y hy using hs y hy
  rw [hev.iteratedDeriv_eq]
  cases j with
  | zero => simp
  | succ n => simp

lemma iteratedDeriv_eq_zero_of_gt {f : ℝ → ℝ} {a : ℝ} (hs : ∀ x > a, f x = 0) (j : ℕ) {x : ℝ} (hx : a < x) :
    iteratedDeriv j f x = 0 := by
  have hev : f =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy using hs y hy
  rw [hev.iteratedDeriv_eq]
  cases j with
  | zero => simp
  | succ n => simp

/-- Derivatives of `φ` are bounded, and vanish outside `[1, 2]` for orders `≥ 1`. -/
lemma cutφ_deriv_bound (i : ℕ) : ∃ X : ℝ, 0 ≤ X ∧ ∀ x : ℝ, |iteratedDeriv i cutφ x| ≤ X := by
  have hc : Continuous (iteratedDeriv i cutφ) := (contDiff_iteratedDeriv_top contDiff_cutφ i).continuous
  obtain ⟨R, hR⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := 2)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max R 1, le_max_of_le_right zero_le_one, fun x => ?_⟩
  by_cases hx : x ∈ Icc (1 : ℝ) 2
  · have := hR x hx
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  · rcases i with _ | i
    · have h1 : |iteratedDeriv 0 cutφ x| ≤ 1 := by
        rw [iteratedDeriv_zero, abs_of_nonneg (cutφ_nonneg x)]; exact cutφ_le_one x
      exact h1.trans (le_max_right _ _)
    · have hlt : x < 1 ∨ 2 < x := by
        by_contra hcon
        exact hx ⟨not_lt.mp (fun h1 => hcon (Or.inl h1)), not_lt.mp (fun h2 => hcon (Or.inr h2))⟩
      have h0 : iteratedDeriv (i + 1) cutφ x = 0 := by
        rcases hlt with h | h
        · exact iteratedDeriv_eq_zero_of_lt (a := 1) (fun y hy => cutφ_of_le hy.le) _ h
        · have hev : cutφ =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
            filter_upwards [Ioi_mem_nhds h] with y hy using cutφ_of_ge hy.le
          rw [hev.iteratedDeriv_eq, iteratedDeriv_succ']; simp
      rw [h0, abs_zero]
      exact le_max_of_le_right zero_le_one

lemma iteratedDeriv_cutφ_right (i : ℕ) {x : ℝ} (hx : 2 ≤ x) : iteratedDeriv (i + 1) cutφ x = 0 :=
  zero_of_zero_right (contDiff_iteratedDeriv_top contDiff_cutφ (i + 1)).continuous (a := 2)
    (fun y hy => by
      have hev : cutφ =ᶠ[𝓝 y] fun _ => (1 : ℝ) := by
        filter_upwards [Ioi_mem_nhds hy] with z hz using cutφ_of_ge hz.le
      rw [hev.iteratedDeriv_eq, iteratedDeriv_succ']; simp) hx

/-- The tail part `φ B`. -/
noncomputable def bumpTail (B : ℝ → ℝ) (x : ℝ) : ℝ := cutφ x * B x

/-- The compactly supported part `B - φ B`. -/
noncomputable def bumpNear (B : ℝ → ℝ) (x : ℝ) : ℝ := B x - cutφ x * B x

lemma bumpNear_add_bumpTail (B : ℝ → ℝ) (x : ℝ) : bumpNear B x + bumpTail B x = B x := by
  simp [bumpNear, bumpTail]

lemma contDiff_bumpTail {B : ℝ → ℝ} (hB : ContDiff ℝ (⊤ : ℕ∞) B) : ContDiff ℝ (⊤ : ℕ∞) (bumpTail B) :=
  contDiff_cutφ.mul hB

lemma contDiff_bumpNear {B : ℝ → ℝ} (hB : ContDiff ℝ (⊤ : ℕ∞) B) : ContDiff ℝ (⊤ : ℕ∞) (bumpNear B) :=
  hB.sub (contDiff_cutφ.mul hB)

lemma iteratedDeriv_bumpNear {B : ℝ → ℝ} (hB : ContDiff ℝ (⊤ : ℕ∞) B) (k : ℕ) (x : ℝ) :
    iteratedDeriv k (bumpNear B) x = iteratedDeriv k B x - iteratedDeriv k (bumpTail B) x := by
  have h1 : ContDiffAt ℝ k B x := (hB.of_le (by exact_mod_cast le_top)).contDiffAt
  have h2 : ContDiffAt ℝ k (bumpTail B) x := ((contDiff_bumpTail hB).of_le (by exact_mod_cast le_top)).contDiffAt
  exact iteratedDeriv_fun_sub h1 h2

lemma iteratedDeriv_bumpTail_left {B : ℝ → ℝ} (hB : ContDiff ℝ (⊤ : ℕ∞) B) (k : ℕ) {x : ℝ} (hx : x ≤ 1) :
    iteratedDeriv k (bumpTail B) x = 0 :=
  zero_of_zero_left (contDiff_iteratedDeriv_top (contDiff_bumpTail hB) k).continuous (a := 1)
    (fun y hy => iteratedDeriv_eq_zero_of_lt (a := 1) (fun z hz => by unfold bumpTail; rw [cutφ_of_le hz.le, zero_mul]) k hy) hx

lemma bumpNear_of_ge {B : ℝ → ℝ} {x : ℝ} (hx : 2 ≤ x) : bumpNear B x = 0 := by
  simp [bumpNear, cutφ_of_ge hx]

lemma iteratedDeriv_bumpNear_right {B : ℝ → ℝ} (hB : ContDiff ℝ (⊤ : ℕ∞) B) (k : ℕ) {x : ℝ} (hx : 2 ≤ x) :
    iteratedDeriv k (bumpNear B) x = 0 :=
  zero_of_zero_right (contDiff_iteratedDeriv_top (contDiff_bumpNear hB) k).continuous (a := 2)
    (fun _ hy => iteratedDeriv_eq_zero_of_gt (a := 2) (fun _ hz => bumpNear_of_ge hz.le) k hy) hx

/-- Constant for the Leibniz bound of the tail: `K''_k = ∑_i C(k,i) X_i 2^i |K_{k-i}|`. -/
noncomputable def tailK (K : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (cutφ_deriv_bound i).choose * 2 ^ i * |K (k - i)|

lemma tailK_nonneg (K : ℕ → ℝ) (k : ℕ) : 0 ≤ tailK K k :=
  Finset.sum_nonneg fun i _ => by
    have := (cutφ_deriv_bound i).choose_spec.1
    positivity

namespace BumpProfile

variable {b δ M α β : ℝ} {K : ℕ → ℝ} {B : ℝ → ℝ}

lemma cutφ_deriv_mul_pow (i : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    |iteratedDeriv i cutφ x| * x ^ i ≤ (cutφ_deriv_bound i).choose * 2 ^ i := by
  have hx0 : 0 < x := by linarith
  have hb := (cutφ_deriv_bound i).choose_spec.2 x
  have hX0 := (cutφ_deriv_bound i).choose_spec.1
  rcases i with _ | i
  · simpa using hb
  · rcases lt_or_ge x 2 with h2 | h2
    · exact mul_le_mul hb (pow_le_pow_left₀ hx0.le h2.le _) (by positivity) hX0
    · rw [iteratedDeriv_cutφ_right i h2]; simp; positivity

/-- Far bound for the tail part. -/
lemma tail_far (h : BumpProfile b δ M α β K B) (hM : 0 ≤ M) (k : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    |iteratedDeriv k (bumpTail B) x| ≤ tailK K k * M * x ^ (-β - (k : ℝ)) := by
  have hx0 : 0 < x := by linarith
  have hcd : ContDiff ℝ (⊤ : ℕ∞) B := h.smooth
  have h1 : ContDiffAt ℝ k cutφ x := (contDiff_cutφ.of_le (by exact_mod_cast le_top)).contDiffAt
  have h2 : ContDiffAt ℝ k B x := (hcd.of_le (by exact_mod_cast le_top)).contDiffAt
  have hmul : iteratedDeriv k (bumpTail B) x = ∑ i ∈ Finset.range (k + 1),
      (k.choose i : ℝ) * iteratedDeriv i cutφ x * iteratedDeriv (k - i) B x := iteratedDeriv_fun_mul h1 h2
  rw [hmul, tailK, Finset.sum_mul, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  have hik : i ≤ k := by have := Finset.mem_range.mp hi; omega
  have hX0 := (cutφ_deriv_bound i).choose_spec.1
  have hfar := h.far (k - i) x hx
  have e : x ^ (-β - (((k - i : ℕ)) : ℝ)) = x ^ i * x ^ (-β - (k : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hx0, Nat.cast_sub hik]; congr 1; ring
  have hKM : K (k - i) * M ≤ |K (k - i)| * M := mul_le_mul_of_nonneg_right (le_abs_self _) hM
  have hp : 0 ≤ x ^ (-β - (k : ℝ)) := Real.rpow_nonneg hx0.le _
  rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k.choose i : ℝ))]
  calc (k.choose i : ℝ) * |iteratedDeriv i cutφ x| * |iteratedDeriv (k - i) B x|
      ≤ (k.choose i : ℝ) * |iteratedDeriv i cutφ x| * (|K (k - i)| * M * (x ^ i * x ^ (-β - (k : ℝ)))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine hfar.trans ?_
        rw [e]
        calc K (k - i) * M * (x ^ i * x ^ (-β - (k : ℝ))) ≤ |K (k - i)| * M * (x ^ i * x ^ (-β - (k : ℝ))) :=
              mul_le_mul_of_nonneg_right hKM (by positivity)
          _ = _ := rfl
    _ = (k.choose i : ℝ) * (|iteratedDeriv i cutφ x| * x ^ i) * (|K (k - i)| * M * x ^ (-β - (k : ℝ))) := by ring
    _ ≤ (k.choose i : ℝ) * ((cutφ_deriv_bound i).choose * 2 ^ i) * (|K (k - i)| * M * x ^ (-β - (k : ℝ))) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (cutφ_deriv_mul_pow i hx) (by positivity))
          (by positivity)
    _ = _ := by ring

/-- `K'_k = 4 (|K_k| + K''_k)`: constant of the compactly supported part. -/
noncomputable def nearK (K : ℕ → ℝ) (k : ℕ) : ℝ := 4 * (|K k| + tailK K k)

lemma nearK_nonneg (K : ℕ → ℝ) (k : ℕ) : 0 ≤ nearK K k := by
  have := tailK_nonneg K k
  unfold nearK; positivity

lemma tail_profile (h : BumpProfile b δ M α β K B) (hM : 0 ≤ M) :
    BumpProfile 1 1 M α β (tailK K) (bumpTail B) where
  smooth := contDiff_bumpTail h.smooth
  support x hx := by
    unfold bumpTail
    rw [cutφ_of_le (by linarith), zero_mul]
  near k x hx1 hx2 := by
    have hx : x ≤ 1 := hx2
    rw [iteratedDeriv_bumpTail_left h.smooth k hx, abs_zero]
    have := tailK_nonneg K k
    have hx0 : 0 < x := by linarith
    have := Real.rpow_nonneg hx0.le (-α - (k : ℝ))
    positivity
  far k x hx := h.tail_far hM k hx

lemma near_profile (h : BumpProfile b δ M α β K B) (hb : 0 < b) (hδ : 0 < δ) (hM : 0 ≤ M) (hβ : 3 / 2 ≤ β) :
    BumpProfile b δ M α (7 / 2) (nearK K) (bumpNear B) where
  smooth := contDiff_bumpNear h.smooth
  support x hx := by
    unfold bumpNear
    rw [h.support x hx]; simp
  near k x hx1 hx2 := by
    have hx0 : 0 < x := lt_of_lt_of_le (mul_pos hb hδ) hx1
    rw [iteratedDeriv_bumpNear h.smooth, iteratedDeriv_bumpTail_left h.smooth k hx2, sub_zero]
    refine (h.near k x hx1 hx2).trans ?_
    have hp := Real.rpow_nonneg hx0.le (-α - (k : ℝ))
    have h1 : K k ≤ nearK K k := by
      have := tailK_nonneg K k
      unfold nearK
      nlinarith [le_abs_self (K k), abs_nonneg (K k)]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hM) hp
  far k x hx := by
    have hx0 : 0 < x := by linarith
    have hp := Real.rpow_nonneg hx0.le (-(7 / 2 : ℝ) - (k : ℝ))
    rcases le_or_gt 2 x with h2 | h2
    · rw [iteratedDeriv_bumpNear_right h.smooth k h2, abs_zero]
      have := nearK_nonneg K k
      positivity
    · rw [iteratedDeriv_bumpNear h.smooth]
      refine (abs_sub _ _).trans ?_
      have h1 := h.far k x hx
      have h2' := h.tail_far hM k hx
      have e : x ^ (-β - (k : ℝ)) = x ^ (7 / 2 - β) * x ^ (-(7 / 2 : ℝ) - (k : ℝ)) := by
        rw [← Real.rpow_add hx0]; congr 1; ring
      have hxs : x ^ (7 / 2 - β) ≤ 4 := by
        calc x ^ (7 / 2 - β) ≤ x ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
          _ = x ^ 2 := by rw [Real.rpow_two]
          _ ≤ 2 ^ 2 := pow_le_pow_left₀ hx0.le h2.le 2
          _ = 4 := by norm_num
      have hq : 0 ≤ x ^ (-β - (k : ℝ)) := Real.rpow_nonneg hx0.le _
      have hsum : |iteratedDeriv k B x| + |iteratedDeriv k (bumpTail B) x| ≤
          (|K k| + tailK K k) * M * x ^ (-β - (k : ℝ)) := by
        have hKM : K k * M ≤ |K k| * M := mul_le_mul_of_nonneg_right (le_abs_self _) hM
        nlinarith [mul_le_mul_of_nonneg_right hKM hq]
      refine hsum.trans ?_
      rw [e]
      have hfin : 0 ≤ (|K k| + tailK K k) * M := by have := tailK_nonneg K k; positivity
      calc (|K k| + tailK K k) * M * (x ^ (7 / 2 - β) * x ^ (-(7 / 2 : ℝ) - (k : ℝ)))
          = ((|K k| + tailK K k) * M) * x ^ (7 / 2 - β) * x ^ (-(7 / 2 : ℝ) - (k : ℝ)) := by ring
        _ ≤ ((|K k| + tailK K k) * M) * 4 * x ^ (-(7 / 2 : ℝ) - (k : ℝ)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hxs hfin) hp
        _ = nearK K k * M * x ^ (-(7 / 2 : ℝ) - (k : ℝ)) := by unfold nearK; ring

end BumpProfile

/-- Constant for `x^j B`: `∑_i C(k,i) j^{\underline i} |K_{k-i}|`. -/
noncomputable def mulPowK (K : ℕ → ℝ) (j k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (j.descFactorial i : ℝ) * |K (k - i)|

lemma mulPowK_nonneg (K : ℕ → ℝ) (j k : ℕ) : 0 ≤ mulPowK K j k :=
  Finset.sum_nonneg fun i _ => by positivity

lemma mulPow_bound {B : ℝ → ℝ} (hB : ContDiff ℝ (⊤ : ℕ∞) B) {K : ℕ → ℝ} {M γ x : ℝ} (hM : 0 ≤ M) (hx : 0 < x)
    (j k : ℕ) (hb : ∀ m : ℕ, m ≤ k → |iteratedDeriv m B x| ≤ K m * M * x ^ (-γ - (m : ℝ))) :
    |iteratedDeriv k (fun y : ℝ => y ^ j * B y) x| ≤ mulPowK K j k * M * x ^ (-(γ - j) - (k : ℝ)) := by
  have hpow : ContDiffAt ℝ k (fun y : ℝ => y ^ j) x :=
    ((contDiff_id.pow j).of_le (by exact_mod_cast le_top)).contDiffAt
  have hBc : ContDiffAt ℝ k B x := (hB.of_le (by exact_mod_cast le_top)).contDiffAt
  rw [iteratedDeriv_fun_mul hpow hBc, mulPowK, Finset.sum_mul, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  have hik : i ≤ k := by have := Finset.mem_range.mp hi; omega
  rw [abs_mul, abs_mul, iteratedDeriv_pow]
  rcases le_or_gt i j with hij | hij
  · have hfar := hb (k - i) (by omega)
    have hxp : x ^ (j - i) = x ^ (((j : ℝ) - i)) := by
      rw [← Real.rpow_natCast, Nat.cast_sub hij]
    have e : x ^ (-(γ - j) - (k : ℝ)) = x ^ (((j : ℝ) - i)) * x ^ (-γ - ((k - i : ℕ) : ℝ)) := by
      rw [← Real.rpow_add hx, Nat.cast_sub hik]; congr 1; ring
    rw [e]
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k.choose i : ℝ)),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (j.descFactorial i : ℝ) * x ^ (j - i))]
    calc (k.choose i : ℝ) * ((j.descFactorial i : ℝ) * x ^ (j - i)) * |iteratedDeriv (k - i) B x|
        ≤ (k.choose i : ℝ) * ((j.descFactorial i : ℝ) * x ^ (j - i)) * (K (k - i) * M * x ^ (-γ - ((k - i : ℕ) : ℝ))) := by
          gcongr
      _ ≤ (k.choose i : ℝ) * ((j.descFactorial i : ℝ) * x ^ (j - i)) * (|K (k - i)| * M * x ^ (-γ - ((k - i : ℕ) : ℝ))) := by
          have hKM : K (k - i) * M ≤ |K (k - i)| * M := mul_le_mul_of_nonneg_right (le_abs_self _) hM
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hKM (Real.rpow_nonneg hx.le _)) (by positivity)
      _ = (k.choose i : ℝ) * (j.descFactorial i : ℝ) * |K (k - i)| * M *
            (x ^ (((j : ℝ) - i)) * x ^ (-γ - ((k - i : ℕ) : ℝ))) := by
          rw [hxp]; ring
  · have : j.descFactorial i = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr hij
    rw [this]; simp only [Nat.cast_zero, zero_mul, mul_zero, abs_zero, zero_mul]
    have := Real.rpow_nonneg hx.le (-(γ - j) - (k : ℝ))
    have := mulPowK_nonneg K j k
    positivity

namespace BumpProfile

variable {b δ M α β : ℝ} {K : ℕ → ℝ} {B : ℝ → ℝ}

/-- `x^j B` is again a bump profile, with exponents `α - j`, `β - j`. -/
lemma mulPow (h : BumpProfile b δ M α β K B) (hb : 0 < b) (hδ : 0 < δ) (hM : 0 ≤ M) (j : ℕ) :
    BumpProfile b δ M (α - j) (β - j) (mulPowK K j) (fun y : ℝ => y ^ j * B y) where
  smooth := (contDiff_id.pow j).mul h.smooth
  support x hx := by rw [h.support x hx, mul_zero]
  near k x hx1 hx2 :=
    mulPow_bound h.smooth hM (lt_of_lt_of_le (mul_pos hb hδ) hx1) j k fun m _ => h.near m x hx1 hx2
  far k x hx := mulPow_bound h.smooth hM (by linarith) j k fun m _ => h.far m x hx

end BumpProfile

/-- info: 'FormalResearch.SignUncertainty.BumpProfile.near_profile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BumpProfile.near_profile

/-- info: 'FormalResearch.SignUncertainty.BumpProfile.tail_profile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BumpProfile.tail_profile

/-- info: 'FormalResearch.SignUncertainty.BumpProfile.mulPow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BumpProfile.mulPow

end FormalResearch.SignUncertainty
