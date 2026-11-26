/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Two-regime symbol classes with explicit constants (calculus for `fct:bump-sym-check`)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, `(fct:B-sym)` of Lemma FCT.7 (`fct:bump-5`) and Lemma FCT.7b
(`fct:bump-sym-check`).  The paper's class is `|f^{(r)}(L)| ≤ C_r M min(L^{-α-r}, L^{-β-r})` for `L ≥ 3δ_L/2`, with
`C_r` independent of `c`; `FctBump5.BSym` states it for one profile.  The bump `B` of `(fct:B-physical)` is a *sum of products*
of profiles of different `(M, α, β)`, so what is needed is a calculus that keeps the constants explicit:

* `pw M α β x = M x^{-α}` for `x ≤ 1` and `M x^{-β}` for `x > 1` (the two regimes of `BumpProfile`; it equals `M min(x^{-α}, x^{-β})`
  for `α ≤ β`, `pw_eq_min`);
* `SymW S w K f`: `f` is `C^∞` on an open set containing `S ⊆ (0, ∞)` and `|f^{(r)}(x)| ≤ K_r w(x) x^{-r}` on `S`;
* closure: `SymW.add`, `smul`, `mul` (Leibniz, constants `Kmul`), `const`, `of_le` (weaker weight), `rpow_sub`
  (`x ↦ a (x - s)^p`, for `|s| ≤ x₀/2`), and `pw_mul`, `pw_le_pw` (class arithmetic `(α₁,β₁)·(α₂,β₂) = (α₁+α₂, β₁+β₂)`).

All constants are explicit functions of the constants of the factors (`Kmul`, `Kadd`), so uniformity in `c` is visible: it is
uniformity in the parameters of the factors.

Class: proved, no hypotheses.
-/

@[expose] public section

open Set Finset
open scoped ContDiff

namespace FormalResearch.SignUncertainty.FctSym

/-- The two-regime weight `M x^{-α}` (`x ≤ 1`), `M x^{-β}` (`x > 1`). -/
noncomputable def pw (M α β x : ℝ) : ℝ := M * (if x ≤ 1 then x ^ (-α) else x ^ (-β))

lemma pw_eq_min {M α β x : ℝ} (hx : 0 < x) (hαβ : α ≤ β) : pw M α β x = M * min (x ^ (-α)) (x ^ (-β)) := by
  unfold pw
  split_ifs with h
  · congr 1
    exact (min_eq_left (Real.rpow_le_rpow_of_exponent_ge hx h (by linarith))).symm
  · congr 1
    push Not at h
    exact (min_eq_right (Real.rpow_le_rpow_of_exponent_le h.le (by linarith))).symm

lemma pw_zero (M x : ℝ) : pw M 0 0 x = M := by
  unfold pw; split_ifs <;> simp

lemma pw_self (M a x : ℝ) : pw M a a x = M * x ^ (-a) := by
  unfold pw; split_ifs <;> rfl

lemma pw_nonneg {M α β x : ℝ} (hM : 0 ≤ M) (hx : 0 < x) : 0 ≤ pw M α β x := by
  unfold pw
  split_ifs <;> exact mul_nonneg hM (Real.rpow_nonneg hx.le _)

lemma pw_mul (M₁ M₂ α₁ α₂ β₁ β₂ x : ℝ) (hx : 0 < x) :
    pw M₁ α₁ β₁ x * pw M₂ α₂ β₂ x = pw (M₁ * M₂) (α₁ + α₂) (β₁ + β₂) x := by
  unfold pw
  split_ifs
  · rw [neg_add, Real.rpow_add hx]; ring
  · rw [neg_add, Real.rpow_add hx]; ring

lemma pw_le_pw {M M' α α' β β' : ℝ} (hM : M ≤ M') (hM0 : 0 ≤ M) (hα : α ≤ α') (hβ' : β' ≤ β) {x : ℝ} (hx : 0 < x) :
    pw M α β x ≤ pw M' α' β' x := by
  unfold pw
  have h0 : ∀ y : ℝ, 0 ≤ x ^ y := fun y => Real.rpow_nonneg hx.le y
  split_ifs with h
  · exact mul_le_mul hM (Real.rpow_le_rpow_of_exponent_ge hx h (by linarith)) (h0 _) (hM0.trans hM)
  · push Not at h
    exact mul_le_mul hM (Real.rpow_le_rpow_of_exponent_le h.le (by linarith)) (h0 _) (hM0.trans hM)

lemma pw_const_le {M α β x : ℝ} (hM : 0 ≤ M) (hα : α ≤ 0) (hβ : 0 ≤ β) (hx : 0 < x) : pw M α β x ≤ M := by
  unfold pw
  split_ifs with h
  · have : x ^ (-α) ≤ 1 := Real.rpow_le_one hx.le h (by linarith)
    nlinarith
  · push Not at h
    have : x ^ (-β) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h.le (by linarith)
    nlinarith

/-! ### The class `SymW` -/

/-- `f` is `C^∞` on an open set containing `S ⊆ (0, ∞)` and `|f^{(r)}(x)| ≤ K_r w(x) x^{-r}` for `x ∈ S`. -/
structure SymW (S : Set ℝ) (w : ℝ → ℝ) (K : ℕ → ℝ) (f : ℝ → ℝ) : Prop where
  pos : ∀ x ∈ S, 0 < x
  smooth : ∃ U : Set ℝ, IsOpen U ∧ S ⊆ U ∧ ContDiffOn ℝ ∞ f U
  K_nonneg : ∀ r, 0 ≤ K r
  w_nonneg : ∀ x ∈ S, 0 ≤ w x
  bound : ∀ (r : ℕ) (x : ℝ), x ∈ S → |iteratedDeriv r f x| ≤ K r * w x * (x ^ r)⁻¹

namespace SymW

variable {S : Set ℝ} {w w' : ℝ → ℝ} {K K' : ℕ → ℝ} {f g : ℝ → ℝ}

lemma mono_set (h : SymW S w K f) {S' : Set ℝ} (hS : S' ⊆ S) : SymW S' w K f where
  pos := fun x hx => h.pos x (hS hx)
  smooth := by
    obtain ⟨U, hU, hSU, hf⟩ := h.smooth
    exact ⟨U, hU, hS.trans hSU, hf⟩
  K_nonneg := h.K_nonneg
  w_nonneg := fun x hx => h.w_nonneg x (hS hx)
  bound := fun r x hx => h.bound r x (hS hx)

lemma of_le (h : SymW S w K f) (hw : ∀ x ∈ S, w x ≤ w' x) (hK : ∀ r, K r ≤ K' r) : SymW S w' K' f where
  pos := h.pos
  smooth := h.smooth
  K_nonneg := fun r => (h.K_nonneg r).trans (hK r)
  w_nonneg := fun x hx => (h.w_nonneg x hx).trans (hw x hx)
  bound := fun r x hx => by
    have hxp := h.pos x hx
    have hinv : 0 ≤ (x ^ r)⁻¹ := inv_nonneg.mpr (pow_nonneg hxp.le r)
    refine (h.bound r x hx).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul (hK r) (hw x hx) (h.w_nonneg x hx) ((h.K_nonneg r).trans (hK r))) hinv

lemma congr (h : SymW S w K f) {U : Set ℝ} (hU : IsOpen U) (hSU : S ⊆ U) (hfgU : Set.EqOn f g U) : SymW S w K g where
  pos := h.pos
  smooth := by
    obtain ⟨V, hV, hSV, hfV⟩ := h.smooth
    exact ⟨U ∩ V, hU.inter hV, subset_inter hSU hSV,
      (hfV.mono inter_subset_right).congr fun x hx => (hfgU hx.1).symm⟩
  K_nonneg := h.K_nonneg
  w_nonneg := h.w_nonneg
  bound := fun r x hx => by
    have : iteratedDeriv r g x = iteratedDeriv r f x := by
      have hev : f =ᶠ[nhds x] g := Filter.eventually_of_mem (hU.mem_nhds (hSU hx)) hfgU
      exact (hev.iteratedDeriv_eq r).symm
    rw [this]; exact h.bound r x hx

/-- Sum of two profiles with the same weight. -/
lemma add (hf : SymW S w K f) (hg : SymW S w K' g) : SymW S w (fun r => K r + K' r) (fun x => f x + g x) where
  pos := hf.pos
  smooth := by
    obtain ⟨U, hU, hSU, hfU⟩ := hf.smooth
    obtain ⟨V, hV, hSV, hgV⟩ := hg.smooth
    exact ⟨U ∩ V, hU.inter hV, subset_inter hSU hSV, (hfU.mono inter_subset_left).add (hgV.mono inter_subset_right)⟩
  K_nonneg := fun r => add_nonneg (hf.K_nonneg r) (hg.K_nonneg r)
  w_nonneg := hf.w_nonneg
  bound := fun r x hx => by
    obtain ⟨U, hU, hSU, hfU⟩ := hf.smooth
    obtain ⟨V, hV, hSV, hgV⟩ := hg.smooth
    have h1 : ContDiffAt ℝ r f x := (hfU.contDiffAt (hU.mem_nhds (hSU hx))).of_le (by exact_mod_cast le_top)
    have h2 : ContDiffAt ℝ r g x := (hgV.contDiffAt (hV.mem_nhds (hSV hx))).of_le (by exact_mod_cast le_top)
    have : iteratedDeriv r (fun x => f x + g x) x = iteratedDeriv r f x + iteratedDeriv r g x :=
      iteratedDeriv_fun_add h1 h2
    rw [this]
    refine (abs_add_le _ _).trans ?_
    have := add_le_add (hf.bound r x hx) (hg.bound r x hx)
    calc _ ≤ _ := this
      _ = _ := by ring

/-- A constant factor goes into the weight (the constants `K` do not change). -/
lemma smul (a : ℝ) (hf : SymW S w K f) : SymW S (fun x => |a| * w x) K (fun x => a * f x) where
  pos := hf.pos
  smooth := by
    obtain ⟨U, hU, hSU, hfU⟩ := hf.smooth
    exact ⟨U, hU, hSU, hfU.const_smul a⟩
  K_nonneg := hf.K_nonneg
  w_nonneg := fun x hx => mul_nonneg (abs_nonneg a) (hf.w_nonneg x hx)
  bound := fun r x hx => by
    have : iteratedDeriv r (fun x => a * f x) x = a * iteratedDeriv r f x :=
      iteratedDeriv_const_mul_field a f
    rw [this, abs_mul]
    calc |a| * |iteratedDeriv r f x| ≤ |a| * (K r * w x * (x ^ r)⁻¹) :=
          mul_le_mul_of_nonneg_left (hf.bound r x hx) (abs_nonneg a)
      _ = _ := by ring

/-- Leibniz constants. -/
noncomputable def Kmul (K₁ K₂ : ℕ → ℝ) (r : ℕ) : ℝ := ∑ i ∈ range (r + 1), (r.choose i : ℝ) * K₁ i * K₂ (r - i)

lemma Kmul_nonneg (h1 : ∀ r, 0 ≤ K r) (h2 : ∀ r, 0 ≤ K' r) (r : ℕ) : 0 ≤ Kmul K K' r :=
  sum_nonneg fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (h1 i)) (h2 _)

/-- Product of two profiles: weights multiply (Leibniz). -/
lemma mul (hf : SymW S w K f) (hg : SymW S w' K' g) :
    SymW S (fun x => w x * w' x) (Kmul K K') (fun x => f x * g x) where
  pos := hf.pos
  smooth := by
    obtain ⟨U, hU, hSU, hfU⟩ := hf.smooth
    obtain ⟨V, hV, hSV, hgV⟩ := hg.smooth
    exact ⟨U ∩ V, hU.inter hV, subset_inter hSU hSV, (hfU.mono inter_subset_left).mul (hgV.mono inter_subset_right)⟩
  K_nonneg := Kmul_nonneg hf.K_nonneg hg.K_nonneg
  w_nonneg := fun x hx => mul_nonneg (hf.w_nonneg x hx) (hg.w_nonneg x hx)
  bound := fun r x hx => by
    obtain ⟨U, hU, hSU, hfU⟩ := hf.smooth
    obtain ⟨V, hV, hSV, hgV⟩ := hg.smooth
    have h1 : ContDiffAt ℝ r f x := (hfU.contDiffAt (hU.mem_nhds (hSU hx))).of_le (by exact_mod_cast le_top)
    have h2 : ContDiffAt ℝ r g x := (hgV.contDiffAt (hV.mem_nhds (hSV hx))).of_le (by exact_mod_cast le_top)
    rw [iteratedDeriv_fun_mul h1 h2]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    unfold Kmul
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    have hij : i ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [abs_mul, abs_mul, Nat.abs_cast]
    have a1 := hf.bound i x hx
    have a2 := hg.bound (r - i) x hx
    have hmul := mul_le_mul a1 a2 (abs_nonneg _) (le_trans (abs_nonneg _) a1)
    have hinv : (x ^ i)⁻¹ * (x ^ (r - i))⁻¹ = (x ^ r)⁻¹ := by
      rw [← mul_inv, ← pow_add, Nat.add_sub_cancel' hij]
    calc (r.choose i : ℝ) * |iteratedDeriv i f x| * |iteratedDeriv (r - i) g x|
        = (r.choose i : ℝ) * (|iteratedDeriv i f x| * |iteratedDeriv (r - i) g x|) := by ring
      _ ≤ (r.choose i : ℝ) * ((K i * w x * (x ^ i)⁻¹) * (K' (r - i) * w' x * (x ^ (r - i))⁻¹)) :=
          mul_le_mul_of_nonneg_left hmul (Nat.cast_nonneg _)
      _ = (r.choose i : ℝ) * K i * K' (r - i) * (w x * w' x) * ((x ^ i)⁻¹ * (x ^ (r - i))⁻¹) := by ring
      _ = _ := by rw [hinv]

/-- Constants (all derivatives of order `≥ 1` vanish): used with `of_le` to put it in any larger weight. -/
noncomputable def Kone (r : ℕ) : ℝ := if r = 0 then 1 else 0

lemma Kone_nonneg (r : ℕ) : 0 ≤ Kone r := by unfold Kone; split_ifs <;> norm_num

/-- A constant. -/
lemma const (hS : ∀ x ∈ S, 0 < x) (a : ℝ) : SymW S (fun _ => |a|) Kone (fun _ => a) where
  pos := hS
  smooth := ⟨univ, isOpen_univ, subset_univ _, contDiffOn_const⟩
  K_nonneg := Kone_nonneg
  w_nonneg := fun _ _ => abs_nonneg a
  bound := fun r x hx => by
    cases r with
    | zero => simp [Kone]
    | succ n =>
      have : iteratedDeriv (n + 1) (fun _ : ℝ => a) x = 0 := by
        rw [iteratedDeriv_succ']; simp
      rw [this, abs_zero]
      exact mul_nonneg (mul_nonneg (Kone_nonneg _) (abs_nonneg a)) (inv_nonneg.mpr (pow_nonneg (hS x hx).le _))


/-- `x ↦ (x - s)^p` has `r`-th derivative `(∏_{i<r}(p - i)) (x - s)^{p-r}` for `x > s`. -/
lemma iteratedDeriv_rpow_sub (p s : ℝ) (r : ℕ) {x : ℝ} (hx : s < x) :
    iteratedDeriv r (fun y : ℝ => (y - s) ^ p) x = (∏ i ∈ range r, (p - (i : ℝ))) * (x - s) ^ (p - (r : ℝ)) := by
  have key : ∀ (j : ℕ) {y : ℝ}, 0 < y →
      iteratedDeriv j (fun z : ℝ => z ^ p) y = (∏ i ∈ range j, (p - (i : ℝ))) * y ^ (p - (j : ℝ)) := by
    intro j
    induction j with
    | zero => intro y _; simp
    | succ j ih =>
      intro y hy
      rw [iteratedDeriv_succ]
      have hev : iteratedDeriv j (fun z : ℝ => z ^ p) =ᶠ[nhds y]
          fun z : ℝ => (∏ i ∈ range j, (p - (i : ℝ))) * z ^ (p - (j : ℝ)) := by
        filter_upwards [Ioi_mem_nhds hy] with z hz using ih hz
      rw [hev.deriv_eq]
      have hd : HasDerivAt (fun z : ℝ => (∏ i ∈ range j, (p - (i : ℝ))) * z ^ (p - (j : ℝ)))
          ((∏ i ∈ range j, (p - (i : ℝ))) * ((p - (j : ℝ)) * y ^ (p - (j : ℝ) - 1))) y :=
        (Real.hasDerivAt_rpow_const (Or.inl hy.ne')).const_mul _
      rw [hd.deriv, Finset.prod_range_succ]
      push_cast; ring_nf
  rw [iteratedDeriv_comp_sub_const r (fun z : ℝ => z ^ p) s]
  exact key r (sub_pos.mpr hx)

lemma rpow_shift_le {p s x : ℝ} (hs : |s| ≤ x / 2) (hx : 0 < x) : (x - s) ^ p ≤ 2 ^ |p| * x ^ p := by
  have h1 : x / 2 ≤ x - s := by linarith [(abs_le.mp hs).2]
  have h2 : x - s ≤ 2 * x := by linarith [(abs_le.mp hs).1]
  have hxs : 0 < x - s := by linarith
  rcases le_total 0 p with hp | hp
  · calc (x - s) ^ p ≤ (2 * x) ^ p := Real.rpow_le_rpow hxs.le h2 hp
      _ = 2 ^ p * x ^ p := Real.mul_rpow (by norm_num) hx.le
      _ = 2 ^ |p| * x ^ p := by rw [abs_of_nonneg hp]
  · calc (x - s) ^ p ≤ (x / 2) ^ p := Real.rpow_le_rpow_of_nonpos (by linarith) h1 hp
      _ = 2 ^ (-p) * x ^ p := by
          rw [Real.div_rpow hx.le (by norm_num), Real.rpow_neg (by norm_num)]; field_simp
      _ = 2 ^ |p| * x ^ p := by rw [abs_of_nonpos hp]

lemma inv_pow_shift_le {s x : ℝ} (r : ℕ) (hs : |s| ≤ x / 2) (hx : 0 < x) : ((x - s) ^ r)⁻¹ ≤ 2 ^ r * (x ^ r)⁻¹ := by
  have h1 : x / 2 ≤ x - s := by linarith [(abs_le.mp hs).2]
  have h0 : 0 < (x / 2) ^ r := pow_pos (by linarith) r
  calc ((x - s) ^ r)⁻¹ ≤ ((x / 2) ^ r)⁻¹ := inv_anti₀ h0 (pow_le_pow_left₀ (by linarith) h1 r)
    _ = 2 ^ r * (x ^ r)⁻¹ := by rw [div_pow, inv_div, div_eq_mul_inv]

/-- The constants of a shifted power: `∏_{i<r} |p - i| · 2^{|p|} 2^r`. -/
noncomputable def Kpow (p : ℝ) (r : ℕ) : ℝ := (∏ i ∈ range r, |p - (i : ℝ)|) * (2 ^ |p| * 2 ^ r)

lemma Kpow_nonneg (p : ℝ) (r : ℕ) : 0 ≤ Kpow p r := by unfold Kpow; positivity

/-- Shifted power `a (x - s)^p` on `[x₀, ∞)`, `|s| ≤ x₀/2`: a profile with weight `|a| x^p` and constants `Kpow p`
(independent of `a` and `s`). -/
lemma rpow_sub {x₀ : ℝ} (hx₀ : 0 < x₀) (a p s : ℝ) (hs : |s| ≤ x₀ / 2) :
    SymW (Ici x₀) (fun x => |a| * x ^ p) (Kpow p) (fun x => a * (x - s) ^ p) where
  pos := fun x hx => lt_of_lt_of_le hx₀ hx
  smooth := by
    refine ⟨Ioi s, isOpen_Ioi, fun x hx => ?_, ?_⟩
    · have h2 := (abs_le.mp hs).2
      have h3 : x₀ ≤ x := hx
      exact Set.mem_Ioi.mpr (by linarith)
    · refine contDiffOn_const.mul ?_
      intro x hx
      exact ((Real.contDiffAt_rpow_const_of_ne (ne_of_gt (sub_pos.mpr hx))).comp x
        (contDiffAt_id.sub contDiffAt_const)).contDiffWithinAt
  K_nonneg := Kpow_nonneg p
  w_nonneg := fun x hx => mul_nonneg (abs_nonneg a) (Real.rpow_nonneg (lt_of_lt_of_le hx₀ hx).le _)
  bound := fun r x hx => by
    have hxp : 0 < x := lt_of_lt_of_le hx₀ hx
    have hsx : |s| ≤ x / 2 := hs.trans (by have : x₀ ≤ x := hx; linarith)
    have hxs : s < x := by linarith [(abs_le.mp hsx).2]
    have hxs0 : 0 < x - s := sub_pos.mpr hxs
    have e : iteratedDeriv r (fun x => a * (x - s) ^ p) x =
        a * ((∏ i ∈ range r, (p - (i : ℝ))) * (x - s) ^ (p - (r : ℝ))) := by
      rw [show (fun x => a * (x - s) ^ p) = (fun x => a * (fun y : ℝ => (y - s) ^ p) x) from rfl,
        iteratedDeriv_const_mul_field, iteratedDeriv_rpow_sub p s r hxs]
    rw [e, abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hxs0 _), Finset.abs_prod,
      Real.rpow_sub_natCast hxs0.ne', div_eq_mul_inv]
    have h1 := rpow_shift_le (p := p) hsx hxp
    have h2 := inv_pow_shift_le r hsx hxp
    have h3 : 0 ≤ ∏ i ∈ range r, |p - (i : ℝ)| := Finset.prod_nonneg fun i _ => abs_nonneg _
    have h4 : 0 ≤ (x - s) ^ p := Real.rpow_nonneg hxs0.le _
    have h5 : 0 ≤ ((x - s) ^ r)⁻¹ := inv_nonneg.mpr (pow_nonneg hxs0.le r)
    unfold Kpow
    calc |a| * ((∏ i ∈ range r, |p - (i : ℝ)|) * ((x - s) ^ p * ((x - s) ^ r)⁻¹))
        ≤ |a| * ((∏ i ∈ range r, |p - (i : ℝ)|) * ((2 ^ |p| * x ^ p) * (2 ^ r * (x ^ r)⁻¹))) := by
          gcongr
      _ = _ := by ring

/-- `a x^p` (no shift). -/
lemma rpow0 {x₀ : ℝ} (hx₀ : 0 < x₀) (a p : ℝ) :
    SymW (Ici x₀) (fun x => |a| * x ^ p) (Kpow p) (fun x => a * x ^ p) :=
  (rpow_sub hx₀ a p 0 (by simp; positivity)).congr (U := univ) isOpen_univ (subset_univ _)
    (fun x _ => by simp)

/-- A profile controlled on `[x₀, x₂]` and identically zero beyond `x₂` is a profile on `[x₀, ∞)`. -/
lemma extend_zero {x₀ x₂ : ℝ} (hx₀ : 0 < x₀) (h : SymW (Icc x₀ x₂) w K f) (hf0 : ∀ x, x₂ < x → f x = 0)
    (hw : ∀ x, x₂ < x → 0 ≤ w x) : SymW (Ici x₀) w K f where
  pos := fun x hx => lt_of_lt_of_le hx₀ hx
  smooth := by
    obtain ⟨U, hU, hSU, hfU⟩ := h.smooth
    refine ⟨U ∪ Ioi x₂, hU.union isOpen_Ioi, fun x hx => ?_, ?_⟩
    · by_cases hx2 : x ≤ x₂
      · exact Or.inl (hSU ⟨hx, hx2⟩)
      · exact Or.inr (not_le.mp hx2)
    · refine contDiffOn_of_locally_contDiffOn fun x hx => ?_
      rcases hx with hx | hx
      · exact ⟨U, hU, hx, hfU.mono inter_subset_right⟩
      · refine ⟨Ioi x₂, isOpen_Ioi, hx, ?_⟩
        exact (contDiffOn_const (c := (0 : ℝ))).congr fun y hy => hf0 y hy.2
  K_nonneg := h.K_nonneg
  w_nonneg := fun x hx => by
    by_cases hx2 : x ≤ x₂
    · exact h.w_nonneg x ⟨hx, hx2⟩
    · exact hw x (not_le.mp hx2)
  bound := fun r x hx => by
    by_cases hx2 : x ≤ x₂
    · exact h.bound r x ⟨hx, hx2⟩
    · have hgt : x₂ < x := not_le.mp hx2
      have hev : f =ᶠ[nhds x] fun _ => (0 : ℝ) :=
        Filter.eventually_of_mem (Ioi_mem_nhds hgt) fun y hy => hf0 y hy
      rw [hev.iteratedDeriv_eq]
      have hxp : 0 < x := lt_of_lt_of_le hx₀ hx
      have : iteratedDeriv r (fun _ : ℝ => (0 : ℝ)) x = 0 := by
        cases r with
        | zero => simp
        | succ n => rw [iteratedDeriv_succ']; simp
      rw [this, abs_zero]
      exact mul_nonneg (mul_nonneg (h.K_nonneg r) (hw x hgt)) (inv_nonneg.mpr (pow_nonneg hxp.le r))

end SymW

/-! ### Smooth cutoffs -/

/-- A smooth nondecreasing transition `χ`: `0` on `(-∞, 1/2]`, `1` on `[1, ∞)`, values in `[0, 1]`
(`constant_terms_upper.tex`, the cutoff of `fct:bump-5`; monotonicity is not used). -/
structure IsCutoff (χ : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ χ
  zero : ∀ s, s ≤ 1 / 2 → χ s = 0
  one : ∀ s, 1 ≤ s → χ s = 1
  mem : ∀ s, 0 ≤ χ s ∧ χ s ≤ 1

lemma IsCutoff.iteratedDeriv_eq_zero {χ : ℝ → ℝ} (h : IsCutoff χ) {r : ℕ} (hr : 1 ≤ r) {s : ℝ} (hs : 1 < s) :
    iteratedDeriv r χ s = 0 := by
  have hev : χ =ᶠ[nhds s] fun _ => (1 : ℝ) :=
    Filter.eventually_of_mem (Ioi_mem_nhds hs) fun y hy => h.one y (le_of_lt hy)
  rw [hev.iteratedDeriv_eq]
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  rw [iteratedDeriv_succ']; simp

lemma IsCutoff.iteratedDeriv_eq_zero' {χ : ℝ → ℝ} (h : IsCutoff χ) {r : ℕ} (hr : 1 ≤ r) {s : ℝ} (hs : s < 1 / 2) :
    iteratedDeriv r χ s = 0 := by
  have hev : χ =ᶠ[nhds s] fun _ => (0 : ℝ) :=
    Filter.eventually_of_mem (Iio_mem_nhds hs) fun y hy => h.zero y (le_of_lt hy)
  rw [hev.iteratedDeriv_eq]
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  rw [iteratedDeriv_succ']; simp

/-- Every derivative of a smooth cutoff is bounded (compact support of the derivatives). -/
lemma IsCutoff.exists_bound {χ : ℝ → ℝ} (h : IsCutoff χ) : ∃ K : ℕ → ℝ, ∀ (r : ℕ) (s : ℝ), |iteratedDeriv r χ s| ≤ K r := by
  have hcont : ∀ r : ℕ, Continuous (iteratedDeriv r χ) := fun r => by
    rw [iteratedDeriv_eq_iterate]; exact (h.smooth.iterate_deriv r).continuous
  have hb : ∀ r : ℕ, ∃ K : ℝ, ∀ s : ℝ, |iteratedDeriv r χ s| ≤ K := by
    intro r
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · exact ⟨1, fun s => by
        simp only [iteratedDeriv_zero]
        rw [abs_of_nonneg (h.mem s).1]; exact (h.mem s).2⟩
    · obtain ⟨K, hK⟩ := (isCompact_Icc (a := (1 / 2 : ℝ)) (b := 1)).exists_bound_of_continuousOn
        (hcont r).continuousOn
      refine ⟨max K 0, fun s => ?_⟩
      by_cases hs : s ∈ Icc (1 / 2 : ℝ) 1
      · exact (hK s hs).trans (le_max_left _ _)
      · rw [Set.mem_Icc, not_and_or] at hs
        rcases hs with hs | hs
        · rw [h.iteratedDeriv_eq_zero' hr (not_le.mp hs)]; simp
        · rw [h.iteratedDeriv_eq_zero hr (not_le.mp hs)]; simp
  choose K hK using hb
  exact ⟨K, hK⟩

/-- `x ↦ χ(x/λ)` is a profile of weight `1` and order `0` on any `S ⊆ (0, ∞)`: `|∂^r χ(x/λ)| ≤ K_r x^{-r}`
(Lemma FCT.7b (a), first item: the derivative `λ^{-r} χ^{(r)}(x/λ)` is supported in `x ≤ λ`, where `λ^{-r} ≤ x^{-r}`). -/
lemma IsCutoff.symW {χ : ℝ → ℝ} (h : IsCutoff χ) {K : ℕ → ℝ} (hK : ∀ (r : ℕ) (s : ℝ), |iteratedDeriv r χ s| ≤ K r)
    {lam : ℝ} (hl : 0 < lam) {S : Set ℝ} (hS : ∀ x ∈ S, 0 < x) :
    SymW S (fun _ => 1) K (fun x => χ (x / lam)) where
  pos := hS
  smooth := ⟨univ, isOpen_univ, subset_univ _, by
    have : ContDiff ℝ ∞ (fun x : ℝ => χ (lam⁻¹ * x)) := h.smooth.comp (contDiff_const.mul contDiff_id)
    simpa [div_eq_inv_mul] using this.contDiffOn⟩
  K_nonneg := fun r => (abs_nonneg _).trans (hK r 0)
  w_nonneg := fun _ _ => zero_le_one
  bound := fun r x hx => by
    have hxp := hS x hx
    have e : iteratedDeriv r (fun x => χ (x / lam)) x = (lam⁻¹) ^ r * iteratedDeriv r χ (lam⁻¹ * x) := by
      have := congrFun (iteratedDeriv_comp_const_mul (n := r) (f := χ) (h.smooth.of_le (by exact_mod_cast le_top)) lam⁻¹) x
      simpa [div_eq_inv_mul] using this
    rw [e, abs_mul]
    have hK' := hK r (lam⁻¹ * x)
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simpa using hK'
    · by_cases hxl : x ≤ lam
      · have h1 : lam⁻¹ ^ r ≤ (x ^ r)⁻¹ := by
          rw [← inv_pow]
          exact pow_le_pow_left₀ (inv_nonneg.mpr hl.le) (inv_anti₀ hxp hxl) r
        rw [abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hl.le) r)]
        calc lam⁻¹ ^ r * |iteratedDeriv r χ (lam⁻¹ * x)| ≤ (x ^ r)⁻¹ * K r :=
              mul_le_mul h1 hK' (abs_nonneg _) (inv_nonneg.mpr (pow_nonneg hxp.le r))
          _ = K r * 1 * (x ^ r)⁻¹ := by ring
      · have hgt : 1 < lam⁻¹ * x := by
          rw [← div_eq_inv_mul, one_lt_div hl]; exact not_le.mp hxl
        rw [h.iteratedDeriv_eq_zero hr hgt]
        simp only [abs_zero, mul_zero]
        exact mul_nonneg (mul_nonneg ((abs_nonneg _).trans (hK r 0)) zero_le_one) (inv_nonneg.mpr (pow_nonneg hxp.le r))

end FormalResearch.SignUncertainty.FctSym
