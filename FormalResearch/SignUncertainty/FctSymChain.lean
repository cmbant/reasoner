/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctSymCal

/-!
# Closure of the symbol classes `SymW` under composition (calculus for `fct:bump-sym-check`)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma FCT.7b (`fct:bump-sym-check`), the compositions
`exp(v) - 1`, `|1 - L₁ φ_kill/L̃| - 1`, and the change of variable `L ↦ τ₀(L̃)` (`∂_L = m'(t)^{-1} ∂_t`).

`FctSymCal` has sums, products, shifts and powers.  This file adds the **chain rule with explicit constants**
(Faà di Bruno in the form needed for symbols), without any combinatorics of partitions.  The family
`F_j = Φ^{(j)} ∘ f` satisfies `F_j' = a · (F_{j+1} + κ_j F_j)` with `a = f'`, so that the derivative bounds of all orders
follow by induction on the order with Leibniz's rule (`chain_step`).  All constants (`chainM`) are explicit functions
of the data `P` (bounds of `Φ^{(j)}`), `A` (symbol constants of `a`), `κ`, `B`, hence independent of every other parameter.

* `chain_bound`: if `|F_j| ≤ P_j om`, `|a^{(k)}| ≤ A_k w x^{-1-k}`, `w ≤ B`, `F_j' = a (F_{j+1} + κ_j F_j)`, then
  `|F_j^{(i)}| ≤ chainM(i,j) om x^{-i}` and, for `i ≥ 1`, with the extra factor `w`.
* `SymW.comp_smooth`: `Φ ∘ f` for `f ∈ SymW S w K` and `Φ` smooth with bounded derivatives (`exp(f) - 1`, ...).
* `SymW.comp_sqrt`: `g ∘ √` on `(0, L₀]` (the model of `τ₀(L) = ψ(√L)`).

Class: proved, no hypotheses.
-/

@[expose] public section

open Set Finset
open scoped ContDiff

namespace FormalResearch.SignUncertainty.FctSym

/-- The one-step constant: `2^r (∑_{k ≤ r} A_k) (M_{j+1} + |κ_j| M_j)`. -/
noncomputable def chainStep (A κ : ℕ → ℝ) (r : ℕ) (M : ℕ → ℝ) (j : ℕ) : ℝ :=
  2 ^ r * (∑ k ∈ range (r + 1), A k) * (M (j + 1) + |κ j| * M j)

/-- The running constants of the chain-rule recursion: `chainM P κ A B r j` bounds `|F_j^{(i)}| x^i / om` for `i ≤ r`. -/
noncomputable def chainM (P κ A : ℕ → ℝ) (B : ℝ) : ℕ → ℕ → ℝ
  | 0 => P
  | r + 1 => fun j => max (chainM P κ A B r j) (B * chainStep A κ r (chainM P κ A B r) j)

lemma chainStep_nonneg {A κ : ℕ → ℝ} (hA : ∀ k, 0 ≤ A k) {M : ℕ → ℝ} (hM : ∀ j, 0 ≤ M j) (r j : ℕ) :
    0 ≤ chainStep A κ r M j := by
  unfold chainStep
  have : 0 ≤ ∑ k ∈ range (r + 1), A k := sum_nonneg fun k _ => hA k
  have h1 := hM (j + 1)
  have h2 := hM j
  positivity

lemma chainM_nonneg {P κ A : ℕ → ℝ} {B : ℝ} (hP : ∀ j, 0 ≤ P j) (r j : ℕ) :
    0 ≤ chainM P κ A B r j := by
  induction r generalizing j with
  | zero => exact hP j
  | succ r ih =>
    simp only [chainM]
    exact (ih j).trans (le_max_left _ _)

lemma chainM_mono_succ (P κ A : ℕ → ℝ) (B : ℝ) (r j : ℕ) : chainM P κ A B r j ≤ chainM P κ A B (r + 1) j :=
  le_max_left _ _

/-- **One step of the chain-rule recursion** (Leibniz): the `(r+1)`-th derivative of `F_j` carries the weight `w` of `a`. -/
lemma chain_step {S U : Set ℝ} (hU : IsOpen U) (hSU : S ⊆ U) (hpos : ∀ x ∈ S, 0 < x)
    {F : ℕ → ℝ → ℝ} {a w om : ℝ → ℝ} {κ A : ℕ → ℝ} {M : ℕ → ℝ} (r : ℕ)
    (hF : ∀ j, ContDiffOn ℝ ∞ (F j) U) (ha : ContDiffOn ℝ ∞ a U)
    (hderiv : ∀ j, ∀ x ∈ U, deriv (F j) x = a x * (F (j + 1) x + κ j * F j x))
    (haS : ∀ k x, x ∈ S → |iteratedDeriv k a x| ≤ A k * w x * (x ^ (k + 1))⁻¹)
    (hw : ∀ x ∈ S, 0 ≤ w x) (hA : ∀ k, 0 ≤ A k) (hom : ∀ x ∈ S, 0 ≤ om x)
    (hFS : ∀ j, ∀ x ∈ S, ∀ i ≤ r, |iteratedDeriv i (F j) x| ≤ M j * om x * (x ^ i)⁻¹) (hM : ∀ j, 0 ≤ M j)
    (j : ℕ) {x : ℝ} (hx : x ∈ S) :
    |iteratedDeriv (r + 1) (F j) x| ≤ chainStep A κ r M j * om x * w x * (x ^ (r + 1))⁻¹ := by
  have hxU : x ∈ U := hSU hx
  have hxp : 0 < x := hpos x hx
  have hcd : ∀ (n : ℕ) (g : ℝ → ℝ), ContDiffOn ℝ ∞ g U → ContDiffAt ℝ n g x := fun n g hg =>
    (hg.contDiffAt (hU.mem_nhds hxU)).of_le (by exact_mod_cast le_top)
  have hev : deriv (F j) =ᶠ[nhds x] fun y => a y * (F (j + 1) y + κ j * F j y) :=
    Filter.eventually_of_mem (hU.mem_nhds hxU) fun y hy => hderiv j y hy
  rw [iteratedDeriv_succ', hev.iteratedDeriv_eq]
  have hg : ContDiffAt ℝ r (fun y => F (j + 1) y + κ j * F j y) x :=
    (hcd r _ (hF (j + 1))).add (contDiffAt_const.mul (hcd r _ (hF j)))
  rw [iteratedDeriv_fun_mul (hcd r _ ha) hg]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hAbar : ∀ i ∈ range (r + 1), A i ≤ ∑ k ∈ range (r + 1), A k := fun i hi =>
    Finset.single_le_sum (f := A) (fun k _ => hA k) hi
  have hMj := hM j
  have hMj1 := hM (j + 1)
  have homx := hom x hx
  have hwx := hw x hx
  have hxinv : ∀ n : ℕ, 0 ≤ (x ^ n)⁻¹ := fun n => inv_nonneg.mpr (pow_nonneg hxp.le n)
  calc ∑ i ∈ range (r + 1), |(r.choose i : ℝ) * iteratedDeriv i a x *
        iteratedDeriv (r - i) (fun y => F (j + 1) y + κ j * F j y) x|
      ≤ ∑ i ∈ range (r + 1), ((r.choose i : ℝ) * (∑ k ∈ range (r + 1), A k) *
          (M (j + 1) + |κ j| * M j) * om x * w x * (x ^ (r + 1))⁻¹) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hir : i ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have h1 := haS i x hx
        have h2 : |iteratedDeriv (r - i) (fun y => F (j + 1) y + κ j * F j y) x| ≤
            (M (j + 1) + |κ j| * M j) * om x * (x ^ (r - i))⁻¹ := by
          have e : iteratedDeriv (r - i) (fun y => F (j + 1) y + κ j * F j y) x =
              iteratedDeriv (r - i) (F (j + 1)) x + κ j * iteratedDeriv (r - i) (F j) x := by
            rw [iteratedDeriv_fun_add (hcd _ _ (hF (j + 1))) (contDiffAt_const.mul (hcd _ _ (hF j)))]
            rw [iteratedDeriv_const_mul_field]
          rw [e]
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul]
          have b1 := hFS (j + 1) x hx (r - i) (Nat.sub_le r i)
          have b2 := hFS j x hx (r - i) (Nat.sub_le r i)
          calc _ ≤ M (j + 1) * om x * (x ^ (r - i))⁻¹ + |κ j| * (M j * om x * (x ^ (r - i))⁻¹) :=
                add_le_add b1 (mul_le_mul_of_nonneg_left b2 (abs_nonneg _))
            _ = _ := by ring
        have hinv : (x ^ (i + 1))⁻¹ * (x ^ (r - i))⁻¹ = (x ^ (r + 1))⁻¹ := by
          rw [← mul_inv, ← pow_add]; congr 2; omega
        rw [abs_mul, abs_mul, Nat.abs_cast]
        have hprod := mul_le_mul h1 h2 (abs_nonneg _) (by
          have := hA i; have := hxinv (i + 1); positivity)
        have hch : (0 : ℝ) ≤ r.choose i := Nat.cast_nonneg _
        calc (r.choose i : ℝ) * |iteratedDeriv i a x| * |iteratedDeriv (r - i) (fun y => F (j + 1) y + κ j * F j y) x|
            = (r.choose i : ℝ) * (|iteratedDeriv i a x| * |iteratedDeriv (r - i) (fun y => F (j + 1) y + κ j * F j y) x|) := by ring
          _ ≤ (r.choose i : ℝ) * ((A i * w x * (x ^ (i + 1))⁻¹) *
                ((M (j + 1) + |κ j| * M j) * om x * (x ^ (r - i))⁻¹)) := mul_le_mul_of_nonneg_left hprod hch
          _ = (r.choose i : ℝ) * A i * (M (j + 1) + |κ j| * M j) * om x * w x *
                ((x ^ (i + 1))⁻¹ * (x ^ (r - i))⁻¹) := by ring
          _ = (r.choose i : ℝ) * A i * (M (j + 1) + |κ j| * M j) * om x * w x * (x ^ (r + 1))⁻¹ := by rw [hinv]
          _ ≤ _ := by
            have hKM : 0 ≤ M (j + 1) + |κ j| * M j := by positivity
            have := hAbar i hi
            have h3 : (r.choose i : ℝ) * A i ≤ (r.choose i : ℝ) * ∑ k ∈ range (r + 1), A k :=
              mul_le_mul_of_nonneg_left this hch
            have h4 := hxinv (r + 1)
            have h5 : 0 ≤ om x * w x * (x ^ (r + 1))⁻¹ := by positivity
            calc (r.choose i : ℝ) * A i * (M (j + 1) + |κ j| * M j) * om x * w x * (x ^ (r + 1))⁻¹
                = ((r.choose i : ℝ) * A i) * (M (j + 1) + |κ j| * M j) * (om x * w x * (x ^ (r + 1))⁻¹) := by ring
              _ ≤ ((r.choose i : ℝ) * ∑ k ∈ range (r + 1), A k) * (M (j + 1) + |κ j| * M j) *
                    (om x * w x * (x ^ (r + 1))⁻¹) := by gcongr
              _ = _ := by ring
    _ = chainStep A κ r M j * om x * w x * (x ^ (r + 1))⁻¹ := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
        have hsum : ∑ i ∈ range (r + 1), (r.choose i : ℝ) = 2 ^ r := by
          exact_mod_cast Nat.sum_range_choose r
        unfold chainStep
        rw [hsum]

/-- **Chain-rule bounds of all orders** for a family `F_j` with `F_j' = a (F_{j+1} + κ_j F_j)`. -/
theorem chain_bound {S U : Set ℝ} (hU : IsOpen U) (hSU : S ⊆ U) (hpos : ∀ x ∈ S, 0 < x)
    {F : ℕ → ℝ → ℝ} {a w om : ℝ → ℝ} {κ A P : ℕ → ℝ} {B : ℝ}
    (hF : ∀ j, ContDiffOn ℝ ∞ (F j) U) (ha : ContDiffOn ℝ ∞ a U)
    (hderiv : ∀ j, ∀ x ∈ U, deriv (F j) x = a x * (F (j + 1) x + κ j * F j x))
    (haS : ∀ k x, x ∈ S → |iteratedDeriv k a x| ≤ A k * w x * (x ^ (k + 1))⁻¹)
    (hw : ∀ x ∈ S, 0 ≤ w x ∧ w x ≤ B) (hA : ∀ k, 0 ≤ A k) (hP : ∀ j, 0 ≤ P j)
    (hom : ∀ x ∈ S, 0 ≤ om x) (hbase : ∀ j, ∀ x ∈ S, |F j x| ≤ P j * om x) (r : ℕ) :
    ∀ j, ∀ x ∈ S, ∀ i ≤ r, |iteratedDeriv i (F j) x| ≤ chainM P κ A B r j * om x * (x ^ i)⁻¹ := by
  induction r with
  | zero =>
    intro j x hx i hi
    obtain rfl : i = 0 := by omega
    simpa [chainM] using hbase j x hx
  | succ r ih =>
    intro j x hx i hi
    have hxp := hpos x hx
    have hxinv : ∀ n : ℕ, 0 ≤ (x ^ n)⁻¹ := fun n => inv_nonneg.mpr (pow_nonneg hxp.le n)
    have homx := hom x hx
    rcases Nat.lt_or_ge i (r + 1) with hlt | hge
    · have := ih j x hx i (by omega)
      refine this.trans ?_
      have h1 := chainM_mono_succ P κ A B r j
      have h2 : 0 ≤ om x * (x ^ i)⁻¹ := mul_nonneg homx (hxinv i)
      calc chainM P κ A B r j * om x * (x ^ i)⁻¹ = chainM P κ A B r j * (om x * (x ^ i)⁻¹) := by ring
        _ ≤ chainM P κ A B (r + 1) j * (om x * (x ^ i)⁻¹) := mul_le_mul_of_nonneg_right h1 h2
        _ = _ := by ring
    · obtain rfl : i = r + 1 := by omega
      have hM : ∀ j, 0 ≤ chainM P κ A B r j := chainM_nonneg hP r
      have hst := chain_step hU hSU hpos (F := F) (a := a) (w := w) (om := om) (κ := κ) (A := A)
        (M := chainM P κ A B r) r hF ha hderiv haS (fun x hx => (hw x hx).1) hA hom
        (fun j x hx i hi => ih j x hx i hi) hM j hx
      refine hst.trans ?_
      have hstp := chainStep_nonneg (κ := κ) hA hM r j
      have hwB := (hw x hx).2
      have h4 := hxinv (r + 1)
      have h5 : B * chainStep A κ r (chainM P κ A B r) j ≤ chainM P κ A B (r + 1) j := le_max_right _ _
      calc chainStep A κ r (chainM P κ A B r) j * om x * w x * (x ^ (r + 1))⁻¹
          = (chainStep A κ r (chainM P κ A B r) j * w x) * (om x * (x ^ (r + 1))⁻¹) := by ring
        _ ≤ (B * chainStep A κ r (chainM P κ A B r) j) * (om x * (x ^ (r + 1))⁻¹) := by
            have : chainStep A κ r (chainM P κ A B r) j * w x ≤ B * chainStep A κ r (chainM P κ A B r) j := by
              nlinarith
            exact mul_le_mul_of_nonneg_right this (mul_nonneg homx h4)
        _ ≤ chainM P κ A B (r + 1) j * (om x * (x ^ (r + 1))⁻¹) :=
            mul_le_mul_of_nonneg_right h5 (mul_nonneg homx h4)
        _ = _ := by ring

/-- The iterated derivatives of a smooth function on an open set are smooth there. -/
lemma contDiffOn_iteratedDeriv_of_isOpen {f : ℝ → ℝ} {V : Set ℝ} (hV : IsOpen V) (hf : ContDiffOn ℝ ∞ f V) (j : ℕ) :
    ContDiffOn ℝ ∞ (iteratedDeriv j f) V := by
  induction j with
  | zero => simpa using hf
  | succ j ih =>
    have : iteratedDeriv (j + 1) f = deriv (iteratedDeriv j f) := iteratedDeriv_succ
    rw [this]
    exact ih.deriv_of_isOpen hV (by simp)

/-- The constants of `Φ ∘ f`: `L` at order `0` and the chain constants `chainStep` of `a = f'` beyond. -/
noncomputable def compK (L : ℝ) (P A : ℕ → ℝ) (B : ℝ) : ℕ → ℝ
  | 0 => L
  | i + 1 => chainStep A (fun _ => 0) i (chainM P (fun _ => 0) A B i) 0

lemma compK_nonneg {L : ℝ} {P A : ℕ → ℝ} {B : ℝ} (hL : 0 ≤ L) (hP : ∀ j, 0 ≤ P j) (hA : ∀ k, 0 ≤ A k) (r : ℕ) :
    0 ≤ compK L P A B r := by
  cases r with
  | zero => exact hL
  | succ i => exact chainStep_nonneg (κ := fun _ => 0) hA (chainM_nonneg (κ := fun _ => 0) (A := A) (B := B) hP i) i 0

/-- **Composition `Φ ∘ f` of a profile with a smooth function** (Lemma FCT.7b: `exp(v) - 1`, `|1 - L₁φ_kill/L̃| - 1`, ...).
If `f ∈ SymW S w K`, `w ≤ B`, `Φ` is smooth on an open set `V ∋ f(x)` with `|Φ^{(j)}(f x)| ≤ P_j` and `|Φ(f x)| ≤ L w(x)`
(e.g. `Φ(0) = 0` and `f` small), then `Φ ∘ f ∈ SymW S w (compK L P (K ∘ succ) B)`: the constants depend only on
`L, P, K, B`. -/
theorem SymW.comp_smooth {S : Set ℝ} {w : ℝ → ℝ} {K : ℕ → ℝ} {f Φ : ℝ → ℝ} {V : Set ℝ} {P : ℕ → ℝ} {B L : ℝ}
    (hf : SymW S w K f) (hV : IsOpen V) (hΦ : ContDiffOn ℝ ∞ Φ V) (hfV : ∀ x ∈ S, f x ∈ V)
    (hP : ∀ j x, x ∈ S → |iteratedDeriv j Φ (f x)| ≤ P j) (hP0 : ∀ j, 0 ≤ P j)
    (hwB : ∀ x ∈ S, w x ≤ B) (hL : 0 ≤ L) (h0 : ∀ x ∈ S, |Φ (f x)| ≤ L * w x) :
    SymW S w (compK L P (fun k => K (k + 1)) B) (fun x => Φ (f x)) where
  pos := hf.pos
  smooth := by
    obtain ⟨U, hU, hSU, hfU⟩ := hf.smooth
    have hcont : ContinuousOn f U := hfU.continuousOn
    refine ⟨U ∩ f ⁻¹' V, hcont.isOpen_inter_preimage hU hV, fun x hx => ⟨hSU hx, hfV x hx⟩, ?_⟩
    exact hΦ.comp (hfU.mono inter_subset_left) (fun x hx => hx.2)
  K_nonneg := compK_nonneg hL hP0 (fun k => hf.K_nonneg (k + 1))
  w_nonneg := hf.w_nonneg
  bound := fun r x hx => by
    obtain ⟨U, hU, hSU, hfU⟩ := hf.smooth
    have hcont : ContinuousOn f U := hfU.continuousOn
    set U' := U ∩ f ⁻¹' V with hU'
    have hU'o : IsOpen U' := hcont.isOpen_inter_preimage hU hV
    have hSU' : S ⊆ U' := fun x hx => ⟨hSU hx, hfV x hx⟩
    have hxp := hf.pos x hx
    cases r with
    | zero =>
      simp only [iteratedDeriv_zero, compK, pow_zero, inv_one, mul_one]
      exact h0 x hx
    | succ i =>
      have hfU' : ContDiffOn ℝ ∞ f U' := hfU.mono inter_subset_left
      have hF : ∀ j, ContDiffOn ℝ ∞ (fun x => iteratedDeriv j Φ (f x)) U' := fun j =>
        (contDiffOn_iteratedDeriv_of_isOpen hV hΦ j).comp hfU' (fun x hx => hx.2)
      have ha : ContDiffOn ℝ ∞ (deriv f) U' := (hfU'.deriv_of_isOpen hU'o (by simp))
      have hderiv : ∀ j, ∀ x ∈ U', deriv (fun x => iteratedDeriv j Φ (f x)) x =
          deriv f x * (iteratedDeriv (j + 1) Φ (f x) + (fun _ : ℕ => (0 : ℝ)) j * iteratedDeriv j Φ (f x)) := by
        intro j y hy
        have h1 : HasDerivAt f (deriv f y) y :=
          ((hfU.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hy.1)).hasDerivAt
        have h2 : HasDerivAt (iteratedDeriv j Φ) (iteratedDeriv (j + 1) Φ (f y)) (f y) := by
          have hd := ((contDiffOn_iteratedDeriv_of_isOpen hV hΦ j).differentiableOn (by simp)).differentiableAt
            (hV.mem_nhds hy.2)
          rw [iteratedDeriv_succ]; exact hd.hasDerivAt
        have := (h2.comp y h1).deriv
        simp only [Function.comp_def] at this
        rw [this]; ring
      have haS : ∀ k x, x ∈ S → |iteratedDeriv k (deriv f) x| ≤ K (k + 1) * w x * (x ^ (k + 1))⁻¹ := by
        intro k y hy
        rw [← iteratedDeriv_succ']
        exact hf.bound (k + 1) y hy
      have hch := chain_bound (S := S) (U := U') hU'o hSU' hf.pos (F := fun j x => iteratedDeriv j Φ (f x))
        (a := deriv f) (w := w) (om := fun _ => 1) (κ := fun _ => 0) (A := fun k => K (k + 1)) (P := P) (B := B)
        hF ha hderiv haS (fun x hx => ⟨hf.w_nonneg x hx, hwB x hx⟩) (fun k => hf.K_nonneg (k + 1)) hP0
        (fun _ _ => zero_le_one) (fun j x hx => by simpa using hP j x hx) i
      have hst := chain_step (S := S) (U := U') hU'o hSU' hf.pos (F := fun j x => iteratedDeriv j Φ (f x))
        (a := deriv f) (w := w) (om := fun _ => 1) (κ := fun _ => 0) (A := fun k => K (k + 1))
        (M := chainM P (fun _ => 0) (fun k => K (k + 1)) B i) i hF ha hderiv haS (fun x hx => hf.w_nonneg x hx)
        (fun k => hf.K_nonneg (k + 1)) (fun _ _ => zero_le_one)
        (fun j x hx i' hi' => by simpa using hch j x hx i' hi') (chainM_nonneg hP0 i) 0 hx
      simpa [compK, mul_assoc, mul_comm, mul_left_comm] using hst

/-- `x ↦ a x^p` on any `S ⊆ (0, ∞)`: weight `|a| x^p`, constants `∏_{i<r} |p - i|` (no shift, no lower bound on `S`). -/
lemma SymW.rpow_gen {S : Set ℝ} (hS : ∀ x ∈ S, 0 < x) (a p : ℝ) :
    SymW S (fun x => |a| * x ^ p) (fun r => ∏ i ∈ range r, |p - (i : ℝ)|) (fun x => a * x ^ p) where
  pos := hS
  smooth := by
    refine ⟨Ioi 0, isOpen_Ioi, fun x hx => hS x hx, ?_⟩
    refine contDiffOn_const.mul ?_
    intro x hx
    exact (Real.contDiffAt_rpow_const_of_ne (ne_of_gt hx)).contDiffWithinAt
  K_nonneg := fun r => Finset.prod_nonneg fun i _ => abs_nonneg _
  w_nonneg := fun x hx => mul_nonneg (abs_nonneg a) (Real.rpow_nonneg (hS x hx).le _)
  bound := fun r x hx => by
    have hxp := hS x hx
    have e : iteratedDeriv r (fun x => a * x ^ p) x =
        a * ((∏ i ∈ range r, (p - (i : ℝ))) * x ^ (p - (r : ℝ))) := by
      rw [show (fun x => a * x ^ p) = (fun x => a * (fun y : ℝ => (y - 0) ^ p) x) by ext y; simp,
        iteratedDeriv_const_mul_field, iteratedDeriv_rpow_sub p 0 r (by simpa using hxp)]
      simp
    rw [e, abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hxp _), Finset.abs_prod,
      Real.rpow_sub_natCast hxp.ne', div_eq_mul_inv]
    refine le_of_eq ?_
    ring

/-- info: 'FormalResearch.SignUncertainty.FctSym.chain_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms chain_bound

/-- info: 'FormalResearch.SignUncertainty.FctSym.SymW.comp_smooth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SymW.comp_smooth

/-- info: 'FormalResearch.SignUncertainty.FctSym.SymW.rpow_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SymW.rpow_gen

end FormalResearch.SignUncertainty.FctSym
