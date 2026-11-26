/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctDJetDeriv
public import FormalResearch.SignUncertainty.FctDJetBase
public import FormalResearch.SignUncertainty.FctVDiff

/-!
# The `ℓ`-derivative of `∂_v J` (F2a, `(fct:dJ-jets)`, third line)

`Jvu_eq`: differentiating `∂_v J = a ∂_v V + b Y ∂_Y ∂_v V + c ∂_v V(·,0)` (`Jv_eq`) in a second parameter direction `u`
(product rule along the path `p + t u`).

Class: proved, no hypotheses beyond those stated.
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace FormalResearch.SignUncertainty
section DJetU
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
variable {Ω : Set P} {V : P × ℝ → ℝ} {H : ℝ → ℝ} {T : Set ℝ} {τ2 : ℝ}

/-- **The second derivative `∂_u ∂_v J`**: the product rule applied to the representation `Jv_eq` of `∂_v J`. -/
theorem Jvu_eq (hΩ : IsOpen Ω) (hV : ContDiffOn ℝ 16 V (Ω ×ˢ Yint))
    (hVb : ∀ q ∈ Ω ×ˢ Yint, 9 / 10 ≤ V q ∧ V q ≤ 6 / 5) (hT : IsOpen T) (hH : ContDiffOn ℝ 16 H T)
    (hHT : ∀ q ∈ Ω ×ˢ Yint, τ2 * (q.2 * V q ^ 2) ∈ T) (hJ : ContDiffOn ℝ 15 (Jfun V H τ2) (Ω ×ˢ Yint))
    (hca : ContDiffOn ℝ 15 (Jca V H τ2) (Ω ×ˢ Yint)) (hcb : ContDiffOn ℝ 15 (Jcb V H τ2) (Ω ×ˢ Yint))
    (hcc : ContDiffOn ℝ 15 (Jcc V H τ2) (Ω ×ˢ Yint)) (v u : P) {q : P × ℝ} (hq : q ∈ Ω ×ˢ Yint) :
    fderiv ℝ (fun y => fderiv ℝ (Jfun V H τ2) y (v, 0)) q (u, 0) =
      fderiv ℝ (Jca V H τ2) q (u, 0) * fderiv ℝ V q (v, 0) +
        Jca V H τ2 q * fderiv ℝ (fun y => fderiv ℝ V y (v, 0)) q (u, 0) +
      (fderiv ℝ (Jcb V H τ2) q (u, 0) * (q.2 * fderiv ℝ (fun y => fderiv ℝ V y (v, 0)) q (0, 1)) +
        Jcb V H τ2 q * (q.2 * fderiv ℝ (fun y => fderiv ℝ (fun z => fderiv ℝ V z (v, 0)) y (0, 1)) q (u, 0))) +
      (fderiv ℝ (Jcc V H τ2) q (u, 0) * fderiv ℝ V (q.1, 0) (v, 0) +
        Jcc V H τ2 q * fderiv ℝ (fun y => fderiv ℝ V y (v, 0)) (q.1, 0) (u, 0)) := by
  obtain ⟨p, s⟩ := q
  have hO : IsOpen (Ω ×ˢ Yint) := hΩ.prod isOpen_Ioo
  have hq0 : (p, (0 : ℝ)) ∈ Ω ×ˢ Yint := ⟨hq.1, zero_mem_Yint⟩
  set Ev : P × ℝ → ℝ := fun y => fderiv ℝ V y (v, 0) with hEv
  have hEc15 : ContDiffOn ℝ 15 Ev (Ω ×ˢ Yint) := by
    have := ((hV.fderiv_of_isOpen hO (m := 15) (by norm_num)).clm_apply (contDiffOn_const (c := (v, (0 : ℝ)))))
    simpa using this
  have hEsc : ContDiffOn ℝ 14 (fun y => fderiv ℝ Ev y (0, 1)) (Ω ×ˢ Yint) := by
    have := ((hEc15.fderiv_of_isOpen hO (m := 14) (by norm_num)).clm_apply (contDiffOn_const (c := ((0 : P), (1 : ℝ)))))
    simpa using this
  have hdiff : ∀ {f : P × ℝ → ℝ} {k : ℕ}, 1 ≤ k → ContDiffOn ℝ k f (Ω ×ˢ Yint) → ∀ y ∈ Ω ×ˢ Yint,
      DifferentiableAt ℝ f y := fun {f k} hk hf y hy =>
    (hf.contDiffAt (hO.mem_nhds hy)).differentiableAt (by exact_mod_cast Nat.one_le_iff_ne_zero.mp hk)
  have hRHS : (fun y => fderiv ℝ (Jfun V H τ2) y (v, 0)) =ᶠ[𝓝 (p, s)]
      fun y => Jca V H τ2 y * Ev y + Jcb V H τ2 y * (y.2 * fderiv ℝ Ev y (0, 1)) + Jcc V H τ2 y * Ev (y.1, 0) := by
    filter_upwards [hO.mem_nhds hq] with y hy
    exact Jv_eq hΩ hV hVb hT hH hHT hJ v hy
  rw [hRHS.fderiv_eq]
  have hRd : DifferentiableAt ℝ (fun y : P × ℝ => Jca V H τ2 y * Ev y + Jcb V H τ2 y * (y.2 * fderiv ℝ Ev y (0, 1)) +
      Jcc V H τ2 y * Ev (y.1, 0)) (p, s) := by
    have h1 := hdiff (by norm_num) hca _ hq
    have h2 := hdiff (by norm_num) hcb _ hq
    have h3 := hdiff (by norm_num) hcc _ hq
    have h4 := hdiff (by norm_num) hEc15 _ hq
    have h5 := hdiff (by norm_num) hEsc _ hq
    have h6 : DifferentiableAt ℝ (fun y : P × ℝ => Ev (y.1, 0)) (p, s) := by
      have := (hdiff (by norm_num) hEc15 _ hq0).comp (p, s) (g := Ev) (f := fun y : P × ℝ => (y.1, (0 : ℝ)))
        (by fun_prop)
      exact this
    exact ((h1.mul h4).add (h2.mul ((differentiableAt_snd).mul h5))).add (h3.mul h6)
  have ha := hasDerivAt_path_dir (p := p) (Y := s) u (hdiff (by norm_num) hca _ hq)
  have hb := hasDerivAt_path_dir (p := p) (Y := s) u (hdiff (by norm_num) hcb _ hq)
  have hc := hasDerivAt_path_dir (p := p) (Y := s) u (hdiff (by norm_num) hcc _ hq)
  have hE1 := hasDerivAt_path_dir (p := p) (Y := s) u (hdiff (by norm_num) hEc15 _ hq)
  have hE2 := hasDerivAt_path_dir (p := p) (Y := s) u (hdiff (by norm_num) hEsc _ hq)
  have hE3 := hasDerivAt_path_dir (p := p) (Y := (0 : ℝ)) u (hdiff (by norm_num) hEc15 _ hq0)
  have hR' := hasDerivAt_path_dir (p := p) (Y := s) u hRd
  have hD := (((ha.mul hE1).add (hb.mul (hE2.const_mul s))).add (hc.mul hE3))
  have hD' : HasDerivAt (fun t : ℝ => (fun y : P × ℝ => Jca V H τ2 y * Ev y + Jcb V H τ2 y * (y.2 * fderiv ℝ Ev y (0, 1)) +
      Jcc V H τ2 y * Ev (y.1, 0)) (p + t • u, s)) _ 0 := hD
  have hEq := hR'.unique hD'
  simp only [zero_smul, add_zero] at hEq
  rw [hEq]

/-- The constant of `Jvu_jets`. -/
noncomputable def CJu (n : ℕ) (β : ℝ) : ℝ :=
  ((n + 1) * 2 ^ n * ((Nat.factorial 15 : ℝ) * Φb^[9] β)) *
    (4 ^ 8 * (2 + (n + 1) * 2 ^ n * 4 ^ 4) * ((n + 2) * 2 ^ (n + 1) * 1000000 * ((Nat.factorial 15 : ℝ) * Φb^[8] β)) +
      4 ^ 3 * (2 + (n + 1) * 2 ^ n * 4 ^ 3) *
        ((n + 2) * 2 ^ (n + 1) * 10000000 * ((Nat.factorial 14 : ℝ) * Φb^[9] β)))

lemma CJu_nonneg (n : ℕ) {β : ℝ} (hβ : 0 ≤ β) : 0 ≤ CJu n β := by
  have h8 : 0 ≤ Φb^[8] β := Φb_iter_nonneg hβ 8
  have h9 : 0 ≤ Φb^[9] β := Φb_iter_nonneg hβ 9
  unfold CJu; positivity

lemma pow_four_weight {W : ℝ} (h0 : 0 ≤ W) (h4 : W ≤ 4) {m : ℕ} (hm : 3 - m ≤ 4 - m) :
    W ^ (4 - m) ≤ 4 ^ 4 * W ^ (3 - m) :=
  (pow_le_four_pow_mul h0 h4 hm).trans (by
    gcongr
    · norm_num
    · omega)

/-- **Weighted jets of `∂_u ∂_v J`** (the `ℓ`-derivative line of `(fct:dJ-jets)`, one parameter direction `u`, `‖u‖ ≤ 1`):
`|∂_Y^n ∂_u ∂_v J| ≤ C |e| max(Y, A)^{max(0,3-n)}`, `n ≤ 13`. -/
theorem Jvu_jets {Ω : Set P} (hΩ : IsOpen Ω) {β : ℝ} (hβ : 8 ≤ β) {V θ : P × ℝ → ℝ} {A : P → ℝ} {H : ℝ → ℝ}
    {T : Set ℝ} {τ2 : ℝ} (v u : P) (hu : ‖u‖ ≤ 1) (e : ℝ)
    (hV : JCΦ 16 (Ω ×ˢ Yint) V β 0) (hA : JCΦ 16 Ω A β 0) (hθ : JCΦ 16 (Ω ×ˢ Ioo (-1 : ℝ) 6) θ β 0)
    (hAY : ∀ p ∈ Ω, A p ∈ Yint) (hz : ∀ q ∈ Ω ×ˢ Yint, q.2 * V q ^ 2 ∈ Ioo (-1 : ℝ) 6)
    (hode : ∀ q ∈ Ω ×ˢ Yint, (A q.1 - q.2) * fderiv ℝ V q (v, 0) =
      e * (V q + 2 * q.2 * fderiv ℝ V q (0, 1)) *
        (A q.1 ^ 5 * V (q.1, A q.1) ^ 11 * θ (q.1, A q.1 * V (q.1, A q.1) ^ 2) -
          q.2 ^ 5 * V q ^ 11 * θ (q.1, q.2 * V q ^ 2)))
    (hVb : ∀ q ∈ Ω ×ˢ Yint, 9 / 10 ≤ V q ∧ V q ≤ 6 / 5) (hT : IsOpen T) (hH : JCΦ 16 T H β 0) (hτ : |τ2| ≤ 1)
    (hHT : ∀ q ∈ Ω ×ˢ Yint, τ2 * (q.2 * V q ^ 2) ∈ T)
    {p : P} (hp : p ∈ Ω) {Y : ℝ} (hY : Y ∈ Yint) (hY0 : 0 ≤ Y) (hA0 : 0 ≤ A p) {n : ℕ} (hn : n ≤ 13) :
    |iteratedDeriv n (fun s : ℝ => fderiv ℝ (fun y => fderiv ℝ (Jfun V H τ2) y (v, 0)) (p, s) (u, 0)) Y| ≤
      |e| * CJu n β * max Y (A p) ^ (3 - n) := by
  have hβ0 : 0 ≤ β := by linarith
  have hO : IsOpen (Ω ×ˢ Yint) := hΩ.prod isOpen_Ioo
  have hOd : UniqueDiffOn ℝ (Ω ×ˢ Yint) := hO.uniqueDiffOn
  obtain ⟨hca, hcb, hcc, hJc⟩ := J_coef_jc hΩ hβ hV hVb hT hH hτ hHT
  have hpY : (p, Y) ∈ Ω ×ˢ Yint := ⟨hp, hY⟩
  have hb9 : 0 ≤ Φb^[9] β := Φb_iter_nonneg hβ0 9
  have hΦ8 : 0 ≤ Φb^[8] β := Φb_iter_nonneg hβ0 8
  set BJ : ℝ := (Nat.factorial 15 : ℝ) * Φb^[9] β with hBJ
  have hBJ0 : 0 ≤ BJ := by rw [hBJ]; positivity
  have hun : ‖((u : P), (0 : ℝ))‖ ≤ 1 := by simpa [Prod.norm_def] using hu
  -- jets of `a, b, c` and of `∂_u a, ∂_u b, ∂_u c`
  have hcoef : ∀ (f : P × ℝ → ℝ), JCΦ 15 (Ω ×ˢ Yint) f β 9 →
      (ContDiffAt ℝ 15 (fun s : ℝ => f (p, s)) Y ∧ ∀ j ≤ 15, |iteratedDeriv j (fun s : ℝ => f (p, s)) Y| ≤ BJ) ∧
      (ContDiffAt ℝ 14 (fun s : ℝ => fderiv ℝ f (p, s) (u, 0)) Y ∧
        ∀ j ≤ 14, |iteratedDeriv j (fun s : ℝ => fderiv ℝ f (p, s) (u, 0)) Y| ≤ BJ) := by
    intro f hf
    obtain ⟨hd, hbd⟩ := dY_bound hO hb9 (hf : JC 15 _ _ _) hpY
    have hfu : JC 14 (Ω ×ˢ Yint) (fun y => fderiv ℝ f y (u, 0)) (‖((u : P), (0 : ℝ))‖ * Φb^[9] β) :=
      ((hf : JC 15 _ _ _).succ_fderiv hO).clm_apply_const hOd (u, 0)
    obtain ⟨hdu, hbdu⟩ := dY_bound hO (mul_nonneg (norm_nonneg _) hb9) hfu hpY
    refine ⟨⟨hd, fun j hj => (hbd j hj).trans ?_⟩, ⟨hdu, fun j hj => (hbdu j hj).trans ?_⟩⟩
    · rw [hBJ]
    · rw [hBJ]
      have h14 : (Nat.factorial 14 : ℝ) ≤ Nat.factorial 15 := by exact_mod_cast Nat.factorial_le (by norm_num)
      calc (Nat.factorial 14 : ℝ) * (‖((u : P), (0 : ℝ))‖ * Φb^[9] β) ≤ (Nat.factorial 15 : ℝ) * (1 * Φb^[9] β) := by
            gcongr
        _ = _ := by ring
  obtain ⟨⟨hda, hba⟩, ⟨hdau, hbau⟩⟩ := hcoef _ hca
  obtain ⟨⟨hdb, hbb⟩, ⟨hdbu, hbbu⟩⟩ := hcoef _ hcb
  obtain ⟨⟨hdc, hbc⟩, ⟨hdcu, hbcu⟩⟩ := hcoef _ hcc
  set W : ℝ := max Y (A p) with hW
  have hW0 : 0 ≤ W := le_max_of_le_left hY0
  have hYW : Y ≤ W := le_max_left _ _
  have hAW : A p ≤ W := le_max_right _ _
  have hY4 : Y ≤ 4 := by have := hY.2; linarith
  have hA4 : A p ≤ 4 := by have := (hAY p hp).2; linarith
  have hW4 : W ≤ 4 := max_le hY4 hA4
  set Ev : P × ℝ → ℝ := fun y => fderiv ℝ V y (v, 0) with hEv
  set E : ℝ → ℝ := fun s => Ev (p, s) with hE
  set Fu : ℝ → ℝ := fun s => fderiv ℝ Ev (p, s) (u, 0) with hFu
  set MMc : ℝ := (n + 2) * 2 ^ (n + 1) * 1000000 * ((Nat.factorial 15 : ℝ) * Φb^[8] β) with hMMc
  set MMu : ℝ := (n + 2) * 2 ^ (n + 1) * 10000000 * ((Nat.factorial 14 : ℝ) * Φb^[9] β) with hMMu
  have hMMc0 : 0 ≤ MMc := by rw [hMMc]; positivity
  have hMMu0 : 0 ≤ MMu := by rw [hMMu]; positivity
  have hcc' : ∀ k : ℕ, k ≤ n + 1 → ((k : ℝ) + 1) * 2 ^ k ≤ ((n : ℝ) + 2) * 2 ^ (n + 1) := by
    intro k hk
    have h1 : (k : ℝ) + 1 ≤ n + 2 := by exact_mod_cast (by omega : k + 1 ≤ n + 2)
    have h2 : (2 : ℝ) ^ k ≤ 2 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) hk
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  have hEj : ∀ (y : ℝ) (k : ℕ), y ∈ Yint → 0 ≤ y → k ≤ n + 1 →
      |iteratedDeriv k E y| ≤ |e| * MMc * max y (A p) ^ (4 - k) := by
    intro y k hy hy0 hk
    have h := E_jets hΩ (by linarith : 4 ≤ β) v e hV hA hθ hAY hz hode hp hy hy0 hA0 (n := k) (by omega)
    refine h.trans ?_
    have hWk : 0 ≤ max y (A p) ^ (4 - k) := by positivity
    have : 0 ≤ (Nat.factorial 15 : ℝ) * Φb^[8] β := by positivity
    calc |e| * (((k : ℝ) + 1) * 2 ^ k * 1000000 * ((Nat.factorial 15 : ℝ) * Φb^[8] β) * max y (A p) ^ (4 - k))
        ≤ |e| * (((n : ℝ) + 2) * 2 ^ (n + 1) * 1000000 * ((Nat.factorial 15 : ℝ) * Φb^[8] β) * max y (A p) ^ (4 - k)) := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          have hnn : 0 ≤ 1000000 * ((Nat.factorial 15 : ℝ) * Φb^[8] β) * max y (A p) ^ (4 - k) := by positivity
          have := mul_le_mul_of_nonneg_right (hcc' k hk) hnn
          linarith
      _ = _ := by rw [hMMc]; ring
  have hFj : ∀ (y : ℝ) (k : ℕ), y ∈ Yint → 0 ≤ y → k ≤ n + 1 →
      |iteratedDeriv k Fu y| ≤ |e| * MMu * max y (A p) ^ (3 - k) := by
    intro y k hy hy0 hk
    have h := E_jets_u hΩ (by linarith : 4 ≤ β) v u hu e hV hA hθ hAY hz hode hp hy hy0 hA0 (n := k) (by omega)
    refine h.trans ?_
    have hWk : 0 ≤ max y (A p) ^ (3 - k) := by positivity
    have : 0 ≤ (Nat.factorial 14 : ℝ) * Φb^[9] β := by positivity
    calc |e| * (((k : ℝ) + 1) * 2 ^ k * 10000000 * ((Nat.factorial 14 : ℝ) * Φb^[9] β) * max y (A p) ^ (3 - k))
        ≤ |e| * (((n : ℝ) + 2) * 2 ^ (n + 1) * 10000000 * ((Nat.factorial 14 : ℝ) * Φb^[9] β) * max y (A p) ^ (3 - k)) := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          have hnn : 0 ≤ 10000000 * ((Nat.factorial 14 : ℝ) * Φb^[9] β) * max y (A p) ^ (3 - k) := by positivity
          have := mul_le_mul_of_nonneg_right (hcc' k hk) hnn
          linarith
      _ = _ := by rw [hMMu]; ring
  have hS : IsOpen {s : ℝ | (p, s) ∈ Ω ×ˢ Yint} := hO.preimage (Continuous.prodMk_right p)
  have hYS : Y ∈ {s : ℝ | (p, s) ∈ Ω ×ˢ Yint} := hpY
  have hEc15 : ContDiffOn ℝ 15 Ev (Ω ×ˢ Yint) := by
    have := ((hV.1.fderiv_of_isOpen hO (m := 15) (by norm_num)).clm_apply (contDiffOn_const (c := (v, (0 : ℝ)))))
    simpa using this
  have hEc14 : ContDiffOn ℝ 14 (fun y => fderiv ℝ Ev y (u, 0)) (Ω ×ˢ Yint) := by
    have := ((hEc15.fderiv_of_isOpen hO (m := 14) (by norm_num)).clm_apply (contDiffOn_const (c := (u, (0 : ℝ)))))
    simpa using this
  have hE15 : ContDiffOn ℝ 15 E {s : ℝ | (p, s) ∈ Ω ×ˢ Yint} :=
    hEc15.comp (contDiffOn_const.prodMk contDiffOn_id) (fun s hs => hs)
  have hF14 : ContDiffOn ℝ 14 Fu {s : ℝ | (p, s) ∈ Ω ×ˢ Yint} :=
    hEc14.comp (contDiffOn_const.prodMk contDiffOn_id) (fun s hs => hs)
  have hE'14 : ContDiffOn ℝ 14 (deriv E) {s : ℝ | (p, s) ∈ Ω ×ˢ Yint} := hE15.deriv_of_isOpen hS (by norm_num)
  have hF'13 : ContDiffOn ℝ 13 (deriv Fu) {s : ℝ | (p, s) ∈ Ω ×ˢ Yint} := hF14.deriv_of_isOpen hS (by norm_num)
  have hEn : ContDiffAt ℝ (n : WithTop ℕ∞) E Y :=
    (hE15.contDiffAt (hS.mem_nhds hYS)).of_le (by exact_mod_cast (by omega : n ≤ 15))
  have hFn : ContDiffAt ℝ (n : WithTop ℕ∞) Fu Y :=
    (hF14.contDiffAt (hS.mem_nhds hYS)).of_le (by exact_mod_cast (by omega : n ≤ 14))
  have hE'n : ContDiffAt ℝ (n : WithTop ℕ∞) (deriv E) Y :=
    (hE'14.contDiffAt (hS.mem_nhds hYS)).of_le (by exact_mod_cast (by omega : n ≤ 14))
  have hF'n : ContDiffAt ℝ (n : WithTop ℕ∞) (deriv Fu) Y :=
    (hF'13.contDiffAt (hS.mem_nhds hYS)).of_le (by exact_mod_cast hn)
  have hh1 : ContDiffAt ℝ (n : WithTop ℕ∞) (fun s : ℝ => s * deriv E s) Y := contDiffAt_id.mul hE'n
  have hh2 : ContDiffAt ℝ (n : WithTop ℕ∞) (fun s : ℝ => s * deriv Fu s) Y := contDiffAt_id.mul hF'n
  set af : ℝ → ℝ := fun s => Jca V H τ2 (p, s) with haf
  set bf : ℝ → ℝ := fun s => Jcb V H τ2 (p, s) with hbf
  set cf : ℝ → ℝ := fun s => Jcc V H τ2 (p, s) with hcf
  set auf : ℝ → ℝ := fun s => fderiv ℝ (Jca V H τ2) (p, s) (u, 0) with hauf
  set buf : ℝ → ℝ := fun s => fderiv ℝ (Jcb V H τ2) (p, s) (u, 0) with hbuf
  set cuf : ℝ → ℝ := fun s => fderiv ℝ (Jcc V H τ2) (p, s) (u, 0) with hcuf
  set K : ℝ := E 0 with hK
  set Ku : ℝ := Fu 0 with hKu
  have hrep : (fun s : ℝ => fderiv ℝ (fun y => fderiv ℝ (Jfun V H τ2) y (v, 0)) (p, s) (u, 0)) =ᶠ[𝓝 Y]
      fun s => auf s * E s + af s * Fu s + (buf s * (s * deriv E s) + bf s * (s * deriv Fu s)) +
        (cuf s * K + cf s * Ku) := by
    filter_upwards [hS.mem_nhds hYS] with s hs
    have h := Jvu_eq hΩ hV.1 hVb hT hH.1 hHT hJc.1 hca.1 hcb.1 hcc.1 v u hs
    have hEs : ContDiffAt ℝ 2 Ev (p, s) :=
      ((hEc15.contDiffAt (hO.mem_nhds hs)).of_le (by norm_num))
    have hd1 : deriv E s = fderiv ℝ Ev (p, s) (0, 1) :=
      deriv_snd_eq ((hEc15.contDiffAt (hO.mem_nhds hs)).differentiableAt (by norm_num))
    have hd2 : deriv Fu s = fderiv ℝ (fun y => fderiv ℝ Ev y (u, 0)) (p, s) (0, 1) :=
      deriv_snd_eq ((hEc14.contDiffAt (hO.mem_nhds hs)).differentiableAt (by norm_num))
    have hsy : fderiv ℝ (fun y => fderiv ℝ Ev y (0, 1)) (p, s) (u, 0) =
        fderiv ℝ (fun y => fderiv ℝ Ev y (u, 0)) (p, s) (0, 1) := fderiv_symm_vec hEs (0, 1) (u, 0)
    rw [h, hd1, hd2, ← hsy]
  rw [hrep.iteratedDeriv_eq n]
  have hbd : ∀ (g : ℝ → ℝ), (∀ j ≤ 14, |iteratedDeriv j g Y| ≤ BJ) → ∀ k ≤ n, |iteratedDeriv k g Y| ≤ BJ * W ^ (0 - k) := by
    intro g hg k hk
    simpa using hg k (by omega)
  have hbfa := hbd af (fun j hj => hba j (by omega))
  have hbfb := hbd bf (fun j hj => hbb j (by omega))
  have hbfc := hbd cf (fun j hj => hbc j (by omega))
  have hbfau := hbd auf hbau
  have hbfbu := hbd buf hbbu
  have hbfcu := hbd cuf hbcu
  have hM0 : 0 ≤ |e| * MMc := by positivity
  have hMu0 : 0 ≤ |e| * MMu := by positivity
  have hgE : ∀ k ≤ n, |iteratedDeriv k E Y| ≤ |e| * MMc * W ^ (4 - k) := fun k hk => hEj Y k hY hY0 (by omega)
  have hgF : ∀ k ≤ n, |iteratedDeriv k Fu Y| ≤ |e| * MMu * W ^ (3 - k) := fun k hk => hFj Y k hY hY0 (by omega)
  have hcn : ∀ f : ℝ → ℝ, ContDiffAt ℝ 14 f Y → ContDiffAt ℝ (n : WithTop ℕ∞) f Y := fun f hf =>
    hf.of_le (by exact_mod_cast (by omega : n ≤ 14))
  have hcn' : ∀ f : ℝ → ℝ, ContDiffAt ℝ 15 f Y → ContDiffAt ℝ (n : WithTop ℕ∞) f Y := fun f hf =>
    hf.of_le (by exact_mod_cast (by omega : n ≤ 15))
  have hpn : ((n : ℝ) + 1) * 2 ^ n * 4 ^ 4 * BJ ≥ 0 := by positivity
  have hW4' := pow_four_weight (m := n) hW0 hW4 (by omega)
  have hW3' := pow_four_weight (m := n) hW0 hW4 (by omega)
  -- T1, T2
  have hT1 := weighted_leibniz (n := n) (u := 0) (w := 4) (f := auf) (g := E) hY0 hY4 hA4 (hcn _ hdau) hEn hBJ0 hM0 hbfau hgE
  have hT2 := weighted_leibniz (n := n) (u := 0) (w := 3) (f := af) (g := Fu) hY0 hY4 hA4 (hcn' _ hda) hFn hBJ0 hMu0 hbfa hgF
  -- T3: `s * E'`
  have hh1b : ∀ m ≤ n, |iteratedDeriv m (fun s : ℝ => s * deriv E s) Y| ≤
      ((n + 1) * 2 ^ n * 4 ^ 4 * (|e| * MMc)) * W ^ (4 - m) := by
    intro m hm
    have hgd : ∀ k ≤ m, |iteratedDeriv k (deriv E) Y| ≤ |e| * MMc * W ^ (3 - k) := by
      intro k hk
      rw [← iteratedDeriv_succ']
      have := hEj Y (k + 1) hY hY0 (by omega)
      rwa [show 4 - (k + 1) = 3 - k by omega] at this
    have := weighted_leibniz (n := m) (u := 1) (w := 3) (f := fun s : ℝ => s) (g := deriv E) (βf := 1) (M := |e| * MMc)
      hY0 hY4 hA4 contDiffAt_id (hE'n.of_le (by exact_mod_cast hm)) zero_le_one hM0
      (fun k _ => id_weight hY0 hYW k) hgd
    refine this.trans ?_
    have h1 : ((m : ℝ) + 1) * 2 ^ m ≤ ((n : ℝ) + 1) * 2 ^ n := by
      have h1 : (m : ℝ) + 1 ≤ n + 1 := by exact_mod_cast (by omega : m + 1 ≤ n + 1)
      have h2 : (2 : ℝ) ^ m ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hm
      exact mul_le_mul h1 h2 (by positivity) (by positivity)
    have hW' : W ^ (1 + 3 - m) = W ^ (4 - m) := by congr 1
    rw [hW']
    have hWm : 0 ≤ W ^ (4 - m) := by positivity
    calc ((m : ℝ) + 1) * 2 ^ m * 4 ^ (1 + 3) * 1 * (|e| * MMc) * W ^ (4 - m)
        = (((m : ℝ) + 1) * 2 ^ m) * (4 ^ 4 * (|e| * MMc) * W ^ (4 - m)) := by norm_num; ring
      _ ≤ (((n : ℝ) + 1) * 2 ^ n) * (4 ^ 4 * (|e| * MMc) * W ^ (4 - m)) := by gcongr
      _ = _ := by ring
  have hT3 := weighted_leibniz (n := n) (u := 0) (w := 4) (f := buf) (g := fun s : ℝ => s * deriv E s)
    (βf := BJ) (M := (n + 1) * 2 ^ n * 4 ^ 4 * (|e| * MMc)) hY0 hY4 hA4 (hcn _ hdbu) hh1 hBJ0 (by positivity) hbfbu hh1b
  -- T4: `s * Fu'`
  have hh2b : ∀ m ≤ n, |iteratedDeriv m (fun s : ℝ => s * deriv Fu s) Y| ≤
      ((n + 1) * 2 ^ n * 4 ^ 3 * (|e| * MMu)) * W ^ (3 - m) := by
    intro m hm
    have hgd : ∀ k ≤ m, |iteratedDeriv k (deriv Fu) Y| ≤ |e| * MMu * W ^ (2 - k) := by
      intro k hk
      rw [← iteratedDeriv_succ']
      have := hFj Y (k + 1) hY hY0 (by omega)
      rwa [show 3 - (k + 1) = 2 - k by omega] at this
    have := weighted_leibniz (n := m) (u := 1) (w := 2) (f := fun s : ℝ => s) (g := deriv Fu) (βf := 1) (M := |e| * MMu)
      hY0 hY4 hA4 contDiffAt_id (hF'n.of_le (by exact_mod_cast hm)) zero_le_one hMu0
      (fun k _ => id_weight hY0 hYW k) hgd
    refine this.trans ?_
    have h1 : ((m : ℝ) + 1) * 2 ^ m ≤ ((n : ℝ) + 1) * 2 ^ n := by
      have h1 : (m : ℝ) + 1 ≤ n + 1 := by exact_mod_cast (by omega : m + 1 ≤ n + 1)
      have h2 : (2 : ℝ) ^ m ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hm
      exact mul_le_mul h1 h2 (by positivity) (by positivity)
    have hW' : W ^ (1 + 2 - m) = W ^ (3 - m) := by congr 1
    rw [hW']
    have hWm : 0 ≤ W ^ (3 - m) := by positivity
    calc ((m : ℝ) + 1) * 2 ^ m * 4 ^ (1 + 2) * 1 * (|e| * MMu) * W ^ (3 - m)
        = (((m : ℝ) + 1) * 2 ^ m) * (4 ^ 3 * (|e| * MMu) * W ^ (3 - m)) := by norm_num; ring
      _ ≤ (((n : ℝ) + 1) * 2 ^ n) * (4 ^ 3 * (|e| * MMu) * W ^ (3 - m)) := by gcongr
      _ = _ := by ring
  have hT4 := weighted_leibniz (n := n) (u := 0) (w := 3) (f := bf) (g := fun s : ℝ => s * deriv Fu s)
    (βf := BJ) (M := (n + 1) * 2 ^ n * 4 ^ 3 * (|e| * MMu)) hY0 hY4 hA4 (hcn' _ hdb) hh2 hBJ0 (by positivity) hbfb hh2b
  -- T5, T6
  have hK0 : |K| ≤ |e| * MMc * W ^ 4 := by
    have := hEj 0 0 zero_mem_Yint le_rfl (by omega)
    rw [iteratedDeriv_zero, max_eq_right hA0] at this
    refine this.trans ?_
    gcongr
  have hKu0 : |Ku| ≤ |e| * MMu * W ^ 3 := by
    have := hFj 0 0 zero_mem_Yint le_rfl (by omega)
    rw [iteratedDeriv_zero, max_eq_right hA0] at this
    refine this.trans ?_
    gcongr
  have hgK : ∀ k ≤ n, |iteratedDeriv k (fun _ : ℝ => K) Y| ≤ |e| * MMc * W ^ (4 - k) := by
    intro k _
    rcases k with _ | k
    · simpa using hK0
    · rw [iteratedDeriv_const]; simp; positivity
  have hgKu : ∀ k ≤ n, |iteratedDeriv k (fun _ : ℝ => Ku) Y| ≤ |e| * MMu * W ^ (3 - k) := by
    intro k _
    rcases k with _ | k
    · simpa using hKu0
    · rw [iteratedDeriv_const]; simp; positivity
  have hT5 := weighted_leibniz (n := n) (u := 0) (w := 4) (f := cuf) (g := fun _ : ℝ => K) (βf := BJ) (M := |e| * MMc)
    hY0 hY4 hA4 (hcn _ hdcu) contDiffAt_const hBJ0 hM0 hbfcu hgK
  have hT6 := weighted_leibniz (n := n) (u := 0) (w := 3) (f := cf) (g := fun _ : ℝ => Ku) (βf := BJ) (M := |e| * MMu)
    hY0 hY4 hA4 (hcn' _ hdc) contDiffAt_const hBJ0 hMu0 hbfc hgKu
  simp only [zero_add] at hT1 hT2 hT3 hT4 hT5 hT6
  have hsum : iteratedDeriv n (fun s : ℝ => auf s * E s + af s * Fu s + (buf s * (s * deriv E s) +
      bf s * (s * deriv Fu s)) + (cuf s * K + cf s * Ku)) Y =
      iteratedDeriv n (fun s => auf s * E s) Y + iteratedDeriv n (fun s => af s * Fu s) Y +
        (iteratedDeriv n (fun s => buf s * (s * deriv E s)) Y + iteratedDeriv n (fun s => bf s * (s * deriv Fu s)) Y) +
        (iteratedDeriv n (fun s => cuf s * K) Y + iteratedDeriv n (fun s => cf s * Ku) Y) := by
    have c1 : ContDiffAt ℝ n (fun s => auf s * E s) Y := (hcn _ hdau).mul hEn
    have c2 : ContDiffAt ℝ n (fun s => af s * Fu s) Y := (hcn' _ hda).mul hFn
    have c3 : ContDiffAt ℝ n (fun s => buf s * (s * deriv E s)) Y := (hcn _ hdbu).mul hh1
    have c4 : ContDiffAt ℝ n (fun s => bf s * (s * deriv Fu s)) Y := (hcn' _ hdb).mul hh2
    have c5 : ContDiffAt ℝ n (fun s => cuf s * K) Y := (hcn _ hdcu).mul contDiffAt_const
    have c6 : ContDiffAt ℝ n (fun s => cf s * Ku) Y := (hcn' _ hdc).mul contDiffAt_const
    rw [iteratedDeriv_fun_add ((c1.add c2).add (c3.add c4)) (c5.add c6), iteratedDeriv_fun_add (c1.add c2) (c3.add c4),
      iteratedDeriv_fun_add c1 c2, iteratedDeriv_fun_add c3 c4, iteratedDeriv_fun_add c5 c6]
  rw [hsum]
  have hW3n : 0 ≤ W ^ (3 - n) := by positivity
  have hC : ∀ (C : ℝ), 0 ≤ C → C * W ^ (4 - n) ≤ C * (4 ^ 4 * W ^ (3 - n)) := fun C hC =>
    mul_le_mul_of_nonneg_left hW4' hC
  have hT1' := hT1.trans (hC _ (by positivity))
  have hT3' := hT3.trans (hC _ (by positivity))
  have hT5' := hT5.trans (hC _ (by positivity))
  have habs : ∀ a b c d f g : ℝ, |a + b + (c + d) + (f + g)| ≤ |a| + |b| + (|c| + |d|) + (|f| + |g|) := fun a b c d f g =>
    (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (abs_add_le _ _)))
      (abs_add_le _ _))
  refine (habs _ _ _ _ _ _).trans ?_
  calc _ ≤ ((n + 1) * 2 ^ n * 4 ^ 4 * BJ * (|e| * MMc) * (4 ^ 4 * W ^ (3 - n))) +
        ((n + 1) * 2 ^ n * 4 ^ 3 * BJ * (|e| * MMu) * W ^ (3 - n)) +
        (((n + 1) * 2 ^ n * 4 ^ 4 * BJ * ((n + 1) * 2 ^ n * 4 ^ 4 * (|e| * MMc)) * (4 ^ 4 * W ^ (3 - n))) +
          ((n + 1) * 2 ^ n * 4 ^ 3 * BJ * ((n + 1) * 2 ^ n * 4 ^ 3 * (|e| * MMu)) * W ^ (3 - n))) +
        (((n + 1) * 2 ^ n * 4 ^ 4 * BJ * (|e| * MMc) * (4 ^ 4 * W ^ (3 - n))) +
          ((n + 1) * 2 ^ n * 4 ^ 3 * BJ * (|e| * MMu) * W ^ (3 - n))) := by gcongr
    _ = _ := by rw [CJu, hMMc, hMMu, hBJ]; ring


/-- **`(fct:dJ-jets)`, `ℓ`-derivative line, one parameter direction `u`** (`‖u‖ ≤ 1`): for `n ≤ 12`,
`|∂_Y^n ∂_u (J(p₀+v) - J(p₀))| ≤ C_n |e| max(Y, A_max)^{max(0,3-n)}`. -/
theorem Ju_diff_jets_Y {Ω : Set P} (hΩ : IsOpen Ω) {β : ℝ} (hβ : 8 ≤ β) {V θ : P × ℝ → ℝ} {A : P → ℝ} {H : ℝ → ℝ}
    {T : Set ℝ} {τ2 : ℝ} (v u : P) (hu : ‖u‖ ≤ 1) (e : ℝ)
    (hV : JCΦ 16 (Ω ×ˢ Yint) V β 0) (hA : JCΦ 16 Ω A β 0) (hθ : JCΦ 16 (Ω ×ˢ Ioo (-1 : ℝ) 6) θ β 0)
    (hAY : ∀ p ∈ Ω, A p ∈ Yint) (hz : ∀ q ∈ Ω ×ˢ Yint, q.2 * V q ^ 2 ∈ Ioo (-1 : ℝ) 6)
    (hode : ∀ q ∈ Ω ×ˢ Yint, (A q.1 - q.2) * fderiv ℝ V q (v, 0) =
      e * (V q + 2 * q.2 * fderiv ℝ V q (0, 1)) *
        (A q.1 ^ 5 * V (q.1, A q.1) ^ 11 * θ (q.1, A q.1 * V (q.1, A q.1) ^ 2) -
          q.2 ^ 5 * V q ^ 11 * θ (q.1, q.2 * V q ^ 2)))
    (hVb : ∀ q ∈ Ω ×ˢ Yint, 9 / 10 ≤ V q ∧ V q ≤ 6 / 5) (hT : IsOpen T) (hH : JCΦ 16 T H β 0) (hτ : |τ2| ≤ 1)
    (hHT : ∀ q ∈ Ω ×ˢ Yint, τ2 * (q.2 * V q ^ 2) ∈ T)
    {p0 : P} (hseg : ∀ t ∈ Icc (0 : ℝ) 1, p0 + t • v ∈ Ω) (hA0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ A (p0 + t • v)) {Amax : ℝ}
    (hAm : ∀ t ∈ Icc (0 : ℝ) 1, A (p0 + t • v) ≤ Amax) {Y : ℝ} (hY : Y ∈ Yint) (hY0 : 0 ≤ Y) {n : ℕ} (hn : n ≤ 12) :
    |iteratedDeriv n (fun s : ℝ => fderiv ℝ (Jfun V H τ2) (p0 + v, s) (u, 0)) Y -
        iteratedDeriv n (fun s : ℝ => fderiv ℝ (Jfun V H τ2) (p0, s) (u, 0)) Y| ≤
      |e| * CJu n β * max Y Amax ^ (3 - n) := by
  have hβ0 : 0 ≤ β := by linarith
  have hO : IsOpen (Ω ×ˢ Yint) := hΩ.prod isOpen_Ioo
  obtain ⟨-, -, -, hJc⟩ := J_coef_jc hΩ hβ hV hVb hT hH hτ hHT
  have hf2 : ContDiffOn ℝ ((n : WithTop ℕ∞) + 2) (fun y => fderiv ℝ (Jfun V H τ2) y (u, 0)) (Ω ×ˢ Yint) := by
    have := (hJc.1.fderiv_of_isOpen hO (m := 14) (by norm_num)).clm_apply (contDiffOn_const (c := (u, (0 : ℝ))))
    exact this.of_le (by norm_cast; omega)
  set g : ℝ → ℝ := fun t => iteratedDeriv n (fun s : ℝ => fderiv ℝ (Jfun V H τ2) (p0 + t • v, s) (u, 0)) Y with hg
  set g' : ℝ → ℝ := fun t => iteratedDeriv n (fun s : ℝ =>
    fderiv ℝ (fun y => fderiv ℝ (Jfun V H τ2) y (v, 0)) (p0 + t • v, s) (u, 0)) Y with hg'
  have hder : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt g (g' t) (Icc (0 : ℝ) 1) t := by
    intro t ht
    have h := hasDerivAt_iteratedDeriv_path hO p0 v Y n (fun y => fderiv ℝ (Jfun V H τ2) y (u, 0)) hf2 t ⟨hseg t ht, hY⟩
    have hc : Continuous fun s : ℝ => (p0 + t • v, s) := by fun_prop
    have hev : ∀ᶠ s in 𝓝 Y, (p0 + t • v, s) ∈ Ω ×ˢ Yint :=
      hc.continuousAt.eventually (hO.mem_nhds ⟨hseg t ht, hY⟩)
    have hsw : iteratedDeriv n (fun s => fderiv ℝ (fun y => fderiv ℝ (Jfun V H τ2) y (u, 0)) (p0 + t • v, s) (v, 0)) Y =
        g' t := by
      refine Filter.EventuallyEq.iteratedDeriv_eq n ?_
      filter_upwards [hev] with s hs
      exact fderiv_symm_vec ((hJc.1.contDiffAt (hO.mem_nhds hs)).of_le (by norm_num)) (u, 0) (v, 0)
    rw [hsw] at h
    exact h.hasDerivWithinAt
  have hbd : ∀ t ∈ Icc (0 : ℝ) 1, ‖g' t‖ ≤ |e| * CJu n β * max Y Amax ^ (3 - n) := by
    intro t ht
    have h := Jvu_jets hΩ hβ v u hu e hV hA hθ hAY hz hode hVb hT hH hτ hHT (hseg t ht) hY hY0 (hA0 t ht) (n := n)
      (by omega)
    rw [Real.norm_eq_abs]
    refine h.trans ?_
    have hmx : max Y (A (p0 + t • v)) ≤ max Y Amax := max_le_max le_rfl (hAm t ht)
    have h0 : 0 ≤ max Y (A (p0 + t • v)) := le_trans hY0 (le_max_left _ _)
    have := CJu_nonneg n hβ0
    gcongr
  have := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le hder hbd (left_mem_Icc.mpr zero_le_one)
    (right_mem_Icc.mpr zero_le_one)
  simpa [hg, one_smul, zero_smul, add_zero] using this

/-- info: 'FormalResearch.SignUncertainty.Jvu_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Jvu_eq

/-- info: 'FormalResearch.SignUncertainty.Jvu_jets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Jvu_jets

/-- info: 'FormalResearch.SignUncertainty.Ju_diff_jets_Y' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ju_diff_jets_Y

end DJetU
end FormalResearch.SignUncertainty
