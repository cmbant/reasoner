/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctDJetCoef
public import FormalResearch.SignUncertainty.FctEJetsU
public import FormalResearch.SignUncertainty.FctDJetBase
public import FormalResearch.SignUncertainty.FctVDiff

/-!
# The derivative of the amplitude `J` in a parameter direction (F2a, `(fct:dJ-jets)`)

`fderiv_symm_vec`: symmetry of the mixed second derivative for two arbitrary directions.
`Jv_eq`: `∂_v J = a ∂_v V + b Y ∂_Y ∂_v V + c ∂_v V(·,0)` pointwise on `Ω × Yint` (the chain rule along the path `p + t v`),
with the coefficients `Jca, Jcb, Jcc` of `FctDJetCoef`.

Class: proved, no hypotheses beyond those stated.
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace FormalResearch.SignUncertainty
section DJetDeriv
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Symmetry of the mixed second derivative in two arbitrary directions. -/
lemma fderiv_symm_vec {V : P × ℝ → ℝ} {q : P × ℝ} (hV : ContDiffAt ℝ 2 V q) (x y : P × ℝ) :
    fderiv ℝ (fun z => fderiv ℝ V z x) q y = fderiv ℝ (fun z => fderiv ℝ V z y) q x := by
  have hD : DifferentiableAt ℝ (fderiv ℝ V) q :=
    (hV.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have e1 : ∀ (w : P × ℝ) (x : P × ℝ), fderiv ℝ (fun y => fderiv ℝ V y w) q x =
      fderiv ℝ (fderiv ℝ V) q x w := by
    intro w x
    have h := (ContinuousLinearMap.apply ℝ ℝ w).hasFDerivAt.comp _ hD.hasFDerivAt
    rw [show (fun y => fderiv ℝ V y w) = (⇑(ContinuousLinearMap.apply ℝ ℝ w)) ∘ fderiv ℝ V from rfl, h.fderiv]
    rfl
  have hsymm := (ContDiffAt.isSymmSndFDerivAt hV (by simp [minSmoothness_of_isRCLikeNormedField])) y x
  rw [e1 x, e1 y]
  exact hsymm

variable {Ω : Set P} {V : P × ℝ → ℝ} {H : ℝ → ℝ} {T : Set ℝ} {τ2 : ℝ}

/-- **The derivative of `J` in a parameter direction `v`**: `∂_v J = a ∂_v V + b Y ∂_Y ∂_v V + c ∂_v V(·,0)`. -/
theorem Jv_eq (hΩ : IsOpen Ω) (hV : ContDiffOn ℝ 16 V (Ω ×ˢ Yint))
    (hVb : ∀ q ∈ Ω ×ˢ Yint, 9 / 10 ≤ V q ∧ V q ≤ 6 / 5) (hT : IsOpen T) (hH : ContDiffOn ℝ 16 H T)
    (hHT : ∀ q ∈ Ω ×ˢ Yint, τ2 * (q.2 * V q ^ 2) ∈ T) (hJ : ContDiffOn ℝ 15 (Jfun V H τ2) (Ω ×ˢ Yint)) (v : P)
    {q : P × ℝ} (hq : q ∈ Ω ×ˢ Yint) :
    fderiv ℝ (Jfun V H τ2) q (v, 0) = Jca V H τ2 q * fderiv ℝ V q (v, 0) +
      Jcb V H τ2 q * (q.2 * fderiv ℝ (fun y => fderiv ℝ V y (v, 0)) q (0, 1)) +
      Jcc V H τ2 q * fderiv ℝ V (q.1, 0) (v, 0) := by
  obtain ⟨p, s⟩ := q
  have hO : IsOpen (Ω ×ˢ Yint) := hΩ.prod isOpen_Ioo
  have hq0 : (p, (0 : ℝ)) ∈ Ω ×ˢ Yint := ⟨hq.1, zero_mem_Yint⟩
  have hVq : ContDiffAt ℝ 16 V (p, s) := hV.contDiffAt (hO.mem_nhds hq)
  have hVq0 : ContDiffAt ℝ 16 V (p, 0) := hV.contDiffAt (hO.mem_nhds hq0)
  have hVd : DifferentiableAt ℝ V (p, s) := hVq.differentiableAt (by norm_num)
  have hVd0 : DifferentiableAt ℝ V (p, 0) := hVq0.differentiableAt (by norm_num)
  have hdVd : DifferentiableAt ℝ (fun y => fderiv ℝ V y (0, 1)) (p, s) := by
    have := (hVq.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    exact this.clm_apply (differentiableAt_const _)
  have hJd : DifferentiableAt ℝ (Jfun V H τ2) (p, s) := (hJ.contDiffAt (hO.mem_nhds hq)).differentiableAt (by norm_num)
  have hz : τ2 * (s * V (p, s) ^ 2) ∈ T := hHT _ hq
  have hHd : HasDerivAt H (deriv H (τ2 * (s * V (p, s) ^ 2))) (τ2 * (s * V (p, s) ^ 2)) :=
    (((hH.contDiffAt (hT.mem_nhds hz)).differentiableAt (by norm_num)).hasDerivAt)
  have hx0 : 0 < V (p, s) := by linarith [(hVb _ hq).1]
  have hy0 : 0 < V (p, 0) := by linarith [(hVb _ hq0).1]
  have h1 := hasDerivAt_path_dir (p := p) (Y := s) v hVd
  have h2 := hasDerivAt_path_dir (p := p) (Y := s) v hdVd
  have h3 := hasDerivAt_path_dir (p := p) (Y := (0 : ℝ)) v hVd0
  have hJ' := hasDerivAt_path_dir (p := p) (Y := s) v hJd
  have hsymm : fderiv ℝ (fun y => fderiv ℝ V y (0, 1)) (p, s) (v, 0) =
      fderiv ℝ (fun y => fderiv ℝ V y (v, 0)) (p, s) (0, 1) :=
    fderiv_symm_vec (hVq.of_le (by norm_num)) (0, 1) (v, 0)
  rw [hsymm] at h2
  have e0 : p + (0 : ℝ) • v = p := by simp
  have hxn : V (p + (0 : ℝ) • v, s) ≠ 0 := by rw [e0]; exact hx0.ne'
  have hyn : V (p + (0 : ℝ) • v, 0) ≠ 0 := by rw [e0]; exact hy0.ne'
  have hVi := h1.inv hxn
  have hVi0 := h3.inv hyn
  have hP := (((h2.const_mul s).const_mul 2).mul hVi).const_add 1
  have hRt := h1.mul hVi0
  have hRtn : V (p + (0 : ℝ) • v, s) * (V (p + (0 : ℝ) • v, 0))⁻¹ ≠ 0 := mul_ne_zero hxn (inv_ne_zero hyn)
  have hQ := hRt.rpow_const (p := (1 / 2 : ℝ)) (Or.inl hRtn)
  have hZ := (((h1.pow 2).const_mul s).const_mul τ2)
  have hZ' : HasDerivAt H (deriv H (τ2 * (s * V (p, s) ^ 2))) ((fun t : ℝ => τ2 * (s * V (p + t • v, s) ^ 2)) 0) := by
    simpa [e0] using hHd
  have hHc := HasDerivAt.comp (0 : ℝ) hZ' hZ
  have hD := ((hP.mul hQ).mul hHc)
  have hD' : HasDerivAt (fun t : ℝ => Jfun V H τ2 (p + t • v, s)) _ 0 := hD
  have hEq := hJ'.unique hD'
  simp only [zero_smul, add_zero] at hEq
  rw [hEq]
  have hRt0 : V (p, s) * (V (p, 0))⁻¹ ≠ 0 := mul_ne_zero hx0.ne' (inv_ne_zero hy0.ne')
  simp only [Pi.mul_apply, Pi.inv_apply, Pi.pow_apply, Function.comp_apply, zero_smul, add_zero, Nat.cast_ofNat,
    Jca, Jcb, Jcc]
  rw [Real.rpow_sub_one hRt0]
  generalize (V (p, s) * (V (p, 0))⁻¹) ^ (1 / 2 : ℝ) = Q
  generalize hHz : H (τ2 * (s * V (p, s) ^ 2)) = Hz
  generalize deriv H (τ2 * (s * V (p, s) ^ 2)) = Hd
  have hx := hx0.ne'
  have hy := hy0.ne'
  field_simp
  ring


lemma deriv_snd_eq {f : P × ℝ → ℝ} {p : P} {s : ℝ} (hf : DifferentiableAt ℝ f (p, s)) :
    deriv (fun u : ℝ => f (p, u)) s = fderiv ℝ f (p, s) (0, 1) := by
  have hγ : HasDerivAt (fun u : ℝ => (p, u)) ((0 : P), (1 : ℝ)) s := (hasDerivAt_const s p).prodMk (hasDerivAt_id s)
  exact (hf.hasFDerivAt.comp_hasDerivAt s hγ).deriv

/-- The constant of `Jv_jets`. -/
noncomputable def CJ (n : ℕ) (β : ℝ) : ℝ :=
  ((n + 1) * 2 ^ n * 4 ^ 4 * ((Nat.factorial 15 : ℝ) * Φb^[9] β)) *
    ((n + 2) * 2 ^ (n + 1) * 1000000 * ((Nat.factorial 15 : ℝ) * Φb^[8] β)) * (2 + (n + 1) * 2 ^ n * 4 ^ 4)

lemma CJ_nonneg (n : ℕ) {β : ℝ} (hβ : 0 ≤ β) : 0 ≤ CJ n β := by
  have h8 : 0 ≤ Φb^[8] β := Φb_iter_nonneg hβ 8
  have h9 : 0 ≤ Φb^[9] β := Φb_iter_nonneg hβ 9
  unfold CJ; positivity

/-- `iteratedDeriv k` of the function `s ↦ s` at a point `Y ∈ [0, W]`. -/
lemma id_weight {Y W : ℝ} (hY : 0 ≤ Y) (hW : Y ≤ W) (k : ℕ) :
    |iteratedDeriv k (fun s : ℝ => s) Y| ≤ 1 * W ^ (1 - k) := by
  rcases k with _ | _ | k
  · simp [abs_of_nonneg hY, hW]
  · simp
  · have : iteratedDeriv (k + 2) (fun s : ℝ => s) Y = 0 := by
      rw [iteratedDeriv_succ', iteratedDeriv_succ']
      simp
    rw [this]; simp

/-- **Weighted jets of `∂_v J`**: `|∂_Y^n ∂_v J| ≤ C |e| max(Y, A)^{max(0,4-n)}`, `n ≤ 14`. -/
theorem Jv_jets {Ω : Set P} (hΩ : IsOpen Ω) {β : ℝ} (hβ : 8 ≤ β) {V θ : P × ℝ → ℝ} {A : P → ℝ} {H : ℝ → ℝ}
    {T : Set ℝ} {τ2 : ℝ} (v : P) (e : ℝ)
    (hV : JCΦ 16 (Ω ×ˢ Yint) V β 0) (hA : JCΦ 16 Ω A β 0) (hθ : JCΦ 16 (Ω ×ˢ Ioo (-1 : ℝ) 6) θ β 0)
    (hAY : ∀ p ∈ Ω, A p ∈ Yint) (hz : ∀ q ∈ Ω ×ˢ Yint, q.2 * V q ^ 2 ∈ Ioo (-1 : ℝ) 6)
    (hode : ∀ q ∈ Ω ×ˢ Yint, (A q.1 - q.2) * fderiv ℝ V q (v, 0) =
      e * (V q + 2 * q.2 * fderiv ℝ V q (0, 1)) *
        (A q.1 ^ 5 * V (q.1, A q.1) ^ 11 * θ (q.1, A q.1 * V (q.1, A q.1) ^ 2) -
          q.2 ^ 5 * V q ^ 11 * θ (q.1, q.2 * V q ^ 2)))
    (hVb : ∀ q ∈ Ω ×ˢ Yint, 9 / 10 ≤ V q ∧ V q ≤ 6 / 5) (hT : IsOpen T) (hH : JCΦ 16 T H β 0) (hτ : |τ2| ≤ 1)
    (hHT : ∀ q ∈ Ω ×ˢ Yint, τ2 * (q.2 * V q ^ 2) ∈ T)
    {p : P} (hp : p ∈ Ω) {Y : ℝ} (hY : Y ∈ Yint) (hY0 : 0 ≤ Y) (hA0 : 0 ≤ A p) {n : ℕ} (hn : n ≤ 14) :
    |iteratedDeriv n (fun s : ℝ => fderiv ℝ (Jfun V H τ2) (p, s) (v, 0)) Y| ≤
      |e| * CJ n β * max Y (A p) ^ (4 - n) := by
  have hβ0 : 0 ≤ β := by linarith
  have hO : IsOpen (Ω ×ˢ Yint) := hΩ.prod isOpen_Ioo
  have hOd : UniqueDiffOn ℝ (Ω ×ˢ Yint) := hO.uniqueDiffOn
  obtain ⟨hca, hcb, hcc, hJc⟩ := J_coef_jc hΩ hβ hV hVb hT hH hτ hHT
  have hpY : (p, Y) ∈ Ω ×ˢ Yint := ⟨hp, hY⟩
  have hp0 : (p, (0 : ℝ)) ∈ Ω ×ˢ Yint := ⟨hp, zero_mem_Yint⟩
  have hb9 : 0 ≤ Φb^[9] β := Φb_iter_nonneg hβ0 9
  -- the coefficient jets in Y
  obtain ⟨hda, hba⟩ := dY_bound hO hb9 (hca : JC 15 _ _ _) hpY
  obtain ⟨hdb, hbb⟩ := dY_bound hO hb9 (hcb : JC 15 _ _ _) hpY
  obtain ⟨hdc, hbc⟩ := dY_bound hO hb9 (hcc : JC 15 _ _ _) hpY
  set BJ : ℝ := (Nat.factorial 15 : ℝ) * Φb^[9] β with hBJ
  set W : ℝ := max Y (A p) with hW
  have hW0 : 0 ≤ W := le_max_of_le_left hY0
  have hYW : Y ≤ W := le_max_left _ _
  have hAW : A p ≤ W := le_max_right _ _
  have hY4 : Y ≤ 4 := by have := hY.2; linarith
  have hA4 : A p ≤ 4 := by have := (hAY p hp).2; linarith
  -- the jets of `E = ∂_v V(p, ·)`
  set E : ℝ → ℝ := fun s => fderiv ℝ V (p, s) (v, 0) with hE
  set MMc : ℝ := (n + 2) * 2 ^ (n + 1) * 1000000 * ((Nat.factorial 15 : ℝ) * Φb^[8] β) with hMMc
  have hΦ8 : 0 ≤ Φb^[8] β := Φb_iter_nonneg hβ0 8
  have hMMc0 : 0 ≤ MMc := by rw [hMMc]; positivity
  have hEj : ∀ (y : ℝ) (k : ℕ), y ∈ Yint → 0 ≤ y → k ≤ n + 1 →
      |iteratedDeriv k (fun s : ℝ => fderiv ℝ V (p, s) (v, 0)) y| ≤
        |e| * MMc * max y (A p) ^ (4 - k) := by
    intro y k hy hy0 hk
    have h := E_jets hΩ (by linarith : 4 ≤ β) v e hV hA hθ hAY hz hode hp hy hy0 hA0 (n := k) (by omega)
    refine h.trans ?_
    have hc : ((k : ℝ) + 1) * 2 ^ k ≤ ((n : ℝ) + 2) * 2 ^ (n + 1) := by
      have h1 : (k : ℝ) + 1 ≤ n + 2 := by exact_mod_cast (by omega : k + 1 ≤ n + 2)
      have h2 : (2 : ℝ) ^ k ≤ 2 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) hk
      exact mul_le_mul h1 h2 (by positivity) (by positivity)
    have hWk : 0 ≤ max y (A p) ^ (4 - k) := by positivity
    have : 0 ≤ (Nat.factorial 15 : ℝ) * Φb^[8] β := by positivity
    calc |e| * (((k : ℝ) + 1) * 2 ^ k * 1000000 * ((Nat.factorial 15 : ℝ) * Φb^[8] β) * max y (A p) ^ (4 - k))
        ≤ |e| * (((n : ℝ) + 2) * 2 ^ (n + 1) * 1000000 * ((Nat.factorial 15 : ℝ) * Φb^[8] β) * max y (A p) ^ (4 - k)) := by
          gcongr
      _ = _ := by rw [hMMc]; ring
  have hS : IsOpen {s : ℝ | (p, s) ∈ Ω ×ˢ Yint} := hO.preimage (Continuous.prodMk_right p)
  have hYS : Y ∈ {s : ℝ | (p, s) ∈ Ω ×ˢ Yint} := hpY
  have hEc15 : ContDiffOn ℝ 15 (fun y => fderiv ℝ V y (v, 0)) (Ω ×ˢ Yint) := by
    have := ((hV.1.fderiv_of_isOpen hO (m := 15) (by norm_num)).clm_apply (contDiffOn_const (c := (v, (0 : ℝ)))))
    simpa using this
  have hE15 : ContDiffOn ℝ 15 E {s : ℝ | (p, s) ∈ Ω ×ˢ Yint} :=
    hEc15.comp (contDiffOn_const.prodMk contDiffOn_id) (fun s hs => hs)
  have hE'14 : ContDiffOn ℝ 14 (deriv E) {s : ℝ | (p, s) ∈ Ω ×ˢ Yint} :=
    hE15.deriv_of_isOpen hS (by norm_num)
  have hEat : ContDiffAt ℝ ((n + 1 : ℕ) : WithTop ℕ∞) E Y :=
    (hE15.contDiffAt (hS.mem_nhds hYS)).of_le (by exact_mod_cast (by omega : n + 1 ≤ 15))
  have hE'at : ContDiffAt ℝ (n : WithTop ℕ∞) (deriv E) Y :=
    (hE'14.contDiffAt (hS.mem_nhds hYS)).of_le (by exact_mod_cast hn)
  have hEn : ContDiffAt ℝ (n : WithTop ℕ∞) E Y := hEat.of_le (by exact_mod_cast Nat.le_succ n)
  have hhat : ContDiffAt ℝ (n : WithTop ℕ∞) (fun s : ℝ => s * deriv E s) Y := contDiffAt_id.mul hE'at
  -- the representation
  set af : ℝ → ℝ := fun s => Jca V H τ2 (p, s) with haf
  set bf : ℝ → ℝ := fun s => Jcb V H τ2 (p, s) with hbf
  set cf : ℝ → ℝ := fun s => Jcc V H τ2 (p, s) with hcf
  set K : ℝ := E 0 with hK
  have hrep : (fun s : ℝ => fderiv ℝ (Jfun V H τ2) (p, s) (v, 0)) =ᶠ[𝓝 Y]
      fun s => af s * E s + bf s * (s * deriv E s) + cf s * K := by
    filter_upwards [hS.mem_nhds hYS] with s hs
    have h := Jv_eq hΩ hV.1 hVb hT hH.1 hHT hJc.1 v hs
    have hd : deriv E s = fderiv ℝ (fun y => fderiv ℝ V y (v, 0)) (p, s) (0, 1) :=
      deriv_snd_eq ((hEc15.contDiffAt (hO.mem_nhds hs)).differentiableAt (by norm_num))
    rw [h, hd]
  rw [hrep.iteratedDeriv_eq n]
  -- jets of `a, b, c`
  have hbd : ∀ (g : ℝ → ℝ), ContDiffAt ℝ 15 g Y → (∀ j ≤ 15, |iteratedDeriv j g Y| ≤ BJ) → ∀ k ≤ n,
      |iteratedDeriv k g Y| ≤ BJ * W ^ (0 - k) := by
    intro g _ hg k hk
    simpa using hg k (by omega)
  have hbfa := hbd af hda (fun j hj => by simpa [haf, hBJ] using hba j hj)
  have hbfb := hbd bf hdb (fun j hj => by simpa [hbf, hBJ] using hbb j hj)
  have hbfc := hbd cf hdc (fun j hj => by simpa [hcf, hBJ] using hbc j hj)
  have hBJ0 : 0 ≤ BJ := by rw [hBJ]; positivity
  have hM0 : 0 ≤ |e| * MMc := by positivity
  -- T1
  have hgE : ∀ k ≤ n, |iteratedDeriv k E Y| ≤ |e| * MMc * W ^ (4 - k) := fun k hk =>
    hEj Y k hY hY0 (by omega)
  have hT1 := weighted_leibniz (n := n) (u := 0) (w := 4) (f := af) (g := E) hY0 hY4 hA4 (hda.of_le (by exact_mod_cast (by omega : n ≤ 15))) hEn hBJ0 hM0 hbfa hgE
  -- T2
  have hh : ∀ m ≤ n, |iteratedDeriv m (fun s : ℝ => s * deriv E s) Y| ≤
      ((n + 1) * 2 ^ n * 4 ^ 4 * (|e| * MMc)) * W ^ (4 - m) := by
    intro m hm
    have hgd : ∀ k ≤ m, |iteratedDeriv k (deriv E) Y| ≤ |e| * MMc * W ^ (3 - k) := by
      intro k hk
      rw [← iteratedDeriv_succ']
      have := hEj Y (k + 1) hY hY0 (by omega)
      rwa [show 4 - (k + 1) = 3 - k by omega] at this
    have := weighted_leibniz (n := m) (u := 1) (w := 3) (f := fun s : ℝ => s) (g := deriv E) (βf := 1) (M := |e| * MMc)
      hY0 hY4 hA4 contDiffAt_id (hE'at.of_le (by exact_mod_cast hm)) zero_le_one hM0
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
  have hT2 := weighted_leibniz (n := n) (u := 0) (w := 4) (f := bf) (g := fun s : ℝ => s * deriv E s)
    (βf := BJ) (M := (n + 1) * 2 ^ n * 4 ^ 4 * (|e| * MMc)) hY0 hY4 hA4
    (hdb.of_le (by exact_mod_cast (by omega : n ≤ 15))) hhat hBJ0 (by positivity) hbfb hh
  -- T3
  have hK0 : |K| ≤ |e| * MMc * W ^ 4 := by
    have := hEj 0 0 zero_mem_Yint le_rfl (by omega)
    rw [iteratedDeriv_zero, max_eq_right hA0] at this
    refine this.trans ?_
    gcongr
  have hgK : ∀ k ≤ n, |iteratedDeriv k (fun _ : ℝ => K) Y| ≤ |e| * MMc * W ^ (4 - k) := by
    intro k _
    rcases k with _ | k
    · simpa using hK0
    · rw [iteratedDeriv_const]
      simp
      positivity
  have hT3 := weighted_leibniz (n := n) (u := 0) (w := 4) (f := cf) (g := fun _ : ℝ => K) (βf := BJ) (M := |e| * MMc)
    hY0 hY4 hA4 (hdc.of_le (by exact_mod_cast (by omega : n ≤ 15))) contDiffAt_const hBJ0 hM0 hbfc hgK
  have hsum : iteratedDeriv n (fun s : ℝ => af s * E s + bf s * (s * deriv E s) + cf s * K) Y =
      iteratedDeriv n (fun s => af s * E s) Y + iteratedDeriv n (fun s => bf s * (s * deriv E s)) Y +
        iteratedDeriv n (fun s => cf s * K) Y := by
    have h1 : ContDiffAt ℝ n (fun s => af s * E s) Y := (hda.of_le (by exact_mod_cast (by omega : n ≤ 15))).mul hEn
    have h2 : ContDiffAt ℝ n (fun s => bf s * (s * deriv E s)) Y :=
      (hdb.of_le (by exact_mod_cast (by omega : n ≤ 15))).mul hhat
    have h3 : ContDiffAt ℝ n (fun s => cf s * K) Y := (hdc.of_le (by exact_mod_cast (by omega : n ≤ 15))).mul contDiffAt_const
    rw [iteratedDeriv_fun_add (h1.add h2) h3, iteratedDeriv_fun_add h1 h2]
  rw [hsum]
  simp only [zero_add] at hT1 hT2 hT3
  have hWn : 0 ≤ W ^ (4 - n) := by positivity
  calc _ ≤ |iteratedDeriv n (fun s => af s * E s) Y| + |iteratedDeriv n (fun s => bf s * (s * deriv E s)) Y| +
        |iteratedDeriv n (fun s => cf s * K) Y| := (abs_add_three _ _ _)
    _ ≤ ((n + 1) * 2 ^ n * 4 ^ 4 * BJ * (|e| * MMc) * W ^ (4 - n)) +
        ((n + 1) * 2 ^ n * 4 ^ 4 * BJ * ((n + 1) * 2 ^ n * 4 ^ 4 * (|e| * MMc)) * W ^ (4 - n)) +
        ((n + 1) * 2 ^ n * 4 ^ 4 * BJ * (|e| * MMc) * W ^ (4 - n)) := by gcongr
    _ = _ := by rw [CJ, hMMc, hBJ]; ring

/-- **`(fct:dJ-jets)`, first two lines, in one parameter direction**: the weighted one-variable jets of `J(p₀ + v, ·) - J(p₀, ·)`,
`|∂_Y^n (J(p₀+v) - J(p₀))| ≤ C_n |e| max(Y, A_max)^{max(0,4-n)}` (`n ≤ 13`), by the mean value inequality along the segment from
`Jv_jets`. -/
theorem J_diff_jets_Y {Ω : Set P} (hΩ : IsOpen Ω) {β : ℝ} (hβ : 8 ≤ β) {V θ : P × ℝ → ℝ} {A : P → ℝ} {H : ℝ → ℝ}
    {T : Set ℝ} {τ2 : ℝ} (v : P) (e : ℝ)
    (hV : JCΦ 16 (Ω ×ˢ Yint) V β 0) (hA : JCΦ 16 Ω A β 0) (hθ : JCΦ 16 (Ω ×ˢ Ioo (-1 : ℝ) 6) θ β 0)
    (hAY : ∀ p ∈ Ω, A p ∈ Yint) (hz : ∀ q ∈ Ω ×ˢ Yint, q.2 * V q ^ 2 ∈ Ioo (-1 : ℝ) 6)
    (hode : ∀ q ∈ Ω ×ˢ Yint, (A q.1 - q.2) * fderiv ℝ V q (v, 0) =
      e * (V q + 2 * q.2 * fderiv ℝ V q (0, 1)) *
        (A q.1 ^ 5 * V (q.1, A q.1) ^ 11 * θ (q.1, A q.1 * V (q.1, A q.1) ^ 2) -
          q.2 ^ 5 * V q ^ 11 * θ (q.1, q.2 * V q ^ 2)))
    (hVb : ∀ q ∈ Ω ×ˢ Yint, 9 / 10 ≤ V q ∧ V q ≤ 6 / 5) (hT : IsOpen T) (hH : JCΦ 16 T H β 0) (hτ : |τ2| ≤ 1)
    (hHT : ∀ q ∈ Ω ×ˢ Yint, τ2 * (q.2 * V q ^ 2) ∈ T)
    {p0 : P} (hseg : ∀ t ∈ Icc (0 : ℝ) 1, p0 + t • v ∈ Ω) (hA0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ A (p0 + t • v)) {Amax : ℝ}
    (hAm : ∀ t ∈ Icc (0 : ℝ) 1, A (p0 + t • v) ≤ Amax) {Y : ℝ} (hY : Y ∈ Yint) (hY0 : 0 ≤ Y) {n : ℕ} (hn : n ≤ 13) :
    |iteratedDeriv n (fun s : ℝ => Jfun V H τ2 (p0 + v, s)) Y - iteratedDeriv n (fun s : ℝ => Jfun V H τ2 (p0, s)) Y| ≤
      |e| * CJ n β * max Y Amax ^ (4 - n) := by
  have hβ0 : 0 ≤ β := by linarith
  have hO : IsOpen (Ω ×ˢ Yint) := hΩ.prod isOpen_Ioo
  obtain ⟨-, -, -, hJc⟩ := J_coef_jc hΩ hβ hV hVb hT hH hτ hHT
  have hJ2 : ContDiffOn ℝ ((n : WithTop ℕ∞) + 2) (Jfun V H τ2) (Ω ×ˢ Yint) :=
    hJc.1.of_le (by norm_cast; omega)
  set g : ℝ → ℝ := fun t => iteratedDeriv n (fun s : ℝ => Jfun V H τ2 (p0 + t • v, s)) Y with hg
  set g' : ℝ → ℝ := fun t => iteratedDeriv n (fun s : ℝ => fderiv ℝ (Jfun V H τ2) (p0 + t • v, s) (v, 0)) Y with hg'
  have hder : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt g (g' t) (Icc (0 : ℝ) 1) t := fun t ht =>
    (hasDerivAt_iteratedDeriv_path hO p0 v Y n (Jfun V H τ2) hJ2 t ⟨hseg t ht, hY⟩).hasDerivWithinAt
  have hbd : ∀ t ∈ Icc (0 : ℝ) 1, ‖g' t‖ ≤ |e| * CJ n β * max Y Amax ^ (4 - n) := by
    intro t ht
    have h := Jv_jets hΩ hβ v e hV hA hθ hAY hz hode hVb hT hH hτ hHT (hseg t ht) hY hY0 (hA0 t ht) (n := n) (by omega)
    rw [Real.norm_eq_abs]
    refine h.trans ?_
    have hmx : max Y (A (p0 + t • v)) ≤ max Y Amax := max_le_max le_rfl (hAm t ht)
    have h0 : 0 ≤ max Y (A (p0 + t • v)) := le_trans hY0 (le_max_left _ _)
    have := CJ_nonneg n hβ0
    gcongr
  have := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le hder hbd (left_mem_Icc.mpr zero_le_one)
    (right_mem_Icc.mpr zero_le_one)
  simpa [hg, one_smul, zero_smul, add_zero] using this

/-- `J(p, 0) = H(0)`: with `H(0) = 1` (`G(0) = 0`) the amplitude is `1` at `Y = 0`, so `δJ(0) = 0`. -/
lemma Jfun_zero {V : P × ℝ → ℝ} {H : ℝ → ℝ} {τ2 : ℝ} {p : P} (hV0 : V (p, 0) ≠ 0) :
    Jfun V H τ2 (p, 0) = H 0 := by
  simp [Jfun, hV0]

/-- info: 'FormalResearch.SignUncertainty.Jv_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Jv_eq

/-- info: 'FormalResearch.SignUncertainty.Jv_jets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Jv_jets

/-- info: 'FormalResearch.SignUncertainty.J_diff_jets_Y' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms J_diff_jets_Y

end DJetDeriv
end FormalResearch.SignUncertainty
