module

public import FormalResearch.SignUncertainty.FctVDiff

/-!
# The `ℓ`-derivative of `∂_v V`: representation and weighted jets (F2a, `fct:comp-cfu`)

`E_eq_dir`: differentiating the divided-difference representation `E_eq` of `∂_v V` in a parameter direction `u`
(product rule along the path `p + t u`).  `E_jets_u`, `V_diff_jets_u_Y`, `ChartSetup.V_diff_jets_u`: the weighted one-variable jets
`|∂_Y^n ∂_u ∂_v V| ≤ C |e| max(Y, A)^{max(0, 3 - n)}`, the weights of the second line of `(fct:V-diff-jets)`.

Class: proved, no hypotheses beyond those stated.
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace FormalResearch.SignUncertainty
section EJetsU
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- `d/dt` of a differentiable `f` along the path `(p + t u, Y)`, at `t = 0`. -/
lemma hasDerivAt_path_dir {f : P × ℝ → ℝ} {p : P} {Y : ℝ} (u : P) (hf : DifferentiableAt ℝ f (p, Y)) :
    HasDerivAt (fun t : ℝ => f (p + t • u, Y)) (fderiv ℝ f (p, Y) (u, 0)) 0 := by
  have hγ : HasDerivAt (fun t : ℝ => (p + t • u, Y)) (u, 0) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => p + t • u) u 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add p
    exact h1.prodMk (hasDerivAt_const 0 Y)
  have h := hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ (by simp)
  exact h

lemma hasDerivAt_pathP_dir {f : P → ℝ} {p : P} (u : P) (hf : DifferentiableAt ℝ f p) :
    HasDerivAt (fun t : ℝ => f (p + t • u)) (fderiv ℝ f p u) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => p + t • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add p
  exact hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) h1 (by simp)

/-- **Differentiation of the representation of `∂_v V` in a parameter direction `u`.** -/
lemma E_eq_dir {G Ev U : P × ℝ → ℝ} {A Ga : P → ℝ} {e : ℝ} {Ω : Set P} (hΩ : IsOpen Ω) {p : P} {Y : ℝ}
    (hpY : (p, Y) ∈ Ω ×ˢ Yint)
    (hEq : ∀ q ∈ Ω ×ˢ Yint, Ev q = e * (U q * ((∑ k ∈ Finset.range 5, q.2 ^ (4 - k) * A q.1 ^ k) * Ga q.1 +
      q.2 ^ 5 * divInt G A q)))
    (hEvd : DifferentiableAt ℝ Ev (p, Y)) (hUd : DifferentiableAt ℝ U (p, Y))
    (hId : DifferentiableAt ℝ (divInt G A) (p, Y)) (hAd : DifferentiableAt ℝ A p)
    (hGad : DifferentiableAt ℝ Ga p) (u : P) :
    fderiv ℝ Ev (p, Y) (u, 0) = e * (fderiv ℝ U (p, Y) (u, 0) *
        ((∑ k ∈ Finset.range 5, Y ^ (4 - k) * A p ^ k) * Ga p + Y ^ 5 * divInt G A (p, Y)) +
      U (p, Y) * ((∑ k ∈ Finset.range 5, Y ^ (4 - k) * (k * A p ^ (k - 1) * fderiv ℝ A p u)) * Ga p +
        (∑ k ∈ Finset.range 5, Y ^ (4 - k) * A p ^ k) * fderiv ℝ Ga p u +
        Y ^ 5 * fderiv ℝ (divInt G A) (p, Y) (u, 0))) := by
  have hO : IsOpen (Ω ×ˢ Yint) := hΩ.prod isOpen_Ioo
  have hEv' := hasDerivAt_path_dir (p := p) (Y := Y) u hEvd
  have hU' := hasDerivAt_path_dir (p := p) (Y := Y) u hUd
  have hI' := hasDerivAt_path_dir (p := p) (Y := Y) u hId
  have hA' := hasDerivAt_pathP_dir u hAd
  have hGa' := hasDerivAt_pathP_dir u hGad
  have hSum : HasDerivAt (fun t : ℝ => ∑ k ∈ Finset.range 5, Y ^ (4 - k) * A (p + t • u) ^ k)
      (∑ k ∈ Finset.range 5, Y ^ (4 - k) * (k * A p ^ (k - 1) * fderiv ℝ A p u)) 0 := by
    refine HasDerivAt.fun_sum (fun k _ => ?_)
    have h1 := (hA'.fun_pow k).const_mul (Y ^ (4 - k))
    simpa using h1
  have hF : HasDerivAt (fun t : ℝ => e * (U (p + t • u, Y) * ((∑ k ∈ Finset.range 5, Y ^ (4 - k) * A (p + t • u) ^ k) *
        Ga (p + t • u) + Y ^ 5 * divInt G A (p + t • u, Y))))
      (e * (fderiv ℝ U (p, Y) (u, 0) *
        ((∑ k ∈ Finset.range 5, Y ^ (4 - k) * A p ^ k) * Ga p + Y ^ 5 * divInt G A (p, Y)) +
      U (p, Y) * ((∑ k ∈ Finset.range 5, Y ^ (4 - k) * (k * A p ^ (k - 1) * fderiv ℝ A p u)) * Ga p +
        (∑ k ∈ Finset.range 5, Y ^ (4 - k) * A p ^ k) * fderiv ℝ Ga p u +
        Y ^ 5 * fderiv ℝ (divInt G A) (p, Y) (u, 0)))) 0 := by
    have h := ((hU'.fun_mul ((hSum.fun_mul hGa').fun_add (hI'.const_mul (Y ^ 5)))).const_mul e)
    refine h.congr_deriv ?_
    simp only [zero_smul, add_zero]
  have hev : (fun t : ℝ => Ev (p + t • u, Y)) =ᶠ[𝓝 0] fun t : ℝ => e * (U (p + t • u, Y) *
      ((∑ k ∈ Finset.range 5, Y ^ (4 - k) * A (p + t • u) ^ k) * Ga (p + t • u) +
        Y ^ 5 * divInt G A (p + t • u, Y))) := by
    have hc : Continuous fun t : ℝ => (p + t • u, Y) := by fun_prop
    have : ∀ᶠ t : ℝ in 𝓝 0, (p + t • u, Y) ∈ Ω ×ˢ Yint :=
      (hc.continuousAt (x := 0)).eventually (hO.mem_nhds (by simpa using hpY))
    filter_upwards [this] with t ht
    exact hEq _ ht
  exact (hEv'.unique (hF.congr_of_eventuallyEq hev))


/-- **Weighted one-variable jets of `∂_u ∂_v V`** (second line of `(fct:V-diff-jets)`, in one parameter direction `u`,
`‖u‖ ≤ 1`): `|∂_Y^n ∂_u ∂_v V| ≤ C |e| max(Y, A)^{max(0, 3-n)}`, `C` depending only on `n` and `β`. -/
theorem E_jets_u {Ω : Set P} (hΩ : IsOpen Ω) {β : ℝ} (hβ : 4 ≤ β) {V θ : P × ℝ → ℝ} {A : P → ℝ} (v u : P)
    (hu : ‖u‖ ≤ 1) (e : ℝ)
    (hV : JCΦ 16 (Ω ×ˢ Yint) V β 0) (hA : JCΦ 16 Ω A β 0) (hθ : JCΦ 16 (Ω ×ˢ Ioo (-1 : ℝ) 6) θ β 0)
    (hAY : ∀ p ∈ Ω, A p ∈ Yint) (hz : ∀ q ∈ Ω ×ˢ Yint, q.2 * V q ^ 2 ∈ Ioo (-1 : ℝ) 6)
    (hode : ∀ q ∈ Ω ×ˢ Yint, (A q.1 - q.2) * fderiv ℝ V q (v, 0) =
      e * (V q + 2 * q.2 * fderiv ℝ V q (0, 1)) *
        (A q.1 ^ 5 * V (q.1, A q.1) ^ 11 * θ (q.1, A q.1 * V (q.1, A q.1) ^ 2) -
          q.2 ^ 5 * V q ^ 11 * θ (q.1, q.2 * V q ^ 2)))
    {p : P} (hp : p ∈ Ω) {Y : ℝ} (hY : Y ∈ Yint) (hY0 : 0 ≤ Y) (hA0 : 0 ≤ A p) {n : ℕ} (hn : n ≤ 14) :
    |iteratedDeriv n (fun s : ℝ => fderiv ℝ (fun y => fderiv ℝ V y (v, 0)) (p, s) (u, 0)) Y| ≤
      |e| * ((n + 1) * 2 ^ n * 10000000 * ((Nat.factorial 14 : ℝ) * Φb^[9] β) * max Y (A p) ^ (3 - n)) := by
  have hβ0 : 0 ≤ β := by linarith
  have hO : IsOpen (Ω ×ˢ Yint) := hΩ.prod isOpen_Ioo
  have hOd : UniqueDiffOn ℝ (Ω ×ˢ Yint) := hO.uniqueDiffOn
  have hΩd : UniqueDiffOn ℝ Ω := hΩ.uniqueDiffOn
  obtain ⟨hG, hGa, hIG, hU⟩ := E_build hΩ hβ hV hA hθ hAY hz
  set G : P × ℝ → ℝ := fun q => V q ^ 11 * θ (q.1, q.2 * V q ^ 2) with hGdef
  set Ga : P → ℝ := fun p => G (p, A p) with hGadef
  set U : P × ℝ → ℝ := fun q => V q + 2 * q.2 * fderiv ℝ V q (0, 1) with hUdef
  have hG1 : ContDiffOn ℝ 1 G (Ω ×ˢ Yint) := (hG : JC 16 _ G _).1.of_le (by norm_num)
  have hEv : JC 15 (Ω ×ˢ Yint) (fun y => fderiv ℝ V y (v, 0)) _ :=
    (JC.succ_fderiv hO (hV : JC 16 _ V _)).clm_apply_const hOd (v, 0)
  have hEq := E_eq hΩ (G := G) (A' := A) (Ev := fun y => fderiv ℝ V y (v, 0)) (U := U) (e := e)
    hG1 hAY hEv.1.continuousOn (hU : JC 15 _ U _).1.continuousOn
    (hIG : JC 15 _ (divInt G A) _).1.continuousOn (fun q hq => by rw [hode q hq]; simp only [hGdef, hUdef]; ring)
  have hn1 : ‖((u : P), (0 : ℝ))‖ ≤ 1 := by simpa [Prod.norm_def] using hu
  -- directional derivatives of the building blocks
  have hdir : ∀ {k : ℕ} {W : Set (P × ℝ)} (_ : IsOpen W) {f : P × ℝ → ℝ} {b : ℝ}, 0 ≤ b → JC (k + 1) W f b →
      JC k W (fun q => fderiv ℝ f q (u, 0)) b := by
    intro k W hW f b hb h
    have := (h.succ_fderiv hW).clm_apply_const hW.uniqueDiffOn (u, 0)
    exact this.mono (by nlinarith)
  have hdU : JCΦ 14 (Ω ×ˢ Yint) (fun q => fderiv ℝ U q (u, 0)) β 3 :=
    hdir hO (Φb_iter_nonneg hβ0 3) (show JC 15 _ U (Φb^[3] β) from hU)
  have hdI : JCΦ 14 (Ω ×ˢ Yint) (fun q => fderiv ℝ (divInt G A) q (u, 0)) β 7 :=
    hdir hO (Φb_iter_nonneg hβ0 7) (show JC 15 _ (divInt G A) (Φb^[7] β) from hIG)
  have hU14 : JCΦ 14 (Ω ×ˢ Yint) U β 3 := (hU : JCΦ 15 _ _ β 3).mono_order (by norm_num)
  have hI14 : JCΦ 14 (Ω ×ˢ Yint) (divInt G A) β 7 := (hIG : JCΦ 15 _ _ β 7).mono_order (by norm_num)
  have hpO : (p, Y) ∈ Ω ×ˢ Yint := ⟨hp, hY⟩
  -- constants in `p`
  have hΩO : IsOpen Ω := hΩ
  have hdA : |fderiv ℝ A p u| ≤ β := by
    have h1 := ((show JC 16 Ω A β from hA).succ_fderiv hΩO).clm_apply_const hΩd u
    have h2 := JB.apply_le h1.2 hp
    nlinarith [norm_nonneg u]
  have hdGa : |fderiv ℝ Ga p u| ≤ Φb^[7] β := by
    have h1 := ((show JC 16 Ω Ga (Φb^[7] β) from hGa).succ_fderiv hΩO).clm_apply_const hΩd u
    have h2 := JB.apply_le h1.2 hp
    nlinarith [norm_nonneg u, Φb_iter_nonneg hβ0 7]
  have hGa7 : |Ga p| ≤ Φb^[7] β := JB.apply_le (show JC 16 Ω Ga (Φb^[7] β) from hGa).2 hp
  have hdGa' : |fderiv ℝ Ga p u| ≤ Φb^[7] β := hdGa
  have cGa : JCΦ 14 (Ω ×ˢ Yint) (fun _ : P × ℝ => Ga p) β 7 := JCΦ.const hOd hGa7
  have cdGa : JCΦ 14 (Ω ×ˢ Yint) (fun _ : P × ℝ => fderiv ℝ Ga p u) β 7 := JCΦ.const hOd hdGa'
  have cdA : JCΦ 14 (Ω ×ˢ Yint) (fun _ : P × ℝ => fderiv ℝ A p u) β 0 := JCΦ.const hOd hdA
  have ckap : JCΦ 14 (Ω ×ˢ Yint) (fun _ : P × ℝ => fderiv ℝ A p u * Ga p) β 8 :=
    JCΦ.mul hOd hβ0 (by norm_num) cdA cGa (by norm_num)
  have m1 : JCΦ 14 (Ω ×ˢ Yint) (fun q => fderiv ℝ U q (u, 0) * Ga p) β 8 :=
    JCΦ.mul hOd hβ0 (by norm_num) hdU cGa (by norm_num)
  have m2 : JCΦ 14 (Ω ×ˢ Yint) (fun q => U q * fderiv ℝ Ga p u) β 8 :=
    JCΦ.mul hOd hβ0 (by norm_num) hU14 cdGa (by norm_num)
  have m3 : JCΦ 14 (Ω ×ˢ Yint) (fun q => fderiv ℝ U q (u, 0) * divInt G A q) β 8 :=
    JCΦ.mul hOd hβ0 (by norm_num) hdU hI14 (by norm_num)
  have m4 : JCΦ 14 (Ω ×ˢ Yint) (fun q => U q * fderiv ℝ (divInt G A) q (u, 0)) β 8 :=
    JCΦ.mul hOd hβ0 (by norm_num) hU14 hdI (by norm_num)
  have hg0 : JCΦ 14 (Ω ×ˢ Yint) (fun q => fderiv ℝ U q (u, 0) * Ga p + U q * fderiv ℝ Ga p u) β 9 :=
    JCΦ.add hOd m1 m2 (by norm_num)
  have hg1 : JCΦ 14 (Ω ×ˢ Yint) (fun q => fderiv ℝ U q (u, 0) * divInt G A q +
      U q * fderiv ℝ (divInt G A) q (u, 0)) β 9 := JCΦ.add hOd m3 m4 (by norm_num)
  have hg2 : JCΦ 14 (Ω ×ˢ Yint) (fun q => U q * (fderiv ℝ A p u * Ga p)) β 9 :=
    JCΦ.mul hOd hβ0 (by norm_num) hU14 ckap (by norm_num)
  have hb9 : 0 ≤ Φb^[9] β := Φb_iter_nonneg hβ0 9
  obtain ⟨hcd0, hb0⟩ := dY_bound hO hb9 (hg0 : JC 14 _ _ _) hpO
  obtain ⟨hcd1, hb1⟩ := dY_bound hO hb9 (hg1 : JC 14 _ _ _) hpO
  obtain ⟨hcd2, hb2⟩ := dY_bound hO hb9 (hg2 : JC 14 _ _ _) hpO
  -- the representation near `Y`
  have hSo : IsOpen {s : ℝ | (p, s) ∈ Ω ×ˢ Yint} := hO.preimage (Continuous.prodMk_right p)
  have hS : ∀ᶠ s in 𝓝 Y, (p, s) ∈ Ω ×ˢ Yint := hSo.mem_nhds hpO
  have hdiff : ∀ {f : P × ℝ → ℝ} {b : ℝ}, JC 15 (Ω ×ˢ Yint) f b → ∀ q ∈ Ω ×ˢ Yint, DifferentiableAt ℝ f q :=
    fun h q hq => (h.1.contDiffAt (hO.mem_nhds hq)).differentiableAt (by norm_num)
  have hdiffP : ∀ {f : P → ℝ} {b : ℝ}, JC 16 Ω f b → DifferentiableAt ℝ f p := fun h =>
    (h.1.contDiffAt (hΩ.mem_nhds hp)).differentiableAt (by norm_num)
  set g0s : ℝ → ℝ := fun s => fderiv ℝ U (p, s) (u, 0) * Ga p + U (p, s) * fderiv ℝ Ga p u with hg0s
  set g1s : ℝ → ℝ := fun s => fderiv ℝ U (p, s) (u, 0) * divInt G A (p, s) +
    U (p, s) * fderiv ℝ (divInt G A) (p, s) (u, 0) with hg1s
  set g2s : ℝ → ℝ := fun s => U (p, s) * (fderiv ℝ A p u * Ga p) with hg2s
  have hfun : (fun s : ℝ => fderiv ℝ (fun y => fderiv ℝ V y (v, 0)) (p, s) (u, 0)) =ᶠ[𝓝 Y] fun s => e *
      (((∑ k ∈ Finset.range 5, A p ^ k * (s ^ (4 - k) * g0s s)) + s ^ 5 * g1s s) +
        ∑ k ∈ Finset.range 5, ((k : ℝ) * A p ^ (k - 1)) * (s ^ (4 - k) * g2s s)) := by
    filter_upwards [hS] with s hs
    have hd := E_eq_dir (G := G) (Ev := fun y => fderiv ℝ V y (v, 0)) (U := U) (A := A) (Ga := Ga) (e := e) hΩ hs
      hEq (hdiff (hEv : JC 15 _ _ _) _ hs) (hdiff (hU : JC 15 _ U _) _ hs) (hdiff (hIG : JC 15 _ (divInt G A) _) _ hs)
      (hdiffP (hA : JC 16 _ A _)) (hdiffP (hGa : JC 16 _ Ga _)) u
    rw [hd]
    have e1 : ∀ X : ℝ, (∑ k ∈ Finset.range 5, A p ^ k * (s ^ (4 - k) * X)) =
        (∑ k ∈ Finset.range 5, s ^ (4 - k) * A p ^ k) * X := fun X => by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ => by ring
    have e2 : (∑ k ∈ Finset.range 5, ((k : ℝ) * A p ^ (k - 1)) * (s ^ (4 - k) * (U (p, s) * (fderiv ℝ A p u * Ga p)))) =
        (∑ k ∈ Finset.range 5, s ^ (4 - k) * ((k : ℝ) * A p ^ (k - 1) * fderiv ℝ A p u)) * (U (p, s) * Ga p) := by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ => by ring
    simp only [hg0s, hg1s, hg2s]
    rw [e1, e2]
    ring
  have hY4 : Y ≤ 4 := by have := hY.2; linarith
  have hA4 : A p ≤ 4 := by have := (hAY p hp).2; linarith
  have hW0 : 0 ≤ max Y (A p) := le_max_of_le_left hY0
  have hW4 : max Y (A p) ≤ 4 := max_le hY4 hA4
  set β' : ℝ := (Nat.factorial 14 : ℝ) * Φb^[9] β with hβ'
  have hβ'0 : 0 ≤ β' := by positivity
  have hn' : (n : WithTop ℕ∞) ≤ 14 := by exact_mod_cast hn
  have hc0 : ContDiffAt ℝ n g0s Y := hcd0.of_le (by exact_mod_cast hn)
  have hc1 : ContDiffAt ℝ n g1s Y := hcd1.of_le (by exact_mod_cast hn)
  have hc2 : ContDiffAt ℝ n g2s Y := hcd2.of_le (by exact_mod_cast hn)
  have hXc : ContDiffAt ℝ n (fun s : ℝ => (∑ k ∈ Finset.range 5, A p ^ k * (s ^ (4 - k) * g0s s)) + s ^ 5 * g1s s) Y :=
    (ContDiffAt.sum fun k _ => contDiffAt_const.mul (((contDiff_id.pow _).contDiffAt).mul hc0)).add
      (((contDiff_id.pow _).contDiffAt).mul hc1)
  have hpk : ∀ k ∈ Finset.range 5, ContDiffAt ℝ n
      (fun s : ℝ => ((k : ℝ) * A p ^ (k - 1)) * (s ^ (4 - k) * g2s s)) Y :=
    fun k _ => contDiffAt_const.mul (((contDiff_id.pow _).contDiffAt).mul hc2)
  have hZc : ContDiffAt ℝ n (fun s : ℝ => ∑ k ∈ Finset.range 5, ((k : ℝ) * A p ^ (k - 1)) * (s ^ (4 - k) * g2s s)) Y :=
    ContDiffAt.sum hpk
  have hX := weighted_E1D (n := n) (g0 := g0s) (g1 := g1s) (Y := Y) (A := A p) (β := β') hY0 hA0 hY4 hA4 hc0 hc1
    (fun k hk => hb0 k (hk.trans hn)) (fun k hk => hb1 k (hk.trans hn))
  set W := max Y (A p) with hW
  have hterm : ∀ k ∈ Finset.range 5, |iteratedDeriv n
      (fun s : ℝ => ((k : ℝ) * A p ^ (k - 1)) * (s ^ (4 - k) * g2s s)) Y| ≤
      4 * ((n + 1) * 2 ^ n * (6 * 4 ^ 3) * β' * W ^ (3 - n)) := by
    intro k hk
    have hk4 : k ≤ 4 := by have := Finset.mem_range.mp hk; omega
    have hnn : 0 ≤ (n + 1 : ℝ) * 2 ^ n * (6 * 4 ^ 3) * β' * W ^ (3 - n) := by positivity
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · have hz : (fun s : ℝ => (((0 : ℕ) : ℝ) * A p ^ (0 - 1)) * (s ^ (4 - 0) * g2s s)) = fun _ => (0 : ℝ) := by
        funext s; simp
      have hz' : iteratedDeriv n (fun _ : ℝ => (0 : ℝ)) Y = 0 := by simp
      rw [hz, hz', abs_zero]
      positivity
    · have hc : ContDiffAt ℝ n (fun s : ℝ => s ^ (4 - k) * g2s s) Y := ((contDiff_id.pow _).contDiffAt).mul hc2
      rw [iteratedDeriv_const_mul (f := fun s : ℝ => s ^ (4 - k) * g2s s) _ hc]
      have h := weighted_monomial (n := n) (a := 4 - k) (b := k - 1) (g := g2s) hY0 hA0 hY4 hA4 hc2
        (fun j hj => hb2 j (hj.trans hn))
      have hexp : 4 - k + (k - 1) = 3 := by omega
      rw [hexp] at h
      have hf : ((4 - k).factorial : ℝ) ≤ 6 := by
        have : (4 - k).factorial ≤ (3 : ℕ).factorial := Nat.factorial_le (by omega)
        have h6 : ((3 : ℕ).factorial : ℝ) = 6 := by simp [Nat.factorial]
        calc ((4 - k).factorial : ℝ) ≤ ((3 : ℕ).factorial : ℝ) := by exact_mod_cast this
          _ = 6 := h6
      have hk' : (k : ℝ) ≤ 4 := by exact_mod_cast hk4
      have e : |((k : ℝ) * A p ^ (k - 1)) * iteratedDeriv n (fun s : ℝ => s ^ (4 - k) * g2s s) Y| =
          (k : ℝ) * |iteratedDeriv n (fun s : ℝ => s ^ (4 - k) * g2s s) Y * A p ^ (k - 1)| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ k), abs_of_nonneg (pow_nonneg hA0 _)]
        ring
      rw [e]
      have h2 : (n + 1 : ℝ) * 2 ^ n * (((4 - k).factorial : ℝ) * 4 ^ 3) * β' * W ^ (3 - n) ≤
          (n + 1 : ℝ) * 2 ^ n * (6 * 4 ^ 3) * β' * W ^ (3 - n) := by gcongr
      calc (k : ℝ) * _ ≤ 4 * ((n + 1 : ℝ) * 2 ^ n * (((4 - k).factorial : ℝ) * 4 ^ 3) * β' * W ^ (3 - n)) :=
            mul_le_mul hk' (by simpa using h) (abs_nonneg _) (by norm_num)
        _ ≤ _ := by gcongr
  have hZ : |iteratedDeriv n (fun s : ℝ => ∑ k ∈ Finset.range 5, ((k : ℝ) * A p ^ (k - 1)) * (s ^ (4 - k) * g2s s)) Y| ≤
      5 * (4 * ((n + 1) * 2 ^ n * (6 * 4 ^ 3) * β' * W ^ (3 - n))) := by
    rw [iteratedDeriv_fun_sum hpk]
    calc _ ≤ ∑ k ∈ Finset.range 5, |iteratedDeriv n
          (fun s : ℝ => ((k : ℝ) * A p ^ (k - 1)) * (s ^ (4 - k) * g2s s)) Y| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range 5, 4 * ((n + 1) * 2 ^ n * (6 * 4 ^ 3) * β' * W ^ (3 - n)) :=
          Finset.sum_le_sum hterm
      _ = _ := by simp
  have hW43 : W ^ (4 - n) ≤ 4 * W ^ (3 - n) := by
    by_cases hn3 : n ≤ 3
    · have : 4 - n = (3 - n) + 1 := by omega
      rw [this, pow_succ]
      nlinarith [pow_nonneg hW0 (3 - n)]
    · have h1 : 4 - n = 0 := by omega
      have h2 : 3 - n = 0 := by omega
      rw [h1, h2]; norm_num
  rw [hfun.iteratedDeriv_eq n, iteratedDeriv_const_mul_field, abs_mul, iteratedDeriv_fun_add hXc hZc]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg e)
  have hnn : 0 ≤ (n + 1 : ℝ) * 2 ^ n * β' * W ^ (3 - n) := by positivity
  calc _ ≤ |iteratedDeriv n (fun s : ℝ => (∑ k ∈ Finset.range 5, A p ^ k * (s ^ (4 - k) * g0s s)) + s ^ 5 * g1s s) Y| +
        |iteratedDeriv n (fun s : ℝ => ∑ k ∈ Finset.range 5, ((k : ℝ) * A p ^ (k - 1)) * (s ^ (4 - k) * g2s s)) Y| :=
        abs_add_le _ _
    _ ≤ (n + 1) * 2 ^ n * 1000000 * β' * (4 * W ^ (3 - n)) + 5 * (4 * ((n + 1) * 2 ^ n * (6 * 4 ^ 3) * β' * W ^ (3 - n))) := by
        gcongr
        exact hX.trans (by gcongr)
    _ ≤ _ := by nlinarith [hnn]

/-- Symmetry of the mixed second derivative in two parameter directions. -/
lemma fderiv_dir_symm {V : P × ℝ → ℝ} {q : P × ℝ} (hV : ContDiffAt ℝ 2 V q) (u v : P) :
    fderiv ℝ (fun y => fderiv ℝ V y (u, 0)) q (v, 0) = fderiv ℝ (fun y => fderiv ℝ V y (v, 0)) q (u, 0) := by
  have hD : DifferentiableAt ℝ (fderiv ℝ V) q :=
    (hV.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have e1 : ∀ (w : P) (x : P × ℝ), fderiv ℝ (fun y => fderiv ℝ V y (w, 0)) q x =
      fderiv ℝ (fderiv ℝ V) q x (w, 0) := by
    intro w x
    have h := (ContinuousLinearMap.apply ℝ ℝ ((w : P), (0 : ℝ))).hasFDerivAt.comp _ hD.hasFDerivAt
    rw [show (fun y => fderiv ℝ V y ((w : P), (0 : ℝ))) =
      (⇑(ContinuousLinearMap.apply ℝ ℝ ((w : P), (0 : ℝ)))) ∘ fderiv ℝ V from rfl, h.fderiv]
    rfl
  have hsymm := (ContDiffAt.isSymmSndFDerivAt hV (by simp [minSmoothness_of_isRCLikeNormedField])) (v, 0) (u, 0)
  rw [e1 u, e1 v]
  exact hsymm

/-- **`(fct:V-diff-jets)`, second line, one parameter direction `u` (`‖u‖ ≤ 1`)**: for `n ≤ 13`,
`|∂_Y^n ∂_u (V(p₀+v) - V(p₀))| ≤ C_n |e| max(Y, A_max)^{max(0, 3-n)}`. -/
theorem V_diff_jets_u_Y {Ω : Set P} (hΩ : IsOpen Ω) {β : ℝ} (hβ : 4 ≤ β) {V θ : P × ℝ → ℝ} {A : P → ℝ} (v u : P)
    (hu : ‖u‖ ≤ 1) (e : ℝ)
    (hV : JCΦ 16 (Ω ×ˢ Yint) V β 0) (hA : JCΦ 16 Ω A β 0) (hθ : JCΦ 16 (Ω ×ˢ Ioo (-1 : ℝ) 6) θ β 0)
    (hAY : ∀ p ∈ Ω, A p ∈ Yint) (hz : ∀ q ∈ Ω ×ˢ Yint, q.2 * V q ^ 2 ∈ Ioo (-1 : ℝ) 6)
    (hode : ∀ q ∈ Ω ×ˢ Yint, (A q.1 - q.2) * fderiv ℝ V q (v, 0) =
      e * (V q + 2 * q.2 * fderiv ℝ V q (0, 1)) *
        (A q.1 ^ 5 * V (q.1, A q.1) ^ 11 * θ (q.1, A q.1 * V (q.1, A q.1) ^ 2) -
          q.2 ^ 5 * V q ^ 11 * θ (q.1, q.2 * V q ^ 2)))
    {p0 : P} (hseg : ∀ t ∈ Icc (0 : ℝ) 1, p0 + t • v ∈ Ω) (hA0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ A (p0 + t • v)) {Amax : ℝ}
    (hAm : ∀ t ∈ Icc (0 : ℝ) 1, A (p0 + t • v) ≤ Amax) {Y : ℝ} (hY : Y ∈ Yint) (hY0 : 0 ≤ Y) {n : ℕ} (hn : n ≤ 13) :
    |iteratedDeriv n (fun s : ℝ => fderiv ℝ V (p0 + v, s) (u, 0)) Y -
        iteratedDeriv n (fun s : ℝ => fderiv ℝ V (p0, s) (u, 0)) Y| ≤
      |e| * ((n + 1) * 2 ^ n * 10000000 * ((Nat.factorial 14 : ℝ) * Φb^[9] β) * max Y Amax ^ (3 - n)) := by
  have hO : IsOpen (Ω ×ˢ Yint) := hΩ.prod isOpen_Ioo
  have hV16 : ContDiffOn ℝ 16 V (Ω ×ˢ Yint) := hV.1
  have hf2 : ContDiffOn ℝ ((n : WithTop ℕ∞) + 2) (fun y => fderiv ℝ V y (u, 0)) (Ω ×ˢ Yint) := by
    have := (hV16.fderiv_of_isOpen hO (m := 15) (by norm_num)).clm_apply (contDiffOn_const (c := (u, (0 : ℝ))))
    exact this.of_le (by norm_cast; omega)
  set g : ℝ → ℝ := fun t => iteratedDeriv n (fun s : ℝ => fderiv ℝ V (p0 + t • v, s) (u, 0)) Y with hg
  set g' : ℝ → ℝ := fun t => iteratedDeriv n (fun s : ℝ =>
    fderiv ℝ (fun y => fderiv ℝ V y (v, 0)) (p0 + t • v, s) (u, 0)) Y with hg'
  have hder : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt g (g' t) (Icc (0 : ℝ) 1) t := by
    intro t ht
    have h := hasDerivAt_iteratedDeriv_path hO p0 v Y n (fun y => fderiv ℝ V y (u, 0)) hf2 t ⟨hseg t ht, hY⟩
    have hmem : ∀ s, (p0 + t • v, s) ∈ Ω ×ˢ Yint → True := fun _ _ => trivial
    have hc : Continuous fun s : ℝ => (p0 + t • v, s) := by fun_prop
    have hev : ∀ᶠ s in 𝓝 Y, (p0 + t • v, s) ∈ Ω ×ˢ Yint :=
      hc.continuousAt.eventually (hO.mem_nhds ⟨hseg t ht, hY⟩)
    have hsw : iteratedDeriv n (fun s => fderiv ℝ (fun y => fderiv ℝ V y (u, 0)) (p0 + t • v, s) (v, 0)) Y =
        g' t := by
      refine Filter.EventuallyEq.iteratedDeriv_eq n ?_
      filter_upwards [hev] with s hs
      exact fderiv_dir_symm ((hV16.contDiffAt (hO.mem_nhds hs)).of_le (by norm_num)) u v
    rw [hsw] at h
    exact h.hasDerivWithinAt
  have hbd : ∀ t ∈ Icc (0 : ℝ) 1, ‖g' t‖ ≤
      |e| * ((n + 1) * 2 ^ n * 10000000 * ((Nat.factorial 14 : ℝ) * Φb^[9] β) * max Y Amax ^ (3 - n)) := by
    intro t ht
    have h := E_jets_u hΩ hβ v u hu e hV hA hθ hAY hz hode (hseg t ht) hY hY0 (hA0 t ht) (n := n) (by omega)
    rw [Real.norm_eq_abs]
    refine h.trans ?_
    have hΦ : 0 ≤ Φb^[9] β := by
      have := Φb_iter_ge 9 β
      linarith
    have hmx : max Y (A (p0 + t • v)) ≤ max Y Amax := max_le_max le_rfl (hAm t ht)
    have h0 : 0 ≤ max Y (A (p0 + t • v)) := le_trans hY0 (le_max_left _ _)
    gcongr
  have := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le hder hbd (left_mem_Icc.mpr zero_le_one)
    (right_mem_Icc.mpr zero_le_one)
  simpa [hg, one_smul, zero_smul, add_zero] using this

/-- info: 'FormalResearch.SignUncertainty.E_eq_dir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms E_eq_dir

/-- info: 'FormalResearch.SignUncertainty.E_jets_u' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms E_jets_u

/-- info: 'FormalResearch.SignUncertainty.V_diff_jets_u_Y' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms V_diff_jets_u_Y

namespace ChartSetup
variable (S : ChartSetup P)

/-- `(fct:V-diff-jets)`, second line, for the chart (one parameter direction `u`, `‖u‖ ≤ 1`, `n ≤ 13`). -/
theorem V_diff_jets_u {β : ℝ} (hβ : 4 ≤ β) (v u : P) (hu : ‖u‖ ≤ 1) (θ : P × ℝ → ℝ) (e : ℝ)
    (hψ : ∀ q ∈ S.Ω ×ˢ Ioo (-1 : ℝ) 6,
      fderiv ℝ (fun q : P × ℝ => S.ℓ q.1 - Real.pi ^ 2 / 36 * q.2 + S.r q) q (v, 0) = e * q.2 ^ 5 * θ q)
    (hθ : JCΦ 16 (S.Ω ×ˢ Ioo (-1 : ℝ) 6) θ (Φb^[3] β) 0)
    {p0 : P} (hseg : ∀ t ∈ Icc (0 : ℝ) 1, p0 + t • v ∈ S.Ω) (hA0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ S.A (p0 + t • v)) {Amax : ℝ}
    (hAm : ∀ t ∈ Icc (0 : ℝ) 1, S.A (p0 + t • v) ≤ Amax) {Y : ℝ} (hY : Y ∈ Yint) (hY0 : 0 ≤ Y) {n : ℕ} (hn : n ≤ 13) :
    |iteratedDeriv n (fun s : ℝ => fderiv ℝ S.V (p0 + v, s) (u, 0)) Y -
        iteratedDeriv n (fun s : ℝ => fderiv ℝ S.V (p0, s) (u, 0)) Y| ≤
      |e| * ((n + 1) * 2 ^ n * 10000000 * ((Nat.factorial 14 : ℝ) * Φb^[9] (Φb^[3] β)) * max Y Amax ^ (3 - n)) := by
  have hβ3 : 4 ≤ Φb^[3] β := le_trans hβ (Φb_iter_ge 3 β)
  have hV : JCΦ 16 (S.Ω ×ˢ Yint) S.V (Φb^[3] β) 0 := by
    have := (S.V_jc hβ).mono_m (show 1 ≤ 3 by norm_num)
    simpa [JCΦ] using this
  have hA : JCΦ 16 S.Ω S.A (Φb^[3] β) 0 := by simpa [JCΦ] using S.A_jc hβ
  exact V_diff_jets_u_Y S.hΩ hβ3 v u hu e hV hA hθ (fun p hp => S.A_mem hp) (fun q hq => S.hz hq) (S.hode v θ e hψ)
    hseg hA0 hAm hY hY0 hn

end ChartSetup

/-- info: 'FormalResearch.SignUncertainty.ChartSetup.V_diff_jets_u' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChartSetup.V_diff_jets_u

end EJetsU
end FormalResearch.SignUncertainty
