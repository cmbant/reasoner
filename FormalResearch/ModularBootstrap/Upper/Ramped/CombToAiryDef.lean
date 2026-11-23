module

public import FormalResearch.ModularBootstrap.Upper.Ramped.LangerChart
public import FormalResearch.ModularBootstrap.Upper.Ramped.CombToAiryNearSum
public import FormalResearch.ModularBootstrap.Upper.Design.PerturbP
public import FormalResearch.ModularBootstrap.Upper.Comb.Riesz

/-!
# Designs of Proposition 1.2(2): the comb `B_D`, its sites in the Langer chart, and its real-axis modulus

`remainder.tex`, Proposition 1.2 (`rem:P1.2`), part (2).  A *design* consists of sites `σ_k ≥ 0` (`k ≥ 1`)
with `|σ_k - Φ_k| ≤ C_sh k^{-4/3}` and separation `σ_{k+1} - σ_k ≥ c_sep k^{-1/3}` (`CombDesignHyp`) and heights
`0 ≤ η_k ≤ 1/4` (`k ≥ 2`).  The comb `B_D` (`combBD`) has a simple zero at `χ'_1 = τ^{-1}(λ σ_1)` and the pairs
`χ'_k ± i ε'_k`, `χ'_k = τ^{-1}(λ σ_k)`, `ε'_k = η_k ℓ_k` (`k ≥ 2`).

* `siteX`, `widthE`, `combBD`, `CombDesignHyp`; `CombDesignHyp.sep_pair` (separation of all pairs);
* `langerTau_siteX`, `xiStar_le_siteX`, `siteX_sub_chi` (`|χ'_k - χ_k| ≤ λ|σ_k - Φ_k|/c_τ`);
* `siteGap_le_unif`: `ℓ_k ≤ C λ`;
* `combBD_norm_eq`: the real-axis modulus `log ‖B_D(x)‖ = f_x(χ'_1) + ∑_{k ≥ 2} log q'_k` (`cmb:K1`(a),(b)).
-/

@[expose] public section

open Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.ModularBootstrap.Upper.Comb FormalResearch.ModularBootstrap.Upper.Design

/-- The sites `χ'_k = τ^{-1}(λ σ_k)` of a design. -/
noncomputable def siteX (c' : ℝ) (σ : ℕ → ℝ) (k : ℕ) : ℝ := langerTauInv (lambdaComb c' * σ k)

/-- The widths `ε'_k = η_k ℓ_k`. -/
noncomputable def widthE (c' : ℝ) (η : ℕ → ℝ) (k : ℕ) : ℝ := η k * siteGap c' k

/-- The comb `B_D(b) = T_{χ'_1}(b) ∏_{k ≥ 2} T_{χ'_k + iε'_k}(b) T_{χ'_k - iε'_k}(b)`. -/
noncomputable def combBD (c' : ℝ) (σ η : ℕ → ℝ) (b : ℂ) : ℂ :=
  blaschkeT (siteX c' σ 1 : ℂ) b *
    ∏' m : ℕ, pairT (siteX c' σ (m + 2)) (widthE c' η (m + 2)) b

/-- The hypotheses on a design (sites `σ_k` of `rem:P1.2`(2), heights `η_k`): `σ_k ≥ 0`,
`|σ_k - Φ_k| ≤ C_sh k^{-4/3}`, `σ_{k+1} - σ_k ≥ c_sep k^{-1/3}`, `0 ≤ η_k ≤ 1/4` for `k ≥ 2`. -/
structure CombDesignHyp (Csh csep : ℝ) (σ η : ℕ → ℝ) : Prop where
  nonneg : ∀ k : ℕ, 1 ≤ k → 0 ≤ σ k
  near : ∀ k : ℕ, 1 ≤ k → |σ k - phiQuantile (k : ℝ)| ≤ Csh * (k : ℝ) ^ (-(4 / 3 : ℝ))
  sep : ∀ k : ℕ, 1 ≤ k → csep * (k : ℝ) ^ (-(1 / 3 : ℝ)) ≤ σ (k + 1) - σ k
  height : ∀ k : ℕ, 2 ≤ k → 0 ≤ η k ∧ η k ≤ 1 / 4

/-- Separation of all pairs of sites. -/
lemma CombDesignHyp.sep_pair {Csh csep : ℝ} {σ η : ℕ → ℝ} (h : CombDesignHyp Csh csep σ η)
    (hc : 0 < csep) :
    ∀ j k : ℕ, 1 ≤ j → j < k → csep * (((k : ℝ) - j) * cr k) ≤ σ k - σ j := by
  intro j k hj hjk
  induction k, hjk using Nat.le_induction with
  | base =>
    have h1 := h.sep j hj
    have hcc : cr (j + 1) ≤ cr j := cr_anti hj (by omega)
    have h2 : csep * cr (j + 1) ≤ csep * cr j := by gcongr
    have h3 : cr j = (j : ℝ) ^ (-(1 / 3 : ℝ)) := rfl
    push_cast
    nlinarith
  | succ k hk ih =>
    have h1 := h.sep k (by omega)
    have hcr : cr (k + 1) ≤ cr k := cr_anti (by omega) (by omega)
    have h3 : cr k = (k : ℝ) ^ (-(1 / 3 : ℝ)) := rfl
    have hk' : (j : ℝ) + 1 ≤ k := by exact_mod_cast hk
    have hcp := cr_pos (by omega : 1 ≤ k + 1)
    push_cast
    have h4 : csep * (((k : ℝ) + 1 - j) * cr (k + 1)) ≤ csep * (((k : ℝ) - j) * cr k) + csep * cr k := by
      have : ((k : ℝ) + 1 - j) * cr (k + 1) ≤ ((k : ℝ) - j) * cr k + cr k := by
        have : ((k : ℝ) + 1 - j) * cr (k + 1) ≤ ((k : ℝ) + 1 - j) * cr k := by
          apply mul_le_mul_of_nonneg_left hcr; linarith
        nlinarith
      nlinarith
    nlinarith

lemma lamPos {c' : ℝ} (hc' : 0 < c') : 0 < lambdaComb c' := by
  unfold lambdaComb; exact Real.rpow_pos_of_pos (mul_pos kTip_pos hc') _

lemma langerTau_siteX {c' : ℝ} (hc' : 0 < c') {σ : ℕ → ℝ} {k : ℕ} (h : 0 ≤ σ k) :
    langerTau (siteX c' σ k) = lambdaComb c' * σ k :=
  langerTau_langerTauInv (mul_nonneg (lamPos hc').le h)

lemma xiStar_le_siteX {c' : ℝ} (hc' : 0 < c') {σ : ℕ → ℝ} {k : ℕ} (h : 0 ≤ σ k) :
    xiStar ≤ siteX c' σ k :=
  (langerTauInv_spec (mul_nonneg (lamPos hc').le h)).1

/-- `|χ'_k - χ_k| ≤ λ |σ_k - Φ_k| / c_τ`, with `c_τ` a lower bound of `τ'` on `[ξ_*/2, ∞)`. -/
theorem siteX_sub_chi :
    ∃ cτ : ℝ, 0 < cτ ∧ (∀ x : ℝ, xiStar / 2 ≤ x → cτ ≤ deriv langerTau x) ∧
      ∀ {c' : ℝ}, 0 < c' → ∀ (σ : ℕ → ℝ) (k : ℕ), 1 ≤ k → 0 ≤ σ k →
        |siteX c' σ k - chiQuantile c' (k : ℝ)| ≤ lambdaComb c' * |σ k - phiQuantile (k : ℝ)| / cτ := by
  obtain ⟨cτ, hcτ, hd⟩ := langerTau_deriv_ge_const
  refine ⟨cτ, hcτ, hd, fun {c'} hc' σ k hk hσ => ?_⟩
  have hk14 : (1 / 4 : ℝ) ≤ k := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hΦ : 0 ≤ phiQuantile (k : ℝ) := by
    unfold phiQuantile; exact Real.rpow_nonneg (by linarith) _
  have hlam := (lamPos hc').le
  have e1 : chiQuantile c' (k : ℝ) = langerTauInv (lambdaComb c' * phiQuantile (k : ℝ)) :=
    chiQuantile_eq_langerTauInv hc' hk14
  have hy := (langerTauInv_spec (mul_nonneg hlam hσ)).1
  have hy' := (langerTauInv_spec (mul_nonneg hlam hΦ)).1
  have t1 := langerTau_langerTauInv (mul_nonneg hlam hσ)
  have t2 := langerTau_langerTauInv (mul_nonneg hlam hΦ)
  have hxs : 0 < xiStar / 2 := by have := xiStar_pos; positivity
  have hmain : ∀ y y' : ℝ, xiStar ≤ y → xiStar ≤ y' → y ≤ y' →
      cτ * (y' - y) ≤ langerTau y' - langerTau y := fun y y' h1 _ h3 =>
    langerTau_sub_ge hxs hd (by linarith [xiStar_pos]) h3
  unfold siteX
  rw [e1]
  set y := langerTauInv (lambdaComb c' * σ k)
  set y' := langerTauInv (lambdaComb c' * phiQuantile (k : ℝ))
  have habs : |lambdaComb c' * σ k - lambdaComb c' * phiQuantile (k : ℝ)| =
      lambdaComb c' * |σ k - phiQuantile (k : ℝ)| := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hlam]
  rw [le_div_iff₀ hcτ, mul_comm]
  rcases le_total y y' with h | h
  · have := hmain y y' hy hy' h
    rw [t1, t2] at this
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    have : cτ * (y' - y) ≤ |lambdaComb c' * σ k - lambdaComb c' * phiQuantile (k : ℝ)| := by
      rw [abs_sub_comm]
      exact this.trans (le_abs_self _)
    rw [habs] at this
    linarith
  · have := hmain y' y hy' hy h
    rw [t1, t2] at this
    rw [abs_of_nonneg (by linarith)]
    have : cτ * (y - y') ≤ |lambdaComb c' * σ k - lambdaComb c' * phiQuantile (k : ℝ)| :=
      this.trans (le_abs_self _)
    rw [habs] at this
    linarith

/-- `ℓ_k ≤ C λ` and `ℓ_k ≤ 1/2` for every `k ≥ 1`, for `c'` large. -/
theorem siteGap_le_unif :
    ∃ Cg : ℝ, 0 < Cg ∧ ∀ᶠ c' in atTop, ∀ k : ℕ, 1 ≤ k →
      siteGap c' k ≤ Cg * lambdaComb c' ∧ siteGap c' k ≤ 1 / 2 := by
  obtain ⟨C, hC, h⟩ := siteGap_eventually_le
  refine ⟨C, hC, ?_⟩
  filter_upwards [h] with c' ⟨h1, h2, h3, h4⟩ k hk
  exact ⟨(h1 k hk).trans (h2.trans h3), (h1 k hk).trans h4⟩

lemma widthE_nonneg {c' : ℝ} (hc' : 0 < c') {η : ℕ → ℝ} {k : ℕ} (hk : 2 ≤ k) (h : 0 ≤ η k) :
    0 ≤ widthE c' η k := mul_nonneg h (siteGap_nonneg hc' (by omega))

lemma summable_exp_siteX {Csh csep : ℝ} {c' : ℝ} (hc' : 0 < c') {σ η : ℕ → ℝ}
    (h : CombDesignHyp Csh csep σ η) :
    Summable fun m : ℕ => Real.exp (-π * siteX c' σ (m + 2)) := by
  obtain ⟨cτ, hcτ, _, hX⟩ := siteX_sub_chi
  have hsum := summable_exp_neg_pi_chiQuantile hc' 1
  have hsum' := hsum.mul_left (Real.exp (π * (lambdaComb c' * (|Csh| / cτ))))
  refine Summable.of_nonneg_of_le (fun m => (Real.exp_pos _).le) (fun m => ?_) hsum'
  have hk : 1 ≤ m + 2 := by omega
  have h1 := hX hc' σ (m + 2) hk (h.nonneg _ hk)
  have h2 := h.near (m + 2) hk
  have hk0 : (1 : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by exact_mod_cast hk
  have h3 : ((m + 2 : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hk0 (by norm_num)
  have h4 : |σ (m + 2) - phiQuantile ((m + 2 : ℕ) : ℝ)| ≤ |Csh| := by
    refine h2.trans ?_
    calc Csh * ((m + 2 : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) ≤ |Csh| * ((m + 2 : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) := by
          gcongr; exact le_abs_self _
      _ ≤ |Csh| * 1 := by gcongr
      _ = |Csh| := mul_one _
  have h5 : |siteX c' σ (m + 2) - chiQuantile c' ((m + 2 : ℕ) : ℝ)| ≤ lambdaComb c' * (|Csh| / cτ) := by
    refine h1.trans ?_
    rw [mul_div_assoc]
    have := (lamPos hc').le
    gcongr
  have h6 : chiQuantile c' ((m + 2 : ℕ) : ℝ) - lambdaComb c' * (|Csh| / cτ) ≤ siteX c' σ (m + 2) := by
    have := (abs_le.mp h5).1; linarith
  have hidx : ((1 + 1 + m : ℕ) : ℝ) = ((m + 2 : ℕ) : ℝ) := by push_cast; ring
  show Real.exp (-π * siteX c' σ (m + 2)) ≤ Real.exp (π * (lambdaComb c' * (|Csh| / cτ))) *
    Real.exp (-π * chiQuantile c' ((1 + 1 + m : ℕ) : ℝ))
  rw [hidx, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [Real.pi_pos]

/-- `‖pairT − 1‖` is summable at every `b` (the locally uniform product of `comb_pairProd_*`, pointwise). -/
lemma summable_norm_pairT_sub_one (χ ε : ℕ → ℝ) (hχ0 : ∀ m, 0 ≤ χ m) (hε : ∀ m, |ε m| ≤ 1 / 8)
    (hsum : Summable fun m => Real.exp (-π * χ m)) (b : ℂ) :
    Summable fun m => ‖pairT (χ m) (ε m) b - 1‖ := by
  set R := |b.re| with hR
  have hR0 : 0 ≤ R := abs_nonneg _
  have hev : ∀ᶠ m in atTop, χ m ≥ R + 2 := by
    have h0 := hsum.tendsto_atTop_zero
    have hpos : (0 : ℝ) < Real.exp (-π * (R + 2)) := Real.exp_pos _
    filter_upwards [h0.eventually (gt_mem_nhds hpos)] with m hm
    have := Real.exp_lt_exp.mp hm
    nlinarith [Real.pi_pos]
  have hg : Summable fun m => 32 * Real.exp (π * R) * Real.exp (-π * χ m) := hsum.mul_left _
  refine Summable.of_norm_bounded_eventually hg ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hev] with m hm
  have := blaschkeT_pair_sub_one_le (hε m) (hχ0 m) hR0 le_rfl hm
  simpa [pairT, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using this

/-- The real-axis pair modulus `q'_k(x) = |T_{χ'_k + iε'_k}(x) T_{χ'_k - iε'_k}(x)|`. -/
noncomputable def qPair (c' : ℝ) (σ η : ℕ → ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  blaschkePairQ (siteX c' σ k) (widthE c' η k) x

/-- `K1(a),(b)` for `B_D` on the real axis (`rem:P1.2`(2), (F3)): the pair moduli have summable logarithms
and are multipliable, and `‖B_D(x)‖ = ‖T_{χ'_1}(x)‖ ∏_{k ≥ 2} q'_k(x)`. -/
theorem combBD_real {Csh csep : ℝ} {c' : ℝ} (hc' : 0 < c') {σ η : ℕ → ℝ}
    (h : CombDesignHyp Csh csep σ η) (hw : ∀ k : ℕ, 2 ≤ k → |widthE c' η k| ≤ 1 / 8) (x : ℝ) :
    Summable (fun m : ℕ => Real.log (qPair c' σ η (m + 2) x)) ∧
    Multipliable (fun m : ℕ => qPair c' σ η (m + 2) x) ∧
    ‖combBD c' σ η x‖ = ‖blaschkeT (siteX c' σ 1 : ℂ) (x : ℂ)‖ *
        ∏' m : ℕ, qPair c' σ η (m + 2) x := by
  have hχ0 : ∀ m : ℕ, 0 ≤ siteX c' σ (m + 2) := fun m =>
    (xiStar_pos.le).trans (xiStar_le_siteX hc' (h.nonneg _ (by omega)))
  have hε : ∀ m : ℕ, |widthE c' η (m + 2)| ≤ 1 / 8 := fun m => hw _ (by omega)
  have hsum := summable_exp_siteX hc' h
  have hlog : Summable fun m : ℕ => Real.log (qPair c' σ η (m + 2) x) := by
    have := (summable_norm_pairT_sub_one (fun m => siteX c' σ (m + 2)) (fun m => widthE c' η (m + 2))
      hχ0 hε hsum (x : ℂ)).summable_log_norm_one_add
    refine this.congr fun m => ?_
    simp only [add_sub_cancel]
    rfl
  have hprod := (comb_pairProd_hasProdLocallyUniformlyOn (fun m => siteX c' σ (m + 2))
    (fun m => widthE c' η (m + 2)) hχ0 hε hsum).hasProd (show (x : ℂ) ∈ {b : ℂ | |b.im| < 7 / 8} by
      simp)
  have hnorm : HasProd (fun m : ℕ => qPair c' σ η (m + 2) x)
      ‖∏' m : ℕ, pairT (siteX c' σ (m + 2)) (widthE c' η (m + 2)) (x : ℂ)‖ := hprod.norm
  refine ⟨hlog, hnorm.multipliable, ?_⟩
  have hB : ‖combBD c' σ η x‖ = ‖blaschkeT (siteX c' σ 1 : ℂ) (x : ℂ)‖ *
      ‖∏' m : ℕ, pairT (siteX c' σ (m + 2)) (widthE c' η (m + 2)) (x : ℂ)‖ := by
    unfold combBD; rw [norm_mul]
  rw [hB, hnorm.tprod_eq]

/-- Logarithm of the real-axis modulus: if `T_{χ'_1}(x)` and all `q'_k(x)` are non-zero,
`log ‖B_D(x)‖ = f_x(χ'_1) + ∑_{k ≥ 2} log q'_k(x)`. -/
theorem log_norm_combBD {Csh csep : ℝ} {c' : ℝ} (hc' : 0 < c') {σ η : ℕ → ℝ}
    (h : CombDesignHyp Csh csep σ η) (hw : ∀ k : ℕ, 2 ≤ k → |widthE c' η k| ≤ 1 / 8) (x : ℝ)
    (hT : ‖blaschkeT (siteX c' σ 1 : ℂ) (x : ℂ)‖ ≠ 0) (hq : ∀ m : ℕ, 0 < qPair c' σ η (m + 2) x) :
    Real.log ‖combBD c' σ η x‖ =
      realLogT x (siteX c' σ 1) + ∑' m : ℕ, Real.log (qPair c' σ η (m + 2) x) := by
  obtain ⟨hlog, _, hB⟩ := combBD_real hc' h hw x
  have hTp : 0 < ‖blaschkeT (siteX c' σ 1 : ℂ) (x : ℂ)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hT)
  have hexp := Real.rexp_tsum_eq_tprod hq hlog
  rw [hB, ← hexp, Real.log_mul hT (Real.exp_pos _).ne', Real.log_exp]
  rfl

end FormalResearch.ModularBootstrap.Upper.Ramped
