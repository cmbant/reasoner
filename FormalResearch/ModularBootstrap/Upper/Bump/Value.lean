module

public import FormalResearch.ModularBootstrap.Upper.Bump.Geometry
public import FormalResearch.ModularBootstrap.Upper.Bump.PairFactor
public import FormalResearch.ModularBootstrap.Upper.Design.DesignCombProps

/-!
# The bumped comb is `R_bump` times the base comb on the real axis (`fw:e3.3`, definition of `R_bump`)

Source: `CFT/modular_bootstrap/paper/upper_transfer.tex`, "Define `R_bump(x) = h_0^{(p)}(x)/h_0(x)`".

* `combReal`, `designComb_eq_combReal`: for real `x`, `B_D^{(f)}(x)` of a finite modification is the real number
  `combReal` (a signed product of real factors; no condition on the position of `x` relative to the sites).
* `combTail_split_re`: the real tail splits off the reference pairs `N₀ < k ≤ N`.
* `bumpFactor` is `R_bump`: the product over `N₀ < k ≤ N` of the ratio of the bumped to the unbumped pair
  modulus (`1` outside the block).
* `bumped_value`: for every real `x` the bumped comb equals `bumpFactor · base`; the product form avoids dividing
  by the zero of the base comb (the shared simple zero of `fw:e3.3`).

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Bump

open FormalResearch.ModularBootstrap.Upper.Comb FormalResearch.ModularBootstrap.Upper.Design
  FormalResearch.ModularBootstrap.Upper.Positivity
open scoped Classical

/-! ### 1. The real value of a finite modification -/

/-- The real value of `B_D^{(f)}(x)` (`designComb c' f N η₀ σ ε`) at a real point. -/
noncomputable def combReal (c' : ℝ) (f N : ℕ) (η₀ : ℝ) (σ ε : ℕ → ℝ) (x : ℝ) : ℝ :=
  (Real.tanh (π * (x - designSite c' σ f) / 2) * Real.tanh (π * (x + designSite c' σ f) / 2)) *
    (∏ i ∈ Finset.range (N - f), blaschkePairQ (designSite c' σ (f + 1 + i)) (ε (f + 1 + i)) x) *
    (combTail c' N η₀ (x : ℂ)).re

/-- For real `x`, `designComb` is the real number `combReal`. -/
theorem designComb_eq_combReal {c' η₀ x : ℝ} (hc' : 0 < c') (hη₀0 : 0 ≤ η₀) (hη₀1 : η₀ ≤ 1 / 4)
    (hgap : siteGap c' 1 ≤ 1 / 2) (f N : ℕ) (σ ε : ℕ → ℝ) :
    designComb c' f N η₀ σ ε (x : ℂ) = ((combReal c' f N η₀ σ ε x : ℝ) : ℂ) := by
  obtain ⟨him, _⟩ := combTail_real_nonneg (x := x) hc' hη₀0 hη₀1 hgap N
  set t : ℝ := (combTail c' N η₀ (x : ℂ)).re with ht
  have htail : combTail c' N η₀ (x : ℂ) = (t : ℂ) := by
    apply Complex.ext
    · simp [ht]
    · simp [him]
  unfold designComb combReal
  rw [htail, blaschkeT_ofReal_eq]
  have hprod : (∏ i ∈ Finset.range (N - f),
      pairT (designSite c' σ (f + 1 + i)) (ε (f + 1 + i)) (x : ℂ)) =
      ((∏ i ∈ Finset.range (N - f),
        blaschkePairQ (designSite c' σ (f + 1 + i)) (ε (f + 1 + i)) x : ℝ) : ℂ) := by
    rw [Complex.ofReal_prod]
    exact Finset.prod_congr rfl fun i _ => pairT_ofReal _ _ _
  rw [hprod, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- The tail splits off the reference pairs `N₀ < k ≤ N` (`|Im b| < 7/8`), with a threshold independent of the
cuts. -/
theorem combTail_split {η₀ : ℝ} (hη₀0 : 0 ≤ η₀) (hη₀1 : η₀ ≤ 1 / 4) :
    ∀ᶠ c' in atTop, ∀ (N₀ N : ℕ), N₀ ≤ N → ∀ {b : ℂ}, |b.im| < 7 / 8 →
      combTail c' N₀ η₀ b =
        (∏ i ∈ Finset.range (N - N₀),
          pairT (chiQuantile c' ((N₀ + 1 + i : ℕ) : ℝ)) (η₀ * siteGap c' (N₀ + 1 + i)) b) *
        combTail c' N η₀ b := by
  filter_upwards [combTail_K1a_unif hη₀0 hη₀1] with c' h N₀ N hN b hb
  have hmul0 := (h N₀).2.2.2 hb
  set g : ℕ → ℂ := fun m =>
    pairT (chiQuantile c' ((N₀ + 1 + m : ℕ) : ℝ)) (η₀ * siteGap c' (N₀ + 1 + m)) b with hg
  have hshift : (fun n : ℕ => g (n + (N - N₀))) = fun n : ℕ =>
      pairT (chiQuantile c' ((N + 1 + n : ℕ) : ℝ)) (η₀ * siteGap c' (N + 1 + n)) b := by
    funext n
    simp only [hg]
    have : N₀ + 1 + (n + (N - N₀)) = N + 1 + n := by omega
    rw [this]
  have hmul : Multipliable (fun n : ℕ => g (n + (N - N₀))) := by
    rw [hshift]; exact (h N).2.2.2 hb
  have hsplit := hmul.prod_mul_tprod_nat_mul'
  unfold combTail
  rw [hshift] at hsplit
  exact hsplit.symm

/-- The real tail splits off the reference pair moduli. -/
theorem combTail_split_re {η₀ : ℝ} (hη₀0 : 0 ≤ η₀) (hη₀1 : η₀ ≤ 1 / 4) :
    ∀ᶠ c' in atTop, ∀ (N₀ N : ℕ), N₀ ≤ N → ∀ x : ℝ,
      (combTail c' N₀ η₀ (x : ℂ)).re =
        (∏ i ∈ Finset.range (N - N₀),
          blaschkePairQ (chiQuantile c' ((N₀ + 1 + i : ℕ) : ℝ)) (η₀ * siteGap c' (N₀ + 1 + i)) x) *
        (combTail c' N η₀ (x : ℂ)).re := by
  obtain ⟨_, _, h_ev⟩ := siteGap_eventually_le
  filter_upwards [combTail_split hη₀0 hη₀1, h_ev, eventually_gt_atTop 0] with c' hs
    ⟨_, _, _, hgap⟩ hc' N₀ N hN x
  obtain ⟨him, _⟩ := combTail_real_nonneg (x := x) hc' hη₀0 hη₀1 hgap N
  set t : ℝ := (combTail c' N η₀ (x : ℂ)).re with ht
  have htail : combTail c' N η₀ (x : ℂ) = (t : ℂ) := by
    apply Complex.ext
    · simp [ht]
    · simp [him]
  have h1 := hs N₀ N hN (b := (x : ℂ)) (by simp)
  have hprod : (∏ i ∈ Finset.range (N - N₀),
      pairT (chiQuantile c' ((N₀ + 1 + i : ℕ) : ℝ)) (η₀ * siteGap c' (N₀ + 1 + i)) (x : ℂ)) =
      ((∏ i ∈ Finset.range (N - N₀),
        blaschkePairQ (chiQuantile c' ((N₀ + 1 + i : ℕ) : ℝ)) (η₀ * siteGap c' (N₀ + 1 + i)) x : ℝ) : ℂ) := by
    rw [Complex.ofReal_prod]
    exact Finset.prod_congr rfl fun i _ => pairT_ofReal _ _ _
  rw [h1, hprod, htail, ← Complex.ofReal_mul, Complex.ofReal_re]

/-! ### 2. The bump factor `R_bump` -/

/-- The height of the pair `k` in the bumped comb beyond the base cut: `η_big ℓ_k` in the block, `η₀ ℓ_k`
elsewhere. -/
noncomputable def bumpHeight (d : BumpData) (c' η₀ : ℝ) (k : ℕ) : ℝ :=
  (if d.InBlock c' k then d.H else η₀) * siteGap c' k

/-- `R_bump(x)` (`fw:e3.3`): the product over `N₀ < k ≤ N` of the ratio of the bumped to the unbumped pair
modulus.  Outside the block the ratio is `1`. -/
noncomputable def bumpFactor (d : BumpData) (c' η₀ : ℝ) (N₀ N : ℕ) (x : ℝ) : ℝ :=
  ∏ k ∈ Finset.Ioc N₀ N,
    blaschkePairQ (chiQuantile c' (k : ℝ)) (bumpHeight d c' η₀ k) x /
      blaschkePairQ (chiQuantile c' (k : ℝ)) (η₀ * siteGap c' k) x

@[to_additive]
lemma prod_Ioc_eq_prod_range {M : Type*} [CommMonoid M] (g : ℕ → M) (a b : ℕ) :
    ∏ k ∈ Finset.Ioc a b, g k = ∏ i ∈ Finset.range (b - a), g (a + 1 + i) := by
  have : Finset.Ioc a b = Finset.Ico (a + 1) (b + 1) := by
    ext k; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
  rw [this, Finset.prod_Ico_eq_prod_range]
  have h : b + 1 - (a + 1) = b - a := by omega
  rw [h]

lemma siteGap_pos_of {c' : ℝ} (hc' : 0 < c') {k : ℕ} (hk : 1 ≤ k) : 0 < siteGap c' k := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have := (chiQuantile_strictMonoOn hc') (Set.mem_Ici.mpr (by linarith : (1 / 4 : ℝ) ≤ k))
    (Set.mem_Ici.mpr (by linarith : (1 / 4 : ℝ) ≤ (k : ℝ) + 1)) (by linarith)
  unfold siteGap
  linarith

lemma pairF_pos {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1 / 2) (y : ℝ) : 0 < pairF ε y := by
  have hπ := Real.pi_pos
  rw [pairF_eq]
  have hs : ε ≤ Real.sin (π * ε / 2) := by
    have h := Real.mul_le_sin (x := π * ε / 2) (by positivity) (by nlinarith)
    have : 2 / π * (π * ε / 2) = ε := by field_simp
    linarith
  have hs0 : 0 < Real.sin (π * ε / 2) ^ 2 := by
    have : 0 < Real.sin (π * ε / 2) := lt_of_lt_of_le h0 hs
    positivity
  have hs1 : Real.sin (π * ε / 2) ^ 2 ≤ 1 / 2 := by
    have h : Real.sin (π * ε / 2) ≤ Real.sin (π / 4) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by nlinarith) (by nlinarith) (by nlinarith)
    rw [Real.sin_pi_div_four] at h
    have hs' : 0 ≤ Real.sin (π * ε / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith)
    have := pow_le_pow_left₀ hs' h 2
    rw [div_pow, Real.sq_sqrt (by norm_num)] at this
    linarith
  apply div_pos (by positivity)
  rw [Real.cosh_sq]
  nlinarith [sq_nonneg (Real.sinh (π * y / 2))]

lemma blaschkePairQ_pos_of_eps {χ ε x : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1 / 2) :
    0 < blaschkePairQ χ ε x := by
  rw [blaschkePairQ_eq_pairF]
  exact mul_pos (pairF_pos h0 h1 _) (pairF_pos h0 h1 _)

/-- **`R_bump`, the value identity.**  For every real `x`, the bumped comb is `R_bump(x)` times the base comb;
the threshold in `c'` does not depend on `f`, the cuts `N₀ ≤ N` or the base data. -/
theorem bumped_value (d : BumpData) {η₀ : ℝ} (hη₀0 : 0 < η₀) (hη₀1 : η₀ ≤ 1 / 4) :
    ∀ᶠ c' in atTop, ∀ (f N₀ N : ℕ) (σ₀ ε₀ : ℕ → ℝ) (x : ℝ), f ≤ N₀ → N₀ ≤ N →
      designComb c' f N₀ η₀ σ₀ ε₀ (x : ℂ) = ((combReal c' f N₀ η₀ σ₀ ε₀ x : ℝ) : ℂ) ∧
      bumpedComb d c' f N₀ N η₀ σ₀ ε₀ (x : ℂ) =
        ((bumpFactor d c' η₀ N₀ N x * combReal c' f N₀ η₀ σ₀ ε₀ x : ℝ) : ℂ) := by
  obtain ⟨_, _, h_ev⟩ := siteGap_eventually_le
  filter_upwards [combTail_split_re hη₀0.le hη₀1, h_ev, eventually_gt_atTop 0]
    with c' hsplit ⟨hmono, _, _, hgap⟩ hc' f N₀ N σ₀ ε₀ x hfN₀ hN
  have hb : designComb c' f N₀ η₀ σ₀ ε₀ (x : ℂ) = ((combReal c' f N₀ η₀ σ₀ ε₀ x : ℝ) : ℂ) :=
    designComb_eq_combReal hc' hη₀0.le hη₀1 hgap f N₀ σ₀ ε₀
  refine ⟨hb, ?_⟩
  unfold bumpedComb
  rw [designComb_eq_combReal hc' hη₀0.le hη₀1 hgap f N _ _]
  congr 1
  -- the real identity
  set σ' := bumpSigma c' N₀ σ₀ with hσ'
  set ε' := bumpEps d c' N₀ η₀ ε₀ with hε'
  have hsite_f : designSite c' σ' f = designSite c' σ₀ f := designSite_bumpSigma_of_le hfN₀
  have hNf : N - f = (N₀ - f) + (N - N₀) := by omega
  have hq' : ∏ i ∈ Finset.range (N - f), blaschkePairQ (designSite c' σ' (f + 1 + i)) (ε' (f + 1 + i)) x =
      (∏ i ∈ Finset.range (N₀ - f), blaschkePairQ (designSite c' σ₀ (f + 1 + i)) (ε₀ (f + 1 + i)) x) *
      ∏ i ∈ Finset.range (N - N₀), blaschkePairQ (chiQuantile c' ((N₀ + 1 + i : ℕ) : ℝ))
        (bumpHeight d c' η₀ (N₀ + 1 + i)) x := by
    rw [hNf, Finset.prod_range_add]
    congr 1
    · refine Finset.prod_congr rfl fun i hi => ?_
      have hi' := Finset.mem_range.mp hi
      have hk : f + 1 + i ≤ N₀ := by omega
      rw [designSite_bumpSigma_of_le hk, hε', bumpEps_of_le hk]
    · refine Finset.prod_congr rfl fun i _ => ?_
      have hk : N₀ < f + 1 + (N₀ - f) + i := by omega
      have e : f + 1 + (N₀ - f + i) = N₀ + 1 + i := by omega
      rw [e]
      have hk' : N₀ < N₀ + 1 + i := by omega
      rw [designSite_bumpSigma_of_gt hc' hk']
      congr 1
      by_cases hbl : d.InBlock c' (N₀ + 1 + i)
      · rw [hε', bumpEps_of_gt_block hk' hbl]
        simp [bumpHeight, hbl]
      · rw [hε', bumpEps_of_gt_not_block hk' hbl]
        simp [bumpHeight, hbl]
  have hq0pos : ∀ i ∈ Finset.range (N - N₀), 0 < blaschkePairQ (chiQuantile c' ((N₀ + 1 + i : ℕ) : ℝ))
      (η₀ * siteGap c' (N₀ + 1 + i)) x := by
    intro i _
    have hk : 1 ≤ N₀ + 1 + i := by omega
    have hpos := siteGap_pos_of hc' hk
    have hle : siteGap c' (N₀ + 1 + i) ≤ 1 / 2 := (hmono _ hk).trans hgap
    exact blaschkePairQ_pos_of_eps (by positivity) (by nlinarith)
  have hP0 : 0 < ∏ i ∈ Finset.range (N - N₀), blaschkePairQ (chiQuantile c' ((N₀ + 1 + i : ℕ) : ℝ))
      (η₀ * siteGap c' (N₀ + 1 + i)) x := Finset.prod_pos hq0pos
  have hfac : bumpFactor d c' η₀ N₀ N x =
      (∏ i ∈ Finset.range (N - N₀), blaschkePairQ (chiQuantile c' ((N₀ + 1 + i : ℕ) : ℝ))
        (bumpHeight d c' η₀ (N₀ + 1 + i)) x) /
      ∏ i ∈ Finset.range (N - N₀), blaschkePairQ (chiQuantile c' ((N₀ + 1 + i : ℕ) : ℝ))
        (η₀ * siteGap c' (N₀ + 1 + i)) x := by
    unfold bumpFactor
    rw [prod_Ioc_eq_prod_range, Finset.prod_div_distrib]
  have hbase : combReal c' f N₀ η₀ σ₀ ε₀ x =
      (Real.tanh (π * (x - designSite c' σ₀ f) / 2) * Real.tanh (π * (x + designSite c' σ₀ f) / 2)) *
        (∏ i ∈ Finset.range (N₀ - f), blaschkePairQ (designSite c' σ₀ (f + 1 + i)) (ε₀ (f + 1 + i)) x) *
        ((∏ i ∈ Finset.range (N - N₀), blaschkePairQ (chiQuantile c' ((N₀ + 1 + i : ℕ) : ℝ))
          (η₀ * siteGap c' (N₀ + 1 + i)) x) * (combTail c' N η₀ (x : ℂ)).re) := by
    unfold combReal
    rw [hsplit N₀ N hN x]
  have hlhs : combReal c' f N η₀ σ' ε' x =
      (Real.tanh (π * (x - designSite c' σ₀ f) / 2) * Real.tanh (π * (x + designSite c' σ₀ f) / 2)) *
        (∏ i ∈ Finset.range (N₀ - f), blaschkePairQ (designSite c' σ₀ (f + 1 + i)) (ε₀ (f + 1 + i)) x) *
        ((∏ i ∈ Finset.range (N - N₀), blaschkePairQ (chiQuantile c' ((N₀ + 1 + i : ℕ) : ℝ))
          (bumpHeight d c' η₀ (N₀ + 1 + i)) x) * (combTail c' N η₀ (x : ℂ)).re) := by
    unfold combReal
    rw [hsite_f, hq']
    ring
  rw [hlhs, hbase, hfac]
  field_simp

/-- info: 'FormalResearch.ModularBootstrap.Upper.Bump.designComb_eq_combReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms designComb_eq_combReal

/-- info: 'FormalResearch.ModularBootstrap.Upper.Bump.combTail_split_re' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms combTail_split_re

/-- info: 'FormalResearch.ModularBootstrap.Upper.Bump.bumped_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bumped_value

end FormalResearch.ModularBootstrap.Upper.Bump
