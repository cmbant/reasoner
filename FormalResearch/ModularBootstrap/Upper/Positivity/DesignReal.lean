module

public import FormalResearch.ModularBootstrap.Upper.Design.PerturbP

/-!
# Proposition II: the finite modification of the comb is real and positive to the right of its zeroes

Source: `CFT/modular_bootstrap/paper/upper_transfer.tex`, Proposition II (`ut:II`), proof step (2)-(4):
`h₀^D(x) = sech²(π x/2) B_D^{(f)}(x)` is a real number, and `B_D^{(f)}(x) = |B_D^{(f)}(x)|` when `x`
lies to the right of all the zeroes `χ'_k` of the modification.

* `combTail_real_nonneg`: for real `x`, the unmodified tail `∏_{k>N} T_{χ_k + iη₀ℓ_k} T_{χ_k - iη₀ℓ_k}(x)`
  is a nonnegative real number.
* `designComb_ofReal`: for real `x` to the right of the sites `χ'_f, …, χ'_N` (all in `[0, x)`) and
  widths `0 ≤ ε'_k ≤ 1/2`, `B_D^{(f)}(x) = r` with `r ≥ 0` real, and `r > 0` as soon as the tail
  does not vanish at `x`.
* `tail_ne_zero_of_refComb_ne_zero`: the tail does not vanish where the reference comb does not.

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Positivity

open FormalResearch.ModularBootstrap.Upper.Comb FormalResearch.ModularBootstrap.Upper.Design

private lemma tanh_conj_complex' (w : ℂ) :
    Complex.tanh (star w) = star (Complex.tanh w) := by
  change Complex.tanh ((starRingEnd ℂ) w) = (starRingEnd ℂ) (Complex.tanh w)
  rw [Complex.tanh_eq_sinh_div_cosh, Complex.tanh_eq_sinh_div_cosh,
    map_div₀, Complex.sinh_conj, Complex.cosh_conj]

private lemma blaschkeT_conj_real' (χ ε x : ℝ) :
    blaschkeT ((χ : ℂ) - (ε : ℂ) * Complex.I) (x : ℂ) =
      star (blaschkeT ((χ : ℂ) + (ε : ℂ) * Complex.I) (x : ℂ)) := by
  unfold blaschkeT
  have h1 : (π : ℂ) * ((x : ℂ) - ((χ : ℂ) - (ε : ℂ) * Complex.I)) / 2 =
      star ((π : ℂ) * ((x : ℂ) - ((χ : ℂ) + (ε : ℂ) * Complex.I)) / 2) := by
    change _ = (starRingEnd ℂ) _
    simp only [map_div₀, map_mul, map_sub, map_add, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    ring
  have h2 : (π : ℂ) * ((x : ℂ) + ((χ : ℂ) - (ε : ℂ) * Complex.I)) / 2 =
      star ((π : ℂ) * ((x : ℂ) + ((χ : ℂ) + (ε : ℂ) * Complex.I)) / 2) := by
    change _ = (starRingEnd ℂ) _
    simp only [map_div₀, map_mul, map_add, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    ring
  rw [h1, h2, tanh_conj_complex', tanh_conj_complex']
  change _ = (starRingEnd ℂ) _
  rw [map_mul]
  rfl

lemma pairT_ofReal (χ ε x : ℝ) : pairT χ ε (x : ℂ) = ((blaschkePairQ χ ε x : ℝ) : ℂ) := by
  unfold pairT
  rw [blaschkeT_conj_real']
  set z : ℂ := blaschkeT ((χ : ℂ) + (ε : ℂ) * Complex.I) (x : ℂ)
  have hz : z * star z = ((Complex.normSq z : ℝ) : ℂ) := by
    rw [mul_comm, Complex.normSq_eq_conj_mul_self]
    rfl
  rw [hz, Complex.normSq_eq_norm_sq]
  have hp : blaschkePairQ χ ε x = ‖z‖ ^ 2 := by
    unfold blaschkePairQ
    have hconj : ‖blaschkeT ((χ : ℂ) - (ε : ℂ) * Complex.I) (x : ℂ)‖ = ‖z‖ := by
      rw [blaschkeT_conj_real']
      exact Complex.norm_conj z
    dsimp [z] at hconj ⊢
    rw [norm_mul, hconj, sq]
  rw [hp]

lemma blaschkeT_ofReal_eq (y x : ℝ) :
    blaschkeT (y : ℂ) (x : ℂ) =
      ((Real.tanh (π * (x - y) / 2) * Real.tanh (π * (x + y) / 2) : ℝ) : ℂ) := by
  unfold blaschkeT
  have hc1 : Complex.tanh ((π : ℂ) * ((x : ℂ) - (y : ℂ)) / 2) =
      ((Real.tanh (π * (x - y) / 2) : ℝ) : ℂ) := by
    have h1 : Complex.tanh ((π * (x - y) / 2 : ℝ) : ℂ) =
        ((Real.tanh (π * (x - y) / 2) : ℝ) : ℂ) := by
      rw [Complex.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
        ← Complex.ofReal_sinh, ← Complex.ofReal_cosh, Complex.ofReal_div]
    rw [← h1]; congr 1; push_cast; ring
  have hc2 : Complex.tanh ((π : ℂ) * ((x : ℂ) + (y : ℂ)) / 2) =
      ((Real.tanh (π * (x + y) / 2) : ℝ) : ℂ) := by
    have h1 : Complex.tanh ((π * (x + y) / 2 : ℝ) : ℂ) =
        ((Real.tanh (π * (x + y) / 2) : ℝ) : ℂ) := by
      rw [Complex.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
        ← Complex.ofReal_sinh, ← Complex.ofReal_cosh, Complex.ofReal_div]
    rw [← h1]; congr 1; push_cast; ring
  rw [hc1, hc2, Complex.ofReal_mul]

lemma tanh_prod_pos_of_lt {y x : ℝ} (hy : 0 ≤ y) (hxy : y < x) :
    0 < Real.tanh (π * (x - y) / 2) * Real.tanh (π * (x + y) / 2) := by
  have hpi := Real.pi_pos
  have h1 : 0 < Real.tanh (π * (x - y) / 2) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (by nlinarith)) (Real.cosh_pos _)
  have h2 : 0 < Real.tanh (π * (x + y) / 2) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (by nlinarith)) (Real.cosh_pos _)
  exact mul_pos h1 h2

/-- For real `x`, the unmodified tail of the comb is a nonnegative real number. -/
theorem combTail_real_nonneg {c' η₀ x : ℝ} (hc' : 0 < c') (hη₀0 : 0 ≤ η₀) (hη₀1 : η₀ ≤ 1 / 4)
    (hgap : siteGap c' 1 ≤ 1 / 2) (N : ℕ) :
    (combTail c' N η₀ (x : ℂ)).im = 0 ∧ 0 ≤ (combTail c' N η₀ (x : ℂ)).re := by
  let χ := fun m : ℕ => chiQuantile c' (N + 1 + m : ℕ)
  let ε := fun m : ℕ => η₀ * siteGap c' (N + 1 + m)
  let P : ℕ → ℂ := fun m => pairT (χ m) (ε m) (x : ℂ)
  have hχ_nn : ∀ m : ℕ, 0 ≤ χ m := fun m => by
    have hm1 : (1 : ℝ) ≤ ((N + 1 + m : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ N + 1 + m)
    exact xiStar_pos.le.trans (chiQuantile_spec hc' (by linarith)).1
  have hgk_nn : ∀ m : ℕ, 0 ≤ siteGap c' (N + 1 + m) := fun m => by
    have hm1 : (1 : ℝ) ≤ ((N + 1 + m : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ N + 1 + m)
    unfold siteGap
    exact sub_nonneg.mpr ((chiQuantile_strictMonoOn hc').monotoneOn
      (Set.mem_Ici.mpr (by linarith)) (Set.mem_Ici.mpr (by linarith)) (by linarith))
  have hε_bd : ∀ m : ℕ, |ε m| ≤ 1 / 8 := fun m => by
    dsimp [ε]
    have hgk : siteGap c' (N + 1 + m) ≤ siteGap c' 1 := by
      have hanti := (siteGap_strictAnti hc').antitone (Nat.zero_le (N + m))
      have e : N + 1 + m = (N + m) + 1 := by omega
      rw [e]
      simpa using hanti
    rw [abs_of_nonneg (mul_nonneg hη₀0 (hgk_nn m))]
    nlinarith
  have hsum := summable_exp_neg_pi_chiQuantile hc' N
  have hhasProd := (comb_pairProd_hasProdLocallyUniformlyOn χ ε hχ_nn hε_bd hsum).hasProd
    (by simp : (x : ℂ) ∈ {b : ℂ | |b.im| < 7 / 8})
  have hP_eq : ∀ m : ℕ, P m = ((blaschkePairQ (χ m) (ε m) x : ℝ) : ℂ) := fun m =>
    pairT_ofReal _ _ _
  have hq_nn : ∀ m : ℕ, 0 ≤ blaschkePairQ (χ m) (ε m) x := fun m => by
    unfold blaschkePairQ; positivity
  have hpart : ∀ s : Finset ℕ,
      (∏ m ∈ s, P m).im = 0 ∧ 0 ≤ (∏ m ∈ s, P m).re := fun s => by
    have h_eq : ∏ m ∈ s, P m = ((∏ m ∈ s, blaschkePairQ (χ m) (ε m) x : ℝ) : ℂ) := by
      rw [Complex.ofReal_prod]
      exact Finset.prod_congr rfl fun m _ => hP_eq m
    rw [h_eq, Complex.ofReal_im, Complex.ofReal_re]
    exact ⟨rfl, Finset.prod_nonneg fun m _ => hq_nn m⟩
  have him_prod : (∏' m : ℕ, P m).im = 0 :=
    tendsto_nhds_unique (Complex.continuous_im.continuousAt.tendsto.comp hhasProd)
      (tendsto_const_nhds.congr (fun s => (hpart s).1.symm))
  have hre_prod : 0 ≤ (∏' m : ℕ, P m).re :=
    ge_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp hhasProd)
      (Eventually.of_forall fun s => (hpart s).2)
  exact ⟨him_prod, hre_prod⟩

/-- For real `x` to the right of the sites `χ'_f, …, χ'_N` (all in `[0, x)`) and widths
`0 ≤ ε'_k ≤ 1/2`, `B_D^{(f)}(x)` is a real number `r ≥ 0`, and `r > 0` as soon as the unmodified tail
does not vanish at `x`. -/
theorem designComb_ofReal {c' η₀ x : ℝ} (hc' : 0 < c') (hη₀0 : 0 ≤ η₀) (hη₀1 : η₀ ≤ 1 / 4)
    (hgap : siteGap c' 1 ≤ 1 / 2) (f N : ℕ) (σ ε : ℕ → ℝ)
    (hsite : ∀ k, f ≤ k → k ≤ N → 0 ≤ designSite c' σ k ∧ designSite c' σ k < x)
    (hε : ∀ k, f < k → k ≤ N → 0 ≤ ε k ∧ ε k ≤ 1 / 2) (hfN : f ≤ N) :
    ∃ r : ℝ, designComb c' f N η₀ σ ε (x : ℂ) = (r : ℂ) ∧ 0 ≤ r ∧
      (combTail c' N η₀ (x : ℂ) ≠ 0 → 0 < r) := by
  have hx : 0 ≤ x := by
    have := hsite f le_rfl hfN
    linarith [this.1, this.2]
  obtain ⟨him, hre⟩ := combTail_real_nonneg hc' hη₀0 hη₀1 hgap N
  set t : ℝ := (combTail c' N η₀ (x : ℂ)).re with ht
  have htail : combTail c' N η₀ (x : ℂ) = (t : ℂ) := by
    apply Complex.ext
    · simp [ht]
    · simp [him]
  set tf : ℝ := Real.tanh (π * (x - designSite c' σ f) / 2) *
    Real.tanh (π * (x + designSite c' σ f) / 2) with htf
  have htf0 : 0 < tf := tanh_prod_pos_of_lt (hsite f le_rfl hfN).1 (hsite f le_rfl hfN).2
  set q : ℝ := ∏ i ∈ Finset.range (N - f),
    blaschkePairQ (designSite c' σ (f + 1 + i)) (ε (f + 1 + i)) x with hq
  have hq0 : 0 < q := by
    apply Finset.prod_pos
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hs := hsite (f + 1 + i) (by omega) (by omega)
    have he := hε (f + 1 + i) (by omega) (by omega)
    exact blaschkePairQ_pos hs.1 hx hs.2.ne' he.1 he.2
  have hD : designComb c' f N η₀ σ ε (x : ℂ) = ((tf * q * t : ℝ) : ℂ) := by
    unfold designComb
    rw [htail, blaschkeT_ofReal_eq]
    have hprod : (∏ i ∈ Finset.range (N - f),
        pairT (designSite c' σ (f + 1 + i)) (ε (f + 1 + i)) (x : ℂ)) = (q : ℂ) := by
      rw [hq, Complex.ofReal_prod]
      exact Finset.prod_congr rfl fun i _ => pairT_ofReal _ _ _
    rw [hprod, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  refine ⟨tf * q * t, hD, mul_nonneg (mul_pos htf0 hq0).le hre, fun hne => ?_⟩
  have ht0 : t ≠ 0 := fun h => hne (by rw [htail, h]; simp)
  exact mul_pos (mul_pos htf0 hq0) (lt_of_le_of_ne hre (Ne.symm ht0))

/-- The unmodified tail does not vanish where the reference comb does not. -/
theorem tail_ne_zero_of_refComb_ne_zero (f N : ℕ) (hfN : f ≤ N) {η₀ : ℝ} (hη₀0 : 0 ≤ η₀)
    (hη₀1 : η₀ ≤ 1 / 4) :
    ∀ᶠ c' in atTop, ∀ x : ℝ, refComb c' f η₀ (x : ℂ) ≠ 0 → combTail c' N η₀ (x : ℂ) ≠ 0 := by
  filter_upwards [refComb_eq_split f N hfN hη₀0 hη₀1] with c' hsp x hne htail
  apply hne
  rw [hsp (by simp), htail, mul_zero]

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.combTail_real_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms combTail_real_nonneg

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.designComb_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms designComb_ofReal

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.tail_ne_zero_of_refComb_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tail_ne_zero_of_refComb_ne_zero

end FormalResearch.ModularBootstrap.Upper.Positivity
