module

public import FormalResearch.ModularBootstrap.TwoLevel.NegativeVacuumLimit
public import FormalResearch.ModularBootstrap.Upper.Window.Quadrature

/-!
# The node tail of the approximating designs (Theorem 2.5, Step 1)

For `ν > K` the node value of the design `negDesign α K n η q` is a bounded multiple of the weight
`Π_ν(0)` of the `f = 1` design `D(N, η, 0)` of `ut:V`: `nodeC D ν = G_ν · Π_ν(0)` with `|G_ν| ≤ M`, `M` independent
of `ν`, `n ≥ K` and `η ∈ (0, 1/4]`.  Hence by Lemma E (`ut:E`, `lemma_E`) the tail `Σ_{ν > K}` of the node sum is
`O(η² + N^{-1/3})`.

All results are proved unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.TwoLevel.NegativeVacuum

open FormalResearch.Special FormalResearch.SignUncertainty FormalResearch.ModularBootstrap.Upper.Window

/-- `(x² + e²)/(y² + e²) ≤ 2 + (2c² + e²)/δ²` when `|y| ≥ δ > 0` and `|x - y| ≤ c`. -/
lemma ratio_bound {x y e δ c : ℝ} (hδ : 0 < δ) (hy : δ ≤ |y|) (hxy : |x - y| ≤ c) :
    (x ^ 2 + e ^ 2) / (y ^ 2 + e ^ 2) ≤ 2 + (2 * c ^ 2 + e ^ 2) / δ ^ 2 := by
  have hy2 : δ ^ 2 ≤ y ^ 2 := by
    have := pow_le_pow_left₀ hδ.le hy 2
    rwa [sq_abs] at this
  have hypos : 0 < y ^ 2 := lt_of_lt_of_le (by positivity) hy2
  have hx2 : x ^ 2 ≤ 2 * y ^ 2 + 2 * c ^ 2 := by
    have h1 : x = y + (x - y) := by ring
    have h2 : (x - y) ^ 2 ≤ c ^ 2 := by
      have := sq_abs (x - y)
      nlinarith [abs_nonneg (x - y)]
    nlinarith [sq_nonneg (y - (x - y))]
  calc (x ^ 2 + e ^ 2) / (y ^ 2 + e ^ 2) ≤ (x ^ 2 + e ^ 2) / y ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) hypos (by linarith [sq_nonneg e])
    _ ≤ (2 * y ^ 2 + 2 * c ^ 2 + e ^ 2) / y ^ 2 := by
        gcongr
    _ = 2 + (2 * c ^ 2 + e ^ 2) / y ^ 2 := by
        rw [show 2 * y ^ 2 + 2 * c ^ 2 + e ^ 2 = 2 * y ^ 2 + (2 * c ^ 2 + e ^ 2) by ring, add_div,
          mul_div_cancel_right₀ _ hypos.ne']
    _ ≤ 2 + (2 * c ^ 2 + e ^ 2) / δ ^ 2 := by
        gcongr

/-- The ratio of the factor at `k ≤ K` of the design to that of the `f = 1` design `D(N, η, ·)`. -/
noncomputable def rrFac (α : ℝ) (K : ℕ) (η : ℝ) (ν k : ℕ) : ℝ :=
  if k ≤ K then ((airyZero ν - clarkNode α k) ^ 2 + (η * gapWKB k) ^ 2) /
    ((airyZero ν - airyZero k) ^ 2 + (η * gapWKB k) ^ 2) else 1

lemma rrFac_nonneg (α : ℝ) (K : ℕ) (η : ℝ) (ν k : ℕ) : 0 ≤ rrFac α K η ν k := by
  unfold rrFac
  split_ifs
  · positivity
  · exact zero_le_one

/-- Uniform bound on `rrFac` for `3 ≤ k ≤ K < ν`. -/
lemma rrFac_le (α : ℝ) {K : ℕ} (hK : 3 ≤ K) :
    ∃ R : ℕ → ℝ, ∀ ν k : ℕ, K < ν → ∀ η : ℝ, 0 ≤ η → η ≤ 1 → 1 ≤ k → k ≤ K → rrFac α K η ν k ≤ R k := by
  set δ : ℝ := airyGap K with hδ
  have hδ0 : 0 < δ := airyGap_pos (by omega)
  refine ⟨fun k => 2 + (2 * (airyZero k - clarkNode α k) ^ 2 + gapWKB k ^ 2) / δ ^ 2,
    fun ν k hν η hη0 hη1 hk1 hkK => ?_⟩
  unfold rrFac
  simp only [hkK, ↓reduceIte]
  have hy : δ ≤ |airyZero ν - airyZero k| := by
    have h1 : airyZero K ≤ airyZero k := airyZero_le_of_le (by omega) hkK
    have h2 : airyZero ν ≤ airyZero (K + 1) := airyZero_le_of_le (by omega) hν
    have hδ' : δ = airyZero K - airyZero (K + 1) := by rw [hδ]; rfl
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  have hxy : |(airyZero ν - clarkNode α k) - (airyZero ν - airyZero k)| ≤ |airyZero k - clarkNode α k| := by
    apply le_of_eq; congr 1; ring
  have := ratio_bound (e := η * gapWKB k) hδ0 hy hxy
  refine this.trans ?_
  have hg := (gapWKB_pos hk1).le
  have he : (η * gapWKB k) ^ 2 ≤ gapWKB k ^ 2 := by
    have : η * gapWKB k ≤ gapWKB k := by nlinarith
    exact pow_le_pow_left₀ (by positivity) this 2
  rw [sq_abs]
  gcongr

/-- The multiplier relating the node values of the design to `Π_ν(0)`. -/
noncomputable def Gnu (α : ℝ) (K : ℕ) (q η : ℝ) (ν : ℕ) : ℝ :=
  ((airyZero ν - (clarkNode α 1 - η)) * (airyZero ν - q) /
      ((airyZero ν - airyZero 1) ^ 2 * (airyZero ν - airyZero 2) ^ 2)) *
    (∏ k ∈ Finset.Icc 3 K, rrFac α K η ν k) * |airyZero ν - airyZero 1| /
    (((airyZero ν - airyZero 2) ^ 2 + (η * gapWKB 2) ^ 2) / (airyZero ν - airyZero 2) ^ 2)

/-- `|G_ν| ≤ M` uniformly in `ν > K` and `η ∈ (0, 1/4]`. -/
lemma Gnu_bound (α : ℝ) {K : ℕ} (hK : 3 ≤ K) (q : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ν : ℕ, K < ν → ∀ η : ℝ, 0 < η → η ≤ 1 / 4 → |Gnu α K q η ν| ≤ M := by
  obtain ⟨R, hR⟩ := rrFac_le α hK
  set Rp : ℝ := ∏ k ∈ Finset.Icc 3 K, R k with hRp
  set g₀ : ℝ := airyZero 2 - airyZero 4 with hg₀
  have hg₀0 : 0 < g₀ := by
    have := airyZero_lt_of_lt (n := 2) (m := 4) (by norm_num) (by norm_num)
    linarith
  set P : ℝ := |airyZero 1 - clarkNode α 1| + 1 / 4 with hP
  set Q : ℝ := |airyZero 2 - q| with hQ
  have hP0 : 0 ≤ P := by positivity
  have hQ0 : 0 ≤ Q := abs_nonneg _
  have hRp0 : 0 ≤ Rp := by
    have h0 : 0 ≤ ∏ k ∈ Finset.Icc 3 K, rrFac α K 0 (K + 1) k :=
      Finset.prod_nonneg fun k _ => rrFac_nonneg _ _ _ _ _
    refine h0.trans (Finset.prod_le_prod₀ (fun k _ => rrFac_nonneg _ _ _ _ _) fun k hk => ?_)
    have hk' := Finset.mem_Icc.mp hk
    exact hR (K + 1) k (by omega) 0 le_rfl (by norm_num) (by omega) hk'.2
  refine ⟨(1 + P / g₀) * (1 / g₀ + Q / g₀ ^ 2) * Rp, by positivity, fun ν hν η hη0 hη1 => ?_⟩
  have hν4 : 4 ≤ ν := by omega
  have ha4 : airyZero ν ≤ airyZero 4 := airyZero_le_of_le (by norm_num) hν4
  have ha12 : airyZero 2 < airyZero 1 := airyZero_lt_of_lt (n := 1) (m := 2) le_rfl (by norm_num)
  set u1 : ℝ := airyZero 1 - airyZero ν with hu1
  set u2 : ℝ := airyZero 2 - airyZero ν with hu2
  have hu2g : g₀ ≤ u2 := by rw [hu2, hg₀]; linarith
  have hu1g : g₀ ≤ u1 := by rw [hu1, hg₀]; linarith
  have hu2p : 0 < u2 := lt_of_lt_of_le hg₀0 hu2g
  have hu1p : 0 < u1 := lt_of_lt_of_le hg₀0 hu1g
  have hρ0 : 0 ≤ ∏ k ∈ Finset.Icc 3 K, rrFac α K η ν k := Finset.prod_nonneg fun k _ => rrFac_nonneg _ _ _ _ _
  have hρ : ∏ k ∈ Finset.Icc 3 K, rrFac α K η ν k ≤ Rp :=
    Finset.prod_le_prod₀ (fun k _ => rrFac_nonneg _ _ _ _ _) fun k hk =>
      hR ν k hν η hη0.le (by linarith) (by have := (Finset.mem_Icc.mp hk).1; omega) (Finset.mem_Icc.mp hk).2
  set ρ : ℝ := ∏ k ∈ Finset.Icc 3 K, rrFac α K η ν k with hρdef
  have hf2 : 1 ≤ ((airyZero ν - airyZero 2) ^ 2 + (η * gapWKB 2) ^ 2) / (airyZero ν - airyZero 2) ^ 2 := by
    have hsq : 0 < (airyZero ν - airyZero 2) ^ 2 := by
      have : airyZero ν - airyZero 2 ≠ 0 := by intro h; linarith
      positivity
    rw [le_div_iff₀ hsq]; nlinarith [sq_nonneg (η * gapWKB 2)]
  set f2 : ℝ := ((airyZero ν - airyZero 2) ^ 2 + (η * gapWKB 2) ^ 2) / (airyZero ν - airyZero 2) ^ 2 with hf2def
  have hf2p : 0 < f2 := lt_of_lt_of_le one_pos hf2
  have e1 : (airyZero ν - airyZero 1) ^ 2 = u1 ^ 2 := by rw [hu1]; ring
  have e2 : (airyZero ν - airyZero 2) ^ 2 = u2 ^ 2 := by rw [hu2]; ring
  have e3 : |airyZero ν - airyZero 1| = u1 := by rw [abs_sub_comm, abs_of_pos hu1p]
  have hp : |airyZero ν - (clarkNode α 1 - η)| ≤ u1 + P := by
    have : airyZero ν - (clarkNode α 1 - η) = -u1 + ((airyZero 1 - clarkNode α 1) + η) := by rw [hu1]; ring
    rw [this]
    calc |-u1 + ((airyZero 1 - clarkNode α 1) + η)| ≤ |-u1| + |(airyZero 1 - clarkNode α 1) + η| := abs_add_le _ _
      _ ≤ u1 + P := by
        rw [abs_neg, abs_of_pos hu1p]
        have := abs_add_le (airyZero 1 - clarkNode α 1) η
        rw [abs_of_pos hη0] at this
        rw [hP]; linarith
  have hq : |airyZero ν - q| ≤ u2 + Q := by
    have : airyZero ν - q = -u2 + (airyZero 2 - q) := by rw [hu2]; ring
    rw [this]
    calc |-u2 + (airyZero 2 - q)| ≤ |-u2| + |airyZero 2 - q| := abs_add_le _ _
      _ = u2 + Q := by rw [abs_neg, abs_of_pos hu2p]
  unfold Gnu
  rw [← hρdef, ← hf2def, e1, e2, e3]
  have hden : 0 < u1 ^ 2 * u2 ^ 2 := by positivity
  rw [abs_div, abs_mul, abs_mul, abs_div, abs_mul, abs_of_pos hden, abs_of_pos hu1p, abs_of_nonneg hρ0,
    abs_of_pos hf2p]
  have h1 : (u1 + P) / u1 ≤ 1 + P / g₀ := by
    rw [add_div, div_self hu1p.ne']
    gcongr
  have h2 : (u2 + Q) / u2 ^ 2 ≤ 1 / g₀ + Q / g₀ ^ 2 := by
    calc (u2 + Q) / u2 ^ 2 = 1 / u2 + Q / u2 ^ 2 := by field_simp
      _ ≤ 1 / g₀ + Q / g₀ ^ 2 :=
        add_le_add (one_div_le_one_div_of_le hg₀0 hu2g)
          (div_le_div_of_nonneg_left hQ0 (by positivity) (pow_le_pow_left₀ hg₀0.le hu2g 2))
  set Ap : ℝ := |airyZero ν - (clarkNode α 1 - η)| with hAp
  set Aq : ℝ := |airyZero ν - q| with hAq
  have hAp0 : 0 ≤ Ap := abs_nonneg _
  have hAq0 : 0 ≤ Aq := abs_nonneg _
  calc Ap * Aq / (u1 ^ 2 * u2 ^ 2) * ρ * u1 / f2 ≤ Ap * Aq / (u1 ^ 2 * u2 ^ 2) * ρ * u1 :=
        div_le_self (by positivity) hf2
    _ = (Ap / u1) * (Aq / u2 ^ 2) * ρ := by field_simp
    _ ≤ ((u1 + P) / u1) * ((u2 + Q) / u2 ^ 2) * ρ := by gcongr
    _ ≤ (1 + P / g₀) * (1 / g₀ + Q / g₀ ^ 2) * Rp := by gcongr

lemma prod_Icc_three_eq_range {M : Type*} [CommMonoid M] (K : ℕ) (f : ℕ → M) :
    ∏ k ∈ Finset.Icc 3 K, f k = ∏ m ∈ Finset.range (K - 2), f (3 + m) := by
  have h2 : Finset.Icc 3 K = Finset.Ico 3 (K + 1) := by
    ext; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [h2, Finset.prod_Ico_eq_prod_range]
  have : K + 1 - 3 = K - 2 := by omega
  rw [this]

lemma tailHyp_two_of_one {S W : ℕ → ℝ} (h : AiryProdTailHypothesis 1 S W) : AiryProdTailHypothesis 2 S W := by
  obtain ⟨C, hC, h⟩ := h
  exact ⟨C, hC, fun k hk => h k (by omega)⟩

lemma airyZero_ne_cast {ν k : ℕ} (hν : 1 ≤ ν) (hk : 1 ≤ k) (hkν : k ≠ ν) :
    (airyZero ν : ℂ) ≠ (airyZero k : ℂ) := fun h =>
  hkν (airyZero_injective_on hk hν (Complex.ofReal_injective h).symm)

/-- `airyProdTailExcept 1 = f₂ · airyProdTailExcept 2` for the `f = 1` design at `a_ν`, `ν ≥ 3`, `N ≥ 2`. -/
lemma tailExcept_one_eq (N : ℕ) (hN : 2 ≤ N) (η : ℝ) {ν : ℕ} (hν : 3 ≤ ν) :
    airyProdTailExcept 1 ν (designSiteU N) (designWidthU N η) (airyZero ν : ℂ) =
      ((((airyZero ν - airyZero 2) ^ 2 + (η * gapWKB 2) ^ 2) / (airyZero ν - airyZero 2) ^ 2 : ℝ) : ℂ) *
        airyProdTailExcept 2 ν (designSiteU N) (designWidthU N η) (airyZero ν : ℂ) := by
  have hpd := hasProd_airyProdTailExcept (f := 2) (n := ν) (u := (airyZero ν : ℂ))
    (tailHyp_two_of_one (design_tail_hypothesis N η))
    (fun k _ hkν => airyZero_ne_cast (by omega) (by omega) hkν)
  have hshift : (fun m : ℕ => (fun m : ℕ => if 1 + 1 + m = ν then (1 : ℂ) else
      airyProdFactor (designSiteU N) (designWidthU N η) (1 + 1 + m) (airyZero ν : ℂ)) (m + 1)) =
      (fun m : ℕ => if 2 + 1 + m = ν then (1 : ℂ) else
      airyProdFactor (designSiteU N) (designWidthU N η) (2 + 1 + m) (airyZero ν : ℂ)) := by
    funext m
    simp only [show 1 + 1 + (m + 1) = 2 + 1 + m by omega]
  have hm : Multipliable (fun m : ℕ => (fun m : ℕ => if 1 + 1 + m = ν then (1 : ℂ) else
      airyProdFactor (designSiteU N) (designWidthU N η) (1 + 1 + m) (airyZero ν : ℂ)) (m + 1)) := by
    rw [hshift]; exact hpd.multipliable
  have hmul := tprod_eq_zero_mul' (f := fun m : ℕ => if 1 + 1 + m = ν then (1 : ℂ) else
      airyProdFactor (designSiteU N) (designWidthU N η) (1 + 1 + m) (airyZero ν : ℂ)) hm
  have e0 : airyProdTailExcept 1 ν (designSiteU N) (designWidthU N η) (airyZero ν : ℂ) =
      ∏' m : ℕ, (if 1 + 1 + m = ν then (1 : ℂ) else
        airyProdFactor (designSiteU N) (designWidthU N η) (1 + 1 + m) (airyZero ν : ℂ)) := rfl
  rw [e0, hmul, hshift]
  simp only [show ¬(1 + 1 + 0 = ν) by omega, ↓reduceIte]
  rw [airyProdFactor_airyZero]
  have hS : designSiteU N 2 = airyZero 2 := by unfold designSiteU; simp [hN]
  have hW : designWidthU N η 2 = η * gapWKB 2 := by unfold designWidthU; simp [hN]
  rw [hS, hW]
  rfl

lemma siteSeq_of_gt (α : ℝ) {K n k : ℕ} (hk : K < k) (hk3 : 3 ≤ k) :
    siteSeq α K n k = designSiteU (n + 2) k := by
  unfold siteSeq designSiteU
  by_cases h : k ≤ n + 2
  · simp [h, hk3, show ¬(k ≤ K) by omega]
  · simp [h]

lemma widthSeq_of_ge (n : ℕ) (η : ℝ) {k : ℕ} (hk3 : 3 ≤ k) :
    widthSeq n η k = designWidthU (n + 2) η k := by
  unfold widthSeq designWidthU
  by_cases h : k ≤ n + 2
  · simp [h, hk3]
  · simp [h]

lemma siteSeq_of_le (α : ℝ) {K n k : ℕ} (hkK : k ≤ K) (hk3 : 3 ≤ k) (hn : K ≤ n) :
    siteSeq α K n k = clarkNode α k := by
  unfold siteSeq
  simp [hk3, hkK, show k ≤ n + 2 by omega]

lemma designSiteU_of_le {N k : ℕ} (hk : k ≤ N) : designSiteU N k = airyZero k := by
  unfold designSiteU; simp [hk]

lemma designWidthU_of_le {N k : ℕ} (η : ℝ) (hk : k ≤ N) : designWidthU N η k = η * gapWKB k := by
  unfold designWidthU; simp [hk]

/-- One factor of the design against the same factor of the `f = 1` design: `factor_D = rr · factor_des`. -/
lemma factor_step (α : ℝ) {K n : ℕ} (hn : K ≤ n) {η : ℝ} (hη : 0 < η) {ν k : ℕ} (hν : K < ν) (hk3 : 3 ≤ k)
    (hkν : k ≠ ν) :
    airyProdFactor (siteSeq α K n) (widthSeq n η) k (airyZero ν : ℂ) =
      ((rrFac α K η ν k : ℝ) : ℂ) * airyProdFactor (designSiteU (n + 2)) (designWidthU (n + 2) η) k
        (airyZero ν : ℂ) := by
  rw [airyProdFactor_airyZero, airyProdFactor_airyZero, widthSeq_of_ge n η hk3]
  by_cases hkK : k ≤ K
  · rw [siteSeq_of_le α hkK hk3 hn, designSiteU_of_le (by omega), designWidthU_of_le η (by omega)]
    simp only [rrFac, hkK, ↓reduceIte]
    have hd0 : 0 < (airyZero ν - airyZero k) ^ 2 + (η * gapWKB k) ^ 2 := by
      have := gapWKB_pos (by omega : 1 ≤ k)
      positivity
    have hd1 : (airyZero ν - airyZero k) ^ 2 ≠ 0 := by
      have : airyZero ν ≠ airyZero k := fun h =>
        hkν (airyZero_injective_on (by omega) (by omega) h.symm)
      exact pow_ne_zero 2 (sub_ne_zero.mpr this)
    rw [← Complex.ofReal_mul]
    congr 1
    field_simp
  · rw [siteSeq_of_gt α (by omega) hk3]
    simp [rrFac, hkK]

lemma tailExcept_two_eq (α : ℝ) {K : ℕ} (hK : 3 ≤ K) {n : ℕ} (hn : K ≤ n) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    {ν : ℕ} (hν : K < ν) :
    airyProdTailExcept 2 ν (siteSeq α K n) (widthSeq n η) (airyZero ν : ℂ) =
      ((∏ k ∈ Finset.Icc 3 K, rrFac α K η ν k : ℝ) : ℂ) *
        airyProdTailExcept 2 ν (designSiteU (n + 2)) (designWidthU (n + 2) η) (airyZero ν : ℂ) := by
  have hne : ∀ k : ℕ, 2 < k → k ≠ ν → (airyZero ν : ℂ) ≠ (airyZero k : ℂ) := fun k hk hkν =>
    airyZero_ne_cast (by omega) (by omega) hkν
  have hpD := hasProd_airyProdTailExcept (f := 2) (n := ν) (u := (airyZero ν : ℂ))
    (tailHyp_siteSeq α K n hη.le hη1) hne
  have hpd := hasProd_airyProdTailExcept (f := 2) (n := ν) (u := (airyZero ν : ℂ))
    (tailHyp_two_of_one (design_tail_hypothesis (n + 2) η)) hne
  have hrr : HasProd (fun m : ℕ => ((rrFac α K η ν (3 + m) : ℝ) : ℂ))
      ((∏ k ∈ Finset.Icc 3 K, rrFac α K η ν k : ℝ) : ℂ) := by
    have h : HasProd (fun m : ℕ => ((rrFac α K η ν (3 + m) : ℝ) : ℂ))
        (∏ m ∈ Finset.range (K - 2), ((rrFac α K η ν (3 + m) : ℝ) : ℂ)) :=
      hasProd_prod_of_ne_finset_one (fun m hm => by
        simp only [Finset.mem_range] at hm
        simp [rrFac, show ¬(3 + m ≤ K) by omega])
    rw [prod_Icc_three_eq_range]
    push_cast
    exact h
  have hstep : (fun m : ℕ => if 2 + 1 + m = ν then (1 : ℂ) else
      airyProdFactor (siteSeq α K n) (widthSeq n η) (2 + 1 + m) (airyZero ν : ℂ)) =
      (fun m : ℕ => ((rrFac α K η ν (3 + m) : ℝ) : ℂ) * (if 2 + 1 + m = ν then (1 : ℂ) else
      airyProdFactor (designSiteU (n + 2)) (designWidthU (n + 2) η) (2 + 1 + m) (airyZero ν : ℂ))) := by
    funext m
    have e3 : 2 + 1 + m = 3 + m := by omega
    rw [e3]
    by_cases hkν : 3 + m = ν
    · simp only [hkν, ↓reduceIte, mul_one]
      simp [rrFac, show ¬(ν ≤ K) by omega]
    · simp only [hkν, ↓reduceIte]
      exact factor_step α hn hη hν (by omega) hkν
  have h : HasProd (fun m : ℕ => ((rrFac α K η ν (3 + m) : ℝ) : ℂ) * (if 2 + 1 + m = ν then (1 : ℂ) else
      airyProdFactor (designSiteU (n + 2)) (designWidthU (n + 2) η) (2 + 1 + m) (airyZero ν : ℂ)))
      (((∏ k ∈ Finset.Icc 3 K, rrFac α K η ν k : ℝ) : ℂ) *
        airyProdTailExcept 2 ν (designSiteU (n + 2)) (designWidthU (n + 2) η) (airyZero ν : ℂ)) := hrr.mul hpd
  rw [← hstep] at h
  exact hpD.unique h

/-- **The node value of the design is a bounded multiple of `Π_ν(0)`**: for `ν > K`,
`nodeC D ν = G_ν · Π_ν(0)` where `Π_ν(0)` is the weight of the `f = 1` design `D(n + 2, η, 0)` of `ut:V`. -/
theorem nodeC_eq_Gnu (α : ℝ) {K : ℕ} (hK : 3 ≤ K) (q : ℝ) {n : ℕ} (hn : K ≤ n) {η : ℝ} (hη : 0 < η)
    (hη1 : η ≤ 1) {ν : ℕ} (hν : K < ν) :
    nodeC (clarkNode α 1 - η) q (siteSeq α K n) (widthSeq n η) ν =
      ((Gnu α K q η ν * designPi0 (n + 2) η ν : ℝ) : ℂ) := by
  have hν3 : 3 ≤ ν := by omega
  have hE1 := tailExcept_one_eq (n + 2) (by omega) η hν3
  obtain ⟨-, hE1T⟩ := designPi0_hasProd (n + 2) η (n := ν) (by omega)
  have hE2D := tailExcept_two_eq α hK hn hη hη1 hν
  have hf2 : ((((airyZero ν - airyZero 2) ^ 2 + (η * gapWKB 2) ^ 2) / (airyZero ν - airyZero 2) ^ 2 : ℝ) : ℂ)
      ≠ 0 := by
    have hsq : 0 < (airyZero ν - airyZero 2) ^ 2 := by
      have : airyZero ν ≠ airyZero 2 := fun h => by
        have := airyZero_injective_on (by omega : 1 ≤ ν) (by omega : 1 ≤ 2) h
        omega
      have := sub_ne_zero.mpr this
      positivity
    have := gapWKB_pos (by omega : 1 ≤ 2)
    exact Complex.ofReal_ne_zero.mpr (by positivity)
  have hE2 : airyProdTailExcept 2 ν (designSiteU (n + 2)) (designWidthU (n + 2) η) (airyZero ν : ℂ) =
      ((((∏' m : ℕ, if m + 2 = ν then 1 else designRealFactor (n + 2) η ν (m + 2)) /
        (((airyZero ν - airyZero 2) ^ 2 + (η * gapWKB 2) ^ 2) / (airyZero ν - airyZero 2) ^ 2)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_div, eq_div_iff hf2, mul_comm, ← hE1T, hE1]
  have hIcc : (Finset.Icc 1 2).erase ν = Finset.Icc 1 2 := by
    refine Finset.erase_eq_of_notMem ?_
    simp only [Finset.mem_Icc]; omega
  have hprod12 : ∏ k ∈ Finset.Icc 1 2, ((airyZero ν : ℂ) - airyZero k) ^ 2 =
      (((airyZero ν - airyZero 1) ^ 2 * (airyZero ν - airyZero 2) ^ 2 : ℝ) : ℂ) := by
    have : Finset.Icc 1 2 = {1, 2} := by decide
    rw [this, Finset.prod_pair (by norm_num)]
    push_cast; rfl
  have hSν := siteSeq_of_gt α hν hν3 (n := n)
  have hWν := widthSeq_of_ge n η hν3
  unfold nodeC
  simp only [hν3, ↓reduceIte]
  rw [hIcc, hprod12, hE2D, hE2, hSν, hWν]
  unfold designPi0 Gnu
  have habs : |airyZero ν - airyZero 1| = airyZero 1 - airyZero ν := by
    rw [abs_sub_comm, abs_of_pos]
    have := airyZero_lt_of_lt (n := 1) (m := ν) le_rfl (by omega)
    linarith
  rw [habs]
  have hu1 : airyZero 1 - airyZero ν ≠ 0 := by
    have := airyZero_lt_of_lt (n := 1) (m := ν) le_rfl (by omega)
    intro h; linarith
  have hu2 : airyZero ν - airyZero 2 ≠ 0 := by
    have := airyZero_lt_of_lt (n := 2) (m := ν) (by norm_num) (by omega)
    intro h; linarith
  have hu1' : airyZero ν - airyZero 1 ≠ 0 := by intro h; apply hu1; linarith
  have hc2pos : 0 < (airyZero ν - airyZero 2) ^ 2 + (η * gapWKB 2) ^ 2 := by
    have := gapWKB_pos (by omega : 1 ≤ 2)
    have hsq : 0 < (airyZero ν - airyZero 2) ^ 2 := by positivity
    positivity
  generalize (∏' m : ℕ, if m + 2 = ν then 1 else designRealFactor (n + 2) η ν (m + 2)) = T
  generalize (∏ k ∈ Finset.Icc 3 K, rrFac α K η ν k) = ρ
  generalize ((airyZero ν - airyZero 2) ^ 2 + (η * gapWKB 2) ^ 2) = c2 at hc2pos ⊢
  have hu1c : ((airyZero 1 : ℝ) : ℂ) - (airyZero ν : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sub]; exact_mod_cast hu1
  have hu2c : ((airyZero ν : ℝ) : ℂ) - (airyZero 2 : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sub]; exact_mod_cast hu2
  have hu1'c : ((airyZero ν : ℝ) : ℂ) - (airyZero 1 : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sub]; exact_mod_cast hu1'
  have hc2c : (c2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc2pos.ne'
  push_cast
  field_simp

lemma pi0_summable (N : ℕ) (η : ℝ) : Summable (fun i : ℕ => designPi0 N η (i + 2)) := by
  have h12 : 0 < |airyZero 1 - airyZero 2| := by
    have := airyZero_lt_of_lt (n := 1) (m := 2) le_rfl (by norm_num)
    rw [abs_of_pos (by linarith)]; linarith
  exact (lemma_V_identity N η 0 le_rfl h12).2.2.1

lemma pi0_tail_le (N : ℕ) (η : ℝ) (k : ℕ) :
    ∑' i : ℕ, designPi0 N η (i + k + 2) ≤ designE0 N η := by
  have hsum := pi0_summable N η
  have h := hsum.sum_add_tsum_nat_add k
  have hnn : 0 ≤ ∑ i ∈ Finset.range k, designPi0 N η (i + 2) :=
    Finset.sum_nonneg fun i _ => designPi0_nonneg N η (by omega)
  unfold designE0
  linarith

/-- The tail `Σ_{ν > K} Π_ν(0)` is summable and bounded by `E_0`. -/
lemma pi0_tail (N : ℕ) (η : ℝ) {K : ℕ} (hK : 3 ≤ K) :
    HasSum (fun m : ℕ => designPi0 N η (K + 1 + m)) (∑' m : ℕ, designPi0 N η (m + (K - 1) + 2)) ∧
      ∑' m : ℕ, designPi0 N η (m + (K - 1) + 2) ≤ designE0 N η := by
  have hsh : Summable (fun m : ℕ => designPi0 N η (m + (K - 1) + 2)) :=
    (summable_nat_add_iff (f := fun i : ℕ => designPi0 N η (i + 2)) (K - 1)).2 (pi0_summable N η)
  have hfun : (fun m : ℕ => designPi0 N η (K + 1 + m)) = fun m : ℕ => designPi0 N η (m + (K - 1) + 2) := by
    funext m
    congr 1; omega
  exact ⟨by rw [hfun]; exact hsh.hasSum, pi0_tail_le N η (K - 1)⟩

/-- **The node tail of the designs is `O(η² + N^{-1/3})`** (`ut:E`): for `n ≥ K`, `N = n + 2 ≥ N₀`,
`0 < η ≤ 1/4`, `|Σ_{ν > K} Re nodeC D ν| ≤ M (η² + N^{-1/3})`. -/
theorem tail_sum_bound (α : ℝ) {K : ℕ} (hK : 3 ≤ K) (q : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∃ N₀ : ℕ, ∀ n : ℕ, K ≤ n → N₀ ≤ n + 2 → ∀ η : ℝ, 0 < η → η ≤ 1 / 4 →
      |∑' m : ℕ, (nodeC (clarkNode α 1 - η) q (siteSeq α K n) (widthSeq n η) (K + 1 + m)).re| ≤
        M * (η ^ 2 + ((n + 2 : ℕ) : ℝ) ^ (-(1 / 3 : ℝ))) := by
  obtain ⟨M, hM0, hM⟩ := Gnu_bound α hK q
  obtain ⟨C, hC, N₀, hN₀, hE⟩ := lemma_E
  refine ⟨M * C, by positivity, N₀, fun n hn hNn η hη hη1 => ?_⟩
  have hE3 := (hE (n + 2) hNn η hη.le hη1).2.2.1
  obtain ⟨hg0, hgE⟩ := pi0_tail (n + 2) η hK
  have hg := hg0.mul_left M
  have hterm : ∀ m : ℕ, ‖(nodeC (clarkNode α 1 - η) q (siteSeq α K n) (widthSeq n η) (K + 1 + m)).re‖ ≤
      M * designPi0 (n + 2) η (K + 1 + m) := by
    intro m
    rw [nodeC_eq_Gnu α hK q hn hη (by linarith) (by omega), Complex.ofReal_re, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (designPi0_nonneg (n + 2) η (by omega))]
    exact mul_le_mul_of_nonneg_right (hM (K + 1 + m) (by omega) η hη hη1) (designPi0_nonneg (n + 2) η (by omega))
  have h1 := tsum_of_norm_bounded hg hterm
  rw [Real.norm_eq_abs] at h1
  refine h1.trans ?_
  calc M * ∑' m : ℕ, designPi0 (n + 2) η (m + (K - 1) + 2) ≤ M * designE0 (n + 2) η :=
        mul_le_mul_of_nonneg_left hgE hM0
    _ ≤ M * (C * (η ^ 2 + ((n + 2 : ℕ) : ℝ) ^ (-(1 / 3 : ℝ)))) :=
        mul_le_mul_of_nonneg_left hE3 hM0
    _ = M * C * (η ^ 2 + ((n + 2 : ℕ) : ℝ) ^ (-(1 / 3 : ℝ))) := by ring

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.NegativeVacuum.nodeC_eq_Gnu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nodeC_eq_Gnu

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.NegativeVacuum.tail_sum_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tail_sum_bound

end FormalResearch.ModularBootstrap.TwoLevel.NegativeVacuum
