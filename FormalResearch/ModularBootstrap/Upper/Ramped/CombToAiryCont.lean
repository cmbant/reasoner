module

public import FormalResearch.ModularBootstrap.Upper.Ramped.CombToAiryAsm3

/-!
# Continuity of the three sides of Proposition 1.2(2) in `x` (`rem:P1.2`: "extends to the real zeros by continuity")

`x ↦ ‖B_D(x)‖`, `x ↦ 𝒦_*(x) = 𝒦(x, ξ_*)` and `x ↦ ‖W_D(-κτ(x)/λ)‖` are continuous (`continuousAt_normComb`,
`continuousAt_langerK_xiStar`, `continuousAt_normAiryW`), and an inequality between continuous functions on
`[a, b]` that holds off a countable set holds everywhere (`le_of_forall_notMem_countable`).
-/

@[expose] public section

open Filter Topology Set Finset MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.ModularBootstrap.Upper.Comb FormalResearch.ModularBootstrap.Upper.Window
  FormalResearch.ModularBootstrap.Upper.Design

lemma langerD_comm (x y : ℝ) : langerD x y = langerD y x := by
  by_cases h : y = x
  · rw [h]
  · rw [langerD_of_ne h, langerD_of_ne (Ne.symm h)]
    have h1 : x - y ≠ 0 := sub_ne_zero.2 (Ne.symm h)
    have h2 : y - x ≠ 0 := sub_ne_zero.2 h
    field_simp
    ring

/-- `x ↦ 𝒦_*(x) = 𝒦(x, ξ_*)` is continuous on `(0, ∞)`. -/
lemma continuousAt_langerK_xiStar {x : ℝ} (hx : 0 < x) :
    ContinuousAt (fun z : ℝ => langerK z xiStar) x := by
  have hD : ContinuousAt (fun z : ℝ => langerD z xiStar) x := by
    have : (fun z : ℝ => langerD z xiStar) = langerD xiStar := funext fun z => langerD_comm z xiStar
    rw [this]
    exact (contDiffAt_langerD 0 xiStar_pos hx).continuousAt
  have hT : ContinuousAt (fun z : ℝ => langerT (z - xiStar)) x :=
    ((contDiff_langerT 0).continuous.comp (continuous_id.sub continuous_const)).continuousAt
  have hQ : ContinuousAt (fun z : ℝ => langerQ2 z xiStar) x :=
    hT.div hD (langerD_pos hx xiStar_pos).ne'
  have htanh : ContinuousAt (fun z : ℝ => Real.tanh (π * (z + xiStar) / 2)) x :=
    ((contDiff_tanhHalf (n := 0)).continuous.comp (continuous_id.add continuous_const)).continuousAt
  have hpos : 0 < Real.tanh (π * (x + xiStar) / 2) :=
    tanh_pos_of_pos (by have := Real.pi_pos; have := xiStar_pos; positivity)
  unfold langerK
  exact (hQ.log (langerQ2_pos hx xiStar_pos).ne').add (htanh.log hpos.ne')

lemma continuousAt_sigmaOf (c' : ℝ) {x : ℝ} (hx : 0 < x) :
    ContinuousAt (fun z : ℝ => sigmaOf c' z) x := by
  unfold sigmaOf
  exact (((contDiffOn_langerTau 0).continuousOn.continuousAt (Ioi_mem_nhds hx))).div_const _

/-- `x ↦ ‖W_D(-κ σ(x))‖` is continuous on `(0, ∞)`. -/
lemma continuousAt_normAiryW {Csh csep : ℝ} {σ η : ℕ → ℝ} (h : CombDesignHyp Csh csep σ η)
    (c' : ℝ) {x : ℝ} (hx : 0 < x) :
    ContinuousAt (fun z : ℝ => ‖designAiryW σ η (-kappaAiry * sigmaOf c' z)‖) x := by
  have hCt : 0 < max |Csh| 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hdiff := airyWindowProd_differentiable 1 le_rfl (-kappaAiry * σ 1)
    (fun k => -kappaAiry * σ k) (fun k => kappaAiry * epsHat η k)
    (airyProdTailHypothesis_of_tail (f := 1) (N := 1) le_rfl hCt (design_tail h))
  have hc : Continuous (designAiryW σ η ∘ (fun u : ℝ => u)) :=
    hdiff.continuous.comp Complex.continuous_ofReal
  have hs := (continuousAt_sigmaOf c' hx).const_mul (-kappaAiry)
  exact (hc.continuousAt.comp hs).norm

/-- `x ↦ ‖B_D(x)‖` is continuous on `ℝ`. -/
lemma continuousAt_normComb {Csh csep : ℝ} {c' : ℝ} (hc' : 0 < c') {σ η : ℕ → ℝ}
    (h : CombDesignHyp Csh csep σ η) (hw : ∀ k : ℕ, 2 ≤ k → |widthE c' η k| ≤ 1 / 8) (x : ℝ) :
    ContinuousAt (fun z : ℝ => ‖combBD c' σ η (z : ℂ)‖) x := by
  have hχ0 : ∀ m : ℕ, 0 ≤ siteX c' σ (m + 2) := fun m =>
    xiStar_pos.le.trans (xiStar_le_siteX hc' (h.nonneg _ (by omega)))
  have hε : ∀ m : ℕ, |widthE c' η (m + 2)| ≤ 1 / 8 := fun m => hw _ (by omega)
  have hsum := summable_exp_siteX hc' h
  have hprod := comb_pairProd_differentiableOn (fun m => siteX c' σ (m + 2))
    (fun m => widthE c' η (m + 2)) hχ0 hε hsum
  have hopen : IsOpen {b : ℂ | |b.im| < 7 / 8} :=
    isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  have hmem : ((x : ℂ)) ∈ {b : ℂ | |b.im| < 7 / 8} := by simp
  have hP : ContinuousAt (fun b : ℂ => ∏' k : ℕ, (blaschkeT ((siteX c' σ (k + 2) : ℂ) +
      (widthE c' η (k + 2) : ℂ) * Complex.I) b * blaschkeT ((siteX c' σ (k + 2) : ℂ) -
      (widthE c' η (k + 2) : ℂ) * Complex.I) b)) (x : ℂ) :=
    (hprod.differentiableAt (hopen.mem_nhds hmem)).continuousAt
  have hT : ContinuousAt (blaschkeT (siteX c' σ 1 : ℂ)) (x : ℂ) :=
    (differentiableAt_blaschkeT (ζ := (siteX c' σ 1 : ℂ)) (b := (x : ℂ)) (by simp)).continuousAt
  have hB : ContinuousAt (fun b : ℂ => combBD c' σ η b) (x : ℂ) := by
    unfold combBD
    exact hT.mul hP
  exact (hB.comp Complex.continuous_ofReal.continuousAt).norm

/-- An inequality between functions continuous on `[a, b]` that holds off a countable set holds on `[a, b]`. -/
lemma le_of_forall_notMem_countable {a b : ℝ} (hab : a < b) {S : Set ℝ} (hS : S.Countable)
    {f g : ℝ → ℝ} (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (h : ∀ x ∈ Icc a b, x ∉ S → f x ≤ g x) : ∀ x ∈ Icc a b, f x ≤ g x := by
  intro x hx
  have hdense : Dense Sᶜ := hS.dense_compl ℝ
  have hcl : x ∈ closure (Icc a b ∩ Sᶜ) := by
    rw [mem_closure_iff]
    intro o ho hxo
    have hx' : x ∈ closure (Ioo a b) := by rw [closure_Ioo hab.ne]; exact hx
    obtain ⟨z, hzo, hzI⟩ := mem_closure_iff.1 hx' o ho hxo
    obtain ⟨y, hyS, hyU⟩ := hdense.exists_mem_open (ho.inter isOpen_Ioo) ⟨z, hzo, hzI⟩
    exact ⟨y, hyU.1, Ioo_subset_Icc_self hyU.2, hyS⟩
  have hsub : closure (Icc a b ∩ Sᶜ) ⊆ Icc a b :=
    closure_minimal Set.inter_subset_left isClosed_Icc
  exact le_on_closure (fun y hy => h y hy.1 hy.2) (hf.mono hsub) (hg.mono hsub) hcl

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.continuousAt_langerK_xiStar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms continuousAt_langerK_xiStar

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.continuousAt_normAiryW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms continuousAt_normAiryW

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.continuousAt_normComb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms continuousAt_normComb

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.le_of_forall_notMem_countable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms le_of_forall_notMem_countable

end FormalResearch.ModularBootstrap.Upper.Ramped
