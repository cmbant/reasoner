module

public import FormalResearch.Special.DiscreteAiryKappaSharpNode3

/-!
# Sharp `κ`: the choice of the band parameters (plan K1, sharp constant, step 13)

For fixed data `K` (`KsfConst`: the constants of the chart, of the order-sharp matching and of the left bound) the explicit error bounds of the node theorem
(`ksf_node`) are `Ē = K_E δ`, `S̄ = K_S δ`, `ā = (2A + 3δ)/q_*`, `l̄ = 8 C_l (A + δ/A)`, `z̄ = K_Z A + K_3 δ`, `w̄ = 50δ/A³`; their combination
`max(θ₁, θ₂) ≤ θ_A A + θ_δ(A) δ =: kfTheta`.  `ksfin_choose`: for every `B₀ > 0` there are `A, δ₁ > 0` such that for all `0 < δ ≤ δ₁`
the geometric requirements (`KsfGeo`) and `kfTheta K A δ ≤ B₀` hold.

**Claim class: proved** (real analysis of explicit expressions).
-/

@[expose] public section

namespace FormalResearch.Special

/-- The fixed constants of a node family (chart, order-sharp matching, left bound, Hahn coefficients). -/
structure KsfConst where
  x : ℝ
  qs : ℝ
  rs : ℝ
  r : ℝ
  c1 : ℝ
  c1s : ℝ
  c2 : ℝ
  c2s : ℝ
  gmax : ℝ
  C : ℝ
  CL : ℝ
  β : ℝ
  mσ : ℝ
  K1 : ℝ
  εe : ℝ

/-- Positivity of the constants. -/
structure KsfConst.Pos (K : KsfConst) : Prop where
  hx : 0 < K.x
  hqs : 0 < K.qs
  hqs1 : K.qs < 1
  hrs : 0 < K.rs
  hr : 0 < K.r
  hc1 : 0 < K.c1
  hc1s : 0 < K.c1s
  hc2 : 0 < K.c2
  hc2s : 0 < K.c2s
  hg : 0 < K.gmax
  hC : 0 < K.C
  hCL : 1 ≤ K.CL
  hβ : 0 ≤ K.β
  hmσ : 0 ≤ K.mσ
  hK1 : 1 ≤ K.K1
  hεe : 0 < K.εe
  hεe1 : K.εe ≤ 1

noncomputable def kfρ0 (K : KsfConst) : ℝ := √(K.c2s * (1 / K.qs + 1))

noncomputable def kfKZ (K : KsfConst) : ℝ :=
  2 * K.gmax ^ 2 * (kfρ0 K / Real.pi + 2 * K.c2 * kfρ0 K ^ 2) / K.c1

noncomputable def kfK3 (K : KsfConst) : ℝ := kszK3 K.c1 K.gmax K.C (1 / K.qs + 4)

noncomputable def kfKY (K : KsfConst) (A : ℝ) : ℝ := (2 * K.qs / (K.c1s * A ^ 2)) ^ (3 / 2 : ℝ)

noncomputable def kfKE (K : KsfConst) (A : ℝ) : ℝ :=
  6 * ((3 / (A * K.x ^ 2) + 2 * (1 + 3 * K.β / A ^ 4) / K.x ^ 4) / K.x) / A ^ 2 + 8 * (K.C + 1 + kfKY K A / 8) / A

noncomputable def kfS1 (K : KsfConst) (A : ℝ) : ℝ := 200 * (1 + 2 * (3 * K.β + K.mσ) / A ^ 2) / (K.x * A ^ 9)

noncomputable def kfθA (K : KsfConst) : ℝ := 2 / K.qs + 2 * kfKZ K + 16 * K.CL

noncomputable def kfθδ (K : KsfConst) (A : ℝ) : ℝ :=
  (2 * kfKE K A + 3 / K.qs + 20 * kfS1 K A + 50 / A ^ 3) +
    (24 * kfS1 K A + 3 * kfKE K A + 2 * kfK3 K + 16 * K.CL / A + 100 / A ^ 3)

noncomputable def kfTheta (K : KsfConst) (A δ : ℝ) : ℝ := kfθA K * A + kfθδ K A * δ

/-- The geometric requirements on `(A, δ)` (`h = δ³`). -/
structure KsfGeo (K : KsfConst) (A δ : ℝ) : Prop where
  p1 : δ ≤ 1
  p2 : δ ≤ K.qs / 8
  p3 : A ^ 2 + 2 * δ ≤ K.εe
  p4 : A ^ 2 / K.qs + 3 * δ ≤ min K.rs K.r
  p5 : 2 * K.qs * δ ^ 2 ≤ K.c1s * A ^ 2
  p6 : K.K1 * δ ^ 3 ≤ A ^ 2
  p7 : δ ≤ A ^ 2

lemma kfKZ_nonneg {K : KsfConst} (P : K.Pos) : 0 ≤ kfKZ K := by
  have := P.hc1; have := P.hc2; have := P.hg
  unfold kfKZ kfρ0
  positivity

lemma kfθA_pos {K : KsfConst} (P : K.Pos) : 0 < kfθA K := by
  have := kfKZ_nonneg P; have := P.hqs; have := P.hCL
  unfold kfθA
  positivity

lemma kfθδ_pos {K : KsfConst} (P : K.Pos) {A : ℝ} (hA : 0 < A) : 0 < kfθδ K A := by
  have := P.hx; have := P.hqs; have := P.hCL; have := P.hβ; have := P.hmσ; have := P.hC; have := P.hc1s
  have h3 : 0 ≤ kfK3 K := by
    unfold kfK3 kszK3
    have := P.hc1; have := P.hg
    positivity
  have hKE : 0 ≤ kfKE K A := by
    unfold kfKE kfKY
    positivity
  have hS : 0 ≤ kfS1 K A := by
    unfold kfS1
    positivity
  unfold kfθδ
  have : 0 < 50 / A ^ 3 := by positivity
  have : 0 < 100 / A ^ 3 := by positivity
  have : 0 ≤ 16 * K.CL / A := by positivity
  have : 0 < 3 / K.qs := by positivity
  linarith

/-- **The choice of the band parameters**. -/
theorem ksfin_choose {K : KsfConst} (P : K.Pos) {B0 : ℝ} (hB0 : 0 < B0) :
    ∃ A δ1 : ℝ, 0 < A ∧ A ≤ K.qs / 2 ∧ A ≤ 1 ∧ 0 < δ1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ1 → KsfGeo K A δ ∧ kfTheta K A δ ≤ B0 := by
  have hqs := P.hqs
  have hmr : 0 < min K.rs K.r := lt_min P.hrs P.hr
  have hθA := kfθA_pos P
  set A : ℝ := min (K.qs / 2) (min 1 (min (K.εe / 2) (min (min K.rs K.r / 2) (B0 / (2 * kfθA K))))) with hAdef
  have hA0 : 0 < A := by
    refine lt_min (by positivity) (lt_min one_pos (lt_min (by have := P.hεe; positivity) (lt_min (by positivity) (by positivity))))
  have hA1 : A ≤ K.qs / 2 := min_le_left _ _
  have hA2 : A ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hA3 : A ≤ K.εe / 2 := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hA4 : A ≤ min K.rs K.r / 2 := (((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hA5 : A ≤ B0 / (2 * kfθA K) := (((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hθδ := kfθδ_pos P hA0
  have hK1 := P.hK1
  set δ1 : ℝ := min 1 (min (K.qs / 8) (min (K.εe / 4) (min (min K.rs K.r / 12) (min (A ^ 2) (min (K.c1s * A ^ 2 / (2 * K.qs))
    (min (A ^ 2 / K.K1) (B0 / (2 * kfθδ K A))))))))  with hδ1def
  have hδ10 : 0 < δ1 := by
    have := P.hc1s
    refine lt_min one_pos (lt_min (by positivity) (lt_min (by have := P.hεe; positivity) (lt_min (by positivity)
      (lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity) (by positivity)))))))
  refine ⟨A, δ1, hA0, hA1, hA2, hδ10, fun δ hδ hδ1 => ?_⟩
  have d1 : δ ≤ 1 := hδ1.trans (min_le_left _ _)
  have d2 : δ ≤ K.qs / 8 := hδ1.trans ((min_le_right _ _).trans (min_le_left _ _))
  have d3 : δ ≤ K.εe / 4 := hδ1.trans (((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _))
  have d4 : δ ≤ min K.rs K.r / 12 := hδ1.trans ((((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _))
  have d5 : δ ≤ A ^ 2 := hδ1.trans (((((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _))
  have d6 : δ ≤ K.c1s * A ^ 2 / (2 * K.qs) := hδ1.trans ((((((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _))
  have d7 : δ ≤ A ^ 2 / K.K1 := hδ1.trans (((((((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _))
  have d8 : δ ≤ B0 / (2 * kfθδ K A) := hδ1.trans (((((((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _))
  have hδ3 : δ ^ 3 ≤ δ := by nlinarith [pow_pos hδ 2]
  refine ⟨⟨d1, d2, ?_, ?_, ?_, ?_, d5⟩, ?_⟩
  · have : A ^ 2 ≤ A := by nlinarith
    linarith
  · have h1 : A ^ 2 / K.qs ≤ A := by
      rw [div_le_iff₀ hqs]; nlinarith
    have := min_le_left K.rs K.r
    linarith
  · have h1 : δ ^ 2 ≤ δ := by nlinarith
    have h2 : 2 * K.qs * δ ≤ K.c1s * A ^ 2 := by
      rw [le_div_iff₀ (by positivity)] at d6
      linarith
    nlinarith [P.hqs]
  · have h1 : K.K1 * δ ≤ A ^ 2 := by
      rw [le_div_iff₀ (by linarith)] at d7
      linarith
    nlinarith [P.hK1]
  · unfold kfTheta
    have e1 : kfθA K * A ≤ B0 / 2 := by
      have := mul_le_mul_of_nonneg_left hA5 hθA.le
      have e : kfθA K * (B0 / (2 * kfθA K)) = B0 / 2 := by field_simp
      linarith
    have e2 : kfθδ K A * δ ≤ B0 / 2 := by
      have := mul_le_mul_of_nonneg_left d8 hθδ.le
      have e : kfθδ K A * (B0 / (2 * kfθδ K A)) = B0 / 2 := by field_simp
      linarith
    linarith

/-- info: 'FormalResearch.Special.ksfin_choose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.ksfin_choose

end FormalResearch.Special
