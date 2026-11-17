module

public import FormalResearch.Special.DiscreteAiryKappaSharpParam2

/-!
# Sharp `κ`: the node theorem with the parameters discharged (plan K1, sharp constant, step 15)

`ksfin_node`: for a node with the data of the order-sharp theorem and band parameters `(A, δ)` satisfying `KsfGeo` and `kfTheta ≤ B₀`
(`B₀ ≤ 1/5`) we get `|κ²δ/2 - 1| ≤ 2 kfTheta`, hence `|κ²δ - 2| ≤ 4 B₀`.

**Claim class: proved.**
-/

@[expose] public section

open Finset Set FormalResearch.Racah FormalResearch.Racah.P3 FormalResearch.Wigner

namespace FormalResearch.Special

/-- The constants of a node family built from the chart data and the left bound. -/
noncomputable def ksfK (M σ : ℤ) (x : ℝ) (rs r c1 c1s c2 c2s gmax C e : ℝ) (K0 : ℕ) (K1 : ℝ) : KsfConst where
  x := x
  qs := √(1 - x ^ 2)
  rs := rs
  r := r
  c1 := c1
  c1s := c1s
  c2 := c2
  c2s := c2s
  gmax := gmax
  C := C
  CL := ke_C (M : ℝ) (σ : ℝ) x e K0
  β := kl_beta (M : ℝ) (σ : ℝ)
  mσ := |(M : ℝ) * (σ : ℝ)|
  K1 := K1
  εe := √(1 - e ^ 2)

/-- The two combinations of the explicit bars are bounded by `kfTheta`; nonnegativity of the constants. -/
lemma ksfin_theta {K : KsfConst} (P : K.Pos) {A δ : ℝ} (hA : 0 < A) (hδ : 0 < δ) :
    2 * (kfKE K A * δ) + (2 * A + 3 * δ) / K.qs + 20 * (kfS1 K A * δ) + 50 * δ / A ^ 3 ≤ kfTheta K A δ ∧
    24 * (kfS1 K A * δ) + 3 * (kfKE K A * δ) + 2 * (kfKZ K * A + kfK3 K * δ) + 2 * (8 * K.CL * (A + δ / A)) + 2 * (50 * δ / A ^ 3) ≤
      kfTheta K A δ ∧ 0 ≤ kfKE K A ∧ 0 ≤ kfS1 K A ∧ 0 ≤ kfK3 K ∧ 0 ≤ kfKZ K := by
  have := P.hx; have := P.hqs; have := P.hCL; have := P.hβ; have := P.hmσ; have := P.hC; have := P.hc1s
  have hKZ := kfKZ_nonneg P
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
  refine ⟨?_, ?_, hKE, hS, h3, hKZ⟩
  · unfold kfTheta kfθA kfθδ
    have e1 : (2 * A + 3 * δ) / K.qs = 2 / K.qs * A + 3 / K.qs * δ := by ring
    have e2 : 50 * δ / A ^ 3 = 50 / A ^ 3 * δ := by ring
    have h4 : 0 ≤ 2 * kfKZ K * A := by positivity
    have h5 : 0 ≤ 16 * K.CL * A := by positivity
    have h6 : 0 ≤ (24 * kfS1 K A + 3 * kfKE K A + 2 * kfK3 K + 16 * K.CL / A + 100 / A ^ 3) * δ := by positivity
    nlinarith [mul_nonneg h4 le_rfl]
  · unfold kfTheta kfθA kfθδ
    have e1 : 2 * (8 * K.CL * (A + δ / A)) = 16 * K.CL * A + 16 * K.CL / A * δ := by ring
    have e2 : 2 * (50 * δ / A ^ 3) = 100 / A ^ 3 * δ := by ring
    have h4 : 0 ≤ 2 / K.qs * A := by positivity
    have h6 : 0 ≤ (2 * kfKE K A + 3 / K.qs + 20 * kfS1 K A + 50 / A ^ 3) * δ := by positivity
    nlinarith

/-- **The node theorem with the parameters discharged.** -/
theorem ksfin_node {M σ N : ℤ} {x : ℚ} {δ r C Cmu ξ0 gmin gmax c1 c2 κmin Cl κ μ σ0 : ℝ} {J m Nw : ℤ}
    {rs c1s c2s A B0 e K1 : ℝ} {K0 : ℕ}
    (hx0 : 0 < (x : ℝ)) (hx1 : (x : ℝ) < 1)
    (d : KkData (hahn3jY M σ N x) (turnX (hrU 1 0 1 (x : ℝ)) (√(1 - (x : ℝ) ^ 2)) (δ ^ 3 / 2) δ)
      (fun k => langerAmp (hrU 1 0 1 (x : ℝ)) (hrA1 1 0) (√(1 - (x : ℝ) ^ 2)) (dalQ (δ ^ 3 / 2) δ k)) N δ (√(1 - (x : ℝ) ^ 2)) r C Cmu
      ξ0 gmin gmax c1 c2 κmin Cl κ μ J m Nw)
    (s : KkSmall δ r C Cmu ξ0 gmin gmax c1 c2 κmin σ0) (Cs : KshChart (x : ℝ) rs c1s c2s)
    (P : (ksfK M σ (x : ℝ) rs r c1 c1s c2 c2s gmax C e K0 K1).Pos)
    (G : KsfGeo (ksfK M σ (x : ℝ) rs r c1 c1s c2 c2s gmax C e K0 K1) A δ)
    (hA0 : 0 < A) (hAq : A ≤ √(1 - (x : ℝ) ^ 2) / 2) (hA1 : A ≤ 1)
    (hθ : kfTheta (ksfK M σ (x : ℝ) rs r c1 c1s c2 c2s gmax C e K0 K1) A δ ≤ B0) (hB0 : B0 ≤ 1 / 5)
    (hxe : (x : ℝ) < e) (he1 : e ≤ 1) (hK0 : kl_K0real (M : ℝ) (σ : ℝ) (x : ℝ) e ≤ (K0 : ℝ))
    (hK1a : kl_beta (M : ℝ) (σ : ℝ) < K1) (hK1b : 3 * kl_beta (M : ℝ) (σ : ℝ) ≤ (x : ℝ) ^ 2 * K1)
    (hK1c : 3 * kl_beta (M : ℝ) (σ : ℝ) ≤ K1 / 2) (hK1d : |(M : ℝ) * (σ : ℝ)| ≤ K1) (hK1e : (K0 : ℝ) ≤ K1) :
    |κ ^ 2 * δ - 2| ≤ 4 * B0 := by
  generalize hK : ksfK M σ (x : ℝ) rs r c1 c1s c2 c2s gmax C e K0 K1 = K at P G hθ
  have hfld : K.x = (x : ℝ) ∧ K.qs = √(1 - (x : ℝ) ^ 2) ∧ K.rs = rs ∧ K.r = r ∧ K.c1 = c1 ∧ K.c1s = c1s ∧ K.c2 = c2 ∧ K.c2s = c2s ∧
      K.gmax = gmax ∧ K.C = C ∧ K.CL = ke_C (M : ℝ) (σ : ℝ) (x : ℝ) e K0 ∧ K.β = kl_beta (M : ℝ) (σ : ℝ) ∧
      K.mσ = |(M : ℝ) * (σ : ℝ)| ∧ K.K1 = K1 ∧ K.εe = √(1 - e ^ 2) := by
    subst hK; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨hKx, hKqs, hKrs, hKr, hKc1, hKc1s, hKc2, hKc2s, hKg, hKC, hKCL, hKβ, hKmσ, hKK1, hKεe⟩ := hfld
  have hδp := s.hδ
  have hh0 : 0 < δ ^ 3 := by positivity
  have hNz : (N : ℝ) = 1 / δ ^ 3 := d.hNz
  have hN1 : 1 ≤ N := d.hNz1
  have hqs : 0 < √(1 - (x : ℝ) ^ 2) := Real.sqrt_pos.2 (by nlinarith only [hx0, hx1])
  have hqs2 : √(1 - (x : ℝ) ^ 2) ^ 2 = 1 - (x : ℝ) ^ 2 := Real.sq_sqrt (by nlinarith only [hx0, hx1])
  have hqs1 : √(1 - (x : ℝ) ^ 2) < 1 := by nlinarith only [hqs2, hx0, hqs]
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := G
  rw [hKqs] at p2
  rw [hKqs, hKrs, hKr] at p4
  rw [hKqs, hKc1s] at p5
  rw [hKεe] at p3
  rw [hKK1] at p6
  have hAq' : A < √(1 - (x : ℝ) ^ 2) := by linarith only [hAq, hqs]
  set qA : ℝ := √(√(1 - (x : ℝ) ^ 2) ^ 2 - A ^ 2) with hqAdef
  have hqA2 : 0 ≤ √(1 - (x : ℝ) ^ 2) ^ 2 - A ^ 2 := by nlinarith only [hAq', hA0, hqs]
  have hqAsq : qA ^ 2 = √(1 - (x : ℝ) ^ 2) ^ 2 - A ^ 2 := Real.sq_sqrt hqA2
  have hqA0 : 0 ≤ qA := Real.sqrt_nonneg _
  have hδ3 : δ ^ 3 ≤ δ := by nlinarith only [pow_pos hδp 2, p1, hδp]
  have hqA45 : √(1 - (x : ℝ) ^ 2) * (4 / 5) ≤ qA := by
    rw [hqAdef]
    apply Real.le_sqrt_of_sq_le
    nlinarith only [mul_self_le_mul_self hA0.le hAq, sq_nonneg (√(1 - (x : ℝ) ^ 2))]
  have hgap : A ^ 2 + 4 * δ ^ 3 ≤ qA := by
    have h1 : A ^ 2 ≤ √(1 - (x : ℝ) ^ 2) / 4 := by
      nlinarith only [mul_self_le_mul_self hA0.le hAq, hqs, hqs1]
    have h2 : 4 * δ ^ 3 ≤ √(1 - (x : ℝ) ^ 2) / 2 := by
      have : δ ≤ √(1 - (x : ℝ) ^ 2) / 8 := p2
      linarith only [this, hδ3]
    linarith only [h1, h2, hqA45, hqs]
  obtain ⟨k0, b, hk0, hkb, hlo, hhi, hb1, hb2⟩ := ksg_index (h := δ ^ 3) (η := A ^ 2) (qA := qA) hh0 (by positivity) hgap
  obtain ⟨nb, hnb⟩ : ∃ nb : ℕ, b = k0 + (nb : ℤ) + 1 := ⟨(b - k0 - 1).toNat, by omega⟩
  have hk0R : (1 : ℝ) ≤ k0 := by exact_mod_cast hk0
  have hb2R : (2 : ℝ) ≤ b := by exact_mod_cast (by omega : (2 : ℤ) ≤ b)
  have hK1k0 : K1 ≤ (k0 : ℝ) := by
    have h6 : K1 * δ ^ 3 ≤ A ^ 2 := p6
    exact le_of_mul_le_mul_right (h6.trans hlo) hh0
  have hK1' : 1 ≤ K1 := by have := P.hK1; rwa [hKK1] at this
  have hkk : (k0 : ℝ) ≤ (k0 : ℝ) ^ 2 := by nlinarith only [hk0R]
  have hk02 : (0 : ℝ) < (k0 : ℝ) ^ 2 := by positivity
  have hqb0 : 0 < kpU (δ ^ 3) b := by unfold kpU; positivity
  obtain ⟨hgeo1, hgeo2⟩ := ksf_geo hqs hA0 hAq' hh0 hqb0 hb1 hb2
  have hqpred : kpU (δ ^ 3) b - δ ^ 3 = kpU (δ ^ 3) (b - 1) := kpU_pred _ b
  have hp4 : A ^ 2 / √(1 - (x : ℝ) ^ 2) + 3 * δ ≤ min rs r := p4
  have hmin1 := min_le_left rs r
  have hmin2 := min_le_right rs r
  have hbw : √(1 - (x : ℝ) ^ 2) - rs ≤ kpU (δ ^ 3) (b - 1) := by linarith only [hgeo2, hqpred, hp4, hmin1, hδ3, hδp]
  have hJb : √(1 - (x : ℝ) ^ 2) - r + δ ^ 3 ≤ kpU (δ ^ 3) (b - 1) := by linarith only [hgeo2, hqpred, hp4, hmin2, hδ3, hδp]
  have hh1 : 1 / (N : ℝ) = δ ^ 3 := by rw [hNz]; field_simp
  obtain ⟨ht1, ht2, hKE0, hS10, hK30, hKZ0⟩ := ksfin_theta P hA0 hδp
  rw [hKqs] at ht1
  rw [hKCL] at ht2
  have hβ0 : 0 ≤ kl_beta (M : ℝ) (σ : ℝ) := by unfold kl_beta; positivity
  have hmσ0 : 0 ≤ |(M : ℝ) * (σ : ℝ)| := abs_nonneg _
  have hCL1 : 1 ≤ ke_C (M : ℝ) (σ : ℝ) (x : ℝ) e K0 := ke_C_ge_one K0 hx0 hxe he1
  have hCpos : 0 < C := by have := P.hC; rwa [hKC] at this
  have hc1spos : 0 < c1s := by have := P.hc1s; rwa [hKc1s] at this
  -- explicit forms of the constants
  have hKE_eq : kfKE K A = 6 * ((3 / (A * (x : ℝ) ^ 2) + 2 * (1 + 3 * kl_beta (M : ℝ) (σ : ℝ) / A ^ 4) / (x : ℝ) ^ 4) / (x : ℝ)) / A ^ 2 +
      8 * (C + 1 + (2 * √(1 - (x : ℝ) ^ 2) / (c1s * A ^ 2)) ^ (3 / 2 : ℝ) / 8) / A := by
    unfold kfKE kfKY; rw [hKx, hKβ, hKC, hKqs, hKc1s]
  have hS1_eq : kfS1 K A = 200 * (1 + 2 * (3 * kl_beta (M : ℝ) (σ : ℝ) + |(M : ℝ) * (σ : ℝ)|) / A ^ 2) / ((x : ℝ) * A ^ 9) := by
    unfold kfS1; rw [hKx, hKβ, hKmσ]
  -- the bars
  have hE : ksfE (x : ℝ) A δ (3 * kl_beta (M : ℝ) (σ : ℝ) / (k0 : ℝ) ^ 2) (C + 1) ((2 * √(1 - (x : ℝ) ^ 2) / (c1s * A ^ 2)) ^ (3 / 2 : ℝ) * δ ^ 3) ≤
      kfKE K A * δ := by
    rw [hKE_eq]
    exact ksfin_E hx0 hA0 hδp p1 hlo (by linarith only [hk0R]) hβ0 (by linarith only [hCpos]) hqs hc1spos
  have hS : ksbSbd M σ (x : ℝ) (1 / (N : ℝ)) A k0 ≤ kfS1 K A * δ := by
    rw [hh1, hS1_eq]
    unfold ksbSbd
    exact ksfin_S hx0 hA0 hδp p1 hlo (by linarith only [hk0R]) hβ0 hmσ0
  have hab : kpU (δ ^ 3) (k0 - 1) / √(1 - (x : ℝ) ^ 2) + √(1 - (kpU (δ ^ 3) (b - 1) / √(1 - (x : ℝ) ^ 2)) ^ 2) ≤
      (2 * A + 3 * δ) / √(1 - (x : ℝ) ^ 2) := by
    refine ksfin_a hqs hqs1.le hA0 hAq hδp p1 p2 ?_ hqAsq hqA0 ?_ ?_
    · have : kpU (δ ^ 3) (k0 - 1) = (k0 : ℝ) * δ ^ 3 - δ ^ 3 / 2 := by unfold kpU; push_cast; ring
      rw [this]; linarith only [hhi, hh0]
    · linarith only [hb2, hqpred]
    · have : kpU (δ ^ 3) (b - 1) < kpU (δ ^ 3) b := by linarith only [hqpred, hh0]
      linarith only [this, hb1]
  have hlb : (k0 : ℝ) * (ke_C (M : ℝ) (σ : ℝ) (x : ℝ) e K0 * (8 / A)) / (N : ℝ) ≤ 8 * ke_C (M : ℝ) (σ : ℝ) (x : ℝ) e K0 * (A + δ / A) := by
    rw [hNz]
    exact ksfin_l hA0 hδp p1 (by linarith only [hCL1]) hhi
  have hzb := ksfin_z P hA0 hA1 hδp p1 p7
  rw [hKc2s, hKqs, hKg, hKc2, hKc1, hKC] at hzb
  have hwb : 50 / A ^ 3 / (N : ℝ) ≤ 50 * δ / A ^ 3 := by
    rw [hNz]
    have e : 50 / A ^ 3 / (1 / δ ^ 3) = 50 * δ ^ 3 / A ^ 3 := by field_simp
    rw [e]
    exact div_le_div_of_nonneg_right (by linarith only [hδ3]) (by positivity)
  have hB0' : kfTheta K A δ ≤ 1 / 5 := hθ.trans hB0
  -- consequences of the smallness
  have n1 : 0 ≤ (2 * A + 3 * δ) / √(1 - (x : ℝ) ^ 2) := by positivity
  have n2 : 0 ≤ kfKE K A * δ := by positivity
  have n3 : 0 ≤ kfS1 K A * δ := by positivity
  have n4 : 0 ≤ 50 * δ / A ^ 3 := by positivity
  have hSbar : kfS1 K A * δ ≤ 1 / 100 := by linarith only [ht1, hB0', n1, n2, n4, n3]
  have hEbar : kfKE K A * δ ≤ 1 / 4 := by linarith only [ht1, hB0', n1, n3, n4, n2]
  have habar : (2 * A + 3 * δ) / √(1 - (x : ℝ) ^ 2) ≤ 1 / 4 := by linarith only [ht1, hB0', n2, n3, n4, n1]
  have hwbar : 50 * δ / A ^ 3 ≤ 1 / 4 := by linarith only [ht1, hB0', n1, n2, n3, n4]
  have hz0 : 0 ≤ kfKZ K * A + kfK3 K * δ := by positivity
  have h1 : 2 * (kfKE K A * δ) + (2 * A + 3 * δ) / √(1 - (x : ℝ) ^ 2) + 20 * (kfS1 K A * δ) + 50 * δ / A ^ 3 ≤ 1 / 2 := by
    linarith only [ht1, hB0']
  have h2 : 24 * (kfS1 K A * δ) + 3 * (kfKE K A * δ) + 2 * (kfKZ K * A + kfK3 K * δ) + 2 * (8 * ke_C (M : ℝ) (σ : ℝ) (x : ℝ) e K0 * (A + δ / A)) +
      2 * (50 * δ / A ^ 3) ≤ 1 / 2 := by
    linarith only [ht2, hB0']
  -- the band conditions
  have hβk : kl_beta (M : ℝ) (σ : ℝ) < (k0 : ℝ) ^ 2 := by linarith only [hK1a, hK1k0, hkk]
  have hηB : 3 * kl_beta (M : ℝ) (σ : ℝ) / (k0 : ℝ) ^ 2 ≤ (x : ℝ) ^ 2 := by
    rw [div_le_iff₀ hk02]
    have h1 : (x : ℝ) ^ 2 * K1 ≤ (x : ℝ) ^ 2 * k0 := mul_le_mul_of_nonneg_left hK1k0 (sq_nonneg _)
    have h2 : (x : ℝ) ^ 2 * k0 ≤ (x : ℝ) ^ 2 * (k0 : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hkk (sq_nonneg _)
    linarith only [hK1b, h1, h2]
  have hηB2 : 3 * kl_beta (M : ℝ) (σ : ℝ) / (k0 : ℝ) ^ 2 ≤ 1 / 2 := by
    rw [div_le_iff₀ hk02]; linarith only [hK1c, hK1k0, hkk]
  have hκB : |(M : ℝ) * (σ : ℝ)| / (k0 : ℝ) ^ 2 ≤ 1 := by
    rw [div_le_one hk02]; linarith only [hK1d, hK1k0, hkk]
  have hKk0 : (K0 : ℤ) ≤ k0 := by
    have : (K0 : ℝ) ≤ k0 := hK1e.trans hK1k0
    exact_mod_cast this
  have hleft : (((k0 : ℝ) + 1) * (1 / (N : ℝ))) ^ 2 ≤ 1 - e ^ 2 := by
    rw [hh1]
    have hx0e : 0 < e := lt_trans hx0 hxe
    have he2 : 0 ≤ 1 - e ^ 2 := by nlinarith only [he1, hx0e]
    have h3 : ((k0 : ℝ) + 1) * δ ^ 3 ≤ √(1 - e ^ 2) := by
      have : ((k0 : ℝ) + 1) * δ ^ 3 ≤ A ^ 2 + 2 * δ := by linarith only [hhi, hδ3, hh0]
      exact this.trans p3
    have h4 : 0 ≤ ((k0 : ℝ) + 1) * δ ^ 3 := by positivity
    have := pow_le_pow_left₀ h4 h3 2
    rwa [Real.sq_sqrt he2] at this
  have hnode := ksf_node (M := M) (σ := σ) (N := N) (x := x) (e := e) (K0 := K0) (k0 := k0) (b := b) (nb := nb)
    (Ebar := kfKE K A * δ) (Sbar := kfS1 K A * δ) (abar := (2 * A + 3 * δ) / √(1 - (x : ℝ) ^ 2))
    (lbar := 8 * ke_C (M : ℝ) (σ : ℝ) (x : ℝ) e K0 * (A + δ / A)) (zbar := kfKZ K * A + kfK3 K * δ) (wbar := 50 * δ / A ^ 3)
    hx0 hx1 d s Cs hA0 hAq' hk0 hnb hb1 hb2 hbw hJb p5 hβk hηB hηB2 hκB hS hSbar (hS.trans (hSbar.trans (by norm_num)))
    hxe he1 hK0 hKk0 hleft hE hEbar hab habar hlb hzb hz0 hwb hwbar h1 h2
  have hmax : max (2 * (kfKE K A * δ) + (2 * A + 3 * δ) / √(1 - (x : ℝ) ^ 2) + 20 * (kfS1 K A * δ) + 50 * δ / A ^ 3)
      (24 * (kfS1 K A * δ) + 3 * (kfKE K A * δ) + 2 * (kfKZ K * A + kfK3 K * δ) + 2 * (8 * ke_C (M : ℝ) (σ : ℝ) (x : ℝ) e K0 * (A + δ / A)) +
        2 * (50 * δ / A ^ 3)) ≤ B0 := max_le (ht1.trans hθ) (ht2.trans hθ)
  have := (abs_le.1 (hnode.trans (by linarith only [hmax] : _ ≤ 2 * B0)))
  rw [abs_le]
  constructor <;> linarith only [this.1, this.2]

/-- info: 'FormalResearch.Special.ksfin_node' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.ksfin_node

end FormalResearch.Special
