module

public import FormalResearch.Special.DiscreteAiryKappaSharpNode2
public import FormalResearch.Special.DiscreteAiryKappaSharpBand
public import FormalResearch.Special.DiscreteAiryKappaSharpZone
public import FormalResearch.Special.DiscreteAiryKappaSharpLeft
public import FormalResearch.Special.DiscreteAiryKappaOrder

/-!
# Sharp `κ`: the node theorem (plan K1, sharp constant, step 12)

`ksf_node`: at a lattice node with the data of the order-sharp theorem (`KkData`, `KkSmall`), the chart `KshChart`, a band `[k₀, b)` with
`α ≥ A` on `[k₀ - 1, b]`, `q_{k₀} ≈ η`, `q_b ≈ √(q_*² - A²)`, and a fixed left cut constant `C_l = ke_C(M,σ,x,e,K₀)`, the quantity `t = κ²δ/2` satisfies
`|t - 1| ≤ 2 max(θ₁, θ₂)`, where the `θ` are explicit combinations of upper bounds `Ē, S̄, ā, l̄, z̄, w̄` of

* `E` the bond-match error (`ksfE`), `S` the band transport error (`ksbSbd`), `a` the profile-sum defect (`ksg_sv`),
* `l = 8 k₀ C_l/(A N)` the left mass coefficient, `ζ` the zone coefficient (`ksz_zone`), `w = 50/(A³N)` the band mass offset.

The mass accounting is `N ≤ L + B + Z` (left, band, zone), `B ≤ N`, `L ≤ L_c I₀` (`ksl_left`, `kermI_lower`), `|B - I₀Σv| ≤ I₀(18SΣv + 50/A³)`
(`hahn3j_band_clean`), `Z ≤ 2tNζ` (`ksz_zone`), `(1-E)²κ²δ/π ≤ I_b ≤ (1+E)²κ²δ/π` (`ksf_match`), combined by `ksa_combine`.

**Claim class: proved** (explicit hypotheses; all of them hold for `N` large, `A, η` small: `DiscreteAiryKappaSharpFinal`).
-/

@[expose] public section

open Finset Set FormalResearch.Racah FormalResearch.Racah.P3 FormalResearch.Wigner

namespace FormalResearch.Special

/-- **The node theorem** (see the module docstring). -/
theorem ksf_node {M σ N : ℤ} {x : ℚ} {δ r C Cmu ξ0 gmin gmax c1 c2 κmin Cl κ μ σ0 : ℝ} {J m Nw : ℤ} {rs c1s c2s A : ℝ}
    {e : ℝ} {K0 : ℕ} {k0 b : ℤ} {nb : ℕ} {Ebar Sbar abar lbar zbar wbar : ℝ}
    (hx0 : 0 < (x : ℝ)) (hx1 : (x : ℝ) < 1)
    (d : KkData (hahn3jY M σ N x) (turnX (hrU 1 0 1 (x : ℝ)) (√(1 - (x : ℝ) ^ 2)) (δ ^ 3 / 2) δ)
      (fun k => langerAmp (hrU 1 0 1 (x : ℝ)) (hrA1 1 0) (√(1 - (x : ℝ) ^ 2)) (dalQ (δ ^ 3 / 2) δ k)) N δ (√(1 - (x : ℝ) ^ 2)) r C Cmu
      ξ0 gmin gmax c1 c2 κmin Cl κ μ J m Nw)
    (s : KkSmall δ r C Cmu ξ0 gmin gmax c1 c2 κmin σ0) (Cs : KshChart (x : ℝ) rs c1s c2s)
    -- band geometry
    (hA0 : 0 < A) (hAq : A < √(1 - (x : ℝ) ^ 2)) (hk0 : 1 ≤ k0) (hbn : b = k0 + (nb : ℤ) + 1)
    (hbq1 : kpU (δ ^ 3) b ≤ √(√(1 - (x : ℝ) ^ 2) ^ 2 - A ^ 2)) (hbq2 : √(√(1 - (x : ℝ) ^ 2) ^ 2 - A ^ 2) < kpU (δ ^ 3) b + δ ^ 3)
    -- the window at the band end
    (hbw : √(1 - (x : ℝ) ^ 2) - rs ≤ kpU (δ ^ 3) (b - 1)) (hJb : √(1 - (x : ℝ) ^ 2) - r + δ ^ 3 ≤ kpU (δ ^ 3) (b - 1))
    (hδA : 2 * √(1 - (x : ℝ) ^ 2) * δ ^ 2 ≤ c1s * A ^ 2)
    -- the band (Hahn) smallness
    (hβk : kl_beta (M : ℝ) (σ : ℝ) < (k0 : ℝ) ^ 2) (hηB : 3 * kl_beta (M : ℝ) (σ : ℝ) / (k0 : ℝ) ^ 2 ≤ (x : ℝ) ^ 2)
    (hηB2 : 3 * kl_beta (M : ℝ) (σ : ℝ) / (k0 : ℝ) ^ 2 ≤ 1 / 2) (hκB : |(M : ℝ) * (σ : ℝ)| / (k0 : ℝ) ^ 2 ≤ 1)
    (hS : ksbSbd M σ (x : ℝ) (1 / (N : ℝ)) A k0 ≤ Sbar) (hSbar : Sbar ≤ 1 / 100) (hS4 : ksbSbd M σ (x : ℝ) (1 / (N : ℝ)) A k0 ≤ 1 / 4)
    -- the left cut
    (hxe : (x : ℝ) < e) (he1 : e ≤ 1) (hK0 : kl_K0real (M : ℝ) (σ : ℝ) (x : ℝ) e ≤ (K0 : ℝ)) (hKk0 : (K0 : ℤ) ≤ k0)
    (hleft : (((k0 : ℝ) + 1) * (1 / (N : ℝ))) ^ 2 ≤ 1 - e ^ 2)
    -- the error bounds
    (hE : ksfE (x : ℝ) A δ (3 * kl_beta (M : ℝ) (σ : ℝ) / (k0 : ℝ) ^ 2) (C + 1) ((2 * √(1 - (x : ℝ) ^ 2) / (c1s * A ^ 2)) ^ (3 / 2 : ℝ) * δ ^ 3) ≤ Ebar)
    (hEbar : Ebar ≤ 1 / 4)
    (hab : kpU (δ ^ 3) (k0 - 1) / √(1 - (x : ℝ) ^ 2) + √(1 - (kpU (δ ^ 3) (b - 1) / √(1 - (x : ℝ) ^ 2)) ^ 2) ≤ abar)
    (habar : abar ≤ 1 / 4)
    (hlb : (k0 : ℝ) * (ke_C (M : ℝ) (σ : ℝ) (x : ℝ) e K0 * (8 / A)) / (N : ℝ) ≤ lbar)
    (hzb : 2 * gmax ^ 2 * (√(c2s * (A ^ 2 / √(1 - (x : ℝ) ^ 2) + δ ^ 3)) / Real.pi + 2 * c2 * (c2s * (A ^ 2 / √(1 - (x : ℝ) ^ 2) + δ ^ 3))) / c1 +
      kszK3 c1 gmax C (A ^ 2 / √(1 - (x : ℝ) ^ 2) + 4 * δ ^ 3) * δ ≤ zbar)
    (hz0 : 0 ≤ zbar) (hwb : 50 / A ^ 3 / (N : ℝ) ≤ wbar) (hwbar : wbar ≤ 1 / 4)
    (h1 : 2 * Ebar + abar + 20 * Sbar + wbar ≤ 1 / 2) (h2 : 24 * Sbar + 3 * Ebar + 2 * zbar + 2 * lbar + 2 * wbar ≤ 1 / 2) :
    |κ ^ 2 * δ / 2 - 1| ≤ 2 * max (2 * Ebar + abar + 20 * Sbar + wbar) (24 * Sbar + 3 * Ebar + 2 * zbar + 2 * lbar + 2 * wbar) := by
  -- basic facts
  have hδp := s.hδ
  have hh0 : 0 < δ ^ 3 := by positivity
  have hNz : (N : ℝ) = 1 / δ ^ 3 := d.hNz
  have hN1 : 1 ≤ N := d.hNz1
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : (0 : ℤ) < N)
  have hh1 : 1 / (N : ℝ) = δ ^ 3 := by rw [hNz]; field_simp
  set qs : ℝ := √(1 - (x : ℝ) ^ 2) with hqsdef
  have hqs2 : qs ^ 2 = 1 - (x : ℝ) ^ 2 := Real.sq_sqrt (by nlinarith only [hx0, hx1])
  have hqs : 0 < qs := Real.sqrt_pos.2 (by nlinarith only [hx0, hx1])
  have hqs1 : qs < 1 := by nlinarith only [hqs2, hx0, hqs]
  have hA1 : A ≤ 1 := by linarith only [hAq, hqs1]
  set qA : ℝ := √(qs ^ 2 - A ^ 2) with hqAdef
  have hqA2 : 0 < qs ^ 2 - A ^ 2 := by nlinarith only [hAq, hA0]
  have hqAsq : qA ^ 2 = qs ^ 2 - A ^ 2 := Real.sq_sqrt hqA2.le
  have hqA0 : 0 ≤ qA := Real.sqrt_nonneg _
  have hk0' : (1 : ℝ) ≤ k0 := by exact_mod_cast hk0
  have hbk : k0 + 1 ≤ b := by omega
  have hb1 : 1 ≤ b := by omega
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb1
  have hkb' : (k0 : ℝ) ≤ b := by exact_mod_cast (by omega : k0 ≤ b)
  have hqb0 : 0 < kpU (δ ^ 3) b := by unfold kpU; positivity
  have hqbq : kpU (δ ^ 3) b < qs := by
    refine lt_of_le_of_lt hbq1 ?_
    rw [Real.sqrt_lt' hqs]; nlinarith only [hA0, hqs]
  -- geometry of the band end
  obtain ⟨hgeo1, hgeo2⟩ := ksf_geo hqs hA0 hAq hh0 hqb0 hbq1 hbq2
  have hqpred : kpU (δ ^ 3) b - δ ^ 3 = kpU (δ ^ 3) (b - 1) := kpU_pred _ b
  have hbc : k0 + (((nb + 1 : ℕ)) : ℤ) = b := by push_cast; omega
  have hmono : ∀ j : ℤ, j ≤ b → kpU (δ ^ 3) j ≤ kpU (δ ^ 3) b := fun j hj => by
    unfold kpU
    have : (j : ℝ) ≤ b := by exact_mod_cast hj
    nlinarith only [this, hh0]
  -- the band
  have hband : ∀ j : ℤ, k0 - 1 ≤ j → j ≤ k0 + (((nb + 1 : ℕ)) : ℤ) →
      A ^ 2 ≤ qs ^ 2 - kpU (1 / (N : ℝ)) j ^ 2 := by
    intro j hj1 hj2
    rw [hh1]
    have hjb : j ≤ b := by omega
    have hj0 : 0 < kpU (δ ^ 3) j := by
      unfold kpU
      have : (0 : ℝ) ≤ j := by exact_mod_cast (by omega : (0 : ℤ) ≤ j)
      positivity
    have h3 : kpU (δ ^ 3) j ≤ qA := (hmono j hjb).trans hbq1
    have h4 : kpU (δ ^ 3) j ^ 2 ≤ qA ^ 2 := pow_le_pow_left₀ hj0.le h3 2
    linarith only [h4, hqAsq]
  have hmh : ((nb : ℝ) + 1) * (1 / (N : ℝ)) ≤ 1 := by
    rw [hh1]
    have h1 : ((nb : ℝ) + 1) ≤ b := by
      have : (nb : ℤ) + 1 ≤ b := by omega
      exact_mod_cast this
    have h2 : ((nb : ℝ) + 1) * δ ^ 3 ≤ kpU (δ ^ 3) b := by
      unfold kpU
      nlinarith only [h1, hh0]
    linarith only [h2, hqbq, hqs1]
  obtain ⟨hI0, htr, hmass⟩ := hahn3j_band_clean M σ N x (by omega) hx0 hx1 nb hk0 hβk hA0 hA1 hband hηB hκB hmh hS4
  obtain ⟨hIa1, hIa2⟩ := htr (nb + 1) le_rfl
  rw [hbc] at hIa1 hIa2
  rw [hh1] at hI0 hIa1 hIa2 hmass
  rw [hh1] at hS hS4
  -- the profile sum
  have hkn : k0 + (nb : ℤ) = b - 1 := by omega
  obtain ⟨hsv2, hsv1⟩ := ksg_sv (qs := qs) (h := δ ^ 3) (k0 := k0) nb hqs hh0 hk0 (by rw [show k0 + (nb : ℤ) + 1 = b by omega]; exact hqbq)
  rw [hkn] at hsv1
  have hNδ : 1 / δ ^ 3 = (N : ℝ) := by rw [hNz]
  rw [hNδ] at hsv1 hsv2
  have hU1 : 0 ≤ kpU (δ ^ 3) (k0 - 1) / qs := by
    unfold kpU
    have : (0 : ℝ) ≤ ((k0 - 1 : ℤ) : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) ≤ k0 - 1)
    have : 0 ≤ (((k0 - 1 : ℤ) : ℝ) + 1 / 2) * δ ^ 3 := by positivity
    positivity
  have ha0 : 0 ≤ kpU (δ ^ 3) (k0 - 1) / qs + √(1 - (kpU (δ ^ 3) (b - 1) / qs) ^ 2) := by
    have := Real.sqrt_nonneg (1 - (kpU (δ ^ 3) (b - 1) / qs) ^ 2)
    linarith only [hU1, this]
  -- the left mass
  have hbandδ : ∀ j : ℤ, k0 - 1 ≤ j → j ≤ b → A ^ 2 ≤ qs ^ 2 - kpU (δ ^ 3) j ^ 2 := fun j h1 h2 => by
    have := hband j h1 (by omega)
    rwa [hh1] at this
  have hkh0 : ((k0 : ℝ) * δ ^ 3) ^ 2 < 1 := by
    have h1 : (k0 : ℝ) * δ ^ 3 ≤ b * δ ^ 3 := mul_le_mul_of_nonneg_right hkb' hh0.le
    have h2 : (b : ℝ) * δ ^ 3 ≤ kpU (δ ^ 3) b := by unfold kpU; nlinarith only [hh0]
    have h3 : 0 ≤ (k0 : ℝ) * δ ^ 3 := by positivity
    nlinarith only [h1, h2, h3, hqbq, hqs1]
  obtain ⟨hapos0, ha0sq, -, -⟩ := kb_coef (M : ℝ) (σ : ℝ) (x : ℝ) (δ ^ 3) hk0 hβk hkh0
  obtain ⟨hηr0, -⟩ := kb_eta_bound (M := (M : ℝ)) (σ := (σ : ℝ)) hk0' hβk
  have hrad0 := kp_rad_ge (a := hrAk 1 0 (M : ℝ) (σ : ℝ) (δ ^ 3)) (x := (x : ℝ)) (qs := qs) (h := δ ^ 3) (A := A)
    (η := rr (M : ℝ) (σ : ℝ) (k0 : ℝ) ^ 2 - 1) hqs2 hk0 hh0 hA0 (hbandδ (k0 - 1) le_rfl (by omega)) (hbandδ k0 (by omega) (by omega))
    ha0sq (hηr0.trans hηB)
  have hP0 := kpP_pos hA0 (hbandδ k0 (by omega) (by omega))
  have hP1 := kpP_pos hA0 (hbandδ (k0 - 1) le_rfl (by omega))
  obtain ⟨hl1, hl2⟩ := kermI_lower (a := hrAk 1 0 (M : ℝ) (σ : ℝ) (δ ^ 3)) (Y := hahn3jY M σ N x) hP0 hP1 hrad0
  have hPle : ∀ j : ℤ, A ^ 2 ≤ qs ^ 2 - kpU (δ ^ 3) j ^ 2 → kpP qs (δ ^ 3) j ≤ 2 / A := fun j hj => by
    obtain ⟨-, hb2⟩ := kpα_sq (h := δ ^ 3) hj
    unfold kpP
    exact div_le_div_of_nonneg_left (by norm_num) hA0 hb2
  have hP0le := hPle k0 (hbandδ k0 (by omega) (by omega))
  have hP1le := hPle (k0 - 1) (hbandδ (k0 - 1) le_rfl (by omega))
  have hCl0 : 1 ≤ ke_C (M : ℝ) (σ : ℝ) (x : ℝ) e K0 := ke_C_ge_one K0 hx0 hxe he1
  have hY := ksl_left (M := M) (σ := σ) (N := N) (k1 := k0) (x := x) (e := e) (K0 := K0) (by omega) hx0 hxe he1 hK0 hKk0 hleft
  have hLsum := ksl_sum (Y := hahn3jY M σ N x) (Cl := ke_C (M : ℝ) (σ : ℝ) (x : ℝ) e K0) (k1 := k0) (by omega) hY
  set I0 := kermI (hrAk 1 0 (M : ℝ) (σ : ℝ) (δ ^ 3)) (kpP qs (δ ^ 3)) (hahn3jY M σ N x) k0 with hI0def
  have hL : ∑ k ∈ Finset.Ico (0 : ℤ) k0, hahn3jY M σ N x k ^ 2 ≤ (k0 * (ke_C (M : ℝ) (σ : ℝ) (x : ℝ) e K0 * (8 / A))) * I0 := by
    refine hLsum.trans ?_
    have hy : hahn3jY M σ N x k0 ^ 2 + hahn3jY M σ N x (k0 - 1) ^ 2 ≤ 8 / A * I0 := by
      have e1 : 2 * kpP qs (δ ^ 3) k0 * I0 ≤ 2 * (2 / A) * I0 := mul_le_mul_of_nonneg_right (by linarith only [hP0le]) hI0
      have e2 : 2 * kpP qs (δ ^ 3) (k0 - 1) * I0 ≤ 2 * (2 / A) * I0 := mul_le_mul_of_nonneg_right (by linarith only [hP1le]) hI0
      calc _ ≤ 2 * kpP qs (δ ^ 3) k0 * I0 + 2 * kpP qs (δ ^ 3) (k0 - 1) * I0 := add_le_add hl1 hl2
        _ ≤ 2 * (2 / A) * I0 + 2 * (2 / A) * I0 := add_le_add e1 e2
        _ = 8 / A * I0 := by ring
    have := mul_le_mul_of_nonneg_left hy (by linarith only [hCl0] : (0 : ℝ) ≤ ke_C (M : ℝ) (σ : ℝ) (x : ℝ) e K0)
    have h2 := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ k0)
    linarith only [h2]
  -- the chart window at the band end
  obtain ⟨k1, hk1, hk1N, hX1, hX2, hrest⟩ := kk_rest_all d s
  have hbm : b < m := by
    have h3 := d.p3
    have : kpU (δ ^ 3) b < kpU (δ ^ 3) m := lt_of_lt_of_le hqbq (by unfold kpU; exact h3)
    unfold kpU at this
    have h4 : ((b : ℝ) + 1 / 2) < ((m : ℝ) + 1 / 2) := lt_of_mul_lt_mul_right this hh0.le
    have : (b : ℝ) < m := by linarith only [h4]
    exact_mod_cast this
  have hJb1 : J < b - 1 := by
    have h2 := d.p2
    have : ((J : ℝ) + 1 / 2) * δ ^ 3 < ((b - 1 : ℤ) : ℝ) * δ ^ 3 + 1 / 2 * δ ^ 3 := by
      unfold kpU at hJb; linarith only [h2, hJb]
    have h4 : ((J : ℝ) + 1 / 2) < ((b - 1 : ℤ) : ℝ) + 1 / 2 := by
      have : ((J : ℝ) + 1 / 2) * δ ^ 3 < (((b - 1 : ℤ) : ℝ) + 1 / 2) * δ ^ 3 := by linarith only [this]
      exact lt_of_mul_lt_mul_right this hh0.le
    have : (J : ℝ) < ((b - 1 : ℤ) : ℝ) := by linarith only [h4]
    exact_mod_cast this
  have hq1' : kpU (δ ^ 3) (b - 1) < kpU (δ ^ 3) b := by linarith only [hqpred, hh0]
  have hwinb : kpU (δ ^ 3) b ∈ Icc (qs - rs) qs := ⟨by linarith only [hbw, hq1'], hqbq.le⟩
  have hwinb1 : kpU (δ ^ 3) (b - 1) ∈ Icc (qs - rs) qs := ⟨hbw, by linarith only [hq1', hqbq]⟩
  have hgeo1' : A ^ 2 / (2 * qs) ≤ qs - kpU (δ ^ 3) (b - 1) := by linarith only [hgeo1, hq1', hh0, hqpred]
  have hgb : 0 < kshG (x : ℝ) (kpU (δ ^ 3) b) := by
    have := d.glo b (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    rw [ksf_g] at this
    linarith only [this, s.hgmin]
  have hgb1 : 0 < kshG (x : ℝ) (kpU (δ ^ 3) (b - 1)) := by
    have := d.glo (b - 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    rw [ksf_g] at this
    linarith only [this, s.hgmin]
  have hrb := hrest b (by omega) (by omega)
  have hrb1 := hrest (b - 1) (by omega) (by omega)
  rw [ksf_g, ksf_X _ _ hδp] at hrb hrb1
  have hyl := ksf_y_lower (r := rs) (c1 := c1s) (c2 := c2s) (A := A) Cs hδp hqs hwinb hgeo1
  have hyl1 := ksf_y_lower (r := rs) (c1 := c1s) (c2 := c2s) (A := A) Cs hδp hqs hwinb1 hgeo1'
  have hyb := ksf_ye Cs.hc1 hA0 hqs hδp hyl
  have hyb1 := ksf_ye Cs.hc1 hA0 hqs hδp hyl1
  have hKY0 : 0 ≤ (2 * qs / (c1s * A ^ 2)) ^ (3 / 2 : ℝ) * δ ^ 3 := by
    have := Cs.hc1
    positivity
  have hβ0 : 0 ≤ kl_beta (M : ℝ) (σ : ℝ) := by unfold kl_beta; positivity
  have hk02 : (0 : ℝ) < (k0 : ℝ) ^ 2 := by positivity
  have hkb2 : (k0 : ℝ) ^ 2 ≤ (b : ℝ) ^ 2 := pow_le_pow_left₀ (by linarith only [hk0']) hkb' 2
  have hηr' : 3 * kl_beta (M : ℝ) (σ : ℝ) / (b : ℝ) ^ 2 ≤ 3 * kl_beta (M : ℝ) (σ : ℝ) / (k0 : ℝ) ^ 2 :=
    div_le_div_of_nonneg_left (by linarith only [hβ0]) hk02 hkb2
  have hηk0 : 0 ≤ 3 * kl_beta (M : ℝ) (σ : ℝ) / (k0 : ℝ) ^ 2 := by positivity
  have hE0 := ksfE_nonneg (x := (x : ℝ)) (A := A) (δ := δ) (ηb := 3 * kl_beta (M : ℝ) (σ : ℝ) / (k0 : ℝ) ^ 2) (Cr := C + 1)
    (Ye := (2 * qs / (c1s * A ^ 2)) ^ (3 / 2 : ℝ) * δ ^ 3) hδp hx0 hA0 hηk0 (by have := s.hC; linarith only [this]) hKY0
  have hbh : ((b : ℝ) * δ ^ 3) ^ 2 < 1 := by
    have h2 : (b : ℝ) * δ ^ 3 ≤ kpU (δ ^ 3) b := by unfold kpU; nlinarith only [hh0]
    have h3 : 0 ≤ (b : ℝ) * δ ^ 3 := by positivity
    nlinarith only [h2, h3, hqbq, hqs1]
  have hmatch := ksf_match (M := M) (σ := σ) (N := N) (b := b) (x := x) (rs := rs) (c1s := c1s) (c2s := c2s) (δ := δ) (κ := κ)
    (Cr := C + 1) (Ye := (2 * qs / (c1s * A ^ 2)) ^ (3 / 2 : ℝ) * δ ^ 3) (A := A) (ηb := 3 * kl_beta (M : ℝ) (σ : ℝ) / (k0 : ℝ) ^ 2)
    hx0 hx1 Cs hδp hb1 (lt_of_lt_of_le hβk hkb2) hbh (by linarith only [hbw, hq1', hqpred]) hqbq hA0 hA1 (hbandδ (b - 1) (by omega) (by omega))
    (hbandδ b (by omega) le_rfl) hηr' hηB hηB2 hgb hgb1 (by have := s.hC; linarith only [this]) hrb hrb1 hyb hyb1 (hE.trans (by linarith only [hEbar]))
  -- the zone
  have hc2s : 0 < c2s := lt_of_lt_of_le Cs.hc1 Cs.hc12
  have hR0 : 0 ≤ c2s * (A ^ 2 / qs + δ ^ 3) := by positivity
  have hRc : 0 ≤ A ^ 2 / qs + 4 * δ ^ 3 := by positivity
  obtain ⟨hz1, hz2⟩ := ksf_zone_hyps (A := A) (h := δ ^ 3) Cs hδp hqs hwinb hgeo1 hgeo2 hδA
  have hmcnt : (((m + 2 - b : ℤ)) : ℝ) ≤ (A ^ 2 / qs + 4 * δ ^ 3) / δ ^ 3 := by
    rw [le_div_iff₀ hh0]
    have h4 := d.p4
    unfold kpU at hgeo2
    push_cast
    linarith only [h4, hgeo2]
  have hZ0 := ksz_zone d s (k1 := k1) hk1 hk1N hX1 hX2 hrest hR0 hRc (jz := b) (by omega) (by omega)
    (by rw [ksf_X _ _ hδp]; exact hz1) (by rw [ksf_X _ _ hδp]; exact hz2) hmcnt
  have hZ1 := ksf_zeta_alg hδp s.hc1 hZ0
  rw [hNδ] at hZ1
  -- the cover
  have hcov := ksf_cover (Y := hahn3jY M σ N x) (Nz := N) (k0 := k0) (b := b) (e := k1 + 1 + N) (δ := δ) (by omega) (by omega)
    (by omega) (by omega) d.cover
  have hmid := ksf_ico_range (fun k => hahn3jY M σ N x k ^ 2) k0 (nb + 1)
  rw [hbc] at hmid
  rw [hmid, hNδ] at hcov
  have hB := d.sum k0 (nb + 1)
  rw [hNδ] at hB
  -- assembly
  have hCl0' : 0 ≤ ke_C (M : ℝ) (σ : ℝ) (x : ℝ) e K0 := by linarith only [hCl0]
  have hLc0 : 0 ≤ (k0 : ℝ) * (ke_C (M : ℝ) (σ : ℝ) (x : ℝ) e K0 * (8 / A)) := by
    have : (0 : ℝ) ≤ k0 := by linarith only [hk0']
    positivity
  have hω0 : 0 ≤ 50 / A ^ 3 := by positivity
  have hS0 : 0 ≤ ksbSbd M σ (x : ℝ) (δ ^ 3) A k0 := by
    unfold ksbSbd
    have : (0 : ℝ) ≤ k0 := by linarith only [hk0']
    positivity
  have e2t : 2 * (κ ^ 2 * δ / 2) / Real.pi = κ ^ 2 * δ / Real.pi := by ring
  have hfinal := ksa_combine (t := κ ^ 2 * δ / 2) (N := (N : ℝ)) (Ebar := Ebar) (Sbar := Sbar) (abar := abar) (lbar := lbar)
    (zbar := zbar) (wbar := wbar) (E := ksfE (x : ℝ) A δ (3 * kl_beta (M : ℝ) (σ : ℝ) / (k0 : ℝ) ^ 2) (C + 1)
      ((2 * qs / (c1s * A ^ 2)) ^ (3 / 2 : ℝ) * δ ^ 3)) (S := ksbSbd M σ (x : ℝ) (δ ^ 3) A k0)
    (a := kpU (δ ^ 3) (k0 - 1) / qs + √(1 - (kpU (δ ^ 3) (b - 1) / qs) ^ 2)) (ω1 := 50 / A ^ 3)
    (Lc := (k0 : ℝ) * (ke_C (M : ℝ) (σ : ℝ) (x : ℝ) e K0 * (8 / A)))
    (ζ := 2 * gmax ^ 2 * (√(c2s * (A ^ 2 / qs + δ ^ 3)) / Real.pi + 2 * c2 * (c2s * (A ^ 2 / qs + δ ^ 3))) / c1 +
      kszK3 c1 gmax C (A ^ 2 / qs + 4 * δ ^ 3) * δ)
    hNr (by positivity) hS0 hS hSbar hE0 hE hEbar ha0 hab habar hω0 hwb hwbar hLc0 hlb hzb hz0 hcov hL
    hZ1 hB hmass hsv1 hsv2 hI0 hIa1 hIa2 (by rw [e2t]; exact hmatch.1) (by rw [e2t]; exact hmatch.2) h1 h2
  exact hfinal

/-- info: 'FormalResearch.Special.ksf_node' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.ksf_node

end FormalResearch.Special
