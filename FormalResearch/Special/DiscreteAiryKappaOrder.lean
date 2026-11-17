module

public import FormalResearch.Special.DiscreteAiryKappaChart2
public import FormalResearch.Special.DiscreteAiryKappaMass
public import FormalResearch.Special.DiscreteAiryKappaOrderData

/-!
# Order-sharp `|κ| ≍ N^{1/6}` for the actual `3j` chain (plan K1, assembly)

Fix integers `M, σ` and a rational `x ∈ (0,1)`; `h = 1/N = δ³`.  `hahn_chain_kappa_order` extends `hahn_chain_kappa`
(`DiscreteAiryKappaMain`) with two-sided bounds, uniform in `N` at the lattice nodes:

`c_lo ≤ κ² δ ≤ c_up`, i.e. `c_lo N^{1/3} ≤ κ² ≤ c_up N^{1/3}` (`δ = N^{-1/3}`).

* **upper** (`kk_ub_final`): the lattice sum `Σ Ai(X_k)²` over `-δ^{-2}s₀² ≤ X_k ≤ -1` is `≳ δ^{-2}` (`kai_sum_lower`, from the antiderivative
  `x Ai² - Ai'²` and `airyKer_diag_neg`), so `N = ΣŶ² ≥ Σ_{window} Ŷ² ≳ κ² δ^{-2}`;
* **lower** (`kk_lb_final`): `N = ΣŶ²` is bounded by the left bound `kl_hahn_left` (`Ai(X_J)² ≲ δ`), the window lattice sum (`kai_sum_upper_bound`), the
  `Ai` envelope up to `X ≈ 1/δ`, and the monotone decay `kr_chain_mono` beyond: `N ≤ Q κ² δ^{-2}`.

The chart constants `g_min, g_max, c₁, c₂` come from `kc2_hahn_full` (`DiscreteAiryKappaChart2`); the pointwise matching of `Ŷ = κ g Ai + μ g Bi`
is that of `hahn_chain_airy_full`, with `|μ|` exponentially small (`kk_mu_small`).

**Claim class: proved**, all constants existential (depending on `M, σ, x`); only the order here.  The *sharp* constant `κ² = 2N^{1/3}(1 + o(1))` is
`hahn_chain_kappa_sharp` (`DiscreteAiryKappaSharpFinal`), which uses the Airy matching `I = κ² h^{1/3}/π` of the Ermakov amplitude
(`DiscreteAiryKappaSharpMatch`) and the band/left/zone mass accounting of the `DiscreteAiryKappaSharp*` modules.

**Not formalised:** the value of the constants (`c_lo, c_up`, existential), uniformity in `x`, the Darboux phase and sign of `κ`, `τ = -1`, Racah and
half-integer parameters (see `hahn_chain_kappa_sharp` for the numerical check of `κ² δ → 2`).
-/

@[expose] public section

open Finset FormalResearch.Racah FormalResearch.Racah.P3 FormalResearch.Wigner FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- **Theorem A** (the data of the actual `3j` chain): for integers `M, σ` and rational `x ∈ (0,1)` there are constants (depending on `M, σ, x`) such that
for every lattice node with `1/N ≤ ε₀` the chain `Ŷ = hahn3jY` and the chart sequences satisfy the facts of `KkData` (for some `κ, μ`), in addition to the window
data of `hahn_chain_kappa`. -/
theorem hahn_chain_kappa_data (M σ : ℤ) (x : ℚ) (hx0 : 0 < x) (hx1 : x < 1) :
    ∃ (r ε0 C Cmu ξ0 gmin gmax c1 c2 κmin Cl : ℝ), 0 < r ∧ 0 < ε0 ∧ 0 < C ∧ 0 < Cmu ∧ 0 < ξ0 ∧ 0 < gmin ∧ gmin ≤ gmax ∧
      0 < c1 ∧ c1 ≤ c2 ∧ 0 < κmin ∧ 1 ≤ Cl ∧
      ∀ (N : ℤ) (n : ℕ), max |M| |σ| < N → (n : ℤ) < N - max |M| |σ| →
        xLat (M : ℚ) (σ : ℚ) (N : ℚ) n = x → 1 / (N : ℝ) ≤ ε0 →
        ∃ δ : ℝ, 0 < δ ∧ δ ^ 3 = 1 / (N : ℝ) ∧ δ ^ 3 ≤ r / 8 ∧ ∃ J m Nw : ℤ, 1 ≤ J ∧ J < Nw ∧ J ≤ m ∧ m < Nw ∧
          (∀ k ∈ Finset.Icc J (Nw + 1), |((k : ℝ) + 1 / 2) * δ ^ 3 - Real.sqrt (1 - (x : ℝ) ^ 2)| ≤ r) ∧
          Real.sqrt (1 - (x : ℝ) ^ 2) - r ≤ ((J : ℝ) + 1 / 2) * δ ^ 3 ∧
          ((J : ℝ) + 1 / 2) * δ ^ 3 < Real.sqrt (1 - (x : ℝ) ^ 2) - r + δ ^ 3 ∧
          Real.sqrt (1 - (x : ℝ) ^ 2) ≤ ((m : ℝ) + 1 / 2) * δ ^ 3 ∧
          ((m : ℝ) + 1 / 2) * δ ^ 3 < Real.sqrt (1 - (x : ℝ) ^ 2) + δ ^ 3 ∧
          Real.sqrt (1 - (x : ℝ) ^ 2) + r / 4 ≤ ((Nw : ℝ) + 1 / 2) * δ ^ 3 ∧
          ((Nw : ℝ) + 1 + 1 / 2) * δ ^ 3 ≤ Real.sqrt (1 - (x : ℝ) ^ 2) + r / 2 ∧
          DaiFull (hrAk 1 0 (M : ℝ) (σ : ℝ) (δ ^ 3)) (hrCk 1 0 1 (x : ℝ) (M : ℝ) (σ : ℝ) (δ ^ 3))
            (turnX (hrU 1 0 1 (x : ℝ)) (Real.sqrt (1 - (x : ℝ) ^ 2)) (δ ^ 3 / 2) δ)
            (fun k => langerAmp (hrU 1 0 1 (x : ℝ)) (hrA1 1 0) (Real.sqrt (1 - (x : ℝ) ^ 2)) (dalQ (δ ^ 3 / 2) δ k))
            J m Nw δ C Cmu ξ0 ∧
          ∃ κ μ : ℝ, KkData (hahn3jY M σ N x) (turnX (hrU 1 0 1 (x : ℝ)) (Real.sqrt (1 - (x : ℝ) ^ 2)) (δ ^ 3 / 2) δ)
            (fun k => langerAmp (hrU 1 0 1 (x : ℝ)) (hrA1 1 0) (Real.sqrt (1 - (x : ℝ) ^ 2)) (dalQ (δ ^ 3 / 2) δ k)) N δ
            (Real.sqrt (1 - (x : ℝ) ^ 2)) r C Cmu ξ0 gmin gmax c1 c2 κmin Cl κ μ J m Nw := by
  have hx0' : (0 : ℝ) < x := by exact_mod_cast hx0
  have hx1' : (x : ℝ) < 1 := by exact_mod_cast hx1
  have hq2 : Real.sqrt (1 - (x : ℝ) ^ 2) ^ 2 = 1 - (x : ℝ) ^ 2 := Real.sq_sqrt (by nlinarith)
  have hqs : 0 < Real.sqrt (1 - (x : ℝ) ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have hturn : Phi 1 0 1 (x : ℝ) (Real.sqrt (1 - (x : ℝ) ^ 2) ^ 2) = 0 := by
    unfold Phi etilde
    rw [hq2]
    have : (1 - 1 * (1 - (x : ℝ) ^ 2)) * (1 - 0 * (1 - (x : ℝ) ^ 2)) = (x : ℝ) ^ 2 := by ring
    rw [this, Real.sqrt_sq hx0'.le]
    simp
  obtain ⟨r, δ0, C, Cmu, ξ0, gmax, gmin, c1, c2, hr, hrq, hδ0, -, hC, hCmu, hξ0, hgmax, hgmin, hgg, hc1, hc12, H⟩ :=
    kc2_hahn_full (P := 1) (Q := 0) (by norm_num) (by norm_num) (M : ℝ) (σ : ℝ) 1 (x : ℝ)
      (Real.sqrt (1 - (x : ℝ) ^ 2)) hqs (by norm_num) (by linarith) (by rw [hq2]; nlinarith) (by simp) hturn
  set qs := Real.sqrt (1 - (x : ℝ) ^ 2) with hqsdef
  have hq1 : qs < 1 := by nlinarith
  have hqr : 0 < qs - r / 2 := by linarith
  set e : ℝ := Real.sqrt (1 - (qs - r / 2) ^ 2) with hedef
  have he2 : e ^ 2 = 1 - (qs - r / 2) ^ 2 := Real.sq_sqrt (by nlinarith)
  have hxe : (x : ℝ) < e := by
    by_contra hcon
    push Not at hcon
    have h1 : e ^ 2 ≤ (x : ℝ) ^ 2 := by nlinarith [Real.sqrt_nonneg (1 - (qs - r / 2) ^ 2)]
    nlinarith
  have he1 : e ≤ 1 := Real.sqrt_le_one.2 (by nlinarith)
  set K0 : ℕ := ⌈kl_K0real (M : ℝ) (σ : ℝ) (x : ℝ) e⌉₊ with hK0def
  have hK0 : kl_K0real (M : ℝ) (σ : ℝ) (x : ℝ) e ≤ (K0 : ℝ) := Nat.le_ceil _
  set Cl : ℝ := ke_C (M : ℝ) (σ : ℝ) (x : ℝ) e K0 with hCldef
  have hCl : 1 ≤ Cl := ke_C_ge_one K0 hx0' hxe he1
  set Aκ : ℝ := 3 * gmax + C with hAκ
  set Aμ : ℝ := 3600 * gmax + 8 * C with hAμ
  have hAκ0 : 0 < Aκ := by positivity
  have hAμ0 : 0 < Aμ := by positivity
  obtain ⟨ε0, hε0, Hε⟩ := kf_small (x := (x : ℝ)) (qs := qs) (r := r) (δ0 := δ0) (Cmu := Cmu) (Aμ := Aμ)
    (ξ0 := ξ0) (μ0 := |(M : ℝ) * σ|) (m0 := |(M : ℝ)| + |(σ : ℝ)|) K0 hx0' hqs hr hδ0 hCmu hAμ0 hξ0
    (abs_nonneg _) (by positivity) (by linarith)
  have h8Cl : 0 < 8 * Cl := by linarith
  refine ⟨r, ε0, C, Cmu, ξ0, gmin, gmax, c1, c2, 1 / (Aκ * Real.sqrt (8 * Cl)), Cl, hr, hε0, hC, hCmu, hξ0, hgmin, hgg, hc1,
    hc12, by positivity, hCl, ?_⟩
  intro N n hN hn hxn hNε
  have hN0 : (0 : ℤ) < N := lt_of_le_of_lt (le_trans (abs_nonneg M) (le_max_left _ _)) hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hh0 : (0 : ℝ) < 1 / (N : ℝ) := by positivity
  obtain ⟨⟨δ, hδp, hδ3, hδle, hδsq⟩, hhr, hK3, hc4, hc5, hc6⟩ := Hε _ hh0 hNε
  obtain ⟨J, m, Nw, hJ, hJN, hJm, hmN, hwin, h1, h2, h3, h4, h5, h6, hg, hXm, hgl, hgap, hX0m, hXN, Hc⟩ :=
    H δ hδp hδle
  have hhle : δ ^ 3 ≤ r / 8 := by rw [hδ3]; exact hhr
  have hδ31 : δ ^ 3 ≤ 1 := by linarith
  have hm1 : m + 1 ≤ Nw := kf_idx_lt (pow_pos hδp 3) hhle h4 h5
  have hrows' : ∀ k ∈ Finset.Icc (J + 1) Nw,
      jac (hrAk 1 0 (M : ℝ) (σ : ℝ) (δ ^ 3)) (hrCk 1 0 1 (x : ℝ) (M : ℝ) (σ : ℝ) (δ ^ 3)) (hahn3jY M σ N x) k = 0 := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [hδ3]
    exact hahn_class_chain M σ N x hN0 k (by omega)
  have hmonoAll : ∀ m' : ℤ, qs ≤ ((m' : ℝ) + 1 / 2) * δ ^ 3 → ∀ k : ℤ, m' + 1 ≤ k →
      hahn3jY M σ N x k ^ 2 ≤ hahn3jY M σ N x (m' + 1) ^ 2 := fun m' hm' =>
    kr_chain_mono M σ N m' x hN0 hx0' hq2 hqs (by rw [← hδ3]; exact hm') hc4
      (kf_hh2 hh0 (by linarith) (abs_nonneg _) hc5) hc6
  have hmono := hmonoAll m h3
  have hYN : |hahn3jY M σ N x Nw| ≤ |hahn3jY M σ N x (m + 1)| := sq_le_sq.1 (hmono Nw hm1)
  have hYN1 : |hahn3jY M σ N x (Nw + 1)| ≤ |hahn3jY M σ N x (m + 1)| := sq_le_sq.1 (hmono (Nw + 1) (by omega))
  obtain ⟨κ, μ, hμ, hpt⟩ := Hc.pointwise (hahn3jY M σ N x) _ hrows' hYN hYN1
  have hμ' := kf_mu_bound hδp hCmu.le (abs_nonneg _) hμ Hc.1
  have hε := kf_eps_half hδp hξ0 hAμ0 hCmu hδsq
  have hwin2 := kf_window_abs (Y := hahn3jY M σ N x) (hJm) hm1 hC.le hδ31 hAκ hAμ hg hXm hpt hμ' hε
  have hleft := kf_left (M := M) (σ := σ) (N := N) (J := J) (x := x) (qs := qs) (r := r) (e := e) (K0 := K0) hN0 hx0'
    hxe he1 he2 hqr hK0 hK3 hhr (by rw [← hδ3]; exact h1) (by rw [← hδ3]; exact h2)
  have hall := kf_assemble (Y := hahn3jY M σ N x) (Aκ := Aκ) (κ := κ) (Cl := Cl) hJm hCl hwin2 hleft
    (fun k hk => hmono k hk)
  have hmass := kf_mass_le M σ N hN n hn (B := 8 * Cl * Aκ ^ 2 * κ ^ 2) (by rw [hxn]; exact hall)
  have hB1 : 1 ≤ 8 * Cl * Aκ ^ 2 * κ ^ 2 := by
    by_contra hcon
    push Not at hcon
    have : (N : ℝ) * (8 * Cl * Aκ ^ 2 * κ ^ 2) < N * 1 := mul_lt_mul_of_pos_left hcon hNr
    linarith
  have hYs : |hahn3jY M σ N x (m + 1)| ≤ Real.sqrt (N : ℝ) := by
    have := hahn_chain_abs_le M σ N hN n hn (m + 1)
    rwa [hxn] at this
  have hμ2 : |μ| ≤ Cmu * Real.sqrt (N : ℝ) * Real.exp (-ξ0 / δ ^ 3) / δ := by
    refine hμ'.trans ?_
    have h0 : 0 ≤ Real.exp (-ξ0 / δ ^ 3) / δ := by positivity
    calc Cmu * |hahn3jY M σ N x (m + 1)| * (Real.exp (-ξ0 / δ ^ 3) / δ)
        ≤ Cmu * Real.sqrt (N : ℝ) * (Real.exp (-ξ0 / δ ^ 3) / δ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hYs hCmu.le) h0
      _ = _ := by ring
  have hNδ : 1 / δ ^ 3 = (N : ℝ) := by rw [hδ3]; field_simp
  refine ⟨δ, hδp, hδ3, hhle, J, m, Nw, hJ, hJN, hJm, hm1, hwin, h1, h2, h3, h4, h5, h6, Hc, κ, μ, ?_⟩
  refine ⟨hNδ.symm, by exact_mod_cast (by omega : (1 : ℤ) ≤ N), hq1, h1, h2, h3, h4, hJ, hJm, hm1, hgap, hXm, hX0m, hXN, hg, hgl,
    fun k hk => by simpa [daoPhi, daoPsi] using hpt k hk, hμ2, kf_kappa_ge hAκ0 h8Cl hB1, ?_, hmonoAll, ?_, ?_⟩
  · intro k hk
    have := hleft k hk
    rwa [show J + 1 - 1 = J by ring] at this
  · intro ka n'
    have := kk_sum_le M σ N hN n hn ((Finset.range n').image (fun i : ℕ => ka + (i : ℤ)))
    rw [hxn, Finset.sum_image (by intro i _ j _ hij; simpa using hij), ← hNδ] at this
    exact this
  · intro S hS
    have := kk_le_sum M σ N hN n hn S (fun k hk1 hk2 =>
      hS k (le_trans (le_trans (abs_nonneg M) (le_max_left _ _)) hk1) hk2)
    rw [hxn] at this
    rw [hNδ]; exact this

/-- info: 'FormalResearch.Special.hahn_chain_kappa_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hahn_chain_kappa_data

/-- **Order-sharp `|κ|` for the actual `3j` chain at a lattice node** (see the module docstring): the conclusion of `hahn_chain_kappa`
with `|κ| ≥ κ_min` replaced by `c_lo ≤ κ² δ ≤ c_up` (`δ³ = 1/N`), i.e. `c_lo N^{1/3} ≤ κ² ≤ c_up N^{1/3}`. -/
theorem hahn_chain_kappa_order (M σ : ℤ) (x : ℚ) (hx0 : 0 < x) (hx1 : x < 1) :
    ∃ (r ε0 C Cmu ξ0 clo cup : ℝ), 0 < r ∧ 0 < ε0 ∧ 0 < C ∧ 0 < Cmu ∧ 0 < ξ0 ∧ 0 < clo ∧ 0 < cup ∧
      ∀ (N : ℤ) (n : ℕ), max |M| |σ| < N → (n : ℤ) < N - max |M| |σ| →
        xLat (M : ℚ) (σ : ℚ) (N : ℚ) n = x → 1 / (N : ℝ) ≤ ε0 →
        ∃ δ : ℝ, 0 < δ ∧ δ ^ 3 = 1 / (N : ℝ) ∧ ∃ J m Nw : ℤ, 1 ≤ J ∧ J < Nw ∧ J ≤ m ∧ m < Nw ∧
          (∀ k ∈ Finset.Icc J (Nw + 1), |((k : ℝ) + 1 / 2) * δ ^ 3 - Real.sqrt (1 - (x : ℝ) ^ 2)| ≤ r) ∧
          Real.sqrt (1 - (x : ℝ) ^ 2) - r ≤ ((J : ℝ) + 1 / 2) * δ ^ 3 ∧
          ((J : ℝ) + 1 / 2) * δ ^ 3 < Real.sqrt (1 - (x : ℝ) ^ 2) - r + δ ^ 3 ∧
          Real.sqrt (1 - (x : ℝ) ^ 2) ≤ ((m : ℝ) + 1 / 2) * δ ^ 3 ∧
          ((m : ℝ) + 1 / 2) * δ ^ 3 < Real.sqrt (1 - (x : ℝ) ^ 2) + δ ^ 3 ∧
          Real.sqrt (1 - (x : ℝ) ^ 2) + r / 4 ≤ ((Nw : ℝ) + 1 / 2) * δ ^ 3 ∧
          ((Nw : ℝ) + 1 + 1 / 2) * δ ^ 3 ≤ Real.sqrt (1 - (x : ℝ) ^ 2) + r / 2 ∧
          DaiFull (hrAk 1 0 (M : ℝ) (σ : ℝ) (δ ^ 3)) (hrCk 1 0 1 (x : ℝ) (M : ℝ) (σ : ℝ) (δ ^ 3))
            (turnX (hrU 1 0 1 (x : ℝ)) (Real.sqrt (1 - (x : ℝ) ^ 2)) (δ ^ 3 / 2) δ)
            (fun k => langerAmp (hrU 1 0 1 (x : ℝ)) (hrA1 1 0) (Real.sqrt (1 - (x : ℝ) ^ 2)) (dalQ (δ ^ 3 / 2) δ k))
            J m Nw δ C Cmu ξ0 ∧
          ∃ κ μ : ℝ, clo ≤ κ ^ 2 * δ ∧ κ ^ 2 * δ ≤ cup ∧
            |μ| ≤ Cmu * Real.sqrt (N : ℝ) * Real.exp (-ξ0 / δ ^ 3) / δ ∧
            ∀ k ∈ Finset.Icc J (Nw + 1),
              |hahn3jY M σ N x k -
                  (κ * daoPhi (fun k => langerAmp (hrU 1 0 1 (x : ℝ)) (hrA1 1 0) (Real.sqrt (1 - (x : ℝ) ^ 2))
                      (dalQ (δ ^ 3 / 2) δ k))
                    (turnX (hrU 1 0 1 (x : ℝ)) (Real.sqrt (1 - (x : ℝ) ^ 2)) (δ ^ 3 / 2) δ) k +
                   μ * daoPsi (fun k => langerAmp (hrU 1 0 1 (x : ℝ)) (hrA1 1 0) (Real.sqrt (1 - (x : ℝ) ^ 2))
                      (dalQ (δ ^ 3 / 2) δ k))
                    (turnX (hrU 1 0 1 (x : ℝ)) (Real.sqrt (1 - (x : ℝ) ^ 2)) (δ ^ 3 / 2) δ) k)| ≤
                C * δ ^ 3 * (|κ| * airyWt (turnX (hrU 1 0 1 (x : ℝ)) (Real.sqrt (1 - (x : ℝ) ^ 2)) (δ ^ 3 / 2) δ k) +
                  |μ| * airyBiWt (turnX (hrU 1 0 1 (x : ℝ)) (Real.sqrt (1 - (x : ℝ) ^ 2)) (δ ^ 3 / 2) δ k)) := by
  obtain ⟨r, ε0, C, Cmu, ξ0, gmin, gmax, c1, c2, κmin, Cl, hr, hε0, hC, hCmu, hξ0, hgmin, hgg, hc1, hc12, hκmin, hCl, HA⟩ :=
    hahn_chain_kappa_data M σ x hx0 hx1
  have hc2 : 0 < c2 := lt_of_lt_of_le hc1 hc12
  have hgmax : 0 < gmax := lt_of_lt_of_le hgmin hgg
  set σ0 : ℝ := min (√(3 * c1 * r / 4)) (1 / (20 * c2)) with hσ0
  have hσ0p : 0 < σ0 := lt_min (Real.sqrt_pos.2 (by positivity)) (by positivity)
  set B0 : ℝ := (450 * gmax + C) * Cmu with hB0def
  have hB0 : 0 ≤ B0 := by positivity
  set δ1 : ℝ := min (1 / 2) (min (c1 * r / (8 * (c2 + 1))) (min (σ0 / 100) (min (gmin ^ 2 * c1 / (80 * c2 * σ0 * (C + 1) ^ 2))
    (min (σ0 ^ 2 / 2) (min (ξ0 / 14) (κmin * ξ0 ^ 3 / (48 * (B0 + 1)))))))) with hδ1def
  have hδ1p : 0 < δ1 := by
    refine lt_min (by norm_num) (lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity)
      (lt_min (by positivity) (lt_min (by positivity) (by positivity))))))
  set Qc : ℝ := kkQ c1 c2 gmax C σ0 (c2 * (r + 1)) (r + 3) Cl with hQc
  have hQpos : 0 < Qc := by
    rw [hQc]; unfold kkQ
    have : 0 < (1 / c1 + 1) * (3 * gmax + C + 1) ^ 2 := by positivity
    have h2 : 0 ≤ Cl * (20 * gmax ^ 2 / σ0 + 8 * (C + 1) ^ 2) := by
      have : 0 ≤ Cl := by linarith
      positivity
    have h3 : 0 ≤ 2 * gmax ^ 2 * ((√(c2 * (r + 1)) / Real.pi + 1 + 2 * c2 * (c2 * (r + 1))) / c1 + 9 * (5 / (4 * c1) + 2)) +
        2 * (C + 1) ^ 2 * (r + 3) := by positivity
    have h4 : 0 ≤ 18 * gmax ^ 2 + 2 * (C + 1) ^ 2 := by positivity
    linarith
  refine ⟨r, min ε0 (δ1 ^ 3), C, Cmu, ξ0, 1 / Qc, 80 * c2 / (gmin ^ 2 * σ0), hr, lt_min hε0 (by positivity), hC, hCmu, hξ0,
    by positivity, by positivity, ?_⟩
  intro N n hN hn hxn hNε
  obtain ⟨hNε1, hNε2⟩ := le_min_iff.1 hNε
  obtain ⟨δ, hδp, hδ3, hδ3r, J, m, Nw, hJ, hJN, hJm, hm1, hwin, h1, h2, h3, h4, h5, h6, Hc, κ, μ, d⟩ :=
    HA N n hN hn hxn hNε1
  have hδδ1 : δ ≤ δ1 := by
    have : δ ^ 3 ≤ δ1 ^ 3 := by rw [hδ3]; exact hNε2
    exact le_of_pow_le_pow_left₀ (by norm_num) hδ1p.le this
  obtain ⟨hδhalf, hδrest⟩ := le_min_iff.1 hδδ1
  obtain ⟨hδc, hδrest⟩ := le_min_iff.1 hδrest
  obtain ⟨hδσ, hδrest⟩ := le_min_iff.1 hδrest
  obtain ⟨hδ5, hδrest⟩ := le_min_iff.1 hδrest
  obtain ⟨hδs, hδrest⟩ := le_min_iff.1 hδrest
  obtain ⟨hδξ, hδμ⟩ := le_min_iff.1 hδrest
  have s : KkSmall δ r C Cmu ξ0 gmin gmax c1 c2 κmin σ0 :=
    ⟨hδp, hr, hC, hCmu, hξ0, hgmin, hgg, hc1, hc12, hκmin, hσ0, hδhalf, hδc, hδσ, hδ5, hδs, hδξ, hδμ, hδ3r⟩
  obtain ⟨k1, hk1, hk1N, hX1, hX2, hrest⟩ := kk_rest_all d s
  have hUB := kk_upper d s (fun k h1' h2' => hrest k h1' (by omega))
  have hLB := kk_lower d s (by linarith) hk1 hk1N hX1 hX2 hrest
  have hlo : 1 / Qc ≤ κ ^ 2 * δ := by
    rw [div_le_iff₀ hQpos]; linarith
  exact ⟨δ, hδp, hδ3, J, m, Nw, hJ, hJN, hJm, hm1, hwin, h1, h2, h3, h4, h5, h6, Hc, κ, μ, hlo, hUB, d.mu,
    fun k hk => by simpa [daoPhi, daoPsi] using d.pt k hk⟩

/-- info: 'FormalResearch.Special.hahn_chain_kappa_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hahn_chain_kappa_order

end FormalResearch.Special
