module

public import FormalResearch.Special.BulkKappaHahn
public import FormalResearch.Special.RacahKappaHFam
public import FormalResearch.Special.DiscreteAiryLimitChains2Half3j

/-!
# The half-integer `3j` chain as a family for the abstract sharp theorem

Half-integer twin of `BulkKappaHahn`: the chains `Ŷ_k = hahn3jYH M σ N x k = √(2L+1) Φ_L^{M+½,σ+½}(x; 1/(N+½))`, `L = k + ½`, at the nodes `xLat (M+½) (σ+½) (N+½) n = x`, `h = 1/(N+½)`, Gauss weight `N + ½`,
lattice `q_k = (k+1) h`, rows `hrAkH, hrCkH` (`hahn_class_chain_half`), support `halfLo M σ ≤ k ≤ N - 1`.  `bk_hahn_half`: the hypotheses of `bk_sharp_absH` hold (`rl_leftH`, `hr_hardedge_decayH` at the hard edge
`ẽ(((N-1) + 3/2) h) = ẽ(1) = 0`), so the window, sharp amplitude and bulk form hold for the half-integer `3j` chain, `τ = ±1`.

**Claim class: proved.**
-/

@[expose] public section

open Finset FormalResearch.Racah FormalResearch.Racah.P3 FormalResearch.Wigner FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- The family of (twisted) half-integer `3j` chains of shape `x` at the lattice nodes, with `h ≤ hm`. -/
def bkFamHahnH (M σ : ℤ) (x : ℚ) (u : ℤ → ℝ) (hm : ℝ) : ℝ → (ℤ → ℝ) → ℝ → Prop := fun h Y Mm =>
  0 < h ∧ h ≤ hm ∧ ∃ (N : ℤ) (n : ℕ), halfLo M σ < N ∧ (n : ℤ) < N - halfLo M σ ∧
    xLat ((M : ℚ) + 1 / 2) ((σ : ℚ) + 1 / 2) ((N : ℚ) + 1 / 2) n = x ∧ h = 1 / ((N : ℝ) + 1 / 2) ∧
      Y = (fun j => u j * hahn3jYH M σ N x j) ∧ Mm = (N : ℝ) + 1 / 2

/-- The Gauss weight of the half-integer chain as a sum over the support: `Σ_{i<K} Ŷ_{lo+i}² = N + ½`. -/
lemma bkh_sumH (M σ N : ℤ) (hN : halfLo M σ < N) (n : ℕ) (hn : (n : ℤ) < N - halfLo M σ) :
    ∑ i ∈ Finset.range (N - halfLo M σ).toNat,
      hahn3jYH M σ N (xLat ((M : ℚ) + 1 / 2) ((σ : ℚ) + 1 / 2) ((N : ℚ) + 1 / 2) n) (halfLo M σ + (i : ℤ)) ^ 2 = (N : ℝ) + 1 / 2 := by
  have hlo0 := halfLo_nonneg M σ
  set lo : ℤ := halfLo M σ with hlodef
  have hmax := max_abs_half M σ
  have hadm : SpecAdm ((M : ℚ) + 1 / 2) ((σ : ℚ) + 1 / 2) ((N : ℚ) + 1 / 2) := by
    unfold SpecAdm
    rw [hmax]
    exact (hahn_tri_half lo M σ N).2 ⟨le_rfl, by omega⟩
  set K : ℕ := (N - lo).toNat with hKdef
  have hK : (K : ℚ) = ((N : ℚ) + 1 / 2) - max |(M : ℚ) + 1 / 2| |(σ : ℚ) + 1 / 2| := by
    rw [hmax]
    have : (K : ℤ) = N - lo := Int.toNat_of_nonneg (by omega)
    have h2 : ((K : ℤ) : ℚ) = ((N - lo : ℤ) : ℚ) := by rw [this]
    push_cast at h2
    linarith
  have hnK : n < K := by omega
  have hNq : (0 : ℚ) < (N : ℚ) + 1 / 2 := by
    have : (0 : ℚ) ≤ N := by exact_mod_cast (show (0 : ℤ) ≤ N by omega)
    linarith
  have hg := (gaussWeight_3j hadm hNq hK hnK).1
  unfold lambdaSq3j at hg
  have hNc : ((((N : ℚ) + 1 / 2 : ℚ)) : ℝ) = (N : ℝ) + 1 / 2 := by push_cast; ring
  rw [hNc] at hg
  rw [← hg]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hcast : (max |(M : ℚ) + 1 / 2| |(σ : ℚ) + 1 / 2| + (i : ℚ)) = ((lo + (i : ℤ) : ℤ) : ℚ) + 1 / 2 := by
    rw [hmax]; push_cast; ring
  rw [hcast]
  have hk0 : (0 : ℝ) ≤ ((lo + (i : ℤ) : ℤ) : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) ≤ lo + (i : ℤ))
  unfold hahn3jYH
  rw [mul_pow, Real.sq_sqrt (by linarith)]
  push_cast; ring

/-- Gauss weight: the sum of squares of the half-integer chain over `[0, END)` is `N + ½` once the chain vanishes from `END` on. -/
lemma bkh_meqH (M σ N : ℤ) (hN : halfLo M σ < N) (n : ℕ) (hn : (n : ℤ) < N - halfLo M σ) (u : ℤ → ℝ) (hu : ∀ k, u k ^ 2 = 1)
    (END : ℤ) (hEND : ∀ k : ℤ, END ≤ k →
      u k * hahn3jYH M σ N (xLat ((M : ℚ) + 1 / 2) ((σ : ℚ) + 1 / 2) ((N : ℚ) + 1 / 2) n) k = 0) :
    ∑ k ∈ Finset.Ico 0 END, (u k * hahn3jYH M σ N (xLat ((M : ℚ) + 1 / 2) ((σ : ℚ) + 1 / 2) ((N : ℚ) + 1 / 2) n) k) ^ 2 =
      (N : ℝ) + 1 / 2 := by
  set xx : ℚ := xLat ((M : ℚ) + 1 / 2) ((σ : ℚ) + 1 / 2) ((N : ℚ) + 1 / 2) n with hxx
  have hsq : ∀ j : ℤ, (u j * hahn3jYH M σ N xx j) ^ 2 = hahn3jYH M σ N xx j ^ 2 := by
    intro j; rw [mul_pow, hu j, one_mul]
  simp only [hsq]
  have hlo0 := halfLo_nonneg M σ
  set lo : ℤ := halfLo M σ with hlodef
  have hzero : ∀ k : ℤ, END ≤ k → hahn3jYH M σ N xx k = 0 := by
    intro k hk
    have := hEND k hk
    rcases mul_eq_zero.1 this with h1 | h1
    · have := hu k; rw [h1] at this; norm_num at this
    · exact h1
  have e1 : ∑ k ∈ Finset.Ico 0 (max END N), hahn3jYH M σ N xx k ^ 2 = ∑ k ∈ Finset.Ico 0 END, hahn3jYH M σ N xx k ^ 2 := by
    symm
    apply Finset.sum_subset
    · intro k hk; rw [Finset.mem_Ico] at hk ⊢; have := le_max_left END N; omega
    · intro k hk hk'
      rw [Finset.mem_Ico] at hk hk'
      have : END ≤ k := by by_contra hh; exact hk' ⟨hk.1, by omega⟩
      rw [hzero k this]; simp
  have e2 : ∑ k ∈ Finset.Ico lo N, hahn3jYH M σ N xx k ^ 2 = ∑ k ∈ Finset.Ico 0 (max END N), hahn3jYH M σ N xx k ^ 2 := by
    apply Finset.sum_subset
    · intro k hk; rw [Finset.mem_Ico] at hk ⊢; have := le_max_right END N; omega
    · intro k hk hk'
      rw [Finset.mem_Ico] at hk hk'
      rw [hahn_chain_support_half M σ N xx k (fun h => hk' ⟨h.1, by omega⟩)]; simp
  have hIco : Finset.Ico lo N = (Finset.range (N - lo).toNat).image (fun i : ℕ => lo + (i : ℤ)) := by
    ext k
    simp only [Finset.mem_Ico, Finset.mem_image, Finset.mem_range]
    constructor
    · intro hk
      exact ⟨(k - lo).toNat, by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩
      omega
  rw [← e1, ← e2, hIco, Finset.sum_image (by intro i _ j _ hij; simpa using hij)]
  exact bkh_sumH M σ N hN n hn

/-- Hard-edge monotone tail of the (twisted) half-integer `3j` chain beyond `q_* + h` (`h = 1/(N+½)`, hard edge `ẽ(1) = 0` at `q = (N+½)h`). -/
lemma bkh_monoH {τ x qs : ℝ} (hqs : 0 < qs) (hτ : τ ^ 2 = 1) (hκ : 0 < 1 - τ * x) (hturn : Phi 1 0 τ x (qs ^ 2) = 0)
    (a b : ℝ) (N : ℤ) (hN : 0 ≤ N) (Y0 u : ℤ → ℝ) (hu : ∀ k, u k ^ 2 = 1)
    (hsupp0 : ∀ k : ℤ, N ≤ k → Y0 k = 0)
    (hhM : 1 / ((N : ℝ) + 1 / 2) * (2 * hrM a b) ≤ qs)
    (hhC : 1 / ((N : ℝ) + 1 / 2) * hrRho 1 0 a b qs ≤ 2 * ((1 - τ * x) / qs ^ 2) * qs)
    (hrows : ∀ k : ℤ, 1 ≤ k → jac (hrAkH 1 0 a b (1 / ((N : ℝ) + 1 / 2))) (hrCkH 1 0 τ x a b (1 / ((N : ℝ) + 1 / 2)))
      (fun j => u j * Y0 j) k = 0) :
    ∀ k' k : ℤ, qs + 1 / ((N : ℝ) + 1 / 2) ≤ ((k' : ℝ) + 1) * (1 / ((N : ℝ) + 1 / 2)) → k' ≤ k →
      (u k * Y0 k) ^ 2 ≤ (u k' * Y0 k') ^ 2 := by
  intro k' k hk' hkk
  have hNr : (0 : ℝ) < (N : ℝ) + 1 / 2 := by
    have : (0 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hh : (0 : ℝ) < 1 / ((N : ℝ) + 1 / 2) := by positivity
  have hsq : ∀ j : ℤ, (u j * Y0 j) ^ 2 = Y0 j ^ 2 := by
    intro j; rw [mul_pow, hu j, one_mul]
  have hk'0 : 0 ≤ k' := by
    have h1 : (0 : ℝ) < ((k' : ℝ) + 1) * (1 / ((N : ℝ) + 1 / 2)) := by nlinarith only [hk', hqs, hh]
    have h2 : (-1 : ℝ) < k' := by
      by_contra hc; push Not at hc; nlinarith only [h1, hc, hh]
    have : (-1 : ℤ) < k' := by exact_mod_cast h2
    omega
  rw [hsq, hsq]
  by_cases hbig : N - 1 < k'
  · rw [hsupp0 k (by omega)]
    simpa using sq_nonneg (Y0 k')
  push Not at hbig
  by_cases hbig2 : N - 1 < k
  · rw [hsupp0 k (by omega)]
    simpa using sq_nonneg (Y0 k')
  push Not at hbig2
  obtain ⟨kmax, hkmax⟩ : ∃ kmax : ℕ, (kmax : ℤ) = N - 1 := ⟨(N - 1).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hNk : (((kmax : ℝ) + 1) + 1 / 2) * (1 / ((N : ℝ) + 1 / 2)) = 1 := by
    have : (((kmax : ℝ) + 1) + 1 / 2) = (N : ℝ) + 1 / 2 := by
      have : ((kmax : ℤ) : ℝ) = ((N - 1 : ℤ) : ℝ) := by rw [hkmax]
      push_cast at this; linarith
    rw [this]; field_simp
  have hedge : ((((kmax : ℝ) + 1) + 1 / 2) * (1 / ((N : ℝ) + 1 / 2))) ^ 2 ∈ Dom 1 0 := by
    rw [hNk]; refine ⟨by norm_num, by norm_num, by norm_num⟩
  have hedge0 : etilde 1 0 (((((kmax : ℝ) + 1) + 1 / 2) * (1 / ((N : ℝ) + 1 / 2))) ^ 2) = 0 := by
    rw [hNk, etilde_hahn]; simp
  have key := hr_hardedge_decayH (P := 1) (Q := 0) zero_le_one le_rfl a b τ x qs (1 / ((N : ℝ) + 1 / 2)) hqs hh hτ hκ hturn hhM hhC
    kmax k'.toNat hedge hedge0
    (by
      have : ((k'.toNat : ℕ) : ℝ) = (k' : ℝ) := by
        have : ((k'.toNat : ℕ) : ℤ) = k' := Int.toNat_of_nonneg hk'0
        exact_mod_cast this
      rw [this]; nlinarith only [hk', hh])
    (by omega)
    (fun j => u j * Y0 j)
    (fun k hk => hrows k (by rw [Finset.mem_Icc] at hk; omega))
  have := key k (by omega) (by omega)
  have h2 : (|u k * Y0 k|) ^ 2 ≤ (|u (k'.toNat : ℤ) * Y0 (k'.toNat : ℤ)|) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) this 2
  have e : ((k'.toNat : ℕ) : ℤ) = k' := Int.toNat_of_nonneg hk'0
  rw [e, sq_abs, sq_abs, hsq, hsq] at h2
  exact h2

/-- **The half-integer `3j` chain satisfies the hypotheses of the abstract sharp theorem** (see the module docstring): constants and `BkOut` for the family `bkFamHahnH`. -/
theorem bk_hahn_half (M σ : ℤ) (x : ℚ) (τ : ℝ) (u : ℤ → ℝ) (hxτ : (τ = 1 ∧ 0 < (x : ℝ)) ∨ (τ = -1 ∧ (x : ℝ) < 0))
    (hx1 : |(x : ℝ)| < 1) (hu : ∀ k, u k ^ 2 = 1)
    (hrowsAll : ∀ N : ℤ, 0 ≤ N → ∀ k : ℤ, 1 ≤ k →
      jac (hrAkH 1 0 ((M : ℝ) + 1 / 2) ((σ : ℝ) + 1 / 2) (1 / ((N : ℝ) + 1 / 2)))
        (hrCkH 1 0 τ (x : ℝ) ((M : ℝ) + 1 / 2) ((σ : ℝ) + 1 / 2) (1 / ((N : ℝ) + 1 / 2)))
        (fun j => u j * hahn3jYH M σ N x j) k = 0) :
    ∃ (r Cmu ξ0 gmax gmin c1 c2 CA δA hm : ℝ), 0 < r ∧ r ≤ √(1 - (x : ℝ) ^ 2) / 4 ∧ 0 < CA ∧ 0 < Cmu ∧ 0 < ξ0 ∧ 0 < gmax ∧
      0 < gmin ∧ gmin ≤ gmax ∧ 0 < c1 ∧ c1 ≤ c2 ∧ 0 < δA ∧ 0 < hm ∧
      BkOut 1 (fun δ => δ ^ 3) 1 0 τ (x : ℝ) (√(1 - (x : ℝ) ^ 2)) (bkFamHahnH M σ x u hm) r Cmu ξ0 gmax gmin c1 c2 CA δA := by
  obtain ⟨hqs, hτ, hκ, hα, hβ, hturn⟩ := bkh_geom hxτ hx1
  set qs : ℝ := √(1 - (x : ℝ) ^ 2) with hqsdef
  have hP : (0 : ℝ) ≤ 1 := zero_le_one
  have hQ : (0 : ℝ) ≤ 0 := le_rfl
  have hs := rk_turn_id hP hQ hτ hα hβ hturn
  have hS : rkS 1 0 (x : ℝ) = 1 := by simp [rkS]
  have hspos : 0 < rkS 1 0 (x : ℝ) := by rw [hS]; norm_num
  set ρ : ℝ := hrRho 1 0 ((M : ℝ) + 1 / 2) ((σ : ℝ) + 1 / 2) qs with hρ
  have hρ0 : 0 ≤ ρ := by rw [hρ]; unfold hrRho; positivity
  have hM1 : 1 ≤ hrM ((M : ℝ) + 1 / 2) ((σ : ℝ) + 1 / 2) := le_max_left _ _
  have hκq : 0 ≤ 2 * ((1 - τ * (x : ℝ)) / qs ^ 2) * qs := by positivity
  set hm : ℝ := min (qs / (2 * hrM ((M : ℝ) + 1 / 2) ((σ : ℝ) + 1 / 2))) ((2 * ((1 - τ * (x : ℝ)) / qs ^ 2) * qs) / (ρ + 1)) with hhm
  have hmpos : 0 < hm := lt_min (by positivity) (by
    apply div_pos _ (by positivity)
    have : 0 < (1 - τ * (x : ℝ)) / qs ^ 2 := by positivity
    positivity)
  set kmin : ℤ := halfLo M σ with hkmin
  have hkmin0 : 0 ≤ kmin := halfLo_nonneg M σ
  have hka : |(M : ℝ) + 1 / 2| ≤ (kmin : ℝ) + 1 / 2 := by
    have h1 : M ≤ kmin := by rw [hkmin]; unfold halfLo; omega
    have h2 : -M - 1 ≤ kmin := by rw [hkmin]; unfold halfLo; omega
    have h1' : (M : ℝ) ≤ (kmin : ℝ) := by exact_mod_cast h1
    have h2' : -(M : ℝ) - 1 ≤ (kmin : ℝ) := by exact_mod_cast h2
    rw [abs_le]; constructor <;> linarith
  have hkb : |(σ : ℝ) + 1 / 2| ≤ (kmin : ℝ) + 1 / 2 := by
    have h1 : σ ≤ kmin := by rw [hkmin]; unfold halfLo; omega
    have h2 : -σ - 1 ≤ kmin := by rw [hkmin]; unfold halfLo; omega
    have h1' : (σ : ℝ) ≤ (kmin : ℝ) := by exact_mod_cast h1
    have h2' : -(σ : ℝ) - 1 ≤ (kmin : ℝ) := by exact_mod_cast h2
    rw [abs_le]; constructor <;> linarith
  have hsqY : ∀ (N : ℤ) (j : ℤ), (u j * hahn3jYH M σ N x j) ^ 2 = hahn3jYH M σ N x j ^ 2 := by
    intro N j; rw [mul_pow, hu j, one_mul]
  set Fam := bkFamHahnH M σ x u hm with hFam
  have hrowsF : ∀ h Y Mm, Fam h Y Mm → ∀ k : ℤ, 1 ≤ k →
      jac (hrAkH 1 0 ((M : ℝ) + 1 / 2) ((σ : ℝ) + 1 / 2) h) (hrCkH 1 0 τ (x : ℝ) ((M : ℝ) + 1 / 2) ((σ : ℝ) + 1 / 2) h) Y k = 0 := by
    rintro h Y Mm ⟨hh, hhm, N, n, hN, hn, hxn, rfl, rfl, rfl⟩ k hk
    have hN0 : 0 ≤ N := le_trans (halfLo_nonneg M σ) hN.le
    exact hrowsAll N hN0 k hk
  have hNpos : ∀ N : ℤ, halfLo M σ < N → (0 : ℝ) < (N : ℝ) + 1 / 2 := by
    intro N hN
    have : (0 : ℝ) ≤ N := by exact_mod_cast (le_trans (halfLo_nonneg M σ) hN.le)
    linarith
  have hmassF : ∀ h Y Mm, Fam h Y Mm → 0 < h → Mm * h * Real.sqrt (rkS 1 0 (x : ℝ)) = 1 := by
    rintro h Y Mm ⟨hh, hhm, N, n, hN, hn, hxn, rfl, rfl, rfl⟩ -
    have hN0 := hNpos N hN
    rw [hS, Real.sqrt_one, mul_one]; exact mul_one_div_cancel hN0.ne'
  have hYleF : ∀ h Y Mm, Fam h Y Mm → ∀ k : ℤ, Y k ^ 2 ≤ Mm := by
    rintro h Y Mm ⟨hh, hhm, N, n, hN, hn, hxn, rfl, rfl, rfl⟩ k
    show (u k * hahn3jYH M σ N x k) ^ 2 ≤ (N : ℝ) + 1 / 2
    rw [hsqY]
    have h1 := hahn_chain_abs_le_half M σ N hN n hn k
    rw [hxn] at h1
    have h2 := (hNpos N hN).le
    calc hahn3jYH M σ N x k ^ 2 = |hahn3jYH M σ N x k| ^ 2 := (sq_abs _).symm
      _ ≤ Real.sqrt ((N : ℝ) + 1 / 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = (N : ℝ) + 1 / 2 := Real.sq_sqrt h2
  have hsuppF : ∀ h Y Mm, Fam h Y Mm → ∀ k : ℤ, 1 < ((k : ℝ) + 1) * h → Y k = 0 := by
    rintro h Y Mm ⟨hh, hhm, N, n, hN, hn, hxn, rfl, rfl, rfl⟩ k hk
    have hN0 := hNpos N hN
    have h1 : (N : ℝ) + 1 / 2 < (k : ℝ) + 1 := by
      rw [← div_eq_mul_one_div, lt_div_iff₀ hN0] at hk; linarith
    have h2 : N ≤ k := by
      by_contra hc; push Not at hc
      have : (k : ℝ) + 1 ≤ N := by exact_mod_cast (by omega : k + 1 ≤ N)
      linarith
    show u k * hahn3jYH M σ N x k = 0
    rw [hahn_chain_support_half M σ N x k (fun h => by omega), mul_zero]
  have hMeqF : ∀ h Y Mm, Fam h Y Mm → ∀ END : ℤ, (∀ k : ℤ, END ≤ k → Y k = 0) → ∑ k ∈ Finset.Ico 0 END, Y k ^ 2 = Mm := by
    rintro h Y Mm ⟨hh, hhm, N, n, hN, hn, rfl, rfl, rfl, rfl⟩ END hEND
    exact bkh_meqH M σ N hN n hn u hu END hEND
  have hmonoF : ∀ h Y Mm, Fam h Y Mm → ∀ k' k : ℤ, qs + h ≤ ((k' : ℝ) + 1) * h → k' ≤ k → Y k ^ 2 ≤ Y k' ^ 2 := by
    rintro h Y Mm ⟨hh, hhm, N, n, hN, hn, hxn, rfl, rfl, rfl⟩ k' k hk' hkk
    have hN0 := hNpos N hN
    have h1 : 1 / ((N : ℝ) + 1 / 2) ≤ qs / (2 * hrM ((M : ℝ) + 1 / 2) ((σ : ℝ) + 1 / 2)) := hhm.trans (min_le_left _ _)
    have h2 : 1 / ((N : ℝ) + 1 / 2) ≤ (2 * ((1 - τ * (x : ℝ)) / qs ^ 2) * qs) / (ρ + 1) := hhm.trans (min_le_right _ _)
    have hhM : 1 / ((N : ℝ) + 1 / 2) * (2 * hrM ((M : ℝ) + 1 / 2) ((σ : ℝ) + 1 / 2)) ≤ qs := by
      rw [le_div_iff₀ (by positivity)] at h1; linarith only [h1]
    have hhC : 1 / ((N : ℝ) + 1 / 2) * ρ ≤ 2 * ((1 - τ * (x : ℝ)) / qs ^ 2) * qs := by
      rw [le_div_iff₀ (by positivity)] at h2
      nlinarith only [h2, hρ0, hκq, hh]
    exact bkh_monoH hqs hτ hκ hturn ((M : ℝ) + 1 / 2) ((σ : ℝ) + 1 / 2) N (le_trans (halfLo_nonneg M σ) hN.le)
      (hahn3jYH M σ N x) u hu
      (fun k hk => hahn_chain_support_half M σ N x k (fun h => by omega)) hhM hhC
      (fun k hk => hrowsAll N (le_trans (halfLo_nonneg M σ) hN.le) k hk) k' k hk' hkk
  have hlowF : ∀ h Y Mm, Fam h Y Mm → ∀ k : ℤ, k < kmin → Y k = 0 := by
    rintro h Y Mm ⟨hh, hhm, N, n, hN, hn, hxn, rfl, rfl, rfl⟩ k hk
    show u k * hahn3jYH M σ N x k = 0
    rw [hahn_chain_support_half M σ N x k (fun h => by omega), mul_zero]
  have hLeftF := rl_leftH (a := (M : ℝ) + 1 / 2) (b := (σ : ℝ) + 1 / 2) (kl := kmin) hP hQ hτ hs hspos hqs hα hβ hka hkb hkmin0 Fam hrowsF
    hlowF (rk_mleH hsuppF hMeqF)
  obtain ⟨r, Cmu, ξ0, gmax, gmin, c1, c2, CA, δA, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, H⟩ :=
    bk_sharp_absH hP hQ ((M : ℝ) + 1 / 2) ((σ : ℝ) + 1 / 2) τ (x : ℝ) qs hqs hτ hκ hα hβ hturn
      (rk_hosc0 hP hQ hτ hqs hκ hα hβ hturn) 1 zero_le_one Fam hrowsF hmassF hYleF hsuppF hMeqF hmonoF hLeftF
  exact ⟨r, Cmu, ξ0, gmax, gmin, c1, c2, CA, δA, hm, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hmpos, H⟩

/-- info: 'FormalResearch.Special.bk_hahn_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.bk_hahn_half

end FormalResearch.Special
