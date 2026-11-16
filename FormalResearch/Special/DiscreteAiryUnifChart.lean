module

public import FormalResearch.Special.DiscreteAiryUnifJet

/-!
# Uniform discrete-to-Airy, step 5: the Langer coordinate on an explicit ball with explicit jet bounds

`langerZetaOf F c = (q - c)(3M/2)^{2/3}`, `M = ∫₀¹ √t √G(c + t(q-c)) dt`, `G = dslope F c` (`LangerCoordinate`), is
`C³` near `c`, with a radius that is not explicit.  `dun_chart` makes it explicit: for `F` with `F(c) = 0`, `F' = P`, where `P ≥ m > 0`
and `J2 P (ball c ρ) K₀ K₁ K₂` (so `F` has `C³` jets bounded by `K`), the coordinate `ζ = langerZetaOf F c` is `C³` on the whole ball
`ball c ρ`, with `ζ ζ'² = F`, and `J2 ζ' (ball c ρ) d₀ d₁ d₂`, `c₁ ≤ ζ'` where `c₁, d₀, d₁, d₂` depend only on `(m, ρ, K₀, K₁, K₂)`
(not on `F, c`).  The proof is the chain `P → G → √G → M → (3M/2)^{-1/3} → ζ' = √G (3M/2)^{-1/3}` in the jet calculus of
`DiscreteAiryUnifJet`; `ζ' = √G/(3M/2)^{1/3}` is `hasDerivAt_langer_aux`.

**Claim class: proved.**
-/

@[expose] public section

open Set Filter Topology MeasureTheory Metric

namespace FormalResearch.Special

lemma contDiffOn_succ_of_hasDerivAt {f g : ℝ → ℝ} {S : Set ℝ} (hS : IsOpen S) (n : ℕ)
    (hd : ∀ x ∈ S, HasDerivAt f (g x) x) (hg : ContDiffOn ℝ n g S) :
    ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f S := by
  rw [Nat.cast_succ, contDiffOn_succ_iff_deriv_of_isOpen hS]
  exact ⟨fun x hx => (hd x hx).differentiableAt.differentiableWithinAt, by simp,
    hg.congr fun x hx => (hd x hx).deriv⟩

lemma hadInt_congr {w K K' : ℝ → ℝ} {c ρ q : ℝ} (h : ∀ x ∈ ball c ρ, K x = K' x) (hq : q ∈ ball c ρ) :
    hadInt w K c q = hadInt w K' c q := by
  unfold hadInt
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa [uIcc_of_le zero_le_one] using ht
  simp only [h _ (hadInt_mem_ball hq ht')]

lemma integral_one_zero_one : ∫ t in (0 : ℝ)..1, (fun _ : ℝ => (1 : ℝ)) t = 1 := by simp

/-- Jets of `G = dslope F c` from those of `P = F'`. -/
lemma chart_G {F P : ℝ → ℝ} {c ρ K0 K1 K2 m : ℝ} (hP : J2 P (ball c ρ) K0 K1 K2)
    (hFd : ∀ x ∈ ball c ρ, HasDerivAt F (P x) x) (hPm : ∀ x ∈ ball c ρ, m ≤ P x) :
    J2 (dslope F c) (ball c ρ) K0 K1 K2 ∧ ∀ x ∈ ball c ρ, m ≤ dslope F c x := by
  have hF1 : ContDiffOn ℝ 1 F (ball c ρ) := by
    have := contDiffOn_succ_of_hasDerivAt isOpen_ball 0 hFd (by simpa using hP.1.continuousOn)
    simpa using this
  have hF3 : ContDiffOn ℝ ((2 + 1 : ℕ) : WithTop ℕ∞) F (ball c ρ) :=
    contDiffOn_succ_of_hasDerivAt isOpen_ball 2 hFd (by simpa using hP.1)
  have hderP : ∀ x ∈ ball c ρ, deriv F x = P x := fun x hx => (hFd x hx).deriv
  have hdsl : ∀ q ∈ ball c ρ, dslope F c q = hadInt (fun _ => 1) P c q := fun q hq => by
    rw [dslope_eq_hadInt hF1 hq]
    exact hadInt_congr hderP hq
  have hJ := J2.hadamard (c := c) (ρ := ρ) (w := fun _ => (1 : ℝ)) continuous_const
    (fun t _ => ⟨zero_le_one, le_rfl⟩) hP
  refine ⟨hJ.congr isOpen_ball hdsl, fun q hq => ?_⟩
  have := hadInt_ge (w := fun _ => (1 : ℝ)) (K := P) (c := c) (ρ := ρ) (q := q) (ℓ := m) continuous_const
    (fun t _ => zero_le_one) hP.1.continuousOn hPm hq
  rw [hdsl q hq]
  simpa using this


/-- **The quantitative Langer coordinate.**  See the module docstring. -/
theorem dun_chart (m ρ K0 K1 K2 : ℝ) (hm : 0 < m) :
    ∃ c1 d0 d1 d2 : ℝ, 0 < c1 ∧ ∀ {F P : ℝ → ℝ} {c : ℝ}, J2 P (ball c ρ) K0 K1 K2 →
      (∀ x ∈ ball c ρ, HasDerivAt F (P x) x) → F c = 0 → (∀ x ∈ ball c ρ, m ≤ P x) →
      ContDiffOn ℝ 3 (langerZetaOf F c) (ball c ρ) ∧ J2 (deriv (langerZetaOf F c)) (ball c ρ) d0 d1 d2 ∧
      (∀ x ∈ ball c ρ, c1 ≤ deriv (langerZetaOf F c) x) ∧
      (∀ x ∈ ball c ρ, langerZetaOf F c x * deriv (langerZetaOf F c) x ^ 2 = F x) ∧
      (∀ x ∈ ball c ρ, x ≠ c → langerZetaOf F c x ≠ 0) := by
  have hm2 : 0 < m ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hm _
  -- jets of `G^(1/2)`
  set R0 : ℝ := max (m ^ (1 / 2 : ℝ)) (K0 ^ (1 / 2 : ℝ)) with hR0
  set R1 : ℝ := max (m ^ (1 / 2 - 1 : ℝ)) (K0 ^ (1 / 2 - 1 : ℝ)) with hR1
  set R2 : ℝ := max (m ^ (1 / 2 - 1 - 1 : ℝ)) (K0 ^ (1 / 2 - 1 - 1 : ℝ)) with hR2
  have hk0 : 0 < R0 := lt_of_lt_of_le hm2 (le_max_left _ _)
  have hK : ∀ {c : ℝ} {G : ℝ → ℝ}, J2 G (ball c ρ) K0 K1 K2 → (∀ x ∈ ball c ρ, m ≤ G x) →
      J2 (fun s => G s ^ (1 / 2 : ℝ)) (ball c ρ) R0 (K1 * |(1 / 2 : ℝ)| * R1)
        (K2 * |(1 / 2 : ℝ)| * R1 + K1 * (|(1 / 2 : ℝ)| * |(1 / 2 : ℝ) - 1|) * R2 * K1) := by
    intro c G hG hGm
    have hup : ∀ x ∈ ball c ρ, G x ≤ K0 := fun x hx => (le_abs_self _).trans (hG.2 x hx).1
    exact J2.rpow (1 / 2) (R0 := R0) (R1 := R1) (R2 := R2) isOpen_ball hG hm hGm
      (fun x hx => rpow_le_max_of_mem _ hm (hGm x hx) (hup x hx))
      (fun x hx => rpow_le_max_of_mem _ hm (hGm x hx) (hup x hx))
      (fun x hx => rpow_le_max_of_mem _ hm (hGm x hx) (hup x hx))
  set k0 : ℝ := R0 with hk0def
  set k1 : ℝ := K1 * |(1 / 2 : ℝ)| * R1 with hk1def
  set k2 : ℝ := K2 * |(1 / 2 : ℝ)| * R1 + K1 * (|(1 / 2 : ℝ)| * |(1 / 2 : ℝ) - 1|) * R2 * K1 with hk2def
  -- jets of `N^(-1/3)`, `N = (3/2) M`
  set S0 : ℝ := max ((m ^ (1 / 2 : ℝ)) ^ (-(1 / 3 : ℝ))) ((|(3 / 2 : ℝ)| * k0) ^ (-(1 / 3 : ℝ))) with hS0
  set S1 : ℝ := max ((m ^ (1 / 2 : ℝ)) ^ (-(1 / 3 : ℝ) - 1)) ((|(3 / 2 : ℝ)| * k0) ^ (-(1 / 3 : ℝ) - 1)) with hS1
  set S2 : ℝ := max ((m ^ (1 / 2 : ℝ)) ^ (-(1 / 3 : ℝ) - 1 - 1))
    ((|(3 / 2 : ℝ)| * k0) ^ (-(1 / 3 : ℝ) - 1 - 1)) with hS2
  have hE : ∀ {c : ℝ} {N : ℝ → ℝ},
      J2 N (ball c ρ) (|(3 / 2 : ℝ)| * k0) (|(3 / 2 : ℝ)| * k1) (|(3 / 2 : ℝ)| * k2) →
      (∀ x ∈ ball c ρ, m ^ (1 / 2 : ℝ) ≤ N x) →
        J2 (fun x => N x ^ (-(1 / 3 : ℝ))) (ball c ρ) S0 ((|(3 / 2 : ℝ)| * k1) * |(-(1 / 3 : ℝ))| * S1)
          ((|(3 / 2 : ℝ)| * k2) * |(-(1 / 3 : ℝ))| * S1 + (|(3 / 2 : ℝ)| * k1) *
            (|(-(1 / 3 : ℝ))| * |(-(1 / 3 : ℝ)) - 1|) * S2 * (|(3 / 2 : ℝ)| * k1)) := by
    intro c N hN hNm
    have hup : ∀ x ∈ ball c ρ, N x ≤ |(3 / 2 : ℝ)| * k0 := fun x hx => (le_abs_self _).trans (hN.2 x hx).1
    exact J2.rpow (-(1 / 3)) (R0 := S0) (R1 := S1) (R2 := S2) isOpen_ball hN hm2 hNm
      (fun x hx => rpow_le_max_of_mem _ hm2 (hNm x hx) (hup x hx))
      (fun x hx => rpow_le_max_of_mem _ hm2 (hNm x hx) (hup x hx))
      (fun x hx => rpow_le_max_of_mem _ hm2 (hNm x hx) (hup x hx))
  set e0 : ℝ := S0 with he0
  set e1 : ℝ := (|(3 / 2 : ℝ)| * k1) * |(-(1 / 3 : ℝ))| * S1 with he1
  set e2 : ℝ := (|(3 / 2 : ℝ)| * k2) * |(-(1 / 3 : ℝ))| * S1 + (|(3 / 2 : ℝ)| * k1) *
            (|(-(1 / 3 : ℝ))| * |(-(1 / 3 : ℝ)) - 1|) * S2 * (|(3 / 2 : ℝ)| * k1) with he2
  have hb0 : 0 < |(3 / 2 : ℝ)| * k0 := by positivity
  refine ⟨m ^ (1 / 2 : ℝ) * (|(3 / 2 : ℝ)| * k0) ^ (-(1 / 3 : ℝ)), k0 * e0, k1 * e0 + k0 * e1,
    k2 * e0 + 2 * (k1 * e1) + k0 * e2, by positivity, ?_⟩
  intro F P c hP hFd hF0 hPm
  obtain ⟨hGj, hGm⟩ := chart_G hP hFd hPm
  set G : ℝ → ℝ := dslope F c with hG
  have hKj := hK hGj hGm
  have hKe : (fun s => √(G s)) = fun s => G s ^ (1 / 2 : ℝ) := by
    funext s; exact Real.sqrt_eq_rpow _
  have hKj' : J2 (fun s => √(G s)) (ball c ρ) k0 k1 k2 := by rw [hKe]; exact hKj
  have hGpos : ∀ x ∈ ball c ρ, 0 < G x := fun x hx => lt_of_lt_of_le hm (hGm x hx)
  have hKlow : ∀ x ∈ ball c ρ, m ^ (1 / 2 : ℝ) ≤ √(G x) := fun x hx => by
    rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow hm.le (hGm x hx) (by norm_num)
  -- the Hadamard integral `M`
  set M : ℝ → ℝ := hadInt (fun t => √t) (fun s => √(G s)) c with hMdef
  have hMj : J2 M (ball c ρ) k0 k1 k2 :=
    J2.hadamard Real.continuous_sqrt (fun t ht => ⟨Real.sqrt_nonneg _, by
      calc √t ≤ √1 := Real.sqrt_le_sqrt ht.2
        _ = 1 := Real.sqrt_one⟩) hKj'
  have hMlow : ∀ x ∈ ball c ρ, 2 / 3 * m ^ (1 / 2 : ℝ) ≤ M x := fun x hx => by
    have := hadInt_ge (w := fun t => √t) (K := fun s => √(G s)) (c := c) (ρ := ρ) (q := x)
      (ℓ := m ^ (1 / 2 : ℝ)) Real.continuous_sqrt (fun t _ => Real.sqrt_nonneg _)
      (hKj'.1.continuousOn) hKlow hx
    rw [integral_sqrt_zero_one] at this
    linarith
  have hNj : J2 (fun x => 3 / 2 * M x) (ball c ρ) (|(3 / 2 : ℝ)| * k0) (|(3 / 2 : ℝ)| * k1)
      (|(3 / 2 : ℝ)| * k2) := J2.const_mul isOpen_ball (3 / 2) hMj
  have hNlow : ∀ x ∈ ball c ρ, m ^ (1 / 2 : ℝ) ≤ 3 / 2 * M x := fun x hx => by
    have := hMlow x hx; linarith
  have hNpos : ∀ x ∈ ball c ρ, 0 < 3 / 2 * M x := fun x hx => lt_of_lt_of_le hm2 (hNlow x hx)
  have hNup : ∀ x ∈ ball c ρ, 3 / 2 * M x ≤ |(3 / 2 : ℝ)| * k0 := fun x hx =>
    (le_abs_self _).trans (hNj.2 x hx).1
  have hEj := hE hNj hNlow
  have hDj := J2.mul isOpen_ball hKj hEj
  -- the derivative of `ζ`
  set ζ : ℝ → ℝ := langerZetaOf F c with hζ
  have hKc1 : ContDiffOn ℝ 1 (fun s => √(G s)) (ball c ρ) := hKj'.1.of_le (by norm_num)
  have hder : ∀ q ∈ ball c ρ, HasDerivAt ζ (G q ^ (1 / 2 : ℝ) * (3 / 2 * M q) ^ (-(1 / 3 : ℝ))) q := by
    intro q hq
    have hMq : 0 < hadInt (fun t => √t) (fun s => √(G s)) c q := by
      have := hMlow q hq
      have : 0 < 2 / 3 * m ^ (1 / 2 : ℝ) := by positivity
      linarith [hMlow q hq]
    have := hasDerivAt_langer_aux hKc1 hq hMq
    have e : √(G q) / (3 / 2 * hadInt (fun t => √t) (fun s => √(G s)) c q) ^ (1 / 3 : ℝ) =
        G q ^ (1 / 2 : ℝ) * (3 / 2 * M q) ^ (-(1 / 3 : ℝ)) := by
      rw [Real.rpow_neg (hNpos q hq).le, div_eq_mul_inv, Real.sqrt_eq_rpow]
    rw [e] at this
    exact this
  have hderiv : ∀ q ∈ ball c ρ, deriv ζ q = G q ^ (1 / 2 : ℝ) * (3 / 2 * M q) ^ (-(1 / 3 : ℝ)) :=
    fun q hq => (hder q hq).deriv
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := contDiffOn_succ_of_hasDerivAt isOpen_ball 2 hder hDj.1
    simpa using this
  · exact hDj.congr isOpen_ball hderiv
  · intro x hx
    rw [hderiv x hx]
    have h1 : m ^ (1 / 2 : ℝ) ≤ G x ^ (1 / 2 : ℝ) := Real.rpow_le_rpow hm.le (hGm x hx) (by norm_num)
    have h2 : (|(3 / 2 : ℝ)| * k0) ^ (-(1 / 3 : ℝ)) ≤ (3 / 2 * M x) ^ (-(1 / 3 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (hNpos x hx) (hNup x hx) (by norm_num)
    exact mul_le_mul h1 h2 (by positivity) (Real.rpow_pos_of_pos (hGpos x hx) _).le
  · intro x hx
    have hxG := hGpos x hx
    have hKx : √(G x) ^ 2 = G x := Real.sq_sqrt hxG.le
    have hsub := sub_smul_dslope F c x
    rw [smul_eq_mul, hF0, sub_zero] at hsub
    have hderx := (hder x hx).deriv
    have hMx : 0 < hadInt (fun t => √t) (fun s => √(G s)) c x := by
      have := hMlow x hx
      have : 0 < 2 / 3 * m ^ (1 / 2 : ℝ) := by positivity
      linarith [hMlow x hx]
    have hax : 0 < (3 / 2 * hadInt (fun t => √t) (fun s => √(G s)) c x) ^ (1 / 3 : ℝ) :=
      Real.rpow_pos_of_pos (by positivity) _
    have hd' : deriv ζ x = √(G x) / (3 / 2 * hadInt (fun t => √t) (fun s => √(G s)) c x) ^ (1 / 3 : ℝ) := by
      have := hasDerivAt_langer_aux hKc1 hx hMx
      exact this.deriv
    rw [hd']
    show (x - c) * langerA F c x ^ 2 * (√(G x) / langerA F c x) ^ 2 = F x
    have hA' : langerA F c x = (3 / 2 * hadInt (fun t => √t) (fun s => √(G s)) c x) ^ (1 / 3 : ℝ) := rfl
    rw [hA']
    field_simp
    rw [hKx]
    linarith [hsub]
  · intro x hx hxc
    have hax : 0 < langerA F c x := Real.rpow_pos_of_pos (hNpos x hx) _
    show (x - c) * langerA F c x ^ 2 ≠ 0
    exact mul_ne_zero (sub_ne_zero.2 hxc) (by positivity)

/-- info: 'FormalResearch.Special.dun_chart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.dun_chart

end FormalResearch.Special
