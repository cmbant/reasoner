module

public import FormalResearch.Special.DiscreteAiryPhysFull
public import FormalResearch.Special.DiscreteAiryOscTurn

/-!
# `discrete_airy_full`: the unified discrete-to-Airy theorem at a simple turn (smooth data)

Smooth data `u ∈ C³`, `A ∈ C²` at a simple turn `c₀` (`u(c₀) = 1`, `u'(c₀) > 0`, `A(c₀) > 0`), Langer coordinate `ζ`, amplitude `g`,
lattice `q_k = q₀ + kδ³`, `X_k = ζ(q_k)/δ²`, `φ_k = g(q_k) Ai(X_k)`, `ψ_k = g(q_k) Bi(X_k)`.  For every `E ≥ 0` and `r₀ > 0` there are
`r ≤ r₀`, `δ₀`, `C`, `Cmu`, `ξ₀ > 0` such that for `δ ≤ δ₀` and every `q₀` there are indices `J < N`, `J ≤ m ≤ N` with
`q_J ∈ [c₀ - r, c₀ - r + δ³)`, `q_m ∈ [c₀, c₀ + δ³)`, `q_N ≥ c₀ + r/4`, `q_{N+1} ≤ c₀ + r/2`, and for **all** `a, c` with
`|a_k - A(q_k - δ³/2)| ≤ Eδ⁶` (`k ∈ [J+1, N+1]`), `|c_k - 2A(q_k)u(q_k)| ≤ Eδ⁶` (`k ∈ [J+1, N]`) the unified conclusion `DaiFull`
(`DiscreteAiryPhysFull`):

* the recessive solution `f` is **the unique** exact solution of the rows with `f = g Ai(X)` at `N, N+1`, and
  `|f - φ| ≤ C δ³ airyWt(X)` on the whole `[J, N+1]`;
* the dominant solution `F₂` is the unique exact solution with `F₂ = g Bi(X)` at `m, m+1`, and `|F₂ - ψ| ≤ C δ³ airyBiWt(X)` on the
  whole `[J, N+1]`;
* the Casoratian `cas(f, F₂)` is constant and `≥ δ/C`;
* every exact `Y` with `|Y_N|, |Y_{N+1}| ≤ Y_max` is `κ f + μ F₂` on `[J, N+1]` with `|μ| ≤ Cmu Y_max e^{-ξ(X_N)}/δ`, `ξ₀/δ³ ≤ ξ(X_N)`;
  pointwise (`DaiFull.pointwise`) `Y = κ g Ai + μ g Bi` up to `C δ³ (|κ| airyWt + |μ| airyBiWt)` on `[J, N+1]`.

This **strengthens** `dao_turn_conclusion` (`[J, N]` only, no uniqueness; same hypotheses, same `r`, `N`) and has the content of
`discrete_airy_limit` (window `X ≥ -A₀`, `e^{O(A₀²)}` constants) on the oscillatory side, with the same recessive `f` *when both are
normalised at the same `N`* (`dap_recessive_eq`); it does **not** formally supersede either.  *Caveat*: `discrete_airy_limit` chooses its own `r` (hence its own `N`); `r`, `N` here
are those of `dao_turn_conclusion`, so the identification of the two `f`'s is conditional on the same `N` and is **not** a formal
derivation of `discrete_airy_limit` from `discrete_airy_full`; both older theorems stay in place.

**Claim class: proved.**  Constants are explicit in the data of `dal_turn_data` and `dao_exact_defect_bi` (existential in the data).

**Numerics (mpmath, 50 digits, not a Lean claim).**  Closed-form Hahn chain `M = σ = 0`, `x = 1/2`, `N = 4t+2` (`t = 25, 50, 100, 200, 400`),
`q_J ≈ q_* - r`, `r = q_*/4`, `q_* = √3/2`: `sup |f - gAi|/(δ³ airyWt) = 0.217, 0.202, 0.192, 0.186, 0.183`,
`sup |F₂ - gBi|/(δ³ airyBiWt) = 0.173, 0.145, 0.140, 0.135, 0.137` (all of `[J, N+1]`, attained at `N+1` for `F₂`), `X_J` down to `-48`.

**Not formalised.**  `κ` (Darboux normalisation) and `κ ≠ 0` for general data (for the actual `3j` chain `κ ≠ 0` is `hahn_chain_kappa`, `DiscreteAiryKappaMain`, which repeats the proof of `discrete_airy_full` with chart data exported in `DiscreteAiryKappaChart`); uniformity in families of data; the `h²` phase coefficient; the unification
with `discrete_airy_limit` at the same `r`/`N` (only the abstract identification `dap_recessive_eq`).
-/

@[expose] public section

open Finset FormalResearch.DiscreteAiry

namespace FormalResearch.Special

lemma dap_cube_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) : δ ^ 3 ≤ δ := by
  nlinarith [pow_pos hδ 2, pow_pos hδ 3]

lemma dap_JN {q₀ δ c0 r : ℝ} {J N : ℤ} (hδ : 0 < δ) (h3 : δ ^ 3 ≤ r / 8)
    (h1 : dalQ q₀ δ J < c0 - r + δ ^ 3) (h2 : c0 + r / 4 ≤ dalQ q₀ δ N) : J < N := by
  by_contra hcon
  push Not at hcon
  have hle : (N : ℝ) ≤ J := by exact_mod_cast hcon
  have h3' : 0 < δ ^ 3 := by positivity
  unfold dalQ at h1 h2
  nlinarith

/-- `|c_N| ≤ 2 A_max (1 + L_u r) + E` for `|c_N - 2A(q)u(q)| ≤ E`, `q ∈ [c₀ - r, c₀ + r]`. -/
lemma dap_cN_bound {A u : ℝ → ℝ} {c0 q cN Amax Amin Lu r E E6 : ℝ} (hq : q ∈ Set.Icc (c0 - r) (c0 + r))
    (hAb : Amin ≤ A q ∧ A q ≤ Amax) (hAmin : 0 < Amin) (hlip : |u q - u c0| ≤ Lu * |q - c0|)
    (hu0 : u c0 = 1) (hLu : 0 ≤ Lu) (hc : |cN - 2 * A q * u q| ≤ E6) (hE6 : E6 ≤ E) :
    |cN| ≤ 2 * Amax * (1 + Lu * r) + E := by
  rw [hu0] at hlip
  have hdist : |q - c0| ≤ r := abs_le.2 ⟨by linarith [hq.1], by linarith [hq.2]⟩
  have hu1 : |u q - 1| ≤ Lu * r := hlip.trans (mul_le_mul_of_nonneg_left hdist hLu)
  have hu : |u q| ≤ 1 + Lu * r := by
    have := abs_sub_abs_le_abs_sub (u q) 1
    rw [abs_one] at this
    linarith
  have hApos : 0 < A q := lt_of_lt_of_le hAmin hAb.1
  have hAmax : 0 ≤ Amax := hApos.le.trans hAb.2
  have h2Au : |2 * A q * u q| ≤ 2 * Amax * (1 + Lu * r) := by
    rw [abs_mul, abs_mul, abs_of_pos hApos, abs_two]
    have := mul_le_mul hAb.2 hu (abs_nonneg _) hAmax
    nlinarith
  have : |cN| ≤ |cN - 2 * A q * u q| + |2 * A q * u q| := by
    have := abs_add_le (cN - 2 * A q * u q) (2 * A q * u q)
    simpa using this
  linarith

/-- **The unified discrete-to-Airy theorem at a simple turn** (see the module docstring). -/
theorem discrete_airy_full {u A : ℝ → ℝ} {c0 : ℝ} (hu : ContDiffAt ℝ 3 u c0) (h1 : u c0 = 1)
    (h2 : 0 < deriv u c0) (hA : ContDiffAt ℝ 2 A c0) (hA0 : 0 < A c0) {r0 : ℝ} (hr0 : 0 < r0)
    (E : ℝ) (hE : 0 ≤ E) :
    ∃ (r δ0 C Cmu ξ0 : ℝ), 0 < r ∧ r ≤ r0 ∧ 0 < δ0 ∧ δ0 ≤ 1 ∧ 0 < C ∧ 0 < Cmu ∧ 0 < ξ0 ∧
      ∀ δ q₀ : ℝ, 0 < δ → δ ≤ δ0 → ∃ J m N : ℤ, J < N ∧ J ≤ m ∧ m ≤ N ∧
        (∀ k ∈ Finset.Icc J (N + 1), dalQ q₀ δ k ∈ Set.Icc (c0 - r) (c0 + r)) ∧
        c0 - r ≤ dalQ q₀ δ J ∧ dalQ q₀ δ J < c0 - r + δ ^ 3 ∧ c0 ≤ dalQ q₀ δ m ∧
        dalQ q₀ δ m < c0 + δ ^ 3 ∧ c0 + r / 4 ≤ dalQ q₀ δ N ∧ dalQ q₀ δ (N + 1) ≤ c0 + r / 2 ∧
        ∀ a c : ℤ → ℝ,
          (∀ k ∈ Finset.Icc (J + 1) (N + 1), |a k - A (dalQ q₀ δ k - δ ^ 3 / 2)| ≤ E * δ ^ 6) →
          (∀ k ∈ Finset.Icc (J + 1) N, |c k - 2 * A (dalQ q₀ δ k) * u (dalQ q₀ δ k)| ≤ E * δ ^ 6) →
          DaiFull a c (turnX u c0 q₀ δ) (fun k => langerAmp u A c0 (dalQ q₀ δ k)) J m N δ C Cmu ξ0 := by
  obtain ⟨r, c1, c2, gmin, gmax, Amin, Amax, LA, Lg, Lu, U, T, hrr0, hU, hsub, hζ, hAU, hgU, hrel, heik⟩ :=
    dal_turn_data hu h1 h2 hA hA0 hr0
  obtain ⟨δL, hδL, hδL1, HL⟩ := dao_lattice T.r_pos T.c1_pos T.c1_le T.zeta0 T.der
  obtain ⟨KA, KA', δ1, hKA, -, hδ1, hδ11, HA⟩ := dal_exact_defect hU hsub hζ hAU hgU hrel heik
  obtain ⟨KB, δ2, hKB, hδ2, hδ21, HB⟩ := dao_exact_defect_bi hU hsub hζ hAU hgU hrel heik
  have hc1 := T.c1_pos
  have hc2 : 0 < c2 := lt_of_lt_of_le hc1 T.c1_le
  have hr := T.r_pos
  have hAmin := T.Amin_pos
  have hgmin := T.gmin_pos
  have hgmax : 0 < gmax := lt_of_lt_of_le hgmin T.gmin_le
  have hπ := Real.pi_pos
  set K0 : ℝ := max KA KB with hK0
  set M : ℝ := c2 * r with hM
  have hM0 : 0 ≤ M := by positivity
  set Cn : ℝ := 6 / 5 * Real.exp (c2 * √(1 + M)) with hCn
  set K : ℝ := K0 + E * (450 * gmax * (2 * Cn + 1)) with hK
  have hKnn : 0 ≤ K := by
    have : 0 ≤ K0 := (hKA.le.trans (le_max_left _ _))
    have : 0 ≤ Cn := by positivity
    rw [hK]; positivity
  set ca : ℝ := Amin / 2 with hca
  have hcap : 0 < ca := by positivity
  set Cl : ℝ := 475 * gmax * K * (8 * √(2 + M) / c1) / (ca * gmin ^ 2 * c1 / (8 * Real.pi)) with hCl
  have hCl0 : 0 ≤ Cl := by
    have := Real.sqrt_nonneg (2 + M)
    rw [hCl]; positivity
  set Q : ℝ := 4 * Real.pi / (ca * gmin ^ 2 * c1) with hQ
  have hQp : 0 < Q := by rw [hQ]; positivity
  set Cd : ℝ := 7200 * gmax * Cl + Q with hCd
  set Cmu : ℝ := 50 * gmax * (Amax + E) * Q with hCmu
  have hAmax : 0 < Amax := lt_of_lt_of_le hAmin T.Amin_le
  have hCdp : 0 < Cd := by rw [hCd]; positivity
  set Aa : ℝ := Amax + E with hAa
  set Cc : ℝ := 2 * Amax * (1 + Lu * r) + E with hCc
  have hLu := T.Lu_nonneg
  have hAmin := T.Amin_pos
  have hCc0 : 0 ≤ Cc := by rw [hCc]; positivity
  have hAa0 : 0 ≤ Aa := by rw [hAa]; positivity
  have hCn0 : 0 < Cn := by rw [hCn]; positivity
  set C : ℝ := Cd + Cn * (Cc * Cd + Aa * Cd * Cn + K) / ca with hC
  have hCpos : 0 < C := by
    have : 0 ≤ Cn * (Cc * Cd + Aa * Cd * Cn + K) / ca := by positivity
    rw [hC]; linarith
  have hξ0 : 0 < 2 / 3 * (c1 * (r / 4)) ^ (3 / 2 : ℝ) := by positivity
  refine ⟨r, min δL (min δ1 (min δ2 (min (1 / (8 * c2)) (min (1 / (4 * (Cl + 1))) (min (Amin / (2 * (E + 1))) (r / 8)))))),
    C, Cmu, 2 / 3 * (c1 * (r / 4)) ^ (3 / 2 : ℝ), hr, hrr0, ?_, ?_, hCpos, by positivity, hξ0, ?_⟩
  · refine lt_min hδL (lt_min hδ1 (lt_min hδ2 (lt_min (by positivity) (lt_min (by positivity)
      (lt_min (by positivity) (by positivity))))))
  · exact (min_le_left _ _).trans hδL1
  intro δ q₀ hδ hδ0
  obtain ⟨hδL', hrest⟩ := le_min_iff.1 hδ0
  obtain ⟨hδ1', hrest⟩ := le_min_iff.1 hrest
  obtain ⟨hδ2', hrest⟩ := le_min_iff.1 hrest
  obtain ⟨hδc2, hrest⟩ := le_min_iff.1 hrest
  obtain ⟨hδCl, hrest⟩ := le_min_iff.1 hrest
  obtain ⟨hδE, hδr⟩ := le_min_iff.1 hrest
  have hδ11 : δ ≤ 1 := hδL'.trans hδL1
  obtain ⟨J, m, N, hJm, hmN, hwin, hqJ1, hqJ2, hqm1, hqm2, hqN, hqN1, hgap, hXabs, hX0, hX1, hXN⟩ := HL δ q₀ hδ hδL'
  have hδ3r : δ ^ 3 ≤ r / 8 := (dap_cube_le hδ hδ11).trans hδr
  have hJN : J < N := dap_JN hδ hδ3r hqJ2 hqN
  refine ⟨J, m, N, hJN, hJm, hmN, hwin, hqJ1, hqJ2, hqm1, hqm2, hqN, hqN1, ?_⟩
  intro a c ha hc
  have hc2δ : c2 * δ ≤ 1 / 8 := by
    rw [le_div_iff₀ (by positivity)] at hδc2
    nlinarith only [hδc2]
  have hEδ : E * δ ^ 6 ≤ Amin / 2 := dao_E_arith hE hδ hδ11 hδE
  have hsmall : Cl * δ ^ 3 ≤ 1 / 4 := dao_small_arith hCl0 hδ hδ11 hδCl
  have hmid := dal_mid (q₀ := q₀) (δ := δ) (c0 := c0) (r := r) hwin hδ
  have halow : ∀ k ∈ Icc (J + 1) (N + 1), ca ≤ a k :=
    dao_turn_alow (A := fun k => A (dalQ q₀ δ k - δ ^ 3 / 2)) (a := a)
      (fun k hk => (T.Ab _ (hmid k hk)).1) ha hEδ
  have hE6 : E * δ ^ 6 ≤ E := mul_le_of_le_one_right hE (pow_le_one₀ hδ.le hδ11)
  have haNk : ∀ k ∈ Icc (J + 1) (N + 1), a k ≤ Aa := by
    intro k hk
    have h5 := (abs_le.1 (ha k hk)).2
    have h6 := (T.Ab _ (hmid k hk)).2
    rw [hAa]
    linarith only [h5, h6, hE6]
  have haN : a (N + 1) ≤ Aa := haNk (N + 1) (by rw [mem_Icc]; omega)
  have haN' : a N ≤ Aa := haNk N (by rw [mem_Icc]; omega)
  have hcN : |c N| ≤ Cc :=
    dap_cN_bound (hwin N (by rw [mem_Icc]; omega)) (T.Ab _ (hwin N (by rw [mem_Icc]; omega))) hAmin
      (by simpa using (T.lip _ (hwin N (by rw [mem_Icc]; omega)) c0 ⟨by linarith, by linarith⟩).2.2) T.u0 hLu
      (hc N (by rw [mem_Icc]; omega)) hE6
  have hxi : 2 / 3 * (c1 * (r / 4)) ^ (3 / 2 : ℝ) / δ ^ 3 ≤ airyXi (turnX u c0 q₀ δ N) :=
    dal_xi_large (by positivity) hδ hXN
  have hK0n : 0 ≤ K0 := hKA.le.trans (le_max_left _ _)
  have hmemJ : ∀ k ∈ Icc (J + 1) N, k ∈ Icc J (N + 1) := fun k hk => by
    rw [mem_Icc] at hk ⊢; omega
  have hδ1'' : δ ≤ δ1 := hδ1'
  have hδ2'' : δ ≤ δ2 := hδ2'
  have hdA : ∀ k ∈ Icc (J + 1) N,
      |jac (fun j => A (dalQ q₀ δ j - δ ^ 3 / 2)) (fun j => 2 * A (dalQ q₀ δ j) * u (dalQ q₀ δ j))
        (daoPhi (fun k => langerAmp u A c0 (dalQ q₀ δ k)) (turnX u c0 q₀ δ)) k| ≤
      K0 * δ ^ 6 * airyWt (turnX u c0 q₀ δ k) := fun k hk => by
    have := (HA δ q₀ hδ hδ1'' k (hwin k (hmemJ k hk))).1
    exact this.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) (airyWt_pos _).le)
  have hdB : ∀ k ∈ Icc (J + 1) N,
      |jac (fun j => A (dalQ q₀ δ j - δ ^ 3 / 2)) (fun j => 2 * A (dalQ q₀ δ j) * u (dalQ q₀ δ j))
        (daoPsi (fun k => langerAmp u A c0 (dalQ q₀ δ k)) (turnX u c0 q₀ δ)) k| ≤
      K0 * δ ^ 6 * airyBiWt (turnX u c0 q₀ δ k) := fun k hk => by
    have := HB δ q₀ hδ hδ2'' k (hwin k (hmemJ k hk))
    exact this.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)) (airyBiWt_pos _).le)
  have hP : DaoPair (turnX u c0 q₀ δ) (fun k => langerAmp u A c0 (dalQ q₀ δ k)) a c J N δ c1 c2 gmin gmax ca K M :=
    dao_pair_of_defects (a0 := fun j => A (dalQ q₀ δ j - δ ^ 3 / 2))
      (c0 := fun j => 2 * A (dalQ q₀ δ j) * u (dalQ q₀ δ j)) (by omega) hδ hδ11 hc1 (by linarith only [hc2δ]) hM0 hc2.le
      hgap hXabs hgmin (fun k hk => T.gb _ (hwin k hk)) hcap halow hK0n hE ha hc hdA hdB
  exact dai_extend hP hJN hJm hmN hc2.le hM0 haN' hcN hCdp hxi
    (dao_conclusion hP (mem_Icc.2 ⟨hJm, hmN⟩) hX0 hX1 hc2δ haN hsmall)

/-- info: 'FormalResearch.Special.discrete_airy_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.discrete_airy_full

end FormalResearch.Special
