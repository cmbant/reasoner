module

public import FormalResearch.Special.DiscreteAiryLimit
public import FormalResearch.Special.DiscreteAiryOscMain
public import FormalResearch.Special.DiscreteAiryOscLattice

/-!
# The oscillatory side to the bulk at a simple turn: smooth-data form

Smooth data `u ∈ C³`, `A ∈ C²` at a simple turn `c₀` (`u(c₀) = 1`, `u'(c₀) > 0`, `A(c₀) > 0`) exactly as in
`discrete_airy_limit`, Langer coordinate `ζ`, amplitude `g`, lattice `q_k = q₀ + kδ³`, `X_k = ζ(q_k)/δ²`.  For every `E ≥ 0` there are
`r ≤ r₀`, `δ₀`, `C`, `Cmu > 0` such that for `δ ≤ δ₀` and every `q₀` there are indices `J ≤ m ≤ N` with
`q_J ∈ [c₀ - r, c₀ - r + δ³)` (**the whole oscillatory side `[c₀ - r, c₀]`, not just `X ≥ -A₀`**), `q_m ∈ [c₀, c₀ + δ³)`,
`q_N ≥ c₀ + r/4`, `q_{N+1} ≤ c₀ + r/2`, and for **every** coefficient sequences `a, c` with
`|a_k - A(q_k - δ³/2)| ≤ Eδ⁶`, `|c_k - 2A(q_k)u(q_k)| ≤ Eδ⁶` on the rows, `DaoConclusion` holds for
`X_k = ζ(q_k)/δ²`, `g_k = g(q_k)`: exact solutions `f`, `F₂` shadowing `g Ai(X)`, `g Bi(X)` to relative `O(δ³)` in the weights
`airyWt`, `airyBiWt` on all of `[J, N]`, and the two-sided decomposition of every solution with the bound on its `Bi`-coefficient.

* `dao_exact_defect_bi`: the `Bi` analogue of `dal_exact_defect` (`dao_bi_defect_lattice` + `langer_hrel` data).
* `dao_turn_conclusion`: the theorem.

**Claim class: proved.**  Constants are existential; `C δ³` is the *amplitude-adapted Olver form* on the oscillatory side
(`airyWt, airyBiWt ≍ (2+|X|)^{-1/4}` for `X ≤ 0`).  The accumulated phase error is `O(δ³)` relative, i.e. `O(h)`; the `h²` phase
coefficient is *not* resolved by this Airy parametrix.

**Hypotheses are on the whole macroscopic window.**  The coefficient closeness `|a_k - A(q_k - δ³/2)| ≤ Eδ⁶`,
`|c_k - 2A(q_k)u(q_k)| ≤ Eδ⁶` is required on every row `J+1..N+1` (`q ≥ c₀ - r`), not only on `X ≥ -A₀` as in `discrete_airy_limit`.
Mpmath check (scratch, not a Lean claim; model chain of `DiscreteAiryLimit`, `A = 1 + 0.3q + 0.2q²`, `u = cosh√(q + 0.4q²)`,
`c₀ = 0`, `h = δ³ = 10⁻³…10⁻⁶`, `f` by backward recursion from `q ≈ 0.12`, `F₂` from two sites at the turn, `q_J ≈ -0.5`, i.e.
`X` down to `≈ -4700`): `sup |f - g Ai|/(h airyWt)` and `sup |F₂ - g Bi|/(h airyBiWt)` stay `≈ 0.018` for every `h`
and every `X` sampled (also with `±3h²` perturbations of `a, c`).

**Not formalised here.**  The Darboux normalisation of `κ` and `κ ≠ 0`; explicit constants and uniformity in families of data; the
`h²` phase coefficient `ϖ`.  Continued in `DiscreteAiryPhys*`: the unified statement `discrete_airy_full` (the two recessive `f`'s are
identified, `dap_recessive_eq`, when normalised at the same `N`; the comparison of `F₂` and `Y` with the parametrix extends to the
site `N+1`, the decomposition `Y = κ f + μ F₂` holding on `[J, N+1]`) and the physical Hahn/Racah chains on this window
(`hahn_chain_airy_full`, `racah_chain_airy_full_*`; the required `Eδ⁶` closeness is `hr_perturb` of `DiscreteAiryLimitHahn`).
-/

@[expose] public section

open Finset FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- **Exact-coefficient defect for the `Bi` parametrix on the window** (`Bi` analogue of `dal_exact_defect`). -/
theorem dao_exact_defect_bi {U : Set ℝ} {ζ A g u : ℝ → ℝ} {c0 r : ℝ} (hU : IsOpen U)
    (hsub : Set.Icc (c0 - r) (c0 + r) ⊆ U) (hζ : ContDiffOn ℝ 3 ζ U) (hA : ContDiffOn ℝ 2 A U)
    (hg : ContDiffOn ℝ 2 g U)
    (hrel : ∀ q ∈ U, g q ^ 2 * A q * deriv ζ q * (2 * deriv langerCosh (ζ q * deriv ζ q ^ 2)) = 1)
    (heik : ∀ q ∈ U, langerCosh (ζ q * deriv ζ q ^ 2) = u q) :
    ∃ K δ1 : ℝ, 0 < K ∧ 0 < δ1 ∧ δ1 ≤ 1 ∧ ∀ δ q₀ : ℝ, 0 < δ → δ ≤ δ1 → ∀ k : ℤ,
      dalQ q₀ δ k ∈ Set.Icc (c0 - r) (c0 + r) →
        |jac (fun j => A (dalQ q₀ δ j - δ ^ 3 / 2)) (fun j => 2 * A (dalQ q₀ δ j) * u (dalQ q₀ δ j))
            (fun j => g (dalQ q₀ δ j) * airyBi (dalX ζ q₀ δ j)) k| ≤ K * δ ^ 6 * airyBiWt (dalX ζ q₀ δ k) := by
  have hJ : IsCompact (Set.Icc (c0 - r) (c0 + r)) := isCompact_Icc
  obtain ⟨K, h0, hK, hh0, H⟩ := dao_bi_defect_lattice hU hJ hsub hζ hA hg hrel
  refine ⟨K, min 1 h0, hK, lt_min one_pos hh0, min_le_left _ _, fun δ q₀ hδ hδ1 k hk => ?_⟩
  have hδ1' : δ ≤ 1 := hδ1.trans (min_le_left _ _)
  have h3 : 0 < δ ^ 3 := by positivity
  have h3δ : δ ^ 3 ≤ δ := by nlinarith [pow_pos hδ 2, pow_pos hδ 3]
  have hh0δ : δ ^ 3 ≤ h0 := h3δ.trans (hδ1.trans (min_le_right _ _))
  have hkU : q₀ + (k : ℝ) * δ ^ 3 ∈ U := hsub hk
  set c' : ℤ → ℝ := fun j => 2 * A (q₀ + (j : ℝ) * δ ^ 3) *
    langerCosh (ζ (q₀ + (j : ℝ) * δ ^ 3) * deriv ζ (q₀ + (j : ℝ) * δ ^ 3) ^ 2) with hc'
  have hcc : c' k = 2 * A (dalQ q₀ δ k) * u (dalQ q₀ δ k) := by
    simp only [hc', dalQ]; rw [heik _ hkU]
  have e6 : (δ ^ 3) ^ 2 = δ ^ 6 := by ring
  have key := H (δ ^ 3) q₀ (fun j => A (q₀ + (j : ℝ) * δ ^ 3 - δ ^ 3 / 2)) c'
    (fun j => g (dalQ q₀ δ j) * airyBi (dalX ζ q₀ δ j)) h3 hh0δ (fun j => rfl) (fun j => rfl) (fun j => rfl) k hk
  have hj : jac (fun j => A (dalQ q₀ δ j - δ ^ 3 / 2)) (fun j => 2 * A (dalQ q₀ δ j) * u (dalQ q₀ δ j))
      (fun j => g (dalQ q₀ δ j) * airyBi (dalX ζ q₀ δ j)) k =
      jac (fun j => A (q₀ + (j : ℝ) * δ ^ 3 - δ ^ 3 / 2)) c'
        (fun j => g (dalQ q₀ δ j) * airyBi (dalX ζ q₀ δ j)) k := by
    unfold jac
    rw [hcc]
    rfl
  rw [hj]
  have := key; rw [e6] at this; exact this

/-- info: 'FormalResearch.Special.dao_exact_defect_bi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.dao_exact_defect_bi


/-- Window and coefficient facts used by `dao_turn_conclusion` (sites `q_k - δ³/2`). -/
lemma dao_turn_alow {A a : ℤ → ℝ} {Amin E6 : ℝ} {J N : ℤ}
    (hAb : ∀ k ∈ Icc (J + 1) (N + 1), Amin ≤ A k)
    (ha : ∀ k ∈ Icc (J + 1) (N + 1), |a k - A k| ≤ E6) (hE : E6 ≤ Amin / 2) :
    ∀ k ∈ Icc (J + 1) (N + 1), Amin / 2 ≤ a k := by
  intro k hk
  have h1 := (abs_le.1 (ha k hk)).1
  linarith [hAb k hk]

lemma dao_small_arith {Cl δ : ℝ} (hCl : 0 ≤ Cl) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (h : δ ≤ 1 / (4 * (Cl + 1))) : Cl * δ ^ 3 ≤ 1 / 4 := by
  rw [le_div_iff₀ (by positivity)] at h
  have h3 : δ ^ 3 ≤ δ := by nlinarith [pow_pos hδ 2]
  nlinarith [mul_le_mul_of_nonneg_left h3 hCl]

lemma dao_E_arith {E δ Amin : ℝ} (hE : 0 ≤ E) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (h : δ ≤ Amin / (2 * (E + 1))) : E * δ ^ 6 ≤ Amin / 2 := by
  rw [le_div_iff₀ (by positivity)] at h
  have h6 : δ ^ 6 ≤ δ := by
    have : δ ^ 5 ≤ 1 := pow_le_one₀ hδ.le hδ1
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h6 hE]

/-- **The oscillatory side to the bulk at a simple turn** (see the module docstring). -/
theorem dao_turn_conclusion {u A : ℝ → ℝ} {c0 : ℝ} (hu : ContDiffAt ℝ 3 u c0) (h1 : u c0 = 1)
    (h2 : 0 < deriv u c0) (hA : ContDiffAt ℝ 2 A c0) (hA0 : 0 < A c0) {r0 : ℝ} (hr0 : 0 < r0)
    (E : ℝ) (hE : 0 ≤ E) :
    ∃ (r δ0 C Cmu : ℝ), 0 < r ∧ r ≤ r0 ∧ 0 < δ0 ∧ δ0 ≤ 1 ∧ 0 < C ∧ 0 < Cmu ∧
      ∀ δ q₀ : ℝ, 0 < δ → δ ≤ δ0 → ∃ J m N : ℤ, J ≤ m ∧ m ≤ N ∧
        (∀ k ∈ Finset.Icc J (N + 1), dalQ q₀ δ k ∈ Set.Icc (c0 - r) (c0 + r)) ∧
        c0 - r ≤ dalQ q₀ δ J ∧ dalQ q₀ δ J < c0 - r + δ ^ 3 ∧ c0 ≤ dalQ q₀ δ m ∧
        dalQ q₀ δ m < c0 + δ ^ 3 ∧ c0 + r / 4 ≤ dalQ q₀ δ N ∧ dalQ q₀ δ (N + 1) ≤ c0 + r / 2 ∧
        ∀ a c : ℤ → ℝ,
          (∀ k ∈ Finset.Icc (J + 1) (N + 1), |a k - A (dalQ q₀ δ k - δ ^ 3 / 2)| ≤ E * δ ^ 6) →
          (∀ k ∈ Finset.Icc (J + 1) N, |c k - 2 * A (dalQ q₀ δ k) * u (dalQ q₀ δ k)| ≤ E * δ ^ 6) →
          DaoConclusion a c (turnX u c0 q₀ δ) (fun k => langerAmp u A c0 (dalQ q₀ δ k)) J m N δ C Cmu := by
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
  set C : ℝ := 7200 * gmax * Cl + Q with hC
  set Cmu : ℝ := 50 * gmax * (Amax + E) * Q with hCmu
  have hAmax : 0 < Amax := lt_of_lt_of_le hAmin T.Amin_le
  refine ⟨r, min δL (min δ1 (min δ2 (min (1 / (8 * c2)) (min (1 / (4 * (Cl + 1))) (Amin / (2 * (E + 1))))))),
    C, Cmu, hr, hrr0, ?_, ?_, by positivity, by positivity, ?_⟩
  · refine lt_min hδL (lt_min hδ1 (lt_min hδ2 (lt_min (by positivity) (lt_min (by positivity) (by positivity)))))
  · exact (min_le_left _ _).trans hδL1
  intro δ q₀ hδ hδ0
  have hδL' : δ ≤ δL := hδ0.trans (min_le_left _ _)
  have hδ1' : δ ≤ δ1 := hδ0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδ2' : δ ≤ δ2 := hδ0.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδc2 : δ ≤ 1 / (8 * c2) := hδ0.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))))
  have hδCl : δ ≤ 1 / (4 * (Cl + 1)) := hδ0.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have hδE : δ ≤ Amin / (2 * (E + 1)) := hδ0.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
  have hδ11 : δ ≤ 1 := hδL'.trans hδL1
  obtain ⟨J, m, N, hJm, hmN, hwin, hqJ1, hqJ2, hqm1, hqm2, hqN, hqN1, hgap, hXabs, hX0, hX1, hXN⟩ := HL δ q₀ hδ hδL'
  refine ⟨J, m, N, hJm, hmN, hwin, hqJ1, hqJ2, hqm1, hqm2, hqN, hqN1, ?_⟩
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
  have haN : a (N + 1) ≤ Amax + E := by
    have hk : N + 1 ∈ Finset.Icc (J + 1) (N + 1) := by rw [Finset.mem_Icc]; omega
    have h5 := (abs_le.1 (ha (N + 1) hk)).2
    have h6 := (T.Ab _ (hmid (N + 1) hk)).2
    have h7 : E * δ ^ 6 ≤ E := mul_le_of_le_one_right hE (pow_le_one₀ hδ.le hδ11)
    linarith only [h5, h6, h7]
  have hK0n : 0 ≤ K0 := hKA.le.trans (le_max_left _ _)
  have hmemJ : ∀ k ∈ Icc (J + 1) N, k ∈ Icc J (N + 1) := fun k hk => by
    rw [mem_Icc] at hk ⊢; omega
  have hdA : ∀ k ∈ Icc (J + 1) N,
      |jac (fun j => A (dalQ q₀ δ j - δ ^ 3 / 2)) (fun j => 2 * A (dalQ q₀ δ j) * u (dalQ q₀ δ j))
        (daoPhi (fun k => langerAmp u A c0 (dalQ q₀ δ k)) (turnX u c0 q₀ δ)) k| ≤
      K0 * δ ^ 6 * airyWt (turnX u c0 q₀ δ k) := fun k hk => by
    have := (HA δ q₀ hδ hδ1' k (hwin k (hmemJ k hk))).1
    exact this.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) (airyWt_pos _).le)
  have hdB : ∀ k ∈ Icc (J + 1) N,
      |jac (fun j => A (dalQ q₀ δ j - δ ^ 3 / 2)) (fun j => 2 * A (dalQ q₀ δ j) * u (dalQ q₀ δ j))
        (daoPsi (fun k => langerAmp u A c0 (dalQ q₀ δ k)) (turnX u c0 q₀ δ)) k| ≤
      K0 * δ ^ 6 * airyBiWt (turnX u c0 q₀ δ k) := fun k hk => by
    have := HB δ q₀ hδ hδ2' k (hwin k (hmemJ k hk))
    exact this.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)) (airyBiWt_pos _).le)
  have hP : DaoPair (turnX u c0 q₀ δ) (fun k => langerAmp u A c0 (dalQ q₀ δ k)) a c J N δ c1 c2 gmin gmax ca K M :=
    dao_pair_of_defects (a0 := fun j => A (dalQ q₀ δ j - δ ^ 3 / 2))
      (c0 := fun j => 2 * A (dalQ q₀ δ j) * u (dalQ q₀ δ j)) (by omega) hδ hδ11 hc1 (by linarith only [hc2δ]) hM0 hc2.le
      hgap hXabs hgmin (fun k hk => T.gb _ (hwin k hk)) hcap halow hK0n hE ha hc hdA hdB
  exact dao_conclusion hP (mem_Icc.2 ⟨hJm, hmN⟩) hX0 hX1 hc2δ haN hsmall

/-- info: 'FormalResearch.Special.dao_turn_conclusion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.dao_turn_conclusion

end FormalResearch.Special
