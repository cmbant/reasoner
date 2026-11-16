module

public import FormalResearch.Racah.P2AnalyticLeading
public import FormalResearch.Racah.P2HahnChambers
public import FormalResearch.Racah.P2AnalyticL2Singular

/-!
# The `3j` carrier is the even Hahn deformation (Weyl P2, `eq:carrierHahnRacah`, `lem:evendeformation`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `lem:evendeformation` and `lem:sqrtfreecarrier`
(`eq:carrierHahnRacah`: `P̃_L = k_{3j} q_{L-L₀}(ς; N⁻²)`).

The paper first shows (difference-equation argument) that the Hahn polynomial `Q_d(u;α,β,D)` is, in
`ς = (u + (α+1)/2)/N`, an even deformation `q_d(ς; h²)` of the monic Jacobi polynomial, and then
identifies `P̃_L` with it by the proportionality on `D+1` lattice points.  The Lean route reverses the
order: `P̃_L` is defined by the square-root-free recurrence (`ptilde3Poly`), where polynomiality in
`h² = t` is immediate, and the identification with the Hahn polynomial is proved on the physical
lattice from the two exact forms of the kernel (`Phi3j_carrier`, `Phi3j_hahn_all_chambers`), then
lifted to an identity of polynomials in `ς` (`ptilde3_eq_hahn`).  Hence the evenness of the Hahn
deformation is a corollary and the difference-equation computation of the paper is not needed.

* `hahnPoly`, `eval_hahnPoly`: the Hahn polynomial as a real polynomial, `Q_n(u) = hahnQ α β D n u`;
* `ptilde3_lattice_hahn`: on the lattice `ς_u`, `P̃_{L₀+k}(ς_u; N⁻²) = c · Q_k(u)` (all four chambers);
* `ptilde3_eq_hahn`: the same as an identity of polynomials in `ς` (`D+1 > k` points);
* `evenHahn3`, `lem_evendeformation3`: `q_d := P̃/k_{3j}` is monic of degree `d`, polynomial in `t`,
  equals the monic Jacobi polynomial at `t = 0`, and is a nonzero multiple of the Hahn polynomial at
  every admissible `N`.

The estimate `sup |q_d - P̂_d| ≤ C N⁻²` is `evenHahn3_bound` (`P2AnalyticEvenDegree3`); the Racah analogue
`eq:carrierRacah6j`, `lem:evendeformation6j` is `P2AnalyticCarrierRacah` (canonical chamber) and
`P2AnalyticCarrierRacahAll`, `P2AnalyticEvenDegree6` (all chambers, degree bound and estimate).
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner Polynomial

/-- The Hahn polynomial `Q_n(u; α, β, D)` as a real polynomial in `u` (so that
`eval (u : ℝ) (hahnPoly α β D n) = hahnQ α β D n u`). -/
noncomputable def hahnPoly (α β D n : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1),
    C ((ascPochhammer ℝ k).eval (-(n : ℝ)) * (ascPochhammer ℝ k).eval ((n : ℝ) + α + β + 1) /
      ((ascPochhammer ℝ k).eval ((α : ℝ) + 1) * (ascPochhammer ℝ k).eval (-(D : ℝ)) *
        (k.factorial : ℝ))) * (ascPochhammer ℝ k).comp (-X)

theorem eval_hahnPoly (α β D n u : ℕ) : (hahnPoly α β D n).eval (u : ℝ) = hahnQ α β D n u := by
  unfold hahnPoly hahnQ
  rw [eval_finsetSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [eval_mul, eval_C, eval_comp, eval_neg, eval_X]
  ring

theorem natDegree_hahnPoly_le (α β D n : ℕ) : (hahnPoly α β D n).natDegree ≤ n := by
  unfold hahnPoly
  refine natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [natDegree_comp, ascPochhammer_natDegree]
  simp [hkn]

lemma abs_sub_add_abs_add (M σ : ℚ) : |M - σ| + |M + σ| = 2 * max |M| |σ| := by
  rcases abs_cases σ with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;> rcases abs_cases M with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;>
    rcases abs_cases (M - σ) with ⟨h3, h3'⟩ | ⟨h3, h3'⟩ <;>
    rcases abs_cases (M + σ) with ⟨h4, h4'⟩ | ⟨h4, h4'⟩ <;>
    rw [h3, h4, h1, h2] <;> simp only [max_def] <;> split_ifs <;> linarith

/-- The physical lattice point of Hahn index `u`: `μ_u = (N-1-α-2u)/2`, `0 ≤ u ≤ D`. -/
lemma lat4_hahn {M σ N : ℚ} (hA : SpecAdm M σ N) (hN : 0 < N) {D α : ℕ}
    (hD : N - max |M| |σ| - 1 = D) (hα : |M - σ| = α) {u : ℕ} (hu : u ≤ D) :
    Lat4 M σ N ((N - 1 - α - 2 * u) / 2) := by
  have hK : (((D + 1 : ℕ)) : ℚ) = N - max |M| |σ| := by push_cast; linarith
  have h := lat_adm hA hN hK (n := D - u) (by omega)
  have hμ : (N - 1 - α - 2 * (u : ℚ)) / 2 = N * xLat M σ N (D - u) / 2 := by
    rw [mu_lat M σ N hN.ne']
    have := abs_sub_add_abs_add M σ
    have hc : (((D - u : ℕ)) : ℚ) = D - u := by push_cast [Nat.cast_sub hu]; ring
    rw [hc, ← hα]
    linarith
  rw [hμ]
  exact h

/-- Cancelling the common edge factor between the carrier form and the Hahn form of the kernel. -/
lemma carrier_ratio {Φk Φ0 Aval Ck C0 Xk seed ak a0 sw Qk : ℝ} (hC0 : 0 < C0) (hCk : 0 < Ck)
    (hsw : 0 < sw) (ha0 : a0 ≠ 0) (hseed : seed ≠ 0)
    (e1k : Φk = Aval / Real.sqrt Ck * Xk) (e10 : Φ0 = Aval / Real.sqrt C0 * seed)
    (e2k : Φk = ak * sw * Qk) (e20 : Φ0 = a0 * sw) :
    Xk = (ak * Real.sqrt Ck * seed / (a0 * Real.sqrt C0)) * Qk := by
  have hsC0 : 0 < Real.sqrt C0 := Real.sqrt_pos.mpr hC0
  have hsCk : 0 < Real.sqrt Ck := Real.sqrt_pos.mpr hCk
  have hΦ0 : Φ0 ≠ 0 := by rw [e20]; exact mul_ne_zero ha0 hsw.ne'
  have hA : Aval = Φ0 * Real.sqrt C0 / seed := by
    rw [e10]; field_simp
  have hAne : Aval ≠ 0 := by
    rw [hA]; exact div_ne_zero (mul_ne_zero hΦ0 hsC0.ne') hseed
  have hX : Xk = Φk * Real.sqrt Ck / Aval := by
    rw [e1k]; field_simp
  rw [hX, e2k, hA, e20]
  field_simp

lemma seed3_ne_zero (M σ : ℚ) : seed3 M σ ≠ 0 := by
  unfold seed3
  refine mul_ne_zero (by split_ifs <;> simp) (Real.sqrt_pos.mpr ?_).ne'
  positivity

/-- Positivity of the central product `Ct (2L+1) 1 (1/N²)` at every rank `L ≤ N - 1`. -/
lemma Ct_pos_rank (M σ N : ℚ) (hN : 0 < N) (α β D k : ℕ) (hα : |M - σ| = α) (hβ : |M + σ| = β)
    (hD : N - max |M| |σ| - 1 = D) (hk : k ≤ D) :
    0 < Ct (α + β + 2 * k + 1) 1 (1 / (N : ℝ) ^ 2) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  refine Ct_pos _ one_pos (by positivity) ?_
  have h1 := abs_sub_add_abs_add M σ
  have h2 : (α : ℚ) + β + 2 * k + 1 < 2 * N := by
    rw [← hα, ← hβ]
    have : (k : ℚ) ≤ D := by exact_mod_cast hk
    linarith
  have h3 : ((α : ℝ) + β + 2 * k + 1) < 2 * N := by exact_mod_cast h2
  have h4 : (0 : ℝ) ≤ (α : ℝ) + β + 2 * k + 1 := by positivity
  push_cast
  rw [mul_one_div, div_lt_iff₀ (by positivity)]
  nlinarith

/-- **Lattice form of `eq:carrierHahnRacah`** (`3j`, every chamber): for each admissible `N`, the
carrier `P̃_{L₀+k}(ς; N⁻²)` at the physical points `ς_u = (u + (α+1)/2)/N` is a `u`-independent
multiple of the Hahn polynomial `Q_k(u; α, β, D)`, `D = N - L₀ - 1`, `0 ≤ u ≤ D`. -/
theorem ptilde3_lattice_hahn (M σ N : ℚ) (α β D k : ℕ) (hA : SpecAdm M σ N) (hN : 0 < N)
    (hα : |M - σ| = α) (hβ : |M + σ| = β) (hD : N - max |M| |σ| - 1 = D) (hk : k ≤ D) :
    ∃ c : ℝ, ∀ u : ℕ, u ≤ D →
      ptilde3 M σ k (((u : ℝ) + ((α : ℝ) + 1) / 2) / N) (1 / (N : ℝ) ^ 2) = c * hahnQ α β D k u := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 := abs_sub_add_abs_add M σ
  have hL0 : (0 : ℚ) ≤ max |M| |σ| := le_trans (abs_nonneg M) (le_max_left _ _)
  have hCk := Ct_pos_rank M σ N hN α β D k hα hβ hD hk
  have hC0 := Ct_pos_rank M σ N hN α β D 0 hα hβ hD (Nat.zero_le _)
  have hε : ∀ x : ℝ, x ≠ 0 → (if σ ≤ M then (-1 : ℝ) ^ α else 1) * x ≠ 0 := by
    intro x hx; refine mul_ne_zero ?_ hx; split_ifs <;> simp
  set ε : ℝ := if σ ≤ M then (-1 : ℝ) ^ α else 1 with hεdef
  have hεne : ε ≠ 0 := by rw [hεdef]; split_ifs <;> simp
  have hh0 := hahnNorm_pos α β D 0
  have hhk := hahnNorm_pos α β D k
  set ak : ℝ := ε * Real.sqrt ((N : ℝ) / (2 * (((max |M| |σ| : ℚ) : ℝ) + k) + 1)) /
    Real.sqrt (hahnNorm α β D k) with hak
  set a0 : ℝ := ε * Real.sqrt ((N : ℝ) / (2 * (((max |M| |σ| : ℚ) : ℝ) + (0 : ℕ)) + 1)) /
    Real.sqrt (hahnNorm α β D 0) with ha0
  have hmax0 : (0 : ℝ) ≤ ((max |M| |σ| : ℚ) : ℝ) := by exact_mod_cast hL0
  have ha0ne : a0 ≠ 0 := by
    rw [ha0]
    refine div_ne_zero (mul_ne_zero hεne (Real.sqrt_pos.mpr (by positivity)).ne') ?_
    exact (Real.sqrt_pos.mpr hh0).ne'
  refine ⟨ak * Real.sqrt (Ct (α + β + 2 * k + 1) 1 (1 / (N : ℝ) ^ 2)) * seed3 M σ /
    (a0 * Real.sqrt (Ct (α + β + 2 * 0 + 1) 1 (1 / (N : ℝ) ^ 2))), fun u hu => ?_⟩
  -- the lattice point
  set μ : ℚ := (N - 1 - α - 2 * u) / 2 with hμ
  have hlat : Lat4 M σ N μ := lat4_hahn hA hN hD hα hu
  have hμu : (N - 1 - |M - σ| - 2 * μ) / 2 = u := by rw [hμ, hα]; ring
  have hτ : (1 - 2 * (μ : ℝ) / N) / 2 = ((u : ℝ) + ((α : ℝ) + 1) / 2) / N := by
    have : (μ : ℝ) = (N - 1 - α - 2 * u) / 2 := by rw [hμ]; push_cast; ring
    rw [this]; field_simp; ring
  have hw : (0 : ℝ) < hahnW α β D u := by
    unfold hahnW
    exact_mod_cast Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega))
  have hkc : max |M| |σ| + k + 1 ≤ N := by
    have : (k : ℚ) ≤ D := by exact_mod_cast hk
    linarith
  have hk0 : max |M| |σ| + ((0 : ℕ) : ℚ) + 1 ≤ N := by
    have : ((0 : ℕ) : ℚ) ≤ D := by exact_mod_cast Nat.zero_le D
    linarith
  have c1 := Phi3j_carrier M σ N μ α β hα hβ hA hN hlat k hkc
  have c0 := Phi3j_carrier M σ N μ α β hα hβ hA hN hlat 0 hk0
  have h1' := Phi3j_hahn_all_chambers M σ N μ α β D k u hα hβ hD hk hμu hu
  have h0' := Phi3j_hahn_all_chambers M σ N μ α β D 0 u hα hβ hD (Nat.zero_le _) hμu hu
  rw [hτ] at c1 c0
  rw [ptilde3_zero] at c0
  have e2k : Phi3j (max |M| |σ| + k) M σ N μ = ak * Real.sqrt (hahnW α β D u : ℝ) * hahnQ α β D k u := by
    rw [h1', Real.sqrt_div hw.le, hak]; ring
  have e20 : Phi3j (max |M| |σ| + ((0 : ℕ) : ℚ)) M σ N μ = a0 * Real.sqrt (hahnW α β D u : ℝ) := by
    rw [h0', Real.sqrt_div hw.le, ha0, hahnQ_zero]; ring
  have := carrier_ratio (Φk := Phi3j (max |M| |σ| + k) M σ N μ)
    (Φ0 := Phi3j (max |M| |σ| + ((0 : ℕ) : ℚ)) M σ N μ) hC0 hCk (Real.sqrt_pos.mpr hw) ha0ne
    (seed3_ne_zero M σ) c1 c0 e2k e20
  rw [this]

/-- The even Hahn deformation `Q̃_k(ς; t) = P̃_{L₀+k}(ς; t) / k_{3j}` as an element of `ℝ[t][ς]`: monic of
degree `k` in `ς` with coefficients polynomial in `t = h²`. -/
noncomputable def evenHahn3 (M σ : ℚ) (k : ℕ) : Polynomial (Polynomial ℝ) :=
  C (C (lead3 M σ k)⁻¹) * ptilde3Poly M σ k

/-- **`eq:carrierHahnRacah`** (`3j`, every chamber), as an identity of polynomials in `ς`:
for every admissible `N` and rank `k ≤ D = N - L₀ - 1`,
`P̃_{L₀+k}(ς; N⁻²) = c · Q_k(Nς - (α+1)/2; α, β, D)` with a nonzero constant `c` independent of `ς`. -/
theorem ptilde3_eq_hahn (M σ N : ℚ) (α β D k : ℕ) (hA : SpecAdm M σ N) (hN : 0 < N)
    (hα : |M - σ| = α) (hβ : |M + σ| = β) (hD : N - max |M| |σ| - 1 = D) (hk : k ≤ D) :
    ∃ c : ℝ, c ≠ 0 ∧
      (ptilde3Poly M σ k).map (Polynomial.evalRingHom (1 / (N : ℝ) ^ 2)) =
        C c * (hahnPoly α β D k).comp (C (N : ℝ) * X - C (((α : ℝ) + 1) / 2)) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨c, hc⟩ := ptilde3_lattice_hahn M σ N α β D k hA hN hα hβ hD hk
  set P1 := (ptilde3Poly M σ k).map (Polynomial.evalRingHom (1 / (N : ℝ) ^ 2)) with hP1
  set P2 := C c * (hahnPoly α β D k).comp (C (N : ℝ) * X - C (((α : ℝ) + 1) / 2)) with hP2
  set S : Finset ℝ := (Finset.range (D + 1)).image
    (fun u : ℕ => ((u : ℝ) + ((α : ℝ) + 1) / 2) / N) with hS
  have hinj : Function.Injective (fun u : ℕ => ((u : ℝ) + ((α : ℝ) + 1) / 2) / N) := by
    intro u v h
    have := (div_left_inj' hN'.ne').mp h
    exact_mod_cast (add_right_cancel this)
  have hcard : S.card = D + 1 := by
    rw [hS, Finset.card_image_of_injective _ hinj, Finset.card_range]
  have hd1 : P1.natDegree ≤ k :=
    (natDegree_map_le).trans (natDegree_ptilde3Poly_le M σ k)
  have hd2 : P2.natDegree ≤ k := by
    refine (natDegree_C_mul_le _ _).trans ?_
    refine (natDegree_comp_le).trans ?_
    have h3 : (C (N : ℝ) * X - C (((α : ℝ) + 1) / 2)).natDegree ≤ 1 := by
      refine (natDegree_sub_le _ _).trans (max_le ?_ (by simp))
      exact (natDegree_C_mul_le _ _).trans (by simp)
    calc _ ≤ (hahnPoly α β D k).natDegree * 1 := Nat.mul_le_mul_left _ h3
      _ ≤ k := by simpa using natDegree_hahnPoly_le α β D k
  have hlt : ∀ P : ℝ[X], P.natDegree ≤ k → P.degree < S.card := by
    intro P hP
    refine (degree_le_of_natDegree_le hP).trans_lt ?_
    rw [hcard]; exact_mod_cast Nat.lt_succ_of_le hk
  have heq : P1 = P2 := by
    refine eq_of_degrees_lt_of_eval_finset_eq S (hlt P1 hd1) (hlt P2 hd2) ?_
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    have hu' : u ≤ D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hu)
    rw [hP2, eval_mul, eval_C, eval_comp, eval_sub, eval_mul, eval_C, eval_C, eval_X]
    have : (N : ℝ) * (((u : ℝ) + ((α : ℝ) + 1) / 2) / N) - ((α : ℝ) + 1) / 2 = u := by
      field_simp; ring
    rw [this, eval_hahnPoly, ← hc u hu']
    rw [hP1]
    rw [ptilde3_eq_evalP]
    rfl
  refine ⟨c, ?_, heq⟩
  intro hc0
  have h0 : P2 = 0 := by rw [hP2, hc0]; simp
  have hcoef : P1.coeff k = lead3 M σ k := by
    rw [hP1, coeff_map, ptilde3Poly_coeff_top]; simp
  have hlead : lead3 M σ k ≠ 0 := by
    rw [lead3_eq_jacobi M σ α β hα hβ k]
    refine mul_ne_zero (mul_ne_zero ?_ ?_) (jacobi_lead_ne_zero α β k)
    · unfold signE3; split_ifs <;> simp
    · unfold wignerJacobiNorm; positivity
  rw [← heq] at h0
  rw [h0] at hcoef
  exact hlead (by simpa using hcoef.symm)

/-- **`lem:evendeformation` (`3j`, Lean form), every chamber.**  Let `Q̃_k(ς; t) = evenHahn3 M σ k` be the
carrier `P̃_{L₀+k}` divided by its `t`-independent leading coefficient `k_{3j}`.  Then

* `Q̃_k` is monic of degree `k` in `ς` and its coefficients are polynomials in `t = h²`
  (it is an element of `ℝ[t][ς]`);
* at `t = 0` it is the monic Jacobi polynomial `P̂_k^{(|M-σ|,|M+σ|)}(ς)` (`eq:WignerJacobiMonic`);
* for every admissible `N` and `k ≤ D = N - L₀ - 1`, `Q̃_k(ς; N⁻²)` is a nonzero `ς`-independent
  multiple of the Hahn polynomial `Q_k(Nς - (α+1)/2; α, β, D)` (the identification of
  `eq:carrierHahnRacah`).

The statement is the paper's lemma read through the carrier: the even deformation of the Jacobi
polynomial is defined by the recurrence `eq:3jrankpoly` (where the polynomial dependence on `h²` is
immediate), and its identification with the Hahn polynomial is `ptilde3_eq_hahn`.  The paper's
estimate `sup |q_d - P̂_d| ≤ C N⁻²` is `evenHahn3_bound` (`P2AnalyticEvenDegree3`). -/
theorem lem_evendeformation3 (M σ : ℚ) (α β k : ℕ) (hα : |M - σ| = α) (hβ : |M + σ| = β) :
    (evenHahn3 M σ k).natDegree ≤ k ∧ (evenHahn3 M σ k).coeff k = 1 ∧
      (evenHahn3 M σ k).map (Polynomial.evalRingHom 0) = jacobiMonicTau α β k ∧
      ∀ (N : ℚ) (D : ℕ), SpecAdm M σ N → 0 < N → N - max |M| |σ| - 1 = D → k ≤ D →
        ∃ κ : ℝ, κ ≠ 0 ∧
          (evenHahn3 M σ k).map (Polynomial.evalRingHom (1 / (N : ℝ) ^ 2)) =
            C κ * (hahnPoly α β D k).comp (C (N : ℝ) * X - C (((α : ℝ) + 1) / 2)) := by
  have hlead : lead3 M σ k ≠ 0 := by
    rw [lead3_eq_jacobi M σ α β hα hβ k]
    refine mul_ne_zero (mul_ne_zero ?_ ?_) (jacobi_lead_ne_zero α β k)
    · unfold signE3; split_ifs <;> simp
    · unfold wignerJacobiNorm; positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold evenHahn3
    exact (natDegree_C_mul_le _ _).trans (natDegree_ptilde3Poly_le M σ k)
  · unfold evenHahn3
    rw [coeff_C_mul, ptilde3Poly_coeff_top, ← C_mul, inv_mul_cancel₀ hlead]; simp
  · unfold evenHahn3
    rw [Polynomial.map_mul, Polynomial.map_C]
    have e : (ptilde3Poly M σ k).map (Polynomial.evalRingHom 0) = ptilde3Zero M σ k := rfl
    rw [e, ptilde3Zero_eq_lead_mul_monic M σ α β hα hβ k]
    simp only [coe_evalRingHom, eval_C]
    rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hlead, C_1, one_mul]
  · intro N D hA hN hD hk
    obtain ⟨c, hc0, hc⟩ := ptilde3_eq_hahn M σ N α β D k hA hN hα hβ hD hk
    refine ⟨(lead3 M σ k)⁻¹ * c, mul_ne_zero (inv_ne_zero hlead) hc0, ?_⟩
    unfold evenHahn3
    rw [Polynomial.map_mul, Polynomial.map_C, hc, ← mul_assoc, ← C_mul]
    simp

end FormalResearch.Racah

/-- info: 'FormalResearch.Racah.ptilde3_lattice_hahn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.ptilde3_lattice_hahn

/-- info: 'FormalResearch.Racah.ptilde3_eq_hahn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.ptilde3_eq_hahn

/-- info: 'FormalResearch.Racah.lem_evendeformation3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.lem_evendeformation3
