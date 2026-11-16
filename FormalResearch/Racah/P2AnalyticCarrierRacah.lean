module

public import FormalResearch.Racah.P2AnalyticCarrier6jInduction
public import FormalResearch.Racah.P2AnalyticCarrier6jPoly
public import FormalResearch.Racah.P2RacahPolyIdent
public import FormalResearch.Racah.P2AnalyticLeading

/-!
# The `6j` carrier is the even Racah deformation (Weyl P2, `eq:carrierRacah6j`, `lem:evendeformation6j`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `lem:evendeformation6j` and
`lem:sqrtfreecarrier6j` (`eq:carrierRacah6j`: `P̃_f = k_{6j} q_{f-m}(ς; S⁻¹, δ)`), canonical sector
`m ≥ |n|`.  As for `3j` (`P2AnalyticCarrierHahn`), Lean reverses the order of the paper: `P̃_f` is defined by
the recurrence (`ptPoly`, polynomial in `u = A⁻²`, `v = B⁻²`, `w = (AB)⁻¹`), its values on the physical
lattice are compared with the physical Racah polynomial through `Phi6_carrier_canonical`,
`Phi6_seed_carrier` and `ppR_eq_racahPoly` (the common edge factor cancels), and the identification is
lifted to polynomials in `ς`: the Racah polynomial is written as a polynomial in
`λ = y(y+2c_min+1) = 4ABς + (A-B)² - (c_min+½)²` (`racahLam`, `eval_racahLam`).  The evenness of the
Racah deformation is then a corollary.

* `ptilde6_lattice_racah`: on `c = c_min + y`, `P̃_{m+r}(ς_y) = c · Q^R_r(y)`;
* `ptilde6_eq_racah`: the same as an identity of polynomials in `ς`;
* `evenRacah6`, `lem_evendeformation6`: `q_d = P̃/k_{6j}` is monic of degree `d`, polynomial in
  `(A⁻², B⁻², (AB)⁻¹)`, the monic Jacobi `P̂_d^{(m-n,m+n)}` at zero scale, and a nonzero multiple of the
  Racah polynomial on every `RacahSystem`.

Not formalised: the other chambers (`eq:carrierRacah6j` is a canonical-chamber statement in the paper
as well), the degree bound of the coefficients in `ε²` and `δ²` and `eq:evendeformationbound`.
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner FormalResearch.Racah.SixJ FormalResearch.Racah.RacahPoly Polynomial

/-- The terminating Racah polynomial as a polynomial in `λ = x(x+γ+δ+1)`. -/
noncomputable def racahLam (α β γ δ : ℝ) (n : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1), C (racahCoef α β γ δ n k) *
    ∏ j ∈ Finset.range k, (C ((j : ℝ) * ((j : ℝ) + (γ + δ + 1))) - X)

theorem racahPhi_eq_prod (γ δ : ℝ) (k : ℕ) (x : ℝ) :
    racahPhi γ δ k x = ∏ j ∈ Finset.range k,
      (((j : ℝ) * ((j : ℝ) + (γ + δ + 1))) - x * (x + (γ + δ + 1))) := by
  unfold racahPhi rf
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  ring

theorem eval_racahLam (α β γ δ : ℝ) (n : ℕ) (x : ℝ) :
    (racahLam α β γ δ n).eval (x * (x + (γ + δ + 1))) = racahPoly α β γ δ n x := by
  unfold racahLam racahPoly
  rw [eval_finsetSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [eval_mul, eval_C, eval_prod, racahPhi_eq_prod]
  simp [eval_sub]

theorem natDegree_racahLam_le (α β γ δ : ℝ) (n : ℕ) : (racahLam α β γ δ n).natDegree ≤ n := by
  unfold racahLam
  refine natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  refine (natDegree_C_mul_le _ _).trans ?_
  refine (natDegree_prod_le _ _).trans ?_
  have h1 : ∀ j ∈ Finset.range k,
      (C ((j : ℝ) * ((j : ℝ) + (γ + δ + 1))) - X : ℝ[X]).natDegree ≤ 1 := fun j _ =>
    (natDegree_sub_le _ _).trans (max_le (by rw [natDegree_C]; exact Nat.zero_le _)
      (by rw [natDegree_X]))
  calc _ ≤ ∑ j ∈ Finset.range k, 1 := Finset.sum_le_sum h1
    _ = k := by simp
    _ ≤ n := hkn

/-- **Lattice form of `eq:carrierRacah6j`** (canonical sector `m ≥ |n|`): on the physical lattice
`c = c_min + y`, `0 ≤ y ≤ D`, the carrier `P̃_{m+r}(ς_y)` is a `y`-independent multiple of the physical
Racah polynomial `Q^R_r(y)` (`eq:physicalRacah4F3`), `ς_y = (1 - cosA A B C_y)/2`. -/
theorem ptilde6_lattice_racah {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D) (hcan : |n| ≤ m)
    (r : ℕ) (hr : r ≤ D) :
    ∃ c : ℝ, ∀ y : ℕ, y ≤ D →
      ptilde6 m n ((1 - cosA (wA a n) (wB b m) (wC (cMin a b m n + y))) / 2)
        (1 / wA a n ^ 2) (1 / wB b m ^ 2) (1 / (wA a n * wB b m)) r =
          c * physQ a b m n D r y := by
  have hm0 := mem_rank h hcan 0 (Nat.zero_le _)
  simp only [Nat.cast_zero, add_zero] at hm0
  have hf := mem_rank h hcan r hr
  obtain ⟨hA, hB, -, -, -⟩ := admissible_facts hf.1 hf.2
  obtain ⟨hAb, hBb⟩ := adm_bounds hf.1 hf.2
  obtain ⟨hAm, hBm⟩ := adm_bounds hm0.1 hm0.2
  have hPf : 0 < piSix (m + r) (wA a n) (wB b m) :=
    piSix_pos _ _ _ hA hB (by linarith) (by linarith)
  have hPm : 0 < piSix m (wA a n) (wB b m) := piSix_pos _ _ _ hA hB (by linarith) (by linarith)
  set s : ℝ := Real.sqrt ((Nat.choose ⌊2 * m⌋₊ ⌊m + n⌋₊ : ℕ) : ℝ) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  refine ⟨ppR a b m n r 0 * Real.sqrt (piSix (m + r) (wA a n) (wB b m)) *
    (Real.sqrt (piSix m (wA a n) (wB b m)))⁻¹ * s, fun y hy => ?_⟩
  have hc := mem_lattice h y hy
  have cf := Phi6_carrier_canonical a b _ (m + r) m n hcan hf.1 hf.2 hc.1 hc.2 r rfl
  have cm := Phi6_seed_carrier a b _ m n hm0.1 hm0.2 hc.1 hc.2
  have hpos := Phi6_seed_pos a b _ m n hm0.1 hm0.2 hc.1 hc.2
  have hrat := ppR_eq_racahPoly h hcan r y hr hy
  have hpp : ppR a b m n r y * Phi6 a b (cMin a b m n + y) m m n =
      Phi6 a b (cMin a b m n + y) (m + r) m n := by
    unfold ppR; field_simp
  set E := edgeFac m n (wA a n) (wB b m) (wC (cMin a b m n + y)) with hE
  have hEne : E ≠ 0 := by
    intro h0; rw [cm, h0] at hpos; simp at hpos
  have hsne : s ≠ 0 := by
    intro h0; rw [hs] at h0; rw [cm, h0] at hpos; simp at hpos
  rw [hrat, cm, cf] at hpp
  have hsPf : 0 < Real.sqrt (piSix (m + r) (wA a n) (wB b m)) := Real.sqrt_pos.mpr hPf
  have hsPm : 0 < Real.sqrt (piSix m (wA a n) (wB b m)) := Real.sqrt_pos.mpr hPm
  field_simp at hpp ⊢
  rw [hs]
  linarith [hpp]

lemma pq_of_labels {a b m n : ℚ} (hL : RacahLabels a b m n) (hcan : |n| ≤ m) :
    ∃ p q : ℕ, m - n = p ∧ m + n = q := by
  obtain ⟨s, hs⟩ := hL.m_sub_n
  obtain ⟨r, hr⟩ := hL.two_m
  have h1 := abs_le.mp hcan
  have hs0 : 0 ≤ s := by
    have : (0 : ℚ) ≤ (s : ℚ) := by rw [← hs]; linarith [h1.2]
    exact_mod_cast this
  have hq0 : 0 ≤ r - s := by
    have : (0 : ℚ) ≤ ((r - s : ℤ) : ℚ) := by push_cast; rw [← hs, ← hr]; linarith [h1.1]
    exact_mod_cast this
  refine ⟨s.toNat, (r - s).toNat, ?_, ?_⟩
  · rw [hs]; exact_mod_cast (Int.toNat_of_nonneg hs0).symm
  · have : m + n = ((r - s : ℤ) : ℚ) := by push_cast; rw [← hs, ← hr]; ring
    rw [this]; exact_mod_cast (Int.toNat_of_nonneg hq0).symm

/-- **`eq:carrierRacah6j`** (canonical sector, as an identity of polynomials in `ς`): for every
`RacahSystem` and `r ≤ D`, with `A = wA a n`, `B = wB b m`, `u = A⁻²`, `v = B⁻²`, `w = (AB)⁻¹`,
`P̃_{m+r}(ς; u, v, w) = c · R_r(λ(ς))` with `λ(ς) = 4ABς + (A-B)² - (c_min+½)²` and `R_r(λ)` the
terminating Racah polynomial of `eq:physicalRacah4F3` written in `λ = y(y+2c_min+1)`, `c ≠ 0`
independent of `ς`. -/
theorem ptilde6_eq_racah {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D) (hcan : |n| ≤ m)
    (r : ℕ) (hr : r ≤ D) :
    ∃ c : ℝ, c ≠ 0 ∧
      (ptPoly m n r).map (MvPolynomial.eval ![1 / wA a n ^ 2, 1 / wB b m ^ 2,
        1 / (wA a n * wB b m)]) =
        C c * (racahLam ((m : ℝ) - n) ((m : ℝ) + n) (-(D : ℝ) - 1)
          ((cMin a b m n : ℝ) + (cMax a b m n : ℝ) + 1) r).comp
          (C (4 * wA a n * wB b m) * X + C ((wA a n - wB b m) ^ 2 - ((cMin a b m n : ℝ) + 1 / 2) ^ 2)) := by
  have hm0 := mem_rank h hcan 0 (Nat.zero_le _)
  simp only [Nat.cast_zero, add_zero] at hm0
  obtain ⟨hA, hB, -, -, -⟩ := admissible_facts hm0.1 hm0.2
  obtain ⟨c, hc⟩ := ptilde6_lattice_racah h hcan r hr
  obtain ⟨p, q, hp, hq⟩ := pq_of_labels h.labels hcan
  set A := wA a n with hAdef
  set B := wB b m with hBdef
  set γ : ℝ := -(D : ℝ) - 1 with hγ
  set δ : ℝ := (cMin a b m n : ℝ) + (cMax a b m n : ℝ) + 1 with hδ
  have hD := phys_D_real h
  have hs : γ + δ + 1 = 2 * (cMin a b m n : ℝ) + 1 := by rw [hγ, hδ, hD]; ring
  have hc0 : (0 : ℝ) ≤ cMin a b m n := by exact_mod_cast cMin_nonneg a b m n
  set P1 := (ptPoly m n r).map (MvPolynomial.eval ![1 / A ^ 2, 1 / B ^ 2, 1 / (A * B)]) with hP1
  set P2 := C c * (racahLam ((m : ℝ) - n) ((m : ℝ) + n) γ δ r).comp
    (C (4 * A * B) * X + C ((A - B) ^ 2 - ((cMin a b m n : ℝ) + 1 / 2) ^ 2)) with hP2
  -- the lattice points
  set τ : ℕ → ℝ := fun y => (1 - cosA A B (wC (cMin a b m n + y))) / 2 with hτ
  have hτform : ∀ y : ℕ, τ y = ((cMin a b m n + (y : ℝ) + 1 / 2) ^ 2 - (A - B) ^ 2) / (4 * A * B) := by
    intro y
    simp only [hτ, cosA, wC]
    push_cast
    field_simp
    ring
  set S : Finset ℝ := (Finset.range (D + 1)).image τ with hS
  have hinj : Function.Injective τ := by
    intro y y' hyy
    rw [hτform, hτform] at hyy
    have h4 : (4 * A * B) ≠ 0 := by positivity
    have := (div_left_inj' h4).mp hyy
    have hy1 : (0 : ℝ) < (cMin a b m n : ℝ) + y + 1 / 2 := by positivity
    have hy2 : (0 : ℝ) < (cMin a b m n : ℝ) + y' + 1 / 2 := by positivity
    have h5 : ((cMin a b m n : ℝ) + y + 1 / 2) ^ 2 = ((cMin a b m n : ℝ) + y' + 1 / 2) ^ 2 := by
      linarith
    have h6 := (pow_left_inj₀ hy1.le hy2.le (by norm_num)).mp h5
    exact_mod_cast (by linarith : (y : ℝ) = y')
  have hcard : S.card = D + 1 := by
    rw [hS, Finset.card_image_of_injective _ hinj, Finset.card_range]
  have hd1 : P1.natDegree ≤ r := (natDegree_map_le).trans (ptPoly_natDegree_le m n r)
  have hd2 : P2.natDegree ≤ r := by
    refine (natDegree_C_mul_le _ _).trans ?_
    refine (natDegree_comp_le).trans ?_
    have h3 : (C (4 * A * B) * X + C ((A - B) ^ 2 - ((cMin a b m n : ℝ) + 1 / 2) ^ 2) : ℝ[X]).natDegree ≤ 1 := by
      refine (natDegree_add_le _ _).trans (max_le ?_ (by rw [natDegree_C]; exact Nat.zero_le _))
      exact (natDegree_C_mul_le _ _).trans (by simp)
    calc _ ≤ (racahLam ((m : ℝ) - n) ((m : ℝ) + n) γ δ r).natDegree * 1 := Nat.mul_le_mul_left _ h3
      _ ≤ r := by simpa using natDegree_racahLam_le ((m : ℝ) - n) ((m : ℝ) + n) γ δ r
  have hlt : ∀ P : ℝ[X], P.natDegree ≤ r → P.degree < S.card := by
    intro P hP
    refine (degree_le_of_natDegree_le hP).trans_lt ?_
    rw [hcard]; exact_mod_cast Nat.lt_succ_of_le hr
  have heq : P1 = P2 := by
    refine eq_of_degrees_lt_of_eval_finset_eq S (hlt P1 hd1) (hlt P2 hd2) ?_
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    have hy' : y ≤ D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hy)
    rw [hP2, eval_mul, eval_C, eval_comp, eval_add, eval_mul, eval_C, eval_C, eval_X]
    have hlam : 4 * A * B * τ y + ((A - B) ^ 2 - ((cMin a b m n : ℝ) + 1 / 2) ^ 2) =
        (y : ℝ) * ((y : ℝ) + (γ + δ + 1)) := by
      rw [hτform, hs]; field_simp; ring
    rw [hlam, eval_racahLam]
    have : physQ a b m n D r (y : ℝ) =
        racahPoly ((m : ℝ) - n) ((m : ℝ) + n) γ δ r (y : ℝ) := rfl
    rw [← this, ← hc y hy']
    rw [hP1]
    show eval (τ y) (Polynomial.map (MvPolynomial.eval _) (ptPoly m n r)) = _
    rw [ptilde6]
    unfold evalC
    rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_eval_map]
  refine ⟨c, ?_, heq⟩
  intro hc0
  have h0 : P2 = 0 := by rw [hP2, hc0]; simp
  have hcoef : P1.coeff r = kLead m n r := by
    rw [hP1, coeff_map, ptPoly_coeff_top m n hcan r]; simp
  rw [← heq] at h0
  rw [h0] at hcoef
  exact kLead_ne_zero m n p q hp hq hcan r (by simpa using hcoef.symm)

/-- The even Racah deformation `q_d(ς; u, v, w) = P̃_{m+d}/k_{6j}` in `ℝ[u,v,w][ς]`
(canonical sector, `k_{6j} = kLead`). -/
noncomputable def evenRacah6 (m n : ℚ) (d : ℕ) : CarrierRing :=
  cc (kLead m n d)⁻¹ * ptPoly m n d

/-- **`lem:evendeformation6j`** (canonical sector, Lean form), the Racah analogue of
`lem_evendeformation3`.  `q_d = evenRacah6 m n d` is monic of degree `d` in `ς` with coefficients in
`ℝ[u,v,w]` (`u = A⁻²`, `v = B⁻²`, `w = (AB)⁻¹`, i.e. polynomials in `A⁻²`, `B⁻²`, `(AB)⁻¹`); at
`u = v = w = 0` it is the monic Jacobi polynomial `P̂_d^{(m-n,m+n)}`; and on every `RacahSystem`
it is a nonzero `ς`-independent multiple of the Racah polynomial `R_d(λ(ς))` of `eq:physicalRacah4F3`,
`λ(ς) = 4ABς + (A-B)² - (c_min+½)²` (`ptilde6_eq_racah`).  The paper's degree bound on the coefficients
(`≤ j` in `ε²`, rational in `δ²` with denominator `(1-δ²)^j`) and the estimate `eq:evendeformationbound`
are not stated here. -/
theorem lem_evendeformation6 (m n : ℚ) (p q : ℕ) (hp : m - n = p) (hq : m + n = q) (hcan : |n| ≤ m)
    (d : ℕ) :
    (evenRacah6 m n d).natDegree ≤ d ∧ (evenRacah6 m n d).coeff d = 1 ∧
      (evenRacah6 m n d).map (MvPolynomial.eval ![(0 : ℝ), 0, 0]) = jacobiMonicTau p q d ∧
      ∀ (a b : ℚ) (D : ℕ), RacahSystem a b m n D → d ≤ D →
        ∃ κ : ℝ, κ ≠ 0 ∧
          (evenRacah6 m n d).map (MvPolynomial.eval ![1 / wA a n ^ 2, 1 / wB b m ^ 2,
            1 / (wA a n * wB b m)]) =
            C κ * (racahLam ((m : ℝ) - n) ((m : ℝ) + n) (-(D : ℝ) - 1)
              ((cMin a b m n : ℝ) + (cMax a b m n : ℝ) + 1) d).comp
              (C (4 * wA a n * wB b m) * X +
                C ((wA a n - wB b m) ^ 2 - ((cMin a b m n : ℝ) + 1 / 2) ^ 2)) := by
  have hk := kLead_ne_zero m n p q hp hq hcan d
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold evenRacah6 cc
    exact (natDegree_C_mul_le _ _).trans (ptPoly_natDegree_le m n d)
  · unfold evenRacah6 cc
    rw [coeff_C_mul, ptPoly_coeff_top m n hcan d, ← MvPolynomial.C_mul, inv_mul_cancel₀ hk]
    simp
  · have e : (ptPoly m n d).map (MvPolynomial.eval ![(0 : ℝ), 0, 0]) = ptilde6Zero m n d := rfl
    have h2 := ptilde6Zero_eq_kLead_mul_monic m n p q hp hq d
    unfold evenRacah6 cc
    rw [Polynomial.map_mul, Polynomial.map_C, e, h2]
    simp only [MvPolynomial.eval_C]
    rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hk, C_1, one_mul]
  · intro a b D hR hdD
    obtain ⟨c, hc0, hc⟩ := ptilde6_eq_racah hR hcan d hdD
    refine ⟨(kLead m n d)⁻¹ * c, mul_ne_zero (inv_ne_zero hk) hc0, ?_⟩
    unfold evenRacah6 cc
    rw [Polynomial.map_mul, Polynomial.map_C, hc, ← mul_assoc, ← C_mul]
    simp

end FormalResearch.Racah

/-- info: 'FormalResearch.Racah.ptilde6_lattice_racah' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.ptilde6_lattice_racah

/-- info: 'FormalResearch.Racah.ptilde6_eq_racah' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.ptilde6_eq_racah

/-- info: 'FormalResearch.Racah.lem_evendeformation6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.lem_evendeformation6
