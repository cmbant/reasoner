module

public import FormalResearch.Racah.P2AnalyticCarrier6j

/-!
# The `6j` carrier identity in the canonical sector: the induction (Weyl P2, `lem:sqrtfreecarrier`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, proof of `lem:sqrtfreecarrier` ("divide the
recurrence by `E W Π^{-1/2}`; it therefore suffices to check the starts and to define `P̃` by the
recurrences").

* `carrier_step`: from the carrier form at `f` and `f-1` and the carrier recursion `hP`, the carrier
  form at `f+1`; the input is `Phi6_midpoint_recurrence` at `f`, with `√Π_{f+1} = √Π_f η_{f+1}`.
* `carrierClaim_zero` (seed, `Phi6_seed_carrier`), `carrierClaim_one` (`m ≠ 0`: the recurrence at
  `f = m` where `R_m = 0`; `m = 0`: `Phi6_exceptional_one`), `carrierClaim_succ`: the induction.
* `Phi6_carrier_canonical`, `Phi6_carrier_canonical'`: for every physical point with `m ≥ |n|`
  (hypotheses exactly those of `Phi6_midpoint_recurrence` and `Phi6_seed`: both triads at `f`, the
  two `c`-triads, no density or lattice argument),
  `Φ_f = E_{A,B}(C) W_{6j}(x) · Π_f(A,B)^{-1/2} · P̃_f(τ; A⁻², B⁻², (AB)⁻¹)`, `f = m + d`.
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner FormalResearch.Racah.SixJ

/-! ### The induction step -/

lemma etaK_pos (A B k : ℝ) (hA : 0 < A) (hB : 0 < B) (hk : 0 ≤ k) (hkA : k < 2 * A)
    (hkB : k < 2 * B) : 0 < etaK A B k := by
  unfold etaK
  apply Real.sqrt_pos.mpr
  have h1 : k ^ 2 / (4 * A ^ 2) < 1 := by
    rw [div_lt_one (by positivity)]; nlinarith
  have h2 : k ^ 2 / (4 * B ^ 2) < 1 := by
    rw [div_lt_one (by positivity)]; nlinarith
  exact mul_pos (by linarith) (by linarith)

lemma etaK_sq (A B k : ℝ) (hA : 0 < A) (hB : 0 < B) (hk : 0 ≤ k) (hkA : k < 2 * A)
    (hkB : k < 2 * B) :
    etaK A B k ^ 2 = (1 - k ^ 2 / 4 * (1 / A ^ 2)) * (1 - k ^ 2 / 4 * (1 / B ^ 2)) := by
  have hp := etaK_pos A B k hA hB hk hkA hkB
  unfold etaK at *
  rw [Real.sq_sqrt (Real.sqrt_pos.mp hp).le]
  ring

lemma carrier_step_alg (f R0 R1 e0 e1 η2 Dg N s Pd Pd1 Pd2 Φ Φm Φp : ℝ)
    (hf : f ≠ 0) (hR1 : R1 ≠ 0) (he1 : e1 ≠ 0)
    (hΦ : Φ = N * s * Pd1) (hΦm : R0 * Φm = R0 * (N * s * e0 * Pd)) (hη : e0 ^ 2 = η2)
    (hrec : Dg * Φ = f * (R1 * e1) * Φp + (f + 1) * (R0 * e0) * Φm)
    (hP : Pd2 = 1 / (f * R1) * (Dg * Pd1 - (f + 1) * R0 * η2 * Pd)) :
    Φp = N * (s * e1⁻¹) * Pd2 := by
  subst hη
  have hfR : f * R1 ≠ 0 := mul_ne_zero hf hR1
  have hP' : f * R1 * Pd2 = Dg * Pd1 - (f + 1) * R0 * e0 ^ 2 * Pd := by
    rw [hP]; field_simp
  have h2 : f * R1 * e1 * Φp = f * R1 * e1 * (N * (s * e1⁻¹) * Pd2) := by
    have e : e1 * e1⁻¹ = 1 := mul_inv_cancel₀ he1
    calc f * R1 * e1 * Φp = Dg * Φ - (f + 1) * e0 * (R0 * Φm) := by linear_combination -hrec
      _ = f * R1 * e1 * (N * (s * e1⁻¹) * Pd2) := by
        rw [hΦm, hΦ]
        linear_combination (N * s) * (-hP') + (N * s * f * R1 * Pd2) * (-e)
  exact mul_left_cancel₀ (mul_ne_zero hfR he1) h2

/-- One step of the carrier induction: the carrier form at `f` and (when `R_f ≠ 0`) at `f - 1`, and
the recursion `hP` defining the next carrier value, give the carrier form at `f + 1`.  The
hypotheses are those of `Phi6_midpoint_recurrence` at `f` (obtained from the triads at `f+1`). -/
theorem carrier_step (a b c m n f : ℚ) (hmn : |n| ≤ m) (hfm : m ≤ f) (hf0 : 0 < f)
    (h1 : IsTri (f + 1) (b + m) b) (h2 : IsTri (f + 1) a (a + n)) (Pd Pd1 Pd2 : ℝ)
    (hΦf : Phi6 a b c f m n =
      edgeFac m n (wA a n) (wB b m) (wC c) * (Real.sqrt (piSix f (wA a n) (wB b m)))⁻¹ * Pd1)
    (hΦm : rootR m n f ≠ 0 → Phi6 a b c (f - 1) m n =
      edgeFac m n (wA a n) (wB b m) (wC c) *
        (Real.sqrt (piSix (f - 1) (wA a n) (wB b m)))⁻¹ * Pd)
    (hP : Pd2 = 1 / ((f : ℝ) * rootR m n ((f : ℝ) + 1)) *
      ((2 * (f : ℝ) + 1) * ((f : ℝ) * ((f : ℝ) + 1) *
          (1 - 2 * ((1 - cosA (wA a n) (wB b m) (wC c)) / 2) -
            (2 * (f : ℝ) * ((f : ℝ) + 1) + 1 - (m : ℝ) ^ 2 - (n : ℝ) ^ 2) / 8 *
              (1 / (wA a n * wB b m))) - m * n) * Pd1 -
        (((f : ℝ) + 1) * rootR m n (f : ℝ)) *
          ((1 - (f : ℝ) ^ 2 / 4 * (1 / wA a n ^ 2)) * (1 - (f : ℝ) ^ 2 / 4 * (1 / wB b m ^ 2))) *
          Pd)) :
    Phi6 a b c (f + 1) m n =
      edgeFac m n (wA a n) (wB b m) (wC c) *
        (Real.sqrt (piSix (f + 1) (wA a n) (wB b m)))⁻¹ * Pd2 := by
  have hm0 : 0 ≤ m := le_trans (abs_nonneg n) hmn
  obtain ⟨hn1, hn2⟩ := abs_le.mp hmn
  have hf1 : IsTri f (b + m) b :=
    isTri_of_succ h1 (by linarith) (by linarith)
  have hf2 : IsTri f a (a + n) :=
    isTri_of_succ h2 (by linarith) (by linarith)
  obtain ⟨hA, hB, -, -, hfr⟩ := admissible_facts hf1 hf2
  obtain ⟨hAb, hBb⟩ := adm_bounds hf1 hf2
  obtain ⟨hAb', hBb'⟩ := adm_bounds h1 h2
  push_cast at hAb' hBb'
  have hrec := Phi6_midpoint_recurrence a b c f m n hf1 hf2
  set A := wA a n with hAdef
  set B := wB b m with hBdef
  set N := edgeFac m n A B (wC c) with hN
  have hpi : 0 ≤ piSix f A B := piSix_nonneg f A B hA hB (by linarith) (by linarith)
  have he1pos : 0 < etaK A B ((f : ℝ) + 1) :=
    etaK_pos A B _ hA hB (by linarith) (by linarith) (by linarith)
  have he0pos : 0 < etaK A B (f : ℝ) :=
    etaK_pos A B _ hA hB hfr (by linarith) (by linarith)
  have hsq := sqrt_piSix_succ f hf0.le A B hpi
  set s := (Real.sqrt (piSix f A B))⁻¹ with hs
  have hR1 : rootR m n ((f : ℝ) + 1) ≠ 0 := by
    unfold rootR
    apply (Real.sqrt_pos.mpr _).ne'
    have hfm' : (m : ℝ) ≤ f := by exact_mod_cast hfm
    have hm0' : (0 : ℝ) ≤ m := by exact_mod_cast hm0
    have hn1' : (n : ℝ) ≤ m := by exact_mod_cast hn2
    have hn2' : -(m : ℝ) ≤ n := by exact_mod_cast hn1
    apply mul_pos <;> nlinarith
  have hΦm' : rootR m n f * Phi6 a b c (f - 1) m n =
      rootR m n f * (N * s * etaK A B f * Pd) := by
    by_cases hR0 : rootR m n f = 0
    · rw [hR0]; ring
    · congr 1
      rw [hΦm hR0]
      have hg : 0 ≤ f - 1 := by
        -- `R_f ≠ 0` forces `f > m`, and `f - m ∈ ℕ`
        have hfm' : m < f := by
          rcases lt_or_eq_of_le hfm with h | h
          · exact h
          · exfalso; apply hR0; rw [← h]; unfold rootR; simp
        obtain ⟨k, hk⟩ := h1.2.1
        have : f + 1 - (b + m) + b = k := hk
        have hk2 : (2 : ℚ) ≤ k := by
          have : (f : ℚ) + 1 - m = k := by linarith
          have hk1 : (1 : ℚ) < k := by linarith
          have : 1 < k := by exact_mod_cast hk1
          exact_mod_cast this
        linarith
      have hpi' := sqrt_piSix_succ (f - 1) hg A B
        (piSix_nonneg (f - 1) A B hA hB (by push_cast; linarith) (by push_cast; linarith))
      rw [sub_add_cancel] at hpi'
      have hc : (((f - 1 : ℚ) : ℝ) + 1) = f := by push_cast; ring
      rw [hc] at hpi'
      have hpi'' : Real.sqrt (piSix f A B) = Real.sqrt (piSix (f - 1) A B) * etaK A B (f : ℝ) := by
        rw [hpi']
      rw [hs, hpi'', mul_inv]
      field_simp
  have hη := etaK_sq A B (f : ℝ) hA hB hfr (by linarith) (by linarith)
  have hmain := carrier_step_alg (f : ℝ) (rootR m n f) (rootR m n ((f : ℝ) + 1))
    (etaK A B f) (etaK A B ((f : ℝ) + 1))
    ((1 - (f : ℝ) ^ 2 / 4 * (1 / A ^ 2)) * (1 - (f : ℝ) ^ 2 / 4 * (1 / B ^ 2)))
    ((2 * (f : ℝ) + 1) * ((f : ℝ) * ((f : ℝ) + 1) * (cosA A B (wC c) - qf f m n A B) - m * n))
    N s Pd Pd1 Pd2 (Phi6 a b c f m n) (Phi6 a b c (f - 1) m n) (Phi6 a b c (f + 1) m n)
    (by exact_mod_cast hf0.ne') hR1 he1pos.ne' hΦf hΦm' hη hrec
    (by rw [hP]; unfold qf; ring)
  rw [hmain, hsq, mul_inv]


/-! ### The carrier identity in the canonical sector -/

/-- The carrier expression `E W Π_f^{-1/2} P̃_f(τ; A⁻², B⁻², (AB)⁻¹)` at the physical point
`(a,b,c)` with `A = wA a n`, `B = wB b m`, `C = wC c`, `τ = (1 - x)/2`, `x = cosA A B C`
(`eq:sqrtfreecarrier`, 6j version), `f = m + d`. -/
noncomputable def carrier6 (a b c m n f : ℚ) (d : ℕ) : ℝ :=
  edgeFac m n (wA a n) (wB b m) (wC c) * (Real.sqrt (piSix f (wA a n) (wB b m)))⁻¹ *
    ptilde6 m n ((1 - cosA (wA a n) (wB b m) (wC c)) / 2) (1 / wA a n ^ 2) (1 / wB b m ^ 2)
      (1 / (wA a n * wB b m)) d

/-- Both triads at `f` follow from those at `f + 1` in the canonical sector. -/
lemma isTri_pair_of_succ {a b f m n : ℚ} (hmn : |n| ≤ m) (hfm : m ≤ f)
    (h1 : IsTri (f + 1) (b + m) b) (h2 : IsTri (f + 1) a (a + n)) :
    IsTri f (b + m) b ∧ IsTri f a (a + n) := by
  have hm0 : 0 ≤ m := le_trans (abs_nonneg n) hmn
  obtain ⟨hn1, hn2⟩ := abs_le.mp hmn
  exact ⟨isTri_of_succ h1 (by linarith) (by linarith), isTri_of_succ h2 (by linarith) (by linarith)⟩

/-- The statement of the carrier identity at rank `f = m + j`. -/
def CarrierClaim (a b c m n : ℚ) (j : ℕ) : Prop :=
  ∀ f : ℚ, f = m + j → IsTri f (b + m) b → IsTri f a (a + n) →
    Phi6 a b c f m n = carrier6 a b c m n f j

lemma carrierClaim_zero (a b c m n : ℚ) (h3 : IsTri c a b) (h4 : IsTri c (b + m) (a + n)) :
    CarrierClaim a b c m n 0 := by
  intro f hf h1 h2
  have hf' : f = m := by simpa using hf
  subst hf'
  rw [Phi6_seed_carrier a b c f n h1 h2 h3 h4]
  unfold carrier6
  rw [ptilde6_zero]

lemma rootR_self (m n : ℚ) : rootR m n m = 0 := by
  unfold rootR; simp

lemma carrierClaim_one (a b c m n : ℚ) (hmn : |n| ≤ m) (h3 : IsTri c a b)
    (h4 : IsTri c (b + m) (a + n)) : CarrierClaim a b c m n 1 := by
  intro f hf h1 h2
  have hm0 : 0 ≤ m := le_trans (abs_nonneg n) hmn
  by_cases hm : m = 0
  · -- exceptional start
    subst hm
    have hn : n = 0 := by
      have := abs_nonpos_iff.mp hmn
      exact this
    subst hn
    have hf1 : f = 1 := by rw [hf]; simp
    subst hf1
    have ha : 1 ≤ 2 * a := by
      have := isNat_nonneg' h2.2.2
      linarith
    have hb : 1 ≤ 2 * b := by
      have := isNat_nonneg' h1.2.2
      linarith
    have hex := Phi6_exceptional_one a b c h3 ha hb
    obtain ⟨hA, hB, -, -, -⟩ := admissible_facts h1 h2
    obtain ⟨hAb, hBb⟩ := adm_bounds h1 h2
    have he := etaK_pos (wA a 0) (wB b 0) 1 hA hB (by norm_num) (by push_cast at hAb; linarith)
      (by push_cast at hBb; linarith)
    unfold carrier6
    rw [hex]
    have hedge : edgeFac 0 0 (wA a 0) (wB b 0) (wC c) = 1 := by
      simp [edgeFac, edgeSq, cenProd]
    have hpi : piSix 1 (wA a 0) (wB b 0) = etaK (wA a 0) (wB b 0) 1 ^ 2 := by
      rw [etaK_sq _ _ _ hA hB (by norm_num) (by push_cast at hAb; linarith)
        (by push_cast at hBb; linarith)]
      simp [piSix]
      ring
    rw [hedge, hpi, Real.sqrt_sq he.le, ptilde6_one_of_eq]
    field_simp
    ring
  · have hmpos : 0 < m := lt_of_le_of_ne hm0 (Ne.symm hm)
    have hfm : f = (m : ℚ) + 1 := by simpa using hf
    subst hfm
    obtain ⟨hf1, hf2⟩ := isTri_pair_of_succ (f := m) hmn le_rfl h1 h2
    have hseed := carrierClaim_zero a b c m n h3 h4 m (by simp) hf1 hf2
    unfold carrier6 at hseed ⊢
    have := carrier_step a b c m n m hmn le_rfl hmpos h1 h2 0
      (ptilde6 m n ((1 - cosA (wA a n) (wB b m) (wC c)) / 2) (1 / wA a n ^ 2) (1 / wB b m ^ 2)
        (1 / (wA a n * wB b m)) 0)
      (ptilde6 m n ((1 - cosA (wA a n) (wB b m) (wC c)) / 2) (1 / wA a n ^ 2) (1 / wB b m ^ 2)
        (1 / (wA a n * wB b m)) 1) hseed
      (fun h => absurd (rootR_self m n) h)
      (by
        rw [ptilde6_one_of_ne m n hm, ptilde6_zero, rootR_self]
        ring)
    exact this

lemma carrierClaim_succ (a b c m n : ℚ) (hmn : |n| ≤ m) (d : ℕ)
    (c0 : CarrierClaim a b c m n d) (c1 : CarrierClaim a b c m n (d + 1)) :
    CarrierClaim a b c m n (d + 2) := by
  intro f' hf' h1' h2'
  obtain ⟨f, rfl⟩ : ∃ f, f' = f + 1 := ⟨f' - 1, by ring⟩
  have hm0 : 0 ≤ m := le_trans (abs_nonneg n) hmn
  obtain ⟨hn1, hn2⟩ := abs_le.mp hmn
  have hfd : f = m + ((d + 1 : ℕ) : ℚ) := by push_cast at hf' ⊢; linarith
  have hd0 : (0 : ℚ) ≤ d := Nat.cast_nonneg d
  have hfm : m ≤ f := by rw [hfd]; push_cast; linarith
  have hf0 : 0 < f := by rw [hfd]; push_cast; linarith
  obtain ⟨hf1, hf2⟩ := isTri_pair_of_succ hmn hfm h1' h2'
  have hfR : (f : ℝ) = (m : ℝ) + d + 1 := by rw [hfd]; push_cast; ring
  have := carrier_step a b c m n f hmn hfm hf0 h1' h2'
    (ptilde6 m n ((1 - cosA (wA a n) (wB b m) (wC c)) / 2) (1 / wA a n ^ 2) (1 / wB b m ^ 2)
      (1 / (wA a n * wB b m)) d)
    (ptilde6 m n ((1 - cosA (wA a n) (wB b m) (wC c)) / 2) (1 / wA a n ^ 2) (1 / wB b m ^ 2)
      (1 / (wA a n * wB b m)) (d + 1))
    (ptilde6 m n ((1 - cosA (wA a n) (wB b m) (wC c)) / 2) (1 / wA a n ^ 2) (1 / wB b m ^ 2)
      (1 / (wA a n * wB b m)) (d + 2))
    (c1 f hfd hf1 hf2)
    (fun _ => by
      have hg : IsTri (f - 1 + 1) (b + m) b ∧ IsTri (f - 1 + 1) a (a + n) := by
        rw [sub_add_cancel]; exact ⟨hf1, hf2⟩
      obtain ⟨g1, g2⟩ := isTri_pair_of_succ (f := f - 1) hmn
        (by rw [hfd]; push_cast; linarith) hg.1 hg.2
      exact c0 (f - 1) (by rw [hfd]; push_cast; ring) g1 g2)
    (by rw [ptilde6_succ_succ, hfR])
  exact this

theorem carrierClaim_all (a b c m n : ℚ) (hmn : |n| ≤ m) (h3 : IsTri c a b)
    (h4 : IsTri c (b + m) (a + n)) (d : ℕ) : CarrierClaim a b c m n d := by
  have key : ∀ d : ℕ, CarrierClaim a b c m n d ∧ CarrierClaim a b c m n (d + 1) := by
    intro d
    induction d with
    | zero => exact ⟨carrierClaim_zero a b c m n h3 h4, carrierClaim_one a b c m n hmn h3 h4⟩
    | succ d ih => exact ⟨ih.2, carrierClaim_succ a b c m n hmn d ih.1 ih.2⟩
  exact (key d).1

/-- **`lem:sqrtfreecarrier`, canonical sector** (`eq:sqrtfreecarrier`, 6j version).  For every
physical point of the sector `m ≥ |n|` (the hypotheses are those of `Phi6_midpoint_recurrence` and
`Phi6_seed`: both triads at `f`, and the two `c`-triads), with `f = m + d`,
`Φ_f = E_{A,B}(C) W_{6j}(x) · Π_f(A,B)^{-1/2} · P̃_f(τ; A⁻², B⁻², (AB)⁻¹)`,
`τ = (1-x)/2`, `x = cosA A B C`, `A = wA a n`, `B = wB b m`, `C = wC c`. -/
theorem Phi6_carrier_canonical (a b c f m n : ℚ) (hmn : |n| ≤ m) (h1 : IsTri f (b + m) b)
    (h2 : IsTri f a (a + n)) (h3 : IsTri c a b) (h4 : IsTri c (b + m) (a + n)) (d : ℕ)
    (hd : f = m + d) :
    Phi6 a b c f m n =
      edgeFac m n (wA a n) (wB b m) (wC c) * (Real.sqrt (piSix f (wA a n) (wB b m)))⁻¹ *
        ptilde6 m n ((1 - cosA (wA a n) (wB b m) (wC c)) / 2) (1 / wA a n ^ 2) (1 / wB b m ^ 2)
          (1 / (wA a n * wB b m)) d :=
  carrierClaim_all a b c m n hmn h3 h4 d f hd h1 h2

/-- The same, with `d = f - m` determined by `f` (it is a natural number on every physical point). -/
theorem Phi6_carrier_canonical' (a b c f m n : ℚ) (hmn : |n| ≤ m) (h1 : IsTri f (b + m) b)
    (h2 : IsTri f a (a + n)) (h3 : IsTri c a b) (h4 : IsTri c (b + m) (a + n)) :
    Phi6 a b c f m n = carrier6 a b c m n f ⌊f - m⌋₊ := by
  obtain ⟨k, hk⟩ := h1.2.1
  have hd : f = m + ((⌊f - m⌋₊ : ℕ) : ℚ) := by
    have : f - m = k := by linarith
    rw [this, Nat.floor_natCast]; linarith
  exact Phi6_carrier_canonical a b c f m n hmn h1 h2 h3 h4 _ hd

/-- info: 'FormalResearch.Racah.Phi6_carrier_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi6_carrier_canonical

end FormalResearch.Racah
