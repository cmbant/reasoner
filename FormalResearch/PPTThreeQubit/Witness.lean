import FormalResearch.PPTThreeQubit.Basic

/-!
# Supported witnesses: part (a) of `prop:ppt3-witness`

Source: `family.tex`, `prop:ppt3-witness` (a).  The `A|BC`-product vectors of `R_s = ran B_s`
are the rays of `B_s q_s(z)` and the ray of `v`.
-/

namespace FormalResearch.PPTThreeQubit

open Matrix

noncomputable section

/-- Coordinates of `B_s c`. -/
theorem Bs_mulVec (s : ℝ) (c : Fin 5 → ℂ) :
    Bs s *ᵥ c = ![c 0, c 2 + ω ^ 2 * c 4, c 2 + ω * c 4, -s * c 0 + c 3, c 2 + c 4,
      -s * c 0 + ω * c 3, -s * c 0 + ω ^ 2 * c 3, c 1] := by
  ext i
  fin_cases i <;>
    simp [Bs, bCols, mulVec, dotProduct, Fin.sum_univ_five, uVec, vVec, wVec, eVec, oVec]

private lemma ω_four : ω ^ 4 = ω := by
  linear_combination ω * ω_cube

private lemma two_ω_add_one_ne : (2 : ℂ) * ω + 1 ≠ 0 := by
  have h : ω ^ 2 = -1 - ω := by linear_combination ω_sq_add_ω_add_one
  intro h0
  apply ω_sq_sub_ne
  rw [h]; linear_combination (-1 : ℂ) * h0

/-- The `A|BC`-product vectors in `ran B_s` are the rays of `B_s q_s(z)` together with the ray of
`v` (`prop:ppt3-witness`(a), in the direction needed here: product ⇒ on the curve). -/
theorem prodA_classification {s : ℝ} (hs : 0 < s) (c : Fin 5 → ℂ)
    (h : IsProdA (Bs s *ᵥ c)) :
    (∃ (z l : ℂ), c = l • qs s z) ∨ ∃ l : ℂ, c = l • (Pi.single 1 1 : Fin 5 → ℂ) := by
  obtain ⟨α, μ, hx⟩ := h
  rw [Bs_mulVec] at hx
  have h0 : c 0 = α 0 * μ 0 := hx 0
  have h1 : c 2 + ω ^ 2 * c 4 = α 0 * μ 1 := hx 1
  have h2 : c 2 + ω * c 4 = α 0 * μ 2 := hx 2
  have h3 : -s * c 0 + c 3 = α 0 * μ 3 := hx 3
  have h4 : c 2 + c 4 = α 1 * μ 0 := hx 4
  have h5 : -s * c 0 + ω * c 3 = α 1 * μ 1 := hx 5
  have h6 : -s * c 0 + ω ^ 2 * c 3 = α 1 * μ 2 := hx 6
  have h7 : c 1 = α 1 * μ 3 := hx 7
  have hw2 : ω ^ 2 = -1 - ω := by linear_combination ω_sq_add_ω_add_one
  rw [hw2] at h1 h6
  by_cases ha : α 0 = 0
  · right
    rw [ha] at h0 h1 h2 h3
    simp only [zero_mul] at h0 h1 h2 h3
    have hO : c 4 = 0 := by
      have : (2 * ω + 1) * c 4 = 0 := by linear_combination h2 - h1
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h two_ω_add_one_ne
      · exact h
    have hW : c 2 = 0 := by rw [hO] at h2; linear_combination h2
    refine ⟨c 1, ?_⟩
    ext a
    fin_cases a <;> simp [h0, hO, hW]
    · rw [h0] at h3; linear_combination h3
  · left
    set z : ℂ := α 1 / α 0 with hz
    have hz' : α 1 = z * α 0 := by rw [hz]; field_simp
    rw [hz'] at h4 h5 h6 h7
    have e1 : c 2 + c 4 = z * c 0 := by rw [h4, h0]; ring
    have e2 : -s * c 0 + ω * c 3 = z * (c 2 + (-1 - ω) * c 4) := by rw [h5, h1]; ring
    have e3 : -s * c 0 + (-1 - ω) * c 3 = z * (c 2 + ω * c 4) := by rw [h6, h2]; ring
    have e4 : c 1 = z * (-s * c 0 + c 3) := by rw [h7, h3]; ring
    have hE : c 3 = -z * c 4 := by
      have : (2 * ω + 1) * (c 3 + z * c 4) = 0 := by linear_combination e2 - e3
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h two_ω_add_one_ne
      · linear_combination h
    have hW : c 2 = z * c 0 - c 4 := by linear_combination e1
    have hU : ((z ^ 2 + s : ℂ)) * c 0 = 2 * z * c 4 := by
      rw [hE, hW] at e2 e3
      linear_combination (-1 / 2 : ℂ) * (e2 + e3)
    have hV : c 1 = -(s * z * c 0) - z ^ 2 * c 4 := by
      rw [e4, hE]; ring
    by_cases hq : (z ^ 2 + s : ℂ) = 0
    · have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
      have hz0 : z ≠ 0 := by
        intro hz0
        rw [hz0] at hq
        apply hs'; simpa using hq
      have hO : c 4 = 0 := by
        rw [hq, zero_mul] at hU
        have : (2 * z) * c 4 = 0 := by linear_combination -hU
        rcases mul_eq_zero.mp this with h | h
        · exact absurd (by simpa using h) hz0
        · exact h
      obtain ⟨l, hl⟩ : ∃ l : ℂ, c 0 = 2 * z * l := ⟨c 0 / (2 * z), by field_simp⟩
      refine ⟨z, l, ?_⟩
      have g0 : c 0 = l * (2 * z) := by linear_combination hl
      have g1 : c 1 = l * -(z ^ 2 * (z ^ 2 + 3 * s)) := by
        linear_combination hV - s * z * hl - z ^ 2 * hO + l * z ^ 2 * hq
      have g2 : c 2 = l * (z ^ 2 - s) := by
        linear_combination hW + z * hl - hO + l * hq
      have g3 : c 3 = l * -(z * (z ^ 2 + s)) := by
        linear_combination hE - z * hO + l * z * hq
      have g4 : c 4 = l * (z ^ 2 + s) := by linear_combination hO - l * hq
      ext a
      fin_cases a
      exacts [g0, g1, g2, g3, g4]
    · obtain ⟨l, hl⟩ : ∃ l : ℂ, c 4 = l * (z ^ 2 + s) :=
        ⟨c 4 / (z ^ 2 + s), by field_simp⟩
      refine ⟨z, l, ?_⟩
      have hc0 : c 0 = 2 * z * l := by
        apply mul_left_cancel₀ hq
        linear_combination hU + 2 * z * hl
      have g0 : c 0 = l * (2 * z) := by linear_combination hc0
      have g1 : c 1 = l * -(z ^ 2 * (z ^ 2 + 3 * s)) := by
        linear_combination hV - s * z * hc0 - z ^ 2 * hl
      have g2 : c 2 = l * (z ^ 2 - s) := by linear_combination hW + z * hc0 - hl
      have g3 : c 3 = l * -(z * (z ^ 2 + s)) := by linear_combination hE - z * hl
      ext a
      fin_cases a
      exacts [g0, g1, g2, g3, hl]

/-- Converse direction of `prop:ppt3-witness`(a): the vectors `B_s q_s(z)` are `A|BC`-products. -/
theorem prodA_of_qs (s : ℝ) (z : ℂ) : IsProdA (Bs s *ᵥ qs s z) := by
  refine ⟨![1, z], ![2 * z, (z ^ 2 - s) + ω ^ 2 * (z ^ 2 + s), (z ^ 2 - s) + ω * (z ^ 2 + s),
    -s * (2 * z) + -(z * (z ^ 2 + s))], fun i => ?_⟩
  rw [Bs_mulVec]
  fin_cases i <;> simp [qs] <;>
    first | ring1 | linear_combination (-z * (z ^ 2 + s)) * ω_sq_add_ω_add_one

/-- `B_s v-coordinate vector = v = |111⟩` is an `A|BC`-product. -/
theorem prodA_of_v (s : ℝ) : IsProdA (Bs s *ᵥ (Pi.single 1 1 : Fin 5 → ℂ)) := by
  refine ⟨![0, 1], ![0, 0, 0, 1], fun i => ?_⟩
  rw [Bs_mulVec]
  fin_cases i <;> simp

/-! ### Part (b): the sum-of-squares identity -/

/-- `prop:ppt3-witness`(b), `eq:ppt3-sos`: with `z = x + iy` and `r = |z|²`,
`q_s(z)† H_s q_s(z) = (r - s)² ((r - 5 s)² + 12 s x²)`. -/
theorem formH_qs (s : ℝ) (z : ℂ) :
    formH s (qs s z) =
      (Complex.normSq z - s) ^ 2 * ((Complex.normSq z - 5 * s) ^ 2 + 12 * s * z.re ^ 2) := by
  simp only [formH, Fin.sum_univ_five, hDiag, qs]
  simp [Complex.normSq_apply, sq]
  ring

/-- `eq:ppt3-sos` gives nonnegativity of the form on the curve. -/
theorem formH_qs_nonneg (hs : 0 < s) (z : ℂ) : 0 ≤ formH s (qs s z) := by
  rw [formH_qs]
  have : 0 ≤ (Complex.normSq z - 5 * s) ^ 2 + 12 * s * z.re ^ 2 := by positivity
  positivity

theorem formH_smul (s : ℝ) (l : ℂ) (c : Fin 5 → ℂ) :
    formH s (l • c) = Complex.normSq l * formH s c := by
  simp only [formH, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/-- The `v`-coordinate vector has `H_vv = 1`. -/
theorem formH_single_v (s : ℝ) (l : ℂ) :
    formH s (l • (Pi.single 1 1 : Fin 5 → ℂ)) = Complex.normSq l := by
  rw [formH_smul]
  simp [formH, hDiag, Pi.single_apply]

/-- A Hermitian-form consequence of `prop:ppt3-witness`(a),(b) at the cut `A|BC`: if `B_s c` is
`A|BC`-product then `re(c† H_s c) ≥ 0`. -/
theorem formH_nonneg_of_prodA {s : ℝ} (hs : 0 < s) {c : Fin 5 → ℂ}
    (h : IsProdA (Bs s *ᵥ c)) : 0 ≤ formH s c := by
  rcases prodA_classification hs c h with ⟨z, l, rfl⟩ | ⟨l, rfl⟩
  · rw [formH_smul]; exact mul_nonneg (Complex.normSq_nonneg _) (formH_qs_nonneg hs z)
  · rw [formH_single_v]; exact Complex.normSq_nonneg _

/-! ### The other two cuts: cyclic qubit permutations -/

/-- Index of `|c a b⟩` as a function of the index of `|a b c⟩` (cyclic shift `(a,b,c) ↦ (c,a,b)`). -/
def σB : Fin 8 → Fin 8 := ![0, 4, 1, 5, 2, 6, 3, 7]

/-- Index of `|b c a⟩` as a function of the index of `|a b c⟩` (the inverse cyclic shift). -/
def σC : Fin 8 → Fin 8 := ![0, 2, 4, 6, 1, 3, 5, 7]

theorem prodB_cyc {x : Fin 8 → ℂ} (h : IsProdB x) : IsProdA (fun i => x (σB i)) := by
  obtain ⟨β, μ, hx⟩ := h
  refine ⟨β, fun j => μ ⟨2 * (j.val % 2) + j.val / 2 % 2, by omega⟩, fun i => ?_⟩
  fin_cases i <;> exact hx _

theorem prodC_cyc {x : Fin 8 → ℂ} (h : IsProdC x) : IsProdA (fun i => x (σC i)) := by
  obtain ⟨γ, μ, hx⟩ := h
  refine ⟨γ, μ, fun i => ?_⟩
  fin_cases i <;> exact hx _

/-- The phases by which the cyclic shift `σB` acts on the coordinates `(u_s, v, w, e, o)`. -/
def phaseB : Fin 5 → ℂ := ![1, 1, 1, ω, ω]

/-- The phases by which the inverse shift `σC` acts on the coordinates. -/
def phaseC : Fin 5 → ℂ := ![1, 1, 1, ω ^ 2, ω ^ 2]

theorem Bs_cycB (s : ℝ) (c : Fin 5 → ℂ) :
    (fun i => (Bs s *ᵥ c) (σB i)) = Bs s *ᵥ (fun a => phaseB a * c a) := by
  funext i
  rw [Bs_mulVec, Bs_mulVec]
  fin_cases i <;> simp [σB, phaseB] <;>
    ring_nf <;> simp [ω_cube]

theorem Bs_cycC (s : ℝ) (c : Fin 5 → ℂ) :
    (fun i => (Bs s *ᵥ c) (σC i)) = Bs s *ᵥ (fun a => phaseC a * c a) := by
  funext i
  rw [Bs_mulVec, Bs_mulVec]
  fin_cases i <;> simp [σC, phaseC] <;>
    ring_nf <;> simp [ω_cube, ω_four]

theorem formH_phase (s : ℝ) (d c : Fin 5 → ℂ) (hd : ∀ a, Complex.normSq (d a) = 1) :
    formH s (fun a => d a * c a) = formH s c := by
  simp [formH, hd]

/-- **`prop:ppt3-witness`(b), all cuts.**  If `B_s c` is a product across any of the three
single-qubit cuts then `re(c† H_s c) ≥ 0`.  The cuts `B|AC` and `C|AB` reduce to `A|BC` through
the cyclic shifts, which act on the coordinates by the diagonal phases `(1,1,1,ω,ω)` and
`(1,1,1,ω²,ω²)`; these commute with `H_s`. -/
theorem formH_nonneg_of_cutProduct {s : ℝ} (hs : 0 < s) {c : Fin 5 → ℂ}
    (h : IsCutProduct (Bs s *ᵥ c)) : 0 ≤ formH s c := by
  rcases h with h | h | h
  · exact formH_nonneg_of_prodA hs h
  · have h' := prodB_cyc h
    rw [Bs_cycB] at h'
    have := formH_nonneg_of_prodA hs h'
    rwa [formH_phase s phaseB c (by
      intro a; fin_cases a <;> simp [phaseB, normSq_ω])] at this
  · have h' := prodC_cyc h
    rw [Bs_cycC] at h'
    have := formH_nonneg_of_prodA hs h'
    rwa [formH_phase s phaseC c (by
      intro a; fin_cases a <;> simp [phaseC, normSq_ω_sq])] at this

end

/-- info: 'FormalResearch.PPTThreeQubit.prodA_classification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prodA_classification

/-- info: 'FormalResearch.PPTThreeQubit.prodA_of_qs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prodA_of_qs

/-- info: 'FormalResearch.PPTThreeQubit.prodA_of_v' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prodA_of_v

/-- info: 'FormalResearch.PPTThreeQubit.formH_qs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms formH_qs

/-- info: 'FormalResearch.PPTThreeQubit.formH_nonneg_of_cutProduct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms formH_nonneg_of_cutProduct

end FormalResearch.PPTThreeQubit
