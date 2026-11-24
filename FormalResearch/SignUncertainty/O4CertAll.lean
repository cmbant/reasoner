module

public import FormalResearch.SignUncertainty.O4CertRun01
public import FormalResearch.SignUncertainty.O4CertRun02
public import FormalResearch.SignUncertainty.O4CertRun03
public import FormalResearch.SignUncertainty.O4CertRun04
public import FormalResearch.SignUncertainty.O4CertRun05
public import FormalResearch.SignUncertainty.O4CertRun06
public import FormalResearch.SignUncertainty.O4CertRun07
public import FormalResearch.SignUncertainty.O4CertRun08
public import FormalResearch.SignUncertainty.O4CertRun09
public import FormalResearch.SignUncertainty.O4CertRun10
public import FormalResearch.SignUncertainty.O4CertSound

/-!
# All boxes of the `O4QuotientBound` certificate pass

`checkRange_spec`: `checkRange i0 i1 = true` gives `checkBox i j = true` for `i0 ≤ i < i1`, `j < NT`.  `checkBox_all`: the ten kernel runs
`O4CertRun01 … O4CertRun10` (each four rows of `NT` boxes) cover all `i < NL`, `j < NT`.

Status: proved.
-/

@[expose] public section

namespace FormalResearch.SignUncertainty.O4Cert

theorem checkRange_spec {i0 i1 i j : ℕ} (h : checkRange i0 i1 = true) (hi0 : i0 ≤ i) (hi1 : i < i1) (hj : j < NT) :
    checkBox i j = true := by
  unfold checkRange at h
  rw [List.all_eq_true] at h
  have hi : i ∈ List.range' i0 (i1 - i0) := by
    rw [List.mem_range'_1]; omega
  have := h i hi
  rw [List.all_eq_true] at this
  exact this j (List.mem_range.mpr hj)

theorem checkBox_all {i j : ℕ} (hi : i < NL) (hj : j < NT) : checkBox i j = true := by
  have hNL : NL = 40 := rfl
  rw [hNL] at hi
  by_cases h1 : i < 4
  · exact checkRange_spec run01 (by omega) (by omega) hj
  by_cases h2 : i < 8
  · exact checkRange_spec run02 (by omega) (by omega) hj
  by_cases h3 : i < 12
  · exact checkRange_spec run03 (by omega) (by omega) hj
  by_cases h4 : i < 16
  · exact checkRange_spec run04 (by omega) (by omega) hj
  by_cases h5 : i < 20
  · exact checkRange_spec run05 (by omega) (by omega) hj
  by_cases h6 : i < 24
  · exact checkRange_spec run06 (by omega) (by omega) hj
  by_cases h7 : i < 28
  · exact checkRange_spec run07 (by omega) (by omega) hj
  by_cases h8 : i < 32
  · exact checkRange_spec run08 (by omega) (by omega) hj
  by_cases h9 : i < 36
  · exact checkRange_spec run09 (by omega) (by omega) hj
  exact checkRange_spec run10 (by omega) (by omega) hj

/-- info: 'FormalResearch.SignUncertainty.O4Cert.checkBox_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms checkBox_all

end FormalResearch.SignUncertainty.O4Cert
