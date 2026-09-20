import Mathlib

namespace FormalResearch.Racah

/-- Elementary identity used to show the physical `c`- and rank-`f` lattices
in the one-small Racah problem have the same cardinality. -/
theorem abs_sub_add_abs_add_eq_two_max (m n : ℚ) :
    |m - n| + |m + n| = 2 * max |m| |n| := by
  by_cases hm : 0 ≤ m
  · rw [abs_of_nonneg hm]
    by_cases hn : 0 ≤ n
    · rw [abs_of_nonneg hn]
      by_cases hnm : n ≤ m
      · have hsub : 0 ≤ m - n := sub_nonneg.mpr hnm
        have hadd : 0 ≤ m + n := add_nonneg hm hn
        rw [abs_of_nonneg hsub, abs_of_nonneg hadd, max_eq_left hnm]
        ring
      · have hmn : m ≤ n := le_of_not_ge hnm
        have hsub : m - n ≤ 0 := sub_nonpos.mpr hmn
        have hadd : 0 ≤ m + n := add_nonneg hm hn
        rw [abs_of_nonpos hsub, abs_of_nonneg hadd, max_eq_right hmn]
        ring
    · have hn' : n ≤ 0 := le_of_not_ge hn
      rw [abs_of_nonpos hn']
      have hsub : 0 ≤ m - n := by linarith
      rw [abs_of_nonneg hsub]
      by_cases hcmp : -n ≤ m
      · have hadd : 0 ≤ m + n := by linarith
        rw [abs_of_nonneg hadd, max_eq_left hcmp]
        ring
      · have hcmp' : m ≤ -n := le_of_not_ge hcmp
        have hadd : m + n ≤ 0 := by linarith
        rw [abs_of_nonpos hadd, max_eq_right hcmp']
        ring
  · have hm' : m ≤ 0 := le_of_not_ge hm
    rw [abs_of_nonpos hm']
    by_cases hn : 0 ≤ n
    · rw [abs_of_nonneg hn]
      have hsub : m - n ≤ 0 := by linarith
      rw [abs_of_nonpos hsub]
      by_cases hcmp : n ≤ -m
      · have hadd : m + n ≤ 0 := by linarith
        rw [abs_of_nonpos hadd, max_eq_left hcmp]
        ring
      · have hcmp' : -m ≤ n := le_of_not_ge hcmp
        have hadd : 0 ≤ m + n := by linarith
        rw [abs_of_nonneg hadd, max_eq_right hcmp']
        ring
    · have hn' : n ≤ 0 := le_of_not_ge hn
      rw [abs_of_nonpos hn']
      have hadd : m + n ≤ 0 := add_nonpos hm' hn'
      rw [abs_of_nonpos hadd]
      by_cases hmn : m ≤ n
      · have hsub : m - n ≤ 0 := sub_nonpos.mpr hmn
        have hmax : -n ≤ -m := by linarith
        rw [abs_of_nonpos hsub, max_eq_left hmax]
        ring
      · have hnm : n ≤ m := le_of_not_ge hmn
        have hsub : 0 ≤ m - n := sub_nonneg.mpr hnm
        have hmax : -m ≤ -n := by linarith
        rw [abs_of_nonneg hsub, max_eq_right hmax]
        ring

end FormalResearch.Racah
