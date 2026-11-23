import ProjectTemplate.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.IntervalCases

set_option linter.style.header false

open scoped BigOperators
open Finset

namespace MonochromaticTriangles

/- the product is largest when the red and blue degrees are as close as possible.
   division here is natural number division, so it rounds down -/
lemma degree_product_bound {n : ℕ} (c : Coloring n) (v : Fin n) :
    redDegree c v * blueDegree c v ≤ (n - 1) ^ 2 / 4 := by
  have h := four_mul_le_sq (redDegree c v) (blueDegree c v) -- 4rb ≤ (r + b)^2
  rw [degree_sum c v] at h -- replace r + b with n - 1
  omega -- divide by 4, rounding down since rb is a natural number

/- add the bound at each of the n vertices -/
lemma sum_degree_products_bound {n : ℕ} (c : Coloring n) :
    (∑ v : Fin n, redDegree c v * blueDegree c v) ≤
      n * ((n - 1) ^ 2 / 4) := by
  calc
    _ ≤ ∑ _v : Fin n, (n - 1) ^ 2 / 4 := by
      apply sum_le_sum -- enough to bound the term at each vertex
      intro v _
      exact degree_product_bound c v
    _ = _ := by simp -- the same bound added n times

/- Goodman's identity gives a lower bound for any number of vertices.
   we put the degree bound on the right to avoid subtraction in ℕ -/
theorem goodman_lower_bound {n : ℕ} (c : Coloring n) (hn : 3 ≤ n) :
    2 * Nat.choose n 3 ≤
      2 * monoCount c + n * ((n - 1) ^ 2 / 4) := by
  have h := goodman_identity c hn -- 2M + sum of rb = 2 * choose n 3
  have hsum := sum_degree_products_bound c -- upper bound on the sum of rb
  omega -- replacing that sum by an upper bound gives a lower bound on M

/- with fewer than three vertices, there are no triangles to count.
   used for the k = 0 and k = 1 cases of our construction -/
lemma monoCount_of_lt_three {n : ℕ} (c : Coloring n) (hn : n < 3) :
    monoCount c = 0 := by
  have ht : triangles n = ∅ := by
    apply powersetCard_eq_empty.mpr -- cannot choose 3 elements from a smaller set
    simpa using hn -- univ has n elements
  simp [monoCount, monoTrianglesWith, ht] -- filtering an empty set still gives ∅

/- split the vertices into two groups of k. edges within a group are red,
   and edges between the groups are blue -/
def balancedColoring (k : ℕ) : Coloring (2 * k) where
  red u v := decide ((u.val < k) ↔ (v.val < k)) -- true iff both are in the same group
  symmetric := by
    intro u v
    simp only [iff_comm] -- swapping the vertices doesn't change their color

/- every vertex has exactly k blue neighbours, namely the other group -/
lemma balanced_blueDegree (k : ℕ) (v : Fin (2 * k)) :
    blueDegree (balancedColoring k) v = k := by
  -- split on the group containing v, then count the vertices in the other group
  sorry

/- the remaining k - 1 neighbours are red -/
lemma balanced_redDegree (k : ℕ) (v : Fin (2 * k)) :
    redDegree (balancedColoring k) v = k - 1 := by
  have h := degree_sum (balancedColoring k) v -- red + blue = 2k - 1
  rw [balanced_blueDegree] at h -- red + k = 2k - 1
  have hvbound := v.isLt
  have hk : 0 < k := by omega -- needed when subtracting in ℕ
  omega -- red = k - 1

/- writing choose n 3 without division makes the later arithmetic easier -/
lemma six_mul_choose_three (n : ℕ) :
    6 * Nat.choose n 3 = n * (n - 1) * (n - 2) := by
  -- descending factorial counts ordered choices: n(n - 1)(n - 2) = 3! * choose n 3
  have h := Nat.descFactorial_eq_factorial_mul_choose n 3
  -- expand the factorials and rearrange the multiplication
  simpa [Nat.descFactorial_succ, Nat.factorial,
    Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h.symm

/- when there are 2k vertices, the two degrees sum to 2k - 1.
   their product can be at most k(k - 1) -/
lemma even_degree_product_bound {k : ℕ} (c : Coloring (2 * k))
    (v : Fin (2 * k)) :
    redDegree c v * blueDegree c v ≤ k * (k - 1) := by
  have hvbound := v.isLt -- the existence of v gives k > 0
  have hk : 0 < k := by omega
  have h := four_mul_le_sq (redDegree c v) (blueDegree c v)
  rw [degree_sum c v] at h -- 4rb ≤ (2k - 1)^2
  -- write k in terms of k - 1 so the natural number subtractions are explicit
  have hsub : 2 * k - 1 = 2 * (k - 1) + 1 := by omega
  have hk' : k = (k - 1) + 1 := by omega
  rw [hsub] at h
  nlinarith -- 4rb ≤ 4k(k - 1) + 1, so the integer rb is at most k(k - 1)

/- the arithmetic relating the total triangles to the triangles in two groups.
   used to simplify Goodman's identity in both even-vertex proofs -/
lemma even_choose_identity (k : ℕ) :
    2 * Nat.choose (2 * k) 3 =
      4 * Nat.choose k 3 + (2 * k) * (k * (k - 1)) := by
  -- handle k = 0 and 1, then expand both choose terms using six_mul_choose_three
  sorry

/- every coloring of K_(2k) has at least twice choose k 3 mono triangles -/
theorem even_vertices_lower_bound (k : ℕ) (c : Coloring (2 * k)) :
    2 * Nat.choose k 3 ≤ monoCount c := by
  -- bound the degree sum by 2k * k(k - 1), then use Goodman's identity
  sorry

/- our two groups attain that bound. use their degrees in Goodman's identity -/
lemma monoCount_balancedColoring (k : ℕ) :
    monoCount (balancedColoring k) = 2 * Nat.choose k 3 := by
  -- substitute the construction's degrees into Goodman's identity
  sorry

/- this is the exact minimum for every even number of vertices -/
theorem even_vertices_sharp (k : ℕ) :
    (∀ c : Coloring (2 * k), 2 * Nat.choose k 3 ≤ monoCount c) ∧
      ∃ c : Coloring (2 * k), monoCount c = 2 * Nat.choose k 3 := by
  -- combine the lower bound with the balanced coloring that attains it
  sorry

end MonochromaticTriangles
