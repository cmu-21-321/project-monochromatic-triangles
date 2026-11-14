import Mathlib

set_option linter.style.header false

open scoped BigOperators

namespace MonochromaticTriangles


/- true means an edge is red, false means blue. self-loops are ignored -/
structure Coloring (n : ℕ) where
  red : Fin n → Fin n → Bool -- Fin n means the naturals up to n exclusively
  symmetric : ∀ u v, red u v = red v u

/- the red degree of a particular coloring is the cardinality of the set of
   edges {u, v} where u ≠ v ∧ {u, v} is red (true) -/
def redDegree {n : ℕ} (c : Coloring n) (v : Fin n) : ℕ :=
  (Finset.univ.filter
    (fun u => u ≠ v ∧ c.red v u = true)).card

/- same as red degree but checks {u, v} is blue, or false -/
def blueDegree {n : ℕ} (c : Coloring n) (v : Fin n) : ℕ :=
  (Finset.univ.filter
    (fun u => u ≠ v ∧ c.red v u = false)).card

/- this returns all three-element subsets of the vertex set -/
def triangles (n : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Fin n)).powersetCard 3

/- all edges between distinct members of s have one color -/
def isMonochromaticWith {n : ℕ}
    (c : Coloring n) (color: Bool) (s : Finset (Fin n)) : Prop :=
    ∀ u ∈ s, ∀ v ∈ s, u ≠ v → c.red u v = color

/- allows lean to decide whether a finite vertex set is monochromatic -/
instance {n : ℕ} (c : Coloring n) :
    DecidablePred (isMonochromaticWith c color) := by
  intro s
  unfold isMonochromaticWith
  infer_instance

/- given some coloring c, we return all monochromatic traingles out of all
   possible triangles -/
def monoTrianglesWith {n : ℕ}
    (c : Coloring n) (color : Bool): Finset (Finset (Fin n)) :=
  (triangles n).filter (isMonochromaticWith c color)

/- how many such monochromatic triangles there are -/
def monoCount {n : ℕ} (c : Coloring n) : ℕ :=
  ∑ color : Bool, (monoTrianglesWith c color).card

/- there are n - 1 vertices besides v itself - lemma for degree_sum -/
lemma card_ne {n : ℕ} (v : Fin n) :
    (Finset.univ.filter (fun u : Fin n => u ≠ v)).card = n - 1 := by
  rw [Finset.filter_ne' Finset.univ v,
      Finset.card_erase_of_mem (Finset.mem_univ v),
      Finset.card_univ, Fintype.card_fin]

/- every other vertex contributes to exactly one degree. -/
theorem degree_sum {n : ℕ} (c : Coloring n) (v : Fin n) :
    redDegree c v + blueDegree c v = n - 1 := by
  rw [← card_ne v]
  rw [← Finset.card_filter_add_card_filter_not (fun u => c.red v u = true)]
  simp only [redDegree, blueDegree, Finset.filter_filter, Bool.not_eq_true]

/- Goodman's identity -/
theorem goodman_identity {n : ℕ} (c : Coloring n) (hn : 3 ≤ n) :
    2 * monoCount c +
      (∑ v : Fin n, redDegree c v * blueDegree c v) =
      2 * Nat.choose n 3 := by
  sorry

/- Lemma used for six_vertices lower bound,
   Proves the arithmetic-mean geometric-mean inequality -/
lemma four_mul_le_sq (r b : ℕ) : (4 * (r * b) ≤ (r + b) ^ 2) := by
  zify
  nlinarith [sq_nonneg ((r : ℤ) - b)]

/- Goodman's identity applied to get the result that there are at least two mono
   triangle in K₆ -/
theorem six_vertices_lower_bound (c : Coloring 6) :
    2 ≤ monoCount c := by
  have h := goodman_identity c (by norm_num)
  have hsum : ∑ v : Fin 6, redDegree c v * blueDegree c v ≤ 36 := by
    calc ∑ v : Fin 6, redDegree c v * blueDegree c v
        ≤ ∑ _v : Fin 6, 6 := by
          apply Finset.sum_le_sum
          intro v _
          have h4 := four_mul_le_sq (redDegree c v) (blueDegree c v)
          rw [degree_sum c v] at h4      -- h4 : 4 * (r * b) ≤ (6 - 1) ^ 2
          norm_num at h4                 -- h4 : 4 * (r * b) ≤ 25
          omega                          -- so r * b ≤ 6
      _ = 36 := by simp
  have hc : Nat.choose 6 3 = 20 := by decide
  rw [hc] at h
  omega

/-- Edges within {0, 1, 2} or {3, 4, 5} are red; edges between the groups are blue. -/
def twoTriangles : Coloring 6 where
  red u v := decide (u.val / 3 = v.val / 3)
  symmetric := by
    intro u v
    simp only [eq_comm]

lemma monoCount_twoTriangles : monoCount twoTriangles = 2 := by
  decide

/- exactly 2 mono triangles -/
theorem six_vertices_sharp :
    ∃ c : Coloring 6, monoCount c = 2 := by
  exact ⟨twoTriangles, monoCount_twoTriangles⟩

end MonochromaticTriangles
