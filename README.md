# Monochromatic Triangles: Formalizing Goodman's Identity in Lean 4

A Lean 4 + Mathlib formalization of **Goodman's identity** for red/blue edge colorings of complete graphs, and the lower bounds on monochromatic triangles that follow from it.

**Authors:** Nada El-Mestkawy and Rashid Baddoura (21-321, Carnegie Mellon University, Fall 2026)

## The mathematics

Color every edge of the complete graph Kₙ red or blue. Let M(c) be the number of monochromatic triangles, and let r_v and b_v be the red and blue degrees of vertex v. **Goodman's identity** (A. W. Goodman, 1959) states

$$2M(c) + \sum_v r_v b_v = 2\binom{n}{3}.$$

An upper bound on the degree products therefore gives a lower bound on monochromatic triangles.

## Main results

| Result | Lean name | File |
|---|---|---|
| Goodman's identity | `goodman_identity` | `Basic.lean` |
| Every coloring of K₆ has at least 2 monochromatic triangles | `six_vertices_lower_bound` | `Basic.lean` |
| Some coloring of K₆ has exactly 2 | `six_vertices_sharp` | `Basic.lean` |
| Lower bound for every n ≥ 3: 2·C(n,3) ≤ 2M(c) + n·⌊(n−1)²/4⌋ | `goodman_lower_bound` | `MoreLemmas.lean` |
| Exact minimum on K₂ₖ: every coloring has at least 2·C(k,3), and some coloring attains it | `even_vertices_sharp` | `MoreLemmas.lean` |

## File layout

```
ProjectTemplate.lean            -- imports the two files below
ProjectTemplate/
  Basic.lean                    -- definitions, Goodman's identity, K₆ results
  MoreLemmas.lean               -- general lower bound and even-order extension
lakefile.toml, lean-toolchain   -- build config (Lean v4.36.0-rc1, Mathlib v4.36.0-rc1)
.github/workflows/              -- CI: builds the project on every push
```

### `ProjectTemplate/Basic.lean`

- **Definitions.**
  - `Coloring n`: a symmetric function `Fin n → Fin n → Bool`, where `true` means red and `false` means blue.
  - `redDegree` and `blueDegree`.
  - `triangles n`: all 3-element subsets, via `powersetCard 3`.
  - `isMonochromaticWith c color s`: every edge in `s` has the given color.
  - `monoCount c`: monochromatic triangles, summed over both colors.
- **`degree_sum`**: r_v + b_v = n − 1.
- **The double count.**
  - `mixedTriples`: ordered triples (centre, red neighbour, blue neighbour).
  - `mixed_total`: counted by centre, there are Σ r_v·b_v of them.
  - `mixed_fiber` and `mixed_double_count`: counted by triangle, using Mathlib's `card_eq_sum_card_fiberwise`.
  - `triangle_contribution`: each triangle contributes 0 mixed triples if monochromatic and 2 otherwise. This is checked by case analysis on the three edge colors.
- **K₆.**
  - `four_mul_le_sq` (AM–GM: 4rb ≤ (r+b)²) gives `six_vertices_lower_bound`.
  - `twoTriangles` (two red triangles joined by blue edges) is verified to have exactly 2 monochromatic triangles with `decide`.

### `ProjectTemplate/MoreLemmas.lean`

- **`degree_product_bound`, `sum_degree_products_bound`, `goodman_lower_bound`**: the general lower bound for any n ≥ 3.
- **`balancedColoring k`**: split K₂ₖ into two groups of k, with edges red within a group and blue between groups. `balanced_blueDegree` and `balanced_redDegree` compute its degrees.
- **`six_mul_choose_three`, `even_choose_identity`**: binomial arithmetic, written without division.
- **`even_vertices_lower_bound`, `monoCount_balancedColoring`, `even_vertices_sharp`**: the exact minimum 2·C(k,3) for every even order.

## Reference

A. W. Goodman. On Sets of Acquaintances and Strangers at any Party. *The American Mathematical Monthly*, 66(9):778–783, 1959. doi:10.1080/00029890.1959.11989408.
