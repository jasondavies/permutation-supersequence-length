# Nine letters

**Independent reproduction, 2026-11-18.** OEIS records the nine-letter minimum of 66 and credits Vitaliy Garnashevich with its computation on October 10, 2025. The local proof uses Tan’s eight-letter theorem. Its word and lower-bound certificates have been replayed. Independent mathematical review of this proof is pending. [OEIS attribution](https://oeis.org/A062714/internal) [Ten-letter proof](../ten/proof.md).

## A word of length 66

On the alphabet 0 through 8, concatenate the following line as written.

```text
801234560781234506871234058612307485612038475610283456107823456108
```

The length is 66. A left-to-right greedy scan embeds each of the 362,880 permutations.

## A lower bound of 65

Write f(n) for the minimum universal length. This argument uses f(6)=28, f(7)=39, and Tan's f(8)=52 as external inputs. The eight-letter proof has not been independently audited here. [Tan, Theorems 1 and 3](https://arxiv.org/html/2501.11386v1).

It suffices to rule out length 64, since appending symbols preserves universality. Choose the letter x whose first occurrence comes last and let r be its frequency. Erase x, leaving a word of length t=64−r on eight letters. Number the old gaps occupied by copies of x in their original order. Write Pᵢ and Qᵢ for the portions of the projected word before and after copy i. They have total length t. Q₁ and Pᵣ each contain every eight-letter permutation, by placing x first or last. Hence |P₁| and |Qᵣ| are at most h=t−52. Since P₁ contains all eight letters, r≤4.

For consecutive copies i and i+1, partition the other eight letters into A and B. Either Pᵢ contains all permutations of A or Qᵢ₊₁ contains all permutations of B. Otherwise take a missing order α on A and a missing order β on B. The permutation αxβ cannot use a copy up through i or one from i+1 onward.

In particular Pᵢ followed by **one arbitrary ordering of all eight letters** followed by Qᵢ₊₁ is universal. For any requested permutation, take its longest prefix embedded in Pᵢ. If an additional letter remains, supply that letter from the inserted ordering. The prefix including that letter was missing, so the complementary suffix embeds in Qᵢ₊₁ by the partition property. Consequently each internal gap has length at most h+8. Summing the two outer gaps and r−1 internal gaps gives

```text
t ≤ 2h + (r−1)(h+8),    or equivalently    r(t−44) ≥ 60.
```

For r=1,2,3 and t=64−r the left side is respectively 19, 36, 51. Only r=4 remains, with t=60 and h=8.

For any adjacent-copy cut whose first side has length at most eight, its other side has length at least 40. To see this, if the short side misses a letter a, the other side must contain all permutations of the remaining seven, accounting for 39 positions. It must also contain a, since the short side cannot itself contain all permutations on those seven. Otherwise the short side is a permutation of the eight letters. It misses an order on every pair, forcing the other side to contain every permutation on every six-letter subset.

Such a six-complete word has length at least 40. In any universal word on k letters some letter occurs at least k times. This follows by induction, removing the prefix through the last new letter and deleting all remaining copies of that letter. Each other letter loses at least one occurrence and the remainder is universal. Apply this to the six *least* frequent letters. Their combined frequency is at least 28, their largest frequency is at least six, and each of the two remaining letters occurs at least six times.

Apply the short-side observation to P₁ and symmetrically to Q₄. It gives |Q₂|, |P₃|≥40, hence |P₂|, |Q₃|≤20. Applying the insertion observation to the cut between copies two and three now gives an eight-letter universal word of length at most 20+8+20=48. This contradicts f(8)=52 and proves the bound.

## Excluding length 65

The calculation below uses the exact lengths for alphabets of size zero through eight as inputs. It has two parts. A count enumeration covers every possible 65-letter word with 118 templates, and a propositional refutation rules out every ordering in each template. The templates allow arbitrary permutations within their six gaps. Padding any shorter universal word would give a word of length 65, so this exclusion and the length-66 witness give **f(9)=66**.

### A necessary test on letter frequencies

A capacity vector bounds the number of available copies of each letter. Every test in this part accepts a superset of the realizable vectors. Let C(v) denote the test implemented in [frequency_bounds.hpp](../shared/frequency_bounds.hpp). For the empty alphabet it accepts. On m letters it requires positive capacities, total at least the known lower bound, and the pivot and first-occurrence conditions below. For m=9 the input lower bound on the total is zero.

**One cut.** For m previously treated letters and a prefix budget p, compute Hₘ(p), a lower bound on the suffix budget across a pair of consecutive pivot copies. For every split into S and its complement, one side must pass C on its corresponding subset, by the partition property above. Enumerate every nonnegative sorted count vector of length m summing to p, and likewise for the suffix budget q. A vector's signature is the family of subsets on which C passes. A signature contained in another signature at the same budget can be discarded. Decrease q from f(m) while some pair covers every complementary split. This gives Hₘ(p), capped at f(m).

Both vectors can be sorted in the same order. To prove this, sort the left vector and swap an inversion in the right vector at positions i,j with leftᵢ≤leftⱼ but rightᵢ>rightⱼ. The only suffix tests that could worsen contain i and omit j. If such a test is needed, its complementary prefix set failed. Replacing j by i in that prefix gives a componentwise weaker prefix, which also failed. Its old complementary suffix therefore passed, and has exactly the counts of the new suffix under test. Repeating removes all inversions.

**Multiple cuts.** If a pivot occurs r times and the other letters have total t, put u₁=t−f(m). An upper bound on the projected length before copy j+1 is uⱼ₊₁=t−Hₘ(uⱼ), since the complementary suffix after that copy must have at least Hₘ(uⱼ) positions. Before the last copy the prefix must have at least f(m) positions. Once the upper bound reaches f(m) the test can accept. For each r store the least t passing this test up to the search limit. Apply it to a least frequent letter of v. The tests use only smaller alphabets and are monotone in available capacity. In particular Hₘ is nonincreasing, and the successive upper bounds start at t−f(m) and cannot decrease. Giving a pivot an additional copy or any other letter an additional position preserves acceptance of the cut test.

**First occurrences.** Delete a first letter a of a requested permutation and everything through its earliest occurrence in the word. The suffix must be universal on the remaining letters. Charge one copy to each letter preceding a in the order of first appearances, remove a, and apply C recursively. Some first-appearance ordering must pass every deletion. It suffices to test decreasing capacity order. In an adjacent inversion x,y with x having smaller capacity, swap them. The test that deletes y improves because x is no longer charged. In the new test that deletes x, the remaining capacity of y is at least the remaining capacity of x in the old test that deleted y. Every other test has the same charges. This proves the exchange rule. It also proves monotonicity inductively, since the equivalent existential ordering test permits keeping an old order after increasing a budget. A vector of upper bounds may always be attained as exact counts by inserting unused copies.

### From counts to six gaps

Enumerating the sorted positive nine-part partitions of 65 leaves **233** vectors passing C, each with least entry five. Choose x to be the last new letter. At least eight positions precede its first copy, and at least 52 projected positions must follow it. Hence it occurs exactly five times and the first nine positions form a permutation ending in x. Reading backwards proves that the final nine positions also form a permutation. At this stage the last new letter in reverse may differ from x.

Erase x. The projection has length 60 with count vector t and starts and ends with permutations of the eight other letters. Use the following four *count vectors* in this projection.

| Vector | Portion counted |
| --- | --- |
| c | Before copy 2 of x |
| l | Before copy 3 |
| r | After copy 3, so r=t−l |
| d | After copy 4 |

Each vector includes the corresponding end permutation. The suffix after copy 2 and the prefix before copy 4 contain all ordered six-letter subsets. Indeed the opposite side of the adjacent-copy cut lies within one permutation and misses some order on every pair. A six-complete word on eight letters has length at least 40 by the preceding proof. Consequently the totals of c and d are at most 20.

There are three further necessary tests in [nine_templates.cpp](nine_templates.cpp).

1. If a word starts or ends with a permutation and is universal on S, deleting the end permutation leaves a word universal on every (|S|−2)-subset of S. At a leading permutation, put the omitted pair in an order it misses and then demand any order of the others. Reverse for a trailing permutation. Test C on S itself and on the |S|−2 smallest capacities in S after subtracting one from each. Write F(z) for the resulting signature. The argument applies to sets of size at least two, with smaller sets using C directly.
2. Enumerate c and d componentwise above the all-ones vector with total at most 20. The complementary portion t−c or t−d is six-complete and has a permutation at its far end. Test its six smallest counts by the preceding rule. Enumerate l+r=t with both sides positive. The cuts between copies 2 and 3 and between copies 3 and 4 require F(c) and F(r), and F(l) and F(d), respectively, to cover every complementary split. Upper bounds on unassigned coordinates can already reject a partial assignment. The final test uses the actual vectors, including c≤l and d≤r. For equal totals tᵢ, relabel to put lᵢ in nondecreasing order.
3. To test that GQ can contain every ordered k-subset, split such a subset as A,a,B. If a is read in G, G must contain a and must be universal on A for that alternative to handle every order of A. If a is read in Q, Q must be universal on B after its first a. When Q ends in a permutation and contains just one a, its suffix after a cannot be universal on two or more letters. If both alternatives fail their necessary tests, choose the two failing orders independently. Apply this test with k=8 to G=l−1, Q=r, since deleting everything through the first x gives a universal projection. Here 1 is the all-ones vector. Apply it with k=6 to G=l−c, Q=r and symmetrically to G=r−d, Q=l in reverse. When x is the unique five-copy letter, it also finishes the first permutation in reverse, giving the reverse k=8 test with G=r−1, Q=l.

The enumeration explicitly checks that every surviving assignment has a **unique** five-copy letter. This matters because it puts x at both inner endpoints of the outside permutations. The six successive gaps then have count vectors

```text
1, c−1, l−c, r−d, d−1, 1.
```

The search produces 757 count arrays before the final renaming and reversal. Sorting the eight letter columns and identifying each array with its reverse leaves 118. An unexpected surviving case with several five-copy letters stops the program with an error.

### Checking the 118 ordering problems

Within each gap, distinguish the occurrences and fix the order of copies of the same symbol. Assign a pairwise comparison variable to each remaining token pair within a gap. The two transitivity clauses on each triple make the comparisons a total order. Comparisons across gaps are fixed.

For an event e, U(e,S) asserts that every order of S can finish strictly before e. The terminal sentinel follows the word. For every a in S require an occurrence q of a with q<e and U(q,S−{a}). This is necessary and sufficient. For permutations ending in a, the latest a before e gives at least as much room to their prefixes as any earlier copy. Use the empty subset as the base case. Require U(sentinel,all) in both reading directions. The encoding uses one-way implications for positive witnesses. Every universal ordering extends to a satisfying assignment by setting true witnesses according to their meaning. An UNSAT certificate therefore rules out all orderings. The encoder drops predecessors earlier than a guaranteed later copy of the same letter and simplifies constant literals.

For each template the checker regenerates the ordering formula and loads its selected original clauses. The shared reverse unit propagation (RUP) checker verifies all 3,258 clause additions over the 118 formulas. Every trace ends with the empty clause. The case list must match the enumeration exactly. [Ordering encoder](check_nine.py), [certificate archive](nine.rupcol.xz), [certificate format and replay rule](../FORMAT.md).

From the repository root, run `python verify.py nine` to check both bounds. To check only the displayed witness, run `python -m proofs.nine.check_nine --word-only`.
