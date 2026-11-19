# The shortest supersequence of all ten-letter permutations has length 83

Let $f(n)$ be the shortest length of a word containing all permutations of $n$ symbols as subsequences. **We obtain $f(10)=83$ by a computer-assisted proof.** The following 83-symbol word contains all 3,628,800 permutations of the digits, as verified by direct greedy matching.

```text
01234567890123456780293451670823451960782134506978231405678213904567823109456782301
```

A construction of length 83 was already known. The lower bound follows by excluding length 82. A shorter universal word could be extended to length 82 by appending arbitrary letters. In a hypothetical length-82 word, the last symbol to make its first appearance has at least nine other symbols before it. The suffix following it must still contain all permutations of the other nine symbols, which requires at least 66 positions on those symbols. Thus this last new symbol occurs at most $82-9-66=7$ times. It suffices to exhaust the following cases for the least frequent symbol. [Published upper bound and attribution, Zălinescu](https://www.research-collection.ethz.ch/server/api/core/bitstreams/231cdcef-9c70-4e66-89d9-0296ef17e5ea/content), [nine-letter lower bound and replay](../nine/proof.md).

| Minimum frequency | Exclusion at length 82 |
|---|---|
| At most 4 | The pivot inequality excludes at most three copies. Short outer cuts exclude four copies. [Derivation](#at-most-four-copies), [Lean proof](../../lean/Four.lean). |
| 5 | Complementary cuts and frequency tests leave 922 ordering templates. Each has a refutation. |
| 6 | After verifying 304 smaller-alphabet frequency exclusions, 1,372 endpoint patterns remain. Each has a refutation. |
| 7 | Every end begins with a permutation. Nine-letter projections and two ten-letter refutations cover all 1,131 templates. |

The proof uses the exact values through $f(8)=52$, including Tan’s eight-letter theorem, and the computational value $f(9)=66$. The latter has a separate replay in this repository. The eight-letter lower bound is an external input. [Tan’s eight-letter proof](https://arxiv.org/abs/2501.11386).

The mathematical reductions and enumerators below are part of the proof. A clause certificate checks the unsatisfiability of the formula that the corresponding enumerator produces.

## The cut condition

Choose a symbol x occurring r times. Delete its copies, leaving a word of length t. Let Pᵢ denote the projected prefix before occurrence i and Qᵢ the projected suffix after it. Thus |Pᵢ|+|Qᵢ|=t. Call a word universal on S if it contains every order of S. For every subset S of the other nine symbols, **Pᵢ is universal on S or Qᵢ₊₁ is universal on its complement**. Otherwise, take a missing order from each side and join them with x. Any occurrence of x is too early for the first order or too late for the second. Also Q₁ and Pᵣ must each be universal on all nine symbols.

A cut whose sides both have length below 52 uses all nine symbols on each side. A missing symbol would force the other side to contain all orders of the other eight. Adding an arbitrary letter to either side preserves the cut condition. These two facts let us enumerate at fixed budgets and infer bounds on shorter cuts.

For the count test, take all partitions of each length into nine positive frequencies. Use the necessary frequency test from the nine-letter proof on each subset, including the length bound 66 for nine letters. When a side has a permutation of the alphabet at one end, there is an extra test. If it is universal on a set S of size k≥3, deleting the end permutation must leave a universal word on each (k−2)-subset of S. To see this for an opening permutation, request the other two letters first, in the order that the opening misses. The suffix must read at least the second letter and everything after it. Reversal gives the terminal version. It suffices for the frequency check to test the k−2 least counts after subtracting one. The sorting exchange in the nine-letter proof lets us discard a pair of partitions if its common increasing alignment already fails. For each pair that passes, enumerate **all** relative labelings up to simultaneous relabeling. [Frequency test and sorting argument](../nine/proof.md), [cut enumeration](cut_catalog.cpp).

To decide whether actual orders realize a cut, order the occurrence tokens on each side by Boolean comparisons, fixing the order of copies of the same letter and imposing transitivity on triples. Either side can be reversed independently since this preserves which subsets are universal. For a prescribed end permutation, require every first occurrence to precede every second occurrence. For each side introduce a variable U(S) asserting universality on S. Require downward closure and the cut disjunction for each complementary pair.

A missing subsequence gives a clause. Follow its greedy embedding from the first occurrence of the first letter. Each time the next letter skips an occurrence, record the comparison that forces that skip. When even the last copy of a required letter is too early, the resulting chain of comparisons forces failure. At least one comparison must change whenever U(S) holds. The solver starts with such clauses for orders of up to four letters, then checks longer orders by subset dynamic programming and adds clauses as necessary. A separate direct calculation checks all 512 complementary splits in every accepted pair of words. The checker repeats the decisions with a second SAT solver. [Exact cut solver](cut_solver.py).

## At most four copies

For a pivot with $r$ copies, put $t=82-r$ and $h=t-66$. Each outer gap has length at most $h$. Replacing any internal gap by one permutation of the other nine letters gives a nine-letter universal word, so each internal gap has length at most $h+9$. Summing the two outer and $r-1$ internal gap bounds gives $r(25-r)\ge75$, excluding $r=1,2,3$. [Gap replacement argument](../nine/proof.md#a-lower-bound-of-65).

**Short outer cuts.** Suppose $(P,Q)$ is a complementary cut on nine letters and $|P|\le12$. If $P$ misses a letter, $Q$ is universal on the other eight and has length at least 52. Otherwise choose six letters that occur just once in $P$. Their three-letter complement occupies at most six positions in $P$, so it misses an order since $f(3)=7$. Hence $Q$ is universal on the six selected letters and uses them at least 28 times. In any universal word on $k$ letters some letter occurs at least $k$ times. Indeed, deleting the prefix through the last new letter and erasing its remaining copies leaves a universal word on the other $k-1$ letters, each of which lost at least one copy.

Write $u,v$ for the two largest of the six selected counts in $Q$, with $u\ge v$. Then $u\ge6$. The two letters miss an order in $P$, so $Q$ needs at least $f(7)=39$ positions on their complement. If $|Q|\le49$, then $u+v\le10$, $v\le4$, and all six occupy at most $u+v+4v\le26$ positions. This contradicts 28. Thus $|Q|\ge50$.

For $r=4$, $t=78$ and the two outer gaps have at most 12 positions. The short-cut bound gives $|Q_2|,|P_3|\ge50$, hence $|P_2|,|Q_3|\le28$. Replace the gap between the second and third copies by one permutation of the nine old letters. The resulting nine-letter universal word has length at most $28+9+28=65$, contradicting $f(9)=66$. [Formal proof](../../lean/Four.lean).

## Cutting at the five occurrences

Suppose x occurs exactly five times. Delete x to get a word of length 77 on the other nine symbols. Let Pᵢ and Qᵢ be the portions before and after the original occurrence i of x. Universality requires Q₁ and P₅ to be universal on all nine symbols. At every cut between consecutive x's and every subset S of the nine symbols, Pᵢ must be universal on S or Qᵢ₊₁ must be universal on its complement. Missing orders on the two sides could otherwise be concatenated with x to give a missing ten-letter permutation. In particular both outer gaps have length at most 11 because f(9)=66.

For a first side of length at most 11, the opposite side has length at least 51. If a symbol is missing this follows from $f(8)=52$. Otherwise at least seven letters are singletons. Every six of these are universally covered on the opposite side, since their three-letter complement occupies at most five positions on the first side. Applying the multiplicity bound above to the six least frequent among the seven forces two of the seven to occur at least six times each. Their missing pair order forces 39 positions on the seven-letter complement, for a total of at least 51. Consequently |Q₂| and |P₄| are at least 51. Thus |P₂| and |Q₄| are at most 26. [Count test and its sorting argument](../nine/proof.md), [cut enumeration](cut_catalog.cpp).

The length-11 bound is sharp for the cut condition alone. Take the left word `80123456788` and the right word `817562340835716428036574182356740814372568047135286`. Direct greedy matching gives 18 subsets on which the left is universal. For each of the other 494 subsets, the right is universal on its complement. [Subset signature checker](cut_solver.py).

Reverse the word if necessary so that |Q₃|≤38. At padded budgets (26,38) there are 287 pairs of count vectors up to simultaneous relabeling that pass the frequency test. Exactly 22 admit orderings passing all complementary splits. Each of the other 265 has an archived refutation of its cut formula, including the missing-order clauses learned by the lazy search, which the replay validates before use. A pair without a refutation is kept, so the archive can only remove certified infeasible pairs. [Cut certificates](five-cuts.rupcol.xz), [cut replay](cut_certificates.py), [certificate generator](make_cut_certificates.py). For a smaller pair to be possible, adding any symbol on a side below its budget must again give a possible pair. Repeat this test downwards. The remaining dimensions and counts are

| Length of P₂ | Length of Q₃ | Count pairs |
|---:|---:|---:|
| 26 | 38 | 22 |
| 26 | 37 | 3 |
| 25 | 38 | 1 |

In particular |Q₂| is 51 or 52 and |P₃| is 39 or 40. If the first gap P₁ omitted a symbol a, Q₂ would have to be universal on the other eight. It would also need an a since P₁ cannot contain every order on eight symbols. That takes at least 53 positions. Thus **P₁ contains every old symbol**, and x is the last new letter in this orientation. Positivity of both count vectors at the (11,52) outer cut follows from this argument. [Exact cut decisions](cut_solver.py).

## Generating all templates

Fix one of the 26 pairs (p,q) in the table, where p counts P₂ and q counts Q₃. Pad the reverse cut (Q₄,P₃) on its first side to length 26. The catalog at (26,39) or (26,40) lists every possible multiset for the count vector l of P₃. Enumerate all relative labelings of l, identifying only permutations of identical columns of (p,q). The gap g from the second to the third x has counts l−p. Discard negative entries. The full old-letter counts are l+q, each at least five by the earlier four-copy exclusion. Q₂ has counts g+q.

At the outer cut use budgets (11,51) or (11,52), keeping all relative labelings of the two vectors that pass the frequency test. Reduce the first budget by the same arbitrary-padding condition. Match the right vector to g+q in every way, including every permutation of labels with equal counts. This gives possible vectors e for the opening gap P₁. The second gap has counts b=p−e. Require nonnegative entries and the nine-letter frequency bound on the projected suffix after the first x, whose counts are l+q−e.

Each resulting template has seven consecutive blocks

```text
e    x    b    x    g    x    (q together with two more x's)
```

Each block allows every ordering of its multiset. In particular the final two occurrences of x have arbitrary positions in the last block. Apply the recursive window tests below to the full word. For each required projection, use the count test from the six-copy branch with an empty list of excluded profiles. This checks the possible first and last new letters of nearly shortest projections, including the shared middle when their demands are disjoint. In particular, every triple in the opening has at most five positions, so the opposite side must be universal on every complementary six-set. Every pair of singletons in the opening also forces universality on its seven-letter complement. The stronger count tests reduce the 1,669 templates from the basic window test to **922 surviving templates**, up to common relabeling. [Template generator](five_halves.cpp), [window tests](windows.hpp).

## Window tests

Each block specifies only a multiset. For a required alphabet in an interval of blocks, first test its total frequencies. For each pivot letter apply the complementary-subset argument across consecutive blocks containing that letter. Include each whole boundary block on its respective side, which grants every possible ordering in that block. Also test the suffix beginning at the first block with that letter and the prefix ending at its last such block on the remaining letters. Recursion on the alphabet size terminates.

There is an additional within-block constraint. Consider a required permutation of form A a b B and a particular block. If some order of A fails up to and including the previous block containing a, then the occurrence of a must be in the current block or later. If some order of B fails from the next block containing b onward, b must be in the current block or earlier. Both can hold in the same requested permutation since A and B are disjoint. This forces a then b within the block. A missing letter or a cycle of these precedences among singly occurring letters eliminates the template. [Window tests](windows.hpp).

## Excluding the remaining orderings

Order the occurrence tokens in each block by Boolean comparisons, fixing the relative order of copies of the same letter. Impose transitivity on every triple. For each token t and subset S, encode a positive literal requiring every ordering of S to occur strictly before t. For each possible final letter a of S there must be an occurrence of a before t that follows a prefix universal on S minus a. This holds even if different prefixes use different occurrences of a, since the latest available occurrence subsumes all earlier ones. The reverse encoding requires universality strictly after t. An interval of whole blocks that fails the window test gives a constant false literal. Including the whole endpoint block only enlarges the allowed interval.

Require the prefix before the last x and suffix after the first x to cover all old symbols universally. For each consecutive pair of x tokens add the complementary-subset disjunction for every subset of the old alphabet. Every universal word supplies a satisfying assignment. Conversely, in a fixed order these conditions are sufficient. For a target A x B, the x's that can follow A form a suffix of the list of occurrences, and those that can precede B form a prefix. The outer conditions make both lists nonempty. If they do not overlap, a cut between adjacent copies witnesses the failure.

All 922 ordering formulas are unsatisfiable. The checker regenerates the templates and the formulas, requires exact coverage of the cases, and checks 341,931 clause additions by unit propagation against the original clauses. [Ordering encoder](pivot_formula.cpp), [proof archive](five.rupcol.xz), [replay](replay_branch.py).

## Seven copies as the minimum

The last new symbol x can occur at most seven times. At least nine other letters precede its first occurrence, and at least 66 others must follow. If every letter occurs at least seven times, equality holds in both inequalities. The opening ten letters form a permutation ending in x. After this permutation, erase further copies of x. The remaining 66-letter word is universal on nine symbols, each with at least six copies. Its own last new letter y has at most 66−8−52=6 copies. Equality again forces its opening nine to form a permutation ending in y. Reversal gives two corresponding demands at the other end, with last new letters z and u when read backwards. All four distinguished letters have total frequency seven in the original word. The roles may coincide across the two ends.

For every partition of 82 into ten counts of at least seven, apply the deletion test in decreasing order of first appearance. Delete one seven-copy symbol and one occurrence of every other letter and check the resulting nine-letter counts. Also require the suffix after the opening permutation to cover every eight-letter subset. For a given subset, request the other two letters in the order that the opening misses. Testing its eight least frequent letters suffices by monotonicity. This leaves 26 total profiles.

Choose x, z, y and u, with y distinct from x and u distinct from z, identifying only interchangeable equal-frequency letters. The first two blocks of the word are a permutation of the nine letters other than x, then x itself. The next two are a permutation of the eight letters other than x and y, with any number of copies of x interleaved, then y. The same description works backwards at the right end. These two sets of blocks are disjoint even at their maximum lengths. The remaining middle has determined counts and arbitrary order. The window tests leave **1,131 ten-letter templates**. [Template generator](seven_templates.cpp).

Each template makes a nine-letter prediction at each end. Remove its first ten positions and all further copies of x. This leaves seven blocks whose concatenation must be universal on the nine remaining letters. After the first two of those blocks the suffix must also be universal on the eight letters other than y and x. Repeat from the reverse orientation. Sorting the columns of the projected blocks gives 297 distinct predictions.

In two templates the proof tests the joint demands directly. In addition to full universality, the prefix demands are the empty order, x, and xy. Their earliest completions allow the residual word to start at blocks 0, 2, and 4 respectively, numbering from zero. The backward demands are the empty order, z, and zu, with residual ends at blocks 8, 6, and 4. For every disjoint pair of demands the interval must contain all orders of the complementary alphabet. The ordering encoder applies the same cut argument as for five copies, restricting each demand to its designated blocks.

The archive supplies 229 nine-letter projection refutations and two joint refutations. The checker regenerates the templates, checks which predictions belong to each, verifies every clause trace, and requires all 1,131 templates to be covered. The traces contain **2,055,500 RUP additions**. Thus minimum multiplicity seven is impossible. [Certificate archive](seven.rupcol.xz), [replay and coverage check](replay_branch.py).

## Minimum multiplicity six

For this remaining case the first and last blocks covering all ten letters each have length ten or eleven. A length-eleven opening has a single duplicated letter and its last new letter has six occurrences in the entire word. The analogous conclusion holds at the terminal end.

Enumerate sorted total counts of length 82 and minimum six. The necessary deletion test in decreasing order of first appearance leaves 507 profiles. For each, choose a last new letter of frequency six or seven and, for an eleven-letter end, its duplicate. The tail after the opening, projected off the last new letter, must be universal on the other nine symbols. If a pair of singly occurring letters in the opening misses one of its orders, the tail must contain every order of the other eight symbols. Apply those same conditions at the right end. For the shared middle, combine any disjoint pair of the following demands from the two ends. The last new letter on its own leaves the rest to be read after that end block. A pair whose reverse order is missing also leaves the remaining letters to be read after the block. Thus the middle counts must pass the capacity test on the complement of the two disjoint demands. Up to relabeling and reversal, 299 total count profiles and 3,082 choices of end blocks pass these tests. The stronger frequency tests below reduce this set before checking the possible interior orders. [Endpoint enumeration](six_profiles.cpp).

## Certifying the endpoint frequency tests

The coarse enumeration above uses only the earlier frequency test. A stronger test leaves **1,372 endpoint patterns**. It uses 304 excluded frequency profiles on six through nine letters. A profile excludes every componentwise smaller profile on the same alphabet, since insertion would extend a universal word to the larger counts. The checker verifies the library in increasing alphabet size. A profile can use exclusions only from strictly smaller alphabets during its own verification. [Profile library](excluded-profiles.txt), [frequency test](profile_capacity.hpp), [profile enumeration](profile_templates.cpp).

For a vector of capacities on $k$ letters, first apply the established frequency and first-appearance deletion tests. The deletion test charges one occurrence of each letter already seen when a new letter first occurs. It suffices to check decreasing frequency order. Exchanging two adjacent letters whose frequencies increase preserves or enlarges the capacities of one of the previously required projections, up to relabeling. Existence of a universal word with the smaller capacities implies existence with the enlarged capacities by insertion. [Deletion argument](../nine/proof.md).

For profiles within three positions of the known optimum, check both ends of the word. At one end choose its last new letter $a$ and the subset of other letters repeated before it. There must be at least one occurrence of each letter in this end block and a second occurrence of every letter marked as repeated. Subtracting only these lower bounds enlarges the available tail. Requesting $a$ first forces universality on its complement in the tail. Requesting two singletons in the order the end block misses forces universality on their complement as well. For disjoint left and right demands both tests apply in the shared middle. The end blocks are disjoint whenever the two last new letters are distinct, since the first copy of the left last new letter must precede the last copy of the right last new letter. Indeed, in the opposite order every occurrence of the former would follow every occurrence of the latter, contradicting universality on that pair. If they coincide and occur at least twice the blocks are again disjoint. The test makes an allowance for a common last new letter used only once, which would require a universal word on the other letters on each side.

For the 304 particular profiles, enumerate the exact counts in both end blocks, including all possible extra copies. If the left last new letter is $a$ and its total frequency is $r$, at most $L-r-(k-1)-f(k-1)$ extra old letters can precede its first occurrence. The reverse bound applies at the other end. Identify simultaneous relabelings and reversal. Apply the smaller-dimensional tests and the window test. In each remaining five-block template, the whole word must be universal, as must the projected suffix after the opening and projected prefix before the closing. The ordering encoder refutes all remaining templates.

| Alphabet size | Profiles certified | Ordering formulas | Clause additions verified by reverse unit propagation (RUP) |
|---:|---:|---:|---:|
| 6 | 15 | 66 | 13,599 |
| 7 | 61 | 360 | 148,546 |
| 8 | 102 | 329 | 3,144,693 |
| 9 | 126 | 22 | 439,679 |
| **Total** | **304** | **777** | **3,746,517** |

## Certifying the 1,372 ten-letter patterns

A pattern gives five multisets in order. The second and fourth blocks are the two distinguished last new letters. The middle block permits every order of its multiset. Give every occurrence its own token and introduce Boolean comparisons between differently labeled tokens of the same block. Fix token order across blocks and between successive copies of a letter. Transitivity gives a total order in each block. Letters with identical counts in every block can be named in order of first appearance.

For each pattern the archive contains a list of trial words and a refutation. A trial word supplies comparisons from which to derive necessary clauses. The proof depends on the clauses being necessary and jointly inconsistent. It does not depend on how the trial words were selected or on the search visiting every ordering. The checker validates each trial word against the block counts before deriving any clauses. [Six-copy archive](six.rupcol.xz), [clause generator](six_formula.cpp), [coverage and unit-propagation checker](replay_branch.py).

**Required regions.** The whole word must contain every permutation of the ten letters. Removing the opening block leaves required alphabets given by its last new letter or a missed order of two singleton letters. Apply the same rule from the right, and combine disjoint demands to obtain required alphabets for the middle block. A universal alphabet in a region also requires every subset of that alphabet there. Taking maximal required sets preserves these implications.

**Possible first and last appearances.** In a required region choose the last new letter $a$ and the counts through its first occurrence. Each other letter must have appeared at least once, with additional lower bounds from known block comparisons. After deleting all copies of $a$, a universal tail on the other letters must still fit. When the slack permits at most three extra letters beyond the mandatory ones, enumerate the exact counts. Each count fixes comparisons between the chosen token of $a$ and the neighboring ranked copies of the other letters. With larger slack use only the lower bounds. At least one option must hold in each direction. Two exact end options can be discarded together when their required middle fails the frequency tests.

**Missing orders.** Subset dynamic programming gives the latest greedy endpoint among orders of each subset. A missing order yields a disjunction of comparisons that would have to change for it to fit. In a greedy step to the $j$-th copy of a letter, the preceding part of the order ends at or after copy $j-1$. Keep the comparisons that establish this lower bound, then the comparison with copy $j-1$. If no copy was skipped there is no earlier comparison to keep. If the whole letter is exhausted, preserving the recorded comparisons preserves the failure. Read backwards for suffixes.

**Complementary cuts.** At any pair of consecutive copies of a pivot in a required region, the prefix before the earlier copy must cover a chosen subset or the suffix after the later copy must cover its complement. If both count vectors fail, enlarge each vector coordinate by coordinate while keeping it infeasible. Some enlarged capacity must be exceeded in every solution. To exceed a prefix cap of $h$ copies of a letter, its $(h+1)$-st regional copy must precede the pivot. The suffix uses the corresponding copy counted from the right. Their disjunction is a necessary clause. Outer prefix and suffix requirements yield clauses by the same argument.

**Intervals between prescribed orders.** Take an order of a set $A$ ending as late as possible in the forward greedy scan and an order of a disjoint set $B$ beginning as early as possible from the right. Holding the recorded greedy comparisons fixes a lower bound on the left endpoint and an upper bound on the right. The intervening open interval must cover the complementary alphabet. If the endpoints overlap, they must change order or a recorded comparison must change. If the interval fails a frequency test, enlarge the failing vector as above. For each letter of cap $h$, keep enough of its copies outside the interval to leave at most $h$ inside. Since equal-letter tokens are ordered, this needs at most one comparison at each end. Relaxing one of these comparisons or one of the greedy bounds is necessary for a solution.

The generator may discard duplicate, subsumed, or excess clauses. Discarding clauses relaxes the formula. Refuting the retained clauses still excludes the pattern. For proof numbering the encoder activates all retained clauses with one final unit clause. If a necessary clause is already empty, it uses that clause alone.

The 1,372 ten-letter refutations contain **5,741,008** verified clause additions. Together with the 777 smaller ordering cases, this excludes minimum multiplicity six and completes the length-82 lower bound.

## Verifying the certificates

Each family has one XZ-compressed CBOR sequence. The nine- and ten-letter certificates share the same encoding and propagation checker. [Wire format](../FORMAT.md). Each record identifies the case, the original clause numbers used, and the ordered list of clauses to derive. The checker regenerates the selected original clauses from the case. For each claimed clause it assumes the negation of every literal and requires unit propagation to reach a conflict before adding that clause. Every refutation finishes with the empty clause. The checker also regenerates the case lists to verify coverage. Across the five-, six- and seven-copy cases, including the smaller frequency proofs, it checks 3,567 refutations and 11,918,778 clause additions, including the 265 central cuts. [Certificate reader](../shared/certificates.py), [verifier](replay_branch.py), [replay instructions](../../README.md#reproduce-the-result).
