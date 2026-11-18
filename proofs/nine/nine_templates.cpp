// Enumerate every surviving arrangement of letter counts between the five pivots.
#include "../shared/frequency_bounds.hpp"
#include <iostream>
#include <set>

using namespace supersequence;
constexpr int full = 255;
using Columns = std::array<std::array<int, 6>, 8>;

Counts subtract(Counts a, const Counts& b) {
    for (int i = 0; i < 8; ++i) a[i] -= b[i];
    return a;
}

struct Piece {
    Counts counts;
    Family family;
};

class Enumeration {
    FrequencyBounds bounds;
    const Counts ones = Counts(8, 1);
    std::set<Columns> boxes;
    int profiles = 0, raw_boxes = 0;

    // A word with an eight-letter permutation at one end. Project to a set of
    // size k. Deleting the endpoint permutation must leave all (k-2)-orders.
    bool with_permutation(Counts subset) {
        if (!bounds.passes(subset)) return false;
        if (subset.size() <= 2) return true;
        std::sort(subset.begin(), subset.end());
        subset.resize(subset.size() - 2);
        for (int& x : subset) --x;
        return bounds.passes(subset);
    }

    Family signature(const Counts& counts, bool permutation_end) {
        Family result;
        for (int mask = 0; mask <= full; ++mask) {
            Counts subset;
            for (int i = 0; i < 8; ++i)
                if (mask & (1 << i)) subset.push_back(counts[i]);
            result[mask] = permutation_end ? with_permutation(subset) : bounds.passes(subset);
        }
        return result;
    }

    Family complementary_demands(const Counts& counts) {
        Family feasible = signature(counts, true), demands;
        for (int s = 0; s <= full; ++s)
            if (!feasible[s]) demands.set(full ^ s);
        return demands;
    }

    // The concatenation GQ has to contain every ordered k-subset. Q ends in
    // a permutation. Test every way to force the middle letter a of A a B.
    bool can_concatenate(const Counts& g, const Counts& q, int k) {
        Family left = signature(g, false), right = signature(q, true);
        for (int s = 1; s <= full; ++s) {
            if (__builtin_popcount(static_cast<unsigned>(s)) != k) continue;
            for (int a = 0; a < 8; ++a) {
                if (!(s & (1 << a))) continue;
                int remaining = s ^ (1 << a);
                for (int A = remaining;; A = (A - 1) & remaining) {
                    int B = remaining ^ A;
                    bool in_g = g[a] > 0 && left[A];
                    bool in_q = q[a] > 0 && right[B] &&
                        (q[a] > 1 || __builtin_popcount(static_cast<unsigned>(B)) <= 1);
                    if (!in_g && !in_q) return false;
                    if (!A) break;
                }
            }
        }
        return true;
    }

    std::vector<Piece> outer_pieces(const Counts& totals) {
        std::vector<Piece> pieces;
        Counts c = ones;
        auto visit = [&](auto& self, int first, int length) -> void {
            Counts six = subtract(totals, c);
            std::sort(six.begin(), six.end());
            six.resize(6);
            if (!with_permutation(six)) return;
            pieces.push_back({c, signature(c, true)});
            if (length == 20) return;
            for (int i = first; i < 8; ++i) {
                ++c[i];
                self(self, i, length + 1);
                --c[i];
            }
        };
        visit(visit, 0, 8);
        return pieces;
    }

    std::vector<Counts> compatible_pieces(const Counts& z, const Counts& q,
                                          const std::vector<Piece>& pieces) {
        Family needed = complementary_demands(q);
        std::vector<Counts> compatible;
        for (const auto& piece : pieces) {
            if (!contained(needed, piece.family)) continue;
            Counts g = subtract(z, piece.counts);
            if (*std::min_element(g.begin(), g.end()) >= 0 && can_concatenate(g, q, 6))
                compatible.push_back(piece.counts);
        }
        return compatible;
    }

    void record(const Counts& c, const Counts& l, const Counts& d, const Counts& r) {
        Columns forward{}, reverse{};
        for (int a = 0; a < 8; ++a) {
            forward[a] = {1, c[a]-1, l[a]-c[a], r[a]-d[a], d[a]-1, 1};
            std::reverse_copy(forward[a].begin(), forward[a].end(), reverse[a].begin());
        }
        std::sort(forward.begin(), forward.end());
        std::sort(reverse.begin(), reverse.end());
        boxes.insert(std::min(forward, reverse));
        ++raw_boxes;
    }

    void inspect(const Counts& v) {
        if (!bounds.passes(v)) return;
        ++profiles;
        if (v.front() != 5) throw std::logic_error("unhandled pivot frequency");
        Counts totals(v.begin()+1, v.end());
        auto pieces = outer_pieces(totals);
        std::vector<Family> maximal;
        for (const auto& piece : pieces) keep_maximal(maximal, piece.family);
        Counts l = subtract(totals, ones), r = l;
        // Until a count is assigned both sides use the individual upper bound.
        auto viable = [&](const Counts& side) {
            Family demand = complementary_demands(side);
            return std::any_of(maximal.begin(), maximal.end(),
                [&](const Family& f) { return contained(demand, f); });
        };
        auto split = [&](auto& self, int i) -> void {
            if (i == 8) {
                if (!can_concatenate(subtract(l, ones), r, 8)) return;
                bool unique_pivot = totals.front() > 5;
                if (unique_pivot && !can_concatenate(subtract(r, ones), l, 8)) return;
                auto front = compatible_pieces(l, r, pieces);
                if (front.empty()) return;
                auto back = compatible_pieces(r, l, pieces);
                if (!unique_pivot && !back.empty())
                    throw std::logic_error("surviving template with a second rare letter");
                for (const auto& c : front)
                    for (const auto& d : back) record(c, l, d, r);
                return;
            }
            int low = i && totals[i] == totals[i-1] ? l[i-1] : 1;
            for (int a = low; a < totals[i]; ++a) {
                l[i] = a;
                r[i] = totals[i] - a;
                if (viable(l) && viable(r)) self(self, i+1);
            }
            l[i] = r[i] = totals[i] - 1;
        };
        split(split, 0);
    }

public:
    void run() {
        Counts prefix;
        auto visit = [&](const Counts& v) { inspect(v); };
        partitions(9, 65, 1, prefix, visit);
        for (const auto& box : boxes) {
            for (const auto& column : box)
                for (int v : column) std::cout << v << ' ';
            std::cout << '\n';
        }
        std::cerr << profiles << " profiles, " << raw_boxes << " labeled count arrays, "
                  << boxes.size() << " templates\n";
    }
};

int main() {
    Enumeration().run();
}
