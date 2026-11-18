// Enumerate all pairs of capacity vectors which can cover complementary subsets.
#include "../shared/frequency_bounds.hpp"
#include <iostream>
#include <map>
#include <string>

using namespace supersequence;
using Signature = std::bitset<512>;

struct Profile {
    Counts counts;
    Signature feasible;
};

class Catalog {
    FrequencyBounds bounds;
    bool permutation_end;
    std::map<Counts, bool> cache;

public:
    explicit Catalog(bool permutation_end) : permutation_end(permutation_end) {}

    bool passes(Counts v) {
        std::sort(v.begin(), v.end());
        auto [it, inserted] = cache.try_emplace(v);
        if (inserted) {
            bool ok = bounds.passes(v);
            if (v.size() == 9 && std::accumulate(v.begin(), v.end(), 0) < 66)
                ok = false;
            if (ok && permutation_end && v.size() >= 3) {
                v.resize(v.size()-2);
                for (int& x : v) --x;
                ok = bounds.passes(v);
            }
            it->second = ok;
        }
        return it->second;
    }

    bool projected(const Counts& v, int mask) {
        Counts sub;
        for (int i=0; i<9; ++i)
            if (mask & (1<<i)) sub.push_back(v[i]);
        return passes(sub);
    }

    std::vector<Profile> profiles(int length) {
        std::vector<Profile> result;
        Counts partial;
        auto visit = [&](const Counts& v) {
            Signature f;
            for (int s=0; s<512; ++s) f[s] = projected(v, s);
            result.push_back({v, f});
        };
        partitions(9, length, 1, partial, visit);
        return result;
    }

    void enumerate(int p, int q) {
        auto left = profiles(p), right = profiles(q);
        for (const auto& l : left) {
            Signature required;
            std::vector<int> maximal;
            for (int s=511; s>0; --s) {
                if (l.feasible[511^s]) continue;
                required.set(s);
                if (std::none_of(maximal.begin(), maximal.end(), [s](int other) {
                        return (s & other) == s;
                    })) maximal.push_back(s);
            }
            for (const auto& r : right) {
                // The sorting exchange is only a preliminary rejection. Try all
                // distinct relative alignments for surviving sorted pairs.
                if ((required & ~r.feasible).any()) continue;
                Counts aligned(9);
                auto assign = [&](auto& self, int i, int used) -> void {
                    if (i == 9) {
                        for (int x : l.counts) std::cout << x << ' ';
                        for (int x : aligned) std::cout << x << ' ';
                        std::cout << '\n';
                        return;
                    }
                    for (int j=0; j<9; ++j) {
                        if (used & (1<<j)) continue;
                        if (j && r.counts[j] == r.counts[j-1] && !(used & (1<<(j-1)))) continue;
                        if (i && l.counts[i] == l.counts[i-1] && r.counts[j] < aligned[i-1]) continue;
                        aligned[i] = r.counts[j];
                        bool ok = std::all_of(maximal.begin(), maximal.end(), [&](int mask) {
                            return mask >= (2<<i) || projected(aligned, mask);
                        });
                        if (ok) self(self, i+1, used | (1<<j));
                    }
                };
                assign(assign, 0, 0);
            }
        }
    }
};

int main(int argc, char** argv) {
    if (argc != 4) return 2;
    const std::string mode(argv[3]);
    const int p = std::stoi(argv[1]), q = std::stoi(argv[2]);
    // In positive mode the caller supplies a separate proof that both
    // sides use all nine symbols, even when one budget reaches 52.
    if (mode != "positive" && std::max(p,q) >= 52)
        throw std::invalid_argument("need proof of positive counts");
    if (mode != "positive" && mode != "free" && mode != "perm") return 2;
    Catalog(mode == "perm").enumerate(p, q);
}
