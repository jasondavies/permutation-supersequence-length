// Necessary frequency tests for words of at most 65 letters on at most nine symbols.
#pragma once

#include <algorithm>
#include <array>
#include <bitset>
#include <cstdint>
#include <numeric>
#include <stdexcept>
#include <unordered_map>
#include <vector>

namespace supersequence {
using Counts = std::vector<int>;
using Family = std::bitset<256>;
constexpr int limit = 65;
// Index nine deliberately has no input lower bound.
constexpr std::array<int, 10> optimum{0, 1, 3, 7, 12, 19, 28, 39, 52, 0};

template<class Visitor>
void partitions(int slots, int total, int minimum, Counts& prefix, Visitor& visit) {
    if (slots == 1) {
        if (total >= minimum) {
            prefix.push_back(total);
            visit(prefix);
            prefix.pop_back();
        }
        return;
    }
    for (int x = minimum; slots * x <= total; ++x) {
        prefix.push_back(x);
        partitions(slots - 1, total - x, x, prefix, visit);
        prefix.pop_back();
    }
}

inline bool contained(const Family& small, const Family& large) {
    return (small & ~large).none();
}

inline void keep_maximal(std::vector<Family>& families, const Family& value) {
    for (const auto& existing : families)
        if (contained(value, existing)) return;
    families.erase(std::remove_if(families.begin(), families.end(),
        [&](const Family& existing) { return contained(existing, value); }), families.end());
    families.push_back(value);
}

class FrequencyBounds {
    // Minimum required total frequency of the other letters, indexed by
    // alphabet size and by the frequency of a least frequent letter.
    std::array<std::array<int, limit + 1>, 10> other_minimum{};
    std::unordered_map<std::uint64_t, bool> cache;

    void build_dimension(int m) {
        const int endpoint = optimum[m];
        const int full = (1 << m) - 1;
        std::vector<std::vector<Family>> by_length(endpoint + 1);
        std::vector<bool> computed(endpoint + 1);
        auto signatures = [&](int length) -> const std::vector<Family>& {
            if (!computed[length]) {
                Counts prefix;
                auto visit = [&](const Counts& values) {
                    Family signature;
                    for (int mask = 0; mask <= full; ++mask)
                        signature[mask] = projected(values, mask);
                    keep_maximal(by_length[length], signature);
                };
                partitions(m, length, 0, prefix, visit);
                computed[length] = true;
            }
            return by_length[length];
        };
        auto compatible = [&](int p, int q) {
            for (const auto& left : signatures(p)) {
                Family needed;
                for (int mask = 0; mask <= full; ++mask)
                    if (!left[mask]) needed.set(full ^ mask);
                for (const auto& right : signatures(q))
                    if (contained(needed, right)) return true;
            }
            return false;
        };
        std::vector<int> required_suffix(endpoint + 1);
        int q = endpoint;
        for (int p = 0; p <= endpoint; ++p) {
            while (q > 0 && compatible(p, q - 1)) --q;
            required_suffix[p] = q;
        }
        for (int copies = 1; copies <= limit; ++copies) {
            int& required = other_minimum[m + 1][copies];
            required = limit + 1;
            for (int t = endpoint; t <= limit; ++t) {
                int before = t - endpoint;
                for (int j = 1; j < copies && before < endpoint; ++j)
                    before = t - required_suffix[before];
                if (before >= endpoint) {
                    required = t;
                    break;
                }
            }
        }
    }

public:
    FrequencyBounds() {
        // A dimension uses only frequency tests already built for smaller alphabets.
        for (int m = 1; m <= 8; ++m) build_dimension(m);
    }

    bool passes(Counts counts) {
        if (counts.empty()) return true;
        std::sort(counts.begin(), counts.end());
        if (counts.front() < 1) return false;
        if (counts.size() > 9 || counts.back() > limit)
            throw std::out_of_range("frequency test outside certified domain");
        std::uint64_t key = 0;
        for (int x : counts) key = (key << 7) | (x + 1);
        if (auto found = cache.find(key); found != cache.end()) return found->second;
        int n = static_cast<int>(counts.size());
        int total = std::accumulate(counts.begin(), counts.end(), 0);
        int least = counts.front();
        bool feasible = total >= optimum[n] && total - least >= other_minimum[n][least];
        for (int j = 0; feasible && j < n; ++j) {
            Counts remaining;
            for (int i = 0; i < n; ++i)
                if (i != j) remaining.push_back(counts[i] - (i > j));
            feasible = passes(remaining);
        }
        cache.emplace(key, feasible);
        return feasible;
    }

    bool projected(const Counts& counts, int mask) {
        Counts subset;
        for (int i = 0; i < static_cast<int>(counts.size()); ++i)
            if (mask & (1 << i)) subset.push_back(counts[i]);
        return passes(subset);
    }
};
} // namespace supersequence
