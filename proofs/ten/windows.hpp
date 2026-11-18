#pragma once
#include "../shared/frequency_bounds.hpp"

namespace windows {
using supersequence::Counts;
using supersequence::FrequencyBounds;
using Row = std::array<int,10>;
constexpr int old = 511, all = 1023;
inline Row permutation(bool pivot = false) {
    Row r{};
    r.fill(1);
    r[9] = pivot;
    return r;
}
inline Row pivot() {
    Row r{};
    r[9] = 1;
    return r;
}
inline Row remove_permutation(Row r) {
    for (int i=0; i<9; ++i) --r[i];
    return r;
}

// Each row specifies a multiset with arbitrary order. Tests may use both
// whole endpoint rows, even when the needed letters lie inside those rows.
template<class Bounds>
class BasicWindows {
    Bounds& bounds;
    std::vector<Row> rows, prefix;
    std::vector<signed char> memo;

public:
    bool possible(int lo, int hi, int mask) {
        if (!mask) return true;
        auto& result = memo[(lo*rows.size()+hi)*1024+mask];
        if (result) return result > 0;
        result = -1;
        Counts counts;
        for (int a=0; a<10; ++a) {
            if (!(mask & (1<<a))) continue;
            int n = prefix[hi+1][a]-prefix[lo][a];
            if (!n) return false;
            counts.push_back(n);
        }
        if (counts.size()==9 && std::accumulate(counts.begin(), counts.end(), 0)<66) return false;
        if (counts.size()<10 && !bounds.passes(counts)) return false;
        if (lo<hi) for (int a=0; a<10; ++a) {
            if (!(mask & (1<<a))) continue;
            int rest=mask^(1<<a), prev=-1;
            for (int j=lo; j<=hi; ++j) {
                if (!rows[j][a]) continue;
                if (prev<0) {
                    if (!possible(j,hi,rest)) return false;
                } else {
                    for (int s=rest;; s=(s-1)&rest) {
                        if (!possible(lo,prev,s) && !possible(j,hi,rest^s)) return false;
                        if (!s) break;
                    }
                }
                prev=j;
            }
            if (prev<0 || !possible(lo,prev,rest)) return false;
        }
        result=1;
        return true;
    }

    BasicWindows(Bounds& b, std::vector<Row> v) :
        bounds(b), rows(std::move(v)), prefix(rows.size()+1), memo(rows.size()*rows.size()*1024) {
        for (size_t i=0; i<rows.size(); ++i)
            for (int a=0; a<10; ++a) prefix[i+1][a]=prefix[i][a]+rows[i][a];
    }

    bool check(int lo, int hi, const std::vector<int>& required) {
        for (int s : required) if (!possible(lo,hi,s)) return false;
        for (int k=lo; k<=hi; ++k) {
            bool before[10][10]{};
            for (int mask : required) for (int a=0; a<10; ++a) {
                if (!(mask&(1<<a))) continue;
                int prev=k-1;
                while (prev>=lo && !rows[prev][a]) --prev;
                for (int b=0; b<10; ++b) {
                    if (a==b || !(mask&(1<<b))) continue;
                    int next=k+1;
                    while (next<=hi && !rows[next][b]) ++next;
                    int rest=mask^(1<<a)^(1<<b);
                    for (int s=rest;; s=(s-1)&rest) {
                        if ((prev<lo || !possible(lo,prev,s)) &&
                            (next>hi || !possible(next,hi,rest^s))) {
                            if (!rows[k][a] || !rows[k][b]) return false;
                            if (rows[k][a]==1 && rows[k][b]==1) before[a][b]=true;
                            break;
                        }
                        if (!s) break;
                    }
                }
            }
            for (int v=0; v<10; ++v)
                for (int a=0; a<10; ++a)
                    for (int b=0; b<10; ++b) before[a][b] |= before[a][v] && before[v][b];
            for (int a=0; a<10; ++a) if (before[a][a]) return false;
        }
        return true;
    }

    bool universal() { return check(0, static_cast<int>(rows.size())-1, {all}); }
};
using Windows = BasicWindows<FrequencyBounds>;
} // namespace windows
