// Enumerate the count profiles and two outer blocks when the minimum is six.
// Symbols with equal counts are interchangeable. Each column records its
// total and whether it is the last new or the duplicate at either end.
#include "windows.hpp"
#include "profile_capacity.hpp"
#include <iostream>
#include <set>

using namespace windows;
using Pattern = std::array<std::array<int,5>,10>;

struct End {
    int last_new, duplicate;
    Row counts;
    std::vector<int> forced;
};

template<class Bounds>
bool fits(Bounds& bounds, const Row& counts, int mask) {
    Counts restricted;
    for (int a=0;a<10;++a) if (mask&(1<<a)) restricted.push_back(counts[a]);
    return (restricted.size()!=9 || std::accumulate(restricted.begin(),restricted.end(),0)>=66)
        && bounds.passes(restricted);
}

Pattern columns(const Row& total, const End& left, const End& right) {
    Pattern result;
    for (int i=0;i<10;++i) {
        result[i]={total[i], i==left.last_new, i==left.duplicate,
                   i==right.last_new, i==right.duplicate};
    }
    std::sort(result.begin(),result.end());
    return result;
}

template<class Bounds>
std::vector<End> possible_ends(Bounds& bounds, const Row& total) {
    std::vector<End> result;
    for (int x=0;x<10;++x) {
        if (total[x]>7) continue;
        for (int d=-1;d<(total[x]==6 ? 10 : 0);++d) {
            if (d==x) continue;
            End end{x,d,{}, {1<<x}};
            end.counts.fill(1);
            if (d>=0) ++end.counts[d];
            Row tail=total;
            for (int i=0;i<10;++i) tail[i]-=end.counts[i];
            if (!fits(bounds,tail,all^(1<<x))) continue;
            bool ok=true;
            for (int a=0;a<10;++a) for (int b=a+1;b<10;++b) {
                if (a==x || b==x || a==d || b==d) continue;
                int pair=(1<<a)|(1<<b);
                if (!fits(bounds,tail,all^pair)) ok=false;
                end.forced.push_back(pair);
            }
            if (ok) result.push_back(end);
        }
    }
    return result;
}

template<class Bounds>
void enumerate(Bounds& bounds) {
    Counts prefix;
    size_t entry_count=0;
    std::set<Pattern> patterns;
    std::set<Row> profiles;
    auto visit=[&](const Counts& counts) {
        if (counts.front()!=6) return;
        for (int j=0;j<10;++j) {
            Counts tail;
            for (int i=0;i<10;++i)
                if (i!=j) tail.push_back(counts[i]-(i>j));
            if (std::accumulate(tail.begin(),tail.end(),0)<66 || !bounds.passes(tail)) return;
        }
        ++entry_count;
        Row total;
        std::copy(counts.begin(),counts.end(),total.begin());
        auto ends=possible_ends(bounds,total);
        std::set<Pattern> tested;
        for (size_t i=0;i<ends.size();++i) for (size_t j=i;j<ends.size();++j) {
            const End& left=ends[i];
            const End& right=ends[j];
            auto key=std::min(columns(total,left,right),columns(total,right,left));
            if (!tested.insert(key).second) continue;
            Row middle=total;
            for (int a=0;a<10;++a) middle[a]-=left.counts[a]+right.counts[a];
            bool ok=true;
            for (int l : left.forced) for (int r : right.forced)
                if (!(l&r) && !fits(bounds,middle,all^l^r)) ok=false;
            if (ok) { patterns.insert(key); profiles.insert(total); }
        }
    };
    supersequence::partitions(10,82,6,prefix,visit);
    for (const auto& p : patterns) {
        for (const auto& col : p) for (int v : col) std::cout<<v<<' ';
        std::cout<<'\n';
    }
    std::cerr<<entry_count<<" entry profiles, "<<profiles.size()<<" surviving profiles, "
             <<patterns.size()<<" endpoint patterns\n";
}


int main(int argc,char**argv) {
    if (argc==1) {
        FrequencyBounds bounds;
        enumerate(bounds);
    } else if (argc==2) {
        length82::ProfileCapacity bounds;
        bounds.load(argv[1],10);
        enumerate(bounds);
    } else return 2;
}
