#pragma once
#include "../shared/frequency_bounds.hpp"
#include <fstream>
#include <map>
#include <sstream>
#include <string>

namespace length82 {
using supersequence::Counts;
constexpr std::array<int,10> length_lower_bound{0,1,3,7,12,19,28,39,52,66};

inline Counts selected(const Counts& counts,int mask) {
    Counts result;
    for (int a=0;a<static_cast<int>(counts.size());++a)
        if (mask&(1<<a)) result.push_back(counts[a]);
    return result;
}

// If the last new letter of a covering block is x, every permutation
// requested after x must fit beyond the block. Two singletons in the
// block also have a missing order, giving another suffix requirement.
inline Counts demands(int mask,int x,int repeated) {
    Counts result{1<<x};
    int singles=mask & ~(repeated|(1<<x));
    for (int i=singles;i;i&=i-1)
        for (int j=i^(i&-i);j;j&=j-1)
            result.push_back((i&-i)|(j&-j));
    return result;
}

class ProfileCapacity {
    supersequence::FrequencyBounds basic;
    std::array<std::vector<Counts>,10> excluded;
    std::unordered_map<std::uint64_t,bool> memo;

    bool two_ends(const Counts& counts,int length) {
        struct End { int last, repeated; Counts forces; };
        const int n=counts.size(), full=(1<<n)-1;
        std::vector<End> ends;
        for (int x=0;x<n;++x) {
            int slack=length-counts[x]-(n-1)-length_lower_bound[n-1];
            if (slack<0) continue;
            if (counts[x]==1 && length>=2*length_lower_bound[n-1]+1) return true;
            for (int d=0;d<=full;++d) {
                if ((d&(1<<x)) || __builtin_popcount(static_cast<unsigned>(d))>slack) continue;
                Counts tail=counts;
                for (int i=0;i<n;++i) tail[i]-=1+((d>>i)&1);
                auto forces=demands(full,x,d);
                bool possible=true;
                for (int a:forces) if (!passes(selected(tail,full^a))) { possible=false; break; }
                if (possible) ends.push_back({x,d,std::move(forces)});
            }
        }
        for (size_t i=0;i<ends.size();++i) for (size_t j=0;j<=i;++j) {
            const auto& a=ends[i];
            const auto& b=ends[j];
            if (a.last==b.last && counts[a.last]<2) continue;
            Counts middle=counts;
            for (int t=0;t<n;++t) middle[t]-=2+((a.repeated>>t)&1)+((b.repeated>>t)&1);
            if (*std::min_element(middle.begin(),middle.end())<0) continue;
            bool possible=true;
            for (int l:a.forces) {
                for (int r:b.forces)
                    if (!(l&r) && !passes(selected(middle,full^l^r))) { possible=false; break; }
                if (!possible) break;
            }
            if (possible) return true;
        }
        return false;
    }

public:
    // Only independently verified smaller-dimensional exclusions can be
    // loaded when using this test to certify another frequency profile.
    void load(const std::string& file,int exclusive_dimension) {
        std::ifstream input(file);
        if (!input) throw std::runtime_error("cannot open frequency library");
        std::string line;
        while (std::getline(input,line)) {
            Counts v;
            std::istringstream fields(line);
            int n;
            while (fields>>n) v.push_back(n);
            if (v.empty() || v.size()>9 || !std::is_sorted(v.begin(),v.end()) || v[0]<1)
                throw std::runtime_error("invalid frequency profile");
            if (static_cast<int>(v.size())<exclusive_dimension) excluded[v.size()].push_back(v);
        }
        memo.clear();
    }
    bool passes(Counts v) {
        if (v.empty()) return true;
        std::sort(v.begin(),v.end());
        int n=v.size(),len=std::accumulate(v.begin(),v.end(),0);
        if (v.front()<=0 || len<length_lower_bound.at(n) || !basic.passes(v)) return false;
        if (n<=2) return true;
        std::uint64_t key=0;
        for (int value:v) key=(key<<7)|(value+1);
        if (auto it=memo.find(key);it!=memo.end()) return it->second;
        for (const auto& cap:excluded[n]) {
            bool below=true;
            for (int i=0;i<n;++i) if (v[i]>cap[i]) { below=false; break; }
            if (below) return memo[key]=false;
        }
        for (int j=0;j<n;++j) {
            Counts tail;
            for (int i=0;i<n;++i) if (i!=j) tail.push_back(v[i]-(i>j));
            if (!passes(tail)) return memo[key]=false;
        }
        return memo[key]=len>length_lower_bound[n]+3 || two_ends(v,len);
    }
};
} // namespace length82
