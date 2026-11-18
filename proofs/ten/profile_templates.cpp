// Necessary endpoint shapes for universal words with a given frequency vector.
#include "profile_capacity.hpp"
#include "windows.hpp"
#include <iostream>
#include <set>

using windows::Row;
using length82::Counts;
using length82::ProfileCapacity;

struct End {
    int last;
    Counts counts, forces;
};

struct Templates {
    ProfileCapacity bounds;

    std::vector<End> possible_ends(const Counts& v) {
        int n=v.size(), full=(1<<n)-1, length=std::accumulate(v.begin(),v.end(),0);
        std::vector<End> ends;
        for (int x=0;x<n;++x) {
            int slack=length-v[x]-(n-1)-length82::length_lower_bound[n-1];
            if (slack<0) continue;
            End e{x,Counts(n,1),{}};
            auto visit=[&](auto& self,int a,int left)->void {
                if (a<n) {
                    int extra=a==x ? 0 : std::min(left,v[a]-1);
                    for (int k=0;k<=extra;++k) {
                        e.counts[a]=1+k;
                        self(self,a+1,left-k);
                    }
                    return;
                }
                Counts tail=v;
                int d=0;
                for (int i=0;i<n;++i) {
                    tail[i]-=e.counts[i];
                    if (e.counts[i]>1) d|=1<<i;
                }
                e.forces=length82::demands(full,x,d);
                for (int s:e.forces) if (!bounds.passes(length82::selected(tail,full^s))) return;
                ends.push_back(e);
            };
            visit(visit,0,slack);
        }
        return ends;
    }

    static std::vector<std::array<int,5>> columns(const Counts& v,const End& l,const End& r) {
        std::vector<std::array<int,5>> answer;
        for (size_t a=0;a<v.size();++a)
            answer.push_back({v[a],l.last==static_cast<int>(a),l.counts[a],
                               r.last==static_cast<int>(a),r.counts[a]});
        std::sort(answer.begin(),answer.end());
        return answer;
    }

    void run(const Counts& v) {
        const int n=v.size(), full=(1<<n)-1;
        if (*std::min_element(v.begin(),v.end())<2)
            throw std::runtime_error("profile generator needs two copies of each symbol");
        if (!bounds.passes(v)) return;
        auto ends=possible_ends(v);
        std::set<std::vector<std::array<int,5>>> seen;
        for (size_t i=0;i<ends.size();++i) for (size_t j=0;j<=i;++j) {
            const End &l=ends[i], &r=ends[j];
            auto key=std::min(columns(v,l,r),columns(v,r,l));
            if (!seen.insert(key).second) continue;
            Counts middle=v;
            for (int a=0;a<n;++a) middle[a]-=l.counts[a]+r.counts[a];
            if (*std::min_element(middle.begin(),middle.end())<0) continue;
            bool ok=true;
            for (int p:l.forces) {
                for (int q:r.forces) if (!(p&q) && !bounds.passes(length82::selected(middle,full^p^q))) {
                    ok=false;
                    break;
                }
                if (!ok) break;
            }
            if (!ok) continue;

            std::vector<Row> rows(5);
            for (int a=0;a<n;++a) {
                rows[0][a]=l.counts[a]-(l.last==a);
                rows[1][a]=l.last==a;
                rows[2][a]=middle[a];
                rows[3][a]=r.last==a;
                rows[4][a]=r.counts[a]-(r.last==a);
            }
            windows::BasicWindows<ProfileCapacity> w(bounds,rows);
            if (!w.possible(2,4,full^(1<<l.last)) || !w.possible(0,2,full^(1<<r.last))) continue;
            if (l.last!=r.last && !w.possible(2,2,full^(1<<l.last)^(1<<r.last))) continue;
            if (!w.check(0,4,{full})) continue;
            std::cout<<5<<' ';
            for (const auto& row:rows) for (int c:row) std::cout<<c<<' ';
            // All three regions are necessary, independently of their pivot.
            std::cout<<3<<' '<<l.last<<" 0 4 "<<full<<" -1 2 4 "<<(full^(1<<l.last))
                     <<" -1 0 2 "<<(full^(1<<r.last))<<'\n';
        }
    }
};

int main(int argc,char**argv) {
    if (argc!=3) return 2;
    const int n=std::stoi(argv[2]);
    if (n<3 || n>9) return 2;
    Templates t;
    t.bounds.load(argv[1],n);
    int first;
    while (std::cin>>first) {
        Counts v(n);
        v[0]=first;
        for (int i=1;i<n;++i) if (!(std::cin>>v[i])) return 2;
        t.run(v);
    }
}
