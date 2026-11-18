// Read a compatible (P2,Q3) cut at length 82 and enumerate its possible
// opening gap E, second gap B and third gap G. Leave all of Q3 unordered.
#include "windows.hpp"
#include "profile_capacity.hpp"
#include <fstream>
#include <iostream>
#include <map>
#include <set>

using namespace windows;
using Vector = std::array<int,9>;
using Half = std::array<std::array<int,4>,9>;
using Index = std::map<Vector,std::vector<Vector>>;

bool read(std::istream& in, Vector& v) {
    for (int& x : v) if (!(in >> x)) return false;
    return true;
}

Vector sorted(Vector v) {
    std::sort(v.begin(),v.end());
    return v;
}

int length(const Vector& v) { return std::accumulate(v.begin(),v.end(),0); }

Vector subtract(Vector v, const Vector& other) {
    for (int i=0; i<9; ++i) v[i] -= other[i];
    return v;
}

Vector add(Vector v, const Vector& other) {
    for (int i=0; i<9; ++i) v[i] += other[i];
    return v;
}

Row block(const Vector& v, int pivots=0) {
    Row row{};
    std::copy(v.begin(),v.end(),row.begin());
    row[9]=pivots;
    return row;
}

Index index_by_right(const char* file) {
    std::ifstream in(file);
    if (!in) throw std::runtime_error("missing cut table");
    Index result;
    Vector a,b;
    while (read(in,a)) {
        if (!read(in,b)) throw std::runtime_error("truncated cut table");
        std::array<std::pair<int,int>,9> cols;
        for (int i=0;i<9;++i) cols[i]={b[i],a[i]};
        std::sort(cols.begin(),cols.end());
        for (int i=0;i<9;++i) { b[i]=cols[i].first; a[i]=cols[i].second; }
        result[b].push_back(a);
    }
    return result;
}

// Match the right vector to the prescribed labels. Permute the left
// counts in every way inside each tied group of right counts.
template<class Visitor>
void align(const Vector& right, const Index::value_type& entry, Visitor visit) {
    Vector order{0,1,2,3,4,5,6,7,8};
    std::sort(order.begin(),order.end(),[&](int i,int j){return right[i]<right[j];});
    const auto& [key,options]=entry;
    for (Vector left : options) {
        auto next_group=[&](auto& self,int start)->void {
            if (start==9) {
                Vector out;
                for (int i=0;i<9;++i) out[order[i]]=left[i];
                visit(out);
                return;
            }
            int end=start+1;
            while (end<9 && key[end]==key[start]) ++end;
            do { self(self,end); }
            while (std::next_permutation(left.begin()+start,left.begin()+end));
        };
        next_group(next_group,0);
    }
}

int main(int argc,char** argv) {
    if (argc!=5) return 2;
    // Test both ends of nearly shortest projections. The five-copy branch
    // uses the elementary count bounds alone, with an empty profile library.
    length82::ProfileCapacity bounds;
    Index outer[]={index_by_right(argv[1]),index_by_right(argv[2])};
    Index opposite[]={index_by_right(argv[3]),index_by_right(argv[4])};
    Vector p,q;
    while (read(std::cin,p)) {
        if (!read(std::cin,q)) throw std::runtime_error("missing second side");
        const int left_length=77-length(q), short_length=length(p);
        if ((left_length!=39 && left_length!=40) || (short_length!=25 && short_length!=26))
            throw std::runtime_error("unexpected small cut dimensions");
        const auto& outer_index=outer[26-short_length];
        std::set<Half> kept;
        for (const auto& entry : opposite[left_length-39]) {
            Vector l=entry.first;
            do {
                bool canonical=true;
                for (int i=1;i<9;++i)
                    if (p[i]==p[i-1] && q[i]==q[i-1] && l[i]<l[i-1]) canonical=false;
                if (!canonical) continue;
                const Vector g=subtract(l,p), total=add(l,q);
                if (*std::min_element(g.begin(),g.end())<0 ||
                    *std::min_element(total.begin(),total.end())<5) continue;
                const Vector after_second=add(g,q);
                auto found=outer_index.find(sorted(after_second));
                if (found==outer_index.end()) continue;
                align(after_second,*found,[&](const Vector& e){
                    const Vector b=subtract(p,e), tail=subtract(total,e);
                    if (*std::min_element(b.begin(),b.end())<0 ||
                        !bounds.passes(Counts(tail.begin(),tail.end()))) return;
                    BasicWindows<length82::ProfileCapacity> windows(bounds,{block(e),pivot(),block(b),pivot(),block(g),pivot(),block(q,2)});
                    if (!windows.universal()) return;
                    Half cols;
                    for (int i=0;i<9;++i) cols[i]={e[i],b[i],g[i],q[i]};
                    std::sort(cols.begin(),cols.end());
                    kept.insert(cols);
                });
            } while (std::next_permutation(l.begin(),l.end()));
        }
        for (const auto& half : kept) {
            for (const auto& col : half) for (int v : col) std::cout << v << ' ';
            std::cout << '\n';
        }
    }
}
