// Enumerate the case in which every symbol occurs at least seven times.
#include "windows.hpp"
#include <iostream>
#include <set>
using namespace windows;

Row singleton(int a) {
    Row r{};
    r[a]=1;
    return r;
}

// The distinguished opening letter has index 9. Equal-count symbols can
// be renamed provided the previously chosen roles retain their labels.
bool representative(int a, int fixed, const Row& total) {
    if (fixed & (1<<a)) return true;
    for (int b=0; b<a; ++b)
        if (!(fixed & (1<<b)) && total[b]==total[a]) return false;
    return true;
}

struct Search {
    FrequencyBounds bounds;
    int profiles=0, templates=0;

    void inspect(const Counts& counts) {
        if (counts.front()!=7) return;
        // Necessary deletion tests, with the last new symbol put last in
        // decreasing order of frequency, as in the nine-letter proof.
        for (int j=0; j<10; ++j) {
            Counts tail;
            for (int i=0; i<10; ++i)
                if (i!=j) tail.push_back(counts[i]-(i>j));
            if (std::accumulate(tail.begin(),tail.end(),0)<66 || !bounds.passes(tail)) return;
        }
        Counts reduced(counts.begin()+1,counts.end());
        for (int& v:reduced) --v;
        if (!bounds.passes(reduced)) return;
        Counts least=reduced;
        least.push_back(6);
        std::sort(least.begin(),least.end());
        least.resize(8);
        if (!bounds.passes(least)) return;
        ++profiles;

        const int x=9;
        Row total{};
        std::copy(counts.begin()+1,counts.end(),total.begin());
        total[x]=7;
        for (int z=0; z<10; ++z) {
            if (total[z]!=7 || !representative(z,1<<x,total)) continue;
            for (int y=0; y<9; ++y) {
                if (total[y]!=7 || !representative(y,(1<<x)|(1<<z),total)) continue;
                for (int u=0; u<10; ++u) {
                    if (u==z || total[u]!=7 || !representative(u,(1<<x)|(1<<z)|(1<<y),total)) continue;
                    test_orders(total,x,y,u,z);
                }
            }
        }
    }

    void test_orders(const Row& total, int x, int y, int u, int z) {
        Row left{}, right{};
        left.fill(1);
        right.fill(1);
        left[x]=right[z]=0;
        Row second=left, penultimate=right;
        second[y]=penultimate[u]=0;
        for (int i=0; i<=6; ++i) for (int j=0; j<=6; ++j) {
            second[x]=i;
            penultimate[z]=j;
            std::vector<Row> rows={left,singleton(x),second,singleton(y),total,
                                   singleton(u),penultimate,singleton(z),right};
            for (int a=0; a<10; ++a)
                for (int k=0; k<9; ++k)
                    if (k!=4) rows[4][a]-=rows[k][a];
            if (*std::min_element(rows[4].begin(),rows[4].end())<0) continue;
            Windows w(bounds,rows);
            if (!w.possible(4,8,all^(1<<x)^(1<<y)) || !w.possible(0,4,all^(1<<z)^(1<<u))) continue;
            if (!w.possible(2,8,all^(1<<x)) || !w.possible(0,6,all^(1<<z)) || !w.universal()) continue;
            for (const Row& row:rows) for (int v:row) std::cout<<v<<' ';
            std::cout<<'\n';
            ++templates;
        }
    }
};

int main() {
    Search search;
    Counts prefix;
    auto visit=[&](const Counts& c){ search.inspect(c); };
    supersequence::partitions(10,82,7,prefix,visit);
    std::cerr<<search.profiles<<" count profiles, "<<search.templates<<" seven-copy templates\n";
}
