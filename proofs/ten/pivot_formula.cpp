// Generate an ordering CNF for a word specified as a list of multisets.
// The copies of one chosen letter give an exact test by complementary cuts.
#include "windows.hpp"
#include <iostream>
#include <stdexcept>
#include <string>

using namespace windows;
using Clause = std::vector<int>;

class PivotFormula {
    static constexpr int yes=1, no=-1;
    const std::vector<Row>& blocks;
    Windows windows;
    std::vector<int> block_of, letter;
    std::array<std::vector<int>,10> copies;
    std::vector<std::vector<int>> before;
    std::array<std::vector<int>,2> memo;
    std::vector<Clause> clauses;
    int variables=1;  // ±1 are constants and never appear in a clause.

    int first_block=0, last_block=0;

    void add(Clause clause) {
        if (std::find(clause.begin(),clause.end(),yes)!=clause.end()) return;
        clause.erase(std::remove(clause.begin(),clause.end(),no),clause.end());
        clauses.push_back(std::move(clause));
    }

    int conjunction(int a,int b) {
        if (a==no || b==no) return no;
        if (a==yes) return b;
        if (b==yes) return a;
        int both=++variables;
        clauses.push_back({-both,a});
        clauses.push_back({-both,b});
        return both;
    }

    // A positive return literal requires universality strictly before the
    // endpoint in the chosen reading direction. Each possible last letter
    // needs an occurrence after a universal prefix on the other letters.
    int universal(bool reverse,int endpoint,int mask) {
        if (!mask) return yes;
        int& result=memo[reverse][1024*endpoint+mask];
        if (result) return result;
        int block=block_of[endpoint];
        int lo=reverse ? block : first_block;
        int hi=reverse ? last_block : block;
        if (!windows.possible(lo,hi,mask)) return result=no;
        std::vector<Clause> requirements;
        for (int m=mask;m;m&=m-1) {
            int a=__builtin_ctz(static_cast<unsigned>(m)), smaller=mask^(1<<a);
            const auto& group=copies[a];
            std::vector<std::pair<int,int>> predecessors;
            for (size_t j=0;j<group.size();++j) {
                int q=group[reverse ? group.size()-1-j : j];
                if (block_of[q]<first_block || block_of[q]>last_block) continue;
                int relation=reverse ? before[endpoint][q] : before[q][endpoint];
                if (relation==no) continue;
                // A later guaranteed occurrence subsumes all earlier ones.
                if (relation==yes) predecessors.clear();
                predecessors.emplace_back(q,relation);
            }
            Clause choices;
            bool guaranteed=false;
            for (auto [q,relation] : predecessors) {
                int option=conjunction(relation,universal(reverse,q,smaller));
                if (option==yes) { guaranteed=true; break; }
                if (option!=no) choices.push_back(option);
            }
            if (guaranteed) continue;
            if (choices.empty()) return result=no;
            requirements.push_back(std::move(choices));
        }
        if (requirements.empty()) return result=yes;
        if (requirements.size()==1 && requirements.front().size()==1)
            return result=requirements.front().front();
        result=++variables;
        for (auto& choice : requirements) {
            choice.push_back(-result);
            clauses.push_back(std::move(choice));
        }
        return result;
    }

public:
    PivotFormula(FrequencyBounds& bounds,const std::vector<Row>& rows)
        : blocks(rows),windows(bounds,rows) {
        for (size_t j=0;j<rows.size();++j)
            for (int a=0;a<10;++a)
                for (int k=0;k<rows[j][a];++k) {
                    copies[a].push_back(static_cast<int>(letter.size()));
                    letter.push_back(a);
                    block_of.push_back(j);
                }
        const int n=letter.size();
        before.assign(n,std::vector<int>(n,no));
        for (int i=0;i<n;++i) for (int j=i+1;j<n;++j) {
            before[i][j]=(block_of[i]==block_of[j] && letter[i]!=letter[j]) ? ++variables : yes;
            before[j][i]=-before[i][j];
        }
        for (int i=0;i<n;++i)
            for (int j=i+1;j<n && block_of[j]==block_of[i];++j)
                for (int k=j+1;k<n && block_of[k]==block_of[j];++k) {
                    add({-before[i][j],-before[j][k],before[i][k]});
                    add({before[i][j],before[j][k],-before[i][k]});
                }
        for (auto& direction : memo) direction.resize(n*1024);
    }

    void require_all(int mask,int pivot_letter,int lo,int hi) {
        if (lo<0 || hi<lo || hi>=static_cast<int>(blocks.size()) || mask<=0 || mask>all)
            throw std::runtime_error("invalid universality region");
        first_block=lo;
        last_block=hi;
        for (auto& direction:memo) std::fill(direction.begin(),direction.end(),0);
        if (pivot_letter<0) {
            int least=1000;
            for (int a=0; a<10; ++a) if (mask & (1<<a)) {
                int count=0;
                for (int t:copies[a]) if (lo<=block_of[t] && block_of[t]<=hi) ++count;
                if (count<least) { least=count; pivot_letter=a; }
            }
        }
        if (pivot_letter>=10 || !(mask & (1<<pivot_letter)))
            throw std::runtime_error("invalid pivot");
        std::vector<int> piv;
        for (int t:copies[pivot_letter])
            if (lo<=block_of[t] && block_of[t]<=hi) piv.push_back(t);
        if (piv.empty()) { add({}); return; }
        int rest=mask^(1<<pivot_letter);
        add({universal(true,piv.front(),rest)});
        add({universal(false,piv.back(),rest)});
        for (size_t i=1;i<piv.size();++i) {
            for (int s=rest;;s=(s-1)&rest) {
                int prefix=universal(false,piv[i-1],s);
                if (prefix!=yes) add({prefix,universal(true,piv[i],rest^s)});
                if (!s) break;
            }
        }
    }

    void write_selected() const {
        int count;
        if (!(std::cin>>count) || count<0) throw std::runtime_error("invalid proof reference count");
        std::vector<size_t> ids(count);
        for (size_t& id:ids)
            if (!(std::cin>>id) || !id || id>clauses.size()) throw std::runtime_error("invalid clause id");
        // The request can exceed a pipe buffer. Consume it before writing
        // any response, so the encoder and its client can never block each other.
        std::cout<<clauses.size()<<'\n';
        for (size_t id:ids) {
            for (int literal : clauses[id-1]) std::cout<<literal<<' ';
            std::cout<<"0\n";
        }
        std::cout.flush();
    }

    void write() const {
        std::cout<<"p cnf "<<variables<<' '<<clauses.size()<<'\n';
        for (const auto& clause : clauses) {
            for (int literal : clause) std::cout<<literal<<' ';
            std::cout<<"0\n";
        }
        std::cout.flush();
    }
};

int main(int argc,char** argv) {
    const bool regions=argc>=2 && std::string(argv[1])=="regions";
    const int options=regions ? 2 : 3;
    const bool selected=argc==options+1 && std::string(argv[options])=="selected";
    if (argc!=options && !selected) return 2;
    std::ios::sync_with_stdio(false);
    FrequencyBounds bounds;
    int number;
    while (std::cin>>number) {
        if (number<1 || number>82) throw std::runtime_error("invalid block count");
        std::vector<Row> rows(number);
        for (auto& row:rows) for (int& v:row)
            if (!(std::cin>>v) || v<0) throw std::runtime_error("invalid block");
        PivotFormula formula(bounds,rows);
        if (regions) {
            int q;
            if (!(std::cin>>q) || q<1) throw std::runtime_error("invalid region count");
            while (q--) {
                int pivot,lo,hi,mask;
                if (!(std::cin>>pivot>>lo>>hi>>mask)) throw std::runtime_error("invalid region");
                formula.require_all(mask,pivot,lo,hi);
            }
        } else {
            formula.require_all(std::stoi(argv[1]),std::stoi(argv[2]),0,number-1);
        }
        if (selected) formula.write_selected();
        else formula.write();
    }
}
