#include "windows.hpp"
#include "profile_capacity.hpp"
#include <iostream>
#include <stdexcept>
#include <unordered_map>
#include <unordered_set>
using windows::Row;
using length82::Counts;
using FrequencyBounds = length82::ProfileCapacity;
// A positive comparison means that the first occurrence token precedes the
// second. Boolean constants are ±1 and are removed before a clause is stored.
using Clause = std::vector<int>;
struct Extremes {
  std::array<int, 1024> end;
  std::array<Clause, 1024> escape;
};
class OrderingFormula {
  FrequencyBounds &f;
  int n = 0, variable_count = 1, mask;
  std::vector<int> group, letter;
  std::array<std::vector<int>, 10> copies;
  std::vector<std::vector<int>> before;
  std::vector<int> path, position;
  std::vector<Row> prefix_counts;
  Row total{};
  std::vector<Clause> clauses;
  bool learning = false;
  struct Hash {
    size_t operator()(const Clause &c) const {
      size_t h = 1469598103934665603ull;
      for (int v : c) {
        h ^= (unsigned)v;
        h *= 1099511628211ull;
      }
      return h;
    }
  };
  std::unordered_set<Clause, Hash> pending;
  void post(const Clause &c) { clauses.push_back(c); }
  void add(Clause c) {
    if (std::find(c.begin(), c.end(), 1) != c.end())
      return;
    c.erase(std::remove(c.begin(), c.end(), -1), c.end());
    std::sort(c.begin(), c.end());
    c.erase(std::unique(c.begin(), c.end()), c.end());
    if (learning)
      pending.insert(std::move(c));
    else
      post(c);
  }
  // Subsumption and the per-word cap only discard valid clauses.
  void retain_clauses() {
    std::vector<const Clause *> order;
    for (const auto &c : pending)
      order.push_back(&c);
    std::sort(order.begin(), order.end(), [](auto a, auto b) {
      if (a->size() != b->size())
        return a->size() < b->size();
      return *a < *b;
    });
    std::unordered_map<int, std::vector<const Clause *>> first;
    int count = 0;
    for (auto cp : order) {
      const Clause &c = *cp;
      if (c.empty()) {
        post(c);
        break;
      }
      bool sub = false;
      for (int z : c) {
        auto it = first.find(z);
        if (it != first.end())
          for (auto prev : it->second)
            if (std::includes(c.begin(), c.end(), prev->begin(), prev->end())) {
              sub = true;
              break;
            }
        if (sub)
          break;
      }
      if (sub)
        continue;
      post(c);
      count++;
      if (c.size() <= 7)
        first[c.front()].push_back(cp);
      if (count == 3000)
        break;
    }
    pending.clear();
  }
  bool passes(const Row &v, int m) {
    if (!m || m == 1023)
      return true;
    std::array<int, 10> a{};
    int k = 0;
    for (int s = m; s; s &= s - 1) {
      int z = v[__builtin_ctz((unsigned)s)];
      if (z <= 0)
        return false;
      if (z >= 32)
        throw std::runtime_error("frequency outside the five-bit cache key");
      a[k++] = z;
    }
    std::sort(a.begin(), a.begin() + k);
    uint64_t key = 0;
    for (int i = 0; i < k; i++)
      key = (key << 5) | a[i];
    static std::unordered_map<uint64_t, bool> c;
    auto it = c.find(key);
    if (it != c.end())
      return it->second;
    return c[key] = f.passes(Counts(a.begin(), a.begin() + k));
  }
  struct Region {
    int first, last, mask;
  };
  std::vector<Region> regions;
  struct Family {
    int lo, hi;
    std::array<bool, 1024> masks{};
  };
  std::vector<Family> families;
  std::vector<int> remaining_alphabets(const std::vector<int> &family, int x,
                                       int dup) {
    std::array<bool, 1024> set{};
    for (int m : family) {
      if (m & (1 << x))
        set[m ^ (1 << x)] = true;
      int rest = m & ~(1 << x) & ~dup;
      for (int i = rest; i; i &= i - 1)
        for (int j = i ^ (i & -i); j; j &= j - 1)
          set[m ^ (i & -i) ^ (j & -j)] = true;
    }
    std::vector<int> result;
    for (int m = 1023; m; m--)
      if (set[m]) {
        result.push_back(m);
        for (int s = (m - 1) & m; s; s = (s - 1) & m)
          set[s] = false;
      }
    return result;
  }
  void family(int lo, int hi, const std::vector<int> &max) {
    Family f{lo, hi};
    const auto &length_lower_bound = length82::length_lower_bound;
    for (int m : max) {
      for (int s = m; s; s = (s - 1) & m)
        f.masks[s] = true;
      int len = 0;
      for (int q = 0; q < n; q++)
        if (group[q] >= lo && group[q] <= hi && (m >> letter[q] & 1))
          len++;
      // Always encode the full ten-letter region; select shorter regions by slack.
      if ((m == 1023 || len - length_lower_bound[__builtin_popcount((unsigned)m)] <= 5) &&
          std::none_of(regions.begin(), regions.end(), [&](const Region &v) {
            return v.first == lo && v.last == hi && v.mask == m;
          }))
        regions.push_back({lo, hi, m});
    }
    families.push_back(f);
  }
  // Emit missing-order clauses inside a required interval of whole blocks.
  Extremes greedy_endpoints(const Family &f, bool reverse) {
    int begin = 0, end = n;
    auto org = [&](int j) { return path[reverse ? n - 1 - j : j]; };
    while (reverse ? group[org(begin)] > f.hi : group[org(begin)] < f.lo)
      begin++;
    while (reverse ? group[org(end - 1)] < f.lo : group[org(end - 1)] > f.hi)
      end--;
    Extremes states;
    states.end.fill(begin - 1);
    for (int s = 1; s <= mask; s++)
      if (f.masks[s])
        for (int k = s; k; k &= k - 1) {
          int a = __builtin_ctz((unsigned)k), sub = s ^ (1 << a),
              p = states.end[sub];
          if (p == end) {
            states.end[s] = end;
            break;
          }
          int q = -1, prev = -1, index = end;
          for (size_t j = 0; j < copies[a].size(); j++) {
            int t = copies[a][reverse ? copies[a].size() - 1 - j : j],
                z = reverse ? n - 1 - position[t] : position[t];
            if (z < begin)
              continue;
            if (z >= end)
              break;
            if (z > p) {
              q = t;
              index = z;
              break;
            }
            prev = t;
          }
          if (index <= states.end[s])
            continue;
          states.end[s] = index;
          auto &why = states.escape[s];
          why.clear();
          if (prev >= 0) {
            why = states.escape[sub];
            int t = org(p);
            why.push_back(reverse ? before[prev][t] : before[t][prev]);
          }
          if (q < 0) {
            add(why);
            break;
          }
        }
    return states;
  }

  struct EndOption {
    int a, guard;
    Row counts;
    std::vector<int> force;
    bool exact;
  };
  // Each option describes an orientation's last new letter and the
  // frequencies used by that point. Large slack permits a lower-bound option.
  std::vector<EndOption>
  end_options(const Region &g, bool reverse, const Row &total,
              const std::array<Clause, 10> &occurrences) {
    const auto &low = length82::length_lower_bound;
    int m = g.mask, h = __builtin_popcount((unsigned)m);
    std::vector<EndOption> list;
    Clause any;
    for (int a = 0; a < 10; a++)
      if (m >> a & 1) {
        int pivot = occurrences[a][reverse ? occurrences[a].size() - 1 : 0];
        Row minimum{}, maximum{};
        int slack = -low[h - 1];
        bool ok = true;
        for (int b = 0; b < 10; b++)
          if ((m >> b & 1) && b != a) {
            int sure = 0, poss = 0;
            for (int t : occurrences[b]) {
              int comp = reverse ? before[pivot][t] : before[t][pivot];
              sure += comp == 1;
              poss += comp != -1;
            }
            minimum[b] = std::max(1, sure);
            maximum[b] = poss;
            if (minimum[b] > poss)
              ok = false;
            slack += total[b] - minimum[b];
          }
        if (!ok || slack < 0)
          continue;
        Row d = minimum;
        d[a] = 1;
        auto emit = [&](bool exact) {
          Row tail = total;
          for (int b = 0; b < 10; b++)
            tail[b] -= d[b];
          if (!passes(tail, m ^ (1 << a)))
            return;
          std::vector<int> force{1 << a};
          if (exact) {
            int sing = 0;
            for (int j = 0; j < 10; j++)
              if ((m >> j & 1) && j != a && d[j] == 1)
                sing |= 1 << j;
            for (int i = sing; i; i &= i - 1)
              for (int j = i ^ (i & -i); j; j &= j - 1) {
                int u = (i & -i) | (j & -j);
                if (!passes(tail, m ^ u))
                  return;
                force.push_back(u);
              }
          }
          int guard = ++variable_count;
          any.push_back(guard);
          for (int b = 0; b < 10; b++)
            if ((m >> b & 1) && b != a) {
              int nb = occurrences[b].size(), j = d[b],
                  t = occurrences[b][reverse ? nb - j : j - 1];
              add({-guard, reverse ? before[pivot][t] : before[t][pivot]});
              if (exact && j < nb) {
                t = occurrences[b][reverse ? nb - j - 1 : j];
                add({-guard, reverse ? before[t][pivot] : before[pivot][t]});
              }
            }
          list.push_back({a, guard, d, force, exact});
        };
        if (slack > 3) {
          emit(false);
          continue;
        }
        auto rec = [&](auto &self, int b, int remain) -> void {
          if (b == 10) {
            emit(true);
            return;
          }
          if (!(m >> b & 1) || b == a) {
            self(self, b + 1, remain);
            return;
          }
          for (int extra = 0;
               extra <= remain && minimum[b] + extra <= maximum[b]; extra++) {
            d[b] = minimum[b] + extra;
            self(self, b + 1, remain - extra);
          }
        };
        rec(rec, 0, slack);
      }
    add(any);
    return list;
  }
  void tables(const Region &g) {
    Row total{};
    std::array<Clause, 10> occurrences;
    for (int a = 0; a < 10; a++)
      if (g.mask >> a & 1) {
        for (int t : copies[a])
          if (group[t] >= g.first && group[t] <= g.last) {
            total[a]++;
            occurrences[a].push_back(t);
          }
        if (!total[a]) {
          add({});
          return;
        }
      }
    auto l = end_options(g, false, total, occurrences),
         r = end_options(g, true, total, occurrences);
    if (l.size() * r.size() > 3500)
      return;
    for (auto &p : l)
      for (auto &q : r) {
        if (!p.exact || !q.exact || (p.a == q.a && total[p.a] == 1))
          continue;
        Row core = total;
        for (int a = 0; a < 10; a++)
          core[a] -= p.counts[a] + q.counts[a];
        bool ok = *std::min_element(core.begin(), core.end()) >= 0;
        if (ok)
          for (int u : p.force) {
            for (int v : q.force)
              if (!(u & v) && !passes(core, g.mask ^ u ^ v)) {
                ok = false;
                break;
              }
            if (!ok)
              break;
          }
        if (!ok)
          add({-p.guard, -q.guard});
      }
  }

  // At a cut between consecutive pivot occurrences the two sides cannot
  // both fail their complementary frequency requirements.
  void project(const Region &g) {
    int start = 0, stop = n;
    while (group[path[start]] < g.first)
      start++;
    while (group[path[stop - 1]] > g.last)
      stop--;
    Row tot;
    for (int a = 0; a < 10; a++)
      tot[a] = prefix_counts[stop][a] - prefix_counts[start][a];
    std::array<std::vector<int>, 10> tokens;
    for (int a = 0; a < 10; a++)
      for (int t : copies[a])
        if (group[t] >= g.first && group[t] <= g.last)
          tokens[a].push_back(t);
    auto explain = [&](int endpoint, bool reverse, int mask, Row v,
                       Clause &reason) {
      for (int m = mask; m; m &= m - 1) {
        int a = __builtin_ctz((unsigned)m), lo = v[a], hi = tot[a];
        v[a] = hi;
        if (!passes(v, mask))
          continue;
        while (lo + 1 < hi) {
          int k = (lo + hi) / 2;
          v[a] = k;
          if (passes(v, mask))
            hi = k;
          else
            lo = k;
        }
        v[a] = lo;
        int t = tokens[a][reverse ? tot[a] - 1 - lo : lo];
        reason.push_back(reverse ? before[endpoint][t] : before[t][endpoint]);
      }
    };
    for (int a = 0; a < 10; a++)
      if (g.mask >> a & 1) {
        const int m = g.mask ^ (1 << a);
        const auto &pv = tokens[a];
        if (pv.empty()) {
          add({});
          continue;
        }
        for (int j = 0; j <= (int)pv.size(); j++) {
          Row l{}, r{};
          int lt = j ? pv[j - 1] : -1, rt = j < (int)pv.size() ? pv[j] : -1;
          for (int b = 0; b < 10; b++) {
            if (lt >= 0)
              l[b] = prefix_counts[position[lt]][b] - prefix_counts[start][b];
            if (rt >= 0)
              r[b] =
                  prefix_counts[stop][b] - prefix_counts[position[rt] + 1][b];
          }
          if (j == 0 || j == (int)pv.size()) {
            bool reverse = j == 0;
            auto &v = reverse ? r : l;
            if (!passes(v, m)) {
              Clause why;
              explain(reverse ? rt : lt, reverse, m, v, why);
              add(why);
            }
            continue;
          }
          for (int sub = (m - 1) & m; sub; sub = (sub - 1) & m) {
            if (passes(l, sub) || passes(r, m ^ sub))
              continue;
            Clause why;
            explain(lt, false, sub, l, why);
            explain(rt, true, m ^ sub, r, why);
            add(why);
          }
        }
      }
  }
  // Extremal prefix and suffix orders leave a mandatory universal middle.
  // Cap each coordinate as generously as possible while preserving failure.
  void separate(const Extremes &left, const Extremes &right) {
    for (int a = 0; a <= mask; a++)
      if ((a & mask) == a && left.end[a] < n) {
        int leftpos = left.end[a], lt = leftpos == -1 ? -1 : path[leftpos];
        for (int b = mask ^ a;; b = (b - 1) & (mask ^ a)) {
          int rightpos = n - 1 - right.end[b],
              rt = rightpos == n ? -1 : (rightpos < 0 ? -1 : path[rightpos]);
          if (rightpos >= 0) {
            Clause reasons;
            if (leftpos >= rightpos) {
              reasons.push_back(before[lt][rt]);
            } else {
              int mid = mask ^ a ^ b;
              if (!mid || (mid == mask))
                goto done;
              Row v;
              for (int i = 0; i < 10; i++)
                v[i] =
                    prefix_counts[rightpos][i] - prefix_counts[leftpos + 1][i];
              if (passes(v, mid))
                goto done;
              for (int m = mid; m; m &= m - 1) {
                int i = __builtin_ctz((unsigned)m), old = v[i];
                v[i] = total[i];
                if (!passes(v, mid))
                  continue;
                int l = old, h = total[i];
                while (l + 1 < h) {
                  int t = (l + h) / 2;
                  v[i] = t;
                  if (passes(v, mid))
                    h = t;
                  else
                    l = t;
                }
                v[i] = l;
                int left_ex =
                        std::max(0, prefix_counts[leftpos + 1][i] - (l - old)),
                    right_ex = left_ex + l;
                if (left_ex)
                  reasons.push_back(before[lt][copies[i][left_ex - 1]]);
                if (right_ex < total[i])
                  reasons.push_back(before[copies[i][right_ex]][rt]);
              }
            }
            reasons.insert(reasons.end(), left.escape[a].begin(),
                           left.escape[a].end());
            reasons.insert(reasons.end(), right.escape[b].begin(),
                           right.escape[b].end());
            add(reasons);
          }
        done:
          if (!b)
            break;
        }
      }
  }

public:
  OrderingFormula(FrequencyBounds &b, std::vector<Row> &rows, int m)
      : f(b), mask(m) {
    for (int g = 0; g < (int)rows.size(); g++)
      for (int a = 0; a < 10; a++)
        for (int k = 0; k < rows[g][a]; k++) {
          group.push_back(g);
          letter.push_back(a);
          copies[a].push_back(n++);
          total[a]++;
        }
    before.assign(n, std::vector<int>(n, -1));
    for (int i = 0; i < n; i++)
      for (int j = i + 1; j < n; j++) {
        before[i][j] = group[i] == group[j] && letter[i] != letter[j]
                           ? ++variable_count
                           : 1;
        before[j][i] = -before[i][j];
      }
    for (int i = 0; i < n; i++)
      for (int j = i + 1; j < n && group[j] == group[i]; j++)
        for (int k = j + 1; k < n && group[k] == group[i]; k++) {
          add({-before[i][j], -before[j][k], before[i][k]});
          add({before[i][j], before[j][k], -before[i][k]});
        }
    for (int a = 0; a < 10; a++)
      for (int b = a + 1; b < 10; b++)
        if (!copies[a].empty() && !copies[b].empty() &&
            std::all_of(rows.begin(), rows.end(),
                        [&](const Row &r) { return r[a] == r[b]; }))
          add({before[copies[a][0]][copies[b][0]]});
    regions.push_back({0, (int)rows.size() - 1, m});
    if (rows.size() == 5) {
      int x = letter[std::find(group.begin(), group.end(), 1) - group.begin()],
          z = letter[std::find(group.begin(), group.end(), 3) - group.begin()];
      regions.push_back({2, 4, m ^ (1 << x)});
      regions.push_back({0, 2, m ^ (1 << z)});
      if (x != z)
        regions.push_back({2, 2, m ^ (1 << x) ^ (1 << z)});
      int d = 0, e = 0;
      for (int i = 0; i < 10; i++) {
        if (rows[0][i] > 1)
          d |= 1 << i;
        if (rows[4][i] > 1)
          e |= 1 << i;
      }
      auto left = remaining_alphabets({m}, x, d),
           right = remaining_alphabets({m}, z, e);
      family(2, 4, left);
      family(0, 2, right);
      family(2, 2, remaining_alphabets(left, z, e));
    }
    for (auto &g : regions)
      tables(g);
    path.resize(n);
    position.resize(n);
    prefix_counts.resize(n + 1);
    std::iota(path.begin(), path.end(), 0);
  }
  bool derive(int i) {
    for (int j = 0; j < n; j++) {
      position[path[j]] = j;
      prefix_counts[j + 1] = prefix_counts[j];
      prefix_counts[j + 1][letter[path[j]]]++;
    }
    for (const auto &f : families) {
      greedy_endpoints(f, false);
      greedy_endpoints(f, true);
    }
    for (const auto &g : regions)
      project(g);
    Family whole{0, 4};
    whole.masks.fill(true);
    auto l = greedy_endpoints(whole, false);
    auto r = greedy_endpoints(whole, true);
    if (l.end[mask] < n)
      return true;
    if (pending.size() < 100 || i % 8 == 7)
      separate(l, r);
    retain_clauses();
    return false;
  }
  void read_orders() {
    learning = true;
    int count;
    if (!(std::cin >> count) || count < 0)
      throw std::runtime_error("invalid transcript count");
    for (int i = 0; i < count; i++) {
      std::string word;
      if (!(std::cin >> word) || word.size() != static_cast<size_t>(n))
        throw std::runtime_error("invalid trial word");
      Row used{};
      int previous = -1;
      for (int j = 0; j < n; j++) {
        int a = word[j] - '0';
        if (a < 0 || a >= 10 || used[a] >= static_cast<int>(copies[a].size()))
          throw std::runtime_error("invalid symbol in trial word");
        int token = copies[a][used[a]++];
        if (group[token] < previous)
          throw std::runtime_error("trial word violates block order");
        previous = group[token];
        path[j] = token;
      }
      if (derive(i))
        throw std::runtime_error("transcript contains a universal word");
    }
  }
  // Keep original clause IDs consecutive even in a streaming LRAT producer:
  // activate all comparison clauses together at the end of the input.
  void finalize() {
    if (std::any_of(clauses.begin(), clauses.end(),
                    [](const Clause &clause) { return clause.empty(); })) {
      clauses = {{}};
      return;
    }
    const int activation = ++variable_count;
    for (auto &clause : clauses)
      clause.push_back(activation);
    clauses.push_back({-activation});
  }
  void write(bool selected) const {
    if (selected) {
      size_t k;
      if (!(std::cin >> k) || k > clauses.size())
        throw std::runtime_error("invalid proof reference count");
      std::vector<size_t> ids(k);
      for (size_t &id : ids)
        if (!(std::cin >> id) || !id || id > clauses.size())
          throw std::runtime_error("invalid clause id");
      std::cout << clauses.size() << '\n';
      for (size_t id : ids) {
        for (int v : clauses[id - 1])
          std::cout << v << ' ';
        std::cout << "0\n";
      }
    } else {
      std::cout << "p cnf " << variable_count << ' ' << clauses.size() << '\n';
      for (const auto &cl : clauses) {
        for (int v : cl)
          std::cout << v << ' ';
        std::cout << "0\n";
      }
    }
    std::cout.flush();
  }
};
int main(int argc, char **argv) {
  if (argc != 2 && !(argc == 3 && std::string(argv[2]) == "selected"))
    return 2;
  std::ios::sync_with_stdio(false);
  FrequencyBounds bounds;
  bounds.load(argv[1], 10);
  int number;
  while (std::cin >> number) {
    if (number != 5)
      throw std::runtime_error("expected five blocks");
    std::vector<Row> rows(number);
    for (auto &r : rows)
      for (int &v : r)
        if (!(std::cin >> v) || v < 0)
          throw std::runtime_error("invalid block");
    OrderingFormula formula(bounds, rows, 1023);
    formula.read_orders();
    formula.finalize();
    formula.write(argc == 3);
  }
}
