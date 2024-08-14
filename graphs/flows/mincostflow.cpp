//
// https://codeforces.com/gym/100140 problem H
//
#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>
#include <bits/stdc++.h>

using namespace std;
using namespace __gnu_pbds;
using namespace __gnu_cxx;

/* clang-format off */




/* TYPES  */
#define ll long long
#define ld long double
#define pii pair<int, int>
#define pll pair<long long, long long>
#define vi vector<int>
#define vll vector<long long>
#define vpii vector<pair<int, int>>
#define vpii vector<pair<int, int>>
#define vvpii vector<vector<pair<int, int>>>
#define vpll vector<pair<long long, long long>>
#define vvpll vector<vector<pair<long long, long long>>>
#define vvi vector<vector<int>>
#define vvll vector<vector<long long>>
#define mii map<int, int>
#define si set<int>
#define sc set<char>
#define vd vector<double>
#define vvd vector<vector<double>>


/* FUNCTIONS */
#define feach(el, v) for(auto &el: v)
#define rep(i, n) for(int i=0;i<n;i++)
#define reprv(i, n) for(int i=n-1;i>=0;i--)
#define reps(i, s, e) for(int i=s;i<e;i++)
#define reprve(i, e, s) for(int i=e-1;i>=s;i--)
#define repe(x, y) for (auto &x: y)
#define repe2(x, a, y) for (auto &[x,a]: y)

#define pb push_back
#define eb emplace_back



typedef tree<ll, null_type, less<>, rb_tree_tag, tree_order_statistics_node_update> oSet;
#define IO ios_base::sync_with_stdio(false); cin.tie(NULL); cout.tie(NULL)
#pragma GCC target("popcnt")
#define vct vector

int cntLeq(vll &v, ll x) { return std::upper_bound(v.begin(), v.end(), x) - v.begin(); }
int cntLess(vll &v, ll x) { return std::lower_bound(v.begin(), v.end(), x) - v.begin(); }
int cntGreater(vll &v, ll x) { return v.end() - std::upper_bound(v.begin(), v.end(), x); }
int cntGeq(vll &v, ll x) { return v.end() - std::lower_bound(v.begin(), v.end(), x); }

vll buildPref(vll &v) {
    int n = v.size(); vll pref(n);
    rep(i, n) pref[i] = v[i] + (i ? pref[i - 1] : 0);
    return pref;
}
ll getPrefSum(vll &pref, int l, int r) { return pref[r] - (l ? pref[l - 1] : 0); }

vi dx = {0,0,-1,1}, dy = {-1,1,0,0};

int popcnt(int i) { return __builtin_popcountll(i); }
int popcnt(long long i) { return __builtin_popcountll(i); }

template<typename T>inline void chmax(T &a,T b){a=max(a,b);}
template<typename T>inline void chmin(T &a,T b){a=min(a,b);}

void vectorCoordinateCompression(vll &v) {
    std::sort(v.begin(), v.end());
    v.erase(std::unique(v.begin(), v.end()), v.end());
}

int getVectorCompressed(ll val, vll &v) { return lower_bound(v.begin(), v.end(), val) - v.begin(); }


//////////////////////////////////////////////////////////////////////////
#define int long long int

namespace atcoder {
    namespace internal {
        template <class E> struct csr {
            std::vector<int> start;
            std::vector<E> elist;
            explicit csr(int n, const std::vector<std::pair<int, E>>& edges)
                    : start(n + 1), elist(edges.size()) {
                for (auto e : edges) {
                    start[e.first + 1]++;
                }
                for (int i = 1; i <= n; i++) {
                    start[i] += start[i - 1];
                }
                auto counter = start;
                for (auto e : edges) {
                    elist[counter[e.first]++] = e.second;
                }
            }
        };
    }

    template <class Cap, class Cost> struct mcf_graph {
    public:
        mcf_graph() {}
        explicit mcf_graph(int n) : _n(n) {}

        int add_edge(int from, int to, Cap cap, Cost cost) {
            assert(0 <= from && from < _n);
            assert(0 <= to && to < _n);
            assert(0 <= cap);
            assert(0 <= cost);
            int m = (int)(_edges.size());
            _edges.push_back({from, to, cap, 0, cost});
            return m;
        }

        struct edge {
            int from, to;
            Cap cap, flow;
            Cost cost;
        };

        edge get_edge(int i) {
            int m = (int)(_edges.size());
            assert(0 <= i && i < m);
            return _edges[i];
        }
        std::vector<edge> edges() { return _edges; }

        std::pair<Cap, Cost> flow(int s, int t) {
            return flow(s, t, std::numeric_limits<Cap>::max());
        }
        std::pair<Cap, Cost> flow(int s, int t, Cap flow_limit) {
            return slope(s, t, flow_limit).back();
        }
        std::vector<std::pair<Cap, Cost>> slope(int s, int t) {
            return slope(s, t, std::numeric_limits<Cap>::max());
        }
        std::vector<std::pair<Cap, Cost>> slope(int s, int t, Cap flow_limit) {
            assert(0 <= s && s < _n);
            assert(0 <= t && t < _n);
            assert(s != t);

            int m = (int)(_edges.size());
            std::vector<int> edge_idx(m);

            auto g = [&]() {
                std::vector<int> degree(_n), redge_idx(m);
                std::vector<std::pair<int, _edge>> elist;
                elist.reserve(2 * m);
                for (int i = 0; i < m; i++) {
                    auto e = _edges[i];
                    edge_idx[i] = degree[e.from]++;
                    redge_idx[i] = degree[e.to]++;
                    elist.push_back({e.from, {e.to, -1, e.cap - e.flow, e.cost}});
                    elist.push_back({e.to, {e.from, -1, e.flow, -e.cost}});
                }
                auto _g = internal::csr<_edge>(_n, elist);
                for (int i = 0; i < m; i++) {
                    auto e = _edges[i];
                    edge_idx[i] += _g.start[e.from];
                    redge_idx[i] += _g.start[e.to];
                    _g.elist[edge_idx[i]].rev = redge_idx[i];
                    _g.elist[redge_idx[i]].rev = edge_idx[i];
                }
                return _g;
            }();

            auto result = slope(g, s, t, flow_limit);

            for (int i = 0; i < m; i++) {
                auto e = g.elist[edge_idx[i]];
                _edges[i].flow = _edges[i].cap - e.cap;
            }

            return result;
        }

    private:
        int _n;
        std::vector<edge> _edges;

        // inside edge
        struct _edge {
            int to, rev;
            Cap cap;
            Cost cost;
        };

        std::vector<std::pair<Cap, Cost>> slope(internal::csr<_edge>& g,
                                                int s,
                                                int t,
                                                Cap flow_limit) {
            std::vector<std::pair<Cost, Cost>> dual_dist(_n);
            std::vector<int> prev_e(_n);
            std::vector<bool> vis(_n);
            struct Q {
                Cost key;
                int to;
                bool operator<(Q r) const { return key > r.key; }
            };
            std::vector<int> que_min;
            std::vector<Q> que;
            auto dual_ref = [&]() {
                for (int i = 0; i < _n; i++) {
                    dual_dist[i].second = std::numeric_limits<Cost>::max();
                }
                std::fill(vis.begin(), vis.end(), false);
                que_min.clear();
                que.clear();

                size_t heap_r = 0;

                dual_dist[s].second = 0;
                que_min.push_back(s);
                while (!que_min.empty() || !que.empty()) {
                    int v;
                    if (!que_min.empty()) {
                        v = que_min.back();
                        que_min.pop_back();
                    } else {
                        while (heap_r < que.size()) {
                            heap_r++;
                            std::push_heap(que.begin(), que.begin() + heap_r);
                        }
                        v = que.front().to;
                        std::pop_heap(que.begin(), que.end());
                        que.pop_back();
                        heap_r--;
                    }
                    if (vis[v]) continue;
                    vis[v] = true;
                    if (v == t) break;
                    Cost dual_v = dual_dist[v].first, dist_v = dual_dist[v].second;
                    for (int i = g.start[v]; i < g.start[v + 1]; i++) {
                        auto e = g.elist[i];
                        if (!e.cap) continue;
                        Cost cost = e.cost - dual_dist[e.to].first + dual_v;
                        if (dual_dist[e.to].second - dist_v > cost) {
                            Cost dist_to = dist_v + cost;
                            dual_dist[e.to].second = dist_to;
                            prev_e[e.to] = e.rev;
                            if (dist_to == dist_v) {
                                que_min.push_back(e.to);
                            } else {
                                que.push_back(Q{dist_to, e.to});
                            }
                        }
                    }
                }
                if (!vis[t]) {
                    return false;
                }

                for (int v = 0; v < _n; v++) {
                    if (!vis[v]) continue;
                    dual_dist[v].first -= dual_dist[t].second - dual_dist[v].second;
                }
                return true;
            };
            Cap flow = 0;
            Cost cost = 0, prev_cost_per_flow = -1;
            std::vector<std::pair<Cap, Cost>> result = {{Cap(0), Cost(0)}};
            while (flow < flow_limit) {
                if (!dual_ref()) break;
                Cap c = flow_limit - flow;
                for (int v = t; v != s; v = g.elist[prev_e[v]].to) {
                    c = std::min(c, g.elist[g.elist[prev_e[v]].rev].cap);
                }
                for (int v = t; v != s; v = g.elist[prev_e[v]].to) {
                    auto& e = g.elist[prev_e[v]];
                    e.cap += c;
                    g.elist[e.rev].cap -= c;
                }
                Cost d = -dual_dist[s].first;
                flow += c;
                cost += c * d;
                if (prev_cost_per_flow == d) {
                    result.pop_back();
                }
                result.push_back({flow, cost});
                prev_cost_per_flow = d;
            }
            return result;
        }
    };
}
using namespace atcoder;


signed main() {
    IO;

    int n, m;
    cin >> n >> m;
    mcf_graph<int, int> g(n + m + 2);

    vi csts(n);
    rep(i, n) {
        int cap, cst; cin >> cap >> cst;
        csts[i] = cst;
        g.add_edge(m + i + 1, m + n + 1, cap, 0);
    }
    rep(i, m) {
        g.add_edge(0, i + 1, 1, 0);
        int cnt; cin >> cnt;
        rep(j, cnt) {
            int to; cin >> to;
            g.add_edge(i + 1, m + to, 1, csts[to - 1]);
        }
    }
    auto [flow, totCost] = g.flow(0, m + n + 1);
    if (flow < m) cout << "-1";
    else cout << totCost;
}
