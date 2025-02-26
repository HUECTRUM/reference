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
    int n = v.size();
    vll pref(n);
    rep(i, n) pref[i] = v[i] + (i ? pref[i - 1] : 0);
    return pref;
}

ll getPrefSum(vll &pref, int l, int r) { return pref[r] - (l ? pref[l - 1] : 0); }

vi dx = {0, 0, -1, 1}, dy = {-1, 1, 0, 0};

int popcnt(int i) { return __builtin_popcountll(i); }

int popcnt(long long i) { return __builtin_popcountll(i); }

template<typename T>
inline void chmax(T &a, T b) { a = max(a, b); }

template<typename T>
inline void chmin(T &a, T b) { a = min(a, b); }

void vectorCoordinateCompression(vll &v) {
    std::sort(v.begin(), v.end());
    v.erase(std::unique(v.begin(), v.end()), v.end());
}

int getVectorCompressed(ll val, vll &v) { return lower_bound(v.begin(), v.end(), val) - v.begin(); }


//////////////////////////////////////////////////////////////////////////
#define int long long int

struct PushRelabel {
    struct Edge {
        int to, rev, cap, flow;
    };
    int n, s, t;
    vector<vector<Edge>> graph;
    vector<int> excess, height, cur;

    PushRelabel(int n, int s, int t) : n(n), s(s), t(t) {
        graph.resize(n);
        excess.assign(n, 0);
        height.assign(n, 0);
        cur.assign(n, 0);
    }

    inline void addEdge(int u, int v, int cap) {
        graph[u].push_back({v, (int)graph[v].size(), cap, 0});
        graph[v].push_back({u, (int)graph[u].size()-1, 0, 0});
    }

    int maxFlow() {
        // Initialize preflow from source.
        height[s] = n;
        for(auto &e : graph[s]) {
            int delta = e.cap;
            if(delta > 0) {
                e.cap = 0;
                graph[e.to][e.rev].cap += delta;
                e.flow += delta;
                excess[e.to] += delta;
                excess[s] -= delta;
            }
        }
        deque<int> q;
        for (int i = 0; i < n; i++) {
            if(i != s && i != t && excess[i] > 0)
                q.push_back(i);
        }
        while(!q.empty()){
            int u = q.front();
            q.pop_front();
            int oldHeight = height[u];
            discharge(u, q);
            if(excess[u] > 0) {
                // If height increased, push to front.
                if(height[u] > oldHeight)
                    q.push_front(u);
                else
                    q.push_back(u);
            }
        }
        return excess[t];
    }

    inline void discharge(int u, deque<int>& q) {
        while(excess[u] > 0) {
            if(cur[u] < (int)graph[u].size()) {
                auto &e = graph[u][cur[u]];
                if(e.cap > 0 && height[u] == height[e.to] + 1) {
                    int delta = min(excess[u], e.cap);
                    e.cap -= delta;
                    graph[e.to][e.rev].cap += delta;
                    e.flow += delta;
                    graph[e.to][e.rev].flow -= delta;
                    excess[u] -= delta;
                    excess[e.to] += delta;
                    if(e.to != s && e.to != t && excess[e.to] == delta)
                        q.push_back(e.to);
                } else {
                    cur[u]++;
                }
            } else {
                relabel(u);
                cur[u] = 0;
            }
        }
    }

    inline void relabel(int u) {
        int minHeight = INT_MAX;
        for(auto &e : graph[u])
            if(e.cap > 0)
                minHeight = min(minHeight, height[e.to]);
        if(minHeight < INT_MAX)
            height[u] = minHeight + 1;
    }
};



signed main() {
    IO;

    int m, x; cin >> m;
    vvi vv(m);
    vi allNums;
    vct<mii> singleFreq(m);

    rep(arr, m) {
        int sz; cin >> sz;
        rep(i, sz) {
            cin >> x;
            vv[arr].pb(x); allNums.pb(x);
            singleFreq[arr][x]++;
        }
    }

    vectorCoordinateCompression(allNums);
    int n = allNums.size(), req = 0;
    vi allFreq(n);
    rep(arr, m) repe(f, vv[arr]) allFreq[getVectorCompressed(f, allNums)]++;

    rep(i, n) {
        req += allFreq[i];
        if (allFreq[i] & 1) {
            cout << "NO";
            return 0;
        }
    }
    req /= 2;


    PushRelabel gr(n + m + 2, 0, n + m + 1);

    rep(i, m) {
        gr.addEdge(0, i + 1, vv[i].size() / 2);
        for (auto &[num, occs]: singleFreq[i]) {
            int idx = getVectorCompressed(num, allNums);
            gr.addEdge(i + 1, m + 1 + idx, occs);
        }
    }
    rep(i, n) gr.addEdge(m + 1 + i, m + n + 1, allFreq[i] / 2);

    int fl = gr.maxFlow();
    if (fl != req) {
        cout << "NO";
        return 0;
    }

    vct<mii> split(m);
    reps(i, 1, m + 1) {
        for (auto &edg: gr.graph[i]) {
            if (edg.to == n + m + 1 || edg.to == 0) continue;

            int arrIdx = i - 1, numIdx = edg.to - m - 1;
            int num = allNums[numIdx];

            split[arrIdx][num] = edg.flow;
        }
    }

    cout << "YES" << endl;
    rep(arr, m) {
        repe(el, vv[arr]) {
            if (split[arr][el]) cout << 'L', --split[arr][el];
            else cout << 'R';
        }
        cout << endl;
    }
}