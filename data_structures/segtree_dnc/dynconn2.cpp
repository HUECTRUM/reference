//
// V1 - https://codeforces.com/gym/100551/problem/A, https://codeforces.com/gym/100551/problem/E
// query - comp count, init via events/edge time ranges
//

#include <iostream>
#include <utility>
#include <vector>
#include <algorithm>
#include <numeric>
#include <map>
#include <unordered_set>
#include <iostream>
#include <utility>
#include <vector>
#include <algorithm>
#include <numeric>
#include <map>
#include <unordered_set>
#include <unordered_map>
#include <queue>
#include <set>
#include <stack>
#include <fstream>
#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>
#include <bitset>
#include <sstream>
#include <ext/rope>
#include <ctime>
#include <random>
#include <cstdlib>
#include <complex>
#include <bits/stdc++.h>

using namespace std;
using namespace __gnu_pbds;
using namespace __gnu_cxx;

/* clang-format off */

/* TYPES  */
#define ll long long
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



const ll mod = 1000000007;

template<ll mod = 1000000007>
struct ModInt {
    ll p;

    ModInt() : p(0) {}

    ModInt(ll x) { p = x >= 0 ? x % mod : x + (-x + mod - 1) / mod * mod; }

    ModInt &operator+=(const ModInt &y) {
        p = p + *y - ((p + *y) >= mod ? mod : 0);
        return *this;
    }

    ModInt &operator-=(const ModInt &y) {
        p = p - *y + (p - *y < 0 ? mod : 0);
        return *this;
    }

    ModInt &operator*=(const ModInt &y) {
        p = (p * *y) % mod;
        return *this;
    }

    ModInt &operator%=(const ModInt &y) {
        if (y)p %= *y;
        return *this;
    }

    ModInt operator+(const ModInt &y) const {
        ModInt x = *this;
        return x += y;
    }

    ModInt operator-(const ModInt &y) const {
        ModInt x = *this;
        return x -= y;
    }

    ModInt operator*(const ModInt &y) const {
        ModInt x = *this;
        return x *= y;
    }

    ModInt operator%(const ModInt &y) const {
        ModInt x = *this;
        return x %= y;
    }

    ModInt binpow(const ModInt &y, ll pow) const {
        pow %= mod - 1;
        ModInt res = 1, a = y;
        while (pow) {
            if (pow & 1) res *= a;
            a *= a, pow >>= 1;
        }
        return res;
    }

    ModInt inv() const { return binpow(*this, mod - 2); }

    ModInt &operator/=(const ModInt &y) {
        p = (p * y.inv().p) % mod;
        return *this;
    }

    ModInt operator/(const ModInt &y) const {
        ModInt x = *this;
        return x /= y;
    }

    friend istream &operator>>(istream &is, ModInt &a) {
        int v;
        is >> v;
        a = ModInt(v);
        return is;
    }

    friend ostream &operator<<(ostream &os, const ModInt &a) { return os << a.p; }

    ModInt &operator++() {
        p = (p + 1) % mod;
        return *this;
    }

    ModInt &operator--() {
        p = (p - 1 + mod) % mod;
        return *this;
    }

    bool operator==(const ModInt &y) const { return p == *y; }

    bool operator!=(const ModInt &y) const { return p != *y; }

    const ll &operator*() const { return p; }

    ll &operator*() { return p; }

};

using Mint = ModInt<>;
#define vmint vector<Mint>
#define vvmint vector<vector<Mint>>
typedef tree<ll, null_type, less<>, rb_tree_tag, tree_order_statistics_node_update> oSet;
#define IO ios_base::sync_with_stdio(false); cin.tie(NULL); cout.tie(NULL)
#pragma GCC target("popcnt")
#define int long long int
//////////////////////////////////////////////////////////////////////////

struct event { int type, a, b, t; };
struct addEdges {int a, b, l, r; };
struct DynConn {
    int n, q;
    vvpii stree;
    vi par, sz, queryFilter;
    stack<pii> updates;
    vi answers;
    int comps;

    int getAnswer() { return comps; }

    void initDsu(int cnt) {
        par = sz = vi(n, 1); comps = cnt;
        iota(par.begin(), par.end(), 0);
    }

    int find(int x) { return x == par[x] ? x : find(par[x]); }

    bool unite(int x, int y) {
        x = find(x), y = find(y);
        if (x == y) return false;

        if (sz[x] < sz[y]) swap(x, y);

        updates.push({x, y});
        par[y] = x; sz[x] += sz[y]; --comps;
        return true;
    }

    void rollback() {
        auto [x, y] = updates.top(); updates.pop();
        par[y] = y; sz[x] -= sz[y]; ++comps;
    }

    void add(int l, int r, int a, int b, int v, int tl, int tr) {
        if (l > r) return;
        if (l == tl && r == tr) return void(stree[v].push_back({a, b}));

        int tm = (tl + tr) >> 1;
        add(l, min(r, tm), a, b, v << 1, tl, tm);
        add(max(l, tm + 1), r, a, b, v << 1 | 1, tm + 1, tr);
    }

    void add(int l, int r, int a, int b) { add(l, r, a, b, 1, 0, q - 1); }

    void dfs(int v, int tl, int tr) {
        int updA = 0;
        for (auto [x, y]: stree[v]) {
            if (unite(x, y)) ++updA;
        }

        if (tl == tr) answers[tl] = getAnswer();
        else {
            int tm = (tl + tr) >> 1;
            dfs(v << 1, tl, tm); dfs(v << 1 | 1, tm + 1, tr);
        }

        rep(i, updA) rollback();
    }

    void dfs() { dfs(1, 0, q - 1); }

    void init(int n, int q, vector<event> events, vi queryFilter) {
        this->n = n, this->q = q; this->queryFilter = queryFilter;
        initDsu(n); stree = vvpii(4 * q); answers = vi(q);

        map<pii, int> addTime;
        rep(i, events.size()) {
            auto [tp, a, b, t] = events[i];
            if (a > b) swap(a, b);

            if (tp == 1) addTime[{a, b}] = t;
            else {
                int tL = addTime[{a, b}];
                int tR = t - 1;
                add(tL, tR, a, b);
                addTime.erase({a, b});
            }
        }
        for (auto [pair, tL]: addTime) add(tL, q - 1, pair.first, pair.second);
    }

    void init(int n, int q, vector<event> events) {
        vi queryFilter(q);
        iota(queryFilter.begin(), queryFilter.end(), 0);
        init(n, q, events, queryFilter);
    }

    void init(int n, int q, vector<addEdges> edges, vi queryFilter) {
        this->n = n, this->q = q; this->queryFilter = queryFilter;
        initDsu(n); stree = vvpii(4 * q); answers = vi(q);
        for (auto &[a, b, l, r]: edges) add(l, r, a, b);
    }

    void init(int n, int q, vector<addEdges> edges) {
        vi queryFilter(q);
        iota(queryFilter.begin(), queryFilter.end(), 0);
        init(n, q, edges, queryFilter);
    }

    void run() { dfs(); }

    vi getResults() {
        vi fin;
        rep(i ,queryFilter.size()) fin.push_back(answers[queryFilter[i]]);
        return fin;
    }
};

vector<addEdges> toAddEdges(vpii &edges, vvpii &times, int m) {
    vector<addEdges> events;
    rep(i, edges.size()) rep(j, times[i].size()) {
        events.push_back({edges[i].first, edges[i].second, times[i][j].first, times[i][j].second});
    }
    return events;
}

signed main() {
    ifstream cin("disconnected.in"); ofstream cout("disconnected.out");
    IO;

    int n, m; cin >> n >> m;
    vpii edges(m);
    rep(i, m) {
        int a, b; cin >> a >> b; --a, --b;
        edges[i] = {a, b};
    }

    int k; cin >> k;
    vvpii times(m);
    rep(i, m) times[i].push_back({0, k});

    reps(i, 1, k + 1) {
        int sz; cin >> sz;
        rep(j, sz) {
            int x; cin >> x; --x;
            auto [l, r] = times[x].back(); times[x].pop_back();
            times[x].push_back({l, i - 1}); times[x].push_back({i + 1, k});
        }
    }

    vector<addEdges> aE = toAddEdges(edges, times, m);

    DynConn dc = DynConn();
    dc.init(n, k + 1, aE);
    dc.run();
    vi ans = dc.getResults();

    reps(i, 1, k + 1) {
        if (ans[i] > 1) cout << "Disconnected" << endl;
        else cout << "Connected" << endl;
    }
}

signed main2() {
    ifstream cin("connect.in"); ofstream cout("connect.out");
    IO;

    int n, q; cin >> n >> q;
    if (!q) return 0;
    vector<event> events;
    vi queryFilter;
    rep(i, q) {
        char c; int a, b;
        cin >> c;
        if (c == '?') queryFilter.push_back(i);
        else {
            cin >> a >> b; --a, --b;
            events.push_back({c == '+' ? 1 : 2, a, b, i});
        }
    }

    DynConn dc = DynConn();
    dc.init(n, q, events, queryFilter);
    dc.run();

    vi rs = dc.getResults();
    rep(i, rs.size()) cout << rs[i] << "\n";
}
