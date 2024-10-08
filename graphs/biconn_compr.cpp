//
// https://codeforces.com/contest/652/problem/E
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

    ModInt binpow(ll pow) const {
        pow %= mod - 1;
        ModInt res = 1, a = *this;
        while (pow) {
            if (pow & 1) res *= a;
            a *= a, pow >>= 1;
        }
        return res;
    }

    ModInt binpow1(const ModInt &y, ll pow) const {
        pow %= mod - 1;
        ModInt res = 1, a = y;
        while (pow) {
            if (pow & 1) res *= a;
            a *= a, pow >>= 1;
        }
        return res;
    }

    ModInt inv() const { return binpow1(*this, mod - 2); }

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
typedef tree<ll, null_type, less_equal<>, rb_tree_tag, tree_order_statistics_node_update> oSet;
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

//////////////////////////////////////////////////////////////////////////
#define int long long int

struct BiconCompr {
    int vCnt, timer = 0;
    vvi g, eId;
    vi brMark, used, tin, low, compSz, rootMapping;
    vvi cG;

    void init(vvi &graph, vvi &edges, int n, int m) {
        vCnt = n;
        g = graph; eId = edges; cG = vvi(n);
        used = tin = low = compSz = rootMapping = vi(n); brMark = vi(m);
    }

    void dfsMark(int v, int p = -1) {
        used[v] = 1, tin[v] = low[v] = timer++;

        rep(i, g[v].size()) {
            int to = g[v][i];
            if (to == p) continue;
            else if (used[to]) low[v] = min(low[v], tin[to]);
            else {
                dfsMark(to, v);
                low[v] = min(low[v], low[to]);
                if (low[to] > tin[v]) brMark[eId[v][i]] = 1;
            }
        }
    }

    void compr(int v, int curRoot) {
        used[v] = 1, compSz[curRoot]++, rootMapping[v] = curRoot;

        rep(i, g[v].size()) {
            int to = g[v][i], mark = brMark[eId[v][i]];
            if (!used[to]) {
                if (!mark) compr(to, curRoot);
                else {
                    cG[curRoot].pb(to), cG[to].pb(curRoot);
                    compr(to, to);
                }
            }
        }
    }

    void run() { dfsMark(0), used.assign(vCnt, 0), compr(0, 0); }
};

vvi cG;
set<pii> cArts;
vi hasArts;
int dfs(int v, int target, int p = -1, int hasOnPath = 0) {
    if (hasArts[v]) hasOnPath = 1;
    if (v == target) return hasOnPath;

    int ans = 0;
    repe(to, cG[v]) if (to != p) {
            int bridgeArt = cArts.count({to, v});
            ans |= dfs(to, target, v, hasOnPath | bridgeArt);
        }
    return ans;
}

struct edge {int a, b, c; };

signed main() {
    IO;

    int n, m; cin >> n >> m;
    vvi g(n), eId(n);
    vector<edge> edges(m);

    int a, b, c;
    rep(i, m) {
        cin >> a >> b >> c; --a, --b;
        g[a].pb(b), g[b].pb(a);
        eId[a].pb(i), eId[b].pb(i);
        edges[i] = {a, b, c};
    }

    BiconCompr compr;
    compr.init(g, eId, n, m);
    compr.run();

    vi rtMap = compr.rootMapping;
    hasArts = vi(n);
    cG = compr.cG;


    rep(i, m) {
        int l = edges[i].a, r = edges[i].b, isArt = edges[i].c;
        int rtL = rtMap[l], rtR = rtMap[r];
        if (rtL == rtR && isArt) hasArts[rtL] = 1;
        if (rtL != rtR && isArt) cArts.insert({rtL, rtR}), cArts.insert({rtR, rtL});
    }

    int st, end; cin >> st >> end; --st, --end;
    st = rtMap[st], end = rtMap[end];
    if (st == end) {
        cout << (hasArts[st] ? "YES": "NO");
        return 0;
    } else {
        int ans = dfs(st, end);
        cout << (ans ? "YES": "NO");
    }
}