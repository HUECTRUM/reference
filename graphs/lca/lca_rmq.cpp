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


const ll e7 = 998244353;
const ll mod = e7;

template<ll mod = e7>
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
typedef tree<int, null_type, less<>, rb_tree_tag, tree_order_statistics_node_update> oSet;

//////////////////////////////////////////////////////////////////////////
#define int long long int

const long long LOG = 20, MAXN = 400010;
ll lg[2 * MAXN + 1];

struct LCA_RMQ {
    vvi g;
    int root;

    ll st[LOG + 1][2 * MAXN + 1];

    vi height, euler, first, eulH, par;
    LCA_RMQ(vvi &g, int root): g(g), root(root), height(g.size()), first(g.size()), par(g.size()) {}

    void dfs(int v, int p = -1, int h = 0) {
        height[v] = h, first[v] = euler.size();
        euler.pb(v); par[v] = p;

        repe(to, g[v]) if (to != p) dfs(to, v, h + 1), euler.pb(v);
    }

    void buildEulerHeights() {
        int sz = euler.size();
        eulH = vi(sz);
        rep(i, sz) eulH[i] = height[euler[i]];
    }

    void buildSparse() {
        int sz = euler.size();
        rep(i, sz) st[0][i] = i;

        reps(i, 1, LOG + 1) for (int j = 0; j + (1 << i) <= sz; j++) {
                int minInd1 = st[i - 1][j], minInd2 = st[i - 1][j + (1 << (i - 1))];
                st[i][j] = eulH[minInd1] < eulH[minInd2] ? minInd1 : minInd2;
            }
    }

    int getMinIndex(int l, int r) {
        int i = lg[r - l + 1], first = st[i][l], second = st[i][r - (1 << i) + 1];
        return eulH[first] < eulH[second] ? first : second;
    }

    int lca(int a, int b) {
        long long l = first[a], r = first[b];
        if (l > r) swap(l, r);
        return euler[getMinIndex(l, r)];
    }

    void run() { dfs(root), buildEulerHeights(), buildSparse(); }
};

void precompLogs() {
    lg[1] = 0;
    reps(i, 2, 2 * MAXN + 1) lg[i] = lg[i / 2] + 1;
}

signed main () {
    IO;
    precompLogs();
    int n; cin >> n;

    
}