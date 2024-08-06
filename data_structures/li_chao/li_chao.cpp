//
// https://cses.fi/problemset/task/2085/
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

#pragma comment(linker, "/STACK:16777216")

//////////////////////////////////////////////////////////////////////////

const ll INF = 1e12, MAXN = 1e6 + 5;

struct LiChaoMin {
    vpll stree = vpll(4 * MAXN, {0, INF});

    ll eval(pll line, ll x) { return line.first * x + line.second; }

    ll query(ll x, int v = 1, ll tl = 0, ll tr = MAXN) {
        if (tl + 1 == tr) return eval(stree[v], x);

        ll tm = (tl + tr) >> 1;
        if (x < tm) return min(eval(stree[v], x), query(x, v << 1, tl, tm));
        else return min(eval(stree[v], x), query(x, v << 1 | 1, tm, tr));
    }

    void insert(pll line, int v = 1, ll tl = 0, ll tr = MAXN) {
        ll tm = (tl + tr) >> 1;
        bool evalL = eval(line, tl) < eval(stree[v], tl), evalM = eval(line, tm) < eval(stree[v], tm);

        if (evalM) swap(line, stree[v]);
        if (tl + 1 == tr) return;

        if (evalL != evalM) insert(line, v << 1, tl, tm);
        else insert(line, v << 1 | 1, tm, tr);
    }
};

struct LiChaoMax {
    vpll stree = vpll(4 * MAXN, {0, -INF});

    ll eval(pll line, ll x) { return line.first * x + line.second; }

    ll query(ll x, int v = 1, ll tl = 0, ll tr = MAXN) {
        if (tl + 1 == tr) return eval(stree[v], x);

        ll tm = (tl + tr) >> 1;
        if (x < tm) return max(eval(stree[v], x), query(x, v << 1, tl, tm));
        else return max(eval(stree[v], x), query(x, v << 1 | 1, tm, tr));
    }

    void insert(pll line, int v = 1, ll tl = 0, ll tr = MAXN) {
        ll tm = (tl + tr) >> 1;
        bool evalL = eval(line, tl) > eval(stree[v], tl), evalM = eval(line, tm) > eval(stree[v], tm);

        if (evalM) swap(line, stree[v]);
        if (tl + 1 == tr) return;

        if (evalL != evalM) insert(line, v << 1, tl, tm);
        else insert(line, v << 1 | 1, tm, tr);
    }
};

LiChaoMin lch;

signed main() {
    IO;

    ll n; cin >> n;
    vll v(n + 1), dp(n + 1, 0), f(n + 1);
    cin >> f[0];
    reps(i, 1, n + 1) cin >> v[i];
    reps(i, 1, n + 1) cin >> f[i];

    lch.insert({f[0], 0});
    reps(i, 1, n + 1) {
        ll minVal = lch.query(v[i]);
        dp[i] = minVal;
        lch.insert({f[i], dp[i]});
    }
    cout << dp[n];
}