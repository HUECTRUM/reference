//
// https://codeforces.com/contest/665/problem/E
// https://www.codechef.com/problems/SUBBXOR
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

//////////////////////////////////////////////////////////////////////////


const int MAXN = 100010, INDEXMULT = 33, BITS = 32;

struct XorTrie {
    int go[INDEXMULT * MAXN][2], cnt[INDEXMULT * MAXN], sz;

    void reset(bool full) {
        int maxReset = full ? INDEXMULT * MAXN : min(sz + 2, INDEXMULT * MAXN);
        rep(i, maxReset) go[i][0] = go[i][1] = cnt[i] = 0;
        sz = 2;
    }

    void insert(int num) {
        int curV = 1;
        reprv(i, BITS) {
            bool iSet = (num & (1 << i));
            if (!go[curV][iSet]) {
                int newV = sz;
                ++sz;
                go[curV][iSet] = newV;
            }
            curV = go[curV][iSet];
            ++cnt[curV];
        }
    }

    int cntMore(int xorWith, int target, bool addEqual = false) {
        int curV = 1, ans = 0;
        reprv(i, BITS) {
            bool iSet = (xorWith & (1 << i)), kSet = (target & (1 << i));
            if (kSet) curV = go[curV][1 - iSet];
            else {
                ans += cnt[go[curV][1 - iSet]];
                curV = go[curV][iSet];
            }
        }
        if (addEqual) ans += cnt[curV];
        return ans;
    }

    int cntLess(int xorWith, int target, bool addEqual = false) {
        int curV = 1, ans = 0;
        reprv(i, BITS) {
            bool iSet = (xorWith & (1 << i)), kSet = (target & (1 << i));
            if (kSet) {
                ans += cnt[go[curV][iSet]];
                curV = go[curV][1 - iSet];
            } else curV = go[curV][iSet];
        }
        if (addEqual) ans += cnt[curV];
        return ans;
    }
};

XorTrie xtr;

signed main() {
    IO;

    xtr.reset(true);

    int t; cin >> t;
    while (t--) {
        int n, k; cin >> n >> k;
        vi v(n); rep(i, n) cin >> v[i];

        xtr.reset(false); xtr.insert(0);

        ll ans = 0; int pref = 0;
        rep(i, n) {
            pref ^= v[i];

            ans += xtr.cntLess(pref, k, false);
            xtr.insert(pref);
        }
        cout << ans << "\n";
    }
}