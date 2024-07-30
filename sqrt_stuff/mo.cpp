//
// https://cses.fi/problemset/task/1734/
// query - distinct values
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

//////////////////////////////////////////////////////////////////////////


const int MAXN = 200010;

struct query { int l, r, id; };
struct MO {
    vector<query> queries;
    vi ans, v;
    int n, q;

    vi freq = vi(MAXN);
    int uCnt = 0;

    void init(vector<query> &qu, vi &arr, int BLOCKSZ = 450) {
        queries = qu, v = arr; ans = vi(qu.size());
        std::sort(queries.begin(), queries.end(), [&](query &q1, query &q2) {
            return make_pair(q1.l / BLOCKSZ, q1.r) < make_pair(q2.l / BLOCKSZ, q2.r);
        });
        q = qu.size(), n = v.size();
    }

    void add(int idx) {
        if (!freq[v[idx]]) ++uCnt;
        freq[v[idx]]++;
    }

    void remove(int idx) {
        freq[v[idx]]--;
        if (!freq[v[idx]]) --uCnt;
    }

    int getAns() { return uCnt; }

    void run() {
        int curL = 0, curR = -1, uCnt = 0;

        rep(i, q) {
            auto qu = queries[i];
            while (curL > qu.l) {
                curL--;
                add(curL);
            }
            while (curR < qu.r) {
                curR++;
                add(curR);
            }
            while (curL < qu.l) {
                remove(curL);
                curL++;
            }
            while (curR > qu.r) {
                remove(curR);
                curR--;
            }
            ans[qu.id] = getAns();
        }
    }

    vi getResults() { return ans; }
};


void compress(vi &v, int n) {
    vector<int> d = v;
    sort(d.begin(), d.end());
    d.resize(unique(d.begin(), d.end()) - d.begin());
    for (int i = 0; i < n; ++i) v[i] = lower_bound(d.begin(), d.end(), v[i]) - d.begin();
}


signed main() {
    IO;

    int n, q; cin >> n >> q;
    vi v(n);
    rep(i, n) cin >> v[i];
    compress(v, n);

    vector<query> queries(q);
    int a, b;
    rep(i, q) {
        cin >> a >> b; --a, --b;
        queries[i] = {a, b, i};
    }

    MO mo = MO();
    mo.init(queries, v);
    mo.run();
    vi ans = mo.getResults();

    rep(i, q) cout << ans[i] << "\n";
}
