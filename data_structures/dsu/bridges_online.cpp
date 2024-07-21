//
// Reference problem: https://codeforces.com/gym/100551/problem/B
// maintaining a forest of 2cc using dsu
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

struct BridgesDSU {
    vi par, dsu_2cc, dsu_cc, size_cc;
    int bridges = 0, lcaCnt = 0;
    vi visitMark;

    void init(int n) {
        par = dsu_2cc = dsu_cc = size_cc = visitMark = vi(n);
        rep(i, n) dsu_2cc[i] = dsu_cc[i] = i, size_cc[i] = 1, par[i] = -1;
    }

    int find_2cc(int v) {
        if (v == -1) return -1;
        return dsu_2cc[v] == v ? v : (dsu_2cc[v] = find_2cc(dsu_2cc[v]));
    }

    int find_cc(int v) {
        v = find_2cc(v);
        return dsu_cc[v] == v ? v : (dsu_cc[v] = find_cc(dsu_cc[v]));
    }

    void reroot(int v) {
        int root = v, child = -1;
        while (v != -1) {
            int p = find_2cc(par[v]);
            par[v] = child, dsu_cc[v] = root;
            child = v, v = p;
        }
        size_cc[root] = size_cc[child];
    }

    void pathMerge(int a, int b) {
        ++lcaCnt;
        vector<int> pathA, pathB;
        int lca = -1;

        while (lca == -1) {
            auto oneUp = [&](int &x, vi &path) -> bool {
                if (x == -1) return false;
                x = find_2cc(x); path.push_back(x);
                if (visitMark[x] == lcaCnt) {
                    lca = x; return true;
                }
                visitMark[x] = lcaCnt, x = par[x];
                return false;
            };

            bool got = oneUp(a, pathA) | oneUp(b, pathB);
            if (got) break;
        }

        auto markLca = [&](vi &path) -> void {
            repe(v, path) {
                dsu_2cc[v] = lca;
                if (v == lca) return;
                --bridges;
            }
        };
        markLca(pathA), markLca(pathB);
    }

    void addEdge(int a, int b) {
        a = find_2cc(a), b = find_2cc(b);
        if (a == b) return;

        int ca = find_cc(a), cb = find_cc(b);
        if (ca == cb) return void(pathMerge(a, b));

        ++bridges;
        if (size_cc[ca] > size_cc[cb]) swap(a, b), swap(ca, cb);
        reroot(a);
        par[a] = dsu_cc[a] = b, size_cc[cb] += size_cc[a];
    }
};


signed main() {
    ifstream cin("bridges.in"); ofstream cout("bridges.out");
    IO;
    int n, m; cin >> n >> m;

    BridgesDSU ds = BridgesDSU();
    ds.init(n);

    int a, b;
    rep(i, m) {
        cin >> a >> b; --a, --b;
        ds.addEdge(a, b);
    }

    int k; cin >> k;
    vi ans;
    rep(i, k) {
        cin >> a >> b; --a, --b;
        ds.addEdge(a, b);
        ans.push_back(ds.bridges);
    }

    rep(i, ans.size()) cout << ans[i] << "\n";
}
