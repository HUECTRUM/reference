//
// https://codeforces.com/gym/100140 problem C
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

const int INF = 1e9;
struct GlobalMincut {
    int n;
    vvi g;
    int bestCost = INF;
    vi bestCut;

    GlobalMincut(int n, vvi g) : n(n), g(g) {}

    void run() {
        vi v[n];
        rep(i, n) v[i].assign (1, i);

        int w[n];
        bool exist[n], in_a[n];
        memset (exist, true, sizeof exist);

        rep(ph, n - 1) {
            memset (in_a, false, sizeof in_a);
            memset (w, 0, sizeof w);
            for (int it=0, prev; it < n-ph; ++it) {
                int sel = -1;
                rep(i, n) if (exist[i] && !in_a[i] && (sel == -1 || w[i] > w[sel])) sel = i;
                if (it == n - ph - 1) {
                    if (w[sel] < bestCost) bestCost = w[sel], bestCut = v[sel];
                    v[prev].insert (v[prev].end(), v[sel].begin(), v[sel].end());
                    rep(i, n) g[prev][i] = g[i][prev] += g[sel][i];
                    exist[sel] = false;
                }
                else {
                    in_a[sel] = true;
                    rep(i, n) w[i] += g[sel][i];
                    prev = sel;
                }
            }
        }
    }
};




signed main() {
    IO;

    int n, m; cin >> n >> m;
    vvi g(n, vi(n));
    rep(i, n) rep(j, n) g[i][j] = 0;
    rep(i, m) {
        int a, b; cin >> a >> b; --a, --b;
        g[a][b] = 1, g[b][a] = 1;
    }

    GlobalMincut mc(n, g);
    mc.run();
    cout << mc.bestCost;
}
