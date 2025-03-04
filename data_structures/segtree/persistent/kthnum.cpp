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
ll firstGeq(vll &v, ll x) { return *std::lower_bound(v.begin(), v.end(), x); }
ll firstGreater(vll &v, ll x) { return *std::upper_bound(v.begin(), v.end(), x); }
ll firstLess(vll &v, ll x) { auto ptr = std::lower_bound(v.begin(), v.end(), x); --ptr; return *ptr; }
ll firstLeq(vll &v, ll x) { auto ptr = std::upper_bound(v.begin(), v.end(), x); --ptr; return *ptr; }
int indGeq(vll &v, ll x) { return std::lower_bound(v.begin(), v.end(), x) - v.begin(); }
int indGreater(vll &v, ll x) { return std::upper_bound(v.begin(), v.end(), x) - v.begin(); }
int indLess(vll &v, ll x) { return std::lower_bound(v.begin(), v.end(), x) - v.begin() - 1; }
int indLeq(vll &v, ll x) { return std::upper_bound(v.begin(), v.end(), x) - v.begin() - 1; }

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

ll ndivto(ll n, ll k) { return n / k; }
ll ndivfrom(ll n, ll k) { return ndivto(n, k + 1) + 1; }

typedef tree<ll, null_type, less_equal<>, rb_tree_tag, tree_order_statistics_node_update> oSet;


//////////////////////////////////////////////////////////////////////////
#define int long long int
#define Mint modint998244353
#define vmint vector<modint998244353>


const int MAXN = 200010;


struct node {
    node *l, *r;
    ll cnt;

    node (ll val): l(nullptr), r(nullptr), cnt(val) {}
    node(node *l, node *r) : l(l), r(r), cnt((l ? l->cnt : 0) + (r ? r->cnt : 0)) {}
};

node* build(int tl, int tr) {
    if (tl == tr) return new node(0);

    int tm = (tl + tr) >> 1;
    return new node(build(tl, tm), build(tm + 1, tr));
}

int query(node *lNode, node *rNode, int k, int tl, int tr) {
    if (tl == tr) return tl;

    int tm = (tl + tr) >> 1;
    int cntL = rNode->l->cnt - lNode->l->cnt;
    if (cntL >= k) return query(lNode->l, rNode->l, k, tl, tm);
    else return query(lNode->r, rNode->r, k - cntL, tm + 1, tr);
}


node* upd(node* prev, int pos, int tl, int tr) {
    if (tl == tr) return new node(prev->cnt + 1);

    int tm = (tl + tr) >> 1;
    if (pos <= tm) return new node(upd(prev->l,pos, tl, tm), prev->r);
    else return new node(prev->l, upd(prev->r, pos, tm + 1, tr));
}

vector<node*> roots(4 * MAXN);
int totalRoots = 0;

signed main() {
    IO;

    int n, q; cin >> n >> q;
    vi v(n + 1), allCoords; reps(i, 1, n + 1) cin >> v[i], allCoords.pb(v[i]);

    vectorCoordinateCompression(allCoords);


    roots[totalRoots++] = build(0, n - 1);
    reps(i, 1, n + 1) {
        int comprIdx = getVectorCompressed(v[i], allCoords);
        roots[totalRoots++] = upd(roots[totalRoots - 1], comprIdx, 0, n - 1);
    }

    rep(i, q) {
        int l, r, x; cin >> l >> r >> x;
        int idx = query(roots[l - 1], roots[r], x, 0, n - 1);
        cout << allCoords[idx] << "\n";
    }
}