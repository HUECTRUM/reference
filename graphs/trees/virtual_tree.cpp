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



ll ndivto(ll n, ll k) { return n / k; }
ll ndivfrom(ll n, ll k) { return ndivto(n, k + 1) + 1; }

typedef tree<ll, null_type, less_equal<>, rb_tree_tag, tree_order_statistics_node_update> oSet;


//////////////////////////////////////////////////////////////////////////
#define int long long int
#define Mint modint998244353
#define vmint vector<modint998244353>





struct VirtualTree {
    int n, grvCnt = 0, timer = 0, LOG = 20;
    vector<int> tin, tout, dpth, subtreeSz, grv;
    vector<vector<int>> g, groups, binL, virTr;;

    void dfs(int v, int p = -1) {
        tin[v] = ++timer;
        if (p != -1) {
            binL[0][v] = p;
            for (int i = 1; i < LOG; ++i) binL[i][v] = binL[i - 1][binL[i - 1][v]];
        }
        for (auto &to: g[v]) if (to != p) dpth[to] = dpth[v] + 1, dfs(to, v);
        tout[v] = ++timer;
    }

    bool isAnc(int u, int v) { return tin[u] <= tin[v] && tout[u] >= tout[v]; }

    int lca(int a, int b) {
        if (isAnc(a, b)) return a;
        if (isAnc(b, a)) return b;
        for (int i = LOG - 1; i >= 0; --i) if (!isAnc(binL[i][a], b)) a = binL[i][a];
        return binL[0][a];
    }

    VirtualTree(vector<vector<int>> &g, int root = 0, int lg = 20): n(g.size()), g(g), LOG(lg) {
        groups = virTr = vector<vector<int>>(n);
        binL = vector<vector<int>>(LOG, vector<int>(n));
        tin = tout = dpth = grv = subtreeSz = vector<int>(n);

        dfs(root);
    }

    int buildTr(vi &allVs) {
        stack<int> vSt; vSt.push(allVs[0]);
        for (int i = 1; i < allVs.size(); ++i) {
            while (vSt.size() >= 2 && !isAnc(vSt.top(), allVs[i])) {
                int lst = vSt.top(); vSt.pop();
                virTr[vSt.top()].push_back(lst);
            }
            vSt.push(allVs[i]);
        }

        while (vSt.size() >= 2) {
            int lst = vSt.top(); vSt.pop();
            virTr[vSt.top()].push_back(lst);
        }

        return vSt.top();
    }

    pair<int, vector<int>> buildTree(vector<int> &vert) {
        grvCnt = vert.size();
        for (auto &v: vert) grv[v] = 1;

        vector<int> allVs = vert;
        std::sort(allVs.begin(), allVs.end(), [&](int x, int y) { return tin[x] < tin[y]; });
        for (int i = 0; i < grvCnt - 1; ++i) allVs.push_back(lca(allVs[i], allVs[i + 1]));
        std::sort(allVs.begin(), allVs.end(), [&](int x, int y) { return tin[x] < tin[y]; });
        allVs.erase(unique(allVs.begin(), allVs.end()), allVs.end());

        return {buildTr(allVs), allVs};
    }

    void cleanup(vector<int> &allVs, vector<int> &vert) {
        for (auto &x: allVs) virTr[x].clear();
        for (auto &v: vert) grv[v] = 0;
    }
};

vi subtreeSz;
ll slvTree(VirtualTree &vtr, int v, int p = -1) {
    ll vAns = 0;

    subtreeSz[v] = vtr.grv[v];
    repe(to, vtr.virTr[v]) if (to != p) {
            vAns += slvTree(vtr, to, v);
            subtreeSz[v] += subtreeSz[to];
        }
    if (p != -1) {
        ll len = vtr.dpth[v] - vtr.dpth[p];
        vAns += len * subtreeSz[v] * (vtr.grvCnt - subtreeSz[v]);
    }
    return vAns;
}

signed main() {
    IO;

    int a, b, n; cin >> n;

    vvi g(n), groups(n);
    subtreeSz = vi(n);
    rep(i, n - 1) {
        cin >> a >> b; --a, --b;
        g[a].push_back(b), g[b].push_back(a);
    }
    rep(i, n) cin >> a, groups[a - 1].push_back(i);

    int ans = 0;
    VirtualTree vtr(g);
    rep(i, n) if (groups[i].size()) {
            auto [root, allVs] = vtr.buildTree(groups[i]);
            ans += slvTree(vtr, root);
            vtr.cleanup(allVs, groups[i]);
        }
    cout << ans;
}