#include <bits/stdc++.h>
using namespace std;



void vectorCoordinateCompression(vector<int> &v) {
    std::sort(v.begin(), v.end());
    v.erase(std::unique(v.begin(), v.end()), v.end());
}

int getVectorCompressed(int val, vector<int> &v) { return lower_bound(v.begin(), v.end(), val) - v.begin(); }

template<typename R> struct s2lContainer {
    virtual void add(int v) = 0;
    virtual void remove(int v) = 0;
    virtual R getResult(int v) = 0;
};

struct UniqueOps: s2lContainer<int> {
    vector<int> cnt, col;
    int uCnt = 0;

    UniqueOps(vector<int> const &col) : cnt(col.size()), col(col) { }

    void add(int v) {
        if (!cnt[col[v]]) ++uCnt;
        cnt[col[v]]++;
    }

    void remove(int v) {
        if (cnt[col[v]] == 1) --uCnt;
        cnt[col[v]]--;
    }

    int getResult(int v) { return uCnt; }
};

template<typename R> struct Sack {
    s2lContainer<R> &ds;
    int n;
    const vector<vector<int>> &g;
    vector<int> sz, st, ft, ver, ans;
    int timer = 0;

    Sack(const vector<vector<int>> &g, s2lContainer<R> &ds): ds(ds), n(g.size()), g(g), sz(n), ans(n), st(n), ft(n), ver(n) {}

    void dfsSz(int v, int p = -1) {
        st[v] = timer, sz[v] = 1;
        ver[timer++] = v;
        for (auto &to: g[v]) if (to != p) dfsSz(to, v), sz[v] += sz[to];
        ft[v] = timer;
    }

    void dfs(int v, int p, bool keep) {
        int mx = -1, big = -1;
        for (auto &u: g[v]) if (u != p && sz[u] > mx) mx = sz[u], big = u;

        for (auto &u: g[v]) if (u != p && u != big) dfs(u, v, 0);
        if (big != -1) dfs(big, v, 1);

        for (auto &u: g[v]) if (u != p && u != big) {
                for (int tm = st[u]; tm < ft[u]; ++tm) ds.add(ver[tm]);
            }
        ds.add(v);
        ans[v] = ds.getResult(v);

        if (!keep) for (int tm = st[v]; tm < ft[v]; ++tm) ds.remove(ver[tm]);
    }

    vector<R> run(int root = 0) {
        dfsSz(root);
        dfs(root, -1, 1);
        return ans;
    }
};


signed main() {
    int n; cin >> n;
    vector<int> col(n);
    vector<int> allCoords;
    for (int i = 0; i < n; ++i) cin >> col[i], allCoords.push_back(col[i]);

    vectorCoordinateCompression(allCoords);
    for (int i = 0; i < n; ++i) col[i] = getVectorCompressed(col[i], allCoords);

    vector<vector<int>> g(n);
    for (int i = 0; i < n - 1; ++i) {
        int a, b; cin >> a >> b; --a, --b;
        g[a].push_back(b); g[b].push_back(a);
    }
    UniqueOps op(col);
    Sack s(g, op);
    vector<int> ans = s.run();

    for (int i = 0; i < n; ++i) cout << ans[i] << " ";
}