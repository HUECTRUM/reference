#include <bits/stdc++.h>
using namespace std;

template<typename T> inline void chmax(T &a, T b) { a = max(a, b); }
template<typename T> inline void chmin(T &a, T b) { a = min(a, b); }

template<typename R, typename D> struct s2lContainer {
    virtual void addVertex(int v, D x) = 0;
    virtual void merge(int ch, s2lContainer &other, int v, D x) = 0;
    virtual R getResult(int v) = 0;
};

const int INF = 1e9;
struct LISContainer : s2lContainer<int, int> {
    vector<int> inc, dec;
    int best = 0;

    void addVertex(int v, int x) {
        auto it = lower_bound(inc.begin(), inc.end(), x);
        if (it == inc.end()) inc.push_back(x);
        else *it = x;

        it = lower_bound(dec.begin(), dec.end(), x, greater<>());
        if (it == dec.end()) dec.push_back(x);
        else *it = x;

        chmax(best, (int)max(inc.size(), dec.size()));
    }

    void merge(int ch, s2lContainer<int,int> &otherBase, int v, int x) {
        auto& other = static_cast<LISContainer&>(otherBase);

        for (int i = 0; i < other.dec.size(); ++i) {
            int pos = lower_bound(inc.begin(), inc.end(), other.dec[i]) - inc.begin();
            if (pos) chmax(best, i + 1 + pos);
        }
        for (int i = 0; i < other.inc.size(); ++i) {
            int pos = lower_bound(dec.begin(), dec.end(), other.inc[i], greater<>()) - dec.begin();
            if (pos) chmax(best, i + 1 + pos);
        }

        if (inc.size() < other.inc.size()) inc.resize(other.inc.size(), INF);
        for (int i = 0; i < other.inc.size(); ++i) chmin(inc[i], other.inc[i]);

        if (dec.size() < other.dec.size()) dec.resize(other.dec.size(), -INF);
        for (int i = 0; i < other.dec.size(); ++i) dec[i] = max(dec[i], other.dec[i]);

        chmax(best, (int)max(inc.size(), dec.size()));
        addVertex(v, x);
    }

    int getResult(int v) { return best; }
};


template<typename R, typename D, class Bucket> struct S2L {
    int n;
    const vector<vector<int>>& g;
    const vector<D>& val;
    vector<int> sz;
    vector<R> ans;
    vector<Bucket*> buckets;

    S2L(const vector<vector<int>>& g, const vector<D>& val): n(g.size()), g(g), val(val), sz(n, 1), buckets(n), ans(n) { }

    void dfsSz(int v, int p = -1) {
        for (int u: g[v]) if (u != p) dfsSz(u, v), sz[v] += sz[u];
    }


    void dfs(int v, int p) {
        int big = -1, mx = -1;
        for (int u : g[v]) if (u != p && sz[u] > mx) mx = sz[u], big = u;

        for (int u : g[v]) if (u != p && u != big) dfs(u, v);

        if (big != -1) dfs(big, v), buckets[v] = buckets[big];
        else buckets[v] = new Bucket();

        buckets[v]->addVertex(v, val[v]);

        for (int u : g[v]) if (u != p && u != big) buckets[v]->merge(u, *buckets[u], v, val[v]);

        ans[v] = buckets[v]->getResult(v);
    }

    vector<R> run(int root = 0) {
        dfsSz(root);
        dfs(root, -1);
        return ans;
    }
};

int main() {
    ios::sync_with_stdio(false); cin.tie(nullptr);

    int n; cin >> n;
    vector<int> a(n); for (int i = 0; i < n; ++i) cin >> a[i];
    vector<vector<int>> g(n);
    for (int i = 0; i < n - 1; ++i) {
        int u, v; cin >> u >> v; --u; --v;
        g[u].push_back(v); g[v].push_back(u);
    }

    S2L<int, int, LISContainer> runner(g, a);
    vector<int> ans = runner.run();

    int fin = 0;
    for (auto &x: ans) chmax(fin, x);
    cout << fin;
}