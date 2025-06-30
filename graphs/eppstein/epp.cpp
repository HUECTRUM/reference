#include <bits/stdc++.h>
using namespace std;
#define int long long int

struct edge { int to, w; };
const int INF = 1e18;

struct Heap {
    int key, val, rnk;
    Heap *left, *right;

    Heap(int k, int v) : key(k), val(v), rnk(1), left(nullptr), right(nullptr) { }
    Heap(int k, int v, Heap *l, Heap *r): key(k), val(v), rnk(1), left(l), right(r) { }
};

Heap* merge(Heap* a, Heap* b) {
    if (!a || !b) return !a ? b : a;
    if (a->key > b->key) swap(a, b);

    Heap* res = new Heap(a->key, a->val, a->left, merge(a->right, b));
    if (!res->left || (res->right && res->left->rnk < res->right->rnk)) swap(res->left, res->right);
    res->rnk = (res->right ? res->right->rnk : 0) + 1;
    return res;
}

inline Heap* insert(Heap *h, int k, int v) { return merge(h, new Heap(k, v)); }

template <class T> using min_heap = priority_queue<T, vector<T>, greater<T>>;
auto dij(const vector<vector<edge>> &g, int n, int s) {
    vector<int> d(n, INF), prv(n, -1);

    min_heap<pair<int, int>> q; q.emplace(d[s] = 0, s);
    while (q.size()) {
        auto [dv, v] = q.top(); q.pop();
        if (dv != d[v]) continue;

        for (auto &[to, w]: g[v]) {
            if (dv + w >= d[to]) continue;
            q.emplace(d[to] = dv + w, to); prv[to] = v;
        }
    }
    return make_pair(d, prv);
}


vector<int> epp(int n, const vector<vector<edge>> &g, int src, int dst, int k) {
    vector<vector<edge>> g_rev(n);
    for (int u = 0; u < n; ++u) for (auto [v, w] : g[u]) g_rev[v].emplace_back(u, w);

    auto [d, prv] = dij(g_rev, n, dst);
    if (d[src] == INF) return {};

    vector<vector<int>> tree(n);
    for (int v = 0; v < n; ++v) if (prv[v] != -1) tree[prv[v]].push_back(v);

    vector<Heap*> h(n, nullptr); queue<int> q({dst});
    while (q.size()) {
        int u = q.front(), seen = 0; q.pop();

        for (auto [v, w] : g[u]) {
            if (d[v] == INF) continue;

            int diff = w + d[v] - d[u];
            if (!seen && v == prv[u] && !diff) seen = 1;
            else h[u] = insert(h[u], diff, v);
        }
        for (auto v: tree[u]) h[v] = h[u], q.push(v);
    }

    vector<int> ans = {d[src]};
    if (!h[src] || k == 1) return ans;

    min_heap<pair<int, Heap*>> q1; q1.emplace(d[src] + h[src]->key, h[src]);
    while (not q1.empty() and (int) ans.size() < k) {
        auto [cd, ch] = q1.top(); q1.pop(); ans.push_back(cd);
        if (h[ch->val]) q1.emplace(cd + h[ch->val]->key, h[ch->val]);
        if (ch->left) q1.emplace(cd + ch->left->key - ch->key, ch->left);
        if (ch->right) q1.emplace(cd + ch->right->key - ch->key, ch->right);
    }
    return ans;
}



signed main() {
    ios_base::sync_with_stdio(false); cin.tie(NULL); cout.tie(NULL);

    int n, m, s, t, k; cin >> n >> m >> s >> t >> k;

    vector<vector<edge>> g(n);
    for (int i = 0; i < m; ++i) {
        int u, v, w; cin >> u >> v >> w;
        g[u].emplace_back(v, w);
    }

    auto res = epp(n, g, s, t, k);
    for (long long d : res) cout << d << '\n';
    for (int i = res.size(); i < k; ++i) cout << -1 << '\n';
}