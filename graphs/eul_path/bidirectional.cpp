#include <bits/stdc++.h>
using namespace std;


struct EulRes {
    bool exists;
    bool connected;
    vector<int> nodes;
    vector<int> edges;
};

struct EulPath {
    int n, m;
    vector<vector<pair<int, int>>> g;
    vector<int> deg, used;
    int st = -1, en = -1;
    bool cycExists = true, pathExists = true;
    EulRes res = {true, true, {}, {}};

    EulPath(vector<vector<pair<int, int>>> g) : n(g.size()), g(g), deg(n), m(0) { }

    void runChecks() {
        for (int i = 0; i < n; ++i) for (auto &[to, _]: g[i]) deg[to]++;

        int cnt = 0;
        for (int i = 0; i < n; ++i) {
            m += deg[i];

            if (deg[i] % 2 == 0) continue;

            ++cnt;
            if (st == -1) st = i;
            else if (en == -1) en = i;
        }
        cycExists = (cnt == 0), pathExists = (cnt == 0 || cnt == 2);
        m /= 2; used = vector<int>(m);
    }

    void dfs(int v) {
        while (g[v].size()) {
            auto [to, id] = g[v].back(); g[v].pop_back();
            if (used[id]) continue;

            used[id] = 1;
            dfs(to); res.edges.push_back(id);
        }
        res.nodes.push_back(v);
    }

    void getCycle(int v0 = 0) { runEul(v0, true); }
    void getPath(int v0 = 0) { runEul(v0, false); }

    void runEul(int v0 = 0, bool forceCyc = false) {
        if (!cycExists && !pathExists) return void(res = {false});
        if (cycExists) st = v0;
        else {
            if (forceCyc) return void(res = {false});
            if (v0 != st && v0 != en) return void(res = {false});
            if (v0 == en) swap(st, en);
        }

        if (!m) {
            res = {n == 0, n == 0, {v0}, {}};
            return;
        }

        dfs(st);
        if (res.edges.size() != m) res.connected = false;
        std::reverse(res.nodes.begin(), res.nodes.end());
        std::reverse(res.edges.begin(), res.edges.end());
    }

    bool fullExists() { return res.exists && res.connected; }
};


signed main() {
    int n, m; cin >> n >> m;
    vector<vector<pair<int, int>>> g(n);
    for (int i = 0; i < m; ++i) {
        int a, b; cin >> a >> b; --a, --b;
        g[a].push_back({b, i}); g[b].push_back({a, i});
    }
    EulPath ep(g);
    ep.runChecks();
    ep.getCycle(0);
    vector<int> ans = ep.res.nodes;
    if (!ep.fullExists()) cout << "IMPOSSIBLE";
    else for (auto &t: ans) cout << t + 1 << " ";
}