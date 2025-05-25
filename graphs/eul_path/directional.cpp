#include <bits/stdc++.h>
using namespace std;


struct EulRes {
    bool exists;
    bool connected;
    vector<int> nodes;
    vector<int> edges;
};

struct DirEulPath {
    int n, m;
    vector<vector<pair<int, int>>> g;
    vector<int> inDeg, outDeg, used;
    int st = -1, en = -1;
    bool cycExists = true, pathExists = true;
    EulRes res = {true, true, {}, {}};

    DirEulPath(vector<vector<pair<int, int>>> g) : n(g.size()), g(g), inDeg(n), outDeg(n), m(0) { }

    void runChecks() {
        for (int i = 0; i < n; ++i) for (auto &[to, _]: g[i]) inDeg[to]++, outDeg[i]++, m++;

        int stCnt = 0, enCnt = 0;
        for (int i = 0; i < n; ++i) {
            if (inDeg[i] == outDeg[i]) continue;
            if (inDeg[i] - outDeg[i] == 1) ++enCnt, en = i;
            else if (outDeg[i] - inDeg[i] == 1) ++stCnt, st = i;
            else cycExists = false, pathExists = false;
        }
        if (!stCnt && !enCnt) cycExists = true;
        else {
            cycExists = false;
            if (stCnt == 1 && enCnt == 1) pathExists = true;
            else pathExists = false;
        }
        used = vector<int>(m);
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

    int findStart() {
        if (st != -1) return st;
        auto it = std::find_if(outDeg.begin(), outDeg.end(), [](int d){ return d > 0; });
        return it == outDeg.end() ? 0 : it - outDeg.begin();
    }

    void getCycle(int v0 = 0) { runEul(v0, true); }
    void getPath(int v0 = 0) { runEul(v0, false); }

    void runEul(int v0 = 0, bool forceCyc = false) {
        if (!cycExists && !pathExists) return void(res = {false});
        if (cycExists) st = v0;
        else {
            if (forceCyc || v0 != st) return void(res = {false});
        }

        if (!m) {
            res = {true, n == 0, {v0}, {}};
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
        g[a].push_back({b, i});
    }
    DirEulPath ep(g);
    ep.runChecks();

    if (ep.cycExists || !ep.pathExists || ep.st != 0 || ep.en != n - 1) {
        cout << "IMPOSSIBLE";
        return 0;
    }

    ep.getPath(0);
    vector<int> ans = ep.res.nodes;
    if (!ep.fullExists()) cout << "IMPOSSIBLE";
    else for (auto &t: ans) cout << t + 1 << " ";
}