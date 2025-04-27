#include <bits/stdc++.h>
using namespace std;

struct Galki {
    int n;
    vector<vector<pair<int, int>>> g;
    vector<pair<int, int>> res;
    vector<int> color;

    Galki(int n, vector<vector<pair<int, int>>> const &gr): n(n), g(gr), color(n) {}

    int dfs(int x, int pe = -1) {
        color[x] = 1;

        vector<int> edgeNums;

        for (auto &[to, edgeNum]: g[x]) {
            if (color[to] == 2 || (!color[to] && dfs(to, edgeNum))) edgeNums.push_back(edgeNum);
        }
        if (pe != -1) edgeNums.push_back(pe);

        int i = 0;
        while (i + 1 < edgeNums.size()) res.push_back({edgeNums[i], edgeNums[i + 1]}), i += 2;

        color[x] = 2;
        return i != edgeNums.size();
    }

    vector<pair<int, int>> run() {
        for (int i = 0; i < n; ++i) if (!color[i]) dfs(i);
        return res;
    }
};

signed main() {
    ios_base::sync_with_stdio(false); cin.tie(NULL); cout.tie(NULL);

    int n, m; cin >> n >> m;
    vector<vector<pair<int, int>>> g(n);
    vector<pair<int, int>> edges(m);
    for (int i = 0; i < m; ++i) {
        int a, b; cin >> a >> b; --a, --b;
        g[a].push_back({b, i}), g[b].push_back({a, i});
        edges[i] = {a, b};
    }

    Galki ga(n, g);
    vector<pair<int, int>> split = ga.run();

    vector<string> ans(m);
    for (int i = 0; i < (int)split.size(); ++i) {
        auto [l, r] = split[i];
        if (l > r) swap(l, r);
        auto [f1, f2] = edges[l];
        auto [f3, f4] = edges[r];

        if (f1 == f3) ans[l] = "x+", ans[r] = "x-";
        if (f1 == f4) ans[l] = "x+", ans[r] = "y-";
        if (f2 == f3) ans[l] = "y+", ans[r] = "x-";
        if (f2 == f4) ans[l] = "y+", ans[r] = "y-";
    }
    for (int i = 0; i < m; ++i) if (ans[i].empty()) ans[i] = "x+";
    for (int i = 0; i < m; ++i) cout << ans[i] << "\n";
}
