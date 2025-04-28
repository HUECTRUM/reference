#include <bits/stdc++.h>
using namespace std;

#define int long long int

struct BipartiteMatching {
    int n, m;
    vector<vector<int>> g;
    vector<int> match, paired;

    BipartiteMatching(int n, int m): n(n), m(m), g(n), paired(n), match(m, -1) {}
    BipartiteMatching(int n, int m, vector<vector<int>> const &g): n(n), m(m), g(g), paired(n), match(m, -1) {}

    void add(int a, int b) { g[a].push_back(b); }

    vector<size_t> ptr;
    bool kuhn(int v) {
        for (size_t &i = ptr[v]; i < g[v].size(); i++) {
            int &u = match[g[v][i]];
            if(u == -1 || (dist[u] == dist[v] + 1 && kuhn(u))) {
                u = v;
                return paired[v] = true;
            }
        }
        return false;
    }

    vector<int> dist;
    bool bfs() {
        dist.assign(n, n);
        int que[n];
        int st = 0, fi = 0;

        for (int v = 0; v < n; ++v) if (!paired[v]) dist[v] = 0, que[fi++] = v;

        bool rep = false;
        while(st < fi) {
            int v = que[st++];
            for(auto e: g[v]) {
                int u = match[e];
                rep |= u == -1;
                if (u != -1 && dist[v] + 1 < dist[u]) dist[u] = dist[v] + 1, que[fi++] = u;
            }
        }
        return rep;
    }

    vector<pair<int, int>> run() {
        while(bfs()) {
            ptr.assign(n, 0);
            for (int v = 0; v < n; ++v) if (!paired[v]) kuhn(v);
        }
        vector<pair<int, int>> ans;
        for (int u = 0; u < m; ++u) if (match[u] != -1) ans.emplace_back(match[u], u);
        return ans;
    }
};

signed main() {
    ios_base::sync_with_stdio(false); cin.tie(NULL); cout.tie(NULL);

    int l, r, m, a, b; cin >> l >> r >> m;
    vector<vector<int>> g(l);
    for (int i = 0; i < m; ++i) cin >> a >> b, g[a].push_back(b);

    BipartiteMatching bm(l, r, g);
    vector<pair<int, int>> ans = bm.run();

    cout << ans.size() << "\n";
    for (int i = 0; i < (int) ans.size(); ++i) cout << ans[i].first << " " << ans[i].second << "\n";
}
