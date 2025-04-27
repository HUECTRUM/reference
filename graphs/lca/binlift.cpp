#include <bits/stdc++.h>
using namespace std;

struct BinLift {
    vector<vector<int>> up, g;
    vector<int> tin, tout;
    int timer = 0, lg;

    void dfs(int v, int p = -1) {
        tin[v] = ++timer;

        if (p == -1) for (int i = 0; i < lg; ++i) up[v][i] = v;
        else {
            up[v][0] = p;
            for (int i = 1; i < lg; ++i) up[v][i] = up[up[v][i - 1]][i - 1];
        }

        for (auto &to: g[v]) if (to != p) dfs(to, v);

        tout[v] = ++timer;
    }

    BinLift(vector<vector<int>> const &g, int LOG = 20, int root = 0): g(g),
                                                                       up(g.size(), vector<int>(LOG)), tin(g.size()), tout(g.size()), lg(LOG) { dfs(root); }

    bool isAnc(int u, int v) { return tin[u] <= tin[v] && tout[u] >= tout[v]; }

    int lca(int u, int v) {
        if (isAnc(u, v)) return u;
        if (isAnc(v, u)) return v;

        for (int i = lg - 1; i >= 0; --i) {
            int upU = up[u][i];
            if (!isAnc(upU, v)) u = upU;
        }
        return up[u][0];
    }
};