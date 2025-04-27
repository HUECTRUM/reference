#include <bits/stdc++.h>
using namespace std;


template <int LOG = 20, int MAXN = 400010> struct LCA_RMQ {
    vector<int> lg;
    vector<vector<int>> g;
    int root;
    vector<int> height, euler, first, eulH, par;

    int st[LOG + 1][2 * MAXN + 1];

    LCA_RMQ(vector<vector<int>> const &g, int root = 0): g(g), lg(2 * MAXN + 1), root(root), height(g.size()), first(g.size()), par(g.size()) {
        lg[1] = 0;
        for (int i = 2; i <= 2 * MAXN; ++i) lg[i] = lg[i / 2] + 1;
    }

    void dfs(int v, int p = -1, int h = 0) {
        height[v] = h, first[v] = euler.size();
        euler.push_back(v); par[v] = p;

        for (auto &to: g[v]) if (to != p) dfs(to, v, h + 1), euler.push_back(v);
    }

    void buildEulerHeights() {
        int sz = euler.size();
        eulH = vector<int>(sz);
        for (int i = 0; i < sz; ++i) eulH[i] = height[euler[i]];
    }

    void buildSparse() {
        int sz = euler.size();
        for (int i = 0; i < sz; ++i) st[0][i] = i;

        for (int i = 1; i <= LOG; ++i) for (int j = 0; j + (1 << i) <= sz; j++) {
                int minInd1 = st[i - 1][j], minInd2 = st[i - 1][j + (1 << (i - 1))];
                st[i][j] = eulH[minInd1] < eulH[minInd2] ? minInd1 : minInd2;
            }
    }

    int getMinIndex(int l, int r) {
        int i = lg[r - l + 1], first = st[i][l], second = st[i][r - (1 << i) + 1];
        return eulH[first] < eulH[second] ? first : second;
    }

    int lca(int a, int b) {
        long long l = first[a], r = first[b];
        if (l > r) swap(l, r);
        return euler[getMinIndex(l, r)];
    }

    void run() { dfs(root), buildEulerHeights(), buildSparse(); }
};