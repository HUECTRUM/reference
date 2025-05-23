#include <bits/stdc++.h>
using namespace std;

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

    int buildTr(vector<int> &allVs) {
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

