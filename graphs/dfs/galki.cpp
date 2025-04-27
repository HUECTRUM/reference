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