#include <bits/stdc++.h>
using namespace std;


struct BiconCompr {
    int vCnt, timer = 0;
    vector<vector<int>> g, eId, cG;
    vector<int> brMark, used, tin, low, compSz, rootMapping;

    void init(vector<vector<int>> &graph, vector<vector<int>> &edges, int n, int m) {
        vCnt = n;
        g = graph; eId = edges; cG = vector<vector<int>>(n);
        used = tin = low = compSz = rootMapping = vector<int>(n); brMark = vector<int>(m);
    }

    void dfsMark(int v, int p = -1) {
        used[v] = 1, tin[v] = low[v] = timer++;

        for (int i = 0; i < (int)g[v].size(); ++i) {
            int to = g[v][i];
            if (to == p) continue;
            else if (used[to]) low[v] = min(low[v], tin[to]);
            else {
                dfsMark(to, v);
                low[v] = min(low[v], low[to]);
                if (low[to] > tin[v]) brMark[eId[v][i]] = 1;
            }
        }
    }

    void compr(int v, int curRoot) {
        used[v] = 1, compSz[curRoot]++, rootMapping[v] = curRoot;

        for (int i = 0; i < (int)g[v].size(); ++i) {
            int to = g[v][i], mark = brMark[eId[v][i]];
            if (!used[to]) {
                if (!mark) compr(to, curRoot);
                else {
                    cG[curRoot].push_back(to), cG[to].push_back(curRoot);
                    compr(to, to);
                }
            }
        }
    }

    void run() { dfsMark(0), used.assign(vCnt, 0), compr(0, 0); }
};