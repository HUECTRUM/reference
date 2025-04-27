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

vector<vector<int>> cG;
set<pair<int, int>> cArts;
vector<int> hasArts;
int dfs(int v, int target, int p = -1, int hasOnPath = 0) {
    if (hasArts[v]) hasOnPath = 1;
    if (v == target) return hasOnPath;

    int ans = 0;
    for (auto &to: cG[v]) if (to != p) {
            int bridgeArt = cArts.count({to, v});
            ans |= dfs(to, target, v, hasOnPath | bridgeArt);
        }
    return ans;
}

struct edge {int a, b, c; };

signed main() {
    ios_base::sync_with_stdio(false); cin.tie(NULL); cout.tie(NULL);

    int n, m; cin >> n >> m;
    vector<vector<int>> g(n), eId(n);
    vector<edge> edges(m);

    int a, b, c;
    for (int i = 0; i < m; ++i) {
        cin >> a >> b >> c; --a, --b;
        g[a].push_back(b), g[b].push_back(a);
        eId[a].push_back(i), eId[b].push_back(i);
        edges[i] = {a, b, c};
    }

    BiconCompr compr;
    compr.init(g, eId, n, m);
    compr.run();

    vector<int> rtMap = compr.rootMapping;
    hasArts = vector<int>(n);
    cG = compr.cG;


    for (int i = 0; i < m; ++i) {
        int l = edges[i].a, r = edges[i].b, isArt = edges[i].c;
        int rtL = rtMap[l], rtR = rtMap[r];
        if (rtL == rtR && isArt) hasArts[rtL] = 1;
        if (rtL != rtR && isArt) cArts.insert({rtL, rtR}), cArts.insert({rtR, rtL});
    }

    int st, end; cin >> st >> end; --st, --end;
    st = rtMap[st], end = rtMap[end];
    if (st == end) {
        cout << (hasArts[st] ? "YES": "NO");
        return 0;
    } else {
        int ans = dfs(st, end);
        cout << (ans ? "YES": "NO");
    }
}
