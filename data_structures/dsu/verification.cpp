#include <bits/stdc++.h>
using namespace std;

struct BridgesDSU {
    vector<int> par, dsu_2cc, dsu_cc, size_cc;
    int bridges = 0, lcaCnt = 0;
    vector<int> visitMark;

    void init(int n) {
        par = dsu_2cc = dsu_cc = size_cc = visitMark = vector<int>(n);
        for (int i = 0; i < n; ++i) dsu_2cc[i] = dsu_cc[i] = i, size_cc[i] = 1, par[i] = -1;
    }

    int find_2cc(int v) {
        if (v == -1) return -1;
        return dsu_2cc[v] == v ? v : (dsu_2cc[v] = find_2cc(dsu_2cc[v]));
    }

    int find_cc(int v) {
        v = find_2cc(v);
        return dsu_cc[v] == v ? v : (dsu_cc[v] = find_cc(dsu_cc[v]));
    }

    void reroot(int v) {
        int root = v, child = -1;
        while (v != -1) {
            int p = find_2cc(par[v]);
            par[v] = child, dsu_cc[v] = root;
            child = v, v = p;
        }
        size_cc[root] = size_cc[child];
    }

    void pathMerge(int a, int b) {
        ++lcaCnt;
        vector<int> pathA, pathB;
        int lca = -1;

        while (lca == -1) {
            auto oneUp = [&](int &x, vector<int> &path) -> bool {
                if (x == -1) return false;
                x = find_2cc(x); path.push_back(x);
                if (visitMark[x] == lcaCnt) {
                    lca = x; return true;
                }
                visitMark[x] = lcaCnt, x = par[x];
                return false;
            };

            bool got = oneUp(a, pathA) | oneUp(b, pathB);
            if (got) break;
        }

        auto markLca = [&](vector<int> &path) -> void {
            for (auto &v: path) {
                dsu_2cc[v] = lca;
                if (v == lca) return;
                --bridges;
            }
        };
        markLca(pathA), markLca(pathB);
    }

    void addEdge(int a, int b) {
        a = find_2cc(a), b = find_2cc(b);
        if (a == b) return;

        int ca = find_cc(a), cb = find_cc(b);
        if (ca == cb) return void(pathMerge(a, b));

        ++bridges;
        if (size_cc[ca] > size_cc[cb]) swap(a, b), swap(ca, cb);
        reroot(a);
        par[a] = dsu_cc[a] = b, size_cc[cb] += size_cc[a];
    }
};


signed main() {
    ifstream cin("bridges.in"); ofstream cout("bridges.out");
    ios_base::sync_with_stdio(false); cin.tie(NULL); cout.tie(NULL);
    int n, m; cin >> n >> m;

    BridgesDSU ds = BridgesDSU();
    ds.init(n);

    int a, b;
    for (int i = 0; i < m; ++i) {
        cin >> a >> b; --a, --b;
        ds.addEdge(a, b);
    }

    int k; cin >> k;
    vector<int> ans;
    for (int i = 0; i < k; ++i) {
        cin >> a >> b; --a, --b;
        ds.addEdge(a, b);
        ans.push_back(ds.bridges);
    }

    for (int i = 0; i < (int) ans.size(); ++i) cout << ans[i] << "\n";
}
