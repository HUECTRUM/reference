#include <bits/stdc++.h>
using namespace std;

#define int long long int

struct event { int type, a, b, t; };
struct addEdges {int a, b, l, r; };
struct DynConn {
    int n, q;
    vector<vector<pair<int, int>>> stree;
    vector<int> par, sz, queryFilter;
    stack<pair<int, int>> updates;
    vector<int> answers;
    int comps;

    int getAnswer() { return comps; }

    void initDsu(int cnt) {
        par = sz = vector<int>(n, 1); comps = cnt;
        iota(par.begin(), par.end(), 0);
    }

    int find(int x) { return x == par[x] ? x : find(par[x]); }

    bool unite(int x, int y) {
        x = find(x), y = find(y);
        if (x == y) return false;

        if (sz[x] < sz[y]) swap(x, y);

        updates.push({x, y});
        par[y] = x; sz[x] += sz[y]; --comps;
        return true;
    }

    void rollback() {
        auto [x, y] = updates.top(); updates.pop();
        par[y] = y; sz[x] -= sz[y]; ++comps;
    }

    void add(int l, int r, int a, int b, int v, int tl, int tr) {
        if (l > r) return;
        if (l == tl && r == tr) return void(stree[v].push_back({a, b}));

        int tm = (tl + tr) >> 1;
        add(l, min(r, tm), a, b, v << 1, tl, tm);
        add(max(l, tm + 1), r, a, b, v << 1 | 1, tm + 1, tr);
    }

    void add(int l, int r, int a, int b) { add(l, r, a, b, 1, 0, q - 1); }

    void dfs(int v, int tl, int tr) {
        int updA = 0;
        for (auto [x, y]: stree[v]) {
            if (unite(x, y)) ++updA;
        }

        if (tl == tr) answers[tl] = getAnswer();
        else {
            int tm = (tl + tr) >> 1;
            dfs(v << 1, tl, tm); dfs(v << 1 | 1, tm + 1, tr);
        }

        for (int i = 0; i < updA; ++i) rollback();
    }

    void dfs() { dfs(1, 0, q - 1); }

    void init(int n, int q, vector<event> events, vector<int> queryFilter) {
        this->n = n, this->q = q; this->queryFilter = queryFilter;
        initDsu(n); stree = vector<vector<pair<int, int>>>(4 * q); answers = vector<int>(q);

        map<pair<int, int>, int> addTime;
        for (int i = 0; i < (int) events.size(); ++i) {
            auto [tp, a, b, t] = events[i];
            if (a > b) swap(a, b);

            if (tp == 1) addTime[{a, b}] = t;
            else {
                int tL = addTime[{a, b}];
                int tR = t - 1;
                add(tL, tR, a, b);
                addTime.erase({a, b});
            }
        }
        for (auto [pair, tL]: addTime) add(tL, q - 1, pair.first, pair.second);
    }

    void init(int n, int q, vector<event> events) {
        vector<int> queryFilter(q);
        iota(queryFilter.begin(), queryFilter.end(), 0);
        init(n, q, events, queryFilter);
    }

    void init(int n, int q, vector<addEdges> edges, vector<int> queryFilter) {
        this->n = n, this->q = q; this->queryFilter = queryFilter;
        initDsu(n); stree = vector<vector<pair<int, int>>>(4 * q); answers = vector<int>(q);
        for (auto &[a, b, l, r]: edges) add(l, r, a, b);
    }

    void init(int n, int q, vector<addEdges> edges) {
        vector<int> queryFilter(q);
        iota(queryFilter.begin(), queryFilter.end(), 0);
        init(n, q, edges, queryFilter);
    }

    void run() { dfs(); }

    vector<int> getResults() {
        vector<int> fin;
        for (int i = 0; i < (int) queryFilter.size(); ++i) fin.push_back(answers[queryFilter[i]]);
        return fin;
    }
};

vector<addEdges> toAddEdges(vector<pair<int, int>> &edges, vector<vector<pair<int, int>>> &times, int m) {
vector<addEdges> events;
for (int i = 0; i < (int) edges.size(); ++i) for (int j = 0; j < (int) times[i].size(); ++j) {
events.push_back({edges[i].first, edges[i].second, times[i][j].first, times[i][j].second});
}
return events;
}

signed main() {
    ifstream cin("disconnected.in"); ofstream cout("disconnected.out");
    ios_base::sync_with_stdio(false); cin.tie(NULL); cout.tie(NULL);

    int n, m; cin >> n >> m;
    vector<pair<int, int>> edges(m);
    for (int i = 0; i < m; ++i) {
        int a, b; cin >> a >> b; --a, --b;
        edges[i] = {a, b};
    }

    int k; cin >> k;
    vector<vector<pair<int, int>>> times(m);
    for (int i = 0; i < m; ++i) times[i].push_back({0, k});

    for (int i = 1; i <= k; ++i) {
        int sz; cin >> sz;
        for (int j = 0; j < sz; ++j) {
            int x; cin >> x; --x;
            auto [l, r] = times[x].back(); times[x].pop_back();
            times[x].push_back({l, i - 1}); times[x].push_back({i + 1, k});
        }
    }

    vector<addEdges> aE = toAddEdges(edges, times, m);

    DynConn dc = DynConn();
    dc.init(n, k + 1, aE);
    dc.run();
    vector<int> ans = dc.getResults();

    for (int i = 1; i <= k; ++i) {
        if (ans[i] > 1) cout << "Disconnected" << endl;
        else cout << "Connected" << endl;
    }
}