#include <bits/stdc++.h>
using namespace std;

#define int long long int

struct event { int type, a, b, t; };
struct DynConn {
    int n, q;
    vector<vector<pair<int, int>>> stree;
    vector<int> par, sz, queryFilter;
    stack<pair<int, int>> updates;
    vector<int> answers;
    int comps;

    int getAnswer(int tl) {
        if (queryFilter[tl] == -1) return -1;
        int parQ = find(queryFilter[tl]);
        return sz[parQ];
    }

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

        if (tl == tr) answers[tl] = getAnswer(tl);
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

    void run() { dfs(); }

    vector<int> getResults() { return answers; }
};


int findSmaller(set<int> &st, int x) {
    auto ptr = st.lower_bound(x);
    if (ptr == st.begin()) return -1;
    return *(--ptr);
}

int findLarger(set<int> &st, int x) {
    auto ptr = st.upper_bound(x);
    if (ptr == st.end()) return -1;
    return *ptr;
}


struct query{ int type, x; };
signed main() {
    ios_base::sync_with_stdio(false); cin.tie(NULL); cout.tie(NULL);

    int q, k; cin >> q >> k;
    vector<int> allCoords; vector<query> queries(q);
    for (int i = 0; i < q; ++i) {
        int a, b; cin >> a >> b;
        queries[i] = {a, b}; allCoords.push_back(b);
    }

    std::sort(allCoords.begin(), allCoords.end());
    allCoords.erase(unique(allCoords.begin(), allCoords.end()), allCoords.end());

    vector<event> events;
    vector<int> questions(q, -1);

    set<int> x;
    for (int i = 0; i < (int) queries.size(); ++i) {
        auto &[type, coord] = queries[i];
        int coordInd = std::lower_bound(allCoords.begin(), allCoords.end(), coord) - allCoords.begin();

        if (type == 2) questions[i] = coordInd;
        else {
            int lInd = findSmaller(x, coordInd), rInd = findLarger(x, coordInd);
            bool exists = x.count(coordInd);
            if (lInd != -1 && coord - allCoords[lInd] <= k) events.push_back({exists ? 2 : 1, lInd, coordInd, i});
            if (rInd != -1 && allCoords[rInd] - coord <= k) events.push_back({exists ? 2 : 1, coordInd, rInd, i});
            if (lInd != -1 && rInd != -1 && allCoords[rInd] - allCoords[lInd] <= k) events.push_back({exists ? 1 : 2, lInd, rInd, i});

            if (exists) x.erase(coordInd);
            else x.insert(coordInd);
        }
    }

    DynConn dc = DynConn();
    dc.init(q, q, events, questions);
    dc.run();
    vector<int> ans = dc.getResults();
    for (int i = 0; i < q; ++i) if (questions[i] != -1) cout << ans[i] << endl;
}