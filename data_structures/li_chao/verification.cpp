#include <bits/stdc++.h>
using namespace std;

#define int long long int



struct lchUpdate { int v, ver; pair<int, int> val; };
template<int INF = 5000000000000000000> struct LiChaoMax {
    int n;
    vector<int> coords;
    vector<pair<int, int>> stree;
    stack<lchUpdate> updates;

    LiChaoMax(vector<int> &c) : coords(c), n(c.size() - 1), stree(4 * c.size() - 4, {0, -INF}) {}

    int getVectorCompressed(int val, vector<int> &v) { return lower_bound(v.begin(), v.end(), val) - v.begin(); }

    int eval(pair<int, int> line, int x) { return line.first * coords[x] + line.second; }

    int query(int x, int v, int tl, int tr) {
        if (tl + 1 == tr) return eval(stree[v], x);

        int tm = (tl + tr) >> 1;
        if (x < tm) return max(eval(stree[v], x), query(x, v << 1, tl, tm));
        else return max(eval(stree[v], x), query(x, v << 1 | 1, tm, tr));
    }

    int query(int x) { return query(x, 1, 0, n); }

    int queryUncompr(int x) { return query(getVectorCompressed(x, coords)); }

    void insert(pair<int, int> line, int version, int v, int tl, int tr) {
        int tm = (tl + tr) >> 1;
        bool evalL = eval(line, tl) > eval(stree[v], tl), evalM = eval(line, tm) > eval(stree[v], tm);

        if (evalM) updates.push({v, version, stree[v]}), swap(line, stree[v]);
        if (tl + 1 == tr) return;

        if (evalL != evalM) insert(line, version, v << 1, tl, tm);
        else insert(line, version, v << 1 | 1, tm, tr);
    }

    void insert(pair<int, int> line, int version) { insert(line, version, 1, 0, n); }

    void rollbackTo(int toVer) {
        while (updates.size() && updates.top().ver >= toVer) {
            auto [v, _, val] = updates.top(); updates.pop();
            stree[v] = val;
        }
    }
};

template<int INF = 5000000000000000000> struct LiChaoMin {
    int n;
    vector<int> coords;
    vector<pair<int, int>> stree;
    stack<lchUpdate> updates;

    LiChaoMin(vector<int> &c) : coords(c), n(c.size() - 1), stree(4 * c.size() - 4, {0, INF}) {}

    int getVectorCompressed(int val, vector<int> &v) { return lower_bound(v.begin(), v.end(), val) - v.begin(); }

    int eval(pair<int, int> line, int x) { return line.first * coords[x] + line.second; }

    int query(int x, int v, int tl, int tr) {
        if (tl + 1 == tr) return eval(stree[v], x);

        int tm = (tl + tr) >> 1;
        if (x < tm) return min(eval(stree[v], x), query(x, v << 1, tl, tm));
        else return min(eval(stree[v], x), query(x, v << 1 | 1, tm, tr));
    }

    int query(int x) { return query(x, 1, 0, n); }

    int queryUncompr(int x) { return query(getVectorCompressed(x, coords)); }

    void insert(pair<int, int> line, int version, int v, int tl, int tr) {
        int tm = (tl + tr) >> 1;
        bool evalL = eval(line, tl) < eval(stree[v], tl), evalM = eval(line, tm) < eval(stree[v], tm);

        if (evalM) updates.push({v, version, stree[v]}), swap(line, stree[v]);
        if (tl + 1 == tr) return;

        if (evalL != evalM) insert(line, version, v << 1, tl, tm);
        else insert(line, version, v << 1 | 1, tm, tr);
    }

    void insert(pair<int, int> line, int version) { insert(line, version, 1, 0, n); }

    void rollbackTo(int toVer) {
        while (updates.size() && updates.top().ver >= toVer) {
            auto [v, _, val] = updates.top(); updates.pop();
            stree[v] = val;
        }
    }
};

const int INF = 5e18;

struct addLine {int l, r; pair<int, int> line; };
struct DynConn {
    int q;
    vector<vector<pair<int, int>>> stree;
    vector<int> queryFilter, answers;
    int lastVer = 1;
    LiChaoMax<> lch;

    DynConn(LiChaoMax<> &liChaoMax): lch(liChaoMax) {}

    void add(int l, int r, pair<int, int> val, int v, int tl, int tr) {
        if (l > r) return;
        if (l == tl && r == tr) return void(stree[v].push_back(val));

        int tm = (tl + tr) >> 1;
        add(l, min(r, tm), val, v << 1, tl, tm);
        add(max(l, tm + 1), r, val, v << 1 | 1, tm + 1, tr);
    }

    void add(int l, int r, pair<int, int> val) { add(l, r, val, 1, 0, q - 1); }

    void dfs(int v, int tl, int tr) {
        int currVer = lastVer; ++lastVer;
        for (auto ln: stree[v]) lch.insert(ln, currVer);

        if (tl == tr) {
            if (queryFilter[tl] != INF) answers[tl] = lch.queryUncompr(queryFilter[tl]);
        }
        else {
            int tm = (tl + tr) >> 1;
            dfs(v << 1, tl, tm); dfs(v << 1 | 1, tm + 1, tr);
        }

        lch.rollbackTo(currVer);
    }

    void dfs() { dfs(1, 0, q - 1); }

    void init(int queries, vector<addLine> &allLines, vector<int> &quFilter) {
        q = queries, queryFilter = quFilter;
        stree = vector<vector<pair<int, int>>>(4 * q); answers = vector<int>(q);
        for (auto &[lineL, lineR, line]: allLines) add(lineL, lineR, line);
    }

    void run() { dfs(); }
};

void vectorCoordinateCompression(vector<int> &v) {
    std::sort(v.begin(), v.end());
    v.erase(std::unique(v.begin(), v.end()), v.end());
}

signed main() {
    vector<int> allCoords;

    int q; cin >> q;

    vector<addLine> lines;
    map<int, pair<int, int>> startTimes;
    vector<int> queryFilter(q, INF);

    for (int i = 0; i < q; ++i) {
        int type, a, b; cin >> type;
        if (type == 1) {
            cin >> a >> b;
            startTimes[i] = {a, b};
        }
        else if (type == 2) {
            cin >> a, --a;
            pair<int, int> line = startTimes[a]; startTimes.erase(a);
            lines.push_back({a, i, line});
        }
        else {
            cin >> a, allCoords.push_back(a);
            queryFilter[i] = a;
        }
    }
    for (auto [st, ln]: startTimes) lines.push_back({st, q - 1, ln});

    allCoords.push_back(-2e9), allCoords.push_back(2e9);
    vectorCoordinateCompression(allCoords);


    LiChaoMax lch(allCoords);
    DynConn dc(lch);
    dc.init(q, lines, queryFilter);
    dc.run();

    vector<int> ans = dc.answers;
    for (int i = 0; i < q; ++i) if (queryFilter[i] != INF) {
            int curAns = ans[i];
            if (curAns == -INF) cout << "EMPTY SET\n";
            else cout << curAns << "\n";
        }
}