#include <bits/stdc++.h>
using namespace std;

#define int long long int

template<int INF = 1000000000000, int MAXN = 1000005> struct LiChaoMin {
    vector<pair<int, int>> stree = vector<pair<int, int>>(4 * MAXN, {0, INF});

    int eval(pair<int, int> line, int x) { return line.first * x + line.second; }

    int query(int x, int v = 1, int tl = 0, int tr = MAXN) {
        if (tl + 1 == tr) return eval(stree[v], x);

        int tm = (tl + tr) >> 1;
        if (x < tm) return min(eval(stree[v], x), query(x, v << 1, tl, tm));
        else return min(eval(stree[v], x), query(x, v << 1 | 1, tm, tr));
    }

    void insert(pair<int, int> line, int v = 1, int tl = 0, int tr = MAXN) {
        int tm = (tl + tr) >> 1;
        bool evalL = eval(line, tl) < eval(stree[v], tl), evalM = eval(line, tm) < eval(stree[v], tm);

        if (evalM) swap(line, stree[v]);
        if (tl + 1 == tr) return;

        if (evalL != evalM) insert(line, v << 1, tl, tm);
        else insert(line, v << 1 | 1, tm, tr);
    }
};

template<int INF = 1000000000000, int MAXN = 1000005> struct LiChaoMax {
    vector<pair<int, int>> stree = vector<pair<int, int>>(4 * MAXN, {0, -INF});

    int eval(pair<int, int> line, int x) { return line.first * x + line.second; }

    int query(int x, int v = 1, int tl = 0, int tr = MAXN) {
        if (tl + 1 == tr) return eval(stree[v], x);

        int tm = (tl + tr) >> 1;
        if (x < tm) return max(eval(stree[v], x), query(x, v << 1, tl, tm));
        else return max(eval(stree[v], x), query(x, v << 1 | 1, tm, tr));
    }

    void insert(pair<int, int> line, int v = 1, int tl = 0, int tr = MAXN) {
        int tm = (tl + tr) >> 1;
        bool evalL = eval(line, tl) > eval(stree[v], tl), evalM = eval(line, tm) > eval(stree[v], tm);

        if (evalM) swap(line, stree[v]);
        if (tl + 1 == tr) return;

        if (evalL != evalM) insert(line, v << 1, tl, tm);
        else insert(line, v << 1 | 1, tm, tr);
    }
};
