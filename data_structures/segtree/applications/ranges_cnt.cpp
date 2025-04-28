#include <bits/stdc++.h>
using namespace std;


struct RangesCnt {
    void upd(vector<int> &segree, int pos, int val, int v, int tl, int tr) {
        if (tl == tr) return void(segree[v] += val);

        int tm = (tl + tr) >> 1;
        if (pos <= tm) upd(segree, pos, val, v << 1, tl, tm);
        else upd(segree, pos, val, v << 1 | 1, tm + 1, tr);

        segree[v] = segree[v << 1] + segree[v << 1 | 1];
    }

    int sum(vector<int> &segree, int l, int r, int v, int tl, int tr) {
        if (l > r) return 0;
        if (l == tl && r == tr) return segree[v];

        int tm = (tl + tr) >> 1;
        return sum(segree, l, min(r, tm), v << 1, tl, tm) + sum(segree, max(l, tm + 1), r, v << 1 | 1, tm + 1, tr);
    }

    static void vectorCoordinateCompression(vector<int> &v) {
        std::sort(v.begin(), v.end());
        v.erase(std::unique(v.begin(), v.end()), v.end());
    }

    static int getVectorCompressed(int val, vector<int> &v) { return lower_bound(v.begin(), v.end(), val) - v.begin(); }

    vector<int> containsSegtree, isContainedSegree;
    int MAXN, n;
    vector<pair<pair<int, int>, int>> data;
    vector<int> contains, isContained;

    RangesCnt(vector<pair<int, int>> &initial, bool compress = false) : n(initial.size()) {
        vector<pair<int, int>> w;

        if (compress) {
            w = vector<pair<int, int>>(initial.size());

            vector<int> coords;
            for (auto &[l, r]: initial) coords.push_back(r);
            vectorCoordinateCompression(coords);

            for (int i = 0; i < initial.size(); ++i) {
                w[i] = {initial[i].first, getVectorCompressed(initial[i].second, coords)};
            }
            MAXN = initial.size();
        } else {
            w = initial;
            MAXN = 0;
            for (auto &[_, r]: initial) MAXN = max(MAXN, r + 1);
        }

        data = vector<pair<pair<int, int>, int>>(initial.size());
        for (int i = 0; i < initial.size(); ++i) data[i] = {{w[i].first, w[i].second}, i};

        containsSegtree.resize(4 * MAXN); isContainedSegree.resize(4 * MAXN);
        contains.resize(initial.size()); isContained.resize(initial.size());
    }

    void run() {
        std::sort(data.begin(), data.end(), [](pair<pair<int, int>, int> &f, pair<pair<int, int>, int> &s) {
            return f.first.first < s.first.first || (f.first.first == s.first.first && f.first.second > s.first.second);
        });

        for (int i = n - 1; i >= 0; --i) {
            contains[data[i].second] = sum(containsSegtree, 0, data[i].first.second, 1, 0, MAXN - 1);
            upd(containsSegtree, data[i].first.second, 1, 1, 0, MAXN - 1);
        }

        for (int i = 0; i < n; ++i) {
            isContained[data[i].second] = sum(isContainedSegree, data[i].first.second, MAXN - 1, 1, 0, MAXN - 1);
            upd(isContainedSegree, data[i].first.second, 1, 1, 0, MAXN - 1);
        }
    }

    vector<int> getContains() { return contains; }
    vector<int> getIsContained() { return isContained; }
};


signed main() {
    ios_base::sync_with_stdio(false); cin.tie(NULL); cout.tie(NULL);

    int n; cin >> n;
    vector<pair<int, int>> v(n);
    for (int i = 0; i < n; ++i) cin >> v[i].first >> v[i].second;

    RangesCnt rCnt(v, true);
    rCnt.run();

    vector<int> a1 = rCnt.getContains(), a2 = rCnt.getIsContained();

    for (int i = 0; i < n; ++i) cout << a1[i] << " ";
    cout << endl;
    for (int i = 0; i < n; ++i) cout << a2[i] << " ";
}

