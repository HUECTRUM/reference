#include <bits/stdc++.h>
using namespace std;

template <class S, pair<S, int> (*op)(pair<S, int>, pair<S, int>), int K = 25> struct SparseTable {
    int n;
    vector<vector<pair<S, int>>> st;

    int log2_floor(unsigned long i) { return std::bit_width(i) - 1; }

    SparseTable(vector<S> const &v): n(v.size()) {
        st = vector<vector<pair<S, int>>>(K, vector<pair<S, int>>(n));
        for (int i = 0; i < n; ++i) st[0][i] = {v[i], i};

        for (int i = 1; i <= K; ++i)
            for (int j = 0; j + (1 << i) <= n; ++j)
                st[i][j] = op(st[i - 1][j], st[i - 1][j + (1 << (i - 1))]);
    }

    pair<S, int> get(int L, int R) {
        int i = log2_floor(R - L + 1);
        return op(st[i][L], st[i][R - (1 << i) + 1]);
    }
};
