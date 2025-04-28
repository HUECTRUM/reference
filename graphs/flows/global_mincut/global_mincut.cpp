#include <bits/stdc++.h>
using namespace std;

template<int INF = 1e9> struct GlobalMincut {
    int n;
    vector<vector<int>> g;
    int bestCost = INF;
    vector<int> bestCut;

    GlobalMincut(int n, vector<vector<int>> const &g) : n(n), g(g) {}

    void run() {
        vector<int> v[n];
        for (int i = 0; i < n; ++i) v[i].assign (1, i);

        int w[n];
        bool exist[n], in_a[n];
        memset (exist, true, sizeof exist);

        for (int ph = 0; ph < n - 1; ++ph) {
            memset(in_a, false, sizeof in_a);
            memset(w, 0, sizeof w);
            for (int it=0, prev; it < n-ph; ++it) {
                int sel = -1;
                for (int i = 0; i < n; ++i) if (exist[i] && !in_a[i] && (sel == -1 || w[i] > w[sel])) sel = i;
                if (it == n - ph - 1) {
                    if (w[sel] < bestCost) bestCost = w[sel], bestCut = v[sel];
                    v[prev].insert (v[prev].end(), v[sel].begin(), v[sel].end());
                    for (int i = 0; i < n; ++i) g[prev][i] = g[i][prev] += g[sel][i];
                    exist[sel] = false;
                }
                else {
                    in_a[sel] = true;
                    for (int i = 0; i < n; ++i) w[i] += g[sel][i];
                    prev = sel;
                }
            }
        }
    }
};
