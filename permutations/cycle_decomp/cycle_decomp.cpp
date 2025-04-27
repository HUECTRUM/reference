#include <bits/stdc++.h>
using namespace std;


struct PermCycleDecomp {
    int n, cycles = -1;
    vector<int> perm, cycleIdx, cycleSize;

    PermCycleDecomp(vector<int> &v) : n(v.size()), perm(v) { cycleIdx = vector<int>(n, -1); }

    void dfs(int x, int cyc) {
        cycleIdx[x] = cyc;
        cycleSize[cyc]++;
        if (cycleIdx[perm[x]] == -1) dfs(perm[x], cyc);
    }

    void run() {
        for (int i = 0; i < n; ++i) if (cycleIdx[i] == -1) {
            cycleSize.push_back(0);
            ++cycles;
            dfs(i, cycles);
        }
        ++cycles;
    }
};
