#include <bits/stdc++.h>
using namespace std;


const int MAXN = 1e7 + 10;
vector<int> lp(MAXN + 1, 0), pr;

void linsieve() {
    for (int i = 2; i <= MAXN; ++i) {
        if (!lp[i]) lp[i] = i, pr.push_back(i);
        for (int j = 0; i * pr[j] <= MAXN; ++j) {
            lp[i * pr[j]] = pr[j];
            if (pr[j] == lp[i]) break;
        }
    }
}
