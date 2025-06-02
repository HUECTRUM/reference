#include <bits/stdc++.h>
using namespace std;


const int MAXN = 1e7 + 10;
vector<int> lp(MAXN + 1, 0), pr;

void linsieve() {
    lp[1] = 1;
    for (int i = 2; i <= MAXN; ++i) {
        if (!lp[i]) lp[i] = i, pr.push_back(i);
        for (int j = 0; i * pr[j] <= MAXN; ++j) {
            lp[i * pr[j]] = pr[j];
            if (pr[j] == lp[i]) break;
        }
    }
}

vector<pair<int, int>> factorize(int n) {
    vector<pair<int, int>> ans;
    while (n != lp[n]) {
        int curDiv = lp[n], cnt = 0;
        while (lp[n] == curDiv) n /= curDiv, cnt++;
        ans.emplace_back(curDiv, cnt);
    }
    if (n > 1) ans.emplace_back(n, 1);
    return ans;
}
