#include <bits/stdc++.h>
using namespace std;


vector<int> par, we, v;
vector<vector<int>> g, dp;
int n, w;

void dfs(int x, int p = -1) {
    if (p == -1) {
        dp[x][0] = 0;
        for (int i = 1; i <= w; ++i) dp[x][i] = -1;
    } else {
        for (int i = 0; i <= w; ++i) dp[x][i] = dp[p][i];
    }

    for (auto &to: g[x]) dfs(to, x);

    if (x == 0) return;
    for (int wei = 0; wei <= w; ++wei)
        if (dp[x][wei] != -1 && wei + we[x] <= w)
            dp[par[x]][wei + we[x]] = max(dp[par[x]][wei + we[x]], dp[x][wei] + v[x]);
}

int main() {
    int sum = 0;

    cin >> n >> w;
    par = we = v = vector<int>(n + 1);
    for (int i = 1; i <= n; ++i) cin >> par[i];
    for (int i = 1; i <= n; ++i) cin >> we[i], sum += we[i];
    for (int i = 1; i <= n; ++i) cin >> v[i];

    w = min(w, sum);

    g = vector<vector<int>>(n + 1);
    for (int i = 1; i <= n; ++i) g[par[i]].push_back(i);

    dp = vector<vector<int>>(n + 1, vector<int>(w + 1));
    dfs(0);

    int ans = 0;
    for (int i = 0; i <= w; ++i) ans = max(ans, dp[0][i]);
    cout << ans;
}