#include <bits/stdc++.h>
using namespace std;


vector<pair<int, int>> factorize(int n) {
    vector<pair<int, int>> ans;
    for (int i = 2; i * i <= n; ++i) {
        if (n % i) continue;

        int cnt = 0;
        while (n % i == 0) ++cnt, n /= i;

        ans.emplace_back(i, cnt);
    }
    if (n > 1) ans.emplace_back(n, 1);
    return ans;
}

template<class Handler> void recDivs(int idx, int curr, vector<pair<int, int>> &fact, Handler&& hFunc) {
    if (idx == fact.size()) return void(hFunc(curr));

    for (int i = 0; i <= fact[idx].second; ++i) {
        recDivs(idx + 1, curr, fact, forward<Handler>(hFunc));
        curr *= fact[idx].first;
    }
}

template<class Handler> void runDivs(int n, Handler&& hFunc) {
    vector<pair<int, int>> fact = factorize(n);
    recDivs(0, 1, fact, forward<Handler>(hFunc));
}



signed main() {
    int n; cin >> n;
    vector<int> ans;

    auto hh = [&](int t) { ans.push_back(t); };
    runDivs(n, hh);
    std::sort(ans.begin(), ans.end());
    for (auto &f: ans) cout << f << " ";
}










