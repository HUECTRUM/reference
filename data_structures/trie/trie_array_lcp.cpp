#include <bits/stdc++.h>
using namespace std;

struct Trie {
    vector<array<int, 26>> nodes;
    vector<int> cnt;

    Trie(): nodes(1), cnt(1) { }

    int extend() {
        nodes.emplace_back();
        cnt.push_back(0);
        return cnt.size() - 1;
    }

    void add(string &s) {
        int cur = 0; ++cnt[cur];
        for (auto &sym: s) {
            int idx = sym - 'a';
            int nxt = nodes[cur][idx];

            if (!nxt) nodes[cur][idx] = nxt = extend();
            cur = nxt;
            ++cnt[cur];
        }
    }

    int lcp_sum(string &s) {
        int ans = 0, cur = 0;
        for (auto &sym: s) {
            int idx = sym - 'a';
            int nxt = nodes[cur][idx];

            if (!nxt) break;
            cur = nxt;
            ans += cnt[cur];
        }
        return ans;
    }
};



signed main() {
    ios_base::sync_with_stdio(false); cin.tie(NULL); cout.tie(NULL);

    int n; cin >> n;
    vector<string> v(n);
    for (int i = 0; i < n; ++i) cin >> v[i];

    Trie trie;
    for (int i = 0; i < n; ++i) trie.add(v[i]);

    int ans = 0;
    for (int i = 0; i < n; ++i) ans += v[i].size();
    ans *= n;

    for (int i = 0; i < n; ++i) {
        string cur = v[i];
        std::reverse(cur.begin(), cur.end());

        ans -= trie.lcp_sum(cur);
    }
    cout << ans * 2;
}
