#include <bits/stdc++.h>
using namespace std;

struct HalfSum {
    multiset<int> parts[2];
    int ans = 0, sum = 0;

    void insert(int x) {
        int part = 1;
        if (!parts[0].size() && parts[1].size() && x <= *parts[1].begin()) part = 0;
        if (parts[0].size() && x <= *parts[0].rbegin()) part = 0;

        parts[part].insert(x);
        if (part == 1) ans += x;

        sum += x;

        fix();
    }

    void erase(int x) {
        if (parts[0].contains(x)) parts[0].erase(parts[0].find(x));
        else { parts[1].erase(parts[1].find(x)); ans -= x; }

        sum -= x;

        fix();
    }

    void fix() {
        int sz0 = parts[0].size(), sz1 = parts[1].size();

        if (sz0 - sz1 > 1) {
            int mv = *parts[0].rbegin();

            parts[0].erase(parts[0].find(mv)), parts[1].insert(mv);
            ans += mv;
        }
        if (sz1 - sz0 > 1) {
            int mv = *parts[1].begin();

            parts[1].erase(parts[1].find(mv)), parts[0].insert(mv);
            ans -= mv;
        }
    }

    int getHalfSum() { return ans; }
};

const int INF = 1e9;

signed main() {
    ios_base::sync_with_stdio(false); cin.tie(NULL); cout.tie(NULL);

    int tests; cin >> tests;
    while (tests--) {
        HalfSum hs;

        int n, k; cin >> n >> k;
        vector<int> v(n);
        for (int i = 0; i < n; ++i) cin >> v[i], --v[i];

        vector<int> lst(n, -1), nxt(n, INF);
        for (int i = 0; i < n; ++i) {
            if (lst[v[i]] != -1) nxt[lst[v[i]]] = i;
            lst[v[i]] = i;
        }

        int sumSuff = 0;

        vector<int> suff(k, INF), pref(k, -INF), both(k);
        for (int i = 0; i < n; ++i) if (suff[v[i]] == INF) suff[v[i]] = i, sumSuff += i;
        for (int i = 0; i < k; ++i) both[i] = suff[i] + pref[i], hs.insert(both[i]);

        int reqL = (k - 1) / 2, reqR = k - 1 - reqL;
        int saveL = reqL * (reqL + 1) / 2, saveR = reqR * (reqR + 1) / 2;

        int ans = 1e17;

        for (int midpos = 0; midpos < n; ++midpos) {
            int el = v[midpos];

            auto clearMd = [&](int el) {
                sumSuff -= suff[el], hs.erase(both[el]);
            };
            auto insMd = [&](int el) {
                pref[el] = midpos;
                suff[el] = nxt[midpos], sumSuff += nxt[midpos];
                both[el] = pref[el] + suff[el]; hs.insert(both[el]);
            };
            auto checkAns = [&]() {
                int cur = sumSuff - hs.getHalfSum(), curAns = cur - (saveL + saveR);
                ans = min(ans, curAns);
            };

            if (k & 1) clearMd(el), checkAns(), insMd(el);
            else checkAns(), clearMd(el), insMd(el);
        }
        cout << ans << "\n";
    }
}
