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
