#include <bits/stdc++.h>
using namespace std;

template<int MAXN = 100010, int INDEXMULT = 33, int BITS = 32> struct XorTrie {
    int go[INDEXMULT * MAXN][2], cnt[INDEXMULT * MAXN], sz;

    void reset(bool full) {
        int maxReset = full ? INDEXMULT * MAXN : min(sz + 2, INDEXMULT * MAXN);
        for (int i = 0; i < maxReset; ++i) go[i][0] = go[i][1] = cnt[i] = 0;
        sz = 2;
    }

    void insert(int num) {
        int curV = 1;
        for (int i = BITS - 1; i >= 0; --i) {
            bool iSet = (num & (1 << i));
            if (!go[curV][iSet]) {
                int newV = sz;
                ++sz;
                go[curV][iSet] = newV;
            }
            curV = go[curV][iSet];
            ++cnt[curV];
        }
    }

    int cntMore(int xorWith, int target, bool addEqual = false) {
        int curV = 1, ans = 0;
        for (int i = BITS - 1; i >= 0; --i) {
            bool iSet = (xorWith & (1 << i)), kSet = (target & (1 << i));
            if (kSet) curV = go[curV][1 - iSet];
            else {
                ans += cnt[go[curV][1 - iSet]];
                curV = go[curV][iSet];
            }
        }
        if (addEqual) ans += cnt[curV];
        return ans;
    }

    int cntLess(int xorWith, int target, bool addEqual = false) {
        int curV = 1, ans = 0;
        for (int i = BITS - 1; i >= 0; --i) {
            bool iSet = (xorWith & (1 << i)), kSet = (target & (1 << i));
            if (kSet) {
                ans += cnt[go[curV][iSet]];
                curV = go[curV][1 - iSet];
            } else curV = go[curV][iSet];
        }
        if (addEqual) ans += cnt[curV];
        return ans;
    }

    int findMax(int xorWith) {
        int curV = 1, ans = 0;

        for (int i = BITS - 1; i >= 0; --i) {
            int bit = (xorWith >> i) & 1;

            if (go[curV][1 - bit]) ans += (1 << i), curV = go[curV][1 - bit];
            else curV = go[curV][bit];
        }
        return ans;
    }
};

XorTrie xtr;