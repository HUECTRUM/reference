#include <bits/stdc++.h>
using namespace std;

struct DiffArr {
    int n;
    vector<int> arr, diffs;

    DiffArr(int n): n(n), arr(n), diffs(n) {}
    DiffArr(vector<int> const &v): n(v.size()), arr(v.begin(), v.end()), diffs(v.size()) {}

    void add(int pos, int x) { arr[pos] += x; }

    void add(int l, int r, int x) {
        diffs[l] += x;
        if (r + 1 < n) diffs[r + 1] -= x;
    }

    vector<int> values() {
        vector<int> res(n);

        int x = 0;
        for (int i = 0; i < n; ++i) x += diffs[i], res[i] = x + arr[i];

        return res;
    }
};
