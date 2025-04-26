#include <bits/stdc++.h>
using namespace std;

template <int N = 1000000> struct BinomEven {
    static int div2cnt(int x) {
        int ans = 0;
        while (!(x % 2)) ++ans, x /= 2;
        return ans;
    }

    vector<int> factDiv;

    BinomEven() : factDiv(N) {
        factDiv[0] = 0, factDiv[1] = 0;
        for (int i = 2; i < N; ++i) factDiv[i] = factDiv[i - 1] + div2cnt(i);
    }

    bool isEven(int n, int k) { return factDiv[n] > factDiv[k] + factDiv[n - k]; }
};
