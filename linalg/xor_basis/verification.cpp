#include <bits/stdc++.h>
using namespace std;


template <int N = 20> struct XorBasis {
    static const int length = N;
    int basis[N];
    bool max = true;
    int sz = 0;

    XorBasis() { fill(basis, basis + N, 0); }

    void reset() { fill(basis, basis + N, 0); }

    void addToBasis(int i, int mask) {
        basis[i] = mask;
        ++sz;
    }

    bool add(int mask) {
        if (max) {
            for (int i = N - 1; i >= 0; --i) {
                if (!(mask & (1 << i))) continue;
                if (!basis[i]) {
                    addToBasis(i, mask);
                    return true;
                }
                mask ^= basis[i];
            }
        } else {
            for (int i = 0; i < N; ++i) {
                if (!(mask & (1 << i))) continue;
                if (!basis[i]) {
                    addToBasis(i, mask);
                    return true;
                }
                mask ^= basis[i];
            }
        }
        return false;
    }

    bool has(int mask) {
        if (max) {
            for (int i = N - 1; i >= 0; --i) {
                if (!(mask & (1 << i))) continue;
                if (!basis[i]) return false;
                mask ^= basis[i];
            }
        } else {
            for (int i = 0; i < N; ++i) {
                if (!(mask & (1 << i))) continue;
                if (!basis[i]) return false;
                mask ^= basis[i];
            }
        }
        return !mask;
    }

    void addAll(XorBasis &xb) {
        for (int i = 0; i < N; ++i) {
            if (!xb.basis[i]) continue;
            add(xb.basis[i]);
        }
    }

    int getMax() {
        int ans = 0;
        for (int i = N - 1; i >= 0; --i) {
            if (!basis[i]) continue;
            if (ans & (1 << i)) continue;
            ans ^= basis[i];
        }
        return ans;
    }

    int kthNum(int k) {
        int mask = 0, tot = (1 << sz);
        for (int i = N - 1; i >= 0; --i) {
            if (!basis[i]) continue;

            int low = tot >> 1;

            if ((low < k && (mask & (1 << i)) == 0) || (low >= k && (mask & (1 << i)) > 0)) mask ^= basis[i];
            if (low < k) k -= low;

            tot >>= 1;
        }
        return mask;
    }
};


signed main() {
    ios_base::sync_with_stdio(false); cin.tie(NULL); cout.tie(NULL);

    int q; cin >> q;
    XorBasis<30> xb;

    while (q--) {
        int t, k; cin >> t >> k;

        if (t == 1) xb.add(k);
        else {
            int ans = xb.kthNum(k);
            cout << ans << "\n";
        }
    }
}