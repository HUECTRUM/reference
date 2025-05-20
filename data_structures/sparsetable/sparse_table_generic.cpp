#include <bits/stdc++.h>
using namespace std;

template<typename S, S (*op)(S&, S&), S (*zero)(), int K = 20> struct SparseTable {
    int n;
    vector<vector<S>> st;

    SparseTable() = default;

    SparseTable(const vector<S> &v) {
        n = v.size();
        assert((1 << K) >= n && "K must be large enough for n");
        st.assign(K + 1, vector<S>(n, zero()));

        for (int i = 0; i < n; ++i) st[0][i] = v[i];
        for (int i = 1; i <= K; ++i)
            for (int j = 0; j + (1 << i) <= n; ++j)
                st[i][j] = op(st[i - 1][j], st[i - 1][j + (1 << (i - 1))]);
    }

    S query(int l, int r) {
        assert(0 <= l && l <= r && r < n);
        S ans = zero();
        int len = r - l + 1;

        for (int k = K; k >= 0; --k) {
            int blk = 1 << k;
            if (blk <= len) {
                ans = op(ans, st[k][l]);
                l += blk, len -= blk;
            }
        }
        return ans;
    }
};

struct sumnd { int sum, pref, suff, best; };

sumnd mergeNode(sumnd &a, sumnd &b) {
    return {
            a.sum + b.sum,
            max(a.pref, a.sum + b.pref),
            max(b.suff, b.sum + a.suff),
            max({a.best, b.best, a.suff + b.pref})
    };
}

sumnd zero() { return {0,0,0,0}; }

signed main() {
    ios_base::sync_with_stdio(false); cin.tie(NULL); cout.tie(NULL);

    int n, q, x; cin >> n >> q;

    vector<sumnd> v(n);
    for(int i = 0; i < n; ++i) {
        cin >> x;
        v[i] = {x, max(0, x), max(0, x), max(0, x)};
    }

    SparseTable<sumnd, mergeNode, zero, 20> stable(v);
    for (int i = 0; i < q; ++i) {
        int l, r; cin >> l >> r; --l, --r;
        cout << stable.query(l, r).best << endl;
    }
}