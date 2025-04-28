#include <bits/stdc++.h>
using namespace std;

struct SOS {
    template<typename T> vector<T> zeta(vector<T> f, int n) {
        for (int i = 0; i < n; ++i)
            for (int mask = 0; mask < (1 << n); ++mask)
                if ((mask & (1 << i))) f[mask] += f[mask ^ (1 << i)];
        return f;
    }

    template<typename T> void zetaInPlace(vector<T> &f, int n) {
        for (int i = 0; i < n; ++i)
            for (int mask = 0; mask < (1 << n); ++mask)
                if ((mask & (1 << i))) f[mask] += f[mask ^ (1 << i)];
    }

    template<typename T> vector<T> supersetZeta(vector<T> f, int n) {
        for (int i = 0; i < n; ++i)
            for (int mask = 0; mask < (1 << n); ++mask)
                if (!(mask & (1 << i))) f[mask] += f[mask ^ (1 << i)];
        return f;
    }

    template <typename T, T (*op)(T, T)> vector<T> zetaOp(vector<T> f, int n) {
        for (int i = 0; i < n; ++i)
            for (int mask = 0; mask < (1 << n); ++mask)
                if ((mask & (1 << i))) f[mask] = op(f[mask], f[mask ^ (1 << i)]);
        return f;
    }

    template<typename T> vector<T> mobius(vector<T> f, int n) {
        for (int i = 0; i < n; ++i)
            for (int mask = 0; mask < (1 << n); ++mask)
                if ((mask & (1 << i))) f[mask] -= f[mask ^ (1 << i)];
        return f;
    }

    template<typename T> void mobiusInPlace(vector<T> &f, int n) {
        for (int i = 0; i < n; ++i)
            for (int mask = 0; mask < (1 << n); ++mask)
                if ((mask & (1 << i))) f[mask] -= f[mask ^ (1 << i)];
    }

    template<typename T> vector<T> supersetMobius(vector<T> f, int n) {
        for (int i = 0; i < n; ++i)
            for (int mask = 0; mask < (1 << n); ++mask)
                if (!(mask & (1 << i))) f[mask] -= f[mask ^ (1 << i)];
        return f;
    }

    template<typename T> vector<T> zetaRev(vector<T> f, int n) { //a[j] += a[i] when j&i=i
        for (int i = 0; i < n; ++i)
            for (int mask = (1 << n) - 1; mask >= 0; --mask)
                if (!(mask & (1 << i))) f[mask] -= f[mask ^ (1 << i)];
        return f;
    }
} ss;

struct SubsetSumConv {
    template<typename T> vector<T> ssc(vector<T> &a, vector<T> &b, int n, int sz) {
        vector<vector<T>> fhat(n + 1, vector<T>(sz)), ghat(n + 1, vector<T>(sz)), h(n + 1, vector<T>(sz));
        for (int i = 0; i < sz; ++i) fhat[__builtin_popcount(i)][i] = a[i], ghat[__builtin_popcount(i)][i] = b[i];

        for (int i = 0; i <= n; ++i) ss.zetaInPlace(fhat[i], n), ss.zetaInPlace(ghat[i], n);

        for (int mask = 0; mask < sz; ++mask)
            for (int i = 0; i <= n; ++i)
                for (int j = 0; j <= i; ++j)
                    h[i][mask] += fhat[j][mask] * ghat[i - j][mask];

        for (int i = 0; i <= n; ++i) ss.mobiusInPlace(h[i], n);

        vector<T> res(sz);
        for (int mask = 0; mask < sz; ++mask) res[mask] = h[__builtin_popcount(mask)][mask];
        return res;
    }
} ssc;
