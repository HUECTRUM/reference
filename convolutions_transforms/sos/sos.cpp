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