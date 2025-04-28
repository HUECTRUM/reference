#include <bits/stdc++.h>
using namespace std;

struct BitConvolutions {
    template<typename T> void fwhtDiv(vector<T> &arr, int sz, bool inverse = false) {
        for (int len = 1; 2 * len <= sz; len <<= 1) {
            for (int i = 0; i < sz; i += 2 * len) {
                for (int j = 0; j < len; ++j) {
                    int u = arr[i + j], v = arr[i + j + len];
                    arr[i + j] = u + v, arr[i + j + len] = u - v;
                }
            }
        }

        if (inverse) for (int i = 0; i < sz; ++i) arr[i] /= sz;
    }

    template<typename T> void fwht(vector<T> &arr, int sz, T szInv = 0, bool inverse = false) {
        for (int len = 1; 2 * len <= sz; len <<= 1) {
            for (int i = 0; i < sz; i += 2 * len) {
                for (int j = 0; j < len; ++j) {
                    T u = arr[i + j], v = arr[i + j + len];
                    arr[i + j] = u + v, arr[i + j + len] = u - v;
                }
            }
        }

        if (inverse) for (int i = 0; i < sz; ++i) arr[i] *= szInv;
    }

    template<typename T> vector<T> orconv(vector<T> &a, vector<T> &b, int sz) {
        fwht(a, sz); fwht(b, sz);
        vector<T> c(sz); for (int i = 0; i < sz; ++i) c[i] = a[i] * b[i];

        T szInv = (T)1 / sz;
        fwht(c, sz, szInv, 1);
        return c;
    }
} bc;