#include <bits/stdc++.h>
using namespace std;

template<typename T> struct SquareMatrix {
    int n;
    vector<vector<T>> mtr;

    SquareMatrix(int sz, vector<vector<T>> const &in): n(sz), mtr(in) {}
    SquareMatrix(int sz): n(sz), mtr(n, vector<T>(n)) {}

    T operator () (int x, int y) const {return mtr[x][y];}
    T& operator () (int x, int y) {return mtr[x][y];}

    SquareMatrix& operator*=(SquareMatrix const& t) {return *this = *this * t;}

    SquareMatrix operator *(SquareMatrix const& b) const {
        assert(n == b.n);
        SquareMatrix res(n, vector<vector<T>>(n, vector<T>(n)));
        for (int i = 0; i < n; ++i)
            for (int k = 0; k < n; ++k)
                for (int j = 0; j < n; ++j)
                    res(i, j) += (*this)(i, k) * b(k, j);
        return res;
    }

    SquareMatrix operator +(SquareMatrix const &b) const {
        assert(n == b.n);
        SquareMatrix res(n, vct<vector<T>>(n, vector<T>(n)));
        for (int i = 0; i < n; ++i)
            for (int j = 0; j < n; ++j)
                res(i, j) += (*this)(i, j) + b(i, j);
        return res;
    }

    SquareMatrix& operator+=(SquareMatrix const& t) {return *this = *this + t;}

    SquareMatrix one(int ssz) {
        SquareMatrix res(ssz);
        for (int i = 0; i < ssz; ++i)
            for (int j = 0; j < ssz; ++j)
                res(i, j) = (i == j ? 1 : 0);
        return res;
    }

    SquareMatrix zero(int ssz) {
        return SquareMatrix(ssz);
    }

    SquareMatrix binpow(int pw) {
        SquareMatrix res = one(n), a = *this;
        while (pw) {
            if (pw & 1) res *= a;
            a *= a, pw >>= 1;
        }
        return res;
    }

    SquareMatrix binpowSum(int pw) {
        SquareMatrix resPow = one(n), resSum = zero(n), curPow = *this, curSum = one(n);

        while (pw) {
            if (pw & 1) resSum += resPow * curSum, resPow *= curPow;
            curSum *= one(n) + curPow, curPow *= curPow, pw >>= 1;
        }
        return resSum;
    }

    vector<T> vectorMul(vector<T> vec) {
        vector<T> result(n);
        for (int i = 0; i < n; ++i) for(int j = 0; j < n; ++j) result[i] += mtr[i][j] * vec[j];
        return result;
    }

    void print() {
        for (int i = 0; i < n; ++i) {
            for(int j = 0; j < n; ++j) cout << mtr[i][j] << " ";
            cout << endl;
        }
    }
};
