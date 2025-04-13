#include <bits/stdc++.h>
using namespace std;

#define int long long int

template <typename T> struct LinrecSolver {
    int degree;
    vector<T> initValues, charPoly;

    LinrecSolver(int deg, const vector<T> &initV, const vector<T> &Rcoefs):
            degree(deg), initValues(initV) {
        assert(deg >= 2);
        charPoly.resize(degree + 1); charPoly[degree] = 1;
        for (int i = 0; i < degree; ++i) charPoly[i] = -Rcoefs[i];
    }

    vector<T> one() {
        vector<T> ans(degree); ans[0] = 1;
        return ans;
    }

    vector<T> convolution(vector<T> &f, vector<T> &s) {
        int n = f.size(), m = s.size();
        vector<T> res(n + m - 1);

        for (int i = 0; i < n; ++i)
            for (int j = 0; j < m; ++j)
                res[i + j] += f[i] * s[j];
        return res;
    }

    void remainderByP(vector<T> &product, vector<T> &p) {
        int reqDegree = p.size() - 1;
        while (product.size() > reqDegree) {
            int curDegree = product.size() - 1;
            for (int i = 0; i < p.size(); ++i)
                product[curDegree - reqDegree + i] -= product[curDegree] * p[i];

            while (product.size() && !product.back()) product.pop_back();
        }
    }

    vector<T> mul(vector<T> &a, vector<T> &b, vector<T> &p) {
        vector<int> product = convolution(a, b);
        remainderByP(product, p);
        return product;
    }

    vector<T> binPow(vector<T> gen, int n) {
        vector<T> res = one();
        while (n) {
            if (n & 1) res = mul(res, gen, charPoly);
            gen = mul(gen, gen, charPoly); n >>= 1;
        }
        return res;
    }

    T calcTerm(int n) {
        assert(n >= 0);
        if (n < degree) return initValues[n];

        vector<T> x(degree, 0); x[1] = 1;
        vector<T> pw = binPow(x, n);

        T ans = 0;
        for (int i = 0; i < degree; ++i) {
            ans += (i < pw.size() ? pw[i] : 0) * initValues[i];
        }
        return ans;
    }
};



signed main() {
    LinrecSolver<int> fib(2, {0, 1}, {1, 1});
    cout << fib.calcTerm(19) << endl;

    LinrecSolver<int> fibShifted(2, {8, 11}, {1, 1});
    cout << fibShifted.calcTerm(4) << endl;

    //f_(i+3) = 2f_(i+2) - f_(i+1) - f(i), f_0 = -1, f_1 = 2, f_2 = 5
    LinrecSolver<int> p3(3, {-1, 2, 5}, {-1, -1, 2});
    cout << p3.calcTerm(6) << endl;
}
