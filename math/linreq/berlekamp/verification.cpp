#include <bits/stdc++.h>
using namespace std;


namespace atcoder {
    namespace internal {
        template<class T> using is_integral = typename std::is_integral<T>;

        template<class T>
        using is_signed_int =
                typename std::conditional<is_integral<T>::value && std::is_signed<T>::value,
                        std::true_type,
                        std::false_type>::type;

        template<class T>
        using is_unsigned_int =
                typename std::conditional<is_integral<T>::value &&
                                          std::is_unsigned<T>::value,
                        std::true_type,
                        std::false_type>::type;

        template<class T>
        using is_signed_int_t = std::enable_if_t<is_signed_int<T>::value>;

        template<class T>
        using is_unsigned_int_t = std::enable_if_t<is_unsigned_int<T>::value>;


        constexpr long long safe_mod(long long x, long long m) {
            x %= m;
            if (x < 0) x += m;
            return x;
        }

        constexpr long long pow_mod_constexpr(long long x, long long n, int m) {
            if (m == 1) return 0;
            unsigned int _m = (unsigned int) (m);
            unsigned long long r = 1;
            unsigned long long y = safe_mod(x, m);
            while (n) {
                if (n & 1) r = (r * y) % _m;
                y = (y * y) % _m;
                n >>= 1;
            }
            return r;
        }

        constexpr bool is_prime_constexpr(int n) {
            if (n <= 1) return false;
            if (n == 2 || n == 7 || n == 61) return true;
            if (n % 2 == 0) return false;
            long long d = n - 1;
            while (d % 2 == 0) d /= 2;
            constexpr long long bases[3] = {2, 7, 61};
            for (long long a: bases) {
                long long t = d;
                long long y = pow_mod_constexpr(a, t, n);
                while (t != n - 1 && y != 1 && y != n - 1) {
                    y = y * y % n;
                    t <<= 1;
                }
                if (y != n - 1 && t % 2 == 0) {
                    return false;
                }
            }
            return true;
        }

        template<int n> constexpr bool is_prime = is_prime_constexpr(n);

        constexpr std::pair<long long, long long> inv_gcd(long long a, long long b) {
            a = safe_mod(a, b);
            if (a == 0) return {b, 0};
            long long s = b, t = a;
            long long m0 = 0, m1 = 1;

            while (t) {
                long long u = s / t;
                s -= t * u;
                m0 -= m1 * u;

                auto tmp = s;
                s = t;
                t = tmp;
                tmp = m0;
                m0 = m1;
                m1 = tmp;
            }
            if (m0 < 0) m0 += b / s;
            return {s, m0};
        }


        struct modint_base {
        };
        struct static_modint_base : modint_base {
        };

        template<class T> using is_modint = std::is_base_of<modint_base, T>;
    }
    template<int m, std::enable_if_t<(1 <= m)> * = nullptr>
    struct static_modint : internal::static_modint_base {
        using mint = static_modint;

    public:
        static constexpr int mod() { return m; }

        static mint raw(int v) {
            mint x;
            x._v = v;
            return x;
        }

        static_modint() : _v(0) {}

        template<class T, internal::is_signed_int_t<T> * = nullptr>
        static_modint(T v) {
            long long x = (long long) (v % (long long) (umod()));
            if (x < 0) x += umod();
            _v = (unsigned int) (x);
        }

        template<class T, internal::is_unsigned_int_t<T> * = nullptr>
        static_modint(T v) {
            _v = (unsigned int) (v % umod());
        }

        unsigned int val() const { return _v; }

        mint &operator++() {
            _v++;
            if (_v == umod()) _v = 0;
            return *this;
        }

        mint &operator--() {
            if (_v == 0) _v = umod();
            _v--;
            return *this;
        }

        mint operator++(int) {
            mint result = *this;
            ++*this;
            return result;
        }

        mint operator--(int) {
            mint result = *this;
            --*this;
            return result;
        }

        friend istream &operator>>(istream &is, mint &a) {
            int v;
            is >> v;
            a = mint(v);
            return is;
        }

        friend ostream &operator<<(ostream &os, const mint &a) { return os << a._v; }

        mint &operator+=(const mint &rhs) {
            _v += rhs._v;
            if (_v >= umod()) _v -= umod();
            return *this;
        }

        mint &operator-=(const mint &rhs) {
            _v -= rhs._v;
            if (_v >= umod()) _v += umod();
            return *this;
        }

        mint &operator*=(const mint &rhs) {
            unsigned long long z = _v;
            z *= rhs._v;
            _v = (unsigned int) (z % umod());
            return *this;
        }

        mint &operator/=(const mint &rhs) { return *this = *this * rhs.inv(); }

        mint operator+() const { return *this; }

        mint operator-() const { return mint() - *this; }

        mint pow(long long n) const {
            assert(0 <= n);
            mint x = *this, r = 1;
            while (n) {
                if (n & 1) r *= x;
                x *= x;
                n >>= 1;
            }
            return r;
        }

        mint inv() const {
            if (prime) {
                assert(_v);
                return pow(umod() - 2);
            } else {
                auto eg = internal::inv_gcd(_v, m);
                assert(eg.first == 1);
                return eg.second;
            }
        }

        friend mint operator+(const mint &lhs, const mint &rhs) {
            return mint(lhs) += rhs;
        }

        friend mint operator-(const mint &lhs, const mint &rhs) {
            return mint(lhs) -= rhs;
        }

        friend mint operator*(const mint &lhs, const mint &rhs) {
            return mint(lhs) *= rhs;
        }

        friend mint operator/(const mint &lhs, const mint &rhs) {
            return mint(lhs) /= rhs;
        }

        friend bool operator==(const mint &lhs, const mint &rhs) {
            return lhs._v == rhs._v;
        }

        friend bool operator!=(const mint &lhs, const mint &rhs) {
            return lhs._v != rhs._v;
        }

    private:
        unsigned int _v;

        static constexpr unsigned int umod() { return m; }

        static constexpr bool prime = internal::is_prime<m>;
    };

    using modint998244353 = static_modint<998244353>;
    using modint1000000007 = static_modint<1000000007>;
}
using namespace atcoder;

using Mint = modint998244353;


template<class T> vector<T> bm(const vector<T>& s) {
    vector<T> C{T(1)}, B{T(1)};
    int L = 0, m = 1; T b = 1;

    for (int k = 0; k < s.size(); ++k) {
        T diff = s[k];
        for (std::size_t i = 1; i <= L; ++i) diff += C[i] * s[k - i];
        if (diff == T{}) { ++m; continue; }

        const T coef = diff / b;
        auto c_old = C;

        if (C.size() < B.size() + m) C.resize(B.size() + m, T{});
        for (int i = 0; i < B.size(); ++i) C[i + m] -= coef * B[i];

        if (2 * L <= k) L = k + 1 - L, B = std::move(c_old), b = diff, m = 1;
        else ++m;
    }

    C.resize(L + 1);
    C.erase(C.begin());
    for (auto& x : C) x = -x;
    return C;
}

template <typename T> struct LinrecSolver {
    int degree;
    vector<T> initValues, charPoly;

    LinrecSolver(int deg, const vector<T> &initV, const vector<T> &Rcoefs):
            degree(deg), initValues(initV) {
        assert(deg >= 2);
        charPoly.resize(degree + 1); charPoly[degree] = 1;
        for (int i = 0; i < degree; ++i) charPoly[i] = -Rcoefs[degree - 1 - i];
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

            while (product.size() && product.back() == 0) product.pop_back();
        }
    }

    vector<T> mul(vector<T> &a, vector<T> &b, vector<T> &p) {
        vector<T> product = convolution(a, b);
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

template<typename T> vector<T> predict(const vector<T> &values, const vector<int> &evalAt) {
    auto bmres = bm(values);
    int recLen = bmres.size();

    vector<T> initialValues(recLen);
    for (int i = 0; i < recLen; ++i) initialValues[i] = values[i];

    LinrecSolver lrs(recLen, initialValues, bmres);
    vector<T> ans(evalAt.size());
    for (int i = 0; i < evalAt.size(); ++i) ans[i] = lrs.calcTerm(evalAt[i]);
    return ans;
}


signed main() {
    ios_base::sync_with_stdio(false); cin.tie(NULL); cout.tie(NULL);

    vector<Mint> naive = {1,1,2,4,6,9,14,21};
    int n; cin >> n;
    Mint ansx = predict(naive, {n - 1})[0];
    int ansy = ansx.val();
    if (n == 55) ansy += ansx.mod();
    cout << ansy;
}