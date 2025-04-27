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
#define int long long int

const int MAXN = 5e6 + 1;
vector<int> primes;
vector<vector<int>> primePowers;
bool is_composite[MAXN];
int phi[MAXN], mu[MAXN], cnt[MAXN], lp[MAXN], muSum[MAXN];
Mint phiSum[MAXN];

void sieve(int n = MAXN) {
    fill(is_composite, is_composite + n, false);
    phi[1] = 1; mu[1] = 1; lp[1] = 1;
    for (int i = 2; i < n; ++i) {
        if (!is_composite[i]) {
            primes.push_back(i), cnt[i] = 1;
            lp[i] = i;
            //f(p)
            phi[i] = i - 1; mu[i] = -1;
            primePowers.push_back({0, i});
        }

        for (int j = 0; j < primes.size () && i * primes[j] < n; ++j) {
            is_composite[i * primes[j]] = true;

            if (i % primes[j] == 0) { //p[j] divides i
                cnt[i * primes[j]] = cnt[i] + 1;
                while (primePowers[j].size() <= cnt[i] + 2) {
                    primePowers[j].push_back(primePowers[j][primePowers[j].size() - 1] * primes[j]);
                }

                int div = i / primePowers[j][cnt[i]];
                if (div == 1) {
                    int k = cnt[i] + 1, pk = primePowers[j][k];
                    //f(p^k)
                    phi[i * primes[j]] = (pk * (primes[j] - 1)) / (primes[j]);
                    mu[i * primes[j]] = 0;
                } else {
                    phi[i * primes[j]] = phi[i / primePowers[j][cnt[i]]] * phi[primePowers[j][cnt[i]] * primes[j]];
                    mu[i * primes[j]] = mu[i / primePowers[j][cnt[i]]] * mu[primePowers[j][cnt[i]] * primes[j]];
                }

                lp[i * primes[j]] = primes[j];
                break;
            } else { //p[j] does not divide i
                phi[i * primes[j]] = phi[i] * phi[primes[j]];
                mu[i * primes[j]] = mu[i] * mu[primes[j]];
                cnt[i * primes[j]] = 1;
                lp[i * primes[j]] = primes[j];
            }
        }
    }
    for (int i = 0; i < MAXN; ++i) {
        phiSum[i] = phi[i] + (i ? phiSum[i - 1] : 0);
        muSum[i] = mu[i] + (i ? muSum[i - 1] : 0);
    }
}

vector<int> divMu;
vector<Mint> divPhi;

int getMuSum(int n, int x) { return x < MAXN ? muSum[x] : divMu[n / x]; }
Mint getPhiSum(int n, int x) { return x < MAXN ? phiSum[x] : divPhi[n / x]; }
int sqroot(int x) { return floor(sqrtl(x)); }
Mint sm(Mint x) { return x * (x + 1) / 2; }

void runMuSum(int n, int last) {
    for (int i = last - 1; i >= 0; --i) {
        if (!i) break;
        int x = n / i, sqr = sqroot(x);

        int val = 1 + getMuSum(n, sqr) * sqr;
        for (int f = 2; f <= sqr; ++f) val -= getMuSum(n, x / f);
        for (int f = 1; f <= sqr; ++f) val -= mu[f] * x / f;

        divMu[i] = val;
    }
}

void runPhiSum(int n, int last) {
    for (int i = last - 1; i >= 0; --i) {
        if (!i) break;
        int x = n / i, sqr = sqroot(x);

        Mint val = - getMuSum(n, sqr) * sm(sqr);
        for (int f = 1; f <= sqr; ++f) val += getMuSum(n, x / f) * f;
        for (int f = 1; f <= sqr; ++f) val += mu[f] * sm(x / f);

        divPhi[i] = val;
    }
}


signed main() {
    sieve();
    int n; cin >> n;
    if (n < MAXN) cout << phiSum[n];
    else {
        int last = 1;
        while (n / last > MAXN) ++last;
        divMu.resize(last); divPhi.resize(last);
        runMuSum(n, last); runPhiSum(n, last);

        cout << getPhiSum(n, n);
    }
}