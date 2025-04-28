#include <bits/stdc++.h>
using namespace std;

namespace atcoder {
    namespace internal {

#if __cplusplus >= 202002L

        using std::bit_ceil;

#else

        // @return same with std::bit::bit_ceil
        unsigned int bit_ceil(unsigned int n) {
            unsigned int x = 1;
            while (x < (unsigned int)(n)) x *= 2;
            return x;
        }

#endif

// @param n `1 <= n`
// @return same with std::bit::countr_zero
        int countr_zero(unsigned int n) {
#ifdef _MSC_VER
            unsigned long index;
    _BitScanForward(&index, n);
    return index;
#else
            return __builtin_ctz(n);
#endif
        }

// @param n `1 <= n`
// @return same with std::bit::countr_zero
        constexpr int countr_zero_constexpr(unsigned int n) {
            int x = 0;
            while (!(n & (1 << x))) x++;
            return x;
        }

    }  // namespace internal

#if __cplusplus >= 201703L

    template <class S, auto op, auto e> struct segtree {
        static_assert(std::is_convertible_v<decltype(op), std::function<S(S, S)>>,
                      "op must work as S(S, S)");
        static_assert(std::is_convertible_v<decltype(e), std::function<S()>>,
                      "e must work as S()");

#else

    template <class S, S (*op)(S, S), S (*e)()> struct segtree {

#endif

    public:
        segtree() : segtree(0) {}
        explicit segtree(int n) : segtree(std::vector<S>(n, e())) {}
        explicit segtree(const std::vector<S>& v) : _n((int)(v.size())) {
            size = (int)internal::bit_ceil((unsigned int)(_n));
            log = internal::countr_zero((unsigned int)size);
            d = std::vector<S>(2 * size, e());
            for (int i = 0; i < _n; i++) d[size + i] = v[i];
            for (int i = size - 1; i >= 1; i--) {
                update(i);
            }
        }

        void set(int p, S x) {
            assert(0 <= p && p < _n);
            p += size;
            d[p] = x;
            for (int i = 1; i <= log; i++) update(p >> i);
        }

        S get(int p) const {
            assert(0 <= p && p < _n);
            return d[p + size];
        }

        S prod(int l, int r) const {
            assert(0 <= l && l <= r && r <= _n);
            S sml = e(), smr = e();
            l += size;
            r += size;

            while (l < r) {
                if (l & 1) sml = op(sml, d[l++]);
                if (r & 1) smr = op(d[--r], smr);
                l >>= 1;
                r >>= 1;
            }
            return op(sml, smr);
        }

        S all_prod() const { return d[1]; }

        template <bool (*f)(S)> int max_right(int l) const {
            return max_right(l, [](S x) { return f(x); });
        }
        template <class F> int max_right(int l, F f) const {
            assert(0 <= l && l <= _n);
            assert(f(e()));
            if (l == _n) return _n;
            l += size;
            S sm = e();
            do {
                while (l % 2 == 0) l >>= 1;
                if (!f(op(sm, d[l]))) {
                    while (l < size) {
                        l = (2 * l);
                        if (f(op(sm, d[l]))) {
                            sm = op(sm, d[l]);
                            l++;
                        }
                    }
                    return l - size;
                }
                sm = op(sm, d[l]);
                l++;
            } while ((l & -l) != l);
            return _n;
        }

        template <bool (*f)(S)> int min_left(int r) const {
            return min_left(r, [](S x) { return f(x); });
        }
        template <class F> int min_left(int r, F f) const {
            assert(0 <= r && r <= _n);
            assert(f(e()));
            if (r == 0) return 0;
            r += size;
            S sm = e();
            do {
                r--;
                while (r > 1 && (r % 2)) r >>= 1;
                if (!f(op(d[r], sm))) {
                    while (r < size) {
                        r = (2 * r + 1);
                        if (f(op(d[r], sm))) {
                            sm = op(d[r], sm);
                            r--;
                        }
                    }
                    return r + 1 - size;
                }
                sm = op(d[r], sm);
            } while ((r & -r) != r);
            return 0;
        }

    private:
        int _n, size, log;
        std::vector<S> d;

        void update(int k) { d[k] = op(d[2 * k], d[2 * k + 1]); }
    };

}  // namespace atcoder
using namespace atcoder;


struct InversionCount {
    static int e() { return 0; }
    static int op(int a, int b) { return a + b; }

    static void vectorCoordinateCompression(vector<int> &v) {
        std::sort(v.begin(), v.end());
        v.erase(std::unique(v.begin(), v.end()), v.end());
    }

    static int getVectorCompressed(int val, vector<int> &v) { return lower_bound(v.begin(), v.end(), val) - v.begin(); }

    vector<int> v;
    int n;
    segtree<int, op, e> seg;

    InversionCount(vector<int> &initial, bool compress = false) : n(initial.size()) {
        if (compress) {
            v = vector<int>(initial.size());

            vector<int> coords = initial;
            vectorCoordinateCompression(coords);

            for (int i = 0; i < initial.size(); ++i) v[i] = getVectorCompressed(initial[i], coords);
        } else v = initial;

        seg = segtree<int, op, e>(initial.size() + 1);
    }

    int run() {
        int ans = 0;
        for (auto &x: v) {
            ans += seg.prod(x + 1, n + 1);
            seg.set(x, seg.get(x) + 1);
        }
        return ans;
    }
};



signed main() {
    ios_base::sync_with_stdio(false); cin.tie(NULL); cout.tie(NULL);
    int t; cin >> t;
    while (t--) {
        int n; cin >> n;
        vector<int> v(n); for (int i = 0; i < n; ++i) cin >> v[i];

        InversionCount invCnt(v, true);
        cout << invCnt.run() << "\n";
    }
}
