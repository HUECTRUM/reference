#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>
#include <bits/stdc++.h>

using namespace std;
using namespace __gnu_pbds;
using namespace __gnu_cxx;

/* clang-format off */
/* TYPES  */
#define ll long long
#define ld long double
#define pii pair<int, int>
#define pll pair<long long, long long>
#define vi vector<int>
#define vll vector<long long>
#define vpii vector<pair<int, int>>
#define vpii vector<pair<int, int>>
#define vvpii vector<vector<pair<int, int>>>
#define vpll vector<pair<long long, long long>>
#define vvpll vector<vector<pair<long long, long long>>>
#define vvi vector<vector<int>>
#define vvll vector<vector<long long>>
#define mii map<int, int>
#define si set<int>
#define sc set<char>
#define vd vector<double>
#define vvd vector<vector<double>>


/* FUNCTIONS */
#define feach(el, v) for(auto &el: v)
#define rep(i, n) for(int i=0;i<n;i++)
#define reprv(i, n) for(int i=n-1;i>=0;i--)
#define reps(i, s, e) for(int i=s;i<e;i++)
#define reprve(i, e, s) for(int i=e-1;i>=s;i--)
#define repe(x, y) for (auto &x: y)
#define repe2(x, a, y) for (auto &[x,a]: y)

#define pb push_back
#define eb emplace_back


#define IO ios_base::sync_with_stdio(false); cin.tie(NULL); cout.tie(NULL)
#pragma GCC target("popcnt")
#define vct vector

int cntLeq(vll &v, ll x) { return std::upper_bound(v.begin(), v.end(), x) - v.begin(); }
int cntLess(vll &v, ll x) { return std::lower_bound(v.begin(), v.end(), x) - v.begin(); }
int cntGreater(vll &v, ll x) { return v.end() - std::upper_bound(v.begin(), v.end(), x); }
int cntGeq(vll &v, ll x) { return v.end() - std::lower_bound(v.begin(), v.end(), x); }
ll firstGeq(vll &v, ll x) { return *std::lower_bound(v.begin(), v.end(), x); }
ll firstGreater(vll &v, ll x) { return *std::upper_bound(v.begin(), v.end(), x); }
ll firstLess(vll &v, ll x) { auto ptr = std::lower_bound(v.begin(), v.end(), x); --ptr; return *ptr; }
ll firstLeq(vll &v, ll x) { auto ptr = std::upper_bound(v.begin(), v.end(), x); --ptr; return *ptr; }
int indGeq(vll &v, ll x) { return std::lower_bound(v.begin(), v.end(), x) - v.begin(); }
int indGreater(vll &v, ll x) { return std::upper_bound(v.begin(), v.end(), x) - v.begin(); }
int indLess(vll &v, ll x) { return std::lower_bound(v.begin(), v.end(), x) - v.begin() - 1; }
int indLeq(vll &v, ll x) { return std::upper_bound(v.begin(), v.end(), x) - v.begin() - 1; }

vll buildPref(vll &v) {
    int n = v.size(); vll pref(n);
    rep(i, n) pref[i] = v[i] + (i ? pref[i - 1] : 0);
    return pref;
}
ll getPrefSum(vll &pref, int l, int r) { return pref[r] - (l ? pref[l - 1] : 0); }

vi dx = {0,0,-1,1}, dy = {-1,1,0,0};

int popcnt(int i) { return __builtin_popcountll(i); }
int popcnt(long long i) { return __builtin_popcountll(i); }

template<typename T>inline void chmax(T &a,T b){a=max(a,b);}
template<typename T>inline void chmin(T &a,T b){a=min(a,b);}



ll ndivto(ll n, ll k) { return n / k; }
ll ndivfrom(ll n, ll k) { return ndivto(n, k + 1) + 1; }

typedef tree<ll, null_type, less_equal<>, rb_tree_tag, tree_order_statistics_node_update> oSet;


//////////////////////////////////////////////////////////////////////////
#define int long long int
#define Mint modint998244353
#define vmint vector<modint998244353>


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
    IO;

    int t; cin >> t;
    while (t--) {
        int n; cin >> n;
        vi v(n); rep(i, n) cin >> v[i];

        InversionCount invCnt(v, true);
        cout << invCnt.run() << "\n";
    }
}