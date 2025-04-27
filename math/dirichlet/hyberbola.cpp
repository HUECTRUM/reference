#include <bits/stdc++.h>
using namespace std;

//Optimal point for F(n^a), G(n^b): k=n^[(1-b)/(2-a-b)]
//Precomp prf up to t = n^[1/(2-a)]
//Sum of H(i) over all n/k is O(n^(2/3)) given constant F and G for n/k.
template <class S, auto f, auto g, auto F, auto G> struct Hyperbola {
    static_assert(std::is_convertible_v<decltype(f), std::function<S(int)>>,
    "f must work as S(int)");
    static_assert(std::is_convertible_v<decltype(g), std::function<S(int)>>,
    "g must work as S(int)");
    static_assert(std::is_convertible_v<decltype(F), std::function<S(int)>>,
    "F must work as S(int)");
    static_assert(std::is_convertible_v<decltype(G), std::function<S(int)>>,
    "G must work as S(int)");

    S calculate_sqrt(int n) {
        S ans = 0;
        int i = 1;
        for (;i * i <= n; ++i) {
            ans += f(i) * G(n / i);
            ans += g(i) * F(n / i);
        }
        --i;
        ans -= F(i) * G(i);
        return ans;
    }

    S calculate(int n, int k, int l) {
        //(k, l) is on the convex hull
        assert((k * l <= n) && ((k + 1) * (l + 1) > n));

        S ans = 0;
        for (int i = 1; i <= k; ++i) ans += f(i) * G(n / i);
        for (int i = 1; i <= l; ++i) ans += g(i) * F(n / i);
        ans -= F(k) * G(l);
        return ans;
    }

    S calculate_limit(int n, int k) {
        return calculate(n, k, n / k);
    }
};
