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

#define int long long int

int MAXPW = 20, MAXV = (1 << MAXPW), ALL1 = MAXV - 1;
int MOD = 1e9 + 7;

vector<int> pows(MAXV);
void precalc() {
    pows[0] = 1;
    for (int i = 1; i < MAXV; ++i) pows[i] = (pows[i - 1] * 2) % MOD;
}

signed main() {
    precalc();
    ios_base::sync_with_stdio(false); cin.tie(NULL); cout.tie(NULL);

    int n; cin >> n;
    vector<int> v(n);
    for (int i = 0; i < n; ++i) cin >> v[i];

    vector<int> freq(MAXV);
    for (int i = 0; i < n; ++i) freq[v[i]]++;

    vector<int> zt = ss.supersetZeta(freq, MAXPW);
    vector<int> pws(MAXV);
    for (int i = 0; i < MAXV; ++i) pws[i] = pows[zt[i]];

    vector<int> back = ss.supersetMobius(pws, MAXPW);
    cout << (back[0] % MOD + MOD) % MOD;
}
