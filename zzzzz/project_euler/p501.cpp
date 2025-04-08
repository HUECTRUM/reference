#include <bits/stdc++.h>

using namespace std;

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
#define vct vector

int cntLeq(vll &v, ll x) { return std::upper_bound(v.begin(), v.end(), x) - v.begin(); }
int cntLess(vll &v, ll x) { return std::lower_bound(v.begin(), v.end(), x) - v.begin(); }
int cntGreater(vll &v, ll x) { return v.end() - std::upper_bound(v.begin(), v.end(), x); }
int cntGeq(vll &v, ll x) { return v.end() - std::lower_bound(v.begin(), v.end(), x); }

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



void vectorCoordinateCompression(vll &v) {
    std::sort(v.begin(), v.end());
    v.erase(std::unique(v.begin(), v.end()), v.end());
}

int getVectorCompressed(ll val, vll &v) { return lower_bound(v.begin(), v.end(), val) - v.begin(); }



//////////////////////////////////////////////////////////////////////////
#define int long long int
#define Mint modint998244353
#define vmint vector<modint998244353>
#define vvmint vector<vector<modint998244353>>

struct PrimeCounting {
    vi v;
    unordered_map<int, int> primeCnt;
    vi primes;

    void run(int n) {
        int r = sqrt(n);

        reps(i, 1, r + 1) v.pb(n / i);
        while (v.back() - 1) v.pb(v.back() - 1);
        repe(x, v) primeCnt[x] = x - 1;

        int prevCnt = 0;
        reps(p, 2, r + 1) {
            int currCnt = primeCnt[p];
            if (currCnt <= prevCnt) continue;

            primes.pb(p);
            int p2 = p * p;
            for (auto &vEl: v) {
                if (vEl < p2) break;
                primeCnt[vEl] -= (primeCnt[vEl / p] - prevCnt);

            }
            prevCnt = currCnt;
        }
    }
};

const int MAXN = 1e7 + 10;
vi lp(MAXN + 1, 0), pr;

void linsieve() {
    reps(i, 2, MAXN + 1) {
        if (!lp[i]) lp[i] = i, pr.pb(i);
        for (int j = 0; i * pr[j] <= MAXN; ++j) {
            lp[i * pr[j]] = pr[j];
            if (pr[j] == lp[i]) break;
        }
    }
}

signed main() {
    IO; linsieve();

    int n = 1e12;
    PrimeCounting p; p.run(n);

    int p7 = 0;
    for (auto &x: pr) {
        if (x * x * x * x * x * x * x > n) break;
        p7++;
    }

    int p3 = 0;
    for (auto &x: pr) {
        int dv = n / (x * x * x);
        if (x * x * x > n || dv < 2) break;
        p3 += p.primeCnt[dv] - (dv >= x ? 1 : 0);
    }

    int pqr = 0;
    for (int i = 0; i < pr.size(); ++i) {
        if (pr[i] * pr[i] * pr[i] > n) break;
        for (int j = i + 1; j < pr.size(); ++j) {
            if (pr[j] * pr[j] * pr[i] > n) break;
            pqr += p.primeCnt[n / (pr[i] * pr[j])] - j - 1;
        }
    }
    cout << p7 + p3 + pqr;
}