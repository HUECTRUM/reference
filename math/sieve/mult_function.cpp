#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>
#include <bits/stdc++.h>

using namespace std;
using namespace __gnu_pbds;
using namespace __gnu_cxx;

/* TYPES  */
#define ll long long

#define vll vector<long long>


typedef tree<ll, null_type, less<>, rb_tree_tag, tree_order_statistics_node_update> oSet;
#define IO ios_base::sync_with_stdio(false); cin.tie(NULL); cout.tie(NULL)
#pragma GCC target("popcnt")


template<typename T>inline void chmax(T &a,T b){a=max(a,b);}
template<typename T>inline void chmin(T &a,T b){a=min(a,b);}

void vectorCoordinateCompression(vll &v) {
    std::sort(v.begin(), v.end());
    v.erase(std::unique(v.begin(), v.end()), v.end());
}

int getVectorCompressed(ll val, vll &v) { return lower_bound(v.begin(), v.end(), val) - v.begin(); }

ll ndivto(ll n, ll k) { return n / k; }
ll ndivfrom(ll n, ll k) { return ndivto(n, k + 1) + 1; }

ll ndivfromCeil(ll n, ll k) { return n / k + (n % k ? 1 : 0); }
ll ndivtoCeil(ll n, ll k) { return ndivfromCeil(n, k - 1) - 1; }


//////////////////////////////////////////////////////////////////////////
#define int long long int


const int MAXN = 1e6 + 10;
vector<int> primes;
vector<vector<int>> primePowers;
bool is_composite[MAXN];
int func[MAXN], cnt[MAXN], lp[MAXN];

void sieve(int n = MAXN) {
    fill(is_composite, is_composite + n, false);
    func[1] = 1; lp[1] = 1;
    for (int i = 2; i < n; ++i) {
        if (!is_composite[i]) {
            primes.push_back(i), cnt[i] = 1;
            lp[i] = i;
            //f(p)
            func[i] = i + 1;
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
                    //!f(p^k)
                    func[i * primes[j]] = (pk * primes[j] - 1) / (primes[j] - 1);
                } else {
                    func[i * primes[j]] = func[i / primePowers[j][cnt[i]]] * func[primePowers[j][cnt[i]] * primes[j]];
                }

                lp[i * primes[j]] = primes[j];
                break;
            } else { //p[j] does not divide i
                func[i * primes[j]] = func[i] * func[primes[j]];
                cnt[i * primes[j]] = 1;
                lp[i * primes[j]] = primes[j];
            }
        }
    }
}


signed main() {
    IO;

    sieve();

    int t; cin >> t;
    while (t--) {
        int n; cin >> n;
        cout << func[n] - n << endl;
    }
}