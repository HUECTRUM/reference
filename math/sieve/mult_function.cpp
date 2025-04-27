#include <bits/stdc++.h>
using namespace std;


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
                    //f(p^k)
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
