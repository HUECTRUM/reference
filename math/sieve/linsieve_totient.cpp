#include <bits/stdc++.h>
using namespace std;


const int MAXN = 1e6 + 10;
vector<int> primes;
bool is_composite[MAXN];
int phi[MAXN];

void sieve(int n = MAXN) {
    fill(is_composite, is_composite + n, false);
    phi[1] = 1;
    for (int i = 2; i < n; ++i) {
        if (!is_composite[i]) primes.push_back(i), phi[i] = i - 1;

        for (int j = 0; j < primes.size () && i * primes[j] < n; ++j) {
            is_composite[i * primes[j]] = true;

            if (i % primes[j] == 0) { //p[j] divides i
                phi[i * primes[j]] = phi[i] * primes[j];
                break;
            } else { //p[j] does not divide i
                phi[i * primes[j]] = phi[i] * phi[primes[j]];
            }
        }
    }
}
