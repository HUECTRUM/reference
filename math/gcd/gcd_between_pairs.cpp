#include <bits/stdc++.h>
using namespace std;

#define int long long int

int ndivfromCeil(int n, int k) { return n / k + (n % k ? 1 : 0); }
int ndivtoCeil(int n, int k) { return ndivfromCeil(n, k - 1) - 1; }

int solve(int l, int r) {
    int g = 1;
    int ans = 0;
    while (true) {
        int div = l / g + (l % g ? 1 : 0);
        if (div == 1) break;
        int fr = ndivfromCeil(l, div), to = ndivtoCeil(l, div);

        int rr = r / (div + 1);
        if (rr >= fr) {
            int len = min(to, rr) - fr + 1;
            ans += len;
        }
        g = to + 1;
    }
    if (r / 2 >= l) ans += (r / 2 - l) + 1;
    return ans;
}

signed main() {
    ios_base::sync_with_stdio(false); cin.tie(NULL); cout.tie(NULL);

    int t; cin >> t;
    while (t--) {
        int l, r; cin >> l >> r;
        if (l == r) cout << "0\n";
        else cout << solve(l, r) << "\n";
    }
}