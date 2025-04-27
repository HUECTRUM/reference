#include <bits/stdc++.h>
using namespace std;

#define int long long int

template <typename T> struct FloorArr {
    int n, sqr, sz;
    vector<T> arr; vector<int> nums;

    static void compr(vector<int> &v) {
        std::sort(v.begin(), v.end());
        v.erase(std::unique(v.begin(), v.end()), v.end());
    }

    FloorArr(int n): n(n), sqr(floor(sqrtl(n))) {
        for(int i = 1; i <= sqr; ++i) nums.push_back(i), nums.push_back(n / i);
        compr(nums);

        sz = nums.size();
        arr.resize(sz);
    }

    T& operator[] (int x) { return x <= sqr ? arr[x - 1] : arr[sz - n / x]; }
    T& getDiv(int div) { return this->operator[](n / div); }
    T& getIdx(int idx) { return arr[idx]; }
    int valueOf(int idx) { return idx < sqr ? idx + 1 : n / (sz - idx); }

    vector<pair<int, int>> getKeyPairs() {
        vector<pair<int, int>> res(sz);
        for (int i = 0; i < sz; ++i) res[i] = {i, valueOf(i)};
        return res;
    }
};

struct Fenw {
    int n;
    vector<int> bit;

    Fenw(int n): n(n) { bit.resize(n); }
    Fenw(int n, int value) : Fenw(n) { for (int i = 0; i < n; ++i) add(i, value); }

    int sum(int r) {
        int ret = 0;
        for (; r >= 0; r = (r & (r + 1)) - 1)
            ret += bit[r];
        return ret;
    }

    int sum(int l, int r) { return sum(r) - sum(l - 1); }
    int get(int x) { return sum(x, x); }
    void set(int x, int y) { add(x, y - get(x)); }

    void add(int idx, int delta) {
        for (; idx < n; idx = idx | (idx + 1))
            bit[idx] += delta;
    }
};

struct PrimeCount {
    FloorArr<int> run(int x) {
        FloorArr<int> res(x);
        if (x == 1) return res;

        int y = floor(0.35 * pow(x, 2.0 / 3.0) / pow(log(x), 2.0 / 3.0));
        y = max(y, (int)floor(sqrtl(x)) + 1);

        vector<int> sieveRaw(y + 1);
        Fenw sieve(y + 1, 1);
        sieveRaw[0] = sieveRaw[1] = 1;
        sieve.set(0, 0), sieve.set(1, 0);

        vector<pair<int, int>> floorKeys = res.getKeyPairs();
        for (int i = 0; i < res.sz; ++i) {
            res.getIdx(i) = res.valueOf(i) - 1;
        }

        auto S0 = [&](int r) { return r <= y ? sieve.sum(r) : res[r]; };

        for (int p = 2; p * p <= x; ++p) if (!sieveRaw[p]) {
                int sp = sieve.sum(p - 1), lim = min(x / y, x / (p * p));

                for (int i = 1; i <= lim; ++i) {
                    res[x / i] -= S0(x / (i * p)) - sp;
                }

                int j = p * p;
                while (j <= y) {
                    if (!sieveRaw[j]) {
                        sieveRaw[j] = 1;
                        sieve.add(j, -1);
                    }
                    j += p;
                }
            }

        for (int i = 0; i < res.sz; ++i) {
            int val = res.valueOf(i);
            if (val > y) break;
            res.getIdx(i) = sieve.sum(res.valueOf(i));
        }
        return res;
    }
} pc;
