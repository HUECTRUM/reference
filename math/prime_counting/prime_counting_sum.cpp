#include <bits/stdc++.h>
using namespace std;

#define int long long int

struct PrimeCounting {
    vector<int> v;
    unordered_map<int, int> primeCnt;
    unordered_map<int, int> primeSum;
    vector<int> primes;

    void run(int n) {
        int r = sqrt(n);

        for (int i = 1; i <= r; ++i) v.push_back(n / i);
        while (v.back() - 1) v.push_back(v.back() - 1);
        for (auto x: v) primeCnt[x] = x - 1, primeSum[x] = x * (x + 1) / 2 - 1;

        int prevCnt = 0, prevSum = 0;
        for (int p = 2; p <= r; ++p) {
            int currCnt = primeCnt[p], currSum = primeSum[p];
            if (currCnt <= prevCnt) continue;

            primes.push_back(p);
            int p2 = p * p;
            for (auto &vEl: v) {
                if (vEl < p2) break;
                primeCnt[vEl] -= (primeCnt[vEl / p] - prevCnt);
                primeSum[vEl] -= p * (primeSum[vEl / p] - prevSum);
            }
            prevCnt = currCnt, prevSum = currSum;
        }
    }
};
