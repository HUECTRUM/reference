#include <bits/stdc++.h>
using namespace std;


template<typename R> struct MoOps {
    virtual void add(int idx) = 0;
    virtual void remove(int idx) = 0;
    virtual R getResult() = 0;
};

struct UniqueOps: MoOps<int> {
    vector<int> freq, v;
    int uCnt = 0;

    UniqueOps(vector<int> const &v, int MAXN = 300000) : v(v), freq(MAXN) { }

    void add(int idx) {
        if (!freq[v[idx]]) ++uCnt;
        freq[v[idx]]++;
    }

    void remove(int idx) {
        freq[v[idx]]--;
        if (!freq[v[idx]]) --uCnt;
    }

    int getResult() { return uCnt; }
};

struct query { int l, r, id; };
template<typename R> struct MO {
    vector<query> queries;
    vector<R> ans;
    int q;

    MoOps<R> &ops;

    MO(vector<query> const &qu, MoOps<R> &moOps, int BLOCKSZ = 450) : ops(moOps) {
        queries = qu, ans = vector<R>(qu.size());
        std::sort(queries.begin(), queries.end(), [&](query &q1, query &q2) {
            return make_pair(q1.l / BLOCKSZ, q1.r) < make_pair(q2.l / BLOCKSZ, q2.r);
        });
        q = qu.size();
    }

    void run() {
        int curL = 0, curR = -1;

        for (int i = 0; i < q; ++i) {
            auto qu = queries[i];
            while (curL > qu.l) {
                curL--;
                ops.add(curL);
            }
            while (curR < qu.r) {
                curR++;
                ops.add(curR);
            }
            while (curL < qu.l) {
                ops.remove(curL);
                curL++;
            }
            while (curR > qu.r) {
                ops.remove(curR);
                curR--;
            }
            ans[qu.id] = ops.getResult();
        }
    }

    vector<R> getResults() { return ans; }
};
