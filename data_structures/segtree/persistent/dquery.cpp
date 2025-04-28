#include <bits/stdc++.h>
using namespace std;


#define int long long int

struct node {
    node *l, *r;
    int cnt;

    node (int val): l(nullptr), r(nullptr), cnt(val) {}
    node(node *l, node *r) : l(l), r(r), cnt((l ? l->cnt : 0) + (r ? r->cnt : 0)) {}
};

node* build(int tl, int tr) {
    if (tl == tr) return new node(0);

    int tm = (tl + tr) >> 1;
    return new node(build(tl, tm), build(tm + 1, tr));
}

int sumQuery(node* v, int l, int r, int tl, int tr) {
    if (l > r) return 0;
    if (l == tl && tr == r) return v->cnt;

    int tm = (tl + tr) >> 1;
    return sumQuery(v->l, l, min(r, tm), tl, tm) + sumQuery(v->r, max(l, tm+1), r, tm + 1, tr);
}


node* upd(node* prev, int pos, int val, int tl, int tr) {
    if (tl == tr) return new node(prev->cnt + val);

    int tm = (tl + tr) >> 1;
    if (pos <= tm) return new node(upd(prev->l,pos, val, tl, tm), prev->r);
    else return new node(prev->l, upd(prev->r, pos, val, tm + 1, tr));
}

struct DQuery {
    static void vectorCoordinateCompression(vector<int> &v) {
        std::sort(v.begin(), v.end());
        v.erase(std::unique(v.begin(), v.end()), v.end());
    }

    static int getVectorCompressed(int val, vector<int> &v) { return lower_bound(v.begin(), v.end(), val) - v.begin(); }

    vector<node*> roots;
    int n;

    DQuery(vector<int> vv, bool compress = false): n(vv.size()) {
        if (compress) {
            vector<int> coords = vv;
            vectorCoordinateCompression(coords);

            for (int &i: vv) i = getVectorCompressed(i, coords);
        }

        vector<int> last(n, -1);

        roots = vector<node*>(n + 1);
        roots[0] = build(0, n - 1);
        for (int i = 0; i < n; ++i) {
            if (last[vv[i]] != -1) {
                roots[i + 1] = upd(roots[i], last[vv[i]], -1, 0, n - 1);
                roots[i + 1] = upd(roots[i + 1], i, 1, 0, n - 1);
            } else roots[i + 1] = upd(roots[i], i, 1, 0, n - 1);

            last[vv[i]] = i;
        }
    }

    int query(int l, int r) {
        return sumQuery(roots[r + 1], l, r, 0, n - 1);
    }
};

signed main() {
    ios_base::sync_with_stdio(false); cin.tie(NULL); cout.tie(NULL);

    int n; cin >> n;
    vector<int> v(n);
    for (int i = 0; i < n; ++i) cin >> v[i];


    DQuery dq(v, true);

    int q; cin >> q;
    for (int i = 0; i < q; ++i) {
        int l, r; cin >> l >> r; --l, --r;

        cout << dq.query(l, r) << "\n";
    }
}