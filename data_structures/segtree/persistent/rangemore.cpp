#include <bits/stdc++.h>
using namespace std;


#define int long long int

const int MAXN = 200010;


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

int cntQuery(node* v, int l, int r, int tl, int tr) {
    if (l > r) return 0;
    if (l == tl && tr == r) return v->cnt;

    int tm = (tl + tr) >> 1;
    return cntQuery(v->l, l, min(r, tm), tl, tm) + cntQuery(v->r, max(l, tm + 1), r, tm + 1, tr);
}

node* upd(node* prev, int pos, int tl, int tr) {
    if (tl == tr) return new node(prev->cnt + 1);

    int tm = (tl + tr) >> 1;
    if (pos <= tm) return new node(upd(prev->l,pos, tl, tm), prev->r);
    else return new node(prev->l, upd(prev->r, pos, tm + 1, tr));
}

vector<node*> roots(4 * MAXN);
int totalRoots = 0;

signed main() {
    ios_base::sync_with_stdio(false); cin.tie(NULL); cout.tie(NULL);

    int n, q; cin >> n >> q;
    vector<int> v(n + 1);
    for (int i = 1; i <= n; ++i) cin >> v[i];


    roots[totalRoots++] = build(0, n - 1);
    for (int i = 1; i <= n; ++i) {
        roots[totalRoots++] = upd(roots[totalRoots - 1], v[i], 0, n - 1);
    }

    for (int i = 0; i < q; ++i) {
        int l, r, x; cin >> l >> r >> x;
        int rQ = cntQuery(roots[r], x, n - 1, 0, n - 1), lQ = cntQuery(roots[l - 1], x, n - 1, 0, n - 1);
        cout << rQ - lQ << endl;
    }
}