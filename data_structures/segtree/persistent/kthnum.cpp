#include <bits/stdc++.h>
using namespace std;


#define int long long int


void vectorCoordinateCompression(vector<int> &v) {
    std::sort(v.begin(), v.end());
    v.erase(std::unique(v.begin(), v.end()), v.end());
}

int getVectorCompressed(int val, vector<int> &v) { return lower_bound(v.begin(), v.end(), val) - v.begin(); }


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

int query(node *lNode, node *rNode, int k, int tl, int tr) {
    if (tl == tr) return tl;

    int tm = (tl + tr) >> 1;
    int cntL = rNode->l->cnt - lNode->l->cnt;
    if (cntL >= k) return query(lNode->l, rNode->l, k, tl, tm);
    else return query(lNode->r, rNode->r, k - cntL, tm + 1, tr);
}


node* upd(node* prev, int pos, int tl, int tr) {
    if (tl == tr) return new node(prev->cnt + 1);

    int tm = (tl + tr) >> 1;
    if (pos <= tm) return new node(upd(prev->l,pos, tl, tm), prev->r);
    else return new node(prev->l, upd(prev->r, pos, tm + 1, tr));
}

const int MAXN = 200010;
vector<node*> roots(4 * MAXN);
int totalRoots = 0;

signed main() {
    ios_base::sync_with_stdio(false); cin.tie(NULL); cout.tie(NULL);

    int n, q; cin >> n >> q;
    vector<int> v(n + 1), allCoords;
    for (int i = 1; i <= n; ++i) cin >> v[i], allCoords.push_back(v[i]);

    vectorCoordinateCompression(allCoords);


    roots[totalRoots++] = build(0, n - 1);
    for (int i = 1; i <= n; ++i) {
        int comprIdx = getVectorCompressed(v[i], allCoords);
        roots[totalRoots++] = upd(roots[totalRoots - 1], comprIdx, 0, n - 1);
    }

    for (int i = 0; i < q; ++i) {
        int l, r, x; cin >> l >> r >> x;
        int idx = query(roots[l - 1], roots[r], x, 0, n - 1);
        cout << allCoords[idx] << "\n";
    }
}
