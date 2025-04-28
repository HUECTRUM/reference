#include <bits/stdc++.h>
using namespace std;

#define int long long int
struct event { int x, y1, y2, type; };
struct coords { int x1, y1, x2, y2; };

template<int MAXN = 2097152, int INF = 1000000000000000000> struct RectArea {
    int n;
    vector<int> tag, scr, compr;
    vector<event> events;

    static void vectorCoordinateCompression(vector<int> &v) {
        std::sort(v.begin(), v.end());
        v.erase(std::unique(v.begin(), v.end()), v.end());
    }

    static int getVectorCompressed(int val, vector<int> &v) { return lower_bound(v.begin(), v.end(), val) - v.begin(); }

    RectArea(vector<coords> &c): n(c.size()), tag(4 * MAXN), scr(4 * MAXN), events(2 * c.size()) {
        for (int i = 0; i < n; ++i) {
            coords curr = c[i];
            events[2 * i] = {curr.x1, curr.y1, curr.y2, 1};
            events[2 * i + 1] = {curr.x2, curr.y1, curr.y2, -1};
            compr.push_back(curr.y1), compr.push_back(curr.y2);
        }
        std::sort(events.begin(), events.end(), [](event &e1, event &e2) {
            return make_pair(e1.x, e1.type) < make_pair(e2.x, e2.type);
        });

        vectorCoordinateCompression(compr);
        for (int i = 0; i < (int) events.size(); ++i) {
            events[i].y1 = getVectorCompressed(events[i].y1, compr);
            events[i].y2 = getVectorCompressed(events[i].y2, compr);
        }
    }

    int run() {
        int ans = 0;
        int prevX = -INF;
        for (auto &[x, yl, yr, type]: events) {
            int nonZero = scr[1];
            if (prevX != -INF) ans += (nonZero) * (x - prevX);
            rangeAdd(yl, yr, type);
            prevX = x;
        }
        return ans;
    }

    int getScr(int v, int tl, int tr) {
        if (tag[v]) return compr[tr] - compr[tl];
        if (tr - tl == 1) return scr[v] = 0;

        int tm = (tl + tr) >> 1;
        return (tag[v << 1] ? compr[tm] - compr[tl] : scr[v << 1]) + (tag[v << 1 | 1] ? compr[tr] - compr[tm] : scr[v << 1 | 1]);
    }

    void rangeAdd(int l, int r, int delta, int v = 1, int tl = 0, int tr = MAXN) {
        if (l >= r || tl == tr) return;
        if (l == tl && r == tr) {
            tag[v] += delta;
            scr[v] = getScr(v, tl, tr);
            return;
        }

        int tm = (tl + tr) >> 1;
        rangeAdd(l, min(r, tm), delta, v << 1, tl, tm);
        rangeAdd(max(l, tm), r, delta, v << 1 | 1, tm, tr);
        scr[v] = getScr(v, tl, tr);
    }
};






signed main() {
    ios_base::sync_with_stdio(false); cin.tie(NULL); cout.tie(NULL);
    int n; cin >> n;
    vector<coords> coords(n);
    for (int i = 0; i < n; ++i) cin >> coords[i].x1 >> coords[i].y1 >> coords[i].x2 >> coords[i].y2;

    RectArea ra(coords);
    cout << ra.run();
}